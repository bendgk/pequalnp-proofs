// ptrank search: stochastic search for decompositions  A + B^{T1} = I  of small rank(A) + rank(B).  HEURISTIC:
// it produces witnesses (upper bounds on P(n)); it never proves anything about non-existence.
//
// Two neighbourhoods, both simulated annealing with independent restarts on -j threads:
//   --mode terms (default when --R is given):  state = R terms (V_r, U_r); objective rho = rank(I + Phi).
//        Moves: flip one bit of some V_r / U_r (changes n rows of the n^2 x n^2 matrix, updated incrementally),
//        xor a random mask into one row, add a rank-one matrix to one V_r / U_r.  When a restart stalls the state
//        is re-based by a random symmetry (V,U) -> (P V Q^-T, P^-T U Q) plus a random recombination of the terms,
//        which keeps (R, rho) but changes which states are one move away ("polish").
//   --mode pure:  state = the pair (A, B) itself (two n^2 x n^2 bit matrices with A + B^{T1} = I); objective
//        wA*rank(A) + wB*rank(B).  Move: add a pure tensor a(x)b(x)c(x)d, i.e. A += (a(x)b)(c(x)d)^T and
//        B += (c(x)b)(a(x)d)^T, which changes each rank by at most 1.  The move set is invariant under the
//        whole symmetry group.  R is free; the terms are read off B at the end.
// Every reported witness is recomputed from scratch with cost_of() before it is printed or written.
#pragma once
#include "core.hpp"
#include <atomic>
#include <chrono>
#include <cmath>
#include <mutex>
#include <thread>

static const int RMAX = 64;

struct SearchOpts {
    int n = 0, R = -1, threads = 1;
    double time = 10;
    u64 seed = 1;
    int target = -1;  // stop when total <= target (default: never stop early)
    std::string out, mode = "terms", init, algo = "sa", pareto_dir;
    long iters = 0;      // iterations per restart (0 = auto)
    long restarts = 0;   // per thread; 0 = until --time
    double T0 = -1, T1 = -1;
    double wA = 1, wB = 1;
    bool quiet = false;
    int rmaxpure = -1;   // pure mode: penalise rank(B) above this
    int lambda = 2;      // terms mode: penalty per unit of rank deficiency of B (0 = let the terms collapse)
};

static inline double sec_now() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// --------------------------------------------------------------------------------------------- terms mode
struct TermState {
    int n, R, N;
    Term t[RMAX];
    u64 W[RMAX][NMAX];  // W[r][i2] = sum over j1 with U_r[j1][i2] = 1 of 1 << (j1*n)
    u64 M[64];          // I + Phi

    void rebuild() {
        for (int k = 0; k < N; k++) M[k] = 1ull << k;
        for (int r = 0; r < R; r++) {
            for (int i2 = 0; i2 < n; i2++) W[r][i2] = 0;
            for (int j1 = 0; j1 < n; j1++)
                for (int i2 = 0; i2 < n; i2++)
                    if ((t[r].U[j1] >> i2) & 1) W[r][i2] ^= 1ull << (j1 * n);
            for (int i1 = 0; i1 < n; i1++)
                for (int i2 = 0; i2 < n; i2++) M[i1 * n + i2] ^= W[r][i2] * (u64)t[r].V[i1];
        }
    }
    inline void xorV(int r, int i1, unsigned dm) {  // V_r[i1] ^= dm
        t[r].V[i1] ^= (uint8_t)dm;
        u64* row = M + i1 * n;
        for (int i2 = 0; i2 < n; i2++) row[i2] ^= W[r][i2] * (u64)dm;
    }
    inline void xorU(int r, int j1, unsigned dm) {  // U_r[j1] ^= dm
        t[r].U[j1] ^= (uint8_t)dm;
        unsigned d = dm;
        while (d) {
            int i2 = __builtin_ctz(d);
            d &= d - 1;
            W[r][i2] ^= 1ull << (j1 * n);
            for (int i1 = 0; i1 < n; i1++) M[i1 * n + i2] ^= (u64)t[r].V[i1] << (j1 * n);
        }
    }
    inline int rho() const {
        u64 tmp[64];
        memcpy(tmp, M, (size_t)N * 8);
        return rank_rows(tmp, N);
    }
    // rank(B) = R  <=>  the vec(V_r) are linearly independent and the vec(U_r) are linearly independent.
    // deficiency = (R - rank{vec V_r}) + (R - rank{vec U_r});  0 iff rank(B) = R exactly.
    inline int deficiency() const {
        u64 a[RMAX], b[RMAX];
        for (int r = 0; r < R; r++) {
            u64 v = 0, u = 0;
            for (int i = 0; i < n; i++) {
                v |= (u64)t[r].V[i] << (i * n);
                u |= (u64)t[r].U[i] << (i * n);
            }
            a[r] = v;
            b[r] = u;
        }
        return 2 * R - rank_rows(a, R) - rank_rows(b, R);
    }
    inline int objective(int lambda) const { return rho() + (lambda ? lambda * deficiency() : 0); }
};

static double search_bench_incremental(int n, int R, double secs) {
    TermState s;
    s.n = n;
    s.R = R;
    s.N = n * n;
    Rng g(777);
    unsigned mask = (1u << n) - 1;
    for (int r = 0; r < R; r++)
        for (int i = 0; i < n; i++) {
            s.t[r].V[i] = (uint8_t)(g.next() & mask);
            s.t[r].U[i] = (uint8_t)(g.next() & mask);
        }
    s.rebuild();
    double t0 = sec_now();
    u64 evals = 0, acc = 0;
    while (sec_now() - t0 < secs) {
        for (int it = 0; it < 4096; it++) {
            int r = (int)g.below(R), i = (int)g.below(n);
            unsigned b = 1u << g.below(n);
            if (it & 1) s.xorV(r, i, b);
            else s.xorU(r, i, b);
            acc += s.rho();
            evals++;
        }
    }
    double dt = sec_now() - t0;
    // consistency: the incrementally maintained matrix equals a rebuild
    u64 keep[64];
    memcpy(keep, s.M, sizeof keep);
    s.rebuild();
    if (memcmp(keep, s.M, (size_t)s.N * 8) != 0) {
        fprintf(stderr, "INTERNAL ERROR: incremental Phi differs from rebuild\n");
        exit(3);
    }
    (void)acc;
    return evals / dt;
}

// apply (V,U) -> (P V Q^-T, P^-T U Q) with random P, Q, then a random invertible recombination of the terms
static void random_rebase(TermState& s, Rng& g, bool recombine) {
    int n = s.n;
    uint8_t P[NMAX], Q[NMAX], Pi[NMAX], Qi[NMAX], PiT[NMAX], QiT[NMAX];
    mat_random_invertible(n, g, P);
    mat_random_invertible(n, g, Q);
    mat_inv(n, P, Pi);
    mat_inv(n, Q, Qi);
    mat_transpose(n, Pi, PiT);
    mat_transpose(n, Qi, QiT);
    for (int r = 0; r < s.R; r++) {
        mat_mul(n, P, s.t[r].V, s.t[r].V);
        mat_mul(n, s.t[r].V, QiT, s.t[r].V);
        mat_mul(n, PiT, s.t[r].U, s.t[r].U);
        mat_mul(n, s.t[r].U, Q, s.t[r].U);
    }
    if (recombine && s.R >= 2) {
        // elementary recombinations: V_q += V_r, U_r += U_q  keeps sum_r V_r (x) U_r
        for (int k = 0; k < 2 * s.R; k++) {
            int q = (int)g.below(s.R), r = (int)g.below(s.R);
            if (q == r) continue;
            for (int i = 0; i < n; i++) {
                s.t[q].V[i] ^= s.t[r].V[i];
                s.t[r].U[i] ^= s.t[q].U[i];
            }
        }
    }
    s.rebuild();
}

struct Shared {
    std::mutex mu;
    int best_total = 1 << 30;
    std::vector<Term> best;
    std::atomic<bool> stop{false};
    std::atomic<u64> evals{0};
    std::atomic<u64> restarts{0};
    double t0 = 0;
    const SearchOpts* opt = nullptr;
    long hist[4 * 64 + 8];  // best total of each restart
    // Pareto table: for every exact rank(B) = R the smallest rho = rank(A) seen, with a witness
    int par_rho[65];
    std::atomic<int> par_max{1 << 30};  // max over R of par_rho[R] (cheap pre-filter for the workers)
    std::vector<Term> par_wit[65];
    Shared() {
        memset(hist, 0, sizeof hist);
        for (int i = 0; i < 65; i++) par_rho[i] = 1 << 30;
    }
};

// record a candidate; the cost is recomputed from scratch here.  Returns the true cost.
static Cost offer(Shared& sh, int n, const std::vector<Term>& t, int thread, long restart, const char* how) {
    Cost c = cost_of(n, t.data(), (int)t.size());
    std::lock_guard<std::mutex> lk(sh.mu);
    if (c.R <= 64 && c.rho < sh.par_rho[c.R]) {
        sh.par_rho[c.R] = c.rho;
        sh.par_wit[c.R] = t;
        int mx = 0;
        for (int i = 1; i <= 64; i++) mx = std::max(mx, sh.par_rho[i]);
        sh.par_max = mx;
    }
    if (c.total < sh.best_total) {
        sh.best_total = c.total;
        sh.best = t;
        if (!sh.opt->quiet)
            fprintf(stderr, "[search n=%d] %.1fs  total %d = R %d + rho %d   (thread %d restart %ld, %s)\n", n,
                    sec_now() - sh.t0, c.total, c.R, c.rho, thread, restart, how);
        if (sh.opt->target >= 0 && c.total <= sh.opt->target) sh.stop = true;
    }
    return c;
}

static void init_terms(TermState& s, Rng& g, int kind) {
    int n = s.n, R = s.R;
    unsigned mask = (1u << n) - 1;
    for (int r = 0; r < R; r++) memset(&s.t[r], 0, sizeof(Term));
    auto rank1 = [&](Term& t) {
        unsigned a, b, c, d;
        do { a = g.next() & mask; } while (!a);
        do { b = g.next() & mask; } while (!b);
        do { c = g.next() & mask; } while (!c);
        do { d = g.next() & mask; } while (!d);
        for (int i = 0; i < n; i++) {
            t.V[i] = (uint8_t)(((a >> i) & 1) ? d : 0);
            t.U[i] = (uint8_t)(((c >> i) & 1) ? b : 0);
        }
    };
    auto uniform = [&](Term& t) {
        for (int i = 0; i < n; i++) {
            t.V[i] = (uint8_t)(g.next() & mask);
            t.U[i] = (uint8_t)(g.next() & mask);
        }
    };
    auto perm = [&](uint8_t* A) {
        int p[NMAX];
        for (int i = 0; i < n; i++) p[i] = i;
        for (int i = n - 1; i > 0; i--) std::swap(p[i], p[g.below(i + 1)]);
        for (int i = 0; i < n; i++) A[i] = (uint8_t)(1u << p[i]);
    };
    if (kind % 8 >= 6) {
        // block seeds: n = k*mm (or k*mm + rest): terms E_ab (x) I_mm on both sides for random block positions
        // (the block construction uses all k^2 positions); remaining terms rank-one.
        int mm = 2 + (int)g.below(std::max(1, n / 2 - 1));
        if (kind % 8 == 7) {
            for (int tries = 0; tries < 8 && n % mm; tries++) mm = 2 + (int)g.below(std::max(1, n / 2 - 1));
        }
        int k = n / mm, r = 0;
        std::vector<int> pos;
        for (int a = 0; a < k; a++)
            for (int b = 0; b < k; b++) pos.push_back(a * k + b);
        for (int i = (int)pos.size() - 1; i > 0; i--) std::swap(pos[i], pos[g.below(i + 1)]);
        for (size_t q = 0; q < pos.size() && r < R; q++, r++) {
            int a = pos[q] / k, b = pos[q] % k;
            for (int i = 0; i < mm; i++) {
                s.t[r].V[a * mm + i] = (uint8_t)(1u << (b * mm + i));
                s.t[r].U[a * mm + i] = (uint8_t)(1u << (b * mm + i));
            }
        }
        for (; r < R; r++) rank1(s.t[r]);
        s.rebuild();
        return;
    }
    switch (kind % 8) {
        case 0:  // uniform random
            for (int r = 0; r < R; r++) uniform(s.t[r]);
            break;
        case 1:  // the transpose term + random rank-one terms
            mat_ident(n, s.t[0].V);
            mat_ident(n, s.t[0].U);
            for (int r = 1; r < R; r++) rank1(s.t[r]);
            break;
        case 2:  // permutation-type map X -> P X^T Q, rest uniform
            perm(s.t[0].V);
            perm(s.t[0].U);
            for (int r = 1; r < R; r++) uniform(s.t[r]);
            break;
        case 3:  // all rank-one
            for (int r = 0; r < R; r++) rank1(s.t[r]);
            break;
        case 4: {  // block-diagonal transposes: split n = n1 + n2 (+ ...), term q = identity on block q (both sides)
            int parts = std::min(R, 2 + (int)g.below(std::max(1, n - 2)));
            parts = std::min(parts, n);
            int cut[NMAX + 1];
            cut[0] = 0;
            for (int q = 1; q < parts; q++) cut[q] = cut[q - 1] + 1;
            cut[parts] = n;
            // random composition of n into `parts` positive parts
            for (int q = parts - 1; q >= 1; q--) cut[q] = 1 + (int)g.below(n - 1);
            std::sort(cut, cut + parts + 1);
            for (int q = 0; q < parts; q++)
                for (int i = cut[q]; i < cut[q + 1]; i++) {
                    s.t[q].V[i] = (uint8_t)(1u << i);
                    s.t[q].U[i] = (uint8_t)(1u << i);
                }
            for (int r = parts; r < R; r++) rank1(s.t[r]);
            break;
        }
        default:  // transpose conjugated by a random symmetric-ish pair: V = S, U = S^-T ... all invertible pairs
            for (int r = 0; r < R; r++) {
                if (r == 0) {
                    uint8_t S[NMAX], Si[NMAX];
                    mat_random_invertible(n, g, S);
                    mat_inv(n, S, Si);
                    memcpy(s.t[0].V, S, n);
                    mat_transpose(n, Si, s.t[0].U);
                } else
                    uniform(s.t[r]);
            }
            break;
    }
    s.rebuild();
}

static void terms_worker(Shared& sh, const SearchOpts& o, int thread) {
    TermState s;
    s.n = o.n;
    s.R = o.R;
    s.N = o.n * o.n;
    int n = o.n, R = o.R;
    long iters = o.iters > 0 ? o.iters : 20000L * n * R;
    double T0 = o.T0 > 0 ? o.T0 : 1.2, T1 = o.T1 > 0 ? o.T1 : 0.12;
    u64 evals = 0;
    for (long rs = 0; (o.restarts == 0 || rs < o.restarts) && !sh.stop.load(std::memory_order_relaxed); rs++) {
        Rng g(o.seed * 0x9e3779b97f4a7c15ull + (u64)thread * 1000003ull + (u64)rs * 7919ull + 17);
        init_terms(s, g, (int)(rs % 8));
        int cur = s.objective(o.lambda);
        int best_rho = cur;
        std::vector<Term> best_t(s.t, s.t + R);
        offer(sh, n, best_t, thread, rs, "terms-init");
        long since = 0;
        double lt0 = log(T0), lt1 = log(T1);
        struct Op {
            uint8_t side, r, i, dm;
        };
        Op ops[NMAX];
        for (long it = 0; it < iters; it++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)it / (double)iters);
            int nops = 0;
            uint32_t mv = g.below(100);
            int r = (int)g.below(R);
            if (mv < 78) {  // single bit
                ops[nops++] = Op{(uint8_t)g.below(2), (uint8_t)r, (uint8_t)g.below(n), (uint8_t)(1u << g.below(n))};
            } else if (mv < 88) {  // random mask into one row
                unsigned dm;
                do { dm = g.next() & ((1u << n) - 1); } while (!dm);
                ops[nops++] = Op{(uint8_t)g.below(2), (uint8_t)r, (uint8_t)g.below(n), (uint8_t)dm};
            } else {  // add a rank-one matrix a d^T to V_r or U_r
                unsigned a, d;
                do { a = g.next() & g.next() & ((1u << n) - 1); } while (!a);
                do { d = g.next() & g.next() & ((1u << n) - 1); } while (!d);
                uint8_t side = (uint8_t)g.below(2);
                for (int i = 0; i < n; i++)
                    if ((a >> i) & 1) ops[nops++] = Op{side, (uint8_t)r, (uint8_t)i, (uint8_t)d};
            }
            for (int k = 0; k < nops; k++) {
                if (ops[k].side) s.xorU(ops[k].r, ops[k].i, ops[k].dm);
                else s.xorV(ops[k].r, ops[k].i, ops[k].dm);
            }
            int c2 = s.objective(o.lambda);
            evals++;
            if (c2 <= cur || g.uni() < exp((double)(cur - c2) / T)) {
                if (c2 < cur) since = 0;
                cur = c2;
                if (cur < best_rho) {
                    best_rho = cur;
                    best_t.assign(s.t, s.t + R);
                    if (cur < sh.par_max.load(std::memory_order_relaxed)) offer(sh, n, best_t, thread, rs, "terms");
                }
            } else {
                for (int k = 0; k < nops; k++) {
                    if (ops[k].side) s.xorU(ops[k].r, ops[k].i, ops[k].dm);
                    else s.xorV(ops[k].r, ops[k].i, ops[k].dm);
                }
            }
            if (++since > 4000L * n) {  // stalled: re-base by a random symmetry (cost unchanged)
                random_rebase(s, g, true);
                since = 0;
            }
            if ((it & 4095) == 0) {
                if (sh.stop.load(std::memory_order_relaxed)) break;
                if (o.restarts == 0 && sec_now() - sh.t0 > o.time) {
                    sh.stop = true;
                    break;
                }
            }
        }
        {
            Cost c = cost_of(n, best_t.data(), R);
            std::lock_guard<std::mutex> lk(sh.mu);
            if (c.total >= 0 && c.total < 4 * 64 + 8) sh.hist[c.total]++;
        }
        sh.restarts.fetch_add(1);
    }
    sh.evals.fetch_add(evals);
}

// tabu search on the single-bit-flip neighbourhood: every step evaluates ALL 2 R n^2 flips and takes the best
// non-tabu one (ties at random); the flipped bit is tabu for a random tenure; aspiration when a flip beats the
// restart's best.  After `stall` steps without improvement: random symmetry re-base + a few random flips.
static void tabu_worker(Shared& sh, const SearchOpts& o, int thread) {
    TermState s;
    s.n = o.n;
    s.R = o.R;
    s.N = o.n * o.n;
    int n = o.n, R = o.R;
    long steps = o.iters > 0 ? o.iters : 3000L * n;
    u64 evals = 0;
    std::vector<long> tabu((size_t)R * 2 * n * n);
    struct Mv {
        uint8_t side, r, i, j;
    };
    std::vector<Mv> cand;
    for (long rs = 0; (o.restarts == 0 || rs < o.restarts) && !sh.stop.load(std::memory_order_relaxed); rs++) {
        Rng g(o.seed * 0x9e3779b97f4a7c15ull + (u64)thread * 1000003ull + (u64)rs * 7919ull + 41);
        init_terms(s, g, (int)(rs % 8));
        std::fill(tabu.begin(), tabu.end(), -1);
        int cur = s.objective(o.lambda);
        int best_rho = cur;
        std::vector<Term> best_t(s.t, s.t + R);
        offer(sh, n, best_t, thread, rs, "tabu-init");
        long since = 0;
        for (long st = 0; st < steps; st++) {
            int bc = 1 << 30;
            cand.clear();
            for (int r = 0; r < R; r++)
                for (int side = 0; side < 2; side++)
                    for (int i = 0; i < n; i++)
                        for (int j = 0; j < n; j++) {
                            if (side) s.xorU(r, i, 1u << j);
                            else s.xorV(r, i, 1u << j);
                            int c = s.objective(o.lambda);
                            if (side) s.xorU(r, i, 1u << j);
                            else s.xorV(r, i, 1u << j);
                            evals++;
                            bool istabu = tabu[(((size_t)r * 2 + side) * n + i) * n + j] > st;
                            if (istabu && c >= best_rho) continue;
                            if (c < bc) {
                                bc = c;
                                cand.clear();
                            }
                            if (c == bc) cand.push_back(Mv{(uint8_t)side, (uint8_t)r, (uint8_t)i, (uint8_t)j});
                        }
            if (cand.empty()) {
                std::fill(tabu.begin(), tabu.end(), -1);
                continue;
            }
            Mv m = cand[g.below((uint32_t)cand.size())];
            if (m.side) s.xorU(m.r, m.i, 1u << m.j);
            else s.xorV(m.r, m.i, 1u << m.j);
            cur = bc;
            tabu[(((size_t)m.r * 2 + m.side) * n + m.i) * n + m.j] = st + 4 + g.below((uint32_t)(n * R + 4));
            if (cur < best_rho) {
                best_rho = cur;
                best_t.assign(s.t, s.t + R);
                offer(sh, n, best_t, thread, rs, "tabu");
                since = 0;
            } else if (++since > 60L * n) {
                // kick: random symmetry re-base (cost unchanged) and a few random flips
                random_rebase(s, g, true);
                int kicks = 1 + (int)g.below(3);
                for (int k = 0; k < kicks; k++) {
                    if (g.below(2)) s.xorU((int)g.below(R), (int)g.below(n), 1u << g.below(n));
                    else s.xorV((int)g.below(R), (int)g.below(n), 1u << g.below(n));
                }
                std::fill(tabu.begin(), tabu.end(), -1);
                cur = s.objective(o.lambda);
                since = 0;
            }
            if (sh.stop.load(std::memory_order_relaxed)) break;
            if (o.restarts == 0 && (st & 15) == 0 && sec_now() - sh.t0 > o.time) {
                sh.stop = true;
                break;
            }
        }
        {
            Cost c = cost_of(n, best_t.data(), R);
            std::lock_guard<std::mutex> lk(sh.mu);
            if (c.total >= 0 && c.total < 4 * 64 + 8) sh.hist[c.total]++;
        }
        sh.restarts.fetch_add(1);
    }
    sh.evals.fetch_add(evals);
}

// --------------------------------------------------------------------------------------------- pure mode
struct PureState {
    int n, N;
    u64 A[64], B[64];
    void from_terms(const Term* t, int R) {
        phi_rows(n, t, R, A);
        for (int k = 0; k < N; k++) A[k] ^= 1ull << k;
        for (int k = 0; k < N; k++) B[k] = 0;
        for (int r = 0; r < R; r++) {
            u64 vv = 0;
            for (int a = 0; a < n; a++) vv |= (u64)t[r].V[a] << (a * n);
            for (int a = 0; a < n; a++)
                for (int b = 0; b < n; b++)
                    if ((t[r].U[a] >> b) & 1) B[a * n + b] ^= vv;
        }
    }
    // spread(a) * b = a (x) b as an n^2-bit vector with index i1*n + i2
    inline u64 kron(unsigned a, unsigned b) const {
        u64 s = 0;
        while (a) {
            int i = __builtin_ctz(a);
            a &= a - 1;
            s |= (u64)b << (i * n);
        }
        return s;
    }
    inline void move(unsigned a, unsigned b, unsigned c, unsigned d) {
        // A += (a(x)b)(c(x)d)^T ; B += (c(x)b)(a(x)d)^T
        u64 x = kron(a, b), y = kron(c, d);
        while (x) {
            int i = __builtin_ctzll(x);
            x &= x - 1;
            A[i] ^= y;
        }
        u64 xb = kron(c, b), yb = kron(a, d);
        while (xb) {
            int i = __builtin_ctzll(xb);
            xb &= xb - 1;
            B[i] ^= yb;
        }
    }
    inline int rankA() const {
        u64 tmp[64];
        memcpy(tmp, A, (size_t)N * 8);
        return rank_rows(tmp, N);
    }
    inline int rankB() const {
        u64 tmp[64];
        memcpy(tmp, B, (size_t)N * 8);
        return rank_rows(tmp, N);
    }
    // read rank(B) terms off B:  B = sum_r vec(U_r) vec(V_r)^T
    void to_terms(std::vector<Term>& out) const {
        // reduced row echelon basis of the row space
        u64 basis[64];
        int piv[64], k = 0;
        u64 rows[64];
        memcpy(rows, B, (size_t)N * 8);
        for (int i = 0; i < N; i++) {
            u64 v = rows[i];
            for (int q = 0; q < k; q++)
                if ((v >> piv[q]) & 1) v ^= basis[q];
            if (!v) continue;
            int p = __builtin_ctzll(v);
            for (int q = 0; q < k; q++)
                if ((basis[q] >> p) & 1) basis[q] ^= v;
            basis[k] = v;
            piv[k] = p;
            k++;
        }
        out.clear();
        unsigned mask = (1u << n) - 1;
        for (int q = 0; q < k; q++) {
            Term t;
            memset(&t, 0, sizeof t);
            for (int a = 0; a < n; a++) t.V[a] = (uint8_t)((basis[q] >> (a * n)) & mask);
            for (int a = 0; a < n; a++)
                for (int b = 0; b < n; b++)
                    if ((B[a * n + b] >> piv[q]) & 1) t.U[a] |= (uint8_t)(1u << b);
            out.push_back(t);
        }
    }
};

static void pure_worker(Shared& sh, const SearchOpts& o, int thread, const std::vector<Term>* init) {
    PureState s;
    s.n = o.n;
    s.N = o.n * o.n;
    int n = o.n, N = s.N;
    unsigned mask = (1u << n) - 1;
    long iters = o.iters > 0 ? o.iters : 200000L * n * n;
    double T0 = o.T0 > 0 ? o.T0 : 0.9, T1 = o.T1 > 0 ? o.T1 : 0.18;
    u64 evals = 0;
    std::vector<Term> tt;
    for (long rs = 0; (o.restarts == 0 || rs < o.restarts) && !sh.stop.load(std::memory_order_relaxed); rs++) {
        Rng g(o.seed * 0x9e3779b97f4a7c15ull + (u64)thread * 1000003ull + (u64)rs * 7919ull + 29);
        // start: given terms, or B = 0 (A = I), or the transpose solution
        if (init && !init->empty()) s.from_terms(init->data(), (int)init->size());
        else if (rs % 3 == 0) s.from_terms(nullptr, 0);
        else {
            Term t;
            memset(&t, 0, sizeof t);
            if (rs % 3 == 1) {
                mat_ident(n, t.V);
                mat_ident(n, t.U);
            } else {
                for (int i = 0; i < n; i++) {
                    t.V[i] = (uint8_t)(g.next() & mask);
                    t.U[i] = (uint8_t)(g.next() & mask);
                }
            }
            s.from_terms(&t, 1);
        }
        int ra = s.rankA(), rb = s.rankB();
        s.to_terms(tt);
        offer(sh, n, tt, thread, rs, "pure-init");
        auto obj = [&](int a, int b) {
            double v = o.wA * a + o.wB * b;
            if (o.rmaxpure >= 0 && b > o.rmaxpure) v += 2.0 * (b - o.rmaxpure);
            return v;
        };
        double cur = obj(ra, rb);
        int best_total = ra + rb;
        double lt0 = log(T0), lt1 = log(T1);
        for (long it = 0; it < iters; it++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)it / (double)iters);
            unsigned a, b, c, d;
            do { a = g.next() & mask; } while (!a);
            do { b = g.next() & mask; } while (!b);
            do { c = g.next() & mask; } while (!c);
            do { d = g.next() & mask; } while (!d);
            s.move(a, b, c, d);
            int na = s.rankA(), nb = s.rankB();
            double c2 = obj(na, nb);
            evals++;
            if (c2 <= cur || g.uni() < exp((cur - c2) / T)) {
                cur = c2;
                ra = na;
                rb = nb;
                if (ra + rb < best_total) {
                    best_total = ra + rb;
                    if (best_total < sh.best_total) {
                        s.to_terms(tt);
                        offer(sh, n, tt, thread, rs, "pure");
                    }
                }
            } else
                s.move(a, b, c, d);
            if ((it & 4095) == 0) {
                if (sh.stop.load(std::memory_order_relaxed)) break;
                if (o.restarts == 0 && sec_now() - sh.t0 > o.time) {
                    sh.stop = true;
                    break;
                }
            }
        }
        {
            std::lock_guard<std::mutex> lk(sh.mu);
            if (best_total >= 0 && best_total < 4 * 64 + 8) sh.hist[best_total]++;
        }
        sh.restarts.fetch_add(1);
        (void)N;
    }
    sh.evals.fetch_add(evals);
}

// ---------------------------------------------------------------------------------------------
static int cmd_search(int argc, char** argv, int default_threads) {
    SearchOpts o;
    o.threads = default_threads;
    if (argc < 3) {
        fprintf(stderr, "usage: ptrank search N --R r [-j T] [--time S] [--seed X] [--target t] [--out FILE]\n"
                        "                     [--mode terms|pure] [--iters I] [--restarts K] [--T0 x] [--T1 y] [--init FILE.json]\n");
        return 2;
    }
    o.n = atoi(argv[2]);
    bool mode_given = false;
    for (int i = 3; i < argc; i++) {
        std::string a = argv[i];
        auto need = [&](const char* nm) {
            if (i + 1 >= argc) {
                fprintf(stderr, "missing value for %s\n", nm);
                exit(2);
            }
            return argv[++i];
        };
        if (a == "--R") o.R = atoi(need("--R"));
        else if (a == "-j") o.threads = atoi(need("-j"));
        else if (a == "--time") o.time = atof(need("--time"));
        else if (a == "--seed") o.seed = strtoull(need("--seed"), 0, 10);
        else if (a == "--target") o.target = atoi(need("--target"));
        else if (a == "--out") o.out = need("--out");
        else if (a == "--mode") o.mode = need("--mode"), mode_given = true;
        else if (a == "--iters") o.iters = atol(need("--iters"));
        else if (a == "--restarts") o.restarts = atol(need("--restarts"));
        else if (a == "--T0") o.T0 = atof(need("--T0"));
        else if (a == "--T1") o.T1 = atof(need("--T1"));
        else if (a == "--wA") o.wA = atof(need("--wA"));
        else if (a == "--wB") o.wB = atof(need("--wB"));
        else if (a == "--rmax") o.rmaxpure = atoi(need("--rmax"));
        else if (a == "--init") o.init = need("--init");
        else if (a == "--algo") o.algo = need("--algo");
        else if (a == "--lambda") o.lambda = atoi(need("--lambda"));
        else if (a == "--nostrict") o.lambda = 0;
        else if (a == "--pareto-dir") o.pareto_dir = need("--pareto-dir");
        else if (a == "--quiet") o.quiet = true;
        else {
            fprintf(stderr, "unknown option %s\n", a.c_str());
            return 2;
        }
    }
    if (o.n < 2 || o.n > NMAX) {
        fprintf(stderr, "search: need 2 <= N <= 8\n");
        return 2;
    }
    if (o.R < 0 && !mode_given) o.mode = "pure";
    if (o.mode == "terms" && (o.R < 1 || o.R > RMAX)) {
        fprintf(stderr, "search --mode terms: need 1 <= R <= %d\n", RMAX);
        return 2;
    }
    std::vector<Term> init;
    if (!o.init.empty()) {
        std::string s, err;
        Witness w;
        if (!read_file(o.init.c_str(), s) || !parse_witness(s, w, err) || w.n != o.n) {
            fprintf(stderr, "search: cannot use --init %s (%s)\n", o.init.c_str(), err.c_str());
            return 2;
        }
        init = w.terms;
    }
    Shared sh;
    sh.opt = &o;
    sh.t0 = sec_now();
    std::vector<std::thread> th;
    for (int i = 0; i < o.threads; i++) {
        if (o.mode == "pure") th.emplace_back(pure_worker, std::ref(sh), std::cref(o), i, &init);
        else if (o.algo == "tabu") th.emplace_back(tabu_worker, std::ref(sh), std::cref(o), i);
        else th.emplace_back(terms_worker, std::ref(sh), std::cref(o), i);
    }
    for (auto& t : th) t.join();
    double dt = sec_now() - sh.t0;
    fprintf(stderr, "[search n=%d mode=%s algo=%s R=%d] %.1fs, %d threads, %llu restarts, %.3g evals (%.3g evals/s/core)\n", o.n,
            o.mode.c_str(), o.algo.c_str(), o.R, dt, o.threads, (unsigned long long)sh.restarts.load(), (double)sh.evals.load(),
            sh.evals.load() / dt / o.threads);
    fprintf(stderr, "  best total per restart:");
    for (int k = 0; k < 4 * 64 + 8; k++)
        if (sh.hist[k]) fprintf(stderr, "  %d: %ld", k, sh.hist[k]);
    fprintf(stderr, "\n");
    if (sh.best.empty() && sh.best_total == (1 << 30)) {
        printf("RESULT search n=%d: nothing found\n", o.n);
        return 1;
    }
    Cost c = cost_of(o.n, sh.best.data(), (int)sh.best.size());
    printf("RESULT search n=%d: best total %d = R %d + rho %d   (trivial 1+C(n,2) = %d; (7/16) n^2 = %.2f)  UPPER BOUND ONLY\n",
           o.n, c.total, c.R, c.rho, 1 + o.n * (o.n - 1) / 2, 7.0 * o.n * o.n / 16);
    printf("%s\n", witness_json(o.n, sh.best).c_str());
    // Pareto table over exact rank(B): smallest rank(A) seen (heuristic, upper bounds only)
    for (int r = 0; r <= 64; r++) {
        if (sh.par_rho[r] >= (1 << 30)) continue;
        bool dominated = false;
        for (int q = 0; q < r; q++)
            if (sh.par_rho[q] <= sh.par_rho[r]) dominated = true;
        Cost pc = cost_of(o.n, sh.par_wit[r].data(), (int)sh.par_wit[r].size());
        printf("PARETO n=%d rank(B)=%d: min rank(A) found %d (total %d)%s  %s\n", o.n, pc.R, pc.rho, pc.total,
               dominated ? " [dominated]" : "", witness_json(o.n, sh.par_wit[r]).c_str());
        if (!o.pareto_dir.empty()) {
            std::string fn = o.pareto_dir + "/pareto_n" + std::to_string(o.n) + "_R" + std::to_string(pc.R) + "_rho" +
                             std::to_string(pc.rho) + ".json";
            FILE* f = fopen(fn.c_str(), "w");
            if (f) {
                fprintf(f, "%s\n", witness_json(o.n, sh.par_wit[r]).c_str());
                fclose(f);
            }
        }
    }
    if (!o.out.empty()) {
        FILE* f = fopen(o.out.c_str(), "w");
        if (f) {
            fprintf(f, "%s\n", witness_json(o.n, sh.best).c_str());
            fclose(f);
        }
    }
    return 0;
}
