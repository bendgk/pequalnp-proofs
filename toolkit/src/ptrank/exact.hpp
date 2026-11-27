// ptrank exact: exhaustive search for  A + B^{T1} = I  with rank(A) <= rho, rank(B) <= R  over GF(2).
//
// Formulation ("slices").  Write A = sum_{k<rho} vec(A_k) vec(B_k)^T and B^{T1} = (X -> sum_{r<R} V_r X^T U_r).
// With (a,b,c,d) = (i1,i2,j1,j2) the identity A + B^{T1} = I reads, entry by entry,
//      sum_k A_k[a,b] B_k[c,d] + sum_r V_r[a,d] U_r[c,b] = [a=c][b=d]                 (*)
// Row a of the "left" matrices is one vector  l_a = (A_k[a,.])_k , (V_r[a,.])_r  in GF(2)^m, m = n(rho+R);
// row c of the "right" matrices is            r_c = (B_k[c,.])_k , (U_r[c,.])_r  in GF(2)^m.
// (*) says  beta(l_a, r_c) = [a=c] * I_n  for a fixed bilinear map beta : GF(2)^m x GF(2)^m -> M_n:
//      beta(l,r)[b,d] = sum_k l[k,b] r[k,d] + sum_r l[rho+r,d] r[rho+r,b].
// Every pair (A, B) with rank(A) <= rho, rank(B) <= R has such a representation (pad with zero terms), so
// "no (l_0..l_{n-1}, r_0..r_{n-1}) satisfies (*)"  <=>  "no decomposition with rank(A) <= rho and rank(B) <= R".
//
// Search: depth-first in the order l_0, r_0, l_1, r_1, ...  Given the r's chosen so far, the admissible l_a form
// a linear space (kernel of the equations beta(., r_c) = 0, c < a); given the l's, the admissible r_a form an
// affine space (beta(l_c, r_a) = [a=c] I, c <= a).  Both are enumerated completely (Gray code).  Prunings, all
// of them necessary conditions for a solution:
//   - the affine system for r_a must be consistent;
//   - l_{a+1..n-1} are linearly independent members of the kernel of the l-system, so its dimension must be
//     >= n-1-a (same for the r-system).  (Independence: sum_a x_a l_a = 0 gives x_c I = beta(0, r_c) = 0.)
// Symmetry (used ONLY for l_0, unless --orbits): for invertible Q in GL_n, G in GL_rho, H in GL_R the substitution
//      A_k[a,.] -> sum_k' G[k,k'] Q A_k'[a,.],   B_k[c,.] -> sum_k' G^-T[k,k'] Q^-T B_k'[c,.],
//      V_r[a,.] -> sum_r' H[r,r'] Q^-T V_r'[a,.], U_r[c,.] -> sum_r' H^-T[r,r'] Q U_r'[c,.]
// maps solutions of (*) to solutions (it is the (P,Q) symmetry of the brief with P = 1, plus recombination of
// the terms of A and of B).  Under it l_0 = (alpha, nu), alpha = n x rho matrix with columns A_k[0,.], nu = n x R
// with columns V_r[0,.], moves as (alpha, nu) -> (Q alpha G^T, Q^-T nu H^T), and the orbits are classified by
// (s, t, p) = (rank alpha, rank nu, rank nu^T alpha), max(0, s+t-n) <= p <= min(s,t), with representative
//      alpha = [e_0 .. e_{s-1} 0 ..],   nu = [e_0 .. e_{p-1}  e_s .. e_{s+t-p-1}  0 ..].
// `exact ... --count` checks this numerically: the number of solutions computed with one representative per
// class times the class size equals the number computed with no symmetry at all (see docs/ptrank.md).
#pragma once
#include "core.hpp"
#include <algorithm>
#include <atomic>
#include <chrono>
#include <mutex>
#include <thread>

struct LinSys {
    u64 basis[64];
    uint8_t rhs[64];
    u64 has;
    uint8_t bad;
    void clear() {
        has = 0;
        bad = 0;
    }
    inline void insert(u64 c, uint8_t rh) {
        while (c) {
            int p = __builtin_ctzll(c);
            if (!((has >> p) & 1)) {
                basis[p] = c;
                rhs[p] = rh;
                has |= 1ull << p;
                return;
            }
            c ^= basis[p];
            rh ^= rhs[p];
        }
        bad |= rh;
    }
    inline int rank() const { return popc(has); }
};

static inline void linsys_copy(LinSys& d, const LinSys& s, int m) {
    memcpy(d.basis, s.basis, (size_t)m * 8);
    memcpy(d.rhs, s.rhs, (size_t)m);
    d.has = s.has;
    d.bad = s.bad;
}

static inline int linsys_kernel(const LinSys& S, int m, u64* K) {
    int d = 0;
    for (int f = 0; f < m; f++) {
        if ((S.has >> f) & 1) continue;
        u64 x = 1ull << f;
        for (int p = f - 1; p >= 0; p--)
            if (((S.has >> p) & 1) && par(S.basis[p] & x)) x |= 1ull << p;
        K[d++] = x;
    }
    return d;
}
static inline u64 linsys_particular(const LinSys& S, int m, int c) {
    u64 x = 0;
    for (int p = m - 1; p >= 0; p--)
        if ((S.has >> p) & 1)
            if (((S.rhs[p] >> c) & 1) ^ par(S.basis[p] & x)) x |= 1ull << p;
    return x;
}

static std::string u128_str(u128 v) {
    if (v == 0) return "0";
    std::string s;
    while (v) {
        s += (char)('0' + (int)(v % 10));
        v /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

struct ExactOpts {
    int n = 0, R = 0, rho = 0, threads = 1;
    bool count = false, nosym = false, quiet = false, orbits = false;
    long maxsol = 1;  // stop after the first solution unless counting
    double progress_every = 10.0;
};

struct ExactResult {
    bool found = false;
    bool complete = false;
    std::vector<Term> witness;
    std::vector<std::vector<Term>> witnesses;  // --all-classes: first witness of every l_0 class that has one
    u128 count = 0;        // --count: number of solutions (l, r) (with class weights, if symmetry was used)
    bool count_weighted = false;
    u64 cand_l[NMAX], pass_l[NMAX], cand_r[NMAX];
    long classes = 0, tasks = 0;
    double seconds = 0;
    std::string class_report;
};

struct ExactClass {
    int s, t, p;
    u64 l0;
    u128 orbit = 0;  // number of (alpha, nu) in the class (only computed when counting and m is small)
    u128 count = 0;
    bool has_r0 = false;
    bool sat = false;
    long r0_dim = -1;
    long r0_orbits = -1;
};

struct Exact {
    int n, rho, R, K, m;
    u64 SA, SV;
    ExactOpts opt;

    Exact(const ExactOpts& o) : opt(o) {
        n = o.n;
        rho = o.rho;
        R = o.R;
        K = rho + R;
        m = n * K;
        SA = 0;
        SV = 0;
        for (int k = 0; k < rho; k++) SA |= 1ull << (k * n);
        for (int r = 0; r < R; r++) SV |= 1ull << ((rho + r) * n);
    }

    // equations of beta(x, .) : E[b*n+d] is the coefficient mask of the (b,d) entry.
    // By symmetry of beta's formula the same function gives beta(., y) with (b,d) swapped; since the right-hand
    // side [b=d] is symmetric we use it for both sides.
    inline void equations(u64 x, u64* E) const {
        u64 ca[NMAX], cv[NMAX];
        for (int b = 0; b < n; b++) {
            ca[b] = (x >> b) & SA;
            cv[b] = (x >> b) & SV;
        }
        for (int b = 0; b < n; b++)
            for (int d = 0; d < n; d++) E[b * n + d] = (ca[b] << d) | (cv[d] << b);
    }
    // beta(l, r) as n row masks: bit d of row b
    inline void beta(u64 l, u64 r, uint8_t* out) const {
        u64 E[64];
        equations(l, E);
        for (int b = 0; b < n; b++) {
            uint8_t row = 0;
            for (int d = 0; d < n; d++) row |= (uint8_t)(par(E[b * n + d] & r) << d);
            out[b] = row;
        }
    }
    // insert the equations of x into S with right-hand side bit `idx` on the diagonal; returns false if bad
    inline bool add(LinSys& S, u64 x, int idx) const {
        u64 ca[NMAX], cv[NMAX];
        for (int b = 0; b < n; b++) {
            ca[b] = (x >> b) & SA;
            cv[b] = (x >> b) & SV;
        }
        uint8_t diag = (uint8_t)(1u << idx);
        for (int b = 0; b < n; b++)
            for (int d = 0; d < n; d++) {
                S.insert((ca[b] << d) | (cv[d] << b), b == d ? diag : (uint8_t)0);
                if (S.bad) return false;
            }
        return true;
    }

    void classify(u64 l, int& s, int& t, int& p) const {
        // alpha columns = A_k[0,.] (n-bit masks), nu columns = V_r[0,.]
        u64 a[64], v[64], g[64];
        u64 mask = (1ull << n) - 1;
        for (int k = 0; k < rho; k++) a[k] = (l >> (k * n)) & mask;
        for (int r = 0; r < R; r++) v[r] = (l >> ((rho + r) * n)) & mask;
        for (int r = 0; r < R; r++) {
            u64 row = 0;
            for (int k = 0; k < rho; k++) row |= (u64)par(a[k] & v[r]) << k;
            g[r] = row;
        }
        s = rank_rows(a, rho);
        t = rank_rows(v, R);
        p = rank_rows(g, R);
    }
    u64 class_rep(int s, int t, int p) const {
        u64 l = 0;
        for (int k = 0; k < s; k++) l |= 1ull << (k * n + k);
        for (int r = 0; r < p; r++) l |= 1ull << ((rho + r) * n + r);
        for (int r = p; r < t; r++) l |= 1ull << ((rho + r) * n + (s + r - p));
        return l;
    }

    void to_terms(const u64* l, const u64* r, std::vector<Term>& out) const {
        out.clear();
        for (int q = 0; q < R; q++) {
            Term t;
            memset(&t, 0, sizeof t);
            u64 mask = (1ull << n) - 1;
            for (int a = 0; a < n; a++) {
                t.V[a] = (uint8_t)((l[a] >> ((rho + q) * n)) & mask);  // V_q[a][d]
                t.U[a] = (uint8_t)((r[a] >> ((rho + q) * n)) & mask);  // U_q[c][b]
            }
            out.push_back(t);
        }
    }

    // ---------------------------------------------------------------- search
    struct Worker {
        const Exact* E;
        u64 l[NMAX], r[NMAX];
        u64 cand_l[NMAX], pass_l[NMAX], cand_r[NMAX];
        u128 count = 0;
        long nsol = 0;
        bool stop = false;
        long task = 0;
        std::vector<Term> witness;
        bool have_witness = false;
        std::atomic<long>* best_task = nullptr;
        u64 tick = 0;
        Worker() {
            memset(cand_l, 0, sizeof cand_l);
            memset(pass_l, 0, sizeof pass_l);
            memset(cand_r, 0, sizeof cand_r);
        }
    };

    inline bool should_abort(Worker& w) const {
        if (w.stop) return true;
        if (!opt.count && ((++w.tick & 1023) == 0) && w.best_task->load(std::memory_order_relaxed) < w.task) {
            w.stop = true;
            return true;
        }
        return false;
    }

    // r_a ranges over the solutions of Rs (rhs index a)
    void rec_r(Worker& w, int a, const LinSys& Ls, const LinSys& Rs) const {
        u64 Kb[64];
        int d = linsys_kernel(Rs, m, Kb);
        u64 x0 = linsys_particular(Rs, m, a);
        if (a == n - 1) {
            w.cand_r[a] += 1;
            if (opt.count) {
                w.count += (u128)1 << d;
                return;
            }
            w.r[a] = x0;
            if (!w.have_witness) {
                to_terms(w.l, w.r, w.witness);
                w.have_witness = true;
            }
            w.nsol++;
            w.stop = true;
            return;
        }
        u64 x = x0;
        LinSys L2;
        for (u64 i = 0;; i++) {
            w.cand_r[a]++;
            w.r[a] = x;
            linsys_copy(L2, Ls, m);
            add(L2, x, a);  // never inconsistent for the l's already chosen
            if (m - L2.rank() >= n - 1 - a) rec_l(w, a + 1, L2, Rs);
            if (should_abort(w)) return;
            u64 nx = i + 1;
            if (nx >> d) break;
            x ^= Kb[__builtin_ctzll(nx)];
        }
    }

    // l_a ranges over the kernel of Ls
    void rec_l(Worker& w, int a, const LinSys& Ls, const LinSys& Rs) const {
        u64 Kb[64];
        int d = linsys_kernel(Ls, m, Kb);
        if (d < n - a) return;
        u64 x = 0;
        LinSys R2;
        for (u64 i = 1; !(i >> d); i++) {
            x ^= Kb[__builtin_ctzll(i)];
            w.cand_l[a]++;
            linsys_copy(R2, Rs, m);
            if (!add(R2, x, a)) continue;
            if (m - R2.rank() < n - 1 - a) continue;
            w.pass_l[a]++;
            w.l[a] = x;
            rec_r(w, a + 1 - 1, Ls, R2);
            if (should_abort(w)) return;
        }
    }

    ExactResult run();
};

// ------------------------------------------------------------------------------------------------------------
inline ExactResult Exact::run() {
    auto t0 = std::chrono::steady_clock::now();
    ExactResult res;
    memset(res.cand_l, 0, sizeof res.cand_l);
    memset(res.pass_l, 0, sizeof res.pass_l);
    memset(res.cand_r, 0, sizeof res.cand_r);
    if (n < 2 || n > NMAX || m > 64 || rho < 0 || R < 0) {
        fprintf(stderr, "exact: need 2 <= n <= 8 and n*(R+rho) <= 64 (got n=%d R=%d rho=%d)\n", n, R, rho);
        exit(2);
    }
    if (m == 0) {  // A = B = 0 is not the identity
        res.complete = true;
        return res;
    }
    std::vector<ExactClass> cls;
    struct ClsData {
        LinSys Rs0;
        u64 x0;
        u64 K0[64];
        int d0;
        u64 first;  // global index of this class's first task
        u64 ntasks;
        std::vector<u64> reps;  // --orbits: representatives (as r_0 vectors)
    };
    std::vector<ClsData> cd;
    u64 total_tasks = 0;
    if (!opt.nosym) {
        for (int s = 0; s <= std::min(n, rho); s++)
            for (int t = 0; t <= std::min(n, R); t++)
                for (int p = std::max(0, s + t - n); p <= std::min(s, t); p++) {
                    ExactClass c;
                    c.s = s;
                    c.t = t;
                    c.p = p;
                    c.l0 = class_rep(s, t, p);
                    int s2, t2, p2;
                    classify(c.l0, s2, t2, p2);
                    if (s2 != s || t2 != t || p2 != p) {
                        fprintf(stderr, "internal error: class representative is not in its class\n");
                        exit(3);
                    }
                    cls.push_back(c);
                }
        if (opt.count && m <= 30) {  // class sizes by brute force over all (alpha, nu)
            std::vector<u128> sz(cls.size(), 0);
            for (u64 l = 0; l < (1ull << m); l++) {
                int s, t, p;
                classify(l, s, t, p);
                for (size_t i = 0; i < cls.size(); i++)
                    if (cls[i].s == s && cls[i].t == t && cls[i].p == p) {
                        sz[i] += 1;
                        break;
                    }
            }
            u128 sum = 0;
            for (size_t i = 0; i < cls.size(); i++) {
                cls[i].orbit = sz[i];
                sum += sz[i];
            }
            if (sum != ((u128)1 << m)) {
                fprintf(stderr, "internal error: classes do not partition the l_0 space\n");
                exit(3);
            }
            res.count_weighted = true;
        }
        cd.resize(cls.size());
        for (size_t i = 0; i < cls.size(); i++) {
            ClsData& D = cd[i];
            D.Rs0.clear();
            D.first = total_tasks;
            D.ntasks = 0;
            D.d0 = -1;
            if (!add(D.Rs0, cls[i].l0, 0)) continue;  // no r_0 at all
            D.d0 = linsys_kernel(D.Rs0, m, D.K0);
            D.x0 = linsys_particular(D.Rs0, m, 0);
            cls[i].has_r0 = true;
            cls[i].r0_dim = D.d0;
            D.ntasks = 1ull << D.d0;
            total_tasks += D.ntasks;
        }
    } else {
        total_tasks = 1ull << m;
        res.count_weighted = false;
    }
    res.classes = (long)cls.size();
    res.tasks = (long)total_tasks;

    std::atomic<u64> next{0};
    std::atomic<long> best_task{INT64_MAX};
    std::atomic<u64> done{0};
    std::mutex mu;
    std::vector<Term> best_witness;
    long best_witness_task = INT64_MAX;
    int T = std::max(1, opt.threads);
    std::vector<Worker> ws(T);
    std::vector<std::vector<u128>> cls_count(T, std::vector<u128>(cls.size() + 1, 0));
    std::vector<std::vector<char>> cls_sat(T, std::vector<char>(cls.size() + 1, 0));

    auto work = [&](int ti) {
        Worker& w = ws[ti];
        w.E = this;
        w.best_task = &best_task;
        const u64 CH = 16;
        for (;;) {
            u64 lo = next.fetch_add(CH);
            if (lo >= total_tasks) break;
            u64 hi = std::min(total_tasks, lo + CH);
            for (u64 g = lo; g < hi; g++) {
                if (!opt.count && best_task.load() < (long)g) {
                    done.fetch_add(1, std::memory_order_relaxed);
                    continue;
                }
                w.task = (long)g;
                w.stop = false;
                w.have_witness = false;
                u128 before = w.count;
                size_t ci = cls.size();
                LinSys Ls, Rs;
                Ls.clear();
                if (opt.nosym) {
                    u64 l0 = g;
                    Rs.clear();
                    w.l[0] = l0;
                    w.cand_l[0]++;
                    if (add(Rs, l0, 0) && m - Rs.rank() >= n - 1) {
                        w.pass_l[0]++;
                        rec_r(w, 0, Ls, Rs);
                    }
                } else {
                    // locate the class
                    ci = 0;
                    while (ci + 1 < cls.size() && cd[ci + 1].first <= g) ci++;
                    while (cd[ci].ntasks == 0 || g < cd[ci].first || g >= cd[ci].first + cd[ci].ntasks) ci++;
                    const ClsData& D = cd[ci];
                    u64 j = g - D.first;
                    u64 r0 = D.x0;
                    for (u64 jj = j; jj; jj &= jj - 1) r0 ^= D.K0[__builtin_ctzll(jj)];
                    w.l[0] = cls[ci].l0;
                    w.r[0] = r0;
                    w.cand_r[0]++;
                    add(Ls, r0, 0);
                    if (m - D.Rs0.rank() >= n - 1 && m - Ls.rank() >= n - 1) rec_l(w, 1, Ls, D.Rs0);
                }
                cls_count[ti][ci] += w.count - before;
                if (w.have_witness) {
                    cls_sat[ti][ci] = 1;
                    std::lock_guard<std::mutex> lk(mu);
                    if ((long)g < best_witness_task) {
                        best_witness_task = (long)g;
                        best_witness = w.witness;
                    }
                    long cur = best_task.load();
                    while ((long)g < cur && !best_task.compare_exchange_weak(cur, (long)g)) {
                    }
                }
                done.fetch_add(1, std::memory_order_relaxed);
            }
        }
    };
    std::vector<std::thread> th;
    for (int i = 0; i < T; i++) th.emplace_back(work, i);
    {
        double last = 0;
        while (done.load() < total_tasks) {
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
            double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            if (!opt.quiet && el - last >= opt.progress_every) {
                last = el;
                fprintf(stderr, "[exact n=%d R<=%d rho<=%d] %.0fs  tasks %llu/%llu%s\n", n, R, rho, el,
                        (unsigned long long)done.load(), (unsigned long long)total_tasks,
                        best_task.load() != INT64_MAX ? "  (solution found)" : "");
            }
        }
    }
    for (auto& t : th) t.join();
    for (int i = 0; i < T; i++) {
        for (int a = 0; a < NMAX; a++) {
            res.cand_l[a] += ws[i].cand_l[a];
            res.pass_l[a] += ws[i].pass_l[a];
            res.cand_r[a] += ws[i].cand_r[a];
        }
        for (size_t c = 0; c < cls.size(); c++) {
            cls[c].count += cls_count[i][c];
            if (cls_sat[i][c]) cls[c].sat = true;
        }
        if (opt.nosym) res.count += cls_count[i][cls.size()];
    }
    if (!opt.nosym && opt.count) {
        for (auto& c : cls) res.count += res.count_weighted ? c.count * c.orbit : c.count;
    }
    res.found = best_witness_task != INT64_MAX;
    if (res.found) res.witness = best_witness;
    res.complete = true;
    res.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::string rep;
    for (auto& c : cls) {
        char buf[256];
        snprintf(buf, sizeof buf, "  class (s=%d,t=%d,p=%d): r_0 candidates %s", c.s, c.t, c.p,
                 c.has_r0 ? ("2^" + std::to_string(c.r0_dim)).c_str() : "none");
        rep += buf;
        if (opt.count) {
            rep += ", solutions " + u128_str(c.count);
            if (res.count_weighted) rep += " x class size " + u128_str(c.orbit);
        } else if (c.sat)
            rep += ", SOLUTION";
        rep += "\n";
    }
    res.class_report = rep;
    return res;
}
