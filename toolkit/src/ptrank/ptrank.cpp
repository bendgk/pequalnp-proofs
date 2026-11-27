// ptrank — partial-transpose rank of the identity over GF(2), d = 2 (Rossman–Zhu arXiv:2512.01227).
//
//   P(n) = min { rank(A) + rank(B) : A + B^{T1} = I_{n^2} }
//        = min over terms (V_r, U_r) of  rank(B) + rank(id + Phi),  Phi(X) = sum_r V_r X^T U_r.
//
//   ptrank exact N --R r --rho-max k [-j T] [--count] [--nosym] [--orbits]     exhaustive (see exact.hpp)
//   ptrank exact N --total t [-j T] [--both]                                   all splits R + rho = t, R <= rho
//   ptrank search N --R r [-j T] [--time S] [--seed X] [--target t] [--out FILE] ...   stochastic (see search.hpp)
//   ptrank verify FILE.json                                                    recompute (R, rho, total)
//   ptrank gen N R COUNT SEED     random instances with native cost, one JSON per line (cross-check vs ptr.py)
//   ptrank symcheck N R COUNT SEED   numerical check of the symmetries used
//   ptrank bench N R [SECONDS]    cost evaluations per second (one core)
//
// See docs/ptrank.md.  Conventions = src/ptrank/ptr.py (the Python reference).
#include "core.hpp"
#include "exact.hpp"
#include "search.hpp"
#include <chrono>

static double now_s() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

static int env_threads() {
    const char* e = getenv("PNP_THREADS");
    int t = e ? atoi(e) : 1;
    return t < 1 ? 1 : t;
}

static void random_terms(int n, int R, Rng& g, int mode, std::vector<Term>& t) {
    t.assign(R, Term());
    unsigned mask = (1u << n) - 1;
    for (int r = 0; r < R; r++) {
        memset(&t[r], 0, sizeof(Term));
        int md = mode < 0 ? (int)g.below(5) : mode;
        if (md == 0) {  // uniform
            for (int i = 0; i < n; i++) {
                t[r].V[i] = (uint8_t)(g.next() & mask);
                t[r].U[i] = (uint8_t)(g.next() & mask);
            }
        } else if (md == 1) {  // rank-one V and U
            unsigned a = g.next() & mask, b = g.next() & mask, c = g.next() & mask, d = g.next() & mask;
            for (int i = 0; i < n; i++) {
                t[r].V[i] = (uint8_t)(((a >> i) & 1) ? d : 0);
                t[r].U[i] = (uint8_t)(((c >> i) & 1) ? b : 0);
            }
        } else if (md == 2) {  // sparse
            for (int i = 0; i < n; i++) {
                t[r].V[i] = (uint8_t)(g.next() & g.next() & g.next() & mask);
                t[r].U[i] = (uint8_t)(g.next() & g.next() & mask);
            }
        } else if (md == 3) {  // invertible pair
            mat_random_invertible(n, g, t[r].V);
            mat_random_invertible(n, g, t[r].U);
        } else {  // copy / sum of earlier terms (dependent as tensors when V or U is shared)
            if (r >= 1) {
                int q = (int)g.below(r);
                t[r] = t[q];
                if (g.below(2))
                    for (int i = 0; i < n; i++) t[r].V[i] ^= (uint8_t)(g.next() & mask);
                else if (r >= 2) {
                    int q2 = (int)g.below(r);
                    for (int i = 0; i < n; i++) t[r].V[i] ^= t[q2].V[i];
                }
            } else
                mat_ident(n, t[r].V), mat_ident(n, t[r].U);
        }
    }
}

static int cmd_gen(int argc, char** argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ptrank gen N R COUNT SEED\n");
        return 2;
    }
    int n = atoi(argv[2]), R = atoi(argv[3]);
    long cnt = atol(argv[4]);
    Rng g(strtoull(argv[5], 0, 10));
    std::vector<Term> t;
    for (long i = 0; i < cnt; i++) {
        random_terms(n, R, g, -1, t);
        printf("%s\n", witness_json(n, t).c_str());
    }
    return 0;
}

static int cmd_verify(int argc, char** argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: ptrank verify FILE.json\n");
        return 2;
    }
    std::string s, err;
    if (!read_file(argv[2], s)) {
        fprintf(stderr, "verify: cannot read %s\n", argv[2]);
        return 2;
    }
    Witness w;
    if (!parse_witness(s, w, err)) {
        fprintf(stderr, "verify: %s\n", err.c_str());
        return 2;
    }
    Cost c = cost_of(w.n, w.terms.data(), (int)w.terms.size());
    bool ok = true;
    if (w.R >= 0 && w.R != c.R) ok = false;
    if (w.rho >= 0 && w.rho != c.rho) ok = false;
    if (w.total >= 0 && w.total != c.total) ok = false;
    printf("n=%d terms=%zu  recomputed: R=%d rho=%d total=%d   file says: R=%d rho=%d total=%d   %s\n", w.n,
           w.terms.size(), c.R, c.rho, c.total, w.R, w.rho, w.total, ok ? "OK" : "MISMATCH");
    printf("trivial bound 1+C(n,2) = %d;  7/16 n^2 = %.2f\n", 1 + w.n * (w.n - 1) / 2, 7.0 * w.n * w.n / 16);
    if (argc > 3 && !strcmp(argv[3], "-v")) print_term_matrices(stdout, w.n, w.terms);
    return ok ? 0 : 1;
}

static int cmd_bench(int argc, char** argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: ptrank bench N R [SECONDS]\n");
        return 2;
    }
    int n = atoi(argv[2]), R = atoi(argv[3]);
    double secs = argc > 4 ? atof(argv[4]) : 2.0;
    Rng g(12345);
    std::vector<Term> t;
    random_terms(n, R, g, 0, t);
    // (1) full cost from scratch (phi build + two ranks), fresh random bits every call
    double t0 = now_s();
    u64 evals = 0, acc = 0;
    while (now_s() - t0 < secs) {
        for (int it = 0; it < 4096; it++) {
            int r = (int)g.below(R), i = (int)g.below(n);
            t[r].V[i] ^= (uint8_t)(1u << g.below(n));
            Cost c = cost_of(n, t.data(), R);
            acc += c.total;
            evals++;
        }
    }
    double dt = now_s() - t0;
    printf("bench n=%d R=%d: full cost() from scratch (Phi build + rank(B) + rank(I+Phi)): %.3g evals/s/core  (checksum %llu)\n",
           n, R, evals / dt, (unsigned long long)acc);
    // (2) incremental: single bit flip + rank(I + Phi), as used by the search
    double r2 = search_bench_incremental(n, R, secs);
    printf("bench n=%d R=%d: incremental flip + rank(I+Phi) (search inner loop): %.3g evals/s/core\n", n, R, r2);
    return 0;
}

// numerical check of the symmetries: all of these must preserve (R, rho).
static int cmd_symcheck(int argc, char** argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ptrank symcheck N R COUNT SEED [--print]\n");
        return 2;
    }
    int n = atoi(argv[2]), R = atoi(argv[3]);
    long cnt = atol(argv[4]);
    Rng g(strtoull(argv[5], 0, 10));
    bool print = argc > 6 && !strcmp(argv[6], "--print");
    std::vector<Term> t, u;
    long bad = 0;
    for (long it = 0; it < cnt; it++) {
        random_terms(n, R, g, -1, t);
        Cost c0 = cost_of(n, t.data(), R);
        // (a) (V, U) -> (P V Q^-T, P^-T U Q)
        uint8_t P[NMAX], Q[NMAX], Pi[NMAX], Qi[NMAX], PiT[NMAX], QiT[NMAX];
        mat_random_invertible(n, g, P);
        mat_random_invertible(n, g, Q);
        mat_inv(n, P, Pi);
        mat_inv(n, Q, Qi);
        mat_transpose(n, Pi, PiT);
        mat_transpose(n, Qi, QiT);
        u = t;
        for (int r = 0; r < R; r++) {
            mat_mul(n, P, t[r].V, u[r].V);
            mat_mul(n, u[r].V, QiT, u[r].V);
            mat_mul(n, PiT, t[r].U, u[r].U);
            mat_mul(n, u[r].U, Q, u[r].U);
        }
        Cost c1 = cost_of(n, u.data(), R);
        // (b) invertible recombination of the terms as tensors: V'_r = sum_q H[r][q] V_q, U'_r = sum_q H^-T[r][q] U_q
        Cost c2 = c0;
        if (R <= NMAX) {
            uint8_t H[NMAX], Hi[NMAX], HiT[NMAX];
            mat_random_invertible(R, g, H);
            mat_inv(R, H, Hi);
            mat_transpose(R, Hi, HiT);
            for (int r = 0; r < R; r++) {
                memset(&u[r], 0, sizeof(Term));
                for (int q = 0; q < R; q++) {
                    if ((H[r] >> q) & 1)
                        for (int i = 0; i < n; i++) u[r].V[i] ^= t[q].V[i];
                    if ((HiT[r] >> q) & 1)
                        for (int i = 0; i < n; i++) u[r].U[i] ^= t[q].U[i];
                }
            }
            c2 = cost_of(n, u.data(), R);
        }
        // (c) (V, U) -> (U^T, V^T)   (conjugation by X -> X^T)
        for (int r = 0; r < R; r++) {
            mat_transpose(n, t[r].U, u[r].V);
            mat_transpose(n, t[r].V, u[r].U);
        }
        Cost c3 = cost_of(n, u.data(), R);
        // (d) (V, U) -> (U, V)       (adjoint of Phi)
        for (int r = 0; r < R; r++) {
            memcpy(u[r].V, t[r].U, NMAX);
            memcpy(u[r].U, t[r].V, NMAX);
        }
        Cost c4 = cost_of(n, u.data(), R);
        bool ok = c1.R == c0.R && c1.rho == c0.rho && c2.R == c0.R && c2.rho == c0.rho && c3.R == c0.R &&
                  c3.rho == c0.rho && c4.R == c0.R && c4.rho == c0.rho;
        if (!ok) bad++;
        if (print) {
            // one line per instance: original and the four images, for the Python cross-check
            printf("{\"orig\": %s, \"pq\": ", witness_json(n, t).c_str());
            for (int r = 0; r < R; r++) {
                mat_mul(n, P, t[r].V, u[r].V);
                mat_mul(n, u[r].V, QiT, u[r].V);
                mat_mul(n, PiT, t[r].U, u[r].U);
                mat_mul(n, u[r].U, Q, u[r].U);
            }
            printf("%s}\n", witness_json(n, u).c_str());
        }
    }
    fprintf(stderr, "symcheck n=%d R=%d: %ld instances, %ld violations of (R, rho) invariance "
                    "[(P,Q) action, term recombination, (U^T,V^T), (U,V)]\n", n, R, cnt, bad);
    return bad ? 1 : 0;
}

// ------------------------------------------------------------------------------------------------------------
static bool run_exact_one(ExactOpts o, bool json_out, std::vector<Term>* wit = nullptr) {
    Exact E(o);
    ExactResult r = E.run();
    fprintf(stderr, "%s", r.class_report.c_str());
    fprintf(stderr, "  nodes:");
    for (int a = 0; a < o.n; a++)
        fprintf(stderr, "  l_%d %llu->%llu, r_%d %llu;", a, (unsigned long long)r.cand_l[a],
                (unsigned long long)r.pass_l[a], a, (unsigned long long)r.cand_r[a]);
    fprintf(stderr, "\n");
    if (o.count) {
        printf("COUNT n=%d R<=%d rho<=%d: %s solutions (l_0..l_%d, r_0..r_%d) of beta(l_a, r_c) = [a=c] I   [%s, %.2fs, %d threads]\n",
               o.n, o.R, o.rho, u128_str(r.count).c_str(), o.n - 1, o.n - 1,
               o.nosym ? "no symmetry" : (r.count_weighted ? "one l_0 per class x class size" : "UNWEIGHTED class sum"),
               r.seconds, o.threads);
        return r.count != 0;
    }
    if (r.found) {
        Cost c = cost_of(o.n, r.witness.data(), (int)r.witness.size());
        bool ok = c.R <= o.R && c.rho <= o.rho;
        if (!ok) {
            fprintf(stderr, "INTERNAL ERROR: witness does not verify (R=%d rho=%d)\n", c.R, c.rho);
            exit(3);
        }
        printf("RESULT n=%d R<=%d rho<=%d: FOUND  (verified natively: R=%d rho=%d total=%d)  [%.2fs]\n", o.n, o.R, o.rho,
               c.R, c.rho, c.total, r.seconds);
        if (json_out) printf("%s\n", witness_json(o.n, r.witness).c_str());
        if (wit) *wit = r.witness;
        return true;
    }
    printf("RESULT n=%d R<=%d rho<=%d: NONE  (exhaustive: %ld l_0 classes, %ld (l_0,r_0) tasks, %.2fs, %d threads)\n",
           o.n, o.R, o.rho, r.classes, r.tasks, r.seconds, o.threads);
    return false;
}

static int cmd_exact(int argc, char** argv) {
    ExactOpts o;
    o.threads = env_threads();
    int total = -1, rmax = -1;
    bool both = false;
    std::string out;
    if (argc < 3) {
        fprintf(stderr, "usage: ptrank exact N --R r --rho-max k [-j T] [--count] [--nosym]\n"
                        "       ptrank exact N --total t [-j T] [--both]\n");
        return 2;
    }
    o.n = atoi(argv[2]);
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
        else if (a == "--rho-max" || a == "--rho") rmax = atoi(need("--rho-max"));
        else if (a == "-j") o.threads = atoi(need("-j"));
        else if (a == "--count") o.count = true;
        else if (a == "--nosym") o.nosym = true;
        else if (a == "--orbits") o.orbits = true;
        else if (a == "--quiet") o.quiet = true;
        else if (a == "--total") total = atoi(need("--total"));
        else if (a == "--both") both = true;
        else if (a == "--out") out = need("--out");
        else if (a == "--progress") o.progress_every = atof(need("--progress"));
        else {
            fprintf(stderr, "unknown option %s\n", a.c_str());
            return 2;
        }
    }
    if (total >= 0) {
        // P(n) <= total  <=>  some split R + rho = total is feasible; by the A/B symmetry R <= rho suffices.
        bool any = false;
        std::vector<Term> wit;
        for (int R = 0; R <= total; R++) {
            int rho = total - R;
            if (R > rho && !both) break;
            if ((long)o.n * total > 64) {
                fprintf(stderr, "n*(R+rho) > 64 not supported\n");
                return 2;
            }
            ExactOpts q = o;
            q.R = R;
            q.rho = rho;
            if (R == 0 || rho == 0) {
                // rank 0 on one side forces the other side to be the identity (rank n^2)
                bool f = (total >= o.n * o.n);
                printf("RESULT n=%d R<=%d rho<=%d: %s  (trivial: one side is 0, the other is I of rank %d)\n", o.n, R, rho,
                       f ? "FOUND" : "NONE", o.n * o.n);
                any |= f;
                continue;
            }
            if (run_exact_one(q, true, &wit)) {
                any = true;
                if (!out.empty()) {
                    FILE* f = fopen(out.c_str(), "w");
                    if (f) {
                        fprintf(f, "%s\n", witness_json(o.n, wit).c_str());
                        fclose(f);
                    }
                }
            }
            fflush(stdout);
        }
        printf("SUMMARY n=%d: decomposition with rank(A)+rank(B) <= %d %s\n", o.n, total,
               any ? "EXISTS" : (both ? "does NOT exist (all splits searched exhaustively)"
                                      : "does NOT exist (splits R <= rho searched exhaustively; R > rho follows from the A/B swap)"));
        return any ? 0 : 1;
    }
    if (rmax < 0) {
        fprintf(stderr, "exact: give --R r --rho-max k, or --total t\n");
        return 2;
    }
    o.rho = rmax;
    std::vector<Term> wit;
    bool f = run_exact_one(o, true, &wit);
    if (f && !out.empty() && !o.count) {
        FILE* fo = fopen(out.c_str(), "w");
        if (fo) {
            fprintf(fo, "%s\n", witness_json(o.n, wit).c_str());
            fclose(fo);
        }
    }
    return f ? 0 : 1;
}

// ------------------------------------------------------------------------------------------------------------
// brute: histogram of rho = rank(I + Phi) over ALL tuples of R terms (2^(2 n^2 R) of them), by direct evaluation.
// Independent of the slice solver; used to validate it (docs/ptrank.md).  --sym: V_0 only over diag(I_k, 0),
// k = 0..n, each weighted by the number of n x n matrices of rank k (uses the (P,Q) symmetry on the first term).
static int cmd_brute(int argc, char** argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: ptrank brute N R [-j T] [--sym]\n");
        return 2;
    }
    int n = atoi(argv[2]), R = atoi(argv[3]), T = env_threads();
    bool sym = false;
    for (int i = 4; i < argc; i++) {
        if (!strcmp(argv[i], "-j") && i + 1 < argc) T = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--sym")) sym = true;
    }
    int N = n * n;
    int freebits = 2 * N * R - (sym ? N : 0);
    if (n < 2 || n > 5 || R < 1 || freebits > 40) {
        fprintf(stderr, "brute: too big (free bits %d > 40)\n", freebits);
        return 2;
    }
    // bit layout of the free bits: term R-1 first (lowest bits), V then U; with --sym term 0 has only U.
    // chunks: the top `pb` free bits are fixed per task, the rest runs through a Gray code.
    int pb = std::min(freebits - 1, 10);
    int gb = freebits - pb;
    std::vector<u128> wk(n + 1, 1);
    for (int k = 0; k <= n; k++) {
        u128 num = 1, den = 1;
        for (int i = 0; i < k; i++) {
            num *= ((u128)1 << n) - ((u128)1 << i);
            num *= ((u128)1 << n) - ((u128)1 << i);
            den *= ((u128)1 << k) - ((u128)1 << i);
        }
        wk[k] = num / den;
    }
    int kcases = sym ? n + 1 : 1;
    std::vector<std::vector<u128>> hist(T, std::vector<u128>(N + 1, 0));
    std::atomic<long> next{0};
    long ntasks = (long)kcases << pb;
    double t0 = now_s();
    std::atomic<u64> evals{0};
    auto work = [&](int ti) {
        TermState s;
        s.n = n;
        s.R = R;
        s.N = N;
        // map free bit index -> (term, side, row, col)
        struct Loc {
            uint8_t r, side, row, col;
        };
        std::vector<Loc> loc;
        for (int r = R - 1; r >= 0; r--)
            for (int side = 0; side < 2; side++) {
                if (sym && r == 0 && side == 0) continue;
                for (int b = 0; b < N; b++) loc.push_back(Loc{(uint8_t)r, (uint8_t)side, (uint8_t)(b / n), (uint8_t)(b % n)});
            }
        u64 ev = 0;
        for (;;) {
            long task = next.fetch_add(1);
            if (task >= ntasks) break;
            int k = (int)(task >> pb);
            u64 prefix = (u64)task & ((1ull << pb) - 1);
            for (int r = 0; r < R; r++) memset(&s.t[r], 0, sizeof(Term));
            if (sym)
                for (int i = 0; i < k; i++) s.t[0].V[i] = (uint8_t)(1u << i);
            for (int b = 0; b < pb; b++)
                if ((prefix >> b) & 1) {
                    const Loc& L = loc[gb + b];
                    if (L.side) s.t[L.r].U[L.row] ^= (uint8_t)(1u << L.col);
                    else s.t[L.r].V[L.row] ^= (uint8_t)(1u << L.col);
                }
            s.rebuild();
            u64 h[65];
            memset(h, 0, sizeof h);
            h[s.rho()]++;
            for (u64 i = 1; !(i >> gb); i++) {
                const Loc& L = loc[__builtin_ctzll(i)];
                if (L.side) s.xorU(L.r, L.row, 1u << L.col);
                else s.xorV(L.r, L.row, 1u << L.col);
                h[s.rho()]++;
            }
            ev += 1ull << gb;
            u128 w = sym ? wk[k] : (u128)1;
            for (int q = 0; q <= N; q++) hist[ti][q] += w * h[q];
        }
        evals.fetch_add(ev);
    };
    std::vector<std::thread> th;
    for (int i = 0; i < T; i++) th.emplace_back(work, i);
    for (auto& t : th) t.join();
    double dt = now_s() - t0;
    printf("{\"n\": %d, \"R\": %d, \"sym\": %s, \"hist\": {", n, R, sym ? "true" : "false");
    bool first = true;
    int minrho = -1;
    for (int q = 0; q <= N; q++) {
        u128 v = 0;
        for (int i = 0; i < T; i++) v += hist[i][q];
        if (v == 0) continue;
        if (minrho < 0) minrho = q;
        printf("%s\"%d\": %s", first ? "" : ", ", q, u128_str(v).c_str());
        first = false;
    }
    printf("}, \"min_rho\": %d}\n", minrho);
    fprintf(stderr, "brute n=%d R=%d%s: %.3g evaluations in %.1fs on %d threads (%.3g evals/s/core); min rho over all tuples = %d\n",
            n, R, sym ? " (first V in rank normal form, weighted)" : "", (double)evals.load(), dt, T, evals.load() / dt / T, minrho);
    return 0;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr,
                "ptrank — partial-transpose rank of the identity over GF(2)\n"
                "  ptrank exact N --R r --rho-max k [-j T] [--count] [--nosym]\n"
                "  ptrank exact N --total t [-j T] [--both]\n"
                "  ptrank search N --R r [-j T] [--time S] [--seed X] [--target t] [--out FILE]\n"
                "  ptrank verify FILE.json [-v]\n"
                "  ptrank gen N R COUNT SEED | symcheck N R COUNT SEED | bench N R [SECONDS] | brute N R [-j T] [--sym]\n");
        return 2;
    }
    std::string c = argv[1];
    if (c == "gen") return cmd_gen(argc, argv);
    if (c == "verify") return cmd_verify(argc, argv);
    if (c == "bench") return cmd_bench(argc, argv);
    if (c == "symcheck") return cmd_symcheck(argc, argv);
    if (c == "exact") return cmd_exact(argc, argv);
    if (c == "brute") return cmd_brute(argc, argv);
    if (c == "search") return cmd_search(argc, argv, env_threads());
    fprintf(stderr, "unknown command %s\n", c.c_str());
    return 2;
}
