# ptrank — partial-transpose rank of the identity over GF(2), d = 2

Built as ground truth for the analytic (lower-bound) track. Results as of 2026-11-27.

    P(n) = min { rank(A) + rank(B) : A + B^T1 = I_{n^2} }           (B^T1)[(i1,i2),(j1,j2)] = B[(j1,i2),(i1,j2)]
         = min over terms (V_r, U_r) of  rank(B) + rank(id + Phi),   Phi(X) = sum_r V_r X^T U_r,  B = sum_r vec(U_r) vec(V_r)^T

Conventions are exactly those of `src/ptrank/ptr.py` (the pure-Python reference) (matrices = lists of row bitmasks,
bit j of row i = entry [i][j]). "(R, rho)" always means (rank(B), rank(A)) = (rank(B), rank(I + B^T1)).

## Results

| n | P(n) | best total found | (R, rho) | status | witness | method and coverage |
|---|------|------------------|----------|--------|---------|---------------------|
| 2 | 2 | 2 | (1,1) | EXACT | `found/ptrank_n2_2.json` | exhaustive (slice solver) |
| 3 | 4 | 4 | (1,3), (3,1) only | EXACT | `found/ptrank_n3_4.json` | exhaustive: total <= 3 impossible; at total 4 the split (2,2) is impossible |
| 4 | **7** | 7 | (1,6), (6,1) only | **EXACT (new)** | `found/ptrank_n4_7.json` | exhaustive, two independent methods: no decomposition with total <= 6. At total 7 the splits (2,5), (3,4) (and (5,2), (4,3)) are impossible, so every optimal decomposition has rank(B) = 1 or rank(A) = 1 |
| 5 | in {9, 10, 11} | 11 | (1,10) | lower bound 9 EXACT, upper bound 11 | `found/ptrank_n5_11.json` (transpose) | exhaustive: no total <= 8. R = 1 (or rho = 1) forces the other rank >= 10. Totals 9 and 10 are being searched (SAT, in the queue) |
| 6 | in [6, 16] | 16 | (1,15) | upper bound only | `found/ptrank_n6_16.json` (transpose) | not yet searched |
| 7 | in [7, 22] | 22 | (1,21) | upper bound only | `found/ptrank_n7_22.json` (transpose) | not yet searched |
| 8 | in [8, 28] | 28 | (4,24) | upper bound only | `found/ptrank_n8_28.json` (block construction) | not yet searched |

Consequence so far: c* = inf P(n)/n^2 <= 7/16 is NOT improved by n = 4 (P(4) = 7 exactly). No decomposition below
1 + C(n,2) has been found for any n.

### Exhaustive claims, stated precisely

"NONE for (n, R, rho)" means: there are no n^2 x n^2 matrices A, B over GF(2) with A + B^T1 = I, rank(A) <= rho and
rank(B) <= R. Because I^T1 = I, (A, B) -> (B, A) maps decompositions to decompositions, so NONE for (R, rho) is
equivalent to NONE for (rho, R); "total <= t impossible" was obtained from the splits R <= rho, R + rho = t.

| claim | splits covered | native slice solver (`ptrank exact`) | SAT (`satcheck.py --classes`, CaDiCaL 1.9.5) | brute force (`ptrank brute`) |
|---|---|---|---|---|
| n=3: total <= 3 impossible | (1,2) [(2,1) also run] | NONE, < 0.1 s | UNSAT | R=1: min rho = 3 over all 2^18 (V,U) |
| n=3: (2,2) impossible | (2,2) | NONE | UNSAT | R=2: min rho = 3 over all 2^36 pairs of terms, and all 515088 minimisers have rank(B) = 1 |
| n=4: total <= 6 impossible, so P(4) = 7 | (1,5), (2,4), (3,3) [(4,2), (5,1) also run] | NONE: 0.06 s, 2.2 s, 2.3 s on 3 threads; nodes 1.7e6, 1.1e8, 9.6e7 | UNSAT: 0.1 s each (13 / 22 / 26 classes) | R=1: min rho = 6 over all 2^32 (V,U) (rank-normal-form of V, weighted) |
| n=4: (2,5) and (3,4) impossible | (2,5), (3,4) | not finished (needs > 50 s on one thread; cores are busy) | UNSAT: 1.2 s (22 classes), 1.9 s (30 classes) | — |
| n=5: total <= 6 impossible | (1,5), (2,4), (3,3) | NONE, 0.8 s on 1 thread | UNSAT | — |
| n=5: total <= 7 impossible | (1,6), (2,5), (3,4) | (1,6) NONE 4.4 s; others not finished | UNSAT: 0.2 s, 0.5 s, 0.6 s | — |
| n=5: total <= 8 impossible, so P(5) >= 9 | (1,7), (2,6), (3,5), (4,4) | not run | UNSAT: 0.4 s, 10.2 s, 18.5 s, 12.0 s (with `--rowsym`: 3.7 s, 6.8 s, 5.0 s) | — |
| n=5: R = 1 forces rho >= 10 | (1, k), k <= 9 | — | (1,8) UNSAT 7.2 s | R=1: min rho = 10 over all 2^50 (V,U) (V in rank normal form, weighted; 2.0e8 evaluations) |

Rows marked "SAT only" rest on one method; everything about n = 4 with total <= 6 rests on two independent programs
(different language, different algorithm, sharing only the symmetry argument for l_0 below) plus brute force for R = 1.

### Structural facts found on the way (for generalising)

* R = 1, i.e. Phi(X) = V X^T U. Histogram of rho = rank(I + Phi) over ALL pairs (V, U) (`ptrank brute N 1 --sym`):
  - n = 3: {3: 168, 6: 17640, 7: 16464, 8: 158368, 9: 69504}
  - n = 4: {6: 20160, 10: 9374400, 12: 54472320, 13: 363148800, 14: 890749440, 15: 2054553600, 16: 922648576}
  - n = 5: {10: 9999360, 15: 19528750080, 18: 523866470400, 19: 3413914828800, 20: 1336634449920, 21: ..., 25: ...}
  The minimum is C(n,2) and it is attained by exactly |GL_n(2)| pairs (168, 20160, 9999360): one orbit, the transpose
  X -> S X^T S^-1... (V, U) = (S, S^-T) up to the symmetry below. The second smallest value is C(n+1,2) = C(n,2) + n:
  there is a gap of n. So "one term" gives exactly 1 + C(n,2) and nothing near it.
* n = 3, R = 2: min rho over rank(B) = 2 exactly is 4 (total 6); n = 3 optimal decompositions are (1,3) and (3,1) only.
* n = 4: optimal decompositions are (1,6) and (6,1) only. Mixed splits are strictly worse at n = 3 and n = 4.

## CLI

    bin/ptrank exact N --R r --rho-max k [-j T] [--count] [--nosym]     exhaustive: is there (A,B) with rank(B)<=r, rank(A)<=k ?
    bin/ptrank exact N --total t [-j T] [--both]                        all splits R + rho = t with R <= rho (--both: all)
    bin/ptrank search N --R r [-j T] [--time S] [--seed X] [--target t] [--out F.json]   stochastic, fixed number of terms
    bin/ptrank search N [--mode pure] ...                               stochastic, pure-tensor moves on (A, B), R free
    bin/ptrank verify FILE.json [-v]                                    recompute (R, rho, total) of a witness file
    bin/ptrank brute N R [-j T] [--sym]                                 histogram of rho over ALL tuples of R terms
    bin/ptrank gen | symcheck | bench                                   test helpers (below)
    bin/satpy src/ptrank/satcheck.py N R RHO --classes [--rowsym]       independent SAT decision of the same question
    python3 src/ptrank/pycheck.py verify|def FILE.json ...              witness check with ptr.cost / straight from the definition

`-j` defaults to `$PNP_THREADS` or 1. Results on stdout, progress on stderr. `exact` exit code 0 = found, 1 = none.
Witness JSON: `{"n":, "R":, "rho":, "total":, "terms": [[[V rows],[U rows]], ...]}` (row bitmasks as in ptr.py).

## Checks against the reference

* `ptrank gen N R COUNT SEED | python3 src/ptrank/pycheck.py cost`: native (R, rho, total) == `ptr.cost` on
  4200 random instances (n = 2..8, R = 1, 2, 3, 5; uniform, rank-one, sparse, invertible and dependent terms): 0 mismatches.
* Symmetries (all preserve (R, rho); `ptrank symcheck`, 45000 native instances, and 1800 instances re-checked with
  `ptr.cost` via `pycheck.py sym`): 0 violations.
  - (V_r, U_r) -> (P V_r Q^-T, P^-T U_r Q) for invertible P, Q   [conjugation of Phi by X -> P X Q^T]
  - invertible recombination of the terms as tensors: V'_r = sum_q H[r][q] V_q, U'_r = sum_q (H^-T)[r][q] U_q
  - (V_r, U_r) -> (U_r^T, V_r^T)   [conjugation by transposition]   and   (V_r, U_r) -> (U_r, V_r)   [adjoint of Phi]
  - A <-> B (I^T1 = I): not a map on terms; used as "NONE for (R, rho) <=> NONE for (rho, R)".

## How `exact` works (the slice solver)

With (a,b,c,d) = (i1,i2,j1,j2), A = sum_{k<rho} vec(A_k) vec(B_k)^T and B^T1 = [X -> sum_r V_r X^T U_r], the identity
A + B^T1 = I is

    sum_k A_k[a,b] B_k[c,d] + sum_r V_r[a,d] U_r[c,b] = [a=c][b=d]        for all a, b, c, d.

Row a of the "left" matrices is one vector l_a = (A_k[a,.])_k ++ (V_r[a,.])_r in GF(2)^m, m = n(rho+R); row c of the
"right" matrices is r_c = (B_k[c,.])_k ++ (U_r[c,.])_r. The identity says beta(l_a, r_c) = [a=c] I_n for one fixed
bilinear map beta: GF(2)^m x GF(2)^m -> M_n. Depth-first search in the order l_0, r_0, l_1, r_1, ...: given the r's the
admissible l_a form a linear space, given the l's the admissible r_a form an affine space; both are enumerated
completely (Gray code), with incremental echelon forms. Prunings are necessary conditions only (inconsistent system;
kernel too small to hold the remaining, necessarily independent, rows).

Symmetry is used for l_0 only: under the gauge group GL_n x GL_rho x GL_R (Q on the column index, recombination of
the A-terms, recombination of the B-terms) l_0 = (alpha, nu) (alpha = n x rho, nu = n x R) has the invariants
(s, t, p) = (rank alpha, rank nu, rank nu^T alpha) and these classify the orbits; one representative per class.
Check of exactly this step: `ptrank exact --count` counts ALL solutions (l, r); `src/ptrank/validate_exact.py`
compares, for 18 cases with n = 2, 3 (counts up to 4.6e9),
   (number from one representative per class x class size) = (number with no symmetry at all, `--nosym`)
   = (number predicted from `ptrank brute`, which just evaluates rank(I + Phi) for every tuple of terms),
and count(R, rho) = count(rho, R). All equal.

The SAT cross-check (`src/ptrank/satcheck.py`) encodes the displayed identity directly (AND gates + XOR chains),
fixes l_0 to the same class representatives, and with `--rowsym` adds reduced-row-echelon constraints on
l_1..l_{n-1} (symmetry of the row group; `src/ptrank/test_rowsym.py` checks on 12 cases that the SAT/UNSAT answer
of every class is unchanged and equals the native solver's "count > 0"). Every SAT answer is decoded and re-verified
with `ptr.cost`. CDCL is far faster than the enumeration here (n=4 (3,3): 0.1 s vs 5.5 core-seconds).

## Measured speed (Apple M5 Max, one core)

| what | n=4 | n=5 | n=8 |
|---|---|---|---|
| full `cost()` from scratch (Phi build + rank(B) + rank(I+Phi)) | 5.1e6 /s (R=1) | 2.2e6 /s (R=3) | 3.8e5 /s (R=8) |
| search inner loop: incremental bit flip + rank(I+Phi) | 7.3e6 /s | 4.0e6 /s | 1.25e6 /s |
| `brute` (Gray code over all terms) | 8.3e6 /s | 4.5e6 /s | — |
| slice solver | ~1.7e7 nodes/s (n=4, m=24) | | |

(The Python reference does a few thousand cost evaluations per second.)

## Limitations

* `exact` needs n (R + rho) <= 64 and its running time grows like 2^(2(m - n^2)) per class; beyond n = 4 it is only
  practical for small totals. Use the SAT route for n = 5.
* `search` is heuristic: its output is an upper bound only.
