# Results computed with this toolkit (as of 2026-11-27)

Each line says what was computed, how, and what it rests on. "Verified" circuits are in `found/` and pass both
`bin/cktcheck` and the Python reference `py/pnpfast.py check` (re-run for every file in `found/` and `seeds/` when
the toolkit was packaged). Exhaustive (UNSAT) claims are computer searches: no DRAT/LRAT certificate was produced,
and none of them is a Lean proof. Cite them as computational results with the caveats below.

Notation: `K(n)` = least number of gates of a monotone fan-in-2 circuit (basis `ao`) that is 0 on every 1-hot input
and 1 on every 2-hot input of n wires (`specs/kn<n>.spec`). `crown_n` = least `ao` size representing the n x n
crown graph `u != v`. `crown_n = n + K(n)` is Lean-checked (L_meta_18508).

## 1. Exact values of K(n)

| n | K(n) | status | method |
|---|---|---|---|
| 3 | 4 | exact | known; reproduced by `cktsat --min` |
| 4 | 7 | exact | known; reproduced by `cktsat --min` (also `--no-sym`, and brute force) |
| 5 | 10 | exact | known; reproduced by `cktsat --min` and `src/knsat` (kn5 s = 9 UNSAT in 4.1 s without elimination clauses) |
| 6 | **13** | exact (computational) | s = 12 UNSAT by two independent encoders, one of them **without** elimination clauses (below) |
| 7 | **16** | exact (computational), **rests on elimination clauses** | s = 15 UNSAT by two independent encoders, **both** using the elimination step (below) |
| 8..12 | <= 19, 21, 24, 27, 29 | upper bounds only | witnesses `found/kn<n>_<size>_ao.ckt` from `cktsls`; smaller sizes were searched heuristically and not found, which proves nothing |

So far `K(n) = 3n - 5` for n = 3..7.

### K(6) = 13, so crown_6 = 19

* `src/knsat/kn_elim.py 6 12 --elim 2`: UNSAT, 502 s on one core (CaDiCaL 1.9.5). With symmetry filtering on the cubes
  and Kissat 4.0.4: 74 cubes, 11.4 s wall / 67 CPU-s on 6 cores. Uses the elimination clauses (see below), which are
  valid at s = 12 because `K(5) >= 10` is Lean-checked.
* `cktsat` (separate encoder, separate symmetry handling) **without any elimination clauses**: 777 canonical 4-gate
  root cubes, 1651 cubes in total, all UNSAT, 2751 CPU-s. `cktsat --audit --recheck 12` re-derived each shard's cube
  tree and re-solved random leaves with a second solver: audit OK.
* With the Lean-checked `K(6) >= 12` and the 13-gate witness `found/kn6_13_ao.ckt`: K(6) = 13.

### K(7) = 16, so crown_7 = 23

* `src/knsat/kn_cubes.py 7 15 --elim 2`: 475 cubes, all UNSAT, Kissat 4.0.4, 38 min wall on 8 cores (4.9 CPU-hours).
  The cube domain: 1,676,505,600 five-gate prefixes; 1,675,687,359 refuted by unit propagation, 817,766 dropped as
  non-canonical, 475 solved.
* `cktsat -s 15 --elim auto --elim-sem 1 --sens 1 --dep 1 --depth 5` in four shards: 11,266 root cubes, 11,406 cubes,
  all UNSAT, 8460 CPU-s (2.35 CPU-hours). `--audit --recheck 10` on all four shards: audit OK.
* Together with the Lean-checked `crown_7 <= 23` (L_meta_19546) this gives K(7) = 16 and crown_7 = 23; the statement
  "crown_7 <= 22" (unit L-meta-18259) would then be false.

What the K(7) claim rests on — state all of this when citing it:

1. Lean-checked inputs: `K(7) >= 15`, `K(5) >= 10`, `crown_n = n + K(n)`.
2. `K(6) >= 13` — the computational result above (not Lean-checked). It is needed because the elimination clauses at
   s = 15 are valid only if `15 <= K(6) + 2`.
3. The normal-form, symmetry (lex-min representative) and **elimination** arguments in the header of
   `src/knsat/kn_elim.py` (and docs/cktsat.md, "Elimination"), tested in `src/knsat/test_elim.py`, `test_sym.py` and
   `src/cktsat/selftest.py` on all optimal circuits for n = 4, 5 and on random instances.
4. The SAT solvers being right (no proof certificates were produced).

**Independent confirmation of K(7) = 16 without elimination clauses is still pending.** Both runs use the same
elimination step (with independent implementations). A plain run was estimated at 100+ CPU-hours and was not
started. A cross-check of the knsat cube set with CaDiCaL and without the extra F7/F8 clauses was queued; its
outcome is not recorded here.

## 2. Verified circuits (upper bounds) in `found/`

| target | size | basis | file | note |
|---|---|---|---|---|
| crown8..12 | 27, 30, 34, 38, 41 | ao | `found/crown<n>_<size>_ao.ckt` | the K(n) circuit with `z_i = x_i OR y_i` in front. The checked general bound `3n + 4 ceil(sqrt n) - 9` (L_meta_19062) gives 27, 30, 37, 40, 43, so crown10..12 beat it by 3, 2, 2 |
| cand128 (128x128 graph) | 1461 | aon | `found/cand128_1461_aon.ckt` | graphsynth then cktopt; 1500 was the accepted value on main. Three independent tools (graphsynth, cktopt, gpuopt) all stop at 1461-1466 |
| cand32 (32x32 graph) | 181 | aon | `found/cand32_181_aon.ckt` | 180 was the accepted value on main (`seeds/`) |
| match3 | 14 | ao and aon | `found/match3_14_*.ckt` | units ask for 13; not found by `cktsls` |
| mm3 | 45 | aon | `found/mm3_45_aon.ckt` | the naive monotone circuit; unit asks for 44; not found |
| cyc5, cyc6, cyc7 | 7, 8, 10 | aon | `found/cyc*_aon.ckt` | cyc5 = 7 and cyc6 = 8 are exact by `cktsat` (smaller sizes UNSAT) |

Candidate graphs: the structure found (docs/graphsynth.md) is a union of n planted rectangles of d x d (d = 4 for
cand32, 8 for cand128). All circuits found pair up planted rectangles (one AND per pair); the search in this shape
plateaued (10x more time bought 1 gate). Reaching <= 1350 / <= 150 seems to need a different circuit shape. Nothing
here is a lower bound for these graphs.

## 3. Exact tables for small graphs

* `tables/and_{3,4,5}.json` (`andtab`, cross-checked by `andsat`): exact AND-complexity (OR gates free) of every
  bipartite graph up to 5x5. Maximum 2 / 3 / 3; no 5x5 graph needs four AND gates.
* `tables/star_{3,4}.json` (`startab`): exact monotone and with-NOT sizes for every 3x3 and 4x4 graph. `star_5.json`:
  every 5x5 class, exact where the complete passes reached (all but 809 mono and 178 NOT classes), otherwise a proved
  lower bound and the best circuit; the non-exact entries are listed in `tables/star_5_not_exact.txt`.
  `star_4_enc.json`: 4x4 with free encoder wires, complete. See docs/startab.md and docs/andtab.md.
* `tables/kn_optimal_{3,4,5}.json`: optimal kn circuits (K(5) = 10 has exactly 500 non-isomorphic optimal circuits
  in the normal model).
* `found/ptrank_n*.json` (`ptrank`): partial-transpose rank of the identity over GF(2): P(2..4) = 2, 4, 7 exact,
  P(5) in {9, 10, 11}, P(6) <= 16. See docs/ptrank.md.

## 4. Measured speed

All on one Apple M5 Max shared with other heavy jobs (load average often 20-90), so absolute numbers are pessimistic.

| what | measured | baseline |
|---|---|---|
| `cktcheck` / `pnp::eval` | 0.9-1.6e11 gate·points/s per core (`cktcheck --bench`); the 2023-gate 128x128 circuit checks in about 0.2 ms of compute | Python reference (`py/pnpfast.py check`, big-int columns): the same file in about 0.05 s wall including start-up |
| kn5 s = 9 UNSAT | `cktsat` 7.6 s at -j 1; 0.48 CPU-s with implied clauses; `src/knsat` 0.6 s with elimination | 99 s single-thread Python (earlier encoder) |
| kn6 s = 12 UNSAT | 67 CPU-s (knsat, elimination), 109 CPU-s (cktsat, elimination), 2751 CPU-s (cktsat, none) | 502 s one CaDiCaL instance |
| GPU pair-scoring kernel (`gpukit`, Metal) | 82x-137x one CPU core at 16,384 bits per wire (1.3-2.1e13 bit-ops/s); 10-12x at 1024 bits | same loop in C++ on one core, 1.5-1.6e11 bit-ops/s |
| `gpuopt` vs the same loops on one core | singles 57x, pairs 124x, whole round 27x (the rest of a round is CPU work) | docs/gpuopt.md |
| `cktsls` | 5.5e8 candidate-gate evaluations/s per thread on kn7 (one 64-bit word of points) | — |
| `startab` 5x5 | mono pass 11 in 542 s on one thread (1.6e9 prefixes, 3.3e10 gate-ops) | — |

Details and the conditions of each measurement are in the per-tool docs.
