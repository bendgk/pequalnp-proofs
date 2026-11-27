# cktsls — stochastic search for small circuits (upper-bound witnesses)

Status: working. HEURISTIC. It finds witnesses; a run that finds nothing proves nothing (see "Calibration").
Every circuit it prints was re-verified on ALL points with `pnp::verify` + `basis_ok`; the files in `found/` were
also checked with `bin/cktcheck`.

    bin/cktsls SPEC --basis ao|aon -s GATES [-j T] [--time S] [--seed X] [-o OUT.ckt] [--init IN.ckt]
               [--shape SPS[:k]] [--sym PERM [--fixed F]]

Searches for a circuit with AT MOST `GATES` gates that is right on every cared point of every output.
stdout: `FOUND size=... time=... steps=... cand_evals=...` + the circuit (`.ckt` text), exit 0;
or `NOTFOUND (no proof of anything) ... best_cost=...`, exit 1. Progress goes to stderr. Exit 3 = internal error.

| option | meaning |
|---|---|
| `--basis ao` / `aon` | AND/OR, or AND/OR/NOT (NOT counted). Gates are AND/OR of two distinct earlier wires, NOT of one: the output always also satisfies `ao2`. |
| `-s GATES` | size budget. Dead gates are pruned, so the printed circuit may be smaller (`size=` vs `requested=`). |
| `-j T` | threads (default `$PNP_THREADS` or 1). One island per thread. |
| `--islands I` | number of independent islands (default T). The result depends on `--seed` and I only, not on T. |
| `--time S` | wall limit, default 60 (checked between rounds). `--rounds n` = deterministic stop instead. |
| `--seed X` | default 1. Same seed + same islands => same circuit (checked: identical output for `-j 1` and `-j 2`). |
| `-o OUT.ckt` | also save the circuit. `--best F.ckt`: on failure save the best INCORRECT state (its comment says so; never put it in `found/`). |
| `--init IN.ckt` | start every replica from IN: random gates are deleted (readers re-wired to a fanin) or random gates added to reach GATES. A correct IN with at most GATES gates is returned at once. |
| `--shape SPS[:k]` | typed layers, see below. Usually the strongest mode for OR-of-AND-of-OR targets (kn, crown, mm). |
| `--sym PERM` | symmetric ansatz, see below. `--fixed F`: number of self-symmetric gates (default: all feasible values, one per island). |
| `--replicas R` | temperatures per island (default 8). `--tmin` (default 0.03), `--tmax` (default: calibrated), `--hotfrac`, `--noadapt`, `--sweep`. |
| `--sample S` | evaluate on S sampled points + counterexamples (default: all points if P <= 4096, else 1024). |
| `--takeover m` | 0/1/2, see below (default 2 if at most 2 outputs, else 1). |
| `--ladder` | print temperatures / mean cost / exchange rates at the end. `--selfcheck`: recompute everything after each move (debug). |

Helpers in `src/cktsls/tools/`:
* `sps_sat.py N S` (run with `bin/satpy`): EXACT answer by SAT inside the sum-product-sum family for `kn<N>` (see "Family").
* `symdescend.py SPEC BASIS S` : scan symmetry types with `--sym` and walk the size down.
* `kn2crown.py KN.ckt OUT.ckt` : K(n) circuit -> crown_n circuit (z_i = x_i OR y_i in front).

Build: `make -C src/cktsls` (builds to a temporary name and renames, so running jobs keep their binary).

## What it does

State: `GATES` gates forming an arbitrary DAG (a topological order is maintained incrementally), one column of
P bits per wire. Cost = sum over the K outputs of the minimum over ALL wires of the Hamming distance to the target on
the cared points; outputs are re-assigned to their best wire after every move.

Move = heat bath on one gate g ("pick the best replacement", done exactly and for all candidates at once):

1. simulate the fanout cone of g twice, with g = all-0 and g = all-1;
2. for every output in the cone this gives a need-mask pair (T, C): where C(p) = 1 the output is right at p iff
   g(p) = T(p), elsewhere it does not depend on g(p);
3. the exact cost of replacing g by `op(a, b)` is then `base + popcount((op(a,b) ^ T) & C)`: 3 word operations and a
   popcount per candidate when P <= 64. All pairs (a, b) of wires outside the cone, both ops (and NOT a) are scored;
4. the new gate is drawn with probability proportional to exp(-cost / T) (rejection-free);
5. the cone is updated by a mux of the two simulations; no re-simulation.

`cand_evals` counts these exactly scored candidates ("evaluations"). Outputs that are not in the cone contribute
`min(current distance, distance of the candidate column)` ("takeover"), so an unused gate is steered towards
becoming a better output instead of drifting.

Search control: each island runs R replicas on a temperature ladder with replica exchange (parallel tempering).
The cold end (T = 0.03) is in effect greedy + plateau walk; the hot end is calibrated per spec (the temperature where
the mean cost is 40% of the way from a quenched state to a random one); interior temperatures adapt to equalise
exchange rates. Islands are independent (own RNG), rounds are synchronised only for stopping, so runs are reproducible.

Specialisations: P <= 64 one word per wire, also 2/4/8 words; larger P uses a word loop with early abandon.
Big specs (mm3: 2^18 points): cost on a 1024-point sample; when the sample cost is 0 the circuit is checked on all
points and up to 32 wrong points are added to the island's sample (FIFO of 512 counterexamples).

### Typed layers (`--shape`)

`--shape SPS:k` fixes the roles of the gates: first-layer ORs that read inputs or first-layer ORs (so each is the OR
of a set of inputs), then k ANDs of two inputs/first-layer wires, then ORs that combine the products
(`PSP` = the dual). Layer sizes are GATES-2k+K, k, k-K for K outputs, or explicit `SPS:a,b,c`. Without `:k` every
feasible k gets its own island (and there are at least that many islands). Same engine, smaller candidate lists.
It is a restriction of the search space; inside it the search is far stronger (kn9 at 21: plain search fails, the
symmetric ansatz needs 15K-290K steps with the right symmetry, `--shape SPS:4` needs 35K steps with no symmetry;
mm3 at 45: 20-40 s plain, 1.2 s with `--shape SPS:27`).

### Symmetric ansatz (`--sym`)

`--sym "(1 3)(2 6)(5 7)"` restricts the search to circuits invariant under that permutation of the input wires:
gates come in orbits (r gates each, r = order of the permutation) plus F "fixed" gates whose fanin pair is invariant.
One move re-draws a whole orbit; for orbits of up to 4 gates the need-mask trick is generalised (2^r cone
simulations, then one mux tree + popcount per candidate), larger orbits are scored by direct simulation.
cktsls warns when the spec is not invariant under the permutation. A hit is an ordinary verified circuit; a miss
says nothing about asymmetric circuits.

## Guarantees

* A `FOUND` circuit is correct (re-verified on all points, basis checked, size <= GATES).
* `NOTFOUND` is NOT a non-existence statement of any kind, with or without `--shape` / `--sym`.
* Model searched: AND/OR of two distinct earlier wires, NOT of one earlier wire. Constants, copies and missing-wire
  reads (legal in the Lean model) are not generated; they never help a minimum-size circuit for a non-constant
  target (same normal-form argument as in docs/cktsat.md), so no witness size is lost.
* Memory: a few MB (state is O(islands * replicas * wires * words)); mm3 needs about 30 MB for the spec itself.
* `sps_sat.py` is exact, but only for the family it describes (see below).

## Family: sum-product-sum circuits for K(n) (`--shape SPS`, `sps_sat.py`)

Every K(n) circuit cktsls found has this form: ORs of sets of inputs, k ANDs of two such sets (a biclique X x Y of
the complete graph on the inputs, X and Y disjoint), and k-1 ORs of the products; it is correct iff the bicliques
cover every pair. Size = (#set-ORs) + 2k - 1. `sps_sat.py` decides this family exactly (SAT, single thread):

| n | family SAT | time |
|---|---|---|
| 5 | 10 gates SAT (k=3), 9 UNSAT for every k | < 1 s |
| 6 | 13 SAT (k=3), 12 UNSAT for every k | < 1 s |
| 7 | 16 SAT (k=3), 15 UNSAT for every k | 11 s |
| 8 | 18: UNSAT for k = 1,2,3,6,7,8,9 (k = 3: 34-47 s, k = 6: 61 s with `--minimal`); k = 4 and 5 NOT finished | see runs/cktsls/batchF.log |
| 9 | 21 SAT (k=4, 78 s with `--minimal`) | 20 not finished |

These agree with the exhaustive results K(5)=10, K(6)=13, K(7)=16. A family UNSAT says nothing about circuits
outside the family.

## Measured (Apple M5 Max; numbers after 03:55 were taken with load average 20-60, i.e. 2-4x slower)

Throughput, plain mode, one thread ("evaluations" = exactly scored candidate gates):

| spec | steps/s | evaluations/s | note |
|---|---|---|---|
| kn7 s=15 (28 points, 1 word) | 2.0e6 | 5.5e8 | quiet machine |
| kn7 s=15, 5 threads, 600 s | 6.2e6 total | 1.7e9 total | 3.4e8 per thread |
| kn9 s=21 (45 points) | 1.0e6 | 5.7e8 | quiet machine |
| match3 s=13 (512 points, 8 words) | 1.1e6 | 3.3e8 | quiet; 3.1e5 / 9.5e7 under load |
| cyc7 s=9 (128 points) | 1.0e6 | 1.7e8 | under load |
| mm2 s=11 (256 points, 4 outputs) | 4.5e5 | 1.2e8 | under load |
| mm3 s=45 (1024-point sample, 9 outputs) | 1.0e4-1.6e4 | 3.7e7-5.7e7 | under load |
| kn9 `--sym` (orbit moves) | 1.0e5 | 4e7 | under load |
| kn8 s=18 `--shape SPS` | 1.7e6 | 3.3e8 | under load |

Time to solution, plain mode, one thread, default parameters, 20 seeds each (runs/cktsls/validation.txt):

| target | solved | median | max |
|---|---|---|---|
| cyc5 aon 7 | 20/20 | < 1 ms | 2 ms |
| cyc6 aon 8 | 20/20 | 59 ms | 216 ms |
| cyc7 aon 10 | 20/20 | 2 ms | 5 ms |
| mm2 ao 12 / aon 12 | 20/20 | 1 ms / 4 ms | 3 ms / 7 ms |
| kn3 ao 4, kn4 ao 7 | 20/20 | < 1 ms | 1 ms |
| kn5 ao 10 | 20/20 | 1 ms | 2 ms |
| kn6 ao 13 | 20/20 | 3 ms | 8 ms |
| kn7 ao 16 | 20/20 | 9 ms | 18 ms |
| kn7 ao 17 | 20/20 | 5 ms | 13 ms |
| maj5 ao 10 (specs/maj5.spec, added) | 20/20 | 3 ms | 52 ms |
| crown4 ao 11 (10 seeds) | 10/10 | 131 ms | 484 ms |
| crown5 ao 15 (10 seeds) | 10/10 | 510 ms | 1.0 s |
| crown6 ao 19 (6 seeds, 4 s limit) | 5/6 | 1.3 s | > 4 s |
| match3 ao 14 / aon 14 (single runs) | found | 0.1-3.5 s / 1.2-2.8 s | |
| mm3 aon 45 (1 thread, seeds 1, 2) | 2/2 | 20.6 s, 42.2 s | 1.2 s with `--shape SPS:27` |

Negative controls (sizes proven impossible) were never "found": kn3/3, kn4/6, kn5/9, kn6/12, crown4/10, and
kn7/15 (600 s x 5 threads, 3.7e9 steps, 1.03e12 evaluations, best cost 1 = one point wrong).

## Calibration (why NOTFOUND means little)

kn9 at 21 gates exists (3x3 grid circuit). Plain mode did NOT find it in 40 s x 3 threads (1.2e8 steps, 6.5e10
evaluations; it sits at cost 1). `--sym "(1 3)(2 6)(5 7)" --fixed 1` finds it in 16K-290K steps (0.1-3 s);
`--shape SPS:4` in 35K steps (0.05 s). So plain mode finds "generic" circuits and misses structured needles;
`--shape` / `--sym` find them only if the needle has that shape / symmetry.

## Results

Best sizes found (all files in `found/`, all `bin/cktcheck` OK):

| spec | basis | wanted | found | not found (heuristic, proves nothing) |
|---|---|---|---|---|
| kn7 | ao | 15 | 16 (ms) | 15: 600 s x 5 threads plain, best cost 1. (Since settled: K(7) = 16 by exhaustive SAT.) |
| kn8 | ao | 18 | 19 `kn8_19_ao.ckt` | 18: 10 symmetry types x 30 s; `--shape SPS` 240 s (4.0e8 steps, 7.9e10 evaluations), best cost 1 |
| kn9 | ao | 20 | 21 `kn9_21_ao.ckt` | 20: 11 symmetry types x 45 s, best cost 1 |
| kn10 | ao | 23 | 24 `kn10_24_ao.ckt` | 23: 8 symmetry types x 90 s; `--shape SPS` 50 s (6.4e7 steps), best cost 1 |
| kn11 | ao | 26 | 27 `kn11_27_ao.ckt` | 26: 8 symmetry types x 120 s; `--shape SPS` 40 s (3.7e7 steps), best cost 1 |
| kn12 | ao | 28 | 29 `kn12_29_ao.ckt` | 28: `--shape SPS` 45 s (3.2e7 steps), best cost 1 |
| crown8..12 | ao | | 27, 30, 34, 38, 41 `crown<n>_<size>_ao.ckt` | = n + the K(n) circuit above (kn2crown.py) |
| match3 | ao | 13 | 14 `match3_14_ao.ckt` (9 AND + 5 OR, the row expansion) | 13: 300 s x 1 thread (9.2e7 steps, 2.8e10 evaluations), best cost 22 of 512 |
| match3 | aon | 13, 12, 11 | 14 `match3_14_aon.ckt` (no NOT used) | 13: 300 s (1.3e8 steps, 4.1e10 evaluations) best cost 22; 12: 30 s best 25; 11: 30 s best 43 |
| cyc7 | aon | 10 | 10 `cyc7_10_aon.ckt`; reflection-symmetric one `cyc7_10_aon_sym.ckt` | |
| mm3 | aon | 44 | 45 `mm3_45_aon.ckt` (27 AND + 18 OR) | 44: 600 s x 1 thread (8.5e6 steps, 3.0e10 evaluations): best state wrong on 36864 of 2359296 (output, point) pairs = the 45-gate circuit minus one product |

K(n) circuits with 19 / 21 / 24 / 27 / 29 gates for n = 8..12 are found in 0.05-2 s by `--shape SPS` (one thread).

## Limitations

* Heuristic. Needle solutions are missed unless a matching `--shape` / `--sym` is given (see Calibration).
* Cost per move grows like (inputs + GATES)^2: fine up to about 100 wires, slow beyond (cand32 at 205 gates:
  1.1e3 moves/s; cand128 is out of reach).
* `--shape` knows only sum-product-sum and its dual; `--sym` only cyclic groups (one generator) and needs all points.
* `--time` is checked between rounds; the calibration phase before the first round can take about a second on
  mm3-sized inputs.
* Timings above were mostly taken on a loaded machine.
