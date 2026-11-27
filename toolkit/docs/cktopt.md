# cktopt — circuit shrinker that exploits don't-cares

Takes a spec, a correct circuit for it and a basis; returns a smaller correct circuit in the same basis.
Heuristic local search. It never proves minimality. Every circuit it writes has passed `pnp::verify` on the
original spec, and `bin/cktcheck` agrees on every file listed below.

Source: `src/cktopt/cktopt.cpp` (one file, C++20, no dependencies beyond `include/ckt.hpp`), `make -C src/cktopt`.

## CLI

    bin/cktopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X] [--target SIZE]
               [--save PREFIX]        also write every improvement as PREFIX_<size>_<basis>.ckt
               [--rounds R]           stop after R rounds instead of after --time (fully deterministic, see below)
               [--round-work W]       work units per thread per round (default 1.5e8)
               [--level 1..5]         1 cleanup only, 2 + 0-resubstitution with observability, 3 + OR/AND covers,
                                      4 + 2-level terms, 5 + size-neutral rewrites, Paar, sharing optimiser, restarts
               [--max-terms K] [--dfs N]        cover search limits (default 5 terms, 400 search nodes)
               [--share-work W] [--share-group G]   set-space sharing optimiser: work per run (default 4e7 at 1600+
                                                    gates, scaled by (gates/1600)^2 below; 0 = off), terminals
                                                    re-covered together (default 4)
               [--share-only W]       run only the sharing optimiser once with W work units, write the result, exit
               [--mem GB]             refuse / reduce threads above this estimate (default 2)
               [--debug]              full consistency check of the network after every accepted move (slow)
               [--bench]              print evaluator and gate-visit throughput for SPEC/IN and exit
               [-q]                   no progress on stderr
    experimental, off by default: [--share-repair P --share-polish N --share-temp T] [--rar F] [--side-mode 0|1|2]
                                  [--pair-every N] [--pair-cap N] [--no-index]

* Threads: `-j T`, default `$PNP_THREADS` or 1. `--time` default 10 s.
* stderr: size trajectory (`t=… round=… best=… threads: sizes`), then a per-move table and throughput.
  stdout: one line `RESULT size=… input=… and=… or=… not=… basis=… time=… file=…`.
* OUT is rewritten at every improvement, so a killed run still leaves its best circuit.
* `--save PREFIX` overwrites an existing `PREFIX_<size>_<basis>.ckt`. With `--save found/cand128` a file of the same
  size written by another tool is replaced by an equally large verified circuit.
* Stops early when `--target` is reached, or when nothing is left to remove.
* Exit 2 if the input circuit is wrong on the spec, violates the basis, or the memory estimate exceeds `--mem`.
* Input may use every Lean-legal degenerate form (0/1-input gates, forward references reading false, missing
  output wire); it is normalised on load. Output uses only 2-input AND/OR, 1-input NOT, wires defined before use.
  The one exception is a constant output, written as a 0-input gate (`or` = false, `and` = true), which is
  legal in `ao`/`aon` but not in `ao2`.

Determinism: threads only exchange circuits at round boundaries, and a round is a fixed amount of counted work,
not of time. So the result is a function of `(SPEC, IN, --seed, -j, number of rounds completed)`. With `--rounds`
two runs give byte-identical output (tested with `-j 1`; the `-j 2` test needs `MT=1`, see Tests). With `--time`
the number of rounds depends on machine load.

## What it does

Every wire is a P-bit column over the spec's points (P = n·m for a graph spec, 2^N for a tt spec). All checks are
exact bit-parallel simulation on those points; there is no SAT call anywhere.

The key fact used by the column moves: for a gate g let obs(g) be the set of points where flipping g flips some
cared output bit (one re-simulation of g's fanout cone with g complemented). Replacing g by ANY function f of
wires outside g's fanout cone is correct if and only if f = g on obs(g), because points are independent. So a
candidate is checked with one compare over the column. on(g) = g ∧ obs, off(g) = ¬g ∧ obs.

Moves, in the order of `--level`:

1. Cleanup. Structural hashing, constant propagation, double NOT, x∧x, x∧¬x, dead gates, copies; at level 1 a
   gate is merged with any wire equal to it on all cared points.
2. 0-resubstitution with observability. g is replaced by an existing wire (or a constant) that agrees with it on
   obs(g); g and whatever only g needed disappear. In basis `aon` also NOT of an existing wire.
3. Cover resubstitution. g := OR of k existing wires that avoid off(g) and together cover on(g), or dually
   g := AND of k wires that contain on(g) and together kill off(g); accepted when it frees more gates than the k−1
   it adds (exact reference counting). Depth-first set cover, branching on the uncovered point with the fewest
   candidates. In `aon`, complemented wires (¬w with w ⊇ off) are candidates at cost one gate.
4. 2-level terms. The cover may also use a new AND of two wires (in an OR cover) or a new OR of two wires (in an
   AND cover), at cost one gate. This is the "window resynthesis with free outside leaves" of the brief, restricted
   to two levels: there is NO exhaustive enumeration of 4–5-gate windows and no multi-output window.
5. Escape moves.
   (a) Size-neutral rewrites: the same searches accepted at gain 0 with a per-thread probability.
   (b) Paar extraction: AND-trees and OR-trees are flattened to leaf sets, the leaf pair occurring in most sets is
       materialised repeatedly, trees are rebuilt with random shapes; kept only if not larger.
   (c) Set-space sharing optimiser. An OR-forest (dually an AND-forest) is treated purely as a family of leaf
       sets: every OR gate that feeds something other than an OR gate must stay the union of exactly the same
       non-OR wires; how the unions are built and shared is free, and no simulation is needed. Large-neighbourhood
       search: take 1–4 terminals with overlapping sets, drop their private structure, re-cover each with the
       fewest existing sub-unions (exact minimum set cover on at most 64 leaves), extract pairs common to the
       group, keep the result if the forest did not grow. On the 1500-gate cand128 seed it reaches 1470 in 18 s
       alone; the column moves with Paar needed about 69 s for the same size.
   (d) Threads run independent seeds and any thread more than 0–2 gates behind the best restarts from it at the
       next round.

Candidate lookup for the column moves uses a transposed index (for each point, the bitset of wires that are 1
there). Points are randomly permuted at load so every 64-bit word is a random sample and early exits are
effective. The index is skipped when it would exceed 96 MB per thread (`--no-index` forces that path).

Guarantees: moves 1–4 and 5(b), 5(c) never increase the gate count. After every replacement the affected cone is
re-simulated and all outputs are compared with the spec; a mismatch (never seen) discards that thread's network.
Every improvement is exported and re-verified with `pnp::verify` on the un-permuted spec before it is written.

## Measured throughput (Apple M5 Max, one thread, machine load average about 40 during the measurement)

`bin/cktopt SPEC IN --bench -j 1`; `pnp::eval` reference from `bin/cktcheck --bench`.

| spec / circuit | observability evaluator | pnp::eval | strict gate visits |
|---|---|---|---|
| cand128, 2023-gate seed (average cone 119 gates) | 8.2e10 gate·points/s | 9.3e10 | 14,500 /s |
| cand128, 1473-gate circuit (average cone 15) | 7.2e10 | 9.6e10 | 19,600 /s |
| cand32, 206-gate seed | 3.0e10 | 9.2e10 | 115,000 /s |
| mm3, naive 45 gates (262,144 points) | 4.5e10 | 9.5e10 | 12,700 /s |

A gate visit = fanout marking + observability + candidate lookup + cover searches. In a level-5 run the evaluator
is not the bottleneck: a profile of the cand128 seed run has about 57 % of the samples in candidate feasibility
checks and cover searches and 13 % in the evaluator. (Measured before a later 15–20 % speed-up of the feasibility
check; the table above was also measured before it.)

## Results (all files pass `bin/cktcheck SPEC FILE --basis aon`)

Neither live threshold was reached. Everything here is an upper bound; nothing is a lower bound.

### cand128 (aon), wanted <= 1350. Best: 1461, `found/cand128_1461_aon.ckt`

| start | result | run |
|---|---|---|
| seeds/cand128_1500_from_L_meta_19358.ckt, 1500 | 1466 | final binary, defaults, 1 thread, 54 s: 1493 at 0.3 s, 1479 at 3.9 s, 1471 at 16 s, 1468 at 43 s. Gates by move: sharing optimiser 26, Paar 7, 0-resubstitution 1. `runs/cktopt/cand128/final_from1500.ckt` |
| same 1500 seed, before the sharing optimiser existed | 1472, then 1469, then 1466 | 1 thread, three consecutive runs of 52–54 s (column moves + Paar only) |
| same 1500 seed, sharing optimiser alone | 1485 in 0.6 s, 1470 in 18 s | 1 thread, `--share-only 2e8` / `6e9` |
| found/cand128_1464_aon.ckt (graphsynth 1467, then cktopt run by another agent) | 1463, then 1462, then 1461 | 1 thread, 54 s; then `--share-only 4e9` (12 s); then `--share-only 4e9 --share-group 12 --seed 4` (13 s) |
| found/cand128_1466_aon.ckt (graphsynth, seed 41) | 1464 | 1 thread, 38 s |
| found/cand128_1475_aon.ckt (graphsynth 1478) | 1473 | 1 thread, 2 × 45 s |
| seeds/cand128_2046.ckt, 2023 | 1712 | 3 threads, 150 s through pnprun; 1714 at 79 s |
| biclique cover seed, 2194 (the 2023 seed's 106 big bicliques + 24 more from `graphcover.py`, plain OR chains) | 1642 | 1 thread, 50 s; 1645 at 27 s |
| naive row-major circuit, 6612 | 2645 | 1 thread, 50 s; still falling at about 3 gates/s when stopped |

The 1463 → 1463 run of the full loop (54 s, 641,600 gate visits) found nothing; the 1462 came from the sharing
optimiser alone. A further 54 s of the final binary on the 1462 circuit (510,456 gate visits) found nothing, and
so did five more sharing-only runs of 12–14 s with other seeds and group sizes on 1462 and 1461. Multi-thread runs on these circuits were queued through pnprun
(3 threads, later 2) for over an hour and never got slots; they were cancelled, so there is NO multi-thread
measurement on the 1500-class circuits. `runs/cktopt/mt.sh` is the check that was queued
(`bin/pnprun -c 2 -m 2 -t 400 -- sh runs/cktopt/mt.sh`: `-j 2` determinism, then 240 s on the 1461 circuit).

Size against time, 2023 seed, 3 threads: 1913 after round 1 (0.2 s), 1737 at 15 s, 1723 at 31 s, 1717 at 61 s,
1714 at 79 s, 1713 at 123 s, 1712 at 150 s. Moves in that run (sum over the 3 threads, including work repeated
after restarts): OR-cover 403 gates, 0-resubstitution 199, Paar 88, AND-cover 44, 2-level terms 3, NOT 0,
constants 0; 148,498 size-neutral rewrites; 8.06 M gate visits. From the 1500 seed (first 52 s): Paar 19 gates,
OR-cover 9, nothing else.

### cand32 (aon), wanted <= 150. Best known stays 180 (the seed); cktopt did not improve it

| start | result | run |
|---|---|---|
| seeds/cand32_180_from_L_meta_20578.ckt, 180 | 180 | 1 thread, 50 s default (8.25 M visits, 138,782 neutral rewrites, 0 gains); 20 s with `--max-terms 8 --rar 0.3 --pair-every 2`; 50 s with annealed partner exchanges; `--share-only 3e9` |
| seeds/cand32_190_from_L_meta_19143.ckt, 190 | 184 | 1 thread, 20 s |
| seeds/cand32_207.ckt, 206 | 200 | 1 thread, 50 s; 200 reached at 15 s. `found/cand32_200_aon.ckt` (superseded by the 180 seed) |
| naive row-major circuit, 442 gates (no knowledge of the factorisation) | 201 | 1 thread, 20 s. `runs/cktopt/cand32/naive_rows_201.ckt` |
| naive column-major circuit, 442 | 202 | 1 thread, 20 s |
| five greedy biclique covers, 318–345 | 208–229 | 1 thread, 8 s each |

### Other specs (not graph-specific; 1 thread unless noted)

| spec, basis | start | result | time | known |
|---|---|---|---|---|
| cyc7, aon | naive DNF, 699 gates | 10 | 4 s | 10 is the exact size |
| match3, aon | naive DNF, 2231 | 14 | 4 s | 14 already in found/ |
| mm2, aon | naive DNF, 3588 | 12 | 4 s | 12 = naive product |
| kn5, aon | naive DNF, 54 | 10 | 4 s | K(5) = 10 |
| kn6, ao | monotone DNF, 29 | 13 | 15 s, `-j 3` | K(6) = 13 |
| kn7, ao | monotone DNF, 41 | 16 | 15 s, `-j 3` | K(7) in {15, 16} |
| match3, ao | monotone DNF, 17 | 14 | 15 s, `-j 3` | wanted 13 |
| crown7, ao | monotone DNF, 83 | 23 | 15 s, `-j 3` | 22 or 23 |
| mm3, aon | naive product, 45 | 45 | 40 s | no move applies: full truth table, no slack |

The four `-j 3` rows were run outside pnprun under the earlier rule that allowed 3 threads. They only match known bounds.

## What the 64-AND circuits are (checked on every AND gate)

`seeds/cand128_1500_from_L_meta_19358.ckt` is not a cover by 64 bigger bicliques. Each of its 64 AND gates reads
two wires of the form (8 full rows ∪ 8 full columns), and its value is exactly two bicliques:

    (rows R1 ∪ cols C1) AND (rows R2 ∪ cols C2) = R1×C2 ∪ R2×C1,   with R1 ∩ R2 = ∅ and C1 ∩ C2 = ∅ in all 64 gates.

That gives 128 bicliques, 121 of them 8×8 (the rest 7×8, 8×7, 8×9, 9×8), two per AND. It is essentially the
planted cover the 2023 seed already had in part: of that seed's 106 big bicliques, 66 are identical to one of the
128 and 100 are within two row/column changes of one. The 1462-gate circuit (graphsynth lineage) uses 128
bicliques too, 115 of them identical to the 1500 seed's; it differs in partners and sharing.
`cand32_180` is the same construction (16 ANDs, 31 bicliques, 15 of them 4×4). `cand128_1887` and the 2023 seed
have one biclique per AND.

The pairing saves nothing in the term structure: two bicliques cost 2 AND + 2 OR unpaired, and 1 AND + 1 OR + 2
joining ORs paired. Without sharing both forms cost 128 × 16 − 1 = 2047. The whole gain is OR-sharing: a paired
input is one 16-leaf set over 256 leaves instead of two 8-leaf sets over 128, mixed pairs (row ∨ column) can be
shared (195 such gates in the 1500 seed), and the choice of partners can be tuned so that sets overlap.
Measured, OR gates per 16-leaf set: 10.7 in the 1500 seed and 10.4 at 1462, against 15 unshared. So a pair of
bicliques costs 2 × 10.4 + 1 AND + 1 OR = 22.9 gates at 1462. In the unpaired 1642-gate circuit (134 terms, not
the same cover) an 8-leaf set costs 5.1 OR gates, so a pair costs 4 × 5.1 + 2 AND + 2 OR = 24.5: the two joining
ORs of the paired form are paid for entirely by extra sharing.

## How much don't-care freedom is left (measured on `found/cand128_1463_aon.ckt`, exact)

* 91.8 % of the ones of the OR-gate wires are unobservable (988,834 of 1,076,739 wire·point ones).
* But for 1234 of the 1399 OR gates there is no existing wire outside the fanout cone that avoids off(g), touches
  on(g) and is not already a structural subset of g; 145 gates have one such wire, 17 have two, 3 have three
  (0.1 per gate on average, against 10.3 subset candidates per gate).

So on these circuits observability-aware resubstitution has nothing to pick from: the don't-cares are large but
every useful candidate is an exact sub-union. What remains is exact shared-union optimisation plus the choice of
partners. Complemented candidates fired zero times in every run on every cand circuit.

Partner exchange (`--share-repair`, experimental): exchange the partners of two product gates, re-cover the four
sets, polish, keep if the forest did not grow. It detects the 64 (cand128) and 15–16 (cand32) product gates and
checks validity exactly (rows disjoint, columns disjoint, via which leaves meet on some point). On the 1463
circuit the cheap estimate over 7601 valid exchanges was +21.5 gates on average and never below +7, and with 400
polish trials an exchange still cost +16 on average. On cand32_180 the minimum was +3 (average +8.9). With
annealing (`--share-temp`) exchanges are accepted but 180 was not beaten in 16 s or in 50 s. The pairings in these
circuits are local optima under two-gate exchanges.

## What did not work

* Redundancy addition and removal (`--rar`): cand32 seed 156,185 trials for 2 gates; cand128 from the 1712
  circuit 31,319 trials, 0 gates; cand32_180 305,471 trials, 0 gates.
* Preferring popular wires in size-neutral rewrites (`--side-mode 1|2`): within run-to-run noise.
* More cover terms (`--max-terms 8 --dfs 1500`): 1743 and 1730 against 1733 and 1734 at equal work from the
  2023 seed, two seeds each.
* Partner exchanges, see above.
* A greedy biclique cover from scratch (`graphcover.py cover` on all 186,976 big bicliques): 2864 gates before
  shrinking, 1728 after 100 s and still falling slowly — worse than keeping the planted bicliques.

## Helper scripts and tests

* `src/cktopt/tools/graphcover.py` (run with `bin/satpy`): `enum` lists closed bicliques of a graph spec, `cover`
  writes a greedy biclique-cover circuit, optionally keeping the big bicliques of an existing circuit. cand32 has
  1893 closed bicliques (0.1 s). cand128 has 186,976 closed bicliques with at least 8 rows and 8 columns; that list
  came from an earlier scratch version of the enumeration (125 s) and is not stored in the repo. The `enum` in the
  repo was only run on cand32.
* `src/cktopt/tests/run_tests.sh [WORKDIR]`: 30 single-threaded runs plus a determinism check, about 28 s, all
  passing on the final binary —
  8 random bloated circuits in both bases with and without don't-cares and with 1 or 3 outputs, DNF circuits for
  match3/cyc7/kn5/kn6/mm2, every `--level`, the no-index path, the experimental moves, the sharing optimiser alone
  and with exchanges, Lean-style degenerate input. Most use `--debug`. `MT=1` adds two 2-thread runs through
  `bin/pnprun`; those two were NOT run (no free slots).
  `src/cktopt/tests/gen.py` generates the inputs (`random`, `dnf`, `mdnf`, `mm`, `degenerate`).

## Limitations

* Heuristic. No minimality claim, no "no smaller circuit exists" claim of any kind.
* No exhaustive window enumeration and no multi-output column moves (see move 4).
* The sharing optimiser only handles terminals with at most 64 leaves; larger ones keep their structure.
* The random test circuits collapse to 1–11 gates, so they test correctness more than shrinking power.
* Multi-threading was exercised only in early development runs (`-j 2`, `-j 3`) and in one 150 s pnprun job, all
  before the sharing optimiser and several later changes. The final binary was run single-threaded only.
* Memory per thread is about 16 bytes × wires × P/64 plus the point index (at most 96 MB): about 25 MB for
  cand128. A tt spec with more than about 22 inputs and a large circuit will hit `--mem`.
* No change to `include/ckt.hpp` was needed.
