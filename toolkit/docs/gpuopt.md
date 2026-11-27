# gpuopt — GPU-accelerated don't-care circuit shrinker

Takes a spec, a correct circuit and a basis; returns a circuit of the same function on the cared points that is
no larger. **Heuristic**: it proves nothing about minimality. Every move is checked by a full re-simulation
before it is kept, every round's circuit passes `pnp::verify` and `basis_ok` before it can become the best,
and the best is verified again before it is written.

**Result in one line: it did not beat the circuits the CPU tools already had** (cand128 stays at 1462,
cand32 at 180; the units want 1350 and 150). What it adds is an exhaustive statement about those
circuits (section "Results") and measured GPU numbers (section "Throughput").

Sources: `src/gpuopt/gpuopt.cpp` (one file) on top of `src/gpukit/` (docs/gpukit.md). `make -C src/gpuopt`.

## CLI

    bin/gpuopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [--time S] [--rounds R] [--seed X] [--target SIZE]
        --time S          stop after S seconds (default 50; checked inside a round too)
        --rounds R        stop after R rounds instead: fully deterministic for (SPEC, IN, --seed, R)
        --cpu             run the same kernels as plain C++ loops (no GPU, no lock); same results, bit for bit
        --check           after every GPU dispatch recompute it on the CPU and abort on any difference
        --neutral F       size-neutral rewrites per round, as a fraction of the gate count (default 0.05)
        --no-pairs        skip the all-pairs kernel       --no-covers   skip the exact cover moves
        --two-every K     2-level terms every K-th round (default 0 = off, see Results)
        --two-on-words N  ... only for gates whose on-set touches <= N 64-bit words (default 16)
        --bb NODES        branch-and-bound budget per cover search (default 800)
        --max-lits L      widest candidate list given to the exact cover search (default and maximum 256)
        --no-neg          no complemented operands in basis aon
        --found DIR       also save the final / periodic best as DIR/<spec>_<size>_<basis>.ckt, only if it is
                          smaller than every such file already in DIR
        --stats           per-round distribution of candidate-list and care-set sizes
        -q | -v | -vv     quiet / every round / debug

* One CPU thread (`-j` is accepted and ignored). GPU buffers: 160 MB on cand128 (printed at start). Longest single
  GPU dispatch with default settings in the runs below: 42.4 ms (2023-gate seed), 28.5 ms on the 1462-gate circuit.
* Run it as `bin/gpurun -- bin/gpuopt ...` (or bare: it takes the GPU lock itself). Longer than 60 s:
  `bin/pnprun -c 1 -- bin/gpurun -- bin/gpuopt ... --time S`.
* stderr: progress and a table of time, work and moves. stdout: `size N and A or O not T`.
  OUT is rewritten at every improvement.
* Input may use any Lean-legal degenerate gate (copies, constants, forward references); it is normalised.
  Output: 2-input AND/OR, 1-input NOT, operands defined earlier. A constant output is refused (exit 2).
* Limits: fewer than 32,768 wires; cover search only for lists of at most 256 candidates; no move replaces a gate
  by a constant (a gate that is constant on its care set is only removed if some wire or cover says the same).

## What one round does

Every wire is a P-bit column (64-bit words, in a shared GPU buffer). For gate g, care(g) is the set of points
where complementing g changes a cared output (exact: its fanout cone is re-simulated with g flipped, on the
CPU: 6 ms for all gates of the 1462-gate cand128 circuit, 25 ms on the 2023-gate seed). on(g) = g ∧ care(g), off(g) = ¬g ∧ care(g). Replacing g by any function
of wires outside its fanout cone that equals g on care(g) keeps the circuit correct.

1. **GPU "singles"**: for every (gate g, wire w), four exact flags: w or ¬w has no false positive on off(g)
   (usable in an OR), w or ¬w has no false negative on on(g) (usable in an AND). 2.5 M (gate, wire) tests of
   16,384 bits per round on cand128.
2. **GPU "pairs"**: for every gate p and each of its two operands f, and every admissible literal i outside
   the fanout cone of f: over ALL admissible j, is `OR(i, j)` (resp. `AND(i, j)`) equal to p on care(p)? One
   result per i: the best partner (by a per-wire preference with seeded jitter) and the number of feasible
   partners. Complemented literals are included in basis aon. 1.5e9 pair tests per round on cand128.
3. CPU moves, each one applied, re-simulated and kept only if the circuit is still right:
   * **single**: g := w or ¬w (g and everything only g needed disappear).
   * **pair-kill**: gate x dies if every reader p of x has a feasible pair that does not depend on x.
   * **cover**: exact minimum of (#operands + #gates of g's fanout-free cone they keep alive) over OR-covers of
     on(g) and AND-covers of off(g) by admissible wires; branch and bound on the point with the fewest
     candidates. Accepted when it frees a gate.
   * **cover-kill**: a gate x with 2–4 readers dies if every reader (or the root of the fanout-free chain above
     it) has a cover avoiding everything that depends on x, and the extra gates of those covers are fewer
     than what x frees. This is a two-step look-ahead the plain cover move does not see.
   * **neutral**: random same-cost covers / pairs, to move on the plateau.
   * optional **2-level terms** (`--two-every`): a third GPU kernel finds, for every gate g and every wire i
     that is not admissible alone, the wire j maximising |on(g) ∧ i ∧ j| among all j with i ∧ j free of false
     positives; the best 48 products per gate enter the OR-cover search at cost 2.
4. Rebuild: dead gates dropped, structural hashing, wires with identical columns merged; `pnp::verify`.

The GPU results carry no information the CPU does not re-check: a wrong kernel could cost gains, never
correctness.

## Validation

* `sh src/gpuopt/run_tests.sh WORKDIR` (7 s): 14 cases — random bloated circuits in both bases, with and
  without don't-cares, 1 and 3 outputs; naive DNF circuits for cyc7, match3, kn5, mm2 (4 outputs);
  a Lean-degenerate rewrite of the cand32 seed; cand32 in basis ao. Each case runs with `--check` (every GPU
  dispatch of all three kernels compared bit-exactly with the C++ reference), the output passes
  `bin/cktcheck`, and the GPU result equals the `--cpu` result byte for byte. All 14 pass.
  (Sizes reached there and in separate 4 s runs: cyc7 699 → 13, match3 2231 → 17, kn5 54 → 19, mm2 3588 → 12,
  random 140–167 → 2–13. docs/cktopt.md reports 10 / 14 / 10 / 12 for the same four DNF inputs in 4 s: gpuopt stops
  at worse local optima on cyc7, match3 and kn5; it has no Paar extraction and no replace-by-constant move.)
* cand128, 3 rounds from the 1462-gate circuit, GPU against `--cpu`: identical output file.
* Same seed, same `--rounds`: identical output (checked).
* Every circuit named below passes `bin/cktcheck SPEC FILE --basis aon`.

## Throughput (Apple M5 Max, one CPU thread + GPU, machine load average 18–30)

Same code path, same data, identical results (cand128, the 1462-gate circuit, 3 rounds):

| kernel | work | GPU: wall (GPU time) | 1 CPU core, same loop with the same early exits | ratio |
|---|---|---|---|---|
| singles | 7.5e6 (gate, wire) tests x 16,384 bits | 0.04 s (0.03 s) | 2.29 s | 57x |
| pairs | 4.48e9 exact pair tests | 0.09 s (0.06 s) | 11.14 s | 124x |
| whole round | | 0.17 s | 4.6 s | 27x |

Rates in long runs: singles 3.4–4.3e8 (gate, wire) tests/s = 6e12 bit-tests/s; pairs 4–8e10 exact pair tests/s
(early exit after about one word on average); 2-level products 2e9 tests/s for gates with a narrow on-set and
only 1.4e7/s on the full-width path (every pair then needs a 256-word scan; that path is not optimised).
In a default round the GPU is busy for 0.02 s of 0.2 s; the rest is one CPU thread (cover searches and
re-simulation of every tried move), so more GPU would change nothing.

Gates removed against time (default settings, seed 1 / 2, `--time 50` / `--time 40`):

| start | trajectory | moves that removed gates |
|---|---|---|
| seeds/cand128_2046.ckt, 2023 gates | 1953 at 0.6 s (round 0), 1866 at 7.1 s, 1838 at 14.5 s, 1819 at 27.1 s, 1801 at 38.4 s, **1794** at 50 s (125 rounds, still falling; an earlier identical run on a less loaded machine did 137 rounds and ended at 1791) | single 75, pair-kill 54, cover 61, cover-kill 14; 13,367 neutral rewrites |
| seeds/cand128_1500_from_L_meta_19358.ckt | **1495** at 40 s (185 rounds) | pair-kill 1, cover 4 |
| found/cand128_1462_aon.ckt (current best) | **1462** at 40 s (191 rounds) | none; 22,693 neutral rewrites |
| seeds/cand32_207.ckt, 206 gates | 205 or 206 at 20 s (2253 rounds; one seed found 1 pair-kill) | – |
| seeds/cand32_180_from_L_meta_20578.ckt | **180** at 12 s (2505 rounds) | none; 24,894 neutral rewrites |
| found/cand32_181_aon.ckt | 181 at 12 s | none |

For comparison cktopt (CPU, docs/cktopt.md) takes the 2023-gate seed to 1717 in 61 s on 3 threads and the
206-gate cand32 seed to 200 in 15 s on one. gpuopt is the weaker shrinker; see below for why.

## Results

No file was added to `found/`: nothing gpuopt produced is smaller than what is there.

| spec | best known (others) | gpuopt from it | unit wants |
|---|---|---|---|
| cand128 | 1462, found/cand128_1462_aon.ckt (from the other builders' tools) | 1462 | <= 1350 |
| cand32 | 180, seeds/cand32_180_from_L_meta_20578.ckt | 180 | <= 150 |

What the runs do establish about `found/cand128_1462_aon.ckt` and the 180-gate cand32 circuit (measured, not
a proof of minimality; "exhaustive" is over the moves named, with the stated caps):

* no gate can be replaced by an existing wire or its complement (all 2.5 M (gate, wire) combinations per
  round, 191 rounds on cand128, 2,505 on cand32);
* no gate can be freed by re-expressing a reader as OR or AND of any two wires, complemented or not
  (2.4e11 exact pair tests on cand128 over the 40 s run; 6,374 feasible pairs were found, all size-neutral);
* no exact OR/AND cover frees a gate, and no gate with 2–4 readers can be removed by re-covering all its
  readers (794,709 cover searches on cand128, 1,411 of them cut at the 800-node budget; AND lists wider than
  256 candidates are not searched, and on cand128 the median AND list has about 1,000);
* 2-level terms: 0 covers used one. cand128: 5 passes over all gates, 2.8e9 product tests, 3.0 M products
  offered; cand32: 313 passes, 6.0e8 tests, 3.6 M offered. This is why the option is off by default.
* 22,693 random size-neutral rewrites on cand128 (24,894 on cand32), each followed by the searches above, opened
  nothing.

## What the GPU does and does not buy here

The brief's premise was that scoring all pairs of wires is the inner loop. Measured on these circuits:

* The dense kernel is as fast as hoped (110x one core on dense data, 57–124x inside the tool).
* But the problem is sparse. In `--stats` on the 1473-gate cand128 circuit the median gate has 31 on-points
  and 6 admissible OR operands, complements included (90 % have at most 28); an OR-cover search is a set cover over a few dozen
  points and wires. cktopt gets the same candidates from a transposed index (per point, the wires that are 1
  there) at 19,600 gate visits/s on one core, so brute force over 1,700 wires x 16,384 bits per gate only
  re-derives what an index gives for free. The one dense spot, AND operands (median list 1,000 wires, 1.5e9
  pair tests per round), is where the GPU is needed, and it finds almost nothing: about 30 feasible AND/OR
  pairs per round, all neutral.
* After the kernels the round is bounded by one CPU thread doing branch and bound and re-simulation.
* The circuits are 96 % OR gates computing 128 mixed row/column sets of 16 inputs; what is left is the
  shared-union ("ensemble") problem plus the choice of which rectangles share an AND gate. docs/graphsynth.md
  estimates 1420–1450 as the floor of that shape. No local move here, exhaustive or not, crosses it: the
  remaining freedom is a global re-pairing, which is combinatorial search on small sets, not dense bit work.

## What failed

* Reaching either unit threshold, or improving the best known circuit at all.
* 2-level terms (exhaustive best-partner version): no gain, and the full-width kernel path is slow (36 s of
  GPU for one cand128 pass, single dispatches up to 66 ms before the pacing was fixed; with defaults it is off).
* First version of the cover accounting counted only 64 gates of a larger fanout-free cone as freed and
  produced 22,000 "gains" that were not; fixed (cones deeper than 64 gates count as staying alive).
* Pacing dispatches by item count gave one dispatch of 341 ms on the 2023-gate seed (thread cost differs by
  orders of magnitude between gates); replaced by pacing on estimated work.
* A 9-minute run through `pnprun` never started: all 12 core-slots were held for the 25 minutes it waited,
  so nothing here ran longer than 50 s.

## What I would do next

1. Not more dense kernels for cand128/cand32. If the GPU is to help there, it has to run the search the
   graphsynth author names as next step: re-pairing at the true cost, i.e. thousands of independent
   annealing chains over (pairing, node set) with exact min-cover of 16-element sets as the cost. That is
   "tiny fixed state per item" and fits gpukit; the cost function is a set cover over a 16-bit universe.
2. Add Paar extraction and a transposed candidate index so gpuopt matches cktopt from a raw seed, then keep
   the GPU for what the index cannot do (AND lists, complemented operands, kills).
3. Use the pair-score kernel where data is dense: stochastic search on full truth tables (mm3 has 262,144
   points; every (position, operand pair) score there is a dense popcount), not on one-hot graph specs.
