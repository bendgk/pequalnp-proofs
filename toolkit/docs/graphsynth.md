# graphsynth — constructive search for small circuits representing a bipartite graph

`bin/graphsynth` builds AND/OR(/NOT) fan-in-two circuits for `type graph` specs (the "candidate family" units,
`specs/cand32.spec`, `specs/cand128.spec`). It is a **heuristic upper-bound tool**: every circuit it writes has been
re-verified with `pnp::verify`, but it proves nothing about optimality and never claims UNSAT.

Sources: `src/graphsynth/` (`make -C src/graphsynth`), helper `src/graphsynth/py/boolrank.py`.

## CLI

    bin/graphsynth SPEC -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X]
        --rounds R --iters N      R annealing rounds of N moves per thread (default 4 rounds, 25000 moves per rectangle)
        --shape NAME              auto | atoms | concepts | wcover | rows | cols | grow | comp | init
        --init-ckt FILE           start from the cover + pairing of an existing circuit of the same shape
        --atom D                  side of the planted rectangles (default round(sqrt(min(n,m)/2)))
        --found DIR               also save every improvement as DIR/<spec>_<size>_<basis>.ckt
        --restart K               new lineage after K rounds without progress (default 4)
        -v                        per-round log, move statistics, structure of the best state
    bin/graphsynth SPEC --analyze [--ckt C.ckt]     structure report (graph, planted-cover test, circuit anatomy)
    bin/satpy src/graphsynth/py/boolrank.py SPEC K [--time S]   SAT: is there a cover with <= K bicliques?

`graphsynth --help` lists the tuning flags (temperatures, move mix, proxy pairing, weight-annealed covers).
Threads: `-j T`, default `$PNP_THREADS` or 1. Runs with `--rounds`/`--iters` are reproducible for a fixed
`--seed` and `-j` (checked: two runs give byte-identical output); `--time` stops at a round boundary, so the number of
rounds then depends on the machine. Memory: a few MB per thread. n, m <= 128.
Results go to stdout (one line), progress to stderr.

## What it builds

Under the one-row/one-column promise every wire is an n x m 0/1 matrix. The tool only builds this shape:

    OUT = OR over terms j of (S_j AND T_j),   S_j, T_j = OR of some row wires and some column wires ("crosses")

* solo term for a rectangle (biclique) U x V:  S = OR rows(U), T = OR cols(V).
* **cross term** for two rectangles a, b with U_a ∩ U_b = ∅ and V_a ∩ V_b = ∅:
  S = OR(rows(U_a) ∪ cols(V_b)), T = OR(rows(U_b) ∪ cols(V_a)); then S AND T = U_a x V_a ∪ U_b x V_b.
  The gate count before sharing is the same as two solo terms, but the sets become mixed row/column sets, and mixed
  sets share far more sub-unions (measured below). This is also the shape of the two best circuits already in
  pequalnp-proofs (L_meta_20578, 180 gates for cand32; L_meta_19358, 1500 gates for cand128).

gates = #terms (AND) + #terms - 1 (OR) + cost of the OR-ensemble {S_j, T_j}. No NOT gate is used in this shape, so
the circuits are also valid in basis `ao` and `ao2` (checked with `cktcheck --basis ao2`). The only shape with a NOT
is `comp` (NOT of a cover of the complement graph, basis aon only).

### Pipeline

1. **Covers** ("shapes"). `atoms`: closed bicliques with both sides >= d (Close-by-One enumeration, 0.6-1.2 s for the
   187,719 such bicliques of cand128), exact cover by "edge with fewest candidates first", pruning, a
   one-in/several-out local search and trimming of redundant rows/columns. `wcover`: simulated annealing over exact
   covers minimising sum(|U|+|V|) + 3 per rectangle (sub-bicliques allowed; compound "plant/extend/merge then trim"
   moves; 50k compound moves/s on cand32). `concepts`: all closed bicliques. `rows`/`cols`: stars (the rows-first /
   columns-first shapes). `grow`: greedy growth from uncovered edges. `comp`: cover of the complement + one NOT.
   `init`: cover and pairing read out of a given circuit.
2. **Pairing proxy**: which rectangles are crossed. A QAP-style annealing (about 10M swaps/s) maximises
   sum over pairs of cross sets of f(|overlap|) with f(3) = 1, f(4) = 3, ... (overlaps of >= 3 elements are what
   pays), with a bonus that first maximises the number of pairs.
3. **OR-ensemble optimiser**: a node is a set of >= 2 inputs that gets a wire; each node is the OR of an exact minimum
   cover by smaller nodes and single inputs (branch & bound, capped at 4000 nodes per cover), so the cost is a
   function of the node set. Greedy start (Paar: unite the two pieces that co-occur in most covers), then annealing
   over node sets: add an intersection of two nodes (or a pair / near-intersection), add the union of two pieces,
   remove, modify by one element. All moves are journaled and undone exactly; nodes may be built from other targets
   (subset-lattice reuse) and overlapping pieces are allowed (OR is idempotent).
4. **Joint moves at the true gate count**: re-pair two cross terms, pair/split, add/remove one row or column of a
   rectangle (exact cover counts are kept), delete a redundant rectangle / plant a new one, and **refit**: recompute a
   target inside its don't-care interval [L, H] (rows whose edges are covered twice may go, rows adjacent to the whole
   other side may come) and snap it to whatever the existing nodes make cheapest, including an existing node.
   10% of the term-changing moves are followed by a local re-sharing pass.
5. Rounds, one lane per thread; a lane that stalls 4 rounds restarts with a new pairing (and, on small graphs, a new
   weight-annealed cover). The best circuit is rebuilt, verified and written whenever it improves.

### Throughput (measured, Apple M5 Max, one thread unless stated, machine under load 30+)

| what | rate |
|---|---|
| annealing moves, cand128 (128 rectangles, ~450 nodes), T 0.24 -> 0.09 | 0.37-0.46 M moves/s per thread |
| annealing moves, cand32 | 1.3-1.45 M moves/s per thread |
| 3 threads, cand128, before the load rule (outside pnprun) | 0.7-1.1 M moves/s total at low T, 2.0-2.6 M/s at T = 0.6 |
| proxy pairing | 12.8 M swaps in about 1.3 s |
| closed bicliques >= 8x8 of cand128 | 4.9 M concepts visited, 187,719 reported, 0.6 s |
| weight annealing of covers, cand32 | 50k compound moves/s (each trims the whole cover) |

A "move" is one proposed change that reached evaluation or was rejected as not applicable.

## Results

All files below were checked with `bin/cktcheck SPEC FILE --basis aon` (exit 0).

| spec | size | file | how |
|---|---|---|---|
| cand128 | 1478 | found/cand128_1478_aon.ckt | `graphsynth specs/cand128.spec --shape atoms --time 45 --seed 4 --reheat 0.15 --wrect 0.2 -j 1` (46 s, before the refit move existed) |
| cand128 | **1467** | found/cand128_1467_aon.ckt | same with `--time 52 --seed 6 --restart 0` (one thread, 52 s) |
| cand128 | **1464** | found/cand128_1464_aon.ckt | the 1467 circuit through `cktopt --time 45 -j 1` (3 "paar" moves) |
| cand32 | 182 | found/cand32_182_aon.ckt | `graphsynth specs/cand32.spec --wvariants 4 --time 55 --seed 7 -j 1` (seeds 11 and 12 also end at 182) |
| cand32 | 181 | found/cand32_181_aon.ckt | the 182 circuit through `cktopt --time 25 -j 1` |

A longer run, `bin/pnprun -c 1 -- graphsynth specs/cand128.spec --shape atoms --time 500 --seed 41 --reheat 0.15
--wrect 0.2 --restart 5 -j 1` (497 s, 69 rounds, 6 lineages, 220.8 M moves, 0.45 M moves/s), ended at 1466
(found/cand128_1466_aon.ckt; cktopt takes it to 1465). So ten times the time buys about nothing over the best of a
few 52 s seeds: the method plateaus at 1466-1470 before cktopt. found/cand128_1463_aon.ckt is the cktopt agent's
further pass over the 1464 circuit.

Seed-to-seed spread on cand128, one thread, about 52 s each: 1478, 1482 (before refit), 1467, 1470, 1470, and 1477
with a ten times longer proxy phase. Continuing from the 1467 circuit with `--init-ckt` gave 1469.

Reference points: TARGETS.md lists 206 / 2023 as known. pequalnp-proofs already contains better checked circuits
(now also in seeds/): L_meta_20578 = 180 gates for cand32 (16 AND), L_meta_19358 = 1500 gates for cand128 (64 AND).
For cand128 the tool improves on 1500 (1467, and 1464 with cktopt). For cand32 it does **not** beat 180: from scratch
182, 181 after cktopt; started from the 180 circuit's own cover with `--init-ckt` it comes back to exactly 180, and
neither graphsynth nor cktopt finds 179. No target line of TARGETS.md (cand32 <= 150, cand128 <= 1350) is met.

**The accepted 64-AND and 16-AND circuits are not covers by 64 / 16 bigger bicliques.** Simulated wire by wire
(`--analyze --ckt FILE -v`, full listings in runs/graphsynth/analyze_cand128_1500.txt and analyze_cand32_180.txt):
every AND gate takes two crosses and yields two rectangles. seeds/cand128_1500_from_L_meta_19358.ckt is 64 cross
pairs over 128 rectangles of weight 2047 ((8,8) x121, (8,7) x3, (7,8), (8,9) x2, (9,8)); 113 of them are identical
to the planted rectangles graphsynth recovers, 14 differ by one row or column, one by two, and each planted
rectangle is used exactly once. seeds/cand32_180_from_L_meta_20578.ckt is 15 cross pairs + 1 solo over 31
rectangles of weight 250 (15 of them 4x4). So "fewer, larger bicliques" is not what those circuits do; they are the
planted cover in the cross shape, which is the shape this tool searches.

### Shapes compared on cand128 (greedy sharing only unless marked "annealed"; seed 1)

| shape | rectangles | weight | gates |
|---|---|---|---|
| atoms, solo terms (rectangle form), annealed | 128 | 2049 | 1644 |
| atoms, cross terms from the unpaired start, annealed | 128 | 2049 | 1497-1510 |
| atoms, cross terms with proxy pairing, greedy only | 128 | 2049 | 1557 |
| atoms, cross terms with proxy pairing, annealed 45-52 s | 128 | 2049 | 1467-1482 |
| rows-first (row stars) | 128 | 6613 | 2862 |
| columns-first (column stars) | 128 | 6613 | 3104 |
| grow (greedy cover, no planted knowledge) | 274 | 3961 | 2990 |
| comp: NOT(cover of the complement) | 224 | 4463 | 3203 |

cand32 (same columns): atoms 34 / 264 / 208, weight-annealed covers 32-36 / 243-257 / 196-211, rows 229, cols 227
(annealed: 203 and 202, i.e. 139 OR gates for the 32 column neighbourhoods against 143 in the 206-gate seed),
grow 240, comp 265. After annealing the cross shape on a weight-annealed cover wins (182-186).

Shapes that were evaluated but not built as circuits:
* **zero cover (AND of ORs)** is the De Morgan dual of `comp` and was not built separately; with NOT available
  `comp` is never worse, and `comp` is 2x off on cand128 and 25% off on cand32 before annealing (the complement has
  density 0.6 and no planted structure).
* **mixed "A = (cover of A') AND NOT (cover of D)"**: `--analyze` measures the cheapest supersets, the bounding
  rectangle of two cover rectangles. cand128: it always contains >= 26 non-edges (67.8 on average) while saving at
  most 6 gates before D is paid for. cand32: at best 1 non-edge for a saving of at most 3 gates, and removing one
  cell costs 3 gates. Not pursued.
* **encode-then-compute** (encoder from the analytic track): one-hot -> index bits. The positive
  recursive encoder costs 2^(k+1) - k - 3 gates a side: 56 (k = 5), 246 (k = 7) (built and simulated on all one-hot
  inputs for k <= 8); with k NOT gates for the negated
  bits that is 61 / 253 a side, 122 / 506 for both sides. The analytic track's 70 / 278 a side (140 / 556 both sides) is the
  monotone encoder producing both polarities. What is left is a 10- resp. 14-input function. To beat the known
  circuits it would have to cost <= 57 gates (cand32, vs 180) or <= 957 (cand128, vs 1464); to meet the targets
  <= 28 (150) or <= 844 (1350). The graphs carry about 850 / 9,600 bits (n random d x d rectangles up to order), a
  typical function of 10 / 14 inputs needs about 2^N/N = 102 / 1170 gates, and no constructive method gets close to
  that count at 14 inputs. The one-hot wires are exactly the minterms of the index bits, so any OR-of-minterms
  construction on the bits has to rebuild them (48 gates a side at k = 5, 164 at k = 7). I did not build a circuit
  of this shape; the numbers say it cannot compete on cand32 and would need a near-optimal 14-input synthesis on
  cand128. As extra wires inside the factorisation shape the bit sets are useless: they are 16- and 64-element
  sets, and no target contains one.

## Structure report (`--analyze`), and the planted-product hypothesis

| | cand32 | cand128 |
|---|---|---|
| edges, density | 411, 0.4014 | 6485, 0.3958 |
| row degrees min / median / max | 4 / 13 / 20 | 8 / 52 / 81 |
| column degrees min / median / max | 4 / 13 / 21 | 15 / 51 / 85 |
| duplicate rows, columns | 0, 0 | 0, 0 |
| nested row pairs, column pairs | 6, 6 | 9, 0 |
| rank GF(2) / GF(2^31-1) | 31 / 32 | 126 / 128 |
| fooling set (greedy) = lower bound on #rectangles | 20 | 50 |
| closed bicliques | 1893, largest area 36 (6x6) | > 3,000,000; 187,719 with both sides >= 8, largest sides (13,8), (8,13), (10,10) |
| smallest exact cover found | 32 rectangles (the 180-gate circuit uses one with 31) | 128 rectangles |
| lightest exact cover found (sum of sides) | 243 (32 rectangles) | 2049 (128 rectangles) |

**The hypothesis holds, in this sharper form: A is the union of n rectangles with d rows and d columns each,
d = sqrt(n/2)** (32 rectangles 4x4; 128 rectangles 8x8), i.e. A = B o C with exactly d ones in every column of B
and every row of C, and r = n middle vertices. Evidence:

1. Density: 1 - (1 - d^2/n^2)^n = 0.3959 / 0.3941 predicted, 0.4014 / 0.3958 observed.
2. Degrees: a row lying in j rectangles has about n(1 - (1 - d/n)^j) ones. Inverting that for every row and summing
   gives 129.0 (cand32; model n*d = 128) and 1034.7 (cand128; model 1024); columns 128.5 and 1032.8.
3. cand128: an exact cover by exactly 128 closed bicliques exists, and after trimming rows/columns that are covered
   twice it is 114 rectangles 8x8 plus 14 that differ by one line ((8,7) x6, (7,8), (8,9) x6, (8,10)); weight 2049
   against 2048 for the model. The weight annealer found nothing lighter in a short run (40,000 compound moves).
   The 1500-gate circuit of L_meta_19358 uses the same 128 rectangles ((8,8) x121), and the 2023-gate seed uses 106
   of them plus 86 row stars.
4. cand32: noise is of the same order as the 4x4 rectangles (1893 closed bicliques), so the planted cover is not
   unique; the lightest exact covers found have 32 rectangles and weight 243-244 (model 256, minus trimming of doubly
   covered lines). Of the 31 rectangles inside the 180-gate circuit 15 are exactly 4x4.
5. The graph is otherwise unstructured: not symmetric, no dependence on u^v, u&v, u+v, u*v mod n, popcounts.

The 187,719 closed 8x8-or-larger bicliques of cand128 are not 187,719 planted rectangles: rows that lie in 12-16
rectangles and columns that lie in 12-16 form a dense core in which 8x8 bicliques arise by chance. This is why a
"largest first" greedy cover ends at 139-153 rectangles and the planted 128 only come out after the local search.

**What the planted structure gives.** The generator's own circuit is the trivial one, 2 n d - 1 = 255 / 2047 gates.
Everything below that is OR-sharing:

| cand128 | gates |
|---|---|
| planted rectangles, no sharing | 2047 |
| rectangle form, shared row sets and shared column sets separately | 1644 |
| cross form, shared mixed sets (this tool) | 1467 (ensemble 1340 + 127) |

### Seed anatomy

* seeds/cand32_207.ckt (206 gates): columns-first. 32 terms y_v AND (OR of the rows adjacent to v), all edges covered
  once, weight 443; 143 gates build the 32 row sets (142 OR and one AND used as an intersection of row sets), 63
  combine. No planted rectangle is used.
* L_meta_20578 (180 gates): 16 terms over 31 rectangles (15 cross pairs + 1 solo), weight 250, 15 of the rectangles
  exactly 4x4; 149 gates build the sets.
* seeds/cand128_2046.ckt (2023 gates): 106 rectangles of the planted cover (sides 8-10) plus 86 row stars for what
  they miss; weight 2660; 1640 gates build the sets, 383 combine.
* L_meta_19358 (1500 gates): 64 cross pairs over the 128 planted rectangles; 1373 gates build the sets.

## Lower bounds and the exact route

* Proved here: nothing beyond the trivial ones. Every rectangle cover needs >= 20 (cand32) / >= 50 (cand128)
  rectangles (fooling sets, greedy), and sum of sides >= n + m = 64 / 256. These are far below what is found.
  An LP bound over all bicliques would be the next step; the toolkit has no LP solver.
* SAT/MaxSAT on cand32 (`src/graphsynth/py/boolrank.py`, closed bicliques, totalizer, single thread): "cover with
  <= K closed bicliques" is solved instantly for K = 60 and is still undecided after 20 s for K = 40 (Glucose 4)
  and after 60 s for K = 31 (CaDiCaL 1.9.5), although covers with 32 rectangles exist. So an RC2 optimality proof
  for the weight (which additionally needs sub-bicliques) is out of reach this way; I did not run it longer.
  The script is correct on crown8 (it finds the 5-biclique cover).
* Why <= 1350 / <= 150 look out of reach **for this shape** (an estimate, not a proof). The planted cover is rigid on
  cand128 (weight 2049 is the lightest found, and a row can leave a rectangle only if all 8 of its edges are covered
  twice). So the cost is 127 + the OR-ensemble of 128 mixed 16-sets, 2048 incidences. A sub-union of s elements
  shared by t sets saves (s-1)(t-1) gates on s*t incidences: 0.25 per incidence for a pair shared twice, 0.33 for a
  triple shared twice or a pair shared three times, 0.375 for a quad shared twice. 1350 needs 0.34 per incidence on
  average; a 1477-gate state has 0.278 (202 pairs, 90 triples, 35 quads, 9 larger shared nodes), and two random
  16-sets share about one element, so triples and quads exist only where the pairing aligns two overlaps. "Gluing" row u to a
  column sigma(u) so that the pair is reused by many sets would need the row hypergraph and the column hypergraph
  to be nearly isomorphic; for independent random ones a first-moment count caps the aligned incidences at about
  half, and at that level the gain over ordinary pair sharing vanishes. Measured: the tool plateaus at 1466-1470 on
  cand128 whether it runs 52 s or 500 s. My guess (not measured) is that a much better pairing search could reach
  1420-1450, still far from 1350. On cand32 graphsynth, cktopt and the earlier 180 all stop at 180-182.

## Limitations

* One circuit shape (OR of ANDs of crosses, plus one optional NOT on top). No intersections or complements inside
  the ensembles, no K(n)-style gluing z_i = x_i OR y_i (crown5 in basis ao comes out at 18 against the known 16,
  crown8 at 33; in basis aon the `comp` shape gives 2n: 10 and 16).
* Heuristic. Results vary by a few gates with the seed; the pairing is fixed by the proxy and practically never
  changes afterwards (re-pairing moves are accepted about once in 10^5 at annealing temperature). A large-neighbourhood
  variant (`--lns-after`) that re-pairs and re-optimises locally kept 0 of 211 trials and is off by default.
* Covers of cand32 from scratch are slightly worse for sharing than the cover inside the 180-gate circuit.
* Threads: the final scheduler (one independent lane per thread, restarts) has only been run with `-j 1`, because all
  12 pnprun slots were held by other jobs once it was finished; a queued `-c 2` run never started. The previous
  scheduler ran with `-j 3`. Lanes share no mutable state (each has its own state, RNG and copy of the cover), and
  verification and file output happen on the main thread between rounds.

## What I would do next

1. Pairing search at the true cost: evaluate a re-pairing by re-annealing the 20-25 targets that lose shared nodes,
   not only the 4 changed ones; or learn a better proxy from which overlaps end up as shared nodes.
2. LP lower bound for the min-weight cover and for the ensemble cost (column generation over bicliques).
3. A second shape family that can use AND/NOT inside the set algebra (intersections of large sets), which is where
   a non-monotone gain would have to come from.
