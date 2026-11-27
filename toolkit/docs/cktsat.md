# cktsat — exact circuit synthesis by SAT cube-and-conquer

Status: working, validated on small cases (see Validation). The Results section at the bottom is updated as runs
finish; the headline results are at its top.

## What it does

Given a spec (FORMAT.md), a basis (`ao`, `aon`, `ao2`) and a gate count `s`, it either prints a circuit with exactly
`s` gates (re-verified with `pnp::verify` and with `bin/cktcheck`) or reports `UNSAT`: no such circuit exists.
The search is exhaustive (it is a proof, not a heuristic), provided the SAT solvers are right.

    bin/cktsat SPEC --basis ao|aon|ao2 -s S [-j T]       exactly S gates: witness or UNSAT
    bin/cktsat SPEC --basis B --min [--lb L] [--ub U]    minimum size: S = L, L+1, ... until SAT
    bin/cktsat SPEC --basis B -s S --upto [--lb L]       sizes L..S in turn ("is there a circuit with at most S gates?")

Main options

| option | meaning |
|---|---|
| `-j T` | exactly T worker processes (default `$PNP_THREADS` or 1). The master only waits on pipes. |
| `--solver auto` | default. Per cube: unit propagation, then a fresh CaDiCaL 1.9.5 for `--pre-budget` (2000) conflicts, then a fresh Kissat 4.0.4. Stateless, so a cube's answer does not depend on scheduling. Also `kissat`, `cadical195-fresh`, `cadical300-fresh`, and incremental `cadical195`, `cadical300`, `glucose42` (cube = assumptions). |
| `--depth D` / `--min-cubes M` | root cubes = canonical prefixes of D gates (default: the first depth with at least M = 200 cubes). |
| `--budget C --growth G` | a cube that uses more than `C * G^(depth - D)` conflicts is split one gate deeper (default 200000, 1.5). `--budget 0`: never split. |
| `--first "and 0 1"` | only circuits whose first canonical gate is this one. The UNSAT line then says so. |
| `--shard i/n` | only root cubes with index = i mod n (own journal per shard). |
| `--resume` | continue from the journal `runs/cktsat_<spec>_<s>_<basis>.jsonl` (stopped runs lose nothing but the cubes in flight). |
| `--no-sym` | ignore the symmetry group (validation). |
| `--full-model` | Lean-exact degenerate gates (constants, copies, missing-wire reads), no symmetry, one SAT call; satisfiable iff a circuit with AT MOST s gates exists (validation of the normal-form argument). |
| `--elim auto` | elimination clauses from cofactor lower bounds, see below. Off by default; the UNSAT claim then also rests on those bounds, which are printed. `--elim "*:0:13"` gives bounds by hand. `--elim-sem 1` adds the semantic rule. |
| `--sens 1`, `--dep 1` | further implied clauses (reader sensitivity, structural support), see Encoding. Off by default; with `--elim-sem 1` they are what made kn7 s = 15 feasible. |
| `--cegar` | counterexample-guided workers: incremental CaDiCaL on a growing subset of the points (start `--cegar-points` 16). For specs with many points (truth tables in basis aon). 30-50x on cyc5/cyc6. |
| `--audit [--recheck K]` | solve nothing: recompute the root cubes and every split natively and check that every leaf is recorded UNSAT. With `--recheck K`, K random leaves are solved again with another solver (CaDiCaL instead of Kissat). |
| `--no-mono-reduce` | bases ao/ao2: keep all cared points (default: only minimal true and maximal false points, see below). |
| `--seed N` | 0 = canonical cube order. Otherwise cubes are shuffled with this seed (useful when hunting a witness). |
| `--time-limit SEC` | per size; the journal is kept, `--resume` continues. |

Exit status: 0 = SAT, 20 = UNSAT, 3 = stopped early.

Files: `bin/cktsat` (launcher), `bin/cktsat-core` (C++: point reduction, symmetry group, canonical prefixes, CNF,
cofactor specs, decoding + verification, brute force), `src/cktsat/{core.cpp, cktsat.py (master), worker.py,
selftest.py, summarize.py (table of all finished runs), Makefile}`. Build: `make -C src/cktsat`.
Recommended for a hard UNSAT: `bin/pnprun -c 4 -- bin/cktsat SPEC --basis ao -s S --elim auto --elim-sem 1
--sens 1 --dep 1 --budget 3000000 --growth 2`; when slots are scarce, n jobs `--shard i/n -j 1` with one slot each.

## The model that an UNSAT covers

"Normal" circuits with exactly `s` gates:

* gate = AND or OR of two distinct earlier wires `a < b`; in basis `aon` also NOT of one earlier wire;
* every gate except an output is read by a later gate (one output: the output is the last gate);
* no gate column is constant on the points, none equals an input column, no two gate columns are equal
  (columns = values on the cared points of the spec, after merging points with identical inputs);
* inputs that are constant on the points or repeat an earlier input are never read.

Why this loses nothing for the MINIMUM size (full Lean model: 0/1/2-input gates, any wire index, missing wires read
false). Take any circuit. Process gates in order and keep for each wire a representative: a constant, or an earlier
wire with the same column. A gate with fewer than two inputs, with a missing input, with equal inputs, with a constant
input, a NOT of a NOT, or any gate whose column is constant or repeats an earlier column is replaced by its
representative and deleted; unread gates are deleted. Nothing is added, so the result is a normal circuit of at most
the same size computing the same outputs on the points, unless the target itself is constant or equal to an input (or,
with NOT, to a negated input): those cases are answered up front with 0 or 1 gates. Therefore

    minimum size in the full model  =  least s with a normal circuit of exactly s gates.

Caution: "no normal circuit with EXACTLY s gates" is what one `-s S` run proves. "No circuit with at most S gates"
needs every size below S too: use `--upto` / `--min`, or rely on a lower bound you already have (`--lb`).
(For kn7 at 15 the lower bound 15 is a checked theorem, so `-s 15` alone decides the unit.)
With several outputs of which one is constant on its points the normal model does not apply; cktsat stops and asks
for `--full-model`.

`--full-model` encodes the Lean semantics directly (operands range over FALSE, TRUE and all earlier wires, no
ordering, no "is read", no distinctness). The self-test compares it with the normal model and with brute force.

## Point reduction

* Points no output cares about are dropped; points with identical inputs are merged.
* Bases `ao`, `ao2`: every wire is a monotone function, so a cared true point that lies above another cared true
  point is implied by it, and a cared false point below another cared false point likewise. Only the minimal true
  and maximal false points of each output are kept. This is exact (a monotone circuit is right on the kept points iff
  it is right on all cared points), and the normal model is then taken relative to the kept points.
  match3: 512 -> 21 points (6 perfect matchings, 15 maximal non-matchable graphs); cyc7 in basis ao: 128 -> 14.
  Found circuits are still verified on the original spec.

## Symmetry: canonical prefixes

Canonical gate order. Give gate `(op, a, b)` (a < b; NOT: a = -1) the key `(b, a, op)`, AND < OR. Every circuit has
exactly one ordering of its gates in which the keys are strictly increasing (greedy: always place the available gate
with the least key; a gate that becomes available later reads the newest wire and so has a larger key). The CNF
demands this order, so gate permutations are gone.

Group. `G` = all permutations of the input wires that map the set of cared points to itself and preserve targets and
care masks (several outputs: up to a permutation of the outputs). Found by backtracking with a multiset-hash
refinement and an exact check at the leaves. kn_n: S_n; crown_n: 2 n!; cyc_n: dihedral 2n; match3: 72; mm2: 16.
Above `--gcap` (400000) elements a subset is used, which is still sound (less reduction).

Cubes. For h in G and a circuit C let h.C be C with inputs renamed and gates re-sorted. Order circuits
lexicographically by their key sequences. Claim: if C is the least member of its orbit, then its first d gates p,
taken as a circuit on their own, satisfy sort(h.p) >= p for every h. Proof: the first d gates of h.C are
lexicographically <= sort(h.p) (greedy placement over a superset of the gates), so sort(h.p) < p would give
h.C < C. Hence the prefixes p with "sort(h.p) >= p for all h in G" cover every orbit of solutions, and they are
exactly one representative per orbit of d-gate prefixes. They are generated level by level (the property is inherited
by shorter prefixes), which is also how a cube is split: its children are its canonical one-gate extensions.
Using a subset of G only weakens the filter, never the coverage.

A prefix is also dropped, natively, when (all necessary for a normal solution with exactly s gates)
* a gate column is constant or repeats an earlier wire, or equals the target before the last gate;
* too many wires still have to be read: unread prefix gates + unread essential inputs > remaining gates + 1, or more
  than (remaining gates) of them lie below the last prefix gate's larger operand (later gates read at most one wire
  there, because keys increase).
kn7 at s = 15: 2, 10, 76, 795, 11266, 202372 cubes at depth 1..6 (without the group: 42, 1176, 29330, 716625 at
depth 1..4).

Inside the CNF (`--symf`, on by default) the same least-member condition gives, for every involution h in G written
as disjoint swaps (a_1 b_1)...(a_m b_m) with a_t < b_t: "a gate reads b_t only if it or an earlier gate reads some
a_u" (otherwise h lowers the key of the first gate that touches a moved input and changes no earlier gate). For
S_n this says that inputs are first used in increasing order. It removes the symmetry that is left among inputs the
prefix does not touch. It is a necessary condition of the same least member that the cubes cover, so the two combine
soundly.

## Encoding (normal model)

Per gate i: one-hot `s1[i][.]` (smaller operand, or "none" for NOT), one-hot `s2[i][.]` (larger operand), type bit,
NOT bit (aon), value `v[i][p]` and operand values `A[i][p]`, `B[i][p]` per point. Clauses: operand channels, gate
semantics (plus the two type-independent implications), `s1 < s2`, strictly increasing keys, "is read", essential
inputs are read, non-constant, differs from every input column, pairwise different gate columns (`--alldiff`, aux
XOR witnesses), "no gate reads gate i together with an operand of gate i" (`--tri`), and in monotone bases
`v[i][p] <= v[i][q]` for cover pairs p < q of points (`--mono`). All of these are implied by the normal model.
Optional implied clauses, off by default, validated by the self-test:
* `--sens 1` reader sensitivity: (A) two cared points of one output that differ only in input j and have different
  targets: some gate that reads x_j has different values on them (otherwise every gate, and the output, would agree);
  (B) monotone bases: a cared true point p with x_j = 1 such that p without j lies below a cared false point: some
  reader of x_j is 1 at p. For kn_n with a single AND reader this is rule F6 of `src/knsat`.
* `--dep 1` structural support: dep[j][i] <-> gate i depends on x_j through its operands; a gate that does not
  depend on x_j has equal values on two points that differ only in x_j.
On medium-hard kn7 s = 15 cubes (4 cubes, 37.4 s with structural elimination only): `--sens 1` 23.8 s,
`--sens 1 --dep 1` 19.1 s, `--sens 1 --elim-sem 1` 12.9 s, all three 8.4 s. Alone and without elimination clauses
`--dep 1` showed no gain on kn6.
kn7, s = 15: 4483 variables, 54552 clauses (5218 / 63134 with the elimination clauses); match3 in basis ao, s = 13:
2868 variables, 36143 clauses (it would be 54540 / 514214 without the point reduction).

With `--cegar` the CNF is written grouped by point and the column constraints that speak about all points at once
(non-constant, distinct columns, monotone pairs) are left out of the SAT problem: on a subset of the points they
would not be implied. What remains is a relaxation, so UNSAT on the subset is UNSAT; a model is evaluated on all
points and one or two wrong points are added. The native prefix pruning still uses all points.

## Elimination clauses (`--elim`)

Put x_j = c in a correct circuit and simplify. What is left computes the cofactor spec (all cared points with
x_j = c), so it has at least L(f | x_j = c) gates: at most `E = s - L` gates can disappear. (the idea of `src/knsat/kn_elim.py`,
made generic.) cktsat adds, per input j and value c, status variables and a sequential counter "at most E":

* structural rule (always, also with `--cegar`): gone = every gate that reads x_j, and every gate that reads a gate
  that became constant; AND of a 0, OR of a 1 and NOT of a constant are constant again;
* `--elim-sem 1` (off by default; only when the SAT problem sees all cared points, so not after the monotone point
  reduction and not with `--cegar`): gone = every gate whose column on the points with x_j = c is constant or equals
  there the column of an earlier wire other than x_j. Replacing each such gate by that constant / wire leaves a
  normal circuit for the cofactor, so the count is again at most E. Contains the structural rule and also catches
  gates that become equal after the restriction. About 2x on the hard kn7 cubes (measured on a 227-cube sample).
  (A first version applied it on the reduced point set; the self-test caught that within one run: on a subset of
  the points "constant there" does not mean "constant on the cofactor".)
* `--elim-dead 1` (off by default, no gain measured): also counts kept gates that nothing needs any more.

Where L comes from: `--elim auto` runs cktsat itself (`--min`, recursively to `--elim-depth` 3, `--elim-time`
seconds per size) on the cofactor spec of one input per symmetry orbit. Cofactor specs are written in a canonical
form (inputs sorted by an invariant, ties resolved by trying all orders), so isomorphic cofactors share one entry
of the cache `runs/cktsat_elim/cache.json`. Every bound used is printed, stored in the log
(`meta.elim.cofactor_lower_bounds`) and has its own audit logs in `runs/cktsat_elim/`. A cofactor run that hits its
time limit still yields a proven bound (the sizes refuted so far). Trivial cofactors (constant, an input) give no
constraint. `--elim "*:0:13"` takes L from the command line instead (then the claim rests on your number).
An UNSAT obtained with `--elim` rests on the cofactor bounds; an UNSAT without it does not.

## Audit log

`runs/cktsat_<spec>_<s>_<basis>.json`: `meta` (spec, basis, s, model text, group order, encoding options, solver,
budgets, elimination bounds, summary with cube counts, CPU and wall time) and `cubes`: one entry
`[prefix, U | X | S, conflicts, cpu seconds, children]` per cube; `U` = UNSAT leaf, `X` = split into its canonical
one-gate extensions (which appear as later entries), `S` = SAT. (Conflict counts are those of the CaDiCaL pass;
pysat's Kissat reports none.) `.jsonl` next to it is the journal written while running; a line with `hdr: 2` marks
a `--resume` and records the clause options used from there on. `bin/cktsat ... --resume` on a finished run recomputes the root cubes and every split natively and checks
that all leaves are present: it audits coverage, not the solver answers.

## Validation

`bin/satpy src/cktsat/selftest.py --n N --seed S --max M` generates random tiny specs: truth tables on 3-4 inputs,
point lists with don't-cares, small graphs, and (half of the cases) specs with a non-trivial symmetry group (functions
of the Hamming weight, cyclically invariant functions, circulant graphs); 1-2 outputs; all three bases. For each spec
the minimum size (or "more than M") is computed eleven ways, which must agree:

1. brute force over Lean-exact gates, nothing pruned (constants, copies, missing wires; up to 4 gates),
2. brute force over normal gates on the ORIGINAL points (no point reduction, no symmetry, no ordering; up to M),
3. cktsat normal model with symmetry, 4. the same with `--no-sym`, 5. `--full-model`,
6. incremental CaDiCaL with a 50-conflict budget (forces splits), 7. Kissat path with a 15-conflict budget, depth-1
   roots and shuffled cubes, 8. `--elim auto` (structural), 9. `--elim auto --elim-sem 1 --elim-dead 1`,
10. `--dep 1` without `--alldiff`, 11. `--cegar` starting from 3 points.

A twelfth and thirteenth way were added later: `--sens 1`, and everything at once
(`--elim auto --elim-sem 1 --sens 1 --dep 1`); run with seed 5, 30 specs: 30/30 agree (1 gate 1x, 2: 6x, 3: 3x,
4: 4x, 5: 4x, more than 5: 12x).

Full run before that (seed 11, 60 specs, M = 5, 8 min 45 s on one core): 60/60 agree. Answers: 0 gates 1x, 1: 7x, 2: 14x,
3: 5x, 4: 6x, 5: 6x, more than 5: 20x, and one spec (constant-true target in basis ao2) where the normal model
refuses as documented and `--full-model` = brute force = 3. Earlier runs with other seeds: 70 + 12 + 8 + 8 + 6 + 6 + 5
+ 4 specs. Two real bugs were found this way and fixed: size-0 answers (target = an input) were missed by the SAT
path, and the first version of `--elim-sem` counted redundancy on the reduced point set (unsound; it is now only
used when all cared points are present, and is off by default).

Symmetric cases checked against `--no-sym` beyond the self-test: kn4 (ao and aon: 7), crown3 (ao 7, aon 6),
kn5 s = 9 (see Results). Known values reproduced: see Results.

## Limitations

* CNF size grows with points x gates x wires. Fine up to a few hundred points and about 20 gates; with `--cegar`
  more points are possible in basis aon. mm3 (262144 points) and cand32/cand128 are out of reach for exact synthesis.
* The UNSAT answers trust Kissat 4.0.4 / CaDiCaL 1.9.5 (no DRAT proofs: pysat's Kissat has no proof output).
  `--audit --recheck K` re-solves a sample of leaves with the other solver; it is a spot check, not a proof.
* `--solver auto` is deterministic per cube, and an UNSAT run has the same cube tree every time. With `-j > 1` the
  order in which results arrive, and so which witness is found first on a SAT instance, depends on timing.
  `--cegar` and the incremental solvers keep learnt clauses between cubes, so their cube trees can differ from run
  to run (the answers cannot).
* Hunting a witness is not what this tool is best at: it walks the cubes in canonical order (`--seed` shuffles).
  bin/cktsls found kn6 at 13, cyc7 at 10 and match3 at 14 in seconds. cktsat's value is the exhaustive side.
* `--elim-sem 1` needs all cared points in the SAT problem, so it is skipped after the monotone point reduction
  (match3 in basis ao) and with `--cegar`; there only the structural elimination rule applies.
* With several outputs of which one is constant on its points, or a constant-true target in basis ao2, the normal
  model does not apply: use `--full-model`.
* Groups with more than 400000 elements are truncated (sound, less reduction). Enumeration of the root cubes is fast
  up to kn8 (0.25 s at depth 4); beyond that the lex-min test over the whole group would need a restriction to the
  inputs the prefix touches.
* Machine: every number below was measured while other agents kept the load average between 20 and 90, and cktsat
  had 3-4 slots, mostly as separate 1-slot jobs because a request for several slots at once starved behind the
  1-slot jobs of others. `-j` scaling beyond 3 was never measured.

## Results

(partial; updated as runs finish. All runs on the M5 Max while it was heavily loaded by other agents, load average
30-90, so CPU and wall times are pessimistic. cktsat was limited to 3 slots, mostly as three 1-slot jobs.)

### 1. kn6, basis ao, s = 12: UNSAT, WITHOUT any elimination clauses  (K(6) = 13 does not rest on the elimination argument)

cktsat's own encoder, normal model, cubes = the 777 canonical 4-gate prefixes (one per orbit under S_6) plus the
first-use clauses; `--solver auto` (Kissat 4.0.4 on the hard cubes); three shards of the root cubes, one worker each:

| shard | result | cubes | UNSAT leaves | splits | CPU s | wall s | log |
|---|---|---|---|---|---|---|---|
| 0/3 | UNSAT | 612 | 598 | 14 | 1003 | 1062 | runs/cktsat_kn6_12_ao_shard0of3.json |
| 1/3 | UNSAT | 526 | 515 | 11 | 893 | 969 | runs/cktsat_kn6_12_ao_shard1of3.json |
| 2/3 | UNSAT | 513 | 502 | 11 | 855 | 924 | runs/cktsat_kn6_12_ao_shard2of3.json |

**All 777 root cubes are refuted: 1651 cubes (1615 UNSAT leaves, 36 splits), 2751 CPU-s in total; each shard took
15-18 min on one core (the third had to wait 20 min for a free slot).** With the checked theorem K(6) >= 12 this gives K(6) = 13 and
crown6 = 19 (13-gate witness: found/kn6_13_ao_cktsat.ckt, cktcheck OK).
`bin/cktsat specs/kn6.spec --basis ao -s 12 --shard i/3 --audit --recheck 12` re-derives the cube tree of a shard and
solves 12 random leaves again with CaDiCaL 1.9.5: AUDIT OK for all three shards.
(the specialised `src/knsat` run with elimination clauses: 67 CPU-s. Without them: 2751 CPU-s here, on a machine with
load average 30-90.)

### 2. kn6 with cktsat's own elimination clauses: K(6) = 13 in 2 min 5 s on one core

`bin/cktsat specs/kn6.spec --basis ao --min --elim auto` (cofactor bounds computed by cktsat itself, recursively:
kn6|x=0 = kn5 needs 10, kn5|x=0 = kn4 needs 7, ...; kn_n|x=1 = OR of n-1 inputs):

| s | result | cubes | CPU s | wall s (-j 1) | log |
|---|---|---|---|---|---|
| 1..9 | UNSAT | - | 0 | 0 | a cofactor bound (kn5 needs 10 gates) already exceeds s - 1 |
| 10 | UNSAT | 777 | 0.0 | 0.1 | runs/cktsat_kn6_10_ao_elim.json |
| 11 | UNSAT | 777 | 0.9 | 1.4 | runs/cktsat_kn6_11_ao_elim.json |
| 12 | UNSAT | 777 | 109 | 118 | runs/cktsat_kn6_12_ao_elim.json |
| 13 | SAT | 40 | 0.3 | 0.4 | found/kn6_13_ao_cktsat.ckt (cktcheck OK) |

Elimination is worth 24x at kn6 s = 12 (109 against 2751 CPU-s).

### 3. kn7, basis ao, s = 15: UNSAT with cktsat's own encoder and its own elimination clauses  (agrees with the `src/knsat` runner: K(7) = 16)

Bounds from `--elim auto`, printed by every run: kn7|x_j=0 = kn6 needs 13 gates (cktsat: s = 12 UNSAT without
elimination in 1, with elimination in 2; s <= 11 with elimination in 2), kn7|x_j=1 = OR of 6 inputs needs 5. So at
s = 15 at most 2 gates may be redundant under x_j = 0. That single elimination step with L = 13 is the only
ingredient besides the normal model and the SAT answers.

| s | scope | result | cubes | UNSAT leaves | splits | CPU s | log |
|---|---|---|---|---|---|---|---|
| 14 | all 795 roots (depth 4) | UNSAT | 795 | 795 | 0 | 6.8 | runs/cktsat_kn7_14_ao.json |
| 15 | shard 0/4 (2817 roots, depth 5) | UNSAT | 2851 | 2850 | 1 | 1964 | runs/cktsat_kn7_15_ao_shard0of4.json |
| 15 | shard 1/4 (2817 roots) | UNSAT | 2846 | 2845 | 1 | 2180 | runs/cktsat_kn7_15_ao_shard1of4.json |
| 15 | shard 2/4 (2816 roots) | UNSAT | 2839 | 2838 | 1 | 2104 | runs/cktsat_kn7_15_ao_shard2of4.json |
| 15 | shard 3/4 (2816 roots) | UNSAT | 2870 | 2868 | 2 | 2212 | runs/cktsat_kn7_15_ao_shard3of4.json |
| 15 | **all 11266 roots** | **UNSAT** | 11406 | 11401 | 5 | 8460 (2.35 CPU-hours) | |

Wall time 39 minutes (04:37 to 05:16) as four 1-slot jobs. The specialised `src/knsat` runner: 475 cubes, 4.9 CPU-hours, UNSAT.
`bin/cktsat specs/kn7.spec --basis ao -s 15 --elim auto --elim-sem 1 --sens 1 --dep 1 --depth 5 --shard i/4 --audit
--recheck 10`: AUDIT OK for all four shards (cube tree recomputed, every leaf recorded UNSAT, 10 random leaves per
shard solved again with CaDiCaL 1.9.5).

History of the run, for the record. The shards were started with the structural elimination rule only. 8200 of the
11266 root cubes fell within 2 minutes, but the hard ones (prefixes made of ORs) did not finish within the budget
of 3M conflicts (about 280 s each) and were being split (those are the 5 splits). After 9 minutes the shards were
stopped and resumed (`--resume`, same journals, marker line `hdr 2` at the switch) with
`--elim-sem 1 --sens 1 --dep 1`, which are implied clauses too (see Encoding and Elimination; both were in the
self-test before the leaves they produced were trusted: 30/30). The hard cubes then took 20-200 s. Both phases
refute cubes of the same cube tree, so the journals stay valid.

Estimate for kn7 s = 15 WITHOUT elimination clauses: elimination is worth 5x at kn5 s = 9 (7.4 against 1.4 CPU-s)
and 24x at kn6 s = 12 (2751 against 109 CPU-s, structural rule), and with the structural rule alone kn7 was heading
for well over 5 CPU-hours. So the plain run is at least 100 CPU-hours and more likely several hundred: above the
40 CPU-hour limit, NOT queued.

### 4. match3, basis ao, s = 13: UNSAT (with `--elim auto --sens 1 --dep 1`), so the monotone minimum is 14

`bin/cktsat specs/match3.spec --basis ao -s 13 --elim auto --sens 1 --dep 1 --elim-time 900`, one core, 17 minutes
in all, nearly all of it in the cofactor runs. Cofactor bounds found by the recursion (59 cached cofactor specs with
3 to 8 inputs, each with its own audit logs in runs/cktsat_elim/; by symmetry one input stands for all nine):

* match3 | x_e = 0 needs exactly 9 gates (s = 8 UNSAT, 9 SAT);
* match3 | x_e = 1 needs at least 12 gates (s <= 10 excluded by its own cofactor bounds, one of which is an exact 10;
  s = 11 UNSAT; s = 12 hit the 900 s limit with 413 cubes refuted and 311 open, so 12 is a lower bound only).

With these, at s = 13 fixing an input to 1 may remove at most one gate, and all 2482 root cubes are refuted by unit
propagation alone (0 conflicts, 2 CPU-s; log runs/cktsat_match3_13_ao_elim.json). The reason can be read off:
every input then feeds exactly one gate, an AND (an OR reader would become constant 1 and take its own reader with
it). The first gate reads two inputs a, b and is the only reader of a; take a perfect matching through a that
avoids b: the circuit is 1 there and 0 without a, so that AND would have to be 1 there, but b is 0.
Sizes up to 12 are excluded by the same bound (match3 needs at least one gate more than match3 | x_e = 1).
So match3 has no monotone circuit with at most 13 gates; with the 14-gate circuit found/match3_14_ao.ckt (from
cktsls) the monotone minimum is exactly 14. This answer RESTS ON the cofactor bound "match3 | x_e = 1 needs >= 12".
Not cross-checked without elimination: the plain s = 13 instance is far too hard (none of 5 sampled depth-3 cubes
fell within 200000 conflicts).

Running: the same at s = 14 (must be SAT with the same clauses: a check that they do not over-constrain), the
cofactor at s = 12 to the end, and match3 in basis aon at s = 13 (`--cegar --elim auto`).

### Known values reproduced (`--min`: UNSAT proved for every smaller size from 1 unless a `--lb` is noted)

| spec | basis | minimum | expected | notes |
|---|---|---|---|---|
| kn3 | ao | 4 | K(3) = 4 | |
| kn4 | ao | 7 | K(4) = 7 | same with `--no-sym`; brute force also gives 7 |
| kn4 | aon | 7 | | NOT does not help; same with `--no-sym` |
| kn5 | ao | 10 | K(5) = 10 | whole `--min` run 26 s on one core; with `--elim auto --elim-sem 1` 3.9 s |
| kn6 | ao | 13 | K(6) = 13 | see 1 and 2 above |
| crown3 | ao | 7 | 3 + K(3) = 7 | same with `--no-sym` |
| crown3 | aon | 6 | | one gate fewer with NOT; same with `--no-sym` |
| crown4 | ao | >= 11 | 4 + K(4) = 11 | `--lb 9`: s = 9 UNSAT (986 cubes, 102 CPU-s), s = 10 UNSAT (1003 cubes, 406 CPU-s, stopped once and resumed). The s = 11 witness hunt was stopped after 11 min on one core (482 cubes refuted, 913 open, no witness yet; journal kept) to give the slot to more useful runs |
| cyc5 | aon | 7 | n + ceil(n/2) - 1 = 7 | s = 6 UNSAT, 876 cubes |
| cyc6 | aon | 8 | 8 | `--cegar --lb 7`: s = 7 UNSAT 2048 cubes 1.2 CPU-s, s = 8 SAT 21 CPU-s |
| cyc7 | aon | >= 10 | 10 | `--cegar -s 9`: UNSAT, 4164 cubes, 658 CPU-s (runs/cktsat_cyc7_9_aon.json); 10-gate witness: found/cyc7_10_aon.ckt (cktsls). cktsat's own s = 10 hunt was stopped after 4 min (121 of 4172 cubes, no witness yet) |

kn5 s = 9 UNSAT, the Python baseline of 99 s (single thread): cktsat 680 cubes, 7.6 s wall at -j 1 and 2.9 s at -j 3
(first measurement, before the first-use clauses; 10.4 s at -j 1 later on the loaded machine); with
`--elim auto --elim-sem 1 --sens 1 --dep 1` 0.48 CPU-s. -j 6 was not measured: cktsat never had more than 4 slots,
and for most of the session three or four 1-slot jobs.
