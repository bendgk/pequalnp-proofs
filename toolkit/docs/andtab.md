# andtab — exact AND-complexity of bipartite graphs (OR gates free)

Built for the analytic track (barrier audit, section 8, "the AND-count currency"): nobody had exact values of `And`.
Tools: `bin/andtab` (native, all graphs of a size at once), `src/andtab/andsat.py` (SAT, one graph),
`src/andtab/ladder.py`, `src/andtab/structured.py`. Tables: `tables/and_3.json`, `and_4.json`, `and_5.json`,
`and_structured.json`. What is exact and what is only bounded is said explicitly in section 0 and again per entry.

## 0. Results at a glance

**All graphs up to 5x5 — every entry is exact** (`"exact": true` for all 26 + 192 + 3014 classes; a circuit with
`And` AND gates is stored and `And - 1` is refuted exhaustively; two independent methods agree, section 7).

| size | classes | And = 0 | 1 | 2 | 3 | maximum | classes at the maximum | mean over labelled graphs |
|------|---------|---------|-----|------|------|---|------|--------|
| 3x3  | 26      | 7       | 13  | 6    | -    | 2 | 6    | 1.2070 |
| 4x4  | 192     | 11      | 55  | 119  | 7    | 3 | 7    | 1.9124 |
| 5x5  | 3014    | 16      | 174 | 1774 | 1050 | 3 | 1050 | 2.4924 |

Labelled graphs: 3x3 `0:50 1:306 2:156`; 4x4 `0:226 1:8550 2:53496 3:3264`; 5x5 `0:962 1:194850 2:16640700 3:16717920`.
**No graph on 5 + 5 vertices needs four AND gates.** (For comparison the same classes need up to 7 / 11 / >= 12
gates in total, `tables/star_*.json`.)

Extremal classes (class id, rows; same ids as `tables/star_N.json`):
* 3x3, And = 2: `5 [3,1,0]`, `9 [5,3,0]`, `14 [4,2,1]` (perfect matching), `15 [5,2,1]`, `17 [6,3,1]`, `22 [6,5,3]` (crown).
* 4x4, And = 3: `55 [9,5,3,0]`, `106 [12,7,2,1]`, `107 [13,7,2,1]`, `138 [12,10,6,1]`, `139 [13,10,6,1]`,
  `142 [13,11,6,1]`, `166 [14,9,5,3]`. All seven have cover number `cov0 = 4` (so the cover bound gives only 2).
  The 4x4 crown, matching, greater-than, inner product and intersecting graphs all have And = 2.
* 5x5, And = 3: 1050 classes, listed in `tables/and_5.json` (`summary.extremal` has the first 60; filter
  `classes[*].and.size == 3` for all).

Relation to the cover number `cov0` = least number of all-zero rectangles covering the zeros (= Boolean rank of the
complement). Lemma 4: `ceil(log2 cov0) <= And <= cov0 - 1`. Joint counts of classes `(And, cov0)`:
3x3 `(0,<=1):7 (1,2):13 (2,3):6`; 4x4 `(0,<=1):11 (1,2):55 (2,3):94 (2,4):25 (3,4):7`;
5x5 `(0,<=1):16 (1,2):174 (2,3):947 (2,4):827 (3,4):694 (3,5):356`.
So And = ceil(log2 cov0) for 26/26, 185/192 and 2320/3014 classes; it is one more for the rest.
`|And(G) - And(complement of G)|` is 0 or 1 at every size (3x3 `0:8 1:5` pairs, 4x4 `0:81 1:23`, 5x5 `0:1359 1:148`).

**Structured graphs:** section 6 (table with exact / bounded status and how every bound was proved).
**Encoder wires:** giving the row and column bit-sets as free inputs changes nothing (section 6.4).

## 1. Definition and conventions

`And(A)` = the least number of AND gates of a circuit of AND and OR gates of fan-in at most two (Lean: `Monotone2`)
that represents the `n x m` bipartite graph `A` (`PEqualNP.Represents.Represents`: right on the `n*m` inputs
`oneEach u v`), with any number of OR gates. Same input wires (`0..n-1` rows = left vertices, `n..n+m-1` columns =
right vertices) and same points as the `mono` column of `tables/star_*.json`.

On the points a wire is a set of cells of the `n x m` grid (cell `(u,v)` = bit `u*m+v`): input `u` = full row `u`,
input `n+v` = full column `v`, OR = union, AND = intersection, a wire that does not exist = empty set, target =
the cell set of `A`.

**Normal form (this is what every tool here searches).** A circuit with `a` AND gates is `2a+1` subsets:
AND gate `j` computes `(OR of L_j) AND (OR of R_j)` with `L_j, R_j` subsets of the generators
`{n+m inputs} + {AND gates 0..j-1}`; the output is the OR of a subset `Out` of all generators.
Generator index: `0..n-1` rows, `n..n+m-1` columns, `n+m+k` = AND gate `k`.

Conventions: empty OR = empty set. Empty graph: And = 0 (`Out` empty; in a `.ckt` the output names a wire that does
not exist). A union of full rows and columns: And = 0. Complete graph: And = 0 (union of all rows; the star tables
count 1 there, for the constant gate). Only AND gates with two inputs are needed (Lemma 1), so "number of AND
gates" and "number of two-input AND gates" have the same minimum.

**Lemma 1 (normal form loses nothing).** If a `Monotone2` circuit with `a` two-input AND gates represents `A`, then
a normal-form circuit with at most `a` AND gates does, and conversely a normal-form circuit with `a` AND gates
expands into a `Monotone2` circuit with exactly `a` AND gates (all of them two-input) and OR gates of fan-in two.
*Proof.* Give every wire `w` a set `S(w)` of generators whose union is the cell set of `w`: an input: `{w}`; a
missing wire and `OR[]`: empty; `OR[x]`, `AND[x]`: `S(x)`; `OR[x,y]`: `S(x) + S(y)`; `AND[]` (constant true): all
rows; a two-input `AND[x,y]`: it becomes the next AND gate of the normal form with `L = S(x)`, `R = S(y)` (a
forward reference is a missing wire) and `S(w) = {that gate}`. `Out = S(output wire)`. Induction over the gate
list. The converse is an OR chain per subset. ∎

## 2. Lemmas

Write `cl(G)` for the set of all unions of subsets of a family `G` of cell sets (the empty union included),
`L0 = cl(rows, columns)` (level 0; `(2^n - 1)(2^m - 1) + 1` sets; the complement of a level-0 set is a rectangle
`R x C`) and `C_j = cl(rows, columns, g_1..g_j)`.

**Lemma 2 (levels).** `And(T) <= a` iff there are cell sets `g_1..g_a` with `g_j = X_j ∩ Y_j`, `X_j, Y_j` in
`C_{j-1}`, and `T` in `C_a`. Only the cell sets matter, and a `g_j` already in `C_{j-1}` is useless.

**Lemma 3 (last step).** Let `C = cl(G)`. `T` is in `cl(G + {X ∩ Y})` for some `X, Y` in `C` **iff**
`T = X' ∩ Y'` for some `X', Y'` in `C`. *Proof.* If `T = U ∪ (X ∩ Y)` with `U` in `C` then
`T = (U ∪ X) ∩ (U ∪ Y)`; if `T = U` then `T = T ∩ T`. The converse is trivial. ∎
So `And(T) <= a` iff some `g_1..g_{a-1}` make `T` an intersection of two members of `C_{a-1}`. This is the
last-level test that avoids enumerating `2^|closure|` unions: it is a pass over pairs of closure members, and the
last AND gate can always be taken to be the output itself.

**Lemma 4 (cover bound).** If `T` has a circuit with `a` AND gates then the zeros of `T` are covered by at most
`2^a` all-zero rectangles. Hence `ceil(log2 cov0(T)) <= And(T) <= max(cov0(T) - 1, 0)`.
*Proof.* `a = 0`: `T = rows(R) ∪ cols(C)`, its zeros are the rectangle `R^c x C^c`. Step: let `g_1 = X ∩ Y`,
`X, Y` in `L0`. Replace generator `g_1` everywhere by the generators of `L_1` (resp. `R_1`): two circuits with
`a - 1` AND gates computing `T_X`, `T_Y`. A circuit is evaluated cell by cell and is monotone: at a cell where `X`
and `Y` agree all three circuits agree; at a cell in `X \ Y` gate 1 is off, as in the `Y`-circuit, so
`T_Y = T` there and `T_X >= T`; symmetrically on `Y \ X`. So `T = T_X ∩ T_Y`, the zeros of `T` are the zeros of
`T_X` plus those of `T_Y`, and induction applies (`T <= T_X`, so a zero rectangle of `T_X` is one of `T`).
Upper bound: `T` is the intersection of the complements of the `cov0` rectangles, each of level 0. ∎
*Fooling sets.* Zero cells `(u_i, v_i)` with `T(u_i, v_j) = 1` or `T(u_j, v_i) = 1` for all `i != j` lie in
different all-zero rectangles, so `cov0 >=` their number `F` and `And >= ceil(log2 F)`.
*Crown.* The diagonal is a fooling set of size `n`; the bit-partition circuit has `ceil(log2 n)` AND gates. So
`And(crown_n) = ceil(log2 n)`: the regression test of this tool (section 6, also by SAT and by the tables).

**Lemma 5 (subgraphs, full rows, twins).** (a) `And` is monotone under induced subgraphs (delete the dropped rows
and columns from every `L_j`, `R_j`, `Out`: every wire becomes its restriction). (b) Deleting a full row or a full
column does not change `And` (put it back into `Out`). (c) Deleting one of two rows (columns) with the same
neighbourhood does not change `And` (put the twin into every set that contains the other). (d) An all-zero row can
NOT be deleted in general: rows `[1,3,0]` (3x2) has And = 1, rows `[1,3]` has And = 0. The *core* of a graph is
what is left after (b) and (c); `andsat.py` works on the core and lifts the witness back.

**Type bound.** `And(T) <=` the number of distinct row types that are neither empty nor full, and the same for
columns (one AND per type: `(OR of the rows of that type) AND (OR of its columns)`). In the other direction, rows
with the same membership pattern in all `L_j`, `R_j`, `Out` are twins, and with `L_j ∩ R_j = ∅` (Lemma 9, M2) a
row that is not full has `3^a` patterns: the number of distinct non-full row types is at most `3^a`.

**Lemma 6 (the three reductions of the native search lose no class).** At a node the prefix is `g_1..g_d`, the
closure `C = C_d`, a *candidate* is `g = X ∩ Y` not in `C` with `X, Y` in `C`.
* *Symmetry.* `Gamma` = row permutations x column permutations (x transpose if `n = m`) acts on cells and permutes
  the inputs, so it maps circuits to circuits. `H` = the elements fixing every `g_i` of the prefix maps `C` to
  itself and the subtree below `(prefix, g)` onto the subtree below `(prefix, h g)`. Marks are per `Gamma`-class, so
  one candidate per `H`-orbit is enough (the program keeps the numerically least).
* *Dominance.* If `g' ⊊ g` are candidates and `g = g' ∪ U` with `U` in `C`, then `cl(C + g') ⊇ cl(C + g)`: every
  continuation after `g` is a continuation after `g'` (a later generator that is already in the bigger closure is
  simply superfluous). So `g` is dropped; the minimal candidates stay. Test: with `U_g` = union of the generators
  inside `g` (the largest member of `C` inside `g`), `g'` dominates `g` iff `g \ U_g ⊆ g' ⊊ g`.
* *Order (only at depth 2).* At node `(g_1)` a candidate `g_2` that was already a candidate at the root is skipped
  if the class representative of `g_2` is numerically smaller than `g_1` (`g_1` is the least of its class).
*Proof of completeness.* Claim: for every valid sequence `g_1..g_d` there are an enumerated node of depth
`d' <= d` with closure `C'` and `γ` in `Gamma` with `C' ⊇ γ(C_d)`. Induction on `d`: `γ(g_{d+1})` is in `C'`
(same node) or a candidate there; a minimal candidate `g*` dominating it has an `H`-orbit representative `h g*`
that is expanded unless the order rule skips it, and the child's closure contains `h γ(C_{d+1})`. If the order
rule skips `c = h g*` at node `(r)`: both `c` and `r` are root candidates, so `(c, r)` is a valid sequence with
the same closure; redo the step from the root: `c` is dominated by a minimal root candidate `c*`, and
`rep(c*) <= rep(c) < r` because a subset has a smaller value in every labelling. So the new root node has a
strictly smaller representative, and the descent ends. Now let `And(T) = a` with `T = X ∩ Y`, `X, Y` in
`C_{a-1}`: the node from the claim has depth exactly `a - 1` (a smaller depth would give `And(T) < a`), and its
last step marks `γ(T)`; pairs with both operands in the parent's closure can be skipped for the same reason. ∎
All three switches can be turned off (`--nosym --nodom --noorder`); the tables are identical (section 7).

**Lemma 7 (inner product).** An all-zero rectangle `A x B` of `IP_k` (`<u,v> = 0` on it) has `span(A)` orthogonal
to `span(B)`, so `|A||B| <= 2^k`. `IP_k` has `2^(2k-1) + 2^(k-1)` zeros, so `cov0 >= 2^(k-1) + 1` and
`And(IP_k) >= k`.

**Lemma 8 (restriction identity; encoding F).** Replace every AND gate `j` by one of its two ORs, side `s_j` in
`{L, R}`. The circuit `C_s` has no AND gate left and computes a level-0 set `W_s`. Then `T = ∩_s W_s` over all
`2^a` choices (apply the step of Lemma 4 to gate 1, then to gate 2 of both circuits, and so on). Whether input `i`
belongs to gate `j` of `C_s` depends only on `s_0..s_j` and on the membership bits, and
`T(u,v) = AND_s ( u in W_s or v in W_s )`: an exact description of the circuit with no cell variables at all.

**Lemma 9 (side conditions used in the SAT encodings; valid for a MINIMUM circuit only).**
M1 every AND gate is read by a later AND gate or the output (else delete it). M2 `L_j ∩ R_j = ∅`: if `i` is in
both, `g_j = val(i) ∪ g'` with `g' = (OR of L_j - i) ∩ (OR of R_j - i)`; replace gate `j` by `g'` and every use of
`g_j` by `{g', i}`, gate by gate in increasing order; the number of AND gates is unchanged. M3 the least index of
`L_j ∪ R_j` is in `L_j`. M4 if gate `j+1` does not read gate `j` then `L_j >= L_{j+1}` lexicographically on the
common indices. M5 for every automorphism `φ` of the graph (acting on the input indices) the string
`(L_0, R_0, L_1, R_1, ...)` is lexicographically at least its image. M6 (encodings B, F, where the last gate is
the output, Lemma 3; M2 is then not imposed on the last gate) the last gate reads on both sides every generator
lying inside `T`.
*Why they hold together.* The circuits that are minimum and satisfy M1, M2 (and M6) form a non-empty set that is
closed under: swapping `L_j` and `R_j`, exchanging two adjacent gates that do not read each other, and applying an
automorphism of the graph. Take the member whose string `(L_0, R_0, L_1, ...)` is lexicographically largest: a
violation of M3, M4 or M5 would give a member with a larger string. Because they are only valid for a minimum
circuit, a refutation of `a` counts only when every smaller `a` is refuted or excluded by a proved bound; the
`--no-sym` switch drops M1-M6 and gives the pure normal form.

## 3. Method of `bin/andtab` (all classes of a size at once)

`reach[T]` for all `2^(nm)` cell sets, classes under `Gamma` exactly as in `startab` (representative = least value
of `sum_u rows[u] * 2^(m*u)`, ids in increasing order of the representative; `mktable.py` asserts that ids, rows,
orbit sizes and complement ids equal those of `tables/star_N.json`).

Pass `a = 1, 2, ...`: depth-first over prefixes `g_1..g_{a-1}` (candidates = pairwise intersections of the
closure, reduced as in Lemma 6; the closure is kept as a list plus a bitmap and grows by `x ∪ g`), and at depth
`a - 1` the last step of Lemma 3: every pair `X, Y` of closure members with at least one containing the newest
generator, one AND and one bit test per pair. A hit marks the whole class and stores a witness (subsets `L_j`,
`R_j`, `Out` as generator-index masks, transported to the class representative and re-evaluated). After pass `a`
every set with `And <= a` is marked, so a class first marked in pass `a` has `And = a` exactly. A class not reached
by the last complete pass would get the row-type circuit as an upper bound and `"exact": false` — this does not
occur up to 5x5.

Measured (one thread, M5 Max, machine loaded):

| size | time | level 2 | level 3 | pair tests / s |
|------|------|---------|---------|----------------|
| 3x3  | 0.00 s | 8 nodes, 7 of 306 candidates kept | - | 1e8 |
| 4x4  | 0.01 s | 20 nodes, 19 of 8550 root candidates kept | 87 nodes, 8 last-step prefixes (stops when every class is reached) | 1.9e8 |
| 5x5  | 5.9 s (1.4 s of it building the class table) | 72 nodes, 71 of 194850 root candidates kept, 0.74 s | 20189 nodes, 14802 last-step prefixes, 3.48e9 pair tests in 3.7 s | 9.5e8 |

With `--nodom` the 5x5 run takes 23 s (156347 prefixes, 2.2e10 pair tests, 1.06e9/s) and gives the same table.
Level 2 is complete at every size; level 3 at 4x4 and 5x5 ends as soon as every class is reached (nothing is left
to refute, because nothing needs 4).

## 4. Tables

`tables/and_N.json` (N = 3, 4, 5):

    { "n", "m", "quantity", "conventions", "witness_format", "inputs", "symmetry", "group_order", "rows_convention",
      "num_classes", "last_complete_level", "exactness", "extra_fields", "run": {header of the andtab run},
      "summary": { "and_hist_classes", "and_hist_labelled", "mean_and_labelled", "max", "num_extremal", "extremal",
                   "joint_and_vs_star_mono_classes", "and_minus_lb_cov_hist_classes",
                   "star_witness_ands_minus_and_hist_classes", "min_types_minus_and_hist_classes", "complement_gap" },
      "classes": [ { "id", "rows", "orbit_size", "complement",          <- identical to tables/star_N.json
                     "and": { "size", "exact", "lower", "witness": {"L": [[..]], "R": [[..]], "out": [..]},
                              "ckt": ".ckt text", "ckt_gates", "ckt_ands" },
                     "star_mono", "star_mono_lower", "star_mono_ands", "cov0", "lb_cov", "row_types", "col_types" } ] }

* `and.size` = And, `and.exact` true for every class of the three tables.
* `witness`: generator indices as in section 1; `ckt` is the same circuit expanded (OR chains of fan-in two, shared
  prefixes) and passes `bin/cktcheck SPEC CKT --basis ao`; `ckt_ands` = number of `and` lines = And; `ckt_gates` =
  all gates of that expansion (not minimised: only the AND count means something).
* `star_mono` = exact total gate count from the star table (null where that table is not exact: then
  `star_mono_lower`); `star_mono_ands` = AND gates in the star table's witness, an upper bound on And
  (it equals And for 16/25, 149/191 and 1954/3013 classes; the largest excess is 1, 2 and 2).
* `cov0`, `lb_cov = ceil(log2 cov0)`, `row_types`, `col_types`: the bounds of section 2.

Look up any labelled graph: canonicalise with `src/startab/lookup.py` (`canon`), the ids are the same.

## 5. `andsat.py`: one graph by SAT (independent of the native tool)

Iterative deepening over `a`; UNSAT at every `a < A` and SAT at `A` proves `And = A`. Three encodings:
* **A**: selectors `L_j, R_j, Out`, cell values of every gate, output = OR of the selected gates; M1-M5.
* **B** (default): the last gate is the output and equals the graph (Lemma 3), its cell values are constants;
  M1-M6.
* **F**: Lemma 8, no cell variables: per input `i`, gate `j` and side prefix `s_0..s_j` one value variable;
  one binary clause per (one-cell, `s`), one clause per zero-cell.
Automorphisms for M5 are found by a small backtracking search (`--autos K` of each kind, transposing ones
included). Timeouts are conflict budgets checked against wall time (CaDiCaL 1.9.5 through python-sat), so a run is
deterministic except for where a time limit falls.
`ladder.py` applies it to the corners `G_k` of a big graph (Lemma 5a): the bound proved on a small corner is a
bound for the whole graph, and small corners refute much faster than the full graph.

## 6. Structured graphs

Graphs on `n + n` vertices, indices `u, v` in `0..n-1` read as bit-sets: `crown` `u != v`; `match` `u = v`;
`ip` popcount(`u & v`) odd; `disj` `u & v = 0`; `inter` `u & v != 0`; `gt` `u > v`; `randS` = Python
`random.Random(1000*n + S).getrandbits(n)` per row (density 1/2, S = 1, 2, 3). File: `tables/and_structured.json`
(per graph: `rows` hex, `lower`, `lower_how`, `proofs`, `upper`, `upper_how`, `exact`, `witness`, `ckt`).

### 6.1 Table

PRELIMINARY (state of `tables/and_structured.json` while the corner ladders and the n = 32 runs wait for a core
slot; this block is replaced when they finish):

| graph | n = 4 | n = 8 | n = 16 |
|---|---|---|---|
| crown | **2** | **3** | **4** |
| match | **2** | **4** | 4..5 |
| ip | **2** | 4..5 | 4..10 |
| disj | **1** | **2** | **3** |
| inter | **2** | **3** | **4** |
| gt | **2** | **4** | 4..5 |
| rand1 | **1** | **4** | 4..8 |
| rand2 | **2** | **4** | pending |
| rand3 | **2** | **4** | pending |

A bold number is exact (proved lower bound = number of AND gates of a checked circuit). `a..b` means: `And >= a`
is proved, a circuit with `b` AND gates is stored, nothing in between is decided.

### 6.2 How each bound was proved

Lower bounds (each entry names its proof in `lower_how`; all proofs found are in `proofs`):
* `cov`: `ceil(log2 F)` from a 0-fooling set of size `F` (stored in `fooling0_set`, re-checked) or from the exact
  cover number of the zeros (SAT, `cov0`), Lemma 4; for `ip` also the area bound of Lemma 7.
* `sat`: every `a` below the bound refuted by exhaustive SAT on the graph itself, deepening from a proved bound
  (encoding B with M1-M6).
* `sub`: the half-size graph of the family is the top-left corner (asserted) and And is monotone (Lemma 5a).
* `sub+sat`: the same on a smaller corner found by `ladder.py`: the certificate (`lower_certificate`) names the
  corner (its rows) and the SAT steps.
Upper bounds are always circuits (re-evaluated, `.ckt` accepted by `bin/cktcheck --basis ao`): a SAT model, an
explicit construction (`andsat.construct`), or the doubling of the half-size circuit (`andsat.double_wit`).

Explicit constructions (number of AND gates for `n = 2^k`):
* crown: `k` — `OR_i ((u_i=0 or v_i=0) AND (u_i=1 or v_i=1))`; optimal by the fooling set (Lemma 4).
* inter: `k` — `OR_i (u_i AND v_i)`; optimal: the `n` zero cells `(S, complement of S)` are a fooling set.
* disj: `k - 1` — a chain of ANDs of the free ORs `(u_i=0 or v_i=0)`; proved optimal for `k <= 4` by SAT (the cover
  bound only gives `ceil(log2 k)`).
* match, gt: doubling adds 2 AND gates per index bit (`[u_top = v_top] AND old`, resp.
  `(u_top > v_top) OR ((u_top >= v_top) AND old)`); the exact values at 8 (both 4) are below `2k - 1 = 5`.
* ip: `5k - 6` by the parity recursion with both polarities; the exact value at 8 is 5, not 9.

STRUCTURED_NOTES

### 6.3 Corner sequences

`ladder.py` gives And of every corner `G_k` (first `k` indices) of a graph; the values are in
`tables/and_structured.json` under `corner_sequences`.

STRUCTURED_SEQ

### 6.4 Free encoder wires change nothing (request 3)

The wires `{u : bit_i(u) = b}` and `{v : bit_i(v) = b}` are unions of rows / columns, so they are already in the
level-0 closure and every circuit using them becomes a circuit without them with the same AND gates (replace the
wire by its rows / columns inside every `L_j`, `R_j`, `Out`). Confirmed three ways:
* `bin/andtab --n 4 --enc` and `--n 5 --enc`: generators 8 -> 16 (resp. 10 -> 22), level-0 closure 226 vs 226
  (962 vs 962) sets, IDENTICAL; cost tables byte-identical to the plain runs.
* SAT with the encoder wires as real extra free inputs (`andsat.py ... --enc`, 16 inputs instead of 8): all 192
  classes of the 4x4 table come out with the same And (0 mismatches).
* The same at 8x8 (28 inputs instead of 16): crown 3 (a = 2 UNSAT), gt 4 (a = 3 UNSAT), match 4 (a = 3 UNSAT),
  rand1 4 (a = 3 UNSAT) — the values without the extra wires; the witness found with encoder wires is converted
  to a plain one by the substitution above and re-checked.

## 7. Cross-checks done

* Native tool with the reductions off: `--nosym`, `--nodom`, `--noorder` and all three together give byte-identical
  cost tables at 3x3 and 4x4; `--nodom` also at 5x5 (md5 of the `--costs` files).
* SAT, all classes, all three sizes: for every one of the 26 + 192 + 3014 classes `andsat.py table` re-proved the
  value from scratch: UNSAT for every `a < And`, SAT at `And`, witness re-evaluated. Done with encoding A (with
  M1-M4 and in the pure model `--no-sym --no-core`), with encoding B (M1-M6 and automorphisms) and with encoding F:
  0 mismatches each time (9886 SAT calls per pass at 5x5, 3.6 to 5.1 s).
* Every witness: evaluated in C++ (`evalWit`), again in Python (`andlib.eval_wit`), expanded to `.ckt` and accepted
  by `bin/cktcheck --basis ao`; the number of `and` lines equals And (26 + 192 + 3014 circuits).
* Sanity identities asserted by `mktable.py` for every class: ids/rows/orbits/complements equal the star table;
  `And = 0` exactly for the unions of rows and columns; `And <=` AND gates of the star table's monotone witness;
  `And <= min(row types, column types)`; `And >= ceil(log2 cov0)`; invariance under the symmetry group holds by
  construction and is re-checked by the SAT pass (which works on the representative only).
* Crown regression: `And(crown_n) = ceil(log2 n)` comes out of the tables (3x3: 2, 4x4: 2, 5x5: 3) and of SAT
  from zero for n = 8 (a = 2 UNSAT, a = 3 SAT) and n = 16 (a = 3 UNSAT, a = 4 SAT).

## 8. Command lines

    bin/andtab --n N [--m M] [--amax A] [-j T] [--out F.jsonl] [--costs F.bin] [--tlimit SEC] [--enc]
               [--nosym] [--nodom] [--noorder] [-q]
        n*m <= 25. -j defaults to $PNP_THREADS or 1 (threads split the root candidates; used only for a >= 2).
        --out: header line + one JSON line per class (witness verified). --costs: one byte per labelled graph.
        --tlimit: stop the level in progress (then it is NOT complete and nothing is claimed from it).
        --enc: also check that the bit-set wires add nothing to the level-0 closure.
    python3 src/andtab/mktable.py RUN.jsonl tables/star_N.json tables/and_N.json [--md]
        re-evaluates every witness, expands to .ckt, runs bin/cktcheck, asserts the sanity identities, writes the table.
    bin/satpy src/andtab/andsat.py graph --rows 14,13,11,7 [--m 4] [--hex] [--lo L] [--amax A] [--timeout SEC]
               [--model A|B|F] [--autos K] [--enc] [--no-core] [--no-sym] [--solver cadical195] [--ckt OUT.ckt] [--json]
    bin/satpy src/andtab/andsat.py family NAME N [...]       NAME: crown match ip disj inter gt rand<seed>
    bin/satpy src/andtab/andsat.py table tables/and_4.json [--model A|B|F] [--no-sym] [--no-core] [--quiet]
    bin/satpy src/andtab/ladder.py NAME N [--kmin K] [--drop0] [--timeout SEC]       corners of NAME_N
    bin/satpy src/andtab/structured.py run --out runs/andtab/structured.jsonl [--sizes 4,8,16,32] [--timeout SEC]
    bin/satpy src/andtab/structured.py table runs/andtab/structured.jsonl tables/and_structured.json [--md]
    make -C src/andtab        builds bin/andtab

Reproduce the three tables (seconds, one thread):

    for n in 3 4 5; do bin/andtab --n $n --out /tmp/and$n.jsonl && python3 src/andtab/mktable.py /tmp/and$n.jsonl tables/star_$n.json tables/and_$n.json --md; done

## 9. Limits and what is not claimed

* The native tool needs a table of all `2^(nm)` graphs: `nm <= 25`. 6x6 (about 126 000 classes) is not done.
  Its level-3 pass at 5x5 stops once every class is reached; a complete level 3 or 4 (needed only if some graph
  needed more) was never required.
* For one graph the only exhaustive method here is SAT. Refuting `a = 4` takes a fraction of a second on 8x8
  random graphs, 23 s on the 7x7 core of `IP_3`, and does not finish in 90 to 150 s on 16x16 graphs; refuting
  `a = 5` was not achieved on any graph. This is why entries at `n = 16` and `n = 32` are intervals unless the
  cover bound or a small corner settles them. `ladder.py` moves the work to small corners.
* Upper bounds at `n = 16, 32` come from SAT models found within 40 to 90 s per value of `a`, or from the
  constructions; they are not claimed to be optimal. For the 32x32 random graphs only the row-type circuit and
  the proved lower bound are given.
* M1-M6 are valid for minimum circuits only; every refutation used here starts from a proved bound or from 0.
  The pure model (`--no-sym`) was used to cross-check all tables.
* Nothing here is a Lean proof. The `.ckt` witnesses are checked by `bin/cktcheck`; the refutations are SAT runs
  (CaDiCaL 1.9.5 via python-sat, no proof logging) and the exhaustive native search.

## Note from the gpukit builder (2026-11-27; not part of andtab)

A Metal compute harness callable from C++ exists: `src/gpukit/gpu.hpp`, documented in `docs/gpukit.md`
(section "Offer to andtab"). The closure pair pass (X ∩ Y over all pairs of closure members, cell sets in one
64-bit word) is the kind of kernel it runs at 4–8e10 exact pair tests/s against the 1.06e9/s reported above.
5x5 is already done in 23 s on one core, so this only matters for a 6x6 attempt. Nothing was changed in andtab.
