# startab — exact star-complexity tables for all small bipartite graphs

Built for the analytic (lower-bound) track: ground truth to compare LP-dual lower bounds against.
Tool: `bin/startab` (native, multi-threaded, exhaustive). Everything marked "exact" is proved by exhaustive search
in the full Lean model, not best-found.

| file | content |
|---|---|
| `tables/star_3.json`, `tables/star_4.json` | every 3x3 / 4x4 bipartite graph up to row permutations, column permutations and transpose (26 / 192 classes): exact mono and NOT size, one witness each. Complete. |
| `tables/star_5.json` | every 5x5 graph (3014 classes): exact where the complete passes reach, otherwise proved lower bound + best circuit (see section 6 for the counts). |
| `tables/star_5_not_exact.txt` | the complete list of the 5x5 entries that are NOT exact: canonical rows, basis, proved lower bound, best circuit found. Every 5x5 entry not in this list is exact. |
| `tables/star_4_enc.json` | every labelled 4x4 graph with free encoder wires, 805 classes under the bit-structure symmetries (group order 128). Complete and exact; also carries the stars-only sizes for comparison. |
| `tables/star_8_enc_sample.json` | a sample of named 8x8 graphs with free encoder wires: per entry proved lower bound, best circuit, exact flag. |
| `tables/star_3_labelled.json`, `tables/star_4_labelled.json` | one hex digit per LABELLED graph (no canonicalisation needed): mono, NOT, and for 4x4 the two encoder sizes. |
| `src/startab/` | `startab.cpp` (engine), `tricheck.cpp`, `mktable.py`, `lookup.py`, `satcheck.py`, `enc8.py`, `ubsls.py`, `report.py` |
| `runs/startab/` | raw run outputs (`*.jsonl`, `*.cost`, `*.ckpt`, logs) |

## 1. What is tabulated

For a bipartite graph `A : Fin n → Fin m → Bool` the tables give the least number of gates of a circuit `C` with
`Represents A C` (right on the `n*m` inputs `oneEach u v`: exactly row wire `u` and column wire `n+v` on; nothing
is asked elsewhere), in two bases:

| key    | Lean                                         | gates                                              |
|--------|----------------------------------------------|----------------------------------------------------|
| `mono` | `PEqualNP.Represents.RepSizeAtMost` (`Monotone2` + `Represents`) | AND, OR, at most two inputs        |
| `not`  | `FanInTwo` + `Represents`                    | AND, OR, NOT, at most two inputs, NOT counted      |

Every gate counts. A gate may name any wire; a wire that does not exist (yet) reads false; an AND gate with no input
is the constant true (one gate); a gate with one input is a copy; NOT reads its first input only; the output may be
an input wire or a missing wire. Hence: empty graph = 0, a full row or full column = 0, complete graph = 1
(for n, m >= 2; it is not an input and one constant gate does it).

Encoder tables (`star_4_enc.json`): the same, but the circuit also gets, free, the row-bit sets
`{u : bit_i(u) = a}` and the column-bit sets `{v : bit_i(v) = a}` (i < log2 n, a in {0,1}) as extra input wires.
On the points `oneEach u v` these wires carry exactly the literals of the binary indices, so this is the De Morgan
size of `adjFun A` on `2 log n` bits with free literals plus free stars. Wire order: `0..n-1` rows, `n..n+m-1`
columns, then for each row-index bit `i = 0,1,..`: `{bit_i = 0}`, `{bit_i = 1}`, then the same for the column index
(the `"inputs"` array of the JSON lists the names in order: `rb0=0, rb0=1, rb1=0, ...`).

## 2. Why the search loses nothing against the Lean model (normal form)

A wire's value on the `P = n*m` points is a `P`-bit vector (an `n x m` 0/1 matrix); AND/OR/NOT act bitwise.
Call a circuit *normal* if every gate is `AND(a,b)`, `OR(a,b)` with two different earlier existing wires, or
`NOT(a)` with an earlier existing wire, and every gate's vector is new: not all-zero, not all-one, not equal to an
input's or an earlier gate's vector.

**Claim.** Let `T` be a target that is not all-zero, not all-one and not an input vector. Every least circuit for
`T` (in the full Lean model, basis `mono` or `not`) is normal (up to the ignored second input of a NOT gate), its
output is its last gate, and every other gate is read by a later gate.

*Proof.* (1) If gate `j` has the vector of an earlier wire `i` (input or gate) or the zero vector, delete it and
redirect every read of wire `N+j` by a later gate, and the output if it was `N+j`, to `i` (resp. to an index that
never exists, which reads false); references by earlier gates to `N+j` were forward references reading false and
are redirected to a never-existing index too; later wires are renumbered. The circuit computes the same output
with one gate fewer. So in a
least circuit no gate repeats an earlier vector or is zero.
(2) Gate shapes. `OR[]` is zero. `AND[a]`, `OR[a]` copy `a` or are zero. `AND(a,b)` with `a` or `b` missing is
zero; `OR(a,b)` with one missing is a copy or zero; with `a = b` both are copies. All excluded by (1). What is
left: `AND(a,b)`, `OR(a,b)` on two different existing earlier wires, `NOT(a)` on an existing earlier wire
(`NOT[a,b]` is `NOT a`), and gates with the all-one vector (`AND[]`, `NOT[]`, NOT of a missing or zero wire, an OR
that happens to be full).
(3) Suppose gate `j` is all-one and `T` is not. `j` is not the output. A later gate that really reads `j` is
`AND(j,x) = x` (a copy, or zero, or all-one again and then a repeat of `j`), `OR(j,x)` = all-one (repeat of `j`), or
`NOT(j)` = zero: all excluded by (1). So nothing reads `j` and it can be deleted: contradiction with leastness.
(4) Gates after the output gate, and gates read by nobody, can be deleted. ∎

So for such `T` the Lean minimum equals the least `s` such that some set of `s` distinct, non-constant, non-input
vectors containing `T` can be ordered so that each is `a AND b`, `a OR b` (or `NOT a`) of inputs and earlier ones.
The three trivial kinds of target are handled explicitly: zero (0 gates, output = a missing wire), an input vector
(0 gates), all-one (1 gate: it is not an input for n, m >= 2, and `AND[]` is one gate).
With encoder wires the same proof applies verbatim (more input vectors).

## 3. Method (all classes at once)

Pass `r = 2, 3, ...` enumerates every *derivable set* `S'` of `r-1` gate vectors (each derivable from inputs and
the others in some order) and marks every vector `f op x` that one more gate gives. Induction: after pass `r`
every vector of size `<= r` carries its exact size. A vector first marked in pass `r` has a circuit of `r` gates
(the witness) and none of `r-1` (pass `r-1` was complete), so even an interrupted last pass yields exact values for
whatever it marks; what stays unmarked has size `> (last complete pass)`.

* **Each set once.** At a node (set `C`, candidate list = vectors one gate away, minus those seen), the children
  are "add candidate i, forbid candidates before i for the whole subtree" (include/exclude). Every derivable
  superset has exactly one path. A hash set of everything seen (in the set, forbidden, or a live candidate) with
  LIFO undo does the bookkeeping; the list is extended by `new gate op old wire` only.
* **Symmetry.** The group `G` (row perms x column perms x transpose; encoder: index-bit permutations and
  complementations per side x transpose) permutes the inputs. At a node keep `H` = elements of `G` fixing every
  gate vector of the prefix. Candidates split into `H`-orbits; only the first member of each orbit is expanded and
  the whole orbit is forbidden afterwards; the child gets the stabiliser of the new gate in `H`. Forbidden sets stay
  `H`-invariant by induction, so for every derivable set some image under `G` is visited. After each pass the cost
  table is closed under `G` (class minimum).
* **Sink bound.** Fix for every gate of the prefix the derivation it was first found with. Gates not read by
  another gate of the prefix under these derivations are *sinks*. In a least circuit of `r` gates EVERY choice of
  derivations must use every non-output gate (else delete the unused gate), and `R` remaining gates have at most
  `R+1` operand slots for old wires (`2R` slots, `R-1` taken by the new gates feeding each other). So
  `#sinks <= R+1` at every prefix, and the last gate must read all remaining sinks.
* **Cost bounds** (use the exact sizes `c(.)` already known from the earlier passes). Let the prefix have `k`
  gates, `D` be the `R` remaining gates and `U` the old gates read by `D` (all sinks are in `U`, `|U| <= R+1`).
  (a) `sum_{u in U} c(u) >= k`: otherwise rebuild every `u` from scratch with `c(u)` gates and keep `D`:
  fewer than `k + R` gates. (b) `c(u) >= |dom(u)|` where `dom(u)` = gates of the prefix lying in the cone of `u`
  and in the cone of no other member of `U`: nothing outside `dom(u)` reads them (a reader would be in some other
  cone), so they can be replaced by a least circuit for `u`. When `U` is not determined (`|sinks| < R+1`) the
  program only prunes if every admissible `U` fails (one free slot: all choices are tried; more: only (a) with the
  most expensive other gates).
* **Direct completion.** With 2 gates left and 3 sinks, or 3 left and 4 sinks, or 2 left and 2 sinks, all
  completions are generated directly (a superset of what the lists would give; duplicates do no harm because a
  mark is always a real circuit), each filtered by the cost bounds with `U` known exactly.
* **Early stop.** If every class has been resolved the current pass is abandoned: nothing is left to find.
* Threads share work through a small task queue (a thread hands a subtree to an idle thread; state is copied).
  The cost table is deterministic for any `-j`; which witness circuit is stored for a class can differ between
  runs with `-j > 1` (every stored witness is verified).

Switches `--nosym`, `--nosink`, `--nocost`, `--notight`, `--notranspose` turn the individual reductions off; they
exist for cross-checking (section 8).

## 4. Command lines

    bin/startab --n N [--m M] [--basis ao|aon] [--enc] [--rmax R] [--tlimit SEC] [-j T]
                [--out F.jsonl] [--costs F.bin] [--ckpt F.ckpt] [--resume F.ckpt]
                [--split L] [--nosym] [--nosink] [--notight] [--nocost] [--notranspose]
      n*m <= 25.  -j defaults to $PNP_THREADS or 1.  --out: one JSON line per class (witness already verified with
      pnp::verify).  --costs: one byte per labelled graph (index = sum_u rows[u] << (m*u), 255 = not reached).
      --ckpt/--resume: checkpoint after every complete pass / continue from it.  --rmax: last pass to run.
      --tlimit: stop after SEC seconds (the pass in progress is then incomplete; its marks are still exact).
      --ub: after the passes, look for circuits for the classes not reached (section 7).
    bin/startab-tricheck COSTS.bin POINTS [--not] [--sample K] [-j T]      consistency checks of a cost file (section 8)
    python3 src/startab/mktable.py AO.jsonl AON.jsonl tables/star_N.json [--plain-costs AO.cost AON.cost] [--ub F.jsonl] [--md]
      merges the two bases, re-checks EVERY witness with bin/cktcheck against a generated spec, writes the summary blocks.
    python3 src/startab/ubsls.py tables/star_5.json OUT.jsonl [--which undecided|all] [--time S] [-j T]
      better upper bounds for non-exact entries with bin/cktsls (heuristic); merge with mktable.py --ub OUT.jsonl.
    bin/satpy src/startab/enc8.py tables/star_8_enc_sample.json [--conf N] [--budget SEC]      the 8x8 encoder sample
    python3 src/startab/report.py        prints section 6 of this file from the tables
    python3 src/startab/lookup.py tables/star_4.json 14 13 11 7 [--complement] [--ckt mono|not]
      canonicalise any labelled graph, print its entry; --ckt prints the witness transported to that labelling.
    bin/satpy src/startab/satcheck.py tables/star_4.json [--basis mono|not|both] [--only i,j] [--budget SEC]
      independent SAT cross-check (section 7).

## 5. JSON schema (`tables/star_3.json`, `star_4.json`, `star_5.json`, `star_4_enc.json`, `star_8_enc_sample.json`)

    { "n":4, "m":4, "encoder":false,
      "semantics": "...", "inputs": ["r0",..,"c3"], "symmetry": "...", "group_order": 1152,
      "rows_convention": "bit v of rows[u] = A u v; representative = least value of sum_u rows[u] * 2^(m*u)",
      "num_classes": 192, "last_complete_pass": {"mono":11,"not":11},
      "classes": [ { "id":187, "rows":[14,13,11,7], "orbit_size":24, "complement":95,
                     "mono": {"size":11, "exact":true, "witness":"inputs 8\nor 1 0\n...out 18\n"},
                     "not":  {"size":8,  "exact":true, "witness":"..."} }, ... ],
      "summary": { "mono_hist_classes":{size:count}, "mono_hist_labelled":{..}, "not_hist_classes":{..},
                   "not_hist_labelled":{..},
                   "not_saving": {conjectured_bound (2n-5), hist, max, extremal, proven_violations, undecided_by_bounds, holds} },
      "complement_gap": { conjectured_bound (2n-4), hist_pairs, max_gap_exact_pairs,
                          extremal_pairs: [{rows, size, complement_rows, complement_size}],
                          proven_violations, undecided_by_bounds, open_pairs, holds } }

`holds` is `true` (proved for every graph of that size), `false` (a violation is forced) or `null` (the bounds of
some non-exact entries do not decide it; those entries are listed in `undecided_by_bounds`).

* `rows[u]` is an integer, bit `v` set iff `A u v`. `orbit_size` = number of labelled graphs in the class
  (the orbit sizes of a table add up to `2^(n*m)`). `complement` = `id` of the class of the complement graph.
* `exact: true` only if size-1 was refuted exhaustively in the full model (complete pass `size-1`, or the trivial
  cases of section 2). Otherwise the entry is `{"size": best found or null, "exact": false, "lower": L}` with `L`
  proved (`L-1` = last complete pass). An entry with `"exact": true` AND a `"lower"` field was not reached by a
  complete pass itself: its circuit was found separately and has exactly `lower` gates (`"how"` says how).
* `witness` is a toolkit `.ckt` text for the representative `rows`; it passes
  `bin/cktcheck SPEC CKT --basis ao|aon --max size` against `type graph` (plain tables) or `type points` (encoder
  tables, one input column per wire of `"inputs"`).
* Encoder table only: `star_mono`, `star_not` = sizes of the same labelled graph without the encoder wires, and
  `summary.encoder_saving_*`. Classes there are NOT up to arbitrary vertex permutations: only index-bit
  permutations/complementations on each side (the 8 symmetries of the 2-cube for n = 4) and transpose, group
  order `8*8*2 = 128`; these are exactly the relabellings that map the encoder wires to encoder wires.

## 6. Results

### 3x3  (`tables/star_3.json`)

26 classes up to row permutations, column permutations, and transpose (group order 72); 512 labelled graphs. Last complete pass: mono 7, NOT 6.

* mono exact sizes, classes: `0:2 1:4 2:3 3:5 4:3 5:6 6:1 7:2`
* mono exact sizes, labelled graphs: `0:7 1:25 2:72 3:108 4:108 5:114 6:36 7:42`
* NOT  exact sizes, classes: `0:2 1:4 2:5 3:3 4:6 5:3 6:3`
* NOT  exact sizes, labelled graphs: `0:7 1:25 2:90 3:90 4:144 5:78 6:78`
* **NOT saving** `mono - not` (classes with both exact): `0:19 1:7`. Maximum **1**, conjectured bound 2n-5 = **1**. Proven violations: **0**. Classes not both exact: 0, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal classes (rows: mono / not): [3, 3, 0]: 3 / 2; [6, 1, 1]: 5 / 4; [6, 3, 1]: 7 / 6; [6, 6, 1]: 5 / 4; [6, 5, 3]: 7 / 6; [7, 5, 3]: 5 / 4; [7, 7, 3]: 3 / 2
* **Complement gap** `|mono(G) - mono(co-G)|` (pairs with both exact): `0:2 1:7 2:4`. Maximum **2**, conjectured bound 2n-4 = **2**. Proven violations: **0**. Pairs not both exact: 0, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal pairs (rows of G: size / rows of the complement: size): [7, 7, 3]: 3 / [1, 0, 0]: 1; [7, 5, 3]: 5 / [2, 1, 0]: 3; [3, 3, 0]: 3 / [7, 1, 1]: 1; [6, 5, 3]: 7 / [4, 2, 1]: 5
* crown (u != v), rows [6, 5, 3]: mono 7, not 6
* perfect matching (u = v), rows [4, 2, 1]: mono 5, not 5
* largest exact mono sizes: [6, 3, 1]: 7 (not 6); [6, 5, 3]: 7 (not 6); [5, 2, 1]: 6 (not 6); [5, 3, 0]: 5 (not 5); [6, 1, 1]: 5 (not 4); [4, 2, 1]: 5 (not 5)
* largest exact NOT sizes: [5, 2, 1]: 6 (mono 6); [6, 3, 1]: 6 (mono 7); [6, 5, 3]: 6 (mono 7); [5, 3, 0]: 5 (mono 5); [4, 2, 1]: 5 (mono 5); [7, 6, 1]: 5 (mono 5)

### 4x4  (`tables/star_4.json`)

192 classes up to row permutations, column permutations, and transpose (group order 1152); 65536 labelled graphs. Last complete pass: mono 11, NOT 11.

* mono exact sizes, classes: `0:2 1:4 2:4 3:9 4:10 5:20 6:24 7:35 8:30 9:38 10:10 11:6`
* mono exact sizes, labelled graphs: `0:9 1:45 2:200 3:688 4:1776 5:4088 6:7632 7:10322 8:14640 9:18696 10:6096 11:1344`
* NOT  exact sizes, classes: `0:2 1:5 2:7 3:12 4:16 5:26 6:38 7:35 8:34 9:14 10:2 11:1`
* NOT  exact sizes, labelled graphs: `0:9 1:53 2:288 3:1008 4:2792 5:6216 6:11754 7:16104 8:17976 9:8592 10:672 11:72`
* **NOT saving** `mono - not` (classes with both exact): `0:83 1:65 2:32 3:12`. Maximum **3**, conjectured bound 2n-5 = **3**. Proven violations: **0**. Classes not both exact: 0, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal classes (rows: mono / not): [7, 7, 7, 0]: 5 / 2; [13, 11, 7, 0]: 10 / 7; [14, 1, 1, 1]: 7 / 4; [14, 3, 1, 1]: 9 / 6; [14, 7, 1, 1]: 9 / 6; [14, 14, 14, 1]: 7 / 4; [14, 13, 3, 3]: 9 / 6; [14, 13, 7, 3]: 11 / 8; [14, 13, 11, 7]: 11 / 8; [15, 13, 11, 7]: 9 / 6; [15, 15, 11, 7]: 7 / 4; [15, 15, 15, 7]: 5 / 2
* **Complement gap** `|mono(G) - mono(co-G)|` (pairs with both exact): `0:36 1:32 2:22 3:8 4:6`. Maximum **4**, conjectured bound 2n-4 = **4**. Proven violations: **0**. Pairs not both exact: 0, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal pairs (rows of G: size / rows of the complement: size): [15, 15, 15, 7]: 5 / [1, 0, 0, 0]: 1; [15, 15, 11, 7]: 7 / [2, 1, 0, 0]: 3; [15, 13, 11, 7]: 9 / [4, 2, 1, 0]: 5; [7, 7, 7, 0]: 5 / [15, 1, 1, 1]: 1; [13, 11, 7, 0]: 10 / [15, 4, 2, 1]: 6; [14, 13, 11, 7]: 11 / [8, 4, 2, 1]: 7
* crown (u != v), rows [14, 13, 11, 7]: mono 11, not 8
* perfect matching (u = v), rows [8, 4, 2, 1]: mono 7, not 7
* largest exact mono sizes: [14, 11, 7, 1]: 11 (not 9); [14, 9, 5, 3]: 11 (not 10); [12, 10, 5, 3]: 11 (not 11); [13, 12, 7, 3]: 11 (not 9); [14, 13, 7, 3]: 11 (not 8); [14, 13, 11, 7]: 11 (not 8)
* largest exact NOT sizes: [12, 10, 5, 3]: 11 (mono 11); [13, 10, 6, 1]: 10 (mono 10); [14, 9, 5, 3]: 10 (mono 11); [12, 5, 2, 1]: 9 (mono 9); [14, 5, 2, 1]: 9 (mono 9); [11, 7, 2, 1]: 9 (mono 10)

### 5x5  (`tables/star_5.json`)

3014 classes up to row permutations, column permutations, and transpose (group order 28800); 33554432 labelled graphs. Last complete pass: mono 11, NOT 11.

* mono exact sizes, classes: `0:2 1:4 2:4 3:10 4:15 5:29 6:49 7:95 8:151 9:278 10:432 11:679 12:457`  — plus 809 classes (13123800 labelled graphs) with bounds only
* mono exact sizes, labelled graphs: `0:11 1:71 2:420 3:2010 4:8000 5:28400 6:91400 7:257100 8:665500 9:1704570 10:3980100 11:6778650 12:6914400`
* NOT  exact sizes, classes: `0:2 1:5 2:8 3:17 4:30 5:58 6:113 7:196 8:356 9:515 10:643 11:603 12:290`  — plus 178 classes (3122880 labelled graphs) with bounds only
* NOT  exact sizes, labelled graphs: `0:11 1:81 2:570 3:3200 4:14050 5:59600 6:199800 7:629850 8:1832650 9:4503420 10:7860120 11:9843600 12:5484600`
* mono entries that are NOT exact, as [proved lower bound, best circuit found]: [12,13] x515, [12,14] x204, [12,15] x75, [12,16] x14, [12,17] x1
* not entries that are NOT exact, as [proved lower bound, best circuit found]: [12,13] x154, [12,14] x21, [12,15] x3
* **NOT saving** `mono - not` (classes with both exact): `0:706 1:718 2:525 3:201 4:45 5:10`. Maximum **5**, conjectured bound 2n-5 = **5**. Proven violations: **0**. Classes not both exact: 809, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal classes (rows: mono / not): [15, 15, 15, 15, 0]: 7 / 2; [31, 27, 23, 15, 0]: 12 / 7; [30, 1, 1, 1, 1]: 9 / 4; [30, 3, 1, 1, 1]: 11 / 6; [30, 15, 1, 1, 1]: 11 / 6; [30, 30, 30, 30, 1]: 9 / 4; [30, 29, 3, 3, 3]: 11 / 6; [31, 31, 27, 23, 15]: 11 / 6; [31, 31, 31, 23, 15]: 9 / 4; [31, 31, 31, 31, 15]: 7 / 2
* **Complement gap** `|mono(G) - mono(co-G)|` (pairs with both exact): `0:237 1:368 2:185 3:71 4:26 5:9 6:5`. Maximum **6**, conjectured bound 2n-4 = **6**. Proven violations: **0**. Pairs not both exact: 606, of which the bounds leave 0 undecided. Verdict for every graph of this size: **holds**.
  Extremal pairs (rows of G: size / rows of the complement: size): [31, 31, 31, 31, 15]: 7 / [1, 0, 0, 0, 0]: 1; [31, 31, 31, 23, 15]: 9 / [2, 1, 0, 0, 0]: 3; [31, 31, 27, 23, 15]: 11 / [4, 2, 1, 0, 0]: 5; [31, 27, 23, 15, 0]: 12 / [31, 4, 2, 1, 0]: 6; [15, 15, 15, 15, 0]: 7 / [31, 1, 1, 1, 1]: 1
* crown (u != v), rows [30, 29, 27, 23, 15]: mono [12, 15], not 10
* perfect matching (u = v), rows [16, 8, 4, 2, 1]: mono 9, not 9
* largest exact mono sizes: [29, 7, 3, 1, 0]: 12 (not 9); [23, 13, 3, 1, 0]: 12 (not 9); [23, 14, 3, 1, 0]: 12 (not 10); [29, 15, 3, 1, 0]: 12 (not 9); [23, 11, 6, 1, 0]: 12 (not 11); [30, 11, 6, 1, 0]: 12 (not 11)
* largest exact NOT sizes: [26, 14, 7, 1, 0]: 12 (mono 12); [25, 11, 5, 3, 0]: 12 (mono 12); [21, 13, 7, 3, 0]: 12 (mono 12); [26, 21, 12, 3, 0]: 12 (mono 12); [27, 21, 12, 3, 0]: 12 (mono 12); [21, 14, 13, 3, 0]: 12 (mono 12)

### 4x4 with free encoder wires  (`tables/star_4_enc.json`)

805 classes up to index-bit permutations and complementations on each side, and transpose (group order 128); all exact in both bases.

* mono sizes with encoder wires, classes: `0:3 1:9 2:16 3:52 4:85 5:177 6:189 7:182 8:74 9:18`; labelled graphs: `0:17 1:141 2:640 3:2760 4:6544 5:14712 6:17576 7:15746 8:6256 9:1144`
* mono: (stars only) - (with encoder wires), labelled graphs: `0:3216 1:18904 2:28256 3:12608 4:2264 5:256 6:32`; mean size 7.770 -> 5.882
* NOT  sizes with encoder wires, classes: `0:3 1:9 2:18 3:52 4:102 5:172 6:228 7:161 8:57 9:3`; labelled graphs: `0:17 1:141 2:672 3:2792 4:7336 5:14560 6:19962 7:14664 8:5200 9:192`
* NOT : (stars only) - (with encoder wires), labelled graphs: `0:12520 1:30712 2:17840 3:4200 4:264`; mean size 6.985 -> 5.764
* largest encoder saving (mono): [13, 12, 7, 3]: 11 -> 5; [14, 13, 10, 1]: 10 -> 5; [14, 13, 11, 1]: 11 -> 6; [14, 12, 7, 3]: 11 -> 6; [7, 5, 3, 0]: 7 -> 3
* hardest with encoder wires (mono): [9, 10, 6, 1]: 9 (stars only 9); [13, 10, 6, 1]: 9 (stars only 10); [13, 11, 6, 1]: 9 (stars only 10); [3, 14, 6, 1]: 9 (stars only 9); [14, 9, 5, 3]: 9 (stars only 11)

### 8x8 with free encoder wires, sample  (`tables/star_8_enc_sample.json`)

| graph | mono | NOT | note |
|---|---|---|---|
| biclique_x2_y2 | **1** | **1** | K_{4,4}: x2 AND y2 |
| intersect | **5** | **5** | x AND y != 0 (OR_i x_i y_i) |
| disjoint | **5** | **5** | x AND y = 0 |
| equal_low2 | **7** | **7** | x1x0 = y1y0 (two disjoint copies of a 4x4 matching, blown up) |
| xor_bit0 | **3** | **3** | x0 XOR y0 |
| xor_two | **7** | **7** | (x0 XOR y0) OR (x1 XOR y1) |
| matching | [8, 15] | [7, 15] | identity: u = v |
| crown | [8, 11] | [8, 11] | crown: u != v |
| half_le | [8, 9] | [7, 9] | half graph: u <= v |
| half_lt | [8, 9] | [7, 9] | u < v |
| parity | [8, 15] | [8, 11] | parity of all six bits |
| ip | [9, 15] | [8, 12] | inner product mod 2 |
| sum_mod8_zero | [8, 15] | [7, 15] | u + v = 0 mod 8 (a perfect matching) |
| cycle16 | [8, 17] | [8, 16] | Hamilton cycle C16: v in {u, u+1} |
| threshold_sum_ge7 | [8, 9] | [7, 9] | u + v >= 7 |
| paley_like | [9, ?] | [8, 17] | v - u in {1,2,4} mod 8 (circulant) |
| majority3 | **4** | **4** | MAJ(x0, x1, y0) |
| single_edge | **1** | **1** | one edge |
| star_minus_point | **3** | **2** | row star without one point |

Bold = exact (every smaller size refuted by SAT, or lower bound met); `[L, U]` = proved lower bound and best circuit found.

## 7. Entries that are not exact (5x5 only) and how their bounds were made

Which ones: in the JSON every entry carries `"exact"`; `tables/star_5_not_exact.txt` lists all non-exact entries
(rows, basis, lower bound, best circuit), and section 6 gives the counts per `[lower, best]` interval. 3x3, 4x4 and the
4x4 encoder table have no such entries.

* `lower` = (last complete pass) + 1. It is proved in the same sense as the exact entries: every circuit with
  fewer gates was enumerated (up to the reductions of section 3) and none computes the graph.
* `size` = the smallest circuit found, by `--ub` (in `startab.cpp`, after the passes):
  1. *threshold-2 seeds*: stars are put into blocks `B_1..B_k`, `w_i` = OR of block `i`, `M = K_k(w)` with `K_k` a
     monotone circuit that is 0 on one-hot and 1 on two-hot inputs (1, 4, 7, 10, 13 gates for k = 2..6; the fleet's
     crown construction). `M` joins row `u` and column `v` iff they lie in different blocks. All block
     assignments are tried (crown5 gets its 15 gates here).
  2. *decomposition rounds*: `T = a OR b`, `T = a AND b` (all pairs with overlap when the relevant side has at most
     15 points, else partitions only), `T = NOT a`, using for `a`, `b` the exact table or earlier bounds; the two
     circuits are concatenated, equal gates merged, unused gates dropped.
  3. *closure*: one more gate on any two wires of a known class circuit.
  4. optionally `ubsls.py` (stochastic search `bin/cktsls`) on selected classes, merged with `mktable.py --ub`.
  Every such circuit is checked like a witness. If it has exactly `lower` gates the entry is exact
  (`"how"` says so): the lower bound is proved and the circuit meets it.
* The complement-gap and NOT-saving blocks treat these entries with their intervals: a violation is reported only
  if it is forced by the bounds, and `"holds": true` only if it is forced for every pair/class
  (`undecided_by_bounds` empty). `null` means "not decided by the present bounds".

## 8. Cross-checks that were run

1. Every witness is verified three times: by the engine's own evaluator, by `pnp::verify` (shared header) before it
   is printed, and by `bin/cktcheck --basis ao|aon --max size` against a spec generated by `mktable.py`
   (`type graph` for the plain tables, `type points` with one column per input wire for the encoder tables).
2. Two engines. The first engine (sets + symmetry + sink bound only) and the second (plus cost bounds and direct
   completions) give byte-identical cost tables on: 3x3 (both bases, complete), 4x4 (both bases, complete),
   4x4 with encoder wires (both bases, complete), and 5x5 mono for all 33,554,432 labelled graphs through pass 11
   (first engine on 2 threads, second on 1 thread; md5 of the cost array 3c63e4bbec8db91c01876d663a4817cb).
   The first engine itself was compared with its reductions switched off (`--nosink` through pass 8, `--nosym`
   through pass 7, `--nosym --nosink --notranspose` through pass 6 at 4x4, everything at 3x3): no difference.
3. SAT, independent encoding (`satcheck.py`, written from scratch, CaDiCaL 1.9.5 through PySAT): for an entry of
   size `s`, UNSAT for exactly 1, ..., s-1 gates and SAT at `s`, decoded circuit re-evaluated.
   Results are listed in the progress notes at the end.
4. `bin/startab-tricheck`: `size(a op b) <= size(a) + size(b) + 1` and `size(NOT a) <= size(a) + 1` over ALL pairs of
   labelled graphs (3x3, 4x4, 4x4-encoder; 2.1e9 pairs each at 16 points), and every graph of size r >= 2 is
   `a op b` (or `NOT a`) of graphs of size <= r-1. No violation. On 5x5 the same on a random sample of pairs.
5. Sanity built into `mktable.py` (it aborts otherwise): NOT size <= mono size for every class; the complement map is
   an involution on classes; with encoder wires no labelled graph is more expensive than without. Checked
   separately on all three plain tables: mono <= the trivial bound (per non-empty, non-full row `|N(u)|` gates, plus
   the ORs joining the rows; best of rows / columns) for every class, with slack up to 3 / 6 / 12 at n = 3 / 4 / 5;
   `|not(G) - not(co-G)| <= 1` for every complement pair with both exact (26, 192, 2772 pairs): no exception; the
   orbit sizes add up to `2^(n*m)`; the `complement` ids agree with an independent canonicaliser (`lookup.py`).
6. Known values: crown3 = 7 and crown4 = 11 = n + K(n) with K(3) = 4, K(4) = 7 (fleet, L_meta_18508);
   perfect matching n: 5, 7, 9 = 2n-1 for n = 3, 4, 5; empty = 0, full row = 0, complete = 1, single edge = 1.
   crown5: the fleet has `>= 15` checked (L_meta_18006) and `= n + K(5) = 15`; this tool proves `>= 12` (complete
   pass 11) and supplies a verified 15-gate circuit, so the entry is `[12, 15]`, not exact here.

## 9. Measured throughput (Apple M5 Max; the machine was shared and mostly overloaded, load average 30-60)

| run | threads | result |
|---|---|---|
| 4x4 mono, first engine, all passes to 11 complete | 5 | 47.6 s total; pass 11: 1.64e9 sets + 2.75e9 leaf sets, 2.30e10 gate evaluations in 44.1 s = 1.0e8 sets/s, 5.2e8 gate-ops/s |
| 4x4 NOT, first engine, all passes to 11 complete | 5 | 121 s total; pass 11: 3.94e9 sets, 5.92e10 gate-ops in 113 s (5.2e8 gate-ops/s) |
| 4x4 mono, second engine, complete table (stops when every class is resolved) | 2 | 15.7 s |
| 4x4 NOT, second engine, complete table | 2 | 19.7 s |
| 4x4 + encoder wires, both engines, complete table | 3 / 2 | 56 s (first, mostly a pass it did not need) / 20.7 s (second) per basis |
| 5x5 mono pass 10 | 1 | 34.4 s (second engine); 45.7 s on 2 threads (first engine) |
| 5x5 mono pass 11 | 1 | 542 s (second engine: 1.61e9 sets, 3.30e10 gate-ops); 733 s on 2 threads (first engine: 3.19e9 sets, 5.64e10 gate-ops) |
| 5x5 NOT pass 10 | 3 | 36.1 s (second engine); 112 s on 1 thread |
| 5x5 NOT pass 11 | 1 | 1371 s (second engine: 3.53e9 sets, 6.90e10 gate-ops) |

A pass costs 16-18 times the previous one (mono) at 4x4 and 5x5. Memory: 33 MB cost table + 67 MB class table +
4 MB bitmap at 5x5, a few MB per thread. "sets" = prefixes visited; "gate-ops" = output gates evaluated and looked up.

## 10. Limitations, and what to do next

* 5x5 is exact only as far as the complete passes go (see section 6 for the counts). One more pass costs about
  18x: on a quiet machine pass 12 mono is roughly 40 min on 5 cores with the second engine, pass 13 half a day.
  Resume with `bin/startab --n 5 --basis ao --resume runs/startab/star5_ao.ckpt --rmax 12 --ub -j 5 --out
  runs/startab/star5_ao.jsonl --ckpt runs/startab/star5_ao.ckpt` (same for `aon`), then rebuild with
  `python3 src/startab/mktable.py runs/startab/star5_ao.jsonl runs/startab/star5_aon.jsonl tables/star_5.json --ub runs/startab/ub5_sls.jsonl`.
* The cost table is the same for any `-j`; the stored witness of a class may differ between runs with `-j > 1`.
* The method enumerates all classes at once, so it cannot go deeper for one hard graph (crown5 needs 15). For single
  graphs beyond the reach of the passes use `bin/cktsat` / `bin/cktsls`.
* n*m <= 25 (32-bit wires, one byte per labelled graph). 8x8 is out of reach for this engine; the 8x8 encoder file
  is a SAT / stochastic-search sample of named graphs, each entry with its own `lower`, `size`, `exact`.
* Upper bounds of the non-exact 5x5 entries are constructions, not searches; `ubsls.py --which all` would tighten
  many of them (it needs slot time).
* Not done: a 4x5 / 5x4 table (the binary supports `--n 4 --m 5`), and encoder tables for n = 8 beyond the sample.

## Progress notes (appended while the runs were going; newest last)

* 03:45  `tables/star_3.json` (26 classes) and `tables/star_4.json` (192 classes) written: both bases complete and
  exact (4x4: complete passes up to 11). All witnesses pass `bin/cktcheck`. Max mono - not = 2n-5 at both sizes
  (1 and 3), max complement gap = 2n-4 at both sizes (2 and 4): both conjectured bounds hold with equality.
* 03:50  `tables/star_4_enc.json` (805 classes under the group of order 128): complete and exact, both bases
  (complete pass 8, every remaining class found at 9).
* 04:00  SAT cross-check (`satcheck.py`, from-scratch CNF, CaDiCaL 1.9.5): all 46 non-trivial (class, basis)
  entries of 3x3 and 323 entries of 4x4 (every class of size <= 8 in both bases, plus 12 mono and 4 NOT classes
  of size 9) confirmed: UNSAT for every smaller number of gates, SAT at the table size. No mismatch.
* 04:10  Engine rewritten once (cost bounds + direct completions, about 2.5x faster per core); the new engine
  reproduces the complete 3x3, 4x4 and 4x4-encoder cost tables of the first engine byte for byte, both bases.
* 04:12  `bin/startab-tricheck`: subadditivity and local derivability hold over ALL pairs of the 3x3, 4x4 and
  4x4-encoder tables (2.1e9 pairs each at 16 points), both bases.
* 04:25  Preliminary `tables/star_5.json` (3014 classes): mono complete to pass 11, NOT complete to pass 10, plus
  circuits by decomposition / threshold-2 constructions for the classes not reached. The machine was heavily
  loaded (load average 30-60, 8 of 12 slots held by an urgent job), so the 5x5 passes run on one slot.
* 04:36  5x5 mono, complete pass 11 with the second engine on one thread (542 s): cost array identical for all
  33,554,432 labelled graphs to the first engine's pass-11 result. 1748 classes exact by the passes; the `--ub`
  step (threshold-2 seeds + decomposition) finds a 12-gate circuit for 457 of the 1266 classes not reached, which
  makes them exact (lower bound 12 proved by the complete pass 11). 809 mono classes remain as `[12, best found]`.
* 05:01  5x5 NOT, complete pass 11 (1371 s on one thread): 2546 classes exact by the passes, 290 more exact at 12
  by decomposition, 178 classes remain as `[12, best found]`.
* 05:03  `tables/star_5.json` rebuilt (6028 witnesses re-checked with `bin/cktcheck`). Both conjectured bounds are
  now DECIDED for every 5x5 graph, and hold with equality: max (mono - not) = 5 = 2n-5, max complement gap = 6 = 2n-4.
  For the classes that are not exact this uses their intervals: (best mono circuit) - (proved NOT lower bound) <= 5
  for every class, and (best circuit of G) - (proved lower bound of co-G) <= 6 both ways for every pair. The same
  verdicts were recomputed by a separate script straight from the JSON, and the complement ids were re-derived with
  the independent canonicaliser of `lookup.py`. No violation; no pair or class is left undecided.
