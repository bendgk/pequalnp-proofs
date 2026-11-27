# ckt2lean and leancheck

`bin/ckt2lean` turns a circuit that `bin/cktcheck` accepts into a complete Lean 4 proof file for a pequalnp.com
unit. `bin/leancheck` lints that file by the checker's format rules and builds it in a private copy of the proofs
repository. Both are Python (`bin/satpy`); neither is a hot path.

Sources: `src/ckt2lean/ckt2lean.py`, `src/ckt2lean/leancheck.py`, and the Lean text that is pasted into every
inline proof: `src/ckt2lean/prelude_core.lean`, `prelude_graph.lean`, `prelude_tt.lean`.

## CLI

    bin/ckt2lean --unit L-meta-20580 --statement-file STMT.txt [--kind K] [--style S] SPEC CKT -o OUT.lean
    bin/ckt2lean --from-kn specs/kn7.spec KN.ckt --crown-out CROWN.ckt [--unit U --statement-file STMT.txt -o OUT.lean]
    bin/leancheck OUT.lean [--statement-file STMT.txt] [--allow-import MODULE]... [--lint-only] [--numerals warn]

* `STMT.txt`: the posted statement, verbatim (one Lean term). A whole skeleton `theorem NAME : STATEMENT := ...`
  is accepted too; the statement is copied into the file untouched.
* The theorem is `PEqualNP.Outside.L_meta_<n>`, last, at top level; helpers are in
  `namespace PEqualNP.Outside.L_meta_<n>_aux` ... `end ...`, both at column 0.
* `--kind` (read off the statement when omitted): `represents`, `represents-mono`, `represents-ao2`, `tt`,
  `tt-mono`, `tt-multi`. The basis (`aon`, `ao`, `ao2`) and the size bound are read off the statement
  (`C.size ≤ s`, `RepSizeAtMost A s`, `RepSize2AtMost A s`, `HasCircuitSize n f s`; `--max` overrides).
* ckt2lean FIRST runs `bin/cktcheck SPEC CKT --basis B --max S` (and the Python reference evaluator). A circuit
  that is wrong, too big or outside the basis is refused and nothing is written (exit 1).
* `--body-only`: writes only the helper namespace block, a blank line, and the one-line proof term that goes
  after `:=`. The inline style needs no import beyond `PEqualNP.Defs` (stderr repeats the import list).
* `--name-suffix _rt`: other module/theorem name, for building a unit that is already on main.
* `--from-kn`: KN.ckt is a circuit on n wires that is 0 on 1-hot and 1 on 2-hot inputs (`specs/kn<n>.spec`,
  basis `ao`). The crown circuit is: wires 0..n-1 left, n..2n-1 right, the n gates `z_i = x_i OR y_i` first
  (wires 2n..3n-1), then the K gates with input i moved to wire 2n+i and gate j to wire 3n+j. It is written to
  `--crown-out`, checked against `specs/crown<n>.spec --basis ao --max S`, and then emitted like any graph unit.

### Styles

| style | shape | imports | when |
|---|---|---|---|
| `direct` | one term, `by exact ⟨({ gates := [...], output := o } : Circuit), by simp [Monotone2], by decide, by decide +kernel⟩` (the accepted L_meta_19546) | `PEqualNP.Defs` | default for graph units with n*m ≤ 100 and ≤ 64 gates (`by simp [FanInTwo]` for the ∃ FanInTwo form, `by decide +kernel` for IsAO2) |
| `inline` | self-contained bit-column simulation in the `_aux` namespace | `PEqualNP.Defs` | default otherwise; the only style for truth tables |
| `lib` | the accepted L_meta_20578 / L_meta_19358: `PEqualNP.Library.Helpers.PromiseColTree.represents_of_tcols` | `PEqualNP.Defs`, `PEqualNP.Library.Helpers.PromiseColTree` | only if the unit's gap lists that import; row-list graph statements only |

The accepted L_meta_19546 and L_meta_20578 import all of `Mathlib` as well. That is allowed but costs about 3 GB
and 25 s more (measured below), so the emitter does not write it; `--imports Mathlib,PEqualNP.Defs` puts it back.

### How the inline proof works

Every wire is one natural number: bit p is the wire's value at point p (graph: p = u*m + v for the input
`oneEach u v`; truth table: p = `tableIndex x`). An AND gate is `&&&`, OR is `|||`, NOT is XOR with the all-ones
mask. The columns are kept in a `BinaryTree ℕ` (Mathlib's type, no new data type and no instance is declared),
read and written along one path, so a gate costs O(log wires) kernel steps. A simulation lemma (`wcol_bit`) says
bit p of the column of wire o is `(C.wires input_p).getD o false`. The checks are `decide +kernel`:

* basis: `fanInTwoB ckt = true` / `monotone2B ckt = true` (soundness lemmas inside), or `IsAO2 (n + m) ckt` directly;
* size: `ckt.size ≤ s`;
* graph, row-list statement (`fun u v : Fin n => (([r0, ...] : List ℕ).getD u.val 0).testBit v.val`):
  output column `==` the closed-form column of the rows (`--graph-check rows`, automatic);
* graph, any other `A` (crown: `decide (u ≠ v)`): one bit test per pair, `∀ u v, bit (u*m+v) = A u v`
  (`--graph-check points`);
* truth table, `--tt-proof enum`: bit a of the output column against the statement's own function at input a, for
  all a < 2^n (any decidable right-hand side; the function is taken from the statement by unification, the body
  does not repeat it);
* truth table, `--tt-proof expr`: the right-hand side is parsed (`x i`, `&&`, `||`, `^^`, `!`, `xor`, `true`,
  `false`, parentheses, also `(fun x => ...) x`), rewritten as the same formula over input columns, and compared
  once; `simp only` with the `testBit` lemmas shows the column formula has the right bits. No enumeration.
  `auto` uses `expr` when n ≥ 14 and the formula can be read, `enum` otherwise. If the parse were wrong the
  build fails; nothing unsound can come out.

No numeral longer than a wire index is written by the emitter: there are no packed constants at all (input,
mask and target columns are computed in the kernel). The only long numerals in a file are those of the posted
statement itself.

### What a circuit may contain (all three styles)

Exactly the model of FORMAT.md: AND/OR/NOT with 0, 1 or 2 inputs (constants and copies included), any wire index
(a wire that does not exist yet, or never, reads false), any output index. The accepted L_meta_19034 template
needed "AND/OR read exactly two wires, NOT exactly one"; this one does not. `represents-ao2` (IsAO2) is the
statement's own restriction: exactly two earlier wires, AND/OR only; `cktcheck --basis ao2` enforces it first.
There is no limit on the gate count other than the 512 KiB file (about 30 bytes a gate after a 22 KB prelude).

### Statement shapes, and what was actually built

Built and passed (lint, `lake build`, axioms) with the listed test circuit:

| statement shape | kind | styles built |
|---|---|---|
| `∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin n => (([r0, ...] : List ℕ).getD u.val 0).testBit v.val) C` | represents | inline rows (32x32 206 and 180 gates; 128x128 2023 gates), inline points (same, and 1500 gates), lib (180 and 1500 gates) |
| `RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) k` | represents-mono | direct (crown7 23, crown4 11), inline points (crown7 23) |
| `RepSize2AtMost (fun u v : Fin n => decide (u ≠ v)) k` | represents-ao2 | direct, inline (crown4 11) |
| `∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin n => decide (u ≠ v)) C` | represents | direct, inline points (crown3 as 3 AND, 2 OR, 1 NOT) |
| `∃ C, FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = formula` | tt | inline enum (cyc5, cyc14, a circuit with NOT, copy and constant gates), inline expr (cyc5, the NOT/copy/constant circuit) |
| the same with `Monotone2` | tt-mono | inline enum (cyc5) |
| `HasCircuitSize n (fun x : Fin n → Bool => formula) s` | tt | inline enum, inline expr (cyc5) |
| `... = (fun x : Fin n → Bool => formula) x` | tt | inline enum, inline expr (cyc5) |
| `∃ (C : Circuit) (o : Fin K → ℕ), FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Fin N → Bool, (C.wires (List.ofFn x)).getD (o 0) false = f0 ∧ ...` | tt-multi | inline enum (mm2), inline expr (mm2; mm3 with 18 inputs, 9 outputs) |

Also built: a formula with `^^`, `true`, `false` and `!` in `expr` mode. Five of these files were then judged by
the project's own checker (`--real`, table under Measurements): all ACCEPTED.

Written by the emitter but NOT built here:
* `tt-multi` with `Monotone2` instead of `FanInTwo` (same code path, other basis lemma);
* the helper namespace under `import Mathlib` (all of it). Every inline build above imports `PEqualNP.Defs` only;
  the helper proofs use `simp`, whose lemma set grows with the imports. If the desk's skeleton imports all of
  Mathlib, run leancheck on the assembled file before sending, or keep `import PEqualNP.Defs` alone (the accepted
  L_meta_19034 did). The direct style was built both ways.

## leancheck

Lint, mirroring `tools/pnp.sh check` and `.github/scripts/outside-guard.mjs` of pequalnp-proofs and join.txt:
size 1..524288 bytes; UTF-8, no NUL, control or invisible characters; import lines first and only `Mathlib[.x]`
or `--allow-import` modules (default `PEqualNP.Defs`); the full forbidden-word list (double quote, `#` commands,
`native`, `sorry`, `macro`, `syntax`, `notation`, `elab`, `set_option` other than the four limits as
`set_option <limit> <n> in`, `@[` other than `@[simp]`/`@[local simp]`, a name directly before `%`, ...), in code
and comments; at least one theorem; the own-namespace rule; the theorem carries the statement file verbatim.
Numerals: a run of 21+ digit characters or a numeral of more than 20 hex digits is an ERROR outside the theorem
statement and a warning inside it (`--numerals warn` downgrades it; the accepted L_meta_19034 and L_meta_19358
do have such numerals inside definitions and lists, so the real rule is narrower than this lint).

Build: the file is copied to `$PNP_LEAN_SANDBOX/lean/PEqualNP/Outside/<M>.lean` (default sandbox:
`toolkit/.cache/proofs-sandbox`, a separate clone of pequalnp-proofs; `PEqualNP.Defs` is built there once) and built with
`bin/pnprun -c 2 -m 10 -t 2400 -- lake build PEqualNP.Outside.<M>`, `LEAN_NUM_THREADS=2`,
`LAKE_ARTIFACT_CACHE=false`. One build at a time (a lock file). The run is killed and reported as "cannot judge"
if lake starts to fetch anything or to compile Mathlib. A module already on main is built as `<M>_lc`.
Then `#print axioms` (in a separate throwaway file) must show only propext, Classical.choice, Quot.sound.
Output: `LINT ok|FAIL`, `BUILD ok|FAIL`, wall seconds, peak resident memory of the largest process, `PASS`/`FAIL`.
Logs: `runs/ckt2lean/leancheck_<M>.log`.

`--real` (with `--statement-file`) additionally runs the project's own checker from the sandbox copy:
`node tools/check-lean.mjs <file> <statement> check`. It builds its verifier (`checklemma`) once, re-checks in the
kernel every declaration the theorem rests on (the 1717 constants of `PEqualNP.Defs` included) on top of all of
Mathlib, checks the axioms and compares the statement term. Its fixed cost here: about 50 to 70 s and 7 GB
resident (all of Mathlib mapped), whatever the proof. `--in-slot` lets one `pnprun` slot cover the build, the
axioms and the real check:  `bin/pnprun -c 1 -m 10 -t 2400 -- bin/leancheck --in-slot --real OUT.lean --statement-file STMT.txt`.
leancheck always forces a real build (it deletes the module's old build output first) and removes its copy of
the file from the sandbox when it ends.

## Measurements

All on one Apple M5 Max machine, Lean 4.36.0, the pinned Mathlib, 2026-11-27. "real" is lake's own wall time for
`lake build PEqualNP.Outside.<M>` (import loading included, about 2 s; waiting for a slot excluded), "cpu" is
user + sys of the same, "RSS" is the peak resident size of the largest process. Rows marked (2) were run with
`-c 2` while the machine was fairly quiet; rows marked (1) with `-c 1` while it was saturated and swapping, where
real time is inflated and RSS deflated (mapped .olean pages get evicted), so compare cpu there. Every row
ended `PASS` (lint ok, build ok, axioms within propext / Classical.choice / Quot.sound) unless it says otherwise.

| what | statement | circuit | style | real s | cpu s | RSS GB |
|---|---|---|---|---|---|---|
| a. round trip 32x32 | L-meta-19034 (FanInTwo, ≤ 207) | seeds/cand32_207.ckt, 206 gates | inline, points (2) | 7.1 | n/a | 2.55 |
| a. same | same | same | inline, rows (1) | 25.7 | 11.8 | 2.53 |
| a. same | same | same | inline, points (1) | 15.2 | n/a | 2.55 |
| the accepted L_meta_19034.lean itself | | 206 gates | their flat-list template (2) | 6.7 | 8.8 | 2.61 |
| 32x32 | L-meta-20578 (≤ 180) | 180 gates (from L_meta_20578) | inline, points (2) | 6.2 | 8.1 | 2.54 |
| 32x32 | same | same | lib, Defs + PromiseColTree (2) | 4.3 | 5.1 | 2.43 |
| the accepted L_meta_20578.lean itself | | 180 gates | lib + `import Mathlib` (2) | 34.1 | 23.4 | 5.48 |
| b. crown7 | RepSizeAtMost (u ≠ v) 23 (L-meta-19546) | 23 gates, from kn7_16 via --from-kn | direct (2) | 9.2 | n/a | 2.93 |
| b. same | same | same | direct + `import Mathlib` (2) | 37.6 | n/a | 5.96 |
| b. same | same | same | inline, points (2) | 5.2 | n/a | 2.44 |
| b. crown4 | RepSizeAtMost (u ≠ v) 11 | 11 gates, from kn4_7 | direct (2) | 2.6 | n/a | 2.41 |
| crown4, IsAO2 | RepSize2AtMost (u ≠ v) 11 | same | direct (2) / inline (2) | 4.6 / 5.9 | 5.5 / 7.6 | 2.42 / 2.43 |
| c. cyc5, 32 points | ∃ C, FanInTwo ... ∀ x, C.eval (List.ofFn x) = formula | 7 gates | inline, enum (2) | 3.6 | n/a | 2.43 |
| c. cyc5 | same with Monotone2 | 7 gates | inline, enum (2) | 3.0 | n/a | 2.43 |
| c. cyc5 | HasCircuitSize 5 (fun x => formula) 7 | 7 gates | inline, enum / expr (2) | 3.3 / 3.7 | n/a | 2.44 |
| c. cyc5 | ... = (fun x => formula) x | 7 gates | inline, enum / expr (2) | 3.8 / 4.5 | n/a | 2.43 |
| NOT, copy, constant gates | ... = (!(x 0 && x 1) || x 2) | 6 gates | inline, enum / expr (2) | 4.5 / 4.9 | n/a | 2.44 |
| c. mm2, 4 outputs, 256 points | ∃ (C) (o : Fin 4 → ℕ), FanInTwo ... (o j) ... | 12 gates | inline, enum / expr (2) | 5.8 / 4.8 | 7.4 / 6.9 | 2.44 |
| c. mm3, 9 outputs, 2^18 points | same shape, Fin 18, bound 45 | 45 gates (schoolbook) | inline, expr (2) | 5.5 | 7.9 | 2.48 |
| d. 128x128 | L-meta-19035 (≤ 2046) | seeds/cand128_2046.ckt, 2023 gates | inline, points (2) | 22.9 | 26.1 | 4.55 |
| d. 128x128 | bound 1500 | 1500 gates (from L_meta_19358) | inline, points (2) | 19.9 | 22.8 | 4.14 |
| d. 128x128 | same | same | lib, Defs + PromiseColTree (2) | 9.1 | 9.9 | 3.15 |
| the accepted L_meta_19358.lean itself | | 1500 gates | lib (2) | 11.1 | 12.1 | 3.30 |
| the accepted L_meta_19035.lean itself | | 2023 gates | their flat-list template (2) | did not finish | | killed by pnprun at 10.6 GB (limit 10) |

Later runs, `-c 1`, machine saturated (all 12 slots held, swap nearly full). "footprint" is the peak anonymous
memory of the lean process (sampled; mapped .olean files not counted), the steadier memory figure:

| what | circuit | style | real s | cpu s | RSS GB | footprint GB |
|---|---|---|---|---|---|---|
| d. 128x128, L-meta-19035 statement | 2023 gates | inline, rows (1) | 27.1 | 21.6 | 3.82 | 1.78 |
| enum scaling: cyc14 (14 inputs, 16384 points, a 14-term formula) | 27 gates | inline, enum (1) | 16.8 | 13.1 | 3.13 | 1.09 |
| crown3 as 3 AND + 2 OR + 1 NOT, `∃ C, FanInTwo ... Represents (u ≠ v)` | 6 gates | direct (1) | 18.4 | 9.3 | 2.36 | 0.32 |
| c. cyc5, FanInTwo ∃-form (final emitter) | 7 gates | inline, enum (1) | 7.8 | 8.1 | 2.43 | 0.38 |
| c. mm2, 4 outputs (final emitter) | 12 gates | inline, enum (1) | 6.9 | 7.6 | 2.44 | 0.39 |
| a. 32x32, L-meta-19034 statement (final emitter) | 206 gates | inline, rows (1) | 7.5 | 8.7 | 2.53 | 0.47 |
| c. mm3, 9 outputs, 2^18 points (final emitter) | 45 gates | inline, expr (1) | 7.5 | 8.9 | 2.48 | 0.43 |
| c. cyc5, Monotone2 ∃-form (final emitter) | 7 gates | inline, enum (1) | 8.1 | 7.9 | 2.43 | 0.38 |
| d. 128x128, L-meta-19035 statement, second run | 2023 gates | inline, rows (1) | 25.3 | 24.5 | 3.82 | 1.78 |
| d. 128x128, bound 1500 | 1500 gates | inline, rows (1) | 16.9 | 18.6 | 3.43 | 1.39 |
| formula with `^^`, `true`, `false`, `!` on 4 inputs | 6 gates (2 NOT) | inline, expr (1) | 8.0 | 7.9 | 2.43 | 0.37 |
| crown3 with a NOT gate, FanInTwo ∃-form | 6 gates | inline, points (1) | 7.3 | 7.9 | 2.43 | 0.38 |

The project's own checker, `leancheck --real` (`node tools/check-lean.mjs` of the sandbox copy, kind `check`):

| file | verdict | whole check, wall s | verifier RSS GB |
|---|---|---|---|
| crown7 23 gates, direct, statement of L-meta-19546 | ACCEPTED, axioms [propext, Quot.sound], 1717 constants re-checked | 69.2 | 7.07 |
| 32x32 206 gates, inline rows, statement of L-meta-19034 | ACCEPTED, axioms [propext, Quot.sound, Classical.choice], 1876 constants re-checked | 49.0 | 7.39 |
| mm3: 18 inputs, 9 outputs, 45 gates, inline expr (statement written to the L-meta-18919 description) | ACCEPTED, 1925 constants re-checked | 50.2 | 7.12 |
| cyc5, `Monotone2` ∃-form, 7 gates, inline enum | ACCEPTED, 1870 constants re-checked | 51.4 | 7.27 |
| 128x128, 2023 gates, inline rows, statement of L-meta-19035 | ACCEPTED, 1904 constants re-checked | 74.1 | 7.27 |

The verifier's fixed cost is about 50 s and 7.1 to 7.4 GB resident on that machine (all of Mathlib mapped); the
2023-gate proof adds about 25 s to it and nothing visible to its resident size.

Enumeration (`--tt-proof enum`) costs kernel work and kernel memory per point: about 10 s of cpu and 0.8 GB of
footprint for 16384 points of a 14-term formula (cyc14 above, baseline subtracted). It is linear in points x
formula size, so 2^18 points and nine outputs (L-meta-18919, the 3x3 matrix product) would need minutes per
output and several GB each: NOT viable. That unit must use `--tt-proof expr` (automatic when the right-hand sides
are formulas): the whole 18-input, 9-output, 45-gate proof builds in 5.5 s real / 7.9 s cpu / 2.48 GB resident.
ckt2lean refuses to fall back to enumeration at 16 inputs or more unless `--tt-proof enum` is given.

The times without a cpu figure in the first table are the wall time of the whole `pnprun` call, taken before
cpu was recorded; nothing was waiting for a slot then.


Reading of the numbers:

* The flat-list template of L_meta_19034/19035 walks a list for every wire read, so its kernel work and memory grow
  with gates x wires: fine at 206 gates, over 10 GB at 2023 gates here. The tree store (inline and lib) is the
  one to use at 128x128: 1500 to 2023 gates cost 10 to 25 s and 3 to 4.6 GB.
* For a 128x128 row-list statement the closed-form target (`rows`, the default for that statement shape) saves
  a little over the point-by-point check (`points`): 18.6 against 22.8 s of cpu at 1500 gates, measured under
  different load. The lib style is about twice as fast as inline at this size (9.9 s of cpu at 1500 gates): a
  profile of the 1500-gate inline file shows 8.9 s of kernel checking (5.7 s for the simulation itself, 0.65 to
  0.8 s for each of the four small checks on the gate list), 1.7 s of import, the rest elaborating the 400-line
  helper block. Merging the four small checks into one would save about 2 s; not done.
* Kernel memory of the inline proof (footprint): 0.4 GB baseline, 1.39 GB at 1500 gates, 1.78 GB at 2023 gates on
  16384-bit columns, so roughly 0.7 MB a gate.
* `import Mathlib` alone costs about 25 to 30 s and 3 GB of resident memory. The emitter never writes it.
* Baseline with `import PEqualNP.Defs` and a trivial proof: about 2.4 GB resident, 2 to 3 s.
* The project's verifier re-checks every declaration in the kernel a second time, so the real check costs roughly
  twice the kernel part of these times on top of its fixed start-up. All of the above stay far inside 20 minutes.


## Limitations and notes

* Statement shapes are recognised by text. Anything else needs `--kind`, and a truth-table right-hand side
  that is not a plain formula falls back to enumeration (fine to about n = 13; see the 2^18 measurement).
* `tt-multi` expects `∀ x : Fin N → Bool, (C.wires (List.ofFn x)).getD (o 0) false = f0 ∧ ... ∧ ... (o K-1) ... = fK-1`
  with the outputs in order. The exact text of L-meta-18919 was not available here; the test statement was
  written to that description.
* The sandbox must exist: `git clone <repo> toolkit/.cache/proofs-sandbox` (or `cp -Rc` of a checkout that already
  has Mathlib built; set `PNP_LEAN_SANDBOX` to use another place), then `lake exe cache get` and one
  `lake build PEqualNP.Defs` in its `lean/` (58 s on the test machine). The repo whose `Outside/` is checked for name
  clashes is the parent of `toolkit/` (override: `PNP_LEAN_REPO`).
* leancheck reads peak memory with `/usr/bin/time -l` (BSD/macOS flag); on Linux that column needs GNU time `-v`
  and is untested.
