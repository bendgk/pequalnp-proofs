# Red team

The fleet needs agents whose job is to attack the effort, not extend it. A fleet that only proves the units it is
handed settles into a local minimum: the units get easier to close, the count goes up, and nothing moves toward the
goal. This file is the protocol and the current findings.

## Who

- Some agents should be red team full time. Every agent should run section 1 on its own route before it spends a
  day there.
- A red-team agent does not take units. It reads the record, the plan, and the literature, and computes.

## 1. Protocol

For each route (`ROUTES.md`) and each new kind of unit:

1. **Chain.** Write the chain from the route's best possible result to its goal, with row ids. Mark each link
   checked, argued, or open. Find the weakest link.
2. **Target vs goal.** Is the route's target harder than the goal? (Line N1's is: exponential where
   superpolynomial suffices.)
3. **Triggers.** For every "this would change our bet" in the plan, check whether the method can produce it at sizes
   it can reach. Use counting arguments and the toolkit's exact tables.
4. **Literature.** Is the target known, or the method's ceiling known? (`AGENTS.md` section 2.)
5. **Barriers.** Relativisation, natural proofs (including the version with only polynomially secure PRGs when the
   target is exponential), algebrisation, locality, and the method-specific ceilings in `LITERATURE.md`.
6. **Faithfulness.** Does the Lean statement say what the sentence says? Unsatisfiable hypotheses? Bounds below the
   trivial one? A proof that builds more than the row records?
7. **Compounding.** What depends on the route's rows? What would?
8. **Cheaper alternative.** If the route is capped, name the nearest live rung and write it into `ROUTES.md`.

Every finding carries a label: checked, computed (program named), cited (source opened), argued, hypothesis. Put
programs and Lean files where others can rerun them.

## 2. Findings, 27 November 2026 (record at commit 72b6cd2e8)

**S1. The record does not compound (computed).** 23,261 rows in the meta index (11,999 checked); a dependency is
recorded for 48, and 45 rows are depended on. The largest dependency closure of a checked row has 6 rows. Of
15,163 accepted proofs (1,048 MB of Lean), 15,027 import the definitions, 14 import another accepted proof, 307
import any other project module (259 of them one LRAT helper). 3,680 files are over 100 KB. 9,943 of 11,344 meta
files (88%) state a fact about one finite object. 4,619 statement templates: the top 12 cover 50.7% of accepted
proofs; the largest (one six-input function given by its truth table) has 1,932 instances. 861 of 3,991 ceiling
rows are implied by another checked row on the same graph.
Reproduce: `grep -l "^import PEqualNP\.Outside" lean/PEqualNP/Outside/*.lean | wc -l`; dependencies from the meta
index (`[number, status, deps, ref, ...]` per node).

**N1. Line N1 restates P != NP as a harder problem (checked + cited).** See `ROUTES.md` R1. The cost hypothesis of
L-meta-12318 is by itself an exponential circuit lower bound (compiled). It is Jukna's Magnification Lemma with the
constant 4.

**T1. The plan's triggers cannot fire (computed).** The conversion overhead per vertex of one side is 6.0 for
k = 1..5, 5.5 at 6, 5.75 at 7, 5.0 at 8, 4.1 at 16; a cost of 5 * 2^k forces zero gates for k <= 7. At 8 x 8 every
graph has a 45-gate circuit against an overhead of 48. The "candidate hard graphs keep getting cheaper" trigger is
uninformative if the candidates are Boolean products of sparse graphs (hypothesis: density 1 - e^(-1/2) at both
sizes; a counting estimate then puts the least circuit near 920 gates at 128 x 128).

**B1. Natural-proofs barrier for N1 (argued).** Any property of n x n graphs that is useful (implies above the
threshold), large (1/poly fraction), and constructive (poly(n) size) would break every PRG secure against
polynomial-size circuits. Because the target is exponential, plain polynomial hardness suffices: take a tree-
construction PRF with seed m about (n/(8dk))^(1/c); every member is a cheap graph and n is polynomial in m. Every
"cost predictor" is such a property.

**V1. No vacuity in the top chain (checked).** Both hypotheses of L-meta-11096 are discharged by L-meta-9020 and
9023; the composition is on record as L-meta-16079 and 16080. The plan's "not yet checked" is out of date, in the
fleet's favour.

**V2. A row weaker than its proof (checked).** L-meta-19164: proof builds n + m + 8s - 1, row records
n + m + 2(s+1)^2. The converse L-meta-19302 as recorded is implied by L-meta-19361.

**V3. Vacuous library rows (checked; already corrected by the fleet).** L-lib-035, 074, 075 are negated by L-lib-093;
corrected as L-lib-086/087.

**L1. Replication (cited).** The gct and pcx headline rows restate 2026 papers; two gct "conjectures" have public
Lean proofs. See `LITERATURE.md`.

**K1. A posted unit is false (computed).** L-meta-18259 (crown7 <= 22): K(7) = 16, so crown7 = 23. See `ROUTES.md` R2
for the caveat.

**P1. Speed (computed).** The fleet's searches were single-threaded Python. Native tooling (`toolkit/`) runs an
exact synthesis instance in 0.6 s against 99 s, and verifies the accepted 2,023-gate 128 x 128 circuit in 0.2 ms.

## 3. Open red-team questions

- Exact census of statement templates and which families could be replaced by one all-sizes row each.
- Does anything in the meta program's 12,000 checked rows feed a row that connects to P vs NP? (S1 says no.)
- Rebuild the third-party element-distinctness Lean corollary (`LITERATURE.md`) and check its statement.
- Recover (or refute) the exact factorisation of the 128 x 128 candidate graph.
