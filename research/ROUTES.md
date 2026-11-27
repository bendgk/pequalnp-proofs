# Routes

A route is a line of attack with a stated goal. For each: the chain to the goal, the ceiling of the methods in use,
the first open rung (the smallest statement that would be new), and the next concrete step. Before you take a
unit, find its route here. If it has none, ask whether it should exist.

Keep this file current. When you learn something that moves a route, edit it, with a confidence label (see
`AGENTS.md`) and a date.

Status words: **live** (open rung reachable, worth hours), **capped** (known ceiling below the goal; warm-ups only),
**replication** (current rows restate published work), **parked** (open, nobody on it).

---

## R1. Graph complexity, line N1 (the main bet). Status: capped

- **Goal.** An explicit n x n graph (n = 2^k) needing more than 4n + n/d gates gives P != NP (L-meta-12318, with
  the conversion L-meta-11096; composed without hypotheses in L-meta-16079, 16080).
- **Chain, honestly read.** By the conversion row, "above the threshold" is the same as "the adjacency function
  on 2k bits needs about 2^k/(2d) gates": an exponential circuit lower bound for an NP function. P != NP needs only a
  superpolynomial one. The route asks for something harder than its goal (checked: `cost_hypothesis_is_an_
  exponential_lower_bound`, red-team vacuity audit).
- **Known.** This is Jukna's Magnification Lemma (2012, Research Problem 1.38), with his "bad news" remark.
- **Ceilings.** Graphs with a cheap rule: (4 + o(1))n. Natural properties cannot certify the threshold if
  polynomially secure PRGs exist (argued, `REDTEAM.md` B1).
- **Triggers that cannot fire.** At 8 x 8 the conversion overhead is 48 and every graph has a 45-gate circuit
  (computed on 20,006 graphs). Counting guarantees a graph above 4n only from n = 43, where a certificate would be
  a lower bound above 172 gates; exhaustive certificates with NOT gates stall at 5-9 gates. Over all 4 x 4 graphs
  the maximum is 11 gates.
- **What would be worth doing instead.**
  - **AND-count currency (live).** Count AND gates only, ORs free (Cavalar, Oliveira, arXiv 2503.14117). The
    conversion loses nothing, there is no 4n baseline, and And(A_k) >= k^omega(1) for an NP family already gives
    NP not in P/poly. Crown costs exactly log2 n. Proved by hand: ceil(log2 C0) <= And <= C0 - 1; And(u < v) >=
    log2 N + 1 for N = 2^n, n >= 3, one above the only printed explicit bound. **First open rung:** an explicit
    family with And >= (1 + eps) log2 N. Exact And tables: `toolkit/tables/and_{3,4,5}.json`.
  - **Shrink the encoders.** A recursive encoder gives 70 / 278 gates a side at k = 5 / 7 against 104 / 368 in
    L-meta-9023 (computed). Useful only if line N1 continues.

## R2. Monotone threshold-2 and the crown family. Status: capped (mostly known)

- crown_n = n + K(n), K the monotone size of threshold-2 (L-meta-18508). The truth is 2n + Theta(sqrt n).
- **Computed with the toolkit:** K(2..7) = 1, 4, 7, 10, 13, 16. K(7) = 16 means unit L-meta-18259 ("crown7 <= 22")
  is false: crown7 = 23. Caveat: the K(7) search used elimination clauses justified by checked rows; an independent
  run without them was pending at the time of writing. Next: K(8) in {18, 19}; K(8) = 19 would give K(9) = 21.
- Worth hours only as a closed-form all-n statement or as a benchmark for the toolkit.

## R3. NOT gates (line N2). Status: capped

- NOT gates cost at most a factor and O(n) on these inputs (Wegener 1987, Dunne 1988).
- Conjecture L-meta-19158 (one NOT saves at most 2n - 5): holds on every 3 x 3 graph (largest saving 1) and every
  4 x 4 graph (largest saving 3, reached by 12 classes), computed from exact tables (`toolkit/tables/star_{3,4}.json`).
  5 x 5 in progress.
- L-meta-19164 is recorded weaker than its own proof (n + m + 8s - 1 built, n + m + 2(s+1)^2 recorded). Fix that
  first: as recorded, the converse L-meta-19302 never excludes a size L-meta-19361 does not already exclude.
- The "one NOT saves a growing number of gates" rows are the one-hot identity on promise inputs (checked,
  `NotSaving.lean` in the vacuity audit).

## R4. Gate elimination on the standard measure. Status: live (narrow)

- Records: B2 (full binary basis) 4n - O(log n) (Mishra, Santhanam, Nov 2026, unrefereed, in Lean elsewhere).
  U2 (De Morgan) 5n - o(n) (Iwama, Morizumi 2002), 24 years old.
- **Check first:** the claimed superlinear B2 bound for element distinctness (`LITERATURE.md`). If it stands,
  linear-constant records stop mattering as records.
- **First open rungs:** U2 above 5n (needs a new idea; rough odds 1 in 10 for a bounded effort); B2 above 4n
  (needs a new elimination move; under 1 in 20).
- The fleet's `Defs/BinaryCircuit.lean` already expresses the standard measure; its B2 rows stop at 1.5n. A Lean
  proof of Schnorr's 2n bound on the fleet's own `HasBinarySize` was compiled by a red-team agent (no news value,
  shows the machinery works).

## R5. VP != VNP to Boolean circuits. Status: live (new as of 23 Nov 2026)

- VP != VNP is claimed proved, in Lean, twice (`LITERATURE.md`). The question for this fleet is what it gives for
  Boolean circuits.
- **Where it breaks.** Over F_2, the coefficient of a squarefree transversal monomial in f*g splits over disjoint
  slot sets, so a product gate is rank one across a cut. Modulo x^2 = x this fails. Anthropic's paper (section 2.5)
  names the two steps that look inside the circuit (lem_balanced, lem_lowdeg) as the ones that fail, because a
  Boolean circuit may compute any g = HC + sum (x_i^2 - x_i) h_i.
- **The functional version of OpenAI's measure gives nothing superpolynomial:** for every graph G a linear-size
  formula has exactly the slot tensor of the state sum (identity checked by program on five cases).
- **What crosses.** Truth-table tensors with one bit leg per input give n (log n)^sigma for bit networks; the
  element-distinctness corollary above.
- **First open rung, N(t):** every circuit over F_2 of formal degree at most d + t that agrees with the r x r grid
  state sum on {0,1}^N has size q^(Omega(sqrt r)). N(0) follows from the repository's own lemmas; N(c sqrt r) is
  argued; any proof through this measure fails once t >= 2d/k at size q^(O(k)).
- **Also:** Anthropic's contracting branch gives N^(1+delta) for an explicit counting function if some field is
  contracting (argued). A cheap Lean unit: OpenAI's Euclidean flats imply Anthropic's flat case.
- **Barriers.** A Boolean version must be defined on functions, use more than the transversal slot tensor, not be a
  wire-length inequality on bit-leg tensors, and stay non-constructive or non-large.
- **Step 0.** Replay one of the two Lean proofs and restate its main theorem on the fleet's definitions.

## R6. Permanent versus determinant (gct). Status: replication, with one live rung

- The fleet's headline rows are weaker forms of results with public Lean proofs since 6 Oct 2026 (`LITERATURE.md`).
  Two rows carried as conjectures are theorems.
- **Ceilings.** The cubic method stops near 144 m^3; subspaces at (m-1)^2 + 1; Hessian rank at m^2/2 + O(1).
- **First open rungs.** Border dc(perm_m) >= R m^3 by a method that can go further (needs a new method; every
  method the fleet has is too weak). Smaller and concrete: border dc(perm_m) >= (m-1)^2 + 1 over C; dc(perm_4) >= 10
  (known 9 <= dc(perm_4) <= 15).
- **Step 0.** Port `permanent_cubic_lower_bounds` and `corollary12` and restate them on the fleet's definitions.

## R7. Proof complexity (pcx). Status: replication, with two live rungs

- Every headline row restates Braun (arXiv 2609.23015) or Pang (arXiv 2610.00837). All 9 open pcx units were exact
  line counts for 4 or 5 pigeons.
- **First open rung A.** A polynomial-size CNF family with F_2 polynomial-calculus degree >= n/2 - o(n / log n).
  Through Pang's tradeoff this gives the first superpolynomial bound for depth-3 AC0[2]-Frege. Statement:
  `PcxAudit.TargetDegreeHalf` (type-checked on the fleet's definitions by a red-team agent). Low odds; specialists
  are on it. Certain and useful: formalise Conneryd's theorem and the depth-2 tradeoff (no machine-checked proof
  found).
- **First open rung B (the fleet's parked L-pcx-071).** Res(+) does not polynomially simulate constant-degree PC
  over F_2. The degree method cannot touch it. A new rung would be n^(2 + eps) lines for unrestricted Res(+) on such
  a family.
  - New test family (red team, 27 Nov): mod-4 flows (FT4). Constant width and PC degree; contains lifted Tseitin
    as an affine restriction, so it needs Omega(n^2) lines on tripled cubic expanders (via CCC 2026); not a lift in
    disguise (O(log n) communication; O(n) lines in Res over Z_4-linear equations). For this family L-pcx-071
    reads "Res(+) does not simulate resolution over Z_4-linear equations". Width, unsatisfiability and the closure
    lemmas are checked in Lean; the rest are paper proofs.
  - **Missing lemma:** joint surjectivity of a diagonal pencil of up to r quadratic forms on the cycle space, with
    amortised rank accounting. With it: rank Omega(n) on every 5-edge-connected expander, so tree-like 2^Omega(n),
    in a regime where communication arguments provably cannot work.
- **Rung C.** Res(lin) over the integers on a CNF (L-alg-005); a degree-size relation is false there.

## R8. Analytic side routes. Status: mixed

- **Newton polygon of fg + 1** (Koiran, Portier, Tavenas, Thomasse): sharp 2t + 2 in convex position / no doubling /
  two-term cancellation, examples for t >= 4 (one in Lean). General case open. Its VP vs VNP motivation is now moot.
- **Real roots of fg + 1:** binomials solved; R(t) >= max(3t - 2, 4t - 6) against the published 2t - 2 (four
  statements in Lean). Next: R(3) in {7, 8, 9}.
- **Partial-transpose rank over GF(2)** (Rossman, Zhu, arXiv 2512.01227): P(km) <= k^2 P(m), P(8) <= 28; exact P(4) = 7
  computed.
- **LP-dual certificates for the star model:** an integrality gap on the crown from n = 4; cannot certify crown
  values. Dead end, recorded so nobody repeats it.

---

## How to add a route

Write: goal; the chain to P vs NP (or to the stated goal) link by link, with row ids; what is known; ceilings of the
methods in use; the first open rung as a statement; the next concrete step; status. Label every claim.
