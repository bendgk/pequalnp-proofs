# What is already known

Check here before you prove a unit, then search further (`AGENTS.md`, section 2). Add what you find.

Labels: **cited** (source opened by the agent who wrote the line), **snippet** (seen only as a summary or abstract),
**quoted** (read only as quoted by another source). "Unrefereed" means no peer review was found. Fleet row ids refer
to the record at commit 72b6cd2e8 (27 Nov 2026).

## Claimed in November 2026: read these first

| Result | Where | Status |
|---|---|---|
| VP != VNP over every field | Anthropic, `github.com/anthropics/formal-math` (`vp-vnp/`), 23 Nov 2026 | Lean, replayed by several outside parties against the challenge statement; no human referee found (snippet) |
| VP != VNP; VF != VBP != VP != VNP; superpolynomial exact arithmetic circuit bounds for the permanent (char. != 2) | OpenAI, `github.com/openai/math` (`lean/OAI/Computability/VPVNP/Separation.lean`: `vp_ne_vnp`, `corollary12`), 23-24 Nov 2026 | Lean; statements read, not rebuilt; no outside replay found (cited) |
| Border determinantal complexity of perm_m >= m^3 / (5529600 e) for m >= 1408 over C; smooth forms (r-1)(d-1)/(4e) | OpenAI manuscript in `github.com/openai/math`, dated 24 Sep 2026, first commit 6 Oct 2026; Lean `permanent_cubic_lower_bounds`, `smooth_initial_form_lower_bound` | Lean statements read, not compiled (cited) |
| B2 circuits for affine dispersers: size >= 4n - O(log n) | Mishra, Santhanam, ECCC TR26-260 (rev. 1, 3 Nov 2026) | Unrefereed; formalised in `cslib-community/cslib-frontier` as 4n - 10d, later 4n - 9d (snippet) |
| Random k-CNFs need polynomial-calculus degree > n/2 - 4n/sqrt(k) over every field; first superpolynomial bound for depth-2 AC0[p]-Frege | Conneryd, arXiv 2610.40397 (29 Oct 2026) | Unrefereed (cited). Depth 3 is called "the most pressing open problem" |
| Superlinear B2 bound for element distinctness, n (log n)^sigma | Third-party Lean corollary, `github.com/rille111/matmul-9-4-listdistinct` (25 Nov 2026), of a lemma in OpenAI's matrix-multiplication manuscript | README and statement read, not rebuilt; sigma not explicit (snippet). **Check this before any linear-constant B2 work** |

The tracker at `kingy.ai/blog/p-vs-np-race-tracker/` lists claims as they appear (read through a summary; it marks
nothing refereed). Use it as a pointer, not a source.

## Fleet rows that restate published results

| Fleet row | Published source | Relation |
|---|---|---|
| L-pcx-036 (dag-like Res(+), bit PHP, constant 32768, l >= 32) | Braun, arXiv 2609.23015 (19 Sep 2026); its own Lean at `github.com/kbr-/math-research` | Same theorem, same constant (cited) |
| L-pcx-022, 027, 032, 033, 034, 038, 041 | Braun, arXiv 2609.23015 | Re-formalised (cited) |
| L-pcx-042, 044, 017, 048, 053 | Pang, arXiv 2610.00837 (30 Sep 2026), Thm 1.1 at p = 2, Lemma 4.1, Thm 7.2(d) | Same or weaker; 7.2(d) has exp(Omega(N)) (cited) |
| L-pcx-036 vs Pang 7.2(e) | | Weaker than Pang for the same formula (cited) |
| L-pcx-072 | Itsykson, Podolskii, Shekhovtsov, CCC 2026 | The quadratic bound (cited) |
| L-pcx-054 (Res(k,+)) | Pang's argument with degree-k inputs | A variant, not new (argued) |
| L-gct-024 (smooth forms, constant 11) | Sheshadri, arXiv 2606.15970 (14 Jun 2026), constant 4e = 10.87; OpenAI's polar section | Weaker: 4e rounded up to 11 (cited) |
| L-gct-045 (power sums) | Sheshadri, arXiv 2606.11090, 2606.13628 (Lean, constant 4e) | Weaker (cited) |
| L-gct-056, 074 (border dc(perm_m) not O(m^2)) | OpenAI cubic theorem | Weaker (cited) |
| L-gct-057 | OpenAI smooth-projection proposition | Weaker (cited) |
| L-gct-027 (conditional cubic) | OpenAI's proof skeleton and parameters | Same skeleton (cited) |
| L-gct-025, 026, carried as conjectures | OpenAI Lean | **Theorems with public Lean proofs since 6 Oct 2026** (cited) |
| L-gct-009, 010 | Mignon-Ressayre 2004; Landsberg-Manivel-Ressayre 2013 | Labelled as such by the fleet |
| L-meta-12318, 11096 (line N1) | Jukna 2012, Sect. 1.8, Lemma 1.32, Cor. 1.36, Research Problems 1.37-1.38; Jukna 2013, Strong Magnification Lemma (p. 17) and p. 5 ("this is 'bad news'") | The Magnification Lemma with constant 4 (cited) |
| Any graph with a cheap rule | Jukna 2013, Remark 1.18 | Capped at (4 + o(1))n (cited) |
| L-meta-18925 (NOT removal, 3n - 6) | Wegener 1987, Thm 6.13.5 (k = 2), Cor. 13.2, Ch. 3 Ex. 25; Dunne 1988, Lemma 3.32, Thm 3.21 | Corollary of known (cited) |
| "One NOT saves 2n - 5" rows | Berkowitz 1982 pseudo-complement | (argued) |
| L-meta-19062 (crown ceiling) | Adleman 1976 grid; Bloniarz 1979 (MIT/LCS/TR-238), Table 5.1 | Known; weaker than print at n = 128 (cited) |
| L-meta-18487 (crown floor) | Wegener 1987, Thm 6.3.1(ii), with the fleet's L-meta-18508, for n >= 17 | Corollary for n >= 17; the fleet is 1-2 gates ahead for 7 <= n <= 16 (cited) |
| Crown rows in general | crown_n = n + K(n), K = monotone size of threshold-2 (L-meta-18508). Truth: 2n + Theta(sqrt n): Sergeev 2020/2021 (lower), Krapivin, Przybocki, Subercaseaux, arXiv 2603.28954v2, Thm 6 (upper) | (cited) |
| L-meta-25446 (encoder floor) | Chashkin 1994 (as stated in Sergeev, arXiv 2603.24319) | Known up to O(k) (quoted) |
| Conversion overhead 2*2^k + k*2^ceil(k/2) | Jukna 2013, Lemma 1.17: 2*2^k + 8*2^(k/2) | Weaker for k > 8 (cited) |
| Note 1, part (d) | Jukna 2012, p. 43 | Known (cited) |
| Note 1, "unidentified" 4n - 4 for parity | Red'kin 1973 (Wegener 1987, p. 126) | Known (quoted) |

## Where the fleet appears to be ahead ("not found", not "new")

- Crown floor for 7 <= n <= 16, and exact K(n) for small n.
- Read literally, Jukna's Research Problem 1.38 (explicit n x n graph needing cn gates, c > 2) at c = 3, from
  crown_n >= 3n + log n - 4. Cannot pass 3 + o(1).
- L-gct-064 / 070, (2m^2 - 10m + 11)/3 exact and border: the best explicit bound found for 20 <= m <= 10,020,669
  (the cubic bound only overtakes it at m = 10,020,670). Capped by the fleet's own L-gct-044 at (m-1)^2 + 1.
- L-gct-015, m^2/2 + 1 exact, for 5 <= m <= 19.
- Conjecture L-meta-19158 (a NOT gate saves at most 2n - 5): not found in print.

## Ceilings: what a method provably cannot do

| Method | Ceiling | Source |
|---|---|---|
| Star complexity of graphs with a cheap rule | (4 + o(1))n | Jukna 2013, Remark 1.18 |
| Characteristic-cycle counting for border dc | about 144 m^3 for perm_m | Sheshadri, arXiv 2606.15970 v2, Thm 7.7 (unrefereed) |
| Subspace method for dc(perm_m) | (m-1)^2 + 1 | fleet L-gct-044 |
| Hessian rank | m^2/2 + O(1) | standard |
| Gate elimination, one substitution | 5 gates per substitution; 11n for gates-plus-inputs measures | Golovnev, Hirsch, Knop, Kulikov, ECCC TR16-119 |
| Degree method for Res(+) | Cannot separate Res(+) from constant-degree PC (a degree-d refutation is one at every D >= d) | fleet pcx audit, `degree_hypothesis_fails` (checked) |
| Random k-CNFs for AC0[p]-Frege | Depth 2 only | Conneryd, arXiv 2610.40397 |
| Natural properties of graphs vs the N1 threshold | None exists if polynomially secure PRGs exist | `REDTEAM.md`, finding B1 (argued) |

## Classic references

- S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Springer 2012.
- S. Jukna, "Computational Complexity of Graphs", 2013 survey.
- I. Wegener, *The Complexity of Boolean Functions*, Wiley-Teubner 1987.
- P. E. Dunne, *The Complexity of Boolean Networks*, 1988.
- P. Buergisser, survey on VP vs VNP, arXiv 2406.06217.
- Sergeev, survey of exact and asymptotic circuit bounds, arXiv 2603.24319.
