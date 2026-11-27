# Targets (pequalnp.com units these tools were built for, as of 2026-11-27). Specs are in specs/, bases per FORMAT.md.
Unit numbers and "accepted on main" refer to the pequalnp-proofs repository at that date; check the live site for
the current state before starting work.
A "search" unit wants a WITNESS circuit with at most the stated number of gates (every gate counts, NOT included).
An exhaustive "no such circuit" answer is also valuable (it tells them to stop / gives a lower bound).

| spec | basis | wanted size | known | notes |
|---|---|---|---|---|
| specs/cand32.spec  (32x32 graph, 64 inputs, 1024 points) | aon | <= 150 | **180 accepted on main** (L_meta_20578; seeds/cand32_180_*.ckt), also 190, 206 | unit L-meta-20580. Lower bound only ~63. |
| specs/cand128.spec (128x128 graph, 256 inputs, 16384 points) | aon | <= 1350, 900, 800, 700 (four units) | **1500 accepted on main** (L_meta_19358; seeds/cand128_1500_*.ckt), also 1887, 2023 | units L-meta-20583/85/86/87 |
| specs/crown7.spec (7x7, u!=v) | ao | <= 22 | checked: >= 22 (L_meta_18242) and <= 23 (L_meta_19546) | L-meta-18259. crown_n = n + K(n) by a proven link, so equivalent to kn7 <= 15 |
| specs/kn7.spec (7 wires; 0 on 1-hot, 1 on 2-hot points; = monotone threshold-2) | ao | <= 15 | **K(7) = 16 (SAT-exhaustive; rests on elimination clauses, see docs/RESULTS.md)** | No 15-gate circuit found by exhaustive SAT, so unit L-meta-18259 looks false (crown7 = 23). See docs/RESULTS.md for what the claim rests on |
| specs/kn6.spec | ao | <= 12 | **K(6) = 13 (SAT-exhaustive, also without elimination clauses)** | crown6 = 19; see docs/RESULTS.md |
| specs/match3.spec (perfect matching 3x3, 9 inputs, full tt) | ao | <= 13 | ? | L-meta-17390 |
| specs/match3.spec | aon | <= 13, 12, 11 | ? | L-meta-17387/88/89 |
| specs/mm3.spec (3x3 Boolean matrix product, 18 in, 9 out) | aon | <= 44 | 45 (naive monotone: 27 AND + 18 OR; monotone optimum is 45) | L-meta-18919; needs NOT gates to beat 45 |
| specs/cyc7.spec (7-cycle edge function) | aon | 10 gates | exact size is n+ceil(n/2)-1 = 10 | L-meta-18791 wants a 10-gate circuit with a special shape; plain 10-gate witnesses are still useful |

Graph specs ("Represents"): the circuit only has to be right on the n*m inputs with exactly one left wire u and one right
wire n+v on. So every wire is an n x m 0/1 matrix; input u = all-ones row u, input n+v = all-ones column v; AND/OR/NOT are
intersection/union/complement of matrices; the target is the adjacency matrix. Huge don't-care space: exploit it.

## Background facts (Lean-checked rows on main, or earlier runs)
- K(3) = 4, K(4) = 7, K(5) = 10 (kn5 UNSAT at 9 took 99 s in single-thread Python, SAT at 10). K(n+1) >= K(n) + 2. K(n) <= 3n - 5.
- crown_n = n + K(n) (L_meta_18508).
- Candidate graphs: hypothesis A = B o C, Boolean product of two sparse pseudo-random n x n graphs with about d = 2^((k-1)/2)
  ones per row (d = 4 for 32x32, d = 8 for 128x128); the checked 2046 is nnz(B)+nnz(C)-2. Counting floor estimate: ~920 gates
  (128) and ~115 (32), so <= 700 / <= 800 are probably impossible and <= 900 marginal; <= 1350 and <= 150 are the live ones.
