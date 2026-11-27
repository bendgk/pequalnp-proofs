# How an agent works on this attack

Read this before your first unit. `CONTRIBUTING.md` says what a proof file must look like. This file says how to
spend your hours so that the fleet gets smarter rather than only bigger.

The short version: **research before you prove, reuse before you write, build tooling once and share it, and
attack the record as hard as you attack the problem.**

## 1. The loop

Every unit, and every hour you spend without one, goes through these steps in order.

1. **Find out what is known.** Before you prove anything, look for it (section 2). A statement already in print or
   already in Lean elsewhere is not progress. Say so instead of re-proving it.
2. **Find out where it leads.** Read the route it belongs to in `research/ROUTES.md`. Know the route's ceiling (the
   best any known method can reach) and its first open rung. A unit that cannot move a route past its ceiling is a
   warm-up, and should be priced and spent as one.
3. **Use the toolkit.** Any search, check or table goes through `toolkit/` (section 3). If the tool you need does not
   exist, extend the toolkit. Do not write a private script that dies with your session.
4. **Reuse the record.** Build on checked rows instead of re-proving their helpers (section 4).
5. **Leave something behind.** A result, a refutation, a measured dead end, a citation, or a faster tool. Write it
   where the next agent will find it (section 6).
6. **Red-team.** Before you add to a line of work, ask whether the line can reach its goal at all (section 5).

## 2. Literature first, and deep research

The fleet has re-formalised published results without knowing it, and carried theorems with public Lean proofs as
open conjectures. In November 2026 it did not know that VP != VNP had been claimed proved and formalised in Lean.
Your training data probably ends before most of what matters here. Assume it does.

Before you prove a unit:

1. **Search.** arXiv (cs.CC, math.LO, cs.LO), ECCC, Google Scholar, and GitHub for Lean formalisations (search the
   statement's key objects, not only its name). Check `research/LITERATURE.md` first; it lists what the fleet has
   already found.
2. **Check the classics.** For Boolean circuit questions: Jukna, *Boolean Function Complexity* (2012) and
   "Computational Complexity of Graphs" (2013); Wegener, *The Complexity of Boolean Functions* (1987). For algebraic
   and proof-complexity questions: the surveys cited in `research/LITERATURE.md`.
3. **Open the source.** A title or an abstract is not enough to call something known or new. Read the theorem
   statement and its hypotheses. Record what you opened and what you only saw quoted.
4. **Decide, and record the decision.**
   - Already proved, same or stronger: do not re-prove it. Add it to `research/LITERATURE.md` with the citation and
     the fleet row id. Release the unit (`other` today; see `research/PROPOSALS.md` for the `already_known` reason
     the desk should add).
   - Proved elsewhere in Lean: say so. Port it as a library row the fleet can import, not as a fresh leaf.
   - Weaker than print: say so in your note. It may still be worth having as a warm-up, but nobody should call it a
     result.
   - Not found: say "not found in <the sources you opened>", never "new".
5. **Go deep when the unit is on a live route.** Spend real time: read the two or three most recent papers on the
   route, their open-problem sections, and the papers that cite them. Write what you learned into
   `research/ROUTES.md`. An hour of reading that moves a route's "first open rung" is worth more than a hundred
   fixed-instance rows.

Label every claim you write with how you know it: **checked** (in Lean, here), **computed** (by a program you name),
**cited** (source opened), **argued** (reasoning, not formalised), **hypothesis**.

## 3. Tooling: one fast, shared toolkit

Most of the fleet's search work has been single-threaded throwaway Python: count gates, try circuits, repeat. On
one laptop, native tooling made an exact search go from 99 s to 0.6 s, and checks a 2,023-gate circuit on 128 x 128
inputs in 0.2 ms. Agents should spend their time thinking, not waiting.

Rules:

1. **One toolkit.** All shared tooling lives in `toolkit/`. Read `toolkit/README.md`. Use what is there.
2. **Never rewrite. Extend, port, unify.** If a tool is missing a feature, add it to that tool. If two tools overlap,
   merge them. A new tool needs a reason the existing ones cannot be extended, written in its doc. We want one
   framework, not a thousand fragments.
3. **Languages.** Hot paths in C++20 or Rust, built with full optimisation for the native CPU. Dense, uniform kernels
   (score every pair of wires against a target, evaluate many circuits on all points) on the GPU: Metal on Apple
   machines, CUDA on NVIDIA. Python only for glue, file formats and the slow reference checker. For SAT use CaDiCaL
   or Kissat (through `python-sat` is fine); never write your own solver.
4. **GPU first, CPU always.** Prefer a GPU kernel when the machine has a GPU and the work is dense; measure the gain
   before you adopt it. Every GPU path keeps a portable CPU path behind the same interface, so an agent without a
   GPU loses speed, not function.
5. **Your machine, your port.** If you run on an OS, CPU or GPU the toolkit does not support yet, your first job is
   to add that backend behind the existing interface and make it fast. Decide yourself whether a GPU port pays on
   your hardware. `toolkit/PORTING.md` lists what exists and how to add a backend.
6. **Fast techniques that work here.** Bit-parallel truth tables (one bit per input point, 64 points per machine
   word). SAT encodings with strong symmetry breaking and with lemmas the fleet has already checked (restriction,
   gate elimination) added as clauses. Cube-and-conquer across all cores. Incremental evaluation in local search.
   Exact tables of all small cases, computed once and shared.
7. **Two checkers must agree.** Every result is verified by the fast native checker and by the slow reference
   checker before anyone relies on it. Every exhaustive (UNSAT) result keeps an audit log: which cubes, which added
   clauses, and where each clause was proved valid.
8. **Measure.** Every tool's doc gives its speed against the baseline it replaced, on named inputs, and its known
   limits.
9. **Share the machine.** Multi-threaded runs go through `toolkit/bin/pnprun` (core slots and a memory cap). Tools
   default to one thread unless told otherwise.
10. **Leave the table.** Every exhaustive answer goes into `toolkit/tables/` or `toolkit/found/` so nobody computes it
    twice.

## 4. Build on the record

Of 15,163 accepted proofs, 14 import another accepted proof. Of 23,261 rows in the meta index, 48 record a
dependency. Twelve statement templates cover half of all accepted proofs. The record grows, but it does not
compound.

1. **Import, don't re-prove.** A gap may list accepted outside modules as imports (see the header of
   `.github/workflows/authoritative.yml`). When your proof needs a fact the record already has, ask for that import:
   release with `missing_lemma` and name the row you need.
2. **Prove the general statement once.** When you see the same template for the third time, stop. Prove the family
   (all sizes, or all instances of a shape) as one row and let the instances follow from it.
3. **Lift helpers.** A helper lemma you needed in three proofs belongs in a library row. Propose it.
4. **Record dependencies.** When a row follows from others, say which, so the record can show what is load-bearing.
5. **Keep the strongest form.** Do not throw away a stronger bound your proof already built (one checked row did:
   its proof builds n + m + 8s - 1 and records n + m + 2(s+1)^2).

## 5. Red team

Some agents should spend all their time attacking the effort instead of extending it. Every agent should spend some.
`research/REDTEAM.md` has the protocol and the current findings. The questions to ask of any line of work:

1. **Can it reach the goal?** Write the chain from the line's best possible result to the stated goal. Find the
   weakest link. A line whose target is harder than the problem it is meant to solve is a trap.
2. **Can its own trigger fire?** If the plan says "evidence X would change our bet", check whether X is reachable by
   the method in use, at sizes the method can handle.
3. **Is it known?** (Section 2.)
4. **Is it behind a barrier?** Relativisation, natural proofs, algebrisation, locality, and the known ceilings of the
   method (`research/ROUTES.md` lists them per route).
5. **Is it vacuous or weaker than its proof?** Unsatisfiable hypotheses, bounds below the trivial one, statements
   weaker than the proof builds.
6. **Does it compound?** Does anything depend on it?

Write findings with their confidence labels. A refutation of a line is a result.

## 6. Where to write

| What | Where |
|---|---|
| What is known, with sources | `research/LITERATURE.md` |
| Routes: goal, chain, ceiling, first open rung, status | `research/ROUTES.md` |
| Red-team findings and protocol | `research/REDTEAM.md` |
| Changes the desk or checker would need | `research/PROPOSALS.md` |
| Tools, measured speeds, porting | `toolkit/` |
| Exact tables and verified witnesses | `toolkit/tables/`, `toolkit/found/` |

Research and tooling pull requests are separate from proof pull requests. A proof pull request still adds exactly
one file, as `CONTRIBUTING.md` says.
