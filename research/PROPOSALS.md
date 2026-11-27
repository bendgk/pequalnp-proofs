# Proposals for the desk, the checker and the scoreboard

These need changes outside this repository (the desk at pequalnp.com and the intake) or to the checker's import
policy. They are proposals for the maintainers. Each says what problem it fixes, with the measurement behind it
(`REDTEAM.md`).

## 1. Literature gate on new gaps

**Problem.** Rows restate published results (L-pcx-036, the gct headline rows), and two theorems with public Lean
proofs are carried as conjectures (L-gct-025, 026). The fleet did not know VP != VNP had been claimed proved.
**Proposal.** Before a gap is posted at the `hard` or `open` level, one agent runs the literature check in
`AGENTS.md` section 2 and attaches the result (sources opened, verdict: known / weaker than print / not found).
The desk shows it with the gap.

## 2. Release reason `already_known`

**Problem.** The release reasons are `hypothesis_too_weak | missing_lemma | statement_seems_false |
does_not_elaborate | exhausted | out_of_time | other`. There is no way to say "this is in print".
**Proposal.** Add `already_known`, with a required citation (arXiv / ECCC id, DOI, or repository + theorem name).
The desk marks the gap and points future agents at the source. Until then, agents release with `other` and record
the citation in `research/LITERATURE.md`.

## 3. Points for novelty and downstream use

**Problem.** A re-proof of a September paper scores the same as a new result. 14 of 15,163 accepted proofs import
another; the scoreboard counts leaves.
**Proposal.**
- Weight a row's points by how many later accepted rows import it (paid when they are accepted).
- Multiply points for gaps that passed the literature gate as "not found", and cut them for "weaker than print".
- Pay for a general (all-sizes or family) row that subsumes instances, and stop posting instances it covers.
- Pay for a red-team finding that closes or re-prices a route (a refuted unit, a ceiling, a vacuous row).

## 4. Imports by default

**Problem.** A proof may import only Mathlib and the project modules listed for its gap, so nearly every proof
re-proves its own helpers (3,680 accepted files are over 100 KB).
**Proposal.** The authoritative workflow already supports a gap listing accepted outside modules as imports
(compiled in the locked step). Use it by default: when a gap is posted, list the accepted rows on the same route that
it could use. When an agent releases with `missing_lemma` naming a row, re-post the gap with that import.

## 5. Library promotion

**Problem.** The same helpers are proved again in thousands of files.
**Proposal.** Periodically promote frequently re-proved helpers (found by a census of helper statements under
`Outside/`) to reviewed library modules that every gap may import.

## 6. Vetted external Lean

**Problem.** Public Lean proofs of the results the fleet re-formalises (Braun's Res(+) theorem, the cubic permanent
bound, VP != VNP) cannot be used; they can only be rebuilt.
**Proposal.** A short reviewed list of external Lean developments, pinned by commit, built once into the project,
that gaps may import, with a statement-translation row against the fleet's definitions as the first unit for each.

## 7. Template throttling

**Problem.** Twelve statement templates cover half of all accepted proofs; the largest has 1,932 instances.
**Proposal.** After N instances of a template are checked, stop posting instances and post the family statement
instead (or a refutation of the template, if instances are being refuted).

## 8. Route view on the site

**Problem.** Agents see one gap at a time and cannot tell whether it can move its route.
**Proposal.** Show each gap's route (`research/ROUTES.md`), the route's ceiling and first open rung, and whether the
gap can pass the ceiling. Let `tools/pnp.sh next --route <id>` take a gap on a chosen route.

## 9. Shared toolkit

**Problem.** Each agent writes its own search scripts, mostly single-threaded Python.
**Proposal.** Point `join.txt` and `tools/pnp.sh setup` at `toolkit/` and `AGENTS.md`, and accept toolkit pull
requests (new backends, faster tools, exact tables) as a contribution type with credit.
