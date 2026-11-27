# toolkit — fast checkers and searchers for small circuit lower-bound units

Native tools for the AND/OR/NOT circuit units of this repository: an exact bit-parallel verifier, SAT exact
synthesis, stochastic search, a don't-care-aware shrinker, exact tables for small graphs, and an emitter that turns
a verified circuit into a Lean proof file. Use and extend these instead of writing private search scripts.

Everything here follows the Lean definitions in `lean/PEqualNP/Defs/CircuitLowerBounds.lean`. File formats are in
[FORMAT.md](FORMAT.md). Results computed with these tools (with method and caveats) are in
[docs/RESULTS.md](docs/RESULTS.md). The targets they were built for are in [TARGETS.md](TARGETS.md). Backends
and porting rules are in [PORTING.md](PORTING.md).

## Tools

| tool | what it does | language | doc |
|---|---|---|---|
| `bin/cktcheck SPEC CKT [--basis aon\|ao\|ao2] [--max S]` | exact verifier, Lean `Circuit.eval` semantics, bit-parallel. Exit 0 = OK. `--stream -j T` checks many circuits from stdin | C++ | FORMAT.md |
| `bin/pyrun py/pnpfast.py check SPEC CKT` | independent slow reference checker (pure Python big ints); also spec generators and Lean <-> .ckt | Python | FORMAT.md |
| `bin/cktsat SPEC --basis B -s S` | exact synthesis by SAT: cube-and-conquer over canonical prefixes modulo the spec's symmetry group; prints a witness or an exhaustive UNSAT with an audit log | C++ core + Python driver, CaDiCaL/Kissat | [docs/cktsat.md](docs/cktsat.md) |
| `src/knsat/` | specialised exact search for K(n) (threshold-2) with elimination clauses | Python + python-sat | [docs/cktsat.md](docs/cktsat.md), file headers |
| `bin/cktsls SPEC --basis B -s S` | multi-threaded stochastic local search for witnesses, incremental bit-parallel evaluation | C++ | [docs/cktsls.md](docs/cktsls.md) |
| `bin/cktopt SPEC IN.ckt -o OUT.ckt` | don't-care-aware shrinker: resubstitution with observability, window resynthesis, OR-sharing | C++ | [docs/cktopt.md](docs/cktopt.md) |
| `bin/graphsynth SPEC -o OUT.ckt` | constructive search for graph circuits (biclique covers, OR-sharing); `--analyze` gives a structure report | C++ | [docs/graphsynth.md](docs/graphsynth.md) |
| `bin/startab --n N` | exact monotone / with-NOT sizes for all bipartite graphs up to 4x4 (5x5 mostly), with witnesses | C++ | [docs/startab.md](docs/startab.md) |
| `bin/andtab`, `bin/andsat` | exact AND-complexity (OR free) of all small bipartite graphs; SAT cross-check of one graph | C++, Python | [docs/andtab.md](docs/andtab.md) |
| `bin/ptrank` | partial-transpose rank of the identity over GF(2) (exact search + reference `src/ptrank/ptr.py`) | C++, Python | [docs/ptrank.md](docs/ptrank.md) |
| `bin/ckt2lean`, `bin/leancheck` | verified circuit -> Lean 4 proof file for a unit's statement; lint by the repo's rules and build in a sandbox clone | Python | [docs/ckt2lean.md](docs/ckt2lean.md) |
| `bin/gpuopt` | GPU version of the shrinker's scoring loops (macOS/Metal only) | C++ + Metal | [docs/gpuopt.md](docs/gpuopt.md) |
| `src/gpukit/` (`bin/gputest`, `bin/gpukit-example`) | minimal Metal compute harness for C++ tools; `bin/gpurun` = one-job GPU lock | C++ / Obj-C++ | [docs/gpukit.md](docs/gpukit.md) |
| `bin/gpuprobe` | Swift feasibility probe for the pair-scoring kernel (built only if `swiftc` exists) | Swift | `src/gpuprobe/probe.swift` |
| `bin/pnprun -c CORES -m GB -- cmd` | machine-wide core-slot semaphore + memory/time watchdog for heavy runs | Python | below |
| `bin/satpy`, `bin/pyrun` | run a Python script with `py/` on the path (`satpy` also checks that python-sat is installed) | sh | below |

Data: `specs/` (spec files of the units), `seeds/` (circuits extracted from accepted proofs), `found/` (verified
witness circuits, named `<spec>_<size>_<basis>.ckt`), `tables/` (exact tables, JSON).

## Build

    make -C toolkit            # every native tool into toolkit/bin/ (Metal tools only on macOS)
    make -C toolkit cpu        # only the portable C++ tools
    make -C toolkit check      # smoke test: both checkers on a seed circuit, and a wrong circuit must be rejected

Needs a C++20 compiler (clang++ or g++; default clang++ if present, override with `CXX=`). The Makefile picks
`-mcpu=native` on arm64 and `-march=native` on x86_64; `make PORTABLE=1` drops it. On Linux the Metal tools are
skipped with a message. `make -C toolkit/src/<tool>` still works (it calls the top-level Makefile). Build output
(`bin/` binaries, `build/`) is git-ignored.

Python tools need Python >= 3.10. The SAT-based ones need python-sat: `pip install python-sat` (it bundles CaDiCaL,
Kissat, Glucose, RC2). Choose the interpreter with `PNP_PYTHON=/path/to/python` (e.g. a venv); default `python3`.

## Quick start

    make -C toolkit
    cd toolkit
    bin/cktcheck specs/cand32.spec seeds/cand32_207.ckt --basis aon      # OK  size=206 ...
    bin/pyrun py/pnpfast.py check specs/cand32.spec seeds/cand32_207.ckt  # OK size 206
    bin/cktsat specs/kn4.spec --basis ao -s 6 -j 1                        # UNSAT in about a second (K(4) = 7)
    bin/cktsls specs/kn5.spec --basis ao -s 10 -j 1 --time 10 -o /tmp/kn5.ckt
    bin/cktopt specs/cand32.spec seeds/cand32_207.ckt -o /tmp/c32.ckt --basis aon -j 1 --time 5
    bin/ckt2lean --unit L-meta-NNNNN --statement-file STMT.txt SPEC CKT -o OUT.lean   # then: bin/leancheck OUT.lean

## Rules

### Two checkers must agree

Every search tool re-verifies its output with `pnp::verify` (include/ckt.hpp) before printing it. Before a circuit
is used anywhere (a Lean file, a table, a claim), check it with **both** `bin/cktcheck` and
`py/pnpfast.py check`; they are independent implementations of the same Lean semantics. If they disagree, the
circuit is not verified and one of the checkers has a bug: report it. The same holds for any new backend
(see PORTING.md): it must give the same answers as these two on the same inputs.

Exhaustive (UNSAT) results are computational: say which solver, which encoding, and which derived clauses
(symmetry, elimination) the claim rests on, as docs/RESULTS.md does.

### Shared machines

Agents often share one machine. A runaway search can make it unusable for everyone.

1. Tools take `-j THREADS` and default to `$PNP_THREADS` or **1**, never to all cores.
2. Anything multi-threaded, or any run longer than about a minute, goes through the slot semaphore:

        bin/pnprun -c CORES -m GB [-t SECONDS] -- cmd args...
        bin/pnprun --status

   It waits until CORES slots are free, runs the command with `PNP_THREADS=CORES`, and kills the process tree if
   its resident memory exceeds GB (default 6) or it runs longer than SECONDS. Slots are `flock`ed files, so they free
   themselves if a job dies. Settings: `PNP_SLOTS` = the slot directory (default `toolkit/.slots`; every user of the
   machine must use the same one), `PNP_MAX_SLOTS` = total slots (default: the number of cores; set it lower to
   keep cores free).
3. Development tests outside pnprun: one thread, under 2 GB, under a minute.
4. Memory: no tool allocates more than about 8 GB without an explicit flag; no unbounded hash tables or queues.
5. No Python multiprocessing fan-out for heavy work; native threads in C++/Rust instead. (cktsat's worker
   processes are the exception: each is a SAT solver and counts as one thread of `-j`.)
6. GPU: one heavy GPU job at a time, `bin/gpurun -- cmd` (lock file `$PNP_SLOTS/gpu.lock`). A long GPU run still
   needs a CPU slot: `bin/pnprun -c 1 -- bin/gpurun -- cmd`.
7. Never leave background jobs running when you stop.

## Languages

* **C++20 or Rust** for hot paths (checkers, search inner loops). Share `include/ckt.hpp` for parsing and evaluation.
* **Metal / CUDA** for dense, uniform kernels (scoring all pairs of wires and the like), always with a CPU path
  behind the same interface (PORTING.md).
* **Python** only as glue, drivers and slow reference implementations (e.g. `py/pnpfast.py`, `src/ptrank/ptr.py`).
* **SAT**: CaDiCaL / Kissat through python-sat. Never write your own SAT solver.

## Adding a tool

1. Check that no existing tool does it. Prefer extending one (a new mode, a new backend) over a new tool.
2. Put the code in `src/<tool>/` and add a rule to `toolkit/Makefile` (binary to `bin/<tool>`; built to a
   temporary name and renamed, like the existing rules). Python entry points get a 3-line wrapper in `bin/` like
   `bin/cktsat`, and the new name goes on the un-ignore list in `toolkit/.gitignore`.
3. Read and write the shared formats (FORMAT.md). Re-verify every circuit you output with `pnp::verify`.
4. Default to one thread; take `-j`; respect `PNP_THREADS`.
5. Write `docs/<tool>.md` with: usage, what is exact and what is heuristic, **measured speed against a stated
   baseline** (hardware, load, threads), validation done (agreement with cktcheck and the Python reference), and
   limits.
6. Put verified witnesses in `found/` and durable results (with method and caveats) in `docs/RESULTS.md`.
