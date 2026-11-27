# Backends and porting

What runs where today, and the rules for adding a backend (another OS, another GPU).

## Backend matrix (2026-11-27)

"yes" = exists and was tested; "—" = does not exist. "Portable C++" means C++20 + pthreads, built by
`toolkit/Makefile` with clang++ or g++; it was built and tested on macOS arm64 only so far (it uses only the
standard library and GCC/Clang builtins such as `__builtin_ctzll`, so Linux x86_64/arm64 is expected to work, but is
untested).

| tool | portable C++ CPU | Apple Metal GPU | CUDA GPU | other |
|---|---|---|---|---|
| cktcheck | yes | — | — | Python reference `py/pnpfast.py check` |
| cktsat | yes (`cktsat-core`) | — | — | SAT via python-sat (CaDiCaL, Kissat) |
| knsat | — | — | — | Python + python-sat only |
| cktsls | yes | — | — | |
| cktopt | yes | — | — | |
| gpuopt | yes (`--cpu`: same kernels on the CPU, used to check the GPU bit-exactly) | yes | — | |
| gpukit (harness) | — (no CPU fallback device inside gpukit; tools keep their own CPU loop) | yes | — | |
| gpuprobe | — | yes (Swift) | — | |
| graphsynth | yes | — | — | |
| startab, startab-tricheck | yes | — | — | SAT cross-check `src/startab/satcheck.py` |
| andtab | yes | — | — | SAT cross-check `andsat` |
| ptrank | yes | — | — | Python reference `src/ptrank/ptr.py`, SAT check `satcheck.py` |
| ckt2lean, leancheck | — | — | — | Python; leancheck's memory column uses BSD `/usr/bin/time -l` (macOS) |
| pnprun, gpurun | — | — | — | Python, POSIX `flock`; tested on macOS |

There is no CUDA, ROCm, Vulkan or OpenCL backend yet.

## Why GPU, and when

Measured on an Apple M5 Max (docs/gpukit.md, "Measured throughput"; the machine was loaded, load average 18-30):
the dense "score every pair of wires" kernel (for all pairs (a, b) of W wires of P bits, popcount of
`((A|B)^T)&C` and `((A&B)^T)&C`) ran at **82x-137x one CPU core** for P = 16,384 bits (W = 1024..4096; best 137x with
64-bit words at W = 2048), about 1.7e13 bit-ops/s steady state, but only **10-12x** at P = 1024, and below about 1e9
bit-operations per dispatch the CPU is as fast (each command buffer costs about 0.2 ms). Inside a real tool
(`gpuopt`, docs/gpuopt.md) the GPU kernels were 57x (singles) and 124x (pairs) the same loops on one core, but a
whole optimisation round only 27x, because the rest of the round is serial CPU work.

## Porting rules

1. **GPU first when the machine has one and the kernel is dense and uniform** (same work per thread, little
   branching, lots of bit-operations per byte moved). Measure before and after on the same data; put the numbers,
   hardware and load in the tool's doc. If a round is dominated by serial CPU work, a GPU will not help: profile first.
2. **Always keep a portable CPU path behind the same interface.** The CPU path is the reference for the GPU path and
   the fallback on machines without that GPU. `gpuopt --cpu` vs `gpuopt --check` is the model: the same kernels on
   both, compared bit-exactly.
3. **Add a backend behind the existing interface, not a new tool.** An agent on an OS or GPU without a backend
   implements `src/gpukit/gpu.hpp` (`Device`, `Buffer`, `Kernel`, `Args`, `Pacer`) for that platform, e.g.
   `gpu_cuda.cu` next to `gpu.mm`, and selects it in `toolkit/Makefile` by OS / available compiler. Kernels are
   source strings today (Metal Shading Language compiled at run time); a new backend may carry its own kernel
   source for each kernel, kept next to the Metal one with the same name and the same buffer layout.
4. **Every backend passes the same tests.** Run the tool's self-test (`bin/gputest`, `src/gpuopt/run_tests.sh`,
   `src/cktopt/tests/run_tests.sh`) and check every output circuit with `bin/cktcheck` **and**
   `py/pnpfast.py check`. Results must be identical to the CPU path (bit-exact for deterministic tools).
5. **Never rewrite an existing tool.** Extend it (new mode, new backend), port it, or unify two tools; keep the
   command line and file formats compatible. A rewrite throws away the validation the tool already has.
6. **Respect the shared-machine rules** on every backend: default one CPU thread, `pnprun` for long runs, one heavy
   GPU job at a time (`gpurun`, or the in-process lock in gpukit), short dispatches (20-50 ms) when the GPU also
   drives a display, a memory cap on device allocations (gpukit: 2 GiB per process unless raised explicitly).

## Porting checklist for a new platform

1. `make -C toolkit cpu` and `make -C toolkit check`. Fix compiler portability issues in place (keep clang and gcc
   both working). Run `src/cktopt/tests/run_tests.sh` (single thread, short).
2. `bin/pnprun --status` and a tiny `bin/pnprun -c 1 -- true`: check `ps -Ao pid=,ppid=,rss=` works (the memory
   watchdog uses it).
3. For leancheck on Linux, replace `/usr/bin/time -l` with GNU `time -v` parsing (only the memory report uses it).
4. For a GPU: implement gpu.hpp, port `gputest` first (it compares every kernel against a CPU loop), then
   `gpuopt`, then measure against one CPU core and record the table in docs/gpukit.md.
