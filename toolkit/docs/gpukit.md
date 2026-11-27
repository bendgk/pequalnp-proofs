# gpukit — minimal Metal compute harness for C++ tools, and `bin/gpurun`

On a shared machine the GPU is often idle while CPU core-slots are scarce. gpukit was built and measured on an
Apple M5 Max (32 GPU cores, unified memory); it is macOS/Metal only today (see PORTING.md for other backends).
`gpukit` lets a plain C++20 tool run a compute kernel on it: no installs, no offline shader compiler
(kernels are Metal Shading Language source strings compiled at run time), no Objective-C in your code.

Sources: `src/gpukit/gpu.hpp` (API), `src/gpukit/gpu.mm` (Objective-C++ implementation, 170 lines),
`src/gpukit/gputest.cpp` (self-test + benchmark, built as `bin/gputest`), `src/gpukit/example.cpp` (built as `bin/gpukit-example`).

    make -C toolkit gpu                # build/gpu.o, bin/gputest, bin/gpukit-example; macOS only
    bin/gpurun -- bin/gputest          # correctness tests, about 1 s
    bin/gpurun -- bin/gputest --bench  # + throughput table

To use it from your tool: `#include "../gpukit/gpu.hpp"`, link `build/gpu.o` (built by `toolkit/Makefile`) and
`-framework Metal -framework Foundation -framework CoreGraphics` (see the `gpuopt` rule in `toolkit/Makefile`).
Your own files stay ordinary `.cpp` compiled with the usual flags.

## Rules for GPU jobs (they bind every user of the harness)

* **One heavy GPU job at a time.** `bin/gpurun -- cmd ...` takes an exclusive `flock` on
  `$GPUKIT_LOCK`, else `$PNP_SLOTS/gpu.lock`, else `toolkit/.slots/gpu.lock`, then `exec`s the command (no wrapper process; the lock is released when the job and all
  its children are gone). `gpurun --status` shows the holder, `--nowait` fails instead of queueing,
  `-t SECONDS` arms SIGALRM. A tool started WITHOUT gpurun is still safe: `Device::open()` takes the same lock
  in-process (and waits, printing one line) unless `GPURUN_HELD` is set, which gpurun does.
* **gpurun is not pnprun.** A GPU tool still burns one CPU thread. A long run goes
  `bin/pnprun -c 1 -- bin/gpurun -- cmd ...` (in that order, so no GPU lock is held while waiting for a slot).
* **Short dispatches.** On macOS the window server draws the screen on the same GPU. Keep one command buffer at
  20–50 ms and loop; `gpukit::Pacer` does the chunk sizing from the measured GPU time.
  Longest single dispatch in the benchmark below: 14.6 ms; in `gpuopt` with default settings: 42.4 ms.
  Pacing by item count is only safe when every thread costs about the same: see the pitfall on uneven work.
* **Memory.** `alloc()` refuses once the live buffers of a `Device` exceed 2 GiB (`GPUKIT_MAX_BYTES` or
  `OpenOpts::maxBytes` to change it deliberately). The device itself would allow 21 GiB per buffer; that is
  shared with system RAM (36 GB on the test machine), so do not.

## API (`namespace gpukit`, all of it)

    Device* Device::open(std::string* err = nullptr, const OpenOpts& = {});   // nullptr if no Metal device
        OpenOpts { bool lock = true; uint64_t maxBytes = 0; bool quiet = false; }
    std::string name();  uint64_t max_buffer_bytes();  uint64_t allocated_bytes();
    Kernel compile(const std::string& mslSource, const std::string& fn, std::string* err = nullptr);
        Kernel { simd (threadExecutionWidth, 32 here), maxGroup (1024 here), name }; null Kernel on error, *err = compiler text
    Buffer alloc(size_t bytes, std::string* err = nullptr);   void free(Buffer&);
        Buffer { void* data; size_t bytes; as<T>() }   // MTLStorageModeShared, zero-filled, page aligned
    Args().buf(index, buffer, byteOffset = 0).u32(index, v).val<T>(index, pod)   // bindings of one dispatch
    Ticket submit1d(kernel, args, n);  Ticket submit2d(kernel, args, w, h);  Ticket submit(vector<Dispatch>)
    double wait(Ticket&, std::string* err = nullptr);          // GPU seconds of that command buffer, or -1
    double run1d(kernel, args, n, &err);  double run2d(kernel, args, w, h, &err);   // submit + wait
    double gpu_seconds();  uint64_t dispatches();
    Pacer(start, lo, hi, targetSeconds = 0.020).next(done, gpuSeconds) -> next chunk size

* `data` of a Buffer IS the memory the kernel sees (zero copy on Apple silicon). Write inputs in place, call
  `wait()`, read results in place. Do not touch a buffer between `submit` and `wait`.
* `Args::buf(i, ...)` binds `[[buffer(i)]]`; `u32`/`val` bind a by-value constant declared as
  `constant uint &name [[buffer(i)]]` (Metal `setBytes`, at most 4 KB).
* `submit*` returns immediately; several submits queue in order; `submit(vector<Dispatch>)` puts several
  dispatches (each with its own kernel and bindings) into one command buffer.
* Grids need not be multiples of anything (`dispatchThreads`, non-uniform thread groups). 1D kernels take
  `uint gid [[thread_position_in_grid]]`, 2D kernels `uint2 gid` (x < w, y < h).
* One `Device` per process, single-threaded use.

## Example (`src/gpukit/example.cpp`, 30 lines of code)

```cpp
#include "gpu.hpp"
#include <cstdio>
static const char* src = R"(
#include <metal_stdlib>
using namespace metal;
kernel void ham(device const uint *v [[buffer(0)]], device uint *out [[buffer(1)]], constant uint &N [[buffer(2)]],
                uint2 gid [[thread_position_in_grid]]) {      // gid.x = a, gid.y = b
    uint d = 0;
    for (uint w = 0; w < 8; w++) d += popcount(v[gid.x * 8 + w] ^ v[gid.y * 8 + w]);
    out[gid.y * N + gid.x] = d;
}
)";
int main() {
  std::string err;
  gpukit::Device* d = gpukit::Device::open(&err);                 // takes the GPU lock unless run under bin/gpurun
  if (!d) { printf("no GPU: %s\n", err.c_str()); return 1; }
  gpukit::Kernel k = d->compile(src, "ham", &err);
  if (!k) { printf("%s\n", err.c_str()); return 1; }
  const uint32_t N = 2048;
  gpukit::Buffer v = d->alloc(N * 8 * 4), out = d->alloc((size_t)N * N * 4);
  uint32_t* x = v.as<uint32_t>();                                 // shared memory: write inputs in place
  for (uint32_t i = 0; i < N * 8; i++) x[i] = i * 2654435761u ^ (i >> 3);
  double gpuSec = d->run2d(k, gpukit::Args().buf(0, v).buf(1, out).u32(2, N), N, N, &err);   // blocks until done
  if (gpuSec < 0) { printf("%s\n", err.c_str()); return 1; }
  size_t bad = 0;                                                 // results are already in out.data
  for (uint32_t a = 0; a < N; a += 37) for (uint32_t b = 0; b < N; b += 41) {
    uint32_t dd = 0; for (int w = 0; w < 8; w++) dd += __builtin_popcount(x[a * 8 + w] ^ x[b * 8 + w]);
    bad += dd != out.as<uint32_t>()[(size_t)b * N + a];
  }
  printf("%s: %u x %u pairs in %.2f ms GPU, sample check %s\n", d->name().c_str(), N, N, gpuSec * 1e3, bad ? "FAILED" : "ok");
  d->free(v); d->free(out); delete d;
}
```

Output on the test machine: `Apple M5 Max: 2048 x 2048 pairs in 0.13 ms GPU, sample check ok`.

## Validation (`bin/gputest`, every comparison bit-exact against a plain CPU loop on random inputs)

| test | result |
|---|---|
| pair-score kernel (below), `uint` words, W x P = 37x1000, 64x1024, 257x4129, 300x16384 (P not a multiple of 64 included) | exact, 323,028 result words |
| the same kernel on `ulong` words | exact |
| 64-bit integer semantics: `popcount`, `clz`, `ctz`, `*` (wrapping), `+`, `<<`, `>>`, `<` on 65,536 `ulong` pairs | exact |
| compaction with `atomic_fetch_add_explicit` on a `device atomic_uint*`: 10,505 hits of 1,048,576 | exact as a set |
| 3 GiB allocation against the 2 GiB cap | refused |
| benchmark rows: first rows of every GPU result against the CPU loop | equal |

## Measured throughput (Apple M5 Max, 2026-11-27, machine load average 18–30 from other jobs)

Kernel "score every pair of wires": for all pairs (a, b) of W wires of P bits,
popcount(((A|B)^T)&C) and popcount(((A&B)^T)&C), i.e. 2 x P bit-operations per pair, results written for
every pair (W*W*8 bytes). Best of 6 timed passes, each pass split into 5 paced dispatches.
"1 CPU" is the same loop in C++ (`-O3 -mcpu=native`, 64-bit words, one thread) on a slice of the rows.

| W | P | words | wall s per pass | longest dispatch | pairs/s | bit-ops/s | vs 1 CPU core |
|---|---|---|---|---|---|---|---|
| 1024 | 1024 | uint | 0.0015 | 0.3 ms | 6.9e8 | 1.4e12 | 10x |
| 1024 | 1024 | ulong | 0.0012 | 0.2 ms | 8.4e8 | 1.7e12 | 12x |
| 1024 | 1024 | 1 CPU | – | – | 7.2e7 | 1.5e11 | 1 |
| 1024 | 16384 | uint | 0.0026 | 0.9 ms | 4.1e8 | 1.3e13 | 82x |
| 1024 | 16384 | ulong | 0.0021 | 0.7 ms | 5.0e8 | 1.6e13 | 101x |
| 1024 | 16384 | 1 CPU | – | – | 5.0e6 | 1.6e11 | 1 |
| 2048 | 16384 | uint | 0.0080 | 3.4 ms | 5.3e8 | 1.7e13 | 111x |
| 2048 | 16384 | ulong | 0.0064 | 2.7 ms | 6.5e8 | 2.1e13 | 137x |
| 2048 | 16384 | 1 CPU | – | – | 4.7e6 | 1.6e11 | 1 |
| 4096 | 16384 | uint | 0.0312 | 13.8 ms | 5.4e8 | 1.8e13 | 114x |
| 4096 | 16384 | ulong | 0.0327 | 14.6 ms | 5.1e8 | 1.7e13 | 109x |
| 4096 | 16384 | 1 CPU | – | – | 4.7e6 | 1.5e11 | 1 |

* Steady state is about 1.7e13 bit-ops/s, 110x one (loaded) CPU core on this dense kernel.
* A command buffer costs about 0.2 ms of wall time whatever it does (the 1024x1024 rows: GPU time 0.6 ms,
  wall 1.5 ms for 5 dispatches). Below roughly 1e9 bit-operations per dispatch the CPU is as fast.
* Runtime compilation of one kernel (`newLibraryWithSource` + pipeline state): 6.2 ms measured with the OS shader cache warm (printed by `gputest`); expect more on the very first run of a new source.
* In a real tool (`gpuopt`, kernels with early exits): 6e12 bit-tests/s on the per-(gate, wire) filter and
  3–7e10 exact pair tests/s; 56x and 169x the wall time of the same C++ loop on one core (docs/gpuopt.md).

## Pitfalls (all met while writing this)

* **`uint` is 32 bits in MSL.** `ulong` (64 bits) works on this device and OS, including `popcount`, `clz`,
  `ctz`, shifts and wrapping multiply: checked bit-exactly (table above), and it is as fast or faster than two
  `uint` halves. Literals need the suffix: `0ul`, `~0ul`, `1ul << 63`. A `uint64_t` column on the CPU is the
  same bytes as one `ulong` or two `uint` (low half first) on the GPU.
* Index arithmetic is 32-bit too: `cols[w * NW + k]` wraps silently above 2^32 elements. Fine for our sizes; cast to
  `ulong` first if a buffer can exceed 4 G elements.
* Comparisons give `bool`; write `(x == 0ul ? 1u : 0u)`, not arithmetic on the comparison.
* No recursion, no dynamic memory, keep per-thread arrays small. Loops with data-dependent `break` are fine,
  but threads run in SIMD groups of 32: a group lasts as long as its slowest thread, so put similar work next
  to each other in the grid.
* Atomic append (`atomic_fetch_add_explicit(cnt, 1u, memory_order_relaxed)` then `list[k] = ...`) works, but the
  order of the list is not reproducible and anything beyond your capacity is dropped at random. For
  deterministic tools write one fixed result slot per thread instead (what gpuopt does: best partner + count
  per row) and compact on the CPU.
* `Args::val`/`u32` copy at most 4 KB; bigger tables go into a Buffer.
* Shared buffers are not snapshotted: writing to an input after `submit` and before `wait` is a data race.
* `alloc()` counts against a 2 GiB cap per process on purpose; a null Buffer comes back with a message in `*err`.
* **Uneven work per thread breaks count-based pacing.** In gpuopt's pair and product kernels one thread costs
  between a few and 10^5 inner iterations depending on the gate, and chunks of a fixed number of threads
  produced single dispatches of 341 ms (they completed normally, but that is 20 dropped frames for the UI).
  Fix used there: the CPU estimates the work of every item and chunks on the sum (`WorkPacer` in
  `src/gpuopt/gpuopt.cpp`), correcting the budget at once after an overshoot.
* Nothing was tested with a dispatch longer than 341 ms. Do not rely on long dispatches surviving.
* `MTLCreateSystemDefaultDevice()` needs CoreGraphics linked in a command-line tool; the Makefile does it.

## Offer to `andtab` (docs/andtab.md) and other enumerations

The last step of andtab's search ("every pair X, Y of closure members ... X ∩ Y") is the shape this harness is
good at: cell sets of at most 25 or 36 bits fit one `ulong`, a closure list is a buffer, the pair pass is a 2D
grid with one result slot per row. andtab reports 1.06e9 pair tests/s on one core for 5x5 (finished in 23 s, so
5x5 needs nothing); the pair kernels here ran at 4–8e10 exact tests/s. If a 6x6 run or a longer enumeration is
attempted: include `src/gpukit/gpu.hpp`, copy the dispatch loop from `src/gpukit/example.cpp`, keep a CPU
reference of the kernel and compare (as `gpuopt --check` does). I have not written an andtab kernel.

## Who should use it

Worth it for dense, regular work: every (item, item) or (item, candidate) combination, tiny fixed state per
thread, more than about 1e10 bit-operations per call. Not worth it where a CPU can skip almost everything
with an index or an early exit on sparse data; the cand32/cand128 shrinking problem turned out to be of that
kind (docs/gpuopt.md, "What the GPU does and does not buy here").
