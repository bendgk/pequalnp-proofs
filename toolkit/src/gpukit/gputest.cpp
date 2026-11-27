// gputest — gpukit self-test + throughput probe.  Every kernel is compared bit-exactly with a plain CPU loop.
//   gputest            correctness tests (few seconds)
//   gputest --bench    + throughput table (pair-score kernel, 32-bit vs 64-bit words, 1 CPU core reference)
#include "gpu.hpp"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
using namespace gpukit;
typedef uint64_t u64;
typedef uint32_t u32;

static u64 rs = 0x243F6A8885A308D3ull;
static u64 rnd() { u64 z = (rs += 0x9E3779B97F4A7C15ull); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31); }
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

// pair score: for wires a (x) and b (y = row0 + gid.y): popcount(((A|B)^T)&C), popcount(((A&B)^T)&C)
static const char* kPair32 = R"(
#include <metal_stdlib>
using namespace metal;
kernel void score(device const uint *cols [[buffer(0)]], device const uint *T [[buffer(1)]], device const uint *C [[buffer(2)]],
                  device uint *out [[buffer(3)]], constant uint &W [[buffer(4)]], constant uint &NW [[buffer(5)]],
                  constant uint &row0 [[buffer(6)]], uint2 gid [[thread_position_in_grid]]) {
    uint bb = row0 + gid.y;
    uint a = gid.x * NW, b = bb * NW, co = 0, ca = 0;
    for (uint w = 0; w < NW; w++) {
        uint x = cols[a + w], y = cols[b + w], t = T[w], c = C[w];
        co += popcount(((x | y) ^ t) & c);
        ca += popcount(((x & y) ^ t) & c);
    }
    out[(bb * W + gid.x) * 2] = co; out[(bb * W + gid.x) * 2 + 1] = ca;
}
)";
static const char* kPair64 = R"(
#include <metal_stdlib>
using namespace metal;
kernel void score(device const ulong *cols [[buffer(0)]], device const ulong *T [[buffer(1)]], device const ulong *C [[buffer(2)]],
                  device uint *out [[buffer(3)]], constant uint &W [[buffer(4)]], constant uint &NW [[buffer(5)]],
                  constant uint &row0 [[buffer(6)]], uint2 gid [[thread_position_in_grid]]) {
    uint bb = row0 + gid.y;
    uint a = gid.x * NW, b = bb * NW;
    ulong co = 0, ca = 0;
    for (uint w = 0; w < NW; w++) {
        ulong x = cols[a + w], y = cols[b + w], t = T[w], c = C[w];
        co += popcount(((x | y) ^ t) & c);
        ca += popcount(((x & y) ^ t) & c);
    }
    out[(bb * W + gid.x) * 2] = uint(co); out[(bb * W + gid.x) * 2 + 1] = uint(ca);
}
)";
// 64-bit integer semantics check: popcount, clz, ctz, shifts, wrap-around multiply, compare
static const char* kU64 = R"(
#include <metal_stdlib>
using namespace metal;
kernel void u64ops(device const ulong *in [[buffer(0)]], device ulong *out [[buffer(1)]], uint gid [[thread_position_in_grid]]) {
    ulong x = in[2 * gid], y = in[2 * gid + 1];
    ulong r = ulong(popcount(x)) + (ulong(clz(y)) << 8) + (ulong(ctz(x | (1ul << 63))) << 16);
    r ^= (x * y) ^ (x >> (y & 63ul)) ^ (y << (x & 63ul)) ^ (x + y) ^ ((x < y) ? 0x5555000000000000ul : 0ul);
    out[gid] = r;
}
)";
// compaction with an atomic counter: append the index of every element below a threshold
static const char* kCompact = R"(
#include <metal_stdlib>
using namespace metal;
kernel void pick(device const uint *v [[buffer(0)]], device atomic_uint *cnt [[buffer(1)]], device uint *list [[buffer(2)]],
                 constant uint &thr [[buffer(3)]], constant uint &cap [[buffer(4)]], uint gid [[thread_position_in_grid]]) {
    if (v[gid] < thr) {
        uint k = atomic_fetch_add_explicit(cnt, 1u, memory_order_relaxed);
        if (k < cap) list[k] = gid;
    }
}
)";

static int fails = 0;
#define CHECK(c, msg) do { if (!(c)) { printf("FAIL: %s\n", msg); fails++; } } while (0)

struct PairRes { double gpuSec, wallSec; int chunks; double maxChunk; };

// runs the pair kernel over all W x W pairs in row chunks paced to ~20 ms; out must hold W*W*2 u32
static PairRes run_pairs(Device* d, const Kernel& k, Buffer cols, Buffer T, Buffer C, Buffer out, u32 W, u32 NW, double target) {
  PairRes r{0, 0, 0, 0};
  double t0 = now();
  Pacer pc(std::max<u32>(1, W / 16), 1, W, target);
  for (u32 row = 0; row < W;) {
    u32 n = (u32)std::min<size_t>(pc.n, W - row);
    Args a; a.buf(0, cols).buf(1, T).buf(2, C).buf(3, out).u32(4, W).u32(5, NW).u32(6, row);
    std::string err;
    double s = d->run2d(k, a, W, n, &err);
    if (s < 0) { printf("GPU error: %s\n", err.c_str()); exit(1); }
    r.gpuSec += s; r.chunks++; if (s > r.maxChunk) r.maxChunk = s;
    pc.next(n, s);
    row += n;
  }
  r.wallSec = now() - t0;
  return r;
}

static void cpu_pairs64(const u64* cols, const u64* T, const u64* C, u32* out, u32 W, u32 NW64, u32 rowsFrom, u32 rowsTo) {
  for (u32 b = rowsFrom; b < rowsTo; b++)
    for (u32 a = 0; a < W; a++) {
      const u64 *x = cols + (size_t)a * NW64, *y = cols + (size_t)b * NW64;
      u64 co = 0, ca = 0;
      for (u32 w = 0; w < NW64; w++) {
        co += __builtin_popcountll(((x[w] | y[w]) ^ T[w]) & C[w]);
        ca += __builtin_popcountll(((x[w] & y[w]) ^ T[w]) & C[w]);
      }
      out[((size_t)b * W + a) * 2] = (u32)co; out[((size_t)b * W + a) * 2 + 1] = (u32)ca;
    }
}

int main(int argc, char** argv) {
  bool bench = false;
  for (int i = 1; i < argc; i++) if (std::string(argv[i]) == "--bench") bench = true;
  std::string err;
  Device* d = Device::open(&err);
  if (!d) { printf("no GPU: %s\n", err.c_str()); return 1; }
  printf("device: %s   maxBufferLength %.1f GiB\n", d->name().c_str(), d->max_buffer_bytes() / 1073741824.0);
  double tc0 = now();
  Kernel k32 = d->compile(kPair32, "score", &err);
  if (!k32) { printf("compile pair32: %s\n", err.c_str()); return 1; }
  printf("runtime compile of one kernel (newLibraryWithSource + pipeline state): %.1f ms\n", (now() - tc0) * 1e3);
  Kernel k64 = d->compile(kPair64, "score", &err);
  bool has64 = (bool)k64;
  if (!has64) printf("NOTE: 64-bit kernel did not compile: %s\n", err.c_str());
  printf("kernel score: threadExecutionWidth %u, maxTotalThreadsPerThreadgroup %u, ulong kernel %s\n", k32.simd, k32.maxGroup, has64 ? "compiles" : "REJECTED");

  // ---- test 1: pair score, bit-exact vs CPU, several shapes (P not a multiple of 64 included) ----
  struct Shape { u32 W, P; } shapes[] = {{37, 1000}, {64, 1024}, {257, 4096 + 33}, {300, 16384}};
  for (auto sh : shapes) {
    u32 W = sh.W, P = sh.P, NW64 = (P + 63) / 64, NW32 = NW64 * 2;
    Buffer cols = d->alloc((size_t)W * NW64 * 8), T = d->alloc(NW64 * 8), C = d->alloc(NW64 * 8), out = d->alloc((size_t)W * W * 8);
    u64* c = cols.as<u64>(); for (size_t i = 0; i < (size_t)W * NW64; i++) c[i] = rnd();
    u64 *t = T.as<u64>(), *cm = C.as<u64>();
    for (u32 i = 0; i < NW64; i++) { t[i] = rnd(); cm[i] = (rnd() % 4 == 0) ? 0 : (rnd() | rnd()); }
    if (P % 64) cm[NW64 - 1] &= (u64(1) << (P % 64)) - 1;
    std::vector<u32> ref((size_t)W * W * 2);
    cpu_pairs64(c, t, cm, ref.data(), W, NW64, 0, W);
    run_pairs(d, k32, cols, T, C, out, W, NW32, 0.020);     // little-endian: a u64 column is two u32 words, low first
    bool ok32 = memcmp(ref.data(), out.data, ref.size() * 4) == 0;
    bool ok64 = true;
    if (has64) { memset(out.data, 0xff, out.bytes); run_pairs(d, k64, cols, T, C, out, W, NW64, 0.020); ok64 = memcmp(ref.data(), out.data, ref.size() * 4) == 0; }
    printf("pair-score W=%u P=%u: uint kernel %s, ulong kernel %s  (%zu results compared)\n", W, P, ok32 ? "exact" : "MISMATCH", has64 ? (ok64 ? "exact" : "MISMATCH") : "n/a", ref.size());
    CHECK(ok32, "pair32"); CHECK(ok64, "pair64");
    d->free(cols); d->free(T); d->free(C); d->free(out);
  }
  // ---- test 2: 64-bit integer semantics ----
  {
    Kernel ku = d->compile(kU64, "u64ops", &err);
    if (!ku) { printf("ulong ops kernel REJECTED: %s\n", err.c_str()); fails++; }
    else {
      const u32 n = 1 << 16;
      Buffer in = d->alloc((size_t)n * 16), out = d->alloc((size_t)n * 8);
      u64* x = in.as<u64>();
      for (u32 i = 0; i < 2 * n; i++) x[i] = (i % 7 == 0) ? (rnd() >> (rnd() % 64)) : rnd();
      x[0] = 0; x[1] = 0; x[2] = ~u64(0); x[3] = 1;
      d->run1d(ku, Args().buf(0, in).buf(1, out), n, &err);
      size_t bad = 0;
      for (u32 i = 0; i < n; i++) {
        u64 a = x[2 * i], b = x[2 * i + 1];
        u64 clzb = b ? (u64)__builtin_clzll(b) : 64;
        u64 r = (u64)__builtin_popcountll(a) + (clzb << 8) + ((u64)__builtin_ctzll(a | (u64(1) << 63)) << 16);
        r ^= (a * b) ^ (a >> (b & 63)) ^ (b << (a & 63)) ^ (a + b) ^ ((a < b) ? 0x5555000000000000ull : 0);
        if (r != out.as<u64>()[i]) bad++;
      }
      printf("ulong ops (popcount, clz, ctz, *, +, <<, >>, <) on %u items: %s\n", n, bad ? "MISMATCH" : "exact");
      CHECK(bad == 0, "u64 ops");
      d->free(in); d->free(out); d->release(ku);
    }
  }
  // ---- test 3: atomic compaction ----
  {
    Kernel kc = d->compile(kCompact, "pick", &err);
    if (!kc) { printf("atomic kernel REJECTED: %s\n", err.c_str()); fails++; }
    else {
      const u32 n = 1 << 20, cap = 1 << 16, thr = 1000;
      Buffer v = d->alloc((size_t)n * 4), cnt = d->alloc(4), list = d->alloc((size_t)cap * 4);
      u32* vv = v.as<u32>(); std::vector<char> want(n, 0); u32 nwant = 0;
      for (u32 i = 0; i < n; i++) { vv[i] = (u32)(rnd() % 100000); if (vv[i] < thr) { want[i] = 1; nwant++; } }
      d->run1d(kc, Args().buf(0, v).buf(1, cnt).buf(2, list).u32(3, thr).u32(4, cap), n, &err);
      u32 got = cnt.as<u32>()[0]; bool ok = got == nwant && got <= cap;
      for (u32 i = 0; ok && i < got; i++) { u32 id = list.as<u32>()[i]; if (id >= n || !want[id]) ok = false; else want[id] = 0; }
      printf("atomic append compaction: %u hits of %u items: %s\n", got, n, ok ? "exact (as a set)" : "MISMATCH");
      CHECK(ok, "compaction");
      d->free(v); d->free(cnt); d->free(list); d->release(kc);
    }
  }
  // ---- cap test ----
  { std::string e2; Buffer big = d->alloc((size_t)3 << 30, &e2); CHECK(!big, "2 GiB cap not enforced"); printf("buffer cap: 3 GiB alloc %s\n", big ? "ALLOWED (bad)" : "refused (ok)"); }

  if (bench) {
    printf("\n== throughput: all-pairs score, 2 ops (OR, AND) x P bits per pair; dispatches paced to ~20 ms ==\n");
    printf("%6s %6s %-6s %10s %10s %7s %9s %12s %12s\n", "W", "P", "words", "GPU s", "wall s", "chunks", "max ms", "pairs/s", "bit-ops/s");
    struct Shape2 { u32 W, P; } bs[] = {{1024, 1024}, {1024, 16384}, {2048, 16384}, {4096, 16384}};
    for (auto sh : bs) {
      u32 W = sh.W, P = sh.P, NW64 = P / 64;
      Buffer cols = d->alloc((size_t)W * NW64 * 8), T = d->alloc(NW64 * 8), C = d->alloc(NW64 * 8), out = d->alloc((size_t)W * W * 8);
      u64* c = cols.as<u64>(); for (size_t i = 0; i < (size_t)W * NW64; i++) c[i] = rnd();
      for (u32 i = 0; i < NW64; i++) { T.as<u64>()[i] = rnd(); C.as<u64>()[i] = ~u64(0); }
      for (int variant = 0; variant < (has64 ? 2 : 1); variant++) {
        PairRes best{1e9, 1e9, 0, 0};
        for (int rep = 0; rep < 7; rep++) {
          PairRes r = variant ? run_pairs(d, k64, cols, T, C, out, W, NW64, 0.020) : run_pairs(d, k32, cols, T, C, out, W, NW64 * 2, 0.020);
          if (rep && r.wallSec < best.wallSec) best = r;
        }
        double pairs = (double)W * W;
        printf("%6u %6u %-6s %10.4f %10.4f %7d %9.1f %12.3e %12.3e   (by GPU time: %.3e bit-ops/s)\n", W, P, variant ? "ulong" : "uint", best.gpuSec, best.wallSec, best.chunks, best.maxChunk * 1e3,
               pairs / best.wallSec, pairs * P * 2 / best.wallSec, pairs * P * 2 / best.gpuSec);
      }
      // 1 CPU core, same dense kernel (clang -O3 -mcpu=native, 64-bit words), on a slice of rows
      u32 rows = std::max<u32>(1, (u32)(2.0e9 / ((double)W * P * 2)));   // ~2e9 bit-ops
      if (rows > W) rows = W;
      std::vector<u32> ref((size_t)W * W * 2);
      double t0 = now(); cpu_pairs64(c, T.as<u64>(), C.as<u64>(), ref.data(), W, NW64, 0, rows); double dt = now() - t0;
      bool same = memcmp(ref.data(), out.data, (size_t)rows * W * 8) == 0;
      printf("%6u %6u %-6s %10s %10.4f %7s %9s %12.3e %12.3e   (%u rows; equals GPU: %s)\n", W, P, "1 CPU", "-", dt, "-", "-", (double)rows * W / dt, (double)rows * W * P * 2 / dt, rows, same ? "yes" : "NO");
      CHECK(same, "bench compare");
      d->free(cols); d->free(T); d->free(C); d->free(out);
    }
    printf("total GPU time %.3f s in %llu command buffers\n", d->gpu_seconds(), (unsigned long long)d->dispatches());
  }
  printf(fails ? "\nSELFTEST FAILED (%d)\n" : "\nselftest OK\n", fails);
  delete d;
  return fails ? 1 : 0;
}
