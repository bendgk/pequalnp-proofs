// gpukit in 30 lines: Hamming distance of every pair among N 256-bit vectors (N*N results), checked on the CPU.
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
