// tricheck — consistency checks of a startab cost file (one byte per labelled graph, 255 = unknown).
//   tricheck COSTS.bin P [--not] [--sample K] [--lower L] [--cheap L] [-j T]
//   --lower L: entries 255 (not reached) are known to be >= L.   --cheap L: instead of a sample, ALL pairs with
//   size(a) + size(b) + 1 < L (for a table that is complete below L: their results must be in the table).
// P = number of points (n*m).  Checks, over ALL pairs of functions (P <= 16) or K random pairs (larger P):
//   (1) subadditivity: size(a AND b), size(a OR b) <= size(a) + size(b) + 1      (--not: size(NOT a) <= size(a) + 1)
//   (2) local derivability: every function of size r >= 2 is  a AND b / a OR b  (--not: or NOT a)  with
//       size(a), size(b) <= r-1 and size(a) + size(b) + 1 >= r     (the two operands of its output gate)
// Neither proves the table, but any error in a table entry tends to break one of them.
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: tricheck COSTS.bin P [--not] [--sample K] [--lower L] [-j T]\n"); return 2; }
  int P = atoi(argv[2]);
  bool withNot = false; uint64_t sample = 0; int T = getenv("PNP_THREADS") ? atoi(getenv("PNP_THREADS")) : 1;
  int lowerUnknown = 0;      // --lower L: entries 255 (not reached) are known to be >= L
  int cheap = 0;             // --cheap L: test ALL pairs with size(a) + size(b) + 1 < L (implies --lower L)
  for (int i = 3; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--not") withNot = true;
    else if (a == "--sample" && i + 1 < argc) sample = strtoull(argv[++i], nullptr, 10);
    else if (a == "-j" && i + 1 < argc) T = atoi(argv[++i]);
    else if (a == "--lower" && i + 1 < argc) lowerUnknown = atoi(argv[++i]);
    else if (a == "--cheap" && i + 1 < argc) { cheap = atoi(argv[++i]); lowerUnknown = cheap; }
  }
  size_t F = (size_t)1 << P;
  std::vector<uint8_t> c(F);
  FILE* f = fopen(argv[1], "rb");
  if (!f || fread(c.data(), 1, F, f) != F) { fprintf(stderr, "cannot read %zu bytes from %s\n", F, argv[1]); return 2; }
  fclose(f);
  const uint32_t FULL = (uint32_t)(F - 1);
  if (P > 16 && !sample && !cheap) sample = 2000000000ull;
  std::atomic<uint64_t> bad1{0}, pairs{0};
  std::vector<std::atomic<uint8_t>> ok(F);
  for (size_t i = 0; i < F; i++) ok[i].store(0);
  auto test = [&](uint32_t a, uint32_t b) {
    int ca = c[a], cb = c[b];
    if (ca == 255 || cb == 255) return;
    for (int op = 0; op < 2; op++) {
      uint32_t t = op ? (a | b) : (a & b);
      int ct = c[t];
      // an unknown entry (255) is only known to be >= lowerUnknown
      if ((ct != 255 && ct > ca + cb + 1) || (ct == 255 && lowerUnknown > ca + cb + 1)) { if (bad1++ < 5) fprintf(stderr, "subadditivity violated: size(%x %s %x)=%d > %d+%d+1\n", a, op ? "|" : "&", b, ct, ca, cb); }
      if (ct != 255 && ct >= 2 && ca <= ct - 1 && cb <= ct - 1 && !ok[t].load(std::memory_order_relaxed)) ok[t].store(1, std::memory_order_relaxed);
    }
  };
  std::vector<std::vector<uint32_t>> byCost(256);
  if (cheap) for (size_t a = 0; a < F; a++) if (c[a] < cheap) byCost[c[a]].push_back((uint32_t)a);
  std::vector<std::thread> th;
  for (int t = 0; t < T; t++) th.emplace_back([&, t] {
    uint64_t n = 0;
    if (cheap) {
      // every pair with size(a) + size(b) + 1 < cheap: the result must be in the table with at most that size
      for (int ca = 0; 2 * ca + 1 < cheap; ca++)
        for (int cb = ca; ca + cb + 1 < cheap; cb++)
          for (size_t i = t; i < byCost[ca].size(); i += T)
            for (uint32_t b : byCost[cb]) { test(byCost[ca][i], b); n++; }
    } else if (!sample) {
      for (size_t a = t; a < F; a += T) for (size_t b = a; b < F; b++) { test((uint32_t)a, (uint32_t)b); n++; }
    } else {
      uint64_t s = 0x9E3779B97F4A7C15ull * (t + 1);
      auto rnd = [&] { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; };
      for (uint64_t i = 0; i < sample / T; i++) { test((uint32_t)(rnd() & FULL), (uint32_t)(rnd() & FULL)); n++; }
    }
    pairs += n;
  });
  for (auto& x : th) x.join();
  uint64_t bad2 = 0, badn = 0, checked2 = 0;
  if (withNot) for (size_t a = 0; a < F; a++) {
    uint32_t t = FULL & ~(uint32_t)a;
    if (c[a] != 255 && ((c[t] != 255 && c[t] > c[a] + 1) || (c[t] == 255 && lowerUnknown > c[a] + 1))) { if (badn++ < 5) fprintf(stderr, "size(NOT %zx)=%d > %d+1\n", a, c[t], c[a]); }
    if (c[a] != 255 && c[t] != 255 && c[t] >= 2 && c[a] <= c[t] - 1) ok[t].store(1);
  }
  if (!sample && !cheap) for (size_t t = 0; t < F; t++) if (c[t] != 255 && c[t] >= 2) { checked2++; if (!ok[t].load()) { if (bad2++ < 5) fprintf(stderr, "function %zx of size %d has no pair of cheaper operands\n", t, c[t]); } }
  printf("tricheck: P=%d functions=%zu pairs=%llu %s: subadditivity violations %llu, NOT violations %llu, local-derivability failures %llu of %llu%s\n",
         P, F, (unsigned long long)pairs.load(), cheap ? "(all pairs with size(a)+size(b)+1 below the bound)" : sample ? "(random sample)" : "(all pairs)", (unsigned long long)bad1.load(),
         (unsigned long long)badn, (unsigned long long)bad2, (unsigned long long)checked2, (sample || cheap) ? " (not checked in this mode)" : "");
  return (bad1 || bad2 || badn) ? 1 : 0;
}
