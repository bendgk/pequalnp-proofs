// gpuopt — GPU-accelerated don't-care circuit shrinker (heuristic search, exact checking; output always re-verified).
//   gpuopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [--time S] [--rounds R] [--seed X] [--target SIZE] [--cpu] [--check]
// Every wire is a P-bit column over the spec's points. Per round:
//   CPU  simulate, exact care mask C_g of every gate (re-simulate the fanout cone with g complemented)
//   GPU  "singles": for every (target gate, wire) four exact flags (w / ~w has no false positive / no false negative on C_g)
//   GPU  "pairs":   for every job (gate p, fan-in f to get rid of) and every admissible literal i: best partner j such that
//                   op(i, j) equals p on C_p, over ALL admissible j (exhaustive), plus the number of feasible partners
//   CPU  apply moves (replace a gate by a wire / kill a gate by re-expressing all its parents / size-neutral rewrites),
//        each one checked by a full re-simulation before it is kept.
// See docs/gpuopt.md.
#include "../../include/ckt.hpp"
#include "../gpukit/gpu.hpp"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <dirent.h>
#include <unordered_map>

using namespace pnp;
typedef uint32_t u32;
typedef uint8_t u8;

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

struct Rng {
  u64 s;
  explicit Rng(u64 seed = 1) : s(seed * 0x9E3779B97F4A7C15ull + 0x1234567ull) { next(); next(); }
  u64 next() { u64 z = (s += 0x9E3779B97F4A7C15ull); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31); }
  u32 below(u32 n) { return n ? (u32)(((next() >> 32) * (u64)n) >> 32) : 0; }
  double unif() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

// ------------------------------------------------------------------------------------------------ kernels (MSL)
static const char* kMSL = R"(
#include <metal_stdlib>
using namespace metal;
// flags bit0: w has no false positive   (w & ~T & C == 0)      -> usable as an OR operand
//       bit1: ~w has no false positive  (~w & ~T & C == 0)
//       bit2: w has no false negative   (~w & T & C == 0)      -> usable as an AND operand
//       bit3: ~w has no false negative  (w & T & C == 0)
kernel void singles(device const ulong *cols [[buffer(0)]], device const ulong *TC1 [[buffer(1)]], device const ulong *TC0 [[buffer(2)]],
                    device uchar *flags [[buffer(3)]], constant uint &NW [[buffer(4)]], constant uint &WT [[buffer(5)]],
                    constant uint &t0 [[buffer(6)]], uint2 gid [[thread_position_in_grid]]) {
    uint t = t0 + gid.y, w = gid.x;
    uint xb = w * NW, mb = t * NW;
    ulong a0 = 0, a1 = 0, a2 = 0, a3 = 0;
    for (uint k = 0; k < NW; k++) {
        ulong v = cols[xb + k], p1 = TC1[mb + k], p0 = TC0[mb + k];
        a0 |= v & p0; a1 |= ~v & p0; a2 |= ~v & p1; a3 |= v & p1;
        if ((k & 7u) == 7u && a0 != 0ul && a1 != 0ul && a2 != 0ul && a3 != 0ul) break;
    }
    flags[t * WT + w] = uchar((a0 == 0ul ? 1u : 0u) | (a1 == 0ul ? 2u : 0u) | (a2 == 0ul ? 4u : 0u) | (a3 == 0ul ? 8u : 0u));
}
// entry e: entA = lit(16) | score(8) << 16 | kind << 31 (0 = OR list, 1 = AND list); entB = target; entC = end of e's list.
// out[2e] = best partner entry (max score sum, lowest index on ties) or 0xFFFFFFFF; out[2e+1] = number of feasible partners.
kernel void pairs(device const ulong *cols [[buffer(0)]], device const ulong *TC1 [[buffer(1)]], device const ulong *TC0 [[buffer(2)]],
                  device const uint *entA [[buffer(3)]], device const uint *entB [[buffer(4)]], device const uint *entC [[buffer(5)]],
                  device uint *out [[buffer(6)]], constant uint &NW [[buffer(7)]], constant uint &e0 [[buffer(8)]],
                  uint gid [[thread_position_in_grid]]) {
    uint e = e0 + gid;
    uint A = entA[e], t = entB[e], end = entC[e];
    uint kind = A >> 31, lit = A & 0xFFFFu;
    ulong fi = (((lit & 1u) ^ (kind ^ 1u)) != 0u) ? ~0ul : 0ul;
    uint ci = (lit >> 1) * NW, mb = t * NW;
    uint k0 = NW; ulong r0 = 0;
    for (uint k = 0; k < NW; k++) {
        ulong m = (kind != 0u) ? TC0[mb + k] : TC1[mb + k];
        ulong r = m & (cols[ci + k] ^ fi);
        if (r != 0ul) { k0 = k; r0 = r; break; }
    }
    uint best = 0xFFFFFFFFu, bestS = 0, cnt = 0;
    if (k0 < NW) {
        uint si = (A >> 16) & 0xFFu;
        for (uint e2 = e + 1; e2 < end; e2++) {
            uint A2 = entA[e2], lit2 = A2 & 0xFFFFu;
            ulong f2 = (((lit2 & 1u) ^ (kind ^ 1u)) != 0u) ? ~0ul : 0ul;
            uint c2 = (lit2 >> 1) * NW;
            if ((r0 & (cols[c2 + k0] ^ f2)) != 0ul) continue;
            bool ok = true;
            for (uint k = k0 + 1; k < NW; k++) {
                ulong m = (kind != 0u) ? TC0[mb + k] : TC1[mb + k];
                if ((m & (cols[ci + k] ^ fi) & (cols[c2 + k] ^ f2)) != 0ul) { ok = false; break; }
            }
            if (ok) { cnt++; uint s = si + ((A2 >> 16) & 0xFFu); if (best == 0xFFFFFFFFu || s > bestS) { best = e2; bestS = s; } }
        }
    }
    out[2 * e] = best; out[2 * e + 1] = cnt;
}
// 2-level terms for OR covers: entry e = wire i that is NOT admissible alone; over ALL other wires j of the same list
// (entD = list begin, entC = list end) with (i & j) free of false positives on the care set: the partner with the
// largest coverage popcount(T & C & i & j) > 0.  out[2e] = partner entry or 0xFFFFFFFF, out[2e+1] = its coverage.
kernel void prods(device const ulong *cols [[buffer(0)]], device const ulong *TC1 [[buffer(1)]], device const ulong *TC0 [[buffer(2)]],
                  device const uint *entA [[buffer(3)]], device const uint *entB [[buffer(4)]], device const uint *entC [[buffer(5)]],
                  device uint *out [[buffer(6)]], constant uint &NW [[buffer(7)]], constant uint &e0 [[buffer(8)]],
                  device const uint *entD [[buffer(9)]], uint gid [[thread_position_in_grid]]) {
    uint e = e0 + gid;
    uint t = entB[e], end = entC[e], beg = entD[e];
    uint ci = (entA[e] & 0xFFFFu) * NW, mb = t * NW;
    // words where wire i covers on-points (the on-set of a gate is small): at most 16 kept, else the slow path
    uint kc[16]; ulong vc[16]; uint nc = 0; bool more = false;
    for (uint k = 0; k < NW; k++) {
        ulong c = TC1[mb + k] & cols[ci + k];
        if (c != 0ul) { if (nc < 16u) { kc[nc] = k; vc[nc] = c; nc++; } else more = true; }
    }
    uint best = 0xFFFFFFFFu, bestC = 0;
    if (nc != 0u) {
        for (uint e2 = beg; e2 < end; e2++) {
            if (e2 == e) continue;
            uint c2 = (entA[e2] & 0xFFFFu) * NW;
            uint cov = 0;
            if (more) { for (uint k = 0; k < NW; k++) cov += uint(popcount(TC1[mb + k] & cols[ci + k] & cols[c2 + k])); }
            else { for (uint q = 0; q < nc; q++) cov += uint(popcount(vc[q] & cols[c2 + kc[q]])); }
            if (cov <= bestC) continue;                       // cannot improve: skip the false-positive scan
            bool ok = true;
            for (uint k = 0; k < NW; k++) if ((TC0[mb + k] & cols[ci + k] & cols[c2 + k]) != 0ul) { ok = false; break; }
            if (ok) { bestC = cov; best = e2; }
        }
    }
    out[2 * e] = best; out[2 * e + 1] = bestC;
}
)";

// ------------------------------------------------------------------------------------------------ CPU references (same results)
static void cpu_singles(const u64* cols, const u64* TC1, const u64* TC0, u8* flags, u32 NW, u32 WT, u32 t0, u32 t1) {
  for (u32 t = t0; t < t1; t++) {
    const u64 *m1 = TC1 + (size_t)t * NW, *m0 = TC0 + (size_t)t * NW;
    for (u32 w = 0; w < WT; w++) {
      const u64* x = cols + (size_t)w * NW;
      u64 a0 = 0, a1 = 0, a2 = 0, a3 = 0;
      for (u32 k = 0; k < NW; k++) {
        u64 v = x[k], p1 = m1[k], p0 = m0[k];
        a0 |= v & p0; a1 |= ~v & p0; a2 |= ~v & p1; a3 |= v & p1;
        if ((k & 7u) == 7u && a0 && a1 && a2 && a3) break;
      }
      flags[(size_t)t * WT + w] = (u8)((a0 == 0) | ((a1 == 0) << 1) | ((a2 == 0) << 2) | ((a3 == 0) << 3));
    }
  }
}
static void cpu_pairs(const u64* cols, const u64* TC1, const u64* TC0, const u32* entA, const u32* entB, const u32* entC, u32* out, u32 NW, u32 e0, u32 e1) {
  for (u32 e = e0; e < e1; e++) {
    u32 A = entA[e], t = entB[e], end = entC[e];
    u32 kind = A >> 31, lit = A & 0xFFFFu;
    u64 fi = ((lit & 1u) ^ (kind ^ 1u)) ? ~u64(0) : 0;
    const u64* xi = cols + (size_t)(lit >> 1) * NW;
    const u64* M = (kind ? TC0 : TC1) + (size_t)t * NW;
    u32 k0 = NW; u64 r0 = 0;
    for (u32 k = 0; k < NW; k++) { u64 r = M[k] & (xi[k] ^ fi); if (r) { k0 = k; r0 = r; break; } }
    u32 best = 0xFFFFFFFFu, bestS = 0, cnt = 0;
    if (k0 < NW) {
      u32 si = (A >> 16) & 0xFFu;
      for (u32 e2 = e + 1; e2 < end; e2++) {
        u32 A2 = entA[e2], lit2 = A2 & 0xFFFFu;
        u64 f2 = ((lit2 & 1u) ^ (kind ^ 1u)) ? ~u64(0) : 0;
        const u64* x2 = cols + (size_t)(lit2 >> 1) * NW;
        if (r0 & (x2[k0] ^ f2)) continue;
        bool ok = true;
        for (u32 k = k0 + 1; k < NW; k++) if (M[k] & (xi[k] ^ fi) & (x2[k] ^ f2)) { ok = false; break; }
        if (ok) { cnt++; u32 s = si + ((A2 >> 16) & 0xFFu); if (best == 0xFFFFFFFFu || s > bestS) { best = e2; bestS = s; } }
      }
    }
    out[2 * (size_t)e] = best; out[2 * (size_t)e + 1] = cnt;
  }
}

static void cpu_prods(const u64* cols, const u64* TC1, const u64* TC0, const u32* entA, const u32* entB, const u32* entC, const u32* entD, u32* out, u32 NW, u32 e0, u32 e1) {
  for (u32 e = e0; e < e1; e++) {
    u32 t = entB[e], end = entC[e], beg = entD[e];
    const u64 *xi = cols + (size_t)(entA[e] & 0xFFFFu) * NW, *M0 = TC0 + (size_t)t * NW, *M1 = TC1 + (size_t)t * NW;
    u32 kc[16]; u64 vc[16]; u32 nc = 0; bool more = false;
    for (u32 k = 0; k < NW; k++) { u64 c = M1[k] & xi[k]; if (c) { if (nc < 16) { kc[nc] = k; vc[nc] = c; nc++; } else more = true; } }
    u32 best = 0xFFFFFFFFu, bestC = 0;
    if (nc) {
      for (u32 e2 = beg; e2 < end; e2++) {
        if (e2 == e) continue;
        const u64* x2 = cols + (size_t)(entA[e2] & 0xFFFFu) * NW;
        u32 cov = 0;
        if (more) { for (u32 k = 0; k < NW; k++) cov += (u32)__builtin_popcountll(M1[k] & xi[k] & x2[k]); }
        else { for (u32 q = 0; q < nc; q++) cov += (u32)__builtin_popcountll(vc[q] & x2[kc[q]]); }
        if (cov <= bestC) continue;
        bool ok = true;
        for (u32 k = 0; k < NW; k++) if (M0[k] & xi[k] & x2[k]) { ok = false; break; }
        if (ok) { bestC = cov; best = e2; }
      }
    }
    out[2 * (size_t)e] = best; out[2 * (size_t)e + 1] = bestC;
  }
}

// ------------------------------------------------------------------------------------------------ netlist
struct Gt { u8 op; int a, b; };   // wires; NOT reads a (b == a)
struct Net {
  int N = 0;
  std::vector<Gt> g;              // gate id i drives wire N + i
  std::vector<int> outs;
  int wires() const { return N + (int)g.size(); }
};

static Net normalize(const Circuit& c) {      // Lean semantics -> clean net (two existing earlier operands, no constants/copies)
  Net n; n.N = c.N;
  const int C0 = -1, C1 = -2;
  std::vector<int> map((size_t)c.N + c.gates.size());
  for (int i = 0; i < c.N; i++) map[i] = i;
  auto mk = [&](u8 op, int a, int b) { n.g.push_back({op, a, b}); return n.N + (int)n.g.size() - 1; };
  for (size_t j = 0; j < c.gates.size(); j++) {
    const Gate& g = c.gates[j];
    int cur = c.N + (int)j, r;
    auto rd = [&](int w) { return (w >= 0 && w < cur) ? map[w] : C0; };
    if (g.op == NOT) { int a = g.nin >= 1 ? rd(g.a) : C0; r = a == C0 ? C1 : a == C1 ? C0 : mk(NOT, a, a); }
    else if (g.nin == 0) r = g.op == AND ? C1 : C0;
    else if (g.nin == 1) r = rd(g.a);
    else {
      int a = rd(g.a), b = rd(g.b);
      if (g.op == AND) { if (a == C0 || b == C0) r = C0; else if (a == C1) r = b; else if (b == C1) r = a; else if (a == b) r = a; else r = mk(AND, a, b); }
      else { if (a == C1 || b == C1) r = C1; else if (a == C0) r = b; else if (b == C0) r = a; else if (a == b) r = a; else r = mk(OR, a, b); }
    }
    map[cur] = r;
  }
  size_t tot = (size_t)c.N + c.gates.size();
  for (int o : c.outs) {
    int w = (o >= 0 && (size_t)o < tot) ? map[o] : C0;
    if (w < 0) die("gpuopt: an output is constant; nothing to optimise");
    n.outs.push_back(w);
  }
  return n;
}
static Circuit to_circuit(const Net& n) {
  Circuit c; c.N = n.N;
  for (auto& g : n.g) { Gate q; q.op = (Op)g.op; q.nin = g.op == NOT ? 1 : 2; q.a = g.a; q.b = g.op == NOT ? 0 : g.b; c.gates.push_back(q); }
  c.outs = n.outs;
  return c;
}

// live gates in topological order; false if the net has a cycle
static bool topo(const Net& n, std::vector<int>& order, std::vector<u8>& st, std::vector<int>& stack) {
  size_t G = n.g.size();
  st.assign(G, 0); order.clear(); stack.clear();
  for (int o : n.outs) {
    if (o < n.N || st[o - n.N] == 2) continue;
    stack.push_back(o - n.N);
    while (!stack.empty()) {
      int id = stack.back();
      if (st[id] == 2) { stack.pop_back(); continue; }
      if (st[id] == 1) { st[id] = 2; order.push_back(id); stack.pop_back(); continue; }
      st[id] = 1;
      const Gt& g = n.g[id];
      for (int f : {g.a, g.b}) {
        if (f < n.N) continue;
        u8 s = st[f - n.N];
        if (s == 1) return false;            // back edge
        if (s == 0) stack.push_back(f - n.N);
      }
    }
  }
  return true;
}

struct Sim {
  const Spec* sp; size_t NW; u64 lm;
  void gate(const Gt& g, const u64* A, const u64* B, u64* O) const {
    if (g.op == NOT) { for (size_t w = 0; w < NW; w++) O[w] = ~A[w]; O[NW - 1] &= lm; }
    else if (g.op == AND) for (size_t w = 0; w < NW; w++) O[w] = A[w] & B[w];
    else for (size_t w = 0; w < NW; w++) O[w] = A[w] | B[w];
  }
  void run(const Net& n, const std::vector<int>& order, u64* cols) const {
    for (int id : order) { const Gt& g = n.g[id]; gate(g, cols + (size_t)g.a * NW, cols + (size_t)g.b * NW, cols + (size_t)(n.N + id) * NW); }
  }
  bool ok(const Net& n, const u64* cols) const {
    for (int k = 0; k < sp->K; k++) {
      const u64* o = cols + (size_t)n.outs[k] * NW;
      for (size_t w = 0; w < NW; w++) if ((o[w] ^ sp->tgt[k][w]) & sp->care[k][w]) return false;
    }
    return true;
  }
};

static u64 colhash(const u64* c, size_t NW) { u64 h = 0x9E3779B97F4A7C15ull; for (size_t w = 0; w < NW; w++) { h ^= c[w]; h *= 0xBF58476D1CE4E5B9ull; h ^= h >> 29; } return h; }

// Rebuild: drop dead gates, renumber in topological order, structural hashing, merge wires with identical columns
// (identical on ALL points, so interchangeable everywhere). cols receives the simulation of the result; only the
// input columns have to be valid on entry.
static void compact(Net& n, const Sim& sim, u64* cols) {
  size_t NW = sim.NW;
  std::vector<int> order; std::vector<u8> st; std::vector<int> stack;
  std::vector<u64> tmp(NW);
  for (int pass = 0; pass < 16; pass++) {
    if (!topo(n, order, st, stack)) die("gpuopt internal: cycle in compact");
    Net m; m.N = n.N;
    std::vector<int> remap(n.wires(), -1);
    for (int i = 0; i < n.N; i++) remap[i] = i;
    std::unordered_map<u64, int> shash;
    std::unordered_multimap<u64, int> fhash;
    for (int i = 0; i < n.N; i++) fhash.insert({colhash(cols + (size_t)i * NW, NW), i});
    for (int id : order) {
      Gt g = n.g[id];
      int a = remap[g.a], b = remap[g.b], r = -1;
      if (g.op == NOT) { b = a; if (a >= m.N && m.g[a - m.N].op == NOT) r = m.g[a - m.N].a; }
      else { if (a > b) std::swap(a, b); if (a == b) r = a; }
      u64 key = ((u64)g.op << 60) ^ ((u64)a << 30) ^ (u64)b;
      if (r < 0) { auto it = shash.find(key); if (it != shash.end()) r = it->second; }
      if (r < 0) {
        int w = m.N + (int)m.g.size();      // new columns only ever read columns < w, all written in this pass
        Gt q{g.op, a, b};
        sim.gate(q, cols + (size_t)a * NW, cols + (size_t)b * NW, tmp.data());
        u64 h = colhash(tmp.data(), NW);
        auto range = fhash.equal_range(h);
        for (auto it = range.first; it != range.second; ++it)
          if (!memcmp(cols + (size_t)it->second * NW, tmp.data(), NW * 8)) { r = it->second; break; }
        if (r < 0) { memcpy(cols + (size_t)w * NW, tmp.data(), NW * 8); m.g.push_back(q); shash[key] = w; fhash.insert({h, w}); r = w; }
      }
      remap[n.N + id] = r;
    }
    bool merged = m.g.size() != order.size();
    for (int& o : n.outs) o = remap[o];
    m.outs = n.outs;
    n = std::move(m);
    if (!merged) break;                      // nothing merged: every gate is live and in topological order
  }
}

// Chunks a 1D range so that the ESTIMATED work of one dispatch stays near a budget, and adapts the budget to the
// measured GPU time (target 12 ms). Thread cost in the pair / product kernels varies by orders of magnitude between
// gates, so pacing by item count alone gave dispatches of 340 ms.
struct WorkPacer {
  double budget, target;
  explicit WorkPacer(double start, double targetSec = 0.012) : budget(start), target(targetSec) {}
  template <class F> u32 chunk(u32 e, u32 E, F work) const {
    double acc = 0; u32 n = 0;
    while (e + n < E && (n == 0 || acc + work(e + n) <= budget)) { acc += work(e + n); n++; }
    return n;
  }
  void feed(double sec) {
    if (sec <= 0) { budget *= 2; return; }
    double f = target / sec;
    if (f < 0.5) budget *= f;                 // overshoot by more than 2x: correct at once
    else budget *= 0.5 + 0.5 * (f > 2 ? 2 : f);
    if (budget < 1) budget = 1;
  }
};

// ------------------------------------------------------------------------------------------------ engine
struct Options {
  std::string spec, in, out, basis = "aon", found;
  double timeLimit = 50;
  long rounds = -1;
  u64 seed = 1;
  int target = -1;
  bool cpu = false, check = false, neg = true, stats = false;
  double neutral = 0.05;     // fraction of gates given one size-neutral rewrite per round
  int tries = 3;             // alternatives tried per parent when a kill does not verify
  size_t capE = 3u << 20;    // pair-list entries per round
  bool covers = true, pairs = true, twoLevel = true;
  int twoEvery = 0, twoMax = 48, twoOnWords = 16;   // 0 = off (measured: no gain, see docs);  // 2-level terms: every K-th round, at most M terms per gate offered to the cover search
  int maxLits = 256;         // widest literal list given to the exact cover search
  long bbBudget = 800;       // branch-and-bound nodes per cover search
  int chain = 6, maxParents = 4;
  int verbose = 1;
};

struct Job { int p, f; u32 ob, oe, ab, ae; };
struct Cand { u32 score; int op, la, lb; };   // p := op(la, lb), literals = wire*2 + neg

struct Engine {
  const Spec& sp; Options o; Sim sim; size_t NW;
  gpukit::Device* dev = nullptr;
  gpukit::Kernel kS, kP, kQ;
  gpukit::Buffer bCols, bCols2, bTC1, bTC0, bFlags, bEntA, bEntB, bEntC, bOut;
  gpukit::Buffer bPA, bPB, bPC, bPD, bPOut;      // product lists (2-level terms)
  std::vector<u32> prodBeg, prodEnd;
  WorkPacer wpPairs{1e5}, wpProds{3e4};
  long prodSkipped = 0;
  double tProds = 0, gProds = 0, prodTests = 0, prodFound = 0; long aTwo = 0, gTwo = 0;
  size_t capW = 0, capG = 0;
  Net net;
  Rng rng;
  // per-round analysis
  std::vector<std::vector<int>> parents;   // by wire: gate ids reading it
  std::vector<u8> isOut;
  std::vector<u64> tfo; size_t GW = 0;      // per gate: bitset over gate ids
  std::vector<u64> scr; std::vector<u32> stamp; u32 curStamp = 0;
  std::vector<Job> jobs;
  std::vector<int> order; std::vector<u8> st; std::vector<int> stack;
  // stats
  double tCare = 0, tSingles = 0, tPairs = 0, tLists = 0, tMoves = 0, gSingles = 0, gPairs = 0, tCompact = 0;
  double maxDispatch = 0, deadline = 1e300;
  bool late() const { return now() > deadline; }
  long nDispatch = 0;
  long aSingle = 0, aKill = 0, aNeutral = 0, gSingle = 0, gKill = 0, tried = 0, failVerify = 0, failCycle = 0, failGain = 0;
  long aCover = 0, gCover = 0, aCKill = 0, gCKill = 0;
  double pairTests = 0, feasPairs = 0, entriesTot = 0, singleTests = 0;

  Engine(const Spec& s, const Options& op) : sp(s), o(op), rng(op.seed) { sim.sp = &sp; sim.NW = NW = sp.W; sim.lm = sp.lastmask(); }

  gpukit::Buffer alloc(size_t bytes) {
    gpukit::Buffer b;
    if (dev) { std::string err; b = dev->alloc(bytes, &err); if (!b) die(err); }
    else { b.data = aligned_alloc(16384, (bytes + 16383) / 16384 * 16384); if (!b.data) die("out of memory"); memset(b.data, 0, bytes); b.bytes = bytes; }
    return b;
  }
  void init(const Net& start) {
    net = start;
    if (!o.cpu) {
      std::string err;
      dev = gpukit::Device::open(&err);
      if (!dev) die("gpuopt: " + err + " (use --cpu)");
      kS = dev->compile(kMSL, "singles", &err); if (!kS) die(err);
      kP = dev->compile(kMSL, "pairs", &err); if (!kP) die(err);
      kQ = dev->compile(kMSL, "prods", &err); if (!kQ) die(err);
    }
    size_t G0 = net.g.size();
    capG = G0 + G0 / 8 + 256;
    capW = net.N + capG;
    if (capW * 2 >= 65536) die("gpuopt: more than 32767 wires is not supported (16-bit literal ids)");
    bCols = alloc(capW * NW * 8); bCols2 = alloc(capW * NW * 8);
    bTC1 = alloc(capG * NW * 8); bTC0 = alloc(capG * NW * 8);
    bFlags = alloc(capG * capW);
    bEntA = alloc(o.capE * 4); bEntB = alloc(o.capE * 4); bEntC = alloc(o.capE * 4); bOut = alloc(o.capE * 8);
    bPA = alloc(o.capE * 4); bPB = alloc(o.capE * 4); bPC = alloc(o.capE * 4); bPD = alloc(o.capE * 4); bPOut = alloc(o.capE * 8);
    for (auto* b : {&bCols, &bCols2})
      for (int i = 0; i < net.N; i++) memcpy(b->as<u64>() + (size_t)i * NW, sp.in[i].data(), NW * 8);
    scr.resize(capG * NW); stamp.assign(capW, 0);
    compact(net, sim, cols());
    if (!sim.ok(net, cols())) die("gpuopt: the input circuit does not satisfy the spec");
  }
  u64* cols() { return bCols.as<u64>(); }

  // ---- analysis ----
  void analyze() {
    int N = net.N, G = (int)net.g.size();
    parents.assign(N + G, {}); isOut.assign(N + G, 0);
    for (int id = 0; id < G; id++) { const Gt& g = net.g[id]; parents[g.a].push_back(id); if (g.b != g.a) parents[g.b].push_back(id); }
    for (int w : net.outs) isOut[w] = 1;
    GW = (G + 63) / 64;
    tfo.assign((size_t)G * GW, 0);
    for (int id = G - 1; id >= 0; id--) {
      u64* t = &tfo[(size_t)id * GW];
      for (int p : parents[N + id]) { const u64* q = &tfo[(size_t)p * GW]; for (size_t w = 0; w < GW; w++) t[w] |= q[w]; t[p >> 6] |= u64(1) << (p & 63); }
    }
  }
  bool inTfo(int x, int h) const { return (tfo[(size_t)x * GW + (h >> 6)] >> (h & 63)) & 1; }

  void careMasks() {      // exact observability of every gate -> TC1 = col & care, TC0 = ~col & care
    int N = net.N, G = (int)net.g.size();
    u64 *C = cols(), *T1 = bTC1.as<u64>(), *T0 = bTC0.as<u64>();
    std::vector<u64> care(NW);
    for (int g = 0; g < G; g++) {
      if (++curStamp == 0) { std::fill(stamp.begin(), stamp.end(), 0); curStamp = 1; }
      u64* Sg = &scr[(size_t)g * NW]; const u64* Cg = C + (size_t)(N + g) * NW;
      for (size_t w = 0; w < NW; w++) Sg[w] = ~Cg[w];
      Sg[NW - 1] &= sim.lm;
      stamp[N + g] = curStamp;
      const u64* tf = &tfo[(size_t)g * GW];
      for (size_t ww = 0; ww < GW; ww++) {
        u64 bits = tf[ww];
        while (bits) {
          int h = (int)(ww * 64 + __builtin_ctzll(bits)); bits &= bits - 1;
          const Gt& q = net.g[h];
          bool da = stamp[q.a] == curStamp, db = stamp[q.b] == curStamp;
          if (!da && !db) continue;
          const u64* A = da ? &scr[(size_t)(q.a - N) * NW] : C + (size_t)q.a * NW;
          const u64* B = db ? &scr[(size_t)(q.b - N) * NW] : C + (size_t)q.b * NW;
          u64* O = &scr[(size_t)h * NW];
          sim.gate(q, A, B, O);
          if (memcmp(O, C + (size_t)(N + h) * NW, NW * 8)) stamp[N + h] = curStamp;
        }
      }
      std::fill(care.begin(), care.end(), 0);
      for (int k = 0; k < sp.K; k++) {
        int ow = net.outs[k];
        if (ow < N || stamp[ow] != curStamp) continue;
        const u64 *x = &scr[(size_t)(ow - N) * NW], *y = C + (size_t)ow * NW;
        for (size_t w = 0; w < NW; w++) care[w] |= (x[w] ^ y[w]) & sp.care[k][w];
      }
      for (size_t w = 0; w < NW; w++) { T1[(size_t)g * NW + w] = Cg[w] & care[w]; T0[(size_t)g * NW + w] = ~Cg[w] & care[w]; }
    }
  }

  // ---- GPU / CPU kernels ----
  void runSingles() {
    u32 G = (u32)net.g.size(), WT = (u32)net.wires();
    double t0 = now();
    if (dev) {
      gpukit::Pacer pc(std::max<u32>(1, G / 8), 1, G, 0.020);
      for (u32 t = 0; t < G;) {
        u32 n = (u32)std::min<size_t>(pc.n, G - t);
        gpukit::Args a; a.buf(0, bCols).buf(1, bTC1).buf(2, bTC0).buf(3, bFlags).u32(4, (u32)NW).u32(5, WT).u32(6, t);
        std::string err; double s = dev->run2d(kS, a, WT, n, &err);
        if (s < 0) die(err);
        gSingles += s; nDispatch++; maxDispatch = std::max(maxDispatch, s);
        pc.next(n, s); t += n;
      }
      if (o.check) {
        std::vector<u8> ref((size_t)G * WT);
        cpu_singles(cols(), bTC1.as<u64>(), bTC0.as<u64>(), ref.data(), (u32)NW, WT, 0, G);
        if (memcmp(ref.data(), bFlags.data, ref.size())) die("CHECK FAILED: GPU singles differ from the CPU reference");
      }
    } else cpu_singles(cols(), bTC1.as<u64>(), bTC0.as<u64>(), bFlags.as<u8>(), (u32)NW, WT, 0, G);
    singleTests += (double)G * WT;
    tSingles += now() - t0;
  }
  void runPairs(u32 E) {
    double t0 = now();
    if (!E) return;
    if (dev) {
      const u32* EC = bEntC.as<u32>();
      double nw = (double)NW;
      for (u32 e = 0; e < E;) {
        u32 n = wpPairs.chunk(e, E, [&](u32 i) { return (double)(EC[i] - i) + nw; });
        gpukit::Args a; a.buf(0, bCols).buf(1, bTC1).buf(2, bTC0).buf(3, bEntA).buf(4, bEntB).buf(5, bEntC).buf(6, bOut).u32(7, (u32)NW).u32(8, e);
        std::string err; double s = dev->run1d(kP, a, n, &err);
        if (s < 0) die(err);
        gPairs += s; nDispatch++; maxDispatch = std::max(maxDispatch, s);
        wpPairs.feed(s); e += n;
      }
      if (o.check) {
        std::vector<u32> ref((size_t)E * 2);
        cpu_pairs(cols(), bTC1.as<u64>(), bTC0.as<u64>(), bEntA.as<u32>(), bEntB.as<u32>(), bEntC.as<u32>(), ref.data(), (u32)NW, 0, E);
        if (memcmp(ref.data(), bOut.data, ref.size() * 4)) die("CHECK FAILED: GPU pairs differ from the CPU reference");
      }
    } else cpu_pairs(cols(), bTC1.as<u64>(), bTC0.as<u64>(), bEntA.as<u32>(), bEntB.as<u32>(), bEntC.as<u32>(), bOut.as<u32>(), (u32)NW, 0, E);
    tPairs += now() - t0;
  }

  // ---- 2-level terms: for every gate, wires that are not admissible alone but cover something ----
  void runProds() {
    int N = net.N, G = (int)net.g.size(), WT = N + G;
    double t0 = now();
    const u8* F = bFlags.as<u8>();
    u32 *PA = bPA.as<u32>(), *PB = bPB.as<u32>(), *PC = bPC.as<u32>(), *PD = bPD.as<u32>();
    prodBeg.assign(G, 0); prodEnd.assign(G, 0);
    std::vector<float> perEntry(G, 0);
    const u64* T1 = bTC1.as<u64>();
    u32 E = 0;
    for (int p = 0; p < G; p++) {
      const u8* fl = F + (size_t)p * WT; const u64* ex = &tfo[(size_t)p * GW];
      u32 onw = 0;
      for (size_t w = 0; w < NW; w++) onw += T1[(size_t)p * NW + w] != 0;
      if (onw > (u32)o.twoOnWords) { prodSkipped++; continue; }    // wide on-set: every pair would need a full-width scan
      u32 b = E; bool full = false;
      for (int w = 0; w < WT; w++) {
        u8 v = fl[w];
        if ((v & 1) || (v & 8)) continue;                  // admissible alone, or covers nothing
        if (w >= N) { int h = w - N; if (h == p || ((ex[h >> 6] >> (h & 63)) & 1)) continue; }
        if (E + 1 >= o.capE) { full = true; break; }
        PA[E] = (u32)w; PB[E] = (u32)p; E++;
      }
      if (full) { E = b; break; }
      for (u32 e = b; e < E; e++) { PC[e] = E; PD[e] = b; }
      prodBeg[p] = b; prodEnd[p] = E;
      perEntry[p] = (float)((double)(E - b) * (onw > 16 ? NW : onw) + NW);
      prodTests += (double)(E - b) * (E - b > 0 ? E - b - 1 : 0);
    }
    if (E) {
      if (dev) {
        for (u32 e = 0; e < E;) {
          u32 n = wpProds.chunk(e, E, [&](u32 i) { return (double)perEntry[PB[i]]; });
          gpukit::Args a; a.buf(0, bCols).buf(1, bTC1).buf(2, bTC0).buf(3, bPA).buf(4, bPB).buf(5, bPC).buf(6, bPOut).u32(7, (u32)NW).u32(8, e).buf(9, bPD);
          std::string err; double sec = dev->run1d(kQ, a, n, &err);
          if (sec < 0) die(err);
          gProds += sec; nDispatch++; maxDispatch = std::max(maxDispatch, sec);
          wpProds.feed(sec); e += n;
          if (late() && e < E) {                              // out of time: drop the gates not finished
            for (int p = 0; p < G; p++) if (prodEnd[p] > e) prodBeg[p] = prodEnd[p] = 0;
            E = e; break;
          }
        }
        if (o.check) {
          std::vector<u32> ref((size_t)E * 2);
          cpu_prods(cols(), bTC1.as<u64>(), bTC0.as<u64>(), PA, PB, PC, PD, ref.data(), (u32)NW, 0, E);
          if (memcmp(ref.data(), bPOut.data, ref.size() * 4)) die("CHECK FAILED: GPU prods differ from the CPU reference");
        }
      } else cpu_prods(cols(), bTC1.as<u64>(), bTC0.as<u64>(), PA, PB, PC, PD, bPOut.as<u32>(), (u32)NW, 0, E);
    }
    tProds += now() - t0;
  }

  // ---- candidate lists ----
  std::vector<u8> score;       // per wire
  std::vector<int> notOf;      // wire -> wire of an existing NOT gate reading it, or -1
  u32 buildLists(int rot) {
    int N = net.N, G = (int)net.g.size(), WT = N + G;
    const u8* F = bFlags.as<u8>();
    u32 *EA = bEntA.as<u32>(), *EB = bEntB.as<u32>(), *EC = bEntC.as<u32>();
    score.assign(WT, 0); notOf.assign(WT, -1);
    for (int w = 0; w < WT; w++) {
      int base = w < N ? 190 : 100 + 6 * (int)std::min<size_t>(parents[w].size(), 8);
      score[w] = (u8)(base + rng.below(32));
    }
    for (int id = 0; id < G; id++) if (net.g[id].op == NOT) notOf[net.g[id].a] = N + id;
    bool aon = o.basis == "aon" && o.neg;
    jobs.clear();
    u32 E = 0;
    for (int ii = 0; ii < G; ii++) {
      int p = (ii + rot) % G;
      const Gt& g = net.g[p];
      const u8* fl = F + (size_t)p * WT;
      for (int side = 0; side < 2; side++) {
        int f = side ? g.b : g.a;
        if (side && g.b == g.a) break;
        int x = f >= N ? f - N : p;                       // exclusion: TFO(x) + x  (+ f itself when f is an input)
        const u64* ex = &tfo[(size_t)x * GW];
        Job j; j.p = p; j.f = f;
        u32 lists[2][2];
        bool full = false;
        for (int kind = 0; kind < 2 && !full; kind++) {
          lists[kind][0] = E;
          for (int w = 0; w < WT; w++) {
            u8 v = fl[w];
            bool pos = kind == 0 ? ((v & 1) && !(v & 12)) : ((v & 4) && !(v & 3));
            bool neg = aon && (kind == 0 ? ((v & 2) && !(v & 12)) : ((v & 8) && !(v & 3)));
            if (!pos && !neg) continue;
            if (w == f) continue;
            if (w >= N) { int h = w - N; if (h == x || ((ex[h >> 6] >> (h & 63)) & 1)) continue; }
            if (neg && !pos && (notOf[w] >= 0 || (w >= N && net.g[w - N].op == NOT))) continue;   // the complement is a wire already
            if (E + 2 >= o.capE) { full = true; break; }
            if (pos) { EA[E] = (u32)(w * 2) | ((u32)score[w] << 16) | ((u32)kind << 31); EB[E] = (u32)p; E++; }
            else { EA[E] = (u32)(w * 2 + 1) | ((u32)(10 + (score[w] & 31)) << 16) | ((u32)kind << 31); EB[E] = (u32)p; E++; }
          }
          lists[kind][1] = E;
          for (u32 e = lists[kind][0]; e < E; e++) EC[e] = E;
        }
        if (full) { E = lists[0][0]; goto done; }
        j.ob = lists[0][0]; j.oe = lists[0][1]; j.ab = lists[1][0]; j.ae = lists[1][1];
        jobs.push_back(j);
      }
    }
  done:
    entriesTot += E;
    for (auto& j : jobs) { double a = j.oe - j.ob, b = j.ae - j.ab; pairTests += a * (a - 1) / 2 + b * (b - 1) / 2; }
    return E;
  }
  void sizeStats() {
    int N = net.N, G = (int)net.g.size(), WT = N + G;
    const u8* F = bFlags.as<u8>();
    const u64 *T1 = bTC1.as<u64>(), *T0 = bTC0.as<u64>();
    std::vector<double> L[2], U[2], LU[2]; std::vector<int> mf;
    double sumOut = 0; long singles = 0, zeroCare = 0;
    for (int p = 0; p < G; p++) {
      const u8* fl = F + (size_t)p * WT; const u64* ex = &tfo[(size_t)p * GW];
      for (int kind = 0; kind < 2; kind++) {
        long l = 0, u = 0;
        for (int w = 0; w < WT; w++) {
          u8 v = fl[w];
          bool pos = kind == 0 ? ((v & 1) && !(v & 8)) : ((v & 4) && !(v & 2));
          bool neg = (kind == 0 ? ((v & 2) && !(v & 4)) : ((v & 8) && !(v & 1)));
          if (w >= N) { int h = w - N; if (h == p || ((ex[h >> 6] >> (h & 63)) & 1)) continue; }
          l += pos + (o.neg ? neg : 0);
          if (kind == 0 && (v & 1) && (v & 4)) singles++;
        }
        const u64* M = (kind ? T0 : T1) + (size_t)p * NW;
        for (size_t w = 0; w < NW; w++) u += __builtin_popcountll(M[w]);
        L[kind].push_back(l); U[kind].push_back(u); LU[kind].push_back((double)l * u);
        sumOut += (double)u * ((l + 63) / 64) * 8;
      }
      bool z = true; for (size_t w = 0; w < NW; w++) if (T1[(size_t)p * NW + w] | T0[(size_t)p * NW + w]) z = false;
      zeroCare += z;
    }
    auto q = [](std::vector<double> v, double f) { std::sort(v.begin(), v.end()); return v[(size_t)(f * (v.size() - 1))]; };
    auto sum = [](const std::vector<double>& v) { double s = 0; for (double x : v) s += x; return s; };
    for (int kind = 0; kind < 2; kind++)
      fprintf(stderr, "  %s: L median %.0f p90 %.0f max %.0f sum %.0f | U median %.0f p90 %.0f max %.0f sum %.0f | sum L*U %.3e\n", kind ? "AND" : "OR ",
              q(L[kind], .5), q(L[kind], .9), q(L[kind], 1), sum(L[kind]), q(U[kind], .5), q(U[kind], .9), q(U[kind], 1), sum(U[kind]), sum(LU[kind]));
    fprintf(stderr, "  ptmask output would be %.1f MB; single-literal hits %ld; unobservable gates %ld\n", sumOut / 1048576.0, singles, zeroCare);
  }
  void topCands(const Job& j, int K, std::vector<Cand>& out) {
    out.clear();
    const u32 *EA = bEntA.as<u32>(), *R = bOut.as<u32>();
    for (int kind = 0; kind < 2; kind++) {
      u32 b = kind ? j.ab : j.ob, e = kind ? j.ae : j.oe;
      for (u32 i = b; i < e; i++) {
        u32 best = R[2 * (size_t)i];
        if (best == 0xFFFFFFFFu) continue;
        feasPairs += R[2 * (size_t)i + 1];
        Cand c; c.op = kind ? AND : OR; c.la = EA[i] & 0xFFFF; c.lb = EA[best] & 0xFFFF;
        c.score = ((EA[i] >> 16) & 0xFF) + ((EA[best] >> 16) & 0xFF);
        out.push_back(c);
      }
    }
    std::stable_sort(out.begin(), out.end(), [](const Cand& a, const Cand& b) { return a.score > b.score; });
    if ((int)out.size() > K) out.resize(K);
  }

  // ---- exact covers (CPU): g := OR of k admissible wires covering on(g), or AND of k wires killing off(g) ----
  struct CJ {
    bool built = false, ok = false;
    std::vector<int> lits;       // admissible, useful wires outside TFO(g) + g
    std::vector<int> pb;         // second wire of a 2-level term (new AND of lits[i] and pb[i]), or -1
    std::vector<u8> lcost;       // 1, or 2 for a 2-level term
    std::vector<u64> rows;       // distinct points, each a mask over lits (LW words)
    int LW = 0, nrows = 0;
    std::vector<int> S;          // MFFC(g) minus g
    int ns = 0;                  // tracked part: the (at most 64) members nearest to g; deeper ones count as staying alive
    std::vector<u64> rev;        // per literal: members of S (first 64) it keeps alive
  };
  std::vector<CJ> cj[2];
  std::vector<int> refc;
  long bbNodes = 0, bbCalls = 0, bbCut = 0;
  void mffc(int q, std::vector<int>& out) {       // gates that die with q (q excluded)
    out.clear();
    int N = net.N;
    std::vector<int>& st2 = stack; st2.clear(); st2.push_back(q);
    std::vector<int> all;
    while (!st2.empty()) {
      int h = st2.back(); st2.pop_back();
      const Gt g = net.g[h];
      for (int side = 0; side < (g.a == g.b ? 1 : 2); side++) {
        int f = side ? g.b : g.a;
        if (f < N || f >= (int)refc.size()) continue;
        if (--refc[f] == 0) { out.push_back(f - N); st2.push_back(f - N); }
        all.push_back(f);
      }
    }
    for (int f : all) refc[f]++;
  }
  CJ& cover(int q, int kind) {
    CJ& c = cj[kind][q];
    if (c.built) return c;
    c.built = true;
    int N = net.N, G = (int)cj[kind].size(), WT = N + G;
    const u8* fl = bFlags.as<u8>() + (size_t)q * WT;
    const u64* ex = &tfo[(size_t)q * GW];
    for (int w = 0; w < WT; w++) {
      u8 v = fl[w];
      bool pos = kind == 0 ? ((v & 1) && !(v & 8)) : ((v & 4) && !(v & 2));
      if (!pos) continue;
      if (w >= N) { int h = w - N; if (h == q || ((ex[h >> 6] >> (h & 63)) & 1)) continue; }
      c.lits.push_back(w);
      if ((int)c.lits.size() > o.maxLits) return c;        // too wide for the exact search (AND lists of small targets)
    }
    c.pb.assign(c.lits.size(), -1); c.lcost.assign(c.lits.size(), 1);
    if (kind == 0 && o.twoLevel && !prodEnd.empty() && prodEnd[q] > prodBeg[q]) {
      // best partner of every non-admissible wire; keep the widest terms, each unordered pair once
      const u32 *PA = bPA.as<u32>(), *R = bPOut.as<u32>();
      std::vector<std::pair<u32, u64>> pr;
      for (u32 e = prodBeg[q]; e < prodEnd[q]; e++) {
        u32 best = R[2 * (size_t)e];
        if (best == 0xFFFFFFFFu) continue;
        u32 a = PA[e], b2 = PA[best]; if (a > b2) std::swap(a, b2);
        pr.push_back({R[2 * (size_t)e + 1], ((u64)a << 32) | b2});
      }
      std::sort(pr.begin(), pr.end(), [](const std::pair<u32, u64>& x, const std::pair<u32, u64>& y) { return x.first != y.first ? x.first > y.first : x.second < y.second; });
      pr.erase(std::unique(pr.begin(), pr.end()), pr.end());
      prodFound += pr.size();
      int added = 0;
      for (auto& t : pr) {
        if ((int)c.lits.size() >= o.maxLits || added++ >= o.twoMax) break;
        c.lits.push_back((int)(t.second >> 32)); c.pb.push_back((int)(t.second & 0xFFFFFFFFu)); c.lcost.push_back(2);
      }
    }
    int L = (int)c.lits.size();
    if (!L) return c;
    int LW = c.LW = (L + 63) / 64;
    const u64* M = (kind ? bTC0.as<u64>() : bTC1.as<u64>()) + (size_t)q * NW;
    const u64* C = cols();
    std::vector<u64> tmp((size_t)64 * LW);
    std::vector<u64> raw;
    for (size_t wd = 0; wd < NW; wd++) {
      u64 m = M[wd];
      if (!m) continue;
      std::fill(tmp.begin(), tmp.end(), 0);
      for (int i = 0; i < L; i++) {
        u64 x = C[(size_t)c.lits[i] * NW + wd];
        if (c.pb[i] >= 0) x &= C[(size_t)c.pb[i] * NW + wd];
        u64 hit = (kind ? ~x : x) & m;
        while (hit) { int bpos = __builtin_ctzll(hit); hit &= hit - 1; tmp[(size_t)bpos * LW + (i >> 6)] |= u64(1) << (i & 63); }
      }
      while (m) { int bpos = __builtin_ctzll(m); m &= m - 1; raw.insert(raw.end(), tmp.begin() + (size_t)bpos * LW, tmp.begin() + (size_t)(bpos + 1) * LW); }
    }
    size_t U = raw.size() / LW;
    std::vector<u32> idx(U);
    for (u32 i = 0; i < U; i++) idx[i] = i;
    auto less = [&](u32 a, u32 b2) { return std::lexicographical_compare(&raw[(size_t)a * LW], &raw[(size_t)a * LW] + LW, &raw[(size_t)b2 * LW], &raw[(size_t)b2 * LW] + LW); };
    std::sort(idx.begin(), idx.end(), less);
    for (size_t i = 0; i < U; i++) {
      if (i && !less(idx[i - 1], idx[i])) continue;
      const u64* r = &raw[(size_t)idx[i] * LW];
      bool any = false; for (int k = 0; k < LW; k++) any = any || r[k];
      if (!any) return c;                                   // a point nobody covers: no cover of this kind
      c.rows.insert(c.rows.end(), r, r + LW);
    }
    c.nrows = (int)(c.rows.size() / LW);
    mffc(q, c.S);
    std::sort(c.S.begin(), c.S.end(), std::greater<int>());
    c.rev.assign(L, 0);
    c.ns = (int)std::min<size_t>(c.S.size(), 64);
    if (!c.S.empty()) {
      int ns = c.ns;
      std::unordered_map<int, int> pos;
      for (int i = 0; i < ns; i++) pos[c.S[i]] = i;
      std::vector<u64> cone(ns, 0);                         // S is sorted by id descending: fan-ins have larger index
      for (int i = ns - 1; i >= 0; i--) {
        const Gt& g = net.g[c.S[i]];
        u64 m = u64(1) << i;
        for (int f : {g.a, g.b}) if (f >= N) { auto it = pos.find(f - N); if (it != pos.end()) m |= cone[it->second]; }
        cone[i] = m;
      }
      for (int i = 0; i < L; i++) {
        if (c.lits[i] >= N) { auto it = pos.find(c.lits[i] - N); if (it != pos.end()) c.rev[i] = cone[it->second]; }
        if (c.pb[i] >= N) { auto it = pos.find(c.pb[i] - N); if (it != pos.end()) c.rev[i] |= cone[it->second]; }
      }
    }
    c.ok = true;
    return c;
  }
  // minimum of (#literals + #revived gates) over covers that avoid the banned literals; -1 if none within `limit`
  struct BB { const CJ* c; const u64* ban; int limit; long nodes, budget; int bestCost; std::vector<int> best, cur; bool first; Rng* rng; int lc = 0; };
  void bbRec(BB& b, const std::vector<int>& rows, u64 rev) {
    const CJ& c = *b.c;
    int cost = b.lc + __builtin_popcountll(rev);
    if (rows.empty()) { if (cost <= b.limit) { b.bestCost = cost; b.best = b.cur; b.limit = cost - 1; } return; }
    if (cost + 1 > b.limit || b.nodes >= b.budget) return;
    b.nodes++;
    int LW = c.LW, br = -1, bc = 1 << 30;
    for (int r : rows) {
      const u64* m = &c.rows[(size_t)r * LW];
      int pc = 0; for (int w = 0; w < LW; w++) pc += __builtin_popcountll(m[w] & ~b.ban[w]);
      if (pc < bc) { bc = pc; br = r; if (pc <= 1) break; }
    }
    if (bc == 0) return;
    const u64* m = &c.rows[(size_t)br * LW];
    struct Opt2 { int lit; long key; };
    Opt2 opts[256]; int no = 0;
    for (int w = 0; w < LW; w++) {
      u64 bits = m[w] & ~b.ban[w];
      while (bits && no < 256) {
        int i = w * 64 + __builtin_ctzll(bits); bits &= bits - 1;
        int cov = 0; for (int r : rows) cov += (c.rows[(size_t)r * LW + (i >> 6)] >> (i & 63)) & 1;
        int extra = __builtin_popcountll(c.rev[i] & ~rev) + (c.lcost[i] - 1);
        opts[no++] = {i, (long)extra * 1000000 - (long)cov * 64 - (long)(b.rng ? b.rng->below(64) : 0)};
      }
    }
    std::sort(opts, opts + no, [](const Opt2& x, const Opt2& y) { return x.key < y.key; });
    std::vector<int> next;
    for (int t = 0; t < no; t++) {
      int i = opts[t].lit;
      next.clear();
      for (int r : rows) if (!((c.rows[(size_t)r * LW + (i >> 6)] >> (i & 63)) & 1)) next.push_back(r);
      b.cur.push_back(i); b.lc += c.lcost[i];
      bbRec(b, next, rev | c.rev[i]);
      b.cur.pop_back(); b.lc -= c.lcost[i];
      if (b.first && b.bestCost >= 0) return;
      if (b.nodes >= b.budget) return;
    }
  }
  int bb(const CJ& c, const u64* ban, int limit, long budget, std::vector<int>& best, bool first, Rng* r) {
    BB b{&c, ban, limit, 0, budget, -1, {}, {}, first, r, 0};
    std::vector<int> rows(c.nrows);
    for (int i = 0; i < c.nrows; i++) rows[i] = i;
    bbRec(b, rows, 0);
    bbNodes += b.nodes; bbCalls++; if (b.nodes >= b.budget) bbCut++;
    best = b.best;
    return b.bestCost;
  }

  // ---- moves (every one checked by full re-simulation) ----
  struct Undo { std::vector<std::pair<int, Gt>> g; std::vector<int> outs; size_t ng; };
  int litWire(int lit, Undo& u) {             // wire computing the literal; may append a NOT gate
    int w = lit >> 1;
    if (!(lit & 1)) return w;
    if (w >= net.N && net.g[w - net.N].op == NOT) return net.g[w - net.N].a;
    if (w < (int)notOf.size() && notOf[w] >= 0) return notOf[w];
    if (net.g.size() + 1 >= capG) return -1;
    net.g.push_back({(u8)NOT, w, w});
    int nw = net.N + (int)net.g.size() - 1;
    if (w < (int)notOf.size()) notOf[w] = nw;
    return nw;
  }
  void setGate(int id, Gt q, Undo& u) { u.g.push_back({id, net.g[id]}); net.g[id] = q; }
  void begin(Undo& u) { u.g.clear(); u.outs = net.outs; u.ng = net.g.size(); }
  void revert(Undo& u) {
    for (size_t i = u.g.size(); i-- > 0;) net.g[u.g[i].first] = u.g[i].second;
    for (size_t id = u.ng; id < net.g.size(); id++) { int a = net.g[id].a; if (a < (int)notOf.size() && notOf[a] == net.N + (int)id) notOf[a] = -1; }
    net.g.resize(u.ng); net.outs = u.outs;
  }
  int live = 0;
  // returns live-gate count if the current net is acyclic and correct (columns then swapped in), else -1
  int evalNet() {
    tried++;
    if (!topo(net, order, st, stack)) { failCycle++; return -1; }
    u64* c2 = bCols2.as<u64>();
    sim.run(net, order, c2);
    if (!sim.ok(net, c2)) { failVerify++; return -1; }
    return (int)order.size();
  }
  void commit(int nl) { std::swap(bCols, bCols2); live = nl; }
  // q := op-chain over the given wires (k >= 2), or every reader of q moves to the single wire (k == 1)
  bool applyCover(int q, int kind, const std::vector<int>& ws, Undo& u) {
    int N = net.N, k = (int)ws.size();
    if (k == 0) return false;
    if (k == 1) {
      int gw = N + q, w = ws[0];
      for (int id = 0; id < (int)net.g.size(); id++) {
        Gt g = net.g[id];
        if (g.a == gw || g.b == gw) { if (g.a == gw) g.a = w; if (g.b == gw) g.b = w; setGate(id, g, u); }
      }
      for (int& ow : net.outs) if (ow == gw) ow = w;
      return true;
    }
    if (net.g.size() + k >= capG) return false;
    u8 op = kind ? (u8)AND : (u8)OR;
    int t = ws[0];
    for (int i = 1; i < k - 1; i++) { net.g.push_back({op, t, ws[i]}); t = N + (int)net.g.size() - 1; }
    setGate(q, Gt{op, t, ws[k - 1]}, u);
    return true;
  }
  bool structuralLive(int& nl) { if (!topo(net, order, st, stack)) { failCycle++; return false; } nl = (int)order.size(); return true; }

  // one optimisation round; returns gates removed
  int round(int rnd) {
    int N = net.N, G = (int)net.g.size(), WT = N + G;
    int sizeBefore = G;
    double t0 = now();
    analyze(); careMasks();
    tCare += now() - t0;
    runSingles();
    if (o.stats) sizeStats();
    t0 = now();
    u32 E = 0;
    jobs.clear();
    if (o.pairs) E = buildLists((int)rng.below((u32)G));
    else { score.assign(WT, 0); notOf.assign(WT, -1); for (int id = 0; id < G; id++) if (net.g[id].op == NOT) notOf[net.g[id].a] = N + id; }
    tLists += now() - t0;
    runPairs(E);
    prodBeg.clear(); prodEnd.clear();
    if (o.covers && o.twoLevel && o.twoEvery > 0 && rnd % o.twoEvery == 0) runProds();
    t0 = now();
    const u8* F = bFlags.as<u8>();
    live = G;
    Undo u;
    std::vector<u8> touched(capG, 0);
    // (a) replace a gate by a single literal
    for (int g = G - 1; g >= 0; g--) {
      const u8* fl = F + (size_t)g * WT;
      int bestLit = -1, bestRank = -1;
      for (int w = 0; w < WT; w++) {
        u8 v = fl[w];
        bool pos = (v & 1) && (v & 4), neg = (v & 2) && (v & 8) && o.basis == "aon";
        if (!pos && !neg) continue;
        if (w >= N) { int h = w - N; if (h == g || inTfo(g, h)) continue; }
        int rank = pos ? (w < N ? 3 : 2) : (notOf[w] >= 0 ? 2 : 1);
        if (rank > bestRank) { bestRank = rank; bestLit = w * 2 + (pos ? 0 : 1); }
      }
      if (bestLit < 0) continue;
      begin(u);
      int w = litWire(bestLit, u);
      if (w < 0) { revert(u); continue; }
      int gw = N + g;
      for (int id = 0; id < (int)net.g.size(); id++) {
        Gt q = net.g[id];
        if (q.a == gw || q.b == gw) { if (N + id == w) continue; if (q.a == gw) q.a = w; if (q.b == gw) q.b = w; setGate(id, q, u); }
      }
      for (int& ow : net.outs) if (ow == gw) ow = w;
      int nl = 1 << 30;
      if (!structuralLive(nl)) { revert(u); continue; }
      if (nl >= live) { failGain++; revert(u); continue; }
      nl = evalNet();
      if (nl < 0) { revert(u); continue; }
      gSingle += live - nl; aSingle++; commit(nl);
    }
    // (b) kill gate x: every parent gets an exact replacement that does not depend on x
    std::vector<std::vector<int>> jobsOf(WT);        // by fan-in wire f: job indices
    for (size_t j = 0; j < jobs.size(); j++) jobsOf[jobs[j].f].push_back((int)j);
    std::vector<std::vector<Cand>> cands(jobs.size());
    for (size_t j = 0; j < jobs.size(); j++) topCands(jobs[j], o.tries, cands[j]);
    std::vector<int> xs;
    for (int x = 0; x < G; x++) {
      int w = N + x;
      if (isOut[w] || parents[w].empty() || jobsOf[w].size() != parents[w].size()) continue;
      bool all = true;
      for (int j : jobsOf[w]) if (cands[j].empty()) { all = false; break; }
      if (all) xs.push_back(x);
    }
    // few parents first (most likely to verify), then random
    std::vector<std::pair<u64, int>> ordx;
    for (int x : xs) ordx.push_back({((u64)parents[N + x].size() << 32) | rng.below(1u << 30), x});
    std::sort(ordx.begin(), ordx.end());
    for (auto& ox : ordx) {
      int x = ox.second, w = N + x;
      bool skip = false;
      for (int j : jobsOf[w]) if (touched[jobs[j].p]) skip = true;
      if (skip || touched[x]) continue;
      begin(u);
      bool okAll = true;
      int saveLive = live;
      for (int j : jobsOf[w]) {
        int p = jobs[j].p;
        bool done = false;
        for (const Cand& c : cands[j]) {
          size_t mark = u.g.size(); size_t ng = net.g.size();
          int a = litWire(c.la, u), b = a < 0 ? -1 : litWire(c.lb, u);
          if (a < 0 || b < 0) break;
          setGate(p, Gt{(u8)c.op, a, b}, u);
          int nl;
          if (structuralLive(nl)) { done = true; break; }
          // cycle: undo just this parent
          net.g[p] = u.g.back().second; u.g.resize(mark);
          for (size_t id = ng; id < net.g.size(); id++) { int aa = net.g[id].a; if (notOf[aa] == N + (int)id) notOf[aa] = -1; }
          net.g.resize(ng);
        }
        if (!done) { okAll = false; break; }
      }
      int nl = -1;
      if (okAll) {
        int sl = 1 << 30;
        if (structuralLive(sl)) { if (sl < live) nl = evalNet(); else failGain++; }
      }
      if (nl < 0) { revert(u); live = saveLive; continue; }
      gKill += live - nl; aKill++;
      for (int j : jobsOf[w]) touched[jobs[j].p] = 1;
      touched[x] = 1;
      commit(nl);
    }
    // (d) exact covers: strict gains at every gate, then kills of shared gates through alternative covers of all parents
    if (o.covers) {
      for (int kind = 0; kind < 2; kind++) { cj[kind].assign(G, CJ()); }
      refc.assign(WT, 0);
      for (int id = 0; id < G; id++) { const Gt& g = net.g[id]; refc[g.a]++; if (g.b != g.a) refc[g.b]++; }
      for (int w : net.outs) refc[w]++;
      std::vector<u64> noban(8, 0), ban(8, 0);
      std::vector<int> sol, ws;
      // wires of a solution; a 2-level term becomes a new AND gate (call after begin(u): revert() removes it again)
      auto wiresOf = [&](const CJ& c, const std::vector<int>& sl) {
        ws.clear();
        for (int i : sl) {
          if (c.pb[i] < 0) { ws.push_back(c.lits[i]); continue; }
          if (net.g.size() + 2 >= capG) { ws.clear(); return; }
          net.g.push_back({(u8)AND, c.lits[i], c.pb[i]});
          ws.push_back(net.N + (int)net.g.size() - 1);
        }
      };
      auto usesTwo = [&](const CJ& c, const std::vector<int>& sl) { for (int i : sl) if (c.pb[i] >= 0) return true; return false; };
      for (int q = G - 1; q >= 0; q--) {
        if (touched[q]) continue;
        if ((q & 31) == 0 && late()) break;
        for (int kind = 0; kind < 2; kind++) {
          CJ& c = cover(q, kind);
          if (!c.ok) continue;
          int base = c.ns + 2;
          int cost = bb(c, noban.data(), base - 1, o.bbBudget, sol, false, nullptr);
          if (cost < 0) continue;
          begin(u);
          wiresOf(c, sol);
          int nl = 1 << 30;
          if (!applyCover(q, kind, ws, u) || !structuralLive(nl) || nl >= live) {
            if (nl != (1 << 30) && nl >= live) {
              failGain++;
              if (o.verbose >= 3 && failGain < 6) {
                fprintf(stderr, "DBG q=%d kind=%d op=%d a=%d b=%d |S|=%zu cost=%d live %d -> %d  S:", q, kind, u.g.empty() ? -1 : u.g.back().second.op, u.g.empty() ? -1 : u.g.back().second.a, u.g.empty() ? -1 : u.g.back().second.b, c.S.size(), cost, live, nl);
                for (int h : c.S) fprintf(stderr, " %d(ref %d)", h + N, refc[h + N]);
                fprintf(stderr, "  cover:"); for (size_t i = 0; i < sol.size(); i++) fprintf(stderr, " %d(rev %llx)", ws[i], (unsigned long long)c.rev[sol[i]]);
                fprintf(stderr, "\n");
              }
            }
            revert(u); continue;
          }
          nl = evalNet();
          if (nl < 0) { revert(u); continue; }
          if (usesTwo(c, sol)) { gTwo += live - nl; aTwo++; }
          gCover += live - nl; aCover++; touched[q] = 1;
          for (int h : c.S) touched[h] = 1;
          commit(nl);
          break;
        }
      }
      // kills: x has >= 2 readers; each reader (or the root of its fanout-free chain) gets a cover that avoids TFO(x) + x
      std::vector<std::pair<u64, int>> xo;
      for (int x = 0; x < G; x++) if (!isOut[N + x] && parents[N + x].size() >= 2 && (int)parents[N + x].size() <= o.maxParents) xo.push_back({rng.next(), x});
      std::sort(xo.begin(), xo.end());
      std::vector<int> Sx;
      struct Pick { int q, kind; std::vector<int> ws; int delta; };
      for (auto& xe : xo) {
        int x = xe.second;
        if (touched[x]) continue;
        if (late()) break;
        mffc(x, Sx);
        int room = (int)Sx.size() + 1;           // gates freed when x dies
        std::vector<Pick> picks;
        int total = 0; bool okAll = true;
        for (int p : parents[N + x]) {
          Pick bestP; bestP.q = -1; bestP.delta = 1 << 30;
          int q = p;
          for (int depth = 0; depth < o.chain; depth++) {
            if (touched[q]) break;
            for (int kind = 0; kind < 2; kind++) {
              CJ& c = cover(q, kind);
              if (!c.ok) continue;
              std::fill(ban.begin(), ban.end(), 0);
              for (int i = 0; i < (int)c.lits.size(); i++) { int w = c.lits[i]; if (w >= N && (w - N == x || inTfo(x, w - N))) ban[i >> 6] |= u64(1) << (i & 63); }
              int base = c.ns + 2;
              int lim = base + room - 1 - total;
              if (bestP.q >= 0) lim = std::min(lim, base + bestP.delta - 1);
              int cost = bb(c, ban.data(), lim, o.bbBudget, sol, false, &rng);
              if (cost < 0) continue;
              bestP.q = q; bestP.kind = kind; bestP.delta = cost - base; bestP.ws = sol;
            }
            if (isOut[N + q] || parents[N + q].size() != 1) break;
            q = parents[N + q][0];
          }
          if (bestP.q < 0) { okAll = false; break; }
          total += bestP.delta;
          if (total >= room) { okAll = false; break; }
          picks.push_back(bestP);
        }
        if (!okAll) continue;
        begin(u);
        bool good = true;
        std::vector<int> doneQ;
        for (auto& pk : picks) {
          if (std::find(doneQ.begin(), doneQ.end(), pk.q) != doneQ.end()) continue;
          doneQ.push_back(pk.q);
          wiresOf(cj[pk.kind][pk.q], pk.ws);
          if (!applyCover(pk.q, pk.kind, ws, u)) { good = false; break; }
        }
        int nl = 1 << 30;
        if (!good || !structuralLive(nl) || nl >= live) { if (good && nl != (1 << 30)) failGain++; revert(u); continue; }
        nl = evalNet();
        if (nl < 0) { revert(u); continue; }
        gCKill += live - nl; aCKill++;
        touched[x] = 1; for (auto& pk : picks) { touched[pk.q] = 1; for (int h : cj[pk.kind][pk.q].S) touched[h] = 1; }
        for (int h : Sx) touched[h] = 1;
        commit(nl);
      }
      // neutral: a different cover of the same cost (one current fan-in banned)
      long wantN = (long)std::ceil(o.neutral * G);
      for (long tr = 0, done = 0; tr < 8 * wantN && done < wantN; tr++) {
        int q = (int)rng.below((u32)G);
        if (touched[q]) continue;
        int kind = net.g[q].op == AND ? 1 : 0;
        CJ& c = cover(q, kind);
        if (!c.ok) continue;
        std::fill(ban.begin(), ban.end(), 0);
        int nb = 0;
        int fb = rng.below(2) ? net.g[q].a : net.g[q].b;
        for (int i = 0; i < (int)c.lits.size(); i++) if (c.lits[i] == fb) { ban[i >> 6] |= u64(1) << (i & 63); nb++; }
        if (!nb) continue;
        int base = c.ns + 2;
        int cost = bb(c, ban.data(), base, o.bbBudget / 4 + 1, sol, true, &rng);
        if (cost < 0) continue;
        begin(u);
        wiresOf(c, sol);
        int nl = 1 << 30;
        if (!applyCover(q, kind, ws, u) || !structuralLive(nl) || nl > live) { revert(u); continue; }
        nl = evalNet();
        if (nl < 0) { revert(u); continue; }
        if (nl < live) gCover += live - nl;
        aNeutral++; done++; touched[q] = 1;
        commit(nl);
      }
    }
    // (c) size-neutral rewrites (random walk on the plateau)
    long want = (long)std::ceil(o.neutral * G);
    for (long tr = 0, done = 0; tr < 6 * want && done < want && !jobs.empty(); tr++) {
      int j = (int)rng.below((u32)jobs.size());
      if (cands[j].empty() || touched[jobs[j].p]) continue;
      const Cand& c = cands[j][rng.below((u32)cands[j].size())];
      int p = jobs[j].p;
      begin(u);
      int a = litWire(c.la, u), b = a < 0 ? -1 : litWire(c.lb, u);
      if (a < 0 || b < 0) { revert(u); continue; }
      setGate(p, Gt{(u8)c.op, a, b}, u);
      int nl;
      if (!structuralLive(nl) || nl > live) { revert(u); continue; }
      nl = evalNet();
      if (nl < 0) { revert(u); continue; }
      if (nl < live) gKill += live - nl;
      aNeutral++; done++; touched[p] = 1;
      commit(nl);
    }
    tMoves += now() - t0;
    t0 = now();
    compact(net, sim, cols());
    tCompact += now() - t0;
    (void)rnd;
    return sizeBefore - (int)net.g.size();
  }
};

static int best_in_dir(const std::string& dir, const std::string& name, const std::string& basis) {
  int best = 1 << 30;
  DIR* d = opendir(dir.c_str());
  if (!d) return best;
  std::string pre = name + "_", suf = "_" + basis + ".ckt";
  while (dirent* e = readdir(d)) {
    std::string f = e->d_name;
    if (f.size() > pre.size() + suf.size() && f.compare(0, pre.size(), pre) == 0 && f.compare(f.size() - suf.size(), suf.size(), suf) == 0) {
      std::string mid = f.substr(pre.size(), f.size() - pre.size() - suf.size());
      if (!mid.empty() && mid.find_first_not_of("0123456789") == std::string::npos) best = std::min(best, atoi(mid.c_str()));
    }
  }
  closedir(d);
  return best;
}

int main(int argc, char** argv) {
  Options o;
  std::vector<std::string> pos;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto need = [&]() { if (i + 1 >= argc) die("missing value for " + a); return std::string(argv[++i]); };
    if (a == "-o") o.out = need();
    else if (a == "--basis") o.basis = need();
    else if (a == "--time") o.timeLimit = atof(need().c_str());
    else if (a == "--rounds") o.rounds = atol(need().c_str());
    else if (a == "--seed") o.seed = strtoull(need().c_str(), nullptr, 10);
    else if (a == "--target") o.target = atoi(need().c_str());
    else if (a == "--neutral") o.neutral = atof(need().c_str());
    else if (a == "--tries") o.tries = atoi(need().c_str());
    else if (a == "--entries") o.capE = strtoull(need().c_str(), nullptr, 10);
    else if (a == "--found") o.found = need();
    else if (a == "--cpu") o.cpu = true;
    else if (a == "--check") o.check = true;
    else if (a == "--no-neg") o.neg = false;
    else if (a == "--no-covers") o.covers = false;
    else if (a == "--no-pairs") o.pairs = false;
    else if (a == "--no-two") o.twoLevel = false;
    else if (a == "--two-every") o.twoEvery = std::max(0, atoi(need().c_str()));
    else if (a == "--two-on-words") o.twoOnWords = atoi(need().c_str());
    else if (a == "--two-max") o.twoMax = atoi(need().c_str());
    else if (a == "--bb") o.bbBudget = atol(need().c_str());
    else if (a == "--max-lits") o.maxLits = std::min(256, atoi(need().c_str()));
    else if (a == "--chain") o.chain = atoi(need().c_str());
    else if (a == "--max-parents") o.maxParents = atoi(need().c_str());
    else if (a == "--stats") o.stats = true;
    else if (a == "-q") o.verbose = 0;
    else if (a == "-v") o.verbose = 2;
    else if (a == "-vv") o.verbose = 3;
    else if (a == "-j") need();   // accepted for uniformity; gpuopt uses one CPU thread
    else if (a[0] == '-' && a != "-") die("unknown option " + a);
    else pos.push_back(a);
  }
  if (pos.size() != 2 || (o.basis != "aon" && o.basis != "ao")) {
    std::cerr << "usage: gpuopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [--time S] [--rounds R] [--seed X] [--target SIZE]\n"
                 "         [--neutral F] [--tries K] [--no-neg] [--no-pairs] [--no-covers] [--two-every K] [--bb NODES]\n"
                 "         [--entries E] [--found DIR] [--cpu] [--check] [-q|-v]\n";
    return 2;
  }
  o.spec = pos[0]; o.in = pos[1];
  Spec sp = load_spec(o.spec);
  Circuit cin_ = load_circuit(o.in);
  if (cin_.N != sp.N) die("circuit inputs != spec inputs");
  { std::string why; if (!basis_ok(cin_, o.basis, &why)) die("input circuit is not in basis " + o.basis + ": " + why); }
  if (!verify(sp, cin_).ok) die("input circuit does not satisfy the spec");
  Net start = normalize(cin_);
  Engine en(sp, o);
  en.init(start);
  std::string name = o.spec; { auto s = name.find_last_of('/'); if (s != std::string::npos) name = name.substr(s + 1); auto d = name.rfind(".spec"); if (d != std::string::npos) name = name.substr(0, d); }
  Circuit best = to_circuit(en.net);
  if (!verify(sp, best).ok) die("gpuopt internal: compacted circuit is wrong");
  double T0 = now();
  if (o.verbose) fprintf(stderr, "gpuopt %s: start %d gates (file %d), %s, P=%zu, %s\n", name.c_str(), best.size(), cin_.size(), o.basis.c_str(), sp.P,
                         o.cpu ? "CPU kernels" : en.dev->name().c_str());
  auto save = [&](const Circuit& c, const std::string& path) {
    char cm[256]; snprintf(cm, sizeof cm, "gpuopt %s basis=%s size=%d from=%s seed=%llu", o.spec.c_str(), o.basis.c_str(), c.size(), o.in.c_str(), (unsigned long long)o.seed);
    save_circuit(path, c, cm);
  };
  int foundBest = o.found.empty() ? 0 : best_in_dir(o.found, name, o.basis);
  double lastFound = 0;
  bool pendingFound = false;
  auto saveFound = [&](bool force) {
    if (o.found.empty() || !pendingFound) return;
    if (!force && now() - lastFound < 30) return;
    if (best.size() < foundBest) { save(best, o.found + "/" + name + "_" + std::to_string(best.size()) + "_" + o.basis + ".ckt"); foundBest = best.size(); }
    lastFound = now(); pendingFound = false;
  };
  long r = 0;
  if (o.rounds < 0) en.deadline = T0 + o.timeLimit;
  for (;; r++) {
    if (o.rounds >= 0 && r >= o.rounds) break;
    if (o.rounds < 0 && now() - T0 >= o.timeLimit) break;
    if (o.target >= 0 && best.size() <= o.target) break;
    int d = en.round((int)r);
    Circuit c = to_circuit(en.net);
    std::string why;
    if (!verify(sp, c).ok || !basis_ok(c, o.basis, &why)) die("gpuopt internal: round produced a wrong circuit (not saved)");
    if (c.size() < best.size()) { best = c; if (!o.out.empty()) save(best, o.out); pendingFound = true; saveFound(false); }
    if (o.verbose >= 2 || (o.verbose && (d > 0 || r % 20 == 0)))
      fprintf(stderr, "[%7.1fs] round %ld  size %d (best %d)  single %ld pair-kill %ld cover %ld cover-kill %ld neutral %ld | tried %ld bad %ld cyc %ld\n", now() - T0, r, c.size(), best.size(),
              en.aSingle, en.aKill, en.aCover, en.aCKill, en.aNeutral, en.tried, en.failVerify, en.failCycle);
  }
  if (!verify(sp, best).ok) die("gpuopt internal: best circuit is wrong");
  if (!o.out.empty()) save(best, o.out);
  pendingFound = best.size() < foundBest; saveFound(true);
  double T = now() - T0;
  if (o.verbose) {
    fprintf(stderr, "gpuopt done: %d -> %d gates in %.1f s, %ld rounds (%s)\n", cin_.size(), best.size(), T, r, o.cpu ? "cpu" : "gpu");
    fprintf(stderr, "  time: care %.2f  singles %.2f (gpu %.2f)  lists %.2f  pairs %.2f (gpu %.2f)  moves %.2f  compact %.2f   dispatches %ld, longest %.1f ms\n",
            en.tCare, en.tSingles, en.gSingles, en.tLists, en.tPairs, en.gPairs, en.tMoves, en.tCompact, en.nDispatch, en.maxDispatch * 1e3);
    fprintf(stderr, "  work: single tests %.3e (x %zu bits)  list entries %.3e  pair tests %.3e  feasible best-pairs %.3e\n", en.singleTests, sp.P, en.entriesTot, en.pairTests, en.feasPairs);
    fprintf(stderr, "  moves: single %ld (-%ld gates)  pair-kill %ld (-%ld)  cover %ld (-%ld)  cover-kill %ld (-%ld)  neutral %ld | evaluated %ld, wrong %ld, cyclic %ld, no gain %ld\n",
            en.aSingle, en.gSingle, en.aKill, en.gKill, en.aCover, en.gCover, en.aCKill, en.gCKill, en.aNeutral, en.tried, en.failVerify, en.failCycle, en.failGain);
    fprintf(stderr, "  cover search: %ld calls, %ld nodes, %ld hit the node budget\n", en.bbCalls, en.bbNodes, en.bbCut);
    if (o.twoEvery > 0)
      fprintf(stderr, "  2-level terms: %.3e product tests in %.2f s (gpu %.2f), %.3e terms offered to the cover search, %ld covers used one (-%ld gates), %ld gate visits skipped (wide on-set)\n",
              en.prodTests, en.tProds, en.gProds, en.prodFound, en.aTwo, en.gTwo, en.prodSkipped);
  }
  std::cout << "size " << best.size() << " and " << best.count(AND) << " or " << best.count(OR) << " not " << best.count(NOT) << "\n";
  return 0;
}
