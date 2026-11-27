// startab — exact star-complexity tables for ALL small bipartite graphs at once.
//
// Model (Lean: PEqualNP.Represents.RepSizeAtMost and its FanInTwo analogue): a wire is an n x m 0/1 matrix
// (one bit per point (u,v), bit index u*m+v), inputs are the n row stars and the m column stars (plus, with
// --enc, the free "encoder" wires), a gate is AND/OR of two wires (basis ao) or AND/OR/NOT (basis aon), every
// gate counts.  See docs/startab.md for the proof that the normal form searched here (every gate reads two
// distinct earlier wires -- or one for NOT -- and computes a function that is new, not 0 and not all-ones)
// loses nothing against the full Lean model with constants, copies and missing-wire reads.
//
// Method: iterative deepening over SETS of gate functions.  Pass r enumerates every derivable set S' of r-1
// gate functions exactly once up to the symmetry group (include/exclude branching over the candidate list,
// orbit bans under the pointwise stabiliser of the prefix), pruned by the sink bound, and marks every
// function f op x obtainable with one more gate.  After pass r every function of size <= r is marked with
// its exact size.
//
//   startab --n N [--m M] [--basis ao|aon] [--enc] [--rmax R] [--tlimit SEC] [-j T]
//           [--nosym] [--nosink] [--notranspose] [--out FILE.jsonl] [--costs FILE.bin] [-q]
#include "../../include/ckt.hpp"
#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <deque>
#include <functional>
#include <mutex>
#include <thread>

using u8 = uint8_t;
using u16 = uint16_t;
using u32 = uint32_t;
using u64 = uint64_t;

enum { OP_AND = 0, OP_OR = 1, OP_NOT = 2 };
static const int MAXG = 22;       // max gates in a chain
static const int MAXW = 64;       // max wires (inputs + gates)
static const int TABBITS = 13;    // seen-hash: 8192 slots
static const u32 TABSZ = 1u << TABBITS, TABMASK = TABSZ - 1, EMPTY = 0xFFFFFFFFu;
static const int LISTCAP = 6000;

// ------------------------------------------------------------------ problem
static int gn = 0, gm = 0, P = 0, N = 0;
static u32 FULL = 0;
static bool allowNot = false, encMode = false, useSym = true, useSink = true, useTight = true, useCost = true, useTranspose = true, quiet = false;
static std::vector<u32> IN;                 // input functions
static std::vector<std::string> INNAME;
struct GE { u8 pp[32]; u8 ip[48]; };        // image of each point; image index of each input
static std::vector<GE> G;

static inline u32 gapply(const GE& g, u32 f) {
  u32 r = 0;
  while (f) { int p = __builtin_ctz(f); f &= f - 1; r |= 1u << g.pp[p]; }
  return r;
}

static std::atomic<u8>* cost = nullptr;     // 255 = unknown
static std::vector<u16> classOf;            // class id of every function
struct ClassInfo { u32 rep; u32 orbit; };
static std::vector<ClassInfo> classes;
struct Wit { u32 T = 0; int ng = 0; u8 op[MAXG], a[MAXG], b[MAXG]; };
static std::vector<Wit> wit;
static std::atomic<u8>* hasWit = nullptr;

static int R = 0;                           // size of the current pass
static std::atomic<bool> stopFlag{false};
static std::chrono::steady_clock::time_point T0;
static double tlimit = 0;
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count(); }

// ------------------------------------------------------------------ search context
struct Cand { u32 f; u8 op, a, b, pad; };

struct Task {
  int k = 0; u32 Z = 0;
  u32 wires[MAXW]; u8 gop[MAXG], ga[MAXG], gb[MAXG]; u8 cw[MAXW]; u32 cone[MAXG + 1];
  std::vector<Cand> L; std::vector<u16> H; std::vector<u32> seen;
};

struct Ctx {
  u32 wires[MAXW]; u8 gop[MAXG], ga[MAXG], gb[MAXG];
  u32 tab[TABSZ]; u32 undo[TABSZ]; int nundo = 0;
  std::vector<Cand> lists[MAXG + 1];
  std::vector<u16> Hs[MAXG + 1];
  std::vector<std::pair<u32, int>> sorted[MAXG + 1];
  std::vector<u8> dead[MAXG + 1];
  std::vector<int> orb[MAXG + 1];
  u64 nodes = 0, leafc = 0, ops = 0, newmarks = 0, tasks = 0, tight = 0, two = 0, cpr = 0;
  u8 cw[MAXW]; u32 cone[MAXG + 1];     // exact size of every wire's function; gates each gate depends on
  Ctx() { for (auto& l : lists) l.resize(LISTCAP); clear(); }
  void clear() { for (u32 i = 0; i < TABSZ; i++) tab[i] = EMPTY; nundo = 0; }
  inline bool insert(u32 h) {
    u32 i = (h * 0x9E3779B1u) >> (32 - TABBITS);
    for (;;) {
      u32 v = tab[i];
      if (v == h) return false;
      if (v == EMPTY) { tab[i] = h; undo[nundo++] = i; return true; }
      i = (i + 1) & TABMASK;
    }
  }
  inline void rollback(int u0) { while (nundo > u0) tab[undo[--nundo]] = EMPTY; }
};

// ------------------------------------------------------------------ task queue (work sharing)
static std::mutex qmu;
static std::condition_variable qcv;
static std::deque<Task*> queue_;
static std::atomic<int> qsize{0};
static int active = 0, nthreads = 1, splitLevels = 3;   // a subtree is handed to another thread only if it has >= splitLevels levels below it

static void pushTask(Task* t) {
  { std::lock_guard<std::mutex> lk(qmu); queue_.push_back(t); qsize.store((int)queue_.size(), std::memory_order_relaxed); }
  qcv.notify_one();
}
static Task* popTask() {
  std::unique_lock<std::mutex> lk(qmu);
  for (;;) {
    if (!queue_.empty()) {
      Task* t = queue_.front(); queue_.pop_front(); qsize.store((int)queue_.size(), std::memory_order_relaxed);
      active++; return t;
    }
    if (active == 0) { qcv.notify_all(); return nullptr; }
    qcv.wait(lk);
  }
}
static void doneTask() {
  { std::lock_guard<std::mutex> lk(qmu); active--; }
  qcv.notify_all();
}

// ------------------------------------------------------------------ marking
// unres: one bit per function, set while the function has no size <= R yet (4 MB at 5x5, stays in cache,
// unlike the 32 MB cost table).  mark(): the circuit is  c's first k gates, then gate k = cd, then the
// output gate k+1 = (gate k) op (wire x).
static std::atomic<u64>* unres = nullptr;
static std::atomic<long> remainingClasses{0};
static std::atomic<bool> allDone{false};
static inline void mark(Ctx& c, int k, const Cand& cd, u32 T, int op, int x) {
  c.ops++;
  if (!((unres[T >> 6].load(std::memory_order_relaxed) >> (T & 63)) & 1)) return;
  unres[T >> 6].fetch_and(~(u64(1) << (T & 63)), std::memory_order_relaxed);
  u8 cur = cost[T].load(std::memory_order_relaxed);
  if (cur <= R) return;
  if (!cost[T].compare_exchange_strong(cur, (u8)R, std::memory_order_relaxed)) return;
  c.newmarks++;
  u16 cl = classOf[T];
  if (hasWit[cl].exchange(1)) return;
  if (remainingClasses.fetch_sub(1) == 1) { allDone.store(true); stopFlag.store(true); }   // every class resolved: stop early
  Wit& w = wit[cl];
  w.T = T; w.ng = k + 2;
  for (int g = 0; g < k; g++) { w.op[g] = c.gop[g]; w.a[g] = c.ga[g]; w.b[g] = c.gb[g]; }
  w.op[k] = cd.op; w.a[k] = cd.a; w.b[k] = cd.b;
  w.op[k + 1] = (u8)op; w.a[k + 1] = (u8)(N + k); w.b[k + 1] = (u8)x;
}

// ------------------------------------------------------------------ cost-budget bounds
// Let the set hold `ng` gates and let U be the set of existing wires read by the gates still to come.  In a
// least circuit (docs/startab.md, "cost bounds"):
//   (a) sum_{u in U} c(u) >= ng                (else: rebuild every u from scratch, fewer gates)
//   (b) c(u) >= #gates that only u depends on  (else: rebuild u alone from scratch)
// where c() is the exact size of a function, known for every gate of the set because all smaller passes are
// complete.  cw[] caches c of every wire (0 for inputs), cone[g] is the set of gates gate g depends on.
static inline bool boundsU(const Ctx& c, int ng, const int* U, int nu) {
  int sum = 0;
  for (int i = 0; i < nu; i++) sum += c.cw[U[i]];
  if (sum < ng) return false;
  for (int i = 0; i < nu; i++) {
    if (U[i] < N) continue;
    u32 others = 0;
    for (int j = 0; j < nu; j++) if (j != i && U[j] >= N) others |= c.cone[U[j] - N];
    if ((int)c.cw[U[i]] < __builtin_popcount(c.cone[U[i] - N] & ~others)) return false;
  }
  return true;
}
// Prefix test at a node: sinks Z (all in U), `extra` further wires may be read.  false = no least circuit below.
static inline bool prefixBounds(const Ctx& c, int ng, u32 Z, int extra) {
  if (extra > 3) return true;
  int U[8]; int q = 0, sum = 0;
  for (u32 z = Z; z; z &= z - 1) { U[q] = N + __builtin_ctz(z); sum += c.cw[U[q]]; q++; }
  if (extra == 0) return boundsU(c, ng, U, q);
  // (a) with the `extra` most expensive other gates
  int top[3] = {0, 0, 0};
  for (int g = 0; g < ng; g++) if (!((Z >> g) & 1)) {
    int v = c.cw[N + g];
    if (v > top[0]) { top[2] = top[1]; top[1] = top[0]; top[0] = v; }
    else if (v > top[1]) { top[2] = top[1]; top[1] = v; }
    else if (v > top[2]) top[2] = v;
  }
  int s2 = sum;
  for (int e = 0; e < extra; e++) s2 += top[e];
  if (s2 < ng) return false;
  if (extra != 1) return true;
  // exactly one further wire: U = Z (the slot unused or an input) or U = Z + one other gate
  if (boundsU(c, ng, U, q)) return true;
  for (int g = 0; g < ng; g++) if (!((Z >> g) & 1)) { U[q] = N + g; if (boundsU(c, ng, U, q + 1)) return true; }
  return false;
}
static inline u32 coneOf(const Ctx& c, int k, const Cand& cd) {
  return (1u << k) | (cd.a >= N ? c.cone[cd.a - N] : 0) | ((cd.op != OP_NOT && cd.b >= N) ? c.cone[cd.b - N] : 0);
}

// ------------------------------------------------------------------ direct completions of the last gates
// These try a SUPERSET of what the candidate lists would give (banned or duplicate functions are not
// filtered out), so nothing is lost, and every mark is still a real circuit.
//
// Three sinks, two gates left: gate ks = s_i op s_j, output = (gate ks) op s_l.
static inline void closeTight3(Ctx& c, int ks, u32 Z) {
  int s[3]; int q = 0;
  for (u32 z = Z; z; z &= z - 1) s[q++] = N + __builtin_ctz(z);
  c.tight++;
  for (int l = 0; l < 3; l++) {
    const int i = s[(l + 1) % 3], j = s[(l + 2) % 3], x = s[l];
    const u32 a = c.wires[i], b = c.wires[j], w = c.wires[x];
    u32 g = a & b;
    if (g != a && g != b && g != 0) {
      Cand cd{g, OP_AND, (u8)i, (u8)j, 0};
      mark(c, ks, cd, g & w, OP_AND, x); mark(c, ks, cd, g | w, OP_OR, x);
    }
    g = a | b;
    if (g != a && g != b && g != FULL) {
      Cand cd{g, OP_OR, (u8)i, (u8)j, 0};
      mark(c, ks, cd, g & w, OP_AND, x); mark(c, ks, cd, g | w, OP_OR, x);
    }
  }
}
// Four sinks, three gates left: gate ks = s_i op s_j, then three sinks and two gates.
static inline void closeTight4(Ctx& c, int ks, u32 Z) {
  int s[4]; int q = 0;
  for (u32 z = Z; z; z &= z - 1) s[q++] = N + __builtin_ctz(z);
  const int W = N + ks;
  for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) {
    const u32 a = c.wires[s[i]], b = c.wires[s[j]];
    const u32 Z2 = (Z & ~(1u << (s[i] - N)) & ~(1u << (s[j] - N))) | (1u << ks);
    for (int op = 0; op < 2; op++) {
      const u32 g = op == OP_AND ? (a & b) : (a | b);
      if (g == a || g == b || g == 0 || g == FULL) continue;
      c.wires[W] = g; c.gop[ks] = (u8)op; c.ga[ks] = (u8)s[j]; c.gb[ks] = (u8)s[i];
      if (useCost) {
        c.cw[W] = cost[g].load(std::memory_order_relaxed);
        c.cone[ks] = (1u << ks) | c.cone[s[i] - N] | c.cone[s[j] - N];
        if (!prefixBounds(c, ks + 1, Z2, 0)) { c.cpr++; continue; }
      }
      closeTight3(c, ks + 1, Z2);
    }
  }
}
// Two sinks s1, s2, two gates left.  With one further wire y the shapes are
//   (s1 op y) op s2,   (s2 op y) op s1,   (s1 op s2) op y,   and with NOT:  not(s) op s',  not(s1 op s2).
static inline void closeTwo(Ctx& c, int ks, u32 Z) {
  const int s1 = N + __builtin_ctz(Z), s2 = N + __builtin_ctz(Z & (Z - 1));
  const int W = N + ks;
  const u32 a = c.wires[s1], b = c.wires[s2];
  c.two++;
  int U[3] = {s1, s2, 0};
  const bool okNone = !useCost || boundsU(c, ks, U, 2);        // U = {s1, s2}: also covers y = an input
  const u32 gand = a & b, gor = a | b;
  const bool vand = gand != a && gand != b && gand != 0, vor = gor != a && gor != b && gor != FULL;
  const Cand cand{gand, OP_AND, (u8)s2, (u8)s1, 0}, cor{gor, OP_OR, (u8)s2, (u8)s1, 0};
  for (int y = 0; y < W; y++) {
    if (y == s1 || y == s2) continue;
    if (y < N) { if (!okNone) continue; }
    else if (useCost) { U[2] = y; if (!boundsU(c, ks, U, 3)) continue; }
    const u32 w = c.wires[y];
    u32 f = a & w;
    if (f != a && f != w && f != 0) { Cand cd{f, OP_AND, (u8)s1, (u8)y, 0}; mark(c, ks, cd, f & b, OP_AND, s2); mark(c, ks, cd, f | b, OP_OR, s2); }
    f = a | w;
    if (f != a && f != w && f != FULL) { Cand cd{f, OP_OR, (u8)s1, (u8)y, 0}; mark(c, ks, cd, f & b, OP_AND, s2); mark(c, ks, cd, f | b, OP_OR, s2); }
    f = b & w;
    if (f != b && f != w && f != 0) { Cand cd{f, OP_AND, (u8)s2, (u8)y, 0}; mark(c, ks, cd, f & a, OP_AND, s1); mark(c, ks, cd, f | a, OP_OR, s1); }
    f = b | w;
    if (f != b && f != w && f != FULL) { Cand cd{f, OP_OR, (u8)s2, (u8)y, 0}; mark(c, ks, cd, f & a, OP_AND, s1); mark(c, ks, cd, f | a, OP_OR, s1); }
    if (vand) { mark(c, ks, cand, gand & w, OP_AND, y); mark(c, ks, cand, gand | w, OP_OR, y); }
    if (vor) { mark(c, ks, cor, gor & w, OP_AND, y); mark(c, ks, cor, gor | w, OP_OR, y); }
  }
  if (allowNot && okNone) {
    Cand n1{~a & FULL, OP_NOT, (u8)s1, 0, 0}, n2{~b & FULL, OP_NOT, (u8)s2, 0, 0};
    mark(c, ks, n1, n1.f & b, OP_AND, s2); mark(c, ks, n1, n1.f | b, OP_OR, s2);
    mark(c, ks, n2, n2.f & a, OP_AND, s1); mark(c, ks, n2, n2.f | a, OP_OR, s1);
    if (vand) mark(c, ks, cand, ~gand & FULL, OP_NOT, 0);
    if (vor) mark(c, ks, cor, ~gor & FULL, OP_NOT, 0);
  }
}

// set has k = R-2 gates; each candidate f becomes gate k, and the output is gate k+1 = f op x.
static inline void leafLevel(Ctx& c, int k, const Cand* L, int nL, u32 Z) {
  const int W = N + k;
  for (int i = 0; i < nL; i++) {
    const Cand& cd = L[i];
    u32 Z1 = 0;
    if (useSink) {
      Z1 = Z;
      if (cd.a >= N) Z1 &= ~(1u << (cd.a - N));
      if (cd.op != OP_NOT && cd.b >= N) Z1 &= ~(1u << (cd.b - N));
      if (Z1 & (Z1 - 1)) continue;            // two or more sinks besides f: one more gate cannot use them all
    }
    c.leafc++;
    const u32 f = cd.f;
    if (useCost && useSink) {
      // final circuit: k gates, gate k = f, output = f op x, so U = {f, x}
      c.wires[W] = f;
      c.cw[W] = cost[f].load(std::memory_order_relaxed);
      c.cone[k] = coneOf(c, k, cd);
      int U[2] = {W, 0};
      if (Z1) {
        const int x = N + __builtin_ctz(Z1);
        U[1] = x;
        if (!boundsU(c, k + 1, U, 2)) continue;
        const u32 w = c.wires[x];
        mark(c, k, cd, f & w, OP_AND, x); mark(c, k, cd, f | w, OP_OR, x);
      } else {
        // f used up every sink, so every gate is in its cone.  x an input (or the output is NOT f): U = {f}
        // and f itself must need all k+1 gates.  x a gate: U = {f, x}, x may be shared, test the pair.
        const int cf = c.cw[W];
        const bool full = cf >= k + 1;
        for (int x = 0; x < W; x++) {
          if (x < N) { if (!full) continue; }
          else if (cf + (int)c.cw[x] < k + 1 || cf < __builtin_popcount(c.cone[k] & ~c.cone[x - N])) continue;
          const u32 w = c.wires[x];
          mark(c, k, cd, f & w, OP_AND, x); mark(c, k, cd, f | w, OP_OR, x);
        }
        if (allowNot && full) mark(c, k, cd, ~f & FULL, OP_NOT, 0);
      }
      continue;
    }
    if (Z1) {
      int x = N + __builtin_ctz(Z1); u32 w = c.wires[x];
      mark(c, k, cd, f & w, OP_AND, x); mark(c, k, cd, f | w, OP_OR, x);
    } else {
      for (int x = 0; x < W; x++) {
        u32 w = c.wires[x];
        mark(c, k, cd, f & w, OP_AND, x); mark(c, k, cd, f | w, OP_OR, x);
      }
      if (allowNot) mark(c, k, cd, ~f & FULL, OP_NOT, 0);
    }
  }
}

static void node(Ctx& c, int k, const Cand* L, int nL, u32 Z, const std::vector<u16>* H) {
  if (k == R - 2) { leafLevel(c, k, L, nL, Z); return; }
  const int W = N + k;
  const bool sym = useSym && H && H->size() > 1;
  Cand* L2 = c.lists[k + 1].data();
  const int budget = R - k;                    // sinks allowed after adding gate k (remaining gates + 1)
  auto& dead = c.dead[k]; auto& srt = c.sorted[k]; auto& orb = c.orb[k];
  if (sym) {
    dead.assign(nL, 0);
    srt.resize(nL);
    for (int i = 0; i < nL; i++) srt[i] = {L[i].f, i};
    std::sort(srt.begin(), srt.end());
  }
  for (int i = 0; i < nL; i++) {
    if (sym && dead[i]) continue;
    if (stopFlag.load(std::memory_order_relaxed)) return;
    const Cand cd = L[i];
    u32 Z1 = Z;
    if (cd.a >= N) Z1 &= ~(1u << (cd.a - N));
    if (cd.op != OP_NOT && cd.b >= N) Z1 &= ~(1u << (cd.b - N));
    Z1 |= 1u << k;
    const std::vector<u16>* H2 = nullptr;
    if (sym) {
      auto& Hn = c.Hs[k + 1]; Hn.clear(); orb.clear();
      for (u16 h : *H) {
        u32 g = gapply(G[h], cd.f);
        if (g == cd.f) { Hn.push_back(h); continue; }
        auto it = std::lower_bound(srt.begin(), srt.end(), std::make_pair(g, 0));
        if (it == srt.end() || it->first != g) { fprintf(stderr, "internal error: orbit image not a candidate\n"); std::abort(); }
        orb.push_back(it->second);
      }
      H2 = &Hn;
    }
    const int q = __builtin_popcount(Z1);
    if (useSink && q > budget) {
      if (sym) for (int j : orb) dead[j] = 1;
      continue;
    }
    c.wires[W] = cd.f; c.gop[k] = cd.op; c.ga[k] = cd.a; c.gb[k] = cd.b;
    if (useCost && useSink) {
      c.cw[W] = cost[cd.f].load(std::memory_order_relaxed);
      c.cone[k] = coneOf(c, k, cd);
      if (!prefixBounds(c, k + 1, Z1, budget - q)) {
        c.cpr++;
        if (sym) for (int j : orb) dead[j] = 1;
        continue;
      }
    }
    c.nodes++;
    if (useSink && useTight) {
      bool closed = true;
      if (k + 1 == R - 2 && q == 3) closeTight3(c, k + 1, Z1);
      else if (k + 1 == R - 2 && q == 2) closeTwo(c, k + 1, Z1);
      else if (k + 1 == R - 3 && q == 4) closeTight4(c, k + 1, Z1);
      else closed = false;
      if (closed) { if (sym) for (int j : orb) dead[j] = 1; continue; }
    }
    int n2 = 0;
    if (!sym) { n2 = nL - i - 1; std::memcpy(L2, L + i + 1, (size_t)n2 * sizeof(Cand)); }
    else for (int j = i + 1; j < nL; j++) if (!dead[j]) L2[n2++] = L[j];
    const int u0 = c.nundo;
    const u32 f = cd.f;
    for (int x = 0; x < W; x++) {
      u32 w = c.wires[x];
      u32 h = f & w;
      if (h != f && h != w && h != 0 && c.insert(h)) L2[n2++] = Cand{h, OP_AND, (u8)W, (u8)x, 0};
      h = f | w;
      if (h != f && h != w && h != FULL && c.insert(h)) L2[n2++] = Cand{h, OP_OR, (u8)W, (u8)x, 0};
    }
    if (allowNot) { u32 h = ~f & FULL; if (c.insert(h)) L2[n2++] = Cand{h, OP_NOT, (u8)W, 0, 0}; }
    if (n2 >= LISTCAP || c.nundo >= (int)TABSZ / 2) { fprintf(stderr, "internal error: candidate list overflow\n"); std::abort(); }
    if (nthreads > 1 && k + 1 <= R - 2 - splitLevels && qsize.load(std::memory_order_relaxed) < nthreads) {
      Task* t = new Task; t->k = k + 1; t->Z = Z1;
      std::memcpy(t->wires, c.wires, sizeof(t->wires));
      std::memcpy(t->gop, c.gop, sizeof(t->gop)); std::memcpy(t->ga, c.ga, sizeof(t->ga)); std::memcpy(t->gb, c.gb, sizeof(t->gb));
      std::memcpy(t->cw, c.cw, sizeof(t->cw)); std::memcpy(t->cone, c.cone, sizeof(t->cone));
      t->L.assign(L2, L2 + n2);
      if (H2) t->H = *H2;
      for (u32 s = 0; s < TABSZ; s++) if (c.tab[s] != EMPTY) t->seen.push_back(c.tab[s]);
      pushTask(t);
    } else {
      node(c, k + 1, L2, n2, Z1, H2);
    }
    c.rollback(u0);
    if (sym) for (int j : orb) dead[j] = 1;
  }
}

static void worker(Ctx* cp) {
  Ctx& c = *cp;
  while (Task* t = popTask()) {
    c.clear();
    std::memcpy(c.wires, t->wires, sizeof(c.wires));
    std::memcpy(c.gop, t->gop, sizeof(c.gop)); std::memcpy(c.ga, t->ga, sizeof(c.ga)); std::memcpy(c.gb, t->gb, sizeof(c.gb));
    std::memcpy(c.cw, t->cw, sizeof(c.cw)); std::memcpy(c.cone, t->cone, sizeof(c.cone));
    for (u32 s : t->seen) c.insert(s);
    c.nundo = 0;
    int k = t->k;
    std::copy(t->L.begin(), t->L.end(), c.lists[k].begin());
    c.Hs[k] = t->H;
    c.tasks++;
    node(c, k, c.lists[k].data(), (int)t->L.size(), t->Z, &c.Hs[k]);
    delete t;
    doneTask();
  }
}

// ------------------------------------------------------------------ setup: inputs, group, classes
static std::vector<std::vector<int>> indexMaps(int n, bool enc) {
  std::vector<std::vector<int>> res;
  if (!enc) {
    std::vector<int> p(n);
    for (int i = 0; i < n; i++) p[i] = i;
    do res.push_back(p); while (std::next_permutation(p.begin(), p.end()));
  } else {
    int kb = 0; while ((1 << kb) < n) kb++;
    std::vector<int> bp(kb);
    for (int i = 0; i < kb; i++) bp[i] = i;
    do {
      for (int c = 0; c < n; c++) {
        std::vector<int> p(n);
        for (int u = 0; u < n; u++) {
          int v = 0;
          for (int i = 0; i < kb; i++) if ((u >> i) & 1) v |= 1 << bp[i];
          p[u] = v ^ c;
        }
        res.push_back(p);
      }
    } while (std::next_permutation(bp.begin(), bp.end()));
  }
  return res;
}

static void setup() {
  P = gn * gm; FULL = (P == 32) ? ~0u : ((1u << P) - 1);
  IN.clear(); INNAME.clear();
  for (int u = 0; u < gn; u++) { u32 f = 0; for (int v = 0; v < gm; v++) f |= 1u << (u * gm + v); IN.push_back(f); INNAME.push_back("r" + std::to_string(u)); }
  for (int v = 0; v < gm; v++) { u32 f = 0; for (int u = 0; u < gn; u++) f |= 1u << (u * gm + v); IN.push_back(f); INNAME.push_back("c" + std::to_string(v)); }
  if (encMode) {
    int kr = 0; while ((1 << kr) < gn) kr++;
    int kc = 0; while ((1 << kc) < gm) kc++;
    if ((1 << kr) != gn || (1 << kc) != gm) pnp::die("--enc needs n and m to be powers of two");
    for (int i = 0; i < kr; i++) for (int a = 0; a < 2; a++) {
      u32 f = 0;
      for (int u = 0; u < gn; u++) if (((u >> i) & 1) == a) f |= IN[u];
      IN.push_back(f); INNAME.push_back("rb" + std::to_string(i) + "=" + std::to_string(a));
    }
    for (int i = 0; i < kc; i++) for (int a = 0; a < 2; a++) {
      u32 f = 0;
      for (int v = 0; v < gm; v++) if (((v >> i) & 1) == a) f |= IN[gn + v];
      IN.push_back(f); INNAME.push_back("cb" + std::to_string(i) + "=" + std::to_string(a));
    }
  }
  N = (int)IN.size();
  if (N > 48 || N + MAXG > MAXW) pnp::die("too many inputs");
  // symmetry group
  auto RM = indexMaps(gn, encMode), CM = indexMaps(gm, encMode);
  G.clear();
  for (int t = 0; t < ((gn == gm && useTranspose) ? 2 : 1); t++)
    for (auto& rm : RM) for (auto& cm : CM) {
      GE g{};
      for (int u = 0; u < gn; u++) for (int v = 0; v < gm; v++)
        g.pp[u * gm + v] = (u8)(t == 0 ? rm[u] * gm + cm[v] : rm[v] * gm + cm[u]);
      for (int i = 0; i < N; i++) {
        u32 img = gapply(g, IN[i]);
        int j = (int)(std::find(IN.begin(), IN.end(), img) - IN.begin());
        if (j >= N) pnp::die("internal: group element does not preserve the input set");
        g.ip[i] = (u8)j;
      }
      G.push_back(g);
    }
  if (G.size() > 65535) pnp::die("group too large");
  // classes
  size_t F = (size_t)1 << P;
  classOf.assign(F, 0xFFFF);
  classes.clear();
  std::vector<u32> seenTmp;
  for (size_t f = 0; f < F; f++) {
    if (classOf[f] != 0xFFFF) continue;
    if (classes.size() >= 0xFFFF) pnp::die("too many classes");
    u16 id = (u16)classes.size();
    u32 cnt = 0;
    for (auto& g : G) { u32 h = gapply(g, (u32)f); if (classOf[h] == 0xFFFF) { classOf[h] = id; cnt++; } }
    classes.push_back({(u32)f, cnt});
  }
}

// circuit text for class cl (witness transported to the class representative), verified.
static std::string cktText(const std::vector<std::array<int, 3>>& gates, int out) {
  std::string s = "inputs " + std::to_string(N) + "\n";
  for (auto& g : gates) {
    if (g[0] == OP_NOT) s += "not " + std::to_string(g[1]) + "\n";
    else if (g[0] == 3) s += "and\n";
    else s += std::string(g[0] == OP_AND ? "and " : "or ") + std::to_string(g[1]) + " " + std::to_string(g[2]) + "\n";
  }
  s += "out " + std::to_string(out) + "\n";
  return s;
}
static u32 evalGates(const std::vector<std::array<int, 3>>& gates, int out) {
  std::vector<u32> w(IN.begin(), IN.end());
  for (auto& g : gates) {
    auto rd = [&](int i) { return (i >= 0 && i < (int)w.size()) ? w[i] : 0u; };
    u32 v;
    if (g[0] == 3) v = FULL;
    else if (g[0] == OP_NOT) v = ~rd(g[1]) & FULL;
    else if (g[0] == OP_AND) v = rd(g[1]) & rd(g[2]);
    else v = rd(g[1]) | rd(g[2]);
    w.push_back(v);
  }
  return (out >= 0 && out < (int)w.size()) ? w[out] : 0u;
}
// independent re-check through the shared header (pnp::verify) against a spec built for the representative
static bool verifyShared(u32 rep, const std::string& text, int size) {
  pnp::Spec s;
  s.kind = "points"; s.N = N; s.K = 1; s.P = (size_t)P; s.W = 1;
  s.in.assign(N, pnp::Col(1, 0)); s.tgt.assign(1, pnp::Col(1, rep)); s.care.assign(1, pnp::Col(1, FULL));
  for (int i = 0; i < N; i++) s.in[i][0] = IN[i];
  std::istringstream is(text);
  pnp::Circuit c = pnp::parse_circuit(is);
  if (c.size() != size) return false;
  if (!pnp::basis_ok(c, allowNot ? "aon" : "ao")) return false;
  return pnp::verify(s, c).ok;
}

static const char* USAGE =
  "usage: startab --n N [--m M] [--basis ao|aon] [--enc] [--rmax R] [--tlimit SEC] [-j T]\n"
  "               [--out F.jsonl] [--costs F.bin] [--ckpt F.ckpt] [--resume F.ckpt] [--ub]\n"
  "               [--split L] [--nosym] [--nosink] [--notight] [--nocost] [--notranspose] [-q]\n"
  "  exact minimum number of gates for EVERY n x m bipartite graph (n*m <= 25), basis ao (AND/OR) or aon (AND/OR/NOT),\n"
  "  inputs = the n+m stars (--enc: plus the free row-bit / column-bit sets).  One JSON line per symmetry class.\n";

struct CkptHeader { char magic[8]; int32_t n, m, enc, aon, transpose, lastComplete, nclasses, pad; };

int main(int argc, char** argv) {
  T0 = std::chrono::steady_clock::now();
  int rmax = MAXG - 1;
  nthreads = std::getenv("PNP_THREADS") ? atoi(std::getenv("PNP_THREADS")) : 1;
  std::string outp, costp, ckptp, resumep, basis = "ao";
  bool doUB = false;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto nxt = [&]() -> const char* { if (i + 1 >= argc) pnp::die("missing value for " + a); return argv[++i]; };
    if (a == "--n") gn = atoi(nxt());
    else if (a == "--m") gm = atoi(nxt());
    else if (a == "--basis") basis = nxt();
    else if (a == "--enc") encMode = true;
    else if (a == "--rmax") rmax = atoi(nxt());
    else if (a == "--tlimit") tlimit = atof(nxt());
    else if (a == "-j") nthreads = atoi(nxt());
    else if (a == "--nosym") useSym = false;
    else if (a == "--nosink") useSink = false;
    else if (a == "--notight") useTight = false;
    else if (a == "--nocost") useCost = false;
    else if (a == "--notranspose") useTranspose = false;
    else if (a == "--out") outp = nxt();
    else if (a == "--costs") costp = nxt();
    else if (a == "--ckpt") ckptp = nxt();
    else if (a == "--split") splitLevels = atoi(nxt());
    else if (a == "--ub") doUB = true;
    else if (a == "--resume") resumep = nxt();
    else if (a == "--seed") nxt();            // accepted for interface uniformity; the search has no randomness
    else if (a == "-q") quiet = true;
    else pnp::die("unknown argument " + a + "\n" + USAGE);
  }
  if (gm == 0) gm = gn;
  if (gn < 1 || gm < 1 || gn * gm > 25) pnp::die(std::string("need 1 <= n*m <= 25\n") + USAGE);
  if (basis != "ao" && basis != "aon") pnp::die("basis must be ao or aon");
  allowNot = basis == "aon";
  if (nthreads < 1) nthreads = 1;
  if (rmax > MAXG - 1) rmax = MAXG - 1;
  setup();
  const size_t F = (size_t)1 << P;
  fprintf(stderr, "startab: %dx%d%s basis=%s inputs=%d points=%d functions=%zu group=%zu classes=%zu threads=%d sym=%d sink=%d tight=%d cost=%d (setup %.1fs)\n",
          gn, gm, encMode ? " +encoder wires" : "", basis.c_str(), N, P, F, G.size(), classes.size(), nthreads, (int)useSym, (int)useSink, (int)useTight, (int)useCost, now());

  cost = new std::atomic<u8>[F];
  for (size_t f = 0; f < F; f++) cost[f].store(255, std::memory_order_relaxed);
  const size_t UW = (F + 63) / 64;
  unres = new std::atomic<u64>[UW];
  wit.assign(classes.size(), Wit());
  hasWit = new std::atomic<u8>[classes.size()];
  for (size_t i = 0; i < classes.size(); i++) hasWit[i].store(0);

  // root candidates: every function obtainable with one gate from the inputs
  std::vector<Cand> root;
  {
    std::vector<u32> seen = IN; seen.push_back(0); seen.push_back(FULL);
    auto add = [&](u32 h, int op, int a, int b) {
      if (std::find(seen.begin(), seen.end(), h) != seen.end()) return;
      seen.push_back(h); root.push_back(Cand{h, (u8)op, (u8)a, (u8)b, 0});
    };
    for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) { add(IN[j] & IN[i], OP_AND, j, i); add(IN[j] | IN[i], OP_OR, j, i); }
    if (allowNot) for (int i = 0; i < N; i++) add(~IN[i] & FULL, OP_NOT, i, 0);
  }
  int lastComplete = 1;
  if (!resumep.empty()) {
    FILE* cf = fopen(resumep.c_str(), "rb");
    if (!cf) pnp::die("cannot open " + resumep);
    CkptHeader h;
    if (fread(&h, sizeof h, 1, cf) != 1 || std::memcmp(h.magic, "STARTAB1", 8) != 0) pnp::die("bad checkpoint");
    if (h.n != gn || h.m != gm || h.enc != (int)encMode || h.aon != (int)allowNot || h.transpose != (int)useTranspose || h.nclasses != (int)classes.size())
      pnp::die("checkpoint is for a different problem");
    std::vector<u8> buf(F);
    if (fread(buf.data(), 1, F, cf) != F) pnp::die("short checkpoint");
    for (size_t f = 0; f < F; f++) cost[f].store(buf[f], std::memory_order_relaxed);
    std::vector<u8> hw(classes.size());
    if (fread(hw.data(), 1, hw.size(), cf) != hw.size()) pnp::die("short checkpoint");
    for (size_t i = 0; i < hw.size(); i++) hasWit[i].store(hw[i]);
    if (fread(wit.data(), sizeof(Wit), wit.size(), cf) != wit.size()) pnp::die("short checkpoint");
    fclose(cf);
    lastComplete = h.lastComplete;
    fprintf(stderr, "resumed from %s: last complete pass %d\n", resumep.c_str(), lastComplete);
  } else {
    // size 0: the empty graph (a missing wire reads false) and the input wires themselves
    cost[0].store(0);
    for (u32 f : IN) cost[f].store(0);
    // size 1: the constant true (one AND gate reading nothing) and the root candidates
    if (cost[FULL].load() > 1) cost[FULL].store(1);
    for (auto& cd : root) if (cost[cd.f].load() > 1) {
      cost[cd.f].store(1);
      u16 cl = classOf[cd.f];
      if (!hasWit[cl].exchange(1)) { Wit& w = wit[cl]; w.T = cd.f; w.ng = 1; w.op[0] = cd.op; w.a[0] = cd.a; w.b[0] = cd.b; }
    }
  }

  std::vector<u8> cmin(classes.size());
  auto symmetrize = [&](size_t& unresF, size_t& unresC) {
    std::fill(cmin.begin(), cmin.end(), 255);
    for (size_t f = 0; f < F; f++) { u8 v = cost[f].load(std::memory_order_relaxed); if (v < cmin[classOf[f]]) cmin[classOf[f]] = v; }
    unresF = 0; unresC = 0;
    for (size_t f = 0; f < F; f++) { u8 v = cmin[classOf[f]]; cost[f].store(v, std::memory_order_relaxed); if (v == 255) unresF++; }
    for (u8 v : cmin) if (v == 255) unresC++;
  };
  size_t unresF = 0, unresC = 0;
  symmetrize(unresF, unresC);
  fprintf(stderr, "pass %2d: unresolved classes %zu functions %zu  (%.2fs)\n", lastComplete, unresC, unresF, now());

  size_t bad = 0;
  std::vector<size_t> hist(MAXG + 2, 0);
  typedef std::vector<std::array<int, 3>> Gates;
  // circuit for the representative of a resolved class (trivial targets, or the stored witness transported by a group element)
  auto classCircuit = [&](size_t cl, Gates& gates, int& outw) -> bool {
    u32 rep = classes[cl].rep;
    gates.clear(); outw = -1;
    if (rep == 0) { outw = N; return true; }                    // a wire that does not exist reads false
    auto it = std::find(IN.begin(), IN.end(), rep);
    if (it != IN.end()) { outw = (int)(it - IN.begin()); return true; }
    if (rep == FULL && !hasWit[cl].load()) { gates.push_back({3, 0, 0}); outw = N; return true; }
    if (!hasWit[cl].load()) return false;
    const Wit& w = wit[cl];
    const GE* ge = nullptr;
    for (auto& g : G) if (gapply(g, w.T) == rep) { ge = &g; break; }
    if (!ge) { fprintf(stderr, "internal error: witness of class %zu not in the class\n", cl); std::abort(); }
    auto mp = [&](int i) { return i < N ? (int)ge->ip[i] : i; };
    for (int g = 0; g < w.ng; g++) gates.push_back({w.op[g], mp(w.a[g]), mp(w.b[g])});
    outw = N + w.ng - 1;
    return true;
  };
  // upper bounds for classes the passes did not reach (filled by the --ub step): circuit for the representative
  struct UBC { bool have = false; Gates gates; int outw = -1; };
  std::vector<UBC> ubc(classes.size());
  // ---------------------------------------------------------------- output (after every complete pass and at the end)
  auto writeOut = [&](bool lastPassComplete) {
    if (!ckptp.empty()) {
      std::string tmp = ckptp + ".tmp";
      FILE* cf = fopen(tmp.c_str(), "wb");
      if (!cf) pnp::die("cannot write " + tmp);
      CkptHeader h{}; std::memcpy(h.magic, "STARTAB1", 8);
      h.n = gn; h.m = gm; h.enc = encMode; h.aon = allowNot; h.transpose = useTranspose; h.lastComplete = lastComplete; h.nclasses = (int)classes.size();
      fwrite(&h, sizeof h, 1, cf);
      std::vector<u8> buf(F);
      for (size_t f = 0; f < F; f++) buf[f] = cost[f].load();
      fwrite(buf.data(), 1, F, cf);
      std::vector<u8> hw(classes.size());
      for (size_t i = 0; i < hw.size(); i++) hw[i] = hasWit[i].load();
      fwrite(hw.data(), 1, hw.size(), cf);
      fwrite(wit.data(), sizeof(Wit), wit.size(), cf);
      fclose(cf);
      std::rename(tmp.c_str(), ckptp.c_str());
    }
    if (!costp.empty()) {
      FILE* cf = fopen(costp.c_str(), "wb");
      if (!cf) pnp::die("cannot write " + costp);
      std::vector<u8> buf(F);
      for (size_t f = 0; f < F; f++) buf[f] = cost[f].load();
      fwrite(buf.data(), 1, F, cf); fclose(cf);
    }
    if (outp.empty() && !lastPassComplete) return;          // stdout: only once, at the end
    std::string tmp = outp + ".tmp";
    FILE* out = outp.empty() ? stdout : fopen(tmp.c_str(), "w");
    if (!out) pnp::die("cannot write " + outp);
    fprintf(out, "{\"header\":true,\"n\":%d,\"m\":%d,\"enc\":%s,\"basis\":\"%s\",\"inputs\":%d,\"group\":%zu,\"transpose\":%s,\"classes\":%zu,\"last_complete_pass\":%d,\"unresolved\":%zu,\"input_names\":[",
            gn, gm, encMode ? "true" : "false", basis.c_str(), N, G.size(), (gn == gm && useTranspose) ? "true" : "false", classes.size(), lastComplete, unresC);
    for (int i = 0; i < N; i++) fprintf(out, "%s\"%s\"", i ? "," : "", INNAME[i].c_str());
    fprintf(out, "]}\n");
    bad = 0; std::fill(hist.begin(), hist.end(), 0);
    for (size_t cl = 0; cl < classes.size(); cl++) {
      u32 rep = classes[cl].rep;
      u8 v = cmin[cl];
      fprintf(out, "{\"cls\":%zu,\"f\":%u,\"rows\":[", cl, rep);
      for (int u = 0; u < gn; u++) fprintf(out, "%s%u", u ? "," : "", (rep >> (u * gm)) & ((1u << gm) - 1));
      fprintf(out, "],\"orbit\":%u,\"ccls\":%u,", classes[cl].orbit, (unsigned)classOf[~rep & FULL]);
      Gates gates; int outw = -1;
      bool exact = true;
      int sz = v;
      if (v == 255) {
        hist[MAXG + 1]++;
        if (!ubc[cl].have) { fprintf(out, "\"size\":null,\"exact\":false,\"lower\":%d}\n", lastComplete + 1); continue; }
        gates = ubc[cl].gates; outw = ubc[cl].outw; sz = (int)gates.size();
        exact = sz == lastComplete + 1;                        // a circuit at the proved lower bound
      } else {
        hist[v]++;
        if (!classCircuit(cl, gates, outw)) { fprintf(stderr, "internal error: class %zu has size %d but no witness\n", cl, v); bad++; fprintf(out, "\"size\":%d,\"exact\":true}\n", v); continue; }
      }
      std::string text = cktText(gates, outw);
      bool ok = (int)gates.size() == sz && evalGates(gates, outw) == rep && verifyShared(rep, text, sz) && (v == 255 ? sz >= lastComplete + 1 : true);
      if (!ok) { fprintf(stderr, "VERIFY FAILED for class %zu (f=%u size %d)\n", cl, rep, sz); bad++; }
      std::string esc;
      for (char ch : text) { if (ch == '\n') esc += "\\n"; else esc += ch; }
      fprintf(out, "\"size\":%d,\"exact\":%s,", sz, exact ? "true" : "false");
      if (v == 255) fprintf(out, "\"lower\":%d,", lastComplete + 1);
      fprintf(out, "\"verified\":%s,\"witness\":\"%s\"}\n", ok ? "true" : "false", esc.c_str());
    }
    if (out != stdout) { fclose(out); std::rename(tmp.c_str(), outp.c_str()); }
  };

  std::vector<Ctx*> ctxs;
  for (int t = 0; t < nthreads; t++) ctxs.push_back(new Ctx);
  u64 totNodes = 0, totOps = 0;
  for (R = lastComplete + 1; R <= rmax && unresC > 0; R++) {
    double t1 = now();
    for (size_t w = 0; w < UW; w++) unres[w].store(0, std::memory_order_relaxed);
    for (size_t f = 0; f < F; f++) if (cost[f].load(std::memory_order_relaxed) == 255) unres[f >> 6].fetch_or(u64(1) << (f & 63), std::memory_order_relaxed);
    Task* t = new Task; t->k = 0; t->Z = 0;
    for (int i = 0; i < N; i++) t->wires[i] = IN[i];
    std::memset(t->cw, 0, sizeof(t->cw)); std::memset(t->cone, 0, sizeof(t->cone));
    t->L = root;
    for (size_t h = 0; h < G.size(); h++) t->H.push_back((u16)h);
    t->seen = IN; t->seen.push_back(0); t->seen.push_back(FULL);
    for (auto& cd : root) t->seen.push_back(cd.f);
    for (auto c : ctxs) { c->nodes = c->leafc = c->ops = c->newmarks = c->tasks = c->tight = c->two = c->cpr = 0; }
    remainingClasses.store((long)unresC);
    active = 0; pushTask(t);
    std::atomic<bool> done{false};
    std::thread watchdog;
    if (tlimit > 0) watchdog = std::thread([&] {
      while (!done.load()) { if (now() > tlimit) { stopFlag.store(true); break; } std::this_thread::sleep_for(std::chrono::milliseconds(50)); }
    });
    std::vector<std::thread> th;
    for (int i = 1; i < nthreads; i++) th.emplace_back(worker, ctxs[i]);
    worker(ctxs[0]);
    for (auto& x : th) x.join();
    done.store(true);
    if (watchdog.joinable()) watchdog.join();
    u64 nodes = 0, leafc = 0, ops = 0, tasks = 0, tight = 0, two = 0, cpr = 0;
    for (auto c : ctxs) { two += c->two; cpr += c->cpr; nodes += c->nodes; leafc += c->leafc; ops += c->ops; tasks += c->tasks; tight += c->tight; }
    totNodes += nodes + leafc; totOps += ops;
    bool complete = !stopFlag.load() || allDone.load();     // allDone: nothing is left to find, so the pass need not finish
    symmetrize(unresF, unresC);
    double dt = now() - t1;
    fprintf(stderr, "pass %2d: %s  sets %llu (3-sink %llu, 2-sink %llu, cost-pruned %llu)  leaf-sets %llu  gate-ops %llu  tasks %llu  %.2fs  (%.3g sets/s, %.3g ops/s)  unresolved classes %zu functions %zu\n",
            R, allDone.load() ? "all classes resolved, stopped early" : complete ? "complete" : "INTERRUPTED (time limit)", (unsigned long long)nodes, (unsigned long long)tight, (unsigned long long)two, (unsigned long long)cpr, (unsigned long long)leafc,
            (unsigned long long)ops, (unsigned long long)tasks, dt, (nodes + leafc) / std::max(dt, 1e-9), ops / std::max(dt, 1e-9), unresC, unresF);
    if (!complete) break;
    lastComplete = R;
    if (R >= 8 && !outp.empty()) writeOut(false);
  }
  fprintf(stderr, "done: last complete pass %d, unresolved classes %zu, total sets %llu, gate-ops %llu, %.2fs\n",
          lastComplete, unresC, (unsigned long long)totNodes, (unsigned long long)totOps, now());
  if (doUB && unresC > 0) {
    // ---------------------------------------------------------------- upper bounds by decomposition
    // For an unreached class T: T = a op b (or NOT a) with circuits already known for a and b; the two circuits
    // are concatenated, equal gates merged, unused gates dropped.  If the result has (last complete pass)+1
    // gates it is exact.  Several rounds, so that parts may themselves be classes bounded in an earlier round.
    double tu = now();
    std::vector<u8> ubcost(F);
    for (size_t f = 0; f < F; f++) ubcost[f] = cost[f].load();
    auto fnCircuit = [&](u32 a, Gates& gates, int& outw) -> bool {      // circuit for an arbitrary function with a known class circuit
      size_t cl = classOf[a];
      Gates cg; int co;
      if (cmin[cl] != 255) { if (!classCircuit(cl, cg, co)) return false; }
      else { if (!ubc[cl].have) return false; cg = ubc[cl].gates; co = ubc[cl].outw; }
      const GE* ge = nullptr;
      for (auto& g : G) if (gapply(g, classes[cl].rep) == a) { ge = &g; break; }
      if (!ge) return false;
      auto mp = [&](int i) { return i < N ? (int)ge->ip[i] : i; };
      gates.clear();
      for (auto& g : cg) gates.push_back({g[0], g[0] == 3 ? 0 : mp(g[1]), (g[0] == 3 || g[0] == OP_NOT) ? 0 : mp(g[2])});
      outw = mp(co);
      return true;
    };
    auto simplify = [&](const Gates& gates, int outw, Gates& ng, int& nout) {
      std::vector<u32> vec(IN.begin(), IN.end());                  // vectors of the wires kept so far (new numbering)
      std::vector<int> alias(N + gates.size());
      for (int i = 0; i < N; i++) alias[i] = i;
      Gates kept;
      for (size_t j = 0; j < gates.size(); j++) {
        auto g = gates[j];
        int a = alias[g[1]], b = g[0] == OP_NOT ? 0 : alias[g[2]];
        u32 v = g[0] == OP_NOT ? (~vec[a] & FULL) : g[0] == OP_AND ? (vec[a] & vec[b]) : (vec[a] | vec[b]);
        int found = -1;
        for (size_t w = 0; w < vec.size(); w++) if (vec[w] == v) { found = (int)w; break; }
        if (found >= 0) { alias[N + j] = found; continue; }
        alias[N + j] = (int)vec.size(); vec.push_back(v); kept.push_back({g[0], a, b});
      }
      int o = alias[outw];
      std::vector<char> need(N + kept.size(), 0);
      need[o] = 1;
      for (int j = (int)kept.size() - 1; j >= 0; j--) if (need[N + j]) { need[kept[j][1]] = 1; if (kept[j][0] != OP_NOT) need[kept[j][2]] = 1; }
      std::vector<int> ren(N + kept.size(), -1);
      for (int i = 0; i < N; i++) ren[i] = i;
      ng.clear();
      for (size_t j = 0; j < kept.size(); j++) if (need[N + j]) {
        ren[N + j] = N + (int)ng.size();
        ng.push_back({kept[j][0], ren[kept[j][1]], kept[j][0] == OP_NOT ? 0 : ren[kept[j][2]]});
      }
      nout = ren[o];
    };
    struct Dec { int est; u32 a, b; int op; };
    const int LB = lastComplete + 1;
    {
      // Seed: threshold-2 ("crown") constructions.  Put some of the stars into blocks B_1..B_k, let w_i be the OR
      // of block i and M = K_k(w_1..w_k), K_k = any monotone circuit that is 0 on one-hot and 1 on two-hot inputs
      // (4, 7, 10, 13 gates for k = 3..6; circuits below are checked here before use).  At the point (u, v) the
      // wires on are the blocks of row u and of column v, so M joins u and v iff both lie in blocks and in
      // different ones.  The decomposition rounds below then combine these with everything else.
      static const std::vector<Gates> KC = {
        {}, {},
        {{OP_AND, 0, 1}},
        {{OP_AND, 0, 1}, {OP_OR, 0, 1}, {OP_OR, 2, 3}, {OP_AND, 4, 5}},
        {{OP_AND, 0, 1}, {OP_OR, 0, 1}, {OP_AND, 2, 3}, {OP_OR, 2, 3}, {OP_AND, 5, 7}, {OP_OR, 6, 8}, {OP_OR, 4, 9}},
        {{OP_AND, 0, 1}, {OP_OR, 0, 1}, {OP_AND, 2, 3}, {OP_OR, 2, 3}, {OP_AND, 4, 8}, {OP_OR, 4, 8}, {OP_OR, 7, 9}, {OP_OR, 6, 11}, {OP_AND, 10, 12}, {OP_OR, 5, 13}},
        {{OP_OR, 2, 3}, {OP_AND, 4, 5}, {OP_OR, 0, 1}, {OP_OR, 4, 5}, {OP_AND, 2, 3}, {OP_OR, 10, 9}, {OP_OR, 11, 8}, {OP_OR, 7, 6}, {OP_AND, 13, 12}, {OP_AND, 0, 1}, {OP_OR, 11, 15}, {OP_AND, 8, 16}, {OP_OR, 14, 17}}};
      for (int k = 2; k <= 6; k++)
        for (int x = 0; x < (1 << k); x++) {
          const int pc = __builtin_popcount(x);
          if (pc != 1 && pc != 2) continue;
          std::vector<int> w;
          for (int i = 0; i < k; i++) w.push_back((x >> i) & 1);
          for (auto& g : KC[k]) w.push_back(g[0] == OP_AND ? (w[g[1]] & w[g[2]]) : (w[g[1]] | w[g[2]]));
          if (w.back() != (pc == 2)) { fprintf(stderr, "internal error: K_%d circuit is wrong\n", k); std::abort(); }
        }
      const int NS = gn + gm;
      std::vector<int> blk(NS, 0);
      std::vector<int> bestEst(classes.size(), 255);
      std::vector<std::vector<int>> bestBlk(classes.size());
      std::vector<u32> bestM(classes.size(), 0);
      auto leaf = [&](int k) {
        if (k < 2) return;
        int est = (int)KC[k].size(), cnt[8] = {0};
        for (int i = 0; i < NS; i++) cnt[blk[i]]++;
        for (int b = 1; b <= k; b++) est += cnt[b] - 1;
        u32 M = 0;
        for (int u = 0; u < gn; u++) if (blk[u]) for (int v = 0; v < gm; v++) if (blk[gn + v] && blk[gn + v] != blk[u]) M |= 1u << (u * gm + v);
        if (M == 0 || M == FULL) return;
        const size_t cl = classOf[M];
        if (cmin[cl] != 255 || est >= bestEst[cl]) return;
        bestEst[cl] = est; bestBlk[cl] = blk; bestM[cl] = M;
      };
      std::vector<std::pair<int, int>> stack;                     // iterative restricted-growth enumeration
      std::function<void(int, int)> rec = [&](int i, int k) {
        if (i == NS) { leaf(k); return; }
        for (int b = 0; b <= std::min(k + 1, 6); b++) { blk[i] = b; rec(i + 1, std::max(k, b)); }
      };
      rec(0, 0);
      size_t seeded = 0;
      for (size_t cl = 0; cl < classes.size(); cl++) {
        if (bestEst[cl] == 255) continue;
        const std::vector<int>& B = bestBlk[cl];
        int k = 0;
        for (int b : B) k = std::max(k, b);
        Gates all; std::vector<int> w(k + 1, -1);
        for (int b = 1; b <= k; b++)
          for (int i = 0; i < NS; i++) if (B[i] == b) {
            if (w[b] < 0) w[b] = i;
            else { all.push_back({OP_OR, w[b], i}); w[b] = N + (int)all.size() - 1; }
          }
        const int base = N + (int)all.size();
        for (auto& g : KC[k]) all.push_back({g[0], g[1] < k ? w[g[1] + 1] : base + g[1] - k, g[2] < k ? w[g[2] + 1] : base + g[2] - k});
        Gates ng; int nout;
        simplify(all, N + (int)all.size() - 1, ng, nout);
        const GE* ge = nullptr;
        for (auto& g : G) if (gapply(g, bestM[cl]) == classes[cl].rep) { ge = &g; break; }
        for (auto& g : ng) { if (g[1] < N) g[1] = ge->ip[g[1]]; if (g[0] != OP_NOT && g[2] < N) g[2] = ge->ip[g[2]]; }
        if (nout != N + (int)ng.size() - 1 || evalGates(ng, nout) != classes[cl].rep) { fprintf(stderr, "internal error: bad threshold construction\n"); std::abort(); }
        if ((int)ng.size() < LB) { fprintf(stderr, "internal error: circuit below the proved lower bound (class %zu)\n", cl); std::abort(); }
        ubc[cl].have = true; ubc[cl].gates = ng; ubc[cl].outw = nout; seeded++;
        u8 v = (u8)ng.size();
        for (auto& g : G) { u32 h = gapply(g, classes[cl].rep); if (v < ubcost[h]) ubcost[h] = v; }
      }
      fprintf(stderr, "ub seed: threshold-2 constructions for %zu unreached classes  (%.1fs)\n", seeded, now() - tu);
    }
    for (int round = 1; round <= 6; round++) {
      std::vector<size_t> todo;
      for (size_t cl = 0; cl < classes.size(); cl++)
        if (cmin[cl] == 255 && !(ubc[cl].have && (int)ubc[cl].gates.size() == LB)) todo.push_back(cl);
      if (todo.empty()) break;
      std::vector<std::vector<Dec>> best(todo.size());
      std::atomic<size_t> nx{0};
      auto work = [&] {
        for (size_t ti; (ti = nx++) < todo.size();) {
          const size_t cl = todo[ti];
          const u32 T = classes[cl].rep;
          int cur = ubc[cl].have ? (int)ubc[cl].gates.size() : 255;
          std::vector<Dec>& bl = best[ti];
          auto offer = [&](int est, u32 a, u32 b, int op) {       // keep the few best estimates below the current bound
            if (est >= cur) return;
            if (bl.size() == 6 && est >= bl.back().est) return;
            bl.push_back({est, a, b, op});
            std::sort(bl.begin(), bl.end(), [](const Dec& x, const Dec& y) { return x.est < y.est; });
            if (bl.size() > 6) bl.pop_back();
          };
          auto thr = [&] { return bl.size() == 6 ? bl.back().est : cur; };
          for (int type = 0; type < 2; type++) {
            // type 0: T = a | b, a,b subsets of T.   type 1: T = a & b, a,b supersets of T (work with complements in M)
            const u32 M = type == 0 ? T : (FULL & ~T);
            const int t = __builtin_popcount(M);
            const bool fullOverlap = t <= 15;
            for (u32 x = (M - 1) & M; x; x = (x - 1) & M) {        // x: proper non-empty subset of M
              const u32 a = type == 0 ? x : (FULL & ~x);
              const int ca = ubcost[a];
              if (ca + 1 >= thr()) continue;
              const u32 rest = M & ~x;
              u32 c = 0;
              for (;;) {                                           // c: subset of x, c != x
                const u32 y = rest | c;
                if (y != M && y >= x) {                            // unordered pairs once
                  const u32 b = type == 0 ? y : (FULL & ~y);
                  const int cb = ubcost[b];
                  if (cb != 255) offer(ca + cb + 1, a, b, type == 0 ? OP_OR : OP_AND);
                }
                if (!fullOverlap) break;
                c = (c - x) & x;                                   // next subset of x
                if (c == 0) break;
              }
            }
          }
          if (allowNot) { int ca = ubcost[FULL & ~T]; if (ca != 255) offer(ca + 1, FULL & ~T, 0, OP_NOT); }
        }
      };
      std::vector<std::thread> th;
      for (int i = 1; i < nthreads; i++) th.emplace_back(work);
      work();
      for (auto& x : th) x.join();
      size_t improved = 0;
      for (size_t ti = 0; ti < todo.size(); ti++) {
        const size_t cl = todo[ti];
        const u32 T = classes[cl].rep;
        for (auto& d : best[ti]) {
          Gates ga, gb, all, ng; int oa, ob = 0, nout;
          if (!fnCircuit(d.a, ga, oa)) continue;
          if (d.op != OP_NOT && !fnCircuit(d.b, gb, ob)) continue;
          all = ga;
          const int sh = (int)ga.size();
          for (auto g : gb) { if (g[1] >= N) g[1] += sh; if (g[0] != OP_NOT && g[2] >= N) g[2] += sh; all.push_back(g); }
          if (ob >= N) ob += sh;
          all.push_back({d.op, oa, d.op == OP_NOT ? 0 : ob});
          simplify(all, N + (int)all.size() - 1, ng, nout);
          if (nout != N + (int)ng.size() - 1 || evalGates(ng, nout) != T) { fprintf(stderr, "internal error: bad decomposition circuit\n"); std::abort(); }
          if ((int)ng.size() < LB) { fprintf(stderr, "internal error: circuit below the proved lower bound (class %zu)\n", cl); std::abort(); }
          if (!ubc[cl].have || ng.size() < ubc[cl].gates.size()) { ubc[cl].have = true; ubc[cl].gates = ng; ubc[cl].outw = nout; improved++; }
        }
        if (ubc[cl].have) { u8 v = (u8)ubc[cl].gates.size(); for (auto& g : G) { u32 h = gapply(g, T); if (v < ubcost[h]) ubcost[h] = v; } }
      }
      // closure: one more gate on top of a known class circuit (any two of its wires) is a circuit for a new function
      size_t improved2 = 0;
      for (size_t cl = 0; cl < classes.size(); cl++) {
        Gates cg; int co;
        if (cmin[cl] != 255) { if ((int)cmin[cl] + 1 < LB || !classCircuit(cl, cg, co)) continue; }
        else { if (!ubc[cl].have) continue; cg = ubc[cl].gates; co = ubc[cl].outw; }
        std::vector<u32> vec(IN.begin(), IN.end());
        for (auto& g : cg) vec.push_back(g[0] == 3 ? FULL : g[0] == OP_NOT ? (~vec[g[1]] & FULL) : g[0] == OP_AND ? (vec[g[1]] & vec[g[2]]) : (vec[g[1]] | vec[g[2]]));
        const int Wn = (int)vec.size();
        for (int i = 0; i < Wn; i++) for (int j = allowNot ? i : i + 1; j < Wn; j++) for (int op = 0; op < 2; op++) {
          u32 T;
          int gop = op;
          if (i == j) { if (op) continue; T = ~vec[i] & FULL; gop = OP_NOT; }
          else T = op == OP_AND ? (vec[i] & vec[j]) : (vec[i] | vec[j]);
          const size_t tcl = classOf[T];
          if (cmin[tcl] != 255) continue;
          const int cur = ubc[tcl].have ? (int)ubc[tcl].gates.size() : 255;
          if ((int)cg.size() + 1 >= cur) continue;
          Gates all = cg, ng; int nout;
          all.push_back({gop, i, gop == OP_NOT ? 0 : j});
          simplify(all, N + (int)all.size() - 1, ng, nout);
          if ((int)ng.size() >= cur || nout != N + (int)ng.size() - 1) continue;
          const GE* ge = nullptr;                                 // transport to the representative of T's class
          for (auto& g : G) if (gapply(g, T) == classes[tcl].rep) { ge = &g; break; }
          for (auto& g : ng) { if (g[1] < N) g[1] = ge->ip[g[1]]; if (g[0] != OP_NOT && g[2] < N) g[2] = ge->ip[g[2]]; }
          if (evalGates(ng, nout) != classes[tcl].rep) { fprintf(stderr, "internal error: bad closure circuit\n"); std::abort(); }
          if ((int)ng.size() < LB) { fprintf(stderr, "internal error: circuit below the proved lower bound (class %zu)\n", tcl); std::abort(); }
          ubc[tcl].have = true; ubc[tcl].gates = ng; ubc[tcl].outw = nout; improved2++;
          u8 v = (u8)ng.size();
          for (auto& g : G) { u32 h = gapply(g, classes[tcl].rep); if (v < ubcost[h]) ubcost[h] = v; }
        }
      }
      improved += improved2;
      size_t have = 0, exact = 0;
      for (size_t cl = 0; cl < classes.size(); cl++) if (cmin[cl] == 255 && ubc[cl].have) { have++; exact += (int)ubc[cl].gates.size() == LB; }
      fprintf(stderr, "ub round %d: %zu improvements; of %zu unreached classes %zu have a circuit, %zu at the lower bound %d (exact)  (%.1fs)\n",
              round, improved, unresC, have, exact, LB, now() - tu);
      if (!improved) break;
    }
  }
  writeOut(true);
  fprintf(stderr, "histogram of class sizes:");
  for (int s = 0; s <= MAXG; s++) if (hist[s]) fprintf(stderr, " %d:%zu", s, hist[s]);
  if (hist[MAXG + 1]) fprintf(stderr, " unresolved(>=%d):%zu", lastComplete + 1, hist[MAXG + 1]);
  fprintf(stderr, "\n");
  if (bad) { fprintf(stderr, "%zu witness(es) FAILED verification\n", bad); return 1; }
  return 0;
}
