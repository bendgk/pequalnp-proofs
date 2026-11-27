// andtab — exact AND-complexity of ALL small bipartite graphs at once (OR gates are free).
//
// And(A) = least number of AND gates of a circuit of AND/OR gates (fan-in two, any number of ORs) that represents
// the n x m bipartite graph A.  Normal form searched here (docs/andtab.md proves it loses nothing):
//   a circuit with a AND gates is 2a+1 subsets: AND gate j = (OR of L_j) AND (OR of R_j) with L_j, R_j subsets of
//   {n+m input stars} + {AND gates 0..j-1}; the output is the OR of a subset of all of them.
// On the n*m points a wire is a set of cells (bit u*m+v); input u = row u, input n+v = column v, OR = union,
// AND = intersection.  Everything available to an AND or to the output is the UNION-CLOSURE of the generators
// (rows, columns, AND outputs so far).
//
// Method: level a = all cell sets with And <= a.  Level 0 = unions of rows and columns.  For level a the program
// enumerates every sequence of a-1 new generators g_1..g_{a-1} (g_j = X & Y with X, Y in the closure C_{j-1}, g_j
// not in C_{j-1}), reduced by (1) symmetry (row perms x column perms x transpose; only one member of each orbit
// under the stabiliser of the prefix), (2) dominance (g is dropped if another candidate g' has g in closure(C+g')),
// (3) order of independent generators at depth 2, and then marks every T = X & Y with X, Y in C_{a-1}
// (lemma: T is reachable with one more AND from C  iff  T is the intersection of two members of C).
// Marks are per symmetry class.  A class not reached by the last complete level gets the row-type/column-type
// circuit as an upper bound.
//
//   andtab --n N [--m M] [--amax A] [-j T] [--out F.jsonl] [--costs F.bin] [--enc] [--nosym] [--nodom] [--noorder] [-q]
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

using u8 = uint8_t;
using u16 = uint16_t;
using u32 = uint32_t;
using u64 = uint64_t;

static const int MAXA = 6;        // max AND gates in a witness
static const int MAXP = 25;

static int gn = 0, gm = 0, P = 0, NIN = 0;
static u32 FULL = 0;
static bool useSym = true, useDom = true, useOrder = true, quiet = false, encCheck = false;
static std::vector<u32> IN;                       // input generators (rows then columns) as cell masks

struct GE { u8 pp[MAXP]; u8 ip[16]; };            // image of every point; image of every input index
static std::vector<GE> G;
static inline u32 gapply(const GE& g, u32 f) {
  u32 r = 0;
  while (f) { int p = __builtin_ctz(f); f &= f - 1; r |= 1u << g.pp[p]; }
  return r;
}
static inline u32 gmask(const GE& g, u32 mask) {  // act on a mask of generator indices (inputs permuted, gates fixed)
  u32 r = mask >> NIN << NIN;
  for (int i = 0; i < NIN; i++) if ((mask >> i) & 1) r |= 1u << g.ip[i];
  return r;
}

struct Wit { int a = -1; u32 L[MAXA] = {0}, R[MAXA] = {0}; u32 out = 0; };
static u32 evalWit(const Wit& w) {
  u32 val[16 + MAXA];
  for (int i = 0; i < NIN; i++) val[i] = IN[i];
  for (int k = 0; k < w.a; k++) {
    u32 x = 0, y = 0;
    for (int i = 0; i < NIN + k; i++) { if ((w.L[k] >> i) & 1) x |= val[i]; if ((w.R[k] >> i) & 1) y |= val[i]; }
    val[NIN + k] = x & y;
  }
  u32 o = 0;
  for (int i = 0; i < NIN + w.a; i++) if ((w.out >> i) & 1) o |= val[i];
  return o;
}

struct ClassInfo { u32 rep; u32 orbit; };
static std::vector<ClassInfo> classes;
static std::vector<u16> classOf;
static std::vector<u8> level;                     // per class: And, 255 = not reached
static std::vector<Wit> wit;                      // per class, for the representative
static std::unique_ptr<std::atomic<u64>[]> unres; // bit T set while T's class is not reached
static std::atomic<long> remaining{0};
static std::mutex markMu;
static std::chrono::steady_clock::time_point T0;
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count(); }
static double tlimit = 0;                         // --tlimit SEC: stop the level in progress (it is then NOT complete)
static std::atomic<bool> stopFlag{false};
static std::atomic<u64> gPrefixes{0}, gPairs{0};
static std::atomic<double> lastReport{0};

static inline bool ubit(u32 t) { return (unres[t >> 6].load(std::memory_order_relaxed) >> (t & 63)) & 1; }

// T (labelled) is computed by witness w.  Record it for T's class (transported to the representative).
static void markClass(u32 T, const Wit& w) {
  std::lock_guard<std::mutex> lk(markMu);
  if (!ubit(T)) return;
  int c = classOf[T];
  u32 rep = classes[c].rep;
  const GE* sg = nullptr;
  for (const GE& g : G) if (gapply(g, T) == rep) { sg = &g; break; }
  if (!sg) { fprintf(stderr, "internal error: no group element to the representative\n"); exit(2); }
  Wit t; t.a = w.a;
  for (int k = 0; k < w.a; k++) { t.L[k] = gmask(*sg, w.L[k]); t.R[k] = gmask(*sg, w.R[k]); }
  t.out = gmask(*sg, w.out);
  if (evalWit(w) != T || evalWit(t) != rep) { fprintf(stderr, "internal error: witness does not evaluate to its target\n"); exit(2); }
  wit[c] = t; level[c] = (u8)w.a;
  for (const GE& g : G) { u32 x = gapply(g, rep); unres[x >> 6].fetch_and(~(u64(1) << (x & 63)), std::memory_order_relaxed); }
  remaining.fetch_sub(1);
}

// ------------------------------------------------------------------ search
struct Cand { u32 t, i, j; };
struct Ctx {
  std::vector<u32> cs[MAXA + 1], cm[MAXA + 1];     // closure at each depth: cell sets and generator-index masks
  size_t oldn[MAXA + 1] = {0};                     // cs[d][0..oldn[d]) = closure of depth d-1
  std::vector<u64> inC;                            // membership bitmap of the current closure (nested, with undo)
  std::vector<u64> isCand[MAXA + 1];
  std::vector<Cand> cands[MAXA + 1];
  std::vector<u32> keep[MAXA + 1];
  std::vector<int> H[MAXA + 1];                    // indices into G: stabiliser of the prefix
  u32 g[MAXA] = {0}, gL[MAXA] = {0}, gR[MAXA] = {0};
  u64 nodes = 0, pairs = 0, leaves = 0, candTotal = 0, candKept = 0;
  void init() {
    size_t W = (size_t(1) << P) / 64 + 1;
    inC.assign(W, 0);
    for (auto& b : isCand) b.assign(W, 0);
  }
};
static inline bool bget(const std::vector<u64>& b, u32 t) { return (b[t >> 6] >> (t & 63)) & 1; }
static inline void bset(std::vector<u64>& b, u32 t) { b[t >> 6] |= u64(1) << (t & 63); }
static inline void bclr(std::vector<u64>& b, u32 t) { b[t >> 6] &= ~(u64(1) << (t & 63)); }

static std::vector<u32> L0s, L0m;                  // level-0 closure
static std::vector<u64> rootCand;                  // candidates at the root (for the order rule)

static void lastStep(Ctx& c, int d, int a) {
  const std::vector<u32>& S = c.cs[d];
  const u32* s = S.data(); size_t N = S.size();
  c.leaves++;
  {
    u64 np = gPrefixes.fetch_add(1) + 1;
    double t = now();
    if (tlimit > 0 && t > tlimit) stopFlag.store(true);
    double lr = lastReport.load();
    if (!quiet && t - lr > 10 && lastReport.compare_exchange_strong(lr, t))
      fprintf(stderr, "[%.1fs] level %d: %llu prefixes, %.3g pair tests, %ld classes left\n", t, a, (unsigned long long)np, (double)gPairs.load(), remaining.load());
  }
  u64 pairs0 = c.pairs;
  for (size_t j = c.oldn[d]; j < N; j++) {         // at least one operand contains the newest generator
    u32 y = s[j];
    for (size_t i = 0; i < j; i++) {
      u32 t = s[i] & y;
      if (ubit(t)) {
        Wit w; w.a = a;
        for (int k = 0; k < d; k++) { w.L[k] = c.gL[k]; w.R[k] = c.gR[k]; }
        w.L[a - 1] = c.cm[d][i]; w.R[a - 1] = c.cm[d][j]; w.out = 1u << (NIN + a - 1);
        markClass(t, w);
      }
    }
    c.pairs += j;
  }
  gPairs.fetch_add(c.pairs - pairs0);
}

// candidates of the node at depth d (closure c.cs[d]) after the reductions; result in c.keep[d] (indices into cands)
static void genCands(Ctx& c, int d) {
  const std::vector<u32>& S = c.cs[d];
  const u32* s = S.data(); size_t N = S.size();
  auto& cd = c.cands[d]; cd.clear();
  auto& ic = c.isCand[d];
  for (size_t j = 1; j < N; j++) {
    u32 y = s[j];
    for (size_t i = 0; i < j; i++) {
      u32 t = s[i] & y;
      if (!bget(c.inC, t) && !bget(ic, t)) { bset(ic, t); cd.push_back({t, (u32)i, (u32)j}); }
    }
  }
  c.candTotal += cd.size();
  auto& kp = c.keep[d]; kp.clear();
  for (size_t x = 0; x < cd.size(); x++) {
    u32 t = cd[x].t;
    if (useDom) {
      // dominance: g is dropped when another candidate g' satisfies  D_g <= g' < g  (then g = g' | U_g is in
      // closure(C + g')), where U_g = union of the generators inside g and D_g = g minus U_g.
      u32 U = 0;
      for (int i = 0; i < NIN; i++) if ((IN[i] & ~t) == 0) U |= IN[i];
      for (int k = 0; k < d; k++) if ((c.g[k] & ~t) == 0) U |= c.g[k];
      if (U && __builtin_popcount(U) <= 14) {
        u32 D = t & ~U; bool dom = false;
        u32 sub = U;
        do {                                         // all proper submasks of U (including 0)
          sub = (sub - 1) & U;
          if (bget(ic, D | sub)) { dom = true; break; }
        } while (sub);
        if (dom) continue;
      }
    }
    if (useOrder && d == 1 && bget(rootCand, t) && classes[classOf[t]].rep < c.g[0]) continue;
    if (useSym) {
      bool canon = true;
      for (int h : c.H[d]) if (gapply(G[h], t) < t) { canon = false; break; }
      if (!canon) continue;
    }
    kp.push_back((u32)x);
  }
  c.candKept += kp.size();
}
static void clearCands(Ctx& c, int d) { for (const Cand& x : c.cands[d]) bclr(c.isCand[d], x.t); }

static void pushGen(Ctx& c, int d, const Cand& x) {  // builds the closure of depth d+1
  c.g[d] = x.t; c.gL[d] = c.cm[d][x.i]; c.gR[d] = c.cm[d][x.j];
  auto& S = c.cs[d + 1]; auto& M = c.cm[d + 1];
  S = c.cs[d]; M = c.cm[d];
  size_t n0 = S.size(); c.oldn[d + 1] = n0;
  u32 gbit = 1u << (NIN + d);
  for (size_t i = 0; i < n0; i++) {
    u32 y = S[i] | x.t;
    if (!bget(c.inC, y)) { bset(c.inC, y); S.push_back(y); M.push_back(M[i] | gbit); }
  }
  if (useSym) {
    auto& Hn = c.H[d + 1]; Hn.clear();
    for (int h : c.H[d]) if (gapply(G[h], x.t) == x.t) Hn.push_back(h);
  }
}
static void popGen(Ctx& c, int d) {
  auto& S = c.cs[d + 1];
  for (size_t i = c.oldn[d + 1]; i < S.size(); i++) bclr(c.inC, S[i]);
}

static void dfs(Ctx& c, int d, int a) {
  c.nodes++;
  if (remaining.load(std::memory_order_relaxed) == 0 || stopFlag.load(std::memory_order_relaxed)) return;
  if (d == a - 1) { lastStep(c, d, a); return; }
  genCands(c, d);
  for (u32 xi : c.keep[d]) {
    Cand x = c.cands[d][xi];
    pushGen(c, d, x);
    dfs(c, d + 1, a);
    popGen(c, d);
  }
  clearCands(c, d);
}

static void initCtx(Ctx& c) {
  c.init();
  c.cs[0] = L0s; c.cm[0] = L0m; c.oldn[0] = 0;
  for (u32 s : L0s) bset(c.inC, s);
  c.H[0].resize(G.size());
  for (size_t i = 0; i < G.size(); i++) c.H[0][i] = (int)i;
}

// ------------------------------------------------------------------ setup
static void buildGroup() {
  std::vector<int> pr(gn), pc(gm);
  for (int i = 0; i < gn; i++) pr[i] = i;
  do {
    for (int i = 0; i < gm; i++) pc[i] = i;
    do {
      for (int t = 0; t < (gn == gm ? 2 : 1); t++) {
        GE g;
        for (int u = 0; u < gn; u++) for (int v = 0; v < gm; v++) {
          int p = u * gm + v;
          g.pp[p] = t == 0 ? (u8)(pr[u] * gm + pc[v]) : (u8)(pr[v] * gm + pc[u]);   // t=1: transpose first
        }
        for (int u = 0; u < gn; u++) g.ip[u] = t == 0 ? (u8)pr[u] : (u8)(gn + pc[u]);
        for (int v = 0; v < gm; v++) g.ip[gn + v] = t == 0 ? (u8)(gn + pc[v]) : (u8)pr[v];
        G.push_back(g);
      }
    } while (std::next_permutation(pc.begin(), pc.end()));
  } while (std::next_permutation(pr.begin(), pr.end()));
}

static void closureOf(const std::vector<u32>& gens, std::vector<u32>& S, std::vector<u32>& M) {
  std::vector<u64> seen((size_t(1) << P) / 64 + 1, 0);
  S.assign(1, 0); M.assign(1, 0); bset(seen, 0);
  for (size_t gi = 0; gi < gens.size(); gi++) {
    size_t n0 = S.size();
    for (size_t i = 0; i < n0; i++) {
      u32 y = S[i] | gens[gi];
      if (!bget(seen, y)) { bset(seen, y); S.push_back(y); M.push_back(M[i] | (gi < 32 ? 1u << gi : 0)); }
    }
  }
}

// row-type / column-type circuit for the representative of class c (upper bound)
static Wit typeWit(u32 rep) {
  Wit best;
  for (int side = 0; side < 2; side++) {
    int na = side == 0 ? gn : gm, nb = side == 0 ? gm : gn;
    std::vector<u32> type(na);
    for (int x = 0; x < na; x++) {
      u32 t = 0;
      for (int y = 0; y < nb; y++) { int p = side == 0 ? x * gm + y : y * gm + x; if ((rep >> p) & 1) t |= 1u << y; }
      type[x] = t;
    }
    u32 fullb = (nb == 32) ? 0xFFFFFFFFu : ((1u << nb) - 1);
    Wit w; w.a = 0; w.out = 0;
    std::vector<u32> seen;
    bool ok = true;
    for (int x = 0; x < na; x++) {
      int ia = side == 0 ? x : gn + x;
      if (type[x] == fullb) { w.out |= 1u << ia; continue; }
      if (type[x] == 0) continue;
      if (std::find(seen.begin(), seen.end(), type[x]) != seen.end()) continue;
      seen.push_back(type[x]);
      if (w.a >= MAXA) { ok = false; break; }
      u32 Lm = 0, Rm = 0;
      for (int z = 0; z < na; z++) if (type[z] == type[x]) Lm |= 1u << (side == 0 ? z : gn + z);
      for (int y = 0; y < nb; y++) if ((type[x] >> y) & 1) Rm |= 1u << (side == 0 ? gn + y : y);
      w.L[w.a] = Lm; w.R[w.a] = Rm; w.out |= 1u << (NIN + w.a); w.a++;
    }
    if (ok && evalWit(w) == rep && (best.a < 0 || w.a < best.a)) best = w;
  }
  return best;
}

static void printMask(FILE* f, u32 m) {
  fputc('[', f); bool first = true;
  for (int i = 0; i < 32; i++) if ((m >> i) & 1) { fprintf(f, first ? "%d" : ",%d", i); first = false; }
  fputc(']', f);
}

int main(int argc, char** argv) {
  int amax = 4, nthreads = getenv("PNP_THREADS") ? atoi(getenv("PNP_THREADS")) : 1;
  std::string outPath, costPath;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto nx = [&]() { if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", a.c_str()); exit(1); } return std::string(argv[++i]); };
    if (a == "--n") gn = atoi(nx().c_str());
    else if (a == "--m") gm = atoi(nx().c_str());
    else if (a == "--amax") amax = atoi(nx().c_str());
    else if (a == "-j") nthreads = atoi(nx().c_str());
    else if (a == "--out") outPath = nx();
    else if (a == "--costs") costPath = nx();
    else if (a == "--enc") encCheck = true;
    else if (a == "--tlimit") tlimit = atof(nx().c_str());
    else if (a == "--nosym") useSym = false;
    else if (a == "--nodom") useDom = false;
    else if (a == "--noorder") useOrder = false;
    else if (a == "-q") quiet = true;
    else { fprintf(stderr, "usage: andtab --n N [--m M] [--amax A] [-j T] [--out F.jsonl] [--costs F.bin] [--enc] [--nosym] [--nodom] [--noorder] [-q]\n"); return 1; }
  }
  if (gm == 0) gm = gn;
  if (gn < 1 || gm < 1 || gn * gm > MAXP || gn + gm > 16) { fprintf(stderr, "need 1 <= n*m <= 25\n"); return 1; }
  if (nthreads < 1) nthreads = 1;
  if (amax > MAXA) amax = MAXA;
  P = gn * gm; NIN = gn + gm; FULL = (P == 32) ? 0xFFFFFFFFu : ((1u << P) - 1);
  T0 = std::chrono::steady_clock::now();
  for (int u = 0; u < gn; u++) { u32 r = 0; for (int v = 0; v < gm; v++) r |= 1u << (u * gm + v); IN.push_back(r); }
  for (int v = 0; v < gm; v++) { u32 r = 0; for (int u = 0; u < gn; u++) r |= 1u << (u * gm + v); IN.push_back(r); }
  buildGroup();
  // classes (representative = least value; ids in increasing order of the representative, as in tables/star_*.json)
  size_t NF = size_t(1) << P;
  classOf.assign(NF, 0xFFFF);
  for (size_t f = 0; f < NF; f++) {
    if (classOf[f] != 0xFFFF) continue;
    u16 id = (u16)classes.size(); u32 orbit = 0;
    for (const GE& g : G) { u32 x = gapply(g, (u32)f); if (classOf[x] == 0xFFFF) { classOf[x] = id; orbit++; } }
    classes.push_back({(u32)f, orbit});
  }
  int NC = (int)classes.size();
  level.assign(NC, 255); wit.assign(NC, Wit());
  unres.reset(new std::atomic<u64>[NF / 64 + 1]);
  for (size_t i = 0; i < NF / 64 + 1; i++) unres[i].store(~u64(0));
  remaining = NC;
  if (!quiet) fprintf(stderr, "[%.2fs] %dx%d: group %zu, %d classes, %zu labelled graphs, -j %d\n", now(), gn, gm, G.size(), NC, NF, nthreads);
  // level 0
  closureOf(IN, L0s, L0m);
  if (encCheck) {
    // the free "encoder" wires {u : bit_i(u) = b} and {v : bit_i(v) = b} are unions of rows / columns: adding them
    // as generators must not change the level-0 closure (and nothing else in the search depends on the inputs).
    std::vector<u32> gens = IN;
    for (int side = 0; side < 2; side++) {
      int sz = side == 0 ? gn : gm;
      for (int b = 0; (1 << b) < sz; b++) for (int val = 0; val < 2; val++) {
        u32 s = 0;
        for (int x = 0; x < sz; x++) if (((x >> b) & 1) == val) s |= IN[side == 0 ? x : gn + x];
        gens.push_back(s);
      }
    }
    std::vector<u32> S2, M2; closureOf(gens, S2, M2);
    std::vector<u32> A = L0s, B = S2; std::sort(A.begin(), A.end()); std::sort(B.begin(), B.end());
    fprintf(stderr, "[enc] generators %zu -> %zu with the bit-set wires; level-0 closure %zu vs %zu sets: %s\n",
            IN.size(), gens.size(), A.size(), B.size(), A == B ? "IDENTICAL" : "DIFFERENT");
    if (A != B) return 3;
  }
  for (size_t i = 0; i < L0s.size(); i++) {
    if (ubit(L0s[i])) { Wit w; w.a = 0; w.out = L0m[i]; markClass(L0s[i], w); }
  }
  int lastComplete = 0;
  if (!quiet) fprintf(stderr, "[%.2fs] level 0: closure %zu sets, %d classes reached, %ld left\n", now(), L0s.size(), NC - (int)remaining.load(), remaining.load());
  struct LevelStat { int a; double sec; u64 nodes, leaves, pairs, candTotal, candKept; int reached; };
  std::vector<LevelStat> stats;
  for (int a = 1; a <= amax && remaining.load() > 0; a++) {
    double t0 = now(); long before = remaining.load();
    u64 nodes = 0, pairs = 0, leaves = 0, candTotal = 0, candKept = 0;
    if (a == 1 || nthreads == 1) {
      Ctx c; initCtx(c);
      if (a >= 2) {   // remember the root candidates for the order rule
        genCands(c, 0);
        rootCand.assign(NF / 64 + 1, 0);
        for (const Cand& x : c.cands[0]) bset(rootCand, x.t);
        clearCands(c, 0);
        c.candTotal = c.candKept = 0;
      }
      dfs(c, 0, a);
      nodes = c.nodes; pairs = c.pairs; leaves = c.leaves; candTotal = c.candTotal; candKept = c.candKept;
    } else {
      Ctx root; initCtx(root);
      genCands(root, 0);
      rootCand.assign(NF / 64 + 1, 0);
      for (const Cand& x : root.cands[0]) bset(rootCand, x.t);
      std::vector<Cand> tasks;
      for (u32 xi : root.keep[0]) tasks.push_back(root.cands[0][xi]);
      candTotal = root.candTotal; candKept = root.candKept; nodes = 1;
      std::atomic<size_t> next{0};
      std::mutex smu;
      std::vector<std::thread> th;
      for (int t = 0; t < nthreads; t++) th.emplace_back([&]() {
        Ctx c; initCtx(c);
        // the root's candidate list must be present for pushGen (it reads cm[0][i], cm[0][j] only)
        for (;;) {
          size_t k = next.fetch_add(1);
          if (k >= tasks.size()) break;
          pushGen(c, 0, tasks[k]);
          dfs(c, 1, a);
          popGen(c, 0);
        }
        std::lock_guard<std::mutex> lk(smu);
        nodes += c.nodes; pairs += c.pairs; leaves += c.leaves; candTotal += c.candTotal; candKept += c.candKept;
      });
      for (auto& t : th) t.join();
    }
    bool complete = !stopFlag.load();
    if (complete) lastComplete = a;
    double sec = now() - t0;
    stats.push_back({a, sec, nodes, leaves, pairs, candTotal, candKept, (int)(before - remaining.load())});
    if (!quiet) fprintf(stderr, "[%.2fs] level %d: %d classes reached, %ld left; %.2fs, %llu nodes (%llu last-step prefixes), %llu candidates -> %llu kept, %llu pair tests (%.3g/s)\n",
                        now(), a, (int)(before - remaining.load()), remaining.load(), sec, (unsigned long long)nodes, (unsigned long long)leaves,
                        (unsigned long long)candTotal, (unsigned long long)candKept, (unsigned long long)pairs, sec > 0 ? pairs / sec : 0.0);
    if (!complete) { fprintf(stderr, "[%.2fs] level %d INTERRUPTED by --tlimit: its marks are real circuits, but the level is not complete\n", now(), a); break; }
  }
  // classes not reached: row-type / column-type circuit as an upper bound
  std::vector<u8> exact(NC, 1); std::vector<int> lower(NC, 0);
  for (int c = 0; c < NC; c++) {
    if (level[c] != 255) { lower[c] = level[c]; continue; }
    lower[c] = lastComplete + 1;
    Wit w = typeWit(classes[c].rep);
    if (w.a >= 0) { wit[c] = w; level[c] = (u8)w.a; exact[c] = (w.a == lower[c]); }
    else exact[c] = 0;
    if (w.a >= 0 && w.a < lower[c]) { fprintf(stderr, "internal error: type circuit below the proved lower bound\n"); return 2; }
  }
  // output
  FILE* out = stdout;
  if (!outPath.empty()) { out = fopen(outPath.c_str(), "w"); if (!out) { perror("open --out"); return 1; } }
  fprintf(out, "{\"tool\":\"andtab\",\"n\":%d,\"m\":%d,\"group\":%zu,\"classes\":%d,\"transpose\":%s,\"last_complete_level\":%d,\"sym\":%s,\"dom\":%s,\"order\":%s,\"threads\":%d,\"seconds\":%.3f,\"levels\":[",
          gn, gm, G.size(), NC, gn == gm ? "true" : "false", lastComplete, useSym ? "true" : "false", useDom ? "true" : "false", useOrder ? "true" : "false", nthreads, now());
  for (size_t i = 0; i < stats.size(); i++)
    fprintf(out, "%s{\"a\":%d,\"seconds\":%.3f,\"nodes\":%llu,\"prefixes\":%llu,\"pair_tests\":%llu,\"candidates\":%llu,\"kept\":%llu,\"classes_reached\":%d}", i ? "," : "",
            stats[i].a, stats[i].sec, (unsigned long long)stats[i].nodes, (unsigned long long)stats[i].leaves, (unsigned long long)stats[i].pairs,
            (unsigned long long)stats[i].candTotal, (unsigned long long)stats[i].candKept, stats[i].reached);
  fprintf(out, "]}\n");
  for (int c = 0; c < NC; c++) {
    u32 rep = classes[c].rep;
    fprintf(out, "{\"cls\":%d,\"f\":%u,\"rows\":[", c, rep);
    for (int u = 0; u < gn; u++) fprintf(out, u ? ",%u" : "%u", (rep >> (u * gm)) & ((1u << gm) - 1));
    fprintf(out, "],\"orbit\":%u,\"ccls\":%d,", classes[c].orbit, classOf[FULL ^ rep]);
    if (level[c] == 255) fprintf(out, "\"and\":null,\"exact\":false,\"lower\":%d}\n", lower[c]);
    else {
      const Wit& w = wit[c];
      if (evalWit(w) != rep) { fprintf(stderr, "internal error: stored witness wrong\n"); return 2; }
      fprintf(out, "\"and\":%d,\"exact\":%s,\"lower\":%d,\"L\":[", level[c], exact[c] ? "true" : "false", lower[c]);
      for (int k = 0; k < w.a; k++) { if (k) fputc(',', out); printMask(out, w.L[k]); }
      fprintf(out, "],\"R\":[");
      for (int k = 0; k < w.a; k++) { if (k) fputc(',', out); printMask(out, w.R[k]); }
      fprintf(out, "],\"out\":"); printMask(out, w.out);
      fprintf(out, "}\n");
    }
  }
  if (out != stdout) fclose(out);
  if (!costPath.empty()) {       // one byte per labelled graph: And if exact, 200 + lower bound otherwise
    FILE* f = fopen(costPath.c_str(), "wb"); if (!f) { perror("open --costs"); return 1; }
    std::vector<u8> buf(NF);
    for (size_t x = 0; x < NF; x++) { int c = classOf[x]; buf[x] = exact[c] ? level[c] : (u8)(200 + lower[c]); }
    fwrite(buf.data(), 1, NF, f); fclose(f);
  }
  // summary on stderr
  if (!quiet) {
    std::vector<long> hc(16, 0); std::vector<unsigned long long> hl(16, 0); int notExact = 0;
    for (int c = 0; c < NC; c++) { if (exact[c]) { hc[level[c]]++; hl[level[c]] += classes[c].orbit; } else notExact++; }
    fprintf(stderr, "[%.2fs] And histogram (classes):", now());
    for (int a = 0; a < 16; a++) if (hc[a]) fprintf(stderr, " %d:%ld", a, hc[a]);
    fprintf(stderr, "  labelled:");
    for (int a = 0; a < 16; a++) if (hc[a]) fprintf(stderr, " %d:%llu", a, hl[a]);
    fprintf(stderr, "  not exact: %d  (last complete level %d)\n", notExact, lastComplete);
  }
  return 0;
}
