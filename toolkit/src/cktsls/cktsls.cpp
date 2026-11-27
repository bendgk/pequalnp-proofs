// cktsls — native multi-threaded STOCHASTIC search for small fan-in-two circuits (upper-bound witnesses).
//
//   cktsls SPEC --basis ao|aon -s GATES [-j T] [--time S] [--seed X] [-o OUT.ckt] [--init IN.ckt] ...
//
// HEURISTIC: it finds witnesses, it never proves non-existence. See docs/cktsls.md.
//
// Search = parallel tempering over "gate heat-bath" moves.
//   State: s gates (and/or, in aon also not), an arbitrary DAG (a topological order is maintained).
//   Cost : sum over the K outputs of min over ALL wires of the Hamming distance to the target on cared points
//          (outputs are re-assigned to their best wire after every move).
//   Move : pick a gate g. Simulate its fanout cone twice (g = all-0 and g = all-1). That gives, for every
//          output in the cone, a need-mask pair (T, C): the output is right at point p iff g(p) == T(p)
//          wherever C(p) = 1, and does not depend on g(p) elsewhere. The exact cost of EVERY replacement
//          (op, a, b) of g, over all pairs of wires outside the cone, is then base + popcount((x ^ T) & C):
//          a few word operations per candidate instead of a cone simulation. The new gate is drawn from the
//          Boltzmann distribution exp(-cost/T) over all candidates (heat bath; rejection free).
//   Outputs outside the cone contribute min(current distance, distance of the candidate column) ("takeover"),
//   so dead gates are steered towards becoming better outputs instead of drifting.
//   Each island (one per thread) runs R replicas on a geometric temperature ladder with replica exchange.
//   Big specs: evaluation on a sample of points, full verification when the sample cost is 0, and the
//   counterexamples are added to the island's sample (CEGIS).
#include "../../include/ckt.hpp"
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <thread>

using namespace pnp;

namespace {

struct Rng {  // xoroshiro128+
  u64 a, b;
  explicit Rng(u64 seed = 1) { u64 z = seed; a = splitmix(z); b = splitmix(z); if (!(a | b)) a = 1; }
  static u64 splitmix(u64& x) {
    u64 z = (x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
  inline u64 next() {
    u64 s0 = a, s1 = b, r = s0 + s1;
    s1 ^= s0;
    a = ((s0 << 55) | (s0 >> 9)) ^ s1 ^ (s1 << 14);
    b = (s1 << 36) | (s1 >> 28);
    return r;
  }
  inline uint32_t below(uint32_t n) { return (uint32_t)(((next() >> 32) * (u64)n) >> 32); }
  inline double uni() { return (double)(next() >> 11) * (1.0 / 9007199254740992.0); }
};

inline int pc(u64 x) { return __builtin_popcountll(x); }
const uint32_t BIG = 0x3fffffff;

struct Opts {
  std::string spec, basis = "ao", out, init, bestfile;
  int s = -1, T = 1, R = 8, islands = 0, sweep = 0, takeover = -1;
  double tlim = 60, tmin = -1, tmax = -1, hotfrac = 0.4;
  u64 seed = 1;
  long sample = -1, rounds = -1;
  bool quiet = false, selfcheck = false, noprune = false, ladder = false, noadapt = false;
  int migrate = 0;
  std::string sym; int fixed = -1; bool islandsGiven = false, symSlow = false;
  std::string shape;
};

struct SymCfg;
struct ShapeCfg { int nS = 0, nP = 0, nT = 0; bool dual = false; };
// The points the search evaluates on: all cared points of the spec, or a sample of them.
struct View {
  const SymCfg* sym = nullptr;
  const ShapeCfg* shape = nullptr;
  int N = 0, K = 1;
  size_t W = 0, npts = 0;
  std::vector<u64> in, tgt, care;  // N*W, K*W, K*W
  bool sampled = false;
  std::vector<uint32_t> pts;       // sampled: spec point of every slot
  size_t cexBase = 0, cexHead = 0; // slots [cexBase, npts) are a FIFO of counterexample points

  void all(const Spec& sp) {
    N = sp.N; K = sp.K; W = sp.W; npts = sp.P; sampled = false;
    in.assign((size_t)N * W, 0); tgt.assign((size_t)K * W, 0); care.assign((size_t)K * W, 0);
    for (int i = 0; i < N; i++) std::copy(sp.in[i].begin(), sp.in[i].end(), in.begin() + (size_t)i * W);
    for (int k = 0; k < K; k++) {
      std::copy(sp.tgt[k].begin(), sp.tgt[k].end(), tgt.begin() + (size_t)k * W);
      std::copy(sp.care[k].begin(), sp.care[k].end(), care.begin() + (size_t)k * W);
    }
  }
  void setSlot(const Spec& sp, size_t slot, size_t p) {
    pts[slot] = (uint32_t)p;
    u64 bit = u64(1) << (slot % 64); size_t w = slot / 64;
    for (int i = 0; i < N; i++) { u64& x = in[(size_t)i * W + w]; x = getbit(sp.in[i], p) ? (x | bit) : (x & ~bit); }
    for (int k = 0; k < K; k++) {
      u64& t = tgt[(size_t)k * W + w]; t = getbit(sp.tgt[k], p) ? (t | bit) : (t & ~bit);
      u64& c = care[(size_t)k * W + w]; c = getbit(sp.care[k], p) ? (c | bit) : (c & ~bit);
    }
  }
  void sample(const Spec& sp, size_t S, Rng& rng) {
    N = sp.N; K = sp.K; W = (S + 63) / 64; npts = W * 64; sampled = true;
    in.assign((size_t)N * W, 0); tgt.assign((size_t)K * W, 0); care.assign((size_t)K * W, 0);
    pts.assign(npts, 0);
    for (size_t i = 0; i < npts; i++) setSlot(sp, i, (size_t)(rng.next() % sp.P));
    cexBase = npts / 2; cexHead = 0;
  }
  void addCex(const Spec& sp, size_t p) {
    size_t cap = npts - cexBase;
    setSlot(sp, cexBase + (cexHead % cap), p);
    cexHead++;
  }
};

struct GL {  // plain gate list in topological (index) order; wires N+j
  std::vector<uint8_t> op;
  std::vector<uint16_t> fa, fb;
};

// Bring an arbitrary input circuit to exactly s gates of the search model (and/or with two earlier wires, not with one).
GL adaptInit(const Circuit& c, int N, int s, bool aon, Rng& rng) {
  GL g;
  std::vector<int> alias(N + c.gates.size());
  for (int i = 0; i < N; i++) alias[i] = i;
  for (size_t j = 0; j < c.gates.size(); j++) {
    const Gate& q = c.gates[j];
    int cur = N + (int)j, me = N + (int)g.op.size();
    auto rd = [&](int w) { if (w < 0 || w >= cur) die("--init: gate reads a wire that is not earlier"); return alias[w]; };
    if (q.op == NOT) {
      if (!aon) die("--init: NOT gate but basis is ao");
      if (q.nin < 1) die("--init: constant gates are not supported");
      int a = rd(q.a);
      g.op.push_back(NOT); g.fa.push_back(a); g.fb.push_back(a); alias[cur] = me;
    } else if (q.nin == 2) {
      int a = rd(q.a), b = rd(q.b);
      g.op.push_back(q.op); g.fa.push_back(a); g.fb.push_back(b); alias[cur] = me;
    } else if (q.nin == 1) {
      alias[cur] = rd(q.a);  // copy gate: drop it
    } else die("--init: constant gates are not supported");
  }
  while ((int)g.op.size() > s) {  // delete a random gate, readers take one of its fanins instead
    int n = (int)g.op.size(), d = rng.below(n), wd = N + d;
    int t = (rng.next() & 1) ? g.fa[d] : g.fb[d];
    for (int h = d + 1; h < n; h++) {
      if (g.fa[h] == wd) g.fa[h] = t;
      if (g.fb[h] == wd) g.fb[h] = t;
      if (g.fa[h] > wd) g.fa[h]--;
      if (g.fb[h] > wd) g.fb[h]--;
    }
    g.op.erase(g.op.begin() + d); g.fa.erase(g.fa.begin() + d); g.fb.erase(g.fb.begin() + d);
  }
  while ((int)g.op.size() < s) {  // pad with random gates
    int lim = N + (int)g.op.size();
    int a = rng.below(lim), b = rng.below(lim - 1); if (b >= a) b++;
    if (aon && rng.below(5) == 0) { g.op.push_back(NOT); g.fa.push_back(a); g.fb.push_back(a); }
    else { g.op.push_back(rng.next() & 1 ? AND : OR); g.fa.push_back(a); g.fb.push_back(b); }
  }
  return g;
}

template <size_t WF>
struct Replica {
  const View* vw = nullptr;
  int N = 0, K = 1, s = 0, nw = 0, takeover = 2;
  bool aon = false;
  size_t Wd = 0;
  inline size_t W() const { return WF ? WF : Wd; }

  std::vector<uint8_t> op;
  std::vector<uint16_t> fa, fb;     // fanin wires (not: fb == fa)
  std::vector<uint16_t> order, pos; // topological order of the gates
  std::vector<u64> val, V0, V1;     // nw*W
  std::vector<uint32_t> mark;
  uint32_t stamp = 0;
  std::vector<uint16_t> cone, av, tmpo;
  std::vector<uint32_t> dist;       // K*nw
  std::vector<uint16_t> outw;       // K
  uint32_t cost = 0;
  std::vector<u64> actT, actC, avm, xbuf;
  std::vector<uint32_t> ccost, selIdx, pcur;
  std::vector<double> selCum;
  std::vector<int> pas;
  std::vector<uint8_t> kind;
  Rng rng;
  u64 ncand = 0, nsteps = 0, nchanged = 0;
  int nmoves() const { return s; }
  const ShapeCfg* shp = nullptr;    // --shape: typed layers
  std::vector<uint8_t> wcls;        // wire class: 0 input, 1 S (first sum layer), 2 P (products), 3 T (top sums)

  void setup(const View* v, int s_, bool aon_, int takeover_, u64 seed) {
    vw = v; N = v->N; K = v->K; s = s_; nw = N + s; aon = aon_; takeover = takeover_; Wd = v->W;
    rng = Rng(seed);
    shp = v->shape;
    if (shp) {
      wcls.assign(nw, 0);
      for (int j = 0; j < s; j++) wcls[N + j] = j < shp->nS ? 1 : j < shp->nS + shp->nP ? 2 : 3;
    }
    op.assign(s, AND); fa.assign(s, 0); fb.assign(s, 1); order.resize(s); pos.resize(s);
    mark.assign(nw, 0); stamp = 0; cone.resize(s); av.resize(nw); tmpo.resize(s);
    outw.assign(K, 0); pas.resize(K); pcur.resize(K); kind.resize(K);
    size_t nc = (size_t)nw * nw + nw;
    ccost.resize(nc); selIdx.resize(nc); selCum.resize(nc);
    resize();
  }
  void resize() {
    Wd = vw->W;
    const size_t W = this->W();
    val.assign((size_t)nw * W, 0); V0.assign((size_t)nw * W, 0); V1.assign((size_t)nw * W, 0);
    dist.assign((size_t)K * nw, 0);
    actT.assign((size_t)K * W, 0); actC.assign((size_t)K * W, 0); avm.assign((size_t)nw * W, 0); xbuf.assign(W, 0);
  }
  void randomize() {
    if (shp) {  // gate j reads two distinct earlier wires of the classes its layer allows
      std::vector<int> ok;
      for (int j = 0; j < s; j++) {
        const int cg = wcls[N + j];
        ok.clear();
        for (int w = 0; w < N + j; w++) if (cg == 3 ? wcls[w] >= 2 : wcls[w] <= 1) ok.push_back(w);
        if (ok.size() < 2) die("--shape: a layer has fewer than two wires to read");
        int a = rng.below((uint32_t)ok.size()), b = rng.below((uint32_t)ok.size() - 1); if (b >= a) b++;
        op[j] = ((cg == 2) != shp->dual) ? AND : OR; fa[j] = ok[a]; fb[j] = ok[b];
        order[j] = pos[j] = j;
      }
      resim();
      return;
    }
    for (int j = 0; j < s; j++) {
      int lim = N + j;
      int a = rng.below(lim), b = rng.below(lim - 1); if (b >= a) b++;
      if (aon && rng.below(5) == 0) { op[j] = NOT; fa[j] = fb[j] = a; }
      else { op[j] = (rng.next() & 1) ? AND : OR; fa[j] = a; fb[j] = b; }
      order[j] = pos[j] = j;
    }
    resim();
  }
  void load(const GL& g) {
    if (shp) die("--init is not supported together with --shape");
    for (int j = 0; j < s; j++) { op[j] = g.op[j]; fa[j] = g.fa[j]; fb[j] = g.fb[j]; order[j] = pos[j] = j; }
    resim();
  }
  GL snapshot() const {  // in topological order
    GL g; std::vector<int> id(nw);
    for (int i = 0; i < N; i++) id[i] = i;
    for (int i = 0; i < s; i++) id[N + order[i]] = N + i;
    for (int i = 0; i < s; i++) { int h = order[i]; g.op.push_back(op[h]); g.fa.push_back(id[fa[h]]); g.fb.push_back(id[fb[h]]); }
    return g;
  }
  inline void gateEval(int h, u64* o) const {
    const size_t W = this->W();
    const u64* a = &val[(size_t)fa[h] * W]; const u64* b = &val[(size_t)fb[h] * W];
    if (op[h] == AND) for (size_t w = 0; w < W; w++) o[w] = a[w] & b[w];
    else if (op[h] == OR) for (size_t w = 0; w < W; w++) o[w] = a[w] | b[w];
    else for (size_t w = 0; w < W; w++) o[w] = ~a[w];
  }
  inline uint32_t wdist(int k, int w) const {
    const size_t W = this->W();
    const u64* x = &val[(size_t)w * W]; const u64* t = &vw->tgt[(size_t)k * W]; const u64* c = &vw->care[(size_t)k * W];
    uint32_t d = 0;
    for (size_t i = 0; i < W; i++) d += pc((x[i] ^ t[i]) & c[i]);
    return d;
  }
  // full recomputation (after init / after the view changed)
  void resim() {
    const size_t W = this->W();
    if (val.size() != (size_t)nw * W) resize();
    std::copy(vw->in.begin(), vw->in.end(), val.begin());
    for (int i = 0; i < s; i++) { int h = order[i]; gateEval(h, &val[(size_t)(N + h) * W]); }
    cost = 0;
    for (int k = 0; k < K; k++) {
      uint32_t best = BIG; int bw = 0;
      for (int w = 0; w < nw; w++) { uint32_t d = wdist(k, w); dist[(size_t)k * nw + w] = d; if (d < best) { best = d; bw = w; } }
      outw[k] = bw; cost += best;
    }
  }
  bool selfcheck() const {
    const size_t W = this->W();
    std::vector<u64> v((size_t)nw * W);
    std::copy(vw->in.begin(), vw->in.end(), v.begin());
    std::vector<char> seen(nw, 0);
    for (int i = 0; i < N; i++) seen[i] = 1;
    for (int i = 0; i < s; i++) {
      int h = order[i];
      if (pos[h] != i || !seen[fa[h]] || !seen[fb[h]]) return false;
      const u64* a = &v[(size_t)fa[h] * W]; const u64* b = &v[(size_t)fb[h] * W]; u64* o = &v[(size_t)(N + h) * W];
      for (size_t w = 0; w < W; w++) o[w] = op[h] == AND ? (a[w] & b[w]) : op[h] == OR ? (a[w] | b[w]) : ~a[w];
      seen[N + h] = 1;
    }
    if (v != val) return false;
    uint32_t c = 0;
    for (int k = 0; k < K; k++) {
      uint32_t best = BIG;
      for (int w = 0; w < nw; w++) { uint32_t d = wdist(k, w); if (d != dist[(size_t)k * nw + w]) return false; best = std::min(best, d); }
      if (dist[(size_t)k * nw + outw[k]] != best) return false;
      c += best;
    }
    return c == cost;
  }
  Circuit toCircuit(bool prune) const {
    std::vector<char> need(nw, prune ? 0 : 1);
    if (prune) {
      for (int k = 0; k < K; k++) need[outw[k]] = 1;
      for (int i = s - 1; i >= 0; i--) { int h = order[i]; if (need[N + h]) { need[fa[h]] = 1; need[fb[h]] = 1; } }
    }
    std::vector<int> id(nw, -1);
    for (int i = 0; i < N; i++) id[i] = i;
    Circuit c; c.N = N;
    for (int i = 0; i < s; i++) {
      int h = order[i];
      if (!need[N + h]) continue;
      Gate g; g.op = (Op)op[h]; g.a = id[fa[h]];
      if (op[h] == NOT) { g.nin = 1; g.b = 0; } else { g.nin = 2; g.b = id[fb[h]]; }
      id[N + h] = N + (int)c.gates.size();
      c.gates.push_back(g);
    }
    for (int k = 0; k < K; k++) c.outs.push_back(id[outw[k]]);
    return c;
  }

  // One heat-bath update of gate g at the temperature whose weight table is wtab[0..D).
  void step(int g, const float* wtab, int D) {
    const size_t W = this->W();
    const int wg = N + g;
    const uint32_t st = ++stamp;
    nsteps++;
    mark[wg] = st;
    int nc = 0;
    for (int i = pos[g] + 1; i < s; i++) {
      int h = order[i];
      if (mark[fa[h]] == st || mark[fb[h]] == st) { mark[N + h] = st; cone[nc++] = h; }
    }
    u64* v0 = V0.data(); u64* v1 = V1.data(); u64* vv = val.data();
    for (size_t w = 0; w < W; w++) { v0[(size_t)wg * W + w] = 0; v1[(size_t)wg * W + w] = ~u64(0); }
    for (int c = 0; c < nc; c++) {
      int h = cone[c]; size_t a = fa[h], b = fb[h], o = N + h;
      const u64* a0 = (mark[a] == st ? v0 : vv) + a * W; const u64* a1 = (mark[a] == st ? v1 : vv) + a * W;
      const u64* b0 = (mark[b] == st ? v0 : vv) + b * W; const u64* b1 = (mark[b] == st ? v1 : vv) + b * W;
      u64* o0 = v0 + o * W; u64* o1 = v1 + o * W;
      if (op[h] == AND) for (size_t w = 0; w < W; w++) { o0[w] = a0[w] & b0[w]; o1[w] = a1[w] & b1[w]; }
      else if (op[h] == OR) for (size_t w = 0; w < W; w++) { o0[w] = a0[w] | b0[w]; o1[w] = a1[w] | b1[w]; }
      else for (size_t w = 0; w < W; w++) { o0[w] = ~a0[w]; o1[w] = ~a1[w]; }
    }
    // outputs: active (depend on g) -> need masks; others fixed or takeover
    const u64* tg = vw->tgt.data(); const u64* cr = vw->care.data();
    uint32_t base = 0; int nact = 0, npas = 0;
    for (int k = 0; k < K; k++) {
      size_t o = outw[k];
      kind[k] = 1;
      if (mark[o] == st) {
        u64* Tk = &actT[(size_t)nact * W]; u64* Ck = &actC[(size_t)nact * W];
        u64 any = 0; uint32_t fixed = 0;
        for (size_t w = 0; w < W; w++) {
          u64 bad0 = (v0[o * W + w] ^ tg[(size_t)k * W + w]) & cr[(size_t)k * W + w];
          u64 bad1 = (v1[o * W + w] ^ tg[(size_t)k * W + w]) & cr[(size_t)k * W + w];
          fixed += pc(bad0 & bad1); Tk[w] = bad0 & ~bad1; Ck[w] = bad0 ^ bad1; any |= Ck[w];
        }
        if (any) { base += fixed; nact++; kind[k] = 0; }
      }
    }
    const bool usePas = takeover == 2 || (takeover == 1 && nact == 0);
    for (int k = 0; k < K; k++) if (kind[k]) {
      uint32_t cur = dist[(size_t)k * nw + outw[k]];
      if (usePas && cur > 0) { pas[npas] = k; pcur[npas] = cur; npas++; } else base += cur;
    }
    // candidate wires
    int m = 0, only = -1;   // only: the single op this gate may have (shape mode), else -1
    if (!shp) { for (int w = 0; w < nw; w++) if (mark[w] != st) av[m++] = w; }
    else {
      const int cg = wcls[wg];
      for (int w = 0; w < nw; w++) if (mark[w] != st && (cg == 3 ? wcls[w] >= 2 : wcls[w] <= 1)) av[m++] = w;
      only = ((cg == 2) != shp->dual) ? AND : OR;
      if (m < 2) return;
    }
    const bool useNot = aon && !shp;
    const int npair = m * (m - 1) / 2;
    const int ntot = 2 * npair + (useNot ? m : 0);
    int chosen;
    if (nact == 0 && npas == 0) {
      chosen = only < 0 ? rng.below(ntot) : 2 * rng.below(npair) + only;  // g cannot matter: uniform
    } else {
      uint32_t* cc = ccost.data();
      uint32_t cmin = BIG;
      if (nact == 1 && npas == 0) {
        const u64* Tm = actT.data(); const u64* Cm = actC.data();
        u64* am = avm.data();
        for (int i = 0; i < m; i++) for (size_t w = 0; w < W; w++) am[(size_t)i * W + w] = vv[(size_t)av[i] * W + w] & Cm[w];
        if (WF != 0) {  // small fixed W: branch-free
          for (int i = 0; i < m; i++) {
            const u64* xa = am + (size_t)i * W;
            for (int j = i + 1; j < m; j++) {
              const u64* xb = am + (size_t)j * W;
              uint32_t c1 = base, c2 = base;
              for (size_t w = 0; w < W; w++) { c1 += pc((xa[w] & xb[w]) ^ Tm[w]); c2 += pc((xa[w] | xb[w]) ^ Tm[w]); }
              *cc++ = c1; *cc++ = c2;
            }
          }
          if (useNot) for (int i = 0; i < m; i++) {
            const u64* xa = am + (size_t)i * W; uint32_t c1 = base;
            for (size_t w = 0; w < W; w++) c1 += pc(xa[w] ^ Cm[w] ^ Tm[w]);
            *cc++ = c1;
          }
          if (only >= 0) for (int i = 0; i < npair; i++) ccost[2 * i + (1 - only)] = BIG;
          for (int i = 0; i < ntot; i++) cmin = std::min(cmin, ccost[i]);
        } else {  // many words: abandon a candidate once it is hopeless
          uint32_t lim = BIG;
          for (int i = 0; i < m; i++) {
            const u64* xa = am + (size_t)i * W;
            for (int j = i + 1; j < m; j++) {
              const u64* xb = am + (size_t)j * W;
              uint32_t c1 = only == OR ? BIG : base, c2 = only == AND ? BIG : base;
              if (only != OR) for (size_t w = 0; w < W;) {
                size_t e = std::min(W, w + 4);
                for (; w < e; w++) c1 += pc((xa[w] & xb[w]) ^ Tm[w]);
                if (c1 > lim) { c1 = BIG; break; }
              }
              if (only != AND) for (size_t w = 0; w < W;) {
                size_t e = std::min(W, w + 4);
                for (; w < e; w++) c2 += pc((xa[w] | xb[w]) ^ Tm[w]);
                if (c2 > lim) { c2 = BIG; break; }
              }
              *cc++ = c1; *cc++ = c2;
              uint32_t c = std::min(c1, c2);
              if (c < cmin) { cmin = c; lim = cmin + D; }
            }
          }
          if (useNot) for (int i = 0; i < m; i++) {
            const u64* xa = am + (size_t)i * W; uint32_t c1 = base;
            for (size_t w = 0; w < W; w++) c1 += pc(xa[w] ^ Cm[w] ^ Tm[w]);
            *cc++ = c1; cmin = std::min(cmin, c1);
          }
        }
      } else {  // several outputs involved
        u64* x = xbuf.data();
        uint32_t lim = BIG;
        auto gcost = [&]() -> uint32_t {
          uint32_t c = base;
          for (int e = 0; e < nact; e++) {
            const u64* Tk = &actT[(size_t)e * W]; const u64* Ck = &actC[(size_t)e * W];
            for (size_t w = 0; w < W; w++) c += pc((x[w] ^ Tk[w]) & Ck[w]);
            if (c > lim) return BIG;
          }
          for (int e = 0; e < npas; e++) {
            const u64* t = tg + (size_t)pas[e] * W; const u64* q = cr + (size_t)pas[e] * W;
            uint32_t cur = pcur[e], d = 0;
            for (size_t w = 0; w < W;) {
              size_t en = std::min(W, w + 4);
              for (; w < en; w++) d += pc((x[w] ^ t[w]) & q[w]);
              if (d >= cur) { d = cur; break; }
            }
            c += d;
            if (c > lim) return BIG;
          }
          return c;
        };
        for (int i = 0; i < m; i++) {
          const u64* xa = vv + (size_t)av[i] * W;
          for (int j = i + 1; j < m; j++) {
            const u64* xb = vv + (size_t)av[j] * W;
            uint32_t c1 = BIG, c2 = BIG;
            if (only != OR) { for (size_t w = 0; w < W; w++) x[w] = xa[w] & xb[w]; c1 = gcost(); }
            if (only != AND) { for (size_t w = 0; w < W; w++) x[w] = xa[w] | xb[w]; c2 = gcost(); }
            *cc++ = c1; *cc++ = c2;
            uint32_t c = std::min(c1, c2);
            if (c < cmin) { cmin = c; lim = cmin + D; }
          }
        }
        if (useNot) for (int i = 0; i < m; i++) {
          const u64* xa = vv + (size_t)av[i] * W;
          for (size_t w = 0; w < W; w++) x[w] = ~xa[w];
          uint32_t c1 = gcost();
          *cc++ = c1;
          if (c1 < cmin) { cmin = c1; lim = cmin + D; }
        }
      }
      ncand += ntot;
      // Boltzmann draw
      double tot = 0; int nsel = 0;
      const uint32_t* cs = ccost.data();
      for (int i = 0; i < ntot; i++) {
        uint32_t d = cs[i] - cmin;
        if (d < (uint32_t)D) { tot += wtab[d]; selIdx[nsel] = i; selCum[nsel] = tot; nsel++; }
      }
      double r = rng.uni() * tot;
      int lo = (int)(std::upper_bound(selCum.begin(), selCum.begin() + nsel, r) - selCum.begin());
      if (lo >= nsel) lo = nsel - 1;
      chosen = selIdx[lo];
    }
    // decode
    int nop, na, nb;
    if (chosen >= 2 * npair) { nop = NOT; na = nb = av[chosen - 2 * npair]; }
    else {
      nop = (chosen & 1) ? OR : AND;
      int p = chosen >> 1, i = 0;
      while (p >= m - 1 - i) { p -= m - 1 - i; i++; }
      na = av[i]; nb = av[i + 1 + p];
    }
    if (nop == op[g] && ((na == fa[g] && nb == fb[g]) || (na == fb[g] && nb == fa[g]))) return;
    nchanged++;
    // apply
    u64* xg = vv + (size_t)wg * W;
    {
      const u64* a = vv + (size_t)na * W; const u64* b = vv + (size_t)nb * W;
      if (nop == AND) for (size_t w = 0; w < W; w++) xg[w] = a[w] & b[w];
      else if (nop == OR) for (size_t w = 0; w < W; w++) xg[w] = a[w] | b[w];
      else for (size_t w = 0; w < W; w++) xg[w] = ~a[w];
    }
    for (int c = 0; c < nc; c++) {
      size_t o = N + cone[c];
      for (size_t w = 0; w < W; w++) vv[o * W + w] = (v1[o * W + w] & xg[w]) | (v0[o * W + w] & ~xg[w]);
    }
    op[g] = nop; fa[g] = na; fb[g] = nb;
    // keep the order topological: g and its cone move behind the new fanins
    int pg = pos[g], pm = pg;
    if (na >= N) pm = std::max(pm, (int)pos[na - N]);
    if (nb >= N) pm = std::max(pm, (int)pos[nb - N]);
    if (pm > pg) {
      int nt = 0, wpos = pg;
      for (int i = pg; i <= pm; i++) {
        int h = order[i];
        if (mark[N + h] == st) tmpo[nt++] = h; else { order[wpos] = h; pos[h] = wpos; wpos++; }
      }
      for (int i = 0; i < nt; i++) { order[wpos] = tmpo[i]; pos[tmpo[i]] = wpos; wpos++; }
    }
    // distances of the changed wires, outputs, cost
    cost = 0;
    for (int k = 0; k < K; k++) {
      uint32_t* dk = &dist[(size_t)k * nw];
      dk[wg] = wdist(k, wg);
      for (int c = 0; c < nc; c++) dk[N + cone[c]] = wdist(k, N + cone[c]);
      int o = outw[k];
      uint32_t best = dk[o];
      if (mark[o] == st) { for (int w = 0; w < nw; w++) if (dk[w] < best) { best = dk[w]; o = w; } }
      else {
        if (dk[wg] < best) { best = dk[wg]; o = wg; }
        for (int c = 0; c < nc; c++) if (dk[N + cone[c]] < best) { best = dk[N + cone[c]]; o = N + cone[c]; }
      }
      outw[k] = o; cost += best;
    }
  }
};

// ---------------------------------------------------------------------------------------------------------
// Symmetric ansatz (--sym): the circuit is invariant under a permutation sigma of the input wires. Gates come
// in orbits: "full" orbits of r = order(sigma) gates  g, sigma(g), ..., and "fixed" gates (sigma maps the gate
// to itself, so its fanin set is sigma-invariant). One move re-draws a whole orbit (heat bath over the
// representative), each candidate being evaluated by direct simulation of the orbit and its fanout cone.
// This searches a much smaller space in which symmetric needles (grid-type circuits) are easy to hit.
// It is a restriction: nothing found here says anything about asymmetric circuits.
bool g_symdebug = false, g_symbad = false;
std::atomic<u64> g_symeq{0}, g_symlt{0};
struct SymCfg {
  bool slow = false;
  std::vector<int> sigma;  // image of every input wire
  int r = 1;               // order of sigma
  int fixed = 0;           // number of fixed gates
};

template <size_t WF>
struct SymReplica {
  const View* vw = nullptr;
  const SymCfg* sc = nullptr;
  int N = 0, K = 1, s = 0, nw = 0, takeover = 2, r = 1, norb = 0;
  bool aon = false;
  size_t Wd = 0;
  inline size_t Wf() const { return WF ? WF : Wd; }
  std::vector<int> obase, olen, worb;   // orbit -> first gate, length; wire -> orbit (-1 for inputs)
  std::vector<uint8_t> op;
  std::vector<uint16_t> fa, fb, sig;    // per gate fanins; sigma on all wires
  std::vector<uint16_t> oorder, opos;   // topological order of the orbits
  std::vector<u64> val, V;
  std::vector<uint32_t> mark, omark;
  uint32_t stamp = 0;
  std::vector<int> coneOrb, chg, av, tmpo;
  std::vector<uint32_t> dist, mout;
  std::vector<uint16_t> outw;
  uint32_t cost = 0;
  std::vector<uint32_t> ccost, selIdx;
  std::vector<uint16_t> candA, candB;
  std::vector<uint8_t> candOp;
  std::vector<double> selCum;
  Rng rng;
  u64 ncand = 0, nsteps = 0, nchanged = 0;
  int nmoves() const { return norb; }

  void setup(const View* v, int s_, bool aon_, int takeover_, u64 seed) {
    vw = v; sc = v->sym; N = v->N; K = v->K; s = s_; nw = N + s; aon = aon_; takeover = takeover_; Wd = v->W;
    r = sc->r; slowEval = sc->slow;
    rng = Rng(seed);
    int nfull = (s - sc->fixed) / r;
    norb = nfull + sc->fixed;
    obase.resize(norb); olen.resize(norb); worb.assign(nw, -1); sig.resize(nw);
    for (int i = 0; i < N; i++) sig[i] = sc->sigma[i];
    int g = 0;
    for (int o = 0; o < norb; o++) {
      obase[o] = g; olen[o] = o < nfull ? r : 1;
      for (int j = 0; j < olen[o]; j++) { worb[N + g + j] = o; sig[N + g + j] = N + g + (j + 1) % olen[o]; }
      g += olen[o];
    }
    op.assign(s, AND); fa.assign(s, 0); fb.assign(s, 0);
    oorder.resize(norb); opos.resize(norb);
    val.assign((size_t)nw * Wf(), 0); V.assign((size_t)nw * Wf(), 0);
    mark.assign(nw, 0); omark.assign(norb, 0);
    dist.assign((size_t)K * nw, 0); mout.assign(K, 0); outw.assign(K, 0);
    size_t nc = (size_t)nw * nw + nw;
    ccost.resize(nc); selIdx.resize(nc); selCum.resize(nc); candA.resize(nc); candB.resize(nc); candOp.resize(nc);
  }
  void resize() {}
  void setRep(int o, int cop, int a, int b) {
    for (int j = 0; j < olen[o]; j++) {
      int g = obase[o] + j;
      op[g] = cop; fa[g] = a; fb[g] = b;
      a = sig[a]; b = sig[b];
    }
  }
  // candidates for orbit o among the wires in av[0..m): returns their number
  int listCands(int o, int m) {
    int n = 0;
    if (olen[o] > 1 || r == 1) {
      for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
        candA[n] = av[i]; candB[n] = av[j]; candOp[n] = AND; n++;
        candA[n] = av[i]; candB[n] = av[j]; candOp[n] = OR; n++;
      }
      if (aon) for (int i = 0; i < m; i++) { candA[n] = candB[n] = av[i]; candOp[n] = NOT; n++; }
    } else {
      for (int i = 0; i < m; i++) {
        int a = av[i];
        if (sig[a] == a) {
          for (int j = i + 1; j < m; j++) if (sig[av[j]] == av[j]) {
            candA[n] = a; candB[n] = av[j]; candOp[n] = AND; n++;
            candA[n] = a; candB[n] = av[j]; candOp[n] = OR; n++;
          }
          if (aon) { candA[n] = candB[n] = a; candOp[n] = NOT; n++; }
        } else if (sig[sig[a]] == a && a < sig[a]) {
          candA[n] = a; candB[n] = sig[a]; candOp[n] = AND; n++;
          candA[n] = a; candB[n] = sig[a]; candOp[n] = OR; n++;
        }
      }
    }
    return n;
  }
  void randomize() {
    // random order of the orbits; an orbit reads wires of earlier orbits only
    for (int i = 0; i < norb; i++) oorder[i] = i;
    for (int tries = 0;; tries++) {
      for (int i = norb - 1; i > 0; i--) std::swap(oorder[i], oorder[rng.below(i + 1)]);
      bool ok = true;
      int m = 0;
      av.resize(nw);
      for (int i = 0; i < N; i++) av[m++] = i;
      for (int i = 0; i < norb && ok; i++) {
        int o = oorder[i];
        opos[o] = i;
        int n = listCands(o, m);
        if (n == 0) { ok = false; break; }
        int c = rng.below(n);
        setRep(o, candOp[c], candA[c], candB[c]);
        for (int j = 0; j < olen[o]; j++) av[m++] = N + obase[o] + j;
      }
      if (ok) break;
      if (tries > 1000) die("--sym: cannot place the fixed gates (no sigma-invariant pair of wires); change --fixed");
    }
    resim();
  }
  void load(const GL&) { die("--init is not supported together with --sym"); }
  GL snapshot() const {
    GL g; std::vector<int> id(nw);
    for (int i = 0; i < N; i++) id[i] = i;
    int c = N;
    for (int i = 0; i < norb; i++) { int o = oorder[i]; for (int j = 0; j < olen[o]; j++) id[N + obase[o] + j] = c++; }
    for (int i = 0; i < norb; i++) { int o = oorder[i]; for (int j = 0; j < olen[o]; j++) { int h = obase[o] + j; g.op.push_back(op[h]); g.fa.push_back(id[fa[h]]); g.fb.push_back(id[fb[h]]); } }
    return g;
  }
  inline void gev(int cop, const u64* a, const u64* b, u64* o) const {
    if (cop == AND) for (size_t w = 0; w < Wf(); w++) o[w] = a[w] & b[w];
    else if (cop == OR) for (size_t w = 0; w < Wf(); w++) o[w] = a[w] | b[w];
    else for (size_t w = 0; w < Wf(); w++) o[w] = ~a[w];
  }
  inline uint32_t cdist(int k, const u64* x) const {
    const u64* t = &vw->tgt[(size_t)k * Wf()]; const u64* c = &vw->care[(size_t)k * Wf()];
    uint32_t d = 0;
    for (size_t i = 0; i < Wf(); i++) d += pc((x[i] ^ t[i]) & c[i]);
    return d;
  }
  void resim() {
    Wd = vw->W;
    if (val.size() != (size_t)nw * Wf()) { val.assign((size_t)nw * Wf(), 0); V.assign((size_t)nw * Wf(), 0); }
    std::copy(vw->in.begin(), vw->in.end(), val.begin());
    for (int i = 0; i < norb; i++) {
      int o = oorder[i];
      for (int j = 0; j < olen[o]; j++) { int h = obase[o] + j; gev(op[h], &val[(size_t)fa[h] * Wf()], &val[(size_t)fb[h] * Wf()], &val[(size_t)(N + h) * Wf()]); }
    }
    cost = 0;
    for (int k = 0; k < K; k++) {
      uint32_t best = BIG; int bw = 0;
      for (int w = 0; w < nw; w++) { uint32_t d = cdist(k, &val[(size_t)w * Wf()]); dist[(size_t)k * nw + w] = d; if (d < best) { best = d; bw = w; } }
      outw[k] = bw; cost += best;
    }
  }
  bool selfcheck() const {
    std::vector<u64> v((size_t)nw * Wf());
    std::copy(vw->in.begin(), vw->in.end(), v.begin());
    std::vector<char> seen(nw, 0);
    for (int i = 0; i < N; i++) seen[i] = 1;
    for (int i = 0; i < norb; i++) {
      int o = oorder[i];
      if (opos[o] != i) return false;
      for (int j = 0; j < olen[o]; j++) {
        int h = obase[o] + j, h2 = obase[o] + (j + 1) % olen[o];
        if (!seen[fa[h]] || !seen[fb[h]]) return false;
        // symmetry: sigma(h) = h2
        if (op[h] != op[h2]) return false;
        if (!((sig[fa[h]] == fa[h2] && sig[fb[h]] == fb[h2]) || (sig[fa[h]] == fb[h2] && sig[fb[h]] == fa[h2]))) return false;
        const u64* a = &v[(size_t)fa[h] * Wf()]; const u64* b = &v[(size_t)fb[h] * Wf()]; u64* q = &v[(size_t)(N + h) * Wf()];
        for (size_t w = 0; w < Wf(); w++) q[w] = op[h] == AND ? (a[w] & b[w]) : op[h] == OR ? (a[w] | b[w]) : ~a[w];
      }
      for (int j = 0; j < olen[o]; j++) seen[N + obase[o] + j] = 1;
    }
    if (v != val) return false;
    uint32_t c = 0;
    for (int k = 0; k < K; k++) {
      uint32_t best = BIG;
      for (int w = 0; w < nw; w++) { uint32_t d = cdist(k, &val[(size_t)w * Wf()]); if (d != dist[(size_t)k * nw + w]) return false; best = std::min(best, d); }
      if (dist[(size_t)k * nw + outw[k]] != best) return false;
      c += best;
    }
    return c == cost;
  }
  Circuit toCircuit(bool prune) const {
    std::vector<int> ord;
    for (int i = 0; i < norb; i++) { int o = oorder[i]; for (int j = 0; j < olen[o]; j++) ord.push_back(obase[o] + j); }
    std::vector<char> need(nw, prune ? 0 : 1);
    if (prune) {
      for (int k = 0; k < K; k++) need[outw[k]] = 1;
      for (int i = s - 1; i >= 0; i--) { int h = ord[i]; if (need[N + h]) { need[fa[h]] = 1; need[fb[h]] = 1; } }
    }
    std::vector<int> id(nw, -1);
    for (int i = 0; i < N; i++) id[i] = i;
    Circuit c; c.N = N;
    for (int i = 0; i < s; i++) {
      int h = ord[i];
      if (!need[N + h]) continue;
      Gate g; g.op = (Op)op[h]; g.a = id[fa[h]];
      if (op[h] == NOT) { g.nin = 1; g.b = 0; } else { g.nin = 2; g.b = id[fb[h]]; }
      id[N + h] = N + (int)c.gates.size();
      c.gates.push_back(g);
    }
    for (int k = 0; k < K; k++) c.outs.push_back(id[outw[k]]);
    return c;
  }
  // simulate orbit o := (cop, a, b) and its cone into V; returns the cost
  struct CG { const u64* a; const u64* b; u64* o; int op; };
  std::vector<CG> cg;
  std::vector<int> mkOut, actIdx, pasK;
  std::vector<uint32_t> pasCur;
  std::vector<u64> raw, xj;
  std::vector<char> isActBuf;
  bool slowEval = false;   // true: score candidates by direct simulation with the true min-over-wires cost
  void prepCone(int nc, uint32_t st) {
    cg.clear();
    for (int c = 0; c < nc; c++) {
      int q = coneOrb[c];
      for (int j = 0; j < olen[q]; j++) {
        int h = obase[q] + j; size_t x = fa[h], y = fb[h];
        cg.push_back({(mark[x] == st ? V.data() : val.data()) + x * Wf(), (mark[y] == st ? V.data() : val.data()) + y * Wf(), &V[(size_t)(N + h) * Wf()], op[h]});
      }
    }
  }
  inline uint32_t trial(int o, int cop, int a, int b, int nc, uint32_t st) {
    const size_t W = Wf();
    u64* vo = &V[(size_t)(N + obase[o]) * W];
    const u64* vv = val.data();
    for (int j = 0; j < olen[o]; j++) {
      gev(cop, vv + (size_t)a * W, vv + (size_t)b * W, vo + (size_t)j * W);
      a = sig[a]; b = sig[b];
    }
    for (const CG& g : cg) gev(g.op, g.a, g.b, g.o);
    uint32_t c = 0;
    const int* cw = chg.data(); const int ncw = (int)chg.size();
    for (int k = 0; k < K; k++) {
      uint32_t m = mout[k];
      const u64* t = &vw->tgt[(size_t)k * W]; const u64* cr = &vw->care[(size_t)k * W];
      for (int i = 0; i < ncw; i++) {
        const u64* x = &V[(size_t)cw[i] * W];
        uint32_t d = 0;
        for (size_t w = 0; w < W; w++) d += pc((x[w] ^ t[w]) & cr[w]);
        m = d < m ? d : m;
      }
      c += m;
    }
    return c;
  }
  void step(int o, const float* wtab, int D) {
    const uint32_t st = ++stamp;
    nsteps++;
    chg.clear();
    for (int j = 0; j < olen[o]; j++) { mark[N + obase[o] + j] = st; chg.push_back(N + obase[o] + j); }
    omark[o] = st;
    int nc = 0;
    coneOrb.resize(norb);
    for (int i = opos[o] + 1; i < norb; i++) {
      int q = oorder[i], h = obase[q];
      if (mark[fa[h]] == st || mark[fb[h]] == st) {
        omark[q] = st; coneOrb[nc++] = q;
        for (int j = 0; j < olen[q]; j++) { mark[N + obase[q] + j] = st; chg.push_back(N + obase[q] + j); }
      }
    }
    int m = 0;
    av.resize(nw);
    for (int w = 0; w < nw; w++) if (mark[w] != st) av[m++] = w;
    for (int k = 0; k < K; k++) {
      uint32_t b = BIG;
      for (int i = 0; i < m; i++) b = std::min(b, dist[(size_t)k * nw + av[i]]);
      mout[k] = b;
    }
    int ntot = listCands(o, m);
    if (ntot == 0) return;
    prepCone(nc, st);
    uint32_t cmin = BIG;
    const int L = olen[o];
    if (L <= 4 && !slowEval) {
      // Need-mask generalisation: simulate the cone for all 2^L constant settings of the orbit's gates; an output in
      // the cone is then wrong at point p according to mask[x_0(p), ..., x_{L-1}(p)], so a candidate costs one mux
      // tree + popcount per output instead of a cone simulation. Outputs outside the cone: takeover by a member.
      const size_t W = Wf();
      const int nm = 1 << L;
      const u64* tg = vw->tgt.data(); const u64* cr = vw->care.data();
      mkOut.clear();
      for (int k = 0; k < K; k++) if (mark[outw[k]] == st) mkOut.push_back(k);
      raw.resize(mkOut.size() * nm * W);
      u64* vo = &V[(size_t)(N + obase[o]) * W];
      for (int c = 0; c < nm; c++) {
        for (int j = 0; j < L; j++) for (size_t w = 0; w < W; w++) vo[(size_t)j * W + w] = ((c >> j) & 1) ? ~u64(0) : 0;
        for (const CG& g : cg) gev(g.op, g.a, g.b, g.o);
        for (size_t e = 0; e < mkOut.size(); e++) {
          int k = mkOut[e]; const u64* x = &V[(size_t)outw[k] * W];
          for (size_t w = 0; w < W; w++) raw[(e * nm + c) * W + w] = (x[w] ^ tg[(size_t)k * W + w]) & cr[(size_t)k * W + w];
        }
      }
      uint32_t base = 0; int nact = 0;
      actIdx.clear(); pasK.clear(); pasCur.clear();
      std::vector<char>& isAct = isActBuf; isAct.assign(K, 0);
      for (size_t e = 0; e < mkOut.size(); e++) {
        bool same = true;
        for (int c = 1; c < nm && same; c++) for (size_t w = 0; w < W; w++) if (raw[(e * nm + c) * W + w] != raw[e * nm * W + w]) { same = false; break; }
        if (!same) { actIdx.push_back((int)e); isAct[mkOut[e]] = 1; nact++; }
      }
      const bool usePas = takeover == 2 || (takeover == 1 && nact == 0);
      for (int k = 0; k < K; k++) if (!isAct[k]) {
        uint32_t cur = dist[(size_t)k * nw + outw[k]];
        if (usePas && cur > 0) { pasK.push_back(k); pasCur.push_back(cur); } else base += cur;
      }
      xj.resize((size_t)L * W);
      const u64* vv = val.data();
      for (int i = 0; i < ntot; i++) {
        int a = candA[i], b = candB[i], cop = candOp[i];
        for (int j = 0; j < L; j++) { gev(cop, vv + (size_t)a * W, vv + (size_t)b * W, &xj[(size_t)j * W]); a = sig[a]; b = sig[b]; }
        uint32_t c = base;
        for (int e : actIdx) {
          const u64* M = &raw[(size_t)e * nm * W];
          for (size_t w = 0; w < W; w++) {
            u64 m[16];
            for (int q = 0; q < nm; q++) m[q] = M[(size_t)q * W + w];
            for (int j = 0, n2 = nm >> 1; j < L; j++, n2 >>= 1) {
              u64 x = xj[(size_t)j * W + w];
              for (int q = 0; q < n2; q++) m[q] = (x & m[2 * q + 1]) | (~x & m[2 * q]);
            }
            c += pc(m[0]);
          }
        }
        for (size_t e = 0; e < pasK.size(); e++) {
          int k = pasK[e]; uint32_t best = pasCur[e];
          for (int j = 0; j < L; j++) { uint32_t d = cdist(k, &xj[(size_t)j * W]); if (d < best) best = d; }
          c += best;
        }
        if (g_symdebug) {  // the fixed-assignment cost can never be below the true min-over-wires cost
          uint32_t t = trial(o, candOp[i], candA[i], candB[i], nc, st);
          if (t > c) { fprintf(stderr, "cktsls: SYM FAST-PATH MISMATCH fast=%u true=%u\n", c, t); g_symbad = true; }
          if (t == c) g_symeq++; else g_symlt++;
        }
        ccost[i] = c; if (c < cmin) cmin = c;
      }
    } else {
      for (int i = 0; i < ntot; i++) { uint32_t c = trial(o, candOp[i], candA[i], candB[i], nc, st); ccost[i] = c; if (c < cmin) cmin = c; }
    }
    ncand += ntot;
    double tot = 0; int nsel = 0;
    for (int i = 0; i < ntot; i++) {
      uint32_t d = ccost[i] - cmin;
      if (d < (uint32_t)D) { tot += wtab[d]; selIdx[nsel] = i; selCum[nsel] = tot; nsel++; }
    }
    double rr = rng.uni() * tot;
    int lo = (int)(std::upper_bound(selCum.begin(), selCum.begin() + nsel, rr) - selCum.begin());
    if (lo >= nsel) lo = nsel - 1;
    int ch = selIdx[lo];
    int nop = candOp[ch], na = candA[ch], nb = candB[ch];
    int g0 = obase[o];
    if (nop == op[g0]) {  // same orbit as before (any rotation)?
      int a = na, b = nb;
      for (int j = 0; j < olen[o]; j++) {
        if ((a == fa[g0] && b == fb[g0]) || (a == fb[g0] && b == fa[g0])) return;
        a = sig[a]; b = sig[b];
      }
    }
    nchanged++;
    trial(o, nop, na, nb, nc, st);
    for (int w : chg) std::copy(&V[(size_t)w * Wf()], &V[(size_t)w * Wf()] + Wf(), &val[(size_t)w * Wf()]);
    setRep(o, nop, na, nb);
    int po = opos[o], pm = po;
    if (worb[na] >= 0) pm = std::max(pm, (int)opos[worb[na]]);
    if (worb[nb] >= 0) pm = std::max(pm, (int)opos[worb[nb]]);
    if (pm > po) {
      tmpo.clear();
      int wpos = po;
      for (int i = po; i <= pm; i++) {
        int q = oorder[i];
        if (omark[q] == st) tmpo.push_back(q); else { oorder[wpos] = q; opos[q] = wpos; wpos++; }
      }
      for (int q : tmpo) { oorder[wpos] = q; opos[q] = wpos; wpos++; }
    }
    cost = 0;
    for (int k = 0; k < K; k++) {
      uint32_t* dk = &dist[(size_t)k * nw];
      for (int w : chg) dk[w] = cdist(k, &val[(size_t)w * Wf()]);
      int bo = outw[k]; uint32_t best = dk[bo];
      for (int w = 0; w < nw; w++) if (dk[w] < best) { best = dk[w]; bo = w; }
      outw[k] = bo; cost += best;
    }
  }
};

// order of a permutation, and whether the spec is invariant under it (inputs permuted, outputs permuted accordingly)
int permOrder(const std::vector<int>& sg) {
  int n = (int)sg.size(); std::vector<char> seen(n, 0); long ord = 1;
  for (int i = 0; i < n; i++) if (!seen[i]) {
    int len = 0; for (int j = i; !seen[j]; j = sg[j]) { seen[j] = 1; len++; }
    long a = ord, b = len; while (b) { long t = a % b; a = b; b = t; }
    ord = ord / a * len;
  }
  return (int)ord;
}
std::vector<int> parsePerm(const std::string& t, int N) {
  std::vector<int> sg(N);
  for (int i = 0; i < N; i++) sg[i] = i;
  if (t.find('(') != std::string::npos) {
    size_t i = 0;
    while ((i = t.find('(', i)) != std::string::npos) {
      size_t e = t.find(')', i);
      if (e == std::string::npos) die("--sym: missing ')'");
      std::string body = t.substr(i + 1, e - i - 1);
      for (auto& ch : body) if (ch == ',') ch = ' ';
      std::istringstream is(body); std::vector<int> cyc; int x;
      while (is >> x) { if (x < 0 || x >= N) die("--sym: wire out of range"); cyc.push_back(x); }
      for (size_t j = 0; j < cyc.size(); j++) sg[cyc[j]] = cyc[(j + 1) % cyc.size()];
      i = e + 1;
    }
  } else {
    std::string body = t;
    for (auto& ch : body) if (ch == ',') ch = ' ';
    std::istringstream is(body); int x, n = 0;
    while (is >> x) { if (n >= N || x < 0 || x >= N) die("--sym: bad image list"); sg[n++] = x; }
    if (n != N) die("--sym: image list must have one entry per input wire");
  }
  std::vector<char> hit(N, 0);
  for (int i = 0; i < N; i++) { if (hit[sg[i]]) die("--sym: not a permutation"); hit[sg[i]] = 1; }
  return sg;
}
bool specInvariant(const Spec& sp, const std::vector<int>& sg) {
  std::vector<std::pair<std::string, uint32_t>> keys(sp.P);
  for (size_t p = 0; p < sp.P; p++) {
    std::string k(sp.N, '0');
    for (int i = 0; i < sp.N; i++) if (getbit(sp.in[i], p)) k[i] = '1';
    keys[p] = {k, (uint32_t)p};
  }
  std::sort(keys.begin(), keys.end());
  std::vector<uint32_t> pi(sp.P);
  for (size_t p = 0; p < sp.P; p++) {
    std::string k(sp.N, '0');
    for (int i = 0; i < sp.N; i++) if (getbit(sp.in[i], p)) k[sg[i]] = '1';
    auto it = std::lower_bound(keys.begin(), keys.end(), std::make_pair(k, (uint32_t)0));
    if (it == keys.end() || it->first != k) return false;
    pi[p] = it->second;
  }
  for (int k = 0; k < sp.K; k++) {
    bool any = false;
    for (int k2 = 0; k2 < sp.K && !any; k2++) {
      bool ok = true;
      for (size_t p = 0; p < sp.P && ok; p++) {
        bool c1 = getbit(sp.care[k], p), c2 = getbit(sp.care[k2], pi[p]);
        if (c1 != c2 || (c1 && getbit(sp.tgt[k], p) != getbit(sp.tgt[k2], pi[p]))) ok = false;
      }
      any = ok;
    }
    if (!any) return false;
  }
  return true;
}

inline int symFixed(const SymCfg* c) { return c->fixed; }

template <class Rep>
struct Island {
  int id = 0, R = 0, s = 0, sweep = 0;
  const Spec* sp = nullptr;
  const Opts* op = nullptr;
  View vw;
  std::vector<Rep> reps;
  std::vector<int> slot;                 // slot[t] = replica at temperature t
  std::vector<double> temps;
  std::vector<std::vector<float>> wtab;
  Rng rng;
  uint32_t best = BIG;                   // best cost seen (on the island's view)
  GL bestGL;
  bool found = false; long foundIter = -1; Circuit foundCkt;
  u64 nverify = 0, ncex = 0, nswapTry = 0, nswapOk = 0;
  std::vector<double> esum; std::vector<u64> ecnt, eswap, wtry, wok;
  long nadapt = 0, sinceAdapt = 0, iters = 0;
  bool adaptive = true;
  bool bug = false;

  void resimAll() { for (auto& r : reps) r.resim(); best = BIG; }

  static void makeTable(std::vector<float>& tab, double T) {
    int D = (int)std::min(65536.0, 2 + std::ceil(T * 18));
    tab.resize(D);
    for (int d = 0; d < D; d++) tab[d] = (float)std::exp(-(double)d / T);
  }
  void setLadder(double tmin, double tmax) {
    for (int t = 0; t < R; t++) {
      temps[t] = R == 1 ? tmin : tmin * std::pow(tmax / tmin, (double)t / (R - 1));
      makeTable(wtab[t], temps[t]);
    }
  }
  // Move the interior temperatures so that neighbouring replicas exchange at similar rates (ends stay fixed).
  void adapt() {
    if (R < 3) return;
    std::vector<double> gap(R - 1);
    double mean = 0;
    for (int t = 0; t + 1 < R; t++) mean += wtry[t] ? (double)wok[t] / wtry[t] : 1.0;
    mean /= (R - 1);
    double tot = 0, want = std::log(temps[R - 1] / temps[0]);
    for (int t = 0; t + 1 < R; t++) {
      double a = wtry[t] ? (double)wok[t] / wtry[t] : 1.0;
      double f = std::clamp((a + 0.1) / (mean + 0.1), 0.6, 1.6);   // exchanges too rare -> shrink this gap
      gap[t] = std::log(temps[t + 1] / temps[t]) * f;
      tot += gap[t];
    }
    for (int t = 0; t + 1 < R; t++) {
      if (t + 1 < R - 1) { temps[t + 1] = temps[t] * std::exp(gap[t] * want / tot); makeTable(wtab[t + 1], temps[t + 1]); }
      wtry[t] = wok[t] = 0;
    }
    nadapt++;
  }

  // returns true when r is a verified solution; otherwise (sampled view) feeds counterexamples into the sample
  bool check(Rep& r) {
    Circuit c = r.toCircuit(!op->noprune);
    nverify++;
    std::vector<u64> buf;
    eval(*sp, c, buf);
    std::vector<uint32_t> wrong;
    size_t tot = (size_t)c.N + c.gates.size();
    for (size_t w = 0; w < sp->W; w++) {
      u64 d = 0;
      for (int k = 0; k < sp->K; k++) {
        int o = c.outs[k];
        u64 v = (o >= 0 && (size_t)o < tot) ? buf[(size_t)o * sp->W + w] : 0;
        d |= (v ^ sp->tgt[k][w]) & sp->care[k][w];
      }
      while (d) { wrong.push_back((uint32_t)(w * 64 + __builtin_ctzll(d))); d &= d - 1; }
    }
    if (wrong.empty()) {
      Verdict v = verify(*sp, c);
      if (!v.ok || !basis_ok(c, op->basis)) { bug = true; return false; }
      foundCkt = c; found = true;
      return true;
    }
    if (!vw.sampled) { bug = true; return false; }
    ncex++;
    size_t add = std::min<size_t>(wrong.size(), 32);
    for (size_t i = 0; i < add; i++) {
      size_t j = i + rng.below((uint32_t)(wrong.size() - i));
      std::swap(wrong[i], wrong[j]);
      vw.addCex(*sp, wrong[i]);
    }
    resimAll();
    return false;
  }

  void run(long M, std::atomic<long>& stopIter) {
    if (found || bug) return;
    const int nmv = reps[0].nmoves();
    for (auto& r : reps) if (r.cost == 0 && check(r)) { foundIter = 0; lower(stopIter, 0); return; }
    for (long it = 0; it <= stopIter.load(std::memory_order_relaxed) && it < M; it++) {
      for (int t = 0; t < R; t++) {
        Rep& r = reps[slot[t]];
        const float* wt = wtab[t].data(); int D = (int)wtab[t].size();
        for (int q = 0; q < sweep; q++) {
          r.step(r.rng.below(nmv), wt, D);
          if (op->selfcheck && !r.selfcheck()) { bug = true; return; }
          if (r.cost < best) { best = r.cost; bestGL = r.snapshot(); }
          if (r.cost == 0) {
            if (check(r)) { foundIter = it; lower(stopIter, it); return; }
            if (bug) return;
          }
        }
      }
      for (int t = 0; t < R; t++) { esum[t] += reps[slot[t]].cost; ecnt[t]++; }
      for (int t = (int)(iters++ & 1); t + 1 < R; t += 2) {
        Rep& x = reps[slot[t]]; Rep& y = reps[slot[t + 1]];
        double d = (1.0 / temps[t] - 1.0 / temps[t + 1]) * ((double)x.cost - (double)y.cost);
        nswapTry++; wtry[t]++;
        if (d >= 0 || rng.uni() < std::exp(d)) { std::swap(slot[t], slot[t + 1]); nswapOk++; eswap[t]++; wok[t]++; }
      }
      if (adaptive && ++sinceAdapt >= std::min(400L, 40 + 20 * nadapt)) {
        sinceAdapt = 0;
        adapt();
        if (nadapt % 8 == 0) { for (int t = 0; t < R; t++) { esum[t] = 0; ecnt[t] = 0; eswap[t] = 0; } }
      }
    }
  }
  static void lower(std::atomic<long>& a, long v) {
    long c = a.load();
    while (v < c && !a.compare_exchange_weak(c, v)) {}
  }
};

double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

template <class Rep>
int runSearch(const Spec& sp, const Opts& o, const std::vector<View>& views) {
  const bool aon = o.basis == "aon";
  const int s = o.s, nI = (int)views.size(), R = o.R;
  const int K = sp.K, nw = sp.N + s;
  const size_t W = views[0].W, npts = views[0].npts;
  int takeover = o.takeover >= 0 ? o.takeover : (K <= 2 ? 2 : 1);
  double tmin = o.tmin > 0 ? o.tmin : 0.03;
  double tmax = o.tmax;
  if (R == 1) tmax = tmin;
  int sweep = o.sweep > 0 ? o.sweep : std::max(4, s);
  Circuit initc;
  if (!o.init.empty()) { initc = load_circuit(o.init); if (initc.N != sp.N) die("--init: wrong number of inputs"); }

  std::vector<Island<Rep>> isl(nI);
  for (int i = 0; i < nI; i++) {
    Island<Rep>& I = isl[i];
    I.id = i; I.R = R; I.s = s; I.sweep = sweep; I.sp = &sp; I.op = &o; I.vw = views[i];
    u64 z = o.seed * 0x9e3779b97f4a7c15ULL + (u64)i * 0xd1b54a32d192ed03ULL + 12345;
    I.rng = Rng(Rng::splitmix(z));
    I.temps.resize(R); I.wtab.resize(R); I.slot.resize(R); I.reps.resize(R);
    I.esum.assign(R, 0); I.ecnt.assign(R, 0); I.eswap.assign(R, 0);
    I.wtry.assign(R, 0); I.wok.assign(R, 0); I.adaptive = !o.noadapt;
    for (int t = 0; t < R; t++) {
      I.slot[t] = t;
      I.reps[t].setup(&I.vw, s, aon, takeover, Rng::splitmix(z));
      if (!o.init.empty()) I.reps[t].load(adaptInit(initc, sp.N, s, aon, I.reps[t].rng));
      else I.reps[t].randomize();
    }
  }
  double t0 = now(), tlast = t0;
  // a start state (e.g. --init) may already be a solution: check before spending anything
  { std::atomic<long> st0(0); for (auto& I : isl) I.run(0, st0); }
  bool pre = false;
  for (auto& I : isl) pre = pre || I.found || I.bug;
  // rough work per heat-bath step, in word operations
  const double stepWork = (double)nw * nw * (double)std::min<size_t>(W, 4) * (K > 1 ? 2 : 1);
  if (!pre && tmax <= 0) {
    if (605.0 * s * stepWork > 4e9) {
      tmax = std::max(0.2, (double)npts / 150);   // too big to calibrate in about a second: rule of thumb
    } else {
      // Calibrate the hot end: the temperature at which the mean cost is hotfrac of the way from the quenched
      // cost to the infinite-temperature cost.
      u64 z = o.seed * 0x9e3779b97f4a7c15ULL + 999;
      Rep r;
      r.setup(&views[0], s, aon, takeover, Rng::splitmix(z));
      r.randomize();
      std::vector<float> tab;
      auto meanCost = [&](double T, int burn, int n) {
        Island<Rep>::makeTable(tab, T);
        for (int i = 0; i < burn; i++) r.step(r.rng.below(r.nmoves()), tab.data(), (int)tab.size());
        double m = 0;
        for (int i = 0; i < n; i++) { r.step(r.rng.below(r.nmoves()), tab.data(), (int)tab.size()); m += r.cost; }
        return m / n;
      };
      double cinf = meanCost(1e12, 5 * s, 40 * s);
      double ccold = meanCost(tmin, 100 * s, 20 * s);
      double goal = ccold + o.hotfrac * (cinf - ccold);
      double lo = std::log(0.05), hi = std::log(std::max(1.0, (double)npts / 8));
      for (int it = 0; it < 8; it++) {
        double mid = 0.5 * (lo + hi);
        if (meanCost(std::exp(mid), 15 * s, 40 * s) < goal) lo = mid; else hi = mid;
      }
      tmax = std::max(0.12, std::exp(hi));
    }
  }
  if (tmax < tmin) tmax = tmin;
  for (auto& I : isl) I.setLadder(tmin, tmax);
  // deterministic round length (heat-bath iterations per island per round)
  double nsStep = 150.0 + (double)nw * nw * (double)(W <= 8 ? W : 3) * 1.2 * (K > 1 ? 2 : 1);
  long Mmax = std::max(1L, (long)(30e6 / (nsStep * R * sweep)));
  long M = std::min(Mmax, 8L);
  if (!o.quiet)
    fprintf(stderr, "cktsls: %s basis=%s s=%d  N=%d K=%d points=%zu%s W=%zu  islands=%d threads=%d replicas=%d T=[%.3g..%.3g] sweep=%d takeover=%d seed=%llu\n",
            o.spec.c_str(), o.basis.c_str(), s, sp.N, K, npts, views[0].sampled ? " (sampled)" : "", W, nI, o.T, R, tmin, tmax, sweep, takeover,
            (unsigned long long)o.seed);
  long rounds = 0;
  int winner = -1;
  if (pre) {
    for (int i = 0; i < nI; i++) {
      if (isl[i].bug) { fprintf(stderr, "cktsls: INTERNAL ERROR (island %d: verify mismatch)\n", i); return 3; }
      if (isl[i].found && winner < 0) winner = i;
    }
  }
  while (winner < 0) {
    std::atomic<long> stopIter(M - 1);
    std::atomic<int> nextI(0);
    auto work = [&] { for (int i; (i = nextI++) < nI;) isl[i].run(M, stopIter); };
    if (o.T <= 1 || nI == 1) work();
    else {
      std::vector<std::thread> th;
      for (int t = 0; t < std::min(o.T, nI); t++) th.emplace_back(work);
      for (auto& t : th) t.join();
    }
    rounds++;
    long bi = -1;
    for (int i = 0; i < nI; i++) {
      if (isl[i].bug) { fprintf(stderr, "cktsls: INTERNAL ERROR (island %d: selfcheck/verify mismatch)\n", i); return 3; }
      if (isl[i].found && (bi < 0 || isl[i].foundIter < bi)) { bi = isl[i].foundIter; winner = i; }
    }
    double t = now();
    if (winner >= 0) break;
    if (o.migrate > 0 && rounds % o.migrate == 0 && nI > 1) {  // deterministic: copy the best island's best state
      int b = 0;
      for (int i = 1; i < nI; i++) if (isl[i].best < isl[b].best) b = i;
      if (!isl[b].bestGL.op.empty())
        for (int i = 0; i < nI; i++) if (i != b) { auto& r = isl[i].reps[isl[i].slot[R / 2]]; r.load(isl[b].bestGL); }
    }
    if (!o.quiet && t - tlast >= 2.0) {
      u64 st = 0, cd = 0, cx = 0; uint32_t gb = BIG;
      std::string per;
      for (auto& I : isl) {
        for (auto& r : I.reps) { st += r.nsteps; cd += r.ncand; }
        cx += I.ncex; gb = std::min(gb, I.best);
        per += " " + std::to_string(I.reps[I.slot[0]].cost) + "/" + std::to_string(I.best);
      }
      fprintf(stderr, "[%7.1fs] steps %.3g (%.3g/s)  cand-evals %.3g (%.3g/s)  best %u  cold/best per island:%s%s\n", t - t0, (double)st,
              st / (t - t0), (double)cd, cd / (t - t0), gb, per.c_str(), views[0].sampled ? ("  cex " + std::to_string(cx)).c_str() : "");
      tlast = t;
    }
    if (t - t0 >= o.tlim || (o.rounds > 0 && rounds >= o.rounds)) break;
    M = std::min(Mmax, M * 2);
  }
  double el = now() - t0;
  u64 st = 0, cd = 0, cx = 0, sw = 0, swo = 0; uint32_t gb = BIG; int gbi = 0;
  for (auto& I : isl) {
    for (auto& r : I.reps) { st += r.nsteps; cd += r.ncand; }
    cx += I.ncex; sw += I.nswapTry; swo += I.nswapOk;
    if (I.best < gb) { gb = I.best; gbi = I.id; }
  }
  if (o.ladder) {
    fprintf(stderr, "ladder (island 0):  T  mean-cost  swap-up-rate\n");
    auto& I = isl[0];
    for (int t = 0; t < R; t++)
      fprintf(stderr, "  %8.4f  %8.3f  %.3f\n", I.temps[t], I.ecnt[t] ? I.esum[t] / I.ecnt[t] : 0.0, I.ecnt[t] ? 2.0 * I.eswap[t] / I.ecnt[t] : 0.0);
  }
  if (g_symdebug) fprintf(stderr, "sym-debug: fast cost == true cost for %llu candidates, above it for %llu, below (BUG): %s\n",
                          (unsigned long long)g_symeq.load(), (unsigned long long)g_symlt.load(), g_symbad ? "YES" : "never");
  if (winner >= 0) {
    const Circuit& c = isl[winner].foundCkt;
    Verdict v = verify(sp, c);   // final independent re-check on ALL points
    std::string why;
    if (!v.ok || !basis_ok(c, o.basis == "ao" ? "ao2" : "aon", &why) || c.size() > s) {
      fprintf(stderr, "cktsls: INTERNAL ERROR: final verification failed (%s)\n", why.c_str());
      return 3;
    }
    char cm[512];
    std::string symnote;
    if (views[winner].sym) symnote = " sym=\"" + o.sym + "\" fixed=" + std::to_string(symFixed(views[winner].sym));
    if (views[winner].shape) symnote += " shape=" + o.shape.substr(0, 3) + ":" + std::to_string(views[winner].shape->nP);
    snprintf(cm, sizeof cm, "cktsls %s basis=%s size=%d (and %d, or %d, not %d) requested=%d seed=%llu islands=%d time=%.3fs%s", o.spec.c_str(),
             o.basis.c_str(), c.size(), c.count(AND), c.count(OR), c.count(NOT), s, (unsigned long long)o.seed, nI, el, symnote.c_str());
    printf("FOUND size=%d requested=%d basis=%s time=%.3f steps=%llu cand_evals=%llu steps_per_s=%.4g cand_per_s=%.4g seed=%llu island=%d rounds=%ld\n",
           c.size(), s, o.basis.c_str(), el, (unsigned long long)st, (unsigned long long)cd, st / el, cd / el, (unsigned long long)o.seed, winner, rounds);
    write_circuit(std::cout, c, cm);
    if (!o.out.empty()) save_circuit(o.out, c, cm);
    return 0;
  }
  printf("NOTFOUND (no proof of anything) requested=%d basis=%s best_cost=%u%s time=%.3f steps=%llu cand_evals=%llu steps_per_s=%.4g cand_per_s=%.4g seed=%llu rounds=%ld swaps=%.2f%s\n",
         s, o.basis.c_str(), gb, views[0].sampled ? "(sample)" : "", el, (unsigned long long)st, (unsigned long long)cd, st / el, cd / el,
         (unsigned long long)o.seed, rounds, sw ? (double)swo / sw : 0.0, views[0].sampled ? (" cex=" + std::to_string(cx)).c_str() : "");
  if (!o.bestfile.empty() && !isl[gbi].bestGL.op.empty()) {
    const GL& g = isl[gbi].bestGL;
    Circuit c; c.N = sp.N;
    for (size_t j = 0; j < g.op.size(); j++) { Gate q; q.op = (Op)g.op[j]; q.a = g.fa[j]; q.b = g.fb[j]; q.nin = g.op[j] == NOT ? 1 : 2; c.gates.push_back(q); }
    // outputs: best wire per output on all points
    std::vector<u64> buf; eval(sp, c, buf);
    size_t wrongTot = 0;
    for (int k = 0; k < sp.K; k++) {
      size_t bw = 0, bd = ~size_t(0);
      for (size_t w = 0; w < (size_t)c.N + c.gates.size(); w++) {
        size_t d = 0;
        for (size_t i = 0; i < sp.W; i++) d += pc((buf[w * sp.W + i] ^ sp.tgt[k][i]) & sp.care[k][i]);
        if (d < bd) { bd = d; bw = w; }
      }
      c.outs.push_back((int)bw); wrongTot += bd;
    }
    save_circuit(o.bestfile, c, "cktsls BEST-SO-FAR, NOT CORRECT: wrong on " + std::to_string(wrongTot) + " (output,point) pairs");
  }
  return 1;
}

void usage() {
  std::cerr <<
    "usage: cktsls SPEC --basis ao|aon -s GATES [-j T] [--time S] [--seed X] [-o OUT.ckt] [--init IN.ckt]\n"
    "  stochastic search (parallel tempering over gate heat-bath moves) for a circuit with at most GATES gates.\n"
    "  HEURISTIC: exit 0 + verified circuit on stdout when found; exit 1 = nothing found (proves nothing).\n"
    "  -j T            threads (default $PNP_THREADS or 1); one island per thread unless --islands\n"
    "  --islands I     number of independent PT islands (default T). Results depend on seed and I only, not on T\n"
    "  --replicas R    temperatures per island (default 8);  --tmin x --tmax y  ladder ends (default 0.03 .. calibrated)\n"
    "  --noadapt       keep the ladder geometric (default: interior temperatures adapt to equalise exchange rates)\n"
    "  --ladder        print temperatures, mean cost and exchange rates of island 0 at the end\n"
    "  --sweep n       heat-bath steps per replica between exchange attempts (default max(4, GATES))\n"
    "  --sample S      evaluate on S sampled points + counterexamples (default: all points if <= 4096, else 1024)\n"
    "  --takeover m    0 never, 1 only for dead gates, 2 always (default 2 if outputs <= 2 else 1)\n"
    "  --init IN.ckt   start every replica from IN (random gates deleted / padded to reach GATES)\n"
    "  --best F.ckt    on failure, save the best (incorrect) state for a later --init\n"
    "  --migrate n     every n rounds copy the best island's best state into the others (default off)\n"
    "  --sym PERM      symmetric ansatz: only circuits invariant under the input permutation PERM, given as cycles\n"
    "                  \"(0 1)(2 3)\" or as an image list; --fixed F = number of self-symmetric gates (default: every\n"
    "                  feasible F, one per island, and at least that many islands)\n"
    "  --shape SPS[:k] typed layers: ORs over inputs, then k ANDs of those, then ORs of the products (PSP = dual);\n"
    "                  layer sizes GATES-2k+K, k, k-K for K outputs, or explicit SPS:a,b,c. Without :k every feasible\n"
    "                  k gets an island. A restriction of the search space (not combinable with --sym / --init)\n"
    "  --rounds n      stop after n rounds (deterministic stop);  --time S  wall limit (default 60)\n"
    "  --noprune       keep dead gates in the output;  --selfcheck  debug;  -q quiet\n";
}

}  // namespace

int main(int argc, char** argv) {
  Opts o;
  o.T = std::getenv("PNP_THREADS") ? atoi(std::getenv("PNP_THREADS")) : 1;
  std::vector<std::string> posa;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto nx = [&]() -> const char* { if (i + 1 >= argc) { usage(); exit(2); } return argv[++i]; };
    if (a == "--basis") o.basis = nx();
    else if (a == "-s") o.s = atoi(nx());
    else if (a == "-j") o.T = atoi(nx());
    else if (a == "--time") o.tlim = atof(nx());
    else if (a == "--seed") o.seed = strtoull(nx(), nullptr, 10);
    else if (a == "-o") o.out = nx();
    else if (a == "--init") o.init = nx();
    else if (a == "--best") o.bestfile = nx();
    else if (a == "--islands") { o.islands = atoi(nx()); o.islandsGiven = true; }
    else if (a == "--replicas") o.R = atoi(nx());
    else if (a == "--tmin") o.tmin = atof(nx());
    else if (a == "--tmax") o.tmax = atof(nx());
    else if (a == "--hotfrac") o.hotfrac = atof(nx());
    else if (a == "--sweep") o.sweep = atoi(nx());
    else if (a == "--sample") o.sample = atol(nx());
    else if (a == "--takeover") o.takeover = atoi(nx());
    else if (a == "--migrate") o.migrate = atoi(nx());
    else if (a == "--sym") o.sym = nx();
    else if (a == "--shape") o.shape = nx();
    else if (a == "--fixed") o.fixed = atoi(nx());
    else if (a == "--sym-slow") o.symSlow = true;
    else if (a == "--sym-debug") g_symdebug = true;
    else if (a == "--rounds") o.rounds = atol(nx());
    else if (a == "--noprune") o.noprune = true;
    else if (a == "--selfcheck") o.selfcheck = true;
    else if (a == "--ladder") o.ladder = true;
    else if (a == "--noadapt") o.noadapt = true;
    else if (a == "-q") o.quiet = true;
    else if (a == "-h" || a == "--help") { usage(); return 2; }
    else posa.push_back(a);
  }
  if (posa.size() != 1 || o.s < 1 || (o.basis != "ao" && o.basis != "aon")) { usage(); return 2; }
  o.spec = posa[0];
  if (o.T < 1) o.T = 1;
  if (o.R < 1) o.R = 1;
  if (o.islands < 1) o.islands = o.T;
  Spec sp = load_spec(o.spec);
  if (sp.N < 2) die("need at least 2 inputs");
  if (sp.N + o.s > 4000) die("too many wires");
  long S = o.sample >= 0 ? o.sample : (sp.P <= 4096 ? 0 : 1024);
  if (S >= (long)sp.P) S = 0;
  std::vector<View> views(o.islands);
  for (int i = 0; i < o.islands; i++) {
    if (S == 0) views[i].all(sp);
    else { u64 z = o.seed * 0x2545f4914f6cdd1dULL + (u64)i * 977 + 7; Rng r(Rng::splitmix(z)); views[i].sample(sp, (size_t)S, r); }
  }
  if (!o.shape.empty()) {
    // --shape SPS[:k] | PSP[:k]: sum-product-sum (or its dual) with k products: nS = GATES - 2k + 1 first-layer gates
    // reading inputs / first-layer gates, k products of those, k - 1 top gates combining products.
    static std::vector<ShapeCfg> shs;
    if (!o.sym.empty()) die("--shape and --sym cannot be combined");
    std::string kind = o.shape.substr(0, 3);
    if (kind != "SPS" && kind != "PSP") die("--shape: use SPS[:k] or PSP[:k]");
    // counts per island: SPS:k -> k products, k - K top gates (K outputs), GATES - 2k + K first-layer gates;
    // SPS:a,b,c -> explicit (a first-layer, b products, c top gates); bare SPS -> every feasible k, one per island.
    std::vector<std::array<int, 3>> cnt;
    const int K = sp.K;
    auto byK = [&](int k) { return std::array<int, 3>{o.s - 2 * k + K, k, k - K}; };
    if (o.shape.size() > 4 && o.shape[3] == ':') {
      int x = 0, y = 0, z = 0;
      int got = sscanf(o.shape.c_str() + 4, "%d,%d,%d", &x, &y, &z);
      if (got == 3) cnt.push_back({x, y, z});
      else if (got == 1) cnt.push_back(byK(x));
      else die("--shape: use SPS:k or SPS:a,b,c");
    } else for (int k = std::max(2, K); o.s - 2 * k + K >= 0; k++) cnt.push_back(byK(k));
    if (cnt.empty()) die("--shape: GATES too small");
    for (auto& c : cnt) if (c[0] < 0 || c[1] < 1 || c[2] < 0 || c[0] + c[1] + c[2] != o.s) die("--shape: layer sizes must be >= 0 and add up to GATES");
    if (o.islands < (int)cnt.size() && !o.islandsGiven) { o.islands = (int)cnt.size(); views.resize(o.islands, views[0]); }
    shs.resize(o.islands);
    for (int i = 0; i < o.islands; i++) {
      auto& c = cnt[i % cnt.size()];
      shs[i].nS = c[0]; shs[i].nP = c[1]; shs[i].nT = c[2]; shs[i].dual = kind == "PSP";
      views[i].shape = &shs[i];
    }
    if (!o.quiet) { std::cerr << "cktsls: shape " << kind << ", products per island:"; for (int i = 0; i < o.islands; i++) std::cerr << " " << shs[i].nP; std::cerr << "\n"; }
  }
  if (!o.sym.empty()) {
    static std::vector<SymCfg> scs;
    SymCfg sc;
    sc.sigma = parsePerm(o.sym, sp.N);
    sc.slow = o.symSlow;
    sc.r = permOrder(sc.sigma);
    if (sc.r < 2) die("--sym: the permutation is the identity");
    if (S != 0) die("--sym needs all points (no --sample)");
    std::vector<int> fvals;
    if (o.fixed >= 0) {
      if (o.fixed > o.s || (o.s - o.fixed) % sc.r) die("--sym: GATES - fixed must be a multiple of the order of the permutation");
      fvals.push_back(o.fixed);
    } else {  // auto: every feasible number of fixed gates, one per island (round robin)
      int nfixin = 0, n2 = 0;
      for (int i = 0; i < sp.N; i++) { if (sc.sigma[i] == i) nfixin++; else if (sc.sigma[sc.sigma[i]] == i) n2++; }
      bool canFix = sc.r == 2 || n2 > 0 || nfixin >= 2 || (o.basis == "aon" && nfixin >= 1);
      for (int F = o.s % sc.r; F <= o.s; F += sc.r) if (F == 0 || canFix) fvals.push_back(F);
      if (fvals.empty()) die("--sym: no feasible number of fixed gates for this permutation and GATES");
      if (o.islands < (int)fvals.size() && !o.islandsGiven) { o.islands = (int)fvals.size(); views.resize(o.islands, views[0]); }
    }
    scs.resize(o.islands);
    for (int i = 0; i < o.islands; i++) { scs[i] = sc; scs[i].fixed = fvals[i % fvals.size()]; views[i].sym = &scs[i]; }
    if (!specInvariant(sp, sc.sigma)) std::cerr << "cktsls: WARNING: the spec is NOT invariant under --sym; a symmetric circuit cannot compute it\n";
    else if (!o.quiet) {
      std::cerr << "cktsls: symmetric ansatz, order " << sc.r << ", fixed gates per island:";
      for (int i = 0; i < o.islands; i++) std::cerr << " " << scs[i].fixed;
      std::cerr << "\n";
    }
    switch (views[0].W) {
      case 1: return runSearch<SymReplica<1>>(sp, o, views);
      case 2: return runSearch<SymReplica<2>>(sp, o, views);
      default: return runSearch<SymReplica<0>>(sp, o, views);
    }
  }
  switch (views[0].W) {
    case 1: return runSearch<Replica<1>>(sp, o, views);
    case 2: return runSearch<Replica<2>>(sp, o, views);
    case 4: return runSearch<Replica<4>>(sp, o, views);
    case 8: return runSearch<Replica<8>>(sp, o, views);
    default: return runSearch<Replica<0>>(sp, o, views);
  }
}
