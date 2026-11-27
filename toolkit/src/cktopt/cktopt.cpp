// cktopt — multi-threaded circuit shrinker that exploits don't-cares (heuristic; output always re-verified).
//   cktopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X] [--target SIZE] ...
// Every wire is a P-bit column over the spec's cared points; all reasoning is exact bit-parallel simulation.
// See docs/cktopt.md for the move set and guarantees.
#include "../../include/ckt.hpp"
#include <algorithm>
#include <chrono>
#include <climits>
#include <cmath>
#include <mutex>
#include <thread>
#include <unordered_map>

using namespace pnp;
typedef uint8_t u8;

namespace {

struct Rng {
  u64 s;
  explicit Rng(u64 seed = 1) : s(seed * 0x9E3779B97F4A7C15ull + 0x1234567ull) { next(); next(); }
  u64 next() {
    u64 z = (s += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
  }
  uint32_t below(uint32_t n) { return n ? (uint32_t)(((next() >> 32) * (u64)n) >> 32) : 0; }
  double unif() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
  template <class T> void shuffle(std::vector<T>& v) {
    for (size_t i = v.size(); i > 1; i--) std::swap(v[i - 1], v[below((uint32_t)i)]);
  }
};

enum : u8 { K_AND = 0, K_OR = 1, K_NOT = 2, K_IN = 3, K_C0 = 4, K_C1 = 5, K_FREE = 6 };

struct Params {
  bool aon = true;        // NOT gates may be created
  int level = 5;          // 1 cleanup, 2 +0-resub with observability, 3 +k-resub covers, 4 +2-level terms, 5 +sideways/Paar
  int maxTerms = 5;       // max terms in an OR/AND cover
  long dfsBudget = 400;   // DFS nodes per cover search
  u64 dfsWords = 60000;   // word operations per cover search
  int branchMax = 10;     // candidates tried per DFS branch point
  int pairCap = 48;
  int pairEvery = 12;
  int sideMode = 0;       // tie-breaking of size-neutral rewrites: 0 random, 1 prefer popular wires, 2 = 1 + reject unpopular
  double sideTemp = 2.0;
  double rar = 0.0;       // redundancy-addition trials per pass, as a fraction of the gate count
  int rarRegion = 48;     // gates revisited after an addition
  double rarNeutral = 0.3; // probability of keeping a size-neutral addition/removal
  double shareWork = 4e7; // work units of one set-space sharing run at 1600+ gates, scaled down quadratically below (0 = off)
  int shareGroup = 4;     // terminals re-covered together
  double shareRepair = 0;    // fraction of sharing trials that exchange partners between two product gates
  int sharePolish = 8;    // re-cover trials after such an exchange before it is judged
  double shareTemp = 0;   // > 0: exchanges that grow the forest by d are kept with probability exp(-d/temp); best state is returned     // 2-level terms are tried on one visit in pairEvery       // wires considered per branch point for 2-level terms
  bool debug = false;
};

struct Stats {
  // gates removed / moves accepted, by move type
  long gConst = 0, gRes0 = 0, gNot = 0, gOr = 0, gAnd = 0, gPaar = 0, gTwo = 0;
  long aConst = 0, aRes0 = 0, aNot = 0, aOr = 0, aAnd = 0, aPaar = 0, aSide = 0, aTwo = 0;
  long gShare = 0, aShare = 0, aRepair = 0;
  long tries = 0, gRar = 0, aRar = 0, aRarSide = 0, rarTrials = 0, rarCands = 0;
  void add(const Stats& o) {
    gConst += o.gConst; gRes0 += o.gRes0; gNot += o.gNot; gOr += o.gOr; gAnd += o.gAnd; gPaar += o.gPaar; gTwo += o.gTwo;
    aConst += o.aConst; aRes0 += o.aRes0; aNot += o.aNot; aOr += o.aOr; aAnd += o.aAnd; aPaar += o.aPaar; aSide += o.aSide;
    aTwo += o.aTwo; tries += o.tries;
    gShare += o.gShare; aShare += o.aShare; aRepair += o.aRepair;
    gRar += o.gRar; aRar += o.aRar; aRarSide += o.aRarSide; rarTrials += o.rarTrials; rarCands += o.rarCands;
  }
};

struct Sol {
  int form = -1;   // K_OR / K_AND
  int k = 0;       // number of terms
  int w[8];        // term wire
  int w2[8];       // second wire of a 2-level term (opposite op), or -1
  u8 inv[8];       // term is NOT w (costs one gate)
  int gain = INT_MIN;
};

struct Net {
  const Spec* sp = nullptr;
  int N = 0, K = 0;
  size_t W = 0;
  u64 lm = 0;
  int C0 = 0, C1 = 0;
  int cap = 0, nextid = 0;
  std::vector<u8> kind;
  std::vector<int> fa, fb, ref;
  std::vector<std::vector<int>> fo;
  std::vector<u64> col;
  std::vector<int> outs;
  std::vector<int> freeids;
  std::unordered_map<u64, int> strash;
  int ngates = 0;
  std::vector<int> order, pos;
  bool orderDirty = true;
  bool broken = false;
  u64 simw = 0, scanw = 0;   // word operations: gate evaluation / candidate scanning

  // scratch
  std::vector<u64> alt, tmp, obs, on, off;
  std::vector<int> stamp, tstamp, qstamp, fwd, fwdstamp;
  int cur = 0, tcur = 0, qcur = 0, fcur = 0;
  std::vector<int> heap, st, trail, dirty, created, tmpfo;
  std::vector<std::pair<int, int>> wl;
  std::vector<int> nzOn, nzOff, nzAll;
  std::vector<int> eq, up, um, nup, neq, cand;
  std::vector<u8> wflag;
  std::vector<int> wfs;
  // transposed index: for each point, the set of wires that are 1 there (TW words per point)
  bool useT = false;
  static inline bool indexAllowed = true;   // --no-index: always scan wires directly (used for testing / huge specs)
  size_t TW = 0;
  std::vector<u64> T, aliveB, accC, accF, tfoB, ptDone;
  std::vector<int> fstamp, slotStamp, fstamp2, tfiS;
  int icur = 0;
  std::vector<u64> rarZ, offQ;
  int offQstamp = 0;
  int scur2 = 0;
  std::vector<u8> feas;
  // cover search scratch
  std::vector<int> cw, cw2;
  std::vector<u8> cinv;
  std::vector<u64> cov, R;
  std::vector<int> tw;   // active word indices of the cover target
  std::vector<int> vw;   // active word indices of the avoid set

  static u64 key(u8 op, int a, int b) { return ((u64)op << 60) | ((u64)(uint32_t)a << 30) | (u64)(uint32_t)b; }
  u64* C(int id) { return &col[(size_t)id * W]; }
  const u64* C(int id) const { return &col[(size_t)id * W]; }
  bool isGate(int id) const { return kind[id] <= K_NOT; }
  u64 visits = 0;
  u64 totalWork() const { return simw + scanw + visits * 3000; }   // deterministic work measure (a visit has fixed overhead)

  void resizeAll(int ncap) {
    cap = ncap;
    kind.resize(cap, K_FREE); fa.resize(cap, -1); fb.resize(cap, -1); ref.resize(cap, 0); fo.resize(cap);
    col.resize((size_t)cap * W, 0); alt.resize((size_t)cap * W, 0);
    stamp.resize(cap, 0); tstamp.resize(cap, 0); qstamp.resize(cap, 0); fwd.resize(cap, -1); fwdstamp.resize(cap, 0);
    pos.resize(cap, -1);
    wflag.resize(cap, 0); wfs.resize(cap, 0); fstamp.resize(cap, 0); slotStamp.resize(cap, 0); fstamp2.resize(cap, 0); tfiS.resize(cap, 0); feas.resize(cap, 0);
    if (useT && (size_t)(cap + 63) / 64 != TW) rebuildT();
  }
  void tFlip(int id, const u64* diff) {
    const u64 bit = u64(1) << (id & 63);
    const size_t off_ = (size_t)(id >> 6);
    for (size_t w = 0; w < W; w++) {
      u64 x = diff[w];
      while (x) { size_t p_ = w * 64 + __builtin_ctzll(x); x &= x - 1; T[p_ * TW + off_] ^= bit; }
    }
  }
  void rebuildT() {
    TW = (size_t)(cap + 63) / 64;
    T.assign(sp->P * TW, 0);
    aliveB.assign(TW, 0); accC.assign(TW, 0); accF.assign(TW, 0); tfoB.assign(TW, 0);
    for (int id = 0; id < nextid; id++) if (kind[id] != K_FREE && id != C0 && id != C1) {
      tFlip(id, C(id));
      aliveB[id >> 6] |= u64(1) << (id & 63);
    }
  }
  void init(const Spec* s, int gateHint) {
    sp = s; N = s->N; K = s->K; W = s->W; lm = s->lastmask();
    C0 = N; C1 = N + 1; nextid = N + 2;
    resizeAll(N + 2 + std::max(64, gateHint + gateHint / 2 + 64));
    for (int i = 0; i < N; i++) { kind[i] = K_IN; std::memcpy(C(i), s->in[i].data(), W * 8); }
    kind[C0] = K_C0; kind[C1] = K_C1;
    for (size_t w = 0; w < W; w++) { C(C0)[w] = 0; C(C1)[w] = ~u64(0); }
    C(C1)[W - 1] = lm;
    tmp.assign(W, 0); obs.assign(W, 0); on.assign(W, 0); off.assign(W, 0);
    outs.assign(K, C0);
    ref[C0] += K;
    ngates = 0; orderDirty = true; broken = false;
    strash.clear(); freeids.clear();
    useT = indexAllowed && (double)s->P * ((cap + 63) / 64) * 8.0 <= 96e6;
    if (useT) rebuildT();
  }
  int alloc() {
    if (!freeids.empty()) { int id = freeids.back(); freeids.pop_back(); return id; }
    if (nextid == cap) resizeAll(cap + cap / 2 + 64);
    return nextid++;
  }
  void computeInto(u64* o, u8 op, const u64* a, const u64* b) {
    if (op == K_NOT) { for (size_t w = 0; w < W; w++) o[w] = ~a[w]; o[W - 1] &= lm; }
    else if (op == K_AND) for (size_t w = 0; w < W; w++) o[w] = a[w] & b[w];
    else for (size_t w = 0; w < W; w++) o[w] = a[w] | b[w];
    simw += W;
  }
  int create(u8 op, int a, int b) {
    int id = alloc();
    kind[id] = op; fa[id] = a; fb[id] = op == K_NOT ? -1 : b; ref[id] = 0; fo[id].clear();
    fo[a].push_back(id); ref[a]++;
    if (op != K_NOT) { fo[b].push_back(id); ref[b]++; }
    strash[key(op, a, op == K_NOT ? 0 : b)] = id;
    computeInto(C(id), op, C(a), op == K_NOT ? nullptr : C(b));
    if (useT) { tFlip(id, C(id)); aliveB[id >> 6] |= u64(1) << (id & 63); }
    ngates++; orderDirty = true;
    return id;
  }
  // If (op,a,b) reduces to an existing node return it; else -1 with (a,b) canonical.
  int lookup(u8 op, int& a, int& b) const {
    if (op == K_NOT) {
      if (a == C0) return C1;
      if (a == C1) return C0;
      if (kind[a] == K_NOT) return fa[a];
      auto it = strash.find(key(op, a, 0));
      return it == strash.end() ? -1 : it->second;
    }
    if (a == b) return a;
    if (a > b) std::swap(a, b);
    if (op == K_AND) {
      if (a == C0 || b == C0) return C0;
      if (a == C1) return b;
      if (b == C1) return a;
    } else {
      if (a == C1 || b == C1) return C1;
      if (a == C0) return b;
      if (b == C0) return a;
    }
    if ((kind[a] == K_NOT && fa[a] == b) || (kind[b] == K_NOT && fa[b] == a)) return op == K_AND ? C0 : C1;
    auto it = strash.find(key(op, a, b));
    return it == strash.end() ? -1 : it->second;
  }
  int mk(u8 op, int a, int b = -1) {
    int r = lookup(op, a, b);
    if (r >= 0) return r;
    r = create(op, a, b);
    created.push_back(r);
    return r;
  }
  void eraseKey(int x) {
    auto it = strash.find(key(kind[x], fa[x], kind[x] == K_NOT ? 0 : fb[x]));
    if (it != strash.end() && it->second == x) strash.erase(it);
  }
  static void removeOne(std::vector<int>& v, int x) {
    for (size_t i = 0; i < v.size(); i++) if (v[i] == x) { v[i] = v.back(); v.pop_back(); return; }
  }
  void kill(int g) {   // g: gate with no references; removes it and everything that dies with it
    std::vector<int> ks; ks.push_back(g);
    while (!ks.empty()) {
      int x = ks.back(); ks.pop_back();
      if (!isGate(x) || ref[x] != 0) continue;
      eraseKey(x);
      int ins[2] = {fa[x], kind[x] == K_NOT ? -1 : fb[x]};
      kind[x] = K_FREE; ngates--; freeids.push_back(x); orderDirty = true;
      if (useT) { tFlip(x, C(x)); aliveB[x >> 6] &= ~(u64(1) << (x & 63)); }
      for (int f : ins) if (f >= 0) {
        removeOne(fo[f], x); ref[f]--;
        if (ref[f] == 0 && isGate(f)) ks.push_back(f);
      }
    }
  }
  void sweep() {
    for (int id = N + 2; id < nextid; id++) if (isGate(id) && ref[id] == 0) kill(id);
  }
  void ensureOrder() {
    if (!orderDirty) return;
    order.clear();
    for (int id = N + 2; id < nextid; id++) pos[id] = -1;
    for (int s = N + 2; s < nextid; s++) {
      if (!isGate(s) || pos[s] >= 0) continue;
      st.clear(); st.push_back(s);
      while (!st.empty()) {
        int x = st.back();
        if (pos[x] >= 0) { st.pop_back(); continue; }
        bool ready = true;
        int a = fa[x];
        if (isGate(a) && pos[a] < 0) { st.push_back(a); ready = false; }
        if (kind[x] != K_NOT) { int b = fb[x]; if (isGate(b) && pos[b] < 0) { st.push_back(b); ready = false; } }
        if (ready) { pos[x] = (int)order.size(); order.push_back(x); st.pop_back(); }
        if (st.size() > (size_t)4 * cap + 16) die("internal: cycle in network");
      }
    }
    orderDirty = false;
  }
  void hpush(int f) {
    if (qstamp[f] == qcur) return;
    qstamp[f] = qcur;
    heap.push_back(pos[f]);
    std::push_heap(heap.begin(), heap.end(), std::greater<int>());
  }
  int hpop() {
    std::pop_heap(heap.begin(), heap.end(), std::greater<int>());
    int p = heap.back(); heap.pop_back();
    return order[p];
  }
  // obs := points where flipping g changes some cared output bit.
  void computeObs(int g) {
    ensureOrder();
    cur++; qcur++;
    u64* ag = &alt[(size_t)g * W];
    const u64* cg = C(g);
    for (size_t w = 0; w < W; w++) ag[w] = ~cg[w];
    ag[W - 1] &= lm;
    stamp[g] = cur;
    heap.clear();
    for (int f : fo[g]) hpush(f);
    while (!heap.empty()) {
      int f = hpop();
      int a = fa[f];
      const u64* pa = stamp[a] == cur ? &alt[(size_t)a * W] : C(a);
      u64* o = &alt[(size_t)f * W];
      const u64* c = C(f);
      u64 d = 0;
      if (kind[f] == K_NOT) { for (size_t w = 0; w < W; w++) { o[w] = ~pa[w]; } o[W - 1] &= lm; for (size_t w = 0; w < W; w++) d |= o[w] ^ c[w]; }
      else {
        int b = fb[f];
        const u64* pb = stamp[b] == cur ? &alt[(size_t)b * W] : C(b);
        if (kind[f] == K_AND) for (size_t w = 0; w < W; w++) { o[w] = pa[w] & pb[w]; d |= o[w] ^ c[w]; }
        else for (size_t w = 0; w < W; w++) { o[w] = pa[w] | pb[w]; d |= o[w] ^ c[w]; }
      }
      simw += W;
      if (!d) continue;
      stamp[f] = cur;
      for (int h : fo[f]) hpush(h);
    }
    for (size_t w = 0; w < W; w++) obs[w] = 0;
    for (int k = 0; k < K; k++) {
      int o = outs[k];
      if (stamp[o] != cur) continue;
      const u64* a = &alt[(size_t)o * W];
      const u64* c = C(o);
      const u64* care = sp->care[k].data();
      for (size_t w = 0; w < W; w++) obs[w] |= (a[w] ^ c[w]) & care[w];
    }
  }
  void markTFO(int g) {
    tcur++;
    st.clear(); st.push_back(g); tstamp[g] = tcur;
    if (useT) { std::fill(tfoB.begin(), tfoB.end(), 0); tfoB[g >> 6] |= u64(1) << (g & 63); }
    while (!st.empty()) {
      int x = st.back(); st.pop_back();
      for (int h : fo[x]) if (tstamp[h] != tcur) {
        tstamp[h] = tcur; st.push_back(h);
        if (useT) tfoB[h >> 6] |= u64(1) << (h & 63);
      }
    }
  }
  // number of gates that die if g is removed while the wires in keep[] stay referenced
  // leafScore (optional): sum of the remaining reference counts of the wires the freed gates were reading
  int freedIf(int g, const int* keep, int nk, int* leafScore = nullptr) {
    for (int i = 0; i < nk; i++) ref[keep[i]]++;
    int cnt = 0;
    st.clear(); st.push_back(g); trail.clear();
    int ls = 0;
    while (!st.empty()) {
      int x = st.back(); st.pop_back(); cnt++;
      int ins[2] = {fa[x], kind[x] == K_NOT ? -1 : fb[x]};
      for (int f : ins) if (f >= 0) {
        if (isGate(f)) { ref[f]--; trail.push_back(f); if (ref[f] == 0) st.push_back(f); }
        else ls += ref[f] - 1;
      }
    }
    if (leafScore) {
      scur2++;
      for (int f : trail) if (ref[f] > 0 && fstamp2[f] != scur2) { fstamp2[f] = scur2; ls += ref[f]; }
      *leafScore = ls;
    }
    for (int f : trail) ref[f]++;
    for (int i = 0; i < nk; i++) ref[keep[i]]--;
    return cnt;
  }
  int resolve(int y) const {
    while (kind[y] == K_FREE && fwdstamp[y] == fcur && fwd[y] >= 0) y = fwd[y];
    return y;
  }
  bool outputsOK() const {
    for (int k = 0; k < K; k++) {
      const u64* c = C(outs[k]);
      const u64* t = sp->tgt[k].data();
      const u64* care = sp->care[k].data();
      for (size_t w = 0; w < W; w++) if ((c[w] ^ t[w]) & care[w]) return false;
    }
    return true;
  }
  // Redirect every use of g to r (r must not depend on g), remove what dies, restore structural hashing,
  // re-simulate the affected cone and check the outputs.
  bool replace(int g, int r, int skip = -1) {
    fcur++;
    orderDirty = true;
    wl.clear(); wl.push_back({g, r}); dirty.clear();
    for (size_t head = 0; head < wl.size(); head++) {
      int x = wl[head].first, y = resolve(wl[head].second);
      if (kind[x] == K_FREE) continue;
      if (x == y) continue;
      if (kind[y] == K_FREE) {   // the node x was equal to has died: x simply stays, back in the hash table
        int a = fa[x], b = kind[x] == K_NOT ? -1 : fb[x];
        int t = lookup(kind[x], a, b);
        if (t >= 0 && t != x) { wl.push_back({x, t}); continue; }
        if (kind[x] != K_NOT) { fa[x] = a; fb[x] = b; }
        strash[key(kind[x], fa[x], kind[x] == K_NOT ? 0 : fb[x])] = x;
        dirty.push_back(x);
        continue;
      }
      for (int k = 0; k < K; k++) if (outs[k] == x) { outs[k] = y; ref[x]--; ref[y]++; }
      tmpfo = fo[x];
      fo[x].clear();
      for (int f : tmpfo) {
        if (f == skip && x == g) { fo[x].push_back(f); continue; }   // (insertion above g: the new node keeps reading g)
        ref[x]--;
        u8 op = kind[f];
        eraseKey(f);
        if (fa[f] == x) fa[f] = y; else fb[f] = y;
        fo[y].push_back(f); ref[y]++;
        int a = fa[f], b = op == K_NOT ? -1 : fb[f];
        int t = lookup(op, a, b);
        if (t >= 0 && t != x && t != f) { wl.push_back({f, t}); continue; }
        if (op != K_NOT) { fa[f] = a; fb[f] = b; }
        strash[key(op, fa[f], op == K_NOT ? 0 : fb[f])] = f;   // (t == x: f takes over the dying node's slot)
        dirty.push_back(f);
      }
      fwd[x] = y; fwdstamp[x] = fcur;
      if (isGate(x) && ref[x] == 0) kill(x);
    }
    return resim();
  }
  bool resim() {
    ensureOrder();
    qcur++; heap.clear();
    for (int f : dirty) if (isGate(f)) hpush(f);
    while (!heap.empty()) {
      int f = hpop();
      computeInto(tmp.data(), kind[f], C(fa[f]), kind[f] == K_NOT ? nullptr : C(fb[f]));
      u64* c = C(f);
      u64 d = 0;
      for (size_t w = 0; w < W; w++) { u64 x = c[w] ^ tmp[w]; d |= x; c[w] = tmp[w]; tmp[w] = x; }
      if (d) { if (useT) tFlip(f, tmp.data()); for (int h : fo[f]) hpush(h); }
    }
    if (!outputsOK()) { broken = true; return false; }
    return true;
  }

  // ---------------------------------------------------------------- import / export
  void fromCircuit(const Circuit& c) {
    std::vector<int> wid((size_t)c.N + c.gates.size(), C0);
    for (int i = 0; i < c.N; i++) wid[i] = i;
    for (size_t j = 0; j < c.gates.size(); j++) {
      const Gate& g = c.gates[j];
      int curw = c.N + (int)j;
      auto opnd = [&](int i) { return (i >= 0 && i < curw) ? wid[i] : C0; };
      int r;
      if (g.op == NOT) r = g.nin == 0 ? C1 : mk(K_NOT, opnd(g.a));
      else if (g.nin == 0) r = g.op == AND ? C1 : C0;
      else if (g.nin == 1) r = opnd(g.a);
      else r = mk(g.op == AND ? K_AND : K_OR, opnd(g.a), opnd(g.b));
      wid[curw] = r;
    }
    for (int k = 0; k < K; k++) {
      int o = c.outs[k];
      int w = (o >= 0 && (size_t)o < wid.size()) ? wid[o] : C0;
      ref[outs[k]]--; outs[k] = w; ref[w]++;
    }
    sweep();
    created.clear();
  }
  Circuit toCircuit() {
    ensureOrder();
    Circuit c; c.N = N;
    std::vector<int> idx(cap, -1);
    for (int i = 0; i < N; i++) idx[i] = i;
    for (int g : order) {
      Gate q;
      q.op = kind[g] == K_AND ? AND : kind[g] == K_OR ? OR : NOT;
      q.nin = kind[g] == K_NOT ? 1 : 2;
      q.a = idx[fa[g]]; q.b = kind[g] == K_NOT ? 0 : idx[fb[g]];
      idx[g] = N + (int)c.gates.size();
      c.gates.push_back(q);
    }
    for (int k = 0; k < K; k++) {
      int o = outs[k];
      if (o == C0 || o == C1) {
        if (idx[o] < 0) { Gate q; q.op = o == C1 ? AND : OR; q.nin = 0; idx[o] = N + (int)c.gates.size(); c.gates.push_back(q); }
      }
      c.outs.push_back(idx[o]);
    }
    return c;
  }
  int sizeOut() const {   // gate count of the exported circuit (constants at outputs cost a gate)
    bool c0 = false, c1 = false;
    for (int o : outs) { c0 |= o == C0; c1 |= o == C1; }
    return ngates + c0 + c1;
  }
  // full consistency check (debug): structure, hash table, columns, outputs
  bool check(std::string& why) {
    ensureOrder();
    std::vector<int> r(cap, 0);
    for (int o : outs) r[o]++;
    int cnt = 0;
    std::vector<u64> t(W);
    for (int g : order) {
      cnt++;
      int a = fa[g], b = kind[g] == K_NOT ? -1 : fb[g];
      if (kind[a] == K_FREE || (b >= 0 && kind[b] == K_FREE)) { why = "fanin is dead"; return false; }
      if (isGate(a) && pos[a] >= pos[g]) { why = "order"; return false; }
      r[a]++; if (b >= 0) r[b]++;
      if (b >= 0 && a >= b) { why = "not canonical"; return false; }
      auto it = strash.find(key(kind[g], a, b < 0 ? 0 : b));
      if (it == strash.end() || it->second != g) { why = "strash"; return false; }
      u64 sv = simw; computeInto(t.data(), kind[g], C(a), b < 0 ? nullptr : C(b)); simw = sv;
      if (std::memcmp(t.data(), C(g), W * 8)) { why = "column stale at " + std::to_string(g); return false; }
    }
    if (cnt != ngates) { why = "ngates"; return false; }
    if ((int)strash.size() != ngates) { why = "strash size"; return false; }
    for (int id = 0; id < nextid; id++) if (kind[id] != K_FREE) {
      if (r[id] != ref[id]) { why = "ref of " + std::to_string(id); return false; }
      if (isGate(id) && ref[id] == 0) { why = "dangling gate"; return false; }
      int nf = 0; for (int o : outs) nf += o == id;
      if ((int)fo[id].size() + nf != ref[id]) { why = "fanout list of " + std::to_string(id); return false; }
    }
    if (!outputsOK()) { why = "outputs wrong"; return false; }
    return true;
  }

  // ---------------------------------------------------------------- cover search
  // Target bits T (active words tw), candidates with coverage rows in cov. Finds covers of T with <= maxTerms terms.
  int cvForm = 0, cvG = 0, cvM = 0, cvMaxTerms = 0, cvMinGain = 0, cvBranch = 0, cvNT = 0, cvMaxPc = 0;
  u64 cvWordLimit = 0, cvFlip = 0;
  bool cvViaIndex = false, cvLazy = false;
  long cvBudget = 0;
  int cvChosen[8];
  int cvTies = 0, cvSideMode = 0, cvBestScore = 0;
  Sol cvBest;
  Rng* cvRng = nullptr;
  const u64* cvT = nullptr;
  int scur = 0;

  // does wire w avoid the off-set of the current gate? (cached per visit)
  bool avoidsOff(int w) {
    if (fstamp[w] == tcur) return feas[w];
    if (useT) {   // quick reject: wires that are 1 on one of a few sampled off-points
      if (offQstamp != tcur) {
        offQstamp = tcur;
        offQ.assign(TW, 0);
        const int n = (int)nzOff.size();
        const int stride = std::max(1, n / 32);
        int steps = 0;
        for (int i = 0; i < n; i += stride, steps++) {
          int wi = nzOff[i];
          const u64* row = &T[((size_t)wi * 64 + __builtin_ctzll(off[wi])) * TW];
          for (size_t j = 0; j < TW; j++) offQ[j] |= row[j];
        }
        scanw += (u64)steps * TW;
      }
      if ((offQ[w >> 6] >> (w & 63)) & 1) { fstamp[w] = tcur; feas[w] = 0; return false; }
    }
    const u64* c = C(w);
    const int nOff = (int)nzOff.size();
    bool hit = false; int i = 0;
    for (; i < nOff; i++) { int wi = nzOff[i]; if (c[wi] & off[wi]) { hit = true; break; } }
    scanw += i + 1;
    fstamp[w] = tcur; feas[w] = !hit;
    return !hit;
  }
  void cvAddWire(int w, u8 inv) {
    if (!inv) { if (slotStamp[w] == scur) return; slotStamp[w] = scur; }
    const int nT = cvNT;
    const u64* c = C(w);
    const u64 f = inv ? ~cvFlip : cvFlip;
    size_t base = cov.size();
    cov.resize(base + nT);
    u64 any = 0;
    for (int i = 0; i < nT; i++) { u64 x = (c[tw[i]] ^ f) & cvT[tw[i]]; cov[base + i] = x; any |= x; }
    scanw += nT;
    if (!any) { cov.resize(base); return; }
    cw.push_back(w); cw2.push_back(-1); cinv.push_back(inv);
  }
  // lazy OR-form candidates: every wire that contains the point and avoids off
  void cvMaterialize(int ti, int b) {
    if ((ptDone[ti] >> b) & 1) return;
    ptDone[ti] |= u64(1) << b;
    if (cw.size() > 4000) return;
    const u64* row = &T[((size_t)tw[ti] * 64 + b) * TW];
    for (size_t j = 0; j < TW; j++) {
      u64 x = row[j] & aliveB[j] & ~tfoB[j];
      while (x) {
        int w = (int)(j * 64) + __builtin_ctzll(x); x &= x - 1;
        if (slotStamp[w] == scur) continue;
        if (avoidsOff(w)) cvAddWire(w, 0);
      }
    }
    scanw += TW;
  }
  void cvEval(int k, int extra) {
    int keep[16], nk = 0;
    for (int i = 0; i < k; i++) { keep[nk++] = cw[cvChosen[i]]; if (cw2[cvChosen[i]] >= 0) keep[nk++] = cw2[cvChosen[i]]; }
    int cost = k - 1 + extra;
    if (cvM - cost < std::max(cvMinGain, cvBest.gain)) return;
    if (k == 2 && extra == 0 && cvForm == kind[cvG]) {   // identical to the current gate
      int a = keep[0], b = keep[1];
      if ((a == fa[cvG] && b == fb[cvG]) || (a == fb[cvG] && b == fa[cvG])) return;
    }
    int ls = 0;
    int gain = freedIf(cvG, keep, nk, cvSideMode ? &ls : nullptr) - cost;
    if (gain < cvMinGain || gain < cvBest.gain) return;
    int score = 0;
    if (cvSideMode && gain == 0) { for (int i = 0; i < nk; i++) score += ref[keep[i]]; score -= ls; }
    if (gain == cvBest.gain) {
      if (score < cvBestScore) return;
      if (score == cvBestScore) { cvTies++; if (cvRng->below(cvTies) != 0) return; }
      else cvTies = 1;
    } else cvTies = 1;
    cvBestScore = score;
    cvBest.form = cvForm; cvBest.k = k; cvBest.gain = gain;
    for (int i = 0; i < k; i++) { int c = cvChosen[i]; cvBest.w[i] = cw[c]; cvBest.w2[i] = cw2[c]; cvBest.inv[i] = cinv[c]; }
  }
  static int termCost(int w2, u8 inv) { return (w2 >= 0 ? 1 : 0) + (inv ? 1 : 0); }
  void cvDfs(int d, int extra) {
    const int nT = cvNT;
    const u64* r = &R[(size_t)d * nT];
    bool zero = true;
    for (int i = 0; i < nT; i++) if (r[i]) { zero = false; break; }
    if (zero) { if (d > 0) cvEval(d, extra); return; }
    if (d == cvMaxTerms) return;
    if (cvM - (d + extra) < std::max(cvMinGain, cvBest.gain)) return;
    if (cvBudget-- <= 0 || scanw > cvWordLimit) { cvBudget = 0; return; }
    if (!cvLazy) {
      long rem = 0;
      for (int i = 0; i < nT; i++) rem += __builtin_popcountll(r[i]);
      if (rem > (long)(cvMaxTerms - d) * cvMaxPc) return;
    }
    // branch point: among a few uncovered points, the one covered by the fewest candidates
    int bw = -1, bb = 0, bcnt = INT_MAX;
    int start = cvRng->below(nT), samples = 0;
    const int maxSamples = cvLazy ? 3 : 5;
    for (int i = 0; i < nT && samples < maxSamples; i++) {
      int wi = start + i; if (wi >= nT) wi -= nT;
      u64 x = r[wi];
      if (!x) continue;
      samples++;
      int b = __builtin_ctzll(x);
      if (cvLazy) cvMaterialize(wi, b);
      const int nc = (int)cw.size();
      int cnt = 0;
      for (int c = 0; c < nc; c++) cnt += (cov[(size_t)c * nT + wi] >> b) & 1;
      scanw += nc / 8 + 1;
      if (cnt < bcnt) { bcnt = cnt; bw = wi; bb = b; }
      if (cnt == 0) break;
    }
    if (bcnt == 0 || bw < 0) return;
    const int nc = (int)cw.size();
    // candidates covering the branch point, best coverage first
    std::vector<std::pair<int, int>> L;
    L.reserve(bcnt);
    bool last = d == cvMaxTerms - 1;
    for (int c = 0; c < nc; c++) {
      const u64* cv = &cov[(size_t)c * nT];
      if (!((cv[bw] >> bb) & 1)) continue;
      int pc = 0; bool all = true;
      for (int i = 0; i < nT; i++) { pc += __builtin_popcountll(cv[i] & r[i]); if (r[i] & ~cv[i]) all = false; }
      scanw += nT;
      if (last && !all) continue;
      L.push_back({-(pc * 4 - termCost(cw2[c], cinv[c]) * 2) * 8 - (int)cvRng->below(8), c});
    }
    std::sort(L.begin(), L.end());
    int lim = std::min((int)L.size(), cvBranch);
    for (int i = 0; i < lim; i++) {
      int c = L[i].second;
      cvChosen[d] = c;
      const u64* cv = &cov[(size_t)c * nT];
      u64* rn = &R[(size_t)(d + 1) * nT];
      for (int j = 0; j < nT; j++) rn[j] = r[j] & ~cv[j];
      cvDfs(d + 1, extra + termCost(cw2[c], cinv[c]));
      if (cvBudget <= 0) return;
    }
  }
  // form K_OR: cover `on` with wires that avoid `off`.  form K_AND: kill `off` with wires that contain `on`.
  // In both cases a literal is e = col ^ flip, with flip = 0 for OR-form, ~0 for AND-form (and the reverse for NOT terms);
  // e must avoid V and covers e & T.
  void cover(int g, int M, u8 form, bool side, const Params& P, Rng& rng, Sol& best) {
    const u64* T_ = form == K_OR ? on.data() : off.data();
    const u64* V = form == K_OR ? off.data() : on.data();
    tw = form == K_OR ? nzOn : nzOff;
    vw = form == K_OR ? nzOff : nzOn;
    const int nT = (int)tw.size();
    if (!nT) return;
    int maxTerms = std::min({P.maxTerms, 8, M + (side ? 1 : 0)});
    if (maxTerms < 1) return;
    cw.clear(); cw2.clear(); cinv.clear(); cov.clear();
    cvFlip = form == K_OR ? 0 : ~u64(0); cvT = T_; cvNT = nT;
    cvLazy = cvViaIndex && form == K_OR;
    scur++;
    if (cvLazy) ptDone.assign(nT, 0);
    else for (int w : (form == K_OR ? up : um)) cvAddWire(w, 0);
    if (P.aon && form == K_OR) for (int w : nup) cvAddWire(w, 1);
    // 2-level terms: pairs (w1,w2) with e1 & e2 avoiding V, neither feasible alone. Built around uncovered points.
    if (P.level >= 4 && (M >= 2 || side) && rng.below(P.pairEvery) == 0) addPairTerms(g, form, T_, V, cvFlip, P, rng);
    cvMaxPc = 1 << 28;
    if (!cvLazy) {   // quick infeasibility test: the maxTerms largest candidates must be able to cover T
      if (cw.empty()) return;
      int tot = 0;
      for (int i = 0; i < nT; i++) tot += __builtin_popcountll(T_[tw[i]]);
      std::vector<int> pcs(cw.size());
      for (size_t c = 0; c < cw.size(); c++) { int pc = 0; for (int i = 0; i < nT; i++) pc += __builtin_popcountll(cov[c * nT + i]); pcs[c] = pc; }
      scanw += cw.size() * nT;
      std::sort(pcs.begin(), pcs.end(), std::greater<int>());
      long sum = 0;
      for (int i = 0; i < maxTerms && i < (int)pcs.size(); i++) sum += pcs[i];
      if (sum < tot) return;
      cvMaxPc = pcs[0];
    }
    R.assign((size_t)(maxTerms + 1) * nT, 0);
    for (int i = 0; i < nT; i++) R[i] = T_[tw[i]];
    cvForm = form; cvG = g; cvM = M; cvMaxTerms = maxTerms; cvMinGain = side ? 0 : 1; cvBranch = P.branchMax;
    cvBudget = P.dfsBudget; cvRng = &rng; cvWordLimit = scanw + P.dfsWords;
    cvBest = best; cvTies = best.gain > INT_MIN ? 1 : 0; cvSideMode = P.sideMode;
    cvDfs(0, 0);
    best = cvBest;
  }
  // Add AND-pair (OR-form) / OR-pair (AND-form) terms around a few target points.
  void addPairTerms(int g, u8 form, const u64* T_, const u64* V, u64 flip, const Params& P, Rng& rng) {
    const int nT = (int)tw.size();
    const int nV = (int)vw.size();
    // points not covered by any single candidate come first; then a few random target points
    std::vector<u64> un(nT);
    for (int i = 0; i < nT; i++) un[i] = T_[tw[i]];
    const int nc0 = (int)cw.size();
    for (int c = 0; c < nc0; c++) for (int i = 0; i < nT; i++) un[i] &= ~cov[(size_t)c * nT + i];
    int pts[3][2], np = 0;
    for (int pass = 0; pass < 2 && np < 2; pass++) {
      int start = rng.below(nT);
      for (int i = 0; i < nT && np < 2; i++) {
        int wi = start + i; if (wi >= nT) wi -= nT;
        u64 x = pass == 0 ? un[wi] : (T_[tw[wi]] & ~un[wi]);
        if (!x) continue;
        pts[np][0] = wi; pts[np][1] = __builtin_ctzll(x); np++;
      }
    }
    std::vector<int> X;
    std::vector<u64> ev;   // literal values restricted to the avoid-set words
    for (int q = 0; q < np; q++) {
      int wi = tw[pts[q][0]], bit = pts[q][1];
      X.clear();
      const u8 alone = form == K_OR ? 1 : 2;
      if (cvViaIndex) {
        const u64* row = &T[((size_t)wi * 64 + bit) * TW];
        for (size_t j = 0; j < TW; j++) {
          u64 x = (row[j] ^ flip) & aliveB[j] & ~tfoB[j];
          while (x) {
            int w = (int)(j * 64) + __builtin_ctzll(x); x &= x - 1;
            if (form == K_OR ? avoidsOff(w) : (wfs[w] == tcur && (wflag[w] & 2))) continue;
            X.push_back(w);
          }
        }
        scanw += TW;
      } else {
        for (int w : cand) {   // every wire outside the fanout cone that is not feasible alone
          if (!(wflag[w] & alone) && (((C(w)[wi] ^ flip) >> bit) & 1)) X.push_back(w);
        }
        scanw += cand.size() / 8 + 1;
      }
      if ((int)X.size() > P.pairCap) { rng.shuffle(X); X.resize(P.pairCap); }
      const int nx = (int)X.size();
      ev.resize((size_t)nx * nV);
      for (int i = 0; i < nx; i++) { const u64* c = C(X[i]); for (int j = 0; j < nV; j++) ev[(size_t)i * nV + j] = (c[vw[j]] ^ flip) & V[vw[j]]; }
      scanw += (u64)nx * nV;
      int added = 0;
      for (int i = 0; i < nx && added < 24; i++) for (int j = i + 1; j < nx && added < 24; j++) {
        const u64* a = &ev[(size_t)i * nV]; const u64* b = &ev[(size_t)j * nV];
        bool ok = true; int z = 0;
        for (; z < nV; z++) if (a[z] & b[z]) { ok = false; break; }
        scanw += z + 1;
        if (!ok) continue;
        const u64* ca = C(X[i]); const u64* cb = C(X[j]);
        size_t base = cov.size();
        cov.resize(base + nT);
        for (int t = 0; t < nT; t++) cov[base + t] = (ca[tw[t]] ^ flip) & (cb[tw[t]] ^ flip) & T_[tw[t]];
        cw.push_back(X[i]); cw2.push_back(X[j]); cinv.push_back(0);
        added++;
      }
    }
  }
  int applySol(int g, const Sol& s, Rng& rng) {
    int before = ngates;
    created.clear();
    int el[8], m = s.k;
    u8 form = (u8)s.form, other = form == K_OR ? K_AND : K_OR;
    for (int i = 0; i < m; i++) {
      int x = s.w[i];
      if (s.w2[i] >= 0) x = mk(other, s.w[i], s.w2[i]);
      if (s.inv[i]) x = mk(K_NOT, x);
      el[i] = x;
    }
    while (m > 1) {
      int bi = -1, bj = -1;
      for (int i = 0; i < m && bi < 0; i++) for (int j = i + 1; j < m; j++) {
        int a = el[i], b = el[j];
        if (lookup(form, a, b) >= 0) { bi = i; bj = j; break; }
      }
      if (bi < 0) { bi = rng.below(m); bj = rng.below(m - 1); if (bj >= bi) bj++; }
      int r = mk(form, el[bi], el[bj]);
      if (bi > bj) std::swap(bi, bj);
      el[bj] = el[m - 1]; el[bi] = r; m--;
    }
    int r = el[0];
    if (r == g || tstamp[r] == tcur) {
      for (size_t i = created.size(); i-- > 0;) if (isGate(created[i]) && ref[created[i]] == 0) kill(created[i]);
      return INT_MIN;
    }
    replace(g, r);
    return before - ngates;
  }

  // ---------------------------------------------------------------- one local move at gate g
  // returns gates saved (>0), 0 for an accepted size-neutral rewrite, INT_MIN if nothing was done
  int tryGate(int g, Rng& rng, const Params& P, bool side, Stats& stt) {
    stt.tries++; visits++;
    markTFO(g);
    if (P.level >= 2) computeObs(g);
    else { for (size_t w = 0; w < W; w++) obs[w] = 0; for (int k = 0; k < K; k++) for (size_t w = 0; w < W; w++) obs[w] |= sp->care[k][w]; }
    const u64* cg = C(g);
    nzOn.clear(); nzOff.clear(); nzAll.clear();
    for (size_t w = 0; w < W; w++) {
      on[w] = cg[w] & obs[w]; off[w] = ~cg[w] & obs[w];
      if (on[w]) nzOn.push_back((int)w);
      if (off[w]) nzOff.push_back((int)w);
    }
    int before = ngates;
    if (nzOn.empty()) { replace(g, C0); stt.aConst++; stt.gConst += before - ngates; return before - ngates; }
    if (nzOff.empty()) { replace(g, C1); stt.aConst++; stt.gConst += before - ngates; return before - ngates; }
    eq.clear(); up.clear(); um.clear(); nup.clear(); neq.clear(); cand.clear();
    const bool noNot = !P.aon;
    const bool wantPairs = P.level >= 4;
    cvViaIndex = useT;
    if (!useT) {
      // direct scan of every wire. Scan order: words with on-bits first, then off-only words
      nzAll = nzOn;
      const int nOn = (int)nzOn.size();
      for (int w : nzOff) if (!on[w]) nzAll.push_back(w);
      const int nAll = (int)nzAll.size();
      auto scan = [&](int w) {
        if (tstamp[w] == tcur) return;
        const u64* c = C(w);
        u64 A = 0, B = 0, Cc = 0, D = 0;   // w hits off / misses on / misses off / hits on
        int i = 0;
        bool early1 = false, early2 = false;
        for (; i < nOn; i++) {
          int wi = nzAll[i]; u64 x = c[wi];
          A |= x & off[wi]; B |= ~x & on[wi]; Cc |= ~x & off[wi]; D |= x & on[wi];
          if (A && B && (noNot || Cc)) { early1 = true; break; }
        }
        // a wire that touches no on-point cannot cover anything and cannot contain on: only its complement could matter
        if (!early1 && !D && (noNot || Cc)) early1 = true;
        if (!early1) for (; i < nAll; i++) {
          int wi = nzAll[i]; u64 x = c[wi];
          A |= x & off[wi]; Cc |= ~x & off[wi];
          if (A && (noNot || Cc)) { early2 = true; break; }
        }
        scanw += i + 1;
        u8 fl = 0;
        if (early1) fl = 0;
        else if (early2) { if (!B) { um.push_back(w); fl = 2; } }
        else {
          bool a = !A, b = !B, cc = !Cc, d = !D;
          if (a && b) eq.push_back(w);
          else if (!noNot && cc && d) neq.push_back(w);
          if (a) { up.push_back(w); fl |= 1; }
          if (b) { um.push_back(w); fl |= 2; }
          if (!noNot && cc) nup.push_back(w);
        }
        if (wantPairs) { cand.push_back(w); wflag[w] = fl; wfs[w] = tcur; }
      };
      for (int w = 0; w < N; w++) scan(w);
      for (int w : order) scan(w);
    } else {
      // wires that contain every on-point (AND-form candidates; those that also avoid off are equal to g):
      // intersect the index rows of a few on-points, then confirm the survivors on their columns
      auto supersets = [&](const std::vector<int>& nz, const u64* S_, std::vector<u64>& acc) {
        for (size_t j = 0; j < TW; j++) acc[j] = aliveB[j] & ~tfoB[j];
        bool any = true; int steps = 0;
        const int n = (int)nz.size();
        const int stride = std::max(1, n / 24);
        for (int i = (int)rng.below(stride); i < n && any; i += stride) {
          int wi = nz[i];
          size_t p_ = (size_t)wi * 64 + __builtin_ctzll(S_[wi]);
          const u64* row = &T[p_ * TW];
          u64 o = 0;
          for (size_t j = 0; j < TW; j++) { acc[j] &= row[j]; o |= acc[j]; }
          steps++;
          if (!o) any = false;
        }
        scanw += (u64)steps * TW;
        return any;
      };
      auto containsAll = [&](int w, const std::vector<int>& nz, const u64* S_) {
        const u64* c = C(w);
        int i = 0; const int n = (int)nz.size();
        for (; i < n; i++) if (S_[nz[i]] & ~c[nz[i]]) break;
        scanw += i + 1;
        return i == n;
      };
      if (supersets(nzOn, on.data(), accC)) for (size_t j = 0; j < TW; j++) {
        u64 x = accC[j];
        while (x) {
          int w = (int)(j * 64) + __builtin_ctzll(x); x &= x - 1;
          if (!containsAll(w, nzOn, on.data())) continue;
          um.push_back(w); wflag[w] = 2; wfs[w] = tcur;
          if (avoidsOff(w)) eq.push_back(w);
        }
      }
      if (!noNot && supersets(nzOff, off.data(), accF)) for (size_t j = 0; j < TW; j++) {
        // wires that contain every off-point: their complement is an OR-form literal
        u64 x = accF[j];
        while (x) {
          int w = (int)(j * 64) + __builtin_ctzll(x); x &= x - 1;
          const u64* c = C(w);
          bool hit = false;
          for (int wi : nzOn) if (c[wi] & on[wi]) { hit = true; break; }
          bool missesSomeOn = false;
          for (int wi : nzOn) if (on[wi] & ~c[wi]) { missesSomeOn = true; break; }
          scanw += nzOn.size();
          if (!missesSomeOn) continue;            // complement covers nothing
          if (!containsAll(w, nzOff, off.data())) continue;
          nup.push_back(w);
          if (!hit) neq.push_back(w);
        }
      }
    }
    // 0-resubstitution: an existing wire agrees with g wherever g is observable
    if (!eq.empty()) {
      int bw = -1, bg = -1, ties = 0;
      for (int w : eq) {
        int gn = freedIf(g, &w, 1);
        if (gn > bg) { bg = gn; bw = w; ties = 1; }
        else if (gn == bg && rng.below(++ties) == 0) bw = w;
      }
      replace(g, bw);
      stt.aRes0++; stt.gRes0 += before - ngates;
      return before - ngates;
    }
    if (P.level < 2) return INT_MIN;
    int M = freedIf(g, nullptr, 0);
    Sol best;
    cvBestScore = INT_MIN;
    // NOT of an existing wire
    if (!neq.empty() && (M >= 2 || side)) {
      int ties = 0;
      for (int w : neq) {
        int gn = freedIf(g, &w, 1) - 1;
        if (gn < (side ? 0 : 1)) continue;
        if (kind[g] == K_NOT && fa[g] == w) continue;
        if (gn > best.gain) ties = 1;
        else if (gn == best.gain) { if (rng.below(++ties) != 0) continue; }
        else continue;
        best.form = K_OR; best.k = 1; best.w[0] = w; best.w2[0] = -1; best.inv[0] = 1; best.gain = gn;
      }
    }
    if (P.level >= 3 && (M >= 2 || side)) {
      if (rng.below(2)) { cover(g, M, K_OR, side, P, rng, best); cover(g, M, K_AND, side, P, rng, best); }
      else { cover(g, M, K_AND, side, P, rng, best); cover(g, M, K_OR, side, P, rng, best); }
    }
    if (best.gain < (side ? 0 : 1)) return INT_MIN;
    if (best.gain == 0 && P.sideMode == 2 && cvBestScore < 0 && cvBestScore > INT_MIN) {
      if (rng.unif() >= std::exp(cvBestScore / P.sideTemp)) return INT_MIN;
    }
    bool two = false;
    for (int i = 0; i < best.k; i++) two |= best.w2[i] >= 0;
    bool isNot = best.k == 1 && best.inv[0] && best.w2[0] < 0;
    int form = best.form;
    int got = applySol(g, best, rng);
    if (got == INT_MIN) return INT_MIN;
    if (got == 0) stt.aSide++;
    else if (two) { stt.aTwo++; stt.gTwo += got; }
    else if (isNot) { stt.aNot++; stt.gNot += got; }
    else if (form == K_OR) { stt.aOr++; stt.gOr += got; }
    else { stt.aAnd++; stt.gAnd += got; }
    return got;
  }

  // ---------------------------------------------------------------- redundancy addition (and removal by the caller)
  // Adds a wire e above gate g (g' = g OR e with e inside g's don't-cares, or g' = g AND e dually). The outputs do not
  // change, but the points e takes over become don't-cares for the cone below g, where strict moves may now remove
  // more than the addition cost. The caller snapshots the network and rolls back if the size did not go down.
  struct RarCand { int g = -1; u8 form = K_OR; int w1 = -1, w2 = -1; int score = -1; };
  void markTFI(int g) {
    icur++;
    st.clear(); st.push_back(g); tfiS[g] = icur;
    while (!st.empty()) {
      int x = st.back(); st.pop_back();
      int ins[2] = {fa[x], kind[x] == K_NOT ? -1 : fb[x]};
      for (int f : ins) if (f >= 0 && isGate(f) && tfiS[f] != icur) { tfiS[f] = icur; st.push_back(f); }
    }
  }
  bool rarPick(int g, Rng& rng, const Params& P, RarCand& rc) {
    if (!useT) return false;
    markTFO(g);
    computeObs(g);
    const u64* cg = C(g);
    nzOn.clear(); nzOff.clear();
    for (size_t w = 0; w < W; w++) {
      on[w] = cg[w] & obs[w]; off[w] = ~cg[w] & obs[w];
      if (on[w]) nzOn.push_back((int)w);
      if (off[w]) nzOff.push_back((int)w);
    }
    if (nzOn.empty() || nzOff.empty()) return false;
    markTFI(g);
    const u8 form = (!P.aon || rng.below(5)) ? K_OR : K_AND;
    const u64 flip = form == K_OR ? 0 : ~u64(0);
    const u64* T_ = form == K_OR ? on.data() : off.data();
    const u64* V = form == K_OR ? off.data() : on.data();
    const std::vector<int>& tnz = form == K_OR ? nzOn : nzOff;
    const std::vector<int>& vnz = form == K_OR ? nzOff : nzOn;
    const int nV = (int)vnz.size(), nT = (int)tnz.size();
    // a random target point
    int wi = tnz[rng.below((uint32_t)tnz.size())];
    u64 x = T_[wi];
    for (int k = rng.below(__builtin_popcountll(x)); k > 0; k--) x &= x - 1;
    int bit = __builtin_ctzll(x);
    const u64* row = &T[((size_t)wi * 64 + bit) * TW];
    std::vector<int> X;
    rc.g = g; rc.form = form; rc.score = -1;
    int ties = 0;
    auto consider = [&](int w1, int w2, int score) {
      if (score > rc.score) ties = 1;
      else if (score == rc.score) { if (rng.below(++ties) != 0) return; }
      else return;
      rc.w1 = w1; rc.w2 = w2; rc.score = score;
    };
    for (size_t j = 0; j < TW; j++) {
      u64 y = (row[j] ^ flip) & aliveB[j] & ~tfoB[j];
      while (y) {
        int w = (int)(j * 64) + __builtin_ctzll(y); y &= y - 1;
        const u64* c = C(w);
        int i = 0;
        for (; i < nV; i++) if ((c[vnz[i]] ^ flip) & V[vnz[i]]) break;
        scanw += i + 1;
        if (i < nV) { X.push_back(w); continue; }
        if (tfiS[w] == icur) continue;           // already below g: adding it again creates no slack
        int sc = 0;
        for (int t = 0; t < nT; t++) sc += __builtin_popcountll((c[tnz[t]] ^ flip) & T_[tnz[t]]);
        scanw += nT;
        consider(w, -1, sc * 2 + 1);             // an existing wire costs one gate less than a new pair
      }
    }
    scanw += TW;
    if ((int)X.size() > P.pairCap) { rng.shuffle(X); X.resize(P.pairCap); }
    const int nx = (int)X.size();
    std::vector<u64> ev((size_t)nx * nV);
    for (int i = 0; i < nx; i++) { const u64* c = C(X[i]); for (int j = 0; j < nV; j++) ev[(size_t)i * nV + j] = (c[vnz[j]] ^ flip) & V[vnz[j]]; }
    scanw += (u64)nx * nV;
    for (int i = 0; i < nx; i++) for (int j = i + 1; j < nx; j++) {
      const u64* a = &ev[(size_t)i * nV]; const u64* b = &ev[(size_t)j * nV];
      int z = 0;
      for (; z < nV; z++) if (a[z] & b[z]) break;
      scanw += z + 1;
      if (z < nV) continue;
      const u64* ca = C(X[i]); const u64* cb = C(X[j]);
      int sc = 0;
      for (int t = 0; t < nT; t++) sc += __builtin_popcountll((ca[tnz[t]] ^ flip) & (cb[tnz[t]] ^ flip) & T_[tnz[t]]);
      scanw += nT;
      consider(X[i], X[j], sc * 2);
    }
    return rc.score >= 4;
  }
  // returns the new node above g, or -1 if nothing was changed
  int rarApply(const RarCand& rc) {
    created.clear();
    const int g = rc.g;
    const u8 form = rc.form, other = form == K_OR ? K_AND : K_OR;
    auto undo = [&] { for (size_t i = created.size(); i-- > 0;) if (isGate(created[i]) && ref[created[i]] == 0) kill(created[i]); };
    int e = rc.w1;
    if (rc.w2 >= 0) {
      e = mk(other, rc.w1, rc.w2);
      if (created.empty() && tfiS[e] == icur) return -1;   // that pair already exists below g
    }
    if (e == g || e == C0 || e == C1 || tstamp[e] == tcur) { undo(); return -1; }
    rarZ.resize(W);
    const u64* ce = C(e);
    for (size_t w = 0; w < W; w++) rarZ[w] = form == K_OR ? (ce[w] & on[w]) : (~ce[w] & off[w]);
    int a = g, b = e;
    if (lookup(form, a, b) >= 0) { undo(); return -1; }
    int h = create(form, a, b);
    replace(g, h, h);
    return broken ? -1 : h;
  }
  void rarRegionOf(int g, u8 form, std::vector<int>& region, int maxn) {
    region.clear();
    icur++;
    region.push_back(g); tfiS[g] = icur;
    for (size_t head = 0; head < region.size() && (int)region.size() < maxn; head++) {
      int x = region[head];
      int ins[2] = {fa[x], kind[x] == K_NOT ? -1 : fb[x]};
      for (int f : ins) {
        if (f < 0 || !isGate(f) || tfiS[f] == icur) continue;
        const u64* c = C(f);
        bool touch = false;
        if (form == K_OR) { for (size_t w = 0; w < W; w++) if (c[w] & rarZ[w]) { touch = true; break; } }
        else { for (size_t w = 0; w < W; w++) if (~c[w] & rarZ[w]) { touch = true; break; } }
        scanw += W / 4;
        if (!touch) continue;
        tfiS[f] = icur; region.push_back(f);
      }
    }
  }

  // ---------------------------------------------------------------- set-space sharing optimiser
  // An OR-forest (dually an AND-forest) is treated purely as a family of leaf sets: every OR gate that feeds something
  // other than an OR gate (a "terminal") must stay the union of exactly the same leaves ("atoms" = non-OR wires); how the
  // unions are built and shared is free. Large-neighbourhood search: take a few terminals with overlapping sets, drop
  // their private structure, re-cover each with the fewest existing sub-unions (exact search), extract common pairs
  // among them, keep the result if the forest did not grow. No simulation is needed: the functions do not change.
  struct Forest {
    int na = 0, Wb = 0, nn = 0;
    std::vector<u64> bits;
    std::vector<int> c0, c1;
    std::vector<char> alive;
    std::vector<int> term;                   // terminal -> node
    std::vector<u64> tset;                   // terminal sets (fixed), nt * Wb
    std::unordered_map<u64, std::vector<int>> hash;
    int cost = 0;
    u64 work = 0;
    std::vector<u64> tmp;
    std::vector<int> stk;
    const u64* B(int i) const { return &bits[(size_t)i * Wb]; }
    const u64* TS(int t) const { return &tset[(size_t)t * Wb]; }
    u64 hashOf(const u64* b) const {
      u64 h = 1469598103934665603ull;
      for (int i = 0; i < Wb; i++) { h = (h ^ b[i]) * 1099511628211ull; h ^= h >> 31; }
      return h;
    }
    int find(const u64* b) const {
      auto it = hash.find(hashOf(b));
      if (it == hash.end()) return -1;
      for (int i : it->second) if (alive[i] && !std::memcmp(B(i), b, (size_t)Wb * 8)) return i;
      return -1;
    }
    int addRaw(const u64* b, int x, int y) {
      int id = nn++;
      bits.insert(bits.end(), b, b + Wb);
      c0.push_back(x); c1.push_back(y); alive.push_back(1);
      hash[hashOf(B(id))].push_back(id);
      return id;
    }
    int unite(int x, int y) {
      if (x == y) return x;
      tmp.resize(Wb);
      bool xin = true, yin = true;   // y subset of x / x subset of y
      for (int i = 0; i < Wb; i++) { u64 a = bits[(size_t)x * Wb + i], b = bits[(size_t)y * Wb + i]; tmp[i] = a | b; if (b & ~a) xin = false; if (a & ~b) yin = false; }
      if (xin) return x;
      if (yin) return y;
      int f = find(tmp.data());
      if (f >= 0) return f;
      return addRaw(tmp.data(), x, y);
    }
    void recount() {
      for (int i = na; i < nn; i++) alive[i] = 0;
      stk.clear();
      for (int t : term) if (t >= na && !alive[t]) { alive[t] = 1; stk.push_back(t); }
      int c = 0;
      while (!stk.empty()) {
        int x = stk.back(); stk.pop_back(); c++;
        int ch[2] = {c0[x], c1[x]};
        for (int y : ch) if (y >= na && !alive[y]) { alive[y] = 1; stk.push_back(y); }
      }
      cost = c;
      work += (u64)c * 2;
    }
    void truncate(int n0) {
      for (int id = nn - 1; id >= n0; id--) {
        auto it = hash.find(hashOf(B(id)));
        if (it != hash.end()) { auto& v = it->second; for (size_t k = v.size(); k-- > 0;) if (v[k] == id) { v.erase(v.begin() + k); break; } if (v.empty()) hash.erase(it); }
      }
      nn = n0;
      bits.resize((size_t)nn * Wb); c0.resize(nn); c1.resize(nn); alive.resize(nn);
    }
    void compact() {   // drop dead nodes
      std::vector<int> remap(nn, -1);
      int k = 0;
      for (int i = 0; i < nn; i++) if (i < na || alive[i]) remap[i] = k++;
      std::vector<u64> nb((size_t)k * Wb);
      std::vector<int> n0(k), n1(k);
      for (int i = 0; i < nn; i++) if (remap[i] >= 0) {
        std::memcpy(&nb[(size_t)remap[i] * Wb], B(i), (size_t)Wb * 8);
        n0[remap[i]] = i < na ? -1 : remap[c0[i]]; n1[remap[i]] = i < na ? -1 : remap[c1[i]];
      }
      for (int& t : term) if (t >= 0) t = remap[t];
      bits.swap(nb); c0.swap(n0); c1.swap(n1); nn = k; alive.assign(nn, 1);
      hash.clear();
      for (int i = na; i < nn; i++) hash[hashOf(B(i))].push_back(i);
    }
  };
  // minimum number of the given masks whose union is `full` (masks over <= 64 local atoms); result in `pick`
  static void minCover(const std::vector<u64>& mk_, u64 full, Rng& rng, std::vector<int>& pick, long budget) {
    const int n = (int)mk_.size();
    // greedy upper bound
    std::vector<int> best; u64 r = full;
    while (r) {
      int bi = -1, bc = -1;
      for (int i = 0; i < n; i++) { int c = __builtin_popcountll(mk_[i] & r) * 4 + (int)rng.below(4); if ((mk_[i] & r) && c > bc) { bc = c; bi = i; } }
      best.push_back(bi); r &= ~mk_[bi];
    }
    std::vector<int> cur;
    struct Rec {
      const std::vector<u64>& m; Rng& rng; std::vector<int>& best; std::vector<int>& cur; long& budget; int n;
      void go(u64 r) {
        if (!r) { if (cur.size() < best.size() || (cur.size() == best.size() && rng.below(3) == 0)) best = cur; return; }
        if (cur.size() + 1 > best.size() || (cur.size() + 1 == best.size() && budget < 0)) return;
        if (budget-- <= 0) return;
        // lower bound: the largest remaining coverage
        int mx = 0;
        for (int i = 0; i < n; i++) mx = std::max(mx, __builtin_popcountll(m[i] & r));
        int need = (__builtin_popcountll(r) + mx - 1) / mx;
        if ((int)cur.size() + need > (int)best.size()) return;
        // branch on the uncovered atom with the fewest candidates
        int bb = -1, bc = INT_MAX;
        for (u64 x = r; x; x &= x - 1) {
          int b = __builtin_ctzll(x), c = 0;
          for (int i = 0; i < n; i++) c += (m[i] >> b) & 1;
          if (c < bc) { bc = c; bb = b; }
        }
        std::vector<std::pair<int, int>> L;
        for (int i = 0; i < n; i++) if ((m[i] >> bb) & 1) L.push_back({-(__builtin_popcountll(m[i] & r) * 8 + (int)rng.below(8)), i});
        std::sort(L.begin(), L.end());
        for (auto& pr : L) { cur.push_back(pr.second); go(r & ~m[pr.second]); cur.pop_back(); }
      }
    } rec{mk_, rng, best, cur, budget, n};
    rec.go(full);
    pick = best;
  }
  // A product gate AND(P, Q) whose two inputs are OR-terminals over input wires and whose value is the union of two
  // independent products (X1 AND Y1) OR (X2 AND Y2), with P = X1 u X2 and Q = Y1 u Y2 (cross pairs vanish on every point).
  static inline thread_local long dbgProds = 0, dbgAttempts = 0, dbgValid = 0, dbgWorse = 0, dbgEstSum = 0, dbgEstMin = 1000, dbgEstN = 0, dbgFull = 0;
  struct Prod2 { int tP = -1, tQ = -1; u64 sig = 0; std::vector<u64> X1, Y1, X2, Y2; };
  struct Lns {
    Forest& F; Rng& rng;
    int Wb, nt, maxGroup;
    std::vector<int> tsize, elig;
    std::vector<std::vector<int>> nb;
    std::vector<int> savedTerm, atomsOf, cand, pick;
    std::vector<char> savedAlive;
    std::vector<u64> masks;
    std::vector<std::vector<int>> lists;
    std::unordered_map<u64, int> pc;
    bool noCompact = false;
    long kept = 0, tried = 0;
    Lns(Forest& f, Rng& r, int mg) : F(f), rng(r), Wb(f.Wb), nt((int)f.term.size()), maxGroup(mg) { neighbours(); }
    void neighbours() {
      tsize.assign(nt, 0); nb.assign(nt, {}); elig.clear();
      for (int a = 0; a < nt; a++) { int s = 0; for (int i = 0; i < Wb; i++) s += __builtin_popcountll(F.TS(a)[i]); tsize[a] = s; }
      for (int a = 0; a < nt; a++) for (int b = a + 1; b < nt; b++) {
        int s = 0;
        const u64* x = F.TS(a); const u64* y = F.TS(b);
        for (int i = 0; i < Wb; i++) s += __builtin_popcountll(x[i] & y[i]);
        if (s >= 2) { nb[a].push_back(b); nb[b].push_back(a); }
      }
      for (int a = 0; a < nt; a++) if (tsize[a] >= 3 && tsize[a] <= 64) elig.push_back(a);
      F.work += (u64)nt * nt * Wb / 8;
    }
    void pickGroup(std::vector<int>& group, int c) {
      group.clear();
      group.push_back(c);
      int want = 1 + (int)rng.below(maxGroup);
      for (int tries = 0; (int)group.size() < want && tries < 4 * want; tries++) {
        int base = group[rng.below((uint32_t)group.size())];
        if (nb[base].empty()) continue;
        int o = nb[base][rng.below((uint32_t)nb[base].size())];
        if (tsize[o] > 64 || tsize[o] < 3) continue;
        bool dup = false; for (int g : group) dup |= g == o;
        if (!dup) group.push_back(o);
      }
    }
    // rebuild the terminals of `group` (their term[] is -1 and the forest has been recounted)
    void repair(const std::vector<int>& group) {
      lists.assign(group.size(), {});
      for (size_t gi = 0; gi < group.size(); gi++) {
        const u64* S = F.TS(group[gi]);
        int ex = F.find(S);
        if (ex >= 0) { lists[gi].push_back(ex); continue; }
        atomsOf.clear();
        for (int i = 0; i < Wb; i++) for (u64 x = S[i]; x; x &= x - 1) atomsOf.push_back(i * 64 + __builtin_ctzll(x));
        cand.clear(); masks.clear();
        for (int i = F.na; i < F.nn; i++) {
          if (!F.alive[i]) continue;
          const u64* b = F.B(i);
          bool sub = true;
          for (int k = 0; k < Wb; k++) if (b[k] & ~S[k]) { sub = false; break; }
          if (!sub) continue;
          u64 mk_ = 0;
          for (size_t a = 0; a < atomsOf.size(); a++) if ((b[atomsOf[a] >> 6] >> (atomsOf[a] & 63)) & 1) mk_ |= u64(1) << a;
          cand.push_back(i); masks.push_back(mk_);
        }
        F.work += (u64)(F.nn - F.na) * Wb / 4 + 16;
        {   // maximal candidates only; single atoms are always available
          std::vector<int> c2; std::vector<u64> m2;
          for (size_t i = 0; i < cand.size(); i++) {
            bool dom = false;
            for (size_t j = 0; j < cand.size() && !dom; j++) if (j != i && (masks[i] & ~masks[j]) == 0 && (masks[i] != masks[j] || j < i)) dom = true;
            if (!dom) { c2.push_back(cand[i]); m2.push_back(masks[i]); }
          }
          cand.swap(c2); masks.swap(m2);
        }
        for (size_t a = 0; a < atomsOf.size(); a++) { cand.push_back(atomsOf[a]); masks.push_back(u64(1) << a); }
        u64 full = atomsOf.size() >= 64 ? ~u64(0) : ((u64(1) << atomsOf.size()) - 1);
        minCover(masks, full, rng, pick, 300);
        F.work += 200;
        for (int p : pick) lists[gi].push_back(cand[p]);
      }
      while (group.size() > 1) {   // common pairs inside the group
        pc.clear();
        for (auto& L : lists) for (size_t i = 0; i < L.size(); i++) for (size_t j = i + 1; j < L.size(); j++) {
          int x = std::min(L[i], L[j]), y = std::max(L[i], L[j]);
          pc[((u64)x << 32) | (u64)(uint32_t)y]++;
        }
        int mx = 1; u64 bk = 0; int ties = 0;
        for (auto& kv : pc) {
          if (kv.second > mx) { mx = kv.second; bk = kv.first; ties = 1; }
          else if (kv.second == mx && mx >= 2 && rng.below(++ties) == 0) bk = kv.first;
        }
        F.work += pc.size() + 8;
        if (mx < 2) break;
        int x = (int)(bk >> 32), y = (int)(bk & 0xffffffffu);
        int p = F.unite(x, y);
        for (auto& L : lists) {
          int ix = -1, iy = -1;
          for (size_t i = 0; i < L.size(); i++) { if (L[i] == x) ix = (int)i; if (L[i] == y) iy = (int)i; }
          if (ix < 0 || iy < 0) continue;
          L[ix] = p; L[iy] = L.back(); L.pop_back();
        }
      }
      for (size_t gi = 0; gi < group.size(); gi++) {   // finish every list, preferring unions that already exist
        auto& L = lists[gi];
        while (L.size() > 1) {
          int bi = -1, bj = -1;
          F.tmp.resize(Wb);
          for (size_t i = 0; i < L.size() && bi < 0; i++) for (size_t j = i + 1; j < L.size(); j++) {
            const u64* a = F.B(L[i]); const u64* b = F.B(L[j]);
            for (int k = 0; k < Wb; k++) F.tmp[k] = a[k] | b[k];
            if (F.find(F.tmp.data()) >= 0) { bi = (int)i; bj = (int)j; break; }
          }
          F.work += L.size() * L.size() * Wb / 4 + 4;
          if (bi < 0) { bi = rng.below((uint32_t)L.size()); bj = rng.below((uint32_t)L.size() - 1); if (bj >= bi) bj++; }
          int p = F.unite(L[bi], L[bj]);
          if (bi > bj) std::swap(bi, bj);
          L[bj] = L.back(); L.pop_back(); L[bi] = p;
        }
        F.term[group[gi]] = L[0];
      }
    }
    // number of live sub-unions (or atoms) needed to cover set S, minus one: the gates a fresh tree for S would cost
    int coverCost(const u64* S) {
      if (F.find(S) >= 0) return 0;
      atomsOf.clear();
      for (int i = 0; i < Wb; i++) for (u64 x = S[i]; x; x &= x - 1) atomsOf.push_back(i * 64 + __builtin_ctzll(x));
      if (atomsOf.size() > 64) return (int)atomsOf.size() - 1;
      masks.clear();
      for (int i = F.na; i < F.nn; i++) {
        if (!F.alive[i]) continue;
        const u64* b = F.B(i);
        bool sub = true;
        for (int k = 0; k < Wb; k++) if (b[k] & ~S[k]) { sub = false; break; }
        if (!sub) continue;
        u64 mk_ = 0;
        for (size_t a = 0; a < atomsOf.size(); a++) if ((b[atomsOf[a] >> 6] >> (atomsOf[a] & 63)) & 1) mk_ |= u64(1) << a;
        masks.push_back(mk_);
      }
      for (size_t a = 0; a < atomsOf.size(); a++) masks.push_back(u64(1) << a);
      u64 full = atomsOf.size() >= 64 ? ~u64(0) : ((u64(1) << atomsOf.size()) - 1);
      minCover(masks, full, rng, pick, 100);
      F.work += (u64)(F.nn - F.na) * Wb / 4 + 100;
      return (int)pick.size() - 1;
    }
    // drop and rebuild a group; keep the result only if the forest did not grow
    bool trial(const std::vector<int>& group) {
      tried++;
      const int n0 = F.nn, oldCost = F.cost;
      savedAlive = F.alive;
      savedTerm.clear();
      for (int t : group) { savedTerm.push_back(F.term[t]); F.term[t] = -1; }
      F.recount();
      repair(group);
      F.recount();
      if (F.cost <= oldCost) {
        if (!noCompact && F.nn > 6 * (F.cost + F.na) + 256) F.compact();
        kept++;
        return true;
      }
      F.truncate(n0);
      for (size_t gi = 0; gi < group.size(); gi++) F.term[group[gi]] = savedTerm[gi];
      F.alive = savedAlive; F.cost = oldCost;
      return false;
    }
  };
  static bool orthSets(const std::vector<u64>& nonorth, int Wb, const std::vector<u64>& S1, const std::vector<u64>& S2) {
    for (int i = 0; i < Wb; i++) for (u64 x = S1[i]; x; x &= x - 1) {
      const u64* r = &nonorth[(size_t)(i * 64 + __builtin_ctzll(x)) * Wb];
      for (int k = 0; k < Wb; k++) if (r[k] & S2[k]) return false;
    }
    return true;
  }
  // LNS on a forest. With product gates (prods + nonorth) it also re-pairs products between two product gates.
  static int lns(Forest& F, Rng& rng, u64 workBudget, int maxGroup, std::vector<Prod2>* prods, const std::vector<u64>* nonorth,
                 double repairProb, int polish, long* repairsKept, double temp = 0) {
    const int estSlack = 2 + (int)(3 * temp);
    Lns L(F, rng, maxGroup);
    if (L.elig.empty()) return 0;
    F.recount();
    const int startCost = F.cost;
    const int Wb = F.Wb;
    std::vector<int> group, g4, tmpg;
    const u64 w0 = F.work;
    const bool canPair = prods && prods->size() >= 2 && repairProb > 0;
    long acc = 0;
    Forest bestF; int bestCost = F.cost; bool haveBest = false;   // only needed when worse exchanges may be accepted
    if (temp > 0 && canPair) { bestF = F; haveBest = true; }
    while (F.work - w0 < workBudget) {
      if (canPair && rng.unif() < repairProb) {
        // --- exchange partners between two product gates, re-cover their four terminals, polish, keep if not worse
        int ia = rng.below((uint32_t)prods->size()), ib = rng.below((uint32_t)prods->size() - 1);
        if (ib >= ia) ib++;
        Prod2& A = (*prods)[ia]; Prod2& B = (*prods)[ib];
        F.work += 8;
        dbgAttempts++;
        if (A.sig != B.sig) continue;
        const std::vector<u64>* pa[2][2] = {{&A.X1, &A.Y1}, {&A.X2, &A.Y2}};
        const std::vector<u64>* pb[2][2] = {{&B.X1, &B.Y1}, {&B.X2, &B.Y2}};
        int opt = rng.below(2);   // a1 with b1 (and a2 with b2), or a1 with b2 (and a2 with b1)
        Prod2 NA = A, NB = B;
        bool ok = true;
        for (int side = 0; side < 2 && ok; side++) {
          const std::vector<u64>* p0 = pa[side][0]; const std::vector<u64>* p1 = pa[side][1];
          int bsel = side == 0 ? opt : 1 - opt;
          const std::vector<u64>* q0 = pb[bsel][0]; const std::vector<u64>* q1 = pb[bsel][1];
          Prod2& T = side == 0 ? NA : NB;
          // orientation 0: P = p.X u q.X, Q = p.Y u q.Y ; orientation 1: P = p.X u q.Y, Q = p.Y u q.X
          bool o0 = orthSets(*nonorth, Wb, *p0, *q1) && orthSets(*nonorth, Wb, *q0, *p1);
          bool o1 = orthSets(*nonorth, Wb, *p0, *q0) && orthSets(*nonorth, Wb, *p1, *q1);
          F.work += 64;
          if (!o0 && !o1) { ok = false; break; }
          bool use1 = o1 && (!o0 || rng.below(2));
          T.X1 = *p0; T.Y1 = *p1;
          if (use1) { T.X2 = *q1; T.Y2 = *q0; } else { T.X2 = *q0; T.Y2 = *q1; }
        }
        if (!ok) continue;
        dbgValid++;
        g4 = {A.tP, A.tQ, B.tP, B.tQ};
        // snapshot
        const int n0 = F.nn, oldCost = F.cost;
        std::vector<int> termSave = F.term;
        std::vector<char> aliveSave = F.alive;
        {   // cheap estimate first: cost of fresh trees for the four old sets against the four new sets
          for (int t : g4) F.term[t] = -1;
          F.recount();
          std::vector<u64> ns(Wb);
          int oldEst = 0, newEst = 0;
          for (int t : g4) oldEst += L.coverCost(F.TS(t));
          const std::vector<u64>* parts[4][2] = {{&NA.X1, &NA.X2}, {&NA.Y1, &NA.Y2}, {&NB.X1, &NB.X2}, {&NB.Y1, &NB.Y2}};
          for (int i = 0; i < 4; i++) { for (int k = 0; k < Wb; k++) ns[k] = (*parts[i][0])[k] | (*parts[i][1])[k]; newEst += L.coverCost(ns.data()); }
          int d = newEst - oldEst;
          dbgEstSum += d; dbgEstMin = std::min(dbgEstMin, (long)d); dbgEstN++;
          if (d > estSlack) { F.term = termSave; F.alive = aliveSave; F.cost = oldCost; continue; }
        }
        dbgFull++;
        std::vector<u64> tsSave[4];
        for (int i = 0; i < 4; i++) tsSave[i].assign(F.TS(g4[i]), F.TS(g4[i]) + Wb);
        // new terminal sets
        auto setT = [&](int t, const std::vector<u64>& a, const std::vector<u64>& b) { for (int k = 0; k < Wb; k++) F.tset[(size_t)t * Wb + k] = a[k] | b[k]; };
        setT(A.tP, NA.X1, NA.X2); setT(A.tQ, NA.Y1, NA.Y2); setT(B.tP, NB.X1, NB.X2); setT(B.tQ, NB.Y1, NB.Y2);
        for (int t : g4) F.term[t] = -1;
        F.recount();
        L.repair(g4);
        F.recount();
        L.noCompact = true;
        // polish around the four terminals (neighbour lists are slightly stale; that only affects group choice)
        for (int it = 0; it < polish; it++) {
          L.pickGroup(tmpg, g4[rng.below(4)]);
          L.trial(tmpg);
        }
        L.noCompact = false;
        if (F.cost <= oldCost || (temp > 0 && rng.unif() < std::exp(-(double)(F.cost - oldCost) / temp))) {
          A.X1 = NA.X1; A.Y1 = NA.Y1; A.X2 = NA.X2; A.Y2 = NA.Y2;
          B.X1 = NB.X1; B.Y1 = NB.Y1; B.X2 = NB.X2; B.Y2 = NB.Y2;
          acc++;
          for (int t : g4) { int s = 0; for (int i = 0; i < Wb; i++) s += __builtin_popcountll(F.TS(t)[i]); L.tsize[t] = s; }
          if (acc % 16 == 0) L.neighbours();
          if (F.nn > 6 * (F.cost + F.na) + 256) F.compact();
        } else {
          dbgWorse += F.cost - oldCost;
          F.truncate(n0);
          F.term = termSave; F.alive = aliveSave; F.cost = oldCost;
          for (int i = 0; i < 4; i++) std::copy(tsSave[i].begin(), tsSave[i].end(), F.tset.begin() + (size_t)g4[i] * Wb);
        }
        continue;
      }
      L.pickGroup(group, L.elig[rng.below((uint32_t)L.elig.size())]);
      L.trial(group);
      if (temp > 0 && F.cost < bestCost) { bestCost = F.cost; bestF = F; haveBest = true; }
    }
    F.recount();
    if (temp > 0) {
      if (haveBest && bestF.cost <= F.cost) { u64 wk = F.work; F = bestF; F.work = wk; F.recount(); }
      else if (F.cost > startCost) return -1000000;   // drifted above the start without ever improving: caller keeps the old network
    }
    if (repairsKept) *repairsKept += acc;
    return startCost - F.cost;
  }
  // Runs the sharing optimiser on the OR-forest and the AND-forest and rebuilds the network.
  Net share(Rng& rng, u64 workBudget, int maxGroup, int* savedOut = nullptr, double repairProb = 0, int polish = 8, long* repairsKept = nullptr, double temp = 0) {
    ensureOrder();
    std::vector<int> oref(nextid, 0);
    for (int o : outs) oref[o]++;
    Forest F[2];
    std::vector<int> atomIdx[2], atomWire[2], nodeOf[2], termOf[2];
    int saved = 0;
    for (int k = 0; k < 2; k++) {
      Forest& f = F[k];
      atomIdx[k].assign(nextid, -1); nodeOf[k].assign(nextid, -1); termOf[k].assign(nextid, -1);
      for (int g : order) if (kind[g] == k) {
        int ins[2] = {fa[g], fb[g]};
        for (int x : ins) if (kind[x] != k && atomIdx[k][x] < 0) { atomIdx[k][x] = (int)atomWire[k].size(); atomWire[k].push_back(x); }
      }
      f.na = (int)atomWire[k].size();
      if (!f.na) continue;
      f.Wb = (f.na + 63) / 64;
      f.nn = f.na;
      f.bits.assign((size_t)f.na * f.Wb, 0);
      for (int a = 0; a < f.na; a++) f.bits[(size_t)a * f.Wb + (a >> 6)] = u64(1) << (a & 63);
      f.c0.assign(f.na, -1); f.c1.assign(f.na, -1); f.alive.assign(f.na, 1);
      for (int g : order) if (kind[g] == k) {
        int x = kind[fa[g]] == k ? nodeOf[k][fa[g]] : atomIdx[k][fa[g]];
        int y = kind[fb[g]] == k ? nodeOf[k][fb[g]] : atomIdx[k][fb[g]];
        nodeOf[k][g] = f.unite(x, y);
        bool isTerm = oref[g] > 0;
        for (int h : fo[g]) if (kind[h] != k) { isTerm = true; break; }
        if (isTerm) { termOf[k][g] = (int)f.term.size(); f.term.push_back(nodeOf[k][g]); }
      }
      for (int t : f.term) f.tset.insert(f.tset.end(), f.B(t), f.B(t) + f.Wb);
    }
    // order: the AND-forest first (it has no product gates of its own), then the OR-forest with product re-pairing
    for (int k = 0; k < 2; k++) {
      Forest& f = F[k];
      if (!f.na || f.term.size() < 2) continue;
      std::vector<Prod2> prods;
      std::vector<u64> nonorth;
      const int o = 1 - k;   // the other kind: product gates are gates of kind o reading two terminals of kind k
      if (repairProb > 0) {
        const int Wb = f.Wb;
        std::vector<int> inAtoms;
        for (int a = 0; a < f.na; a++) if (kind[atomWire[k][a]] == K_IN) inAtoms.push_back(a);
        // which atoms meet on some point (only input atoms are needed)
        nonorth.assign((size_t)f.na * Wb, 0);
        for (size_t i = 0; i < inAtoms.size(); i++) for (size_t j = i; j < inAtoms.size(); j++) {
          const u64* ca = C(atomWire[k][inAtoms[i]]); const u64* cb = C(atomWire[k][inAtoms[j]]);
          bool meet = false;
          if (k == K_OR) { for (size_t w = 0; w < W; w++) if (ca[w] & cb[w]) { meet = true; break; } }
          else { for (size_t w = 0; w < W; w++) if (~(ca[w] | cb[w]) & (w + 1 == W ? lm : ~u64(0))) { meet = true; break; } }
          if (meet) {
            int a = inAtoms[i], b = inAtoms[j];
            nonorth[(size_t)a * Wb + (b >> 6)] |= u64(1) << (b & 63);
            nonorth[(size_t)b * Wb + (a >> 6)] |= u64(1) << (a & 63);
          }
        }
        std::vector<char> isIn(f.na, 0);
        for (int a : inAtoms) isIn[a] = 1;
        for (int g : order) {
          if (kind[g] != o || oref[g] > 0) continue;
          int p = fa[g], q = fb[g];
          if (kind[p] != k || kind[q] != k || termOf[k][p] < 0 || termOf[k][q] < 0 || ref[p] != 1 || ref[q] != 1 || p == q) continue;
          // g must be an atom of forest k and all its consumers must be gates of kind k
          bool allK = !fo[g].empty();
          for (int h : fo[g]) if (kind[h] != k) { allK = false; break; }
          if (!allK || atomIdx[k][g] < 0) continue;
          const u64* SP = f.TS(termOf[k][p]); const u64* SQ = f.TS(termOf[k][q]);
          std::vector<int> ap, aq;
          bool good = true;
          for (int i = 0; i < Wb && good; i++) {
            if (SP[i] & SQ[i]) good = false;
            for (u64 x = SP[i]; x; x &= x - 1) { int a = i * 64 + __builtin_ctzll(x); if (!isIn[a]) good = false; ap.push_back(a); }
            for (u64 x = SQ[i]; x; x &= x - 1) { int a = i * 64 + __builtin_ctzll(x); if (!isIn[a]) good = false; aq.push_back(a); }
          }
          if (!good || ap.size() > 64 || aq.size() > 64) continue;
          // connected components of the "meet" graph between P's atoms and Q's atoms
          std::vector<int> cp(ap.size(), -1), cq(aq.size(), -1);
          int nc = 0;
          for (size_t s0 = 0; s0 < ap.size(); s0++) {
            if (cp[s0] >= 0) continue;
            std::vector<std::pair<int, int>> st2; st2.push_back({0, (int)s0}); cp[s0] = nc;
            while (!st2.empty()) {
              auto [side, idx] = st2.back(); st2.pop_back();
              int a = side == 0 ? ap[idx] : aq[idx];
              const u64* r = &nonorth[(size_t)a * Wb];
              if (side == 0) { for (size_t j = 0; j < aq.size(); j++) if (cq[j] < 0 && ((r[aq[j] >> 6] >> (aq[j] & 63)) & 1)) { cq[j] = nc; st2.push_back({1, (int)j}); } }
              else { for (size_t j = 0; j < ap.size(); j++) if (cp[j] < 0 && ((r[ap[j] >> 6] >> (ap[j] & 63)) & 1)) { cp[j] = nc; st2.push_back({0, (int)j}); } }
            }
            nc++;
          }
          bool allq = true; for (int c : cq) if (c < 0) allq = false;
          if (nc != 2 || !allq) continue;
          Prod2 pr;
          pr.tP = termOf[k][p]; pr.tQ = termOf[k][q];
          pr.X1.assign(Wb, 0); pr.Y1.assign(Wb, 0); pr.X2.assign(Wb, 0); pr.Y2.assign(Wb, 0);
          for (size_t i = 0; i < ap.size(); i++) (cp[i] == 0 ? pr.X1 : pr.X2)[ap[i] >> 6] |= u64(1) << (ap[i] & 63);
          for (size_t i = 0; i < aq.size(); i++) (cq[i] == 0 ? pr.Y1 : pr.Y2)[aq[i] >> 6] |= u64(1) << (aq[i] & 63);
          bool nonEmpty = false;
          { u64 a1 = 0, a2 = 0, a3 = 0, a4 = 0; for (int i = 0; i < Wb; i++) { a1 |= pr.X1[i]; a2 |= pr.Y1[i]; a3 |= pr.X2[i]; a4 |= pr.Y2[i]; } nonEmpty = a1 && a2 && a3 && a4; }
          if (!nonEmpty) continue;
          // signature: the set of terminals of forest k that contain g as an atom
          u64 sig = 1469598103934665603ull;
          int ga = atomIdx[k][g];
          for (size_t t = 0; t < f.term.size(); t++) if ((f.TS((int)t)[ga >> 6] >> (ga & 63)) & 1) sig = (sig ^ (u64)(t + 1)) * 1099511628211ull;
          pr.sig = sig;
          prods.push_back(pr);
        }
      }
      dbgProds += (long)prods.size();
      saved += lns(f, rng, workBudget, maxGroup, prods.size() >= 2 ? &prods : nullptr, &nonorth, repairProb, polish, repairsKept, temp);
    }
    if (savedOut) *savedOut = saved;
    Net nn;
    nn.init(sp, ngates);
    std::vector<int> nid(nextid, -1);
    for (int i = 0; i < N; i++) nid[i] = i;
    nid[C0] = nn.C0; nid[C1] = nn.C1;
    std::vector<int> newOf[2];
    for (int k = 0; k < 2; k++) newOf[k].assign(F[k].nn, -1);
    std::vector<int> stk;
    for (int g : order) {
      if (kind[g] == K_NOT) { nid[g] = nn.mk(K_NOT, nid[fa[g]]); continue; }
      const int k = kind[g];
      if (termOf[k][g] < 0) continue;
      Forest& f = F[k];
      int root = f.term[termOf[k][g]];
      stk.clear(); stk.push_back(root);
      while (!stk.empty()) {
        int x = stk.back();
        if (newOf[k][x] >= 0) { stk.pop_back(); continue; }
        if (x < f.na) { newOf[k][x] = nid[atomWire[k][x]]; stk.pop_back(); continue; }
        int a = f.c0[x], b = f.c1[x];
        bool ready = true;
        if (newOf[k][a] < 0) { stk.push_back(a); ready = false; }
        if (newOf[k][b] < 0) { stk.push_back(b); ready = false; }
        if (ready) { newOf[k][x] = nn.mk((u8)k, newOf[k][a], newOf[k][b]); stk.pop_back(); }
      }
      nid[g] = newOf[k][root];
    }
    for (int k = 0; k < K; k++) {
      int w = nid[outs[k]];
      nn.ref[nn.outs[k]]--; nn.outs[k] = w; nn.ref[w]++;
    }
    nn.sweep();
    nn.created.clear();
    nn.simw = simw + nn.simw; nn.scanw = scanw;
    nn.visits = visits + (F[0].work + F[1].work) / 3000 + (u64)ngates * 8;
    if (!nn.outputsOK()) nn.broken = true;
    return nn;
  }

  // ---------------------------------------------------------------- Paar-style common-subexpression extraction
  // Flattens AND-trees and OR-trees into leaf sets, repeatedly materialises the most frequent leaf pair, and rebuilds
  // the network. mode 0: only single-fanout internal nodes are flattened (never larger than before);
  // mode 1: every same-op fanin is expanded (re-derives all sharing from scratch; may be larger or smaller).
  Net paar(Rng& rng, int mode, bool subsetFirst) {
    ensureOrder();
    std::vector<char> absorbed(nextid, 0);
    std::vector<int> oref(nextid, 0);
    for (int o : outs) oref[o]++;
    for (int g : order) {
      if (kind[g] > K_OR) continue;
      bool ab = oref[g] == 0;
      for (int f : fo[g]) if (kind[f] != kind[g]) { ab = false; break; }
      if (mode == 0 && ref[g] != 1) ab = false;
      absorbed[g] = ab;
    }
    std::vector<int> roots;
    for (int g : order) if (kind[g] <= K_OR && !absorbed[g]) roots.push_back(g);
    const int R_ = (int)roots.size();
    std::vector<std::vector<int>> sets(R_);
    std::vector<int> seen(nextid, -1);
    for (int ri = 0; ri < R_; ri++) {
      int r = roots[ri];
      std::vector<int>& S = sets[ri];
      st.clear(); st.push_back(r); seen[r] = ri;
      while (!st.empty()) {
        int x = st.back(); st.pop_back();
        int ins[2] = {fa[x], fb[x]};
        for (int f : ins) {
          if (seen[f] == ri) continue;
          seen[f] = ri;
          if (kind[f] == kind[r] && (absorbed[f] || mode == 1)) st.push_back(f);
          else S.push_back(f);
        }
      }
      std::sort(S.begin(), S.end());
    }
    auto contains = [](const std::vector<int>& S, int x) { return std::binary_search(S.begin(), S.end(), x); };
    if (subsetFirst && R_ <= 4000) {
      // use a whole smaller root inside a larger one when its leaf set is contained (largest first)
      std::vector<int> bysize(R_);
      for (int i = 0; i < R_; i++) bysize[i] = i;
      std::stable_sort(bysize.begin(), bysize.end(), [&](int a, int b) { return sets[a].size() > sets[b].size(); });
      std::vector<std::vector<int>> orig = sets;
      for (int i = 0; i < R_; i++) {
        std::vector<int>& S = sets[i];
        for (int j : bysize) {
          if (j == i || kind[roots[j]] != kind[roots[i]]) continue;
          const std::vector<int>& Q = orig[j];
          if (Q.size() < 2 || Q.size() > S.size()) continue;
          if (Q.size() == orig[i].size() && j > i) continue;   // equal sets: the earlier root is the representative
          if (!std::includes(S.begin(), S.end(), Q.begin(), Q.end())) continue;
          std::vector<int> T2;
          std::set_difference(S.begin(), S.end(), Q.begin(), Q.end(), std::back_inserter(T2));
          T2.push_back(roots[j]);
          std::sort(T2.begin(), T2.end());
          S.swap(T2);
        }
      }
    }
    // --- pair extraction
    const int base = nextid;
    struct PairNode { u8 op; int x, y; };
    std::vector<PairNode> pairs;
    const size_t BIG = 64;
    std::unordered_map<u64, int> cnt;
    auto pkey = [](u8 op, int x, int y) { return ((u64)op << 62) | ((u64)(uint32_t)x << 31) | (u64)(uint32_t)y; };
    long guard = 0;
    while (true) {
      cnt.clear();
      for (int i = 0; i < R_; i++) {
        const std::vector<int>& S = sets[i];
        if (S.size() < 2 || S.size() > BIG) continue;
        u8 op = kind[roots[i]];
        for (size_t a = 0; a < S.size(); a++) for (size_t b = a + 1; b < S.size(); b++) cnt[pkey(op, S[a], S[b])]++;
      }
      for (int i = 0; i < R_; i++) {
        const std::vector<int>& S = sets[i];
        if (S.size() <= BIG) continue;
        u8 op = kind[roots[i]];
        for (auto& kv : cnt) {
          if ((u8)(kv.first >> 62) != op) continue;
          int x = (int)((kv.first >> 31) & 0x7fffffff), y = (int)(kv.first & 0x7fffffff);
          if (contains(S, x) && contains(S, y)) kv.second++;
        }
      }
      int maxc = 1;
      for (auto& kv : cnt) maxc = std::max(maxc, kv.second);
      if (maxc < 2) break;
      std::vector<u64> top;
      for (auto& kv : cnt) if (kv.second == maxc) top.push_back(kv.first);
      std::sort(top.begin(), top.end());
      rng.shuffle(top);
      for (u64 k : top) {
        u8 op = (u8)(k >> 62);
        int x = (int)((k >> 31) & 0x7fffffff), y = (int)(k & 0x7fffffff);
        std::vector<int> who;
        for (int i = 0; i < R_; i++) if (kind[roots[i]] == op && contains(sets[i], x) && contains(sets[i], y)) who.push_back(i);
        if ((int)who.size() < maxc) continue;
        int p = base + (int)pairs.size();
        pairs.push_back({op, x, y});
        for (int i : who) {
          std::vector<int>& S = sets[i];
          S.erase(std::lower_bound(S.begin(), S.end(), x));
          S.erase(std::lower_bound(S.begin(), S.end(), y));
          S.push_back(p);
        }
      }
      if (++guard > 1000000) break;
    }
    // --- rebuild
    Net nn;
    nn.init(sp, ngates);
    std::vector<int> nid(nextid, -1), pid(pairs.size(), -1);
    for (int i = 0; i < N; i++) nid[i] = i;
    nid[C0] = nn.C0; nid[C1] = nn.C1;
    std::vector<int> rootIdx(nextid, -1);
    for (int i = 0; i < R_; i++) rootIdx[roots[i]] = i;
    std::vector<int> el, stk;
    // builds old node x (and whatever it needs) in the new net; iterative to keep the stack flat
    auto elemReady = [&](int e) { return e < base ? nid[e] >= 0 : pid[e - base] >= 0; };
    auto elemId = [&](int e) { return e < base ? nid[e] : pid[e - base]; };
    auto build = [&](int top) {
      stk.clear(); stk.push_back(top);
      while (!stk.empty()) {
        int x = stk.back();
        if (elemReady(x)) { stk.pop_back(); continue; }
        bool ready = true;
        if (x >= base) {
          const PairNode& pn = pairs[x - base];
          if (!elemReady(pn.x)) { stk.push_back(pn.x); ready = false; }
          if (!elemReady(pn.y)) { stk.push_back(pn.y); ready = false; }
          if (ready) { pid[x - base] = nn.mk(pn.op, elemId(pn.x), elemId(pn.y)); stk.pop_back(); }
          continue;
        }
        if (kind[x] == K_NOT) {
          if (!elemReady(fa[x])) { stk.push_back(fa[x]); continue; }
          nid[x] = nn.mk(K_NOT, nid[fa[x]]); stk.pop_back();
          continue;
        }
        int ri = rootIdx[x];
        if (ri < 0) {   // absorbed node that is still needed directly (cannot happen for well-formed sets)
          if (!elemReady(fa[x])) { stk.push_back(fa[x]); ready = false; }
          if (!elemReady(fb[x])) { stk.push_back(fb[x]); ready = false; }
          if (ready) { nid[x] = nn.mk(kind[x], elemId(fa[x]), elemId(fb[x])); stk.pop_back(); }
          continue;
        }
        for (int e : sets[ri]) if (!elemReady(e)) { stk.push_back(e); ready = false; }
        if (!ready) continue;
        el.clear();
        for (int e : sets[ri]) el.push_back(elemId(e));
        u8 op = kind[x];
        int m = (int)el.size();
        while (m > 1) {
          int bi = rng.below(m), bj = rng.below(m - 1);
          if (bj >= bi) bj++;
          int r = nn.mk(op, el[bi], el[bj]);
          if (bi > bj) std::swap(bi, bj);
          el[bj] = el[m - 1]; el[bi] = r; m--;
        }
        nid[x] = el[0];
        stk.pop_back();
        if (stk.size() > (size_t)8 * (nextid + pairs.size()) + 64) die("internal: paar rebuild does not terminate");
      }
    };
    for (int k = 0; k < K; k++) {
      build(outs[k]);
      int w = nid[outs[k]];
      nn.ref[nn.outs[k]]--; nn.outs[k] = w; nn.ref[w]++;
    }
    nn.sweep();
    nn.created.clear();
    nn.simw = simw + nn.simw; nn.scanw = scanw; nn.visits = visits + (u64)ngates * 8;
    if (!nn.outputsOK()) nn.broken = true;
    return nn;
  }
};

// permute the points so that every 64-bit word is a random sample of points (makes early exits effective)
Spec permuted(const Spec& s, u64 seed) {
  if (s.P > (size_t(1) << 24)) return s;
  Spec t = s;
  std::vector<uint32_t> perm(s.P);
  for (size_t i = 0; i < s.P; i++) perm[i] = (uint32_t)i;
  Rng r(seed ^ 0xABCDEF);
  for (size_t i = s.P; i > 1; i--) std::swap(perm[i - 1], perm[r.next() % i]);
  auto doit = [&](const Col& a) {
    Col b(s.W, 0);
    for (size_t w = 0; w < s.W; w++) {
      u64 x = a[w];
      while (x) { size_t p = w * 64 + __builtin_ctzll(x); x &= x - 1; if (p < s.P) setbit(b, perm[p]); }
    }
    return b;
  };
  for (auto& c : t.in) c = doit(c);
  for (auto& c : t.tgt) c = doit(c);
  for (auto& c : t.care) c = doit(c);
  return t;
}

struct Worker {
  Net net;
  Rng rng;
  Stats st;
  int id = 0;
  double sideProb = 0.3;
  int stall = 0;
  long passes = 0;
  bool first = true;
  std::string err;

  void shareKick(const Params& P) {
    int before = net.sizeOut();
    long rk = 0;
    double sc = std::min(1.0, net.ngates / 1600.0);
    u64 budget = (u64)(P.shareWork * sc * sc) + 1000;   // small circuits get a much smaller run (a kick should cost about a pass)
    Net nn = net.share(rng, budget, P.shareGroup, nullptr, P.shareRepair, P.sharePolish, &rk, P.shareTemp);
    st.aRepair += rk;
    if (nn.broken) { err = "share produced a wrong circuit (discarded)"; return; }
    if (P.debug) { std::string why; if (!nn.check(why)) { err = "share: inconsistent network: " + why; return; } }
    if (nn.sizeOut() <= before) {
      int d = before - nn.sizeOut();
      if (d > 0) { st.aShare++; st.gShare += d; }
      net = std::move(nn);
    } else { net.simw = nn.simw; net.scanw = nn.scanw; net.visits = nn.visits; }
  }
  void kick(const Params& P) {
    if (P.shareWork > 0 && rng.below(2) == 0) { shareKick(P); return; }
    int before = net.sizeOut();
    int mode = rng.below(4) == 0 ? 1 : 0;
    Net nn = net.paar(rng, mode, rng.below(2));
    if (nn.broken) { err = "paar produced a wrong circuit (discarded)"; return; }
    if (P.debug) { std::string why; if (!nn.check(why)) { err = "paar: inconsistent network: " + why; return; } }
    if (nn.sizeOut() <= before) {
      int d = before - nn.sizeOut();
      if (d > 0) { st.aPaar++; st.gPaar += d; }
      net = std::move(nn);
    } else { net.simw = nn.simw; net.scanw = nn.scanw; net.visits = nn.visits; }
  }
  Net backup;
  std::vector<int> region;
  static void copyLight(Net& dst, Net& src) {   // copy everything except the big scratch buffer
    std::vector<u64> a1, a2;
    a1.swap(dst.alt); a2.swap(src.alt);
    dst = src;
    a2.swap(src.alt); a1.swap(dst.alt);
    if (dst.alt.size() != src.alt.size()) dst.alt.resize(src.alt.size());
  }
  void rarTrial(const Params& P) {
    net.ensureOrder();
    if (net.order.empty()) return;
    st.rarTrials++;
    int g = net.order[rng.below((uint32_t)net.order.size())];
    Net::RarCand rc;
    if (!net.rarPick(g, rng, P, rc)) { net.visits++; return; }
    st.rarCands++;
    copyLight(backup, net);
    net.visits += (u64)net.nextid * net.W / 3000 + 4;
    auto restore = [&] {
      u64 a = net.simw, b = net.scanw, c = net.visits;
      std::swap(net, backup);
      net.simw = a; net.scanw = b; net.visits = c; net.broken = false;
    };
    const int before = net.sizeOut();
    int h = net.rarApply(rc);
    if (h < 0 || net.broken) { restore(); return; }
    net.rarRegionOf(g, rc.form, region, P.rarRegion);
    Stats tmp;
    for (int sweep = 0; sweep < 2 && !net.broken; sweep++) {
      int sz = net.sizeOut();
      for (int x : region) {
        if (!net.isGate(x)) continue;
        net.tryGate(x, rng, P, false, tmp);
        if (net.broken) break;
      }
      if (net.sizeOut() == sz) break;
    }
    if (net.broken) { restore(); return; }
    if (P.debug) { std::string why; if (!net.check(why)) { err = "rar: inconsistent network: " + why; restore(); return; } }
    const int after = net.sizeOut();
    if (after < before) { st.aRar++; st.gRar += before - after; }
    else if (after == before && rng.unif() < P.rarNeutral) st.aRarSide++;
    else restore();
  }
  void pass(const Params& P, u64 deadline) {
    net.ensureOrder();
    std::vector<int> ids = net.order;
    rng.shuffle(ids);
    double sp = (first || P.level < 5) ? 0.0 : sideProb;
    for (int g : ids) {
      if (!net.isGate(g)) continue;
      bool side = sp > 0 && rng.unif() < sp;
      net.tryGate(g, rng, P, side, st);
      if (net.broken) { err = "move produced a wrong circuit"; return; }
      if (P.debug) { std::string why; if (!net.check(why)) { err = "inconsistent network: " + why; net.broken = true; return; } }
      if (net.totalWork() > deadline) break;
    }
    passes++;
    first = false;
  }
  void round(u64 budget, const Params& P) {
    u64 deadline = net.totalWork() + budget;
    while (net.totalWork() < deadline && !net.broken) {
      if (net.ngates == 0) { net.visits += budget / 3000 + 1; break; }   // nothing left to shrink
      net.visits += 16;                                                   // a pass always costs something
      int before = net.sizeOut();
      pass(P, deadline);
      if (net.broken) break;
      if (net.sizeOut() < before) stall = 0; else stall++;
      if (P.level >= 5 && P.rar > 0 && !first) {
        int nt = std::max(4, (int)(net.ngates * P.rar));
        for (int i = 0; i < nt && net.totalWork() < deadline && !net.broken; i++) rarTrial(P);
      }
      if (P.level >= 5 && (stall >= 2 || passes == 1)) { kick(P); if (stall >= 2) stall = 1; }
      if (P.level < 5 && stall >= 1) break;
    }
  }
};

double now() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

}  // namespace

int main(int argc, char** argv) {
  std::string specp, inp, outp, basis = "aon", savePrefix;
  int T = std::getenv("PNP_THREADS") ? atoi(std::getenv("PNP_THREADS")) : 1;
  double timeLimit = 10;
  long rounds = -1;
  u64 seed = 1, roundWork = 150000000ull;
  int target = -1;
  double memGB = 2.0;
  bool quiet = false, bench = false;
  double shareOnly = 0;
  Params P;
  std::vector<std::string> posargs;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto need = [&](const char* n) { if (i + 1 >= argc) die(std::string("missing value for ") + n); return std::string(argv[++i]); };
    if (a == "-o") outp = need("-o");
    else if (a == "--basis") basis = need("--basis");
    else if (a == "-j") T = atoi(need("-j").c_str());
    else if (a == "--time") timeLimit = atof(need("--time").c_str());
    else if (a == "--rounds") rounds = atol(need("--rounds").c_str());
    else if (a == "--round-work") roundWork = (u64)atof(need("--round-work").c_str());
    else if (a == "--seed") seed = strtoull(need("--seed").c_str(), nullptr, 10);
    else if (a == "--target") target = atoi(need("--target").c_str());
    else if (a == "--save") savePrefix = need("--save");
    else if (a == "--level") P.level = atoi(need("--level").c_str());
    else if (a == "--max-terms") P.maxTerms = atoi(need("--max-terms").c_str());
    else if (a == "--dfs") P.dfsBudget = atol(need("--dfs").c_str());
    else if (a == "--side-mode") P.sideMode = atoi(need("--side-mode").c_str());
    else if (a == "--side-temp") P.sideTemp = atof(need("--side-temp").c_str());
    else if (a == "--pair-every") P.pairEvery = atoi(need("--pair-every").c_str());
    else if (a == "--share-only") shareOnly = atof(need("--share-only").c_str());
    else if (a == "--share-work") P.shareWork = atof(need("--share-work").c_str());
    else if (a == "--share-group") P.shareGroup = atoi(need("--share-group").c_str());
    else if (a == "--share-repair") P.shareRepair = atof(need("--share-repair").c_str());
    else if (a == "--share-polish") P.sharePolish = atoi(need("--share-polish").c_str());
    else if (a == "--share-temp") P.shareTemp = atof(need("--share-temp").c_str());
    else if (a == "--rar") P.rar = atof(need("--rar").c_str());
    else if (a == "--rar-region") P.rarRegion = atoi(need("--rar-region").c_str());
    else if (a == "--rar-neutral") P.rarNeutral = atof(need("--rar-neutral").c_str());
    else if (a == "--pair-cap") P.pairCap = atoi(need("--pair-cap").c_str());
    else if (a == "--mem") memGB = atof(need("--mem").c_str());
    else if (a == "--debug") P.debug = true;
    else if (a == "--no-index") Net::indexAllowed = false;
    else if (a == "--bench") bench = true;
    else if (a == "-q") quiet = true;
    else if (a == "-h" || a == "--help") { posargs.clear(); break; }
    else posargs.push_back(a);
  }
  if (bench && outp.empty()) outp = "/dev/null";
  if (posargs.size() != 2 || outp.empty() || (basis != "aon" && basis != "ao")) {
    std::cerr << "usage: cktopt SPEC IN.ckt -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X] [--target SIZE]\n"
                 "              [--save PREFIX] [--level 1..5] [--rounds R] [--round-work W] [--max-terms K] [--dfs N]\n"
                 "              [--share-work W] [--share-group G] [--share-only W] [--mem GB] [--debug] [--bench] [-q]\n"
                 "              experimental: [--share-repair P --share-polish N --share-temp T] [--rar F] [--side-mode 0|1|2]\n"
                 "                            [--pair-every N] [--pair-cap N] [--no-index]      (see docs/cktopt.md)\n"
                 "  default threads: $PNP_THREADS or 1; default --time 10. Output is always re-verified before it is written.\n";
    return 2;
  }
  specp = posargs[0]; inp = posargs[1];
  T = std::max(1, std::min(T, 64));
  P.aon = basis == "aon";
  P.maxTerms = std::max(1, std::min(P.maxTerms, 8));
  double t0 = now();
  Spec spec0 = load_spec(specp);
  Circuit cin = load_circuit(inp);
  if (cin.N != spec0.N) die("circuit inputs != spec inputs");
  if ((int)cin.outs.size() != spec0.K) die("circuit output count != spec outputs");
  std::string why;
  if (!basis_ok(cin, basis, &why)) die("input circuit violates basis " + basis + ": " + why);
  Verdict v0 = verify(spec0, cin);
  if (!v0.ok) die("input circuit is wrong on " + std::to_string(v0.wrong) + " cared (output,point) pairs; nothing to shrink");
  {
    double cap0 = (double)cin.size() * 1.5 + spec0.N + 130;
    double idx = (double)spec0.P * ((cap0 + 63) / 64) * 8.0;
    if (idx > 96e6) idx = 0;                                   // the point index is only built when it is small
    double need = (cap0 * spec0.W * 16.0 + idx) * T / 1e9;
    while (T > 1 && need > memGB) { need = need / T * (T - 1); T--; }
    if (need > memGB) die("needs about " + std::to_string(need) + " GB (> --mem " + std::to_string(memGB) + ")");
  }
  Spec spec = permuted(spec0, seed);

  std::mutex mu;
  Circuit best = cin;
  int bestSize = cin.size();
  auto elapsed = [&] { return now() - t0; };
  auto offer = [&](Net& n, const char* who) -> bool {   // verify + record an improvement
    if (n.sizeOut() >= bestSize) return false;
    Circuit c = n.toCircuit();
    Verdict v = verify(spec0, c);
    std::string w2;
    if (!v.ok || !basis_ok(c, basis, &w2)) {
      std::cerr << "cktopt: INTERNAL ERROR: candidate of size " << c.size() << " failed verification (" << who << "); discarded\n";
      n.broken = true;
      return false;
    }
    best = c; bestSize = c.size();
    std::string cm = "cktopt " + specp + " basis=" + basis + " size=" + std::to_string(bestSize) + " from=" + inp;
    save_circuit(outp, best, cm);
    if (!savePrefix.empty()) save_circuit(savePrefix + "_" + std::to_string(bestSize) + "_" + basis + ".ckt", best, cm);
    return true;
  };

  std::vector<Worker> ws(T);
  {
    Net base;
    base.init(&spec, cin.size());
    base.fromCircuit(cin);
    if (!base.outputsOK()) die("internal: normalised circuit is wrong");
    if (!quiet) std::cerr << "cktopt: " << specp << " inputs=" << spec.N << " outputs=" << spec.K << " points=" << spec.P
                          << " basis=" << basis << " threads=" << T << " | input " << cin.size() << " gates, after structural cleanup "
                          << base.sizeOut() << "\n";
    offer(base, "cleanup");
    static const double sides[] = {0.3, 0.1, 0.6, 1.0, 0.2, 0.05, 0.8, 0.4};
    for (int t = 0; t < T; t++) {
      ws[t].net = base; ws[t].id = t; ws[t].rng = Rng(seed * 1000003 + t * 7919 + 17);
      ws[t].sideProb = sides[t % 8];
    }
  }
  if (shareOnly > 0) {   // only the set-space sharing optimiser, once, with the given work budget
    Net& n = ws[0].net;
    int saved = 0;
    double tb = now();
    long rk = 0;
    Net nn = n.share(ws[0].rng, (u64)shareOnly, P.shareGroup, &saved, P.shareRepair, P.sharePolish, &rk, P.shareTemp);
    std::string why2;
    bool okc = !nn.broken && nn.check(why2);
    if (!quiet || !okc) std::cerr << "cktopt: share-only: forest nodes saved " << saved << ", partner exchanges kept " << rk << ", size " << n.sizeOut() << " -> " << nn.sizeOut() << " in " << now() - tb
              << " s" << (okc ? "" : " (INCONSISTENT: " + why2 + ")") << "\n";
    if (!quiet && Net::dbgAttempts > 0) std::cerr << "cktopt: share-only: product gates " << Net::dbgProds << ", exchange attempts " << Net::dbgAttempts << ", valid " << Net::dbgValid
              << ", estimate avg " << (Net::dbgEstN ? (double)Net::dbgEstSum / Net::dbgEstN : 0.0) << " min " << Net::dbgEstMin << ", fully tried " << Net::dbgFull
              << ", average growth of rejected ones " << (Net::dbgFull - rk > 0 ? (double)Net::dbgWorse / (Net::dbgFull - rk) : 0.0) << "\n";
    if (okc) offer(nn, "share");
    save_circuit(outp, best, "cktopt " + specp + " basis=" + basis + " size=" + std::to_string(bestSize) + " from=" + inp);   // (best was verified)
    std::cout << "RESULT size=" << bestSize << " input=" << cin.size() << " basis=" << basis << " file=" << outp << "\n";
    return okc ? 0 : 1;
  }
  if (bench) {   // raw speed of the incremental evaluator (observability cone simulation) and of full gate visits
    Net& n = ws[0].net;
    n.ensureOrder();
    std::vector<int> ids = n.order;
    double tb = now(); u64 w0 = n.simw; long it = 0;
    do { for (int g : ids) { n.markTFO(g); n.computeObs(g); } it++; } while (now() - tb < 1.0);
    double dt = now() - tb;
    std::cout << "BENCH observability: " << (n.simw - w0) * 64.0 / dt << " gate*points/s, " << it * (double)ids.size() / dt
              << " cones/s, average cone " << (double)(n.simw - w0) / n.W / (it * (double)ids.size()) << " gates\n";
    Params PB = P; PB.level = std::min(P.level, 4);
    Stats sb; Rng rb(seed);
    tb = now(); long v = 0; int sz = n.ngates;
    do { n.ensureOrder(); ids = n.order; for (int g : ids) { if (n.isGate(g)) { n.tryGate(g, rb, PB, false, sb); v++; } } } while (now() - tb < 2.0 && !n.broken);
    dt = now() - tb;
    std::cout << "BENCH strict gate visits: " << v / dt << " visits/s (" << sz << " -> " << n.ngates << " gates in " << dt << " s)\n";
    return 0;
  }
  Stats total;
  u64 simw = 0, scanw = 0;
  long r = 0;
  bool stop = target >= 0 && bestSize <= target;
  double lastPrint = 0;
  for (; !stop; r++) {
    if (rounds >= 0 && r >= rounds) break;
    if (rounds < 0 && elapsed() >= timeLimit) break;
    std::vector<std::thread> th;
    for (int t = 1; t < T; t++) th.emplace_back([&, t] { ws[t].round(roundWork, P); });
    ws[0].round(roundWork, P);
    for (auto& x : th) x.join();
    // deterministic merge: lowest thread index wins ties
    int bi = -1, bs = INT_MAX;
    for (int t = 0; t < T; t++) {
      if (!ws[t].err.empty()) { std::cerr << "cktopt: thread " << t << ": " << ws[t].err << "\n"; ws[t].err.clear(); }
      if (!ws[t].net.broken && ws[t].net.sizeOut() < bs) { bs = ws[t].net.sizeOut(); bi = t; }
    }
    bool improved = false;
    if (bi >= 0 && bs < bestSize) improved = offer(ws[bi].net, "round");
    // threads that are broken or far behind restart from the best circuit
    Net* src = nullptr;
    for (int t = 0; t < T; t++) {
      bool behind = ws[t].net.sizeOut() > bestSize + (t % 3);
      if (ws[t].net.broken || behind) {
        if (bi >= 0 && !ws[bi].net.broken && ws[bi].net.sizeOut() == bestSize && bi != t) src = &ws[bi].net;
        else src = nullptr;
        u64 sw = ws[t].net.simw, cw = ws[t].net.scanw, vs = ws[t].net.visits;
        if (src) ws[t].net = *src;
        else { Net b; b.init(&spec, best.size()); b.fromCircuit(best); ws[t].net = std::move(b); }
        ws[t].net.simw = sw; ws[t].net.scanw = cw; ws[t].net.visits = vs;
        ws[t].stall = 0;
      }
    }
    if (!quiet && (improved || elapsed() - lastPrint > 5)) {
      lastPrint = elapsed();
      std::cerr << "cktopt: t=" << (long)(elapsed() * 10) / 10.0 << "s round=" << r + 1 << " best=" << bestSize << " threads:";
      for (int t = 0; t < T; t++) std::cerr << " " << ws[t].net.sizeOut();
      std::cerr << "\n";
    }
    if (target >= 0 && bestSize <= target) stop = true;
    if (bestSize == 0) stop = true;
    { bool allEmpty = true; for (int t = 0; t < T; t++) allEmpty = allEmpty && ws[t].net.ngates == 0; if (allEmpty) stop = true; }
    if (P.level < 5) { bool all = true; for (int t = 0; t < T; t++) all = all && ws[t].stall >= 1; if (all) break; }
  }
  for (int t = 0; t < T; t++) { total.add(ws[t].st); simw += ws[t].net.simw; scanw += ws[t].net.scanw; }
  // final check of what is on disk
  Circuit fin = best;
  Verdict vf = verify(spec0, fin);
  if (!vf.ok || !basis_ok(fin, basis)) die("internal: final circuit failed verification");
  save_circuit(outp, fin, "cktopt " + specp + " basis=" + basis + " size=" + std::to_string(fin.size()) + " from=" + inp);
  double el = elapsed();
  if (!quiet) {
    std::cerr << "cktopt: moves accepted (gates removed): const " << total.aConst << " (" << total.gConst << "), 0-resub " << total.aRes0
              << " (" << total.gRes0 << "), not " << total.aNot << " (" << total.gNot << "), or-cover " << total.aOr << " (" << total.gOr
              << "), and-cover " << total.aAnd << " (" << total.gAnd << "), 2-level " << total.aTwo << " (" << total.gTwo << "), paar "
              << total.aPaar << " (" << total.gPaar << "), share " << total.aShare << " (" << total.gShare << ", " << total.aRepair << " partner exchanges), size-neutral " << total.aSide << "; gate visits " << total.tries << "\n";
    if (P.rar > 0) std::cerr << "cktopt: redundancy addition: " << total.rarTrials << " trials, " << total.rarCands << " with a candidate, kept "
                             << total.aRar << " (" << total.gRar << " gates), size-neutral kept " << total.aRarSide << "\n";
    std::cerr << "cktopt: evaluator " << simw * 64.0 / el << " gate*points/s (" << simw * 64.0 / el / T << " per thread), candidate scan "
              << scanw * 64.0 / el << " wire*points/s, " << r << " rounds\n";
  }
  std::cout << "RESULT size=" << fin.size() << " input=" << cin.size() << " and=" << fin.count(AND) << " or=" << fin.count(OR)
            << " not=" << fin.count(NOT) << " basis=" << basis << " time=" << el << " file=" << outp << "\n";
  return 0;
}
