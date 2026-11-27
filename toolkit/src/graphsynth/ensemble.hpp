// ensemble.hpp — OR-ensemble optimiser.
//
// Ground set: rows ⊎ columns (B256). A "node" is a set of >= 2 ground elements for which the final circuit has a wire
// (the OR of its elements). Every alive node z is built as the OR of a COVER: nodes that are proper subsets of z plus
// single ground elements, costing |cover| - 1 OR gates. Covers are exact minimum covers over the alive node set
// (branch & bound, capped), so the total cost  sum_z (|cover(z)| - 1)  is a function of the node set alone and the
// search is a walk over node sets (add / remove a node), fully journaled so that any move can be undone.
// Target nodes carry a reference count (tref); intermediate nodes carry the `inter` flag.
#pragma once
#include "gs_common.hpp"

namespace gs {

struct Ens {
  struct Node {
    B256 s;
    int sz = 0, first = -1;
    int tref = 0;
    bool inter = false, alive = false;
    int uses = 0;            // number of alive covers that use this node as a piece
    int apos = -1;           // position in aliveList
    std::vector<int> cov;    // pieces: >= 0 node id, < 0 ground element ~e
  };
  std::vector<Node> nd;
  std::vector<int> freeIds, aliveList;
  std::vector<int> ht;       // open addressing: -1 empty, -2 tombstone, else node id
  size_t htMask = 0, htUsed = 0;
  std::vector<int> elemNodes[256];
  long cost = 0;             // sum over alive nodes of |cov| - 1
  size_t bbLimit = 4000;     // branch & bound node cap per cover
  u64 nCover = 0;            // statistics: covers computed

  // journal
  enum { J_COVER, J_CREATE, J_REMOVE, J_FLAG };
  struct JE { int type, id, a, b, off, len; };
  std::vector<JE> jr;
  std::vector<int> jpool, pendingFree;

  Ens() { ht.assign(1 << 13, -1); htMask = ht.size() - 1; nd.reserve(4096); jr.reserve(1024); jpool.reserve(1 << 14); for (auto& v : elemNodes) v.reserve(64); }

  // ---------------- hash table
  int find(const B256& s) const {
    size_t h = s.hash() & htMask;
    for (;;) {
      int v = ht[h];
      if (v == -1) return -1;
      if (v >= 0 && nd[v].s == s) return v;
      h = (h + 1) & htMask;
    }
  }
  void ht_rebuild(size_t cap) {
    ht.assign(cap, -1); htMask = cap - 1; htUsed = 0;
    for (int id : aliveList) ht_insert(id);
  }
  void ht_insert(int id) {
    if ((htUsed + 1) * 2 > ht.size()) ht_rebuild(aliveList.size() * 4 > ht.size() ? ht.size() * 2 : ht.size());
    size_t h = nd[id].s.hash() & htMask;
    while (ht[h] >= 0) h = (h + 1) & htMask;
    if (ht[h] == -1) htUsed++;
    ht[h] = id;
  }
  void ht_erase(int id) {
    size_t h = nd[id].s.hash() & htMask;
    while (ht[h] != id) h = (h + 1) & htMask;
    ht[h] = -2;
  }

  // ---------------- registration (no journaling here)
  void reg(int id) {
    Node& x = nd[id];
    x.alive = true;
    ht_insert(id);           // before aliveList.push_back: a rebuild re-inserts exactly the alive list
    x.apos = (int)aliveList.size(); aliveList.push_back(id);
    x.s.each([&](int e) { elemNodes[e].push_back(id); });
    cost += (long)x.cov.size() - 1;
    for (int p : x.cov) if (p >= 0) nd[p].uses++;
  }
  void unreg(int id) {
    Node& x = nd[id];
    x.alive = false;
    int last = aliveList.back(); aliveList[x.apos] = last; nd[last].apos = x.apos; aliveList.pop_back(); x.apos = -1;
    ht_erase(id);
    x.s.each([&](int e) { auto& v = elemNodes[e]; for (size_t i = 0; i < v.size(); i++) if (v[i] == id) { v[i] = v.back(); v.pop_back(); break; } });
    cost -= (long)x.cov.size() - 1;
    for (int p : x.cov) if (p >= 0) nd[p].uses--;
  }
  void set_cover(int id, const int* pc, int n) {
    Node& x = nd[id];
    for (int p : x.cov) if (p >= 0) nd[p].uses--;
    cost += (long)n - (long)x.cov.size();
    x.cov.assign(pc, pc + n);
    for (int p : x.cov) if (p >= 0) nd[p].uses++;
  }
  void j_cover(int id) {
    Node& x = nd[id];
    jr.push_back({J_COVER, id, 0, 0, (int)jpool.size(), (int)x.cov.size()});
    jpool.insert(jpool.end(), x.cov.begin(), x.cov.end());
  }

  // ---------------- exact minimum cover of the set z by alive proper-subset nodes + singletons
  struct Scratch {
    std::vector<int> cid, csz, order, pick, bestPick, out;
    std::vector<u64> cm;
    std::vector<B256> cb;
    size_t bb = 0;
  } sc;
  int bbBest = 0;
  void bb_rec(int i, u64 covered, int gain, int depth, u64 full, int nc) {
    if (++sc.bb > bbLimit) return;
    int rem = __builtin_popcountll(full & ~covered);
    if (rem < 2) return;
    for (int j = i; j < nc; j++) {
      int mx = sc.csz[j] < rem ? sc.csz[j] : rem;       // candidates are sorted by size, descending
      if (mx < 2) return;
      if (gain + rem - (rem + mx - 1) / mx <= bbBest) return;
      int marg = __builtin_popcountll(sc.cm[j] & ~covered);
      if (marg < 2) continue;
      if ((int)sc.pick.size() <= depth) sc.pick.resize(depth + 1);
      sc.pick[depth] = j;
      int ng = gain + marg - 1;
      if (ng > bbBest) { bbBest = ng; sc.bestPick.assign(sc.pick.begin(), sc.pick.begin() + depth + 1); }
      bb_rec(j + 1, covered | sc.cm[j], ng, depth + 1, full, nc);
      if (sc.bb > bbLimit) return;
    }
  }
  // result in sc.out
  void compute_cover(const B256& z, int zsz) {
    nCover++;
    sc.cid.clear(); sc.cb.clear(); sc.csz.clear();
    z.each([&](int e) {
      for (int w : elemNodes[e]) {
        const Node& x = nd[w];
        if (x.first == e && x.sz < zsz && x.s.subset_of(z)) { sc.cid.push_back(w); }
      }
    });
    int nc = (int)sc.cid.size();
    sc.out.clear();
    if (nc == 0) { z.each([&](int e) { sc.out.push_back(~e); }); return; }
    // sort candidates by size desc, then id (deterministic)
    std::sort(sc.cid.begin(), sc.cid.end(), [&](int a, int b) { return nd[a].sz != nd[b].sz ? nd[a].sz > nd[b].sz : a < b; });
    if (zsz <= 64) {
      // compress to local indices
      int loc[256]; int k = 0; int elems[64];
      z.each([&](int e) { loc[e] = k; elems[k] = e; k++; });
      u64 full = zsz == 64 ? ~u64(0) : ((u64(1) << zsz) - 1);
      sc.cm.resize(nc); sc.csz.resize(nc);
      for (int i = 0; i < nc; i++) { u64 mk = 0; nd[sc.cid[i]].s.each([&](int e) { mk |= u64(1) << loc[e]; }); sc.cm[i] = mk; sc.csz[i] = nd[sc.cid[i]].sz; }
      // greedy start
      u64 covered = 0; int gain = 0; sc.bestPick.clear();
      for (;;) {
        int bj = -1, bm = 1;
        for (int j = 0; j < nc; j++) { int mg = __builtin_popcountll(sc.cm[j] & ~covered); if (mg > bm) { bm = mg; bj = j; } }
        if (bj < 0) break;
        covered |= sc.cm[bj]; gain += bm - 1; sc.bestPick.push_back(bj);
      }
      bbBest = gain;
      if (nc > 1) { sc.bb = 0; bb_rec(0, 0, 0, 0, full, nc); }
      covered = 0;
      for (int j : sc.bestPick) { sc.out.push_back(sc.cid[j]); covered |= sc.cm[j]; }
      u64 rest = full & ~covered;
      while (rest) { int b = __builtin_ctzll(rest); rest &= rest - 1; sc.out.push_back(~elems[b]); }
    } else {
      // large set: greedy only
      B256 covered;
      for (;;) {
        int bj = -1, bm = 1;
        for (int j = 0; j < nc; j++) { int mg = nd[sc.cid[j]].s.andnot(covered).count(); if (mg > bm) { bm = mg; bj = j; } }
        if (bj < 0) break;
        covered = covered | nd[sc.cid[bj]].s; sc.out.push_back(sc.cid[bj]);
      }
      z.andnot(covered).each([&](int e) { sc.out.push_back(~e); });
    }
  }

  // Flexible target: the cheapest set S' with L ⊆ S' ⊆ H given the alive nodes. If a single alive node w (other than
  // `exclude`) satisfies L ⊆ w ⊆ H it is returned (the target then costs nothing extra); otherwise S' = L ∪ (union of
  // the nodes ⊆ H that give the best cover of L). Returns false if nothing better than L itself is suggested.
  bool flex_target(const B256& L, const B256& H, int exclude, B256& out) {
    int lsz = L.count();
    out = L;
    if (lsz < 2) return false;
    sc.cid.clear();
    int single = -1;
    L.each([&](int e) {
      for (int w : elemNodes[e]) {
        if (w == exclude) continue;
        const Node& x = nd[w];
        if (!x.s.subset_of(H)) continue;
        B256 I = x.s & L;
        if (I.first() != e) continue;
        int ic = I.count();
        if (ic == lsz) { if (single < 0 || x.sz < nd[single].sz || (x.sz == nd[single].sz && w < single)) single = w; }
        else if (ic >= 2) sc.cid.push_back(w);
      }
    });
    if (single >= 0) { out = nd[single].s; return true; }
    int nc = (int)sc.cid.size();
    if (nc == 0 || lsz > 64) return false;
    std::sort(sc.cid.begin(), sc.cid.end(), [&](int a, int b) { int ca = (nd[a].s & L).count(), cb = (nd[b].s & L).count(); return ca != cb ? ca > cb : a < b; });
    int loc[256]; int k = 0;
    L.each([&](int e) { loc[e] = k++; });
    u64 full = lsz == 64 ? ~u64(0) : ((u64(1) << lsz) - 1);
    sc.cm.resize(nc); sc.csz.resize(nc);
    for (int i = 0; i < nc; i++) { u64 mk = 0; (nd[sc.cid[i]].s & L).each([&](int e) { mk |= u64(1) << loc[e]; }); sc.cm[i] = mk; sc.csz[i] = __builtin_popcountll(mk); }
    u64 covered = 0; int gain = 0; sc.bestPick.clear();
    for (;;) {
      int bj = -1, bm = 1;
      for (int j = 0; j < nc; j++) { int mg = __builtin_popcountll(sc.cm[j] & ~covered); if (mg > bm) { bm = mg; bj = j; } }
      if (bj < 0) break;
      covered |= sc.cm[bj]; gain += bm - 1; sc.bestPick.push_back(bj);
    }
    bbBest = gain;
    if (nc > 1) { sc.bb = 0; bb_rec(0, 0, 0, 0, full, nc); }
    for (int j : sc.bestPick) out = out | nd[sc.cid[j]].s;
    return out != L;
  }

  // ---------------- journaled operations
  int new_id() {
    if (!freeIds.empty()) { int id = freeIds.back(); freeIds.pop_back(); return id; }
    nd.emplace_back(); nd.back().cov.reserve(24);
    return (int)nd.size() - 1;
  }
  std::vector<int> tmpIds;
  // creates the node for set s (must not exist, |s| >= 2); re-optimises the covers of its supersets.
  int create(const B256& s, int tref, bool inter) {
    int id = new_id();
    Node& x = nd[id];
    x.s = s; x.sz = s.count(); x.first = s.first(); x.tref = tref; x.inter = inter; x.uses = 0;
    compute_cover(s, x.sz);
    nd[id].cov.assign(sc.out.begin(), sc.out.end());
    reg(id);
    jr.push_back({J_CREATE, id, 0, 0, (int)jpool.size(), 0});
    // supersets: scan the shortest element list
    int be = -1; size_t bl = ~size_t(0);
    s.each([&](int e) { if (elemNodes[e].size() < bl) { bl = elemNodes[e].size(); be = e; } });
    tmpIds.assign(elemNodes[be].begin(), elemNodes[be].end());
    int sz = nd[id].sz;
    for (int z : tmpIds) {
      if (z == id) continue;
      Node& y = nd[z];
      if (y.sz <= sz || !s.subset_of(y.s)) continue;
      compute_cover(y.s, y.sz);
      if (sc.out.size() < nd[z].cov.size()) { j_cover(z); set_cover(z, sc.out.data(), (int)sc.out.size()); }
    }
    return id;
  }
  // removes node id; covers that used it are recomputed.
  void remove(int id) {
    B256 s = nd[id].s; int sz = nd[id].sz;
    int be = -1; size_t bl = ~size_t(0);
    s.each([&](int e) { if (elemNodes[e].size() < bl) { bl = elemNodes[e].size(); be = e; } });
    tmpIds.clear();
    if (nd[id].uses > 0)
      for (int z : elemNodes[be]) {
        if (z == id) continue;
        Node& y = nd[z];
        if (y.sz <= sz) continue;
        for (int p : y.cov) if (p == id) { tmpIds.push_back(z); break; }
      }
    unreg(id);
    jr.push_back({J_REMOVE, id, 0, 0, (int)jpool.size(), 0});
    pendingFree.push_back(id);
    for (int z : tmpIds) {
      Node& y = nd[z];
      compute_cover(y.s, y.sz);
      j_cover(z); set_cover(z, sc.out.data(), (int)sc.out.size());
    }
  }
  void flag(int id, int tref, bool inter) {
    jr.push_back({J_FLAG, id, nd[id].tref, nd[id].inter ? 1 : 0, (int)jpool.size(), 0});
    nd[id].tref = tref; nd[id].inter = inter;
  }
  void add_target(const B256& s) {
    if (s.count() < 2) return;
    int id = find(s);
    if (id >= 0) flag(id, nd[id].tref + 1, nd[id].inter);
    else create(s, 1, false);
  }
  void release_target(const B256& s) {
    if (s.count() < 2) return;
    int id = find(s);
    assert(id >= 0 && nd[id].tref > 0);
    if (nd[id].tref > 1 || nd[id].inter) { flag(id, nd[id].tref - 1, nd[id].inter); return; }
    if (nd[id].uses > 0) { flag(id, 0, true); return; }   // still useful as an intermediate
    flag(id, 0, false);
    remove(id);
  }
  size_t mark() const { return jr.size(); }
  void commit() {
    jr.clear(); jpool.clear();
    for (int id : pendingFree) freeIds.push_back(id);
    pendingFree.clear();
  }
  // undo every journal entry from `mark` on (mark = 0: the whole open move)
  void undo_to(size_t mark) {
    if (mark >= jr.size()) return;
    for (size_t k = jr.size(); k-- > mark;) {
      JE& e = jr[k];
      switch (e.type) {
        case J_COVER: set_cover(e.id, jpool.data() + e.off, e.len); break;
        case J_CREATE: unreg(e.id); nd[e.id].cov.clear(); freeIds.push_back(e.id); break;
        case J_REMOVE:
          reg(e.id);
          for (size_t q = pendingFree.size(); q-- > 0;) if (pendingFree[q] == e.id) { pendingFree.erase(pendingFree.begin() + q); break; }
          break;
        case J_FLAG: nd[e.id].tref = e.a; nd[e.id].inter = e.b != 0; break;
      }
    }
    jpool.resize(jr[mark].off);
    jr.resize(mark);
  }
  void undo() { undo_to(0); jr.clear(); jpool.clear(); pendingFree.clear(); }

  // ---------------- consistency check (debug) : recomputes everything from scratch
  bool check(std::string* why = nullptr) const {
    long c = 0;
    std::vector<int> uses(nd.size(), 0);
    for (int id : aliveList) {
      const Node& x = nd[id];
      B256 u;
      for (int p : x.cov) {
        if (p >= 0) {
          if (!nd[p].alive || nd[p].sz >= x.sz || !nd[p].s.subset_of(x.s)) { if (why) *why = "bad piece"; return false; }
          u = u | nd[p].s; uses[p]++;
        } else u.set(~p);
      }
      if (u != x.s) { if (why) *why = "cover does not equal set"; return false; }
      c += (long)x.cov.size() - 1;
      if (x.tref == 0 && !x.inter) { if (why) *why = "alive node without owner"; return false; }
    }
    if (c != cost) { if (why) *why = "cost mismatch"; return false; }
    for (int id : aliveList) if (uses[id] != nd[id].uses) { if (why) *why = "uses mismatch"; return false; }
    return true;
  }
};

}  // namespace gs
