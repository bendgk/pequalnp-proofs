// sol.hpp — a full solution: exact rectangle cover + pairing of rectangles into terms + OR-ensemble, with
// journaled local-search moves and the circuit builder.
//
// Circuit shape:   OUT = OR over terms j of (S_j AND T_j)
//   solo term  (rect a)     : S = OR rows(U_a),               T = OR cols(V_a)            -> rectangle U_a x V_a
//   cross term (rects a, b) : S = OR rows(U_a) ∪ cols(V_b),   T = OR rows(U_b) ∪ cols(V_a) -> U_a x V_a  ∪  U_b x V_b
//                             (valid because U_a ∩ U_b = ∅ and V_a ∩ V_b = ∅: no full row / column appears)
// gates = (#terms ANDs) + (#terms - 1 ORs) + ensemble cost of the family {S_j, T_j}.
#pragma once
#include "cover.hpp"
#include "ensemble.hpp"

namespace gs {

struct Params {
  double t0 = 0.24, t1 = 0.09;    // temperature schedule inside a round (geometric)
  double nodePenalty = 0.02;      // tiny cost per intermediate node, breaks plateaus toward fewer nodes
  // move mix (weights)
  double wAdd = 40, wPaar = 15, wRemove = 20, wModify = 10, wSwap = 6, wPair = 2, wElem = 4, wRect = 1, wRefit = 3;
  bool allowPairs = true, allowCover = true;
  double pRepair = 0.1;           // fraction of term-changing moves that are followed by a local re-sharing pass
};

struct Sol {
  const Graph* g = nullptr;
  int n = 0, m = 0;
  std::vector<Rect> rect;
  std::vector<int> partner;      // -1 solo, else the rect it is crossed with
  std::vector<char> ralive;
  std::vector<int> rfree;
  std::vector<uint16_t> cov;
  Ens ens;
  int nTerms = 0, nRects = 0;
  // statistics
  u64 tried[10] = {0}, acc[10] = {0};

  long total() const { return nTerms == 0 ? 1 : ens.cost + 2L * nTerms - 1; }
  int inter_count() const { int c = 0; for (int id : ens.aliveList) c += ens.nd[id].tref == 0; return c; }

  void init(const Graph& gr, const std::vector<Rect>& rs, const std::vector<int>* pairing = nullptr) {
    g = &gr; n = gr.n; m = gr.m;
    rect = rs; partner.assign(rs.size(), -1); ralive.assign(rs.size(), 1);
    cov.assign((size_t)n * m, 0);
    nRects = nTerms = (int)rs.size();
    for (auto& r : rect) cov_add(r, 1);
    if (pairing)
      for (size_t a = 0; a < rect.size(); a++) {
        int b = (*pairing)[a];
        if (b > (int)a && disjoint((int)a, b)) { partner[a] = b; partner[b] = (int)a; nTerms--; }
      }
    for (size_t a = 0; a < rect.size(); a++) if (partner[a] < 0 || partner[a] > (int)a) add_term((int)a);
    ens.commit();
  }
  void cov_add(const Rect& r, int d) { r.U.each([&](int u) { r.V.each([&](int v) { cov[(size_t)u * m + v] += d; }); }); }
  bool disjoint(int a, int b) const { return (rect[a].U & rect[b].U).none() && (rect[a].V & rect[b].V).none(); }
  void term_targets(int a, B256 t[2]) const {
    int b = partner[a];
    if (b < 0) { t[0] = B256::make(rect[a].U, B128()); t[1] = B256::make(B128(), rect[a].V); }
    else { t[0] = B256::make(rect[a].U, rect[b].V); t[1] = B256::make(rect[b].U, rect[a].V); }
  }
  void add_term(int a) { B256 t[2]; term_targets(a, t); ens.add_target(t[0]); ens.add_target(t[1]); }
  void release_term(int a) { B256 t[2]; term_targets(a, t); ens.release_target(t[0]); ens.release_target(t[1]); }

  // ------------------------------------------------------------------ moves. Each returns false if not applicable;
  // otherwise it has applied the move (ens journal open) and filled `undo` so that reject() can restore the Sol level.
  struct Undo {
    int kind = 0;
    int a = -1, b = -1, c = -1, d = -1;
    int pa = -1, pb = -1, pc = -1, pd = -1;
    Rect oldRect, oldRect2;
    int dTerms = 0, dRects = 0;
  } ud;

  int rand_rect(Rng& r) const {
    if (nRects == 0) return -1;
    for (int k = 0; k < 64; k++) { int a = r.below((u32)rect.size()); if (ralive[a]) return a; }
    return -1;
  }
  static int kth_bit(const B256& s, int k) {
    for (int w = 0; w < 4; w++) {
      int c = __builtin_popcountll(s.w[w]);
      if (k < c) { u64 x = s.w[w]; while (k--) x &= x - 1; return w * 64 + __builtin_ctzll(x); }
      k -= c;
    }
    return -1;
  }
  static int kth_bit(const B128& s, int k) {
    for (int w = 0; w < 2; w++) {
      int c = __builtin_popcountll(s.w[w]);
      if (k < c) { u64 x = s.w[w]; while (k--) x &= x - 1; return w * 64 + __builtin_ctzll(x); }
      k -= c;
    }
    return -1;
  }
  B256 piece_set(int p) const { if (p >= 0) return ens.nd[p].s; B256 b; b.set(~p); return b; }

  // Start node of an ensemble move. With a non-empty `focus` (sets of recently changed targets) the walk starts at one
  // of those targets and, with some probability, descends into the node pieces of its cover.
  std::vector<B256> focus;
  int pick_node(Rng& r) {
    if (!focus.empty() && r.below(10) < 9) {
      int z = ens.find(focus[r.below((u32)focus.size())]);
      if (z >= 0) {
        while (r.below(5) < 2) {
          auto& cv = ens.nd[z].cov;
          int p = cv[r.below((u32)cv.size())];
          if (p < 0) break;
          z = p;
        }
        return z;
      }
    }
    return ens.aliveList[r.below((u32)ens.aliveList.size())];
  }
  int pick_inter(Rng& r) {
    if (!focus.empty() && r.below(10) < 9) {
      int z = ens.find(focus[r.below((u32)focus.size())]);
      if (z < 0) return -1;
      for (int k = 0; k < 4; k++) {
        auto& cv = ens.nd[z].cov;
        int p = cv[r.below((u32)cv.size())];
        if (p < 0) continue;
        z = p;
        if (ens.nd[z].tref == 0 && r.below(3) < 2) return z;
      }
      return ens.nd[z].tref == 0 ? z : -1;
    }
    for (int k = 0; k < 8; k++) { int c = ens.aliveList[r.below((u32)ens.aliveList.size())]; if (ens.nd[c].tref == 0) return c; }
    return -1;
  }

  bool mv_add(Rng& r) {            // new intermediate node from the intersection of two nodes
    if (ens.aliveList.empty()) return false;
    int z1 = pick_node(r);
    const B256 s1 = ens.nd[z1].s;
    int e = kth_bit(s1, r.below(ens.nd[z1].sz));
    auto& L = ens.elemNodes[e];
    if (L.size() < 2) return false;
    int z2 = L[r.below((u32)L.size())];
    if (z2 == z1) return false;
    B256 I = s1 & ens.nd[z2].s;
    int c = I.count();
    if (c < 2) return false;
    B256 w = I;
    u32 v = r.below(10);
    if (v >= 5 && c >= 3) {
      if (v < 8) {                 // a pair inside the intersection
        int e2 = e; while (e2 == e) e2 = kth_bit(I, r.below(c));
        w = B256(); w.set(e); w.set(e2);
      } else {                     // drop one element
        int e2 = e; while (e2 == e) e2 = kth_bit(I, r.below(c));
        w.clr(e2);
      }
    }
    if (ens.find(w) >= 0) return false;
    ens.create(w, 0, true);
    return true;
  }
  bool mv_paar(Rng& r) {           // new node = union of two pieces of one cover
    if (ens.aliveList.empty()) return false;
    int z1 = pick_node(r);
    auto& cv = ens.nd[z1].cov;
    if (cv.size() < 3) return false;
    int i = r.below((u32)cv.size()), j = r.below((u32)cv.size());
    if (i == j) return false;
    B256 w = piece_set(cv[i]) | piece_set(cv[j]);
    if (ens.find(w) >= 0) return false;
    // needs a second superset to ever pay off: cheap test through the shortest element list
    ens.create(w, 0, true);
    return true;
  }
  bool mv_remove(Rng& r) {
    if (ens.aliveList.empty()) return false;
    int z = pick_inter(r);
    if (z < 0) return false;
    ens.flag(z, 0, false); ens.remove(z);
    return true;
  }
  bool mv_modify(Rng& r) {         // replace an intermediate node by a neighbour set
    if (ens.aliveList.empty()) return false;
    int z = pick_inter(r);
    if (z < 0) return false;
    B256 s = ens.nd[z].s, w = s;
    int sz = ens.nd[z].sz;
    if (r.below(2) && sz >= 3) w.clr(kth_bit(s, r.below(sz)));
    else {
      // add an element from a random superset
      int e = kth_bit(s, r.below(sz));
      auto& L = ens.elemNodes[e];
      int z2 = L[r.below((u32)L.size())];
      if (z2 == z || !s.subset_of(ens.nd[z2].s)) return false;
      B256 x = ens.nd[z2].s.andnot(s);
      int c = x.count();
      if (c < 2) return false;      // adding the only missing element would recreate z2
      w.set(kth_bit(x, r.below(c)));
    }
    if (ens.find(w) >= 0) return false;
    ens.flag(z, 0, false); ens.remove(z);
    ens.create(w, 0, true);
    return true;
  }
  bool mv_swap(Rng& r) {           // re-pair: (a,b),(c,d) -> (a,c),(b,d)   [b or d may be absent]
    int a = rand_rect(r), c = rand_rect(r);
    if (a < 0 || c < 0 || a == c) return false;
    int b = partner[a], d = partner[c];
    if (b == c) return false;
    if (b < 0 && d < 0) return false;       // that is mv_pair
    if (!disjoint(a, c)) return false;
    if (b >= 0 && d >= 0 && !disjoint(b, d)) return false;
    ud.kind = 1; ud.a = a; ud.b = b; ud.c = c; ud.d = d; ud.dTerms = 0;
    release_term(a); release_term(c);
    partner[a] = c; partner[c] = a;
    if (b >= 0 && d >= 0) { partner[b] = d; partner[d] = b; }
    else if (b >= 0) partner[b] = -1;
    else partner[d] = -1;
    add_term(a);
    if (b >= 0) add_term(b); else add_term(d);
    return true;
  }
  bool mv_pair(Rng& r) {           // pair two solo rects, or split a pair
    int a = rand_rect(r);
    if (a < 0) return false;
    int b = partner[a];
    if (b >= 0) {
      ud.kind = 2; ud.a = a; ud.b = b; ud.dTerms = 1;
      release_term(a);
      partner[a] = partner[b] = -1;
      add_term(a); add_term(b);
      nTerms++;
      return true;
    }
    int c = rand_rect(r);
    if (c < 0 || c == a || partner[c] >= 0 || !disjoint(a, c)) return false;
    ud.kind = 3; ud.a = a; ud.b = c; ud.dTerms = -1;
    release_term(a); release_term(c);
    partner[a] = c; partner[c] = a;
    add_term(a);
    nTerms--;
    return true;
  }
  bool mv_elem(Rng& r) {           // add / remove one row or column of a rectangle
    int a = rand_rect(r);
    if (a < 0) return false;
    Rect nr = rect[a];
    int b = partner[a];
    bool rowSide = r.below(2), add = r.below(2);
    if (rowSide) {
      if (add) {
        int u = r.below(n);
        if (nr.U.get(u) || !nr.V.subset_of(g->row[u])) return false;
        if (b >= 0 && rect[b].U.get(u)) return false;
        nr.U.set(u);
      } else {
        int c = nr.U.count();
        if (c < 2) return false;
        int u = kth_bit(nr.U, r.below(c));
        bool ok = true; nr.V.each([&](int v) { if (cov[(size_t)u * m + v] < 2) ok = false; });
        if (!ok) return false;
        nr.U.clr(u);
      }
    } else {
      if (add) {
        int v = r.below(m);
        if (nr.V.get(v) || !nr.U.subset_of(g->col[v])) return false;
        if (b >= 0 && rect[b].V.get(v)) return false;
        nr.V.set(v);
      } else {
        int c = nr.V.count();
        if (c < 2) return false;
        int v = kth_bit(nr.V, r.below(c));
        bool ok = true; nr.U.each([&](int u) { if (cov[(size_t)u * m + v] < 2) ok = false; });
        if (!ok) return false;
        nr.V.clr(v);
      }
    }
    ud.kind = 4; ud.a = a; ud.oldRect = rect[a]; ud.dTerms = 0;
    release_term(a);
    cov_add(rect[a], -1); rect[a] = nr; cov_add(rect[a], 1);
    add_term(a);
    return true;
  }
  // Re-fit one target inside its don't-care interval. For the target rows(U_a) ∪ cols(V_b) of the term (a, b) (b = a
  // for a solo term) the rows of U_a whose edges in rect a are all covered twice may be dropped, rows adjacent to all
  // of V_a (and outside U_b) may be added; likewise for the columns of V_b against U_b. Any set between is a valid
  // target; take the one the existing nodes make cheapest (possibly an existing node itself).
  bool mv_refit(Rng& r) {
    int a = rand_rect(r);
    if (a < 0) return false;
    int b = partner[a];
    bool solo = b < 0;
    bool rowsOnly = false, colsOnly = false;
    if (solo) { b = a; if (r.below(2)) rowsOnly = true; else colsOnly = true; }
    const Rect &ra = rect[a], &rb = rect[b];
    B128 Lr = ra.U, Hr = ra.U, Lc = rb.V, Hc = rb.V;
    if (!colsOnly) {
      ra.U.each([&](int u) { bool red = true; ra.V.each([&](int v) { if (cov[(size_t)u * m + v] < 2) red = false; }); if (red) Lr.clr(u); });
      if (Lr.none()) Lr.set(kth_bit(ra.U, r.below(ra.U.count())));
      for (int u = 0; u < n; u++) if (!ra.U.get(u) && ra.V.subset_of(g->row[u]) && (solo || !rb.U.get(u))) Hr.set(u);
    }
    if (!rowsOnly) {
      rb.V.each([&](int v) { bool red = true; rb.U.each([&](int u) { if (cov[(size_t)u * m + v] < 2) red = false; }); if (red) Lc.clr(v); });
      if (Lc.none()) Lc.set(kth_bit(rb.V, r.below(rb.V.count())));
      for (int v = 0; v < m; v++) if (!rb.V.get(v) && rb.U.subset_of(g->col[v]) && (solo || !ra.V.get(v))) Hc.set(v);
    }
    B256 S, L, H;
    if (solo) { S = rowsOnly ? B256::make(ra.U, B128()) : B256::make(B128(), rb.V); L = rowsOnly ? B256::make(Lr, B128()) : B256::make(B128(), Lc); H = rowsOnly ? B256::make(Hr, B128()) : B256::make(B128(), Hc); }
    else { S = B256::make(ra.U, rb.V); L = B256::make(Lr, Lc); H = B256::make(Hr, Hc); }
    if (L == H) return false;
    B256 N;
    ens.flex_target(L, H, ens.find(S), N);
    if (N == S) {                   // nothing structural suggested: random single-element change inside the interval
      B256 fl = H.andnot(L);
      int c = fl.count();
      if (!c) return false;
      int e = kth_bit(fl, r.below(c));
      if (N.get(e)) N.clr(e); else N.set(e);
    }
    if (N == S) return false;
    ud.kind = 7; ud.a = a; ud.b = b; ud.oldRect = rect[a]; ud.oldRect2 = rect[b]; ud.dTerms = 0;
    release_term(a);
    cov_add(rect[a], -1); if (b != a) cov_add(rect[b], -1);
    if (!colsOnly) rect[a].U = N.rows();
    if (!rowsOnly) rect[b].V = N.cols();
    cov_add(rect[a], 1); if (b != a) cov_add(rect[b], 1);
    add_term(a);
    return true;
  }
  bool mv_rect(Rng& r) {           // delete a fully redundant rectangle, or add a new one grown from a random edge
    if (r.below(2)) {
      int a = rand_rect(r);
      if (a < 0 || nRects < 2) return false;
      bool red = true;
      rect[a].U.each([&](int u) { rect[a].V.each([&](int v) { if (cov[(size_t)u * m + v] < 2) red = false; }); });
      if (!red) return false;
      int b = partner[a];
      ud.kind = 5; ud.a = a; ud.b = b; ud.oldRect = rect[a];
      release_term(a);
      cov_add(rect[a], -1); ralive[a] = 0; partner[a] = -1; nRects--;
      if (b >= 0) { partner[b] = -1; add_term(b); ud.dTerms = 0; }   // the pair term becomes a solo term
      else { nTerms--; ud.dTerms = -1; }
      return true;
    }
    // new rectangle: random edge, random maximal-ish biclique through it, restricted to a random sub-rectangle
    int u0 = r.below(n);
    int dc = g->row[u0].count();
    if (!dc) return false;
    int v0 = kth_bit(g->row[u0], r.below(dc));
    Rect nr; nr.U.set(u0); nr.V = g->row[u0];
    int tries = 2 + r.below(6);
    for (int k = 0; k < tries; k++) {
      B128 cu = g->col[v0].andnot(nr.U);
      int c = cu.count();
      if (!c) break;
      int u = kth_bit(cu, r.below(c));
      B128 V2 = nr.V & g->row[u];
      if (V2.count() < 2) continue;
      nr.U.set(u); nr.V = V2;
    }
    if (nr.U.count() < 2 || nr.V.count() < 2) return false;
    int a;
    if (!rfree.empty()) { a = rfree.back(); rfree.pop_back(); }
    else { a = (int)rect.size(); rect.push_back(Rect()); partner.push_back(-1); ralive.push_back(0); }
    ud.kind = 6; ud.a = a; ud.dTerms = 1;
    rect[a] = nr; partner[a] = -1; ralive[a] = 1; nRects++; nTerms++;
    cov_add(nr, 1);
    add_term(a);
    return true;
  }
  void reject() {
    ens.undo();
    switch (ud.kind) {
      case 1:
        partner[ud.a] = ud.b; partner[ud.c] = ud.d;
        if (ud.b >= 0) partner[ud.b] = ud.a;
        if (ud.d >= 0) partner[ud.d] = ud.c;
        break;
      case 2: partner[ud.a] = ud.b; partner[ud.b] = ud.a; nTerms--; break;
      case 3: partner[ud.a] = -1; partner[ud.b] = -1; nTerms++; break;
      case 4: cov_add(rect[ud.a], -1); rect[ud.a] = ud.oldRect; cov_add(rect[ud.a], 1); break;
      case 5:
        rect[ud.a] = ud.oldRect; ralive[ud.a] = 1; nRects++; cov_add(rect[ud.a], 1);
        partner[ud.a] = ud.b; if (ud.b >= 0) partner[ud.b] = ud.a;
        nTerms -= ud.dTerms;
        break;
      case 6: cov_add(rect[ud.a], -1); ralive[ud.a] = 0; nRects--; nTerms--; rfree.push_back(ud.a); break;
      case 7:
        cov_add(rect[ud.a], -1); if (ud.b != ud.a) cov_add(rect[ud.b], -1);
        rect[ud.a] = ud.oldRect; if (ud.b != ud.a) rect[ud.b] = ud.oldRect2;
        cov_add(rect[ud.a], 1); if (ud.b != ud.a) cov_add(rect[ud.b], 1);
        break;
    }
    ud.kind = 0;
  }
  void accept() {
    ens.commit();
    if (ud.kind == 5) rfree.push_back(ud.a);
    ud.kind = 0;
  }

  // Local re-sharing after targets changed: for each given target, try every intersection with another node as a
  // new intermediate and keep those that lower the ensemble cost.
  std::vector<B256> repCand;
  std::vector<int> repStamp; int repTick = 0;
  void repair(const B256* tg, int nt) {
    for (int t = 0; t < nt; t++) {
      if (tg[t].count() < 3) continue;
      int z = ens.find(tg[t]);
      if (z < 0) continue;
      const B256 s = ens.nd[z].s;
      if (repStamp.size() < ens.nd.size() + 64) repStamp.resize(ens.nd.size() + 1024, 0);
      repTick++;
      repCand.clear();
      s.each([&](int e) {
        for (int y : ens.elemNodes[e]) {
          if (y == z || repStamp[y] == repTick) continue;
          repStamp[y] = repTick;
          B256 I = s & ens.nd[y].s;
          if (I.count() < 2 || I == ens.nd[y].s || I == s) continue;
          if (ens.find(I) >= 0) continue;
          bool dup = false;
          for (auto& c : repCand) if (c == I) { dup = true; break; }
          if (!dup) repCand.push_back(I);
        }
      });
      std::sort(repCand.begin(), repCand.end(), [](const B256& a, const B256& b) { int ca = a.count(), cb = b.count(); if (ca != cb) return ca > cb; for (int k = 3; k >= 0; k--) if (a.w[k] != b.w[k]) return a.w[k] < b.w[k]; return false; });
      for (auto& I : repCand) {
        if (ens.find(I) >= 0) continue;
        size_t mk = ens.mark(); long before = ens.cost;
        ens.create(I, 0, true);
        if (ens.cost >= before) ens.undo_to(mk);
      }
    }
  }
  void repair_terms(Rng& r, const Params& P, int a, int b) {
    if (P.pRepair <= 0 || r.uni() >= P.pRepair) return;
    B256 t[4]; int k = 0;
    if (a >= 0 && ralive[a]) { term_targets(a, t + k); k += 2; }
    if (b >= 0 && ralive[b] && b != a && partner[a] != b) { term_targets(b, t + k); k += 2; }
    repair(t, k);
  }

  // one annealing step at temperature T. Returns true if a move was evaluated.
  bool step(Rng& r, double T, const Params& P) {
    double tot = P.wAdd + P.wPaar + P.wRemove + P.wModify + (P.allowPairs ? P.wSwap + P.wPair : 0) + (P.allowCover ? P.wElem + P.wRect + P.wRefit : 0);
    double x = r.uni() * tot;
    int kind;
    long before = total();
    int ib = (int)ens.aliveList.size();
    ud.kind = 0;
    bool ok;
    if ((x -= P.wAdd) < 0) { kind = 0; ok = mv_add(r); }
    else if ((x -= P.wPaar) < 0) { kind = 1; ok = mv_paar(r); }
    else if ((x -= P.wRemove) < 0) { kind = 2; ok = mv_remove(r); }
    else if ((x -= P.wModify) < 0) { kind = 3; ok = mv_modify(r); }
    else if (P.allowPairs && (x -= P.wSwap) < 0) { kind = 4; ok = mv_swap(r); }
    else if (P.allowPairs && (x -= P.wPair) < 0) { kind = 5; ok = mv_pair(r); }
    else if (P.allowCover && (x -= P.wElem) < 0) { kind = 6; ok = mv_elem(r); }
    else if (P.allowCover && (x -= P.wRefit) < 0) { kind = 8; ok = mv_refit(r); }
    else if (P.allowCover) { kind = 7; ok = mv_rect(r); }
    else return false;
    if (!ok) return false;
    if (kind >= 4 && kind != 8) {  // targets changed: optionally re-share around the touched terms
      if (ud.kind == 1) repair_terms(r, P, ud.a, ud.b >= 0 ? ud.b : ud.d);
      else if (ud.kind == 2 || ud.kind == 3) repair_terms(r, P, ud.a, ud.b);
      else if (ud.kind == 4 || ud.kind == 6) repair_terms(r, P, ud.a, -1);
      else if (ud.kind == 5 && ud.b >= 0) repair_terms(r, P, ud.b, -1);
    }
    tried[kind]++;
    double d = (double)(total() - before) + P.nodePenalty * ((int)ens.aliveList.size() - ib);
    if (d <= 0 || r.uni() < std::exp(-d / T)) { accept(); acc[kind]++; }
    else reject();
    return true;
  }

  // ------------------------------------------------------------------ large-neighbourhood step on the term level:
  // apply one re-pairing / cover move unconditionally, re-share around the touched targets (repair pass + `steps`
  // focused ensemble moves at temperature T), and report the new total. The caller keeps a copy to roll back.
  bool lns_move(Rng& r, const Params& P, long steps, double T) {
    ud.kind = 0;
    bool ok;
    u32 v = r.below(100);
    if (!P.allowPairs) v = 95;
    if (v < 80) ok = mv_swap(r);
    else if (v < 90 || !P.allowCover) ok = mv_pair(r);
    else ok = mv_elem(r);
    if (!ok) return false;
    B256 t[8]; int k = 0;
    auto addT = [&](int a) { if (a >= 0 && ralive[a]) { bool dup = false; B256 x[2]; term_targets(a, x); for (int i = 0; i < k; i++) if (t[i] == x[0] || t[i] == x[1]) dup = true; if (!dup && k + 2 <= 8) { t[k++] = x[0]; t[k++] = x[1]; } } };
    addT(ud.a); addT(ud.b); addT(ud.c); addT(ud.d);
    repair(t, k);
    accept();
    focus.assign(t, t + k);
    Params Q = P; Q.allowPairs = false; Q.allowCover = false;
    for (long i = 0; i < steps; i++) step(r, T, Q);
    focus.clear();
    return true;
  }

  // ------------------------------------------------------------------ pairing by a fast proxy (QAP-style annealing).
  // Each cross set is U_a ∪ V_partner(a). Two cross sets that share k >= 2 elements can share a k-element node, so
  // the proxy maximises  sum over pairs of sets of f(|overlap|)  with f convex (concentrated overlaps pay more per
  // element). Only applied to a state in which every rectangle is still a solo term. Returns the proxy value.
  double pair_proxy(Rng& r, long iters, const double* f /*[0..8]*/) {
    int R = (int)rect.size();
    if (R < 4) return 0;
    std::vector<uint8_t> ou((size_t)R * R), ov((size_t)R * R);
    for (int a = 0; a < R; a++) for (int c = 0; c < R; c++) {
      ou[(size_t)a * R + c] = (uint8_t)std::min(8, (rect[a].U & rect[c].U).count());
      ov[(size_t)a * R + c] = (uint8_t)std::min(8, (rect[a].V & rect[c].V).count());
    }
    auto ok = [&](int a, int b) { return a != b && ou[(size_t)a * R + b] == 0 && ov[(size_t)a * R + b] == 0; };
    std::vector<int> pr(R, -1);
    // random greedy perfect-ish matching on the "disjoint" graph
    std::vector<int> ord(R);
    for (int i = 0; i < R; i++) ord[i] = i;
    for (int i = R; i > 1; i--) std::swap(ord[i - 1], ord[r.below(i)]);
    for (int i = 0; i < R; i++) {
      int a = ord[i];
      if (pr[a] >= 0) continue;
      for (int j = i + 1; j < R; j++) { int b = ord[j]; if (pr[b] < 0 && ok(a, b)) { pr[a] = b; pr[b] = a; break; } }
    }
    // contribution of the set of atom a (U_a ∪ V_pr[a]) against all other sets; unpaired atoms have pure sets and
    // are ignored by the proxy
    auto fo = [&](int k) { return f[k > 8 ? 8 : k]; };
    auto contrib = [&](int a) {
      double s = 0; int b = pr[a];
      if (b < 0) return s;
      const uint8_t* oua = &ou[(size_t)a * R]; const uint8_t* ovb = &ov[(size_t)b * R];
      for (int c = 0; c < R; c++) { int d = pr[c]; if (c == a || d < 0) continue; s += fo(oua[c] + ovb[d]); }
      return s;
    };
    double bonus = 4 * f[8] + 10;   // every cross pair is worth more than any overlap pattern: maximise #pairs first
    double phi = 0;
    for (int a = 0; a < R; a++) phi += contrib(a);
    phi /= 2;
    for (int a = 0; a < R; a++) if (pr[a] > a) phi += bonus;
    double best = phi; std::vector<int> bestPr = pr;
    double T0 = 2.0, T1 = 0.05, ratio = std::log(T1 / T0);
    int tch[4], old[4];
    for (long it = 0; it < iters; it++) {
      int a = r.below(R), c = r.below(R);
      if (a == c) continue;
      int b = pr[a], d = pr[c];
      if (b == c) continue;
      if (b < 0 && d >= 0) { std::swap(a, c); std::swap(b, d); }    // now: a paired or both solo
      int nt = 0;
      double dBonus = 0;
      if (b >= 0 && d >= 0) {
        if (r.below(2)) std::swap(c, d);              // (a,b),(c,d) -> (a,c),(b,d)
        if (!ok(a, c) || !ok(b, d)) continue;
        tch[0] = a; tch[1] = b; tch[2] = c; tch[3] = d; nt = 4;
      } else if (b >= 0) {                            // (a,b), c solo -> (a,c), b solo   or  (b,c), a solo
        if (r.below(2)) std::swap(a, b);
        if (!ok(a, c)) continue;
        tch[0] = a; tch[1] = b; tch[2] = c; nt = 3;
      } else {                                        // two solos -> a pair
        if (!ok(a, c)) continue;
        tch[0] = a; tch[1] = c; nt = 2; dBonus = bonus;
      }
      double before = 0;
      for (int k = 0; k < nt; k++) { before += contrib(tch[k]); old[k] = pr[tch[k]]; }
      if (nt == 4) { pr[a] = c; pr[c] = a; pr[b] = d; pr[d] = b; }
      else if (nt == 3) { pr[a] = c; pr[c] = a; pr[b] = -1; }
      else { pr[a] = c; pr[c] = a; }
      double after = 0;
      for (int k = 0; k < nt; k++) after += contrib(tch[k]);
      // pairs among the touched sets are counted twice in `before`/`after`; that only rescales their weight
      double dl = after - before + dBonus, T = T0 * std::exp(ratio * (double)it / (double)iters);
      if (dl >= 0 || r.uni() < std::exp(dl / T)) { phi += dl; if (phi > best) { best = phi; bestPr = pr; } }
      else for (int k = 0; k < nt; k++) pr[tch[k]] = old[k];
    }
    pr = bestPr;
    // install the pairing
    for (int a = 0; a < R; a++) {
      int b = pr[a];
      if (b < 0 || b < a || !ralive[a] || !ralive[b] || partner[a] >= 0 || partner[b] >= 0 || !disjoint(a, b)) continue;
      release_term(a); release_term(b);
      partner[a] = b; partner[b] = a;
      add_term(a);
      nTerms--;
      ens.commit();
    }
    return best;
  }

  // ------------------------------------------------------------------ greedy initialisation (Paar-style): repeatedly
  // create the union of the two pieces that co-occur in the most covers (random tie-break), while that saves gates.
  void greedy_pairs(Rng& r) {
    std::unordered_map<u64, int> cnt;
    for (;;) {
      cnt.clear();
      for (int id : ens.aliveList) {
        auto& cv = ens.nd[id].cov;
        for (size_t i = 0; i < cv.size(); i++) for (size_t j = i + 1; j < cv.size(); j++) {
          u64 a = (u64)(cv[i] + 1000), b = (u64)(cv[j] + 1000);
          if (a > b) std::swap(a, b);
          cnt[(a << 32) | b]++;
        }
      }
      int best = 1; std::vector<u64> ties;
      for (auto& [k, c] : cnt) { if (c > best) { best = c; ties.clear(); } if (c == best && c >= 2) ties.push_back(k); }
      if (ties.empty()) break;
      std::sort(ties.begin(), ties.end());
      u64 k = ties[r.below((u32)ties.size())];
      int p = (int)(k >> 32) - 1000, q = (int)(k & 0xffffffffu) - 1000;
      B256 w = piece_set(p) | piece_set(q);
      if (ens.find(w) >= 0) break;   // cannot happen with exact covers, guard against loops
      long before = ens.cost;
      ens.create(w, 0, true);
      if (ens.cost >= before) { ens.undo(); break; }
      ens.commit();
    }
  }
  // drop intermediates that do not pay for themselves (cost-neutral or worse), repeat until stable
  void cleanup() {
    for (bool ch = true; ch;) {
      ch = false;
      std::vector<int> ids(ens.aliveList);
      std::sort(ids.begin(), ids.end());
      for (int z : ids) {
        if (!ens.nd[z].alive || ens.nd[z].tref != 0) continue;
        long before = ens.cost;
        ens.flag(z, 0, false); ens.remove(z);
        if (ens.cost <= before) { ens.commit(); ch = true; }
        else ens.undo();
      }
    }
  }

  // ------------------------------------------------------------------ checks and circuit construction
  bool valid(std::string* why = nullptr) const {
    std::vector<uint16_t> c2((size_t)n * m, 0);
    int terms = 0, rects = 0;
    for (size_t a = 0; a < rect.size(); a++) {
      if (!ralive[a]) continue;
      rects++;
      if (!is_biclique(*g, rect[a]) || rect[a].U.none() || rect[a].V.none()) { if (why) *why = "rect is not a biclique"; return false; }
      rect[a].U.each([&](int u) { rect[a].V.each([&](int v) { c2[(size_t)u * m + v]++; }); });
      int b = partner[a];
      if (b < 0) terms++;
      else {
        if (!ralive[b] || partner[b] != (int)a || !disjoint((int)a, b)) { if (why) *why = "bad pairing"; return false; }
        if ((int)a < b) terms++;
      }
    }
    if (c2 != cov) { if (why) *why = "cover counts out of date"; return false; }
    for (int u = 0; u < n; u++) for (int v = 0; v < m; v++) if ((c2[(size_t)u * m + v] > 0) != g->adj(u, v)) { if (why) *why = "not an exact cover"; return false; }
    if (terms != nTerms || rects != nRects) { if (why) *why = "term/rect count mismatch"; return false; }
    // every target must be an alive node with the right reference count
    std::unordered_map<B256, int, B256Hash> refs;
    for (size_t a = 0; a < rect.size(); a++) {
      if (!ralive[a] || (partner[a] >= 0 && partner[a] < (int)a)) continue;
      B256 t[2]; term_targets((int)a, t);
      for (int k = 0; k < 2; k++) if (t[k].count() >= 2) refs[t[k]]++;
    }
    for (auto& [s, c] : refs) { int id = ens.find(s); if (id < 0 || ens.nd[id].tref != c) { if (why) *why = "target refcount mismatch"; return false; } }
    for (int id : ens.aliveList) if (ens.nd[id].tref > 0 && !refs.count(ens.nd[id].s)) { if (why) *why = "stale target"; return false; }
    return ens.check(why);
  }

  pnp::Circuit build() const {
    pnp::Circuit c; c.N = n + m;
    auto ew = [&](int e) { return e < 128 ? e : n + (e - 128); };
    std::vector<int> ids(ens.aliveList);
    std::sort(ids.begin(), ids.end(), [&](int a, int b) { return ens.nd[a].sz != ens.nd[b].sz ? ens.nd[a].sz < ens.nd[b].sz : a < b; });
    std::vector<int> wire(ens.nd.size(), -1);
    auto emit = [&](pnp::Op op, int a, int b) { pnp::Gate gt; gt.op = op; gt.nin = 2; gt.a = a; gt.b = b; c.gates.push_back(gt); return c.N + (int)c.gates.size() - 1; };
    for (int id : ids) {
      auto& cv = ens.nd[id].cov;
      int w = -1;
      for (int p : cv) { int pw = p >= 0 ? wire[p] : ew(~p); w = w < 0 ? pw : emit(pnp::OR, w, pw); }
      wire[id] = w;
    }
    auto tw = [&](const B256& t) { if (t.count() == 1) return ew(t.first()); return wire[ens.find(t)]; };
    int acc = -1;
    for (size_t a = 0; a < rect.size(); a++) {
      if (!ralive[a] || (partner[a] >= 0 && partner[a] < (int)a)) continue;
      B256 t[2]; term_targets((int)a, t);
      int x = emit(pnp::AND, tw(t[0]), tw(t[1]));
      acc = acc < 0 ? x : emit(pnp::OR, acc, x);
    }
    if (acc < 0) { pnp::Gate gt; gt.op = pnp::OR; gt.nin = 0; c.gates.push_back(gt); acc = c.N; }   // empty graph: constant false
    c.outs.push_back(acc);
    return c;
  }
};

}  // namespace gs
