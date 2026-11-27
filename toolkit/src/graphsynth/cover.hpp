// cover.hpp — initial biclique covers (exact covers of the edge set by rectangles U x V inside the graph).
#pragma once
#include "bicliq.hpp"

namespace gs {

inline std::vector<Rect> row_stars(const Graph& g) {
  std::vector<Rect> r;
  for (int u = 0; u < g.n; u++) if (g.row[u].any()) { Rect x; x.U.set(u); x.V = g.row[u]; r.push_back(x); }
  return r;
}
inline std::vector<Rect> col_stars(const Graph& g) {
  std::vector<Rect> r;
  for (int v = 0; v < g.m; v++) if (g.col[v].any()) { Rect x; x.V.set(v); x.U = g.col[v]; r.push_back(x); }
  return r;
}

// remove rectangles all of whose edges are covered at least twice (heaviest first)
inline void prune_redundant(const Graph& g, std::vector<Rect>& sol, CovCount& cc) {
  for (bool ch = true; ch;) {
    ch = false;
    int bi = -1, bw = -1;
    for (size_t i = 0; i < sol.size(); i++) {
      bool red = true;
      sol[i].U.each([&](int u) { sol[i].V.each([&](int v) { if (cc.at(u, v) < 2) red = false; }); });
      int w = sol[i].U.count() + sol[i].V.count();
      if (red && w > bw) { bw = w; bi = (int)i; }
    }
    if (bi >= 0) { cc.add(sol[bi], -1); sol.erase(sol.begin() + bi); ch = true; }
  }
}
// drop single rows / columns of a rectangle whose edges inside it are all covered at least twice
inline void trim_cover(const Graph& g, std::vector<Rect>& sol, CovCount& cc) {
  int n = g.n, m = g.m;
  for (bool ch = true; ch;) {
    ch = false;
    for (auto& r : sol) {
      for (int u = 0; u < n; u++) if (r.U.get(u) && r.U.count() > 1) {
        bool red = true; r.V.each([&](int v) { if (cc.at(u, v) < 2) red = false; });
        if (red) { r.V.each([&](int v) { cc.c[(size_t)u * m + v]--; }); r.U.clr(u); ch = true; }
      }
      for (int v = 0; v < m; v++) if (r.V.get(v) && r.V.count() > 1) {
        bool red = true; r.U.each([&](int u) { if (cc.at(u, v) < 2) red = false; });
        if (red) { r.U.each([&](int u) { cc.c[(size_t)u * m + v]--; }); r.V.clr(v); ch = true; }
      }
    }
  }
}

// Cover from a candidate list (closed bicliques): repeatedly take the uncovered edge that lies in the fewest candidates
// and the candidate through it that covers most uncovered edges; prune; then "one in, several out" local search
// (add a candidate that makes >= 2 chosen rectangles redundant); finally trim optional rows/columns.
// Returns false if the candidates do not cover every edge.
inline bool cover_from_candidates(const Graph& g, const std::vector<Rect>& cand, std::vector<Rect>& sol, bool trim, std::string* log = nullptr) {
  int n = g.n, m = g.m;
  std::vector<int> cnt((size_t)n * m, 0);
  for (auto& c : cand) c.U.each([&](int u) { c.V.each([&](int v) { cnt[(size_t)u * m + v]++; }); });
  for (int u = 0; u < n; u++) { bool ok = true; g.row[u].each([&](int v) { if (!cnt[(size_t)u * m + v]) ok = false; }); if (!ok) return false; }
  sol.clear();
  std::vector<B128> unc = g.row; int left = g.edges;
  while (left > 0) {
    int be = -1;
    for (int u = 0; u < n; u++) unc[u].each([&](int v) { if (be < 0 || cnt[(size_t)u * m + v] < cnt[be]) be = u * m + v; });
    int bu = be / m, bv = be % m, best = -1, bn = -1;
    for (size_t i = 0; i < cand.size(); i++) if (cand[i].U.get(bu) && cand[i].V.get(bv)) {
      int nw = 0; cand[i].U.each([&](int u) { nw += (cand[i].V & unc[u]).count(); });
      if (nw > bn) { bn = nw; best = (int)i; }
    }
    cand[best].U.each([&](int u) { unc[u] = unc[u].andnot(cand[best].V); });
    left -= bn; sol.push_back(cand[best]);
  }
  CovCount cc(n, m);
  for (auto& r : sol) cc.add(r, 1);
  prune_redundant(g, sol, cc);
  size_t start = sol.size();
  for (bool improved = true; improved;) {
    improved = false;
    std::vector<std::vector<std::pair<int, B128>>> priv(sol.size());
    for (size_t i = 0; i < sol.size(); i++)
      sol[i].U.each([&](int u) { B128 p; sol[i].V.each([&](int v) { if (cc.at(u, v) == 1) p.set(v); }); if (p.any()) priv[i].push_back({u, p}); });
    int bestq = -1, bestk = 1;
    for (size_t q = 0; q < cand.size(); q++) {
      int k = 0;
      for (size_t i = 0; i < sol.size(); i++) {
        bool in = true;
        for (auto& [u, p] : priv[i]) if (!cand[q].U.get(u) || !p.subset_of(cand[q].V)) { in = false; break; }
        if (in) k++;
      }
      if (k > bestk) { bestk = k; bestq = (int)q; }
    }
    if (bestq >= 0) {
      size_t before = sol.size();
      sol.push_back(cand[bestq]); cc.add(cand[bestq], 1);
      prune_redundant(g, sol, cc);
      if (sol.size() < before) improved = true;
    }
  }
  if (trim) trim_cover(g, sol, cc);
  if (log) *log = "greedy " + std::to_string(start) + " rects -> local search " + std::to_string(sol.size()) + " rects, weight " + std::to_string(weight(sol));
  return true;
}

// Greedy cover without an explicit candidate list: grow a maximal biclique around each uncovered edge (randomised).
inline std::vector<Rect> greedy_grow_cover(const Graph& g, Rng& rng) {
  int n = g.n, m = g.m;
  std::vector<B128> unc = g.row;
  std::vector<Rect> sol;
  std::vector<int> es;
  for (int u = 0; u < n; u++) g.row[u].each([&](int v) { es.push_back(u * m + v); });
  for (size_t i = es.size(); i > 1; i--) std::swap(es[i - 1], es[rng.below((u32)i)]);
  for (int e : es) {
    int u0 = e / m, v0 = e % m;
    if (!unc[u0].get(v0)) continue;
    Rect r; r.U.set(u0); r.V = g.row[u0];
    // add rows greedily while the number of uncovered edges inside grows
    for (;;) {
      int bu = -1; long bs = 0;
      auto score = [&](const B128& U, const B128& V) { long s = 0; U.each([&](int u) { s += (V & unc[u]).count(); }); return s * 64 - (U.count() + V.count()); };
      long cur = score(r.U, r.V);
      for (int u = 0; u < n; u++) {
        if (r.U.get(u)) continue;
        B128 V2 = r.V & g.row[u];
        if (!V2.get(v0)) continue;
        B128 U2 = r.U; U2.set(u);
        long s = score(U2, V2) + (long)rng.below(8);
        if (s > cur + bs) { bs = s - cur; bu = u; }
      }
      if (bu < 0) break;
      r.U.set(bu); r.V = r.V & g.row[bu];
    }
    // keep only columns that carry an uncovered edge, then re-close rows over those columns
    B128 need; r.U.each([&](int u) { need = need | (r.V & unc[u]); });
    r.V = need;
    r.U.each([&](int u) { unc[u] = unc[u].andnot(r.V); });
    sol.push_back(r);
  }
  CovCount cc(n, m);
  for (auto& r : sol) cc.add(r, 1);
  prune_redundant(g, sol, cc);
  trim_cover(g, sol, cc);
  return sol;
}


// ---------------------------------------------------------------------------------------------------------------------
// Min-weight exact cover search (weight = sum |U|+|V|, optionally + lambda per rectangle): simulated annealing over
// exact covers. Every move is a compound "perturb, then trim everything that became redundant" step, evaluated on a
// copy-on-reject basis (the state is small). Moves: (1) plant a new rectangle grown from a random edge, (2) add one
// row/column to a rectangle, (3) merge two rectangles (U1 ∪ U2) x (V1 ∩ V2) or (U1 ∩ U2) x (V1 ∪ V2).
struct WCover {
  const Graph& g;
  int n, m;
  std::vector<Rect> r;
  std::vector<uint16_t> cc;
  double lambda = 0;
  u64 moves = 0, accepted = 0;
  WCover(const Graph& g_, const std::vector<Rect>& init) : g(g_), n(g_.n), m(g_.m), r(init), cc((size_t)g_.n * g_.m, 0) {
    for (auto& x : r) add(x, 1);
  }
  void add(const Rect& x, int d) { x.U.each([&](int u) { x.V.each([&](int v) { cc[(size_t)u * m + v] += d; }); }); }
  double cost() const { double w = 0; for (auto& x : r) w += x.U.count() + x.V.count() + lambda; return w; }
  static int kth(const B128& s, int k) {
    for (int w = 0; w < 2; w++) {
      int c = __builtin_popcountll(s.w[w]);
      if (k < c) { u64 x = s.w[w]; while (k--) x &= x - 1; return w * 64 + __builtin_ctzll(x); }
      k -= c;
    }
    return -1;
  }
  // remove every row/column/rectangle that is redundant, scanning from a random start
  void trim(Rng& rng) {
    for (bool ch = true; ch;) {
      ch = false;
      size_t k0 = r.empty() ? 0 : rng.below((u32)r.size());
      for (size_t kk = 0; kk < r.size(); kk++) {
        Rect& x = r[(kk + k0) % r.size()];
        bool rowsFirst = rng.below(2);
        for (int pass = 0; pass < 2; pass++) {
          if ((pass == 0) == rowsFirst) {
            int u0 = rng.below(n);
            for (int i = 0; i < n; i++) {
              int u = (i + u0) % n;
              if (!x.U.get(u)) continue;
              bool red = true; x.V.each([&](int v) { if (cc[(size_t)u * m + v] < 2) red = false; });
              if (red) { x.V.each([&](int v) { cc[(size_t)u * m + v]--; }); x.U.clr(u); ch = true; }
            }
          } else {
            int v0 = rng.below(m);
            for (int i = 0; i < m; i++) {
              int v = (i + v0) % m;
              if (!x.V.get(v)) continue;
              bool red = true; x.U.each([&](int u) { if (cc[(size_t)u * m + v] < 2) red = false; });
              if (red) { x.U.each([&](int u) { cc[(size_t)u * m + v]--; }); x.V.clr(v); ch = true; }
            }
          }
        }
      }
      // rectangles that lost a whole side cover nothing any more
      for (size_t k = r.size(); k-- > 0;)
        if (r[k].U.none() || r[k].V.none()) { add(r[k], -1); r[k] = r.back(); r.pop_back(); }
    }
  }
  bool perturb(Rng& rng) {
    u32 t = rng.below(10);
    if (t < 4 || r.empty()) {            // new rectangle through a random edge
      int u0 = rng.below(n); int dc = g.row[u0].count(); if (!dc) return false;
      int v0 = kth(g.row[u0], rng.below(dc));
      Rect x; x.U.set(u0); x.V = g.row[u0];
      int grow = 1 + rng.below(7);
      for (int k = 0; k < grow; k++) {
        B128 cu = g.col[v0].andnot(x.U); int c = cu.count(); if (!c) break;
        int u = kth(cu, rng.below(c));
        B128 V2 = x.V & g.row[u];
        if (V2.count() < 2) continue;
        x.U.set(u); x.V = V2;
      }
      if (rng.below(2)) x.U = g.rows_of(x.V);      // close the row side
      r.push_back(x); add(x, 1);
      return true;
    }
    if (t < 7) {                         // add one element to a random rectangle
      Rect& x = r[rng.below((u32)r.size())];
      if (rng.below(2)) { int u = rng.below(n); if (x.U.get(u) || !x.V.subset_of(g.row[u])) return false; x.V.each([&](int v) { cc[(size_t)u * m + v]++; }); x.U.set(u); }
      else { int v = rng.below(m); if (x.V.get(v) || !x.U.subset_of(g.col[v])) return false; x.U.each([&](int u) { cc[(size_t)u * m + v]++; }); x.V.set(v); }
      return true;
    }
    if (r.size() < 2) return false;      // merge-style rectangle from two existing ones
    size_t a = rng.below((u32)r.size()), b = rng.below((u32)r.size());
    if (a == b) return false;
    Rect x;
    if (rng.below(2)) { x.U = r[a].U | r[b].U; x.V = r[a].V & r[b].V; }
    else { x.U = r[a].U & r[b].U; x.V = r[a].V | r[b].V; }
    if (x.U.none() || x.V.none()) return false;
    r.push_back(x); add(x, 1);
    return true;
  }
  void run(Rng& rng, long iters, double t0, double t1) {
    std::vector<Rect> sr; std::vector<uint16_t> sc;
    double cur = cost(), ratio = std::log(t1 / t0);
    std::vector<Rect> best = r; double bestc = cur;
    for (long i = 0; i < iters; i++) {
      double T = t0 * std::exp(ratio * (double)i / (double)iters);
      sr = r; sc = cc;
      if (!perturb(rng)) continue;
      trim(rng);
      moves++;
      double nc = cost(), d = nc - cur;
      if (d <= 0 || rng.uni() < std::exp(-d / T)) { cur = nc; accepted++; if (cur < bestc) { bestc = cur; best = r; } }
      else { r.swap(sr); cc.swap(sc); }
    }
    r = best; std::fill(cc.begin(), cc.end(), 0);
    for (auto& x : r) add(x, 1);
  }
};


// ---------------------------------------------------------------------------------------------------------------------
// Read the cover (and the cross pairing) out of an existing circuit of the shape OR_j (S_j AND T_j), where S_j and T_j
// are "crosses" (OR of some row wires and some column wires). Every AND gate whose two inputs are crosses with
// disjoint row parts and disjoint column parts contributes the rectangles rows(S) x cols(T) and rows(T) x cols(S).
// Other AND gates are ignored. Returns false unless the rectangles found cover the graph exactly.
inline bool cover_from_circuit(const pnp::Spec& spec, const Graph& g, const pnp::Circuit& c, std::vector<Rect>& rects, std::vector<int>& partner) {
  std::vector<pnp::u64> buf;
  pnp::eval(spec, c, buf);
  size_t W = spec.W; int n = g.n, m = g.m;
  auto cross = [&](int w, B128& U, B128& V) {
    if (w < 0 || (size_t)w >= (size_t)c.N + c.gates.size()) return false;
    const pnp::u64* col = &buf[(size_t)w * W];
    auto bit = [&](int u, int v) { size_t p = (size_t)u * m + v; return (col[p / 64] >> (p % 64)) & 1; };
    U = B128(); V = low_mask(m);
    for (int u = 0; u < n; u++) {
      bool full = true; B128 r;
      for (int v = 0; v < m; v++) { if (bit(u, v)) r.set(v); else full = false; }
      if (full) U.set(u); else V = V & r;
    }
    if (U.count() == n) V = B128();   // all-ones wire: treat as rows-only
    for (int u = 0; u < n; u++) if (!U.get(u)) for (int v = 0; v < m; v++) if ((bool)bit(u, v) != V.get(v)) return false;
    return true;
  };
  rects.clear(); partner.clear();
  for (auto& gt : c.gates) {
    if (gt.op != pnp::AND || gt.nin != 2) continue;
    B128 U1, V1, U2, V2;
    if (!cross(gt.a, U1, V1) || !cross(gt.b, U2, V2)) continue;
    if ((U1 & U2).any() || (V1 & V2).any()) continue;
    Rect r1{U1, V2}, r2{U2, V1};
    bool e1 = r1.U.any() && r1.V.any(), e2 = r2.U.any() && r2.V.any();
    if (e1 && !is_biclique(g, r1)) continue;
    if (e2 && !is_biclique(g, r2)) continue;
    if (e1 && e2) { int a = (int)rects.size(); rects.push_back(r1); rects.push_back(r2); partner.push_back(a + 1); partner.push_back(a); }
    else if (e1) { rects.push_back(r1); partner.push_back(-1); }
    else if (e2) { rects.push_back(r2); partner.push_back(-1); }
  }
  return !rects.empty() && covers_exactly(g, rects);
}

}  // namespace gs
