// bicliq.hpp — closed-biclique (formal concept) enumeration with size thresholds, and cover helpers.
#pragma once
#include "gs_common.hpp"

namespace gs {

// Close-by-One over row sets. Reports every closed biclique (U, V) with |V| >= minV (and |U| >= minU at report time).
// Stops (returns false) once more than `limit` concepts were visited.
struct Cbo {
  const Graph& g;
  int minU, minV;
  size_t limit, visited = 0;
  bool truncated = false;
  std::vector<Rect> out;
  Cbo(const Graph& g_, int minU_, int minV_, size_t limit_) : g(g_), minU(minU_), minV(minV_), limit(limit_) {}
  void rec(const B128& U, const B128& V, int y) {
    if (truncated) return;
    if (++visited > limit) { truncated = true; return; }
    if (U.count() >= minU && V.any()) out.push_back({U, V});
    for (int j = y; j < g.n; j++) {
      if (U.get(j)) continue;
      B128 V2 = V & g.row[j];
      if (V2.count() < minV || V2.none()) continue;
      B128 U2;
      for (int u = 0; u < g.n; u++) if (V2.subset_of(g.row[u])) U2.set(u);
      B128 lm = low_mask(j);
      if ((U2 & lm) != (U & lm)) continue;
      rec(U2, V2, j + 1);
    }
  }
  void run() {
    B128 V = low_mask(g.m);
    B128 U;
    for (int u = 0; u < g.n; u++) if (V.subset_of(g.row[u])) U.set(u);
    // top concept (all columns) is reported only if some row is full
    visited = 0;
    if (U.any() && U.count() >= minU) out.push_back({U, V});
    for (int j = 0; j < g.n; j++) {
      if (U.get(j)) continue;
      B128 V2 = g.row[j];
      if (V2.count() < minV || V2.none()) continue;
      B128 U2;
      for (int u = 0; u < g.n; u++) if (V2.subset_of(g.row[u])) U2.set(u);
      B128 lm = low_mask(j);
      if ((U2 & lm) != (U & lm)) continue;
      rec(U2, V2, j + 1);
    }
  }
};

// cover multiplicity matrix
struct CovCount {
  int n, m;
  std::vector<uint16_t> c;
  CovCount(int n_, int m_) : n(n_), m(m_), c((size_t)n_ * m_, 0) {}
  void add(const Rect& r, int d) { r.U.each([&](int u) { r.V.each([&](int v) { c[(size_t)u * m + v] += d; }); }); }
  int at(int u, int v) const { return c[(size_t)u * m + v]; }
};

inline bool is_biclique(const Graph& g, const Rect& r) {
  bool ok = true;
  r.U.each([&](int u) { if (!r.V.subset_of(g.row[u])) ok = false; });
  return ok;
}
inline bool covers_exactly(const Graph& g, const std::vector<Rect>& rs) {
  std::vector<B128> cov(g.n);
  for (auto& r : rs) {
    if (!is_biclique(g, r)) return false;
    r.U.each([&](int u) { cov[u] = cov[u] | r.V; });
  }
  for (int u = 0; u < g.n; u++) if (cov[u] != g.row[u]) return false;
  return true;
}
inline int weight(const std::vector<Rect>& rs) { int w = 0; for (auto& r : rs) w += r.U.count() + r.V.count(); return w; }

}  // namespace gs
