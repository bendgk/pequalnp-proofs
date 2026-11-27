// analyze.hpp — structure report for a graph spec (and optionally a seed circuit):  graphsynth SPEC --analyze [--ckt C]
#pragma once
#include "cover.hpp"

namespace gs {

inline int gf2_rank(const Graph& g) {
  std::vector<B128> r = g.row;
  int rank = 0;
  for (int c = 0; c < g.m && rank < g.n; c++) {
    int piv = -1;
    for (int i = rank; i < g.n; i++) if (r[i].get(c)) { piv = i; break; }
    if (piv < 0) continue;
    std::swap(r[rank], r[piv]);
    for (int i = 0; i < g.n; i++) if (i != rank && r[i].get(c)) r[i] = r[i] ^ r[rank];
    rank++;
  }
  return rank;
}
// rank over GF(p), p = 2^31 - 1: a lower bound for the rational rank (and almost surely equal to it)
inline int modp_rank(const Graph& g) {
  const u64 P = 2147483647ull;
  auto pw = [&](u64 a, u64 e) { u64 r = 1; a %= P; while (e) { if (e & 1) r = r * a % P; a = a * a % P; e >>= 1; } return r; };
  std::vector<std::vector<u64>> a(g.n, std::vector<u64>(g.m, 0));
  for (int u = 0; u < g.n; u++) for (int v = 0; v < g.m; v++) a[u][v] = g.adj(u, v);
  int rank = 0;
  for (int c = 0; c < g.m && rank < g.n; c++) {
    int piv = -1;
    for (int i = rank; i < g.n; i++) if (a[i][c]) { piv = i; break; }
    if (piv < 0) continue;
    std::swap(a[rank], a[piv]);
    u64 inv = pw(a[rank][c], P - 2);
    for (int i = 0; i < g.n; i++) {
      if (i == rank || !a[i][c]) continue;
      u64 f = a[i][c] * inv % P;
      for (int j = c; j < g.m; j++) a[i][j] = (a[i][j] + P - f * a[rank][j] % P) % P;
    }
    rank++;
  }
  return rank;
}
// Fooling set: edges (u_i, v_i) such that for i != j not both (u_i, v_j) and (u_j, v_i) are edges. No rectangle inside
// the graph contains two of them, so every biclique cover has at least that many rectangles (Boolean rank bound).
inline int fooling_set(const Graph& g, Rng& rng, int restarts) {
  std::vector<int> es;
  for (int u = 0; u < g.n; u++) g.row[u].each([&](int v) { es.push_back(u * g.m + v); });
  int best = 0;
  std::vector<int> cur;
  for (int rs = 0; rs < restarts; rs++) {
    for (size_t i = es.size(); i > 1; i--) std::swap(es[i - 1], es[rng.below((u32)i)]);
    cur.clear();
    for (int e : es) {
      int u = e / g.m, v = e % g.m;
      bool ok = true;
      for (int f : cur) { int u2 = f / g.m, v2 = f % g.m; if (u2 == u || v2 == v || (g.adj(u, v2) && g.adj(u2, v))) { ok = false; break; } }
      if (ok) cur.push_back(e);
    }
    best = std::max(best, (int)cur.size());
  }
  return best;
}
inline void print_hist(const char* name, std::vector<int> d) {
  std::sort(d.begin(), d.end());
  double mean = 0; for (int x : d) mean += x; mean /= std::max<size_t>(1, d.size());
  printf("%s: min %d  median %d  max %d  mean %.2f\n   sorted:", name, d.front(), d[d.size() / 2], d.back(), mean);
  for (int x : d) printf(" %d", x);
  printf("\n");
}
// positive-polarity recursive binary encoder for a one-hot family of 2^k wires: pair neighbours (2^(k-1) ORs give the
// one-hot family of the upper k-1 bits), bit 0 = OR of the odd wires (2^(k-1) - 1 ORs), recurse.
inline long encoder_pos(int k) { return k <= 1 ? 0 : (1L << k) - 1 + encoder_pos(k - 1); }
// monotone encoder for both polarities from the analytic track's barrier audit (R(k))
inline long encoder_both(int k) { if (k <= 1) return 0; int a = k / 2, b = k - a; return 2 * (1L << k) - (1L << a) - (1L << b) + encoder_both(a) + encoder_both(b); }

inline int analyze(const Graph& G, const pnp::Spec& spec, const std::string& cktPath, bool listTerms = false) {
  int n = G.n, m = G.m;
  printf("== graph: n=%d m=%d edges=%d density=%.4f\n", n, m, G.edges, (double)G.edges / ((double)n * m));
  std::vector<int> dr, dc;
  for (int u = 0; u < n; u++) dr.push_back(G.row[u].count());
  for (int v = 0; v < m; v++) dc.push_back(G.col[v].count());
  print_hist("row degrees", dr);
  print_hist("col degrees", dc);
  int dupR = 0, dupC = 0, nestR = 0, nestC = 0;
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (a != b) { if (a < b && G.row[a] == G.row[b]) dupR++; else if (G.row[a] != G.row[b] && G.row[a].subset_of(G.row[b])) nestR++; }
  for (int a = 0; a < m; a++) for (int b = 0; b < m; b++) if (a != b) { if (a < b && G.col[a] == G.col[b]) dupC++; else if (G.col[a] != G.col[b] && G.col[a].subset_of(G.col[b])) nestC++; }
  printf("duplicate row pairs %d, duplicate column pairs %d, nested row pairs (a strictly inside b) %d, nested column pairs %d\n", dupR, dupC, nestR, nestC);
  printf("rank over GF(2): %d   rank over GF(2^31-1): %d   (min(n,m) = %d)\n", gf2_rank(G), modp_rank(G), std::min(n, m));
  Rng rng(12345);
  int fs = fooling_set(G, rng, 2000);
  printf("fooling set (greedy, 2000 restarts): %d  => every biclique cover needs >= %d rectangles (Boolean rank >= %d)\n", fs, fs, fs);
  printf("trivial weight bound: every non-isolated row and column lies in a rectangle => sum(|U|+|V|) >= %d\n",
         (int)std::count_if(dr.begin(), dr.end(), [](int x) { return x > 0; }) + (int)std::count_if(dc.begin(), dc.end(), [](int x) { return x > 0; }));

  // closed bicliques
  {
    Cbo all(G, 1, 1, 3000000); all.run();
    if (!all.truncated) {
      std::map<std::pair<int, int>, int> h; long bestArea = 0; Rect bestR;
      for (auto& r : all.out) { h[{r.U.count(), r.V.count()}]++; long a = (long)r.U.count() * r.V.count(); if (a > bestArea) { bestArea = a; bestR = r; } }
      printf("closed (maximal) bicliques: %zu in total; largest area %ld (%dx%d)\n", all.out.size(), bestArea, bestR.U.count(), bestR.V.count());
      printf("   count by (|U|,|V|):");
      for (auto& [k, v] : h) printf(" (%d,%d):%d", k.first, k.second, v);
      printf("\n");
    } else printf("closed (maximal) bicliques: more than 3,000,000 (enumeration stopped)\n");
  }
  // planted model: union of ~min(n,m) random d x d rectangles
  int d = std::max(2, (int)std::lround(std::sqrt(std::min(n, m) / 2.0)));
  {
    double sr = 0, sc = 0;
    for (int x : dr) if (x < m) sr += std::log(1.0 - (double)x / m) / std::log(1.0 - (double)d / m);
    for (int x : dc) if (x < n) sc += std::log(1.0 - (double)x / n) / std::log(1.0 - (double)d / n);
    printf("== planted-product test (A = union of r random %dx%d rectangles, i.e. A = B o C with %d ones per column of B / row of C)\n", d, d, d);
    printf("density predicted by r = n: 1-(1-(d/n)(d/m))^n = %.4f (observed %.4f)\n", 1 - std::pow(1 - (double)d * d / ((double)n * m), n), (double)G.edges / ((double)n * m));
    printf("rectangles per row estimated from degrees, summed: %.1f (model: r*d = %d for r = n); per column: %.1f\n", sr, n * d, sc);
    double t0 = now_s();
    Cbo cbo(G, d, d, 20000000); cbo.run();
    if (cbo.truncated) printf("closed bicliques with both sides >= %d: enumeration truncated\n", d);
    else {
      std::map<std::pair<int, int>, int> h;
      for (auto& r : cbo.out) h[{r.U.count(), r.V.count()}]++;
      printf("closed bicliques with both sides >= %d: %zu (%.2fs):", d, cbo.out.size(), now_s() - t0);
      int shown = 0;
      for (auto& [k, v] : h) if (shown++ < 40) printf(" (%d,%d):%d", k.first, k.second, v);
      printf("\n");
      std::vector<Rect> sol; std::string log;
      if (cover_from_candidates(G, cbo.out, sol, false, &log)) {
        printf("exact cover by such bicliques (before trimming): %s\n", log.c_str());
        CovCount cc(n, m);
        for (auto& r : sol) cc.add(r, 1);
        trim_cover(G, sol, cc);
        std::map<std::pair<int, int>, int> hs;
        for (auto& r : sol) hs[{r.U.count(), r.V.count()}]++;
        printf("after trimming redundant rows/columns: %zu rectangles, weight %d, sizes:", sol.size(), weight(sol));
        for (auto& [k, v] : hs) printf(" (%d,%d):%d", k.first, k.second, v);
        std::map<int, int> mult;
        for (int u = 0; u < n; u++) G.row[u].each([&](int v) { mult[cc.at(u, v)]++; });
        printf("\n   edge cover multiplicity:");
        for (auto& [k, v] : mult) printf(" %d:%d", k, v);
        printf("\n   => trivial circuit of this cover: %d gates (weight - 1)\n", weight(sol) - 1);
        // mixed shape "A = (cover of a superset A') AND NOT (cover of D)": the cheapest supersets merge two rectangles
        // into their bounding rectangle; count the non-edges that D would then have to cover exactly
        int bestBad = 1 << 30, bestSave = 0; long sumBad = 0, pairsN = 0;
        for (size_t a = 0; a < sol.size(); a++) for (size_t b = a + 1; b < sol.size(); b++) {
          B128 U = sol[a].U | sol[b].U, V = sol[a].V | sol[b].V;
          int bad = 0; U.each([&](int u) { bad += V.andnot(G.row[u]).count(); });
          int save = sol[a].U.count() + sol[b].U.count() + sol[a].V.count() + sol[b].V.count() - U.count() - V.count() + 2;
          sumBad += bad; pairsN++;
          if (bad < bestBad || (bad == bestBad && save > bestSave)) { bestBad = bad; bestSave = save; }
        }
        if (pairsN) printf("   mixed shape test: bounding rectangle of two cover rectangles contains on average %.1f non-edges, at best %d (while saving at most %d gates before D is paid for)\n",
                           (double)sumBad / pairsN, bestBad, bestSave);
      } else printf("these bicliques do NOT cover every edge: no planted cover with all sides >= %d\n", d);
    }
    Rng rw(777);
    if ((size_t)n * m <= 4096) {
      std::vector<Rect> init = greedy_grow_cover(G, rw);
      int bestW = 1 << 30; size_t bestR = 0;
      for (int rep = 0; rep < 4; rep++) {
        WCover w(G, init); w.lambda = 3;
        w.run(rw, 300000, 1.2, 0.15);
        if (weight(w.r) < bestW) { bestW = weight(w.r); bestR = w.r.size(); }
      }
      printf("min-weight exact cover found by annealing (4 runs, sub-bicliques allowed): weight %d with %zu rectangles\n", bestW, bestR);
    }
  }
  // encode-then-compute shape
  if (n == m && (n & (n - 1)) == 0) {
    int k = 0; while ((1 << k) < n) k++;
    printf("== encode-then-compute shape (k = %d bits a side)\n", k);
    printf("encoders: positive bits %ld gates a side (+%d NOT for the negations in basis aon = %ld a side, %ld both sides);\n", encoder_pos(k), k, encoder_pos(k) + k, 2 * (encoder_pos(k) + k));
    printf("          monotone both polarities (analytic R(k)) %ld a side, %ld both sides\n", encoder_both(k), 2 * encoder_both(k));
    printf("          the adjacency function then is a %d-input function; Shannon count 2^%d/%d = %.0f gates for a typical one\n", 2 * k, 2 * k, 2 * k, std::pow(2.0, 2 * k) / (2 * k));
  }
  // seed circuit
  if (!cktPath.empty()) {
    pnp::Circuit c = pnp::load_circuit(cktPath);
    pnp::Verdict v = pnp::verify(spec, c);
    printf("== circuit %s: %d gates (and %d, or %d, not %d), %s\n", cktPath.c_str(), c.size(), c.count(pnp::AND), c.count(pnp::OR), c.count(pnp::NOT), v.ok ? "verified" : "WRONG");
    std::vector<pnp::u64> buf; pnp::eval(spec, c, buf);
    size_t W = spec.W;
    int kRow = 0, kCol = 0, kCross = 0, kGen = 0;
    for (size_t j = 0; j < c.gates.size(); j++) {
      const pnp::u64* col = &buf[((size_t)c.N + j) * W];
      auto bit = [&](int u, int vv) { size_t p = (size_t)u * m + vv; return (col[p / 64] >> (p % 64)) & 1; };
      bool rowset = true, colset = true, cross = true;
      B128 U, V = low_mask(m);
      for (int u = 0; u < n; u++) {
        bool full = true, empty = true; B128 r;
        for (int vv = 0; vv < m; vv++) { if (bit(u, vv)) { r.set(vv); empty = false; } else full = false; }
        if (!full && !empty) rowset = false;
        if (full) U.set(u); else V = V & r;
      }
      for (int u = 0; u < n; u++) for (int vv = 0; vv < m; vv++) { bool b = bit(u, vv); if (b != V.get(vv) && !U.get(u)) cross = false; if (b != (bool)bit(0, vv)) colset = false; }
      if (rowset) kRow++; else if (colset) kCol++; else if (cross) kCross++; else kGen++;
    }
    printf("gates by the matrix they compute: union of full rows %d, union of full columns %d, cross (rows ∪ columns) %d, other %d\n", kRow, kCol, kCross, kGen);
    std::vector<Rect> rects; std::vector<int> partner;
    if (cover_from_circuit(spec, G, c, rects, partner)) {
      int pairs = 0; for (size_t a = 0; a < partner.size(); a++) pairs += partner[a] > (int)a;
      std::map<std::pair<int, int>, int> hs;
      for (auto& r : rects) hs[{r.U.count(), r.V.count()}]++;
      CovCount cc(n, m);
      for (auto& r : rects) cc.add(r, 1);
      std::map<int, int> mult;
      for (int u = 0; u < n; u++) G.row[u].each([&](int vv) { mult[cc.at(u, vv)]++; });
      int terms = (int)rects.size() - pairs;
      printf("it is an OR of %d AND terms over %zu rectangles (%d cross pairs, %d solo); weight %d; %d gates build the OR-sets, %d combine the terms\n", terms, rects.size(), pairs,
             (int)rects.size() - 2 * pairs, weight(rects), c.size() - (2 * terms - 1), 2 * terms - 1);
      printf("   rectangle sizes:");
      for (auto& [k, vv] : hs) printf(" (%d,%d):%d", k.first, k.second, vv);
      printf("\n   edge cover multiplicity:");
      for (auto& [k, vv] : mult) printf(" %d:%d", k, vv);
      printf("\n");
      if (listTerms) {
        auto show = [&](const B128& b) { printf("["); bool f = true; b.each([&](int i) { printf(f ? "%d" : " %d", i); f = false; }); printf("]"); };
        int t = 0;
        for (size_t a = 0; a < rects.size(); a++) {
          if (partner[a] >= 0 && partner[a] < (int)a) continue;
          printf("   term %d: U=", t++); show(rects[a].U); printf(" V="); show(rects[a].V);
          if (partner[a] >= 0) { printf("  +  U="); show(rects[partner[a]].U); printf(" V="); show(rects[partner[a]].V); }
          printf("\n");
        }
      }
    } else printf("its AND gates do not form an exact cover by (pairs of) rectangles\n");
  }
  return 0;
}
}  // namespace gs
