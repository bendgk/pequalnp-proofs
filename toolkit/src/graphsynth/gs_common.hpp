// gs_common.hpp — shared bits for graphsynth (bit-parallel sets over rows ⊎ columns).
#pragma once
#include "../../include/ckt.hpp"
#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <map>
#include <mutex>
#include <thread>
#include <unordered_map>

namespace gs {
using u64 = uint64_t;
using u32 = uint32_t;

// 128-bit set (one side: rows or columns)
struct B128 {
  u64 w[2] = {0, 0};
  bool get(int i) const { return (w[i >> 6] >> (i & 63)) & 1; }
  void set(int i) { w[i >> 6] |= u64(1) << (i & 63); }
  void clr(int i) { w[i >> 6] &= ~(u64(1) << (i & 63)); }
  int count() const { return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]); }
  bool any() const { return (w[0] | w[1]) != 0; }
  bool none() const { return (w[0] | w[1]) == 0; }
  B128 operator&(const B128& o) const { return {{w[0] & o.w[0], w[1] & o.w[1]}}; }
  B128 operator|(const B128& o) const { return {{w[0] | o.w[0], w[1] | o.w[1]}}; }
  B128 operator^(const B128& o) const { return {{w[0] ^ o.w[0], w[1] ^ o.w[1]}}; }
  B128 andnot(const B128& o) const { return {{w[0] & ~o.w[0], w[1] & ~o.w[1]}}; }  // this \ o
  bool operator==(const B128& o) const { return w[0] == o.w[0] && w[1] == o.w[1]; }
  bool operator!=(const B128& o) const { return !(*this == o); }
  bool subset_of(const B128& o) const { return ((w[0] & ~o.w[0]) | (w[1] & ~o.w[1])) == 0; }
  bool operator<(const B128& o) const { return w[1] != o.w[1] ? w[1] < o.w[1] : w[0] < o.w[0]; }
  int first() const { return w[0] ? __builtin_ctzll(w[0]) : w[1] ? 64 + __builtin_ctzll(w[1]) : -1; }
  template <class F> void each(F f) const {
    for (int k = 0; k < 2; k++) { u64 x = w[k]; while (x) { f(k * 64 + __builtin_ctzll(x)); x &= x - 1; } }
  }
  std::vector<int> list() const { std::vector<int> r; each([&](int i) { r.push_back(i); }); return r; }
};
inline B128 low_mask(int k) {  // bits 0..k-1
  B128 b;
  if (k >= 128) { b.w[0] = b.w[1] = ~u64(0); }
  else if (k >= 64) { b.w[0] = ~u64(0); b.w[1] = (k == 64) ? 0 : ((u64(1) << (k - 64)) - 1); }
  else b.w[0] = k ? ((u64(1) << k) - 1) : 0;
  return b;
}

// 256-bit set over the ground set rows ⊎ columns: row u = bit u, column v = bit 128+v.
struct B256 {
  u64 w[4] = {0, 0, 0, 0};
  bool get(int i) const { return (w[i >> 6] >> (i & 63)) & 1; }
  void set(int i) { w[i >> 6] |= u64(1) << (i & 63); }
  void clr(int i) { w[i >> 6] &= ~(u64(1) << (i & 63)); }
  int count() const {
    return __builtin_popcountll(w[0]) + __builtin_popcountll(w[1]) + __builtin_popcountll(w[2]) + __builtin_popcountll(w[3]);
  }
  bool any() const { return (w[0] | w[1] | w[2] | w[3]) != 0; }
  bool none() const { return !any(); }
  B256 operator&(const B256& o) const { return {{w[0] & o.w[0], w[1] & o.w[1], w[2] & o.w[2], w[3] & o.w[3]}}; }
  B256 operator|(const B256& o) const { return {{w[0] | o.w[0], w[1] | o.w[1], w[2] | o.w[2], w[3] | o.w[3]}}; }
  B256 andnot(const B256& o) const { return {{w[0] & ~o.w[0], w[1] & ~o.w[1], w[2] & ~o.w[2], w[3] & ~o.w[3]}}; }
  bool operator==(const B256& o) const { return w[0] == o.w[0] && w[1] == o.w[1] && w[2] == o.w[2] && w[3] == o.w[3]; }
  bool operator!=(const B256& o) const { return !(*this == o); }
  bool subset_of(const B256& o) const {
    return ((w[0] & ~o.w[0]) | (w[1] & ~o.w[1]) | (w[2] & ~o.w[2]) | (w[3] & ~o.w[3])) == 0;
  }
  bool intersects(const B256& o) const { return ((w[0] & o.w[0]) | (w[1] & o.w[1]) | (w[2] & o.w[2]) | (w[3] & o.w[3])) != 0; }
  B128 rows() const { return {{w[0], w[1]}}; }
  B128 cols() const { return {{w[2], w[3]}}; }
  static B256 make(const B128& r, const B128& c) { return {{r.w[0], r.w[1], c.w[0], c.w[1]}}; }
  int first() const { for (int k = 0; k < 4; k++) if (w[k]) return k * 64 + __builtin_ctzll(w[k]); return -1; }
  template <class F> void each(F f) const {
    for (int k = 0; k < 4; k++) { u64 x = w[k]; while (x) { f(k * 64 + __builtin_ctzll(x)); x &= x - 1; } }
  }
  u64 hash() const {
    u64 h = w[0] * 0x9E3779B97F4A7C15ull;
    h = (h ^ (h >> 29)) + w[1] * 0xBF58476D1CE4E5B9ull;
    h = (h ^ (h >> 31)) + w[2] * 0x94D049BB133111EBull;
    h = (h ^ (h >> 30)) + w[3] * 0xD6E8FEB86659FD93ull;
    return h ^ (h >> 32);
  }
};
struct B256Hash { size_t operator()(const B256& b) const { return (size_t)b.hash(); } };

// xoshiro256** — deterministic per-thread RNG
struct Rng {
  u64 s[4];
  explicit Rng(u64 seed = 1) {
    for (int i = 0; i < 4; i++) { seed += 0x9E3779B97F4A7C15ull; u64 z = seed; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; s[i] = z ^ (z >> 31); }
  }
  static u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
  u64 next() {
    u64 r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
    return r;
  }
  u32 below(u32 n) { return (u32)(((next() >> 32) * (u64)n) >> 32); }
  double uni() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

struct Graph {
  int n = 0, m = 0;
  std::vector<B128> row;  // row[u] = neighbours (columns) of left vertex u
  std::vector<B128> col;  // col[v] = neighbours (rows) of right vertex v
  int edges = 0;
  bool adj(int u, int v) const { return row[u].get(v); }
  Graph complement() const {
    Graph g; g.n = n; g.m = m; g.row.assign(n, B128()); g.col.assign(m, B128());
    for (int u = 0; u < n; u++) for (int v = 0; v < m; v++) if (!adj(u, v)) { g.row[u].set(v); g.col[v].set(u); g.edges++; }
    return g;
  }
  Graph transpose() const { Graph g; g.n = m; g.m = n; g.row = col; g.col = row; g.edges = edges; return g; }
  // rows containing all of V / columns common to all of U
  B128 rows_of(const B128& V) const { B128 U = low_mask(n); V.each([&](int v) { U = U & col[v]; }); return U; }
  B128 cols_of(const B128& U) const { B128 V = low_mask(m); U.each([&](int u) { V = V & row[u]; }); return V; }
};
inline Graph graph_from_spec(const pnp::Spec& s) {
  if (s.kind != "graph") pnp::die("graphsynth needs a 'type graph' spec");
  if (s.gn > 128 || s.gm > 128) pnp::die("graphsynth supports n, m <= 128");
  Graph g; g.n = s.gn; g.m = s.gm; g.row.assign(g.n, B128()); g.col.assign(g.m, B128());
  for (int u = 0; u < g.n; u++) for (int v = 0; v < g.m; v++)
    if (pnp::getbit(s.tgt[0], (size_t)u * g.m + v)) { g.row[u].set(v); g.col[v].set(u); g.edges++; }
  return g;
}
inline double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// a biclique / combinatorial rectangle U x V
struct Rect { B128 U, V; };
}  // namespace gs
