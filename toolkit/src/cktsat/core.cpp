// cktsat-core — native part of cktsat (exact circuit synthesis by SAT cube-and-conquer).
//   prep    SPEC --basis B                      problem summary as one JSON line (points, symmetry group, trivial cases)
//   encode  SPEC --basis B -s S -o F.cnf        DIMACS of "a normal-form circuit with exactly S gates exists"
//   cubes   SPEC --basis B -s S --depth D       canonical gate prefixes up to the spec's symmetry group (one per orbit)
//   serve   SPEC --basis B -s S                 stdin: "split <prefix>" -> the canonical one-gate extensions of that prefix
//   decode  SPEC --basis B -s S < model         model (true literals) -> verified .ckt on stdout
//   brute   SPEC --basis B --max S [--full]     independent brute-force minimum size (validation only, tiny cases)
// See docs/cktsat.md for the model, the encoding and the soundness argument of the symmetry reduction.
#include "../../include/ckt.hpp"
#include <algorithm>
#include <atomic>
#include <chrono>
#include <functional>
#include <map>
#include <mutex>
#include <thread>
#include <unordered_map>
using namespace pnp;

// ------------------------------------------------------------------ gates of a prefix
struct PG { int op, a, b; };   // op 0 = and, 1 = or, 2 = not.  Binary: a < b.  NOT: a = -1, reads b.
static inline bool keyLess(const PG& x, const PG& y) {
  if (x.b != y.b) return x.b < y.b;
  if (x.a != y.a) return x.a < y.a;
  return x.op < y.op;
}
static inline bool keyEq(const PG& x, const PG& y) { return x.op == y.op && x.a == y.a && x.b == y.b; }
static const char* OPN[3] = {"and", "or", "not"};

static std::string prefix_str(const std::vector<PG>& p) {
  std::string s;
  for (size_t i = 0; i < p.size(); i++) {
    if (i) s += ";";
    s += OPN[p[i].op];
    if (p[i].op != 2) s += " " + std::to_string(p[i].a);
    s += " " + std::to_string(p[i].b);
  }
  return s;
}
static bool parse_gate(const std::string& t, PG& g) {
  std::istringstream is(t);
  std::string op; int x, y;
  if (!(is >> op)) return false;
  if (op == "not") { if (!(is >> x)) return false; g = {2, -1, x}; return true; }
  if (op != "and" && op != "or") return false;
  if (!(is >> x >> y) || x == y) return false;
  if (x > y) std::swap(x, y);
  g = {op == "and" ? 0 : 1, x, y};
  return true;
}
static std::vector<PG> parse_prefix(const std::string& s) {
  std::vector<PG> p;
  size_t i = 0;
  while (i <= s.size()) {
    size_t j = s.find(';', i);
    if (j == std::string::npos) j = s.size();
    std::string t = s.substr(i, j - i);
    if (t.find_first_not_of(" \t\r\n") != std::string::npos) {
      PG g;
      if (!parse_gate(t, g)) die("bad gate in prefix: '" + t + "'");
      p.push_back(g);
    }
    i = j + 1;
  }
  return p;
}

// ------------------------------------------------------------------ the reduced problem
struct Prob {
  Spec sp;
  std::string basis;
  bool allowNot = false;
  int N = 0, K = 1, P = 0, W = 0;   // inputs, outputs, reduced points, words per reduced column
  u64 lm = ~u64(0);                 // mask of the last word
  std::vector<Col> in, tgt, care;   // columns over the reduced points
  std::vector<size_t> rep;          // reduced point -> an original point
  std::vector<char> active;         // input has a non-constant column that no earlier input has
  std::vector<char> essential;      // some gate must read this input
  std::vector<std::vector<int>> G;  // symmetry group (or a subset of it) as permutations of the inputs
  bool gtrunc = false;
  // K == 1 trivial cases: -1 none, 0 constant false, 1 constant true, 2 equals input trivIn, 3 equals NOT input trivIn
  int triv = -1, trivIn = -1;
  bool constOutput = false;         // K > 1 and some target is constant on its cared points
  bool allPoints = true;            // the reduced points are all cared points (nothing dropped as implied)
};

static inline u64 mix(u64 x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
  return x;
}
static bool col_const(const Prob& pr, const Col& c) {
  bool all0 = true, all1 = true;
  for (int w = 0; w < pr.W; w++) {
    u64 m = (w == pr.W - 1) ? pr.lm : ~u64(0);
    if (c[w] & m) all0 = false;
    if ((c[w] & m) != m) all1 = false;
  }
  return all0 || all1;
}
static bool match_on(const Col& a, const Col& b, const Col& care) {
  for (size_t w = 0; w < a.size(); w++) if ((a[w] ^ b[w]) & care[w]) return false;
  return true;
}

struct GroupFinder {
  const Prob& pr;
  int n, P, K;
  std::vector<int> act;                       // active inputs
  std::vector<std::string> pat;               // patterns over the active inputs
  std::unordered_map<std::string, int> idx;
  std::vector<int> perm;
  std::vector<char> used;
  std::vector<std::vector<int>> out;
  size_t cap;
  bool trunc = false;
  std::vector<std::pair<u64, u64>> fs;        // multiset fingerprint of the source side after t inputs
  std::vector<int> sigma;

  GroupFinder(const Prob& p, size_t cap_) : pr(p), cap(cap_) {
    P = pr.P; K = pr.K;
    for (int i = 0; i < pr.N; i++) if (pr.active[i]) act.push_back(i);
    n = (int)act.size();
    pat.assign(P, std::string(n, '0'));
    for (int p2 = 0; p2 < P; p2++) {
      for (int t = 0; t < n; t++) if (getbit(pr.in[act[t]], p2)) pat[p2][t] = '1';
      idx[pat[p2]] = p2;
    }
    perm.assign(n, -1); used.assign(n, 0); sigma.assign(P, 0);
  }
  u64 sig0(int p) const {
    std::vector<int> codes;
    for (int k = 0; k < K; k++) codes.push_back(getbit(pr.care[k], p) ? (getbit(pr.tgt[k], p) ? 2 : 1) : 0);
    if (K > 1) std::sort(codes.begin(), codes.end());   // outputs may be permuted too
    u64 h = 0x9e3779b97f4a7c15ULL;
    for (int c : codes) h = mix(h * 5 + c + 1);
    return h;
  }
  static std::pair<u64, u64> fp(const std::vector<u64>& h) {
    u64 s = 0, x = 0;
    for (u64 v : h) { s += mix(v ^ 0x1234567); x ^= mix(v + 0x777); }
    return {s, x};
  }
  bool leaf() {
    std::string y(n, '0');
    for (int p = 0; p < P; p++) {
      for (int t = 0; t < n; t++) y[perm[t]] = pat[p][t];
      auto it = idx.find(y);
      if (it == idx.end()) return false;
      sigma[p] = it->second;
    }
    // outputs: need a permutation tau of the outputs with (care,tgt)_k(p) = (care,tgt)_tau(k)(sigma p)
    std::vector<char> usedk(K, 0);
    for (int k = 0; k < K; k++) {
      bool found = false;
      for (int k2 = 0; k2 < K && !found; k2++) {
        if (usedk[k2]) continue;
        bool ok = true;
        for (int p = 0; p < P && ok; p++) {
          bool c1 = getbit(pr.care[k], p), c2 = getbit(pr.care[k2], sigma[p]);
          if (c1 != c2) ok = false;
          else if (c1 && getbit(pr.tgt[k], p) != getbit(pr.tgt[k2], sigma[p])) ok = false;
        }
        if (ok) { usedk[k2] = 1; found = true; }
      }
      if (!found) return false;
    }
    return true;
  }
  void rec(int t, const std::vector<u64>& hd) {
    if (trunc) return;
    if (t == n) {
      if (leaf()) {
        if (out.size() >= cap) { trunc = true; return; }
        std::vector<int> h(pr.N);
        for (int i = 0; i < pr.N; i++) h[i] = i;
        for (int q = 0; q < n; q++) h[act[q]] = act[perm[q]];
        out.push_back(h);
      }
      return;
    }
    std::vector<u64> h2(P);
    for (int c = 0; c < n; c++) {
      if (used[c]) continue;
      for (int p = 0; p < P; p++) h2[p] = mix(hd[p] * 3 + (pat[p][c] == '1') + 1);
      if (fp(h2) != fs[t + 1]) continue;
      perm[t] = c; used[c] = 1;
      rec(t + 1, h2);
      used[c] = 0;
      if (trunc) return;
    }
  }
  void run() {
    std::vector<u64> h(P);
    for (int p = 0; p < P; p++) h[p] = sig0(p);
    std::vector<u64> h0 = h;
    fs.assign(n + 1, {0, 0});
    fs[0] = fp(h);
    for (int t = 0; t < n; t++) {
      for (int p = 0; p < P; p++) h[p] = mix(h[p] * 3 + (pat[p][t] == '1') + 1);
      fs[t + 1] = fp(h);
    }
    rec(0, h0);
  }
};

static void build_prob(Prob& pr, const std::string& specPath, const std::string& basis, bool sym, size_t gcap, bool monoReduce = true) {
  if (basis != "ao" && basis != "aon" && basis != "ao2") die("basis must be ao, aon or ao2");
  pr.sp = load_spec(specPath);
  pr.basis = basis; pr.allowNot = basis == "aon";
  const Spec& s = pr.sp;
  pr.N = s.N; pr.K = s.K;
  // 1. keep the points some output cares about; merge points with the same input pattern
  std::unordered_map<std::string, int> idx;
  std::vector<std::vector<char>> code;   // per reduced point, per output: 0 don't care, 1 false, 2 true
  for (size_t p = 0; p < s.P; p++) {
    bool any = false;
    for (int k = 0; k < s.K; k++) if (getbit(s.care[k], p)) any = true;
    if (!any) continue;
    std::string key(s.N, '0');
    for (int i = 0; i < s.N; i++) if (getbit(s.in[i], p)) key[i] = '1';
    auto it = idx.find(key);
    int r;
    if (it == idx.end()) { r = (int)pr.rep.size(); idx[key] = r; pr.rep.push_back(p); code.push_back(std::vector<char>(s.K, 0)); }
    else r = it->second;
    for (int k = 0; k < s.K; k++) if (getbit(s.care[k], p)) {
      char c = getbit(s.tgt[k], p) ? 2 : 1;
      if (code[r][k] && code[r][k] != c) die("spec is contradictory: two points with the same inputs want different outputs");
      code[r][k] = c;
    }
  }
  // 1b. monotone bases: every wire is a monotone function of the inputs, so a cared true point that lies above
  //     another cared true point is implied by it, and a cared false point below another cared false point too.
  //     Only the minimal true points and the maximal false points of each output have to be kept.
  if (basis != "aon" && monoReduce && pr.rep.size() <= 30000) {
    size_t R = pr.rep.size();
    int Wn = (s.N + 63) / 64;
    std::vector<std::vector<u64>> bits(R, std::vector<u64>(Wn, 0));
    for (size_t r = 0; r < R; r++) for (int i = 0; i < s.N; i++) if (getbit(s.in[i], pr.rep[r])) bits[r][i / 64] |= u64(1) << (i % 64);
    auto subset = [&](size_t a, size_t b) {     // a strictly inside b
      bool neq = false;
      for (int w = 0; w < Wn; w++) { if (bits[a][w] & ~bits[b][w]) return false; if (bits[a][w] != bits[b][w]) neq = true; }
      return neq;
    };
    for (int k = 0; k < s.K; k++) {
      std::vector<size_t> ones, zeros;
      for (size_t r = 0; r < R; r++) { if (code[r][k] == 2) ones.push_back(r); else if (code[r][k] == 1) zeros.push_back(r); }
      std::vector<size_t> drop;
      for (size_t a : ones) for (size_t b : ones) if (subset(b, a)) { drop.push_back(a); break; }
      for (size_t a : zeros) for (size_t b : zeros) if (subset(a, b)) { drop.push_back(a); break; }
      for (size_t a : drop) code[a][k] = 0;
    }
    std::vector<size_t> rep2;
    std::vector<std::vector<char>> code2;
    for (size_t r = 0; r < R; r++) {
      bool any = false;
      for (int k = 0; k < s.K; k++) if (code[r][k]) any = true;
      if (any) { rep2.push_back(pr.rep[r]); code2.push_back(code[r]); }
    }
    if (rep2.size() != pr.rep.size()) pr.allPoints = false;
    for (size_t r = 0; r < R && pr.allPoints; r++) for (int k = 0; k < s.K; k++)
      if ((code[r][k] != 0) != (bool)getbit(s.care[k], pr.rep[r])) pr.allPoints = false;
    pr.rep.swap(rep2); code.swap(code2);
  }
  pr.P = (int)pr.rep.size();
  if (pr.P == 0) die("spec has no cared point");
  pr.W = (pr.P + 63) / 64;
  pr.lm = (pr.P % 64) ? ((u64(1) << (pr.P % 64)) - 1) : ~u64(0);
  pr.in.assign(pr.N, Col(pr.W, 0)); pr.tgt.assign(pr.K, Col(pr.W, 0)); pr.care.assign(pr.K, Col(pr.W, 0));
  for (int r = 0; r < pr.P; r++) {
    for (int i = 0; i < pr.N; i++) if (getbit(s.in[i], pr.rep[r])) setbit(pr.in[i], r);
    for (int k = 0; k < pr.K; k++) {
      if (code[r][k]) setbit(pr.care[k], r);
      if (code[r][k] == 2) setbit(pr.tgt[k], r);
    }
  }
  // 2. active inputs
  pr.active.assign(pr.N, 1);
  for (int i = 0; i < pr.N; i++) {
    if (col_const(pr, pr.in[i])) { pr.active[i] = 0; continue; }
    for (int j = 0; j < i; j++) if (pr.active[j] && pr.in[j] == pr.in[i]) { pr.active[i] = 0; break; }
  }
  // 3. trivial cases
  if (pr.K == 1) {
    Col z(pr.W, 0), o(pr.W, ~u64(0));
    if (match_on(pr.tgt[0], z, pr.care[0])) pr.triv = 0;
    else if (match_on(pr.tgt[0], o, pr.care[0])) pr.triv = 1;
    else for (int i = 0; i < pr.N && pr.triv < 0; i++) {
      if (match_on(pr.tgt[0], pr.in[i], pr.care[0])) { pr.triv = 2; pr.trivIn = i; }
    }
    if (pr.triv < 0 && pr.allowNot) for (int i = 0; i < pr.N && pr.triv < 0; i++) {
      Col c = pr.in[i];
      for (auto& w : c) w = ~w;
      if (match_on(pr.tgt[0], c, pr.care[0])) { pr.triv = 3; pr.trivIn = i; }
    }
  } else {
    Col z(pr.W, 0), o(pr.W, ~u64(0));
    for (int k = 0; k < pr.K; k++)
      if (match_on(pr.tgt[k], z, pr.care[k]) || match_on(pr.tgt[k], o, pr.care[k])) pr.constOutput = true;
  }
  // 4. essential inputs: two cared points of one output that differ only in input i (among the active
  //    inputs) and have different targets, and that output is not simply input i itself.
  pr.essential.assign(pr.N, 0);
  {
    std::vector<int> act;
    for (int i = 0; i < pr.N; i++) if (pr.active[i]) act.push_back(i);
    int n = (int)act.size();
    std::vector<std::string> pat(pr.P, std::string(n, '0'));
    for (int p = 0; p < pr.P; p++) for (int t = 0; t < n; t++) if (getbit(pr.in[act[t]], p)) pat[p][t] = '1';
    for (int t = 0; t < n; t++) {
      std::unordered_map<std::string, int> seen;
      bool ess = false;
      for (int p = 0; p < pr.P && !ess; p++) {
        std::string key = pat[p]; key[t] = '0';
        auto it = seen.find(key);
        if (it == seen.end()) { seen[key] = p; continue; }
        int q = it->second;
        for (int k = 0; k < pr.K; k++) {
          if (!getbit(pr.care[k], p) || !getbit(pr.care[k], q)) continue;
          if (getbit(pr.tgt[k], p) == getbit(pr.tgt[k], q)) continue;
          if (pr.K > 1 && match_on(pr.tgt[k], pr.in[act[t]], pr.care[k])) continue;
          ess = true; break;
        }
      }
      pr.essential[act[t]] = ess;
    }
    // monotone bases: a monotone function that ignores input i cannot be 1 on p and 0 on q when p minus i is
    // contained in q minus i. (This is what makes every wire of a graph spec such as crown_n essential.)
    if (!pr.allowNot && pr.P <= 4096) {
      int Wn = (n + 63) / 64;
      std::vector<std::vector<u64>> bits(pr.P, std::vector<u64>(Wn, 0));
      for (int p = 0; p < pr.P; p++) for (int t = 0; t < n; t++) if (pat[p][t] == '1') bits[p][t / 64] |= u64(1) << (t % 64);
      for (int k = 0; k < pr.K; k++) {
        std::vector<int> ones, zeros;
        for (int p = 0; p < pr.P; p++) if (getbit(pr.care[k], p)) (getbit(pr.tgt[k], p) ? ones : zeros).push_back(p);
        for (int p : ones) for (int q : zeros) {
          // inputs on in p but off in q: if there is exactly one such input t, then t is essential
          int cnt = 0, which = -1;
          for (int w = 0; w < Wn && cnt < 2; w++) {
            u64 d = bits[p][w] & ~bits[q][w];
            if (d) { cnt += __builtin_popcountll(d); which = w * 64 + __builtin_ctzll(d); }
          }
          if (cnt != 1) continue;
          if (pr.K > 1 && match_on(pr.tgt[k], pr.in[act[which]], pr.care[k])) continue;
          pr.essential[act[which]] = 1;
        }
      }
    }
  }
  // 5. symmetry group
  if (sym && pr.N <= 64) {
    GroupFinder gf(pr, gcap);
    gf.run();
    pr.G = gf.out; pr.gtrunc = gf.trunc;
  }
  if (pr.G.empty()) {
    std::vector<int> id(pr.N);
    for (int i = 0; i < pr.N; i++) id[i] = i;
    pr.G.push_back(id);
  }
}

// ------------------------------------------------------------------ variable layout (normal model)
struct Layout {
  int N, P, s, total;
  std::vector<int> base;
  Layout(int N_, int P_, int s_) : N(N_), P(P_), s(s_) {
    int v = 0;
    for (int i = 0; i < s; i++) { base.push_back(v); v += 3 + 2 * (N + i) + 3 * P; }
    total = v;
  }
  int s1none(int i) const { return base[i] + 1; }
  int s1(int i, int j) const { return base[i] + 2 + j; }
  int s2(int i, int k) const { return base[i] + 2 + (N + i) + k; }
  int t(int i) const { return base[i] + 2 + 2 * (N + i); }
  int ng(int i) const { return base[i] + 3 + 2 * (N + i); }
  int v(int i, int p) const { return base[i] + 4 + 2 * (N + i) + p; }
  int A(int i, int p) const { return v(i, p) + P; }
  int B(int i, int p) const { return v(i, p) + 2 * P; }
};
// full model: extended wires 0 = FALSE (a missing wire), 1 = TRUE (a 0-input AND), 2 + w = wire w
struct LayoutF {
  int N, P, s, total;
  std::vector<int> base;
  LayoutF(int N_, int P_, int s_) : N(N_), P(P_), s(s_) {
    int v = 0;
    for (int i = 0; i < s; i++) { base.push_back(v); v += 2 + 2 * (N + i + 2) + 3 * P; }
    total = v;
  }
  int E(int i) const { return N + i + 2; }
  int s1(int i, int x) const { return base[i] + 1 + x; }
  int s2(int i, int x) const { return base[i] + 1 + E(i) + x; }
  int t(int i) const { return base[i] + 1 + 2 * E(i); }
  int ng(int i) const { return base[i] + 2 + 2 * E(i); }
  int v(int i, int p) const { return base[i] + 3 + 2 * E(i) + p; }
  int A(int i, int p) const { return v(i, p) + P; }
  int B(int i, int p) const { return v(i, p) + 2 * P; }
};

struct Cnf {
  int nv = 0;
  size_t ncl = 0;
  std::vector<int> buf;
  int cur = -1;                 // group of the clauses being added: -1 structural, p = they mention point p only
  std::vector<int> grp;         // group per clause
  void add(std::initializer_list<int> c) { for (int x : c) buf.push_back(x); buf.push_back(0); ncl++; grp.push_back(cur); }
  void add(const std::vector<int>& c) { for (int x : c) buf.push_back(x); buf.push_back(0); ncl++; grp.push_back(cur); }
  // structural clauses first, then one block per point introduced by a line "c point <p>"
  void write_by_point(const std::string& path, const std::string& comment, int P) const {
    FILE* f = fopen(path.c_str(), "w");
    if (!f) die("cannot write " + path);
    fprintf(f, "c %s\np cnf %d %zu\n", comment.c_str(), nv, ncl);
    std::vector<std::string> blocks(P + 1);
    size_t ci = 0;
    std::string* cur_s = &blocks[grp.empty() ? 0 : grp[0] + 1];
    for (int x : buf) {
      if (x == 0) { *cur_s += "0\n"; ci++; if (ci < grp.size()) cur_s = &blocks[grp[ci] + 1]; }
      else { *cur_s += std::to_string(x); *cur_s += ' '; }
    }
    fwrite(blocks[0].data(), 1, blocks[0].size(), f);
    for (int p = 0; p < P; p++) { fprintf(f, "c point %d\n", p); fwrite(blocks[p + 1].data(), 1, blocks[p + 1].size(), f); }
    fclose(f);
  }
  int var() { return ++nv; }
  void exactly_one(const std::vector<int>& xs) {
    add(xs);
    for (size_t a = 0; a < xs.size(); a++) for (size_t b = a + 1; b < xs.size(); b++) add({-xs[a], -xs[b]});
  }
  void write(const std::string& path, const std::string& comment) const {
    FILE* f = fopen(path.c_str(), "w");
    if (!f) die("cannot write " + path);
    fprintf(f, "c %s\np cnf %d %zu\n", comment.c_str(), nv, ncl);
    std::string out;
    out.reserve(1 << 20);
    for (int x : buf) {
      if (x == 0) out += "0\n"; else { out += std::to_string(x); out += ' '; }
      if (out.size() > (1 << 20) - 64) { fwrite(out.data(), 1, out.size(), f); out.clear(); }
    }
    fwrite(out.data(), 1, out.size(), f);
    fclose(f);
  }
};

struct ElimBound { int j, c, E; };   // under x_j = c at most E gates may vanish
struct EncOpts {
  bool alldiff = true, tri = true, ess = true, order = true, mono = true, dep = true;
  bool cegar = false;   // only clauses that are valid on any subset of the points; per-point clauses are grouped
  bool symf = true;     // first-use order of the inputs along every involution of the group
  bool sens = false;    // reader sensitivity clauses
  bool elimDead = false; // elimination also counts gates that are no longer needed after the restriction
  bool elimSem = false;  // elimination also counts gates whose column on the restricted points is constant or repeated
  std::vector<ElimBound> elim;
};

// Cover pairs (p, q) of the reduced points: pattern(p) is a proper subset of pattern(q) and no point lies between.
// In a monotone basis every wire w has w(p) <= w(q) for such pairs.
static std::vector<std::pair<int, int>> cover_pairs(const Prob& pr) {
  int P = pr.P, N = pr.N;
  std::vector<std::pair<int, int>> out;
  if (P > 4096) return out;
  int Wn = (N + 63) / 64;
  std::vector<std::vector<u64>> pat(P, std::vector<u64>(Wn, 0));
  for (int p = 0; p < P; p++) for (int i = 0; i < N; i++) if (getbit(pr.in[i], p)) pat[p][i / 64] |= u64(1) << (i % 64);
  auto sub = [&](int a, int b) {   // pattern a strictly inside pattern b
    bool neq = false;
    for (int w = 0; w < Wn; w++) { if (pat[a][w] & ~pat[b][w]) return false; if (pat[a][w] != pat[b][w]) neq = true; }
    return neq;
  };
  for (int p = 0; p < P; p++) {
    std::vector<int> sup;
    for (int q = 0; q < P; q++) if (q != p && sub(p, q)) sup.push_back(q);
    for (int q : sup) {
      bool minimal = true;
      for (int r : sup) if (r != q && sub(r, q)) { minimal = false; break; }
      if (minimal) out.push_back({p, q});
    }
  }
  return out;
}

// Normal model: s gates; gate i reads two distinct earlier wires a < b (AND/OR) or one earlier wire (NOT, basis aon);
// gates sorted strictly by (b, a, op); every gate except an output is read; no gate column is constant, equals an
// input column or another gate's column on the points.
static void encode_normal(const Prob& pr, int s, const EncOpts& eo, Cnf& F, std::vector<std::vector<int>>* outsel = nullptr) {
  int N = pr.N, P = pr.P, K = pr.K;
  bool an = pr.allowNot;
  Layout L(N, P, s);
  F.nv = L.total;
  auto inbit = [&](int j, int p) { return getbit(pr.in[j], p); };
  for (int i = 0; i < s; i++) {
    int nW = N + i;
    for (int j = 0; j < N; j++) if (!pr.active[j]) { F.add({-L.s1(i, j)}); F.add({-L.s2(i, j)}); }
    F.add({-L.s1(i, nW - 1)});
    if (!an) { F.add({-L.s2(i, 0)}); F.add({-L.s1none(i)}); F.add({-L.ng(i)}); }
    else {
      F.add({-L.s1none(i), L.ng(i)}); F.add({L.s1none(i), -L.ng(i)});
      F.add({-L.ng(i), -L.t(i)});
    }
    std::vector<int> x1, x2;
    x1.push_back(L.s1none(i));
    for (int j = 0; j < nW; j++) { x1.push_back(L.s1(i, j)); x2.push_back(L.s2(i, j)); }
    F.exactly_one(x1); F.exactly_one(x2);
    for (int j = 0; j < nW; j++) for (int k = 0; k <= j; k++) F.add({-L.s1(i, j), -L.s2(i, k)});
    for (int j = 0; j < nW; j++) for (int p = 0; p < P; p++) {
      F.cur = p;
      if (j < N) {
        bool x = inbit(j, p);
        F.add({-L.s1(i, j), x ? L.A(i, p) : -L.A(i, p)});
        F.add({-L.s2(i, j), x ? L.B(i, p) : -L.B(i, p)});
      } else {
        int x = L.v(j - N, p);
        F.add({-L.s1(i, j), -L.A(i, p), x}); F.add({-L.s1(i, j), L.A(i, p), -x});
        F.add({-L.s2(i, j), -L.B(i, p), x}); F.add({-L.s2(i, j), L.B(i, p), -x});
      }
    }
    for (int p = 0; p < P; p++) {
      F.cur = p;
      int A = L.A(i, p), B = L.B(i, p), V = L.v(i, p), T = L.t(i), G = L.ng(i);
      auto addp = [&](std::vector<int> c) { if (an) c.push_back(G); F.add(c); };
      addp({-T, -V, A}); addp({-T, -V, B}); addp({-T, V, -A, -B});
      addp({T, V, -A}); addp({T, V, -B}); addp({T, -V, A, B});
      addp({-V, A, B}); addp({V, -A, -B});          // hold for AND and for OR
      if (an) { F.add({-G, -V, -B}); F.add({-G, V, B}); F.add({-G, -A}); }
    }
    F.cur = -1;
    if (eo.cegar) continue;     // the column constraints below speak about all points at once
    std::vector<int> c1, c0;
    for (int p = 0; p < P; p++) { c1.push_back(L.v(i, p)); c0.push_back(-L.v(i, p)); }
    F.add(c1); F.add(c0);
    for (int j = 0; j < N; j++) if (pr.active[j]) {
      std::vector<int> c;
      for (int p = 0; p < P; p++) c.push_back(inbit(j, p) ? -L.v(i, p) : L.v(i, p));
      F.add(c);
    }
  }
  // monotone basis: every gate column is monotone along the point order
  if (eo.mono && !an && !eo.cegar) {
    auto cp = cover_pairs(pr);
    for (int i = 0; i < s; i++) for (auto& [p, q] : cp) F.add({-L.v(i, p), L.v(i, q)});
  }
  // outputs
  std::vector<std::vector<int>> osel;
  if (K == 1) {
    for (int p = 0; p < P; p++) { F.cur = p; F.add({getbit(pr.tgt[0], p) ? L.v(s - 1, p) : -L.v(s - 1, p)}); }
    F.cur = -1;
    if (!eo.cegar) for (int i = 0; i + 1 < s; i++) {
      std::vector<int> c;
      for (int p = 0; p < P; p++) c.push_back(getbit(pr.tgt[0], p) ? -L.v(i, p) : L.v(i, p));
      F.add(c);
    }
  } else {
    osel.assign(K, std::vector<int>(N + s, 0));
    for (int k = 0; k < K; k++) {
      std::vector<int> xs;
      for (int w = 0; w < N + s; w++) {
        if (w < N) {
          if (!pr.active[w] || !match_on(pr.tgt[k], pr.in[w], pr.care[k])) continue;
          osel[k][w] = F.var(); xs.push_back(osel[k][w]);
        } else {
          osel[k][w] = F.var(); xs.push_back(osel[k][w]);
          for (int p = 0; p < P; p++) if (getbit(pr.care[k], p)) {
            F.cur = p;
            F.add({-osel[k][w], getbit(pr.tgt[k], p) ? L.v(w - N, p) : -L.v(w - N, p)});
          }
          F.cur = -1;
        }
      }
      F.exactly_one(xs);
    }
    std::vector<int> c;
    for (int k = 0; k < K; k++) c.push_back(osel[k][N + s - 1]);
    F.add(c);
  }
  if (outsel) *outsel = osel;
  // every gate but the last is read by a later gate (or is an output)
  for (int i = 0; i + 1 < s; i++) {
    std::vector<int> c;
    for (int i2 = i + 1; i2 < s; i2++) { c.push_back(L.s1(i2, N + i)); c.push_back(L.s2(i2, N + i)); }
    if (K > 1) for (int k = 0; k < K; k++) c.push_back(osel[k][N + i]);
    F.add(c);
  }
  // canonical order: (b, a, op) strictly increasing, where a = -1 for NOT and AND < OR
  if (eo.order) for (int i = 0; i + 1 < s; i++) {
    int nW = N + i;
    for (int k = 0; k < nW; k++) {
      for (int k2 = 0; k2 < k; k2++) F.add({-L.s2(i, k), -L.s2(i + 1, k2)});
      // same b: a must not decrease (none < 0 < 1 < ...)
      for (int j = 0; j < k; j++) {
        F.add({-L.s2(i, k), -L.s2(i + 1, k), -L.s1(i, j), -L.s1none(i + 1)});
        for (int j2 = 0; j2 < j; j2++) F.add({-L.s2(i, k), -L.s2(i + 1, k), -L.s1(i, j), -L.s1(i + 1, j2)});
        // same a and b: AND then OR
        F.add({-L.s2(i, k), -L.s2(i + 1, k), -L.s1(i, j), -L.s1(i + 1, j), L.t(i)});
        F.add({-L.s2(i, k), -L.s2(i + 1, k), -L.s1(i, j), -L.s1(i + 1, j), -L.t(i + 1)});
      }
      F.add({-L.s2(i, k), -L.s2(i + 1, k), -L.s1none(i), -L.s1none(i + 1)});
    }
  }
  // a gate never reads gate i together with an operand of gate i (the result would repeat a column or be constant)
  if (eo.tri) for (int i = 0; i < s; i++) for (int i2 = i + 1; i2 < s; i2++) for (int j = 0; j < N + i; j++) {
    F.add({-L.s2(i2, N + i), -L.s1(i2, j), -L.s1(i, j)});
    F.add({-L.s2(i2, N + i), -L.s1(i2, j), -L.s2(i, j)});
  }
  // essential inputs are read
  if (eo.ess) for (int j = 0; j < N; j++) if (pr.essential[j]) {
    std::vector<int> c;
    for (int i = 0; i < s; i++) { c.push_back(L.s1(i, j)); c.push_back(L.s2(i, j)); }
    F.add(c);
  }
  // Input symmetry inside the CNF. Let h in G be an involution, i.e. disjoint swaps (a_1 b_1)...(a_m b_m), a_t < b_t.
  // In the lexicographically least member of an orbit, the first gate that reads one of these inputs reads one of
  // the a_t: otherwise h would lower that gate's key and leave all earlier gates alone. So: a gate reads b_t only if
  // it or an earlier gate reads some a_u. (For S_n: inputs are first used in increasing order.)
  if (eo.symf && pr.G.size() > 1) {
    std::vector<std::vector<std::pair<int, int>>> invs;
    for (auto& h : pr.G) {
      bool inv = true, id = true;
      for (int j = 0; j < N; j++) { if (h[h[j]] != j) inv = false; if (h[j] != j) id = false; }
      if (!inv || id) continue;
      std::vector<std::pair<int, int>> pairs;
      for (int j = 0; j < N; j++) if (h[j] > j) pairs.push_back({j, h[j]});
      invs.push_back(pairs);
    }
    std::stable_sort(invs.begin(), invs.end(), [](const auto& x, const auto& y) { return x.size() < y.size(); });
    // with all transpositions of a set present, larger involutions inside it add nothing; keep it small anyway
    if (invs.size() > 400) invs.resize(400);
    if (!invs.empty()) {
      std::vector<std::vector<int>> rdv(s, std::vector<int>(N, 0)), usedv(s, std::vector<int>(N, 0));
      for (int i = 0; i < s; i++) for (int j = 0; j < N; j++) if (pr.active[j]) {
        int r = F.var(), u = F.var();
        rdv[i][j] = r; usedv[i][j] = u;
        F.add({-L.s1(i, j), r}); F.add({-L.s2(i, j), r}); F.add({-r, L.s1(i, j), L.s2(i, j)});
        if (i == 0) { F.add({-u, r}); F.add({u, -r}); }
        else { F.add({-u, r, usedv[i - 1][j]}); F.add({u, -r}); F.add({u, -usedv[i - 1][j]}); }
      }
      for (auto& pairs : invs) for (int i = 0; i < s; i++) for (auto& [a, b] : pairs) {
        std::vector<int> c{-rdv[i][b]};
        for (auto& [a2, b2] : pairs) c.push_back(usedv[i][a2]);
        F.add(c);
      }
    }
  }
  // Sensitivity of the readers. (A) Two cared points p0, p1 of one output that differ only in input j and have
  // different targets: if every gate that reads x_j had equal values at p0 and p1, so would every gate, and the
  // output. So some reader of x_j differs there. (B) Monotone bases: a cared true point p with x_j = 1 such that
  // p without j lies below some cared false point: the circuit is 0 at "p without j" by monotonicity, so some
  // reader of x_j is 1 at p. (For kn_n with a single AND reader this is rule F6 of src/knsat.)
  if (eo.sens && !eo.cegar) {
    std::vector<int> act;
    for (int j = 0; j < N; j++) if (pr.active[j]) act.push_back(j);
    int n = (int)act.size();
    std::vector<std::string> pat(P, std::string(n, '0'));
    for (int p = 0; p < P; p++) for (int q = 0; q < n; q++) if (getbit(pr.in[act[q]], p)) pat[p][q] = '1';
    std::unordered_map<std::string, int> idx;
    for (int p = 0; p < P; p++) idx[pat[p]] = p;
    auto below = [&](const std::string& a, const std::string& b) {   // a <= b pointwise
      for (int q = 0; q < n; q++) if (a[q] == '1' && b[q] == '0') return false;
      return true;
    };
    for (int q = 0; q < n; q++) {
      int j = act[q];
      for (int p = 0; p < P; p++) {
        if (pat[p][q] != '1') continue;
        std::string y = pat[p]; y[q] = '0';
        auto it = idx.find(y);
        int p0 = it == idx.end() ? -1 : it->second;
        int mode = 0;     // 1: readers differ between p0 and p;  2: some reader is 1 at p
        for (int k = 0; k < K && !mode; k++) {
          if (!getbit(pr.care[k], p)) continue;
          if (K > 1 && match_on(pr.tgt[k], pr.in[j], pr.care[k])) continue;   // the output may be x_j itself
          if (p0 >= 0 && getbit(pr.care[k], p0) && getbit(pr.tgt[k], p0) != getbit(pr.tgt[k], p)) { mode = 1; break; }
          if (!an && getbit(pr.tgt[k], p)) {
            for (int f = 0; f < P && !mode; f++)
              if (getbit(pr.care[k], f) && !getbit(pr.tgt[k], f) && below(y, pat[f])) mode = 2;
          }
        }
        if (!mode) continue;
        std::vector<int> cl;
        for (int i = 0; i < s; i++) {
          int z = F.var();
          cl.push_back(z);
          F.add({-z, L.s1(i, j), L.s2(i, j)});
          if (mode == 2) F.add({-z, L.v(i, p)});
          else if (!an) { F.add({-z, L.v(i, p)}); F.add({-z, -L.v(i, p0)}); }
          else { F.add({-z, L.v(i, p), L.v(i, p0)}); F.add({-z, -L.v(i, p), -L.v(i, p0)}); }
        }
        F.add(cl);
      }
    }
  }
  // structural support: dep[j][i] <-> gate i depends on input j through its operands. A gate that does not depend
  // on input j has the same value on two points that differ only in input j.
  if (eo.dep && !eo.cegar) {
    std::vector<int> act;
    for (int j = 0; j < N; j++) if (pr.active[j]) act.push_back(j);
    int n = (int)act.size();
    std::vector<std::string> pat(P, std::string(n, '0'));
    for (int p = 0; p < P; p++) for (int q = 0; q < n; q++) if (getbit(pr.in[act[q]], p)) pat[p][q] = '1';
    std::unordered_map<std::string, int> idx;
    for (int p = 0; p < P; p++) idx[pat[p]] = p;
    for (int q = 0; q < n; q++) {
      int j = act[q];
      std::vector<std::pair<int, int>> pairs;    // (p with x_j = 0, p' with x_j = 1)
      for (int p = 0; p < P; p++) if (pat[p][q] == '0') {
        std::string y = pat[p]; y[q] = '1';
        auto it = idx.find(y);
        if (it != idx.end()) pairs.push_back({p, it->second});
      }
      if (pairs.empty()) continue;
      std::vector<int> dep(s), dA(s), dB(s);
      for (int i = 0; i < s; i++) { dep[i] = F.var(); dA[i] = F.var(); dB[i] = F.var(); }
      for (int i = 0; i < s; i++) {
        for (int w = 0; w < N + i; w++) {
          if (w < N) {
            F.add({-L.s1(i, w), w == j ? dA[i] : -dA[i]});
            F.add({-L.s2(i, w), w == j ? dB[i] : -dB[i]});
          } else {
            int d = dep[w - N];
            F.add({-L.s1(i, w), -dA[i], d}); F.add({-L.s1(i, w), dA[i], -d});
            F.add({-L.s2(i, w), -dB[i], d}); F.add({-L.s2(i, w), dB[i], -d});
          }
        }
        F.add({-L.s1none(i), -dA[i]});
        F.add({-dep[i], dA[i], dB[i]}); F.add({dep[i], -dA[i]}); F.add({dep[i], -dB[i]});
        for (auto& [p0, p1] : pairs) {
          F.add({dep[i], -L.v(i, p0), L.v(i, p1)});
          F.add({dep[i], L.v(i, p0), -L.v(i, p1)});
        }
      }
      if (K == 1 && pr.essential[j]) F.add({dep[s - 1]});
    }
  }
  // all gate columns pairwise distinct; dw[i][i2] = first of P witness variables "gates i and i2 differ at point p"
  std::vector<std::vector<int>> dw(s, std::vector<int>(s, 0));
  if (eo.alldiff && !eo.cegar) for (int i = 0; i < s; i++) for (int i2 = i + 1; i2 < s; i2++) {
    if (K == 1 && i2 == s - 1) continue;   // covered by the unit target column
    std::vector<int> c;
    for (int p = 0; p < P; p++) {
      int d = F.var();
      if (p == 0) dw[i][i2] = d;
      c.push_back(d);
      F.add({-d, L.v(i, p), L.v(i2, p)}); F.add({-d, -L.v(i, p), -L.v(i2, p)});
    }
    F.add(c);
  }
  // elimination: put x_j = c and simplify. Every gate that reads x_j vanishes, a gate that became constant makes its
  // readers vanish, AND of a 0 / OR of a 1 / NOT of a constant is constant again. At most E gates may vanish.
  for (auto& eb : eo.elim) {
    int j = eb.j, c = eb.c, E = eb.E;
    if (j < 0 || j >= N || !pr.active[j]) continue;
    if (E >= s) continue;
    if (E < 0) { F.add(std::vector<int>{}); continue; }
    std::vector<int> e(s), cz(s), co(s);
    for (int i = 0; i < s; i++) { e[i] = F.var(); cz[i] = F.var(); co[i] = F.var(); }
    for (int i = 0; i < s; i++) {
      int T = L.t(i), G = L.ng(i);
      for (int sel : {L.s1(i, j), L.s2(i, j)}) {
        F.add({-sel, e[i]});
        if (c == 0) { F.add({-sel, -T, cz[i]}); if (an) F.add({-sel, -G, co[i]}); }
        else { F.add({-sel, T, G, co[i]}); if (an) F.add({-sel, -G, cz[i]}); }
      }
      for (int h = 0; h < i; h++) for (int sel : {L.s1(i, N + h), L.s2(i, N + h)}) {
        F.add({-sel, -cz[h], e[i]}); F.add({-sel, -co[h], e[i]});
        F.add({-sel, -cz[h], -T, cz[i]});
        F.add({-sel, -co[h], T, G, co[i]});
        if (an) { F.add({-sel, -cz[h], -G, co[i]}); F.add({-sel, -co[h], -G, cz[i]}); }
      }
    }
    // Semantic version (needs the distinctness witnesses, so not with --cegar): on the points with x_j = c, a gate
    // whose column is constant there, or equals there the column of an earlier wire other than x_j, can be replaced
    // by that constant / wire. The gates that are not redundant in this sense form a circuit for the cofactor, so
    // at most E gates are redundant. This contains the structural rule above and also catches gates that become
    // equal after the restriction.
    // It must see ALL cared points with x_j = c: after the monotone point reduction it does not, so it is skipped.
    if (eo.elimSem && eo.alldiff && !eo.cegar && pr.allPoints) {
      std::vector<int> Pc;
      for (int p = 0; p < P; p++) if ((int)getbit(pr.in[j], p) == c) Pc.push_back(p);
      if (!Pc.empty()) {
        std::vector<int> x(s);
        for (int i = 0; i < s; i++) {
          int red = F.var();
          std::vector<int> c1{red}, c0{red};
          for (int p : Pc) { c1.push_back(L.v(i, p)); c0.push_back(-L.v(i, p)); }
          F.add(c1); F.add(c0);
          for (int w = 0; w < N; w++) if (w != j && pr.active[w]) {
            std::vector<int> cl{red};
            for (int p : Pc) cl.push_back(getbit(pr.in[w], p) ? -L.v(i, p) : L.v(i, p));
            F.add(cl);
          }
          for (int i0 = 0; i0 < i; i0++) {
            std::vector<int> cl{red};
            if (dw[i0][i]) for (int p : Pc) cl.push_back(dw[i0][i] + p);
            else for (int p : Pc) cl.push_back(getbit(pr.tgt[0], p) ? -L.v(i0, p) : L.v(i0, p));   // i is the output gate
            F.add(cl);
          }
          x[i] = F.var();
          F.add({-e[i], x[i]}); F.add({-red, x[i]});
        }
        e = x;
      }
    }
    // Dead gates vanish as well: a kept gate is only needed if it is an output or some reader of it is neither
    // constant nor dead itself. un[i] = gate i is not needed. x[i] = gate i is gone (vanished or dead).
    if (eo.elimDead) {
      std::vector<int> un(s, 0), x(s);
      for (int i = 0; i < s; i++) if (!(K == 1 && i == s - 1)) un[i] = F.var();
      for (int i = 0; i < s; i++) {
        x[i] = F.var();
        F.add({-e[i], x[i]});
        if (!un[i]) continue;
        F.add({-un[i], x[i]});
        std::vector<int> c{un[i]};
        for (int r2 = i + 1; r2 < s; r2++) {
          int w = F.var();
          c.push_back(w);
          F.add({-w, L.s1(r2, N + i), L.s2(r2, N + i)});
          F.add({-w, -cz[r2]}); F.add({-w, -co[r2]});
          if (un[r2]) F.add({-w, -un[r2]});
        }
        if (K > 1) for (int k = 0; k < K; k++) c.push_back(osel[k][N + i]);
        F.add(c);
      }
      e = x;
    }
    if (E == 0) { for (int i = 0; i < s; i++) F.add({-e[i]}); continue; }
    // sequential counter: r[i][k] = at least k+1 of e[0..i] are true
    std::vector<std::vector<int>> r(s, std::vector<int>(E));
    for (int i = 0; i < s; i++) for (int k = 0; k < E; k++) r[i][k] = F.var();
    for (int i = 0; i < s; i++) {
      F.add({-e[i], r[i][0]});
      if (i > 0) {
        for (int k = 0; k < E; k++) F.add({-r[i - 1][k], r[i][k]});
        for (int k = 1; k < E; k++) F.add({-e[i], -r[i - 1][k - 1], r[i][k]});
        F.add({-e[i], -r[i - 1][E - 1]});
      }
    }
  }
}

// Full model (Lean semantics, FORMAT.md): every gate is op(x, y) with x, y in {FALSE, TRUE} + earlier wires (basis
// ao2: earlier wires only), x = y allowed, NOT reads x; no ordering, no "used", no distinctness. Outputs read FALSE
// (a missing wire) or any wire. Satisfiable iff a circuit with AT MOST s gates exists.
static void encode_full(const Prob& pr, int s, Cnf& F, std::vector<std::vector<int>>* outsel) {
  int N = pr.N, P = pr.P, K = pr.K;
  bool an = pr.allowNot, ao2 = pr.basis == "ao2";
  LayoutF L(N, P, s);
  F.nv = L.total;
  for (int i = 0; i < s; i++) {
    int E = L.E(i);
    std::vector<int> x1, x2;
    for (int x = 0; x < E; x++) { x1.push_back(L.s1(i, x)); x2.push_back(L.s2(i, x)); }
    F.exactly_one(x1); F.exactly_one(x2);
    if (ao2) for (int x = 0; x < 2; x++) { F.add({-L.s1(i, x)}); F.add({-L.s2(i, x)}); }
    if (!an) F.add({-L.ng(i)}); else F.add({-L.ng(i), -L.t(i)});
    for (int x = 0; x < E; x++) for (int p = 0; p < P; p++) {
      int w = x - 2;
      if (x < 2 || w < N) {
        bool val = x == 0 ? false : x == 1 ? true : getbit(pr.in[w], p);
        F.add({-L.s1(i, x), val ? L.A(i, p) : -L.A(i, p)});
        F.add({-L.s2(i, x), val ? L.B(i, p) : -L.B(i, p)});
      } else {
        int y = L.v(w - N, p);
        F.add({-L.s1(i, x), -L.A(i, p), y}); F.add({-L.s1(i, x), L.A(i, p), -y});
        F.add({-L.s2(i, x), -L.B(i, p), y}); F.add({-L.s2(i, x), L.B(i, p), -y});
      }
    }
    for (int p = 0; p < P; p++) {
      int A = L.A(i, p), B = L.B(i, p), V = L.v(i, p), T = L.t(i), G = L.ng(i);
      auto addp = [&](std::vector<int> c) { if (an) c.push_back(G); F.add(c); };
      addp({-T, -V, A}); addp({-T, -V, B}); addp({-T, V, -A, -B});
      addp({T, V, -A}); addp({T, V, -B}); addp({T, -V, A, B});
      if (an) { F.add({-G, -V, -A}); F.add({-G, V, A}); }
    }
  }
  std::vector<std::vector<int>> osel(K, std::vector<int>(N + s + 1, 0));   // index 0 = FALSE, 1 + w = wire w
  for (int k = 0; k < K; k++) {
    std::vector<int> xs;
    for (int x = 0; x <= N + s; x++) {
      osel[k][x] = F.var(); xs.push_back(osel[k][x]);
      for (int p = 0; p < P; p++) if (getbit(pr.care[k], p)) {
        bool want = getbit(pr.tgt[k], p);
        if (x == 0) { if (want) F.add({-osel[k][x]}); }
        else if (x - 1 < N) { if (getbit(pr.in[x - 1], p) != want) F.add({-osel[k][x]}); }
        else F.add({-osel[k][x], want ? L.v(x - 1 - N, p) : -L.v(x - 1 - N, p)});
      }
    }
    F.exactly_one(xs);
  }
  if (outsel) *outsel = osel;
}

// ------------------------------------------------------------------ canonical prefixes
// Sorted form of the relabelled prefix h(p), compared position by position with p.
// Returns -1 if sort(h p) < p, 0 if equal, +1 if greater.
static int cmp_relabel(const int* h, const PG* p, int d, int N) {
  int nidx[64];
  for (int t = 0; t < d; t++) nidx[t] = -1;
  u64 placed = 0;
  for (int pos = 0; pos < d; pos++) {
    PG best{0, 0, 0};
    int bt = -1;
    for (int t = 0; t < d; t++) {
      if ((placed >> t) & 1) continue;
      const PG& g = p[t];
      int x, y;
      if (g.b < N) y = h[g.b]; else { int q = nidx[g.b - N]; if (q < 0) continue; y = N + q; }
      if (g.op == 2) x = -1;
      else {
        if (g.a < N) x = h[g.a]; else { int q = nidx[g.a - N]; if (q < 0) continue; x = N + q; }
        if (x > y) std::swap(x, y);
      }
      PG c{g.op, x, y};
      if (bt < 0 || keyLess(c, best)) { best = c; bt = t; }
    }
    if (keyLess(best, p[pos])) return -1;
    if (keyLess(p[pos], best)) return 1;
    nidx[bt] = pos; placed |= u64(1) << bt;
  }
  return 0;
}

struct Ctx {
  const Prob& pr;
  int s;
  bool hasFirst = false;
  PG first{0, 0, 0};
  Ctx(const Prob& p, int s_) : pr(p), s(s_) {}

  bool minimal(const std::vector<PG>& p) const {
    int d = (int)p.size();
    for (auto& h : pr.G) if (cmp_relabel(h.data(), p.data(), d, pr.N) < 0) return false;
    return true;
  }
  Col gate_col(const PG& g, const std::vector<Col>& w) const {
    Col c(pr.W);
    for (int q = 0; q < pr.W; q++) {
      if (g.op == 0) c[q] = w[g.a][q] & w[g.b][q];
      else if (g.op == 1) c[q] = w[g.a][q] | w[g.b][q];
      else c[q] = ~w[g.b][q];
    }
    c[pr.W - 1] &= pr.lm;
    return c;
  }
  // structural validity of a prefix handed in from outside
  void check_prefix(const std::vector<PG>& p) const {
    if ((int)p.size() > s) die("prefix longer than s");
    for (size_t i = 0; i < p.size(); i++) {
      const PG& g = p[i];
      int nW = pr.N + (int)i;
      if (g.op < 0 || g.op > 2 || g.b < 0 || g.b >= nW) die("prefix: bad gate");
      if (g.op == 2 ? (!pr.allowNot || g.a != -1) : (g.a < 0 || g.a >= g.b)) die("prefix: bad gate");
      if (i && !keyLess(p[i - 1], g)) die("prefix: gates not in canonical order");
    }
  }
  std::vector<int> lits(const std::vector<PG>& p) const {
    Layout L(pr.N, pr.P, (int)p.size());
    std::vector<int> r;
    for (int i = 0; i < (int)p.size(); i++) {
      const PG& g = p[i];
      r.push_back(L.s2(i, g.b));
      if (g.op == 2) { r.push_back(L.s1none(i)); r.push_back(L.ng(i)); r.push_back(-L.t(i)); }
      else { r.push_back(L.s1(i, g.a)); r.push_back(g.op == 0 ? L.t(i) : -L.t(i)); }
    }
    return r;
  }
  // All one-gate extensions of p that can still lead to a normal circuit that is lexicographically least in its orbit.
  void children(const std::vector<PG>& p, std::vector<std::vector<PG>>& out) const {
    int N = pr.N, K = pr.K, d = (int)p.size();
    if (d >= s) return;
    std::vector<Col> w(pr.in.begin(), pr.in.end());
    for (auto& g : p) w.push_back(gate_col(g, w));
    int nW = N + d;
    std::vector<char> rd(nW + 1, 0);
    for (auto& g : p) { rd[g.b] = 1; if (g.a >= 0) rd[g.a] = 1; }
    // may gate t (t < d) be an output?  (K > 1 only; for K = 1 the output is the last gate)
    std::vector<char> canOut(d + 1, 0);
    if (K > 1) for (int t = 0; t < d; t++) for (int k = 0; k < K; k++) if (match_on(w[N + t], pr.tgt[k], pr.care[k])) canOut[t] = 1;
    std::vector<PG> q = p;
    q.push_back(PG{0, 0, 0});
    int r = s - (d + 1);
    int b0 = d ? p.back().b : 0;
    for (int b = b0; b < nW; b++) {
      if (b < N && !pr.active[b]) continue;
      for (int a = pr.allowNot ? -1 : 0; a < b; a++) {
        if (a >= 0 && a < N && !pr.active[a]) continue;
        for (int op = (a < 0 ? 2 : 0); op <= (a < 0 ? 2 : 1); op++) {
          PG g{op, a, b};
          if (d && !keyLess(p.back(), g)) continue;
          if (d == 0 && hasFirst && !keyEq(g, first)) continue;
          Col c = gate_col(g, w);
          if (col_const(pr, c)) continue;
          bool dup = false;
          for (int x = 0; x < nW && !dup; x++) if ((x >= N || pr.active[x]) && w[x] == c) dup = true;
          if (dup) continue;
          bool newCanOut = false;
          if (K == 1) {
            bool isT = c == pr.tgt[0];
            if (r == 0 ? !isT : isT) continue;
          } else {
            for (int k = 0; k < K; k++) if (match_on(c, pr.tgt[k], pr.care[k])) newCanOut = true;
            if (r == 0 && !newCanOut) continue;
          }
          // wires that still have to be read by one of the r remaining gates
          int needs = 0, low = 0;
          auto isread = [&](int x) { return rd[x] || x == g.a || x == g.b; };
          for (int x = 0; x < N; x++) if (pr.essential[x] && !isread(x)) { needs++; if (x < g.b) low++; }
          for (int t = 0; t < d; t++) if (!isread(N + t) && !canOut[t]) { needs++; if (N + t < g.b) low++; }
          if (K == 1) {
            // the new gate is unread; at the end exactly the last gate is unread; a gate removes at most one
            if (r == 0 ? needs != 0 : needs + 1 > r + 1) continue;
          } else {
            int self = newCanOut ? 0 : 1;
            if (r == 0 ? needs != 0 : 2 * r < needs + self + std::max(0, r - K)) continue;
          }
          if (low > r) continue;   // every later gate has b >= g.b, so it reads at most one wire below g.b
          q[d] = g;
          if (!minimal(q)) continue;
          out.push_back(q);
        }
      }
    }
  }
};

static std::vector<std::vector<PG>> expand_level(const Ctx& cx, const std::vector<std::vector<PG>>& cur, int T) {
  std::vector<std::vector<std::vector<PG>>> res(cur.size());
  std::atomic<size_t> nx{0};
  auto work = [&] { for (size_t i; (i = nx++) < cur.size();) cx.children(cur[i], res[i]); };
  std::vector<std::thread> th;
  for (int t = 0; t < std::max(1, T); t++) th.emplace_back(work);
  for (auto& t : th) t.join();
  std::vector<std::vector<PG>> out;
  for (auto& v : res) for (auto& p : v) out.push_back(std::move(p));
  return out;
}

static void print_cube(const Ctx& cx, const std::vector<PG>& p) {
  std::string line = prefix_str(p) + "\t";
  for (int x : cx.lits(p)) { line += std::to_string(x); line += ' '; }
  line += "\n";
  fputs(line.c_str(), stdout);
}

// ------------------------------------------------------------------ decode a model
static int cmd_decode(const Prob& pr, int s, bool full, bool alldiffUnused) {
  std::vector<char> pos;
  {
    int x;
    while (std::cin >> x) if (x > 0) { if ((size_t)x >= pos.size()) pos.resize(x + 1, 0); pos[x] = 1; }
  }
  auto on = [&](int v) { return v > 0 && (size_t)v < pos.size() && pos[v]; };
  Circuit c;
  c.N = pr.N;
  int N = pr.N;
  if (!full) {
    Layout L(N, pr.P, s);
    for (int i = 0; i < s; i++) {
      int a = -1, b = -1;
      for (int j = 0; j < N + i; j++) { if (on(L.s1(i, j))) a = j; if (on(L.s2(i, j))) b = j; }
      Gate g;
      if (on(L.ng(i))) { g.op = NOT; g.nin = 1; g.a = b; g.b = 0; }
      else { g.op = on(L.t(i)) ? AND : OR; g.nin = 2; g.a = a; g.b = b; }
      if (b < 0 || (g.op != NOT && a < 0)) die("decode: model selects no operand for gate " + std::to_string(i));
      c.gates.push_back(g);
    }
    if (pr.K == 1) c.outs.push_back(N + s - 1);
    else {
      Cnf F; std::vector<std::vector<int>> osel;
      EncOpts eo; eo.alldiff = false; eo.tri = false; eo.ess = false; eo.order = false; eo.dep = false; eo.symf = false; eo.sens = false;
      encode_normal(pr, s, eo, F, &osel);   // output selectors are allocated right after the gate blocks
      for (int k = 0; k < pr.K; k++) {
        int o = -1;
        for (int w = 0; w < N + s; w++) if (on(osel[k][w])) o = w;
        if (o < 0) die("decode: no output selected");
        c.outs.push_back(o);
      }
    }
  } else {
    LayoutF L(N, pr.P, s);
    int missing = N + s + 1;
    for (int i = 0; i < s; i++) {
      int x = -1, y = -1;
      for (int e = 0; e < L.E(i); e++) { if (on(L.s1(i, e))) x = e; if (on(L.s2(i, e))) y = e; }
      if (x < 0 || y < 0) die("decode: model selects no operand");
      Gate g;
      auto wire = [&](int e) { return e == 0 ? missing : e - 2; };
      if (on(L.ng(i))) {
        if (x == 1) { g.op = OR; g.nin = 0; }            // NOT TRUE = false
        else if (x == 0) { g.op = NOT; g.nin = 0; }      // NOT [] = true
        else { g.op = NOT; g.nin = 1; g.a = wire(x); }
      } else {
        bool isAnd = on(L.t(i));
        if (x == 1 && y == 1) { g.op = AND; g.nin = 0; }                       // true
        else if (x == 1 || y == 1) {
          int o = x == 1 ? y : x;
          if (isAnd) { g.op = AND; g.nin = 1; g.a = wire(o); }                 // copy (FALSE -> missing wire)
          else { g.op = AND; g.nin = 0; }                                      // x OR TRUE = true
        } else { g.op = isAnd ? AND : OR; g.nin = 2; g.a = wire(x); g.b = wire(y); }
      }
      c.gates.push_back(g);
    }
    Cnf F; std::vector<std::vector<int>> osel;
    encode_full(pr, s, F, &osel);
    for (int k = 0; k < pr.K; k++) {
      int o = -1;
      for (int x = 0; x <= N + s; x++) if (on(osel[k][x])) o = x;
      if (o < 0) die("decode: no output selected");
      c.outs.push_back(o == 0 ? missing : o - 1);
    }
  }
  Verdict v = verify(pr.sp, c);
  std::string why;
  bool bok = basis_ok(c, pr.basis, &why);
  if (!v.ok || !bok) {
    std::cerr << "decode: circuit FAILS verification (wrong=" << v.wrong << " " << why << ")\n";
    write_circuit(std::cerr, c);
    return 1;
  }
  write_circuit(std::cout, c);
  return 0;
}

// ------------------------------------------------------------------ brute force (validation)
// Works on the ORIGINAL spec columns (no point reduction, no symmetry, no ordering).
struct Brute {
  const Spec& sp;
  bool an, ao2, full;
  int N;
  size_t W;
  std::vector<u64> buf;    // wires 0..N+depth-1; in full mode two extra leading wires FALSE, TRUE
  int nw = 0;
  u64 nodes = 0, cap = ~u64(0);
  bool capped = false;
  Brute(const Spec& s, const std::string& basis, bool full_) : sp(s), an(basis == "aon"), ao2(basis == "ao2"), full(full_) {
    N = s.N; W = s.W;
    buf.assign((size_t)(N + 2 + 40) * W, 0);
    if (full) {
      for (size_t w = 0; w < W; w++) { buf[w] = 0; buf[W + w] = ~u64(0); }
      buf[2 * W - 1] = s.lastmask();
      nw = 2;
    }
    for (int i = 0; i < N; i++) { std::memcpy(&buf[(size_t)nw * W], s.in[i].data(), W * 8); nw++; }
  }
  bool wire_matches(const u64* c, int k) const {
    for (size_t w = 0; w < W; w++) if ((c[w] ^ sp.tgt[k][w]) & sp.care[k][w]) return false;
    return true;
  }
  bool done() const {
    for (int k = 0; k < sp.K; k++) {
      bool ok = false;
      for (int x = 0; x < nw && !ok; x++) {
        if (full && x == 1) continue;             // TRUE is not a wire an output can name
        ok = wire_matches(&buf[(size_t)x * W], k);
      }
      if (!ok && !full) { std::vector<u64> z(W, 0); ok = wire_matches(z.data(), k); }
      if (!ok) return false;
    }
    return true;
  }
  bool dfs(int left) {
    if (done()) return true;
    if (left == 0) return false;
    if (nodes > cap) { capped = true; return false; }
    u64* O = &buf[(size_t)nw * W];
    u64 lmask = sp.lastmask();
    int lo = (full && ao2) ? 2 : 0;
    for (int b = lo; b < nw; b++) {
      const u64* Bc = &buf[(size_t)b * W];
      for (int a = lo; a <= b; a++) {
        if (!full && a == b) continue;
        const u64* Ac = &buf[(size_t)a * W];
        for (int op = 0; op < 2; op++) {
          nodes++;
          bool allz = true, allo = true;
          for (size_t w = 0; w < W; w++) {
            O[w] = op == 0 ? (Ac[w] & Bc[w]) : (Ac[w] | Bc[w]);
            u64 m = w == W - 1 ? lmask : ~u64(0);
            if (O[w] & m) allz = false;
            if ((O[w] & m) != m) allo = false;
          }
          if (!full) {
            if (allz || allo) continue;
            bool dup = false;
            for (int x = 0; x < nw && !dup; x++) dup = std::memcmp(&buf[(size_t)x * W], O, W * 8) == 0;
            if (dup) continue;
          }
          nw++;
          bool r = dfs(left - 1);
          nw--;
          if (r) return true;
        }
      }
      if (an) {
        nodes++;
        bool allz = true, allo = true;
        for (size_t w = 0; w < W; w++) {
          u64 m = w == W - 1 ? lmask : ~u64(0);
          O[w] = ~Bc[w] & m;
          if (O[w]) allz = false;
          if (O[w] != m) allo = false;
        }
        if (!full) {
          if (allz || allo) continue;
          bool dup = false;
          for (int x = 0; x < nw && !dup; x++) dup = std::memcmp(&buf[(size_t)x * W], O, W * 8) == 0;
          if (dup) continue;
        }
        nw++;
        bool r = dfs(left - 1);
        nw--;
        if (r) return true;
      }
    }
    return false;
  }
};

// ------------------------------------------------------------------ main
int main(int argc, char** argv) {
  if (argc < 3) {
    std::cerr << "usage: cktsat-core prep|encode|cubes|serve|decode|brute SPEC --basis ao|aon|ao2 [-s S] ...\n";
    return 2;
  }
  std::string cmd = argv[1], specp = argv[2], basis = "ao", outp, firstS;
  int s = -1, depth = -1, T = std::getenv("PNP_THREADS") ? atoi(std::getenv("PNP_THREADS")) : 1, maxS = 6, maxDepth = 64;
  long minCubes = -1;
  double maxNodes = 3e9;
  int cofJ = -1, cofC = -1;
  size_t gcap = 400000;
  bool sym = true, full = false, monoRed = true;
  EncOpts eo;
  for (int i = 3; i < argc; i++) {
    std::string a = argv[i];
    auto nxt = [&]() -> std::string { if (i + 1 >= argc) die("missing value for " + a); return argv[++i]; };
    if (a == "--basis") basis = nxt();
    else if (a == "-s") s = atoi(nxt().c_str());
    else if (a == "-o") outp = nxt();
    else if (a == "--depth") depth = atoi(nxt().c_str());
    else if (a == "--min-cubes") minCubes = atol(nxt().c_str());
    else if (a == "--max-depth") maxDepth = atoi(nxt().c_str());
    else if (a == "--first") firstS = nxt();
    else if (a == "--gcap") gcap = (size_t)atol(nxt().c_str());
    else if (a == "--no-sym") sym = false;
    else if (a == "--no-mono-reduce") monoRed = false;
    else if (a == "--full-model" || a == "--full") full = true;
    else if (a == "--alldiff") eo.alldiff = atoi(nxt().c_str());
    else if (a == "--tri") eo.tri = atoi(nxt().c_str());
    else if (a == "--ess") eo.ess = atoi(nxt().c_str());
    else if (a == "--order") eo.order = atoi(nxt().c_str());
    else if (a == "--mono") eo.mono = atoi(nxt().c_str());
    else if (a == "--dep") eo.dep = atoi(nxt().c_str());
    else if (a == "--cegar") eo.cegar = true;
    else if (a == "--symf") eo.symf = atoi(nxt().c_str());
    else if (a == "--sens") eo.sens = atoi(nxt().c_str());
    else if (a == "--elim-dead") eo.elimDead = atoi(nxt().c_str());
    else if (a == "--elim-sem") eo.elimSem = atoi(nxt().c_str());
    else if (a == "--input") cofJ = atoi(nxt().c_str());
    else if (a == "--value") cofC = atoi(nxt().c_str());
    else if (a == "--elim-bounds") {       // j:c:E,j:c:E,...
      std::string v = nxt();
      for (auto& ch : v) if (ch == ':' || ch == ',') ch = ' ';
      std::istringstream is(v);
      ElimBound eb;
      while (is >> eb.j >> eb.c >> eb.E) eo.elim.push_back(eb);
    }
    else if (a == "--max") maxS = atoi(nxt().c_str());
    else if (a == "--max-nodes") maxNodes = atof(nxt().c_str());
    else if (a == "-j") T = atoi(nxt().c_str());
    else die("unknown option " + a);
  }
  if (cmd == "brute") {
    Spec sp = load_spec(specp);
    auto t0 = std::chrono::steady_clock::now();
    for (int k = 0; k <= maxS; k++) {
      Brute b(sp, basis, full);
      b.cap = (u64)maxNodes;
      bool r = b.dfs(k);
      if (!r && b.capped) { std::cout << "min ? (node cap hit at size " << k << ")\n"; return 0; }
      double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      std::cerr << "brute size " << k << ": " << (r ? "SAT" : "UNSAT") << "  nodes " << b.nodes << "  t " << dt << "s\n";
      if (r) { std::cout << "min " << k << "\n"; return 0; }
    }
    std::cout << "min >" << maxS << "\n";
    return 0;
  }
  Prob pr;
  // a cofactor is taken on ALL cared points (the reduced set would give a much weaker cofactor spec)
  build_prob(pr, specp, basis, sym && !full && cmd != "cofactor", gcap, monoRed && cmd != "cofactor");
  if (cmd == "prep") {
    int nact = 0, ness = 0;
    for (int i = 0; i < pr.N; i++) { nact += pr.active[i]; ness += pr.essential[i]; }
    // size 0: every output is constant false on its points (a missing wire) or equals an input there
    std::vector<int> o0;
    {
      Col z(pr.W, 0);
      for (int k = 0; k < pr.K; k++) {
        int w = -1;
        if (match_on(pr.tgt[k], z, pr.care[k])) w = pr.N;
        for (int i2 = 0; i2 < pr.N && w < 0; i2++) if (match_on(pr.tgt[k], pr.in[i2], pr.care[k])) w = i2;
        if (w < 0) { o0.clear(); break; }
        o0.push_back(w);
      }
    }
    // orbits of the inputs under the group (representative = least input of the orbit)
    std::vector<int> orb(pr.N);
    for (int i2 = 0; i2 < pr.N; i2++) orb[i2] = i2;
    for (bool ch = true; ch;) {
      ch = false;
      for (auto& h : pr.G) for (int i2 = 0; i2 < pr.N; i2++) {
        int m = std::min(orb[i2], orb[h[i2]]);
        if (orb[i2] != m || orb[h[i2]] != m) { orb[i2] = orb[h[i2]] = m; ch = true; }
      }
    }
    std::cout << "{\"orbit\":[";
    for (int i2 = 0; i2 < pr.N; i2++) std::cout << (i2 ? "," : "") << (pr.active[i2] ? orb[i2] : -1);
    std::cout << "],\"size0\":[";
    for (size_t k = 0; k < o0.size(); k++) std::cout << (k ? "," : "") << o0[k];
    std::cout << "],\"N\":" << pr.N << ",\"K\":" << pr.K << ",\"P\":" << pr.P << ",\"P_orig\":" << pr.sp.P
              << ",\"active\":" << nact << ",\"essential\":" << ness << ",\"group\":" << pr.G.size()
              << ",\"group_truncated\":" << (pr.gtrunc ? "true" : "false") << ",\"trivial\":" << pr.triv
              << ",\"trivial_input\":" << pr.trivIn << ",\"const_output\":" << (pr.constOutput ? "true" : "false") << "}\n";
    return 0;
  }
  if (cmd == "cofactor") {
    // the points with x_j = c, as a points spec over the inputs that are still active there (sorted: canonical text)
    if (outp.empty() || cofJ < 0 || cofJ >= pr.N || (cofC != 0 && cofC != 1)) die("cofactor needs --input J --value C -o FILE");
    std::vector<int> pts;
    for (int p = 0; p < pr.P; p++) if ((int)getbit(pr.in[cofJ], p) == cofC) pts.push_back(p);
    std::vector<int> keep;
    for (int i2 = 0; i2 < pr.N; i2++) {
      if (i2 == cofJ) continue;
      bool all0 = true, all1 = true, dupc = false;
      for (int p : pts) { if (getbit(pr.in[i2], p)) all0 = false; else all1 = false; }
      if (all0 || all1) continue;
      for (int k2 : keep) {
        bool same = true;
        for (int p : pts) if (getbit(pr.in[i2], p) != getbit(pr.in[k2], p)) { same = false; break; }
        if (same) { dupc = true; break; }
      }
      if (!dupc) keep.push_back(i2);
    }
    // Canonical text under renaming of the inputs (so that isomorphic cofactors share one cache entry): order the
    // inputs by an invariant and, if the tie classes are small enough, take the lexicographically least point list.
    std::vector<std::string> outs;
    for (int p : pts) {
      std::string b2;
      for (int k2 = 0; k2 < pr.K; k2++) b2 += !getbit(pr.care[k2], p) ? '-' : getbit(pr.tgt[k2], p) ? '1' : '0';
      outs.push_back(b2);
    }
    auto build = [&](const std::vector<int>& order) {
      std::vector<std::string> ls;
      for (size_t q = 0; q < pts.size(); q++) {
        std::string a2;
        for (int i2 : order) a2 += getbit(pr.in[i2], pts[q]) ? '1' : '0';
        ls.push_back("p " + a2 + " " + outs[q]);
      }
      std::sort(ls.begin(), ls.end());
      ls.erase(std::unique(ls.begin(), ls.end()), ls.end());
      return ls;
    };
    std::vector<std::string> sig;
    for (int i2 : keep) {
      std::map<std::string, int> cnt;
      for (size_t q = 0; q < pts.size(); q++) if (getbit(pr.in[i2], pts[q])) {
        int wgt = 0;
        for (int i3 : keep) wgt += getbit(pr.in[i3], pts[q]);
        cnt[outs[q] + "/" + std::to_string(wgt)]++;
      }
      std::string sg;
      for (auto& [k2, v2] : cnt) sg += k2 + ":" + std::to_string(v2) + ";";
      sig.push_back(sg);
    }
    std::vector<int> ord(keep.size());
    for (size_t q = 0; q < ord.size(); q++) ord[q] = (int)q;
    std::stable_sort(ord.begin(), ord.end(), [&](int x, int y) { return sig[x] < sig[y]; });
    std::vector<int> order;
    for (int q : ord) order.push_back(keep[q]);
    std::vector<std::string> lines = build(order);
    {
      // tie classes are runs of equal signatures; enumerate their permutations when there are few
      std::vector<std::pair<int, int>> runs;
      double total = 1;
      for (size_t q = 0; q < ord.size();) {
        size_t e2 = q;
        while (e2 < ord.size() && sig[ord[e2]] == sig[ord[q]]) e2++;
        runs.push_back({(int)q, (int)e2});
        for (size_t f2 = 2; f2 <= e2 - q; f2++) total *= (double)f2;
        q = e2;
      }
      if (total > 1 && total * (double)pts.size() <= 4e7) {
        std::vector<int> cur = order;
        std::function<void(size_t)> rec = [&](size_t ri) {
          if (ri == runs.size()) { auto ls = build(cur); if (ls < lines) lines = ls; return; }
          auto [b3, e3] = runs[ri];
          std::sort(cur.begin() + b3, cur.begin() + e3);
          do { rec(ri + 1); } while (std::next_permutation(cur.begin() + b3, cur.begin() + e3));
        };
        rec(0);
      }
    }
    std::ofstream f(outp);
    if (!f) die("cannot write " + outp);
    f << "type points\ninputs " << keep.size() << "\noutputs " << pr.K << "\n";
    for (auto& l : lines) f << l << "\n";
    std::cout << "{\"points\":" << lines.size() << ",\"inputs\":" << keep.size() << "}\n";
    return 0;
  }
  if (s < 1) die("need -s S with S >= 1");
  if (cmd == "encode") {
    if (outp.empty()) die("encode needs -o FILE");
    if (!full && pr.K > 1 && pr.constOutput) die("an output is constant on its points: use --full-model");
    Cnf F;
    std::vector<std::vector<int>> osel;
    if (full) encode_full(pr, s, F, nullptr); else encode_normal(pr, s, eo, F, &osel);
    std::string comment = std::string("cktsat ") + (full ? "full" : "normal") + " model, basis " + basis + ", s=" + std::to_string(s);
    if (eo.cegar && !full) {
      F.write_by_point(outp, comment + " (grouped by point)", pr.P);
      // what a worker needs to evaluate a model on all points
      std::ofstream m(outp + ".meta");
      Layout L(pr.N, pr.P, s);
      m << "{\"N\":" << pr.N << ",\"P\":" << pr.P << ",\"K\":" << pr.K << ",\"s\":" << s << ",\"gates\":[";
      for (int i = 0; i < s; i++)
        m << (i ? "," : "") << "[" << L.s1(i, 0) << "," << L.s2(i, 0) << "," << L.t(i) << "," << L.ng(i) << "]";
      auto colstr = [&](const Col& c) { std::string t; for (int p = 0; p < pr.P; p++) t += getbit(c, p) ? '1' : '0'; return t; };
      m << "],\"in\":[";
      for (int i = 0; i < pr.N; i++) m << (i ? "," : "") << "\"" << colstr(pr.in[i]) << "\"";
      m << "],\"tgt\":[";
      for (int k = 0; k < pr.K; k++) m << (k ? "," : "") << "\"" << colstr(pr.tgt[k]) << "\"";
      m << "],\"care\":[";
      for (int k = 0; k < pr.K; k++) m << (k ? "," : "") << "\"" << colstr(pr.care[k]) << "\"";
      m << "],\"osel\":[";
      for (size_t k = 0; k < osel.size(); k++) {
        m << (k ? "," : "") << "[";
        for (size_t w = 0; w < osel[k].size(); w++) m << (w ? "," : "") << osel[k][w];
        m << "]";
      }
      m << "]}\n";
    } else F.write(outp, comment);
    std::cout << "{\"vars\":" << F.nv << ",\"clauses\":" << F.ncl << "}\n";
    return 0;
  }
  if (cmd == "decode") return cmd_decode(pr, s, full, false);
  Ctx cx(pr, s);
  if (!firstS.empty()) {
    if (!parse_gate(firstS, cx.first)) die("bad --first");
    cx.hasFirst = true;
  }
  if (cmd == "cubes") {
    std::vector<std::vector<PG>> cur(1);
    int d = 0;
    while (d < s && d < maxDepth) {
      if (depth >= 0 && d >= depth) break;
      if (depth < 0 && d >= 1 && (long)cur.size() >= minCubes) break;
      cur = expand_level(cx, cur, T);
      d++;
      std::cerr << "cktsat-core: depth " << d << ": " << cur.size() << " canonical prefixes\n";
      if (cur.empty()) break;
    }
    std::cout << "depth " << d << " count " << cur.size() << "\n";
    for (auto& p : cur) print_cube(cx, p);
    return 0;
  }
  if (cmd == "serve") {
    std::string line;
    while (std::getline(std::cin, line)) {
      if (line == "quit") break;
      if (line.rfind("split ", 0) == 0) {
        std::vector<PG> p = parse_prefix(line.substr(6));
        cx.check_prefix(p);
        std::vector<std::vector<PG>> out;
        cx.children(p, out);
        std::cout << "n " << out.size() << "\n";
        for (auto& q : out) print_cube(cx, q);
        std::cout << "end" << std::endl;
      } else {
        std::cout << "error unknown command" << std::endl;
      }
    }
    return 0;
  }
  die("unknown command " + cmd);
}
