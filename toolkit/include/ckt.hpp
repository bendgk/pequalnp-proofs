// ckt.hpp — shared core for the toolkit's tools (header-only, C++20).
// Spec + Circuit formats are documented in ../FORMAT.md. Semantics mirror the Lean definitions
// (PEqualNP.CircuitLowerBounds.Circuit.eval) exactly: a wire index that does not exist yet reads false,
// AND[]=true, OR[]=false, NOT[]=true, NOT reads only its first input, missing output wire reads false.
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace pnp {
using u64 = uint64_t;
using Col = std::vector<u64>;  // one bit per point

enum Op : uint8_t { AND = 0, OR = 1, NOT = 2 };
inline const char* opname(Op o) { return o == AND ? "and" : o == OR ? "or" : "not"; }

struct Gate {
  Op op = AND;
  int nin = 2;        // number of inputs named (0..2)
  int a = 0, b = 0;   // wire indices (any non-negative int; see Lean semantics)
};

struct Circuit {
  int N = 0;                 // number of input wires
  std::vector<Gate> gates;   // gate j produces wire N+j
  std::vector<int> outs;     // output wire(s)
  int size() const { return (int)gates.size(); }
  int count(Op o) const { int c = 0; for (auto& g : gates) c += g.op == o; return c; }
};

struct Spec {
  std::string kind;          // "graph" | "tt" | "points"
  int N = 0, K = 1;          // inputs, outputs
  size_t P = 0, W = 0;       // points, 64-bit words per column
  int gn = 0, gm = 0;        // graph sides (kind == graph)
  std::vector<Col> in;       // N input columns
  std::vector<Col> tgt;      // K target columns
  std::vector<Col> care;     // K care masks (bit set = point matters)
  u64 lastmask() const { return (P % 64) ? ((u64(1) << (P % 64)) - 1) : ~u64(0); }
};

[[noreturn]] inline void die(const std::string& m) { std::cerr << "error: " << m << "\n"; std::exit(2); }

inline int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}
// hex string (optionally 0x-prefixed) -> little-endian words, nbits wide
inline Col hex_to_bits(std::string h, size_t nbits) {
  if (h.size() >= 2 && h[0] == '0' && (h[1] == 'x' || h[1] == 'X')) h = h.substr(2);
  Col w((nbits + 63) / 64, 0);
  size_t pos = 0;
  for (size_t i = h.size(); i-- > 0;) {
    int v = hexval(h[i]);
    if (v < 0) die("bad hex digit in spec");
    for (int k = 0; k < 4; k++, pos++)
      if ((v >> k) & 1) { if (pos >= nbits) die("hex number wider than expected"); w[pos / 64] |= u64(1) << (pos % 64); }
  }
  return w;
}
inline bool getbit(const Col& c, size_t p) { return (c[p / 64] >> (p % 64)) & 1; }
inline void setbit(Col& c, size_t p) { c[p / 64] |= u64(1) << (p % 64); }

inline Spec load_spec(const std::string& path) {
  std::ifstream f(path);
  if (!f) die("cannot open spec " + path);
  Spec s;
  std::string line, key;
  std::vector<std::string> rows, tts;
  std::vector<std::pair<std::string, std::string>> pts;
  while (std::getline(f, line)) {
    auto h = line.find('#');
    if (h != std::string::npos) line = line.substr(0, h);
    std::istringstream is(line);
    if (!(is >> key)) continue;
    if (key == "type") is >> s.kind;
    else if (key == "n") is >> s.gn;
    else if (key == "m") is >> s.gm;
    else if (key == "inputs") is >> s.N;
    else if (key == "outputs") is >> s.K;
    else if (key == "rows") { std::string t; while (is >> t) rows.push_back(t); }
    else if (key == "tt") { std::string t; is >> t; tts.push_back(t); }
    else if (key == "p") { std::string a, b; is >> a >> b; pts.push_back({a, b}); }
    else die("unknown spec key: " + key);
  }
  if (s.kind == "graph") {
    int n = s.gn, m = s.gm;
    if ((int)rows.size() != n) die("graph spec: need n rows");
    s.N = n + m; s.K = 1; s.P = (size_t)n * m; s.W = (s.P + 63) / 64;
    s.in.assign(s.N, Col(s.W, 0)); s.tgt.assign(1, Col(s.W, 0)); s.care.assign(1, Col(s.W, 0));
    for (int u = 0; u < n; u++) {
      Col r = hex_to_bits(rows[u], m);
      for (int v = 0; v < m; v++) {
        size_t p = (size_t)u * m + v;
        setbit(s.in[u], p); setbit(s.in[n + v], p); setbit(s.care[0], p);
        if (getbit(r, v)) setbit(s.tgt[0], p);
      }
    }
  } else if (s.kind == "tt") {
    if (s.N < 1 || s.N > 26) die("tt spec: inputs must be 1..26");
    if ((int)tts.size() != s.K) die("tt spec: need one tt line per output");
    s.P = size_t(1) << s.N; s.W = (s.P + 63) / 64;
    s.in.assign(s.N, Col(s.W, 0));
    for (int i = 0; i < s.N; i++)
      for (size_t p = 0; p < s.P; p++) if ((p >> i) & 1) setbit(s.in[i], p);
    for (int k = 0; k < s.K; k++) {
      s.tgt.push_back(hex_to_bits(tts[k], s.P));
      Col c(s.W, ~u64(0)); c[s.W - 1] = s.lastmask(); s.care.push_back(c);
    }
  } else if (s.kind == "points") {
    s.P = pts.size(); s.W = (s.P + 63) / 64;
    if (!s.P) die("points spec: no points");
    s.in.assign(s.N, Col(s.W, 0)); s.tgt.assign(s.K, Col(s.W, 0)); s.care.assign(s.K, Col(s.W, 0));
    for (size_t p = 0; p < s.P; p++) {
      auto& [a, b] = pts[p];
      if ((int)a.size() != s.N || (int)b.size() != s.K) die("points spec: bad line width");
      for (int i = 0; i < s.N; i++) if (a[i] == '1') setbit(s.in[i], p);
      for (int k = 0; k < s.K; k++) {
        if (b[k] != '-') setbit(s.care[k], p);
        if (b[k] == '1') setbit(s.tgt[k], p);
      }
    }
  } else die("spec: unknown type '" + s.kind + "'");
  return s;
}

inline Circuit parse_circuit(std::istream& f) {
  Circuit c;
  std::string line, key;
  bool seenN = false;
  while (std::getline(f, line)) {
    auto h = line.find('#');
    if (h != std::string::npos) line = line.substr(0, h);
    std::istringstream is(line);
    if (!(is >> key)) continue;
    if (key == "inputs") { is >> c.N; seenN = true; }
    else if (key == "out") { int w; while (is >> w) c.outs.push_back(w); }
    else if (key == "and" || key == "or" || key == "not") {
      Gate g; g.op = key == "and" ? AND : key == "or" ? OR : NOT;
      int w, k = 0, v[2] = {0, 0};
      while (is >> w) { if (k < 2) v[k] = w; k++; }
      if (k > 2) die("gate with more than 2 inputs");
      g.nin = k; g.a = v[0]; g.b = v[1];
      c.gates.push_back(g);
    } else if (key == "end") break;   // lets several circuits share one stream
    else die("unknown circuit key: " + key);
  }
  if (!seenN) die("circuit: missing 'inputs N'");
  return c;
}
inline Circuit load_circuit(const std::string& path) {
  if (path == "-") return parse_circuit(std::cin);
  std::ifstream f(path);
  if (!f) die("cannot open circuit " + path);
  return parse_circuit(f);
}
inline void write_circuit(std::ostream& o, const Circuit& c, const std::string& comment = "") {
  if (!comment.empty()) o << "# " << comment << "\n";
  o << "inputs " << c.N << "\n";
  for (auto& g : c.gates) {
    o << opname(g.op);
    if (g.nin >= 1) o << " " << g.a;
    if (g.nin >= 2) o << " " << g.b;
    o << "\n";
  }
  o << "out";
  for (int w : c.outs) o << " " << w;
  o << "\n";
}
inline void save_circuit(const std::string& path, const Circuit& c, const std::string& comment = "") {
  std::ofstream f(path);
  if (!f) die("cannot write " + path);
  write_circuit(f, c, comment);
}

// Lean-exact bit-parallel evaluation. wires: (N + size) columns of W words, row-major.
// Returns the buffer; wire i is at &buf[i*W].
inline void eval(const Spec& s, const Circuit& c, std::vector<u64>& buf) {
  size_t W = s.W, tot = (size_t)c.N + c.gates.size();
  buf.assign(tot * W, 0);
  for (int i = 0; i < c.N && i < s.N; i++) std::memcpy(&buf[(size_t)i * W], s.in[i].data(), W * 8);
  u64 lm = s.lastmask();
  static thread_local std::vector<u64> zero;
  if (zero.size() < W) zero.assign(W, 0);
  for (size_t j = 0; j < c.gates.size(); j++) {
    const Gate& g = c.gates[j];
    size_t cur = (size_t)c.N + j;                       // wires that exist: 0..cur-1
    const u64* A = (g.nin >= 1 && g.a >= 0 && (size_t)g.a < cur) ? &buf[(size_t)g.a * W] : zero.data();
    const u64* B = (g.nin >= 2 && g.b >= 0 && (size_t)g.b < cur) ? &buf[(size_t)g.b * W] : zero.data();
    u64* O = &buf[cur * W];
    if (g.op == NOT) {                                  // !(headD false): no input -> true
      for (size_t w = 0; w < W; w++) O[w] = ~A[w];
    } else if (g.op == AND) {
      if (g.nin == 0) for (size_t w = 0; w < W; w++) O[w] = ~u64(0);
      else if (g.nin == 1) for (size_t w = 0; w < W; w++) O[w] = A[w];
      else for (size_t w = 0; w < W; w++) O[w] = A[w] & B[w];
    } else {
      if (g.nin == 0) for (size_t w = 0; w < W; w++) O[w] = 0;
      else if (g.nin == 1) for (size_t w = 0; w < W; w++) O[w] = A[w];
      else for (size_t w = 0; w < W; w++) O[w] = A[w] | B[w];
    }
    O[W - 1] &= lm;
  }
}

struct Verdict {
  bool ok = false;
  size_t wrong = 0;          // number of (output, point) pairs that are wrong (cared points only)
  int bad_out = -1; size_t bad_point = 0;   // first mismatch
};
// Checks all K outputs on all cared points. Does not check the basis; see basis_ok.
inline Verdict verify(const Spec& s, const Circuit& c) {
  Verdict v;
  if (c.N != s.N) die("circuit inputs != spec inputs");
  if ((int)c.outs.size() != s.K) die("circuit has " + std::to_string(c.outs.size()) + " outputs, spec wants " + std::to_string(s.K));
  std::vector<u64> buf; eval(s, c, buf);
  size_t tot = (size_t)c.N + c.gates.size();
  for (int k = 0; k < s.K; k++) {
    int o = c.outs[k];
    for (size_t w = 0; w < s.W; w++) {
      u64 val = (o >= 0 && (size_t)o < tot) ? buf[(size_t)o * s.W + w] : 0;
      u64 d = (val ^ s.tgt[k][w]) & s.care[k][w];
      if (d) {
        if (v.bad_out < 0) { v.bad_out = k; v.bad_point = w * 64 + __builtin_ctzll(d); }
        v.wrong += __builtin_popcountll(d);
      }
    }
  }
  v.ok = v.wrong == 0;
  return v;
}
// basis: "aon" (FanInTwo), "ao" (Monotone2), "ao2" (IsAO2: and/or, exactly 2 inputs, earlier wires)
inline bool basis_ok(const Circuit& c, const std::string& basis, std::string* why = nullptr) {
  for (size_t j = 0; j < c.gates.size(); j++) {
    const Gate& g = c.gates[j];
    auto fail = [&](const char* m) { if (why) *why = "gate " + std::to_string(j) + ": " + m; return false; };
    if (basis != "aon" && g.op == NOT) return fail("NOT gate in a monotone basis");
    if (basis == "ao2") {
      if (g.nin != 2) return fail("needs exactly 2 inputs");
      int cur = c.N + (int)j;
      if (g.a < 0 || g.a >= cur || g.b < 0 || g.b >= cur) return fail("reads a wire that is not earlier");
    }
  }
  return true;
}
// Describe a point for humans.
inline std::string point_str(const Spec& s, size_t p) {
  std::ostringstream o;
  if (s.kind == "graph") o << "u=" << p / s.gm << " v=" << p % s.gm;
  else { o << "x="; for (int i = 0; i < s.N; i++) o << (getbit(s.in[i], p) ? '1' : '0'); }
  return o.str();
}
}  // namespace pnp
