// cktcheck — exact, bit-parallel circuit checker (Lean Circuit.eval semantics).
//   cktcheck SPEC CKT [--basis aon|ao|ao2] [--max SIZE] [-q]
//   cktcheck SPEC -  --stream [-j T] ...   many circuits on stdin, each terminated by a line "end";
//                                          prints one line per circuit: index OK|BAD size wrong
//   cktcheck SPEC CKT --bench               throughput of the evaluator on this spec/circuit
// Exit status: 0 = every circuit OK, 1 = some circuit wrong, 2 = usage/parse error.
#include "../../include/ckt.hpp"
#include <atomic>
#include <chrono>
#include <thread>
using namespace pnp;

int main(int argc, char** argv) {
  std::string specp, cktp, basis = "aon";
  bool stream = false, bench = false, quiet = false;
  int maxsize = -1, T = std::getenv("PNP_THREADS") ? atoi(std::getenv("PNP_THREADS")) : 1;
  std::vector<std::string> pos;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--basis" && i + 1 < argc) basis = argv[++i];
    else if (a == "--max" && i + 1 < argc) maxsize = atoi(argv[++i]);
    else if (a == "-j" && i + 1 < argc) T = atoi(argv[++i]);
    else if (a == "--stream") stream = true;
    else if (a == "--bench") bench = true;
    else if (a == "-q") quiet = true;
    else pos.push_back(a);
  }
  if (pos.size() != 2 || (basis != "aon" && basis != "ao" && basis != "ao2")) {
    std::cerr << "usage: cktcheck SPEC CKT [--basis aon|ao|ao2] [--max SIZE] [--stream] [--bench] [-j T] [-q]\n";
    return 2;
  }
  Spec s = load_spec(pos[0]);
  if (stream) {
    std::vector<Circuit> cs;
    while (std::cin.peek() != EOF) {
      Circuit c = parse_circuit(std::cin);
      if (c.outs.empty() && c.gates.empty()) break;
      cs.push_back(c);
      while (std::cin.peek() == '\n') std::cin.get();
    }
    std::vector<int> res(cs.size());
    std::vector<size_t> wr(cs.size());
    std::atomic<size_t> nx{0};
    auto work = [&] {
      for (size_t i; (i = nx++) < cs.size();) {
        Verdict v = verify(s, cs[i]);
        bool ok = v.ok && basis_ok(cs[i], basis) && (maxsize < 0 || cs[i].size() <= maxsize);
        res[i] = ok; wr[i] = v.wrong;
      }
    };
    std::vector<std::thread> th;
    for (int t = 0; t < std::max(1, T); t++) th.emplace_back(work);
    for (auto& t : th) t.join();
    bool all = true;
    for (size_t i = 0; i < cs.size(); i++) {
      std::cout << i << (res[i] ? " OK " : " BAD ") << cs[i].size() << " " << wr[i] << "\n";
      all = all && res[i];
    }
    return all ? 0 : 1;
  }
  Circuit c = load_circuit(pos[1]);
  if (bench) {
    std::vector<u64> buf;
    auto t0 = std::chrono::steady_clock::now();
    size_t it = 0;
    double dt = 0;
    do { for (int k = 0; k < 64; k++) eval(s, c, buf); it += 64;
         dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); } while (dt < 1.0);
    std::cout << "evals/s " << it / dt << "  gate*points/s " << it / dt * c.size() * (double)s.P << "\n";
    return 0;
  }
  Verdict v = verify(s, c);
  std::string why;
  bool bok = basis_ok(c, basis, &why);
  bool sok = maxsize < 0 || c.size() <= maxsize;
  bool ok = v.ok && bok && sok;
  if (!quiet) {
    std::cout << (ok ? "OK" : "BAD") << "  size=" << c.size() << " (and " << c.count(AND) << ", or " << c.count(OR)
              << ", not " << c.count(NOT) << ")  inputs=" << s.N << " outputs=" << s.K << " points=" << s.P
              << " basis=" << basis << "\n";
    if (!v.ok) std::cout << "  wrong on " << v.wrong << " (output,point) pairs; first: output " << v.bad_out
                         << " at " << point_str(s, v.bad_point) << "\n";
    if (!bok) std::cout << "  basis violation: " << why << "\n";
    if (!sok) std::cout << "  size " << c.size() << " exceeds --max " << maxsize << "\n";
  }
  return ok ? 0 : 1;
}
