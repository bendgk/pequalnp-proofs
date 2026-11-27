// graphsynth — constructive multi-threaded search for small AND/OR(/NOT) circuits representing a bipartite graph.
// See ../../docs/graphsynth.md.   graphsynth SPEC -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X] ...
#include "sol.hpp"
#include "analyze.hpp"

using namespace gs;

struct Options {
  std::string spec, out, basis = "aon", shape = "auto", found, initCkt;
  int T = 1;
  double timeLimit = 0;
  u64 seed = 1;
  int rounds = -1;
  long iters = 0;              // 0: 25000 moves per rectangle of the cover
  int atom = -1;
  bool analyze = false, verbose = false;
  long proxyIters = 100000;   // proxy-pairing annealing moves per rectangle
  double reheat = 0.17;
  int wvariants = 3;
  int lnsAfter = 1 << 30;        // experimental LNS rounds from this round on
  int restart = 4;               // a lane restarts (new cover variant / new pairing) after this many rounds without progress
  long lnsSteps = 3000;
  double lnsT = 0.1;
  long witers = 300000;
  double wlambda = 3;
  double f2 = 0, f3 = 1, f4 = 3;
  std::string analyzeCkt;
  Params P;
};

static void usage() {
  std::cerr <<
    "usage: graphsynth SPEC -o OUT.ckt [--basis aon|ao] [-j T] [--time S] [--seed X]\n"
    "  search control\n"
    "    --rounds R  --iters N     R annealing rounds of N moves per thread (default 4 rounds, 25000 moves per rectangle);\n"
    "                              deterministic for fixed --seed, -j, --rounds, --iters. --time S instead: rounds until S seconds\n"
    "    --shape NAME              initial cover: auto (all, best kept) | atoms | concepts | wcover | rows | cols | grow | comp | init\n"
    "    --init-ckt FILE           read cover + cross pairing from a circuit of the shape OR_j (S_j AND T_j) (shape 'init')\n"
    "    --atom D                  side of the planted rectangles for --shape atoms (default round(sqrt(min(n,m)/2)))\n"
    "    --wvariants K --witers N --wlambda L   weight-annealed covers (shape wcover; auto only when n*m <= 4096)\n"
    "    --no-pairs  --no-cover    disable cross pairing / cover-changing moves\n"
    "    --proxy N                 proxy-pairing annealing moves per rectangle (default 100000; 0 = start unpaired)\n"
    "    --t0 X --t1 X --reheat X  temperatures: first round of a lineage t0 -> t1, later rounds reheat -> t1 (0.24, 0.09, 0.17)\n"
    "    --restart K               new lineage (new cover variant / pairing) after K rounds without progress (default 4, 0 = never)\n"
    "    --repair P  --wswap --wpair --welem --wrect --wrefit W   move mix;  --lns-after R --lns-steps N --lns-t X  experimental\n"
    "  output\n"
    "    --found DIR               also save every improvement as DIR/<spec>_<size>_<basis>.ckt\n"
    "    -v                        per-round log, move statistics, structure of the best state\n"
    "  graphsynth SPEC --analyze [--ckt C.ckt] [-v] structure report of the graph (and of a circuit; -v lists its terms)\n"
    "Threads: -j T, default $PNP_THREADS or 1. Every circuit written was verified with pnp::verify first.\n";
}

struct Shape { std::string name; Graph g; bool complemented = false; std::vector<Rect> cover; std::string note; std::vector<int> pairing; };

static pnp::Circuit finish(const Sol& s, bool complemented) {
  pnp::Circuit c = s.build();
  if (complemented) {
    pnp::Gate gt; gt.op = pnp::NOT; gt.nin = 1; gt.a = c.outs[0]; gt.b = 0;
    c.gates.push_back(gt); c.outs[0] = c.N + (int)c.gates.size() - 1;
  }
  return c;
}

int main(int argc, char** argv) {
  Options o;
  if (const char* e = std::getenv("PNP_THREADS")) o.T = std::max(1, atoi(e));
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto need = [&](const char* nm) { if (i + 1 >= argc) { std::cerr << "missing value for " << nm << "\n"; usage(); std::exit(2); } return std::string(argv[++i]); };
    if (a == "-o") o.out = need("-o");
    else if (a == "--basis") o.basis = need("--basis");
    else if (a == "-j") o.T = std::max(1, atoi(need("-j").c_str()));
    else if (a == "--time") o.timeLimit = atof(need("--time").c_str());
    else if (a == "--seed") o.seed = strtoull(need("--seed").c_str(), nullptr, 10);
    else if (a == "--rounds") o.rounds = atoi(need("--rounds").c_str());
    else if (a == "--iters") o.iters = atol(need("--iters").c_str());
    else if (a == "--shape") o.shape = need("--shape");
    else if (a == "--atom") o.atom = atoi(need("--atom").c_str());
    else if (a == "--no-pairs") o.P.allowPairs = false;
    else if (a == "--no-cover") o.P.allowCover = false;
    else if (a == "--t0") o.P.t0 = atof(need("--t0").c_str());
    else if (a == "--t1") o.P.t1 = atof(need("--t1").c_str());
    else if (a == "--lns-after") o.lnsAfter = atoi(need("--lns-after").c_str());
    else if (a == "--restart") o.restart = atoi(need("--restart").c_str());
    else if (a == "--lns-steps") o.lnsSteps = atol(need("--lns-steps").c_str());
    else if (a == "--lns-t") o.lnsT = atof(need("--lns-t").c_str());
    else if (a == "--wvariants") o.wvariants = atoi(need("--wvariants").c_str());
    else if (a == "--wlambda") o.wlambda = atof(need("--wlambda").c_str());
    else if (a == "--witers") o.witers = atol(need("--witers").c_str());
    else if (a == "--reheat") o.reheat = atof(need("--reheat").c_str());
    else if (a == "--proxy") o.proxyIters = atol(need("--proxy").c_str());
    else if (a == "--f2") o.f2 = atof(need("--f2").c_str());
    else if (a == "--f3") o.f3 = atof(need("--f3").c_str());
    else if (a == "--f4") o.f4 = atof(need("--f4").c_str());
    else if (a == "--repair") o.P.pRepair = atof(need("--repair").c_str());
    else if (a == "--wswap") o.P.wSwap = atof(need("--wswap").c_str());
    else if (a == "--wpair") o.P.wPair = atof(need("--wpair").c_str());
    else if (a == "--welem") o.P.wElem = atof(need("--welem").c_str());
    else if (a == "--wrefit") o.P.wRefit = atof(need("--wrefit").c_str());
    else if (a == "--wrect") o.P.wRect = atof(need("--wrect").c_str());
    else if (a == "--node-penalty") o.P.nodePenalty = atof(need("--node-penalty").c_str());
    else if (a == "--init-ckt") o.initCkt = need("--init-ckt");
    else if (a == "--found") o.found = need("--found");
    else if (a == "--analyze") o.analyze = true;
    else if (a == "--ckt") o.analyzeCkt = need("--ckt");
    else if (a == "-v") o.verbose = true;
    else if (a == "-h" || a == "--help") { usage(); return 0; }
    else if (!a.empty() && a[0] == '-') { std::cerr << "unknown option " << a << "\n"; usage(); return 2; }
    else if (o.spec.empty()) o.spec = a;
    else { usage(); return 2; }
  }
  if (o.spec.empty() || (o.basis != "aon" && o.basis != "ao")) { usage(); return 2; }
  pnp::Spec spec = pnp::load_spec(o.spec);
  Graph G = graph_from_spec(spec);
  if (o.analyze) return analyze(G, spec, o.analyzeCkt, o.verbose);
  if (o.out.empty()) { usage(); return 2; }
  if (o.rounds < 0 && o.timeLimit <= 0) o.rounds = 4;
  double tStart = now_s();
  auto elapsed = [&] { return now_s() - tStart; };
  std::string specName = o.spec.substr(o.spec.find_last_of('/') + 1);
  if (specName.size() > 5 && specName.substr(specName.size() - 5) == ".spec") specName.resize(specName.size() - 5);

  // ------------------------------------------------------------ initial covers ("shapes")
  std::vector<Shape> shapes;
  auto want = [&](const char* nm) { return o.shape == "auto" || o.shape == nm; };   // --shape init: only --init-ckt
  Rng rng0(o.seed * 7919 + 13);
  if (!o.initCkt.empty()) {
    pnp::Circuit ic = pnp::load_circuit(o.initCkt);
    Shape s; s.name = "init"; s.g = G;
    if (ic.N == spec.N && cover_from_circuit(spec, G, ic, s.cover, s.pairing)) {
      int pairs = 0; for (size_t a = 0; a < s.pairing.size(); a++) pairs += s.pairing[a] > (int)a;
      s.note = "cover and pairing read from " + o.initCkt + " (" + std::to_string(ic.size()) + " gates, " + std::to_string(pairs) + " cross pairs)";
      shapes.push_back(s);
    } else std::cerr << "[shape init] " << o.initCkt << " is not an OR of ANDs of crosses covering the graph exactly; ignored\n";
  }
  if (want("atoms")) {
    int d = o.atom > 0 ? o.atom : std::max(2, (int)std::lround(std::sqrt(std::min(G.n, G.m) / 2.0)));
    Cbo cbo(G, d, d, 20000000); cbo.run();
    Shape s; s.name = "atoms"; s.g = G;
    std::string log;
    if (!cbo.truncated && cover_from_candidates(G, cbo.out, s.cover, true, &log)) {
      s.note = "closed bicliques with both sides >= " + std::to_string(d) + ": " + std::to_string(cbo.out.size()) + " candidates; " + log;
      shapes.push_back(s);
    } else std::cerr << "[shape atoms] no exact cover from closed bicliques with sides >= " << d << (cbo.truncated ? " (enumeration truncated)" : "") << "\n";
  }
  if (want("concepts")) {
    Cbo cbo(G, 1, 1, 400000); cbo.run();
    Shape s; s.name = "concepts"; s.g = G;
    std::string log;
    if (!cbo.truncated && cover_from_candidates(G, cbo.out, s.cover, true, &log)) {
      s.note = "all " + std::to_string(cbo.out.size()) + " closed bicliques; " + log;
      shapes.push_back(s);
    } else std::cerr << "[shape concepts] skipped (more than 400000 closed bicliques)\n";
  }
  if (want("wcover") && (o.shape == "wcover" || (size_t)G.n * G.m <= 4096)) {
    // min-weight exact covers by annealing (several seeds, in parallel); even variants start from the lightest cover
    // built so far, odd ones from a grown cover
    std::vector<Rect> base;
    for (auto& s : shapes) if (s.name != "init" && (base.empty() || weight(s.cover) < weight(base))) base = s.cover;
    std::vector<Shape> ws(o.wvariants);
    std::atomic<int> nx{0};
    auto work = [&] {
      for (int v; (v = nx++) < o.wvariants;) {
        Rng rw(o.seed * 104729 + 31 * v + 5);
        std::vector<Rect> init = (v % 2 == 0 && !base.empty()) ? base : greedy_grow_cover(G, rw);
        WCover w(G, init);
        w.lambda = o.wlambda;
        w.run(rw, o.witers, 1.2, 0.15);
        ws[v].name = "wcover" + std::to_string(v); ws[v].g = G; ws[v].cover = w.r;
        ws[v].note = "weight-annealed cover (" + std::to_string(w.moves) + " compound moves)";
      }
    };
    std::vector<std::thread> th;
    for (int t = 0; t < std::min(o.T, o.wvariants); t++) th.emplace_back(work);
    for (auto& x : th) x.join();
    for (auto& s : ws) shapes.push_back(s);
  }
  if (want("rows")) { Shape s; s.name = "rows"; s.g = G; s.cover = row_stars(G); shapes.push_back(s); }
  if (want("cols")) { Shape s; s.name = "cols"; s.g = G; s.cover = col_stars(G); shapes.push_back(s); }
  if (want("grow")) { Shape s; s.name = "grow"; s.g = G; s.cover = greedy_grow_cover(G, rng0); shapes.push_back(s); }
  if (want("comp") && o.basis == "aon") {
    Shape s; s.name = "comp"; s.g = G.complement(); s.complemented = true;
    s.cover = greedy_grow_cover(s.g, rng0);
    s.note = "NOT of a cover of the complement graph";
    shapes.push_back(s);
  }
  if (shapes.empty()) { std::cerr << "no usable shape\n"; return 2; }
  for (auto& s : shapes)
    if (!covers_exactly(s.g, s.cover)) { std::cerr << "internal error: shape " << s.name << " is not an exact cover\n"; return 3; }

  // ------------------------------------------------------------ best-so-far bookkeeping
  long bestSize = -1;
  std::string bestShape;
  auto report = [&](const Sol& s, const Shape& sh, const char* stage) {
    pnp::Circuit c = finish(s, sh.complemented);
    pnp::Verdict v = pnp::verify(spec, c);
    std::string why;
    if (!v.ok || !pnp::basis_ok(c, o.basis, &why)) {
      std::cerr << "internal error: built circuit failed verification (shape " << sh.name << ", wrong " << v.wrong << ") " << why << "\n";
      std::exit(3);
    }
    if (bestSize < 0 || c.size() < bestSize) {
      bestSize = c.size(); bestShape = sh.name;
      std::string cm = "graphsynth " + specName + " shape=" + sh.name + " terms=" + std::to_string(s.nTerms) + " rects=" + std::to_string(s.nRects) + " seed=" + std::to_string(o.seed);
      pnp::save_circuit(o.out, c, cm);
      if (!o.found.empty()) pnp::save_circuit(o.found + "/" + specName + "_" + std::to_string(c.size()) + "_" + o.basis + ".ckt", c, cm);
      fprintf(stderr, "[%7.1fs] NEW BEST %d gates (and %d, or %d, not %d)  shape=%s terms=%d rects=%d inter=%d  (%s) verified\n", elapsed(), c.size(),
              c.count(pnp::AND), c.count(pnp::OR), c.count(pnp::NOT), sh.name.c_str(), s.nTerms, s.nRects, s.inter_count(), stage);
    }
  };

  // ------------------------------------------------------------ phase 1: every shape: proxy pairing + greedy sharing
  auto init_state = [&](Sol& s, const Shape& sh, Rng& r, bool log) {
    s = Sol();
    s.init(sh.g, sh.cover, sh.pairing.empty() ? nullptr : &sh.pairing);
    long trivial = s.total();
    double phi = 0; int pairs = (int)sh.cover.size() - s.nTerms;
    if (o.P.allowPairs && o.proxyIters > 0 && sh.pairing.empty()) {
      double st = o.f4 - o.f3;
      double f[9] = {0, 0, o.f2, o.f3, o.f4, o.f4 + st, o.f4 + 2 * st, o.f4 + 3 * st, o.f4 + 4 * st};
      phi = s.pair_proxy(r, o.proxyIters * (long)sh.cover.size(), f);
      pairs = (int)sh.cover.size() - s.nTerms;
    }
    s.greedy_pairs(r);
    if (log)
      fprintf(stderr, "[%7.1fs] shape %-8s rects=%d weight=%d  unshared=%ld  proxy pairing: %d cross pairs (value %.0f)  greedy-shared=%ld%s  %s\n", elapsed(), sh.name.c_str(),
              (int)sh.cover.size(), weight(sh.cover), trivial + (sh.complemented ? 1 : 0), pairs, phi, s.total() + (sh.complemented ? 1 : 0), sh.complemented ? " (incl. NOT)" : "", sh.note.c_str());
  };
  struct Run { int shape; Sol sol; long total; };
  std::vector<Run> runs;
  for (size_t si = 0; si < shapes.size(); si++) {
    Shape& sh = shapes[si];
    Sol s;
    Rng r(o.seed * 1000003 + si);
    init_state(s, sh, r, true);
    std::string why;
    if (!s.valid(&why)) { std::cerr << "internal error after greedy: " << why << "\n"; return 3; }
    report(s, sh, "greedy");
    runs.push_back({(int)si, s, s.total() + (sh.complemented ? 1 : 0)});
  }
  std::sort(runs.begin(), runs.end(), [](const Run& a, const Run& b) { return a.total < b.total; });

  int T = o.T;
  long iters = o.iters > 0 ? o.iters : std::max(200000L, 25000L * (long)shapes[runs[0].shape].cover.size());
  u64 movesTotal = 0;
  double tAnneal = now_s();
  auto anneal = [&](Sol& s, Rng& r, long n, double t0) {
    double ratio = std::log(o.P.t1 / t0);
    for (long i = 0; i < n; i++) s.step(r, t0 * std::exp(ratio * (double)i / (double)n), o.P);
    s.cleanup();
    s.greedy_pairs(r);          // any pair of pieces still shared by two covers becomes a node
    s.cleanup();
  };
  // ------------------------------------------------------------ phase 1b: a short anneal of every shape whose greedy
  // size is within 8% of the best one (greedy sizes are too noisy to rank shapes), then re-rank.
  size_t pool = 1;
  if (o.rounds != 0) {
    size_t cand = 1;
    while (cand < runs.size() && cand < 12 && runs[cand].total <= runs[0].total * 1.08) cand++;
    if (cand > 1) {
      std::atomic<size_t> nx{0};
      std::vector<std::thread> th;
      for (int t = 0; t < T; t++)
        th.emplace_back([&] {
          for (size_t k; (k = nx++) < cand;) {
            Rng r(o.seed * 7777 + 13 * k + 1);
            anneal(runs[k].sol, r, iters / 3, o.P.t0);
            runs[k].total = runs[k].sol.total() + (shapes[runs[k].shape].complemented ? 1 : 0);
          }
        });
      for (auto& x : th) x.join();
      movesTotal += (u64)(iters / 3) * cand;
      for (size_t k = 0; k < cand; k++) {
        fprintf(stderr, "[%7.1fs] shape %-8s after a short anneal: %ld\n", elapsed(), shapes[runs[k].shape].name.c_str(), runs[k].total);
        report(runs[k].sol, shapes[runs[k].shape], "short anneal");
      }
      std::sort(runs.begin(), runs.begin() + cand, [](const Run& a, const Run& b) { return a.total < b.total; });
      while (pool < cand && runs[pool].total <= runs[0].total * 1.03) pool++;    // shapes worth restarting from
    }
  }

  // ------------------------------------------------------------ phase 2: annealing rounds, one "lane" per thread.
  // A lane anneals its state round after round (round 0 of a lineage from t0, later rounds from the reheat
  // temperature) and falls back to its lineage best when a round ends worse. A lane that has not improved for
  // `restart` rounds starts a new lineage: a shape from the pool, on small graphs with a freshly weight-annealed
  // cover, and a new proxy pairing. Everything a lane does depends only on its own RNG, so a run is reproducible.
  struct Lane { Sol sol, best; Shape shape; long bestTot = 0; int stall = 0; bool fresh = true, restartNow = false; long lineages = 1; };
  std::vector<Lane> lanes(T);
  std::vector<Rng> rngs;
  for (int t = 0; t < T; t++) rngs.emplace_back(o.seed * 0x9E3779B97F4A7C15ull + 1000 * t + 17);
  bool smallGraph = (size_t)G.n * G.m <= 4096;
  auto new_lineage = [&](Lane& L, Rng& r) {
    const Run& base = runs[r.below((u32)pool)];
    L.shape = shapes[base.shape];
    if (smallGraph && !L.shape.complemented && r.below(3) != 0) {       // perturb the cover itself
      WCover w(G, L.shape.cover);
      w.lambda = o.wlambda;
      w.run(r, o.witers / 3, 0.9, 0.15);
      L.shape.cover = w.r; L.shape.pairing.clear(); L.shape.name = "wcover*";
    }
    init_state(L.sol, L.shape, r, false);
    L.fresh = true; L.stall = 0; L.restartNow = false; L.lineages++;
    L.best = L.sol; L.bestTot = L.sol.total() + (L.shape.complemented ? 1 : 0);
  };
  if (o.rounds != 0) {
    std::vector<std::thread> th;
    for (int t = 0; t < T; t++)
      th.emplace_back([&, t] {
        Lane& L = lanes[t];
        if (t < (int)pool) { L.shape = shapes[runs[t].shape]; L.sol = runs[t].sol; L.fresh = t >= 1 || pool == 1; }
        else { new_lineage(L, rngs[t]); L.lineages = 1; }
        L.best = L.sol; L.bestTot = L.sol.total() + (L.shape.complemented ? 1 : 0);
      });
    for (auto& x : th) x.join();
  }
  std::vector<long> lnsTried(T, 0), lnsKept(T, 0);
  double lastRound = 0;
  int roundsDone = 0;
  for (int round = 0; o.rounds < 0 || round < o.rounds; round++) {
    if (o.timeLimit > 0 && elapsed() + 0.5 * lastRound >= o.timeLimit) break;
    double tr = now_s();
    std::vector<std::thread> th;
    for (int t = 0; t < T; t++)
      th.emplace_back([&, t] {
        Lane& L = lanes[t]; Rng& r = rngs[t];
        if (L.restartNow) new_lineage(L, r);
        if (round >= o.lnsAfter) {
          // experimental LNS round: term-level moves, each followed by focused re-sharing; keep a trial only if it does not lose
          Sol& s = L.sol;
          long trials = std::max(1L, iters / (4 * o.lnsSteps));
          Sol backup = s;
          long cur = s.total();
          for (long q = 0; q < trials; q++) {
            if (!s.lns_move(r, o.P, o.lnsSteps, o.lnsT)) continue;
            lnsTried[t]++;
            long nt = s.total();
            if (nt <= cur) { cur = nt; backup = s; lnsKept[t]++; }
            else s = backup;
          }
          s.cleanup(); s.greedy_pairs(r); s.cleanup();
        } else anneal(L.sol, r, iters, L.fresh ? o.P.t0 : o.reheat);
        L.fresh = false;
      });
    for (auto& x : th) x.join();
    lastRound = now_s() - tr;
    movesTotal += (u64)iters * T;
    roundsDone++;
    int bt = 0;
    std::vector<long> tot(T);
    for (int t = 0; t < T; t++) {
      tot[t] = lanes[t].sol.total() + (lanes[t].shape.complemented ? 1 : 0);
      if (tot[t] < tot[bt]) bt = t;
    }
    std::string why;
    if (!lanes[bt].sol.valid(&why)) { std::cerr << "internal error: invalid state after round: " << why << "\n"; return 3; }
    report(lanes[bt].sol, lanes[bt].shape, "anneal");
    if (o.verbose || T * (o.rounds < 0 ? 40 : o.rounds) <= 64 || round % 8 == 0) {
      fprintf(stderr, "[%7.1fs] round %d: lane totals", elapsed(), round);
      for (int t = 0; t < T; t++) fprintf(stderr, " %ld%s", tot[t], lanes[t].stall == 0 && lanes[t].lineages > 1 && tot[t] >= lanes[t].bestTot ? "*" : "");
      fprintf(stderr, "  best %ld | %.2fM moves/s (%d threads)\n", bestSize, movesTotal / (now_s() - tAnneal) / 1e6, T);
    }
    for (int t = 0; t < T; t++) {
      Lane& L = lanes[t];
      if (tot[t] < L.bestTot) { L.best = L.sol; L.bestTot = tot[t]; L.stall = 0; }
      else { L.stall++; if (tot[t] > L.bestTot) L.sol = L.best; }
      if (o.restart > 0 && L.stall >= o.restart) L.restartNow = true;
    }
  }
  long lineages = 0;
  for (auto& L : lanes) lineages += L.lineages;
  std::vector<Sol> sols;
  for (auto& L : lanes) sols.push_back(L.best);
  if (o.verbose) {
    long a = 0, b = 0; for (int t = 0; t < T; t++) { a += lnsTried[t]; b += lnsKept[t]; }
    fprintf(stderr, "  LNS trials %ld, kept %ld\n", a, b);
  }
  if (o.verbose) {
    static const char* nm[9] = {"add", "paar", "remove", "modify", "swap", "pair", "elem", "rect", "refit"};
    for (int k = 0; k < 9; k++) { u64 a = 0, b = 0; for (auto& s : sols) { a += s.tried[k]; b += s.acc[k]; } fprintf(stderr, "  move %-7s tried %llu accepted %llu\n", nm[k], (unsigned long long)a, (unsigned long long)b); }
  }
  if (o.verbose) {
    // structure of the best state: intermediate nodes by size / kind / number of users
    int bt = 0;
    for (int t = 1; t < T; t++) if (sols[t].total() < sols[bt].total()) bt = t;
    const Sol& s = sols[bt];
    std::map<std::string, int> h;
    int pairsT = 0;
    for (size_t a = 0; a < s.rect.size(); a++) if (s.ralive[a] && s.partner[a] > (int)a) pairsT++;
    for (int id : s.ens.aliveList) {
      const auto& x = s.ens.nd[id];
      int r = x.s.rows().count(), c = x.s.cols().count();
      char buf[96];
      snprintf(buf, sizeof buf, "%s size=%2d %s uses=%d cost=%d", x.tref ? "target" : "inter ", x.sz, r && c ? "mixed" : r ? "rows " : "cols ", x.tref ? 0 : std::min(x.uses, 9), (int)x.cov.size() - 1);
      h[buf]++;
    }
    fprintf(stderr, "  best state: %d terms (%d cross pairs), %d rects, ensemble cost %ld\n", s.nTerms, pairsT, s.nRects, s.ens.cost);
    for (auto& [k, v] : h) fprintf(stderr, "    %4d x %s\n", v, k.c_str());
  }
  printf("graphsynth %s basis=%s best=%ld gates shape=%s out=%s verified=yes time=%.1fs rounds=%d lineages=%ld moves=%llu (%.2fM/s)\n", specName.c_str(), o.basis.c_str(), bestSize,
         bestShape.c_str(), o.out.c_str(), elapsed(), roundsDone, lineages, (unsigned long long)movesTotal, movesTotal / std::max(1e-9, now_s() - tAnneal) / 1e6);
  return 0;
}
