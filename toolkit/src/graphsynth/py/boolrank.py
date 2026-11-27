"""boolrank.py — Boolean rank (minimum number of bicliques covering the edges) of a graph spec by SAT.

    bin/satpy src/graphsynth/py/boolrank.py SPEC K [--time S]

Decides "is there an exact cover with at most K closed bicliques" (closed = maximal bicliques; for the NUMBER of
rectangles they lose nothing). SAT -> prints a cover; UNSAT -> Boolean rank > K (exhaustive for this question).
Single-threaded. Only sensible while the graph has a few thousand closed bicliques (cand32: 1893).
"""
import sys, threading, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

def load(path):
    rows = []; n = m = 0
    for line in open(path):
        p = line.split('#')[0].split()
        if not p: continue
        if p[0] == 'n': n = int(p[1])
        elif p[0] == 'm': m = int(p[1])
        elif p[0] == 'rows': rows += [int(x, 16) for x in p[1:]]
    return n, m, rows

def closed_bicliques(R, n, m):
    cols = [sum(((R[u] >> v) & 1) << u for u in range(n)) for v in range(m)]
    seen = set(r for r in R if r); work = list(seen)
    while work:
        V = work.pop()
        for u in range(n):
            W = V & R[u]
            if W and W not in seen:
                seen.add(W); work.append(W)
    out = []
    for V in seen:
        U = (1 << n) - 1
        for v in range(m):
            if (V >> v) & 1: U &= cols[v]
        out.append((U, V))
    return out

def main():
    spec, K = sys.argv[1], int(sys.argv[2])
    tmax = float(sys.argv[sys.argv.index('--time') + 1]) if '--time' in sys.argv else 50.0
    n, m, R = load(spec)
    bc = closed_bicliques(R, n, m)
    cover = {}
    for i, (U, V) in enumerate(bc):
        for u in range(n):
            if (U >> u) & 1:
                for v in range(m):
                    if (V >> v) & 1: cover.setdefault((u, v), []).append(i + 1)
    cnf = CardEnc.atmost(lits=list(range(1, len(bc) + 1)), bound=K, top_id=len(bc), encoding=EncType.totalizer)
    s = Solver(name='g4', bootstrap_with=cnf.clauses)        # Glucose 4: supports interrupt()
    for u in range(n):
        for v in range(m):
            if (R[u] >> v) & 1: s.add_clause(cover[(u, v)])
    t0 = time.time()
    timer = threading.Timer(tmax, s.interrupt)
    timer.start()
    res = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    dt = time.time() - t0
    if res is True:
        mod = set(x for x in s.get_model() if 0 < x <= len(bc))
        ch = [bc[i - 1] for i in mod]
        pc = lambda x: bin(x).count('1')
        print(f"SAT: cover with {len(ch)} closed bicliques (K={K}), closed weight {sum(pc(U)+pc(V) for U,V in ch)}, {dt:.1f}s; closed bicliques total {len(bc)}")
    elif res is False:
        print(f"UNSAT: no cover with <= {K} bicliques, so Boolean rank >= {K+1} ({dt:.1f}s; {len(bc)} closed bicliques)")
    else:
        print(f"UNKNOWN after {dt:.1f}s (K={K})")

if __name__ == '__main__':
    main()
