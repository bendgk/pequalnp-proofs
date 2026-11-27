"""kn_elim.py — exact search for K(n) = monotone circuit size of threshold-2 on n wires (specs/knN.spec),
with ELIMINATION constraints that are valid whenever s <= K(n-1) + E.   (2026-11-27)

Model searched ("normal" circuits): s gates, each AND or OR of two distinct earlier wires, last gate is the output,
every other gate is read by a later gate, every gate column is non-constant and differs from every input column
(and with --distinct from every other gate column).  A MINIMAL circuit is always normal (a duplicate/constant
column or an unread gate could be removed), so if K(n) >= s is already known, "no normal s-gate circuit" means
"no circuit with <= s gates" in the full Lean model (Monotone2, constants, copies, missing wires).

Symmetry breaking (both hold simultaneously for the lex-min representative over input relabelings x gate orders,
key sequence ((b_0,a_0),(b_1,a_1),...), compared lexicographically, each key colex):
  G: if gate i+1 does not read gate i then (b_i, a_i) <= (b_{i+1}, a_{i+1}) colex.
  F: inputs are first used in increasing order: gate i reads input j+1 only if some gate <= i reads input j.

Elimination constraints (--elim E): put x_j = 0 and simplify structurally (OR(0,w) -> w, AND(0,w) -> 0,
op(w,w) -> w).  The result computes threshold-2 on n-1 wires, so it has >= K(n-1) gates: at most
E = s - K(n-1) gates disappear.  Every gate reading x_j disappears, and every gate reading a gate that became 0
disappears.  For E = 2 this forces, for every input j:
  F1  at most 2 gates read x_j;
  F2  if 2 gates read x_j, both are OR gates;
  F3  an AND gate reading x_j has exactly one reader, and that reader is an OR gate;
  F4  if 2 gates read x_j and one is g = OR(x_j, h), no gate reads both g and h (it would become op(h,h));
  F5  if g = AND(x_j, h) and its reader is r = OR(g, k), no gate reads both r and k.
For general E only "at most E gates read x_j" is added (F1).

usage: satpy kn_elim.py N S [--elim E] [--solver cadical195] [--distinct] [--and-count K] [--cube i/n] [--out FILE.ckt]
"""
import itertools, sys, time


def build(n, s, elim=None, distinct=False, and_count=None, tiebreak=True, typec=True, extra=False):
    nv = [0]
    cl = []

    def var():
        nv[0] += 1
        return nv[0]
    add = cl.append
    pts, tgt = [], []
    for i in range(n):
        pts.append([int(k == i) for k in range(n)]); tgt.append(0)
    for i, j in itertools.combinations(range(n), 2):
        pts.append([int(k in (i, j)) for k in range(n)]); tgt.append(1)
    P = len(pts)
    a, b, t, va, vb, v = [], [], [], [], [], []
    for i in range(s):
        W = n + i
        a.append([var() for _ in range(W)]); b.append([var() for _ in range(W)]); t.append(var())
        va.append([var() for _ in range(P)]); vb.append([var() for _ in range(P)]); v.append([var() for _ in range(P)])

    def exactly_one(xs):
        add(list(xs))
        for x, y in itertools.combinations(xs, 2): add([-x, -y])
    for i in range(s):
        W = n + i
        exactly_one(a[i]); exactly_one(b[i])
        add([-a[i][W - 1]]); add([-b[i][0]])
        for j in range(W):
            for k in range(j + 1):          # need a < b strictly: forbid b = k <= j = a
                add([-a[i][j], -b[i][k]])
        for j in range(W):
            for p in range(P):
                if j < n:
                    x = pts[p][j]
                    add([-a[i][j], va[i][p] if x else -va[i][p]])
                    add([-b[i][j], vb[i][p] if x else -vb[i][p]])
                else:
                    x = v[j - n][p]
                    add([-a[i][j], -va[i][p], x]); add([-a[i][j], va[i][p], -x])
                    add([-b[i][j], -vb[i][p], x]); add([-b[i][j], vb[i][p], -x])
        for p in range(P):
            A, B, V, T = va[i][p], vb[i][p], v[i][p], t[i]
            add([-T, -V, A]); add([-T, -V, B]); add([-T, V, -A, -B])     # AND
            add([T, V, -A]); add([T, V, -B]); add([T, -V, A, B])         # OR
            add([-A, -B, V]); add([A, B, -V])                            # holds for both types
        add([v[i][p] for p in range(P)]); add([-v[i][p] for p in range(P)])           # non-constant
        for j in range(n):                                                               # differs from input j
            add([(-v[i][p] if pts[p][j] else v[i][p]) for p in range(P)])
    for p in range(P):
        add([v[s - 1][p] if tgt[p] else -v[s - 1][p]])
    for i in range(s - 1):                                                               # every gate is read
        add([a[i2][n + i] for i2 in range(i + 1, s)] + [b[i2][n + i] for i2 in range(i + 1, s)])
    if distinct:
        for i in range(s):
            for i2 in range(i + 1, s):
                ds = []
                for p in range(P):
                    d = var(); ds.append(d)
                    add([-d, v[i][p], v[i2][p]]); add([-d, -v[i][p], -v[i2][p]])
                add(ds)
    # ---- G: gate order
    for i in range(s - 1):
        W = n + i
        uses = b[i + 1][W]
        for k in range(W):
            for k2 in range(k):
                add([uses, -b[i][k], -b[i + 1][k2]])
            for j in range(k):
                for j2 in range(j):
                    add([uses, -b[i][k], -b[i + 1][k], -a[i][j], -a[i + 1][j2]])
                if tiebreak:   # same operands: OR before AND (type as last key component)
                    add([uses, -b[i][k], -b[i + 1][k], -a[i][j], -a[i + 1][j], -t[i], t[i + 1]])
                    add([uses, -b[i][k], -b[i + 1][k], -a[i][j], -a[i + 1][j], -t[i], -t[i + 1]])
    # ---- reads[i][j] for input wires j, and readers of gate wires
    r = [[var() for _ in range(n)] for _ in range(s)]
    for i in range(s):
        for j in range(n):
            add([-a[i][j], r[i][j]]); add([-b[i][j], r[i][j]]); add([-r[i][j], a[i][j], b[i][j]])
    # ---- F: inputs first used in increasing order
    for i in range(s):
        for j in range(n - 1):
            add([-r[i][j + 1]] + [r[i2][j] for i2 in range(i + 1)])
    for j in range(n):                       # every input is read (threshold-2 depends on every input)
        add([r[i][j] for i in range(s)])
    # ---- elimination constraints
    if elim is not None:
        E = elim
        for j in range(n):                   # F1: at most E readers
            for comb in itertools.combinations(range(s), E + 1):
                add([-r[i][j] for i in comb])
        if E == 2:
            rg = {}                          # rg[i,i2]: gate i2 reads gate i

            def reads_gate(i, i2):
                if (i, i2) not in rg:
                    x = var(); rg[(i, i2)] = x
                    add([-a[i2][n + i], x]); add([-b[i2][n + i], x]); add([-x, a[i2][n + i], b[i2][n + i]])
                return rg[(i, i2)]
            tw = [var() for _ in range(n)]   # tw[j]: input j has two readers
            for j in range(n):
                for i1, i2 in itertools.combinations(range(s), 2):
                    add([-r[i1][j], -r[i2][j], tw[j]])
                    add([-r[i1][j], -r[i2][j], -t[i1]]); add([-r[i1][j], -r[i2][j], -t[i2]])      # F2
                for i in range(s):
                    add([-tw[j], -r[i][j], -t[i]])                                                 # F2 again via tw
                    # F3: AND gate i reading input j: exactly one reader, an OR gate.  (i = s-1 impossible: output)
                    if i == s - 1:
                        add([-r[i][j], -t[i]])
                        continue
                    for i2 in range(i + 1, s):
                        add([-r[i][j], -t[i], -reads_gate(i, i2), -t[i2]])
                        for i3 in range(i2 + 1, s):
                            add([-r[i][j], -t[i], -reads_gate(i, i2), -reads_gate(i, i3)])
                    # F4: two readers, gate i = OR(x_j, h): nobody reads both gate i and h
                    W = n + i
                    for h in range(W):
                        if h == j: continue
                        lo, hi = min(h, j), max(h, j)
                        for i3 in range(i + 1, s):
                            add([-tw[j], -a[i][lo], -b[i][hi], -a[i3][h], -b[i3][W]])
                    # F5: gate i = AND(x_j, h), its reader i2 = OR(gate i, k): nobody reads both gate i2 and k
                    for i2 in range(i + 1, s):
                        W2 = n + i2
                        for k in range(W2):
                            if k == W: continue
                            lo, hi = min(k, W), max(k, W)
                            for i3 in range(i2 + 1, s):
                                add([-r[i][j], -t[i], -a[i2][lo], -b[i2][hi], -a[i3][k], -b[i3][W2]])
    if elim == 2 and typec:
        # F6 (uses the target): if the AND gate i reads input j then (F2) it is the only reader of x_j, so its other
        # operand h does not depend on x_j.  The points {j,y} and {y} differ only in x_j, the output differs on them,
        # and gate i is 0 at {y}; so gate i must be 1 at {j,y}, i.e. h({y}) = h({j,y}) = 1 for every y != j.
        single = {y: y for y in range(n)}            # point index of the 1-hot input y is y (see kn_points order)
        for i in range(s):
            for j in range(n):
                for y in range(n):
                    if y == j: continue
                    add([-a[i][j], -t[i], vb[i][single[y]]])
                    add([-b[i][j], -t[i], va[i][single[y]]])
    if elim == 2 and typec and extra:
        # tw[j] exact: tw[j] -> at least two readers
        for j in range(n):
            add([-tw[j]] + [r[i][j] for i in range(s)])
            for i in range(s):
                add([-tw[j], -r[i][j]] + [r[i2][j] for i2 in range(s) if i2 != i])
        # F7 (uses the target): x_j has ONE reader, g = OR(x_j, h).  h does not depend on x_j.  At {j,y}: g = 1 and the
        # output is 1; at {y}: if h({y}) = 1 then g = 1 too and nothing else changed, so the output would be 1: wrong.
        # Hence h is 0 on every 1-hot point y != j.
        # F8: x_j has TWO readers g1 = OR(x_j, h1), g2 = OR(x_j, h2).  {j,y} and {y} differ only through g1, g2, and both
        # are 1 at {j,y}; so at {y} they are not both 1: not (h1({y}) and h2({y})), with h's actual values at {y}.
        for j in range(n):
            for y in range(n):
                if y == j: continue
                for i in range(s):
                    add([tw[j], -a[i][j], t[i], -vb[i][y]])
                    add([tw[j], -b[i][j], t[i], -va[i][y]])
                    for i2 in range(i + 1, s):
                        for (s1_, o1) in ((a[i][j], vb[i][y]), (b[i][j], va[i][y])):
                            for (s2_, o2) in ((a[i2][j], vb[i2][y]), (b[i2][j], va[i2][y])):
                                add([-s1_, -s2_, -o1, -o2])
    if and_count is not None:
        from pysat.card import CardEnc, EncType
        ce = CardEnc.equals(lits=t, bound=and_count, top_id=nv[0], encoding=EncType.seqcounter)
        nv[0] = max(nv[0], ce.nv)
        cl.extend(ce.clauses)
    return dict(nv=nv[0], cl=cl, a=a, b=b, t=t, v=v, pts=pts, tgt=tgt)


def decode(E, model, n, s):
    m = set(x for x in model if x > 0)
    gates = []
    for i in range(s):
        j = next(j for j, x in enumerate(E['a'][i]) if x in m)
        k = next(k for k, x in enumerate(E['b'][i]) if x in m)
        gates.append(('and' if E['t'][i] in m else 'or', j, k))
    return gates


def check(gates, n):
    for pt, tg in zip(*kn_points(n)):
        w = list(pt)
        for op, j, k in gates:
            w.append((w[j] & w[k]) if op == 'and' else (w[j] | w[k]))
        if w[-1] != tg: return False
    return True


def kn_points(n):
    pts, tgt = [], []
    for i in range(n):
        pts.append([int(k == i) for k in range(n)]); tgt.append(0)
    for i, j in itertools.combinations(range(n), 2):
        pts.append([int(k in (i, j)) for k in range(n)]); tgt.append(1)
    return pts, tgt


if __name__ == '__main__':
    from pysat.solvers import Solver
    A = sys.argv[1:]
    n, s = int(A[0]), int(A[1])
    opt = dict(elim=None, solver='cadical195', distinct=False, and_count=None, out=None)
    i = 2
    while i < len(A):
        if A[i] == '--elim': opt['elim'] = int(A[i + 1]); i += 2
        elif A[i] == '--solver': opt['solver'] = A[i + 1]; i += 2
        elif A[i] == '--distinct': opt['distinct'] = True; i += 1
        elif A[i] == '--and-count': opt['and_count'] = int(A[i + 1]); i += 2
        elif A[i] == '--out': opt['out'] = A[i + 1]; i += 2
        elif A[i] == '--cube': opt['cube'] = __import__('json').loads(A[i + 1]); i += 2
        else: sys.exit(__doc__)
    t0 = time.time()
    E = build(n, s, elim=opt['elim'], distinct=opt['distinct'], and_count=opt['and_count'])
    for gi, (ca, cb, ct) in enumerate(opt.get('cube') or []):      # cube given as [[a,b,t],...] for gates 0..: unit clauses
        E['cl'] += [[E['a'][gi][ca]], [E['b'][gi][cb]], [E['t'][gi] if ct else -E['t'][gi]]]
    t1 = time.time()
    S = Solver(name=opt['solver'], bootstrap_with=E['cl'])
    ok = S.solve()
    dt = time.time() - t1
    tag = f"kn{n} s={s} elim={opt['elim']} distinct={opt['distinct']} and={opt['and_count']} solver={opt['solver']}"
    print(f"{tag}: vars={E['nv']} clauses={len(E['cl'])} encode={t1 - t0:.1f}s -> {'SAT' if ok else 'UNSAT'} in {dt:.1f}s", flush=True)
    if ok:
        g = decode(E, S.get_model(), n, s)
        assert check(g, n), "decoded circuit is wrong"
        txt = f"inputs {n}\n" + ''.join(f"{op} {j} {k}\n" for op, j, k in g) + f"out {n + s - 1}\n"
        print(txt, end='')
        if opt['out']: open(opt['out'], 'w').write(txt)
    S.delete()
