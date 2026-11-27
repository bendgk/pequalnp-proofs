#!/usr/bin/env python3
"""sps_sat.py N S [--k K1,K2,..] [--minimal] [--solver cadical195|...] [--out FILE.ckt] [--conf BUDGET]

EXACT search, by SAT, inside ONE family of circuits for K(N) = specs/kn<N>.spec (N wires, false on 1-hot points,
true on 2-hot points, basis ao). Run it with bin/satpy (single thread per call).

Family "sum-product-sum" (what `cktsls --shape SPS` searches stochastically):
    c  OR gates  S_1..S_c : each the OR of two earlier wires among the inputs and S-gates   (so every S wire is the
                             OR of a SET of inputs)
    k  AND gates P_1..P_k : each the AND of two wires among the inputs and S-gates           (a biclique X_i x Y_i)
    k-1 OR gates           : OR of all the products
    total gates S = c + 2k - 1.
Such a circuit is correct iff every product has disjoint sides and every pair {u,v} lies in some X_i x Y_i.
For each k with c = S - 2k + 1 >= 0 the script answers SAT (prints/saves a circuit, to be checked with bin/cktcheck)
or UNSAT. UNSAT for all k means: NO circuit OF THIS FAMILY with at most S gates. It says NOTHING about circuits
outside the family (products of products, ORs mixing sets and products, ...).

Symmetry breaking (sound for the family; all three hold for the solution whose gate list is lexicographically
least among its relabelings/reorderings): S gates in co-lexicographic order unless a gate reads its predecessor;
products in lexicographic order; the first gate reading input u+1 is not before the first gate reading input u.
Duplicate/unused gates are allowed, so "c sets, k products" covers every smaller c and k as well.
--minimal adds "every gate is needed" constraints (no S gate equals a fanin, S sets pairwise different, every S gate
read later, products pairwise different). That is only sound when S is already known to be a lower bound for K(N)
(e.g. K(8) >= 18 from K(7) = 16 and K(n+1) >= K(n) + 2); the output says so.
"""
import sys, time, itertools
from pysat.solvers import Solver


def build(n, c, k, minimal=False):
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    cl = []
    W = n + c                      # wires that are sets: n singletons + c S-gates
    m = [[None] * n for _ in range(W)]   # membership m[w][u]; singletons are constants
    TRUE = new(); cl.append([TRUE])
    for w in range(n):
        for u in range(n): m[w][u] = TRUE if w == u else -TRUE
    for w in range(n, W):
        for u in range(n): m[w][u] = new()
    def exactly_one(vs):
        cl.append(list(vs))
        for a, b in itertools.combinations(vs, 2): cl.append([-a, -b])
    fa, fb, xy = {}, {}, {}
    def gate_inputs(tag, lim):
        """two one-hot selectors a < b < lim and the membership copies x (of a), y (of b)"""
        A = [new() for _ in range(lim)]; B = [new() for _ in range(lim)]
        exactly_one(A); exactly_one(B)
        for a in range(lim):
            for b in range(a + 1):
                cl.append([-A[a], -B[b]])           # a < b
        x = [new() for _ in range(n)]; y = [new() for _ in range(n)]
        for a in range(lim):
            for u in range(n):
                cl.append([-A[a], -x[u], m[a][u]]); cl.append([-A[a], x[u], -m[a][u]])
                cl.append([-B[a], -y[u], m[a][u]]); cl.append([-B[a], y[u], -m[a][u]])
        fa[tag] = A; fb[tag] = B; xy[tag] = (x, y)
        return x, y
    # S gates
    for j in range(c):
        w = n + j
        x, y = gate_inputs(('S', j), w)
        for u in range(n):
            cl.append([-x[u], m[w][u]]); cl.append([-y[u], m[w][u]]); cl.append([-m[w][u], x[u], y[u]])
    for j in range(c - 1):          # colex order unless gate j+1 reads gate j (then its b is wire n+j)
        A0, B0, A1, B1 = fa[('S', j)], fb[('S', j)], fa[('S', j + 1)], fb[('S', j + 1)]
        for b in range(len(B0)):
            for b2 in range(b):
                cl.append([-B0[b], -B1[b2]])
            for a in range(len(A0)):
                for a2 in range(a):
                    cl.append([-B0[b], -B1[b], -A0[a], -A1[a2]])
    # products
    pairs = list(itertools.combinations(range(n), 2))
    cov = []
    for i in range(k):
        x, y = gate_inputs(('P', i), W)
        for u in range(n): cl.append([-x[u], -y[u]])            # disjoint sides: false on every 1-hot point
        row = []
        for (u, v) in pairs:
            q = new(); row.append(q)
            cl.append([-q, x[u], x[v]]); cl.append([-q, y[u], y[v]])
        cov.append(row)
    for i in range(k - 1):          # lexicographic order of the products by (b, a)
        A0, B0, A1, B1 = fa[('P', i)], fb[('P', i)], fa[('P', i + 1)], fb[('P', i + 1)]
        for b in range(W):
            for b2 in range(b):
                cl.append([-B0[b], -B1[b2]])
            for a in range(W):
                for a2 in range(a):
                    cl.append([-B0[b], -B1[b], -A0[a], -A1[a2]])
    for pi in range(len(pairs)): cl.append([cov[i][pi] for i in range(k)])
    if minimal:
        # Valid only when S is already known to be a lower bound for ALL circuits: then a circuit with exactly S
        # gates has no gate to spare, so (i) no S gate equals one of its fanins, (ii) the S sets are pairwise
        # different, (iii) every S gate is read by a later gate, (iv) the products are pairwise different.
        def some(lits_fn):
            aux = []
            for u in range(n):
                q = new(); aux.append(q)
                for l in lits_fn(u): cl.append([-q, l])
            cl.append(aux)
        for j in range(c):
            x, y = xy[('S', j)]
            some(lambda u: (x[u], -y[u])); some(lambda u: (y[u], -x[u]))
            w = n + j
            readers = [fa[('S', j2)][w] for j2 in range(j + 1, c) if w < len(fa[('S', j2)])]
            readers += [fb[('S', j2)][w] for j2 in range(j + 1, c) if w < len(fb[('S', j2)])]
            readers += [fa[('P', i)][w] for i in range(k)] + [fb[('P', i)][w] for i in range(k)]
            cl.append(readers)
            for j2 in range(j + 1, c):
                w2 = n + j2
                aux = []
                for u in range(n):
                    q1 = new(); q2 = new(); aux += [q1, q2]
                    cl.append([-q1, m[w][u]]); cl.append([-q1, -m[w2][u]])
                    cl.append([-q2, -m[w][u]]); cl.append([-q2, m[w2][u]])
                cl.append(aux)
        for i in range(k - 1):
            A0, B0, A1, B1 = fa[('P', i)], fb[('P', i)], fa[('P', i + 1)], fb[('P', i + 1)]
            for b in range(W):
                for a in range(W):
                    cl.append([-B0[b], -B1[b], -A0[a], -A1[a]])
    # input symmetry: the first gate (S gates in order, then products) that reads input u+1 is not before the
    # first gate that reads input u
    tags = [('S', j) for j in range(c)] + [('P', i) for i in range(k)]
    prev = [None] * n
    for tg in tags:
        A, B = fa[tg], fb[tg]
        cur = []
        for u in range(n):
            lits = [x for x in ((A[u] if u < len(A) else None), (B[u] if u < len(B) else None)) if x is not None]
            q = new()                                   # q -> input u is read by this gate or an earlier one
            cl.append([-q] + lits + ([prev[u]] if prev[u] is not None else []))
            cur.append(q)
        for u in range(n - 1):
            for x in ((A[u + 1] if u + 1 < len(A) else None), (B[u + 1] if u + 1 < len(B) else None)):
                if x is not None: cl.append([-x, cur[u]])
        prev = cur
    return nv[0], cl, fa, fb


def decode(model, n, c, k, fa, fb):
    val = set(v for v in model if v > 0)
    pick = lambda vs: next(i for i, v in enumerate(vs) if v in val)
    lines = [f'inputs {n}']
    for j in range(c): lines.append(f'or {pick(fa[("S", j)])} {pick(fb[("S", j)])}')
    for i in range(k): lines.append(f'and {pick(fa[("P", i)])} {pick(fb[("P", i)])}')
    first = n + c
    acc = first
    for i in range(1, k):
        lines.append(f'or {acc} {first + i}')
        acc = n + c + k + i - 1
    lines.append(f'out {acc}')
    return '\n'.join(lines) + '\n'


def main():
    a = sys.argv[1:]
    if len(a) < 2: sys.exit(__doc__)
    n, s = int(a[0]), int(a[1])
    ks, solver, out, conf, minimal = None, 'cadical195', None, None, False
    i = 2
    while i < len(a):
        if a[i] == '--k': ks = [int(x) for x in a[i + 1].split(',')]; i += 2
        elif a[i] == '--solver': solver = a[i + 1]; i += 2
        elif a[i] == '--out': out = a[i + 1]; i += 2
        elif a[i] == '--conf': conf = int(a[i + 1]); i += 2
        elif a[i] == '--minimal': minimal = True; i += 1
        else: sys.exit(__doc__)
    if ks is None: ks = [k for k in range(1, s + 1) if s - 2 * k + 1 >= 0]
    allunsat = True
    for k in ks:
        c = s - 2 * k + 1
        if c < 0: continue
        nv, cl, fa, fb = build(n, c, k, minimal)
        t0 = time.time()
        with Solver(name=solver, bootstrap_with=cl) as S:
            if conf:
                S.conf_budget(conf); r = S.solve_limited(expect_interrupt=False)
            else:
                r = S.solve()
            dt = time.time() - t0
            if r:
                txt = decode(S.get_model(), n, c, k, fa, fb)
                print(f'kn{n} S={s} k={k} c={c}: SAT  ({nv} vars, {len(cl)} clauses, {dt:.1f}s)', flush=True)
                sys.stdout.write(txt)
                if out:
                    open(out, 'w').write(f'# sps_sat.py kn{n}: sum-product-sum circuit, {c} set-ORs, {k} products, {k - 1} top ORs = {s} gates\n' + txt)
                    print(f'saved {out} (check it with bin/cktcheck)')
                return 0
            elif r is None:
                allunsat = False
                print(f'kn{n} S={s} k={k} c={c}: UNKNOWN (budget of {conf} conflicts used up, {dt:.1f}s)', flush=True)
            else:
                print(f'kn{n} S={s} k={k} c={c}: UNSAT ({nv} vars, {len(cl)} clauses, {dt:.1f}s)', flush=True)
    if allunsat and len(ks) == len([k for k in range(1, s + 1) if s - 2 * k + 1 >= 0]):
        if minimal:
            print(f'kn{n}: NO sum-product-sum circuit with exactly {s} gates in which every gate is needed (every k UNSAT, --minimal).')
            print(f'      If K({n}) >= {s} is known, this means: no sum-product-sum circuit with at most {s} gates. Family statement only.')
        else:
            print(f'kn{n}: NO sum-product-sum circuit with at most {s} gates (every k UNSAT). Family statement only.')
    return 20 if allunsat else 3


if __name__ == '__main__':
    sys.exit(main())
