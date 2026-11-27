#!/usr/bin/env python3
"""allopt.py -- enumerate the optimal AND-circuits of one graph up to symmetry (run with bin/satpy via bin/pnprun).

    bin/satpy src/andtab/allopt.py --rows 85,102,51,120,45,30,75 --m 7 --a 5 [--name NAME] [--timeout SEC] [--max N]
                                   --out runs/andtab/allopt_NAME.json

`--a` must be And of the graph (already proved).  A circuit is identified with the FAMILY of cell sets of its AND
gates: by Lemma 2 of docs/andtab.md nothing else matters, and by Lemma 3 the last gate can be taken to be the graph
itself, so the family is {g_0, .., g_{a-2}} together with the graph.  The enumeration uses encoding B of andsat.py
with the conditions M1-M6 (every optimal circuit is equivalent to one satisfying them: strip common generators,
saturate the last gate, swap sides, reorder independent gates, apply an automorphism) and blocks, after every
model, the ordered tuple of the cell sets of g_0..g_{a-2}.  Models are then grouped into classes under the full
automorphism group of the graph (transposing ones included) and the order of the gates.
"complete": true  means the solver answered UNSAT after the last blocking clause: the list of classes is then ALL
optimal gate families in that normal form, up to symmetry.  Otherwise the list is only what was found in the time.
"""
import argparse, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andlib, andsat


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', required=True); ap.add_argument('--m', type=int, default=0)
    ap.add_argument('--a', type=int, required=True)
    ap.add_argument('--name', default='graph')
    ap.add_argument('--timeout', type=float, default=1800, help='total seconds')
    ap.add_argument('--max', type=int, default=20000, help='stop after this many models')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    rows = [int(x, 0) for x in a.rows.split(',')]
    n = len(rows); m = a.m or n
    T = andlib.rows_to_mask(rows, m)
    P = n * m; N = n + m
    inputs = andlib.gens(n, m)
    autos = andsat.automorphisms(n, m, T, 100000)
    # cell permutations of the automorphisms (identity added)
    perms = [list(range(P))]
    for phi in autos:
        pp = [0] * P
        for u in range(n):
            for v in range(m):
                x, y = phi[u], phi[n + v]
                r, c = (x, y - n) if x < n else (y, x - n)
                pp[u * m + v] = r * m + c
        perms.append(pp)

    def act(pp, s):
        r = 0
        while s:
            p = (s & -s).bit_length() - 1; s &= s - 1
            r |= 1 << pp[p]
        return r
    cl, nv, info = andsat.encode2(P, inputs, T, a.a, True, autos, 1)
    from pysat.solvers import Solver
    S = Solver(name='cadical195', bootstrap_with=cl)
    V = info['V']
    classes = {}; order = []
    t0 = time.time(); nmodels = 0; complete = False; stopped = None
    while True:
        r = None
        while r is None:
            S.conf_budget(20000)
            r = S.solve_limited()
            if r is None and time.time() - t0 > a.timeout:
                break
        if r is None:
            stopped = 'time limit'; break
        if r is False:
            complete = True; break
        model = S.get_model()
        pos = set(v for v in model if v > 0)
        L, R, out = andsat.decode(model, info, a.a)
        val = list(inputs)
        for j in range(a.a):
            x = 0; y = 0
            for i in L[j]: x |= val[i]
            for i in R[j]: y |= val[i]
            val.append(x & y)
        assert val[-1] == T and andlib.eval_wit(n, m, L, R, out) == T
        gates = val[N:N + a.a - 1]
        for j in range(a.a - 1):
            assert all(((gates[j] >> p) & 1) == (V[j][p] in pos) for p in range(P))
        key = min(tuple(sorted(act(pp, g) for g in gates)) for pp in perms)
        nmodels += 1
        if key not in classes:
            reads = [[k for k in range(j) if (N + k) in L[j] or (N + k) in R[j]] for j in range(a.a)]
            classes[key] = dict(models=0, witness=dict(L=L, R=R, out=out),
                                gate_rows=[andlib.mask_to_rows(g, n, m) for g in gates] + [rows],
                                gate_sizes=[bin(g).count('1') for g in gates] + [bin(T).count('1')],
                                gates_inside_graph=[(g & ~T) == 0 for g in gates],
                                reads=reads, depth=None)
            d = [0] * a.a
            for j in range(a.a):
                d[j] = 1 + max([d[k] for k in reads[j]] or [0])
            classes[key]['depth'] = max(d)
            order.append(key)
            print('[%.0fs] class %d (model %d): gate sizes %s, depth %d, reads %s' % (time.time() - t0, len(order), nmodels,
                  classes[key]['gate_sizes'], classes[key]['depth'], reads), flush=True)
        classes[key]['models'] += 1
        S.add_clause([(-V[j][p] if V[j][p] in pos else V[j][p]) for j in range(a.a - 1) for p in range(P)])
        if nmodels >= a.max:
            stopped = 'model limit'; break
        if time.time() - t0 > a.timeout:
            stopped = 'time limit'; break
    S.delete()
    res = dict(name=a.name, n=n, m=m, rows=rows, a=a.a, complete=complete, stopped=stopped, models=nmodels,
               num_classes=len(order), automorphisms=len(perms), seconds=round(time.time() - t0, 1),
               meaning=('classes of optimal circuits (families of AND-gate cell sets; the last gate is the graph) under the automorphism '
                        'group of the graph and the order of the gates, in the normal form M1-M6 of docs/andtab.md. complete = the SAT '
                        'solver proved there is no further one. gate_rows[j][u] = row u of the cell set of AND gate j (bit v).'),
               classes=[classes[k] for k in order])
    json.dump(res, open(a.out, 'w'), separators=(',', ':'))
    print('%s: a = %d: %d models, %d classes, %s (%.0fs) -> %s' % (a.name, a.a, nmodels, len(order),
          'COMPLETE (UNSAT after the last blocking clause)' if complete else 'NOT complete (%s)' % stopped, time.time() - t0, a.out), flush=True)


if __name__ == '__main__':
    main()
