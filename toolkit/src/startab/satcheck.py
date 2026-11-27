#!/usr/bin/env python3
"""satcheck.py -- independent SAT cross-check of startab tables (run with bin/satpy).

    bin/satpy src/startab/satcheck.py tables/star_4.json [--basis mono|not|both] [--timeout SEC] [--min-size K]
                                      [--max-size K] [--only i,j,...] [--every K] [--solver cadical195|glucose42]

For every selected class of the table and every basis it builds, from scratch (nothing shared with startab.cpp),
the CNF "there is a circuit of EXACTLY t gates, each AND/OR of two distinct earlier wires (or, basis not, a NOT
of one earlier wire), every gate but the last read by a later gate, the last gate equal to the graph on all n*m
points" (plus, unless --no-order, a sound gate-order symmetry break), and checks
    t = 1 .. size-1 : UNSAT      (so no normal-form circuit of fewer gates exists)
    t = size        : SAT, and the decoded circuit is re-evaluated in Python.
A minimal circuit always has every gate used, so UNSAT for every t < size proves size is a lower bound in the
normal-form model; docs/startab.md proves the normal form loses nothing against the Lean model.
Classes of size 0, and the complete graph (size 1 by the constant gate), are trivial and skipped.
Prints one line per (class, basis): OK / MISMATCH / TIMEOUT, and a summary.  Exit 1 on any MISMATCH.
"""
import argparse, json, sys, threading, time


def inputs_for(n, m, enc):
    P = n * m
    cols = []
    for u in range(n):
        cols.append(sum(1 << (u * m + v) for v in range(m)))
    for v in range(m):
        cols.append(sum(1 << (u * m + v) for u in range(n)))
    if enc:
        kr = n.bit_length() - 1; kc = m.bit_length() - 1
        assert 1 << kr == n and 1 << kc == m
        for i in range(kr):
            for a in (0, 1):
                cols.append(sum(cols[u] for u in range(n) if ((u >> i) & 1) == a))
        for i in range(kc):
            for a in (0, 1):
                cols.append(sum(cols[n + v] for v in range(m) if ((v >> i) & 1) == a))
    return cols, P


def encode(cols, P, target, s, allow_not, order=True):
    N = len(cols)
    cl = []
    cnt = [0]

    def var():
        cnt[0] += 1
        return cnt[0]

    S1, S2, AND, NOT, A, B, V = [], [], [], [], [], [], []
    for i in range(s):
        W = N + i
        s1 = [var() for _ in range(W)]; s2 = [var() for _ in range(W)]
        t = var(); ng = var() if allow_not else None
        a = [var() for _ in range(P)]; b = [var() for _ in range(P)]; v = [var() for _ in range(P)]
        S1.append(s1); S2.append(s2); AND.append(t); NOT.append(ng); A.append(a); B.append(b); V.append(v)
        for sel in (s1, s2):                       # exactly one operand each
            cl.append(list(sel))
            for x in range(W):
                for y in range(x + 1, W):
                    cl.append([-sel[x], -sel[y]])
        for j in range(W):                         # a binary gate reads two different wires, first < second
            for k in range(j + 1):
                cl.append(([ng] if allow_not else []) + [-s1[j], -s2[k]])
        if allow_not:
            cl.append([-ng, s2[0]])                # a NOT gate ignores its second operand: pin it
            cl.append([-ng, -t])
        for j in range(W):
            for p in range(P):
                if j < N:
                    bit = (cols[j] >> p) & 1
                    cl.append([-s1[j], a[p] if bit else -a[p]])
                    cl.append([-s2[j], b[p] if bit else -b[p]])
                else:
                    x = V[j - N][p]
                    cl.append([-s1[j], -a[p], x]); cl.append([-s1[j], a[p], -x])
                    cl.append([-s2[j], -b[p], x]); cl.append([-s2[j], b[p], -x])
        for p in range(P):
            pre = []
            if allow_not:
                cl.append([-ng, -v[p], -a[p]]); cl.append([-ng, v[p], a[p]])
                pre = [ng]
            cl.append(pre + [-t, -v[p], a[p]]); cl.append(pre + [-t, -v[p], b[p]]); cl.append(pre + [-t, v[p], -a[p], -b[p]])
            cl.append(pre + [t, v[p], -a[p]]); cl.append(pre + [t, v[p], -b[p]]); cl.append(pre + [t, -v[p], a[p], b[p]])
    for p in range(P):                             # the last gate is the target
        cl.append([V[s - 1][p] if (target >> p) & 1 else -V[s - 1][p]])
    for i in range(s - 1):                         # every other gate is read by a later one
        c = []
        for i2 in range(i + 1, s):
            c.append(S1[i2][N + i]); c.append(S2[i2][N + i])
        cl.append(c)
    if order:
        # Sound symmetry break: order the gates greedily, always placing the available gate with the colex-least
        # operand pair (second, first).  Then a gate that does not read its predecessor was already available
        # one step earlier, so its pair is not smaller than the predecessor's.
        for i in range(s - 1):
            W = N + i
            uses = [S1[i + 1][W], S2[i + 1][W]]
            for k in range(W):
                for k2 in range(k):
                    cl.append(uses + [-S2[i][k], -S2[i + 1][k2]])
                for j in range(W):
                    for j2 in range(j):
                        cl.append(uses + [-S2[i][k], -S2[i + 1][k], -S1[i][j], -S1[i + 1][j2]])
    return cl, dict(S1=S1, S2=S2, AND=AND, NOT=NOT), cnt[0]


def decode(model, Vr, N, s, allow_not):
    pos = set(x for x in model if x > 0)
    gates = []
    for i in range(s):
        j = next(j for j, x in enumerate(Vr['S1'][i]) if x in pos)
        k = next(k for k, x in enumerate(Vr['S2'][i]) if x in pos)
        if allow_not and Vr['NOT'][i] in pos:
            gates.append(('not', j, j))
        else:
            gates.append(('and' if Vr['AND'][i] in pos else 'or', j, k))
    return gates


def evaluate(cols, P, gates):
    full = (1 << P) - 1
    w = list(cols)
    for op, j, k in gates:
        w.append(w[j] & w[k] if op == 'and' else w[j] | w[k] if op == 'or' else full & ~w[j])
    return w[-1]


def solve(clauses, solver, timeout):
    """returns (True/False/None, model)"""
    from pysat.solvers import Solver
    S = Solver(name=solver, bootstrap_with=clauses)
    try:
        if timeout and solver.startswith('g'):
            timer = threading.Timer(timeout, lambda: S.interrupt())
            timer.start()
            r = S.solve_limited(expect_interrupt=True)
            timer.cancel()
        else:
            r = S.solve()
        return r, (S.get_model() if r else None)
    finally:
        S.delete()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('table')
    ap.add_argument('--basis', default='both')
    ap.add_argument('--timeout', type=float, default=0, help='per SAT call, seconds (glucose solvers only)')
    ap.add_argument('--min-size', type=int, default=1)
    ap.add_argument('--max-size', type=int, default=99)
    ap.add_argument('--only', default='')
    ap.add_argument('--every', type=int, default=1, help='take every K-th class')
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--no-order', action='store_true', help='drop the gate-order symmetry break (pure model, slower)')
    ap.add_argument('--budget', type=float, default=0, help='stop after this many seconds in total')
    a = ap.parse_args()
    T = json.load(open(a.table))
    n, m = T['n'], T['m']
    enc = bool(T.get('encoder'))
    cols, P = inputs_for(n, m, enc)
    N = len(cols)
    full = (1 << P) - 1
    only = set(int(x) for x in a.only.split(',')) if a.only else None
    bases = ['mono', 'not'] if a.basis == 'both' else [a.basis]
    t00 = time.time()
    nok = nbad = nto = 0
    todo = []
    for ci, c in enumerate(T['classes']):
        if only is not None and ci not in only: continue
        if only is None and ci % a.every: continue
        for bs in bases:
            e = c.get(bs)
            if e and e.get('exact'): todo.append((e['size'], ci, bs))
    todo.sort()                                    # easy ones first
    for _, ci, bs in todo:
        c = T['classes'][ci]
        tgt = sum(r << (u * m) for u, r in enumerate(c['rows']))
        if True:
            e = c.get(bs)
            if not e or not e.get('exact'): continue
            size = e['size']
            if size < a.min_size or size > a.max_size: continue
            if size == 0 or tgt == full: continue
            if a.budget and time.time() - t00 > a.budget:
                print('budget exhausted; stopping'); break
            t0 = time.time(); status = 'OK'; detail = ''
            for t in range(1, size + 1):
                cl, Vr, nv = encode(cols, P, tgt, t, bs == 'not', not a.no_order)
                r, model = solve(cl, a.solver, a.timeout)
                if r is None:
                    status = 'TIMEOUT'; detail = f'at t={t}'; break
                if t < size and r:
                    status = 'MISMATCH'; detail = f'SAT at t={t} < size {size}: {decode(model, Vr, N, t, bs == "not")}'; break
                if t == size:
                    if not r:
                        status = 'MISMATCH'; detail = f'UNSAT at the table size {size}'
                    else:
                        g = decode(model, Vr, N, t, bs == 'not')
                        if evaluate(cols, P, g) != tgt:
                            status = 'MISMATCH'; detail = 'decoded circuit is wrong (encoder bug)'
            nok += status == 'OK'; nbad += status == 'MISMATCH'; nto += status == 'TIMEOUT'
            print(f'class {ci} rows {c["rows"]} {bs} size {size}: {status} {detail} ({time.time() - t0:.1f}s)', flush=True)
    print(f'summary: {nok} confirmed (UNSAT below, SAT at the size), {nbad} mismatches, {nto} timeouts, {time.time() - t00:.0f}s')
    sys.exit(1 if nbad else 0)


if __name__ == '__main__':
    main()
