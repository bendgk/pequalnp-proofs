#!/usr/bin/env python3
"""Test-case generator for cktopt (no dependencies beyond py/pnpfast.py).

  gen.py random SEED N G K P DC OUTDIR basis   random circuit with N inputs, G gates, K outputs; spec = its outputs on P random
                                               points (DC = fraction of don't-care outputs); then the circuit is bloated
                                               with redundant gates. Writes OUTDIR/rand_SEED.spec and OUTDIR/rand_SEED.ckt
  gen.py dnf SPEC OUT.ckt                      naive DNF circuit (one AND-chain per true point of each output; NOT gates
                                               for negative literals) for a tt/points spec.  basis aon.
  gen.py mdnf SPEC OUT.ckt                     monotone DNF (AND of the variables that are 1 at each true point; no NOT):
                                               correct whenever the spec is monotone on its cared points.  basis ao.
  gen.py mm K OUT.ckt                          naive K x K Boolean matrix product (K^3 AND + K^2 (K-1) OR), inputs as in mm3.spec
  gen.py degenerate SEED SPEC IN.ckt OUT.ckt   rewrite a circuit with Lean-style degenerate gates (copies, constants,
                                               forward references that read false) without changing its function
"""
import os, random, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, 'py'))
import pnpfast as pf


def rand_case(seed, N, G, K, P, dc, outdir, basis):
    rnd = random.Random(seed)
    ops = ['and', 'or'] + (['not'] if basis == 'aon' else [])
    gates = []
    for j in range(G):
        op = rnd.choice(ops)
        lo = max(0, N + j - 12) if rnd.random() < 0.7 else 0
        a = rnd.randrange(lo, N + j); b = rnd.randrange(0, N + j)
        gates.append((op, [a] if op == 'not' else [a, b]))
    outs = [N + G - 1 - k for k in range(K)]
    pts = set()
    while len(pts) < min(P, 2 ** N):
        pts.add(tuple(rnd.randrange(2) for _ in range(N)))
    pts = sorted(pts)
    # evaluate on the points
    cols = [sum(p[i] << q for q, p in enumerate(pts)) for i in range(N)]
    S = dict(P=len(pts), cols=cols)
    w = pf.eval_cols(S, N, gates)
    lines = ['type points', f'inputs {N}', f'outputs {K}']
    for q, p in enumerate(pts):
        o = ''.join('-' if rnd.random() < dc else str((w[outs[k]] >> q) & 1) for k in range(K))
        lines.append('p ' + ''.join(map(str, p)) + ' ' + o)
    open(os.path.join(outdir, f'rand_{seed}.spec'), 'w').write('\n'.join(lines) + '\n')
    # bloat: duplicates, double negation, x&x, x|x, absorbed terms, dead gates
    cur = list(gates); m = {i: i for i in range(N + G)}
    def add(op, ins):
        cur.append((op, ins)); return N + len(cur) - 1
    for _ in range(G):
        x = rnd.randrange(N + G)
        r = rnd.randrange(6 if basis == 'aon' else 5)
        if r == 0: add('or', [x, x])
        elif r == 1: add('and', [x, rnd.randrange(N + len(cur))])          # dead
        elif r == 2:                                                        # absorption: x | (x & y) feeds nobody yet
            y = rnd.randrange(N + len(cur)); t = add('and', [x, y]); add('or', [x, t])
        elif r == 3: add('and', [x])                                        # copy
        elif r == 4:
            y = rnd.randrange(N + len(cur)); t = add('or', [x, y]); add('and', [x, t])
        else: t = add('not', [x]); add('not', [t])
    # re-route the outputs through redundant logic that preserves them
    newouts = []
    for o in outs:
        y = rnd.randrange(N + len(cur))
        t = add('and', [o, y]); u = add('or', [o, t])                      # o | (o & y) == o
        if basis == 'aon': v = add('not', [u]); u = add('not', [v])
        newouts.append(u)
    pf.save_ckt(os.path.join(outdir, f'rand_{seed}.ckt'), N, cur, newouts, f'random test seed {seed}, core {G} gates')
    print(len(cur))


def dnf(spec, outp):
    S = pf.load_spec(spec); N, K = S['N'], S['K']
    gates = []
    def add(op, ins):
        gates.append((op, ins)); return N + len(gates) - 1
    neg = {}
    outs = []
    for k in range(K):
        terms = []
        for p in range(S['P']):
            if not ((S['care'][k] >> p) & 1) or not ((S['tgt'][k] >> p) & 1): continue
            lits = []
            for i in range(N):
                if (S['cols'][i] >> p) & 1: lits.append(i)
                else:
                    if i not in neg: neg[i] = add('not', [i])
                    lits.append(neg[i])
            cur = lits[0]
            for x in lits[1:]: cur = add('and', [cur, x])
            terms.append(cur)
        if not terms: outs.append(add('or', []))
        else:
            cur = terms[0]
            for x in terms[1:]: cur = add('or', [cur, x])
            outs.append(cur)
    assert pf.check(S, N, gates, outs) == 0
    pf.save_ckt(outp, N, gates, outs, 'naive DNF')
    print(len(gates))


def mdnf(spec, outp):
    S = pf.load_spec(spec); N, K = S['N'], S['K']
    gates = []
    def add(op, ins):
        gates.append((op, ins)); return N + len(gates) - 1
    outs = []
    memo = {}
    for k in range(K):
        pts = [tuple(i for i in range(N) if (S['cols'][i] >> p) & 1) for p in range(S['P'])
               if ((S['care'][k] >> p) & 1) and ((S['tgt'][k] >> p) & 1)]
        mins = [t for t in set(pts) if not any(set(o) < set(t) for o in set(pts))]   # minimal true points only
        terms = []
        for lits in sorted(mins):
            if lits not in memo:
                if not lits: memo[lits] = add('and', [])
                else:
                    cur = lits[0]
                    for x in lits[1:]: cur = add('and', [cur, x])
                    memo[lits] = cur
            terms.append(memo[lits])
        if not terms: outs.append(add('or', []))
        else:
            cur = terms[0]
            for x in terms[1:]: cur = add('or', [cur, x])
            outs.append(cur)
    wrong = pf.check(S, N, gates, outs)
    if wrong: sys.exit('spec is not monotone on its cared points (wrong=%d)' % wrong)
    pf.save_ckt(outp, N, gates, outs, 'monotone DNF')
    print(len(gates))


def mm(K, outp):
    N = 2 * K * K; gates = []
    def add(op, ins):
        gates.append((op, ins)); return N + len(gates) - 1
    outs = []
    for i in range(K):
        for j in range(K):
            ts = [add('and', [K * i + k, K * K + K * k + j]) for k in range(K)]
            cur = ts[0]
            for x in ts[1:]: cur = add('or', [cur, x])
            outs.append(cur)
    pf.save_ckt(outp, N, gates, outs, 'naive matrix product')
    print(len(gates))


def degenerate(seed, spec, inp, outp):
    rnd = random.Random(seed)
    S = pf.load_spec(spec); N, gates, outs = pf.load_ckt(inp)
    new = []; m = list(range(N))
    def add(op, ins):
        new.append((op, ins)); return N + len(new) - 1
    for op, ins in gates:
        ins = [m[i] for i in ins]
        r = rnd.randrange(5)
        if r == 0 and op != 'not':                       # x op x-copy through a 1-input gate
            c = add(rnd.choice(['and', 'or']), [ins[0]]); ins = [c] + ins[1:]
        elif r == 1 and op == 'or' and len(ins) == 2:    # or with a forward reference (reads false)
            t = add('or', [ins[0], N + len(new) + 5]); ins = [t, ins[1]]
        elif r == 2 and op == 'and' and len(ins) == 2:   # and with constant true
            t = add('and', []); ins = [add('and', [ins[0], t]), ins[1]]
        m.append(add(op, ins))
    newouts = [m[o] for o in outs]
    assert pf.check(S, N, new, newouts) == 0
    pf.save_ckt(outp, N, new, newouts, 'degenerate rewrite')
    print(len(new))


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'random': rand_case(int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]), float(a[6]), a[7], a[8])
    elif a[0] == 'dnf': dnf(a[1], a[2])
    elif a[0] == 'mdnf': mdnf(a[1], a[2])
    elif a[0] == 'mm': mm(int(a[1]), a[2])
    elif a[0] == 'degenerate': degenerate(int(a[1]), a[2], a[3], a[4])
    else: sys.exit(__doc__)
