#!/usr/bin/env python3
"""graphcover.py — seed circuits for GRAPH specs: a biclique cover written as  OR_i (OR rows_i) AND (OR cols_i).
The cover is naive (plain OR chains, no sharing); cktopt does the sharing and the don't-care clean-up afterwards.

  graphcover.py enum SPEC OUT.txt [--minr R] [--minc C]      list closed bicliques (rows x cols) with >= R rows, >= C cols
                                                             (hex row mask, hex column mask per line)
  graphcover.py cover SPEC BICS.txt OUT.ckt [--alpha A] [--min-ratio Q] [--min-gain G] [--keep IN.ckt] [--seed S]
        greedy weighted cover: repeatedly take the biclique maximising new_points / (rows+cols)^A; stop when the
        ratio drops below Q or the gain below G; what is left is covered by single-row terms.
        --keep IN.ckt : first take every AND gate of IN.ckt that is a biclique with >= 6 rows and >= 6 columns.
        --seed S      : random tie-breaking / noise for restarts.
Run with bin/satpy (needs int.bit_count). Single-threaded.
"""
import heapq, os, random, sys, time
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, 'py'))
import pnpfast as pf

pc = int.bit_count


def bits(x):
    r = []
    while x:
        b = x & -x; r.append(b.bit_length() - 1); x ^= b
    return r


def load_graph(spec):
    S = pf.load_spec(spec)
    if S['kind'] != 'graph': sys.exit('graphcover: graph specs only')
    n, m = S['n'], S['m']; A = S['tgt'][0]
    rowA = [(A >> (u * m)) & ((1 << m) - 1) for u in range(n)]
    colA = [sum(((rowA[u] >> v) & 1) << u for u in range(n)) for v in range(m)]
    return S, n, m, rowA, colA


def enum(spec, outp, minr, minc):
    S, n, m, rowA, colA = load_graph(spec)
    out = set()
    sys.setrecursionlimit(10000)

    def closure_rows(common):
        L = (1 << n) - 1
        for v in bits(common): L &= colA[v]
        return L

    def rec(start, k, common):
        if k >= 1:
            L = closure_rows(common)
            if pc(L) >= minr:
                out.add((L, common))
                if minr > 1: return
        for u in range(start, n):
            c = common & rowA[u]
            if pc(c) >= minc and c != common: rec(u + 1, k + 1, c)
            elif pc(c) >= minc and k == 0: rec(u + 1, 1, c)
    rec(0, 0, (1 << m) - 1)
    with open(outp, 'w') as f:
        for L, R in sorted(out, key=lambda t: -pc(t[0]) * pc(t[1])): f.write('%x %x\n' % (L, R))
    print('graphcover: %d closed bicliques with >= %d rows and >= %d columns' % (len(out), minr, minc), file=sys.stderr)


def cover(spec, bicf, outp, alpha, minratio, mingain, keep, seed):
    S, n, m, rowA, colA = load_graph(spec)
    rnd = random.Random(seed)
    B = []
    for line in open(bicf):
        a, b = line.split(); B.append((bits(int(a, 16)), int(b, 16)))
    cov = [0] * n
    chosen = []
    if keep:
        N, gates, outs = pf.load_ckt(keep)
        w = pf.eval_cols(S, N, gates)
        full = (1 << m) - 1
        for j, (op, ins) in enumerate(gates):
            if op != 'and': continue
            x = w[N + j]
            rows = [u for u in range(n) if (x >> (u * m)) & full]
            R = 0
            for u in rows: R |= (x >> (u * m)) & full
            if len(rows) >= 6 and pc(R) >= 6 and all(((x >> (u * m)) & full) == R for u in rows):
                chosen.append((rows, R))
                for u in rows: cov[u] |= R
    kept = len(chosen)
    noise = (lambda: 1.0 + 0.1 * rnd.random()) if seed else (lambda: 1.0)
    wgt = [(len(L) + pc(R)) ** alpha for L, R in B]
    def gain(i):
        R = B[i][1]; return sum(pc(R & ~cov[u]) for u in B[i][0])
    h = [(-gain(i) / wgt[i] * noise(), i) for i in range(len(B))]
    h = [t for t in h if t[0] < 0]
    heapq.heapify(h)
    while h:
        r0, i = heapq.heappop(h)
        g = gain(i)
        if g < mingain or g / wgt[i] < minratio: continue
        r = -g / wgt[i] * noise()
        if h and r > h[0][0] + 1e-12: heapq.heappush(h, (r, i)); continue
        chosen.append(B[i])
        for u in B[i][0]: cov[u] |= B[i][1]
    left = 0
    for u in range(n):
        r = rowA[u] & ~cov[u]
        if r: chosen.append(([u], r)); left += pc(r)
    # drop terms that are completely covered by the others (largest first)
    cnt = {}
    for L, R in chosen:
        for u in L:
            for v in bits(R): cnt[(u, v)] = cnt.get((u, v), 0) + 1
    final = []
    for L, R in sorted(chosen, key=lambda t: -(len(t[0]) + pc(t[1]))):
        pts = [(u, v) for u in L for v in bits(R)]
        if all(cnt[p] >= 2 for p in pts):
            for p in pts: cnt[p] -= 1
        else: final.append((L, R))
    NN = n + m; gates = []
    def chain(ws):
        cur = ws[0]
        for x in ws[1:]:
            gates.append(('or', [cur, x])); cur = NN + len(gates) - 1
        return cur
    ts = []
    for L, R in final:
        a = chain(L); b = chain([n + v for v in bits(R)])
        gates.append(('and', [a, b])); ts.append(NN + len(gates) - 1)
    o = chain(ts)
    wrong = pf.check(S, NN, gates, [o])
    if wrong: sys.exit('graphcover: internal error, cover is wrong on %d points' % wrong)
    pf.save_ckt(outp, NN, gates, [o], 'graphcover: %d terms (%d kept), %d points left to single rows' % (len(final), kept, left))
    print('graphcover: %d terms (%d kept from --keep), %d points via single rows, %d gates -> %s' % (len(final), kept, left, len(gates), outp), file=sys.stderr)


if __name__ == '__main__':
    a = sys.argv[1:]
    def opt(name, default, cast=float):
        if name in a:
            i = a.index(name); v = cast(a[i + 1]); del a[i:i + 2]; return v
        return default
    if not a: sys.exit(__doc__)
    if a[0] == 'enum':
        minr = opt('--minr', 1, int); minc = opt('--minc', 1, int)
        enum(a[1], a[2], minr, minc)
    elif a[0] == 'cover':
        alpha = opt('--alpha', 1.0); q = opt('--min-ratio', 0.0); g = opt('--min-gain', 1, int)
        keep = opt('--keep', None, str); seed = opt('--seed', 0, int)
        cover(a[1], a[2], a[3], alpha, q, g, keep, seed)
    else:
        sys.exit(__doc__)
