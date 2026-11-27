#!/usr/bin/env python3
"""ladder.py -- lower bounds for a big graph from its small corners (run with bin/satpy, heavy runs via bin/pnprun).

    bin/satpy src/andtab/ladder.py FAMILY N [--kmin K] [--drop0] [--timeout SEC] [--out runs/andtab/ladder.jsonl]
                                            [--seq runs/andtab/ladder_seq.jsonl] [--autos 400] [--amax A]

G = the N x N graph FAMILY_N (andsat.family_rows), G_k = its induced subgraph on rows and columns 0..k-1
(with --drop0: on rows and columns 1..k-1).  And is monotone under induced subgraphs (docs/andtab.md, Lemma 5),
so And(G_k) is non-decreasing in k and every lower bound for G_k is a lower bound for G.
For k = kmin..N: iterative deepening by SAT starting at the bound proved so far (andsat.and_search with lo = that
bound, conditions M1-M6 are then legitimate).  UNSAT raises the bound; SAT gives And(G_k) exactly; a time-out
keeps the bound and the ladder goes on to the next k (with a quarter of the time limit until the bound moves).
Writes one line per k to --seq and, at the end, one record for FAMILY_N to --out in the format of structured.py
(lower bound with its certificate; upper bound only if And(G_N) itself was settled).
"""
import argparse, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andlib, andsat


def corner(rows_full, k, drop0):
    idx = list(range(1, k)) if drop0 else list(range(k))
    rows = [sum(1 << b for b, v in enumerate(idx) if (rows_full[u] >> v) & 1) for u in idx]
    return rows, len(idx)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('family'); ap.add_argument('n', type=int)
    ap.add_argument('--kmin', type=int, default=2)
    ap.add_argument('--drop0', action='store_true')
    ap.add_argument('--timeout', type=float, default=120)
    ap.add_argument('--amax', type=int, default=10)
    ap.add_argument('--autos', type=int, default=400)
    ap.add_argument('--model', default='B')
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--lo', type=int, default=0, help='bound already proved for the corner kmin (default 0)')
    ap.add_argument('--out', default='runs/andtab/ladder.jsonl')
    ap.add_argument('--seq', default='runs/andtab/ladder_seq.jsonl')
    a = ap.parse_args()
    n = a.n
    rows_full = andsat.family_rows(a.family, n)
    name = '%s_%d' % (a.family, n)
    lo = a.lo; cert = None; stuck_at = None
    last = None
    for k in range(a.kmin, n + 1):
        rows, kk = corner(rows_full, k, a.drop0)
        if kk < 1:
            continue
        T = andlib.rows_to_mask(rows, kk)
        tmo = a.timeout / 4 if stuck_at == lo else a.timeout
        t0 = time.time()
        res = andsat.and_search(kk, kk, T, lo=lo, amax=a.amax, timeout=tmo, nautos=a.autos, model=a.model, solver=a.solver)
        rec = dict(graph=name, k=k, drop0=a.drop0, size=kk, rows=['%x' % r for r in rows], lower=res['lower'], upper=res['upper'],
                   exact=res['exact'], steps=res['steps'], started_at=lo, seconds=round(time.time() - t0, 1), model=a.model, solver=a.solver)
        if res['lower'] > lo:
            cert = dict(k=k, drop0=a.drop0, size=kk, rows=rec['rows'], steps=res['steps'], started_at=lo, proved=res['lower'])
        lo = res['lower']
        if any(s[1] == 'TIMEOUT' for s in res['steps']):
            stuck_at = lo
        if res['witness'] is not None:
            L, R, out = res['witness']
            assert andlib.eval_wit(kk, kk, L, R, out) == T
            rec['witness'] = dict(L=L, R=R, out=out)
        with open(a.seq, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        print('%s corner k=%d%s (%dx%d): And %s  steps %s  (%.1fs)' % (name, k, ' drop0' if a.drop0 else '', kk, kk,
              ('= %d' % res['upper']) if res['exact'] else '>= %d' % res['lower'], res['steps'][1:], time.time() - t0), flush=True)
        last = (rec, res, rows, kk, T)
    # record for the full graph
    full_rows = rows_full
    out = dict(name=name, family=a.family, n=n, m=n, rows=['%x' % r for r in full_rows], lower=lo, upper=None, exact=False,
               source='ladder')
    if cert is not None:
        out['lower_how'] = ('sub+sat: the induced subgraph on rows and columns %s (size %d) needs %d AND gates: every a < %d refuted by '
                            'exhaustive SAT on it (deepening started at the bound %d proved on smaller corners)'
                            % ('1..%d' % (cert['k'] - 1) if cert['drop0'] else '0..%d' % (cert['k'] - 1), cert['size'], cert['proved'], cert['proved'], cert['started_at']))
        out['lower_certificate'] = cert
    else:
        out['lower_how'] = 'trivial'
    rec, res, rows, kk, T = last
    if not a.drop0 and res['witness'] is not None and kk == n:
        L, R, o = res['witness']
        ckt, n_and, n_or = andlib.wit_to_ckt(n, n, L, R, o)
        assert andlib.cktcheck(andlib.graph_spec(n, n, full_rows), ckt, 'ao')
        out.update(upper=n_and, upper_how='SAT witness', exact=(n_and == lo), witness=dict(L=L, R=R, out=o), ckt=ckt, ckt_ands=n_and,
                   ckt_gates=n_and + n_or, cktcheck='OK')
    with open(a.out, 'a') as f:
        f.write(json.dumps(out) + '\n')
    print('%s: proved lower bound %d (%s)' % (name, lo, out['lower_how']), flush=True)


if __name__ == '__main__':
    main()
