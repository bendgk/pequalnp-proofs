#!/usr/bin/env python3
"""ubsls.py -- better UPPER bounds for table entries that are not exact, with the stochastic search bin/cktsls.

    python3 src/startab/ubsls.py tables/star_5.json OUT.jsonl [--which undecided|all] [--basis mono|not|both]
                                 [--time S] [-j T] [--budget SEC] [--seed X]

For every selected entry (class, basis) with "exact": false it asks bin/cktsls (heuristic, another toolkit tool)
for a circuit with size-1, size-2, ... gates, never below the proved "lower", S seconds per attempt, and appends
every improvement to OUT.jsonl as {"f","rows","basis","size","witness","how"}.  mktable.py --ub OUT.jsonl merges
them (each circuit is re-checked with bin/cktcheck there; an entry becomes exact when the size meets "lower").
--which undecided : only the classes listed under "undecided_by_bounds" of the two conjecture blocks (default).
Nothing here can change a lower bound or an "exact": true entry.
"""
import argparse, json, os, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('table'); ap.add_argument('out')
    ap.add_argument('--which', default='undecided')
    ap.add_argument('--basis', default='mono')
    ap.add_argument('--time', type=float, default=20)
    ap.add_argument('-j', type=int, default=int(os.environ.get('PNP_THREADS', '1')))
    ap.add_argument('--budget', type=float, default=0)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    T = json.load(open(a.table))
    n, m = T['n'], T['m']
    assert not T['encoder']
    want = None
    if a.which == 'undecided':
        want = set()
        for e in T['summary']['not_saving'].get('undecided_by_bounds', []): want.add(tuple(e['rows']))
        for e in T['complement_gap'].get('undecided_by_bounds', []):
            want.add(tuple(e['rows'])); want.add(tuple(e['complement_rows']))
    bases = ['mono', 'not'] if a.basis == 'both' else [a.basis]
    tmp = tempfile.mkdtemp(prefix='ubsls_')
    t0 = time.time()
    out = open(a.out, 'a')
    todo = []
    for c in T['classes']:
        if want is not None and tuple(c['rows']) not in want: continue
        for bs in bases:
            e = c[bs]
            if e['exact'] or e['size'] is None: continue
            todo.append((e['size'] - e['lower'], c, bs))
    todo.sort(key=lambda x: -x[0])                         # widest gaps first
    for _, c, bs in todo:
        e = c[bs]
        spec = os.path.join(tmp, 's.spec')
        open(spec, 'w').write('type graph\nn %d\nm %d\nrows %s\n' % (n, m, ' '.join('%x' % r for r in c['rows'])))
        size = e['size']
        while size - 1 >= e['lower']:
            if a.budget and time.time() - t0 > a.budget: break
            ck = os.path.join(tmp, 'c.ckt')
            if os.path.exists(ck): os.unlink(ck)
            r = subprocess.run([os.path.join(ROOT, 'bin', 'cktsls'), spec, '--basis', 'ao' if bs == 'mono' else 'aon', '-s', str(size - 1),
                                '-j', str(a.j), '--time', str(a.time), '--seed', str(a.seed), '-o', ck, '-q'],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if r.returncode != 0 or not os.path.exists(ck): break
            chk = subprocess.run([os.path.join(ROOT, 'bin', 'cktcheck'), spec, ck, '--basis', 'ao' if bs == 'mono' else 'aon', '--max', str(size - 1), '-q'])
            if chk.returncode != 0: break
            text = ''.join(l for l in open(ck) if not l.startswith('#'))
            size = sum(1 for l in text.split('\n') if l.split()[:1] and l.split()[0] in ('and', 'or', 'not'))
            f = sum(r_ << (m * u) for u, r_ in enumerate(c['rows']))
            out.write(json.dumps(dict(f=f, rows=c['rows'], basis='ao' if bs == 'mono' else 'aon', size=size, witness=text,
                                      how='stochastic search (bin/cktsls)')) + '\n'); out.flush()
            print('class %d rows %s %s: %d -> %d (lower %d)' % (c['id'], c['rows'], bs, e['size'], size, e['lower']), flush=True)
        if a.budget and time.time() - t0 > a.budget: break
    print('done in %.0fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
