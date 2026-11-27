#!/usr/bin/env python3
"""structured.py -- And for structured graphs (run with bin/satpy; heavy runs through bin/pnprun -c 1).

    bin/satpy src/andtab/structured.py run --out runs/andtab/structured.jsonl [--sizes 4,8,16,32]
              [--families crown,match,ip,disj,inter,gt,rand1,rand2,rand3] [--timeout SEC] [--wtimeout SEC] [--redo NAME,..]
    bin/satpy src/andtab/structured.py table runs/andtab/structured.jsonl tables/and_structured.json [--md]

For each graph (one JSON line per graph, appended; graphs already in the file are skipped unless --redo):
  lower bounds, each PROVED:  (cov) ceil(log2 F) from a 0-fooling set of size F (Lemma 4; the set is stored and
      re-checked) or from the exact cover number of the zeros found by SAT;
      (sub) the family at half the size is an induced subgraph (checked here) and And is monotone under induced
      subgraphs (Lemma 5); (sat) exhaustive SAT refutation of every a below the bound (andsat.py, conditions M1-M5).
  upper bounds, each a circuit checked by andlib.eval_wit and bin/cktcheck: the SAT witness, or the explicit
      construction of andsat.construct, or (random graphs) the row-type circuit.
"exact" only when lower == upper.
"""
import argparse, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andlib, andsat


def type_circuit(n, m, T):
    """row-type or column-type circuit (And <= number of distinct types that are neither empty nor full)."""
    best = None
    for side in (0, 1):
        na, nb = (n, m) if side == 0 else (m, n)
        typ = []
        for x in range(na):
            t = 0
            for y in range(nb):
                p = x * m + y if side == 0 else y * m + x
                if (T >> p) & 1:
                    t |= 1 << y
            typ.append(t)
        fullb = (1 << nb) - 1
        L = []; R = []; out = []; seen = {}
        for x in range(na):
            if typ[x] == fullb:
                out.append(x if side == 0 else n + x); continue
            if typ[x] == 0 or typ[x] in seen:
                continue
            seen[typ[x]] = 1
            L.append([(z if side == 0 else n + z) for z in range(na) if typ[z] == typ[x]])
            R.append([(n + y if side == 0 else y) for y in range(nb) if (typ[x] >> y) & 1])
            out.append(n + m + len(L) - 1)
        if best is None or len(L) < len(best[0]):
            best = (L, R, sorted(out))
    assert andlib.eval_wit(n, m, *best) == T
    return best


def do_graph(name, fam, n, prev, a):
    rows = andsat.family_rows(fam, n)
    m = n
    T = andlib.rows_to_mask(rows, m)
    t00 = time.time()
    rec = dict(name=name, family=fam, n=n, m=m, rows=['%x' % r for r in rows], density=bin(T).count('1') / (n * m))
    lowers = []       # (value, how)
    # --- cover bound
    fs = andsat.fooling0(n, m, T, tries=100 if n <= 16 else 20)
    andsat.check_fooling0(n, m, T, fs)
    rec['fooling0'] = len(fs); rec['fooling0_set'] = fs
    lowers.append((andlib.ceil_log2(len(fs)), 'cov: 0-fooling set of size %d' % len(fs)))
    if n <= 16:
        lo, hi = andsat.cov0_sat(n, m, T, timeout=a.covtimeout)
        rec['cov0'] = [lo, hi]
        lowers.append((andlib.ceil_log2(lo), 'cov: cover number of the zeros %s (SAT)' % ('= %d' % lo if lo == hi else '>= %d' % lo)))
    if fam == 'ip':
        k = n.bit_length() - 1      # area bound: an all-zero rectangle of IP_k has at most 2^k cells (docs, Lemma 7)
        zeros = n * n - bin(T).count('1')
        c = -(-zeros // n)
        rec['cov0_area_bound'] = c
        lowers.append((andlib.ceil_log2(c), 'cov: %d zeros, every all-zero rectangle has at most %d cells, so cov0 >= %d' % (zeros, n, c)))
    # --- induced subgraph of the same family
    if prev is not None and not fam.startswith('rand'):
        h = n // 2
        sub = [r & ((1 << h) - 1) for r in rows[:h]]
        assert sub == andsat.family_rows(fam, h), 'the half-size graph is not the top-left corner'
        lowers.append((prev['lower'], 'sub: %s_%d is an induced subgraph and And(%s_%d) >= %d' % (fam, h, fam, h, prev['lower'])))
    lo = max(v for v, _ in lowers)
    how = [h for v, h in lowers if v == lo][0]
    print('%s: proved lower bound %d (%s)' % (name, lo, how), file=sys.stderr, flush=True)
    # --- independent cross-check of the proved bound: SAT deepening from 0 up to the bound (short time limit)
    proved = lo
    if lo >= 1:
        chk = andsat.and_search(n, m, T, lo=0, amax=lo - 1, timeout=a.chktimeout, nautos=a.autos)
        rec['sat_check_of_proved_bound'] = dict(steps=chk['steps'], confirmed=(chk['lower'] == lo and chk['witness'] is None))
        assert chk['witness'] is None, 'SAT found a circuit below a PROVED lower bound: bug'
        print('  SAT cross-check of the proved bound %d: %s' % (lo, 'every a < %d refuted' % lo if rec['sat_check_of_proved_bound']['confirmed'] else 'not finished: %s' % chk['steps'][-1:]), file=sys.stderr, flush=True)
    # --- SAT deepening from the proved bound
    res = andsat.and_search(n, m, T, lo=lo, amax=a.amax, timeout=a.timeout, log=sys.stderr, nautos=a.autos)
    rec['core'] = res['core']; rec['steps'] = res['steps']; rec['autos'] = res['autos']; rec['proved_bound_before_sat'] = proved
    if res['lower'] > lo:
        lo = res['lower']; how = 'sat: every a < %d refuted by exhaustive SAT (from the proved bound %d up)' % (lo, max(v for v, _ in lowers))
    wit = None; uhow = None
    if res['witness'] is not None:
        wit = res['witness']; uhow = 'SAT witness'
    else:
        # witness search above the undecided level, pure model (no minimality conditions)
        cons = andsat.construct(fam, n)
        if cons is not None:
            wit = cons[:3]; uhow = 'construction: ' + cons[3]
            assert andlib.eval_wit(n, m, *wit) == T, 'construction wrong'
        tw = type_circuit(n, m, T)
        if wit is None or len(tw[0]) < len(wit[0]):
            wit = tw; uhow = 'row-type / column-type circuit'
        ci = andlib.core(n, m, T); n2, m2, T2 = ci[0], ci[1], ci[2]
        inputs = andlib.gens(n2, m2)
        wsteps = []
        for aa in range(lo, min(len(wit[0]), lo + a.wmax)):
            t0 = time.time()
            cl, nv, info = andsat.encode(n2 * m2, inputs, T2, aa, sym=False)
            r, model, confl = andsat.run_solver(cl, 'cadical195', a.wtimeout)
            wsteps.append((aa, 'TIMEOUT' if r is None else ('SAT' if r else 'UNSAT'), round(time.time() - t0, 2), confl))
            print('  witness search a=%d: %s (%.1fs)' % (aa, wsteps[-1][1], time.time() - t0), file=sys.stderr, flush=True)
            if r:
                L, R, out = andsat.decode(model, info, aa)
                assert andlib.eval_wit(n2, m2, L, R, out, inputs) == T2
                wit = andlib.lift(n, m, ci, L, R, out); uhow = 'SAT witness (pure model, no lower-bound claim)'
                break
        rec['witness_steps'] = wsteps
    L, R, out = wit
    assert andlib.eval_wit(n, m, L, R, out) == T
    ckt, n_and, n_or = andlib.wit_to_ckt(n, m, L, R, out)
    assert andlib.cktcheck(andlib.graph_spec(n, m, rows), ckt, 'ao'), 'cktcheck refused the circuit'
    assert n_and == len(L) and n_and >= lo
    rec.update(lower=lo, lower_how=how, lower_all=lowers, upper=n_and, upper_how=uhow, exact=(lo == n_and),
               witness=dict(L=L, R=R, out=out), ckt=ckt, ckt_ands=n_and, ckt_gates=n_and + n_or, cktcheck='OK',
               seconds=round(time.time() - t00, 1))
    return rec


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    r.add_argument('--out', required=True)
    r.add_argument('--sizes', default='4,8,16,32')
    r.add_argument('--families', default='crown,match,ip,disj,inter,gt,rand1,rand2,rand3')
    r.add_argument('--timeout', type=float, default=60, help='seconds per SAT call of the deepening')
    r.add_argument('--wtimeout', type=float, default=30, help='seconds per SAT call of the witness search')
    r.add_argument('--wmax', type=int, default=99, help='witness search tries at most this many values of a above the proved bound')
    r.add_argument('--covtimeout', type=float, default=20)
    r.add_argument('--chktimeout', type=float, default=20, help='seconds per SAT call when re-proving a bound that is already proved')
    r.add_argument('--amax', type=int, default=12)
    r.add_argument('--autos', type=int, default=64)
    r.add_argument('--redo', default='')
    t = sub.add_parser('table')
    t.add_argument('runs', help='comma separated list of run files (structured.py run / ladder.py --out)')
    t.add_argument('out'); t.add_argument('--md', action='store_true')
    t.add_argument('--seq', default='', help='ladder.py --seq file: adds the corner sequences')
    a = ap.parse_args()
    if a.cmd == 'run':
        done = {}
        if os.path.exists(a.out):
            for l in open(a.out):
                e = json.loads(l); done[e['name']] = e
        redo = set(a.redo.split(',')) if a.redo else set()
        os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
        for n in [int(x) for x in a.sizes.split(',')]:
            for fam in a.families.split(','):
                name = '%s_%d' % (fam, n)
                if name in done and name not in redo:
                    continue
                prev = done.get('%s_%d' % (fam, n // 2))
                rec = do_graph(name, fam, n, prev, a)
                done[name] = rec
                with open(a.out, 'a') as f:
                    f.write(json.dumps(rec) + '\n')
                print('%s: And in [%d, %d]%s  lower: %s; upper: %s  (%.1fs)' % (name, rec['lower'], rec['upper'], ' EXACT' if rec['exact'] else '',
                      rec['lower_how'], rec['upper_how'], rec['seconds']), flush=True)
        return
    # table: the LAST line for each name wins; lines are merged keeping the best proved bounds
    # every line of every run file is a record for one graph; keep the best PROVED lower bound and the best circuit
    best = {}
    for path in a.runs.split(','):
        for l in open(path):
            e = json.loads(l)
            o = best.get(e['name'])
            if o is None:
                o = best[e['name']] = dict(name=e['name'], family=e['family'], n=e['n'], m=e['m'], rows=e['rows'],
                                           lower=-1, upper=None, proofs=[])
            assert o['rows'] == e['rows']
            if e.get('lower_how') and e['lower_how'] != 'trivial':
                p = dict(bound=e['lower'], how=e['lower_how'])
                if e.get('lower_certificate'): p['certificate'] = e['lower_certificate']
                if p not in o['proofs']: o['proofs'].append(p)
            if e['lower'] > o['lower']:
                o['lower'] = e['lower']; o['lower_how'] = e.get('lower_how', 'trivial')
            if e.get('witness') is not None and (o['upper'] is None or e['upper'] < o['upper']):
                for k in ('upper', 'upper_how', 'witness'):
                    o[k] = e[k]
            for k in ('fooling0', 'fooling0_set', 'cov0', 'cov0_area_bound', 'density', 'sat_check_of_proved_bound', 'steps', 'core'):
                if k in e and k not in o: o[k] = e[k]
    order = ['crown', 'match', 'ip', 'disj', 'inter', 'gt']
    hered = set(order)
    names = sorted(best, key=lambda x: ((order.index(best[x]['family']) if best[x]['family'] in order else 99), best[x]['family'], best[x]['n']))
    for nm in names:                    # lower bounds go up: FAMILY_{n/2} is the top-left corner of FAMILY_n (Lemma 5a)
        e = best[nm]
        h = best.get('%s_%d' % (e['family'], e['n'] // 2))
        if e['family'] in hered and h is not None and h['lower'] > e['lower']:
            assert [r & ((1 << h['n']) - 1) for r in [int(x, 16) for x in e['rows']][:h['n']]] == [int(x, 16) for x in h['rows']]
            e['lower'] = h['lower']
            e['lower_how'] = 'sub: %s is an induced subgraph (top-left corner) and And(%s) >= %d [%s]' % (h['name'], h['name'], h['lower'], h['lower_how'])
            e['proofs'].append(dict(bound=e['lower'], how=e['lower_how']))
    for nm in names:                    # upper bounds by doubling the half-size circuit (match, gt: +2 AND gates)
        e = best[nm]
        h = best.get('%s_%d' % (e['family'], e['n'] // 2))
        if e['family'] in ('match', 'gt') and h is not None and h['upper'] is not None and (e['upper'] is None or h['upper'] + 2 < e['upper']):
            hn = h['n']; w = h['witness']
            L, R, out = andsat.double_wit(e['family'], hn, w['L'], w['R'], w['out'])
            assert andlib.eval_wit(e['n'], e['n'], L, R, out) == andlib.rows_to_mask([int(x, 16) for x in e['rows']], e['n'])
            e['upper'] = len(L); e['witness'] = dict(L=L, R=R, out=out)
            e['upper_how'] = ('doubling the circuit of %s (%s): 2 more AND gates, top index bit handled separately'
                              % (h['name'], h['upper_how']))
    graphs = []
    for nm in names:
        e = best[nm]
        n = e['n']; rows = [int(x, 16) for x in e['rows']]
        T = andlib.rows_to_mask(rows, n)
        w = e['witness']
        assert andlib.eval_wit(n, n, w['L'], w['R'], w['out']) == T
        ckt, n_and, n_or = andlib.wit_to_ckt(n, n, w['L'], w['R'], w['out'])
        assert andlib.cktcheck(andlib.graph_spec(n, n, rows), ckt, 'ao') and n_and == e['upper'] and e['upper'] >= e['lower']
        e.update(ckt=ckt, ckt_ands=n_and, ckt_gates=n_and + n_or, cktcheck='OK', exact=(e['lower'] == e['upper']))
        graphs.append(e)
    Tb = dict(
        quantity='And = least number of AND gates (fan-in two) with free OR gates, Represents semantics; see docs/andtab.md',
        definitions=dict(crown='u != v', match='u == v', ip='inner product mod 2 of the binary indices: popcount(u & v) odd',
                         disj='index bit-sets disjoint: u & v == 0', inter='u & v != 0', gt='u > v',
                         randS='random.Random(1000*n + S).getrandbits(n) per row (Python), density 1/2'),
        rows_convention='rows[u] is hex; bit v of rows[u] = A u v',
        status_note=('"exact": true iff lower == upper. lower_how says how the lower bound was PROVED ("proofs" lists every proved '
                     'bound for the graph); upper_how where the circuit comes from. "witness" (L, R, out as in tables/and_N.json) and '
                     '"ckt" are the circuit with "upper" AND gates; every circuit passed bin/cktcheck --basis ao.'),
        graphs=graphs)
    if a.seq and os.path.exists(a.seq):
        seqs = {}
        for l in open(a.seq):
            e = json.loads(l)
            key = e['graph'] + (' (rows and columns 1..k-1)' if e['drop0'] else ' (rows and columns 0..k-1)')
            seqs.setdefault(key, {})[e['k']] = dict(k=e['k'], size=e['size'], lower=e['lower'], upper=e['upper'], exact=e['exact'], steps=e['steps'])
        Tb['corner_sequences'] = {k: [v[i] for i in sorted(v)] for k, v in seqs.items()}
        Tb['corner_sequences_note'] = ('And of the induced subgraph on the first k indices of the named graph (ladder.py): "exact" entries are '
                                       'And of that corner; otherwise "lower" is proved and the SAT call at that value timed out.')
    json.dump(Tb, open(a.out, 'w'), separators=(',', ':'))
    print('wrote %s: %d graphs' % (a.out, len(graphs)), file=sys.stderr)
    if a.md:
        fams = []
        for e in graphs:
            if e['family'] not in fams: fams.append(e['family'])
        sizes = sorted(set(e['n'] for e in graphs))
        print('| graph | ' + ' | '.join('n = %d' % s for s in sizes) + ' |')
        print('|---|' + '---|' * len(sizes))
        for f in fams:
            cells = []
            for s in sizes:
                e = best.get('%s_%d' % (f, s))
                if e is None: cells.append('')
                elif e['exact']: cells.append('**%d**' % e['upper'])
                else: cells.append('%d..%d' % (e['lower'], e['upper']))
            print('| %s | ' % f + ' | '.join(cells) + ' |')
        print()
        for e in graphs:
            print('- `%s`: %s; lower: %s; upper: %s' % (e['name'], ('And = %d' % e['upper']) if e['exact'] else 'And in [%d, %d]' % (e['lower'], e['upper']), e['lower_how'], e['upper_how']))


if __name__ == '__main__':
    main()
