#!/usr/bin/env python3
"""enc8.py -- a SAMPLE of 8x8 graphs with free encoder wires (run with bin/satpy).

    bin/satpy src/startab/enc8.py tables/star_8_enc_sample.json [--state runs/startab/enc8.state.jsonl]
                                  [--conf N] [--budget SEC] [--smax S] [--only name,name] [--basis mono|not|both]

Inputs of the circuit: the 16 stars (wires 0..7 rows, 8..15 columns) plus the 12 free encoder wires
(16..21: rb0=0, rb0=1, rb1=0, rb1=1, rb2=0, rb2=1;  22..27: the same for the column index).
For each named graph and basis the script proves lower bounds and finds circuits by SAT (the encoding of
satcheck.py: exactly t gates, every gate read, output last; plus the sound gate-order symmetry break):
    t = 1, 2, ... : UNSAT within --conf conflicts  -> size > t ;  SAT -> size = t (exact, all smaller t refuted);
    conflict limit hit -> the lower bound stops at t; an upper bound is then looked for with the stochastic
    search bin/cktsls at sizes lower, lower+1, ... (heuristic: finds circuits, proves nothing).
A second rigorous lower bound comes from the exact 4x4 encoder table: fixing one row-index bit and one column-index
bit restricts the graph to a 4x4 graph, the restricted input wires are 4x4 input wires, zero or all-one, and neither
zero nor all-one wires help a least circuit of a target that is not all-one (docs/startab.md), so
size_8(G) >= size_4(restriction) for every restriction that is not the complete graph.
Results are cached in the state file (one JSON line per finished SAT call), so the script can be re-run with
a larger --conf or --smax and continues where it stopped.
"""
import argparse, json, os, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import satcheck, mktable, lookup

N8 = 8


def graphs():
    G = {}
    def add(name, f, note):
        G[name] = (tuple(sum(1 << v for v in range(8) if f(u, v)) for u in range(8)), note)
    bit = lambda x, i: (x >> i) & 1
    add('biclique_x2_y2', lambda u, v: bit(u, 2) & bit(v, 2), 'K_{4,4}: x2 AND y2')
    add('intersect', lambda u, v: int(u & v != 0), 'x AND y != 0 (OR_i x_i y_i)')
    add('disjoint', lambda u, v: int(u & v == 0), 'x AND y = 0')
    add('equal_low2', lambda u, v: int((u & 3) == (v & 3)), 'x1x0 = y1y0 (two disjoint copies of a 4x4 matching, blown up)')
    add('xor_bit0', lambda u, v: bit(u, 0) ^ bit(v, 0), 'x0 XOR y0')
    add('xor_two', lambda u, v: (bit(u, 0) ^ bit(v, 0)) | (bit(u, 1) ^ bit(v, 1)), '(x0 XOR y0) OR (x1 XOR y1)')
    add('matching', lambda u, v: int(u == v), 'identity: u = v')
    add('crown', lambda u, v: int(u != v), 'crown: u != v')
    add('half_le', lambda u, v: int(u <= v), 'half graph: u <= v')
    add('half_lt', lambda u, v: int(u < v), 'u < v')
    add('parity', lambda u, v: bin(u ^ v).count('1') & 1, 'parity of all six bits')
    add('ip', lambda u, v: bin(u & v).count('1') & 1, 'inner product mod 2')
    add('sum_mod8_zero', lambda u, v: int((u + v) % 8 == 0), 'u + v = 0 mod 8 (a perfect matching)')
    add('cycle16', lambda u, v: int(v == u or v == (u + 1) % 8), 'Hamilton cycle C16: v in {u, u+1}')
    add('threshold_sum_ge7', lambda u, v: int(u + v >= 7), 'u + v >= 7')
    add('paley_like', lambda u, v: int(((u - v) % 8) in (1, 2, 4)), 'v - u in {1,2,4} mod 8 (circulant)')
    add('majority3', lambda u, v: int(bit(u, 0) + bit(u, 1) + bit(v, 0) >= 2), 'MAJ(x0, x1, y0)')
    add('single_edge', lambda u, v: int(u == 3 and v == 5), 'one edge')
    add('star_minus_point', lambda u, v: int(u == 0 and v != 0), 'row star without one point')
    return G


def constructions():
    """explicit circuits (upper bounds) for some of the named graphs; wires: rows 0..7, columns 8..15,
    row-bit sets 16+2i+a, column-bit sets 22+2i+a"""
    rb = lambda i, a: 16 + 2 * i + a
    cb = lambda i, a: 22 + 2 * i + a
    C = {}
    def circuit(f):
        g = []
        def G(op, a, b):
            g.append((op, a, b)); return 28 + len(g) - 1
        f(G)
        return 'inputs 28\n' + ''.join('%s %d %d\n' % x for x in g) + 'out %d\n' % (28 + len(g) - 1)
    def matching(G):                      # AND_i (x_i = y_i)
        e = [G('or', G('and', rb(i, 0), cb(i, 0)), G('and', rb(i, 1), cb(i, 1))) for i in range(3)]
        G('and', G('and', e[0], e[1]), e[2])
    def crown(G):                         # OR_i (x_i != y_i)
        e = [G('or', G('and', rb(i, 0), cb(i, 1)), G('and', rb(i, 1), cb(i, 0))) for i in range(3)]
        G('or', G('or', e[0], e[1]), e[2])
    def parity(G):                        # (rows of odd weight AND columns of even weight) OR (even AND odd), by stars
        odd = [u for u in range(8) if bin(u).count('1') & 1]; even = [u for u in range(8) if not bin(u).count('1') & 1]
        def orl(ws):
            w = ws[0]
            for x in ws[1:]: w = G('or', w, x)
            return w
        ro, re_, co, ce = orl(odd), orl(even), orl([8 + v for v in odd]), orl([8 + v for v in even])
        G('or', G('and', ro, ce), G('and', re_, co))
    def ip(G):                            # dual-rail XOR of the three products x_i y_i
        m = [G('and', rb(i, 1), cb(i, 1)) for i in range(3)]
        nm = [G('or', rb(i, 0), cb(i, 0)) for i in range(3)]
        b = G('or', G('and', m[0], nm[1]), G('and', nm[0], m[1]))
        nb = G('or', G('and', m[0], m[1]), G('and', nm[0], nm[1]))
        G('or', G('and', b, nm[2]), G('and', nb, m[2]))
    for name, f in (('matching', matching), ('crown', crown), ('parity', parity), ('ip', ip)):
        C[name] = circuit(f)
    return C


def subcube_lower(rows, T4):
    """max over the 36 (row bit, value, column bit, value) restrictions of the exact 4x4 encoder sizes"""
    idx = {tuple(c['rows']): c for c in T4['classes']}
    best = {'mono': 0, 'not': 0}
    for i in range(3):
        for a in (0, 1):
            us = [u for u in range(8) if ((u >> i) & 1) == a]
            for j in range(3):
                for b in (0, 1):
                    vs = [v for v in range(8) if ((v >> j) & 1) == b]
                    sub = [sum(((rows[u] >> v) & 1) << y for y, v in enumerate(vs)) for u in us]
                    if all(r == 15 for r in sub): continue      # all-one restriction: an all-one wire may be free here
                    _, crow, _ = lookup.canon(sub, 4, 4, True, True)
                    c = idx[tuple(crow)]
                    for k in best: best[k] = max(best[k], c[k]['size'])
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out')
    ap.add_argument('--state', default=os.path.join(os.environ.get('PNP_RUNS') or os.path.join(ROOT, 'runs'), 'startab', 'enc8.state.jsonl'))
    ap.add_argument('--conf', type=int, default=300000, help='conflict limit per SAT call')
    ap.add_argument('--budget', type=float, default=0, help='stop starting new SAT calls after SEC seconds')
    ap.add_argument('--smax', type=int, default=14)
    ap.add_argument('--sls-time', type=float, default=5, help='seconds per bin/cktsls attempt (upper bounds)')
    ap.add_argument('--sls-range', type=int, default=10, help='sizes lower..lower+range-1 are tried for an upper bound')
    ap.add_argument('--only', default='')
    ap.add_argument('--basis', default='both')
    ap.add_argument('--table4', default=os.path.join(ROOT, 'tables', 'star_4_enc.json'))
    a = ap.parse_args()
    from pysat.solvers import Solver
    cols, P = satcheck.inputs_for(8, 8, True)
    N = len(cols)
    full = (1 << P) - 1
    T4 = json.load(open(a.table4))
    state = {}
    if os.path.exists(a.state):
        for line in open(a.state):
            e = json.loads(line)
            key = (e['name'], e['basis'], e['t'])
            if key not in state or e['res'] not in ('limit', 'none') or (state[key]['res'] == 'limit' and e['conf'] > state[key]['conf']) \
               or (state[key]['res'] == 'none' and e['res'] == 'none' and e['secs'] > state[key]['secs']):
                state[key] = e
    sf = open(a.state, 'a')
    G = graphs()
    only = set(a.only.split(',')) if a.only else None
    bases = ['mono', 'not'] if a.basis == 'both' else [a.basis]
    t00 = time.time()
    tmp = tempfile.mkdtemp(prefix='enc8_')
    out = []
    ents = {}
    CONS = constructions()
    def run_sat(name, bs, tgt, t):
        key = (name, bs, t)
        e = state.get(key)
        need = e is None or (e['res'] == 'limit' and e['conf'] < a.conf)
        if need and (only is None or name in only) and not (a.budget and time.time() - t00 > a.budget):
            cl, Vr, nv = satcheck.encode(cols, P, tgt, t, bs == 'not', True)
            S = Solver(name='cadical195', bootstrap_with=cl)
            S.conf_budget(a.conf)
            t0 = time.time()
            r = S.solve_limited()
            e = dict(name=name, basis=bs, t=t, conf=a.conf, secs=round(time.time() - t0, 2),
                     res='sat' if r else 'unsat' if r is False else 'limit')
            if r:
                g = satcheck.decode(S.get_model(), Vr, N, t, bs == 'not')
                assert satcheck.evaluate(cols, P, g) == tgt
                e['ckt'] = 'inputs %d\n' % N + ''.join(('not %d\n' % j) if op == 'not' else ('%s %d %d\n' % (op, j, k)) for op, j, k in g) + 'out %d\n' % (N + t - 1)
            S.delete()
            state[key] = e
            sf.write(json.dumps(e) + '\n'); sf.flush()
            print('%-20s %-4s t=%-2d %-5s %6.1fs' % (name, bs, t, e['res'], e['secs']), flush=True)
        return e
    def run_sls(name, bs, rows, s_):
        key = (name, bs, 'sls%d' % s_)
        e = state.get(key)
        retry = e is not None and e['res'] == 'none' and e['secs'] < a.sls_time - 0.5     # a longer attempt is allowed to retry
        if (e is None or retry) and (only is None or name in only) and not (a.budget and time.time() - t00 > a.budget):
            sp = os.path.join(tmp, 'sls.spec'); ck = os.path.join(tmp, 'sls.ckt')
            open(sp, 'w').write(mktable.spec_text(8, 8, True, list(rows)))
            if os.path.exists(ck): os.unlink(ck)
            t0 = time.time()
            r = subprocess.run([os.path.join(ROOT, 'bin', 'cktsls'), sp, '--basis', 'ao' if bs == 'mono' else 'aon', '-s', str(s_), '-j', '1',
                                '--time', str(a.sls_time), '--seed', '3', '-o', ck, '-q'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            e = dict(name=name, basis=bs, t='sls%d' % s_, conf=0, secs=round(time.time() - t0, 2), res='none')
            if r.returncode == 0 and os.path.exists(ck):
                text = ''.join(l for l in open(ck) if not l.startswith('#'))
                e['res'] = 'found'; e['ckt'] = text
                e['size'] = sum(1 for l in text.split('\n') if l.split()[:1] and l.split()[0] in ('and', 'or', 'not'))
            state[key] = e
            sf.write(json.dumps(e) + '\n'); sf.flush()
            print('%-20s %-4s sls s=%-2d %-5s %6.1fs' % (name, bs, s_, e['res'] + (' %d' % e['size'] if e['res'] == 'found' else ''), e['secs']), flush=True)
        return e
    for bs in bases:                       # all graphs in the first basis, then the second
        for name, (rows, note) in G.items():
            tgt = sum(r << (u * 8) for u, r in enumerate(rows))
            sub = subcube_lower(rows, T4)
            ent = ents.setdefault(name, dict(name=name, note=note, rows=list(rows)))
            d = dict(size=None, exact=False, lower=1, witness=None)
            if tgt == 0 or tgt in cols:
                d = dict(size=0, exact=True, witness='inputs %d\nout %d\n' % (N, N if tgt == 0 else cols.index(tgt)))
            elif tgt == full:
                d = dict(size=1, exact=True, witness='inputs %d\nand\nout %d\n' % (N, N))
            else:
                lower_sat = 1          # every t < lower_sat refuted by SAT
                for t in range(1, a.smax + 1):
                    e = run_sat(name, bs, tgt, t)
                    if e is None or e['res'] == 'limit': break
                    if e['res'] == 'sat':
                        d['size'] = t; d['witness'] = e['ckt']; break
                    lower_sat = t + 1
                d['lower_sat'] = lower_sat
                d['lower_subcube'] = sub[bs]
                d['lower'] = max(lower_sat, sub[bs])
                if d['size'] is None:      # upper bound by stochastic search (heuristic)
                    # best circuit already in the cache, if any
                    for (nm_, bs_, t_), e in state.items():
                        if nm_ == name and bs_ == bs and e['res'] == 'found' and (d['size'] is None or e['size'] < d['size']):
                            d['size'] = e['size']; d['witness'] = e['ckt']; d['how'] = 'stochastic search (bin/cktsls)'
                    if d['size'] is None:  # nothing yet: smallest size that succeeds, going up
                        for s_ in range(d['lower'], d['lower'] + a.sls_range):
                            e = run_sls(name, bs, rows, s_)
                            if e is None: break
                            if e['res'] == 'found':
                                d['size'] = e['size']; d['witness'] = e['ckt']; d['how'] = 'stochastic search (bin/cktsls)'; break
                    else:                  # improve: going down from the best known size
                        while d['size'] - 1 >= d['lower']:
                            e = run_sls(name, bs, rows, d['size'] - 1)
                            if e is None or e['res'] != 'found': break
                            d['size'] = e['size']; d['witness'] = e['ckt']; d['how'] = 'stochastic search (bin/cktsls)'
                if bs == 'not' and 'mono' in ent and ent['mono'].get('size') is not None and (d['size'] is None or ent['mono']['size'] < d['size']):
                    d['size'] = ent['mono']['size']; d['witness'] = ent['mono']['witness']     # a monotone circuit is a FanInTwo circuit
                    d['how'] = 'the monotone circuit'
                if name in CONS:           # explicit construction (monotone, so valid in both bases)
                    text = CONS[name]
                    sz = sum(1 for l in text.split('\n') if l.split()[:1] and l.split()[0] in ('and', 'or', 'not'))
                    if d['size'] is None or sz < d['size']:
                        d['size'] = sz; d['witness'] = text; d['how'] = 'explicit construction'
                d['exact'] = d['size'] is not None and d['size'] == d['lower']
            if d.get('witness'):
                sp = os.path.join(tmp, 's.spec'); ck = os.path.join(tmp, 'c.ckt')
                open(sp, 'w').write(mktable.spec_text(8, 8, True, list(rows))); open(ck, 'w').write(d['witness'])
                r = subprocess.run([os.path.join(ROOT, 'bin', 'cktcheck'), sp, ck, '--basis', 'ao' if bs == 'mono' else 'aon', '--max', str(d['size']), '-q'])
                assert r.returncode == 0, 'cktcheck failed for %s %s' % (name, bs)
            ent[bs] = d
    out = [ents[name] for name in G if name in ents]
    names = ['r%d' % i for i in range(8)] + ['c%d' % i for i in range(8)] + ['rb%d=%d' % (i, v) for i in range(3) for v in (0, 1)] + ['cb%d=%d' % (i, v) for i in range(3) for v in (0, 1)]
    T = dict(n=8, m=8, encoder=True, inputs=names,
             semantics=('SAMPLE of named 8x8 graphs, sizes with the 16 stars plus the 12 free encoder wires as inputs (same model as '
                        'star_4_enc.json). "lower" is proved: max of "lower_sat" (every smaller number of gates refuted by SAT in the '
                        'normal-form model) and "lower_subcube" (largest exact 4x4 encoder size of a restriction obtained by fixing one '
                        'row-index bit and one column-index bit). "size" is the smallest circuit found (checked with bin/cktcheck); '
                        '"exact" iff size == lower. Labelled graphs; no symmetry reduction.'),
             rows_convention='bit v of rows[u] = A u v', classes=out)
    json.dump(T, open(a.out, 'w'), indent=1)
    print('wrote', a.out)
    for e in out:
        print('  %-20s' % e['name'], ' '.join('%s: %s%s' % (bs, e[bs]['size'], '' if e[bs]['exact'] else ' (lower %d)' % e[bs]['lower']) for bs in bases if bs in e))


if __name__ == '__main__':
    main()
