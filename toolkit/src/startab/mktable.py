#!/usr/bin/env python3
"""mktable.py -- merge the two startab runs (basis ao and aon) of one size into tables/star_*.json.

    python3 src/startab/mktable.py AO.jsonl AON.jsonl OUT.json [--ub UB.jsonl ...] [--no-cktcheck] [--md]

* every witness is re-checked with bin/cktcheck against a spec generated here for that graph
  (graph spec for the plain tables, points spec for the encoder tables; basis ao resp. aon, --max size);
* sanity checks: not <= mono, sizes monotone under nothing else, complement lookup is an involution;
* writes the summary blocks: histograms, NOT saving against 2n-5, complement gap against 2n-4.
--ub FILE.jsonl : extra upper bounds (lines {"f":int,"basis":"ao"|"aon","size":k,"witness":"..."}) for classes
                  the exhaustive run did not reach; they are stored with "exact": false.
--md            : print the summary as markdown on stdout.
"""
import collections, json, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CKTCHECK = os.path.join(ROOT, 'bin', 'cktcheck')


def load(path):
    L = [json.loads(l) for l in open(path)]
    return L[0], L[1:]


def input_cols(n, m, enc):
    cols = [sum(1 << (u * m + v) for v in range(m)) for u in range(n)]
    cols += [sum(1 << (u * m + v) for u in range(n)) for v in range(m)]
    if enc:
        kr = n.bit_length() - 1; kc = m.bit_length() - 1
        for i in range(kr):
            for a in (0, 1):
                cols.append(sum(cols[u] for u in range(n) if ((u >> i) & 1) == a))
        for i in range(kc):
            for a in (0, 1):
                cols.append(sum(cols[n + v] for v in range(m) if ((v >> i) & 1) == a))
    return cols


def spec_text(n, m, enc, rows):
    if not enc:
        return 'type graph\nn %d\nm %d\nrows %s\n' % (n, m, ' '.join('%x' % r for r in rows))
    cols = input_cols(n, m, True)
    out = ['type points', 'inputs %d' % len(cols), 'outputs 1']
    for u in range(n):
        for v in range(m):
            p = u * m + v
            out.append('p %s %d' % (''.join('1' if (c >> p) & 1 else '0' for c in cols), (rows[u] >> v) & 1))
    return '\n'.join(out) + '\n'


def main():
    a = sys.argv[1:]
    ubfiles = []; do_check = True; md = False; plain = None
    pos = []
    i = 0
    while i < len(a):
        if a[i] == '--ub': ubfiles.append(a[i + 1]); i += 2
        elif a[i] == '--no-cktcheck': do_check = False; i += 1
        elif a[i] == '--md': md = True; i += 1
        elif a[i] == '--plain-costs': plain = (a[i + 1], a[i + 2]); i += 3
        else: pos.append(a[i]); i += 1
    if len(pos) != 3: sys.exit(__doc__)
    hA, A = load(pos[0]); hB, B = load(pos[1])
    assert hA['basis'] == 'ao' and hB['basis'] == 'aon'
    for k in ('n', 'm', 'enc', 'group', 'classes', 'transpose'):
        assert hA[k] == hB[k], 'the two runs are for different problems'
    n, m, enc = hA['n'], hA['m'], hA['enc']
    assert len(A) == len(B) == hA['classes']
    ub = collections.defaultdict(dict)
    for f in ubfiles:
        for line in open(f):
            e = json.loads(line)
            key = 'mono' if e['basis'] == 'ao' else 'not'
            if e['f'] not in ub[key] or e['size'] < ub[key][e['f']]['size']:
                ub[key][e['f']] = e
    tmp = tempfile.mkdtemp(prefix='startab_')
    nchecked = 0
    classes = []
    for x, y in zip(A, B):
        assert x['f'] == y['f'] and x['rows'] == y['rows'] and x['orbit'] == y['orbit'] and x['ccls'] == y['ccls']
        c = dict(id=x['cls'], rows=x['rows'], orbit_size=x['orbit'], complement=x['ccls'])
        for key, e, h, basis in (('mono', x, hA, 'ao'), ('not', y, hB, 'aon')):
            if e['size'] is not None:
                assert e.get('verified') is True, 'unverified witness in the run output'
                d = dict(size=e['size'], exact=bool(e['exact']), witness=e['witness'])
                if 'lower' in e:                 # not reached by a complete pass: circuit found by decomposition
                    assert e['size'] >= e['lower'] and e['exact'] == (e['size'] == e['lower'])
                    d['lower'] = e['lower']; d['how'] = 'lower bound from the last complete pass, circuit by decomposition'
            else:
                d = dict(size=None, exact=False, lower=e['lower'], witness=None)
            if not d['exact']:
                u = ub[key].get(x['f'])
                if u is not None and (d['size'] is None or u['size'] < d['size']):
                    assert u['size'] >= e['lower'], 'upper bound below the proved lower bound: %r' % (u,)
                    d['size'] = u['size']; d['witness'] = u['witness']; d['how'] = u.get('how', 'external upper bound')
                    if u['size'] == e['lower']: d['exact'] = True     # found a circuit at the proved lower bound
            if d['witness'] is not None and do_check:
                sp = os.path.join(tmp, 's.spec'); ck = os.path.join(tmp, 'c.ckt')
                open(sp, 'w').write(spec_text(n, m, enc, x['rows'])); open(ck, 'w').write(d['witness'])
                r = subprocess.run([CKTCHECK, sp, ck, '--basis', basis, '--max', str(d['size']), '-q'])
                if r.returncode != 0:
                    sys.exit('cktcheck FAILED: class %d rows %r basis %s' % (x['cls'], x['rows'], basis))
                ngates = sum(1 for l in d['witness'].split('\n') if l.split()[:1] and l.split()[0] in ('and', 'or', 'not'))
                assert ngates == d['size']
                nchecked += 1
            c[key] = d
        classes.append(c)
    if plain:        # encoder table: also record the plain star sizes of the same labelled graph
        pm = open(plain[0], 'rb').read(); pn = open(plain[1], 'rb').read()
        assert len(pm) == len(pn) == 1 << (n * m)
        for c, x in zip(classes, A):
            assert pm[x['f']] != 255 and pn[x['f']] != 255
            c['star_mono'] = pm[x['f']]; c['star_not'] = pn[x['f']]
            for key, sk in (('mono', 'star_mono'), ('not', 'star_not')):
                if c[key]['exact']: assert c[key]['size'] <= c[sk], 'encoder wires made a graph more expensive?'
    # ---------------------------------------------------------------- sanity
    for c in classes:
        assert classes[c['complement']]['complement'] == c['id'], 'complement is not an involution on classes'
        mo, no = c['mono'], c['not']
        if mo['exact'] and no['exact']: assert no['size'] <= mo['size'], 'NOT size above monotone size: %r' % c
        lo_m = mo['size'] if mo['exact'] else mo['lower']
        hi_n = no['size'] if no['size'] is not None else None
        if not no['exact'] and mo['size'] is not None and (no['size'] is None or no['size'] > mo['size']):
            no['size'] = mo['size']; no['witness'] = mo['witness']       # a monotone circuit is a FanInTwo circuit
            no['note'] = 'upper bound copied from the monotone entry'
            if no['size'] == no['lower']: no['exact'] = True
    # ---------------------------------------------------------------- summary
    def lo(e): return e['size'] if e['exact'] else e['lower']
    def hi(e): return e['size'] if e['size'] is not None else None
    S = {}
    for key in ('mono', 'not'):
        hc = collections.Counter(); hl = collections.Counter(); un = 0; unl = 0
        for c in classes:
            if c[key]['exact']: hc[c[key]['size']] += 1; hl[c[key]['size']] += c['orbit_size']
            else: un += 1; unl += c['orbit_size']
        S[key + '_hist_classes'] = {str(k): hc[k] for k in sorted(hc)}
        S[key + '_hist_labelled'] = {str(k): hl[k] for k in sorted(hl)}
        S[key + '_not_exact_classes'] = un
        S[key + '_not_exact_labelled'] = unl
    # NOT saving: conjecture mono <= not + 2n-5
    bound = 2 * n - 5
    sh = collections.Counter(); best = -1; ext = []; viol = []; open_ = 0
    for c in classes:
        mo, no = c['mono'], c['not']
        if mo['exact'] and no['exact']:
            d = mo['size'] - no['size']; sh[d] += 1
            if d > best: best = d; ext = []
            if d == best: ext.append(dict(rows=c['rows'], mono=mo['size'], **{'not': no['size']}))
        else:
            open_ += 1
        if hi(no) is not None and lo(mo) - hi(no) > bound:
            viol.append(dict(rows=c['rows'], mono_lower=lo(mo), not_upper=hi(no)))
    # classes where the bounds do not yet decide the conjecture: (best mono circuit) - (proved NOT lower bound) > bound
    und = [dict(rows=c['rows'], mono=[lo(c['mono']), hi(c['mono'])], **{'not': [lo(c['not']), hi(c['not'])]})
           for c in classes if not (c['mono']['exact'] and c['not']['exact'])
           and (hi(c['mono']) is None or hi(c['mono']) - lo(c['not']) > bound)]
    S['not_saving'] = dict(conjectured_bound=bound, statement='mono(G) <= not(G) + 2n-5',
                           hist={str(k): sh[k] for k in sorted(sh)}, max=best, extremal=ext[:40],
                           num_extremal=len(ext), classes_not_both_exact=open_, proven_violations=viol,
                           undecided_by_bounds=und,
                           holds=(False if (viol or best > bound) else True if not und else None))
    # complement gap: conjecture |mono(G) - mono(co-G)| <= 2n-4
    cb = 2 * n - 4
    gh = collections.Counter(); gbest = -1; gext = []; gviol = []; gopen = 0; gposs = []; gund = []
    for c in classes:
        d = classes[c['complement']]
        if d['id'] < c['id']: continue
        a_, b_ = c['mono'], d['mono']
        if a_['exact'] and b_['exact']:
            g = abs(a_['size'] - b_['size']); gh[g] += 1
            if g > gbest: gbest = g; gext = []
            if g == gbest:
                big, small = (c, d) if a_['size'] >= b_['size'] else (d, c)
                gext.append(dict(rows=big['rows'], size=big['mono']['size'], complement_rows=small['rows'], complement_size=small['mono']['size']))
        else:
            gopen += 1
            # proven part of the gap, and the largest gap the bounds still allow
            pl = max(lo(a_) - (hi(b_) if hi(b_) is not None else 10 ** 9), lo(b_) - (hi(a_) if hi(a_) is not None else 10 ** 9))
            if pl > cb: gviol.append(dict(rows=c['rows'], complement_rows=d['rows'], proven_gap=pl))
            e_ = dict(rows=c['rows'], complement_rows=d['rows'], mono=[lo(a_), hi(a_)], complement_mono=[lo(b_), hi(b_)])
            gposs.append(e_)
            if hi(a_) is None or hi(b_) is None or max(hi(a_) - lo(b_), hi(b_) - lo(a_)) > cb: gund.append(e_)
    S_gap = dict(conjectured_bound=cb, statement='|mono(G) - mono(complement of G)| <= 2n-4',
                 hist_pairs={str(k): gh[k] for k in sorted(gh)}, max_gap_exact_pairs=gbest, extremal_pairs=gext[:60],
                 num_extremal_pairs=len(gext), pairs_not_both_exact=gopen, proven_violations=gviol,
                 undecided_by_bounds=gund,
                 holds=(False if (gviol or gbest > cb) else True if not gund else None))
    if gopen:
        S_gap['note'] = ('%d complement pairs have an entry that is only bounded ([lower, best-found], listed in "open_pairs"); '
                         '"max_gap_exact_pairs" is over the pairs with both sizes exact. "holds" is true when no pair is violated '
                         'and, for every pair that is not exact, (best circuit of one) - (proved lower bound of the other) <= bound '
                         'both ways ("undecided_by_bounds" empty), which proves the bound for every graph of this size.' % gopen)
        S_gap['open_pairs'] = gposs
    if plain:
        for key, sk in (('mono', 'star_mono'), ('not', 'star_not')):
            dh = collections.Counter(); dl = collections.Counter(); joint = collections.Counter()
            for c in classes:
                if not c[key]['exact']: continue
                d = c[sk] - c[key]['size']; dh[d] += 1; dl[d] += c['orbit_size']; joint[(c[sk], c[key]['size'])] += c['orbit_size']
            S['encoder_saving_' + key] = dict(
                meaning='(size with the stars only) - (size with the free encoder wires), same labelled graph',
                hist_classes={str(k): dh[k] for k in sorted(dh)}, hist_labelled={str(k): dl[k] for k in sorted(dl)},
                joint_labelled={'%d,%d' % k: joint[k] for k in sorted(joint)},
                mean_star_labelled=sum(k[0] * v for k, v in joint.items()) / sum(joint.values()),
                mean_enc_labelled=sum(k[1] * v for k, v in joint.items()) / sum(joint.values()))
    names = hA['input_names']
    kind = ('the %d stars (wires 0..%d: left/row vertices, then right/column vertices)' % (n + m, n + m - 1))
    if enc:
        kind += (' PLUS the free encoder wires %s (wire order as listed in "inputs": for each row-index bit i the set '
                 '{u : bit_i(u) = 0} then {u : bit_i(u) = 1}, then the same for the column index)' % ', '.join(names[n + m:]))
    T = dict(
        n=n, m=m, encoder=bool(enc),
        semantics=('Exact least number of gates of a circuit that is right on the n*m inputs with exactly one row wire and one '
                   'column wire on (Lean: PEqualNP.Represents.Represents). "mono": AND/OR gates of fan-in at most two '
                   '(Monotone2, RepSizeAtMost). "not": AND/OR/NOT gates, NOT counted (FanInTwo). Constants cost a gate, a missing '
                   'wire reads false, the output may be an input wire or a missing wire. Inputs: ' + kind + '. '
                   'Witnesses are .ckt texts (toolkit/FORMAT.md). "exact": true means every smaller size was refuted exhaustively in the '
                   'full model; otherwise "lower" is the proved lower bound and "size" the best circuit found (or null).'),
        inputs=names,
        symmetry=(('index-bit permutations and complementations on each side' if enc else 'row permutations, column permutations')
                  + (', and transpose' if hA['transpose'] else '') + ' (group order %d)' % hA['group']),
        group_order=hA['group'],
        rows_convention='bit v of rows[u] = A u v; the class representative is the member with the least value of sum_u rows[u] * 2^(m*u)',
        num_classes=len(classes),
        last_complete_pass={'mono': hA['last_complete_pass'], 'not': hB['last_complete_pass']},
        summary=S, complement_gap=S_gap, classes=classes)
    json.dump(T, open(pos[2], 'w'), separators=(',', ':'))
    print('wrote %s: %d classes, %d witnesses checked with bin/cktcheck' % (pos[2], len(classes), nchecked), file=sys.stderr)
    if md:
        print('### %dx%d%s' % (n, m, ' with free encoder wires' if enc else ''))
        print('classes: %d (%s); labelled graphs: %d' % (len(classes), T['symmetry'], 2 ** (n * m)))
        for key, nm in (('mono', 'mono (AND/OR)'), ('not', 'with NOT')):
            print('- %s size histogram, classes: %s%s' % (nm, ' '.join('%s:%s' % kv for kv in S[key + '_hist_classes'].items()),
                  (' ; not exact: %d' % S[key + '_not_exact_classes']) if S[key + '_not_exact_classes'] else ''))
            print('- %s size histogram, labelled graphs: %s' % (nm, ' '.join('%s:%s' % kv for kv in S[key + '_hist_labelled'].items())))
        ns = S['not_saving']
        print('- mono - not histogram (classes with both exact): %s ; max %d against 2n-5 = %d ; proven violations: %d ; classes not both exact: %d, undecided by the bounds: %d ; holds for every graph of this size: %s (None = not decided yet)'
              % (' '.join('%s:%s' % kv for kv in ns['hist'].items()), ns['max'], bound, len(ns['proven_violations']), ns['classes_not_both_exact'], len(ns['undecided_by_bounds']), ns['holds']))
        if plain:
            for key in ('mono', 'not'):
                es = S['encoder_saving_' + key]
                print('- %s: (stars only) - (with encoder wires), labelled graphs: %s ; mean size %.3f -> %.3f'
                      % (key, ' '.join('%s:%s' % kv for kv in es['hist_labelled'].items()), es['mean_star_labelled'], es['mean_enc_labelled']))
        print('- complement gap histogram (pairs with both exact): %s ; max %d against 2n-4 = %d ; proven violations: %d ; pairs not both exact: %d, undecided by the bounds: %d ; holds for every graph of this size: %s (None = not decided yet)'
              % (' '.join('%s:%s' % kv for kv in S_gap['hist_pairs'].items()), gbest, cb, len(gviol), gopen, len(gund), S_gap['holds']))


if __name__ == '__main__':
    main()
