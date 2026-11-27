#!/usr/bin/env python3
"""mktable.py -- turn an andtab run (JSONL) into tables/and_N.json, aligned class by class with tables/star_N.json.

    python3 src/andtab/mktable.py RUN.jsonl tables/star_N.json tables/and_N.json [--md] [--no-cktcheck]

For every class: the witness (L, R, out) is re-evaluated here in Python (andlib.eval_wit, independent of the C++),
expanded to a .ckt, and the .ckt is checked with bin/cktcheck --basis ao against a generated graph spec; the
number of `and` lines of the .ckt must equal the tabulated And.  Sanity checks done here and refused on failure:
  ids / rows / orbit sizes / complement ids equal the star table's;  And <= number of AND gates of the star
  table's monotone witness;  And = 0 exactly for unions of rows and columns;  And <= number of row types and
  <= number of column types;  And >= ceil(log2 cov0) (Lemma 4 of docs/andtab.md).
"""
import collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andlib


def main():
    a = sys.argv[1:]
    md = '--md' in a; do_check = '--no-cktcheck' not in a
    pos = [x for x in a if not x.startswith('--')]
    if len(pos) != 3:
        sys.exit(__doc__)
    lines = [json.loads(l) for l in open(pos[0])]
    hdr, run = lines[0], lines[1:]
    star = json.load(open(pos[1]))
    n, m = hdr['n'], hdr['m']
    assert (star['n'], star['m']) == (n, m) and not star['encoder']
    assert len(run) == hdr['classes'] == star['num_classes'], 'class counts differ from the star table'
    assert hdr['group'] == star['group_order']
    G = andlib.gens(n, m)
    full = (1 << (n * m)) - 1
    level0 = set()
    for R in range(1 << n):
        for C in range(1 << m):
            s = 0
            for u in range(n):
                if (R >> u) & 1: s |= G[u]
            for v in range(m):
                if (C >> v) & 1: s |= G[n + v]
            level0.add(s)
    classes = []; nchecked = 0
    for e, sc in zip(run, star['classes']):
        assert e['cls'] == sc['id'] and e['rows'] == sc['rows'] and e['orbit'] == sc['orbit_size'] and e['ccls'] == sc['complement'], \
            'class %d does not line up with the star table' % e['cls']
        T = andlib.rows_to_mask(e['rows'], m)
        assert T == e['f']
        assert e['and'] is not None
        L, R, out = e['L'], e['R'], e['out']
        assert len(L) == len(R) == e['and']
        assert andlib.eval_wit(n, m, L, R, out) == T, 'witness of class %d does not compute the graph' % e['cls']
        ckt, n_and, n_or = andlib.wit_to_ckt(n, m, L, R, out)
        assert n_and == e['and'] == andlib.ckt_and_count(ckt)
        if do_check:
            if not andlib.cktcheck(andlib.graph_spec(n, m, e['rows']), ckt, 'ao', n_and + n_or):
                sys.exit('cktcheck FAILED for class %d rows %r' % (e['cls'], e['rows']))
            nchecked += 1
        # sanity
        assert (e['and'] == 0) == (T in level0), 'And = 0 must be exactly the unions of rows and columns'
        rt, ct = andlib.type_counts(n, m, T)
        assert e['and'] <= min(rt, ct), 'And above the row-type / column-type bound'
        c0 = andlib.cov0(n, m, T)
        lb = andlib.ceil_log2(c0)
        assert e['and'] >= lb, 'And below the cover lower bound?!'
        sm = sc['mono']
        star_ands = andlib.ckt_and_count(sm['witness']) if sm.get('witness') else None
        if star_ands is not None and not (T == full):
            # the star table's circuit for the complete graph is the constant gate `and` (no inputs); skip that one
            assert e['and'] <= star_ands, 'And above the AND count of the star witness (class %d)' % e['cls']
        d = dict(id=e['cls'], rows=e['rows'], orbit_size=e['orbit'], complement=e['ccls'])
        d['and'] = dict(size=e['and'], exact=bool(e['exact']), lower=e['lower'],
                        witness=dict(L=L, R=R, out=out), ckt=ckt, ckt_gates=n_and + n_or, ckt_ands=n_and)
        d['star_mono'] = sm['size'] if sm['exact'] else None
        d['star_mono_lower'] = sm['size'] if sm['exact'] else sm.get('lower')
        d['star_mono_ands'] = star_ands
        d['cov0'] = c0; d['lb_cov'] = lb; d['row_types'] = rt; d['col_types'] = ct
        classes.append(d)
    for c in classes:
        assert classes[c['complement']]['complement'] == c['id']
    # ---------------------------------------------------------------- summary
    hc = collections.Counter(); hl = collections.Counter(); notexact = 0
    for c in classes:
        if c['and']['exact']:
            hc[c['and']['size']] += 1; hl[c['and']['size']] += c['orbit_size']
        else:
            notexact += 1
    assert sum(c['orbit_size'] for c in classes) == 1 << (n * m)
    mx = max(hc)
    ext = [dict(id=c['id'], rows=c['rows'], orbit_size=c['orbit_size'], star_mono=c['star_mono'], complement=c['complement'],
                complement_and=classes[c['complement']]['and']['size'])
           for c in classes if c['and']['exact'] and c['and']['size'] == mx]
    joint = collections.Counter(); slack_lb = collections.Counter(); slack_star = collections.Counter(); slack_type = collections.Counter()
    for c in classes:
        if c['star_mono'] is not None:
            joint[(c['and']['size'], c['star_mono'])] += 1
        slack_lb[c['and']['size'] - c['lb_cov']] += 1
        if c['star_mono_ands'] is not None and c['id'] != len(classes) - 1:
            slack_star[c['star_mono_ands'] - c['and']['size']] += 1
        slack_type[min(c['row_types'], c['col_types']) - c['and']['size']] += 1
    gap = collections.Counter(); gbest = -1; gext = []
    for c in classes:
        d = classes[c['complement']]
        if d['id'] < c['id']:
            continue
        g = abs(c['and']['size'] - d['and']['size']); gap[g] += 1
        if g > gbest:
            gbest = g; gext = []
        if g == gbest:
            big, small = (c, d) if c['and']['size'] >= d['and']['size'] else (d, c)
            gext.append(dict(rows=big['rows'], **{'and': big['and']['size']}, complement_rows=small['rows'], complement_and=small['and']['size']))
    S = dict(
        and_hist_classes={str(k): hc[k] for k in sorted(hc)},
        and_hist_labelled={str(k): hl[k] for k in sorted(hl)},
        not_exact_classes=notexact,
        mean_and_labelled=sum(k * v for k, v in hl.items()) / sum(hl.values()),
        max=mx, num_extremal=len(ext), extremal=ext[:60],
        joint_and_vs_star_mono_classes={'%d,%d' % k: joint[k] for k in sorted(joint)},
        and_minus_lb_cov_hist_classes={str(k): slack_lb[k] for k in sorted(slack_lb)},
        star_witness_ands_minus_and_hist_classes={str(k): slack_star[k] for k in sorted(slack_star)},
        min_types_minus_and_hist_classes={str(k): slack_type[k] for k in sorted(slack_type)},
        complement_gap=dict(statement='|And(G) - And(complement of G)|', hist_pairs={str(k): gap[k] for k in sorted(gap)},
                            max=gbest, num_extremal_pairs=len(gext), extremal_pairs=gext[:40]))
    T = dict(
        n=n, m=m,
        quantity=('And(A) = least number of AND gates of a circuit of AND and OR gates (fan-in at most two, any number of OR gates) '
                  'that is right on the n*m inputs with exactly one row wire and one column wire on (Lean: Monotone2 + '
                  'PEqualNP.Represents.Represents; same inputs and points as tables/star_%d.json). Only AND gates are counted.' % n),
        conventions=('empty OR = empty set (a wire that does not exist reads false); empty graph: And 0; a union of full rows and '
                     'columns: And 0; complete graph: And 0 (union of all rows; the star table counts 1 there for the constant gate). '
                     'An AND gate with fewer than two inputs is a constant or a copy and never needed.'),
        witness_format=('"witness": {"L": [...], "R": [...], "out": [...]}: AND gate j = (OR of generators L[j]) AND (OR of generators R[j]); '
                        'the output is the OR of the generators in "out". Generator index i: 0..n-1 = row (left vertex) i, '
                        'n..n+m-1 = column (right vertex) i-n, n+m+k = AND gate k. "ckt" is the same circuit expanded into a '
                        '.ckt (toolkit/FORMAT.md; basis ao, ORs of fan-in two); it passes bin/cktcheck --basis ao; "ckt_ands" = number of and lines = And.'),
        inputs=star['inputs'], symmetry=star['symmetry'], group_order=star['group_order'],
        rows_convention=star['rows_convention'], num_classes=len(classes),
        last_complete_level=hdr['last_complete_level'],
        exactness=('"exact": true means: a circuit with "size" AND gates is stored, and "size"-1 AND gates were refuted by the '
                   'exhaustive level enumeration of bin/andtab (levels 0..%d complete; docs/andtab.md section 3).' % hdr['last_complete_level']),
        extra_fields=('star_mono = exact gate count from tables/star_%d.json (null if not exact there; star_mono_lower then); '
                      'star_mono_ands = AND gates in that table\'s witness (an upper bound on And); cov0 = least number of '
                      'all-zero rectangles covering the zeros of the graph; lb_cov = ceil(log2 cov0) <= And; '
                      'row_types / col_types = number of distinct row / column types that are neither empty nor full (>= And).' % n),
        run=hdr, summary=S, classes=classes)
    json.dump(T, open(pos[2], 'w'), separators=(',', ':'))
    print('wrote %s: %d classes, %d witnesses checked with bin/cktcheck' % (pos[2], len(classes), nchecked), file=sys.stderr)
    if md:
        print('### %dx%d' % (n, m))
        print('- classes: %d (%s); labelled graphs: %d' % (len(classes), star['symmetry'], 2 ** (n * m)))
        print('- And histogram, classes: %s' % ' '.join('%s:%s' % kv for kv in S['and_hist_classes'].items()))
        print('- And histogram, labelled graphs: %s (mean %.4f)' % (' '.join('%s:%s' % kv for kv in S['and_hist_labelled'].items()), S['mean_and_labelled']))
        print('- maximum: %d, attained by %d classes' % (mx, len(ext)))
        print('- And - ceil(log2 cov0), classes: %s' % ' '.join('%s:%s' % kv for kv in S['and_minus_lb_cov_hist_classes'].items()))
        print('- (AND gates of the star-table witness) - And, classes: %s' % ' '.join('%s:%s' % kv for kv in S['star_witness_ands_minus_and_hist_classes'].items()))
        print('- min(row types, column types) - And, classes: %s' % ' '.join('%s:%s' % kv for kv in S['min_types_minus_and_hist_classes'].items()))
        print('- |And(G) - And(co-G)| over complement pairs: %s' % ' '.join('%s:%s' % kv for kv in S['complement_gap']['hist_pairs'].items()))
        print('- joint (And, star mono size) class counts: %s' % ' '.join('%s:%s' % kv for kv in S['joint_and_vs_star_mono_classes'].items()))


if __name__ == '__main__':
    main()
