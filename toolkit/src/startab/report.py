#!/usr/bin/env python3
"""report.py -- print the results section of docs/startab.md from the tables (markdown on stdout).

    python3 src/startab/report.py [tables_dir]
"""
import json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'tables')


def load(name):
    p = os.path.join(TD, name)
    return json.load(open(p)) if os.path.exists(p) else None


def hist(d):
    return ' '.join('%s:%s' % kv for kv in d.items())


def rng(e):
    if e['exact']: return str(e['size'])
    return '[%d, %s]' % (e['lower'], e['size'] if e['size'] is not None else '?')


def star(T):
    n = T['n']; S = T['summary']; C = T['classes']
    print('### %dx%d  (`tables/star_%d.json`)\n' % (n, n, n))
    print('%d classes up to %s; %d labelled graphs. Last complete pass: mono %d, NOT %d.\n'
          % (len(C), T['symmetry'], 2 ** (n * n), T['last_complete_pass']['mono'], T['last_complete_pass']['not']))
    for key, nm in (('mono', 'mono'), ('not', 'NOT ')):
        ne = S[key + '_not_exact_classes']
        print('* %s exact sizes, classes: `%s`%s' % (nm, hist(S[key + '_hist_classes']),
              ('  — plus %d classes (%d labelled graphs) with bounds only' % (ne, S[key + '_not_exact_labelled'])) if ne else ''))
        print('* %s exact sizes, labelled graphs: `%s`' % (nm, hist(S[key + '_hist_labelled'])))
    if any(not c['mono']['exact'] for c in C) or any(not c['not']['exact'] for c in C):
        for key in ('mono', 'not'):
            g = {}
            for c in C:
                e = c[key]
                if not e['exact']: g[(e['lower'], e['size'])] = g.get((e['lower'], e['size']), 0) + 1
            print('* %s entries that are NOT exact, as [proved lower bound, best circuit found]: %s'
                  % (key, ', '.join('[%d,%s] x%d' % (k[0], k[1], v) for k, v in sorted(g.items()))))
    ns = S['not_saving']
    print('* **NOT saving** `mono - not` (classes with both exact): `%s`. Maximum **%d**, conjectured bound 2n-5 = **%d**. '
          'Proven violations: **%d**. Classes not both exact: %d, of which the bounds leave %d undecided. Verdict for every graph of this size: **%s**.'
          % (hist(ns['hist']), ns['max'], ns['conjectured_bound'], len(ns['proven_violations']), ns['classes_not_both_exact'],
             len(ns.get('undecided_by_bounds', [])), {True: 'holds', False: 'VIOLATED', None: 'not decided'}[ns.get('holds')]))
    print('  Extremal classes (rows: mono / not): ' + '; '.join('%s: %d / %d' % (e['rows'], e['mono'], e['not']) for e in ns['extremal'][:14])
          + (' ... (%d in all)' % ns['num_extremal'] if ns['num_extremal'] > 14 else ''))
    for e in ns.get('undecided_by_bounds', []):
        print('  - undecided: rows %s mono in %s, not in %s' % (e['rows'], e['mono'], e['not']))
    for e in ns['proven_violations']:
        print('  - **VIOLATION**: %s' % e)
    g = T['complement_gap']
    print('* **Complement gap** `|mono(G) - mono(co-G)|` (pairs with both exact): `%s`. Maximum **%d**, conjectured bound 2n-4 = **%d**. '
          'Proven violations: **%d**. Pairs not both exact: %d, of which the bounds leave %d undecided. Verdict for every graph of this size: **%s**.'
          % (hist(g['hist_pairs']), g['max_gap_exact_pairs'], g['conjectured_bound'], len(g['proven_violations']), g['pairs_not_both_exact'],
             len(g.get('undecided_by_bounds', [])), {True: 'holds', False: 'VIOLATED', None: 'not decided'}[g.get('holds')]))
    print('  Extremal pairs (rows of G: size / rows of the complement: size): '
          + '; '.join('%s: %d / %s: %d' % (e['rows'], e['size'], e['complement_rows'], e['complement_size']) for e in g['extremal_pairs'][:12])
          + (' ... (%d in all)' % g['num_extremal_pairs'] if g['num_extremal_pairs'] > 12 else ''))
    for e in g.get('undecided_by_bounds', []):
        print('  - undecided: rows %s mono in %s, complement %s mono in %s' % (e['rows'], e['mono'], e['complement_rows'], e['complement_mono']))
    for e in g['proven_violations']:
        print('  - **VIOLATION**: %s' % e)
    # named graphs
    crown = [((1 << n) - 1) ^ (1 << u) for u in range(n)]
    ident = [1 << u for u in range(n)]
    idx = {tuple(sorted(c['rows'])): c for c in C}
    def find(rows):
        return idx.get(tuple(sorted(rows)))
    for nm, rows in (('crown (u != v)', crown), ('perfect matching (u = v)', ident)):
        c = find(rows)
        if c: print('* %s, rows %s: mono %s, not %s' % (nm, c['rows'], rng(c['mono']), rng(c['not'])))
    top = sorted(C, key=lambda c: -(c['mono']['size'] if c['mono']['exact'] else -1))[:6]
    print('* largest exact mono sizes: ' + '; '.join('%s: %d (not %s)' % (c['rows'], c['mono']['size'], rng(c['not'])) for c in top))
    top = sorted(C, key=lambda c: -(c['not']['size'] if c['not']['exact'] else -1))[:6]
    print('* largest exact NOT sizes: ' + '; '.join('%s: %d (mono %s)' % (c['rows'], c['not']['size'], rng(c['mono'])) for c in top))
    print()


def main():
    for n in (3, 4, 5):
        T = load('star_%d.json' % n)
        if T: star(T)
    E = load('star_4_enc.json')
    if E:
        S = E['summary']; C = E['classes']
        print('### 4x4 with free encoder wires  (`tables/star_4_enc.json`)\n')
        print('%d classes up to %s; all exact in both bases.\n' % (len(C), E['symmetry']))
        for key, nm in (('mono', 'mono'), ('not', 'NOT ')):
            print('* %s sizes with encoder wires, classes: `%s`; labelled graphs: `%s`' % (nm, hist(S[key + '_hist_classes']), hist(S[key + '_hist_labelled'])))
            es = S['encoder_saving_' + key]
            print('* %s: (stars only) - (with encoder wires), labelled graphs: `%s`; mean size %.3f -> %.3f' % (nm, hist(es['hist_labelled']), es['mean_star_labelled'], es['mean_enc_labelled']))
        top = sorted(C, key=lambda c: -(c['star_mono'] - c['mono']['size']))[:5]
        print('* largest encoder saving (mono): ' + '; '.join('%s: %d -> %d' % (c['rows'], c['star_mono'], c['mono']['size']) for c in top))
        top = sorted(C, key=lambda c: -c['mono']['size'])[:5]
        print('* hardest with encoder wires (mono): ' + '; '.join('%s: %d (stars only %d)' % (c['rows'], c['mono']['size'], c['star_mono']) for c in top))
        print()
    E8 = load('star_8_enc_sample.json')
    if E8:
        print('### 8x8 with free encoder wires, sample  (`tables/star_8_enc_sample.json`)\n')
        print('| graph | mono | NOT | note |')
        print('|---|---|---|---|')
        for c in E8['classes']:
            def cell(e):
                if e is None: return '-'
                if e['exact']: return '**%d**' % e['size']
                return '[%d, %s]' % (e['lower'], e['size'] if e['size'] is not None else '?')
            print('| %s | %s | %s | %s |' % (c['name'], cell(c.get('mono')), cell(c.get('not')), c['note']))
        print('\nBold = exact (every smaller size refuted by SAT, or lower bound met); `[L, U]` = proved lower bound and best circuit found.\n')


if __name__ == '__main__':
    main()
