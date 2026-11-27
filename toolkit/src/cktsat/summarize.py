"""Markdown table of every finished cktsat run: bin/satpy src/cktsat/summarize.py [runs-dir ...]"""
import glob, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
dirs = sys.argv[1:] or [(os.environ.get('PNP_RUNS') or os.path.join(ROOT, 'runs'))]
rows = []
for d in dirs:
    for f in sorted(glob.glob(os.path.join(d, 'cktsat_*.json'))):
        try:
            m = json.load(open(f))['meta']
        except Exception:
            continue
        sm = m.get('summary', {})
        el = m.get('elim') or {}
        elim = 'yes' if el.get('max_vanishing') else 'no'
        scope = ' '.join(x for x in [('shard ' + m['shard']) if m.get('shard') else '', ('first=' + m['first']) if m.get('first') else '',
                                     'no-sym' if m.get('no_sym') else ''] if x)
        rows.append((m['spec'].replace('.spec', ''), m['basis'], m['s'], sm.get('result', '?'), scope, elim, m.get('solver', ''),
                     sm.get('roots', 0), sm.get('cubes', 0), sm.get('split', 0), sm.get('cpu', 0), sm.get('wall', 0), sm.get('workers', 0),
                     os.path.relpath(f, ROOT)))
print('| spec | basis | s | result | scope | elim | solver | root cubes | cubes | splits | CPU s | wall s | -j | log |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
for r in sorted(rows, key=lambda r: (r[0], r[1], r[2], r[4])):
    print('| ' + ' | '.join(str(x) for x in r) + ' |')
