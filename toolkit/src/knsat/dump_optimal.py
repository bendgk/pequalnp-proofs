"""dump_optimal.py N S OUT.json [CAP] — all optimal circuits for K(N) (size S) up to isomorphism, with structure flags.
Enumerates every solution of the canonical-order CNF (kn_elim.build without elimination clauses), groups them by
full canonical form (input relabelling x gate reordering), and writes one representative per class."""
import sys, os, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kn_elim, kn_cubes
from pysat.solvers import Cadical195
n, s, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
cap = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 7
E = kn_elim.build(n, s)
S = Cadical195(bootstrap_with=E['cl'])
sel = [x for i in range(s) for x in E['a'][i] + E['b'][i]] + E['t']
classes = {}; nsol = 0
while nsol < cap and S.solve():
    mdl = S.get_model(); m = set(x for x in mdl if x > 0)
    g = kn_elim.decode(E, mdl, n, s); assert kn_elim.check(g, n)
    nsol += 1
    cube = tuple((a, b, 1 if op == 'and' else 0) for op, a, b in g)
    classes.setdefault(tuple(kn_cubes.canon(n, cube)), g)
    S.add_clause([-x if x in m else x for x in sel])
complete = nsol < cap
rows = []
for key, g in sorted(classes.items()):
    andd = [0] * n; fan = [0] * (n + s)
    for op, a, b in g:
        andd.append(max(andd[a], andd[b]) + (op == 'and')); fan[a] += 1; fan[b] += 1
    rows.append(dict(gates=[[op, a, b] for op, a, b in g], ands=sum(op == 'and' for op, _, _ in g), ors=sum(op == 'or' for op, _, _ in g),
                     and_depth=andd[-1], single_level=andd[-1] <= 1, input_fanouts=fan[:n], max_gate_fanout=max(fan[n:]),
                     ckt=f"inputs {n}\n" + ''.join(f"{op} {a} {b}\n" for op, a, b in g) + f"out {n + s - 1}\n"))
summary = dict(n=n, size=s, cnf_solutions=nsol, complete=complete, classes=len(rows),
               single_level=sum(r['single_level'] for r in rows),
               by_and_count=dict(collections.Counter(r['ands'] for r in rows)),
               by_and_depth=dict(collections.Counter(r['and_depth'] for r in rows)),
               by_input_fanout_multiset=dict(collections.Counter(str(sorted(r['input_fanouts'])) for r in rows)))
json.dump(dict(summary=summary, note="K(n) = monotone fan-in-2 AND/OR circuits, 0 on 1-hot, 1 on 2-hot points (= threshold-2). "
               "single_level: every input-to-output path passes through at most one AND gate. One representative per class "
               "under input relabelling and gate reordering.", circuits=rows), open(out, 'w'), indent=0)
print(json.dumps(summary))
