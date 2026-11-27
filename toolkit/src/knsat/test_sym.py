"""test_sym.py — soundness tests for the cube filter (sym) and for F6.  Run: satpy test_sym.py
For kn4 s=7 and kn5 s=10 (SAT instances) enumerate ALL solutions of the CNF (which already has G, F, tie-break),
group them into isomorphism classes (full-circuit canonical form), and check that every class contains a solution whose
D-gate prefix passes is_canonical, for D = 1..4.  Also check claim F6 on every solution:
an AND gate that is the ONLY reader of input j has its other operand true at every other 1-hot point."""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kn_elim, kn_cubes
from pysat.solvers import Cadical195

for n, s, cap in ((4, 7, 10 ** 6), (5, 10, 60000)):
    E = kn_elim.build(n, s)
    S = Cadical195(bootstrap_with=E['cl'])
    sols = []
    sel = [x for i in range(s) for x in E['a'][i] + E['b'][i]] + E['t']
    while len(sols) < cap and S.solve():
        m = set(x for x in S.get_model() if x > 0)
        g = kn_elim.decode(E, S.get_model(), n, s)
        assert kn_elim.check(g, n)
        sols.append(g)
        S.add_clause([-x if x in m else x for x in sel])
    complete = len(sols) < cap
    S.delete()
    classes = collections.defaultdict(list)
    for g in sols:
        cube = tuple((a, b, 1 if op == 'and' else 0) for op, a, b in g)
        classes[tuple(kn_cubes.canon(n, cube))].append(cube)
    print(f"kn{n} s={s}: {len(sols)} CNF solutions ({'all' if complete else 'capped'}), {len(classes)} isomorphism classes")
    if complete:
        for D in (1, 2, 3, 4):
            bad = [c for c, members in classes.items() if not any(kn_cubes.is_canonical(n, m[:D]) for m in members)]
            kept = sum(1 for members in classes.values() for m in members if kn_cubes.is_canonical(n, m[:D]))
            print(f"   D={D}: classes with no solution passing the prefix filter: {len(bad)}   (solutions passing: {kept}/{len(sols)})")
            assert not bad, "SYM FILTER UNSOUND"
        # the lex-min member of each class must itself be a CNF solution (G, F, tie-break are necessary conditions)
        missing = [c for c, members in classes.items() if tuple((a, b, t) for (b, a, t) in c) not in set(members)]
        print(f"   classes whose lex-min member is not a CNF solution: {len(missing)}")
        assert not missing, "G/F/tie-break are not implied by lex-min"
    # F6
    pts, _ = kn_elim.kn_points(n)
    chk = 0
    for g in sols:
        cols = [[p[j] for p in pts] for j in range(n)]
        for op, a, b in g:
            cols.append([(x & y) if op == 'and' else (x | y) for x, y in zip(cols[a], cols[b])])
        for j in range(n):
            R = [i for i, (op, a, b) in enumerate(g) if j in (a, b)]
            if len(R) == 1 and g[R[0]][0] == 'and':
                op, a, b = g[R[0]]; h = b if a == j else a
                assert all(cols[h][y] == 1 for y in range(n) if y != j), ("F6 FAILS", g, j)
                chk += 1
    print(f"   F6 held in all {chk} applicable (solution, input) cases")
    # F7 / F8 (the --extra clauses)
    c7 = c8 = 0
    for g in sols:
        cols = [[p[j] for p in pts] for j in range(n)]
        for op, a, b in g:
            cols.append([(x & y) if op == 'and' else (x | y) for x, y in zip(cols[a], cols[b])])
        for j in range(n):
            R = [i for i, (op, a, b) in enumerate(g) if j in (a, b)]
            oth = [(g[i][2] if g[i][1] == j else g[i][1]) for i in R]
            if len(R) == 1 and g[R[0]][0] == 'or':
                assert all(cols[oth[0]][y] == 0 for y in range(n) if y != j), ("F7 FAILS", g, j); c7 += 1
            if len(R) == 2 and all(g[i][0] == 'or' for i in R):
                assert all(not (cols[oth[0]][y] and cols[oth[1]][y]) for y in range(n) if y != j), ("F8 FAILS", g, j); c8 += 1
    print(f"   F7 held in all {c7} cases, F8 held in all {c8} cases")
