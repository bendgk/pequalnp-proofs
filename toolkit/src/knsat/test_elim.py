"""test_elim.py — soundness tests for kn_elim.py's constraints.

Test 1 (derivation): for random NORMAL monotone circuits (two distinct earlier operands, every non-output gate read,
all columns on the K(n) points distinct and non-constant), compute e_j = number of gates removed by structural
simplification after x_j := 0, independently, and check:  (all e_j <= 2 and no output collapse)  ==>  F1,F2,F3 hold.
Test 2 (encoding): for random circuit STRUCTURES, the CNF restricted to structure (no target clauses) is satisfiable
under assumptions fixing all selectors  <=>  an independent Python predicate for
"a<b, every gate read, G, F, every input read, F1..F5 (when elim=2), column constraints" holds.
Run:  satpy test_elim.py [seconds]
"""
import itertools, random, sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kn_elim


def columns(n, gates):
    pts, _ = kn_elim.kn_points(n)
    cols = [tuple(p[j] for p in pts) for j in range(n)]
    for op, a, b in gates:
        cols.append(tuple((x & y) if op == 'and' else (x | y) for x, y in zip(cols[a], cols[b])))
    return cols


def removed_when_zero(n, gates, j):
    """Structural simplification with x_j = 0.  Returns (number of removed gates, output_is_zero)."""
    alias = {}                      # wire -> wire it aliases, or 'Z' for constant 0
    alias[j] = 'Z'
    res = lambda w: alias.get(w, w)
    removed = 0
    for i, (op, a, b) in enumerate(gates):
        w = n + i
        A, B = res(a), res(b)
        if A == 'Z' and B == 'Z': alias[w] = 'Z'; removed += 1
        elif A == 'Z' or B == 'Z':
            other = B if A == 'Z' else A
            alias[w] = 'Z' if op == 'and' else other
            removed += 1
        elif A == B: alias[w] = A; removed += 1
    return removed, res(n + len(gates) - 1) == 'Z'


def readers(n, gates, w):
    return [i for i, (op, a, b) in enumerate(gates) if a == w or b == w]


def F123(n, gates):
    s = len(gates)
    for j in range(n):
        R = readers(n, gates, j)
        if len(R) > 2: return False                                   # F1
        if len(R) == 2 and any(gates[i][0] == 'and' for i in R): return False   # F2
        for i in R:
            if gates[i][0] == 'and':                                   # F3
                if i == s - 1: return False
                RR = readers(n, gates, n + i)
                if len(RR) != 1 or gates[RR[0]][0] != 'or': return False
    return True


def F45(n, gates):
    for j in range(n):
        R = readers(n, gates, j)
        for i in R:
            op, a, b = gates[i]
            h = b if a == j else a
            if len(R) == 2 and op == 'or':
                for (op3, a3, b3) in gates[i + 1:]:
                    if {a3, b3} == {h, n + i}: return False            # F4
            if op == 'and':
                for i2 in readers(n, gates, n + i):
                    op2, a2, b2 = gates[i2]
                    if op2 != 'or': continue
                    k = b2 if a2 == n + i else a2
                    for (op3, a3, b3) in gates[i2 + 1:]:
                        if {a3, b3} == {k, n + i2}: return False        # F5
    return True


def G_ok(n, gates):
    for i in range(len(gates) - 1):
        (_, a, b), (_, a2, b2) = gates[i], gates[i + 1]
        if b2 == n + i: continue
        if (b2, a2) < (b, a): return False
        if (b2, a2) == (b, a) and gates[i][0] != 'or': return False    # tie-break: same operands => the first is OR
    return True


def F_ok(n, gates):
    first = [min(readers(n, gates, j), default=10 ** 9) for j in range(n)]
    return all(first[j] <= first[j + 1] for j in range(n - 1)) and all(f < 10 ** 9 for f in first)


def random_circuit(n, s, rng, bias_inputs=True):
    gates = []
    for i in range(s):
        W = n + i
        if bias_inputs and rng.random() < 0.5 and i > 0:
            b = W - 1 if rng.random() < 0.6 else rng.randrange(1, W)
        else:
            b = rng.randrange(1, W)
        a = rng.randrange(b)
        gates.append((rng.choice(['and', 'or']), a, b))
    return gates


def all_read(n, gates):
    s = len(gates)
    return all(readers(n, gates, n + i) for i in range(s - 1))


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 40
    rng = random.Random(12345)
    # ---------------- Test 1
    t0 = time.time(); tried = normal = lowe = 0
    while time.time() - t0 < budget / 2:
        n = rng.choice([3, 4, 5, 6]); s = rng.randrange(n - 1, 3 * n)
        g = random_circuit(n, s, rng)
        tried += 1
        if not all_read(n, g): continue
        cols = columns(n, g)
        if len(set(cols)) != len(cols) or any(len(set(c)) == 1 for c in cols[n:]): continue
        if any(not readers(n, g, j) for j in range(n)): continue
        normal += 1
        es = [removed_when_zero(n, g, j) for j in range(n)]
        if all(e <= 2 and not z for e, z in es):
            lowe += 1
            assert F123(n, g), ("DERIVATION BUG: e<=2 everywhere but F1-F3 fail", n, g, es)
            assert F45(n, g), ("DERIVATION BUG: e<=2 everywhere but F4/F5 fail", n, g, es)
    print(f"test 1: {tried} random circuits, {normal} normal, {lowe} with all e_j <= 2 — F1..F5 held on all of them")
    # ---------------- Test 2
    from pysat.solvers import Cadical195
    t0 = time.time(); stats = {}
    cache = {}
    while time.time() - t0 < budget / 2:
        n = rng.choice([3, 4, 5]); s = rng.randrange(max(2, n - 1), 2 * n + 2); elim = rng.choice([None, 2])
        key = (n, s, elim)
        if key not in cache:
            E = kn_elim.build(n, s, elim=elim, typec=False)   # F6 uses the target, so it is not a structural constraint
            P = len(E['pts'])
            # drop the target clauses (unit clauses on the last gate's value vars) to test structure only
            last = set(E['v'][s - 1])
            cl = [c for c in E['cl'] if not (len(c) == 1 and abs(c[0]) in last)]
            cache[key] = (E, Cadical195(bootstrap_with=cl))
        E, S = cache[key]
        g = random_circuit(n, s, rng)
        # make canonical-ish sometimes so that the positive side is exercised
        ass = []
        for i, (op, a, b) in enumerate(g):
            ass += [E['a'][i][a], E['b'][i][b], E['t'][i] if op == 'and' else -E['t'][i]]
        sat = S.solve(assumptions=ass)
        cols = columns(n, g)
        col_ok = all(len(set(c)) == 2 for c in cols[n:]) and all(c not in cols[:n] for c in cols[n:])
        pred = all_read(n, g) and G_ok(n, g) and F_ok(n, g) and col_ok
        if elim == 2: pred = pred and F123(n, g) and F45(n, g)
        stats[(elim, pred)] = stats.get((elim, pred), 0) + 1
        assert sat == pred, ("ENCODING MISMATCH", key, g, sat, pred)
    print("test 2: CNF == independent predicate on", sum(stats.values()), "random structures;", dict(sorted(stats.items(), key=str)))


if __name__ == '__main__':
    main()
