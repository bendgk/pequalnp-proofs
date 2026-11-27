#!/usr/bin/env python3
"""Independent SAT cross-check of `ptrank exact` (run with bin/satpy; single thread).

Encodes, straight from the definition in tensor form,
    sum_{k<rho} A_k[a,b] B_k[c,d] + sum_{r<R} V_r[a,d] U_r[c,b] = [a=c][b=d]      for all a,b,c,d < n     (over GF(2))
i.e.  A + B^T1 = I with A = sum_k vec(A_k) vec(B_k)^T (rank <= rho) and B = sum_r vec(U_r) vec(V_r)^T (rank <= R).
UNSAT  <=>  no decomposition with rank(A) <= rho and rank(B) <= R.

Symmetry breaking (optional, --classes): row 0 of the A_k and V_r is fixed to one representative (s,t,p) of each
orbit of the gauge group GL_n x GL_rho x GL_R (same argument as docs/ptrank.md, different code); the instance is
then solved once per class.  Without --classes no symmetry is used at all (only feasible for tiny cases).
A SAT answer is decoded to terms and re-verified with ptr.cost.

usage: satcheck.py N R RHO [--classes [--rowsym]] [--solver cadical195|kissat404|...] [--only s,t,p]
"""
import sys, time, itertools
sys.dont_write_bytecode = True
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ptr
from pysat.solvers import Solver


def build(n, R, rho):
    vid = itertools.count(1)
    A = [[[next(vid) for b in range(n)] for a in range(n)] for k in range(rho)]
    B = [[[next(vid) for d in range(n)] for c in range(n)] for k in range(rho)]
    V = [[[next(vid) for d in range(n)] for a in range(n)] for r in range(R)]
    U = [[[next(vid) for b in range(n)] for c in range(n)] for r in range(R)]
    clauses = []

    def AND(x, y):
        z = next(vid)
        clauses.extend([[-z, x], [-z, y], [z, -x, -y]])
        return z

    def XOR_eq(lits, rhs):
        # xor(lits) == rhs, chained in chunks of 3 with fresh variables
        lits = list(lits)
        while len(lits) > 3:
            x, y = lits.pop(), lits.pop()
            z = next(vid)
            # z = x ^ y
            clauses.extend([[-z, x, y], [-z, -x, -y], [z, -x, y], [z, x, -y]])
            lits.append(z)
        k = len(lits)
        for signs in itertools.product([0, 1], repeat=k):
            # forbid assignments with wrong parity: assignment bits = signs; parity(signs) != rhs -> clause
            if sum(signs) % 2 != rhs:
                clauses.append([(-l if s else l) for l, s in zip(lits, signs)])

    for a in range(n):
        for b in range(n):
            for c in range(n):
                for d in range(n):
                    terms = [AND(A[k][a][b], B[k][c][d]) for k in range(rho)]
                    terms += [AND(V[r][a][d], U[r][c][b]) for r in range(R)]
                    XOR_eq(terms, 1 if (a == c and b == d) else 0)
    return A, B, V, U, clauses, next(vid) - 1


def class_units(n, R, rho, s, t, p, A, V):
    """row 0 of A_k is e_k for k < s, 0 otherwise; row 0 of V_r is e_r (r < p), e_{s+r-p} (p <= r < t), 0 otherwise."""
    units = []
    for k in range(rho):
        for b in range(n):
            units.append(A[k][0][b] if (k < s and b == k) else -A[k][0][b])
    for r in range(R):
        for d in range(n):
            one = (r < p and d == r) or (p <= r < t and d == s + r - p)
            units.append(V[r][0][d] if one else -V[r][0][d])
    return units


def row_symmetry_clauses(n, R, rho, A, V, l0_bits, vid_start):
    """Symmetry breaking for the row group {P in GL_n : first row e_0} (it fixes l_0).  With
    l_a = (A_k[a][b])_{k,b} ++ (V_r[a][d])_{r,d} read as a bit vector in this fixed order:
      (a) l_a -> l_a + l_0 (and r_0 -> r_0 + r_a) is a symmetry, so bit j0 of l_a is 0 for a >= 1, j0 = first 1 of l_0;
      (b),(c) any invertible recombination of l_1..l_{n-1} (with the dual recombination of r_1..r_{n-1}) is a
          symmetry, so (l_1, .., l_{n-1}) may be taken as THE reduced row echelon basis of its span, ordered by
          pivot: at the first 1 of l_a' every other l_a (a >= 1) is 0, and first1(l_1) < first1(l_2) < ...
    Every orbit contains exactly one such tuple, so adding these clauses keeps satisfiability."""
    cl = []
    vid = vid_start
    m = n * (rho + R)

    def lvec(a):
        return [A[k][a][b] for k in range(rho) for b in range(n)] + [V[r][a][d] for r in range(R) for d in range(n)]
    L = [lvec(a) for a in range(n)]
    if any(l0_bits):
        j0 = l0_bits.index(1)
        for a in range(1, n):
            cl.append([-L[a][j0]])
    # f[a][i] must be true when l_a is zero on positions < i
    f = {}
    for a in range(1, n):
        f[a] = []
        for i in range(m + 1):
            vid += 1
            f[a].append(vid)
        cl.append([f[a][0]])
        for i in range(m):
            cl.append([-f[a][i], L[a][i], f[a][i + 1]])
        cl.append([-f[a][m]])                      # l_a != 0
    for a in range(1, n):
        for a2 in range(1, n):
            if a == a2:
                continue
            for i in range(m):                     # at the pivot of l_a2, l_a is 0
                cl.append([-f[a2][i], -L[a2][i], -L[a][i]])
    for a in range(1, n - 1):                      # pivot(l_a) < pivot(l_{a+1}): l_a zero on [0..i] => l_{a+1}[i] = 0
        for i in range(m):
            cl.append([-f[a][i + 1], -L[a + 1][i]])
    return cl, vid


def main():
    args = sys.argv[1:]
    if len(args) < 3:
        sys.exit(__doc__)
    n, R, rho = int(args[0]), int(args[1]), int(args[2])
    classes = '--classes' in args
    rowsym = '--rowsym' in args
    solver = args[args.index('--solver') + 1] if '--solver' in args else 'cadical195'
    only = tuple(int(x) for x in args[args.index('--only') + 1].split(',')) if '--only' in args else None
    A, B, V, U, clauses, nv = build(n, R, rho)
    print(f'n={n} R<={R} rho<={rho}: {nv} variables, {len(clauses)} clauses, solver {solver}', flush=True)
    cases = [None]
    if classes:
        cases = [(s, t, p) for s in range(min(n, rho) + 1) for t in range(min(n, R) + 1)
                 for p in range(max(0, s + t - n), min(s, t) + 1)]
        if only:
            cases = [only]
    any_sat = False
    t00 = time.time()
    for cs in cases:
        t0 = time.time()
        with Solver(name=solver, bootstrap_with=clauses) as S:
            assum = class_units(n, R, rho, *cs, A, V) if cs else []
            for u in assum:
                S.add_clause([u])
            if rowsym and cs:
                l0 = [1 if u > 0 else 0 for u in assum]   # same order as lvec(0)
                extra, _ = row_symmetry_clauses(n, R, rho, A, V, l0, nv)
                for c in extra:
                    S.add_clause(c)
            res = S.solve()
            tag = f'class (s,t,p)={cs}' if cs else 'no symmetry'
            if res:
                any_sat = True
                m = set(x for x in S.get_model() if x > 0)
                terms = []
                for r in range(R):
                    Vr = [sum(1 << d for d in range(n) if V[r][a][d] in m) for a in range(n)]
                    Ur = [sum(1 << b for b in range(n) if U[r][c][b] in m) for c in range(n)]
                    terms.append((Vr, Ur))
                Rt, rhot, tot = ptr.cost(n, terms)
                ok = Rt <= R and rhot <= rho
                print(f'  {tag}: SAT  ptr.cost = ({Rt}, {rhot}, {tot}) {"OK" if ok else "DECODE MISMATCH"}  terms {terms}  [{time.time()-t0:.1f}s]', flush=True)
            else:
                print(f'  {tag}: UNSAT  [{time.time()-t0:.1f}s]', flush=True)
    print(f'RESULT n={n} R<={R} rho<={rho}: {"SAT" if any_sat else "UNSAT"} ({len(cases)} case(s), {time.time()-t00:.1f}s)')


if __name__ == '__main__':
    main()
