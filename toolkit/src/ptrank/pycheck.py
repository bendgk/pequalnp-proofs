#!/usr/bin/env python3
"""Independent checks of ptrank against the reference implementation ptr.py (pure Python, single thread).

  pycheck.py cost   < lines of `ptrank gen N R COUNT SEED`        native (R, rho, total) == ptr.cost(n, terms)
  pycheck.py sym    < lines of `ptrank symcheck N R COUNT SEED --print`   ptr.cost is invariant under the (P,Q) action
  pycheck.py verify FILE.json [...]                                recompute a witness file with ptr.cost
  pycheck.py def    FILE.json [...]                                check the DEFINITION directly: build B, B^T1, A = I + B^T1,
                                                                   and report rank(A) + rank(B) (no map form, no ptr.phi_matrix)
The reference is src/ptrank/ptr.py (pure Python; no bytecode is written).
"""
import sys, json
sys.dont_write_bytecode = True
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ptr  # noqa: E402


def terms_of(obj):
    return [(list(V), list(U)) for V, U in obj['terms']]


def by_definition(n, terms):
    """rank(B), rank(I + B^T1) straight from the definition:
    B[(p1,p2),(q1,q2)] = sum_r U_r[p1][p2] V_r[q1][q2];  (B^T1)[(i1,i2),(j1,j2)] = B[(j1,i2),(i1,j2)]."""
    N = n * n
    B = [0] * N
    for V, U in terms:
        vv = 0
        for q1 in range(n):
            for q2 in range(n):
                if (V[q1] >> q2) & 1:
                    vv |= 1 << (q1 * n + q2)
        for p1 in range(n):
            for p2 in range(n):
                if (U[p1] >> p2) & 1:
                    B[p1 * n + p2] ^= vv
    A = [1 << k for k in range(N)]
    for i1 in range(n):
        for i2 in range(n):
            for j1 in range(n):
                for j2 in range(n):
                    if (B[j1 * n + i2] >> (i1 * n + j2)) & 1:
                        A[i1 * n + i2] ^= 1 << (j1 * n + j2)
    return ptr.rank_gf2(list(B)), ptr.rank_gf2(list(A))


def main():
    cmd = sys.argv[1]
    if cmd == 'cost':
        k = bad = 0
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            o = json.loads(line)
            R, rho, tot = ptr.cost(o['n'], terms_of(o))
            k += 1
            if (R, rho, tot) != (o['R'], o['rho'], o['total']):
                bad += 1
                print('MISMATCH', line, 'ptr.py says', (R, rho, tot))
        print(f'pycheck cost: {k} instances, {bad} mismatches against ptr.cost')
        sys.exit(1 if bad else 0)
    if cmd == 'sym':
        k = bad = 0
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            o = json.loads(line)
            c0 = ptr.cost(o['orig']['n'], terms_of(o['orig']))
            c1 = ptr.cost(o['pq']['n'], terms_of(o['pq']))
            k += 1
            if c0 != c1:
                bad += 1
                print('SYMMETRY VIOLATION', line)
        print(f'pycheck sym: {k} instances, {bad} violations of cost invariance under (V,U) -> (P V Q^-T, P^-T U Q)')
        sys.exit(1 if bad else 0)
    if cmd in ('verify', 'def'):
        rc = 0
        for path in sys.argv[2:]:
            o = json.load(open(path))
            n = o['n']
            t = terms_of(o)
            R, rho, tot = ptr.cost(n, t)
            ok = (R, rho, tot) == (o.get('R', R), o.get('rho', rho), o.get('total', tot))
            msg = f'{path}: n={n} terms={len(t)}  ptr.cost -> (R, rho, total) = ({R}, {rho}, {tot})'
            if cmd == 'def':
                rb, ra = by_definition(n, t)
                ok = ok and (rb, ra) == (R, rho)
                msg += f';  from the definition: rank(B) = {rb}, rank(I + B^T1) = {ra}'
            print(msg, ' OK' if ok else ' MISMATCH')
            if not ok:
                rc = 1
        sys.exit(rc)
    sys.exit(__doc__)


if __name__ == '__main__':
    main()
