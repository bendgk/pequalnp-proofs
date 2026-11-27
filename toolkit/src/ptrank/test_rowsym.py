#!/usr/bin/env python3
"""Soundness test for satcheck.py --rowsym (run with bin/satpy, single thread, a few seconds).

For every l_0 class of several small (n, R, rho) the instance is solved with and without the row-symmetry clauses;
the SAT/UNSAT answers must be identical (the clauses may only remove symmetric copies of solutions, never all
solutions of a class).  The pattern is also compared with the native solver's per-class solution counts
(`ptrank exact --count`: count > 0  <=>  SAT)."""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import satcheck  # noqa: E402
from pysat.solvers import Solver  # noqa: E402

CASES = [(2, 1, 1), (2, 2, 2), (3, 1, 3), (3, 3, 1), (3, 1, 4), (3, 2, 3), (3, 3, 2), (3, 2, 4), (3, 3, 3),
         (4, 1, 6), (4, 6, 1), (4, 1, 7)]


def sat_pattern(n, R, rho, rowsym):
    A, B, V, U, clauses, nv = satcheck.build(n, R, rho)
    out = {}
    for s in range(min(n, rho) + 1):
        for t in range(min(n, R) + 1):
            for p in range(max(0, s + t - n), min(s, t) + 1):
                with Solver(name='cadical195', bootstrap_with=clauses) as S:
                    units = satcheck.class_units(n, R, rho, s, t, p, A, V)
                    for u in units:
                        S.add_clause([u])
                    if rowsym:
                        extra, _ = satcheck.row_symmetry_clauses(n, R, rho, A, V, [1 if u > 0 else 0 for u in units], nv)
                        for c in extra:
                            S.add_clause(c)
                    out[(s, t, p)] = bool(S.solve())
    return out


def native_pattern(n, R, rho):
    p = subprocess.run([os.path.join(ROOT, 'bin', 'ptrank'), 'exact', str(n), '--R', str(R), '--rho-max', str(rho),
                        '--count', '-j', '1', '--quiet'], capture_output=True, text=True)
    out = {}
    for m in re.finditer(r'class \(s=(\d+),t=(\d+),p=(\d+)\): r_0 candidates \S+, solutions (\d+)', p.stderr):
        out[(int(m.group(1)), int(m.group(2)), int(m.group(3)))] = int(m.group(4)) > 0
    return out


def main():
    bad = 0
    for n, R, rho in CASES:
        a = sat_pattern(n, R, rho, False)
        b = sat_pattern(n, R, rho, True)
        line = f'n={n} R<={R} rho<={rho}: {sum(a.values())} SAT classes of {len(a)}; with --rowsym {sum(b.values())}'
        ok = a == b
        if n * (R + rho) <= 18:       # native count mode is only cheap for small cases
            c = native_pattern(n, R, rho)
            line += f'; native solver (count > 0) {sum(c.values())}'
            ok = ok and a == c
        print(('OK   ' if ok else 'FAIL ') + line, flush=True)
        bad += not ok
    print('test_rowsym:', 'ALL OK' if not bad else f'{bad} FAILURES')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
