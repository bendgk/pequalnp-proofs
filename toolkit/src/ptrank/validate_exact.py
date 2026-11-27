#!/usr/bin/env python3
"""Validation of `ptrank exact` (the slice solver) by exact solution counts.

For given (n, R, rho) the slice solver counts the tuples (l_0..l_{n-1}, r_0..r_{n-1}) with beta(l_a, r_c) = [a=c] I,
i.e. the tuples (A_k, B_k)_{k<rho}, (V_r, U_r)_{r<R} with  sum_k vec(A_k) vec(B_k)^T + [X -> sum_r V_r X^T U_r] = I.
The same number is computed here from an INDEPENDENT brute force (`ptrank brute`, direct evaluation of rank(I + Phi)
for every tuple of R terms) as
        sum over all tuples of R terms of  F(rank(I + Phi), rho),
where F(k, rho) = number of pairs (X, Y) of N x rho matrices with X Y^T = a fixed N x N matrix of rank k (N = n^2):
        F(k, rho) = sum_{j=k}^{min(rho,N)} [N-k choose j-k]_2 * prod_{i<j} (2^rho - 2^i) * 2^(N (rho - j)).
(F itself is checked by brute force for tiny sizes below.)  The solver is run three ways:
   --count           one l_0 per symmetry class, weighted by the class size
   --count --nosym   every l_0, no symmetry at all (small cases only)
and with R and rho swapped (the A/B symmetry says the two counts are equal).
Usage: validate_exact.py [quick|full]     (threads: $PNP_THREADS or 1; run it under bin/pnprun -c 3 for speed)
"""
import sys, os, json, subprocess, itertools, re, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.path.join(ROOT, 'bin', 'ptrank')
J = os.environ.get('PNP_THREADS', '1')


def gbinom(a, b):
    if b < 0 or b > a:
        return 0
    num = den = 1
    for i in range(b):
        num *= (1 << (a - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def F(k, rho, N):
    tot = 0
    for j in range(k, min(rho, N) + 1):
        inj = 1
        for i in range(j):
            inj *= (1 << rho) - (1 << i)
        tot += gbinom(N - k, j - k) * inj * (1 << (N * (rho - j)))
    return tot


def rank_gf2(rows):
    rows = [r for r in rows if r]
    rk = 0
    while rows:
        p = rows.pop()
        rk += 1
        low = p & -p
        rows = [x ^ p if x & low else x for x in rows]
        rows = [x for x in rows if x]
    return rk


def check_F():
    """brute force: count (X, Y) in (F_2^{N x rho})^2 with X Y^T = A for one A of each rank."""
    for N, rho in [(2, 1), (2, 2), (3, 1), (3, 2), (2, 3), (3, 3)]:
        cnt = {}
        for X in itertools.product(range(1 << rho), repeat=N):        # rows of X
            for Y in itertools.product(range(1 << rho), repeat=N):    # rows of Y
                A = tuple(sum((bin(X[i] & Y[j]).count('1') & 1) << j for j in range(N)) for i in range(N))
                cnt[A] = cnt.get(A, 0) + 1
        for A, c in cnt.items():
            k = rank_gf2(list(A))
            assert c == F(k, rho, N), (N, rho, A, c, F(k, rho, N))
        # matrices that never occur must have rank > rho
        print(f'  F(k, rho={rho}, N={N}) formula == brute force for all {len(cnt)} reachable matrices')


def brute_hist(n, R, sym):
    out = subprocess.run([BIN, 'brute', str(n), str(R), '-j', J] + (['--sym'] if sym else []),
                         capture_output=True, text=True, check=True).stdout
    o = json.loads(out)
    return {int(k): int(v) for k, v in o['hist'].items()}


def solver_count(n, R, rho, nosym=False):
    args = [BIN, 'exact', str(n), '--R', str(R), '--rho-max', str(rho), '--count', '-j', J, '--quiet']
    if nosym:
        args.append('--nosym')
    t0 = time.time()
    p = subprocess.run(args, capture_output=True, text=True)
    m = re.search(r'COUNT .*?: (\d+) solutions', p.stdout)
    assert m, p.stdout + p.stderr
    return int(m.group(1)), time.time() - t0


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'quick'
    print('formula F:')
    check_F()
    cases = [(2, 1, 1, True), (2, 1, 2, True), (2, 2, 1, True), (2, 2, 2, True), (2, 1, 3, True), (2, 3, 1, True),
             (2, 2, 3, True), (2, 3, 2, True), (2, 3, 3, True),
             (3, 1, 2, True), (3, 2, 1, True), (3, 1, 3, True), (3, 3, 1, True), (3, 2, 2, True),
             (3, 1, 4, False), (3, 4, 1, False), (3, 2, 3, False), (3, 3, 2, False)]
    if mode == 'full':
        cases += [(3, 1, 5, False), (3, 5, 1, False), (3, 2, 4, False), (3, 4, 2, False), (3, 3, 3, False),
                  (4, 1, 6, False), (4, 6, 1, False)]
    hists = {}
    bad = 0
    for n, R, rho, do_nosym in cases:
        # brute force is run on the side with the fewer terms (R or rho), the other count follows from the swap
        Rb, rb = (R, rho) if R <= rho else (rho, R)
        key = (n, Rb)
        if key not in hists:
            sym = (2 * n * n * Rb > 30)
            hists[key] = brute_hist(n, Rb, sym)
        expect = sum(c * F(k, rb, n * n) for k, c in hists[key].items() if k <= rb)
        got, dt = solver_count(n, R, rho)
        line = f'n={n} R<={R} rho<={rho}: brute-force count {expect}; solver (classes x weights) {got} [{dt:.1f}s]'
        ok = got == expect
        if do_nosym and n * (R + rho) <= 15:
            got2, dt2 = solver_count(n, R, rho, nosym=True)
            line += f'; solver (no symmetry) {got2} [{dt2:.1f}s]'
            ok = ok and got2 == expect
        print(('OK   ' if ok else 'FAIL ') + line, flush=True)
        bad += not ok
    print('validate_exact:', 'ALL OK' if not bad else f'{bad} FAILURES')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
