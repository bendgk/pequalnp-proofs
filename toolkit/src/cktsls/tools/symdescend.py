#!/usr/bin/env python3
"""symdescend.py SPEC BASIS S_START [--time T] [-j J] [--maxorder M] [--perms FILE] [--min S_MIN] [--seed X]

Drive `cktsls --sym` over many symmetry types and walk the size down:
for s = S_START, S_START-1, ...: try every permutation type (one cktsls run each, --fixed auto, T seconds, J threads);
on a hit save found/<spec>_<size>_<basis>.ckt (re-checked with bin/cktcheck) and go on with size-1;
stop when no type gives a hit (that proves NOTHING: heuristic search inside a symmetric ansatz).

Permutations: by default one representative of every cycle type of S_N with order <= M (default 4). That is only
right when EVERY permutation of the inputs is a symmetry of the spec (kn*, th*, maj* ...). For other specs give
--perms FILE (one permutation per line, cycles "(0 1)(2 3)" or an image list); cktsls warns if one is not a symmetry.
Run heavy scans through bin/pnprun.
"""
import os, subprocess, sys
from math import gcd

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
a = sys.argv[1:]
if len(a) < 3: sys.exit(__doc__)
spec, basis, s = a[0], a[1], int(a[2])
tl, J, maxorder, permfile, smin, seed = 20.0, int(os.environ.get('PNP_THREADS', '1')), 4, None, 1, 1
i = 3
while i < len(a):
    if a[i] == '--time': tl = float(a[i + 1]); i += 2
    elif a[i] == '-j': J = int(a[i + 1]); i += 2
    elif a[i] == '--maxorder': maxorder = int(a[i + 1]); i += 2
    elif a[i] == '--perms': permfile = a[i + 1]; i += 2
    elif a[i] == '--min': smin = int(a[i + 1]); i += 2
    elif a[i] == '--seed': seed = int(a[i + 1]); i += 2
    else: sys.exit(__doc__)
specpath = spec if os.path.exists(spec) else f'{ROOT}/specs/{spec}.spec'
name = os.path.basename(specpath).replace('.spec', '')


def n_inputs(path):
    for l in open(path):
        t = l.split()
        if t and t[0] == 'inputs': return int(t[1])
        if t and t[0] == 'n': n = int(t[1])
        if t and t[0] == 'm': return n + int(t[1])
    raise SystemExit('cannot read the number of inputs')


def partitions(n, mx):
    if n == 0:
        yield []
        return
    for k in range(min(n, mx), 0, -1):
        for p in partitions(n - k, k): yield [k] + p


def cycle_types(N, maxorder):
    out = []
    for part in partitions(N, N):
        r = 1
        for c in part: r = r * c // gcd(r, c)
        if r < 2 or r > maxorder: continue
        cyc, pos = [], 0
        for c in part:
            if c > 1: cyc.append('(' + ' '.join(str(pos + k) for k in range(c)) + ')')
            pos += c
        out.append((r, -sum(1 for c in part if c > 1), ''.join(cyc)))
    out.sort()
    return [t[2] for t in out]


perms = [l.strip() for l in open(permfile) if l.strip() and not l.startswith('#')] if permfile else cycle_types(n_inputs(specpath), maxorder)
print(f'# symdescend {name} basis={basis} start={s} time/run={tl}s j={J} perms={len(perms)}', flush=True)
while s >= smin:
    hit = None
    for sym in perms:
        out = f'{ROOT}/found/{name}_{s}_{basis}.ckt.tmp'
        cmd = [f'{ROOT}/bin/cktsls', specpath, '--basis', basis, '-s', str(s), '--sym', sym, '--time', str(tl), '-j', str(J), '--seed', str(seed), '-q', '-o', out]
        res = subprocess.run(cmd, capture_output=True, text=True)
        line = res.stdout.split('\n')[0] if res.stdout else ''
        if line.startswith('FOUND'):
            size = int(line.split('size=')[1].split()[0])
            dst = f'{ROOT}/found/{name}_{size}_{basis}.ckt'
            os.replace(out, dst)
            chk = subprocess.run([f'{ROOT}/bin/cktcheck', specpath, dst, '--basis', basis, '--max', str(s)], capture_output=True, text=True)
            fixed = [l for l in res.stdout.split('\n') if l.startswith('#')][0].split('fixed=')[-1]
            print(f'{name} s={s} sym={sym}: FOUND size={size} time={line.split("time=")[1].split()[0]}s fixed={fixed} -> {dst}  cktcheck: {chk.stdout.strip().split(chr(10))[0]}', flush=True)
            if chk.returncode != 0: sys.exit('cktcheck FAILED')
            hit = (sym, size)
            break
        if os.path.exists(out): os.remove(out)
        bc = line.split('best_cost=')[1].split()[0] if 'best_cost=' in line else (res.stderr.strip().split('\n')[-1][:70] if res.stderr.strip() else '?')
        print(f'{name} s={s} sym={sym}: not found, best_cost={bc}', flush=True)
    if not hit:
        print(f'{name}: no hit at s={s} with any of {len(perms)} symmetry types ({tl}s x {J} threads each). Heuristic: proves nothing.', flush=True)
        break
    perms.remove(hit[0]); perms.insert(0, hit[0])   # try the successful type first at the next size
    s = hit[1] - 1
