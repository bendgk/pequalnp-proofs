"""cktsat self-test: random tiny specs, brute force vs SAT (normal+symmetry, normal without symmetry, full model).
    bin/satpy src/cktsat/selftest.py [--n 40] [--seed 1] [--max 5]
Uses at most 2 worker processes; every brute-force call is node-capped."""
import argparse, os, random, re, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CORE, CKTSAT = ROOT + '/bin/cktsat-core', ROOT + '/bin/cktsat'


def tt_spec(N, fs):
    lines = ['type tt', f'inputs {N}', f'outputs {len(fs)}']
    for f in fs:
        lines.append('tt %x' % sum(1 << p for p in range(1 << N) if f[p]))
    return '\n'.join(lines) + '\n'


def rand_mono(rng, N):
    terms = [rng.sample(range(N), rng.randint(2, min(3, N))) for _ in range(rng.randint(2, 4))]
    return [int(any(all((p >> i) & 1 for i in t) for t in terms)) for p in range(1 << N)]


def gen(rng, kind, basis):
    if kind == 'sym':        # specs with a non-trivial symmetry group, so that the canonical-prefix code is exercised
        mode = rng.choice(['weight', 'weight', 'cyclic', 'graph'])
        if mode == 'weight':
            N = rng.choice([3, 4, 5])
            if basis == 'aon':
                w = [rng.randint(0, 1) for _ in range(N + 1)]
            else:
                thr = rng.randint(2, N); w = [int(k >= thr) for k in range(N + 1)]
            care = [rng.random() < 0.75 for _ in range(N + 1)]
            if sum(care) < 2: care = [True] * (N + 1)
            lines = ['type points', f'inputs {N}', 'outputs 1']
            for p in range(1 << N):
                k = bin(p).count('1')
                if care[k]: lines.append('p ' + ''.join(str((p >> i) & 1) for i in range(N)) + ' ' + str(w[k]))
            return '\n'.join(lines) + '\n'
        if mode == 'cyclic':
            N = rng.choice([3, 4, 5])
            g = rand_mono(rng, N) if basis != 'aon' or rng.random() < 0.5 else [rng.randint(0, 1) for _ in range(1 << N)]
            rot = lambda p, k: ((p << k) | (p >> (N - k))) & ((1 << N) - 1)
            f = [int(any(g[rot(p, k)] for k in range(N))) for p in range(1 << N)]
            return tt_spec(N, [f])
        n = rng.choice([3, 4])
        row = rng.randint(1, (1 << n) - 2)
        rows = [((row << k) | (row >> (n - k))) & ((1 << n) - 1) for k in range(n)]
        return f'type graph\nn {n}\nm {n}\nrows ' + ' '.join('%x' % r for r in rows) + '\n'
    if kind == 'tt':
        N = rng.choice([3, 4]); K = rng.choice([1, 1, 1, 2])
        if basis == 'aon':
            fs = [[rng.randint(0, 1) for _ in range(1 << N)] for _ in range(K)]
            if rng.random() < 0.5:   # easier functions so that minima of 3..5 show up
                fs = [[int(bool(a) ^ bool(b)) if rng.random() < 0.5 else a for a, b in zip(rand_mono(rng, N), rand_mono(rng, N))] for _ in range(K)]
        else:
            fs = [rand_mono(rng, N) for _ in range(K)]
        return tt_spec(N, fs)
    if kind == 'points':
        N = rng.choice([4, 5]); K = rng.choice([1, 1, 2])
        pts = rng.sample(range(1 << N), rng.randint(5, 12))
        f = [rand_mono(rng, N) for _ in range(K)] if basis != 'aon' else [[rng.randint(0, 1) for _ in range(1 << N)] for _ in range(K)]
        lines = ['type points', f'inputs {N}', f'outputs {K}']
        for p in pts:
            outs = ''.join('-' if rng.random() < 0.2 else str(f[k][p]) for k in range(K))
            if set(outs) == {'-'}: outs = str(f[0][p]) + outs[1:]
            lines.append('p ' + ''.join(str((p >> i) & 1) for i in range(N)) + ' ' + outs)
        return '\n'.join(lines) + '\n'
    n, m = rng.choice([(2, 3), (3, 3), (3, 4)])
    rows = [rng.randint(0, (1 << m) - 1) for _ in range(n)]
    return f'type graph\nn {n}\nm {m}\nrows ' + ' '.join('%x' % r for r in rows) + '\n'


def brute(path, basis, mx, full):
    a = [CORE, 'brute', path, '--basis', basis, '--max', str(mx), '--max-nodes', '4e8'] + (['--full'] if full else [])
    out = subprocess.run(a, capture_output=True, text=True).stdout.strip()
    m = re.match(r'min (>?)(\d+|\?)', out)
    if m.group(2) == '?': return None
    return ('>' if m.group(1) else '=', int(m.group(2)))


def cktsat(path, basis, mx, extra, logdir):
    a = [CKTSAT, path, '--basis', basis, '--min', '--ub', str(mx), '-j', os.environ.get('PNP_THREADS', '2'), '--logdir', logdir, '--min-cubes', '20'] + extra
    r = subprocess.run(a, capture_output=True, text=True)
    out = r.stdout
    if 'INTERNAL ERROR' in out + r.stderr: return ('ERR', r.stderr)
    m = re.search(r'^SAT .* (?:s|size)=(\d+)', out, re.M)
    if m: return ('=', int(m.group(1)))
    if r.returncode not in (0, 20): return ('ERR', r.stderr[-300:])
    return ('>', mx)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=40); ap.add_argument('--seed', type=int, default=1); ap.add_argument('--max', type=int, default=5)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    bad = 0; hist = {}
    with tempfile.TemporaryDirectory(dir=(os.environ.get('PNP_RUNS') or os.path.join(ROOT, 'runs'))) as td:
        for t in range(a.n):
            kind = rng.choice(['tt', 'points', 'graph', 'sym', 'sym', 'sym']); basis = rng.choice(['ao', 'aon', 'aon', 'ao2'])
            path = os.path.join(td, f't{t}.spec')
            open(path, 'w').write(gen(rng, kind, basis))
            bf = brute(path, basis, min(a.max, 4), True)       # Lean-exact gates, nothing pruned
            bn = brute(path, basis, a.max, False)              # normal gates only (no constants/copies)
            res = {}
            res['sym'] = cktsat(path, basis, a.max, [], td)
            res['nosym'] = cktsat(path, basis, a.max, ['--no-sym'], td)
            res['full'] = cktsat(path, basis, min(a.max, 4), ['--full-model'], td)
            res['inc'] = cktsat(path, basis, a.max, ['--solver', 'cadical195', '--budget', '50'], td)
            res['elim'] = cktsat(path, basis, a.max, ['--elim', 'auto', '--elim-depth', '4'], td)
            res['dep'] = cktsat(path, basis, a.max, ['--dep', '1', '--alldiff', '0', '--solver', 'cadical195-fresh'], td)
            res['elimdead'] = cktsat(path, basis, a.max, ['--elim', 'auto', '--elim-dead', '1', '--elim-sem', '1', '--solver', 'cadical195-fresh'], td)
            res['sens'] = cktsat(path, basis, a.max, ['--sens', '1'], td)
            res['all'] = cktsat(path, basis, a.max, ['--elim', 'auto', '--elim-sem', '1', '--sens', '1', '--dep', '1'], td)
            res['cegar'] = cktsat(path, basis, a.max, ['--cegar', '--cegar-points', '3', '--budget', '300'], td)
            res['split'] = cktsat(path, basis, a.max, ['--budget', '15', '--growth', '1.0', '--depth', '1', '--seed', '7'], td)
            ok = True; why = []
            def same(x, y, cap):   # compare two (rel, n) answers that are both exact up to cap
                if x is None or y is None: return True
                if x[0] == 'ERR' or y[0] == 'ERR': return False
                if x[0] == '=' and y[0] == '=': return x[1] == y[1]
                if x[0] == '=' : return x[1] > y[1] if y[1] < cap else True
                if y[0] == '=' : return y[1] > x[1] if x[1] < cap else True
                return True
            # exactness reference: full brute up to 4, normal brute above (normal brute cannot build constants)
            for k in ('sym', 'nosym', 'inc', 'split', 'elim', 'elimdead', 'dep', 'sens', 'all', 'cegar'):
                if res[k][0] == 'ERR' and 'constant' in str(res[k][1]): continue   # documented: needs --full-model
                if not same(res[k], bf, 99): ok = False; why.append(f'{k} vs brute-full')
                if bn is not None and bf is not None and bf[0] == '>' and not same(res[k], bn, 99): ok = False; why.append(f'{k} vs brute-normal')
                if res[k][0] == 'ERR': ok = False; why.append(f'{k} error')
            if not same(res['full'], bf, 99) or res['full'][0] == 'ERR': ok = False; why.append('full-model vs brute-full')
            if res['sym'] != res['nosym'] and 'ERR' not in (res['sym'][0], res['nosym'][0]): ok = False; why.append('sym vs nosym')
            key = f"{res['sym'][0]}{res['sym'][1] if res['sym'][0] != 'ERR' else ''}"
            hist[key] = hist.get(key, 0) + 1
            if not ok:
                bad += 1
                keep = os.path.join(os.environ.get('PNP_RUNS') or os.path.join(ROOT, 'runs'), f'selftest_fail_{a.seed}_{t}.spec')
                open(keep, 'w').write(open(path).read())
                print(f'MISMATCH test {t} {kind} {basis}: {why} brute_full={bf} brute_normal={bn} {res}  spec kept at {keep}')
            else:
                print(f'ok {t:3d} {kind:6s} {basis:3s} brute_full={bf} brute_normal={bn} sym={res["sym"]} nosym={res["nosym"]} full={res["full"]} inc={res["inc"]} split={res["split"]} elim={res["elim"]} elimdead={res["elimdead"]} dep={res["dep"]} sens={res["sens"]} all={res["all"]} cegar={res["cegar"]}', flush=True)
    print(f'{a.n - bad}/{a.n} agree; distribution of answers: {dict(sorted(hist.items()))}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
