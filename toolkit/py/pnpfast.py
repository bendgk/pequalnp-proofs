"""pnpfast.py — Python mirror of include/ckt.hpp (slow reference) + spec generators + Lean <-> .ckt.

CLI:
    python3 py/pnpfast.py gen-specs                 write specs/*.spec for the live units
    python3 py/pnpfast.py lean2ckt FILE.lean N OUT.ckt   extract ⟨GateOp.x, [..]⟩ gates (+ output wire) from a Lean file
    python3 py/pnpfast.py ckt2lean FILE.ckt         print the gate list as Lean  (⟨GateOp.or, [0, 1]⟩, ...) and the output
    python3 py/pnpfast.py check SPEC CKT            slow independent reference check (pure Python big ints)
"""
import json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------- spec / circuit io
def load_spec(path):
    kind = None; d = dict(rows=[], tts=[], pts=[]); n = m = N = 0; K = 1
    for line in open(path):
        line = line.split('#')[0].split()
        if not line: continue
        k = line[0]
        if k == 'type': kind = line[1]
        elif k == 'n': n = int(line[1])
        elif k == 'm': m = int(line[1])
        elif k == 'inputs': N = int(line[1])
        elif k == 'outputs': K = int(line[1])
        elif k == 'rows': d['rows'] += line[1:]
        elif k == 'tt': d['tts'].append(line[1])
        elif k == 'p': d['pts'].append((line[1], line[2]))
    S = dict(kind=kind)
    if kind == 'graph':
        N = n + m; P = n * m; cols = [0] * N; tgt = 0
        for u in range(n):
            r = int(d['rows'][u], 16)
            for v in range(m):
                p = u * m + v
                cols[u] |= 1 << p; cols[n + v] |= 1 << p
                if (r >> v) & 1: tgt |= 1 << p
        S.update(N=N, K=1, P=P, cols=cols, tgt=[tgt], care=[(1 << P) - 1], n=n, m=m)
    elif kind == 'tt':
        P = 1 << N
        cols = [sum(1 << p for p in range(P) if (p >> i) & 1) for i in range(N)]
        S.update(N=N, K=K, P=P, cols=cols, tgt=[int(t, 16) for t in d['tts']], care=[(1 << P) - 1] * K)
    elif kind == 'points':
        P = len(d['pts']); cols = [0] * N; tgt = [0] * K; care = [0] * K
        for p, (a, b) in enumerate(d['pts']):
            for i in range(N):
                if a[i] == '1': cols[i] |= 1 << p
            for k in range(K):
                if b[k] != '-': care[k] |= 1 << p
                if b[k] == '1': tgt[k] |= 1 << p
        S.update(N=N, K=K, P=P, cols=cols, tgt=tgt, care=care)
    else:
        raise ValueError('unknown spec type')
    return S


def load_ckt(path):
    N = None; gates = []; outs = []
    for line in (sys.stdin if path == '-' else open(path)):
        line = line.split('#')[0].split()
        if not line: continue
        if line[0] == 'inputs': N = int(line[1])
        elif line[0] == 'out': outs = [int(x) for x in line[1:]]
        elif line[0] in ('and', 'or', 'not'): gates.append((line[0], [int(x) for x in line[1:]]))
        else: raise ValueError('bad circuit line: ' + ' '.join(line))
    return N, gates, outs


def save_ckt(path, N, gates, outs, comment=None):
    with open(path, 'w') as f:
        if comment: f.write('# ' + comment + '\n')
        f.write(f'inputs {N}\n')
        for op, ins in gates: f.write(op + ''.join(' %d' % i for i in ins) + '\n')
        f.write('out ' + ' '.join(map(str, outs)) + '\n')


def eval_cols(S, N, gates):
    """Lean-exact: a wire that does not exist yet reads false."""
    full = (1 << S['P']) - 1
    w = list(S['cols'][:N])
    for op, ins in gates:
        vals = [w[i] if 0 <= i < len(w) else 0 for i in ins]
        if op == 'and':
            x = full
            for v in vals: x &= v
        elif op == 'or':
            x = 0
            for v in vals: x |= v
        else:
            x = full & ~(vals[0] if vals else 0)
        w.append(x)
    return w


def check(S, N, gates, outs):
    w = eval_cols(S, N, gates)
    wrong = 0
    for k in range(S['K']):
        val = w[outs[k]] if 0 <= outs[k] < len(w) else 0
        wrong += bin((val ^ S['tgt'][k]) & S['care'][k]).count('1')
    return wrong


# ---------------------------------------------------------------- Lean <-> ckt
def lean2ckt(path, N):
    s = open(path, encoding='utf-8').read()
    gates = [(m.group(1), [int(t) for t in re.findall(r'\d+', m.group(2))])
             for m in re.finditer(r'⟨GateOp\.(and|or|not),\s*\[([^\]]*)\]⟩', s)]
    out = None
    for pat in (r'output\s*:=\s*(\d+)', r'⟨cktGates,\s*(\d+)⟩', r'\]\s*,\s*(\d+)⟩'):
        m = re.search(pat, s)
        if m: out = int(m.group(1)); break
    return N, gates, [out if out is not None else N + len(gates) - 1]


def ckt2lean(N, gates, outs):
    body = ',\n  '.join('⟨GateOp.%s, [%s]⟩' % (op, ', '.join(map(str, ins))) for op, ins in gates)
    return '[\n  ' + body + ']', outs


# ---------------------------------------------------------------- spec generators for the live units
CAND32 = "f2bc7573 59092a9d c443c8c2 1d58483a 1b7982bb a8882290 74d0fd25 00041402 6879a8a5 d65a6f1a 7455fba3 24508c1a 3050a010 68658ad5 10a00735 5e55690e 6ab804a4 00b01458 f447af40 00b07351 a88c2290 40d9d7bc 40241486 54058082 6891afb9 50ddf79e 553080be 28c180f8 6ac8ae9e a6860e80 20508c18 10f01050".split()


def w(path, text):
    open(os.path.join(ROOT, 'specs', path), 'w').write(text)
    print('wrote specs/' + path)


def tt_spec(N, fs):
    lines = ['type tt', f'inputs {N}', f'outputs {len(fs)}']
    for f in fs:
        t = 0
        for p in range(1 << N):
            if f([(p >> i) & 1 for i in range(N)]): t |= 1 << p
        lines.append('tt %x' % t)
    return '\n'.join(lines) + '\n'


def gen_specs(rows128=None):
    for n in range(3, 13):
        # crown: u joined to v when u != v  (Represents (fun u v : Fin n => decide (u ≠ v)))
        w(f'crown{n}.spec', f'type graph\nn {n}\nm {n}\nrows ' + ' '.join('%x' % (((1 << n) - 1) ^ (1 << u)) for u in range(n)) + '\n')
        # K(n): n wires, false on every 1-hot input, true on every 2-hot input
        pts = []
        for i in range(n):
            pts.append(('p ' + ''.join('1' if k == i else '0' for k in range(n)) + ' 0'))
        for i in range(n):
            for j in range(i + 1, n):
                pts.append(('p ' + ''.join('1' if k in (i, j) else '0' for k in range(n)) + ' 1'))
        w(f'kn{n}.spec', f'type points\ninputs {n}\noutputs 1\n' + '\n'.join(pts) + '\n')
    w('cand32.spec', 'type graph\nn 32\nm 32\nrows ' + ' '.join(CAND32) + '\n')
    if rows128:
        R = json.load(open(rows128))
        w('cand128.spec', 'type graph\nn 128\nm 128\nrows ' + ' '.join('%032x' % (int(r, 16) if isinstance(r, str) else r) for r in R) + '\n')
    # perfect matching in a 3x3 bipartite graph on 9 edge bits (L-meta-17387..17390)
    pm = lambda x: (x[0] & x[4] & x[8]) | (x[0] & x[5] & x[7]) | (x[1] & x[3] & x[8]) | (x[1] & x[5] & x[6]) | (x[2] & x[3] & x[7]) | (x[2] & x[4] & x[6])
    w('match3.spec', tt_spec(9, [pm]))
    # 3x3 Boolean matrix product, 18 inputs, 9 outputs (L-meta-18919): out[3i+j] = OR_k x[3i+k] & x[9+3k+j]
    mm = [(lambda x, i=i, j=j: any(x[3 * i + k] & x[9 + 3 * k + j] for k in range(3))) for i in range(3) for j in range(3)]
    w('mm3.spec', tt_spec(18, mm))
    mm2 = [(lambda x, i=i, j=j: any(x[2 * i + k] & x[4 + 2 * k + j] for k in range(2))) for i in range(2) for j in range(2)]
    w('mm2.spec', tt_spec(8, mm2))
    # edge function of the n-cycle: OR_i x_i & x_{i+1}
    for n in (5, 6, 7, 8, 9):
        w(f'cyc{n}.spec', tt_spec(n, [lambda x, n=n: any(x[i] & x[(i + 1) % n] for i in range(n))]))


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a: sys.exit(__doc__)
    if a[0] == 'gen-specs':
        gen_specs(a[1] if len(a) > 1 else None)
    elif a[0] == 'lean2ckt':
        N, g, o = lean2ckt(a[1], int(a[2])); save_ckt(a[3], N, g, o, 'from ' + os.path.basename(a[1]))
        print(f'{len(g)} gates, out {o}')
    elif a[0] == 'ckt2lean':
        N, g, o = load_ckt(a[1]); body, outs = ckt2lean(N, g, o); print(body); print('-- output wire(s):', outs)
    elif a[0] == 'check':
        S = load_spec(a[1]); N, g, o = load_ckt(a[2]); wr = check(S, N, g, o)
        print('OK' if wr == 0 else f'BAD wrong={wr}', 'size', len(g)); sys.exit(0 if wr == 0 else 1)
    else:
        sys.exit(__doc__)
