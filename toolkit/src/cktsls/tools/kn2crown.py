#!/usr/bin/env python3
"""kn2crown.py KN.ckt OUT.ckt  -- turn a circuit for specs/kn<n>.spec (n inputs) into one for specs/crown<n>.spec
(2n inputs: n left + n right) by putting z_i = x_i OR y_i in front (crown_n <= n + K(n)). Check the result with bin/cktcheck."""
import sys
src, dst = sys.argv[1], sys.argv[2]
n = None; gates = []; outs = []
for line in open(src):
    t = line.split('#')[0].split()
    if not t: continue
    if t[0] == 'inputs': n = int(t[1])
    elif t[0] == 'out': outs = [int(x) for x in t[1:]]
    else: gates.append((t[0], [int(x) for x in t[1:]]))
m = lambda w: 2 * n + w            # kn input i -> z_i (wire 2n+i); kn gate j (wire n+j) -> wire 3n+j
with open(dst, 'w') as f:
    f.write(f'# crown{n} from {src}: z_i = x_i or y_i, then the K({n}) circuit; size {n + len(gates)}\n')
    f.write(f'inputs {2 * n}\n')
    for i in range(n): f.write(f'or {i} {n + i}\n')
    for op, ins in gates: f.write(op + ''.join(' %d' % m(w) for w in ins) + '\n')
    f.write('out ' + ' '.join(str(m(w)) for w in outs) + '\n')
