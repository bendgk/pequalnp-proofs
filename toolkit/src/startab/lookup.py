#!/usr/bin/env python3
"""lookup.py -- look a bipartite graph up in a startab table.

    python3 src/startab/lookup.py tables/star_4.json 14 13 11 7        # rows as integers (bit v of rows[u] = A u v)
    python3 src/startab/lookup.py tables/star_4.json 0xe 0xd 0xb 0x7   # hex also accepted
    python3 src/startab/lookup.py tables/star_4.json --complement 14 13 11 7
    python3 src/startab/lookup.py tables/star_4.json --ckt mono 14 13 11 7   # witness for THIS labelling, as .ckt text

Canonicalises the graph under the table's symmetry group (plain tables: row permutations, column permutations
and transpose; encoder tables: index-bit permutations/complementations on each side and transpose) and prints the
class entry.  With --ckt the stored witness is transported back to the given labelling (input wires renamed).
"""
import itertools, json, sys


def index_maps(n, enc):
    if not enc:
        return [list(p) for p in itertools.permutations(range(n))]
    kb = n.bit_length() - 1
    res = []
    for bp in itertools.permutations(range(kb)):
        for c in range(n):
            res.append([sum(((u >> i) & 1) << bp[i] for i in range(kb)) ^ c for u in range(n)])
    return res


def enc_wires(n, m):
    """index sets of the encoder wires, as (side, set of indices), in table order"""
    out = []
    for side, size in ((0, n), (1, m)):
        for i in range(size.bit_length() - 1):
            for a in (0, 1):
                out.append((side, frozenset(u for u in range(size) if ((u >> i) & 1) == a)))
    return out


def canon(rows, n, m, enc, transpose):
    """returns (canonical value, canonical rows, (t, rm, cm)) where the group element maps the given graph to the
    canonical one: plain: canon[rm[u]][cm[v]] = A[u][v];  transposed: canon[rm[v]][cm[u]] = A[u][v]."""
    best = None
    A = [[(rows[u] >> v) & 1 for v in range(m)] for u in range(n)]
    RM = index_maps(n, enc); CM = index_maps(m, enc)
    for t in ((0, 1) if (transpose and n == m) else (0,)):
        B = A if t == 0 else [[A[v][u] for v in range(n)] for u in range(m)]   # B[x][y]: x indexes new rows before relabelling
        for rm in RM:
            # value = sum over (x,y) with B[x][y] of 2^(rm[x]*m + cm[y])
            for cm in CM:
                val = 0
                for x in range(n):
                    bx = B[x]; sh = rm[x] * m
                    for y in range(m):
                        if bx[y]: val |= 1 << (sh + cm[y])
                if best is None or val < best[0]:
                    best = (val, t, rm, cm)
    val, t, rm, cm = best
    return val, [(val >> (u * m)) & ((1 << m) - 1) for u in range(n)], (t, rm, cm)


def transport(witness, n, m, enc, g):
    """witness is a circuit for the canonical graph; return the circuit for the original labelling."""
    t, rm, cm = g
    # original input wire -> canonical input wire.  Plain: row u -> row rm[u], column v -> column cm[v].
    # Transposed: canon[rm[v]][cm[u]] = A[u][v]: original row u is canonical column cm[u], original column v is canonical row rm[v].
    fwd = {}
    for u in range(n): fwd[u] = (rm[u]) if t == 0 else (n + cm[u])
    for v in range(m): fwd[n + v] = (n + cm[v]) if t == 0 else (rm[v])
    if enc:
        E = enc_wires(n, m)
        for i, (side, st) in enumerate(E):
            if t == 0: img = (side, frozenset((rm if side == 0 else cm)[x] for x in st))
            else: img = (1 - side, frozenset((cm if side == 0 else rm)[x] for x in st))
            fwd[n + m + i] = n + m + E.index(img)
    inv = {c: o for o, c in fwd.items()}          # canonical wire -> original wire
    N = len(fwd)
    out = []
    for line in witness.strip().split('\n'):
        p = line.split()
        if p[0] in ('and', 'or', 'not', 'out'):
            out.append(' '.join([p[0]] + [str(inv[int(x)]) if int(x) < N else x for x in p[1:]]))
        else:
            out.append(line)
    return '\n'.join(out) + '\n'


def main():
    a = sys.argv[1:]
    comp = False; ckt = None
    if len(a) < 2: sys.exit(__doc__)
    T = json.load(open(a[0])); a = a[1:]
    while a and a[0].startswith('--'):
        if a[0] == '--complement': comp = True; a = a[1:]
        elif a[0] == '--ckt': ckt = a[1]; a = a[2:]
        else: sys.exit(__doc__)
    n, m, enc = T['n'], T['m'], T['encoder']
    rows = [int(x, 0) for x in a]
    if len(rows) != n: sys.exit('need %d rows' % n)
    if comp: rows = [r ^ ((1 << m) - 1) for r in rows]
    val, crow, g = canon(rows, n, m, enc, 'transpose' in T['symmetry'])
    idx = {tuple(c['rows']): c for c in T['classes']}
    c = idx[tuple(crow)]
    if ckt:
        e = c[ckt]
        if e.get('witness') is None: sys.exit('no witness stored')
        sys.stdout.write(transport(e['witness'], n, m, enc, g))
        return
    print('rows %s -> class %d, canonical rows %s, orbit size %d' % (rows, c['id'], c['rows'], c['orbit_size']))
    for key in ('mono', 'not'):
        e = c[key]
        if e['exact']: print('  %-4s size %d (exact)' % (key, e['size']))
        else: print('  %-4s size in [%d, %s] (not exact; best circuit found: %s)' % (key, e['lower'], e['size'] if e['size'] is not None else '?', e['size']))
    if 'star_mono' in c: print('  stars only (no encoder wires): mono %d, not %d' % (c['star_mono'], c['star_not']))
    d = T['classes'][c['complement']]
    print('  complement: class %d rows %s mono %s%s' % (d['id'], d['rows'], d['mono']['size'], '' if d['mono']['exact'] else ' (not exact)'))


if __name__ == '__main__':
    main()
