#!/usr/bin/env python3
"""andlib.py -- shared helpers for the AND-complexity tables (pure Python, no SAT).

A graph is (n, m, T) with T an int cell mask: bit u*m+v set iff A u v  (rows[u] has bit v set iff A u v).
A witness is (L, R, out): L[j], R[j] = lists of generator indices feeding AND gate j, out = list of generator indices
OR-ed into the output.  Generator indices: 0..n-1 rows (left vertices), n..n+m-1 columns (right vertices),
n+m+k = AND gate k.  Empty OR = empty set.
"""
import os, subprocess, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CKTCHECK = os.path.join(ROOT, 'bin', 'cktcheck')


def gens(n, m):
    g = [sum(1 << (u * m + v) for v in range(m)) for u in range(n)]
    g += [sum(1 << (u * m + v) for u in range(n)) for v in range(m)]
    return g


def rows_to_mask(rows, m):
    return sum(r << (m * u) for u, r in enumerate(rows))


def mask_to_rows(T, n, m):
    return [(T >> (u * m)) & ((1 << m) - 1) for u in range(n)]


def eval_wit(n, m, L, R, out, inputs=None):
    """cell mask computed by the witness (independent of everything else in this directory)."""
    val = list(inputs) if inputs is not None else gens(n, m)
    N = len(val)
    for j in range(len(L)):
        x = 0; y = 0
        for i in L[j]:
            assert 0 <= i < N + j, 'AND gate %d reads generator %d which is not earlier' % (j, i)
            x |= val[i]
        for i in R[j]:
            assert 0 <= i < N + j, 'AND gate %d reads generator %d which is not earlier' % (j, i)
            y |= val[i]
        val.append(x & y)
    o = 0
    for i in out:
        o |= val[i]
    return o


def wit_to_ckt(n, m, L, R, out, n_inputs=None):
    """expand a witness into a toolkit .ckt (basis ao: AND/OR, every gate with exactly two earlier wires).
    Returns (text, number of AND gates, number of OR gates).  An OR of one wire is the wire itself; the empty
    output is a wire that does not exist (reads false, FORMAT.md)."""
    N = n + m if n_inputs is None else n_inputs
    lines = []
    wire_of = {i: i for i in range(N)}          # generator index -> wire
    memo = {}

    def emit(op, a, b):
        lines.append('%s %d %d' % (op, a, b))
        return N + len(lines) - 1

    def big_or(idx):
        ws = sorted(set(wire_of[i] for i in idx))
        assert ws, 'empty OR feeding an AND gate'
        cur = (ws[0],)
        w = ws[0]
        for x in ws[1:]:
            cur = cur + (x,)
            if cur not in memo:
                memo[cur] = emit('or', w, x)
            w = memo[cur]
        return w
    n_and = 0
    for j in range(len(L)):
        a = big_or(L[j]); b = big_or(R[j])
        wire_of[N + j] = emit('and', a, b); n_and += 1
    if out:
        o = big_or(out)
        text = 'inputs %d\n%s%sout %d\n' % (N, '\n'.join(lines), '\n' if lines else '', o)
    else:
        text = 'inputs %d\n%s%sout %d\n' % (N, '\n'.join(lines), '\n' if lines else '', N + len(lines))
    return text, n_and, len(lines) - n_and


def ckt_and_count(text):
    return sum(1 for l in text.split('\n') if l.split()[:1] == ['and'])


def ckt_gate_count(text):
    return sum(1 for l in text.split('\n') if l.split()[:1] and l.split()[0] in ('and', 'or', 'not'))


def graph_spec(n, m, rows):
    return 'type graph\nn %d\nm %d\nrows %s\n' % (n, m, ' '.join('%x' % r for r in rows))


_tmp = None


def cktcheck(spec_text, ckt_text, basis='ao', maxgates=None):
    """True iff bin/cktcheck accepts (exit 0)."""
    global _tmp
    if _tmp is None:
        _tmp = tempfile.mkdtemp(prefix='andtab_')
    sp = os.path.join(_tmp, 's.spec'); ck = os.path.join(_tmp, 'c.ckt')
    open(sp, 'w').write(spec_text); open(ck, 'w').write(ckt_text)
    cmd = [CKTCHECK, sp, ck, '--basis', basis, '-q']
    if maxgates is not None:
        cmd += ['--max', str(maxgates)]
    return subprocess.run(cmd).returncode == 0


# ---------------------------------------------------------------- reductions and bounds
def core(n, m, T):
    """remove full rows/columns and merge twin rows/columns.  And is unchanged (docs/andtab.md, Lemma 5).
    Returns (n2, m2, T2, rowmap, colmap, full_rows, full_cols): rowmap[u] = core row of original row u or None if
    row u is full; same for columns."""
    A = [[(T >> (u * m + v)) & 1 for v in range(m)] for u in range(n)]
    full_rows = [u for u in range(n) if all(A[u])]
    full_cols = [v for v in range(m) if all(A[u][v] for u in range(n))]
    rs = [u for u in range(n) if u not in full_rows]
    cs = [v for v in range(m) if v not in full_cols]
    rkey = {}; rowmap = [None] * n; rrep = []
    for u in rs:
        k = tuple(A[u][v] for v in cs)
        if k not in rkey:
            rkey[k] = len(rrep); rrep.append(u)
        rowmap[u] = rkey[k]
    ckey = {}; colmap = [None] * m; crep = []
    for v in cs:
        k = tuple(A[u][v] for u in rrep)
        if k not in ckey:
            ckey[k] = len(crep); crep.append(v)
        colmap[v] = ckey[k]
    n2, m2 = len(rrep), len(crep)
    T2 = 0
    for a, u in enumerate(rrep):
        for b, v in enumerate(crep):
            if A[u][v]:
                T2 |= 1 << (a * m2 + b)
    return n2, m2, T2, rowmap, colmap, full_rows, full_cols


def lift(n, m, core_info, L, R, out):
    """witness for the core graph -> witness for the original graph."""
    n2, m2, T2, rowmap, colmap, full_rows, full_cols = core_info

    def conv(idx):
        res = []
        for i in idx:
            if i < n2:
                res += [u for u in range(n) if rowmap[u] == i]
            elif i < n2 + m2:
                res += [n + v for v in range(m) if colmap[v] == i - n2]
            else:
                res.append(n + m + (i - n2 - m2))
        return sorted(res)
    return [conv(x) for x in L], [conv(x) for x in R], sorted(conv(out) + list(full_rows) + [n + v for v in full_cols])


def zero_rectangles(n, m, T):
    """maximal all-zero combinatorial rectangles of T, as cell masks (one per set of rows with a common zero column)."""
    zc = []
    for u in range(n):
        zc.append(sum(1 << v for v in range(m) if not (T >> (u * m + v)) & 1))
    seen = set(); rects = []
    for R in range(1, 1 << n):
        C = (1 << m) - 1
        for u in range(n):
            if (R >> u) & 1:
                C &= zc[u]
        if not C:
            continue
        # close the row set
        R2 = sum(1 << u for u in range(n) if (zc[u] & C) == C)
        if (R2, C) in seen:
            continue
        seen.add((R2, C))
        mask = 0
        for u in range(n):
            if (R2 >> u) & 1:
                mask |= C << (u * m)
        rects.append(mask)
    return rects


def cov0(n, m, T, limit=12):
    """least number of all-zero rectangles covering the zeros of T (= Boolean rank of the complement), by
    iterative-deepening search.  Fine up to about 6 x 6; for larger graphs use andsat.cov0_sat."""
    full = (1 << (n * m)) - 1
    Z = full & ~T
    if Z == 0:
        return 0
    rects = zero_rectangles(n, m, T)
    by_cell = {}
    for p in range(n * m):
        if (Z >> p) & 1:
            by_cell[p] = [r for r in rects if (r >> p) & 1]

    def rec(rem, k):
        if rem == 0:
            return True
        if k == 0:
            return False
        p = (rem & -rem).bit_length() - 1
        for r in by_cell[p]:
            if rec(rem & ~r, k - 1):
                return True
        return False
    for k in range(1, limit + 1):
        if rec(Z, k):
            return k
    return None


def ceil_log2(x):
    return 0 if x <= 1 else (x - 1).bit_length()


def type_counts(n, m, T):
    """(#distinct row types that are neither empty nor full, same for columns): And <= min of the two."""
    rows = set(); cols = set()
    for u in range(n):
        r = (T >> (u * m)) & ((1 << m) - 1)
        if r not in (0, (1 << m) - 1):
            rows.add(r)
    for v in range(m):
        c = sum(1 << u for u in range(n) if (T >> (u * m + v)) & 1)
        if c not in (0, (1 << n) - 1):
            cols.add(c)
    return len(rows), len(cols)
