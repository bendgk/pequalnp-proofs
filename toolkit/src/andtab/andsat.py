#!/usr/bin/env python3
"""andsat.py -- AND-complexity of ONE bipartite graph by SAT (run with bin/satpy).  Independent of bin/andtab.

    bin/satpy src/andtab/andsat.py graph --rows 14,13,11,7 [--m 4] [--hex] [--lo L] [--amax A] [--timeout SEC]
                                         [--enc] [--no-core] [--no-sym] [--solver cadical195] [--ckt OUT.ckt] [--json]
    bin/satpy src/andtab/andsat.py table tables/and_4.json [--every K] [--only i,j] [--timeout SEC] [--budget SEC]
    bin/satpy src/andtab/andsat.py family NAME N [...same options as graph]     NAME in crown match ip disj inter gt rand<seed>

`graph`/`family`: iterative deepening a = lo, lo+1, ...: "is there a normal-form circuit with exactly a AND gates?"
UNSAT at every a < A and SAT at A proves And = A (docs/andtab.md section 2: the normal form with the extra
conditions M1-M4 loses nothing for a MINIMUM circuit, and a = 0 is decided directly).  The witness is re-evaluated
in Python (andlib.eval_wit) and its .ckt is checked with bin/cktcheck --basis ao.
`table`: for every class of an and-table re-prove the value: UNSAT at size-1 (all smaller a too), SAT at size.

CNF for a given a (N = number of free input wires, P = number of cells):
  Ls[j][i], Rs[j][i]   generator i (input i < N, or AND gate i-N < j) is in L_j / R_j
  Os[k]                AND gate k is OR-ed into the output (inputs inside the graph are always in the output)
  V[j][p]              AND gate j is on at cell p;  XL[j][p], XR[j][p] its two ORs;  t = (selector AND V) products
  XL[j][p] <-> OR(Ls[j][i] : input i contains p) OR OR(Ls[j][N+k] AND V[k][p] : k < j),  V = XL AND XR,
  cell in the graph and in no free input inside the graph: some gate in the output is on;  cell not in the graph:
  no gate in the output is on.
Conditions valid for a minimum circuit (so only used together with "all smaller a refuted"):
  M1 every AND gate is read by a later AND gate or the output, and the last one is in the output;
  M2 L_j and R_j are disjoint;  M3 the least generator index of L_j u R_j is in L_j;
  M4 if gate j+1 does not read gate j then L_j >= L_{j+1} lexicographically (as 0/1 vectors on the common indices);
  M5 for automorphisms phi of the graph: (L_0, R_0, L_1, ...) >= its image under phi, lexicographically
     (cut after --autodepth gates).  M3-M5 hold together for the circuit whose string is the largest in its orbit.
"""
import argparse, json, os, random, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andlib


# ---------------------------------------------------------------- automorphisms of the graph
def isos(A, B, n, m, limit):
    """up to `limit` pairs (a, b) of bijections with B[a[u]][b[v]] == A[u][v] (A, B: n x m 0/1 lists)."""
    res = []
    a = [None] * n; used = [False] * n
    sigA = [0] * m; sigB = [0] * m

    def rec(k):
        if len(res) >= limit:
            return
        if k == n:
            # match the columns: equal full signatures, paired in sorted order
            ia = sorted(range(m), key=lambda v: sigA[v]); ib = sorted(range(m), key=lambda v: sigB[v])
            b = [None] * m
            for x, y in zip(ia, ib):
                b[x] = y
            res.append((a[:], b))
            return
        for r in range(n):
            if used[r]:
                continue
            oldA = sigA[:]; oldB = sigB[:]
            for v in range(m):
                sigA[v] = (sigA[v] << 1) | A[k][v]
                sigB[v] = (sigB[v] << 1) | B[r][v]
            if sorted(sigA) == sorted(sigB):
                a[k] = r; used[r] = True
                rec(k + 1)
                used[r] = False
            sigA[:] = oldA; sigB[:] = oldB
    rec(0)
    return res


def automorphisms(n, m, T, limit=64):
    """automorphisms of the graph as permutations phi of the n+m input indices (row u = u, column v = n+v):
    the cell (u, v) = row u ^ column v goes to phi(u) ^ phi(n+v), and T is preserved.  Includes the transposing
    ones when n == m.  The identity is left out.  At most about `limit` of each kind."""
    A = [[(T >> (u * m + v)) & 1 for v in range(m)] for u in range(n)]
    res = []
    for a, b in isos(A, A, n, m, limit):
        phi = a + [n + x for x in b]
        if phi != list(range(n + m)):
            res.append(phi)
    if n == m:
        At = [[A[v][u] for v in range(n)] for u in range(n)]
        for a, b in isos(A, At, n, n, limit):
            # At[a[u]][b[v]] = A[u][v], i.e. A[b[v]][a[u]] = A[u][v]: row u -> column a[u], column v -> row b[v]
            res.append([n + x for x in a] + list(b))
    for phi in res:                                   # verify
        pos = {}
        for u in range(n):
            for v in range(m):
                x, y = phi[u], phi[n + v]
                r, c = (x, y - n) if x < n else (y, x - n)
                assert A[r][c] == A[u][v]
    return res


# ---------------------------------------------------------------- encoding
def lex_geq(cl, var, xs, ys, guard=None):
    """clauses for  xs >=lex ys  (index 0 most significant, true > false); skipped positions with the same variable."""
    eq = None
    for x, y in zip(xs, ys):
        if x == y:
            continue
        base = ([-guard] if guard else []) + ([-eq] if eq else [])
        cl.append(base + [x, -y])
        e2 = var()
        b2 = [-eq] if eq else []
        cl.append(b2 + [x, y, e2]); cl.append(b2 + [-x, -y, e2])
        eq = e2


def encode(P, inputs, T, a, sym=True, autos=(), autodepth=1):
    """inputs: list of cell masks (free input wires).  Returns (clauses, nvars, info).
    autos: automorphisms of the graph as permutations of the input indices (lex-leader on the first
    `autodepth` gates: M5)."""
    N = len(inputs)
    full = (1 << P) - 1
    assert T & ~full == 0 and a >= 1
    cnt = [0]

    def var():
        cnt[0] += 1
        return cnt[0]
    cl = []
    free_out = [i for i in range(N) if inputs[i] and (inputs[i] & ~T) == 0]
    covered = 0
    for i in free_out:
        covered |= inputs[i]
    D = T & ~covered
    ins_at = [[i for i in range(N) if (inputs[i] >> p) & 1] for p in range(P)]
    Ls = [[var() for _ in range(N + j)] for j in range(a)]
    Rs = [[var() for _ in range(N + j)] for j in range(a)]
    Os = [var() for _ in range(a)]
    V = [[var() for _ in range(P)] for j in range(a)]
    for j in range(a):
        for side, S in ((0, Ls), (1, Rs)):
            X = [var() for _ in range(P)]
            for p in range(P):
                lits = [S[j][i] for i in ins_at[p]]
                for k in range(j):
                    t = var()
                    cl.append([-t, S[j][N + k]]); cl.append([-t, V[k][p]]); cl.append([t, -S[j][N + k], -V[k][p]])
                    lits.append(t)
                for l in lits:
                    cl.append([-l, X[p]])
                cl.append([-X[p]] + lits)
            if side == 0:
                XL = X
            else:
                XR = X
        for p in range(P):
            cl.append([-V[j][p], XL[p]]); cl.append([-V[j][p], XR[p]]); cl.append([V[j][p], -XL[p], -XR[p]])
    for p in range(P):
        if (D >> p) & 1:
            ws = []
            for k in range(a):
                w = var()
                cl.append([-w, Os[k]]); cl.append([-w, V[k][p]])
                ws.append(w)
            cl.append(ws)
        elif not (T >> p) & 1:
            for k in range(a):
                cl.append([-Os[k], -V[k][p]])
    if sym:
        cl.append([Os[a - 1]])                                             # M1
        for k in range(a - 1):
            cl.append([Os[k]] + [Ls[j][N + k] for j in range(k + 1, a)] + [Rs[j][N + k] for j in range(k + 1, a)])
        for j in range(a):
            for i in range(N + j):
                cl.append([-Ls[j][i], -Rs[j][i]])                          # M2
                cl.append([-Rs[j][i]] + Ls[j][:i])                         # M3
        for j in range(a - 1):                                             # M4
            K = N + j
            c = var()                                                      # c <-> gate j+1 does not read gate j
            cl.append([-c, -Ls[j + 1][K]]); cl.append([-c, -Rs[j + 1][K]]); cl.append([c, Ls[j + 1][K], Rs[j + 1][K]])
            lex_geq(cl, var, Ls[j][:K], Ls[j + 1][:K], guard=c)
        for phi in autos:                                                  # M5: string >= its image under phi
            assert len(phi) == N
            inv = [0] * N
            for i in range(N):
                inv[phi[i]] = i
            xs = []; ys = []
            for j in range(min(autodepth, a)):
                for S in (Ls, Rs):
                    xs += S[j]
                    ys += [S[j][inv[i]] for i in range(N)] + S[j][N:]
            lex_geq(cl, var, xs, ys)
    return cl, cnt[0], dict(Ls=Ls, Rs=Rs, Os=Os, free_out=free_out, N=N)


def encode2(P, inputs, T, a, sym=True, autos=(), autodepth=1, strip=False):
    """second encoding ("B"): the LAST AND gate is the output and equals the graph (Lemma 3 of docs/andtab.md:
    T has a circuit with a AND gates iff T = X & Y with X, Y in the closure after a-1 gates), so its cell values
    are constants.  Gates 0..a-2 are encoded as in encode().  Conditions used when sym (minimum circuits only):
    M1 every gate but the last is read by a later gate; M2/M3 on gates 0..a-2, L >=lex R on the last gate;
    M4 on pairs j, j+1 <= a-2; M5 automorphisms; M6 the last gate reads, on BOTH sides, every free input that
    lies inside the graph and every gate that lies inside the graph (adding g <= T to both sides changes nothing)."""
    N = len(inputs)
    full = (1 << P) - 1
    assert T & ~full == 0 and a >= 1
    cnt = [0]

    def var():
        cnt[0] += 1
        return cnt[0]
    cl = []
    ins_at = [[i for i in range(N) if (inputs[i] >> p) & 1] for p in range(P)]
    Ls = [[var() for _ in range(N + j)] for j in range(a)]
    Rs = [[var() for _ in range(N + j)] for j in range(a)]
    V = [[var() for _ in range(P)] for j in range(a - 1)]
    for j in range(a - 1):                         # inner gates
        Xs = []
        for S in (Ls, Rs):
            X = [var() for _ in range(P)]
            for p in range(P):
                lits = [S[j][i] for i in ins_at[p]]
                for k in range(j):
                    t = var()
                    cl.append([-t, S[j][N + k]]); cl.append([-t, V[k][p]]); cl.append([t, -S[j][N + k], -V[k][p]])
                    lits.append(t)
                for l in lits:
                    cl.append([-l, X[p]])
                cl.append([-X[p]] + lits)
            Xs.append(X)
        for p in range(P):
            cl.append([-V[j][p], Xs[0][p]]); cl.append([-V[j][p], Xs[1][p]]); cl.append([V[j][p], -Xs[0][p], -Xs[1][p]])
        if sym and strip:
            # M7 (semantic form of M2, inner gates): no generator of L_j lies inside OR(R_j), and vice versa
            # (if val(i) <= Y then (X' u i) n Y = (X' n Y) u val(i): strip i exactly as in M2).
            for S, Xo in ((Ls, Xs[1]), (Rs, Xs[0])):
                for i in range(N):
                    cells = [p for p in range(P) if (inputs[i] >> p) & 1]
                    cl.append([-S[j][i]] + [-Xo[p] for p in cells])
                for k in range(j):
                    ds = []
                    for p in range(P):
                        d = var()
                        cl.append([-d, V[k][p]]); cl.append([-d, -Xo[p]])
                        ds.append(d)
                    cl.append([-S[j][N + k]] + ds)
    j = a - 1                                      # last gate = T
    for p in range(P):
        if (T >> p) & 1:
            for S in (Ls, Rs):
                lits = [S[j][i] for i in ins_at[p]]
                for k in range(j):
                    t = var()
                    cl.append([-t, S[j][N + k]]); cl.append([-t, V[k][p]])
                    lits.append(t)
                cl.append(lits)
        else:
            A = [[-Ls[j][i]] for i in ins_at[p]] + [[-Ls[j][N + k], -V[k][p]] for k in range(j)]
            B = [[-Rs[j][i]] for i in ins_at[p]] + [[-Rs[j][N + k], -V[k][p]] for k in range(j)]
            for x in A:
                for y in B:
                    cl.append(sorted(set(x + y)))
    free_in = [i for i in range(N) if inputs[i] and (inputs[i] & ~T) == 0]
    if sym:
        for i in free_in:                                                  # M6 (inputs)
            cl.append([Ls[j][i]]); cl.append([Rs[j][i]])
        for k in range(a - 1):                                             # M6 (gates): sub <-> gate k inside T
            sub = var()
            outside = [V[k][p] for p in range(P) if not (T >> p) & 1]
            for v in outside:
                cl.append([-sub, -v])
            cl.append([sub] + outside)
            cl.append([-sub, Ls[j][N + k]]); cl.append([-sub, Rs[j][N + k]])
        for k in range(a - 1):                                             # M1
            cl.append([Ls[jj][N + k] for jj in range(k + 1, a)] + [Rs[jj][N + k] for jj in range(k + 1, a)])
        for jj in range(a - 1):
            for i in range(N + jj):
                cl.append([-Ls[jj][i], -Rs[jj][i]])                        # M2
                cl.append([-Rs[jj][i]] + Ls[jj][:i])                       # M3
        lex_geq(cl, var, Ls[j], Rs[j])                                     # M3 for the last gate
        for jj in range(a - 2):                                            # M4 (both gates before the last)
            K = N + jj
            c = var()
            cl.append([-c, -Ls[jj + 1][K]]); cl.append([-c, -Rs[jj + 1][K]]); cl.append([c, Ls[jj + 1][K], Rs[jj + 1][K]])
            lex_geq(cl, var, Ls[jj][:K], Ls[jj + 1][:K], guard=c)
        for phi in autos:                                                  # M5
            assert len(phi) == N
            inv = [0] * N
            for i in range(N):
                inv[phi[i]] = i
            xs = []; ys = []
            for jj in range(min(autodepth, a)):
                for S in (Ls, Rs):
                    xs += S[jj]
                    ys += [S[jj][inv[i]] for i in range(N)] + S[jj][N:]
            lex_geq(cl, var, xs, ys)
    return cl, cnt[0], dict(Ls=Ls, Rs=Rs, Os=None, free_out=[], N=N, last_only=True)


def encode3(n, m, T, a, sym=True, autos=(), autodepth=1):
    """third encoding ("F", factorised; plain inputs only: rows 0..n-1, columns n..n+m-1).
    Lemma 8 of docs/andtab.md: replace every AND gate j by ONE of its two ORs, side s_j in {L, R}.  The circuit
    then has no AND gate and computes a union of rows and columns W_s, and  T = intersection over all 2^a
    choices s of W_s.  Whether input i belongs to gate j after the replacement depends only on s_0..s_j:
        val[i][j][s] <-> (i in S_j) or OR_{k<j} (gate k in S_j and val[i][k][s restricted to 0..k]),  S_j = L_j or R_j by s_j.
    With the last gate as the output:  T(u,v) = AND_s ( val[u][a-1][s] or val[n+v][a-1][s] ).
    No cell variables: (n+m) * (2^(a+1) - 2) value variables, one binary clause per (one-cell, s)."""
    N = n + m
    assert a >= 1
    cnt = [0]

    def var():
        cnt[0] += 1
        return cnt[0]
    cl = []
    Ls = [[var() for _ in range(N + j)] for j in range(a)]
    Rs = [[var() for _ in range(N + j)] for j in range(a)]
    val = [[[var() for _ in range(1 << (j + 1))] for j in range(a)] for i in range(N)]
    for i in range(N):
        for j in range(a):
            for s in range(1 << (j + 1)):
                S = Rs[j] if (s >> j) & 1 else Ls[j]
                lits = [S[i]]
                for k in range(j):
                    t = var(); w = val[i][k][s & ((1 << (k + 1)) - 1)]
                    cl.append([-t, S[N + k]]); cl.append([-t, w]); cl.append([t, -S[N + k], -w])
                    lits.append(t)
                x = val[i][j][s]
                for l in lits:
                    cl.append([-l, x])
                cl.append([-x] + lits)
    for u in range(n):
        for v in range(m):
            if (T >> (u * m + v)) & 1:
                for s in range(1 << a):
                    cl.append([val[u][a - 1][s], val[n + v][a - 1][s]])
            else:
                zs = []
                for s in range(1 << a):
                    z = var()
                    cl.append([-z, -val[u][a - 1][s]]); cl.append([-z, -val[n + v][a - 1][s]])
                    zs.append(z)
                cl.append(zs)
    j = a - 1
    if sym:
        for k in range(a - 1):                                             # M1
            cl.append([Ls[jj][N + k] for jj in range(k + 1, a)] + [Rs[jj][N + k] for jj in range(k + 1, a)])
        for jj in range(a - 1):
            for i in range(N + jj):
                cl.append([-Ls[jj][i], -Rs[jj][i]])                        # M2
                cl.append([-Rs[jj][i]] + Ls[jj][:i])                       # M3
        lex_geq(cl, var, Ls[j], Rs[j])                                     # M3 for the last gate
        for jj in range(a - 2):                                            # M4
            K = N + jj
            c = var()
            cl.append([-c, -Ls[jj + 1][K]]); cl.append([-c, -Rs[jj + 1][K]]); cl.append([c, Ls[jj + 1][K], Rs[jj + 1][K]])
            lex_geq(cl, var, Ls[jj][:K], Ls[jj + 1][:K], guard=c)
        for phi in autos:                                                  # M5
            assert len(phi) == N
            inv = [0] * N
            for i in range(N):
                inv[phi[i]] = i
            xs = []; ys = []
            for jj in range(min(autodepth, a)):
                for S in (Ls, Rs):
                    xs += S[jj]
                    ys += [S[jj][inv[i]] for i in range(N)] + S[jj][N:]
            lex_geq(cl, var, xs, ys)
    return cl, cnt[0], dict(Ls=Ls, Rs=Rs, Os=None, free_out=[], N=N, last_only=True)


def decode(model, info, a):
    pos = set(v for v in model if v > 0)
    N = info['N']
    L = [[i for i in range(N + j) if info['Ls'][j][i] in pos] for j in range(a)]
    R = [[i for i in range(N + j) if info['Rs'][j][i] in pos] for j in range(a)]
    if info.get('last_only'):
        out = [N + a - 1]
    else:
        out = list(info['free_out']) + [N + k for k in range(a) if info['Os'][k] in pos]
    return L, R, out


def run_solver(clauses, solver='cadical195', timeout=0, chunk=20000):
    """returns (True/False/None, model, conflicts).  None = time limit hit (checked every `chunk` conflicts)."""
    from pysat.solvers import Solver
    S = Solver(name=solver, bootstrap_with=clauses)
    t0 = time.time()
    try:
        if not timeout:
            r = S.solve()
        else:
            while True:
                S.conf_budget(chunk)
                r = S.solve_limited()
                if r is not None or time.time() - t0 > timeout:
                    break
        confl = None
        try:
            confl = S.accum_stats().get('conflicts')
        except Exception:
            pass
        return r, (S.get_model() if r else None), confl
    finally:
        S.delete()


def level0(P, inputs, T):
    """T is a union of free inputs (And = 0)?  returns the list of inputs or None."""
    idx = [i for i in range(len(inputs)) if (inputs[i] & ~T) == 0 and inputs[i]]
    u = 0
    for i in idx:
        u |= inputs[i]
    return idx if u == T else None


def enc_inputs(n, m):
    """the free encoder wires: row-bit sets {u : bit_i(u) = b} and column-bit sets, as (cell masks, names, members)
    where members[e] = the plain input indices (rows / columns) whose union the wire is."""
    G = andlib.gens(n, m)
    res = []; names = []; members = []
    for side, sz, off, nm in ((0, n, 0, 'rb'), (1, m, n, 'cb')):
        b = 0
        while (1 << b) < sz:
            for val in (0, 1):
                s = 0; mem = []
                for x in range(sz):
                    if ((x >> b) & 1) == val:
                        s |= G[off + x]; mem.append(off + x)
                res.append(s); names.append('%s%d=%d' % (nm, b, val)); members.append(mem)
            b += 1
    return res, names, members


def and_search(n, m, T, lo=0, amax=8, timeout=0, use_core=True, sym=True, solver='cadical195', enc=False, log=None,
               nautos=64, autodepth=1, model='B'):
    """iterative deepening.  Returns dict(lower=, upper=, exact=, witness=(L,R,out) for the ORIGINAL graph or None,
    steps=[(a, 'SAT'|'UNSAT'|'TIMEOUT', seconds, conflicts)], inputs=N).
    model: 'A' = encode() (output is an OR of gates), 'B' = encode2() (last gate is the graph)."""
    def say(s):
        if log:
            print(s, file=log, flush=True)
    if use_core and not enc:
        ci = andlib.core(n, m, T)
        n2, m2, T2 = ci[0], ci[1], ci[2]
    else:
        ci = None; n2, m2, T2 = n, m, T
    P = n2 * m2
    inputs = andlib.gens(n2, m2)
    if enc:
        inputs = inputs + enc_inputs(n2, m2)[0]
    steps = []
    autos = automorphisms(n2, m2, T2, nautos) if (sym and nautos and not enc and P) else []
    say('  core %dx%d, %d inputs, %d automorphisms used for symmetry breaking' % (n2, m2, len(inputs), len(autos)))
    res = dict(n=n, m=m, core=[n2, m2], lower=lo, upper=None, exact=False, witness=None, steps=steps, inputs=len(inputs), autos=len(autos))

    def finish(L, R, out):
        assert andlib.eval_wit(n2, m2, L, R, out, inputs) == T2, 'decoded witness is wrong (encoder bug)'
        if enc:
            # replace every encoder wire by the rows / columns it is the union of (free ORs): a plain witness
            mem = enc_inputs(n2, m2)[2]; N0 = n2 + m2; NE = len(mem)

            def conv(idx):
                r = set()
                for i in idx:
                    if i < N0: r.add(i)
                    elif i < N0 + NE: r.update(mem[i - N0])
                    else: r.add(i - NE)
                return sorted(r)
            res['witness_with_encoder_wires'] = (L, R, out)
            L, R, out = [conv(x) for x in L], [conv(x) for x in R], conv(out)
            assert andlib.eval_wit(n2, m2, L, R, out) == T2, 'substituting the encoder wires changed the function'
        if ci is not None:
            L, R, out = andlib.lift(n, m, ci, L, R, out)
            assert andlib.eval_wit(n, m, L, R, out) == T
        res['witness'] = (L, R, out); res['upper'] = len(L)
    z = level0(P, inputs, T2) if P else []
    if P == 0 or z is not None:
        finish([], [], z or [])
        res['lower'] = 0; res['exact'] = True
        steps.append((0, 'SAT', 0.0, 0))
        return res
    steps.append((0, 'UNSAT', 0.0, 0))
    a = max(lo, 1)
    res['lower'] = a
    while a <= amax:
        t0 = time.time()
        if model == 'F' and not enc:
            cl, nv, info = encode3(n2, m2, T2, a, sym, autos, autodepth)
        else:
            cl, nv, info = (encode if model == 'A' else encode2)(P, inputs, T2, a, sym, autos, autodepth)
        r, mdl, confl = run_solver(cl, solver, timeout)
        dt = time.time() - t0
        st = 'TIMEOUT' if r is None else ('SAT' if r else 'UNSAT')
        steps.append((a, st, round(dt, 2), confl))
        say('  a=%d: %s  (%d vars, %d clauses, %.1fs, %s conflicts)' % (a, st, nv, len(cl), dt, confl))
        if r is None:
            return res
        if r:
            L, R, out = decode(mdl, info, a)
            finish(L, R, out)
            res['exact'] = True
            return res
        a += 1
        res['lower'] = a
    return res


# ---------------------------------------------------------------- cover number of the zeros, fooling sets
def cov0_sat(n, m, T, timeout=0, solver='cadical195', kmax=None):
    """exact least number of all-zero rectangles covering the zeros of T (Boolean rank of the complement).
    Returns (lower, upper): equal when solved."""
    P = n * m; full = (1 << P) - 1
    Z = full & ~T
    if Z == 0:
        return 0, 0
    zc = [sum(1 << v for v in range(m) if not (T >> (u * m + v)) & 1) for u in range(n)]
    fs = fooling0(n, m, T)
    k = max(1, len(fs))
    ub = min(sum(1 for u in range(n) if zc[u]), sum(1 for v in range(m) if any((zc[u] >> v) & 1 for u in range(n))))
    while k < ub and (kmax is None or k <= kmax):
        cnt = [0]

        def var():
            cnt[0] += 1
            return cnt[0]
        cl = []
        A = [[var() for _ in range(n)] for _ in range(k)]; B = [[var() for _ in range(m)] for _ in range(k)]
        for r in range(k):
            for u in range(n):
                for v in range(m):
                    if (T >> (u * m + v)) & 1:
                        cl.append([-A[r][u], -B[r][v]])
        for u in range(n):
            for v in range(m):
                if not (T >> (u * m + v)) & 1:
                    ws = []
                    for r in range(k):
                        w = var(); cl.append([-w, A[r][u]]); cl.append([-w, B[r][v]]); ws.append(w)
                    cl.append(ws)
        for i, (u, v) in enumerate(fs[:k]):          # symmetry breaking: fooling cell i lies in rectangle i
            cl.append([A[i][u]]); cl.append([B[i][v]])
        r, _, _ = run_solver(cl, solver, timeout)
        if r is None:
            return k, ub
        if r:
            return k, k
        k += 1
    return k, ub


def fooling0(n, m, T, tries=200, seed=1):
    """a large 0-fooling set: zero cells (u_i, v_i) with T(u_i, v_j) = 1 or T(u_j, v_i) = 1 for all i != j (greedy,
    randomised restarts, deterministic for a fixed seed).  Any such set is a certificate that cov0 >= its size."""
    zeros = [(u, v) for u in range(n) for v in range(m) if not (T >> (u * m + v)) & 1]

    def ok(a, b):
        return ((T >> (a[0] * m + b[1])) & 1) or ((T >> (b[0] * m + a[1])) & 1)
    rng = random.Random(seed)
    best = []
    for t in range(tries):
        order = zeros[:]
        if t:
            rng.shuffle(order)
        cur = []
        for z in order:
            if all(ok(z, y) for y in cur):
                cur.append(z)
        if len(cur) > len(best):
            best = cur
    return best


def check_fooling0(n, m, T, fs):
    for i, a in enumerate(fs):
        assert not (T >> (a[0] * m + a[1])) & 1
        for b in fs[:i]:
            assert ((T >> (a[0] * m + b[1])) & 1) or ((T >> (b[0] * m + a[1])) & 1)
    return True


# ---------------------------------------------------------------- families and explicit constructions
def popc(x):
    return bin(x).count('1')


FAMILIES = {
    'crown': lambda u, v: u != v,
    'match': lambda u, v: u == v,
    'ip': lambda u, v: popc(u & v) & 1 == 1,
    'disj': lambda u, v: (u & v) == 0,
    'inter': lambda u, v: (u & v) != 0,
    'gt': lambda u, v: u > v,
}


def family_rows(name, n):
    if name.startswith('rand'):
        rng = random.Random(1000 * n + int(name[4:] or 0))
        return [rng.getrandbits(n) for _ in range(n)]
    f = FAMILIES[name]
    return [sum(1 << v for v in range(n) if f(u, v)) for u in range(n)]


class Builder:
    """tiny DSL for explicit constructions: a wire is a frozenset of generator indices (their OR); OR is `|`."""
    def __init__(self, n, m):
        self.n, self.m = n, m; self.L = []; self.R = []

    def rows(self, pred):
        return frozenset(u for u in range(self.n) if pred(u))

    def cols(self, pred):
        return frozenset(self.n + v for v in range(self.m) if pred(v))

    def AND(self, x, y):
        self.L.append(sorted(x)); self.R.append(sorted(y))
        return frozenset([self.n + self.m + len(self.L) - 1])

    def wit(self, out):
        return self.L, self.R, sorted(out)


def construct(name, n):
    """explicit circuit for the family at n = 2^k: (L, R, out, description) or None."""
    k = n.bit_length() - 1
    if 1 << k != n or name.startswith('rand'):
        return None
    B = Builder(n, n)
    r = lambda i, b: B.rows(lambda u: ((u >> i) & 1) == b)
    c = lambda i, b: B.cols(lambda v: ((v >> i) & 1) == b)
    if name == 'crown':          # u != v  iff  some bit differs:  (u_i=0 or v_i=0) and (u_i=1 or v_i=1)
        out = frozenset()
        for i in range(k):
            out |= B.AND(r(i, 0) | c(i, 0), r(i, 1) | c(i, 1))
        return B.wit(out) + ('bit partition: one AND per index bit',)
    if name == 'inter':
        out = frozenset()
        for i in range(k):
            out |= B.AND(r(i, 1), c(i, 1))
        return B.wit(out) + ('OR over bits of (u_i AND v_i)',)
    if name == 'disj':           # AND over bits of the free OR (u_i=0 or v_i=0)
        acc = r(0, 0) | c(0, 0)
        for i in range(1, k):
            acc = B.AND(acc, r(i, 0) | c(i, 0))
        return B.wit(acc) + ('chain of k-1 ANDs of the free ORs (u_i=0 or v_i=0)',)
    if name == 'gt':             # u > v, from the low bit up: G = (u_i > v_i) or ((u_i >= v_i) and G')
        acc = B.AND(r(0, 1), c(0, 0))
        for i in range(1, k):
            acc = B.AND(r(i, 1), c(i, 0)) | B.AND(r(i, 1) | c(i, 0), acc)
        return B.wit(acc) + ('bitwise comparison, 2 ANDs per bit after the first',)
    if name == 'match':          # all bits equal
        eq = lambda i: B.AND(r(i, 0) | c(i, 1), r(i, 1) | c(i, 0))
        acc = eq(0)
        for i in range(1, k):
            acc = B.AND(acc, eq(i))
        return B.wit(acc) + ('AND over bits of (u_i = v_i): 2k-1 ANDs',)
    if name == 'ip':             # pair (parity, co-parity): P' = (P and D) or (N and E), N' = (N and D) or (P and E)
        E = B.AND(r(0, 1), c(0, 1)); Pw = E; Nw = r(0, 0) | c(0, 0)
        for i in range(1, k):
            E = B.AND(r(i, 1), c(i, 1)); Dw = r(i, 0) | c(i, 0)
            P2 = B.AND(Pw, Dw) | B.AND(Nw, E)
            if i < k - 1:
                N2 = B.AND(Nw, Dw) | B.AND(Pw, E)
                Nw = N2
            Pw = P2
        return B.wit(Pw) + ('parity recursion with both polarities: 5k-6 ANDs',)
    return None


def double_wit(fam, n, L, R, out):
    """circuit for match_{2n} / gt_{2n} from a circuit (L, R, out) for the n x n graph: the old circuit is run on the
    low parts (u mod n, v mod n) of the indices (every row/column is replaced by its two copies) and the top bit is
    handled with 2 more AND gates:
      match: [u_top = v_top] (one AND of two free ORs) AND old
      gt:    (u_top = 1 and v_top = 0)  OR  ((u_top = 1 or v_top = 0) AND old)."""
    def conv(idx):
        r = []
        for i in idx:
            if i < n: r += [i, i + n]
            elif i < 2 * n: r += [2 * n + (i - n), 3 * n + (i - n)]
            else: r.append(4 * n + (i - 2 * n))
        return sorted(r)
    L2 = [conv(x) for x in L]; R2 = [conv(x) for x in R]; o2 = conv(out)
    a = len(L2); g = 4 * n + a
    rows0 = list(range(0, n)); rows1 = list(range(n, 2 * n))
    cols0 = list(range(2 * n, 3 * n)); cols1 = list(range(3 * n, 4 * n))
    if fam == 'match':
        L2.append(rows0 + cols1); R2.append(rows1 + cols0)          # gate g: top bits equal
        L2.append(o2); R2.append([g])
        return L2, R2, [g + 1]
    if fam == 'gt':
        L2.append(rows1); R2.append(cols0)                          # gate g: u_top > v_top
        L2.append(rows1 + cols0); R2.append(o2)                     # gate g+1: u_top >= v_top and low parts greater
        return L2, R2, [g, g + 1]
    raise ValueError(fam)


# ---------------------------------------------------------------- CLI
def report(n, m, rows, res, name=None, ckt_path=None, as_json=False):
    T = andlib.rows_to_mask(rows, m)
    out = dict(name=name, n=n, m=m, rows=rows, lower=res['lower'], upper=res['upper'], exact=res['exact'], core=res['core'],
               steps=res['steps'])
    if res['witness'] is not None:
        L, R, o = res['witness']
        ckt, n_and, n_or = andlib.wit_to_ckt(n, m, L, R, o)
        ok = andlib.cktcheck(andlib.graph_spec(n, m, rows), ckt, 'ao')
        assert ok and n_and == res['upper'], 'cktcheck refused the witness'
        out.update(witness=dict(L=L, R=R, out=o), ckt_ands=n_and, ckt_gates=n_and + n_or, cktcheck='OK')
        if ckt_path:
            open(ckt_path, 'w').write(ckt)
    if as_json:
        print(json.dumps(out))
    else:
        if res['exact']:
            print('And = %d (exact: a = %d refuted; witness checked by cktcheck, %d AND + %d OR gates)'
                  % (res['upper'], res['upper'] - 1, out['ckt_ands'], out['ckt_gates'] - out['ckt_ands']) if res['upper'] else 'And = 0 (union of rows and columns)')
        else:
            print('And >= %d (a = %d not decided within the limits)' % (res['lower'], res['lower']))
        if res['witness'] is not None:
            print('witness L=%s R=%s out=%s' % (out['witness']['L'], out['witness']['R'], out['witness']['out']))
    return out


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)

    def common(p):
        p.add_argument('--lo', type=int, default=0, help='start the deepening here (ONLY if And >= lo is already proved)')
        p.add_argument('--amax', type=int, default=8)
        p.add_argument('--timeout', type=float, default=0, help='seconds per SAT call (0 = none)')
        p.add_argument('--enc', action='store_true', help='also give the row/column bit-set wires as free inputs')
        p.add_argument('--no-core', action='store_true', help='do not remove full rows/columns and twins first')
        p.add_argument('--no-sym', action='store_true', help='drop M1-M5 (pure model: any a, not only the minimum)')
        p.add_argument('--autos', type=int, default=64, help='use up to this many automorphisms of each kind (0 = none)')
        p.add_argument('--autodepth', type=int, default=1, help='lex-leader over the first this-many gates')
        p.add_argument('--model', default='B', choices=['A', 'B', 'F'],
                       help='CNF encoding: A = output is an OR of gates, B = last gate is the graph, F = factorised (no cell variables)')
        p.add_argument('--solver', default='cadical195')
        p.add_argument('--ckt', default=None)
        p.add_argument('--json', action='store_true')
    g = sub.add_parser('graph'); common(g)
    g.add_argument('--rows', required=True, help='comma separated; bit v of rows[u] = A u v')
    g.add_argument('--m', type=int, default=0)
    g.add_argument('--hex', action='store_true')
    f = sub.add_parser('family'); common(f)
    f.add_argument('name'); f.add_argument('n', type=int)
    t = sub.add_parser('table')
    t.add_argument('table'); t.add_argument('--every', type=int, default=1); t.add_argument('--only', default='')
    t.add_argument('--timeout', type=float, default=0); t.add_argument('--budget', type=float, default=0)
    t.add_argument('--solver', default='cadical195'); t.add_argument('--no-core', action='store_true')
    t.add_argument('--offset', type=int, default=0)
    t.add_argument('--no-sym', action='store_true', help='drop M1-M4: the pure normal-form model')
    t.add_argument('--quiet', action='store_true')
    t.add_argument('--model', default='B', choices=['A', 'B', 'F'])
    a = ap.parse_args()
    if a.cmd in ('graph', 'family'):
        if a.cmd == 'graph':
            rows = [int(x, 16 if a.hex else 0) for x in a.rows.split(',')]
            n = len(rows); m = a.m or max(n, max(rows).bit_length())
            name = None
        else:
            n = m = a.n; rows = family_rows(a.name, n); name = '%s_%d' % (a.name, n)
        T = andlib.rows_to_mask(rows, m)
        res = and_search(n, m, T, lo=a.lo, amax=a.amax, timeout=a.timeout, use_core=not a.no_core, sym=not a.no_sym,
                         solver=a.solver, enc=a.enc, log=sys.stderr, nautos=a.autos, autodepth=a.autodepth, model=a.model)
        report(n, m, rows, res, name, a.ckt, a.json)
        return
    if a.cmd == 'table':
        Tb = json.load(open(a.table)); n, m = Tb['n'], Tb['m']
        only = set(int(x) for x in a.only.split(',')) if a.only else None
        t00 = time.time(); nok = nbad = nto = 0; tot_calls = 0
        for c in Tb['classes']:
            if only is not None and c['id'] not in only: continue
            if only is None and (c['id'] - a.offset) % a.every: continue
            if a.budget and time.time() - t00 > a.budget:
                print('budget exhausted; stopping before class %d' % c['id']); break
            T = andlib.rows_to_mask(c['rows'], m)
            t0 = time.time()
            res = and_search(n, m, T, lo=0, amax=c['and']['size'], timeout=a.timeout, use_core=not a.no_core, sym=not a.no_sym, solver=a.solver, model=a.model)
            tot_calls += len(res['steps'])
            if res['exact'] and res['upper'] == c['and']['size']:
                status = 'OK'; nok += 1
            elif any(s[1] == 'TIMEOUT' for s in res['steps']):
                status = 'TIMEOUT'; nto += 1
            else:
                status = 'MISMATCH'; nbad += 1
            if status != 'OK' or (c['and']['size'] >= 3 and not a.quiet) or only is not None:
                print('class %d rows %s: table %d, SAT says %s  %s (%.2fs) steps %s' % (c['id'], c['rows'], c['and']['size'],
                      res['upper'] if res['exact'] else '>= %d' % res['lower'], status, time.time() - t0, res['steps']), flush=True)
        print('summary: %d classes confirmed (UNSAT at every a < And, SAT at And, witness re-evaluated), %d mismatches, %d timeouts, %d SAT calls, %.1fs'
              % (nok, nbad, nto, tot_calls, time.time() - t00))
        sys.exit(1 if nbad else 0)


if __name__ == '__main__':
    main()
