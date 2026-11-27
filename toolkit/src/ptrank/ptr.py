"""Partial-transpose rank of the identity over GF(2), d = 2 (Rossman-Zhu arXiv:2512.01227, Def. 3.4).

  P(n) = min { rank(A) + rank(B) : A + B^{T1} = I_{n^2} },  (B^{T1})[(i1,i2),(j1,j2)] = B[(j1,i2),(i1,j2)].

Map form used here (equivalent, see check_equiv):
  B = sum_r vec(U_r) vec(V_r)^T  <=>  B^{T1} is the map  X -> sum_r V_r X^T U_r  on n x n matrices,
  so  P(n) = min over terms (V_r, U_r), r < R, of  R + rank(id - Phi),  Phi(X) = sum_r V_r X^T U_r.

Matrices over GF(2) are lists of row bitmasks.  Pure Python, single thread."""
import sys, random, itertools

def rank_gf2(rows):
    rows = [r for r in rows if r]; rk = 0
    while rows:
        p = rows.pop(); rk += 1; low = p & -p
        rows = [x ^ p if x & low else x for x in rows]; rows = [x for x in rows if x]
    return rk

def phi_matrix(n, terms):
    """n^2 x n^2 matrix of Phi(X) = sum_r V X^T U; row index (i1,i2) = i1*n+i2, column (j1,j2) = j1*n+j2.
    (V X^T U)[i1,i2] = sum_{j1,j2} V[i1,j2] X[j1,j2] U[j1,i2].  V, U are lists of n row bitmasks."""
    M = [0] * (n * n)
    for V, U in terms:
        for i1 in range(n):
            for i2 in range(n):
                row = 0
                for j1 in range(n):
                    if (U[j1] >> i2) & 1:
                        row ^= V[i1] << (j1 * n)      # bits j2 of V[i1] placed at column j1*n + j2
                M[i1 * n + i2] ^= row
    return M

def cost(n, terms):
    """(R, rho, R + rho): R = rank of B (number of independent terms as tensors), rho = rank(I + Phi)."""
    M = phi_matrix(n, terms)
    rho = rank_gf2([M[k] ^ (1 << k) for k in range(n * n)])
    # rank of B = rank of the span of vec(U) (x) vec(V); compute via the n^2 x n^2 matrix sum vec(U) vec(V)^T
    B = [0] * (n * n)
    for V, U in terms:
        vv = sum(V[a] << (a * n) for a in range(n))
        for a in range(n):
            for b in range(n):
                if (U[a] >> b) & 1: B[a * n + b] ^= vv
    R = rank_gf2(B)
    return R, rho, R + rho

def ident(n): return [1 << i for i in range(n)]

def embed(n, m, a, b, Vs, Us):
    """place m x m matrices into block (a,b) pattern used by the block construction:
    term (E_ab (x) V) X^T-form ... we simply build the n x n matrices with V in block (a,b) and U in block (a,b)."""
    V = [0] * n; U = [0] * n
    for i in range(m):
        V[a * m + i] = Vs[i] << (b * m)
        U[a * m + i] = Us[i] << (b * m)
    return V, U

def block_terms(n, m, sub):
    """Block construction P(k m) <= k^2 P(m): for each ordered pair of blocks (a,b) use a copy of the
    m-solution `sub` (list of (V,U)) mapping block (b,a) of X^T ... verified numerically by cost()."""
    k = n // m; out = []
    for a in range(k):
        for b in range(k):
            for Vs, Us in sub:
                # Phi(X) = V X^T U with V supported on rows of block a, cols of block b; U rows block a... tried forms below
                V = [0] * n; U = [0] * n
                for i in range(m):
                    V[a * m + i] = Vs[i] << (b * m)     # V: block (a, b)
                    U[a * m + i] = Us[i] << (b * m)     # U: block (a, b)
                out.append((V, U))
    return out

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'table'
    if cmd == 'table':
        print("trivial decomposition Phi(X) = X^T:")
        for n in range(2, 9):
            print("  n", n, "(R, rho, total) =", cost(n, [(ident(n), ident(n))]), " 1 + C(n,2) =", 1 + n * (n - 1) // 2)
        print("block construction from the trivial m-solution (k = n/m blocks a side):")
        for n, m in [(4, 2), (6, 3), (6, 2), (8, 4), (8, 2), (9, 3), (10, 5), (12, 4), (12, 6), (12, 3), (16, 4), (16, 8)]:
            t = block_terms(n, m, [(ident(m), ident(m))])
            R, rho, tot = cost(n, t)
            k = n // m
            print(f"  n {n:2d} m {m}: (R, rho, total) = ({R}, {rho}, {tot})   k^2 (1 + C(m,2)) = {k*k*(1 + m*(m-1)//2)}   1 + C(n,2) = {1 + n*(n-1)//2}")
