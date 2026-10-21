"""Check the Q3 counterexample to interior-cover excision for (J_1, box) cubical homology.

A graph is the closure space c(S) = S u N(S).  A singular n-cube is a map
{0,1}^n -> V sending cube edges to edges or single vertices (box-product continuity).
Chains are normalized: cubes constant along some coordinate are zero.
"""
from itertools import product

P = 2_147_483_647  # rank mod a large prime; ranks agree with Q for these small complexes


def cubes(closed_nbhd, verts, n):
    """All maps {0,1}^n -> verts with sigma(x ^ e_i) in N[sigma(x)]."""
    out, size = [], 1 << n

    def extend(partial):
        x = len(partial)
        if x == size:
            out.append(tuple(partial))
            return
        for v in verts:
            if all(v in closed_nbhd[partial[x ^ (1 << i)]] for i in range(n) if x >> i & 1):
                extend(partial + [v])

    extend([])
    return out


def degenerate(s, n):
    return any(all(s[x] == s[x | 1 << i] for x in range(1 << n) if not x >> i & 1) for i in range(n))


def face(s, n, i, b):
    """Restrict coordinate i to b; remaining coordinates keep their order."""
    res = []
    for y in range(1 << (n - 1)):
        low, high = y & ((1 << i) - 1), y >> i
        res.append(s[(high << (i + 1)) | (b << i) | low])
    return tuple(res)


def boundary(s, n):
    out = {}
    for i in range(n):
        sign = -1 if i % 2 == 0 else 1  # (-1)^(i+1) with i starting at 0
        for b, sb in ((0, sign), (1, -sign)):
            f = face(s, n, i, b)
            if not degenerate(f, n - 1):
                out[f] = out.get(f, 0) + sb
    return out


def rank_mod_p(rows):
    """Rank of a sparse matrix given as a list of {col: val} dicts."""
    pivots, r = {}, 0
    for row in rows:
        row = {c: v % P for c, v in row.items() if v % P}
        while row:
            c = min(row)
            if c not in pivots:
                inv = pow(row[c], P - 2, P)
                pivots[c] = {k: v * inv % P for k, v in row.items()}
                r += 1
                break
            prow, f = pivots[c], row[c]
            for k, v in prow.items():
                row[k] = (row.get(k, 0) - f * v) % P
                if row[k] == 0:
                    del row[k]
    return r


def betti(cells_by_dim, top):
    """Betti numbers b_0..b_{top-1} of the complex spanned by the given basis cells."""
    ranks = {}
    for n in range(1, top + 1):
        idx = {c: k for k, c in enumerate(cells_by_dim[n - 1])}
        rows = [{idx[f]: v for f, v in boundary(s, n).items() if f in idx} for s in cells_by_dim[n]]
        ranks[n] = rank_mod_p(rows)
    return [len(cells_by_dim[n]) - ranks.get(n, 0) - ranks[n + 1] for n in range(top)]


def complex_on(cube_lists, keep):
    """Normalized cubes satisfying keep(image)."""
    return {n: [s for s in cs if not degenerate(s, n) and keep(set(s))] for n, cs in cube_lists.items()}


def main():
    verts = list(range(8))  # Q3: vertices are 3-bit strings
    N = {v: {v} | {v ^ (1 << i) for i in range(3)} for v in verts}
    TOP = 3  # 3-cubes are needed for H_2
    all_cubes = {n: cubes(N, verts, n) for n in range(TOP + 1)}
    print("singular cubes in Q3 by dimension:", {n: len(c) for n, c in all_cubes.items()})
    for s in all_cubes[3]:  # sign convention sanity check: d o d = 0
        dd = {}
        for f, v in boundary(s, 3).items():
            for g, w in boundary(f, 2).items():
                dd[g] = dd.get(g, 0) + v * w
        assert not any(dd.values()), "boundary of boundary is not zero"

    X = set(verts)
    A = X - {0b111}
    B = X - {0b000}
    L = A & B
    interior = lambda S: {v for v in verts if N[v] <= S}
    assert interior(A) | interior(B) == X, "not an interior cover"
    print("i(A) =", sorted(interior(A)), " i(B) =", sorted(interior(B)))

    def absolute(S):
        return betti(complex_on(all_cubes, lambda im: im <= S), TOP)

    def relative(S, T):  # H(S, T), T a subset of S
        return betti(complex_on(all_cubes, lambda im: im <= S and not im <= T), TOP)

    for name, S in (("X=Q3", X), ("A=Q3-111", A), ("B=Q3-000", B), ("L=A&B", L)):
        print(f"H_0..2({name}) ranks:", absolute(S))
    hBL, hXA = relative(B, L), relative(X, A)
    print("H_0..2(B, L) ranks:", hBL)
    print("H_0..2(X, A) ranks:", hXA)
    small = betti(complex_on(all_cubes, lambda im: im <= A or im <= B), TOP)
    print("H_0..2 of {A,B}-small chains:", small)

    assert absolute(L)[:2] == [1, 1], "L should be a 6-cycle with H_1 of rank 1"
    assert hBL[2] == 1 and hXA[2] == 0, "excision should fail in degree 2"
    assert hBL[:2] == hXA[:2], "excision should hold in degrees 0 and 1"
    print("OK: H_2(B, A&B) has rank 1, H_2(X, A) = 0, so excision fails in degree 2.")


if __name__ == "__main__":
    main()
