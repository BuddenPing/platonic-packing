"""Numerical check of the half-space descriptions of the 120-cell and the 600-cell used in Lean.

lean-optimality/PackingOptimality/Cells120.lean defines the 120-cell of edge 1 as
    {y : <n, y> <= (7 + 3 sqrt5)/4 for every vertex n of the unit 600-cell},
the unit 600-cell being the 8 points +-e_i, the 16 points (+-1/2)^4 and the 96 even permutations of
(+-phi, +-1, +-1/phi, 0)/2.

lean-optimality/PackingOptimality/Cells600.lean defines the 600-cell of edge 1 as
    {y : <v, y> <= 2 + sqrt5 for every vertex v of the standard 120-cell},
the standard 120-cell (circumradius 2 sqrt2) being all permutations of (0,0,+-2,+-2), (+-1,+-1,+-1,+-sqrt5),
(+-phi^-2,+-phi,+-phi,+-phi), (+-phi^-1,+-phi^-1,+-phi^-1,+-phi^2) and the even permutations of
(0,+-phi^-2,+-1,+-phi^2), (0,+-phi^-1,+-phi,+-sqrt5), (+-phi^-1,+-1,+-phi,+-2).

For each description this script takes the vertex set of the expected polytope and checks that every
inequality is valid on it, is tight at exactly as many vertices as a cell has (20 for a dodecahedral cell, 4 for
a tetrahedral one), and that the edge is 1. A valid inequality tight on a whole cell is that cell's facet, so the
half-spaces are exactly the facets and the polytope is the expected one.
"""
import itertools

import numpy as np

PHI = (1 + 5 ** 0.5) / 2
S5 = 5 ** 0.5


def parity(p):
    return sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2


def orbit(w, even_only=False):
    out = set()
    for signs in itertools.product([1, -1], repeat=4):
        sw = [a * b for a, b in zip(signs, w)]
        for p in itertools.permutations(range(4)):
            if even_only and parity(p):
                continue
            out.add(tuple(round(sw[p[i]], 12) for i in range(4)))
    return np.array(sorted(out))


def cell600(scale=1.0, odd=False):
    pts = [orbit((1, 0, 0, 0)), orbit((0.5,) * 4)]
    base = (PHI / 2, 0.5, 1 / (2 * PHI), 0)
    o = set()
    for signs in itertools.product([1, -1], repeat=4):
        sw = [a * b for a, b in zip(signs, base)]
        for p in itertools.permutations(range(4)):
            if parity(p) == (1 if odd else 0):
                o.add(tuple(round(sw[p[i]], 12) for i in range(4)))
    pts.append(np.array(sorted(o)))
    return scale * np.unique(np.vstack(pts), axis=0)


def cell120(odd=False):
    allp = [(0, 0, 2, 2), (1, 1, 1, S5), (PHI ** -2, PHI, PHI, PHI), (1 / PHI, 1 / PHI, 1 / PHI, PHI ** 2)]
    evenp = [(0, PHI ** -2, 1, PHI ** 2), (0, 1 / PHI, PHI, S5), (1 / PHI, 1, PHI, 2)]
    pts = [orbit(w) for w in allp]
    for w in evenp:
        o = set()
        for signs in itertools.product([1, -1], repeat=4):
            sw = [a * b for a, b in zip(signs, w)]
            for p in itertools.permutations(range(4)):
                if parity(p) == (1 if odd else 0):
                    o.add(tuple(round(sw[p[i]], 12) for i in range(4)))
        pts.append(np.array(sorted(o)))
    return np.unique(np.round(np.vstack(pts), 9), axis=0)


def check(name, normals, offset, verts, cell_size):
    d = normals @ verts.T
    assert d.max() <= offset + 1e-9, (name, d.max(), offset)
    tight = (np.abs(d - offset) < 1e-9).sum(axis=1)
    assert set(tight) == {cell_size}, (name, set(tight))
    dist = np.linalg.norm(verts[:, None, :] - verts[None, :, :], axis=2)
    edge = dist[dist > 1e-9].min()
    assert abs(edge - 1) < 1e-9, (name, edge)
    print(f"{name}: {len(normals)} facets, {len(verts)} vertices, every facet meets {cell_size}, edge {edge:.12f}")


# 120-cell of edge 1: the standard 120-cell (edge 2/phi^2) in the odd orientation, scaled by phi^2/2.
check("120-cell", cell600(), (7 + 3 * S5) / 4, cell120(odd=True) * PHI ** 2 / 2, 20)
# 600-cell of edge 1: the unit 600-cell (edge 1/phi) in the odd orientation, scaled by phi.
check("600-cell", cell120(), 2 + S5, cell600(scale=PHI, odd=True), 4)
