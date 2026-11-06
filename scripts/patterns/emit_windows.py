"""Emit lean-optimality/PackingOptimality/Windows.lean: exact lattice-window packings.

* Rhombic dodecahedra R = {|x_i| + |x_j| <= 1}, the Voronoi cell of the FCC lattice D3: the window
  W(s, o) = {w in D3 : |w_i + o_i| + |w_j + o_j| <= s - 1} gives |W| copies of R in s R. Scale 3: 19 pieces
  (offset 0), scale 4: 44 (offset (1/2,1/2,1/2)), scale 5: 93 (offset 0).
* Truncated cubes T = {|x_i| <= a, |x_0| + |x_1| + |x_2| <= 2a + 1/2}, a = (1 + sqrt2)/2, inside the Voronoi cell
  [-a, a]^3 of 2a Z^3: the 4 x 4 x 4 grid minus its 8 corners gives 56 copies of T in 4 T (Cartesian shell).
"""
import itertools, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def d3win(M, e):
    """w in D3 with |2 w_i + e_i| + |2 w_j + e_j| <= M for all pairs, sorted by code."""
    pts = []
    for w in itertools.product(range(-6, 7), repeat=3):
        if sum(w) % 2: continue
        if all(abs(2 * w[i] + e[i]) + abs(2 * w[j] + e[j]) <= M for i, j in ((0, 1), (0, 2), (1, 2))): pts.append(w)
    return sorted(pts, key=code)


def code(w): return (w[0] + 8) * 289 + (w[1] + 8) * 17 + (w[2] + 8)


def tcuwin():
    pts = [w for w in itertools.product(range(4), repeat=3) if not all(x in (0, 3) for x in w)]
    return sorted(pts, key=code)


def lean_list(pts):
    return '![' + ', '.join('![' + ', '.join(str(x) for x in w) + ']' for w in pts) + ']'


TEMPLATE = open(os.path.join(ROOT, 'scripts', 'patterns', 'Windows.lean.tmpl')).read()
W19, W44, W93, W56 = d3win(4, (0, 0, 0)), d3win(6, (1, 1, 1)), d3win(8, (0, 0, 0)), tcuwin()
assert (len(W19), len(W44), len(W93), len(W56)) == (19, 44, 93, 56)
out = (TEMPLATE.replace('@@W19@@', lean_list(W19)).replace('@@W44@@', lean_list(W44))
       .replace('@@W93@@', lean_list(W93)).replace('@@W56@@', lean_list(W56)))
open(os.path.join(ROOT, 'lean-optimality', 'PackingOptimality', 'Windows.lean'), 'w').write(out)
print('wrote Windows.lean')
