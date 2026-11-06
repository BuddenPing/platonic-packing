"""PingYou's F and P steps and the arrows between packings (credit: PingYou Ltd, Nov 2026).

F  hold every orientation fixed and minimize the container scale S over the centres. For fixed orientations and
   one fixed separating axis u_ij per pair, every constraint is linear in the centres c and in S:
     container  <N_f, c_i> + h_i(N_f) <= beta_f S          (h_i = support function of the placed piece i)
     pair       <u, c_i> + h_i(u) <= <u, c_j> - h_j(-u)     (piece i below the plane, j above)
   so S is an exact LP optimum for that choice of axes, and any LP solution is a valid packing (each pair is
   separated by a plane). F iterates: re-select each pair's best separating axis at the current point (the current
   point then stays feasible, so S never increases) and re-solve.
P  minimize S with centres and rotations free: the repository's certified sequential LP (src/fastslp.py).

Record units throughout (unit-edge canonical solids, container = S x canonical container at the origin).
"""
import json, os, sys, math, itertools
import numpy as np
from scipy.optimize import linprog
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'src')); sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
from features import SOL, quat_to_R
import exact, fastslp


class Geom:
    def __init__(self, piece, container):
        self.piece, self.container = piece, container
        P, Cn = SOL[piece], SOL[container]
        self.V = np.array(P['V'], float)
        self.FN = np.array(P['normals'], float)
        E = np.array([self.V[j] - self.V[i] for i, j in P['edges']])
        E /= np.linalg.norm(E, axis=1)[:, None]
        self.E = E
        self.CN = np.array(Cn['normals'], float)
        CV = np.array(Cn['V'], float)
        self.beta = np.array([self.CN[f] @ CV[F[0]] for f, F in enumerate(Cn['faces'])])
        self.circ = float(np.linalg.norm(self.V, axis=1).max())

    def axes(self, Ri, Rj):
        A = [self.FN @ Ri.T, self.FN @ Rj.T]
        Ei, Ej = self.E @ Ri.T, self.E @ Rj.T
        X = np.cross(Ei[:, None, :], Ej[None, :, :]).reshape(-1, 3)
        nx = np.linalg.norm(X, axis=1); X = X[nx > 1e-6] / nx[nx > 1e-6][:, None]
        A.append(X)
        return np.concatenate(A)

    def best_axis(self, ci, Ri, cj, Rj):
        U = self.axes(Ri, Rj)
        Wi, Wj = self.V @ Ri.T, self.V @ Rj.T
        hi = (U @ Wi.T).max(1); hj = (-U @ Wj.T).max(1)      # h_i(u), h_j(-u)
        g = U @ (cj - ci) - hi - hj
        # also the reversed orientation of each axis
        hi2 = (-U @ Wi.T).max(1); hj2 = (U @ Wj.T).max(1)
        g2 = -U @ (cj - ci) - hi2 - hj2
        k, k2 = g.argmax(), g2.argmax()
        return (U[k], g[k]) if g[k] >= g2[k2] else (-U[k2], g2[k2])

    def scale(self, C, R):
        X = np.concatenate([C[i] + self.V @ R[i].T for i in range(len(C))])
        return float(((X @ self.CN.T) / self.beta[None]).max())


def F(geom, C, R, iters=60, gap=0.0, tol=1e-10, verbose=False):
    """Fixed-orientation LP descent. Returns (S, C)."""
    C = np.array(C, float); n = len(C)
    W = [geom.V @ r.T for r in R]
    Hc = np.array([(geom.CN @ w.T).max(1) for w in W])          # n x F support values
    S_prev = np.inf
    for it in range(iters):
        rows, rhs = [], []
        nv = 3 * n + 1
        for i in range(n):                                       # container
            for f in range(len(geom.CN)):
                a = np.zeros(nv); a[3 * i:3 * i + 3] = geom.CN[f]; a[-1] = -geom.beta[f]
                rows.append(a); rhs.append(-Hc[i, f])
        for i, j in itertools.combinations(range(n), 2):
            if np.linalg.norm(C[i] - C[j]) > 2 * geom.circ + 3.0: continue    # far pairs: guarded by trust region
            u, g = geom.best_axis(C[i], R[i], C[j], R[j])
            hi = (W[i] @ u).max(); hj = (-(W[j] @ u)).max()
            a = np.zeros(nv); a[3 * i:3 * i + 3] = u; a[3 * j:3 * j + 3] = -u
            rows.append(a); rhs.append(-hi - hj - gap)
        cost = np.zeros(nv); cost[-1] = 1
        bnd = [(C.flat[k] - 1.0, C.flat[k] + 1.0) for k in range(3 * n)] + [(0, None)]   # trust region 1 edge
        res = linprog(cost, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bnd, method='highs')
        if res.status != 0: break
        Cn = res.x[:3 * n].reshape(n, 3); S = res.x[-1]
        # far pairs may have come close: verify every pair; if any overlap, shrink the step
        ok = all(geom.best_axis(Cn[i], R[i], Cn[j], R[j])[1] >= -1e-9 for i, j in itertools.combinations(range(n), 2))
        if not ok:
            Cn = (C + Cn) / 2
            if not all(geom.best_axis(Cn[i], R[i], Cn[j], R[j])[1] >= -1e-9 for i, j in itertools.combinations(range(n), 2)):
                break
            S = geom.scale(Cn, R)
        C = Cn
        if verbose: print(f'  F it {it}: S = {S:.9f}')
        if S_prev - S < tol: break
        S_prev = S
    return geom.scale(C, R), C


def P(piece, container, C, R, tlimit=60):
    """Certified SLP with rotations free (internal units of exact.py)."""
    pb = exact.Problem(piece, container)
    Ci = np.asarray(C) * pb.edge
    L0, _, C0 = fastslp.certify_fast(pb, Ci, R)
    L, C1, R1, hist = fastslp.solve(pb, C0, list(R), L0, outer=600, tlimit=tlimit)
    L2, _, C2 = fastslp.certify_fast(pb, C1, R1)
    return pb.s_of_L(L2), np.asarray(C2) / pb.edge, R1


def FP(piece, container, C, R, tlimit=60, verbose=False):
    g = Geom(piece, container)
    sF, CF = F(g, C, R, verbose=verbose)
    sP, CP, RP = P(piece, container, CF, R, tlimit)
    return sF, sP, CP, RP


def load(family, n):
    rec = json.load(open(os.path.join(ROOT, 'records', family, f'{family}_n{n:02d}.json')))
    Pz = np.array(rec['pieces'], float)
    return rec, Pz[:, :3], [quat_to_R(q) for q in Pz[:, 3:7]]
