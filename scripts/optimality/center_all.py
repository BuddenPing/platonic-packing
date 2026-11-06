"""Centre lemma test: for piece P (unit edge) inside s*C (C centred at origin), is the origin always in the interior of P?
M(s) = max over rotations R, faces f of P, feasible centres p of [ -(R m_f).p - rho_f ]  (origin outside P iff >= 0).
If M(s) < 0 for s just below the n=2 record, two pieces cannot fit below it: s(2) >= that value."""
import json, sys, numpy as np
from scipy.optimize import minimize, linprog
from scipy.spatial import HalfspaceIntersection
from scipy.spatial.transform import Rotation as Rot
ROOT = __import__('os').path.dirname(__import__('os').path.dirname(__import__('os').path.dirname(__import__('os').path.abspath(__file__)))); sys.path.insert(0, ROOT + '/src'); sys.path.insert(0, ROOT + '/scripts')
import exact, engine as E
def unit(name):
    S = exact.SOL[name]; V = np.array(S['V'], float); e = min(np.linalg.norm(V[i] - V[j]) for i, j in S['edges'])
    V = V / e; V = V - V.mean(0)
    N = np.array([np.array(n, float) / np.linalg.norm(n) for n in S['normals']])
    off = np.array([N[k] @ V[f[0]] for k, f in enumerate(S['faces'])])
    return V, N, off
def M_of(P, C, s, R):
    V, Nm, rho = P; CV, CN, Coff = C
    h = (V @ R.T @ CN.T).max(0)                       # support of rotated P along container normals
    b = s * Coff - h                                  # CN.p <= b
    # feasible centres: polytope {p : CN p <= b}; Chebyshev centre
    A = np.hstack([CN, np.linalg.norm(CN, axis=1, keepdims=True)])
    res = linprog([0, 0, 0, -1], A_ub=A, b_ub=b, bounds=[(None, None)] * 3 + [(0, None)], method='highs')
    if res.status != 0 or res.x[3] <= 1e-12:
        return -np.inf if res.status == 0 else -np.inf  # (empty or degenerate: no placement)
    hs = HalfspaceIntersection(np.hstack([CN, -b[:, None]]), res.x[:3])
    W = hs.intersections                             # vertices of the feasible region
    Rm = Nm @ R.T                                    # rotated piece face normals
    return float((-(W @ Rm.T) - rho[None, :]).max())
def Mmax(P, C, s, nrand=3000, nloc=12, seed=0):
    rs = Rot.random(nrand, random_state=seed).as_matrix()
    vals = np.array([M_of(P, C, s, R) for R in rs])
    best = vals.max()
    for k in np.argsort(vals)[-nloc:]:
        if not np.isfinite(vals[k]): continue
        q0 = Rot.from_matrix(rs[k]).as_rotvec()
        f = lambda v: -M_of(P, C, s, Rot.from_rotvec(v).as_matrix())
        r = minimize(f, q0, method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-12, maxiter=4000))
        best = max(best, -r.fun)
    return best
if __name__ == '__main__':
    pairs = sys.argv[1:] or [p for p in E.PID if E.FAM[p] == 'platonic']
    for p in pairs:
        Pn, Cn = E.PID[p]; P, C = unit(Pn), unit(Cn)
        r2 = json.load(open(f'{ROOT}/records/{p}/{p}_n02.json'))['s_tight']
        m = Mmax(P, C, r2 * (1 - 1e-7))
        print(f'{p:9s} s(2) record {r2:.7f}   M just below = {m:+.2e}   {"CENTRE LEMMA HOLDS" if m < 0 else "fails"}', flush=True)
