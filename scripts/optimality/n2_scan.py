"""n = 2 scan: for a centrally symmetric container C and an achiral piece P, s(2) equals the centre threshold
s_c = min over rotations R of s*(R), the smallest scale at which P (rotated by R) fits in s*C with the centre of C
outside its interior. (Below s_c every placement contains the centre, so two pieces cannot fit; at s_c the best
placement and its point reflection through the centre form a 2-packing.)

s*(R) = min over facets q of P of LP_q(R):  min s  s.t.  h_P(R^T n_l) + n_l.p <= s c_l  (all container facets l),
                                                        (R m_q).p <= -k_q       (facet q of the piece cuts off 0)
Only one facet per symmetry orbit of P is needed.  usage: python3 scripts/optimality/n2_scan.py [problem ...]"""
import json, os, sys, numpy as np
from scipy.optimize import linprog, minimize
from scipy.spatial.transform import Rotation as Rot
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT + '/src'); sys.path.insert(0, ROOT + '/scripts')
import exact, engine as E

def solid(name):
    S = exact.SOL[name]; V = np.array(S['V'], float)
    e = min(np.linalg.norm(V[i] - V[j]) for i, j in S['edges']); V = V / e; V = V - V.mean(0)
    N = np.array([np.array(n, float) / np.linalg.norm(n) for n in S['normals']])
    off = np.array([N[k] @ V[f[0]] for k, f in enumerate(S['faces'])])
    return V, N, off

def centrally_symmetric(V, tol=1e-9):
    return all(np.min(np.linalg.norm(V + v, axis=1)) < tol for v in V)

def facet_orbits(V, N, tol=1e-7):
    """one facet per orbit under the rotation group of the solid (found from vertex-set symmetries)"""
    # brute force: rotations mapping the vertex set to itself, from pairs of vertex frames
    from itertools import permutations
    G = []
    i0 = 0; nb = np.argsort(np.linalg.norm(V - V[i0], axis=1))[1:4]
    A = np.array([V[i0], V[nb[0]], V[nb[1]]]).T
    for a in range(len(V)):
        for b in range(len(V)):
            for c in range(len(V)):
                if len({a, b, c}) < 3: continue
                B = np.array([V[a], V[b], V[c]]).T
                try: M = B @ np.linalg.inv(A)
                except np.linalg.LinAlgError: continue
                if np.abs(M @ M.T - np.eye(3)).max() > 1e-6 or np.linalg.det(M) < 0: continue
                W = V @ M.T
                if all(np.min(np.linalg.norm(V - w, axis=1)) < tol for w in W): G.append(M)
        if len(V) > 30 and a > 2: break
    reps, seen = [], set()
    for k in range(len(N)):
        if k in seen: continue
        reps.append(k)
        for M in G:
            j = int(np.argmin(np.linalg.norm(N - N[k] @ M.T, axis=1)))
            if np.linalg.norm(N[j] - N[k] @ M.T) < 1e-6: seen.add(j)
    return reps

def s_star(P, C, R, qs):
    V, Nm, k = P; CV, CN, Coff = C
    h = (CN @ R @ V.T).max(1)                    # support of R P along container normals
    best = np.inf
    for q in qs:
        u = R @ Nm[q]
        # variables (s, p1, p2, p3): -c_l s + n_l.p <= -h_l ;  u.p <= -k_q
        A = np.vstack([np.hstack([-Coff[:, None], CN]), np.hstack([[0], u])])
        b = np.concatenate([-h, [-k[q]]])
        r = linprog([1, 0, 0, 0], A_ub=A, b_ub=b, bounds=[(0, None)] + [(None, None)] * 3, method='highs')
        if r.status == 0: best = min(best, r.fun)
    return best

def threshold(P, C, nrand=4000, nloc=25, seed=1):
    qs = facet_orbits(P[0], P[1])
    rs = Rot.random(nrand, random_state=seed)
    vals = np.array([s_star(P, C, R, qs) for R in rs.as_matrix()])
    best, bq = np.inf, None
    for i in np.argsort(vals)[:nloc]:
        f = lambda v: s_star(P, C, Rot.from_rotvec(v).as_matrix(), qs)
        r = minimize(f, rs[i].as_rotvec(), method='Nelder-Mead', options=dict(xatol=1e-11, fatol=1e-13, maxiter=6000))
        if r.fun < best: best, bq = r.fun, r.x
    return best, Rot.from_rotvec(bq), qs

if __name__ == '__main__':
    probs = sys.argv[1:] or list(E.PID)
    out = []
    for p in probs:
        pn, cn = E.PID[p]; P, C = solid(pn), solid(cn)
        f2 = f'{ROOT}/records/{p}/{p}_n02.json'
        if not os.path.exists(f2): continue
        r2 = json.load(open(f2)); rec = r2['s_tight']
        if not centrally_symmetric(C[0]):
            print(f'{p:16s} container not centrally symmetric', flush=True); continue
        sc, R, qs = threshold(P, C)
        gap = (rec - sc) / rec
        row = dict(problem=p, piece=pn, container=cn, record=rec, s_c=sc, rel_gap=gap, closed_form=r2.get('closed_form_conjecture'),
                   found_by=r2.get('found_by'), quat=R.as_quat().tolist(), facet_orbits=len(qs))
        out.append(row)
        print(f'{p:16s} record {rec:.9f}  s_c {sc:.9f}  gap {gap:+.1e}  cf {r2.get("closed_form_conjecture")}', flush=True)
    json.dump(out, open(f'{ROOT}/scripts/optimality/n2_scan.json' if not sys.argv[1:] else '/dev/null', 'w'), indent=1)
