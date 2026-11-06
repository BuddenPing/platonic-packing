"""Per-direction relaxation of the n = 2 centre lemma.

For a piece face (unit normal m, offset k) whose plane cuts off the centre, with u = R m, the centre can be cut off
only if  max_p (-u).p <= B(u, s) := min_{lam >= 0, sum lam_l n_l = -u} sum_l lam_l (s c_l - mu(<n_l, u>))  is >= k,
where mu(t) = min { h_P(nu) : |nu| = 1, <nu, m> = t } is the least support of the piece in a direction making
inner product t with m (every container constraint is relaxed separately). So s(2) >= s_rel := min_u s_u, with
B(u, s_u) = k. The relaxation depends on u only: a 2-parameter problem instead of rotations (3 parameters)."""
import json, os, sys, numpy as np
from scipy.optimize import linprog, minimize, minimize_scalar
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from n2_scan import solid, centrally_symmetric, facet_orbits, ROOT, E

TH = np.linspace(0, 2 * np.pi, 2881)[:-1]
def mu_fn(V, m):
    a = np.cross(m, [1, 0, 0] if abs(m[0]) < 0.9 else [0, 1, 0]); a /= np.linalg.norm(a); b = np.cross(m, a)
    vm, va, vb = V @ m, V @ a, V @ b
    def mu(t):
        st = np.sqrt(max(0.0, 1 - t * t))
        h = lambda th: (t * vm + st * (va * np.cos(th) + vb * np.sin(th))).max()
        hs = np.array([(t * vm + st * (va * np.cos(x) + vb * np.sin(x))).max() for x in TH[::8]])
        i = int(hs.argmin()); x0 = TH[::8][i]; d = TH[8] - TH[0]
        r = minimize_scalar(h, bounds=(x0 - d, x0 + d), method='bounded', options=dict(xatol=1e-12))
        return min(r.fun, hs.min())
    return mu

def B(u, s, CN, Coff, muv):
    r = linprog(s * Coff - muv, A_eq=CN.T, b_eq=-u, bounds=[(0, None)] * len(CN), method='highs')
    return r.fun if r.status == 0 else np.inf

def s_u(u, CN, Coff, mu, k, lo=0.05, hi=20):
    muv = np.array([mu(t) for t in CN @ u])
    for _ in range(60):
        mid = (lo + hi) / 2
        if B(u, mid, CN, Coff, muv) >= k: hi = mid
        else: lo = mid
    return hi

def relaxed(p, nrand=600, nloc=10):
    pn, cn = E.PID[p]; (V, N, k), (CV, CN, Coff) = solid(pn), solid(cn)
    best = np.inf
    for q in facet_orbits(V, N):
        mu = mu_fn(V, N[q])
        rng = np.random.default_rng(0); U = rng.normal(size=(nrand, 3)); U /= np.linalg.norm(U, axis=1)[:, None]
        vals = np.array([s_u(u, CN, Coff, mu, k[q]) for u in U])
        for i in np.argsort(vals)[:nloc]:
            f = lambda x: s_u(x / np.linalg.norm(x), CN, Coff, mu, k[q])
            r = minimize(f, U[i], method='Nelder-Mead', options=dict(xatol=1e-9, fatol=1e-11, maxiter=800))
            best = min(best, r.fun, vals[i])
    return best

if __name__ == '__main__':
    for p in sys.argv[1:]:
        rec = json.load(open(f'{ROOT}/records/{p}/{p}_n02.json'))['s_tight']
        sr = relaxed(p)
        print(f'{p:10s} record {rec:.9f}  relaxed bound {sr:.9f}  gap {(rec - sr) / rec:+.1e}', flush=True)
