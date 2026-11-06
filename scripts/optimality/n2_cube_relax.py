"""Per-coordinate relaxation of the n = 2 centre lemma for hypercube containers (any dimension).

Container [-s/2, s/2]^d (unit edge times s), piece P (unit edge, centred), a facet of P with unit normal m and offset
k. With u = R m, the centre can be cut off by that facet only if  sum_i |u_i| (s/2 - mu(-|u_i|)) >= k,  where
mu(t) = min{ h_P(nu) : |nu| = 1, <nu, m> = t } (each row of R relaxed separately). Hence s(2) >= s_rel = min over
unit u of  2 (k + sum_i |u_i| mu(-|u_i|)) / sum_i |u_i|.  If s_rel equals the record, the lemma reduces to this
inequality in u (separable: one-variable functions of the u_i, constrained by sum u_i^2 = 1)."""
import json, os, sys, numpy as np
from scipy.optimize import minimize
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def piece_nd(pid):
    d = json.load(open(f'{ROOT}/src/polytopes_nd.json'))[pid]
    V = np.array(d['Vf'] if isinstance(d['Vf'], list) else d['V'], float)
    return V

def load_piece(name):
    if name in json.load(open(f'{ROOT}/src/polytopes_nd.json')):
        P = json.load(open(f'{ROOT}/src/polytopes_nd.json'))[name]
        V = np.array(P['Vf'], float); V = V / P['edge']; V = V - V.mean(0)
        N = np.array(P['N'], float); N /= np.linalg.norm(N, axis=1)[:, None]
        k = np.array([max(V @ n) for n in N])
        return V, N, k
    from n2_scan import solid
    return solid(name)

def mu_table(V, m, ts, nsamp):
    d = V.shape[1]
    # orthonormal basis of m-perp
    Q, _ = np.linalg.qr(np.column_stack([m, np.random.default_rng(0).normal(size=(d, d - 1))]))
    B = Q[:, 1:]; vm = V @ m; vb = V @ B
    rng = np.random.default_rng(1); W = rng.normal(size=(nsamp, d - 1)); W /= np.linalg.norm(W, axis=1)[:, None]
    out = []
    for t in ts:
        st = np.sqrt(max(0, 1 - t * t))
        H = (t * vm[None, :] + st * (W @ vb.T)).max(1)
        j = np.argsort(H)[:6]; best = H.min()
        for jj in j:
            f = lambda w: (t * vm + st * (vb @ (w / np.linalg.norm(w)))).max()
            r = minimize(f, W[jj], method='Nelder-Mead', options=dict(xatol=1e-11, fatol=1e-13, maxiter=3000))
            best = min(best, r.fun)
        out.append(best)
    return np.array(out)

def s_rel(piece, d, nsamp=4000, nt=401, nrand=4000):
    V, N, k = load_piece(piece)
    # one facet per orbit: facets with equal offsets and the same sorted vertex-inner-product profile
    prof = {}
    for q in range(len(N)):
        key = (round(k[q], 9), tuple(np.round(np.sort(V @ N[q]), 7)))
        prof.setdefault(key, q)
    best = (np.inf, None)
    ts = np.linspace(-1, 0, nt)
    for q in prof.values():
        mt = mu_table(V, N[q], ts, nsamp)
        mu = lambda t: np.interp(t, ts, mt)
        def su(u):
            u = np.abs(u) / np.linalg.norm(u); L = u.sum()
            return 2 * (k[q] + (u * mu(-u)).sum()) / L
        rng = np.random.default_rng(2); U = rng.normal(size=(nrand, d))
        vals = np.array([su(u) for u in U])
        for i in np.argsort(vals)[:12]:
            r = minimize(su, U[i], method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-12, maxiter=4000))
            if r.fun < best[0]: best = (r.fun, np.abs(r.x) / np.linalg.norm(r.x))
    return best

if __name__ == '__main__':
    cases = [a.split(':') for a in sys.argv[1:]]   # record_id:piece:dim
    for rid, piece, d in cases:
        rec = json.load(open(f'{ROOT}/records/{rid.rsplit("_n", 1)[0]}/{rid}.json'))
        sr, u = s_rel(piece, int(d))
        print(f'{rid:14s} record {rec["s_tight"]:.9f}  relaxed {sr:.9f}  gap {(rec["s_tight"] - sr) / rec["s_tight"]:+.1e}  u* {np.round(np.sort(u)[::-1], 4)}  cf {rec.get("closed_form_conjecture")}', flush=True)
