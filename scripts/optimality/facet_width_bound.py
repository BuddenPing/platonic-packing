"""Facet-width lower bound for n = 2 (any container C, centred at its circumcentre). If a piece misses the centre
in its interior, one of its facet planes separates it from the centre, so the piece lies in a slab of width
w_f = h_P(n_f) + h_P(-n_f) on one side of a plane through the centre; that slab reaches at most s R_C (R_C the
circumradius of C). Hence every placement contains the centre when s < min_f w_f / R_C, and s(2) >= min_f w_f / R_C.
Records equal to this bound are optimal with an elementary lower bound."""
import json, os, sys, glob, numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ball_bound import ND
def geom(name):
    if name in ND:
        P = ND[name]; V = np.array(P['Vf'], float) / P['edge']; V -= V.mean(0)
        N = np.array(P['N'], float); N /= np.linalg.norm(N, axis=1)[:, None]
    else:
        from n2_scan import solid
        V, N, _ = solid(name)
    return V, N
rows = []
for f in sorted(glob.glob(f'{ROOT}/records/*/*_n02.json')):
    r = json.load(open(f)); pc, cn = r.get('piece'), r.get('container')
    try: V, N = geom(pc); CV, _ = geom(cn)
    except Exception: continue
    wmin = min((V @ n).max() - (V @ n).min() for n in N)
    RC = np.linalg.norm(CV, axis=1).max()
    b = wmin / RC
    rows.append(((r['s_tight'] - b) / r['s_tight'], r['record_id'], r['s_tight'], b, r.get('closed_form_conjecture')))
for g, rid, s, b, cf in sorted(rows):
    if g < 1e-6: print(f'{rid:16s} record {s:.10f}  facet-width bound {b:.10f}  gap {g:+.1e}  cf {cf}')
print('pairs', len(rows))
