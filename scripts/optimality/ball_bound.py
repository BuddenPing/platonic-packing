"""Two-ball lower bound for n = 2: each piece contains its inscribed ball (radius k), so two pieces need two disjoint
balls of radius k. In a container s*C (C regular, inradius r_C, diameter D_C, centred), the admissible ball centres
form ((s r_C - k)/r_C) C, so two balls fit only if (s r_C - k) D_C / r_C >= 2k, i.e. s >= (k / r_C)(1 + 2 r_C / D_C).
Records equal to this bound are optimal with an elementary lower bound."""
import json, os, sys, glob, numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
ND = json.load(open(f'{ROOT}/src/polytopes_nd.json'))
def geom(name):
    if name in ND:
        P = ND[name]; V = np.array(P['Vf'], float) / P['edge']; V -= V.mean(0)
        N = np.array(P['N'], float); N /= np.linalg.norm(N, axis=1)[:, None]
    else:
        from n2_scan import solid
        V, N, _ = solid(name)
    k = min(max(V @ n) for n in N)
    D = max(np.linalg.norm(a - b) for a in V for b in V)
    return k, D
rows = []
for f in sorted(glob.glob(f'{ROOT}/records/*/*_n02.json')):
    r = json.load(open(f)); pc, cn = r.get('piece'), r.get('container')
    try: kP, _ = geom(pc); rC, DC = geom(cn)
    except Exception as e: continue
    bound = (kP / rC) * (1 + 2 * rC / DC)
    gap = (r['s_tight'] - bound) / r['s_tight']
    rows.append((gap, r['record_id'], r['s_tight'], bound, r.get('closed_form_conjecture')))
for g, rid, s, b, cf in sorted(rows):
    if g < 1e-6: print(f'{rid:16s} record {s:.10f}  ball bound {b:.10f}  gap {g:+.1e}  cf {cf}')
print('pairs scanned', len(rows))
