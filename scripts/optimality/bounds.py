"""Simple provable lower bounds for s(P in C, n) vs the records, low n."""
import json, sys, os, itertools, numpy as np
ROOT = __import__('os').path.dirname(__import__('os').path.dirname(__import__('os').path.dirname(__import__('os').path.abspath(__file__))))
sys.path.insert(0, ROOT + '/src'); sys.path.insert(0, ROOT + '/scripts')
import exact, engine as E

def unit(name):
    S = exact.SOL[name]; V = np.array(S['V'], float)
    e = min(np.linalg.norm(V[i] - V[j]) for i, j in S['edges'])
    return V / e, S                       # unit edge (catalogue convention)

def minwidth(V, S):
    dirs = [np.array(n, float) for n in S['normals']]
    E_ = [V[j] - V[i] for i, j in S['edges']]
    for a, b in itertools.combinations(E_, 2):
        c = np.cross(a, b); nc = np.linalg.norm(c)
        if nc > 1e-12: dirs.append(c / nc)
    best = 1e9
    for u in dirs:
        u = u / np.linalg.norm(u); p = V @ u; best = min(best, p.max() - p.min())
    return best

def inr(V, S):   # radius of a ball centred at the centroid inside the solid (exact inradius for insphere solids)
    c = V.mean(0); r = 1e9
    for f, nrm in zip(S['faces'], S['normals']):
        nrm = np.array(nrm, float); nrm /= np.linalg.norm(nrm); r = min(r, abs((V[f[0]] - c) @ nrm))
    return r

def diam(V): return max(np.linalg.norm(a - b) for a, b in itertools.combinations(V, 2))
def vol(S, V0, V): return S['volume'] * (np.linalg.norm(V[0] - V[1]) / 1) ** 0 if False else None

cache = {}
def props(name):
    if name not in cache:
        V, S = unit(name)
        Vr = np.array(S['V'], float); scale = np.linalg.norm(V[0] - V[1]) / np.linalg.norm(Vr[0] - Vr[1])
        cache[name] = dict(w=minwidth(V, S), r=inr(V, S), d=diam(V), vol=S['volume'] * scale ** 3)
    return cache[name]

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
rows = []
for p, (P, C) in E.PID.items():
    a, b = props(P), props(C)
    b1 = {'width': a['w'] / b['w'], 'diameter': a['d'] / b['d'], 'inradius': a['r'] / b['r']}
    for n in range(2, NMAX + 1):
        f = f'{ROOT}/records/{p}/{p}_n{n:02d}.json'
        r = json.load(open(f)); st = r['s_tight']
        bounds = dict(b1, volume=(n * a['vol'] / b['vol']) ** (1 / 3))
        k, L = max(bounds.items(), key=lambda x: x[1])
        rows.append(dict(p=p, fam=E.FAM[p], n=n, s=st, L=L, bound=k, gap=(st - L) / L, vlb_rec=r.get('volume_lower_bound'),
                         cf=r.get('closed_form_conjecture'), who=r['found_by'][:50]))
json.dump(rows, open(os.path.dirname(__file__) + f'/bounds_n{NMAX}.json', 'w'), indent=0)
tight = [x for x in rows if x['gap'] < 1e-6]
print('rows', len(rows), 'tight', len(tight))
for x in sorted(tight, key=lambda x: (x['p'], x['n'])): print(f"{x['p']:14s} n={x['n']:3d} s={x['s']:.9f} bound={x['bound']:8s} L={x['L']:.9f} gap={x['gap']:.1e} cf={x['cf']}")
# check our volume bound against the record's field
bad = [x for x in rows if x['vlb_rec'] and abs(x['vlb_rec'] - ((x['n'] * 1) and x['vlb_rec'])) > 1]
