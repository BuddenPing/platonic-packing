"""Structural features of every 3D catalogue record (6 Nov 2026, pattern classification).

For each record (records/<family>/<id>.json, unit-edge canonical solids, container s_full x canonical container
centred at the origin) this computes, at a tolerance `tol` in piece edges:

  orient   orientation classes: pieces i ~ j when R_i^-1 R_j is a proper symmetry of the piece
           (class sizes, largest first, e.g. [40, 31] for a two-orientation Welsh window)
  sym      the configuration symmetry group: container symmetries h (reflections included) that map the set of
           placed pieces onto itself (each piece's vertex set onto another piece's vertex set); order and
           proper/improper counts, plus the same at a loose tolerance (approximate symmetry)
  layers   for each container face normal, the centres grouped by height (gap > `ltol` edges starts a new
           layer); the direction with the fewest layers is reported with its counts, e.g. 9+11+9
  lattice  for every orientation class with >= 4 pieces: whether all centres are integer combinations of three
           difference vectors (max residual < tol); Gram invariants of a reduced basis

Usage: python3 scripts/patterns/features.py [--families f1,f2] [--out docs/patterns/features3d.json]
"""
import json, os, sys, glob, argparse, itertools, time
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import symmetry

SOL = json.load(open(os.path.join(ROOT, 'src', 'solids.json')))


def quat_to_R(q):
    q = np.asarray(q, float); q = q / np.linalg.norm(q); w, x, y, z = q
    return np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                     [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                     [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])


def orient_classes(R, Gp, tol):
    """Union pieces whose orientations differ by a proper piece symmetry (within tol, Frobenius)."""
    n = len(R); lab = list(range(n))
    def find(i):
        while lab[i] != i: lab[i] = lab[lab[i]]; i = lab[i]
        return i
    Rs = np.stack(R); Gs = np.stack(Gp)                      # Gp proper symmetries
    for i in range(n):
        RiG = np.einsum('ab,gbc->gac', Rs[i], Gs)            # R_i g for all g
        d = np.sqrt(((RiG[None] - Rs[:, None]) ** 2).sum((2, 3))).min(1)   # n
        for j in np.nonzero(d < tol)[0]:
            a, b = find(i), find(int(j))
            if a != b: lab[a] = b
    groups = {}
    for i in range(n): groups.setdefault(find(i), []).append(i)
    return sorted(groups.values(), key=len, reverse=True)


def config_symmetry(C, R, Vp, H, tol):
    """Container symmetries mapping the placed pieces onto themselves."""
    W = [C[i] + Vp @ R[i].T for i in range(len(C))]           # world vertices per piece
    Wsort = [w[np.lexsort(np.round(w.T, 6)[::-1])] for w in W]
    cen = np.array(C)
    ok = []
    for h in H:
        hc = cen @ h.T
        D = np.linalg.norm(hc[:, None] - cen[None], axis=2)
        j = D.argmin(1)
        if D[np.arange(len(C)), j].max() > tol or len(set(j.tolist())) < len(C): continue
        good = True
        for i in range(len(C)):
            hw = W[i] @ h.T
            dmin = np.linalg.norm(hw[:, None] - W[j[i]][None], axis=2).min(1).max()
            if dmin > tol: good = False; break
        if good: ok.append(h)
    return ok


def layers(C, normals, ltol):
    best = None
    for nrm in normals:
        z = np.sort(C @ np.asarray(nrm, float))
        cuts = np.nonzero(np.diff(z) > ltol)[0]
        sizes = np.diff(np.concatenate([[0], cuts + 1, [len(z)]])).tolist()
        if best is None or len(sizes) < len(best[0]): best = (sizes, nrm)
    return best


def lattice(C, tol):
    """Integer-lattice test for a point set: basis from short independent differences, integer residuals."""
    P = np.asarray(C, float)
    if len(P) < 4: return None
    D = (P[:, None] - P[None]).reshape(-1, 3)
    D = D[np.linalg.norm(D, axis=1) > 1e-6]
    D = D[np.argsort(np.linalg.norm(D, axis=1))]
    basis = []
    for d in D:
        M = np.array(basis + [d])
        if np.linalg.matrix_rank(M, 1e-6) == len(M): basis.append(d)
        if len(basis) == 3: break
    if len(basis) < 3: return {'dim': len(basis)}
    B = np.array(basis).T
    X = np.linalg.solve(B, (P - P[0]).T).T
    res = np.abs(X - np.round(X)).max()
    if res > tol:
        # half-integer refinement (centred lattices): try basis / 2 combinations
        return {'dim': 3, 'lattice': False, 'residual': float(res)}
    G = B.T @ B
    ev = np.sort(np.linalg.eigvalsh(G))
    return {'dim': 3, 'lattice': True, 'residual': float(res), 'gram': np.round(G, 6).tolist(),
            'det': float(abs(np.linalg.det(B)))}


def analyze(rec, tol=1e-4, loose=2e-2, ltol=0.05):
    piece, cont = rec['piece'], rec['container']
    P = np.array(rec['pieces'], float); C = P[:, :3]; R = [quat_to_R(q) for q in P[:, 3:7]]
    Gp = [g for g in symmetry.sym_group(piece) if np.linalg.det(g) > 0]
    H = symmetry.sym_group(cont)
    Vp = np.array(SOL[piece]['V'], float)
    oc = orient_classes(R, Gp, 1e-3)
    sy = config_symmetry(C, R, Vp, H, tol); sy_l = config_symmetry(C, R, Vp, H, loose)
    ly = layers(C, SOL[cont]['normals'], ltol)
    lat = [lattice(C[g], 1e-3) for g in oc if len(g) >= 4]
    return {'record_id': rec['record_id'], 'family': rec.get('family'), 'piece': piece, 'container': cont,
            'n': rec['n'], 's': rec['s_full'], 'closed_form': rec.get('closed_form_conjecture'),
            'found_by': rec.get('found_by'), 'move': (rec.get('search') or {}).get('move'),
            'orient': [len(g) for g in oc],
            'sym': {'order': len(sy), 'proper': sum(1 for h in sy if np.linalg.det(h) > 0)},
            'sym_loose': {'order': len(sy_l), 'proper': sum(1 for h in sy_l if np.linalg.det(h) > 0)},
            'layers': {'sizes': ly[0], 'normal': np.round(ly[1], 4).tolist()} if ly else None,
            'lattice': lat}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--families'); ap.add_argument('--out', default=os.path.join(ROOT, 'docs', 'patterns', 'features3d.json'))
    ap.add_argument('--nmax', type=int, default=1000)
    a = ap.parse_args()
    fams = a.families.split(',') if a.families else sorted(os.listdir(os.path.join(ROOT, 'records')))
    out = []; t0 = time.time()
    for fam in fams:
        for f in sorted(glob.glob(os.path.join(ROOT, 'records', fam, f'{fam}_n*.json'))):
            try: rec = json.load(open(f))
            except Exception: continue
            if not isinstance(rec, dict) or 'pieces' not in rec or rec.get('dim', 3) != 3: continue
            if rec['piece'] not in SOL or rec['container'] not in SOL or rec['n'] > a.nmax: continue
            out.append(analyze(rec))
        print(fam, len(out), f'{time.time() - t0:.0f}s', flush=True)
    json.dump(out, open(a.out, 'w'), indent=0)


if __name__ == '__main__':
    main()
