"""Subset inheritance between catalogue records (6 Nov 2026).

For records k < N of one family, the inherited fraction f(k, N) is the largest fraction of the k pieces that can
be matched, one-to-one, to pieces of the N-packing after one container symmetry h and one translation t: piece i
of record k matches piece j of record N when |h c_i + t - c_j| < tol and the placed vertex sets agree
(h(c_i + R_i V) + t = c_j + R_j V as sets, within tol), so the orientation must agree too (up to the piece's own
symmetries). f = 1 means record k is literally k pieces of record N, moved rigidly (a frozen subset: deletion);
f close to 1 means most of record k survives inside record N (partial inheritance).

Usage: python3 scripts/patterns/inherit.py [--families ...] [--kmax 40] [--gap 6] [--out docs/patterns/inherit3d.json]
"""
import json, os, sys, glob, argparse, time
import numpy as np
from scipy.optimize import linear_sum_assignment
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts')); sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
import symmetry
from features import SOL, quat_to_R


def load(fam, n):
    f = os.path.join(ROOT, 'records', fam, f'{fam}_n{n:02d}.json')
    if not os.path.exists(f): return None
    r = json.load(open(f))
    if not isinstance(r, dict) or 'pieces' not in r or r.get('dim', 3) != 3: return None
    P = np.array(r['pieces'], float)
    return r, P[:, :3], [quat_to_R(q) for q in P[:, 3:7]]


def fraction(A, B, V, H, tol=0.02):
    ra, CA, RA = A; rb, CB, RB = B
    k = len(CA)
    WA = np.stack([CA[i] + V @ RA[i].T for i in range(k)])      # k x nv x 3
    WB = np.stack([CB[j] + V @ RB[j].T for j in range(len(CB))])
    best = 0
    anchors = range(min(k, 3))
    for h in H:
        hC = CA @ h.T; hW = WA @ h.T
        for a in anchors:
            for j0 in range(len(CB)):
                t = CB[j0] - hC[a]
                D = np.linalg.norm((hC + t)[:, None] - CB[None], axis=2)          # k x N
                cand = D < tol
                if cand.sum(1).astype(bool).sum() <= best: continue
                M = np.zeros_like(D, dtype=bool)
                for i, j in zip(*np.nonzero(cand)):
                    d = np.linalg.norm((hW[i] + t)[:, None] - WB[j][None], axis=2).min(1).max()
                    M[i, j] = d < tol
                if M.any():
                    r, c = linear_sum_assignment(-M.astype(float))
                    m = int(M[r, c].sum())
                    if m > best:
                        best = m
                        if best == k: return 1.0
    return best / k


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--families'); ap.add_argument('--kmax', type=int, default=40); ap.add_argument('--gap', type=int, default=6)
    ap.add_argument('--out', default=os.path.join(ROOT, 'docs', 'patterns', 'inherit3d.json'))
    a = ap.parse_args()
    fams = a.families.split(',') if a.families else sorted(os.listdir(os.path.join(ROOT, 'records')))
    out = json.load(open(a.out)) if os.path.exists(a.out) else {}
    t0 = time.time()
    for fam in fams:
        if fam in out: continue
        recs = {n: load(fam, n) for n in range(2, a.kmax + a.gap + 1)}
        recs = {n: r for n, r in recs.items() if r}
        if not recs: continue
        r0 = next(iter(recs.values()))[0]
        if r0['piece'] not in SOL or r0['container'] not in SOL: continue
        V = np.array(SOL[r0['piece']]['V'], float); H = symmetry.sym_group(r0['container'])
        res = {}
        for k in sorted(recs):
            if k > a.kmax: break
            for N in range(k + 1, k + a.gap + 1):
                if N in recs:
                    res[f'{k}-{N}'] = round(fraction(recs[k], recs[N], V, H), 4)
        out[fam] = res
        json.dump(out, open(a.out, 'w'))
        print(fam, len(res), f'{time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
