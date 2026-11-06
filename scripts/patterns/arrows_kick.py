"""Insertion and kick arrows (PingYou Ltd, Nov 2026: E3 "add a body at an affine guess, F -> P, spin +12 deg,
F -> P"; E4 "a hub body at the mean of the centres, R = diag(1,-1,-1), F -> P"; E2 "group rotations +-16 deg,
spins +-6 deg, F -> P after each kick").

  insertion  from a (k-1)-packing: one more body at the hub (mean of centres) or at a hole (the point of the
             container farthest from all centres, on a grid), with each orientation already present, the identity
             and diag(1,-1,-1); then F -> P.
  kicks      from the best k-packing: rotate one body by +-theta about each of its three local axes, or a layer of
             bodies about the x, y or z axis through its centroid; F -> P after each kick; keep improvements
             (first improvement, repeated until a full sweep fails or the time is up).

Usage: python3 scripts/patterns/arrows_kick.py FAMILY K OUTDIR [--from-dir DIR] [--minutes M]
Packings are read from DIR/<family>_nKK.json (arrow results, record units) if present, else from the records.
"""
import json, os, sys, time, argparse, itertools
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
import fp, exact
from features import quat_to_R, SOL


def rotm(axis, th):
    a = np.asarray(axis, float); a = a / np.linalg.norm(a)
    K = np.array([[0, -a[2], a[1]], [a[2], 0, -a[0]], [-a[1], a[0], 0]])
    return np.eye(3) + np.sin(th) * K + (1 - np.cos(th)) * K @ K


def current(fam, k, d):
    f = os.path.join(d, f'{fam}_n{k:02d}.json') if d else None
    if f and os.path.exists(f):
        w = json.load(open(f))
        pb = exact.Problem(w['piece'], w['container'])
        C = np.array(w['C']) if w.get('units') == 'record' else np.array(w['C'])
        R = [exact.quat_to_R(np.array(q) / np.linalg.norm(q)) for q in w['Q']]
        return w['s'], C, R, w.get('arrow', 'arrow')
    rec, C, R = fp.load(fam, k)
    return rec['s_full'], C, R, 'record'


def save(out, fam, k, piece, cont, s, C, R, arrow, before):
    json.dump(dict(piece=piece, container=cont, n=k, s=s, C=np.asarray(C).tolist(), units='record',
                   Q=[exact.R_to_quat(r).tolist() for r in R], arrow=arrow, record_before=before),
              open(os.path.join(out, f'{fam}_n{k:02d}.json'), 'w'))


def holes(geom, C, s, m=9):
    lo, hi = -s * geom.circ * 0.0 - s, s
    g = np.linspace(-1, 1, m)
    CV = np.array(SOL[geom.container]['V'], float) * s
    P = np.array([CV.T @ w for w in np.random.default_rng(0).dirichlet(np.ones(len(CV)), 400)])
    d = np.min(np.linalg.norm(P[:, None] - C[None], axis=2), axis=1)
    return P[np.argsort(-d)[:4]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('family'); ap.add_argument('K', type=int); ap.add_argument('out')
    ap.add_argument('--from-dir'); ap.add_argument('--minutes', type=float, default=20)
    ap.add_argument('--tlimit', type=float, default=20)
    a = ap.parse_args()
    t_end = time.time() + 60 * a.minutes
    os.makedirs(a.out, exist_ok=True)
    log = open(os.path.join(a.out, f'{a.family}_kick.log'), 'a')
    rec, _, _ = fp.load(a.family, a.K); piece, cont = rec['piece'], rec['container']; before = rec['s_full']
    geom = fp.Geom(piece, cont)
    best_s, C, R, how = current(a.family, a.K, a.from_dir)
    # ---- insertion from k-1
    try:
        s1, C1, R1, how1 = current(a.family, a.K - 1, a.from_dir)
        cand_pos = [C1.mean(0)] + list(holes(geom, C1, s1))
        orients = [R1[i] for i in range(len(R1))][:6] + [np.eye(3), np.diag([1.0, -1, -1])]
        for p, Rn in itertools.product(cand_pos, orients):
            if time.time() > t_end: break
            Cn = np.vstack([C1, p]); Rl = list(R1) + [Rn]
            try: sF, sP, CP, RP = fp.FP(piece, cont, Cn, Rl, tlimit=a.tlimit)
            except Exception as e: continue
            tag = ''
            if sP < best_s - 1e-9:
                best_s, C, R, how = sP, CP, RP, f'insert into n{a.K - 1} ({how1}) at {np.round(p, 3).tolist()}'; tag = ' IMPROVES'
                save(a.out, a.family, a.K, piece, cont, best_s, C, R, how, before)
            print(f'{a.family} k={a.K} insert F {sF:.6f} P {sP:.9f}{tag}', file=log, flush=True)
    except FileNotFoundError:
        pass
    # ---- kicks
    improved = True
    while improved and time.time() < t_end:
        improved = False
        moves = []
        for i in range(len(C)):
            for ax in range(3):
                for th in (6, -6, 12, -12, 16, -16):
                    moves.append(('spin', i, ax, th))
        for d in range(3):
            z = C[:, d]; cut = np.median(z)
            for grp in (np.nonzero(z <= cut)[0], np.nonzero(z > cut)[0]):
                for th in (16, -16, 8, -8):
                    moves.append(('group', tuple(grp.tolist()), d, th))
        for mv in moves:
            if time.time() > t_end: break
            Rk = [r.copy() for r in R]; Ck = C.copy()
            if mv[0] == 'spin':
                _, i, ax, th = mv
                Rk[i] = rotm(R[i][:, ax], np.radians(th)) @ R[i]
            else:
                _, grp, d, th = mv
                e = np.zeros(3); e[(d + 1) % 3] = 1.0
                Q = rotm(e, np.radians(th)); cen = C[list(grp)].mean(0)
                for i in grp:
                    Ck[i] = cen + Q @ (C[i] - cen); Rk[i] = Q @ R[i]
            try: sF, sP, CP, RP = fp.FP(piece, cont, Ck, Rk, tlimit=a.tlimit)
            except Exception: continue
            if sP < best_s - 1e-9:
                best_s, C, R = sP, CP, RP; how = f'{how}; kick {mv[0]} {mv[1:]}'
                save(a.out, a.family, a.K, piece, cont, best_s, C, R, how, before)
                print(f'{a.family} k={a.K} kick {mv} -> {sP:.10f} IMPROVES', file=log, flush=True)
                improved = True; break
    print(f'== {a.family} k={a.K}: record {before:.10f} best {best_s:.10f} ({how})', file=log, flush=True)


if __name__ == '__main__':
    main()
