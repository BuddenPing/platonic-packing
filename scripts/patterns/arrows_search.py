"""Systematic arrows (PingYou's subset relaxation, Nov 2026) over one family.

For each target k and each source record N > k: candidate k-subsets of the N-packing (caps along container
directions, nearest clusters, random connected clusters), each relaxed by F (fixed-orientation LP) then P (free
certified SLP). Insertion arrows from k-1 (one piece at the hub = mean of centres, or at the best hole, with each
orientation present in the source) are tried too. Every result is a certified packing (fastslp.certify_fast);
improvements over the catalogue record are written to OUT/<family>_nKK.json in solver form for claim.py.

Usage: python3 scripts/patterns/arrows_search.py FAMILY KMIN KMAX NMAX OUTDIR [--per 24] [--seed 1]
"""
import json, os, sys, time, random, argparse, itertools
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
import fp
from subset_relax import directions
import exact


def subsets(C, k, dirs, rng, per):
    n = len(C); out = []
    for d in dirs: out.append(tuple(sorted(np.argsort(-(C @ d))[:k])))
    for i in range(n): out.append(tuple(sorted(np.argsort(((C - C[i]) ** 2).sum(1))[:k])))
    for _ in range(per):                                  # random connected growth
        S = [rng.randrange(n)]
        while len(S) < k:
            rest = [j for j in range(n) if j not in S]
            d = np.array([min(np.linalg.norm(C[j] - C[i]) for i in S) for j in rest])
            w = np.exp(-(d - d.min()) * 3.0); j = rng.choices(rest, weights=w)[0]
            S.append(j)
        out.append(tuple(sorted(S)))
    seen, res = set(), []
    for s in out:
        s = tuple(int(x) for x in s)
        if s not in seen: seen.add(s); res.append(s)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('family'); ap.add_argument('kmin', type=int); ap.add_argument('kmax', type=int)
    ap.add_argument('nmax', type=int); ap.add_argument('out')
    ap.add_argument('--per', type=int, default=24); ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--tlimit', type=float, default=30)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True); rng = random.Random(a.seed)
    log = open(os.path.join(a.out, f'{a.family}.log'), 'a')
    for k in range(a.kmin, a.kmax + 1):
        try: rk, _, _ = fp.load(a.family, k)
        except FileNotFoundError: continue
        piece, cont = rk['piece'], rk['container']; best = rk['s_full']; won = None
        dirs = directions(exact.Problem(piece, cont))
        for N in range(k + 1, a.nmax + 1):
            try: rN, C, R = fp.load(a.family, N)
            except FileNotFoundError: continue
            for sub in subsets(C, k, dirs, rng, a.per):
                t0 = time.time()
                try:
                    sF, sP, CP, RP = fp.FP(piece, cont, C[list(sub)], [R[i] for i in sub], tlimit=a.tlimit)
                except Exception as e:
                    print(f'{a.family} {N}->{k} {sub}: error {e}', file=log, flush=True); continue
                flag = ''
                if sP < best - 1e-9:
                    best = sP; flag = '  IMPROVES'
                    won = dict(piece=piece, container=cont, n=k, s=sP, C=(np.asarray(CP)).tolist(),
                               Q=[exact.R_to_quat(r).tolist() for r in RP], arrow=f'subset N{N}->{k}',
                               subset=list(sub), record_before=rk['s_full'])
                    json.dump(won, open(os.path.join(a.out, f'{a.family}_n{k:02d}.json'), 'w'))
                print(f'{a.family} {N:3d}->{k:3d} {str(sub):40s} F {sF:.6f} P {sP:.9f} rec {rk["s_full"]:.9f}{flag} '
                      f'{time.time() - t0:.0f}s', file=log, flush=True)
        print(f'== {a.family} k={k}: record {rk["s_full"]:.10f} best arrow {best:.10f}{" NEW" if won else ""}',
              file=log, flush=True)


if __name__ == '__main__':
    main()
