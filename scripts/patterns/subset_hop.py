"""Subset relaxation with the soft-to-rigid simulator (credit: PingYou Ltd, "N19 recovers N6 and N8").

Keep k pieces of the archived best N-packing (state/best/<problem>/nNN.json, internal units), drop the rest,
soften, shake briefly and re-sharpen under pressure (src/sim.js hop with remove = the dropped pieces), then
tighten with the certified sequential LP (engine.tighten). Subsets: caps along container directions, nearest
clusters around pieces and container vertices, the central core, and the greedy LP deletion chain.

Usage: python3 scripts/patterns/subset_hop.py PROBLEM N K [--reps R] [--max M] [--out FILE]
"""
import json, os, sys, time, argparse, random
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'src')); sys.path.insert(0, os.path.join(ROOT, 'scripts'))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'patterns'))
import exact
import engine as E
from subset_relax import directions, greedy_deletion


def subsets(pb, C, R, k, limit):
    n = len(C); subs = [greedy_deletion(pb, C, R, k)]
    CON = exact.SOL[pb.container]; V = np.array(CON['V'], float)
    for d in directions(pb):
        subs.append(tuple(sorted(np.argsort(-(C @ d))[:k])))
    Lh = None
    for v in V:                                               # clusters at container vertices (scaled into place)
        x = v / np.linalg.norm(v) * np.linalg.norm(C, axis=1).max()
        subs.append(tuple(sorted(np.argsort(((C - x) ** 2).sum(1))[:k])))
    for i in range(n):
        subs.append(tuple(sorted(np.argsort(((C - C[i]) ** 2).sum(1))[:k])))
    subs.append(tuple(sorted(np.argsort((C ** 2).sum(1))[:k])))
    seen, out = set(), []
    for s in subs:
        s = tuple(int(i) for i in s)
        if s not in seen: seen.add(s); out.append(s)
    return out[:limit]


def run(problem, N, K, reps=1, limit=30, log=print, seed=1):
    caseN = E.load_case(problem, N); caseK = E.load_case(problem, K)
    best = caseN['best']; tgt = caseK['best']['s'] if caseK and caseK['best'] else None
    piece, container = E.PID[problem]
    pb = E.problem(problem)
    C = np.array(best['C']); Q = best['Q']; R = [exact.quat_to_R(np.array(q) / np.linalg.norm(q)) for q in Q]
    sim = E.Sim(); rng = random.Random(seed)
    res = []
    for sub in subsets(pb, C, R, K, limit):
        drop = [i for i in range(N) if i not in sub]
        for r in range(reps):
            sd = rng.randrange(1, 2 ** 31 - 1)
            raw = sim.call(dict(op='hop', piece=piece, container=container, seed=sd, C=C.tolist(), Q=Q,
                                L=2 * pb.rhoC * best['s'], remove=drop, add=0, rh=rng.uniform(0.12, 0.3),
                                expand=0.0, morph=4000 + 150 * K, settle=1000 + 25 * K))
            row = {'piece': piece, 'container': container, 'problem': problem, 'n': K, 'seed': sd, 'mode': 'subset',
                   'B': 0, 'C': raw['C'], 'Q': raw['Q']}
            out = E.tighten(row, tgt, K, 0.05)
            res.append((out['s'], sub, raw['s'], out))
            log(f'{problem} {N}->{K} subset {sub}: raw {raw["s"]:.6f} -> {out["s"]:.10f}  (best {tgt})')
    res.sort(key=lambda x: x[0])
    return res, tgt


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('problem'); ap.add_argument('N', type=int); ap.add_argument('K', type=int)
    ap.add_argument('--reps', type=int, default=1); ap.add_argument('--max', type=int, default=30)
    ap.add_argument('--out')
    a = ap.parse_args()
    t0 = time.time()
    res, tgt = run(a.problem, a.N, a.K, a.reps, a.max)
    s, sub, raw, out = res[0]
    print(f'BEST {a.problem} {a.N}->{a.K}: {s:.12f} (archive best {tgt}) subset {sub}  {time.time() - t0:.0f}s')
    if a.out:
        json.dump(dict(out, subset=list(sub), source_n=a.N, raw=raw), open(a.out, 'w'))
