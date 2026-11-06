"""Subset relaxation: derive k-piece packings from a certified N-piece record.

Pattern credited to PingYou Ltd ("N19 recovers N6 and N8", square antiprisms, Nov 2026): select k bodies of a
larger certified packing, then let the container shrink while positions and orientations adjust. Here the
selection is by geometric heuristics (caps along container directions, nearest-neighbour clusters, greedy
deletion), and the relaxation is the repository's certified sequential-LP tightening (src/fastslp.py), whose
every accepted round is legalized and certified.

Usage: python3 scripts/patterns/subset_relax.py FAMILY N K [--tlimit SEC] [--max SUBSETS]
"""
import json, math, os, sys, time, itertools, argparse, glob
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'src'))
import exact, fastslp


def load(family, n):
    f = os.path.join(ROOT, 'records', family, f'{family}_n{n:02d}.json')
    if not os.path.exists(f): return None
    return json.load(open(f))


def internal(rec):
    pb = exact.Problem(rec['piece'], rec['container'])
    P = np.array(rec['pieces'], float)
    C = P[:, :3] * pb.edge
    R = [exact.quat_to_R(q / np.linalg.norm(q)) for q in P[:, 3:]]
    return pb, C, R


def directions(pb):
    """Unit directions: container face normals, vertex directions and edge-midpoint directions."""
    CON = exact.SOL[pb.container]
    V = np.array(CON['V'], float); D = [np.array(n, float) for n in CON['normals']]
    D += [v / np.linalg.norm(v) for v in V]
    for i, j in CON['edges']:
        m = (V[i] + V[j]) / 2
        if np.linalg.norm(m) > 1e-9: D.append(m / np.linalg.norm(m))
    out = []
    for d in D:
        if all(np.linalg.norm(d - e) > 1e-6 for e in out): out.append(d)
    return out


def candidate_subsets(pb, C, R, k, limit):
    n = len(C); subs = []
    for d in directions(pb):                                   # caps
        subs.append(tuple(sorted(np.argsort(-(C @ d))[:k])))
    for i in range(n):                                         # nearest clusters around each piece
        subs.append(tuple(sorted(np.argsort(((C - C[i]) ** 2).sum(1))[:k])))
    cen = C.mean(0)                                            # central core
    subs.append(tuple(sorted(np.argsort(((C - cen) ** 2).sum(1))[:k])))
    seen, out = set(), []
    for s in subs:
        if s not in seen: seen.add(s); out.append(s)
    return out[:limit]


def greedy_deletion(pb, C, R, k):
    """Delete pieces one by one, each time the piece whose removal lets the (unoptimized) container shrink most."""
    idx = list(range(len(C)))
    while len(idx) > k:
        best = None
        for j in idx:
            rest = [i for i in idx if i != j]
            L, _ = exact.tight_container(pb, C[rest], [R[i] for i in rest])
            if best is None or L < best[0]: best = (L, j)
        idx.remove(best[1])
    return tuple(idx)


def relax(pb, C, R, sub, tlimit):
    Cs = C[list(sub)]; Rs = [R[i] for i in sub]
    L0, _, C0 = fastslp.certify_fast(pb, Cs, Rs)
    L, C1, R1, hist = fastslp.solve(pb, C0, Rs, L0, outer=400, tlimit=tlimit)
    L2, _, C2 = fastslp.certify_fast(pb, C1, R1)
    return pb.s_of_L(L0), pb.s_of_L(L2), C2, R1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('family'); ap.add_argument('N', type=int); ap.add_argument('K', type=int)
    ap.add_argument('--tlimit', type=float, default=60); ap.add_argument('--max', type=int, default=40)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    rec = load(a.family, a.N); tgt = load(a.family, a.K)
    pb, C, R = internal(rec)
    subs = [greedy_deletion(pb, C, R, a.K)] + candidate_subsets(pb, C, R, a.K, a.max)
    best = None
    t0 = time.time()
    for sub in subs:
        s0, s1, C2, R2 = relax(pb, C, R, sub, a.tlimit)
        print(f'subset {sub}: start {s0:.9f} -> {s1:.9f}   (record k: {tgt["s_full"] if tgt else None})', flush=True)
        if best is None or s1 < best[0]: best = (s1, sub, C2, R2)
    print(f'best {best[0]:.12f} from {a.family} N={a.N}, k={a.K}; record {tgt["s_full"] if tgt else None}; {time.time()-t0:.0f}s')
    if a.out:
        json.dump(dict(piece=pb.piece, container=pb.container, n=a.K, C=np.asarray(best[2]).tolist(),
                       Q=[exact.R_to_quat(r).tolist() for r in best[3]], s=best[0], source=f'{a.family}_n{a.N:02d}',
                       subset=list(map(int, best[1]))), open(a.out, 'w'))


if __name__ == '__main__':
    main()
