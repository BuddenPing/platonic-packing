"""Generate the band lemmas of OctInCube.lean: exact rational constants, and nlinarith hints found by LP.

Per row: r >= 0, m >= r/3, 6m^2 - 4mr + r^2 >= 1. Goal r(1-m) <= a + b r^2 on lo <= r^2 <= hi. With z = r m and
L = r - a - b r^2: if z < L then q(L) > q(z) >= 0 where q(z) = 6z^2 - 4r^2 z + r^4 - r^2, so it suffices that
P(r) = q(L(r)) <= 0 whenever L(r) > r^2/3 (and r in the band)."""
import sympy as sp, numpy as np, json, sys
from scipy.optimize import linprog
r = sp.symbols('r'); R = sp.Rational
muA = lambda x: (2 * x + np.sqrt(np.clip(6 - 2 * x * x, 0, None))) / 6
phi = lambda x: x * (1 - muA(x))

def P_of(a, b):
    L = r - a - b * r**2
    return sp.expand(6 * L**2 - 4 * r**2 * L + r**4 - r**2), sp.expand(L - r**2 / 3)

def sqrt_lo(x, den=10000):   # rational q with q^2 <= x
    q = R(int(np.floor(np.sqrt(float(x)) * den)), den)
    while q * q > x: q -= R(1, den)
    return q
def sqrt_hi(x, den=10000):
    q = R(int(np.ceil(np.sqrt(float(x)) * den)), den)
    while q * q < x: q += R(1, den)
    return q

def certificate(P, G, lo, hi, double_root=None):
    """find lam >= 0 with -P = sum lam_k * term_k (terms nonneg on the band, G >= 0), exact match of coefficients"""
    rl, rh = sqrt_lo(lo), sqrt_hi(hi)
    lin = {'L': r - rl, 'U': rh - r, 'G': G, 'H': hi - r**2, 'Lo': r**2 - lo}
    terms = {'1': sp.Integer(1)}
    for n1, e1 in lin.items(): terms[n1] = e1
    names = list(lin)
    for i in range(len(names)):
        for j in range(i, len(names)):
            terms[names[i] + names[j]] = lin[names[i]] * lin[names[j]]
    cs = [R(k, 40) for k in range(0, 81)]
    for c in cs:
        terms[f'sq:{c}'] = (r - c)**2
        for n1, e1 in lin.items(): terms[f'{n1}sq:{c}'] = e1 * (r - c)**2
        terms[f'LUsq:{c}'] = (r - rl) * (rh - r) * (r - c)**2
    if double_root is not None:
        d = (r - double_root)**2
        terms['D'] = d
        for n1, e1 in lin.items(): terms[f'{n1}D'] = e1 * d
        for c in cs: terms[f'Dsq:{c}'] = d * (r - c)**2
        for n1 in names:
            for n2 in names: terms[f'{n1}{n2}D'] = lin[n1] * lin[n2] * d
    keys = list(terms); polys = [sp.Poly(sp.expand(terms[k]), r) for k in keys]; tgt = sp.Poly(sp.expand(-P), r)
    deg = max([p.degree() for p in polys] + [tgt.degree()])
    M = np.array([[float(p.coeff_monomial(r**d)) for p in polys] for d in range(deg + 1)])
    v = np.array([float(tgt.coeff_monomial(r**d)) for d in range(deg + 1)])
    res = linprog(np.ones(len(keys)), A_eq=M, b_eq=v, bounds=[(0, None)] * len(keys), method='highs')
    if res.status != 0: return None, rl, rh
    return [k for k, x in zip(keys, res.x) if x > 1e-11], rl, rh

if __name__ == '__main__':
    out = {}
    # tangent band
    a, b = R(1, 4), R(1, 12); T = R(209, 100)
    P, G = P_of(a, b)
    c, rl, rh = certificate(P, G, 0, T, double_root=1)
    print('tangent', c, rl, rh); out['tangent'] = dict(a=str(a), b=str(b), lo='0', hi=str(T), P=str(P), G=str(G), terms=c, rl=str(rl), rh=str(rh))
    bands = [R(209, 100), R(212, 100), R(216, 100), R(222, 100), R(230, 100), R(240, 100), R(255, 100), R(270, 100), R(285, 100), R(295, 100), R(3)]
    cs = R(4227, 10000); tot_ok = True
    for lo, hi in zip(bands[:-1], bands[1:]):
        u = np.linspace(float(lo), float(hi), 4001); f = phi(np.sqrt(u))
        bf = (f[-1] - f[0]) / float(hi - lo); af = f[0] - bf * float(lo); af += max((f - (af + bf * u)).max(), 0) + 5e-5
        bq = R(int(np.ceil(bf * 100000)), 100000); aq = R(int(np.ceil((af + 1e-5) * 100000)), 100000)
        # check the line dominates phi numerically with exact constants
        mid = (lo + hi) / 2; t = sqrt_lo(2 * (3 - mid), 1000) if mid < 3 else R(1, 20)
        t = max(t, R(1, 50))
        Sb = lambda x: (6 - 2 * x + t * t) / (2 * t)
        marg = min(1 - (aq + bq * x + cs * Sb(x)) for x in (lo, hi))
        P, G = P_of(aq, bq)
        cert, rl, rh = certificate(P, G, lo, hi)
        print(f'band [{lo},{hi}] a={aq} b={bq} t={t} margin={float(marg):+.5f} cert={cert is not None}')
        tot_ok &= cert is not None and marg > 0
        out[f'band_{lo}_{hi}'] = dict(a=str(aq), b=str(bq), lo=str(lo), hi=str(hi), t=str(t), P=str(P), G=str(G), terms=cert, rl=str(rl), rh=str(rh), margin=float(marg))
    print('all ok', tot_ok)
    json.dump(out, open('oct_bands.json', 'w'), indent=1)
