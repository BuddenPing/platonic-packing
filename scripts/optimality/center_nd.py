import numpy as np
from scipy.optimize import minimize
from scipy.stats import special_ortho_group
from scipy.linalg import expm
def F(R):
    w = np.abs(R).sum(1)
    return max((np.abs(R[:, j]) * (1 - w / 2)).sum() for j in range(R.shape[0]))
def skew(v, d):
    A = np.zeros((d, d)); iu = np.triu_indices(d, 1); A[iu] = v; return A - A.T
for d in (2, 3, 4, 5, 6):
    Rs = special_ortho_group.rvs(d, size=20000, random_state=d)
    vals = np.array([F(R) for R in Rs]); best = vals.max()
    for k in np.argsort(vals)[-30:]:
        R0 = Rs[k]; m = d * (d - 1) // 2
        res = minimize(lambda v: -F(R0 @ expm(skew(v, d))), np.zeros(m), method='Nelder-Mead',
                       options=dict(xatol=1e-12, fatol=1e-14, maxiter=40000, maxfev=40000))
        best = max(best, -res.fun)
    print(d, 'max F =', round(best, 10), '(lemma needs <= 0.5)')
