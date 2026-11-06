"""Does every unit cube inside the cube [-a,a]^3 (a<1) contain the origin?
For rotation R (columns = cube axes) the farthest the centre p can be from the origin along axis r_j, subject to
containment |p_i| <= a - w_i/2 (w_i = row-1-norm of R = width of the unit cube along e_i), is
F_j(R) = sum_i |R_ij| (a - w_i/2). The origin is outside the cube iff some F_j >= 1/2 is achievable."""
import numpy as np
from scipy.optimize import minimize
from scipy.spatial.transform import Rotation as Rot
def F(R, a=1.0):
    w = np.abs(R).sum(1)
    return max((np.abs(R[:, j]) * (a - w / 2)).sum() for j in range(3))
def feasible(R, a=1.0): return (np.abs(R).sum(1) <= 2 * a).all()
best = -1; bestR = None
rs = Rot.random(200000, random_state=1).as_matrix()
vals = [F(R) for R in rs]
i = int(np.argmax(vals)); print('random max', vals[i])
for k in np.argsort(vals)[-50:]:
    q0 = Rot.from_matrix(rs[k]).as_rotvec()
    res = minimize(lambda v: -F(Rot.from_rotvec(v).as_matrix()), q0, method='Nelder-Mead', options=dict(xatol=1e-12, fatol=1e-14, maxiter=20000))
    v = -res.fun
    if v > best: best, bestR = v, Rot.from_rotvec(res.x).as_matrix()
print('max F over rotations (a=1):', best); print(np.round(bestR, 6))
# also for 2D (squares) analogue
def F2(t, a=1.0):
    R = np.array([[np.cos(t), -np.sin(t)], [np.sin(t), np.cos(t)]]); w = np.abs(R).sum(1)
    return max((np.abs(R[:, j]) * (a - w / 2)).sum() for j in range(2))
ts = np.linspace(0, np.pi / 2, 200001); print('2D max', max(F2(t) for t in ts))
