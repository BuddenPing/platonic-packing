"""Emit lean-optimality/PackingOptimality/Simplex5.lean (two 5-simplices in a 5-cube).

The base of the placed simplex is the order-5 Paley matrix M[i][j] = chi(j - i), chi the quadratic character
mod 5, scaled by 1/sqrt10: its rows are 5 unit-edge simplex vertices in the hyperplane sum x = 0.
"""
import sys

chi = {0: 0, 1: 1, 4: 1, 2: -1, 3: -1}
M = [[chi[(j - i) % 5] for j in range(5)] for i in range(5)]
R3, R10 = "Real.sqrt 3", "Real.sqrt 10"


def num(m):
    return {0: "0", 1: "1", -1: "(-1)"}[m]


def vrow(i):
    return f"pt5 {' '.join(f'({R10} / 10 * {num(m)})' for m in M[i])}"


def arow(i):
    return f"pt5 {' '.join(f'({R10} / 5 * {num(m)} - {R3} / 15)' for m in M[i])}"


vs = ",\n    ".join([f"pt5 ({R3} / 5) ({R3} / 5) ({R3} / 5) ({R3} / 5) ({R3} / 5)"] + [vrow(i) for i in range(5)])
as_ = ",\n    ".join([f"pt5 ({R3} / 3) ({R3} / 3) ({R3} / 3) ({R3} / 3) ({R3} / 3)"] + [arow(i) for i in range(5)])

out = open(sys.argv[1]).read().replace("@@VERTICES@@", vs).replace("@@NORMALS@@", as_)
open(sys.argv[2], "w").write(out)
