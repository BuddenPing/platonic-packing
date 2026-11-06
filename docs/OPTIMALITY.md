# Which records are optimal?

_6 November 2026._ A record gives an upper bound: its packing fits in a container of scale s. It is **optimal**
when no packing of the same n pieces fits in a smaller container. This file tracks which low-n records are
proven optimal, which are optimal conditional on a single lemma, and which have strong numerical evidence.
Machine-readable list: [`optimality.json`](optimality.json). Lean proofs: [`lean-optimality/`](../lean-optimality).

## 1. Proven in Lean

| Record | Optimal side | Argument | Lean theorem |
|---|---|---|---|
| 8 cubes in a cube (`cubincub_n08`) | 2 | volume bound + 2×2×2 grid | `cubincub_n08` |
| 27 cubes in a cube (`cubincub_n27`) | 3 | volume bound + 3×3×3 grid | `cubincub_n27` |
| 64 cubes in a cube (`cubincub_n64`) | 4 | volume bound + 4×4×4 grid | `cubincub_n64` |
| 16 tesseracts in a tesseract (`c8inc8_n16`) | 2 | volume bound + grid | `c8inc8_n16` |
| 32 5-cubes in a 5-cube (`hc5inhc5_n32`) | 2 | volume bound + grid | `hc5inhc5_n32` |
| 8 triangular prisms in a triangular prism (`pr3inpr3_n08`) | 2 | volume bound + tiling | `pr3inpr3_n08` |
| 27 triangular prisms in a triangular prism (`pr3inpr3_n27`) | 3 | volume bound + tiling | `pr3inpr3_n27` |
| 64 triangular prisms in a triangular prism (`pr3inpr3_n64`) | 4 | volume bound + tiling | `pr3inpr3_n64` |

All five are instances of one theorem, `cubes_in_cube_optimal`: in every dimension d ≥ 1, the smallest cube
holding k^d unit cubes has side exactly k. The proof works for any rigid motions, reflections included, and only
requires disjoint interiors, so touching is allowed. Its lower bound is the general volume theorem
`card_mul_volume_le`, for congruent convex bodies in any finite-dimensional Euclidean space; its upper bound is
the grid. The prism results are instances of `prisms_in_prism_optimal`. The scale-k prism is tiled by k³ unit
prisms: k layers of k² triangles, upward ones placed as translates and downward ones as point reflections.
Distinct tiles have disjoint interiors because an interior point determines its tile. Every theorem depends only
on Lean's standard axioms (`Axioms.lean`, checked in CI).

## 2. Optimal if the cube centre lemma holds: cubes, 2 ≤ n ≤ 2^d (76 records)

**Cube centre lemma.** A unit d-cube inside a cube of side less than 2 contains that cube's centre in its
interior.

If the lemma holds, no two unit cubes fit in a cube of side below 2 (the common-point lemma, proven in Lean). The
2×2×…×2 grid then shows that side 2 is optimal for every 2 ≤ n ≤ 2^d. Lean proves this implication
(`cube_plateau_of_centre_lemma`). It covers `cubincub_n02`–`n07`, `c8inc8_n02`–`n15`,
`hc5inhc5_n02`–`n31` and `hc6inhc6_n02`–`n24` (the catalogue stops at n = 24 in 6D).

Status of the lemma:
- **Reformulation.** If the cube is placed by an orthogonal matrix R, the lemma is equivalent to
  Σᵢ |Rᵢⱼ| (2 − Σₖ |Rᵢₖ|) ≤ 1 for every column j.
- **Numerical check.** The maximum over all rotations is exactly 1/2, attained at axis-aligned placements, in
  every dimension d = 2–6 (`scripts/optimality/center_lemma.py`, `center_nd.py`).
- **d = 2.** The inequality is (u − 1)² ≥ 0 with u = |cos θ| + |sin θ|.
- **d = 3: proof on paper.**
  1. Write the other two columns as (b, c) = rotation by θ of a fixed orthonormal pair.
  2. The left side is then a polygonal seminorm of (cos θ, sin θ). On each cone where all signs are fixed it is
     linear, and a point z = λz₁ + μz₂ on the unit circle has λ + μ ≥ 1. So its minimum lies at a breakpoint,
     where one entry of b or c is zero.
  3. There the inequality reduces to 2[(1 − q)(1 − p) + p(1 − s)(1 − t)] ≥ 0, with p, q, s, t ∈ [0,1] the
     absolute values of the remaining entries.
- **General d.** Open. An equivalent minimax form: there is μ ∈ [0,1]^d with Σₖ Rᵢₖ⁻ + (Rμ)ᵢ ≥ 1 for every row
  i, where Rᵢₖ⁻ = max(−Rᵢₖ, 0).

## 3. n = 2: numerical evidence for 20 Platonic records

For n = 2 a stronger fact holds. Let s_c be the scale below which every placement of a single piece contains
the container's centre in its interior. The common-point lemma gives s(2) ≥ s_c. When the container is
centrally symmetric (cube, octahedron, dodecahedron, icosahedron), equality holds: the best single placement that
avoids the centre, together with its reflection through the centre, is a 2-packing. So **s(2) is a one-piece
problem**, the best fit of one piece beside the centre.

A global search over rotations, with exact linear programming over translations (`scripts/optimality/center_all.py`), finds
s_c equal to the record value to about 7 significant digits in all 20 cases below. That includes 2 cubes in a
tetrahedron, whose container is not centrally symmetric. So each of these n = 2 records is optimal to within
about 10⁻⁷, as far as the search can tell. This is evidence, not proof: the search over rotations could miss
the worst placement.

| Record | s | Closed form | Found by |
|---|---|---|---|
| 2 octahedra in an octahedron (`octinoct_n02`) | 1.9331196 | — | Alejandro Zarzuelo |
| 2 icosahedra in an icosahedron (`icoinico_n02`) | 1.9630860 | — | Alejandro Zarzuelo |
| 2 dodecahedra in a dodecahedron (`dodindod_n02`) | 1.9875981 | — | Alejandro Zarzuelo |
| 2 cubes in an octahedron (`cubinoct_n02`) | 2.4142136 | 1 + √2 | Alejandro Zarzuelo |
| 2 octahedra in a cube (`octincub_n02`) | 1.4142136 | √2 | Alejandro Zarzuelo |
| 2 dodecahedra in an icosahedron (`dodinico_n02`) | 2.8944272 | (10 + 2√5)/5 | Alejandro Zarzuelo |
| 2 icosahedra in a dodecahedron (`icoindod_n02`) | 1.2360680 | -1 + √5 | Alejandro Zarzuelo |
| 2 tetrahedra in a cube (`tetincub_n02`) | 0.9428091 | — | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 tetrahedra in an octahedron (`tetinoct_n02`) | 1.1547006 | — | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 tetrahedra in a dodecahedron (`tetindod_n02`) | 0.5826881 | — | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 tetrahedra in an icosahedron (`tetinico_n02`) | 0.8585154 | — | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 cubes in a tetrahedron (`cubintet_n02`) | 4.3794455 | 2 + √(72√2 + 102)/6 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 cubes in a dodecahedron (`cubindod_n02`) | 0.9155439 | — | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 cubes in an icosahedron (`cubinico_n02`) | 1.4886140 | -53/38 + 49√5/38 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 octahedra in a dodecahedron (`octindod_n02`) | 0.7400667 | -4/3 + (2√(3 - √5) + 2√5)/3 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 octahedra in an icosahedron (`octinico_n02`) | 1.0803631 | √(28 - 12√5) | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 dodecahedra in a cube (`dodincub_n02`) | 3.8368484 | 16/267 + (334√2 + √(63020√2 + 198270))/267 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 dodecahedra in an octahedron (`dodinoct_n02`) | 4.7268394 | √(64527√5 + 146083)/114 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 icosahedra in a cube (`icoincub_n02`) | 2.4907120 | 1 + 2√5/3 | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |
| 2 icosahedra in an octahedron (`icoinoct_n02`) | 2.9953525 | √(2√5 + 9/2) | Timo Berthold, Dominik Kamp, Gioni Mexi, Sebastian Pokutta and Imre Pólik |

The centre argument fails for tetrahedron containers with tetrahedra, octahedra, dodecahedra or icosahedra as
pieces: a single piece can avoid the centroid at the record scale. The plateaus there, for example octahedra in
a tetrahedron at s = 3 for n = 2–4 and icosahedra in a tetrahedron at s = 5.3582 for n = 2–4, need a different
argument.

## 4. Next targets

- Formalize the cube centre lemma for d = 3 (closes cubincub n = 2–7), then look for a general-d proof.
- n = 2: certify s_c rigorously for one pair, for example 2 octahedra in a cube at √2. That needs a rigorous
  global bound over all rotations.
- Plateaus starting above n = 2, which need new ideas:
  - octahedra in an octahedron, n = 3–6 (s = 2)
  - tetrahedra in a tetrahedron, n = 3–4 (2)
  - dodecahedra in a dodecahedron, n = 3–4 (2) and n = 5–6 (√5)
  - icosahedra in an octahedron, n = 4–6
  - dodecahedra in a cube, n = 3–4 (2 + √5)
  - octahedra in a cube, n = 7–8 (19√2/15)
  - cubes in a dodecahedron, n = 6–8 (√5 − 1)
