# Which records are optimal?

_6 November 2026._ A record gives an upper bound: its packing fits in a container of scale s. It is **optimal**
when no packing of the same n pieces fits in a smaller container. This file tracks which low-n records are
proven optimal in Lean, which are proven elsewhere with computer assistance, and which have strong numerical
evidence.
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
| 2 cubes in a cube (`cubincub_n02`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n02` |
| 3 cubes in a cube (`cubincub_n03`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n03` |
| 4 cubes in a cube (`cubincub_n04`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n04` |
| 5 cubes in a cube (`cubincub_n05`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n05` |
| 6 cubes in a cube (`cubincub_n06`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n06` |
| 7 cubes in a cube (`cubincub_n07`) | 2 | cube centre lemma (d = 3) + grid | `cubincub_n07` |

The five records with k^d cubes are instances of one theorem, `cubes_in_cube_optimal`: in every dimension d ≥ 1, the smallest cube
holding k^d unit cubes has side exactly k. The proof works for any rigid motions, reflections included, and only
requires disjoint interiors, so touching is allowed. Its lower bound is the general volume theorem
`card_mul_volume_le`, for congruent convex bodies in any finite-dimensional Euclidean space; its upper bound is
the grid. The prism results are instances of `prisms_in_prism_optimal`. The scale-k prism is tiled by k³ unit
prisms: k layers of k² triangles, upward ones placed as translates and downward ones as point reflections.
Distinct tiles have disjoint interiors because an interior point determines its tile. Every theorem depends only
on Lean's standard axioms (`Axioms.lean`, checked in CI).

**Cubes in a cube, n = 2–7 (`CubeCentre.lean`).** Side 2 is optimal for every n from 2 to 8. The upper bound is
the 2×2×2 grid with cubes removed. The lower bound is the **cube centre lemma in dimension 3** (`centre3`): a unit
cube placed by any rigid motion inside a cube of side s < 2 contains the centre (s/2, s/2, s/2) in its interior.
So any two such cubes share an interior point, and no two fit (the common-point lemma).

The lemma reduces to a matrix inequality, `core`. For an orthogonal matrix with columns a, b, c:

  2 (|a₀| + |a₁| + |a₂| − 1) ≤ Σᵢ |aᵢ| (|bᵢ| + |cᵢ|).

The proof has two steps.

1. **A zero entry.** If one entry of b or c is zero, the inequality is an identity. The difference of the two
   sides is 2(1 − P)(1 − Q) + 2P(1 − S)(1 − T), where P, Q, S, T ∈ [0, 1] are absolute values of remaining
   entries. This is `reduced`, and `zero_case` covers all six positions by symmetry.
2. **The general case.** Rotate (b, c) in its own plane by a unit vector (p, q). The right side is continuous on
   the unit circle, so it has a minimiser.
   - If the minimiser has a zero entry, step 1 applies.
   - If not, no entry changes sign for small t. The rotated neighbours (p ∓ tq, q ± tp)/√(1 + t²) then have
     values that average to the minimum divided by √(1 + t²). One of them is below the minimum, which is
     impossible.

The Lean proof uses no computer search. Hiroaki Hosono had proved the same inequality ("Lemma F") with
computer assistance; see section 2.

The geometric step (`centre3`) takes an image vertex in each coordinate direction. This shows the image centre
is within (s − wᵢ)/2 of s/2 in coordinate i, where wᵢ is the cube's width along that axis. Pulled back through
the isometry and combined with `core`, the container's centre lies strictly inside the unit cube.

## 2. Proven with computer assistance elsewhere, not in Lean (71 records)

Hiroaki Hosono (wand125) has computer-assisted proofs of the following results. Each was checked by two
independent checkers, and none has been peer reviewed. They are in
[wand125/square-packing](https://github.com/wand125/square-packing) (MIT; read at commit `ea1c454`,
31 Oct 2026). The catalogue records equal these values.

| Result | Records | Method |
|---|---|---|
| s_d(2) = 2 for d = 4, 5, 6 | `c8inc8_n02`–`n15`, `hc5inhc5_n02`–`n31`, `hc6inhc6_n02`–`n24` (67 records, side 2) | the cube centre lemma in dimension d (see below), then the plateau argument |
| s₃(9) = s₃(10) = 2 + 1/√2 | `cubincub_n09`, `cubincub_n10` | an 8-point lemma by interval branch and bound ([`problems/cubes-in-cube`](https://github.com/wand125/square-packing/tree/main/problems/cubes-in-cube)) |
| s₃(25) = s₃(26) = 3 | `cubincub_n25`, `cubincub_n26` | a closed counting measure by interval branch and bound ([`closed-measure`](https://github.com/wand125/square-packing/tree/main/problems/cubes-in-cube/closed-measure)) |

**The cube centre lemma.** A unit d-cube inside a cube of side less than 2 contains that cube's centre in its
interior. For a cube placed by an orthogonal matrix R, it follows from "Lemma F": Σᵢ |Rᵢⱼ| (2 − Σₖ |Rᵢₖ|) ≤ 1 for
every column j. With the common-point lemma and the 2×2×…×2 grid, it gives side 2 for every 2 ≤ n ≤ 2^d. Lean
proves that implication (`cube_plateau_of_centre_lemma`). Status by dimension:

- **d = 2.** The inequality is (u − 1)² ≥ 0 with u = |cos θ| + |sin θ|.
- **d = 3.** Proven in Lean here (`CubeCentre.core`, section 1). Hosono proved it earlier with computer
  assistance: a hand proof near the axes plus interval checks elsewhere, and later a 5-simplex spectral
  certificate. The Lean proof here uses no computer search.
- **d = 4, 5, 6.** Hosono, [`problems/cubes-n-dim`](https://github.com/wand125/square-packing/tree/main/problems/cubes-n-dim).
  - **Near an axis:** a polar-decomposition step reduces the claim to Lemma F one dimension down. It is
    formalized in Lean there for any dimension, with that lower-dimensional Lemma F as a hypothesis.
  - **Elsewhere:** a spectral bound with exact rational certificates: 557 simplices in 4D, 21,502 in 5D and
    about 2.8 million in 6D. 4D also has an interval branch-and-bound proof.
- **All d.** Open.

**Towards Lean in 4D.** Hosono's Lean theorem `near_region` takes Lemma F in dimension 3 as a hypothesis, and that
lemma is now `CubeCentre.core`. Combining the two developments, which use different Lean and Mathlib versions,
would put the 4D near-axis region in Lean. The far region, with its 557-simplex certificate, would then be the
only part of s₄(2) = 2 still outside Lean.

**Numerical check here.** The maximum of the left side of Lemma F over all rotations is exactly 1, attained at
axis-aligned placements, in every dimension d = 2–6 (`scripts/optimality/center_lemma.py`, `center_nd.py`).

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

- Lean proofs for the 71 records of section 2. The nearest target is s₄(2) = 2 (14 records): Hosono's near-axis
  step plus `CubeCentre.core`, and a Lean check of the 557-simplex far-region certificate.
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
