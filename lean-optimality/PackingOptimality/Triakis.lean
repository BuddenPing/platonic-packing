import PackingOptimality.Patterns
import PackingOptimality.Prisms
import PackingOptimality.CentreGeneral

/-!
# Triakis tetrahedra: the recursion `4ᵏ` pieces at scale `(5/3)ᵏ`

The catalogue's 4-piece record for triakis tetrahedra in a triakis tetrahedron has scale `5/3`. Composition
(`Packing.pow`) turns it into `4ᵏ` pieces at `(5/3)ᵏ`: 16 at `25/9` and 64 at `125/27`. These are the catalogue's 16-
and 64-piece records, identified as composites by PingYou Ltd ("a four-piece packing, squared", "cubed").
Deletion gives every smaller count at the same scale (`Packing.restrict`), e.g. the 12-piece record at `25/9`.

**The piece.** The triakis tetrahedron of the catalogue (`src/solids.json`):
`Kt = {x : ⟨m, x⟩ ≤ 9√2/4}` over its 12 face normals `m` (the integer vectors of the form `(1, 3, 1)`, up to the
tetrahedral symmetries, divided by `√11`; written here undivided).

**The 4-piece packing at `5/3`.** Piece `i` is `Rᵢ Kt + (√2/2) σᵢ`, where the rotations `Rᵢ` have entries `±1/3`,
`±2/3`, and `σᵢ ∈ {(-1, 1, 1), (-1, -1, -1), (1, 1, -1), (1, -1, 1)}`. Containment is a linear consequence of the 12
face inequalities (`linarith` finds the multipliers). The six pairs touch along the planes `xₐ ± x_b = 0`.
-/

namespace PackingOptimality.Triakis

open Set
open scoped Pointwise RealInnerProductSpace

/-- The face inequalities `⟨m_f, x⟩ ≤ 9√2/4` of the triakis tetrahedron. -/
def Kt : Set P3 := {x |
  -x 0 + 3 * x 1 - x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ -3 * x 0 + x 1 - x 2 ≤ 9 * Real.sqrt 2 / 4 ∧
  -x 0 + x 1 - 3 * x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ x 0 + 3 * x 1 + x 2 ≤ 9 * Real.sqrt 2 / 4 ∧
  x 0 + x 1 + 3 * x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ 3 * x 0 + x 1 + x 2 ≤ 9 * Real.sqrt 2 / 4 ∧
  -x 0 - x 1 + 3 * x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ -3 * x 0 - x 1 + x 2 ≤ 9 * Real.sqrt 2 / 4 ∧
  -x 0 - 3 * x 1 + x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ 3 * x 0 - x 1 - x 2 ≤ 9 * Real.sqrt 2 / 4 ∧
  x 0 - x 1 - 3 * x 2 ≤ 9 * Real.sqrt 2 / 4 ∧ x 0 - 3 * x 1 - x 2 ≤ 9 * Real.sqrt 2 / 4}

theorem mem_smul_Kt {s : ℝ} (hs : 0 < s) {x : P3}
    (h : -x 0 + 3 * x 1 - x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ -3 * x 0 + x 1 - x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧
      -x 0 + x 1 - 3 * x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ x 0 + 3 * x 1 + x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧
      x 0 + x 1 + 3 * x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ 3 * x 0 + x 1 + x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧
      -x 0 - x 1 + 3 * x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ -3 * x 0 - x 1 + x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧
      -x 0 - 3 * x 1 + x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ 3 * x 0 - x 1 - x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧
      x 0 - x 1 - 3 * x 2 ≤ s * (9 * Real.sqrt 2 / 4) ∧ x 0 - 3 * x 1 - x 2 ≤ s * (9 * Real.sqrt 2 / 4)) :
    x ∈ s • Kt := by
  refine ⟨s⁻¹ • x, ?_, by simp [smul_smul, hs.ne']⟩
  have hi : 0 < s⁻¹ := inv_pos.mpr hs
  have e : s⁻¹ * (s * (9 * Real.sqrt 2 / 4)) = 9 * Real.sqrt 2 / 4 := by field_simp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [Kt, Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h0 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h1 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h2 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h3 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h4 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h5 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h6 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h7 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h8 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h9 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h10 hi.le; rw [e] at this; linarith
  · have := mul_le_mul_of_nonneg_left h11 hi.le; rw [e] at this; linarith

/-! ## The four rotations (entries `±1/3`, `±2/3`) -/

/-- The linear map with matrix `A / 3`. -/
noncomputable def lin3 (A : Fin 3 → Fin 3 → ℝ) : P3 →ₗ[ℝ] P3 where
  toFun y := pt ((A 0 0 * y 0 + A 0 1 * y 1 + A 0 2 * y 2) / 3) ((A 1 0 * y 0 + A 1 1 * y 1 + A 1 2 * y 2) / 3)
    ((A 2 0 * y 0 + A 2 1 * y 1 + A 2 2 * y 2) / 3)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r y := by ext i; fin_cases i <;> simp <;> ring

theorem lin3_apply (A : Fin 3 → Fin 3 → ℝ) (y : P3) : lin3 A y =
    pt ((A 0 0 * y 0 + A 0 1 * y 1 + A 0 2 * y 2) / 3) ((A 1 0 * y 0 + A 1 1 * y 1 + A 1 2 * y 2) / 3)
      ((A 2 0 * y 0 + A 2 1 * y 1 + A 2 2 * y 2) / 3) := rfl

def A0 : Fin 3 → Fin 3 → ℝ := ![![2, 2, -1], ![1, -2, -2], ![-2, 1, -2]]
def A1 : Fin 3 → Fin 3 → ℝ := ![![-2, -2, -1], ![1, -2, 2], ![-2, 1, 2]]
def A2 : Fin 3 → Fin 3 → ℝ := ![![1, 2, 2], ![-2, -1, 2], ![2, -2, 1]]
def A3 : Fin 3 → Fin 3 → ℝ := ![![1, -2, -2], ![2, -1, 2], ![-2, -2, 1]]

theorem inner3 (u y : P3) : ⟪u, y⟫ = u 0 * y 0 + u 1 * y 1 + u 2 * y 2 := by
  rw [CentreGeneral.inner_sum, Fin.sum_univ_three]

noncomputable def rot (A : Fin 3 → Fin 3 → ℝ) (h : ∀ x y : P3, ⟪lin3 A x, lin3 A y⟫ = ⟪x, y⟫) : P3 ≃ₗᵢ[ℝ] P3 :=
  (LinearMap.isometryOfInner (lin3 A) h).toLinearIsometryEquiv rfl

theorem orth (A : Fin 3 → Fin 3 → ℝ) (hA : A = A0 ∨ A = A1 ∨ A = A2 ∨ A = A3) :
    ∀ x y : P3, ⟪lin3 A x, lin3 A y⟫ = ⟪x, y⟫ := by
  intro x y
  rw [inner3, inner3, lin3_apply, lin3_apply]
  rcases hA with rfl | rfl | rfl | rfl <;> simp [A0, A1, A2, A3] <;> ring

def Amat : Fin 4 → Fin 3 → Fin 3 → ℝ := ![A0, A1, A2, A3]

theorem Amat_cases (i : Fin 4) : Amat i = A0 ∨ Amat i = A1 ∨ Amat i = A2 ∨ Amat i = A3 := by
  fin_cases i <;> simp [Amat]

/-- The centres `(√2/2) σᵢ`. -/
noncomputable def cen : Fin 4 → P3 := ![
  pt (-(Real.sqrt 2 / 2)) (Real.sqrt 2 / 2) (Real.sqrt 2 / 2),
  pt (-(Real.sqrt 2 / 2)) (-(Real.sqrt 2 / 2)) (-(Real.sqrt 2 / 2)),
  pt (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)),
  pt (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)) (Real.sqrt 2 / 2)]

noncomputable def g (i : Fin 4) : P3 ≃ᵃⁱ[ℝ] P3 :=
  (rot (Amat i) (orth _ (Amat_cases i))).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ P3 (cen i))

theorem g_apply (i : Fin 4) (y : P3) : g i y = cen i + lin3 (Amat i) y := rfl

theorem s2pos : 0 < Real.sqrt 2 := by positivity

/-! ## Containment -/

set_option maxHeartbeats 4000000 in
theorem inside (i : Fin 4) : g i '' Kt ⊆ (5 / 3 : ℝ) • Kt := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hy
  have h2 := s2pos
  apply mem_smul_Kt (by norm_num)
  rw [g_apply]
  fin_cases i <;> simp [cen, Amat, A0, A1, A2, A3, lin3_apply] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Separation along `xₐ ± x_b = 0` -/

/-- The functional `sa xₐ + sb x_b`. -/
noncomputable def f2 (a b : Fin 3) (sa sb : ℝ) : P3 →L[ℝ] ℝ :=
  sa • EuclideanSpace.proj a + sb • EuclideanSpace.proj b

theorem f2_apply (a b : Fin 3) (sa sb : ℝ) (x : P3) : f2 a b sa sb x = sa * x a + sb * x b := rfl

theorem f2_surj (a b : Fin 3) (hab : a ≠ b) (sa sb : ℝ) (hsa : sa ≠ 0) : Function.Surjective (f2 a b sa sb) :=
  fun t => ⟨EuclideanSpace.single a (t / sa), by
    rw [f2_apply]; simp [Ne.symm hab]; field_simp⟩

theorem sep {i j : Fin 4} {a b : Fin 3} (hab : a ≠ b) {sa sb : ℝ} (hsa : sa ≠ 0)
    (hi : ∀ y ∈ Kt, f2 a b sa sb (g i y) ≤ 0) (hj : ∀ y ∈ Kt, 0 ≤ f2 a b sa sb (g j y)) :
    Disjoint (interior (g i '' Kt)) (interior (g j '' Kt)) :=
  interior_disjoint_of_separated (f2 a b sa sb) (f2_surj a b hab sa sb hsa) (c := 0)
    (by rintro _ ⟨y, hy, rfl⟩; exact hi y hy) (by rintro _ ⟨y, hy, rfl⟩; exact hj y hy)

macro "side" : tactic => `(tactic| (
  intro y hy
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := hy
  have h2 := s2pos
  rw [f2_apply, g_apply]
  simp [cen, Amat, A0, A1, A2, A3, lin3_apply]
  linarith))

theorem d01 : Disjoint (interior (g 0 '' Kt)) (interior (g 1 '' Kt)) :=
  sep (a := 1) (b := 2) (by decide) (sa := -1) (sb := -1) (by norm_num) (by side) (by side)
theorem d02 : Disjoint (interior (g 0 '' Kt)) (interior (g 2 '' Kt)) :=
  sep (a := 0) (b := 2) (by decide) (sa := 1) (sb := -1) (by norm_num) (by side) (by side)
theorem d03 : Disjoint (interior (g 0 '' Kt)) (interior (g 3 '' Kt)) :=
  sep (a := 0) (b := 1) (by decide) (sa := 1) (sb := -1) (by norm_num) (by side) (by side)
theorem d12 : Disjoint (interior (g 1 '' Kt)) (interior (g 2 '' Kt)) :=
  sep (a := 0) (b := 1) (by decide) (sa := 1) (sb := 1) (by norm_num) (by side) (by side)
theorem d13 : Disjoint (interior (g 1 '' Kt)) (interior (g 3 '' Kt)) :=
  sep (a := 0) (b := 2) (by decide) (sa := 1) (sb := 1) (by norm_num) (by side) (by side)
theorem d23 : Disjoint (interior (g 2 '' Kt)) (interior (g 3 '' Kt)) :=
  sep (a := 1) (b := 2) (by decide) (sa := -1) (sb := 1) (by norm_num) (by side) (by side)

/-- **Four triakis tetrahedra in a triakis tetrahedron of scale `5/3`.** -/
noncomputable def ktt4 : Packing Kt Kt (5 / 3) 4 where
  g := g
  inside := inside
  disjoint i j hij :=
    match i, j, hij with
    | 0, 0, h => absurd rfl h
    | 0, 1, _ => d01 | 0, 2, _ => d02 | 0, 3, _ => d03
    | 1, 0, _ => d01.symm | 1, 1, h => absurd rfl h | 1, 2, _ => d12 | 1, 3, _ => d13
    | 2, 0, _ => d02.symm | 2, 1, _ => d12.symm | 2, 2, h => absurd rfl h | 2, 3, _ => d23
    | 3, 0, _ => d03.symm | 3, 1, _ => d13.symm | 3, 2, _ => d23.symm | 3, 3, h => absurd rfl h

end PackingOptimality.Triakis

namespace PackingOptimality

open Triakis

/-- **The triakis recursion.** `4ᵏ` triakis tetrahedra fit in a triakis tetrahedron of scale `(5/3)ᵏ`; in
particular 16 at `25/9` and 64 at `125/27`. -/
theorem triakis_recursion : ∀ k : ℕ, Nonempty (Packing Kt Kt ((5 / 3) ^ k) (4 ^ k)) :=
  fun k => ⟨ktt4.pow (by norm_num) k⟩

theorem ktt16 : Nonempty (Packing Kt Kt (25 / 9) 16) := by
  have := triakis_recursion 2; norm_num at this; exact this

theorem ktt64 : Nonempty (Packing Kt Kt (125 / 27) 64) := by
  have := triakis_recursion 3; norm_num at this; exact this

end PackingOptimality
