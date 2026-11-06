import PackingOptimality.Polytopes4
import PackingOptimality.FacetWidth

/-!
# Two 5-cells in a 24-cell: edge `√10/4` is optimal

**Theorem (`c5inc24_n02`).** Two regular 5-cells (4-simplices) of edge 1 fit in a 24-cell of edge `√10/4`, and in
no smaller one.

**Lower bound.** The facet-width lemma. The 5-cell of edge 1 has height `√(5/8)`, and the 24-cell
`{‖y‖_∞ ≤ √2/2, ‖y‖₁ ≤ √2}` of edge 1 lies in the unit ball (`‖y‖² ≤ ‖y‖_∞ ‖y‖₁ ≤ 1`).

**Construction.** The apex is the vertex `(√5/4)(1, 1, 0, 0)` of the scaled 24-cell, and the base tetrahedron lies
in the hyperplane `y₀ + y₁ = 0` through the centre. One base vertex is `(√3/4)(1, -1, 0, 0)`. The other three sit
over the circle of radius `√3/3` in the `(y₂, y₃)`-plane at angles `15°`, `135°` and `255°`. Rotating them `15°`
away from the axes is what makes them fit: the largest coordinate is `(3√2 + √6)/12 ≈ 0.5577`, against the bound
`√5/4 ≈ 0.5590`. The point reflection is the second 5-cell, on the other side of `y₀ + y₁ = 0`.

The piece is written through its barycentric coordinates: `λ₀ = (2√5/5)(y₀ + y₁)` for the apex and
`λⱼ = 1/4 + ⟨2 qⱼ - (√5/10)(1, 1, 0, 0), y⟩` for the base vertices `qⱼ`.
-/

namespace PackingOptimality.C5inC24

open Set BallBound CentreGeneral FacetWidth Polytopes4
open scoped Pointwise RealInnerProductSpace

theorem r2_2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem r3_2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem r5_2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- Normalise polynomials in `√2`, `√3` and `√5`. -/
macro "rad4" : tactic => `(tactic| (
  try ring_nf
  repeat (simp only [r2_2, r3_2, r5_2]; try ring_nf)))

/-- `√6 = √2 √3` is written as a product throughout. -/
noncomputable def vv : Fin 5 → E4 := ![
  pt4 (Real.sqrt 5 / 4) (Real.sqrt 5 / 4) 0 0,
  pt4 (Real.sqrt 3 / 4) (-(Real.sqrt 3 / 4)) 0 0,
  pt4 (-(Real.sqrt 3 / 12)) (Real.sqrt 3 / 12) ((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12)
    ((3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 12),
  pt4 (-(Real.sqrt 3 / 12)) (Real.sqrt 3 / 12) (-(Real.sqrt 2 * Real.sqrt 3 / 6)) (Real.sqrt 2 * Real.sqrt 3 / 6),
  pt4 (-(Real.sqrt 3 / 12)) (Real.sqrt 3 / 12) (-((3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 12))
    (-((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12))]

noncomputable def aa : Fin 5 → E4 := ![
  pt4 (2 * Real.sqrt 5 / 5) (2 * Real.sqrt 5 / 5) 0 0,
  pt4 (Real.sqrt 3 / 2 - Real.sqrt 5 / 10) (-(Real.sqrt 3 / 2) - Real.sqrt 5 / 10) 0 0,
  pt4 (-(Real.sqrt 3 / 6) - Real.sqrt 5 / 10) (Real.sqrt 3 / 6 - Real.sqrt 5 / 10)
    ((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 6) ((3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 6),
  pt4 (-(Real.sqrt 3 / 6) - Real.sqrt 5 / 10) (Real.sqrt 3 / 6 - Real.sqrt 5 / 10)
    (-(Real.sqrt 2 * Real.sqrt 3 / 3)) (Real.sqrt 2 * Real.sqrt 3 / 3),
  pt4 (-(Real.sqrt 3 / 6) - Real.sqrt 5 / 10) (Real.sqrt 3 / 6 - Real.sqrt 5 / 10)
    (-((3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 6)) (-((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 6))]

noncomputable def cc : Fin 5 → ℝ := ![0, 1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- The regular 5-cell of edge 1, placed with its apex at a vertex of the 24-cell of edge `√10/4`. -/
noncomputable def c5 : Set E4 := {y | ∀ j, 0 ≤ cc j + ⟪aa j, y⟫}

theorem inner4 (u y : E4) : ⟪u, y⟫ = u 0 * y 0 + u 1 * y 1 + u 2 * y 2 + u 3 * y 3 := by
  rw [CentreGeneral.inner_sum, Fin.sum_univ_four]

theorem v_mem (j : Fin 5) : vv j ∈ c5 := by
  intro k
  rw [inner4]
  fin_cases j <;> fin_cases k <;> simp [vv, aa, cc] <;> rad4 <;> norm_num

theorem v_one (j : Fin 5) : 1 ≤ cc j + ⟪aa j, vv j⟫ := by
  rw [inner4]
  fin_cases j <;> simp [vv, aa, cc] <;> rad4 <;> norm_num

theorem norm_a (j : Fin 5) : ‖aa j‖ ^ 2 * (5 / 8) ≤ 1 := by
  rw [← real_inner_self_eq_norm_sq, inner4]
  fin_cases j <;> simp [aa] <;> rad4 <;> norm_num

theorem c24_norm (x : E4) (hx : x ∈ c24) : ‖x‖ ^ 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := mem_c24 hx
  rw [norm_sq_sum, Fin.sum_univ_four]
  have e : ∀ i, x i ^ 2 ≤ |x i| * (Real.sqrt 2 / 2) := fun i => by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left (h1 i) (abs_nonneg _)
  have : (|x 0| + |x 1| + |x 2| + |x 3|) * (Real.sqrt 2 / 2) ≤ Real.sqrt 2 * (Real.sqrt 2 / 2) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have hs := r2_2
  nlinarith [e 0, e 1, e 2, e 3]

/-- The optimal edge, written as `√2 √5/4 = √10/4`. -/
noncomputable def sC : ℝ := Real.sqrt 2 * Real.sqrt 5 / 4

theorem sC_eq : sC = Real.sqrt 10 / 4 := by
  unfold sC; rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

theorem sC_pos : 0 < sC := by unfold sC; positivity

/-- **Centre lemma.** -/
theorem centre_c5 (s : ℝ) (hs0 : 0 ≤ s) (hs : s < sC) (g : E4 ≃ᵃⁱ[ℝ] E4) (hg : g '' c5 ⊆ s • c24) :
    (0 : E4) ∈ interior (g '' c5) := by
  refine centre_of_facet_width cc aa vv rfl v_mem v_one norm_a c24_norm hs0 ?_ g hg
  have h1 : s ^ 2 < sC ^ 2 := by nlinarith [sC_pos]
  have h2 : sC ^ 2 = 5 / 8 := by unfold sC; rad4
  nlinarith

/-! ## The piece lies in the 24-cell -/

theorem bary (y : E4) : ∑ j, (cc j + ⟪aa j, y⟫) • vv j = y := by
  ext k
  simp only [inner4, Fin.sum_univ_five, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [vv, aa, cc] <;> rad4

theorem bary_sum (y : E4) : ∑ j, (cc j + ⟪aa j, y⟫) = 1 := by
  simp only [inner4, Fin.sum_univ_five]
  simp [aa, cc]; rad4

theorem c5_sub {S : Set E4} (hS : Convex ℝ S) (hv : ∀ j, vv j ∈ S) : c5 ⊆ S := by
  intro y hy
  rw [← bary y]
  exact hS.sum_mem (fun j _ => hy j) (bary_sum y) (fun j _ => hv j)

theorem convex_c24 : Convex ℝ c24 := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  have e : ∀ i, |(p • x + q • y) i| ≤ p * |x i| + q * |y i| := fun i => by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |p * x i + q * y i| ≤ |p * x i| + |q * y i| := abs_add_le _ _
      _ = p * |x i| + q * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
  refine ⟨fun i => ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (hx1 i) hp
    have := mul_le_mul_of_nonneg_left (hy1 i) hq
    have h := e i
    have : p * (Real.sqrt 2 / 2) + q * (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by rw [← add_mul, hpq, one_mul]
    linarith
  · have hs : ∑ i, |(p • x + q • y) i| ≤ ∑ i, (p * |x i| + q * |y i|) := Finset.sum_le_sum fun i _ => e i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have := mul_le_mul_of_nonneg_left hx2 hp
    have := mul_le_mul_of_nonneg_left hy2 hq
    have : p * Real.sqrt 2 + q * Real.sqrt 2 = Real.sqrt 2 := by rw [← add_mul, hpq, one_mul]
    linarith

theorem mem_smul_c24 {s : ℝ} (hs : 0 < s) {x : E4} (h1 : ∀ i, |x i| ≤ s * (Real.sqrt 2 / 2))
    (h2 : |x 0| + |x 1| + |x 2| + |x 3| ≤ s * Real.sqrt 2) : x ∈ s • c24 := by
  refine ⟨s⁻¹ • x, ⟨fun i => ?_, ?_⟩, by simp [smul_smul, hs.ne']⟩
  · rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    calc s⁻¹ * |x i| ≤ s⁻¹ * (s * (Real.sqrt 2 / 2)) := mul_le_mul_of_nonneg_left (h1 i) (by positivity)
      _ = Real.sqrt 2 / 2 := by field_simp
  · simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hs), ← Finset.mul_sum,
      Fin.sum_univ_four]
    calc s⁻¹ * (|x 0| + |x 1| + |x 2| + |x 3|) ≤ s⁻¹ * (s * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.sqrt 2 := by field_simp

theorem neg_c24 {s : ℝ} : ∀ x ∈ s • c24, -x ∈ s • c24 := by
  rintro _ ⟨y, ⟨h1, h2⟩, rfl⟩
  exact ⟨-y, ⟨fun i => by simpa using h1 i, by simpa using h2⟩, by simp⟩

/-! ## The five vertices -/

theorem e1 : sC * (Real.sqrt 2 / 2) = Real.sqrt 5 / 4 := by unfold sC; rad4
theorem e2 : sC * Real.sqrt 2 = Real.sqrt 5 / 2 := by unfold sC; rad4

theorem bnd : 1.73 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.7321 ∧ 1.414 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4143 ∧
    2.236 ≤ Real.sqrt 5 := by
  have h2 := r2_2; have h3 := r3_2; have h5 := r5_2
  have p2 := Real.sqrt_nonneg 2; have p3 := Real.sqrt_nonneg 3; have p5 := Real.sqrt_nonneg 5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The tight coordinate: `(3√2 + √6)/12 ≤ √5/4`. -/
theorem tight : (3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12 ≤ Real.sqrt 5 / 4 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := bnd
  have h : ((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12) ^ 2 ≤ (Real.sqrt 5 / 4) ^ 2 := by
    have e : ((3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12) ^ 2 = (24 + 12 * Real.sqrt 3) / 144 := by rad4
    rw [e, div_pow, r5_2]; nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h

theorem v_in (j : Fin 5) : vv j ∈ sC • c24 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := bnd
  have t := tight
  have p6 : 0 ≤ Real.sqrt 2 * Real.sqrt 3 := by positivity
  have m6 : Real.sqrt 2 * Real.sqrt 3 ≤ 3 * Real.sqrt 2 := by nlinarith
  refine mem_smul_c24 sC_pos (fun i => ?_) ?_
  · rw [e1, abs_le]
    fin_cases j <;> fin_cases i <;> simp [vv] <;> (try constructor) <;> nlinarith
  · rw [e2]
    fin_cases j <;> simp [vv]
    · rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 5 / 4)]; linarith
    · rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 3 / 4)]; linarith
    · rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 3 / 12), abs_of_pos (by positivity :
        (0 : ℝ) < (3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12), abs_of_nonneg (by linarith :
        (0 : ℝ) ≤ (3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 12)]
      nlinarith
    · rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 3 / 12), abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt 3 / 6)]
      nlinarith
    · rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 3 / 12), abs_of_pos (by positivity :
        (0 : ℝ) < (3 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 3) / 12), abs_of_nonneg (by linarith :
        (0 : ℝ) ≤ (3 * Real.sqrt 2 - Real.sqrt 2 * Real.sqrt 3) / 12)]
      nlinarith

theorem inside : (AffineIsometryEquiv.refl ℝ E4) '' c5 ⊆ sC • c24 := by
  rw [AffineIsometryEquiv.coe_refl, Set.image_id]
  exact c5_sub (convex_c24.smul _) v_in

/-! ## Separation by `y₀ + y₁ = 0` -/

noncomputable def f01 : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0 + EuclideanSpace.proj 1

theorem f01_surjective : Function.Surjective f01 :=
  fun t => ⟨EuclideanSpace.single 0 t, by simp [f01]⟩

theorem sep (y : E4) (hy : y ∈ c5) : 0 ≤ f01 ((AffineIsometryEquiv.refl ℝ E4) y) := by
  have h := hy 0
  rw [inner4] at h
  simp [aa, cc] at h
  show 0 ≤ y 0 + y 1
  have : 0 < Real.sqrt 5 := by positivity
  nlinarith

noncomputable def c5Packing : Packing c5 c24 sC 2 :=
  pairPacking (AffineIsometryEquiv.refl ℝ E4) inside neg_c24 f01 f01_surjective sep

end PackingOptimality.C5inC24

namespace PackingOptimality

open C5inC24 Polytopes4

/-- **Two 5-cells in a 24-cell: edge `√10/4` is optimal.** -/
theorem c5inc24_n02 : Nonempty (Packing c5 c24 (Real.sqrt 10 / 4) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c5 c24 s 2 → Real.sqrt 10 / 4 ≤ s := by
  rw [← sC_eq]
  refine ⟨⟨c5Packing⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_c5 s hs h g hg) le_rfl P

end PackingOptimality
