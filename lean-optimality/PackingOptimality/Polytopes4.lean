import PackingOptimality.BallBound
import PackingOptimality.Cubes

/-!
# Two 16-cells or 24-cells in a tesseract or a 16-cell: the two-ball bound is attained

All three results are new:
* **`c16inc8_n02`**: two 16-cells (edge 1) in a tesseract need edge `3√2/4`.
* **`c24inc8_n02`**: two 24-cells (edge 1) in a tesseract need edge `3√2/2`.
* **`c24inc16_n02`**: two 24-cells (edge 1) in a 16-cell need edge 3.

**Lower bounds.** Every piece contains its inscribed ball, so the two-ball lemma (`BallBound`) applies. The bound
is `3 × inradius` in a tesseract, and `3 × inradius / circumradius(16-cell)` in a 16-cell.

**Constructions.** For 24-cells, a translation of the piece and its point reflection. For 16-cells, the reflection
`I - ½𝟙𝟙ᵀ` and a translation, then the point reflection.
-/

namespace PackingOptimality.Polytopes4

open Set BallBound CentreGeneral
open scoped Pointwise RealInnerProductSpace

abbrev E4 := EuclideanSpace ℝ (Fin 4)

noncomputable def pt4 (a b c e : ℝ) : E4 := WithLp.toLp 2 ![a, b, c, e]
@[simp] theorem pt4_0 (a b c e : ℝ) : pt4 a b c e 0 = a := by simp [pt4]
@[simp] theorem pt4_1 (a b c e : ℝ) : pt4 a b c e 1 = b := by simp [pt4]
@[simp] theorem pt4_2 (a b c e : ℝ) : pt4 a b c e 2 = c := by simp [pt4]
@[simp] theorem pt4_3 (a b c e : ℝ) : pt4 a b c e 3 = e := by simp [pt4]

theorem s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
theorem s2pos : 0 < Real.sqrt 2 := by positivity

theorem l1_le_two_norm (y : E4) : |y 0| + |y 1| + |y 2| + |y 3| ≤ 2 * ‖y‖ := by
  have h := norm_sq_sum y
  simp only [Fin.sum_univ_four] at h
  have h2 : (|y 0| + |y 1| + |y 2| + |y 3|) ^ 2 ≤ (2 * ‖y‖) ^ 2 := by
    rw [mul_pow, h]
    nlinarith [sq_abs (y 0), sq_abs (y 1), sq_abs (y 2), sq_abs (y 3), sq_nonneg (|y 0| - |y 1|),
      sq_nonneg (|y 0| - |y 2|), sq_nonneg (|y 0| - |y 3|), sq_nonneg (|y 1| - |y 2|),
      sq_nonneg (|y 1| - |y 3|), sq_nonneg (|y 2| - |y 3|)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

theorem coord_le_norm (y : E4) (i : Fin 4) : |y i| ≤ ‖y‖ := by
  have h := norm_sq_sum y
  have : y i ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [h]; exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← sq_abs] at this
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The 16-cell of edge 1: `‖y‖₁ ≤ √2/2`. -/
noncomputable def c16 : Set E4 := l1Ball 4 (Real.sqrt 2 / 2)

/-- The 24-cell of edge 1: `‖y‖_∞ ≤ √2/2` and `‖y‖₁ ≤ √2`. -/
noncomputable def c24 : Set E4 := {y | (∀ i, |y i| ≤ Real.sqrt 2 / 2) ∧ ∑ i, |y i| ≤ Real.sqrt 2}

theorem ball_c16 (y : E4) (hy : ‖y‖ ≤ Real.sqrt 2 / 4) : y ∈ c16 := by
  show ∑ i, |y i| ≤ _
  rw [Fin.sum_univ_four]; linarith [l1_le_two_norm y]

theorem ball_c24 (y : E4) (hy : ‖y‖ ≤ Real.sqrt 2 / 2) : y ∈ c24 :=
  ⟨fun i => (coord_le_norm y i).trans hy, by rw [Fin.sum_univ_four]; linarith [l1_le_two_norm y]⟩

theorem mem_c24 {y : E4} (hy : y ∈ c24) :
    (∀ i, |y i| ≤ Real.sqrt 2 / 2) ∧ |y 0| + |y 1| + |y 2| + |y 3| ≤ Real.sqrt 2 := by
  obtain ⟨h1, h2⟩ := hy; exact ⟨h1, by rwa [Fin.sum_univ_four] at h2⟩

theorem mem_c16 {y : E4} (hy : y ∈ c16) : |y 0| + |y 1| + |y 2| + |y 3| ≤ Real.sqrt 2 / 2 := by
  have : ∑ i, |y i| ≤ _ := hy; rwa [Fin.sum_univ_four] at this

/-! ## Separating functionals -/

noncomputable def sum4 : E4 →L[ℝ] ℝ :=
  EuclideanSpace.proj 0 + EuclideanSpace.proj 1 + EuclideanSpace.proj 2 + EuclideanSpace.proj 3

theorem sum4_apply (x : E4) : sum4 x = x 0 + x 1 + x 2 + x 3 := rfl

theorem sum4_surjective : Function.Surjective sum4 :=
  fun t => ⟨EuclideanSpace.single 0 t, by simp [sum4_apply, PiLp.single_apply]⟩

theorem disjoint_of_sep (f : E4 →L[ℝ] ℝ) (hf : Function.Surjective f) (g : E4 ≃ᵃⁱ[ℝ] E4) (K : Set E4)
    (h : ∀ y ∈ K, 0 ≤ f (g y)) :
    Disjoint (interior ((g.trans (LinearIsometryEquiv.neg ℝ (E := E4)).toAffineIsometryEquiv) '' K))
      (interior (g '' K)) := by
  apply interior_disjoint_of_separated f hf (c := 0)
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    show f (-(g y)) ≤ 0
    rw [map_neg]; linarith [h y hy]
  · rintro _ ⟨y, hy, rfl⟩; exact h y hy

/-- A two-piece packing from one placement and its point reflection. -/
noncomputable def pairPacking {K C : Set E4} {s : ℝ} (g : E4 ≃ᵃⁱ[ℝ] E4) (hin : g '' K ⊆ s • C)
    (hneg : ∀ x ∈ s • C, -x ∈ s • C) (f : E4 →L[ℝ] ℝ) (hf : Function.Surjective f)
    (hsep : ∀ y ∈ K, 0 ≤ f (g y)) : Packing K C s 2 where
  g := ![g, g.trans (LinearIsometryEquiv.neg ℝ (E := E4)).toAffineIsometryEquiv]
  inside := by
    intro i; fin_cases i
    · exact hin
    · rintro _ ⟨y, hy, rfl⟩
      exact hneg _ (hin ⟨y, hy, rfl⟩)
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (disjoint_of_sep f hf g K hsep).symm
    · exact disjoint_of_sep f hf g K hsep
    · exact absurd rfl hij

theorem neg_box {s : ℝ} : ∀ x ∈ s • boxC 4, -x ∈ s • boxC 4 := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨-y, fun i => by simpa using hy i, by simp⟩

theorem neg_l1 {s ρ : ℝ} : ∀ x ∈ s • l1Ball 4 ρ, -x ∈ s • l1Ball 4 ρ := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨-y, by simpa [l1Ball] using hy, by simp⟩

/-! ## 24-cells in a tesseract: side `3√2/2` -/

noncomputable def tr24 : E4 ≃ᵃⁱ[ℝ] E4 :=
  AffineIsometryEquiv.constVAdd ℝ E4 (pt4 (Real.sqrt 2 / 4) (Real.sqrt 2 / 4) (Real.sqrt 2 / 4) (Real.sqrt 2 / 4))

theorem tr24_apply (y : E4) :
    tr24 y = pt4 (Real.sqrt 2 / 4) (Real.sqrt 2 / 4) (Real.sqrt 2 / 4) (Real.sqrt 2 / 4) + y := rfl

noncomputable def c24inc8_packing : Packing c24 (boxC 4) (3 * Real.sqrt 2 / 2) 2 := by
  refine pairPacking tr24 ?_ neg_box sum4 sum4_surjective ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_smul_box_of_coord (by positivity) fun i => ?_
    have := abs_le.mp ((mem_c24 hy).1 i)
    rw [tr24_apply, PiLp.add_apply, abs_le]
    fin_cases i <;> simp at this ⊢ <;> constructor <;> nlinarith [s2pos]
  · intro y hy
    obtain ⟨-, h⟩ := mem_c24 hy
    rw [sum4_apply, tr24_apply]; simp
    linarith [neg_abs_le (y 0), neg_abs_le (y 1), neg_abs_le (y 2), neg_abs_le (y 3)]

/-- **Two 24-cells in a tesseract: edge `3√2/2` is optimal.** -/
theorem c24inc8_n02 : Nonempty (Packing c24 (boxC 4) (3 * Real.sqrt 2 / 2) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c24 (boxC 4) s 2 → 3 * Real.sqrt 2 / 2 ≤ s := by
  refine ⟨⟨c24inc8_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_box c24 (k := Real.sqrt 2 / 2) (t := 2)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) ball_c24 hs (by linarith) g hg) le_rfl P

/-! ## 24-cells in a 16-cell: side 3 -/

noncomputable def tr24' : E4 ≃ᵃⁱ[ℝ] E4 := AffineIsometryEquiv.constVAdd ℝ E4 (pt4 (Real.sqrt 2 / 2) 0 0 0)

theorem tr24'_apply (y : E4) : tr24' y = pt4 (Real.sqrt 2 / 2) 0 0 0 + y := rfl

noncomputable def c24inc16_packing : Packing c24 c16 3 2 := by
  refine pairPacking tr24' ?_ neg_l1 (EuclideanSpace.proj 0) (proj_surjective 0) ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := mem_c24 hy
    refine mem_smul_l1_of (by norm_num) ?_
    rw [Fin.sum_univ_four, tr24'_apply]; simp
    have := abs_add_le (Real.sqrt 2 / 2) (y 0)
    rw [abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2)] at this
    linarith
  · intro y hy
    have := abs_le.mp ((mem_c24 hy).1 0)
    simp [tr24'_apply]; linarith

/-- **Two 24-cells in a 16-cell: edge 3 is optimal.** -/
theorem c24inc16_n02 : Nonempty (Packing c24 c16 3 2) ∧ ∀ s : ℝ, 0 ≤ s → Packing c24 c16 s 2 → 3 ≤ s := by
  refine ⟨⟨c24inc16_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_l1 c24 (k := Real.sqrt 2 / 2)
    (ρ := Real.sqrt 2 / 2) (t := 2) (by positivity) (by norm_num) (by norm_num) ball_c24 hs
    (by nlinarith [s2pos]) g hg) le_rfl P

/-! ## 16-cells in a tesseract: side `3√2/4` -/

/-- The reflection `I - ½ 𝟙𝟙ᵀ`. -/
noncomputable def H4l : E4 →ₗ[ℝ] E4 where
  toFun y := pt4 (y 0 - (y 0 + y 1 + y 2 + y 3) / 2) (y 1 - (y 0 + y 1 + y 2 + y 3) / 2)
    (y 2 - (y 0 + y 1 + y 2 + y 3) / 2) (y 3 - (y 0 + y 1 + y 2 + y 3) / 2)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

theorem H4l_apply (y : E4) : H4l y = pt4 (y 0 - (y 0 + y 1 + y 2 + y 3) / 2) (y 1 - (y 0 + y 1 + y 2 + y 3) / 2)
    (y 2 - (y 0 + y 1 + y 2 + y 3) / 2) (y 3 - (y 0 + y 1 + y 2 + y 3) / 2) := rfl

noncomputable def H4 : E4 ≃ₗᵢ[ℝ] E4 :=
  (LinearEquiv.ofInvolutive H4l (fun y => by ext i; fin_cases i <;> simp [H4l_apply] <;> ring)).isometryOfInner
    (fun x y => by
      show ⟪H4l x, H4l y⟫ = ⟪x, y⟫
      simp only [inner_sum, Fin.sum_univ_four, H4l_apply, pt4_0, pt4_1, pt4_2, pt4_3]
      ring)

noncomputable def g16 : E4 ≃ᵃⁱ[ℝ] E4 :=
  H4.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ E4 (pt4 (Real.sqrt 2 / 8) (Real.sqrt 2 / 8) (Real.sqrt 2 / 8) (Real.sqrt 2 / 8)))

theorem g16_apply (y : E4) :
    g16 y = pt4 (Real.sqrt 2 / 8) (Real.sqrt 2 / 8) (Real.sqrt 2 / 8) (Real.sqrt 2 / 8) + H4l y := rfl

noncomputable def c16inc8_packing : Packing c16 (boxC 4) (3 * Real.sqrt 2 / 4) 2 := by
  refine pairPacking g16 ?_ neg_box sum4 sum4_surjective ?_
  · rintro _ ⟨y, hy, rfl⟩
    have h := mem_c16 hy
    refine mem_smul_box_of_coord (by positivity) fun i => ?_
    rw [g16_apply, PiLp.add_apply, H4l_apply, abs_le]
    fin_cases i <;> simp <;> constructor <;>
      linarith [neg_abs_le (y 0), le_abs_self (y 0), neg_abs_le (y 1), le_abs_self (y 1),
        neg_abs_le (y 2), le_abs_self (y 2), neg_abs_le (y 3), le_abs_self (y 3)]
  · intro y hy
    have h := mem_c16 hy
    rw [sum4_apply, g16_apply]; simp [H4l_apply]
    linarith [le_abs_self (y 0), le_abs_self (y 1), le_abs_self (y 2), le_abs_self (y 3)]

/-- **Two 16-cells in a tesseract: edge `3√2/4` is optimal.** -/
theorem c16inc8_n02 : Nonempty (Packing c16 (boxC 4) (3 * Real.sqrt 2 / 4) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c16 (boxC 4) s 2 → 3 * Real.sqrt 2 / 4 ≤ s := by
  refine ⟨⟨c16inc8_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_box c16 (k := Real.sqrt 2 / 4) (t := 2)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) ball_c16 hs (by linarith) g hg) le_rfl P

end PackingOptimality.Polytopes4
