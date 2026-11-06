import PackingOptimality.Polytopes4

/-!
# Two 120-cells in a tesseract or a 16-cell: the two-ball bound is attained

Both results are new:
* **`c120inc8_n02`**: two 120-cells (edge 1) in a tesseract need edge `(21 + 9√5)/4`.
* **`c120inc16_n02`**: two 120-cells (edge 1) in a 16-cell need edge `3√2 (7 + 3√5)/4`.

**The piece.** The regular 120-cell of edge 1 is the polar of the 600-cell: the intersection of the 120 half-spaces
`⟪n, y⟫ ≤ k` over the vertices `n` of the unit 600-cell (the 8 points `±eᵢ`, the 16 points `(±½, ±½, ±½, ±½)` and
the 96 even permutations of `(±φ, ±1, ±1/φ, 0)/2`), with inradius `k = φ⁴/2 = (7 + 3√5)/4`.
(`scripts/optimality/check_polar_hreps.py` checks numerically that every one of these facets meets 20 vertices of
the 120-cell, and that the edge is 1.)

**Lower bounds.** All the normals are unit vectors, so the piece contains the ball of radius `k` and the
two-ball lemma (`BallBound`) gives `3k` in a tesseract and `3k/ρ = 3√2 k` in the 16-cell `‖y‖₁ ≤ √2/2`.

**Constructions.** Only nine of the facets are needed. The facets `±eᵢ` give `|yᵢ| ≤ k`, so the translate by
`(k/2)𝟙` lies in the tesseract of side `3k`, and the facet with normal `-𝟙/2` puts it on the side `Σ xᵢ ≥ 0`.
The sixteen facets `(±½)⁴` give `‖y‖₁ ≤ 2k`, so the translate by `k e₀` has `‖x‖₁ ≤ 3k`, and the facet `-e₀`
puts it on the side `x₀ ≥ 0`. In each case the point reflection is the second piece.
-/

namespace PackingOptimality.Cells120

open Set BallBound CentreGeneral Polytopes4
open scoped Pointwise RealInnerProductSpace

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem s5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
theorem s5pos : 0 < Real.sqrt 5 := by positivity
theorem φ_pos : 0 < φ := by unfold φ; positivity
theorem φ_sq : φ ^ 2 = φ + 1 := by unfold φ; nlinarith [s5]

/-- The inradius of the 120-cell of edge 1, `φ⁴/2`. -/
noncomputable def k120 : ℝ := (7 + 3 * Real.sqrt 5) / 4

theorem k120_eq : k120 = φ ^ 4 / 2 := by
  have h : φ ^ 4 = (φ + 1) ^ 2 := by rw [← φ_sq]; ring
  rw [h]; unfold k120 φ; nlinarith [s5]

theorem k120_pos : 0 < k120 := by unfold k120; positivity

/-- The 120 vertices of the 600-cell of circumradius 1. -/
noncomputable def N600 : Set E4 :=
  {n | ∃ i : Fin 4, n = EuclideanSpace.single i 1 ∨ n = EuclideanSpace.single i (-1)} ∪
  {n | ∀ i, n i = 1 / 2 ∨ n i = -1 / 2} ∪
  {n | ∃ π ∈ alternatingGroup (Fin 4), ∃ a b c : ℝ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      ∀ i, n i = ![a * φ / 2, b / 2, c / (2 * φ), 0] (π i)}

/-- The regular 120-cell of edge 1, as the polar of the 600-cell. -/
noncomputable def c120 : Set E4 := {y | ∀ n ∈ N600, ⟪n, y⟫ ≤ k120}

theorem sq_one {a : ℝ} (h : a = 1 ∨ a = -1) : a ^ 2 = 1 := by rcases h with rfl | rfl <;> norm_num

theorem N600_norm : ∀ n ∈ N600, ‖n‖ ≤ 1 := by
  rintro n ((⟨i, rfl | rfl⟩ | hn) | ⟨π, -, a, b, c, ha, hb, hc, hn⟩)
  · simp
  · simp
  · have h2 : ‖n‖ ^ 2 = 1 := by
      rw [norm_sq_sum, Fin.sum_univ_four]
      rcases hn 0 with h0 | h0 <;> rcases hn 1 with h1 | h1 <;> rcases hn 2 with h2 | h2 <;>
        rcases hn 3 with h3 | h3 <;> rw [h0, h1, h2, h3] <;> norm_num
    nlinarith [norm_nonneg n]
  · have h2 : ‖n‖ ^ 2 = 1 := by
      rw [norm_sq_sum]
      simp_rw [hn]
      rw [Equiv.sum_comp π (fun j => (![a * φ / 2, b / 2, c / (2 * φ), 0] j) ^ 2), Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
      have hφ := φ_pos
      have ha2 := sq_one ha; have hb2 := sq_one hb; have hc2 := sq_one hc
      field_simp
      have e1 : a ^ 2 * φ ^ 2 = φ ^ 2 := by rw [ha2, one_mul]
      have e3 : φ ^ 4 = (φ + 1) ^ 2 := by rw [← φ_sq]; ring
      nlinarith [φ_sq]
    nlinarith [norm_nonneg n]

theorem ball_c120 (y : E4) (hy : ‖y‖ ≤ k120) : y ∈ c120 := fun n hn =>
  (real_inner_le_norm n y).trans (by nlinarith [N600_norm n hn, norm_nonneg n, norm_nonneg y, k120_pos])

/-! ## The nine facets used by the constructions -/

theorem coord_le {y : E4} (hy : y ∈ c120) (i : Fin 4) : |y i| ≤ k120 := by
  have h1 := hy _ (Or.inl (Or.inl ⟨i, Or.inl rfl⟩))
  have h2 := hy _ (Or.inl (Or.inl ⟨i, Or.inr rfl⟩))
  rw [EuclideanSpace.inner_single_left] at h1 h2
  simp at h1 h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- The vertex `(±½, ±½, ±½, ±½)` with the signs of `y`. -/
noncomputable def sgnV (y : E4) : E4 := WithLp.toLp 2 fun i => if 0 ≤ y i then 1 / 2 else -1 / 2

theorem sgnV_mem (y : E4) : sgnV y ∈ N600 := Or.inl (Or.inr fun i => by
  show (if 0 ≤ y i then (1 / 2 : ℝ) else -1 / 2) = 1 / 2 ∨ (if 0 ≤ y i then (1 / 2 : ℝ) else -1 / 2) = -1 / 2
  split_ifs <;> norm_num)

theorem l1_le {y : E4} (hy : y ∈ c120) : |y 0| + |y 1| + |y 2| + |y 3| ≤ 2 * k120 := by
  have h := hy _ (sgnV_mem y)
  rw [inner_sum, Fin.sum_univ_four] at h
  have e : ∀ i, (sgnV y) i * y i = |y i| / 2 := fun i => by
    show (if 0 ≤ y i then (1 / 2 : ℝ) else -1 / 2) * y i = _
    split_ifs with hi
    · rw [abs_of_nonneg hi]; ring
    · rw [abs_of_neg (not_le.mp hi)]; ring
  rw [e, e, e, e] at h; linarith

/-- The vertex `-𝟙/2`. -/
noncomputable def negHalf : E4 := WithLp.toLp 2 fun _ => -1 / 2

theorem sum_ge {y : E4} (hy : y ∈ c120) : -(2 * k120) ≤ y 0 + y 1 + y 2 + y 3 := by
  have h := hy negHalf (Or.inl (Or.inr fun i => Or.inr rfl))
  rw [inner_sum, Fin.sum_univ_four] at h
  simp only [negHalf] at h
  linarith

/-! ## 120-cells in a tesseract: side `3k = (21 + 9√5)/4` -/

noncomputable def tr8 : E4 ≃ᵃⁱ[ℝ] E4 :=
  AffineIsometryEquiv.constVAdd ℝ E4 (pt4 (k120 / 2) (k120 / 2) (k120 / 2) (k120 / 2))

theorem tr8_apply (y : E4) : tr8 y = pt4 (k120 / 2) (k120 / 2) (k120 / 2) (k120 / 2) + y := rfl

theorem val8 : (21 + 9 * Real.sqrt 5) / 4 = 3 * k120 := by unfold k120; ring

noncomputable def c120inc8_packing : Packing c120 (boxC 4) ((21 + 9 * Real.sqrt 5) / 4) 2 := by
  rw [val8]
  refine pairPacking tr8 ?_ neg_box sum4 sum4_surjective ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_smul_box_of_coord (by linarith [k120_pos]) fun i => ?_
    have h0 := abs_le.mp (coord_le hy 0); have h1 := abs_le.mp (coord_le hy 1)
    have h2 := abs_le.mp (coord_le hy 2); have h3 := abs_le.mp (coord_le hy 3)
    rw [tr8_apply, PiLp.add_apply, abs_le]
    fin_cases i <;> simp <;> constructor <;> linarith
  · intro y hy
    have := sum_ge hy
    rw [sum4_apply, tr8_apply]; simp
    linarith

/-- **Two 120-cells in a tesseract: edge `(21 + 9√5)/4` is optimal.** -/
theorem c120inc8_n02 : Nonempty (Packing c120 (boxC 4) ((21 + 9 * Real.sqrt 5) / 4) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c120 (boxC 4) s 2 → (21 + 9 * Real.sqrt 5) / 4 ≤ s := by
  refine ⟨⟨c120inc8_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  rw [val8] at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_box c120 (k := k120) (t := 2)
    k120_pos (by norm_num) (by norm_num) (by norm_num) ball_c120 hs (by linarith) g hg) le_rfl P

/-! ## 120-cells in a 16-cell: side `3√2 k` -/

noncomputable def tr16 : E4 ≃ᵃⁱ[ℝ] E4 := AffineIsometryEquiv.constVAdd ℝ E4 (pt4 k120 0 0 0)

theorem tr16_apply (y : E4) : tr16 y = pt4 k120 0 0 0 + y := rfl

theorem val16 : 3 * Real.sqrt 2 * (7 + 3 * Real.sqrt 5) / 4 = 3 * Real.sqrt 2 * k120 := by unfold k120; ring

noncomputable def c120inc16_packing : Packing c120 c16 (3 * Real.sqrt 2 * (7 + 3 * Real.sqrt 5) / 4) 2 := by
  rw [val16]
  refine pairPacking tr16 ?_ neg_l1 (EuclideanSpace.proj 0) (proj_surjective 0) ?_
  · rintro _ ⟨y, hy, rfl⟩
    have h := l1_le hy
    refine mem_smul_l1_of (by have := k120_pos; positivity) ?_
    rw [Fin.sum_univ_four, tr16_apply]; simp
    have e : 3 * Real.sqrt 2 * k120 * (Real.sqrt 2 / 2) = 3 * k120 := by
      have := s2; linear_combination (3 * k120 / 2) * this
    rw [e]
    have := abs_add_le k120 (y 0)
    rw [abs_of_pos k120_pos] at this
    linarith
  · intro y hy
    have := abs_le.mp (coord_le hy 0)
    simp [tr16_apply]; linarith

/-- **Two 120-cells in a 16-cell: edge `3√2 (7 + 3√5)/4` is optimal.** -/
theorem c120inc16_n02 : Nonempty (Packing c120 c16 (3 * Real.sqrt 2 * (7 + 3 * Real.sqrt 5) / 4) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c120 c16 s 2 → 3 * Real.sqrt 2 * (7 + 3 * Real.sqrt 5) / 4 ≤ s := by
  refine ⟨⟨c120inc16_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  rw [val16] at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_l1 c120 (k := k120)
    (ρ := Real.sqrt 2 / 2) (t := 2) k120_pos (by norm_num) (by norm_num) ball_c120 hs
    (by nlinarith [s2pos, s2, k120_pos]) g hg) le_rfl P

end PackingOptimality.Cells120
