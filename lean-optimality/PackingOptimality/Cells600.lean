import PackingOptimality.Cells120

/-!
# Two 600-cells in a tesseract or a 16-cell: the two-ball bound is attained

Both results are new:
* **`c600inc8_n02`**: two 600-cells (edge 1) in a tesseract need edge `3√2 (2 + √5)/4 = (6√2 + 3√10)/4`.
* **`c600inc16_n02`**: two 600-cells (edge 1) in a 16-cell need edge `3 (2 + √5)/2 = (6 + 3√5)/2`.

**The piece.** The regular 600-cell of edge 1 is the polar of the 120-cell: the intersection of the 600
half-spaces `⟪v, y⟫ ≤ 2 + √5 = φ³` over the vertices `v` of the standard 120-cell of circumradius `2√2` (all
permutations of `(0, 0, ±2, ±2)`, `(±1, ±1, ±1, ±√5)`, `(±φ⁻², ±φ, ±φ, ±φ)`, `(±φ⁻¹, ±φ⁻¹, ±φ⁻¹, ±φ²)`, and the
even permutations of `(0, ±φ⁻², ±1, ±φ²)`, `(0, ±φ⁻¹, ±φ, ±√5)`, `(±φ⁻¹, ±1, ±φ, ±2)`). Its inradius is
`k = φ³/(2√2) = √2 (2 + √5)/4`. (`scripts/optimality/check_polar_hreps.py` checks numerically that each of these
facets meets 4 vertices of the 600-cell, and that the edge is 1.)

**Lower bounds.** Every normal has length `2√2`, so the piece contains the ball of radius `k`, and the two-ball
lemma (`BallBound`) gives `3k` in a tesseract and `3√2 k` in the 16-cell `‖y‖₁ ≤ √2/2`.

**Constructions.** The rotation `M = (1/√2) [[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 1], [0, 0, 1, -1]]` turns the
24 facets with normals `(0, 0, ±2, ±2)` (and permutations) into facets with normals `±eᵢ` and `(±½)⁴`. The
rotated piece has `|xᵢ| ≤ k` and `‖x‖₁ ≤ 2k`, exactly as the 120-cell had, and the same translations
(`(k/2)𝟙` in the tesseract, `k e₀` in the 16-cell) and point reflections finish the packings.
-/

namespace PackingOptimality.Cells600

open Set BallBound CentreGeneral Polytopes4 Cells120
open scoped Pointwise RealInnerProductSpace

/-- Sign vectors. -/
def IsSign (e : Fin 4 → ℝ) : Prop := ∀ i, e i = 1 ∨ e i = -1

/-- The signed permutations of `w` by the permutations in `P`. -/
def fam (w : Fin 4 → ℝ) (P : Set (Equiv.Perm (Fin 4))) : Set E4 :=
  {n | ∃ π ∈ P, ∃ e, IsSign e ∧ ∀ i, n i = e i * w (π i)}

theorem fam_norm_sq {w : Fin 4 → ℝ} {P : Set (Equiv.Perm (Fin 4))} {n : E4} (h : n ∈ fam w P) :
    ‖n‖ ^ 2 = ∑ j, w j ^ 2 := by
  obtain ⟨π, -, e, he, hn⟩ := h
  rw [norm_sq_sum]
  calc ∑ i, n i ^ 2 = ∑ i, w (π i) ^ 2 := Finset.sum_congr rfl fun i _ => by
        rw [hn, mul_pow, sq_one (he i), one_mul]
    _ = ∑ j, w j ^ 2 := Equiv.sum_comp π (fun j => w j ^ 2)

/-- The 24 points with two coordinates `±2` and two coordinates `0`. -/
def twos : Set E4 :=
  {n | ∃ a b : Fin 4, a ≠ b ∧ ∃ σ τ : ℝ, (σ = 1 ∨ σ = -1) ∧ (τ = 1 ∨ τ = -1) ∧
    n = EuclideanSpace.single a (2 * σ) + EuclideanSpace.single b (2 * τ)}

/-- Even permutations. -/
def A4 : Set (Equiv.Perm (Fin 4)) := (alternatingGroup (Fin 4) : Set (Equiv.Perm (Fin 4)))

/-- The 600 vertices of the standard 120-cell, of circumradius `2√2`. Here `φ⁻¹ = φ - 1`, `φ⁻² = 2 - φ` and
`φ² = φ + 1`. -/
noncomputable def V120 : Set E4 :=
  twos ∪ fam ![1, 1, 1, Real.sqrt 5] univ ∪ fam ![2 - φ, φ, φ, φ] univ ∪
    fam ![φ - 1, φ - 1, φ - 1, φ + 1] univ ∪ fam ![0, 2 - φ, 1, φ + 1] A4 ∪
    fam ![0, φ - 1, φ, Real.sqrt 5] A4 ∪ fam ![φ - 1, 1, φ, 2] A4

/-- The regular 600-cell of edge 1, as the polar of the 120-cell. -/
noncomputable def c600 : Set E4 := {y | ∀ v ∈ V120, ⟪v, y⟫ ≤ 2 + Real.sqrt 5}

theorem twos_inner (a b : Fin 4) (x z : ℝ) (y : E4) :
    ⟪EuclideanSpace.single a x + EuclideanSpace.single b z, y⟫ = x * y a + z * y b := by
  rw [inner_add_left, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]; simp

theorem twos_norm {n : E4} (h : n ∈ twos) : ‖n‖ ^ 2 = 8 := by
  obtain ⟨a, b, hab, σ, τ, hσ, hτ, rfl⟩ := h
  rw [norm_add_sq_real, EuclideanSpace.inner_single_left]
  have h1 : ‖EuclideanSpace.single a (2 * σ)‖ ^ 2 = 4 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, mul_pow, sq_one hσ]; norm_num
  have h2 : ‖EuclideanSpace.single b (2 * τ)‖ ^ 2 = 4 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, mul_pow, sq_one hτ]; norm_num
  rw [h1, h2]
  simp [hab]
  norm_num

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem V120_norm : ∀ v ∈ V120, ‖v‖ ^ 2 = 8 := by
  rintro v ((((((hv | hv) | hv) | hv) | hv) | hv) | hv)
  · exact twos_norm hv
  all_goals rw [fam_norm_sq hv, Fin.sum_univ_four]; simp
  · norm_num
  · linear_combination 4 * φ_sq
  · linear_combination 4 * φ_sq
  · linear_combination 2 * φ_sq
  · linear_combination 2 * φ_sq
  · linear_combination 2 * φ_sq

/-- The inradius of the 600-cell of edge 1. -/
noncomputable def k600 : ℝ := Real.sqrt 2 * (2 + Real.sqrt 5) / 4

theorem k600_pos : 0 < k600 := by unfold k600; positivity

theorem V120_norm' (v : E4) (hv : v ∈ V120) : ‖v‖ = 2 * Real.sqrt 2 := by
  have h := V120_norm v hv
  have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  exact (pow_left_inj₀ (norm_nonneg v) (by positivity) two_ne_zero).mp (h.trans h8.symm)

theorem ball_c600 (y : E4) (hy : ‖y‖ ≤ k600) : y ∈ c600 := fun v hv => by
  have h := real_inner_le_norm v y
  rw [V120_norm' v hv] at h
  have e : 2 * Real.sqrt 2 * k600 = 2 + Real.sqrt 5 := by
    unfold k600; have := s2; linear_combination (2 + Real.sqrt 5) / 2 * this
  nlinarith [s2pos]

/-! ## The facets `(0, 0, ±2, ±2)` -/

theorem two_le {y : E4} (hy : y ∈ c600) {a b : Fin 4} (hab : a ≠ b) {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hτ : τ = 1 ∨ τ = -1) : σ * y a + τ * y b ≤ (2 + Real.sqrt 5) / 2 := by
  have := hy _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, b, hab, σ, τ, hσ, hτ, rfl⟩))))))
  rw [twos_inner] at this; linarith

/-! ## The rotation `M` -/

noncomputable def cs : ℝ := Real.sqrt 2 / 2

theorem cs_sq : cs ^ 2 = 1 / 2 := by unfold cs; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem cs_pos : 0 < cs := by unfold cs; positivity

theorem cs_k : cs * ((2 + Real.sqrt 5) / 2) = k600 := by unfold cs k600; ring

noncomputable def Ml : E4 →ₗ[ℝ] E4 where
  toFun y := pt4 (cs * (y 0 + y 1)) (cs * (y 0 - y 1)) (cs * (y 2 + y 3)) (cs * (y 2 - y 3))
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r y := by ext i; fin_cases i <;> simp <;> ring

theorem Ml_apply (y : E4) :
    Ml y = pt4 (cs * (y 0 + y 1)) (cs * (y 0 - y 1)) (cs * (y 2 + y 3)) (cs * (y 2 - y 3)) := rfl

noncomputable def M : E4 ≃ₗᵢ[ℝ] E4 :=
  (LinearEquiv.ofInvolutive Ml (fun y => by
      ext i; fin_cases i <;> simp [Ml_apply]
      · linear_combination (2 * y 0) * cs_sq
      · linear_combination (2 * y 1) * cs_sq
      · linear_combination (2 * y 2) * cs_sq
      · linear_combination (2 * y 3) * cs_sq)).isometryOfInner
    (fun x y => by
      show ⟪Ml x, Ml y⟫ = ⟪x, y⟫
      simp only [CentreGeneral.inner_sum, Fin.sum_univ_four, Ml_apply, pt4_0, pt4_1, pt4_2, pt4_3]
      linear_combination (2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3)) * cs_sq)

theorem cs_abs {u : ℝ} (h1 : u ≤ (2 + Real.sqrt 5) / 2) (h2 : -u ≤ (2 + Real.sqrt 5) / 2) :
    |cs * u| ≤ k600 := by
  rw [← cs_k, abs_mul, abs_of_pos cs_pos]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, h1⟩) cs_pos.le

theorem Ml_bound {y : E4} (hy : y ∈ c600) (i : Fin 4) : |Ml y i| ≤ k600 := by
  have o : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have n : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  fin_cases i
  · show |cs * (y 0 + y 1)| ≤ k600
    have := two_le hy (a := 0) (b := 1) (by decide) o o
    have := two_le hy (a := 0) (b := 1) (by decide) n n
    exact cs_abs (by linarith) (by linarith)
  · show |cs * (y 0 - y 1)| ≤ k600
    have := two_le hy (a := 0) (b := 1) (by decide) o n
    have := two_le hy (a := 0) (b := 1) (by decide) n o
    exact cs_abs (by linarith) (by linarith)
  · show |cs * (y 2 + y 3)| ≤ k600
    have := two_le hy (a := 2) (b := 3) (by decide) o o
    have := two_le hy (a := 2) (b := 3) (by decide) n n
    exact cs_abs (by linarith) (by linarith)
  · show |cs * (y 2 - y 3)| ≤ k600
    have := two_le hy (a := 2) (b := 3) (by decide) o n
    have := two_le hy (a := 2) (b := 3) (by decide) n o
    exact cs_abs (by linarith) (by linarith)

/-! ## 600-cells in a tesseract: side `3k = 3√2 (2 + √5)/4` -/

noncomputable def g8 : E4 ≃ᵃⁱ[ℝ] E4 :=
  M.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ E4 (pt4 (k600 / 2) (k600 / 2) (k600 / 2) (k600 / 2)))

theorem g8_apply (y : E4) : g8 y = pt4 (k600 / 2) (k600 / 2) (k600 / 2) (k600 / 2) + Ml y := rfl

theorem val8 : 3 * Real.sqrt 2 * (2 + Real.sqrt 5) / 4 = 3 * k600 := by unfold k600; ring

noncomputable def c600inc8_packing : Packing c600 (boxC 4) (3 * Real.sqrt 2 * (2 + Real.sqrt 5) / 4) 2 := by
  rw [val8]
  refine pairPacking g8 ?_ neg_box sum4 sum4_surjective ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_smul_box_of_coord (by linarith [k600_pos]) fun i => ?_
    have := abs_le.mp (Ml_bound hy i)
    rw [g8_apply, PiLp.add_apply, abs_le]
    fin_cases i <;> simp at this ⊢ <;> constructor <;> linarith
  · intro y hy
    have h := two_le hy (a := 0) (b := 2) (by decide) (Or.inr rfl) (Or.inr rfl)
    rw [sum4_apply, g8_apply]; simp [Ml_apply]
    have e : cs * (y 0 + y 2) ≥ -k600 := by
      rw [← cs_k]; nlinarith [cs_pos]
    linarith

/-- **Two 600-cells in a tesseract: edge `3√2 (2 + √5)/4` is optimal.** -/
theorem c600inc8_n02 : Nonempty (Packing c600 (boxC 4) (3 * Real.sqrt 2 * (2 + Real.sqrt 5) / 4) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c600 (boxC 4) s 2 → 3 * Real.sqrt 2 * (2 + Real.sqrt 5) / 4 ≤ s := by
  refine ⟨⟨c600inc8_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  rw [val8] at h
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_box c600 (k := k600) (t := 2)
    k600_pos (by norm_num) (by norm_num) (by norm_num) ball_c600 hs (by linarith) g hg) le_rfl P

/-! ## 600-cells in a 16-cell: side `3√2 k = 3 (2 + √5)/2` -/

theorem l1_M {y : E4} (hy : y ∈ c600) :
    |y 0 + y 1| + |y 0 - y 1| + |y 2 + y 3| + |y 2 - y 3| ≤ 2 + Real.sqrt 5 := by
  have o : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have n : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have := two_le hy (a := 0) (b := 2) (by decide) o o
  have := two_le hy (a := 0) (b := 2) (by decide) o n
  have := two_le hy (a := 0) (b := 2) (by decide) n o
  have := two_le hy (a := 0) (b := 2) (by decide) n n
  have := two_le hy (a := 0) (b := 3) (by decide) o o
  have := two_le hy (a := 0) (b := 3) (by decide) o n
  have := two_le hy (a := 0) (b := 3) (by decide) n o
  have := two_le hy (a := 0) (b := 3) (by decide) n n
  have := two_le hy (a := 1) (b := 2) (by decide) o o
  have := two_le hy (a := 1) (b := 2) (by decide) o n
  have := two_le hy (a := 1) (b := 2) (by decide) n o
  have := two_le hy (a := 1) (b := 2) (by decide) n n
  have := two_le hy (a := 1) (b := 3) (by decide) o o
  have := two_le hy (a := 1) (b := 3) (by decide) o n
  have := two_le hy (a := 1) (b := 3) (by decide) n o
  have := two_le hy (a := 1) (b := 3) (by decide) n n
  rcases abs_cases (y 0 + y 1) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases abs_cases (y 0 - y 1) with ⟨h2, -⟩ | ⟨h2, -⟩ <;>
    rcases abs_cases (y 2 + y 3) with ⟨h3, -⟩ | ⟨h3, -⟩ <;> rcases abs_cases (y 2 - y 3) with ⟨h4, -⟩ | ⟨h4, -⟩ <;>
    rw [h1, h2, h3, h4] <;> linarith

noncomputable def g16 : E4 ≃ᵃⁱ[ℝ] E4 :=
  M.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ E4 (pt4 k600 0 0 0))

theorem g16_apply (y : E4) : g16 y = pt4 k600 0 0 0 + Ml y := rfl

theorem val16 : 3 * (2 + Real.sqrt 5) / 2 * (Real.sqrt 2 / 2) = 3 * k600 := by unfold k600; ring

noncomputable def c600inc16_packing : Packing c600 c16 (3 * (2 + Real.sqrt 5) / 2) 2 := by
  refine pairPacking g16 ?_ neg_l1 (EuclideanSpace.proj 0) (proj_surjective 0) ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine mem_smul_l1_of (by positivity) ?_
    rw [val16, Fin.sum_univ_four, g16_apply]; simp [Ml_apply]
    have h := l1_M hy
    have t := abs_add_le k600 (cs * (y 0 + y 1))
    rw [abs_of_pos k600_pos] at t
    simp only [abs_mul, abs_of_pos cs_pos] at t ⊢
    have e : cs * (|y 0 + y 1| + |y 0 - y 1| + |y 2 + y 3| + |y 2 - y 3|) ≤ 2 * k600 := by
      rw [show 2 * k600 = cs * (2 + Real.sqrt 5) by rw [← cs_k]; ring]
      exact mul_le_mul_of_nonneg_left h cs_pos.le
    linarith
  · intro y hy
    have := abs_le.mp (Ml_bound hy 0)
    simp [g16_apply] at this ⊢; linarith

/-- **Two 600-cells in a 16-cell: edge `3 (2 + √5)/2` is optimal.** -/
theorem c600inc16_n02 : Nonempty (Packing c600 c16 (3 * (2 + Real.sqrt 5) / 2) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing c600 c16 s 2 → 3 * (2 + Real.sqrt 5) / 2 ≤ s := by
  refine ⟨⟨c600inc16_packing⟩, fun s hs P => ?_⟩
  by_contra h; push Not at h
  have h' := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < Real.sqrt 2 / 2)
  rw [val16] at h'
  exact no_packing_two_of_common_point (0 : E4) (fun g hg => centre_ball_l1 c600 (k := k600)
    (ρ := Real.sqrt 2 / 2) (t := 2) k600_pos (by norm_num) (by norm_num) ball_c600 hs (by linarith) g hg)
    le_rfl P

end PackingOptimality.Cells600
