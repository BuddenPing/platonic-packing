import PackingOptimality.OctBands
import PackingOptimality.CentreGeneral
import PackingOptimality.Prisms

/-!
# Two octahedra in a cube: side √2 is optimal

**Theorem (`octincub_n02`).** Two regular octahedra of edge 1 fit in a cube of edge `√2` (with disjoint interiors),
and in no smaller cube.

**Lemma O.** For a 3×3 orthogonal matrix with rows `ρᵢ`, any signs `σ ∈ {±1}³` and any `mᵢ ≥ ‖ρᵢ‖_∞`:
`Σᵢ |⟨ρᵢ, σ⟩| (1 - mᵢ) ≤ 1`. Equality holds for `ρᵢ = (2/3, 2/3, -1/3)` up to signs and order.

Proof of Lemma O:
* **Per row.** If `|ρₖ| ≤ m`, `Σ ρₖ² = 1` and `r = |Σ ρₖ|`, then `r ≤ 3m` and `1 ≤ 6m² - 4mr + r²`. Put
  `dₖ = m ∓ ρₖ ≥ 0`; then `Σ dₖ² ≤ (Σ dₖ)²`.
* **Lines.** Hence `r (1 - m)` lies below the tangent line `1/4 + r²/12` while `r² ≤ 2.09`, and below explicit
  lines on ten bands of `r² ∈ [2.09, 3]` (`OctBands`, with exact certificates).
* **Summing.** `Σᵢ rᵢ² = |Rσ|² = 3`, so if every `rᵢ² ≤ 2.09` the tangent lines give exactly 1. Otherwise one row
  is large and the other two have `m ≥ 0.5773` and `(r₁ + r₂)² ≤ 2(3 - r₀²)`.

**Centre lemma.** Let an octahedron (circumradius `ρ = √2/2`) be placed by `g = L + p` inside the cube
`[-s/2, s/2]³` with `s < √2`. Its vertices give `|pᵢ| + ρ|Aᵢₖ| ≤ s/2`. Lemma O with `mᵢ = (s/2 - |pᵢ|)/ρ` and
`σ = sign(L⁻¹(-p))` then shows `‖L⁻¹(-p)‖₁ < ρ`: the centre is strictly inside. So any two such octahedra share
an interior point.

**Construction.** At `s = √2`, place `H(octa) + (ρ/3)(1, 1, 1)` and its point reflection, with `H = I - (2/3)𝟙𝟙ᵀ`.
The plane `x + y + z = 0` separates them.
-/

namespace PackingOptimality.OctInCube

open Set Matrix NearAxis CentreGeneral OctBands
open scoped RealInnerProductSpace Pointwise

/-! ## The separable inequality -/

theorem one_big (rB mB r1 m1 r2 m2 : ℝ) (hrB : 0 ≤ rB) (hmB : rB / 3 ≤ mB)
    (hQB : 1 ≤ 6 * mB ^ 2 - 4 * mB * rB + rB ^ 2) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hm1 : (5773 / 10000 : ℝ) ≤ m1) (hm2 : (5773 / 10000 : ℝ) ≤ m2) (hs : rB ^ 2 + r1 ^ 2 + r2 ^ 2 = 3)
    (hbig : (209 / 100 : ℝ) ≤ rB ^ 2) : rB * (1 - mB) + r1 * (1 - m1) + r2 * (1 - m2) ≤ 1 := by
  have e1 : r1 * (1 - m1) ≤ 4227 / 10000 * r1 := by nlinarith
  have e2 : r2 * (1 - m2) ≤ 4227 / 10000 * r2 := by nlinarith
  have hS : (r1 + r2) ^ 2 ≤ 2 * (3 - rB ^ 2) := by nlinarith [sq_nonneg (r1 - r2)]
  have hS0 : 0 ≤ r1 + r2 := by linarith
  have h3 : rB ^ 2 ≤ 3 := by nlinarith [sq_nonneg r1, sq_nonneg r2]
  have amgm : ∀ t : ℝ, 0 < t → r1 + r2 ≤ (2 * (3 - rB ^ 2) + t ^ 2) / (2 * t) := fun t ht => by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (r1 + r2 - t)]
  by_cases hc : rB ^ 2 ≤ (53 / 25 : ℝ)
  · -- band [209/100, 53/25]
    have hb := oct_band1 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (1337 / 1000 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (1337 / 1000 : ℝ) ^ 2) / (2 * (1337 / 1000 : ℝ)) = (6 + (1337 / 1000 : ℝ) ^ 2) / (2 * (1337 / 1000 : ℝ)) - rB ^ 2 / (1337 / 1000 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (54 / 25 : ℝ)
  · -- band [53/25, 54/25]
    have hb := oct_band2 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (1311 / 1000 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (1311 / 1000 : ℝ) ^ 2) / (2 * (1311 / 1000 : ℝ)) = (6 + (1311 / 1000 : ℝ) ^ 2) / (2 * (1311 / 1000 : ℝ)) - rB ^ 2 / (1311 / 1000 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (111 / 50 : ℝ)
  · -- band [54/25, 111/50]
    have hb := oct_band3 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (159 / 125 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (159 / 125 : ℝ) ^ 2) / (2 * (159 / 125 : ℝ)) = (6 + (159 / 125 : ℝ) ^ 2) / (2 * (159 / 125 : ℝ)) - rB ^ 2 / (159 / 125 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (23 / 10 : ℝ)
  · -- band [111/50, 23/10]
    have hb := oct_band4 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (152 / 125 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (152 / 125 : ℝ) ^ 2) / (2 * (152 / 125 : ℝ)) = (6 + (152 / 125 : ℝ) ^ 2) / (2 * (152 / 125 : ℝ)) - rB ^ 2 / (152 / 125 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (12 / 5 : ℝ)
  · -- band [23/10, 12/5]
    have hb := oct_band5 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (57 / 50 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (57 / 50 : ℝ) ^ 2) / (2 * (57 / 50 : ℝ)) = (6 + (57 / 50 : ℝ) ^ 2) / (2 * (57 / 50 : ℝ)) - rB ^ 2 / (57 / 50 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (51 / 20 : ℝ)
  · -- band [12/5, 51/20]
    have hb := oct_band6 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (128 / 125 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (128 / 125 : ℝ) ^ 2) / (2 * (128 / 125 : ℝ)) = (6 + (128 / 125 : ℝ) ^ 2) / (2 * (128 / 125 : ℝ)) - rB ^ 2 / (128 / 125 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (27 / 10 : ℝ)
  · -- band [51/20, 27/10]
    have hb := oct_band7 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (433 / 500 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (433 / 500 : ℝ) ^ 2) / (2 * (433 / 500 : ℝ)) = (6 + (433 / 500 : ℝ) ^ 2) / (2 * (433 / 500 : ℝ)) - rB ^ 2 / (433 / 500 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (57 / 20 : ℝ)
  · -- band [27/10, 57/20]
    have hb := oct_band8 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (67 / 100 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (67 / 100 : ℝ) ^ 2) / (2 * (67 / 100 : ℝ)) = (6 + (67 / 100 : ℝ) ^ 2) / (2 * (67 / 100 : ℝ)) - rB ^ 2 / (67 / 100 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  by_cases hc : rB ^ 2 ≤ (59 / 20 : ℝ)
  · -- band [57/20, 59/20]
    have hb := oct_band9 rB mB hrB hmB hQB (by linarith) hc
    have ha := amgm (447 / 1000 : ℝ) (by norm_num)
    have : (2 * (3 - rB ^ 2) + (447 / 1000 : ℝ) ^ 2) / (2 * (447 / 1000 : ℝ)) = (6 + (447 / 1000 : ℝ) ^ 2) / (2 * (447 / 1000 : ℝ)) - rB ^ 2 / (447 / 1000 : ℝ) := by ring
    rw [this] at ha
    linarith
  push Not at hc
  have hc : rB ^ 2 ≤ (3 : ℝ) := h3
  -- band [59/20, 3]
  have hb := oct_band10 rB mB hrB hmB hQB (by linarith) hc
  have ha := amgm (223 / 1000 : ℝ) (by norm_num)
  have : (2 * (3 - rB ^ 2) + (223 / 1000 : ℝ) ^ 2) / (2 * (223 / 1000 : ℝ)) = (6 + (223 / 1000 : ℝ) ^ 2) / (2 * (223 / 1000 : ℝ)) - rB ^ 2 / (223 / 1000 : ℝ) := by ring
  rw [this] at ha
  linarith

theorem oct_sep (r0 r1 r2 m0 m1 m2 : ℝ) (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hm0 : r0 / 3 ≤ m0) (hm1 : r1 / 3 ≤ m1) (hm2 : r2 / 3 ≤ m2)
    (hQ0 : 1 ≤ 6 * m0 ^ 2 - 4 * m0 * r0 + r0 ^ 2) (hQ1 : 1 ≤ 6 * m1 ^ 2 - 4 * m1 * r1 + r1 ^ 2)
    (hQ2 : 1 ≤ 6 * m2 ^ 2 - 4 * m2 * r2 + r2 ^ 2)
    (hl0 : (5773 / 10000 : ℝ) ≤ m0) (hl1 : (5773 / 10000 : ℝ) ≤ m1) (hl2 : (5773 / 10000 : ℝ) ≤ m2)
    (hs : r0 ^ 2 + r1 ^ 2 + r2 ^ 2 = 3) :
    r0 * (1 - m0) + r1 * (1 - m1) + r2 * (1 - m2) ≤ 1 := by
  by_cases b0 : (209 / 100 : ℝ) ≤ r0 ^ 2
  · exact one_big r0 m0 r1 m1 r2 m2 hr0 hm0 hQ0 hr1 hr2 hl1 hl2 hs b0
  by_cases b1 : (209 / 100 : ℝ) ≤ r1 ^ 2
  · have := one_big r1 m1 r0 m0 r2 m2 hr1 hm1 hQ1 hr0 hr2 hl0 hl2 (by linarith) b1; linarith
  by_cases b2 : (209 / 100 : ℝ) ≤ r2 ^ 2
  · have := one_big r2 m2 r0 m0 r1 m1 hr2 hm2 hQ2 hr0 hr1 hl0 hl1 (by linarith) b2; linarith
  push Not at b0 b1 b2
  have t0 := oct_tangent r0 m0 hr0 hm0 hQ0 (sq_nonneg _) b0.le
  have t1 := oct_tangent r1 m1 hr1 hm1 hQ1 (sq_nonneg _) b1.le
  have t2 := oct_tangent r2 m2 hr2 hm2 hQ2 (sq_nonneg _) b2.le
  linarith

/-! ## Per row, and Lemma O -/

theorem row_facts (a b c m : ℝ) (ha : |a| ≤ m) (hb : |b| ≤ m) (hc : |c| ≤ m) (h1 : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    |a + b + c| / 3 ≤ m ∧ 1 ≤ 6 * m ^ 2 - 4 * m * |a + b + c| + |a + b + c| ^ 2 ∧ (5773 / 10000 : ℝ) ≤ m := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  refine ⟨?_, ?_, ?_⟩
  · have : |a + b + c| ≤ 3 * m := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · rw [sq_abs]
    rcases le_total 0 (a + b + c) with hs | hs
    · rw [abs_of_nonneg hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2), mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2),
        mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2)]
    · rw [abs_of_nonpos hs]
      nlinarith [mul_nonneg (neg_le_iff_add_nonneg.mp ha1) (neg_le_iff_add_nonneg.mp hb1),
        mul_nonneg (neg_le_iff_add_nonneg.mp ha1) (neg_le_iff_add_nonneg.mp hc1),
        mul_nonneg (neg_le_iff_add_nonneg.mp hb1) (neg_le_iff_add_nonneg.mp hc1)]
  · have hm0 : 0 ≤ m := le_trans (abs_nonneg a) ha
    have : 1 ≤ 3 * m ^ 2 := by nlinarith [sq_abs a, sq_abs b, sq_abs c, abs_nonneg a, abs_nonneg b, abs_nonneg c]
    nlinarith

theorem sum_w_sq (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1) (σ : Fin 3 → ℝ) (hσ : ∀ k, σ k ^ 2 = 1) :
    (R 0 0 * σ 0 + R 0 1 * σ 1 + R 0 2 * σ 2) ^ 2 + (R 1 0 * σ 0 + R 1 1 * σ 1 + R 1 2 * σ 2) ^ 2 +
      (R 2 0 * σ 0 + R 2 1 * σ 1 + R 2 2 * σ 2) ^ 2 = 3 := by
  have col : ∀ a b, R 0 a * R 0 b + R 1 a * R 1 b + R 2 a * R 2 b = if a = b then 1 else 0 := fun a b => by
    have h := congrFun (congrFun hR a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply] at h
    exact h
  have c00 := col 0 0; have c01 := col 0 1; have c02 := col 0 2
  have c11 := col 1 1; have c12 := col 1 2; have c22 := col 2 2
  simp only [Fin.reduceEq, ↓reduceIte] at c00 c01 c02 c11 c12 c22
  linear_combination σ 0 ^ 2 * c00 + σ 1 ^ 2 * c11 + σ 2 ^ 2 * c22 + 2 * σ 0 * σ 1 * c01 +
    2 * σ 0 * σ 2 * c02 + 2 * σ 1 * σ 2 * c12 + hσ 0 + hσ 1 + hσ 2

/-- **Lemma O.** -/
theorem lemmaO (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1) (hR' : R * Rᵀ = 1) (σ : Fin 3 → ℝ)
    (hσ : ∀ k, σ k ^ 2 = 1) (m : Fin 3 → ℝ) (hm : ∀ i k, |R i k| ≤ m i) :
    ∑ i, |∑ k, R i k * σ k| * (1 - m i) ≤ 1 := by
  have hs1 : ∀ k, |σ k| = 1 := fun k => by
    have h := hσ k; rw [← sq_abs] at h
    nlinarith [abs_nonneg (σ k)]
  have row : ∀ i, (R i 0 * σ 0) ^ 2 + (R i 1 * σ 1) ^ 2 + (R i 2 * σ 2) ^ 2 = 1 := fun i => by
    have h := congrFun (congrFun hR' i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h
    linear_combination h + R i 0 ^ 2 * hσ 0 + R i 1 ^ 2 * hσ 1 + R i 2 ^ 2 * hσ 2
  have hb : ∀ i k, |R i k * σ k| ≤ m i := fun i k => by rw [abs_mul, hs1, mul_one]; exact hm i k
  have f0 := row_facts _ _ _ _ (hb 0 0) (hb 0 1) (hb 0 2) (row 0)
  have f1 := row_facts _ _ _ _ (hb 1 0) (hb 1 1) (hb 1 2) (row 1)
  have f2 := row_facts _ _ _ _ (hb 2 0) (hb 2 1) (hb 2 2) (row 2)
  have hw := sum_w_sq R hR σ hσ
  simp only [Fin.sum_univ_three]
  exact oct_sep _ _ _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) f0.1 f1.1 f2.1 f0.2.1 f1.2.1 f2.2.1
    f0.2.2 f1.2.2 f2.2.2 (by rw [sq_abs, sq_abs, sq_abs]; exact hw)


/-! ## Octahedra and the cube -/

/-- The regular octahedron of edge 1, centred at the origin (circumradius `√2/2`). -/
noncomputable def octa : Set P3 := {y | |y 0| + |y 1| + |y 2| ≤ Real.sqrt 2 / 2}

/-- The cube of edge 1, centred at the origin. -/
def cubeC : Set P3 := {x | ∀ i, |x i| ≤ 1 / 2}

theorem coord_of_mem_smul {s : ℝ} (hs : 0 ≤ s) {x : P3} (hx : x ∈ s • cubeC) (i : Fin 3) : |x i| ≤ s / 2 := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs]
  nlinarith [hy i]

theorem mem_smul_of_coord {s : ℝ} (hs : 0 < s) {x : P3} (hx : ∀ i, |x i| ≤ s / 2) : x ∈ s • cubeC := by
  refine ⟨s⁻¹ • x, fun i => ?_, by simp [smul_smul, hs.ne']⟩
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  rw [inv_mul_le_iff₀ hs]; linarith [hx i]

theorem single_apply3 (k : Fin 3) (c : ℝ) (j : Fin 3) :
    (EuclideanSpace.single k c : P3) j = if j = k then c else 0 := by
  simp [PiLp.single_apply]

theorem single_mem_octa (k : Fin 3) {c : ℝ} (hc : |c| ≤ Real.sqrt 2 / 2) : (EuclideanSpace.single k c : P3) ∈ octa := by
  simp only [octa, Set.mem_setOf_eq]
  fin_cases k <;> simp [single_apply3] <;> exact hc

/-- **The centre lemma for an octahedron in a cube.** -/
theorem centre_oct (s : ℝ) (hs0 : 0 ≤ s) (hs : s < Real.sqrt 2) (g : P3 ≃ᵃⁱ[ℝ] P3) (hg : g '' octa ⊆ s • cubeC) :
    (0 : P3) ∈ interior (g '' octa) := by
  set ρ := Real.sqrt 2 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρs : s / 2 < ρ := by rw [hρ]; linarith
  set L := g.linearIsometryEquiv with hLdef
  set A := matOf L with hA
  set p := g 0 with hp
  have hgx : ∀ x, g x = L x + p := fun x => by have := g.map_vadd 0 x; simpa using this
  have hAt : Aᵀ * A = 1 := matOf_orth L
  have hAA : A * Aᵀ = 1 := mul_eq_one_comm.mp hAt
  -- the vertices `±ρ e_k` give `|pᵢ| + ρ |Aᵢₖ| ≤ s/2`
  have vert : ∀ i k, |p i| + ρ * |A i k| ≤ s / 2 := by
    intro i k
    have e : ∀ c : ℝ, (g (EuclideanSpace.single k c)) i = c * A i k + p i := by
      intro c
      rw [hgx, PiLp.add_apply, matOf_apply]
      fin_cases k <;> simp [mul_comm, hA]
    have h1 := coord_of_mem_smul hs0 (hg ⟨_, single_mem_octa k (c := ρ) (by rw [abs_of_pos hρ0]), rfl⟩) i
    have h2 := coord_of_mem_smul hs0 (hg ⟨_, single_mem_octa k (c := -ρ) (by rw [abs_neg, abs_of_pos hρ0]), rfl⟩) i
    rw [e] at h1 h2
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rcases le_total 0 (p i) with hp0 | hp0 <;> rcases le_total 0 (A i k) with ha0 | ha0
    · rw [abs_of_nonneg hp0, abs_of_nonneg ha0]; nlinarith
    · rw [abs_of_nonneg hp0, abs_of_nonpos ha0]; nlinarith
    · rw [abs_of_nonpos hp0, abs_of_nonneg ha0]; nlinarith
    · rw [abs_of_nonpos hp0, abs_of_nonpos ha0]; nlinarith
  set m : Fin 3 → ℝ := fun i => (s / 2 - |p i|) / ρ with hmdef
  have hm : ∀ i k, |A i k| ≤ m i := fun i k => by
    simp only [hmdef]; rw [le_div_iff₀ hρ0]; linarith [vert i k]
  -- the preimage of the centre
  obtain ⟨y, hy⟩ : ∃ y, y = g.symm 0 := ⟨_, rfl⟩
  have hgy : g y = 0 := by rw [hy]; exact g.apply_symm_apply 0
  have hLy : L y = -p := by rw [hgx] at hgy; exact eq_neg_of_add_eq_zero_left hgy
  have hyk : ∀ k, y k = ∑ i, A i k * (-p i) := by
    intro k
    have : y = L.symm (-p) := by rw [← hLy, L.symm_apply_apply]
    rw [this, matOf_symm_apply]; simp [hA]
  set σ : Fin 3 → ℝ := fun k => if 0 ≤ y k then 1 else -1 with hσdef
  have hσ : ∀ k, σ k ^ 2 = 1 := fun k => by simp only [hσdef]; split_ifs <;> norm_num
  have hσy : ∀ k, σ k * y k = |y k| := fun k => by
    simp only [hσdef]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hO := lemmaO A hAt hAA σ hσ m hm
  have hw := sum_w_sq A hAt σ hσ
  simp only [Fin.sum_univ_three] at hO
  set w0 := A 0 0 * σ 0 + A 0 1 * σ 1 + A 0 2 * σ 2
  set w1 := A 1 0 * σ 0 + A 1 1 * σ 1 + A 1 2 * σ 2
  set w2 := A 2 0 * σ 0 + A 2 1 * σ 1 + A 2 2 * σ 2
  have hsum : |y 0| + |y 1| + |y 2| = -(p 0 * w0 + p 1 * w1 + p 2 * w2) := by
    rw [← hσy 0, ← hσy 1, ← hσy 2, hyk 0, hyk 1, hyk 2]
    simp only [Fin.sum_univ_three]; ring
  have hpw : -(p 0 * w0 + p 1 * w1 + p 2 * w2) ≤ |p 0| * |w0| + |p 1| * |w1| + |p 2| * |w2| := by
    have := neg_abs_le (p 0 * w0); have := neg_abs_le (p 1 * w1); have := neg_abs_le (p 2 * w2)
    rw [abs_mul] at *; linarith
  -- multiply Lemma O by `ρ`
  have hO' : |w0| * (ρ - s / 2 + |p 0|) + |w1| * (ρ - s / 2 + |p 1|) + |w2| * (ρ - s / 2 + |p 2|) ≤ ρ := by
    have e : ∀ (w q : ℝ), |w| * (1 - (s / 2 - |q|) / ρ) * ρ = |w| * (ρ - s / 2 + |q|) := fun w q => by
      field_simp; ring
    have := mul_le_mul_of_nonneg_right hO hρ0.le
    simp only [hmdef] at this
    rw [add_mul, add_mul, e, e, e, one_mul] at this
    exact this
  have hpos : 0 < |w0| + |w1| + |w2| := by
    have h3 : |w0| ^ 2 + |w1| ^ 2 + |w2| ^ 2 = 3 := by rw [sq_abs, sq_abs, sq_abs]; exact hw
    nlinarith [abs_nonneg w0, abs_nonneg w1, abs_nonneg w2]
  have hlt : |y 0| + |y 1| + |y 2| < ρ := by
    have : 0 < (ρ - s / 2) * (|w0| + |w1| + |w2|) := mul_pos (by linarith) hpos
    nlinarith
  -- the open octahedron maps onto an open subset of the image that contains the centre
  let U : Set P3 := {z | |z 0| + |z 1| + |z 2| < ρ}
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have himg : IsOpen (g '' U) := by simpa using g.toHomeomorph.isOpenMap U hUo
  have hsub : g '' U ⊆ g '' octa := image_mono fun z (hz : |z 0| + |z 1| + |z 2| < ρ) =>
    show |z 0| + |z 1| + |z 2| ≤ Real.sqrt 2 / 2 from hz.le
  exact interior_maximal hsub himg ⟨y, hlt, hgy⟩


/-! ## The packing at side √2 -/

/-- The reflection `H = I - (2/3) 𝟙𝟙ᵀ` in the plane `x + y + z = 0`. -/
noncomputable def Hl : P3 →ₗ[ℝ] P3 where
  toFun y := pt (y 0 - 2 / 3 * (y 0 + y 1 + y 2)) (y 1 - 2 / 3 * (y 0 + y 1 + y 2)) (y 2 - 2 / 3 * (y 0 + y 1 + y 2))
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

theorem Hl_apply (y : P3) :
    Hl y = pt (y 0 - 2 / 3 * (y 0 + y 1 + y 2)) (y 1 - 2 / 3 * (y 0 + y 1 + y 2)) (y 2 - 2 / 3 * (y 0 + y 1 + y 2)) := rfl

noncomputable def Heq : P3 ≃ₗ[ℝ] P3 :=
  LinearEquiv.ofInvolutive Hl (fun y => by ext i; fin_cases i <;> simp [Hl_apply] <;> ring)

noncomputable def Hiso : P3 ≃ₗᵢ[ℝ] P3 :=
  Heq.isometryOfInner (fun x y => by
    show ⟪Hl x, Hl y⟫ = ⟪x, y⟫
    simp only [CentreGeneral.inner_sum, Fin.sum_univ_three, Hl_apply, pt_zero, pt_one, pt_two]
    ring)

theorem Hiso_apply (y : P3) : Hiso y = Hl y := rfl

noncomputable def p0 : P3 := pt (Real.sqrt 2 / 2 / 3) (Real.sqrt 2 / 2 / 3) (Real.sqrt 2 / 2 / 3)

noncomputable def g1 : P3 ≃ᵃⁱ[ℝ] P3 :=
  Hiso.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ P3 p0)

noncomputable def g2 : P3 ≃ᵃⁱ[ℝ] P3 := g1.trans (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv

theorem g1_apply (y : P3) : g1 y = p0 + Hl y := rfl
theorem g2_apply (y : P3) : g2 y = -(p0 + Hl y) := rfl

theorem g1_coord (y : P3) (i : Fin 3) :
    g1 y i = Real.sqrt 2 / 2 / 3 + (y i - 2 / 3 * (y 0 + y 1 + y 2)) := by
  rw [g1_apply, PiLp.add_apply, Hl_apply]; fin_cases i <;> simp [p0]

theorem g1_bound {y : P3} (hy : y ∈ octa) (i : Fin 3) : |g1 y i| ≤ Real.sqrt 2 / 2 := by
  have hy' : |y 0| + |y 1| + |y 2| ≤ Real.sqrt 2 / 2 := hy
  have a0 := abs_le.mp (le_refl |y 0|); have a1 := abs_le.mp (le_refl |y 1|); have a2 := abs_le.mp (le_refl |y 2|)
  have n0 := abs_nonneg (y 0); have n1 := abs_nonneg (y 1); have n2 := abs_nonneg (y 2)
  rw [g1_coord, abs_le]
  fin_cases i <;> simp <;> constructor <;> linarith [neg_abs_le (y 0), le_abs_self (y 0), neg_abs_le (y 1),
    le_abs_self (y 1), neg_abs_le (y 2), le_abs_self (y 2)]

theorem sqrt2_pos' : (0 : ℝ) < Real.sqrt 2 := by positivity

theorem g1_inside : g1 '' octa ⊆ Real.sqrt 2 • cubeC := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_smul_of_coord sqrt2_pos' fun i => g1_bound hy i

theorem g2_inside : g2 '' octa ⊆ Real.sqrt 2 • cubeC := by
  rintro _ ⟨y, hy, rfl⟩
  refine mem_smul_of_coord sqrt2_pos' fun i => ?_
  have := g1_bound hy i
  rw [g2_apply, PiLp.neg_apply, abs_neg, ← g1_apply]; exact this

/-- `x + y + z`. -/
noncomputable def sum3 : P3 →L[ℝ] ℝ := coordL 0 + coordL 1 + coordL 2

theorem sum3_apply (x : P3) : sum3 x = x 0 + x 1 + x 2 := rfl

theorem sum3_surjective : Function.Surjective sum3 :=
  fun t => ⟨EuclideanSpace.single 0 t, by simp [sum3_apply, single_apply3]⟩

theorem sum3_g1 (y : P3) : sum3 (g1 y) = Real.sqrt 2 / 2 - (y 0 + y 1 + y 2) := by
  rw [sum3_apply, g1_coord, g1_coord, g1_coord]; ring

theorem octa_sum {y : P3} (hy : y ∈ octa) : y 0 + y 1 + y 2 ≤ Real.sqrt 2 / 2 := by
  have hy' : |y 0| + |y 1| + |y 2| ≤ Real.sqrt 2 / 2 := hy
  linarith [le_abs_self (y 0), le_abs_self (y 1), le_abs_self (y 2)]

theorem g12_disjoint : Disjoint (interior (g2 '' octa)) (interior (g1 '' octa)) := by
  apply interior_disjoint_of_separated sum3 sum3_surjective (c := 0)
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [g2_apply, map_neg, ← g1_apply, sum3_g1]; linarith [octa_sum hy]
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Ici]
    rw [sum3_g1]; linarith [octa_sum hy]

/-- Two octahedra of edge 1 in the cube of edge √2. -/
noncomputable def octPacking : Packing octa cubeC (Real.sqrt 2) 2 where
  g := ![g1, g2]
  inside := by
    intro i; fin_cases i
    · exact g1_inside
    · exact g2_inside
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact g12_disjoint.symm
    · exact g12_disjoint
    · exact absurd rfl hij

end PackingOptimality.OctInCube

namespace PackingOptimality

open OctInCube

/-- **Two octahedra in a cube: side √2 is optimal.** Two regular octahedra of edge 1 fit in a cube of edge `√2`
with disjoint interiors, and in no smaller cube. -/
theorem octincub_n02 : Nonempty (Packing octa cubeC (Real.sqrt 2) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing octa cubeC s 2 → Real.sqrt 2 ≤ s := by
  refine ⟨⟨octPacking⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : P3) (fun g hg => centre_oct s hs h g hg) le_rfl P

end PackingOptimality
