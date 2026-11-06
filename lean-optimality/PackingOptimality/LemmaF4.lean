import PackingOptimality.CubeCentre
import PackingOptimality.NearAxis

/-!
# Lemma F in dimension 4, and s₄(2) = 2

`F_j(R) = Σᵢ |Rᵢⱼ| (2 - ‖row i‖₁) ≤ 1` for every orthogonal 4×4 matrix and every column `j`.

* **Lemma F in dimension 3** in Hosono's matrix form (`lemmaF3`), from `CubeCentre.core`.
* **Near an axis**, `Rᵢⱼ² ≥ 2/3` for some `i`: Hosono's polar-decomposition step (`NearAxis.near_region`),
  which takes Lemma F in dimension 3 as its hypothesis.
* **Elsewhere**, every `Rᵢⱼ² ≤ 2/3`: an elementary bound. For each other column `k`, the vector
  `zᵢ = Rᵢⱼ Rᵢₖ` has zero sum, so `‖z‖₁ ≥ √2 ‖z‖₂`, and `‖z‖₂ ≥ Σᵢ |Rᵢⱼ| Rᵢₖ²` (Cauchy–Schwarz). Summing over
  `k ≠ j` gives `F_j ≤ 2S - 1 - √2 Σᵢ xᵢ(1 - xᵢ²)` with `xᵢ = |Rᵢⱼ|`, `S = Σᵢ xᵢ`, and a one-variable case
  analysis shows the right side is at most 1 when every `xᵢ² ≤ 2/3`.
-/

namespace PackingOptimality.LemmaF4

open NearAxis Matrix

/-! ## Lemma F in dimension 3, matrix form -/

theorem lemmaF3 : LemmaF 3 := by
  intro Q hQ j
  have hQ' : Qᵀ * Q = 1 := mul_eq_one_comm.mp hQ
  have row : ∀ i, Q i 0 ^ 2 + Q i 1 ^ 2 + Q i 2 ^ 2 = 1 := fun i => by
    have h := congrFun (congrFun hQ i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply_eq] at h
    linear_combination h
  have col : ∀ a b, Q 0 a * Q 0 b + Q 1 a * Q 1 b + Q 2 a * Q 2 b = if a = b then 1 else 0 := fun a b => by
    have h := congrFun (congrFun hQ' a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply] at h
    exact h
  have c00 := col 0 0; have c01 := col 0 1; have c02 := col 0 2
  have c11 := col 1 1; have c12 := col 1 2; have c22 := col 2 2
  simp only [Fin.reduceEq, ↓reduceIte] at c00 c01 c02 c11 c12 c22
  have r0 := row 0; have r1 := row 1; have r2 := row 2
  have s : ∀ i k : Fin 3, |Q i k| ^ 2 = Q i k ^ 2 := fun i k => sq_abs _
  simp only [Fcol, rowL1, l1, Fin.sum_univ_three]
  fin_cases j
  · have := CubeCentre.core (Q 0 0) (Q 1 0) (Q 2 0) (Q 0 1) (Q 1 1) (Q 2 1) (Q 0 2) (Q 1 2) (Q 2 2)
      (by linear_combination c00) (by linear_combination c11) (by linear_combination c22) c01 c02 c12 r0 r1 r2
    simp only [Fin.zero_eta, Fin.isValue]
    linarith [s 0 0, s 1 0, s 2 0]
  · have := CubeCentre.core (Q 0 1) (Q 1 1) (Q 2 1) (Q 0 0) (Q 1 0) (Q 2 0) (Q 0 2) (Q 1 2) (Q 2 2)
      (by linear_combination c11) (by linear_combination c00) (by linear_combination c22)
      (by linear_combination c01) c12 c02 (by linear_combination r0) (by linear_combination r1)
      (by linear_combination r2)
    simp only [Fin.mk_one, Fin.isValue]
    linarith [s 0 1, s 1 1, s 2 1]
  · have := CubeCentre.core (Q 0 2) (Q 1 2) (Q 2 2) (Q 0 0) (Q 1 0) (Q 2 0) (Q 0 1) (Q 1 1) (Q 2 1)
      (by linear_combination c22) (by linear_combination c00) (by linear_combination c11)
      (by linear_combination c02) (by linear_combination c12) c01 (by linear_combination r0)
      (by linear_combination r1) (by linear_combination r2)
    simp only [Fin.reduceFinMk, Fin.isValue]
    linarith [s 0 2, s 1 2, s 2 2]

/-! ## The block decomposition around an entry -/

variable {m : ℕ}

theorem sum_rows (R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hR : R * Rᵀ = 1) (a b : Fin (m + 1)) :
    ∑ k, R a k * R b k = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hR a) b
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem sum_cols (R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hR : Rᵀ * R = 1) (a b : Fin (m + 1)) :
    ∑ i, R i a * R i b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hR a) b
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem block_orth (R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hR : R * Rᵀ = 1) (hR' : Rᵀ * R = 1)
    (i₀ j : Fin (m + 1)) :
    BlockOrth (R i₀ j) (fun k => R i₀ (j.succAbove k)) (fun i => R (i₀.succAbove i) j)
      (fun i k => R (i₀.succAbove i) (j.succAbove k)) where
  col1 := by
    have h := sum_cols R hR' j j
    rw [Fin.sum_univ_succAbove _ i₀, if_pos rfl] at h
    simp only [sq2, pow_two]; linear_combination h
  row1 := by
    have h := sum_rows R hR i₀ i₀
    rw [Fin.sum_univ_succAbove _ j, if_pos rfl] at h
    simp only [sq2, pow_two]; linear_combination h
  col1_perp := fun k => by
    have h := sum_cols R hR' j (j.succAbove k)
    rw [Fin.sum_univ_succAbove _ i₀, if_neg (Fin.succAbove_ne j k).symm] at h
    exact h
  rows := fun i k => by
    have h := sum_rows R hR (i₀.succAbove i) (i₀.succAbove k)
    rw [Fin.sum_univ_succAbove _ j] at h
    simp only [Fin.succAbove_right_inj] at h
    exact h

theorem rowL1_split (R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (i j : Fin (m + 1)) :
    rowL1 R i = |R i j| + ∑ k, |R i (j.succAbove k)| := by
  simp only [rowL1, l1]
  exact Fin.sum_univ_succAbove (fun k => |R i k|) j

theorem Fcol_eq_F1 (R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (i₀ j : Fin (m + 1)) :
    Fcol R j = F1 (R i₀ j) (fun k => R i₀ (j.succAbove k)) (fun i => R (i₀.succAbove i) j)
      (fun i k => R (i₀.succAbove i) (j.succAbove k)) := by
  unfold Fcol
  rw [Fin.sum_univ_succAbove _ i₀]
  simp only [rowL1_split R _ j]
  simp only [F1, l1, rowL1]
  ring_nf

/-- **Near an axis (Hosono).** If some entry of column `j` has square at least `2/3`, then `F_j ≤ 1`. -/
theorem near4 (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : R * Rᵀ = 1) (i₀ j : Fin 4) (hc : 2 / 3 ≤ R i₀ j ^ 2) :
    Fcol R j ≤ 1 := by
  have hR' : Rᵀ * R = 1 := mul_eq_one_comm.mp hR
  have hB := block_orth (m := 3) R hR hR' i₀ j
  rw [Fcol_eq_F1 (m := 3) R i₀ j]
  have hs : ((3 : ℕ) : ℝ) * sq2 (fun i => R (i₀.succAbove i) j) ≤ 1 := by
    have := hB.col1; push_cast; linarith
  rcases lt_or_gt_of_ne (show R i₀ j ≠ 0 by rintro h; rw [h] at hc; norm_num at hc) with hneg | hpos
  · -- flip the sign of the corner and of the rest of its row
    have hB' : BlockOrth (-R i₀ j) (-fun k => R i₀ (j.succAbove k)) (fun i => R (i₀.succAbove i) j)
        (fun i k => R (i₀.succAbove i) (j.succAbove k)) :=
      { col1 := by rw [neg_sq]; exact hB.col1
        row1 := by
          have := hB.row1
          simp only [sq2, Pi.neg_apply, neg_sq] at this ⊢
          exact this
        col1_perp := fun k => by
          have := hB.col1_perp k
          simp only [Pi.neg_apply]
          linarith
        rows := hB.rows }
    have := near_region (m := 3) (by norm_num) lemmaF3 hB' (by linarith) hs
    simpa [F1, l1, abs_neg] using this
  · exact near_region (m := 3) (by norm_num) lemmaF3 hB hpos hs


/-! ## Away from the axes -/

/-- The one-variable function of the far-region bound (`140/99 ≤ √2`). -/
noncomputable def phi (t : ℝ) : ℝ := 140 / 99 * (t - t ^ 3) - 2 * t

theorem phi_small (t : ℝ) (ht : 0 ≤ t) (h : t ^ 2 ≤ 2 / 5) :
    -6592 / 100000 + (-165782 / 100000) * t ^ 2 ≤ phi t := by
  have hU : 0 ≤ 6325 / 10000 - t := by nlinarith
  unfold phi
  nlinarith [mul_nonneg hU (sq_nonneg (t - 6 / 25)), mul_nonneg hU (sq_nonneg (t - 53 / 200)),
    mul_nonneg hU (sq_nonneg (t - 27 / 100))]

theorem phi_large (t : ℝ) (ht : 0 ≤ t) (_h1 : 2 / 5 ≤ t ^ 2) (h2 : t ^ 2 ≤ 2 / 3) :
    -14366 / 100000 + (-165782 / 100000) * t ^ 2 ≤ phi t := by
  have hU : 0 ≤ 8165 / 10000 - t := by nlinarith
  unfold phi
  nlinarith [mul_nonneg hU (sq_nonneg (t - 1 / 40)), mul_nonneg hU (sq_nonneg (t - 141 / 200)),
    mul_nonneg hU (sq_nonneg (t - 197 / 200))]

theorem phi_large2 (t : ℝ) (ht : 0 ≤ t) (h1 : 2 / 5 ≤ t ^ 2) (h2 : t ^ 2 ≤ 3 / 5) :
    3645 / 100000 + (-191374 / 100000) * t ^ 2 ≤ phi t := by
  have hU : 0 ≤ 7746 / 10000 - t := by nlinarith
  have hL : 0 ≤ t - 6324 / 10000 := by nlinarith
  unfold phi
  nlinarith [mul_nonneg hL hU, mul_nonneg hU (sq_nonneg (t - 57 / 100)),
    mul_nonneg hU (sq_nonneg (t - 23 / 40))]

/-- Each coordinate is small (`≤ 2/5`), middle (`2/5` to `3/5`) or big (`≥ 3/5`), with its line bounds. -/
theorem phi_cases (t : ℝ) (ht : 0 ≤ t) (hc : t ^ 2 ≤ 2 / 3) :
    (t ^ 2 ≤ 2 / 5 ∧ -6592 / 100000 + (-165782 / 100000) * t ^ 2 ≤ phi t) ∨
    (2 / 5 ≤ t ^ 2 ∧ t ^ 2 ≤ 3 / 5 ∧ -14366 / 100000 + (-165782 / 100000) * t ^ 2 ≤ phi t ∧
      3645 / 100000 + (-191374 / 100000) * t ^ 2 ≤ phi t) ∨
    (3 / 5 ≤ t ^ 2 ∧ -14366 / 100000 + (-165782 / 100000) * t ^ 2 ≤ phi t) := by
  rcases le_total (t ^ 2) (2 / 5) with h | h
  · exact Or.inl ⟨h, phi_small t ht h⟩
  · rcases le_total (t ^ 2) (3 / 5) with h' | h'
    · exact Or.inr (Or.inl ⟨h, h', phi_large t ht h hc, phi_large2 t ht h h'⟩)
    · exact Or.inr (Or.inr ⟨h', phi_large t ht h hc⟩)

set_option maxHeartbeats 4000000 in
/-- The far-region inequality: `Σᵢ φ(xᵢ) ≥ -2` when `Σ xᵢ² = 1` and every `xᵢ² ≤ 2/3`. Each `xᵢ` is bounded
by a line in `xᵢ²`, depending on its range; the three-way split per coordinate is closed by `linarith`. -/
theorem far_poly (x0 x1 x2 x3 : ℝ) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (hs : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) (c0 : x0 ^ 2 ≤ 2 / 3) (c1 : x1 ^ 2 ≤ 2 / 3)
    (c2 : x2 ^ 2 ≤ 2 / 3) (c3 : x3 ^ 2 ≤ 2 / 3) :
    -2 ≤ phi x0 + phi x1 + phi x2 + phi x3 := by
  have q0 := sq_nonneg x0; have q1 := sq_nonneg x1; have q2 := sq_nonneg x2; have q3 := sq_nonneg x3
  rcases phi_cases x0 h0 c0 with ⟨k0, f0⟩ | ⟨k0, k0', f0, g0⟩ | ⟨k0, f0⟩ <;>
  rcases phi_cases x1 h1 c1 with ⟨k1, f1⟩ | ⟨k1, k1', f1, g1⟩ | ⟨k1, f1⟩ <;>
  rcases phi_cases x2 h2 c2 with ⟨k2, f2⟩ | ⟨k2, k2', f2, g2⟩ | ⟨k2, f2⟩ <;>
  rcases phi_cases x3 h3 c3 with ⟨k3, f3⟩ | ⟨k3, k3', f3, g3⟩ | ⟨k3, f3⟩ <;>
  linarith

/-- For two columns `a ⊥ b` with `‖b‖ = 1`: `(140/99) Σᵢ |aᵢ| bᵢ² ≤ Σᵢ |aᵢ| |bᵢ|`.
(`zᵢ = aᵢ bᵢ` has zero sum, so `‖z‖₁² ≥ 2‖z‖₂²`; and `Σ |aᵢ| bᵢ² = Σ |zᵢ| |bᵢ| ≤ ‖z‖₂` by Cauchy–Schwarz.) -/
theorem pair_bound (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ) (hab : a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 = 0)
    (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 = 1) :
    140 / 99 * (|a0| * b0 ^ 2 + |a1| * b1 ^ 2 + |a2| * b2 ^ 2 + |a3| * b3 ^ 2) ≤
      |a0| * |b0| + |a1| * |b1| + |a2| * |b2| + |a3| * |b3| := by
  set z0 := a0 * b0; set z1 := a1 * b1; set z2 := a2 * b2; set z3 := a3 * b3
  have pz : ∀ u v : ℝ, 0 ≤ |u| * |v| + u * v := fun u v => by
    have := neg_le_abs (u * v); rw [abs_mul] at this; linarith
  -- zero sum: ‖z‖₁² ≥ 2 ‖z‖₂²
  have hX : 2 * (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2) ≤ (|z0| + |z1| + |z2| + |z3|) ^ 2 := by
    have h2 : (z0 + z1 + z2 + z3) ^ 2 = 0 := by rw [hab]; ring
    nlinarith [pz z0 z1, pz z0 z2, pz z0 z3, pz z1 z2, pz z1 z3, pz z2 z3, sq_abs z0, sq_abs z1,
      sq_abs z2, sq_abs z3]
  -- Cauchy–Schwarz
  have hY : (|z0| * |b0| + |z1| * |b1| + |z2| * |b2| + |z3| * |b3|) ^ 2 ≤ z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 := by
    have e : (|z0| * |b0| + |z1| * |b1| + |z2| * |b2| + |z3| * |b3|) ^ 2 +
        ((|z0| * |b1| - |z1| * |b0|) ^ 2 + (|z0| * |b2| - |z2| * |b0|) ^ 2 + (|z0| * |b3| - |z3| * |b0|) ^ 2 +
         (|z1| * |b2| - |z2| * |b1|) ^ 2 + (|z1| * |b3| - |z3| * |b1|) ^ 2 + (|z2| * |b3| - |z3| * |b2|) ^ 2)
        = (|z0| ^ 2 + |z1| ^ 2 + |z2| ^ 2 + |z3| ^ 2) * (|b0| ^ 2 + |b1| ^ 2 + |b2| ^ 2 + |b3| ^ 2) := by ring
    simp only [sq_abs] at e
    rw [hb, mul_one] at e
    nlinarith [sq_nonneg (|z0| * |b1| - |z1| * |b0|), sq_nonneg (|z0| * |b2| - |z2| * |b0|),
      sq_nonneg (|z0| * |b3| - |z3| * |b0|), sq_nonneg (|z1| * |b2| - |z2| * |b1|),
      sq_nonneg (|z1| * |b3| - |z3| * |b1|), sq_nonneg (|z2| * |b3| - |z3| * |b2|)]
  have ez : ∀ (a b : ℝ), |a * b| * |b| = |a| * b ^ 2 := fun a b => by rw [abs_mul, mul_assoc, abs_mul_abs_self, sq]
  have ez' : ∀ (a b : ℝ), |a * b| = |a| * |b| := fun a b => abs_mul a b
  rw [ez, ez, ez, ez] at hY
  rw [ez', ez', ez', ez'] at hX
  set Y := |a0| * b0 ^ 2 + |a1| * b1 ^ 2 + |a2| * b2 ^ 2 + |a3| * b3 ^ 2
  set X := |a0| * |b0| + |a1| * |b1| + |a2| * |b2| + |a3| * |b3|
  have hY0 : 0 ≤ Y := by positivity
  have hX0 : 0 ≤ X := by positivity
  nlinarith

/-- **Away from the axes.** If every entry of column `j` has square at most `2/3`, then `F_j ≤ 1`. -/
theorem far_core (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 e0 e1 e2 e3 : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1)
    (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 + c3 ^ 2 = 1)
    (he : e0 ^ 2 + e1 ^ 2 + e2 ^ 2 + e3 ^ 2 = 1)
    (hab : a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 = 0) (hac : a0 * c0 + a1 * c1 + a2 * c2 + a3 * c3 = 0)
    (hae : a0 * e0 + a1 * e1 + a2 * e2 + a3 * e3 = 0)
    (r0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 + e0 ^ 2 = 1) (r1 : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 + e1 ^ 2 = 1)
    (r2 : a2 ^ 2 + b2 ^ 2 + c2 ^ 2 + e2 ^ 2 = 1) (r3 : a3 ^ 2 + b3 ^ 2 + c3 ^ 2 + e3 ^ 2 = 1)
    (f0 : a0 ^ 2 ≤ 2 / 3) (f1 : a1 ^ 2 ≤ 2 / 3) (f2 : a2 ^ 2 ≤ 2 / 3) (f3 : a3 ^ 2 ≤ 2 / 3) :
    |a0| * (2 - (|a0| + |b0| + |c0| + |e0|)) + |a1| * (2 - (|a1| + |b1| + |c1| + |e1|)) +
      |a2| * (2 - (|a2| + |b2| + |c2| + |e2|)) + |a3| * (2 - (|a3| + |b3| + |c3| + |e3|)) ≤ 1 := by
  have pb := pair_bound a0 a1 a2 a3 b0 b1 b2 b3 hab hb
  have pc := pair_bound a0 a1 a2 a3 c0 c1 c2 c3 hac hc
  have pe := pair_bound a0 a1 a2 a3 e0 e1 e2 e3 hae he
  have hp := far_poly |a0| |a1| |a2| |a3| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (by simp only [sq_abs]; exact ha) (by rw [sq_abs]; exact f0) (by rw [sq_abs]; exact f1)
    (by rw [sq_abs]; exact f2) (by rw [sq_abs]; exact f3)
  simp only [phi] at hp
  have w : ∀ (x b c e : ℝ), x ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 = 1 →
      |x| * b ^ 2 + |x| * c ^ 2 + |x| * e ^ 2 = |x| - |x| ^ 3 := fun x b c e h => by
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
    rw [this]; linear_combination |x| * h
  have w0 := w a0 b0 c0 e0 r0; have w1 := w a1 b1 c1 e1 r1
  have w2 := w a2 b2 c2 e2 r2; have w3 := w a3 b3 c3 e3 r3
  have s0 := sq_abs a0; have s1 := sq_abs a1; have s2 := sq_abs a2; have s3 := sq_abs a3
  linarith


theorem far4 (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : R * Rᵀ = 1) (j : Fin 4) (hf : ∀ i, R i j ^ 2 ≤ 2 / 3) :
    Fcol R j ≤ 1 := by
  have hR' : Rᵀ * R = 1 := mul_eq_one_comm.mp hR
  have row : ∀ i, R i 0 ^ 2 + R i 1 ^ 2 + R i 2 ^ 2 + R i 3 ^ 2 = 1 := fun i => by
    have h := congrFun (congrFun hR i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, Matrix.one_apply_eq] at h
    linear_combination h
  have col : ∀ a b, R 0 a * R 0 b + R 1 a * R 1 b + R 2 a * R 2 b + R 3 a * R 3 b = if a = b then 1 else 0 :=
    fun a b => by
      have h := congrFun (congrFun hR' a) b
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, Matrix.one_apply] at h
      exact h
  have c00 := col 0 0; have c11 := col 1 1; have c22 := col 2 2; have c33 := col 3 3
  have c01 := col 0 1; have c02 := col 0 2; have c03 := col 0 3
  have c12 := col 1 2; have c13 := col 1 3; have c23 := col 2 3
  simp only [Fin.reduceEq, ↓reduceIte] at c00 c11 c22 c33 c01 c02 c03 c12 c13 c23
  have r0 := row 0; have r1 := row 1; have r2 := row 2; have r3 := row 3
  have hf0 := hf 0; have hf1 := hf 1; have hf2 := hf 2; have hf3 := hf 3
  simp only [Fcol, rowL1, l1, Fin.sum_univ_four]
  fin_cases j
  · have := far_core (R 0 0) (R 1 0) (R 2 0) (R 3 0) (R 0 1) (R 1 1) (R 2 1) (R 3 1)
      (R 0 2) (R 1 2) (R 2 2) (R 3 2) (R 0 3) (R 1 3) (R 2 3) (R 3 3)
      (by linear_combination c00) (by linear_combination c11) (by linear_combination c22)
      (by linear_combination c33) c01 c02 c03 r0 r1 r2 r3 hf0 hf1 hf2 hf3
    simp only [Fin.zero_eta, Fin.isValue]; linarith
  · have := far_core (R 0 1) (R 1 1) (R 2 1) (R 3 1) (R 0 0) (R 1 0) (R 2 0) (R 3 0)
      (R 0 2) (R 1 2) (R 2 2) (R 3 2) (R 0 3) (R 1 3) (R 2 3) (R 3 3)
      (by linear_combination c11) (by linear_combination c00) (by linear_combination c22)
      (by linear_combination c33) (by linear_combination c01) c12 c13
      (by linear_combination r0) (by linear_combination r1) (by linear_combination r2)
      (by linear_combination r3) hf0 hf1 hf2 hf3
    simp only [Fin.mk_one, Fin.isValue]; linarith
  · have := far_core (R 0 2) (R 1 2) (R 2 2) (R 3 2) (R 0 0) (R 1 0) (R 2 0) (R 3 0)
      (R 0 1) (R 1 1) (R 2 1) (R 3 1) (R 0 3) (R 1 3) (R 2 3) (R 3 3)
      (by linear_combination c22) (by linear_combination c00) (by linear_combination c11)
      (by linear_combination c33) (by linear_combination c02) (by linear_combination c12) c23
      (by linear_combination r0) (by linear_combination r1) (by linear_combination r2)
      (by linear_combination r3) hf0 hf1 hf2 hf3
    simp only [Fin.reduceFinMk, Fin.isValue]; linarith
  · have := far_core (R 0 3) (R 1 3) (R 2 3) (R 3 3) (R 0 0) (R 1 0) (R 2 0) (R 3 0)
      (R 0 1) (R 1 1) (R 2 1) (R 3 1) (R 0 2) (R 1 2) (R 2 2) (R 3 2)
      (by linear_combination c33) (by linear_combination c00) (by linear_combination c11)
      (by linear_combination c22) (by linear_combination c03) (by linear_combination c13)
      (by linear_combination c23)
      (by linear_combination r0) (by linear_combination r1) (by linear_combination r2)
      (by linear_combination r3) hf0 hf1 hf2 hf3
    simp only [Fin.reduceFinMk, Fin.isValue]; linarith

/-- **Lemma F in dimension 4.** For every orthogonal 4×4 matrix and every column `j`,
`Σᵢ |Rᵢⱼ| (2 - ‖row i‖₁) ≤ 1`. -/
theorem lemmaF4 : LemmaF 4 := by
  intro R hR j
  by_cases h : ∃ i, 2 / 3 ≤ R i j ^ 2
  · obtain ⟨i₀, hi⟩ := h
    exact near4 R hR i₀ j hi
  · push Not at h
    exact far4 R hR j fun i => (h i).le

end PackingOptimality.LemmaF4
