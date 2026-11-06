import PackingOptimality.Cubes

/-!
# The cube centre lemma in dimension 3

For an orthogonal 3×3 matrix with columns `a, b, c`:
`2 (|a₀| + |a₁| + |a₂| - 1) ≤ Σᵢ |aᵢ| (|bᵢ| + |cᵢ|)`. Equivalently (`Σᵢ aᵢ² = 1`),
`Σᵢ |aᵢ| (2 - (|aᵢ| + |bᵢ| + |cᵢ|)) ≤ 1`: the box of feasible centres of a unit cube inside a cube of side 2
lies in the cube's own body, so a unit cube inside a cube of side less than 2 contains the centre.

Proof: (1) with a zero entry in `b` or `c` the inequality is an identity,
`2 [(1 - P)(1 - Q) + P (1 - S)(1 - T)] ≥ 0`; (2) in general, rotate `(b, c)` in its plane by a unit vector
`(p, q)`; the right side is a continuous function on the unit circle with a minimiser, and the minimiser has
a zero entry: otherwise all signs are constant near it, the right side is linear in `(p, q)` there, and the
two nearby points `(p ∓ t q, q ± t p) / √(1 + t²)` would average below the minimum.
-/

namespace PackingOptimality.CubeCentre

theorem pqst (P Q S T : ℝ) (hP : 0 ≤ P) (_hQ : 0 ≤ Q) (_hS : 0 ≤ S) (_hT : 0 ≤ T)
    (hPQ : P ^ 2 + Q ^ 2 = 1) (hST : S ^ 2 + T ^ 2 = 1) :
    2 * (P * S + P * T + Q - 1) ≤ P * S * (Q * S + T) + P * T * (Q * T + S) + Q * P := by
  have hP1 : P ≤ 1 := by nlinarith only [hPQ, sq_nonneg Q, sq_nonneg (P - 1)]
  have hQ1 : Q ≤ 1 := by nlinarith only [hPQ, sq_nonneg P, sq_nonneg (Q - 1)]
  have hS1 : S ≤ 1 := by nlinarith only [hST, sq_nonneg T, sq_nonneg (S - 1)]
  have hT1 : T ≤ 1 := by nlinarith only [hST, sq_nonneg S, sq_nonneg (T - 1)]
  have k1 : 0 ≤ (1 - P) * (1 - Q) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ P * ((1 - S) * (1 - T)) := mul_nonneg hP (mul_nonneg (by linarith) (by linarith))
  have key : P * S * (Q * S + T) + P * T * (Q * T + S) + Q * P - 2 * (P * S + P * T + Q - 1)
      = 2 * ((1 - P) * (1 - Q)) + 2 * (P * ((1 - S) * (1 - T))) := by
    linear_combination (P * Q) * hST
  linarith

/-- Step 1: the inequality when `c₂ = 0`. -/
theorem reduced (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1)
    (_hab : a0 * b0 + a1 * b1 + a2 * b2 = 0) (hac : a0 * c0 + a1 * c1 + a2 * c2 = 0)
    (hbc : b0 * c0 + b1 * c1 + b2 * c2 = 0)
    (_hr0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 = 1) (_hr1 : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 1)
    (hr2 : a2 ^ 2 + b2 ^ 2 + c2 ^ 2 = 1) (h : c2 = 0) :
    2 * (|a0| + |a1| + |a2| - 1) ≤ |a0| * (|b0| + |c0|) + |a1| * (|b1| + |c1|) + |a2| * (|b2| + |c2|) := by
  subst h
  have hc' : c0 ^ 2 + c1 ^ 2 = 1 := by linear_combination hc
  have hac' : a0 * c0 + a1 * c1 = 0 := by linear_combination hac
  have hbc' : b0 * c0 + b1 * c1 = 0 := by linear_combination hbc
  obtain ⟨l, hl⟩ : ∃ l, l = a1 * c0 - a0 * c1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = b1 * c0 - b0 * c1 := ⟨_, rfl⟩
  have ea0 : a0 = -l * c1 := by linear_combination c0 * hac' - a0 * hc' + c1 * hl
  have ea1 : a1 = l * c0 := by linear_combination c1 * hac' - a1 * hc' - c0 * hl
  have eb0 : b0 = -m * c1 := by linear_combination c0 * hbc' - b0 * hc' + c1 * hm
  have eb1 : b1 = m * c0 := by linear_combination c1 * hbc' - b1 * hc' - c0 * hm
  have e : a0 ^ 2 + a1 ^ 2 = l ^ 2 := by rw [ea0, ea1]; linear_combination l ^ 2 * hc'
  have e' : b0 ^ 2 + b1 ^ 2 = m ^ 2 := by rw [eb0, eb1]; linear_combination m ^ 2 * hc'
  have hl2 : l ^ 2 = b2 ^ 2 := by linear_combination -e + ha - hr2
  have hm2 : m ^ 2 = a2 ^ 2 := by linear_combination -e' + hb - hr2
  have al : |l| = |b2| := (sq_eq_sq_iff_abs_eq_abs l b2).mp hl2
  have am : |m| = |a2| := (sq_eq_sq_iff_abs_eq_abs m a2).mp hm2
  have xa0 : |a0| = |b2| * |c1| := by rw [ea0, abs_mul, abs_neg, al]
  have xa1 : |a1| = |b2| * |c0| := by rw [ea1, abs_mul, al]
  have xb0 : |b0| = |a2| * |c1| := by rw [eb0, abs_mul, abs_neg, am]
  have xb1 : |b1| = |a2| * |c0| := by rw [eb1, abs_mul, am]
  rw [xa0, xa1, xb0, xb1, abs_zero, add_zero]
  have hPQ : |b2| ^ 2 + |a2| ^ 2 = 1 := by rw [sq_abs, sq_abs]; linear_combination hr2
  have hST : |c1| ^ 2 + |c0| ^ 2 = 1 := by rw [sq_abs, sq_abs]; linear_combination hc'
  have := pqst |b2| |a2| |c1| |c0| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hPQ hST
  linarith

/-- Step 1': the inequality when `b` or `c` has a zero entry (permute rows, swap `b` and `c`). -/
theorem zero_case (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1)
    (hab : a0 * b0 + a1 * b1 + a2 * b2 = 0) (hac : a0 * c0 + a1 * c1 + a2 * c2 = 0)
    (hbc : b0 * c0 + b1 * c1 + b2 * c2 = 0)
    (hr0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 = 1) (hr1 : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 1)
    (hr2 : a2 ^ 2 + b2 ^ 2 + c2 ^ 2 = 1)
    (h : b0 = 0 ∨ b1 = 0 ∨ b2 = 0 ∨ c0 = 0 ∨ c1 = 0 ∨ c2 = 0) :
    2 * (|a0| + |a1| + |a2| - 1) ≤ |a0| * (|b0| + |c0|) + |a1| * (|b1| + |c1|) + |a2| * (|b2| + |c2|) := by
  rcases h with h | h | h | h | h | h
  · have := reduced a2 a1 a0 c2 c1 c0 b2 b1 b0 (by linear_combination ha) (by linear_combination hc)
      (by linear_combination hb) (by linear_combination hac) (by linear_combination hab)
      (by linear_combination hbc) (by linear_combination hr2) (by linear_combination hr1)
      (by linear_combination hr0) h
    linarith
  · have := reduced a0 a2 a1 c0 c2 c1 b0 b2 b1 (by linear_combination ha) (by linear_combination hc)
      (by linear_combination hb) (by linear_combination hac) (by linear_combination hab)
      (by linear_combination hbc) (by linear_combination hr0) (by linear_combination hr2)
      (by linear_combination hr1) h
    linarith
  · have := reduced a0 a1 a2 c0 c1 c2 b0 b1 b2 (by linear_combination ha) (by linear_combination hc)
      (by linear_combination hb) (by linear_combination hac) (by linear_combination hab)
      (by linear_combination hbc) (by linear_combination hr0) (by linear_combination hr1)
      (by linear_combination hr2) h
    linarith
  · have := reduced a2 a1 a0 b2 b1 b0 c2 c1 c0 (by linear_combination ha) (by linear_combination hb)
      (by linear_combination hc) (by linear_combination hab) (by linear_combination hac)
      (by linear_combination hbc) (by linear_combination hr2) (by linear_combination hr1)
      (by linear_combination hr0) h
    linarith
  · have := reduced a0 a2 a1 b0 b2 b1 c0 c2 c1 (by linear_combination ha) (by linear_combination hb)
      (by linear_combination hc) (by linear_combination hab) (by linear_combination hac)
      (by linear_combination hbc) (by linear_combination hr0) (by linear_combination hr2)
      (by linear_combination hr1) h
    linarith
  · exact reduced a0 a1 a2 b0 b1 b2 c0 c1 c2 ha hb hc hab hac hbc hr0 hr1 hr2 h


/-- `|B| + |C|` for the rotated pair `B = p b + q c`, `C = p c - q b` of row entries. -/
def T (p q b c : ℝ) : ℝ := |p * b + q * c| + |p * c - q * b|

theorem T_nonneg (p q b c : ℝ) : 0 ≤ T p q b c := by unfold T; positivity

theorem T_hom (l p q b c : ℝ) (hl : 0 ≤ l) : T (l * p) (l * q) b c = l * T p q b c := by
  unfold T
  rw [show l * p * b + l * q * c = l * (p * b + q * c) by ring,
    show l * p * c - l * q * b = l * (p * c - q * b) by ring, abs_mul, abs_mul, abs_of_nonneg hl]
  ring

theorem abs_pm (x u : ℝ) (h : |u| ≤ |x|) : |x + u| + |x - u| = 2 * |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h ⊢
    obtain ⟨h1, h2⟩ := abs_le.mp h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
  · rw [abs_of_nonpos hx] at h ⊢
    obtain ⟨h1, h2⟩ := abs_le.mp h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring

/-- Away from a zero entry, `T` is linear: the two rotated neighbours average to the centre. -/
theorem T_pair (p q b c t : ℝ) (ht : 0 ≤ t) (h1 : t * |p * c - q * b| ≤ |p * b + q * c|)
    (h2 : t * |p * b + q * c| ≤ |p * c - q * b|) :
    T (p - t * q) (q + t * p) b c + T (p + t * q) (q - t * p) b c = 2 * T p q b c := by
  unfold T
  rw [show (p - t * q) * b + (q + t * p) * c = (p * b + q * c) + t * (p * c - q * b) by ring,
    show (p - t * q) * c - (q + t * p) * b = (p * c - q * b) - t * (p * b + q * c) by ring,
    show (p + t * q) * b + (q - t * p) * c = (p * b + q * c) - t * (p * c - q * b) by ring,
    show (p + t * q) * c - (q - t * p) * b = (p * c - q * b) + t * (p * b + q * c) by ring]
  have e1 := abs_pm (p * b + q * c) (t * (p * c - q * b)) (by rwa [abs_mul, abs_of_nonneg ht])
  have e2 := abs_pm (p * c - q * b) (t * (p * b + q * c)) (by rwa [abs_mul, abs_of_nonneg ht])
  linarith

/-- The right side of the inequality for the frame `(a, p b + q c, p c - q b)`. -/
def Phi (a0 a1 a2 b0 b1 b2 c0 c1 c2 p q : ℝ) : ℝ :=
  |a0| * T p q b0 c0 + |a1| * T p q b1 c1 + |a2| * T p q b2 c2

theorem abs_le_one_of_sq (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : |y| ≤ 1 :=
  (sq_le_one_iff_abs_le_one y).mp (by nlinarith only [h, sq_nonneg x, sq_nonneg z])

theorem abs_le_one_of_sq' (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : |z| ≤ 1 :=
  (sq_le_one_iff_abs_le_one z).mp (by nlinarith only [h, sq_nonneg x, sq_nonneg y])

/-- **The core inequality.** For an orthogonal matrix with columns `a, b, c`,
`2 (Σᵢ |aᵢ| - 1) ≤ Σᵢ |aᵢ| (|bᵢ| + |cᵢ|)`. -/
theorem core (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1)
    (hab : a0 * b0 + a1 * b1 + a2 * b2 = 0) (hac : a0 * c0 + a1 * c1 + a2 * c2 = 0)
    (hbc : b0 * c0 + b1 * c1 + b2 * c2 = 0)
    (hr0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 = 1) (hr1 : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 1)
    (hr2 : a2 ^ 2 + b2 ^ 2 + c2 ^ 2 = 1) :
    2 * (|a0| + |a1| + |a2| - 1) ≤ |a0| * (|b0| + |c0|) + |a1| * (|b1| + |c1|) + |a2| * (|b2| + |c2|) := by
  let f : ℝ × ℝ → ℝ := fun y => Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 y.1 y.2
  let S : Set (ℝ × ℝ) := {y | y.1 ^ 2 + y.2 ^ 2 = 1}
  have hS : IsCompact S := by
    have hclosed : IsClosed S := isClosed_eq (by fun_prop) continuous_const
    refine ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
      hclosed ?_
    intro y hy
    have hy : y.1 ^ 2 + y.2 ^ 2 = 1 := hy
    have h1 : |y.1| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp (by nlinarith only [hy, sq_nonneg y.2])
    have h2 : |y.2| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp (by nlinarith only [hy, sq_nonneg y.1])
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hcont : ContinuousOn f S := by
    apply Continuous.continuousOn
    simp only [f, Phi, T]
    fun_prop
  obtain ⟨z, hzS, hmin⟩ := hS.exists_isMinOn ⟨(1, 0), by simp [S]⟩ hcont
  have h10 : f (1, 0) = |a0| * (|b0| + |c0|) + |a1| * (|b1| + |c1|) + |a2| * (|b2| + |c2|) := by
    simp [f, Phi, T]
  rw [← h10]
  refine le_trans ?_ (isMinOn_iff.mp hmin (1, 0) (by simp [S]))
  obtain ⟨p, q⟩ := z
  have hz : p ^ 2 + q ^ 2 = 1 := hzS
  -- the rotated frame is orthonormal
  have fB : (p * b0 + q * c0) ^ 2 + (p * b1 + q * c1) ^ 2 + (p * b2 + q * c2) ^ 2 = 1 := by
    linear_combination p ^ 2 * hb + 2 * p * q * hbc + q ^ 2 * hc + hz
  have fC : (p * c0 - q * b0) ^ 2 + (p * c1 - q * b1) ^ 2 + (p * c2 - q * b2) ^ 2 = 1 := by
    linear_combination p ^ 2 * hc - 2 * p * q * hbc + q ^ 2 * hb + hz
  have faB : a0 * (p * b0 + q * c0) + a1 * (p * b1 + q * c1) + a2 * (p * b2 + q * c2) = 0 := by
    linear_combination p * hab + q * hac
  have faC : a0 * (p * c0 - q * b0) + a1 * (p * c1 - q * b1) + a2 * (p * c2 - q * b2) = 0 := by
    linear_combination p * hac - q * hab
  have fBC : (p * b0 + q * c0) * (p * c0 - q * b0) + (p * b1 + q * c1) * (p * c1 - q * b1)
      + (p * b2 + q * c2) * (p * c2 - q * b2) = 0 := by
    linear_combination (p ^ 2 - q ^ 2) * hbc + p * q * hc - p * q * hb
  have f0 : a0 ^ 2 + (p * b0 + q * c0) ^ 2 + (p * c0 - q * b0) ^ 2 = 1 := by
    linear_combination hr0 + (b0 ^ 2 + c0 ^ 2) * hz
  have f1 : a1 ^ 2 + (p * b1 + q * c1) ^ 2 + (p * c1 - q * b1) ^ 2 = 1 := by
    linear_combination hr1 + (b1 ^ 2 + c1 ^ 2) * hz
  have f2 : a2 ^ 2 + (p * b2 + q * c2) ^ 2 + (p * c2 - q * b2) ^ 2 = 1 := by
    linear_combination hr2 + (b2 ^ 2 + c2 ^ 2) * hz
  show _ ≤ Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 p q
  by_cases hzero : p * b0 + q * c0 = 0 ∨ p * b1 + q * c1 = 0 ∨ p * b2 + q * c2 = 0 ∨
      p * c0 - q * b0 = 0 ∨ p * c1 - q * b1 = 0 ∨ p * c2 - q * b2 = 0
  · exact zero_case a0 a1 a2 _ _ _ _ _ _ ha fB fC faB faC fBC f0 f1 f2 hzero
  exfalso
  push Not at hzero
  obtain ⟨n0, n1, n2, m0, m1, m2⟩ := hzero
  -- a step `t > 0` small enough that no entry changes sign
  set t := min (min (min |p * b0 + q * c0| |p * b1 + q * c1|) (min |p * b2 + q * c2| |p * c0 - q * b0|))
    (min |p * c1 - q * b1| |p * c2 - q * b2|) with ht_def
  have ht : 0 < t := by
    simp only [ht_def, lt_min_iff, abs_pos]; exact ⟨⟨⟨n0, n1⟩, ⟨n2, m0⟩⟩, ⟨m1, m2⟩⟩
  have tB0 : t ≤ |p * b0 + q * c0| := by simp [ht_def]
  have tB1 : t ≤ |p * b1 + q * c1| := by simp [ht_def]
  have tB2 : t ≤ |p * b2 + q * c2| := by simp [ht_def]
  have tC0 : t ≤ |p * c0 - q * b0| := by simp [ht_def]
  have tC1 : t ≤ |p * c1 - q * b1| := by simp [ht_def]
  have tC2 : t ≤ |p * c2 - q * b2| := by simp [ht_def]
  have small : ∀ x y : ℝ, |x| ≤ 1 → t ≤ |y| → t * |x| ≤ |y| := fun x y hx hy => by
    have := mul_le_mul_of_nonneg_left hx ht.le; linarith
  have P0 := T_pair p q b0 c0 t ht.le (small _ _ (abs_le_one_of_sq' _ _ _ f0) tB0)
    (small _ _ (abs_le_one_of_sq _ _ _ f0) tC0)
  have P1 := T_pair p q b1 c1 t ht.le (small _ _ (abs_le_one_of_sq' _ _ _ f1) tB1)
    (small _ _ (abs_le_one_of_sq _ _ _ f1) tC1)
  have P2 := T_pair p q b2 c2 t ht.le (small _ _ (abs_le_one_of_sq' _ _ _ f2) tB2)
    (small _ _ (abs_le_one_of_sq _ _ _ f2) tC2)
  set F := Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 p q with hF
  set Fp := Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 (p - t * q) (q + t * p) with hFp
  set Fm := Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 (p + t * q) (q - t * p) with hFm
  have hsum : Fp + Fm = 2 * F := by
    simp only [hF, hFp, hFm, Phi]
    linear_combination |a0| * P0 + |a1| * P1 + |a2| * P2
  -- the neighbours, scaled back to the circle
  set r := Real.sqrt (1 + t ^ 2) with hr
  have hr2 : r ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hr1 : 1 < r := by rw [hr, Real.lt_sqrt zero_le_one]; have := pow_pos ht 2; linarith
  have hri : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hri0 : 0 ≤ r⁻¹ := inv_nonneg.mpr (by linarith)
  have scaled : ∀ u v : ℝ, u ^ 2 + v ^ 2 = 1 + t ^ 2 →
      F ≤ r⁻¹ * Phi a0 a1 a2 b0 b1 b2 c0 c1 c2 u v := by
    intro u v huv
    have hmem : (r⁻¹ * u, r⁻¹ * v) ∈ S := by
      show (r⁻¹ * u) ^ 2 + (r⁻¹ * v) ^ 2 = 1
      rw [mul_pow, mul_pow, ← mul_add, huv, inv_pow, hr2, inv_mul_cancel₀ (by positivity)]
    have := isMinOn_iff.mp hmin _ hmem
    simp only [f, Phi, T_hom _ _ _ _ _ hri0] at this
    rw [hF]
    simp only [Phi]
    linear_combination this
  have sp := scaled (p - t * q) (q + t * p) (by linear_combination (1 + t ^ 2) * hz)
  have sm := scaled (p + t * q) (q - t * p) (by linear_combination (1 + t ^ 2) * hz)
  -- the value at the minimiser is positive
  have Fpos : 0 < F := by
    have T0 : 0 < T p q b0 c0 := by unfold T; have := abs_pos.mpr n0; positivity
    have T1 : 0 < T p q b1 c1 := by unfold T; have := abs_pos.mpr n1; positivity
    have T2 : 0 < T p q b2 c2 := by unfold T; have := abs_pos.mpr n2; positivity
    have g0 := mul_nonneg (abs_nonneg a0) (T_nonneg p q b0 c0)
    have g1 := mul_nonneg (abs_nonneg a1) (T_nonneg p q b1 c1)
    have g2 := mul_nonneg (abs_nonneg a2) (T_nonneg p q b2 c2)
    by_cases h0 : a0 = 0
    · by_cases h1 : a1 = 0
      · have h2 : a2 ≠ 0 := by rintro rfl; subst h0; subst h1; norm_num at ha
        have := mul_pos (abs_pos.mpr h2) T2; simp only [hF, Phi]; linarith
      · have := mul_pos (abs_pos.mpr h1) T1; simp only [hF, Phi]; linarith
    · have := mul_pos (abs_pos.mpr h0) T0; simp only [hF, Phi]; linarith
  have key : r⁻¹ * Fp + r⁻¹ * Fm = 2 * (r⁻¹ * F) := by rw [← mul_add, hsum]; ring
  have := mul_lt_of_lt_one_left Fpos hri
  linarith


/-- The bound for one column: with `|dᵢ| ≤ (s - wᵢ)/2` (`wᵢ` the `i`-th row sum of `|entries|`) and `s < 2`,
`|Σᵢ aᵢ dᵢ| < 1/2`. -/
theorem col_bound (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 = 1) (hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 1)
    (hab : a0 * b0 + a1 * b1 + a2 * b2 = 0) (hac : a0 * c0 + a1 * c1 + a2 * c2 = 0)
    (hbc : b0 * c0 + b1 * c1 + b2 * c2 = 0)
    (hr0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 = 1) (hr1 : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 1)
    (hr2 : a2 ^ 2 + b2 ^ 2 + c2 ^ 2 = 1) {s : ℝ} (hs : s < 2) (d0 d1 d2 : ℝ)
    (h0 : |d0| ≤ (s - (|a0| + |b0| + |c0|)) / 2) (h1 : |d1| ≤ (s - (|a1| + |b1| + |c1|)) / 2)
    (h2 : |d2| ≤ (s - (|a2| + |b2| + |c2|)) / 2) :
    |a0 * d0 + a1 * d1 + a2 * d2| < 1 / 2 := by
  have hcore := core a0 a1 a2 b0 b1 b2 c0 c1 c2 ha hb hc hab hac hbc hr0 hr1 hr2
  have hsq : |a0| ^ 2 + |a1| ^ 2 + |a2| ^ 2 = 1 := by rw [sq_abs, sq_abs, sq_abs]; exact ha
  have hpos : 0 < |a0| + |a1| + |a2| := by
    by_contra hneg
    push Not at hneg
    nlinarith only [hneg, abs_nonneg a0, abs_nonneg a1, abs_nonneg a2, hsq]
  have tri : |a0 * d0 + a1 * d1 + a2 * d2| ≤ |a0| * |d0| + |a1| * |d1| + |a2| * |d2| := by
    calc |a0 * d0 + a1 * d1 + a2 * d2| ≤ |a0 * d0 + a1 * d1| + |a2 * d2| := abs_add_le _ _
      _ ≤ |a0 * d0| + |a1 * d1| + |a2 * d2| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul]
  have m0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg a0)
  have m1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg a1)
  have m2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg a2)
  have hgap : 0 < (2 - s) * (|a0| + |a1| + |a2|) := mul_pos (by linarith) hpos
  linarith

/-! ## From the matrix inequality to the centre of the container -/

open scoped RealInnerProductSpace Pointwise
open Set

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The standard basis vector `e_k`. -/
noncomputable def e (k : Fin 3) : E3 := EuclideanSpace.single k 1

/-- The matrix entry `(L e_k)_i` of a linear isometry. -/
noncomputable def mat (L : E3 ≃ₗᵢ[ℝ] E3) (i k : Fin 3) : ℝ := L (e k) i

theorem inner3 (u v : E3) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_e (u : E3) (k : Fin 3) : ⟪u, e k⟫ = u k := by
  rw [inner3]; fin_cases k <;> simp [e]

theorem inner_ee (j k : Fin 3) : ⟪e j, e k⟫ = if j = k then 1 else 0 := by
  rw [inner3]; fin_cases j <;> fin_cases k <;> simp [e]

theorem decomp (x : E3) : x = x 0 • e 0 + x 1 • e 1 + x 2 • e 2 := by
  ext i; fin_cases i <;> simp [e]

theorem mat_apply (L : E3 ≃ₗᵢ[ℝ] E3) (x : E3) (i : Fin 3) :
    L x i = mat L i 0 * x 0 + mat L i 1 * x 1 + mat L i 2 * x 2 := by
  conv_lhs => rw [decomp x]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mat]
  ring

theorem mat_symm_apply (L : E3 ≃ₗᵢ[ℝ] E3) (y : E3) (k : Fin 3) :
    L.symm y k = mat L 0 k * y 0 + mat L 1 k * y 1 + mat L 2 k * y 2 := by
  rw [← inner_e (L.symm y) k, ← L.inner_map_map, L.apply_symm_apply, inner3]
  simp only [mat]; ring

theorem col (L : E3 ≃ₗᵢ[ℝ] E3) (j k : Fin 3) :
    mat L 0 j * mat L 0 k + mat L 1 j * mat L 1 k + mat L 2 j * mat L 2 k = if j = k then 1 else 0 := by
  have h := L.inner_map_map (e j) (e k)
  rw [inner3, inner_ee] at h
  simp only [mat]; exact h

theorem row (L : E3 ≃ₗᵢ[ℝ] E3) (i : Fin 3) : mat L i 0 ^ 2 + mat L i 1 ^ 2 + mat L i 2 ^ 2 = 1 := by
  have hsym : ∀ k, L.symm (e i) k = mat L i k := by
    intro k; rw [mat_symm_apply]; fin_cases i <;> simp [e]
  have h := L.symm.inner_map_map (e i) (e i)
  rw [inner3, hsym, hsym, hsym, inner_ee, if_pos rfl] at h
  linear_combination h

theorem pos_part (a : ℝ) : a * (if 0 ≤ a then 1 else 0) = (a + |a|) / 2 := by
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (not_le.mp h)]; ring

theorem neg_part (a : ℝ) : a * (if 0 ≤ a then 0 else 1) = (a - |a|) / 2 := by
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (not_le.mp h)]; ring

theorem smul_cube_coord {s : ℝ} (hs : 0 ≤ s) {y : E3} (hy : y ∈ s • cube 3) (i : Fin 3) :
    0 ≤ y i ∧ y i ≤ s := by
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact ⟨mul_nonneg hs (hx i).1, mul_le_of_le_one_right hs (hx i).2⟩

/-- **The cube centre lemma, d = 3.** A unit cube placed by any rigid motion inside a cube `[0, s]³` with
`s < 2` contains the centre `(s/2, s/2, s/2)` in its interior. -/
theorem centre3 (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2) (g : E3 ≃ᵃⁱ[ℝ] E3) (hg : g '' cube 3 ⊆ s • cube 3) :
    (s / 2) • WithLp.toLp 2 (fun _ => (1 : ℝ)) ∈ interior (g '' cube 3) := by
  set L := g.linearIsometryEquiv with hLdef
  set m : E3 := (s / 2) • WithLp.toLp 2 (fun _ => (1 : ℝ)) with hm
  have hgx : ∀ x, g x = L x + g 0 := fun x => by have := g.map_vadd 0 x; simpa using this
  -- each coordinate of the image of a point of the cube lies in `[0, s]`
  have vert : ∀ t : Fin 3 → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) → ∀ i,
      0 ≤ mat L i 0 * t 0 + mat L i 1 * t 1 + mat L i 2 * t 2 + g 0 i ∧
      mat L i 0 * t 0 + mat L i 1 * t 1 + mat L i 2 * t 2 + g 0 i ≤ s := by
    intro t ht i
    have hmem : g (WithLp.toLp 2 t) ∈ s • cube 3 := hg ⟨_, fun k => by simpa using ht k, rfl⟩
    have := smul_cube_coord hs0 hmem i
    rw [hgx, PiLp.add_apply, mat_apply] at this
    simpa using this
  -- the two extreme vertices in direction `i`: the image's centre is within `(s - wᵢ)/2` of `s/2`
  have bnd : ∀ i, |s / 2 - (g 0 i + (mat L i 0 + mat L i 1 + mat L i 2) / 2)| ≤
      (s - (|mat L i 0| + |mat L i 1| + |mat L i 2|)) / 2 := by
    intro i
    have up := (vert (fun k => if 0 ≤ mat L i k then 1 else 0) (fun k => by split_ifs <;> norm_num) i).2
    have lo := (vert (fun k => if 0 ≤ mat L i k then 0 else 1) (fun k => by split_ifs <;> norm_num) i).1
    simp only [pos_part, neg_part] at up lo
    rw [abs_le]; constructor <;> linarith
  -- the preimage of the centre
  obtain ⟨x, hx⟩ : ∃ x, x = g.symm m := ⟨_, rfl⟩
  have hgxm : g x = m := by rw [hx]; exact g.apply_symm_apply m
  have hLx : L x = m - g 0 := by rw [← hgxm, hgx x, add_sub_cancel_right]
  have hxk : ∀ k, x k = mat L 0 k * (s / 2 - g 0 0) + mat L 1 k * (s / 2 - g 0 1) +
      mat L 2 k * (s / 2 - g 0 2) := by
    intro k
    have h1 : x = L.symm (m - g 0) := by rw [← hLx, L.symm_apply_apply]
    rw [h1, mat_symm_apply]
    simp [hm]
  have c00 := col L 0 0; have c01 := col L 0 1; have c02 := col L 0 2
  have c10 := col L 1 0; have c11 := col L 1 1; have c12 := col L 1 2
  have c20 := col L 2 0; have c21 := col L 2 1; have c22 := col L 2 2
  simp only [Fin.reduceEq, ↓reduceIte] at c00 c01 c02 c10 c11 c12 c20 c21 c22
  have r0 := row L 0; have r1 := row L 1; have r2 := row L 2
  set d0 := s / 2 - (g 0 0 + (mat L 0 0 + mat L 0 1 + mat L 0 2) / 2) with hd0
  set d1 := s / 2 - (g 0 1 + (mat L 1 0 + mat L 1 1 + mat L 1 2) / 2) with hd1
  set d2 := s / 2 - (g 0 2 + (mat L 2 0 + mat L 2 1 + mat L 2 2) / 2) with hd2
  have b0 := bnd 0; have b1 := bnd 1; have b2 := bnd 2
  have k0 : |x 0 - 1 / 2| < 1 / 2 := by
    rw [show x 0 - 1 / 2 = mat L 0 0 * d0 + mat L 1 0 * d1 + mat L 2 0 * d2 by
      rw [hxk 0, hd0, hd1, hd2]; linear_combination (1 / 2 : ℝ) * c00 + (1 / 2 : ℝ) * c01 + (1 / 2 : ℝ) * c02]
    exact col_bound _ _ _ _ _ _ _ _ _ (by linear_combination c00) (by linear_combination c11)
      (by linear_combination c22) c01 c02 c12 r0 r1 r2 hs d0 d1 d2 b0 b1 b2
  have k1 : |x 1 - 1 / 2| < 1 / 2 := by
    rw [show x 1 - 1 / 2 = mat L 0 1 * d0 + mat L 1 1 * d1 + mat L 2 1 * d2 by
      rw [hxk 1, hd0, hd1, hd2]; linear_combination (1 / 2 : ℝ) * c10 + (1 / 2 : ℝ) * c11 + (1 / 2 : ℝ) * c12]
    exact col_bound _ _ _ _ _ _ _ _ _ (by linear_combination c11) (by linear_combination c00)
      (by linear_combination c22) c10 c12 c02 (by linear_combination r0) (by linear_combination r1)
      (by linear_combination r2) hs d0 d1 d2 (by linarith) (by linarith) (by linarith)
  have k2 : |x 2 - 1 / 2| < 1 / 2 := by
    rw [show x 2 - 1 / 2 = mat L 0 2 * d0 + mat L 1 2 * d1 + mat L 2 2 * d2 by
      rw [hxk 2, hd0, hd1, hd2]; linear_combination (1 / 2 : ℝ) * c20 + (1 / 2 : ℝ) * c21 + (1 / 2 : ℝ) * c22]
    exact col_bound _ _ _ _ _ _ _ _ _ (by linear_combination c22) (by linear_combination c00)
      (by linear_combination c11) c20 c21 c01 (by linear_combination r0) (by linear_combination r1)
      (by linear_combination r2) hs d0 d1 d2 (by linarith) (by linarith) (by linarith)
  have hU : ∀ k, 0 < x k ∧ x k < 1 := by
    have key : ∀ k : Fin 3, |x k - 1 / 2| < 1 / 2 := by
      intro k; fin_cases k
      exacts [k0, k1, k2]
    intro k
    obtain ⟨h1, h2⟩ := abs_lt.mp (key k)
    exact ⟨by linarith, by linarith⟩
  -- the open cube maps onto an open set inside the image, containing the centre
  let U : Set E3 := {y | ∀ k, 0 < y k ∧ y k < 1}
  have hUo : IsOpen U := by
    have : U = ⋂ i, ((fun y : E3 => y i) ⁻¹' Ioo 0 1) := by ext y; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
  have himg : IsOpen (g '' U) := by simpa using g.toHomeomorph.isOpenMap U hUo
  have hsub : g '' U ⊆ g '' cube 3 := image_mono fun y hy k => ⟨(hy k).1.le, (hy k).2.le⟩
  exact interior_maximal hsub himg ⟨x, hU, hgxm⟩

end PackingOptimality.CubeCentre

namespace PackingOptimality

open Set
open scoped Pointwise

/-- **Cubes in a cube, n = 2, ..., 8: side 2 is optimal.** With the proven cube centre lemma in dimension 3,
any two unit cubes in a cube of side `s < 2` would both contain the centre in their interiors. -/
theorem cubincub_plateau {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 8) :
    Nonempty (Packing (cube 3) (cube 3) 2 n) ∧ ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s n → 2 ≤ s :=
  cube_plateau_of_centre_lemma (d := 3) (by norm_num) CubeCentre.centre3 hn2 hn

theorem cubincub_n02 : Nonempty (Packing (cube 3) (cube 3) 2 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 2 → 2 ≤ s := cubincub_plateau le_rfl (by norm_num)
theorem cubincub_n03 : Nonempty (Packing (cube 3) (cube 3) 2 3) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 3 → 2 ≤ s := cubincub_plateau (by norm_num) (by norm_num)
theorem cubincub_n04 : Nonempty (Packing (cube 3) (cube 3) 2 4) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 4 → 2 ≤ s := cubincub_plateau (by norm_num) (by norm_num)
theorem cubincub_n05 : Nonempty (Packing (cube 3) (cube 3) 2 5) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 5 → 2 ≤ s := cubincub_plateau (by norm_num) (by norm_num)
theorem cubincub_n06 : Nonempty (Packing (cube 3) (cube 3) 2 6) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 6 → 2 ≤ s := cubincub_plateau (by norm_num) (by norm_num)
theorem cubincub_n07 : Nonempty (Packing (cube 3) (cube 3) 2 7) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 3) (cube 3) s 7 → 2 ≤ s := cubincub_plateau (by norm_num) (by norm_num)

end PackingOptimality
