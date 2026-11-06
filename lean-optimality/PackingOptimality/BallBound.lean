import PackingOptimality.Basic
import PackingOptimality.CentreGeneral

/-!
# The two-ball lemma

If the piece contains the closed ball of radius `k` about the origin, its image contains the ball of radius `k`
about `p = g 0`. Since that ball lies in the container, `p` is close to the container's centre, and when `‖p‖ < k`
the centre is inside the piece.

* **Hypercube** `[-s/2, s/2]^d`: the ball gives `|pᵢ| + k ≤ s/2`, so `‖p‖² ≤ d (s/2 - k)²`.
  This is `< k²` when `s < 2k (1 + 1/√d)`.
* **Cross-polytope** `{‖x‖₁ ≤ S}`: the ball gives `‖p‖₁ + k √d ≤ S`, and `‖p‖ ≤ ‖p‖₁`. Stated with `√d` passed as
  `t` with `t² = d`.
-/

namespace PackingOptimality.BallBound

open Set CentreGeneral
open scoped Pointwise RealInnerProductSpace

variable {d : ℕ}

/-- The centred unit hypercube. -/
def boxC (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, |x i| ≤ 1 / 2}

theorem coord_of_mem_smul_box {s : ℝ} (hs : 0 ≤ s) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s • boxC d)
    (i : Fin d) : |x i| ≤ s / 2 := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs]
  nlinarith [hy i]

theorem mem_smul_box_of_coord {s : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin d)} (hx : ∀ i, |x i| ≤ s / 2) :
    x ∈ s • boxC d := by
  refine ⟨s⁻¹ • x, fun i => ?_, by simp [smul_smul, hs.ne']⟩
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  rw [inv_mul_le_iff₀ hs]; linarith [hx i]

theorem norm_sq_sum (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_sum]; simp [sq]

/-- The point `p ± k eᵢ` is the image of `±k L⁻¹ eᵢ`, a point of norm `k`. -/
theorem image_dir (g : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) :
    g (g.linearIsometryEquiv.symm u) = u + g 0 := by
  have := g.map_vadd 0 (g.linearIsometryEquiv.symm u); simpa using this

theorem interior_of_near (g : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) {K : Set _} {k : ℝ}
    (hK : ∀ y, ‖y‖ ≤ k → y ∈ K) (hp : ‖g 0‖ < k) : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior (g '' K) := by
  let U : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 k
  have himg : IsOpen (g '' U) := by simpa using g.toHomeomorph.isOpenMap U Metric.isOpen_ball
  have hsub : g '' U ⊆ g '' K := image_mono fun y hy => hK y (le_of_lt (by simpa [U] using hy))
  refine interior_maximal hsub himg ⟨g.linearIsometryEquiv.symm (-g 0), ?_, ?_⟩
  · simp [U, norm_neg, hp]
  · rw [image_dir]; simp

/-- **Two-ball lemma, hypercube container.** -/
theorem centre_ball_box (K : Set (EuclideanSpace ℝ (Fin d))) {k s t : ℝ} (hk : 0 < k) (hd : 0 < d) (ht : 0 < t)
    (htd : t ^ 2 = d) (hK : ∀ y, ‖y‖ ≤ k → y ∈ K) (hs0 : 0 ≤ s) (hs : t * (s / 2 - k) < k)
    (g : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) (hg : g '' K ⊆ s • boxC d) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior (g '' K) := by
  have side : ∀ i, |g 0 i| + k ≤ s / 2 := by
    intro i
    have mem : ∀ c : ℝ, |c| ≤ k → EuclideanSpace.single i c + g 0 ∈ s • boxC d := fun c hc => by
      rw [← image_dir]
      refine hg ⟨_, hK _ ?_, rfl⟩
      rw [LinearIsometryEquiv.norm_map]; simpa using hc
    have h1 := coord_of_mem_smul_box hs0 (mem k (by rw [abs_of_pos hk])) i
    have h2 := coord_of_mem_smul_box hs0 (mem (-k) (by rw [abs_neg, abs_of_pos hk])) i
    simp [PiLp.add_apply, PiLp.single_apply] at h1 h2
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp h2
    rcases le_total 0 (g 0 i) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  apply interior_of_near g hK
  have hnn : 0 ≤ s / 2 - k := by have := side ⟨0, hd⟩; linarith [abs_nonneg (g 0 ⟨0, hd⟩)]
  have hsq : ‖g 0‖ ^ 2 < k ^ 2 := by
    rw [norm_sq_sum]
    calc ∑ i, g 0 i ^ 2 ≤ ∑ _i : Fin d, (s / 2 - k) ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          have := side i
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      _ = (t * (s / 2 - k)) ^ 2 := by simp [mul_pow, htd]
      _ < k ^ 2 := by nlinarith [mul_nonneg ht.le hnn]
  nlinarith [norm_nonneg (g 0)]

/-- The centred cross-polytope `{‖x‖₁ ≤ ρ}`. -/
def l1Ball (d : ℕ) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∑ i, |x i| ≤ ρ}

theorem l1_of_mem_smul {s ρ : ℝ} (hs : 0 ≤ s) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s • l1Ball d ρ) :
    ∑ i, |x i| ≤ s * ρ := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hs, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hy hs

theorem mem_smul_l1_of {s ρ : ℝ} (hs : 0 < s) {x : EuclideanSpace ℝ (Fin d)} (hx : ∑ i, |x i| ≤ s * ρ) :
    x ∈ s • l1Ball d ρ := by
  refine ⟨s⁻¹ • x, ?_, by simp [smul_smul, hs.ne']⟩
  show ∑ i, |(s⁻¹ • x) i| ≤ ρ
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hs), ← Finset.mul_sum]
  rw [inv_mul_le_iff₀ hs]; exact hx

theorem norm_le_l1 (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ≤ ∑ i, |x i| := by
  have h1 : ‖x‖ ^ 2 ≤ (∑ i, |x i|) ^ 2 := by
    rw [norm_sq_sum]
    calc ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp [sq_abs]
      _ ≤ (∑ i, |x i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _) two_ne_zero |>.mp h1

/-- **Two-ball lemma, cross-polytope container.** `t = √d`. -/
theorem centre_ball_l1 (K : Set (EuclideanSpace ℝ (Fin d))) {k s ρ t : ℝ} (hk : 0 < k) (ht : 0 < t)
    (htd : t ^ 2 = d) (hK : ∀ y, ‖y‖ ≤ k → y ∈ K) (hs0 : 0 ≤ s) (hs : s * ρ - k * t < k)
    (g : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) (hg : g '' K ⊆ s • l1Ball d ρ) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior (g '' K) := by
  obtain ⟨p, hp⟩ : ∃ p, p = g 0 := ⟨_, rfl⟩
  -- the point `p + (k/t) σ`, σ the sign vector of `p`, lies in the ball of radius `k` about `p`
  set σ : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => if 0 ≤ p i then (1 : ℝ) else -1)
  have hσ : ‖σ‖ = t := by
    have : ‖σ‖ ^ 2 = t ^ 2 := by
      rw [norm_sq_sum, htd]; simp only [σ]
      simp [apply_ite (fun x : ℝ => x ^ 2)]
    exact (pow_left_inj₀ (norm_nonneg _) ht.le two_ne_zero).mp this
  have hmem : (k / t) • σ + g 0 ∈ s • l1Ball d ρ := by
    rw [← image_dir]
    refine hg ⟨_, hK _ ?_, rfl⟩
    rw [LinearIsometryEquiv.norm_map, norm_smul, hσ, Real.norm_eq_abs, abs_of_pos (div_pos hk ht)]
    rw [div_mul_cancel₀ _ ht.ne']
  rw [← hp, add_comm] at hmem
  have h1 := l1_of_mem_smul hs0 hmem
  -- `Σ |pᵢ + (k/t) σᵢ| = Σ |pᵢ| + d k / t = Σ |pᵢ| + k t`
  have e : ∑ i, |(p + (k / t) • σ) i| = ∑ i, |p i| + k * t := by
    have : ∀ i, |(p + (k / t) • σ) i| = |p i| + k / t := fun i => by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, σ]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg (by positivity), abs_of_nonneg h]
      · push Not at h; rw [mul_neg_one, abs_of_neg (by have := div_pos hk ht; linarith), abs_of_neg h]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htd]; field_simp
  rw [e] at h1
  apply interior_of_near g hK
  have := norm_le_l1 p
  rw [← hp]; linarith

end PackingOptimality.BallBound
