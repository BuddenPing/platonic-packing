import PackingOptimality.Basic

/-!
# The facet-width lemma

Let the piece be `K = {y | ∀ j, 0 ≤ c j + ⟪a j, y⟫}`, a polytope given by its facet inequalities. Suppose every
facet `j` has a point `v j ∈ K` with `c j + ⟪a j, v j⟫ ≥ 1` (the opposite vertex). Then the piece's width in the
direction of `a j` is at least `W = 1 / max ‖a j‖`.

If the piece is placed inside `s • C`, with `C` inside the ball of radius `R` about the origin, and `s R < W`, then
the origin lies in the interior of the piece.

*Proof.* If the preimage `y*` of the origin satisfied every facet inequality strictly, it would lie in an open
subset of `K`. Otherwise some facet has `c j + ⟪a j, y*⟫ ≤ 0`. Then `⟪a j, v j - y*⟫ ≥ 1`, so
`‖v j - y*‖ ≥ W`. The image of `v j` is therefore at distance at least `W` from the origin, but it lies in
`s • C`, within distance `s R`.

Stated with squared norms (`W2 = W²`, `R2 = R²`) to keep square roots out of the hypotheses.
-/

namespace PackingOptimality.FacetWidth

open Set
open scoped Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem centre_of_facet_width {k : ℕ} (c : Fin k → ℝ) (a v : Fin k → E) {W2 R2 s : ℝ} {K C : Set E}
    (hK : K = {y | ∀ j, 0 ≤ c j + ⟪a j, y⟫}) (hv : ∀ j, v j ∈ K) (hv1 : ∀ j, 1 ≤ c j + ⟪a j, v j⟫)
    (ha : ∀ j, ‖a j‖ ^ 2 * W2 ≤ 1) (hC : ∀ x ∈ C, ‖x‖ ^ 2 ≤ R2) (hs0 : 0 ≤ s) (hs : s ^ 2 * R2 < W2)
    (g : E ≃ᵃⁱ[ℝ] E) (hg : g '' K ⊆ s • C) : (0 : E) ∈ interior (g '' K) := by
  obtain ⟨y, hy⟩ : ∃ y, y = g.symm 0 := ⟨_, rfl⟩
  have hgy : g y = 0 := by rw [hy]; exact g.apply_symm_apply 0
  by_cases h : ∀ j, 0 < c j + ⟪a j, y⟫
  · let U : Set E := {z | ∀ j, 0 < c j + ⟪a j, z⟫}
    have hUo : IsOpen U := by
      have : U = ⋂ j, {z | 0 < c j + ⟪a j, z⟫} := by ext z; simp [U]
      rw [this]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)
    have himg : IsOpen (g '' U) := by simpa using g.toHomeomorph.isOpenMap U hUo
    have hsub : g '' U ⊆ g '' K := image_mono fun z hz => by rw [hK]; exact fun j => (hz j).le
    exact interior_maximal hsub himg ⟨y, h, hgy⟩
  · exfalso
    push Not at h
    obtain ⟨j, hj⟩ := h
    have h1 : 1 ≤ ⟪a j, v j - y⟫ := by rw [inner_sub_right]; linarith [hv1 j]
    have h2 : ⟪a j, v j - y⟫ ≤ ‖a j‖ * ‖v j - y‖ := real_inner_le_norm _ _
    have hd : ‖g (v j)‖ = ‖v j - y‖ := by
      rw [← sub_zero (g (v j)), ← hgy, ← dist_eq_norm, ← dist_eq_norm, g.dist_map]
    obtain ⟨x, hx, hxe⟩ := Set.mem_smul_set.mp (hg ⟨v j, hv j, rfl⟩)
    have hn : ‖g (v j)‖ ^ 2 ≤ s ^ 2 * R2 := by
      rw [← hxe, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow]
      exact mul_le_mul_of_nonneg_left (hC x hx) (by positivity)
    have hsq : 1 ≤ ‖a j‖ ^ 2 * ‖v j - y‖ ^ 2 := by
      have := mul_le_mul h1 h1 zero_le_one (by linarith)
      nlinarith [norm_nonneg (a j), norm_nonneg (v j - y)]
    rw [hd] at hn
    have hW : W2 ≤ ‖v j - y‖ ^ 2 := by
      by_contra hlt
      push Not at hlt
      have := ha j
      nlinarith [sq_nonneg ‖a j‖, sq_nonneg ‖v j - y‖]
    linarith

end PackingOptimality.FacetWidth
