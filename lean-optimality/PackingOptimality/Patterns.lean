import PackingOptimality.Basic
import PackingOptimality.Cubes

/-!
# Pattern mechanisms of the catalogue, formalized

General constructions behind recurring patterns in the catalogue, stated for congruent copies of a body `K` in a
scaled container `s • C` in any finite-dimensional real inner product space.

* **Deletion** (`Packing.restrict`, `Basic.lean`): any `m ≤ n` pieces of an `n`-packing form an `m`-packing, so
  `s(m) ≤ s(n)`. This covers the catalogue's monotone repairs and "N minus one piece" records, and is the first
  step of PingYou's subset relaxation (N19 → N6, N8).
* **Scale monotonicity** (`Packing.mono`): for a convex container containing the origin, a packing at scale `s`
  is one at every larger scale.
* **Composition** (`Packing.compose`): `n` copies of `Q` in `s • C` and `m` copies of `P` in `t • Q` give `n m`
  copies of `P` in `(s t) • C`. With `P = Q = C` this is the recursion `s(n m) ≤ s(n) s(m)`
  (`Packing.selfCompose`), and its powers `s(nᵏ) ≤ s(n)ᵏ` (`Packing.pow`): PingYou's 16 = 4² and 64 = 4³
  triakis tetrahedra at `(5/3)²` and `(5/3)³`, and the cube grids `k³` at scale `k`.
* **Voronoi windows** (`voronoi_disjoint`, `voronoi_packing`, `lattice_window`): bodies lying in the Voronoi
  cells of distinct points have disjoint interiors. A finite window of a lattice tiling, or of any point set
  whose Voronoi cells contain the pieces, is therefore a packing as soon as each piece fits in the container. This
  covers cube grids, Cartesian shells (56 truncated cubes), FCC shells and windows (19 and 44 rhombic
  dodecahedra), column arrays of prisms and two-orientation windows on a diamond-type point set.
-/

namespace PackingOptimality

open Set
open scoped Pointwise RealInnerProductSpace

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem affine_apply_eq (g : E ≃ᵃⁱ[ℝ] E) (x : E) : g x = g.linearIsometryEquiv x + g 0 := by
  have := g.map_vadd 0 x; simpa using this

/-- The conjugate of an affine isometry by the dilation `x ↦ t x`: same linear part, translation `t • g 0`. -/
noncomputable def dil (t : ℝ) (g : E ≃ᵃⁱ[ℝ] E) : E ≃ᵃⁱ[ℝ] E :=
  g.linearIsometryEquiv.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ E (t • g 0))

theorem dil_apply (t : ℝ) (g : E ≃ᵃⁱ[ℝ] E) (x : E) : dil t g x = t • g 0 + g.linearIsometryEquiv x := rfl

theorem dil_smul (t : ℝ) (g : E ≃ᵃⁱ[ℝ] E) (y : E) : dil t g (t • y) = t • g y := by
  rw [dil_apply, map_smul, affine_apply_eq g y, smul_add, add_comm]

theorem dil_image_smul (t : ℝ) (g : E ≃ᵃⁱ[ℝ] E) (A : Set E) : dil t g '' (t • A) = t • (g '' A) := by
  ext x; constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨g a, ⟨a, ha, rfl⟩, (dil_smul t g a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨t • a, ⟨a, ha, rfl⟩, dil_smul t g a⟩

theorem interior_image_disjoint (f : E ≃ᵃⁱ[ℝ] E) {A B : Set E} (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (f '' A)) (interior (f '' B)) := by
  have hA : interior (f '' A) = f '' interior A := (f.toHomeomorph.image_interior A).symm
  have hB : interior (f '' B) = f '' interior B := (f.toHomeomorph.image_interior B).symm
  rw [hA, hB]; exact (Set.disjoint_image_iff f.injective).mpr h

/-- **Scale monotonicity.** For a convex container containing the origin, `s ≤ t` turns an `s`-packing into a
`t`-packing. -/
def Packing.mono {K C : Set E} {s t : ℝ} {n : ℕ} (P : Packing K C s n) (hC : Convex ℝ C) (h0 : (0 : E) ∈ C)
    (hs : 0 ≤ s) (hst : s ≤ t) : Packing K C t n where
  g := P.g
  inside := fun i => (P.inside i).trans (by
    rintro _ ⟨c, hc, rfl⟩
    rcases hs.lt_or_eq with hs' | hs'
    · have ht : 0 < t := lt_of_lt_of_le hs' hst
      refine ⟨(s / t) • c, ?_, by show t • ((s / t) • c) = s • c; rw [smul_smul, mul_div_cancel₀ _ ht.ne']⟩
      have := hC.smul_mem_of_zero_mem h0 hc ⟨div_nonneg hs ht.le, (div_le_one ht).mpr hst⟩
      exact this
    · subst hs'; exact ⟨0, h0, by simp⟩)
  disjoint := P.disjoint

/-- **Composition.** `n` copies of `Q` in `s • C` and `m` copies of `P` in `t • Q` give `n * m` copies of `P` in
`(s * t) • C`: put a copy of the `m`-packing (scaled by `t`) inside each copy of `Q`. -/
noncomputable def Packing.compose {P Q C : Set E} {s t : ℝ} {n m : ℕ} (A : Packing Q C s n)
    (B : Packing P Q t m) (ht : t ≠ 0) : Packing P C (s * t) (n * m) where
  g k := (B.g (finProdFinEquiv.symm k).2).trans (dil t (A.g (finProdFinEquiv.symm k).1))
  inside k := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq, hqy⟩ := B.inside _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hcq⟩ := A.inside (finProdFinEquiv.symm k).1 ⟨q, hq, rfl⟩
    refine ⟨c, hc, ?_⟩
    simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply]
    rw [← hqy, dil_smul, ← hcq, smul_smul, mul_comm]
  disjoint k k' hkk' := by
    set i := (finProdFinEquiv.symm k).1; set j := (finProdFinEquiv.symm k).2
    set i' := (finProdFinEquiv.symm k').1; set j' := (finProdFinEquiv.symm k').2
    have himg : ∀ (a : Fin n) (b : Fin m), ((B.g b).trans (dil t (A.g a))) '' P = dil t (A.g a) '' (B.g b '' P) := by
      intro a b; rw [AffineIsometryEquiv.coe_trans, Set.image_comp]
    simp only [himg]
    by_cases hi : i = i'
    · have hj : j ≠ j' := by
        intro hj; apply hkk'
        apply finProdFinEquiv.symm.injective
        exact Prod.ext hi hj
      rw [← hi]
      exact interior_image_disjoint _ (B.disjoint hj)
    · have sub : ∀ (a : Fin n) (b : Fin m), dil t (A.g a) '' (B.g b '' P) ⊆ t • (A.g a '' Q) := by
        intro a b
        rw [← dil_image_smul]; exact Set.image_mono (B.inside b)
      refine Disjoint.mono (interior_mono (sub i j)) (interior_mono (sub i' j')) ?_
      rw [interior_smul₀ ht, interior_smul₀ ht, ← Set.image_smul, ← Set.image_smul]
      exact (Set.disjoint_image_iff (smul_right_injective E ht)).mpr (A.disjoint hi)

/-- **Recursion.** `s(n m) ≤ s(n) s(m)` when the piece is the container. -/
noncomputable def Packing.selfCompose {K : Set E} {s t : ℝ} {n m : ℕ} (A : Packing K K s n) (B : Packing K K t m)
    (ht : t ≠ 0) : Packing K K (s * t) (n * m) := A.compose B ht

/-- One piece: the identity placement. -/
noncomputable def Packing.one (K : Set E) : Packing K K 1 1 where
  g _ := AffineIsometryEquiv.refl ℝ E
  inside _ := by simp
  disjoint i j hij := absurd (Subsingleton.elim i j) hij

/-- **Powers.** `s(nᵏ) ≤ s(n)ᵏ` when the piece is the container. -/
noncomputable def Packing.pow {K : Set E} {s : ℝ} {n : ℕ} (A : Packing K K s n) (hs : s ≠ 0) :
    ∀ k : ℕ, Packing K K (s ^ k) (n ^ k)
  | 0 => by simpa using Packing.one K
  | k + 1 => by
    have h := (Packing.pow A hs k).selfCompose A hs
    rw [← pow_succ, ← pow_succ] at h
    exact h

/-! ## Voronoi windows -/

/-- Two sets on the two sides of the bisector of `p ≠ q` (each point at least as close to its own centre) have
disjoint interiors. -/
theorem voronoi_disjoint {p q : E} (hpq : p ≠ q) {A B : Set E} (hA : ∀ x ∈ A, ‖x - p‖ ≤ ‖x - q‖)
    (hB : ∀ x ∈ B, ‖x - q‖ ≤ ‖x - p‖) : Disjoint (interior A) (interior B) := by
  have hv : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  let f : E →L[ℝ] ℝ := innerSL ℝ (q - p)
  have hf : Function.Surjective f := by
    intro t
    refine ⟨(t / ‖q - p‖ ^ 2) • (q - p), ?_⟩
    simp only [f, innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq]
    have : ‖q - p‖ ^ 2 ≠ 0 := by positivity
    field_simp
  have e : ∀ x, f x = ⟪x, q⟫ - ⟪x, p⟫ := fun x => by
    show ⟪q - p, x⟫ = _
    rw [inner_sub_left, real_inner_comm q x, real_inner_comm p x]
  have key : ∀ x, ‖x - p‖ ≤ ‖x - q‖ ↔ f x ≤ (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
    intro x
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real, e]
    constructor <;> intro h <;> linarith
  apply interior_disjoint_of_separated f hf (c := (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2)
  · intro x hx; exact (key x).mp (hA x hx)
  · intro x hx
    show (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 ≤ f x
    have h := hB x hx
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real] at h
    rw [e]; linarith

/-- **Voronoi packing.** Copies `g i '' K` lying in the Voronoi cells of distinct centres `c i`, and inside
`s • C`, form a packing. -/
noncomputable def voronoi_packing {K C : Set E} {s : ℝ} {n : ℕ} (g : Fin n → E ≃ᵃⁱ[ℝ] E) (c : Fin n → E)
    (hc : Function.Injective c) (hvor : ∀ i j, ∀ x ∈ g i '' K, ‖x - c i‖ ≤ ‖x - c j‖)
    (hin : ∀ i, g i '' K ⊆ s • C) : Packing K C s n where
  g := g
  inside := hin
  disjoint i j hij := voronoi_disjoint (hc.ne hij) (hvor i j) (hvor j i)

/-- **Lattice windows.** If `K` lies in the Voronoi cell at `0` of an additive subgroup `Λ`, the translates of
`K` by distinct points of `Λ` that fit in `s • C` form a packing. -/
noncomputable def lattice_window {K C : Set E} {s : ℝ} {n : ℕ} (Λ : AddSubgroup E)
    (hK : ∀ x ∈ K, ∀ v ∈ Λ, ‖x‖ ≤ ‖x - v‖) (p : Fin n → E) (hp : Function.Injective p) (hpΛ : ∀ i, p i ∈ Λ)
    (hin : ∀ i, ∀ x ∈ K, p i + x ∈ s • C) : Packing K C s n :=
  voronoi_packing (fun i => AffineIsometryEquiv.constVAdd ℝ E (p i)) p hp
    (by
      rintro i j _ ⟨x, hx, rfl⟩
      show ‖p i + x - p i‖ ≤ ‖p i + x - p j‖
      have := hK x hx (p j - p i) (Λ.sub_mem (hpΛ j) (hpΛ i))
      simpa [add_sub_cancel_left, sub_sub_eq_add_sub, add_comm, add_sub_assoc] using this)
    (by rintro i _ ⟨x, hx, rfl⟩; exact hin i x hx)

/-! ## Separator certificates (PingYou's F step) -/

/-- **Separator certificates.** Placements inside `s • C` such that every pair is split by a hyperplane (a
nonzero functional `f i j` with `g i '' K ≤ c i j ≤ g j '' K`) form a packing. This is the soundness of the
fixed-orientation step F: an LP solution with one separating axis per pair is a packing. -/
noncomputable def Packing.of_separators {K C : Set E} {s : ℝ} {n : ℕ} (g : Fin n → E ≃ᵃⁱ[ℝ] E)
    (hin : ∀ i, g i '' K ⊆ s • C) (f : Fin n → Fin n → E →L[ℝ] ℝ) (hf : ∀ i j, i ≠ j → Function.Surjective (f i j))
    (c : Fin n → Fin n → ℝ) (hlo : ∀ i j, i < j → ∀ y ∈ K, f i j (g i y) ≤ c i j)
    (hhi : ∀ i j, i < j → ∀ y ∈ K, c i j ≤ f i j (g j y)) : Packing K C s n where
  g := g
  inside := hin
  disjoint i j hij := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact interior_disjoint_of_separated (f i j) (hf i j hij) (c := c i j)
        (by rintro _ ⟨y, hy, rfl⟩; exact hlo i j h y hy) (by rintro _ ⟨y, hy, rfl⟩; exact hhi i j h y hy)
    · exact (interior_disjoint_of_separated (f j i) (hf j i (Ne.symm hij)) (c := c j i)
        (by rintro _ ⟨y, hy, rfl⟩; exact hlo j i h y hy) (by rintro _ ⟨y, hy, rfl⟩; exact hhi j i h y hy)).symm

/-- **Common rescaling.** A packing of `K` in `s • C` is one of `b • K` in `s • (b • C)`. -/
noncomputable def Packing.smulBoth {K C : Set E} {s : ℝ} {n : ℕ} (P : Packing K C s n) (b : ℝ) (hb : b ≠ 0) :
    Packing (b • K) (b • C) s n where
  g i := dil b (P.g i)
  inside i := by
    rw [dil_image_smul]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := P.inside i hy
    exact ⟨b • c, ⟨c, hc, rfl⟩, by show s • b • c = b • s • c; rw [smul_smul, smul_smul, mul_comm]⟩
  disjoint i j hij := by
    show Disjoint (interior (dil b (P.g i) '' (b • K))) (interior (dil b (P.g j) '' (b • K)))
    rw [dil_image_smul, dil_image_smul, interior_smul₀ hb, interior_smul₀ hb, ← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective E hb)).mpr (P.disjoint hij)

end PackingOptimality
