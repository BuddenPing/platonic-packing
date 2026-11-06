import Mathlib

/-!
# Packings of congruent convex bodies and the volume lower bound

A packing of `n` congruent copies of `K` in the scaled container `s • C` places each copy by an affine
isometry (rotations, reflections and translations are all allowed, so a lower bound proved here holds a
fortiori for the catalogue's rotation-only packings), keeps every copy inside `s • C`, and requires distinct
copies to have disjoint interiors (touching is allowed).
-/

namespace PackingOptimality

open MeasureTheory Set Module
open scoped Pointwise ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `n` congruent copies of `K` packed in `s • C`. -/
structure Packing (K C : Set E) (s : ℝ) (n : ℕ) where
  g : Fin n → E ≃ᵃⁱ[ℝ] E
  inside : ∀ i, g i '' K ⊆ s • C
  disjoint : Pairwise fun i j => Disjoint (interior (g i '' K)) (interior (g j '' K))

/-- Affine isometries of a finite-dimensional real inner product space preserve Lebesgue measure. -/
theorem affineIsometry_measurePreserving (g : E ≃ᵃⁱ[ℝ] E) : MeasurePreserving g volume volume := by
  have hlin : MeasurePreserving g.linearIsometryEquiv volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have htr : MeasurePreserving (fun x : E => x + g 0) volume volume :=
    measurePreserving_add_right volume (g 0)
  have hdecomp : (g : E → E) = (fun x : E => x + g 0) ∘ g.linearIsometryEquiv := by
    funext x
    have := g.toAffineEquiv.toAffineMap.decomp
    have h2 := congrFun this x
    simp only [Function.comp_apply]
    rw [show g x = g.toAffineEquiv.toAffineMap x from rfl, h2]
    simp [add_comm]
  rw [hdecomp]
  exact htr.comp hlin

theorem volume_image_affineIsometry (g : E ≃ᵃⁱ[ℝ] E) (S : Set E) : volume (g '' S) = volume S := by
  have h := (affineIsometry_measurePreserving g)
  have e : g '' S = g.toHomeomorph.toMeasurableEquiv '' S := rfl
  rw [e, MeasurableEquiv.image_eq_preimage_symm]
  exact (h.symm g.toHomeomorph.toMeasurableEquiv).measure_preimage_equiv S

end PackingOptimality

namespace PackingOptimality

open MeasureTheory Set Module
open scoped Pointwise ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A convex set and its interior have the same volume (its frontier is null). -/
theorem volume_interior_of_convex {S : Set E} (hS : Convex ℝ S) : volume (interior S) = volume S := by
  apply le_antisymm (measure_mono interior_subset)
  calc volume S ≤ volume (interior S ∪ frontier S) := by
        apply measure_mono
        intro x hx
        have : x ∈ closure S := subset_closure hx
        rw [closure_eq_interior_union_frontier] at this
        exact this
    _ ≤ volume (interior S) + volume (frontier S) := measure_union_le _ _
    _ = volume (interior S) := by rw [hS.addHaar_frontier volume, add_zero]

/-- **Volume bound.** `n` congruent copies of a convex body `K` with pairwise disjoint interiors inside
`s • C` have total volume at most `|s|^d · vol C`. -/
theorem card_mul_volume_le {K C : Set E} {s : ℝ} {n : ℕ} (hK : Convex ℝ K) (P : Packing K C s n) :
    (n : ℝ≥0∞) * volume K ≤ ENNReal.ofReal (|s ^ finrank ℝ E|) * volume C := by
  have hconv : ∀ i, Convex ℝ (P.g i '' K) := fun i =>
    hK.affine_image (P.g i).toAffineEquiv.toAffineMap
  have hvol : ∀ i, volume (interior (P.g i '' K)) = volume K := fun i => by
    rw [volume_interior_of_convex (hconv i), volume_image_affineIsometry]
  calc (n : ℝ≥0∞) * volume K = ∑ i : Fin n, volume (interior (P.g i '' K)) := by
        simp [hvol]
    _ = volume (⋃ i, interior (P.g i '' K)) := by
        rw [measure_iUnion (fun i j hij => P.disjoint hij) (fun i => isOpen_interior.measurableSet),
          tsum_fintype]
    _ ≤ volume (s • C) := measure_mono (iUnion_subset fun i => interior_subset.trans (P.inside i))
    _ = ENNReal.ofReal (|s ^ finrank ℝ E|) * volume C := Measure.addHaar_smul volume s C

/-- **Self-packing bound.** If `K` is a convex body (positive, finite volume), `n` congruent copies of `K`
fit in `s • K` only if `n ≤ |s|^d`. -/
theorem card_le_of_packing_self {K : Set E} {s : ℝ} {n : ℕ} (hK : Convex ℝ K)
    (hpos : 0 < volume K) (hfin : volume K < ∞) (P : Packing K K s n) :
    (n : ℝ) ≤ |s| ^ finrank ℝ E := by
  have h := card_mul_volume_le hK P
  have hne : volume K ≠ 0 := hpos.ne'
  have hle : (n : ℝ≥0∞) ≤ ENNReal.ofReal (|s ^ finrank ℝ E|) :=
    (ENNReal.mul_le_mul_iff_left hne hfin.ne).mp h
  have hle' : ENNReal.ofReal (n : ℝ) ≤ ENNReal.ofReal (|s ^ finrank ℝ E|) := by
    simpa using hle
  have := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp hle'
  simpa [abs_pow] using this

end PackingOptimality

namespace PackingOptimality

open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A packing of `n` copies restricts to a packing of any `m ≤ n` of them: `s(m) ≤ s(n)`. -/
def Packing.restrict {K C : Set E} {s : ℝ} {n m : ℕ} (P : Packing K C s n) (h : m ≤ n) :
    Packing K C s m where
  g := fun i => P.g (Fin.castLE h i)
  inside := fun i => P.inside _
  disjoint := fun i j hij => P.disjoint fun h' => hij (Fin.castLE_injective h h')

/-- **Common-point lemma.** If every congruent copy of `K` inside `s • C` contains the point `c` in its
interior, two copies cannot be packed in `s • C` (so `s(n) > s` for every `n ≥ 2`). -/
theorem no_packing_two_of_common_point {K C : Set E} {s : ℝ} (c : E)
    (h : ∀ g : E ≃ᵃⁱ[ℝ] E, g '' K ⊆ s • C → c ∈ interior (g '' K)) {n : ℕ} (hn : 2 ≤ n) :
    Packing K C s n → False := by
  intro P
  have P2 := P.restrict hn
  have h0 := h (P2.g 0) (P2.inside 0)
  have h1 := h (P2.g 1) (P2.inside 1)
  exact Set.disjoint_left.mp (P2.disjoint (by decide : (0 : Fin 2) ≠ 1)) h0 h1

end PackingOptimality
