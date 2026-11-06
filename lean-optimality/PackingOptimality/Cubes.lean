import PackingOptimality.Basic

/-!
# Cubes in a cube: `k^d` unit cubes need a cube of side exactly `k`, in every dimension

Lower bound: the volume bound (`card_le_of_packing_self`). Upper bound: the grid of `k^d` translated unit
cubes, which touch along faces but have pairwise disjoint interiors.
-/

namespace PackingOptimality

open MeasureTheory Set Module
open scoped Pointwise ENNReal

/-- Interiors of two sets on opposite sides of a hyperplane `f = c` are disjoint. -/
theorem interior_disjoint_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E →L[ℝ] ℝ) (hf : Function.Surjective f) {A B : Set E} {c : ℝ}
    (hA : A ⊆ f ⁻¹' Iic c) (hB : B ⊆ f ⁻¹' Ici c) : Disjoint (interior A) (interior B) := by
  have hopen : IsOpenMap f := f.isOpenMap hf
  have h1 : interior A ⊆ f ⁻¹' Iio c := by
    calc interior A ⊆ interior (f ⁻¹' Iic c) := interior_mono hA
      _ = f ⁻¹' interior (Iic c) := (hopen.preimage_interior_eq_interior_preimage f.continuous _).symm
      _ = f ⁻¹' Iio c := by rw [interior_Iic]
  have h2 : interior B ⊆ f ⁻¹' Ioi c := by
    calc interior B ⊆ interior (f ⁻¹' Ici c) := interior_mono hB
      _ = f ⁻¹' interior (Ici c) := (hopen.preimage_interior_eq_interior_preimage f.continuous _).symm
      _ = f ⁻¹' Ioi c := by rw [interior_Ici]
  rw [Set.disjoint_left]
  intro x hxA hxB
  have h1x := h1 hxA
  have h2x := h2 hxB
  simp only [mem_preimage, mem_Iio, mem_Ioi] at h1x h2x
  linarith

variable {d : ℕ}

/-- The unit cube `[0,1]^d` in Euclidean `d`-space. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

theorem convex_cube : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

theorem cube_isBounded : Bornology.IsBounded (cube d) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt d, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have := hx i
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [this.1, this.2]
    _ = d := by simp

theorem volume_cube_lt_top : volume (cube d) < ∞ := cube_isBounded.measure_lt_top

theorem volume_cube_pos : 0 < volume (cube d) := by
  let U : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 < x i ∧ x i < 1}
  have hU : IsOpen U := by
    have : U = ⋂ i, ((fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Ioo 0 1) := by
      ext x; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
  have hne : U.Nonempty := ⟨WithLp.toLp 2 (fun _ => (1 : ℝ) / 2), fun i => by norm_num⟩
  calc 0 < volume U := hU.measure_pos volume hne
    _ ≤ volume (cube d) := measure_mono fun x hx i => ⟨(hx i).1.le, (hx i).2.le⟩

/-- The integer translation vector of a grid cell. -/
noncomputable def cell {k : ℕ} (v : Fin d → Fin k) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((v i : ℕ) : ℝ))

@[simp] theorem cell_apply {k : ℕ} (v : Fin d → Fin k) (i : Fin d) : cell v i = ((v i : ℕ) : ℝ) := rfl

/-- Translation by a grid cell, as an affine isometry. -/
noncomputable def cellMap {k : ℕ} (v : Fin d → Fin k) : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) (cell v)

theorem cellMap_apply {k : ℕ} (v : Fin d → Fin k) (x : EuclideanSpace ℝ (Fin d)) :
    cellMap v x = cell v + x := rfl

theorem mem_smul_cube {k : ℝ} (hk : 0 < k) {y : EuclideanSpace ℝ (Fin d)}
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ k) : y ∈ k • cube d := by
  refine ⟨k⁻¹ • y, fun i => ?_, ?_⟩
  · simp only [PiLp.smul_apply, smul_eq_mul]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hk.le) (hy i).1
    · rw [inv_mul_le_iff₀ hk]; simpa using (hy i).2
  · simp [smul_smul, hk.ne']

theorem cell_inside {k : ℕ} (hk : 0 < k) (v : Fin d → Fin k) :
    cellMap v '' cube d ⊆ (k : ℝ) • cube d := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_smul_cube (by exact_mod_cast hk)
  intro i
  have hxi := hx i
  have hv : ((v i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (v i).isLt
  have hv0 : (0 : ℝ) ≤ ((v i : ℕ) : ℝ) := by positivity
  rw [cellMap_apply, PiLp.add_apply, cell_apply]
  constructor <;> linarith [hxi.1, hxi.2]

theorem proj_surjective (i : Fin d) : Function.Surjective (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i) :=
  fun t => ⟨EuclideanSpace.single i t, by simp⟩

theorem cell_disjoint {k : ℕ} {v w : Fin d → Fin k} (h : v ≠ w) :
    Disjoint (interior (cellMap v '' cube d)) (interior (cellMap w '' cube d)) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ w i := Function.ne_iff.mp h
  have key : ∀ {v w : Fin d → Fin k} (i : Fin d), ((v i : ℕ) < (w i : ℕ)) →
      Disjoint (interior (cellMap v '' cube d)) (interior (cellMap w '' cube d)) := by
    intro v w i hlt
    have hle : ((v i : ℕ) : ℝ) + 1 ≤ ((w i : ℕ) : ℝ) := by exact_mod_cast hlt
    apply interior_disjoint_of_separated (EuclideanSpace.proj i) (proj_surjective i)
      (c := ((v i : ℕ) : ℝ) + 1)
    · rintro _ ⟨x, hx, rfl⟩
      simp only [mem_preimage, mem_Iic]
      change (cell v + x) i ≤ _
      rw [PiLp.add_apply, cell_apply]
      linarith [(hx i).2]
    · rintro _ ⟨x, hx, rfl⟩
      simp only [mem_preimage, mem_Ici]
      change _ ≤ (cell w + x) i
      rw [PiLp.add_apply, cell_apply]
      linarith [(hx i).1]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with hlt | hlt
  · exact key i hlt
  · exact (key i hlt).symm

/-- The grid packing of `k^d` unit cubes in the cube of side `k`. -/
noncomputable def gridPacking (k : ℕ) (hk : 0 < k) : Packing (cube d) (cube d) k (k ^ d) where
  g := fun m => cellMap (finFunctionFinEquiv.symm m)
  inside := fun m => cell_inside hk _
  disjoint := fun m m' hmm' => cell_disjoint fun h => hmm' (finFunctionFinEquiv.symm.injective h)

/-- No packing of `k^d` unit cubes fits in a cube of side less than `k`. -/
theorem cube_side_ge {k : ℕ} {s : ℝ} (hd : d ≠ 0) (P : Packing (cube d) (cube d) s (k ^ d)) :
    (k : ℝ) ≤ |s| := by
  have h := card_le_of_packing_self convex_cube volume_cube_pos volume_cube_lt_top P
  rw [finrank_euclideanSpace_fin] at h
  push_cast at h
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg s) hd).mp h

/-- **Cubes in a cube.** In every dimension `d ≥ 1`, the smallest cube holding `k^d` unit cubes (with
pairwise disjoint interiors, each placed by any rigid motion) has side exactly `k`. -/
theorem cubes_in_cube_optimal (hd : d ≠ 0) (k : ℕ) (hk : 0 < k) :
    Nonempty (Packing (cube d) (cube d) k (k ^ d)) ∧
      ∀ s : ℝ, Packing (cube d) (cube d) s (k ^ d) → (k : ℝ) ≤ |s| :=
  ⟨⟨gridPacking k hk⟩, fun _ P => cube_side_ge hd P⟩

/-! Catalogue instances: `cubincub` n = 8, 27, 64 (side 2, 3, 4), tesseracts `c8inc8` n = 16 and
5-cubes `hc5inhc5` n = 32 (side 2). -/

theorem cubincub_n08 : Nonempty (Packing (cube 3) (cube 3) 2 8) ∧
    ∀ s : ℝ, Packing (cube 3) (cube 3) s 8 → 2 ≤ |s| := by
  simpa using cubes_in_cube_optimal (d := 3) (by norm_num) 2 (by norm_num)

theorem cubincub_n27 : Nonempty (Packing (cube 3) (cube 3) 3 27) ∧
    ∀ s : ℝ, Packing (cube 3) (cube 3) s 27 → 3 ≤ |s| := by
  simpa using cubes_in_cube_optimal (d := 3) (by norm_num) 3 (by norm_num)

theorem cubincub_n64 : Nonempty (Packing (cube 3) (cube 3) 4 64) ∧
    ∀ s : ℝ, Packing (cube 3) (cube 3) s 64 → 4 ≤ |s| := by
  simpa using cubes_in_cube_optimal (d := 3) (by norm_num) 4 (by norm_num)

theorem c8inc8_n16 : Nonempty (Packing (cube 4) (cube 4) 2 16) ∧
    ∀ s : ℝ, Packing (cube 4) (cube 4) s 16 → 2 ≤ |s| := by
  simpa using cubes_in_cube_optimal (d := 4) (by norm_num) 2 (by norm_num)

theorem hc5inhc5_n32 : Nonempty (Packing (cube 5) (cube 5) 2 32) ∧
    ∀ s : ℝ, Packing (cube 5) (cube 5) s 32 → 2 ≤ |s| := by
  simpa using cubes_in_cube_optimal (d := 5) (by norm_num) 2 (by norm_num)

end PackingOptimality

namespace PackingOptimality

open Set
open scoped Pointwise

variable {d : ℕ}

/-- **Plateau, conditional on the cube centre lemma.** If every unit `d`-cube inside a cube of side
`s < 2` contains the container's centre in its interior (verified numerically for d = 2, ..., 6; the
container here is `s • [0,1]^d`, with centre `(s/2, ..., s/2)`), then side 2 is optimal for every
`2 ≤ n ≤ 2^d`: the grid gives side 2, and no smaller side works. -/
theorem cube_plateau_of_centre_lemma (hd : d ≠ 0)
    (centre : ∀ s : ℝ, 0 ≤ s → s < 2 → ∀ g : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d),
      g '' cube d ⊆ s • cube d → (s / 2) • WithLp.toLp 2 (fun _ => (1 : ℝ)) ∈ interior (g '' cube d))
    {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 2 ^ d) :
    Nonempty (Packing (cube d) (cube d) 2 n) ∧ ∀ s : ℝ, 0 ≤ s → Packing (cube d) (cube d) s n → 2 ≤ s := by
  refine ⟨⟨by simpa using (gridPacking 2 (by norm_num) (d := d)).restrict hn⟩, fun s hs P => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact no_packing_two_of_common_point _ (centre s hs hlt) hn2 P

end PackingOptimality
