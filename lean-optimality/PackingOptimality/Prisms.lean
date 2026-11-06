import PackingOptimality.Cubes

/-!
# Triangular prisms in a triangular prism: `k^3` unit prisms need scale exactly `k`

The unit triangular prism (equilateral base of edge 1, height 1) is the image of the right-triangle prism
`R = {y | 0 ≤ y₀, 0 ≤ y₁, y₀ + y₁ ≤ 1, 0 ≤ y₂ ≤ 1}` under a linear map `shear`. The scale-`k` prism is tiled
by `k^3` pieces: in each of `k` layers, `k(k+1)/2` upward triangles (translates) and `k(k-1)/2` downward
triangles (point reflections). Translations and point reflections commute with `shear` up to a change of
vector, so the tiles are congruent copies of the unit prism placed by affine isometries. Distinct tiles have
disjoint interiors because an interior point determines `⌊y₀⌋`, `⌊y₁⌋`, `⌊y₂⌋` and the orientation.
-/

namespace PackingOptimality

open MeasureTheory Set Module
open scoped Pointwise ENNReal

abbrev P3 := EuclideanSpace ℝ (Fin 3)

noncomputable def pt (a b c : ℝ) : P3 := WithLp.toLp 2 ![a, b, c]

@[simp] theorem pt_zero (a b c : ℝ) : pt a b c 0 = a := by simp [pt]
@[simp] theorem pt_one (a b c : ℝ) : pt a b c 1 = b := by simp [pt]
@[simp] theorem pt_two (a b c : ℝ) : pt a b c 2 = c := by simp [pt]

theorem pt_eta (y : P3) : pt (y 0) (y 1) (y 2) = y := by
  ext i; fin_cases i <;> simp

theorem sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := by positivity
theorem sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- Right-triangle model → equilateral prism. -/
noncomputable def shearL : P3 →ₗ[ℝ] P3 where
  toFun y := pt (y 0 + y 1 / 2) (Real.sqrt 3 / 2 * y 1) (y 2)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

noncomputable def unshearL : P3 →ₗ[ℝ] P3 where
  toFun x := pt (x 0 - x 1 / Real.sqrt 3) (2 / Real.sqrt 3 * x 1) (x 2)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

noncomputable def shear : P3 ≃L[ℝ] P3 :=
  (LinearEquiv.ofLinear shearL unshearL
    (by
      apply LinearMap.ext; intro x
      ext i; fin_cases i <;> simp [shearL, unshearL] <;> field_simp <;> ring)
    (by
      apply LinearMap.ext; intro y
      ext i; fin_cases i <;> simp [shearL, unshearL] <;> field_simp <;> ring)).toContinuousLinearEquiv

theorem shear_apply (y : P3) : shear y = pt (y 0 + y 1 / 2) (Real.sqrt 3 / 2 * y 1) (y 2) := rfl

/-- The right-triangle prism (model). -/
def rprism : Set P3 := {y | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1 ∧ 0 ≤ y 2 ∧ y 2 ≤ 1}

/-- The unit triangular prism: equilateral base of edge 1 (vertices `(0,0)`, `(1,0)`, `(1/2, √3/2)`), height 1. -/
noncomputable def prism3 : Set P3 := shear '' rprism

theorem convex_rprism : Convex ℝ rprism := by
  intro x hx y hy a b ha hb hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨k1, k2, k3, k4, k5⟩ := hy
  simp only [rprism, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem convex_prism3 : Convex ℝ prism3 :=
  convex_rprism.linear_image (shear : P3 →L[ℝ] P3).toLinearMap

theorem continuous_coord (i : Fin 3) : Continuous fun y : P3 => y i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

theorem volume_prism3_pos : 0 < volume prism3 := by
  let U : Set P3 := {y | 0 < y 0 ∧ 0 < y 1 ∧ y 0 + y 1 < 1 ∧ 0 < y 2 ∧ y 2 < 1}
  have hU : IsOpen U := by
    have c0 := continuous_coord 0; have c1 := continuous_coord 1; have c2 := continuous_coord 2
    exact ((isOpen_lt continuous_const c0).inter ((isOpen_lt continuous_const c1).inter
      ((isOpen_lt (c0.add c1) continuous_const).inter ((isOpen_lt continuous_const c2).inter
        (isOpen_lt c2 continuous_const)))))
  have hne : U.Nonempty := ⟨pt (1/4) (1/4) (1/2), by simp [U]; norm_num⟩
  have hopen : IsOpen (shear '' U) := shear.toHomeomorph.isOpenMap U hU
  calc 0 < volume (shear '' U) := hopen.measure_pos volume (hne.image _)
    _ ≤ volume prism3 := measure_mono (image_mono fun y hy =>
        ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.1.le, hy.2.2.2.2.le⟩)

theorem volume_prism3_lt_top : volume prism3 < ∞ := by
  have hb : Bornology.IsBounded rprism := cube_isBounded.subset fun y hy i => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    fin_cases i
    · exact ⟨h1, by simp; linarith⟩
    · exact ⟨h2, by simp; linarith⟩
    · exact ⟨h4, h5⟩
  exact ((shear : P3 →L[ℝ] P3).lipschitz.isBounded_image hb).measure_lt_top

/-! ### Tiles of the scale-`k` prism (in the model) -/

def upTile (a b c : ℕ) : Set P3 :=
  {y | (a : ℝ) ≤ y 0 ∧ (b : ℝ) ≤ y 1 ∧ y 0 + y 1 ≤ a + b + 1 ∧ (c : ℝ) ≤ y 2 ∧ y 2 ≤ c + 1}

def downTile (a b c : ℕ) : Set P3 :=
  {y | y 0 ≤ a + 1 ∧ y 1 ≤ b + 1 ∧ (a : ℝ) + b + 1 ≤ y 0 + y 1 ∧ (c : ℝ) ≤ y 2 ∧ y 2 ≤ c + 1}

noncomputable def upMap (a b c : ℕ) : P3 ≃ᵃⁱ[ℝ] P3 :=
  AffineIsometryEquiv.constVAdd ℝ P3 (shear (pt a b c))

noncomputable def downMap (a b c : ℕ) : P3 ≃ᵃⁱ[ℝ] P3 :=
  (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ P3 (shear (pt (a + 1) (b + 1) (c + 1))))

theorem upMap_apply (a b c : ℕ) (x : P3) : upMap a b c x = shear (pt a b c) + x := rfl

theorem downMap_apply (a b c : ℕ) (x : P3) :
    downMap a b c x = shear (pt (a + 1) (b + 1) (c + 1)) + -x := rfl

theorem upMap_image (a b c : ℕ) : upMap a b c '' prism3 = shear '' upTile a b c := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    refine ⟨pt a b c + y, ?_, ?_⟩
    · simp only [upTile, mem_setOf_eq, PiLp.add_apply, pt_zero, pt_one, pt_two]
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [upMap_apply, map_add]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    refine ⟨shear (z - pt a b c), ⟨z - pt a b c, ?_, rfl⟩, ?_⟩
    · simp only [rprism, mem_setOf_eq, PiLp.sub_apply, pt_zero, pt_one, pt_two]
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [upMap_apply, map_sub]; abel

theorem downMap_image (a b c : ℕ) : downMap a b c '' prism3 = shear '' downTile a b c := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    refine ⟨pt (a + 1) (b + 1) (c + 1) - y, ?_, ?_⟩
    · simp only [downTile, mem_setOf_eq, PiLp.sub_apply, pt_zero, pt_one, pt_two]
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [downMap_apply, map_sub]; abel
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    refine ⟨shear (pt (a + 1) (b + 1) (c + 1) - z), ⟨pt (a + 1) (b + 1) (c + 1) - z, ?_, rfl⟩, ?_⟩
    · simp only [rprism, mem_setOf_eq, PiLp.sub_apply, pt_zero, pt_one, pt_two]
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [downMap_apply, map_sub]; abel

theorem mem_smul_rprism {k : ℝ} (hk : 0 < k) {y : P3}
    (h1 : 0 ≤ y 0) (h2 : 0 ≤ y 1) (h3 : y 0 + y 1 ≤ k) (h4 : 0 ≤ y 2) (h5 : y 2 ≤ k) :
    y ∈ k • rprism := by
  refine ⟨k⁻¹ • y, ?_, by simp [smul_smul, hk.ne']⟩
  have hk' : 0 < k⁻¹ := inv_pos.mpr hk
  simp only [rprism, mem_setOf_eq, PiLp.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_, by positivity, ?_⟩
  · rw [← mul_add, inv_mul_le_iff₀ hk]; linarith
  · rw [inv_mul_le_iff₀ hk]; linarith

theorem smul_prism3 (k : ℝ) : k • prism3 = shear '' (k • rprism) := by
  rw [prism3, ← image_smul_set]

theorem upTile_inside {k a b c : ℕ} (hab : a + b + 1 ≤ k) (hc : c + 1 ≤ k) :
    shear '' upTile a b c ⊆ (k : ℝ) • prism3 := by
  rw [smul_prism3]
  apply image_mono
  rintro y ⟨h1, h2, h3, h4, h5⟩
  have hab' : (a : ℝ) + b + 1 ≤ k := by exact_mod_cast hab
  have hc' : (c : ℝ) + 1 ≤ k := by exact_mod_cast hc
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  exact mem_smul_rprism (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)

theorem downTile_inside {k a b c : ℕ} (hab : a + b + 2 ≤ k) (hc : c + 1 ≤ k) :
    shear '' downTile a b c ⊆ (k : ℝ) • prism3 := by
  rw [smul_prism3]
  apply image_mono
  rintro y ⟨h1, h2, h3, h4, h5⟩
  have hab' : (a : ℝ) + b + 2 ≤ k := by exact_mod_cast hab
  have hc' : (c : ℝ) + 1 ≤ k := by exact_mod_cast hc
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  exact mem_smul_rprism (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)

/-- Interior of a set below a hyperplane lies strictly below it. -/
theorem interior_subset_lt {S : Set P3} (f : P3 →L[ℝ] ℝ) (hf : Function.Surjective f) {c : ℝ}
    (hS : ∀ y ∈ S, f y ≤ c) : ∀ y ∈ interior S, f y < c := by
  have hopen : IsOpenMap f := f.isOpenMap hf
  intro y hy
  have : y ∈ interior (f ⁻¹' Iic c) := interior_mono (fun z hz => hS z hz) hy
  rw [← hopen.preimage_interior_eq_interior_preimage f.continuous, interior_Iic] at this
  exact this

theorem neg_surjective {f : P3 →L[ℝ] ℝ} (hf : Function.Surjective f) : Function.Surjective (-f) :=
  fun t => let ⟨y, hy⟩ := hf (-t); ⟨y, by simp [hy]⟩

theorem interior_subset_gt {S : Set P3} (f : P3 →L[ℝ] ℝ) (hf : Function.Surjective f) {c : ℝ}
    (hS : ∀ y ∈ S, c ≤ f y) : ∀ y ∈ interior S, c < f y := by
  intro y hy
  have := interior_subset_lt (-f) (neg_surjective hf) (c := -c) (fun z hz => by
    simp only [ContinuousLinearMap.neg_apply]; linarith [hS z hz]) y hy
  simp only [ContinuousLinearMap.neg_apply] at this
  linarith

noncomputable def coordL (i : Fin 3) : P3 →L[ℝ] ℝ := EuclideanSpace.proj i

theorem coordL_apply (i : Fin 3) (y : P3) : coordL i y = y i := rfl

theorem coordL_surjective (i : Fin 3) : Function.Surjective (coordL i) := proj_surjective i

noncomputable def sumL : P3 →L[ℝ] ℝ := coordL 0 + coordL 1

theorem sumL_apply (y : P3) : sumL y = y 0 + y 1 := rfl

theorem sumL_surjective : Function.Surjective sumL :=
  fun t => ⟨EuclideanSpace.single 0 t, by simp [sumL, coordL_apply]⟩

/-- Coordinates of interior points of an up tile. -/
theorem upTile_interior {a b c : ℕ} {y : P3} (hy : y ∈ interior (upTile a b c)) :
    (a : ℝ) < y 0 ∧ (b : ℝ) < y 1 ∧ y 0 + y 1 < a + b + 1 ∧ (c : ℝ) < y 2 ∧ y 2 < c + 1 :=
  ⟨interior_subset_gt (coordL 0) (coordL_surjective 0) (fun z hz => hz.1) y hy,
   interior_subset_gt (coordL 1) (coordL_surjective 1) (fun z hz => hz.2.1) y hy,
   interior_subset_lt sumL sumL_surjective (fun z hz => hz.2.2.1) y hy,
   interior_subset_gt (coordL 2) (coordL_surjective 2) (fun z hz => hz.2.2.2.1) y hy,
   interior_subset_lt (coordL 2) (coordL_surjective 2) (fun z hz => hz.2.2.2.2) y hy⟩

theorem downTile_interior {a b c : ℕ} {y : P3} (hy : y ∈ interior (downTile a b c)) :
    y 0 < a + 1 ∧ y 1 < b + 1 ∧ (a : ℝ) + b + 1 < y 0 + y 1 ∧ (c : ℝ) < y 2 ∧ y 2 < c + 1 :=
  ⟨interior_subset_lt (coordL 0) (coordL_surjective 0) (fun z hz => hz.1) y hy,
   interior_subset_lt (coordL 1) (coordL_surjective 1) (fun z hz => hz.2.1) y hy,
   interior_subset_gt sumL sumL_surjective (fun z hz => hz.2.2.1) y hy,
   interior_subset_gt (coordL 2) (coordL_surjective 2) (fun z hz => hz.2.2.2.1) y hy,
   interior_subset_lt (coordL 2) (coordL_surjective 2) (fun z hz => hz.2.2.2.2) y hy⟩

theorem nat_eq_of_unit_interval {a a' : ℕ} {y : ℝ} (h1 : (a : ℝ) < y) (h2 : y < a + 1)
    (h3 : (a' : ℝ) < y) (h4 : y < a' + 1) : a = a' := by
  have e1 : (a : ℝ) < ((a' + 1 : ℕ) : ℝ) := by push_cast; linarith
  have e2 : (a' : ℝ) < ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_lt.mp e1
  have := Nat.cast_lt.mp e2
  omega

/-! ### The tiling -/

/-- Tile labels `(a, b, c, up?)` of the scale-`k` prism. -/
def ValidTile (k : ℕ) (t : Fin k × Fin k × Fin k × Bool) : Prop :=
  (if t.2.2.2 then t.1.val + t.2.1.val + 1 ≤ k else t.1.val + t.2.1.val + 2 ≤ k)

instance (k : ℕ) : DecidablePred (ValidTile k) := fun t => by unfold ValidTile; infer_instance

abbrev Tile (k : ℕ) := {t : Fin k × Fin k × Fin k × Bool // ValidTile k t}

def tileSet {k : ℕ} (t : Tile k) : Set P3 :=
  if t.1.2.2.2 then upTile t.1.1 t.1.2.1 t.1.2.2.1 else downTile t.1.1 t.1.2.1 t.1.2.2.1

noncomputable def tileMap {k : ℕ} (t : Tile k) : P3 ≃ᵃⁱ[ℝ] P3 :=
  if t.1.2.2.2 then upMap t.1.1 t.1.2.1 t.1.2.2.1 else downMap t.1.1 t.1.2.1 t.1.2.2.1

theorem tileMap_image {k : ℕ} (t : Tile k) : tileMap t '' prism3 = shear '' tileSet t := by
  unfold tileMap tileSet
  split_ifs
  · exact upMap_image _ _ _
  · exact downMap_image _ _ _

theorem tile_inside {k : ℕ} (t : Tile k) : tileMap t '' prism3 ⊆ (k : ℝ) • prism3 := by
  rw [tileMap_image]
  obtain ⟨⟨a, b, c, up⟩, hv⟩ := t
  have hc : c.val + 1 ≤ k := c.isLt
  unfold ValidTile at hv
  cases up
  · simp only [Bool.false_eq_true, ↓reduceIte] at hv
    simpa [tileSet] using downTile_inside hv hc
  · simp only [↓reduceIte] at hv
    simpa [tileSet] using upTile_inside hv hc

theorem tile_disjoint {k : ℕ} {t t' : Tile k} (h : t ≠ t') :
    Disjoint (interior (tileMap t '' prism3)) (interior (tileMap t' '' prism3)) := by
  have e : ∀ S : Set P3, interior (shear '' S) = shear '' interior S := fun S => by
    have := shear.toHomeomorph.image_interior S
    simpa using this.symm
  rw [tileMap_image, tileMap_image, e, e, Set.disjoint_image_iff shear.injective]
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨⟨a, b, c, up⟩, hv⟩ := t
  obtain ⟨⟨a', b', c', up'⟩, hv'⟩ := t'
  apply h
  have key : (a : ℕ) = a' ∧ (b : ℕ) = b' ∧ (c : ℕ) = c' ∧ up = up' := by
    cases up <;> cases up' <;> simp only [tileSet, Bool.false_eq_true, ↓reduceIte] at hy hy'
    · obtain ⟨p1, p2, p3, p4, p5⟩ := downTile_interior hy
      obtain ⟨q1, q2, q3, q4, q5⟩ := downTile_interior hy'
      refine ⟨nat_eq_of_unit_interval (by linarith) p1 (by linarith) q1,
        nat_eq_of_unit_interval (by linarith) p2 (by linarith) q2,
        nat_eq_of_unit_interval p4 p5 q4 q5, rfl⟩
    · obtain ⟨p1, p2, p3, p4, p5⟩ := downTile_interior hy
      obtain ⟨q1, q2, q3, q4, q5⟩ := upTile_interior hy'
      have ea := nat_eq_of_unit_interval (by linarith) p1 q1 (by linarith)
      have eb := nat_eq_of_unit_interval (by linarith) p2 q2 (by linarith)
      have ea' : ((a : ℕ) : ℝ) = ((a' : ℕ) : ℝ) := by exact_mod_cast ea
      have eb' : ((b : ℕ) : ℝ) = ((b' : ℕ) : ℝ) := by exact_mod_cast eb
      exfalso; linarith
    · obtain ⟨p1, p2, p3, p4, p5⟩ := upTile_interior hy
      obtain ⟨q1, q2, q3, q4, q5⟩ := downTile_interior hy'
      have ea := nat_eq_of_unit_interval p1 (by linarith) (by linarith) q1
      have eb := nat_eq_of_unit_interval p2 (by linarith) (by linarith) q2
      have ea' : ((a : ℕ) : ℝ) = ((a' : ℕ) : ℝ) := by exact_mod_cast ea
      have eb' : ((b : ℕ) : ℝ) = ((b' : ℕ) : ℝ) := by exact_mod_cast eb
      exfalso; linarith
    · obtain ⟨p1, p2, p3, p4, p5⟩ := upTile_interior hy
      obtain ⟨q1, q2, q3, q4, q5⟩ := upTile_interior hy'
      refine ⟨nat_eq_of_unit_interval p1 (by linarith) q1 (by linarith),
        nat_eq_of_unit_interval p2 (by linarith) q2 (by linarith),
        nat_eq_of_unit_interval p4 p5 q4 q5, rfl⟩
  obtain ⟨e1, e2, e3, e4⟩ := key
  have : a = a' := Fin.ext e1
  have : b = b' := Fin.ext e2
  have : c = c' := Fin.ext e3
  subst_vars
  rfl

/-- The tiling of the scale-`k` prism by `k^3` unit prisms (given the tile count). -/
noncomputable def prismTiling (k : ℕ) (hcard : Fintype.card (Tile k) = k ^ 3) :
    Packing prism3 prism3 k (k ^ 3) where
  g := fun i => tileMap ((Fintype.equivFinOfCardEq hcard).symm i)
  inside := fun i => tile_inside _
  disjoint := fun i j hij => tile_disjoint fun h => hij ((Fintype.equivFinOfCardEq hcard).symm.injective h)

theorem prism_scale_ge {k : ℕ} {s : ℝ} (P : Packing prism3 prism3 s (k ^ 3)) : (k : ℝ) ≤ |s| := by
  have h := card_le_of_packing_self convex_prism3 volume_prism3_pos volume_prism3_lt_top P
  rw [finrank_euclideanSpace_fin] at h
  push_cast at h
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg s) (by norm_num)).mp h

/-- **Triangular prisms in a triangular prism.** `k^3` unit prisms need scale exactly `k` (here for the
catalogue's `k = 2, 3, 4`; the tile count is checked by `decide`). -/
theorem prisms_in_prism_optimal (k : ℕ) (hcard : Fintype.card (Tile k) = k ^ 3) :
    Nonempty (Packing prism3 prism3 k (k ^ 3)) ∧
      ∀ s : ℝ, Packing prism3 prism3 s (k ^ 3) → (k : ℝ) ≤ |s| :=
  ⟨⟨prismTiling k hcard⟩, fun _ P => prism_scale_ge P⟩

theorem pr3inpr3_n08 : Nonempty (Packing prism3 prism3 2 8) ∧
    ∀ s : ℝ, Packing prism3 prism3 s 8 → 2 ≤ |s| := by
  simpa using prisms_in_prism_optimal 2 (by decide)

theorem pr3inpr3_n27 : Nonempty (Packing prism3 prism3 3 27) ∧
    ∀ s : ℝ, Packing prism3 prism3 s 27 → 3 ≤ |s| := by
  simpa using prisms_in_prism_optimal 3 (by decide)

theorem pr3inpr3_n64 : Nonempty (Packing prism3 prism3 4 64) ∧
    ∀ s : ℝ, Packing prism3 prism3 s 64 → 4 ≤ |s| := by
  simpa using prisms_in_prism_optimal 4 (by decide)

end PackingOptimality
