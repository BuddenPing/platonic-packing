import PackingOptimality.TetInDod

/-!
# Two tetrahedra in an icosahedron: edge `2√((5 - √5)/15)` is optimal

**Theorem (`tetinico_n02`).** Two regular tetrahedra of edge 1 fit in a regular icosahedron of edge
`s = 2√((5 - √5)/15) ≈ 0.8585`, and in no smaller one.

**Lower bound.** The facet-width lemma. The icosahedron of edge 1 is the convex hull of its 12 vertices, the
cyclic permutations of `(0, ±1/2, ±φ/2)`, all at distance `R = √(φ + 2)/2` from the centre; so `s R ≥ √(2/3)`,
the height of the tetrahedron.

**Construction.** Put the apex at the vertex `s (0, 1/2, φ/2)` of the scaled icosahedron and the opposite face in
the plane `y + φ z = 0` through the centre, one edge parallel to the `x`-axis. With `ι = 1/√(3(φ + 2))` the
vertices are
`A = (0, √2 ι, √2 φ ι)`, `B₀ = (0, φ ι, -ι)` and `B± = (±1/2, -φ ι/2, ι/2)`, and the rotation taking the
tetrahedron of `TetInCube` there has entries in `ℚ(√2, φ, ι)`. Each base vertex is an explicit convex
combination of three vertices of the scaled icosahedron and its centre:
* `B₀ = s (α/2 V₁ + α/2 V₂ + α V₃)` with `α = √2(φ - 1)/2`;
* `B₊ = s (a V₄ + b V₅ + c V₆)` with `c = √2/4`, `a, b = √2 ((φ - 1)(κ - 1) ± 1)/8`, `κ = √(3(φ + 2))`.
The point reflection gives the second tetrahedron, separated by the plane `y + φ z = 0`.
-/

namespace PackingOptimality.TetInIco

open Set FacetWidth OctInCube TetInCube TetInOct TetInDod
open scoped Pointwise RealInnerProductSpace

/-- The 12 vertices of the regular icosahedron of edge 1. -/
noncomputable def icoV : Finset P3 :=
  ({pt 0 (1/2) (φ/2), pt 0 (1/2) (-(φ/2)), pt 0 (-(1/2)) (φ/2), pt 0 (-(1/2)) (-(φ/2)),
    pt (1/2) (φ/2) 0, pt (1/2) (-(φ/2)) 0, pt (-(1/2)) (φ/2) 0, pt (-(1/2)) (-(φ/2)) 0,
    pt (φ/2) 0 (1/2), pt (φ/2) 0 (-(1/2)), pt (-(φ/2)) 0 (1/2), pt (-(φ/2)) 0 (-(1/2))} : Finset P3)

/-- The regular icosahedron of edge 1, centred at the origin. -/
noncomputable def ico : Set P3 := convexHull ℝ (icoV : Set P3)

theorem icoV_norm : ∀ x ∈ icoV, ‖x‖ ^ 2 = (φ + 2) / 4 := by
  have h := φ_sq
  intro x hx
  simp only [icoV, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [norm_sq_pt] <;> nlinarith [h]

theorem ico_norm (x : P3) (hx : x ∈ ico) : ‖x‖ ^ 2 ≤ (φ + 2) / 4 := by
  have hφ := φ_pos
  have hsub : ico ⊆ Metric.closedBall 0 (Real.sqrt ((φ + 2) / 4)) := by
    apply convexHull_min _ (convex_closedBall 0 _)
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [icoV_norm y hy]
  have := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  have h2 := pow_le_pow_left₀ (norm_nonneg x) this 2
  rwa [Real.sq_sqrt (by positivity)] at h2

/-! ## Constants -/

theorem s5_bounds : 2.2 ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 2.24 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

theorem φ_bounds : 1.6 ≤ φ ∧ φ ≤ 1.62 := by
  obtain ⟨h1, h2⟩ := s5_bounds; unfold φ; constructor <;> linarith

theorem s2_bounds : 1.41 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.42 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-- `ι = 1/√(3(φ + 2))`. -/
noncomputable def ι : ℝ := Real.sqrt ((3 - φ) / 15)

theorem ι_pos : 0 < ι := Real.sqrt_pos.mpr (by linarith [φ_bounds.2])

theorem r2_2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem r2_3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, r2_2]
theorem r2_4 : Real.sqrt 2 ^ 4 = 4 := by rw [show 4 = 2 * 2 by rfl, pow_mul, r2_2]; norm_num
theorem φ_2 : φ ^ 2 = φ + 1 := φ_sq
theorem φ_3 : φ ^ 3 = 2 * φ + 1 := by rw [pow_succ, φ_sq]; linear_combination φ_sq
theorem φ_4 : φ ^ 4 = 3 * φ + 2 := by rw [show 4 = 2 * 2 by rfl, pow_mul, φ_sq]; linear_combination φ_sq
theorem ι_2 : ι ^ 2 = (3 - φ) / 15 := Real.sq_sqrt (by linarith [φ_bounds.2])
theorem ι_3 : ι ^ 3 = ι * ((3 - φ) / 15) := by rw [pow_succ, ι_2, mul_comm]
theorem ι_4 : ι ^ 4 = ((3 - φ) / 15) ^ 2 := by rw [show 4 = 2 * 2 by rfl, pow_mul, ι_2]

/-- Normalise polynomials in `√2`, `φ`, `ι` modulo `√2² = 2`, `φ² = φ + 1`, `ι² = (3 - φ)/15`. -/
macro "rad_ring" : tactic => `(tactic| (
  try ring_nf
  repeat (simp only [r2_2, r2_3, r2_4, φ_2, φ_3, φ_4, ι_2, ι_3, ι_4]; try ring_nf)))

/-- The optimal edge, `s = 2√2 ι`. -/
noncomputable def si : ℝ := 2 * Real.sqrt 2 * ι

theorem si_pos : 0 < si := by unfold si; have := ι_pos; positivity

theorem si_eq : si = 2 * Real.sqrt ((5 - Real.sqrt 5) / 15) := by
  unfold si ι
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2; unfold φ; ring

/-- `κ = 1/ι = √(3(φ + 2))`. -/
noncomputable def κ : ℝ := (3 * φ + 6) * ι

theorem κ_sq : κ ^ 2 = 3 * φ + 6 := by unfold κ; rad_ring

theorem κ_pos : 0 < κ := by unfold κ; have := ι_pos; have := φ_pos; positivity

theorem κ_ι : κ * ι = 1 := by unfold κ; rad_ring

theorem κ_ge : φ + 1 ≤ κ := by
  have h : (φ + 1) ^ 2 ≤ κ ^ 2 := by rw [κ_sq]; nlinarith [φ_sq]
  exact (pow_le_pow_iff_left₀ (by linarith [φ_pos]) κ_pos.le two_ne_zero).mp h

theorem κ_le : κ ≤ 3.3 := by
  have h : κ ^ 2 ≤ 3.3 ^ 2 := by rw [κ_sq]; nlinarith [φ_bounds.2]
  exact (pow_le_pow_iff_left₀ κ_pos.le (by norm_num) two_ne_zero).mp h

/-! ## Lower bound -/

theorem centre_tet_ico (s : ℝ) (hs0 : 0 ≤ s) (hs : s < si) (g : P3 ≃ᵃⁱ[ℝ] P3) (hg : g '' tetra ⊆ s • ico) :
    (0 : P3) ∈ interior (g '' tetra) := by
  refine centre_of_facet_width (fun _ => 1 / 4) a v rfl v_mem v_one norm_a ico_norm hs0 ?_ g hg
  have hsi : si ^ 2 * ((φ + 2) / 4) = 2 / 3 := by unfold si; rad_ring
  have h1 : s ^ 2 < si ^ 2 := by nlinarith [si_pos]
  have h2 : 0 < (φ + 2) / 4 := by have := φ_pos; positivity
  nlinarith

/-! ## The rotation -/

noncomputable def qα : ℝ := Real.sqrt 2 / 2
noncomputable def qβ : ℝ := ι * (2 - Real.sqrt 2 * φ) / 2
noncomputable def qγ : ℝ := ι * (1 + Real.sqrt 2 * φ)
noncomputable def qδ : ℝ := ι * (2 * φ + Real.sqrt 2) / 2
noncomputable def qε : ℝ := ι * (φ - Real.sqrt 2)

noncomputable def Ql : P3 →ₗ[ℝ] P3 where
  toFun y := pt (qα * (y 0 - y 1)) (qβ * (y 0 + y 1) + qγ * y 2) (qδ * (y 0 + y 1) + qε * y 2)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r y := by ext i; fin_cases i <;> simp <;> ring

theorem Ql_apply (y : P3) :
    Ql y = pt (qα * (y 0 - y 1)) (qβ * (y 0 + y 1) + qγ * y 2) (qδ * (y 0 + y 1) + qε * y 2) := rfl

theorem hα : qα ^ 2 = 1 / 2 := by unfold qα; rad_ring
theorem hβδ : qβ ^ 2 + qδ ^ 2 = 1 / 2 := by unfold qβ qδ; rad_ring
theorem hβγ : qβ * qγ + qδ * qε = 0 := by unfold qβ qγ qδ qε; rad_ring
theorem hγε : qγ ^ 2 + qε ^ 2 = 1 := by unfold qγ qε; rad_ring

theorem Ql_inner (x y : P3) : ⟪Ql x, Ql y⟫ = ⟪x, y⟫ := by
  simp only [CentreGeneral.inner_sum, Fin.sum_univ_three, Ql_apply, pt_zero, pt_one, pt_two]
  linear_combination ((x 0 - x 1) * (y 0 - y 1)) * hα + ((x 0 + x 1) * (y 0 + y 1)) * hβδ +
    ((x 0 + x 1) * y 2 + x 2 * (y 0 + y 1)) * hβγ + (x 2 * y 2) * hγε

noncomputable def Q : P3 ≃ₗᵢ[ℝ] P3 := (Ql.isometryOfInner Ql_inner).toLinearIsometryEquiv rfl

noncomputable def pI : P3 := pt 0 (Real.sqrt 2 * ι / 4) (Real.sqrt 2 * φ * ι / 4)

noncomputable def gI : P3 ≃ᵃⁱ[ℝ] P3 :=
  Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ P3 pI)

theorem gI_apply (y : P3) : gI y = pI + Ql y := rfl

/-! ## The images of the vertices -/

theorem gI_v0 : gI (v 0) = pt 0 (Real.sqrt 2 * ι) (Real.sqrt 2 * φ * ι) := by
  rw [gI_apply]; ext i; fin_cases i <;> simp [Ql_apply, pI, v, sig, qα, qβ, qγ, qδ, qε] <;> rad_ring

theorem gI_v1 : gI (v 1) = pt (1 / 2) (-(φ * ι / 2)) (ι / 2) := by
  rw [gI_apply]; ext i; fin_cases i <;> simp [Ql_apply, pI, v, sig, qα, qβ, qγ, qδ, qε] <;> rad_ring

theorem gI_v2 : gI (v 2) = pt (-(1 / 2)) (-(φ * ι / 2)) (ι / 2) := by
  rw [gI_apply]; ext i; fin_cases i <;> simp [Ql_apply, pI, v, sig, qα, qβ, qγ, qδ, qε] <;> rad_ring

theorem gI_v3 : gI (v 3) = pt 0 (φ * ι) (-ι) := by
  rw [gI_apply]; ext i; fin_cases i <;> simp [Ql_apply, pI, v, sig, qα, qβ, qγ, qδ, qε] <;> rad_ring

/-! ## Convex combinations in the icosahedron -/

theorem neg_pt (a b c : ℝ) : -pt a b c = pt (-a) (-b) (-c) := by ext i; fin_cases i <;> simp

theorem mem_ico {x : P3} (hx : x ∈ icoV) : x ∈ ico := subset_convexHull ℝ _ hx

theorem zero_mem_ico : (0 : P3) ∈ ico := by
  have h := (convex_convexHull ℝ (icoV : Set P3)) (mem_ico (x := pt 0 (1/2) (φ/2)) (by simp [icoV]))
    (mem_ico (x := pt 0 (-(1/2)) (-(φ/2))) (by simp [icoV])) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (0 : P3) = (1 / 2 : ℝ) • pt 0 (1/2) (φ/2) + (1 / 2 : ℝ) • pt 0 (-(1/2)) (-(φ/2)) := by
    ext i; fin_cases i <;> simp
  rw [e]; exact h

theorem comb3 {P R T : P3} (hP : P ∈ ico) (hR : R ∈ ico) (hT : T ∈ ico) {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c ≤ 1) : a • P + b • R + c • T ∈ ico := by
  have := (convex_convexHull ℝ (icoV : Set P3)).sum_mem (t := (Finset.univ : Finset (Fin 4)))
    (w := ![a, b, c, 1 - a - b - c]) (z := ![P, R, T, 0])
    (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_four])
    (by intro i _; fin_cases i <;> simp <;> first | exact hP | exact hR | exact hT | exact zero_mem_ico)
  show a • P + b • R + c • T ∈ convexHull ℝ (icoV : Set P3)
  simpa [Fin.sum_univ_four] using this

theorem neg_ico {x : P3} (hx : x ∈ ico) : -x ∈ ico := by
  have hsub : ico ⊆ -ico := by
    apply convexHull_min _ (convex_convexHull ℝ _).neg
    intro y hy
    rw [Set.mem_neg]
    apply mem_ico
    simp only [icoV, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [neg_pt, icoV]
  have := hsub hx
  rwa [Set.mem_neg] at this

/-! ## The four vertices lie in `si • ico` -/

/-- Weight for `B₀`. -/
noncomputable def w3 : ℝ := Real.sqrt 2 * (φ - 1) / 2

theorem w3_bounds : 0 ≤ w3 ∧ w3 / 2 + w3 / 2 + w3 ≤ 1 := by
  obtain ⟨p1, p2⟩ := φ_bounds; obtain ⟨r1, r2⟩ := s2_bounds
  unfold w3; constructor
  · have : 0 ≤ φ - 1 := by linarith
    positivity
  · nlinarith

noncomputable def wa : ℝ := Real.sqrt 2 * ((φ - 1) * (κ - 1) + 1) / 8
noncomputable def wb : ℝ := Real.sqrt 2 * ((φ - 1) * (κ - 1) - 1) / 8
noncomputable def wc : ℝ := Real.sqrt 2 / 4

theorem wab_bounds : 0 ≤ wa ∧ 0 ≤ wb ∧ 0 ≤ wc ∧ wa + wb + wc ≤ 1 := by
  obtain ⟨p1, p2⟩ := φ_bounds; obtain ⟨r1, r2⟩ := s2_bounds
  have k1 := κ_ge; have k2 := κ_le
  have e1 : 1 ≤ (φ - 1) * (κ - 1) := by nlinarith [φ_sq]
  have e2 : (φ - 1) * (κ - 1) ≤ 1.43 := by nlinarith
  unfold wa wb wc
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · have : 0 ≤ (φ - 1) * (κ - 1) - 1 := by linarith
    positivity
  · nlinarith

theorem v0_mem : gI (v 0) ∈ si • ico := by
  rw [gI_v0]
  refine ⟨pt 0 (1/2) (φ/2), mem_ico (by simp [icoV]), ?_⟩
  ext i; fin_cases i <;> simp [si] <;> ring

theorem v3_mem : gI (v 3) ∈ si • ico := by
  rw [gI_v3]
  obtain ⟨h0, h1⟩ := w3_bounds
  refine ⟨(w3 / 2) • pt (1/2) (φ/2) 0 + (w3 / 2) • pt (-(1/2)) (φ/2) 0 + w3 • pt 0 (1/2) (-(φ/2)),
    comb3 (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV]))
      (by linarith) (by linarith) h0 h1, ?_⟩
  ext i; fin_cases i <;> simp [si, w3] <;> rad_ring

theorem v1_mem : gI (v 1) ∈ si • ico := by
  rw [gI_v1]
  obtain ⟨ha, hb, hc, h⟩ := wab_bounds
  refine ⟨wa • pt (φ/2) 0 (1/2) + wb • pt (φ/2) 0 (-(1/2)) + wc • pt (1/2) (-(φ/2)) 0,
    comb3 (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV])) ha hb hc h, ?_⟩
  ext i; fin_cases i <;> simp [si, wa, wb, wc, κ] <;> rad_ring

theorem v2_mem : gI (v 2) ∈ si • ico := by
  rw [gI_v2]
  obtain ⟨ha, hb, hc, h⟩ := wab_bounds
  refine ⟨wa • pt (-(φ/2)) 0 (1/2) + wb • pt (-(φ/2)) 0 (-(1/2)) + wc • pt (-(1/2)) (-(φ/2)) 0,
    comb3 (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV])) (mem_ico (by simp [icoV])) ha hb hc h, ?_⟩
  ext i; fin_cases i <;> simp [si, wa, wb, wc, κ] <;> rad_ring

theorem convSI : Convex ℝ (si • ico) := (convex_convexHull ℝ _).smul _

theorem gI_inside : gI '' tetra ⊆ si • ico :=
  image_tetra_sub gI convSI fun j => by
    fin_cases j
    · exact v0_mem
    · exact v1_mem
    · exact v2_mem
    · exact v3_mem

/-! ## Separation by the plane `y + φ z = 0` -/

noncomputable def fsep : P3 →L[ℝ] ℝ := EuclideanSpace.proj 1 + φ • EuclideanSpace.proj 2

theorem fsep_apply (x : P3) : fsep x = x 1 + φ * x 2 := rfl

theorem fsep_surjective : Function.Surjective fsep :=
  fun t => ⟨EuclideanSpace.single 1 t, by simp [fsep_apply]⟩

theorem fsep_gI {y : P3} (hy : y ∈ tetra) : 0 ≤ fsep (gI y) := by
  obtain ⟨f0, -, -, -⟩ := mem_tetra.mp hy
  have e : fsep (gI y) = ι * (1 + φ ^ 2) * (Real.sqrt 2 / 4 + (y 0 + y 1 + y 2)) := by
    rw [fsep_apply, gI_apply]; simp [Ql_apply, pI, qβ, qγ, qδ, qε]; ring
  rw [e]
  have : 0 ≤ Real.sqrt 2 / 4 + (y 0 + y 1 + y 2) := by nlinarith [TetInCube.s2, TetInCube.s2pos]
  have := ι_pos
  positivity

noncomputable def gI' : P3 ≃ᵃⁱ[ℝ] P3 := gI.trans (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv

theorem gI'_apply (y : P3) : gI' y = -gI y := rfl

theorem gI'_inside : gI' '' tetra ⊆ si • ico := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := gI_inside ⟨y, hy, rfl⟩
  exact ⟨-x, neg_ico hx, by simp only [gI'_apply, ← hxy, smul_neg]⟩

theorem gI_disjoint : Disjoint (interior (gI' '' tetra)) (interior (gI '' tetra)) := by
  apply interior_disjoint_of_separated fsep fsep_surjective (c := 0)
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [gI'_apply, map_neg]; linarith [fsep_gI hy]
  · rintro _ ⟨y, hy, rfl⟩
    exact fsep_gI hy

noncomputable def tetIcoPacking : Packing tetra ico si 2 where
  g := ![gI, gI']
  inside := by
    intro i; fin_cases i
    · exact gI_inside
    · exact gI'_inside
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact gI_disjoint.symm
    · exact gI_disjoint
    · exact absurd rfl hij

end PackingOptimality.TetInIco

namespace PackingOptimality

open TetInCube TetInIco

/-- **Two tetrahedra in an icosahedron: edge `2√((5 - √5)/15)` is optimal.** -/
theorem tetinico_n02 : Nonempty (Packing tetra ico (2 * Real.sqrt ((5 - Real.sqrt 5) / 15)) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing tetra ico s 2 → 2 * Real.sqrt ((5 - Real.sqrt 5) / 15) ≤ s := by
  rw [← si_eq]
  refine ⟨⟨tetIcoPacking⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : P3) (fun g hg => centre_tet_ico s hs h g hg) le_rfl P

end PackingOptimality
