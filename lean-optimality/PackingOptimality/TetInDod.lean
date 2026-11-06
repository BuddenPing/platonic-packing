import PackingOptimality.TetInOct

/-!
# Two tetrahedra in a dodecahedron: edge `2√2/(3φ) = √2(√5 - 1)/3` is optimal

**Theorem (`tetindod_n02`).** Two regular tetrahedra of edge 1 fit in a regular dodecahedron of edge
`√2(√5 - 1)/3`, and in no smaller one.

**Lower bound.** The facet-width lemma. The dodecahedron of edge 1 is the convex hull of its 20 vertices, all at
distance `R = √3 φ/2` from the centre, so `s² · 3φ²/4 ≥ 2/3`.

**Construction.** The eight vertices `(±φ/2)(±1, ±1, ±1)` of the dodecahedron span an inscribed cube. At scale
`s = 2√2/(3φ)` this is the cube of edge `2√2/3` holding the two tetrahedra of `TetInCube`. The packing is the same:
each tetrahedron vertex is a cube corner or the convex combination `½, ¼, ¼` of three corners.
-/

namespace PackingOptimality.TetInDod

open Set FacetWidth OctInCube TetInCube TetInOct
open scoped Pointwise RealInnerProductSpace

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem s5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
theorem s5pos : 0 < Real.sqrt 5 := by positivity
theorem φ_sq : φ ^ 2 = φ + 1 := by unfold φ; nlinarith [s5]
theorem φ_pos : 0 < φ := by unfold φ; positivity

/-- The 20 vertices of the regular dodecahedron of edge 1. -/
noncomputable def dodV : Finset P3 :=
  ({pt (φ/2) (φ/2) (φ/2), pt (φ/2) (φ/2) (-(φ/2)), pt (φ/2) (-(φ/2)) (φ/2), pt (φ/2) (-(φ/2)) (-(φ/2)),
    pt (-(φ/2)) (φ/2) (φ/2), pt (-(φ/2)) (φ/2) (-(φ/2)), pt (-(φ/2)) (-(φ/2)) (φ/2), pt (-(φ/2)) (-(φ/2)) (-(φ/2)),
    pt 0 (1/2) (φ^2/2), pt 0 (1/2) (-(φ^2/2)), pt 0 (-(1/2)) (φ^2/2), pt 0 (-(1/2)) (-(φ^2/2)),
    pt (1/2) (φ^2/2) 0, pt (1/2) (-(φ^2/2)) 0, pt (-(1/2)) (φ^2/2) 0, pt (-(1/2)) (-(φ^2/2)) 0,
    pt (φ^2/2) 0 (1/2), pt (φ^2/2) 0 (-(1/2)), pt (-(φ^2/2)) 0 (1/2), pt (-(φ^2/2)) 0 (-(1/2))} : Finset P3)

/-- The regular dodecahedron of edge 1, centred at the origin. -/
noncomputable def dod : Set P3 := convexHull ℝ (dodV : Set P3)

theorem norm_sq_pt (a b c : ℝ) : ‖pt a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, CentreGeneral.inner_sum, Fin.sum_univ_three]; simp; ring

theorem dodV_norm : ∀ x ∈ dodV, ‖x‖ ^ 2 = 3 * φ ^ 2 / 4 := by
  have h := φ_sq
  intro x hx
  simp only [dodV, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rw [norm_sq_pt] <;> nlinarith [h]

theorem dod_norm (x : P3) (hx : x ∈ dod) : ‖x‖ ^ 2 ≤ 3 * φ ^ 2 / 4 := by
  have hR : 0 ≤ Real.sqrt (3 * φ ^ 2 / 4) := Real.sqrt_nonneg _
  have hsub : dod ⊆ Metric.closedBall 0 (Real.sqrt (3 * φ ^ 2 / 4)) := by
    apply convexHull_min _ (convex_closedBall 0 _)
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [dodV_norm y hy]
  have := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  have h2 := pow_le_pow_left₀ (norm_nonneg x) this 2
  rwa [Real.sq_sqrt (by positivity)] at h2

/-- The optimal edge: `s = 2√2/(3φ)`. -/
noncomputable def sd : ℝ := 2 * Real.sqrt 2 / (3 * φ)

theorem sd_pos : 0 < sd := by unfold sd; have := φ_pos; positivity

theorem sd_phi : sd * φ = 2 * Real.sqrt 2 / 3 := by unfold sd; have := φ_pos; field_simp

theorem centre_tet_dod (s : ℝ) (hs0 : 0 ≤ s) (hs : s < sd) (g : P3 ≃ᵃⁱ[ℝ] P3) (hg : g '' tetra ⊆ s • dod) :
    (0 : P3) ∈ interior (g '' tetra) := by
  have hφ := φ_pos
  refine centre_of_facet_width (fun _ => 1 / 4) a v rfl v_mem v_one norm_a dod_norm hs0 ?_ g hg
  have h1 : s * φ < 2 * Real.sqrt 2 / 3 := by rw [← sd_phi]; exact mul_lt_mul_of_pos_right hs hφ
  have h2 : 0 ≤ s * φ := by positivity
  nlinarith [s2, mul_self_lt_mul_self h2 h1]

/-! ## The packing: the cube packing inside the inscribed cube -/

theorem convS : Convex ℝ (sd • dod) := (convex_convexHull ℝ _).smul _

/-- The corners `(±√2/3, ±√2/3, ±√2/3)` are vertices of the scaled dodecahedron. -/
theorem corner (e0 e1 e2 : ℝ) (h0 : e0 = 1 ∨ e0 = -1) (h1 : e1 = 1 ∨ e1 = -1) (h2 : e2 = 1 ∨ e2 = -1) :
    pt (e0 * (Real.sqrt 2 / 3)) (e1 * (Real.sqrt 2 / 3)) (e2 * (Real.sqrt 2 / 3)) ∈ sd • dod := by
  refine Set.mem_smul_set.mpr ⟨pt (e0 * (φ / 2)) (e1 * (φ / 2)) (e2 * (φ / 2)), subset_convexHull ℝ _ ?_, ?_⟩
  · rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      simp [dodV]
  · have h := sd_phi
    ext i; fin_cases i <;> simp
    · linear_combination (e0 / 2) * h
    · linear_combination (e1 / 2) * h
    · linear_combination (e2 / 2) * h

theorem comb {A B C : P3} (hA : A ∈ sd • dod) (hB : B ∈ sd • dod) (hC : C ∈ sd • dod) :
    (1 / 2 : ℝ) • A + (1 / 4 : ℝ) • B + (1 / 4 : ℝ) • C ∈ sd • dod := by
  have hm := convS hB hC (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h := convS hA hm (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert h using 1
  simp only [smul_add, smul_smul]; norm_num; abel

theorem vertex_mem (j : Fin 4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : ε • t1 (v j) ∈ sd • dod := by
  have m : ∀ e0 e1 e2 : ℝ, (e0 = 1 ∨ e0 = -1) → (e1 = 1 ∨ e1 = -1) → (e2 = 1 ∨ e2 = -1) →
      pt (ε * e0 * (Real.sqrt 2 / 3)) (ε * e1 * (Real.sqrt 2 / 3)) (ε * e2 * (Real.sqrt 2 / 3)) ∈ sd • dod := by
    intro e0 e1 e2 h0 h1 h2
    apply corner <;> rcases hε with rfl | rfl <;> [rcases h0 with rfl | rfl; rcases h0 with rfl | rfl;
      rcases h1 with rfl | rfl; rcases h1 with rfl | rfl; rcases h2 with rfl | rfl; rcases h2 with rfl | rfl] <;>
      norm_num
  have o : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have n : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  fin_cases j
  · convert m 1 1 1 o o o using 1
    ext i; fin_cases i <;> simp [t1_apply, p1, v, sig] <;> ring
  · convert comb (m 1 (-1) (-1) o n n) (m 1 1 (-1) o o n) (m 1 (-1) 1 o n o) using 1
    ext i; fin_cases i <;> simp [t1_apply, p1, v, sig] <;> ring
  · convert comb (m (-1) 1 (-1) n o n) (m 1 1 (-1) o o n) (m (-1) 1 1 n o o) using 1
    ext i; fin_cases i <;> simp [t1_apply, p1, v, sig] <;> ring
  · convert comb (m (-1) (-1) 1 n n o) (m 1 (-1) 1 o n o) (m (-1) 1 1 n o o) using 1
    ext i; fin_cases i <;> simp [t1_apply, p1, v, sig] <;> ring

theorem t1_inside_dod : t1 '' tetra ⊆ sd • dod :=
  image_tetra_sub t1 convS fun j => by simpa using vertex_mem j 1 (Or.inl rfl)

theorem t2_inside_dod : t2 '' tetra ⊆ sd • dod :=
  image_tetra_sub t2 convS fun j => by
    have := vertex_mem j (-1) (Or.inr rfl)
    rw [neg_one_smul] at this
    simpa [t2_apply, t1_apply] using this

noncomputable def tetDodPacking : Packing tetra dod sd 2 where
  g := ![t1, t2]
  inside := by
    intro i; fin_cases i
    · exact t1_inside_dod
    · exact t2_inside_dod
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact t12_disjoint.symm
    · exact t12_disjoint
    · exact absurd rfl hij

end PackingOptimality.TetInDod

namespace PackingOptimality

open TetInCube TetInDod

/-- **Two tetrahedra in a dodecahedron: edge `2√2/(3φ)` is optimal.** -/
theorem tetindod_n02 : Nonempty (Packing tetra dod sd 2) ∧ ∀ s : ℝ, 0 ≤ s → Packing tetra dod s 2 → sd ≤ s := by
  refine ⟨⟨tetDodPacking⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : P3) (fun g hg => centre_tet_dod s hs h g hg) le_rfl P

end PackingOptimality
