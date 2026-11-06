import PackingOptimality.FacetWidth
import PackingOptimality.OctInCube

/-!
# Two tetrahedra in a cube: side 2√2/3 is optimal

**Theorem (`tetincub_n02`).** Two regular tetrahedra of edge 1 fit in a cube of edge `2√2/3`, and in no smaller
cube.

**Lower bound.** This is the facet-width lemma. If the cube's centre is not inside a tetrahedron, a face plane
separates them, and the opposite vertex lies at height `√(2/3)` beyond that plane. That vertex is within
`(s/2)√3` of the centre, so `√(2/3) ≤ (s/2)√3`, that is `s ≥ 2√2/3`.

**Construction.** Translate the tetrahedron by `(√2/12)(1, 1, 1)`, so that its apex is a corner of the cube and
its opposite face lies in the plane `x + y + z = 0` through the centre. Add its point reflection.
-/

namespace PackingOptimality.TetInCube

open Set FacetWidth OctInCube
open scoped Pointwise RealInnerProductSpace

/-- The face normals `(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)` (also the vertex directions). -/
noncomputable def sig : Fin 4 → P3 := ![pt 1 1 1, pt 1 (-1) (-1), pt (-1) 1 (-1), pt (-1) (-1) 1]

noncomputable def a (j : Fin 4) : P3 := (Real.sqrt 2 / 2) • sig j
noncomputable def v (j : Fin 4) : P3 := (Real.sqrt 2 / 4) • sig j

/-- The regular tetrahedron of edge 1 with vertices `(√2/4) σⱼ`, centred at its centroid: barycentric
coordinates `1/4 + (√2/2) ⟨σⱼ, y⟩ ≥ 0`. -/
noncomputable def tetra : Set P3 := {y | ∀ j, 0 ≤ (fun _ : Fin 4 => (1 / 4 : ℝ)) j + ⟪a j, y⟫}

theorem s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
theorem s2pos : 0 < Real.sqrt 2 := by positivity

theorem inner_a (j : Fin 4) (y : P3) :
    ⟪a j, y⟫ = Real.sqrt 2 / 2 * (sig j 0 * y 0 + sig j 1 * y 1 + sig j 2 * y 2) := by
  simp only [a, inner_smul_left, CentreGeneral.inner_sum, Fin.sum_univ_three, RCLike.conj_to_real]
  try ring

theorem mem_tetra {y : P3} : y ∈ tetra ↔
    0 ≤ 1 / 4 + Real.sqrt 2 / 2 * (y 0 + y 1 + y 2) ∧ 0 ≤ 1 / 4 + Real.sqrt 2 / 2 * (y 0 - y 1 - y 2) ∧
    0 ≤ 1 / 4 + Real.sqrt 2 / 2 * (-y 0 + y 1 - y 2) ∧ 0 ≤ 1 / 4 + Real.sqrt 2 / 2 * (-y 0 - y 1 + y 2) := by
  simp only [tetra, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    rw [inner_a] at h0 h1 h2 h3
    simp [sig] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨f0, f1, f2, f3⟩ j
    rw [inner_a]
    fin_cases j <;> simp [sig] <;> linarith

theorem v_mem (j : Fin 4) : v j ∈ tetra := by
  rw [mem_tetra]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> fin_cases j <;> simp [v, sig] <;> nlinarith [s2]

theorem v_one (j : Fin 4) : 1 ≤ (fun _ : Fin 4 => (1 / 4 : ℝ)) j + ⟪a j, v j⟫ := by
  rw [inner_a]
  fin_cases j <;> simp [v, sig] <;> nlinarith [s2]

theorem norm_a (j : Fin 4) : ‖a j‖ ^ 2 * (2 / 3) ≤ 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_a]
  fin_cases j <;> simp [a, sig] <;> nlinarith [s2]

theorem cube_norm (x : P3) (hx : x ∈ cubeC) : ‖x‖ ^ 2 ≤ 3 / 4 := by
  rw [← real_inner_self_eq_norm_sq, CentreGeneral.inner_sum, Fin.sum_univ_three]
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  rw [abs_le] at h0 h1 h2
  nlinarith

/-- **The tetrahedron centre lemma in a cube.** -/
theorem centre_tet (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * Real.sqrt 2 / 3) (g : P3 ≃ᵃⁱ[ℝ] P3)
    (hg : g '' tetra ⊆ s • cubeC) : (0 : P3) ∈ interior (g '' tetra) :=
  centre_of_facet_width (fun _ => 1 / 4) a v rfl v_mem v_one norm_a cube_norm hs0
    (by nlinarith [s2, s2pos]) g hg

/-! ## The packing -/

noncomputable def p1 : P3 := pt (Real.sqrt 2 / 12) (Real.sqrt 2 / 12) (Real.sqrt 2 / 12)

noncomputable def t1 : P3 ≃ᵃⁱ[ℝ] P3 := AffineIsometryEquiv.constVAdd ℝ P3 p1
noncomputable def t2 : P3 ≃ᵃⁱ[ℝ] P3 := t1.trans (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv

theorem t1_apply (y : P3) : t1 y = p1 + y := rfl
theorem t2_apply (y : P3) : t2 y = -(p1 + y) := rfl

theorem t1_bound {y : P3} (hy : y ∈ tetra) (i : Fin 3) : |t1 y i| ≤ 2 * Real.sqrt 2 / 3 / 2 := by
  obtain ⟨f0, f1, f2, f3⟩ := mem_tetra.mp hy
  rw [t1_apply, PiLp.add_apply, abs_le]
  fin_cases i <;> simp [p1] <;> constructor <;> nlinarith [s2, s2pos]

theorem pos3 : (0 : ℝ) < 2 * Real.sqrt 2 / 3 := by positivity

theorem t1_inside : t1 '' tetra ⊆ (2 * Real.sqrt 2 / 3) • cubeC := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_smul_of_coord pos3 fun i => t1_bound hy i

theorem t2_inside : t2 '' tetra ⊆ (2 * Real.sqrt 2 / 3) • cubeC := by
  rintro _ ⟨y, hy, rfl⟩
  refine mem_smul_of_coord pos3 fun i => ?_
  rw [t2_apply, PiLp.neg_apply, abs_neg, ← t1_apply]; exact t1_bound hy i

theorem sum3_t1 {y : P3} (hy : y ∈ tetra) : 0 ≤ sum3 (t1 y) := by
  obtain ⟨f0, -, -, -⟩ := mem_tetra.mp hy
  rw [sum3_apply, t1_apply, PiLp.add_apply, PiLp.add_apply, PiLp.add_apply]
  simp only [p1, pt_zero, pt_one, pt_two]
  nlinarith [s2, s2pos]

theorem t12_disjoint : Disjoint (interior (t2 '' tetra)) (interior (t1 '' tetra)) := by
  apply interior_disjoint_of_separated sum3 sum3_surjective (c := 0)
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [t2_apply, map_neg, ← t1_apply]; linarith [sum3_t1 hy]
  · rintro _ ⟨y, hy, rfl⟩
    exact sum3_t1 hy

noncomputable def tetPacking : Packing tetra cubeC (2 * Real.sqrt 2 / 3) 2 where
  g := ![t1, t2]
  inside := by
    intro i; fin_cases i
    · exact t1_inside
    · exact t2_inside
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact t12_disjoint.symm
    · exact t12_disjoint
    · exact absurd rfl hij

end PackingOptimality.TetInCube

namespace PackingOptimality

open TetInCube OctInCube

/-- **Two tetrahedra in a cube: side 2√2/3 is optimal.** -/
theorem tetincub_n02 : Nonempty (Packing tetra cubeC (2 * Real.sqrt 2 / 3) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing tetra cubeC s 2 → 2 * Real.sqrt 2 / 3 ≤ s := by
  refine ⟨⟨tetPacking⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : P3) (fun g hg => centre_tet s hs h g hg) le_rfl P

end PackingOptimality
