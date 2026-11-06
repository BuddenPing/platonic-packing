import PackingOptimality.TetInCube

/-!
# Two tetrahedra in an octahedron: edge 2/√3 is optimal

**Theorem (`tetinoct_n02`).** Two regular tetrahedra of edge 1 fit in a regular octahedron of edge `2/√3`, and in
no smaller one.

**Lower bound.** The facet-width lemma, with the octahedron `{‖x‖₁ ≤ √2/2}` inside the ball of radius `√2/2`:
`s² / 2 ≥ 2/3`.

**Construction.** Reflect by the Householder map `H` with `H (1,1,1)/√3 = e₃`, and lift by `(√6/12) e₃`. The
apex goes to the octahedron's vertex `(√6/3) e₃`, and the base lies in the plane `z = 0`, inside the equatorial
square. Add the point reflection.
-/

namespace PackingOptimality.TetInOct

open Set FacetWidth OctInCube TetInCube
open scoped Pointwise RealInnerProductSpace

theorem s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
theorem s3pos : 0 < Real.sqrt 3 := by positivity
theorem s3lt : Real.sqrt 3 < 2 := by nlinarith [s3, s3pos]

theorem octa_norm (x : P3) (hx : x ∈ octa) : ‖x‖ ^ 2 ≤ 1 / 2 := by
  have hx' : |x 0| + |x 1| + |x 2| ≤ Real.sqrt 2 / 2 := hx
  rw [← real_inner_self_eq_norm_sq, CentreGeneral.inner_sum, Fin.sum_univ_three]
  have : (|x 0| + |x 1| + |x 2|) ^ 2 ≤ 1 / 2 := by
    have h0 : 0 ≤ |x 0| + |x 1| + |x 2| := by positivity
    nlinarith [s2]
  nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2)]

/-- **The tetrahedron centre lemma in an octahedron.** -/
theorem centre_tet_oct (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * Real.sqrt 3 / 3) (g : P3 ≃ᵃⁱ[ℝ] P3)
    (hg : g '' tetra ⊆ s • octa) : (0 : P3) ∈ interior (g '' tetra) :=
  centre_of_facet_width (fun _ => 1 / 4) a v rfl v_mem v_one norm_a octa_norm hs0
    (by nlinarith [s3, s3pos]) g hg

/-! ## The construction -/

/-- The Householder reflection with `H (1,1,1) = √3 e₃`. -/
noncomputable def Hh : P3 →ₗ[ℝ] P3 where
  toFun y := pt ((3 - Real.sqrt 3) / 6 * y 0 - (3 + Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
    (-(3 + Real.sqrt 3) / 6 * y 0 + (3 - Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
    (Real.sqrt 3 / 3 * y 0 + Real.sqrt 3 / 3 * y 1 + Real.sqrt 3 / 3 * y 2)
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c y := by ext i; fin_cases i <;> simp <;> ring

theorem Hh_apply (y : P3) : Hh y = pt ((3 - Real.sqrt 3) / 6 * y 0 - (3 + Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
    (-(3 + Real.sqrt 3) / 6 * y 0 + (3 - Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
    (Real.sqrt 3 / 3 * y 0 + Real.sqrt 3 / 3 * y 1 + Real.sqrt 3 / 3 * y 2) := rfl

/-- Ring normalisation that also replaces `√3²` by 3 and `√2²` by 2. -/
macro "sqrt_ring" : tactic => `(tactic| (ring_nf; simp only [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
  Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]; ring_nf))

/-- Split `|c₀| + |c₁| + |c₂| ≤ B` into its sign cases and close each by `nlinarith` with the radical facts. -/
macro "l1_tac" : tactic => `(tactic| (
  have p2 := s2pos; have p3 := s3pos; have p6 := mul_pos s2pos s3pos
  have e3 := s3; have e2 := s2; have l3 := s3lt
  repeat rw [abs_eq_max_neg]
  simp only [max_def]
  repeat (split_ifs <;> try nlinarith)
  all_goals nlinarith))

noncomputable def Hiso3 : P3 ≃ₗᵢ[ℝ] P3 :=
  (LinearEquiv.ofInvolutive Hh (fun y => by
      ext i; fin_cases i <;> simp [Hh_apply] <;> sqrt_ring)).isometryOfInner
    (fun x y => by
      show ⟪Hh x, Hh y⟫ = ⟪x, y⟫
      simp only [CentreGeneral.inner_sum, Fin.sum_univ_three, Hh_apply, pt_zero, pt_one, pt_two]
      sqrt_ring)


/-! ### Barycentric coordinates and convexity -/

theorem bary (y : P3) : y = ∑ j, ((fun _ : Fin 4 => (1 / 4 : ℝ)) j + ⟪a j, y⟫) • v j := by
  ext i
  simp only [inner_a, Fin.sum_univ_four, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v, sig]
  fin_cases i <;> simp <;> sqrt_ring

theorem bary_sum (y : P3) : ∑ j, ((fun _ : Fin 4 => (1 / 4 : ℝ)) j + ⟪a j, y⟫) = 1 := by
  simp only [inner_a, Fin.sum_univ_four, sig]; simp; ring

/-- An affine map sends the tetrahedron into a convex set containing the images of its vertices. -/
theorem image_tetra_sub (g : P3 ≃ᵃⁱ[ℝ] P3) {S : Set P3} (hS : Convex ℝ S) (hv : ∀ j, g (v j) ∈ S) :
    g '' tetra ⊆ S := by
  rintro _ ⟨y, hy, rfl⟩
  have hgx : ∀ x, g x = g.linearIsometryEquiv x + g 0 := fun x => by have := g.map_vadd 0 x; simpa using this
  set lam : Fin 4 → ℝ := fun j => (fun _ : Fin 4 => (1 / 4 : ℝ)) j + ⟪a j, y⟫
  have hl0 : ∀ j ∈ Finset.univ, 0 ≤ lam j := fun j _ => hy j
  have hl1 : ∑ j, lam j = 1 := bary_sum y
  have : g y = ∑ j, lam j • g (v j) := by
    conv_lhs => rw [bary y]
    rw [hgx, map_sum]
    simp only [map_smul, hgx (v _), smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hl1, one_smul]
    rfl
  rw [this]
  exact hS.sum_mem hl0 hl1 fun j _ => hv j

theorem convex_octa : Convex ℝ octa := by
  intro x hx y hy p q hp hq hpq
  have hx' : |x 0| + |x 1| + |x 2| ≤ Real.sqrt 2 / 2 := hx
  have hy' : |y 0| + |y 1| + |y 2| ≤ Real.sqrt 2 / 2 := hy
  show |(p • x + q • y) 0| + |(p • x + q • y) 1| + |(p • x + q • y) 2| ≤ Real.sqrt 2 / 2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e : ∀ i, |p * x i + q * y i| ≤ p * |x i| + q * |y i| := fun i => by
    calc |p * x i + q * y i| ≤ |p * x i| + |q * y i| := abs_add_le _ _
      _ = p * |x i| + q * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
  have := e 0; have := e 1; have := e 2
  have hx2 := mul_le_mul_of_nonneg_left hx' hp
  have hy2 := mul_le_mul_of_nonneg_left hy' hq
  have : p * (Real.sqrt 2 / 2) + q * (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by rw [← add_mul, hpq, one_mul]
  nlinarith

theorem mem_smul_octa {t : ℝ} (ht : 0 < t) {x : P3} (hx : |x 0| + |x 1| + |x 2| ≤ t * (Real.sqrt 2 / 2)) :
    x ∈ t • octa := by
  refine ⟨t⁻¹ • x, ?_, by simp [smul_smul, ht.ne']⟩
  show |(t⁻¹ • x) 0| + |(t⁻¹ • x) 1| + |(t⁻¹ • x) 2| ≤ Real.sqrt 2 / 2
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr ht)]
  rw [← mul_add, ← mul_add, inv_mul_le_iff₀ ht]; exact hx

/-! ### The packing -/

noncomputable def q3 : P3 := pt 0 0 (Real.sqrt 2 * Real.sqrt 3 / 12)

noncomputable def h1 : P3 ≃ᵃⁱ[ℝ] P3 := Hiso3.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ P3 q3)

theorem h1_apply (y : P3) : h1 y = q3 + Hh y := rfl

theorem h1_coord (y : P3) :
    h1 y = pt ((3 - Real.sqrt 3) / 6 * y 0 - (3 + Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
      (-(3 + Real.sqrt 3) / 6 * y 0 + (3 - Real.sqrt 3) / 6 * y 1 + Real.sqrt 3 / 3 * y 2)
      (Real.sqrt 3 / 3 * y 0 + Real.sqrt 3 / 3 * y 1 + Real.sqrt 3 / 3 * y 2 + Real.sqrt 2 * Real.sqrt 3 / 12) := by
  rw [h1_apply, Hh_apply]; ext i; fin_cases i <;> simp [q3] <;> ring

theorem scale_pos : (0 : ℝ) < 2 * Real.sqrt 3 / 3 := by positivity

theorem h1_vertex (j : Fin 4) : h1 (v j) ∈ (2 * Real.sqrt 3 / 3) • octa := by
  apply mem_smul_octa scale_pos
  rw [h1_coord]
  simp only [pt_zero, pt_one, pt_two]
  fin_cases j <;> simp [v, sig] <;> l1_tac

theorem h1_inside : h1 '' tetra ⊆ (2 * Real.sqrt 3 / 3) • octa :=
  image_tetra_sub h1 (convex_octa.smul _) h1_vertex

theorem h1_sep {y : P3} (hy : y ∈ tetra) : 0 ≤ coordL 2 (h1 y) := by
  obtain ⟨f0, -, -, -⟩ := mem_tetra.mp hy
  rw [coordL_apply, h1_coord, pt_two]
  nlinarith [s2, s3, s2pos, s3pos, mul_pos s2pos s3pos]

noncomputable def tetOctPacking : Packing tetra octa (2 * Real.sqrt 3 / 3) 2 where
  g := ![h1, h1.trans (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv]
  inside := by
    intro i; fin_cases i
    · exact h1_inside
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hze⟩ := Set.mem_smul_set.mp (h1_inside ⟨y, hy, rfl⟩)
      refine Set.mem_smul_set.mpr ⟨-z, ?_, ?_⟩
      · have hz' : |z 0| + |z 1| + |z 2| ≤ Real.sqrt 2 / 2 := hz
        show |(-z) 0| + |(-z) 1| + |(-z) 2| ≤ Real.sqrt 2 / 2
        simpa using hz'
      · show _ = -(h1 y); rw [smul_neg, hze]
  disjoint := by
    have key : Disjoint (interior ((h1.trans (LinearIsometryEquiv.neg ℝ (E := P3)).toAffineIsometryEquiv) '' tetra))
        (interior (h1 '' tetra)) := by
      apply interior_disjoint_of_separated (coordL 2) (coordL_surjective 2) (c := 0)
      · rintro _ ⟨y, hy, rfl⟩
        simp only [Set.mem_preimage, Set.mem_Iic]
        show coordL 2 (-(h1 y)) ≤ 0
        rw [map_neg]; linarith [h1_sep hy]
      · rintro _ ⟨y, hy, rfl⟩; exact h1_sep hy
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key.symm
    · exact key
    · exact absurd rfl hij

end PackingOptimality.TetInOct

namespace PackingOptimality

open TetInCube OctInCube TetInOct

/-- **Two tetrahedra in an octahedron: edge `2/√3 = 2√3/3` is optimal.** -/
theorem tetinoct_n02 : Nonempty (Packing tetra octa (2 * Real.sqrt 3 / 3) 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing tetra octa s 2 → 2 * Real.sqrt 3 / 3 ≤ s := by
  refine ⟨⟨tetOctPacking⟩, fun s hs P => ?_⟩
  by_contra h
  push Not at h
  exact no_packing_two_of_common_point (0 : P3) (fun g hg => centre_tet_oct s hs h g hg) le_rfl P

end PackingOptimality
