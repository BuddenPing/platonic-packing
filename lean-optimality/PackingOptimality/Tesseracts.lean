import PackingOptimality.LemmaF4
import PackingOptimality.CentreGeneral

/-!
# Tesseracts in a tesseract, n = 2, …, 16: side 2 is optimal

Lemma F in dimension 4 (`LemmaF4.lemmaF4`) gives the cube centre lemma in dimension 4
(`CentreGeneral.centre_of_lemmaF`): a unit 4-cube inside a 4-cube of side `s < 2` contains the centre. So any
two such cubes share an interior point, and the 2×2×2×2 grid gives side 2 for every `2 ≤ n ≤ 16`. The result
s₄(2) = 2 is due to Hiroaki Hosono, with a computer-assisted far region; the proof here has no computer search.
-/

namespace PackingOptimality

open Set
open scoped Pointwise

/-- **The cube centre lemma in dimension 4.** -/
theorem centre4 (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2)
    (g : EuclideanSpace ℝ (Fin 4) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 4)) (hg : g '' cube 4 ⊆ s • cube 4) :
    (s / 2) • WithLp.toLp 2 (fun _ => (1 : ℝ)) ∈ interior (g '' cube 4) :=
  CentreGeneral.centre_of_lemmaF LemmaF4.lemmaF4 s hs0 hs g hg

/-- **Tesseracts in a tesseract, 2 ≤ n ≤ 16: side 2 is optimal.** -/
theorem c8inc8_plateau {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 16) :
    Nonempty (Packing (cube 4) (cube 4) 2 n) ∧ ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s n → 2 ≤ s :=
  cube_plateau_of_centre_lemma (d := 4) (by norm_num) centre4 hn2 hn

theorem c8inc8_n02 : Nonempty (Packing (cube 4) (cube 4) 2 2) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 2 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n03 : Nonempty (Packing (cube 4) (cube 4) 2 3) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 3 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n04 : Nonempty (Packing (cube 4) (cube 4) 2 4) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 4 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n05 : Nonempty (Packing (cube 4) (cube 4) 2 5) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 5 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n06 : Nonempty (Packing (cube 4) (cube 4) 2 6) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 6 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n07 : Nonempty (Packing (cube 4) (cube 4) 2 7) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 7 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n08 : Nonempty (Packing (cube 4) (cube 4) 2 8) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 8 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n09 : Nonempty (Packing (cube 4) (cube 4) 2 9) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 9 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n10 : Nonempty (Packing (cube 4) (cube 4) 2 10) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 10 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n11 : Nonempty (Packing (cube 4) (cube 4) 2 11) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 11 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n12 : Nonempty (Packing (cube 4) (cube 4) 2 12) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 12 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n13 : Nonempty (Packing (cube 4) (cube 4) 2 13) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 13 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n14 : Nonempty (Packing (cube 4) (cube 4) 2 14) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 14 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)
theorem c8inc8_n15 : Nonempty (Packing (cube 4) (cube 4) 2 15) ∧
    ∀ s : ℝ, 0 ≤ s → Packing (cube 4) (cube 4) s 15 → 2 ≤ s := c8inc8_plateau (by norm_num) (by norm_num)

end PackingOptimality
