import DPCut.BipartiteGraphs
import DPCut.CutReconstruction

/-! The star family supplies the (1-gamma) dependence near gamma = 1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

def starEdge {n r : ℕ} (h : r + 1 ≤ n) (i : Fin r) : Edge n := bipartiteEdge h (i, 0)

lemma cut_star {n r : ℕ} (h : r + 1 ≤ n) (t : ℝ) (x : Fin r → Bool)
    (S : Finset (Fin r)) :
    cut (bitGraph (starEdge h) t x) (S.image (bipartiteLeft h)) =
      ∑ i ∈ S, if x i then t else 0 := by
  rw [cut, bitGraph, pairing_embedWeights]
  simp only [cutQuery, starEdge, bipartiteEdge, left_mem_left, right_not_mem_left,
    iff_false, ite_not, mul_ite, mul_one, mul_zero]
  simp

lemma star_compatible_distance {n r : ℕ} (h : r + 1 ≤ n)
    {t γ A : ℝ} (x y : Fin r → Bool) {H : Weights n}
    (hx : AllCuts (bitGraph (starEdge h) t x) H γ A)
    (hy : AllCuts (bitGraph (starEdge h) t y) H γ A) :
    (1 - γ) * t * hamming x y ≤ 4 * A := by
  classical
  let S : (Fin r → Bool) → (Fin r → Bool) → Finset (Fin r) :=
    fun x y => Finset.univ.filter (fun i => x i = true ∧ y i = false)
  have hdir (x y : Fin r → Bool)
      (hx : AllCuts (bitGraph (starEdge h) t x) H γ A)
      (hy : AllCuts (bitGraph (starEdge h) t y) H γ A) :
      (1 - γ) * t * ((S x y).card : ℝ) ≤ 2 * A := by
    have hcx : cut (bitGraph (starEdge h) t x) ((S x y).image (bipartiteLeft h)) =
        t * (S x y).card := by
      rw [cut_star]
      have he : (∑ i ∈ S x y, if x i then t else 0) = ∑ _i ∈ S x y, t := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [(Finset.mem_filter.mp hi).2.1]
      rw [he]; simp [mul_comm]
    have hcy : cut (bitGraph (starEdge h) t y) ((S x y).image (bipartiteLeft h)) = 0 := by
      rw [cut_star]
      apply Finset.sum_eq_zero
      intro i hi
      simp [(Finset.mem_filter.mp hi).2.2]
    have h₁ := (abs_le.mp (hx ((S x y).image (bipartiteLeft h)))).2
    have h₂ := (abs_le.mp (hy ((S x y).image (bipartiteLeft h)))).1
    rw [hcx] at h₁
    rw [hcy] at h₂
    nlinarith
  have he : hamming x y = ((S x y).card : ℝ) + (S y x).card := by
    simp only [hamming, S, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; cases x i <;> cases y i <;> norm_num
  rw [he]
  linarith [hdir x y hx hy, hdir y x hy hx]

theorem star_lower_bound {n r : ℕ} (h : r + 1 ≤ n) (hr : 0 < r)
    {ε δ β γ A : ℝ} {M : Kernel (Weights n) (Weights n)} [IsMarkovKernel M]
    (hδ : 0 ≤ δ) (hβ : β ≤ 1 / 40) (hγ : γ < 1) (hDP : EdgeDP M ε δ)
    (hacc : ∀ w : Weights n, Nonnegative w → HighProbability (M w) β
      (fun h => AllCuts w h γ A))
    {t : ℕ} (ht : 0 < t) (he : Real.exp ((t : ℝ) * ε) ≤ 3)
    (hd : δ * (∑ j ∈ Finset.range t, Real.exp ((j : ℝ) * ε)) ≤ 3 / 100) :
    (1 - γ) * t * r ≤ 20 * A := by
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  obtain ⟨x, y, H, hx, hy, hdist⟩ := private_cut_reconstruction hδ hβ hDP hacc
    (bitGraph (starEdge h) t) (bitGraph_nonnegative _ (by positivity)) ht he hd
    (bitGraph_flip_distance _ (by positivity))
  have hh := star_compatible_distance h x y hx hy
  simp only [Fintype.card_fin] at hdist
  have hm := mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (sub_nonneg.mpr hγ.le) (by positivity : (0 : ℝ) ≤ t))
  nlinarith

end DPCut
