import DPCut.BipartiteGraphs
import DPCut.CutReconstruction

/-! The bipartite family lower bound, with a square right-hand size for calibration. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

theorem bipartite_lower_bound {n r k : ℕ} (h : r + k ^ 2 ≤ n) (hr : 0 < r) (hk : 0 < k)
    {ε δ β γ A : ℝ} {M : Kernel (Weights n) (Weights n)} [IsMarkovKernel M]
    (hδ : 0 ≤ δ) (hβ : β ≤ 1 / 40) (hγ : 0 ≤ γ) (hA : 0 ≤ A)
    (hsmall : γ * k ≤ 1 / 2048) (hDP : EdgeDP M ε δ)
    (hacc : ∀ w : Weights n, Nonnegative w → HighProbability (M w) β
      (fun h => AllCuts w h γ A))
    {t : ℕ} (ht : 0 < t) (he : Real.exp ((t : ℝ) * ε) ≤ 3)
    (hd : δ * (∑ j ∈ Finset.range t, Real.exp ((j : ℝ) * ε)) ≤ 3 / 100) :
    (t : ℝ) * r * k ≤ 2048 * A := by
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hkk : 0 < k ^ 2 := pow_pos hk _
  haveI : Nonempty (Fin (k ^ 2)) := Fin.pos_iff_nonempty.mp hkk
  obtain ⟨x, y, H, hx, hy, hdist⟩ := private_cut_reconstruction hδ hβ hDP hacc
    (bitGraph (bipartiteEdge h) t) (bitGraph_nonnegative _ (by positivity)) ht he hd
    (bitGraph_flip_distance _ (by positivity))
  have hh := bipartite_compatible_distance h hkk (by positivity) hγ x y hx hy
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow] at hdist
  have hs : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = k := by simp
  rw [hs] at hh
  push_cast at hh
  have hm := mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℝ) ≤ t)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have htr : (0 : ℝ) ≤ (t : ℝ) * r * (k : ℝ) ^ 2 := by positivity
  have hsm := mul_le_mul_of_nonneg_right hsmall htr
  have hka : 0 ≤ (k : ℝ) * A := mul_nonneg hkr.le hA
  have hbound : (t : ℝ) * r * (k : ℝ) ^ 2 ≤ 2048 * k * A := by nlinarith
  nlinarith

end DPCut
