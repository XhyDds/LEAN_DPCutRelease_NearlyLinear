import DPCut.WeightedChiSquare
import DPCut.Statements

/-! Lemma 15 (`lem:concentration_chi-squares`): the signed Laurent–Massart inequality. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DPCut

theorem lemma15 : WeightedChiSquareStatement := by
  intro n a t ht
  exact weighted_chiSquare_tail a (norm_nonneg a)
    (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i) ht

/-- The same statement for independent standard normals on any probability space. -/
theorem lemma15_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (Z : Fin n → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, μ.map (Z i) = gaussianReal 0 1) (a : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    prob μ {ω | |∑ i, a i * (Z i ω ^ 2 - 1)| >
      2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + ‖a‖ * t)} ≤ 2 * Real.exp (-t) := by
  have hmap : μ.map (fun ω i => Z i ω) = standardGaussian n := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hZ i).aemeasurable)).mp hIndep
    simpa only [hLaw, standardGaussian] using h
  have hm : Measurable (fun ω i => Z i ω) := measurable_pi_lambda _ hZ
  have hevent : MeasurableSet {z : Fin n → ℝ | |∑ i, a i * (z i ^ 2 - 1)| >
      2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + ‖a‖ * t)} := by
    apply measurableSet_lt measurable_const
    fun_prop
  have h := lemma15 n a t ht
  unfold prob at h ⊢
  rw [← hmap, Measure.map_apply hm hevent] at h
  exact h

end DPCut
