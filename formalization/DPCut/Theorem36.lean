import DPCut.HierarchyCalibration

/-! Theorem 36, statistical conclusion, relative only to the explicit external
one-cut ARV contract. The hierarchy recursion and transfer are proved here. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

theorem theorem36 (o : InducedARVContract) : PrivateHierarchyStatement := by
  obtain ⟨CA, hCA, hrelease⟩ := theorem1_statistical
  refine ⟨o.balance, 512 * hierarchyRatioCoefficient o, CA, 2, o.balance_pos, o.balance_le,
    mul_pos (by norm_num) (hierarchyRatioCoefficient_pos o), hCA, by norm_num, ?_⟩
  intro η hη hη₁
  refine ⟨hierarchyAddCoefficient o, hierarchyAddCoefficient_pos o, ?_⟩
  intro ε hε hε₁ n hn
  let p : Parameters := ⟨η, ε, (n : ℝ)⁻¹ ^ 10, (n : ℝ)⁻¹ ^ 10⟩
  have hp : p.Valid := by
    simpa [p, applicationParameters, min_eq_left hε₁] using applicationParameters_valid hn hη hη₁ hε
  obtain ⟨M, hM, hgraph, hDP, hu⟩ := hrelease n hn p hp
  letI := hM
  let K := nonprivateHierarchyKernel o n
  let R : Kernel (Weights n) (Hierarchy n) :=
    ⟨fun w => (M w).bind K, measurable_bind_kernel M.measurable (K.measurable.comp measurable_snd)⟩
  letI : IsMarkovKernel R := ⟨fun w => probability_bind (M w) K K.measurable⟩
  have hτ := inverse_tenth_small hn |>.1
  refine ⟨R, inferInstance, hDP.postprocess hε.le hτ.le K, ?_⟩
  intro w hw
  have hgood := (hu w hw).and_ae (measurableSet_nonnegative measurable_id) (hgraph w hw)
  have hlog : 0 ≤ logFactor n 1 p := (by norm_num : (0 : ℝ) ≤ 1).trans (core_log_bounds hn (le_refl 1) p hp).one_le
  have hE : 0 ≤ CA * mainError n p := by
    have hγ := hp.1
    have he := hp.2.2.1
    unfold mainError
    positivity
  have hb : HighProbability (R w) ((n : ℝ)⁻¹ ^ 10 + (n : ℝ)⁻¹ ^ 10)
      (fun T => BalancedHierarchy o.balance T ∧ hcCost w T ≤
        (512 * hierarchyRatioCoefficient o) * Real.sqrt (Real.log n) * hcOptimum w +
        hierarchyAddCoefficient o * (CA * mainError n p) * n * (Real.log n) ^ (3 / 2 : ℝ)) := by
    apply hgood.bind K hτ.le hτ.le (Set.toFinite _ |>.measurableSet)
    intro h hh
    apply (nonprivateHierarchy_quality o hn hh.2).mono _ (Set.toFinite _ |>.measurableSet)
    intro T hT
    exact ⟨hT.1, hierarchy_calibrated_transfer o hn hw hη.le hη₁ hE hh.1 hT.1 hT.2⟩
  apply hb.weaken
  have hi := inverse_tenth_le_inverse_square hn
  convert add_le_add hi hi using 1
  ring

end DPCut
