import DPCut.MatrixFactorAlgorithm
import DPCut.MatrixPSDAlgorithm
import DPCut.GaussianQuadratic

/-! The recursive factor gives exactly the covariance Gaussian law already
used in the release proof. No spectral-factor computation is assumed. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal MatrixOrder
namespace DPCut.MatrixElimination

@[fun_prop] lemma measurable_lowerBlock (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) × Mat n => lowerBlock p.1 p.2.1 p.2.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun _ => ?_) j
    · exact measurable_fst
    · exact measurable_const
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [lowerBlock_succ_zero]; fun_prop
    · simp only [lowerBlock_succ_succ]; fun_prop

lemma measurable_factor (n : ℕ) : Measurable (factor (n:=n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun M : Mat (n+1) => factor M)
    simp only [factor]
    apply (measurable_lowerBlock n).comp
      (f := fun M : Mat (n+1) => (Real.sqrt (M 0 0), (fun i => row M i / Real.sqrt (M 0 0)), factor (schur M)))
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk
    · unfold row; fun_prop
    · exact ih.comp (measurable_schur n)

lemma gaussian_map_eq_of_covariance {n : ℕ} (A B : Mat n) (hAB : A*Aᵀ = B*Bᵀ) :
    (standardGaussian n).map (fun z => A *ᵥ z) =
      (standardGaussian n).map (fun z => B *ᵥ z) := by
  have hA := measurable_mulVec A
  have hB := measurable_mulVec B
  letI := Measure.isProbabilityMeasure_map (μ := standardGaussian n) hA.aemeasurable
  letI := Measure.isProbabilityMeasure_map (μ := standardGaussian n) hB.aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.measurable hA, Measure.map_map L.measurable hB]
  let a : Fin n → ℝ := fun i => L (Pi.single i 1)
  have hL (M : Mat n) : L ∘ (fun z => M *ᵥ z) = (fun z => ∑ i, (a ᵥ* M) i * z i) := by
    ext z
    change L (M *ᵥ z) = _
    rw [strongDual_eq_sum]
    exact Matrix.dotProduct_mulVec a M z
  rw [hL A, hL B]
  change charFun ((gaussianProduct (Fin n)).map _) 1 = charFun ((gaussianProduct (Fin n)).map _) 1
  rw [gaussianProduct_map_sum, gaussianProduct_map_sum]
  have hsq : (∑ i, (a ᵥ* A) i ^ 2) = ∑ i, (a ᵥ* B) i ^ 2 := by
    simp only [pow_two]
    change (a ᵥ* A) ⬝ᵥ (a ᵥ* A) = (a ᵥ* B) ⬝ᵥ (a ᵥ* B)
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_vecMul, hAB,
      ← Matrix.mulVec_vecMul, Matrix.dotProduct_mulVec]
  have hv : (∑ i, (⟨(a ᵥ* A) i ^ 2, sq_nonneg _⟩ : ℝ≥0)) =
      ∑ i, (⟨(a ᵥ* B) i ^ 2, sq_nonneg _⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    exact (NNReal.coe_sum Finset.univ (fun i => (⟨(a ᵥ* A) i ^ 2, sq_nonneg _⟩ : ℝ≥0))).trans
      (hsq.trans (NNReal.coe_sum Finset.univ (fun i => (⟨(a ᵥ* B) i ^ 2, sq_nonneg _⟩ : ℝ≥0))).symm)
  rw [hv]

lemma factor_gaussian_law {n : ℕ} (M : Mat n) (hM : M.PosDef) :
    (standardGaussian n).map (fun z => factor M *ᵥ z) = gaussian M := by
  apply gaussian_map_eq_of_covariance
  rw [factor_correct M hM, posDef_transpose hM.posDef_sqrt,
    CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]

lemma factor_gaussianBatch_law {n : ℕ} (M : Mat n) (hM : M.PosDef) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => standardGaussian n)).map
      (fun z j => factor M *ᵥ z j) = gaussianBatch M k := by
  rw [Measure.pi_map_pi (fun _ : Fin k => (measurable_mulVec (factor M)).aemeasurable)]
  simp only [factor_gaussian_law M hM, gaussianBatch]

end DPCut.MatrixElimination
