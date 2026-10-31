import DPCut.QuadraticMoments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-! Orthogonal invariance and Gaussian quadratic forms, for Lemma 11. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal Matrix

namespace DPCut

lemma gaussianProduct_map_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (gaussianProduct ι).map (fun z => ∑ i, a i * z i) =
      gaussianReal 0 (∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) := by
  classical
  let f : ι → (ι → ℝ) → ℝ := fun i z => a i * z i
  have hm : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hi : iIndepFun f (gaussianProduct ι) :=
    iIndepFun_pi (fun i => (measurable_const_mul (a i)).aemeasurable)
  have hd (i : ι) : (gaussianProduct ι).map (f i) =
      gaussianReal 0 (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) := by
    have he := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
    calc
      _ = ((gaussianProduct ι).map (Function.eval i)).map (a i * ·) := by
        exact (Measure.map_map (measurable_const_mul (a i))
          (show Measurable (Function.eval i : (ι → ℝ) → ℝ) from measurable_pi_apply i)).symm
      _ = (gaussianReal 0 1).map (a i * ·) := by rw [show (gaussianProduct ι).map (Function.eval i) = _ from he]
      _ = _ := by simp [gaussianReal_map_const_mul]
  have hs (s : Finset (ι)) :
      (gaussianProduct ι).map (∑ i ∈ s, f i) =
        gaussianReal 0 (∑ i ∈ s, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, gaussianReal_zero_var]
      exact (Measure.map_const (μ := gaussianProduct ι) (0 : ℝ)).trans (by simp)
    | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      convert gaussianReal_add_gaussianReal_of_indepFun
        (hi.indepFun_finset_sum_of_notMem hm his).symm (hd i) ih using 1
      simp
  have hf : (∑ i : ι, f i) = (fun z => ∑ i, a i * z i) := by
    ext z
    simp [f]
  rw [← hf]
  exact hs Finset.univ


lemma measurable_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    Measurable (fun z => A.mulVec z) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

lemma strongDual_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    L z = ∑ i, L (Pi.single i 1) * z i := by
  calc
    L z = L (∑ i, z i • (Pi.single i 1 : ι → ℝ)) := by
      congr 1
      ext j
      simp [Pi.single_apply, Finset.sum_apply]
    _ = _ := by simp [map_sum, mul_comm]

/-- The concrete product normal law is invariant under an orthogonal change of coordinates. -/
lemma gaussianProduct_map_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) :
    (gaussianProduct ι).map (fun z => (U : Matrix ι ι ℝ).mulVec z) = gaussianProduct ι := by
  let M : Matrix ι ι ℝ := U
  have hm : Measurable (fun z => M.mulVec z) := measurable_mulVec M
  haveI : IsProbabilityMeasure ((gaussianProduct ι).map (fun z => M.mulVec z)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.measurable hm]
  let a : ι → ℝ := fun i => L (Pi.single i 1)
  have hL : (L : (ι → ℝ) → ℝ) = (fun z => ∑ i, a i * z i) := by
    ext z; exact strongDual_eq_sum L z
  have hLM : L ∘ (fun z => M.mulVec z) = (fun z => ∑ i, (a ᵥ* M) i * z i) := by
    ext z
    change L (M.mulVec z) = _
    rw [strongDual_eq_sum]
    exact Matrix.dotProduct_mulVec a M z
  rw [hLM, hL, gaussianProduct_map_sum, gaussianProduct_map_sum]
  have hMM : M * Mᵀ = 1 := by
    simpa [M, Matrix.star_eq_conjTranspose] using unitary.coe_mul_star_self U
  have hsq : (∑ i, (a ᵥ* M) i ^ 2) = ∑ i, a i ^ 2 := by
    simp only [pow_two]
    change (a ᵥ* M) ⬝ᵥ (a ᵥ* M) = a ⬝ᵥ a
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_vecMul, hMM, Matrix.one_mulVec]
  have hv : (∑ i, (⟨(a ᵥ* M) i ^ 2, sq_nonneg _⟩ : ℝ≥0)) =
      ∑ i, (⟨a i ^ 2, sq_nonneg _⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    exact (NNReal.coe_sum Finset.univ (fun i => (⟨(a ᵥ* M) i ^ 2, sq_nonneg _⟩ : ℝ≥0))).trans
      (hsq.trans (NNReal.coe_sum Finset.univ (fun i => (⟨a i ^ 2, sq_nonneg _⟩ : ℝ≥0))).symm)
  rw [hv]

def quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ :=
  z ⬝ᵥ A.mulVec z

lemma measurable_quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    Measurable (quadratic A) := by
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

lemma allLp_quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    AllLp (gaussianProduct ι) (quadratic A) := by
  unfold quadratic Matrix.mulVec dotProduct
  exact AllLp.sum Finset.univ (fun i _ => (allLp_standardGaussian_eval i).mul
    (AllLp.sum Finset.univ (fun j _ => (allLp_standardGaussian_eval j).const_mul (A i j))))

lemma quadratic_eigenvectorUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (z : ι → ℝ) :
    quadratic A ((hA.eigenvectorUnitary : Matrix ι ι ℝ).mulVec z) =
      ∑ i, hA.eigenvalues i * z i ^ 2 := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hd : Uᵀ * A * U = diagonal hA.eigenvalues := by
    simpa [U, Matrix.star_eq_conjTranspose] using hA.star_mul_self_mul_eq_diagonal
  change (U *ᵥ z) ⬝ᵥ A *ᵥ (U *ᵥ z) = _
  rw [dotProduct_mulVec, vecMul_mulVec,
    ← dotProduct_mulVec z (Uᵀ * A) (U *ᵥ z), mulVec_mulVec, hd]
  simp only [mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- Mean and kurtosis bound for an arbitrary real symmetric Gaussian quadratic form. -/
lemma gaussian_quadratic_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ z, quadratic A z ∂gaussianProduct ι) = A.trace ∧
    (∫ z, (quadratic A z - A.trace) ^ 4 ∂gaussianProduct ι) ≤
      15 * (∫ z, (quadratic A z - A.trace) ^ 2 ∂gaussianProduct ι) ^ 2 := by
  have he (p : ℕ) : (∫ z, (quadratic A z - A.trace) ^ p ∂gaussianProduct ι) =
      (∫ z, (∑ i, hA.eigenvalues i * (z i ^ 2 - 1)) ^ p ∂gaussianProduct ι) := by
    calc
      _ = ∫ z, (quadratic A z - A.trace) ^ p
          ∂(gaussianProduct ι).map (fun z => (hA.eigenvectorUnitary : Matrix ι ι ℝ).mulVec z) := by
        rw [gaussianProduct_map_unitary]
      _ = _ := by
        rw [integral_map (measurable_mulVec _).aemeasurable
          (((measurable_quadratic A).sub_const _).pow_const p).aestronglyMeasurable]
        apply integral_congr_ae
        filter_upwards [] with z
        rw [quadratic_eigenvectorUnitary hA, hA.trace_eq_sum_eigenvalues]
        congr 1
        simp [mul_sub, Finset.sum_sub_distrib]
  obtain ⟨h1, h2, h4⟩ := diagonal_gaussian_moments hA.eigenvalues
  have h1' := he 1
  simp only [pow_one] at h1'
  rw [h1, integral_sub (allLp_quadratic A).integrable (integrable_const _)] at h1'
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at h1'
  refine ⟨by linarith, ?_⟩
  rw [he 4, he 2, h2]
  nlinarith [h4]

end DPCut
