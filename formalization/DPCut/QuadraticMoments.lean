import DPCut.GaussianMoments

/-! Second and fourth moments of centered diagonal Gaussian quadratic forms. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DPCut

variable {ι : Type*} [Fintype ι]

lemma allLp_standardGaussian_eval (i : ι) :
    AllLp (gaussianProduct ι) (fun z => z i) :=
  allLp_gaussian_id.comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

lemma centered_gaussian_square_eval_moments (i : ι) (a : ℝ) :
    (∫ z, a * (z i ^ 2 - 1) ∂gaussianProduct ι) = 0 ∧
    (∫ z, (a * (z i ^ 2 - 1)) ^ 2 ∂gaussianProduct ι) = 2 * a ^ 2 ∧
    (∫ z, (a * (z i ^ 2 - 1)) ^ 4 ∂gaussianProduct ι) = 60 * a ^ 4 := by
  have he (p : ℕ) : (∫ z, (z i ^ 2 - 1) ^ p ∂gaussianProduct ι) =
      (∫ x : ℝ, (x ^ 2 - 1) ^ p ∂gaussianReal 0 1) := by
    have hm := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by fun_prop)]
  obtain ⟨h1, h2, h4⟩ := centered_gaussian_square_moments
  have h1' := he 1
  simp only [pow_one] at h1'
  simp only [mul_pow, integral_const_mul, h1', he 2, he 4, h1, h2, h4, mul_zero]
  constructor
  · trivial
  constructor <;> ring

/-- A centered diagonal quadratic Gaussian has fourth moment at most 15 times variance squared. -/
lemma diagonal_gaussian_moments (a : ι → ℝ) :
    let W := fun z : ι → ℝ => ∑ i, a i * (z i ^ 2 - 1)
    (∫ z, W z ∂gaussianProduct ι) = 0 ∧
    (∫ z, W z ^ 2 ∂gaussianProduct ι) = 2 * ∑ i, a i ^ 2 ∧
    (∫ z, W z ^ 4 ∂gaussianProduct ι) ≤ 60 * (∑ i, a i ^ 2) ^ 2 := by
  classical
  let f : ι → (ι → ℝ) → ℝ := fun i z => a i * (z i ^ 2 - 1)
  have hf (i : ι) : AllLp (gaussianProduct ι) (f i) :=
    (((allLp_standardGaussian_eval i).pow 2).sub (AllLp.const 1)).const_mul (a i)
  have hm (i : ι) : Measurable (f i) := by dsimp [f]; fun_prop
  have hi : iIndepFun f (gaussianProduct ι) :=
    iIndepFun_pi (fun i => (by fun_prop : Measurable (fun x : ℝ => a i * (x ^ 2 - 1))).aemeasurable)
  have hs (s : Finset (ι)) : AllLp (gaussianProduct ι) (fun z => ∑ i ∈ s, f i z) :=
    AllLp.sum s (fun i _ => hf i)
  have hm1 (s : Finset (ι)) :
      (∫ z, (∑ i ∈ s, f i z) ∂gaussianProduct ι) = 0 := by
    rw [integral_finset_sum _ (fun i _ => (hf i).integrable)]
    apply Finset.sum_eq_zero
    intro i _
    exact (centered_gaussian_square_eval_moments i (a i)).1
  have h24 (s : Finset (ι)) :
      (∫ z, (∑ i ∈ s, f i z) ^ 2 ∂gaussianProduct ι) = 2 * ∑ i ∈ s, a i ^ 2 ∧
      (∫ z, (∑ i ∈ s, f i z) ^ 4 ∂gaussianProduct ι) ≤ 60 * (∑ i ∈ s, a i ^ 2) ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      have hind : IndepFun (f i) (fun z => ∑ j ∈ s, f j z) (gaussianProduct ι) := by
        convert (hi.indepFun_finset_sum_of_notMem hm his).symm using 1
        ext z; simp
      obtain ⟨h1i, h2i, h4i⟩ := centered_gaussian_square_eval_moments i (a i)
      change (∫ z, f i z ∂gaussianProduct ι) = 0 at h1i
      change (∫ z, f i z ^ 2 ∂gaussianProduct ι) = 2 * a i ^ 2 at h2i
      change (∫ z, f i z ^ 4 ∂gaussianProduct ι) = 60 * a i ^ 4 at h4i
      have hp2 := integral_add_pow_of_indep (hf i) (hs s) hind 2
      have hp4 := integral_add_pow_of_indep (hf i) (hs s) hind 4
      norm_num [Finset.sum_range_succ, Nat.choose, h1i, h2i, h4i, hm1 s, ih.1] at hp2 hp4
      simp only [Finset.sum_insert his]
      constructor
      · rw [hp2]; ring
      · rw [hp4]
        have hsum : 0 ≤ ∑ j ∈ s, a j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (a j))
        nlinarith [ih.2, mul_nonneg (sq_nonneg (a i)) hsum]
  exact ⟨hm1 Finset.univ, h24 Finset.univ⟩

end DPCut
