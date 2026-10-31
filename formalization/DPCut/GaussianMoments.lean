import DPCut.GaussianWitness
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Finite Gaussian moments used in the proof of Lemma 11. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace DPCut

/-- A finite product of standard normals, with an arbitrary finite index type. -/
abbrev gaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

/-- Membership in every finite Lp space, convenient for polynomial expressions. -/
def AllLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ

namespace AllLp
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {f g : Ω → ℝ}

lemma const [IsProbabilityMeasure μ] (c : ℝ) : AllLp μ (fun _ => c) := fun _ _ => memLp_const c
lemma add (hf : AllLp μ f) (hg : AllLp μ g) : AllLp μ (fun x => f x + g x) :=
  fun p hp => (hf p hp).add (hg p hp)
lemma sub (hf : AllLp μ f) (hg : AllLp μ g) : AllLp μ (fun x => f x - g x) :=
  fun p hp => (hf p hp).sub (hg p hp)
lemma const_mul (hf : AllLp μ f) (c : ℝ) : AllLp μ (fun x => c * f x) :=
  fun p hp => (hf p hp).const_mul c
lemma div_const (hf : AllLp μ f) (c : ℝ) : AllLp μ (fun x => f x / c) := by
  simpa only [div_eq_mul_inv, mul_comm] using hf.const_mul c⁻¹
lemma mul (hf : AllLp μ f) (hg : AllLp μ g) : AllLp μ (fun x => f x * g x) := by
  intro p hp
  haveI : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
    rw [ENNReal.mul_inv (by simp) (by simp), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]⟩
  exact (hg (2 * p) (by finiteness)).mul' (hf (2 * p) (by finiteness))
lemma pow [IsProbabilityMeasure μ] (hf : AllLp μ f) (j : ℕ) : AllLp μ (fun x => f x ^ j) := by
  induction j with
  | zero => simpa using (const (μ := μ) 1)
  | succ j ih => simpa only [pow_succ] using ih.mul hf
lemma sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, AllLp μ (f i)) : AllLp μ (fun x => ∑ i ∈ s, f i x) :=
  fun p hp => memLp_finset_sum s (fun i hi => hf i hi p hp)
lemma integrable (hf : AllLp μ f) : Integrable f μ :=
  memLp_one_iff_integrable.1 (hf 1 (by simp))
lemma abs (hf : AllLp μ f) : AllLp μ (fun x => |f x|) :=
  fun p hp => (hf p hp).norm
lemma comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {g : Ω' → Ω} (hf : AllLp μ f) (hg : MeasurePreserving g ν μ) :
    AllLp ν (f ∘ g) := fun p hp => (hf p hp).comp_measurePreserving hg
end AllLp

lemma allLp_gaussian_id : AllLp (gaussianReal 0 1) (fun x : ℝ => x) :=
  fun p hp => memLp_id_gaussianReal' p hp

private def gaussianDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (gaussianDerivativePolynomial n).derivative +
      Polynomial.X * gaussianDerivativePolynomial n

private lemma iteratedDeriv_gaussian_mgf (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => (gaussianDerivativePolynomial n).eval t * Real.exp (t ^ 2 / 2) := by
  induction n with
  | zero => simp [gaussianDerivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have he : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2))
        (t * Real.exp (t ^ 2 / 2)) t := by
      convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1
      simp only [Pi.pow_apply, id_eq]
      ring
    have hh := ((gaussianDerivativePolynomial n).hasDerivAt t |>.mul he).deriv
    change deriv (fun t => (gaussianDerivativePolynomial n).eval t * Real.exp (t ^ 2 / 2)) t = _ at hh
    rw [hh]
    simp only [gaussianDerivativePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]
    ring

private lemma gaussian_moment (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal 0 1) = (gaussianDerivativePolynomial n).eval 0 := by
  have h := iteratedDeriv_mgf_zero (μ := gaussianReal 0 1) (X := id)
    (by simp [integrableExpSet_id_gaussianReal]) n
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  rw [iteratedDeriv_gaussian_mgf] at h
  simpa using h.symm

lemma gaussian_moment_two : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  rw [gaussian_moment]
  norm_num [gaussianDerivativePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]

lemma gaussian_moment_four : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  rw [gaussian_moment]
  norm_num [gaussianDerivativePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]

lemma gaussian_moment_six : (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 1) = 15 := by
  rw [gaussian_moment]
  norm_num [gaussianDerivativePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]

lemma gaussian_moment_eight : (∫ x : ℝ, x ^ 8 ∂gaussianReal 0 1) = 105 := by
  rw [gaussian_moment]
  norm_num [gaussianDerivativePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]

lemma centered_gaussian_square_moments :
    (∫ x : ℝ, (x ^ 2 - 1) ∂gaussianReal 0 1) = 0 ∧
    (∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂gaussianReal 0 1) = 2 ∧
    (∫ x : ℝ, (x ^ 2 - 1) ^ 4 ∂gaussianReal 0 1) = 60 := by
  have hi (p : ℕ) := (allLp_gaussian_id.pow p).integrable
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_sub (hi 2) (integrable_const 1), gaussian_moment_two]
    simp
  · have he : (fun x : ℝ => (x ^ 2 - 1) ^ 2) = (fun x => x ^ 4 - 2 * x ^ 2 + 1) := by
      ext x; ring
    have h42 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) :=
      (hi 4).sub ((hi 2).const_mul 2)
    rw [he, integral_add h42 (integrable_const 1),
      integral_sub (hi 4) ((hi 2).const_mul 2), integral_const_mul,
      gaussian_moment_four, gaussian_moment_two]
    norm_num
  · have he : (fun x : ℝ => (x ^ 2 - 1) ^ 4) =
        (fun x => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2 + 1) := by
      ext x; ring
    have h86 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6) (gaussianReal 0 1) :=
      (hi 8).sub ((hi 6).const_mul 4)
    have h864 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4) (gaussianReal 0 1) :=
      h86.add ((hi 4).const_mul 6)
    have h8642 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2)
        (gaussianReal 0 1) := h864.sub ((hi 2).const_mul 4)
    rw [he, integral_add h8642 (integrable_const 1),
      integral_sub h864 ((hi 2).const_mul 4),
      integral_add h86 ((hi 4).const_mul 6),
      integral_sub (hi 8) ((hi 6).const_mul 4)]
    simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul,
      one_mul, gaussian_moment_eight, gaussian_moment_six, gaussian_moment_four, gaussian_moment_two]
    norm_num

lemma integral_add_pow_of_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : AllLp μ f) (hg : AllLp μ g)
    (hfg : IndepFun f g μ) (p : ℕ) :
    (∫ x, (f x + g x) ^ p ∂μ) =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) *
        (∫ x, f x ^ j ∂μ) * (∫ x, g x ^ (p - j) ∂μ) := by
  have he : (fun x => (f x + g x) ^ p) =
      (fun x => ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * f x ^ j * g x ^ (p - j)) := by
    ext x
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [he, integral_finset_sum _ (fun j _ =>
    (((hf.pow j).const_mul _).mul (hg.pow (p - j))).integrable)]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have h := hfg.comp (measurable_id.pow_const j) (measurable_id.pow_const (p - j))
  congr 1
  exact h.integral_fun_mul_eq_mul_integral ((hf.pow j) 1 (by simp)).1
    ((hg.pow (p - j)) 1 (by simp)).1

end DPCut
