import DPCut.BernoulliConcentration
import DPCut.CCResidual
import DPCut.ApplicationPostprocessing

/-! Measurable independent Bernoulli rounding and the uniform comparison of
all correlation-clustering objectives. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def clipUnit (r : ℝ) : ℝ := min 1 (max 0 r)

lemma clipUnit_bounds (r : ℝ) : 0 ≤ clipUnit r ∧ clipUnit r ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma clipUnit_eq {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) : clipUnit r = r := by
  simp [clipUnit, max_eq_right hr.1, min_eq_right hr.2]

def bernoulliBits {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) : Measure (ι → Bool) :=
  discreteMeasure (bernoulliWeight (fun i => clipUnit (p i)))

instance bernoulliBits_probability {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    IsProbabilityMeasure (bernoulliBits p) := by
  classical
  exact discreteMeasure_probability (bernoulliWeight_nonneg (fun i => clipUnit_bounds (p i)))
    (bernoulliWeight_sum _)

lemma measurable_bernoulliBits {ι : Type*} [Fintype ι] [DecidableEq ι] : Measurable (@bernoulliBits ι _ _) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [bernoulliBits, discreteMeasure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro x _
  apply Measurable.mul _ measurable_const
  apply Measurable.ennreal_ofReal
  unfold bernoulliWeight clipUnit
  apply Finset.measurable_prod
  intro i _
  cases hx : x i <;> simp only [Bool.false_eq_true, reduceIte] <;> fun_prop

def bitsWeights {n : ℕ} (x : Edge n → Bool) : Weights n := fun e => if x e then 1 else 0

lemma bitsWeights_unweighted {n : ℕ} (x : Edge n → Bool) : IsUnweighted (bitsWeights x) := by
  intro e
  dsimp [bitsWeights]
  split <;> simp

def bernoulliRounding {n : ℕ} : Kernel (Weights n) (Weights n) :=
  ⟨fun p => (bernoulliBits p).map bitsWeights,
    (Measure.measurable_map bitsWeights (measurable_of_finite bitsWeights)).comp measurable_bernoulliBits⟩

instance bernoulliRounding_markov {n : ℕ} : IsMarkovKernel (bernoulliRounding (n := n)) := by
  constructor
  intro p
  exact Measure.isProbabilityMeasure_map (measurable_of_finite bitsWeights).aemeasurable

lemma bernoulliRounding_unweighted {n : ℕ} (p : Weights n) :
    ∀ᵐ j ∂bernoulliRounding p, IsUnweighted j := by
  apply (ae_map_iff (measurable_of_finite bitsWeights).aemeasurable (by
    unfold IsUnweighted
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun e =>
      (measurableSet_eq_fun (measurable_pi_apply e) measurable_const).union
        (measurableSet_eq_fun (measurable_pi_apply e) measurable_const))).mpr
  exact Filter.Eventually.of_forall bitsWeights_unweighted

def ccDesiredBits {n : ℕ} (π : Partition n) : Edge n → Bool :=
  fun e => decide (π e.val.1 ≠ π e.val.2)

lemma ccCost_bits {n : ℕ} (π : Partition n) (x : Edge n → Bool) :
    ccCost (bitsWeights x) π = bernoulliCount (ccDesiredBits π) x := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : π e.val.1 = π e.val.2 <;> cases h : x e <;>
    simp [bitsWeights, ccDesiredBits, he, h]

lemma ccCost_bernoulliMean {n : ℕ} (p : Weights n) (π : Partition n) :
    ccCost p π = bernoulliMean p (ccDesiredBits π) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : π e.val.1 = π e.val.2 <;> simp [ccDesiredBits, he]

lemma discreteMeasure_event {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Set ι) :
    discreteMeasure p s = ENNReal.ofReal (∑ i, if i ∈ s then p i else 0) := by
  classical
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  simp only [discreteMeasure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split; exact hp i; exact le_refl 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [hi]

lemma bernoulliBits_cc_tail {n : ℕ} {p : Weights n} (hp : Bounded 1 p)
    (π : Partition n) {η t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ht : 0 ≤ t) :
    bernoulliBits p {x | η * ccCost p π + 3 / η * t < |ccCost (bitsWeights x) π - ccCost p π|} ≤
      ENNReal.ofReal (2 * Real.exp (-t)) := by
  have hclip : (fun e => clipUnit (p e)) = p := funext fun e => clipUnit_eq (hp e)
  rw [bernoulliBits, hclip]
  have hdm := discreteMeasure_event (bernoulliWeight p) (bernoulliWeight_nonneg hp)
    {x | η * ccCost p π + 3 / η * t < |ccCost (bitsWeights x) π - ccCost p π|}
  rw [hdm]
  apply ENNReal.ofReal_le_ofReal
  simp only [Set.mem_setOf_eq]
  simp_rw [ccCost_bits]
  rw [ccCost_bernoulliMean]
  exact bernoulli_relative_tail hp (ccDesiredBits π) hη hη1 ht

lemma measurableSet_cc_rounding {n : ℕ} (p : Weights n) (η R : ℝ) :
    MeasurableSet {j | ∀ π : Partition n, |ccCost j π - ccCost p π| ≤ η * ccCost p π + R} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro π
  have hcost : Measurable (fun j : Weights n => ccCost j π) := by
    unfold ccCost
    apply Finset.measurable_sum
    intro e _
    by_cases he : π e.val.1 = π e.val.2 <;> simp only [he, if_true, if_false] <;> fun_prop
  exact measurableSet_le ((hcost.sub measurable_const).abs) measurable_const

theorem cc_bernoulli_rounding {n : ℕ} (hn : 2 ≤ n) {p : Weights n} (hp : Bounded 1 p)
    {η β : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hβ : 0 < β) (hβ1 : β < 1) :
    HighProbability (bernoulliRounding p) β (fun j => ∀ π : Partition n,
      |ccCost j π - ccCost p π| ≤ η * ccCost p π + 3 / η * (n * Real.log n + Real.log (2 / β))) := by
  let t := (n : ℝ) * Real.log n + Real.log (2 / β)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : 0 ≤ t := add_nonneg (mul_nonneg hn0.le (Real.log_natCast_nonneg _))
    (Real.log_nonneg ((one_le_div hβ).mpr (by linarith)))
  apply highProbability_of_failure (measurableSet_cc_rounding p η _) hβ.le
  change (bernoulliBits p).map bitsWeights {j | ¬∀ π : Partition n,
    |ccCost j π - ccCost p π| ≤ η * ccCost p π + 3 / η * t} ≤ _
  change (bernoulliBits p).map (bitsWeights (n := n))
    {j | ∀ π : Partition n, |ccCost j π - ccCost p π| ≤ η * ccCost p π + 3 / η * t}ᶜ ≤ _
  rw [Measure.map_apply (measurable_of_finite (bitsWeights (n := n)))
    (measurableSet_cc_rounding p η (3 / η * t)).compl]
  have hbad : (bitsWeights (n := n)) ⁻¹' {j | ∀ π : Partition n,
      |ccCost j π - ccCost p π| ≤ η * ccCost p π + 3 / η * t}ᶜ =
      ⋃ π : Partition n, {x | η * ccCost p π + 3 / η * t < |ccCost (bitsWeights x) π - ccCost p π|} := by
    ext x
    simp
  rw [hbad]
  apply (measure_iUnion_fintype_le _ _).trans
  apply (Finset.sum_le_sum fun π _ => bernoulliBits_cc_tail hp π hη hη1 ht).trans
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have heq : (Fintype.card (Partition n) : ℝ) * (2 * Real.exp (-t)) = β := by
    have hexp : Real.exp ((n : ℝ) * Real.log n) = (n : ℝ) ^ n := by
      rw [Real.exp_nat_mul, Real.exp_log hn0]
    have hc : (Fintype.card (Partition n) : ℝ) = (n : ℝ) ^ n := by
      simp [Partition]
    rw [hc, ← hexp]
    dsimp [t]
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / β)]
    have hz := (Real.exp_pos ((n : ℝ) * Real.log n)).ne'
    field_simp
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), heq]

end DPCut
