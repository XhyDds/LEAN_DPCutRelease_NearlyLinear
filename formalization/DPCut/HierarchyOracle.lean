import DPCut.ExternalApplicationContracts
import DPCut.FiniteAmplification
import DPCut.HierarchyComparator

/-! The external ARV dependency concerns only one induced-graph balanced cut.
Amplification, small-cluster fallback, recursion, and HC analysis are internal. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

/-- Weighted ARV with comparison balance 1/4 and constant success probability.
The ambient-vertex interface avoids exposing relabeling choices to the recursion.
The returned balance is normalized downward to at most 1/3. -/
structure InducedARVContract where
  balance : ℝ
  balance_pos : 0 < balance
  balance_le : balance ≤ 1 / 3
  factor : ℝ
  factor_pos : 0 < factor
  kernel : (n : ℕ) → Finset (Fin n) → Kernel (Weights n) (Finset (Fin n))
  markov : ∀ n A, IsMarkovKernel (kernel n A)
  approximation : ∀ n, 2 ≤ n → ∀ A : Finset (Fin n), 4 ≤ A.card → ∀ w, Nonnegative w →
    HighProbability (kernel n A w) (1 / 2) (fun S => BalancedWithin balance A S ∧
      inducedExpansion w A S ≤ (1 + factor * Real.sqrt (Real.log n)) *
        sInf (inducedExpansion w A '' {R | BalancedWithin (1 / 4) A R}))
  run : (n : ℕ) → Finset (Fin n) → Weights n → CostedLaw (Finset (Fin n))
  realizes : ∀ n A w, (run n A w).law = kernel n A w
  coefficient : ℝ
  degree : ℕ
  coefficient_pos : 0 < coefficient
  cost_le : ∀ n A w, (run n A w).cost ≤ ENNReal.ofReal (coefficient * (1 + (n : ℝ)) ^ degree)

instance (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) : IsMarkovKernel (o.kernel n A) := o.markov n A

@[fun_prop] lemma measurable_inducedExpansion {n : ℕ} (A S : Finset (Fin n)) :
    Measurable (fun w : Weights n => inducedExpansion w A S) := by
  unfold inducedExpansion
  apply Measurable.div_const
  unfold between
  apply Finset.measurable_sum
  intro e he
  split_ifs <;> fun_prop

def hierarchyFactor (o : InducedARVContract) (n : ℕ) : ℝ := 1 + o.factor * Real.sqrt (Real.log n)

def hierarchySplitKernel (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) :
    Kernel (Weights n) (Finset (Fin n)) :=
  if 4 ≤ A.card then amplifiedFinite (o.kernel n A) (BalancedWithin o.balance A)
    (fun w S => -inducedExpansion w A S) (fun S => (measurable_inducedExpansion A S).neg)
    (24 * n) (halfSubset A)
  else ⟨fun _ => Measure.dirac (halfSubset A), measurable_const⟩

instance hierarchySplitKernel_markov (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) :
    IsMarkovKernel (hierarchySplitKernel o n A) := by
  unfold hierarchySplitKernel
  split_ifs
  · infer_instance
  · exact ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.dirac (halfSubset A)))⟩

lemma hierarchy_repetitions {n : ℕ} (hn : 2 ≤ n) :
    Real.log (1 / ((n : ℝ)⁻¹ ^ 12)) / (1 / 2) ≤ (24 * n : ℕ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [one_div, Real.log_inv, Real.log_pow, Real.log_inv]
  push_cast
  have hh := Real.log_le_sub_one_of_pos hp
  nlinarith

lemma hierarchySplitKernel_quality (o : InducedARVContract) {n : ℕ} (hn : 2 ≤ n)
    {w : Weights n} (hw : Nonnegative w) (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
    HighProbability (hierarchySplitKernel o n A w) ((n : ℝ)⁻¹ ^ 12)
      (fun S => S ⊆ A ∧ SplitQuality w (1 / 4) o.balance (hierarchyFactor o n) A S (A \ S)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ : 0 < (n : ℝ)⁻¹ ^ 12 := by positivity
  by_cases hlarge : 4 ≤ A.card
  · have hgood := o.approximation n hn A hlarge w hw
    have hscore : HighProbability (o.kernel n A w) (1 - (1 / 2)) (fun S =>
        BalancedWithin o.balance A S ∧
        -(hierarchyFactor o n * sInf (inducedExpansion w A '' {R | BalancedWithin (1 / 4) A R})) ≤
          -inducedExpansion w A S) := by
      rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      apply hgood.mono _ (Set.toFinite _ |>.measurableSet)
      intro S hs
      exact ⟨hs.1, neg_le_neg hs.2⟩
    have hh := amplifiedFinite_success (o.kernel n A) (BalancedWithin o.balance A)
      (fun w S => -inducedExpansion w A S) (fun S => (measurable_inducedExpansion A S).neg)
      (halfSubset A) (halfSubset_balanced hA o.balance_le) w (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hτ hscore (24 * n) (hierarchy_repetitions hn)
    rw [hierarchySplitKernel, if_pos hlarge]
    apply hh.mono _ (Set.toFinite _ |>.measurableSet)
    intro S hs
    refine ⟨hs.1.1, hs.1.2.1, hs.1.2.2, ?_⟩
    have hlarge' : 1 / (1 / 4 : ℝ) ≤ (A.card : ℝ) := by norm_num; exact_mod_cast hlarge
    rw [if_pos hlarge']
    exact neg_le_neg_iff.mp hs.2
  · have hsmall : ¬ 1 / (1 / 4 : ℝ) ≤ (A.card : ℝ) := by norm_num; exact_mod_cast (lt_of_not_ge hlarge)
    have hbal := halfSubset_balanced hA o.balance_le
    have hq : (halfSubset A) ⊆ A ∧
        SplitQuality w (1 / 4) o.balance (hierarchyFactor o n) A (halfSubset A) (A \ halfSubset A) := by
      refine ⟨hbal.1, hbal.2.1, hbal.2.2, ?_⟩
      simpa only [if_neg hsmall] using halfSubset_even A
    rw [hierarchySplitKernel, if_neg hlarge]
    exact (highProbability_dirac_finite (halfSubset A) hq).weaken hτ.le

end DPCut
