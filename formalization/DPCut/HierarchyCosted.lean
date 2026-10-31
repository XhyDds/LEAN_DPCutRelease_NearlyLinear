import DPCut.ApplicationCosted
import DPCut.Theorem36

/-! Real-model runtime of the guarded binary recursion, including failed calls. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def costedHierarchySplit (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) (w : Weights n) :
    CostedLaw (Finset (Fin n)) :=
  if 4 ≤ A.card then costedAmplifiedFinite (o.run n A w) (BalancedWithin o.balance A)
    (fun S => -inducedExpansion w A S) (vectorBlockCost n) (24 * n) (halfSubset A)
  else .charge (vectorBlockCost n) (.pure (halfSubset A))

lemma costedHierarchySplit_law (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) (w : Weights n) :
    (costedHierarchySplit o n A w).law = hierarchySplitKernel o n A w := by
  unfold costedHierarchySplit hierarchySplitKernel
  split_ifs
  · exact costedAmplifiedFinite_law (o.kernel n A) (BalancedWithin o.balance A)
      (fun w S => -inducedExpansion w A S) (fun S => (measurable_inducedExpansion A S).neg)
      w _ (o.realizes n A w) _ _ _
  · rfl

def hierarchySplitCostBound (o : InducedARVContract) (n : ℕ) : ℝ≥0∞ :=
  vectorBlockCost n + (24 * n : ℕ) *
    (ENNReal.ofReal (o.coefficient * (1 + (n : ℝ)) ^ o.degree) + 2 * vectorBlockCost n)

lemma costedHierarchySplit_cost (o : InducedARVContract) (n : ℕ) (A : Finset (Fin n)) (w : Weights n) :
    (costedHierarchySplit o n A w).cost ≤ hierarchySplitCostBound o n := by
  unfold costedHierarchySplit hierarchySplitCostBound
  split_ifs
  · exact (costedAmplifiedFinite_cost _ _ _ _ _ _ (o.cost_le n A w)).trans (le_add_left le_rfl)
  · simp only [CostedLaw.charge, CostedLaw.pure, add_zero]
    exact le_add_right le_rfl

def costedHierarchy {n : ℕ} (run : Finset (Fin n) → Weights n → CostedLaw (Finset (Fin n)))
    (c : ℝ) : ℕ → Finset (Fin n) → Weights n → CostedLaw (Hierarchy n)
  | 0, A, _ => .charge (vectorBlockCost n) (.pure {A})
  | t + 1, A, w => .charge (vectorBlockCost n) (if 2 ≤ A.card then
      (run A w).bind fun raw =>
        let S := safeHierarchySplit c A raw
        (costedHierarchy run c t S w).bind fun L =>
          (costedHierarchy run c t (A \ S) w).map (joinHierarchy A L) (vectorBlockCost n)
    else .pure {A})

lemma costedHierarchy_law {n : ℕ}
    (run : Finset (Fin n) → Weights n → CostedLaw (Finset (Fin n)))
    (K : Finset (Fin n) → Kernel (Weights n) (Finset (Fin n)))
    (hK : ∀ A w, (run A w).law = K A w) (c : ℝ) (t : ℕ) (A : Finset (Fin n)) (w : Weights n) :
    (costedHierarchy run c t A w).law = hierarchyLaw K c t A w := by
  induction t generalizing A with
  | zero => rfl
  | succ t ih =>
    simp only [costedHierarchy, hierarchyLaw, CostedLaw.charge_law]
    split_ifs
    · simp only [CostedLaw.bind_law, CostedLaw.map_law, hK, ih]
    · rfl

lemma costedHierarchy_cost {n : ℕ}
    (run : Finset (Fin n) → Weights n → CostedLaw (Finset (Fin n)))
    {B : ℝ≥0∞} (hB : ∀ A w, (run A w).cost ≤ B)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1 / 3) (t : ℕ) (A : Finset (Fin n))
    (hA : A.Nonempty) (w : Weights n) :
    (costedHierarchy run c t A w).cost ≤ (2 * A.card - 1 : ℕ) * (B + 2 * vectorBlockCost n) := by
  let U := B + 2 * vectorBlockCost n
  have leaf (A : Finset (Fin n)) (hA : A.Nonempty) : vectorBlockCost n ≤ (2 * A.card - 1 : ℕ) * U := by
    have hcount : (1 : ℝ≥0∞) ≤ (2 * A.card - 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ 2 * A.card - 1 by have := hA.card_pos; omega)
    have hv : vectorBlockCost n ≤ U := by
      dsimp [U]
      calc
        _ ≤ 2 * vectorBlockCost n := by
          have hh : (1 : ℝ≥0∞) ≤ 2 := by norm_num
          simpa using mul_le_mul_right' hh (vectorBlockCost n)
        _ ≤ _ := le_add_left le_rfl
    exact hv.trans (by simpa using mul_le_mul_right' hcount U)
  induction t generalizing A with
  | zero =>
    simpa only [costedHierarchy, CostedLaw.charge, CostedLaw.pure, add_zero] using leaf A hA
  | succ t ih =>
    by_cases hlarge : 2 ≤ A.card
    · have cont (raw : Finset (Fin n)) :
          ((costedHierarchy run c t (safeHierarchySplit c A raw) w).bind fun L =>
            (costedHierarchy run c t (A \ safeHierarchySplit c A raw) w).map (joinHierarchy A L) (vectorBlockCost n)).cost ≤
          (2 * A.card - 2 : ℕ) * U + vectorBlockCost n := by
        let S := safeHierarchySplit c A raw
        have hbal := safeHierarchySplit_balanced hc₁ hlarge raw
        obtain ⟨hneS, hneC, hltS, hltC⟩ := hbal.split_data hc hlarge
        have hsum : S.card + (A \ S).card = A.card := by
          simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hbal.1
        have hcount : (2 * S.card - 1) + (2 * (A \ S).card - 1) = 2 * A.card - 2 := by
          have hspos : 0 < S.card := hneS.card_pos
          have hcpos : 0 < (A \ S).card := hneC.card_pos
          omega
        calc
          _ ≤ (2 * S.card - 1 : ℕ) * U + ((2 * (A \ S).card - 1 : ℕ) * U + vectorBlockCost n) := by
            apply CostedLaw.bind_cost_le _ _ (ih S hneS)
            intro L
            exact add_le_add_right (ih (A \ S) hneC) _
          _ = _ := by rw [← add_assoc, ← add_mul, ← Nat.cast_add, hcount]
      have hcount : (2 * A.card - 2) + 1 = 2 * A.card - 1 := by omega
      calc
        _ ≤ vectorBlockCost n + (B + ((2 * A.card - 2 : ℕ) * U + vectorBlockCost n)) := by
          apply CostedLaw.charge_cost_le
          rw [if_pos hlarge]
          exact CostedLaw.bind_cost_le _ _ (hB A w) cont
        _ = (2 * A.card - 1 : ℕ) * U := by
          rw [← hcount, Nat.cast_add, Nat.cast_one]
          dsimp [U]
          ring
    · simpa only [costedHierarchy, if_neg hlarge, CostedLaw.charge, CostedLaw.pure, add_zero] using leaf A hA

lemma hierarchySplitCost_polynomial (o : InducedARVContract) : PolynomialVertexBound (hierarchySplitCostBound o) := by
  have h24 : PolynomialVertexBound (fun _ => (24 : ℝ≥0∞)) := by simpa using PolynomialVertexBound.constant 24 (by norm_num)
  have h2 : PolynomialVertexBound (fun _ => (2 : ℝ≥0∞)) := by simpa using PolynomialVertexBound.constant 2 (by norm_num)
  have hn : PolynomialVertexBound (fun n => (n : ℝ≥0∞)) := vertex_count_polynomial.mono (fun _ _ => le_add_right le_rfl)
  have hAlg : PolynomialVertexBound (fun n => ENNReal.ofReal (o.coefficient * (1 + (n : ℝ)) ^ o.degree)) :=
    ⟨o.coefficient, o.coefficient_pos, o.degree, fun _ _ => le_refl _⟩
  change PolynomialVertexBound (fun n => vectorBlockCost n + (24 * n : ℕ) * _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using vector_block_polynomial.add ((h24.mul hn).mul (hAlg.add (h2.mul vector_block_polynomial)))

lemma hierarchyCost_polynomial (o : InducedARVContract) :
    PolynomialVertexBound (fun n => (2 * n - 1 : ℕ) * (hierarchySplitCostBound o n + 2 * vectorBlockCost n)) := by
  have h2 : PolynomialVertexBound (fun _ => (2 : ℝ≥0∞)) := by simpa using PolynomialVertexBound.constant 2 (by norm_num)
  have hcount : PolynomialVertexBound (fun n => (2 * n - 1 : ℕ)) :=
    (h2.mul vertex_count_polynomial).mono (fun n hn => by
      have hh : (2 * n - 1 : ℕ) ≤ 2 * (n + 1) := by omega
      exact_mod_cast hh)
  exact hcount.mul ((hierarchySplitCost_polynomial o).add (h2.mul vector_block_polynomial))

end DPCut
