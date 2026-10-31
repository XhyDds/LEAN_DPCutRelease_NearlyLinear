import DPCut.HierarchyCosted
import DPCut.LSWApplicationGuarantees

/-! Polynomial real-model implementations of the actual Appendix C reductions.
Each certificate includes equality of the costed program's law to the statistical
kernel implemented using LSW. LSW and cited external application algorithm
contracts remain explicit; no exact SDP oracle is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

def costedPrivateHierarchy {n : ℕ} (hLSW : LSWStatement) (o : InducedARVContract)
    (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) : CostedLaw (Hierarchy n) :=
  LSWApplications.costedPostprocess (LSWApplications.family hLSW) hn p hp (fun h => costedHierarchy (costedHierarchySplit o n) o.balance n Finset.univ h) w

theorem hierarchy_reduction_runtime (hLSW : LSWStatement) (o : InducedARVContract)
    {η ε : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n), ∀ w : Weights n,
      (costedPrivateHierarchy hLSW o hn (applicationParameters n η ε) (applicationParameters_valid hn hη hη₁ hε) w).law =
        (LSWRelease.kernel (LSWApplications.family hLSW) hn (applicationParameters n η ε)
          (applicationParameters_valid hn hη hη₁ hε) w).bind (nonprivateHierarchyKernel o n) ∧
      (costedPrivateHierarchy hLSW o hn (applicationParameters n η ε) (applicationParameters_valid hn hη hη₁ hε) w).cost ≤
        ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) := by
  obtain ⟨C, hC, d, hcost⟩ := LSWApplications.postprocess_composed_cost_polynomial (LSWApplications.family hLSW) hη hη₁ hε (hierarchyCost_polynomial o)
  refine ⟨C, hC, d, fun n hn w => ⟨?_, ?_⟩⟩
  · apply LSWApplications.costedPostprocess_law
    intro h
    exact costedHierarchy_law (costedHierarchySplit o n) (hierarchySplitKernel o n) (costedHierarchySplit_law o n) _ _ _ _
  · apply (LSWApplications.costedPostprocess_cost (LSWApplications.family hLSW) hn _ (applicationParameters_valid hn hη hη₁ hε) _ (fun h => ?_) w).trans (hcost n hn)
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using costedHierarchy_cost (costedHierarchySplit o n)
      (costedHierarchySplit_cost o n) o.balance_pos o.balance_le n Finset.univ hne h

def costedCCSolver {n : ℕ} (run : Weights n → CostedLaw (Partition n)) (k t : ℕ) (seed : Partition n)
    (w : Weights n) : CostedLaw (Partition n) :=
  costedAmplifiedFinite (run w) (fun π => clusterCount π ≤ k) (fun π => -ccCost w π)
    (vectorBlockCost n) t seed

lemma costedCCSolver_law {n : ℕ} (run : Weights n → CostedLaw (Partition n))
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] (hK : ∀ w, (run w).law = K w)
    (k t : ℕ) (seed : Partition n) (w : Weights n) :
    (costedCCSolver run k t seed w).law = amplifiedCC K k t seed w := by
  rw [costedCCSolver, costedAmplifiedFinite, costedBestOf_law, CostedLaw.map_law, hK]
  have he : safeFinite (fun π : Partition n => clusterCount π ≤ k) seed = feasibleCC k seed := by
    funext π
    by_cases hp : clusterCount π ≤ k <;> simp [safeFinite, feasibleCC, hp]
  rw [he]
  rfl

theorem cc_reduction_runtime (hLSW : LSWStatement)
    (base alg : PolynomialGraphAlgorithm Partition) {γ ε s : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1 / 4) (hε : 0 < ε) (hs : 0 < s)
    (clusters : ℕ → ℕ) (seed : ∀ n, Partition n) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n), ∀ w : Weights n,
      let t := ⌈Real.log (1 / ((n : ℝ)⁻¹ ^ 10)) / s⌉₊
      let p := ccParameters n γ ε
      let run := LSWApplications.costedCC (LSWApplications.family hLSW) hn p (ccParameters_valid hn hγ hγ₁ hε) (base.run n) (costedCCSolver (alg.run n) (clusters n) t (seed n))
      letI := base.markov n
      letI := alg.markov n
      (run w).law = LSWApplications.ccPrivateKernel (LSWApplications.family hLSW) hn p (ccParameters_valid hn hγ hγ₁ hε)
        (base.kernel n) (amplifiedCC (alg.kernel n) (clusters n) t (seed n)) w ∧
      (run w).cost ≤ ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) := by
  obtain ⟨C, hC, d, hcost⟩ := LSWApplications.cc_composed_cost_polynomial (LSWApplications.family hLSW) hγ hγ₁ hε hs
    (graph_algorithm_cost_polynomial base) (graph_algorithm_cost_polynomial alg)
  refine ⟨C, hC, d, ?_⟩
  intro n hn w
  dsimp only
  letI := base.markov n
  letI := alg.markov n
  constructor
  · exact LSWApplications.costedCC_law (LSWApplications.family hLSW) hn _ (ccParameters_valid hn hγ hγ₁ hε) _ _ _ _
      (base.realizes n) (costedCCSolver_law (alg.run n) (alg.kernel n) (alg.realizes n) _ _ _) w
  · apply (LSWApplications.costedCC_cost (LSWApplications.family hLSW) hn _ (ccParameters_valid hn hγ hγ₁ hε) _ _ (base.cost_le n) (fun j => ?_) w).trans (hcost n hn)
    exact costedAmplifiedFinite_cost _ _ _ _ _ _ (alg.cost_le n j)

def costedMaxKSolver {n : ℕ} (run : Weights n → CostedLaw (Partition n)) (t : ℕ)
    (seed : Partition n) (w : Weights n) : CostedLaw (Partition n) :=
  costedBestOf (run w) (partitionCut w) (vectorBlockCost n) t seed

lemma costedMaxKSolver_law {n : ℕ} (run : Weights n → CostedLaw (Partition n))
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] (hK : ∀ w, (run w).law = K w)
    (t : ℕ) (seed : Partition n) (w : Weights n) :
    (costedMaxKSolver run t seed w).law = amplifiedMaxK K t seed w := by
  rw [costedMaxKSolver, costedBestOf_law, hK]
  rfl

theorem max_k_reduction_runtime (hLSW : LSWStatement) (alg : PolynomialGraphAlgorithm Partition)
    {η ε s : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1 / 4) (hε : 0 < ε) (hs : 0 < s)
    (seed : ∀ n, Partition n) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n), ∀ w : Weights n,
      let t := ⌈Real.log (1 / ((n : ℝ)⁻¹ ^ 10)) / s⌉₊
      let p := applicationParameters n η ε
      let run := LSWApplications.costedPostprocess (LSWApplications.family hLSW) hn p (applicationParameters_valid hn hη hη₁ hε) (costedMaxKSolver (alg.run n) t (seed n))
      letI := alg.markov n
      (run w).law = (LSWRelease.kernel (LSWApplications.family hLSW) hn p (applicationParameters_valid hn hη hη₁ hε) w).bind (amplifiedMaxK (alg.kernel n) t (seed n)) ∧
      (run w).cost ≤ ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) := by
  have hS := (amplification_repetitions_polynomial hs).mul
    ((graph_algorithm_cost_polynomial alg).add vector_block_polynomial)
  obtain ⟨C, hC, d, hcost⟩ := LSWApplications.postprocess_composed_cost_polynomial (LSWApplications.family hLSW) hη hη₁ hε hS
  refine ⟨C, hC, d, ?_⟩
  intro n hn w
  dsimp only
  letI := alg.markov n
  constructor
  · exact LSWApplications.costedPostprocess_law (LSWApplications.family hLSW) hn _ (applicationParameters_valid hn hη hη₁ hε) _ _ (costedMaxKSolver_law (alg.run n) (alg.kernel n) (alg.realizes n) _ _) w
  · exact (LSWApplications.costedPostprocess_cost (LSWApplications.family hLSW) hn _ (applicationParameters_valid hn hη hη₁ hε) _ (fun j => costedBestOf_cost _ _ _ _ _ (alg.cost_le n j)) w).trans (hcost n hn)

/-- Any polynomial external constrained-cut solver composes with the release;
this includes the bisection and balanced-cut instantiations of Theorem 34. -/
theorem constrained_reduction_runtime (hLSW : LSWStatement)
    (alg : PolynomialGraphAlgorithm (fun n => Finset (Fin n))) {η ε : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n), ∀ w : Weights n,
      (LSWApplications.costedPostprocess (LSWApplications.family hLSW) hn (applicationParameters n η ε) (applicationParameters_valid hn hη hη₁ hε) (alg.run n) w).law =
        (LSWRelease.kernel (LSWApplications.family hLSW) hn (applicationParameters n η ε)
          (applicationParameters_valid hn hη hη₁ hε) w).bind (alg.kernel n) ∧
      (LSWApplications.costedPostprocess (LSWApplications.family hLSW) hn (applicationParameters n η ε) (applicationParameters_valid hn hη hη₁ hε) (alg.run n) w).cost ≤
        ENNReal.ofReal (C * (1 + (n : ℝ)) ^ d) := by
  obtain ⟨C, hC, d, hcost⟩ := LSWApplications.postprocess_composed_cost_polynomial (LSWApplications.family hLSW) hη hη₁ hε (graph_algorithm_cost_polynomial alg)
  exact ⟨C, hC, d, fun n hn w => ⟨LSWApplications.costedPostprocess_law (LSWApplications.family hLSW) hn _ (applicationParameters_valid hn hη hη₁ hε) _ _ (alg.realizes n) w,
    (LSWApplications.costedPostprocess_cost (LSWApplications.family hLSW) hn _ (applicationParameters_valid hn hη hη₁ hε) _ (alg.cost_le n) w).trans (hcost n hn)⟩⟩

end DPCut
