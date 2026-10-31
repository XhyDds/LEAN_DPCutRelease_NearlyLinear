import DPCut.PolynomialRuntime
import DPCut.Lemma29

/-! Cost interpretation of the actual capped release in the selected real model.
The finite projection examines m+1 candidates with O(m) work each; its vector
block charge is deliberately enlarged to 10000 (n+1)^4. Exact scalar arithmetic,
exponentials, and random primitives retain the real-model interpretation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def cappedBlockCost (n : ℕ) : ℝ≥0∞ := vectorBlockCost n * vectorBlockCost n

def costedCappedInner {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) : ℕ → Weights n → CostedLaw (Option (Weights n × Weights n))
  | 0, _ => .pure none
  | t + 1, h => (costedAggregate sdp c.oracle p.gamma w h).bind fun b =>
      .charge (cappedBlockCost n) (if b.Accepts h then .pure (some (h, b.residual))
        else costedCappedInner sdp p c w a H t (cappedNext c a H h b))

def costedCappedOuter {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) : ℕ → Weights n → Weights n → CostedLaw (Weights n)
  | 0, _, out => .pure out
  | t + 1, a, out => (CostedLaw.sample (laplace (1 / c.eps2)) 1).bind fun noise =>
      .charge (cappedBlockCost n)
        (let wi := hadamard a w
         let M := lowerBiasedMass (mass a) (mass wi) noise c.tau2
         if a = 0 ∨ M ≤ c.stop then .pure out else
         (costedCappedInner sdp p c wi a M c.T2 (initialEstimate M a)).bind fun result =>
         match result with
         | none => costedCappedOuter sdp p c w t a out
         | some (h, r) => costedCappedOuter sdp p c w t (residualUpdate a r) (out + hadamard h r))

def costedCappedRelease {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (a w : Weights n) :
    CostedLaw (Weights n) := costedCappedOuter sdp p (cappedRunConfig n p) w (cappedRunConfig n p).T1 a 0

lemma costedCappedInner_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    (costedCappedInner sdp p c w a H t h).law = cappedInnerLoop p c w a H t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [costedCappedInner, cappedInnerLoop, CostedLaw.bind_law, costedAggregate_law]
    congr 1
    funext b
    simp only [CostedLaw.charge_law]
    split_ifs <;> simp [ih]

lemma costedCappedOuter_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedCappedOuter sdp p c w t a out).law = cappedOuterLoop p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    simp only [costedCappedOuter, cappedOuterLoop, CostedLaw.bind_law, CostedLaw.sample_law]
    congr 1
    funext noise
    simp only [CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, costedCappedInner_law]
      congr 1
      funext result
      cases result <;> simp [ih]

lemma costedCappedRelease_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (a w : Weights n) :
    (costedCappedRelease sdp p a w).law = cappedReleaseLaw p a w :=
  costedCappedOuter_law sdp p _ w _ a 0

def cappedInnerCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T2 * (aggregateCostBound sdp n c.oracle + cappedBlockCost n)

def cappedCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  (cappedRunConfig n p).T1 * (1 + cappedBlockCost n + cappedInnerCostBound sdp n (cappedRunConfig n p))

lemma costedCappedInner_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    (costedCappedInner sdp p c w a H t h).cost ≤ t * (aggregateCostBound sdp n c.oracle + cappedBlockCost n) := by
  let S := aggregateCostBound sdp n c.oracle + cappedBlockCost n
  induction t generalizing h with
  | zero => simp [costedCappedInner, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ aggregateCostBound sdp n c.oracle + (cappedBlockCost n + t * S) := by
        apply CostedLaw.bind_cost_le _ _ (costedAggregate_cost sdp c.oracle p.gamma w h)
        intro b
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · exact ih _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedCappedOuter_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedCappedOuter sdp p c w t a out).cost ≤ t * (1 + cappedBlockCost n + cappedInnerCostBound sdp n c) := by
  let S := 1 + cappedBlockCost n + cappedInnerCostBound sdp n c
  induction t generalizing a out with
  | zero => simp [costedCappedOuter, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ 1 + (cappedBlockCost n + (cappedInnerCostBound sdp n c + t * S)) := by
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (costedCappedInner_cost sdp p c _ _ _ _ _)
          intro result
          cases result <;> exact ih _ _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedCappedRelease_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (a w : Weights n) :
    (costedCappedRelease sdp p a w).cost ≤ cappedCostBound sdp n p :=
  costedCappedOuter_cost sdp p _ w _ a 0

lemma capped_runtime_parameter_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    let R := runtimeScale n p
    let c := cappedRunConfig n p
    (c.T1 : ℝ) ≤ 81 * R ∧ (c.T2 : ℝ) ≤ 102 * R ^ 3 ∧
      (c.oracle.K : ℝ) ≤ 2000000 * R ∧ (c.oracle.k : ℝ) ≤ 10000000000 * R := by
  let L := logFactor n 1 p
  let R := runtimeScale n p
  have hL := core_log_bounds hn (le_refl (1 : ℝ)) p hp
  have hLR : L ≤ R := main_log_le_runtimeScale hn hp
  obtain ⟨hT1, hT2⟩ := outer_horizons_bound hn (le_refl (1 : ℝ)) p hp hL
  obtain ⟨hK, hk⟩ := oracle_sample_sizes_bound hn (le_refl (1 : ℝ)) p hp hL
  change ((cappedRunConfig n p).T1 : ℝ) ≤ _ at hT1
  change ((cappedRunConfig n p).T2 : ℝ) ≤ _ at hT2
  change ((cappedRunConfig n p).oracle.K : ℝ) ≤ _ at hK
  change ((cappedRunConfig n p).oracle.k : ℝ) ≤ _ at hk
  dsimp only
  refine ⟨by linarith, ?_, by linarith, by linarith⟩
  have hR : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans (runtimeScale_bounds hp).2.2
  have hgi : 1 / p.gamma ≤ R := (runtimeScale_bounds hp).2.1
  have hg := hp.1
  calc
    _ ≤ 102 * L / p.gamma ^ 2 := hT2
    _ = 102 * L * (1 / p.gamma) ^ 2 := by ring
    _ ≤ 102 * R * R ^ 2 := mul_le_mul (by linarith)
      (pow_le_pow_left₀ (by positivity) hgi 2) (sq_nonneg _) (by positivity)
    _ = _ := by ring

lemma polynomial_capped_parameters :
    PolynomialRuntimeBound (fun n p => (cappedRunConfig n p).T1) ∧
    PolynomialRuntimeBound (fun n p => (cappedRunConfig n p).T2) ∧
    PolynomialRuntimeBound (fun n p => (cappedRunConfig n p).oracle.K) ∧
    PolynomialRuntimeBound (fun n p => (cappedRunConfig n p).oracle.k) := by
  refine ⟨⟨81, by norm_num, 1, ?_⟩, ⟨102, by norm_num, 3, ?_⟩,
    ⟨2000000, by norm_num, 1, ?_⟩, ⟨10000000000, by norm_num, 1, ?_⟩⟩ <;>
    intro n hn p hp
  · simpa using ENNReal.ofReal_le_ofReal (capped_runtime_parameter_bounds hn hp).1
  · simpa using ENNReal.ofReal_le_ofReal (capped_runtime_parameter_bounds hn hp).2.1
  · simpa using ENNReal.ofReal_le_ofReal (capped_runtime_parameter_bounds hn hp).2.2.1
  · simpa using ENNReal.ofReal_le_ofReal (capped_runtime_parameter_bounds hn hp).2.2.2

theorem cappedCostBound_polynomial (sdp : ExactSDPOracleCost) : PolynomialRuntimeBound (cappedCostBound sdp) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h2 : PolynomialRuntimeBound (fun _ _ => (2 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 2 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 100 (by norm_num)
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := by
    simpa only [vectorBlockCost, pow_two] using h100.mul (polynomial_vertices.mul polynomial_vertices)
  have hcap : PolynomialRuntimeBound (fun n _ => cappedBlockCost n) := hB.mul hB
  obtain ⟨hT1, hT2, hK, hk⟩ := polynomial_capped_parameters
  have hG : PolynomialRuntimeBound (fun n p => gaussianBatchCost n (cappedRunConfig n p).oracle.k) :=
    (hB.mul polynomial_vertices).mul (hk.add h1)
  have hTrial : PolynomialRuntimeBound (fun n p => trialCostBound n (cappedRunConfig n p).oracle) :=
    (hG.add h1).add hB
  have hW : PolynomialRuntimeBound (fun n p => witnessCostBound sdp n (cappedRunConfig n p).oracle) :=
    (hB.add (polynomial_sdp sdp)).add (hK.mul hTrial)
  have hAgg : PolynomialRuntimeBound (fun n p => aggregateCostBound sdp n (cappedRunConfig n p).oracle) :=
    polynomial_edges.mul (hB.add (h2.mul hW))
  exact hT1.mul ((h1.add hcap).add (hT2.mul (hAgg.add hcap)))

end DPCut
