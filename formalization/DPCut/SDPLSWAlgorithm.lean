import DPCut.VerifiedLinearAlgebra

/-! SDP reduction using the formal LSW parameter, reported-time truncation
and independent restarts. Feasibility, approximation and assigned-cost bounds
are proved here; the timed interface does not certify operational solver runtime. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Metric
open scoped RealInnerProductSpace ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

namespace SDPCoordinates

variable (I : LinearAlgebraImplementation) {n : ℕ} (hn : 2 ≤ n)
  {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)

def solve (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ)
    (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  (costedRestart (A.run fuel D) repeats).mapArithmetic (decodeArithmetic I hn)

lemma solve_law (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ)
    (D : Weights n) :
    (solve I hn A fuel repeats D).law =
      (costedRestart (A.run fuel D) repeats).law.map (decode hn) := by
  simp only [solve, CostedLaw.mapArithmetic_law, decodeArithmetic_value]

lemma measurable_solve (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ) :
    Measurable (fun D => (solve I hn A fuel repeats D).law) := by
  simp only [solve_law, costedRestart_law]
  exact (Measure.measurable_map _ (measurable_decode hn)).comp
    (measurable_repeatUntil (A.measurable_run fuel) measurable_snd repeats)

instance solve_probability (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ)
    (D : Weights n) : IsProbabilityMeasure (solve I hn A fuel repeats D).law := by
  simp only [solve_law, costedRestart_law]
  letI := repeatUntil_probability (A.run fuel D).law measurable_id repeats
  exact Measure.isProbabilityMeasure_map (measurable_decode hn).aemeasurable

lemma solve_cost (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ) (D : Weights n) :
    (solve I hn A fuel repeats D).cost ≤ repeats * ((fuel : ℝ≥0∞) + 1) + oracleCharge n :=
  CostedLaw.mapArithmetic_cost_le _ _
    (costedRestart_cost _ (A.run_cost fuel D) repeats) (decodeArithmetic_cost I hn)

lemma measurable_objective (lam : ℝ) (D : Weights n) : Measurable (objective lam D) := by
  unfold objective
  apply Measurable.add
  · unfold pairing fractionalQuery
    fun_prop
  · exact (continuous_id.matrix_det.measurable.log).const_mul lam

lemma measurableSet_accurate (ε : ℝ) (D : Weights n) :
    MeasurableSet {x | LSW.Accurate (problem hn hlam hB) ε D x} := by
  have heq : {x | LSW.Accurate (problem hn hlam hB) ε D x} =
      body n ∩ {x : Space n | optimum lam (boundedObjective B D) -
        objective lam (boundedObjective B D) (lift x) ≤ ε} := by
    ext x
    exact accurate_iff hn hlam hB ε D x
  rw [heq]
  exact (body_compact n).isClosed.measurableSet.inter
    (measurableSet_le (measurable_const.sub
      ((measurable_objective lam (boundedObjective B D)).comp (continuous_lift n).measurable)) measurable_const)

lemma measurableSet_gap (ε : ℝ) (D : Weights n) : MeasurableSet
    {X : FeasibleMatrix n | ε < optimum lam D - objective lam D X.val} :=
  measurableSet_lt measurable_const
    (measurable_const.sub ((measurable_objective lam D).comp measurable_subtype_coe))

lemma solve_failure (A : TimedAlgorithm (Weights n) (Space n)) {ε : ℝ}
    (ha : ∀ D, ∀ᵐ z ∂A.completed D, LSW.Accurate (problem hn hlam hB) ε D z.2)
    {fuel : ℕ} (hfuel : 0 < fuel) (repeats : ℕ) (D : Weights n)
    (hmean : A.expectedCost D ≤ (fuel : ℝ≥0∞) / 2) :
    (solve I hn A fuel repeats D).law
      {X | ε < optimum lam (boundedObjective B D) - objective lam (boundedObjective B D) X.val}
      ≤ (1 / 2 : ℝ≥0∞) ^ repeats := by
  let Q (o : Option (Space n)) := o.elim True (LSW.Accurate (problem hn hlam hB) ε D)
  have hQ : MeasurableSet {o | Q o} := measurableSet_option_elim (measurableSet_accurate hn hlam hB ε D)
  have hrun : ∀ᵐ o ∂(A.run fuel D).law, Q o := by
    rw [A.run_law]
    apply (ae_map_iff (measurable_timeoutResult fuel).aemeasurable hQ).mpr
    filter_upwards [ha D] with z hz
    dsimp [timeoutResult]
    split_ifs
    · exact hz
    · trivial
  have hrep : ∀ᵐ o ∂(costedRestart (A.run fuel D) repeats).law, Q o := by
    rw [costedRestart_law]
    exact repeatUntil_ae measurable_id hQ trivial hrun repeats
  rw [solve_law, Measure.map_apply (measurable_decode hn)
    (measurableSet_gap ε (boundedObjective B D))]
  apply (measure_mono_ae ?_).trans (A.restart_failure_le hfuel D hmean repeats)
  filter_upwards [hrep] with o ho
  intro hbad
  cases o with
  | none => rfl
  | some x =>
    obtain ⟨hx, hg⟩ := (accurate_iff hn hlam hB ε D x).mp ho
    have hd : (decode hn (some x)).val = lift x := by simp [decode, safeMatrix, hx]
    change ε < optimum lam (boundedObjective B D) - objective lam (boundedObjective B D) (decode hn (some x)).val at hbad
    rw [hd] at hbad
    exact False.elim (not_lt_of_ge hg hbad)

end SDPCoordinates

/-- Public LSW complexity scale for this SDP. The objective magnitude `B` and
regularization `lam` occur explicitly, inside the logarithm. -/
def sdpLSWScale (n : ℕ) (lam B ε : ℝ) : ℝ :=
  1 + n * n + SDPCoordinates.oracleCharge n + Real.log (8 * n) +
    Real.log ((1 + 2 * B + lam * (n : ℝ)^2) / ε)

/-- LSW specialized to the paper's log-determinant SDP, including exact
feasibility and approximate optimality. No exact SDP solve is assumed. -/
theorem lsw_sdp (hLSW : LSWStatement) (I : LinearAlgebraImplementation) :
    ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ,
    ∀ (n : ℕ) (hn : 2 ≤ n) (lam B ε : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B),
      0 < ε → ε ≤ 1/2 →
      ∃ A : TimedAlgorithm (Weights n) (SDPCoordinates.Space n),
        (∀ D, ∀ᵐ z ∂A.completed D,
          LSW.Accurate (SDPCoordinates.problem hn hlam hB) ε D z.2) ∧
        ∀ D, A.expectedCost D ≤ ENNReal.ofReal (C * sdpLSWScale n lam B ε ^ degree) := by
  obtain ⟨C, hC, d, h⟩ := hLSW
  refine ⟨C, hC, d, ?_⟩
  intro n hn lam B ε hlam hB hε hεhalf
  have hdim : 1 ≤ Fintype.card (Fin n × Fin n) := by simp; nlinarith
  obtain ⟨A, ha, hc⟩ := h (Fin n × Fin n) inferInstance hdim (Weights n) inferInstance
    (SDPCoordinates.problem hn hlam hB) (SDPCoordinates.oracle hn hlam hB I) ε hε hεhalf
  refine ⟨A, ha, ?_⟩
  intro D
  have hs : LSW.scale (SDPCoordinates.problem hn hlam hB)
      (SDPCoordinates.oracle hn hlam hB I) ε = sdpLSWScale n lam B ε := by
    simp only [LSW.scale, SDPCoordinates.problem, SDPCoordinates.oracle, sdpLSWScale,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    congr 2
    congr 1
    ring
  simpa only [hs] using hc D

end DPCut
