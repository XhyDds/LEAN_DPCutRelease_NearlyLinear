import DPCut.SDPLSWProblem

/-! Conditional SDP implementation, with an operational timeout and independent
restarts. This file proves the reduction from LSW; no approximate-SDP solver is
assumed. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Metric
open scoped RealInnerProductSpace ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

abbrev FeasibleMatrix (n : ℕ) := {X : Mat n // X ∈ feasible n}

namespace SDPCoordinates

variable {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)

def safeMatrix (x : Space n) : FeasibleMatrix n :=
  if h : x ∈ body n then ⟨lift x, h.2⟩ else ⟨1, feasible_one hn⟩

lemma safeMatrix_val (x : Space n) :
    (safeMatrix hn x).val = if x ∈ body n then lift x else 1 := by
  unfold safeMatrix
  split_ifs <;> rfl

/-- The fallback guard can be evaluated using the permitted PSD primitive and
one norm comparison; it does not need a universal quadratic-form search. -/
lemma mem_body_iff_primitive (P : LinearAlgebraPrimitives) (x : Space n) :
    x ∈ body n ↔ ‖x‖ ≤ 2*(n:ℝ) ∧ P.psdWitness n (slack x) = none := by
  constructor
  · intro hx
    exact ⟨by simpa using hx.1, (P.none_iff n (slack x) (slack_hermitian x)).mpr
      ((slack_posSemidef_iff x).mpr hx.2)⟩
  · rintro ⟨hx,hp⟩
    exact ⟨by simpa using hx, (slack_posSemidef_iff x).mp
      ((P.none_iff n (slack x) (slack_hermitian x)).mp hp)⟩

lemma safeMatrix_val_primitive (P : LinearAlgebraPrimitives) (x : Space n) :
    (safeMatrix hn x).val =
      if ‖x‖ ≤ 2*(n:ℝ) ∧ P.psdWitness n (slack x) = none then lift x else 1 := by
  rw [safeMatrix_val, mem_body_iff_primitive P x]
  split_ifs <;> rfl

lemma measurable_safeMatrix : Measurable (safeMatrix hn) := by
  refine (show Measurable (fun x => (safeMatrix hn x).val) from ?_).subtype_mk
  simp_rw [safeMatrix_val]
  exact Measurable.ite (body_compact n).isClosed.measurableSet
    (continuous_lift n).measurable measurable_const

def decode (o : Option (Space n)) : FeasibleMatrix n :=
  o.elim ⟨1, feasible_one hn⟩ (safeMatrix hn)

lemma measurable_decode : Measurable (decode hn) :=
  measurable_option_elim _ (measurable_safeMatrix hn)

def solve (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ)
    (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  (costedRestart (A.run fuel D) repeats).map (decode hn) (oracleCharge n)

lemma measurable_solve (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ) :
    Measurable (fun D => (solve hn A fuel repeats D).law) := by
  simp only [solve, CostedLaw.map_law, costedRestart_law]
  exact (Measure.measurable_map _ (measurable_decode hn)).comp
    (measurable_repeatUntil (A.measurable_run fuel) measurable_snd repeats)

instance solve_probability (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ)
    (D : Weights n) : IsProbabilityMeasure (solve hn A fuel repeats D).law := by
  simp only [solve, CostedLaw.map_law, costedRestart_law]
  letI := repeatUntil_probability (A.run fuel D).law measurable_id repeats
  exact Measure.isProbabilityMeasure_map (measurable_decode hn).aemeasurable

lemma solve_cost (A : TimedAlgorithm (Weights n) (Space n)) (fuel repeats : ℕ) (D : Weights n) :
    (solve hn A fuel repeats D).cost ≤ repeats * ((fuel : ℝ≥0∞) + 1) + oracleCharge n :=
  add_le_add_right (costedRestart_cost _ (A.run_cost fuel D) repeats) _

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
    (solve hn A fuel repeats D).law
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
  rw [solve, CostedLaw.map_law, Measure.map_apply (measurable_decode hn)
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
theorem lsw_sdp (hLSW : LSWStatement) (P : LinearAlgebraPrimitives) :
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
    (SDPCoordinates.problem hn hlam hB) (SDPCoordinates.oracle hn hlam hB P) ε hε hεhalf
  refine ⟨A, ha, ?_⟩
  intro D
  have hs : LSW.scale (SDPCoordinates.problem hn hlam hB)
      (SDPCoordinates.oracle hn hlam hB P) ε = sdpLSWScale n lam B ε := by
    simp only [LSW.scale, SDPCoordinates.problem, SDPCoordinates.oracle, sdpLSWScale,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    congr 2
    congr 1
    ring
  simpa only [hs] using hc D

end DPCut
