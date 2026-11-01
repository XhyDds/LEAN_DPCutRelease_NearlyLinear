import DPCut.SDPSeparation
import DPCut.Lemma19

/-! Specialization of the external LSW problem and oracle to the actual SDP.
Inputs outside a public l1 bound are replaced by zero. On all bounded inputs
this totalization is the identity. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Metric
open scoped RealInnerProductSpace BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

@[fun_prop] lemma continuous_l1 (n : ℕ) : Continuous (l1 (n := n)) := by
  unfold l1; fun_prop

def boundedObjective {n : ℕ} (B : ℝ) (D : Weights n) : Weights n :=
  if l1 D ≤ B then D else 0

@[fun_prop] lemma measurable_boundedObjective (n : ℕ) (B : ℝ) :
    Measurable (boundedObjective (n := n) B) := by
  exact Measurable.ite (measurableSet_le (continuous_l1 n).measurable measurable_const)
    measurable_id measurable_const

lemma boundedObjective_eq {n : ℕ} {B : ℝ} {D : Weights n} (hD : l1 D ≤ B) :
    boundedObjective B D = D := if_pos hD

lemma boundedObjective_l1_le {n : ℕ} {B : ℝ} (hB : 0 ≤ B) (D : Weights n) :
    l1 (boundedObjective B D) ≤ B := by
  unfold boundedObjective
  split_ifs with h
  · exact h
  · simpa [l1] using hB

namespace SDPCoordinates

variable {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)

def problem : LSW.Problem (Fin n × Fin n) (Weights n) where
  body := body n
  value D x := objective lam (boundedObjective B D) (lift x)
  measurable_value := by
    unfold objective pairing fractionalQuery
    apply Measurable.add
    · fun_prop
    · apply Measurable.const_mul
      exact ((continuous_lift n).comp continuous_snd).matrix_det.measurable.log
  convex := body_convex n
  compact := body_compact n
  concave D := by
    refine ⟨body_convex n, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp only
    rw [lift_combo x y hab]
    exact (objective_concaveOn hn hlam (boundedObjective B D)).2 hx.2 hy.2 ha hb hab
  innerRadius := 1/4
  outerRadius := 2*n
  inner_pos := by norm_num
  radii_order := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  inner_ball := inner_ball hn
  outer_ball := fun _ h => h.1
  rangeBound := 1 + 2 * B + lam * (n : ℝ) ^ 2
  range_one_le := by nlinarith [mul_nonneg hlam (sq_nonneg (n : ℝ))]
  range_le D x hx y hy := (objective_range_bound hn hlam (boundedObjective_l1_le hB D) hx.2 hy.2).trans (by linarith)

/-- Public first-order-oracle budget, including projection, determinant,
inverse and negative quadratic-form witnesses. `Counted.answer_steps` proves
the budget for the scalar implementation; log remains an elementary real op. -/
def oracleCharge (n : ℕ) : ℕ := 1000 * (n+1)^6 + 2 * linearAlgebraPrimitiveCost n

def answer (P : LinearAlgebraPrimitives) (lam B : ℝ)
    (q : Weights n × Space n) : LSW.Reply (Fin n × Fin n) :=
  if 2 * (n : ℝ) < ‖q.2‖ then .inl q.2 else
    (P.psdWitness n (slack q.2)).elim
      (.inr (objective lam (boundedObjective B q.1) (lift q.2),
        normal n (objectiveMatrix (boundedObjective B q.1) + lam • (lift q.2)⁻¹)))
      (fun v => .inl (normal n (-(Matrix.vecMulVec v v))))

lemma measurable_answer (P : LinearAlgebraPrimitives) (lam B : ℝ) :
    Measurable (answer (n := n) P lam B) := by
  have hm : Measurable (fun q : Weights n × Space n => P.psdWitness n (slack q.2)) :=
    (P.measurable_psdWitness n).comp ((continuous_slack n).measurable.comp measurable_snd)
  have hf : Measurable (fun q : Weights n × Space n =>
      (objective lam (boundedObjective B q.1) (lift q.2),
        normal n (objectiveMatrix (boundedObjective B q.1) + lam • (lift q.2)⁻¹))) := by
    apply Measurable.prodMk
    · unfold objective pairing fractionalQuery
      fun_prop
    · apply (normal n).continuous_of_finiteDimensional.measurable.comp
      have hi : Measurable (fun q : Weights n × Space n => (lift q.2)⁻¹) :=
        (measurable_matrix_inv n).comp ((continuous_lift n).measurable.comp measurable_snd)
      change Measurable (fun q : Weights n × Space n => fun i j =>
        objectiveMatrix (boundedObjective B q.1) i j + lam * ((lift q.2)⁻¹ i j))
      apply measurable_pi_lambda _
      intro i
      apply measurable_pi_lambda _
      intro j
      apply Measurable.add
      · simp only [objectiveMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        apply Finset.measurable_sum
        intro e _
        exact (((measurable_pi_apply e).comp
          ((measurable_boundedObjective n B).comp measurable_fst)).div_const 4).mul_const _
      · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hi)).const_mul lam
  have hg : Measurable (fun v : Fin n → ℝ =>
      (Sum.inl (normal n (-(Matrix.vecMulVec v v))) : LSW.Reply (Fin n × Fin n))) := by
    apply measurable_inl.comp
    apply (normal n).continuous_of_finiteDimensional.measurable.comp
    change Measurable (fun v : Fin n → ℝ => fun i j => -(v i * v j))
    fun_prop
  unfold answer
  apply Measurable.ite (measurableSet_lt measurable_const (continuous_snd.norm.measurable))
    (measurable_inl.comp measurable_snd)
  exact measurable_option_elim_vary (measurable_inr.comp hf) hg hm

lemma answer_correct (P : LinearAlgebraPrimitives) (D : Weights n) (x : Space n) :
    LSW.CorrectReply (problem hn hlam hB) D x (answer P lam B (D,x)) := by
  unfold answer
  dsimp only
  split_ifs with hx
  · exact ball_cut x hx
  · have hb : ‖x‖ ≤ 2 * (n : ℝ) := le_of_not_gt hx
    cases h : P.psdWitness n (slack x) with
    | none =>
      have hp := (P.none_iff n (slack x) (slack_hermitian x)).mp h
      have hmem : x ∈ body n := ⟨by simpa using hb, (slack_posSemidef_iff x).mp hp⟩
      refine ⟨hmem, rfl, ?_⟩
      intro y hy
      exact objective_supergradient hn hlam (boundedObjective B D) hmem hy
    | some v =>
      exact psd_cut hn x v (P.witness_negative n (slack x) v h)

lemma accurate_iff (ε : ℝ) (D : Weights n) (x : Space n) :
    LSW.Accurate (problem hn hlam hB) ε D x ↔ x ∈ body n ∧
      optimum lam (boundedObjective B D) - objective lam (boundedObjective B D) (lift x) ≤ ε := by
  constructor
  · rintro ⟨hx, ha⟩
    refine ⟨hx, ?_⟩
    have hopt := optimizer_isOptimizer hn lam (boundedObjective B D)
    have h := ha (encode (optimizer lam (boundedObjective B D))) (encode_mem hn hopt.1)
    change objective lam (boundedObjective B D) (lift (encode (optimizer lam (boundedObjective B D)))) - _ ≤ ε at h
    rwa [lift_encode hopt.1, ← optimum_eq_objective_optimizer hn] at h
  · rintro ⟨hx, ha⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hopt := (optimizer_isOptimizer hn lam (boundedObjective B D)).2 (lift y) hy.2
    rw [← optimum_eq_objective_optimizer hn] at hopt
    exact (sub_le_sub_right hopt _).trans ha

end SDPCoordinates
end DPCut
