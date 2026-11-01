import DPCut.SDPLSWProblem

/-! Semantic specification of the feasible output and fallback decoder.
The counted implementation is in `SDPArithmeticFallback`. -/
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

end SDPCoordinates
end DPCut
