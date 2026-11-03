import DPCut.TypedPublicData

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.TypedMachine

theorem scheduleFuel_value {Γ : List ValueType} (e : PublicExpressions Γ) (s : Environment Γ) :
    (scheduleFuel e).eval s =
      let range : ℝ := 1+2*e.run.terms.oracle.bound.eval s+
        e.run.oracle.lambda.eval s*(e.dimension:ℝ)^2
      let radius := (1/4:ℝ)*(e.accuracy.eval s/4/(2*range))
      Nat.floor (2*(((e.dimension*e.dimension:ℕ):ℝ)+2)*((e.dimension*e.dimension:ℕ):ℝ)*
        Real.log ((2*(e.dimension:ℝ))/radius))+1 := by
  norm_num [scheduleFuel,Term.eval,RealBinary.eval,RealUnary.eval,NaturalBinary.eval]

theorem scheduleRounds_value {Γ : List ValueType} (e : PublicExpressions Γ) (s : Environment Γ) :
    (scheduleRounds e).eval s =
      ⌈Real.log (2*(1+2*e.run.terms.oracle.bound.eval s+e.run.oracle.lambda.eval s*(e.dimension:ℝ)^2)/
        e.accuracy.eval s)/Real.log 2⌉₊+1 := by
  norm_num [scheduleRounds,Term.eval,RealBinary.eval,RealUnary.eval,NaturalBinary.eval]

theorem publicData_schedules {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    let S := releaseSolver hn p hp
    (publicData n p).1 4 =
      RealMachine.EllipsoidCode.iterations hn S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg ∧
    (publicData n p).1 5 =
      EllipsoidOptimization.rounds (SDPFlat.problem hn S.lambda_nonneg S.bound_nonneg) S.accuracy := by
  let e := publicExpressions n parameterTerms
  let s := parameterInput p
  have hs := publicExpressions_matches n parameterTerms s
  rw [parameterTerms_input] at hs
  have hB := hs.run.terms.1.2.2
  have hl := hs.run.oracle.lambda
  have ha := hs.accuracy
  have hf := scheduleFuel_value e s
  have hr := scheduleRounds_value e s
  change (scheduleFuel e).eval s = _ ∧ (scheduleRounds e).eval s = _
  dsimp only at hf
  rw [hf,hr,hB,hl,ha]
  constructor <;> rfl

end DPCut.TypedMachine
