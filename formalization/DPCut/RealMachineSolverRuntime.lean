import DPCut.RealMachineSolver

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

def runtimeCoefficient : ℝ :=
  1000000000 * (1 + EllipsoidOptimization.roundCoefficient)

theorem runtimeCoefficient_pos : 0 < runtimeCoefficient := by
  have h := EllipsoidOptimization.roundCoefficient_pos
  unfold runtimeCoefficient
  positivity

theorem solverBound_polynomial {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) :
    (solverBound n (iterations hn lam B epsilon hlam hB)
        (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon) : ℝ) ≤
      runtimeCoefficient * EllipsoidOptimization.scale (SDPFlat.problem hn hlam hB) epsilon ^ 10 := by
  let P := SDPFlat.problem hn hlam hB
  let S := EllipsoidOptimization.scale P epsilon
  have hs := EllipsoidOptimization.scale_bounds P he hehalf
  have hS : 1 ≤ S := hs.1
  have hm : (n:ℝ)*n ≤ S := by simpa using hs.2.1
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnS : (n:ℝ) ≤ S := (le_mul_of_one_le_right (by positivity) hnR).trans hm
  have hnplus : (n:ℝ)+1 ≤ 2*S := by linarith
  have hmplus : (n:ℝ)*n+1 ≤ 2*S := by linarith
  have hp6 : ((n:ℝ)+1)^6 ≤ 64*S^6 := by
    convert pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)+1) hnplus 6 using 1 <;> ring
  have hp4 : ((n:ℝ)+1)^4 ≤ 16*S^4 := by
    convert pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)+1) hnplus 4 using 1 <;> ring
  have hm3 : ((n:ℝ)*n+1)^3 ≤ 8*S^3 := by
    convert pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)*n+1) hmplus 3 using 1 <;> ring
  have h36 : S^3 ≤ S^6 := pow_le_pow_right₀ hS (by decide)
  have h46 : S^4 ≤ S^6 := pow_le_pow_right₀ hS (by decide)
  have h69 : S^6 ≤ S^9 := pow_le_pow_right₀ hS (by decide)
  have h610 : S^6 ≤ S^10 := pow_le_pow_right₀ hS (by decide)
  have h110 : S ≤ S^10 := by simpa using pow_le_pow_right₀ hS (show 1 ≤ 10 by decide)
  have hone6 : 1 ≤ S^6 := one_le_pow₀ hS
  have hinside : 50000*((n:ℝ)+1)^6 + 1000*((n:ℝ)*n+1)^3 + 3 ≤ 4000000*S^6 := by
    linarith
  have hfuel : (iterations hn lam B epsilon hlam hB : ℝ) ≤ 61*S^3 :=
    EllipsoidOptimization.feasibilityBudget_le_scale P he hehalf
  have hround : (EllipsoidOptimization.rounds P epsilon : ℝ) ≤
      EllipsoidOptimization.roundCoefficient*S := EllipsoidOptimization.rounds_le_scale P he hehalf
  have hstep : 100*((n:ℝ)+1)^4 +
      (iterations hn lam B epsilon hlam hB : ℝ) *
        (50000*((n:ℝ)+1)^6 + 1000*((n:ℝ)*n+1)^3 + 3) ≤ 245000000*S^9 := by
    have hprod := mul_le_mul hfuel hinside (by positivity)
      (by positivity : 0 ≤ 61*S^3)
    have heq : (61*S^3)*(4000000*S^6) = 244000000*S^9 := by ring
    rw [heq] at hprod
    linarith
  have htotal := mul_le_mul hround hstep (by positivity)
    (mul_nonneg EllipsoidOptimization.roundCoefficient_pos.le (by linarith : 0 ≤ S))
  have hprod : (EllipsoidOptimization.roundCoefficient*S)*(245000000*S^9) =
      245000000*EllipsoidOptimization.roundCoefficient*S^10 := by ring
  rw [hprod] at htotal
  unfold solverBound
  push_cast
  change 12000*((n:ℝ)+1)^6 +
    (EllipsoidOptimization.rounds P epsilon : ℝ) *
      (100*((n:ℝ)+1)^4 + (iterations hn lam B epsilon hlam hB : ℝ) *
        (50000*((n:ℝ)+1)^6 + 1000*((n:ℝ)*n+1)^3 + 3)) + 13*(n:ℝ)*n ≤ _
  unfold runtimeCoefficient
  nlinarith [mul_nonneg EllipsoidOptimization.roundCoefficient_pos.le (pow_nonneg (by linarith : 0 ≤ S) 10)]

theorem solverProgram_polynomial {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2)
    (tapes : Tapes) (s : State) :
    let output := (solverProgram n base (iterations hn lam B epsilon hlam hB)
      (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)).execute tapes s
    (output.operations - s.operations : ℕ) ≤
      runtimeCoefficient * EllipsoidOptimization.scale (SDPFlat.problem hn hlam hB) epsilon ^ 10 := by
  let output := (solverProgram n base (iterations hn lam B epsilon hlam hB)
    (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)).execute tapes s
  have hs := solverProgram_steps n base (iterations hn lam B epsilon hlam hB)
    (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon) tapes s
  have hnat : output.operations - s.operations ≤ solverBound n (iterations hn lam B epsilon hlam hB)
      (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon) :=
    Nat.sub_le_iff_le_add.mpr (by simpa only [Nat.add_comm] using hs)
  exact (Nat.cast_le.mpr hnat).trans
    (solverBound_polynomial hn lam B epsilon hlam hB he hehalf)

end DPCut.RealMachine.EllipsoidCode
