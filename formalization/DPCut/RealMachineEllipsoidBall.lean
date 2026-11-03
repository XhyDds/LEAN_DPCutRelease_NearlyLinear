import DPCut.RealMachineTargetScript

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def ballProgram (n base : ℕ) : Code :=
  .seq (arrayProgram (vectorAddress (slot (n*n) base 0)) (fun _ : Fin (n*n) => .rational 0))
    (matrixMapProgram (n*n) (slot (n*n) base 1) (fun ij => if ij.1 = ij.2 then
      .mul (.rational 2) (.cast (.natural n)) else .rational 0))

theorem ballProgram_steps (n base : ℕ) : Steps (ballProgram n base) (20 * (n + 1) ^ 4) := by
  have hc := arrayProgram_steps (vectorAddress (slot (n*n) base 0)) (fun _ : Fin (n*n) => Expr.rational 0) 1 (by intro i; rfl)
  have ha := matrixMap_steps (n*n) (slot (n*n) base 1) 4 (fun ij => if ij.1 = ij.2 then
    Expr.mul (.rational 2) (.cast (.natural n)) else .rational 0) (by
      intro ij; dsimp only; split <;> norm_num [Expr.operations])
  exact (hc.seq ha).mono (by ring_nf; omega)

theorem ballProgram_context {n : ℕ} (base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : TargetCode.Context n base lam B threshold D s) :
    TargetCode.Context n base lam B threshold D ((ballProgram n base).execute tapes s) := by
  have hceil : (ballProgram n base).RealWriteCeiling (slot (n*n) base 3) :=
    ⟨ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)),
      ceiling_matrixMap _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))⟩
  exact TargetCode.context_of_high n base lam B threshold D s _
    (Code.realWriteCeiling_frame _ _ hceil tapes s) hs

theorem ballProgram_value {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (tapes : Tapes) (s : State) :
    Matches (n*n) base ((ballProgram n base).execute tapes s)
      (EllipsoidMethod.Ellipsoid.ball 0 (2*(n:ℝ)) (by exact_mod_cast (show 0 < 2*n by omega))) := by
  let first := (arrayProgram (vectorAddress (slot (n*n) base 0)) (fun _ : Fin (n*n) => Expr.rational 0)).execute tapes s
  let result := (matrixMapProgram (n*n) (slot (n*n) base 1) (fun ij => if ij.1 = ij.2 then
    Expr.mul (.rational 2) (.cast (.natural n)) else .rational 0)).execute tapes first
  have hcenter : center (n*n) base result = 0 := by
    ext i
    have hi := vector_before_slot (n*n) base 0 1 (by decide) i
    change result.memory.real (vectorAddress (slot (n*n) base 0) i) = 0
    rw [matrixMap_frame _ _ _ _ _ _ (by
      intro ij
      have ho := (matrix_range (slot (n*n) base 1) ij).1
      omega)]
    have hv := arrayProgram_value tapes s (vectorAddress (slot (n*n) base 0)) (fun _ : Fin (n*n) => Expr.rational 0)
      (vectorAddress_injective _) (fun _ _ => realFrame_rational _ _) i
    simpa only [Expr.eval, Rat.cast_zero] using hv
  have haxes : axes (n*n) base result = (2*(n:ℝ)) • (1 : Matrix (Fin (n*n)) (Fin (n*n)) ℝ) := by
    have hv := matrixMap_value tapes first (n*n) (slot (n*n) base 1) (fun ij => if ij.1 = ij.2 then
      Expr.mul (.rational 2) (.cast (.natural n)) else .rational 0) (by
        intro ij kl
        dsimp only
        split
        · exact realFrame_mul (realFrame_rational _ _) (by intro memory value; rfl)
        · exact realFrame_rational _ _)
    funext i j
    change readMatrix (n*n) (slot (n*n) base 1) result.memory i j = _
    rw [hv i j]
    by_cases hij : i = j <;> simp [Expr.eval, hij]
  change Matches (n*n) base result _
  refine ⟨hcenter, ?_⟩
  rw [haxes]
  ext x i
  simp [Matrix.toEuclideanLin_apply, Matrix.smul_mulVec, EllipsoidMethod.Ellipsoid.ball,
    LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, Units.smul_def, PiLp.smul_apply, smul_eq_mul]

end DPCut.RealMachine.EllipsoidCode
