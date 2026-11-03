import DPCut.TypedImplementedRelease

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped ENNReal

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

abbrev InstructionFunction := ∀ (n : ℕ), 2 ≤ n → ∀ p : Parameters, p.Valid → ℕ

def totalInstructions (f : InstructionFunction) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  if h : 2 ≤ n ∧ p.Valid then f n h.1 p h.2 else 0

def PolynomialInstructions (f : InstructionFunction) : Prop := PolynomialRuntimeBound (totalInstructions f)

theorem PolynomialInstructions.of_existing {f : ℕ → Parameters → ℕ}
    (h : PolynomialRuntimeBound (fun n p => (f n p : ℝ≥0∞))) :
    PolynomialInstructions (fun n _ p _ => f n p) := by
  apply h.of_le
  intro n hn p hp
  simp [totalInstructions,hn,hp]

theorem PolynomialInstructions.constant (k : ℕ) :
    PolynomialInstructions (fun _ _ _ _ => k) := by
  apply (PolynomialRuntimeBound.constant (k+1:ℝ) (by positivity)).of_le
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp)]
  exact_mod_cast (show k ≤ k+1 by omega)

theorem PolynomialInstructions.of_le {f g : InstructionFunction}
    (hg : PolynomialInstructions g) (h : ∀ n hn p hp, f n hn p hp ≤ g n hn p hp) :
    PolynomialInstructions f := by
  apply (PolynomialRuntimeBound.of_le hg)
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp)]
  exact_mod_cast h n hn p hp

theorem PolynomialInstructions.add {f g : InstructionFunction}
    (hf : PolynomialInstructions f) (hg : PolynomialInstructions g) :
    PolynomialInstructions (fun n hn p hp => f n hn p hp+g n hn p hp) := by
  apply (PolynomialRuntimeBound.add hf hg).of_le
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp),Nat.cast_add]
  exact le_refl _

theorem PolynomialInstructions.mul {f g : InstructionFunction}
    (hf : PolynomialInstructions f) (hg : PolynomialInstructions g) :
    PolynomialInstructions (fun n hn p hp => f n hn p hp*g n hn p hp) := by
  apply (PolynomialRuntimeBound.mul hf hg).of_le
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp),Nat.cast_mul]
  exact le_refl _

theorem PolynomialInstructions.pow {f : InstructionFunction}
    (hf : PolynomialInstructions f) (k : ℕ) :
    PolynomialInstructions (fun n hn p hp => f n hn p hp^k) := by
  apply (PolynomialRuntimeBound.pow hf k).of_le
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp),Nat.cast_pow]
  exact le_refl _

theorem PolynomialInstructions.max {f g : InstructionFunction}
    (hf : PolynomialInstructions f) (hg : PolynomialInstructions g) :
    PolynomialInstructions (fun n hn p hp => max (f n hn p hp) (g n hn p hp)) :=
  (hf.add hg).of_le (fun _ _ _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

theorem PolynomialInstructions.scalarArray {f : InstructionFunction}
    (normal : Bool) (context : ∀ n, 2 ≤ n → ∀ p : Parameters, p.Valid → List ValueType)
    (hf : PolynomialInstructions f) :
    PolynomialInstructions (fun n hn p hp => (scalarArray normal (f n hn p hp) (context n hn p hp)).operations) :=
  ((PolynomialInstructions.constant 30).mul ((hf.add (PolynomialInstructions.constant 1)).pow 2)).of_le
    (fun n hn p hp => scalarArray_operations normal (f n hn p hp) (context n hn p hp))

theorem polynomial_instruction_vertices : PolynomialInstructions (fun n _ _ _ => n) :=
  PolynomialInstructions.of_existing (polynomial_vertices.of_le (fun _ _ _ _ => le_add_of_nonneg_right (by positivity)))

theorem polynomial_instruction_edges : PolynomialInstructions (fun n _ _ _ => Fintype.card (Edge n)) :=
  PolynomialInstructions.of_existing polynomial_edges

theorem polynomial_instruction_T1 :
    PolynomialInstructions (fun n _ p _ => (fullRunConfig n (precisionParameters p)).T1) :=
  PolynomialInstructions.of_existing polynomial_full_parameters.1.precision

theorem polynomial_instruction_T2 :
    PolynomialInstructions (fun n _ p _ => (fullRunConfig n (precisionParameters p)).T2) :=
  PolynomialInstructions.of_existing polynomial_full_parameters.2.1.precision

theorem polynomial_instruction_trials :
    PolynomialInstructions (fun n _ p _ => (fullRunConfig n (precisionParameters p)).oracle.K) :=
  PolynomialInstructions.of_existing polynomial_full_parameters.2.2.1.precision

theorem polynomial_instruction_batch :
    PolynomialInstructions (fun n _ p _ => (fullRunConfig n (precisionParameters p)).oracle.k) :=
  PolynomialInstructions.of_existing polynomial_full_parameters.2.2.2.precision

theorem polynomial_instruction_solver :
    PolynomialInstructions (fun n hn p hp => (releaseSolver hn p hp).operationBound) := by
  apply polynomial_releaseSolver.of_le
  intro n hn p hp
  simp only [totalInstructions,dif_pos (And.intro hn hp)]
  have h := ENNReal.ofReal_le_ofReal (releaseSolver hn p hp).operationBound_polynomial
  simpa only [ENNReal.ofReal_natCast,releaseSolver,solverScale] using h

end DPCut.TypedMachine
