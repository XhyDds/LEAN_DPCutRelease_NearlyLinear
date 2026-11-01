import DPCut.CostedProgram
import DPCut.Arithmetic

/-! Compose a random law with a deterministic value/counter computation.
The uniform assigned cost uses the supremum of its stored counters. Connecting
those counters to execution steps is a separate obligation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut.CostedLaw
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

def mapArithmetic (p : CostedLaw α) (f : α → Arithmetic β) : CostedLaw β :=
  ⟨p.law.map (fun x => (f x).value), p.cost + ⨆ x, ((f x).steps : ℝ≥0∞)⟩

@[simp] lemma mapArithmetic_law (p : CostedLaw α) (f : α → Arithmetic β) :
    (p.mapArithmetic f).law = p.law.map (fun x => (f x).value) := rfl

lemma mapArithmetic_cost_le (p : CostedLaw α) (f : α → Arithmetic β)
    {a : ℝ≥0∞} {b : ℕ} (hp : p.cost ≤ a) (hf : ∀ x, (f x).steps ≤ b) :
    (p.mapArithmetic f).cost ≤ a + b := by
  apply add_le_add hp
  exact iSup_le (fun x => by exact_mod_cast hf x)

end DPCut.CostedLaw
