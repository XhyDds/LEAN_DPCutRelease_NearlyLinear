import DPCut.PreprocessUtility
import DPCut.Statements

/-!
Lemma 12 (`lem:preprocess`) of the current root manuscript. Only the noisy
excess vector is released; the clipped component stays private. The exact
thresholds and the original inventory statement are unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace DPCut

/-- Pure privacy and simultaneous relative cut accuracy of preprocessing. -/
theorem lemma12 : PreprocessStatement := by
  intro n hn ε β γ hε _hε1 hβ hβ1 hγ _hγ1
  exact ⟨preprocess_private hε β γ, fun w hw => preprocess_utility hn hε hβ hβ1 hγ w hw⟩

end DPCut
