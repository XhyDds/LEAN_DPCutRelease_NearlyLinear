import DPCut.FullReleasePrivacy
import DPCut.FullReleaseUtility

/-!
The complete statistical conclusion of Theorem 1 for the actual full release law.
The separate computational-model target also requires an implementation and cost proof.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- Theorem 1's privacy, nonnegative output, and simultaneous all-cut guarantee. -/
theorem theorem1_statistical : MainStatisticalStatement := by
  refine ⟨(2 : ℝ) ^ 166, by positivity, ?_⟩
  intro n hn p hp
  refine ⟨fullReleaseKernel hn p hp, inferInstance, ?_, fullRelease_private hn hp, ?_⟩
  · intro w _
    exact fullReleaseLaw_nonnegative hn hp w
  · exact fun w hw => fullRelease_utility hn hp w hw

end DPCut
