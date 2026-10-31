import DPCut.Lemma22
import DPCut.CutBasics

/-! Cut linearity, telescoping release accuracy, and the final discarded residual. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DPCut

lemma AllCuts.mono_error {n : ℕ} {w h : Weights n} {γ A B : ℝ}
    (hcut : AllCuts w h γ A) (hAB : A ≤ B) : AllCuts w h γ B := by
  intro S
  exact (hcut S).trans (by linarith)

lemma AllCuts.add {n : ℕ} {w₁ w₂ h₁ h₂ : Weights n} {γ A B : ℝ}
    (h₁c : AllCuts w₁ h₁ γ A) (h₂c : AllCuts w₂ h₂ γ B) :
    AllCuts (w₁ + w₂) (h₁ + h₂) γ (A + B) := by
  intro S
  rw [cut_add, cut_add]
  have ht := abs_add_le (cut w₁ S - cut h₁ S) (cut w₂ S - cut h₂ S)
  have he : cut w₁ S + cut w₂ S - (cut h₁ S + cut h₂ S) =
      (cut w₁ S - cut h₁ S) + (cut w₂ S - cut h₂ S) := by ring
  rw [he]
  linarith [h₁c S, h₂c S]

/-- Accuracy of everything already retired from the active mask. -/
def ReleaseInvariant {n : ℕ} (w a out : Weights n) (γ A : ℝ) : Prop :=
  Nonnegative out ∧ AllCuts (w - hadamard a w) out γ A

lemma releaseInvariant_initial {n : ℕ} (w : Weights n) (γ : ℝ) :
    ReleaseInvariant w 1 0 γ 0 := by
  constructor
  · intro e; simp
  · intro S; simp [cut, pairing, hadamard]

lemma retired_update_identity {n : ℕ} (w a r : Weights n) :
    w - hadamard (residualUpdate a r) w =
      (w - hadamard a w) + hadamard (hadamard a w) r := by
  funext e
  simp only [Pi.sub_apply, Pi.add_apply, hadamard, residualUpdate]
  ring

lemma ReleaseInvariant.update {n : ℕ} {w a out h r : Weights n} {γ A B : ℝ}
    (hi : ReleaseInvariant w a out γ A) (hh : Nonnegative h) (hr : IsMask r)
    (hcut : AllCuts (hadamard (hadamard a w) r) (hadamard h r) γ B) :
    ReleaseInvariant w (residualUpdate a r) (out + hadamard h r) γ (A + B) := by
  refine ⟨fun e => add_nonneg (hi.1 e) (mul_nonneg (hh e) (hr e).1), ?_⟩
  rw [retired_update_identity]
  exact hi.2.add hcut

lemma ReleaseInvariant.finish {n : ℕ} {w a out : Weights n} {γ A R : ℝ}
    (hi : ReleaseInvariant w a out γ A) (hw : Nonnegative w) (ha : IsMask a)
    (hγ : 0 ≤ γ) (hres : mass (hadamard a w) ≤ R) :
    Nonnegative out ∧ AllCuts w out γ (A + R) := by
  refine ⟨hi.1, ?_⟩
  intro S
  have hwA : Nonnegative (hadamard a w) := fun e => mul_nonneg (ha e).1 (hw e)
  have hrcut := cut_nonneg hwA S
  have hrle := (cut_le_mass hwA S).trans hres
  have hc := hi.2 S
  rw [cut_sub] at hc
  have ht := abs_add_le (cut w S - cut (hadamard a w) S - cut out S) (cut (hadamard a w) S)
  rw [abs_of_nonneg hrcut] at ht
  have he : cut w S - cut (hadamard a w) S - cut out S + cut (hadamard a w) S =
      cut w S - cut out S := by ring
  rw [he] at ht
  nlinarith [mul_nonneg hγ hrcut]

end DPCut
