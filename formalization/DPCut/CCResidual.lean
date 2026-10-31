import DPCut.ApplicationOptima

/-! Appendix C: residual sign coding and uniform correlation-clustering transfer. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

/-- The same sign map encodes disagreements and decodes fractional positive edges. -/
def ccResidual {n : ℕ} (π₀ : Partition n) (w : Weights n) : Weights n :=
  fun e => if π₀ e.val.1 = π₀ e.val.2 then 1 - w e else w e

lemma ccResidual_involutive {n : ℕ} (π₀ : Partition n) (w : Weights n) :
    ccResidual π₀ (ccResidual π₀ w) = w := by
  ext e; simp only [ccResidual]; split <;> ring

lemma mass_ccResidual {n : ℕ} (π₀ : Partition n) (w : Weights n) :
    mass (ccResidual π₀ w) = ccCost w π₀ := rfl

lemma ccResidual_bounded {n : ℕ} (π₀ : Partition n) {w : Weights n}
    (hw : Bounded 1 w) : Bounded 1 (ccResidual π₀ w) := by
  intro e
  dsimp [ccResidual]
  split
  · constructor <;> linarith [(hw e).1, (hw e).2]
  · exact hw e

lemma ccResidual_distance {n : ℕ} (π₀ : Partition n) (w w' : Weights n) :
    l1 (ccResidual π₀ w - ccResidual π₀ w') = l1 (w - w') := by
  unfold l1
  apply Finset.sum_congr rfl
  intro e _
  simp only [Pi.sub_apply, ccResidual]
  split
  · have he : (1 - w e) - (1 - w' e) = -(w e - w' e) := by ring
    rw [he, abs_neg]
  · rfl

lemma labelCut_sub {n : ℕ} {ι : Type*} [DecidableEq ι]
    (w h : Weights n) (π : Fin n → ι) : labelCut (w - h) π = labelCut w π - labelCut h π := by
  simp [labelCut, pairing, sub_mul, Finset.sum_sub_distrib]

lemma labelCut_discrete {n : ℕ} (w : Weights n) : labelCut w (id : Fin n → Fin n) = mass w := by
  unfold labelCut pairing mass
  apply Finset.sum_congr rfl
  intro e _
  simp [labelQuery, ne_of_lt e.property]

lemma cc_residual_identity {n : ℕ} (π₀ π : Partition n) (x h : Weights n) :
    ccCost (ccResidual π₀ h) π - ccCost (ccResidual π₀ x) π =
      2 * labelCut (h - x) π + 2 * labelCut (h - x) π₀ -
        4 * labelCut (h - x) (fun v => (π v, π₀ v)) + mass (h - x) := by
  simp only [ccCost, labelCut, pairing, mass, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : π e.val.1 = π e.val.2 <;> by_cases hb : π₀ e.val.1 = π₀ e.val.2 <;>
    simp [ccResidual, labelQuery, hp, hb, Prod.mk.injEq] <;> ring

lemma ccCost_nonneg {n : ℕ} {w : Weights n} (hw : Bounded 1 w) (π : Partition n) :
    0 ≤ ccCost w π := by
  apply Finset.sum_nonneg
  intro e _; split
  · exact sub_nonneg.mpr (hw e).2
  · exact (hw e).1

lemma cc_residual_transfer {n : ℕ} {x h : Weights n} {γ A : ℝ}
    (hx : Nonnegative x) (hγ : 0 ≤ γ) (hc : AllCuts x h γ A) (π₀ π : Partition n) :
    |ccCost (ccResidual π₀ h) π - ccCost (ccResidual π₀ x) π| ≤ 9 * γ * mass x + 18 * A := by
  have hb {ι : Type} [Fintype ι] [DecidableEq ι] (π : Fin n → ι) :
      |labelCut (h - x) π| ≤ γ * mass x + 2 * A := by
    rw [labelCut_sub]
    exact (label_cut_transfer hc π).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (labelCut_le_mass hx π) hγ) _)
  have h₁ := abs_le.mp (hb π)
  have h₂ := abs_le.mp (hb π₀)
  have h₃ := abs_le.mp (hb (fun v => (π v, π₀ v)))
  have h₄ := abs_le.mp (hb (id : Fin n → Fin n))
  rw [labelCut_discrete] at h₄
  rw [cc_residual_identity, abs_le]
  constructor <;> linarith

lemma cc_baseline_transfer {n : ℕ} {w h : Weights n} {π₀ : Partition n} {γ A c A₀ : ℝ}
    (hw : Bounded 1 w) (hγ : 0 ≤ γ) (hc : AllCuts (ccResidual π₀ w) h γ A)
    (hbase : ccCost w π₀ ≤ c * ccOptimum w + A₀) (hc0 : 0 ≤ c) (π : Partition n) :
    |ccCost (ccResidual π₀ h) π - ccCost w π| ≤
      (9 * c * γ) * ccCost w π + 9 * γ * A₀ + 18 * A := by
  have hx : Nonnegative (ccResidual π₀ w) := fun e => (ccResidual_bounded π₀ hw e).1
  have hh := cc_residual_transfer hx hγ hc π₀ π
  rw [ccResidual_involutive, mass_ccResidual] at hh
  have ho := mul_le_mul_of_nonneg_left (ccOptimum_le w π) hc0
  have hb := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 9 * γ)
  have hbo := mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ 9 * γ)
  nlinarith

/-- Combining residual transfer with a relative Bernoulli-rounding event. -/
lemma cc_surrogate_transfer {n : ℕ} {w p j : Weights n} {a b η R : ℝ}
    (hη : 0 ≤ η)
    (hres : ∀ π : Partition n, |ccCost p π - ccCost w π| ≤ a * ccCost w π + b)
    (hrnd : ∀ π : Partition n, |ccCost j π - ccCost p π| ≤ η * ccCost p π + R) :
    ∀ π : Partition n, |ccCost j π - ccCost w π| ≤
      (a + η * (1 + a)) * ccCost w π + (1 + η) * b + R := by
  intro π
  have hh := (abs_sub_le (ccCost j π) (ccCost p π) (ccCost w π)).trans
    (add_le_add (hrnd π) (hres π))
  have hu := mul_le_mul_of_nonneg_left (abs_le.mp (hres π)).2 hη
  nlinarith

lemma cc_approximation_transfer {n : ℕ} {w j : Weights n} {θ B ρ : ℝ}
    (hθ : θ < 1) (hρ : 0 ≤ ρ) (hcmp : ∀ π : Partition n,
      |ccCost j π - ccCost w π| ≤ θ * ccCost w π + B)
    {π : Partition n} (hπ : ccCost j π ≤ ρ * ccOptimum j) :
    ccCost w π ≤ ρ * (1 + θ) / (1 - θ) * ccOptimum w + (ρ + 1) / (1 - θ) * B := by
  obtain ⟨πstar, hopt⟩ := ccOptimum_exists w
  have h₁ := (abs_le.mp (hcmp π)).1
  have h₂ := (abs_le.mp (hcmp πstar)).2
  rw [hopt] at h₂
  have hs := mul_le_mul_of_nonneg_left (ccOptimum_le j πstar) hρ
  have hr := mul_le_mul_of_nonneg_left h₂ hρ
  have hpos : 0 < 1 - θ := by linarith
  have hh : ccCost w π ≤ (ρ * (1 + θ) * ccOptimum w + (ρ + 1) * B) / (1 - θ) :=
    (le_div_iff₀ hpos).mpr (by nlinarith)
  convert hh using 1
  ring

end DPCut
