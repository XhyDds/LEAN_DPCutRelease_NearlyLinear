import DPCut.MultiplicativeWeights
import DPCut.Lemma20

/-! Deterministic initialization and progress of each rejected inner iteration. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

lemma Aggregate.Partition.pairing_mass {n : ℕ} {a : Aggregate n} (ha : a.Partition)
    (h : Weights n) : pairing h a.plus + pairing h a.minus + pairing h a.residual = mass h := by
  simp only [pairing, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = h e * (a.plus e + a.minus e + a.residual e) := by ring
    _ = _ := by rw [ha.2.2.2 e]; simp

lemma plus_normalized_gap {γ M H x y : ℝ} (hγ : 0 < γ) (hM : 0 < M) (hH : 0 < H)
    (hHH : H ≤ (1 + γ / 4) * M) (hx : H ≤ 3 * x) (hy : (1 + γ) * y ≤ x) :
    γ / (4 * (1 + γ)) ≤ x / H - y / M := by
  have hx3 : (1 / 3 : ℝ) ≤ x / H := (le_div_iff₀ hH).mpr (by linarith)
  have hx0 : 0 ≤ x / H := by linarith
  have hxq : H * (x / H) = x := mul_div_cancel₀ _ hH.ne'
  have hyq : M * (y / M) = y := mul_div_cancel₀ _ hM.ne'
  have hr := mul_le_mul_of_nonneg_right hHH hx0
  have hab : (1 + γ) * (y / M) ≤ (1 + γ / 4) * (x / H) := by
    apply (mul_le_mul_iff_right₀ hM).mp
    have hyq' := congrArg (fun z => (1 + γ) * z) hyq
    nlinarith only [hy, hxq, hr, hyq']
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + γ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hx3 hγ.le]

lemma minus_normalized_gap {γ M H x y : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4)
    (hM : 0 < M) (hH : 0 < H) (hMH : M ≤ H) (hx : H ≤ 3 * x)
    (hy : x ≤ (1 - γ) * y) (hy0 : 0 ≤ y) :
    γ / (4 * (1 + γ)) ≤ y / M - x / H := by
  have hx3 : (1 / 3 : ℝ) ≤ x / H := (le_div_iff₀ hH).mpr (by linarith)
  have hx0 : 0 ≤ x / H := by linarith
  have hy0' : 0 ≤ y / M := div_nonneg hy0 hM.le
  have hxq : H * (x / H) = x := mul_div_cancel₀ _ hH.ne'
  have hyq : M * (y / M) = y := mul_div_cancel₀ _ hM.ne'
  have hr := mul_le_mul_of_nonneg_right hMH hx0
  have hab : x / H ≤ (1 - γ) * (y / M) := by
    apply (mul_le_mul_iff_right₀ hM).mp
    have hyq' := congrArg (fun z => (1 - γ) * z) hyq
    nlinarith only [hy, hxq, hr, hyq']
  have hy3 : (1 / 3 : ℝ) ≤ y / M := by nlinarith
  have hgap : γ / 3 ≤ y / M - x / H := by
    nlinarith [mul_le_mul_of_nonneg_left hy3 hγ.le]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + γ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 4 * (1 + γ) by positivity)]

theorem innerNext_progress {n : ℕ} (p : Parameters) (c : RunConfig) {w h : Weights n}
    {M H B : ℝ} {a : Aggregate n} (hw : Nonnegative w) (hM : 0 < M) (hH : 0 < H)
    (hmw : mass w = M) (hh : EstimateValid w H h) (hMH : M ≤ H)
    (hHH : H ≤ (1 + p.gamma / 4) * M) (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hη : c.eta = stepSize p.gamma) (ha : a.Partition) (hacc : a.Accurate w h p.gamma B)
    (hreject : ¬a.Accepts h) :
    EstimateValid w H (innerNext c H h a) ∧
      p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2) ≤
        potential w h M H - potential w (innerNext c H h a) M H := by
  have hsum := ha.pairing_mass h
  rw [hh.2.1] at hsum
  change ¬max (pairing h a.plus) (pairing h a.minus) ≤ pairing h a.residual at hreject
  unfold innerNext
  split_ifs with hover
  · have hdom : H ≤ 3 * pairing h a.plus := by
      rw [max_eq_left hover] at hreject
      linarith
    have hgap := plus_normalized_gap hγ hM hH hHH hdom hacc.1
    rw [← pairing_normalized_difference] at hgap
    refine ⟨hh.update hH _ _, ?_⟩
    rw [hη]
    exact mw_potential_progress n w h a.plus M H p.gamma 1 hw hh.1 ha.1 hM hH
      hmw hh.2.1 hh.2.2 hγ hγ1 (Or.inl rfl) (by simpa using hgap)
  · have hdom : H ≤ 3 * pairing h a.minus := by
      rw [max_eq_right (le_of_not_ge hover)] at hreject
      linarith
    have hy0 : 0 ≤ pairing w a.minus := Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (ha.2.1 e).1
    have hgap := minus_normalized_gap hγ hγ1 hM hH hMH hdom hacc.2.1 hy0
    have hgap' : p.gamma / (4 * (1 + p.gamma)) ≤
        (-1 : ℝ) * pairing (fun e => h e / H - w e / M) a.minus := by
      rw [pairing_normalized_difference]
      linarith
    refine ⟨hh.update hH _ _, ?_⟩
    rw [hη]
    exact mw_potential_progress n w h a.minus M H p.gamma (-1) hw hh.1 ha.2.1 hM hH
      hmw hh.2.1 hh.2.2 hγ hγ1 (Or.inr rfl) hgap'

lemma masked_positive_support {n : ℕ} {w a : Weights n} (_hw : Nonnegative w)
    (ha : IsMask a) (e : Edge n) (he : 0 < hadamard a w e) : 0 < a e := by
  by_contra hp
  have hz : a e = 0 := le_antisymm (le_of_not_gt hp) (ha e).1
  simp [hadamard, hz] at he

lemma mask_mass_pos {n : ℕ} {w a : Weights n} (hw : Nonnegative w) (ha : IsMask a)
    (hm : 0 < mass (hadamard a w)) : 0 < mass a := by
  obtain ⟨e, he, hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun e _ => mul_nonneg (ha e).1 (hw e))).mp hm
  exact Finset.sum_pos' (fun e _ => (ha e).1)
    ⟨e, he, masked_positive_support hw ha e hp⟩

lemma initialEstimate_valid {n : ℕ} {w a : Weights n} {H : ℝ} (hw : Nonnegative w)
    (ha : IsMask a) (hm : 0 < mass (hadamard a w)) (hH : 0 < H) :
    EstimateValid (hadamard a w) H (initialEstimate H a) := by
  have hmA := mask_mass_pos hw ha hm
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact div_nonneg (mul_nonneg hH.le (ha e).1) hmA.le
  · simp only [mass, initialEstimate, ← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ H hmA.ne'
  · intro e he
    exact div_pos (mul_pos hH (masked_positive_support hw ha e he)) hmA

theorem initialEstimate_potential_le {n : ℕ} (hn : 2 ≤ n) {U H : ℝ} {w a : Weights n}
    (hU : 0 ≤ U) (hw : Bounded U w) (ha : IsMask a) (hH : 0 < H)
    (hm : 0 < mass (hadamard a w)) (hlarge : n * U ≤ mass (hadamard a w)) :
    potential (hadamard a w) (initialEstimate H a) (mass (hadamard a w)) H ≤
      mass (hadamard a w) * Real.log n := by
  let M := mass (hadamard a w)
  have hw0 : Nonnegative w := fun e => (hw e).1
  have hwA : Nonnegative (hadamard a w) := fun e => mul_nonneg (ha e).1 (hw e).1
  have hv := initialEstimate_valid hw0 ha hm hH
  have hmA := mask_mass_pos hw0 ha hm
  have hcard : mass a ≤ (n : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Edge n, (1 : ℝ) := Finset.sum_le_sum fun e _ => (ha e).2
      _ = (Fintype.card (Edge n) : ℝ) := by simp
      _ ≤ _ := edge_card_le_square n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [(normalizedKL_finite_formula hwA hv.1 hm hH rfl hv.2.1 hv.2.2).2]
  rw [mass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : hadamard a w e = 0
  · simp [he]
  · have he0 : 0 < hadamard a w e := lt_of_le_of_ne (hwA e) (Ne.symm he)
    have ha0 := masked_positive_support hw0 ha e he0
    have hr : (hadamard a w e / M) / (initialEstimate H a e / H) = w e * mass a / M := by
      dsimp [hadamard, initialEstimate]
      field_simp
    have hrpos : 0 < (hadamard a w e / M) / (initialEstimate H a e / H) :=
      div_pos (div_pos he0 hm) (div_pos (hv.2.2 e he0) hH)
    have hrle : (hadamard a w e / M) / (initialEstimate H a e / H) ≤ n := by
      rw [hr]
      apply (div_le_iff₀ hm).mpr
      have hu := mul_le_mul (hw e).2 hcard hmA.le hU
      have hnM := mul_le_mul_of_nonneg_left hlarge hn0.le
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hrpos hrle) he0.le

lemma innerHorizon_progress_budget {n : ℕ} {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M) :
    M * Real.log n < (innerHorizon n γ : ℝ) * (γ ^ 2 * M / (64 * (1 + γ) ^ 2)) := by
  have hd : 0 < γ ^ 2 * M / (64 * (1 + γ) ^ 2) := by positivity
  have hceil := Nat.le_ceil (64 * (1 + γ) ^ 2 * Real.log n / γ ^ 2)
  have ht : 64 * (1 + γ) ^ 2 * Real.log n / γ ^ 2 < (innerHorizon n γ : ℝ) := by
    unfold innerHorizon
    push_cast
    linarith
  have he : (64 * (1 + γ) ^ 2 * Real.log n / γ ^ 2) *
      (γ ^ 2 * M / (64 * (1 + γ) ^ 2)) = M * Real.log n := by field_simp
  rw [← he]
  exact mul_lt_mul_of_pos_right ht hd

end DPCut
