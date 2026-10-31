import DPCut.CappedLSWWitness
import DPCut.ApplicationRuntimeBounds

/-! Polynomial vertex-count bounds for the LSW-based application solvers.
All application parameters are fixed before the vertex count, as in Appendix C. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

lemma PolynomialVertexBound.pow {f : ℕ → ℝ≥0∞} (hf : PolynomialVertexBound f) (k : ℕ) :
    PolynomialVertexBound (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using PolynomialVertexBound.constant 1 (by norm_num)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

lemma PolynomialVertexBound.real_add {f g : ℕ → ℝ}
    (hf : PolynomialVertexBound (fun n => ENNReal.ofReal (f n)))
    (hg : PolynomialVertexBound (fun n => ENNReal.ofReal (g n))) :
    PolynomialVertexBound (fun n => ENNReal.ofReal (f n+g n)) :=
  (hf.add hg).mono (fun _ _ => ENNReal.ofReal_add_le)

lemma PolynomialVertexBound.real_mul {f g : ℕ → ℝ}
    (hf : PolynomialVertexBound (fun n => ENNReal.ofReal (f n)))
    (hg : PolynomialVertexBound (fun n => ENNReal.ofReal (g n)))
    (h0 : ∀ n, 2 ≤ n → 0 ≤ f n) :
    PolynomialVertexBound (fun n => ENNReal.ofReal (f n*g n)) :=
  (hf.mul hg).mono (fun n hn => le_of_eq (ENNReal.ofReal_mul (h0 n hn)))

lemma PolynomialVertexBound.real_pow {f : ℕ → ℝ}
    (hf : PolynomialVertexBound (fun n => ENNReal.ofReal (f n))) (k : ℕ)
    (h0 : ∀ n, 2 ≤ n → 0 ≤ f n) :
    PolynomialVertexBound (fun n => ENNReal.ofReal (f n^k)) :=
  (hf.pow k).mono (fun n hn => le_of_eq (ENNReal.ofReal_pow (h0 n hn) k))

lemma PolynomialVertexBound.ceil {f : ℕ → ℝ}
    (hf : PolynomialVertexBound (fun n => ENNReal.ofReal (f n))) :
    PolynomialVertexBound (fun n => (⌈f n⌉₊ : ℝ≥0∞)) := by
  have h1 : PolynomialVertexBound (fun _ => (1:ℝ≥0∞)) := by
    simpa using PolynomialVertexBound.constant 1 (by norm_num)
  apply (hf.add h1).mono
  intro n hn
  by_cases h0 : 0 ≤ f n
  · have h := ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one h0).le
    rw [ENNReal.ofReal_add h0 (by norm_num : (0:ℝ)≤1)] at h
    simpa using h
  · simp [Nat.ceil_eq_zero.mpr (le_of_not_ge h0)]

lemma real_vertex_polynomial : PolynomialVertexBound (fun n => ENNReal.ofReal (n:ℝ)) :=
  vertex_count_polynomial.mono (fun n _ => by simp)

lemma PolynomialRuntimeBound.cc {f : ℕ → Parameters → ℝ≥0∞}
    (hf : PolynomialRuntimeBound f) {γ ε : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1/4) (hε : 0 < ε) :
    PolynomialVertexBound (fun n => f n (ccParameters n γ ε)) := by
  obtain ⟨B, hB, hb⟩ := cc_runtimeScale_bound hγ hε
  exact hf.specialize _ (fun _ hn => ccParameters_valid hn hγ hγ₁ hε) hB hb

/-- The solver cost is polynomial in the logarithm of the precision index. -/
lemma configuredLSW_cost_polynomial (F : CuttingPlaneFamily)
    (N : ℕ → Parameters → ℕ) (lam B : ℕ → Parameters → ℝ)
    (hN : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (Real.log (N n p))))
    (hl : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (lam n p)))
    (hB : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (B n p)))
    (hN2 : ∀ n, 2 ≤ n → ∀ p, p.Valid → 2 ≤ N n p)
    (hl0 : ∀ n, 2 ≤ n → ∀ p, p.Valid → 0 ≤ lam n p)
    (hB0 : ∀ n, 2 ≤ n → ∀ p, p.Valid → 0 ≤ B n p) :
    PolynomialRuntimeBound (fun n p => ConfiguredLSW.cost F n (N n p) (lam n p) (B n p)) := by
  have hc (a : ℝ) (ha : 0<a) := PolynomialRuntimeBound.constant a ha
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using hc 1 (by norm_num)
  have hn2 := polynomial_real_vertices.real_pow 2 (fun n _ _ _ => Nat.cast_nonneg n)
  have hcharge : PolynomialRuntimeBound (fun n _ => ENNReal.ofReal (SDPCoordinates.oracleCharge n:ℝ)) := by
    simpa using polynomial_sdp_oracleCharge
  have hs : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (ConfiguredLSW.scale n (N n p) (lam n p) (B n p))) :=
    ((((((hc 20 (by norm_num)).real_add hn2).real_add hcharge).real_add
      ((hc 12 (by norm_num)).real_mul polynomial_real_vertices (by intros; norm_num))).real_add
      ((hc 2 (by norm_num)).real_mul hB (by intros; norm_num))).real_add
      (hl.real_mul hn2 hl0)).real_add ((hc 2 (by norm_num)).real_mul hN (by intros; norm_num))
  have hf := ((hc (2*F.coefficient) (by linarith [F.coefficient_pos])).real_mul
    (hs.real_pow F.degree (fun n hn p hp => ConfiguredLSW.scale_nonneg hn (hN2 n hn p hp)
      (hl0 n hn p hp) (hB0 n hn p hp))) (by intros; linarith [F.coefficient_pos])).ceil.add h1
  have hrlog : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (2*Real.log (2*(N n p:ℝ)))) := by
    apply ((hc 4 (by norm_num)).real_add ((hc 2 (by norm_num)).real_mul hN (by intros; norm_num))).of_le
    intro n hn p hp
    apply ENNReal.ofReal_le_ofReal
    have hpos : (0:ℝ) < N n p := by exact_mod_cast (show 0 < N n p by have := hN2 n hn p hp; omega)
    rw [Real.log_mul (by norm_num) hpos.ne']
    have := Real.log_le_self (by norm_num : (0:ℝ)≤2)
    linarith
  have hr : PolynomialRuntimeBound (fun n p => (ConfiguredLSW.repeats (N n p):ℝ≥0∞)) := by
    simpa [ConfiguredLSW.repeats] using hrlog.ceil.add h1
  simpa [ConfiguredLSW.cost, ConfiguredLSW.fuel] using
    (hr.mul (hf.add h1)).add polynomial_sdp_oracleCharge

lemma polynomial_capped_lam : PolynomialRuntimeBound
    (fun n p => ENNReal.ofReal (cappedRunConfig n p).oracle.lam) := by
  refine ⟨(10:ℝ)^28, by positivity, 7, ?_⟩
  intro n hn p hp
  have hL := core_log_bounds hn (le_refl (1:ℝ)) p hp
  have h := (outer_oracle_size_bounds hn (le_refl (1:ℝ)) p hp hL).2
  have hg := (runtimeScale_bounds (n:=n) hp).2.1
  have he := runtimeScale_epsilon (n:=n) hp
  have hLle := main_log_le_runtimeScale hn hp
  have hR : 0 ≤ runtimeScale n p := (by norm_num : (0:ℝ) ≤ 1).trans (runtimeScale_bounds hp).2.2
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (10:ℝ)^28 * logFactor n 1 p ^ 5 / (p.gamma*p.epsilon) := h
    _ = (10:ℝ)^28 * logFactor n 1 p ^ 5 * (1/p.gamma)*(1/p.epsilon) := by ring
    _ ≤ (10:ℝ)^28 * runtimeScale n p ^ 5 * runtimeScale n p * runtimeScale n p :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hL.one_le]) hLle 5) (by positivity)) hg
        (one_div_pos.mpr hp.1).le (by positivity)) he (one_div_pos.mpr hp.2.2.1).le (by positivity)
    _ = _ := by ring

end DPCut
