import DPCut.LSWSolverFamily

/-! Uniform polynomial majorants for objective magnitudes, logarithmic accuracy,
LSW timeouts, and independent restart counts. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

lemma PolynomialRuntimeBound.real_add {f g : ℕ → Parameters → ℝ}
    (hf : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p)))
    (hg : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (g n p))) :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p + g n p)) :=
  (hf.add hg).of_le (fun _ _ _ _ => ENNReal.ofReal_add_le)

lemma PolynomialRuntimeBound.real_mul {f g : ℕ → Parameters → ℝ}
    (hf : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p)))
    (hg : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (g n p)))
    (h0 : ∀ n, 2 ≤ n → ∀ p, p.Valid → 0 ≤ f n p) :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p * g n p)) :=
  (hf.mul hg).of_le (fun n hn p hp => le_of_eq (ENNReal.ofReal_mul (h0 n hn p hp)))

lemma PolynomialRuntimeBound.real_pow {f : ℕ → Parameters → ℝ}
    (hf : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p))) (k : ℕ)
    (h0 : ∀ n, 2 ≤ n → ∀ p, p.Valid → 0 ≤ f n p) :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p ^ k)) :=
  (hf.pow k).of_le (fun n hn p hp => le_of_eq (ENNReal.ofReal_pow (h0 n hn p hp) k))

lemma PolynomialRuntimeBound.ceil {f : ℕ → Parameters → ℝ}
    (hf : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (f n p))) :
    PolynomialRuntimeBound (fun n p => (⌈f n p⌉₊ : ℝ≥0∞)) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  apply (hf.add h1).of_le
  intro n hn p hp
  by_cases h0 : 0 ≤ f n p
  · have h := ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one h0).le
    rw [ENNReal.ofReal_add h0 (by norm_num : (0:ℝ)≤1)] at h
    simpa using h
  · simp [Nat.ceil_eq_zero.mpr (le_of_not_ge h0)]

lemma polynomial_real_vertices : PolynomialRuntimeBound (fun n _ => ENNReal.ofReal (n:ℝ)) :=
  polynomial_vertices.of_le (fun _ _ _ _ => by simp)

lemma polynomial_sdp_lam : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (fullRunConfig n p).oracle.lam) :=
  ⟨10^40, by positivity, 7, fun n hn p hp => ENNReal.ofReal_le_ofReal (full_sdp_magnitude_bounds hn hp).1⟩

lemma polynomial_publicObjectiveBound : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (publicObjectiveBound n p)) :=
  ⟨10^10, by positivity, 5, fun n hn p hp => ENNReal.ofReal_le_ofReal (full_sdp_magnitude_bounds hn hp).2⟩

lemma polynomial_sdp_oracleCharge : PolynomialRuntimeBound (fun n _ => (SDPCoordinates.oracleCharge n : ℝ≥0∞)) := by
  have h := ((PolynomialRuntimeBound.constant 1000 (by norm_num)).mul (polynomial_vertices.pow 6)).add
    ((PolynomialRuntimeBound.constant 200 (by norm_num)).mul (polynomial_vertices.pow 3))
  simpa [SDPCoordinates.oracleCharge, linearAlgebraPrimitiveCost, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ← mul_assoc] using h

lemma solverScale_nonneg {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) : 0 ≤ solverScale n p := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hB := publicObjectiveBound_nonneg hn (precisionParameters_valid hp)
  have hl : 0 ≤ (fullRunConfig n (precisionParameters p)).oracle.lam := by linarith [(approxConfig_bounds hn hp).lam_lower]
  have he := solverAccuracy_bounds hn hp
  have hrange : 1 ≤ 1 + 2*publicObjectiveBound n (precisionParameters p) +
      (fullRunConfig n (precisionParameters p)).oracle.lam * (n:ℝ)^2 := by nlinarith [mul_nonneg hl (sq_nonneg (n:ℝ))]
  have hlog := Real.log_nonneg ((one_le_div he.1).mpr (he.2.trans (by linarith : (1/2:ℝ) ≤
    1 + 2*publicObjectiveBound n (precisionParameters p) + (fullRunConfig n (precisionParameters p)).oracle.lam * (n:ℝ)^2)))
  have hg := Real.log_nonneg (show (1:ℝ) ≤ 8*n by linarith)
  unfold solverScale sdpLSWScale
  positivity

lemma solverScale_upper {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    solverScale n p ≤ 20 + (n:ℝ)^2 + SDPCoordinates.oracleCharge n + 12*n +
      2*publicObjectiveBound n (precisionParameters p) +
      (fullRunConfig n (precisionParameters p)).oracle.lam * (n:ℝ)^2 +
      2 * (1+n+|Real.log (approximationRadius n p)|) := by
  let B := publicObjectiveBound n (precisionParameters p)
  let lam := (fullRunConfig n (precisionParameters p)).oracle.lam
  let r := approximationRadius n p
  let T := 1+2*B+lam*(n:ℝ)^2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hr : 0<r := (approximationRadius_bounds (n:=n) hp).1
  have hB : 0 ≤ B := publicObjectiveBound_nonneg hn (precisionParameters_valid hp)
  have hl : 0 ≤ lam := by linarith [(approxConfig_bounds hn hp).lam_lower]
  have hT : 0<T := by dsimp [T]; positivity
  have hε : solverAccuracy n p ≠ 0 := (solverAccuracy_bounds hn hp).1.ne'
  have heq : Real.log (T / solverAccuracy n p) =
      Real.log T - 2*Real.log r + Real.log 8 + 4*Real.log n := by
    rw [Real.log_div hT.ne' hε]
    unfold solverAccuracy
    rw [Real.log_div (pow_ne_zero _ hr.ne') (by positivity), Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow, Real.log_pow]
    dsimp [r]
    ring
  have hg := Real.log_le_self (show (0:ℝ)≤8*n by positivity)
  have ht := Real.log_le_self hT.le
  have hnlog := Real.log_le_self hn0.le
  have h8 := Real.log_le_self (by norm_num : (0:ℝ)≤8)
  have hab := neg_le_abs (Real.log r)
  change 1+(n:ℝ)*n+SDPCoordinates.oracleCharge n+Real.log (8*n)+Real.log (T / solverAccuracy n p) ≤ _
  rw [heq]
  dsimp [T, B, lam, r] at ht hab ⊢
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma polynomial_solverScale : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (solverScale n p)) := by
  have hn2 := polynomial_real_vertices.real_pow 2 (fun n _ _ _ => Nat.cast_nonneg n)
  have hcharge : PolynomialRuntimeBound (fun n _ => ENNReal.ofReal (SDPCoordinates.oracleCharge n : ℝ)) := by
    simpa using polynomial_sdp_oracleCharge
  have h12n := (PolynomialRuntimeBound.constant 12 (by norm_num)).real_mul polynomial_real_vertices (by intros; norm_num)
  have h2B := (PolynomialRuntimeBound.constant 2 (by norm_num)).real_mul polynomial_publicObjectiveBound.precision (by intros; norm_num)
  have hlamn := polynomial_sdp_lam.precision.real_mul hn2
    (fun n hn p hp => by linarith [(approxConfig_bounds hn hp).lam_lower])
  have h2r := (PolynomialRuntimeBound.constant 2 (by norm_num)).real_mul polynomial_approximationScale (by intros; norm_num)
  exact ((((((PolynomialRuntimeBound.constant 20 (by norm_num)).real_add hn2).real_add hcharge).real_add h12n).real_add h2B).real_add hlamn).real_add h2r |>.of_le
    (fun n hn p hp => ENNReal.ofReal_le_ofReal (solverScale_upper hn hp))

lemma polynomial_solverRestarts : PolynomialRuntimeBound (fun n p => (solverRestarts n p : ℝ≥0∞)) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have hmajor := (PolynomialRuntimeBound.constant 4 (by norm_num)).real_add
    ((PolynomialRuntimeBound.constant 2 (by norm_num)).real_mul polynomial_approximationScale (by intros; norm_num))
  have hlog : PolynomialRuntimeBound (fun n p => ENNReal.ofReal (2*Real.log (2/approximationRadius n p))) := by
    apply hmajor.of_le
    intro n hn p hp
    apply ENNReal.ofReal_le_ofReal
    have hr := (approximationRadius_bounds (n:=n) hp).1
    rw [Real.log_div (by norm_num) hr.ne']
    have h2 := Real.log_le_self (by norm_num : (0:ℝ)≤2)
    have ha := neg_le_abs (Real.log (approximationRadius n p))
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  simpa [solverRestarts] using hlog.ceil.add h1

lemma polynomial_solverFuel (F : CuttingPlaneFamily) : PolynomialRuntimeBound (fun n p => (solverFuel F n p : ℝ≥0∞)) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have hpow := polynomial_solverScale.real_pow F.degree (fun _ hn _ hp => solverScale_nonneg hn hp)
  have hprod := (PolynomialRuntimeBound.constant (2*F.coefficient) (by linarith [F.coefficient_pos])).real_mul
    hpow (fun _ _ _ _ => by linarith [F.coefficient_pos])
  simpa [solverFuel] using hprod.ceil.add h1

theorem solverCost_polynomial (F : CuttingPlaneFamily) : PolynomialRuntimeBound (solverCost F) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  exact (polynomial_solverRestarts.mul ((polynomial_solverFuel F).add h1)).add polynomial_sdp_oracleCharge

end DPCut
