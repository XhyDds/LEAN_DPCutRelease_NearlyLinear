import DPCut.CostedProgramBounds

/-! Public iteration and batch-size bounds for the oracle-relative runtime theorem. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

lemma runtimeScale_bounds {n : ℕ} {p : Parameters} (hp : p.Valid) :
    1 + (n : ℝ) ≤ runtimeScale n p ∧ 1 / p.gamma ≤ runtimeScale n p ∧
      1 ≤ runtimeScale n p := by
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  have hld : 0 ≤ Real.log (1 / p.delta) := Real.log_nonneg ((one_le_div hd).mpr (by linarith))
  have hlb : 0 ≤ Real.log (1 / p.beta) := Real.log_nonneg ((one_le_div hb).mpr (by linarith))
  have hig := (one_div_pos.mpr hg).le
  have hie := (one_div_pos.mpr he).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [runtimeScale]
  constructor
  · linarith
  constructor <;> linarith

lemma main_log_le_runtimeScale {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    logFactor n 1 p ≤ runtimeScale n p := by
  rw [main_log_expansion hn hp]
  have hln := Real.log_le_self (Nat.cast_nonneg n)
  have hlg := Real.log_le_self (one_div_nonneg.mpr hp.1.le)
  have hle := Real.log_le_self (one_div_nonneg.mpr hp.2.2.1.le)
  simp only [one_div, Real.log_inv] at hlg hle
  simp only [runtimeScale, one_div, Real.log_inv]
  linarith

lemma oracle_sample_sizes_bound {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    let c := runConfig n U p outerUtilityConstants
    (c.oracle.K : ℝ) ≤ 2000000 * L ∧ (c.oracle.k : ℝ) ≤ 10000000000 * L := by
  let c := runConfig n U p outerUtilityConstants
  have hb := outer_budget_bounds hn hU p hp hL
  have ho := (outerConfig_inner_utility_bounds hn hU p hp).oracle_privacy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < L := by linarith [hL.one_le]
  have hlogb : -Real.log c.betaGE ≤ 190 * L := by simpa [one_div, Real.log_inv] using hb.log_betaGE
  have hlogd : -Real.log c.deltaGE ≤ 190 * L := by simpa [one_div, Real.log_inv] using hb.log_deltaGE
  have hlogn : Real.log (n / c.betaGE) ≤ 191 * L := by
    rw [Real.log_div hn0.ne' hb.betaGE_pos.ne']
    linarith [hL.log_n]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 : 0 < Real.log (n / c.betaGE) :=
    Real.log_pos ((one_lt_div hb.betaGE_pos).mpr (by linarith [hb.betaGE_lt_one]))
  have hK : 0 < c.oracle.K := Nat.ceil_pos.mpr (by change 0 < 8192 * Real.log (n / c.betaGE); positivity)
  have hKR : (0 : ℝ) < c.oracle.K := by exact_mod_cast hK
  have hKb : (c.oracle.K : ℝ) ≤ 2000000 * L := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 8192 * Real.log (n / c.betaGE) by positivity)
    change (⌈8192 * Real.log (n / c.betaGE)⌉₊ : ℝ) ≤ _
    linarith [hL.one_le]
  have hlogK : Real.log c.oracle.K ≤ 2000001 * L := by
    convert log_le_from_bound hKR (by norm_num : (0 : ℝ) < 2000000) hL.one_le hKb using 1
    norm_num
  have hlogSmall {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 20) (hb0 : 0 < b)
      (hlogb : -Real.log b ≤ 190 * L) :
      Real.log (1 / (b / (a * (n : ℝ) ^ 2 * c.oracle.K))) ≤ 3000000 * L := by
    rw [one_div, Real.log_inv, Real.log_div hb0.ne' (by positivity),
      Real.log_mul (by positivity) hKR.ne', Real.log_mul ha.ne' (pow_ne_zero _ hn0.ne'),
      Real.log_pow]
    have hla := (Real.log_le_self ha.le).trans ha1
    norm_num
    linarith [hL.log_n, hL.one_le]
  have hβ1 : Real.log (1 / c.oracle.beta1) ≤ 3000000 * L :=
    hlogSmall (by norm_num) (by norm_num) hb.betaGE_pos hlogb
  have hδ1 : Real.log (1 / c.oracle.delta1) ≤ 3000000 * L :=
    hlogSmall (by norm_num) (by norm_num) hb.deltaGE_pos hlogd
  have hβpos : 0 < c.oracle.beta1 := ho.beta_pos
  have hδpos : 0 < c.oracle.delta1 := ho.delta_pos
  have hlogbatch : Real.log (n / (c.oracle.beta1 * c.oracle.delta1)) ≤ 6000001 * L := by
    rw [Real.log_div hn0.ne' (mul_pos hβpos hδpos).ne', Real.log_mul hβpos.ne' hδpos.ne']
    simp only [one_div, Real.log_inv] at hβ1 hδ1
    linarith [hL.log_n]
  have hlogbatch0 : 0 ≤ Real.log (n / (c.oracle.beta1 * c.oracle.delta1)) := by
    apply Real.log_nonneg
    apply (one_le_div (mul_pos hβpos hδpos)).mpr
    have hβsmall : c.oracle.beta1 < 1 := ho.beta_lt_one
    have hδsmall : c.oracle.delta1 < 1 / 2 := ho.delta_lt_half
    nlinarith
  refine ⟨hKb, ?_⟩
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 512 * Real.log (n / (c.oracle.beta1 * c.oracle.delta1)) by positivity)
  change (⌈512 * Real.log (n / (c.oracle.beta1 * c.oracle.delta1))⌉₊ : ℝ) ≤ _
  linarith [hL.one_le]

def fullRunConfig (n : ℕ) (p : Parameters) : RunConfig :=
  runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants

theorem full_runtime_parameter_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    let R := runtimeScale n p
    let c := fullRunConfig n p
    (c.T1 : ℝ) ≤ 5184 * R ∧ (c.T2 : ℝ) ≤ 26112 * R ^ 3 ∧
      (c.oracle.K : ℝ) ≤ 128000000 * R ∧ (c.oracle.k : ℝ) ≤ 640000000000 * R := by
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  let L := logFactor n U q
  let R := runtimeScale n p
  have hU : 1 ≤ U := preprocessingThreshold_one_le hn hp
  have hq : q.Valid := boundedParameters_valid hp
  have hL := core_log_bounds hn hU q hq
  have hLR : L ≤ 64 * R := (full_release_log_bound hn hp).trans
    (mul_le_mul_of_nonneg_left (main_log_le_runtimeScale hn hp) (by norm_num))
  obtain ⟨hT1, hT2⟩ := outer_horizons_bound hn hU q hq hL
  obtain ⟨hK, hk⟩ := oracle_sample_sizes_bound hn hU q hq hL
  change ((fullRunConfig n p).T1 : ℝ) ≤ _ at hT1
  change ((fullRunConfig n p).T2 : ℝ) ≤ _ at hT2
  change ((fullRunConfig n p).oracle.K : ℝ) ≤ _ at hK
  change ((fullRunConfig n p).oracle.k : ℝ) ≤ _ at hk
  dsimp only
  refine ⟨by linarith, ?_, by linarith, by linarith⟩
  have hg := hp.1
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans (runtimeScale_bounds hp).2.2
  have hgi : 1 / p.gamma ≤ R := (runtimeScale_bounds hp).2.1
  calc
    _ ≤ 102 * L / (p.gamma / 2) ^ 2 := hT2
    _ = 408 * L * (1 / p.gamma) ^ 2 := by ring
    _ ≤ 408 * (64 * R) * R ^ 2 :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hgi 2) (sq_nonneg _) (by positivity)
    _ = _ := by ring

end DPCut
