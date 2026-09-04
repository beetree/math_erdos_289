module

public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.LargeEstimates

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

lemma large_enough_N :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
        (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ (log N) ^ (1 / 500 : ℝ) < 2 * M ∧
        2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        3 * ε * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * (log N) ^ (1 / 500 : ℝ)) ∧
        (log N) ^ (1 / 500 : ℝ) ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
        3 * ε' * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux := large_enough_Naux c hc
  have haux4 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 24 : ℝ) * ‖x ^ (1 / 125 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 125 : ℝ) by norm_num)).bound
      (show 0 < (1 / 24 : ℝ) by norm_num)
  have haux5 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (2 / 3 : ℝ) * ‖x ^ (3 / 500 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (3 / 500 : ℝ) by norm_num)).bound
      (show 0 < (2 / 3 : ℝ) by norm_num)
  have haux6 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 2 : ℝ) * ‖x ^ (1 / 200 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop ((192 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux4
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux5
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux6
    , hlargeaux ] with
    N hN1 hN2 hN3 hN3new hN3new2 hN3new3 hotheraux
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (192 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  have hbound1 :
      log (log N) ≤ (1 / 24 : ℝ) * (log N) ^ (1 / 125 : ℝ) := by
    have habs :
        log (log N) ≤ (1 / 24 : ℝ) * |(log N) ^ (1 / 125 : ℝ)| := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new
    rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 125 : ℝ) by positivity)] at habs
    exact habs
  have hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ) := by
    nlinarith
  have hN10 :
      log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le,
      abs_of_nonneg (show 0 ≤ (log N) ^ (3 / 500 : ℝ) by positivity)] using hN3new2
  have hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ) := by
    have hbound3 :
        log (log N) ≤ (1 / 2 : ℝ) * (log N) ^ (1 / 200 : ℝ) := by
      have habs :
          log (log N) ≤ (1 / 2 : ℝ) * |(log N) ^ (1 / 200 : ℝ)| := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new3
      rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 200 : ℝ) by positivity)] at habs
      exact habs
    nlinarith
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ (1 / 100 : ℝ))
  let T : ℝ := M / log N
  let ε : ℝ := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let P : ℝ := (log N) ^ (1 / 500 : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε'pos : 0 < ε' := by
    dsimp [ε']
    positivity
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hotheraux' :
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M := by
    simpa [M, L, T, ε, ε', K, P] using hotheraux
  have hTp : 192 * P < M := by
    simpa [M, P] using large_enough_N_hTp N hN1 hN2 hN5 hN6 hN7 hN8
  have hT : 4 * P < M := by
    have hstep : 4 * P ≤ 192 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hTp
  have hT' : P < M := by
    have hstep : P ≤ 4 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hT
  have hT1 : 3 * ε' * log (log N) ≤ 2 / P ^ 2 := by
    simpa [ε', P] using large_enough_N_hT1 N hN8 hN10
  have hT2 : 2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
    simpa [ε'] using large_enough_N_hT2 N hN8 hN11
  have hT3 : ε ≤ ε' := by
    simpa [ε, ε'] using large_enough_N_hT3 N hN2 hN6 hN7 hN8 hN10
  have hKlower : 8 ≤ K := by
    simpa [K] using large_enough_N_hKlower N hN1 hN3 hN5 hN6 hN7 hN8
  have hsum :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) := by
    simpa [M, ε', P] using large_enough_N_hsum N hN8 hN9 (by simpa [M, P] using hT)
  have honeOverM : 1 / M < ε' * log (log N) := by
    simpa [M, ε'] using large_enough_N_honeOverM N hN1 hN5 hN8 hN9
  change
    1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
      (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ P < 2 * M ∧
      2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      3 * ε * log (log N) ≤ 2 / P ^ 2 ∧
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) ∧
      P ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
      3 * ε' * log (log N) ≤ 2 / P ^ 2 ∧
      2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
      (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M
  constructor
  · simpa [M, ε] using large_enough_N_hMε N hN1 hN5 hN6 hN7
  constructor
  · exact hεpos
  constructor
  · have hrec : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      exact
        one_div_le_one_div_of_le
          (by norm_num : 0 < (2 : ℝ))
          (by linarith : (2 : ℝ) ≤ log (log N))
    have hexp : (1 : ℝ) ≤ (1 - (1 : ℝ) / log (log N)) * (2 : ℝ) := by
      nlinarith
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (N : ℝ) ^ ((1 - (1 : ℝ) / log (log N)) * (2 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      _ = M ^ (2 : ℝ) := by
        dsimp [M]
        rw [← Real.rpow_mul (le_of_lt hN6)]
  constructor
  · calc
      M = (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by rfl
      _ < (N : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN5
        have hdivpos : 0 < (1 : ℝ) / log (log N) := by positivity
        nlinarith
      _ = N := by rw [Real.rpow_one]
  constructor
  · exact hMpos
  constructor
  · exact hN8
  constructor
  · exact hKlower
  constructor
  · simpa [M, K] using large_enough_N_hKM N hN5 hN7
  constructor
  · have hstep : M ≤ 2 * M := by
      nlinarith [hMpos]
    exact lt_of_lt_of_le hT' hstep
  constructor
  · have hmul1 : 2 * ε ≤ 2 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (2 : ℝ) by norm_num)
    have hmul2 : (2 * ε) * log (log N) ≤ (2 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT2
    simpa [mul_assoc] using hmul2
  constructor
  · have hmul1 : 3 * ε ≤ 3 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (3 : ℝ) by norm_num)
    have hmul2 : (3 * ε) * log (log N) ≤ (3 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT1
    simpa [mul_assoc] using hmul2
  constructor
  · exact hsum
  constructor
  · exact le_of_lt <| (_root_.lt_div_iff₀ (show 0 < (192 : ℝ) by norm_num)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hTp
  constructor
  · exact honeOverM
  constructor
  · exact hT1
  constructor
  · exact hT2
  · exact hotheraux' hT3

lemma technical_prop_hdiv_aux
    (y z : ℝ) (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∣ n)
    (hyd₁ : y ≤ d₁)
    (hd₁₂ : 4 * d₁ ≤ d₂)
    (hd₂z : (d₂ : ℝ) ≤ z) :
    ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
  refine ⟨d₁, hyd₁, ?_, hd₁⟩
  have hd₁₂' : (4 : ℝ) * d₁ ≤ d₂ := by
    exact_mod_cast hd₁₂
  nlinarith

lemma technical_prop_hrecB
    (N : ℕ) (M ε' y z : ℝ) (A' B : Finset ℕ) (d : ℕ)
    (h1y : 1 ≤ y)
    (hz_pos : 0 < z)
    (hzN : z ≤ (log N) ^ (1 / 500 : ℝ))
    (hε'M :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * ((log N) ^ (1 / 500 : ℝ))))
    (hrecB : rec_sum A' ≤ 3 * rec_sum B)
    (hdy : y ≤ d)
    (hdz : (d : ℝ) ≤ z / 4)
    (htechrec : (2 : ℝ) / d - 1 / M ≤ rec_sum A') :
    2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
  have hd_pos : 0 < (d : ℝ) := by
    linarith
  have hdz' : (d : ℝ) ≤ z := by
    nlinarith [hdz, hz_pos]
  have hsmall : 3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * d) := by
    calc
      3 * (2 * ε' * log (log N)) + 1 / M ≤
          1 / (2 * ((log N) ^ (1 / 500 : ℝ))) := hε'M
      _ ≤ 1 / (2 * z) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith [hzN]
      _ ≤ 1 / (2 * d) := by
        apply one_div_le_one_div_of_le
        · nlinarith [hd_pos]
        · nlinarith [hdz']
  have hhalfEq : (1 / (2 * d) : ℝ) = ((1 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
  have hadd :
      (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) = (2 : ℝ) / d := by
    field_simp [hd_pos.ne']
    ring
  have hsmall' :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ ((1 / 2 : ℝ) / d) := by
    rw [← hhalfEq]
    exact hsmall
  have hbound :
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤ (2 : ℝ) / d := by
    calc
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤
          (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hsmall' ((3 / 2 : ℝ) / d)
      _ = (2 : ℝ) / d := hadd
  have hpre :
      (3 / 2 : ℝ) / d + 3 * (2 * ε' * log (log N)) ≤ rec_sum A' := by
    linarith
  have haux : (3 : ℝ) * (2 / ((4 : ℝ) * d)) = ((3 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
    ring
  have hrecB' : (rec_sum A' : ℝ) ≤ 3 * (rec_sum B : ℝ) := by
    exact_mod_cast hrecB
  have hmulA : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ rec_sum A' := by
    rw [mul_add, haux]
    exact hpre
  have hmulB : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ 3 * rec_sum B := by
    exact le_trans hmulA hrecB'
  exact le_of_mul_le_mul_left hmulB (show 0 < (3 : ℝ) by norm_num)

set_option maxHeartbeats 1000000 in
-- The translated Lean 4 proof is long enough that it needs more heartbeats to elaborate.
theorem technical_prop :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ y z : ℝ,
      1 ≤ y → 4 * y + 4 ≤ z → z ≤ (log N) ^ (1 / 500 : ℝ) → 0 ∉ A →
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) →
      2 / y + (log N) ^ (-(1 / 200 : ℝ)) ≤ rec_sum A →
      (∀ n ∈ A, ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
  obtain ⟨c, hc, circle_method⟩ := circle_method_prop2
  obtain hlargeN := large_enough_N
  specialize hlargeN c hc
  filter_upwards
    [ main_tech_lemma
    , force_good_properties
    , force_good_properties2
    , circle_method
    , hlargeN ] with
    N htechlemma hforce1 hforce2 hcircle hlargeN
  clear circle_method
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ ((1 : ℝ) / 100))
  let T : ℝ := M / log N
  rcases hlargeN with
    ⟨hMε, hε, hM3, hM2, hM1, hlogN3, heK, hKM, hlogN4, hlogN5, hlogN6, hlargeNnew,
      hlargenew2, hε'M, hlarge3, hlarge4, hεε'M, hUhelper, hUhelper2, hUhelper3, hlarge7⟩
  have hNMcast : (N : ℝ) ≤ M ^ 2 := by
    rw [← Real.rpow_natCast]
    exact hM3
  have hM2aux : M ≤ N := by
    exact le_of_lt hM2
  intro A hA y z h1y hyz hzN h0A hA2 hrec hdiv hsmooth hreg
  have htemp6 :
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) = K := by
    have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hM1 hM2aux
    rw [← Real.rpow_add hNpos]
    have hEq :
        1 - (1 : ℝ) / log (log N) + (-(2 : ℝ) / log (log N)) =
          1 - (3 : ℝ) / log (log N) := by
      ring_nf
    rw [hEq]
  have hzT : 0 < T := by
    exact div_pos hM1 hlogN3
  have hzL : 0 < L := by
    apply div_pos hM1
    apply mul_pos
    · exact zero_lt_two
    · exact Real.rpow_pos_of_pos hlogN3 _
  have hyzaux : y ≤ z := by
    apply le_trans (b := 4 * y)
    · exact le_mul_of_one_le_left (le_trans zero_le_one h1y) (by norm_num : (1 : ℝ) ≤ 4)
    · apply le_trans (b := 4 * y + 4)
      · exact le_add_of_nonneg_right (show 0 ≤ (4 : ℝ) by norm_num)
      · exact hyz
  have hz_pos : 0 < z := by
    exact lt_of_lt_of_le zero_lt_one (le_trans h1y hyzaux)
  have hwM : z / 4 < 2 * M := by
    apply lt_of_lt_of_le (b := z)
    · rw [div_lt_iff₀ zero_lt_four]
      exact lt_mul_of_one_lt_right hz_pos one_lt_four
    · exact le_trans hzN (le_of_lt hlogN4)
  have h8z : 8 ≤ z := by
    apply le_trans (b := 4 * y + 4)
    · have h4y : 4 ≤ 4 * y := by
        exact le_mul_of_one_le_right (show 0 ≤ (4 : ℝ) by norm_num) h1y
      linarith
    · exact hyz
  have h2z : 2 ≤ z / 4 := by
    rw [le_div_iff₀ zero_lt_four]
    norm_num1
    exact h8z
  have hyz' : ⌈y⌉₊ ≤ ⌊z / 4⌋₊ := by
    rw [Nat.ceil_le]
    apply le_trans (b := z / 4 - 1)
    · apply le_sub_right_of_add_le
      rw [le_div_iff₀ zero_lt_four, add_mul, one_mul, mul_comm]
      exact hyz
    · rw [sub_le_iff_le_add]
      refine le_trans le_rfl ?_
      have hfloor : z / 4 < (⌊z / 4⌋₊ : ℝ) + 1 := by
        exact Nat.lt_floor_add_one (z / 4)
      exact le_of_lt hfloor
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  have h0ε' : 0 < ε' := by
    exact Real.rpow_pos_of_pos hlogN3 _
  have hε'w2 : 3 * ε' * log (log N) ≤ 2 / (z ^ 2) := by
    have hsq : z ^ 2 ≤ ((log N) ^ ((1 / 500 : ℝ))) ^ 2 := by
      nlinarith [hzN, hz_pos, show 0 ≤ (log N) ^ ((1 / 500 : ℝ)) by positivity]
    have hInv : 1 / (((log N) ^ ((1 / 500 : ℝ))) ^ 2) ≤ 1 / (z ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hz_pos) hsq
    refine hlarge3.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hε'z : 3 * ε' * log (log N) ≤ 2 / ((z / 4) ^ 2) := by
    have hεzaux : (z / 4) ^ 2 ≤ z ^ 2 := by
      nlinarith [hz_pos]
    have hInv : 1 / (z ^ 2) ≤ 1 / ((z / 4) ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hz_pos zero_lt_four)) hεzaux
    refine hε'w2.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hrec' : 2 / y + 2 * ε' * log (log N) ≤ rec_sum A := by
    apply le_trans ?_ hrec
    exact add_le_add le_rfl hlarge4
  have hsmooth' : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε' * M := by
    intro q hq
    rw [ppowers_in_set, Finset.mem_biUnion] at hq
    rcases hq with ⟨a, ha, hq⟩
    rw [Finset.mem_filter] at hq
    simp_rw [is_smooth] at hsmooth
    specialize hsmooth a ha q hq.2.1
    apply le_trans _ hεε'M
    exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
  have hdiv' : ∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
    intro n hn
    specialize hdiv n hn
    rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
    exact technical_prop_hdiv_aux y z n d₁ d₂ hd₁ hyd₁ hd₁₂ hd₂z
  have htech2 := htechlemma
  specialize htechlemma M ε' y (z / 4) A hA hM1 hM2 h0ε' hwM hε'M h1y h2z hyz' hε'z hA2 hrec'
    hsmooth' hdiv'
  rcases htechlemma with ⟨A', hA', d, htech⟩
  have hzd : d ≠ 0 := by
    have hd1 : 1 ≤ d := by
      exact_mod_cast le_trans h1y htech.2.1
    exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
  by_cases
    hgoodsubset :
      ∃ B ⊆ A',
        rec_sum A' ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)
  · clear hforce1
    rcases hgoodsubset with ⟨B, hB, hrecB, hppB⟩
    have hB2 : B ⊆ Finset.range (N + 1) := by
      exact (hB.trans hA').trans hA
    have hzM : z < 2 * M := by
      exact lt_of_le_of_lt hzN hlogN4
    have h14d : 1 ≤ (4 : ℝ) * d := by
      have hd1 : (1 : ℝ) ≤ d := by
        exact le_trans h1y htech.2.1
      nlinarith
    have h2z' : 2 ≤ z := by
      exact le_trans (by norm_num1 : (2 : ℝ) ≤ 8) h8z
    have hdz : ⌈(4 : ℝ) * d⌉₊ ≤ ⌊z⌋₊ := by
      have h4dz : (4 : ℝ) * d ≤ z := by
        nlinarith [htech.2.2.1]
      have h4dz_nat : 4 * d ≤ ⌊z⌋₊ := by
        exact (Nat.le_floor_iff (le_of_lt hz_pos)).mpr <| by
          simpa [Nat.cast_mul] using h4dz
      rw [show ((4 : ℝ) * d) = ((4 * d : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
      exact h4dz_nat
    have hB3 : ∀ n : ℕ, n ∈ B → M ≤ n := by
      intro n hn
      exact hA2 n ((hB.trans hA') hn)
    have hrecB' : 2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
      exact technical_prop_hrecB N M ε' y z A' B d h1y hz_pos hzN hlargeNnew hrecB htech.2.1
        htech.2.2.1 htech.2.2.2.2.1
    have hsmoothB : ∀ q ∈ ppowers_in_set B, (q : ℝ) ≤ ε' * M := by
      intro q hq
      exact hsmooth' q ((ppowers_in_set_subset ((hB.trans hA'))) hq)
    have hdivB :
        ∀ n : ℕ, n ∈ B → ∃ d₁ : ℕ, (4 : ℝ) * d ≤ d₁ ∧ (d₁ : ℝ) ≤ z ∧ d₁ ∣ n := by
      intro n hn
      specialize hdiv n ((hB.trans hA') hn)
      rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
      have hdle : d ≤ d₁ := by
        obtain htech' := htech.2.2.2.2.2.2.2
        specialize htech' n (hB hn) d₁ hd₁
        apply le_of_not_gt
        intro hfoo
        specialize htech' hfoo
        exact (not_le.mpr htech') hyd₁
      refine ⟨d₂, ?_, hd₂z, hd₂⟩
      norm_cast
      apply le_trans (b := 4 * d₁)
      · have hdle' : (d : ℝ) ≤ d₁ := by
          exact_mod_cast hdle
        nlinarith
      · exact hd₁₂
    specialize htech2 M ε' ((4 : ℝ) * d) z B hB2 hM1 hM2 h0ε' hzM hε'M h14d h2z' hdz hε'w2 hB3
      hrecB' hsmoothB hdivB
    rcases htech2 with ⟨B', hB', d', htech2⟩
    have hB'2 : B' ⊆ Finset.range (N + 1) := by
      exact hB'.trans hB2
    have hB'reg : arith_regular N B' := by
      exact hreg.subset (hB'.trans (hB.trans hA'))
    have hB'3 : ∀ q ∈ ppowers_in_set B', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local B' q := by
      obtain htech2' := htech2.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech2' q hq)
    have hB'4 : (ppower_rec_sum B' : ℝ) ≤ (2 / 3) * log (log N) := by
      apply le_trans _ hppB
      norm_cast
      exact ppower_rec_sum_mono hB'
    have hB'5 : ∀ n : ℕ, n ∈ B' → M ≤ n := by
      intro n hn
      exact hA2 n ((hA' <| hB <| hB' hn))
    have hB'n0 : 0 ∉ B' := by
      intro hz
      exact h0A (hA' (hB (hB' hz)))
    specialize hforce2 M B' hB'2 hM1 (le_of_lt hM2) hNMcast hB'n0 hB'5 hB'reg hB'3 hB'4
    have hzd' : d' ≠ 0 := by
      have hd1 : 1 ≤ d' := by
        exact_mod_cast le_trans h14d htech2.2.1
      exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
    have hd'M : (d' : ℝ) ≤ M / 192 := by
      exact le_trans htech2.2.2.1 (le_trans hzN hlargenew2)
    have hB'6 : ∀ n : ℕ, n ∈ B' → n ≤ N := by
      intro n hn
      rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
      exact hB'2 hn
    have hdB' : d' ∣ B'.lcm id := by
      rcases htech2.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
      exact dvd_trans hnew (Finset.dvd_lcm hn)
    let U' :=
      min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d') (T * K ^ 2 / (N ^ 2 * log N)))
    have hU'M : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U' := by
      rw [le_min_iff]
      constructor
      · exact hUhelper
      · rw [le_min_iff]
        constructor
        · apply le_trans (b := c * M / z)
          · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
            · exact hUhelper3
            · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                exact one_div_le_one_div_of_le hz_pos hzN
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · have hd'pos : 0 < (d' : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero hzd'
            have hInv : 1 / z ≤ 1 / d' := by
              exact one_div_le_one_div_of_le hd'pos htech2.2.2.1
            simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
              (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
        · exact hUhelper2
    have hppB' : ∀ q : ℕ, q ∈ ppowers_in_set B' → (q : ℝ) ≤ U' := by
      intro q hq
      rw [ppowers_in_set, Finset.mem_biUnion] at hq
      rcases hq with ⟨a, ha, hq⟩
      rw [Finset.mem_filter] at hq
      simp_rw [is_smooth] at hsmooth
      specialize hsmooth a (hA' (hB (hB' ha))) q hq.2.1
      apply le_trans _ hU'M
      exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
    have hgoodB' : good_condition B' K T L := by
      rw [htemp6] at hforce2
      exact hforce2
    specialize
      @hcircle K L M T d' B' hzT hzL heK hKM hM2aux hzd' hd'M hB'5 hB'6 htech2.2.2.2.1
        htech2.2.2.2.2.1 hdB' hppB' hgoodB'
    rcases hcircle with ⟨S, hS, hcirc⟩
    refine ⟨S, hS.trans (hB'.trans (hB.trans hA')), d', ?_, htech2.2.2.1, hcirc⟩
    apply le_trans htech.2.1
    apply le_trans (b := (4 : ℝ) * d)
    · exact le_mul_of_one_le_left (Nat.cast_nonneg d) (by norm_num : (1 : ℝ) ≤ 4)
    · exact htech2.2.1
  · clear hforce2 htech2
    have hrangeA' : A' ⊆ Finset.range (N + 1) := by
      exact hA'.trans hA
    have hregA' : arith_regular N A' := by
      exact hreg.subset hA'
    have hNA' : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A' := by
      have hdP : (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) / 4 := by
        nlinarith [htech.2.2.1, hzN]
      have htwoDiv : (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 2 / d := by
        have hdpos : 0 < (d : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hzd
        have hInv : 1 / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 1 / d := by
          exact one_div_le_one_div_of_le hdpos hdP
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
      exact hlarge7.trans <| (sub_le_sub_right htwoDiv _).trans htech.2.2.2.2.1
    have hppA' : ∀ q ∈ ppowers_in_set A', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A' q := by
      obtain htech' := htech.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech' q hq)
    have hA'5 : ∀ n : ℕ, n ∈ A' → M ≤ n := by
      intro n hn
      exact hA2 n (hA' hn)
    have hA'n0 : 0 ∉ A' := by
      intro hz
      exact h0A (hA' hz)
    specialize hforce1 M A' hrangeA' hM1 (le_of_lt hM2) hNMcast hA'n0 hA'5 hregA' hNA' hppA'
    rcases hforce1 with htemp1 | htemp2
    · exfalso
      exact hgoodsubset htemp1
    · have hgoodA' : good_condition A' K T L := by
        rw [htemp6] at htemp2
        exact htemp2
      have hdM : (d : ℝ) ≤ M / 192 := by
        apply le_trans htech.2.2.1
        apply le_trans (b := z / 4)
        · exact le_rfl
        · apply le_trans ?_ (le_trans hzN hlargenew2)
          exact div_le_self (le_of_lt hz_pos) (by norm_num : (1 : ℝ) ≤ 4)
      have hA'6 : ∀ n : ℕ, n ∈ A' → n ≤ N := by
        intro n hn
        rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
        exact hrangeA' hn
      have hdA' : d ∣ A'.lcm id := by
        rcases htech.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
        exact dvd_trans hnew (Finset.dvd_lcm hn)
      let U :=
        min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d) (T * K ^ 2 / (N ^ 2 * log N)))
      have hUM : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U := by
        rw [le_min_iff]
        constructor
        · exact hUhelper
        · rw [le_min_iff]
          constructor
          · apply le_trans (b := c * M / z)
            · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
              · exact hUhelper3
              · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                  exact one_div_le_one_div_of_le hz_pos hzN
                simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                  (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
            · have hdpos : 0 < (d : ℝ) := by
                exact_mod_cast Nat.pos_of_ne_zero hzd
              have hdz' : (d : ℝ) ≤ z := by
                have : (d : ℝ) ≤ z / 4 := htech.2.2.1
                nlinarith
              have hInv : 1 / z ≤ 1 / d := by
                exact one_div_le_one_div_of_le hdpos hdz'
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · exact hUhelper2
      have hppA' : ∀ q : ℕ, q ∈ ppowers_in_set A' → (q : ℝ) ≤ U := by
        intro q hq
        rw [ppowers_in_set, Finset.mem_biUnion] at hq
        rcases hq with ⟨a, ha, hq⟩
        rw [Finset.mem_filter] at hq
        simp_rw [is_smooth] at hsmooth
        specialize hsmooth a (hA' ha) q hq.2.1
        apply le_trans _ hUM
        exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
      specialize
        @hcircle K L M T d A' hzT hzL heK hKM hM2aux hzd hdM hA'5 hA'6 htech.2.2.2.1
          htech.2.2.2.2.1 hdA' hppA' hgoodA'
      rcases hcircle with ⟨S, hS, hcirc⟩
      refine ⟨S, hS.trans hA', d, htech.2.1, ?_, hcirc⟩
      apply le_trans htech.2.2.1
      apply div_le_self
      · exact le_trans zero_le_one (le_trans h1y hyzaux)
      · norm_num

end UnitFractions
