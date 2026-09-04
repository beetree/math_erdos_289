module

public import SolveMath.Corpus.NumberTheory.UnitFractionAuxiliaryEstimates.DivisorSelection
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

open Classical

noncomputable section

theorem find_good_d_hfinal {C : ℝ} {A : Finset ℕ} {q N k : ℕ}
    {D2 : Finset ℕ} {newLocal : ℕ → Finset ℕ}
    (hC : 0 < C) (hlarge1 : 0 < log N) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))))
    (hbound4 : D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2)) :
    ∃ d ∈ D2,
      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
  have hsumq' : (0 : ℝ) < rec_sum_local A q := by
    refine lt_of_lt_of_le ?_ hsumq
    exact one_div_pos.mpr hlarge1
  have hpos : (0 : ℚ) < rec_sum_local A q / 2 := by
    have : (0 : ℚ) < rec_sum_local A q := by exact_mod_cast hsumq'
    linarith
  obtain ⟨d, hd, hineq⟩ := weighted_ph hpos (fun d _ ↦ by positivity) hbound3
  refine ⟨d, hd, ?_⟩
  have hFnonneg : (0 : ℝ) ≤ (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by positivity
  have hineqR :
      (rec_sum_local A q : ℝ) / 2 ≤
        (D2.sum (fun d ↦ (1 / d : ℚ)) : ℝ) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    have hcast :
        (((rec_sum_local A q : ℚ) / 2 : ℚ) : ℝ) ≤
          ((D2.sum (fun d ↦ (1 / d : ℚ)) *
            (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) : ℚ) : ℝ) := by
      exact_mod_cast hineq
    simpa [Rat.cast_sum] using hcast
  have hL : (0 : ℝ) < log N ^ ((2 : ℝ) / k) := Real.rpow_pos_of_pos hlarge1 _
  have hmul :
      (D2.sum (fun d ↦ (1 / d : ℚ)) : ℝ) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) ≤
        (log N ^ ((2 : ℝ) / k) / (C * 2)) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) :=
    mul_le_mul_of_nonneg_right (by simpa using hbound4) hFnonneg
  have hfinal2 :
      (rec_sum_local A q : ℝ) / 2 ≤
        (log N ^ ((2 : ℝ) / k) / (C * 2)) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) :=
    le_trans hineqR hmul
  have hkey :
      rec_sum_local A q * C ≤
        log N ^ ((2 : ℝ) / k) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    have e :
        (log N ^ ((2 : ℝ) / k) / (C * 2)) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) =
          (log N ^ ((2 : ℝ) / k) * (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n))) / (2 * C) := by
      ring
    rw [e, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < 2 * C)] at hfinal2
    nlinarith [hfinal2]
  rw [div_le_iff₀ hL]
  nlinarith [hkey]

theorem find_good_d :
    ∃ c C : ℝ,
      0 < c ∧
        0 < C ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ M : ℝ,
              ∀ k : ℕ,
                ∀ A ⊆ range (N + 1),
                  0 < M →
                    M ≤ N →
                      1 < k →
                        (k : ℝ) ≤ c * log (log N) →
                          (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                            ∀ q ∈ ppowers_in_set A,
                              1 / log N ≤ rec_sum_local A q →
                                ∃ d : ℕ,
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d ∧
                                    ((ω d : ℝ) < (5 / log k) * log (log N)) ∧
                                      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
                                        ((local_part A q).filter
                                            (fun n ↦ q * d ∣ n ∧
                                              Nat.Coprime (q * d) (n / (q * d)))).sum
                                          (fun n ↦ (q * d / n : ℝ)) := by
  classical
  rcases useful_rec_bound with ⟨C1, hC1, hrec1⟩
  let C2 := max C1 2
  let c : ℝ := (1 / 2) / Real.log C2
  have hc : 0 < c := by
    simp only [c, C2]
    refine div_pos (by norm_num) ?_
    apply Real.log_pos
    exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)
  let C : ℝ := 1 / (C1 * 2)
  have hC : 0 < C := by
    simp only [C]
    rw [one_div_pos]
    exact mul_pos hC1 zero_lt_two
  have hC' : C1 = 1 / (C * 2) := by
    simp only [C]
    have hC10 : C1 ≠ 0 := ne_of_gt hC1
    field_simp [hC10]
  have hC2 : 1 < C2 := by
    dsimp [C2]
    exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards
    [ find_good_d_aux1
    , find_good_d_aux2
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , eventually_gt_atTop (0 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (16 : ℝ)) ] with
    N haux1 haux2 hlarge hlarge' hlarge'' M k A hAN hzM hMN h1k hkN hAreg q hq hsumq
  dsimp at hlarge
  have hlarge1 : 0 < log N := lt_trans zero_lt_one hlarge
  have hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
    exact find_good_d_hlarge2 hlarge1 hlarge''
  let y : ℝ := Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  let u : ℝ := Real.exp (-log N ^ ((1 : ℝ) - 1 / k))
  have h1y : 1 < y := by
    simp only [y]
    rw [Real.one_lt_exp_iff]
    exact Real.rpow_pos_of_pos hlarge1 _
  have hyN : y < N := by
    simpa [y] using find_good_d_hyN (N := N) (k := k) hlarge hlarge' h1k
  have h0k : (0 : ℝ) < k := by exact_mod_cast (lt_trans zero_lt_one h1k)
  let D : Finset ℕ :=
    (range (N + 1)).filter
      (fun d : ℕ ↦
        (∀ r : ℕ,
            IsPrimePow r →
              r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
          M * u < q * d ∧ q * d ≤ N)
  specialize haux2 M k A hAN hzM hMN (le_of_lt h1k) hAreg q hq
  specialize haux1 M u y q A hAN hzM hMN (le_of_lt (Real.exp_pos _))
  let newLocal : ℕ → Finset ℕ := fun d ↦
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hlocal2 : local_part A q ⊆ D.biUnion newLocal := by
    exact find_good_d_hlocal2 (A := A) (q := q) D newLocal rfl haux2
  have hrecbound :
      rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hrecbound (A := A) (q := q) D newLocal rfl hlocal2
  have hDu : ∀ d ∈ D, M * u < q * d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : ∀ d ∈ D, d ≠ 0 := by
    exact find_good_d_hDnotzero hzM (by simpa [u] using Real.exp_pos _) hDu
  set ω0 : ℝ := (5 / log k) * log (log N) with hω0
  let D1 := D.filter (fun d ↦ ω0 ≤ (ω d : ℝ))
  have hrec2 := hrec1
  specialize hrec1 y k N D1 h1y hyN (le_of_lt h1k)
  have haux1D1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d := by
    intro d hd
    exact haux1 d (Finset.mem_of_mem_filter d hd)
  have hrec1bound :
      D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k := by
    apply hrec1
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2 := by
    exact
      find_good_d_hbound1 (C1 := C1) (c := c) (y := y) (ω0 := ω0) (N := N) (q := q) (k := k)
        (A := A) (D1 := D1) (newLocal := newLocal) hC1 (by simp [c, C2]) rfl hkN hlarge1
        hlarge2 h1k h0k hω0 hsumq (by
          intro d hd
          exact (Finset.mem_filter.mp hd).2) haux1D1 hrec1bound
  let D2 := D.filter (fun d ↦ (ω d : ℝ) < ω0)
  specialize hrec2 y 1 N D2 h1y hyN (le_rfl : 1 ≤ 1)
  have hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1 := by
    apply hrec2
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hbound2 (A := A) (q := q) (D := D) (D1 := D1) (D2 := D2)
      (newLocal := newLocal) rfl rfl hrecbound hbound1
  have hD2notzero : ∀ d ∈ D2, d ≠ 0 := by
    intro d hd
    exact hDnotzero d (Finset.mem_of_mem_filter d hd)
  have hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
    exact find_good_d_hbound3 (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hbound2 hD2notzero
  have hbound4 :
      D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
    exact find_good_d_hbound4 (C1 := C1) (C := C) (N := N) (k := k) (y := y) (D2 := D2) hC'
      rfl hlarge1 hrec2bound
  obtain ⟨d, hd, hfinal⟩ :=
    find_good_d_hfinal (C := C) (A := A) (q := q) (N := N) (k := k) (D2 := D2)
      (newLocal := newLocal) hC hlarge1 hsumq hbound3 hbound4
  rcases Finset.mem_filter.mp hd with ⟨hdD, hdω⟩
  rcases Finset.mem_filter.mp hdD with ⟨_hdRange, hdProps⟩
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa [u] using hdProps.2.1
  · simpa [hω0] using hdω
  · simpa [newLocal] using hfinal

theorem find_good_x_h1k {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊)
    (hlarge0 : 0 < log (log (log N))) (_hlarge1 : 0 < log (log N))
    (hlarge4 : 4 * log (log (log N)) ≤ log (log N)) :
    1 < k := by
  have htwo : (2 : ℝ) < (k : ℝ) + 1 := by
    calc
      (2 : ℝ) ≤ (log (log N)) / (2 * log (log (log N))) := by
        rw [_root_.le_div_iff₀ (show 0 < 2 * log (log (log N)) by positivity), ← mul_assoc]
        norm_num
        exact hlarge4
      _ < (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one ((log (log N)) / (2 * log (log (log N))))
      _ = (k : ℝ) + 1 := by rw [hk]
  have htwo_nat : 2 < k + 1 := by
    exact_mod_cast htwo
  exact Nat.lt_of_succ_lt_succ htwo_nat

theorem find_good_x_hkc {N k : ℕ} {c : ℝ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (hc : 0 < c)
    (hlarge5 : 1 / c / 2 ≤ log (log (log N))) (hlarge0 : 0 < log (log (log N)))
    (hlarge1 : 0 < log (log N)) :
    (k : ℝ) ≤ c * log (log N) := by
  calc
    (k : ℝ) = (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) := by rw [hk]
    _ ≤ (log (log N)) / (2 * log (log (log N))) := by
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        positivity)
    _ ≤ c * log (log N) := by
      have haux : 1 / c ≤ 2 * log (log (log N)) := by
        have hmul := mul_le_mul_of_nonneg_left hlarge5 (show (0 : ℝ) ≤ 2 by positivity)
        calc
          1 / c = 2 * (1 / c / 2) := by ring
          _ ≤ 2 * log (log (log N)) := hmul
      have hinv : 1 / (2 * log (log (log N))) ≤ c := by
        exact (one_div_le (show 0 < 2 * log (log (log N)) by positivity) hc).2 haux
      rw [div_eq_mul_one_div, mul_comm c]
      exact mul_le_mul_of_nonneg_left hinv (le_of_lt hlarge1)

theorem find_good_x_hlogNk {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (h1k : 1 < k)
    (hlarge7 : log 2 < log (log (log N))) (hlarge1 : 0 < log (log N))
    (hlarge2 : 0 < log N) (hlarge3 : 1 ≤ log N) :
    2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
  have hlarge0 : 0 < log (log (log N)) := by
    exact lt_trans (Real.log_pos one_lt_two) hlarge7
  let u : ℝ := log (log (log N)) / log (log N)
  have hpowpos : 0 < log N ^ u := by
    exact Real.rpow_pos_of_pos hlarge2 _
  have hmid : (2 : ℝ) < log N ^ u := by
    rw [← Real.log_lt_log_iff zero_lt_two hpowpos, Real.log_rpow hlarge2]
    dsimp [u]
    have hmul :
        log (log (log N)) / log (log N) * log (log N) = log (log (log N)) := by
      field_simp [ne_of_gt hlarge1]
    rw [hmul]
    exact hlarge7
  have hlt2 : 2 * log N ^ u < log N ^ (2 * u) := by
    calc
      2 * log N ^ u < log N ^ u * log N ^ u := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
          mul_lt_mul_of_pos_right hmid hpowpos
      _ = log N ^ (u + u) := by
        rw [← Real.rpow_add hlarge2]
      _ = log N ^ (2 * u) := by ring_nf
  have hexp_le : 2 * log (log (log N)) / log (log N) ≤ (1 : ℝ) / k := by
    rw [le_one_div (show 0 < 2 * log (log (log N)) / log (log N) by
      refine div_pos ?_ hlarge1
      exact mul_pos zero_lt_two hlarge0)]
    · rw [one_div_div]
      rw [hk]
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        exact mul_nonneg zero_le_two (le_of_lt hlarge0))
    · exact_mod_cast (lt_trans zero_lt_one h1k)
  have hu_eq : log N ^ u = log (log N) := by
    calc
      log N ^ u = Real.exp (Real.log (log N) * u) := by
        rw [Real.rpow_def_of_pos hlarge2]
      _ = Real.exp (log (log (log N))) := by
        dsimp [u]
        congr 1
        field_simp [ne_of_gt hlarge1]
      _ = log (log N) := by
        rw [Real.exp_log hlarge1]
  have hu2_eq : 2 * u = 2 * log (log (log N)) / log (log N) := by
    dsimp [u]
    field_simp [ne_of_gt hlarge1]
  calc
    2 * log (log N) = 2 * (log N ^ u) := by rw [hu_eq]
    _ < log N ^ (2 * u) := hlt2
    _ = log N ^ (2 * log (log (log N)) / log (log N)) := by rw [hu2_eq]
    _ ≤ log N ^ ((1 : ℝ) / k) := by
      exact Real.rpow_le_rpow_of_exponent_le hlarge3 hexp_le

theorem find_good_x_hA_I' {N k : ℕ} {M : ℝ} {A : Finset ℕ} {I : Finset ℤ}
    {A_I : Finset ℕ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ)) (hreg : arith_regular N A)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
  intro n hn
  rw [hA_I_def] at hn
  refine ⟨hMA n (Finset.mem_of_mem_filter n hn), ?_⟩
  rw [arith_regular] at hreg
  exact lt_of_le_of_lt (hreg n (Finset.mem_of_mem_filter n hn)).2 hlogNk

theorem find_good_x_hqA_I {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hq : q ∈ ppowers_in_set A) (_h0A : 0 ∉ A)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge2 : 0 < log N) :
    q ∈ ppowers_in_set A_I := by
  rcases mem_ppowers_in_set.mp hq with ⟨hqpp, _⟩
  refine mem_ppowers_in_set.mpr ⟨hqpp, ?_⟩
  by_contra hlocalempty
  rw [Finset.not_nonempty_iff_eq_empty] at hlocalempty
  rw [rec_sum_local, hlocalempty, Finset.sum_empty, Rat.cast_zero] at hqlocal
  have hpos : 0 < (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) := by
    refine one_div_pos.mpr ?_
    positivity
  linarith

theorem find_good_x_hqlocal2 {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N) (hlarge2 : 0 < log N)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q) :
    1 / log N ≤ rec_sum_local A_I q := by
  have hpow99 : (2 : ℝ) ≤ log N ^ ((99 : ℝ) / 100) := by
    have hpow99' : (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) ≤ log N ^ ((99 : ℝ) / 100) := by
      exact Real.rpow_le_rpow (by positivity) hlarge6 (by positivity)
    calc
      (2 : ℝ) = (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) := by
        rw [← Real.rpow_mul zero_le_two]
        norm_num
      _ ≤ log N ^ ((99 : ℝ) / 100) := hpow99'
  have hden : 2 * log N ^ ((1 : ℝ) / 100) ≤ log N := by
    calc
      2 * log N ^ ((1 : ℝ) / 100)
          ≤ log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100) := by
            exact mul_le_mul_of_nonneg_right hpow99 (by positivity)
      _ = log N := by
        calc
          log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100)
              = log N ^ (((99 : ℝ) / 100) + ((1 : ℝ) / 100)) := by
                  rw [← Real.rpow_add hlarge2]
          _ = log N := by
            norm_num [Real.rpow_one]
  have hdenpos : 0 < 2 * log N ^ ((1 : ℝ) / 100) := by positivity
  exact le_trans (one_div_le_one_div_of_le hdenpos hden) hqlocal

theorem find_good_x_hsum {N q k d : ℕ} {M C : ℝ} {A A_I A_I' A_I'' : Finset ℕ}
    {I : Finset ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hA_I : A_I ⊆ range (N + 1)) (hA_I_subA : A_I ⊆ A) (hq : q ∈ ppowers_in_set A)
    (h0A : 0 ∉ A) (hC : 0 < C)
    (hreg : arith_regular N A)
    (hlargerecbound :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤ rec_sum A_I'' →
        (∀ n ∈ A_I'', (1 - 2 / 99) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
          (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
            (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k))
    (hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N))
    (hgood2 : (ω d : ℝ) < (5 / log k) * log (log N))
    (hgood3 :
      C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) ≤
        ((local_part A_I q).filter
            (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
          (fun n ↦ (q * d / n : ℝ)))
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N) :
    ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
  let _ := M
  let _ := I
  have hqpp : IsPrimePow q := (mem_ppowers_in_set.mp hq).1
  have hmain :
      (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
        (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    refine hlargerecbound ?_ ?_
    · calc
        log N ^ (-((2 : ℝ) / 99) / 2)
            ≤ C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := hlogNk2
        _ ≤ C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) := by
          have hmul : C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) ≤ C * rec_sum_local A_I q := by
            exact mul_le_mul_of_nonneg_left hqlocal (le_of_lt hC)
          exact div_le_div_of_nonneg_right hmul (by
            exact Real.rpow_nonneg (le_of_lt hlarge2) ((2 : ℝ) / k))
        _ ≤
            ((local_part A_I q).filter
                (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
              (fun n ↦ (q * d / n : ℝ)) := hgood3
        _ ≤ rec_sum A_I'' := by
          rw [rec_sum, Rat.cast_sum]
          push_cast
          let g : ℕ → ℕ := fun n ↦ n / (q * d)
          refine Finset.sum_le_sum_of_injOn g ?_ ?_ ?_ ?_
          · intro a ha b hb hab
            have ha' := Finset.mem_filter.mp ha
            have hb' := Finset.mem_filter.mp hb
            calc
              a = (q * d) * g a := by
                simp [g, Nat.mul_div_cancel' ha'.2.1]
              _ = (q * d) * g b := by rw [hab]
              _ = b := by
                simp [g, Nat.mul_div_cancel' hb'.2.1]
          · intro x hx
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            rw [hA_I''_def, Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_range]
              exact lt_of_le_of_lt (Nat.div_le_self a (q * d))
                (Finset.mem_range.mp (hA_I ha_local.1))
            · refine ⟨a, ?_, ?_, ?_⟩
              · rw [hA_I'_def, Finset.mem_filter]
                exact ⟨ha_local.1, ha'.2.1⟩
              · dsimp [g]
                exact Nat.div_mul_cancel ha'.2.1
              · simpa [g, Nat.coprime_comm] using ha'.2.2
          · intro a ha
            apply le_of_eq
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            have haA : a ∈ A := hA_I_subA ha_local.1
            have ha0 : a ≠ 0 := by
              intro hzero
              exact h0A (hzero ▸ haA)
            have hqd0 : q * d ≠ 0 := by
              intro hzero
              have : a = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ ha'.2.1)
              exact ha0 this
            have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast hqd0
            have hcast : (g a : ℝ) = (a : ℝ) / (q * d : ℕ) := by
              dsimp [g]
              rw [Nat.cast_div ha'.2.1 hqd0']
            rw [hcast, one_div_div, Nat.cast_mul]
          · intro b hb _
            exact one_div_nonneg.2 (Nat.cast_nonneg b)
    · intro n hn
      rw [hA_I''_def, Finset.mem_filter] at hn
      rcases hn.2 with ⟨m, hm1, hm2, hm3⟩
      rw [hA_I'_def, Finset.mem_filter] at hm1
      have hmA : m ∈ A := hA_I_subA hm1.1
      have hm0 : m ≠ 0 := by
        intro hzero
        exact h0A (hzero ▸ hmA)
      have hqdpos : 0 < q * d := by
        refine Nat.pos_iff_ne_zero.mpr ?_
        intro hzero
        have : m = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ hm1.2)
        exact hm0 this
      have hmdiv : m / (q * d) = n := by
        apply Nat.div_eq_of_eq_mul_right hqdpos
        simpa [mul_comm] using hm2.symm
      have hmreg := hreg m hmA
      refine ⟨?_, ?_⟩
      · calc
          (1 - 2 / 99) * log (log N) ≤ (ω m : ℝ) - (1 + 5 / log k * log (log N)) := by
            rw [le_sub_iff_add_le]
            exact le_trans hNlogk hmreg.1
          _ ≤ (ω m : ℝ) - ω (q * d) := by
            apply sub_le_sub_left
            calc
              (ω (q * d) : ℝ) ≤ 1 + (ω d : ℝ) := by
                exact_mod_cast omega_mul_ppower (a := d) hqpp
              _ ≤ 1 + (5 / log k) * log (log N) := by
                linarith [le_of_lt hgood2]
          _ ≤ ω (m / (q * d)) := sub_le_omega_div hm1.2
          _ = ω n := by rw [hmdiv]
      · calc
          (ω n : ℝ) = ω (m / (q * d)) := by rw [← hmdiv]
          _ ≤ ω m := by exact_mod_cast omega_div_le hm1.2
          _ ≤ 2 * log (log N) := hmreg.2
  calc
    ((35 : ℝ) / 100) * log (log N)
        ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) := by
          have hmul := mul_le_mul_of_nonneg_right useful_exp_estimate (le_of_lt hlarge1)
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := hmain

theorem find_good_x_hI'ne {N q d : ℕ} {A_I' A_I'' : Finset ℕ} {I I' : Finset ℤ}
    (hA_I'_witness : ∀ n ∈ A_I', ∃ x ∈ I, (n : ℤ) ∣ x)
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x))
    (hsum : ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlarge1 : 0 < log (log N)) :
    I'.Nonempty := by
  rw [hI'_def, Finset.filter_nonempty_iff]
  have hA_I'_ne : A_I'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    rw [Finset.eq_empty_iff_forall_notMem] at hem
    have hA_I''_empty : A_I'' = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro h
      rw [hA_I''_def, Finset.filter_nonempty_iff] at h
      rcases h with ⟨a, ha1, n, hn1, hn2⟩
      exact hem n hn1
    have hpp_empty : ppowers_in_set A_I'' = ∅ := by
      rw [hA_I''_empty]
      exact Finset.biUnion_empty
    rw [hpp_empty, Finset.sum_empty, ← not_lt] at hsum
    have hpos : 0 < ((35 : ℝ) / 100) * log (log N) := by positivity
    exact (hsum hpos).elim
  obtain ⟨n, hn⟩ := hA_I'_ne
  rcases hA_I'_witness n hn with ⟨x, hxI, hnx⟩
  exact ⟨x, hxI, n, hn, hnx⟩

theorem find_good_x_hI'single {N q k d : ℕ} {M t : ℝ} {A A_I A_I' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') (hI :
      I =
        Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (h0M : 0 < M) (hMN : M ≤ N) (_h0A : 0 ∉ A)
    (hgood1 : M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ y ∈ I', x = y := by
  intro y hy
  by_contra hxy
  have hx' := hx
  rw [hI'_def, Finset.mem_filter] at hx'
  rcases hx'.2 with ⟨mx, hmx, hmx'⟩
  have hmxqd : ((q * d : ℤ) ∣ (mx : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmx
    exact_mod_cast hmx.2
  have hdx : ((q * d : ℤ) ∣ x) := dvd_trans hmxqd hmx'
  have hy' := hy
  rw [hI'_def, Finset.mem_filter] at hy'
  rcases hy'.2 with ⟨my, hmy, hmy'⟩
  have hmyqd : ((q * d : ℤ) ∣ (my : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmy
    exact_mod_cast hmy.2
  have hdy : ((q * d : ℤ) ∣ y) := dvd_trans hmyqd hmy'
  let z : ℤ := |x - y|
  have hdz : ((q * d : ℤ) ∣ z) := by
    dsimp [z]
    rw [dvd_abs]
    exact dvd_sub hdx hdy
  have hzs :
      (z : ℝ) ≤ (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
    let w : ℝ := M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))
    let b : ℤ := ⌊t + w / 2⌋
    let a : ℤ := ⌈t - w / 2⌉
    have hIab : I = Icc a b := by
      simpa [a, b, w] using hI
    have hIx : x ∈ Icc a b := by
      simpa [hIab] using hx'.1
    have hIy : y ∈ Icc a b := by
      simpa [hIab] using hy'.1
    calc
      (z : ℝ) ≤ b - a := by
        simpa [z, Int.cast_abs] using (two_in_Icc hIx hIy)
      _ ≤ w / 2 + w / 2 := by
        simpa [a, b, w] using (floor_sub_ceil (z := t) (x := w / 2) (y := w / 2))
      _ = w := by ring
      _ = (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by rfl
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le h0M hMN
  have hpow_bound :
      (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    calc
      (N : ℝ) ^ (-(2 : ℝ) / log (log N))
          = Real.exp (log N * (-(2 : ℝ) / log (log N))) := by
              rw [Real.exp_mul, Real.exp_log hNpos]
      _ ≤ Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
        refine Real.exp_le_exp.mpr ?_
        have hloglog_bound : log (log N) ≤ 2 * log N ^ ((1 : ℝ) / k) := by
          have haux1 : log (log N) ≤ 2 * log (log N) := by linarith
          have haux2 : log (log N) ≤ log N ^ ((1 : ℝ) / k) := by
            exact le_trans haux1 (le_of_lt hlogNk)
          linarith
        have hdiv : 1 ≤ 2 * log N ^ ((1 : ℝ) / k) / log (log N) := by
          rw [le_div_iff₀ hlarge1]
          simpa using hloglog_bound
        have hsplit : log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k) = log N := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k)
                = log N ^ (((1 : ℝ) - 1 / k) + ((1 : ℝ) / k)) := by
                    rw [← Real.rpow_add hlarge2]
            _ = log N ^ (1 : ℝ) := by ring_nf
            _ = log N := by rw [Real.rpow_one]
        have hpow_main :
            log N ^ ((1 : ℝ) - 1 / k) ≤ 2 * log N / log (log N) := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) ≤
                log N ^ ((1 : ℝ) - 1 / k) * (2 * log N ^ ((1 : ℝ) / k) / log (log N)) := by
                  exact le_mul_of_one_le_right (by positivity) hdiv
            _ = (2 * (log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k))) / log (log N) := by ring
            _ = 2 * log N / log (log N) := by rw [hsplit]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using neg_le_neg hpow_main
  have hwidth_bound :
      M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    exact mul_le_mul_of_nonneg_left hpow_bound (le_of_lt h0M)
  have hzpos : 0 < z := by
    dsimp [z]
    exact abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hqdlez : ((q * d : ℤ)) ≤ z := by
    have hqdleabs : ((q * d : ℤ)) ≤ |z| := Int.le_abs_of_dvd (ne_of_gt hzpos) hdz
    simpa [abs_of_nonneg (le_of_lt hzpos)] using hqdleabs
  have hqdz : (q : ℝ) * d ≤ z := by
    exact_mod_cast hqdlez
  exact (not_le_of_gt hgood1) (le_trans hqdz (le_trans hzs hwidth_bound))

theorem find_good_x_hqx {q d : ℕ} {A_I A_I' : Finset ℕ} {I I' : Finset ℤ} {x : ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') :
    (q : ℤ) ∣ x := by
  rw [hI'_def] at hx
  rcases (Finset.mem_filter.mp hx).2 with ⟨n, hn, hnx⟩
  rw [hA_I'_def] at hn
  have hqdvdqd : (q : ℤ) ∣ (q * d : ℤ) := ⟨d, by simp⟩
  have hqdvdn_nat : q * d ∣ n := (Finset.mem_filter.mp hn).2
  have hqdvdn : ((q * d : ℤ) ∣ (n : ℤ)) := by
    rcases hqdvdn_nat with ⟨m, rfl⟩
    refine ⟨m, by simp [mul_assoc, mul_left_comm, mul_comm]⟩
  exact dvd_trans hqdvdqd (dvd_trans hqdvdn hnx)

theorem find_good_x_hpp {N q d : ℕ} {A A_I A_I' A_I'' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (_hx : x ∈ I') (h0A : 0 ∉ A) (hI'single : ∀ y ∈ I', x = y) :
    ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
  intro r hr
  rw [ppowers_in_set, Finset.mem_biUnion] at hr
  rcases hr with ⟨a, ha, hr⟩
  rw [Finset.mem_filter] at hr
  rw [hA_I''_def] at ha
  rw [Finset.mem_filter]
  rw [Finset.mem_filter] at ha
  rcases ha.2 with ⟨m, hm1, hm2⟩
  have hm1' := hm1
  rw [hA_I'_def, Finset.mem_filter] at hm1
  rw [hA_I_def, Finset.mem_filter] at hm1
  rcases hm1.1.2 with ⟨y, hy1, hy2⟩
  have hyI' : y ∈ I' := by
    rw [hI'_def, Finset.mem_filter]
    exact ⟨hy1, m, hm1', hy2⟩
  have hyx : x = y := hI'single y hyI'
  rw [hyx, ppowers_in_set, Finset.mem_biUnion]
  refine ⟨?_, ?_⟩
  · refine ⟨m, hm1.1.1, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hr.2.1, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [← hm2.1]
        exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
      · intro h0m
        rw [h0m] at hm1
        exact h0A hm1.1.1
    · rw [← hm2.1, mul_comm, Nat.mul_div_assoc]
      · refine Nat.Coprime.mul_right ?_ hr.2.2
        exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hr.1) hm2.2
      · exact Nat.dvd_of_mem_divisors hr.1
  · refine dvd_trans ?_ hy2
    have hrdvdm : r ∣ m := by
      rw [← hm2.1]
      exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
    exact_mod_cast hrdvdm

theorem find_good_x :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ A ⊆ range (N + 1),
          0 < M →
            M ≤ N →
              0 ∉ A →
                (∀ n ∈ A, M ≤ (n : ℝ)) →
                  arith_regular N A →
                    ∀ t : ℝ, ∀ I : Finset ℤ, ∀ q ∈ ppowers_in_set A,
                      I =
                          Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
                            ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ →
                        (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
                            rec_sum_local (A.filter (fun n ↦ ∃ x ∈ I, (n : ℤ) ∣ x)) q →
                          ∃ xq, xq ∈ I ∧ (q : ℤ) ∣ xq ∧
                              ((35 : ℝ) / 100) * log (log N) ≤
                                ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ xq)).sum
                                  (fun r : ℕ ↦ (1 / r : ℝ)) := by
  classical
  obtain ⟨c, C, hc, hC, hgoodd⟩ := find_good_d
  have heasy1 : 0 < ((2 : ℝ) / 99) := by
    norm_num
  have heasy2 : ((2 : ℝ) / 99) < 1 / 2 := by
    norm_num
  obtain hlargerecbound := rec_qsum_lower_bound ((2 : ℝ) / 99) heasy1 heasy2
  filter_upwards [hgoodd, hlargerecbound, another_large_N c C hc hC] with
    N hgooddN hlargerecbound hlargegroup M A hA h0M hMN h0A hMA hreg t I q hq hI hqlocal
  have hlarge4 : 4 * log (log (log N)) ≤ log (log N) := by
    exact hlargegroup.2.2.1
  have hlarge5 : 1 / c / 2 ≤ log (log (log N)) := by
    exact hlargegroup.1
  have hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N := by
    exact hlargegroup.2.1
  have hlarge7 : log 2 < log (log (log N)) := by
    exact hlargegroup.2.2.2.1
  have hlarge0 : 0 < log (log (log N)) := lt_trans (Real.log_pos one_lt_two) hlarge7
  have hlarge1 : 0 < log (log N) := by
    have hpos : 0 < 4 * log (log (log N)) := by positivity
    exact lt_of_lt_of_le hpos hlarge4
  have hlarge3 : 1 ≤ log N := by
    refine le_trans ?_ hlarge6
    refine one_le_rpow one_le_two ?_
    norm_num
  have hlarge2 : 0 < log N := lt_of_lt_of_le zero_lt_one hlarge3
  set A_I : Finset ℕ := A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x) with hA_I_def
  set k : ℕ := ⌊(log (log N)) / (2 * log (log (log N)))⌋₊ with hk
  have h1k : 1 < k := by
    simpa [hk] using find_good_x_h1k (N := N) (k := k) hk hlarge0 hlarge1 hlarge4
  have hkc : (k : ℝ) ≤ c * log (log N) := by
    simpa [hk] using find_good_x_hkc (N := N) (k := k) (c := c) hk hc hlarge5 hlarge0 hlarge1
  have hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
    simpa [hk] using find_good_x_hlogNk (N := N) (k := k) hk h1k hlarge7 hlarge1 hlarge2 hlarge3
  have hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := by
    simpa [hk] using hlargegroup.2.2.2.2.1
  have hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N) := by
    simpa [hk] using hlargegroup.2.2.2.2.2
  have hA_I : A_I ⊆ range (N + 1) := by
    simpa [hA_I_def] using subset_trans (Finset.filter_subset _ _) hA
  have hA_I' : ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
    simpa [hA_I_def] using
      find_good_x_hA_I' (N := N) (k := k) (M := M) (A := A) (I := I) (A_I := A_I) hA_I_def
        hMA hreg hlogNk
  have hqA_I : q ∈ ppowers_in_set A_I := by
    simpa [hA_I_def] using
      find_good_x_hqA_I (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def hq h0A
        hqlocal hlarge2
  have hqlocal2 : 1 / log N ≤ rec_sum_local A_I q := by
    simpa [hA_I_def] using
      find_good_x_hqlocal2 (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def
        hlarge6 hlarge2 hqlocal
  specialize hgooddN M k A_I hA_I h0M hMN h1k hkc hA_I' q hqA_I hqlocal2
  rcases hgooddN with ⟨d, hgood1, hgood2, hgood3⟩
  set A_I' : Finset ℕ := A_I.filter (fun n : ℕ ↦ q * d ∣ n) with hA_I'_def
  set A_I'' : Finset ℕ :=
    (range (N + 1)).filter
      (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)) with hA_I''_def
  have hsum :
      ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    exact
      find_good_x_hsum (N := N) (q := q) (k := k) (d := d) (M := M) (C := C) (A := A)
        (A_I := A_I) (A_I' := A_I') (A_I'' := A_I'') (I := I) hA_I'_def hA_I''_def hA_I
        (by
          intro n hn
          rw [hA_I_def, Finset.mem_filter] at hn
          exact hn.1)
        hq
        h0A hC hreg
        (by
          intro hrec hreg'
          exact hlargerecbound A_I'' hrec hreg')
        hlogNk2 hNlogk hgood2 hgood3 hqlocal hlarge1 hlarge2
  set I' : Finset ℤ := I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x) with hI'_def
  have hI'ne : I'.Nonempty := by
    exact
      find_good_x_hI'ne (N := N) (q := q) (d := d) (A_I' := A_I') (A_I'' := A_I'')
        (I := I) (I' := I') (by
          intro n hn
          rw [hA_I'_def, Finset.mem_filter] at hn
          rcases (Finset.mem_filter.mp hn.1).2 with ⟨x, hxI, hnx⟩
          exact ⟨x, hxI, hnx⟩) hA_I''_def hI'_def hsum hlarge1
  obtain ⟨x, hx⟩ := hI'ne
  have hI'single : ∀ y ∈ I', x = y := by
    exact
      find_good_x_hI'single (N := N) (q := q) (k := k) (d := d) (M := M) (t := t) (A := A)
        (A_I := A_I) (A_I' := A_I') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hI'_def
        hx hI h0M hMN h0A hgood1 hlarge1 hlarge2 hlogNk
  have hxI : x ∈ I := by
    rw [hI'_def] at hx
    exact Finset.mem_of_mem_filter x hx
  have hqx : (q : ℤ) ∣ x := by
    exact find_good_x_hqx (q := q) (d := d) (A_I := A_I) (A_I' := A_I') (I := I) (I' := I')
      (x := x) hA_I'_def hI'_def hx
  have hpp :
      ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
    exact
      find_good_x_hpp (N := N) (q := q) (d := d) (A := A) (A_I := A_I) (A_I' := A_I')
        (A_I'' := A_I'') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hA_I''_def hI'_def
        hx h0A hI'single
  have hfinal :
      ((35 : ℝ) / 100) * log (log N) ≤
        ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)).sum (fun r ↦ (1 / r : ℝ)) := by
    exact le_trans hsum <|
      Finset.sum_le_sum_of_subset_of_nonneg hpp (by
        intro i _ _
        positivity)
  exact ⟨x, hxI, hqx, hfinal⟩

end

end UnitFractions
