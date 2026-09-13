import Erdos289CLT.Basic

/-!
# Analytic bookkeeping

The uniform inequalities of paper §3–§4: the pool weights at stages `q > B` sum
to less than `1/20`; every stage has enough candidate centres; a pool pair at a
stage `q` with `m ≫ q / log q` has mass `O(log q / q²)`; the quota grows slowly.
-/

namespace Erdos289.CLT

open Finset

/-- The sum `∑_{B ≤ q ≤ X} 3 s(q) · 4 log q / (c₀ q²)` is below `1/20` for large `B`
(uniformly in `X`; the summand is `O(q^{-9/8})`). -/
private theorem log_nat_le_rpow_one_eighth {q : ℕ} (hq : 1 ≤ q) :
    Real.log q ≤ 8 * (q : ℝ) ^ ((1 : ℝ) / 8) := by
  have hqpos : (0:ℝ) < q := by positivity
  have hroot : 0 < (q : ℝ) ^ ((1:ℝ)/8) := by positivity
  have hlogroot : Real.log ((q:ℝ) ^ ((1:ℝ)/8)) ≤ (q:ℝ) ^ ((1:ℝ)/8) - 1 :=
    Real.log_le_sub_one_of_pos hroot
  have hsplit : Real.log q = 8 * Real.log ((q:ℝ) ^ ((1:ℝ)/8)) := by
    rw [Real.log_rpow hqpos]
    ring
  rw [hsplit]
  nlinarith [hlogroot]

private theorem tail_summand_le (c₀ : ℝ) (hc : 0 < c₀) {q : ℕ} (hq : 1 ≤ q) :
    (3 * (s q : ℝ)) * (4 * Real.log q / (c₀ * (q : ℝ) ^ 2)) ≤
      (192 / c₀) * (q : ℝ) ^ (-(9 : ℝ) / 8) := by
  have hqpos : (0:ℝ) < q := by positivity
  have hs : (s q : ℝ) ≤ (q:ℝ) ^ ((3:ℝ)/4) + 1 := s_le_rpow_add_one q
  have hlog : Real.log q ≤ 8 * (q:ℝ) ^ ((1:ℝ)/8) := log_nat_le_rpow_one_eighth hq
  have hq18_le : (q:ℝ) ^ ((1:ℝ)/8) ≤ (q:ℝ) ^ ((7:ℝ)/8) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_cast)
    norm_num
  have hq34_le : (q:ℝ) ^ ((7:ℝ)/8) ≤ (q:ℝ) ^ ((9:ℝ)/8) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_cast)
    norm_num
  have hmain : (q:ℝ) ^ ((1:ℝ)/8) * ((q:ℝ) ^ ((3:ℝ)/4) + 1) ≤
      2 * (q:ℝ) ^ ((7:ℝ)/8) := by
    have h1 : (q:ℝ) ^ ((1:ℝ)/8) * (q:ℝ) ^ ((3:ℝ)/4) ≤ (q:ℝ) ^ ((7:ℝ)/8) := by
      rw [← Real.rpow_add hqpos]
      norm_num
    nlinarith [h1, hq18_le]
  have hprod : (q:ℝ) ^ ((1:ℝ)/8) * ((q:ℝ) ^ ((3:ℝ)/4) + 1) *
      (q:ℝ) ^ ((9:ℝ)/8) ≤ 2 * (q:ℝ)^2 := by
    calc (q:ℝ) ^ ((1:ℝ)/8) * ((q:ℝ) ^ ((3:ℝ)/4) + 1) * (q:ℝ) ^ ((9:ℝ)/8)
          ≤ (2 * (q:ℝ) ^ ((7:ℝ)/8)) * (q:ℝ) ^ ((9:ℝ)/8) :=
            mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = 2 * ((q:ℝ) ^ ((7:ℝ)/8) * (q:ℝ) ^ ((9:ℝ)/8)) := by ring
        _ = 2 * (q:ℝ)^2 := by
            rw [← Real.rpow_add hqpos]
            norm_num
  calc (3 * (s q : ℝ)) * (4 * Real.log q / (c₀ * (q:ℝ)^2))
      ≤ 3 * ((q:ℝ)^((3:ℝ)/4) + 1) * (4 * (8 * (q:ℝ)^((1:ℝ)/8)) / (c₀ * (q:ℝ)^2)) := by
        gcongr
    _ ≤ (192 / c₀) * (q:ℝ) ^ (-(9:ℝ)/8) := by
        norm_num [Real.rpow_neg]
        field_simp
        nlinarith [hprod, hq18_le, hq34_le, hc]

theorem tail_small (c₀ : ℝ) (hc : 0 < c₀) : ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ X : ℕ,
    ∑ q ∈ Finset.Icc B X, (3 * (s q : ℝ)) * (4 * Real.log q / (c₀ * (q : ℝ) ^ 2)) < 1 / 20 := by
  set g : ℕ → ℝ := fun q => (192 / c₀) * (q : ℝ) ^ (-(9:ℝ)/8) with hg
  have hgnonneg : ∀ q, 0 ≤ g q := by
    intro q
    have h1 : (0:ℝ) ≤ (q:ℝ) ^ (-(9:ℝ)/8) := Real.rpow_nonneg (by positivity) _
    have h2 : (0:ℝ) ≤ 192 / c₀ := by positivity
    exact mul_nonneg h2 h1
  have hgsummable : Summable g := by
    have h1 : Summable (fun q : ℕ => (q:ℝ) ^ (-(9:ℝ)/8)) := Real.summable_nat_rpow.mpr (by norm_num)
    exact h1.mul_left _
  set S : ℝ := ∑' q, g q with hS
  have hpartial_le : ∀ n : ℕ, ∑ q ∈ Finset.range n, g q ≤ S :=
    fun n => hgsummable.sum_le_tsum _ (fun i _ => hgnonneg i)
  have htendsto : Filter.Tendsto (fun n => ∑ q ∈ Finset.range n, g q) Filter.atTop (nhds S) :=
    hgsummable.hasSum.tendsto_sum_nat
  have htendsto0 : Filter.Tendsto (fun n => S - ∑ q ∈ Finset.range n, g q) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := S) (f := Filter.atTop)).sub htendsto
    simpa using h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htendsto0 (1/20) (by norm_num)
  refine ⟨max N 1, ?_⟩
  intro B hB X
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) hB
  have hBN : N ≤ B := le_trans (le_max_left _ _) hB
  have hbound : ∀ q ∈ Finset.Icc B X, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀ * (q:ℝ)^2)) ≤ g q := by
    intro q hq
    have hq1 : 1 ≤ q := le_trans hB1 (Finset.mem_Icc.mp hq).1
    exact tail_summand_le c₀ hc hq1
  have hsum_le : ∑ q ∈ Finset.Icc B X, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀ * (q:ℝ)^2))
      ≤ ∑ q ∈ Finset.Icc B X, g q := Finset.sum_le_sum hbound
  have hlt : ∑ q ∈ Finset.Icc B X, g q < 1/20 := by
    by_cases hBX : B ≤ X
    · have heq : Finset.Icc B X = Finset.Ico B (X+1) := (Finset.Ico_add_one_right_eq_Icc B X).symm
      rw [heq, Finset.sum_Ico_eq_sub g (by omega : B ≤ X+1)]
      have hrange_le : ∑ q ∈ Finset.range (X+1), g q ≤ S := hpartial_le (X+1)
      have hdist := hN B hBN
      rw [Real.dist_eq] at hdist
      have habs : S - ∑ q ∈ Finset.range B, g q < 1/20 := by
        rw [abs_of_nonneg (by linarith [hpartial_le B])] at hdist
        linarith
      linarith
    · have hempty : Finset.Icc B X = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty]
      simp
  linarith

private theorem nat_log2_mul_log2_le {q : ℕ} (hq : 1 ≤ q) :
    (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
  have hle : (2:ℕ) ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hlecast : ((2:ℕ)^Nat.log 2 q : ℝ) ≤ (q:ℝ) := by exact_mod_cast hle
  have hpow : ((2:ℕ)^Nat.log 2 q : ℝ) = (2:ℝ)^(Nat.log 2 q) := by push_cast; ring
  have hloglepow : Real.log ((2:ℝ)^(Nat.log 2 q)) ≤ Real.log q := by
    apply Real.log_le_log (by positivity)
    rw [← hpow]; exact hlecast
  rwa [Real.log_pow] at hloglepow

/-- For large `B` and every `q ≥ B`, `c₀ q / log q` exceeds the quota plus all exclusions. -/
theorem cand_enough (c₀ : ℝ) (hc : 0 < c₀) : ∃ B₂ : ℕ, ∀ B : ℕ, B₂ ≤ B → ∀ q : ℕ, B ≤ q →
    ((9 * s q + 2 * s B + 2 * (2 * Nat.log 2 q + 1) : ℕ) : ℝ) ≤ c₀ * q / Real.log q := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C' : ℝ := 88 + 256 / Real.log 2 + 104 with hC'
  have hC'pos : 0 < C' := by positivity
  set q0 : ℝ := (C' / c₀) ^ (8:ℝ) with hq0
  have hq0nonneg : 0 ≤ C' / c₀ := by positivity
  set B₂ : ℕ := max (Nat.ceil q0) 2 with hB₂
  refine ⟨B₂, ?_⟩
  intro B hB q hBq
  have hq2 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) hB) hBq
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogqpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  rw [le_div_iff₀ hlogqpos]
  push_cast
  have hsB_le_sq : s B ≤ s q := s_mono hBq
  have hsq_bound : (s q :ℝ) ≤ (q:ℝ)^((3:ℝ)/4) + 1 := s_le_rpow_add_one q
  have hlog2mul : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := nat_log2_mul_log2_le hq1
  have hlogq_bound : Real.log q ≤ 8 * (q:ℝ)^((1:ℝ)/8) := log_nat_le_rpow_one_eighth hq1
  have hstep1 : (9 * (s q:ℝ) + 2 * (s B:ℝ) + 2 * (2 * (Nat.log 2 q:ℝ) + 1))
      ≤ 11 * (q:ℝ)^((3:ℝ)/4) + 4 * (Nat.log 2 q : ℝ) + 13 := by
    have h1 : (s B:ℝ) ≤ (s q:ℝ) := by exact_mod_cast hsB_le_sq
    nlinarith [hsq_bound, h1]
  have hq14_le_q78 : (q:ℝ)^((1:ℝ)/4) ≤ (q:ℝ)^((7:ℝ)/8) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
    norm_num
  have hq18_le_q78 : (q:ℝ)^((1:ℝ)/8) ≤ (q:ℝ)^((7:ℝ)/8) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1)
    norm_num
  have hterm1 : 11 * (q:ℝ)^((3:ℝ)/4) * Real.log q ≤ 88 * (q:ℝ)^((7:ℝ)/8) := by
    have h1 : (q:ℝ)^((3:ℝ)/4) * Real.log q ≤ (q:ℝ)^((3:ℝ)/4) * (8 * (q:ℝ)^((1:ℝ)/8)) :=
      mul_le_mul_of_nonneg_left hlogq_bound (by positivity)
    have h2 : (q:ℝ)^((3:ℝ)/4) * (8 * (q:ℝ)^((1:ℝ)/8)) = 8 * (q:ℝ)^((7:ℝ)/8) := by
      rw [show (q:ℝ)^((3:ℝ)/4) * (8 * (q:ℝ)^((1:ℝ)/8)) = 8 * ((q:ℝ)^((3:ℝ)/4) * (q:ℝ)^((1:ℝ)/8)) by ring,
        ← Real.rpow_add hqpos]
      norm_num
    nlinarith [h1, h2]
  have hterm2 : (4 * (Nat.log 2 q : ℝ) * Real.log q) * Real.log 2 ≤ 256 * (q:ℝ)^((7:ℝ)/8) := by
    have hLnn : 0 ≤ (Nat.log 2 q:ℝ) := by positivity
    have hℓnn : 0 ≤ Real.log q := hlogqpos.le
    have h1 : (Nat.log 2 q:ℝ) * Real.log 2 * Real.log q ≤ Real.log q * Real.log q :=
      mul_le_mul_of_nonneg_right hlog2mul hℓnn
    have h2 : Real.log q * Real.log q ≤ (8 * (q:ℝ)^((1:ℝ)/8)) * (8 * (q:ℝ)^((1:ℝ)/8)) :=
      mul_le_mul hlogq_bound hlogq_bound hℓnn (by positivity)
    have h3 : (8 * (q:ℝ)^((1:ℝ)/8)) * (8 * (q:ℝ)^((1:ℝ)/8)) = 64 * (q:ℝ)^((1:ℝ)/4) := by
      rw [show (8 * (q:ℝ)^((1:ℝ)/8)) * (8 * (q:ℝ)^((1:ℝ)/8)) = 64 * ((q:ℝ)^((1:ℝ)/8) * (q:ℝ)^((1:ℝ)/8)) by ring,
        ← Real.rpow_add hqpos]
      norm_num
    nlinarith [h1, h2, h3, hq14_le_q78]
  have hterm3' : 13 * Real.log q ≤ 104 * (q:ℝ)^((7:ℝ)/8) := by
    nlinarith [hlogq_bound, hq18_le_q78]
  have hterm2' : 4 * (Nat.log 2 q : ℝ) * Real.log q ≤ (256 / Real.log 2) * (q:ℝ)^((7:ℝ)/8) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
    exact hterm2
  have hcombine : (11 * (q:ℝ)^((3:ℝ)/4) + 4 * (Nat.log 2 q : ℝ) + 13) * Real.log q ≤ C' * (q:ℝ)^((7:ℝ)/8) := by
    have hexpand : (11 * (q:ℝ)^((3:ℝ)/4) + 4 * (Nat.log 2 q : ℝ) + 13) * Real.log q
        = 11 * (q:ℝ)^((3:ℝ)/4) * Real.log q + 4 * (Nat.log 2 q:ℝ) * Real.log q + 13 * Real.log q := by ring
    rw [hexpand, hC']
    nlinarith [hterm1, hterm2', hterm3']
  have hfinal : (9 * (s q:ℝ) + 2 * (s B:ℝ) + 2 * (2 * (Nat.log 2 q:ℝ) + 1)) * Real.log q ≤ C' * (q:ℝ)^((7:ℝ)/8) :=
    le_trans (mul_le_mul_of_nonneg_right hstep1 hlogqpos.le) hcombine
  have hqge : (q0:ℝ) ≤ (q:ℝ) := by
    have h1 : q0 ≤ (Nat.ceil q0 : ℝ) := Nat.le_ceil q0
    have h2 : (Nat.ceil q0 : ℝ) ≤ (B₂ : ℝ) := by
      exact_mod_cast le_max_left (Nat.ceil q0) 2
    have h3 : (B₂:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
    have h4 : (B:ℝ) ≤ (q:ℝ) := by exact_mod_cast hBq
    linarith
  have hq18ge : C' / c₀ ≤ (q:ℝ) ^ ((1:ℝ)/8) := by
    have h1 : ((q0:ℝ)) ^ ((1:ℝ)/8) ≤ (q:ℝ) ^ ((1:ℝ)/8) :=
      Real.rpow_le_rpow (by positivity) hqge (by norm_num)
    have h2 : (q0:ℝ) ^ ((1:ℝ)/8) = C' / c₀ := by
      rw [hq0, ← Real.rpow_mul hq0nonneg]
      norm_num
    linarith [h1, h2]
  have hlast : C' * (q:ℝ)^((7:ℝ)/8) ≤ c₀ * q := by
    have h1 : C' ≤ (q:ℝ)^((1:ℝ)/8) * c₀ := (div_le_iff₀ hc).mp hq18ge
    have h2 : C' * (q:ℝ)^((7:ℝ)/8) ≤ ((q:ℝ)^((1:ℝ)/8) * c₀) * (q:ℝ)^((7:ℝ)/8) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((q:ℝ)^((1:ℝ)/8) * c₀) * (q:ℝ)^((7:ℝ)/8) = c₀ * q := by
      rw [show ((q:ℝ)^((1:ℝ)/8) * c₀) * (q:ℝ)^((7:ℝ)/8) = c₀ * ((q:ℝ)^((1:ℝ)/8) * (q:ℝ)^((7:ℝ)/8)) by ring,
        ← Real.rpow_add hqpos]
      norm_num
    linarith [h2, h3]
  linarith [hfinal, hlast]

/-- A pool pair `[lo, lo+1]` with `q m ∈ {lo, lo+1}` and `m ≥ c₀ q / log q` has small mass. -/
theorem pool_pair_mass_le (c₀ : ℝ) (hc : 0 < c₀) {q m lo : ℕ} (hq : 2 ≤ q)
    (hm : c₀ * q / Real.log q ≤ m) (hm1 : 1 ≤ m) (hlo : lo = q * m ∨ lo + 1 = q * m) :
    ((Iv.pair lo).mass : ℝ) ≤ 4 * Real.log q / (c₀ * (q : ℝ) ^ 2) := by
  have hlogpos : 0 < Real.log q := Real.log_pos (by norm_cast)
  have hqm : q ≤ q * m := Nat.le_mul_of_pos_right q hm1
  have hqm2 : 2 ≤ q * m := by omega
  have hqpos : (0:ℝ) < q := by positivity
  have hq' : (0:ℝ) < q * m := by positivity
  have hcast : ((c₀ : ℝ) * q / Real.log q ≤ m) := by exact_mod_cast hm
  have hcmul : (c₀ : ℝ) * q ≤ Real.log q * m := by
    rw [div_le_iff₀ hlogpos] at hcast
    linarith [hcast]
  have hcq : (c₀ : ℝ) * q * q ≤ Real.log q * (q * m) := by
    nlinarith [sq_nonneg q]
  -- First show the crude real mass estimate at the integer location.
  have hlo1 : 1 ≤ lo := by
    rcases hlo with h | h
    · linarith [hqm2]
    · omega
  have hloreal : (1:ℝ) ≤ lo := by exact_mod_cast hlo1
  have hmass : ((Iv.pair lo).mass : ℝ) ≤ 2 / lo :=
    pair_mass_le_real hlo1
  have hkey : 2 / (lo : ℝ) ≤ 4 / (q * m : ℝ) := by
    rcases hlo with h | h
    · have hqmreal : (0:ℝ) ≤ (q * m : ℝ) := by positivity
      rw [h]
      push_cast [Nat.cast_mul] at hqmreal ⊢
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hqmreal]
    · have h' : ((q * m : ℕ) : ℝ) = lo + 1 := by exact_mod_cast h.symm
      push_cast [Nat.cast_mul] at h' ⊢
      rw [h']
      have hlopos : (0:ℝ) ≤ lo := by positivity
      field_simp
      nlinarith [hloreal]
  calc ((Iv.pair lo).mass : ℝ) ≤ 2 / lo := hmass
    _ ≤ 4 / (q * m : ℝ) := hkey
    _ ≤ 4 * Real.log q / (c₀ * q ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hcq]

/-- `s(n+1) ≤ 2 s(2^{⌊log₂ n⌋})`. -/
theorem s_succ_le {n : ℕ} (_hn : 1 ≤ n) : s (n + 1) ≤ 2 * s (2 ^ Nat.log 2 n) := by
  have h : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by
    have h' := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    exact Nat.succ_le_of_lt h'
  have heq : 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by
    rw [Nat.pow_succ]
    ring
  calc s (n + 1) ≤ s (2 ^ (Nat.log 2 n + 1)) := s_mono h
    _ = s (2 * 2 ^ Nat.log 2 n) := by rw [heq]
    _ ≤ 2 * s (2 ^ Nat.log 2 n) := s_two_mul_le _

end Erdos289.CLT
