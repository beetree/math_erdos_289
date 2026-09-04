import Erdos289.Lemma1
import Erdos289.Lemma4

set_option maxHeartbeats 1000000

namespace Erdos289

open Finset Filter Topology

-- Scratch: helper divisor-count lemma
theorem divisors_card_le_rpow (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, ∀ n : ℕ, (q:ℝ) ≤ (n:ℝ) → (n:ℝ) ≤ (q:ℝ)^C →
      (n.divisors.card : ℝ) ≤ (q:ℝ)^δ := by
  have hδ' : (0:ℝ) < δ / C := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (divisor_bound (δ / C) hδ')
  filter_upwards [eventually_ge_atTop N] with q hq n hqn hnC
  have hnN : N ≤ n := by
    have : (N:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have : (N:ℝ) ≤ (n:ℝ) := le_trans this hqn
    exact_mod_cast this
  have htau : (n.divisors.card : ℝ) ≤ (n:ℝ) ^ (δ/C) := hN n hnN
  have hqpos : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hmono : (n:ℝ) ^ (δ/C) ≤ ((q:ℝ)^C) ^ (δ/C) :=
    Real.rpow_le_rpow (by positivity) hnC hδ'.le
  have heq : ((q:ℝ)^C) ^ (δ/C) = (q:ℝ)^δ := by
    rw [← Real.rpow_mul hqpos]
    congr 1
    field_simp
  linarith [htau, hmono, heq ▸ hmono]

theorem tendsto_log_natCast_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

-- eventual linear domination: c ≤ η * log q
theorem const_le_mul_log_eventually (c η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, c ≤ η * Real.log q := by
  have h := tendsto_log_natCast_atTop.eventually_ge_atTop (c / η)
  filter_upwards [h] with q hq
  rw [div_le_iff₀ hη] at hq
  linarith

theorem rpow_ge_eventually (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ q : ℕ in atTop, c ≤ (q:ℝ)^ε := by
  have h := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

open Classical in
/-- The set of `t` in `Icc A B` with a prime factor exceeding `Dn`. -/
noncomputable def bigPrimeFactor (A B Dn : ℕ) : Finset ℕ :=
  (Finset.Icc A B).filter (fun t => ∃ ℓ, ℓ.Prime ∧ Dn < ℓ ∧ ℓ ∣ t)

theorem bigPrimeFactor_subset (A B Dn : ℕ) (hA : 1 ≤ A) :
    bigPrimeFactor A B Dn ⊆
      ((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun ℓ => (Icc A B).filter (ℓ ∣ ·)) := by
  intro t ht
  simp only [bigPrimeFactor, mem_filter, mem_Icc] at ht
  obtain ⟨⟨htA, htB⟩, ℓ, hℓ, hℓD, hℓt⟩ := ht
  have ht0 : 0 < t := by omega
  have hℓt' : ℓ ≤ t := Nat.le_of_dvd ht0 hℓt
  refine Finset.mem_biUnion.mpr ⟨ℓ, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hℓD, hℓt'.trans htB⟩, hℓ⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htA, htB⟩, hℓt⟩

theorem bigPrimeFactor_card_le (A B Dn : ℕ) (hAB : A ≤ B) :
    (((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun ℓ => (Icc A B).filter (ℓ ∣ ·))).card ≤
      ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) := by
  have h1 : (((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun ℓ => (Icc A B).filter (ℓ ∣ ·))).card
      ≤ ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, ((Icc A B).filter (ℓ ∣ ·)).card :=
    Finset.card_biUnion_le
  have h2 : (∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, ((Icc A B).filter (ℓ ∣ ·)).card : ℝ) ≤
      ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    simp only [mem_filter, mem_Ioc] at hℓ
    have hℓ0 : 0 < ℓ := hℓ.2.pos
    rw [sub_div]
    exact card_filter_dvd_Icc_le A B ℓ hℓ0 hAB
  calc ((((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun ℓ => (Icc A B).filter (ℓ ∣ ·))).card : ℝ)
      ≤ (∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, ((Icc A B).filter (ℓ ∣ ·)).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) := h2

theorem bad1_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∃ η : ℝ, 0 < η ∧ η < ε / 2 ∧ ∀ᶠ q : ℕ in atTop,
      ((bigPrimeFactor ⌈4 * (q:ℝ)^ε⌉₊ ⌊5 * (q:ℝ)^ε⌋₊ ⌈(q:ℝ)^(ε - η)⌉₊).card : ℝ) ≤
        κ * (q:ℝ)^ε := by
  intro κ hκ
  set η : ℝ := ε * (min κ 1) / 100 with hηdef
  have hminpos : 0 < min κ 1 := lt_min hκ (by norm_num)
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηε : η < ε / 2 := by
    rw [hηdef]
    have : min κ 1 ≤ 1 := min_le_right _ _
    nlinarith
  refine ⟨η, hη0, hηε, ?_⟩
  obtain ⟨C_pc, hC_pc⟩ := primeCounting_le
  have hCpc0 : 0 ≤ C_pc := by
    have h2 := hC_pc 2 (le_refl 2)
    push_cast at h2
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpc0 : (0:ℝ) ≤ (Nat.primeCounting 2 : ℝ) := by positivity
    rw [le_div_iff₀ hlog2] at h2
    nlinarith [h2, hlog2, hpc0]
  obtain ⟨X₁, hX₁2, hmert⟩ := mertens_gap (κ / 25) (by linarith)
  have hεη0 : 0 < ε - η := by linarith
  filter_upwards [rpow_ge_eventually ε hε0 4, rpow_ge_eventually (ε - η) hεη0 (X₁ : ℝ),
      const_le_mul_log_eventually (Real.log 5) η hη0,
      const_le_mul_log_eventually (25 * C_pc / κ) ε hε0,
      eventually_ge_atTop 2]
    with q hM4 hDX1 hlog5 hCbound hq2
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  set M : ℝ := (q:ℝ) ^ ε with hMdef
  set D : ℝ := (q:ℝ) ^ (ε - η) with hDdef
  set A : ℕ := ⌈4 * M⌉₊ with hAdef
  set B : ℕ := ⌊5 * M⌋₊ with hBdef
  set Dn : ℕ := ⌈D⌉₊ with hDndef
  have hM1 : (1:ℝ) ≤ M := by linarith [hM4]
  have hAR : 4 * M ≤ (A:ℝ) := Nat.le_ceil _
  have hBR : (B:ℝ) ≤ 5 * M := Nat.floor_le (by linarith)
  have hBR2 : 5 * M - 1 < (B:ℝ) := by
    have := Nat.lt_floor_add_one (5 * M)
    linarith [this]
  have hA1 : 1 ≤ A := by
    have : (1:ℝ) ≤ (A:ℝ) := by linarith
    exact_mod_cast this
  have hDM : D ≤ M := by
    rw [hDdef, hMdef]
    apply Real.rpow_le_rpow_of_exponent_le hqR1
    linarith
  have hBge4M : 4 * M ≤ (B:ℝ) := by linarith
  have hAleB : A ≤ B := by
    rw [hAdef]
    exact Nat.ceil_le.mpr hBge4M
  have hDnleB : Dn ≤ B := by
    rw [hDndef]
    exact Nat.ceil_le.mpr (by linarith [hDM, hBge4M])
  have hX1leDn : X₁ ≤ Dn := by
    have h1 : (X₁:ℝ) ≤ D := hDX1
    have h2 : D ≤ (Dn:ℝ) := Nat.le_ceil _
    have : (X₁:ℝ) ≤ (Dn:ℝ) := le_trans h1 h2
    exact_mod_cast this
  have hB2 : 2 ≤ B := by omega
  -- Step 1: subset + biUnion card bound
  have hsub : bigPrimeFactor A B Dn ⊆
      ((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun ℓ => (Icc A B).filter (ℓ ∣ ·)) :=
    bigPrimeFactor_subset A B Dn hA1
  have hcard1 : ((bigPrimeFactor A B Dn).card : ℝ) ≤
      ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) := by
    calc ((bigPrimeFactor A B Dn).card : ℝ)
        ≤ ((((Finset.Ioc Dn B).filter Nat.Prime).biUnion
            (fun ℓ => (Icc A B).filter (ℓ ∣ ·))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) :=
          bigPrimeFactor_card_le A B Dn hAleB
  -- Step 2: split the sum
  set S : ℝ := ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (1:ℝ)/ℓ with hSdef
  set P : ℕ := ((Finset.Ioc Dn B).filter Nat.Prime).card with hPdef
  have hsplit : ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2)
      = ((B:ℝ) - A) * S + 2 * P := by
    have e1 : ∀ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime,
        ((B:ℝ)-A)/ℓ + 2 = ((B:ℝ)-A)*(1/(ℓ:ℝ)) + 2 := by
      intro ℓ _; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, hSdef, hPdef]
    ring
  -- Step 3: bound S via mertens_gap
  have hSbound : S ≤ Real.log (Real.log B / Real.log Dn) + κ / 25 :=
    hmert Dn B hX1leDn hDnleB
  have hDn2 : 2 ≤ Dn := le_trans hX₁2 hX1leDn
  have hDnR1 : (1:ℝ) < (Dn:ℝ) := by exact_mod_cast (by omega : 1 < Dn)
  have hlogDnpos : 0 < Real.log (Dn:ℝ) := Real.log_pos hDnR1
  have hlogDn_ge : (ε - η) * Real.log q ≤ Real.log (Dn:ℝ) := by
    have h1 : D ≤ (Dn:ℝ) := Nat.le_ceil _
    have hDpos : 0 < D := by rw [hDdef]; positivity
    have h2 : Real.log D ≤ Real.log (Dn:ℝ) := Real.log_le_log hDpos h1
    rwa [hDdef, Real.log_rpow hqpos] at h2
  have hBR1 : (1:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hlogB_le : Real.log (B:ℝ) ≤ Real.log 5 + ε * Real.log q := by
    have h1 : Real.log (B:ℝ) ≤ Real.log (5 * M) := Real.log_le_log (by linarith) hBR
    have h5Mpos : (0:ℝ) < 5 := by norm_num
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    rwa [hMdef, Real.log_rpow hqpos] at h1
  set γ : ℝ := 2 * η / (ε - η) with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hchain : Real.log (B:ℝ) ≤ (1 + γ) * Real.log (Dn:ℝ) := by
    have hstep1 : Real.log 5 + ε * Real.log q ≤ (ε + η) * Real.log q := by linarith [hlog5]
    have hstep2 : (1 + γ) * (ε - η) = ε + η := by
      rw [hγdef]; field_simp; ring
    have hstep3 : (ε + η) * Real.log q ≤ (1 + γ) * Real.log (Dn:ℝ) := by
      rw [← hstep2]
      have hlogqpos : 0 ≤ Real.log q := Real.log_nonneg hqR1
      nlinarith [hlogDn_ge, hγ0]
    linarith [hlogB_le, hstep1, hstep3]
  have hratio : Real.log (B:ℝ) / Real.log (Dn:ℝ) ≤ 1 + γ := by
    rw [div_le_iff₀ hlogDnpos]
    linarith [hchain]
  have hloglog : Real.log (Real.log B / Real.log Dn) ≤ γ := by
    have h1 : Real.log (Real.log (B:ℝ) / Real.log (Dn:ℝ)) ≤ Real.log (1 + γ) :=
      Real.log_le_log (div_pos (Real.log_pos hBR1) hlogDnpos) hratio
    have h2 : Real.log (1 + γ) ≤ γ := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + γ by linarith)
      linarith
    linarith
  have hγbound : γ ≤ κ / 25 := by
    rw [hγdef]
    have hεη2 : ε / 2 ≤ ε - η := by linarith
    have hminκ : min κ 1 ≤ κ := min_le_left _ _
    rw [div_le_iff₀ hεη0]
    have h100 : η = ε * min κ 1 / 100 := hηdef
    nlinarith [hminκ, hεη2, hε0.le]
  have hSbound2 : S ≤ 2 * κ / 25 := by
    have := hSbound
    linarith [hloglog, hγbound]
  have hSnonneg : 0 ≤ S := by
    rw [hSdef]; apply Finset.sum_nonneg; intro ℓ hℓ; positivity
  have hBA : (B:ℝ) - A ≤ M := by linarith [hBR, hAR]
  have hBAnonneg : (0:ℝ) ≤ (B:ℝ) - A := by
    have h : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAleB
    linarith
  have hterm1 : ((B:ℝ) - A) * S ≤ M * (2 * κ / 25) := by
    calc ((B:ℝ) - A) * S ≤ M * S := by
          apply mul_le_mul_of_nonneg_right hBA hSnonneg
      _ ≤ M * (2 * κ / 25) := by
          apply mul_le_mul_of_nonneg_left hSbound2 (by linarith)
  -- bound P via primeCounting_le
  have hPsub : (Finset.Ioc Dn B).filter Nat.Prime ⊆ (Finset.Icc 1 B).filter Nat.Prime := by
    intro x hx
    simp only [mem_filter, mem_Ioc, mem_Icc] at hx ⊢
    exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩
  have hPle : P ≤ Nat.primeCounting B := by
    rw [hPdef, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    exact Finset.card_le_card hPsub
  have hPleR : (P:ℝ) ≤ C_pc * (B:ℝ) / Real.log B := by
    have h1 : (Nat.primeCounting B : ℝ) ≤ C_pc * (B:ℝ) / Real.log B := hC_pc B hB2
    have h2 : (P:ℝ) ≤ (Nat.primeCounting B : ℝ) := by exact_mod_cast hPle
    linarith
  have hlogB_ge4 : Real.log 4 + ε * Real.log q ≤ Real.log (B:ℝ) := by
    have h1 : Real.log (4 * M) ≤ Real.log (B:ℝ) := Real.log_le_log (by linarith) hBge4M
    rwa [Real.log_mul (by norm_num) (by linarith), hMdef, Real.log_rpow hqpos] at h1
  have hlog4nonneg : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogBge : 25 * C_pc / κ ≤ Real.log (B:ℝ) := by
    have := hCbound
    linarith [hlogB_ge4, hlog4nonneg]
  have hterm2 : 2 * (P:ℝ) ≤ (2 / 5) * κ * M := by
    have key : 2 * C_pc * (B:ℝ) ≤ (2/5) * κ * M * Real.log (B:ℝ) := by
      have hstepA : 25 * C_pc ≤ κ * Real.log (B:ℝ) := by
        rw [div_le_iff₀ hκ] at hlogBge; linarith
      have hstepB : (10:ℝ) * C_pc ≤ (2/5) * κ * Real.log (B:ℝ) := by linarith
      have h1 : 2 * C_pc * (B:ℝ) ≤ 2 * C_pc * (5 * M) :=
        mul_le_mul_of_nonneg_left hBR (by linarith)
      have h3 : (10 * C_pc) * M ≤ ((2/5) * κ * Real.log (B:ℝ)) * M :=
        mul_le_mul_of_nonneg_right hstepB (by linarith)
      calc 2 * C_pc * (B:ℝ) ≤ 2 * C_pc * (5 * M) := h1
        _ = (10 * C_pc) * M := by ring
        _ ≤ ((2/5) * κ * Real.log (B:ℝ)) * M := h3
        _ = (2/5) * κ * M * Real.log (B:ℝ) := by ring
    have hlogBpos : 0 < Real.log (B:ℝ) := Real.log_pos hBR1
    calc 2 * (P:ℝ) ≤ 2 * (C_pc * (B:ℝ) / Real.log B) := by linarith [hPleR]
      _ = 2 * C_pc * (B:ℝ) / Real.log B := by ring
      _ ≤ (2/5) * κ * M := by
          rw [div_le_iff₀ hlogBpos]; linarith [key]
  -- combine everything
  have hfinal : ((bigPrimeFactor A B Dn).card : ℝ) ≤
      M * (2 * κ / 25) + (2/5) * κ * M := by
    calc ((bigPrimeFactor A B Dn).card : ℝ)
        ≤ ∑ ℓ ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B:ℝ) - A)/ℓ + 2) := hcard1
      _ = ((B:ℝ) - A) * S + 2 * P := hsplit
      _ ≤ M * (2 * κ / 25) + (2/5) * κ * M := by linarith [hterm1, hterm2]
  have : M * (2 * κ / 25) + (2/5) * κ * M ≤ κ * M := by nlinarith [hM1, hκ]
  calc ((bigPrimeFactor A B Dn).card : ℝ) ≤ M * (2 * κ / 25) + (2/5) * κ * M := hfinal
    _ ≤ κ * M := this

theorem log_mul_rpow_neg_le (c target : ℝ) (hc : 0 < c) (htarget : 0 < target) :
    ∀ᶠ q : ℕ in atTop, Real.log q / (q:ℝ)^c ≤ target := by
  have hc2 : (0:ℝ) < c/2 := by linarith
  have key : ∀ᶠ q:ℕ in atTop, Real.log q ≤ (q:ℝ)^(c/2) / (c/2) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have h1 : Real.log ((q:ℝ)^(c/2)) ≤ (q:ℝ)^(c/2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hqpos] at h1
    rw [le_div_iff₀ hc2]
    nlinarith [h1]
  have hbound2 : ∀ᶠ q:ℕ in atTop, (2/c) / (q:ℝ)^(c/2) ≤ target := by
    have hev := rpow_neg_mul_eventually_le (c/2) hc2 (2/c) target htarget
    filter_upwards [hev, eventually_gt_atTop 0] with q hq hqpos'
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos'
    rw [Real.rpow_neg hqpos.le] at hq
    rwa [div_eq_mul_inv]
  filter_upwards [key, hbound2, eventually_gt_atTop 0] with q hlogq hbnd hqpos'
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos'
  have hc2pos : (0:ℝ) < (q:ℝ)^(c/2) := Real.rpow_pos_of_pos hqpos (c/2)
  have heq : (q:ℝ)^c = (q:ℝ)^(c/2) * (q:ℝ)^(c/2) := by rw [← Real.rpow_add hqpos]; ring_nf
  rw [heq, div_le_iff₀ (by positivity)]
  have hB' : 2/c ≤ target * (q:ℝ)^(c/2) := by
    rw [div_le_iff₀ hc2pos] at hbnd
    linarith [hbnd]
  calc Real.log q ≤ (q:ℝ)^(c/2)/(c/2) := hlogq
    _ = (2/c) * (q:ℝ)^(c/2) := by field_simp
    _ ≤ (target * (q:ℝ)^(c/2)) * (q:ℝ)^(c/2) :=
        mul_le_mul_of_nonneg_right hB' (by positivity)
    _ = target * ((q:ℝ)^(c/2) * (q:ℝ)^(c/2)) := by ring

theorem mOf_bound {q U t : ℕ} (hUdvd : q ∣ U) (hU1 : 1 < U) (hcop : Nat.Coprime t U)
    (M : ℝ) (hMpos : 0 < M) (ht2 : (t:ℝ) ≤ 5 * M) (hr2 : 2 * rOf U t < q) :
    (mOf q U t : ℝ) < 3 * M := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hUdvd; omega
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqRpos : (0:ℝ) < (q:ℝ) := by linarith
  have heq : q * mOf q U t + 1 = rOf U t * t := mOf_spec hUdvd hU1 hcop
  have heqR : (q:ℝ) * mOf q U t + 1 = (rOf U t : ℝ) * t := by exact_mod_cast heq
  have hrR : (rOf U t : ℝ) < (q:ℝ)/2 := by
    have h : (2 * rOf U t : ℝ) < q := by exact_mod_cast hr2
    linarith
  have hrnn : (0:ℝ) ≤ (rOf U t : ℝ) := by positivity
  have htnn : (0:ℝ) ≤ (t : ℝ) := by positivity
  have hprod : (rOf U t : ℝ) * t ≤ (q:ℝ)/2 * (5*M) := by
    have h1 : (rOf U t : ℝ) * t ≤ (q:ℝ)/2 * t := mul_le_mul_of_nonneg_right hrR.le htnn
    have h2 : (q:ℝ)/2 * t ≤ (q:ℝ)/2 * (5*M) := mul_le_mul_of_nonneg_left ht2 (by positivity)
    linarith
  have hqm : (q:ℝ) * (mOf q U t : ℝ) < (q:ℝ) * (3 * M) := by nlinarith [heqR, hprod, hqRpos, hMpos]
  exact lt_of_mul_lt_mul_left hqm hqRpos.le

theorem primepow_coprime_of_dvd {q ℓ b m : ℕ} (hℓ : ℓ.Prime) (hb : 0 < b)
    (hdvd : ℓ ^ b ∣ q * m + 1) : Nat.Coprime (ℓ ^ b) q := by
  have hℓnq : ¬ ℓ ∣ q := by
    intro hℓq
    have hℓdvd1 : ℓ ∣ q * m + 1 := (dvd_pow_self ℓ hb.ne').trans hdvd
    have hℓqm : ℓ ∣ q * m := hℓq.mul_right m
    have h1 : ℓ ∣ (q * m + 1 - q * m) := Nat.dvd_sub hℓdvd1 hℓqm
    have h2 : q * m + 1 - q * m = 1 := by omega
    rw [h2] at h1
    have hle : ℓ ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    have := hℓ.two_le
    omega
  exact (hℓ.coprime_iff_not_dvd.2 hℓnq).pow_left b

theorem rOf_pos {q U t : ℕ} (hUdvd : q ∣ U) (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    0 < rOf U t := by
  have heq := mOf_spec hUdvd hU1 hcop
  by_contra h
  push_neg at h
  have hr0 : rOf U t = 0 := by omega
  rw [hr0] at heq
  simp only [Nat.zero_mul] at heq
  omega

open Classical in
noncomputable def pkFiber (q U : ℕ) (T : Finset ℕ) (ℓ b : ℕ) : Finset ℕ :=
  T.filter (fun t => ℓ ^ b ∣ q * mOf q U t + 1)

open Classical in
noncomputable def noBigFactor (Dn : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.filter (fun t => ∀ ℓ, ℓ.Prime → ℓ ∣ t → ℓ ≤ Dn)

open Classical in
noncomputable def sieveBad2 (q U Dn : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (noBigFactor Dn T).filter (fun t => ¬ Powersmooth (q / 2) (q * mOf q U t + 1))

theorem pkFiber_card_le {q U ℓ b Mn : ℕ} (hUdvd : q ∣ U) (hU1 : 1 < U) (hℓ : ℓ.Prime)
    (hb : 0 < b) (T : Finset ℕ) (hTcop : ∀ t ∈ T, Nat.Coprime t U)
    (hMn : ∀ t ∈ T, mOf q U t < Mn) (hbig : Mn ≤ ℓ ^ b)
    (C δ : ℝ) (hdiv : ∀ n : ℕ, (q:ℝ) ≤ (n:ℝ) → (n:ℝ) ≤ (q:ℝ)^C → (n.divisors.card:ℝ) ≤ (q:ℝ)^δ)
    (hNle : (q:ℝ) * (Mn:ℝ) + 1 ≤ (q:ℝ)^C) (hq1 : 1 ≤ q) :
    ((pkFiber q U T ℓ b).card : ℝ) ≤ (q:ℝ)^δ := by
  rcases Finset.eq_empty_or_nonempty (pkFiber q U T ℓ b) with hemp | hne
  · rw [hemp]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨t0, ht0⟩ := hne
  have ht0' := ht0
  simp only [pkFiber, mem_filter] at ht0'
  obtain ⟨ht0T, ht0dvd⟩ := ht0'
  set m0 := mOf q U t0 with hm0def
  have hcop_u : Nat.Coprime (ℓ ^ b) q := primepow_coprime_of_dvd hℓ hb ht0dvd
  have hall : ∀ t ∈ pkFiber q U T ℓ b, mOf q U t = m0 := by
    intro t ht
    have ht' := ht
    simp only [pkFiber, mem_filter] at ht'
    obtain ⟨htT, htdvd⟩ := ht'
    have hm_t : mOf q U t < Mn := hMn t htT
    have hm_t0 : mOf q U t0 < Mn := hMn t0 ht0T
    have hlen : |((m0 : ℤ) - (mOf q U t : ℤ))| < ((ℓ ^ b : ℕ) : ℤ) := by
      have hb1 : (mOf q U t : ℤ) < (Mn:ℤ) := by exact_mod_cast hm_t
      have hb2 : (m0 : ℤ) < (Mn:ℤ) := by exact_mod_cast hm_t0
      have hb3 : (0:ℤ) ≤ (mOf q U t : ℤ) := by positivity
      have hb4 : (0:ℤ) ≤ (m0 : ℤ) := by positivity
      have hbigZ : (Mn:ℤ) ≤ ((ℓ ^ b : ℕ) : ℤ) := by exact_mod_cast hbig
      rw [abs_lt]
      omega
    exact unique_m_mod_u hcop_u htdvd ht0dvd hlen
  have hsub : pkFiber q U T ℓ b ⊆ (q * m0 + 1).divisors := by
    intro t ht
    have heqm : mOf q U t = m0 := hall t ht
    have ht' := ht
    simp only [pkFiber, mem_filter] at ht'
    obtain ⟨htT, _⟩ := ht'
    have hspec : q * mOf q U t + 1 = rOf U t * t := mOf_spec hUdvd hU1 (hTcop t htT)
    rw [heqm] at hspec
    rw [Nat.mem_divisors]
    exact ⟨⟨rOf U t, by rw [hspec]; ring⟩, by positivity⟩
  have hcardle : (pkFiber q U T ℓ b).card ≤ (q * m0 + 1).divisors.card := Finset.card_le_card hsub
  have hℓb2 : 2 ≤ ℓ ^ b := by
    have h1 : ℓ ≤ ℓ ^ b := by
      calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
        _ ≤ ℓ ^ b := Nat.pow_le_pow_right hℓ.one_lt.le hb
    exact le_trans hℓ.two_le h1
  have hqm0ge2 : 2 ≤ q * m0 + 1 := le_trans hℓb2 (Nat.le_of_dvd (by omega) ht0dvd)
  have hm0pos : 1 ≤ m0 := by
    rcases Nat.eq_zero_or_pos m0 with h0 | hpos
    · exfalso; rw [h0] at hqm0ge2; simp at hqm0ge2
    · exact hpos
  have hNq : (q:ℝ) ≤ ((q * m0 + 1 : ℕ):ℝ) := by
    push_cast
    have hm0R : (1:ℝ) ≤ (m0:ℝ) := by exact_mod_cast hm0pos
    have hqR : (0:ℝ) ≤ (q:ℝ) := by positivity
    nlinarith [hm0R, hqR]
  have hm0Mn : m0 < Mn := hMn t0 ht0T
  have hNq2 : ((q * m0 + 1 : ℕ):ℝ) ≤ (q:ℝ)^C := by
    push_cast
    have hle : (m0:ℝ) ≤ (Mn:ℝ) := by exact_mod_cast hm0Mn.le
    have hqR : (0:ℝ) ≤ (q:ℝ) := by positivity
    nlinarith [hNle, hle, hqR]
  have hτ := hdiv (q * m0 + 1) hNq hNq2
  calc ((pkFiber q U T ℓ b).card:ℝ) ≤ ((q * m0 + 1).divisors.card:ℝ) := by exact_mod_cast hcardle
    _ ≤ (q:ℝ)^δ := hτ

theorem sieveBad2_subset {q U Dn Bmax : ℕ} (hUdvd : q ∣ U) (hU1 : 1 < U)
    (T : Finset ℕ) (hTcop : ∀ t ∈ T, Nat.Coprime t U) (hTr2 : ∀ t ∈ T, 2 * rOf U t < q)
    (hBmax : ∀ t ∈ T, ∀ ℓ b, ℓ.Prime → 0 < b → ℓ ^ b ∣ q * mOf q U t + 1 → b ≤ Bmax) :
    sieveBad2 q U Dn T ⊆
      ((((Finset.Icc 2 Dn).filter Nat.Prime) ×ˢ (Finset.Icc 1 Bmax)).filter
          (fun p => q / 2 < p.1 ^ p.2)).biUnion
        (fun p => pkFiber q U T p.1 p.2) := by
  intro t ht
  simp only [sieveBad2, noBigFactor, mem_filter] at ht
  obtain ⟨⟨htT, hnobig⟩, hnp⟩ := ht
  unfold Powersmooth at hnp
  push_neg at hnp
  obtain ⟨ℓ, e, hℓ, he, hpe, hgt⟩ := hnp
  have hr0 : 0 < rOf U t := rOf_pos hUdvd hU1 (hTcop t htT)
  have heq : q * mOf q U t + 1 = rOf U t * t := mOf_spec hUdvd hU1 (hTcop t htT)
  have hpe' : ℓ ^ e ∣ rOf U t * t := heq ▸ hpe
  have hr2 : 2 * rOf U t < q := hTr2 t htT
  have hgt' : rOf U t < ℓ ^ e := by omega
  have hℓt : ℓ ∣ t := primepow_dvd_of_gt hℓ hr0 hgt' hpe'
  have hℓDn : ℓ ≤ Dn := hnobig ℓ hℓ hℓt
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have he1 : 1 ≤ e := he
  have heBmax : e ≤ Bmax := hBmax t htT ℓ e hℓ he hpe
  refine Finset.mem_biUnion.mpr ⟨(ℓ, e), ?_, ?_⟩
  · simp only [mem_filter, Finset.mem_product, mem_Icc]
    exact ⟨⟨⟨⟨hℓ2, hℓDn⟩, hℓ⟩, ⟨he1, heBmax⟩⟩, hgt⟩
  · simp only [pkFiber, mem_filter]
    exact ⟨htT, hpe⟩

theorem bad2_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (η : ℝ) (hη0 : 0 < η) (hηε : η < ε / 2) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ U : ℕ, q ∣ U → 1 < U → ∀ T : Finset ℕ,
      (∀ t ∈ T, Nat.Coprime t U) →
      (∀ t ∈ T, 4 * (q:ℝ)^ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 5 * (q:ℝ)^ε) →
      (∀ t ∈ T, 2 * rOf U t < q) →
      ((sieveBad2 q U ⌈(q:ℝ)^(ε - η)⌉₊ T).card : ℝ) ≤ κ * (q:ℝ)^ε := by
  intro κ hκ
  set δ : ℝ := η / 8 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hεη0 : 0 < ε - η := by linarith
  set K : ℝ := 4 / Real.log 2 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
  have hηδ0 : 0 < η - δ := by rw [hδdef]; linarith
  have htarget0 : 0 < κ / (2 * K) := by positivity
  filter_upwards [divisors_card_le_rpow 4 δ (by norm_num) hδ0,
      rpow_le_div_eventually ε hε1 6 (by norm_num),
      rpow_ge_eventually (ε - η) hεη0 1,
      log_mul_rpow_neg_le (η - δ) (κ / (2*K)) hηδ0 htarget0,
      eventually_ge_atTop 2]
    with q hdivbound hM6 hDge1 hlogbound hq2
  intro U hUdvd hU1 T hTcop hTt hTr2
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqRpos : (0:ℝ) < (q:ℝ) := by linarith
  set M : ℝ := (q:ℝ) ^ ε with hMdef
  set D : ℝ := (q:ℝ) ^ (ε - η) with hDdef
  set Dn : ℕ := ⌈D⌉₊ with hDndef
  have hMpos : 0 < M := by
    rw [hMdef]; exact Real.rpow_pos_of_pos hqRpos ε
  have hMleq : M ≤ (q:ℝ) := by
    rw [hMdef]
    have h := Real.rpow_le_rpow_of_exponent_le hqR1 hε1.le
    rwa [Real.rpow_one] at h
  -- Mn : a nat upper bound on mOf q U t for all t ∈ T
  set Mn : ℕ := ⌈3 * M⌉₊ with hMndef
  have hMnle : (Mn:ℝ) ≤ 3 * (q:ℝ) := by
    rw [hMndef]
    have hc : (3 * M : ℝ) ≤ ((3 * q : ℕ):ℝ) := by push_cast; linarith [hMleq]
    have hle := Nat.ceil_le.mpr hc
    have : (⌈3*M⌉₊ : ℝ) ≤ ((3*q:ℕ):ℝ) := by exact_mod_cast hle
    push_cast at this
    linarith [this]
  have hMn : ∀ t ∈ T, mOf q U t < Mn := by
    intro t htT
    have hb := mOf_bound hUdvd hU1 (hTcop t htT) M hMpos (hTt t htT).2 (hTr2 t htT)
    have hc : (mOf q U t : ℝ) < (Mn:ℝ) := by
      calc (mOf q U t : ℝ) < 3 * M := hb
        _ ≤ (Mn:ℝ) := Nat.le_ceil _
    exact_mod_cast hc
  have hNbound4 : (q:ℝ) * (Mn:ℝ) + 1 ≤ (q:ℝ)^4 := by
    have h1 : (q:ℝ) * (Mn:ℝ) ≤ (q:ℝ) * (3 * (q:ℝ)) :=
      mul_le_mul_of_nonneg_left hMnle (by linarith)
    have h2 : (q:ℝ) * (3 * (q:ℝ)) + 1 ≤ (q:ℝ)^4 := by
      have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
      nlinarith [hq2R, sq_nonneg ((q:ℝ) - 2), sq_nonneg ((q:ℝ)^2 - 2)]
    linarith [h1, h2]
  have hqpow4 : (q:ℝ)^(4:ℝ) = (q:ℝ)^(4:ℕ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hNbound4rpow : (q:ℝ) * (Mn:ℝ) + 1 ≤ (q:ℝ)^(4:ℝ) := by
    rw [hqpow4]; exact hNbound4
  have hq1 : 1 ≤ q := by omega
  -- Bmax : a nat upper bound on the exponent b for offending prime powers
  set Nbound : ℕ := q * Mn + 1 with hNbdef
  set Bmax : ℕ := Nat.log 2 Nbound with hBmaxdef
  have hBmaxR : (Bmax : ℝ) ≤ K * Real.log q := by
    have hNbpos : Nbound ≠ 0 := by rw [hNbdef]; omega
    have h1 : (2:ℕ) ^ Bmax ≤ Nbound := Nat.pow_log_le_self 2 hNbpos
    have h1R : ((2:ℕ)^Bmax : ℝ) ≤ (Nbound:ℝ) := by exact_mod_cast h1
    have h2R : (2:ℝ)^(Bmax:ℕ) = (2:ℝ)^(Bmax:ℝ) := by
      rw [← Real.rpow_natCast (2:ℝ) Bmax]
    have h3 : Real.log ((2:ℝ)^(Bmax:ℝ)) ≤ Real.log (Nbound:ℝ) := by
      apply Real.log_le_log (by positivity)
      rw [← h2R]; push_cast at h1R ⊢; exact h1R
    rw [Real.log_rpow (by norm_num)] at h3
    have hNbR : (Nbound:ℝ) ≤ (q:ℝ)^4 := by
      rw [hNbdef]; push_cast; linarith [hNbound4]
    have h4 : Real.log (Nbound:ℝ) ≤ Real.log ((q:ℝ)^4) := by
      apply Real.log_le_log (by positivity) hNbR
    rw [show ((q:ℝ)^4 : ℝ) = (q:ℝ)^(4:ℝ) by rw [← Real.rpow_natCast]; norm_num,
      Real.log_rpow hqRpos] at h4
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
    nlinarith [h3, h4]
  -- hBmax : the exponent bound needed for `sieveBad2_subset`
  have hBmax : ∀ t ∈ T, ∀ ℓ b, ℓ.Prime → 0 < b → ℓ ^ b ∣ q * mOf q U t + 1 → b ≤ Bmax := by
    intro t htT ℓ b hℓ hb hdvd
    have hmlt : mOf q U t < Mn := hMn t htT
    have hqm1 : q * mOf q U t + 1 ≤ Nbound := by
      rw [hNbdef]
      have : mOf q U t ≤ Mn - 1 := by omega
      calc q * mOf q U t + 1 ≤ q * (Mn - 1) + 1 := by
            have := Nat.mul_le_mul_left q this
            omega
        _ ≤ q * Mn + 1 := by
            have : q * (Mn-1) ≤ q * Mn := Nat.mul_le_mul_left q (by omega)
            omega
    have h2ble : (2:ℕ)^b ≤ ℓ^b := Nat.pow_le_pow_left hℓ.two_le b
    have hple : (2:ℕ)^b ≤ Nbound := le_trans h2ble (le_trans (Nat.le_of_dvd (by omega) hdvd) hqm1)
    have hNbne : Nbound ≠ 0 := by rw [hNbdef]; omega
    exact (Nat.le_log_iff_pow_le (by norm_num) hNbne).mpr hple
  have hcontain := sieveBad2_subset hUdvd hU1 T hTcop hTr2 hBmax (Dn := Dn)
  -- card bound via the containment + per-fiber bound
  set Grid' : Finset (ℕ × ℕ) :=
      ((((Finset.Icc 2 Dn).filter Nat.Prime) ×ˢ (Finset.Icc 1 Bmax)).filter
        (fun p => q / 2 < p.1 ^ p.2)) with hGrid'def
  have hfiberbound : ∀ p ∈ Grid', ((pkFiber q U T p.1 p.2).card : ℝ) ≤ (q:ℝ)^δ := by
    intro p hp
    rw [hGrid'def] at hp
    simp only [mem_filter, Finset.mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨⟨hℓ2, hℓDn⟩, hℓp⟩, ⟨hb1, hbBmax⟩⟩, hgt⟩ := hp
    have hbig : Mn ≤ p.1 ^ p.2 := by
      have h3M : 3 * M ≤ (q:ℝ) / 2 := by linarith [hM6]
      have hqlt : (q:ℝ) < 2 * ((p.1^p.2 : ℕ):ℝ) := by
        have : q < 2 * p.1^p.2 := by omega
        exact_mod_cast this
      have h3Mlt : 3 * M < ((p.1^p.2 : ℕ):ℝ) := by linarith [h3M, hqlt]
      have hceil : ⌈3 * M⌉₊ ≤ p.1^p.2 := Nat.ceil_le.mpr h3Mlt.le
      rw [hMndef]; exact hceil
    exact pkFiber_card_le hUdvd hU1 hℓp hb1 T hTcop hMn hbig (4:ℝ) δ hdivbound hNbound4rpow hq1
  have hcardsum : ((sieveBad2 q U Dn T).card : ℝ) ≤ ∑ p ∈ Grid', ((pkFiber q U T p.1 p.2).card : ℝ) := by
    have h1 : (sieveBad2 q U Dn T).card ≤ (Grid'.biUnion (fun p => pkFiber q U T p.1 p.2)).card :=
      Finset.card_le_card hcontain
    have h2 : (Grid'.biUnion (fun p => pkFiber q U T p.1 p.2)).card ≤
        ∑ p ∈ Grid', (pkFiber q U T p.1 p.2).card := Finset.card_biUnion_le
    calc ((sieveBad2 q U Dn T).card : ℝ)
        ≤ ((Grid'.biUnion (fun p => pkFiber q U T p.1 p.2)).card : ℝ) := by exact_mod_cast h1
      _ ≤ (∑ p ∈ Grid', (pkFiber q U T p.1 p.2).card : ℝ) := by exact_mod_cast h2
      _ = ∑ p ∈ Grid', ((pkFiber q U T p.1 p.2).card : ℝ) := by push_cast; ring
  have hsumbound : ∑ p ∈ Grid', ((pkFiber q U T p.1 p.2).card : ℝ) ≤ (Grid'.card : ℝ) * (q:ℝ)^δ := by
    calc ∑ p ∈ Grid', ((pkFiber q U T p.1 p.2).card : ℝ) ≤ ∑ p ∈ Grid', (q:ℝ)^δ :=
          Finset.sum_le_sum hfiberbound
      _ = (Grid'.card : ℝ) * (q:ℝ)^δ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hGridcard : Grid'.card ≤ Dn * Bmax := by
    rw [hGrid'def]
    calc (((((Finset.Icc 2 Dn).filter Nat.Prime) ×ˢ (Finset.Icc 1 Bmax)).filter
            (fun p => q / 2 < p.1 ^ p.2))).card
        ≤ (((Finset.Icc 2 Dn).filter Nat.Prime) ×ˢ (Finset.Icc 1 Bmax)).card :=
          Finset.card_filter_le _ _
      _ = ((Finset.Icc 2 Dn).filter Nat.Prime).card * (Finset.Icc 1 Bmax).card :=
          Finset.card_product _ _
      _ ≤ Dn * Bmax := by
          apply Nat.mul_le_mul
          · calc ((Finset.Icc 2 Dn).filter Nat.Prime).card ≤ (Finset.Icc 2 Dn).card :=
                  Finset.card_filter_le _ _
              _ = Dn - 1 := by rw [Nat.card_Icc]; omega
              _ ≤ Dn := by omega
          · rw [Nat.card_Icc]; omega
  have hDnR : (Dn:ℝ) ≤ 2 * D := by
    rw [hDndef]
    have h1 : (D:ℝ) ≤ (⌈D⌉₊:ℝ) := Nat.le_ceil _
    have h2 : (⌈D⌉₊:ℝ) < D + 1 := Nat.ceil_lt_add_one (by linarith [hDge1])
    linarith [hDge1]
  have hDnBmaxR : (Dn:ℝ) * (Bmax:ℝ) ≤ (2 * D) * (K * Real.log q) := by
    have hDnnn : (0:ℝ) ≤ (Dn:ℝ) := by positivity
    have hBmaxnn : (0:ℝ) ≤ (Bmax:ℝ) := by positivity
    calc (Dn:ℝ) * (Bmax:ℝ) ≤ (2*D) * (Bmax:ℝ) :=
          mul_le_mul_of_nonneg_right hDnR hBmaxnn
      _ ≤ (2*D) * (K * Real.log q) :=
          mul_le_mul_of_nonneg_left hBmaxR (by positivity [hDge1])
  have hfinal1 : ((sieveBad2 q U Dn T).card : ℝ) ≤ (2 * D) * (K * Real.log q) * (q:ℝ)^δ := by
    calc ((sieveBad2 q U Dn T).card : ℝ) ≤ (Grid'.card : ℝ) * (q:ℝ)^δ :=
          le_trans hcardsum hsumbound
      _ ≤ (Dn:ℝ) * (Bmax:ℝ) * (q:ℝ)^δ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hGridcard
      _ ≤ ((2*D) * (K * Real.log q)) * (q:ℝ)^δ :=
          mul_le_mul_of_nonneg_right hDnBmaxR (by positivity)
  have hDq : D * (q:ℝ)^δ = M / (q:ℝ)^(η-δ) := by
    rw [hDdef, hMdef, ← Real.rpow_add hqRpos]
    rw [eq_div_iff (by positivity : (q:ℝ)^(η-δ) ≠ 0)]
    rw [← Real.rpow_add hqRpos]
    congr 1
    ring
  have hfinal2 : (2 * D) * (K * Real.log q) * (q:ℝ)^δ = 2 * K * M * (Real.log q / (q:ℝ)^(η - δ)) := by
    have heq1 : (2*D)*(K*Real.log q)*(q:ℝ)^δ = 2*K*Real.log q*(D*(q:ℝ)^δ) := by ring
    rw [heq1, hDq]; ring
  have hfinal3 : 2 * K * M * (Real.log q / (q:ℝ)^(η - δ)) ≤ 2 * K * M * (κ / (2 * K)) := by
    apply mul_le_mul_of_nonneg_left hlogbound
    positivity
  have hfinal4 : 2 * K * M * (κ / (2 * K)) = κ * M := by field_simp
  calc ((sieveBad2 q U Dn T).card:ℝ) ≤ (2*D) * (K * Real.log q) * (q:ℝ)^δ := hfinal1
    _ = 2*K*M*(Real.log q/(q:ℝ)^(η-δ)) := hfinal2
    _ ≤ 2*K*M*(κ/(2*K)) := hfinal3
    _ = κ * M := hfinal4

end Erdos289
