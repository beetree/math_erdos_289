import Erdos289.SignedDefs
import Erdos289.Lemma4

open Finset Filter Topology Erdos289

namespace Erdos289.SignedD1G

/-! ## A. Real-analysis helpers -/

/-- `log t ≤ t ^ δ / δ` for every `δ > 0` and `t > 0`. -/
theorem log_le_rpow_div (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ t ^ δ / δ := by
  have h1 : Real.log (t ^ δ) ≤ t ^ δ - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht δ)
  rw [Real.log_rpow ht] at h1
  rw [le_div_iff₀ hδ]
  linarith

/-- A product `K * q^(-δ)` (`δ > 0` fixed) is eventually `≤` any fixed positive `c`. -/
theorem rpow_neg_mul_ev (δ : ℝ) (hδ : 0 < δ) (K c : ℝ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop, K * (q : ℝ) ^ (-δ) ≤ c := by
  have htend : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (nhds 0) := tendsto_rpow_neg_atTop hδ
  have htend2 : Tendsto (fun q : ℕ => (q : ℝ) ^ (-δ)) atTop (nhds 0) :=
    htend.comp tendsto_natCast_atTop_atTop
  have htend3 : Tendsto (fun q : ℕ => K * (q : ℝ) ^ (-δ)) atTop (nhds (K * 0)) :=
    htend2.const_mul K
  rw [mul_zero] at htend3
  exact htend3.eventually_le_const hc

/-- `K ≤ q ^ δ` eventually, for fixed `K` and `δ > 0`. -/
theorem const_le_rpow_ev (K δ : ℝ) (hδ : 0 < δ) : ∀ᶠ q : ℕ in atTop, K ≤ (q : ℝ) ^ δ := by
  have h : Tendsto (fun q : ℕ => (q : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop K

/-- `C ≤ log X` eventually. -/
theorem log_ge_ev (C : ℝ) : ∀ᶠ X : ℕ in atTop, C ≤ Real.log X :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

/-! ## B. The divisor envelope is `q^{o(1)}` -/

/-- The divisor envelope is at least `1` (it includes `τ(1) = 1`). -/
theorem one_le_Venv (ε : ℝ) (hε : 0 < ε) {q : ℕ} (hq : 1 ≤ q) : 1 ≤ Venv ε q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := Real.one_le_rpow hq1 (by linarith)
  have h25 : (1 : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε) := by linarith
  have hceil : (1 : ℝ) ≤ (⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ : ℝ) := h25.trans (Nat.le_ceil _)
  have hceil' : 1 ≤ ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ := by exact_mod_cast hceil
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ := by
    simp only [Finset.mem_Icc]; exact ⟨le_refl _, hceil'⟩
  have h := Finset.le_sup (f := fun n : ℕ => n.divisors.card) hmem
  simpa [Venv] using h

/-- The divisor envelope satisfies `V(q) ≤ q^ξ` eventually, for every `ξ > 0`. -/
theorem venv_le (ε : ℝ) (hε : 0 < ε) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ q : ℕ in atTop, (Venv ε q : ℝ) ≤ (q : ℝ) ^ ξ := by
  set δ : ℝ := ξ / (2 * (1 + ε)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (divisor_bound δ hδ)
  filter_upwards [eventually_ge_atTop 1, const_le_rpow_ev (N₀ : ℝ) ξ hξ,
    const_le_rpow_ev ((26 : ℝ) ^ δ) (ξ / 2) (by positivity)] with q hq1 hN hC
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := Real.one_le_rpow hq1R (by linarith)
  have hkey : ∀ n ∈ Finset.Icc 1 ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊,
      (n.divisors.card : ℝ) ≤ (q : ℝ) ^ ξ := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rcases Nat.lt_or_ge n N₀ with hlt | hge
    · calc (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n
        _ ≤ (N₀ : ℝ) := by exact_mod_cast hlt.le
        _ ≤ (q : ℝ) ^ ξ := hN
    · have hτ : (n.divisors.card : ℝ) ≤ (n : ℝ) ^ δ := hN₀ n hge
      have hnM : (n : ℝ) ≤ 26 * (q : ℝ) ^ (1 + ε) := by
        have h1 : (n : ℝ) ≤ (⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by exact_mod_cast hn.2
        have h2 : ((⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ : ℕ) : ℝ) < 25 * (q : ℝ) ^ (1 + ε) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        linarith [hpow, h1, h2]
      have h3 : (n : ℝ) ^ δ ≤ (26 * (q : ℝ) ^ (1 + ε)) ^ δ :=
        Real.rpow_le_rpow (by positivity) hnM hδ.le
      have hexp : (1 + ε) * δ = ξ / 2 := by rw [hδdef]; field_simp
      have h4 : (26 * (q : ℝ) ^ (1 + ε)) ^ δ = (26 : ℝ) ^ δ * (q : ℝ) ^ (ξ / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hq0.le, hexp]
      have h5 : (26 : ℝ) ^ δ * (q : ℝ) ^ (ξ / 2) ≤ (q : ℝ) ^ (ξ / 2) * (q : ℝ) ^ (ξ / 2) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      have h6 : (q : ℝ) ^ (ξ / 2) * (q : ℝ) ^ (ξ / 2) = (q : ℝ) ^ ξ := by
        rw [← Real.rpow_add hq0]; congr 1; ring
      calc (n.divisors.card : ℝ) ≤ (n : ℝ) ^ δ := hτ
        _ ≤ (26 * (q : ℝ) ^ (1 + ε)) ^ δ := h3
        _ = (26 : ℝ) ^ δ * (q : ℝ) ^ (ξ / 2) := h4
        _ ≤ (q : ℝ) ^ (ξ / 2) * (q : ℝ) ^ (ξ / 2) := h5
        _ = (q : ℝ) ^ ξ := h6
  have hsup : Venv ε q ≤ ⌊(q : ℝ) ^ ξ⌋₊ := by
    refine Finset.sup_le ?_
    intro n hn
    exact Nat.le_floor (hkey n hn)
  calc (Venv ε q : ℝ) ≤ (⌊(q : ℝ) ^ ξ⌋₊ : ℝ) := by exact_mod_cast hsup
    _ ≤ (q : ℝ) ^ ξ := Nat.floor_le (by positivity)

/-- `E(q) = V(q)^2 log q ≤ q^ζ` eventually, for every `ζ > 0`. -/
theorem eenv_le (ε : ℝ) (hε : 0 < ε) (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ q : ℕ in atTop, Eenv ε q ≤ (q : ℝ) ^ ζ := by
  filter_upwards [eventually_ge_atTop 1, venv_le ε hε (ζ / 4) (by positivity),
    const_le_rpow_ev (4 / ζ) (ζ / 4) (by positivity)] with q hq1 hV hL
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hVnn : (0 : ℝ) ≤ (Venv ε q : ℝ) := by positivity
  have hsq : (Venv ε q : ℝ) ^ 2 ≤ (q : ℝ) ^ (ζ / 2) := by
    have h1 : (Venv ε q : ℝ) ^ 2 ≤ ((q : ℝ) ^ (ζ / 4)) ^ 2 := by nlinarith [hV, hVnn]
    have h2 : ((q : ℝ) ^ (ζ / 4)) ^ 2 = (q : ℝ) ^ (ζ / 2) := by
      rw [sq, ← Real.rpow_add hq0]; congr 1; ring
    linarith [h1, h2.le, h2.ge]
  have hlog : Real.log q ≤ (q : ℝ) ^ (ζ / 2) := by
    have h1 : Real.log q ≤ (q : ℝ) ^ (ζ / 4) / (ζ / 4) := log_le_rpow_div (ζ / 4) (by positivity) hq0
    have h2 : (q : ℝ) ^ (ζ / 4) / (ζ / 4) = (4 / ζ) * (q : ℝ) ^ (ζ / 4) := by field_simp
    have h3 : (4 / ζ) * (q : ℝ) ^ (ζ / 4) ≤ (q : ℝ) ^ (ζ / 4) * (q : ℝ) ^ (ζ / 4) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    have h4 : (q : ℝ) ^ (ζ / 4) * (q : ℝ) ^ (ζ / 4) = (q : ℝ) ^ (ζ / 2) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  have hlognn : 0 ≤ Real.log q := Real.log_nonneg hq1R
  have hmul : (Venv ε q : ℝ) ^ 2 * Real.log q ≤ (q : ℝ) ^ (ζ / 2) * (q : ℝ) ^ (ζ / 2) :=
    mul_le_mul hsq hlog hlognn (by positivity)
  have hfin : (q : ℝ) ^ (ζ / 2) * (q : ℝ) ^ (ζ / 2) = (q : ℝ) ^ ζ := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  rw [Eenv]
  linarith [hmul, hfin.le, hfin.ge]

/-- For prime powers `q`, the lower multiplier bound `R(q)` is positive. -/
theorem Rq_pos (ε : ℝ) (hε : 0 < ε) {q : ℕ} (hq : 2 ≤ q) : 0 < Rq ε q := by
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hV : 1 ≤ Venv ε q := one_le_Venv ε hε (by omega)
  have hlog : 0 < Real.log q := Real.log_pos hq1R
  have hE : 0 < Eenv ε q := by rw [Eenv]; positivity
  rw [Rq]
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) hE

/-! ## C. Counting the higher prime powers -/

/-- The number of prime powers `p^a ≤ N` with `a ≥ 2` is at most `√N · log₂ N`.
(Extracted from the proof of `Erdos289.primePow_count_le`.) -/
theorem card_pp_notPrime_le (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card
      ≤ Nat.sqrt N * Nat.log 2 N := by
  classical
  set S2 : Finset ℕ := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) with hS2def
  have hkey : ∀ n ∈ S2, 2 ≤ n.minFac ∧ n.minFac ^ 2 ≤ N ∧ 2 ≤ Nat.log n.minFac n ∧
      Nat.log n.minFac n ≤ Nat.log 2 N ∧ n = n.minFac ^ (Nat.log n.minFac n) := by
    intro n hn
    simp only [hS2def, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hIPP, hnp⟩ := hn
    have hn2 : 2 ≤ n := hIPP.two_le
    have hmf : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
    obtain ⟨k, hklog, hkpos, heq⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hIPP
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso
        have hk1 : k = 1 := by omega
        subst hk1
        have hn1' : n = n.minFac := by simpa using heq
        exact hnp (by rw [hn1']; exact hmf)
      · exact h
    have hlogeq : Nat.log n.minFac n = k := by
      have h1 := congrArg (Nat.log n.minFac) heq
      rwa [Nat.log_pow hmf.one_lt] at h1
    refine ⟨hmf.two_le, ?_, ?_, ?_, ?_⟩
    · calc n.minFac ^ 2 ≤ n.minFac ^ k := Nat.pow_le_pow_right hmf.one_le hk2
        _ = n := heq.symm
        _ ≤ N := hnN
    · rw [hlogeq]; exact hk2
    · rw [hlogeq]
      calc k ≤ Nat.log 2 n := hklog
        _ ≤ Nat.log 2 N := Nat.log_mono_right hnN
    · rw [hlogeq]; exact heq
  set T : Finset (ℕ × ℕ) := (Finset.Icc 2 (Nat.sqrt N)) ×ˢ (Finset.Icc 2 (Nat.log 2 N)) with hTdef
  have hmaps : ∀ n ∈ S2, (n.minFac, Nat.log n.minFac n) ∈ T := by
    intro n hn
    obtain ⟨h1, h2, h3, h4, _⟩ := hkey n hn
    simp only [hTdef, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨h1, Nat.le_sqrt'.mpr h2⟩, h3, h4⟩
  have hinj : Set.InjOn (fun n => (n.minFac, Nat.log n.minFac n)) (S2 : Set ℕ) := by
    intro n1 hn1 n2 hn2 heq12
    obtain ⟨_, _, _, _, hval1⟩ := hkey n1 hn1
    obtain ⟨_, _, _, _, hval2⟩ := hkey n2 hn2
    have e1 : n1.minFac = n2.minFac := congrArg Prod.fst heq12
    have e2 : Nat.log n1.minFac n1 = Nat.log n2.minFac n2 := congrArg Prod.snd heq12
    calc n1 = n1.minFac ^ (Nat.log n1.minFac n1) := hval1
      _ = n2.minFac ^ (Nat.log n2.minFac n2) := by rw [e2, e1]
      _ = n2 := hval2.symm
  have hcard_le : S2.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun n => (n.minFac, Nat.log n.minFac n)) hmaps hinj
  have hIccle : ∀ m : ℕ, (Finset.Icc 2 m).card ≤ m := by
    intro m; rw [Nat.card_Icc]; omega
  have hTcard_le : T.card ≤ Nat.sqrt N * Nat.log 2 N := by
    rw [hTdef, Finset.card_product]
    exact Nat.mul_le_mul (hIccle _) (hIccle _)
  exact hcard_le.trans hTcard_le

/-- `Nat.sqrt N ≤ √N`. -/
theorem natSqrt_le_sqrt (N : ℕ) : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
  apply Real.le_sqrt_of_sq_le
  have := Nat.sqrt_le' N
  exact_mod_cast this

/-- `log₂ N · log 2 ≤ log N`. -/
theorem natLog2_mul_log_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h1 : (2 : ℕ) ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : (((2 : ℕ) ^ (Nat.log 2 N) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have h3 : Real.log (((2 : ℕ) ^ (Nat.log 2 N) : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by positivity) h2
  rwa [show (((2 : ℕ) ^ (Nat.log 2 N) : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 N) by push_cast; ring,
    Real.log_pow] at h3

/-- Bookkeeping: an endpoint `n ∈ [1, X]` of the triple `{k-1, k, k+1}` forces `k ≤ X + 1`. -/
theorem label_le_of_mem_triple (k n X : ℕ) (hk : 2 ≤ k) (hnX : n ≤ X)
    (h : n = k - 1 ∨ n = k ∨ n = k + 1) : k ≤ X + 1 := by omega


/-! ## D. Parameter definitions and algebraic relations -/

/-- The target ratio `t₀ = exp(κ / 36)`. -/
noncomputable def t0 (κ : ℝ) : ℝ := Real.exp (κ / 36)

/-- `1 < t₀`. -/
theorem t0_gt_one (κ : ℝ) (hκ : 0 < κ) : 1 < t0 κ := by
  have h := Real.add_one_le_exp (κ / 36)
  unfold t0; linarith

/-- The parameter `ζ > 0`. -/
noncomputable def zeta (ε κ : ℝ) : ℝ :=
  min (min (ε / 2) (1 / 8)) ((t0 κ - 1) * (1 + ε) / (6 * t0 κ))

theorem zeta_pos (ε : ℝ) (hε0 : 0 < ε) (κ : ℝ) (hκ : 0 < κ) : 0 < zeta ε κ := by
  have ht1 := t0_gt_one κ hκ
  have ht0 : 0 < t0 κ := by linarith
  unfold zeta
  refine lt_min (lt_min (by linarith) (by norm_num)) ?_
  exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)

theorem zeta_le_half_eps (ε κ : ℝ) : zeta ε κ ≤ ε / 2 :=
  le_trans (min_le_left _ _) (min_le_left _ _)

theorem zeta_le_eighth (ε κ : ℝ) : zeta ε κ ≤ 1 / 8 :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem zeta_le_ratio (ε κ : ℝ) : zeta ε κ ≤ (t0 κ - 1) * (1 + ε) / (6 * t0 κ) :=
  min_le_right _ _

/-- Exponent `a = (1 - ζ) / (1 + ε)`. -/
noncomputable def param_a (ε κ : ℝ) : ℝ := (1 - zeta ε κ) / (1 + ε)

/-- Exponent `b = 1 / (1 + ε - ζ)`. -/
noncomputable def param_b (ε κ : ℝ) : ℝ := 1 / (1 + ε - zeta ε κ)

/-- Exponent `γ = a - b / 2`. -/
noncomputable def param_gamma (ε κ : ℝ) : ℝ := param_a ε κ - param_b ε κ / 2

theorem param_a_pos (ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (κ : ℝ) (_hκ : 0 < κ) :
    0 < param_a ε κ := by
  have hz : zeta ε κ ≤ 1 / 8 := zeta_le_eighth ε κ
  unfold param_a
  exact div_pos (by linarith) (by linarith)

theorem param_b_pos (ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (κ : ℝ) (_hκ : 0 < κ) :
    0 < param_b ε κ := by
  have hz : zeta ε κ ≤ 1 / 8 := zeta_le_eighth ε κ
  unfold param_b
  exact div_pos one_pos (by linarith)

theorem param_b_le_one (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (κ : ℝ) (_hκ : 0 < κ) :
    param_b ε κ ≤ 1 := by
  have hz : zeta ε κ ≤ ε / 2 := zeta_le_half_eps ε κ
  have hden : 0 < 1 + ε - zeta ε κ := by linarith
  unfold param_b
  rw [div_le_one hden]
  linarith

theorem param_a_le_b (ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (κ : ℝ) (hκ : 0 < κ) :
    param_a ε κ ≤ param_b ε κ := by
  set z := zeta ε κ
  have hz0 : 0 < z := zeta_pos ε hε0 κ hκ
  have hz8 : z ≤ 1 / 8 := zeta_le_eighth ε κ
  have hden : 0 < 1 + ε - z := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  have hpos : 0 < (1 + ε) * (1 + ε - z) := mul_pos h1ε hden
  have e1 : param_a ε κ * ((1 + ε) * (1 + ε - z)) = (1 - z) * (1 + ε - z) := by
    unfold param_a
    rw [show ((1 - z) / (1 + ε)) * ((1 + ε) * (1 + ε - z)) =
        (((1 - z) / (1 + ε)) * (1 + ε)) * (1 + ε - z) by ring]
    rw [div_mul_cancel₀ (1 - z) h1ε.ne']
  have e2 : param_b ε κ * ((1 + ε) * (1 + ε - z)) = 1 + ε := by
    unfold param_b
    rw [show (1 / (1 + ε - z)) * ((1 + ε) * (1 + ε - z)) =
        (1 + ε) * ((1 / (1 + ε - z)) * (1 + ε - z)) by ring]
    rw [one_div_mul_cancel hden.ne', mul_one]
  have hkey : (1 - z) * (1 + ε - z) ≤ 1 + ε := by
    nlinarith [hz0.le, hε0, sq_nonneg z]
  rw [← mul_le_mul_iff_of_pos_right hpos, e1, e2]
  exact hkey

theorem param_gamma_pos (ε : ℝ) (hε0 : 0 < ε) (_hε1 : ε < 1) (κ : ℝ) (hκ : 0 < κ) :
    0 < param_gamma ε κ := by
  set z := zeta ε κ
  have hz0 : 0 < z := zeta_pos ε hε0 κ hκ
  have hz8 : z ≤ 1 / 8 := zeta_le_eighth ε κ
  have hden : 0 < 1 + ε - z := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  have hpos : 0 < (1 + ε) * (1 + ε - z) := mul_pos h1ε hden
  have e1 : (2 * param_a ε κ) * ((1 + ε) * (1 + ε - z)) = 2 * (1 - z) * (1 + ε - z) := by
    unfold param_a
    rw [show (2 * ((1 - z) / (1 + ε))) * ((1 + ε) * (1 + ε - z)) =
        2 * (((1 - z) / (1 + ε)) * (1 + ε)) * (1 + ε - z) by ring]
    rw [div_mul_cancel₀ (1 - z) h1ε.ne']
  have e2 : param_b ε κ * ((1 + ε) * (1 + ε - z)) = 1 + ε := by
    unfold param_b
    rw [show (1 / (1 + ε - z)) * ((1 + ε) * (1 + ε - z)) =
        (1 + ε) * ((1 / (1 + ε - z)) * (1 + ε - z)) by ring]
    rw [one_div_mul_cancel hden.ne', mul_one]
  have key : 1 + ε < 2 * (1 - z) * (1 + ε - z) := by
    nlinarith [hz0.le, hz8, hε0, _hε1, sq_nonneg z, mul_nonneg hz0.le hε0.le]
  have hlt : param_b ε κ < 2 * param_a ε κ := by
    rw [← mul_lt_mul_iff_of_pos_right hpos, e2, e1]
    exact key
  unfold param_gamma
  linarith

theorem param_b_lt_t0_mul_a (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (κ : ℝ) (hκ : 0 < κ) :
    param_b ε κ < t0 κ * param_a ε κ := by
  set t := t0 κ
  set z := zeta ε κ
  have ht0 : 0 < t := by
    have := t0_gt_one κ hκ
    linarith
  have hz0 : 0 < z := zeta_pos ε hε0 κ hκ
  have hzt : z ≤ (t - 1) * (1 + ε) / (6 * t) := zeta_le_ratio ε κ
  have hz8 : z ≤ 1 / 8 := zeta_le_eighth ε κ
  have hden : 0 < 1 + ε - z := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  have hpos : 0 < (1 + ε) * (1 + ε - z) := mul_pos h1ε hden
  have h6 : 6 * t * z ≤ (t - 1) * (1 + ε) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 6 * t)] at hzt
    linarith
  have hin : 0 ≤ (1 - z) * (1 + ε - z) - ((1 + ε) - 3 * z) := by
    nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hε1.le), sq_nonneg z]
  have hstep1 : t * ((1 + ε) - 3 * z) ≤ t * ((1 - z) * (1 + ε - z)) := by
    nlinarith [ht0.le, hin]
  have hstep2 : 1 + ε < t * ((1 + ε) - 3 * z) := by
    have ht1 : 0 < t - 1 := by linarith [t0_gt_one κ hκ]
    nlinarith [h6, mul_pos h1ε ht1]
  have key2 : 1 + ε < t * ((1 - z) * (1 + ε - z)) := lt_of_lt_of_le hstep2 hstep1
  have e1 : (t * param_a ε κ) * ((1 + ε) * (1 + ε - z)) = t * ((1 - z) * (1 + ε - z)) := by
    unfold param_a
    rw [show (t * ((1 - z) / (1 + ε))) * ((1 + ε) * (1 + ε - z)) =
        t * (((1 - z) / (1 + ε)) * (1 + ε)) * (1 + ε - z) by ring]
    rw [div_mul_cancel₀ (1 - z) h1ε.ne']
    ring
  have e2 : param_b ε κ * ((1 + ε) * (1 + ε - z)) = 1 + ε := by
    unfold param_b
    rw [show (1 / (1 + ε - z)) * ((1 + ε) * (1 + ε - z)) =
        (1 + ε) * ((1 / (1 + ε - z)) * (1 + ε - z)) by ring]
    rw [one_div_mul_cancel hden.ne', mul_one]
  rw [← mul_lt_mul_iff_of_pos_right hpos, e2, e1]
  exact key2


/-! ## E. The covering finset -/

/-- Multiplier cap for stage `q` and endpoint bound `X`: `cap q X = min ⌊8 q^ε⌋ ⌊(X+1)/q⌋`. -/
noncomputable def cap (ε : ℝ) (q X : ℕ) : ℕ := min ⌊8 * (q : ℝ) ^ ε⌋₊ ((X + 1) / q)

/-- The covering finset `Fcov` of possible endpoints in `[1, X]`. -/
noncomputable def Fcov (ε : ℝ) (Zn X : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 Zn).filter (fun q => IsPrimePow q)).biUnion
    (fun q => (Finset.Icc 1 (cap ε q X)).biUnion
      (fun m => ({q * m - 1, q * m, q * m + 1} : Finset ℕ)))

theorem cap_le_eight_rpow (ε : ℝ) (q X : ℕ) : (cap ε q X : ℝ) ≤ 8 * (q : ℝ) ^ ε := by
  have h1 : cap ε q X ≤ ⌊8 * (q : ℝ) ^ ε⌋₊ := min_le_left _ _
  calc (cap ε q X : ℝ) ≤ (⌊8 * (q : ℝ) ^ ε⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ 8 * (q : ℝ) ^ ε := Nat.floor_le (by positivity)

theorem cap_le_div (ε : ℝ) (q X : ℕ) (_hq : 0 < q) :
    (cap ε q X : ℝ) ≤ ((X : ℝ) + 1) / (q : ℝ) := by
  have h1 : cap ε q X ≤ (X + 1) / q := min_le_right _ _
  calc (cap ε q X : ℝ) ≤ (((X + 1) / q : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ ((X + 1 : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    _ = ((X : ℝ) + 1) / (q : ℝ) := by push_cast; ring

theorem card_triple_le (x y z : ℕ) : ({x, y, z} : Finset ℕ).card ≤ 3 := by
  have e1 := Finset.card_insert_le x ({y, z} : Finset ℕ)
  have e2 := Finset.card_insert_le y ({z} : Finset ℕ)
  have e3 : ({z} : Finset ℕ).card = 1 := Finset.card_singleton z
  omega

theorem card_inner_biUnion_le (ε : ℝ) (q X : ℕ) :
    ((Finset.Icc 1 (cap ε q X)).biUnion
      (fun m => ({q * m - 1, q * m, q * m + 1} : Finset ℕ))).card ≤ 3 * cap ε q X := by
  calc ((Finset.Icc 1 (cap ε q X)).biUnion
      (fun m => ({q * m - 1, q * m, q * m + 1} : Finset ℕ))).card
      ≤ ∑ m ∈ Finset.Icc 1 (cap ε q X), ({q * m - 1, q * m, q * m + 1} : Finset ℕ).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ Finset.Icc 1 (cap ε q X), 3 := Finset.sum_le_sum (fun m _ => card_triple_le _ _ _)
    _ = 3 * cap ε q X := by rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]; omega

theorem Fcov_card_le (ε : ℝ) (Zn X : ℕ) :
    (Fcov ε Zn X).card ≤
      ∑ q ∈ (Finset.Icc 1 Zn).filter (fun q => IsPrimePow q), 3 * cap ε q X := by
  unfold Fcov
  exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun q _ => card_inner_biUnion_le ε q X))

theorem q_le_pow_of_qm_le {q m : ℕ} (hq0 : (0 : ℝ) < (q : ℝ))
    {ε ζ b : ℝ} (hb0 : 0 < b) (hbe : (1 + ε - ζ) * b = 1)
    (hmge : (q : ℝ) ^ (ε - ζ) ≤ (m : ℝ)) {X : ℕ}
    (hqm : (q : ℝ) * (m : ℝ) ≤ (X : ℝ) + 1) :
    (q : ℝ) ≤ ((X : ℝ) + 1) ^ b := by
  have hq1εζ : (q : ℝ) ^ (1 + ε - ζ) ≤ (X : ℝ) + 1 := by
    have e : (q : ℝ) ^ (1 + ε - ζ) = (q : ℝ) * (q : ℝ) ^ (ε - ζ) := by
      rw [show (1 : ℝ) + ε - ζ = 1 + (ε - ζ) by ring, Real.rpow_add hq0, Real.rpow_one]
    rw [e]
    calc (q : ℝ) * (q : ℝ) ^ (ε - ζ) ≤ (q : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hmge hq0.le
      _ ≤ (X : ℝ) + 1 := hqm
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hq0.le _) hq1εζ hb0.le
  rwa [← Real.rpow_mul hq0.le, hbe, Real.rpow_one] at h1

theorem pstar_subset_Fcov (ε : ℝ) (hε0 : 0 < ε) (κ : ℝ) (L : ℕ) (X : ℕ)
    (q₁ : ℕ) (hq₁ : ∀ q, q₁ ≤ q → Eenv ε q ≤ (q : ℝ) ^ (zeta ε κ))
    (Zn : ℕ) (hZndef : Zn = ⌊((X : ℝ) + 1) ^ (param_b ε κ)⌋₊)
    (hq₁Z : q₁ ≤ Zn) (hb0 : 0 < param_b ε κ)
    (hbe : (1 + ε - zeta ε κ) * param_b ε κ = 1) :
    PstarSigned ε L ∩ Set.Icc 1 X ⊆ (Fcov ε Zn X : Set ℕ) := by
  rintro n ⟨⟨q, m, hIPP, _hLq, hm1, hm2, hn⟩, _hn1, hnX⟩
  have hq2 : 2 ≤ q := hIPP.two_le
  have hqpos : 0 < q := by omega
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hRpos : 0 < Rq ε q := Rq_pos ε hε0 hq2
  have hm0 : 1 ≤ m := by
    have h1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hRpos hm1
    have h2 : 0 < m := by exact_mod_cast h1
    omega
  have hqm2 : 2 ≤ q * m := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ q * m := Nat.mul_le_mul hq2 hm0
  have hqmX : q * m ≤ X + 1 := label_le_of_mem_triple (q * m) n X hqm2 hnX hn
  have hqmXR : (q : ℝ) * (m : ℝ) ≤ (X : ℝ) + 1 := by
    have h : ((q * m : ℕ) : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by exact_mod_cast hqmX
    push_cast at h; linarith
  have hqZ : q ≤ Zn := by
    rcases Nat.lt_or_ge q q₁ with hlt | hge
    · omega
    · have hE := hq₁ q hge
      have hEpos : 0 < Eenv ε q := by
        have hV : 1 ≤ Venv ε q := one_le_Venv ε hε0 (by omega)
        have hVR : (1 : ℝ) ≤ (Venv ε q : ℝ) := by exact_mod_cast hV
        have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
        rw [Eenv]; positivity
      have hdiv : (q : ℝ) ^ ε / (q : ℝ) ^ (zeta ε κ) ≤ (q : ℝ) ^ ε / Eenv ε q :=
        div_le_div_of_nonneg_left (by positivity) hEpos hE
      have hRge : (q : ℝ) ^ (ε - zeta ε κ) ≤ Rq ε q := by
        rw [Rq, Real.rpow_sub hq0R]; exact hdiv
      have hmge : (q : ℝ) ^ (ε - zeta ε κ) ≤ (m : ℝ) := le_trans hRge hm1
      have hqle := q_le_pow_of_qm_le hq0R hb0 hbe hmge hqmXR
      rw [hZndef]; exact Nat.le_floor hqle
  have hmcap : m ≤ cap ε q X := by
    unfold cap
    refine le_min (Nat.le_floor hm2) ?_
    exact (Nat.le_div_iff_mul_le hqpos).mpr (by rw [mul_comm]; exact hqmX)
  have hqmem : q ∈ (Finset.Icc 1 Zn).filter (fun q => IsPrimePow q) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hqpos, hqZ⟩, hIPP⟩
  unfold Fcov
  refine Finset.mem_biUnion.mpr ⟨q, hqmem, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨m, ?_, ?_⟩
  · simp only [Finset.mem_Icc]; exact ⟨hm0, hmcap⟩
  · rcases hn with h | h | h <;> simp [h]


/-! ## F. Sum bounds -/

theorem sum_split_Yn_Zn (f : ℕ → ℝ) (Yn Zn : ℕ) (hYZ : Yn ≤ Zn) :
    ∑ q ∈ (Finset.Icc 1 Zn).filter (fun q => IsPrimePow q), f q =
      (∑ q ∈ (Finset.Icc 1 Yn).filter (fun q => IsPrimePow q), f q) +
        ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), f q := by
  have hsplit : (Finset.Icc 1 Zn).filter (fun q => IsPrimePow q) =
      ((Finset.Icc 1 Yn).filter (fun q => IsPrimePow q)) ∪
      ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)) := by
    rw [← Finset.filter_union]
    congr 1
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint ((Finset.Icc 1 Yn).filter (fun q => IsPrimePow q))
      ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx'
    omega
  rw [hsplit, Finset.sum_union hdisj]

theorem sum_small_q_bound (ε κ : ℝ) (hε0 : 0 < ε) (hκ : 0 < κ) (X Yn : ℕ)
    (hX0 : (0 : ℝ) < (X : ℝ))
    (hYn_le : (Yn : ℝ) ≤ (X : ℝ) ^ (param_a ε κ))
    (hae : param_a ε κ * (1 + ε) = 1 - zeta ε κ)
    (h24 : 24 * (X : ℝ) ^ (-zeta ε κ) ≤ κ / 3) :
    ∑ q ∈ (Finset.Icc 1 Yn).filter (fun q => IsPrimePow q), 3 * (cap ε q X : ℝ) ≤ (κ / 3) * (X : ℝ) := by
  have hstep1 : ∑ q ∈ (Finset.Icc 1 Yn).filter (fun q => IsPrimePow q), 3 * (cap ε q X : ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 Yn, 3 * (cap ε q X : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _; positivity
  have hstep2 : ∑ q ∈ Finset.Icc 1 Yn, 3 * (cap ε q X : ℝ)
      ≤ ∑ _q ∈ Finset.Icc 1 Yn, 24 * (Yn : ℝ) ^ ε := by
    refine Finset.sum_le_sum ?_
    intro q hq
    simp only [Finset.mem_Icc] at hq
    have h1 : (cap ε q X : ℝ) ≤ 8 * (q : ℝ) ^ ε := cap_le_eight_rpow ε q X
    have h2 : (q : ℝ) ^ ε ≤ (Yn : ℝ) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq.2) hε0.le
    linarith
  have hcardIcc : (Finset.Icc 1 Yn).card = Yn := by rw [Nat.card_Icc]; omega
  have hstep3 : (∑ _q ∈ Finset.Icc 1 Yn, 24 * (Yn : ℝ) ^ ε) = (Yn : ℝ) * (24 * (Yn : ℝ) ^ ε) := by
    rw [Finset.sum_const, hcardIcc, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos Yn with rfl | hYnpos
  · simp at hstep1 hstep2 hstep3
    positivity
  · have hYnR : (0 : ℝ) < (Yn : ℝ) := by exact_mod_cast hYnpos
    have hstep4 : (Yn : ℝ) * (24 * (Yn : ℝ) ^ ε) = 24 * (Yn : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hYnR, Real.rpow_one]; ring
    have hstep5 : (Yn : ℝ) ^ (1 + ε) ≤ (X : ℝ) ^ (1 - zeta ε κ) := by
      have h2 : (Yn : ℝ) ^ (1 + ε) ≤ ((X : ℝ) ^ (param_a ε κ)) ^ (1 + ε) :=
        Real.rpow_le_rpow hYnR.le hYn_le (by linarith)
      rwa [← Real.rpow_mul hX0.le, hae] at h2
    have hstep6 : 24 * (X : ℝ) ^ (1 - zeta ε κ) ≤ (κ / 3) * (X : ℝ) := by
      have e : (X : ℝ) ^ (1 - zeta ε κ) = (X : ℝ) * (X : ℝ) ^ (-zeta ε κ) := by
        rw [show (1 : ℝ) - zeta ε κ = 1 + (-zeta ε κ) by ring, Real.rpow_add hX0, Real.rpow_one]
      rw [e]
      calc 24 * ((X : ℝ) * (X : ℝ) ^ (-zeta ε κ)) = (24 * (X : ℝ) ^ (-zeta ε κ)) * (X : ℝ) := by ring
        _ ≤ (κ / 3) * (X : ℝ) := mul_le_mul_of_nonneg_right h24 hX0.le
    linarith

theorem sum_large_q_le_recip (ε : ℝ) (X Yn Zn : ℕ) :
    ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 3 * (cap ε q X : ℝ) ≤
      3 * ((X : ℝ) + 1) *
        ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 1 / (q : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
  have hq0 : 0 < q := by omega
  have h := cap_le_div ε q X hq0
  rw [div_eq_mul_one_div] at h
  linarith

theorem sum_recip_split (Yn Zn : ℕ) :
    ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 1 / (q : ℝ) =
      (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ)) +
        ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ) :=
  (Finset.sum_filter_add_sum_filter_not _ (fun q => Nat.Prime q) _).symm

theorem sum_primes_bound (Yn Zn : ℕ) (κ : ℝ)
    (hgap : (∑ p ∈ (Finset.Ioc Yn Zn).filter Nat.Prime, (1 : ℝ) / p) ≤
      Real.log (Real.log (Zn : ℝ) / Real.log (Yn : ℝ)) + κ / 36)
    (hratio : Real.log (Zn : ℝ) / Real.log (Yn : ℝ) ≤ t0 κ)
    (hlogZpos : 0 < Real.log (Zn : ℝ)) (hlogYpos : 0 < Real.log (Yn : ℝ)) :
    ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ) ≤ κ / 18 := by
  have hsub2 : ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q) ⊆
      (Finset.Ioc Yn Zn).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  have h1 : ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ)
      ≤ ∑ p ∈ (Finset.Ioc Yn Zn).filter Nat.Prime, 1 / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub2 ?_
    intro i _ _; positivity
  have hpos : 0 < Real.log (Zn : ℝ) / Real.log (Yn : ℝ) := div_pos hlogZpos hlogYpos
  have h3 : Real.log (Real.log (Zn : ℝ) / Real.log (Yn : ℝ)) ≤ κ / 36 := by
    calc Real.log (Real.log (Zn : ℝ) / Real.log (Yn : ℝ)) ≤ Real.log (t0 κ) :=
          Real.log_le_log hpos hratio
      _ = κ / 36 := by unfold t0; rw [Real.log_exp]
  linarith [h1, hgap, h3]

theorem log_ratio_le_t0 (b a t0_val : ℝ) (hb0 : 0 ≤ b) (ht0 : 0 ≤ t0_val)
    {X Yn Zn : ℕ} (hlogY : 0 < Real.log (Yn : ℝ))
    (hlZ : Real.log (Zn : ℝ) ≤ b * Real.log ((X : ℝ) + 1))
    (hlY : a * Real.log X - Real.log 2 ≤ Real.log (Yn : ℝ))
    (hlX1 : Real.log ((X : ℝ) + 1) ≤ Real.log 2 + Real.log X)
    (hthr : (b + t0_val) * Real.log 2 ≤ (t0_val * a - b) * Real.log X) :
    Real.log (Zn : ℝ) / Real.log (Yn : ℝ) ≤ t0_val := by
  rw [div_le_iff₀ hlogY]
  have e1 : b * Real.log ((X : ℝ) + 1) ≤ b * (Real.log 2 + Real.log X) :=
    mul_le_mul_of_nonneg_left hlX1 hb0
  have e2 : t0_val * (a * Real.log X - Real.log 2) ≤ t0_val * Real.log (Yn : ℝ) :=
    mul_le_mul_of_nonneg_left hlY ht0
  linarith [hlZ, e1, e2, hthr]

theorem sum_higher_recip_le (Yn Zn : ℕ) (hYnR : (0 : ℝ) < (Yn : ℝ)) (hZnpos : 1 ≤ Zn) :
    ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ) ≤
      (Real.sqrt (Zn : ℝ) * (Real.log (Zn : ℝ) / Real.log 2)) * (1 / (Yn : ℝ)) := by
  set S := ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q)
  have hsub : S ⊆ (Finset.Icc 1 Zn).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨by omega, hx.1.1.2⟩, hx.1.2, hx.2⟩
  have hcard : S.card ≤ Nat.sqrt Zn * Nat.log 2 Zn :=
    le_trans (Finset.card_le_card hsub) (card_pp_notPrime_le Zn)
  have hterm : ∀ q ∈ S, 1 / (q : ℝ) ≤ 1 / (Yn : ℝ) := by
    intro q hq
    simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hq
    have h : (Yn : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1.1.1.le
    exact one_div_le_one_div_of_le hYnR h
  have h1 := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at h1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc1 : (S.card : ℝ) ≤ (Nat.sqrt Zn : ℝ) * (Nat.log 2 Zn : ℝ) := by exact_mod_cast hcard
  have hs : (Nat.sqrt Zn : ℝ) ≤ Real.sqrt (Zn : ℝ) := natSqrt_le_sqrt Zn
  have hl : (Nat.log 2 Zn : ℝ) ≤ Real.log (Zn : ℝ) / Real.log 2 := by
    have h := natLog2_mul_log_le Zn hZnpos
    rw [le_div_iff₀ hlog2]; linarith
  have h2 : (S.card : ℝ) ≤ Real.sqrt (Zn : ℝ) * (Real.log (Zn : ℝ) / Real.log 2) := by
    calc (S.card : ℝ) ≤ (Nat.sqrt Zn : ℝ) * (Nat.log 2 Zn : ℝ) := hc1
      _ ≤ Real.sqrt (Zn : ℝ) * (Real.log (Zn : ℝ) / Real.log 2) :=
          mul_le_mul hs hl (by positivity) (Real.sqrt_nonneg _)
  calc ∑ q ∈ S, 1 / (q : ℝ) ≤ (S.card : ℝ) * (1 / (Yn : ℝ)) := h1
    _ ≤ (Real.sqrt (Zn : ℝ) * (Real.log (Zn : ℝ) / Real.log 2)) * (1 / (Yn : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)



theorem sqrt_Zn_le {X Zn : ℕ} (hX0 : 0 < (X : ℝ)) (hX1 : 1 ≤ (X : ℝ))
    {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hZn_le : (Zn : ℝ) ≤ ((X : ℝ) + 1) ^ b) :
    Real.sqrt (Zn : ℝ) ≤ 2 * (X : ℝ) ^ (b / 2) := by
  have h2 : Real.sqrt (((X : ℝ) + 1) ^ b) = ((X : ℝ) + 1) ^ (b / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  have h5 : (2 : ℝ) ^ (b / 2) ≤ 2 := by
    calc (2 : ℝ) ^ (b / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc Real.sqrt (Zn : ℝ) ≤ Real.sqrt (((X : ℝ) + 1) ^ b) := Real.sqrt_le_sqrt hZn_le
    _ = ((X : ℝ) + 1) ^ (b / 2) := h2
    _ ≤ (2 * (X : ℝ)) ^ (b / 2) := Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    _ = (2 : ℝ) ^ (b / 2) * (X : ℝ) ^ (b / 2) := Real.mul_rpow (by norm_num) hX0.le
    _ ≤ 2 * (X : ℝ) ^ (b / 2) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hX0.le (b / 2))

theorem log_Zn_le {X Zn : ℕ} (hX2 : (2 : ℝ) ≤ (X : ℝ))
    {b : ℝ} (_hb0 : 0 < b) (hb1 : b ≤ 1)
    (hlZ : Real.log (Zn : ℝ) ≤ b * Real.log ((X : ℝ) + 1))
    (hlX1 : Real.log ((X : ℝ) + 1) ≤ Real.log 2 + Real.log X) :
    Real.log (Zn : ℝ) ≤ 2 * Real.log X := by
  have h3 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlog2le : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  calc Real.log (Zn : ℝ) ≤ b * Real.log ((X : ℝ) + 1) := hlZ
    _ ≤ 1 * Real.log ((X : ℝ) + 1) := mul_le_mul_of_nonneg_right hb1 h3
    _ = Real.log ((X : ℝ) + 1) := one_mul _
    _ ≤ Real.log 2 + Real.log X := hlX1
    _ ≤ 2 * Real.log X := by linarith

theorem inv_Yn_le {X Yn : ℕ} {a : ℝ} (hYn_ge : (X : ℝ) ^ a / 2 ≤ (Yn : ℝ))
    (hpos : 0 < (X : ℝ) ^ a / 2) :
    1 / (Yn : ℝ) ≤ 2 / (X : ℝ) ^ a := by
  have h := one_div_le_one_div_of_le hpos hYn_ge
  rwa [one_div_div] at h

theorem higher_product_bound (γ b a : ℝ) (hγdef : γ = a - b / 2) (hγ0 : 0 < γ)
    (X : ℝ) (hX0 : 0 < X)
    {sqrtZ logZ invY : ℝ}
    (hsqrtZ : sqrtZ ≤ 2 * X ^ (b / 2)) (_hsqrtZnn : 0 ≤ sqrtZ)
    (hlogZ : logZ ≤ 2 * Real.log X) (hlogZnn : 0 ≤ logZ)
    (hinvY : invY ≤ 2 / X ^ a) (hinvYnn : 0 ≤ invY)
    (hlog2 : 0 < Real.log 2) :
    (sqrtZ * (logZ / Real.log 2)) * invY ≤ (16 / (γ * Real.log 2)) * X ^ (-(γ / 2)) := by
  have hlogbd : Real.log X ≤ (2 / γ) * X ^ (γ / 2) := by
    have h := log_le_rpow_div (γ / 2) (by positivity) hX0
    have e : X ^ (γ / 2) / (γ / 2) = (2 / γ) * X ^ (γ / 2) := by field_simp
    linarith [h, e.le, e.ge]
  have hdiv2 : logZ / Real.log 2 ≤ (2 * Real.log X) / Real.log 2 := by
    exact div_le_div_of_nonneg_right hlogZ hlog2.le
  have hstep1 : sqrtZ * (logZ / Real.log 2) ≤ (2 * X ^ (b / 2)) * ((2 * Real.log X) / Real.log 2) :=
    mul_le_mul hsqrtZ hdiv2 (div_nonneg hlogZnn hlog2.le) (by positivity)
  have hnn : 0 ≤ ((2 * X ^ (b / 2)) * ((2 * Real.log X) / Real.log 2)) := by
    have : 0 ≤ (2 * Real.log X) / Real.log 2 := div_nonneg (by linarith [hlogZnn, hlogZ]) hlog2.le
    positivity
  have hstep2 : (sqrtZ * (logZ / Real.log 2)) * invY ≤
      ((2 * X ^ (b / 2)) * ((2 * Real.log X) / Real.log 2)) * (2 / X ^ a) :=
    mul_le_mul hstep1 hinvY hinvYnn hnn
  have halg : ((2 * X ^ (b / 2)) * ((2 * Real.log X) / Real.log 2)) * (2 / X ^ a) =
      (8 / Real.log 2) * ((X ^ (b / 2) / X ^ a) * Real.log X) := by field_simp; ring
  have hpow : X ^ (b / 2) / X ^ a = X ^ (-γ) := by
    rw [← Real.rpow_sub hX0]; congr 1; rw [hγdef]; ring
  have hprod : X ^ (-γ) * X ^ (γ / 2) = X ^ (-(γ / 2)) := by
    rw [← Real.rpow_add hX0]; congr 1; ring
  have hfin : (8 / Real.log 2) * (X ^ (-γ) * Real.log X) ≤ (16 / (γ * Real.log 2)) * X ^ (-(γ / 2)) := by
    calc (8 / Real.log 2) * (X ^ (-γ) * Real.log X)
        ≤ (8 / Real.log 2) * (X ^ (-γ) * ((2 / γ) * X ^ (γ / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left hlogbd (by positivity)
      _ = (16 / (γ * Real.log 2)) * (X ^ (-γ) * X ^ (γ / 2)) := by field_simp; ring
      _ = (16 / (γ * Real.log 2)) * X ^ (-(γ / 2)) := by rw [hprod]
  calc (sqrtZ * (logZ / Real.log 2)) * invY
      ≤ ((2 * X ^ (b / 2)) * ((2 * Real.log X) / Real.log 2)) * (2 / X ^ a) := hstep2
    _ = (8 / Real.log 2) * (X ^ (-γ) * Real.log X) := by rw [halg, hpow]
    _ ≤ (16 / (γ * Real.log 2)) * X ^ (-(γ / 2)) := hfin

theorem sum_large_q_bound (X : ℕ) (κ : ℝ) {C_gam : ℝ} (_hC_gam : 0 < C_gam)
    {Yn Zn : ℕ} (hXpos : 0 < (X : ℝ)) (hX1_le : 3 * ((X : ℝ) + 1) ≤ 6 * (X : ℝ))
    (hPBsplit : ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 1 / (q : ℝ) =
      (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ)) +
        ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ))
    (hprimes : ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ) ≤ κ / 18)
    (hhigher2 : ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ) ≤
      (16 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2)))
    (h96 : (96 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2)) ≤ κ / 3) :
    3 * ((X : ℝ) + 1) * (∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 1 / (q : ℝ)) ≤ (2 * κ / 3) * (X : ℝ) := by
  have hSPnn : 0 ≤ ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hSHnn : 0 ≤ ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hP1 : 3 * ((X : ℝ) + 1) * (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ))
      ≤ (κ / 3) * (X : ℝ) := by
    calc 3 * ((X : ℝ) + 1) * (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => Nat.Prime q), 1 / (q : ℝ))
        ≤ 6 * (X : ℝ) * (κ / 18) := mul_le_mul hX1_le hprimes hSPnn (by positivity)
      _ = (κ / 3) * (X : ℝ) := by ring
  have hP2 : 3 * ((X : ℝ) + 1) * (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ))
      ≤ (κ / 3) * (X : ℝ) := by
    have hstep : 3 * ((X : ℝ) + 1) * (∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ))
        ≤ 6 * (X : ℝ) * ((16 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2))) :=
      mul_le_mul hX1_le hhigher2 hSHnn (by positivity)
    have h : 6 * (X : ℝ) * ((16 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2))) =
        (X : ℝ) * ((96 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2))) := by ring
    have h2 : (X : ℝ) * ((96 / (C_gam * Real.log 2)) * (X : ℝ) ^ (-(C_gam / 2))) ≤ (X : ℝ) * (κ / 3) :=
      mul_le_mul_of_nonneg_left h96 hXpos.le
    linarith [hstep, h, h2]
  rw [hPBsplit, mul_add]
  linarith [hP1, hP2]



theorem param_b_mul_cancel (ε : ℝ) (hε0 : 0 < ε) (κ : ℝ) : (1 + ε - zeta ε κ) * param_b ε κ = 1 := by
  have hden : 0 < 1 + ε - zeta ε κ := by
    have hz8 : zeta ε κ ≤ 1 / 8 := zeta_le_eighth ε κ
    linarith
  unfold param_b
  rw [show (1 + ε - zeta ε κ) * (1 / (1 + ε - zeta ε κ)) = (1 + ε - zeta ε κ) / (1 + ε - zeta ε κ) by ring]
  exact div_self hden.ne'

theorem param_a_mul_cancel (ε : ℝ) (hε0 : 0 < ε) (κ : ℝ) : param_a ε κ * (1 + ε) = 1 - zeta ε κ := by
  have h1ε : 0 < 1 + ε := by linarith
  unfold param_a
  rw [show ((1 - zeta ε κ) / (1 + ε)) * (1 + ε) = ((1 - zeta ε κ) * (1 + ε)) / (1 + ε) by ring]
  exact mul_div_cancel_right₀ (1 - zeta ε κ) h1ε.ne'

/-! ## G. Lemma D1 -/

/-- **Lemma D1** (`docs/elementary_replacements.md`, Section 3, display (D2)): the enlarged
deterministic set of possible signed correction endpoints has density zero. -/
theorem lemmaD1G (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (L : ℕ) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ X : ℕ in Filter.atTop,
      ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * X := by
  intro κ hκ
  set a := param_a ε κ
  set b := param_b ε κ
  set γ := param_gamma ε κ
  set z := zeta ε κ
  set t := t0 κ
  have ha0 : 0 < a := param_a_pos ε hε0 hε1 κ hκ
  have hb0 : 0 < b := param_b_pos ε hε0 hε1 κ hκ
  have hb1 : b ≤ 1 := param_b_le_one ε hε0 hε1 κ hκ
  have hab : a ≤ b := param_a_le_b ε hε0 hε1 κ hκ
  have hγ0 : 0 < γ := param_gamma_pos ε hε0 hε1 κ hκ
  have hta : b < t * a := param_b_lt_t0_mul_a ε hε0 hε1 κ hκ
  have hz0 : 0 < z := zeta_pos ε hε0 κ hκ
  have ht0 : 0 < t := by
    have := t0_gt_one κ hκ
    linarith
  have hbe : (1 + ε - z) * b = 1 := param_b_mul_cancel ε hε0 κ
  have hae : a * (1 + ε) = 1 - z := param_a_mul_cancel ε hε0 κ
  obtain ⟨X₁, hX₁2, hgap⟩ := mertens_gap (κ / 36) (by positivity)
  obtain ⟨q₁, hq₁⟩ := eventually_atTop.1 (eenv_le ε hε0 z hz0)
  filter_upwards [eventually_ge_atTop 2,
    const_le_rpow_ev (X₁ : ℝ) a ha0,
    const_le_rpow_ev (q₁ : ℝ) b hb0,
    rpow_neg_mul_ev z hz0 24 (κ / 3) (by positivity),
    rpow_neg_mul_ev (γ / 2) (by positivity) (96 / (γ * Real.log 2)) (κ / 3) (by positivity),
    log_ge_ev ((b + t) * Real.log 2 / (t * a - b))] with
    X hX2 hXa hXb h24 h96 hlogX
  have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by linarith
  have hX1le : (X : ℝ) ≤ (X : ℝ) + 1 := by linarith
  have hXab : (X : ℝ) ^ a ≤ ((X : ℝ) + 1) ^ b :=
    (Real.rpow_le_rpow_of_exponent_le hX1R hab).trans (Real.rpow_le_rpow hX0.le hX1le hb0.le)
  set Yn : ℕ := ⌊(X : ℝ) ^ a⌋₊ with hYndef
  set Zn : ℕ := ⌊((X : ℝ) + 1) ^ b⌋₊ with hZndef
  have hYZ : Yn ≤ Zn := Nat.floor_mono hXab
  have hX₁Y : X₁ ≤ Yn := by rw [hYndef]; exact Nat.le_floor hXa
  have hYn2 : 2 ≤ Yn := le_trans hX₁2 hX₁Y
  have hZn2 : 2 ≤ Zn := le_trans hYn2 hYZ
  have hq₁Z : q₁ ≤ Zn := by
    rw [hZndef]
    exact Nat.le_floor (le_trans hXb (Real.rpow_le_rpow hX0.le hX1le hb0.le))
  have hYnR : (0 : ℝ) < (Yn : ℝ) := by exact_mod_cast (by omega : 0 < Yn)
  have hZnR : (0 : ℝ) < (Zn : ℝ) := by exact_mod_cast (by omega : 0 < Zn)
  have hZn_le : (Zn : ℝ) ≤ ((X : ℝ) + 1) ^ b := Nat.floor_le (by positivity)
  have hYn_le : (Yn : ℝ) ≤ (X : ℝ) ^ a := Nat.floor_le (by positivity)
  have hXa2 : (2 : ℝ) ≤ (X : ℝ) ^ a := le_trans (by exact_mod_cast hX₁2) hXa
  have hYn_ge : (X : ℝ) ^ a / 2 ≤ (Yn : ℝ) := by
    have h : (X : ℝ) ^ a < (Yn : ℝ) + 1 := by
      rw [hYndef]; exact_mod_cast Nat.lt_floor_add_one ((X : ℝ) ^ a)
    linarith [h, hXa2]
  have hlogY : 0 < Real.log (Yn : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Yn))
  have hlogZ : 0 < Real.log (Zn : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Zn))
  have hlZ : Real.log (Zn : ℝ) ≤ b * Real.log ((X : ℝ) + 1) := by
    have h := Real.log_le_log hZnR hZn_le
    rwa [Real.log_rpow (by linarith)] at h
  have hlY : a * Real.log X - Real.log 2 ≤ Real.log (Yn : ℝ) := by
    have h := Real.log_le_log (by positivity) hYn_ge
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_rpow hX0] at h
  have hlX1 : Real.log ((X : ℝ) + 1) ≤ Real.log 2 + Real.log X := by
    have h := Real.log_le_log (by linarith) (by linarith : (X : ℝ) + 1 ≤ 2 * (X : ℝ))
    rwa [Real.log_mul (by norm_num) (by linarith)] at h
  have hsub : PstarSigned ε L ∩ Set.Icc 1 X ⊆ (Fcov ε Zn X : Set ℕ) :=
    pstar_subset_Fcov ε hε0 κ L X q₁ hq₁ Zn rfl hq₁Z hb0 hbe
  have hncard : ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ (Fcov ε Zn X).card := by
    have hle : (PstarSigned ε L ∩ Set.Icc 1 X).ncard ≤ (Fcov ε Zn X).card := by
      have h := Set.ncard_le_ncard hsub (Fcov ε Zn X).finite_toSet
      rwa [Set.ncard_coe_finset] at h
    exact_mod_cast hle
  have hFcard : ((Fcov ε Zn X).card : ℝ) ≤
      ∑ q ∈ (Finset.Icc 1 Zn).filter (fun q => IsPrimePow q), 3 * (cap ε q X : ℝ) := by
    have h := Fcov_card_le ε Zn X
    exact_mod_cast h
  have hsumsplit := sum_split_Yn_Zn (fun q => 3 * (cap ε q X : ℝ)) Yn Zn hYZ
  have hA := sum_small_q_bound ε κ hε0 hκ X Yn hX0 hYn_le hae h24
  have hthr : (b + t) * Real.log 2 ≤ (t * a - b) * Real.log X := by
    have hd : (0 : ℝ) < t * a - b := by linarith
    rw [div_le_iff₀ hd] at hlogX
    linarith
  have hratio : Real.log (Zn : ℝ) / Real.log (Yn : ℝ) ≤ t :=
    log_ratio_le_t0 b a t hb0.le ht0.le hlogY hlZ hlY hlX1 hthr
  have hgap_inst := hgap Yn Zn hX₁Y hYZ
  have hprimes := sum_primes_bound Yn Zn κ hgap_inst hratio hlogZ hlogY
  have hsqZ := sqrt_Zn_le hX0 hX1R hb0 hb1 hZn_le
  have hlogZle := log_Zn_le hX2R hb0 hb1 hlZ hlX1
  have hYinv := inv_Yn_le hYn_ge (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod := higher_product_bound γ b a rfl hγ0 (X : ℝ) hX0 hsqZ (Real.sqrt_nonneg _) hlogZle hlogZ.le hYinv (by positivity) hlog2
  have hsum_high := sum_higher_recip_le Yn Zn hYnR (by omega)
  have hhigher2 : ∑ q ∈ ((Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q)).filter (fun q => ¬ Nat.Prime q), 1 / (q : ℝ) ≤
      (16 / (γ * Real.log 2)) * (X : ℝ) ^ (-(γ / 2)) :=
    le_trans hsum_high hprod
  have hX1_le : 3 * ((X : ℝ) + 1) ≤ 6 * (X : ℝ) := by linarith
  have hPBsplit := sum_recip_split Yn Zn
  have hB := sum_large_q_bound X κ hγ0 hX0 hX1_le hPBsplit hprimes hhigher2 h96
  have hBrecip := sum_large_q_le_recip ε X Yn Zn
  have hBtot : ∑ q ∈ (Finset.Ioc Yn Zn).filter (fun q => IsPrimePow q), 3 * (cap ε q X : ℝ) ≤ (2 * κ / 3) * (X : ℝ) :=
    le_trans hBrecip hB
  linarith [hncard, hFcard, hsumsplit, hA, hBtot]


end Erdos289.SignedD1G

namespace Erdos289

/-- **Lemma D1** (docs Section 3): the enlarged endpoint set has density zero. -/
theorem lemmaD1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (L : ℕ) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ X : ℕ in Filter.atTop,
      ((PstarSigned ε L ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * X :=
  SignedD1G.lemmaD1G ε hε0 hε1 L

#print axioms lemmaD1

end Erdos289
