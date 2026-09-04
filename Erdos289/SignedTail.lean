import Erdos289.SignedDefs
import Erdos289.Tail

/-!
# Signed correction fibers: tail estimates (displays (D4)-(D5))

Tail-mass estimates for the elementary replacement of Lemma 1 (`docs/elementary_replacements.md`,
Section 4). These mirror `Erdos289/Tail.lean`'s tail-sum technique at the exponent `-41/40`
(instead of `-21/20`), and combine it with the eventual smallness of the divisor envelope
`Eenv` (`Erdos289/SignedDefs.lean`) coming from the divisor bound.
-/

namespace Erdos289.SignedTail

open Finset Filter Real Topology

/-- A power `q ^ b` eventually dominates `C * q ^ a + D` when `a < b` (used to package
"for sufficiently large `q`" real-asymptotic estimates as a single rpow bound). -/
theorem eventually_rpow_dominates (a b C D : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a + D ≤ (q : ℝ) ^ b := by
  have h1 : Tendsto (fun q : ℕ => (q : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun q : ℕ => (q : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop (C + 1), h2.eventually_ge_atTop D,
    eventually_ge_atTop (1 : ℕ)] with q hq1 hq2 hq3
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqa_nn : (0 : ℝ) ≤ (q : ℝ) ^ a := Real.rpow_nonneg hqpos.le a
  have hsplit : (q : ℝ) ^ b = (q : ℝ) ^ a * (q : ℝ) ^ (b - a) := by
    rw [← Real.rpow_add hqpos]; ring_nf
  rw [hsplit]
  nlinarith

/-- `log q` is eventually dominated by `K * q ^ a` for any fixed `a > 0`, `K > 0`. -/
theorem eventually_log_le_rpow (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∀ᶠ q : ℕ in atTop, Real.log q ≤ K * (q : ℝ) ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).def hK
  have h2 : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h3 := h2.eventually h
  filter_upwards [h3, eventually_ge_atTop (1 : ℕ)] with q hq hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hrpow_nn : 0 ≤ (q : ℝ) ^ a := Real.rpow_nonneg hqpos.le a
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog_nn, abs_of_nonneg hrpow_nn] at hq

end Erdos289.SignedTail

namespace Erdos289

open Finset Filter Real Topology Erdos289.SignedTail

/-- Tail-sum estimate (D4)-companion: the sum of `n ^ (-41/40)` over `n ∈ (L, H]` is at most
`40 * L ^ (-1/40)`. Same proof as `sum_rpow_tail_le`, with antiderivative `40 x^{-1/40}`. -/
theorem sum_rpow_tail_le' (L H : ℕ) (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(41 : ℝ) / 40) ≤ 40 * (L : ℝ) ^ (-(1 : ℝ) / 40) := by
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  by_cases hLH : L ≤ H
  · have hf : AntitoneOn (fun x : ℝ => x ^ (-(41 : ℝ) / 40)) (Set.Icc (L : ℝ) (H : ℝ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hLpos hx.1) hxy (by norm_num)
    have hmain := AntitoneOn.sum_le_integral_Ico hLH hf
    have e1 : ∑ i ∈ Finset.Ico L H, ((i + 1 : ℕ) : ℝ) ^ (-(41 : ℝ) / 40)
        = ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(41 : ℝ) / 40) := by
      apply Finset.sum_nbij' (fun i => i + 1) (fun n => n - 1)
      · intro a ha; simp only [Finset.mem_Ico] at ha; simp only [Finset.mem_Ioc]; omega
      · intro a ha; simp only [Finset.mem_Ioc] at ha; simp only [Finset.mem_Ico]; omega
      · intro a _; omega
      · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
      · intro a _; rfl
    have h0 : (0 : ℝ) ∉ Set.uIcc (L : ℝ) (H : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hLH)]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith
    have hint : ∫ x in (L : ℝ)..(H : ℝ), x ^ (-(41 : ℝ) / 40)
        = 40 * ((L : ℝ) ^ (-(1 : ℝ) / 40) - (H : ℝ) ^ (-(1 : ℝ) / 40)) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      norm_num
      ring
    have hHnn : (0 : ℝ) ≤ (H : ℝ) ^ (-(1 : ℝ) / 40) := Real.rpow_nonneg (by positivity) _
    calc ∑ n ∈ Finset.Ioc L H, (n : ℝ) ^ (-(41 : ℝ) / 40)
        = ∑ i ∈ Finset.Ico L H, ((i + 1 : ℕ) : ℝ) ^ (-(41 : ℝ) / 40) := e1.symm
      _ ≤ ∫ x in (L : ℝ)..(H : ℝ), x ^ (-(41 : ℝ) / 40) := hmain
      _ = 40 * ((L : ℝ) ^ (-(1 : ℝ) / 40) - (H : ℝ) ^ (-(1 : ℝ) / 40)) := hint
      _ ≤ 40 * (L : ℝ) ^ (-(1 : ℝ) / 40) := by nlinarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

/-- The divisor envelope `Eenv ε q` is eventually at most any fixed power `q ^ η`, for fixed
`0 < ε < 1`. Combines the divisor bound (uniformly over `n ≤ ⌈25 q^{1+ε}⌉`, via the
`max n₀ (x ^ δ)` majorant technique) with `log q ≤ q ^ η` eventually. -/
theorem Eenv_le_eventually (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, Eenv ε q ≤ (q : ℝ) ^ η := by
  classical
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set θ : ℝ := η / 4 with hθ_def
  have hθpos : 0 < θ := by positivity
  set δ : ℝ := θ / (2 * (1 + ε)) with hδ_def
  have hδpos : 0 < δ := by positivity
  -- Divisor majorant `Dfun x = max n₀ (x ^ δ)`.
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (divisor_bound δ hδpos)
  obtain ⟨Dfun, hDval⟩ : ∃ f : ℝ → ℝ, ∀ x : ℝ, f x = max (n₀ : ℝ) (x ^ δ) :=
    ⟨_, fun _ => rfl⟩
  have hDmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → Dfun x ≤ Dfun y := by
    intro x y hx hxy
    rw [hDval, hDval]
    exact max_le_max le_rfl (Real.rpow_le_rpow hx hxy hδpos.le)
  have hDdiv : ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℝ)) ≤ Dfun (n : ℝ) := by
    intro n hn
    rw [hDval]
    rcases le_or_gt n₀ n with h | h
    · exact le_trans (hn₀ n h) (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      have h1 : ((n.divisors.card : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.card_divisors_le_self n
      have h2 : (n : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h.le
      linarith
  have hDnn : ∀ x : ℝ, 0 ≤ Dfun x := by
    intro x
    rw [hDval]
    exact le_trans (by positivity) (le_max_left (n₀ : ℝ) (x ^ δ))
  -- Pointwise bound on `Venv ε q` for `q ≥ 1`.
  have hVenv_pt : ∀ q : ℕ, 1 ≤ q →
      (Venv ε q : ℝ) ≤ (n₀ : ℝ) + (26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε)) := by
    intro q hq
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
    set W : ℕ := ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ with hW_def
    have hVenv_le : (Venv ε q : ℝ) ≤ Dfun (W : ℝ) := by
      have hb : Venv ε q ≤ ⌊Dfun (W : ℝ)⌋₊ := by
        show (Finset.Icc 1 W).sup (fun n => n.divisors.card) ≤ ⌊Dfun (W : ℝ)⌋₊
        apply Finset.sup_le
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnW : n ≤ W := (Finset.mem_Icc.mp hn).2
        have hle : (n.divisors.card : ℝ) ≤ Dfun (W : ℝ) :=
          le_trans (hDdiv n hn1) (hDmono n W (by positivity) (by exact_mod_cast hnW))
        exact Nat.le_floor hle
      calc (Venv ε q : ℝ) ≤ (⌊Dfun (W : ℝ)⌋₊ : ℝ) := by exact_mod_cast hb
        _ ≤ Dfun (W : ℝ) := Nat.floor_le (hDnn _)
    have hWle : (W : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hq1e : (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := by
      have h := Real.rpow_le_rpow (zero_le_one) hqR h1ε.le
      simpa using h
    have hWle2 : (W : ℝ) ≤ 26 * (q : ℝ) ^ (1 + ε) := by linarith
    have hDW : Dfun (W : ℝ) ≤ Dfun (26 * (q : ℝ) ^ (1 + ε)) :=
      hDmono W (26 * (q : ℝ) ^ (1 + ε)) (by positivity) hWle2
    have hDval26 : Dfun (26 * (q : ℝ) ^ (1 + ε)) = max (n₀ : ℝ) ((26 * (q : ℝ) ^ (1 + ε)) ^ δ) :=
      hDval _
    have hrw : (26 * (q : ℝ) ^ (1 + ε)) ^ δ = (26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hqpos.le]
      congr 2
      ring
    have hXnn : (0 : ℝ) ≤ (26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε)) := by positivity
    have hn0nn : (0 : ℝ) ≤ (n₀ : ℝ) := by positivity
    calc (Venv ε q : ℝ) ≤ Dfun (W : ℝ) := hVenv_le
      _ ≤ Dfun (26 * (q : ℝ) ^ (1 + ε)) := hDW
      _ = max (n₀ : ℝ) ((26 * (q : ℝ) ^ (1 + ε)) ^ δ) := hDval26
      _ = max (n₀ : ℝ) ((26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε))) := by rw [hrw]
      _ ≤ (n₀ : ℝ) + (26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε)) :=
          max_le (le_add_of_nonneg_right hXnn) (le_add_of_nonneg_left hn0nn)
  have h2ε : (2 * (1 + ε) : ℝ) ≠ 0 := by positivity
  have hδ1ε_eq : δ * (1 + ε) = θ / 2 := by
    rw [hδ_def]; field_simp
  have hδ1ε : δ * (1 + ε) < θ := by rw [hδ1ε_eq]; linarith
  have hVenv_dom :
      ∀ᶠ q : ℕ in atTop, (26 : ℝ) ^ δ * (q : ℝ) ^ (δ * (1 + ε)) + (n₀ : ℝ) ≤ (q : ℝ) ^ θ :=
    eventually_rpow_dominates (δ * (1 + ε)) θ ((26 : ℝ) ^ δ) (n₀ : ℝ)
      (mul_pos hδpos h1ε) hδ1ε
  have hVenv_ev : ∀ᶠ q : ℕ in atTop, (Venv ε q : ℝ) ≤ (q : ℝ) ^ θ := by
    filter_upwards [hVenv_dom, eventually_ge_atTop (1 : ℕ)] with q hdom hq1
    have hpt := hVenv_pt q hq1
    linarith
  have hlog_ev : ∀ᶠ q : ℕ in atTop, Real.log q ≤ (q : ℝ) ^ θ := by
    have h := eventually_log_le_rpow θ 1 hθpos (by norm_num)
    filter_upwards [h] with q hq
    simpa using hq
  filter_upwards [hVenv_ev, hlog_ev, eventually_ge_atTop (1 : ℕ)] with q hVenv hlog hq1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hVennn : (0 : ℝ) ≤ (Venv ε q : ℝ) := by positivity
  have hqθnn : (0 : ℝ) ≤ (q : ℝ) ^ θ := Real.rpow_nonneg hqpos.le θ
  have hsq : ((Venv ε q : ℝ)) ^ 2 ≤ ((q : ℝ) ^ θ) ^ 2 := by
    apply pow_le_pow_left₀ hVennn hVenv
  have hsq2 : ((q : ℝ) ^ θ) ^ 2 = (q : ℝ) ^ (2 * θ) := by
    rw [pow_two, ← Real.rpow_add hqpos]
    congr 1
    ring
  have hlognn : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR
  have hstep : Eenv ε q ≤ (q : ℝ) ^ (2 * θ) * (q : ℝ) ^ θ := by
    unfold Eenv
    calc (Venv ε q : ℝ) ^ 2 * Real.log q
        ≤ ((q : ℝ) ^ θ) ^ 2 * Real.log q := by
          apply mul_le_mul_of_nonneg_right hsq hlognn
      _ = (q : ℝ) ^ (2 * θ) * Real.log q := by rw [hsq2]
      _ ≤ (q : ℝ) ^ (2 * θ) * (q : ℝ) ^ θ := by
          apply mul_le_mul_of_nonneg_left hlog (by positivity)
  have hcomb : (q : ℝ) ^ (2 * θ) * (q : ℝ) ^ θ = (q : ℝ) ^ (3 * θ) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    ring
  have hfinal : (q : ℝ) ^ (3 * θ) ≤ (q : ℝ) ^ η := by
    apply Real.rpow_le_rpow_of_exponent_le hqR
    rw [hθ_def]; linarith
  calc Eenv ε q ≤ (q : ℝ) ^ (2 * θ) * (q : ℝ) ^ θ := hstep
    _ = (q : ℝ) ^ (3 * θ) := hcomb
    _ ≤ (q : ℝ) ^ η := hfinal

/-- Stage-mass bound for the signed construction (docs display (D4)): given
`Eenv (1/10) q ≤ q ^ (1/40)`, the total mass of `s q` correction pairs at label `q`, each
bounded by `3 * Eenv (1/10) q * q^(-11/10)`, is at most `3 * q^(-41/40)`. Uses
`s q = ⌊q^(1/20)⌋₊ ≤ q^(1/20)`. -/
theorem signed_stage_mass_le (q : ℕ) (hq : 1 ≤ q)
    (hE : Eenv (1 / 10) q ≤ (q : ℝ) ^ ((1 : ℝ) / 40)) :
    (s q : ℝ) * 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10)
      ≤ 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hs : (s q : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 20) := by
    unfold s
    exact Nat.floor_le (by positivity)
  have hEnn : 0 ≤ Eenv (1 / 10) q := by
    unfold Eenv
    have := Real.log_nonneg hqR
    positivity
  have hprod : (s q : ℝ) * Eenv (1 / 10) q
      ≤ (q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ ((1 : ℝ) / 40) :=
    mul_le_mul hs hE hEnn (by positivity)
  have hexp : (q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ ((1 : ℝ) / 40) * (q : ℝ) ^ (-(11 : ℝ) / 10)
      = (q : ℝ) ^ (-(41 : ℝ) / 40) := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    congr 1
    ring
  calc (s q : ℝ) * 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10)
      = 3 * ((s q : ℝ) * Eenv (1 / 10) q) * (q : ℝ) ^ (-(11 : ℝ) / 10) := by ring
    _ ≤ 3 * ((q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ ((1 : ℝ) / 40)) * (q : ℝ) ^ (-(11 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
    _ = 3 * ((q : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ^ ((1 : ℝ) / 40) * (q : ℝ) ^ (-(11 : ℝ) / 10)) := by
        ring
    _ = 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by rw [hexp]

/-- Total signed-correction mass estimate (docs display (D5)): summing the per-stage bound
`signed_stage_mass_le` over prime-power labels `q ∈ (L, H]` gives at most `120 * L^(-1/40)`. -/
theorem signed_total_mass_le (L H : ℕ) (hL : 1 ≤ L) :
    ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40)
      ≤ 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) := by
  have hIcc_eq : Finset.Icc (L + 1) H = Finset.Ioc L H := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  calc ∑ q ∈ (Finset.Icc (L + 1) H).filter IsPrimePow, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40)
      ≤ ∑ q ∈ Finset.Icc (L + 1) H, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro q _ _; positivity
    _ = ∑ q ∈ Finset.Ioc L H, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by rw [hIcc_eq]
    _ = 3 * ∑ q ∈ Finset.Ioc L H, (q : ℝ) ^ (-(41 : ℝ) / 40) := by rw [Finset.mul_sum]
    _ ≤ 3 * (40 * (L : ℝ) ^ (-(1 : ℝ) / 40)) := by
        apply mul_le_mul_of_nonneg_left (sum_rpow_tail_le' L H hL) (by norm_num)
    _ = 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) := by ring

/-- The total signed-correction mass `120 * L ^ (-1/40)` is eventually below any fixed `δ > 0`
(companion to (D5), used to choose `L` in the final assembly). -/
theorem eventually_mass_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℕ in atTop, 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < δ := by
  have hexp : (-(1 : ℝ) / 40) = -((1 : ℝ) / 40) := by ring
  have htend : Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 40)) atTop (nhds 0) := by
    rw [hexp]
    exact tendsto_rpow_neg_atTop (by norm_num)
  have htend2 : Tendsto (fun L : ℕ => (L : ℝ) ^ (-(1 : ℝ) / 40)) atTop (nhds 0) :=
    htend.comp tendsto_natCast_atTop_atTop
  have htend3 :
      Tendsto (fun L : ℕ => 120 * (L : ℝ) ^ (-(1 : ℝ) / 40)) atTop (nhds (120 * 0)) :=
    htend2.const_mul 120
  rw [mul_zero] at htend3
  exact htend3.eventually_lt_const hδ

end Erdos289
