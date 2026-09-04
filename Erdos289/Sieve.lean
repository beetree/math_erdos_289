import Erdos289.Lemma4
import Erdos289.ExternalBridge

/-!
# Sieve helpers for the signed construction

Arithmetic and analytic lemmas about the factorization `q * m + 1 = r * t` (via modular
inverses `rOf`/`mOf`) and the powersmoothness sieve (`bigPrimeFactor`), used by
`Erdos289/SignedF1.lean`. Extracted verbatim from the retired `Lemma1Basic.lean` / `Lemma1.lean`
/ `Lemma1OddCount.lean` (the equidistribution-based even/odd case counts and the final assembly
`lemma1` are not needed by the signed construction and are not reproduced here).
-/

set_option maxHeartbeats 1000000

namespace Erdos289

open Finset Filter Topology

/-! ## Setup: the factorization `q*m+1 = r*t` via modular inverses -/

/-- The companion `r`-value for `t` at modulus `U`: the canonical representative in `[0, U)`
of `t⁻¹ mod U`. -/

def rOf (U t : ℕ) : ℕ := ((t : ZMod U)⁻¹).val

/-- The `m`-value produced by the factorization `q * m + 1 = rOf U t * t`. Only meaningful
(and only used below) when `U` is a multiple of `q` and `t` is coprime to `U`, in which case
`mOf_spec` shows the defining equation actually holds. -/
def mOf (q U t : ℕ) : ℕ := (rOf U t * t - 1) / q

/-- The defining equation for `mOf`: whenever `U` is a positive multiple of `q` and `t` is
coprime to `U`, `q * mOf q U t + 1 = rOf U t * t`. This is what turns `t` (together with the
modulus `U`) into a genuine factorization `qm+1 = rt` as in the paper's display (2.1). -/
theorem mOf_spec {q U t : ℕ} (hU : q ∣ U) (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    q * mOf q U t + 1 = rOf U t * t := by
  have hval : ((rOf U t * t : ℕ) : ZMod U) = ((1 : ℕ) : ZMod U) := by
    push_cast; exact ZMod.val_inv_mul hcop
  have hmod : rOf U t * t ≡ 1 [MOD U] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hval
  have hmodeq : rOf U t * t % U = 1 % U := hmod
  have h1modU : (1 : ℕ) % U = 1 := Nat.mod_eq_of_lt hU1
  have h1le : 1 ≤ rOf U t * t := by
    rcases Nat.eq_zero_or_pos (rOf U t * t) with h0 | hpos
    · rw [h0, Nat.zero_mod, h1modU] at hmodeq; omega
    · exact hpos
  have hdvdU : U ∣ rOf U t * t - 1 := (Nat.modEq_iff_dvd' h1le).1 hmod.symm
  have hdvdq : q ∣ rOf U t * t - 1 := hU.trans hdvdU
  unfold mOf
  rw [Nat.mul_div_cancel' hdvdq]
  omega

/-! ## A real-analysis helper: `q^ε ≤ q/c` eventually, for `ε < 1` -/

/-- For fixed `ε < 1` and any `c > 0`, `q^ε ≤ q/c` for all sufficiently large `q`. Used
throughout to turn the various "for `q` large enough" thresholds of the construction into
explicit `Q₀` bounds. -/
theorem rpow_le_div_eventually (ε : ℝ) (hε1 : ε < 1) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ ε ≤ (q : ℝ) / c := by
  have hy : (0 : ℝ) < 1 - ε := by linarith
  have htend : Tendsto (fun x : ℝ => x ^ (-(1 - ε))) atTop (nhds 0) := tendsto_rpow_neg_atTop hy
  have htend2 : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(1 - ε))) atTop (nhds 0) :=
    htend.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (-(1 - ε)) < 1 / c :=
    htend2.eventually_lt_const (by positivity)
  filter_upwards [hev, eventually_gt_atTop 0] with q hq hq0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hsplit : (q : ℝ) ^ ε = (q : ℝ) ^ (-(1 - ε)) * (q : ℝ) := by
    have h1 : (q : ℝ) ^ (-(1 - ε) + 1) = (q : ℝ) ^ (-(1 - ε)) * (q : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add hqR _ _
    rw [Real.rpow_one] at h1
    rwa [show -(1 - ε) + 1 = ε by ring] at h1
  have hlt : (q : ℝ) ^ ε < (1 / c) * (q : ℝ) := by
    rw [hsplit]; exact mul_lt_mul_of_pos_right hq hqR
  have : (1 / c) * (q : ℝ) = (q : ℝ) / c := by ring
  linarith [this ▸ hlt]

/-! ## Prime power divisibility (paper §2, the sieve paragraph) -/

/-- If a prime power `ℓ^b` exceeds `r` and divides `r * t`, then `ℓ ∣ t`. Used with `r < q/2`
to show that any prime power `> q/2` dividing `qm+1 = rt` must divide `t` (paper: "since both
factors are less than `q/2`, `ℓ ∣ t`; otherwise `u ∣ r`"). -/
theorem primepow_dvd_of_gt {r t ℓ b : ℕ} (hℓ : ℓ.Prime) (hr0 : 0 < r)
    (hgt : r < ℓ ^ b) (hdvd : ℓ ^ b ∣ r * t) : ℓ ∣ t := by
  by_contra hndvd
  have hcop : Nat.Coprime ℓ t := hℓ.coprime_iff_not_dvd.2 hndvd
  have hcop' : Nat.Coprime (ℓ ^ b) t := hcop.pow_left b
  have hdr : ℓ ^ b ∣ r := hcop'.dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd hr0 hdr
  omega

/-- A product `K * q^(-δ)` (`δ > 0` fixed) is eventually `≤` any fixed positive `c`, as
`q → ∞`. The real-analysis workhorse behind the `o(M)`-to-explicit-`Q₀` conversions below. -/
theorem rpow_neg_mul_eventually_le (δ : ℝ) (hδ : 0 < δ) (K c : ℝ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop, K * (q : ℝ) ^ (-δ) ≤ c := by
  have htend : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (nhds 0) := tendsto_rpow_neg_atTop hδ
  have htend2 : Tendsto (fun q : ℕ => (q : ℝ) ^ (-δ)) atTop (nhds 0) :=
    htend.comp tendsto_natCast_atTop_atTop
  have htend3 : Tendsto (fun q : ℕ => K * (q : ℝ) ^ (-δ)) atTop (nhds (K * 0)) :=
    htend2.const_mul K
  rw [mul_zero] at htend3
  exact htend3.eventually_le_const hc

theorem tendsto_log_natCast_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `c ≤ η * log q` eventually, for fixed `c` and `η > 0`. -/
theorem const_le_mul_log_eventually (c η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, c ≤ η * Real.log q := by
  have h := tendsto_log_natCast_atTop.eventually_ge_atTop (c / η)
  filter_upwards [h] with q hq
  rw [div_le_iff₀ hη] at hq
  linarith

/-- `c ≤ q^ε` eventually, for fixed `c` and `ε > 0`. -/
theorem rpow_ge_eventually (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ q : ℕ in atTop, c ≤ (q : ℝ) ^ ε := by
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

/-- `log q / q^c ≤ target` eventually, for fixed `c, target > 0`. Used to absorb `Bmax` (which
grows like `log q`) against any positive power of `q`, below. -/
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

/-- `rOf U t > 0` whenever `t` is coprime to `U > 1`: otherwise `mOf_spec`'s equation
`q * mOf q U t + 1 = 0 * t = 0` is impossible. -/
theorem rOf_pos {q U t : ℕ} (hUdvd : q ∣ U) (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    0 < rOf U t := by
  have heq := mOf_spec hUdvd hU1 hcop
  by_contra h
  push Not at h
  have hr0 : rOf U t = 0 := by omega
  rw [hr0] at heq
  simp only [Nat.zero_mul] at heq
  omega

end Erdos289

