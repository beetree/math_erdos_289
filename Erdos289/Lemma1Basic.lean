import Erdos289.Defs
import Erdos289.External
import Erdos289.ErdosTuran
import Erdos289.Lemma4

/-!
# Lemma 1: definitions and arithmetic lemmas

Split out of `Lemma1.lean` so that the analytic sub-lemmas can be worked on in parallel.
-/

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

/-! ## Factorization bounds (paper display (2.1) and the sentence following it) -/

/-- **Factorization bounds**: for `q` large enough (depending only on `ε`), any factorization
`q * m + 1 = r * t` with `4M ≤ t ≤ 5M` and `3q/10 ≤ r ≤ 7q/20` (writing `M = q^ε` as a real
number) forces `m` into `[M, 2M]` and both `r, t` below `q/2`. -/
theorem factorization_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q → ∀ r t m : ℕ,
      q * m + 1 = r * t →
      4 * (q : ℝ) ^ ε ≤ (t : ℝ) → (t : ℝ) ≤ 5 * (q : ℝ) ^ ε →
      3 * (q : ℝ) / 10 ≤ (r : ℝ) → (r : ℝ) ≤ 7 * (q : ℝ) / 20 →
      ((q : ℝ) ^ ε ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ε) ∧ 2 * r < q ∧ 2 * t < q := by
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.1
    ((rpow_le_div_eventually ε hε1 20 (by norm_num)).and (eventually_ge_atTop 5))
  refine ⟨Q₁, fun q hq r t m heq ht1 ht2 hr1 hr2 => ?_⟩
  obtain ⟨hM, hq5⟩ := hQ₁ q hq
  have hqR : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have heqR : (q : ℝ) * m + 1 = (r : ℝ) * t := by exact_mod_cast heq
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hexp : (q : ℝ) ^ (1 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hqge1 (by linarith)
  have hexp2 : (q : ℝ) ^ ((1 : ℝ) + ε) = (q : ℝ) * (q : ℝ) ^ ε := by
    rw [Real.rpow_add hqpos, Real.rpow_one]
  rw [Real.rpow_one, hexp2] at hexp
  have hqM5 : (5 : ℝ) ≤ (q : ℝ) * (q : ℝ) ^ ε := le_trans hqR hexp
  have hrt_lo : (3 * (q : ℝ) / 10) * (4 * (q : ℝ) ^ ε) ≤ (r : ℝ) * t :=
    mul_le_mul hr1 ht1 (by positivity) (by positivity)
  have hrt_hi : (r : ℝ) * t ≤ (7 * (q : ℝ) / 20) * (5 * (q : ℝ) ^ ε) :=
    mul_le_mul hr2 ht2 (by positivity) (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [hrt_lo, heqR, hqM5]
  · nlinarith [hrt_hi, heqR]
  · have : (2 * r : ℝ) < q := by nlinarith [hr2, hqpos]
    exact_mod_cast this
  · have hMle : (q : ℝ) ^ ε ≤ (q : ℝ) / 20 := hM
    have : (2 * t : ℝ) < q := by nlinarith [ht2, hMle, hqpos]
    exact_mod_cast this

/-! ## Prime power divisibility and uniqueness (paper §2, the sieve paragraph) -/

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

/-- **Uniqueness mod `u`**: if `u` is coprime to `q` and `m₁, m₂` are within `u` of each other
(`|m₂ - m₁| < u`) and both satisfy `u ∣ qm+1`, then `m₁ = m₂`. Used with `u > q/2 > M` (the
length of the interval `[M, 2M]`) to show each "witness" prime power `u` kills at most one
candidate `m` in the sieve. -/
theorem unique_m_mod_u {q u m₁ m₂ : ℕ} (hcop : Nat.Coprime u q)
    (hdvd1 : u ∣ q * m₁ + 1) (hdvd2 : u ∣ q * m₂ + 1) (hlen : |(m₂ : ℤ) - m₁| < u) :
    m₁ = m₂ := by
  have hdvd1' : (u : ℤ) ∣ (q : ℤ) * m₁ + 1 := by exact_mod_cast hdvd1
  have hdvd2' : (u : ℤ) ∣ (q : ℤ) * m₂ + 1 := by exact_mod_cast hdvd2
  have hdvd : (u : ℤ) ∣ (q : ℤ) * ((m₂ : ℤ) - m₁) := by
    have h := dvd_sub hdvd2' hdvd1'
    have heq : (q : ℤ) * m₂ + 1 - ((q : ℤ) * m₁ + 1) = (q : ℤ) * ((m₂ : ℤ) - m₁) := by ring
    rwa [heq] at h
  have hcopZ : IsCoprime (u : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast hcop
  have hdvd' : (u : ℤ) ∣ ((m₂ : ℤ) - m₁) := hcopZ.dvd_of_dvd_mul_left hdvd
  have hz : (m₂ : ℤ) - m₁ = 0 := Int.eq_zero_of_abs_lt_dvd hdvd' hlen
  omega

/-! ## B. Equidistribution of modular inverses (paper §2, "uniform discrepancy" paragraph)

For a modulus `U`, the inverses `t⁻¹ mod U` of `t` ranging over a prefix `(0, T]` coprime to
`U` are equidistributed among residue intervals `[α, α+ℓ) ⊆ [0, U)`. This is the mechanism
that, combined with `bourgain_garaev` and `erdos_turan`, produces the `o(M)` error terms in
`even_case_count` / `odd_case_count` below. -/

/-- The set of `t` in `(T₁, T₂]`, coprime to `U`, whose inverse mod `U` lands in the residue
interval `[α, α+ℓ)`. -/
def invCand (U T₁ T₂ α ℓ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U ∧ rOf U t ∈ Finset.Ico α (α + ℓ))



/-! ## C. Construction and count (paper §2, displays (2.1)-(2.2))

`M = q^ε`. The even case (`q = 2^a`) chooses `t` odd with `r = t⁻¹ mod q` in the target
interval; the odd case (`q = p^a`, `p` odd) chooses `t` coprime to `2p` with `r = t⁻¹ mod 4q`
in the target interval (giving `4 ∣ m` directly, since `4 ∣ 4q ∣ (r t - 1) = qm`), and
additionally requires `p ∤ m`. Both counts are stated as the lower bound needed downstream
(matching the paper's `density · M + o(M)`, using `density ≥ 1/360` uniformly: `1/80` in the
even case, `(1-1/p)²/160 ≥ 1/360` for `p ≥ 3` in the odd case, paper display (2.2)). -/

/-- The even-case (`q = 2^a`) candidate set of `t`'s: `t ∈ (T₁, T₂]` coprime to `q`
(equivalently odd), with `r = t⁻¹ mod q` in the target interval `[3q/10, 7q/20]`, producing an
odd `m`. -/
noncomputable def evenCandT (q T₁ T₂ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t q ∧
    3 * (q : ℝ) / 10 ≤ (rOf q t : ℝ) ∧ (rOf q t : ℝ) ≤ 7 * (q : ℝ) / 20 ∧ Odd (mOf q q t))

/-- The odd-case (`q = p^a`, `p` odd) candidate set of `t`'s: `t ∈ (T₁, T₂]` coprime to `2p`,
with `r = t⁻¹ mod 4q` in the target interval `[3q/10, 7q/20]` (forcing `4 ∣ qm`), and
`p ∤ m`. -/
noncomputable def oddCandT (q p T₁ T₂ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t (2 * p) ∧
    3 * (q : ℝ) / 10 ≤ (rOf (4 * q) t : ℝ) ∧ (rOf (4 * q) t : ℝ) ≤ 7 * (q : ℝ) / 20 ∧
      ¬ p ∣ mOf q (4 * q) t)


end Erdos289
