import Erdos289.Defs
import Erdos289.External
import Erdos289.ErdosTuran

/-!
# Lemma 1: nonadjacent prime-power correction families

For fixed `0 < ε < 1` and every sufficiently large prime power `q = p ^ a` there is a fiber
`I_q ⊆ [q^ε, 2q^ε]` of size at least `q^(ε - o(1))` such that every `m ∈ I_q` satisfies
`p ∤ m`, `4 ∣ q m`, and `q m + 1` is `(q/2)`-powersmooth.

The `o(1)` in the exponent is made explicit through an arbitrary `η > 0`.

## Proof roadmap (Section 2 of the paper, `proof.txt` lines 99-177)

We follow the paper's five-part structure:

* **A** (`Erdos289/ErdosTuran.lean`): the classical Erdős–Turán discrepancy inequality
  (`erdos_turan`), an unproved external input.
* **B** (`equidist_inverse`): the equidistribution, in residue intervals modulo a modulus
  `U ∈ {q, 2q, 4q, 4pq}`, of the inverses `t⁻¹ mod U` of `t` in a prefix `(0, T]`,
  `T ≤ 5 q^ε`. This is the paper's "uniform discrepancy justification" paragraph,
  combining `bourgain_garaev` and `erdos_turan`; sorried here as a single precise
  statement.
* **C** (`even_case_count`, `odd_case_count`): the explicit counts (2.1)-(2.2) of
  candidate `t`'s produced by the construction, in the even (`q = 2^a`) and odd
  (`q = p^a`, `p` odd) cases. Sorried (they package an application of B together with
  the parity/coprimality bookkeeping of the paper).
* **D** (`sieve_powersmooth`): the powersmoothness sieve, removing candidates with a
  large prime factor (display (2.3), via `mertens_second`) or a large "witness" prime
  power dividing `qm+1` (via `primePow_count_le`/`divisor_bound`). Sorried as a single
  statement; its intended proof uses the fully proved `primepow_dvd_of_gt` and
  `unique_m_mod_u` below.
* **E** (`lemma1` itself): the final assembly, fully proved from B/C/D and the fully
  proved elementary lemmas (`factorization_bounds`, the divisor-bound pigeonhole
  argument `card_le_mul_card_image`, etc.), with no gap.

Fully proved, purely arithmetic ingredients: `rpow_le_div_eventually`,
`factorization_bounds`, `primepow_dvd_of_gt`, `unique_m_mod_u`, and the final assembly
`lemma1` itself (given B, C, D as black boxes).
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

/-- **Equidistribution of modular inverses** (paper §2): for a prime power `q = p^a`, a
modulus `U ∈ {q, 2q, 4q, 4pq}`, a prefix length `T ≤ 5 q^ε`, and a residue interval
`[α, α+ℓ) ⊆ [0, U)`, the count of `t ≤ T` coprime to `U` with `t⁻¹ mod U ∈ [α, α+ℓ)` matches
the expected count `φ(U)/U · T · ℓ/U` up to an error `o(q^ε)`, uniformly in all of the above.

The moduli `U` range over `q, 2q` in the even case and `4q, 4pq` in the odd case (`Erdos289`
paper, Section 2, "Here is the uniform discrepancy justification..."): for a fixed nonzero
Fourier frequency `h`, reduce to `U₀/(h,U₀)`, where `bourgain_garaev` applies since
`q/|h| ≤ U₀/(h,U₀) ≤ 4q²` and the underlying prime `p` remains a unit; `erdos_turan` then
converts the resulting bound on exponential sums into the discrepancy bound stated here. This
is an unproved external input, built from `bourgain_garaev` and `erdos_turan`. -/
theorem equidist_inverse (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
      ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
        ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |((invCand U T₁ T₂ α ℓ).card : ℝ)
                - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)|
              ≤ κ * (q : ℝ) ^ ε := by
  sorry

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

/-- **Even case count** (paper: "The count of such `t` is `M/40 + o(M)`. Among them, `2 ∣ m`
iff the inverse modulo `2q` belongs to the same absolute interval; their count is
`M/80 + o(M)`. Thus `M/80 + o(M)` choices have odd `m`."). Stated as the lower bound needed
downstream; proved (in the paper) from `equidist_inverse` applied at moduli `q` and `2q`. -/
theorem even_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ a : ℕ, 0 < a → q = 2 ^ a →
      (q : ℝ) ^ ε / 80 - κ * (q : ℝ) ^ ε ≤
        ((evenCandT q ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  sorry

/-- **Odd case count** (paper display (2.2)): "Since `4 ∣ m`, the additional condition `p ∣ m`
is equivalent to `rt ≡ 1 (mod 4pq)` ... Subtracting leaves `(1-1/p)² M / 160 + o(M) ≥ M/360 +
o(M)`." Stated as the lower bound needed downstream (using `p ≥ 3`, so `(1-1/p)² ≥ 4/9`);
proved (in the paper) from `equidist_inverse` applied at moduli `4q` and `4pq`. -/
theorem odd_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → Odd p → 0 < a → q = p ^ a →
      (q : ℝ) ^ ε / 360 - κ * (q : ℝ) ^ ε ≤
        ((oddCandT q p ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  sorry

/-! ## D. Powersmoothness sieve (paper §2, displays (2.3) and the paragraph after it) -/

/-- **Powersmoothness sieve**: for `q` large and `D = q^(ε-η)` (any fixed small `η`, absorbed
into `κ` here), given a modulus `U` (a multiple of `q`) and a finite set `T` of `t`'s in
`(4M, 5M]` (`M = q^ε`) each with companion `r = rOf U t < q/2`, there is a subset `T' ⊆ T`
with `|T| ≤ |T'| + κM` such that `q * mOf q U t + 1` is `(q/2)`-powersmooth for every `t ∈ T'`.

This combines the paper's two sieve steps: removing `t` with a prime factor exceeding `D`
(display (2.3), via `mertens_second`); and removing, for each of the `O(D log q)` prime
powers `u = ℓ^b ∈ (q/2, 2qM]` with `ℓ ≤ D` prime (counted as in `primePow_count_le`), the
(at most one, by `unique_m_mod_u`) `m` with `u ∣ q m + 1`, together with all `t ∈ T` giving
rise to it (at most `τ(qm+1) = q^{o(1)}` many, by `divisor_bound`). The base bound `ℓ ≤ D` for
any offending prime power `> q/2` follows from `primepow_dvd_of_gt`, using `r < q/2`. -/
theorem sieve_powersmooth (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ U : ℕ, q ∣ U → 0 < U →
      ∀ T : Finset ℕ,
        (∀ t ∈ T, 4 * (q : ℝ) ^ ε ≤ (t : ℝ) ∧ (t : ℝ) ≤ 5 * (q : ℝ) ^ ε) →
        (∀ t ∈ T, 2 * rOf U t < q) →
        ∃ T' ⊆ T, (T.card : ℝ) ≤ (T'.card : ℝ) + κ * (q : ℝ) ^ ε ∧
          ∀ t ∈ T', Powersmooth (q / 2) (q * mOf q U t + 1) := by
  sorry

/-! ## E. Final assembly (fully proved from B/C/D and the elementary lemmas above) -/

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

/-- Shared final-assembly step (fully proved from `sieve_powersmooth` and `divisor_bound`,
via the divisor-bound pigeonhole argument `Finset.card_le_mul_card_image`): given a candidate
Finset `T` of `t`'s in `(4M, 5M]` (`M = q^ε`), each coprime to a modulus `U` (a multiple of
`q`, `U > 1`) with companion `r = rOf U t ∈ [3q/10, 7q/20]`, and `|T| ≥ M/720`, there is (for
`q` large, depending only on `ε, η`) a Finset `I ⊆ [M, 2M] ∩ ℕ` of size `≥ q^(ε-η)`, all
`m ∈ I` arising as `mOf q U t` for some `t ∈ T`, with `q * m + 1` `(q/2)`-powersmooth. -/
theorem assemble_from_candidates (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ U : ℕ, q ∣ U → 1 < U →
      ∀ T : Finset ℕ,
        (∀ t ∈ T, Nat.Coprime t U) →
        (∀ t ∈ T, 3 * (q : ℝ) / 10 ≤ (rOf U t : ℝ) ∧ (rOf U t : ℝ) ≤ 7 * (q : ℝ) / 20) →
        (∀ t ∈ T, 4 * (q : ℝ) ^ ε ≤ (t : ℝ) ∧ (t : ℝ) ≤ 5 * (q : ℝ) ^ ε) →
        (q : ℝ) ^ ε / 720 ≤ (T.card : ℝ) →
        ∃ I : Finset ℕ,
          (∀ m ∈ I, (q : ℝ) ^ ε ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ε) ∧
          (q : ℝ) ^ (ε - η) ≤ (I.card : ℝ) ∧
          (∀ m ∈ I, Powersmooth (q / 2) (q * m + 1)) ∧
          (∀ m ∈ I, ∃ t ∈ T, m = mOf q U t) := by
  obtain ⟨Q_fb, hQ_fb⟩ := factorization_bounds ε hε0 hε1
  have hεdiv : (0 : ℝ) < η / 12 := by linarith
  obtain ⟨N_div, hN_div⟩ := eventually_atTop.1 (divisor_bound (η / 12) hεdiv)
  have hc2 : (0 : ℝ) < 1 / 2880 := by norm_num
  filter_upwards [sieve_powersmooth ε hε0 hε1 (1 / 1440) (by norm_num),
      eventually_ge_atTop Q_fb, eventually_ge_atTop N_div, eventually_ge_atTop 3,
      rpow_neg_mul_eventually_le (3 * η / 4) (by linarith) 1 (1 / 2880) hc2,
      rpow_neg_mul_eventually_le η hη 1 (1 / 2880) hc2]
    with q hsieve hqfb hqNdiv hq3 hbound1 hbound2
  intro U hUdvd hU1 T hTcop hTr hTt hTcard
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hMge1 : (1 : ℝ) ≤ (q : ℝ) ^ ε := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hqR1 hε0.le
    rwa [Real.one_rpow] at h
  have hqMle : (q : ℝ) ^ ε ≤ (q : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hqR1 hε1.le
    rwa [Real.rpow_one] at h
  have hTr2 : ∀ t ∈ T, 2 * rOf U t < q := by
    intro t ht
    obtain ⟨_, hr2⟩ := hTr t ht
    have : (2 * rOf U t : ℝ) < q := by nlinarith [hr2, hqR1]
    exact_mod_cast this
  obtain ⟨T', hT'sub, hT'card, hT'smooth⟩ := hsieve U hUdvd (by omega) T hTt hTr2
  have hT'card2 : (q : ℝ) ^ ε / 1440 ≤ (T'.card : ℝ) := by linarith [hT'card, hTcard]
  refine ⟨T'.image (mOf q U), ?_, ?_, ?_, ?_⟩
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨t, htT', rfl⟩ := hm
    have htT : t ∈ T := hT'sub htT'
    have heq : q * mOf q U t + 1 = rOf U t * t := mOf_spec hUdvd hU1 (hTcop t htT)
    obtain ⟨hr1, hr2⟩ := hTr t htT
    obtain ⟨ht1, ht2⟩ := hTt t htT
    exact (hQ_fb q hqfb (rOf U t) t (mOf q U t) heq ht1 ht2 hr1 hr2).1
  · -- cardinality bound via the divisor-bound pigeonhole
    have hfiber : ∀ b ∈ T'.image (mOf q U),
        (T'.filter (fun t => mOf q U t = b)).card ≤
          (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℕ) := by
      intro b hb
      have hsub : T'.filter (fun t => mOf q U t = b) ⊆ (q * b + 1).divisors := by
        intro t ht
        rw [Finset.mem_filter] at ht
        obtain ⟨htT', hmeq⟩ := ht
        have htT : t ∈ T := hT'sub htT'
        have heq : q * mOf q U t + 1 = rOf U t * t := mOf_spec hUdvd hU1 (hTcop t htT)
        rw [hmeq] at heq
        rw [Nat.mem_divisors]
        exact ⟨⟨rOf U t, by rw [heq]; ring⟩, by omega⟩
      have hcard1 : (T'.filter (fun t => mOf q U t = b)).card ≤ (q * b + 1).divisors.card :=
        Finset.card_le_card hsub
      obtain ⟨t0, ht0T', ht0eq⟩ := Finset.mem_image.1 hb
      have ht0T : t0 ∈ T := hT'sub ht0T'
      have heq0 : q * mOf q U t0 + 1 = rOf U t0 * t0 := mOf_spec hUdvd hU1 (hTcop t0 ht0T)
      obtain ⟨hr1, hr2⟩ := hTr t0 ht0T
      obtain ⟨ht1, ht2⟩ := hTt t0 ht0T
      have hbbound := hQ_fb q hqfb (rOf U t0) t0 (mOf q U t0) heq0 ht1 ht2 hr1 hr2
      have hb2M : (b : ℝ) ≤ 2 * (q : ℝ) ^ ε := ht0eq ▸ hbbound.1.2
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := ht0eq ▸ le_trans hMge1 hbbound.1.1
      have hb2q : (b : ℝ) ≤ 2 * (q : ℝ) := le_trans hb2M (by nlinarith [hqMle])
      have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      have hnq3 : q * b + 1 ≤ q ^ 3 := by
        have : (((q * b + 1 : ℕ)) : ℝ) ≤ ((q : ℝ)) ^ 3 := by
          have hbR : (b : ℝ) ≤ 2 * (q : ℝ) := hb2q
          push_cast
          nlinarith [hqR1, hbR, hq3R,
            mul_nonneg (by linarith : (0:ℝ) ≤ (q:ℝ) - 3) (sq_nonneg (q:ℝ)),
            mul_nonneg (by linarith : (0:ℝ) ≤ (q:ℝ) - 3) (by linarith : (0:ℝ) ≤ (q:ℝ)),
            mul_le_mul_of_nonneg_left hbR (by linarith : (0:ℝ) ≤ (q:ℝ))]
        exact_mod_cast this
      have hnge : N_div ≤ q * b + 1 := by
        have h1 : (q : ℝ) ≤ ((q * b + 1 : ℕ) : ℝ) := by
          push_cast; nlinarith [hb1]
        have h2 : (N_div : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNdiv
        have : (N_div : ℝ) ≤ ((q * b + 1 : ℕ) : ℝ) := le_trans h2 h1
        exact_mod_cast this
      have htau : ((q * b + 1).divisors.card : ℝ) ≤ ((q * b + 1 : ℕ) : ℝ) ^ (η / 12) :=
        hN_div (q * b + 1) hnge
      have hqb3 : ((q * b + 1 : ℕ) : ℝ) ≤ ((q : ℝ) ^ 3 : ℝ) := by exact_mod_cast hnq3
      have hmono : ((q * b + 1 : ℕ) : ℝ) ^ (η / 12) ≤ ((q : ℝ) ^ 3) ^ (η / 12) :=
        Real.rpow_le_rpow (by positivity) hqb3 hεdiv.le
      have hcast3 : ((q : ℝ) ^ 3) ^ (η / 12) = (q : ℝ) ^ (η / 4) := by
        rw [← Real.rpow_natCast (q : ℝ) 3, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      have hfinal : ((q * b + 1).divisors.card : ℝ) ≤ (q : ℝ) ^ (η / 4) := by
        rw [← hcast3]; exact le_trans htau hmono
      have hceil : (q : ℝ) ^ (η / 4) ≤ (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) := Nat.le_ceil _
      have : ((q * b + 1).divisors.card : ℝ) ≤ (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) :=
        le_trans hfinal hceil
      have := le_trans hcard1 (by exact_mod_cast this : (q * b + 1).divisors.card ≤ _)
      exact this
    have hpig : (T'.card : ℕ) ≤ (⌈(q : ℝ) ^ (η / 4)⌉₊) * (T'.image (mOf q U)).card :=
      Finset.card_le_mul_card_image T' _ hfiber
    have hpigR : (T'.card : ℝ) ≤ (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) * ((T'.image (mOf q U)).card : ℝ) := by
      exact_mod_cast hpig
    have hceilR : (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) ≤ (q : ℝ) ^ (η / 4) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith [hqR1]
    have hstep1 : (q : ℝ) ^ (-(3 * η / 4)) ≤ 1 / 2880 := by simpa using hbound1
    have hbound1' : (q : ℝ) ^ (η / 4) ≤ (1 / 2880) * (q : ℝ) ^ η := by
      have hmul := mul_le_mul_of_nonneg_left hstep1
        (le_of_lt (Real.rpow_pos_of_pos hqpos η))
      have hlhs : (q : ℝ) ^ η * (q : ℝ) ^ (-(3 * η / 4)) = (q : ℝ) ^ (η / 4) := by
        rw [← Real.rpow_add hqpos]; ring_nf
      rw [hlhs] at hmul
      linarith [hmul]
    have hstep2 : (q : ℝ) ^ (-η) ≤ 1 / 2880 := by simpa using hbound2
    have hbound2' : (1 : ℝ) ≤ (1 / 2880) * (q : ℝ) ^ η := by
      have hmul := mul_le_mul_of_nonneg_left hstep2
        (le_of_lt (Real.rpow_pos_of_pos hqpos η))
      have hlhs : (q : ℝ) ^ η * (q : ℝ) ^ (-η) = 1 := by
        rw [← Real.rpow_add hqpos]; simp
      rw [hlhs] at hmul
      linarith [hmul]
    have hceilbound : (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) ≤ (1 / 1440) * (q : ℝ) ^ η := by
      linarith [hceilR, hbound1', hbound2']
    have hpigR' : (T'.card : ℝ) ≤
        (1 / 1440) * (q : ℝ) ^ η * ((T'.image (mOf q U)).card : ℝ) := by
      calc (T'.card : ℝ) ≤ (⌈(q : ℝ) ^ (η / 4)⌉₊ : ℝ) * ((T'.image (mOf q U)).card : ℝ) := hpigR
        _ ≤ (1 / 1440) * (q : ℝ) ^ η * ((T'.image (mOf q U)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hceilbound (by positivity)
    have hcombine : (q : ℝ) ^ ε / 1440 ≤
        (1 / 1440) * (q : ℝ) ^ η * ((T'.image (mOf q U)).card : ℝ) :=
      le_trans hT'card2 hpigR'
    have hcombine2 : (q : ℝ) ^ ε ≤ (q : ℝ) ^ η * ((T'.image (mOf q U)).card : ℝ) := by
      linarith [hcombine]
    have hqη_pos : (0 : ℝ) < (q : ℝ) ^ η := Real.rpow_pos_of_pos hqpos η
    have hfinal2 : (q : ℝ) ^ ε / (q : ℝ) ^ η ≤ ((T'.image (mOf q U)).card : ℝ) := by
      rw [div_le_iff₀ hqη_pos]; linarith [hcombine2]
    have hrpowsub : (q : ℝ) ^ (ε - η) = (q : ℝ) ^ ε / (q : ℝ) ^ η := Real.rpow_sub hqpos ε η
    rw [hrpowsub]
    exact hfinal2
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨t, htT', rfl⟩ := hm
    exact hT'smooth t htT'
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨t, htT', rfl⟩ := hm
    exact ⟨t, hT'sub htT', rfl⟩

/-- Membership in `Ioc ⌊4M⌋₊ ⌊5M⌋₊` gives the real bounds `4M ≤ t ≤ 5M`. -/
theorem Ioc_floor_mem_bounds {q : ℕ} (ε : ℝ) (t : ℕ)
    (ht : t ∈ Finset.Ioc ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊) :
    4 * (q : ℝ) ^ ε ≤ (t : ℝ) ∧ (t : ℝ) ≤ 5 * (q : ℝ) ^ ε := by
  rw [Finset.mem_Ioc] at ht
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · have hstepR : ((⌊4 * (q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast ht1
    have hlt : 4 * (q : ℝ) ^ ε < ((⌊4 * (q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  · have hle : (t : ℝ) ≤ ((⌊5 * (q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast ht2
    have hfl : ((⌊5 * (q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) ≤ 5 * (q : ℝ) ^ ε := Nat.floor_le (by positivity)
    linarith

/-- Companion to `mOf_spec`: the full modulus `U` divides `q * mOf q U t` (not just `q`
itself), whenever `U` is a positive multiple of `q` and `t` is coprime to `U`. Used to derive
`4 ∣ q * m` in the odd case from `4 ∣ U = 4q`. -/
theorem mOf_dvd {q U t : ℕ} (hU : q ∣ U) (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    U ∣ q * mOf q U t := by
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
  have heq : rOf U t * t - 1 = q * mOf q U t := by
    have := mOf_spec hU hU1 hcop
    omega
  rwa [heq] at hdvdU

/-- **Lemma 1** of the paper. -/
theorem lemma1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (η : ℝ) (hη : 0 < η) :
    ∃ Q₀ : ℕ, ∀ p a : ℕ, p.Prime → 0 < a → Q₀ ≤ p ^ a →
      ∃ I : Finset ℕ,
        (∀ m ∈ I, ((p ^ a : ℕ) : ℝ) ^ ε ≤ m ∧ (m : ℝ) ≤ 2 * ((p ^ a : ℕ) : ℝ) ^ ε) ∧
        ((p ^ a : ℕ) : ℝ) ^ (ε - η) ≤ I.card ∧
        ∀ m ∈ I, ¬ p ∣ m ∧ 4 ∣ p ^ a * m ∧ Powersmooth (p ^ a / 2) (p ^ a * m + 1) := by
  have hκC : (0 : ℝ) < 1 / 720 := by norm_num
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((((even_case_count ε hε0 hε1 (1 / 720) hκC).and
        (odd_case_count ε hε0 hε1 (1 / 720) hκC)).and
        (assemble_from_candidates ε η hε0 hε1 hη)).and (eventually_ge_atTop 4))
  refine ⟨N, fun p a hp ha hQ => ?_⟩
  set q := p ^ a with hqdef
  obtain ⟨⟨⟨hev, hod⟩, hasm⟩, hq4⟩ := hN q hQ
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by
    have hqpos : 0 < q := hqdef ▸ pow_pos hp.pos a
    exact_mod_cast hqpos
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · -- even case: p = 2
    subst hp2
    have hqeq : q = 2 ^ a := hqdef
    have hevcard := hev a ha hqeq.symm
    set T := evenCandT q ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊ with hTdef
    have hTcop : ∀ t ∈ T, Nat.Coprime t q := by
      intro t ht
      rw [hTdef] at ht; unfold evenCandT at ht; rw [Finset.mem_filter] at ht
      exact ht.2.1
    have hTr : ∀ t ∈ T, 3 * (q : ℝ) / 10 ≤ (rOf q t : ℝ) ∧ (rOf q t : ℝ) ≤ 7 * (q : ℝ) / 20 := by
      intro t ht
      rw [hTdef] at ht; unfold evenCandT at ht; rw [Finset.mem_filter] at ht
      exact ⟨ht.2.2.1, ht.2.2.2.1⟩
    have hTt : ∀ t ∈ T, 4 * (q : ℝ) ^ ε ≤ (t : ℝ) ∧ (t : ℝ) ≤ 5 * (q : ℝ) ^ ε := by
      intro t ht
      rw [hTdef] at ht; unfold evenCandT at ht; rw [Finset.mem_filter] at ht
      exact Ioc_floor_mem_bounds ε t ht.1
    have hTodd : ∀ t ∈ T, Odd (mOf q q t) := by
      intro t ht
      rw [hTdef] at ht; unfold evenCandT at ht; rw [Finset.mem_filter] at ht
      exact ht.2.2.2.2
    have hTcard : (q : ℝ) ^ ε / 720 ≤ (T.card : ℝ) := by
      have hqεpos : (0 : ℝ) ≤ (q : ℝ) ^ ε := by positivity
      linarith [hevcard]
    obtain ⟨I, hImem, hIcard, hIsmooth, hIfrom⟩ :=
      hasm q (dvd_refl q) (by omega) T hTcop hTr hTt hTcard
    refine ⟨I, hImem, hIcard, fun m hm => ?_⟩
    obtain ⟨t, htT, rfl⟩ := hIfrom m hm
    have hmodd : Odd (mOf q q t) := hTodd t htT
    have ha2 : 2 ≤ a := by
      have h4eq : (2:ℕ) ^ 2 = 4 := by norm_num
      rw [hqeq] at hq4
      have : (2:ℕ)^2 ≤ 2^a := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have h4dvdq : (4 : ℕ) ∣ q := by
      have : (2:ℕ)^2 ∣ 2^a := pow_dvd_pow 2 ha2
      rwa [show (2:ℕ)^2 = 4 by norm_num, ← hqeq] at this
    refine ⟨?_, dvd_mul_of_dvd_left h4dvdq _, hIsmooth (mOf q q t) hm⟩
    · intro hdvd
      obtain ⟨k, hk⟩ := hmodd
      obtain ⟨j, hj⟩ := hdvd
      omega
  · -- odd case: p odd
    have hqeq : q = p ^ a := hqdef
    have hodcard := hod p a hp hpodd ha hqeq.symm
    set U := 4 * q with hUdef
    set T := oddCandT q p ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊ with hTdef
    have hcop4q : ∀ t : ℕ, Nat.Coprime t (2 * p) → Nat.Coprime t U := by
      intro t ht
      have h2 : Nat.Coprime t 2 := Nat.Coprime.coprime_dvd_right ⟨p, rfl⟩ ht
      have hpc : Nat.Coprime t p := Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ ht
      have h4 : Nat.Coprime t 4 := by
        have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4eq]; exact h2.pow_right 2
      have hq : Nat.Coprime t q := by rw [hqeq]; exact hpc.pow_right a
      rw [hUdef]
      exact h4.mul_right hq
    have hTcop : ∀ t ∈ T, Nat.Coprime t U := by
      intro t ht
      rw [hTdef] at ht; unfold oddCandT at ht; rw [Finset.mem_filter] at ht
      exact hcop4q t ht.2.1
    have hTr : ∀ t ∈ T, 3 * (q : ℝ) / 10 ≤ (rOf U t : ℝ) ∧ (rOf U t : ℝ) ≤ 7 * (q : ℝ) / 20 := by
      intro t ht
      rw [hTdef] at ht; unfold oddCandT at ht; rw [Finset.mem_filter] at ht
      exact ⟨ht.2.2.1, ht.2.2.2.1⟩
    have hTt : ∀ t ∈ T, 4 * (q : ℝ) ^ ε ≤ (t : ℝ) ∧ (t : ℝ) ≤ 5 * (q : ℝ) ^ ε := by
      intro t ht
      rw [hTdef] at ht; unfold oddCandT at ht; rw [Finset.mem_filter] at ht
      exact Ioc_floor_mem_bounds ε t ht.1
    have hTpm : ∀ t ∈ T, ¬ p ∣ mOf q U t := by
      intro t ht
      rw [hTdef] at ht; unfold oddCandT at ht; rw [Finset.mem_filter] at ht
      exact ht.2.2.2.2
    have hTcard : (q : ℝ) ^ ε / 720 ≤ (T.card : ℝ) := by linarith [hodcard]
    have hU1 : 1 < U := by rw [hUdef]; omega
    obtain ⟨I, hImem, hIcard, hIsmooth, hIfrom⟩ :=
      hasm U ⟨4, by rw [hUdef]; ring⟩ hU1 T hTcop hTr hTt hTcard
    refine ⟨I, hImem, hIcard, fun m hm => ?_⟩
    obtain ⟨t, htT, rfl⟩ := hIfrom m hm
    have htT' : t ∈ T := htT
    have hpm : ¬ p ∣ mOf q U t := hTpm t htT'
    have hUdvdqm : U ∣ q * mOf q U t := mOf_dvd (⟨4, by rw [hUdef]; ring⟩) hU1 (hTcop t htT')
    have h4dvdqm : (4 : ℕ) ∣ q * mOf q U t := by
      have : (4:ℕ) ∣ U := ⟨q, hUdef⟩
      exact this.trans hUdvdqm
    exact ⟨hpm, h4dvdqm, hIsmooth (mOf q U t) hm⟩

end Erdos289
