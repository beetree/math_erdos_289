import Erdos289CLT.Basic

/-!
# The pair attached to a carrier prime (paper Lemma 1, construction)

Fix a prime power `q = p^α` and a prime carrier `b ∈ (q/D, q/16)`, `b ≠ p`.
Put `d = 8` for odd `p`, `d = 1` for `p = 2`, `r = d b`, and let `t ∈ [1, q-1]` be the
inverse of `r` modulo `q`.  Then
`m₊ = (r t - 1)/q`, `m₋ = (r (q - t) + 1)/q` satisfy `m₊ + m₋ = r`, both lie in `(0, r)`,
and at least one is coprime to `p`; we take `m = m₊` unless `p ∣ m₊`.
The companion of `q m` is `d b T` with `T = t` (for `m₊`, pair `{q m, q m + 1}`) or
`T = q - t` (for `m₋`, pair `{q m - 1, q m}`).

`good_carrier_powersmooth`: if `b ∤ T`, and (for odd `p`) `2^{⌊log₂ q⌋ - 2} ∤ T`, then every
prime power dividing the companion `d b T` is below `q`: a prime `ℓ ∉ {2, b}` contributes
only through `T < q`; a power `b^e ≥ q` would force `b ∣ T`; a power `2^e ≥ q` with `d = 8`
would force `2^{e-3} ∣ T` with `2^{e-3} ≥ q/8`; for `p = 2` both `b` and `T` are odd.
-/

namespace Erdos289.CLT

open Finset

/-- `d = 1` for `p = 2`, `d = 8` otherwise. -/
def dOf (p : ℕ) : ℕ := if p = 2 then 1 else 8

/-- The inverse of `r` modulo `q`, as a natural number below `q`. -/
def invMod (q r : ℕ) : ℕ := ((r : ZMod q)⁻¹).val

/-- `m₊ = (r t - 1)/q`. -/
def mPlus (q r : ℕ) : ℕ := (r * invMod q r - 1) / q

/-- `m₋ = (r (q - t) + 1)/q`. -/
def mMinus (q r : ℕ) : ℕ := (r * (q - invMod q r) + 1) / q

/-- The chosen coefficient: `m₊` unless `p ∣ m₊`, in which case `m₋`. -/
def mOf (p q b : ℕ) : ℕ :=
  if p ∣ mPlus q (dOf p * b) then mMinus q (dOf p * b) else mPlus q (dOf p * b)

/-- The lower endpoint of the pair: `q m₊` (pair `{q m₊, q m₊ + 1}`) or `q m₋ - 1`
(pair `{q m₋ - 1, q m₋}`). -/
def loOf (p q b : ℕ) : ℕ :=
  if p ∣ mPlus q (dOf p * b) then q * mMinus q (dOf p * b) - 1 else q * mPlus q (dOf p * b)

/-- The cofactor `T ∈ {t, q - t}` with companion `= d b T`. -/
def TOf (p q b : ℕ) : ℕ :=
  if p ∣ mPlus q (dOf p * b) then q - invMod q (dOf p * b) else invMod q (dOf p * b)

theorem invMod_spec {q r : ℕ} (hq : 1 < q) (hc : Nat.Coprime r q) :
    0 < invMod q r ∧ invMod q r < q ∧ r * invMod q r ≡ 1 [MOD q] := by
  have hne : NeZero q := ⟨by omega⟩
  have hval : invMod q r < q := ZMod.val_lt _
  have hmod : r * invMod q r ≡ 1 [MOD q] := by
    rw [invMod, ← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_mul, Nat.cast_one]
    exact ZMod.mul_val_inv hc
  refine ⟨?_, hval, hmod⟩
  rcases Nat.eq_zero_or_pos (invMod q r) with h0 | h0
  · exfalso
    rw [h0] at hmod
    rw [Nat.ModEq, Nat.mul_zero, Nat.zero_mod, Nat.mod_eq_of_lt hq] at hmod
    exact absurd hmod (by simp)
  · exact h0

/-- `m₊`, `m₋` satisfy the two exact division identities and sum to `r`. -/
theorem mPlus_mMinus_spec {q r : ℕ} (hq : 1 < q) (hc : Nat.Coprime r q) :
    q * mPlus q r + 1 = r * invMod q r ∧
    q * mMinus q r = r * (q - invMod q r) + 1 ∧
    mPlus q r + mMinus q r = r := by
  obtain ⟨ht0, htq, htmod⟩ := invMod_spec hq hc
  have hmod1 : r * invMod q r % q = 1 := by
    have h := htmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt hq] at h
  have hda1 : q * (r * invMod q r / q) + r * invMod q r % q = r * invMod q r :=
    Nat.div_add_mod (r * invMod q r) q
  rw [hmod1] at hda1
  have heq1 : q * mPlus q r + 1 = r * invMod q r := by
    show q * ((r * invMod q r - 1) / q) + 1 = r * invMod q r
    have hdvd : q ∣ (r * invMod q r - 1) := ⟨r * invMod q r / q, by omega⟩
    rw [Nat.mul_div_cancel' hdvd]
    omega
  have hstep : r * (q - invMod q r) + 1 + q * mPlus q r = q * r := by
    have hexp : r * (q - invMod q r) = r * q - r * invMod q r :=
      Nat.mul_sub_left_distrib r q (invMod q r)
    have hcomm : r * q = q * r := Nat.mul_comm r q
    rw [hexp, hcomm]
    have hle : r * invMod q r ≤ q * r := by rw [← hcomm]; exact Nat.mul_le_mul_left r htq.le
    omega
  have hdvd2 : q ∣ (r * (q - invMod q r) + 1) := by
    have heqR : r * (q - invMod q r) + 1 = q * r - q * mPlus q r := by omega
    rw [heqR]
    exact Nat.dvd_sub (dvd_mul_right q r) (dvd_mul_right q (mPlus q r))
  have heqMinus : q * mMinus q r = r * (q - invMod q r) + 1 := by
    show q * ((r * (q - invMod q r) + 1) / q) = r * (q - invMod q r) + 1
    exact Nat.mul_div_cancel' hdvd2
  refine ⟨heq1, heqMinus, ?_⟩
  have hqpos : 0 < q := by omega
  have hqsum : q * mPlus q r + q * mMinus q r = q * r := by omega
  have h2 : q * (mPlus q r + mMinus q r) = q * r := by rw [Nat.mul_add]; exact hqsum
  exact Nat.eq_of_mul_eq_mul_left hqpos h2

/-- If `q m + 1 = r x`, then `x` is coprime to `q`. -/
theorem coprime_of_eq_add_one_left {q r x m : ℕ} (h : q * m + 1 = r * x) :
    Nat.Coprime x q := by
  have hg1 : Nat.gcd x q ∣ r * x := (Nat.gcd_dvd_left x q).mul_left r
  have hg2 : Nat.gcd x q ∣ q * m := (Nat.gcd_dvd_right x q).mul_right m
  have hdvd : Nat.gcd x q ∣ (r * x - q * m) := Nat.dvd_sub hg1 hg2
  have heq : r * x - q * m = 1 := by omega
  rw [heq] at hdvd
  exact Nat.dvd_one.mp hdvd

/-- If `r x + 1 = q m`, then `x` is coprime to `q`. -/
theorem coprime_of_eq_add_one_right {q r x m : ℕ} (h : r * x + 1 = q * m) :
    Nat.Coprime x q := by
  have hg1 : Nat.gcd x q ∣ r * x := (Nat.gcd_dvd_left x q).mul_left r
  have hg2 : Nat.gcd x q ∣ q * m := (Nat.gcd_dvd_right x q).mul_right m
  have hdvd : Nat.gcd x q ∣ (q * m - r * x) := Nat.dvd_sub hg2 hg1
  have heq : q * m - r * x = 1 := by omega
  rw [heq] at hdvd
  exact Nat.dvd_one.mp hdvd

/-- Basic properties of the pair attached to a carrier. -/
theorem carrier_props {p α b Dc : ℕ} (hp : p.Prime) (hα : 0 < α) (hD : 16 < Dc)
    (hq : Dc ^ 3 < p ^ α) (hb : b.Prime) (hbp : b ≠ p)
    (hb1 : p ^ α / Dc < b) (hb2 : b < p ^ α / 16) :
    1 ≤ mOf p (p ^ α) b ∧ mOf p (p ^ α) b < p ^ α ∧ Nat.Coprime (mOf p (p ^ α) b) (p ^ α) ∧
    (loOf p (p ^ α) b = p ^ α * mOf p (p ^ α) b ∨
      loOf p (p ^ α) b + 1 = p ^ α * mOf p (p ^ α) b) ∧
    companion (p ^ α) (loOf p (p ^ α) b) (mOf p (p ^ α) b) = dOf p * b * TOf p (p ^ α) b ∧
    1 ≤ TOf p (p ^ α) b ∧ TOf p (p ^ α) b < p ^ α ∧ Nat.Coprime (TOf p (p ^ α) b) (p ^ α) ∧
    8 ∣ ctr (p ^ α) (loOf p (p ^ α) b) (mOf p (p ^ α) b) ∧
    (dOf p * b * TOf p (p ^ α) b ≡ 1 [MOD p ^ α] ∨
      dOf p * b * TOf p (p ^ α) b + 1 ≡ 0 [MOD p ^ α]) := by
  set q := p ^ α with hqdef
  have hqpos : 0 < q := pow_pos hp.pos α
  have hDcpos : 0 < Dc := by omega
  have hqcube : Dc ^ 3 < q := hq
  have hq4096 : 4096 < q := by
    have h17 : 17 ≤ Dc := by omega
    have h17c : (17 : ℕ) ^ 3 ≤ Dc ^ 3 := Nat.pow_le_pow_left h17 3
    norm_num at h17c
    omega
  have hq2 : 1 < q := by omega
  have hqltbDc : q < b * Dc := (Nat.div_lt_iff_lt_mul hDcpos).mp hb1
  have hcube2 : Dc ^ 2 * Dc < b * Dc := by nlinarith [hqcube, hqltbDc]
  have hDc2b : Dc ^ 2 < b := Nat.lt_of_mul_lt_mul_right hcube2
  have hb256 : 256 < b := by nlinarith [hD, hDc2b]
  have hbne2 : b ≠ 2 := by omega
  have h16b : 16 * b + 16 ≤ q := by omega
  have hbq_cop : Nat.Coprime b q := by
    have hbp_cop : Nat.Coprime b p := (Nat.coprime_primes hb hp).mpr hbp
    rw [hqdef]; exact hbp_cop.pow_right α
  have hcases : (p = 2 ∧ dOf p = 1) ∨ (p ≠ 2 ∧ dOf p = 8) := by
    unfold dOf
    by_cases h : p = 2
    · exact Or.inl ⟨h, by simp [h]⟩
    · exact Or.inr ⟨h, by simp [h]⟩
  set r := dOf p * b with hrdef
  have hrq_cop : Nat.Coprime r q := by
    rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩
    · rw [hrdef, hd, one_mul]; exact hbq_cop
    · have h2p_cop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpodd)
      have h8q_cop : Nat.Coprime 8 q := by
        have h23 : Nat.Coprime (2 ^ 3) (p ^ α) := h2p_cop.pow 3 α
        rw [hqdef]; simpa using h23
      rw [hrdef, hd]; exact h8q_cop.mul_left hbq_cop
  have hr_lt_q : r < q := by
    rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩ <;> rw [hrdef, hd] <;> omega
  have hr_gt1 : 1 < r := by
    rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩ <;> rw [hrdef, hd] <;> omega
  have hpr : ¬ p ∣ r := by
    intro hdvd
    rw [hrdef] at hdvd
    rcases hp.dvd_mul.mp hdvd with hdd | hbb
    · rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩
      · rw [hd] at hdd; exact absurd (Nat.dvd_one.mp hdd) hp.ne_one
      · rw [hd] at hdd
        have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdd)
        exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
    · exact hbp ((Nat.prime_dvd_prime_iff_eq hp hb).mp hbb).symm
  obtain ⟨heq1, heqMinus, hsum⟩ := mPlus_mMinus_spec hq2 hrq_cop
  obtain ⟨ht0, htq, _⟩ := invMod_spec hq2 hrq_cop
  have hmPlus_pos : 0 < mPlus q r := by
    have h2t : 2 ≤ r * invMod q r := Nat.mul_le_mul hr_gt1 ht0
    have hqm_pos : 0 < q * mPlus q r := by omega
    rcases Nat.eq_zero_or_pos (mPlus q r) with h0 | h0
    · rw [h0, Nat.mul_zero] at hqm_pos; omega
    · exact h0
  have hmMinus_pos : 0 < mMinus q r := by
    have hqm_pos : 0 < q * mMinus q r := by omega
    rcases Nat.eq_zero_or_pos (mMinus q r) with h0 | h0
    · rw [h0, Nat.mul_zero] at hqm_pos; omega
    · exact h0
  have hmPlus_lt_r : mPlus q r < r := by omega
  have hmMinus_lt_r : mMinus q r < r := by omega
  have hmPlus_lt_q : mPlus q r < q := lt_trans hmPlus_lt_r hr_lt_q
  have hmMinus_lt_q : mMinus q r < q := lt_trans hmMinus_lt_r hr_lt_q
  have hnotboth : ¬ (p ∣ mPlus q r ∧ p ∣ mMinus q r) := by
    rintro ⟨h1, h2⟩
    exact hpr (hsum ▸ Nat.dvd_add h1 h2)
  have hα3 : p = 2 → 3 ≤ α := by
    intro hp2
    by_contra hlt
    push Not at hlt
    have hle : (p:ℕ) ^ α ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [hp2] at hle
    norm_num at hle
    have hq4096' : 4096 < p ^ α := by rw [← hqdef]; exact hq4096
    rw [hp2] at hq4096'
    omega
  by_cases hcond : p ∣ mPlus q r
  · -- m = mMinus, lo = q*mMinus - 1, T = q - t
    have hmOf : mOf p q b = mMinus q r := by
      show (if p ∣ mPlus q r then mMinus q r else mPlus q r) = mMinus q r
      simp [hcond]
    have hloOf : loOf p q b = q * mMinus q r - 1 := by
      show (if p ∣ mPlus q r then q * mMinus q r - 1 else q * mPlus q r) = q * mMinus q r - 1
      simp [hcond]
    have hTOf : TOf p q b = q - invMod q r := by
      show (if p ∣ mPlus q r then q - invMod q r else invMod q r) = q - invMod q r
      simp [hcond]
    have hpm : ¬ p ∣ mMinus q r := fun h => hnotboth ⟨hcond, h⟩
    have hXpos : 0 < q * mMinus q r := Nat.mul_pos hqpos hmMinus_pos
    have hcompanion : companion q (loOf p q b) (mOf p q b) = r * (q - invMod q r) := by
      rw [hloOf, hmOf]
      show 2 * (q * mMinus q r - 1) + 1 - q * mMinus q r = r * (q - invMod q r)
      omega
    refine ⟨by omega, hmOf ▸ hmMinus_lt_q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmOf]
      have : Nat.Coprime p (mMinus q r) := hp.coprime_iff_not_dvd.mpr hpm
      rw [hqdef]; exact this.symm.pow_right α
    · rw [hloOf, hmOf]; right; omega
    · rw [hcompanion, hTOf]
    · rw [hTOf]; omega
    · rw [hTOf]; omega
    · rw [hTOf]; exact coprime_of_eq_add_one_right heqMinus.symm
    · show 8 ∣ (if Even q then q * mOf p q b else companion q (loOf p q b) (mOf p q b))
      rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩
      · have hqeven : Even q := by
          rw [hqdef, hp2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
        rw [ite_eq_left hqeven, hmOf]
        have h8q : (8:ℕ) ∣ q := by
          rw [hqdef, hp2]
          exact pow_dvd_pow 2 (hα3 hp2)
        exact h8q.mul_right _
      · have hqodd : ¬ Even q := by
          have hop : Odd p := hp.eq_two_or_odd'.resolve_left hpodd
          have hoq : Odd q := by rw [hqdef]; exact hop.pow
          exact Nat.not_even_iff_odd.mpr hoq
        rw [ite_eq_right hqodd, hcompanion, hrdef, hd, mul_assoc]
        exact dvd_mul_right 8 _
    · right
      rw [hTOf]
      have : r * (q - invMod q r) + 1 = q * mMinus q r := heqMinus.symm
      exact Nat.modEq_zero_iff_dvd.mpr ⟨mMinus q r, this⟩
  · -- m = mPlus, lo = q*mPlus, T = t
    have hmOf : mOf p q b = mPlus q r := by
      show (if p ∣ mPlus q r then mMinus q r else mPlus q r) = mPlus q r
      simp [hcond]
    have hloOf : loOf p q b = q * mPlus q r := by
      show (if p ∣ mPlus q r then q * mMinus q r - 1 else q * mPlus q r) = q * mPlus q r
      simp [hcond]
    have hTOf : TOf p q b = invMod q r := by
      show (if p ∣ mPlus q r then q - invMod q r else invMod q r) = invMod q r
      simp [hcond]
    have hcompanion : companion q (loOf p q b) (mOf p q b) = r * invMod q r := by
      rw [hloOf, hmOf]
      show 2 * (q * mPlus q r) + 1 - q * mPlus q r = r * invMod q r
      omega
    refine ⟨by omega, hmOf ▸ hmPlus_lt_q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmOf]
      have : Nat.Coprime p (mPlus q r) := hp.coprime_iff_not_dvd.mpr hcond
      rw [hqdef]; exact this.symm.pow_right α
    · rw [hloOf, hmOf]; left; rfl
    · rw [hcompanion, hTOf]
    · rw [hTOf]; omega
    · rw [hTOf]; omega
    · rw [hTOf]; exact coprime_of_eq_add_one_left heq1
    · show 8 ∣ (if Even q then q * mOf p q b else companion q (loOf p q b) (mOf p q b))
      rcases hcases with ⟨hp2, hd⟩ | ⟨hpodd, hd⟩
      · have hqeven : Even q := by
          rw [hqdef, hp2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
        rw [ite_eq_left hqeven, hmOf]
        have h8q : (8:ℕ) ∣ q := by
          rw [hqdef, hp2]
          exact pow_dvd_pow 2 (hα3 hp2)
        exact h8q.mul_right _
      · have hqodd : ¬ Even q := by
          have hop : Odd p := hp.eq_two_or_odd'.resolve_left hpodd
          have hoq : Odd q := by rw [hqdef]; exact hop.pow
          exact Nat.not_even_iff_odd.mpr hoq
        rw [ite_eq_right hqodd, hcompanion, hrdef, hd, mul_assoc]
        exact dvd_mul_right 8 _
    · left
      rw [hTOf]
      exact Nat.ModEq.symm ((Nat.modEq_iff_dvd' (by omega)).mpr ⟨mPlus q r, by omega⟩)

/-- A carrier whose cofactor `T` is not divisible by `b`, nor (for odd `p`) by
`2^{⌊log₂ q⌋ - 2}`, gives a companion all of whose prime-power divisors are below `q`. -/
theorem good_carrier_powersmooth {p α b Dc : ℕ} (hp : p.Prime) (hα : 0 < α) (hD : 16 < Dc)
    (hq : Dc ^ 3 < p ^ α) (hb : b.Prime) (hbp : b ≠ p)
    (hb1 : p ^ α / Dc < b) (hb2 : b < p ^ α / 16)
    (hbT : ¬ b ∣ TOf p (p ^ α) b)
    (h2 : p ≠ 2 → ¬ 2 ^ (Nat.log 2 (p ^ α) - 2) ∣ TOf p (p ^ α) b) :
    Powersmooth (p ^ α - 1) (companion (p ^ α) (loOf p (p ^ α) b) (mOf p (p ^ α) b)) := by
  obtain ⟨_hm1, _hmlt, _hmcop, _hlomcond, hcompeq, hT1, hTlt, hTcop, _h8ctr, _hcong⟩ :=
    carrier_props hp hα hD hq hb hbp hb1 hb2
  set q := p ^ α with hqdef
  set T := TOf p q b with hTdef
  set d := dOf p with hddef
  rw [hcompeq]
  have hTpos : 0 < T := hT1
  have hDcpos : 0 < Dc := by omega
  have hq4096 : 4096 < q := by
    have h17 : 17 ≤ Dc := by omega
    have h17c : (17 : ℕ) ^ 3 ≤ Dc ^ 3 := Nat.pow_le_pow_left h17 3
    norm_num at h17c
    omega
  have hq2 : 1 < q := by omega
  have hqltbDc : q < b * Dc := (Nat.div_lt_iff_lt_mul hDcpos).mp hb1
  have hcube2 : Dc ^ 2 * Dc < b * Dc := by nlinarith [hq, hqltbDc]
  have hDc2b : Dc ^ 2 < b := Nat.lt_of_mul_lt_mul_right hcube2
  have hb256 : 256 < b := by nlinarith [hD, hDc2b]
  have hbne2 : b ≠ 2 := by omega
  have hbodd : Odd b := hb.eq_two_or_odd'.resolve_left hbne2
  have h16b : 16 * b + 16 ≤ q := by omega
  have hdcases : d = 1 ∨ d = 8 := by
    rw [hddef]; unfold dOf; by_cases h : p = 2 <;> simp [h]
  intro ℓ e hℓ he hdvd
  by_cases hℓ2 : ℓ = 2
  · rw [hℓ2] at hdvd ⊢
    rcases hdcases with hd1 | hd8
    · exfalso
      have hp2 : p = 2 := by
        by_contra hpne
        have hd8' : dOf p = 8 := by unfold dOf; simp [hpne]
        rw [hddef] at hd1
        omega
      have hqeven : Even q := by
        rw [hqdef, hp2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      have hTodd : Odd T := by
        by_contra hTev
        rw [Nat.not_odd_iff_even] at hTev
        have h2T : (2 : ℕ) ∣ T := even_iff_two_dvd.mp hTev
        have h2q : (2 : ℕ) ∣ q := even_iff_two_dvd.mp hqeven
        have hgcd : (2 : ℕ) ∣ Nat.gcd T q := Nat.dvd_gcd h2T h2q
        rw [hTcop] at hgcd
        omega
      have hodd_prod : Odd (d * b * T) := by
        rw [hd1, one_mul]; exact hbodd.mul hTodd
      have h2dvd : (2 : ℕ) ∣ d * b * T := dvd_trans (dvd_pow_self 2 (by omega : e ≠ 0)) hdvd
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd)) hodd_prod
    · have hpodd : p ≠ 2 := by
        intro hp2
        have hd1' : dOf p = 1 := by unfold dOf; simp [hp2]
        rw [hddef] at hd8
        omega
      have hqodd : Odd q := by
        rw [hqdef]; exact (hp.eq_two_or_odd'.resolve_left hpodd).pow
      by_cases he3 : e < 3
      · have h2e8 : (2 : ℕ) ^ e ≤ 8 := by
          calc (2 : ℕ) ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 8 := by norm_num
        omega
      · push Not at he3
        have hcop3 : Nat.Coprime (2 ^ (e - 3)) b := (Nat.coprime_two_left.mpr hbodd).pow_left _
        have hdvd2 : 2 ^ 3 * 2 ^ (e - 3) ∣ 2 ^ 3 * (b * T) := by
          rw [← pow_add]
          have he3' : 3 + (e - 3) = e := by omega
          rw [he3']
          have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
          rw [hd8, h8eq, mul_assoc] at hdvd
          exact hdvd
        have hdvd3 : 2 ^ (e - 3) ∣ b * T :=
          (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2 ^ 3)).mp hdvd2
        have hdvd4 : 2 ^ (e - 3) ∣ T := hcop3.dvd_of_dvd_mul_left hdvd3
        by_contra hcon
        push Not at hcon
        have hge : q ≤ 2 ^ e := by omega
        have hLbound : Nat.log 2 q + 1 ≤ e := by
          by_contra hlt
          push Not at hlt
          have hle : e ≤ Nat.log 2 q := by omega
          have h2e : (2 : ℕ) ^ e ≤ 2 ^ (Nat.log 2 q) := Nat.pow_le_pow_right (by norm_num) hle
          have hlog : (2 : ℕ) ^ (Nat.log 2 q) ≤ q := Nat.pow_log_le_self 2 (by omega)
          have heq : (2 : ℕ) ^ e = q := by omega
          have hepos : 0 < e := by omega
          have heven : Even ((2 : ℕ) ^ e) := Nat.even_pow.mpr ⟨even_two, hepos.ne'⟩
          rw [heq] at heven
          exact (Nat.not_even_iff_odd.mpr hqodd) heven
        have hLge2 : 2 ≤ Nat.log 2 q := by
          have h1 : (2 : ℕ) ^ 2 ≤ q := by omega
          exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h1
        have hfinal : 2 ^ (Nat.log 2 q - 2) ∣ T := by
          have hle2 : Nat.log 2 q - 2 ≤ e - 3 := by omega
          exact dvd_trans (pow_dvd_pow 2 hle2) hdvd4
        exact (h2 hpodd) hfinal
  · by_cases hℓb : ℓ = b
    · rw [hℓb] at hdvd ⊢
      have hbd_cop : Nat.Coprime b d := by
        rcases hdcases with hd1 | hd8
        · rw [hd1]; exact Nat.coprime_one_right b
        · rw [hd8]
          have h2c : Nat.Coprime b 2 := (Nat.coprime_primes hb Nat.prime_two).mpr hbne2
          have h23 : Nat.Coprime b (2 ^ 3) := h2c.pow_right 3
          simpa using h23
      by_cases he1 : e = 1
      · rw [he1, pow_one]; omega
      · exfalso
        have he2 : 2 ≤ e := by omega
        have hcopE : Nat.Coprime (b ^ (e - 1)) d := hbd_cop.pow_left (e - 1)
        have hdvd2 : b ^ 1 * b ^ (e - 1) ∣ b ^ 1 * (d * T) := by
          rw [← pow_add]
          have he1' : 1 + (e - 1) = e := by omega
          rw [he1', pow_one]
          have hcomm : d * b * T = b * (d * T) := by ring
          rw [hcomm] at hdvd
          exact hdvd
        have hdvd3 : b ^ (e - 1) ∣ d * T :=
          (Nat.mul_dvd_mul_iff_left (pow_pos hb.pos 1)).mp hdvd2
        have hdvd4 : b ^ (e - 1) ∣ T := hcopE.dvd_of_dvd_mul_left hdvd3
        have hbdvd : b ∣ b ^ (e - 1) := dvd_pow_self b (by omega)
        exact hbT (hbdvd.trans hdvd4)
    · have hcop_b : Nat.Coprime ℓ b := (Nat.coprime_primes hℓ hb).mpr hℓb
      have hcop_d : Nat.Coprime ℓ d := by
        rcases hdcases with hd1 | hd8
        · rw [hd1]; exact Nat.coprime_one_right ℓ
        · rw [hd8]
          have h2c : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2
          have h23 : Nat.Coprime ℓ (2 ^ 3) := h2c.pow_right 3
          simpa using h23
      have hcop : Nat.Coprime (ℓ ^ e) (d * b) := (hcop_d.mul_right hcop_b).pow_left e
      have hdvdT : ℓ ^ e ∣ T := hcop.dvd_of_dvd_mul_left hdvd
      have hle : ℓ ^ e ≤ T := Nat.le_of_dvd hTpos hdvdT
      omega

end Erdos289.CLT
