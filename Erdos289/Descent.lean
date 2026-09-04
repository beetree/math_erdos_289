import Erdos289.Defs
import Erdos289.DenBound
import Erdos289.Cancel
import Erdos289.Lemma2
import Erdos289.Lemma5
import Erdos289.Harmonic
import Erdos289.Tail
import Erdos289.Expert

/-!
# Section 4: the correction procedure with a predetermined number of pairs

Given an initial deficit whose reduced denominator only has prime powers at most `H`, visit
every prime power `q ∈ (L, H]` in decreasing order. At stage `q` the full power `q` (if present)
is cancelled using `c_q ≤ s(q)` correction pairs `[qm, qm+1]` with `m` in the Lemma 1 fiber
`I_q` (Lemma 3 supplies the required congruence), and then `s(q) - c_q` auxiliary pairs from
`F_q` are added. Each stage adds exactly `s(q)` pairs, the invariant "no prime power `≥ q` in
the denominator" is restored, and after all stages the denominator only has prime powers at
most `L`.
-/

namespace Erdos289

open Finset

/-- The predetermined number of correction intervals `C_H = ∑_{L < q ≤ H, q prime power} s(q)`. -/
noncomputable def CH (L H : ℕ) : ℕ := ∑ q ∈ (Icc (L + 1) H).filter IsPrimePow, s q

/-- The data fixed once and for all before `k` is chosen: a cutoff `L`, an auxiliary family,
and, for every prime power `q > L`, a Lemma 1 fiber `I_q` (with `ε = 1/10`) that is large enough
for Lemma 3 to apply. -/
structure CorrectionData where
  L : ℕ
  A : AuxFamily L
  /-- The fiber `I_q` of Lemma 1 (indexed by the prime power `q`). -/
  I : ℕ → Finset ℕ
  I_range : ∀ q, IsPrimePow q → L < q →
    ∀ m ∈ I q, (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10)
  I_coprime : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, Nat.Coprime m q
  I_four : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, 4 ∣ q * m
  I_smooth : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, Powersmooth (q / 2) (q * m + 1)
  /-- Lemma 3 applies to `I_q`: every residue is a short sum of inverses. -/
  I_cover : ∀ q, IsPrimePow q → L < q → ∀ r : ZMod q,
    ∃ S ⊆ I q, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r

/-! ## Elementary helper lemmas -/

/-- If `m` is coprime to `q` and `p ∣ q`, then `p ∤ m`. -/
theorem not_dvd_of_coprime_of_dvd {m q p : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (hcop : Nat.Coprime m q) : ¬ p ∣ m := by
  intro hpm
  have hg : p ∣ Nat.gcd m q := Nat.dvd_gcd hpm hpq
  rw [hcop] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

/-- For real `q ≥ 5`, `2 * q ^ (1/10) < q`. -/
theorem two_mul_rpow_tenth_lt {q : ℝ} (hq : 5 ≤ q) : 2 * q ^ ((1 : ℝ) / 10) < q := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  rw [show (1 : ℝ) / 10 = (10 : ℝ)⁻¹ by norm_num,
    show (2 : ℝ) * q ^ (10 : ℝ)⁻¹ < q ↔ q ^ (10 : ℝ)⁻¹ < q / 2 by constructor <;> intro <;> linarith,
    Real.rpow_inv_lt_iff_of_pos hq0 (by linarith) (by norm_num)]
  have h9 : (5 : ℝ) ^ 9 ≤ q ^ 9 := by gcongr
  have hqe : (q / 2) ^ (10 : ℝ) = q ^ 10 / 2 ^ 10 := by
    rw [Real.rpow_ofNat, div_pow]
  rw [hqe]
  nlinarith [h9]

/-- For prime power `q ∈ AuxFamily`/`I_q` data with cutoff `C.L ≥ 4`, `q > C.L` implies
`5 ≤ q`, and any `m` with `(m : ℝ) ≤ 2 * q ^ (1/10)` satisfies `m < q`. -/
theorem lt_of_real_le_two_mul_rpow_tenth {q m : ℕ} (hq5 : 5 ≤ q)
    (hm : (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10)) : m < q := by
  have hq5' : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have := two_mul_rpow_tenth_lt hq5'
  have : (m : ℝ) < (q : ℝ) := lt_of_le_of_lt hm this
  exact_mod_cast this

/-- If `0 < q` and `(q : ℝ) ^ (1/10) ≤ m`, then `0 < m`. -/
theorem nat_pos_of_real_rpow_le {q m : ℕ} (hq : 0 < q) (h : (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m) :
    0 < m := by
  have hpos : (0 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  have : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hpos h
  exact_mod_cast this

/-- A pair is never separated from itself. -/
theorem Iv.pair_not_sep_self (a : ℕ) : ¬ Iv.Sep (Iv.pair a) (Iv.pair a) := by
  simp only [Iv.Sep, Iv.pair]
  omega

/-! ## Separation of stage pairs -/

/-- A pair produced at stage `q` of the correction procedure: either a correction pair
`[qm, qm+1]` with `m ∈ I_q`, or an auxiliary pair `[a, a+1]` with `a ∈ F_q`. -/
def IsStagePair (C : CorrectionData) (q : ℕ) (I : Iv) : Prop :=
  (∃ m ∈ C.I q, I = Iv.pair (q * m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a)

/-- Any two distinct stage pairs, possibly from different stages `q₁ ≠ q₂` (with `q₁, q₂` prime
powers `> C.L`), are separated. This covers both the intra-stage separation of Lemma 2 /
`AuxFamily.sep_aux` and the cross-stage separation used to glue stages together in the
induction for `descent`. -/
theorem sep_of_stage_pairs (C : CorrectionData) (hL : 4 ≤ C.L) {q₁ q₂ : ℕ}
    (hq₁ : IsPrimePow q₁) (hLq₁ : C.L < q₁) (hq₂ : IsPrimePow q₂) (hLq₂ : C.L < q₂)
    {I J : Iv} (hI : IsStagePair C q₁ I) (hJ : IsStagePair C q₂ J) (hne : I ≠ J) :
    Iv.Sep I J := by
  have hq₁5 : 5 ≤ q₁ := by omega
  have hq₂5 : 5 ≤ q₂ := by omega
  rcases hI with ⟨m₁, hm₁, rfl⟩ | ⟨a₁, ha₁, rfl⟩ <;>
    rcases hJ with ⟨m₂, hm₂, rfl⟩ | ⟨a₂, ha₂, rfl⟩
  · -- correction pair vs. correction pair: Lemma 2
    obtain ⟨p₁, e₁, hp₁, he₁, hpe₁⟩ := (isPrimePow_nat_iff q₁).mp hq₁
    obtain ⟨p₂, e₂, hp₂, he₂, hpe₂⟩ := (isPrimePow_nat_iff q₂).mp hq₂
    have hpm₁ : ¬ p₁ ∣ m₁ := not_dvd_of_coprime_of_dvd hp₁ (hpe₁ ▸ dvd_pow_self p₁ he₁.ne')
      (C.I_coprime _ hq₁ hLq₁ m₁ hm₁)
    have hpm₂ : ¬ p₂ ∣ m₂ := not_dvd_of_coprime_of_dvd hp₂ (hpe₂ ▸ dvd_pow_self p₂ he₂.ne')
      (C.I_coprime _ hq₂ hLq₂ m₂ hm₂)
    have hmlt₁ : m₁ < p₁ ^ e₁ :=
      hpe₁ ▸ lt_of_real_le_two_mul_rpow_tenth hq₁5 (C.I_range _ hq₁ hLq₁ m₁ hm₁).2
    have hmlt₂ : m₂ < p₂ ^ e₂ :=
      hpe₂ ▸ lt_of_real_le_two_mul_rpow_tenth hq₂5 (C.I_range _ hq₂ hLq₂ m₂ hm₂).2
    have hm0₁ : 0 < m₁ := nat_pos_of_real_rpow_le (by omega) (C.I_range _ hq₁ hLq₁ m₁ hm₁).1
    have hm0₂ : 0 < m₂ := nat_pos_of_real_rpow_le (by omega) (C.I_range _ hq₂ hLq₂ m₂ hm₂).1
    have h4₁ : 4 ∣ p₁ ^ e₁ * m₁ := hpe₁ ▸ C.I_four _ hq₁ hLq₁ m₁ hm₁
    have h4₂ : 4 ∣ p₂ ^ e₂ * m₂ := hpe₂ ▸ C.I_four _ hq₂ hLq₂ m₂ hm₂
    have hne_label : (p₁ ^ e₁, m₁) ≠ (p₂ ^ e₂, m₂) := by
      intro heq
      obtain ⟨h1, h2⟩ := Prod.mk.inj heq
      apply hne
      rw [← hpe₁, ← hpe₂, h1, h2]
    have hsep := lemma2 hp₁ hp₂ he₁ he₂ hpm₁ hpm₂ hmlt₁ hmlt₂ hm0₁ hm0₂ h4₁ h4₂ hne_label
    unfold corrPair at hsep
    rwa [hpe₁, hpe₂] at hsep
  · -- correction pair vs. auxiliary pair
    have hmem : Iv.pair (q₁ * m₁) ∈ PstarPairs C.L :=
      ⟨q₁, m₁, hq₁, hLq₁, (C.I_range _ hq₁ hLq₁ m₁ hm₁).1, (C.I_range _ hq₁ hLq₁ m₁ hm₁).2, rfl⟩
    exact (C.A.sep_corr q₂ hq₂ hLq₂ a₂ ha₂ (Iv.pair (q₁ * m₁)) hmem).symm
  · -- auxiliary pair vs. correction pair
    have hmem : Iv.pair (q₂ * m₂) ∈ PstarPairs C.L :=
      ⟨q₂, m₂, hq₂, hLq₂, (C.I_range _ hq₂ hLq₂ m₂ hm₂).1, (C.I_range _ hq₂ hLq₂ m₂ hm₂).2, rfl⟩
    exact C.A.sep_corr q₁ hq₁ hLq₁ a₁ ha₁ (Iv.pair (q₂ * m₂)) hmem
  · -- auxiliary pair vs. auxiliary pair
    have hne' : (q₁, a₁) ≠ (q₂, a₂) := by
      intro heq
      obtain ⟨_, h2⟩ := Prod.mk.inj heq
      exact hne (by rw [h2])
    exact C.A.sep_aux q₁ q₂ hq₁ hLq₁ hq₂ hLq₂ a₁ ha₁ a₂ ha₂ hne'

/-! ## The prime-power cancellation step -/

/-- The heart of a single correction stage: given `DenBound q r`, either `q` already does not
divide the reduced denominator (and `S = ∅` works), or Lemma 3's covering set `S ⊆ I_q`
cancels the full power of `q` from the denominator (Lemma 1 / Cancel.lean). Either way we land
on `DenBound (q - 1)` after subtracting the correction pairs' masses for `S`. -/
theorem cancel_or_trivial (C : CorrectionData) (hL : 4 ≤ C.L) {q : ℕ}
    (hq : IsPrimePow q) (hLq : C.L < q) (r : ℚ) (hr : DenBound q r) :
    ∃ S ⊆ C.I q, S.card ≤ s q ∧ DenBound (q - 1) (r - ∑ m ∈ S, w (q * m)) := by
  classical
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff q).mp hq
  have hq5 : 5 ≤ q := by omega
  have hq0 : 0 < q := by omega
  by_cases hqdvd : q ∣ r.den
  · -- Case A: `q` divides the denominator; cancel it using Lemma 3.
    obtain ⟨v, hv_eq⟩ := hqdvd
    have hden_pos : 0 < r.den := Rat.pos r
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with rfl | h
      · simp at hv_eq
      · exact h
    have hpv : ¬ p ∣ v := by
      intro hpvdvd
      obtain ⟨v', hv'⟩ := hpvdvd
      have heq2 : r.den = p ^ (a + 1) * v' := by rw [hv_eq, hv', ← hpa]; ring
      have hdvd2 : p ^ (a + 1) ∣ r.den := ⟨v', heq2⟩
      have hple : p ^ (a + 1) ≤ q := hr p (a + 1) hp (by omega) hdvd2
      rw [← hpa, pow_succ] at hple
      have hpapos : 0 < p ^ a := pow_pos hp.pos a
      nlinarith [hp.two_le]
    obtain ⟨S, hS_sub, hS_card, hS_cong⟩ :=
      C.I_cover q hq hLq ((r.num : ZMod q) * (v : ZMod q)⁻¹)
    have hS0 : ∀ m ∈ S, 0 < m := fun m hm =>
      nat_pos_of_real_rpow_le hq0 (C.I_range q hq hLq m (hS_sub hm)).1
    have hSp : ∀ m ∈ S, ¬ p ∣ m := fun m hm =>
      not_dvd_of_coprime_of_dvd hp (hpa ▸ dvd_pow_self p ha.ne')
        (C.I_coprime q hq hLq m (hS_sub hm))
    have hcancel := cancel_step hp ha hpa.symm hv0 hpv S hS0 hSp hS_cong
    have hden_cast : (r.den : ℚ) = (q : ℚ) * (v : ℚ) := by exact_mod_cast hv_eq
    have hreq : r = (r.num : ℚ) / ((q : ℚ) * (v : ℚ)) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [hden_cast]
    have hcancel' : ¬ p ∣ (r - ∑ m ∈ S, w (q * m)).den := by rw [hreq]; exact hcancel
    have hDB1 : DenBound q (r - ∑ m ∈ S, w (q * m)) := by
      apply hr.sub
      apply DenBound.sum
      intro m hm
      have hmq' : m < p ^ a := by
        rw [hpa]
        exact lt_of_real_le_two_mul_rpow_tenth hq5 (C.I_range q hq hLq m (hS_sub hm)).2
      have hm0 : 0 < m := hS0 m hm
      have hpmm : ¬ p ∣ m := hSp m hm
      have hsmooth1 : Powersmooth q (q * m) := by
        intro l e hl he hdvd
        rw [← hpa] at hdvd
        have := primePow_dvd_mul_le hp hpmm hmq' hm0 hl he hdvd
        rwa [hpa] at this
      have hsmooth2 : Powersmooth q (q * m + 1) :=
        (C.I_smooth q hq hLq m (hS_sub hm)).mono (Nat.div_le_self q 2)
      exact DenBound.w hsmooth1 hsmooth2
    exact ⟨S, hS_sub, hS_card, DenBound.of_not_dvd_of_le hDB1 hpa.symm hp hcancel'⟩
  · -- Case B: `q` already does not divide the denominator.
    refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_⟩
    simp only [Finset.sum_empty, sub_zero]
    intro l e hl he hle
    have hlq : l ^ e ≤ q := hr l e hl he hle
    have hne : l ^ e ≠ q := by rintro rfl; exact hqdvd hle
    omega

/-! ## Mass bounds for individual stage pairs -/

/-- `q ^ (11/10) = q * q ^ (1/10)`. -/
theorem rpow_eleven_tenth {q : ℝ} (hq : 0 < q) :
    q ^ ((11 : ℝ) / 10) = q * q ^ ((1 : ℝ) / 10) := by
  have h : (11 : ℝ) / 10 = 1 + 1 / 10 := by norm_num
  rw [h, Real.rpow_add hq, Real.rpow_one]

/-- The mass of a correction pair `[qm, qm+1]` with `m ∈ I_q` is at most `2 q ^ (-11/10)`. -/
theorem corr_mass_le (C : CorrectionData) (hL : 4 ≤ C.L) {q m : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) (hm : m ∈ C.I q) :
    ((Iv.pair (q * m)).mass : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
  have hq0 : 0 < q := by omega
  have hm0 : 0 < m := nat_pos_of_real_rpow_le hq0 (C.I_range q hq hLq m hm).1
  have hmlow := (C.I_range q hq hLq m hm).1
  have hqm0 : 0 < q * m := Nat.mul_pos hq0 hm0
  have hstep1 : ((Iv.pair (q * m)).mass : ℝ) ≤ 2 / ((q * m : ℕ) : ℝ) := by
    have heq : (Iv.pair (q * m)).mass = w (q * m) := Iv.mass_pair (q * m)
    rw [heq]
    have hw := w_le hqm0
    have hw' : ((w (q * m) : ℚ) : ℝ) ≤ ((2 / ((q * m : ℕ) : ℚ) : ℚ) : ℝ) := by exact_mod_cast hw
    rwa [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at hw'
  have hqR0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hqR0' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqmR : (q : ℝ) ^ ((11 : ℝ) / 10) ≤ ((q * m : ℕ) : ℝ) := by
    rw [rpow_eleven_tenth hqR0']
    push_cast
    nlinarith [hmlow, hqR0]
  have hposL : (0 : ℝ) < (q : ℝ) ^ ((11 : ℝ) / 10) := by positivity
  have hposR : (0 : ℝ) < ((q * m : ℕ) : ℝ) := by exact_mod_cast hqm0
  have hstep2 : 2 / ((q * m : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
    have heq : (q : ℝ) ^ (-(11 : ℝ) / 10) = ((q : ℝ) ^ ((11 : ℝ) / 10))⁻¹ := by
      rw [show (-(11 : ℝ) / 10) = -((11 : ℝ) / 10) by ring, Real.rpow_neg hqR0]
    rw [heq, ← div_eq_mul_inv]
    gcongr
  linarith [hstep1, hstep2]

/-- The mass of an auxiliary pair `[a, a+1]` with `a ∈ F_q` is at most `2 q ^ (-11/10)`. -/
theorem aux_mass_le (C : CorrectionData) (hL : 4 ≤ C.L) {q a : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) (ha : a ∈ C.A.F q) :
    ((Iv.pair a).mass : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
  have hq0 : 0 < q := by omega
  have hqR0' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlow := C.A.lower q hq hLq a ha
  have ha0R : (0 : ℝ) < (a : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hqR0' _) hlow
  have ha0 : 0 < a := by exact_mod_cast ha0R
  have hstep1 : ((Iv.pair a).mass : ℝ) ≤ 2 / (a : ℝ) := by
    have heq : (Iv.pair a).mass = w a := Iv.mass_pair a
    rw [heq]
    have hw := w_le ha0
    have hw' : ((w a : ℚ) : ℝ) ≤ ((2 / (a : ℚ) : ℚ) : ℝ) := by exact_mod_cast hw
    rwa [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at hw'
  have hposL : (0 : ℝ) < (q : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_pos_of_pos hqR0' _
  have hstep2 : 2 / (a : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
    have heq : (q : ℝ) ^ (-(11 : ℝ) / 10) = ((q : ℝ) ^ ((11 : ℝ) / 10))⁻¹ := by
      rw [show (-(11 : ℝ) / 10) = -((11 : ℝ) / 10) by ring, Real.rpow_neg hqR0'.le]
    rw [heq, ← div_eq_mul_inv]
    gcongr
  linarith [hstep1, hstep2]

/-! ## A single correction stage -/

/-- Injectivity of `Iv.pair`. -/
theorem Iv.pair_injective : Function.Injective Iv.pair := fun x y h => by
  have := congrArg Iv.lo h
  simpa [Iv.pair] using this

/-- **A single stage of the correction procedure**: given a prime power `q > C.L` and a
deficit `r` with `DenBound q r`, there is a finset `P` of exactly `s q` stage pairs for `q`,
mutually separated, with `DenBound (q - 1)` on the remaining deficit, and total mass at most
`2 s(q) q^{-11/10}`. -/
theorem stage (C : CorrectionData) (hL : 4 ≤ C.L) {q : ℕ} (hq : IsPrimePow q) (hLq : C.L < q)
    (r : ℚ) (hr : DenBound q r) :
    ∃ P : Finset Iv,
      P.card = s q ∧
      (∀ I ∈ P, IsStagePair C q I) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      DenBound (q - 1) (r - ∑ I ∈ P, I.mass) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤ 2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
  classical
  have hq0 : 0 < q := by omega
  obtain ⟨S, hS_sub, hS_card, hDB⟩ := cancel_or_trivial C hL hq hLq r hr
  have hcardT : s q - S.card ≤ (C.A.F q).card := by rw [C.A.card_eq q hq hLq]; omega
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hcardT
  set corrSet := S.image (fun m => Iv.pair (q * m)) with hcorrSet_def
  set auxSet := T.image Iv.pair with hauxSet_def
  have hinj_corr : Function.Injective (fun m => Iv.pair (q * m)) :=
    Iv.pair_injective.comp (mul_right_injective₀ hq0.ne')
  have hcorr_card : corrSet.card = S.card := Finset.card_image_of_injective S hinj_corr
  have haux_card : auxSet.card = T.card := Finset.card_image_of_injective T Iv.pair_injective
  have hdisj : Disjoint corrSet auxSet := by
    rw [Finset.disjoint_left]
    rintro I hI1 hI2
    simp only [hcorrSet_def, hauxSet_def, Finset.mem_image] at hI1 hI2
    obtain ⟨m, hm, hmI⟩ := hI1
    obtain ⟨a, ha, haI⟩ := hI2
    have hmem : Iv.pair (q * m) ∈ PstarPairs C.L :=
      ⟨q, m, hq, hLq, (C.I_range q hq hLq m (hS_sub hm)).1,
        (C.I_range q hq hLq m (hS_sub hm)).2, rfl⟩
    have hsep := C.A.sep_corr q hq hLq a (hT_sub ha) (Iv.pair (q * m)) hmem
    have heqI : Iv.pair (q * m) = Iv.pair a := hmI.trans haI.symm
    rw [← heqI] at hsep
    exact Iv.pair_not_sep_self (q * m) hsep
  refine ⟨corrSet ∪ auxSet, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcorr_card, haux_card, hT_card]
    omega
  · intro I hI
    rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
    rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
    · exact Or.inl ⟨m, hS_sub hm, hmI.symm⟩
    · exact Or.inr ⟨a, hT_sub ha, haI.symm⟩
  · intro I hI J hJ hne
    have hIsp : IsStagePair C q I := by
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
      rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
      · exact Or.inl ⟨m, hS_sub hm, hmI.symm⟩
      · exact Or.inr ⟨a, hT_sub ha, haI.symm⟩
    have hJsp : IsStagePair C q J := by
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hJ
      rcases hJ with ⟨m, hm, hmJ⟩ | ⟨a, ha, haJ⟩
      · exact Or.inl ⟨m, hS_sub hm, hmJ.symm⟩
      · exact Or.inr ⟨a, hT_sub ha, haJ.symm⟩
    exact sep_of_stage_pairs C hL hq hLq hq hLq hIsp hJsp hne
  · have hsum_split : ∑ I ∈ corrSet ∪ auxSet, I.mass =
        (∑ m ∈ S, w (q * m)) + ∑ a ∈ T, w a := by
      rw [Finset.sum_union hdisj, hcorrSet_def, hauxSet_def,
        Finset.sum_image (fun x _ y _ h => hinj_corr h),
        Finset.sum_image (fun x _ y _ h => Iv.pair_injective h)]
      simp only [Iv.mass_pair]
    rw [hsum_split, ← sub_sub]
    apply hDB.sub
    apply DenBound.sum
    intro a ha
    have hsmooth1 : Powersmooth (q / 2) a := C.A.smooth_lo q hq hLq a (hT_sub ha)
    have hsmooth2 : Powersmooth (q / 2) (a + 1) := C.A.smooth_hi q hq hLq a (hT_sub ha)
    have hDBa : DenBound (q / 2) (w a) := DenBound.w hsmooth1 hsmooth2
    exact hDBa.mono (by omega)
  · have hbound : ∀ I ∈ corrSet ∪ auxSet, (I.mass : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
      intro I hI
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
      rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
      · rw [← hmI]; exact corr_mass_le C hL hq hLq (hS_sub hm)
      · rw [← haI]; exact aux_mass_le C hL hq hLq (hT_sub ha)
    calc ((∑ I ∈ corrSet ∪ auxSet, I.mass : ℚ) : ℝ)
        = ∑ I ∈ corrSet ∪ auxSet, (I.mass : ℝ) := by push_cast; rfl
      _ ≤ ∑ _I ∈ corrSet ∪ auxSet, 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := Finset.sum_le_sum hbound
      _ = (corrSet ∪ auxSet).card * (2 * (q : ℝ) ^ (-(11 : ℝ) / 10)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
          rw [Finset.card_union_of_disjoint hdisj, hcorr_card, haux_card, hT_card]
          have : S.card + (s q - S.card) = s q := by omega
          rw [this]; ring

/-- If the same interval `I` is a stage pair both for `q₁` and for `q₂` (with `q₁, q₂` prime
powers `> C.L`), then `q₁ = q₂`. Used to show that stage pairs for distinct prime powers are
always distinct intervals, hence that stages can be freely unioned. -/
theorem stage_pair_label_eq (C : CorrectionData) (hL : 4 ≤ C.L) {q₁ q₂ : ℕ}
    (hq₁ : IsPrimePow q₁) (hLq₁ : C.L < q₁) (hq₂ : IsPrimePow q₂) (hLq₂ : C.L < q₂)
    {I : Iv} (h1 : IsStagePair C q₁ I) (h2 : IsStagePair C q₂ I) : q₁ = q₂ := by
  have hq₁5 : 5 ≤ q₁ := by omega
  have hq₂5 : 5 ≤ q₂ := by omega
  rcases h1 with ⟨m₁, hm₁, hI1⟩ | ⟨a₁, ha₁, hI1⟩ <;>
    rcases h2 with ⟨m₂, hm₂, hI2⟩ | ⟨a₂, ha₂, hI2⟩
  · -- correction, correction
    obtain ⟨p₁, e₁, hp₁, he₁, hpe₁⟩ := (isPrimePow_nat_iff q₁).mp hq₁
    obtain ⟨p₂, e₂, hp₂, he₂, hpe₂⟩ := (isPrimePow_nat_iff q₂).mp hq₂
    have hpm₁ : ¬ p₁ ∣ m₁ := not_dvd_of_coprime_of_dvd hp₁ (hpe₁ ▸ dvd_pow_self p₁ he₁.ne')
      (C.I_coprime _ hq₁ hLq₁ m₁ hm₁)
    have hpm₂ : ¬ p₂ ∣ m₂ := not_dvd_of_coprime_of_dvd hp₂ (hpe₂ ▸ dvd_pow_self p₂ he₂.ne')
      (C.I_coprime _ hq₂ hLq₂ m₂ hm₂)
    have hmlt₁ : m₁ < p₁ ^ e₁ :=
      hpe₁ ▸ lt_of_real_le_two_mul_rpow_tenth hq₁5 (C.I_range _ hq₁ hLq₁ m₁ hm₁).2
    have hmlt₂ : m₂ < p₂ ^ e₂ :=
      hpe₂ ▸ lt_of_real_le_two_mul_rpow_tenth hq₂5 (C.I_range _ hq₂ hLq₂ m₂ hm₂).2
    have hm0₁ : 0 < m₁ := nat_pos_of_real_rpow_le (by omega) (C.I_range _ hq₁ hLq₁ m₁ hm₁).1
    have hm0₂ : 0 < m₂ := nat_pos_of_real_rpow_le (by omega) (C.I_range _ hq₂ hLq₂ m₂ hm₂).1
    have heqprod : q₁ * m₁ = q₂ * m₂ := Iv.pair_injective (hI1.symm.trans hI2)
    have heqprod' : p₁ ^ e₁ * m₁ = p₂ ^ e₂ * m₂ := by rw [hpe₁, hpe₂]; exact heqprod
    have hres := eq_of_mul_eq hp₁ hp₂ he₁ he₂ hpm₁ hpm₂ hmlt₁ hmlt₂ hm0₁ hm0₂ heqprod'
    rw [← hpe₁, ← hpe₂]; exact hres.1
  · -- correction, auxiliary: impossible
    exfalso
    have hmem : Iv.pair (q₁ * m₁) ∈ PstarPairs C.L :=
      ⟨q₁, m₁, hq₁, hLq₁, (C.I_range _ hq₁ hLq₁ m₁ hm₁).1, (C.I_range _ hq₁ hLq₁ m₁ hm₁).2, rfl⟩
    have hsep := C.A.sep_corr q₂ hq₂ hLq₂ a₂ ha₂ (Iv.pair (q₁ * m₁)) hmem
    have heq : Iv.pair (q₁ * m₁) = Iv.pair a₂ := hI1.symm.trans hI2
    rw [← heq] at hsep
    exact absurd hsep (Iv.pair_not_sep_self _)
  · -- auxiliary, correction: impossible
    exfalso
    have hmem : Iv.pair (q₂ * m₂) ∈ PstarPairs C.L :=
      ⟨q₂, m₂, hq₂, hLq₂, (C.I_range _ hq₂ hLq₂ m₂ hm₂).1, (C.I_range _ hq₂ hLq₂ m₂ hm₂).2, rfl⟩
    have hsep := C.A.sep_corr q₁ hq₁ hLq₁ a₁ ha₁ (Iv.pair (q₂ * m₂)) hmem
    have heq : Iv.pair a₁ = Iv.pair (q₂ * m₂) := hI1.symm.trans hI2
    rw [← heq] at hsep
    exact absurd hsep (Iv.pair_not_sep_self _)
  · -- auxiliary, auxiliary
    by_contra hne
    have ha12 : a₁ = a₂ := Iv.pair_injective (hI1.symm.trans hI2)
    have hne' : (q₁, a₁) ≠ (q₂, a₂) := fun heq2 => hne (Prod.mk.inj heq2).1
    have hsep := C.A.sep_aux q₁ q₂ hq₁ hLq₁ hq₂ hLq₂ a₁ ha₁ a₂ ha₂ hne'
    rw [ha12] at hsep
    exact absurd hsep (Iv.pair_not_sep_self _)

/-! ## Endpoint bookkeeping for stage pairs -/

/-- The endpoints of any stage pair for `q` lie in `U C.L C.A`. -/
theorem stagePair_mem_U (C : CorrectionData) {q : ℕ} (hq : IsPrimePow q) (hLq : C.L < q)
    {I : Iv} (hI : IsStagePair C q I) : I.lo ∈ U C.L C.A ∧ I.hi ∈ U C.L C.A := by
  rcases hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
  · exact ⟨Or.inl ⟨q, m, hq, hLq, (C.I_range q hq hLq m hm).1, (C.I_range q hq hLq m hm).2,
        Or.inl rfl⟩,
      Or.inl ⟨q, m, hq, hLq, (C.I_range q hq hLq m hm).1, (C.I_range q hq hLq m hm).2,
        Or.inr rfl⟩⟩
  · exact ⟨Or.inr ⟨q, hq, hLq, a, ha, Or.inl rfl⟩, Or.inr ⟨q, hq, hLq, a, ha, Or.inr rfl⟩⟩

/-- The right endpoint of any stage pair for `q` is at most `2 q ^ (11/10) + 1`. -/
theorem stagePair_hi_le (C : CorrectionData) (hL : 4 ≤ C.L) {q : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) {I : Iv} (hI : IsStagePair C q I) :
    (I.hi : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10) + 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  rcases hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
  · have hup := (C.I_range q hq hLq m hm).2
    show ((q * m + 1 : ℕ) : ℝ) ≤ _
    push_cast
    have hmul : (q : ℝ) * (m : ℝ) ≤ (q : ℝ) * (2 * (q : ℝ) ^ ((1 : ℝ) / 10)) :=
      mul_le_mul_of_nonneg_left hup hq0.le
    rw [rpow_eleven_tenth hq0]
    linarith
  · have hup := C.A.upper q hq hLq a ha
    show ((a + 1 : ℕ) : ℝ) ≤ _
    push_cast at hup ⊢
    linarith

/-! ## The recurrence for `CH` -/

/-- `C_{H+1} = C_H + s(H+1)` if `H + 1` is a prime power, else `C_{H+1} = C_H`. -/
theorem CH_succ (L H : ℕ) (hLH : L ≤ H) :
    CH L (H + 1) = CH L H + (if IsPrimePow (H + 1) then s (H + 1) else 0) := by
  simp only [CH, Finset.sum_filter]
  rw [Finset.sum_Icc_succ_top (by omega : L + 1 ≤ H + 1)]

/-! ## The induction -/

/-- The inductive form of `descent`, with `H ≥ C.L` (allowing the base case `H = C.L`) and an
explicit stage-by-stage bound on the total mass, strong enough to carry through the induction. -/
theorem descent' (C : CorrectionData) (hL : 4 ≤ C.L) :
    ∀ H, C.L ≤ H → ∀ r₀ : ℚ, DenBound H r₀ →
    ∃ P : Finset Iv,
      P.card = CH C.L H ∧
      (∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ H ∧ IsStagePair C q I) ∧
      (∀ I ∈ P, I.lo ∈ U C.L C.A ∧ I.hi ∈ U C.L C.A) ∧
      (∀ I ∈ P, 4 ∣ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 2 * (H : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤
        ∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
          2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) ∧
      DenBound C.L (r₀ - ∑ I ∈ P, I.mass) := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base =>
    intro r₀ hr₀
    refine ⟨∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [CH]
    · simp
    · simp
    · simp
    · simp
    · simp
    · simpa using hr₀
  | succ H hH IH =>
    intro r₀ hr₀
    by_cases hpp : IsPrimePow (H + 1)
    · have hLq' : C.L < H + 1 := by omega
      obtain ⟨Pq, hPq_card, hPq_mem, hPq_sep, hPq_DB, hPq_mass⟩ := stage C hL hpp hLq' r₀ hr₀
      have hDBr1 : DenBound H (r₀ - ∑ I ∈ Pq, I.mass) := by
        have hHeq : H + 1 - 1 = H := by omega
        rwa [hHeq] at hPq_DB
      obtain ⟨P', hP'_card, hP'_mem, hP'_UU, hP'_end, hP'_sep, hP'_mass, hP'_DB⟩ :=
        IH (r₀ - ∑ I ∈ Pq, I.mass) hDBr1
      have hdisj : Disjoint Pq P' := by
        rw [Finset.disjoint_left]
        intro I hI hI'
        obtain ⟨q', hq', hLq'', hqH', hsp'⟩ := hP'_mem I hI'
        have hlabel := stage_pair_label_eq C hL hpp hLq' hq' hLq'' (hPq_mem I hI) hsp'
        omega
      have hsumeq : ∑ I ∈ Pq ∪ P', I.mass = ∑ I ∈ Pq, I.mass + ∑ I ∈ P', I.mass :=
        Finset.sum_union hdisj
      have hHmono : (H : ℝ) ^ ((11 : ℝ) / 10) ≤ ((H : ℝ) + 1) ^ ((11 : ℝ) / 10) := by
        apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      refine ⟨Pq ∪ P', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hPq_card, hP'_card, CH_succ C.L H hH, if_pos hpp]
        omega
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · exact ⟨H + 1, hpp, hLq', le_refl _, hPq_mem I hI⟩
        · obtain ⟨q', hq', hLq'', hqH', hsp'⟩ := hP'_mem I hI
          exact ⟨q', hq', hLq'', by omega, hsp'⟩
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · exact stagePair_mem_U C hpp hLq' (hPq_mem I hI)
        · exact hP'_UU I hI
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · rcases hPq_mem I hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
          · exact ⟨C.I_four (H + 1) hpp hLq' m hm, rfl,
              stagePair_hi_le C hL hpp hLq' (Or.inl ⟨m, hm, rfl⟩)⟩
          · exact ⟨C.A.four_dvd (H + 1) hpp hLq' a ha, rfl,
              stagePair_hi_le C hL hpp hLq' (Or.inr ⟨a, ha, rfl⟩)⟩
        · obtain ⟨h4, hhi, hend⟩ := hP'_end I hI
          exact ⟨h4, hhi, by push_cast at hend ⊢; linarith⟩
      · intro I hI J hJ hne
        rw [Finset.mem_union] at hI hJ
        rcases hI with hI | hI <;> rcases hJ with hJ | hJ
        · exact hPq_sep I hI J hJ hne
        · obtain ⟨q', hq', hLq'', hqH', hsp'⟩ := hP'_mem J hJ
          exact sep_of_stage_pairs C hL hpp hLq' hq' hLq'' (hPq_mem I hI) hsp' hne
        · obtain ⟨q', hq', hLq'', hqH', hsp'⟩ := hP'_mem I hI
          exact sep_of_stage_pairs C hL hq' hLq'' hpp hLq' hsp' (hPq_mem J hJ) hne
        · exact hP'_sep I hI J hJ hne
      · rw [hsumeq]
        have hPq_mass' := hPq_mass
        have hP'_mass' := hP'_mass
        push_cast at hPq_mass' hP'_mass' ⊢
        have hsum_succ :
            ∑ q ∈ (Finset.Icc (C.L + 1) (H + 1)).filter IsPrimePow,
                2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) =
              (∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
                  2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10)) +
                2 * (s (H + 1) : ℝ) * ((H : ℝ) + 1) ^ (-(11 : ℝ) / 10) := by
          simp only [Finset.sum_filter]
          rw [Finset.sum_Icc_succ_top (by omega : C.L + 1 ≤ H + 1), if_pos hpp]
          push_cast
          ring
        rw [hsum_succ]
        linarith [hPq_mass', hP'_mass']
      · rw [hsumeq, ← sub_sub]
        exact hP'_DB
    · have hDB' : DenBound H r₀ := by
        intro l e hl he hle
        have hle' := hr₀ l e hl he hle
        have hne : l ^ e ≠ H + 1 := by
          intro heq
          exact hpp ((isPrimePow_nat_iff _).mpr ⟨l, e, hl, he, heq⟩)
        omega
      obtain ⟨P', hP'_card, hP'_mem, hP'_UU, hP'_end, hP'_sep, hP'_mass, hP'_DB⟩ := IH r₀ hDB'
      have hHmono : (H : ℝ) ^ ((11 : ℝ) / 10) ≤ ((H : ℝ) + 1) ^ ((11 : ℝ) / 10) := by
        apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      refine ⟨P', ?_, ?_, ?_, ?_, hP'_sep, ?_, hP'_DB⟩
      · rw [hP'_card, CH_succ C.L H hH, if_neg hpp, add_zero]
      · intro I hI
        obtain ⟨q', hq', hLq'', hqH', hsp'⟩ := hP'_mem I hI
        exact ⟨q', hq', hLq'', by omega, hsp'⟩
      · exact hP'_UU
      · intro I hI
        obtain ⟨h4, hhi, hend⟩ := hP'_end I hI
        refine ⟨h4, hhi, ?_⟩
        push_cast at hend ⊢
        linarith
      · have hmono : ∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
              2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) ≤
            ∑ q ∈ (Finset.Icc (C.L + 1) (H + 1)).filter IsPrimePow,
              2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · apply Finset.filter_subset_filter
            intro x hx
            simp only [Finset.mem_Icc] at hx ⊢
            omega
          · intro i _ _; positivity
        linarith [hP'_mass, hmono]

/-- **The correction procedure** (Section 4). For correction data `C` with cutoff `L`, every
`H > L`, and every deficit `r₀` with `DenBound H r₀`, there is a finset `P` of pairs such that:
* `|P| = C_H` exactly;
* every pair in `P` is a correction pair `[qm, qm+1]` with `m ∈ I_q` or an auxiliary pair from
  `F_q`, for some prime power `q ∈ (L, H]`; in particular both endpoints lie in `U`;
* every pair starts at a multiple of `4` and ends at most `2 H^{11/10} + 1`;
* the pairs are mutually separated;
* the total mass is at most `40 L^{-1/20}`;
* the corrected deficit `r₀ - ∑ mass` has `DenBound L`. -/
theorem descent (C : CorrectionData) (hL : 4 ≤ C.L) (H : ℕ) (hH : C.L < H) (r₀ : ℚ)
    (hr₀ : DenBound H r₀) :
    ∃ P : Finset Iv,
      P.card = CH C.L H ∧
      (∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ H ∧
        ((∃ m ∈ C.I q, I = Iv.pair (q * m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a))) ∧
      (∀ I ∈ P, I.lo ∈ U C.L C.A ∧ I.hi ∈ U C.L C.A) ∧
      (∀ I ∈ P, 4 ∣ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 2 * (H : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤ 40 * (C.L : ℝ) ^ (-(1 : ℝ) / 20) ∧
      DenBound C.L (r₀ - ∑ I ∈ P, I.mass) := by
  obtain ⟨P, hcard, hmem, hUU, hend, hsep, hmass, hDB⟩ := descent' C hL H hH.le r₀ hr₀
  refine ⟨P, hcard, ?_, hUU, hend, hsep, ?_, hDB⟩
  · intro I hI
    obtain ⟨q, hq, hLq, hqH, hsp⟩ := hmem I hI
    exact ⟨q, hq, hLq, hqH, hsp⟩
  · calc ((∑ I ∈ P, I.mass : ℚ) : ℝ)
        ≤ ∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
            2 * (s q : ℝ) * (q : ℝ) ^ (-(11 : ℝ) / 10) := hmass
      _ ≤ 40 * (C.L : ℝ) ^ (-(1 : ℝ) / 20) := sum_stage_mass_le C.L H (by omega)

/-- **(4.8)**: `C_H ≤ H^{21/20}`. -/
theorem CH_le (L H : ℕ) : (CH L H : ℝ) ≤ (H : ℝ) ^ ((21 : ℝ) / 20) := by
  unfold CH s
  exact_mod_cast sum_rpow_le L H

end Erdos289
