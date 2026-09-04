import Erdos289.SignedDefs
import Erdos289.Descent
import Erdos289.SignedTail
import Erdos289.SignedCancel

/-!
# Section 4 (signed version): the correction procedure with signed fibers

The elementary replacement of the correction procedure (`docs/elementary_replacements.md`,
Section 4): correction pairs are the signed pairs `{q m, q m + σ}` from the compatible fibers of
Lemmas F1–F2, auxiliary pairs come from an `AuxFamilyS`, cancellation uses the signed identity (D3),
and the mass bound is (D5). The statements mirror `Erdos289.CorrectionData` / `Erdos289.descent`.
-/

namespace Erdos289

open Finset

/-- The data fixed for one run of the signed correction procedure, for the cutoff `L` and the
upper label `H`: an auxiliary family avoiding the enlarged endpoint set, signed fibers for every
label, and the retained sub-fibers `J q ⊆ (F q).I` of Lemma F2 (mutually separated, large, and
covering every residue by at most `s q` inverses via the covering lemma with `C = 8`). -/
structure CorrectionDataS (ε : ℝ) where
  L : ℕ
  H : ℕ
  LH : L ≤ H
  A : AuxFamilyS ε L
  /-- Signed fibers at every label (Lemma F1). -/
  F : (q : ℕ) → SignedFiber ε q
  /-- Retained multipliers (Lemma F2). -/
  J : ℕ → Finset ℕ
  J_sub : ∀ q, J q ⊆ (F q).I
  J_card : ∀ q, IsPrimePow q → L < q → q ≤ H → (q : ℝ) ^ (7 * ε / 8) ≤ ((J q).card : ℝ)
  J_sep : ∀ q q' : ℕ, IsPrimePow q → L < q → q ≤ H → IsPrimePow q' → L < q' → q' ≤ H →
    ∀ m ∈ J q, ∀ m' ∈ J q', (q, m) ≠ (q', m') →
      Iv.Sep (signedPair q m ((F q).σ m)) (signedPair q' m' ((F q').σ m'))
  /-- Covering: every residue is a sum of at most `s q` inverses of retained multipliers. -/
  cover : ∀ q, IsPrimePow q → L < q → q ≤ H → ∀ r : ZMod q,
    ∃ S ⊆ J q, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r
  /-- The divisor envelope is small beyond the cutoff (docs, before display (D4)). -/
  E_small : ∀ q, IsPrimePow q → L < q → Eenv ε q ≤ (q : ℝ) ^ ((1 : ℝ) / 40)

/-! ## Helper lemmas, kept in `Erdos289.DescentS` -/

namespace DescentS

open SignedCancel

/-! ### Small real-analytic facts about `Venv`/`Eenv` -/

/-- `Venv ε q ≥ 1` for `q ≥ 1`: `n = 1` always contributes to the divisor-count supremum. -/
theorem venv_ge_one (ε : ℝ) (q : ℕ) (hq : 1 ≤ q) : 1 ≤ Venv ε q := by
  unfold Venv
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hpow_pos : (0 : ℝ) < 25 * (q : ℝ) ^ (1 + ε) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hqpos _)
  have hceil_pos : 0 < ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ := Nat.ceil_pos.mpr hpow_pos
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ :=
    Finset.mem_Icc.mpr ⟨le_refl 1, hceil_pos⟩
  have hle := Finset.le_sup (f := fun n => n.divisors.card) hmem
  simpa [Nat.divisors_one, Finset.card_singleton] using hle

/-- `1 < log q` for `q ≥ 3` (from `exp 1 < 3`). -/
theorem one_lt_log_of_three_le {q : ℕ} (hq : 3 ≤ q) : 1 < Real.log q := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have he3 : Real.exp 1 < (q : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three hqR
  have hlt := Real.log_lt_log (Real.exp_pos 1) he3
  rwa [Real.log_exp] at hlt

/-- `Eenv (1/10) q > 0` for `q ≥ 3`. -/
theorem eenv_pos {q : ℕ} (hq3 : 3 ≤ q) : 0 < Eenv (1 / 10) q := by
  unfold Eenv
  have hV := venv_ge_one (1 / 10) q (by omega)
  have hVR : (0 : ℝ) < (Venv (1 / 10) q : ℝ) := by exact_mod_cast (by omega : 0 < Venv (1/10) q)
  have hlog := one_lt_log_of_three_le hq3
  exact mul_pos (pow_pos hVR 2) (by linarith)

/-- `Eenv (1/10) q ≥ 1` for `q ≥ 3`. -/
theorem eenv_ge_one {q : ℕ} (hq3 : 3 ≤ q) : 1 ≤ Eenv (1 / 10) q := by
  unfold Eenv
  have hV := venv_ge_one (1 / 10) q (by omega)
  have hVR : (1 : ℝ) ≤ (Venv (1 / 10) q : ℝ) := by exact_mod_cast hV
  have hVsq : (1 : ℝ) ≤ (Venv (1 / 10) q : ℝ) ^ 2 := by nlinarith
  have hlog := one_lt_log_of_three_le hq3
  nlinarith [hVsq, hlog]

/-! ### Basic facts about `signedPair` -/

/-- The right endpoint of a signed pair is always the left endpoint plus one. -/
theorem signedPair_hi_eq_lo_succ (q m : ℕ) (σ : ℤ) :
    (signedPair q m σ).hi = (signedPair q m σ).lo + 1 := by
  unfold signedPair; split_ifs <;> rfl

/-- Both endpoints of a signed pair at a valid multiplier lie in `PstarSigned`. -/
theorem signedPair_mem_PstarSigned {ε : ℝ} {L q m : ℕ} (σ : ℤ)
    (hq : IsPrimePow q) (hLq : L < q) (hlow : Rq ε q ≤ m) (hup : (m : ℝ) ≤ 8 * (q : ℝ) ^ ε)
    (h2 : 2 ≤ q * m) :
    (signedPair q m σ).lo ∈ PstarSigned ε L ∧ (signedPair q m σ).hi ∈ PstarSigned ε L := by
  unfold signedPair
  split_ifs with hσ
  · exact ⟨⟨q, m, hq, hLq, hlow, hup, Or.inr (Or.inl rfl)⟩,
      ⟨q, m, hq, hLq, hlow, hup, Or.inr (Or.inr rfl)⟩⟩
  · have he : q * m - 1 + 1 = q * m := by omega
    exact ⟨⟨q, m, hq, hLq, hlow, hup, Or.inl rfl⟩,
      ⟨q, m, hq, hLq, hlow, hup, Or.inr (Or.inl he)⟩⟩

/-- `m ↦ signedPair q m (σ m)` is injective on any finite set of multipliers `m` with
`2 ≤ q * m` (for `q ≥ 2`). -/
theorem signedPair_injOn {q : ℕ} (hq2 : 2 ≤ q) (σ : ℕ → ℤ) {S : Finset ℕ}
    (h2 : ∀ m ∈ S, 2 ≤ q * m) : Set.InjOn (fun m => signedPair q m (σ m)) S := by
  intro m₁ hm₁ m₂ hm₂ heq
  have hlo : (signedPair q m₁ (σ m₁)).lo = (signedPair q m₂ (σ m₂)).lo := congrArg Iv.lo heq
  have h2₁ := h2 m₁ hm₁
  have h2₂ := h2 m₂ hm₂
  have hcast : ∀ m : ℕ, 2 ≤ q * m →
      ∃ c : ℤ, (c = 0 ∨ c = 1) ∧
        ((signedPair q m (σ m)).lo : ℤ) = (q : ℤ) * (m : ℤ) - c := by
    intro m hm
    unfold signedPair
    split_ifs with h
    · exact ⟨0, Or.inl rfl, by show ((q * m : ℕ) : ℤ) = (q : ℤ) * (m : ℤ) - 0; push_cast; ring⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      have h1 : (1 : ℕ) ≤ q * m := by omega
      show ((q * m - 1 : ℕ) : ℤ) = (q : ℤ) * (m : ℤ) - 1
      rw [Nat.cast_sub h1]; push_cast; ring
  obtain ⟨c₁, hc₁, e1⟩ := hcast m₁ h2₁
  obtain ⟨c₂, hc₂, e2⟩ := hcast m₂ h2₂
  rw [hlo] at e1
  have heqZ : (q : ℤ) * (m₁ : ℤ) - c₁ = (q : ℤ) * (m₂ : ℤ) - c₂ := by rw [← e1, e2]
  have hqZ : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
  have hm12 : (m₁ : ℤ) = (m₂ : ℤ) := by
    by_contra hne
    have hne' : (m₁ : ℤ) - (m₂ : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have habs : 1 ≤ |(m₁ : ℤ) - (m₂ : ℤ)| := Int.one_le_abs hne'
    have hdiff : (q : ℤ) * ((m₁ : ℤ) - (m₂ : ℤ)) = c₁ - c₂ := by linarith [heqZ]
    have habsq : (q : ℤ) ≤ |(q : ℤ) * ((m₁ : ℤ) - (m₂ : ℤ))| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < (q:ℤ))]
      nlinarith [habs]
    rw [hdiff] at habsq
    rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> simp at habsq <;> linarith
  exact_mod_cast hm12

/-! ### Separation facts -/

/-- A signed correction pair is separated from any auxiliary pair from a (possibly different)
label, using `AuxFamilyS.avoid`. -/
theorem sep_corr_aux_signed {ε : ℝ} {L q q' : ℕ} (A : AuxFamilyS ε L) (σ : ℤ)
    {m a : ℕ} (hq : IsPrimePow q) (hLq : L < q) (hlow : Rq ε q ≤ m) (hup : (m : ℝ) ≤ 8 * (q : ℝ) ^ ε)
    (h2 : 2 ≤ q * m) (hq' : IsPrimePow q') (hLq' : L < q') (ha : a ∈ A.F q') :
    Iv.Sep (signedPair q m σ) (Iv.pair a) := by
  have hmem := (signedPair_mem_PstarSigned σ hq hLq hlow hup h2).1
  have havoid := A.avoid q' hq' hLq' a ha _ hmem
  have hhi := signedPair_hi_eq_lo_succ q m σ
  unfold Iv.Sep
  show (signedPair q m σ).hi + 1 < (Iv.pair a).lo ∨ (Iv.pair a).hi + 1 < (signedPair q m σ).lo
  simp only [Iv.pair]
  omega

/-- A pair produced at stage `q` of the signed correction procedure: either a retained signed
correction pair `{q m, q m + σ}` with `m ∈ J q`, or an auxiliary pair `[a, a+1]` with `a ∈ F q`. -/
def IsStagePairS (C : CorrectionDataS ((1 : ℝ) / 10)) (q : ℕ) (I : Iv) : Prop :=
  (∃ m ∈ C.J q, I = signedPair q m ((C.F q).σ m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a)

/-- Any two distinct stage pairs, possibly from different stages `q₁ ≠ q₂`, are separated. -/
theorem sep_of_stage_pairs_signed (C : CorrectionDataS ((1 : ℝ) / 10))
    {q₁ q₂ : ℕ} (hq₁ : IsPrimePow q₁) (hLq₁ : C.L < q₁) (hqH₁ : q₁ ≤ C.H)
    (hq₂ : IsPrimePow q₂) (hLq₂ : C.L < q₂) (hqH₂ : q₂ ≤ C.H)
    {I J : Iv} (hI : IsStagePairS C q₁ I) (hJ : IsStagePairS C q₂ J) (hne : I ≠ J) :
    Iv.Sep I J := by
  rcases hI with ⟨m₁, hm₁, rfl⟩ | ⟨a₁, ha₁, rfl⟩ <;>
    rcases hJ with ⟨m₂, hm₂, rfl⟩ | ⟨a₂, ha₂, rfl⟩
  · apply C.J_sep q₁ q₂ hq₁ hLq₁ hqH₁ hq₂ hLq₂ hqH₂ m₁ hm₁ m₂ hm₂
    intro heq
    apply hne
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    subst h1; subst h2; rfl
  · have hmem₁ := C.J_sub q₁ hm₁
    exact sep_corr_aux_signed C.A ((C.F q₁).σ m₁) hq₁ hLq₁ ((C.F q₁).lower m₁ hmem₁)
      ((C.F q₁).upper m₁ hmem₁) ((C.F q₁).two_le m₁ hmem₁) hq₂ hLq₂ ha₂
  · have hmem₂ := C.J_sub q₂ hm₂
    exact (sep_corr_aux_signed C.A ((C.F q₂).σ m₂) hq₂ hLq₂ ((C.F q₂).lower m₂ hmem₂)
      ((C.F q₂).upper m₂ hmem₂) ((C.F q₂).two_le m₂ hmem₂) hq₁ hLq₁ ha₁).symm
  · apply C.A.sep_aux q₁ q₂ hq₁ hLq₁ hq₂ hLq₂ a₁ ha₁ a₂ ha₂
    intro heq
    apply hne
    have ha12 : a₁ = a₂ := (Prod.mk.inj heq).2
    rw [ha12]

/-- If the same interval `I` is a stage pair both for `q₁` and for `q₂`, then `q₁ = q₂`. -/
theorem stage_pair_labelS_eq (C : CorrectionDataS ((1 : ℝ) / 10))
    {q₁ q₂ : ℕ} (hq₁ : IsPrimePow q₁) (hLq₁ : C.L < q₁) (hqH₁ : q₁ ≤ C.H)
    (hq₂ : IsPrimePow q₂) (hLq₂ : C.L < q₂) (hqH₂ : q₂ ≤ C.H)
    {I : Iv} (h1 : IsStagePairS C q₁ I) (h2 : IsStagePairS C q₂ I) : q₁ = q₂ := by
  by_contra hne
  rcases h1 with ⟨m₁, hm₁, hI1⟩ | ⟨a₁, ha₁, hI1⟩ <;>
    rcases h2 with ⟨m₂, hm₂, hI2⟩ | ⟨a₂, ha₂, hI2⟩
  · have hne' : (q₁, m₁) ≠ (q₂, m₂) := fun heq => hne (Prod.mk.inj heq).1
    have hsep := C.J_sep q₁ q₂ hq₁ hLq₁ hqH₁ hq₂ hLq₂ hqH₂ m₁ hm₁ m₂ hm₂ hne'
    rw [← hI1, ← hI2] at hsep
    have hhi : I.hi = I.lo + 1 := by rw [hI2]; exact signedPair_hi_eq_lo_succ q₂ m₂ _
    unfold Iv.Sep at hsep
    omega
  · exfalso
    have hmem₁ := C.J_sub q₁ hm₁
    have hsep := sep_corr_aux_signed C.A ((C.F q₁).σ m₁) hq₁ hLq₁ ((C.F q₁).lower m₁ hmem₁)
      ((C.F q₁).upper m₁ hmem₁) ((C.F q₁).two_le m₁ hmem₁) hq₂ hLq₂ ha₂
    rw [← hI1, ← hI2] at hsep
    have hhi : I.hi = I.lo + 1 := by rw [hI1]; exact signedPair_hi_eq_lo_succ q₁ m₁ _
    unfold Iv.Sep at hsep
    omega
  · exfalso
    have hmem₂ := C.J_sub q₂ hm₂
    have hsep := sep_corr_aux_signed C.A ((C.F q₂).σ m₂) hq₂ hLq₂ ((C.F q₂).lower m₂ hmem₂)
      ((C.F q₂).upper m₂ hmem₂) ((C.F q₂).two_le m₂ hmem₂) hq₁ hLq₁ ha₁
    rw [← hI2, ← hI1] at hsep
    have hhi : I.hi = I.lo + 1 := by rw [hI2]; exact signedPair_hi_eq_lo_succ q₂ m₂ _
    unfold Iv.Sep at hsep
    omega
  · have ha12 : a₁ = a₂ := Iv.pair_injective (hI1.symm.trans hI2)
    have hne' : (q₁, a₁) ≠ (q₂, a₂) := fun heq2 => hne (Prod.mk.inj heq2).1
    have hsep := C.A.sep_aux q₁ q₂ hq₁ hLq₁ hq₂ hLq₂ a₁ ha₁ a₂ ha₂ hne'
    rw [ha12] at hsep
    exact absurd hsep (Iv.pair_not_sep_self _)

/-! ### Mass bounds for individual stage pairs -/

/-- The mass of a signed correction pair `{q m, q m + σ}` is at most `3 * Eenv (1/10) q * q^{-11/10}`. -/
theorem corrS_mass_le {q m : ℕ} (hq3 : 3 ≤ q) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m)
    (hlow : Rq (1 / 10) q ≤ m) :
    ((signedPair q m σ).mass : ℝ) ≤ 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
  have hq0 : 0 < q := by omega
  have hqR0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hEpos : 0 < Eenv (1 / 10) q := eenv_pos hq3
  have hmass_le : ((signedPair q m σ).mass : ℝ) ≤ 3 / ((q * m : ℕ) : ℝ) := by
    have heq : (signedPair q m σ).mass = wSigned q m σ := (wSigned_eq hσ h2).symm
    rw [heq]
    have hb := wSigned_le h2 hσ
    have hbR : ((wSigned q m σ : ℚ) : ℝ) ≤ ((3 / (q * m : ℚ) : ℚ) : ℝ) := by exact_mod_cast hb
    have hcast_eq : ((3 / (q * m : ℚ) : ℚ) : ℝ) = 3 / ((q * m : ℕ) : ℝ) := by push_cast; ring
    rwa [hcast_eq] at hbR
  have hstep : (q : ℝ) ^ ((1 : ℝ) / 10) ≤ (m : ℝ) * Eenv (1 / 10) q := by
    have hRqm : Rq (1 / 10) q ≤ (m : ℝ) := hlow
    unfold Rq at hRqm
    rw [div_le_iff₀ hEpos] at hRqm
    linarith [hRqm]
  have hqmE : (q : ℝ) ^ ((11 : ℝ) / 10) ≤ ((q * m : ℕ) : ℝ) * Eenv (1 / 10) q := by
    push_cast
    rw [rpow_eleven_tenth hqR0]
    calc (q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 10)
        ≤ (q : ℝ) * ((m : ℝ) * Eenv (1 / 10) q) :=
          mul_le_mul_of_nonneg_left hstep hqR0.le
      _ = (q : ℝ) * (m : ℝ) * Eenv (1 / 10) q := by ring
  have hfinal : 3 / ((q * m : ℕ) : ℝ) ≤ 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
    have hqm0 : (0 : ℝ) < ((q * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q * m)
    have hqR11pos : (0 : ℝ) < (q : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_pos_of_pos hqR0 _
    rw [show (q : ℝ) ^ (-(11 : ℝ) / 10) = ((q : ℝ) ^ ((11 : ℝ) / 10))⁻¹ by
          rw [show (-(11 : ℝ) / 10) = -((11 : ℝ) / 10) by ring, Real.rpow_neg hqR0.le],
        ← div_eq_mul_inv, div_le_div_iff₀ hqm0 hqR11pos]
    nlinarith [hqmE]
  linarith [hmass_le, hfinal]

/-- The mass of an auxiliary pair `[a, a+1]` with `a ∈ F q` is at most
`3 * Eenv (1/10) q * q^{-11/10}`. -/
theorem auxS_mass_le {q a : ℕ} (hq3 : 3 ≤ q) (hlow : (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) :
    ((Iv.pair a).mass : ℝ) ≤ 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
  have hq0 : 0 < q := by omega
  have hqR0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hEge1 : 1 ≤ Eenv (1 / 10) q := eenv_ge_one hq3
  have ha0R : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hqR0 _) hlow
  have ha0 : 0 < a := by exact_mod_cast ha0R
  have hstep1 : ((Iv.pair a).mass : ℝ) ≤ 2 / (a : ℝ) := by
    have heq : (Iv.pair a).mass = w a := mass_pair a
    rw [heq]
    have hw := w_le ha0
    have hw' : ((w a : ℚ) : ℝ) ≤ ((2 / (a : ℚ) : ℚ) : ℝ) := by exact_mod_cast hw
    rwa [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at hw'
  have hstep2 : 2 / (a : ℝ) ≤ 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
    have heq : (q : ℝ) ^ (-(11 : ℝ) / 10) = ((q : ℝ) ^ ((11 : ℝ) / 10))⁻¹ := by
      rw [show (-(11 : ℝ) / 10) = -((11 : ℝ) / 10) by ring, Real.rpow_neg hqR0.le]
    rw [heq, ← div_eq_mul_inv]
    gcongr
  have hstep3 : 2 * (q : ℝ) ^ (-(11 : ℝ) / 10) ≤ 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
    have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(11 : ℝ) / 10) := Real.rpow_nonneg hqR0.le _
    nlinarith [hpos, hEge1]
  linarith [hstep1, hstep2, hstep3]

/-! ### The prime-power cancellation step -/

/-- The signed analogue of `Erdos289.cancel_or_trivial`. -/
theorem cancel_or_trivial_signed (C : CorrectionDataS ((1 : ℝ) / 10)) {q : ℕ}
    (hq : IsPrimePow q) (hLq : C.L < q) (hqH : q ≤ C.H) (r : ℚ) (hr : DenBound q r) :
    ∃ S ⊆ C.J q, S.card ≤ s q ∧
      DenBound (q - 1) (r - ∑ m ∈ S, wSigned q m ((C.F q).σ m)) := by
  classical
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff q).mp hq
  have hq0 : 0 < q := by omega
  by_cases hqdvd : q ∣ r.den
  · obtain ⟨v, hv_eq⟩ := hqdvd
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
      C.cover q hq hLq hqH ((r.num : ZMod q) * (v : ZMod q)⁻¹)
    have hS0 : ∀ m ∈ S, 0 < m := fun m hm => by
      have h2 := (C.F q).two_le m (C.J_sub q (hS_sub hm))
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp at h2
      · exact hm0
    have hSp : ∀ m ∈ S, ¬ p ∣ m := fun m hm =>
      not_dvd_of_coprime_of_dvd hp (hpa ▸ dvd_pow_self p ha.ne')
        ((C.F q).coprime m (C.J_sub q (hS_sub hm)))
    have hSσ : ∀ m ∈ S, (C.F q).σ m = 1 ∨ (C.F q).σ m = -1 := fun m hm =>
      (C.F q).sign m (C.J_sub q (hS_sub hm))
    have hcancel := cancel_step_signed hp ha hpa.symm hv0 hpv S (C.F q).σ hSσ hS0 hSp hS_cong
    have hden_cast : (r.den : ℚ) = (q : ℚ) * (v : ℚ) := by exact_mod_cast hv_eq
    have hreq : r = (r.num : ℚ) / ((q : ℚ) * (v : ℚ)) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [hden_cast]
    have hcancel' : ¬ p ∣ (r - ∑ m ∈ S, wSigned q m ((C.F q).σ m)).den := by
      rw [hreq]; exact hcancel
    have hDB1 : DenBound q (r - ∑ m ∈ S, wSigned q m ((C.F q).σ m)) := by
      apply hr.sub
      apply DenBound.sum
      intro m hm
      have hmem := C.J_sub q (hS_sub hm)
      have hm0 : 0 < m := hS0 m hm
      have hpmm : ¬ p ∣ m := hSp m hm
      have hmq' : m < p ^ a := by rw [hpa]; exact (C.F q).lt m hmem
      have hqm2 : 2 ≤ q * m := (C.F q).two_le m hmem
      have hsmooth1 : Powersmooth q (q * m) := by
        intro l e hl he hdvd
        rw [← hpa] at hdvd
        have := primePow_dvd_mul_le hp hpmm hmq' hm0 hl he hdvd
        rwa [hpa] at this
      have hsmooth2 : Powersmooth q (neighbor q m ((C.F q).σ m)) :=
        SignedCancel.powersmooth_mono ((C.F q).smooth m hmem) (by omega)
      rw [SignedCancel.wSigned_eq_neighbor (hSσ m hm) hqm2]
      exact (DenBound.one_div hsmooth1).add (DenBound.one_div hsmooth2)
    exact ⟨S, hS_sub, hS_card, DenBound.of_not_dvd_of_le hDB1 hpa.symm hp hcancel'⟩
  · refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_⟩
    simp only [Finset.sum_empty, sub_zero]
    intro l e hl he hle
    have hlq : l ^ e ≤ q := hr l e hl he hle
    have hne : l ^ e ≠ q := by rintro rfl; exact hqdvd hle
    omega

/-! ## Endpoint bookkeeping for stage pairs -/

theorem stagePairS_mem_U (C : CorrectionDataS ((1 : ℝ) / 10)) {q : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) {I : Iv} (hI : IsStagePairS C q I) :
    I.lo ∈ USigned ((1 : ℝ) / 10) C.L C.A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) C.L C.A := by
  rcases hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
  · have hmem := C.J_sub q hm
    have hmem2 := signedPair_mem_PstarSigned ((C.F q).σ m) hq hLq ((C.F q).lower m hmem)
      ((C.F q).upper m hmem) ((C.F q).two_le m hmem)
    exact ⟨Or.inl hmem2.1, Or.inl hmem2.2⟩
  · exact ⟨Or.inr ⟨q, hq, hLq, a, ha, Or.inl rfl⟩, Or.inr ⟨q, hq, hLq, a, ha, Or.inr rfl⟩⟩

theorem stagePairS_lo_ge_one (C : CorrectionDataS ((1 : ℝ) / 10)) {q : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) {I : Iv} (hI : IsStagePairS C q I) : 1 ≤ I.lo := by
  rcases hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
  · have hmem := C.J_sub q hm
    have h2 := (C.F q).two_le m hmem
    unfold signedPair
    split_ifs with hσ
    · show 1 ≤ q * m; omega
    · show 1 ≤ q * m - 1; omega
  · have hlow := C.A.lower q hq hLq a ha
    have hqR0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have ha0R : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hqR0 _) hlow
    have ha0 : 0 < a := by exact_mod_cast ha0R
    show 1 ≤ a
    omega

theorem stagePairS_hi_le (C : CorrectionDataS ((1 : ℝ) / 10)) {q : ℕ} (hq : IsPrimePow q)
    (hLq : C.L < q) (hqH : q ≤ C.H) {I : Iv} (hI : IsStagePairS C q I) :
    (I.hi : ℝ) ≤ 8 * (C.H : ℝ) ^ ((11 : ℝ) / 10) + 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqHR : (q : ℝ) ≤ (C.H : ℝ) := by exact_mod_cast hqH
  have hqH11 : (q : ℝ) ^ ((11 : ℝ) / 10) ≤ (C.H : ℝ) ^ ((11 : ℝ) / 10) :=
    Real.rpow_le_rpow hq0.le hqHR (by norm_num)
  rcases hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
  · have hmem := C.J_sub q hm
    have hup := (C.F q).upper m hmem
    have h2 := (C.F q).two_le m hmem
    have hhi_le : ((signedPair q m ((C.F q).σ m)).hi : ℝ) ≤ (q : ℝ) * (m : ℝ) + 1 := by
      unfold signedPair
      split_ifs with hσ
      · show ((q * m + 1 : ℕ) : ℝ) ≤ _; push_cast; linarith
      · have heq2 : q * m - 1 + 1 = q * m := by omega
        show ((q * m - 1 + 1 : ℕ) : ℝ) ≤ _
        rw [heq2]; push_cast; linarith
    have hqm8 : (q : ℝ) * (m : ℝ) ≤ 8 * (q : ℝ) ^ ((11 : ℝ) / 10) := by
      have h1 : (q : ℝ) * (m : ℝ) ≤ (q : ℝ) * (8 * (q : ℝ) ^ ((1 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hup hq0.le
      have h2 : (q : ℝ) * (8 * (q : ℝ) ^ ((1 : ℝ) / 10)) = 8 * (q : ℝ) ^ ((11 : ℝ) / 10) := by
        rw [rpow_eleven_tenth hq0]; ring
      linarith [h1, h2]
    linarith [hhi_le, hqm8, hqH11]
  · have hup := C.A.upper q hq hLq a ha
    have hqnn : (0 : ℝ) ≤ (q : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_nonneg hq0.le _
    show ((a + 1 : ℕ) : ℝ) ≤ _
    push_cast at hup ⊢
    nlinarith [hup, hqH11, hqnn]

/-! ## A single correction stage -/

/-- **A single stage of the signed correction procedure**: given a prime power `q ∈ (C.L, C.H]`
and a deficit `r` with `DenBound q r`, there is a finset `P` of exactly `s q` stage pairs for
`q`, mutually separated, with `DenBound (q - 1)` on the remaining deficit, and total mass at
most `3 q^{-41/40}`. -/
theorem stage_signed (C : CorrectionDataS ((1 : ℝ) / 10)) (hL : 4 ≤ C.L) {q : ℕ}
    (hq : IsPrimePow q) (hLq : C.L < q) (hqH : q ≤ C.H) (r : ℚ) (hr : DenBound q r) :
    ∃ P : Finset Iv,
      P.card = s q ∧
      (∀ I ∈ P, IsStagePairS C q I) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      DenBound (q - 1) (r - ∑ I ∈ P, I.mass) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤ 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by
  classical
  have hq0 : 0 < q := by omega
  have hq3 : 3 ≤ q := by omega
  obtain ⟨S, hS_sub, hS_card, hDB⟩ := cancel_or_trivial_signed C hq hLq hqH r hr
  have hcardT : s q - S.card ≤ (C.A.F q).card := by rw [C.A.card_eq q hq hLq]; omega
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hcardT
  set corrSet := S.image (fun m => signedPair q m ((C.F q).σ m)) with hcorrSet_def
  set auxSet := T.image Iv.pair with hauxSet_def
  have hSmem2 : ∀ m ∈ S, 2 ≤ q * m := fun m hm => (C.F q).two_le m (C.J_sub q (hS_sub hm))
  have hinj_corr : Set.InjOn (fun m => signedPair q m ((C.F q).σ m)) S :=
    signedPair_injOn (by omega) _ hSmem2
  have hcorr_card : corrSet.card = S.card := Finset.card_image_of_injOn hinj_corr
  have haux_card : auxSet.card = T.card := Finset.card_image_of_injective T Iv.pair_injective
  have hdisj : Disjoint corrSet auxSet := by
    rw [Finset.disjoint_left]
    rintro I hI1 hI2
    simp only [hcorrSet_def, hauxSet_def, Finset.mem_image] at hI1 hI2
    obtain ⟨m, hm, hmI⟩ := hI1
    obtain ⟨a, ha, haI⟩ := hI2
    have hmem := C.J_sub q (hS_sub hm)
    have hsep := sep_corr_aux_signed C.A ((C.F q).σ m) hq hLq ((C.F q).lower m hmem)
      ((C.F q).upper m hmem) ((C.F q).two_le m hmem) hq hLq (hT_sub ha)
    have heqI : signedPair q m ((C.F q).σ m) = Iv.pair a := hmI.trans haI.symm
    rw [heqI] at hsep
    exact Iv.pair_not_sep_self a hsep
  refine ⟨corrSet ∪ auxSet, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcorr_card, haux_card, hT_card]; omega
  · intro I hI
    rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
    rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
    · exact Or.inl ⟨m, hS_sub hm, hmI.symm⟩
    · exact Or.inr ⟨a, hT_sub ha, haI.symm⟩
  · intro I hI J hJ hne
    have hIsp : IsStagePairS C q I := by
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
      rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
      · exact Or.inl ⟨m, hS_sub hm, hmI.symm⟩
      · exact Or.inr ⟨a, hT_sub ha, haI.symm⟩
    have hJsp : IsStagePairS C q J := by
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hJ
      rcases hJ with ⟨m, hm, hmJ⟩ | ⟨a, ha, haJ⟩
      · exact Or.inl ⟨m, hS_sub hm, hmJ.symm⟩
      · exact Or.inr ⟨a, hT_sub ha, haJ.symm⟩
    exact sep_of_stage_pairs_signed C hq hLq hqH hq hLq hqH hIsp hJsp hne
  · have hsum_split : ∑ I ∈ corrSet ∪ auxSet, I.mass =
        (∑ m ∈ S, wSigned q m ((C.F q).σ m)) + ∑ a ∈ T, w a := by
      rw [Finset.sum_union hdisj, hcorrSet_def, hauxSet_def,
        Finset.sum_image hinj_corr,
        Finset.sum_image Iv.pair_injective.injOn]
      congr 1
      · exact Finset.sum_congr rfl fun m hm =>
          (wSigned_eq ((C.F q).sign m (C.J_sub q (hS_sub hm))) (hSmem2 m hm)).symm
      · exact Finset.sum_congr rfl fun a _ => mass_pair a
    rw [hsum_split, ← sub_sub]
    apply hDB.sub
    apply DenBound.sum
    intro a ha
    have hsmooth1 : Powersmooth (q / 2) a := C.A.smooth_lo q hq hLq a (hT_sub ha)
    have hsmooth2 : Powersmooth (q / 2) (a + 1) := C.A.smooth_hi q hq hLq a (hT_sub ha)
    have hDBa : DenBound (q / 2) (w a) := DenBound.w hsmooth1 hsmooth2
    exact hDBa.mono (by omega)
  · have hbound : ∀ I ∈ corrSet ∪ auxSet, (I.mass : ℝ) ≤
        3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
      intro I hI
      rw [Finset.mem_union, hcorrSet_def, hauxSet_def, Finset.mem_image, Finset.mem_image] at hI
      rcases hI with ⟨m, hm, hmI⟩ | ⟨a, ha, haI⟩
      · rw [← hmI]
        have hmem := C.J_sub q (hS_sub hm)
        exact corrS_mass_le hq3 ((C.F q).σ m) ((C.F q).sign m hmem) (hSmem2 m hm)
          ((C.F q).lower m hmem)
      · rw [← haI]
        exact auxS_mass_le hq3 (C.A.lower q hq hLq a (hT_sub ha))
    have hcard_eq : (corrSet ∪ auxSet).card = s q := by
      rw [Finset.card_union_of_disjoint hdisj, hcorr_card, haux_card, hT_card]; omega
    calc ((∑ I ∈ corrSet ∪ auxSet, I.mass : ℚ) : ℝ)
        = ∑ I ∈ corrSet ∪ auxSet, (I.mass : ℝ) := by push_cast; rfl
      _ ≤ ∑ _I ∈ corrSet ∪ auxSet, 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) :=
          Finset.sum_le_sum hbound
      _ = (corrSet ∪ auxSet).card * (3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (s q : ℝ) * 3 * Eenv (1 / 10) q * (q : ℝ) ^ (-(11 : ℝ) / 10) := by
          rw [hcard_eq]; ring
      _ ≤ 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := signed_stage_mass_le q (by omega) (C.E_small q hq hLq)

end DescentS

open DescentS

/-- The inductive form of `descentS`, with `H` ranging over `[C.L, C.H]`. -/
theorem descentS' (C : CorrectionDataS ((1 : ℝ) / 10)) (hL : 4 ≤ C.L) :
    ∀ H, C.L ≤ H → H ≤ C.H → ∀ r₀ : ℚ, DenBound H r₀ →
    ∃ P : Finset Iv,
      P.card = CH C.L H ∧
      (∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ H ∧ IsStagePairS C q I) ∧
      (∀ I ∈ P, I.lo ∈ USigned ((1 : ℝ) / 10) C.L C.A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) C.L C.A) ∧
      (∀ I ∈ P, 1 ≤ I.lo ∧ I.hi = I.lo + 1 ∧
        (I.hi : ℝ) ≤ 8 * (C.H : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤
        ∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) ∧
      DenBound C.L (r₀ - ∑ I ∈ P, I.mass) := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base =>
    intro _hHC r₀ hr₀
    refine ⟨∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [CH]
    · simp
    · simp
    · simp
    · simp
    · simp
    · simpa using hr₀
  | succ H hH IH =>
    intro hHC r₀ hr₀
    have hHC' : H ≤ C.H := by omega
    by_cases hpp : IsPrimePow (H + 1)
    · have hLq' : C.L < H + 1 := by omega
      have hqH' : H + 1 ≤ C.H := hHC
      obtain ⟨Pq, hPq_card, hPq_mem, hPq_sep, hPq_DB, hPq_mass⟩ :=
        DescentS.stage_signed C hL hpp hLq' hqH' r₀ hr₀
      have hDBr1 : DenBound H (r₀ - ∑ I ∈ Pq, I.mass) := by
        have hHeq : H + 1 - 1 = H := by omega
        rwa [hHeq] at hPq_DB
      obtain ⟨P', hP'_card, hP'_mem, hP'_UU, hP'_end, hP'_sep, hP'_mass, hP'_DB⟩ :=
        IH hHC' (r₀ - ∑ I ∈ Pq, I.mass) hDBr1
      have hdisj : Disjoint Pq P' := by
        rw [Finset.disjoint_left]
        intro I hI hI'
        obtain ⟨q', hq', hLq'', hqH'', hsp'⟩ := hP'_mem I hI'
        have hlabel := stage_pair_labelS_eq C hpp hLq' hqH' hq' hLq'' (by omega : q' ≤ C.H)
          (hPq_mem I hI) hsp'
        omega
      have hsumeq : ∑ I ∈ Pq ∪ P', I.mass = ∑ I ∈ Pq, I.mass + ∑ I ∈ P', I.mass :=
        Finset.sum_union hdisj
      refine ⟨Pq ∪ P', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hPq_card, hP'_card, CH_succ C.L H hH,
          ite_eq_left_of_eq_true _ _ (eq_true hpp)]
        omega
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · exact ⟨H + 1, hpp, hLq', le_refl _, hPq_mem I hI⟩
        · obtain ⟨q', hq', hLq'', hqH'', hsp'⟩ := hP'_mem I hI
          exact ⟨q', hq', hLq'', by omega, hsp'⟩
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · exact DescentS.stagePairS_mem_U C hpp hLq' (hPq_mem I hI)
        · exact hP'_UU I hI
      · intro I hI
        rw [Finset.mem_union] at hI
        rcases hI with hI | hI
        · refine ⟨DescentS.stagePairS_lo_ge_one C hpp hLq' (hPq_mem I hI), ?_,
            DescentS.stagePairS_hi_le C hpp hLq' hqH' (hPq_mem I hI)⟩
          rcases hPq_mem I hI with ⟨m, hm, rfl⟩ | ⟨a, ha, rfl⟩
          · exact DescentS.signedPair_hi_eq_lo_succ (H + 1) m _
          · rfl
        · exact hP'_end I hI
      · intro I hI J hJ hne
        rw [Finset.mem_union] at hI hJ
        rcases hI with hI | hI <;> rcases hJ with hJ | hJ
        · exact hPq_sep I hI J hJ hne
        · obtain ⟨q', hq', hLq'', hqH'', hsp'⟩ := hP'_mem J hJ
          exact DescentS.sep_of_stage_pairs_signed C hpp hLq' hqH' hq' hLq'' (by omega)
            (hPq_mem I hI) hsp' hne
        · obtain ⟨q', hq', hLq'', hqH'', hsp'⟩ := hP'_mem I hI
          exact DescentS.sep_of_stage_pairs_signed C hq' hLq'' (by omega) hpp hLq' hqH'
            hsp' (hPq_mem J hJ) hne
        · exact hP'_sep I hI J hJ hne
      · rw [hsumeq]
        have hsum_succ :
            ∑ q ∈ (Finset.Icc (C.L + 1) (H + 1)).filter IsPrimePow,
                3 * (q : ℝ) ^ (-(41 : ℝ) / 40) =
              (∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
                  3 * (q : ℝ) ^ (-(41 : ℝ) / 40)) +
                3 * ((H : ℝ) + 1) ^ (-(41 : ℝ) / 40) := by
          simp only [Finset.sum_filter]
          rw [Finset.sum_Icc_succ_top (by omega : C.L + 1 ≤ H + 1),
            ite_eq_left_of_eq_true _ _ (eq_true hpp)]
          push_cast
          ring
        rw [hsum_succ]
        push_cast at hPq_mass hP'_mass ⊢
        linarith [hPq_mass, hP'_mass]
      · rw [hsumeq, ← sub_sub]
        exact hP'_DB
    · have hDB' : DenBound H r₀ := by
        intro l e hl he hle
        have hle' := hr₀ l e hl he hle
        have hne : l ^ e ≠ H + 1 := by
          intro heq
          exact hpp ((isPrimePow_nat_iff _).mpr ⟨l, e, hl, he, heq⟩)
        omega
      obtain ⟨P', hP'_card, hP'_mem, hP'_UU, hP'_end, hP'_sep, hP'_mass, hP'_DB⟩ :=
        IH hHC' r₀ hDB'
      refine ⟨P', ?_, ?_, hP'_UU, hP'_end, hP'_sep, ?_, hP'_DB⟩
      · rw [hP'_card, CH_succ C.L H hH, ite_eq_right_of_eq_false _ _ (eq_false hpp), add_zero]
      · intro I hI
        obtain ⟨q', hq', hLq'', hqH'', hsp'⟩ := hP'_mem I hI
        exact ⟨q', hq', hLq'', by omega, hsp'⟩
      · have hmono : ∑ q ∈ (Finset.Icc (C.L + 1) H).filter IsPrimePow,
              3 * (q : ℝ) ^ (-(41 : ℝ) / 40) ≤
            ∑ q ∈ (Finset.Icc (C.L + 1) (H + 1)).filter IsPrimePow,
              3 * (q : ℝ) ^ (-(41 : ℝ) / 40) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · apply Finset.filter_subset_filter
            intro x hx
            simp only [Finset.mem_Icc] at hx ⊢
            omega
          · intro i _ _; positivity
        linarith [hP'_mass, hmono]


/-- **The signed correction procedure** (docs Section 4). Mirrors `Erdos289.descent`:
exactly `C_H` pairs, each a retained signed correction pair or an auxiliary pair, with both
endpoints in `USigned`, mutually separated, ending at most `8 H^{11/10} + 1`, of total mass at most
`120 L^{-1/40}`, and reducing the deficit's denominator to prime powers at most `L`. -/
theorem descentS (C : CorrectionDataS ((1 : ℝ) / 10)) (hL : 4 ≤ C.L) (hH : C.L < C.H)
    (r₀ : ℚ) (hr₀ : DenBound C.H r₀) :
    ∃ P : Finset Iv,
      P.card = CH C.L C.H ∧
      (∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ C.H ∧
        ((∃ m ∈ C.J q, I = signedPair q m ((C.F q).σ m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a))) ∧
      (∀ I ∈ P, I.lo ∈ USigned ((1 : ℝ) / 10) C.L C.A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) C.L C.A) ∧
      (∀ I ∈ P, 1 ≤ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 8 * (C.H : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤ 120 * (C.L : ℝ) ^ (-(1 : ℝ) / 40) ∧
      DenBound C.L (r₀ - ∑ I ∈ P, I.mass) := by
  obtain ⟨P, hcard, hmem, hUU, hend, hsep, hmass, hDB⟩ :=
    descentS' C hL C.H hH.le (le_refl C.H) r₀ hr₀
  refine ⟨P, hcard, ?_, hUU, hend, hsep, ?_, hDB⟩
  · intro I hI
    obtain ⟨q, hq, hLq, hqH, hsp⟩ := hmem I hI
    exact ⟨q, hq, hLq, hqH, hsp⟩
  · calc ((∑ I ∈ P, I.mass : ℚ) : ℝ)
        ≤ ∑ q ∈ (Finset.Icc (C.L + 1) C.H).filter IsPrimePow, 3 * (q : ℝ) ^ (-(41 : ℝ) / 40) :=
          hmass
      _ ≤ 120 * (C.L : ℝ) ^ (-(1 : ℝ) / 40) := signed_total_mass_le C.L C.H (by omega)

end Erdos289
