import Erdos289.SignedDefs
import Erdos289.Sieve

set_option maxHeartbeats 1000000

/-!
# Lemma F1: many individually valid signed pairs

This file formalizes Lemma F1 of `docs/elementary_replacements.md` (Section 2, displays
(F1)–(F8)): for every sufficiently large prime power `q = p ^ a` there is a *signed fiber*
`F : SignedFiber ε q` — a set of multipliers `m` with attached signs `σ m ∈ {1, -1}` — of
cardinality at least `q ^ ε / (8 V(q))`.
-/

namespace Erdos289.SignedF1

open Finset Filter Topology

/-! ## The signed multiplier construction (docs Step 2, displays (F4)–(F5)) -/

/-- The scaling factor of the construction: `1` when `q` is a power of `2`, `4` otherwise. -/
def cf (p : ℕ) : ℕ := if p = 2 then 1 else 4

lemma cf_pos (p : ℕ) : 0 < cf p := by unfold cf; split <;> norm_num

lemma cf_le (p : ℕ) : cf p ≤ 4 := by unfold cf; split <;> norm_num

/-- The companion `r`: the canonical inverse of `cf p * t` modulo `q`. -/
noncomputable def rr (q p t : ℕ) : ℕ := rOf q (cf p * t)

/-- The `+` multiplier, defined by `q * mPlus + 1 = cf p * rr * t`. -/
noncomputable def mPlus (q p t : ℕ) : ℕ := mOf q q (cf p * t)

/-- The `-` multiplier, defined by `q * mMinus - 1 = cf p * (q - rr) * t`. -/
noncomputable def mMinus (q p t : ℕ) : ℕ := cf p * t - mPlus q p t

/-- The chosen multiplier: `mPlus` when `p ∤ mPlus`, else `mMinus`. -/
noncomputable def mult (q p t : ℕ) : ℕ := if p ∣ mPlus q p t then mMinus q p t else mPlus q p t

/-- The chosen sign: `+1` with `mPlus`, `-1` with `mMinus`. -/
noncomputable def sgn (q p t : ℕ) : ℤ := if p ∣ mPlus q p t then -1 else 1

/-- The cofactor `f` in the identity `neighbor = cf p * f * t`. -/
noncomputable def fac (q p t : ℕ) : ℕ := if p ∣ mPlus q p t then q - rr q p t else rr q p t

/-- Standing hypotheses for the construction at label `q = p ^ a` and parameter `t`. -/
structure Ctx (q p t : ℕ) : Prop where
  prime : p.Prime
  isPow : ∃ a, 0 < a ∧ q = p ^ a
  four_le : 4 ≤ q
  odd : ¬ 2 ∣ t
  ndvd : ¬ p ∣ t
  two_le : 2 ≤ t

namespace Ctx

variable {q p t : ℕ}

lemma one_lt_q (h : Ctx q p t) : 1 < q := by have := h.four_le; omega

lemma ndvd_cf (h : Ctx q p t) : ¬ p ∣ cf p * t := by
  intro hd
  rcases (Nat.Prime.dvd_mul h.prime).1 hd with h1 | h1
  · unfold cf at h1
    by_cases hp2 : p = 2
    · simp [hp2] at h1
    · simp [hp2] at h1
      have : p ∣ 2 ^ 2 := by simpa using h1
      have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
        (h.prime.dvd_of_dvd_pow this)
      exact hp2 this
  · exact h.ndvd h1

lemma cop (h : Ctx q p t) : Nat.Coprime (cf p * t) q := by
  obtain ⟨a, _, rfl⟩ := h.isPow
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.ndvd_cf).symm

lemma cft_pos (h : Ctx q p t) : 0 < cf p * t := by
  have := h.two_le; exact Nat.mul_pos (cf_pos p) (by omega)

/-- The defining equation of `mPlus`. -/
lemma spec_plus (h : Ctx q p t) : q * mPlus q p t + 1 = cf p * rr q p t * t := by
  have := mOf_spec (dvd_refl q) h.one_lt_q h.cop
  unfold mPlus rr
  rw [this]; ring

lemma rr_pos (h : Ctx q p t) : 0 < rr q p t := rOf_pos (dvd_refl q) h.one_lt_q h.cop

lemma rr_lt (h : Ctx q p t) : rr q p t < q := by
  have : NeZero q := ⟨by have := h.four_le; omega⟩
  exact ZMod.val_lt _

lemma mPlus_pos (h : Ctx q p t) : 1 ≤ mPlus q p t := by
  by_contra hc
  have h0 : mPlus q p t = 0 := by omega
  have hs := h.spec_plus
  rw [h0, Nat.mul_zero] at hs
  have ht := h.two_le
  have : cf p * rr q p t * t ≥ 2 := by
    have := h.rr_pos
    calc cf p * rr q p t * t ≥ 1 * 1 * 2 := by
          exact Nat.mul_le_mul (Nat.mul_le_mul (cf_pos p) this) ht
      _ = 2 := by ring
  omega

lemma mPlus_lt (h : Ctx q p t) : mPlus q p t < cf p * t := by
  have hs := h.spec_plus
  have hr := h.rr_lt
  have hct := h.cft_pos
  have hkey : cf p * rr q p t * t ≤ (q - 1) * (cf p * t) := by
    calc cf p * rr q p t * t = rr q p t * (cf p * t) := by ring
      _ ≤ (q - 1) * (cf p * t) := Nat.mul_le_mul_right _ (by omega)
  have hq : 1 < q := h.one_lt_q
  nlinarith [hs, hkey, hct, hq]

lemma mMinus_pos (h : Ctx q p t) : 1 ≤ mMinus q p t := by
  have := h.mPlus_lt; unfold mMinus; omega

lemma mMinus_lt (h : Ctx q p t) : mMinus q p t < cf p * t := by
  have := h.mPlus_pos; have := h.mPlus_lt; unfold mMinus; omega

lemma sum_eq (h : Ctx q p t) : mPlus q p t + mMinus q p t = cf p * t := by
  have := h.mPlus_lt; unfold mMinus; omega

/-- The defining equation of `mMinus`. -/
lemma spec_minus (h : Ctx q p t) : q * mMinus q p t = cf p * (q - rr q p t) * t + 1 := by
  have hs := h.spec_plus
  have hr := (h.rr_lt).le
  have hm := (h.mPlus_lt).le
  have h1 : (q : ℤ) * (mMinus q p t : ℕ) = (q : ℤ) * ((cf p * t : ℕ) - (mPlus q p t : ℕ)) := by
    unfold mMinus; rw [Nat.cast_sub hm]
  have h2 : ((cf p * (q - rr q p t) * t : ℕ) : ℤ)
      = (cf p : ℤ) * ((q : ℤ) - (rr q p t : ℤ)) * (t : ℤ) := by
    push_cast [Nat.cast_sub hr]; ring
  have hsZ : (q : ℤ) * (mPlus q p t : ℕ) + 1 = (cf p : ℤ) * (rr q p t : ℤ) * (t : ℤ) := by
    exact_mod_cast hs
  have : (q : ℤ) * (mMinus q p t : ℕ) = ((cf p * (q - rr q p t) * t : ℕ) : ℤ) + 1 := by
    rw [h1, h2]; push_cast; linarith [hsZ]
  exact_mod_cast this

lemma not_both (h : Ctx q p t) : ¬ (p ∣ mPlus q p t ∧ p ∣ mMinus q p t) := by
  rintro ⟨h1, h2⟩
  exact h.ndvd_cf (h.sum_eq ▸ Nat.dvd_add h1 h2)

lemma mult_ndvd (h : Ctx q p t) : ¬ p ∣ mult q p t := by
  unfold mult
  split
  · rename_i hd; exact fun hc => h.not_both ⟨hd, hc⟩
  · rename_i hd; exact hd

lemma mult_pos (h : Ctx q p t) : 1 ≤ mult q p t := by
  unfold mult; split
  · exact h.mMinus_pos
  · exact h.mPlus_pos

lemma mult_lt (h : Ctx q p t) : mult q p t < cf p * t := by
  unfold mult; split
  · exact h.mMinus_lt
  · exact h.mPlus_lt

lemma fac_pos (h : Ctx q p t) : 1 ≤ fac q p t := by
  unfold fac; split
  · have := h.rr_lt; omega
  · exact h.rr_pos

lemma fac_lt (h : Ctx q p t) : fac q p t < q := by
  unfold fac; split
  · have := h.rr_pos; have := h.rr_lt; omega
  · exact h.rr_lt

lemma sgn_cases (_h : Ctx q p t) : sgn q p t = 1 ∨ sgn q p t = -1 := by
  unfold sgn; split
  · right; rfl
  · left; rfl

lemma two_le_qm (h : Ctx q p t) : 2 ≤ q * mult q p t := by
  have := h.mult_pos; have := h.four_le; nlinarith

/-- The key identity: the neighbor of the chosen pair is `cf p * f * t`. -/
lemma neighbor_eq (h : Ctx q p t) :
    neighbor q (mult q p t) (sgn q p t) = cf p * fac q p t * t := by
  by_cases hd : p ∣ mPlus q p t
  · have hs : sgn q p t = -1 := by simp [sgn, hd]
    have hm : mult q p t = mMinus q p t := by simp [mult, hd]
    have hf : fac q p t = q - rr q p t := by simp [fac, hd]
    rw [hs, hm, hf, show neighbor q (mMinus q p t) (-1) = q * mMinus q p t - 1 from rfl]
    have := h.spec_minus
    omega
  · have hs : sgn q p t = 1 := by simp [sgn, hd]
    have hm : mult q p t = mPlus q p t := by simp [mult, hd]
    have hf : fac q p t = rr q p t := by simp [fac, hd]
    rw [hs, hm, hf, show neighbor q (mPlus q p t) 1 = q * mPlus q p t + 1 from rfl]
    exact h.spec_plus


lemma four_dvd_q (h : Ctx q p t) (hp2 : p = 2) : 4 ∣ q := by
  obtain ⟨a, ha, rfl⟩ := h.isPow
  subst hp2
  have h4 : 4 ≤ 2 ^ a := h.four_le
  have ha2 : 2 ≤ a := by
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · exfalso
      have : a = 1 := by omega
      subst this; norm_num at h4
    · exact hge
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ∣ 2 ^ a := pow_dvd_pow 2 ha2

lemma four_dvd_qm (h : Ctx q p t) (hp2 : p = 2) : 4 ∣ q * mult q p t :=
  Dvd.dvd.mul_right (h.four_dvd_q hp2) _

lemma cf_eq_four (hp2 : p ≠ 2) : cf p = 4 := by simp [cf, hp2]

lemma cf_eq_one (hp2 : p = 2) : cf p = 1 := by simp [cf, hp2]

lemma four_dvd_neighbor (h : Ctx q p t) (hp2 : p ≠ 2) :
    4 ∣ neighbor q (mult q p t) (sgn q p t) := by
  rw [h.neighbor_eq, cf_eq_four hp2]
  exact ⟨fac q p t * t, by ring⟩

lemma not_four_dvd_qm (h : Ctx q p t) (hp2 : p ≠ 2) : ¬ 4 ∣ q * mult q p t := by
  obtain ⟨k, hk⟩ := h.four_dvd_neighbor hp2
  have h2 := h.two_le_qm
  rcases h.sgn_cases with hs | hs
  · rw [hs, show neighbor q (mult q p t) 1 = q * mult q p t + 1 from rfl] at hk
    omega
  · rw [hs, show neighbor q (mult q p t) (-1) = q * mult q p t - 1 from rfl] at hk
    omega

lemma slot_eq_even (h : Ctx q p t) (hp2 : p = 2) :
    slot q (mult q p t) (sgn q p t) = q * mult q p t := by
  have h4 := h.four_dvd_qm hp2
  simp [slot, h4]

lemma slot_eq_odd (h : Ctx q p t) (hp2 : p ≠ 2) :
    slot q (mult q p t) (sgn q p t) = neighbor q (mult q p t) (sgn q p t) := by
  have h4 := h.not_four_dvd_qm hp2
  simp [slot, h4]

lemma four_dvd_slot (h : Ctx q p t) : 4 ∣ slot q (mult q p t) (sgn q p t) := by
  by_cases hp2 : p = 2
  · rw [h.slot_eq_even hp2]; exact h.four_dvd_qm hp2
  · rw [h.slot_eq_odd hp2]; exact h.four_dvd_neighbor hp2

lemma t_dvd_neighbor (h : Ctx q p t) : t ∣ neighbor q (mult q p t) (sgn q p t) :=
  ⟨cf p * fac q p t, by rw [h.neighbor_eq]; ring⟩

lemma neighbor_pos (h : Ctx q p t) : 1 ≤ neighbor q (mult q p t) (sgn q p t) := by
  have h2 := h.two_le_qm
  rcases h.sgn_cases with hs | hs
  · rw [hs, show neighbor q (mult q p t) 1 = q * mult q p t + 1 from rfl]; omega
  · rw [hs, show neighbor q (mult q p t) (-1) = q * mult q p t - 1 from rfl]; omega

lemma neighbor_cast (h : Ctx q p t) :
    ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ)
      = (q : ℤ) * (mult q p t : ℕ) + sgn q p t := by
  have h2 := h.two_le_qm
  rcases h.sgn_cases with hs | hs
  · rw [hs, show neighbor q (mult q p t) 1 = q * mult q p t + 1 from rfl]; push_cast; ring
  · rw [hs, show neighbor q (mult q p t) (-1) = q * mult q p t - 1 from rfl]
    rw [Nat.cast_sub (by omega : 1 ≤ q * mult q p t)]; push_cast; ring

lemma coprime_mult (h : Ctx q p t) : Nat.Coprime (mult q p t) q := by
  obtain ⟨a, _, rfl⟩ := h.isPow
  exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.mult_ndvd).symm

/-- A prime power `ℓ ^ b ≥ q` dividing the neighbor forces `ℓ ∣ cf p * t` (docs (F7)). -/
lemma big_primepow (h : Ctx q p t) {l b : ℕ} (hl : l.Prime) (_hb : 0 < b)
    (hdvd : l ^ b ∣ neighbor q (mult q p t) (sgn q p t)) (hge : q ≤ l ^ b) :
    l ∣ cf p * t := by
  rw [h.neighbor_eq] at hdvd
  have hdvd' : l ^ b ∣ fac q p t * (cf p * t) := by
    rw [show fac q p t * (cf p * t) = cf p * fac q p t * t by ring]; exact hdvd
  exact primepow_dvd_of_gt hl h.fac_pos (lt_of_lt_of_le h.fac_lt hge) hdvd'

/-- A prime power dividing the neighbor is automatically coprime to `q` (the neighbor is
`± 1` modulo `q`). -/
lemma coprime_primepow (h : Ctx q p t) {l b : ℕ} (hl : l.Prime) (hb : 0 < b)
    (hdvd : l ^ b ∣ neighbor q (mult q p t) (sgn q p t)) : Nat.Coprime (l ^ b) q := by
  obtain ⟨a, ha, hqa⟩ := h.isPow
  have hpn : ¬ (p : ℤ) ∣ ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ) := by
    intro hpd
    have hpq : (p : ℤ) ∣ (q : ℤ) := by
      rw [hqa]; exact_mod_cast dvd_pow_self p ha.ne'
    have h3 : sgn q p t
        = ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ) - (q : ℤ) * (mult q p t : ℕ) := by
      rw [h.neighbor_cast]; ring
    have hd : (p : ℤ) ∣ sgn q p t := by
      rw [h3]; exact dvd_sub hpd (hpq.mul_right _)
    have hp2 : 2 ≤ p := h.prime.two_le
    rcases h.sgn_cases with hs | hs <;> rw [hs] at hd
    · have := Int.le_of_dvd (by norm_num) hd; omega
    · have hd1 : (p : ℤ) ∣ 1 := (Int.dvd_neg).mp hd
      have := Int.le_of_dvd (by norm_num) hd1; omega
  have hlp : l ≠ p := by
    intro he
    have hd : (l : ℤ) ∣ ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ) := by
      exact_mod_cast dvd_trans (dvd_pow_self l hb.ne') hdvd
    rw [he] at hd
    exact hpn hd
  have hcopl : Nat.Coprime l p := (Nat.coprime_primes hl h.prime).2 hlp
  rw [hqa]
  exact Nat.Coprime.pow b a hcopl

lemma t_mem_divisors (h : Ctx q p t) :
    t ∈ (q * mult q p t + 1).divisors ∪ (q * mult q p t - 1).divisors := by
  have h2 := h.two_le_qm
  have hd := h.t_dvd_neighbor
  rcases h.sgn_cases with hs | hs
  · rw [hs, show neighbor q (mult q p t) 1 = q * mult q p t + 1 from rfl] at hd
    exact Finset.mem_union_left _ (Nat.mem_divisors.2 ⟨hd, by omega⟩)
  · rw [hs, show neighbor q (mult q p t) (-1) = q * mult q p t - 1 from rfl] at hd
    exact Finset.mem_union_right _ (Nat.mem_divisors.2 ⟨hd, by omega⟩)

end Ctx

/-! ## Elementary counting (docs Step 1) -/

/-- A set of integers in `[a, b]` lying in a single residue class mod `d` injects into
`[a / d, b / d]` via `n ↦ n / d`. -/
lemma card_of_single_class {a b d : ℕ} (_hd : 0 < d) {F : Finset ℕ} (hF : F ⊆ Icc a b)
    (hmod : ∀ x ∈ F, ∀ y ∈ F, x % d = y % d) : F.card ≤ (Icc (a / d) (b / d)).card := by
  refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
  · intro n hn
    have hn' := Finset.mem_Icc.1 (hF hn)
    exact Finset.mem_Icc.2 ⟨Nat.div_le_div_right hn'.1, Nat.div_le_div_right hn'.2⟩
  · intro x hx y hy hxy
    have h1 := hmod x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy)
    have hxy' : x / d = y / d := hxy
    calc x = d * (x / d) + x % d := (Nat.div_add_mod x d).symm
      _ = d * (y / d) + y % d := by rw [hxy', h1]
      _ = y := Nat.div_add_mod y d

/-- Real form of `card_of_single_class`. -/
lemma card_of_single_class_real {a b d : ℕ} (hd : 0 < d) (hab : a ≤ b) {F : Finset ℕ}
    (hF : F ⊆ Icc a b) (hmod : ∀ x ∈ F, ∀ y ∈ F, x % d = y % d) :
    (F.card : ℝ) ≤ ((b : ℝ) - a) / d + 2 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : F.card ≤ (Icc (a / d) (b / d)).card := card_of_single_class hd hF hmod
  rw [Nat.card_Icc] at h1
  have h2 : a / d ≤ b / d := Nat.div_le_div_right hab
  have h3 : (F.card : ℝ) ≤ ((b / d : ℕ) : ℝ) + 1 - ((a / d : ℕ) : ℝ) := by
    have hcast : ((b / d + 1 - a / d : ℕ) : ℝ) = ((b / d : ℕ) : ℝ) + 1 - ((a / d : ℕ) : ℝ) := by
      have hle : a / d ≤ b / d + 1 := by omega
      push_cast [Nat.cast_sub hle]; ring
    calc (F.card : ℝ) ≤ ((b / d + 1 - a / d : ℕ) : ℝ) := by exact_mod_cast h1
      _ = _ := hcast
  have hb : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := by
    rw [le_div_iff₀ hdR]
    have := Nat.div_mul_le_self b d
    exact_mod_cast this
  have ha : (a : ℝ) / d - 1 ≤ ((a / d : ℕ) : ℝ) := by
    have hmodlt : a % d < d := Nat.mod_lt _ hd
    have heq : d * (a / d) + a % d = a := Nat.div_add_mod a d
    have hh : (a : ℝ) ≤ (d : ℝ) * ((a / d : ℕ) : ℝ) + (d : ℝ) := by
      have e1 : (a : ℝ) = (d : ℝ) * ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) := by
        exact_mod_cast heq.symm
      have e2 : ((a % d : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hmodlt.le
      linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hdR]
    nlinarith [hh]
  have : ((b : ℝ) - a) / d = (b : ℝ) / d - (a : ℝ) / d := by ring
  linarith [h3, hb, ha]

/-! ## The parameter set `T_q` (docs Step 1) -/

/-- The parameter set: the odd numbers `t = 2 s + 1` with `s ∈ [A, B]` and `p ∤ t`. -/
noncomputable def Tset (p A B : ℕ) : Finset ℕ :=
  ((Icc A B).filter (fun s => ¬ p ∣ (2 * s + 1))).image (fun s => 2 * s + 1)

lemma mem_Tset {p A B t : ℕ} :
    t ∈ Tset p A B ↔ ∃ s, A ≤ s ∧ s ≤ B ∧ ¬ p ∣ (2 * s + 1) ∧ 2 * s + 1 = t := by
  simp only [Tset, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨s, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨s, h1, h2, h3, h4⟩
  · rintro ⟨s, h1, h2, h3, h4⟩; exact ⟨s, ⟨⟨h1, h2⟩, h3⟩, h4⟩

lemma Tset_odd {p A B t : ℕ} (ht : t ∈ Tset p A B) : ¬ 2 ∣ t := by
  obtain ⟨s, _, _, _, rfl⟩ := mem_Tset.1 ht; omega

lemma Tset_ndvd {p A B t : ℕ} (ht : t ∈ Tset p A B) : ¬ p ∣ t := by
  obtain ⟨s, _, _, h3, rfl⟩ := mem_Tset.1 ht; exact h3

lemma Tset_lb {p A B t : ℕ} (ht : t ∈ Tset p A B) : 2 * A + 1 ≤ t := by
  obtain ⟨s, h1, _, _, rfl⟩ := mem_Tset.1 ht; omega

lemma Tset_ub {p A B t : ℕ} (ht : t ∈ Tset p A B) : t ≤ 2 * B + 1 := by
  obtain ⟨s, _, h2, _, rfl⟩ := mem_Tset.1 ht; omega

lemma Tset_subset_Icc (p A B : ℕ) : Tset p A B ⊆ Icc (2 * A + 1) (2 * B + 1) := by
  intro t ht; exact mem_Icc.2 ⟨Tset_lb ht, Tset_ub ht⟩

/-- `|T_q| ≥ (B - A + 1) - ((B - A)/3 + 2)`, uniformly in the prime `p` (docs `(F13)`'s
first step). -/
lemma Tset_card_ge (p A B : ℕ) (hp : p.Prime) (hAB : A ≤ B) :
    ((B : ℝ) - A + 1) - (((B : ℝ) - A) / 3 + 2) ≤ ((Tset p A B).card : ℝ) := by
  have hABR : (0 : ℝ) ≤ (B : ℝ) - A := by
    have : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    linarith
  set Bad : Finset ℕ := (Icc A B).filter (fun s => p ∣ (2 * s + 1)) with hBad
  set Gd : Finset ℕ := (Icc A B).filter (fun s => ¬ p ∣ (2 * s + 1)) with hGd
  have hcards : Bad.card + Gd.card = (Icc A B).card := by
    rw [hBad, hGd]; exact Finset.card_filter_add_card_filter_not _
  have hIcc : ((Icc A B).card : ℝ) = (B : ℝ) - A + 1 := by
    rw [Nat.card_Icc]
    have : ((B + 1 - A : ℕ) : ℝ) = (B : ℝ) + 1 - (A : ℝ) := by
      push_cast [Nat.cast_sub (by omega : A ≤ B + 1)]; ring
    rw [this]; ring
  have himg : (Tset p A B).card = Gd.card := by
    rw [Tset, hGd]
    exact Finset.card_image_of_injective _ (fun x y hxy => by omega)
  have hBadle : (Bad.card : ℝ) ≤ ((B : ℝ) - A) / 3 + 2 := by
    by_cases hp2 : p = 2
    · have : Bad = ∅ := by
        rw [hBad, hp2]
        refine Finset.filter_eq_empty_iff.2 ?_
        intro s _
        omega
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ ((B : ℝ) - A) / 3 := by positivity
      linarith
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
      have hIC : IsCoprime (p : ℤ) 2 := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.gcd] using hcop2
      have hmod : ∀ x ∈ Bad, ∀ y ∈ Bad, x % p = y % p := by
        intro x hx y hy
        rw [hBad, Finset.mem_filter] at hx hy
        have hdx : (p : ℤ) ∣ (2 * (x : ℤ) + 1) := by exact_mod_cast hx.2
        have hdy : (p : ℤ) ∣ (2 * (y : ℤ) + 1) := by exact_mod_cast hy.2
        have hd2 : (p : ℤ) ∣ 2 * ((y : ℤ) - (x : ℤ)) := by
          have h := dvd_sub hdy hdx
          have e : 2 * (y : ℤ) + 1 - (2 * (x : ℤ) + 1) = 2 * ((y : ℤ) - (x : ℤ)) := by ring
          rwa [e] at h
        have hfin : (p : ℤ) ∣ ((y : ℤ) - (x : ℤ)) := hIC.dvd_of_dvd_mul_left hd2
        exact Nat.modEq_iff_dvd.2 hfin
      have hsub : Bad ⊆ Icc A B := Finset.filter_subset _ _
      have hpz : 0 < p := by omega
      have := card_of_single_class_real hpz hAB hsub hmod
      have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have hdiv : ((B : ℝ) - A) / p ≤ ((B : ℝ) - A) / 3 := by
        apply div_le_div_of_nonneg_left hABR (by norm_num) hpR
      linarith
  have : (Gd.card : ℝ) = ((Icc A B).card : ℝ) - (Bad.card : ℝ) := by
    have : ((Bad.card + Gd.card : ℕ) : ℝ) = ((Icc A B).card : ℝ) := by exact_mod_cast hcards
    push_cast at this
    linarith
  rw [himg, this, hIcc]
  linarith [hBadle]


/-! ## Large prime factors of the parameter (docs display (F6)) -/

open Classical in
lemma bigPrimeFactor_subset_Icc (A B Dn : ℕ) : bigPrimeFactor A B Dn ⊆ Finset.Icc A B := by
  unfold bigPrimeFactor
  exact Finset.filter_subset _ _

/-- The count of `t ∈ [A, B] ⊆ [q^ε, 2 q^ε]` with a prime factor exceeding `q^(ε-η)` is at
most `κ q^ε`, for a suitable `η > 0` depending only on `ε` and `κ`. This is `bad1_bound` of
`Erdos289/Lemma1.lean` on the interval `[q^ε, 2 q^ε]` instead of `[4 q^ε, 5 q^ε]`. -/
theorem bigPrime_gen (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ η < ε / 2 ∧ ∀ᶠ q : ℕ in atTop, ∀ A B : ℕ,
      (q : ℝ) ^ ε ≤ (A : ℝ) → (B : ℝ) ≤ 2 * (q : ℝ) ^ ε →
      ((bigPrimeFactor A B ⌈(q : ℝ) ^ (ε - η)⌉₊).card : ℝ) ≤ κ * (q : ℝ) ^ ε := by
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
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpc0 : (0 : ℝ) ≤ (Nat.primeCounting 2 : ℝ) := by positivity
    rw [le_div_iff₀ hlog2] at h2
    nlinarith [h2, hlog2, hpc0]
  obtain ⟨X₁, hX₁2, hmert⟩ := mertens_gap (κ / 25) (by linarith)
  have hεη0 : 0 < ε - η := by linarith
  filter_upwards [rpow_ge_eventually ε hε0 4, rpow_ge_eventually (ε - η) hεη0 (X₁ : ℝ),
      const_le_mul_log_eventually (Real.log 2) η hη0,
      const_le_mul_log_eventually (25 * C_pc / κ) ε hε0,
      eventually_ge_atTop 2]
    with q hM4 hDX1 hlog2 hCbound hq2
  intro A B hA hB
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set M : ℝ := (q : ℝ) ^ ε with hMdef
  set D : ℝ := (q : ℝ) ^ (ε - η) with hDdef
  set Dn : ℕ := ⌈D⌉₊ with hDndef
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hAR : M ≤ (A : ℝ) := hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast this
  rcases Nat.lt_or_ge B A with hBA' | hAleB
  · have hemp : Finset.Icc A B = ∅ := Finset.Icc_eq_empty (by omega)
    have hz : bigPrimeFactor A B Dn = ∅ :=
      Finset.subset_empty.1 (hemp ▸ bigPrimeFactor_subset_Icc A B Dn)
    rw [hz]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAleB
  have hDM : D ≤ M := by
    rw [hDdef, hMdef]
    exact Real.rpow_le_rpow_of_exponent_le hqR1 (by linarith)
  have hDnleB : Dn ≤ B := by
    rw [hDndef]; exact Nat.ceil_le.mpr (by linarith)
  have hX1leDn : X₁ ≤ Dn := by
    have h1 : (X₁ : ℝ) ≤ D := hDX1
    have h2 : D ≤ (Dn : ℝ) := Nat.le_ceil _
    have : (X₁ : ℝ) ≤ (Dn : ℝ) := le_trans h1 h2
    exact_mod_cast this
  have hB4 : (4 : ℝ) ≤ (B : ℝ) := by linarith
  have hB2 : 2 ≤ B := by
    have : (2 : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this
  have hBR1 : (1 : ℝ) < (B : ℝ) := by linarith
  have hsub : bigPrimeFactor A B Dn ⊆
      ((Finset.Ioc Dn B).filter Nat.Prime).biUnion (fun l => (Icc A B).filter (l ∣ ·)) :=
    bigPrimeFactor_subset A B Dn hA1
  have hcard1 : ((bigPrimeFactor A B Dn).card : ℝ) ≤
      ∑ l ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B : ℝ) - A) / l + 2) := by
    calc ((bigPrimeFactor A B Dn).card : ℝ)
        ≤ ((((Finset.Ioc Dn B).filter Nat.Prime).biUnion
            (fun l => (Icc A B).filter (l ∣ ·))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ l ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B : ℝ) - A) / l + 2) :=
          bigPrimeFactor_card_le A B Dn hAleB
  set S : ℝ := ∑ l ∈ (Finset.Ioc Dn B).filter Nat.Prime, (1 : ℝ) / l with hSdef
  set P : ℕ := ((Finset.Ioc Dn B).filter Nat.Prime).card with hPdef
  have hsplit : ∑ l ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B : ℝ) - A) / l + 2)
      = ((B : ℝ) - A) * S + 2 * P := by
    have e1 : ∀ l ∈ (Finset.Ioc Dn B).filter Nat.Prime,
        ((B : ℝ) - A) / l + 2 = ((B : ℝ) - A) * (1 / (l : ℝ)) + 2 := by
      intro l _; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, hSdef, hPdef]
    ring
  have hSbound : S ≤ Real.log (Real.log B / Real.log Dn) + κ / 25 :=
    hmert Dn B hX1leDn hDnleB
  have hDn2 : 2 ≤ Dn := le_trans hX₁2 hX1leDn
  have hDnR1 : (1 : ℝ) < (Dn : ℝ) := by exact_mod_cast (by omega : 1 < Dn)
  have hlogDnpos : 0 < Real.log (Dn : ℝ) := Real.log_pos hDnR1
  have hlogDn_ge : (ε - η) * Real.log q ≤ Real.log (Dn : ℝ) := by
    have h1 : D ≤ (Dn : ℝ) := Nat.le_ceil _
    have hDpos : 0 < D := by rw [hDdef]; positivity
    have h2 : Real.log D ≤ Real.log (Dn : ℝ) := Real.log_le_log hDpos h1
    rwa [hDdef, Real.log_rpow hqpos] at h2
  have hlogB_le : Real.log (B : ℝ) ≤ Real.log 2 + ε * Real.log q := by
    have h1 : Real.log (B : ℝ) ≤ Real.log (2 * M) := Real.log_le_log (by linarith) hB
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    rwa [hMdef, Real.log_rpow hqpos] at h1
  have hlogB_ge : ε * Real.log q ≤ Real.log (B : ℝ) := by
    have h1 : Real.log M ≤ Real.log (B : ℝ) := Real.log_le_log hMpos (by linarith)
    rwa [hMdef, Real.log_rpow hqpos] at h1
  set γ : ℝ := 2 * η / (ε - η) with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hchain : Real.log (B : ℝ) ≤ (1 + γ) * Real.log (Dn : ℝ) := by
    have hstep1 : Real.log 2 + ε * Real.log q ≤ (ε + η) * Real.log q := by linarith
    have hstep2 : (1 + γ) * (ε - η) = ε + η := by rw [hγdef]; field_simp; ring
    have hstep3 : (ε + η) * Real.log q ≤ (1 + γ) * Real.log (Dn : ℝ) := by
      rw [← hstep2]
      have hlogqpos : 0 ≤ Real.log q := Real.log_nonneg hqR1
      nlinarith [hlogDn_ge, hγ0]
    linarith
  have hratio : Real.log (B : ℝ) / Real.log (Dn : ℝ) ≤ 1 + γ := by
    rw [div_le_iff₀ hlogDnpos]; linarith
  have hloglog : Real.log (Real.log B / Real.log Dn) ≤ γ := by
    have h1 : Real.log (Real.log (B : ℝ) / Real.log (Dn : ℝ)) ≤ Real.log (1 + γ) :=
      Real.log_le_log (div_pos (Real.log_pos hBR1) hlogDnpos) hratio
    have h2 : Real.log (1 + γ) ≤ γ := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + γ by linarith)
      linarith
    linarith
  have hγbound : γ ≤ κ / 25 := by
    rw [hγdef]
    have hεη2 : ε / 2 ≤ ε - η := by linarith
    have hminκ : min κ 1 ≤ κ := min_le_left _ _
    rw [div_le_iff₀ hεη0]
    have h100 : η = ε * min κ 1 / 100 := hηdef
    nlinarith [hminκ, hεη2, hε0.le]
  have hSbound2 : S ≤ 2 * κ / 25 := by linarith
  have hSnonneg : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg fun l _ => by positivity
  have hBAle : (B : ℝ) - A ≤ M := by linarith
  have hBAnonneg : (0 : ℝ) ≤ (B : ℝ) - A := by linarith
  have hterm1 : ((B : ℝ) - A) * S ≤ M * (2 * κ / 25) := by
    calc ((B : ℝ) - A) * S ≤ M * S := mul_le_mul_of_nonneg_right hBAle hSnonneg
      _ ≤ M * (2 * κ / 25) := mul_le_mul_of_nonneg_left hSbound2 (by linarith)
  have hPsub : (Finset.Ioc Dn B).filter Nat.Prime ⊆ (Finset.Icc 1 B).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩
  have hPle : P ≤ Nat.primeCounting B := by
    rw [hPdef, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    exact Finset.card_le_card hPsub
  have hPleR : (P : ℝ) ≤ C_pc * (B : ℝ) / Real.log B := by
    have h1 : (Nat.primeCounting B : ℝ) ≤ C_pc * (B : ℝ) / Real.log B := hC_pc B hB2
    have h2 : (P : ℝ) ≤ (Nat.primeCounting B : ℝ) := by exact_mod_cast hPle
    linarith
  have hlogBpos : 0 < Real.log (B : ℝ) := Real.log_pos hBR1
  have hlogBge : 25 * C_pc / κ ≤ Real.log (B : ℝ) := le_trans hCbound hlogB_ge
  have hstepA : 25 * C_pc ≤ κ * Real.log (B : ℝ) := by
    rw [div_le_iff₀ hκ] at hlogBge; linarith
  have hterm2 : 2 * (P : ℝ) ≤ (4 / 25) * κ * M := by
    have h3 := mul_le_mul_of_nonneg_left hstepA hMpos.le
    have h2 : 4 * C_pc * M ≤ (4 / 25) * κ * M * Real.log (B : ℝ) := by nlinarith [h3]
    have h1 : 2 * C_pc * (B : ℝ) ≤ 4 * C_pc * M := by nlinarith [hB, hCpc0]
    calc 2 * (P : ℝ) ≤ 2 * (C_pc * (B : ℝ) / Real.log B) := by linarith
      _ = 2 * C_pc * (B : ℝ) / Real.log B := by ring
      _ ≤ (4 / 25) * κ * M := by rw [div_le_iff₀ hlogBpos]; linarith
  have hfinal : ((bigPrimeFactor A B Dn).card : ℝ) ≤ M * (2 * κ / 25) + (4 / 25) * κ * M := by
    calc ((bigPrimeFactor A B Dn).card : ℝ)
        ≤ ∑ l ∈ (Finset.Ioc Dn B).filter Nat.Prime, (((B : ℝ) - A) / l + 2) := hcard1
      _ = ((B : ℝ) - A) * S + 2 * P := hsplit
      _ ≤ M * (2 * κ / 25) + (4 / 25) * κ * M := by linarith
  nlinarith [hfinal, hM1, hκ]


/-! ## The divisor envelope `V(q)` (docs display (F1)) -/

lemma Venv_pos (ε : ℝ) {q : ℕ} (hq : 1 ≤ q) (hε : 0 ≤ ε) : 1 ≤ Venv ε q := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := Real.one_le_rpow hqR (by linarith)
  have hN : 1 ≤ ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
  have h := Finset.le_sup (f := fun n : ℕ => n.divisors.card)
    (Finset.mem_Icc.2 ⟨le_refl 1, hN⟩)
  simpa [Venv] using h

lemma tau_le_Venv (ε : ℝ) (q n : ℕ) (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε)) :
    n.divisors.card ≤ Venv ε q := by
  refine Finset.le_sup (f := fun m : ℕ => m.divisors.card) (Finset.mem_Icc.2 ⟨hn1, ?_⟩)
  have h : (n : ℝ) ≤ ((⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ : ℕ) : ℝ) := le_trans hn (Nat.le_ceil _)
  exact_mod_cast h

/-- `V(q) ≤ q^δ` eventually, for any `δ > 0` (docs: "the divisor bound implies `V(q) = q^{o(1)}`").
Uniformity over `n ≤ ⌈25 q^{1+ε}⌉` comes from applying `divisor_bound` at exponent
`δ / (2(1+ε))` and absorbing the finitely many small `n` into `τ(n) ≤ n`. -/
theorem Venv_le_rpow (ε δ : ℝ) (hε0 : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (Venv ε q : ℝ) ≤ (q : ℝ) ^ δ := by
  set δ' : ℝ := δ / (2 * (1 + ε)) with hδ'def
  have hδ'0 : 0 < δ' := by rw [hδ'def]; positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (divisor_bound δ' hδ'0)
  filter_upwards [rpow_ge_eventually δ hδ (n₀ : ℝ),
      rpow_ge_eventually (δ / 2) (by linarith) ((26 : ℝ) ^ δ'),
      eventually_ge_atTop 1] with q hq1 hq2 hq3
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := Real.one_le_rpow hqR1 (by linarith)
  set N : ℕ := ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊ with hNdef
  have hNle : (N : ℝ) ≤ 26 * (q : ℝ) ^ (1 + ε) := by
    have h1 : (N : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε) + 1 :=
      le_of_lt (by rw [hNdef]; exact Nat.ceil_lt_add_one (by positivity))
    linarith
  have hqδ : (0 : ℝ) < (q : ℝ) ^ δ := Real.rpow_pos_of_pos hqpos δ
  have key : ∀ n ∈ Finset.Icc 1 N, n.divisors.card ≤ ⌊(q : ℝ) ^ δ⌋₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    refine Nat.le_floor ?_
    rcases Nat.lt_or_ge n n₀ with hlt | hge
    · calc (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n
        _ ≤ (n₀ : ℝ) := by exact_mod_cast hlt.le
        _ ≤ (q : ℝ) ^ δ := hq1
    · have h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) ^ δ' := hn₀ n hge
      have h2 : (n : ℝ) ≤ 26 * (q : ℝ) ^ (1 + ε) := by
        have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
        linarith
      have h3 : (n : ℝ) ^ δ' ≤ (26 * (q : ℝ) ^ (1 + ε)) ^ δ' :=
        Real.rpow_le_rpow (by positivity) h2 hδ'0.le
      have h4 : (26 * (q : ℝ) ^ (1 + ε)) ^ δ' = (26 : ℝ) ^ δ' * (q : ℝ) ^ (δ / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hqpos.le]
        congr 2
        rw [hδ'def]; field_simp
      have h5 : (26 : ℝ) ^ δ' * (q : ℝ) ^ (δ / 2) ≤ (q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hq2 (by positivity)
      have h6 : (q : ℝ) ^ (δ / 2) * (q : ℝ) ^ (δ / 2) = (q : ℝ) ^ δ := by
        rw [← Real.rpow_add hqpos]; congr 1; ring
      linarith [h1, h3, h4 ▸ h3, h5, h6]
  have hsup : Venv ε q ≤ ⌊(q : ℝ) ^ δ⌋₊ := Finset.sup_le key
  calc (Venv ε q : ℝ) ≤ ((⌊(q : ℝ) ^ δ⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
    _ ≤ (q : ℝ) ^ δ := Nat.floor_le hqδ.le


/-! ## The construction at a fixed label `q = p ^ a` -/

/-- Lower end of the `s`-range; the parameters are `t = 2 s + 1` with `s ∈ [Aq, Bq]`. -/
noncomputable def Aq (ε : ℝ) (q : ℕ) : ℕ := ⌈(q : ℝ) ^ ε / 2⌉₊

/-- Upper end of the `s`-range. -/
noncomputable def Bq (ε : ℝ) (q : ℕ) : ℕ := ⌊(q : ℝ) ^ ε⌋₊ - 1

/-- The threshold `T = q^(ε-η)` for large prime factors of `t` (docs Step 3). -/
noncomputable def Dq (ε η : ℝ) (q : ℕ) : ℕ := ⌈(q : ℝ) ^ (ε - η)⌉₊

/-- Exponent budget for prime powers dividing a neighbor. -/
noncomputable def Bmx (q : ℕ) : ℕ := ⌊5 * Real.log q⌋₊

/-- The parameter set `T_q` of docs Step 1. -/
noncomputable def Tq (ε : ℝ) (q p : ℕ) : Finset ℕ := Tset p (Aq ε q) (Bq ε q)

open Classical in
/-- The parameters surviving the large-prime-factor sieve (docs display (F6)). -/
noncomputable def NoBig (ε η : ℝ) (q p : ℕ) : Finset ℕ :=
  (Tq ε q p).filter (fun t => ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)

open Classical in
/-- The parameters surviving all three deletions of docs Step 3. -/
noncomputable def GoodT (ε η : ℝ) (q p : ℕ) : Finset ℕ :=
  (NoBig ε η q p).filter (fun t =>
    Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧ Rq ε q ≤ (mult q p t : ℝ))

/-- The multiplier set of the fiber. -/
noncomputable def Iq (ε η : ℝ) (q p : ℕ) : Finset ℕ := (GoodT ε η q p).image (mult q p)

open Classical in
/-- The parameters `t` whose neighbor is divisible by the prime power `l ^ b`, with sign `σ`. -/
noncomputable def pkFib (ε η : ℝ) (q p l b : ℕ) (σ : ℤ) : Finset ℕ :=
  (NoBig ε η q p).filter
    (fun t => sgn q p t = σ ∧ l ^ b ∣ neighbor q (mult q p t) (sgn q p t))

open Classical in
/-- The grid of witness prime powers `l ^ b ≥ q` with `l ≤ T`, `b ≤ Bmx`, together with a sign. -/
noncomputable def wgrid (ε η : ℝ) (q : ℕ) : Finset ((ℕ × ℕ) × ℤ) :=
  ((((Finset.Icc 2 (Dq ε η q)).filter Nat.Prime) ×ˢ Finset.Icc 1 (Bmx q)) ×ˢ
      ({1, -1} : Finset ℤ)).filter (fun x => q ≤ x.1.1 ^ x.1.2)

/-- The asymptotic facts about `q` used by the construction. -/
structure Large (ε η : ℝ) (q p : ℕ) : Prop where
  prime : p.Prime
  isPow : ∃ a, 0 < a ∧ q = p ^ a
  five_le : 5 ≤ q
  M100 : (100 : ℝ) ≤ (q : ℝ) ^ ε
  q16 : (q : ℝ) ^ ε ≤ (q : ℝ) / 16
  Vle : (Venv ε q : ℝ) ≤ (q : ℝ) ^ (η / 4)
  logle : Real.log q ≤ (q : ℝ) ^ (η / 4)
  log800 : (800 : ℝ) ≤ Real.log q
  bad2 : 4000 * (q : ℝ) ^ (-(η / 2)) ≤ 1
  bad3 : 800 * (q : ℝ) ^ (-(ε - η / 4)) ≤ 1
  D2 : (2 : ℝ) ≤ (q : ℝ) ^ (ε - η)
  q25 : (25 : ℝ) ≤ (q : ℝ) ^ (2 - ε)
  bigP : ∀ A B : ℕ, (q : ℝ) ^ ε ≤ (A : ℝ) → (B : ℝ) ≤ 2 * (q : ℝ) ^ ε →
    ((bigPrimeFactor A B (Dq ε η q)).card : ℝ) ≤ (q : ℝ) ^ ε / 200

namespace Large

variable {ε η : ℝ} {q p : ℕ}

lemma qpos (hL : Large ε η q p) : (0 : ℝ) < (q : ℝ) := by
  have : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hL.five_le
  linarith

lemma q1 (hL : Large ε η q p) : (1 : ℝ) ≤ (q : ℝ) := by
  have : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hL.five_le
  linarith

lemma Vone (hL : Large ε η q p) (hε0 : 0 < ε) : (1 : ℝ) ≤ (Venv ε q : ℝ) := by
  have h5 := hL.five_le
  have h : 1 ≤ Venv ε q := Venv_pos ε (by omega : 1 ≤ q) hε0.le
  exact_mod_cast h

lemma rpow_one_add (hL : Large ε η q p) : (q : ℝ) ^ (1 + ε) = (q : ℝ) * (q : ℝ) ^ ε := by
  rw [Real.rpow_add hL.qpos, Real.rpow_one]

lemma one_le_rpow_one_add (hL : Large ε η q p) (hε0 : 0 < ε) :
    (1 : ℝ) ≤ (q : ℝ) ^ (1 + ε) := Real.one_le_rpow hL.q1 (by linarith)

/-! ### The range of the parameter `t` -/

lemma Aq_ge (_hL : Large ε η q p) : (q : ℝ) ^ ε / 2 ≤ ((Aq ε q : ℕ) : ℝ) := Nat.le_ceil _

lemma Aq_le (_hL : Large ε η q p) : ((Aq ε q : ℕ) : ℝ) ≤ (q : ℝ) ^ ε / 2 + 1 :=
  le_of_lt (Nat.ceil_lt_add_one (by positivity))

lemma floor_ge (hL : Large ε η q p) : 100 ≤ ⌊(q : ℝ) ^ ε⌋₊ :=
  Nat.le_floor (by exact_mod_cast hL.M100)

lemma Bq_le (hL : Large ε η q p) : ((Bq ε q : ℕ) : ℝ) ≤ (q : ℝ) ^ ε - 1 := by
  have hf := hL.floor_ge
  have h1 : ((Bq ε q : ℕ) : ℝ) = ((⌊(q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) - 1 := by
    rw [Bq, Nat.cast_sub (by omega)]; norm_num
  have h2 : ((⌊(q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) ≤ (q : ℝ) ^ ε := Nat.floor_le (by positivity)
  rw [h1]; linarith

lemma Bq_ge (hL : Large ε η q p) : (q : ℝ) ^ ε - 2 ≤ ((Bq ε q : ℕ) : ℝ) := by
  have hf := hL.floor_ge
  have h1 : ((Bq ε q : ℕ) : ℝ) = ((⌊(q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) - 1 := by
    rw [Bq, Nat.cast_sub (by omega)]; norm_num
  have h2 : (q : ℝ) ^ ε < ((⌊(q : ℝ) ^ ε⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [h1]; linarith

lemma Aq_le_Bq (hL : Large ε η q p) : Aq ε q ≤ Bq ε q := by
  have h1 := hL.Aq_le
  have h2 := hL.Bq_ge
  have h3 := hL.M100
  have : ((Aq ε q : ℕ) : ℝ) ≤ ((Bq ε q : ℕ) : ℝ) := by linarith
  exact_mod_cast this

lemma t_gt (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) : (q : ℝ) ^ ε < (t : ℝ) := by
  have h := Tset_lb ht
  have h1 : ((2 * Aq ε q + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  have h2 := hL.Aq_ge
  push_cast at h1
  linarith

lemma t_le (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) : (t : ℝ) ≤ 2 * (q : ℝ) ^ ε := by
  have h := Tset_ub ht
  have h1 : (t : ℝ) ≤ ((2 * Bq ε q + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have h2 := hL.Bq_le
  push_cast at h1
  linarith

lemma t_two_le (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) : 2 ≤ t := by
  have h := hL.t_gt ht
  have h2 := hL.M100
  have : (2 : ℝ) ≤ (t : ℝ) := by linarith
  exact_mod_cast this

lemma ctx (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) : Ctx q p t :=
  { prime := hL.prime
    isPow := hL.isPow
    four_le := by have := hL.five_le; omega
    odd := Tset_odd ht
    ndvd := Tset_ndvd ht
    two_le := hL.t_two_le ht }

/-! ### The multiplier bounds -/

lemma mult_le (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) :
    (mult q p t : ℝ) ≤ 8 * (q : ℝ) ^ ε := by
  have hc := (hL.ctx ht).mult_lt
  have h1 : (mult q p t : ℝ) ≤ ((cf p * t : ℕ) : ℝ) := by exact_mod_cast hc.le
  have h2 : ((cf p : ℕ) : ℝ) ≤ 4 := by exact_mod_cast cf_le p
  have h3 := hL.t_le ht
  have h4 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  push_cast at h1
  nlinarith [h1, h2, h3, h4]

lemma mult_lt_q (hL : Large ε η q p) {t : ℕ} (ht : t ∈ Tq ε q p) : mult q p t < q := by
  have h1 := hL.mult_le ht
  have h2 := hL.q16
  have : (mult q p t : ℝ) < (q : ℝ) := by
    have hq := hL.qpos
    nlinarith
  exact_mod_cast this

lemma qm_le (hL : Large ε η q p) (hε0 : 0 < ε) {t : ℕ} (ht : t ∈ Tq ε q p) :
    (q : ℝ) * (mult q p t : ℝ) + 1 ≤ 25 * (q : ℝ) ^ (1 + ε) := by
  have h1 := hL.mult_le ht
  have h2 := hL.qpos
  have h3 : (q : ℝ) * (mult q p t : ℝ) ≤ (q : ℝ) * (8 * (q : ℝ) ^ ε) :=
    mul_le_mul_of_nonneg_left h1 h2.le
  have h4 := hL.rpow_one_add
  have h5 := hL.one_le_rpow_one_add hε0
  nlinarith [h3, h4, h5]

lemma neighbor_le (hL : Large ε η q p) (hε0 : 0 < ε) {t : ℕ} (ht : t ∈ Tq ε q p) :
    ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε) := by
  have hc := hL.ctx ht
  have hcast := hc.neighbor_cast
  have hs := hc.sgn_cases
  have h1 := hL.qm_le hε0 ht
  have hσle : sgn q p t ≤ 1 := by rcases hs with hσ | hσ <;> simp [hσ]
  have hZ : ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ)
      ≤ (q : ℤ) * ((mult q p t : ℕ) : ℤ) + 1 := by rw [hcast]; linarith
  have hR : ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℝ)
      ≤ (q : ℝ) * (mult q p t : ℝ) + 1 := by exact_mod_cast hZ
  linarith

end Large


open Classical in
lemma NoBig_subset (ε η : ℝ) (q p : ℕ) : NoBig ε η q p ⊆ Tq ε q p := by
  unfold NoBig; exact Finset.filter_subset _ _

open Classical in
lemma GoodT_subset (ε η : ℝ) (q p : ℕ) : GoodT ε η q p ⊆ NoBig ε η q p := by
  unfold GoodT; exact Finset.filter_subset _ _

open Classical in
lemma pkFib_subset (ε η : ℝ) (q p l b : ℕ) (σ : ℤ) :
    pkFib ε η q p l b σ ⊆ NoBig ε η q p := by
  unfold pkFib; exact Finset.filter_subset _ _

/-- **Signed uniqueness mod `u`**: for a fixed sign, a modulus coprime to `q` and exceeding the
spread of the multipliers determines the multiplier. -/
lemma unique_m_signed {q u m₁ m₂ : ℕ} {σ : ℤ} (hcop : Nat.Coprime u q)
    (h1 : (u : ℤ) ∣ (q : ℤ) * (m₁ : ℤ) + σ) (h2 : (u : ℤ) ∣ (q : ℤ) * (m₂ : ℤ) + σ)
    (hlen : |(m₂ : ℤ) - (m₁ : ℤ)| < (u : ℤ)) : m₁ = m₂ := by
  have hdvd : (u : ℤ) ∣ (q : ℤ) * ((m₂ : ℤ) - (m₁ : ℤ)) := by
    have h := dvd_sub h2 h1
    have e : (q : ℤ) * (m₂ : ℤ) + σ - ((q : ℤ) * (m₁ : ℤ) + σ)
        = (q : ℤ) * ((m₂ : ℤ) - (m₁ : ℤ)) := by ring
    rwa [e] at h
  have hcopZ : IsCoprime (u : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
  have hdvd' : (u : ℤ) ∣ ((m₂ : ℤ) - (m₁ : ℤ)) := hcopZ.dvd_of_dvd_mul_left hdvd
  have hz : (m₂ : ℤ) - (m₁ : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd' hlen
  omega

/-- Every fibre of `t ↦ mult q p t` has at most `2 V(q)` elements: `t` divides `q m ± 1`. -/
lemma fiber_card_le (ε : ℝ) (q p m : ℕ) (S : Finset ℕ)
    (hS : ∀ t ∈ S, Ctx q p t ∧ mult q p t = m) (hm1 : 1 ≤ m) (hq : 4 ≤ q)
    (hb : (q : ℝ) * (m : ℝ) + 1 ≤ 25 * (q : ℝ) ^ (1 + ε)) :
    S.card ≤ 2 * Venv ε q := by
  have hqm : 4 * 1 ≤ q * m := Nat.mul_le_mul hq hm1
  have hqm2 : 2 ≤ q * m := by omega
  have hsub : S ⊆ (q * m + 1).divisors ∪ (q * m - 1).divisors := by
    intro t ht
    obtain ⟨hctx, hmt⟩ := hS t ht
    have h := hctx.t_mem_divisors
    rwa [hmt] at h
  have h1 : (q * m + 1).divisors.card ≤ Venv ε q := by
    refine tau_le_Venv ε q _ (by omega) ?_
    push_cast
    linarith
  have h2 : (q * m - 1).divisors.card ≤ Venv ε q := by
    refine tau_le_Venv ε q _ (by omega) ?_
    have he : ((q * m - 1 : ℕ) : ℝ) = (q : ℝ) * (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [he]; linarith
  calc S.card ≤ ((q * m + 1).divisors ∪ (q * m - 1).divisors).card := Finset.card_le_card hsub
    _ ≤ (q * m + 1).divisors.card + (q * m - 1).divisors.card := Finset.card_union_le _ _
    _ ≤ 2 * Venv ε q := by omega

namespace Large

variable {ε η : ℝ} {q p : ℕ}

/-- The exponent of any prime power dividing a neighbor is at most `Bmx q = ⌊5 log q⌋`. -/
lemma bmx (hL : Large ε η q p) (hε0 : 0 < ε) {t : ℕ} (ht : t ∈ Tq ε q p)
    {l b : ℕ} (hl : l.Prime) (hb : 0 < b)
    (hdvd : l ^ b ∣ neighbor q (mult q p t) (sgn q p t)) : b ≤ Bmx q := by
  have hn1 : 1 ≤ neighbor q (mult q p t) (sgn q p t) := (hL.ctx ht).neighbor_pos
  have hdvdle : l ^ b ≤ neighbor q (mult q p t) (sgn q p t) := Nat.le_of_dvd (by omega) hdvd
  have hnle := hL.neighbor_le hε0 ht
  have hle : ((l ^ b : ℕ) : ℝ) ≤ 25 * (q : ℝ) ^ (1 + ε) := by
    have : ((l ^ b : ℕ) : ℝ) ≤ ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℝ) := by
      exact_mod_cast hdvdle
    linarith
  have h2b : ((2 ^ b : ℕ) : ℝ) ≤ ((l ^ b : ℕ) : ℝ) := by
    have : (2 : ℕ) ^ b ≤ l ^ b := Nat.pow_le_pow_left hl.two_le b
    exact_mod_cast this
  have hq3 : 25 * (q : ℝ) ^ (1 + ε) ≤ (q : ℝ) ^ (3 : ℝ) := by
    have hsplit : (q : ℝ) ^ (2 - ε) * (q : ℝ) ^ (1 + ε) = (q : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_add hL.qpos]; congr 1; ring
    nlinarith [hL.q25, hL.one_le_rpow_one_add hε0]
  have hlog : (b : ℝ) * Real.log 2 ≤ 3 * Real.log q := by
    have h1 : Real.log (((2 ^ b : ℕ) : ℝ)) ≤ Real.log ((q : ℝ) ^ (3 : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [show (((2 : ℕ) ^ b : ℕ) : ℝ) = (2 : ℝ) ^ b by push_cast; ring, Real.log_pow,
      Real.log_rpow hL.qpos] at h1
    linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogq : (0 : ℝ) ≤ Real.log q := by have := hL.log800; linarith
  have hbnn : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hfin : (b : ℝ) ≤ 5 * Real.log q := by nlinarith [hlog, hlog2, hlogq, hbnn]
  exact Nat.le_floor hfin

/-- Each witness prime power and sign accounts for at most `V(q)` parameters (docs (F7)). -/
lemma pkFib_card_le (hL : Large ε η q p) (hε0 : 0 < ε) {l b : ℕ} (σ : ℤ)
    (hl : l.Prime) (hb : 0 < b) (hbig : q ≤ l ^ b) :
    (pkFib ε η q p l b σ).card ≤ Venv ε q := by
  rcases Finset.eq_empty_or_nonempty (pkFib ε η q p l b σ) with hemp | hne
  · rw [hemp]; simp
  obtain ⟨t₀, ht₀⟩ := hne
  have hmemT : ∀ t ∈ pkFib ε η q p l b σ, t ∈ Tq ε q p := fun t ht =>
    NoBig_subset ε η q p (pkFib_subset ε η q p l b σ ht)
  have hprop : ∀ t ∈ pkFib ε η q p l b σ,
      sgn q p t = σ ∧ l ^ b ∣ neighbor q (mult q p t) (sgn q p t) := by
    intro t ht
    have h := ht
    rw [pkFib, Finset.mem_filter] at h
    exact h.2
  have hdvdZ : ∀ t ∈ pkFib ε η q p l b σ,
      ((l ^ b : ℕ) : ℤ) ∣ (q : ℤ) * ((mult q p t : ℕ) : ℤ) + σ := by
    intro t ht
    obtain ⟨hσt, hdvdt⟩ := hprop t ht
    have hz : ((l ^ b : ℕ) : ℤ) ∣ ((neighbor q (mult q p t) (sgn q p t) : ℕ) : ℤ) := by
      exact_mod_cast hdvdt
    rw [(hL.ctx (hmemT t ht)).neighbor_cast, hσt] at hz
    exact hz
  have hσ₀ := (hprop t₀ ht₀).1
  have hctx₀ := hL.ctx (hmemT t₀ ht₀)
  have hall : ∀ t ∈ pkFib ε η q p l b σ, mult q p t = mult q p t₀ := by
    intro t ht
    have hcop : Nat.Coprime (l ^ b) q :=
      (hL.ctx (hmemT t ht)).coprime_primepow hl hb (hprop t ht).2
    have hlt1 : mult q p t < q := hL.mult_lt_q (hmemT t ht)
    have hlt2 : mult q p t₀ < q := hL.mult_lt_q (hmemT t₀ ht₀)
    have hqle : (q : ℤ) ≤ ((l ^ b : ℕ) : ℤ) := by exact_mod_cast hbig
    have hlen : |((mult q p t₀ : ℕ) : ℤ) - ((mult q p t : ℕ) : ℤ)| < ((l ^ b : ℕ) : ℤ) := by
      have e1 : ((mult q p t : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hlt1
      have e2 : ((mult q p t₀ : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hlt2
      have e3 : (0 : ℤ) ≤ ((mult q p t : ℕ) : ℤ) := by positivity
      have e4 : (0 : ℤ) ≤ ((mult q p t₀ : ℕ) : ℤ) := by positivity
      rw [abs_lt]; omega
    exact unique_m_signed hcop (hdvdZ t ht) (hdvdZ t₀ ht₀) hlen
  have hsub : pkFib ε η q p l b σ ⊆
      (neighbor q (mult q p t₀) (sgn q p t₀)).divisors := by
    intro t ht
    have hd := (hL.ctx (hmemT t ht)).t_dvd_neighbor
    rw [hall t ht, (hprop t ht).1, ← hσ₀] at hd
    exact Nat.mem_divisors.2 ⟨hd, by have := hctx₀.neighbor_pos; omega⟩
  calc (pkFib ε η q p l b σ).card
      ≤ (neighbor q (mult q p t₀) (sgn q p t₀)).divisors.card := Finset.card_le_card hsub
    _ ≤ Venv ε q := tau_le_Venv ε q _ hctx₀.neighbor_pos (hL.neighbor_le hε0 (hmemT t₀ ht₀))


lemma Dq_two_le (hL : Large ε η q p) : 2 ≤ Dq ε η q := by
  have h1 : (q : ℝ) ^ (ε - η) ≤ ((Dq ε η q : ℕ) : ℝ) := Nat.le_ceil _
  have h2 := hL.D2
  have : (2 : ℝ) ≤ ((Dq ε η q : ℕ) : ℝ) := by linarith
  exact_mod_cast this

lemma Dq_le (hL : Large ε η q p) : ((Dq ε η q : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ (ε - η) := by
  have h1 : ((Dq ε η q : ℕ) : ℝ) < (q : ℝ) ^ (ε - η) + 1 := by
    rw [Dq]; exact Nat.ceil_lt_add_one (by positivity)
  have h2 := hL.D2
  linarith

lemma Bmx_le (hL : Large ε η q p) : ((Bmx q : ℕ) : ℝ) ≤ 5 * (q : ℝ) ^ (η / 4) := by
  have h1 : ((Bmx q : ℕ) : ℝ) ≤ 5 * Real.log q := by
    rw [Bmx]; exact Nat.floor_le (by have := hL.log800; linarith)
  have h2 := hL.logle
  linarith

open Classical in
/-- Docs display (F7): the parameters whose neighbor is not strictly `q`-powersmooth. -/
lemma bad2_card_le (hL : Large ε η q p) (hε0 : 0 < ε) (_hη0 : 0 < η) :
    (((NoBig ε η q p).filter
        (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card : ℝ)
      ≤ (q : ℝ) ^ ε / 200 := by
  classical
  have hD2 := hL.Dq_two_le
  have hsub : (NoBig ε η q p).filter
      (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))
      ⊆ (wgrid ε η q).biUnion (fun x => pkFib ε η q p x.1.1 x.1.2 x.2) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htN, hns⟩ := ht
    have htT : t ∈ Tq ε q p := NoBig_subset ε η q p htN
    have hnobig : ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q := by
      have h := htN; rw [NoBig, Finset.mem_filter] at h; exact h.2
    rw [Powersmooth] at hns
    push Not at hns
    obtain ⟨l, e, hl, he, hdvd, hgt⟩ := hns
    have hq5 := hL.five_le
    have hge : q ≤ l ^ e := by omega
    have hctx := hL.ctx htT
    have hlcf := hctx.big_primepow hl he hdvd hge
    have hlD : l ≤ Dq ε η q := by
      by_cases hp2 : p = 2
      · rw [Ctx.cf_eq_one hp2, one_mul] at hlcf
        exact hnobig l hl hlcf
      · rw [Ctx.cf_eq_four hp2] at hlcf
        rcases (Nat.Prime.dvd_mul hl).1 hlcf with h4 | ht'
        · have hl2 : l ∣ 2 := hl.dvd_of_dvd_pow (show l ∣ 2 ^ 2 by simpa using h4)
          have : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 hl2
          omega
        · exact hnobig l hl ht'
    have heB : e ≤ Bmx q := hL.bmx hε0 htT hl he hdvd
    refine Finset.mem_biUnion.2 ⟨((l, e), sgn q p t), ?_, ?_⟩
    · rw [wgrid, Finset.mem_filter]
      refine ⟨Finset.mem_product.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hl.two_le, hlD⟩, hl⟩,
         Finset.mem_Icc.2 ⟨he, heB⟩⟩, ?_⟩, hge⟩
      rcases hctx.sgn_cases with h | h <;> simp [h]
    · rw [pkFib, Finset.mem_filter]
      exact ⟨htN, rfl, hdvd⟩
  have hper : ∀ x ∈ wgrid ε η q, (pkFib ε η q p x.1.1 x.1.2 x.2).card ≤ Venv ε q := by
    intro x hx
    rw [wgrid, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨⟨⟨hxl, hxb⟩, _⟩, hxq⟩ := hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hxl
    rw [Finset.mem_Icc] at hxb
    exact hL.pkFib_card_le hε0 x.2 hxl.2 hxb.1 hxq
  have hcardN : ((NoBig ε η q p).filter
      (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card
      ≤ (wgrid ε η q).card * Venv ε q := by
    calc ((NoBig ε η q p).filter
        (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card
        ≤ ((wgrid ε η q).biUnion (fun x => pkFib ε η q p x.1.1 x.1.2 x.2)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ wgrid ε η q, (pkFib ε η q p x.1.1 x.1.2 x.2).card := Finset.card_biUnion_le
      _ ≤ (wgrid ε η q).card • Venv ε q := Finset.sum_le_card_nsmul _ _ _ hper
      _ = (wgrid ε η q).card * Venv ε q := by simp [smul_eq_mul]
  have hwg : (wgrid ε η q).card ≤ 2 * (Dq ε η q * Bmx q) := by
    have h1 : wgrid ε η q ⊆
        ((((Finset.Icc 2 (Dq ε η q)).filter Nat.Prime) ×ˢ Finset.Icc 1 (Bmx q)) ×ˢ
          ({1, -1} : Finset ℤ)) := by
      rw [wgrid]; exact Finset.filter_subset _ _
    have h2 := Finset.card_le_card h1
    rw [Finset.card_product, Finset.card_product] at h2
    have h3 : ((Finset.Icc 2 (Dq ε η q)).filter Nat.Prime).card ≤ Dq ε η q := by
      calc ((Finset.Icc 2 (Dq ε η q)).filter Nat.Prime).card
          ≤ (Finset.Icc 2 (Dq ε η q)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = Dq ε η q + 1 - 2 := Nat.card_Icc _ _
        _ ≤ Dq ε η q := by omega
    have h4 : (Finset.Icc 1 (Bmx q)).card = Bmx q := by rw [Nat.card_Icc]; omega
    have h5 : ({1, -1} : Finset ℤ).card = 2 := by decide
    rw [h4, h5] at h2
    calc (wgrid ε η q).card
        ≤ (((Finset.Icc 2 (Dq ε η q)).filter Nat.Prime).card * Bmx q) * 2 := h2
      _ ≤ (Dq ε η q * Bmx q) * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_right _ h3)
      _ = 2 * (Dq ε η q * Bmx q) := by ring
  -- pass to the reals
  have hqpos := hL.qpos
  have hXpos : (0 : ℝ) < (q : ℝ) ^ (ε - η) := Real.rpow_pos_of_pos hqpos _
  have hYpos : (0 : ℝ) < (q : ℝ) ^ (η / 4) := Real.rpow_pos_of_pos hqpos _
  have hεpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqpos _
  have hD := hL.Dq_le
  have hB := hL.Bmx_le
  have hV := hL.Vle
  have hDnn : (0 : ℝ) ≤ ((Dq ε η q : ℕ) : ℝ) := by positivity
  have hBnn : (0 : ℝ) ≤ ((Bmx q : ℕ) : ℝ) := by positivity
  have hVnn : (0 : ℝ) ≤ ((Venv ε q : ℕ) : ℝ) := by positivity
  have hR1 : (((NoBig ε η q p).filter
      (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card : ℝ)
      ≤ 2 * (((Dq ε η q : ℕ) : ℝ) * ((Bmx q : ℕ) : ℝ)) * ((Venv ε q : ℕ) : ℝ) := by
    have h : (((NoBig ε η q p).filter
        (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card : ℝ)
        ≤ ((2 * (Dq ε η q * Bmx q) : ℕ) : ℝ) * ((Venv ε q : ℕ) : ℝ) := by
      have hstep : ((NoBig ε η q p).filter
          (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card
          ≤ (2 * (Dq ε η q * Bmx q)) * Venv ε q :=
        le_trans hcardN (Nat.mul_le_mul_right _ hwg)
      exact_mod_cast hstep
    push_cast at h
    linarith
  have hs1 : ((Dq ε η q : ℕ) : ℝ) * ((Bmx q : ℕ) : ℝ)
      ≤ (2 * (q : ℝ) ^ (ε - η)) * (5 * (q : ℝ) ^ (η / 4)) :=
    mul_le_mul hD hB hBnn (by positivity)
  have hs2 : 2 * (((Dq ε η q : ℕ) : ℝ) * ((Bmx q : ℕ) : ℝ)) * ((Venv ε q : ℕ) : ℝ)
      ≤ 2 * ((2 * (q : ℝ) ^ (ε - η)) * (5 * (q : ℝ) ^ (η / 4))) * (q : ℝ) ^ (η / 4) := by
    have ha : 2 * (((Dq ε η q : ℕ) : ℝ) * ((Bmx q : ℕ) : ℝ))
        ≤ 2 * ((2 * (q : ℝ) ^ (ε - η)) * (5 * (q : ℝ) ^ (η / 4))) := by linarith
    have := mul_le_mul ha hV hVnn (by positivity)
    linarith
  have e1 : (q : ℝ) ^ (ε - η) * (q : ℝ) ^ (η / 4) * (q : ℝ) ^ (η / 4)
      = (q : ℝ) ^ ε * (q : ℝ) ^ (-(η / 2)) := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    congr 1; ring
  have e2 : 2 * ((2 * (q : ℝ) ^ (ε - η)) * (5 * (q : ℝ) ^ (η / 4))) * (q : ℝ) ^ (η / 4)
      = 20 * ((q : ℝ) ^ ε * (q : ℝ) ^ (-(η / 2))) := by
    rw [← e1]; ring
  have hbad := hL.bad2
  rw [e2] at hs2
  have hfinal : 20 * ((q : ℝ) ^ ε * (q : ℝ) ^ (-(η / 2))) ≤ (q : ℝ) ^ ε / 200 := by
    have h := mul_le_mul_of_nonneg_left hbad hεpos.le
    nlinarith [h]
  linarith [hR1, hs2, hfinal]

open Classical in
/-- Docs display (F8): the parameters whose multiplier is below `R(q)`. -/
lemma bad3_card_le (hL : Large ε η q p) (hε0 : 0 < ε) :
    (((NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ)))).card : ℝ)
      ≤ (q : ℝ) ^ ε / 200 := by
  classical
  have hqpos := hL.qpos
  have hVge : (1 : ℝ) ≤ ((Venv ε q : ℕ) : ℝ) := hL.Vone hε0
  have hlog := hL.log800
  have hEpos : (0 : ℝ) < Eenv ε q := by
    rw [Eenv]; positivity
  have hRpos : (0 : ℝ) < Rq ε q := by
    rw [Rq]; exact div_pos (Real.rpow_pos_of_pos hqpos _) hEpos
  set S := (NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ))) with hSdef
  have hST : ∀ t ∈ S, t ∈ Tq ε q p := by
    intro t ht
    rw [hSdef, Finset.mem_filter] at ht
    exact NoBig_subset ε η q p ht.1
  have hfib : ∀ a ∈ S.image (mult q p),
      (S.filter (fun x => mult q p x = a)).card ≤ 2 * Venv ε q := by
    intro a ha
    obtain ⟨t, htS, hta⟩ := Finset.mem_image.1 ha
    refine fiber_card_le ε q p a _ ?_ ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter] at hu
      exact ⟨hL.ctx (hST u hu.1), hu.2⟩
    · rw [← hta]; exact (hL.ctx (hST t htS)).mult_pos
    · have := hL.five_le; omega
    · rw [← hta]; exact hL.qm_le hε0 (hST t htS)
  have hcard : S.card ≤ (2 * Venv ε q) * (S.image (mult q p)).card :=
    Finset.card_le_mul_card_image _ _ hfib
  have himg : (S.image (mult q p)).card ≤ ⌊Rq ε q⌋₊ + 1 := by
    have hsub : S.image (mult q p) ⊆ Finset.range (⌊Rq ε q⌋₊ + 1) := by
      intro a ha
      obtain ⟨t, htS, hta⟩ := Finset.mem_image.1 ha
      rw [hSdef, Finset.mem_filter] at htS
      have hlt : (mult q p t : ℝ) < Rq ε q := not_le.1 htS.2
      have : mult q p t ≤ ⌊Rq ε q⌋₊ := Nat.le_floor hlt.le
      rw [Finset.mem_range, ← hta]
      omega
    calc (S.image (mult q p)).card ≤ (Finset.range (⌊Rq ε q⌋₊ + 1)).card :=
          Finset.card_le_card hsub
      _ = ⌊Rq ε q⌋₊ + 1 := Finset.card_range _
  have hfloor : ((⌊Rq ε q⌋₊ : ℕ) : ℝ) ≤ Rq ε q := Nat.floor_le hRpos.le
  have hR1 : (S.card : ℝ) ≤ 2 * ((Venv ε q : ℕ) : ℝ) * (Rq ε q + 1) := by
    have h : S.card ≤ (2 * Venv ε q) * (⌊Rq ε q⌋₊ + 1) :=
      le_trans hcard (Nat.mul_le_mul_left _ himg)
    have h' : (S.card : ℝ) ≤ ((2 * Venv ε q : ℕ) : ℝ) * (((⌊Rq ε q⌋₊ + 1 : ℕ)) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    nlinarith [h', hfloor, hVge]
  -- `2 V R = 2 q^ε / (V log q) ≤ q^ε / 400`
  have hterm1 : 2 * ((Venv ε q : ℕ) : ℝ) * Rq ε q ≤ (q : ℝ) ^ ε / 400 := by
    have heq : 2 * ((Venv ε q : ℕ) : ℝ) * Rq ε q
        = 2 * (q : ℝ) ^ ε / (((Venv ε q : ℕ) : ℝ) * Real.log q) := by
      rw [Rq, Eenv]
      field_simp
    rw [heq]
    have hden : (800 : ℝ) ≤ ((Venv ε q : ℕ) : ℝ) * Real.log q := by nlinarith [hVge, hlog]
    have hdenpos : (0 : ℝ) < ((Venv ε q : ℕ) : ℝ) * Real.log q := by linarith
    have hεpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqpos _
    rw [div_le_iff₀ hdenpos]
    linarith [mul_le_mul_of_nonneg_left hden hεpos.le]
  have hterm2 : 2 * ((Venv ε q : ℕ) : ℝ) ≤ (q : ℝ) ^ ε / 400 := by
    have hV := hL.Vle
    have he3 : (q : ℝ) ^ ε * (q : ℝ) ^ (-(ε - η / 4)) = (q : ℝ) ^ (η / 4) := by
      rw [← Real.rpow_add hqpos]; congr 1; ring
    have hεpos : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hqpos _
    have hbad := hL.bad3
    have h1 := mul_le_mul_of_nonneg_left hbad hεpos.le
    have h2 : 800 * (q : ℝ) ^ (η / 4) ≤ (q : ℝ) ^ ε := by
      calc 800 * (q : ℝ) ^ (η / 4) = 800 * ((q : ℝ) ^ ε * (q : ℝ) ^ (-(ε - η / 4))) := by rw [he3]
        _ ≤ (q : ℝ) ^ ε := by linarith
    linarith [hV, h2]
  linarith [hR1, hterm1, hterm2]


/-! ### The surviving parameters -/

lemma Tq_card_ge (hL : Large ε η q p) : (q : ℝ) ^ ε / 3 - 3 ≤ ((Tq ε q p).card : ℝ) := by
  have h := Tset_card_ge p (Aq ε q) (Bq ε q) hL.prime hL.Aq_le_Bq
  have hA1 := hL.Aq_ge
  have hA2 := hL.Aq_le
  have hB1 := hL.Bq_ge
  have hB2 := hL.Bq_le
  have hM := hL.M100
  rw [Tq]
  linarith

open Classical in
lemma NoBig_card_ge (hL : Large ε η q p) :
    ((Tq ε q p).card : ℝ) - (q : ℝ) ^ ε / 200 ≤ ((NoBig ε η q p).card : ℝ) := by
  have hsplit : (NoBig ε η q p).card
      + ((Tq ε q p).filter (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)).card
      = (Tq ε q p).card := by
    rw [NoBig]; exact Finset.card_filter_add_card_filter_not _
  have hsub : (Tq ε q p).filter (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)
      ⊆ bigPrimeFactor (2 * Aq ε q + 1) (2 * Bq ε q + 1) (Dq ε η q) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htT, hbad⟩ := ht
    push Not at hbad
    obtain ⟨l, hl, hdvd, hgt⟩ := hbad
    rw [bigPrimeFactor, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Tset_lb htT, Tset_ub htT⟩, l, hl, hgt, hdvd⟩
  have hA : (q : ℝ) ^ ε ≤ ((2 * Aq ε q + 1 : ℕ) : ℝ) := by
    have := hL.Aq_ge
    push_cast
    linarith
  have hB : ((2 * Bq ε q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ε := by
    have := hL.Bq_le
    push_cast
    linarith
  have hbnd := hL.bigP (2 * Aq ε q + 1) (2 * Bq ε q + 1) hA hB
  have hle : (((Tq ε q p).filter
      (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)).card : ℝ) ≤ (q : ℝ) ^ ε / 200 := by
    have h1 : ((Tq ε q p).filter (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)).card
        ≤ (bigPrimeFactor (2 * Aq ε q + 1) (2 * Bq ε q + 1) (Dq ε η q)).card :=
      Finset.card_le_card hsub
    have h2 : (((Tq ε q p).filter
        (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)).card : ℝ)
        ≤ ((bigPrimeFactor (2 * Aq ε q + 1) (2 * Bq ε q + 1) (Dq ε η q)).card : ℝ) := by
      exact_mod_cast h1
    linarith
  have hsplitR : ((NoBig ε η q p).card : ℝ)
      + (((Tq ε q p).filter (fun t => ¬ ∀ l : ℕ, l.Prime → l ∣ t → l ≤ Dq ε η q)).card : ℝ)
      = ((Tq ε q p).card : ℝ) := by exact_mod_cast hsplit
  linarith

open Classical in
lemma GoodT_card_ge (hL : Large ε η q p) (hε0 : 0 < ε) (hη0 : 0 < η) :
    (q : ℝ) ^ ε / 4 ≤ ((GoodT ε η q p).card : ℝ) := by
  have hsplit : (GoodT ε η q p).card
      + ((NoBig ε η q p).filter (fun t =>
          ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
             Rq ε q ≤ (mult q p t : ℝ)))).card = (NoBig ε η q p).card := by
    rw [GoodT]; exact Finset.card_filter_add_card_filter_not _
  have hsub : (NoBig ε η q p).filter (fun t =>
      ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
         Rq ε q ≤ (mult q p t : ℝ)))
      ⊆ ((NoBig ε η q p).filter
          (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t))))
        ∪ ((NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ)))) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htN, hnot⟩ := ht
    by_cases hps : Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t))
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨htN, fun hc => hnot ⟨hps, hc⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨htN, hps⟩)
  have hcnt : (((NoBig ε η q p).filter (fun t =>
      ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
         Rq ε q ≤ (mult q p t : ℝ)))).card : ℝ) ≤ (q : ℝ) ^ ε / 200 + (q : ℝ) ^ ε / 200 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((NoBig ε η q p).filter
        (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t))))
      ((NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ))))
    have h3 : ((NoBig ε η q p).filter (fun t =>
        ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
           Rq ε q ≤ (mult q p t : ℝ)))).card
        ≤ ((NoBig ε η q p).filter
            (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card
          + ((NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ)))).card :=
      le_trans h1 h2
    have h4 : (((NoBig ε η q p).filter (fun t =>
        ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
           Rq ε q ≤ (mult q p t : ℝ)))).card : ℝ)
        ≤ (((NoBig ε η q p).filter
            (fun t => ¬ Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)))).card : ℝ)
          + (((NoBig ε η q p).filter (fun t => ¬ (Rq ε q ≤ (mult q p t : ℝ)))).card : ℝ) := by
      exact_mod_cast h3
    linarith [hL.bad2_card_le hε0 hη0, hL.bad3_card_le hε0]
  have hsplitR : ((GoodT ε η q p).card : ℝ)
      + (((NoBig ε η q p).filter (fun t =>
          ¬ (Powersmooth (q - 1) (neighbor q (mult q p t) (sgn q p t)) ∧
             Rq ε q ≤ (mult q p t : ℝ)))).card : ℝ) = ((NoBig ε η q p).card : ℝ) := by
    exact_mod_cast hsplit
  have hT := hL.Tq_card_ge
  have hN := hL.NoBig_card_ge
  have hM := hL.M100
  linarith

open Classical in
lemma Iq_card_ge (hL : Large ε η q p) (hε0 : 0 < ε) (hη0 : 0 < η) :
    (q : ℝ) ^ ε / (8 * (Venv ε q : ℝ)) ≤ ((Iq ε η q p).card : ℝ) := by
  have hGT : ∀ t ∈ GoodT ε η q p, t ∈ Tq ε q p := fun t ht =>
    NoBig_subset ε η q p (GoodT_subset ε η q p ht)
  have hfib : ∀ a ∈ (GoodT ε η q p).image (mult q p),
      ((GoodT ε η q p).filter (fun x => mult q p x = a)).card ≤ 2 * Venv ε q := by
    intro a ha
    obtain ⟨t, htG, hta⟩ := Finset.mem_image.1 ha
    refine fiber_card_le ε q p a _ ?_ ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter] at hu
      exact ⟨hL.ctx (hGT u hu.1), hu.2⟩
    · rw [← hta]; exact (hL.ctx (hGT t htG)).mult_pos
    · have := hL.five_le; omega
    · rw [← hta]; exact hL.qm_le hε0 (hGT t htG)
  have hcard : (GoodT ε η q p).card ≤ (2 * Venv ε q) * (Iq ε η q p).card := by
    rw [Iq]; exact Finset.card_le_mul_card_image _ _ hfib
  have hcardR : ((GoodT ε η q p).card : ℝ)
      ≤ 2 * ((Venv ε q : ℕ) : ℝ) * ((Iq ε η q p).card : ℝ) := by
    have : ((GoodT ε η q p).card : ℝ) ≤ (((2 * Venv ε q) * (Iq ε η q p).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at this
    linarith
  have hG := hL.GoodT_card_ge hε0 hη0
  have hV := hL.Vone hε0
  have hVpos : (0 : ℝ) < 8 * ((Venv ε q : ℕ) : ℝ) := by linarith
  rw [div_le_iff₀ hVpos]
  nlinarith [hG, hcardR, hV]

end Large

/-! ## The fiber -/

open Classical in
/-- A choice of parameter `t` realizing each multiplier of the fiber. -/
noncomputable def tpick (ε η : ℝ) (q p m : ℕ) : ℕ :=
  if h : ∃ t ∈ GoodT ε η q p, mult q p t = m then h.choose else 0

/-- The sign attached to each multiplier of the fiber. -/
noncomputable def sigmaOf (ε η : ℝ) (q p : ℕ) : ℕ → ℤ := fun m => sgn q p (tpick ε η q p m)

lemma tpick_spec (ε η : ℝ) (q p m : ℕ) (hm : m ∈ Iq ε η q p) :
    tpick ε η q p m ∈ GoodT ε η q p ∧ mult q p (tpick ε η q p m) = m := by
  have h : ∃ t ∈ GoodT ε η q p, mult q p t = m := by
    obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 hm
    exact ⟨t, ht, hteq⟩
  unfold tpick
  split_ifs
  exact h.choose_spec

open Classical in
lemma pick_props (ε η : ℝ) (q p : ℕ) {m : ℕ} (hm : m ∈ Iq ε η q p) :
    tpick ε η q p m ∈ Tq ε q p ∧ mult q p (tpick ε η q p m) = m ∧
      Powersmooth (q - 1) (neighbor q m (sigmaOf ε η q p m)) ∧ Rq ε q ≤ (m : ℝ) := by
  obtain ⟨htG, htm⟩ := tpick_spec ε η q p m hm
  have htN := GoodT_subset ε η q p htG
  have htT := NoBig_subset ε η q p htN
  have hG := htG
  rw [GoodT, Finset.mem_filter] at hG
  obtain ⟨_, hsm, hlow⟩ := hG
  have hσ : sigmaOf ε η q p m = sgn q p (tpick ε η q p m) := rfl
  rw [hσ]
  set t := tpick ε η q p m with ht
  refine ⟨htT, htm, ?_, ?_⟩
  · rw [← htm]; exact hsm
  · rw [← htm]; exact hlow

namespace Large

variable {ε η : ℝ} {q p : ℕ}

open Classical in
/-- The signed fiber produced by the construction (docs Lemma F1, Step 4). -/
noncomputable def fiber (hL : Large ε η q p) : SignedFiber ε q where
  I := Iq ε η q p
  σ := sigmaOf ε η q p
  sign := by
    intro m hm
    obtain ⟨htT, _, _, _⟩ := pick_props ε η q p hm
    exact (hL.ctx htT).sgn_cases
  lower := fun m hm => (pick_props ε η q p hm).2.2.2
  upper := by
    intro m hm
    obtain ⟨htT, htm, _, _⟩ := pick_props ε η q p hm
    rw [← htm]; exact hL.mult_le htT
  lt := by
    intro m hm
    obtain ⟨htT, htm, _, _⟩ := pick_props ε η q p hm
    rw [← htm]; exact hL.mult_lt_q htT
  coprime := by
    intro m hm
    obtain ⟨htT, htm, _, _⟩ := pick_props ε η q p hm
    rw [← htm]; exact (hL.ctx htT).coprime_mult
  two_le := by
    intro m hm
    obtain ⟨htT, htm, _, _⟩ := pick_props ε η q p hm
    rw [← htm]; exact (hL.ctx htT).two_le_qm
  smooth := fun m hm => (pick_props ε η q p hm).2.2.1
  four := by
    intro m hm
    obtain ⟨htT, htm, _, _⟩ := pick_props ε η q p hm
    have hσ : sigmaOf ε η q p m = sgn q p (tpick ε η q p m) := rfl
    rw [hσ]
    set t := tpick ε η q p m with ht
    rw [← htm]
    exact (hL.ctx htT).four_dvd_slot
  slot_inj := by
    intro m₁ h₁ m₂ h₂ heq
    have hm₁ : m₁ ∈ Iq ε η q p := Finset.mem_coe.1 h₁
    have hm₂ : m₂ ∈ Iq ε η q p := Finset.mem_coe.1 h₂
    obtain ⟨htT₁, htm₁, _, _⟩ := pick_props ε η q p hm₁
    obtain ⟨htT₂, htm₂, _, _⟩ := pick_props ε η q p hm₂
    have hc₁ := hL.ctx htT₁
    have hc₂ := hL.ctx htT₂
    have heq' : slot q m₁ (sigmaOf ε η q p m₁) = slot q m₂ (sigmaOf ε η q p m₂) := heq
    have hq5 := hL.five_le
    by_cases hp2 : p = 2
    · have e₁ : slot q m₁ (sigmaOf ε η q p m₁) = q * m₁ := by
        have h := hc₁.slot_eq_even hp2
        rw [htm₁] at h; exact h
      have e₂ : slot q m₂ (sigmaOf ε η q p m₂) = q * m₂ := by
        have h := hc₂.slot_eq_even hp2
        rw [htm₂] at h; exact h
      rw [e₁, e₂] at heq'
      exact Nat.eq_of_mul_eq_mul_left (by omega) heq'
    · have e₁ : slot q m₁ (sigmaOf ε η q p m₁) = neighbor q m₁ (sigmaOf ε η q p m₁) := by
        have h := hc₁.slot_eq_odd hp2
        rw [htm₁] at h; exact h
      have e₂ : slot q m₂ (sigmaOf ε η q p m₂) = neighbor q m₂ (sigmaOf ε η q p m₂) := by
        have h := hc₂.slot_eq_odd hp2
        rw [htm₂] at h; exact h
      have hz₁ : ((neighbor q m₁ (sigmaOf ε η q p m₁) : ℕ) : ℤ)
          = (q : ℤ) * (m₁ : ℤ) + sigmaOf ε η q p m₁ := by
        have h := hc₁.neighbor_cast
        rw [htm₁] at h; exact h
      have hz₂ : ((neighbor q m₂ (sigmaOf ε η q p m₂) : ℕ) : ℤ)
          = (q : ℤ) * (m₂ : ℤ) + sigmaOf ε η q p m₂ := by
        have h := hc₂.neighbor_cast
        rw [htm₂] at h; exact h
      rw [e₁, e₂] at heq'
      have hcast : (q : ℤ) * (m₁ : ℤ) + sigmaOf ε η q p m₁
          = (q : ℤ) * (m₂ : ℤ) + sigmaOf ε η q p m₂ := by
        rw [← hz₁, ← hz₂, heq']
      have hs1 : sigmaOf ε η q p m₁ = 1 ∨ sigmaOf ε η q p m₁ = -1 := hc₁.sgn_cases
      have hs2 : sigmaOf ε η q p m₂ = 1 ∨ sigmaOf ε η q p m₂ = -1 := hc₂.sgn_cases
      by_contra hne
      have hne' : (m₁ : ℤ) - (m₂ : ℤ) ≠ 0 := fun h => hne (by omega)
      have habs : 1 ≤ |(m₁ : ℤ) - (m₂ : ℤ)| := by
        rcases lt_trichotomy ((m₁ : ℤ) - (m₂ : ℤ)) 0 with h | h | h
        · rw [abs_of_neg h]; omega
        · exact absurd h hne'
        · rw [abs_of_pos h]; omega
      have hkey : (q : ℤ) * ((m₁ : ℤ) - (m₂ : ℤ))
          = sigmaOf ε η q p m₂ - sigmaOf ε η q p m₁ := by linarith [hcast]
      have hb : |(q : ℤ) * ((m₁ : ℤ) - (m₂ : ℤ))| ≤ 2 := by
        rw [hkey]
        rcases hs1 with s1 | s1 <;> rcases hs2 with s2 | s2 <;> rw [s1, s2] <;> norm_num
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ))] at hb
      have hq5Z : (5 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq5
      nlinarith [hb, habs, hq5Z]

end Large

/-! ## Lemma F1 -/

end SignedF1

open SignedF1 in
/-- **Lemma F1** (docs `elementary_replacements.md`, Section 2, displays (F1)–(F8)): for every
sufficiently large prime power `q` there is a signed correction fiber at `q` with at least
`q^ε / (8 V(q))` multipliers. -/
theorem lemmaF1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∃ F : SignedFiber ε q, (q : ℝ) ^ ε / (8 * (Venv ε q : ℝ)) ≤ (F.I.card : ℝ) := by
  obtain ⟨η, hη0, hηε, hbig⟩ := bigPrime_gen ε hε0 hε1 (1 / 200) (by norm_num)
  have hη4 : (0 : ℝ) < η / 4 := by linarith
  have hεη4 : (0 : ℝ) < ε - η / 4 := by linarith
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  have h2ε : (0 : ℝ) < 2 - ε := by linarith
  have hεη : (0 : ℝ) < ε - η := by linarith
  have hev : ∀ᶠ q : ℕ in Filter.atTop, IsPrimePow q →
      ∃ F : SignedFiber ε q, (q : ℝ) ^ ε / (8 * (Venv ε q : ℝ)) ≤ (F.I.card : ℝ) := by
    filter_upwards [hbig, Venv_le_rpow ε (η / 4) hε0 hη4,
      log_mul_rpow_neg_le (η / 4) 1 hη4 (by norm_num),
      rpow_ge_eventually ε hε0 100, rpow_le_div_eventually ε hε1 16 (by norm_num),
      Filter.eventually_ge_atTop 5, const_le_mul_log_eventually 800 1 (by norm_num),
      rpow_neg_mul_eventually_le (η / 2) hη2 4000 1 (by norm_num),
      rpow_neg_mul_eventually_le (ε - η / 4) hεη4 800 1 (by norm_num),
      rpow_ge_eventually (ε - η) hεη 2, rpow_ge_eventually (2 - ε) h2ε 25]
      with q hqbig hqV hqlog hqM hq16 hq5 hqlog800 hqb2 hqb3 hqD2 hq25
    intro hpp
    obtain ⟨pp, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff q).1 hpp
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
      linarith
    have hlogq : Real.log q ≤ (q : ℝ) ^ (η / 4) := by
      have hp4 : (0 : ℝ) < (q : ℝ) ^ (η / 4) := Real.rpow_pos_of_pos hqpos _
      rwa [div_le_one hp4] at hqlog
    have hL : Large ε η q pp :=
      { prime := hp
        isPow := ⟨k, hk, hpk.symm⟩
        five_le := hq5
        M100 := hqM
        q16 := hq16
        Vle := hqV
        logle := hlogq
        log800 := by linarith
        bad2 := hqb2
        bad3 := hqb3
        D2 := hqD2
        q25 := hq25
        bigP := by
          intro A B hA hB
          have h := hqbig A B hA hB
          rw [Dq]
          linarith }
    exact ⟨hL.fiber, hL.Iq_card_ge hε0 hη0⟩
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨Q₀, fun q hq hQ => hQ₀ q hQ hq⟩

end Erdos289
