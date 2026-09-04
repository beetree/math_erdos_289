import Erdos289.Defs
import Erdos289.External
import Erdos289.ErdosTuran

open Finset Filter Topology

namespace Erdos289
namespace EquidistD

set_option maxHeartbeats 1000000

/-! ## 1. Setup and Definitions -/

/-- Companion inverse value for `t` modulo `U`. Identical to `Erdos289.rOf`. -/
def rOfB (U t : ℕ) : ℕ := ((t : ZMod U)⁻¹).val

/-- Candidate set of `t ∈ (T₁, T₂]` coprime to `U` whose inverse modulo `U` falls in `[α, α+ℓ)`.
Identical to `Erdos289.invCand`. -/
def invCandB (U T₁ T₂ α ℓ : ℕ) : Finset ℕ :=
  (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U ∧ rOfB U t ∈ Finset.Ico α (α + ℓ))

/-! ## 2. Multiples Counting and Division Bounds -/

lemma nat_div_bounds (n d : ℕ) (hd : 0 < d) :
    (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) ∧ ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨?_, Nat.cast_div_le⟩
  have heq := Nat.div_add_mod n d
  have hmod := Nat.mod_lt n hd
  have h1 : n < d * (n / d) + d := by omega
  have h2 : (n : ℝ) < (((d * (n / d) + d : ℕ)) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  have h3 : (n : ℝ) / d < (n / d : ℕ) + 1 := by
    rw [div_lt_iff₀ hdR]
    linarith
  linarith

lemma div_sub_div_bound (T₁ T₂ d : ℕ) (hd : 0 < d) (hT : T₁ ≤ T₂) :
    |(((T₂ / d - T₁ / d : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (d : ℝ))| ≤ 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hTsub : ((T₂ - T₁ : ℕ) : ℝ) = (T₂ : ℝ) - (T₁ : ℝ) := Nat.cast_sub hT
  have hdivsub : ((T₂ / d - T₁ / d : ℕ) : ℝ) = (T₂ / d : ℕ) - (T₁ / d : ℕ) := by
    have : T₁ / d ≤ T₂ / d := Nat.div_le_div_right hT
    exact Nat.cast_sub this
  rw [hTsub, hdivsub, sub_div]
  obtain ⟨h2lt, h2le⟩ := nat_div_bounds T₂ d hd
  obtain ⟨h1lt, h1le⟩ := nat_div_bounds T₁ d hd
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem card_filter_dvd_Ioc_zero (T d : ℕ) :
    ((Ioc 0 T).filter (d ∣ ·)).card = T / d := by
  have h := Nat.card_multiples T d
  rw [← h]
  apply Finset.card_bij (fun a _ => a - 1)
  · intro a ha
    rw [mem_filter, mem_Ioc] at ha
    rw [mem_filter, mem_range]
    have : a - 1 + 1 = a := by omega
    refine ⟨by omega, ?_⟩
    rw [this]; exact ha.2
  · intro a1 ha1 a2 ha2 heq
    rw [mem_filter, mem_Ioc] at ha1 ha2
    omega
  · intro b hb
    rw [mem_filter, mem_range] at hb
    refine ⟨b + 1, ?_, by omega⟩
    rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hb.2⟩

theorem card_filter_dvd_Ioc (T₁ T₂ d : ℕ) (hT : T₁ ≤ T₂) :
    ((Ioc T₁ T₂).filter (d ∣ ·)).card = T₂ / d - T₁ / d := by
  have hdisj0 : Disjoint (Ioc 0 T₁) (Ioc T₁ T₂) := by
    rw [Ioc_disjoint_Ioc]
    omega
  have hdisj := Disjoint.mono (Finset.filter_subset (d ∣ ·) (Ioc 0 T₁)) (Finset.filter_subset (d ∣ ·) (Ioc T₁ T₂)) hdisj0
  have hunion : (Ioc 0 T₁).filter (d ∣ ·) ∪ (Ioc T₁ T₂).filter (d ∣ ·) = (Ioc 0 T₂).filter (d ∣ ·) := by
    rw [← Finset.filter_union, Ioc_union_Ioc_eq_Ioc (by omega) hT]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, card_filter_dvd_Ioc_zero, card_filter_dvd_Ioc_zero] at hcard
  omega

/-! ## 3. Inclusion–Exclusion on Intervals (Lemma iii) -/

lemma card_filter_not {α : Type*} [DecidableEq α] (s : Finset α)
    (A : α → Prop) [DecidablePred A] :
    ((s.filter (fun x => ¬ A x)).card : ℝ) = (s.card : ℝ) - ((s.filter A).card : ℝ) := by
  have heq : s.filter (fun x => ¬ A x) = s \ s.filter A := by
    ext x
    simp only [mem_filter, Finset.mem_sdiff]
    tauto
  have hsub : s.filter A ⊆ s := filter_subset _ _
  have hcard : (s \ s.filter A).card = s.card - (s.filter A).card := card_sdiff_of_subset hsub
  have hle : (s.filter A).card ≤ s.card := card_le_card hsub
  rw [heq, hcard]
  exact Nat.cast_sub hle

lemma card_filter_not_and_not {α : Type*} [DecidableEq α] (s : Finset α)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B] :
    ((s.filter (fun x => ¬ A x ∧ ¬ B x)).card : ℝ) =
      (s.card : ℝ) - ((s.filter A).card : ℝ) - ((s.filter B).card : ℝ)
        + ((s.filter (fun x => A x ∧ B x)).card : ℝ) := by
  have heq : s.filter (fun x => ¬ A x ∧ ¬ B x) = s \ (s.filter A ∪ s.filter B) := by
    ext x
    simp only [mem_filter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hsub : s.filter A ∪ s.filter B ⊆ s := by
    intro x hx
    simp only [Finset.mem_union, mem_filter] at hx
    rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
  have hcard1 : (s \ (s.filter A ∪ s.filter B)).card = s.card - (s.filter A ∪ s.filter B).card :=
    card_sdiff_of_subset hsub
  have hcard2 : (s.filter A ∪ s.filter B).card + (s.filter A ∩ s.filter B).card =
      (s.filter A).card + (s.filter B).card := card_union_add_card_inter _ _
  have hinter : s.filter A ∩ s.filter B = s.filter (fun x => A x ∧ B x) := by
    ext x
    simp only [mem_inter, mem_filter]
    tauto
  rw [hinter] at hcard2
  have hle : (s.filter A ∪ s.filter B).card ≤ s.card := card_le_card hsub
  rw [heq, hcard1]
  have hcard1R : ((s.card - (s.filter A ∪ s.filter B).card : ℕ) : ℝ) =
      (s.card : ℝ) - ((s.filter A ∪ s.filter B).card : ℝ) := Nat.cast_sub hle
  have hcard2R : (((s.filter A ∪ s.filter B).card : ℝ) + ((s.filter (fun x => A x ∧ B x)).card : ℝ))
      = ((s.filter A).card : ℝ) + ((s.filter B).card : ℝ) := by
    exact_mod_cast hcard2
  linarith

lemma coprime_pow_prime {p : ℕ} (hp : p.Prime) (t k : ℕ) (hk : 0 < k) :
    Nat.Coprime t (p ^ k) ↔ ¬ p ∣ t := by
  constructor
  · intro h hdvd
    have h1 : p ∣ p ^ k := dvd_pow_self p hk.ne'
    have h2 : p ∣ Nat.gcd t (p ^ k) := Nat.dvd_gcd hdvd h1
    rw [h.gcd_eq_one] at h2
    have := Nat.le_of_dvd (by omega) h2
    have := hp.two_le
    omega
  · intro h
    exact hp.coprime_pow_of_not_dvd h

lemma coprime_mul_prime_pows {p : ℕ} (hp : p.Prime) (t k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Nat.Coprime t (2 ^ k * p ^ m) ↔ ¬ 2 ∣ t ∧ ¬ p ∣ t := by
  rw [Nat.coprime_mul_iff_right, coprime_pow_prime Nat.prime_two t k hk, coprime_pow_prime hp t m hm]

theorem totient_two_pow (k : ℕ) (hk : 0 < k) :
    ((Nat.totient (2 ^ k) : ℝ)) / (2 ^ k : ℝ) = 1 / 2 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hφeq : (2 ^ (k' + 1)).totient = 2 ^ k' := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two k']; norm_num
  rw [hφeq, pow_succ]
  have h2n : (2:ℝ)^k' ≠ 0 := by positivity
  push_cast
  field_simp

theorem totient_odd_prime_pow (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    ((Nat.totient (p ^ a) : ℝ)) / (p ^ a : ℝ) = 1 - 1 / (p : ℝ) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hφeq : (p ^ (a' + 1)).totient = p ^ a' * (p - 1) :=
    Nat.totient_prime_pow_succ hp a'
  rw [hφeq, pow_succ]
  have h1 : 1 ≤ p := hp.one_lt.le
  have hpa : (p:ℝ)^a' ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    positivity
  have hpR : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    positivity
  push_cast
  rw [Nat.cast_sub h1]
  push_cast
  field_simp

theorem totient_two_pow_mul_odd_prime_pow (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) (hm : 0 < m) :
    ((Nat.totient (2 ^ k * p ^ m) : ℝ)) / (2 ^ k * p ^ m : ℝ) = (1 / 2) * (1 - 1 / (p : ℝ)) := by
  have hcop2p : Nat.Coprime 2 p := by
    apply Nat.prime_two.coprime_iff_not_dvd.2
    intro h2p
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p
    exact hp2 this.symm
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) := Nat.Coprime.pow k m hcop2p
  rw [Nat.totient_mul hcop]
  push_cast
  have h1 : ((Nat.totient (2 ^ k) : ℝ) * (Nat.totient (p ^ m) : ℝ)) / ((2 : ℝ) ^ k * (p : ℝ) ^ m)
      = ((Nat.totient (2 ^ k) : ℝ) / (2 : ℝ) ^ k) * ((Nat.totient (p ^ m) : ℝ) / (p : ℝ) ^ m) := by
    ring
  rw [h1, totient_two_pow k hk, totient_odd_prime_pow p m hp hm]

lemma coprime_count_two (T₁ T₂ k : ℕ) (hk : 0 < k) (hT : T₁ ≤ T₂) :
    |(((Ioc T₁ T₂).filter (fun t => Nat.Coprime t (2 ^ k))).card : ℝ) -
      (Nat.totient (2 ^ k) : ℝ) / (2 ^ k : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 1 := by
  have hcongr : (Ioc T₁ T₂).filter (fun t => Nat.Coprime t (2 ^ k)) =
      (Ioc T₁ T₂).filter (fun t => ¬ 2 ∣ t) := by
    apply Finset.filter_congr
    intro t _
    exact coprime_pow_prime Nat.prime_two t k hk
  rw [hcongr, card_filter_not, Nat.card_Ioc, card_filter_dvd_Ioc T₁ T₂ 2 hT, totient_two_pow k hk]
  have hdiv := div_sub_div_bound T₁ T₂ 2 (by omega) hT
  have : ((T₂ - T₁ : ℕ) : ℝ) - (T₂ / 2 - T₁ / 2 : ℕ) - (1 / 2) * ((T₂ - T₁ : ℕ) : ℝ)
      = - (((T₂ / 2 - T₁ / 2 : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / 2) := by ring
  rw [this, abs_neg]
  exact hdiv

lemma coprime_count_odd_prime (T₁ T₂ p a : ℕ) (hp : p.Prime) (ha : 0 < a) (hT : T₁ ≤ T₂) :
    |(((Ioc T₁ T₂).filter (fun t => Nat.Coprime t (p ^ a))).card : ℝ) -
      (Nat.totient (p ^ a) : ℝ) / (p ^ a : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 1 := by
  have hcongr : (Ioc T₁ T₂).filter (fun t => Nat.Coprime t (p ^ a)) =
      (Ioc T₁ T₂).filter (fun t => ¬ p ∣ t) := by
    apply Finset.filter_congr
    intro t _
    exact coprime_pow_prime hp t a ha
  rw [hcongr, card_filter_not, Nat.card_Ioc, card_filter_dvd_Ioc T₁ T₂ p hT, totient_odd_prime_pow p a hp ha]
  have hdiv := div_sub_div_bound T₁ T₂ p hp.pos hT
  have : ((T₂ - T₁ : ℕ) : ℝ) - (T₂ / p - T₁ / p : ℕ) - (1 - 1 / (p : ℝ)) * ((T₂ - T₁ : ℕ) : ℝ)
      = - (((T₂ / p - T₁ / p : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (p : ℝ)) := by ring
  rw [this, abs_neg]
  exact hdiv

lemma test_tri (E1 E2 E3 : ℝ) (h1 : |E1| ≤ 1) (h2 : |E2| ≤ 1) (h3 : |E3| ≤ 1) :
    |-E1 - E2 + E3| ≤ 3 := by
  have heq : -E1 - E2 + E3 = (-E1 + -E2) + E3 := by ring
  rw [heq]
  have ha1 := abs_add_le (-E1 + -E2) E3
  have ha2 := abs_add_le (-E1) (-E2)
  rw [abs_neg E1] at ha2
  rw [abs_neg E2] at ha2
  linarith

lemma coprime_count_two_mul_odd_prime (T₁ T₂ p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 0 < k) (hm : 0 < m) (hT : T₁ ≤ T₂) :
    |(((Ioc T₁ T₂).filter (fun t => Nat.Coprime t (2 ^ k * p ^ m))).card : ℝ) -
      (Nat.totient (2 ^ k * p ^ m) : ℝ) / (2 ^ k * p ^ m : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 3 := by
  have hcongr : (Ioc T₁ T₂).filter (fun t => Nat.Coprime t (2 ^ k * p ^ m)) =
      (Ioc T₁ T₂).filter (fun t => ¬ 2 ∣ t ∧ ¬ p ∣ t) := by
    apply Finset.filter_congr
    intro t _
    exact coprime_mul_prime_pows hp t k m hk hm
  have hcop2p : Nat.Coprime 2 p := by
    apply Nat.prime_two.coprime_iff_not_dvd.2
    intro h2p
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p
    exact hp2 this.symm
  have hdvd2p : ∀ t, 2 ∣ t ∧ p ∣ t ↔ 2 * p ∣ t := fun t =>
    ⟨fun ⟨h2, hp⟩ => hcop2p.mul_dvd_of_dvd_of_dvd h2 hp,
     fun h => ⟨(dvd_mul_right 2 p).trans h, (dvd_mul_left p 2).trans h⟩⟩
  have hinter : (Ioc T₁ T₂).filter (fun t => 2 ∣ t ∧ p ∣ t) =
      (Ioc T₁ T₂).filter (2 * p ∣ ·) := by
    apply Finset.filter_congr
    intro t _
    exact hdvd2p t
  have h2ppos : 0 < 2 * p := mul_pos (by omega) hp.pos
  rw [hcongr, card_filter_not_and_not, hinter, Nat.card_Ioc,
      card_filter_dvd_Ioc T₁ T₂ 2 hT, card_filter_dvd_Ioc T₁ T₂ p hT,
      card_filter_dvd_Ioc T₁ T₂ (2 * p) hT,
      totient_two_pow_mul_odd_prime_pow p k m hp hp2 hk hm]
  have hd1 := div_sub_div_bound T₁ T₂ 2 (by omega) hT
  have hd2 := div_sub_div_bound T₁ T₂ p hp.pos hT
  have hd3 := div_sub_div_bound T₁ T₂ (2 * p) h2ppos hT
  push_cast at hd3
  set E1 := (((T₂ / 2 - T₁ / 2 : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / 2)
  set E2 := (((T₂ / p - T₁ / p : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (p : ℝ))
  set E3 := (((T₂ / (2 * p) - T₁ / (2 * p) : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (2 * (p : ℝ)))
  have hring : ((T₂ - T₁ : ℕ) : ℝ) - (T₂ / 2 - T₁ / 2 : ℕ) - (T₂ / p - T₁ / p : ℕ)
      + (T₂ / (2 * p) - T₁ / (2 * p) : ℕ) - (1 / 2) * (1 - 1 / (p : ℝ)) * ((T₂ - T₁ : ℕ) : ℝ)
      = - E1 - E2 + E3 := by
    dsimp [E1, E2, E3]
    ring
  rw [hring]
  exact test_tri E1 E2 E3 hd1 hd2 hd3

/-- **Lemma (iii)**: The count of `t ∈ (T₁, T₂]` coprime to `U` is within an absolute constant `4`
of `φ(U)/U · (T₂ - T₁)` for all moduli `U ∈ {q, 2q, 4q, 4pq}`. -/
theorem coprime_count_le_four (q p a U T₁ T₂ : ℕ) (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a)
    (hU : U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q) (hT : T₁ ≤ T₂) :
    |(((Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)).card : ℝ) -
      (Nat.totient U : ℝ) / (U : ℝ) * ((T₂ - T₁ : ℕ) : ℝ)| ≤ 4 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · -- p = 2
    have hq2 : q = 2 ^ a := hq
    rcases hU with hU | hU | hU | hU
    · rw [hU, hq2]
      have := coprime_count_two T₁ T₂ a ha hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq2, show 2 * 2 ^ a = 2 ^ (a + 1) by ring]
      have := coprime_count_two T₁ T₂ (a + 1) (by omega) hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq2, show 4 * 2 ^ a = 2 ^ (a + 2) by ring]
      have := coprime_count_two T₁ T₂ (a + 2) (by omega) hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq2, show 4 * 2 * 2 ^ a = 2 ^ (a + 3) by ring]
      have := coprime_count_two T₁ T₂ (a + 3) (by omega) hT
      push_cast at this ⊢
      linarith
  · -- p ≠ 2
    rcases hU with hU | hU | hU | hU
    · rw [hU, hq]
      have := coprime_count_odd_prime T₁ T₂ p a hp ha hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq, show 2 * p ^ a = 2 ^ 1 * p ^ a by ring]
      have := coprime_count_two_mul_odd_prime T₁ T₂ p 1 a hp hp2 (by omega) ha hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq, show 4 * p ^ a = 2 ^ 2 * p ^ a by ring]
      have := coprime_count_two_mul_odd_prime T₁ T₂ p 2 a hp hp2 (by omega) ha hT
      push_cast at this ⊢
      linarith
    · rw [hU, hq, show 4 * p * p ^ a = 2 ^ 2 * p ^ (a + 1) by ring]
      have := coprime_count_two_mul_odd_prime T₁ T₂ p 2 (a + 1) hp hp2 (by omega) (by omega) hT
      push_cast at this ⊢
      linarith

/-! ## 4. Exponential Character and Modular Inversion Reductions (Lemmas i & ii) -/

lemma norm_e_eq_one (m : ℕ) (x : ℤ) : ‖e m x‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  have : (2 * ↑Real.pi * Complex.I * (x : ℂ) / (m : ℂ)) =
      (((2 * Real.pi * (x : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
             Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Real.exp_zero]

lemma e_periodic (m : ℕ) (x y : ℤ) (hm : 0 < m) (hmod : x ≡ y [ZMOD m]) :
    e m x = e m y := by
  have hdvd : (m : ℤ) ∣ x - y := hmod.symm.dvd
  obtain ⟨k, hk⟩ := hdvd
  have hdiff : x = y + (m : ℤ) * k := by omega
  unfold e
  have hmR : (m : ℂ) ≠ 0 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    exact_mod_cast this
  have hsplit : (2 * ↑Real.pi * Complex.I * (x : ℂ) / (m : ℂ)) =
      (2 * ↑Real.pi * Complex.I * (y : ℂ) / (m : ℂ)) + (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [hdiff]
    push_cast
    field_simp [hmR]
  rw [hsplit, Complex.exp_add]
  have hper : Complex.exp ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I k
  rw [hper, mul_one]

lemma e_div_gcd (U h : ℕ) (x : ℤ) (hh : 0 < h) :
    let g := Nat.gcd h U
    let U' := U / g
    let h' := h / g
    e U (h * x) = e U' (h' * x) := by
  intro g U' h'
  have hg : 0 < g := Nat.gcd_pos_of_pos_left U hh
  have hgR : (g : ℂ) ≠ 0 := by
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    exact_mod_cast this
  have hU : U = g * U' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right h U)).symm
  have hh_eq : h = g * h' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left h U)).symm
  unfold e
  have hnum : (2 * ↑Real.pi * Complex.I * (↑(↑h * x) : ℂ)) =
      (g : ℂ) * (2 * ↑Real.pi * Complex.I * (↑(↑h' * x) : ℂ)) := by
    push_cast [hh_eq]
    ring
  have hden : (U : ℂ) = (g : ℂ) * (U' : ℂ) := by
    push_cast [hU]
    ring
  rw [hnum, hden, mul_div_mul_left _ _ hgR]

lemma rOfB_modeq (U U' t : ℕ) (hdvd : U' ∣ U) (hcop : Nat.Coprime t U) :
    rOfB U t ≡ rOfB U' t [MOD U'] := by
  have hcop' : Nat.Coprime t U' := hcop.coprime_dvd_right hdvd
  have hvalU : ((rOfB U t * t : ℕ) : ZMod U) = ((1 : ℕ) : ZMod U) := by
    push_cast [rOfB]; exact ZMod.val_inv_mul hcop
  have hmodU : rOfB U t * t ≡ 1 [MOD U] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hvalU
  have hmodU' : rOfB U t * t ≡ 1 [MOD U'] := hmodU.of_dvd hdvd
  have hvalU' : ((rOfB U' t * t : ℕ) : ZMod U') = ((1 : ℕ) : ZMod U') := by
    push_cast [rOfB]; exact ZMod.val_inv_mul hcop'
  have hmodU'' : rOfB U' t * t ≡ 1 [MOD U'] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hvalU'
  have htrans : rOfB U t * t ≡ rOfB U' t * t [MOD U'] := hmodU'.trans hmodU''.symm
  exact Nat.ModEq.cancel_right_of_coprime hcop'.symm htrans

lemma e_rOfB_reduce (U h : ℕ) (t : ℕ) (hh : 0 < h) (hcop : Nat.Coprime t U) :
    let g := Nat.gcd h U
    let U' := U / g
    let h' := h / g
    1 < U' →
    e U (h * (rOfB U t : ℤ)) = e U' (h' * (rOfB U' t : ℤ)) := by
  intro g U' h' hU'
  have h1 : e U (h * (rOfB U t : ℤ)) = e U' (h' * (rOfB U t : ℤ)) := e_div_gcd U h (rOfB U t : ℤ) hh
  rw [h1]
  have hdvd : U' ∣ U := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right h U)
  have hmod := rOfB_modeq U U' t hdvd hcop
  have hmodZ : (h' * (rOfB U t : ℤ)) ≡ (h' * (rOfB U' t : ℤ)) [ZMOD U'] := by
    have : (rOfB U t : ℤ) ≡ (rOfB U' t : ℤ) [ZMOD U'] := by exact_mod_cast hmod
    exact Int.ModEq.mul_left (h' : ℤ) this
  exact e_periodic U' (h' * (rOfB U t : ℤ)) (h' * (rOfB U' t : ℤ)) (by omega) hmodZ

/-! ## 5. Prefix-Difference Bounds from Bourgain–Garaev (Lemma iv) -/

lemma trivial_exp_sum_bound (m N : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℤ) :
    ‖∑ n ∈ (Icc 1 N).filter P, e m (f n)‖ ≤ (N : ℝ) := by
  have h1 : ‖∑ n ∈ (Icc 1 N).filter P, e m (f n)‖ ≤ ∑ n ∈ (Icc 1 N).filter P, ‖e m (f n)‖ :=
    norm_sum_le _ _
  have h2 : ∑ n ∈ (Icc 1 N).filter P, ‖e m (f n)‖ = (((Icc 1 N).filter P).card : ℝ) := by
    simp only [norm_e_eq_one, sum_const, nsmul_eq_mul, mul_one]
  have h3 : ((Icc 1 N).filter P).card ≤ N := by
    have hle : ((Icc 1 N).filter P).card ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
    rw [Nat.card_Icc] at hle
    omega
  have h3R : (((Icc 1 N).filter P).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast h3
  linarith

lemma bg_prefix_bound (c : ℝ) (hc0 : 0 < c) (hcc0 : c < Classical.choose bourgain_garaev)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, (N : ℝ) < (m : ℝ) →
      ∀ a : ℕ, Nat.Coprime a m →
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
            e m (a * ((n : ZMod m)⁻¹).val)‖ ≤ (m : ℝ) ^ c + ε * (N : ℝ) := by
  have hbg := (Classical.choose_spec bourgain_garaev).2 c hc0 hcc0 ε hε
  filter_upwards [hbg] with m hm N hNm a ha
  rcases le_or_gt (N : ℝ) ((m : ℝ) ^ c) with hle | hgt
  · have htriv := trivial_exp_sum_bound m N (fun n => Nat.Coprime n m)
        (fun n => (a : ℤ) * ((n : ZMod m)⁻¹).val)
    have : 0 ≤ ε * (N : ℝ) := by positivity
    linarith
  · have hbound := hm N hgt hNm a ha
    have hmpos : 0 ≤ (m : ℝ) ^ c := by positivity
    linarith

lemma sum_Ioc_eq_sub_Icc {M : Type*} [AddCommGroup M] (T₁ T₂ : ℕ) (hT : T₁ ≤ T₂)
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → M) :
    ∑ n ∈ (Ioc T₁ T₂).filter P, f n =
      (∑ n ∈ (Icc 1 T₂).filter P, f n) - (∑ n ∈ (Icc 1 T₁).filter P, f n) := by
  have hdisj : Disjoint ((Icc 1 T₁).filter P) ((Ioc T₁ T₂).filter P) := by
    apply Disjoint.mono (filter_subset _ _) (filter_subset _ _)
    rw [disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [mem_Icc] at hx
    simp only [mem_Ioc] at hy
    omega
  have hunion : (Icc 1 T₁).filter P ∪ (Ioc T₁ T₂).filter P = (Icc 1 T₂).filter P := by
    rw [← filter_union]
    congr 1
    ext x
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  rw [← hunion, sum_union hdisj]
  abel

/-- **Lemma (iv)**: Prefix-difference bound from `bourgain_garaev` for an interval `(T₁, T₂]`. -/
lemma bg_interval_bound (c : ℝ) (hc0 : 0 < c) (hcc0 : c < Classical.choose bourgain_garaev)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) < (m : ℝ) →
      ∀ a : ℕ, Nat.Coprime a m →
        ‖∑ n ∈ (Finset.Ioc T₁ T₂).filter (fun n => Nat.Coprime n m),
            e m (a * ((n : ZMod m)⁻¹).val)‖ ≤ 2 * (m : ℝ) ^ c + 2 * ε * (T₂ : ℝ) := by
  filter_upwards [bg_prefix_bound c hc0 hcc0 ε hε] with m hm T₁ T₂ hT hT₂ a ha
  have hT₁m : (T₁ : ℝ) < (m : ℝ) := by
    have : (T₁ : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast hT
    linarith
  rw [sum_Ioc_eq_sub_Icc T₁ T₂ hT]
  have h1 := hm T₂ hT₂ a ha
  have h2 := hm T₁ hT₁m a ha
  have htri := norm_sub_le (∑ n ∈ (Icc 1 T₂).filter (fun n => Nat.Coprime n m), e m (a * ((n : ZMod m)⁻¹).val))
                           (∑ n ∈ (Icc 1 T₁).filter (fun n => Nat.Coprime n m), e m (a * ((n : ZMod m)⁻¹).val))
  have hT₁T₂ : (T₁ : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast hT
  have : ε * (T₁ : ℝ) ≤ ε * (T₂ : ℝ) := by nlinarith
  linarith

/-! ## 6. Exponential Sum Bound (reduction from Bourgain–Garaev) -/

theorem rpow_ge_eventually (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ q : ℕ in atTop, c ≤ (q:ℝ)^ε := by
  have h := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **Exponential sum bound** (Bourgain–Garaev reduction, paper §2, lines 135–148):
For fixed Fourier frequency `h ≥ 1` and tolerance `δ > 0`, the short inverse sum
`∑_{t ∈ (T₁, T₂], (t, U)=1} e_U(h · t⁻¹)` is bounded by `δ · q^ε` for all sufficiently large `q`.

The reduction uses:
1. `e_rOfB_reduce`: reduces `e_U(h · t⁻¹)` to `e_{U'}(h' · t⁻¹)` where `U' = U / gcd(h, U)`
   and `h' = h / gcd(h, U)` is coprime to `U'`.
2. For large `q`, `U' ≥ q / h → ∞`, so `bourgain_garaev` / `bg_interval_bound` applies at modulus `U'`.
3. For `T ≤ (U')^c`, `trivial_exp_sum_bound` bounds the sum by `(U')^c ≤ (4q²)^c = o(q^ε)`.
4. In the odd case where `2 ∤ U'`, the condition `(t, U) = 1` is `t odd ∧ p ∤ t`, which splits
   into `p ∤ t` minus even terms `t = 2u` with `p ∤ u`; substituting `t = 2u` gives phase
   `e_{U'}((h' · 2⁻¹) u⁻¹)` with unit coefficient `h' · 2⁻¹ mod U'`, which is again bounded
   by `bg_interval_bound`. -/
theorem exp_sum_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (h : ℕ) (hh : 0 < h) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
      ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
        ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
          ‖∑ t ∈ (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U),
              e U (h * (rOfB U t : ℤ))‖ ≤ δ * (q : ℝ) ^ ε := by
  sorry

/-! ## 7. Erdős–Turán Application and Master Theorem (Lemma vi) -/

lemma invCandB_card_eq (U T₁ T₂ α ℓ : ℕ) :
    let S := (Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)
    let N := S.card
    let x : Fin N → ZMod U := fun j => ((((S.equivFin.symm j).val : ℕ) : ZMod U)⁻¹)
    (univ.filter (fun j => (x j).val ∈ Ico α (α + ℓ))).card =
      (invCandB U T₁ T₂ α ℓ).card := by
  intro S N x
  have hbij : (univ.filter (fun j => (x j).val ∈ Ico α (α + ℓ))).card =
      (S.filter (fun t => rOfB U t ∈ Ico α (α + ℓ))).card := by
    apply Finset.card_bij (fun j _ => (S.equivFin.symm j).val)
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      simp only [mem_filter]
      refine ⟨(S.equivFin.symm j).2, ?_⟩
      exact hj
    · intro j1 hj1 j2 hj2 heq
      have : (S.equivFin.symm j1) = (S.equivFin.symm j2) := Subtype.ext heq
      exact S.equivFin.symm.injective this
    · intro t ht
      simp only [mem_filter] at ht
      obtain ⟨htS, htr⟩ := ht
      refine ⟨S.equivFin ⟨t, htS⟩, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        dsimp [x]
        rw [Equiv.symm_apply_apply]
        exact htr
      · rw [Equiv.symm_apply_apply]
  rw [hbij]
  unfold invCandB
  rw [filter_filter]

lemma exp_sum_eq (U T₁ T₂ h : ℕ) :
    let S := (Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)
    let N := S.card
    let x : Fin N → ZMod U := fun j => ((((S.equivFin.symm j).val : ℕ) : ZMod U)⁻¹)
    ∑ j : Fin N, e U (h * ((x j).val : ℤ)) =
      ∑ t ∈ S, e U (h * (rOfB U t : ℤ)) := by
  intro S N x
  have h1 : ∑ j : Fin N, e U (h * ((x j).val : ℤ)) =
      ∑ s : S, e U (h * (rOfB U s.val : ℤ)) := by
    rw [← S.equivFin.symm.sum_comp]
    apply Fintype.sum_congr
    intro j
    dsimp [x, rOfB]
  rw [h1]
  exact Finset.sum_coe_sort S (fun t => e U (h * (rOfB U t : ℤ)))

/-- **Equidistribution of modular inverses** (paper §2): for a prime power `q = p^a`, a
modulus `U ∈ {q, 2q, 4q, 4pq}`, a prefix length `T ≤ 5 q^ε`, and a residue interval
`[α, α+ℓ) ⊆ [0, U)`, the count of `t ≤ T` coprime to `U` with `t⁻¹ mod U ∈ [α, α+ℓ)` matches
the expected count `φ(U)/U · T · ℓ/U` up to an error `≤ κ · q^ε`. -/
theorem equidist_inverseD (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
      ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
        ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |((invCandB U T₁ T₂ α ℓ).card : ℝ)
                - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)|
              ≤ κ * (q : ℝ) ^ ε := by
  intro κ hκ
  obtain ⟨C, hC0, hET⟩ := erdos_turan
  set H₀ : ℕ := ⌈20 * C / κ⌉₊ + 1 with hH₀def
  have hH₀pos : 0 < H₀ := by omega
  have hH₀R : 20 * C / κ < (H₀ : ℝ) := by
    have h1 : (20 * C / κ : ℝ) ≤ (⌈20 * C / κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (H₀ : ℝ) = (⌈20 * C / κ⌉₊ : ℝ) + 1 := by
      rw [hH₀def]; push_cast; rfl
    linarith
  have hH₀Rpos : 0 < (H₀ : ℝ) := by positivity
  have hC_H₀ : C * 5 / (H₀ : ℝ) < κ / 4 := by
    have h1 : 20 * C < (H₀ : ℝ) * κ := by
      rwa [div_lt_iff₀ hκ] at hH₀R
    have h2 : (C * 5) / (H₀ : ℝ) * 4 < κ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hH₀Rpos]
      linarith
    linarith
  set M_H₀ : ℝ := ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) with hM_H₀def
  have hM_H₀pos : 0 < M_H₀ := by
    apply Finset.sum_pos'
    · intro i hi; simp only [mem_Icc] at hi; positivity
    · refine ⟨1, ?_, by positivity⟩
      simp only [mem_Icc]
      omega
  set δ : ℝ := κ / (4 * C * M_H₀) with hδdef
  have hδpos : 0 < δ := by positivity
  have h4_ev : ∀ᶠ q : ℕ in atTop, 4 ≤ (κ / 4) * (q : ℝ) ^ ε := by
    filter_upwards [rpow_ge_eventually ε hε0 (16 / κ)] with q hq
    have hpos4 : 0 ≤ κ / 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hq hpos4
    have h16 : (κ / 4) * (16 / κ) = 4 := by
      have : κ ≠ 0 := hκ.ne'
      field_simp
      ring
    linarith
  have hall_h : ∀ᶠ q : ℕ in atTop, ∀ h ∈ Icc 1 H₀,
      ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
        ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
          ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
            ‖∑ t ∈ (Finset.Ioc T₁ T₂).filter (fun t => Nat.Coprime t U),
                e U (h * (rOfB U t : ℤ))‖ ≤ δ * (q : ℝ) ^ ε := by
    rw [Finset.eventually_all]
    intro h hh
    simp only [mem_Icc] at hh
    exact exp_sum_bound ε hε0 hε1 h (by omega) δ hδpos
  filter_upwards [hall_h, h4_ev, eventually_ge_atTop 1] with q hqh h4q hq1
  intro p a hp ha hq U hU T₁ T₂ hT hT₂ α ℓ hαℓ
  set S := (Ioc T₁ T₂).filter (fun t => Nat.Coprime t U) with hSdef
  set N := S.card with hNdef
  have hqpos : 0 < q := by rw [hq]; exact pow_pos hp.pos a
  have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hppos : 0 < p := hp.pos
  have hUpos : 0 < U := by
    rcases hU with rfl | rfl | rfl | rfl
    · exact hqpos
    · exact mul_pos (by omega) hqpos
    · exact mul_pos (by omega) hqpos
    · exact mul_pos (mul_pos (by omega) hppos) hqpos
  have hURpos : 0 < (U : ℝ) := by exact_mod_cast hUpos
  have hℓleU : ℓ ≤ U := by omega
  have hℓUR : (ℓ : ℝ) / (U : ℝ) ≤ 1 := by
    rw [div_le_one₀ hURpos]
    exact_mod_cast hℓleU
  have hℓUR_nonneg : 0 ≤ (ℓ : ℝ) / (U : ℝ) := by positivity
  have hNleT₂ : (N : ℝ) ≤ 5 * (q : ℝ) ^ ε := by
    have h1 : N ≤ T₂ - T₁ := by
      rw [hNdef, hSdef]
      have : ((Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)).card ≤ (Ioc T₁ T₂).card :=
        card_le_card (filter_subset _ _)
      rw [Nat.card_Ioc] at this
      exact this
    have h2 : T₂ - T₁ ≤ T₂ := by omega
    have : (N : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast (h1.trans h2)
    linarith [hT₂]
  -- Erdős-Turán bound
  set x : Fin N → ZMod U := fun j => ((((S.equivFin.symm j).val : ℕ) : ZMod U)⁻¹) with hxdef
  have hET_app := hET U hUpos N x H₀ hH₀pos α ℓ hαℓ
  rw [invCandB_card_eq U T₁ T₂ α ℓ] at hET_app
  have heval_sum : ∀ h ∈ Icc 1 H₀, ‖∑ j : Fin N, e U (h * ((x j).val : ℤ))‖ ≤ δ * (q : ℝ) ^ ε := by
    intro h hh
    rw [exp_sum_eq U T₁ T₂ h]
    exact hqh h hh p a hp ha hq U hU T₁ T₂ hT hT₂
  have hsum_bound : ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖
      ≤ M_H₀ * (δ * (q : ℝ) ^ ε) := by
    have : ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖
        ≤ ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * (δ * (q : ℝ) ^ ε) := by
      apply Finset.sum_le_sum
      intro h hh
      have h1pos : 0 ≤ (1 : ℝ) / (h : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (heval_sum h hh) h1pos
    rw [← Finset.sum_mul] at this
    exact this
  have hET_RHS : C * ((N : ℝ) / (H₀ : ℝ) + ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖)
      ≤ (κ / 2) * (q : ℝ) ^ ε := by
    have hpart1 : C * ((N : ℝ) / (H₀ : ℝ)) ≤ (κ / 4) * (q : ℝ) ^ ε := by
      have h1 : C * ((N : ℝ) / (H₀ : ℝ)) = (C / (H₀ : ℝ)) * (N : ℝ) := by ring
      have h2 : (C / (H₀ : ℝ)) * (N : ℝ) ≤ (C / (H₀ : ℝ)) * (5 * (q : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hNleT₂ (by positivity)
      have h3 : (C / (H₀ : ℝ)) * (5 * (q : ℝ) ^ ε) = (C * 5 / (H₀ : ℝ)) * (q : ℝ) ^ ε := by ring
      have h4 : (C * 5 / (H₀ : ℝ)) * (q : ℝ) ^ ε ≤ (κ / 4) * (q : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hC_H₀.le (by positivity)
      linarith
    have hpart2 : C * (∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖)
        ≤ (κ / 4) * (q : ℝ) ^ ε := by
      have h1 : C * (∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖)
          ≤ C * (M_H₀ * (δ * (q : ℝ) ^ ε)) :=
        mul_le_mul_of_nonneg_left hsum_bound hC0.le
      have h2 : C * (M_H₀ * (δ * (q : ℝ) ^ ε)) = (κ / 4) * (q : ℝ) ^ ε := by
        dsimp [δ]
        field_simp
        try ring
      linarith
    calc C * ((N : ℝ) / (H₀ : ℝ) + ∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖)
        = C * ((N : ℝ) / (H₀ : ℝ)) + C * (∑ h ∈ Icc 1 H₀, (1 : ℝ) / (h : ℝ) * ‖∑ j, e U (h * ((x j).val : ℤ))‖) := by ring
      _ ≤ (κ / 4) * (q : ℝ) ^ ε + (κ / 4) * (q : ℝ) ^ ε := by linarith
      _ = (κ / 2) * (q : ℝ) ^ ε := by ring
  have hET_final : |((invCandB U T₁ T₂ α ℓ).card : ℝ) - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
      ≤ (κ / 2) * (q : ℝ) ^ ε :=
    hET_app.trans hET_RHS
  -- Coprime count error
  have hcop_diff := coprime_count_le_four q p a U T₁ T₂ hp ha hq hU hT
  have hcop_diff_scaled : |(N : ℝ) * (ℓ : ℝ) / (U : ℝ)
      - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)|
      ≤ (κ / 4) * (q : ℝ) ^ ε := by
    have heq_factor : (N : ℝ) * (ℓ : ℝ) / (U : ℝ)
        - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)
        = ((N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ))) * ((ℓ : ℝ) / (U : ℝ)) := by
      ring
    rw [heq_factor, abs_mul]
    have h1 : |((N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)))| ≤ 4 := by
      rw [show (N : ℝ) = (((Ioc T₁ T₂).filter (fun t => Nat.Coprime t U)).card : ℝ) from rfl]
      exact hcop_diff
    have h2 : |(ℓ : ℝ) / (U : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hℓUR_nonneg]
      exact hℓUR
    have hmul : |(N : ℝ) - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ))| * |(ℓ : ℝ) / (U : ℝ)| ≤ 4 * 1 :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith [hmul, h4q]
  have htri := abs_sub_le ((invCandB U T₁ T₂ α ℓ).card : ℝ) ((N : ℝ) * (ℓ : ℝ) / (U : ℝ))
      ((Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ))
  linarith

end EquidistD
end Erdos289
