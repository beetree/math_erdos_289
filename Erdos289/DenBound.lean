import Erdos289.Defs

/-!
# Denominator bookkeeping

`DenBound B r` says every prime-power divisor of the reduced denominator of `r` is
at most `B`. This file collects the basic algebraic bookkeeping needed to track
denominator bounds through sums, negation, division, and casts, plus a couple of
prime-power-specific refinements used to bound denominators of harmonic-type sums
by `lcm(1, ..., L)`.
-/

namespace Erdos289

open Finset

/-- Every prime-power divisor of the reduced denominator of `r` is at most `B`. -/
def DenBound (B : ℕ) (r : ℚ) : Prop :=
  ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ r.den → p ^ e ≤ B

namespace DenBound

lemma mono {B B' : ℕ} {r : ℚ} (hBB' : B ≤ B') (h : DenBound B r) : DenBound B' r :=
  fun p e hp he hpe => (h p e hp he hpe).trans hBB'

lemma of_den_dvd {B D : ℕ} {r : ℚ} (hdvd : r.den ∣ D)
    (hB : ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ D → p ^ e ≤ B) : DenBound B r :=
  fun p e hp he hpe => hB p e hp he (hpe.trans hdvd)

lemma of_den_le {B : ℕ} {r : ℚ} (h : r.den ≤ B) : DenBound B r :=
  fun _ _ _ _ hpe => (Nat.le_of_dvd (Rat.pos r) hpe).trans h

/-- A prime power (with positive exponent) never divides `1`. -/
lemma not_prime_pow_dvd_one {p e : ℕ} (hp : p.Prime) (he : 0 < e) : ¬ p ^ e ∣ 1 := by
  intro hpe
  have h1 : p ^ e = 1 := Nat.dvd_one.mp hpe
  have h2 : 1 < p ^ e := one_lt_pow' hp.one_lt he.ne'
  omega

lemma of_den_eq_one {B : ℕ} {r : ℚ} (h : r.den = 1) : DenBound B r := by
  intro p e hp he hpe
  rw [h] at hpe
  exact absurd hpe (not_prime_pow_dvd_one hp he)

lemma intCast (B : ℕ) (z : ℤ) : DenBound B (z : ℚ) :=
  of_den_eq_one (by simp)

lemma natCast (B n : ℕ) : DenBound B (n : ℚ) :=
  of_den_eq_one (by simp)

/-- If a prime power divides the denominator of `x + y`, it divides the denominator
of `x` or of `y`. -/
lemma prime_pow_dvd_add_den {p e : ℕ} (hp : p.Prime) {x y : ℚ}
    (hpe : p ^ e ∣ (x + y).den) : p ^ e ∣ x.den ∨ p ^ e ∣ y.den := by
  have hdvd : p ^ e ∣ x.den.lcm y.den := hpe.trans (Rat.add_den_dvd_lcm x y)
  have hx : x.den ≠ 0 := x.den_ne_zero
  have hy : y.den ≠ 0 := y.den_ne_zero
  have hle : e ≤ (x.den.lcm y.den).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hx hy)).mp hdvd
  rw [Nat.factorization_lcm hx hy, Finsupp.sup_apply, le_sup_iff] at hle
  rcases hle with h1 | h1
  · exact Or.inl ((hp.pow_dvd_iff_le_factorization hx).mpr h1)
  · exact Or.inr ((hp.pow_dvd_iff_le_factorization hy).mpr h1)

lemma add {B : ℕ} {x y : ℚ} (hx : DenBound B x) (hy : DenBound B y) : DenBound B (x + y) := by
  intro p e hp he hpe
  rcases prime_pow_dvd_add_den hp hpe with h | h
  · exact hx p e hp he h
  · exact hy p e hp he h

lemma neg {B : ℕ} {x : ℚ} (hx : DenBound B x) : DenBound B (-x) := by
  intro p e hp he hpe
  rw [Rat.neg_den] at hpe
  exact hx p e hp he hpe

lemma sub {B : ℕ} {x y : ℚ} (hx : DenBound B x) (hy : DenBound B y) : DenBound B (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma sum {ι : Type*} {B : ℕ} {S : Finset ι} {f : ι → ℚ} (h : ∀ i ∈ S, DenBound B (f i)) :
    DenBound B (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact of_den_eq_one (by simp)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma div_nat {B : ℕ} (z : ℤ) {D : ℕ} (_hD : D ≠ 0)
    (hB : ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ D → p ^ e ≤ B) :
    DenBound B ((z : ℚ) / D) := by
  apply of_den_dvd _ hB
  have heq : (z : ℚ) / (D : ℚ) = Rat.divInt z (D : ℤ) := (Rat.divInt_eq_div z (D : ℤ)).symm
  rw [heq]
  have h := Rat.den_dvd z (D : ℤ)
  exact_mod_cast h

lemma one_div {B n : ℕ} (h : Powersmooth B n) : DenBound B (1 / (n : ℚ)) := by
  rw [_root_.one_div]
  intro p e hp he hpe
  rw [Rat.inv_natCast_den] at hpe
  split_ifs at hpe with hn
  · exact absurd hpe (not_prime_pow_dvd_one hp he)
  · exact h p e hp he hpe

lemma w {B n : ℕ} (hn : Powersmooth B n) (hn1 : Powersmooth B (n + 1)) :
    DenBound B (Erdos289.w n) := by
  have h1 : DenBound B (1 / (n : ℚ)) := one_div hn
  have h2 : DenBound B (1 / ((n : ℚ) + 1)) := by
    have h2' := one_div (n := n + 1) hn1
    push_cast at h2'
    exact h2'
  unfold Erdos289.w
  exact h1.add h2

/-- If `q = p ^ a` bounds the denominator of `r`, but `p` does not divide the
denominator of `r`, then in fact `q - 1` bounds the denominator of `r`. -/
lemma of_not_dvd_of_le {q a p : ℕ} {r : ℚ} (hr : DenBound q r) (hpa : q = p ^ a)
    (hp : p.Prime) (hnd : ¬ p ∣ r.den) : DenBound (q - 1) r := by
  intro l e hl he hle
  have hlq : l ^ e ≤ q := hr l e hl he hle
  have hne : l ≠ p := by
    rintro rfl
    exact hnd (dvd_trans (dvd_pow_self l he.ne') hle)
  have hneq : l ^ e ≠ q := by
    subst hpa
    intro heq
    apply hne
    have hld : l ∣ p ^ a := heq ▸ dvd_pow_self l he.ne'
    exact (Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow hld)
  omega

/-- The lcm of `1, ..., L`. -/
def lcmIcc (L : ℕ) : ℕ := (Finset.Icc 1 L).lcm id

lemma lcmIcc_pos (L : ℕ) : 0 < lcmIcc L := by
  rw [lcmIcc, Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
  intro x hx
  have := (Finset.mem_Icc.mp hx).1
  simp only [id]
  omega

lemma le_dvd_lcmIcc {L n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ L) : n ∣ lcmIcc L := by
  have hmem : n ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨h1, h2⟩
  exact Finset.dvd_lcm hmem

lemma lcm {L : ℕ} {r : ℚ} (h : DenBound L r) : r.den ∣ lcmIcc L := by
  rw [lcmIcc, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · have hle : p ^ k ≤ L := h p k hp hk0 hpk
    have hmem : p ^ k ∈ Finset.Icc 1 L :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.pos.ne'), hle⟩
    exact Finset.dvd_lcm hmem

end DenBound

end Erdos289
