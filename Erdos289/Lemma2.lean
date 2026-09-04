import Erdos289.Defs

/-!
# Erdős Problem 289: Lemma 2

The pairs `[qm, qm+1]`, for `m ∈ I_q` (where `q = p^a` is a prime power), are mutually
disjoint and nonadjacent, including when `q` varies.

The key facts about `I_q` from Lemma 1 that we need here are: for `m ∈ I_q`,
`p ∤ m`, `4 ∣ q*m`, and `m < q`. We abstract the argument in terms of these facts.
-/

namespace Erdos289

/-- Every prime-power divisor of `p ^ a * m` is at most `p ^ a`, when `p` is prime, `p ∤ m`,
and `0 < m < p ^ a`. This says that the largest prime-power divisor of `p ^ a * m` is
(uniquely) `p ^ a`. -/
theorem primePow_dvd_mul_le {p a m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m < p ^ a)
    (hm0 : 0 < m) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 0 < e) (hdvd : ℓ ^ e ∣ p ^ a * m) :
    ℓ ^ e ≤ p ^ a := by
  by_cases hlp : ℓ = p
  · subst hlp
    have hcop : Nat.Coprime ℓ m := hℓ.coprime_iff_not_dvd.2 hpm
    have hcop' : Nat.Coprime (ℓ ^ e) m := hcop.pow_left e
    have : ℓ ^ e ∣ ℓ ^ a := hcop'.dvd_of_dvd_mul_right hdvd
    exact Nat.le_of_dvd (pow_pos hℓ.pos a) this
  · have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ hp).2 hlp
    have hcop' : Nat.Coprime (ℓ ^ e) (p ^ a) := hcop.pow e a
    have hdm : ℓ ^ e ∣ m := hcop'.dvd_of_dvd_mul_left hdvd
    have : ℓ ^ e ≤ m := Nat.le_of_dvd hm0 hdm
    exact le_trans this (le_of_lt hm)

/-- If `p ^ a * m = p' ^ a' * m'` with `p, p'` prime, `p ∤ m`, `p' ∤ m'`, and
`0 < m < p ^ a`, `0 < m' < p' ^ a'`, then `p ^ a = p' ^ a'` and `m = m'`.
This is the uniqueness of the "label" `(q, m)` of a correction pair `[qm, qm+1]`. -/
theorem eq_of_mul_eq {p a m p' a' m' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (ha : 0 < a)
    (ha' : 0 < a') (hpm : ¬ p ∣ m) (hpm' : ¬ p' ∣ m') (hm : m < p ^ a) (hm' : m' < p' ^ a')
    (hm0 : 0 < m) (hm0' : 0 < m') (h : p ^ a * m = p' ^ a' * m') :
    p ^ a = p' ^ a' ∧ m = m' := by
  have hdvd1 : p' ^ a' ∣ p ^ a * m := h ▸ Dvd.intro m' rfl
  have hdvd2 : p ^ a ∣ p' ^ a' * m' := h.symm ▸ Dvd.intro m rfl
  have hle1 : p' ^ a' ≤ p ^ a := primePow_dvd_mul_le hp hpm hm hm0 hp' ha' hdvd1
  have hle2 : p ^ a ≤ p' ^ a' := primePow_dvd_mul_le hp' hpm' hm' hm0' hp ha hdvd2
  have heq : p ^ a = p' ^ a' := le_antisymm hle2 hle1
  refine ⟨heq, ?_⟩
  have h' : p ^ a * m = p ^ a * m' := by rw [h, heq]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h'

/-- Two pairs `[x, x+1]` and `[y, y+1]` with `x ≠ y` both multiples of `4` are separated:
distinct multiples of `4` differ by at least `4`, leaving at least two unused integers
between the two pairs. -/
theorem sep_pair_of_four_dvd {x y : ℕ} (hx : 4 ∣ x) (hy : 4 ∣ y) (hxy : x ≠ y) :
    Iv.Sep (Iv.pair x) (Iv.pair y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  unfold Iv.Sep Iv.pair
  simp only
  omega

/-- The correction pair with label `(q, m)` is `[q*m, q*m+1]`. -/
def corrPair (q m : ℕ) : Iv := Iv.pair (q * m)

/-- **Lemma 2.** The correction pairs `[qm, qm+1]` for distinct labels `(q, m) = (p^a, m)`,
`(q', m') = (p'^a', m')` (with `q, q'` prime powers, `p ∤ m`, `p' ∤ m'`, `m < q`, `m' < q'`,
and `4 ∣ qm`, `4 ∣ q'm'`) are mutually separated -- disjoint and nonadjacent, whether or not
`q = q'`. -/
theorem lemma2 {p a m p' a' m' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (ha : 0 < a) (ha' : 0 < a')
    (hpm : ¬ p ∣ m) (hpm' : ¬ p' ∣ m') (hm : m < p ^ a) (hm' : m' < p' ^ a') (hm0 : 0 < m)
    (hm0' : 0 < m') (h4 : 4 ∣ p ^ a * m) (h4' : 4 ∣ p' ^ a' * m')
    (hne : (p ^ a, m) ≠ (p' ^ a', m')) :
    Iv.Sep (corrPair (p ^ a) m) (corrPair (p' ^ a') m') := by
  unfold corrPair
  apply sep_pair_of_four_dvd h4 h4'
  intro h
  apply hne
  obtain ⟨h1, h2⟩ := eq_of_mul_eq hp hp' ha ha' hpm hpm' hm hm' hm0 hm0' h
  rw [h1, h2]

end Erdos289
