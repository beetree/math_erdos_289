import Mathlib

/-!
# Erdős Problem 289: shared definitions

Definitions used throughout the formalization of `erdos_289_full_proof.pdf`.
-/

namespace Erdos289

open Finset

/-- `n` is `y`-powersmooth if every prime-power divisor of `n` is at most `y`. -/
def Powersmooth (y n : ℕ) : Prop :=
  ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ n → p ^ e ≤ y

/-- Reciprocal mass of the integer interval `[a, b]` (both endpoints included). -/
def mass (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

/-- Reciprocal mass of the pair `[a, a + 1]`, written `w(a)` in the paper. -/
def w (a : ℕ) : ℚ := 1 / a + 1 / (a + 1)

lemma mass_pair (a : ℕ) : mass a (a + 1) = w a := by
  unfold mass w
  rw [show Icc a (a + 1) = {a, a + 1} by ext; simp; omega]
  rw [sum_pair (by omega)]; push_cast; ring

lemma mass_triple (a : ℕ) : mass a (a + 2) = 1 / a + w (a + 1) := by
  unfold mass w
  rw [show Icc a (a + 2) = {a, a + 1, a + 2} by ext; simp; omega]
  rw [sum_insert (by simp), sum_pair (by omega)]
  push_cast; ring

/-- An integer interval `[lo, hi]`. -/
@[ext]
structure Iv where
  lo : ℕ
  hi : ℕ
deriving DecidableEq

namespace Iv

/-- Reciprocal mass of an interval. -/
def mass (I : Iv) : ℚ := Erdos289.mass I.lo I.hi

/-- Two intervals are separated if at least one integer lies strictly between them. -/
def Sep (I J : Iv) : Prop := I.hi + 1 < J.lo ∨ J.hi + 1 < I.lo

lemma Sep.symm {I J : Iv} (h : Sep I J) : Sep J I := Or.symm h

/-- The pair `[a, a+1]`. -/
def pair (a : ℕ) : Iv := ⟨a, a + 1⟩

/-- The triple `[a, a+2]`. -/
def triple (a : ℕ) : Iv := ⟨a, a + 2⟩

end Iv

/-- A finite family of intervals witnessing the theorem for a given `k`:
exactly `k` intervals, each of length 2 or 3, within `[1, 20k]`, pairwise separated,
with reciprocal masses summing to `1`. -/
structure GoodFamily (k : ℕ) where
  F : Finset Iv
  card_eq : F.card = k
  one_le : ∀ I ∈ F, 1 ≤ I.lo
  le_bound : ∀ I ∈ F, I.hi ≤ 20 * k
  len : ∀ I ∈ F, I.hi + 1 - I.lo = 2 ∨ I.hi + 1 - I.lo = 3
  sep : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Iv.Sep I J
  sum_eq : ∑ I ∈ F, I.mass = 1

/-- The statement of Erdős Problem 289 (nonadjacent form) for a fixed `k`:
there are integer intervals `[a i, b i]`, `i < k`, with `1 ≤ a i ≤ b i ≤ 20k`,
each of length 2 or 3, consecutive intervals separated by at least one unused integer,
and reciprocals summing to `1`. -/
def Statement (k : ℕ) : Prop :=
  ∃ a b : Fin k → ℕ,
    (∀ i, 1 ≤ a i) ∧ (∀ i, a i ≤ b i) ∧ (∀ i, b i ≤ 20 * k) ∧
    (∀ i, b i + 1 - a i = 2 ∨ b i + 1 - a i = 3) ∧
    (∀ i j : Fin k, i.val + 1 = j.val → b i + 1 < a j) ∧
    ∑ i, mass (a i) (b i) = 1

end Erdos289
