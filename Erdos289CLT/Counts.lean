import Erdos289CLT.Asymptotics

/-!
# The count intervals

`Ucount B X = ∑ s(q)` over prime powers `q ∈ (B, X]`.  Starting from width `2 s(B)`
at a power of two `B`, the count interval at cutoff `X` is
`[u₀ + Ucount B X, u₀ + 2 s(B) + 2 Ucount B X]`; successive intervals overlap and
their right endpoints tend to infinity, so every large `k` lies in one of them.
-/

namespace Erdos289.CLT

open Finset

/-- `∑ s(q)` over the prime powers `q ∈ (B, X]`. -/
noncomputable def Ucount (B X : ℕ) : ℕ := ∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, s q

theorem Ucount_succ_of_isPrimePow {B X : ℕ} (hBX : B ≤ X) (h : IsPrimePow (X + 1)) :
    Ucount B (X + 1) = Ucount B X + s (X + 1) := by
  have hmem : (X + 1) ∉ (Finset.Ioc B X).filter IsPrimePow := by
    simp [Finset.mem_filter]
  have heq : (Finset.Ioc B (X + 1)).filter IsPrimePow =
      insert (X + 1) ((Finset.Ioc B X).filter IsPrimePow) := by
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hBX, Finset.filter_insert, ite_eq_left h]
  rw [Ucount, Ucount, heq, Finset.sum_insert hmem]
  ring

theorem Ucount_succ_of_not_isPrimePow {B X : ℕ} (hBX : B ≤ X) (h : ¬ IsPrimePow (X + 1)) :
    Ucount B (X + 1) = Ucount B X := by
  have heq : (Finset.Ioc B (X + 1)).filter IsPrimePow =
      (Finset.Ioc B X).filter IsPrimePow := by
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hBX, Finset.filter_insert, ite_eq_right h]
  rw [Ucount, Ucount, heq]

private theorem log_two_sub_one_of_pred_eq_two_pow {n k : ℕ} (hk : 1 ≤ k) (h : n + 1 = 2 ^ k) :
    Nat.log 2 n = k - 1 := by
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · have h1 : 0 < 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
    have hexp : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [Nat.pow_succ]
    omega
  · rw [show (k - 1) + 1 = k from by omega]
    exact h ▸ Nat.lt_succ_self _

private theorem log_two_succ_eq_log_two {n : ℕ} (hn : 1 ≤ n)
    (h : n + 1 ≠ 2 ^ (Nat.log 2 n + 1)) : Nat.log 2 (n + 1) = Nat.log 2 n := by
  refine Nat.log_eq_of_pow_le_of_lt_pow
    ((@Nat.pow_log_le_self 2 n (by omega)).trans (Nat.le_succ n)) ?_
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    simpa using this
  omega

/-- The width invariant: at every level `X ≥ B` the width `2 s(B) + Ucount B X` dominates
`2 s(2^{⌊log₂ X⌋})`, hence `s(X+1)`. -/
theorem width_invariant {B : ℕ} (hB : 1 ≤ B) (hBpow : B = 2 ^ Nat.log 2 B) {X : ℕ}
    (hBX : B ≤ X) : 2 * s (2 ^ Nat.log 2 X) ≤ 2 * s B + Ucount B X := by
  obtain ⟨n, rfl⟩ : ∃ n, X = B + n := ⟨X - B, by omega⟩
  induction n with
  | zero =>
    show 2 * s (2 ^ Nat.log 2 B) ≤ 2 * s B + Ucount B B
    rw [show 2 ^ Nat.log 2 B = B from hBpow.symm]
    exact Nat.le_add_right _ _
  | succ n ih =>
    have hxB : B ≤ B + n := by omega
    by_cases hpow : ∃ k, B + n + 1 = 2 ^ k
    · obtain ⟨k, hk⟩ := hpow
      have hkpos : 1 ≤ k := by
        cases k with
        | zero => rw [Nat.pow_zero] at hk; omega
        | succ m => exact Nat.succ_le_succ (Nat.zero_le m)
      have hpp : IsPrimePow (B + n + 1) := by
        rw [hk]
        exact IsPrimePow.pow (Nat.Prime.isPrimePow Nat.prime_two) (Nat.ne_of_gt hkpos)
      have hlogpow : Nat.log 2 (B + n + 1) = k := by
        rw [hk, Nat.log_pow (by norm_num : 1 < 2)]
      have hlogx : Nat.log 2 (B + n) = k - 1 :=
        log_two_sub_one_of_pred_eq_two_pow hkpos hk
      have hpoweq : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [Nat.pow_succ]
        ring
      have hA : s (2 * 2 ^ Nat.log 2 (B + n)) ≤ 2 * s B + Ucount B (B + n) :=
        Nat.le_trans (s_two_mul_le _) (ih hxB)
      rw [hlogx, ← hpoweq] at hA
      show 2 * s (2 ^ Nat.log 2 (B + n + 1)) ≤
        2 * s B + Ucount B (B + n + 1)
      rw [Ucount_succ_of_isPrimePow hxB hpp, hlogpow, hk]
      omega
    · have hne : B + n + 1 ≠ 2 ^ (Nat.log 2 (B + n) + 1) := by
        intro he
        exact hpow ⟨_, he⟩
      have hlog : Nat.log 2 (B + n + 1) = Nat.log 2 (B + n) :=
        log_two_succ_eq_log_two (by omega) hne
      by_cases hpp : IsPrimePow (B + n + 1)
      · show 2 * s (2 ^ Nat.log 2 (B + n + 1)) ≤
          2 * s B + Ucount B (B + n + 1)
        rw [hlog, Ucount_succ_of_isPrimePow hxB hpp]
        omega
      · show 2 * s (2 ^ Nat.log 2 (B + n + 1)) ≤
          2 * s B + Ucount B (B + n + 1)
        rw [hlog, Ucount_succ_of_not_isPrimePow hxB hpp]
        exact ih hxB
theorem s_succ_le_width {B : ℕ} (hB : 1 ≤ B) (hBpow : B = 2 ^ Nat.log 2 B) {X : ℕ}
    (hBX : B ≤ X) : s (X + 1) ≤ 2 * s B + Ucount B X :=
  Nat.le_trans (s_succ_le (by omega)) (width_invariant hB hBpow hBX)

private theorem Ucount_split {B X Y : ℕ} (hBX : B ≤ X) (hXY : X ≤ Y) :
    Ucount B Y = Ucount B X +
      ∑ q ∈ (Finset.Ioc X Y).filter IsPrimePow, s q := by
  have hsets : (Finset.Ioc B Y).filter IsPrimePow =
      (Finset.Ioc B X).filter IsPrimePow ∪ (Finset.Ioc X Y).filter IsPrimePow := by
    refine Finset.ext fun q => ?_
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hq⟩
      by_cases h : q ≤ X
      · exact Or.inl ⟨⟨h1, h⟩, hq⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hq⟩
    · rintro (⟨⟨h1, h2⟩, hq⟩ | ⟨⟨h1, h2⟩, hq⟩)
      · exact ⟨⟨h1, by omega⟩, hq⟩
      · exact ⟨⟨by omega, h2⟩, hq⟩
  have hdisj : Disjoint ((Finset.Ioc B X).filter IsPrimePow)
      ((Finset.Ioc X Y).filter IsPrimePow) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha hb
    omega
  unfold Ucount
  rw [hsets, Finset.sum_union hdisj]

theorem Ucount_unbounded (B : ℕ) : ∀ n : ℕ, ∃ X : ℕ, n ≤ Ucount B X := by
  have key : ∀ n : ℕ, ∃ X : ℕ, B ≤ X ∧ n ≤ Ucount B X := by
    intro n
    induction n with
    | zero => exact ⟨B, le_refl _, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨X, hBX, hn⟩ := ih
      obtain ⟨p, hpmax, hpprime⟩ := Nat.exists_infinite_primes (max B X + 1)
      have hpB : B < p := by omega
      have hpX : X < p := by omega
      have hmem : p ∈ (Finset.Ioc X p).filter IsPrimePow := by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨by omega, Nat.Prime.isPrimePow hpprime⟩
      have hsppos : 1 ≤ s p := s_pos (Nat.Prime.pos hpprime)
      have hsum : s p ≤ ∑ q ∈ (Finset.Ioc X p).filter IsPrimePow, s q := by
        have hsub : {p} ⊆ (Finset.Ioc X p).filter IsPrimePow :=
          Finset.singleton_subset_iff.2 hmem
        calc s p = ∑ q ∈ {p}, s q := Eq.symm (Finset.sum_singleton _ _)
          _ ≤ ∑ q ∈ (Finset.Ioc X p).filter IsPrimePow, s q :=
                Finset.sum_le_sum_of_subset hsub
      refine ⟨p, by omega, ?_⟩
      have hXY : X ≤ p := by omega
      have hsplit := Ucount_split hBX hXY
      calc n + 1 ≤ n + s p := by omega
        _ ≤ Ucount B X + ∑ q ∈ (Finset.Ioc X p).filter IsPrimePow, s q := by omega
        _ = Ucount B p := hsplit.symm
  intro n
  obtain ⟨X, _, hX⟩ := key n
  exact ⟨X, hX⟩

private theorem Ucount_mono {B X X' : ℕ} (h : X ≤ X') : Ucount B X ≤ Ucount B X' := by
  unfold Ucount
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right h))

private theorem Ucount_succ_le {B X : ℕ} (hBX : B ≤ X) :
    Ucount B (X + 1) ≤ Ucount B X + s (X + 1) := by
  by_cases hpp : IsPrimePow (X + 1)
  · rw [Ucount_succ_of_isPrimePow hBX hpp]
  · rw [Ucount_succ_of_not_isPrimePow hBX hpp]
    omega

/-- Every `k ≥ u₀ + Ucount B X₀` lies in the count interval of some cutoff `X ≥ X₀`. -/
theorem exists_cutoff {B X₀ u₀ : ℕ} (hB : 1 ≤ B) (hBpow : B = 2 ^ Nat.log 2 B) (hX₀ : B ≤ X₀) :
    ∀ k : ℕ, u₀ + Ucount B X₀ ≤ k →
      ∃ X : ℕ, X₀ ≤ X ∧ u₀ + Ucount B X ≤ k ∧ k ≤ u₀ + 2 * s B + 2 * Ucount B X := by
  intro k hk
  obtain ⟨X', hX'⟩ := Ucount_unbounded B k
  have hex : ∃ n : ℕ, k ≤ u₀ + 2 * s B + 2 * Ucount B (X₀ + n) := by
    refine ⟨max X₀ X' - X₀, ?_⟩
    have heq : X₀ + (max X₀ X' - X₀) = max X₀ X' := by omega
    rw [heq]
    have h1 : X' ≤ max X₀ X' := le_max_right _ _
    have h2 : k ≤ Ucount B (max X₀ X') := le_trans hX' (Ucount_mono h1)
    omega
  classical
  have hn : k ≤ u₀ + 2 * s B + 2 * Ucount B (X₀ + Nat.find hex) := Nat.find_spec hex
  refine ⟨X₀ + Nat.find hex, Nat.le_add_right _ _, ?_, hn⟩
  rcases hcase : Nat.find hex with _ | m
  · simpa using hk
  · have hmlt : m < Nat.find hex := by omega
    have hfmin := Nat.find_min hex hmlt
    push Not at hfmin
    have hBXm : B ≤ X₀ + m := by omega
    have hstep : s (X₀ + m + 1) ≤ 2 * s B + Ucount B (X₀ + m) :=
      s_succ_le_width hB hBpow hBXm
    have hUstep : Ucount B (X₀ + m + 1) ≤ Ucount B (X₀ + m) + s (X₀ + m + 1) :=
      Ucount_succ_le hBXm
    have hgoaleq : X₀ + (m + 1) = X₀ + m + 1 := by omega
    rw [hgoaleq]
    omega

end Erdos289.CLT
