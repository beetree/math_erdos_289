import Erdos289.Defs
import Erdos289.ExternalAxioms

/-!
# External inputs from the published literature

This file collects the classical analytic number theory estimates used by the proof and the
places where the literature inputs enter. Historically the literature results were declared here
as named `axiom`s; in the completed formalization every input used by the terminal theorem is a
proved theorem: Chebyshev's bound is derived below from Mathlib, the prime-power count is proved
below from it, and Mertens' second theorem, the divisor bound, the Liu–Sawhney theorem and the
Conlon–Fox–Pham structure theorem are supplied by vendored proofs via `Erdos289/ExternalBridge.lean`
and `Erdos289/CFPBridge.lean`. The terminal theorem `Erdos289.candidateStatement` reports only
`[propext, Classical.choice, Quot.sound]`. Bourgain–Garaev and Erdős–Turán are not used.
-/

namespace Erdos289

open Filter Topology
open scoped BigOperators

/-! ## 1. Liu–Sawhney: dense subsets of `[1,N]` contain a unit-fraction sum to `1`. -/

-- `liu_sawhney` is now derived from the audited axiom module; see `ExternalBridge.lean`.

/-! ## 2. Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte: structure in bounded subset sums.

To state this theorem we first need a notion of a (proper) generalized arithmetic
progression (GAP) of bounded rank, and its dilates, following the conventions spelled
out in the proof text (Section 1, lines 63-81): a GAP of rank `D` is given by integer
generators `d : Fin D → ℤ` together with real coordinate bounds `α β : Fin D → ℝ`; its
underlying set consists of the integer combinations `∑ i, n i * d i` with each integer
coordinate `n i` inside `[α i, β i]`. It is *proper* when this coordinate-to-value map is
injective on the coordinate box. Dilating by a real `t` keeps the same generators and
scales the coordinate intervals to `[t * α i, t * β i]`. -/

/-- A generalized arithmetic progression (GAP): integer generators `d i` together with
real lower/upper coordinate bounds `α i ≤ β i`, following Conlon–Fox–He–Mubayi–Pham–Suk–
Verstraëte (and Conlon–Fox–Pham, *Homogeneous structures in subset sums and non-averaging
sets*, Theorem 1.5, from which the structure theorem below is derived). -/
structure GAP where
  /-- The rank of the progression. -/
  D : ℕ
  /-- The integer generators `d 1, …, d D`. -/
  d : Fin D → ℤ
  /-- The lower coordinate bounds. -/
  α : Fin D → ℝ
  /-- The upper coordinate bounds. -/
  β : Fin D → ℝ

namespace GAP

/-- The underlying set of a GAP: all integer combinations `∑ i, n i * d i` with every
coordinate `n i` inside the real interval `[α i, β i]`. -/
def set (P : GAP) : Set ℤ :=
  {x | ∃ n : Fin P.D → ℤ, (∀ i, P.α i ≤ (n i : ℝ) ∧ (n i : ℝ) ≤ P.β i) ∧ x = ∑ i, n i * P.d i}

/-- A GAP is *proper* if distinct admissible coordinate vectors give distinct values,
i.e. the progression has one element for each point of its defining integer coordinate
box. -/
def Proper (P : GAP) : Prop :=
  ∀ n m : Fin P.D → ℤ,
    (∀ i, P.α i ≤ (n i : ℝ) ∧ (n i : ℝ) ≤ P.β i) →
    (∀ i, P.α i ≤ (m i : ℝ) ∧ (m i : ℝ) ≤ P.β i) →
    ∑ i, n i * P.d i = ∑ i, m i * P.d i → n = m

/-- The dilate `t • P` of a GAP by a real `t`: the same generators, with coordinate
bounds scaled by `t`. For noninteger `t` this depends on the chosen representation `P`,
which is why the representation is kept fixed throughout the proof (Section 1, lines
78-81). -/
def dilate (t : ℝ) (P : GAP) : GAP where
  D := P.D
  d := P.d
  α := fun i => t * P.α i
  β := fun i => t * P.β i

end GAP

/-- The set of subset sums of a finite set `J` of natural numbers, viewed as a set of
integers: `{∑ x ∈ T, (x : ℤ) | T ⊆ J}`. -/
def subsetSums (J : Finset ℕ) : Set ℤ :=
  {x | ∃ T ⊆ J, x = ∑ i ∈ T, (i : ℤ)}

-- `cfhmpsv_structure` is now derived from the audited axiom module; see `ExternalBridge.lean`.

/-! ## 3. Bourgain–Garaev: short sums of modular inverses. -/

/-- The additive character `e_m(x) = exp(2πix/m)`. -/
noncomputable def e (m : ℕ) (x : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x / m)

-- `bourgain_garaev` is now derived from the audited axiom module; see `ExternalBridge.lean`.

/-! ## 4. Classical estimates.

We first check what Mathlib already supplies:

* `Chebyshev.pi_le_log4_mul_div` in `Mathlib.NumberTheory.Chebyshev` gives an explicit
  Chebyshev-type upper bound `π ⌊x⌋₊ ≤ log 4 * x / log √x + √x`, from which the crude
  bound `primeCounting_le` below is derived (no `sorry` needed).
* Mathlib has no Mertens' second theorem (no lemma name involving `Mertens`, and no
  statement of `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)`); `mertens_second` is supplied by the
  vendored proof `Erdos289.Ported.mertens_second` (see `ExternalBridge.lean`).
* Mathlib has no uniform divisor bound `τ(n) = n^{o(1)}` (only the trivial
  `Nat.card_divisors_le_self : n.divisors.card ≤ n`); `divisor_bound` is supplied by the
  vendored proof `Erdos289.Ported.divisor_bound` (see `ExternalBridge.lean`).
* Mathlib has no bound on the count of prime powers up to `Y`; `primePow_count_le` is proved
  below from `primeCounting_le` (a prime power `≤ Y` is `p^k` with `p ≤ Y` and `k ≤ log₂ Y`,
  and for `k ≥ 2` already `p ≤ √Y`). -/

/-- **Chebyshev's upper bound** for the prime counting function. Proved here from
`Chebyshev.pi_le_log4_mul_div` (Mathlib), using `log x ≤ 2 * (√x - 1) ≤ 2 √x` and
`√x * log x ≤ 2 x` to absorb the `√x` error term of the Mathlib bound into the
main term. -/
theorem primeCounting_le :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → (Nat.primeCounting x : ℝ) ≤ C * (x : ℝ) / Real.log x := by
  refine ⟨2 * Real.log 4 + 2, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hsqrtpos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hfloor : ⌊(x : ℝ)⌋₊ = x := Nat.floor_natCast x
  have h := Chebyshev.pi_le_log4_mul_div hx1
  rw [hfloor] at h
  have hlogsqrt : Real.log (Real.sqrt (x : ℝ)) = Real.log (x : ℝ) / 2 := Real.log_sqrt hxpos.le
  have hsq : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := Real.mul_self_sqrt hxpos.le
  have hlogne : Real.log (x : ℝ) ≠ 0 := hlogpos.ne'
  have hlog_le : Real.log (x : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
    have h1 : Real.log (Real.sqrt (x : ℝ)) ≤ Real.sqrt (x : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hsqrtpos
    rw [hlogsqrt] at h1
    linarith
  rw [hlogsqrt] at h
  rw [le_div_iff₀ hlogpos]
  have e1 : Real.log 4 * (x : ℝ) / (Real.log (x : ℝ) / 2) * Real.log (x : ℝ)
      = 2 * Real.log 4 * (x : ℝ) := by
    field_simp
  have e2 : Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤ 2 * (x : ℝ) := by
    nlinarith [Real.sqrt_nonneg (x : ℝ), hlog_le, hsq]
  have hh : (Nat.primeCounting x : ℝ) * Real.log (x : ℝ)
      ≤ (Real.log 4 * (x : ℝ) / (Real.log (x : ℝ) / 2) + Real.sqrt (x : ℝ)) * Real.log (x : ℝ) :=
    mul_le_mul_of_nonneg_right h hlogpos.le
  rw [add_mul, e1] at hh
  linarith

-- `mertens_second` and `divisor_bound` are aliases of the vendored proofs; see `ExternalBridge.lean`.

/-- The count of prime powers up to `Y` is `O(Y / log Y)`, uniformly in `Y`. This is a
routine consequence of `primeCounting_le` (a prime power `p^k ≤ Y` has `p ≤ Y`, and for
`k ≥ 2` already `p ≤ √Y`, while `k ≤ log₂ Y` always); the counting argument is carried out
below. -/
theorem primePow_count_le :
    ∃ C : ℝ, ∀ Y : ℕ, 2 ≤ Y →
      (((Finset.Icc 1 Y).filter (fun n => IsPrimePow n)).card : ℝ) ≤ C * (Y : ℝ) / Real.log Y := by
  obtain ⟨C1, hC1⟩ := primeCounting_le
  refine ⟨C1 + 16 / Real.log 2, fun Y hY => ?_⟩
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hY1 : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 1 < Y)
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos hY1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set S : Finset ℕ := (Finset.Icc 1 Y).filter (fun n => IsPrimePow n) with hSdef
  set S1 : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime with hS1def
  set S2 : Finset ℕ := (Finset.Icc 1 Y).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) with hS2def
  have hSsub : S ⊆ S1 ∪ S2 := by
    intro n hn
    simp only [hSdef, Finset.mem_filter] at hn
    by_cases hp : Nat.Prime n
    · exact Finset.mem_union_left _ (by simp [hS1def, hn.1, hp])
    · exact Finset.mem_union_right _ (by simp [hS2def, hn.1, hn.2, hp])
  have hScard : (S.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
    calc (S.card : ℝ) ≤ ((S1 ∪ S2).card : ℝ) := by exact_mod_cast Finset.card_le_card hSsub
    _ ≤ (S1.card : ℝ) + (S2.card : ℝ) := by exact_mod_cast Finset.card_union_le S1 S2
  -- Bound `S1`, the primes, via `primeCounting_le`.
  have hS1eq : S1 = Nat.primesLE Y := by
    rw [hS1def, Nat.primesLE_eq_filter_Icc_one]
  have hS1card : (S1.card : ℝ) ≤ C1 * (Y : ℝ) / Real.log Y := by
    rw [hS1eq, Nat.primesLE_card_eq_primeCounting]
    exact hC1 Y hY
  -- Bound `S2`, the higher prime powers, by injecting into a small product `Finset`.
  have hkey : ∀ n ∈ S2, 2 ≤ n.minFac ∧ n.minFac ^ 2 ≤ Y ∧ 2 ≤ Nat.log n.minFac n ∧
      Nat.log n.minFac n ≤ Nat.log 2 Y ∧ n = n.minFac ^ (Nat.log n.minFac n) := by
    intro n hn
    simp only [hS2def, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnY⟩, hIPP, hnp⟩ := hn
    have hn2 : 2 ≤ n := hIPP.two_le
    have hmf : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
    obtain ⟨k, hklog, hkpos, heq⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hIPP
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso
        have hk1 : k = 1 := by omega
        subst hk1
        have hn1' : n = n.minFac := by simpa using heq
        exact hnp (by rw [hn1']; exact hmf)
      · exact h
    have hlogeq : Nat.log n.minFac n = k := by
      have h1 := congrArg (Nat.log n.minFac) heq
      rwa [Nat.log_pow hmf.one_lt] at h1
    refine ⟨hmf.two_le, ?_, ?_, ?_, ?_⟩
    · calc n.minFac ^ 2 ≤ n.minFac ^ k := Nat.pow_le_pow_right hmf.one_le hk2
      _ = n := heq.symm
      _ ≤ Y := hnY
    · rw [hlogeq]; exact hk2
    · rw [hlogeq]
      calc k ≤ Nat.log 2 n := hklog
      _ ≤ Nat.log 2 Y := Nat.log_mono_right hnY
    · rw [hlogeq]; exact heq
  set T : Finset (ℕ × ℕ) := (Finset.Icc 2 (Nat.sqrt Y)) ×ˢ (Finset.Icc 2 (Nat.log 2 Y)) with hTdef
  have hmaps : ∀ n ∈ S2, (n.minFac, Nat.log n.minFac n) ∈ T := by
    intro n hn
    obtain ⟨h1, h2, h3, h4, _⟩ := hkey n hn
    simp only [hTdef, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨h1, Nat.le_sqrt'.mpr h2⟩, h3, h4⟩
  have hinj : Set.InjOn (fun n => (n.minFac, Nat.log n.minFac n)) (S2 : Set ℕ) := by
    intro n1 hn1 n2 hn2 heq12
    obtain ⟨_, _, _, _, hval1⟩ := hkey n1 hn1
    obtain ⟨_, _, _, _, hval2⟩ := hkey n2 hn2
    have e1 : n1.minFac = n2.minFac := congrArg Prod.fst heq12
    have e2 : Nat.log n1.minFac n1 = Nat.log n2.minFac n2 := congrArg Prod.snd heq12
    calc n1 = n1.minFac ^ (Nat.log n1.minFac n1) := hval1
    _ = n2.minFac ^ (Nat.log n2.minFac n2) := by rw [e2, e1]
    _ = n2 := hval2.symm
  have hcard_le : S2.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun n => (n.minFac, Nat.log n.minFac n)) hmaps hinj
  have hIccle : ∀ m : ℕ, (Finset.Icc 2 m).card ≤ m := by
    intro m; rw [Nat.card_Icc]; omega
  have hTcard_le : T.card ≤ Nat.sqrt Y * Nat.log 2 Y := by
    rw [hTdef, Finset.card_product]
    exact Nat.mul_le_mul (hIccle _) (hIccle _)
  have hS2card_nat : (S2.card : ℝ) ≤ (Nat.sqrt Y : ℝ) * (Nat.log 2 Y : ℝ) := by
    have : S2.card ≤ Nat.sqrt Y * Nat.log 2 Y := hcard_le.trans hTcard_le
    exact_mod_cast this
  -- Analytic bound: `√Y · log₂ Y = O(Y / log Y)`.
  have hnatsqrt_le : (Nat.sqrt Y : ℝ) ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    have := Nat.sqrt_le' Y
    exact_mod_cast this
  have hnatlog_le : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log Y := by
    have h1 : (2 : ℕ) ^ (Nat.log 2 Y) ≤ Y := Nat.pow_log_le_self 2 (by omega)
    have h2 : (((2 : ℕ) ^ (Nat.log 2 Y) : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast h1
    have h3 : Real.log (((2 : ℕ) ^ (Nat.log 2 Y) : ℕ) : ℝ) ≤ Real.log Y :=
      Real.log_le_log (by positivity) h2
    rwa [show (((2 : ℕ) ^ (Nat.log 2 Y) : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 Y) by push_cast; ring,
      Real.log_pow] at h3
  have hYsq : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = (Y : ℝ) := Real.mul_self_sqrt hYpos.le
  have hlogsq_le : Real.log (Y : ℝ) * Real.log (Y : ℝ) ≤ 16 * Real.sqrt (Y : ℝ) := by
    set w := Real.sqrt (Real.sqrt (Y : ℝ)) with hwdef
    have hw_pos : 0 < w := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hYpos)
    have h1 : w * w = Real.sqrt (Y : ℝ) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hw4 : w ^ 4 = (Y : ℝ) := by
      have e : w ^ 4 = (w * w) * (w * w) := by ring
      rw [e, h1, hYsq]
    have hlogw_le : Real.log w ≤ w :=
      le_trans (Real.log_le_sub_one_of_pos hw_pos) (by linarith)
    have hlogY_eq : Real.log (Y : ℝ) = 4 * Real.log w := by
      conv_lhs => rw [← hw4]
      rw [Real.log_pow]; norm_num
    have hlogY_le : Real.log (Y : ℝ) ≤ 4 * w := by rw [hlogY_eq]; linarith
    have hsq := mul_self_le_mul_self hlogYpos.le hlogY_le
    calc Real.log (Y : ℝ) * Real.log (Y : ℝ) ≤ (4 * w) * (4 * w) := hsq
    _ = 16 * (w * w) := by ring
    _ = 16 * Real.sqrt (Y : ℝ) := by rw [h1]
  have hstep : (Nat.sqrt Y : ℝ) * (Nat.log 2 Y : ℝ) * (Real.log 2 * Real.log Y) ≤ 16 * (Y : ℝ) := by
    have e1 : (Nat.sqrt Y : ℝ) * ((Nat.log 2 Y : ℝ) * Real.log 2) ≤ Real.sqrt Y * Real.log Y :=
      mul_le_mul hnatsqrt_le hnatlog_le (by positivity) (Real.sqrt_nonneg _)
    have e2 : (Nat.sqrt Y : ℝ) * ((Nat.log 2 Y : ℝ) * Real.log 2) * Real.log Y
        ≤ Real.sqrt Y * Real.log Y * Real.log Y :=
      mul_le_mul_of_nonneg_right e1 hlogYpos.le
    have e3 : Real.sqrt Y * Real.log Y * Real.log Y ≤ Real.sqrt Y * (16 * Real.sqrt Y) := by
      have h4 := mul_le_mul_of_nonneg_left hlogsq_le (Real.sqrt_nonneg (Y : ℝ))
      calc Real.sqrt Y * Real.log Y * Real.log Y = Real.sqrt Y * (Real.log Y * Real.log Y) := by
            ring
      _ ≤ Real.sqrt Y * (16 * Real.sqrt Y) := h4
    calc (Nat.sqrt Y : ℝ) * (Nat.log 2 Y : ℝ) * (Real.log 2 * Real.log Y)
        = (Nat.sqrt Y : ℝ) * ((Nat.log 2 Y : ℝ) * Real.log 2) * Real.log Y := by ring
    _ ≤ Real.sqrt Y * Real.log Y * Real.log Y := e2
    _ ≤ Real.sqrt Y * (16 * Real.sqrt Y) := e3
    _ = 16 * (Real.sqrt Y * Real.sqrt Y) := by ring
    _ = 16 * (Y : ℝ) := by rw [hYsq]
  have hfinal : (Nat.sqrt Y : ℝ) * (Nat.log 2 Y : ℝ) ≤ 16 / Real.log 2 * (Y : ℝ) / Real.log Y := by
    rw [show (16 : ℝ) / Real.log 2 * (Y : ℝ) / Real.log Y
        = 16 * (Y : ℝ) / (Real.log 2 * Real.log Y) by field_simp]
    rw [le_div_iff₀ (mul_pos hlog2pos hlogYpos)]
    exact hstep
  have hS2card : (S2.card : ℝ) ≤ 16 / Real.log 2 * (Y : ℝ) / Real.log Y :=
    hS2card_nat.trans hfinal
  calc (S.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := hScard
  _ ≤ C1 * (Y : ℝ) / Real.log Y + 16 / Real.log 2 * (Y : ℝ) / Real.log Y := by
      linarith [hS1card, hS2card]
  _ = (C1 + 16 / Real.log 2) * (Y : ℝ) / Real.log Y := by ring

end Erdos289
