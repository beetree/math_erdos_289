import Erdos289.Defs

/-!
# Erdős Problem 289: ported elementary lemmas from the expert starter

This file ports the elementary, self-contained lemmas of the uncompiled starter
kit in `expert_input/starter/erdos289_lean/Erdos289/{Intervals,PowerSmooth,
Padding,Cancellation}.lean` to our own `Iv`, `w`, `mass`, and `Powersmooth`
definitions from `Erdos289.Defs`, and to the Mathlib version pinned by this
project. `OpenObligations.lean` is skipped: its content is already covered by
`lemma1`, `lemma3`, and `liu_sawhney` elsewhere in this project.
-/

namespace Erdos289

open Finset

/-! ## Intervals -/

namespace Iv

/-- Length of an interval, i.e. the number of integers it contains. -/
def length (I : Iv) : ℕ := I.hi + 1 - I.lo

/-- The interval as a `Finset` of the integers it contains. -/
def carrier (I : Iv) : Finset ℕ := Finset.Icc I.lo I.hi

/-- Ordered separation: `I` entirely precedes `J`, with at least one integer
omitted in between. This is one of the two disjuncts of the symmetric `Sep`. -/
def Separated (I J : Iv) : Prop := I.hi + 1 < J.lo

theorem Separated.sep {I J : Iv} (h : Separated I J) : Sep I J := Or.inl h

theorem sep_iff {I J : Iv} : Sep I J ↔ Separated I J ∨ Separated J I := Iff.rfl

@[simp] theorem length_pair (a : ℕ) : (pair a).length = 2 := by
  simp only [length, pair]; omega

@[simp] theorem length_triple (a : ℕ) : (triple a).length = 3 := by
  simp only [length, triple]; omega

theorem mass_pair (a : ℕ) : (pair a).mass = w a := Erdos289.mass_pair a

theorem mass_triple (a : ℕ) : (triple a).mass = 1 / a + w (a + 1) := Erdos289.mass_triple a

/-- Extending `[a+1,a+2]` to `[a,a+2]` adds exactly `1/a`. -/
theorem mass_extend_pair (a : ℕ) :
    (triple a).mass = (pair (a + 1)).mass + 1 / a := by
  rw [mass_triple, mass_pair]; ring

/-- A start gap of three is exactly sufficient for nonadjacent two-term blocks. -/
theorem pair_separated_iff (a b : ℕ) : Separated (pair a) (pair b) ↔ a + 3 ≤ b := by
  simp only [Separated, pair]; omega

/-- Distinct increasing multiples of four leave two unused integers between
the corresponding pairs. -/
theorem pairs_separated_of_four_dvd_lt {a b : ℕ} (ha : 4 ∣ a) (hb : 4 ∣ b) (hab : a < b) :
    Separated (pair a) (pair b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  rw [pair_separated_iff]
  omega

theorem triples_separated_of_four_le {a b : ℕ} (h : a + 4 ≤ b) :
    Separated (triple a) (triple b) := by
  simp only [Separated, triple]; omega

/-- Core triples at starts `K*d` stay separated when `K ≥ 4`. -/
theorem core_triples_separated {K d e : ℕ} (hK : 4 ≤ K) (hde : d < e) :
    Separated (triple (K * d)) (triple (K * e)) := by
  apply triples_separated_of_four_le
  have hsucc : d + 1 ≤ e := by omega
  have hmul : K * (d + 1) ≤ K * e := Nat.mul_le_mul_left K hsucc
  nlinarith

/-- Subintervals inherit the separation of their containing intervals. -/
theorem separated_of_subintervals {I J I' J' : Iv}
    (h : Separated I J) (hI : I'.hi ≤ I.hi) (hJ : J.lo ≤ J'.lo) :
    Separated I' J' := by
  unfold Separated at *
  omega

theorem disjoint_carrier_of_separated {I J : Iv} (h : Separated I J) :
    Disjoint I.carrier J.carrier := by
  apply Finset.disjoint_left.mpr
  intro n hnI hnJ
  have hI := (Finset.mem_Icc.mp hnI).2
  have hJ := (Finset.mem_Icc.mp hnJ).1
  unfold Separated at h
  omega

/-- Concrete regression example for the statement mismatch: `[4,5]` and `[6,7]`
have disjoint carriers but are not `Sep`-separated (no integer is omitted
between them), so disjointness of carriers is strictly weaker than `Sep`. -/
theorem adjacency_allowed_is_strictly_weaker :
    Disjoint (pair 4).carrier (pair 6).carrier ∧ ¬ Sep (pair 4) (pair 6) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro n hn4 hn6
    simp only [carrier, pair, Finset.mem_Icc] at hn4 hn6
    omega
  · simp only [Sep, pair]
    omega

end Iv

/-- General comparison target for Problem 289: `k` intervals, each of length at
least two, contained in `[1, C*k]`, pairwise separated in the ordered sense for
`i < j`, with total reciprocal mass `1`. This drops the length-at-most-three
restriction of `GoodFamily`/`Statement` and allows an arbitrary bound
coefficient `C`, matching the general form used to compare against the
candidate theorem. -/
structure Problem289WitnessIv (C k : ℕ) where
  intervals : Fin k → Iv
  positive : ∀ i, 1 ≤ (intervals i).lo
  length_at_least_two : ∀ i, (intervals i).lo + 1 ≤ (intervals i).hi
  separated : ∀ i j, i < j → Iv.Separated (intervals i) (intervals j)
  bounded : ∀ i, (intervals i).hi ≤ C * k
  total_mass : ∑ i, (intervals i).mass = 1

/-- `Statement k` only asserts separation between *consecutive* indices; here we
show the left endpoints `a` are forced to be strictly increasing, which upgrades
the consecutive separation to separation for every pair `i < j`, giving a
`Problem289WitnessIv 20 k`. -/
theorem Statement.problem289Iv {k : ℕ} (h : Statement k) :
    Nonempty (Problem289WitnessIv 20 k) := by
  obtain ⟨a, b, h1, hab, hbound, hlen, hstep, hsum⟩ := h
  have main : ∀ n, ∀ i : Fin k, i.val < n → ∀ hn : n < k, b i + 1 < a ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro i hin hnk
      rcases Nat.lt_or_ge (i.val + 1) n with hgt | hle
      · have hn'k : n - 1 < k := by omega
        have hIH : b i + 1 < a ⟨n - 1, hn'k⟩ := IH (n - 1) (by omega) i (by omega) hn'k
        have hstep' : b (⟨n - 1, hn'k⟩ : Fin k) + 1 < a ⟨n, hnk⟩ :=
          hstep ⟨n - 1, hn'k⟩ ⟨n, hnk⟩ (by show n - 1 + 1 = n; omega)
        have hab' : a (⟨n - 1, hn'k⟩ : Fin k) ≤ b (⟨n - 1, hn'k⟩ : Fin k) := hab _
        omega
      · have heq : i.val + 1 = n := by omega
        exact hstep i ⟨n, hnk⟩ heq
  have hsep : ∀ i j : Fin k, i < j → b i + 1 < a j := by
    intro i j hij
    have hij' : i.val < j.val := hij
    simpa using main j.val i hij' j.isLt
  refine ⟨⟨fun i => (⟨a i, b i⟩ : Iv), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i; exact h1 i
  · intro i; show a i + 1 ≤ b i; have h2 := hlen i; have h3 := hab i; omega
  · intro i j hij; exact hsep i j hij
  · intro i; exact hbound i
  · exact hsum

/-! ## Powersmoothness -/

/-- Increasing the cutoff preserves powersmoothness. -/
theorem Powersmooth.mono {y z n : ℕ} (h : Powersmooth y n) (hyz : y ≤ z) :
    Powersmooth z n := by
  intro p e hp he hpe
  exact le_trans (h p e hp he hpe) hyz

/-- A divisor inherits every bound on prime-power divisors. -/
theorem Powersmooth.of_dvd {y m n : ℕ} (h : Powersmooth y n) (hmn : m ∣ n) :
    Powersmooth y m := by
  intro p e hp he hpe
  exact h p e hp he (hpe.trans hmn)

/-- Positive integers at most the cutoff are powersmooth. -/
theorem powersmooth_of_le {y n : ℕ} (hn : 0 < n) (hny : n ≤ y) : Powersmooth y n := by
  intro p e _ _ hpe
  exact le_trans (Nat.le_of_dvd hn hpe) hny

/-- Bridge to the starter's `PowerSmooth` formulation, quantifying over all
prime-power divisors rather than over `(p, e)` pairs. -/
theorem Powersmooth.iff_isPrimePow {y n : ℕ} :
    Powersmooth y n ↔ ∀ r : ℕ, IsPrimePow r → r ∣ n → r ≤ y := by
  constructor
  · intro h r hr hrn
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff r).mp hr
    exact h p e hp he hrn
  · intro h p e hp he hpe
    exact h (p ^ e) ((isPrimePow_nat_iff (p ^ e)).mpr ⟨p, e, hp, he, rfl⟩) hpe

/-- Powersmoothness is not closed under multiplication: both factors satisfy
cutoff four, while their product sixteen does not. -/
theorem powersmooth_multiplication_counterexample :
    Powersmooth 4 4 ∧ ¬ Powersmooth 4 16 := by
  constructor
  · exact powersmooth_of_le (by norm_num) (by norm_num)
  · intro h
    have h16 : IsPrimePow (16 : ℕ) :=
      (isPrimePow_nat_iff 16).mpr ⟨2, 4, by norm_num, by norm_num, by norm_num⟩
    have hbad : (16 : ℕ) ≤ 4 := (Powersmooth.iff_isPrimePow.mp h) 16 h16 (by norm_num)
    norm_num at hbad

/-! ## Finite predetermined-count padding -/

/-- If actual correction uses at most the stage budget, enough disjoint reserved
objects allow the stage to be filled to exactly that budget. -/
theorem exists_exact_padding {α : Type*} [DecidableEq α]
    (actual pool : Finset α) (s : ℕ)
    (hdis : Disjoint actual pool)
    (hactual : actual.card ≤ s) (hpool : s ≤ pool.card) :
    ∃ pad : Finset α, pad ⊆ pool ∧ Disjoint actual pad ∧
      pad.card = s - actual.card ∧ (actual ∪ pad).card = s := by
  have hneed : s - actual.card ≤ pool.card :=
    le_trans (Nat.sub_le s actual.card) hpool
  obtain ⟨pad, hsub, hcard⟩ := Finset.exists_subset_card_eq hneed
  have hdis' : Disjoint actual pad := hdis.mono_right hsub
  refine ⟨pad, hsub, hdis', hcard, ?_⟩
  rw [Finset.card_union_of_disjoint hdis', hcard]
  omega

/-- A property possessed by all reserved objects survives the padding choice. -/
theorem padding_preserves_property {α : Type*}
    (pool pad : Finset α) (P : α → Prop)
    (hsub : pad ⊆ pool) (hpool : ∀ a ∈ pool, P a) :
    ∀ a ∈ pad, P a := by
  intro a ha
  exact hpool a (hsub ha)

/-- Exact stage sizes sum to a count independent of the actual cancellation
choices. Stages include labels absent from the current denominator. -/
theorem scheduled_count {ι : Type*} (stages : Finset ι) (s c : ι → ℕ)
    (hc : ∀ q ∈ stages, c q ≤ s q) :
    (∑ q ∈ stages, (c q + (s q - c q))) = ∑ q ∈ stages, s q := by
  apply Finset.sum_congr rfl
  intro q hq
  have h := hc q hq
  omega

/-- The algebra behind the final number of intervals, with the necessary
non-truncation bound on natural subtraction stated explicitly. -/
theorem final_interval_count (k R C : ℕ) (h : R + C ≤ k) :
    (k - R - C) + R + C = k := by
  omega

/-- A stage whose two families both have per-pair cost at most `w` retains the
same `s*w` bound after filling the slots; there is no extra factor of two. -/
theorem padded_stage_cost {s c : ℕ} {w actualCost padCost : ℝ}
    (hc : c ≤ s) (ha : actualCost ≤ (c : ℝ) * w)
    (hp : padCost ≤ ((s - c : ℕ) : ℝ) * w) :
    actualCost + padCost ≤ (s : ℝ) * w := by
  have hcast : (c : ℝ) + ((s - c : ℕ) : ℝ) = (s : ℝ) := by
    exact_mod_cast (show c + (s - c) = s by omega)
  calc
    actualCost + padCost ≤ (c : ℝ) * w + ((s - c : ℕ) : ℝ) * w := add_le_add ha hp
    _ = ((c : ℝ) + ((s - c : ℕ) : ℝ)) * w := by ring
    _ = (s : ℝ) * w := by rw [hcast]

/-- A global mass budget guarantees positivity at every partial correction
stage; positivity is a separate hypothesis from modular cancellation. -/
theorem residual_positive {r cost budget : ℚ}
    (hcost : cost ≤ budget) (hbudget : budget < r) : 0 < r - cost := by
  linarith

/-- Integer common-denominator completion adds exactly the missing mass. -/
theorem exact_mass_completion (mass residual : ℚ)
    (h : residual = 1 - mass) : mass + residual = 1 := by
  linarith

/-! ## Elementary denominator cancellation -/

/-- Multiplying a correction pair's mass by its distinguished factor. -/
theorem q_mul_w (q m : ℕ) (hq : 0 < q) (hm : 0 < m) :
    (q : ℚ) * w (q * m) = 1 / (m : ℚ) + (q : ℚ) / ((q : ℚ) * (m : ℚ) + 1) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hqm : (q : ℚ) * (m : ℚ) + 1 ≠ 0 := by positivity
  unfold w
  push_cast
  field_simp [hq', hm', hqm]

/-- An integer quotient witness gives the corresponding rational identity. -/
theorem rational_quotient_of_mul_eq (a D : ℕ) (z : ℤ) (ha : 0 < a)
    (hz : (a : ℤ) * z = (D : ℤ)) :
    (D : ℚ) / (a : ℚ) = (z : ℚ) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  apply (div_eq_iff ha').2
  have hz' : (a : ℚ) * (z : ℚ) = (D : ℚ) := by exact_mod_cast hz
  simpa [mul_comm] using hz'.symm

/-- Explicit common-denominator identity for one finite correction step.

Here `V`, `A m`, and `B m` witness the integer quotients `D/v`, `D/m`,
and `D/(q*m+1)`, respectively. Existence of these witnesses is exactly the
relevant common-denominator divisibility assertion. The numerator must be
grouped with explicit parentheses: `u * V - (∑ m ∈ S, A m) - (q : ℤ) * (∑ m ∈ S, B m)`,
since without them the leading sum binder would absorb the following
subtraction. -/
theorem correction_common_denominator
    (q v D : ℕ) (u V : ℤ) (S : Finset ℕ) (A B : ℕ → ℤ)
    (hq : 0 < q) (hv : 0 < v)
    (hm : ∀ m ∈ S, 0 < m)
    (hV : (v : ℤ) * V = (D : ℤ))
    (hA : ∀ m ∈ S, (m : ℤ) * A m = (D : ℤ))
    (hB : ∀ m ∈ S, ((q * m + 1 : ℕ) : ℤ) * B m = (D : ℤ)) :
    (q : ℚ) * (D : ℚ) *
        ((u : ℚ) / ((q : ℚ) * (v : ℚ)) - ∑ m ∈ S, w (q * m)) =
      ((u * V - (∑ m ∈ S, A m) - (q : ℤ) * (∑ m ∈ S, B m) : ℤ) : ℚ) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hv)
  have hV' := rational_quotient_of_mul_eq v D V hv hV
  have hu : (q : ℚ) * (D : ℚ) * ((u : ℚ) / ((q : ℚ) * (v : ℚ))) =
      (u : ℚ) * (V : ℚ) := by
    rw [← hV']
    field_simp [hq', hv']
  have hp : ∀ m ∈ S,
      (q : ℚ) * (D : ℚ) * w (q * m) =
        (A m : ℚ) + (q : ℚ) * (B m : ℚ) := by
    intro m hmem
    have hA' := rational_quotient_of_mul_eq m D (A m) (hm m hmem) (hA m hmem)
    have hB' := rational_quotient_of_mul_eq (q * m + 1) D (B m)
      (Nat.zero_lt_succ _) (hB m hmem)
    calc
      (q : ℚ) * (D : ℚ) * w (q * m) =
          (D : ℚ) * ((q : ℚ) * w (q * m)) := by ring
      _ = (D : ℚ) * (1 / (m : ℚ) +
          (q : ℚ) / ((q : ℚ) * (m : ℚ) + 1)) := by
        rw [q_mul_w q m hq (hm m hmem)]
      _ = (D : ℚ) / (m : ℚ) +
          (q : ℚ) * ((D : ℚ) / ((q * m + 1 : ℕ) : ℚ)) := by
        push_cast
        ring
      _ = (A m : ℚ) + (q : ℚ) * (B m : ℚ) := by rw [hA', hB']
  calc
    (q : ℚ) * (D : ℚ) *
        ((u : ℚ) / ((q : ℚ) * (v : ℚ)) - ∑ m ∈ S, w (q * m)) =
        (u : ℚ) * (V : ℚ) - ∑ m ∈ S, ((A m : ℚ) + (q : ℚ) * (B m : ℚ)) := by
      rw [mul_sub, hu, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl hp
    _ = ((u * V - (∑ m ∈ S, A m) - (q : ℤ) * (∑ m ∈ S, B m) : ℤ) : ℚ) := by
      push_cast
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- If the cleared numerator is divisible by the whole factor `q`, that whole
factor cancels. The conclusion gives a denominator `D`, without any factor of
`q` left over; this is stronger than cancellation of just its underlying prime. -/
theorem cancel_full_factor (q D : ℕ) (r : ℚ) (N : ℤ)
    (hq : 0 < q) (hD : 0 < D)
    (hclear : (q : ℚ) * (D : ℚ) * r = (N : ℚ))
    (hdiv : (q : ℤ) ∣ N) :
    ∃ z : ℤ, r = (z : ℚ) / (D : ℚ) := by
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z, ?_⟩
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  apply (eq_div_iff hD').2
  have hz' : (N : ℚ) = (q : ℚ) * (z : ℚ) := by exact_mod_cast hz
  have heq : (q : ℚ) * ((D : ℚ) * r) = (q : ℚ) * (z : ℚ) := by
    simpa [mul_assoc, hz'] using hclear
  have hc := mul_left_cancel₀ hq' heq
  simpa [mul_comm] using hc

/-- The inverse-covering congruence, after clearing the invertible denominators,
is exactly the first divisibility hypothesis below. The second portion of the
mass already has a factor `q`, so it does not affect that congruence. -/
theorem correction_numerator_dvd (q : ℕ) (u V : ℤ)
    (S : Finset ℕ) (A B : ℕ → ℤ)
    (hresidue : (q : ℤ) ∣ u * V - (∑ m ∈ S, A m)) :
    (q : ℤ) ∣ u * V - (∑ m ∈ S, A m) - (q : ℤ) * (∑ m ∈ S, B m) := by
  apply dvd_sub hresidue
  exact ⟨∑ m ∈ S, B m, rfl⟩

/-- One algebraic absorption step removes the complete distinguished factor
from an available common denominator. The analytic covering theorem will
supply `S` and `hresidue`; it is not assumed or formalized here. -/
theorem correction_cancels_with_divisible_numerator
    (q v D : ℕ) (u V : ℤ) (S : Finset ℕ) (A B : ℕ → ℤ)
    (hq : 0 < q) (hv : 0 < v) (hD : 0 < D)
    (hm : ∀ m ∈ S, 0 < m)
    (hV : (v : ℤ) * V = (D : ℤ))
    (hA : ∀ m ∈ S, (m : ℤ) * A m = (D : ℤ))
    (hB : ∀ m ∈ S, ((q * m + 1 : ℕ) : ℤ) * B m = (D : ℤ))
    (hresidue : (q : ℤ) ∣ u * V - (∑ m ∈ S, A m)) :
    ∃ z : ℤ,
      (u : ℚ) / ((q : ℚ) * (v : ℚ)) - ∑ m ∈ S, w (q * m) =
        (z : ℚ) / (D : ℚ) := by
  exact cancel_full_factor q D _ _ hq hD
    (correction_common_denominator q v D u V S A B hq hv hm hV hA hB)
    (correction_numerator_dvd q u V S A B hresidue)

/-- A representation whose denominator has no factor `p`. This definition does
not impose a choice of reduced fraction and needs no primality hypothesis. -/
def HasPrimeFreeDenominator (p : ℕ) (r : ℚ) : Prop :=
  ∃ (z : ℤ) (D : ℕ), 0 < D ∧ ¬ p ∣ D ∧ r = (z : ℚ) / (D : ℚ)

/-- Clearing a numerator divisible by all of `q` preserves a denominator with
no factor `p`, if the chosen remaining common denominator has that property.
In the application `q = p^a`; no exponent-one cancellation is substituted. -/
theorem cancel_full_factor_prime_free (q D p : ℕ) (r : ℚ) (N : ℤ)
    (hq : 0 < q) (hD : 0 < D) (hpD : ¬ p ∣ D)
    (hclear : (q : ℚ) * (D : ℚ) * r = (N : ℚ))
    (hdiv : (q : ℤ) ∣ N) :
    HasPrimeFreeDenominator p r := by
  obtain ⟨z, hz⟩ := cancel_full_factor q D r N hq hD hclear hdiv
  exact ⟨z, D, hD, hpD, hz⟩

end Erdos289
