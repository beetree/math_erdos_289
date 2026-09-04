import Mathlib

/-!
# The nonadjacent formulation of Erdős Problem 289

This file specifies the target and proves elementary interval facts. It does not
assert the candidate theorem: `CandidateStatement` and `Problem289Statement` are
definitions of propositions, not axioms or proved theorems.

The initial source draft has not yet been checked by a Lean executable; the
project build is the authority on whether these proof scripts elaborate.

An interval has inclusive natural-number endpoints. Nonadjacency is the strict
condition `left.hi + 1 < right.lo`, so at least one integer is omitted between
successive intervals.
-/

open scoped BigOperators

namespace Erdos289

/-- An integer interval with inclusive endpoints. Empty intervals are permitted
at this raw-data level and excluded by the hypotheses of the witnesses below. -/
structure NatInterval where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

namespace NatInterval

def carrier (I : NatInterval) : Finset ℕ := Finset.Icc I.lo I.hi

def length (I : NatInterval) : ℕ := I.hi + 1 - I.lo

/-- Reciprocal mass is rational and hence exact. Positive endpoints in a witness
exclude zero; Lean's totalized division is not relied on to admit denominator 0. -/
def mass (I : NatInterval) : ℚ := ∑ n ∈ I.carrier, (1 : ℚ) / (n : ℚ)

/-- Ordered separation with at least one omitted integer. -/
def Separated (I J : NatInterval) : Prop := I.hi + 1 < J.lo

/-- The weaker condition in the former adjacency-allowed draft. -/
def DisjointOrdered (I J : NatInterval) : Prop := I.hi < J.lo

def pair (a : ℕ) : NatInterval := ⟨a, a + 1⟩

def triple (a : ℕ) : NatInterval := ⟨a, a + 2⟩

@[simp] theorem pair_lo (a : ℕ) : (pair a).lo = a := rfl
@[simp] theorem pair_hi (a : ℕ) : (pair a).hi = a + 1 := rfl
@[simp] theorem triple_lo (a : ℕ) : (triple a).lo = a := rfl
@[simp] theorem triple_hi (a : ℕ) : (triple a).hi = a + 2 := rfl

@[simp] theorem length_pair (a : ℕ) : (pair a).length = 2 := by
  simp only [length, pair]
  omega

@[simp] theorem length_triple (a : ℕ) : (triple a).length = 3 := by
  simp only [length, triple]
  omega

theorem carrier_pair (a : ℕ) : (pair a).carrier = {a, a + 1} := by
  ext n
  simp only [carrier, pair, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem carrier_triple (a : ℕ) : (triple a).carrier = {a, a + 1, a + 2} := by
  ext n
  simp only [carrier, triple, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem mass_pair (a : ℕ) :
    (pair a).mass = (1 : ℚ) / a + (1 : ℚ) / (a + 1 : ℕ) := by
  have h : a ≠ a + 1 := by omega
  simp [mass, carrier_pair, h]

theorem mass_triple (a : ℕ) :
    (triple a).mass =
      (1 : ℚ) / a + (1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + 2 : ℕ) := by
  have h₁ : a ≠ a + 1 := by omega
  have h₂ : a ≠ a + 2 := by omega
  have h₃ : a + 1 ≠ a + 2 := by omega
  simp [mass, carrier_triple, h₁, h₂, h₃, add_assoc]

/-- Extending `[a+1,a+2]` to `[a,a+2]` adds exactly `1/a`. -/
theorem mass_extend_pair (a : ℕ) :
    (triple a).mass = (pair (a + 1)).mass + (1 : ℚ) / a := by
  rw [mass_triple, mass_pair]
  push_cast
  ring

theorem separated_implies_disjointOrdered {I J : NatInterval}
    (h : I.Separated J) : I.DisjointOrdered J := by
  unfold Separated at h
  unfold DisjointOrdered
  omega

theorem disjoint_carrier_of_ordered {I J : NatInterval}
    (h : I.DisjointOrdered J) : Disjoint I.carrier J.carrier := by
  apply Finset.disjoint_left.mpr
  intro n hnI hnJ
  have hI := (Finset.mem_Icc.mp hnI).2
  have hJ := (Finset.mem_Icc.mp hnJ).1
  unfold DisjointOrdered at h
  omega

theorem disjoint_carrier_of_separated {I J : NatInterval}
    (h : I.Separated J) : Disjoint I.carrier J.carrier :=
  disjoint_carrier_of_ordered (separated_implies_disjointOrdered h)

/-- A start gap of three is exactly sufficient for nonadjacent two-term blocks. -/
theorem pair_separated_iff (a b : ℕ) :
    (pair a).Separated (pair b) ↔ a + 3 ≤ b := by
  simp only [Separated, pair]
  omega

theorem pairs_separated_of_three_le {a b : ℕ} (h : a + 3 ≤ b) :
    (pair a).Separated (pair b) := (pair_separated_iff a b).mpr h

theorem pairs_separated_of_four_le {a b : ℕ} (h : a + 4 ≤ b) :
    (pair a).Separated (pair b) := by
  apply pairs_separated_of_three_le
  omega

/-- Distinct increasing multiples of four leave two unused integers between
the corresponding pairs. -/
theorem pairs_at_four_multiples_separated {a b : ℕ} (h : a < b) :
    (pair (4 * a)).Separated (pair (4 * b)) := by
  apply pairs_separated_of_four_le
  omega

theorem pairs_separated_of_four_dvd {a b : ℕ}
    (ha : 4 ∣ a) (hb : 4 ∣ b) (hab : a < b) :
    (pair a).Separated (pair b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  apply pairs_at_four_multiples_separated
  omega

theorem triples_separated_of_four_le {a b : ℕ} (h : a + 4 ≤ b) :
    (triple a).Separated (triple b) := by
  simp only [Separated, triple]
  omega

/-- Core triples at starts `K*d` stay separated when `K ≥ 4`. -/
theorem core_triples_separated {K d e : ℕ} (hK : 4 ≤ K) (hde : d < e) :
    (triple (K * d)).Separated (triple (K * e)) := by
  apply triples_separated_of_four_le
  have hsucc : d + 1 ≤ e := by omega
  have hmul : K * (d + 1) ≤ K * e := Nat.mul_le_mul_left K hsucc
  nlinarith

/-- Subintervals inherit the separation of their containing intervals. -/
theorem separated_of_subintervals {I J I' J' : NatInterval}
    (h : I.Separated J) (hI : I'.hi ≤ I.hi) (hJ : J.lo ≤ J'.lo) :
    I'.Separated J' := by
  unfold Separated at *
  omega

/-- The omitted integer `I.hi+1` certifies the stronger separation condition. -/
theorem omitted_integer_between {I J : NatInterval} (h : I.Separated J) :
    I.hi < I.hi + 1 ∧ I.hi + 1 < J.lo ∧
      I.hi + 1 ∉ I.carrier ∧ I.hi + 1 ∉ J.carrier := by
  simp only [Separated] at h
  simp only [carrier, Finset.mem_Icc]
  omega

/-- Concrete regression test for the statement mismatch: these pairs are
disjoint, but no integer is omitted between them. -/
theorem adjacency_allowed_is_strictly_weaker :
    (pair 4).DisjointOrdered (pair 6) ∧
    Disjoint (pair 4).carrier (pair 6).carrier ∧
    ¬ (pair 4).Separated (pair 6) := by
  constructor
  · norm_num [DisjointOrdered, pair]
  constructor
  · exact disjoint_carrier_of_ordered (by norm_num [DisjointOrdered, pair])
  · norm_num [Separated, pair]

end NatInterval

/-- The proposed stronger theorem: exactly `k` ordered nonadjacent blocks, each
of length two or three, total reciprocal mass one, and denominators at most `20k`.
This structure records data and obligations; it supplies no existence proof. -/
structure FamilyWitness (k : ℕ) where
  intervals : Fin k → NatInterval
  positive : ∀ i, 1 ≤ (intervals i).lo
  short : ∀ i, (intervals i).hi = (intervals i).lo + 1 ∨
    (intervals i).hi = (intervals i).lo + 2
  separated : ∀ i j, i < j → (intervals i).Separated (intervals j)
  bounded : ∀ i, (intervals i).hi ≤ 20 * k
  total_mass : ∑ i, (intervals i).mass = 1

/-- The general linear-bound target drops the candidate's length upper bound and
allows an arbitrary fixed denominator-bound coefficient `C`. -/
structure Problem289Witness (C k : ℕ) where
  intervals : Fin k → NatInterval
  positive : ∀ i, 1 ≤ (intervals i).lo
  length_at_least_two : ∀ i, (intervals i).lo + 1 ≤ (intervals i).hi
  separated : ∀ i j, i < j → (intervals i).Separated (intervals j)
  bounded : ∀ i, (intervals i).hi ≤ C * k
  total_mass : ∑ i, (intervals i).mass = 1

def CandidateStatement : Prop :=
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Nonempty (FamilyWitness k)

def Problem289Statement : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Nonempty (Problem289Witness C k)

def FamilyWitness.toProblem289Witness {k : ℕ} (W : FamilyWitness k) :
    Problem289Witness 20 k where
  intervals := W.intervals
  positive := W.positive
  length_at_least_two := by
    intro i
    rcases W.short i with h | h <;> omega
  separated := W.separated
  bounded := W.bounded
  total_mass := W.total_mass

theorem candidate_implies_problem289 (h : CandidateStatement) : Problem289Statement := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨20, by norm_num, k₀, ?_⟩
  intro k hk
  obtain ⟨W⟩ := hk₀ k hk
  exact ⟨W.toProblem289Witness⟩

theorem FamilyWitness.length_two_or_three {k : ℕ} (W : FamilyWitness k) (i : Fin k) :
    (W.intervals i).length = 2 ∨ (W.intervals i).length = 3 := by
  rcases W.short i with h | h
  · left
    unfold NatInterval.length
    omega
  · right
    unfold NatInterval.length
    omega

theorem FamilyWitness.pairwise_disjoint {k : ℕ} (W : FamilyWitness k) :
    Pairwise (fun i j : Fin k => Disjoint (W.intervals i).carrier (W.intervals j).carrier) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact NatInterval.disjoint_carrier_of_separated (W.separated i j h)
  · exact (NatInterval.disjoint_carrier_of_separated (W.separated j i h)).symm

/-- Indexing by `Fin k` really gives `k` distinct intervals. -/
theorem FamilyWitness.intervals_injective {k : ℕ} (W : FamilyWitness k) :
    Function.Injective W.intervals := by
  intro i j hij
  by_contra hne
  have hlohi : (W.intervals j).lo ≤ (W.intervals j).hi := by
    rcases W.short j with h | h <;> omega
  rcases lt_or_gt_of_ne hne with h | h
  · have hsep := W.separated i j h
    rw [hij] at hsep
    unfold NatInterval.Separated at hsep
    omega
  · have hsep := W.separated j i h
    rw [hij] at hsep
    unfold NatInterval.Separated at hsep
    omega

theorem FamilyWitness.denominator_bounds {k : ℕ} (W : FamilyWitness k)
    {i : Fin k} {n : ℕ} (hn : n ∈ (W.intervals i).carrier) :
    1 ≤ n ∧ n ≤ 20 * k := by
  have hmem := Finset.mem_Icc.mp hn
  have hpositive := W.positive i
  have hbounded := W.bounded i
  omega

end Erdos289
