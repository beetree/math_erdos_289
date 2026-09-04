/-
Shared identity between `Nat.primeCounting` and the cardinality of the prime
filter of `Finset.Icc 1 n`.

Other edges use it through `DisjointResidueFamilyExtremals.MertensBasic`,
and one further edge had proved the mirrored form independently under its
own namespace.  The declaration keeps its original name and namespace so
existing consumers are unaffected.
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace DisjointResidueFamilyExtremals

lemma primeCounting_eq_card_Icc_filter_prime (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card
        = ((Finset.range (n + 1)).filter Nat.Prime).card := by
          congr 1
          ext p
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
          constructor
          · rintro ⟨⟨_, hpn⟩, hp⟩
            exact ⟨hpn, hp⟩
          · rintro ⟨hpn, hp⟩
            exact ⟨⟨hp.one_le, hpn⟩, hp⟩
    _ = Nat.count Nat.Prime (n + 1) := (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
    _ = Nat.primeCounting n := rfl

end DisjointResidueFamilyExtremals
