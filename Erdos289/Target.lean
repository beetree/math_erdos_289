import Erdos289.Intervals
import Erdos289.Defs

/-!
# Erdős Problem 289: bridging our `Statement` to the audited target

This file connects `Statement k` (and the eventually-true form of it) to the
externally audited `FamilyWitness` and `CandidateStatement` from
`Erdos289.Intervals`.

`Erdos289.Expert` is not imported here: this file's proof of
`Statement.familyWitness` reimplements the consecutive-separation
induction from `Statement.problem289` directly, so it needs only `Defs`
and `Intervals`. (An earlier name collision between `Expert`'s witness
structure and the audited `Problem289Witness` in `Erdos289.Intervals` has
been resolved by renaming the former to `Problem289WitnessIv`; the root
module `Erdos289.lean` imports both files.)
-/

namespace Erdos289

/-- Our consecutive-separation statement yields the audited `FamilyWitness`. -/
theorem Statement.familyWitness {k : ℕ} (h : Statement k) : Nonempty (FamilyWitness k) := by
  obtain ⟨a, b, h1, hab, hbound, hlen, hstep, hsum⟩ := h
  -- Upgrade consecutive separation to separation for every pair `i < j`,
  -- exactly as in `Statement.problem289`.
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
  refine ⟨⟨fun i => (⟨a i, b i⟩ : NatInterval), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i; exact h1 i
  · intro i
    show b i = a i + 1 ∨ b i = a i + 2
    have h2 := hlen i
    have h3 := hab i
    omega
  · intro i j hij
    show b i + 1 < a j
    exact hsep i j hij
  · intro i; exact hbound i
  · show ∑ i, NatInterval.mass (⟨a i, b i⟩ : NatInterval) = 1
    have hmass : ∀ i, NatInterval.mass (⟨a i, b i⟩ : NatInterval) = mass (a i) (b i) := fun i => rfl
    rw [Finset.sum_congr rfl (fun i _ => hmass i)]
    exact hsum

/-- `∀ᶠ k, Statement k` yields the audited `CandidateStatement`. -/
theorem candidateStatement_of (h : ∀ᶠ k : ℕ in Filter.atTop, Statement k) : CandidateStatement := by
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨k₀, fun k hk => (hk₀ k hk).familyWitness⟩

end Erdos289
