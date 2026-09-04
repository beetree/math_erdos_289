import Erdos289.Lemma3Basic

/-!
# Lemma 3: steps 4–5 (open)

The simultaneous-approximation / divisor-bound step (3.2), isolated for parallel work.
-/

set_option maxRecDepth 100000

namespace Erdos289

open Finset Filter Real Topology

/-- **Paper's steps 4–5, quantitative form (`(3.2)`).** For a proper GAP `P` representing `0`
via `v` and every `j ∈ J` (`J` a set of naturals `< q`, each with a small modular-inverse
witness `i j ≤ 2 q^ε`, `|J| ≥ q^(7ε/8)/2`), the active-coordinate count `d ≥ 1` and product
`V` of active extents satisfy `V ≥ q^(1 - dε/8 - dε/500) / (32d)^d`.

This packages the paper's simultaneous-approximation / divisor-bound argument (Section 3,
steps 4–5): apply `simultaneous_approx` to the active generators with box sizes
`B i := (4q/a i)(V/q)^(1/d)` (needing `V < q`, and, to control the pigeonhole box count
`∏ ⌈q/B i⌉₊ < q` when `d ≥ 2`, that `V/q` is already small — supplied in the application by
the face-counting bound `(3.1)`, which is *not* assumed here since this lemma is stated to
hold unconditionally for the actual `V`); then bound each `j`'s image under the resulting `T`
via `gap_active_repr`, and apply `divisor_count_bound`. Establishing the box-count / pigeonhole
inequality rigorously, uniformly over the finitely many `d ≤ d₀` and large `q`, needs a
careful case analysis (the naive per-coordinate ceiling bound is not uniform in the extents
`a i`; only the *product* `∏ a i = V` is controlled, so unbalanced extents need the dilate's
upper bound on `V` from `(3.1)` to control the pigeonhole box sizes) that was not completed in
the time available for this formalization round; it is isolated here as the one remaining
`sorry` in this file, stated as a self-contained, true real-analytic/combinatorial fact. -/
lemma paper_steps_4_5 (ε c : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (d₀ : ℕ) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, 2 ≤ q → Q₀ ≤ q →
      ∀ (P : GAP) (v : Fin P.D → ℤ) (J : Finset ℕ),
        P.D ≤ d₀ →
        (∀ i, P.α i ≤ (v i:ℝ) ∧ (v i:ℝ) ≤ P.β i) → (∑ i, v i * P.d i = 0) →
        (∀ j ∈ J, (j:ℤ) ∈ P.set) → (∀ j ∈ J, j < q) →
        (∀ j ∈ J, ∃ i : ℕ, 0 < i ∧ (i:ℝ) ≤ 2 * (q:ℝ)^ε ∧ (i:ZMod q) * (j:ZMod q) = 1) →
        (q:ℝ)^(7*ε/8) / 2 ≤ (J.card:ℝ) →
        1 ≤ (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card →
        ((∏ i ∈ Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋), (⌊P.β i⌋ - ⌈P.α i⌉).toNat : ℕ)
              : ℝ)
          ≥ (q:ℝ) ^ (1 - ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ) * ε / 8
                - ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ) * ε / 500)
            / (32 * ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ)) ^
                (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card := by
  sorry


end Erdos289
