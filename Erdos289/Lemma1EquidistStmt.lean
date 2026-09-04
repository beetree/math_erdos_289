import Erdos289.Lemma1Basic
import Erdos289.ExternalBridge
import Erdos289.Lemma1Equidist

/-!
# Lemma 1: the equidistribution statement

Proved in `Lemma1Equidist.lean` (namespace `Erdos289.Equidist`) from `bourgain_garaev` and
`erdos_turan`, following the author's blueprint; restated here in terms of `rOf`/`invCand`.
-/

namespace Erdos289

open Finset Filter Topology

/-- **Equidistribution of modular inverses** (paper §2): for a prime power `q = p^a`, a
modulus `U ∈ {q, 2q, 4q, 4pq}`, a prefix length `T ≤ 5 q^ε`, and a residue interval
`[α, α+ℓ) ⊆ [0, U)`, the count of `t ≤ T` coprime to `U` with `t⁻¹ mod U ∈ [α, α+ℓ)` matches
the expected count `φ(U)/U · T · ℓ/U` up to an error `o(q^ε)`, uniformly in all of the above.

The moduli `U` range over `q, 2q` in the even case and `4q, 4pq` in the odd case (`Erdos289`
paper, Section 2, "Here is the uniform discrepancy justification..."): for a fixed nonzero
Fourier frequency `h`, reduce to `U₀/(h,U₀)`, where `bourgain_garaev` applies since
`q/|h| ≤ U₀/(h,U₀) ≤ 4q²` and the underlying prime `p` remains a unit; `erdos_turan` then
converts the resulting bound on exponential sums into the discrepancy bound stated here. This
is an unproved external input, built from `bourgain_garaev` and `erdos_turan`. -/
theorem equidist_inverse (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → 0 < a → q = p ^ a →
      ∀ U : ℕ, U = q ∨ U = 2 * q ∨ U = 4 * q ∨ U = 4 * p * q →
        ∀ T₁ T₂ : ℕ, T₁ ≤ T₂ → (T₂ : ℝ) ≤ 5 * (q : ℝ) ^ ε →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |((invCand U T₁ T₂ α ℓ).card : ℝ)
                - (Nat.totient U : ℝ) / (U : ℝ) * (((T₂ - T₁ : ℕ) : ℝ)) * (ℓ : ℝ) / (U : ℝ)|
              ≤ κ * (q : ℝ) ^ ε := by
  have h := Equidist.equidist_inverse' ε hε0 hε1
  simpa [Equidist.invCand', Equidist.rOf', invCand, rOf] using h

end Erdos289
