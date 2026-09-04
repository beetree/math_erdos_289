import Erdos289.Defs
import Erdos289.DenBound
import Erdos289.Cancel
import Erdos289.Lemma1
import Erdos289.Lemma2
import Erdos289.Lemma3
import Erdos289.Lemma5

/-!
# Section 4: the correction procedure with a predetermined number of pairs

Given an initial deficit whose reduced denominator only has prime powers at most `H`, visit
every prime power `q ∈ (L, H]` in decreasing order. At stage `q` the full power `q` (if present)
is cancelled using `c_q ≤ s(q)` correction pairs `[qm, qm+1]` with `m` in the Lemma 1 fiber
`I_q` (Lemma 3 supplies the required congruence), and then `s(q) - c_q` auxiliary pairs from
`F_q` are added. Each stage adds exactly `s(q)` pairs, the invariant "no prime power `≥ q` in
the denominator" is restored, and after all stages the denominator only has prime powers at
most `L`.
-/

namespace Erdos289

open Finset

/-- The predetermined number of correction intervals `C_H = ∑_{L < q ≤ H, q prime power} s(q)`. -/
noncomputable def CH (L H : ℕ) : ℕ := ∑ q ∈ (Icc (L + 1) H).filter IsPrimePow, s q

/-- The data fixed once and for all before `k` is chosen: a cutoff `L`, an auxiliary family,
and, for every prime power `q > L`, a Lemma 1 fiber `I_q` (with `ε = 1/10`) that is large enough
for Lemma 3 to apply. -/
structure CorrectionData where
  L : ℕ
  A : AuxFamily L
  /-- The fiber `I_q` of Lemma 1 (indexed by the prime power `q`). -/
  I : ℕ → Finset ℕ
  I_range : ∀ q, IsPrimePow q → L < q →
    ∀ m ∈ I q, (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10)
  I_coprime : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, Nat.Coprime m q
  I_four : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, 4 ∣ q * m
  I_smooth : ∀ q, IsPrimePow q → L < q → ∀ m ∈ I q, Powersmooth (q / 2) (q * m + 1)
  /-- Lemma 3 applies to `I_q`: every residue is a short sum of inverses. -/
  I_cover : ∀ q, IsPrimePow q → L < q → ∀ r : ZMod q,
    ∃ S ⊆ I q, S.card ≤ s q ∧ ∑ i ∈ S, ((i : ZMod q)⁻¹) = r

/-- **The correction procedure** (Section 4). For correction data `C` with cutoff `L`, every
`H > L`, and every deficit `r₀` with `DenBound H r₀`, there is a finset `P` of pairs such that:
* `|P| = C_H` exactly;
* every pair in `P` is a correction pair `[qm, qm+1]` with `m ∈ I_q` or an auxiliary pair from
  `F_q`, for some prime power `q ∈ (L, H]`; in particular both endpoints lie in `U`;
* every pair starts at a multiple of `4` and ends at most `2 H^{11/10} + 1`;
* the pairs are mutually separated;
* the total mass is at most `40 L^{-1/20}`;
* the corrected deficit `r₀ - ∑ mass` has `DenBound L`. -/
theorem descent (C : CorrectionData) (H : ℕ) (hH : C.L < H) (r₀ : ℚ) (hr₀ : DenBound H r₀) :
    ∃ P : Finset Iv,
      P.card = CH C.L H ∧
      (∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ H ∧
        ((∃ m ∈ C.I q, I = Iv.pair (q * m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a))) ∧
      (∀ I ∈ P, I.lo ∈ U C.L C.A ∧ I.hi ∈ U C.L C.A) ∧
      (∀ I ∈ P, 4 ∣ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 2 * (H : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
      ((∑ I ∈ P, I.mass : ℚ) : ℝ) ≤ 40 * (C.L : ℝ) ^ (-(1 : ℝ) / 20) ∧
      DenBound C.L (r₀ - ∑ I ∈ P, I.mass) := by
  sorry

/-- **(4.8)**: `C_H ≤ H^{21/20}`. -/
theorem CH_le (L H : ℕ) : (CH L H : ℝ) ≤ (H : ℝ) ^ ((21 : ℝ) / 20) := by
  sorry

end Erdos289
