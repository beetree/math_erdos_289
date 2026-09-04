import Erdos289.Lemma3Steps45
import Erdos289.Defs
import Erdos289.External

/-!
# Lemma 3: sparse modular inverse subsets cover all residues

For fixed `0 < ε < 1` and every sufficiently large prime power `q`: if
`I ⊆ [q^ε, 2q^ε]` consists of integers coprime to `q` and `|I| ≥ q^(7ε/8)`, then every residue
modulo `q` is a sum of inverses of at most `q^(ε/2)` distinct members of `I`.

Everything below is proved for an arbitrary fixed constant `C ≥ 1` in place of the `2`, and
with no lower endpoint restriction: `I ⊆ [1, C q^ε]` (`lemma3_wide`). `lemma3` itself is the
case `C = 2`. This is what the elementary replacement argument of
`docs/elementary_replacements.md` (Corollary C4) requires, its correction multipliers ranging
over `[R(q), 8 q^ε]`.

The proof follows Section 3 of `erdos_289_full_proof.pdf` ("Sparse modular inverse subsets
cover all residues"), a sparse extension of Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte,
Theorem 2. It is organized as a chain of lemmas mirroring the paper's argument:

* `simultaneous_approx`: the pigeonhole/simultaneous-approximation step (paper's step 4).
* `invVal_injOn`: the modular-inverse-value map is injective on `I` (paper's step 0).
* `exists_S_of_covering`: pulls the final conclusion back through that injective map from a
  "subset sums of `J'` cover every residue" statement (paper's step 6, final paragraph).
* `eventually_rpow_dominates`, `eventually_log_le_rpow`, `lemma3_growth_bounds`: the
  elementary but bookkeeping-heavy real-asymptotic inequalities needed to apply the external
  structure theorem for large `q` (paper's "For sufficiently large q, `q ≤ m^(2/ε)`,
  `m^(1/3) ≤ s ≤ cm/log m`").
* `lemma3_structure_apply`: instantiates `cfhmpsv_structure` (paper's step 1) and derives
  `|J| ≥ m/2` from the growth bounds.
* `ap_unit_covers`, `gap_active_repr`, `gap_active_nonempty`, `gap_dilate_face_count`,
  `gap_interval_count_ge`: reusable pieces of the additive-combinatorial core (paper's steps
  2, 3, and the final covering paragraph): coordinate extraction, existence of an active
  coordinate, the face-counting cardinality bound (3.1), and dilated-interval integer counts.
  These are proved in full.
* `divisor_count_bound`: the divisor-counting cardinality bound (paper's step 5), proved in
  full: pairing each `j` with a bounded witness and a small modular inverse embeds `J`
  injectively into boundedly many divisors of boundedly many integers.
* `paper_steps_4_5`: the quantitative form of the paper's steps 4–5 (simultaneous
  approximation + the divisor-bound argument, paper's (3.2)): the active-coordinate product
  `V` satisfies `V ≥ q^(1 - dε/8 - dε/500) / (16Cd)^d`. This is the one remaining `sorry` in
  the file — see its docstring for exactly what is missing (a uniform-in-`d ≤ d₀` pigeonhole
  box-count estimate) and what is proved instead (`hd1_and_big` inside `lemma3_core` derives
  the paper's `d = 1` dichotomy and the final quantitative bound on `V` from this one
  statement, in full, including all of the surrounding real-asymptotic bookkeeping).
* `lemma3_core`: assembles the pieces above into the full argument (paper's steps 2–6: active
  coordinates, face counting (3.1), the `d = 1` dichotomy, and the final covering conclusion).
  Every step is now proved in full except for the one `sorry` isolated inside
  `paper_steps_4_5` above (threaded in as a black box).

`lemma3` itself is assembled from these pieces with no further `sorry`.
-/

set_option maxRecDepth 100000

namespace Erdos289

open Finset Filter Real Topology

set_option maxHeartbeats 1000000 in
/-- **Steps 2–6** of the proof of Lemma 3 (the genuinely hard additive-combinatorial core).

Given the data supplied by `lemma3_structure_apply` for a large prime power `q` — a proper
GAP `P` of rank `≤ d₀` with `J ∪ {0} ⊆ P.set`, `|J| ≥ m/2` (`m` the ambient cardinality with
`q^(7ε/8) ≤ m`), all elements of `J` units mod `q`, `J' ⊆ J` with `|J'| ≤ s := ⌊q^(ε/2)⌋₊`,
and a translate `x + (c s) • P ⊆ subsetSums J'` — the conclusion is that the subset sums of
`J'` cover every residue class mod `q`.

This packages the remainder of the paper's argument (Section 3, from "Choose an integer
coordinate vector `v` representing `0` …" to the end of the proof):

* **Coordinates.** Pick an integer vector `v` representing `0` in `P`. Set `ℓ i = ⌈α i⌉`,
  `u i = ⌊β i⌋`. Call a coordinate *active* when `u i > ℓ i`; there is at least one active
  coordinate (since `P` contains `0` and the nonzero elements of `J`). Write `d` for the
  number of active coordinates, `a i = u i - ℓ i ≥ 1` for active `i`, and `V = ∏ a i` over
  active coordinates. Every `j ∈ J` is `∑ (n i - v i) * d i` over active `i`, with
  `|n i - v i| ≤ a i`.

* **Face counting (paper's (3.1)).** Fixing the inactive coordinates at any admissible value
  produces a face of the dilate `(c s) • P`; for each active coordinate the corresponding
  dilated interval contains at least `(c s / 2) * a i` integers, so the face has at least
  `(c s / 2) ^ d * V` points. These points are pairwise distinct (this needs the *dilate* to
  be proper — see the caveat below) and all lie in `subsetSums J' ⊆ [0, s * q]`
  (`Erdos289.subsetSums`), giving `(c s / 2) ^ d * V ≤ s * q + 1`, i.e.
  `V ≪_ε q * s ^ (1 - d)`.

* **Simultaneous approximation.** If `V < q`, apply `simultaneous_approx` (above) to the
  generators `d i` of the active coordinates with `B i := (4 q / a i) * (V / q) ^ (1/d)`,
  giving `1 ≤ T < q` and `e i ≡ T * d i (mod q)` with `|e i| ≤ B i`.

* **The divisor-bound argument (paper's (3.2)).** For `j ∈ J`, the centered representative of
  `T * j mod q` has size `≤ R := 4 d q (V/q)^(1/d)`. Pairing it with `i ∈ I` such that
  `j ≡ i⁻¹ (mod q)` produces `i * h = q * z + T` with `z` bounded and nonzero (`|i * h| ≤
  q^(1+ε)`); the divisor bound `Erdos289.divisor_bound` shows each `z` arises from at most
  `q^(o(1))` pairs `(i, h)`, so counting pairs against `|J| ≥ m/2` forces
  `V ≥ q^(1 - d ε / 8 - o(1))`. For `d ≥ 2` this contradicts the face-counting bound above
  (since `(d-1)ε/2 - dε/8 = (3d-4)ε/8 > 0`), forcing `d = 1`.

* **Conclusion when `d = 1`.** Every `j ∈ J` is then a multiple of the single active
  generator `d 1`; since these `j` are units mod `q`, so is `d 1`. The one-dimensional face
  of the dilate along this coordinate then has `≥ q^(1 + 3ε/8 - o(1)) > q` terms in arithmetic
  progression with common difference a unit mod `q`, hence covers every residue class mod
  `q`; each term is (by the translate hypothesis) a subset sum of `J'`, giving the stated
  conclusion.

**Caveat on the formalization of the external input.** The face-counting step needs the
*dilate* `(c s) • P`, not merely `P`, to be proper: distinct admissible coordinate vectors in
a face of the dilate must give distinct values, and properness of `P` (injectivity on the
*unscaled* box `∏ [α i, β i]`) does not formally imply injectivity on the larger, rescaled box
`∏ [c s α i, c s β i]` that the dilate's coordinates range over. The paper's source
(Conlon–Fox–Pham, *Homogeneous structures in subset sums and non-averaging sets*, Theorem
1.5, as used in Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte, Theorem 3) does supply a proper
dilate, but `Erdos289.cfhmpsv_structure` in `Erdos289/External.lean` only records `P.Proper`
for the un-dilated `P`. Completing this lemma either needs `GAP.Proper` reformulated as a
scale-invariant notion (e.g. properness of every dilate, or properness stated directly for
coordinate differences `n - m` rather than for the coordinate box), or `cfhmpsv_structure`'s
conclusion strengthened to assert `(GAP.dilate (c * s) P).Proper` explicitly. This has now
been done: `cfhmpsv_structure` asserts properness of the dilate, and it is threaded through
as the hypothesis `(GAP.dilate (c * s) P).Proper` below.

**Further gaps discovered while formalizing this lemma (round 2).** Three additional facts,
each true in the *concrete* application (`lemma3_structure_apply`/`lemma3`) but not derivable
from `lemma3_core`'s hypotheses in the abstract, were needed: (1) the face-counting bound
`(3.1)` needs `subsetSums J'` confined to an interval of length `O(s q)`, which needs elements
of `J'` bounded by (roughly) `q`; (2) the divisor-count bound `(3.2)` needs, for each `j ∈ J`,
a bound `((j:ZMod q)⁻¹).val ≤ C q^ε`; (3) the face-counting construction needs, for each
inactive coordinate, an admissible *integer* point in the dilated (real-valued) interval
`[t α i, t β i]`. All three are now resolved (round 3) by adding the hypotheses `hJlt`,
`hJsmall`, and threading `(GAP.dilate (c * s) P).set.Nonempty` (`hPne`) through from
`cfhmpsv_structure`, matching what the concrete application actually supplies.

**Remaining gap (round 3).** The quantitative form of the paper's steps 4–5 (simultaneous
approximation combined with the divisor-bound argument, giving `(3.2)`) is isolated as the
lemma `paper_steps_4_5` above, with a single `sorry` inside it; seeing why (uniformly
controlling the multi-dimensional pigeonhole box count over `d ≤ d₀` needs the *actual*,
generator-dependent upper bound on `V` from `(3.1)`, not merely `V < q`) and what remains true
and provable is documented in that lemma's docstring. Every other step below — the coordinate
extraction, face counting `(3.1)` itself, the `d = 1` dichotomy derived from `paper_steps_4_5`
via a real-asymptotic argument uniform in `d ≤ d₀`, and the final one-dimensional covering
argument — is proved in full. -/
lemma lemma3_core (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 < c) (C : ℝ)
    (hC : 1 ≤ C) (d₀ : ℕ) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ (m : ℕ) (J J' : Finset ℕ) (P : GAP),
        P.Proper → (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊:ℝ)) P).Proper →
        (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊:ℝ)) P).set.Nonempty → P.D ≤ d₀ → J' ⊆ J →
        (m:ℝ)/2 ≤ (J.card:ℝ) →
        (∀ x ∈ J, (x:ℤ) ∈ P.set) → (0:ℤ) ∈ P.set →
        (∀ j ∈ J, IsUnit ((j:ℕ):ZMod q)) →
        (∀ j ∈ J, j < q) →
        (∀ j ∈ J, ∃ i : ℕ, 0 < i ∧ (i:ℝ) ≤ C * (q:ℝ)^ε ∧ (i:ZMod q) * (j:ZMod q) = 1) →
        J'.card ≤ ⌊(q:ℝ)^(ε/2)⌋₊ →
        (q:ℝ)^(7*ε/8) ≤ (m:ℝ) →
        (∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊:ℝ)) P).set, x + y ∈ subsetSums J') →
        ∀ r : ZMod q, ∃ T ⊆ J', ((∑ i ∈ T, (i:ℤ) : ℤ) : ZMod q) = r := by
  have hSbig : ∀ᶠ q:ℕ in atTop, max (2/c+1) 2 ≤ (q:ℝ)^(ε/2) := by
    have h2 : Tendsto (fun q:ℕ => (q:ℝ)^(ε/2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    exact h2.eventually_ge_atTop (max (2/c+1) 2)
  rw [eventually_atTop] at hSbig
  obtain ⟨Q₀, hQ₀⟩ := hSbig
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  obtain ⟨Q₁, hQ₁⟩ := paper_steps_4_5 ε c C hε0 hε1 hc hC d₀
  -- for the `d ≥ 2` rejection: `q` large enough that `q^(2·373ε/1000 - ε/2)` beats the
  -- constants arising from `(cs/2)^d ≥ (c/4)^d q^(dε/2)` combined with `(3.2)`, uniformly over
  -- `d ≤ d₀`.
  have hSbig2 : ∀ᶠ q:ℕ in atTop,
      (2:ℝ) * (64 * C * (d₀:ℝ) * (1 + 1/c)) ^ d₀ < (q:ℝ)^(123*ε/500) := by
    have h2 : Tendsto (fun q:ℕ => (q:ℝ)^(123*ε/500)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact h2.eventually_gt_atTop _
  -- for the `d = 1` conclusion: `q` large enough that `q^(373ε/1000)` beats `64C/c`.
  have hSbig3 : ∀ᶠ q:ℕ in atTop, (64:ℝ)*C/c < (q:ℝ)^(373*ε/1000) := by
    have h2 : Tendsto (fun q:ℕ => (q:ℝ)^(373*ε/1000)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact h2.eventually_gt_atTop _
  rw [eventually_atTop] at hSbig2 hSbig3
  obtain ⟨Q₂, hQ₂⟩ := hSbig2
  obtain ⟨Q₃, hQ₃⟩ := hSbig3
  refine ⟨max (max Q₀ Q₁) (max (max Q₂ Q₃) 2), fun q hqpp hq m J J' P hPproper hPdil hPne hPD
    hJ'J hJcard hJmem h0mem hunits hJlt hJsmall hJ'card hmcard hxdilate r => ?_⟩
  classical
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)
  have hqQ0 : Q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqQ1 : Q₁ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqQ2 : Q₂ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hq)
  have hqQ3 : Q₃ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hq)
  have hNZq : NeZero q := ⟨by omega⟩
  have hFact : Fact (1 < q) := ⟨by omega⟩
  set s : ℕ := ⌊(q:ℝ)^(ε/2)⌋₊ with hsdef
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0<q)
  have hQ₀' := hQ₀ q hqQ0
  have hqeps2c : 2/c + 1 ≤ (q:ℝ)^(ε/2) := le_trans (le_max_left _ _) hQ₀'
  have hqeps2 : (2:ℝ) ≤ (q:ℝ)^(ε/2) := le_trans (le_max_right _ _) hQ₀'
  have hspos : 2/c < (s:ℝ) := by
    have h2 : (q:ℝ)^(ε/2) < (s:ℝ)+1 := by rw [hsdef]; exact Nat.lt_floor_add_one _
    linarith
  have ht2 : (2:ℝ) ≤ c * (s:ℝ) := by
    have hh := (div_lt_iff₀ hc).mp hspos
    linarith
  have hs_ub : (s:ℝ) ≤ (q:ℝ)^(ε/2) := by rw [hsdef]; exact Nat.floor_le (by positivity)
  have hs_lb : (q:ℝ)^(ε/2)/2 ≤ (s:ℝ) := by
    have h2 : (q:ℝ)^(ε/2) < (s:ℝ)+1 := by rw [hsdef]; exact Nat.lt_floor_add_one _
    linarith [hqeps2]
  have hcs_lb : (c/4) * (q:ℝ)^(ε/2) ≤ c * (s:ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_left hs_lb hc.le
    linarith [this]
  -- coordinate setup
  obtain ⟨v, hv, hv0eq⟩ := h0mem
  have hv0 : ∑ i, v i * P.d i = 0 := hv0eq.symm
  set Active : Finset (Fin P.D) := Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋) with hActive
  -- nonzero element of J
  have hqpow_pos : (0:ℝ) < (q:ℝ)^(7*ε/8) := Real.rpow_pos_of_pos hqR _
  have hmpos : 0 < m := by
    have : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hqpow_pos hmcard
    exact_mod_cast this
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
  have hJcardR : (0:ℝ) < (J.card:ℝ) := lt_of_lt_of_le (by linarith) hJcard
  have hJcardpos : 0 < J.card := by exact_mod_cast hJcardR
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hJcardpos
  have hj₀ne : (j₀:ℤ) ≠ 0 := by
    intro h0
    have hu := hunits j₀ hj₀
    have h0' : j₀ = 0 := by exact_mod_cast h0
    rw [h0'] at hu
    simp only [Nat.cast_zero] at hu
    exact not_isUnit_zero hu
  have hActiveNE : Active.Nonempty :=
    gap_active_nonempty P v hv hv0 (j₀:ℤ) (hJmem j₀ hj₀) hj₀ne
  set d : ℕ := Active.card with hddef
  have hd1 : 1 ≤ d := Finset.card_pos.mpr hActiveNE
  set V : ℕ := ∏ i ∈ Active, (⌊P.β i⌋ - ⌈P.α i⌉).toNat with hVdef
  -- GAP 3: admissible inactive-coordinate assignment for the dilate (documented gap; see
  -- lemma3_core's docstring, item (3)).
  obtain ⟨w, hw⟩ : ∃ w : Fin P.D → ℤ, ∀ i, ¬ (⌈P.α i⌉ < ⌊P.β i⌋) →
      (c * (s:ℝ)) * P.α i ≤ (w i:ℝ) ∧ (w i:ℝ) ≤ (c * (s:ℝ)) * P.β i := by
    obtain ⟨y, n, hn, _⟩ := hPne
    exact ⟨n, fun i _ => hn i⟩
  -- GAP 1: elements of `J'` are bounded by `q` in the concrete application (see item (1)).
  have hJ'bound : ∀ z ∈ subsetSums J', (0:ℤ) ≤ z ∧ z ≤ (J'.card:ℤ) * q := by
    intro z hz
    obtain ⟨T, hTJ', hzeq⟩ := hz
    have hTJ : T ⊆ J := hTJ'.trans hJ'J
    have hnn : (0:ℤ) ≤ z := by
      rw [hzeq]
      exact Finset.sum_nonneg (fun i _ => by positivity)
    have hub : z ≤ (T.card:ℤ) * q := by
      rw [hzeq]
      calc ∑ i ∈ T, (i:ℤ) ≤ ∑ i ∈ T, (q:ℤ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiq : i < q := hJlt i (hTJ hi)
            exact_mod_cast hiq.le
        _ = (T.card:ℤ) * q := by rw [Finset.sum_const]; ring
    refine ⟨hnn, le_trans hub ?_⟩
    have : T.card ≤ J'.card := Finset.card_le_card hTJ'
    have hqnn : (0:ℤ) ≤ (q:ℤ) := by positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hqnn
  set x : ℤ := hxdilate.choose with hxdef
  have hxspec : ∀ y ∈ (GAP.dilate (c*(s:ℝ)) P).set, x + y ∈ subsetSums J' := hxdilate.choose_spec
  have hFace : (c * (s:ℝ) / 2) ^ d * (V:ℝ) ≤ (J'.card:ℤ) * q - 0 + 1 := by
    have := gap_dilate_face_count P (c * (s:ℝ)) ht2 hPdil w hw (subsetSums J') x 0
      ((J'.card:ℤ)*q) (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) hJ'bound hxspec
    simpa [hActive, hddef, hVdef] using this
  -- GAP 2 + steps 4–5 (simultaneous approximation, divisor-bound argument (3.2)), combined
  -- with the face-count bound `hFace` above (paper's (3.1)), to force `d = 1` and get a
  -- quantitative lower bound on `V` exceeding `q` after scaling by `s`. See lemma3_core's
  -- docstring, item (2), and Section 3 of the paper (steps 4–5).
  have hd1_and_big : d = 1 ∧ (c * (s:ℝ) / 2) * (V:ℝ) > q := by
    have hdd0 : d ≤ d₀ := by
      have h1 : Active.card ≤ Fintype.card (Fin P.D) := Finset.card_le_univ Active
      rw [Fintype.card_fin] at h1
      rw [hddef]; exact le_trans h1 hPD
    have hJcardbig : (q:ℝ)^(7*ε/8) / 2 ≤ (J.card:ℝ) := by linarith [hmcard, hJcard]
    have hd1' : 1 ≤ (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card := by
      rw [← hActive]; exact hd1
    have hVraw := hQ₁ q hq2 hqQ1 P v J hPD hv hv0 hJmem hJlt hJsmall hJcardbig hd1'
    have hVbound : (q:ℝ) ^ (1 - (d:ℝ)*ε/8 - (d:ℝ)*ε/500) / (16*C*(d:ℝ))^d ≤ (V:ℝ) := by
      simpa [hActive, hddef, hVdef] using hVraw
    have hFaceR : (c * (s:ℝ) / 2) ^ d * (V:ℝ) ≤ (s:ℝ)*(q:ℝ) + 1 := by
      have h1 : (J'.card:ℝ) ≤ (s:ℝ) := by exact_mod_cast hJ'card
      have h2 := hFace
      push_cast at h2
      nlinarith [h2, h1, hqR.le]
    have hpow_eq : ∀ n : ℕ, ((q:ℝ)^(ε/2))^n = (q:ℝ)^(ε/2 * n) := by
      intro n
      rw [← Real.rpow_natCast ((q:ℝ)^(ε/2)) n, ← Real.rpow_mul hqR.le]
    have hSQ : (s:ℝ)*(q:ℝ) + 1 ≤ 2*(q:ℝ)^(1+ε/2) := by
      have hqexp_ge1 : (1:ℝ) ≤ (q:ℝ)^(1+ε/2) := by
        have h1 : (q:ℝ)^(0:ℝ) ≤ (q:ℝ)^(1+ε/2) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ q)) (by linarith)
        rwa [Real.rpow_zero] at h1
      have hSQ1 : (s:ℝ)*(q:ℝ) ≤ (q:ℝ)^(1+ε/2) := by
        have h1 : (s:ℝ)*(q:ℝ) ≤ (q:ℝ)^(ε/2) * (q:ℝ)^(1:ℝ) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_right hs_ub hqR.le
        rw [← Real.rpow_add hqR] at h1
        rwa [show ε/2+1 = 1+ε/2 by ring] at h1
      linarith [hSQ1, hqexp_ge1]
    rcases eq_or_ne d 1 with hd1eq | hdne1
    · refine ⟨hd1eq, ?_⟩
      have hVbound1 : (q:ℝ)^(1 - ε/8 - ε/500) / (16*C) ≤ (V:ℝ) := by
        have h := hVbound
        rw [hd1eq] at h
        simpa using h
      have step1 : (c/4)*(q:ℝ)^(ε/2) * (V:ℝ) ≤ (c*(s:ℝ)/2) * (V:ℝ) :=
        mul_le_mul_of_nonneg_right hcs_lb (by positivity)
      have step2 : (c/4)*(q:ℝ)^(ε/2) * ((q:ℝ)^(1-ε/8-ε/500)/(16*C))
          ≤ (c/4)*(q:ℝ)^(ε/2) * (V:ℝ) :=
        mul_le_mul_of_nonneg_left hVbound1 (by positivity)
      have step3 : (c/4)*(q:ℝ)^(ε/2) * ((q:ℝ)^(1-ε/8-ε/500)/(16*C))
          = (c/(64*C)) * (q:ℝ)^(1+ε*(373/1000)) := by
        rw [show (c/4)*(q:ℝ)^(ε/2) * ((q:ℝ)^(1-ε/8-ε/500)/(16*C))
            = (c/(64*C)) * ((q:ℝ)^(ε/2) * (q:ℝ)^(1-ε/8-ε/500)) by
              field_simp; ring,
          ← Real.rpow_add hqR]
        congr 2
        ring
      have step4 : (64:ℝ)*C/c < (q:ℝ)^(373*ε/1000) := hQ₃ q hqQ3
      have step5 : (q:ℝ) < (c/(64*C)) * (q:ℝ)^(1+ε*(373/1000)) := by
        have hqR1 : (q:ℝ)^(1+ε*(373/1000)) = (q:ℝ) * (q:ℝ)^(373*ε/1000) := by
          rw [show (1:ℝ)+ε*(373/1000) = 373*ε/1000 + 1 by ring, Real.rpow_add hqR, Real.rpow_one]
          ring
        rw [hqR1]
        have h2 : (q:ℝ) * ((64:ℝ)*C/c) < (q:ℝ) * (q:ℝ)^(373*ε/1000) :=
          mul_lt_mul_of_pos_left step4 hqR
        have h7 : c/(64*C) * ((q:ℝ)*((64:ℝ)*C/c)) < c/(64*C) * ((q:ℝ)*(q:ℝ)^(373*ε/1000)) :=
          mul_lt_mul_of_pos_left h2 (by positivity)
        have h8 : c/(64*C) * ((q:ℝ)*((64:ℝ)*C/c)) = q := by field_simp
        linarith [h7, h8]
      linarith [step1, step2, step3, step5]
    · exfalso
      have hd2 : 2 ≤ d := by omega
      have hcsd_lb : ((c/4)*(q:ℝ)^(ε/2))^d ≤ (c*(s:ℝ)/2)^d :=
        pow_le_pow_left₀ (by positivity) hcs_lb d
      have hcsd_eq : ((c/4)*(q:ℝ)^(ε/2))^d = (c/4)^d * (q:ℝ)^(ε/2*d) := by
        rw [mul_pow, hpow_eq]
      have hstep1 : (c/4)^d * (q:ℝ)^(ε/2*d)
            * ((q:ℝ)^(1 - (d:ℝ)*ε/8 - (d:ℝ)*ε/500)/(16*C*(d:ℝ))^d)
          ≤ (c*(s:ℝ)/2)^d * (V:ℝ) := by
        rw [← hcsd_eq]
        refine mul_le_mul hcsd_lb hVbound ?_ ?_
        · exact div_nonneg (Real.rpow_nonneg hqR.le _) (le_of_lt (by
            apply pow_pos; positivity))
        · exact pow_nonneg (by positivity) d
      have hexp_eq : (q:ℝ)^(ε/2*d) * (q:ℝ)^(1 - (d:ℝ)*ε/8 - (d:ℝ)*ε/500)
          = (q:ℝ)^(1 + (d:ℝ)*ε*(373/1000)) := by
        rw [← Real.rpow_add hqR]; congr 1; ring
      have hstep3 : (c/4)^d/(16*C*(d:ℝ))^d * (q:ℝ)^(1 + (d:ℝ)*ε*(373/1000))
          ≤ (s:ℝ)*(q:ℝ)+1 := by
        have heq2 : (c/4)^d * (q:ℝ)^(ε/2*d)
              * ((q:ℝ)^(1 - (d:ℝ)*ε/8 - (d:ℝ)*ε/500)/(16*C*(d:ℝ))^d)
            = (c/4)^d/(16*C*(d:ℝ))^d
              * ((q:ℝ)^(ε/2*d) * (q:ℝ)^(1 - (d:ℝ)*ε/8 - (d:ℝ)*ε/500)) := by
          ring
        rw [heq2, hexp_eq] at hstep1
        exact le_trans hstep1 hFaceR
      have hd0pos : 0 < d₀ := lt_of_lt_of_le hd1 hdd0
      have hd0R : (0:ℝ) < (d₀:ℝ) := by exact_mod_cast hd0pos
      have hd0R1 : (1:ℝ) ≤ (d₀:ℝ) := by exact_mod_cast hd0pos
      set K : ℝ := (64*C*(d₀:ℝ)*(1+1/c))^d₀ with hKdef
      have hKpos : 0 < K := by rw [hKdef]; positivity
      have hconst_bound : K⁻¹ ≤ (c/4)^d/(16*C*(d:ℝ))^d := by
        have hbase_le : (64*C*(d:ℝ))/c ≤ 64*C*(d₀:ℝ)*(1+1/c) := by
          have h1 : (d:ℝ) ≤ (d₀:ℝ) := by exact_mod_cast hdd0
          have h2 : (64:ℝ)*C*(d:ℝ)/c ≤ 64*C*(d₀:ℝ)/c := by
            apply div_le_div_of_nonneg_right (by nlinarith [h1, hCpos]) hc.le
          have h3 : (64:ℝ)*C*(d₀:ℝ)/c ≤ 64*C*(d₀:ℝ)*(1+1/c) := by
            have heq : (64:ℝ)*C*(d₀:ℝ)/c = 64*C*(d₀:ℝ)*(1/c) := by ring
            rw [heq]
            have hd0nn : (0:ℝ) ≤ (d₀:ℝ) := by positivity
            nlinarith [hd0nn, hc, hCpos]
          linarith
        have hpow_le : ((64*C*(d:ℝ))/c)^d ≤ K := by
          rw [hKdef]
          have hstepA : ((64*C*(d:ℝ))/c)^d ≤ (64*C*(d₀:ℝ)*(1+1/c))^d :=
            pow_le_pow_left₀ (by positivity) hbase_le d
          have hstepB : (64*C*(d₀:ℝ)*(1+1/c))^d ≤ (64*C*(d₀:ℝ)*(1+1/c))^d₀ := by
            refine pow_le_pow_right₀ ?_ hdd0
            have hCd0 : (1:ℝ) ≤ C * (d₀:ℝ) := by nlinarith [hC, hd0R1]
            have hcinv : (0:ℝ) < 1/c := one_div_pos.mpr hc
            nlinarith [hCd0, hcinv]
          linarith
        have hinv : (c/4)^d/(16*C*(d:ℝ))^d = ((64*C*(d:ℝ)/c))⁻¹ ^ d := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
        rw [hinv, inv_pow]
        exact inv_anti₀ (by positivity) hpow_le
      have hqbig : 2*K < (q:ℝ)^(123*ε/500) := by rw [hKdef]; exact hQ₂ q hqQ2
      have hexp_split : (q:ℝ)^(1 + (d:ℝ)*ε*(373/1000))
          = (q:ℝ)^(1+ε/2) * (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2) := by
        rw [← Real.rpow_add hqR]; congr 1; ring
      have hmargin : (123*ε/500 : ℝ) ≤ (d:ℝ)*ε*(373/1000) - ε/2 := by
        have h2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd2
        nlinarith [h2, hε0]
      have hexp_mono : (q:ℝ)^(123*ε/500) ≤ (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ q)) hmargin
      have hbig2K : 2*K < (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2) := lt_of_lt_of_le hqbig hexp_mono
      have hfinal2 : (s:ℝ)*(q:ℝ)+1 < (c/4)^d/(16*C*(d:ℝ))^d * (q:ℝ)^(1 + (d:ℝ)*ε*(373/1000)) := by
        rw [hexp_split]
        calc (s:ℝ)*(q:ℝ)+1 ≤ 2*(q:ℝ)^(1+ε/2) := hSQ
          _ = K⁻¹ * (q:ℝ)^(1+ε/2) * (2*K) := by field_simp
          _ < K⁻¹ * (q:ℝ)^(1+ε/2) * (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2) := by
              apply mul_lt_mul_of_pos_left hbig2K
              positivity
          _ ≤ ((c/4)^d/(16*C*(d:ℝ))^d) * (q:ℝ)^(1+ε/2) * (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_right hconst_bound (by positivity)
          _ = (c/4)^d/(16*C*(d:ℝ))^d * ((q:ℝ)^(1+ε/2) * (q:ℝ)^((d:ℝ)*ε*(373/1000) - ε/2)) := by
              ring
      linarith [hstep3, hfinal2]
  obtain ⟨hd1eq, hbig⟩ := hd1_and_big
  obtain ⟨i₁, hi₁eq⟩ := Finset.card_eq_one.mp (hddef ▸ hd1eq)
  have hi₁active : i₁ ∈ Active := hi₁eq ▸ Finset.mem_singleton_self i₁
  have hi₁activeP : ⌈P.α i₁⌉ < ⌊P.β i₁⌋ := by simpa [hActive] using hi₁active
  have hVeq : (V:ℝ) = (⌊P.β i₁⌋:ℝ) - (⌈P.α i₁⌉:ℝ) := by
    have : V = (⌊P.β i₁⌋ - ⌈P.α i₁⌉).toNat := by rw [hVdef, hi₁eq]; simp
    rw [this]
    have h2 : ((⌊P.β i₁⌋ - ⌈P.α i₁⌉:ℤ).toNat:ℝ) = ((⌊P.β i₁⌋ - ⌈P.α i₁⌉:ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ⌊P.β i₁⌋ - ⌈P.α i₁⌉)
    rw [h2]; push_cast; ring
  -- generator at i₁ is a unit mod q
  obtain ⟨n₀, hn₀, hj₀eq, hbdd, hinact⟩ := gap_active_repr P v hv hv0 (j₀:ℤ) (hJmem j₀ hj₀)
  have hj₀eq' : (j₀:ℤ) = (n₀ i₁ - v i₁) * P.d i₁ := by
    rw [hj₀eq, show Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋) = ({i₁} : Finset (Fin P.D))
      from hActive ▸ hi₁eq]
    simp
  have hunit_gen : IsUnit ((P.d i₁ : ZMod q)) := by
    have hu := hunits j₀ hj₀
    rw [show ((j₀:ℕ):ZMod q) = ((n₀ i₁ - v i₁ : ℤ):ZMod q) * (P.d i₁ : ZMod q) by
      have := hj₀eq'
      have hcast : ((j₀:ℕ):ZMod q) = ((j₀:ℤ):ZMod q) := by push_cast; ring
      rw [hcast, this]; push_cast; ring] at hu
    exact isUnit_of_mul_isUnit_right hu
  -- one-dimensional face covers all residues
  have hcount : (q:ℕ) ≤ (Finset.Icc ⌈(c*(s:ℝ))*P.α i₁⌉ ⌊(c*(s:ℝ))*P.β i₁⌋).card := by
    have hge := gap_interval_count_ge (P.α i₁) (P.β i₁) (c*(s:ℝ)) ht2 hi₁activeP
    rw [← hVeq] at hge
    have : (q:ℝ) ≤ ((Finset.Icc ⌈(c*(s:ℝ))*P.α i₁⌉ ⌊(c*(s:ℝ))*P.β i₁⌋).card:ℝ) := by
      linarith [hge, hbig]
    exact_mod_cast this
  set L' : ℤ := ⌈(c*(s:ℝ))*P.α i₁⌉ with hL'def
  set U' : ℤ := ⌊(c*(s:ℝ))*P.β i₁⌋ with hU'def
  set cnt : ℕ := (Finset.Icc L' U').card with hcntdef
  set CONST : ℤ := L' * P.d i₁ + ∑ i ∈ Finset.univ.filter (fun i => i ≠ i₁), w i * P.d i
    with hCONSTdef
  have hcardeq2 : (cnt:ℤ) = U' - L' + 1 := by
    have h1 : (Finset.Icc L' U').card = (U'+1-L').toNat := Int.card_Icc _ _
    have hle : L' ≤ U' := by
      by_contra hcon
      push Not at hcon
      have : (Finset.Icc L' U').card = 0 := by rw [Finset.Icc_eq_empty (by omega)]; simp
      rw [hcntdef, this] at hcount
      omega
    rw [hcntdef, h1, Int.toNat_of_nonneg (by omega)]
    ring
  have hn : ∀ t : ℕ, t < cnt → ∀ i, (c*(s:ℝ)) * P.α i ≤ ((if i = i₁ then L' + t else w i : ℤ):ℝ)
      ∧ ((if i = i₁ then L' + t else w i : ℤ):ℝ) ≤ (c*(s:ℝ)) * P.β i := by
    intro t ht i
    by_cases hi : i = i₁
    · subst hi
      simp only [ite_true]
      have hLU : L' + (t:ℤ) ≤ U' := by
        have : (t:ℤ) < cnt := by exact_mod_cast ht
        omega
      constructor
      · calc (c*(s:ℝ)) * P.α i ≤ (L':ℝ) := by rw [hL'def]; exact Int.le_ceil _
          _ ≤ ((L' + (t:ℤ) : ℤ):ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) t]
      · calc ((L' + (t:ℤ) : ℤ):ℝ) ≤ (U':ℝ) := by exact_mod_cast hLU
          _ ≤ (c*(s:ℝ)) * P.β i := by rw [hU'def]; exact Int.floor_le _
    · simp only [ite_eq_right_of_eq_false _ _ (eq_false hi)]
      exact hw i (by
        by_contra hcon
        have hiA : i ∈ Active := by simpa [hActive] using hcon
        rw [hi₁eq] at hiA
        exact hi (Finset.mem_singleton.mp hiA))
  have hy_mem : ∀ t : ℕ, t < cnt →
      (t:ℤ) * P.d i₁ + CONST ∈ (GAP.dilate (c*(s:ℝ)) P).set := by
    intro t ht
    show ∃ n : Fin P.D → ℤ, (∀ i, (c*(s:ℝ)) * P.α i ≤ (n i:ℝ) ∧ (n i:ℝ) ≤ (c*(s:ℝ)) * P.β i) ∧
      (t:ℤ) * P.d i₁ + CONST = ∑ i, n i * P.d i
    refine ⟨fun i => if i = i₁ then L' + t else w i, hn t ht, ?_⟩
    rw [hCONSTdef]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i = i₁)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => i = i₁),
        (if i = i₁ then L' + (t:ℤ) else w i) * P.d i = (L' + t) * P.d i₁ := by
      rw [Finset.filter_eq']
      simp
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ i = i₁),
        (if i = i₁ then L' + (t:ℤ) else w i) * P.d i
        = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i₁), w i * P.d i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      rw [ite_eq_right_of_eq_false _ _ (eq_false hi.2)]
    rw [h1, h2]
    ring
  have hxy_sub : ∀ t : ℕ, t < cnt → x + ((t:ℤ) * P.d i₁ + CONST) ∈ subsetSums J' :=
    fun t ht => hxspec _ (hy_mem t ht)
  have hcov : ∀ r : ZMod q, ∃ t : ℕ, t < cnt ∧
      ((x + ((t:ℤ) * P.d i₁ + CONST) : ℤ) : ZMod q) = r := by
    intro r
    obtain ⟨t, ht, heq⟩ := ap_unit_covers (x + CONST) (P.d i₁) hunit_gen cnt hcount r
    refine ⟨t, ht, ?_⟩
    rw [← heq]
    congr 1
    ring
  obtain ⟨t, ht, heq⟩ := hcov r
  obtain ⟨T, hTJ', hTeq⟩ := hxy_sub t ht
  refine ⟨T, hTJ', ?_⟩
  rw [← hTeq]
  exact heq

/-- **Lemma 3, wide form.** The covering statement for an arbitrary fixed constant `C ≥ 1` and
with no lower endpoint restriction: `I ⊆ [1, C q^ε]`.

This is what the elementary replacement argument of `docs/elementary_replacements.md`
(Corollary C4) needs: the correction multipliers there satisfy `R(q) ≤ m ≤ 8 q^ε`, so the
covering lemma must accept `I ⊆ [1, 8 q^ε]`. The paper's `lemma3` is the case `C = 2` (its
lower bound `q^ε ≤ i` is only used there to get `0 < i`). -/
theorem lemma3_wide (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (C : ℝ) (hC : 1 ≤ C) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ I : Finset ℕ,
        (∀ i ∈ I, 0 < i ∧ (i : ℝ) ≤ C * (q : ℝ) ^ ε) →
        (∀ i ∈ I, Nat.Coprime i q) →
        (q : ℝ) ^ (7 * ε / 8) ≤ I.card →
        ∀ r : ZMod q, ∃ S ⊆ I, (S.card : ℝ) ≤ (q : ℝ) ^ (ε / 2) ∧
          ∑ i ∈ S, ((i : ZMod q)⁻¹) = r := by
  obtain ⟨c, hc, d₀, Q₁, hQ₁⟩ := lemma3_structure_apply ε hε0 hε1 C hC
  obtain ⟨Q₂, hQ₂⟩ := lemma3_core ε hε0 hε1 c hc C hC d₀
  obtain ⟨Q₃, hQ₃⟩ := lemma3_growth_bounds ε hε0 hε1 1 (by norm_num) C hC
  refine ⟨max (max Q₁ Q₂) Q₃, fun q hqpp hq I hI1 hI2 hI3 => ?_⟩
  have hqQ1 : Q₁ ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have hqQ2 : Q₂ ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have hqQ3 : Q₃ ≤ q := le_trans (le_max_right _ _) hq
  have hq2 : 2 ≤ q := hqpp.two_le
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  obtain ⟨J, J', P, hJA, hPproper, hPdil, hPne, hPD, hJ'J, hJcard, hJmem, h0mem, hJ'card, x, hxdilate⟩ :=
    hQ₁ q hqpp hqQ1 I hI1 hI2 hI3
  have hunits : ∀ j ∈ J, IsUnit ((j:ℕ):ZMod q) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJA hj)
    have hcop := hI2 i hi
    have hui : IsUnit (i:ZMod q) := (ZMod.isUnit_iff_coprime i q).2 hcop
    have hcast : (((i:ZMod q)⁻¹).val : ZMod q) = (i:ZMod q)⁻¹ := ZMod.natCast_rightInverse _
    rw [hcast]
    exact ⟨⟨(i:ZMod q)⁻¹, i, ZMod.inv_mul_of_unit _ hui, ZMod.mul_inv_of_unit _ hui⟩, rfl⟩
  have hJlt : ∀ j ∈ J, j < q := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJA hj)
    exact ZMod.val_lt _
  have hJsmall : ∀ j ∈ J, ∃ i : ℕ, 0 < i ∧ (i:ℝ) ≤ C * (q:ℝ)^ε ∧ (i:ZMod q) * (j:ZMod q) = 1 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJA hj)
    have hcop := hI2 i hi
    have hui : IsUnit (i:ZMod q) := (ZMod.isUnit_iff_coprime i q).2 hcop
    refine ⟨i, (hI1 i hi).1, (hI1 i hi).2, ?_⟩
    have hcast : (((i:ZMod q)⁻¹).val : ZMod q) = (i:ZMod q)⁻¹ := ZMod.natCast_rightInverse _
    rw [hcast]
    exact ZMod.mul_inv_of_unit _ hui
  have hcover := hQ₂ q hqpp hqQ2 I.card J J' P hPproper hPdil hPne hPD hJ'J hJcard hJmem h0mem
    hunits hJlt hJsmall hJ'card hI3 ⟨x, hxdilate⟩
  have hA_qlt : C * (q:ℝ) ^ ε < q := (hQ₃ q hqQ3).1
  have hlt : ∀ i ∈ I, i < q := by
    intro i hi
    have hi2 := (hI1 i hi).2
    have hiR : (i:ℝ) < q := lt_of_le_of_lt hi2 hA_qlt
    exact_mod_cast hiR
  have hInj : Set.InjOn (fun i : ℕ => ((i:ZMod q)⁻¹).val) I := invVal_injOn hq2 hI2 hlt
  have hJ'A : J' ⊆ I.image (fun i : ℕ => ((i:ZMod q)⁻¹).val) := hJ'J.trans hJA
  have hBs : ((J'.card:ℝ)) ≤ (q:ℝ)^(ε/2) := by
    calc (J'.card:ℝ) ≤ (⌊(q:ℝ)^(ε/2)⌋₊:ℝ) := by exact_mod_cast hJ'card
      _ ≤ (q:ℝ)^(ε/2) := Nat.floor_le (by positivity)
  exact exists_S_of_covering hq0 hInj hJ'A ((q:ℝ)^(ε/2)) hBs hcover

/-- **Lemma 3** of the paper: the case `C = 2` of `lemma3_wide` (the lower endpoint
restriction `q^ε ≤ i` is only used to see that `i` is positive). -/
theorem lemma3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ I : Finset ℕ,
        (∀ i ∈ I, (q : ℝ) ^ ε ≤ i ∧ (i : ℝ) ≤ 2 * (q : ℝ) ^ ε) →
        (∀ i ∈ I, Nat.Coprime i q) →
        (q : ℝ) ^ (7 * ε / 8) ≤ I.card →
        ∀ r : ZMod q, ∃ S ⊆ I, (S.card : ℝ) ≤ (q : ℝ) ^ (ε / 2) ∧
          ∑ i ∈ S, ((i : ZMod q)⁻¹) = r := by
  obtain ⟨Q₀, hQ₀⟩ := lemma3_wide ε hε0 hε1 2 (by norm_num)
  refine ⟨Q₀, fun q hqpp hq I hI1 hI2 hI3 => hQ₀ q hqpp hq I (fun i hi => ⟨?_, (hI1 i hi).2⟩)
    hI2 hI3⟩
  have hqpos : 0 < q := by have := hqpp.two_le; omega
  have hqεpos : (0:ℝ) < (q:ℝ)^ε := Real.rpow_pos_of_pos (by exact_mod_cast hqpos) ε
  have hiR : (0:ℝ) < (i:ℝ) := lt_of_lt_of_le hqεpos (hI1 i hi).1
  exact_mod_cast hiR

end Erdos289
