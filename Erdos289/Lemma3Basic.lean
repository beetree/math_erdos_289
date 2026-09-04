import Erdos289.Defs
import Erdos289.ExternalBridge
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

The proof follows Section 4 of `erdos_289_full_proof.pdf` ("Sparse modular inverse subsets
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
  coordinate, the face-counting cardinality bound (4.3), and dilated-interval integer counts.
  These are proved in full.
* `divisor_count_bound`: the divisor-counting cardinality bound (paper's step 5), proved in
  full: pairing each `j` with a bounded witness and a small modular inverse embeds `J`
  injectively into boundedly many divisors of boundedly many integers.
* `paper_steps_4_5`: the quantitative form of the paper's steps 4–5 (simultaneous
  approximation + the divisor-bound argument, paper's (4.6)): the active-coordinate product
  `V` satisfies `V ≥ q^(1 - dε/8 - dε/500) / (16Cd)^d`. Proved in full in
  `Erdos289/Lemma3Steps45.lean` (a uniform-in-`d ≤ d₀` pigeonhole box count plus the
  divisor-count bound); `hd1_and_big` inside `lemma3_core` derives the paper's `d = 1`
  dichotomy and the final quantitative bound on `V` from this one statement, including all of
  the surrounding real-asymptotic bookkeeping. Note that this fixed-loss bound differs from
  the paper's divisor-envelope display (paper (4.5)); both force rank one.
* `lemma3_core`: assembles the pieces above into the full argument (paper's steps 2–6: active
  coordinates, face counting, the `d = 1` dichotomy, and the final covering conclusion).
  Every step is proved in full.

`lemma3` and `lemma3_wide` are assembled from these pieces with no `sorry`.
-/

set_option maxRecDepth 100000

namespace Erdos289

open Finset Filter Real Topology


/-- **Step 4** of the proof of Lemma 3 (simultaneous approximation by pigeonhole).

Fix a modulus `q ≥ 2`, generators `d : Fin D → ℤ`, and positive real bounds `B i`. If the
number of boxes `∏ i, ⌈q / B i⌉₊` obtained by partitioning each coordinate `[0, q)` into
intervals of length `B i` is less than `q`, then pigeonholing the `q` vectors
`(t * d i mod q) i` for `t = 0, …, q - 1` into these boxes produces `1 ≤ T < q` and, for each
coordinate `i`, an integer `e i ≡ T * d i (mod q)` with `|e i| ≤ B i`. -/
lemma simultaneous_approx {q : ℕ} (hq : 2 ≤ q) {D : ℕ} (d : Fin D → ℤ) (B : Fin D → ℝ)
    (hB : ∀ i, 0 < B i) (hprod : (∏ i, ⌈(q:ℝ) / B i⌉₊) < q) :
    ∃ T : ℤ, 1 ≤ T ∧ T < q ∧
      ∀ i, ∃ e : ℤ, (e : ZMod q) = (T : ZMod q) * (d i : ZMod q) ∧ |(e:ℝ)| ≤ B i := by
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set N : Fin D → ℕ := fun i => ⌈(q:ℝ) / B i⌉₊ with hNdef
  have hNpos : ∀ i, 0 < N i := by
    intro i
    apply Nat.ceil_pos.mpr
    have := hB i
    positivity
  have hNB : ∀ i, (q:ℝ) ≤ N i * B i := by
    intro i
    have h1 : (q:ℝ) / B i ≤ N i := Nat.le_ceil _
    have h2 := hB i
    calc (q:ℝ) = (q / B i) * B i := by field_simp
    _ ≤ (N i : ℝ) * B i := by gcongr
  set R : Fin D → ℤ → ℤ := fun i t => (t * d i) % (q:ℤ) with hRdef
  have hRnn : ∀ i t, 0 ≤ R i t := fun i t => Int.emod_nonneg _ (by exact_mod_cast (by omega : (q:ℤ) ≠ 0))
  have hRltq : ∀ i t, R i t < (q:ℤ) := fun i t => Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : (0:ℤ) < q))
  have hRcast : ∀ i t, (R i t : ZMod q) = (t : ZMod q) * (d i : ZMod q) := by
    intro i t
    have : (R i t : ZMod q) = ((t * d i : ℤ) : ZMod q) := by
      rw [hRdef]; push_cast
      simp
    rw [this]; push_cast; ring
  set box : Fin D → ℤ → ℕ := fun i t => ⌊(R i t : ℝ) * N i / q⌋₊ with hboxdef
  have hboxlt : ∀ i (t : ℤ), box i t < N i := by
    intro i t
    rw [hboxdef]
    rw [Nat.floor_lt (by
      have h1 := hRnn i t
      have : (0:ℝ) ≤ (R i t : ℝ) := by exact_mod_cast h1
      positivity)]
    rw [div_lt_iff₀ hqR]
    have h1 : (R i t : ℝ) < q := by exact_mod_cast hRltq i t
    have h2 : (0:ℝ) < (N i : ℝ) := by exact_mod_cast hNpos i
    nlinarith
  set g : ℕ → (Π i : Fin D, Fin (N i)) := fun t i => ⟨box i (t : ℤ), hboxlt i t⟩ with hgdef
  have hcard : ((Finset.range q).image g).card < (Finset.range q).card := by
    rw [Finset.card_range]
    calc ((Finset.range q).image g).card
        ≤ Fintype.card (Π i : Fin D, Fin (N i)) := Finset.card_le_univ _
      _ = ∏ i, N i := by rw [Fintype.card_pi]; simp
      _ < q := hprod
  obtain ⟨t1, ht1, t2, ht2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_image_lt hcard
  simp only [Finset.mem_range] at ht1 ht2
  have hbeq : ∀ i, box i (t1 : ℤ) = box i (t2 : ℤ) := by
    intro i
    have := congrFun heq i
    simpa [hgdef] using this
  have hbound : ∀ i, |(R i (t1 : ℤ) : ℝ) - (R i (t2 : ℤ) : ℝ)| * N i < (q : ℝ) := by
    intro i
    have hk := hbeq i
    have hN0 : (0:ℝ) < (N i : ℝ) := by exact_mod_cast hNpos i
    have hx1nn : (0:ℝ) ≤ (R i (t1:ℤ) : ℝ) * N i / q := by
      have h0 := hRnn i (t1:ℤ)
      have h0' : (0:ℝ) ≤ (R i (t1:ℤ) : ℝ) := by exact_mod_cast h0
      positivity
    have hx2nn : (0:ℝ) ≤ (R i (t2:ℤ) : ℝ) * N i / q := by
      have h0 := hRnn i (t2:ℤ)
      have h0' : (0:ℝ) ≤ (R i (t2:ℤ) : ℝ) := by exact_mod_cast h0
      positivity
    have e1 : (box i (t2:ℤ) : ℝ) * q ≤ (R i (t1:ℤ) : ℝ) * N i := by
      have h : (box i (t1:ℤ) : ℝ) ≤ (R i (t1:ℤ) : ℝ) * N i / q := Nat.floor_le hx1nn
      rw [hk] at h
      rwa [le_div_iff₀ hqR] at h
    have e2 : (R i (t1:ℤ) : ℝ) * N i < ((box i (t2:ℤ) : ℝ) + 1) * q := by
      have h : (R i (t1:ℤ) : ℝ) * N i / q < (box i (t1:ℤ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [hk] at h
      rwa [div_lt_iff₀ hqR] at h
    have e3 : (box i (t2:ℤ) : ℝ) * q ≤ (R i (t2:ℤ) : ℝ) * N i :=
      (le_div_iff₀ hqR).mp (Nat.floor_le hx2nn)
    have e4 : (R i (t2:ℤ) : ℝ) * N i < ((box i (t2:ℤ) : ℝ) + 1) * q :=
      (div_lt_iff₀ hqR).mp (Nat.lt_floor_add_one _)
    have hp : ((R i (t1:ℤ) : ℝ) - (R i (t2:ℤ) : ℝ)) * N i < q := by nlinarith
    have hn : -(q:ℝ) < ((R i (t1:ℤ) : ℝ) - (R i (t2:ℤ) : ℝ)) * N i := by nlinarith
    calc |(R i (t1:ℤ) : ℝ) - (R i (t2:ℤ) : ℝ)| * N i
        = |((R i (t1:ℤ) : ℝ) - (R i (t2:ℤ) : ℝ)) * N i| := by rw [abs_mul, abs_of_nonneg hN0.le]
      _ < q := abs_lt.mpr ⟨hn, hp⟩
  have hBbound : ∀ i, |(R i (t1 : ℤ) : ℝ) - (R i (t2 : ℤ) : ℝ)| ≤ B i := by
    intro i
    have h1 := hbound i
    have h2 := hNB i
    have hN0 : (0:ℝ) < (N i : ℝ) := by exact_mod_cast hNpos i
    have h3 : |(R i (t1 : ℤ) : ℝ) - (R i (t2 : ℤ) : ℝ)| ≤ (q:ℝ) / N i := by
      rw [le_div_iff₀ hN0]; linarith
    have h4 : (q:ℝ) / N i ≤ B i := by
      rw [div_le_iff₀ hN0]; linarith
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨(t2:ℤ) - (t1:ℤ), by omega, by omega, fun i => ⟨R i (t2:ℤ) - R i (t1:ℤ), ?_, ?_⟩⟩
    · have h1 := hRcast i (t2:ℤ)
      have h2 := hRcast i (t1:ℤ)
      push_cast at h1 h2 ⊢
      rw [h1, h2]; ring
    · push_cast
      rw [abs_sub_comm]
      exact hBbound i
  · refine ⟨(t1:ℤ) - (t2:ℤ), by omega, by omega, fun i => ⟨R i (t1:ℤ) - R i (t2:ℤ), ?_, ?_⟩⟩
    · have h1 := hRcast i (t1:ℤ)
      have h2 := hRcast i (t2:ℤ)
      push_cast at h1 h2 ⊢
      rw [h1, h2]; ring
    · push_cast
      exact hBbound i

/-- **Step 0** of the proof of Lemma 3: the map sending `i` to the natural-number
representative (`val`) of `(i : ZMod q)⁻¹` is injective on any `I` consisting of elements
below `q` that are coprime to `q`. -/
lemma invVal_injOn {q : ℕ} (hq : 2 ≤ q) {I : Finset ℕ}
    (hcop : ∀ i ∈ I, Nat.Coprime i q) (hlt : ∀ i ∈ I, i < q) :
    Set.InjOn (fun i : ℕ => ((i : ZMod q)⁻¹).val) I := by
  have : NeZero q := ⟨by omega⟩
  intro i hi j hj hij
  simp only at hij
  have hui : IsUnit (i : ZMod q) := (ZMod.isUnit_iff_coprime i q).2 (hcop i hi)
  have huj : IsUnit (j : ZMod q) := (ZMod.isUnit_iff_coprime j q).2 (hcop j hj)
  have heq : (i : ZMod q)⁻¹ = (j : ZMod q)⁻¹ := ZMod.val_injective q hij
  have h1 : (i : ZMod q) * (j : ZMod q)⁻¹ = 1 := by
    rw [← heq]; exact ZMod.mul_inv_of_unit _ hui
  have h2 : (j : ZMod q)⁻¹ * (i : ZMod q) = 1 := by rw [mul_comm]; exact h1
  have h3 : (i : ZMod q) = (j : ZMod q) := ((ZMod.inv_mul_eq_one_of_isUnit huj (i:ZMod q)).mp h2).symm
  have h4 := congrArg ZMod.val h3
  rwa [ZMod.val_cast_of_lt (hlt i hi), ZMod.val_cast_of_lt (hlt j hj)] at h4

/-- The last paragraph of the proof of Lemma 3: once the subset sums of `J' ⊆ I.image φ`
(where `φ` is the modular-inverse-value map) are known to cover every residue class mod `q`
using at most `B` terms, pulling back through the injective map `φ` produces, for every
residue `r`, a set `S ⊆ I` of at most `B` elements whose inverses sum to `r`. -/
lemma exists_S_of_covering {q : ℕ} (hq0 : q ≠ 0) {I : Finset ℕ}
    (hInj : Set.InjOn (fun i : ℕ => ((i:ZMod q)⁻¹).val) I)
    {J' : Finset ℕ} (hJ' : J' ⊆ I.image (fun i : ℕ => ((i:ZMod q)⁻¹).val))
    (B : ℝ) (hB : (J'.card:ℝ) ≤ B)
    (hcover : ∀ r : ZMod q, ∃ T ⊆ J', ((∑ i ∈ T, (i:ℤ) : ℤ) : ZMod q) = r) :
    ∀ r : ZMod q, ∃ S ⊆ I, (S.card:ℝ) ≤ B ∧ ∑ i ∈ S, ((i:ZMod q)⁻¹) = r := by
  have : NeZero q := ⟨hq0⟩
  intro r
  obtain ⟨T, hTJ', hTsum⟩ := hcover r
  set φ : ℕ → ℕ := fun i => ((i:ZMod q)⁻¹).val with hφdef
  set S : Finset ℕ := I.filter (fun i => φ i ∈ T) with hSdef
  have hSI : S ⊆ I := Finset.filter_subset _ _
  have hTA : T ⊆ I.image φ := hTJ'.trans hJ'
  have himageS : S.image φ = T := by
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [hSdef, Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiT⟩, rfl⟩ := hx
      exact hiT
    · intro x hx
      obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp (hTA hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, hx⟩, rfl⟩
  have hInjS : Set.InjOn φ S := hInj.mono hSI
  have hcardS : S.card = T.card := by
    rw [← himageS]
    exact (Finset.card_image_of_injOn hInjS).symm
  refine ⟨S, hSI, ?_, ?_⟩
  · rw [hcardS]
    have hTle : T.card ≤ J'.card := Finset.card_le_card hTJ'
    calc (T.card:ℝ) ≤ (J'.card:ℝ) := by exact_mod_cast hTle
      _ ≤ B := hB
  · have hval : ∀ i ∈ S, (i:ZMod q)⁻¹ = ((φ i : ℕ) : ZMod q) := by
      intro i _
      exact (ZMod.natCast_rightInverse ((i:ZMod q)⁻¹)).symm
    calc ∑ i ∈ S, ((i:ZMod q)⁻¹)
        = ∑ i ∈ S, ((φ i : ℕ):ZMod q) := Finset.sum_congr rfl hval
      _ = ((∑ i ∈ S, φ i : ℕ) : ZMod q) := by push_cast; rfl
      _ = ((∑ i ∈ S, (φ i:ℤ) : ℤ) : ZMod q) := by push_cast; rfl
      _ = ((∑ j ∈ S.image φ, (j:ℤ) : ℤ) : ZMod q) := by
            rw [Finset.sum_image (fun x hx y hy hxy => hInjS hx hy hxy)]
      _ = ((∑ j ∈ T, (j:ℤ) : ℤ) : ZMod q) := by rw [himageS]
      _ = r := hTsum

/-- A power `q ^ a` eventually dominates `C * q ^ b + D` when `b < a` (used repeatedly below
to make the paper's "for sufficiently large `q`" estimates precise). -/
lemma eventually_rpow_dominates (a b C D : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q:ℝ) ^ a + D ≤ (q:ℝ) ^ b := by
  have h1 : Tendsto (fun q : ℕ => (q:ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun q : ℕ => (q:ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop (C + 1), h2.eventually_ge_atTop D,
    eventually_ge_atTop (1:ℕ)] with q hq1 hq2 hq3
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqa_nn : (0:ℝ) ≤ (q:ℝ) ^ a := Real.rpow_nonneg hqpos.le a
  have hsplit : (q:ℝ) ^ b = (q:ℝ) ^ a * (q:ℝ) ^ (b - a) := by
    rw [← Real.rpow_add hqpos]; ring_nf
  rw [hsplit]
  nlinarith

/-- `log q` is eventually dominated by `K * q ^ a` for any fixed `a > 0`, `K > 0`. -/
lemma eventually_log_le_rpow (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∀ᶠ q : ℕ in atTop, Real.log q ≤ K * (q:ℝ)^a := by
  have h := (isLittleO_log_rpow_atTop ha).def hK
  have h2 : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h3 := h2.eventually h
  filter_upwards [h3, eventually_ge_atTop (1:ℕ)] with q hq hq1
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog_nn : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hrpow_nn : 0 ≤ (q:ℝ)^a := Real.rpow_nonneg hqpos.le a
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog_nn, abs_of_nonneg hrpow_nn] at hq

/-- The "for sufficiently large `q`" real-asymptotic estimates from the proof of Lemma 3:
`C q^ε < q` (so that `I`'s elements are `< q`), and, for `m` in the admissible range
`[q^(7ε/8), C q^ε]` (i.e. `m = |I|`, using the interval and cardinality hypotheses on `I`),
writing `s := ⌊q^(ε/2)⌋₊`: `q ≤ m^(2/ε)`, `m^(1/3) ≤ s`, and `s ≤ c m / log m`, matching
exactly the hypotheses `cfhmpsv_structure` needs for `β = 2/ε`, `η = 1/3`.

Here `C ≥ 1` is an arbitrary fixed constant (the paper's Lemma 3 is the case `C = 2`); since
`C` is fixed, all four estimates still hold for sufficiently large `q`. -/
lemma lemma3_growth_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 < c)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q →
      C * (q:ℝ) ^ ε < q ∧
      ∀ m : ℕ, (q:ℝ) ^ (7*ε/8) ≤ m → (m:ℝ) ≤ C*(q:ℝ)^ε →
        (q:ℝ) ≤ (m:ℝ) ^ (2/ε) ∧
        (m:ℝ) ^ ((1:ℝ)/3) ≤ (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ) ∧
        (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ) ≤ c * m / Real.log m := by
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  have hA : ∀ᶠ q : ℕ in atTop, (C + 1) * (q:ℝ)^ε + 0 ≤ (q:ℝ)^(1:ℝ) :=
    eventually_rpow_dominates ε 1 (C + 1) 0 hε0 hε1
  have hB : ∀ᶠ q : ℕ in atTop,
      C^((1:ℝ)/3) * (q:ℝ)^(ε/3) + 1 ≤ (q:ℝ)^(ε/2) :=
    eventually_rpow_dominates (ε/3) (ε/2) (C^((1:ℝ)/3)) 1 (by linarith) (by linarith)
  have hCe : ∀ᶠ q : ℕ in atTop, Real.log C + ε * Real.log q ≤ c * (q:ℝ)^(3*ε/8) := by
    have h1 := eventually_log_le_rpow (3*ε/8) (c / (2*ε)) (by linarith) (by positivity)
    have h2 : Tendsto (fun q : ℕ => (q:ℝ)^(3*ε/8)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [h1, h2.eventually_ge_atTop (2 * Real.log C / c)] with q hq1 hq2
    have h3 : Real.log C ≤ c/2 * (q:ℝ)^(3*ε/8) := by
      have h3' := (div_le_iff₀ hc).mp hq2
      nlinarith
    have hlog : ε * Real.log q ≤ c/2 * (q:ℝ)^(3*ε/8) := by
      have hmul := mul_le_mul_of_nonneg_left hq1 hε0.le
      calc ε * Real.log q ≤ ε * (c/(2*ε) * (q:ℝ)^(3*ε/8)) := hmul
        _ = c/2 * (q:ℝ)^(3*ε/8) := by field_simp
    linarith
  have hD : ∀ᶠ q : ℕ in atTop, (2:ℝ) ≤ (q:ℝ)^(7*ε/8) := by
    have h2 : Tendsto (fun q : ℕ => (q:ℝ)^(7*ε/8)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    exact h2.eventually_ge_atTop 2
  have hQ0 := (hA.and (hB.and (hCe.and hD)))
  rw [eventually_atTop] at hQ0
  obtain ⟨Q₀, hQ₀⟩ := hQ0
  refine ⟨max Q₀ 2, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqQ0 : Q₀ ≤ q := le_trans (le_max_left _ _) hq
  obtain ⟨hA', hB', hC', hD'⟩ := hQ₀ q hqQ0
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqEps : (0:ℝ) < (q:ℝ)^ε := Real.rpow_pos_of_pos hqR ε
  constructor
  · rw [Real.rpow_one] at hA'
    linarith
  · intro m hm7 hm2
    have hmR : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le (by positivity) hm7
    have hm1 : (1:ℝ) < (m:ℝ) := lt_of_lt_of_le (by norm_num) (le_trans hD' hm7)
    refine ⟨?_, ?_, ?_⟩
    · -- q ≤ m ^ (2/ε)
      have step1 : ((q:ℝ)^(7*ε/8))^(2/ε) ≤ (m:ℝ)^(2/ε) :=
        Real.rpow_le_rpow (by positivity) hm7 (by positivity)
      have step2 : ((q:ℝ)^(7*ε/8))^(2/ε) = (q:ℝ)^((7*ε/8) * (2/ε)) :=
        (Real.rpow_mul hqR.le (7*ε/8) (2/ε)).symm
      have step3 : (7*ε/8) * (2/ε) = (7:ℝ)/4 := by field_simp; ring
      have step4 : (q:ℝ) ≤ (q:ℝ)^((7:ℝ)/4) := by
        calc (q:ℝ) = (q:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
          _ ≤ (q:ℝ)^((7:ℝ)/4) := Real.rpow_le_rpow_of_exponent_le
                (by exact_mod_cast (by omega : 1 ≤ q)) (by norm_num)
      rw [step2, step3] at step1
      linarith
    · calc (m:ℝ)^((1:ℝ)/3) ≤ (C*(q:ℝ)^ε)^((1:ℝ)/3) :=
            Real.rpow_le_rpow (by positivity) hm2 (by positivity)
        _ = C^((1:ℝ)/3) * (q:ℝ)^(ε/3) := by
            rw [Real.mul_rpow hCpos.le (by positivity), ← Real.rpow_mul hqR.le]
            congr 2
            ring
        _ ≤ ⌊(q:ℝ)^(ε/2)⌋₊ := by
            have hsfloor : (q:ℝ)^(ε/2) < (⌊(q:ℝ)^(ε/2)⌋₊:ℝ) + 1 := Nat.lt_floor_add_one _
            linarith
    · -- ⌊q^(ε/2)⌋₊ ≤ c * m / log m
      have hlogm_pos : 0 < Real.log (m:ℝ) := Real.log_pos hm1
      have hlogm_le : Real.log (m:ℝ) ≤ Real.log C + ε * Real.log q := by
        calc Real.log (m:ℝ) ≤ Real.log (C*(q:ℝ)^ε) := Real.log_le_log hmR hm2
          _ = Real.log C + Real.log ((q:ℝ)^ε) := Real.log_mul (ne_of_gt hCpos) hqEps.ne'
          _ = Real.log C + ε * Real.log q := by rw [Real.log_rpow hqR]
      have key : (q:ℝ)^(ε/2) * Real.log (m:ℝ) ≤ c * (m:ℝ) := by
        calc (q:ℝ)^(ε/2) * Real.log (m:ℝ)
            ≤ (q:ℝ)^(ε/2) * (c*(q:ℝ)^(3*ε/8)) :=
              mul_le_mul_of_nonneg_left (le_trans hlogm_le hC') (by positivity)
          _ = c * (q:ℝ)^(ε/2 + 3*ε/8) := by rw [Real.rpow_add hqR]; ring
          _ = c * (q:ℝ)^(7*ε/8) := by rw [show ε/2+3*ε/8 = 7*ε/8 by ring]
          _ ≤ c * (m:ℝ) := by
              apply mul_le_mul_of_nonneg_left hm7 hc.le
      have hfrac : (q:ℝ)^(ε/2) ≤ c * (m:ℝ) / Real.log (m:ℝ) := by
        rw [le_div_iff₀ hlogm_pos]; exact key
      have hsfloor : (⌊(q:ℝ)^(ε/2)⌋₊:ℝ) ≤ (q:ℝ)^(ε/2) := Nat.floor_le (by positivity)
      linarith

/-- **Step 1** of the proof of Lemma 3: applying the CFHMPSV structure theorem
(`cfhmpsv_structure`) with `β = 2/ε`, `η = 1/3`. For `ε` fixed, obtain `c > 0` and `d₀` from
that theorem; then for all sufficiently large prime powers `q` and all finite `I` satisfying
the hypotheses of Lemma 3, writing `φ` for the modular-inverse-value map, `A := I.image φ`
and `m := A.card`, and `s := ⌊q ^ (ε/2)⌋₊`: there are `J ⊆ A`, a proper GAP `P` of rank
`≤ d₀`, and `J' ⊆ J` with `J'.card ≤ s`, `(m:ℝ)/2 ≤ J.card`, every `x ∈ J` and `0` lying in
`P.set`, and a translate of the dilate `(c * s) • P` contained in the subset sums of `J'`.

The hypothesis on `I` is the general one, `I ⊆ [1, C q^ε]` for a fixed `C ≥ 1` (no lower
endpoint restriction); the paper's Lemma 3 is the case `C = 2`. -/
lemma lemma3_structure_apply (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (C : ℝ) (hC : 1 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ I : Finset ℕ,
        (∀ i ∈ I, 0 < i ∧ (i : ℝ) ≤ C * (q : ℝ) ^ ε) →
        (∀ i ∈ I, Nat.Coprime i q) →
        (q : ℝ) ^ (7 * ε / 8) ≤ I.card →
        ∃ (J J' : Finset ℕ) (P : GAP),
          J ⊆ I.image (fun i : ℕ => ((i:ZMod q)⁻¹).val) ∧ P.Proper ∧
          (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ)) P).Proper ∧
          (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ)) P).set.Nonempty ∧ P.D ≤ d₀ ∧ J' ⊆ J ∧
          ((I.card : ℝ)) / 2 ≤ (J.card : ℝ) ∧
          (∀ x ∈ J, (x : ℤ) ∈ P.set) ∧ (0:ℤ) ∈ P.set ∧
          J'.card ≤ ⌊(q:ℝ)^(ε/2)⌋₊ ∧
          ∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ)) P).set, x + y ∈ subsetSums J' := by
  obtain ⟨c, hc, d₀, hstruct⟩ := cfhmpsv_structure (2/ε) (by rw [lt_div_iff₀ hε0]; linarith) (1/3)
    (by norm_num) (by norm_num)
  rw [eventually_atTop] at hstruct
  obtain ⟨M₀, hM₀⟩ := hstruct
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcl2 : (0:ℝ) < c * Real.log 2 := mul_pos hc hlog2
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  obtain ⟨Q₁, hQ₁⟩ := lemma3_growth_bounds ε hε0 hε1 (c * Real.log 2 / 2) (by positivity) C hC
  have hMtend : Tendsto (fun q : ℕ => (q:ℝ)^(7*ε/8)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.mp (hMtend.eventually_ge_atTop (max (M₀:ℝ) 2))
  refine ⟨c, hc, d₀, max (max Q₁ Q₂) 2, fun q _ hq I hI1 hI2 hI3 => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqQ1 : Q₁ ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have hqQ2 : Q₂ ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨hA_qlt, hbounds⟩ := hQ₁ q hqQ1
  set φ : ℕ → ℕ := fun i => ((i:ZMod q)⁻¹).val with hφdef
  have hlt : ∀ i ∈ I, i < q := by
    intro i hi
    have hi2 := (hI1 i hi).2
    have hiR : (i:ℝ) < q := lt_of_le_of_lt hi2 hA_qlt
    exact_mod_cast hiR
  have hInj : Set.InjOn φ I := invVal_injOn hq2 hI2 hlt
  set A : Finset ℕ := I.image φ with hAdef
  have hAcard : A.card = I.card := Finset.card_image_of_injOn hInj
  have hFact : Fact (1 < q) := ⟨by omega⟩
  have hAsub : A ⊆ Finset.Icc 1 q := by
    intro x hx
    simp only [hAdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hcop := hI2 i hi
    have hui : IsUnit (i:ZMod q) := (ZMod.isUnit_iff_coprime i q).2 hcop
    have hne0 : (i:ZMod q)⁻¹ ≠ 0 := by
      intro hz
      have h1 : (i:ZMod q) * (i:ZMod q)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hui
      rw [hz, mul_zero] at h1
      exact zero_ne_one h1
    have hvalpos : 0 < φ i := by
      rw [hφdef]
      simp only
      rcases Nat.eq_zero_or_pos (((i:ZMod q)⁻¹).val) with h0 | hpos
      · exfalso; apply hne0
        have hri := ZMod.natCast_rightInverse ((i:ZMod q)⁻¹)
        rw [h0] at hri
        simpa using hri.symm
      · exact hpos
    have hvallt : φ i < q := by rw [hφdef]; exact ZMod.val_lt _
    simp only [Finset.mem_Icc]
    omega
  set m := I.card with hmdef
  have hm7 : (q:ℝ)^(7*ε/8) ≤ (m:ℝ) := hI3
  have hmM0 : (max (M₀:ℝ) 2) ≤ (m:ℝ) := le_trans (hQ₂ q hqQ2) hm7
  have hmM0' : M₀ ≤ m := by
    have := le_trans (le_max_left (M₀:ℝ) 2) hmM0
    exact_mod_cast this
  have hm2R : (2:ℝ) ≤ (m:ℝ) := le_trans (le_max_right (M₀:ℝ) 2) hmM0
  have hm1 : (1:ℝ) < (m:ℝ) := by linarith
  have hm2q : (m:ℝ) ≤ C*(q:ℝ)^ε := by
    have hqε : (0:ℝ) < (q:ℝ)^ε := Real.rpow_pos_of_pos hqR ε
    have hCqnn : (0:ℝ) ≤ C*(q:ℝ)^ε := mul_nonneg hCpos.le hqε.le
    have hIsub : I ⊆ Finset.Icc 1 ⌊C*(q:ℝ)^ε⌋₊ := by
      intro i hi
      have h1 := (hI1 i hi).1
      have h2 := (hI1 i hi).2
      simp only [Finset.mem_Icc]
      exact ⟨h1, Nat.le_floor h2⟩
    have := Finset.card_le_card hIsub
    rw [Nat.card_Icc] at this
    have hfloor_le : (⌊C*(q:ℝ)^ε⌋₊ : ℝ) ≤ C*(q:ℝ)^ε := Nat.floor_le hCqnn
    have : (m:ℝ) ≤ ((⌊C*(q:ℝ)^ε⌋₊ + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast this
    simp only [Nat.add_sub_cancel] at this
    linarith
  obtain ⟨hq_mB, hm13, hslog⟩ := hbounds m hm7 hm2q
  set s := ⌊(q:ℝ)^(ε/2)⌋₊ with hsdef
  have hlogm_pos : 0 < Real.log (m:ℝ) := Real.log_pos hm1
  have hlogTwo_eq : Erdos289.External.logTwo (m:ℝ) = Real.log m / Real.log 2 := rfl
  -- `hslog : s ≤ (c * log 2 / 2) * m / log m`; double to reach the `logTwo`-form threshold.
  have hslog2 : (s:ℝ) ≤ c * (m:ℝ) / Erdos289.External.logTwo m := by
    have heq : c * (m:ℝ) / Erdos289.External.logTwo m = c * Real.log 2 * (m:ℝ) / Real.log m := by
      rw [hlogTwo_eq]; field_simp
    rw [heq]
    have hmono : c * Real.log 2 / 2 * (m:ℝ) / Real.log m ≤ c * Real.log 2 * (m:ℝ) / Real.log m := by
      gcongr
      linarith
    linarith
  obtain ⟨J, P, J', hJA, hPproper, hPdil, hPne, hPD, hJ'J, hJcard, hJmem, h0mem, hJ'card, x, hxdilate⟩ :=
    hM₀ m hmM0' q hq_mB A hAsub hAcard s hm13 hslog2
  have hshalf : c⁻¹ * (s:ℝ) * Erdos289.External.logTwo m ≤ (m:ℝ)/2 := by
    have hslm : (s:ℝ) * Real.log (m:ℝ) ≤ c * Real.log 2 / 2 * (m:ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogm_pos] at hslog
      linarith
    have hlhs : c⁻¹ * (s:ℝ) * Erdos289.External.logTwo m
        = (s:ℝ) * Real.log m / (c * Real.log 2) := by
      rw [hlogTwo_eq]; field_simp
    have hrhs : c * Real.log 2 / 2 * (m:ℝ) / (c * Real.log 2) = (m:ℝ)/2 := by
      field_simp
    rw [hlhs, ← hrhs]
    gcongr
  refine ⟨J, J', P, hJA, hPproper, hPdil, hPne, hPD, hJ'J, ?_, hJmem, h0mem, hJ'card, x, hxdilate⟩
  have : (m:ℝ) - c⁻¹ * (s:ℝ) * Erdos289.External.logTwo m ≤ (J.card:ℝ) := hJcard
  linarith

/-- Helper: an arithmetic progression `x + t * δ`, `t = 0, …, n-1`, with `δ` a unit mod `q`
and `n ≥ q`, covers every residue class mod `q` (paper's final paragraph). -/
lemma ap_unit_covers {q : ℕ} [NeZero q] (x δ : ℤ) (hδ : IsUnit (δ : ZMod q)) (n : ℕ)
    (hn : q ≤ n) : ∀ r : ZMod q, ∃ t : ℕ, t < n ∧ ((x + t * δ : ℤ) : ZMod q) = r := by
  intro r
  set t0 : ZMod q := (δ:ZMod q)⁻¹ * (r - (x:ZMod q)) with ht0def
  refine ⟨t0.val, lt_of_lt_of_le (ZMod.val_lt t0) hn, ?_⟩
  have hcast : ((t0.val : ℕ) : ZMod q) = t0 := ZMod.natCast_rightInverse t0
  have hinv : (δ:ZMod q)⁻¹ * (δ:ZMod q) = 1 := ZMod.inv_mul_of_unit _ hδ
  push_cast
  rw [hcast, ht0def]
  calc (x:ZMod q) + ((δ:ZMod q)⁻¹ * (r - (x:ZMod q))) * (δ:ZMod q)
      = (x:ZMod q) + (r - (x:ZMod q)) * ((δ:ZMod q)⁻¹ * (δ:ZMod q)) := by ring
    _ = (x:ZMod q) + (r - (x:ZMod q)) * 1 := by rw [hinv]
    _ = r := by ring

/-- **Step 2** of the proof of Lemma 3 (coordinate extraction). Given a GAP `P`, an integer
coordinate vector `v` representing `0 ∈ P.set`, and any `j ∈ P.set`, `j` decomposes as a sum
over the *active* coordinates (those with `⌈α i⌉ < ⌊β i⌋`) of `(n i - v i) * d i`, with
`|n i - v i|` bounded by `a i := ⌊β i⌋ - ⌈α i⌉` on active coordinates, and `n i = v i` exactly
on inactive coordinates (whose contribution therefore cancels after subtracting the
representation of `0`). -/
lemma gap_active_repr (P : GAP) (v : Fin P.D → ℤ)
    (hv : ∀ i, P.α i ≤ (v i:ℝ) ∧ (v i:ℝ) ≤ P.β i) (hv0 : ∑ i, v i * P.d i = 0)
    (j : ℤ) (hj : j ∈ P.set) :
    ∃ n : Fin P.D → ℤ, (∀ i, P.α i ≤ (n i:ℝ) ∧ (n i:ℝ) ≤ P.β i) ∧
      j = ∑ i ∈ Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋), (n i - v i) * P.d i ∧
      (∀ i, ⌈P.α i⌉ < ⌊P.β i⌋ → |n i - v i| ≤ ⌊P.β i⌋ - ⌈P.α i⌉) ∧
      (∀ i, ¬ (⌈P.α i⌉ < ⌊P.β i⌋) → n i = v i) := by
  obtain ⟨n, hn, hjeq⟩ := hj
  have hℓv : ∀ i, ⌈P.α i⌉ ≤ v i := fun i => Int.ceil_le.2 (hv i).1
  have huv : ∀ i, v i ≤ ⌊P.β i⌋ := fun i => Int.le_floor.2 (hv i).2
  have hℓn : ∀ i, ⌈P.α i⌉ ≤ n i := fun i => Int.ceil_le.2 (hn i).1
  have hun : ∀ i, n i ≤ ⌊P.β i⌋ := fun i => Int.le_floor.2 (hn i).2
  have hinactive : ∀ i, ¬ (⌈P.α i⌉ < ⌊P.β i⌋) → n i = v i := by
    intro i hi
    have hle : ⌈P.α i⌉ ≤ ⌊P.β i⌋ := le_trans (hℓv i) (huv i)
    have heq : ⌈P.α i⌉ = ⌊P.β i⌋ := le_antisymm hle (not_lt.mp hi)
    have h1 : n i = ⌈P.α i⌉ := le_antisymm (heq ▸ hun i) (hℓn i)
    have h2 : v i = ⌈P.α i⌉ := le_antisymm (heq ▸ huv i) (hℓv i)
    rw [h1, h2]
  refine ⟨n, hn, ?_, ?_, hinactive⟩
  · have hstep : j = ∑ i, (n i - v i) * P.d i := by
      rw [hjeq]
      have : ∑ i, v i * P.d i = 0 := hv0
      have hsub : ∑ i, (n i - v i) * P.d i = (∑ i, n i * P.d i) - ∑ i, v i * P.d i := by
        rw [← Finset.sum_sub_distrib]
        congr 1; ext i; ring
      rw [hsub, this, sub_zero]
    rw [hstep]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)]
    have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ (⌈P.α i⌉ < ⌊P.β i⌋)), (n i - v i) * P.d i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter] at hi
      rw [hinactive i hi.2]
      ring
    rw [hzero, add_zero]
  · intro i hi
    have h1 := hℓn i
    have h2 := hun i
    have h3 := hℓv i
    have h4 := huv i
    rw [abs_le]
    constructor <;> omega

/-- At least one coordinate of a GAP `P` is active, given `P.set` contains `0` (via `v`) and a
nonzero integer `j` (paper: "There is at least one active coordinate, because `P` contains
zero and the nonzero elements of `J`"). -/
lemma gap_active_nonempty (P : GAP) (v : Fin P.D → ℤ)
    (hv : ∀ i, P.α i ≤ (v i:ℝ) ∧ (v i:ℝ) ≤ P.β i) (hv0 : ∑ i, v i * P.d i = 0)
    (j : ℤ) (hj : j ∈ P.set) (hjne : j ≠ 0) :
    (Finset.univ.filter (fun i : Fin P.D => ⌈P.α i⌉ < ⌊P.β i⌋)).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  obtain ⟨n, hn, hjeq, hbound, hinact⟩ := gap_active_repr P v hv hv0 j hj
  rw [h] at hjeq
  simp at hjeq
  exact hjne hjeq

/-- **Face counting (4.3)**. Fixing the inactive coordinates of the dilate `t • P`
(`t = c * s`) at an admissible vector `w`, and letting the active coordinates range over
their dilated intervals, produces (via properness of the dilate) an injective map into any
set `S` containing `x + (dilate).set` and bounded in `[L, U]`; comparing cardinalities gives
`(t/2)^d * V ≤ U - L + 1`, where `d` is the number of active coordinates and
`V = ∏ (active) (⌊β i⌋ - ⌈α i⌉)`. -/
lemma gap_dilate_face_count (P : GAP) (t : ℝ) (ht2 : 2 ≤ t)
    (hPdil : (GAP.dilate t P).Proper)
    (w : Fin P.D → ℤ)
    (hw : ∀ i, ¬ (⌈P.α i⌉ < ⌊P.β i⌋) → t * P.α i ≤ (w i:ℝ) ∧ (w i:ℝ) ≤ t * P.β i)
    (S : Set ℤ) (x L U : ℤ) (hLU_le : L ≤ U) (hLU : ∀ z ∈ S, L ≤ z ∧ z ≤ U)
    (hdilate : ∀ y ∈ (GAP.dilate t P).set, x + y ∈ S) :
    ((t/2) ^ (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card *
        (∏ i ∈ Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋), (⌊P.β i⌋ - ⌈P.α i⌉).toNat : ℝ))
      ≤ (U - L + 1 : ℝ) := by
  classical
  set Active : Finset (Fin P.D) := Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋) with hActive
  set Box : Finset (Fin P.D → ℤ) :=
    Fintype.piFinset (fun i => if i ∈ Active then Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋ else {w i}) with hBox
  have htpos : (0:ℝ) < t := by linarith
  have hmem_dilate : ∀ e ∈ Box, ∀ i, t * P.α i ≤ (e i : ℝ) ∧ (e i:ℝ) ≤ t * P.β i := by
    intro e he i
    rw [hBox, Fintype.mem_piFinset] at he
    have hei := he i
    by_cases hiA : i ∈ Active
    · simp only [hiA, ite_true, Finset.mem_Icc] at hei
      refine ⟨?_, ?_⟩
      · calc t * P.α i ≤ (⌈t*P.α i⌉ : ℝ) := Int.le_ceil _
          _ ≤ (e i : ℝ) := by exact_mod_cast hei.1
      · calc (e i:ℝ) ≤ (⌊t*P.β i⌋:ℝ) := by exact_mod_cast hei.2
          _ ≤ t * P.β i := Int.floor_le _
    · simp only [hiA, ite_false, Finset.mem_singleton] at hei
      rw [hei]
      exact hw i (by simpa [hActive] using hiA)
  have hmapsto : ∀ e ∈ Box, x + ∑ i, e i * P.d i ∈ Finset.Icc L U := by
    intro e he
    have hy : (∑ i, e i * P.d i) ∈ (GAP.dilate t P).set := ⟨e, hmem_dilate e he, rfl⟩
    have hin := hdilate _ hy
    have hb := hLU _ hin
    simp only [Finset.mem_Icc]
    exact hb
  have hinj : Set.InjOn (fun e : Fin P.D → ℤ => x + ∑ i, e i * P.d i) Box := by
    intro e1 he1 e2 he2 heq
    simp only at heq
    have heq' : ∑ i, e1 i * P.d i = ∑ i, e2 i * P.d i := by linarith [heq]
    exact hPdil e1 e2 (hmem_dilate e1 he1) (hmem_dilate e2 he2) heq'
  have hcard_le : Box.card ≤ (Finset.Icc L U).card :=
    Finset.card_le_card_of_injOn _ hmapsto hinj
  have hboxcard : Box.card = ∏ i ∈ Active, (Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card := by
    rw [hBox, Fintype.card_piFinset]
    simp only [apply_ite Finset.card, Finset.card_singleton]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hIcccard : ((Finset.Icc L U).card : ℝ) = (U:ℝ) - (L:ℝ) + 1 := by
    have h1 : (Finset.Icc L U).card = (U+1-L).toNat := Int.card_Icc _ _
    have h2 : ((U+1-L).toNat : ℝ) = ((U+1-L : ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ U + 1 - L)
    rw [h1, h2]; push_cast; ring
  have hfactor : ∀ i ∈ Active, (t/2) * ((⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ)) ≤
      ((Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card : ℝ) := by
    intro i hiA0
    have hiA : ⌈P.α i⌉ < ⌊P.β i⌋ := by
      simpa [hActive] using hiA0
    have ha1 : (1:ℤ) ≤ ⌊P.β i⌋ - ⌈P.α i⌉ := by omega
    have haR : (1:ℝ) ≤ (⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ) := by
      have : ((1:ℤ):ℝ) ≤ ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ):ℝ) := by exact_mod_cast ha1
      push_cast at this; linarith
    have hBA : (P.β i - P.α i) ≥ (⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ) := by
      have e1 : ((⌊P.β i⌋:ℤ):ℝ) ≤ P.β i := Int.floor_le _
      have e2 : P.α i ≤ (⌈P.α i⌉:ℝ) := Int.le_ceil _
      linarith
    have hmul1 : t * ((⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ)) ≤ t*P.β i - t*P.α i := by
      have h := mul_le_mul_of_nonneg_left hBA htpos.le
      nlinarith [h]
    have hmul2 : (2:ℝ) ≤ t * ((⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ)) :=
      calc (2:ℝ) = 2 * 1 := by ring
        _ ≤ t * ((⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ)) := mul_le_mul ht2 haR (by norm_num) (by linarith)
    have hfl : t*P.β i < (⌊t*P.β i⌋:ℝ) + 1 := Int.lt_floor_add_one _
    have hce : (⌈t*P.α i⌉:ℝ) < t*P.α i + 1 := Int.ceil_lt_add_one _
    have hZpos : (0:ℤ) ≤ ⌊t*P.β i⌋ + 1 - ⌈t*P.α i⌉ := by
      have hposR : (0:ℝ) < (⌊t*P.β i⌋:ℝ) + 1 - (⌈t*P.α i⌉:ℝ) := by nlinarith [hmul1, hmul2, hfl, hce]
      have hz : (0:ℤ) < ⌊t*P.β i⌋ + 1 - ⌈t*P.α i⌉ := by exact_mod_cast hposR
      omega
    have hcardeq : ((Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card:ℝ)
        = (⌊t*P.β i⌋:ℝ) + 1 - (⌈t*P.α i⌉:ℝ) := by
      have h1 : (Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card = (⌊t*P.β i⌋+1-⌈t*P.α i⌉).toNat :=
        Int.card_Icc _ _
      have h2 : ((⌊t*P.β i⌋+1-⌈t*P.α i⌉).toNat : ℝ) = ((⌊t*P.β i⌋+1-⌈t*P.α i⌉ : ℤ):ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hZpos
      rw [h1, h2]; push_cast; ring
    rw [hcardeq]
    linarith [hmul1, hmul2, hfl, hce]
  have htoNatcast : ∀ i ∈ Active, ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ).toNat:ℝ) = (⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ) := by
    intro i hiA0
    have hiA : ⌈P.α i⌉ < ⌊P.β i⌋ := by simpa [hActive] using hiA0
    have h2 : ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ).toNat:ℝ) = ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ⌊P.β i⌋ - ⌈P.α i⌉)
    rw [h2]; push_cast; ring
  have hprod_le : (t/2)^Active.card * (∏ i ∈ Active, ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ).toNat:ℝ)) ≤
      ∏ i ∈ Active, ((Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card : ℝ) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i hi
      rw [htoNatcast i hi]
      have hiA : ⌈P.α i⌉ < ⌊P.β i⌋ := by simpa [hActive] using hi
      have h1 : (1:ℤ) ≤ ⌊P.β i⌋ - ⌈P.α i⌉ := by omega
      have h2 : (1:ℝ) ≤ (⌊P.β i⌋:ℝ) - (⌈P.α i⌉:ℝ) := by
        have h3 : ((1:ℤ):ℝ) ≤ ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ):ℝ) := by exact_mod_cast h1
        push_cast at h3; linarith
      nlinarith [h2, htpos]
    · intro i hi
      rw [htoNatcast i hi]
      exact hfactor i hi
  calc (t/2)^Active.card * (∏ i ∈ Active, ((⌊P.β i⌋ - ⌈P.α i⌉:ℤ).toNat:ℝ))
      ≤ ∏ i ∈ Active, ((Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card : ℝ) := hprod_le
    _ = ((∏ i ∈ Active, (Finset.Icc ⌈t*P.α i⌉ ⌊t*P.β i⌋).card : ℕ) : ℝ) := by push_cast; ring
    _ = ((Box.card : ℕ):ℝ) := by rw [hboxcard]
    _ ≤ ((Finset.Icc L U).card : ℝ) := by exact_mod_cast hcard_le
    _ = (U - L + 1 : ℝ) := by rw [hIcccard]

/-- A real interval `[A, B]` (with `⌈A⌉ < ⌊B⌋`, i.e. containing at least two integers) dilated
by `t ≥ 2` contains at least `(t/2) * (⌊B⌋ - ⌈A⌉)` integers. Used for the one-dimensional face
in the `d = 1` conclusion of `lemma3_core`. -/
lemma gap_interval_count_ge (A B t : ℝ) (ht2 : 2 ≤ t) (hAB : ⌈A⌉ < ⌊B⌋) :
    (t/2) * ((⌊B⌋:ℝ) - (⌈A⌉:ℝ)) ≤ ((Finset.Icc ⌈t*A⌉ ⌊t*B⌋).card : ℝ) := by
  have htpos : (0:ℝ) < t := by linarith
  have ha1 : (1:ℤ) ≤ ⌊B⌋ - ⌈A⌉ := by omega
  have haR : (1:ℝ) ≤ (⌊B⌋:ℝ) - (⌈A⌉:ℝ) := by
    have : ((1:ℤ):ℝ) ≤ ((⌊B⌋ - ⌈A⌉:ℤ):ℝ) := by exact_mod_cast ha1
    push_cast at this
    linarith
  have hBA : (B - A) ≥ (⌊B⌋:ℝ) - (⌈A⌉:ℝ) := by
    have e1 : ((⌊B⌋:ℤ):ℝ) ≤ B := Int.floor_le _
    have e2 : A ≤ (⌈A⌉:ℝ) := Int.le_ceil _
    linarith
  have hmul1 : t * ((⌊B⌋:ℝ) - (⌈A⌉:ℝ)) ≤ t*B - t*A := by
    have h := mul_le_mul_of_nonneg_left hBA htpos.le
    nlinarith [h]
  have hmul2 : (2:ℝ) ≤ t * ((⌊B⌋:ℝ) - (⌈A⌉:ℝ)) :=
    calc (2:ℝ) = 2 * 1 := by ring
      _ ≤ t * ((⌊B⌋:ℝ) - (⌈A⌉:ℝ)) := mul_le_mul ht2 haR (by norm_num) (by linarith)
  have hfl : t*B < (⌊t*B⌋:ℝ) + 1 := Int.lt_floor_add_one _
  have hce : (⌈t*A⌉:ℝ) < t*A + 1 := Int.ceil_lt_add_one _
  have hZpos : (0:ℤ) ≤ ⌊t*B⌋ + 1 - ⌈t*A⌉ := by
    have hposR : (0:ℝ) < (⌊t*B⌋:ℝ) + 1 - (⌈t*A⌉:ℝ) := by nlinarith [hmul1, hmul2, hfl, hce]
    have hz : (0:ℤ) < ⌊t*B⌋ + 1 - ⌈t*A⌉ := by exact_mod_cast hposR
    omega
  have hcardeq : ((Finset.Icc ⌈t*A⌉ ⌊t*B⌋).card:ℝ) = (⌊t*B⌋:ℝ) + 1 - (⌈t*A⌉:ℝ) := by
    have h1 : (Finset.Icc ⌈t*A⌉ ⌊t*B⌋).card = (⌊t*B⌋+1-⌈t*A⌉).toNat := Int.card_Icc _ _
    have h2 : ((⌊t*B⌋+1-⌈t*A⌉).toNat : ℝ) = ((⌊t*B⌋+1-⌈t*A⌉ : ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hZpos
    rw [h1, h2]; push_cast; ring
  rw [hcardeq]
  have hstep1 : (⌊t*B⌋:ℝ) + 1 - (⌈t*A⌉:ℝ) > t*B - t*A - 1 := by linarith [hfl, hce]
  have hstep2 : t*B - t*A - 1 ≥ t*((⌊B⌋:ℝ)-(⌈A⌉:ℝ)) - 1 := by linarith [hmul1]
  have hstep3 : t*((⌊B⌋:ℝ)-(⌈A⌉:ℝ)) - 1 ≥ (t/2)*((⌊B⌋:ℝ)-(⌈A⌉:ℝ)) := by linarith [hmul2]
  linarith [hstep1, hstep2, hstep3]

/-- **Divisor-counting step** (paper's step 5). If every `j ∈ J` (naturals `< q`) has a witness
integer `h j`, of absolute value at most `R`, congruent to `T * j` mod `q` (`T` a fixed integer
with `1 ≤ T < q`), and a positive integer `i0 j ≤ Imax` inverse to `j` mod `q`, then `J` is
small: writing `N w := q * w + T`, the pair `(z j, i0 j)` — where `z j` is the (bounded)
integer with `i0 j * h j = N (z j)` — is injective in `j` (since `i0 j` alone already
determines `j`, via `i0 j`'s role as an inverse of `j` and `j < q`), and for each of the
`O(Imax * R / q)` values `z j` can take, `i0 j` must be one of the (boundedly many, via `D`)
divisors of `|N (z j)|`. -/
lemma divisor_count_bound {q : ℕ} (hq2 : 2 ≤ q) (T : ℤ) (hT1 : 1 ≤ T) (hTq : T < q)
    (R Imax : ℝ) (hR : 0 ≤ R) (hImax : 0 ≤ Imax)
    (J : Finset ℕ) (hJlt : ∀ j ∈ J, j < q)
    (h : ℕ → ℤ) (hh : ∀ j ∈ J, |(h j : ℝ)| ≤ R ∧ ((h j : ZMod q) = (T : ZMod q) * (j : ZMod q)))
    (i0 : ℕ → ℕ) (hi0pos : ∀ j ∈ J, 0 < i0 j) (hi0le : ∀ j ∈ J, (i0 j : ℝ) ≤ Imax)
    (hi0inv : ∀ j ∈ J, (i0 j : ZMod q) * (j : ZMod q) = 1)
    (D : ℝ → ℝ) (hDmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → D x ≤ D y)
    (hDdiv : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ D n) :
    (J.card : ℝ) ≤ (2 * (⌈Imax * R / q + 1⌉₊ : ℝ) + 1) *
      D ((q:ℝ) * ((⌈Imax * R / q + 1⌉₊ : ℝ) + 1)) := by
  have : NeZero q := ⟨by omega⟩
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set Z : ℕ := ⌈Imax * R / q + 1⌉₊ with hZdef
  have hZR : Imax * R / q + 1 ≤ (Z:ℝ) := Nat.le_ceil _
  have hcong : ∀ j ∈ J, (((i0 j:ℤ) * h j - T : ℤ) : ZMod q) = 0 := by
    intro j hj
    have h1 : (h j : ZMod q) = (T:ZMod q) * (j:ZMod q) := (hh j hj).2
    push_cast
    rw [h1]
    have heq2 : ((i0 j:ℕ):ZMod q) * ((T:ZMod q)*(j:ZMod q))
        = (T:ZMod q) * (((i0 j:ℕ):ZMod q) * (j:ZMod q)) := by ring
    rw [heq2, hi0inv j hj, mul_one, sub_self]
  have hex : ∀ j, j ∈ J → ∃ zz : ℤ, (i0 j:ℤ) * h j - T = q * zz := by
    intro j hj
    have hd : (q:ℤ) ∣ ((i0 j:ℤ) * h j - T) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (hcong j hj)
    obtain ⟨zz, hzz⟩ := hd
    exact ⟨zz, hzz⟩
  set z : ℕ → ℤ := fun j => if hj : j ∈ J then (hex j hj).choose else 0 with hzdef
  have hzspec : ∀ j ∈ J, (i0 j:ℤ) * h j - T = q * z j := by
    intro j hj
    simp only [hzdef, dite_eq_left_of_eq_true (eq_true hj)]
    exact (hex j hj).choose_spec
  have hzbound : ∀ j ∈ J, |(z j : ℝ)| ≤ (Z:ℝ) := by
    intro j hj
    have heq := hzspec j hj
    have heqR : (q:ℝ) * (z j : ℝ) = (i0 j:ℝ) * (h j : ℝ) - (T:ℝ) := by exact_mod_cast heq.symm
    have h2 : |(i0 j:ℝ) * (h j:ℝ)| = (i0 j:ℝ) * |(h j:ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by exact_mod_cast (hi0pos j hj).le)]
    have h3 : |(T:ℝ)| = (T:ℝ) := abs_of_pos (by exact_mod_cast hT1 : (0:ℝ) < T)
    have hb1 : |(i0 j:ℝ) * (h j:ℝ) - (T:ℝ)| ≤ (i0 j:ℝ) * |(h j:ℝ)| + (T:ℝ) := by
      calc |(i0 j:ℝ) * (h j:ℝ) - (T:ℝ)| = |(i0 j:ℝ)*(h j:ℝ) + (-(T:ℝ))| := by ring_nf
        _ ≤ |(i0 j:ℝ)*(h j:ℝ)| + |(-(T:ℝ))| := abs_add_le _ _
        _ = (i0 j:ℝ)*|(h j:ℝ)| + (T:ℝ) := by rw [h2, abs_neg, h3]
    have hqz_abs : |(q:ℝ) * (z j:ℝ)| ≤ (i0 j:ℝ) * |(h j:ℝ)| + (T:ℝ) := heqR ▸ hb1
    have hle1 : (i0 j:ℝ) * |(h j:ℝ)| + (T:ℝ) < Imax * R + q := by
      have hi0 := hi0le j hj
      have hhR := (hh j hj).1
      have hi0pos' : (0:ℝ) ≤ (i0 j:ℝ) := by exact_mod_cast (hi0pos j hj).le
      have : (i0 j:ℝ) * |(h j:ℝ)| ≤ Imax * R := by
        calc (i0 j:ℝ) * |(h j:ℝ)| ≤ Imax * |(h j:ℝ)| := by
              apply mul_le_mul_of_nonneg_right hi0 (abs_nonneg _)
          _ ≤ Imax * R := by apply mul_le_mul_of_nonneg_left hhR hImax
      have hTqR : (T:ℝ) < (q:ℝ) := by exact_mod_cast hTq
      linarith
    have hqz_lt : |(q:ℝ) * (z j:ℝ)| < Imax * R + q := lt_of_le_of_lt hqz_abs hle1
    have hqz_abs2 : (q:ℝ) * |(z j:ℝ)| < Imax * R + q := by
      rwa [abs_mul, abs_of_nonneg hqR.le] at hqz_lt
    have hdiv : |(z j:ℝ)| < (Imax*R+(q:ℝ))/q := by
      rw [lt_div_iff₀ hqR]; linarith [hqz_abs2]
    have heqdiv : (Imax*R+(q:ℝ))/q = Imax*R/q + 1 := by field_simp
    linarith [hdiv, heqdiv, hZR]
  have hzboundZ : ∀ j ∈ J, z j ∈ Finset.Icc (-(Z:ℤ)) (Z:ℤ) := by
    intro j hj
    have hb := hzbound j hj
    rw [Finset.mem_Icc]
    have h1 : -(Z:ℝ) ≤ (z j:ℝ) ∧ (z j:ℝ) ≤ (Z:ℝ) := abs_le.mp hb
    constructor
    · have : ((-(Z:ℤ)):ℝ) ≤ (z j:ℝ) := by push_cast; linarith [h1.1]
      exact_mod_cast this
    · exact_mod_cast h1.2
  set Icc' : Finset ℤ := Finset.Icc (-(Z:ℤ)) (Z:ℤ) with hIccdef
  have hNne : ∀ w ∈ Icc', (q:ℤ) * w + T ≠ 0 := by
    intro w _ hcontra
    have hdvd2 : (q:ℤ) ∣ T := ⟨-w, by linarith⟩
    have hle : (q:ℤ) ≤ T := Int.le_of_dvd (by linarith) hdvd2
    linarith
  have hNbound : ∀ w ∈ Icc', ((q:ℤ)*w+T).natAbs ≤ q*(Z+1) := by
    intro w hw
    rw [hIccdef, Finset.mem_Icc] at hw
    have hwabs : |w| ≤ (Z:ℤ) := abs_le.mpr hw
    have h1 : |(q:ℤ)*w| ≤ (q:ℤ)*(Z:ℤ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (q:ℤ))]
      exact mul_le_mul_of_nonneg_left hwabs (by positivity)
    have h3 : |(q:ℤ)*w + T| ≤ (q:ℤ)*(Z:ℤ) + T := by
      calc |(q:ℤ)*w+T| ≤ |(q:ℤ)*w| + |T| := by
            calc |(q:ℤ)*w+T| = |(q:ℤ)*w + T| := rfl
              _ ≤ |(q:ℤ)*w| + |T| := abs_add_le _ _
        _ ≤ (q:ℤ)*(Z:ℤ) + T := by
            have := abs_of_pos (by linarith : (0:ℤ) < T)
            linarith [h1, this.le]
    have h4 : (q:ℤ)*(Z:ℤ) + T ≤ (q:ℤ)*((Z:ℤ)+1) := by nlinarith [hTq]
    have h5 : |(q:ℤ)*w+T| ≤ (q:ℤ)*((Z:ℤ)+1) := le_trans h3 h4
    rw [Int.abs_eq_natAbs] at h5
    have h6 : (((q:ℤ)*w+T).natAbs : ℤ) ≤ ((q*(Z+1):ℕ):ℤ) := by push_cast; linarith [h5]
    exact_mod_cast h6
  have hinj : Set.InjOn (fun j => (z j, i0 j)) J := by
    intro j1 hj1 j2 hj2 heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hi0eq⟩ := heq
    have hu1 : (i0 j1 : ZMod q) * (j1:ZMod q) = 1 := hi0inv j1 hj1
    have hu2 : (i0 j1 : ZMod q) * (j2:ZMod q) = 1 := by
      rw [hi0eq]; exact hi0inv j2 hj2
    have hunit : IsUnit ((i0 j1 : ℕ) : ZMod q) := IsUnit.of_mul_eq_one _ hu1
    have hj12 : (j1 : ZMod q) = (j2:ZMod q) := hunit.mul_left_cancel (hu1.trans hu2.symm)
    have h4 := congrArg ZMod.val hj12
    rwa [ZMod.val_cast_of_lt (hJlt j1 hj1), ZMod.val_cast_of_lt (hJlt j2 hj2)] at h4
  set Target : Finset (ℤ × ℕ) :=
    Icc'.biUnion (fun w => (((q:ℤ)*w+T).natAbs.divisors).image (fun i => (w, i))) with hTargetdef
  have hmapsto : ∀ j ∈ J, (z j, i0 j) ∈ Target := by
    intro j hj
    rw [hTargetdef, Finset.mem_biUnion]
    refine ⟨z j, hzboundZ j hj, ?_⟩
    rw [Finset.mem_image]
    refine ⟨i0 j, ?_, rfl⟩
    rw [Nat.mem_divisors]
    have hNj : (q:ℤ)*(z j) + T = (i0 j:ℤ) * h j := by linarith [hzspec j hj]
    have hdvdZ : (i0 j:ℤ) ∣ (q:ℤ)*(z j)+T := ⟨h j, hNj⟩
    refine ⟨?_, fun hz0 => hNne (z j) (hzboundZ j hj) (Int.natAbs_eq_zero.mp hz0)⟩
    have h7 := Int.natAbs_dvd_natAbs.mpr hdvdZ
    simpa using h7
  have hcardle : (J.card:ℝ) ≤ (Target.card:ℝ) := by
    have := Finset.card_le_card_of_injOn (fun j => (z j, i0 j)) hmapsto hinj
    exact_mod_cast this
  have hIcc'card : Icc'.card = 2*Z+1 := by
    rw [hIccdef, Int.card_Icc]
    omega
  have hTargetcard : (Target.card:ℝ) ≤ (2*(Z:ℝ)+1) * D ((q:ℝ)*((Z:ℝ)+1)) := by
    have hbiunion : Target.card
        ≤ ∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.image (fun i => (w,i))).card :=
      Finset.card_biUnion_le
    have hsum2 : ∀ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.card : ℝ) ≤ D ((q:ℝ)*((Z:ℝ)+1)) := by
      intro w hw
      have hn1 : 1 ≤ ((q:ℤ)*w+T).natAbs := by
        have hne := hNne w hw
        omega
      have hstep := hDdiv _ hn1
      have hle : (((q:ℤ)*w+T).natAbs : ℝ) ≤ (q:ℝ)*((Z:ℝ)+1) := by
        have hb := hNbound w hw
        have : (((q:ℤ)*w+T).natAbs : ℝ) ≤ ((q*(Z+1):ℕ):ℝ) := by exact_mod_cast hb
        push_cast at this; linarith
      exact hstep.trans (hDmono _ _ (by positivity) hle)
    have hstep1 : (Target.card : ℝ)
        ≤ (∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.image (fun i => (w,i))).card : ℕ) := by
      exact_mod_cast hbiunion
    have hstep2 : (∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.image (fun i => (w,i))).card : ℕ)
        ≤ (∑ w ∈ Icc', ((q:ℤ)*w+T).natAbs.divisors.card : ℕ) := by
      apply Finset.sum_le_sum
      intro w _
      exact Finset.card_image_le
    have hstep3 : ((∑ w ∈ Icc', ((q:ℤ)*w+T).natAbs.divisors.card : ℕ) : ℝ)
        = ∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.card : ℝ) := by push_cast; ring
    have hstep4 : ∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.card : ℝ)
        ≤ ∑ w ∈ Icc', D ((q:ℝ)*((Z:ℝ)+1)) := Finset.sum_le_sum hsum2
    have hstep5 : ∑ _w ∈ Icc', D ((q:ℝ)*((Z:ℝ)+1)) = (Icc'.card : ℝ) * D ((q:ℝ)*((Z:ℝ)+1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hstep6 : (Icc'.card : ℝ) = 2*(Z:ℝ)+1 := by rw [hIcc'card]; push_cast; ring
    calc (Target.card:ℝ) ≤ ((∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.image (fun i => (w,i))).card : ℕ):ℝ) := by
          exact_mod_cast hstep1
      _ ≤ ((∑ w ∈ Icc', ((q:ℤ)*w+T).natAbs.divisors.card : ℕ):ℝ) := by exact_mod_cast hstep2
      _ = ∑ w ∈ Icc', (((q:ℤ)*w+T).natAbs.divisors.card : ℝ) := hstep3
      _ ≤ ∑ _w ∈ Icc', D ((q:ℝ)*((Z:ℝ)+1)) := hstep4
      _ = (Icc'.card : ℝ) * D ((q:ℝ)*((Z:ℝ)+1)) := hstep5
      _ = (2*(Z:ℝ)+1) * D ((q:ℝ)*((Z:ℝ)+1)) := by rw [hstep6]
  calc (J.card:ℝ) ≤ (Target.card:ℝ) := hcardle
    _ ≤ (2*(Z:ℝ)+1) * D ((q:ℝ)*((Z:ℝ)+1)) := hTargetcard


end Erdos289
