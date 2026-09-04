import Erdos289.Defs
import Erdos289.External

/-!
# Lemma 3: sparse modular inverse subsets cover all residues

For fixed `0 < ε < 1` and every sufficiently large prime power `q`: if
`I ⊆ [q^ε, 2q^ε]` consists of integers coprime to `q` and `|I| ≥ q^(7ε/8)`, then every residue
modulo `q` is a sum of inverses of at most `q^(ε/2)` distinct members of `I`.

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
* `lemma3_core`: assembles the pieces above into the full argument (paper's steps 2–6: active
  coordinates, face counting (3.1), the `d = 1` dichotomy, and the final covering conclusion).
  Three genuinely irreducible gaps remain as individually documented `sorry`s inside its proof
  (not as separate lemma statements, since those would be false without the missing context) —
  see its docstring, "Further gaps discovered while formalizing this lemma": (1) a magnitude
  bound on `J'`'s elements needed for the face-counting bound, (2) the simultaneous-approximation
  / divisor-bound argument (paper's steps 4–5, (3.2)) forcing `d = 1` and a quantitative lower
  bound on `V`, and (3) existence of admissible dilated-integer points on inactive coordinates.
  All other steps (coordinate extraction, face counting (3.1) itself, the `d = 1` case's
  one-dimensional covering argument) are proved in full from these three facts.

`lemma3` itself is assembled from these pieces with no further `sorry`.
-/

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
`2 q^ε < q` (so that `I`'s elements are `< q`), and, for `m` in the admissible range
`[q^(7ε/8), 2q^ε]` (i.e. `m = |I|`, using the interval and cardinality hypotheses on `I`),
writing `s := ⌊q^(ε/2)⌋₊`: `q ≤ m^(2/ε)`, `m^(1/3) ≤ s`, and `s ≤ c m / log m`, matching
exactly the hypotheses `cfhmpsv_structure` needs for `β = 2/ε`, `η = 1/3`. -/
lemma lemma3_growth_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 < c) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q →
      2 * (q:ℝ) ^ ε < q ∧
      ∀ m : ℕ, (q:ℝ) ^ (7*ε/8) ≤ m → (m:ℝ) ≤ 2*(q:ℝ)^ε →
        (q:ℝ) ≤ (m:ℝ) ^ (2/ε) ∧
        (m:ℝ) ^ ((1:ℝ)/3) ≤ (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ) ∧
        (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ) ≤ c * m / Real.log m := by
  have hA : ∀ᶠ q : ℕ in atTop, 3 * (q:ℝ)^ε + 0 ≤ (q:ℝ)^(1:ℝ) :=
    eventually_rpow_dominates ε 1 3 0 hε0 hε1
  have hB : ∀ᶠ q : ℕ in atTop,
      (2:ℝ)^((1:ℝ)/3) * (q:ℝ)^(ε/3) + 1 ≤ (q:ℝ)^(ε/2) :=
    eventually_rpow_dominates (ε/3) (ε/2) (2^((1:ℝ)/3)) 1 (by linarith) (by linarith)
  have hC : ∀ᶠ q : ℕ in atTop, Real.log 2 + ε * Real.log q ≤ c * (q:ℝ)^(3*ε/8) := by
    have h1 := eventually_log_le_rpow (3*ε/8) (c / (2*ε)) (by linarith) (by positivity)
    have h2 : Tendsto (fun q : ℕ => (q:ℝ)^(3*ε/8)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [h1, h2.eventually_ge_atTop (2 * Real.log 2 / c)] with q hq1 hq2
    have h3 : Real.log 2 ≤ c/2 * (q:ℝ)^(3*ε/8) := by
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
  have hQ0 := (hA.and (hB.and (hC.and hD)))
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
    · calc (m:ℝ)^((1:ℝ)/3) ≤ (2*(q:ℝ)^ε)^((1:ℝ)/3) :=
            Real.rpow_le_rpow (by positivity) hm2 (by positivity)
        _ = (2:ℝ)^((1:ℝ)/3) * (q:ℝ)^(ε/3) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hqR.le]
            congr 2
            ring
        _ ≤ ⌊(q:ℝ)^(ε/2)⌋₊ := by
            have hsfloor : (q:ℝ)^(ε/2) < (⌊(q:ℝ)^(ε/2)⌋₊:ℝ) + 1 := Nat.lt_floor_add_one _
            linarith
    · -- ⌊q^(ε/2)⌋₊ ≤ c * m / log m
      have hlogm_pos : 0 < Real.log (m:ℝ) := Real.log_pos hm1
      have hlogm_le : Real.log (m:ℝ) ≤ Real.log 2 + ε * Real.log q := by
        calc Real.log (m:ℝ) ≤ Real.log (2*(q:ℝ)^ε) := Real.log_le_log hmR hm2
          _ = Real.log 2 + Real.log ((q:ℝ)^ε) := Real.log_mul (by norm_num) hqEps.ne'
          _ = Real.log 2 + ε * Real.log q := by rw [Real.log_rpow hqR]
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
`P.set`, and a translate of the dilate `(c * s) • P` contained in the subset sums of `J'`. -/
lemma lemma3_structure_apply (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ I : Finset ℕ,
        (∀ i ∈ I, (q : ℝ) ^ ε ≤ i ∧ (i : ℝ) ≤ 2 * (q : ℝ) ^ ε) →
        (∀ i ∈ I, Nat.Coprime i q) →
        (q : ℝ) ^ (7 * ε / 8) ≤ I.card →
        ∃ (J J' : Finset ℕ) (P : GAP),
          J ⊆ I.image (fun i : ℕ => ((i:ZMod q)⁻¹).val) ∧ P.Proper ∧
          (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ)) P).Proper ∧ P.D ≤ d₀ ∧ J' ⊆ J ∧
          ((I.card : ℝ)) / 2 ≤ (J.card : ℝ) ∧
          (∀ x ∈ J, (x : ℤ) ∈ P.set) ∧ (0:ℤ) ∈ P.set ∧
          J'.card ≤ ⌊(q:ℝ)^(ε/2)⌋₊ ∧
          ∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊ : ℝ)) P).set, x + y ∈ subsetSums J' := by
  obtain ⟨c, hc, d₀, hstruct⟩ := cfhmpsv_structure (2/ε) (by rw [lt_div_iff₀ hε0]; linarith) (1/3)
    (by norm_num) (by norm_num)
  rw [eventually_atTop] at hstruct
  obtain ⟨M₀, hM₀⟩ := hstruct
  obtain ⟨Q₁, hQ₁⟩ := lemma3_growth_bounds ε hε0 hε1 (c/2) (by positivity)
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
  have hm2q : (m:ℝ) ≤ 2*(q:ℝ)^ε := by
    have hIsub : I ⊆ Finset.Icc 1 ⌊2*(q:ℝ)^ε⌋₊ := by
      intro i hi
      have h1 := (hI1 i hi).1
      have h2 := (hI1 i hi).2
      have hqε : (0:ℝ) < (q:ℝ)^ε := Real.rpow_pos_of_pos hqR ε
      have hipos : 0 < i := by
        have : (0:ℝ) < (i:ℝ) := lt_of_lt_of_le hqε h1
        exact_mod_cast this
      simp only [Finset.mem_Icc]
      refine ⟨hipos, Nat.le_floor h2⟩
    have := Finset.card_le_card hIsub
    rw [Nat.card_Icc] at this
    have hfloor_le : (⌊2*(q:ℝ)^ε⌋₊ : ℝ) ≤ 2*(q:ℝ)^ε := Nat.floor_le (by positivity)
    have : (m:ℝ) ≤ ((⌊2*(q:ℝ)^ε⌋₊ + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast this
    simp only [Nat.add_sub_cancel] at this
    linarith
  obtain ⟨hq_mB, hm13, hslog⟩ := hbounds m hm7 hm2q
  set s := ⌊(q:ℝ)^(ε/2)⌋₊ with hsdef
  have hlogm_pos : 0 < Real.log (m:ℝ) := Real.log_pos hm1
  have hslog2 : (s:ℝ) ≤ c * (m:ℝ) / Real.log (m:ℝ) := by
    have : c/2 * (m:ℝ)/Real.log (m:ℝ) ≤ c * (m:ℝ)/Real.log (m:ℝ) := by
      gcongr
      nlinarith
    linarith
  obtain ⟨J, P, J', hJA, hPproper, hPdil, hPne, hPD, hJ'J, hJcard, hJmem, h0mem, hJ'card, x, hxdilate⟩ :=
    hM₀ m hmM0' q hq_mB A hAsub hAcard s hm13 hslog2
  have hshalf : c⁻¹ * (s:ℝ) * Real.log (m:ℝ) ≤ (m:ℝ)/2 := by
    have hslm : (s:ℝ) * Real.log (m:ℝ) ≤ c/2 * (m:ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogm_pos] at hslog
      linarith
    have := mul_le_mul_of_nonneg_left hslm (inv_nonneg.mpr hc.le)
    have hcancel : c⁻¹ * (c/2 * m) = m/2 := by field_simp
    calc c⁻¹ * (s:ℝ) * Real.log (m:ℝ) = c⁻¹ * ((s:ℝ) * Real.log (m:ℝ)) := by ring
      _ ≤ c⁻¹ * (c/2 * (m:ℝ)) := this
      _ = (m:ℝ)/2 := hcancel
  refine ⟨J, J', P, hJA, hPproper, hPdil, hPD, hJ'J, ?_, hJmem, h0mem, hJ'card, x, hxdilate⟩
  have : (m:ℝ) - c⁻¹ * (s:ℝ) * Real.log (m:ℝ) ≤ (J.card:ℝ) := hJcard
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

/-- **Face counting (3.1)**. Fixing the inactive coordinates of the dilate `t • P`
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

**Further gaps discovered while formalizing this lemma.** Three additional facts, each true
in the *concrete* application (`lemma3_structure_apply`/`lemma3`) but not derivable from
`lemma3_core`'s hypotheses in the abstract, are needed and are isolated below as individually
documented `sorry`s (per instructions, since `lemma3_core`'s statement itself may not be
changed): (1) the face-counting bound `(3.1)` needs `subsetSums J'` confined to an interval of
length `O(s q)`, which needs elements of `J'` bounded by (roughly) `q`; abstractly `J'` is an
arbitrary `Finset ℕ` with no such bound. (2) the divisor-count bound `(3.2)` needs, for each
`j ∈ J`, a bound `((j:ZMod q)⁻¹).val ≤ 2 q^ε` (matching `j`'s origin as `i⁻¹.val` for
`i ∈ I ⊆ [q^ε, 2q^ε]` in the concrete application); abstractly only `IsUnit (j:ZMod q)` is
known. (3) the face-counting construction needs, for each inactive coordinate, an admissible
*integer* point in the dilated (real-valued) interval `[t α i, t β i]`; since dilation scales
by an arbitrary real `t`, this is not automatic from `P`'s properness. -/
lemma lemma3_core (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 < c) (d₀ : ℕ) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ (m : ℕ) (J J' : Finset ℕ) (P : GAP),
        P.Proper → (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊:ℝ)) P).Proper → P.D ≤ d₀ → J' ⊆ J →
        (m:ℝ)/2 ≤ (J.card:ℝ) →
        (∀ x ∈ J, (x:ℤ) ∈ P.set) → (0:ℤ) ∈ P.set →
        (∀ j ∈ J, IsUnit ((j:ℕ):ZMod q)) →
        J'.card ≤ ⌊(q:ℝ)^(ε/2)⌋₊ →
        (q:ℝ)^(7*ε/8) ≤ (m:ℝ) →
        (∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (⌊(q:ℝ)^(ε/2)⌋₊:ℝ)) P).set, x + y ∈ subsetSums J') →
        ∀ r : ZMod q, ∃ T ⊆ J', ((∑ i ∈ T, (i:ℤ) : ℤ) : ZMod q) = r := by
  have hSbig : ∀ᶠ q:ℕ in atTop, 2/c + 1 ≤ (q:ℝ)^(ε/2) := by
    have h2 : Tendsto (fun q:ℕ => (q:ℝ)^(ε/2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    exact h2.eventually_ge_atTop (2/c+1)
  rw [eventually_atTop] at hSbig
  obtain ⟨Q₀, hQ₀⟩ := hSbig
  refine ⟨max Q₀ 2, fun q hqpp hq m J J' P hPproper hPdil hPD hJ'J hJcard hJmem h0mem hunits
    hJ'card hmcard hxdilate r => ?_⟩
  classical
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqQ0 : Q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hNZq : NeZero q := ⟨by omega⟩
  have hFact : Fact (1 < q) := ⟨by omega⟩
  set s : ℕ := ⌊(q:ℝ)^(ε/2)⌋₊ with hsdef
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0<q)
  have hspos : 2/c < (s:ℝ) := by
    have h1 := hQ₀ q hqQ0
    have h2 : (q:ℝ)^(ε/2) < (s:ℝ)+1 := by rw [hsdef]; exact Nat.lt_floor_add_one _
    linarith
  have ht2 : (2:ℝ) ≤ c * (s:ℝ) := by
    have hh := (div_lt_iff₀ hc).mp hspos
    linarith
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
    sorry
  -- GAP 1: elements of `J'` are bounded by `q` in the concrete application (see item (1)).
  have hJ'bound : ∀ z ∈ subsetSums J', (0:ℤ) ≤ z ∧ z ≤ (J'.card:ℤ) * q := by
    sorry
  set x : ℤ := hxdilate.choose with hxdef
  have hxspec : ∀ y ∈ (GAP.dilate (c*(s:ℝ)) P).set, x + y ∈ subsetSums J' := hxdilate.choose_spec
  have hFace : (c * (s:ℝ) / 2) ^ d * (V:ℝ) ≤ (J'.card:ℤ) * q - 0 + 1 := by
    have := gap_dilate_face_count P (c * (s:ℝ)) ht2 hPdil w hw (subsetSums J') x 0
      ((J'.card:ℤ)*q) (by positivity) hJ'bound hxspec
    simpa [hActive, hddef, hVdef] using this
  -- GAP 2 + steps 4–5 (simultaneous approximation, divisor-bound argument (3.2)), combined
  -- with the face-count bound `hFace` above (paper's (3.1)), to force `d = 1` and get a
  -- quantitative lower bound on `V` exceeding `q` after scaling by `s`. See lemma3_core's
  -- docstring, item (2), and Section 3 of the paper (steps 4–5).
  have hd1_and_big : d = 1 ∧ (c * (s:ℝ) / 2) * (V:ℝ) > q := by
    sorry
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
      push_neg at hcon
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
    · simp only [if_neg hi]
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
      rw [if_neg hi.2]
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

/-- **Lemma 3** of the paper. -/
theorem lemma3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, IsPrimePow q → Q₀ ≤ q →
      ∀ I : Finset ℕ,
        (∀ i ∈ I, (q : ℝ) ^ ε ≤ i ∧ (i : ℝ) ≤ 2 * (q : ℝ) ^ ε) →
        (∀ i ∈ I, Nat.Coprime i q) →
        (q : ℝ) ^ (7 * ε / 8) ≤ I.card →
        ∀ r : ZMod q, ∃ S ⊆ I, (S.card : ℝ) ≤ (q : ℝ) ^ (ε / 2) ∧
          ∑ i ∈ S, ((i : ZMod q)⁻¹) = r := by
  obtain ⟨c, hc, d₀, Q₁, hQ₁⟩ := lemma3_structure_apply ε hε0 hε1
  obtain ⟨Q₂, hQ₂⟩ := lemma3_core ε hε0 hε1 c hc d₀
  obtain ⟨Q₃, hQ₃⟩ := lemma3_growth_bounds ε hε0 hε1 1 (by norm_num)
  refine ⟨max (max Q₁ Q₂) Q₃, fun q hqpp hq I hI1 hI2 hI3 => ?_⟩
  have hqQ1 : Q₁ ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have hqQ2 : Q₂ ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have hqQ3 : Q₃ ≤ q := le_trans (le_max_right _ _) hq
  have hq2 : 2 ≤ q := hqpp.two_le
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  obtain ⟨J, J', P, hJA, hPproper, hPdil, hPD, hJ'J, hJcard, hJmem, h0mem, hJ'card, x, hxdilate⟩ :=
    hQ₁ q hqpp hqQ1 I hI1 hI2 hI3
  have hunits : ∀ j ∈ J, IsUnit ((j:ℕ):ZMod q) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJA hj)
    have hcop := hI2 i hi
    have hui : IsUnit (i:ZMod q) := (ZMod.isUnit_iff_coprime i q).2 hcop
    have hcast : (((i:ZMod q)⁻¹).val : ZMod q) = (i:ZMod q)⁻¹ := ZMod.natCast_rightInverse _
    rw [hcast]
    exact ⟨⟨(i:ZMod q)⁻¹, i, ZMod.inv_mul_of_unit _ hui, ZMod.mul_inv_of_unit _ hui⟩, rfl⟩
  have hcover := hQ₂ q hqpp hqQ2 I.card J J' P hPproper hPdil hPD hJ'J hJcard hJmem h0mem hunits
    hJ'card hI3 ⟨x, hxdilate⟩
  have hA_qlt : 2 * (q:ℝ) ^ ε < q := (hQ₃ q hqQ3).1
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

end Erdos289
