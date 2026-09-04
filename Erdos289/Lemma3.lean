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
* `lemma3_core`: the remaining, genuinely hard additive-combinatorial argument (paper's
  steps 2–6: active coordinates, face counting (3.1), the divisor-bound argument (3.2), the
  `d = 1` dichotomy, and the final covering conclusion). This is left as a precisely stated
  `sorry`, together with a documented gap in the formalization of the external structure
  theorem (properness of the *dilate*, not just of `P`) that step 2–3 of the paper's argument
  needs; see its docstring.

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
  obtain ⟨J, P, J', hJA, hPproper, hPdil, hPD, hJ'J, hJcard, hJmem, h0mem, hJ'card, x, hxdilate⟩ :=
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
as the hypothesis `(GAP.dilate (c * s) P).Proper` below. -/
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
  sorry

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
