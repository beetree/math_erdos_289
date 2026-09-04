import Erdos289.Defs
import Erdos289.Sorting
import Erdos289.DenBound
import Erdos289.Lemma5
import Erdos289.Core
import Erdos289.MainPairs
import Erdos289.Descent
import Erdos289.CorrData
import Erdos289.Harmonic
import Erdos289.Expert
import Erdos289.Tail

/-!
# Final assembly: Erdős Problem 289

This file proves the main theorem `erdos289 : ∀ᶠ k : ℕ in Filter.atTop, Statement k`
by building a `GoodFamily k` for all sufficiently large `k`, following Sections 5-7
of the paper.
-/

namespace Erdos289

open Finset Filter

/-! ## Step 0: asymptotic threshold lemmas -/

/-- For `L` large enough, `40 * L ^ (-1/20) < 1 / 16000` (so that the correction mass,
which is at most `40 * L ^ (-1/20)`, is below `δ / 16`). -/
lemma exists_L1 : ∃ L1 : ℕ, ∀ L, L1 ≤ L → 40 * (L : ℝ) ^ (-(1 : ℝ) / 20) < 1 / 16000 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 20)) atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := (1:ℝ)/20) (by norm_num)
    simpa [neg_div] using this
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun L : ℕ => 40 * (L : ℝ) ^ (-(1 : ℝ) / 20)) atTop (nhds 0) := by
    have h4 := h2.const_mul (40 : ℝ)
    simpa using h4
  have h5 : ∀ᶠ L : ℕ in atTop, 40 * (L : ℝ) ^ (-(1 : ℝ) / 20) < 1 / 16000 :=
    (tendsto_order.mp h3).2 (1 / 16000) (by norm_num)
  exact Filter.eventually_atTop.mp h5

/-- A generic asymptotic helper: `c * k ^ e = o(k)` for `e < 1`, `c ≥ 0`, so eventually
`c * k ^ e ≤ ε * k` for any `ε > 0`. -/
lemma rpow_le_linear_eventually {c ε : ℝ} (_hc : 0 ≤ c) (hε : 0 < ε) {e : ℝ} (he1 : e < 1) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → c * (k : ℝ) ^ e ≤ ε * k := by
  have hpos : 0 < 1 - e := by linarith
  have h1 : Tendsto (fun x : ℝ => x ^ (-(1 - e))) atTop (nhds 0) := tendsto_rpow_neg_atTop hpos
  have h2 : Tendsto (fun x : ℝ => c * x ^ (-(1 - e))) atTop (nhds 0) := by
    have := h1.const_mul c; simpa using this
  have h3 := h2.comp tendsto_natCast_atTop_atTop
  have h4 : ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ (-(1 - e)) < ε := (tendsto_order.mp h3).2 ε hε
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h4
  refine ⟨max k0 1, fun k hk => ?_⟩
  have hk0' : k0 ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hlt := hk0 k hk0'
  have heq : (k : ℝ) ^ e = (k : ℝ) ^ (-(1 - e)) * (k : ℝ) := by
    have hexp : e = -(1 - e) + 1 := by ring
    conv_lhs => rw [hexp]
    rw [Real.rpow_add hkpos, Real.rpow_one]
  rw [heq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hlt.le hkpos.le

/-- A composite asymptotic helper: `(c1 * k ^ a + b) ^ p = o(k)` when `a * p < 1`
(with `c1 > 0`, `a > 0`, `b, p ≥ 0`), so eventually `(c1 * k ^ a + b) ^ p ≤ ε * k`. -/
lemma poly_rpow_le_linear_eventually {c1 b ε : ℝ} (hc1 : 0 < c1) (hb : 0 ≤ b) (hε : 0 < ε)
    {a p : ℝ} (ha0 : 0 < a) (hp0 : 0 ≤ p) (hap : a * p < 1) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → (c1 * (k : ℝ) ^ a + b) ^ p ≤ ε * k := by
  have h1 : Tendsto (fun x : ℝ => x ^ a) atTop atTop := tendsto_rpow_atTop ha0
  have h2 : Tendsto (fun x : ℝ => c1 * x ^ a) atTop atTop := h1.const_mul_atTop hc1
  have h3 := h2.comp tendsto_natCast_atTop_atTop
  have h4 : ∀ᶠ k : ℕ in atTop, b ≤ c1 * (k : ℝ) ^ a := h3.eventually_ge_atTop b
  obtain ⟨k1, hk1⟩ := Filter.eventually_atTop.mp h4
  obtain ⟨k2, hk2⟩ := rpow_le_linear_eventually (c := (2 * c1) ^ p) (ε := ε)
    (by positivity) hε (e := a * p) hap
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2' : k2 ≤ k := le_trans (le_max_right _ _) hk
  have hkann : (0 : ℝ) ≤ (k : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg k) a
  have hstep1 : c1 * (k : ℝ) ^ a + b ≤ 2 * c1 * (k : ℝ) ^ a := by
    have := hk1 k hk1'; linarith
  have hstep2 : (c1 * (k : ℝ) ^ a + b) ^ p ≤ (2 * c1 * (k : ℝ) ^ a) ^ p :=
    Real.rpow_le_rpow (by positivity) hstep1 hp0
  have hstep3 : (2 * c1 * (k : ℝ) ^ a) ^ p = (2 * c1) ^ p * (k : ℝ) ^ (a * p) := by
    rw [Real.mul_rpow (by positivity) hkann, ← Real.rpow_mul (Nat.cast_nonneg k)]
  rw [hstep3] at hstep2
  exact le_trans hstep2 (hk2 k hk2')

/-! ## Step 1: numeric asymptotic package for a fixed cutoff `L` -/

/-- `Q k` cast to `ℝ` is at most `k ^ (4/5)`. -/
lemma Q_le_rpow (k : ℕ) : (Q k : ℝ) ≤ (k : ℝ) ^ ((4 : ℝ) / 5) :=
  Nat.floor_le (by positivity)

/-- `H L k` cast to `ℝ` is at most `K L * B L * k ^ (4/5) + 2`. -/
lemma H_le (L k : ℕ) : (H L k : ℝ) ≤ (K L : ℝ) * (B L : ℝ) * (k : ℝ) ^ ((4 : ℝ) / 5) + 2 := by
  unfold H
  have h1 : (Q k : ℝ) ≤ (k : ℝ) ^ ((4 : ℝ) / 5) := Q_le_rpow k
  have h2 : (0:ℝ) ≤ (K L : ℝ) * (B L : ℝ) := by positivity
  push_cast
  nlinarith

/-- The numeric asymptotic package needed for the assembly, for a fixed cutoff `L ≥ 11`
and auxiliary family `A`: for all sufficiently large `k`, `k` is large, `Q k > L`, the core
count and correction count are each at most `k / 8`, and `H L k ^ (11/10)` is a tiny
fraction of `k`. -/
lemma asymptotic_package (L : ℕ) (hL : 11 ≤ L) (A : AuxFamily L) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      4096000 ≤ k ∧
      L + 1 ≤ Q k ∧
      ((coreSet L A k).card : ℝ) ≤ (k : ℝ) / 8 ∧
      (CH L (H L k) : ℝ) ≤ (k : ℝ) / 8 ∧
      (H L k : ℝ) ^ ((11 : ℝ) / 10) ≤ (k : ℝ) / 1000000 ∧
      Wcore L A k < 1 / 8 := by
  obtain ⟨k_core, hk_core⟩ := core L hL A
  have hKpos : (0:ℝ) < (K L : ℝ) := by
    have := K_ge_27720 hL; exact_mod_cast (by omega : 0 < K L)
  have hBpos : (0:ℝ) < (B L : ℝ) := by
    have : 0 < B L := pow_pos (by norm_num) _
    exact_mod_cast this
  -- R.card ≤ B * k^(4/5) ≤ k/8
  obtain ⟨k1, hk1⟩ := rpow_le_linear_eventually (c := (B L : ℝ)) (ε := 1/8)
    (by positivity) (by norm_num) (e := (4:ℝ)/5) (by norm_num)
  -- Hk^(21/20) ≤ k/8, via CH_le and H_le
  obtain ⟨k2, hk2⟩ := poly_rpow_le_linear_eventually (c1 := (K L : ℝ) * (B L : ℝ)) (b := 2)
    (ε := 1/8) (by positivity) (by norm_num) (by norm_num)
    (a := (4:ℝ)/5) (p := (21:ℝ)/20) (by norm_num) (by norm_num) (by norm_num)
  -- Hk^(11/10) ≤ k/1000000
  obtain ⟨k3, hk3⟩ := poly_rpow_le_linear_eventually (c1 := (K L : ℝ) * (B L : ℝ)) (b := 2)
    (ε := 1/1000000) (by positivity) (by norm_num) (by norm_num)
    (a := (4:ℝ)/5) (p := (11:ℝ)/10) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨k4, hk4⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop (L + 1))
  refine ⟨max (max k_core k1) (max (max k2 k3) (max k4 4096000)), fun k hk => ?_⟩
  have hkcore' : k_core ≤ k := by omega
  have hk1' : k1 ≤ k := by omega
  have hk2' : k2 ≤ k := by omega
  have hk3' : k3 ≤ k := by omega
  have hk4' : k4 ≤ k := by omega
  have hk5' : 4096000 ≤ k := by omega
  refine ⟨hk5', hk4 k hk4', ?_, ?_, ?_, (hk_core k hkcore').2.1⟩
  · exact le_trans (hk_core k hkcore').1 (by linarith [hk1 k hk1'])
  · have hHk := H_le L k
    have hHnn : (0:ℝ) ≤ (H L k : ℝ) := Nat.cast_nonneg _
    have hstep : (H L k : ℝ) ^ ((21:ℝ)/20) ≤
        ((K L : ℝ) * (B L : ℝ) * (k:ℝ) ^ ((4:ℝ)/5) + 2) ^ ((21:ℝ)/20) :=
      Real.rpow_le_rpow hHnn hHk (by norm_num)
    have := hk2 k hk2'
    exact le_trans (CH_le L (H L k)) (by linarith)
  · have hHk := H_le L k
    have hHnn : (0:ℝ) ≤ (H L k : ℝ) := Nat.cast_nonneg _
    have hstep : (H L k : ℝ) ^ ((11:ℝ)/10) ≤
        ((K L : ℝ) * (B L : ℝ) * (k:ℝ) ^ ((4:ℝ)/5) + 2) ^ ((11:ℝ)/10) :=
      Real.rpow_le_rpow hHnn hHk (by norm_num)
    have := hk3 k hk3'
    linarith

/-! ## Step 2: structural helper lemmas -/

lemma w_nonneg (a : ℕ) : 0 ≤ w a := by unfold w; positivity

lemma Wcore_nonneg (L : ℕ) (A : AuxFamily L) (k : ℕ) : 0 ≤ Wcore L A k := by
  unfold Wcore
  apply Finset.sum_nonneg
  intro d _
  rw [show (corePair L d).mass = w (K L * d + 1) from Iv.mass_pair _]
  exact w_nonneg _

@[simp] lemma corePair_lo (L d : ℕ) : (corePair L d).lo = K L * d + 1 := rfl
@[simp] lemma corePair_hi (L d : ℕ) : (corePair L d).hi = K L * d + 2 := rfl
@[simp] lemma coreTriple_lo (L d : ℕ) : (coreTriple L d).lo = K L * d := rfl
@[simp] lemma coreTriple_hi (L d : ℕ) : (coreTriple L d).hi = K L * d + 2 := rfl

/-- `K L = DenBound.lcmIcc L` (both defined as `(Icc 1 L).lcm id`). -/
lemma K_eq_lcmIcc (L : ℕ) : K L = DenBound.lcmIcc L := rfl

/-- `IsMainPair k I` implies `k / 1024 ≤ I.lo` as reals (uniformly across the near-range
and far-band cases). -/
lemma IsMainPair.lo_ge {k : ℕ} {I : Iv} (h : IsMainPair k I) : (k : ℝ) / 1024 ≤ (I.lo : ℝ) := by
  obtain ⟨a, hIeq, -, -, -, hcase⟩ := h
  have hIlo : I.lo = a := by rw [hIeq]; rfl
  rw [hIlo]
  rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have : (k:ℝ) / 1024 ≤ 4 * (k:ℝ) := by linarith
    linarith

/-- Separation between `coreTriple L d` and `coreTriple L d'` (`d ≠ d'`) transfers to any
pair of intervals `X, Y` that are sandwiched between the core pair and core triple at `d`
and `d'` respectively (i.e. `X.hi ≤ (coreTriple L d).hi`, `(coreTriple L d).lo ≤ X.lo`, and
likewise for `Y, d'`). In particular it covers all four combinations of `corePair`/`coreTriple`
at `d` and `d'`. -/
lemma sep_of_core_variant {L d d' : ℕ} (h : Iv.Sep (coreTriple L d) (coreTriple L d'))
    {X Y : Iv} (hXhi : X.hi ≤ (coreTriple L d).hi) (hXlo : (coreTriple L d).lo ≤ X.lo)
    (hYhi : Y.hi ≤ (coreTriple L d').hi) (hYlo : (coreTriple L d').lo ≤ Y.lo) :
    Iv.Sep X Y := by
  rcases h with h | h
  · exact Or.inl (Iv.separated_of_subintervals h hXhi hYlo)
  · exact Or.inr (Iv.separated_of_subintervals h hYhi hXlo)

lemma corePair_sub_coreTriple (L d : ℕ) :
    (corePair L d).hi ≤ (coreTriple L d).hi ∧ (coreTriple L d).lo ≤ (corePair L d).lo := by
  simp

/-- Every element of `Pstar L` is positive. -/
lemma Pstar_pos {L n : ℕ} (h : n ∈ Pstar L) : 1 ≤ n := by
  obtain ⟨q, m, hqpp, -, hqm1, -, hn⟩ := h
  have hq2 : 2 ≤ q := hqpp.two_le
  have hqR : (0:ℝ) < (q:ℝ) := by positivity
  have hmR : (0:ℝ) < (q:ℝ) ^ ((1:ℝ)/10) := Real.rpow_pos_of_pos hqR _
  have hm1 : 1 ≤ m := by
    have : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hmR hqm1
    exact_mod_cast this
  rcases hn with hn | hn <;> subst hn <;> nlinarith

/-- Every element of `Fstar L A.F` is positive. -/
lemma Fstar_pos {L : ℕ} {A : AuxFamily L} {n : ℕ} (h : n ∈ Fstar L A.F) : 1 ≤ n := by
  obtain ⟨q, hqpp, hLq, a, haF, hn⟩ := h
  have hq2 : 2 ≤ q := hqpp.two_le
  have hqR : (0:ℝ) < (q:ℝ) := by positivity
  have ha := A.lower q hqpp hLq a haF
  have haR : (0:ℝ) < (q:ℝ) ^ ((11:ℝ)/10) := Real.rpow_pos_of_pos hqR _
  have ha1 : 1 ≤ a := by
    have : (0:ℝ) < (a:ℝ) := lt_of_lt_of_le haR ha
    exact_mod_cast this
  rcases hn with hn | hn <;> omega

/-- Every element of `U L A` is positive. -/
lemma U_pos {L : ℕ} {A : AuxFamily L} {n : ℕ} (h : n ∈ U L A) : 1 ≤ n := by
  rcases h with h | h
  · exact Pstar_pos h
  · exact Fstar_pos h

lemma K_pos (L : ℕ) : 0 < K L := by rw [K_eq_lcmIcc]; exact DenBound.lcmIcc_pos L

lemma B_pos (L : ℕ) : 0 < B L := pow_pos (by norm_num) _

lemma Q_le_H (L k : ℕ) : Q k ≤ H L k := by
  have hK : 0 < K L := K_pos L
  have hB : 0 < B L := B_pos L
  have hmul : 0 < K L * B L := Nat.mul_pos hK hB
  have hstep : Q k ≤ K L * B L * Q k := Nat.le_mul_of_pos_left _ hmul
  unfold H
  omega

open Classical in
lemma coreSet_hi_le {L k d : ℕ} (A : AuxFamily L) (hd : d ∈ coreSet L A k) :
    K L * d + 2 ≤ H L k := by
  have hmem := (Finset.mem_filter.mp hd).1
  rw [Finset.mem_Ico] at hmem
  have hle : K L * d ≤ K L * B L * Q k := by
    have h1 : K L * d ≤ K L * (d + 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : K L * (d + 1) ≤ K L * (B L * Q k) := Nat.mul_le_mul_left _ hmem.2
    rw [← mul_assoc] at h2
    omega
  unfold H
  omega

/-- `DenBound (H L k) (Wcore L A k)`: the core mass only involves prime powers up to `H L k`. -/
lemma DenBound_Wcore {L : ℕ} (A : AuxFamily L) (k : ℕ) :
    DenBound (H L k) (Wcore L A k) := by
  unfold Wcore
  apply DenBound.sum
  intro d hd
  rw [show (corePair L d).mass = w (K L * d + 1) from Iv.mass_pair _]
  have hbound := coreSet_hi_le A hd
  apply DenBound.w
  · exact powersmooth_of_le (by omega) (by omega)
  · exact powersmooth_of_le (by omega) hbound

/-- `DenBound (H L k) (∑ I ∈ P, I.mass)` for any finset `P` of main pairs. -/
lemma DenBound_Wmain {k : ℕ} {P : Finset Iv} (hP : ∀ I ∈ P, IsMainPair k I) (L : ℕ) :
    DenBound (H L k) (∑ I ∈ P, I.mass) := by
  have hQH : Q k ≤ H L k := Q_le_H L k
  apply DenBound.sum
  intro I hI
  obtain ⟨a, hIeq, -, hpa, hpa1, -⟩ := hP I hI
  have hmass : I.mass = w a := by rw [hIeq]; exact Iv.mass_pair a
  rw [hmass]
  apply DenBound.w
  · exact hpa.mono hQH
  · exact hpa1.mono hQH

/-! ## Step 3: main assembly -/

lemma Wcorr_nonneg {L H : ℕ} {P : Finset Iv}
    (hP : ∀ I ∈ P, ∃ q, IsPrimePow q ∧ L < q ∧ q ≤ H ∧
      ((∃ m, I = Iv.pair (q * m)) ∨ (∃ a, I = Iv.pair a))) :
    0 ≤ ∑ I ∈ P, I.mass := by
  apply Finset.sum_nonneg
  intro I hI
  obtain ⟨q, -, -, -, ⟨m, hIeq⟩ | ⟨a, hIeq⟩⟩ := hP I hI <;>
    rw [hIeq, Iv.mass_pair] <;> exact w_nonneg _

@[simp] lemma Iv.pair_lo' (a : ℕ) : (Iv.pair a).lo = a := rfl
@[simp] lemma Iv.pair_hi' (a : ℕ) : (Iv.pair a).hi = a + 1 := rfl
@[simp] lemma Iv.triple_lo' (a : ℕ) : (Iv.triple a).lo = a := rfl
@[simp] lemma Iv.triple_hi' (a : ℕ) : (Iv.triple a).hi = a + 2 := rfl

/-- No interval is separated from itself (it always has `lo ≤ hi`). -/
lemma Iv.Sep_irrefl {I : Iv} (hle : I.lo ≤ I.hi) : ¬ Iv.Sep I I := by
  unfold Iv.Sep; omega

/-- Separation between `coreTriple L d` and an arbitrary interval `J` transfers to any `X`
sandwiched between the core pair and core triple at `d`. -/
lemma sep_core_left {L d : ℕ} {J : Iv} (h : Iv.Sep (coreTriple L d) J)
    {X : Iv} (hXhi : X.hi ≤ (coreTriple L d).hi) (hXlo : (coreTriple L d).lo ≤ X.lo) :
    Iv.Sep X J := by
  rcases h with h | h
  · exact Or.inl (Iv.separated_of_subintervals h hXhi (le_refl _))
  · exact Or.inr (Iv.separated_of_subintervals h (le_refl _) hXlo)

lemma corePair_injective {L : ℕ} (hL : 0 < K L) : Function.Injective (corePair L) := by
  intro d d' h
  have h2 := congrArg Iv.lo h
  simp only [corePair_lo] at h2
  exact Nat.eq_of_mul_eq_mul_left hL (by omega)

lemma coreTriple_injective {L : ℕ} (hL : 0 < K L) : Function.Injective (coreTriple L) := by
  intro d d' h
  have h2 := congrArg Iv.lo h
  simp only [coreTriple_lo] at h2
  exact Nat.eq_of_mul_eq_mul_left hL h2

/-- If `0 < r` and `r.den ∣ K`, then `r = j / K` for some positive natural `j`. -/
lemma rat_eq_div_of_den_dvd {K : ℕ} {r : ℚ} (hr : 0 < r) (hden : r.den ∣ K) (hK : 0 < K) :
    ∃ j : ℕ, 1 ≤ j ∧ r = (j : ℚ) / (K : ℚ) := by
  obtain ⟨c, hc⟩ := hden
  have hdenpos : 0 < r.den := Rat.pos r
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso; rw [h0, mul_zero] at hc; omega
    · exact h0
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hprod : 0 < r.num * (c : ℤ) := by positivity
  set j : ℕ := (r.num * (c : ℤ)).toNat with hjdef
  have hjint : (j : ℤ) = r.num * (c : ℤ) := Int.toNat_of_nonneg hprod.le
  refine ⟨j, ?_, ?_⟩
  · have : (0:ℤ) < j := hjint ▸ hprod
    exact_mod_cast this
  · have hKQ : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
    have hrd : (r.den : ℚ) ≠ 0 := by exact_mod_cast hdenpos.ne'
    rw [eq_div_iff hKQ]
    have hr' : (r.num : ℚ) = r * (r.den : ℚ) := by
      have := (Rat.num_div_den r); field_simp at this ⊢; linarith [this]
    have hKcast : (K : ℚ) = (r.den : ℚ) * (c : ℚ) := by exact_mod_cast hc
    rw [hKcast, ← mul_assoc, ← hr']
    have : (j : ℚ) = (r.num : ℚ) * (c : ℚ) := by exact_mod_cast hjint
    rw [this]

/-- `j ≤ ⌈K * δ⌉₊` when `r ≤ δ` and `r = j / K`. -/
lemma j_le_ceil {K j : ℕ} {r δ : ℚ} (hr : r = (j : ℚ) / (K : ℚ)) (hle : r ≤ δ) (hK : 0 < K) :
    j ≤ ⌈(K : ℚ) * δ⌉₊ := by
  have hjle : (j : ℚ) ≤ (K : ℚ) * δ := by
    have := (div_le_iff₀ (by exact_mod_cast hK : (0:ℚ) < K)).mp (hr ▸ hle)
    linarith
  have heq : (j : ℕ) = ⌈(j : ℚ)⌉₊ := (Nat.ceil_natCast j).symm
  rw [heq]
  exact Nat.ceil_mono hjle

set_option maxHeartbeats 4000000 in
/-- Building a `GoodFamily k` from fixed correction data `C` with `C.L ≥ 11`, once the
correction mass bound `40 * C.L ^ (-1/20) < 1/16000` holds. -/
theorem goodFamily_of_large (C : CorrectionData) (hL11 : 11 ≤ C.L)
    (hmassbound : 40 * (C.L : ℝ) ^ (-(1 : ℝ) / 20) < 1 / 16000) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k → Nonempty (GoodFamily k) := by
  classical
  have hL4 : 4 ≤ C.L := by omega
  obtain ⟨k_asy, hk_asy⟩ := asymptotic_package C.L hL11 C.A
  obtain ⟨k_core, hk_core⟩ := core C.L hL11 C.A
  obtain ⟨k_main, hk_main⟩ := mainPairs
  refine ⟨max (max k_asy k_core) k_main, fun k hk => ?_⟩
  have hk_asy' : k_asy ≤ k := by omega
  have hk_core' : k_core ≤ k := by omega
  have hk_main' : k_main ≤ k := by omega
  obtain ⟨hk4M, hQL1, hRcard, hCHcard, hHrpow, hWcoreLt⟩ := hk_asy k hk_asy'
  have hKLpos : 0 < K C.L := K_pos C.L
  -- nat count bookkeeping
  have hsum4 : 4 * ((coreSet C.L C.A k).card + CH C.L (H C.L k)) ≤ k := by
    have h1 : ((coreSet C.L C.A k).card : ℝ) + (CH C.L (H C.L k) : ℝ) ≤ (k : ℝ) / 4 := by
      linarith
    have h2 : ((4 * ((coreSet C.L C.A k).card + CH C.L (H C.L k)) : ℕ) : ℝ) ≤ (k : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  have hsum2 : (coreSet C.L C.A k).card + CH C.L (H C.L k) ≤ k / 2 := by omega
  have hsumle : (coreSet C.L C.A k).card + CH C.L (H C.L k) ≤ k := by omega
  have hMbound1 : k / 2 ≤ k - (coreSet C.L C.A k).card - CH C.L (H C.L k) := by omega
  have hMbound2 : k - (coreSet C.L C.A k).card - CH C.L (H C.L k) ≤ k := by omega
  have hδval : δ = (1 : ℚ) / 1000 := rfl
  have hWnn : 0 ≤ Wcore C.L C.A k := Wcore_nonneg C.L C.A k
  have hτlb : (1 : ℚ) / 2 < 1 - Wcore C.L C.A k - δ / 2 := by rw [hδval]; linarith
  have hτub : (1 - Wcore C.L C.A k - δ / 2 : ℚ) < 1 := by rw [hδval]; linarith
  obtain ⟨Pmain, hPcard, hPmain, hPsep, hPmassLo, hPmassHi⟩ :=
    hk_main k hk_main' (k - (coreSet C.L C.A k).card - CH C.L (H C.L k)) hMbound1 hMbound2
      (1 - Wcore C.L C.A k - δ / 2) hτlb hτub
  have hr₀lb : δ / 2 ≤ 1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass := by linarith
  have hr₀ub : 1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass ≤ δ / 2 + 2048 / (k : ℚ) := by
    linarith
  have hQH : Q k ≤ H C.L k := Q_le_H C.L k
  have hHClt : C.L < H C.L k := by
    have : C.L < Q k := by omega
    omega
  have hr₀DB : DenBound (H C.L k) (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) :=
    (DenBound.of_den_eq_one (by rfl : (1 : ℚ).den = 1)).sub
      (DenBound_Wcore C.A k) |>.sub (DenBound_Wmain hPmain C.L)
  obtain ⟨Pcorr, hPcorrCard, hPcorrMem, hPcorrUU, hPcorrEnd, hPcorrSep, hPcorrMassR, hPcorrDB⟩ :=
    descent C hL4 (H C.L k) hHClt (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) hr₀DB
  have hWcorr_nn : 0 ≤ ∑ I ∈ Pcorr, I.mass :=
    Wcorr_nonneg (fun I hI => by
      obtain ⟨q, hqpp, hLq, hqH, hm | ha⟩ := hPcorrMem I hI
      · obtain ⟨m, hm, hIeq⟩ := hm; exact ⟨q, hqpp, hLq, hqH, Or.inl ⟨m, hIeq⟩⟩
      · obtain ⟨a, ha, hIeq⟩ := ha; exact ⟨q, hqpp, hLq, hqH, Or.inr ⟨a, hIeq⟩⟩)
  have hWcorrlt : (∑ I ∈ Pcorr, I.mass : ℚ) < δ / 16 := by
    have h3 : ∑ I ∈ Pcorr, I.mass < (1 / 16000 : ℚ) := by
      have h1 : ((∑ I ∈ Pcorr, I.mass : ℚ) : ℝ) < ((1 / 16000 : ℚ) : ℝ) := by
        have heq : ((1 / 16000 : ℚ) : ℝ) = (1 / 16000 : ℝ) := by norm_num
        rw [heq]
        exact lt_of_le_of_lt hPcorrMassR hmassbound
      exact_mod_cast h1
    rw [hδval]; linarith
  have hkQ : (4096000 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk4M
  have hkQpos : (0 : ℚ) < (k : ℚ) := by linarith
  have h2048 : (2048 : ℚ) / (k : ℚ) ≤ δ / 2 := by
    rw [hδval]
    have heq : (1 : ℚ) / 1000 / 2 = 1 / 2000 := by norm_num
    rw [heq, div_le_div_iff₀ hkQpos (by norm_num : (0:ℚ) < 2000)]
    nlinarith
  have hrlb : δ / 4 ≤
      (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass := by
    rw [hδval] at hWcorrlt ⊢; linarith
  have hrub : (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass ≤ δ := by
    linarith
  have hrpos : 0 <
      (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass := by
    rw [hδval] at hrlb; linarith
  have hrden : ((1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass).den ∣ K C.L := by
    rw [K_eq_lcmIcc]; exact DenBound.lcm hPcorrDB
  set r : ℚ := (1 - Wcore C.L C.A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass with hrdef
  obtain ⟨j, hj1, hjeq⟩ := rat_eq_div_of_den_dvd hrpos hrden hKLpos
  have hjlej0 : j ≤ j₀ C.L := j_le_ceil hjeq hrub hKLpos
  obtain ⟨D, hDsub, hDsum⟩ := (hk_core k hk_core').2.2.1 j hj1 hjlej0
  have hDsum' : ∑ d ∈ D, (1 : ℚ) / (K C.L * d) = r := by rw [hDsum, ← hjeq]
  have hDcardle : D.card ≤ (coreSet C.L C.A k).card := Finset.card_le_card hDsub
  have hk4MR : (4096000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4M
  -- margin bound: correction/core intervals are tiny compared to k
  have hSmallBound : 2 * (H C.L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024 := by
    nlinarith [hHrpow, hk4MR]
  have hHk1R : (1 : ℝ) ≤ (H C.L k : ℝ) := by
    have : 1 ≤ H C.L k := by unfold H; omega
    exact_mod_cast this
  have hHkleRpow : (H C.L k : ℝ) ≤ (H C.L k : ℝ) ^ ((11 : ℝ) / 10) := by
    calc (H C.L k : ℝ) = (H C.L k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (H C.L k : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_le_rpow_of_exponent_le hHk1R (by norm_num)
  have hHk20k : (H C.L k : ℝ) ≤ 20 * (k : ℝ) := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hHrpow, hHkleRpow]
  -- cross-group separation facts
  have hSep_main_corr : ∀ I ∈ Pmain, ∀ J ∈ Pcorr, Iv.Sep I J := by
    intro I hI J hJ
    have hIlo := (hPmain I hI).lo_ge
    have hJhi := (hPcorrEnd J hJ).2.2
    have hlt : (J.hi : ℝ) + 1 < (I.lo : ℝ) := by linarith
    exact Or.inr (by exact_mod_cast hlt)
  have hSep_main_core : ∀ I ∈ Pmain, ∀ d ∈ coreSet C.L C.A k, ∀ X : Iv,
      X.hi ≤ (coreTriple C.L d).hi → Iv.Sep I X := by
    intro I hI d hd X hXhi
    have hIlo := (hPmain I hI).lo_ge
    have hdbound := coreSet_hi_le C.A hd
    have hXhi' : X.hi ≤ H C.L k := by rw [coreTriple_hi] at hXhi; omega
    have hXhiR : (X.hi : ℝ) ≤ (H C.L k : ℝ) := by exact_mod_cast hXhi'
    have hlt : (X.hi : ℝ) + 1 < (I.lo : ℝ) := by linarith
    exact Or.inr (by exact_mod_cast hlt)
  have hSep_corr_core : ∀ J ∈ Pcorr, ∀ d ∈ coreSet C.L C.A k, ∀ X : Iv,
      X.hi ≤ (coreTriple C.L d).hi → (coreTriple C.L d).lo ≤ X.lo → Iv.Sep X J := by
    intro J hJ d hd X hXhi hXlo
    have hJlo := (hPcorrUU J hJ).1
    have hJhi := (hPcorrUU J hJ).2
    have hJeq := (hPcorrEnd J hJ).2.1
    exact sep_core_left ((hk_core k hk_core').2.2.2.2 d hd J hJlo hJhi hJeq) hXhi hXlo
  -- membership decomposition for the two core-image groups
  have hG3mem : ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L),
      ∃ d ∈ coreSet C.L C.A k \ D, X = corePair C.L d := by
    intro X hX
    obtain ⟨d, hd, hXeq⟩ := Finset.mem_image.mp hX
    exact ⟨d, hd, hXeq.symm⟩
  have hG4mem : ∀ X ∈ D.image (coreTriple C.L),
      ∃ d ∈ D, X = coreTriple C.L d := by
    intro X hX
    obtain ⟨d, hd, hXeq⟩ := Finset.mem_image.mp hX
    exact ⟨d, hd, hXeq.symm⟩
  have hMainLoHi : ∀ I ∈ Pmain, I.lo ≤ I.hi := by
    intro I hI; obtain ⟨a, hIeq, -, -, -, -⟩ := hPmain I hI; rw [hIeq]; simp
  have hCorrLoHi : ∀ I ∈ Pcorr, I.lo ≤ I.hi := by
    intro I hI; have := (hPcorrEnd I hI).2.1; omega
  have hG3LoHi : ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L), X.lo ≤ X.hi := by
    intro X hX; obtain ⟨d, -, hXeq⟩ := hG3mem X hX; rw [hXeq]; simp
  -- cross-group separation facts (needed both for disjointness and the final `sep` field)
  have hSep13 : ∀ I ∈ Pmain, ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L), Iv.Sep I X := by
    intro I hI X hX
    obtain ⟨d, hd, hXeq⟩ := hG3mem X hX
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).1
    exact hSep_main_core I hI d (Finset.mem_sdiff.mp hd).1 X hXhi
  have hSep14 : ∀ I ∈ Pmain, ∀ X ∈ D.image (coreTriple C.L), Iv.Sep I X := by
    intro I hI X hX
    obtain ⟨d, hd, hXeq⟩ := hG4mem X hX
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]
    exact hSep_main_core I hI d (hDsub hd) X hXhi
  have hSep23 : ∀ J ∈ Pcorr, ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L), Iv.Sep X J := by
    intro J hJ X hX
    obtain ⟨d, hd, hXeq⟩ := hG3mem X hX
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).1
    have hXlo : (coreTriple C.L d).lo ≤ X.lo := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).2
    exact hSep_corr_core J hJ d (Finset.mem_sdiff.mp hd).1 X hXhi hXlo
  have hSep24 : ∀ J ∈ Pcorr, ∀ X ∈ D.image (coreTriple C.L), Iv.Sep X J := by
    intro J hJ X hX
    obtain ⟨d, hd, hXeq⟩ := hG4mem X hX
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]
    have hXlo : (coreTriple C.L d).lo ≤ X.lo := by rw [hXeq]
    exact hSep_corr_core J hJ d (hDsub hd) X hXhi hXlo
  have hSep34 : ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L), ∀ Y ∈ D.image (coreTriple C.L),
      Iv.Sep X Y := by
    intro X hX Y hY
    obtain ⟨d, hd, hXeq⟩ := hG3mem X hX
    obtain ⟨d', hd', hYeq⟩ := hG4mem Y hY
    have hdd' : d ≠ d' := by
      intro heq; subst heq; exact (Finset.mem_sdiff.mp hd).2 hd'
    have hsepTT := (hk_core k hk_core').2.2.2.1 d (Finset.mem_sdiff.mp hd).1 d' (hDsub hd') hdd'
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).1
    have hXlo : (coreTriple C.L d).lo ≤ X.lo := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).2
    have hYhi : Y.hi ≤ (coreTriple C.L d').hi := by rw [hYeq]
    have hYlo : (coreTriple C.L d').lo ≤ Y.lo := by rw [hYeq]
    exact sep_of_core_variant hsepTT hXhi hXlo hYhi hYlo
  have hSepG3 : ∀ X ∈ (coreSet C.L C.A k \ D).image (corePair C.L),
      ∀ Y ∈ (coreSet C.L C.A k \ D).image (corePair C.L), X ≠ Y → Iv.Sep X Y := by
    intro X hX Y hY hXY
    obtain ⟨d, hd, hXeq⟩ := hG3mem X hX
    obtain ⟨d', hd', hYeq⟩ := hG3mem Y hY
    have hdd' : d ≠ d' := by intro heq; apply hXY; rw [hXeq, hYeq, heq]
    have hsepTT := (hk_core k hk_core').2.2.2.1 d (Finset.mem_sdiff.mp hd).1 d'
      (Finset.mem_sdiff.mp hd').1 hdd'
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).1
    have hXlo : (coreTriple C.L d).lo ≤ X.lo := by rw [hXeq]; exact (corePair_sub_coreTriple C.L d).2
    have hYhi : Y.hi ≤ (coreTriple C.L d').hi := by rw [hYeq]; exact (corePair_sub_coreTriple C.L d').1
    have hYlo : (coreTriple C.L d').lo ≤ Y.lo := by rw [hYeq]; exact (corePair_sub_coreTriple C.L d').2
    exact sep_of_core_variant hsepTT hXhi hXlo hYhi hYlo
  have hSepG4 : ∀ X ∈ D.image (coreTriple C.L), ∀ Y ∈ D.image (coreTriple C.L), X ≠ Y → Iv.Sep X Y := by
    intro X hX Y hY hXY
    obtain ⟨d, hd, hXeq⟩ := hG4mem X hX
    obtain ⟨d', hd', hYeq⟩ := hG4mem Y hY
    have hdd' : d ≠ d' := by intro heq; apply hXY; rw [hXeq, hYeq, heq]
    have hsepTT := (hk_core k hk_core').2.2.2.1 d (hDsub hd) d' (hDsub hd') hdd'
    have hXhi : X.hi ≤ (coreTriple C.L d).hi := by rw [hXeq]
    have hXlo : (coreTriple C.L d).lo ≤ X.lo := by rw [hXeq]
    have hYhi : Y.hi ≤ (coreTriple C.L d').hi := by rw [hYeq]
    have hYlo : (coreTriple C.L d').lo ≤ Y.lo := by rw [hYeq]
    exact sep_of_core_variant hsepTT hXhi hXlo hYhi hYlo
  -- disjointness of the four groups
  have hDisj12 : Disjoint Pmain Pcorr :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (hMainLoHi I hI) (hSep_main_corr I hI I hI'))
  have hDisj13 : Disjoint Pmain ((coreSet C.L C.A k \ D).image (corePair C.L)) :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (hMainLoHi I hI) (hSep13 I hI I hI'))
  have hDisj14 : Disjoint Pmain (D.image (coreTriple C.L)) :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (hMainLoHi I hI) (hSep14 I hI I hI'))
  have hDisj23 : Disjoint Pcorr ((coreSet C.L C.A k \ D).image (corePair C.L)) :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (hCorrLoHi J hJ) (hSep23 J hJ J hJ'))
  have hDisj24 : Disjoint Pcorr (D.image (coreTriple C.L)) :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (hCorrLoHi J hJ) (hSep24 J hJ J hJ'))
  have hDisj34 : Disjoint ((coreSet C.L C.A k \ D).image (corePair C.L)) (D.image (coreTriple C.L)) :=
    Finset.disjoint_left.mpr (fun X hX hX' => Iv.Sep_irrefl (hG3LoHi X hX) (hSep34 X hX X hX'))
  have hD_12_3 : Disjoint (Pmain ∪ Pcorr) ((coreSet C.L C.A k \ D).image (corePair C.L)) :=
    Finset.disjoint_union_left.mpr ⟨hDisj13, hDisj23⟩
  have hD_123_4 : Disjoint (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L))
      (D.image (coreTriple C.L)) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hDisj14, hDisj24⟩, hDisj34⟩
  -- cardinality
  have hcard1 : (Pmain ∪ Pcorr).card = Pmain.card + Pcorr.card := Finset.card_union_of_disjoint hDisj12
  have hcard2 : (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L)).card =
      (Pmain ∪ Pcorr).card + ((coreSet C.L C.A k \ D).image (corePair C.L)).card :=
    Finset.card_union_of_disjoint hD_12_3
  have hcard3 : (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪ D.image (coreTriple C.L)).card
      = (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L)).card
        + (D.image (coreTriple C.L)).card :=
    Finset.card_union_of_disjoint hD_123_4
  have hG3card : ((coreSet C.L C.A k \ D).image (corePair C.L)).card = (coreSet C.L C.A k \ D).card :=
    Finset.card_image_of_injective _ (corePair_injective hKLpos)
  have hG4card : (D.image (coreTriple C.L)).card = D.card :=
    Finset.card_image_of_injective _ (coreTriple_injective hKLpos)
  have hRsetDcard : (coreSet C.L C.A k \ D).card = (coreSet C.L C.A k).card - D.card :=
    Finset.card_sdiff_of_subset hDsub
  have hFcard : (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)).card = k := by
    rw [hcard3, hcard2, hcard1, hG3card, hG4card, hRsetDcard, hPcard, hPcorrCard]
    omega
  -- mass
  have hmass_extend : ∀ d : ℕ, (coreTriple C.L d).mass =
      (corePair C.L d).mass + 1 / ((K C.L : ℚ) * (d : ℚ)) := by
    intro d
    have h := Iv.mass_extend_pair (K C.L * d)
    push_cast at h
    exact h
  have hSumEq : ∑ I ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), I.mass = 1 := by
    rw [Finset.sum_union hD_123_4, Finset.sum_union hD_12_3, Finset.sum_union hDisj12]
    rw [Finset.sum_image (fun d _ d' _ h => corePair_injective hKLpos h)]
    rw [Finset.sum_image (fun d _ d' _ h => coreTriple_injective hKLpos h)]
    have hextend : ∑ d ∈ D, (coreTriple C.L d).mass
        = ∑ d ∈ D, (corePair C.L d).mass + ∑ d ∈ D, (1 : ℚ) / ((K C.L : ℚ) * (d : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun d _ => hmass_extend d)
    rw [hextend, hDsum']
    have hWcoreSplit : ∑ d ∈ (coreSet C.L C.A k \ D), (corePair C.L d).mass
        + ∑ d ∈ D, (corePair C.L d).mass = Wcore C.L C.A k :=
      Finset.sum_sdiff hDsub
    linarith only [hWcoreSplit, hrdef]
  -- GoodFamily fields
  have hOneLeField : ∀ I ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), 1 ≤ I.lo := by
    intro I hI
    simp only [Finset.mem_union] at hI
    rcases hI with ((hI | hI) | hI) | hI
    · have hge := (hPmain I hI).lo_ge
      have : (1 : ℝ) ≤ (I.lo : ℝ) := by nlinarith [hk4MR]
      exact_mod_cast this
    · exact U_pos (hPcorrUU I hI).1
    · obtain ⟨d, -, hIeq⟩ := hG3mem I hI
      rw [hIeq]; simp only [corePair_lo]; omega
    · obtain ⟨d, hd, hIeq⟩ := hG4mem I hI
      have hdmem := (Finset.mem_filter.mp (hDsub hd)).1
      rw [Finset.mem_Ico] at hdmem
      have hd1 : 1 ≤ d := by omega
      have hpos : 0 < K C.L * d := Nat.mul_pos hKLpos hd1
      rw [hIeq]; simp only [coreTriple_lo]; omega
  have hLeBoundField : ∀ I ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), I.hi ≤ 20 * k := by
    intro I hI
    simp only [Finset.mem_union] at hI
    rcases hI with ((hI | hI) | hI) | hI
    · obtain ⟨a, hIeq, -, -, -, hcase⟩ := hPmain I hI
      rw [hIeq]; simp only [Iv.pair_hi']
      rcases hcase with ⟨-, h2⟩ | ⟨-, h2⟩
      · have hle : a + 1 ≤ k := by exact_mod_cast h2
        omega
      · exact_mod_cast h2
    · have hend := (hPcorrEnd I hI).2.2
      have : (I.hi : ℝ) ≤ 20 * (k : ℝ) := by linarith [hSmallBound]
      exact_mod_cast this
    · obtain ⟨d, hd, hIeq⟩ := hG3mem I hI
      have hb := coreSet_hi_le C.A (Finset.mem_sdiff.mp hd).1
      have hnat : H C.L k ≤ 20 * k := by exact_mod_cast hHk20k
      rw [hIeq]; simp only [corePair_hi]; omega
    · obtain ⟨d, hd, hIeq⟩ := hG4mem I hI
      have hb := coreSet_hi_le C.A (hDsub hd)
      have hnat : H C.L k ≤ 20 * k := by exact_mod_cast hHk20k
      rw [hIeq]; simp only [coreTriple_hi]; omega
  have hLenField : ∀ I ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), I.hi + 1 - I.lo = 2 ∨ I.hi + 1 - I.lo = 3 := by
    intro I hI
    simp only [Finset.mem_union] at hI
    rcases hI with ((hI | hI) | hI) | hI
    · obtain ⟨a, hIeq, -, -, -, -⟩ := hPmain I hI
      left; rw [hIeq]; simp only [Iv.pair_hi', Iv.pair_lo']; omega
    · have := (hPcorrEnd I hI).2.1; left; omega
    · obtain ⟨d, -, hIeq⟩ := hG3mem I hI
      left; rw [hIeq]; simp only [corePair_hi, corePair_lo]; omega
    · obtain ⟨d, -, hIeq⟩ := hG4mem I hI
      right; rw [hIeq]; simp only [coreTriple_hi, coreTriple_lo]; omega
  have hSepField : ∀ I ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), ∀ J ∈ (Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪
      D.image (coreTriple C.L)), I ≠ J → Iv.Sep I J := by
    intro I hI J hJ hIJ
    simp only [Finset.mem_union] at hI hJ
    rcases hI with ((hI | hI) | hI) | hI <;> rcases hJ with ((hJ | hJ) | hJ) | hJ
    · exact hPsep I hI J hJ hIJ
    · exact hSep_main_corr I hI J hJ
    · exact hSep13 I hI J hJ
    · exact hSep14 I hI J hJ
    · exact (hSep_main_corr J hJ I hI).symm
    · exact hPcorrSep I hI J hJ hIJ
    · exact (hSep23 I hI J hJ).symm
    · exact (hSep24 I hI J hJ).symm
    · exact (hSep13 J hJ I hI).symm
    · exact hSep23 J hJ I hI
    · exact hSepG3 I hI J hJ hIJ
    · exact hSep34 I hI J hJ
    · exact (hSep14 J hJ I hI).symm
    · exact hSep24 J hJ I hI
    · exact (hSep34 J hJ I hI).symm
    · exact hSepG4 I hI J hJ hIJ
  exact ⟨⟨Pmain ∪ Pcorr ∪ (coreSet C.L C.A k \ D).image (corePair C.L) ∪ D.image (coreTriple C.L),
    hFcard, hOneLeField, hLeBoundField, hLenField, hSepField, hSumEq⟩⟩

/-! ## Step 4: final assembly -/

/-- **Erdős Problem 289**: for all sufficiently large `k`, there are `k` pairwise-separated
integer intervals of length `2` or `3`, contained in `[1, 20k]`, with reciprocal masses
summing to `1`. -/
theorem erdos289 : ∀ᶠ k : ℕ in Filter.atTop, Statement k := by
  obtain ⟨L0, hL0⟩ := correctionData_exists
  obtain ⟨L1, hL1⟩ := exists_L1
  obtain ⟨C, hCL⟩ := hL0 (max L0 (max 11 L1)) (le_max_left _ _)
  have hL11 : 11 ≤ C.L := by rw [hCL]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hLL1 : L1 ≤ C.L := by rw [hCL]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmassbound : 40 * (C.L : ℝ) ^ (-(1 : ℝ) / 20) < 1 / 16000 := hL1 C.L hLL1
  obtain ⟨k0, hk0⟩ := goodFamily_of_large C hL11 hmassbound
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  obtain ⟨G⟩ := hk0 k hk
  exact G.statement

end Erdos289
