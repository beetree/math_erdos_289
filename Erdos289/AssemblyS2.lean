import Erdos289.Defs
import Erdos289.Sorting
import Erdos289.DenBound
import Erdos289.Core
import Erdos289.CoreS
import Erdos289.MainPairs
import Erdos289.DescentS
import Erdos289.CorrDataS
import Erdos289.Lemma5S
import Erdos289.SignedD1
import Erdos289.SignedTail
import Erdos289.Target

/-!
# Final assembly (signed variant): Erdős Problem 289

This file proves the main theorem `erdos289S2 : ∀ᶠ k : ℕ in Filter.atTop, Statement k`
using the signed components (Sections 3-7) of the elementary replacement strategy.
-/

namespace Erdos289.AssemblyS2

open Finset Filter

/-! ## Step 0: asymptotic threshold lemmas -/

/-- For `L` large enough, `120 * L ^ (-1/40) < 1 / 16000` via `eventually_mass_small`. -/
lemma exists_L1 : ∃ L1 : ℕ, ∀ L, L1 ≤ L → 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < 1 / 16000 := by
  have h := eventually_mass_small (1 / 16000) (by norm_num)
  exact Filter.eventually_atTop.mp h

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

/-- A composite asymptotic helper: `(c1 * k ^ a + b) ^ p = o(k)` when `a * p < 1`. -/
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

lemma H_ge_one (L k : ℕ) : 1 ≤ H L k := by unfold H; omega

/-- Bounds on powers of `H L k`. -/
lemma H_rpow_bounds {L k : ℕ} (hk4M : 4096000 ≤ k)
    (hHrpow : (H L k : ℝ) ^ ((11 : ℝ) / 10) ≤ (k : ℝ) / 1000000) :
    8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024 ∧
    (H L k : ℝ) ≤ 20 * (k : ℝ) ∧
    (H L k : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10) := by
  have hk4MR : (4096000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4M
  have hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024 := by
    nlinarith [hHrpow, hk4MR]
  have hH1 : (1 : ℝ) ≤ (H L k : ℝ) := by exact_mod_cast H_ge_one L k
  have hHleRpow : (H L k : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10) := by
    calc (H L k : ℝ) = (H L k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
  have hH20k : (H L k : ℝ) ≤ 20 * (k : ℝ) := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hHrpow, hHleRpow]
  exact ⟨hSmall, hH20k, hHleRpow⟩

/-! ## Step 1: numeric asymptotic package for a fixed cutoff `L` -/

/-- Density hypothesis for `USigned` at `ε = 1/10`. -/
lemma uSigned_density_ten (L : ℕ) (A : AuxFamilyS ((1 : ℝ) / 10) L) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ X : ℕ in Filter.atTop,
      ((USigned ((1 : ℝ) / 10) L A ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * (X : ℝ) :=
  USigned_density ((1 : ℝ) / 10) (by norm_num) (by norm_num) L A
    (lemmaD1 ((1 : ℝ) / 10) (by norm_num) (by norm_num) L)

/-- Asymptotic package for signed assembly. -/
lemma asymptotic_packageS (L : ℕ) (hL : 11 ≤ L) (A : AuxFamilyS ((1 : ℝ) / 10) L) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      4096000 ≤ k ∧
      L + 1 ≤ Q k ∧
      (((coreSetS ((1 : ℝ) / 10) L A k).card : ℝ) ≤ (k : ℝ) / 8) ∧
      ((CH L (H L k) : ℝ) ≤ (k : ℝ) / 8) ∧
      ((H L k : ℝ) ^ ((11 : ℝ) / 10) ≤ (k : ℝ) / 1000000) ∧
      WcoreS ((1 : ℝ) / 10) L A k < 1 / 8 := by
  obtain ⟨k_core, hk_core⟩ := coreS ((1 : ℝ) / 10) L hL A (uSigned_density_ten L A)
  have hKpos : (0:ℝ) < (K L : ℝ) := by
    have := K_ge_27720 hL; exact_mod_cast (by omega : 0 < K L)
  have hBpos : (0:ℝ) < (B L : ℝ) := by
    have : 0 < B L := pow_pos (by norm_num) _
    exact_mod_cast this
  obtain ⟨k1, hk1⟩ := rpow_le_linear_eventually (c := (B L : ℝ)) (ε := 1/8)
    (by positivity) (by norm_num) (e := (4:ℝ)/5) (by norm_num)
  obtain ⟨k2, hk2⟩ := poly_rpow_le_linear_eventually (c1 := (K L : ℝ) * (B L : ℝ)) (b := 2)
    (ε := 1/8) (by positivity) (by norm_num) (by norm_num)
    (a := (4:ℝ)/5) (p := (21:ℝ)/20) (by norm_num) (by norm_num) (by norm_num)
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

lemma WcoreS_nonneg (ε : ℝ) (L : ℕ) (A : AuxFamilyS ε L) (k : ℕ) : 0 ≤ WcoreS ε L A k := by
  unfold WcoreS
  apply Finset.sum_nonneg
  intro d _
  rw [show (corePair L d).mass = w (K L * d + 1) from Iv.mass_pair _]
  exact w_nonneg _

@[simp] lemma corePair_lo (L d : ℕ) : (corePair L d).lo = K L * d + 1 := rfl
@[simp] lemma corePair_hi (L d : ℕ) : (corePair L d).hi = K L * d + 2 := rfl
@[simp] lemma coreTriple_lo (L d : ℕ) : (coreTriple L d).lo = K L * d := rfl
@[simp] lemma coreTriple_hi (L d : ℕ) : (coreTriple L d).hi = K L * d + 2 := rfl

lemma K_eq_lcmIcc (L : ℕ) : K L = DenBound.lcmIcc L := rfl

lemma IsMainPair_lo_ge {k : ℕ} {I : Iv} (h : IsMainPair k I) : (k : ℝ) / 1024 ≤ (I.lo : ℝ) := by
  obtain ⟨a, hIeq, -, -, -, hcase⟩ := h
  have hIlo : I.lo = a := by rw [hIeq]; rfl
  rw [hIlo]
  rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have : (k:ℝ) / 1024 ≤ 4 * (k:ℝ) := by linarith
    linarith

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
lemma coreSetS_hi_le {ε : ℝ} {L k d : ℕ} (A : AuxFamilyS ε L) (hd : d ∈ coreSetS ε L A k) :
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

lemma DenBound_WcoreS {ε : ℝ} {L : ℕ} (A : AuxFamilyS ε L) (k : ℕ) :
    DenBound (H L k) (WcoreS ε L A k) := by
  unfold WcoreS
  apply DenBound.sum
  intro d hd
  rw [show (corePair L d).mass = w (K L * d + 1) from Iv.mass_pair _]
  have hbound := coreSetS_hi_le A hd
  apply DenBound.w
  · exact powersmooth_of_le (by omega) (by omega)
  · exact powersmooth_of_le (by omega) hbound

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

lemma WcorrS_nonneg {C : CorrectionDataS ((1 : ℝ) / 10)} {P : Finset Iv}
    (hP : ∀ I ∈ P, ∃ q, IsPrimePow q ∧ C.L < q ∧ q ≤ C.H ∧
      ((∃ m ∈ C.J q, I = signedPair q m ((C.F q).σ m)) ∨ (∃ a ∈ C.A.F q, I = Iv.pair a))) :
    0 ≤ ∑ I ∈ P, I.mass := by
  apply Finset.sum_nonneg
  intro I hI
  obtain ⟨q, -, -, -, ⟨m, -, hIeq⟩ | ⟨a, -, hIeq⟩⟩ := hP I hI
  · rw [hIeq]
    unfold signedPair
    split_ifs <;> rw [Iv.mass_pair] <;> exact w_nonneg _
  · rw [hIeq, Iv.mass_pair]
    exact w_nonneg _

@[simp] lemma Iv.pair_lo' (a : ℕ) : (Iv.pair a).lo = a := rfl
@[simp] lemma Iv.pair_hi' (a : ℕ) : (Iv.pair a).hi = a + 1 := rfl
@[simp] lemma Iv.triple_lo' (a : ℕ) : (Iv.triple a).lo = a := rfl
@[simp] lemma Iv.triple_hi' (a : ℕ) : (Iv.triple a).hi = a + 2 := rfl

lemma Iv.Sep_irrefl {I : Iv} (hle : I.lo ≤ I.hi) : ¬ Iv.Sep I I := by
  unfold Iv.Sep; omega

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

lemma j_le_ceil {K j : ℕ} {r δ : ℚ} (hr : r = (j : ℚ) / (K : ℚ)) (hle : r ≤ δ) (hK : 0 < K) :
    j ≤ ⌈(K : ℚ) * δ⌉₊ := by
  have hjle : (j : ℚ) ≤ (K : ℚ) * δ := by
    have := (div_le_iff₀ (by exact_mod_cast hK : (0:ℚ) < K)).mp (hr ▸ hle)
    linarith
  have heq : (j : ℕ) = ⌈(j : ℚ)⌉₊ := (Nat.ceil_natCast j).symm
  rw [heq]
  exact Nat.ceil_mono hjle

/-! ## Step 3: correction data and family structure -/

/-- Build correction data with exact cutoff `L` and auxiliary family `A`. -/
def mkCorrectionDataS {L : ℕ} (CH : CorrectionDataS ((1 : ℝ) / 10)) (hL : CH.L = L)
    (A : AuxFamilyS ((1 : ℝ) / 10) L) : CorrectionDataS ((1 : ℝ) / 10) where
  L := L
  H := CH.H
  LH := hL ▸ CH.LH
  A := A
  F := CH.F
  J := CH.J
  J_sub := CH.J_sub
  J_card := fun q hq hLq hqH => CH.J_card q hq (hL ▸ hLq) hqH
  J_sep := fun q q' hq hLq hqH hq' hLq' hq'H m hm m' hm' hne =>
    CH.J_sep q q' hq (hL ▸ hLq) hqH hq' (hL ▸ hLq') hq'H m hm m' hm' hne
  cover := fun q hq hLq hqH r => CH.cover q hq (hL ▸ hLq) hqH r
  E_small := fun q hq hLq => CH.E_small q hq (hL ▸ hLq)

@[simp] lemma mkCorrectionDataS_L {L : ℕ} (CH : CorrectionDataS ((1 : ℝ) / 10)) (hL : CH.L = L)
    (A : AuxFamilyS ((1 : ℝ) / 10) L) : (mkCorrectionDataS CH hL A).L = L := rfl

@[simp] lemma mkCorrectionDataS_H {L : ℕ} (CH : CorrectionDataS ((1 : ℝ) / 10)) (hL : CH.L = L)
    (A : AuxFamilyS ((1 : ℝ) / 10) L) : (mkCorrectionDataS CH hL A).H = CH.H := rfl

@[simp] lemma mkCorrectionDataS_A {L : ℕ} (CH : CorrectionDataS ((1 : ℝ) / 10)) (hL : CH.L = L)
    (A : AuxFamilyS ((1 : ℝ) / 10) L) : (mkCorrectionDataS CH hL A).A = A := rfl

lemma sep_main_corr {k L : ℕ} {I J : Iv} (hI : IsMainPair k I)
    (hJend : (J.hi : ℝ) ≤ 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 1)
    (hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024) :
    Iv.Sep I J := by
  have hIlo := IsMainPair_lo_ge hI
  have hlt : (J.hi : ℝ) + 1 < (I.lo : ℝ) := by linarith
  exact Or.inr (by exact_mod_cast hlt)

lemma sep_main_core {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {I X : Iv} {d : ℕ}
    (hI : IsMainPair k I) (hd : d ∈ coreSetS ((1 : ℝ) / 10) L A k)
    (hXhi : X.hi ≤ (coreTriple L d).hi)
    (hHkleRpow : (H L k : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10))
    (hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024) :
    Iv.Sep I X := by
  have hIlo := IsMainPair_lo_ge hI
  have hdbound := coreSetS_hi_le A hd
  have hXhi' : X.hi ≤ H L k := by rw [coreTriple_hi] at hXhi; omega
  have hXhiR : (X.hi : ℝ) ≤ (H L k : ℝ) := by exact_mod_cast hXhi'
  have hHrpow_nn : (0 : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt : (X.hi : ℝ) + 1 < (I.lo : ℝ) := by linarith
  exact Or.inr (by exact_mod_cast hlt)

lemma sep_corr_core {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {J X : Iv} {d : ℕ}
    (hCoreSep : ∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ I : Iv,
      I.lo ∈ USigned ((1 : ℝ) / 10) L A → I.hi ∈ USigned ((1 : ℝ) / 10) L A →
      I.hi = I.lo + 1 → Iv.Sep (coreTriple L d) I)
    (hd : d ∈ coreSetS ((1 : ℝ) / 10) L A k)
    (hJlo : J.lo ∈ USigned ((1 : ℝ) / 10) L A) (hJhi : J.hi ∈ USigned ((1 : ℝ) / 10) L A)
    (hJeq : J.hi = J.lo + 1)
    (hXhi : X.hi ≤ (coreTriple L d).hi) (hXlo : (coreTriple L d).lo ≤ X.lo) :
    Iv.Sep X J :=
  sep_core_left (hCoreSep d hd J hJlo hJhi hJeq) hXhi hXlo

lemma F_sep {Pmain Pcorr G3 G4 : Finset Iv}
    (hSep11 : ∀ I ∈ Pmain, ∀ J ∈ Pmain, I ≠ J → Iv.Sep I J)
    (hSep12 : ∀ I ∈ Pmain, ∀ J ∈ Pcorr, Iv.Sep I J)
    (hSep13 : ∀ I ∈ Pmain, ∀ X ∈ G3, Iv.Sep I X)
    (hSep14 : ∀ I ∈ Pmain, ∀ X ∈ G4, Iv.Sep I X)
    (hSep22 : ∀ I ∈ Pcorr, ∀ J ∈ Pcorr, I ≠ J → Iv.Sep I J)
    (hSep23 : ∀ J ∈ Pcorr, ∀ X ∈ G3, Iv.Sep X J)
    (hSep24 : ∀ J ∈ Pcorr, ∀ X ∈ G4, Iv.Sep X J)
    (hSep33 : ∀ X ∈ G3, ∀ Y ∈ G3, X ≠ Y → Iv.Sep X Y)
    (hSep34 : ∀ X ∈ G3, ∀ Y ∈ G4, Iv.Sep X Y)
    (hSep44 : ∀ X ∈ G4, ∀ Y ∈ G4, X ≠ Y → Iv.Sep X Y) :
    ∀ I ∈ Pmain ∪ Pcorr ∪ G3 ∪ G4, ∀ J ∈ Pmain ∪ Pcorr ∪ G3 ∪ G4, I ≠ J → Iv.Sep I J := by
  intro I hI J hJ hIJ
  simp only [Finset.mem_union] at hI hJ
  rcases hI with ((hI | hI) | hI) | hI <;> rcases hJ with ((hJ | hJ) | hJ) | hJ
  · exact hSep11 I hI J hJ hIJ
  · exact hSep12 I hI J hJ
  · exact hSep13 I hI J hJ
  · exact hSep14 I hI J hJ
  · exact (hSep12 J hJ I hI).symm
  · exact hSep22 I hI J hJ hIJ
  · exact (hSep23 I hI J hJ).symm
  · exact (hSep24 I hI J hJ).symm
  · exact (hSep13 J hJ I hI).symm
  · exact hSep23 J hJ I hI
  · exact hSep33 I hI J hJ hIJ
  · exact hSep34 I hI J hJ
  · exact (hSep14 J hJ I hI).symm
  · exact hSep24 J hJ I hI
  · exact (hSep34 J hJ I hI).symm
  · exact hSep44 I hI J hJ hIJ

lemma F_card {Pmain Pcorr G3 G4 : Finset Iv} {k M CH c3 c4 : ℕ}
    (hM : Pmain.card = M) (hCH : Pcorr.card = CH)
    (hc3 : G3.card = c3) (hc4 : G4.card = c4)
    (hsum : M + CH + c3 + c4 = k)
    (h1LoHi : ∀ I ∈ Pmain, I.lo ≤ I.hi) (h2LoHi : ∀ I ∈ Pcorr, I.lo ≤ I.hi)
    (h3LoHi : ∀ X ∈ G3, X.lo ≤ X.hi)
    (hSep12 : ∀ I ∈ Pmain, ∀ J ∈ Pcorr, Iv.Sep I J)
    (hSep13 : ∀ I ∈ Pmain, ∀ X ∈ G3, Iv.Sep I X)
    (hSep14 : ∀ I ∈ Pmain, ∀ X ∈ G4, Iv.Sep I X)
    (hSep23 : ∀ J ∈ Pcorr, ∀ X ∈ G3, Iv.Sep X J)
    (hSep24 : ∀ J ∈ Pcorr, ∀ X ∈ G4, Iv.Sep X J)
    (hSep34 : ∀ X ∈ G3, ∀ Y ∈ G4, Iv.Sep X Y) :
    (Pmain ∪ Pcorr ∪ G3 ∪ G4).card = k := by
  have d12 : Disjoint Pmain Pcorr :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep12 I hI I hI'))
  have d13 : Disjoint Pmain G3 :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep13 I hI I hI'))
  have d14 : Disjoint Pmain G4 :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep14 I hI I hI'))
  have d23 : Disjoint Pcorr G3 :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (h2LoHi J hJ) (hSep23 J hJ J hJ'))
  have d24 : Disjoint Pcorr G4 :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (h2LoHi J hJ) (hSep24 J hJ J hJ'))
  have d34 : Disjoint G3 G4 :=
    Finset.disjoint_left.mpr (fun X hX hX' => Iv.Sep_irrefl (h3LoHi X hX) (hSep34 X hX X hX'))
  have du3 : Disjoint (Pmain ∪ Pcorr) G3 := Finset.disjoint_union_left.mpr ⟨d13, d23⟩
  have du4 : Disjoint (Pmain ∪ Pcorr ∪ G3) G4 :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d14, d24⟩, d34⟩
  rw [Finset.card_union_of_disjoint du4, Finset.card_union_of_disjoint du3,
      Finset.card_union_of_disjoint d12, hM, hCH, hc3, hc4]
  omega

lemma F_mass {L : ℕ} (hKL : 0 < K L) {Pmain Pcorr : Finset Iv} {R D : Finset ℕ} (hDsub : D ⊆ R)
    (h1LoHi : ∀ I ∈ Pmain, I.lo ≤ I.hi) (h2LoHi : ∀ I ∈ Pcorr, I.lo ≤ I.hi)
    (h3LoHi : ∀ X ∈ (R \ D).image (corePair L), X.lo ≤ X.hi)
    (hSep12 : ∀ I ∈ Pmain, ∀ J ∈ Pcorr, Iv.Sep I J)
    (hSep13 : ∀ I ∈ Pmain, ∀ X ∈ (R \ D).image (corePair L), Iv.Sep I X)
    (hSep14 : ∀ I ∈ Pmain, ∀ X ∈ D.image (coreTriple L), Iv.Sep I X)
    (hSep23 : ∀ J ∈ Pcorr, ∀ X ∈ (R \ D).image (corePair L), Iv.Sep X J)
    (hSep24 : ∀ J ∈ Pcorr, ∀ X ∈ D.image (coreTriple L), Iv.Sep X J)
    (hSep34 : ∀ X ∈ (R \ D).image (corePair L), ∀ Y ∈ D.image (coreTriple L), Iv.Sep X Y)
    (hDsum : ∑ d ∈ D, (1 : ℚ) / (K L * d) =
      (1 - ∑ d ∈ R, (corePair L d).mass - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass) :
    ∑ I ∈ Pmain ∪ Pcorr ∪ (R \ D).image (corePair L) ∪ D.image (coreTriple L), I.mass = 1 := by
  have d12 : Disjoint Pmain Pcorr :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep12 I hI I hI'))
  have d13 : Disjoint Pmain ((R \ D).image (corePair L)) :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep13 I hI I hI'))
  have d14 : Disjoint Pmain (D.image (coreTriple L)) :=
    Finset.disjoint_left.mpr (fun I hI hI' => Iv.Sep_irrefl (h1LoHi I hI) (hSep14 I hI I hI'))
  have d23 : Disjoint Pcorr ((R \ D).image (corePair L)) :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (h2LoHi J hJ) (hSep23 J hJ J hJ'))
  have d24 : Disjoint Pcorr (D.image (coreTriple L)) :=
    Finset.disjoint_left.mpr (fun J hJ hJ' => Iv.Sep_irrefl (h2LoHi J hJ) (hSep24 J hJ J hJ'))
  have d34 : Disjoint ((R \ D).image (corePair L)) (D.image (coreTriple L)) :=
    Finset.disjoint_left.mpr (fun X hX hX' => Iv.Sep_irrefl (h3LoHi X hX) (hSep34 X hX X hX'))
  have du3 : Disjoint (Pmain ∪ Pcorr) ((R \ D).image (corePair L)) :=
    Finset.disjoint_union_left.mpr ⟨d13, d23⟩
  have du4 : Disjoint (Pmain ∪ Pcorr ∪ (R \ D).image (corePair L)) (D.image (coreTriple L)) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d14, d24⟩, d34⟩
  rw [Finset.sum_union du4, Finset.sum_union du3, Finset.sum_union d12,
      Finset.sum_image (fun d _ d' _ h => corePair_injective hKL h),
      Finset.sum_image (fun d _ d' _ h => coreTriple_injective hKL h)]
  have hextend : ∑ d ∈ D, (coreTriple L d).mass =
      ∑ d ∈ D, (corePair L d).mass + ∑ d ∈ D, (1 : ℚ) / ((K L : ℚ) * (d : ℚ)) := by
    have he : ∀ d : ℕ, (coreTriple L d).mass =
        (corePair L d).mass + 1 / ((K L : ℚ) * (d : ℚ)) := by
      intro d; have h := Iv.mass_extend_pair (K L * d); push_cast at h; exact h
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => he d)
  have hsplit : ∑ d ∈ R \ D, (corePair L d).mass + ∑ d ∈ D, (corePair L d).mass =
      ∑ d ∈ R, (corePair L d).mass := Finset.sum_sdiff hDsub
  have hDsum' : ∑ d ∈ D, (1 : ℚ) / ((K L : ℚ) * (d : ℚ)) = ∑ d ∈ D, (1 : ℚ) / (K L * d) := rfl
  rw [hextend, hDsum', hDsum]
  linarith [hsplit]

lemma F_one_le {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {Pmain Pcorr : Finset Iv}
    {D : Finset ℕ} (hPmain : ∀ I ∈ Pmain, IsMainPair k I) (hk4M : 4096000 ≤ k)
    (hPcorrEnd : ∀ I ∈ Pcorr, 1 ≤ I.lo) (hKL : 0 < K L) (hQ1 : 1 ≤ Q k)
    (hD : D ⊆ coreSetS ((1 : ℝ) / 10) L A k) :
    ∀ I ∈ Pmain ∪ Pcorr ∪ (coreSetS ((1 : ℝ) / 10) L A k \ D).image (corePair L) ∪
      D.image (coreTriple L), 1 ≤ I.lo := by
  classical
  intro I hI
  simp only [Finset.mem_union] at hI
  rcases hI with ((hI | hI) | hI) | hI
  · have hge := IsMainPair_lo_ge (hPmain I hI)
    have hk4MR : (4096000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4M
    have : (1 : ℝ) ≤ (I.lo : ℝ) := by nlinarith [hk4MR]
    exact_mod_cast this
  · exact (hPcorrEnd I hI)
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hI
    simp only [corePair_lo]; omega
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hI
    have hdmem := (Finset.mem_filter.mp (hD hd)).1
    rw [Finset.mem_Ico] at hdmem
    have hd1 : 1 ≤ d := le_trans hQ1 hdmem.1
    have hpos : 0 < K L * d := Nat.mul_pos hKL hd1
    rw [coreTriple_lo]; omega

lemma F_hi_le {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {Pmain Pcorr : Finset Iv}
    {D : Finset ℕ} (hPmain : ∀ I ∈ Pmain, IsMainPair k I)
    (hPcorrEnd : ∀ I ∈ Pcorr, (I.hi : ℝ) ≤ 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 1)
    (hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024)
    (hHk20k : H L k ≤ 20 * k) (hk4M : 4096000 ≤ k)
    (hD : D ⊆ coreSetS ((1 : ℝ) / 10) L A k) :
    ∀ I ∈ Pmain ∪ Pcorr ∪ (coreSetS ((1 : ℝ) / 10) L A k \ D).image (corePair L) ∪
      D.image (coreTriple L), I.hi ≤ 20 * k := by
  intro I hI
  simp only [Finset.mem_union] at hI
  rcases hI with ((hI | hI) | hI) | hI
  · obtain ⟨a, hIeq, -, -, -, hcase⟩ := hPmain I hI
    rw [hIeq]; simp only [Iv.pair_hi']
    rcases hcase with ⟨-, h2⟩ | ⟨-, h2⟩
    · have hle : a + 1 ≤ k := by exact_mod_cast h2
      omega
    · exact_mod_cast h2
  · have hend := hPcorrEnd I hI
    have hk4MR : (4096000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4M
    have : (I.hi : ℝ) ≤ 20 * (k : ℝ) := by linarith [hSmall, hk4MR]
    exact_mod_cast this
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hI
    have hb := coreSetS_hi_le A (Finset.mem_sdiff.mp hd).1
    simp only [corePair_hi]; omega
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hI
    have hb := coreSetS_hi_le A (hD hd)
    simp only [coreTriple_hi]; omega

lemma F_len {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {Pmain Pcorr : Finset Iv}
    {D : Finset ℕ} (hPmain : ∀ I ∈ Pmain, IsMainPair k I)
    (hPcorrEnd : ∀ I ∈ Pcorr, I.hi = I.lo + 1) :
    ∀ I ∈ Pmain ∪ Pcorr ∪ (coreSetS ((1 : ℝ) / 10) L A k \ D).image (corePair L) ∪
      D.image (coreTriple L), I.hi + 1 - I.lo = 2 ∨ I.hi + 1 - I.lo = 3 := by
  intro I hI
  simp only [Finset.mem_union] at hI
  rcases hI with ((hI | hI) | hI) | hI
  · obtain ⟨a, hIeq, -, -, -, -⟩ := hPmain I hI
    left; rw [hIeq]; simp only [Iv.pair_hi', Iv.pair_lo']; omega
  · have := hPcorrEnd I hI; left; omega
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hI
    left; simp only [corePair_hi, corePair_lo]; omega
  · obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hI
    right; simp only [coreTriple_hi, coreTriple_lo]; omega

lemma Wcorr_lt_delta_div_16 {L : ℕ} {mass : ℚ}
    (hmass : (mass : ℝ) ≤ 120 * (L : ℝ) ^ (-(1 : ℝ) / 40))
    (hmassbound : 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < 1 / 16000) :
    mass < δ / 16 := by
  have h1 : (mass : ℝ) < (1 / 16000 : ℝ) := lt_of_le_of_lt hmass hmassbound
  have h2 : mass < (1 / 16000 : ℚ) := by
    have heq : ((1 / 16000 : ℚ) : ℝ) = (1 / 16000 : ℝ) := by norm_num
    exact_mod_cast (heq ▸ h1)
  have hδval : δ = (1 : ℚ) / 1000 := rfl
  rw [hδval]; linarith

lemma residual_bounds {k : ℕ} (hk4M : 4096000 ≤ k) {r₀ Wcorr : ℚ}
    (hr₀lb : δ / 2 ≤ r₀) (hr₀ub : r₀ ≤ δ / 2 + 2048 / (k : ℚ))
    (hWcorr_nn : 0 ≤ Wcorr) (hWcorr : Wcorr < δ / 16) :
    δ / 4 ≤ r₀ - Wcorr ∧ r₀ - Wcorr ≤ δ ∧ 0 < r₀ - Wcorr := by
  have hkQ : (4096000 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk4M
  have hkQpos : (0 : ℚ) < (k : ℚ) := by linarith
  have hδval : δ = (1 : ℚ) / 1000 := rfl
  have h2048 : (2048 : ℚ) / (k : ℚ) ≤ δ / 2 := by
    rw [hδval]
    have heq : (1 : ℚ) / 1000 / 2 = 1 / 2000 := by norm_num
    rw [heq, div_le_div_iff₀ hkQpos (by norm_num : (0:ℚ) < 2000)]
    nlinarith
  have hrlb : δ / 4 ≤ r₀ - Wcorr := by rw [hδval] at hWcorr ⊢; linarith
  have hrub : r₀ - Wcorr ≤ δ := by linarith
  have hrpos : 0 < r₀ - Wcorr := by rw [hδval] at hrlb; linarith
  exact ⟨hrlb, hrub, hrpos⟩

lemma sep_main_all {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L}
    {Pmain Pcorr : Finset Iv} {D : Finset ℕ}
    (hPmain : ∀ I ∈ Pmain, IsMainPair k I)
    (hPcorrEnd : ∀ I ∈ Pcorr, (I.hi : ℝ) ≤ 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 1)
    (hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024)
    (hHleRpow : (H L k : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10))
    (hDsub : D ⊆ coreSetS ((1 : ℝ) / 10) L A k) :
    (∀ I ∈ Pmain, ∀ J ∈ Pcorr, Iv.Sep I J) ∧
    (∀ I ∈ Pmain, ∀ X ∈ (coreSetS ((1 : ℝ) / 10) L A k \ D).image (corePair L), Iv.Sep I X) ∧
    (∀ I ∈ Pmain, ∀ X ∈ D.image (coreTriple L), Iv.Sep I X) := by
  refine ⟨fun I hI J hJ => sep_main_corr (hPmain I hI) (hPcorrEnd J hJ) hSmall, ?_, ?_⟩
  · intro I hI X hX; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    exact sep_main_core (hPmain I hI) (Finset.mem_sdiff.mp hd).1
      (corePair_sub_coreTriple L d).1 hHleRpow hSmall
  · intro I hI X hX; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    exact sep_main_core (hPmain I hI) (hDsub hd) (le_refl _) hHleRpow hSmall

lemma sep_corr_core_all {k L : ℕ} {A : AuxFamilyS ((1 : ℝ) / 10) L} {Pcorr : Finset Iv} {D : Finset ℕ}
    (hCoreSepU : ∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ I : Iv,
      I.lo ∈ USigned ((1 : ℝ) / 10) L A → I.hi ∈ USigned ((1 : ℝ) / 10) L A →
      I.hi = I.lo + 1 → Iv.Sep (coreTriple L d) I)
    (hPcorrUU : ∀ I ∈ Pcorr, I.lo ∈ USigned ((1 : ℝ) / 10) L A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) L A)
    (hPcorrEnd : ∀ I ∈ Pcorr, I.hi = I.lo + 1)
    (hDsub : D ⊆ coreSetS ((1 : ℝ) / 10) L A k) :
    (∀ J ∈ Pcorr, ∀ X ∈ (coreSetS ((1 : ℝ) / 10) L A k \ D).image (corePair L), Iv.Sep X J) ∧
    (∀ J ∈ Pcorr, ∀ X ∈ D.image (coreTriple L), Iv.Sep X J) := by
  refine ⟨?_, ?_⟩
  · intro J hJ X hX; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    exact sep_corr_core hCoreSepU (Finset.mem_sdiff.mp hd).1
      (hPcorrUU J hJ).1 (hPcorrUU J hJ).2 (hPcorrEnd J hJ)
      (corePair_sub_coreTriple L d).1 (corePair_sub_coreTriple L d).2
  · intro J hJ X hX; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    exact sep_corr_core hCoreSepU (hDsub hd) (hPcorrUU J hJ).1 (hPcorrUU J hJ).2
      (hPcorrEnd J hJ) (le_refl _) (le_refl _)

lemma sep_core_pairs_triples {L : ℕ} {R D : Finset ℕ}
    (hCoreSepTT : ∀ d ∈ R, ∀ d' ∈ R, d ≠ d' → Iv.Sep (coreTriple L d) (coreTriple L d'))
    (hDsub : D ⊆ R) :
    (∀ X ∈ (R \ D).image (corePair L), ∀ Y ∈ D.image (coreTriple L), Iv.Sep X Y) ∧
    (∀ X ∈ (R \ D).image (corePair L), ∀ Y ∈ (R \ D).image (corePair L), X ≠ Y → Iv.Sep X Y) ∧
    (∀ X ∈ D.image (coreTriple L), ∀ Y ∈ D.image (coreTriple L), X ≠ Y → Iv.Sep X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hX Y hY; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hY
    have hdd' : d ≠ d' := by intro heq; subst heq; exact (Finset.mem_sdiff.mp hd).2 hd'
    exact sep_of_core_variant (hCoreSepTT d (Finset.mem_sdiff.mp hd).1 d' (hDsub hd') hdd')
      (corePair_sub_coreTriple L d).1 (corePair_sub_coreTriple L d).2 (le_refl _) (le_refl _)
  · intro X hX Y hY hXY; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hY
    have hdd' : d ≠ d' := by intro heq; apply hXY; rw [heq]
    exact sep_of_core_variant (hCoreSepTT d (Finset.mem_sdiff.mp hd).1 d' (Finset.mem_sdiff.mp hd').1 hdd')
      (corePair_sub_coreTriple L d).1 (corePair_sub_coreTriple L d).2
      (corePair_sub_coreTriple L d').1 (corePair_sub_coreTriple L d').2
  · intro X hX Y hY hXY; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hY
    have hdd' : d ≠ d' := by intro heq; apply hXY; rw [heq]
    exact sep_of_core_variant (hCoreSepTT d (hDsub hd) d' (hDsub hd') hdd')
      (le_refl _) (le_refl _) (le_refl _) (le_refl _)

noncomputable def goodFamilyS_build {k L : ℕ} (A : AuxFamilyS ((1 : ℝ) / 10) L)
    (Pmain Pcorr : Finset Iv) (D : Finset ℕ) (hPmain : ∀ I ∈ Pmain, IsMainPair k I)
    (hPcard : Pmain.card = k - (coreSetS ((1 : ℝ) / 10) L A k).card - CH L (H L k))
    (hPsep : ∀ I ∈ Pmain, ∀ J ∈ Pmain, I ≠ J → Iv.Sep I J) (hPcorrCard : Pcorr.card = CH L (H L k))
    (hPcorrUU : ∀ I ∈ Pcorr, I.lo ∈ USigned ((1 : ℝ) / 10) L A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) L A)
    (hPcorrEnd : ∀ I ∈ Pcorr, 1 ≤ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 1)
    (hPcorrSep : ∀ I ∈ Pcorr, ∀ J ∈ Pcorr, I ≠ J → Iv.Sep I J) (hDsub : D ⊆ coreSetS ((1 : ℝ) / 10) L A k)
    (hCoreSepTT : ∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ d' ∈ coreSetS ((1 : ℝ) / 10) L A k, d ≠ d' →
      Iv.Sep (coreTriple L d) (coreTriple L d'))
    (hCoreSepU : ∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ I : Iv,
      I.lo ∈ USigned ((1 : ℝ) / 10) L A → I.hi ∈ USigned ((1 : ℝ) / 10) L A →
      I.hi = I.lo + 1 → Iv.Sep (coreTriple L d) I)
    (hDsum : ∑ d ∈ D, (1 : ℚ) / (K L * d) =
      (1 - ∑ d ∈ coreSetS ((1 : ℝ) / 10) L A k, (corePair L d).mass - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass)
    (hk4M : 4096000 ≤ k) (hQ1 : 1 ≤ Q k) (hSmall : 8 * (H L k : ℝ) ^ ((11 : ℝ) / 10) + 3 ≤ (k : ℝ) / 1024)
    (hH20k : H L k ≤ 20 * k) (hHleRpow : (H L k : ℝ) ≤ (H L k : ℝ) ^ ((11 : ℝ) / 10))
    (hKLpos : 0 < K L) (hsum_le : (coreSetS ((1 : ℝ) / 10) L A k).card + CH L (H L k) ≤ k) :
    GoodFamily k := by
  classical
  set R := coreSetS ((1 : ℝ) / 10) L A k with hRdef
  set G3 := (R \ D).image (corePair L) with hG3def
  set G4 := D.image (coreTriple L) with hG4def
  have h1LoHi : ∀ I ∈ Pmain, I.lo ≤ I.hi := by
    intro I hI; obtain ⟨a, hIeq, -, -, -, -⟩ := hPmain I hI; rw [hIeq]; simp
  have h2LoHi : ∀ I ∈ Pcorr, I.lo ≤ I.hi := by
    intro I hI; have := (hPcorrEnd I hI).2.1; omega
  have h3LoHi : ∀ X ∈ G3, X.lo ≤ X.hi := by
    intro X hX; obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hX; simp
  obtain ⟨hSep12, hSep13, hSep14⟩ :=
    sep_main_all (A := A) hPmain (fun I hI => (hPcorrEnd I hI).2.2) hSmall hHleRpow hDsub
  obtain ⟨hSep23, hSep24⟩ :=
    sep_corr_core_all hCoreSepU hPcorrUU (fun I hI => (hPcorrEnd I hI).2.1) hDsub
  obtain ⟨hSep34, hSep33, hSep44⟩ :=
    sep_core_pairs_triples hCoreSepTT hDsub
  have hc3 : G3.card = R.card - D.card := by
    rw [hG3def, Finset.card_image_of_injective _ (corePair_injective hKLpos),
        Finset.card_sdiff_of_subset hDsub]
  have hc4 : G4.card = D.card := by
    rw [hG4def, Finset.card_image_of_injective _ (coreTriple_injective hKLpos)]
  have hDcard : D.card ≤ R.card := Finset.card_le_card hDsub
  have hcard_sum : (k - R.card - CH L (H L k)) + CH L (H L k) + (R.card - D.card) + D.card = k := by omega
  have hFcard := F_card hPcard hPcorrCard hc3 hc4 hcard_sum h1LoHi h2LoHi h3LoHi
    hSep12 hSep13 hSep14 hSep23 hSep24 hSep34
  have hFsep := F_sep hPsep hSep12 hSep13 hSep14 hPcorrSep hSep23 hSep24 hSep33 hSep34 hSep44
  have hFmass := F_mass hKLpos hDsub h1LoHi h2LoHi h3LoHi hSep12 hSep13 hSep14 hSep23 hSep24 hSep34 hDsum
  have hFone := F_one_le hPmain hk4M (fun I hI => (hPcorrEnd I hI).1) hKLpos hQ1 hDsub
  have hFhi := F_hi_le hPmain (fun I hI => (hPcorrEnd I hI).2.2) hSmall hH20k hk4M hDsub
  have hFlen := F_len (A := A) (D := D) hPmain (fun I hI => (hPcorrEnd I hI).2.1)
  exact {
    F := Pmain ∪ Pcorr ∪ G3 ∪ G4
    card_eq := hFcard
    one_le := hFone
    le_bound := hFhi
    len := hFlen
    sep := hFsep
    sum_eq := hFmass
  }

lemma choose_main_pairs {k L : ℕ} (A : AuxFamilyS ((1 : ℝ) / 10) L)
    (hk_asy : 4096000 ≤ k ∧ L + 1 ≤ Q k ∧
      (((coreSetS ((1 : ℝ) / 10) L A k).card : ℝ) ≤ (k : ℝ) / 8) ∧
      ((CH L (H L k) : ℝ) ≤ (k : ℝ) / 8) ∧
      ((H L k : ℝ) ^ ((11 : ℝ) / 10) ≤ (k : ℝ) / 1000000) ∧
      WcoreS ((1 : ℝ) / 10) L A k < 1 / 8)
    (hk_main : ∀ M, k / 2 ≤ M → M ≤ k → ∀ τ : ℚ, 1 / 2 < τ → τ < 1 →
      ∃ P : Finset Iv, P.card = M ∧ (∀ I ∈ P, IsMainPair k I) ∧
        (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
        τ - 2048 / k ≤ ∑ I ∈ P, I.mass ∧ ∑ I ∈ P, I.mass ≤ τ) :
    ∃ Pmain : Finset Iv,
      Pmain.card = k - (coreSetS ((1 : ℝ) / 10) L A k).card - CH L (H L k) ∧
      (∀ I ∈ Pmain, IsMainPair k I) ∧
      (∀ I ∈ Pmain, ∀ J ∈ Pmain, I ≠ J → Iv.Sep I J) ∧
      δ / 2 ≤ 1 - WcoreS ((1 : ℝ) / 10) L A k - ∑ I ∈ Pmain, I.mass ∧
      1 - WcoreS ((1 : ℝ) / 10) L A k - ∑ I ∈ Pmain, I.mass ≤ δ / 2 + 2048 / (k : ℚ) := by
  classical
  set Hk := H L k
  set R := coreSetS ((1 : ℝ) / 10) L A k
  have hsum4 : 4 * (R.card + CH L Hk) ≤ k := by
    have h1 : (R.card : ℝ) + (CH L Hk : ℝ) ≤ (k : ℝ) / 4 := by linarith [hk_asy.2.2.1, hk_asy.2.2.2.1]
    have h2 : ((4 * (R.card + CH L Hk) : ℕ) : ℝ) ≤ (k : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hMbound1 : k / 2 ≤ k - R.card - CH L Hk := by omega
  have hMbound2 : k - R.card - CH L Hk ≤ k := by omega
  have hδval : δ = (1 : ℚ) / 1000 := rfl
  have hWnn : 0 ≤ WcoreS ((1 : ℝ) / 10) L A k := WcoreS_nonneg _ _ _ _
  have hτlb : (1 : ℚ) / 2 < 1 - WcoreS ((1 : ℝ) / 10) L A k - δ / 2 := by rw [hδval]; linarith [hk_asy.2.2.2.2.2]
  have hτub : (1 - WcoreS ((1 : ℝ) / 10) L A k - δ / 2 : ℚ) < 1 := by rw [hδval]; linarith [hWnn]
  obtain ⟨Pmain, hPcard, hPmain, hPsep, hPmassLo, hPmassHi⟩ :=
    hk_main (k - R.card - CH L Hk) hMbound1 hMbound2 (1 - WcoreS ((1 : ℝ) / 10) L A k - δ / 2) hτlb hτub
  refine ⟨Pmain, hPcard, hPmain, hPsep, by linarith, by linarith [hPmassLo]⟩

lemma choose_correction_pairs {L : ℕ} (hL4 : 4 ≤ L) (A : AuxFamilyS ((1 : ℝ) / 10) L)
    (L₀ : ℕ) (hL0 : ∀ L', L₀ ≤ L' → ∀ H, L' ≤ H → ∃ C : CorrectionDataS ((1 : ℝ) / 10), C.L = L' ∧ C.H = H)
    (hLL0 : L₀ ≤ L) (Hk : ℕ) (hLH : L < Hk) (r₀ : ℚ) (hr₀DB : DenBound Hk r₀) :
    ∃ Pcorr : Finset Iv,
      Pcorr.card = CH L Hk ∧
      0 ≤ ∑ I ∈ Pcorr, I.mass ∧
      (∀ I ∈ Pcorr, I.lo ∈ USigned ((1 : ℝ) / 10) L A ∧ I.hi ∈ USigned ((1 : ℝ) / 10) L A) ∧
      (∀ I ∈ Pcorr, 1 ≤ I.lo ∧ I.hi = I.lo + 1 ∧ (I.hi : ℝ) ≤ 8 * (Hk : ℝ) ^ ((11 : ℝ) / 10) + 1) ∧
      (∀ I ∈ Pcorr, ∀ J ∈ Pcorr, I ≠ J → Iv.Sep I J) ∧
      (((∑ I ∈ Pcorr, I.mass : ℚ) : ℝ) ≤ 120 * (L : ℝ) ^ (-(1 : ℝ) / 40)) ∧
      DenBound L (r₀ - ∑ I ∈ Pcorr, I.mass) := by
  obtain ⟨CH_data, hCHL, hCHH⟩ := hL0 L hLL0 Hk hLH.le
  set C := mkCorrectionDataS CH_data hCHL A
  have hCH' : C.H = Hk := hCHH
  have hHltC : C.L < C.H := by rw [show C.L = L from rfl, hCH']; exact hLH
  have hr₀DBC : DenBound C.H r₀ := by rw [hCH']; exact hr₀DB
  obtain ⟨Pcorr, hPcorrCard, hPcorrMem, hPcorrUU, hPcorrEnd, hPcorrSep, hPcorrMassR, hPcorrDB⟩ :=
    descentS C hL4 hHltC r₀ hr₀DBC
  rw [show C.L = L from rfl, hCH'] at hPcorrCard
  rw [hCH'] at hPcorrEnd
  have hWcorr_nn : 0 ≤ ∑ I ∈ Pcorr, I.mass := WcorrS_nonneg hPcorrMem
  exact ⟨Pcorr, hPcorrCard, hWcorr_nn, hPcorrUU, hPcorrEnd, hPcorrSep, hPcorrMassR, hPcorrDB⟩

lemma goodFamilyS_at (L : ℕ) (_hL11 : 11 ≤ L) (hL4 : 4 ≤ L)
    (hmassbound : 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < 1 / 16000) (A : AuxFamilyS ((1 : ℝ) / 10) L)
    (L₀ : ℕ) (hL0 : ∀ L', L₀ ≤ L' → ∀ H, L' ≤ H → ∃ C : CorrectionDataS ((1 : ℝ) / 10), C.L = L' ∧ C.H = H)
    (hLL0 : L₀ ≤ L) (k : ℕ)
    (hk_asy : 4096000 ≤ k ∧ L + 1 ≤ Q k ∧ (((coreSetS ((1 : ℝ) / 10) L A k).card : ℝ) ≤ (k : ℝ) / 8) ∧
      ((CH L (H L k) : ℝ) ≤ (k : ℝ) / 8) ∧ ((H L k : ℝ) ^ ((11 : ℝ) / 10) ≤ (k : ℝ) / 1000000) ∧
      WcoreS ((1 : ℝ) / 10) L A k < 1 / 8)
    (hk_core : ((coreSetS ((1 : ℝ) / 10) L A k).card : ℝ) ≤ B L * (k : ℝ) ^ ((4 : ℝ) / 5) ∧
      WcoreS ((1 : ℝ) / 10) L A k < 1 / 8 ∧
      (∀ j, 1 ≤ j → j ≤ j₀ L → ∃ D ⊆ coreSetS ((1 : ℝ) / 10) L A k, ∑ d ∈ D, (1 : ℚ) / (K L * d) = j / K L) ∧
      (∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ d' ∈ coreSetS ((1 : ℝ) / 10) L A k, d ≠ d' →
        Iv.Sep (coreTriple L d) (coreTriple L d')) ∧
      (∀ d ∈ coreSetS ((1 : ℝ) / 10) L A k, ∀ I : Iv,
        I.lo ∈ USigned ((1 : ℝ) / 10) L A → I.hi ∈ USigned ((1 : ℝ) / 10) L A →
        I.hi = I.lo + 1 → Iv.Sep (coreTriple L d) I))
    (hk_main : ∀ M, k / 2 ≤ M → M ≤ k → ∀ τ : ℚ, 1 / 2 < τ → τ < 1 →
      ∃ P : Finset Iv, P.card = M ∧ (∀ I ∈ P, IsMainPair k I) ∧
        (∀ I ∈ P, ∀ J ∈ P, I ≠ J → Iv.Sep I J) ∧
        τ - 2048 / k ≤ ∑ I ∈ P, I.mass ∧ ∑ I ∈ P, I.mass ≤ τ) :
    Nonempty (GoodFamily k) := by
  classical
  set Hk := H L k with hHkdef
  set R := coreSetS ((1 : ℝ) / 10) L A k with hRdef
  obtain ⟨Pmain, hPcard, hPmain, hPsep, hr₀lb, hr₀ub⟩ := choose_main_pairs A hk_asy hk_main
  have hLH : L < Hk := by
    have h1 : L + 1 ≤ Q k := hk_asy.2.1
    have h2 : Q k ≤ Hk := Q_le_H L k
    omega
  have hr₀DB : DenBound Hk (1 - WcoreS ((1 : ℝ) / 10) L A k - ∑ I ∈ Pmain, I.mass) :=
    (DenBound.of_den_eq_one (by rfl : (1 : ℚ).den = 1)).sub
      (DenBound_WcoreS A k) |>.sub (DenBound_Wmain hPmain L)
  obtain ⟨Pcorr, hPcorrCard, hWcorr_nn, hPcorrUU, hPcorrEnd, hPcorrSep, hPcorrMassR, hPcorrDB⟩ :=
    choose_correction_pairs hL4 A L₀ hL0 hLL0 Hk hLH _ hr₀DB
  have hWcorrlt : (∑ I ∈ Pcorr, I.mass : ℚ) < δ / 16 :=
    Wcorr_lt_delta_div_16 hPcorrMassR hmassbound
  obtain ⟨hrlb, hrub, hrpos⟩ := residual_bounds hk_asy.1 hr₀lb hr₀ub hWcorr_nn hWcorrlt
  have hKLpos : 0 < K L := K_pos L
  have hrden : ((1 - WcoreS ((1 : ℝ) / 10) L A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass).den ∣ K L := by
    rw [K_eq_lcmIcc]; exact DenBound.lcm hPcorrDB
  set r : ℚ := (1 - WcoreS ((1 : ℝ) / 10) L A k - ∑ I ∈ Pmain, I.mass) - ∑ I ∈ Pcorr, I.mass with hrdef
  obtain ⟨j, hj1, hjeq⟩ := rat_eq_div_of_den_dvd hrpos hrden hKLpos
  have hjlej0 : j ≤ j₀ L := j_le_ceil hjeq hrub hKLpos
  obtain ⟨D, hDsub, hDsum⟩ := hk_core.2.2.1 j hj1 hjlej0
  have hDsum' : ∑ d ∈ D, (1 : ℚ) / (K L * d) = r := by rw [hDsum, ← hjeq]
  obtain ⟨hSmall, hH20k, hHleRpow⟩ := H_rpow_bounds hk_asy.1 hk_asy.2.2.2.2.1
  have hH20k_nat : Hk ≤ 20 * k := by exact_mod_cast hH20k
  have hQ1 : 1 ≤ Q k := by have := hk_asy.2.1; omega
  have hsumle : R.card + CH L Hk ≤ k := by
    have h1 : (R.card : ℝ) + (CH L Hk : ℝ) ≤ (k : ℝ) / 4 := by linarith [hk_asy.2.2.1, hk_asy.2.2.2.1]
    have h2 : ((4 * (R.card + CH L Hk) : ℕ) : ℝ) ≤ (k : ℝ) := by push_cast; linarith
    have h3 : 4 * (R.card + CH L Hk) ≤ k := by exact_mod_cast h2
    omega
  refine ⟨goodFamilyS_build A Pmain Pcorr D hPmain hPcard hPsep hPcorrCard
    hPcorrUU hPcorrEnd hPcorrSep hDsub hk_core.2.2.2.1 hk_core.2.2.2.2
    hDsum' hk_asy.1 hQ1 hSmall hH20k_nat hHleRpow hKLpos hsumle⟩

theorem goodFamilyS_of_large (L : ℕ) (hL11 : 11 ≤ L) (hL4 : 4 ≤ L)
    (hmassbound : 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < 1 / 16000)
    (A : AuxFamilyS ((1 : ℝ) / 10) L) (L₀ : ℕ)
    (hL0 : ∀ L', L₀ ≤ L' → ∀ H, L' ≤ H → ∃ C : CorrectionDataS ((1 : ℝ) / 10), C.L = L' ∧ C.H = H)
    (hLL0 : L₀ ≤ L) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k → Nonempty (GoodFamily k) := by
  classical
  obtain ⟨k_asy, hk_asy⟩ := asymptotic_packageS L hL11 A
  obtain ⟨k_core, hk_core⟩ := coreS ((1 : ℝ) / 10) L hL11 A (uSigned_density_ten L A)
  obtain ⟨k_main, hk_main⟩ := mainPairs
  refine ⟨max (max k_asy k_core) k_main, fun k hk => ?_⟩
  have hk_asy' : k_asy ≤ k := by omega
  have hk_core' : k_core ≤ k := by omega
  have hk_main' : k_main ≤ k := by omega
  exact goodFamilyS_at L hL11 hL4 hmassbound A L₀ hL0 hLL0 k
    (hk_asy k hk_asy') (hk_core k hk_core') (hk_main k hk_main')

end Erdos289.AssemblyS2

namespace Erdos289

/-- **Erdős Problem 289 (signed variant)**: for all sufficiently large `k`, there are `k`
pairwise-separated integer intervals of length `2` or `3`, contained in `[1, 20k]`,
with reciprocal masses summing to `1`. -/
theorem erdos289S2 : ∀ᶠ k : ℕ in Filter.atTop, Statement k := by
  obtain ⟨L₀, hL₀⟩ := correctionDataS_exists
  obtain ⟨L1, hL1⟩ := AssemblyS2.exists_L1
  obtain ⟨L2, hL2⟩ := lemma5S ((1 : ℝ) / 10) (by norm_num) (by norm_num)
  set L := max (max L₀ 11) (max L1 L2) with hLdef
  have hL_ge_L0 : L₀ ≤ L := by omega
  have hL11 : 11 ≤ L := by omega
  have hL4 : 4 ≤ L := by omega
  have hL_ge_L1 : L1 ≤ L := by omega
  have hL_ge_L2 : L2 ≤ L := by omega
  have hmassbound : 120 * (L : ℝ) ^ (-(1 : ℝ) / 40) < 1 / 16000 := hL1 L hL_ge_L1
  obtain ⟨A⟩ := hL2 L hL_ge_L2
  obtain ⟨k0, hk0⟩ := AssemblyS2.goodFamilyS_of_large L hL11 hL4 hmassbound A L₀ hL₀ hL_ge_L0
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  obtain ⟨G⟩ := hk0 k hk
  exact G.statement

/-- Audited candidate statement from `erdos289S2`. -/
theorem candidateStatementS2 : CandidateStatement := candidateStatement_of erdos289S2

end Erdos289
