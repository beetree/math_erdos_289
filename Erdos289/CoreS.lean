import Erdos289.SignedDefs
import Erdos289.Core

/-!
# The signed analogue of the core lemma

The signed analogue of `Erdos289.core` (`Erdos289/Core.lean`), with the protected set
`USigned ε L A` in place of `U L A`, and a density-zero hypothesis in place of `U_count`.
Only the exclusion bound changes (`Excl_bound_eventually` becomes `CoreS.ExclS_bound_eventually`,
using `κ := 1 / (8 K B + 8)`); everything else (harmonic bound, residual filling via `lemma6`,
separations) is copied from `Erdos289.core` with `U` replaced by `USigned`.
-/

namespace Erdos289

open Finset

open Classical in
/-- The reserve parameters `R = {d ∈ [Q, BQ) : [Kd - 1, Kd + 3] ∩ USigned = ∅}`, the signed
analogue of `coreSet`. -/
noncomputable def coreSetS (ε : ℝ) (L : ℕ) (A : AuxFamilyS ε L) (k : ℕ) : Finset ℕ :=
  (Finset.Ico (Q k) (B L * Q k)).filter
    (fun d => ∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ USigned ε L A)

/-- The mandatory core mass, the signed analogue of `Wcore`. -/
noncomputable def WcoreS (ε : ℝ) (L : ℕ) (A : AuxFamilyS ε L) (k : ℕ) : ℚ :=
  ∑ d ∈ coreSetS ε L A k, (corePair L d).mass

namespace CoreS

open Classical in
/-- The excluded parameters within the reserve range `[Q, BQ)`, the signed analogue of `Excl`. -/
noncomputable def ExclS (ε : ℝ) (L : ℕ) (A : AuxFamilyS ε L) (k : ℕ) : Finset ℕ :=
  Ico (Q k) (B L * Q k) \ coreSetS ε L A k

open Classical in
/-- Every excluded `d` has some witness `n ∈ USigned` in its protected window. -/
lemma ExclS_witness {ε : ℝ} {L : ℕ} {A : AuxFamilyS ε L} {k : ℕ} {d : ℕ}
    (hd : d ∈ ExclS ε L A k) :
    ∃ n, K L * d - 1 ≤ n ∧ n ≤ K L * d + 3 ∧ n ∈ USigned ε L A := by
  have hmem := Finset.mem_sdiff.mp hd
  have hd1 : d ∈ Ico (Q k) (B L * Q k) := hmem.1
  have hd2 : d ∉ coreSetS ε L A k := hmem.2
  have hPd : ¬ (∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ USigned ε L A) := by
    intro hP
    exact hd2 (Finset.mem_filter.mpr ⟨hd1, hP⟩)
  push Not at hPd
  exact hPd

/-- The excluded count is at most the count of `USigned` in the relevant range. -/
lemma ExclS_card_le {ε : ℝ} {L : ℕ} (hL : 11 ≤ L) {A : AuxFamilyS ε L} {k : ℕ}
    (hQ1 : 1 ≤ Q k) :
    (ExclS ε L A k).card ≤ (USigned ε L A ∩ Set.Icc 1 (K L * B L * Q k + 3)).ncard := by
  have hex : ∀ d ∈ ExclS ε L A k, ∃ n, K L * d - 1 ≤ n ∧ n ≤ K L * d + 3 ∧ n ∈ USigned ε L A :=
    fun d hd => ExclS_witness hd
  choose! f hf1 hf2 hf3 using hex
  have hK8 : 8 ≤ K L := le_trans (by norm_num) (K_ge_27720 hL)
  have hmaps : ∀ d ∈ ExclS ε L A k, f d ∈ USigned ε L A ∩ Set.Icc 1 (K L * B L * Q k + 3) := by
    intro d hd
    have hmem := Finset.mem_sdiff.mp hd
    have hd1 : d ∈ Ico (Q k) (B L * Q k) := hmem.1
    rw [Finset.mem_Ico] at hd1
    obtain ⟨hdlo, hdhi⟩ := hd1
    have hd1' : 1 ≤ d := le_trans hQ1 hdlo
    have hKd : 27720 ≤ K L * d :=
      le_trans (K_ge_27720 hL) (Nat.le_mul_of_pos_right (K L) hd1')
    have hKdub : K L * d ≤ K L * B L * Q k := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (le_of_lt hdhi)
    have hlo := hf1 d hd
    have hhi := hf2 d hd
    exact ⟨hf3 d hd, by omega, by omega⟩
  have hinj : Set.InjOn f (ExclS ε L A k : Set ℕ) := by
    intro d hd d' hd' hff
    simp only [Finset.mem_coe] at hd hd'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact window_disjoint hK8 h (hf1 d hd) (hf2 d hd) (hff ▸ hf1 d' hd') (hff ▸ hf2 d' hd')
    · exact window_disjoint hK8 h (hf1 d' hd') (hf2 d' hd')
        (hff ▸ hf1 d hd) (hff ▸ hf2 d hd)
  have hfin : (USigned ε L A ∩ Set.Icc 1 (K L * B L * Q k + 3)).Finite :=
    (Set.finite_Icc 1 (K L * B L * Q k + 3)).subset Set.inter_subset_right
  have := Set.ncard_le_ncard_of_injOn f hmaps hinj hfin
  rwa [Set.ncard_coe_finset] at this

/-- Eventually, the excluded parameters number at most a quarter of `Q k`. Uses the density-zero
hypothesis with `κ := 1 / (8 K B + 8)`, so that eventually `|USigned ∩ [1, KBQ+3]| ≤ κ (KBQ+3) ≤
Q/4` (the last step needing only `Q ≥ 1`). -/
lemma ExclS_bound_eventually {ε : ℝ} {L : ℕ} (hL : 11 ≤ L) {A : AuxFamilyS ε L}
    (hU : ∀ κ : ℝ, 0 < κ → ∀ᶠ X : ℕ in Filter.atTop,
      ((USigned ε L A ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * X) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ((ExclS ε L A k).card : ℝ) ≤ (Q k : ℝ) / 4 := by
  have hK27720 := K_ge_27720 hL
  have hK1 : 1 ≤ K L := le_trans (by norm_num) hK27720
  have hB1 : 1 ≤ B L := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hKBpos : 0 < K L * B L := by positivity
  set κ : ℝ := 1 / (8 * (K L : ℝ) * (B L : ℝ) + 8) with hκdef
  have hKBr : (1 : ℝ) ≤ (K L : ℝ) * (B L : ℝ) := by
    have hK1r : (1 : ℝ) ≤ (K L : ℝ) := by exact_mod_cast hK1
    have hB1r : (1 : ℝ) ≤ (B L : ℝ) := by exact_mod_cast hB1
    nlinarith
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (hU κ hκpos)
  have hpointwise : ∀ k, Q k ≤ K L * B L * Q k + 3 := by
    intro k
    have h1 : Q k ≤ Q k * (K L * B L) := Nat.le_mul_of_pos_right (Q k) hKBpos
    have h2 : Q k * (K L * B L) = K L * B L * Q k := by ring
    omega
  have hX_atTop : Filter.Tendsto (fun k => K L * B L * Q k + 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hpointwise tendsto_Q_atTop
  obtain ⟨k_X, hk_X⟩ := Filter.eventually_atTop.mp (hX_atTop.eventually_ge_atTop X₀)
  obtain ⟨k_a, hk_a⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop 1)
  refine ⟨max k_a k_X, fun k hk => ?_⟩
  have hQ1 : 1 ≤ Q k := hk_a k (le_trans (le_max_left _ _) hk)
  have hXge : X₀ ≤ K L * B L * Q k + 3 := hk_X k (le_trans (le_max_right _ _) hk)
  have hcard := ExclS_card_le hL (A := A) hQ1
  have hUbound := hX₀ (K L * B L * Q k + 3) hXge
  have hQr1 : (1 : ℝ) ≤ (Q k : ℝ) := by exact_mod_cast hQ1
  have hprod : (Q k : ℝ) ≤ (K L : ℝ) * (B L : ℝ) * (Q k : ℝ) := by nlinarith
  have hXreal_le : κ * ((K L * B L * Q k + 3 : ℕ) : ℝ) ≤ (Q k : ℝ) / 4 := by
    rw [hκdef]
    push_cast
    rw [div_mul_eq_mul_div, one_mul,
      div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith [hprod, hQr1]
  calc ((ExclS ε L A k).card : ℝ)
      ≤ ((USigned ε L A ∩ Set.Icc 1 (K L * B L * Q k + 3)).ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ κ * ((K L * B L * Q k + 3 : ℕ) : ℝ) := hUbound
    _ ≤ (Q k : ℝ) / 4 := hXreal_le

/-- The residual `j/K`, for `0 ≤ j ≤ j₀`, is realized as a sum over a subset of the signed core
confined to the first `j` dyadic bands `[Q, Q·4^j)`; the signed analogue of `residual_fill`. -/
lemma residual_fill_S {ε : ℝ} {L : ℕ} (hL : 11 ≤ L) {A : AuxFamilyS ε L} {k T₀ : ℕ}
    (hlemma6 : ∀ T, T₀ ≤ T → ∀ E ⊆ Ico T (4 * T), (E.card : ℝ) ≤ (T : ℝ) / 4 →
      ∃ D ⊆ Ico T (4 * T) \ E, ∑ d ∈ D, (1 : ℚ) / d = 1)
    (hT0 : T₀ ≤ Q k)
    (hExcl : ((ExclS ε L A k).card : ℝ) ≤ (Q k : ℝ) / 4) :
    ∀ j, j ≤ j₀ L → ∃ D ⊆ coreSetS ε L A k, D ⊆ Ico (Q k) (Q k * 4 ^ j) ∧
      ∑ d ∈ D, (1 : ℚ) / (K L * d) = (j : ℚ) / K L := by
  intro j
  induction j with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    intro hjle
    obtain ⟨D, hDsub, hDband, hDsum⟩ := ih (by omega)
    set T := Q k * 4 ^ n with hTdef
    have hTQ : Q k ≤ T := by
      rw [hTdef]; exact Nat.le_mul_of_pos_right (Q k) (by positivity)
    have hTge : T₀ ≤ T := le_trans hT0 hTQ
    have h4n1 : 4 ^ (n + 1) ≤ B L := by
      rw [B]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hTupper : 4 * T ≤ B L * Q k := by
      calc 4 * T = Q k * 4 ^ (n + 1) := by rw [hTdef]; ring
        _ ≤ Q k * B L := Nat.mul_le_mul_left _ h4n1
        _ = B L * Q k := mul_comm _ _
    have hband_sub : Ico T (4 * T) \ coreSetS ε L A k ⊆ ExclS ε L A k := by
      intro d hd
      simp only [ExclS, Finset.mem_sdiff] at hd ⊢
      exact ⟨Finset.Ico_subset_Ico hTQ hTupper hd.1, hd.2⟩
    have hEcardle : (Ico T (4 * T) \ coreSetS ε L A k).card ≤ (ExclS ε L A k).card :=
      Finset.card_le_card hband_sub
    have hEcard : ((Ico T (4 * T) \ coreSetS ε L A k).card : ℝ) ≤ (T : ℝ) / 4 := by
      have h1 : ((Ico T (4 * T) \ coreSetS ε L A k).card : ℝ) ≤ ((ExclS ε L A k).card : ℝ) := by
        exact_mod_cast hEcardle
      have h2 : (Q k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTQ
      linarith [hExcl]
    obtain ⟨D', hD'sub, hD'sum⟩ :=
      hlemma6 T hTge (Ico T (4 * T) \ coreSetS ε L A k) Finset.sdiff_subset hEcard
    rw [Finset.sdiff_sdiff_self_left] at hD'sub
    have hD'core : D' ⊆ coreSetS ε L A k := hD'sub.trans Finset.inter_subset_right
    have hD'band : D' ⊆ Ico T (4 * T) := hD'sub.trans Finset.inter_subset_left
    have hbandeq : Q k * 4 ^ (n + 1) = 4 * T := by rw [hTdef]; ring
    refine ⟨D ∪ D', Finset.union_subset hDsub hD'core, ?_, ?_⟩
    · apply Finset.union_subset
      · exact hDband.trans (Finset.Ico_subset_Ico (le_refl _) (by rw [hTdef]; nlinarith [pow_pos (show (0:ℕ) < 4 by norm_num) n]))
      · rw [hbandeq]; exact hD'band.trans (Finset.Ico_subset_Ico hTQ (le_refl _))
    · have hdisj : Disjoint D D' := by
        apply Finset.disjoint_left.mpr
        intro d hdD hdD'
        have h1 := hDband hdD
        have h2 := hD'band hdD'
        rw [Finset.mem_Ico] at h1 h2
        omega
      rw [Finset.sum_union hdisj, hDsum]
      have hsum2 : ∑ d ∈ D', (1 : ℚ) / (K L * d) = (1 : ℚ) / (K L) * ∑ d ∈ D', (1 : ℚ) / d := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by rw [div_mul_div_comm, one_mul]
      rw [hsum2, hD'sum]
      have hK0 : (K L : ℚ) ≠ 0 := by
        have := K_ge_27720 hL; positivity
      push_cast
      field_simp

end CoreS

/-- **Signed analogue of `core`**. For `L ≥ 11` and any signed auxiliary family `A` whose
protected set `USigned ε L A` has density zero, for all sufficiently large `k`:
the core count is `O(k^{4/5})`; the core mass is below `1/8`; every residual `j/K` with
`1 ≤ j ≤ j₀` is a sum of `1/(Kd)` over a subset of the core; core triples are mutually separated;
and every core triple is separated from every pair with both endpoints in `USigned`. -/
theorem coreS (ε : ℝ) (L : ℕ) (hL : 11 ≤ L) (A : AuxFamilyS ε L)
    (hU : ∀ κ : ℝ, 0 < κ → ∀ᶠ X : ℕ in Filter.atTop,
      ((USigned ε L A ∩ Set.Icc 1 X).ncard : ℝ) ≤ κ * X) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ((coreSetS ε L A k).card : ℝ) ≤ B L * (k : ℝ) ^ ((4 : ℝ) / 5) ∧
      WcoreS ε L A k < 1 / 8 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ j₀ L → ∃ D ⊆ coreSetS ε L A k, ∑ d ∈ D, (1 : ℚ) / (K L * d) = j / K L) ∧
      (∀ d ∈ coreSetS ε L A k, ∀ d' ∈ coreSetS ε L A k, d ≠ d' →
        Iv.Sep (coreTriple L d) (coreTriple L d')) ∧
      (∀ d ∈ coreSetS ε L A k, ∀ I : Iv, I.lo ∈ USigned ε L A → I.hi ∈ USigned ε L A →
        I.hi = I.lo + 1 → Iv.Sep (coreTriple L d) I) := by
  classical
  have hK27720 := K_ge_27720 hL
  have hK8 : 8 ≤ K L := le_trans (by norm_num) hK27720
  obtain ⟨T₀, hT₀⟩ := lemma6
  obtain ⟨k₁, hk₁⟩ := CoreS.ExclS_bound_eventually hL (A := A) hU
  obtain ⟨k_Q1, hk_Q1⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop 1)
  obtain ⟨k_QT0, hk_QT0⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop T₀)
  refine ⟨max k₁ (max k_Q1 k_QT0), fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkQ1 : k_Q1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkQT0 : k_QT0 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hQ1 : 1 ≤ Q k := hk_Q1 k hkQ1
  have hQT0 : T₀ ≤ Q k := hk_QT0 k hkQT0
  have hExcl : ((CoreS.ExclS ε L A k).card : ℝ) ≤ (Q k : ℝ) / 4 := hk₁ k hk1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) core count bound
    have hcard_sub : coreSetS ε L A k ⊆ Ico (Q k) (B L * Q k) := Finset.filter_subset _ _
    have hcard_le : (coreSetS ε L A k).card ≤ B L * Q k := by
      have h1 := Finset.card_le_card hcard_sub
      rw [Nat.card_Ico] at h1
      omega
    have haQ : (Q k : ℝ) ≤ (k : ℝ) ^ ((4 : ℝ) / 5) := Nat.floor_le (by positivity)
    calc ((coreSetS ε L A k).card : ℝ) ≤ ((B L * Q k : ℕ) : ℝ) := by exact_mod_cast hcard_le
      _ = (B L : ℝ) * (Q k : ℝ) := by push_cast; ring
      _ ≤ (B L : ℝ) * (k : ℝ) ^ ((4 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_left haQ (by positivity)
  · -- (b) core mass bound
    have step1 : WcoreS ε L A k ≤ ∑ d ∈ coreSetS ε L A k, (2 : ℚ) / (K L * d) := by
      rw [WcoreS]
      apply Finset.sum_le_sum
      intro d hd
      have hdmem : d ∈ Ico (Q k) (B L * Q k) := (Finset.mem_filter.mp hd).1
      have hd1 : 1 ≤ d := le_trans hQ1 (Finset.mem_Ico.mp hdmem).1
      have hKdN : 0 < K L * d := by positivity
      have hKdQ : (0 : ℚ) < (K L : ℚ) * (d : ℚ) := by exact_mod_cast hKdN
      calc (corePair L d).mass ≤ 2 / ((K L * d + 1 : ℕ) : ℚ) := pair_mass_le (by positivity)
        _ = 2 / ((K L : ℚ) * d + 1) := by push_cast; ring_nf
        _ ≤ (2 : ℚ) / (K L * d) :=
            div_le_div_of_nonneg_left (by norm_num) hKdQ (by linarith)
    have step2 : ∑ d ∈ coreSetS ε L A k, (2 : ℚ) / (K L * d) ≤
        ∑ d ∈ Ico (Q k) (B L * Q k), (2 : ℚ) / (K L * d) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro d _ _; positivity
    have step3 : ∑ d ∈ Ico (Q k) (B L * Q k), (2 : ℚ) / (K L * d) =
        (2 / K L : ℚ) * ∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [div_mul_div_comm]; ring_nf
    have hWreal : (WcoreS ε L A k : ℝ) ≤
        (2 / (K L : ℝ)) * (Real.log (B L) + 1 / (Q k : ℝ)) := by
      have hcast : (WcoreS ε L A k : ℝ) ≤
          ((2 / K L : ℚ) * ∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d : ℚ) := by
        exact_mod_cast (le_trans step1 (le_trans step2 (le_of_eq step3)))
      have hsum := sum_inv_Ico_le_rat (Q k) (B L) (by omega)
      have hK0 : (0 : ℝ) ≤ 2 / (K L : ℝ) := by positivity
      calc (WcoreS ε L A k : ℝ)
          ≤ ((2 / K L : ℚ) * ∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d : ℚ) := hcast
        _ = (2 / (K L : ℝ)) * ((∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d : ℚ) : ℝ) := by
            push_cast; ring
        _ ≤ (2 / (K L : ℝ)) * (Real.log (B L) + 1 / (Q k : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum hK0
    have hlogB : Real.log (B L) = (j₀ L : ℝ) * Real.log 4 := by
      rw [B]; push_cast; rw [Real.log_pow]
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
      linarith
    have hj0le : (j₀ L : ℝ) ≤ (K L : ℝ) * δ + 1 := j₀_le L
    have hδnn : (0:ℝ) ≤ (δ:ℝ) := by
      have : (0:ℚ) ≤ δ := by unfold δ; norm_num
      exact_mod_cast this
    have hKLr : (27720 : ℝ) ≤ (K L : ℝ) := by exact_mod_cast hK27720
    have hQkr : (1 : ℝ) ≤ (Q k : ℝ) := by exact_mod_cast hQ1
    have hδval : (δ : ℝ) = 1 / 1000 := by unfold δ; push_cast; norm_num
    have hfinal : (2 / (K L : ℝ)) * (Real.log (B L) + 1 / (Q k : ℝ)) < 1 / 8 := by
      rw [hlogB]
      rw [hδval] at hj0le
      have hlog4nn : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hKLpos : (0:ℝ) < (K L : ℝ) := by linarith
      have expand : (2 / (K L:ℝ)) * ((j₀ L:ℝ) * Real.log 4 + 1/(Q k:ℝ))
          = (2/(K L:ℝ)) * ((j₀ L:ℝ) * Real.log 4) + (2/(K L:ℝ)) * (1/(Q k:ℝ)) := by ring
      rw [expand]
      have ht1 : (2:ℝ)/(K L) * ((j₀ L:ℝ) * Real.log 4) ≤
          (2:ℝ)/(K L) * (((K L:ℝ) * (1/1000) + 1) * 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hj0le hlog4 hlog4nn (by linarith)) (by positivity)
      have ht2 : (2:ℝ)/(K L) * (((K L:ℝ) * (1/1000) + 1) * 3) = 6/1000 + 6/(K L:ℝ) := by
        field_simp; ring
      have ht3 : (2:ℝ)/(K L) * (1/(Q k:ℝ)) ≤ 2/(K L:ℝ) := by
        have hQle1 : (1:ℝ)/(Q k:ℝ) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        have h2Knn : (0:ℝ) ≤ 2/(K L:ℝ) := by positivity
        calc (2:ℝ)/(K L) * (1/(Q k:ℝ)) ≤ 2/(K L:ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hQle1 h2Knn
          _ = 2/(K L:ℝ) := by ring
      have ht5 : (8:ℝ)/(K L:ℝ) ≤ 8/27720 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKLr
      have hsum68 : (6:ℝ)/(K L:ℝ) + 2/(K L:ℝ) = 8/(K L:ℝ) := by ring
      linarith
    have : (WcoreS ε L A k : ℝ) < 1 / 8 := lt_of_le_of_lt hWreal hfinal
    have hfin2 : (WcoreS ε L A k : ℝ) < ((1/8 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hfin2
  · -- (c) residual filling
    intro j hj1 hjle
    obtain ⟨D, hDsub, _, hDsum⟩ :=
      CoreS.residual_fill_S hL (A := A) (k := k) hT₀ hQT0 hExcl j hjle
    exact ⟨D, hDsub, hDsum⟩
  · -- (d) distinct core triples are separated
    intro d _ d' _ hne
    simp only [Iv.Sep, coreTriple, Iv.triple]
    rcases lt_or_gt_of_ne hne with h | h
    · have hmul : K L * (d + 1) ≤ K L * d' := Nat.mul_le_mul_left _ h
      have hexp : K L * (d + 1) = K L * d + K L := by ring
      omega
    · have hmul : K L * (d' + 1) ≤ K L * d := Nat.mul_le_mul_left _ h
      have hexp : K L * (d' + 1) = K L * d' + K L := by ring
      omega
  · -- (e) core triples separated from every `USigned`-pair
    intro d hd I hIlo hIhi hIlen
    have hdmem : ∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ USigned ε L A :=
      (Finset.mem_filter.mp hd).2
    have h1 : ¬ (K L * d - 1 ≤ I.lo ∧ I.lo ≤ K L * d + 3) := by
      rintro ⟨ha, hb⟩; exact hdmem I.lo ha hb hIlo
    have h2 : ¬ (K L * d - 1 ≤ I.hi ∧ I.hi ≤ K L * d + 3) := by
      rintro ⟨ha, hb⟩; exact hdmem I.hi ha hb hIhi
    simp only [Iv.Sep, coreTriple, Iv.triple]
    omega

end Erdos289
