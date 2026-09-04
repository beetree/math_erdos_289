import Erdos289.Defs
import Erdos289.Lemma5
import Erdos289.Lemma6
import Erdos289.Harmonic

/-!
# Section 5: the core pairs and the residual mass

Constants: `δ = 1/1000`, `K = lcm(1, …, L)`, `j₀ = ⌈K δ⌉`, `B = 4^{j₀}`; for the target `k`,
`Q = ⌊k^{4/5}⌋` and `H = K B Q + 2`. The core parameters are
`R = {d ∈ [Q, BQ) : [Kd - 1, Kd + 3] ∩ U = ∅}`; for each `d ∈ R` the core pair is
`[Kd + 1, Kd + 2]`, which may later be extended to the triple `[Kd, Kd + 2]`.
-/

namespace Erdos289

open Finset

/-- `δ = 1/1000`. -/
def δ : ℚ := 1 / 1000

/-- `K = lcm(1, …, L)`. -/
def K (L : ℕ) : ℕ := (Icc 1 L).lcm id

/-- `j₀ = ⌈K δ⌉`. -/
def j₀ (L : ℕ) : ℕ := ⌈(K L : ℚ) * δ⌉₊

/-- `B = 4^{j₀}`. -/
def B (L : ℕ) : ℕ := 4 ^ j₀ L

/-- `Q = ⌊k^{4/5}⌋`. -/
noncomputable def Q (k : ℕ) : ℕ := ⌊(k : ℝ) ^ ((4 : ℝ) / 5)⌋₊

/-- `H = K B Q + 2`. -/
noncomputable def H (L k : ℕ) : ℕ := K L * B L * Q k + 2

open Classical in
/-- The reserve parameters `R = {d ∈ [Q, BQ) : [Kd - 1, Kd + 3] ∩ U = ∅}` (5.2). -/
noncomputable def coreSet (L : ℕ) (A : AuxFamily L) (k : ℕ) : Finset ℕ :=
  (Ico (Q k) (B L * Q k)).filter
    (fun d => ∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ U L A)

/-- The core pair `[Kd + 1, Kd + 2]`. -/
def corePair (L d : ℕ) : Iv := Iv.pair (K L * d + 1)

/-- The extended core triple `[Kd, Kd + 2]`. -/
def coreTriple (L d : ℕ) : Iv := Iv.triple (K L * d)

/-- The mandatory core mass `W_core`. -/
noncomputable def Wcore (L : ℕ) (A : AuxFamily L) (k : ℕ) : ℚ :=
  ∑ d ∈ coreSet L A k, (corePair L d).mass

/-- For `L ≥ 11`, `K L ≥ 27720 = lcm(1, …, 11)`. -/
lemma K_ge_27720 {L : ℕ} (hL : 11 ≤ L) : 27720 ≤ K L := by
  have hsub : Icc 1 11 ⊆ Icc 1 L := Finset.Icc_subset_Icc_right hL
  have hdvd : (Icc 1 11).lcm id ∣ K L := Finset.lcm_mono hsub
  have heq : (Icc 1 11).lcm id = 27720 := by decide
  rw [heq] at hdvd
  have hpos : 0 < K L := by
    rw [K, Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    simp only [Finset.mem_Icc, id] at hx hx0
    omega
  exact Nat.le_of_dvd hpos hdvd

/-- `j₀ L ≤ K L * δ + 1` as reals. -/
lemma j₀_le (L : ℕ) : (j₀ L : ℝ) ≤ (K L : ℝ) * (δ : ℝ) + 1 := by
  have hδ : (0:ℚ) ≤ δ := by unfold δ; norm_num
  have h : (0:ℚ) ≤ (K L : ℚ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  have hq : (j₀ L : ℚ) ≤ (K L : ℚ) * δ + 1 := (Nat.ceil_lt_add_one h).le
  exact_mod_cast hq

/-- `Q k → ∞` as `k → ∞`. -/
lemma tendsto_Q_atTop : Filter.Tendsto Q Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/5)).comp tendsto_natCast_atTop_atTop)

/-- Two "windows" `[Kd-1, Kd+3]` around distinct `d, d'` are disjoint when `K ≥ 8`. -/
lemma window_disjoint {K d d' n : ℕ} (hK : 8 ≤ K) (hdd' : d < d')
    (_h1 : K * d - 1 ≤ n) (h2 : n ≤ K * d + 3)
    (h3 : K * d' - 1 ≤ n) (h4 : n ≤ K * d' + 3) : False := by
  have hexp : K * (d + 1) = K * d + K := by ring
  have hle : K * (d + 1) ≤ K * d' := Nat.mul_le_mul_left _ hdd'
  rw [hexp] at hle
  omega

open Classical in
/-- The excluded parameters within the reserve range `[Q, BQ)`. -/
noncomputable def Excl (L : ℕ) (A : AuxFamily L) (k : ℕ) : Finset ℕ :=
  Ico (Q k) (B L * Q k) \ coreSet L A k

open Classical in
/-- Every excluded `d` has some witness `n ∈ U` in its protected window. -/
lemma Excl_witness {L : ℕ} {A : AuxFamily L} {k : ℕ} {d : ℕ} (hd : d ∈ Excl L A k) :
    ∃ n, K L * d - 1 ≤ n ∧ n ≤ K L * d + 3 ∧ n ∈ U L A := by
  have hmem := Finset.mem_sdiff.mp hd
  have hd1 : d ∈ Ico (Q k) (B L * Q k) := hmem.1
  have hd2 : d ∉ coreSet L A k := hmem.2
  have hPd : ¬ (∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ U L A) := by
    intro hP
    exact hd2 (Finset.mem_filter.mpr ⟨hd1, hP⟩)
  push Not at hPd
  exact hPd

/-- The excluded count is at most the count of `U` in the relevant range. -/
lemma Excl_card_le {L : ℕ} (hL : 11 ≤ L) {A : AuxFamily L} {k : ℕ} (hQ1 : 1 ≤ Q k) :
    (Excl L A k).card ≤ (U L A ∩ Set.Icc 1 (K L * B L * Q k + 3)).ncard := by
  have hex : ∀ d ∈ Excl L A k, ∃ n, K L * d - 1 ≤ n ∧ n ≤ K L * d + 3 ∧ n ∈ U L A :=
    fun d hd => Excl_witness hd
  choose! f hf1 hf2 hf3 using hex
  have hK8 : 8 ≤ K L := le_trans (by norm_num) (K_ge_27720 hL)
  have hmaps : ∀ d ∈ Excl L A k, f d ∈ U L A ∩ Set.Icc 1 (K L * B L * Q k + 3) := by
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
  have hinj : Set.InjOn f (Excl L A k : Set ℕ) := by
    intro d hd d' hd' hff
    simp only [Finset.mem_coe] at hd hd'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact window_disjoint hK8 h (hf1 d hd) (hf2 d hd) (hff ▸ hf1 d' hd') (hff ▸ hf2 d' hd')
    · exact window_disjoint hK8 h (hf1 d' hd') (hf2 d' hd')
        (hff ▸ hf1 d hd) (hff ▸ hf2 d hd)
  have hfin : (U L A ∩ Set.Icc 1 (K L * B L * Q k + 3)).Finite :=
    (Set.finite_Icc 1 (K L * B L * Q k + 3)).subset Set.inter_subset_right
  have := Set.ncard_le_ncard_of_injOn f hmaps hinj hfin
  rwa [Set.ncard_coe_finset] at this

/-- Eventually, the excluded parameters number at most a quarter of `Q k`. -/
lemma Excl_bound_eventually (L : ℕ) (hL : 11 ≤ L) (A : AuxFamily L) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ((Excl L A k).card : ℝ) ≤ (Q k : ℝ) / 4 := by
  obtain ⟨C, hC⟩ := U_count L A
  have hCnonneg : 0 ≤ C := by
    by_contra h
    push Not at h
    have h2 := hC 2 (by norm_num)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hneg : C * (2:ℝ) / Real.log 2 < 0 := by
      apply div_neg_of_neg_of_pos _ hlog2
      nlinarith
    have hnn : (0:ℝ) ≤ ((U L A ∩ Set.Icc 1 2).ncard : ℝ) := Nat.cast_nonneg _
    linarith
  set M : ℝ := 4 * C * (K L * B L + 3) with hM
  have hlogtop : Filter.Tendsto (fun k => Real.log (Q k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_Q_atTop)
  obtain ⟨k_c, hk_c⟩ := Filter.eventually_atTop.mp (hlogtop.eventually_ge_atTop M)
  obtain ⟨k_a, hk_a⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop 1)
  refine ⟨max k_a k_c, fun k hk => ?_⟩
  have hQ1 : 1 ≤ Q k := hk_a k (le_trans (le_max_left _ _) hk)
  have hlogQ : M ≤ Real.log (Q k : ℝ) := hk_c k (le_trans (le_max_right _ _) hk)
  have hcard := Excl_card_le hL (A := A) hQ1
  have hX2 : 2 ≤ K L * B L * Q k + 3 := by omega
  have hUcount := hC (K L * B L * Q k + 3) hX2
  set X : ℕ := K L * B L * Q k + 3 with hXdef
  have hQr1 : (1:ℝ) ≤ (Q k : ℝ) := by exact_mod_cast hQ1
  have hKBnn : (0:ℝ) ≤ (K L : ℝ) * (B L : ℝ) := by positivity
  have hB1 : 1 ≤ B L := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hK1 : (1:ℝ) ≤ (K L : ℝ) := by exact_mod_cast le_trans (by norm_num) (K_ge_27720 hL)
  have hB1r : (1:ℝ) ≤ (B L : ℝ) := by exact_mod_cast hB1
  have hKB1 : (1:ℝ) ≤ (K L : ℝ) * (B L : ℝ) := by nlinarith
  have hXrle : (X : ℝ) ≤ (K L * B L + 3 : ℝ) * (Q k : ℝ) := by
    rw [hXdef]; push_cast; nlinarith
  have hQrleXr : (Q k : ℝ) ≤ (X : ℝ) := by
    rw [hXdef]; push_cast; nlinarith
  have hXrpos : (1:ℝ) < (X : ℝ) := by
    rw [hXdef]; push_cast; nlinarith
  have hlogXrpos : 0 < Real.log (X : ℝ) := Real.log_pos hXrpos
  have hlogXrM : M ≤ Real.log (X : ℝ) :=
    le_trans hlogQ (Real.log_le_log (by linarith) hQrleXr)
  have step1 : 4 * C * (X : ℝ) ≤ 4 * C * ((K L * B L + 3 : ℝ) * (Q k : ℝ)) :=
    mul_le_mul_of_nonneg_left hXrle (by linarith)
  have step2 : 4 * C * ((K L * B L + 3 : ℝ) * (Q k : ℝ)) = M * (Q k : ℝ) := by rw [hM]; ring
  have step3 : M * (Q k : ℝ) ≤ Real.log (X : ℝ) * (Q k : ℝ) :=
    mul_le_mul_of_nonneg_right hlogXrM (by linarith)
  have key : C * (X : ℝ) * 4 ≤ (Q k : ℝ) * Real.log (X : ℝ) := by nlinarith
  have hfinal : C * (X : ℝ) / Real.log (X : ℝ) ≤ (Q k : ℝ) / 4 :=
    (div_le_div_iff₀ hlogXrpos (by norm_num)).mpr (by nlinarith)
  calc ((Excl L A k).card : ℝ) ≤ ((U L A ∩ Set.Icc 1 X).ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ C * (X : ℝ) / Real.log (X : ℝ) := hUcount
    _ ≤ (Q k : ℝ) / 4 := hfinal

/-- The residual `j/K`, for `0 ≤ j ≤ j₀`, is realized as a sum over a subset of the core
confined to the first `j` dyadic bands `[Q, Q·4^j)`. -/
lemma residual_fill {L : ℕ} (hL : 11 ≤ L) {A : AuxFamily L} {k T₀ : ℕ}
    (hlemma6 : ∀ T, T₀ ≤ T → ∀ E ⊆ Ico T (4 * T), (E.card : ℝ) ≤ (T : ℝ) / 4 →
      ∃ D ⊆ Ico T (4 * T) \ E, ∑ d ∈ D, (1 : ℚ) / d = 1)
    (hT0 : T₀ ≤ Q k)
    (hExcl : ((Excl L A k).card : ℝ) ≤ (Q k : ℝ) / 4) :
    ∀ j, j ≤ j₀ L → ∃ D ⊆ coreSet L A k, D ⊆ Ico (Q k) (Q k * 4 ^ j) ∧
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
    have hband_sub : Ico T (4 * T) \ coreSet L A k ⊆ Excl L A k := by
      intro d hd
      simp only [Excl, Finset.mem_sdiff] at hd ⊢
      exact ⟨Finset.Ico_subset_Ico hTQ hTupper hd.1, hd.2⟩
    have hEcardle : (Ico T (4 * T) \ coreSet L A k).card ≤ (Excl L A k).card :=
      Finset.card_le_card hband_sub
    have hEcard : ((Ico T (4 * T) \ coreSet L A k).card : ℝ) ≤ (T : ℝ) / 4 := by
      have h1 : ((Ico T (4 * T) \ coreSet L A k).card : ℝ) ≤ ((Excl L A k).card : ℝ) := by
        exact_mod_cast hEcardle
      have h2 : (Q k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTQ
      linarith [hExcl]
    obtain ⟨D', hD'sub, hD'sum⟩ :=
      hlemma6 T hTge (Ico T (4 * T) \ coreSet L A k) Finset.sdiff_subset hEcard
    rw [Finset.sdiff_sdiff_self_left] at hD'sub
    have hD'core : D' ⊆ coreSet L A k := hD'sub.trans Finset.inter_subset_right
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

/-- **Section 5** of the paper, packaged. For `L ≥ 11` (so that `K ≥ 8` and `K δ ≥ 2`) and any
auxiliary family `A`, for all sufficiently large `k`:
the core count is `O(k^{4/5})`; the core mass is below `1/8`; every residual `j/K` with
`1 ≤ j ≤ j₀` is a sum of `1/(Kd)` over a subset of the core; core triples are mutually separated;
and every core triple is separated from every pair with both endpoints in `U`. -/
theorem core (L : ℕ) (hL : 11 ≤ L) (A : AuxFamily L) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ((coreSet L A k).card : ℝ) ≤ B L * (k : ℝ) ^ ((4 : ℝ) / 5) ∧
      Wcore L A k < 1 / 8 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ j₀ L →
        ∃ D ⊆ coreSet L A k, ∑ d ∈ D, (1 : ℚ) / (K L * d) = j / K L) ∧
      (∀ d ∈ coreSet L A k, ∀ d' ∈ coreSet L A k, d ≠ d' →
        Iv.Sep (coreTriple L d) (coreTriple L d')) ∧
      (∀ d ∈ coreSet L A k, ∀ I : Iv, I.lo ∈ U L A → I.hi ∈ U L A → I.hi = I.lo + 1 →
        Iv.Sep (coreTriple L d) I) := by
  classical
  have hK27720 := K_ge_27720 hL
  have hK8 : 8 ≤ K L := le_trans (by norm_num) hK27720
  obtain ⟨T₀, hT₀⟩ := lemma6
  obtain ⟨k₁, hk₁⟩ := Excl_bound_eventually L hL A
  obtain ⟨k_Q1, hk_Q1⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop 1)
  obtain ⟨k_QT0, hk_QT0⟩ := Filter.eventually_atTop.mp (tendsto_Q_atTop.eventually_ge_atTop T₀)
  refine ⟨max k₁ (max k_Q1 k_QT0), fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkQ1 : k_Q1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkQT0 : k_QT0 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hQ1 : 1 ≤ Q k := hk_Q1 k hkQ1
  have hQT0 : T₀ ≤ Q k := hk_QT0 k hkQT0
  have hExcl : ((Excl L A k).card : ℝ) ≤ (Q k : ℝ) / 4 := hk₁ k hk1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) core count bound
    have hcard_sub : coreSet L A k ⊆ Ico (Q k) (B L * Q k) := Finset.filter_subset _ _
    have hcard_le : (coreSet L A k).card ≤ B L * Q k := by
      have h1 := Finset.card_le_card hcard_sub
      rw [Nat.card_Ico] at h1
      omega
    have haQ : (Q k : ℝ) ≤ (k : ℝ) ^ ((4 : ℝ) / 5) := Nat.floor_le (by positivity)
    calc ((coreSet L A k).card : ℝ) ≤ ((B L * Q k : ℕ) : ℝ) := by exact_mod_cast hcard_le
      _ = (B L : ℝ) * (Q k : ℝ) := by push_cast; ring
      _ ≤ (B L : ℝ) * (k : ℝ) ^ ((4 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_left haQ (by positivity)
  · -- (b) core mass bound
    have step1 : Wcore L A k ≤ ∑ d ∈ coreSet L A k, (2 : ℚ) / (K L * d) := by
      rw [Wcore]
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
    have step2 : ∑ d ∈ coreSet L A k, (2 : ℚ) / (K L * d) ≤
        ∑ d ∈ Ico (Q k) (B L * Q k), (2 : ℚ) / (K L * d) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro d _ _; positivity
    have step3 : ∑ d ∈ Ico (Q k) (B L * Q k), (2 : ℚ) / (K L * d) =
        (2 / K L : ℚ) * ∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [div_mul_div_comm]; ring_nf
    have hWreal : (Wcore L A k : ℝ) ≤
        (2 / (K L : ℝ)) * (Real.log (B L) + 1 / (Q k : ℝ)) := by
      have hcast : (Wcore L A k : ℝ) ≤
          ((2 / K L : ℚ) * ∑ d ∈ Ico (Q k) (B L * Q k), (1 : ℚ) / d : ℚ) := by
        exact_mod_cast (le_trans step1 (le_trans step2 (le_of_eq step3)))
      have hsum := sum_inv_Ico_le_rat (Q k) (B L) (by omega)
      have hK0 : (0 : ℝ) ≤ 2 / (K L : ℝ) := by positivity
      calc (Wcore L A k : ℝ)
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
    have : (Wcore L A k : ℝ) < 1 / 8 := lt_of_le_of_lt hWreal hfinal
    have hfin2 : (Wcore L A k : ℝ) < ((1/8 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hfin2
  · -- (c) residual filling
    intro j hj1 hjle
    obtain ⟨D, hDsub, _, hDsum⟩ :=
      residual_fill hL (A := A) (k := k) hT₀ hQT0 hExcl j hjle
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
  · -- (e) core triples separated from every `U`-pair
    intro d hd I hIlo hIhi hIlen
    have hdmem : ∀ n, K L * d - 1 ≤ n → n ≤ K L * d + 3 → n ∉ U L A :=
      (Finset.mem_filter.mp hd).2
    have h1 : ¬ (K L * d - 1 ≤ I.lo ∧ I.lo ≤ K L * d + 3) := by
      rintro ⟨ha, hb⟩; exact hdmem I.lo ha hb hIlo
    have h2 : ¬ (K L * d - 1 ≤ I.hi ∧ I.hi ≤ K L * d + 3) := by
      rintro ⟨ha, hb⟩; exact hdmem I.hi ha hb hIhi
    simp only [Iv.Sep, coreTriple, Iv.triple]
    omega

end Erdos289
