import Erdos289CLT.Pools
import Erdos289.Intervals

/-!
# Assembly of the main theorem

Choose `B` (a power of two) large enough for `pairs_lemma`, `subsets_lemma`,
`tail_small` and `cand_enough`; build the stage-`B` pool and the seed family; for each
cutoff `X` choose the pools by Hall's theorem and iterate the transfer; take `X₀` with
`β ∈ G_{X₀}`; for `k` in the count interval of some `X ≥ X₀`, residue zero gives a
configuration of weight a positive integer below `2`, hence `1`.
-/

namespace Erdos289.CLT

open Finset

theorem main_theorem : MainStatement := by
  classical
  obtain ⟨c₀, hc₀, q₀, hpairs⟩ := pairs_lemma
  obtain ⟨n₀, hsubsets⟩ := subsets_lemma
  obtain ⟨B₁, htail⟩ := tail_small c₀ hc₀
  obtain ⟨B₂, hcand⟩ := cand_enough c₀ hc₀
  set N : ℕ := q₀ ⊔ n₀ ⊔ B₁ ⊔ B₂ ⊔ 9 with hNdef
  set B : ℕ := 2 ^ N with hBdef
  have hNltB : N < B := N.lt_two_pow_self
  have hB9 : 9 ≤ B := by omega
  have hB1 : 1 ≤ B := by omega
  have hq₀B : q₀ ≤ B := by omega
  have hn₀B : n₀ ≤ B := by omega
  have hB₁B : B₁ ≤ B := by omega
  have hB₂B : B₂ ≤ B := by omega
  have hBpow : B = 2 ^ Nat.log 2 B := by
    rw [hBdef, Nat.log_pow (by norm_num : 1 < 2)]
  have hBpp : IsPrimePow B := by
    rw [hBdef]
    exact (Nat.Prime.isPrimePow Nat.prime_two).pow (by omega : N ≠ 0)
  -- Choose, for every `q`, pairs data whenever `q` is a prime power `≥ B`.
  have hexMlo : ∀ q : ℕ, ∃ (Mq : Finset ℕ) (loq : ℕ → ℕ),
      IsPrimePow q → B ≤ q → PairsData c₀ q Mq loq := by
    intro q
    by_cases h : IsPrimePow q ∧ B ≤ q
    · obtain ⟨hpp, hBq⟩ := h
      obtain ⟨p, α, hp, hα, hpow⟩ := (isPrimePow_nat_iff q).mp hpp
      subst hpow
      have hq₀pq : q₀ ≤ p ^ α := hq₀B.trans hBq
      obtain ⟨Mq, loq, hcard, hprop⟩ := hpairs p α hp hα hq₀pq
      exact ⟨Mq, loq, fun _ _ => ⟨hcard, hprop⟩⟩
    · exact ⟨∅, fun _ => 0, fun hpp hBq => absurd ⟨hpp, hBq⟩ h⟩
  choose M lo hMlo using hexMlo
  -- The stage-`B` pool and the seed family.
  have hmass : (3 * (s B : ℝ)) * (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) < 1 / 20 := by
    have h := htail B hB₁B B
    rwa [Finset.Icc_self, Finset.sum_singleton] at h
  have henough : ((9 * s B + 2 * s B + 2 * (2 * Nat.log 2 B + 1) : ℕ) : ℝ) ≤ c₀ * B / Real.log B :=
    hcand B hB₂B B (le_refl B)
  obtain ⟨PBm, hPBmsub, hPBmcard, hPBmctr, hPBcard, hPBpair, hPBG, hPBsep, hPBchain, hPBw, hPBblock⟩ :=
    seed_pool_exists c₀ hc₀ B hB9 hBpp (M B) (lo B) (hMlo B hBpp (le_refl B))
      (hsubsets B hn₀B) henough hmass
  set PB : Finset Iv := PBm.image (poolIv (lo B)) with hPBdef
  set PBc : Finset ℕ := PBm.image (fun m => ctr B (lo B m) m) with hPBcdef
  have hPBc : PBc.card ≤ 2 * s B := by
    rw [hPBcdef]
    calc (PBm.image (fun m => ctr B (lo B m) m)).card ≤ PBm.card := Finset.card_image_le
      _ = 2 * s B := hPBmcard
  obtain ⟨Fm₀, hFm₀n, hFm₀u, hFm₀v, hFm₀bound, hFm₀supp, hFm₀S⟩ :=
    seed_family B (by omega) PB hPBcard hPBpair hPBG hPBsep hPBchain hPBw
  -- The support of the seed family is covered by small intervals, chain blocks, or the
  -- stage-`B` pool block.
  have hsupp₀ : ∀ I ∈ Fm₀.supp, I.hi ≤ 6 ∨
      ∃ a, 8 ∣ a ∧ (a ∈ chainLabels B ∨ a ∈ PBc) ∧ a ≤ I.lo + 1 ∧ I.hi ≤ a + 2 := by
    intro I hI
    rw [hFm₀supp] at hI
    rcases Finset.mem_union.mp hI with hIseed | hIPB
    · unfold seedSupp at hIseed
      rcases Finset.mem_union.mp hIseed with hIseed' | hItriple
      · rcases Finset.mem_union.mp hIseed' with hIsmall | hIpair
        · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hIsmall
          exact Or.inl (smallIv_block hh).2
        · obtain ⟨lab, hlab, rfl⟩ := Finset.mem_image.mp hIpair
          obtain ⟨hb1, hb2⟩ := chainIv_block lab false
          exact Or.inr ⟨lab, (chainLabels_dvd B hlab).1, Or.inl hlab, hb1, hb2⟩
      · obtain ⟨lab, hlab, rfl⟩ := Finset.mem_image.mp hItriple
        obtain ⟨hb1, hb2⟩ := chainIv_block lab true
        exact Or.inr ⟨lab, (chainLabels_dvd B hlab).1, Or.inl hlab, hb1, hb2⟩
    · obtain ⟨a, ha, h8, hle1, hle2⟩ := hPBblock I hIPB
      exact Or.inr ⟨a, h8, Or.inr ha, hle1, hle2⟩
  -- A cutoff `X₀` with the translate `β` already in `G_{X₀}`.
  obtain ⟨n_β, hn_β⟩ := exists_InG Fm₀.β
  set X₀ : ℕ := max B n_β with hX₀def
  have hInGX₀ : InG X₀ Fm₀.β := hn_β.mono (le_max_right B n_β)
  have hBX₀ : B ≤ X₀ := le_max_left B n_β
  refine ⟨seedLong B, Fm₀.u + Ucount B X₀, ?_⟩
  intro k hk
  obtain ⟨X, hX₀X, hkX1, hkX2⟩ := exists_cutoff (u₀ := Fm₀.u) hB1 hBpow hBX₀ k hk
  have hBX : B ≤ X := hBX₀.trans hX₀X
  obtain ⟨pool, hpoolcard, hpoolpair, hpoolsep, hpooldisj, hpoolsep_old, hpoolG, hpoolcover, hpoolmass⟩ :=
    stage_pools_exist c₀ hc₀ B X hB9 M lo
      (fun q hpp hBq _ => hMlo q hpp hBq.le)
      (fun q _ hBq _ => hsubsets q (hn₀B.trans hBq.le))
      (fun q hBq => hcand B hB₂B q hBq.le)
      PBc hPBc Fm₀.supp hsupp₀
  obtain ⟨Fm, hFmβ, hFmn, hFmS, hFmu, hFmv, hFmbound⟩ :=
    iterate_transfer B X hBX hB1 hBpow Fm₀ hFm₀n (by omega)
      pool hpoolcard hpoolpair hpoolsep hpooldisj hpoolsep_old hpoolG hpoolcover
  -- The bound at level `X` is below `2`.
  have hstage_le : ∀ q ∈ (Finset.Ioc B X).filter IsPrimePow,
      ((∑ J ∈ pool q, J.mass : ℚ):ℝ) ≤ (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2)) := by
    intro q hq
    obtain ⟨hqIoc, hqpp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hBq, hqX⟩ := Finset.mem_Ioc.mp hqIoc
    exact hpoolmass q hqpp hBq hqX
  have hsum1 : ((∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, ∑ J ∈ pool q, J.mass : ℚ):ℝ) ≤
      ∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2)) := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum hstage_le
  have hsubIoc : (Finset.Ioc B X).filter IsPrimePow ⊆ Finset.Icc B X := by
    intro q hq
    obtain ⟨hqIoc, _⟩ := Finset.mem_filter.mp hq
    obtain ⟨hBq, hqX⟩ := Finset.mem_Ioc.mp hqIoc
    exact Finset.mem_Icc.mpr ⟨hBq.le, hqX⟩
  have hnonneg : ∀ q ∈ Finset.Icc B X, q ∉ (Finset.Ioc B X).filter IsPrimePow →
      0 ≤ (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2)) := by
    intro q hq _
    obtain ⟨hBq, _⟩ := Finset.mem_Icc.mp hq
    have hq1 : 1 ≤ q := le_trans (by omega) hBq
    have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
    have hsnn : (0:ℝ) ≤ 3 * (s q:ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hqsq : (0:ℝ) ≤ c₀ * (q:ℝ)^2 := mul_nonneg hc₀.le (sq_nonneg _)
    have hnum : (0:ℝ) ≤ 4 * Real.log q := by linarith
    exact mul_nonneg hsnn (div_nonneg hnum hqsq)
  have hsum2 : ∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2))
      ≤ ∑ q ∈ Finset.Icc B X, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubIoc hnonneg
  have htailX : ∑ q ∈ Finset.Icc B X, (3 * (s q:ℝ)) * (4 * Real.log q / (c₀*(q:ℝ)^2)) < 1/20 :=
    htail B hB₁B X
  have hstagesum_lt : ((∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, ∑ J ∈ pool q, J.mass : ℚ):ℝ) < 1/20 :=
    lt_of_le_of_lt (hsum1.trans hsum2) htailX
  have hstagesum_lt' : (∑ q ∈ (Finset.Ioc B X).filter IsPrimePow, ∑ J ∈ pool q, J.mass : ℚ) < 1/20 := by
    have h2020 : (((1:ℚ)/20:ℚ):ℝ) = 1/20 := by norm_num
    rw [← h2020] at hstagesum_lt
    exact_mod_cast hstagesum_lt
  have hFmbound_lt : Fm.bound < 2 := by
    rw [hFmbound, hFm₀bound]
    linarith [hstagesum_lt']
  -- Realize residue `0` at count `k`.
  have hzero : InG Fm.n (0 - Fm.β) := by
    rw [hFmn, hFmβ, zero_sub]
    exact (hInGX₀.mono hX₀X).neg
  obtain ⟨C, hCP, hCnu, j, hCw⟩ := Fm.realizes 0 hzero k (by omega) (by omega)
  have hk1 : 1 ≤ k := by omega
  have hCF_card : C.F.card = k := hCnu
  have hCFNonempty : C.F.Nonempty := Finset.card_pos.mp (by omega)
  have hCwpos : 0 < C.w := Config.w_pos C hCFNonempty
  have hCwlt : C.w < Fm.bound := Fm.w_lt C hCP
  have h0j : (0:ℚ) < (j:ℚ) := by rw [hCw] at hCwpos; simpa using hCwpos
  have hj2 : (j:ℚ) < 2 := by rw [hCw] at hCwlt; linarith [hFmbound_lt]
  have hj1 : j = 1 := by
    have h0' : (0:ℤ) < j := by exact_mod_cast h0j
    have h2' : j < 2 := by exact_mod_cast hj2
    omega
  have hCw1 : C.w = 1 := by rw [hCw, hj1]; norm_num
  have hCF_sub : ∀ I ∈ C.F, I ∈ Fm.supp := fun I hI => Fm.mem_supp C hCP I hI
  exact ⟨C, hCnu, hCw1, fun I hI => Fm.supp_len I (hCF_sub I hI), fun I hI hlen => by
    have := Fm.supp_long I (hCF_sub I hI) hlen
    rwa [hFmS, hFm₀S] at this⟩

/-- The ordered form of the theorem: `k` intervals of length `2`, `3` or `4` inside
`{2, 3, …}`, consecutive ones separated by an unused integer, reciprocal sum `1`, with all
intervals longer than two taken from a fixed finite set. -/
structure Witness234 (k : ℕ) where
  intervals : Fin k → NatInterval
  two_le : ∀ i, 2 ≤ (intervals i).lo
  short : ∀ i, (intervals i).lo + 1 ≤ (intervals i).hi ∧ (intervals i).hi ≤ (intervals i).lo + 3
  separated : ∀ i j, i < j → (intervals i).Separated (intervals j)
  total_mass : ∑ i, (intervals i).mass = 1

def Statement234 : Prop :=
  ∃ S : Finset NatInterval, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ W : Witness234 k, ∀ i, (W.intervals i).length ≠ 2 → W.intervals i ∈ S

theorem statement234_of_main (h : MainStatement) : Statement234 := by
  classical
  obtain ⟨S, k₀, hk₀⟩ := h
  refine ⟨S.image (fun I => (⟨I.lo, I.hi⟩ : NatInterval)), k₀, ?_⟩
  intro k hk
  obtain ⟨C, hCnu, hCw, hCshort, hClong⟩ := hk₀ k hk
  set A : Finset ℕ := C.F.image Iv.lo with hAdef
  have hlo_injOn : Set.InjOn Iv.lo (C.F : Set Iv) := by
    intro I hI J hJ hlo
    simp only [Finset.mem_coe] at hI hJ
    by_contra hne
    have hsep := C.sep I hI J hJ hne
    have hIlen := C.len_ge I hI
    have hJlen := C.len_ge J hJ
    unfold Iv.Sep at hsep
    omega
  have hAcard : A.card = k := by
    rw [hAdef, Finset.card_image_of_injOn hlo_injOn]
    exact hCnu
  set e : Fin k ↪o ℕ := A.orderEmbOfFin hAcard with hedef
  have hmem : ∀ i : Fin k, e i ∈ A := fun i => Finset.orderEmbOfFin_mem A hAcard i
  have hex : ∀ i : Fin k, ∃ I ∈ C.F, Iv.lo I = e i := by
    intro i
    have hh := hmem i
    rw [hAdef, Finset.mem_image] at hh
    exact hh
  choose Ic hIcF hIclo using hex
  have hai : ∀ i, Iv.lo (Ic i) = e i := hIclo
  have hIcInj : Function.Injective Ic := by
    intro i j hij
    have : e i = e j := by rw [← hIclo i, ← hIclo j, hij]
    exact e.injective this
  set intervals : Fin k → NatInterval := fun i => ⟨e i, (Ic i).hi⟩ with hintervalsdef
  have htwo_le : ∀ i, 2 ≤ (intervals i).lo := by
    intro i
    show 2 ≤ e i
    rw [← hai i]
    exact C.two_le (Ic i) (hIcF i)
  have hshort : ∀ i, (intervals i).lo + 1 ≤ (intervals i).hi ∧
      (intervals i).hi ≤ (intervals i).lo + 3 := by
    intro i
    have hlenge := C.len_ge (Ic i) (hIcF i)
    have hle4 := hCshort (Ic i) (hIcF i)
    unfold ivLen at hle4
    have hlohi := Config.lo_le_hi C (hIcF i)
    show e i + 1 ≤ (Ic i).hi ∧ (Ic i).hi ≤ e i + 3
    rw [← hai i]
    omega
  have hsep' : ∀ i j, i < j → (intervals i).Separated (intervals j) := by
    intro i j hij
    show (Ic i).hi + 1 < e j
    have haij : e i < e j := e.lt_iff_lt.mpr hij
    have hne : Ic i ≠ Ic j := by
      intro heq
      rw [← hai i, ← hai j, heq] at haij
      exact lt_irrefl _ haij
    have hsep := C.sep (Ic i) (hIcF i) (Ic j) (hIcF j) hne
    have hlei := Config.lo_le_hi C (hIcF i)
    have hlej := Config.lo_le_hi C (hIcF j)
    unfold Iv.Sep at hsep
    rw [hai i] at hlei hsep
    rw [hai j] at hlej hsep
    omega
  have htotal : ∑ i, (intervals i).mass = 1 := by
    have hsurj : Set.SurjOn Ic (↑(Finset.univ : Finset (Fin k))) (↑C.F) := by
      intro I hI
      rw [Finset.mem_coe] at hI
      have hIloA : Iv.lo I ∈ A := by
        rw [hAdef, Finset.mem_image]; exact ⟨I, hI, rfl⟩
      have hIloA' : Iv.lo I ∈ Finset.image e Finset.univ := by
        rw [Finset.image_orderEmbOfFin_univ A hAcard]; exact hIloA
      obtain ⟨i, -, hei⟩ := Finset.mem_image.mp hIloA'
      have hlo_eq : Iv.lo (Ic i) = Iv.lo I := by rw [hai i, hei]
      have hIc_eq : Ic i = I :=
        hlo_injOn (Finset.mem_coe.mpr (hIcF i)) (Finset.mem_coe.mpr hI) hlo_eq
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), hIc_eq⟩
    have hstep : ∀ i ∈ (Finset.univ : Finset (Fin k)), (intervals i).mass = Iv.mass (Ic i) := by
      intro i _
      show Erdos289.NatInterval.mass ⟨e i, (Ic i).hi⟩ = Erdos289.mass (Ic i).lo (Ic i).hi
      unfold Erdos289.NatInterval.mass Erdos289.NatInterval.carrier Erdos289.mass
      rw [hai i]
    calc ∑ i, (intervals i).mass = ∑ I ∈ C.F, Iv.mass I := by
          apply Finset.sum_nbij Ic (fun i _ => hIcF i) (hIcInj.injOn) hsurj hstep
      _ = C.w := rfl
      _ = 1 := hCw
  refine ⟨⟨intervals, htwo_le, hshort, hsep', htotal⟩, ?_⟩
  intro i hlen
  have heq : ivLen (Ic i) = (intervals i).length := by
    show (Ic i).hi + 1 - (Ic i).lo = (Ic i).hi + 1 - e i
    rw [hai i]
  have hlenC : ivLen (Ic i) ≠ 2 := heq ▸ hlen
  have hIcS : Ic i ∈ S := hClong (Ic i) (hIcF i) hlenC
  show intervals i ∈ S.image (fun I => (⟨I.lo, I.hi⟩ : NatInterval))
  rw [Finset.mem_image]
  refine ⟨Ic i, hIcS, ?_⟩
  show (⟨(Ic i).lo, (Ic i).hi⟩ : NatInterval) = intervals i
  rw [hai i]

theorem statement234 : Statement234 := statement234_of_main main_theorem

end Erdos289.CLT
