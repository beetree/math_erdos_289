import Erdos289CLT.Seed
import Erdos289CLT.StagePool
import Erdos289CLT.Stages

/-!
# The stage-`B` pool and the pools of all later stages

`seed_pool_exists` builds the stage-`B` pool feeding `seed_family`; `stage_pools_exist`
selects, by Hall's theorem (`choose_pools`), the pools of all prime-power stages
`B < q ≤ X` with the properties required by `iterate_transfer`.
-/

namespace Erdos289.CLT

open Finset

/-- The data delivered by `pairs_lemma` at a stage `q`. -/
def PairsData (c₀ : ℝ) (q : ℕ) (M : Finset ℕ) (lo : ℕ → ℕ) : Prop :=
  c₀ * q / Real.log q ≤ M.card ∧
  ∀ m ∈ M, c₀ * q / Real.log q ≤ m ∧ m < q ∧ Nat.Coprime m q ∧
    (lo m = q * m ∨ lo m + 1 = q * m) ∧
    Powersmooth (q - 1) (companion q (lo m) m) ∧ 8 ∣ ctr q (lo m) m

/-- The covering hypothesis (conclusion of `subsets_lemma`) at modulus `q`. -/
def SubsetsCover (q : ℕ) : Prop :=
  ∀ A : Finset ℕ, (∀ a ∈ A, a < q ∧ Nat.Coprime a q) →
    (q : ℝ) ^ ((3 : ℝ) / 4) ≤ A.card → ∀ b : ℕ, ∃ Cs ⊆ A, (∑ a ∈ Cs, a) ≡ b [MOD q]

/-- The stage-`B` pool: `2 s(B)` pairs from the pairs data at `B` whose centres avoid the chain
labels; it satisfies the hypotheses of `seed_family`, and its centres describe its blocks. -/
theorem seed_pool_exists (c₀ : ℝ) (hc : 0 < c₀) (B : ℕ) (hB : 9 ≤ B) (hBpp : IsPrimePow B)
    (M : Finset ℕ) (lo : ℕ → ℕ) (hdata : PairsData c₀ B M lo) (hsub : SubsetsCover B)
    (henough : ((9 * s B + 2 * s B + 2 * (2 * Nat.log 2 B + 1) : ℕ) : ℝ) ≤ c₀ * B / Real.log B)
    (hmass : (3 * (s B : ℝ)) * (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) < 1 / 20) :
    ∃ PBm ⊆ M, PBm.card = 2 * s B ∧ (∀ m ∈ PBm, ctr B (lo m) m ∉ chainLabels B) ∧
      (PBm.image (poolIv lo)).card = 2 * s B ∧
      (∀ I ∈ PBm.image (poolIv lo), 8 ≤ I.lo ∧ I.hi = I.lo + 1) ∧
      (∀ I ∈ PBm.image (poolIv lo), InG B I.mass) ∧
      (∀ I ∈ PBm.image (poolIv lo), ∀ J ∈ PBm.image (poolIv lo), I ≠ J → Iv.Sep I J) ∧
      (∀ I ∈ PBm.image (poolIv lo), ∀ lab ∈ chainLabels B, Iv.Sep I (Iv.triple lab)) ∧
      (∑ I ∈ PBm.image (poolIv lo), I.mass < 1 / 20) ∧
      (∀ I ∈ PBm.image (poolIv lo), ∃ a ∈ PBm.image (fun m => ctr B (lo m) m),
        8 ∣ a ∧ a ≤ I.lo + 1 ∧ I.hi ≤ a + 2) := by
  classical
  obtain ⟨hMcard, hMdata⟩ := hdata
  have hlogBpos : 0 < Real.log B := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hM' : ∀ m ∈ M, 1 ≤ m ∧ m < B ∧ Nat.Coprime m B ∧ (lo m = B * m ∨ lo m + 1 = B * m) ∧
      Powersmooth (B - 1) (companion B (lo m) m) ∧ 8 ∣ ctr B (lo m) m := by
    intro m hm
    obtain ⟨hmge, hmlt, hcop, hlo, hps, hdvd⟩ := hMdata m hm
    have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
    have hpos : (0 : ℝ) < c₀ * B / Real.log B := div_pos (mul_pos hc hBpos) hlogBpos
    have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hpos hmge
    have hm0 : m ≠ 0 := Nat.cast_ne_zero.mp hmpos.ne'
    exact ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmlt, hcop, hlo, hps, hdvd⟩
  obtain ⟨hInjM, hPropM, hCtrInjM, _⟩ :=
    stage_pool_props B hBpp hB M lo hM' hsub M (subset_refl M)
  set cand : Finset ℕ := M.filter (fun m => ctr B (lo m) m ∉ chainLabels B) with hcanddef
  have hcandsubM : cand ⊆ M := Finset.filter_subset _ _
  have hctr_le_sq : ∀ m ∈ M, ctr B (lo m) m ≤ B ^ 2 := by
    intro m hm
    obtain ⟨_, hmlt, _, hlo, _, _⟩ := hM' m hm
    obtain ⟨_, _, _, hctrle, _, _⟩ := hPropM m hm
    have hlom1 : lo m + 1 ≤ B * m + 1 := by rcases hlo with h | h <;> omega
    have step : B * (m + 1) ≤ B * B := Nat.mul_le_mul (le_refl B) (by omega)
    have expand : B * (m + 1) = B * m + B := by ring
    have hfin : B * m + 1 ≤ B * B := by omega
    calc ctr B (lo m) m ≤ lo m + 1 := hctrle
      _ ≤ B * m + 1 := hlom1
      _ ≤ B * B := hfin
      _ = B ^ 2 := (pow_two B).symm
  have hnegcard : (M.filter (fun m => ctr B (lo m) m ∈ chainLabels B)).card ≤
      2 * (2 * Nat.log 2 B + 1) := by
    have hmaps : Set.MapsTo (fun m => ctr B (lo m) m)
        ↑(M.filter (fun m => ctr B (lo m) m ∈ chainLabels B))
        ↑((chainLabels B).filter (fun lab => lab ≤ B ^ 2)) := by
      intro m hm
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hm ⊢
      exact ⟨hm.2, hctr_le_sq m hm.1⟩
    have hinj : Set.InjOn (fun m => ctr B (lo m) m)
        ↑(M.filter (fun m => ctr B (lo m) m ∈ chainLabels B)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      by_contra hne
      exact hCtrInjM x hx.1 y hy.1 hne hxy
    calc (M.filter (fun m => ctr B (lo m) m ∈ chainLabels B)).card
        ≤ ((chainLabels B).filter (fun lab => lab ≤ B ^ 2)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ ≤ 2 * (2 * Nat.log 2 B + 1) := chainLabels_filter_le B B
  have hsplit : cand.card + (M.filter (fun m => ctr B (lo m) m ∈ chainLabels B)).card
      = M.card := by
    have hbase := Finset.card_filter_add_card_filter_not (s := M)
      (p := fun m => ctr B (lo m) m ∉ chainLabels B)
    have hfiltereq : M.filter (fun m => ¬ (ctr B (lo m) m ∉ chainLabels B)) =
        M.filter (fun m => ctr B (lo m) m ∈ chainLabels B) := by
      apply Finset.filter_congr
      intro m _
      tauto
    rw [hfiltereq] at hbase
    rw [hcanddef]
    exact hbase
  have hMcard_ge : 9 * s B + 2 * s B + 2 * (2 * Nat.log 2 B + 1) ≤ M.card := by
    have h1 : ((9 * s B + 2 * s B + 2 * (2 * Nat.log 2 B + 1) : ℕ) : ℝ) ≤ (M.card : ℝ) :=
      henough.trans hMcard
    exact_mod_cast h1
  have hcand2sB : 2 * s B ≤ cand.card := by omega
  obtain ⟨PBm, hPBmsub, hPBmcard⟩ := Finset.exists_subset_card_eq hcand2sB
  have hPBmsubM : PBm ⊆ M := hPBmsub.trans hcandsubM
  have hInjPBm : Set.InjOn (poolIv lo) ↑PBm := hInjM.mono (Finset.coe_subset.mpr hPBmsubM)
  refine ⟨PBm, hPBmsubM, hPBmcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact (Finset.mem_filter.mp (hPBmsub hm)).2
  · rw [Finset.card_image_of_injOn hInjPBm]; exact hPBmcard
  · intro I hI
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨h8, hhi, _, _, _, _⟩ := hPropM m (hPBmsubM hm)
    exact ⟨h8, hhi⟩
  · intro I hI
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨_, _, hInG, _, _, _⟩ := hPropM m (hPBmsubM hm)
    exact hInG
  · intro I hI J hJ hIJ
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hJ
    have hmm' : m ≠ m' := by
      intro h; apply hIJ; rw [h]
    obtain ⟨_, _, _, hctrleI, hhileI, _⟩ := hPropM m (hPBmsubM hm)
    obtain ⟨_, _, _, hctrleJ, hhileJ, _⟩ := hPropM m' (hPBmsubM hm')
    obtain ⟨_, _, _, _, _, hdvdI⟩ := hM' m (hPBmsubM hm)
    obtain ⟨_, _, _, _, _, hdvdJ⟩ := hM' m' (hPBmsubM hm')
    exact sep_of_blocks hdvdI hdvdJ (hCtrInjM m (hPBmsubM hm) m' (hPBmsubM hm') hmm')
      ⟨hctrleI, hhileI⟩ ⟨hctrleJ, hhileJ⟩
  · intro I hI lab hlab
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨_, _, _, hctrle, hhile, _⟩ := hPropM m (hPBmsubM hm)
    obtain ⟨_, _, _, _, _, hdvd⟩ := hM' m (hPBmsubM hm)
    have hne : ctr B (lo m) m ≠ lab := by
      intro heq
      apply (Finset.mem_filter.mp (hPBmsub hm)).2
      rw [heq]; exact hlab
    have hlabblock : lab ≤ (Iv.triple lab).lo + 1 ∧ (Iv.triple lab).hi ≤ lab + 2 := by
      simp only [Iv.triple]
      omega
    exact sep_of_blocks hdvd (chainLabels_dvd B hlab).1 hne ⟨hctrle, hhile⟩ hlabblock
  · have hsumeq : (∑ I ∈ PBm.image (poolIv lo), I.mass) = ∑ m ∈ PBm, (poolIv lo m).mass :=
      Finset.sum_image hInjPBm
    have hreal : (∑ m ∈ PBm, ((poolIv lo m).mass : ℝ)) < 1 / 20 := by
      have hterm : ∀ m ∈ PBm, ((poolIv lo m).mass : ℝ) ≤ 4 * Real.log B / (c₀ * (B : ℝ) ^ 2) := by
        intro m hm
        obtain ⟨hmge, _, _, hlo, _, _⟩ := hMdata m (hPBmsubM hm)
        obtain ⟨hm1, _, _, _, _, _⟩ := hM' m (hPBmsubM hm)
        exact pool_pair_mass_le c₀ hc (by omega) hmge hm1 hlo
      have hsum_le : (∑ m ∈ PBm, ((poolIv lo m).mass : ℝ)) ≤
          PBm.card • (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) :=
        Finset.sum_le_card_nsmul PBm _ _ hterm
      have hnsmuleq : PBm.card • (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) =
          (PBm.card : ℝ) * (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) := by
        rw [nsmul_eq_mul]
      have hXnonneg : 0 ≤ 4 * Real.log B / (c₀ * (B : ℝ) ^ 2) := by positivity
      have hcardle : (PBm.card : ℝ) ≤ 3 * (s B : ℝ) := by
        rw [hPBmcard]
        have hsnonneg : (0 : ℝ) ≤ (s B : ℝ) := Nat.cast_nonneg _
        push_cast
        linarith
      calc (∑ m ∈ PBm, ((poolIv lo m).mass : ℝ))
          ≤ PBm.card • (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) := hsum_le
        _ = (PBm.card : ℝ) * (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) := hnsmuleq
        _ ≤ (3 * (s B : ℝ)) * (4 * Real.log B / (c₀ * (B : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_right hcardle hXnonneg
        _ < 1 / 20 := hmass
    rw [hsumeq]
    have hcast : ((∑ m ∈ PBm, (poolIv lo m).mass : ℚ) : ℝ) < ((1 / 20 : ℚ) : ℝ) := by
      push_cast; exact hreal
    exact_mod_cast hcast
  · intro I hI
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    refine ⟨ctr B (lo m) m, Finset.mem_image_of_mem _ hm, ?_, ?_, ?_⟩
    · exact (hM' m (hPBmsubM hm)).2.2.2.2.2
    · exact (hPropM m (hPBmsubM hm)).2.2.2.1
    · exact (hPropM m (hPBmsubM hm)).2.2.2.2.1

/-- `stage_pool_props`, repackaged from the `PairsData` hypothesis (`1 ≤ m` derived from the
lower bound `c₀ q / log q ≤ m`). -/
private theorem stage_pool_props' (c₀ : ℝ) (hc : 0 < c₀) (q : ℕ) (hq : IsPrimePow q)
    (hq9 : 9 ≤ q) (M : Finset ℕ) (lo : ℕ → ℕ) (hdata : PairsData c₀ q M lo)
    (hsub : SubsetsCover q) (T : Finset ℕ) (hT : T ⊆ M) :
    Set.InjOn (poolIv lo) T ∧
    (∀ m ∈ T, 8 ≤ (poolIv lo m).lo ∧ (poolIv lo m).hi = (poolIv lo m).lo + 1 ∧
      InG q (poolIv lo m).mass ∧
      ctr q (lo m) m ≤ (poolIv lo m).lo + 1 ∧ (poolIv lo m).hi ≤ ctr q (lo m) m + 2 ∧
      (lpp (ctr q (lo m) m - 1) = q ∨ lpp (ctr q (lo m) m) = q ∨
        lpp (ctr q (lo m) m + 1) = q)) ∧
    (∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → ctr q (lo m) m ≠ ctr q (lo m') m') ∧
    (∀ T' ⊆ T, s q ≤ T'.card → ∀ z : ℚ, InG q z →
      ∃ Cs ⊆ T'.image (poolIv lo), InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) := by
  obtain ⟨hMcard, hMdata⟩ := hdata
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hM' : ∀ m ∈ M, 1 ≤ m ∧ m < q ∧ Nat.Coprime m q ∧ (lo m = q * m ∨ lo m + 1 = q * m) ∧
      Powersmooth (q - 1) (companion q (lo m) m) ∧ 8 ∣ ctr q (lo m) m := by
    intro m hm
    obtain ⟨hmge, hmlt, hcop, hlo, hps, hdvd⟩ := hMdata m hm
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hpos : (0 : ℝ) < c₀ * q / Real.log q := div_pos (mul_pos hc hqpos) hlogpos
    have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hpos hmge
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hmpos.ne'), hmlt, hcop, hlo, hps, hdvd⟩
  exact stage_pool_props q hq hq9 M lo hM' hsub T hT

/-- The pools at all prime-power stages `B < q ≤ X`, chosen by Hall's theorem among the centres
avoiding the chain labels and the stage-`B` centres `PBc`; they satisfy the hypotheses of
`iterate_transfer` and the per-stage mass bound. -/
theorem stage_pools_exist (c₀ : ℝ) (hc : 0 < c₀) (B X : ℕ) (hB : 9 ≤ B)
    (M : ℕ → Finset ℕ) (lo : ℕ → ℕ → ℕ)
    (hdata : ∀ q, IsPrimePow q → B < q → q ≤ X → PairsData c₀ q (M q) (lo q))
    (hsub : ∀ q, IsPrimePow q → B < q → q ≤ X → SubsetsCover q)
    (henough : ∀ q, B < q →
      ((9 * s q + 2 * s B + 2 * (2 * Nat.log 2 q + 1) : ℕ) : ℝ) ≤ c₀ * q / Real.log q)
    (PBc : Finset ℕ) (hPBc : PBc.card ≤ 2 * s B)
    (supp₀ : Finset Iv)
    (hsupp₀ : ∀ I ∈ supp₀, I.hi ≤ 6 ∨
      ∃ a, 8 ∣ a ∧ (a ∈ chainLabels B ∨ a ∈ PBc) ∧ a ≤ I.lo + 1 ∧ I.hi ≤ a + 2) :
    ∃ pool : ℕ → Finset Iv,
      (∀ q, IsPrimePow q → B < q → q ≤ X → (pool q).card = 3 * s q) ∧
      (∀ q, ∀ I ∈ pool q, 2 ≤ I.lo ∧ I.hi = I.lo + 1) ∧
      (∀ q q', ∀ I ∈ pool q, ∀ J ∈ pool q', I ≠ J → Iv.Sep I J) ∧
      (∀ q q', q ≠ q' → Disjoint (pool q) (pool q')) ∧
      (∀ q, ∀ I ∈ supp₀, ∀ J ∈ pool q, Iv.Sep I J) ∧
      (∀ q, ∀ J ∈ pool q, InG q J.mass) ∧
      (∀ q, IsPrimePow q → B < q → q ≤ X → ∀ T ⊆ pool q, T.card = s q →
        ∀ z : ℚ, InG q z → ∃ Cs ⊆ T, InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) ∧
      (∀ q, IsPrimePow q → B < q → q ≤ X →
        ((∑ J ∈ pool q, J.mass : ℚ) : ℝ) ≤
          (3 * (s q : ℝ)) * (4 * Real.log q / (c₀ * (q : ℝ) ^ 2))) := by
  classical
  set cand : ℕ → Finset ℕ := fun q =>
    (M q).filter (fun m => ctr q (lo q m) m ∉ chainLabels B ∧ ctr q (lo q m) m ∉ PBc)
    with hcanddef
  set ctrs : ℕ → Finset ℕ := fun q => (cand q).image (fun m => ctr q (lo q m) m) with hctrsdef
  have hcandsubM : ∀ q, cand q ⊆ M q := by
    intro q
    simp only [hcanddef]
    exact Finset.filter_subset _ _
  have hStage : ∀ q, IsPrimePow q → B < q → q ≤ X →
      Set.InjOn (poolIv (lo q)) ↑(M q) ∧
      (∀ m ∈ M q, 8 ≤ (poolIv (lo q) m).lo ∧ (poolIv (lo q) m).hi = (poolIv (lo q) m).lo + 1 ∧
        InG q (poolIv (lo q) m).mass ∧ ctr q (lo q m) m ≤ (poolIv (lo q) m).lo + 1 ∧
        (poolIv (lo q) m).hi ≤ ctr q (lo q m) m + 2 ∧
        (lpp (ctr q (lo q m) m - 1) = q ∨ lpp (ctr q (lo q m) m) = q ∨
          lpp (ctr q (lo q m) m + 1) = q)) ∧
      (∀ m ∈ M q, ∀ m' ∈ M q, m ≠ m' → ctr q (lo q m) m ≠ ctr q (lo q m') m') ∧
      (∀ T' ⊆ M q, s q ≤ T'.card → ∀ z : ℚ, InG q z →
        ∃ Cs ⊆ T'.image (poolIv (lo q)), InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) :=
    fun q hpp hBq hqX => stage_pool_props' c₀ hc q hpp (by omega) (M q) (lo q)
      (hdata q hpp hBq hqX) (hsub q hpp hBq hqX) (M q) (subset_refl _)
  have hdeg : ∀ q, IsPrimePow q → B < q → q ≤ X → 9 * s q ≤ (ctrs q).card := by
    intro q hpp hBq hqX
    obtain ⟨_, hPropMq, hCtrInjMq, _⟩ := hStage q hpp hBq hqX
    obtain ⟨hMcard, hMdata⟩ := hdata q hpp hBq hqX
    have hctr_le_sq : ∀ m ∈ M q, ctr q (lo q m) m ≤ q ^ 2 := by
      intro m hm
      obtain ⟨_, hmlt, _, hlo, _, _⟩ := hMdata m hm
      obtain ⟨_, _, _, hctrle, _, _⟩ := hPropMq m hm
      have hlom1 : lo q m + 1 ≤ q * m + 1 := by rcases hlo with h | h <;> omega
      have step : q * (m + 1) ≤ q * q := Nat.mul_le_mul (le_refl q) (by omega)
      have expand : q * (m + 1) = q * m + q := by ring
      have hfin : q * m + 1 ≤ q * q := by omega
      calc ctr q (lo q m) m ≤ lo q m + 1 := hctrle
        _ ≤ q * m + 1 := hlom1
        _ ≤ q * q := hfin
        _ = q ^ 2 := (pow_two q).symm
    have hnegcard : ((M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨
        ctr q (lo q m) m ∈ PBc)).card ≤ 2 * (2 * Nat.log 2 q + 1) + PBc.card := by
      have hmaps : Set.MapsTo (fun m => ctr q (lo q m) m)
          ↑((M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨ ctr q (lo q m) m ∈ PBc))
          ↑(((chainLabels B).filter (fun lab => lab ≤ q ^ 2)) ∪ PBc) := by
        intro m hm
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hm
        simp only [Finset.coe_union, Set.mem_union, Finset.coe_filter, Set.mem_ofPred_eq]
        rcases hm.2 with h | h
        · exact Or.inl ⟨h, hctr_le_sq m hm.1⟩
        · exact Or.inr h
      have hinj : Set.InjOn (fun m => ctr q (lo q m) m)
          ↑((M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨
            ctr q (lo q m) m ∈ PBc)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
        by_contra hne
        exact hCtrInjMq x hx.1 y hy.1 hne hxy
      calc ((M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨
            ctr q (lo q m) m ∈ PBc)).card
          ≤ (((chainLabels B).filter (fun lab => lab ≤ q ^ 2)) ∪ PBc).card :=
            Finset.card_le_card_of_injOn _ hmaps hinj
        _ ≤ ((chainLabels B).filter (fun lab => lab ≤ q ^ 2)).card + PBc.card :=
            Finset.card_union_le _ _
        _ ≤ 2 * (2 * Nat.log 2 q + 1) + PBc.card := by
            have := chainLabels_filter_le B q
            omega
    have hsplit : (cand q).card +
        ((M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨
          ctr q (lo q m) m ∈ PBc)).card = (M q).card := by
      have hbase := Finset.card_filter_add_card_filter_not (s := M q)
        (p := fun m => ctr q (lo q m) m ∉ chainLabels B ∧ ctr q (lo q m) m ∉ PBc)
      have hfiltereq : (M q).filter (fun m => ¬ (ctr q (lo q m) m ∉ chainLabels B ∧
          ctr q (lo q m) m ∉ PBc)) =
          (M q).filter (fun m => ctr q (lo q m) m ∈ chainLabels B ∨ ctr q (lo q m) m ∈ PBc) := by
        apply Finset.filter_congr
        intro m _
        tauto
      rw [hfiltereq] at hbase
      simp only [hcanddef]
      exact hbase
    have hMqcard_ge : 9 * s q + 2 * s B + 2 * (2 * Nat.log 2 q + 1) ≤ (M q).card := by
      have h1 : ((9 * s q + 2 * s B + 2 * (2 * Nat.log 2 q + 1) : ℕ) : ℝ) ≤ ((M q).card : ℝ) :=
        (henough q hBq).trans hMcard
      exact_mod_cast h1
    have hcandcard : 9 * s q ≤ (cand q).card := by omega
    have hinjcandq : Set.InjOn (fun m => ctr q (lo q m) m) ↑(cand q) := by
      intro x hx y hy hxy
      by_contra hne
      exact hCtrInjMq x (hcandsubM q (Finset.mem_coe.mp hx))
        y (hcandsubM q (Finset.mem_coe.mp hy)) hne hxy
    calc 9 * s q ≤ (cand q).card := hcandcard
      _ = (ctrs q).card := by simp only [hctrsdef]; exact (Finset.card_image_of_injOn hinjcandq).symm
  have hmult : ∀ a q, IsPrimePow q → B < q → q ≤ X → a ∈ ctrs q →
      lpp (a - 1) = q ∨ lpp a = q ∨ lpp (a + 1) = q := by
    intro a q hpp hBq hqX ha
    obtain ⟨_, hPropMq, _, _⟩ := hStage q hpp hBq hqX
    simp only [hctrsdef] at ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    exact (hPropMq m (hcandsubM q hm)).2.2.2.2.2
  obtain ⟨chosen, hchosen_sub, hchosen_disj⟩ := choose_pools B X ctrs hdeg hmult
  have hinjcand : ∀ q, IsPrimePow q → B < q → q ≤ X →
      Set.InjOn (fun m => ctr q (lo q m) m) ↑(cand q) := by
    intro q hpp hBq hqX
    obtain ⟨_, _, hCtrInjMq, _⟩ := hStage q hpp hBq hqX
    intro x hx y hy hxy
    by_contra hne
    exact hCtrInjMq x (hcandsubM q (Finset.mem_coe.mp hx))
      y (hcandsubM q (Finset.mem_coe.mp hy)) hne hxy
  have hinjpool : ∀ q, IsPrimePow q → B < q → q ≤ X →
      Set.InjOn (poolIv (lo q)) ↑(cand q) := by
    intro q hpp hBq hqX
    obtain ⟨hInjMq, _, _, _⟩ := hStage q hpp hBq hqX
    exact hInjMq.mono (Finset.coe_subset.mpr (hcandsubM q))
  have hfiltcard : ∀ q, IsPrimePow q → B < q → q ≤ X →
      ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)).card = 3 * s q := by
    intro q hpp hBq hqX
    obtain ⟨hsub, hcardchosen⟩ := hchosen_sub q hpp hBq hqX
    have hfiltImg : ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)).image
        (fun m => ctr q (lo q m) m) = chosen q := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨m, ⟨hmcand, hmchosen⟩, rfl⟩
        exact hmchosen
      · intro ha
        have haCtrs : a ∈ ctrs q := hsub ha
        simp only [hctrsdef] at haCtrs
        obtain ⟨m, hmcand, hmeq⟩ := Finset.mem_image.mp haCtrs
        exact ⟨m, ⟨hmcand, hmeq ▸ ha⟩, hmeq⟩
    have hinjfilt : Set.InjOn (fun m => ctr q (lo q m) m)
        ↑((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)) :=
      (hinjcand q hpp hBq hqX).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    rw [← Finset.card_image_of_injOn hinjfilt, hfiltImg]
    exact hcardchosen
  set pool : ℕ → Finset Iv := fun q =>
    if IsPrimePow q ∧ B < q ∧ q ≤ X then
      ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)).image (poolIv (lo q))
    else ∅ with hpooldef
  have hpool_eq_filterimage : ∀ q, IsPrimePow q → B < q → q ≤ X →
      pool q = ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)).image (poolIv (lo q)) := by
    intro q hpp hBq hqX
    simp only [hpooldef]
    rw [ite_eq_left ⟨hpp, hBq, hqX⟩]
  have hpool_empty : ∀ q, ¬ (IsPrimePow q ∧ B < q ∧ q ≤ X) → pool q = ∅ := by
    intro q hq
    simp only [hpooldef]
    rw [ite_eq_right hq]
  refine ⟨pool, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- card
    intro q hpp hBq hqX
    rw [hpool_eq_filterimage q hpp hBq hqX,
      Finset.card_image_of_injOn ((hinjpool q hpp hBq hqX).mono
        (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    exact hfiltcard q hpp hBq hqX
  · -- pair shape
    intro q I hI
    by_cases hq : IsPrimePow q ∧ B < q ∧ q ≤ X
    · rw [hpool_eq_filterimage q hq.1 hq.2.1 hq.2.2] at hI
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
      have hmcand := (Finset.mem_filter.mp hm).1
      obtain ⟨_, hPropMq, _, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
      obtain ⟨h8, hhi, _, _, _, _⟩ := hPropMq m (hcandsubM q hmcand)
      exact ⟨by omega, hhi⟩
    · rw [hpool_empty q hq] at hI
      exact absurd hI (Finset.notMem_empty I)
  · -- separation between pool pairs
    intro q q' I hI J hJ hIJ
    by_cases hq : IsPrimePow q ∧ B < q ∧ q ≤ X
    · by_cases hq' : IsPrimePow q' ∧ B < q' ∧ q' ≤ X
      · rw [hpool_eq_filterimage q hq.1 hq.2.1 hq.2.2] at hI
        rw [hpool_eq_filterimage q' hq'.1 hq'.2.1 hq'.2.2] at hJ
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hJ
        have hmcand := (Finset.mem_filter.mp hm).1
        have hmchosen := (Finset.mem_filter.mp hm).2
        have hm'cand := (Finset.mem_filter.mp hm').1
        have hm'chosen := (Finset.mem_filter.mp hm').2
        obtain ⟨_, hPropMq, _, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
        obtain ⟨_, hPropMq', _, _⟩ := hStage q' hq'.1 hq'.2.1 hq'.2.2
        obtain ⟨_, _, _, hctrleI, hhileI, _⟩ := hPropMq m (hcandsubM q hmcand)
        obtain ⟨_, _, _, hctrleJ, hhileJ, _⟩ := hPropMq' m' (hcandsubM q' hm'cand)
        by_cases hqq' : q = q'
        · subst hqq'
          have hmm' : m ≠ m' := by intro h; apply hIJ; rw [h]
          obtain ⟨_, _, _, _, _, hdvdI⟩ := (hdata q hq.1 hq.2.1 hq.2.2).2 m (hcandsubM q hmcand)
          obtain ⟨_, _, _, _, _, hdvdJ⟩ :=
            (hdata q hq.1 hq.2.1 hq.2.2).2 m' (hcandsubM q hm'cand)
          obtain ⟨_, _, hCtrInjMq, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
          exact sep_of_blocks hdvdI hdvdJ
            (hCtrInjMq m (hcandsubM q hmcand) m' (hcandsubM q hm'cand) hmm')
            ⟨hctrleI, hhileI⟩ ⟨hctrleJ, hhileJ⟩
        · obtain ⟨_, _, _, _, _, hdvdI⟩ := (hdata q hq.1 hq.2.1 hq.2.2).2 m (hcandsubM q hmcand)
          obtain ⟨_, _, _, _, _, hdvdJ⟩ :=
            (hdata q' hq'.1 hq'.2.1 hq'.2.2).2 m' (hcandsubM q' hm'cand)
          have hne : ctr q (lo q m) m ≠ ctr q' (lo q' m') m' := by
            intro heq
            exact (Finset.disjoint_left.mp (hchosen_disj q q' hqq') hmchosen) (heq ▸ hm'chosen)
          exact sep_of_blocks hdvdI hdvdJ hne ⟨hctrleI, hhileI⟩ ⟨hctrleJ, hhileJ⟩
      · rw [hpool_empty q' hq'] at hJ
        exact absurd hJ (Finset.notMem_empty J)
    · rw [hpool_empty q hq] at hI
      exact absurd hI (Finset.notMem_empty I)
  · -- disjointness across stages
    intro q q' hqq'
    by_cases hq : IsPrimePow q ∧ B < q ∧ q ≤ X
    · by_cases hq' : IsPrimePow q' ∧ B < q' ∧ q' ≤ X
      · rw [hpool_eq_filterimage q hq.1 hq.2.1 hq.2.2, hpool_eq_filterimage q' hq'.1 hq'.2.1 hq'.2.2]
        rw [Finset.disjoint_left]
        intro I hI hI'
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
        obtain ⟨m', hm', hmeq⟩ := Finset.mem_image.mp hI'
        have hmcand := (Finset.mem_filter.mp hm).1
        have hmchosen := (Finset.mem_filter.mp hm).2
        have hm'cand := (Finset.mem_filter.mp hm').1
        have hm'chosen := (Finset.mem_filter.mp hm').2
        obtain ⟨_, hPropMq, _, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
        obtain ⟨_, hPropMq', _, _⟩ := hStage q' hq'.1 hq'.2.1 hq'.2.2
        obtain ⟨_, _, _, hctrleI, hhileI, _⟩ := hPropMq m (hcandsubM q hmcand)
        have hI'block : ctr q' (lo q' m') m' ≤ (poolIv (lo q) m).lo + 1 ∧
            (poolIv (lo q) m).hi ≤ ctr q' (lo q' m') m' + 2 := by
          have h := hPropMq' m' (hcandsubM q' hm'cand)
          rw [hmeq] at h
          exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
        obtain ⟨_, _, _, _, _, hdvdI⟩ := (hdata q hq.1 hq.2.1 hq.2.2).2 m (hcandsubM q hmcand)
        obtain ⟨_, _, _, _, _, hdvdI'⟩ :=
          (hdata q' hq'.1 hq'.2.1 hq'.2.2).2 m' (hcandsubM q' hm'cand)
        have hne : ctr q (lo q m) m ≠ ctr q' (lo q' m') m' := by
          intro heq
          exact (Finset.disjoint_left.mp (hchosen_disj q q' hqq') hmchosen) (heq ▸ hm'chosen)
        have hsep : Iv.Sep (poolIv (lo q) m) (poolIv (lo q) m) :=
          sep_of_blocks hdvdI hdvdI' hne ⟨hctrleI, hhileI⟩ hI'block
        have hlohi : (poolIv (lo q) m).lo ≤ (poolIv (lo q) m).hi := by
          simp only [poolIv, Iv.pair]; omega
        exact absurd rfl (Sep.ne hsep hlohi hlohi)
      · rw [hpool_empty q' hq']
        simp
    · rw [hpool_empty q hq]
      simp
  · -- separation from supp₀
    intro q I hI J hJ
    by_cases hq : IsPrimePow q ∧ B < q ∧ q ≤ X
    · rw [hpool_eq_filterimage q hq.1 hq.2.1 hq.2.2] at hJ
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hJ
      have hmcand := (Finset.mem_filter.mp hm).1
      obtain ⟨_, hPropMq, _, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
      obtain ⟨h8, _, _, hctrle, hhile, _⟩ := hPropMq m (hcandsubM q hmcand)
      obtain ⟨_, _, _, _, _, hdvd⟩ := (hdata q hq.1 hq.2.1 hq.2.2).2 m (hcandsubM q hmcand)
      rcases hsupp₀ I hI with hsmall | ⟨a, hadvd, hamem, hale, hihi⟩
      · exact sep_small hsmall h8
      · have hmcandfilt := Finset.mem_filter.mp hmcand
        have hane : a ≠ ctr q (lo q m) m := by
          rcases hamem with hachain | haPBc
          · intro heq; exact hmcandfilt.2.1 (heq ▸ hachain)
          · intro heq; exact hmcandfilt.2.2 (heq ▸ haPBc)
        exact sep_of_blocks hadvd hdvd hane ⟨hale, hihi⟩ ⟨hctrle, hhile⟩
    · rw [hpool_empty q hq] at hJ
      exact absurd hJ (Finset.notMem_empty J)
  · -- InG
    intro q J hJ
    by_cases hq : IsPrimePow q ∧ B < q ∧ q ≤ X
    · rw [hpool_eq_filterimage q hq.1 hq.2.1 hq.2.2] at hJ
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨_, hPropMq, _, _⟩ := hStage q hq.1 hq.2.1 hq.2.2
      exact (hPropMq m (hcandsubM q (Finset.mem_filter.mp hm).1)).2.2.1
    · rw [hpool_empty q hq] at hJ
      exact absurd hJ (Finset.notMem_empty J)
  · -- covering
    intro q hpp hBq hqX T hTsub hTcard z hz
    rw [hpool_eq_filterimage q hpp hBq hqX] at hTsub
    obtain ⟨T', hT'sub, hT'img⟩ := Finset.subset_image_iff.mp hTsub
    have hT'cand : T' ⊆ cand q := hT'sub.trans (Finset.filter_subset _ _)
    have hT'M : T' ⊆ M q := hT'cand.trans (hcandsubM q)
    have hT'cardeq : T'.card = T.card := by
      rw [← hT'img]
      exact (Finset.card_image_of_injOn ((hinjpool q hpp hBq hqX).mono
        (Finset.coe_subset.mpr hT'cand))).symm
    have hT'cardge : s q ≤ T'.card := by rw [hT'cardeq, hTcard]
    obtain ⟨_, _, _, hcovering⟩ := hStage q hpp hBq hqX
    obtain ⟨Cs, hCssub, hInGCs⟩ := hcovering T' hT'M hT'cardge z hz
    refine ⟨Cs, ?_, hInGCs⟩
    rw [← hT'img]
    exact hCssub
  · -- mass bound
    intro q hpp hBq hqX
    rw [hpool_eq_filterimage q hpp hBq hqX]
    have hinjfilt : Set.InjOn (poolIv (lo q)) ↑((cand q).filter
        (fun m => ctr q (lo q m) m ∈ chosen q)) :=
      (hinjpool q hpp hBq hqX).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    have hsumeq : (∑ I ∈ ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)).image
        (poolIv (lo q)), I.mass) =
        ∑ m ∈ (cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q), (poolIv (lo q) m).mass :=
      Finset.sum_image hinjfilt
    have hreal : (∑ m ∈ (cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q),
        ((poolIv (lo q) m).mass : ℝ)) ≤
        (3 * (s q : ℝ)) * (4 * Real.log q / (c₀ * (q : ℝ) ^ 2)) := by
      have hterm : ∀ m ∈ (cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q),
          ((poolIv (lo q) m).mass : ℝ) ≤ 4 * Real.log q / (c₀ * (q : ℝ) ^ 2) := by
        intro m hm
        have hmM : m ∈ M q := hcandsubM q (Finset.mem_filter.mp hm).1
        obtain ⟨hmge, _, _, hlo, _, _⟩ := (hdata q hpp hBq hqX).2 m hmM
        have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
        have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
        have hpos : (0 : ℝ) < c₀ * q / Real.log q := div_pos (mul_pos hc hqpos) hlogpos
        have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hpos hmge
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hmpos.ne')
        exact pool_pair_mass_le c₀ hc (by omega) hmge hm1 hlo
      have hsum_le := Finset.sum_le_card_nsmul
        ((cand q).filter (fun m => ctr q (lo q m) m ∈ chosen q)) _ _ hterm
      rw [hfiltcard q hpp hBq hqX, nsmul_eq_mul] at hsum_le
      push_cast at hsum_le
      exact hsum_le
    rw [hsumeq]
    push_cast
    exact hreal

end Erdos289.CLT
