import Erdos289CLT.Transfer

/-!
# A finite starting family (paper §3)

With `B` a power of two, write `D_B = 2^e M` (`M` odd), take `N ≥ e` with
`2^{N-3} ≥ M`, `K = M 2^N`.  The two chains `[2^i+1, 2^i+2]`, `[M 2^i+1, M 2^i+2]`
(`3 ≤ i ≤ N`) may each be extended to the left by one integer, adding `1/2^i`
resp. `1/(M 2^i)`; together the extensions represent every multiple of `1/K`
in `[0, 1/4)`.  Five small intervals `J_h` of weight `11/30 + h/60`
(`h ∈ {0,15,28,43,55}`) supply the coarse adjustment.  Adjoining any subset of a
stage-`B` pool `PB` of `2 s(B)` pairs realizes `(β + G_B) × [t+1, t+1+2s(B)]`,
`t = 2(N-2)`, with all weights below `39/20`.
-/

namespace Erdos289.CLT

open Finset

/-- The exponent of `2` in `D_B`. -/
def e (B : ℕ) : ℕ := (D B).factorization 2

/-- The odd part `M` of `D_B`. -/
def Modd (B : ℕ) : ℕ := D B / 2 ^ e B

/-- The chain length parameter `N`. -/
def Nn (B : ℕ) : ℕ := max (e B) (Nat.log 2 (Modd B) + 4)

/-- `K = M 2^N`. -/
def K (B : ℕ) : ℕ := Modd B * 2 ^ Nn B

/-- `t = 2(N - 2)`, the number of chain pairs. -/
def tB (B : ℕ) : ℕ := 2 * (Nn B - 2)

/-- The five coarse-adjustment indices. -/
def hSet : Finset ℕ := {0, 15, 28, 43, 55}

/-- The small interval `J_h`. -/
def smallIv (h : ℕ) : Iv :=
  if h = 15 then ⟨4, 6⟩ else if h = 28 then ⟨2, 3⟩ else if h = 43 then ⟨2, 4⟩
  else if h = 55 then ⟨2, 5⟩ else ⟨5, 6⟩

/-- A chain interval at label `lab`: `[lab+1, lab+2]`, or `[lab, lab+2]` when extended. -/
def chainIv (lab : ℕ) (ext : Bool) : Iv := if ext then Iv.triple lab else Iv.pair (lab + 1)

/-- The labels `2^i` and `M 2^i`, `3 ≤ i ≤ N`, of the two chains. -/
def chainLabels (B : ℕ) : Finset ℕ :=
  (Icc 3 (Nn B)).image (fun i => 2 ^ i) ∪ (Icc 3 (Nn B)).image (fun i => Modd B * 2 ^ i)

/-- The seed configuration with coarse index `h`, extension sets `U`, `V`, and pool part. -/
def seedF (B h : ℕ) (U V : Finset ℕ) (pool : Finset Iv) : Finset Iv :=
  {smallIv h} ∪ (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))) ∪
    (Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V))) ∪ pool

/-- All intervals that can occur in a seed configuration apart from the pool. -/
def seedSupp (B : ℕ) : Finset Iv :=
  hSet.image smallIv ∪ (chainLabels B).image (fun lab => Iv.pair (lab + 1)) ∪
    (chainLabels B).image Iv.triple

/-- The fixed finite set of admissible intervals longer than two. -/
def seedLong (B : ℕ) : Finset Iv := hSet.image smallIv ∪ (chainLabels B).image Iv.triple

theorem smallIv_mass (h : ℕ) (hh : h ∈ hSet) :
    (smallIv h).mass = 11 / 30 + (h : ℚ) / 60 := by
  simp only [hSet, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [smallIv, Iv.mass, Erdos289.mass]
    norm_num [Finset.sum_Icc_succ_top]


theorem chainLabels_dvd (B : ℕ) {lab : ℕ} (h : lab ∈ chainLabels B) : 8 ∣ lab ∧ 8 ≤ lab := by
  simp only [chainLabels, Finset.mem_union, Finset.mem_image] at h
  rcases h with h | h
  · obtain ⟨i, hi, rfl⟩ := h
    simp only [Finset.mem_Icc] at hi
    have hi3 : 3 ≤ i := hi.1
    have hp : 8 ∣ 2 ^ i := by
      obtain ⟨k, hk⟩ : ∃ k, i = 3 + k := ⟨i - 3, by omega⟩
      exact ⟨2 ^ k, by rw [hk, pow_add]; norm_num⟩
    have h8 : 8 ≤ 2 ^ i := by
      have h := pow_le_pow_right' (a := (2:ℕ)) (by norm_num) hi3
      norm_num at h
      omega
    exact ⟨hp, h8⟩
  · obtain ⟨i, hi, rfl⟩ := h
    simp only [Finset.mem_Icc] at hi
    have hi3 : 3 ≤ i := hi.1
    have hp : 8 ∣ 2 ^ i := by
      obtain ⟨k, hk⟩ : ∃ k, i = 3 + k := ⟨i - 3, by omega⟩
      exact ⟨2 ^ k, by rw [hk, pow_add]; norm_num⟩
    have h8 : 8 ≤ 2 ^ i := by
      have h := pow_le_pow_right' (a := (2:ℕ)) (by norm_num) hi3
      norm_num at h
      omega
    have hMpos : 0 < Modd B := by
      unfold Modd
      apply Nat.div_pos _ (by positivity)
      have hz : D B ≠ 0 := ne_of_gt (D_pos B)
      have hp2 : Nat.Prime 2 := by norm_num
      have hdvd : 2 ^ e B ∣ D B := by
        rw [hp2.pow_dvd_iff_le_factorization hz]
        exact le_refl _
      exact Nat.le_of_dvd (D_pos B) hdvd
    exact ⟨dvd_mul_of_dvd_right hp _, le_trans h8 (Nat.le_mul_of_pos_left (2 ^ i) hMpos)⟩


/-- If `2^i` is at most `q^2` and `i ≥ 3`, then `i` is at most twice the base-2
logarithm of `q`. -/
theorem two_pow_le_sq_log_bound {i q : ℕ} (_hi : 3 ≤ i) (h : 2 ^ i ≤ q ^ 2) :
    i ≤ 2 * Nat.log 2 q + 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp at h
  · by_contra hcon
    set L := Nat.log 2 q with hL
    have hq : q < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hpow2 : (q ^ 2 : ℕ) < (2 ^ (L + 1)) ^ 2 :=
      Nat.pow_lt_pow_left (n := 2) hq (by norm_num)
    have hbase : (2 ^ (L + 1) : ℕ) ^ 2 = 2 ^ ((L + 1) * 2) := by ring_nf
    have hpow : (q ^ 2 : ℕ) < 2 ^ ((L + 1) * 2) := by rw [← hbase]; exact hpow2
    have hge : (L + 1) * 2 ≤ i := by omega
    have hmono : (2:ℕ) ^ ((L + 1) * 2) ≤ 2 ^ i :=
      pow_le_pow_right' (by norm_num) hge
    exact absurd h (Nat.not_le.2 (lt_of_lt_of_le hpow hmono))


/-- The filtered image of a finite set under an injective-like map has cardinality bounded
by the corresponding filtered index set. -/
theorem image_filter_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (I : Finset α) (p : β → Prop) [DecidablePred p] :
    ((I.image f).filter p).card ≤ (I.filter (fun i => p (f i))).card := by
  have hEq : (I.image f).filter p = (I.filter (fun i => p (f i))).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨⟨a, ha, rfl⟩, hx⟩ := h
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
    · intro h
      obtain ⟨a, ⟨ha, hx⟩, rfl⟩ := h
      exact ⟨⟨a, ha, rfl⟩, hx⟩
  rw [hEq]
  exact Finset.card_image_le



/-- Few chain labels are at most `q²`. -/
theorem chainLabels_filter_le (B q : ℕ) :
    ((chainLabels B).filter (fun lab => lab ≤ q ^ 2)).card ≤ 2 * (2 * Nat.log 2 q + 1) := by
  set N := Nn B with hN
  set M := Modd B with hM
  have hMpos : 0 < M := by
    rw [hM]
    unfold Modd
    apply Nat.div_pos _ (by positivity)
    have hz : D B ≠ 0 := ne_of_gt (D_pos B)
    have hp2 : Nat.Prime 2 := by norm_num
    have hdvd : 2 ^ e B ∣ D B := by
      rw [hp2.pow_dvd_iff_le_factorization hz]
      exact le_refl _
    exact Nat.le_of_dvd (D_pos B) hdvd
  have hEq : (chainLabels B).filter (fun lab => lab ≤ q ^ 2) =
      ((Icc 3 N).image (fun i => 2 ^ i)).filter (fun lab => lab ≤ q ^ 2) ∪
        ((Icc 3 N).image (fun i => M * 2 ^ i)).filter (fun lab => lab ≤ q ^ 2) := by
    simp only [chainLabels, Finset.filter_union]
    rw [hN, hM]
  rw [hEq]
  refine le_trans (Finset.card_union_le _ _) ?_
  have hc1 : (((Icc 3 N).image (fun i => 2 ^ i)).filter (fun lab => lab ≤ q ^ 2)).card ≤
      2 * Nat.log 2 q + 1 := by
    refine le_trans (image_filter_card_le (fun i => 2 ^ i) (Icc 3 N) _) ?_
    have hsub : (Icc 3 N).filter (fun i => 2 ^ i ≤ q ^ 2) ⊆
        Icc 3 (2 * Nat.log 2 q + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
      obtain ⟨⟨h3, hN⟩, hlab⟩ := hi
      exact ⟨h3, two_pow_le_sq_log_bound h3 hlab⟩
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  have hc2 : (((Icc 3 N).image (fun i => M * 2 ^ i)).filter (fun lab => lab ≤ q ^ 2)).card ≤
      2 * Nat.log 2 q + 1 := by
    refine le_trans (image_filter_card_le (fun i => M * 2 ^ i) (Icc 3 N) _) ?_
    have hsub : (Icc 3 N).filter (fun i => M * 2 ^ i ≤ q ^ 2) ⊆
        Icc 3 (2 * Nat.log 2 q + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
      obtain ⟨⟨h3, hN⟩, hlab⟩ := hi
      refine ⟨h3, two_pow_le_sq_log_bound h3 ?_⟩
      exact le_trans (Nat.le_mul_of_pos_left _ hMpos) hlab
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  omega



/-- `2^e B` divides `D B`. -/
theorem pow_e_dvd_D (B : ℕ) : 2 ^ e B ∣ D B := by
  have hz : D B ≠ 0 := ne_of_gt (D_pos B)
  have hp2 : Nat.Prime 2 := by norm_num
  rw [hp2.pow_dvd_iff_le_factorization hz]
  exact le_refl _

/-- `D B = 2^e B * Modd B`. -/
theorem D_eq_e_mul_Modd (B : ℕ) : D B = 2 ^ e B * Modd B := by
  rw [Modd, Nat.mul_div_cancel' (pow_e_dvd_D B)]

/-- `Modd B` is positive. -/
theorem Modd_pos (B : ℕ) : 0 < Modd B := by
  have hD : D B = 2 ^ e B * Modd B := D_eq_e_mul_Modd B
  have hDpos := D_pos B
  rcases Nat.eq_zero_or_pos (Modd B) with h0 | h0
  · rw [h0, mul_zero] at hD
    omega
  · exact h0

/-- For `B ≥ 8`, the exponent of `2` in `D B` is at least `3`. -/
theorem e_ge_three {B : ℕ} (hB : 8 ≤ B) : 3 ≤ e B := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hlog := Nat.factorization_lcmUpto B hp2
  unfold e
  rw [hlog]
  have h8 : (2 : ℕ) ^ 3 ≤ B := by
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  exact (Nat.le_log_iff_pow_le hp2.one_lt (by omega : B ≠ 0)).mpr h8

/-- `3` divides `Modd B` for `B ≥ 8`, whence `Modd B > 1`. -/
theorem one_lt_Modd {B : ℕ} (hB : 8 ≤ B) : 1 < Modd B := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hD3 : 3 ∣ D B := by
    have hz : D B ≠ 0 := ne_of_gt (D_pos B)
    rw [show (3 : ℕ) = 3 ^ 1 from rfl, hp3.pow_dvd_iff_le_factorization hz,
      Nat.factorization_lcmUpto B hp3]
    exact (Nat.log_pos (by norm_num) (by omega : (3 : ℕ) ≤ B))
  have he := e_ge_three hB
  have hcop : Nat.Coprime 3 (2 ^ e B) := (by norm_num : Nat.Coprime 3 2).pow_right _
  have hM3 : 3 ∣ Modd B := by
    have hD3' : 3 ∣ 2 ^ e B * Modd B := by rw [← D_eq_e_mul_Modd]; exact hD3
    exact hcop.dvd_of_dvd_mul_left hD3'
  exact le_trans (by norm_num) (Nat.le_of_dvd (Modd_pos B) hM3)

/-- `Modd B` is odd. -/
theorem Modd_odd (B : ℕ) : ¬ 2 ∣ Modd B := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hMpos := Modd_pos B
  rintro ⟨k, hk⟩
  have hD : 2 ^ (e B + 1) ∣ D B := by
    rw [D_eq_e_mul_Modd, hk, pow_succ]
    exact mul_dvd_mul_left _ (Dvd.intro k rfl)
  rw [hp2.pow_dvd_iff_le_factorization (D_pos B).ne'] at hD
  unfold e at hD
  omega

/-- The chain length `N` is at least the exponent of `2`. -/
theorem e_le_N (B : ℕ) : e B ≤ Nn B := Nat.le_max_left _ _

/-- The chain length `N` exceeds the base-2 logarithm of `Modd B`. -/
theorem log_Modd_lt_N (B : ℕ) : Nat.log 2 (Modd B) + 4 ≤ Nn B := Nat.le_max_right _ _

/-- `Modd B ≤ 2^(Nn B - 3)` for `B ≥ 8`. -/
theorem Modd_le_pow_N {B : ℕ} (_hB : 8 ≤ B) : Modd B ≤ 2 ^ (Nn B - 3) := by
  have hlt : Modd B < 2 ^ (Nat.log 2 (Modd B) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : Nat.log 2 (Modd B) + 1 ≤ Nn B - 3 := by
    have := log_Modd_lt_N B
    omega
  exact le_trans hlt.le (pow_le_pow_right' (by norm_num) hle)

/-- `D B` divides `K B`. -/
theorem D_dvd_K (B : ℕ) : D B ∣ K B := by
  rw [D_eq_e_mul_Modd, K]
  have h1 : 2 ^ e B * Modd B ∣ 2 ^ Nn B * Modd B :=
    Nat.mul_dvd_mul_right (pow_dvd_pow 2 (e_le_N B)) (Modd B)
  rwa [mul_comm (Modd B) (2 ^ Nn B)]

/-- `K B / 4 = Modd B * 2^(Nn B - 2)`. -/
theorem K_div_four (B : ℕ) (hB : 8 ≤ B) : K B / 4 = Modd B * 2 ^ (Nn B - 2) := by
  have hN3 : 3 ≤ Nn B := le_trans (e_ge_three hB) (e_le_N B)
  have hN2 : 2 ≤ Nn B := by omega
  unfold K
  have hpow : 4 ∣ 2 ^ Nn B := by
    obtain ⟨k, hk⟩ : ∃ k, Nn B = 2 + k := ⟨Nn B - 2, by omega⟩
    exact ⟨2 ^ k, by rw [hk, pow_add]; norm_num⟩
  rw [Nat.mul_div_assoc _ hpow]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k, Nn B = 2 + k := ⟨Nn B - 2, by omega⟩
  rw [hk, pow_add]
  norm_num


/-- A prime `p ≠ 2` at most `B` divides `Modd B`, for `B ≥ 8`. -/
theorem prime_dvd_Modd {B p : ℕ} (hB8 : 8 ≤ B) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hpB : p ≤ B) : p ∣ Modd B := by
  have hDp : p ∣ D B := by
    have hz : D B ≠ 0 := ne_of_gt (D_pos B)
    rw [show p = p ^ 1 from (pow_one p).symm, hp.pow_dvd_iff_le_factorization hz,
      Nat.factorization_lcmUpto B hp]
    exact Nat.log_pos hp.one_lt hpB
  have he := e_ge_three hB8
  have hcop : Nat.Coprime p (2 ^ e B) :=
    ((Nat.coprime_primes hp (by norm_num)).mpr hp2).pow_right _
  have hM : p ∣ 2 ^ e B * Modd B := by rw [← D_eq_e_mul_Modd]; exact hDp
  exact hcop.dvd_of_dvd_mul_left hM

/-- `105 ∣ Modd B` for `B ≥ 8`. -/
theorem dvd_Modd_105 {B : ℕ} (hB8 : 8 ≤ B) : 105 ∣ Modd B := by
  have h3 : 3 ∣ Modd B := prime_dvd_Modd hB8 (by norm_num) (by norm_num) (by omega)
  have h5 : 5 ∣ Modd B := prime_dvd_Modd hB8 (by norm_num) (by norm_num) (by omega)
  have h7 : 7 ∣ Modd B := prime_dvd_Modd hB8 (by norm_num) (by norm_num) (by omega)
  have h15 : 15 ∣ Modd B := (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3 h5
  exact (by norm_num : Nat.Coprime 15 7).mul_dvd_of_dvd_of_dvd h15 h7

/-- `Modd B ≥ 105` for `B ≥ 8`. -/
theorem Modd_ge_105 {B : ℕ} (hB8 : 8 ≤ B) : 105 ≤ Modd B :=
  Nat.le_of_dvd (Modd_pos B) (dvd_Modd_105 hB8)

/-- `60 ∣ K B` for `B ≥ 8`. -/
theorem sixty_dvd_K {B : ℕ} (hB8 : 8 ≤ B) : 60 ∣ K B := by
  have h3 : 3 ∣ Modd B := prime_dvd_Modd hB8 (by norm_num) (by norm_num) (by omega)
  have h5 : 5 ∣ Modd B := prime_dvd_Modd hB8 (by norm_num) (by norm_num) (by omega)
  have h15 : 15 ∣ Modd B := (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3 h5
  have hN3 : 3 ≤ Nn B := le_trans (e_ge_three hB8) (e_le_N B)
  have h4 : 4 ∣ 2 ^ Nn B := by
    obtain ⟨k, hk⟩ : ∃ k, Nn B = 2 + k := ⟨Nn B - 2, by omega⟩
    exact ⟨2 ^ k, by rw [hk, pow_add]; norm_num⟩
  have h15K : 15 ∣ K B := dvd_mul_of_dvd_left h15 (2 ^ Nn B)
  have h4K : 4 ∣ K B := dvd_mul_of_dvd_right h4 (Modd B)
  exact (by norm_num : Nat.Coprime 4 15).mul_dvd_of_dvd_of_dvd h4K h15K

/-- `2^i = 2^j → i = j`. -/
theorem pow2_inj {i j : ℕ} (h : (2 : ℕ) ^ i = 2 ^ j) : i = j :=
  Nat.pow_right_injective (le_refl 2) h

/-- `Modd B * 2^i = Modd B * 2^j → i = j`. -/
theorem Mpow2_inj {B i j : ℕ} (h : Modd B * 2 ^ i = Modd B * 2 ^ j) : i = j :=
  Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left (Modd_pos B) h)

/-- `2^i` is never equal to `Modd B * 2^j`. -/
theorem label_ne {B : ℕ} (hB8 : 8 ≤ B) (i j : ℕ) : (2 : ℕ) ^ i ≠ Modd B * 2 ^ j := by
  intro heq
  have hp2 : Nat.Prime 2 := by norm_num
  have h1 : ((2 : ℕ) ^ i).factorization 2 = i := Nat.factorization_pow_self hp2
  have e1 : (Modd B * 2 ^ j : ℕ).factorization 2 =
      (Modd B).factorization 2 + (2 ^ j : ℕ).factorization 2 := by
    rw [Nat.factorization_mul (Modd_pos B).ne' (show (2 : ℕ) ^ j ≠ 0 by positivity),
      Finsupp.add_apply]
  have h2 : (Modd B * 2 ^ j : ℕ).factorization 2 = j := by
    rw [e1, Nat.factorization_eq_zero_of_not_dvd (Modd_odd B), Nat.factorization_pow_self hp2,
      Nat.zero_add]
  have hcong : ((2 : ℕ) ^ i).factorization 2 = (Modd B * 2 ^ j : ℕ).factorization 2 := by
    rw [heq]
  rw [h1, h2] at hcong
  subst hcong
  have hMcancel : Modd B = 1 := by
    have h2ipos : (0 : ℕ) < 2 ^ i := by positivity
    have heq' : (1 : ℕ) * 2 ^ i = Modd B * 2 ^ i := by rw [one_mul]; exact heq
    exact (Nat.eq_of_mul_eq_mul_right h2ipos heq').symm
  have := one_lt_Modd hB8
  omega

/-- A chain interval at label `lab` lies in the block `[lab, lab+2]`. -/
theorem chainIv_block (lab : ℕ) (ext : Bool) :
    lab ≤ (chainIv lab ext).lo + 1 ∧ (chainIv lab ext).hi ≤ lab + 2 := by
  cases ext <;> simp [chainIv, Iv.triple, Iv.pair]; omega

/-- A chain interval at label `lab` has `lo ≥ lab`. -/
theorem chainIv_lo_ge (lab : ℕ) (ext : Bool) : lab ≤ (chainIv lab ext).lo := by
  cases ext <;> simp [chainIv, Iv.triple, Iv.pair]

/-- A chain interval is a valid pair-or-more piece: `2 ≤ lo`, `lo + 1 ≤ hi`. -/
theorem chainIv_valid {lab : ℕ} (hlab : 8 ≤ lab) (ext : Bool) :
    2 ≤ (chainIv lab ext).lo ∧ (chainIv lab ext).lo + 1 ≤ (chainIv lab ext).hi := by
  cases ext <;> simp [chainIv, Iv.triple, Iv.pair] <;> omega

/-- Two chain intervals at distinct chain labels are separated. -/
theorem chainIv_sep {B lab lab' : ℕ} (h : lab ∈ chainLabels B) (h' : lab' ∈ chainLabels B)
    (hne : lab ≠ lab') (e1 e2 : Bool) : Iv.Sep (chainIv lab e1) (chainIv lab' e2) :=
  sep_of_blocks (chainLabels_dvd B h).1 (chainLabels_dvd B h').1 hne
    (chainIv_block lab e1) (chainIv_block lab' e2)

/-- A chain interval is separated from a pool pair, given the triple at that label is. -/
theorem chainIv_pool_sep {lab : ℕ} {I : Iv} (hsep : Iv.Sep I (Iv.triple lab)) (ext : Bool) :
    Iv.Sep I (chainIv lab ext) := by
  cases ext with
  | true => exact hsep
  | false =>
    refine Sep.of_sub hsep ⟨?_, ?_⟩
    · show lab ≤ lab + 1
      omega
    · show lab + 1 + 1 ≤ lab + 2
      omega

/-- The small interval lies in `[2, 6]`. -/
theorem smallIv_block {h : ℕ} (hh : h ∈ hSet) : 2 ≤ (smallIv h).lo ∧ (smallIv h).hi ≤ 6 := by
  simp only [hSet, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [smallIv]

/-- The small interval is a valid configuration piece. -/
theorem smallIv_valid {h : ℕ} (hh : h ∈ hSet) :
    2 ≤ (smallIv h).lo ∧ (smallIv h).lo + 1 ≤ (smallIv h).hi := by
  simp only [hSet, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [smallIv]

/-- Membership in a seed configuration's finset. -/
theorem seedF_mem (B h : ℕ) (U V : Finset ℕ) (pool : Finset Iv) (I : Iv) :
    I ∈ seedF B h U V pool ↔
      I = smallIv h ∨ (∃ i ∈ Icc 3 (Nn B), chainIv (2 ^ i) (decide (i ∈ U)) = I) ∨
      (∃ i ∈ Icc 3 (Nn B), chainIv (Modd B * 2 ^ i) (decide (i ∈ V)) = I) ∨ I ∈ pool := by
  simp only [seedF, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem mem_chainLabels1 (B : ℕ) {i : ℕ} (hi : i ∈ Icc 3 (Nn B)) :
    (2 : ℕ) ^ i ∈ chainLabels B := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)

theorem mem_chainLabels2 (B : ℕ) {i : ℕ} (hi : i ∈ Icc 3 (Nn B)) :
    Modd B * 2 ^ i ∈ chainLabels B := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)

theorem seedF_isConfig (B h : ℕ) (hB8 : 8 ≤ B) (hh : h ∈ hSet) (U V : Finset ℕ)
    (_hU : U ⊆ Icc 3 (Nn B)) (_hV : V ⊆ Icc 3 (Nn B))
    (PB pool : Finset Iv) (hpool : pool ⊆ PB)
    (hPBpair : ∀ I ∈ PB, 8 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hPBsep : ∀ I ∈ PB, ∀ J ∈ PB, I ≠ J → Iv.Sep I J)
    (hPBchain : ∀ I ∈ PB, ∀ lab ∈ chainLabels B, Iv.Sep I (Iv.triple lab)) :
    ∃ C : Config, C.F = seedF B h U V pool := by
  have hlab1 := @mem_chainLabels1 B
  have hlab2 := @mem_chainLabels2 B
  have htwo_le : ∀ I ∈ seedF B h U V pool, 2 ≤ I.lo := by
    intro I hI
    rcases (seedF_mem B h U V pool I).mp hI with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hIpool
    · exact (smallIv_valid hh).1
    · exact (chainIv_valid (chainLabels_dvd B (hlab1 hi)).2 _).1
    · exact (chainIv_valid (chainLabels_dvd B (hlab2 hi)).2 _).1
    · exact (hPBpair I (hpool hIpool)).1.trans' (by norm_num)
  have hlen_ge : ∀ I ∈ seedF B h U V pool, I.lo + 1 ≤ I.hi := by
    intro I hI
    rcases (seedF_mem B h U V pool I).mp hI with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hIpool
    · exact (smallIv_valid hh).2
    · exact (chainIv_valid (chainLabels_dvd B (hlab1 hi)).2 _).2
    · exact (chainIv_valid (chainLabels_dvd B (hlab2 hi)).2 _).2
    · have := hPBpair I (hpool hIpool); omega
  have hsep : ∀ I ∈ seedF B h U V pool, ∀ J ∈ seedF B h U V pool, I ≠ J → Iv.Sep I J := by
    intro I hI J hJ hIJ
    rcases (seedF_mem B h U V pool I).mp hI with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hIpool <;>
      rcases (seedF_mem B h U V pool J).mp hJ with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | hJpool
    · exact absurd rfl hIJ
    · exact sep_small (smallIv_block hh).2
        ((chainIv_lo_ge _ _).trans' (chainLabels_dvd B (hlab1 hj)).2)
    · exact sep_small (smallIv_block hh).2
        ((chainIv_lo_ge _ _).trans' (chainLabels_dvd B (hlab2 hj)).2)
    · exact sep_small (smallIv_block hh).2 (hPBpair J (hpool hJpool)).1
    · exact (sep_small (smallIv_block hh).2
        ((chainIv_lo_ge _ _).trans' (chainLabels_dvd B (hlab1 hi)).2)).symm
    · have hij : i ≠ j := fun he => hIJ (by rw [he])
      exact chainIv_sep (hlab1 hi) (hlab1 hj) (fun he => hij (pow2_inj he)) _ _
    · exact chainIv_sep (hlab1 hi) (hlab2 hj) (label_ne hB8 i j) _ _
    · exact (chainIv_pool_sep (hPBchain J (hpool hJpool) _ (hlab1 hi)) _).symm
    · exact (sep_small (smallIv_block hh).2
        ((chainIv_lo_ge _ _).trans' (chainLabels_dvd B (hlab2 hi)).2)).symm
    · exact chainIv_sep (hlab2 hi) (hlab1 hj) (fun he => label_ne hB8 j i he.symm) _ _
    · have hij : i ≠ j := fun he => hIJ (by rw [he])
      exact chainIv_sep (hlab2 hi) (hlab2 hj) (fun he => hij (Mpow2_inj he)) _ _
    · exact (chainIv_pool_sep (hPBchain J (hpool hJpool) _ (hlab2 hi)) _).symm
    · exact (sep_small (smallIv_block hh).2 (hPBpair I (hpool hIpool)).1).symm
    · exact chainIv_pool_sep (hPBchain I (hpool hIpool) _ (hlab1 hj)) _
    · exact chainIv_pool_sep (hPBchain I (hpool hIpool) _ (hlab2 hj)) _
    · exact hPBsep I (hpool hIpool) J (hpool hJpool) hIJ
  exact ⟨⟨seedF B h U V pool, htwo_le, hlen_ge, hsep⟩, rfl⟩

/-- A chain interval's `hi` field. -/
theorem chainIv_hi (lab : ℕ) (ext : Bool) : (chainIv lab ext).hi = lab + 2 := by
  cases ext <;> simp [chainIv, Iv.triple, Iv.pair]

/-- A small interval is never equal to a chain interval. -/
theorem smallIv_ne_chainIv {B h lab : ℕ} (hh : h ∈ hSet) (hlab : lab ∈ chainLabels B)
    (ext : Bool) : smallIv h ≠ chainIv lab ext := by
  intro heq
  have h1 := (smallIv_block hh).2
  have h2 := (chainLabels_dvd B hlab).2
  have h3 : (smallIv h).hi = (chainIv lab ext).hi := by rw [heq]
  rw [chainIv_hi] at h3
  omega

/-- Two chain intervals at distinct chain labels are distinct. -/
theorem chainIv_ne_of_ne {lab lab' : ℕ} (hne : lab ≠ lab') (e1 e2 : Bool) :
    chainIv lab e1 ≠ chainIv lab' e2 := by
  intro heq
  have h3 : (chainIv lab e1).hi = (chainIv lab' e2).hi := by rw [heq]
  rw [chainIv_hi, chainIv_hi] at h3
  exact hne (by omega)

/-- A chain interval based on `2^i` never equals one based on `Modd B * 2^j`. -/
theorem chainIv1_ne_chainIv2 {B : ℕ} (hB8 : 8 ≤ B) (i j : ℕ) (e1 e2 : Bool) :
    chainIv (2 ^ i) e1 ≠ chainIv (Modd B * 2 ^ j) e2 :=
  chainIv_ne_of_ne (label_ne hB8 i j) e1 e2

/-- A pool pair separated from a chain triple is distinct from any chain interval at that
label. -/
theorem pool_ne_chainIv {lab : ℕ} {I : Iv} (hsep : Iv.Sep I (Iv.triple lab)) (ext : Bool)
    (hIlohi : I.lo ≤ I.hi) : I ≠ chainIv lab ext := by
  intro heq
  have hS : Iv.Sep I (chainIv lab ext) := chainIv_pool_sep hsep ext
  rw [← heq] at hS
  exact absurd rfl (Sep.ne hS hIlohi hIlohi)

/-- Injectivity of a chain-index map based on `2^i`, reading off `i` from the `hi` field. -/
theorem chainIv_fun_inj1 {f : ℕ → Bool} {i j : ℕ}
    (h : chainIv (2 ^ i) (f i) = chainIv (2 ^ j) (f j)) : i = j := by
  have hh : (chainIv (2 ^ i) (f i)).hi = (chainIv (2 ^ j) (f j)).hi := by rw [h]
  rw [chainIv_hi, chainIv_hi] at hh
  exact pow2_inj (by omega)

/-- Injectivity of a chain-index map based on `Modd B * 2^i`, reading off `i` from the
`hi` field. -/
theorem chainIv_fun_inj2 {B : ℕ} {f : ℕ → Bool} {i j : ℕ}
    (h : chainIv (Modd B * 2 ^ i) (f i) = chainIv (Modd B * 2 ^ j) (f j)) : i = j := by
  have hh : (chainIv (Modd B * 2 ^ i) (f i)).hi = (chainIv (Modd B * 2 ^ j) (f j)).hi := by
    rw [h]
  rw [chainIv_hi, chainIv_hi] at hh
  exact Mpow2_inj (B := B) (by omega)

/-- The mass of a chain interval in terms of the baseline pair mass and an extension term. -/
theorem chainIv_mass (lab : ℕ) (ext : Bool) :
    (chainIv lab ext).mass = (Iv.pair (lab + 1)).mass + (if ext then (1 : ℚ) / lab else 0) := by
  cases ext
  · simp [chainIv]
  · simp only [chainIv, ite_true]
    rw [triple_mass, pair_mass]
    push_cast
    ring

/-- The cardinality of a seed configuration's finset. -/
theorem seedF_card (B h : ℕ) (hB8 : 8 ≤ B) (hh : h ∈ hSet) (U V : Finset ℕ)
    (PB pool : Finset Iv) (hpool : pool ⊆ PB)
    (hPBpair : ∀ I ∈ PB, 8 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hPBchain : ∀ I ∈ PB, ∀ lab ∈ chainLabels B, Iv.Sep I (Iv.triple lab)) :
    (seedF B h U V pool).card = tB B + 1 + pool.card := by
  have hN3 : 3 ≤ Nn B := le_trans (e_ge_three hB8) (e_le_N B)
  have hIcc : (Icc 3 (Nn B)).card = Nn B - 2 := by rw [Nat.card_Icc]; omega
  have hinj1 : Set.InjOn (fun i => chainIv (2 ^ i) (decide (i ∈ U))) (Icc 3 (Nn B)) := by
    intro i _ j _ h
    dsimp only at h
    have hh : (chainIv (2 ^ i) (decide (i ∈ U))).hi = (chainIv (2 ^ j) (decide (j ∈ U))).hi := by
      rw [h]
    rw [chainIv_hi, chainIv_hi] at hh
    exact pow2_inj (by omega)
  have hinj2 : Set.InjOn (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V))) (Icc 3 (Nn B)) := by
    intro i _ j _ h
    dsimp only at h
    have hh : (chainIv (Modd B * 2 ^ i) (decide (i ∈ V))).hi =
        (chainIv (Modd B * 2 ^ j) (decide (j ∈ V))).hi := by rw [h]
    rw [chainIv_hi, chainIv_hi] at hh
    exact Mpow2_inj (B := B) (by omega)
  have hcard1 : ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))).card =
      Nn B - 2 := by rw [Finset.card_image_of_injOn hinj1, hIcc]
  have hcard2 : ((Icc 3 (Nn B)).image
      (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))).card = Nn B - 2 := by
    rw [Finset.card_image_of_injOn hinj2, hIcc]
  have hpoolIlohi : ∀ I ∈ pool, I.lo ≤ I.hi := fun I hI => by
    have := hPBpair I (hpool hI); omega
  have hd1 : Disjoint ({smallIv h} : Finset Iv)
      ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    exact smallIv_ne_chainIv hh (mem_chainLabels1 B hi) _ heq.symm
  have hd2 : Disjoint ({smallIv h} : Finset Iv)
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    exact smallIv_ne_chainIv hh (mem_chainLabels2 B hi) _ heq.symm
  have hd3 : Disjoint ({smallIv h} : Finset Iv) pool := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    have h8 := (hPBpair (smallIv h) (hpool hmem)).1
    have h6 := (smallIv_block hh).2
    have hlh := (smallIv_valid hh).2
    omega
  have hpoolIlohi : ∀ I ∈ pool, I.lo ≤ I.hi := fun I hI => by
    have := hPBpair I (hpool hI); omega
  have hd4 : Disjoint ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))))
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hx2
    exact chainIv1_ne_chainIv2 hB8 i j _ _ heq.symm
  have hd5 : Disjoint ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) pool := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    exact pool_ne_chainIv (hPBchain _ (hpool hx2) _ (mem_chainLabels1 B hi)) _
      (hpoolIlohi _ hx2) rfl
  have hd6 : Disjoint ((Icc 3 (Nn B)).image
      (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) pool := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    exact pool_ne_chainIv (hPBchain _ (hpool hx2) _ (mem_chainLabels2 B hi)) _
      (hpoolIlohi _ hx2) rfl
  have e1 : Disjoint ({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) pool :=
    Finset.disjoint_union_left.mpr ⟨hd3, hd5⟩
  have e2 : Disjoint (({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) pool :=
    Finset.disjoint_union_left.mpr ⟨e1, hd6⟩
  have e3 : Disjoint ({smallIv h} : Finset Iv)
      ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) := hd1
  have e4 : Disjoint ({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))))
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) :=
    Finset.disjoint_union_left.mpr ⟨hd2, hd4⟩
  show ({smallIv h} ∪ (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))) ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V))) ∪ pool).card =
      tB B + 1 + pool.card
  rw [Finset.card_union_of_disjoint e2, Finset.card_union_of_disjoint e4,
    Finset.card_union_of_disjoint e3, Finset.card_singleton, hcard1, hcard2, tB]
  omega

/-- The reciprocal-mass decomposition of a seed configuration's finset. -/
theorem seedF_mass (B h : ℕ) (hB8 : 8 ≤ B) (hh : h ∈ hSet) (U V : Finset ℕ)
    (hU : U ⊆ Icc 3 (Nn B)) (hV : V ⊆ Icc 3 (Nn B))
    (PB pool : Finset Iv) (hpool : pool ⊆ PB)
    (hPBpair : ∀ I ∈ PB, 8 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hPBchain : ∀ I ∈ PB, ∀ lab ∈ chainLabels B, Iv.Sep I (Iv.triple lab)) :
    ∑ I ∈ seedF B h U V pool, I.mass =
      (smallIv h).mass + (∑ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass) +
      (∑ i ∈ U, (1 : ℚ) / 2 ^ i) +
      (∑ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass) +
      (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) +
      ∑ I ∈ pool, I.mass := by
  have hinj1 : Set.InjOn (fun i => chainIv (2 ^ i) (decide (i ∈ U))) (Icc 3 (Nn B)) := by
    intro i _ j _ h
    dsimp only at h
    have hh : (chainIv (2 ^ i) (decide (i ∈ U))).hi = (chainIv (2 ^ j) (decide (j ∈ U))).hi := by
      rw [h]
    rw [chainIv_hi, chainIv_hi] at hh
    exact pow2_inj (by omega)
  have hinj2 : Set.InjOn (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V))) (Icc 3 (Nn B)) := by
    intro i _ j _ h
    dsimp only at h
    have hh : (chainIv (Modd B * 2 ^ i) (decide (i ∈ V))).hi =
        (chainIv (Modd B * 2 ^ j) (decide (j ∈ V))).hi := by rw [h]
    rw [chainIv_hi, chainIv_hi] at hh
    exact Mpow2_inj (B := B) (by omega)
  have hd1 : Disjoint ({smallIv h} : Finset Iv)
      ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    exact smallIv_ne_chainIv hh (mem_chainLabels1 B hi) _ heq.symm
  have hd2 : Disjoint ({smallIv h} : Finset Iv)
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    exact smallIv_ne_chainIv hh (mem_chainLabels2 B hi) _ heq.symm
  have hd3 : Disjoint ({smallIv h} : Finset Iv) pool := by
    rw [Finset.disjoint_singleton_left]
    intro hmem
    have h8 := (hPBpair (smallIv h) (hpool hmem)).1
    have h6 := (smallIv_block hh).2
    have hlh := (smallIv_valid hh).2
    omega
  have hpoolIlohi : ∀ I ∈ pool, I.lo ≤ I.hi := fun I hI => by
    have := hPBpair I (hpool hI); omega
  have hd4 : Disjoint ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))))
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hx2
    exact chainIv1_ne_chainIv2 hB8 i j _ _ heq.symm
  have hd5 : Disjoint ((Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) pool := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    exact pool_ne_chainIv (hPBchain _ (hpool hx2) _ (mem_chainLabels1 B hi)) _
      (hpoolIlohi _ hx2) rfl
  have hd6 : Disjoint ((Icc 3 (Nn B)).image
      (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) pool := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx1
    exact pool_ne_chainIv (hPBchain _ (hpool hx2) _ (mem_chainLabels2 B hi)) _
      (hpoolIlohi _ hx2) rfl
  have e1 : Disjoint ({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) pool :=
    Finset.disjoint_union_left.mpr ⟨hd3, hd5⟩
  have e2 : Disjoint (({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U)))) ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) pool :=
    Finset.disjoint_union_left.mpr ⟨e1, hd6⟩
  have e4 : Disjoint ({smallIv h} ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))))
      ((Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V)))) :=
    Finset.disjoint_union_left.mpr ⟨hd2, hd4⟩
  have hU' : (Icc 3 (Nn B)) ∩ U = U := Finset.inter_eq_right.mpr hU
  have hV' : (Icc 3 (Nn B)) ∩ V = V := Finset.inter_eq_right.mpr hV
  have hchain1 : ∀ i ∈ Icc 3 (Nn B),
      (fun i : ℕ => (1 : ℚ) / 2 ^ i) i = (1 : ℚ) / 2 ^ i := fun _ _ => rfl
  show ∑ I ∈ {smallIv h} ∪ (Icc 3 (Nn B)).image (fun i => chainIv (2 ^ i) (decide (i ∈ U))) ∪
      (Icc 3 (Nn B)).image (fun i => chainIv (Modd B * 2 ^ i) (decide (i ∈ V))) ∪ pool, I.mass =
      (smallIv h).mass + (∑ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass) +
      (∑ i ∈ U, (1 : ℚ) / 2 ^ i) +
      (∑ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass) +
      (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) +
      ∑ I ∈ pool, I.mass
  rw [Finset.sum_union e2, Finset.sum_union e4, Finset.sum_union hd1, Finset.sum_singleton,
    Finset.sum_image hinj1, Finset.sum_image hinj2]
  have hsum1 : ∑ i ∈ Icc 3 (Nn B), (chainIv (2 ^ i) (decide (i ∈ U))).mass =
      (∑ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass) + ∑ i ∈ U, (1 : ℚ) / 2 ^ i := by
    have : ∀ i ∈ Icc 3 (Nn B), (chainIv (2 ^ i) (decide (i ∈ U))).mass =
        (Iv.pair (2 ^ i + 1)).mass + (if i ∈ U then (1 : ℚ) / 2 ^ i else 0) := by
      intro i _
      rw [chainIv_mass]
      congr 1
      by_cases hiU : i ∈ U <;> simp [hiU]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib,
      Finset.sum_ite_mem (Icc 3 (Nn B)) U, hU']
  have hsum2 : ∑ i ∈ Icc 3 (Nn B), (chainIv (Modd B * 2 ^ i) (decide (i ∈ V))).mass =
      (∑ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass) +
      ∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i) := by
    have : ∀ i ∈ Icc 3 (Nn B), (chainIv (Modd B * 2 ^ i) (decide (i ∈ V))).mass =
        (Iv.pair (Modd B * 2 ^ i + 1)).mass + (if i ∈ V then (1 : ℚ) / (Modd B * 2 ^ i) else 0) := by
      intro i _
      rw [chainIv_mass]
      congr 1
      by_cases hiV : i ∈ V <;> simp [hiV]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib,
      Finset.sum_ite_mem (Icc 3 (Nn B)) V, hV']
  rw [hsum1, hsum2]
  ring

/-- `K B` is positive. -/
theorem K_pos (B : ℕ) : 0 < K B := by
  unfold K
  exact Nat.mul_pos (Modd_pos B) (by positivity)

/-- Every small interval lies in `seedSupp B`. -/
theorem smallIv_mem_seedSupp {B h : ℕ} (hh : h ∈ hSet) : smallIv h ∈ seedSupp B :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))

/-- Every chain interval lies in `seedSupp B`. -/
theorem chainIv_mem_seedSupp {B lab : ℕ} (hlab : lab ∈ chainLabels B) (ext : Bool) :
    chainIv lab ext ∈ seedSupp B := by
  unfold seedSupp
  cases ext
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hlab))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hlab)

/-- A small interval has length at most `4`. -/
theorem smallIv_ivLen_le4 {h : ℕ} (hh : h ∈ hSet) : ivLen (smallIv h) ≤ 4 := by
  simp only [hSet, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [smallIv, ivLen]

/-- The exact value of a truncated geometric sum of `1/2^i`. -/
theorem sum_inv_two_pow_Icc (a : ℕ) : ∀ N, a ≤ N + 1 →
    ∑ i ∈ Icc a N, (1 : ℚ) / 2 ^ i = 2 / 2 ^ a - 2 / 2 ^ (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro ha
    interval_cases a <;> norm_num
  | succ n ih =>
    intro ha
    by_cases hle : a ≤ n + 1
    · rw [Finset.sum_Icc_succ_top hle, ih hle]
      have h2 : (2 : ℚ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      rw [h2]
      field_simp
      ring
    · have hempty : Icc a (n + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      have haeq : a = n + 2 := by omega
      rw [hempty, haeq]
      simp

set_option maxHeartbeats 1000000 in
/-- The seed family.  `PB` is a stage-`B` pool: `2 s(B)` pairs starting at `8` or later,
with masses in `G_B`, pairwise separated, separated from every chain triple `[lab, lab+2]`,
of total mass below `1/20`. -/
theorem seed_family (B : ℕ) (hB8 : 8 ≤ B)
    (PB : Finset Iv) (hPBcard : PB.card = 2 * s B)
    (hPBpair : ∀ I ∈ PB, 8 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hPBG : ∀ I ∈ PB, InG B I.mass)
    (hPBsep : ∀ I ∈ PB, ∀ J ∈ PB, I ≠ J → Iv.Sep I J)
    (hPBchain : ∀ I ∈ PB, ∀ lab ∈ chainLabels B, Iv.Sep I (Iv.triple lab))
    (hPBw : ∑ I ∈ PB, I.mass < 1 / 20) :
    ∃ Fm : Fam, Fm.n = B ∧ Fm.u = tB B + 1 ∧ Fm.v = tB B + 1 + 2 * s B ∧
      Fm.bound = 39 / 20 ∧ Fm.supp = seedSupp B ∪ PB ∧ Fm.S = seedLong B := by
  have hN3 : 3 ≤ Nn B := le_trans (e_ge_three hB8) (e_le_N B)
  have hM105 : 105 ≤ Modd B := Modd_ge_105 hB8
  have hMpos : 0 < Modd B := Modd_pos B
  set σ1 : ℚ := ∑ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass with hσ1def
  set σ2 : ℚ := ∑ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass with hσ2def
  set β : ℚ := 11 / 30 + σ1 + σ2 with hβdef
  have hgeom : ∑ i ∈ Icc 3 (Nn B), (1 : ℚ) / 2 ^ i ≤ 1 / 4 := by
    rw [sum_inv_two_pow_Icc 3 (Nn B) (by omega)]
    have h0 : (0 : ℚ) ≤ 2 / 2 ^ (Nn B + 1) := by positivity
    norm_num
    linarith
  have hσ1le : σ1 ≤ 1 / 2 := by
    have hterm : ∀ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass ≤ 2 * ((1 : ℚ) / 2 ^ i) := by
      intro i _
      have h1 : (Iv.pair (2 ^ i + 1)).mass ≤ 2 / ((2 ^ i + 1 : ℕ) : ℚ) :=
        pair_mass_le (a := 2 ^ i + 1) (Nat.le_add_left 1 _)
      have h2 : (2 : ℚ) / ((2 ^ i + 1 : ℕ) : ℚ) ≤ 2 * ((1 : ℚ) / 2 ^ i) := by
        rw [mul_one_div]
        have hpos : (0 : ℚ) < 2 ^ i := by positivity
        have hle : (2 : ℚ) ^ i ≤ ((2 ^ i + 1 : ℕ) : ℚ) := by push_cast; linarith
        exact div_le_div_of_nonneg_left (by norm_num) hpos hle
      linarith
    have := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at this
    calc σ1 = ∑ i ∈ Icc 3 (Nn B), (Iv.pair (2 ^ i + 1)).mass := hσ1def
      _ ≤ 2 * ∑ i ∈ Icc 3 (Nn B), (1 : ℚ) / 2 ^ i := this
      _ ≤ 2 * (1 / 4) := by linarith [hgeom]
      _ = 1 / 2 := by norm_num
  have hσ2le : σ2 ≤ 1 / 210 := by
    have hterm : ∀ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass ≤
        2 * ((1 : ℚ) / 105 / 2 ^ i) := by
      intro i _
      have h1 : (Iv.pair (Modd B * 2 ^ i + 1)).mass ≤ 2 / ((Modd B * 2 ^ i + 1 : ℕ) : ℚ) :=
        pair_mass_le (a := Modd B * 2 ^ i + 1) (Nat.le_add_left 1 _)
      have h2 : (2 : ℚ) / ((Modd B * 2 ^ i + 1 : ℕ) : ℚ) ≤ 2 * ((1 : ℚ) / 105 / 2 ^ i) := by
        have hpos : (0 : ℚ) < 105 * 2 ^ i := by positivity
        have hMQ : (105 : ℚ) ≤ (Modd B : ℚ) := by exact_mod_cast hM105
        have hle : (105 : ℚ) * 2 ^ i ≤ ((Modd B * 2 ^ i + 1 : ℕ) : ℚ) := by
          push_cast
          have : (105 : ℚ) * 2 ^ i ≤ (Modd B : ℚ) * 2 ^ i := by
            apply mul_le_mul_of_nonneg_right hMQ (by positivity)
          linarith
        have := div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 2) hpos hle
        calc (2:ℚ) / ((Modd B * 2 ^ i + 1 : ℕ) : ℚ) ≤ 2 / (105 * 2 ^ i) := this
          _ = 2 * ((1:ℚ)/105/2^i) := by ring
      linarith
    have hsum := Finset.sum_le_sum hterm
    have heq : ∑ i ∈ Icc 3 (Nn B), 2 * ((1:ℚ) / 105 / 2 ^ i) =
        (2 / 105) * ∑ i ∈ Icc 3 (Nn B), (1:ℚ) / 2 ^ i := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    calc σ2 = ∑ i ∈ Icc 3 (Nn B), (Iv.pair (Modd B * 2 ^ i + 1)).mass := hσ2def
      _ ≤ ∑ i ∈ Icc 3 (Nn B), 2 * ((1 : ℚ) / 105 / 2 ^ i) := hsum
      _ = (2/105) * ∑ i ∈ Icc 3 (Nn B), (1:ℚ)/2^i := heq
      _ ≤ (2/105) * (1/4) := by linarith [hgeom]
      _ ≤ 1/210 := by norm_num
  have hβle : β ≤ 9 / 10 := by rw [hβdef]; linarith [hσ1le, hσ2le]
  classical
  let P : Config → Prop := fun C => ∃ h ∈ hSet, ∃ U ⊆ Icc 3 (Nn B), ∃ V ⊆ Icc 3 (Nn B),
    ∃ pool ⊆ PB, C.F = seedF B h U V pool ∧
      (h : ℚ) / 60 + (∑ i ∈ U, (1 : ℚ) / 2 ^ i) + (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) < 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  exact {
    P := P, supp := seedSupp B ∪ PB, S := seedLong B, β := β, n := B,
    u := tB B + 1, v := tB B + 1 + 2 * s B, bound := 39 / 20,
    mem_supp := by
        intro C hC I hI
        obtain ⟨h, hh, U, hU, V, hV, pool, hpool, hCF, _⟩ := hC
        rw [hCF] at hI
        rcases (seedF_mem B h U V pool I).mp hI with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hIpool
        · exact Finset.mem_union_left _ (smallIv_mem_seedSupp hh)
        · exact Finset.mem_union_left _ (chainIv_mem_seedSupp (mem_chainLabels1 B hi) _)
        · exact Finset.mem_union_left _ (chainIv_mem_seedSupp (mem_chainLabels2 B hi) _)
        · exact Finset.mem_union_right _ (hpool hIpool),
    supp_len := by
        intro I hI
        rcases Finset.mem_union.mp hI with hIseed | hIPB
        · unfold seedSupp at hIseed
          rcases Finset.mem_union.mp hIseed with hIAB | hItriple
          · rcases Finset.mem_union.mp hIAB with hIsmall | hIpair
            · obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.mp hIsmall
              exact smallIv_ivLen_le4 hh0
            · obtain ⟨lab, hlab, rfl⟩ := Finset.mem_image.mp hIpair
              simp only [ivLen, Iv.pair]
              omega
          · obtain ⟨lab, hlab, rfl⟩ := Finset.mem_image.mp hItriple
            simp only [ivLen, Iv.triple]
            omega
        · have := hPBpair I hIPB
          simp only [ivLen]
          omega,
    supp_long := by
        intro I hI hlen
        rcases Finset.mem_union.mp hI with hIseed | hIPB
        · unfold seedSupp at hIseed
          rcases Finset.mem_union.mp hIseed with hIAB | hItriple
          · rcases Finset.mem_union.mp hIAB with hIsmall | hIpair
            · exact Finset.mem_union_left _ hIsmall
            · exfalso
              obtain ⟨lab, hlab, rfl⟩ := Finset.mem_image.mp hIpair
              simp only [ivLen, Iv.pair] at hlen
              omega
          · exact Finset.mem_union_right _ hItriple
        · exfalso
          have := hPBpair I hIPB
          simp only [ivLen] at hlen
          omega,
    w_lt := by
        intro C hC
        obtain ⟨h, hh, U, hU, V, hV, pool, hpool, hCF, hextlt⟩ := hC
        have hmass := seedF_mass B h hB8 hh U V hU hV PB pool hpool hPBpair hPBchain
        show C.w < (39 : ℚ) / 20
        unfold Config.w
        rw [hCF, hmass, smallIv_mass h hh]
        have hpoolle : ∑ I ∈ pool, I.mass ≤ ∑ I ∈ PB, I.mass :=
          Finset.sum_le_sum_of_subset_of_nonneg hpool (fun I _ _ => mass_nonneg I)
        have hpoollt : ∑ I ∈ pool, I.mass < 1 / 20 := lt_of_le_of_lt hpoolle hPBw
        have hβeq : β = 11 / 30 + σ1 + σ2 := hβdef
        nlinarith [hβle, hextlt, hpoollt],
    realizes := by
        intro z hz c hc1 hc2
        set r := c - (tB B + 1) with hrdef
        have hrle : r ≤ PB.card := by rw [hPBcard]; omega
        obtain ⟨pool, hpool, hpoolcard⟩ := Finset.exists_subset_card_eq hrle
        have hpoolG : InG B (∑ I ∈ pool, I.mass) :=
          InG_sum pool Iv.mass (fun I hI => hPBG I (hpool hI))
        have hw0 : InG B (z - β - ∑ I ∈ pool, I.mass) := by
          have heq : z - β - ∑ I ∈ pool, I.mass = (z - β) - ∑ I ∈ pool, I.mass := by ring
          rw [heq]; exact hz.sub hpoolG
        set w0 : ℚ := z - β - ∑ I ∈ pool, I.mass with hw0def
        set x : ℚ := Int.fract w0 with hxdef
        have hx0 : 0 ≤ x := Int.fract_nonneg w0
        have hx1 : x < 1 := Int.fract_lt_one w0
        have hxG : InG B x := InG_fract hw0
        obtain ⟨h, hh, hrem0, hrem1⟩ : ∃ h ∈ hSet, (h : ℚ) / 60 ≤ x ∧ x - (h : ℚ) / 60 < 1 / 4 := by
          by_cases c1 : x < 15 / 60
          · exact ⟨0, by decide, by norm_num; linarith, by norm_num; linarith⟩
          push Not at c1
          by_cases c2 : x < 28 / 60
          · exact ⟨15, by decide, by norm_num; linarith, by norm_num; linarith⟩
          push Not at c2
          by_cases c3 : x < 43 / 60
          · exact ⟨28, by decide, by norm_num; linarith, by norm_num; linarith⟩
          push Not at c3
          by_cases c4 : x < 55 / 60
          · exact ⟨43, by decide, by norm_num; linarith, by norm_num; linarith⟩
          push Not at c4
          exact ⟨55, by decide, by norm_num; linarith, by norm_num; linarith⟩
        set rem : ℚ := x - (h : ℚ) / 60 with hremdef
        have hKpos : (0 : ℚ) < (K B : ℚ) := by exact_mod_cast K_pos B
        obtain ⟨t, ht⟩ := D_dvd_K B
        obtain ⟨zx, hzx⟩ := hxG
        obtain ⟨kk, hkk⟩ := sixty_dvd_K hB8
        have hxK : x * (K B : ℚ) = ((zx * t : ℤ) : ℚ) := by
          rw [ht]; push_cast; linear_combination (t : ℚ) * hzx
        have hhK : (h : ℚ) / 60 * (K B : ℚ) = ((h * kk : ℕ) : ℚ) := by
          rw [hkk]; push_cast; ring
        have hremK : rem * (K B : ℚ) = ((zx * t - h * kk : ℤ) : ℚ) := by
          rw [hremdef, sub_mul, hxK, hhK]; push_cast; ring
        have hnonneg : (0 : ℤ) ≤ zx * t - h * kk := by
          have h1 : (0 : ℚ) ≤ rem * (K B : ℚ) := mul_nonneg (by linarith) hKpos.le
          rw [hremK] at h1; exact_mod_cast h1
        set y : ℕ := (zx * t - h * kk).toNat with hydef
        have hycast : (y : ℤ) = zx * t - h * kk := Int.toNat_of_nonneg hnonneg
        have hyQ : (y : ℚ) = rem * (K B : ℚ) := by rw [hremK]; exact_mod_cast hycast
        have hybound : (y : ℚ) < (K B : ℚ) / 4 := by
          rw [hyQ]; nlinarith [hKpos, hrem1]
        have h4dvd : (4 : ℕ) ∣ K B := ⟨15 * kk, by rw [hkk]; ring⟩
        have hcast4 : (K B : ℚ) / 4 = ((K B / 4 : ℕ) : ℚ) := by
          rw [div_eq_iff (by norm_num : (4 : ℚ) ≠ 0)]
          exact_mod_cast (Nat.div_mul_cancel h4dvd).symm
        rw [hcast4] at hybound
        have hyNat : y < K B / 4 := by exact_mod_cast hybound
        rw [K_div_four B hB8] at hyNat
        set a : ℕ := y / Modd B with hadef
        set b' : ℕ := y % Modd B with hbdef
        have hyab : y = Modd B * a + b' := (Nat.div_add_mod y (Modd B)).symm
        have hbl : b' < Modd B := Nat.mod_lt y (Modd_pos B)
        have hal : a < 2 ^ (Nn B - 2) := by
          by_contra hcon
          push Not at hcon
          have hmul : Modd B * 2 ^ (Nn B - 2) ≤ Modd B * a := Nat.mul_le_mul_left _ hcon
          omega
        have hblt3 : b' < 2 ^ (Nn B - 3) := lt_of_lt_of_le hbl (Modd_le_pow_N hB8)
        have hNa : ∀ j ∈ a.bitIndices, j ≤ Nn B - 3 := by
          intro j hj
          by_contra hcon
          push Not at hcon
          have hjge : Nn B - 2 ≤ j := by omega
          have hpow : (2 : ℕ) ^ (Nn B - 2) ≤ 2 ^ j := pow_le_pow_right' (by norm_num) hjge
          have halt : a < 2 ^ j := lt_of_lt_of_le hal hpow
          have hfalse : a.testBit j = false := Nat.testBit_eq_false_of_lt halt
          have htrue : a.testBit j = true := Nat.mem_bitIndices.mp hj
          rw [hfalse] at htrue; exact absurd htrue (by decide)
        have hNb : ∀ j ∈ b'.bitIndices, j ≤ Nn B - 4 := by
          intro j hj
          by_contra hcon
          push Not at hcon
          have hjge : Nn B - 3 ≤ j := by omega
          have hpow : (2 : ℕ) ^ (Nn B - 3) ≤ 2 ^ j := pow_le_pow_right' (by norm_num) hjge
          have hblt : b' < 2 ^ j := lt_of_lt_of_le hblt3 hpow
          have hfalse : b'.testBit j = false := Nat.testBit_eq_false_of_lt hblt
          have htrue : b'.testBit j = true := Nat.mem_bitIndices.mp hj
          rw [hfalse] at htrue; exact absurd htrue (by decide)
        set U : Finset ℕ := a.bitIndices.toFinset.image (fun j => Nn B - j) with hUdef
        set V : Finset ℕ := b'.bitIndices.toFinset.image (fun j => Nn B - j) with hVdef
        have hUsub : U ⊆ Icc 3 (Nn B) := by
          intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          rw [List.mem_toFinset] at hj
          have hjb := hNa j hj
          simp only [Finset.mem_Icc]; omega
        have hVsub : V ⊆ Icc 3 (Nn B) := by
          intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          rw [List.mem_toFinset] at hj
          have hjb := hNb j hj
          simp only [Finset.mem_Icc]; omega
        have hinjU : Set.InjOn (fun j => Nn B - j) (a.bitIndices.toFinset : Set ℕ) := by
          intro j hj j' hj' heq
          simp only [Finset.mem_coe, List.mem_toFinset] at hj hj'
          dsimp only at heq
          have h1 := hNa j hj; have h2 := hNa j' hj'; omega
        have hinjV : Set.InjOn (fun j => Nn B - j) (b'.bitIndices.toFinset : Set ℕ) := by
          intro j hj j' hj' heq
          simp only [Finset.mem_coe, List.mem_toFinset] at hj hj'
          dsimp only at heq
          have h1 := hNb j hj; have h2 := hNb j' hj'; omega
        have hUsum : ∑ i ∈ U, (1 : ℚ) / 2 ^ i = (a : ℚ) / 2 ^ (Nn B) := by
          rw [hUdef, Finset.sum_image hinjU]
          have hstep : ∀ j ∈ a.bitIndices.toFinset,
              (1 : ℚ) / 2 ^ (Nn B - j) = (2 : ℚ) ^ j / 2 ^ (Nn B) := by
            intro j hj
            rw [List.mem_toFinset] at hj
            have hjle : j ≤ Nn B := by have := hNa j hj; omega
            have hpoweq : (2 : ℚ) ^ (Nn B) = 2 ^ (Nn B - j) * 2 ^ j := by
              rw [← pow_add]; congr 1; omega
            rw [hpoweq]; field_simp
          have hsumeq : (∑ j ∈ a.bitIndices.toFinset, (2 : ℚ) ^ j) = (a : ℚ) := by
            have := Finset.sum_toFinset_bitIndices_two_pow a
            exact_mod_cast this
          rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, hsumeq]
        have hVsum : ∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i) = (b' : ℚ) / (Modd B * 2 ^ (Nn B)) := by
          rw [hVdef, Finset.sum_image hinjV]
          have hstep : ∀ j ∈ b'.bitIndices.toFinset,
              (1 : ℚ) / (Modd B * 2 ^ (Nn B - j)) = (2 : ℚ) ^ j / (Modd B * 2 ^ (Nn B)) := by
            intro j hj
            rw [List.mem_toFinset] at hj
            have hjle : j ≤ Nn B := by have := hNb j hj; omega
            have hpoweq : (2 : ℚ) ^ (Nn B) = 2 ^ (Nn B - j) * 2 ^ j := by
              rw [← pow_add]; congr 1; omega
            rw [hpoweq]; field_simp
          have hsumeq : (∑ j ∈ b'.bitIndices.toFinset, (2 : ℚ) ^ j) = (b' : ℚ) := by
            have := Finset.sum_toFinset_bitIndices_two_pow b'
            exact_mod_cast this
          rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, hsumeq]
        have hextsum : (h : ℚ) / 60 + (∑ i ∈ U, (1 : ℚ) / 2 ^ i) +
            (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) = x := by
          have hKeq : (K B : ℚ) = (Modd B : ℚ) * 2 ^ (Nn B) := by unfold K; push_cast; ring
          have hyval : (y : ℚ) = (Modd B : ℚ) * (a : ℚ) + (b' : ℚ) := by exact_mod_cast hyab
          have hM0 : (Modd B : ℚ) ≠ 0 := by exact_mod_cast (Modd_pos B).ne'
          have h20 : (2 : ℚ) ^ (Nn B) ≠ 0 := by positivity
          have hcombine : (a : ℚ) / 2 ^ (Nn B) + (b' : ℚ) / ((Modd B : ℚ) * 2 ^ (Nn B)) =
              (y : ℚ) / (K B : ℚ) := by
            rw [hKeq, hyval]; field_simp
          have hyKrem : (y : ℚ) / (K B : ℚ) = rem := by
            rw [hyQ, mul_div_assoc, div_self hKpos.ne', mul_one]
          rw [hremdef] at hyKrem
          rw [hUsum, hVsum]
          linarith [hcombine, hyKrem]
        have hextlt : (h : ℚ) / 60 + (∑ i ∈ U, (1 : ℚ) / 2 ^ i) +
            (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) < 1 := by rw [hextsum]; exact hx1
        obtain ⟨C, hCF⟩ :=
          seedF_isConfig B h hB8 hh U V hUsub hVsub PB pool hpool hPBpair hPBsep hPBchain
        refine ⟨C, ⟨h, hh, U, hUsub, V, hVsub, pool, hpool, hCF, hextlt⟩, ?_, -⌊w0⌋, ?_⟩
        · show C.F.card = c
          rw [hCF, seedF_card B h hB8 hh U V PB pool hpool hPBpair hPBchain, hpoolcard, hrdef]
          omega
        · have hmass := seedF_mass B h hB8 hh U V hUsub hVsub PB pool hpool hPBpair hPBchain
          show C.w = z + ((-⌊w0⌋ : ℤ) : ℚ)
          unfold Config.w
          rw [hCF, hmass, smallIv_mass h hh]
          have hw_eq : (11 : ℚ) / 30 + (h : ℚ) / 60 + σ1 + (∑ i ∈ U, (1 : ℚ) / 2 ^ i) + σ2 +
              (∑ i ∈ V, (1 : ℚ) / (Modd B * 2 ^ i)) + ∑ I ∈ pool, I.mass =
              β + x + ∑ I ∈ pool, I.mass := by
            rw [hβdef]; linarith [hextsum]
          rw [hw_eq]
          have hfract : x + (⌊w0⌋ : ℚ) = w0 := by rw [hxdef]; exact Int.fract_add_floor w0
          push_cast
          linarith [hfract, hw0def]
    }
  repeat rfl

end Erdos289.CLT
