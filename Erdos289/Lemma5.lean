import Erdos289.Defs
import Erdos289.Lemma2
import Erdos289.Lemma4
import Erdos289.Tail

/-!
# Lemma 5: auxiliary pairs with a predetermined count per stage

For a sufficiently large cutoff `L`, fix simultaneously for every prime power `q > L` a family
`F_q` of exactly `s(q) = ⌊q^(1/20)⌋` pairs `[a, a+1]` with `q^(11/10) ≤ a`, `a + 1 ≤ 2 q^(11/10)`,
`4 ∣ a`, both endpoints `(q/2)`-powersmooth, all auxiliary pairs mutually separated and
separated from every possible correction pair, with `|F* ∩ [1, X]| = O(X^(21/22))`.
-/

set_option maxHeartbeats 4000000

namespace Erdos289

open Finset

/-- `s(q) = ⌊q^(1/20)⌋`, the number of pairs added at stage `q`. -/
noncomputable def s (q : ℕ) : ℕ := ⌊(q : ℝ) ^ ((1 : ℝ) / 20)⌋₊

/-- The set `P*` of all possible correction endpoints above the cutoff `L`:
`{q m, q m + 1}` for prime powers `q > L` and `q^(1/10) ≤ m ≤ 2 q^(1/10)`. -/
def Pstar (L : ℕ) : Set ℕ :=
  {n | ∃ q m : ℕ, IsPrimePow q ∧ L < q ∧
    (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10) ∧
    (n = q * m ∨ n = q * m + 1)}

/-- The set of correction pairs whose endpoints lie in `P*`. -/
def PstarPairs (L : ℕ) : Set Iv :=
  {I | ∃ q m : ℕ, IsPrimePow q ∧ L < q ∧
    (q : ℝ) ^ ((1 : ℝ) / 10) ≤ m ∧ (m : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10) ∧ I = Iv.pair (q * m)}

/-- The combined endpoint set `F*` of an auxiliary family `F : ℕ → Finset ℕ`
(where `F q` is the set of left endpoints of the auxiliary pairs at stage `q`). -/
def Fstar (L : ℕ) (F : ℕ → Finset ℕ) : Set ℕ :=
  {n | ∃ q : ℕ, IsPrimePow q ∧ L < q ∧ ∃ a ∈ F q, n = a ∨ n = a + 1}

/-- An auxiliary family for the cutoff `L`: the data required by Lemma 5. -/
structure AuxFamily (L : ℕ) where
  /-- Left endpoints of the auxiliary pairs at stage `q`. -/
  F : ℕ → Finset ℕ
  card_eq : ∀ q, IsPrimePow q → L < q → (F q).card = s q
  lower : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a
  upper : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)
  four_dvd : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, 4 ∣ a
  smooth_lo : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, Powersmooth (q / 2) a
  smooth_hi : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, Powersmooth (q / 2) (a + 1)
  /-- Auxiliary pairs are mutually separated (across all stages). -/
  sep_aux : ∀ q q', IsPrimePow q → L < q → IsPrimePow q' → L < q' →
    ∀ a ∈ F q, ∀ a' ∈ F q', (q, a) ≠ (q', a') → Iv.Sep (Iv.pair a) (Iv.pair a')
  /-- Auxiliary pairs are separated from every possible correction pair. -/
  sep_corr : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, ∀ J ∈ PstarPairs L, Iv.Sep (Iv.pair a) J
  /-- `|F* ∩ [1, X]| = O(X^(21/22))`. -/
  count : ∃ C : ℝ, ∀ X : ℕ, ((Fstar L F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * (X : ℝ) ^ ((21 : ℝ) / 22)

/-- **(4.2)**: `|P* ∩ [1, X]| ≪ X / log X`, independently of `L`. -/
theorem Pstar_count : ∃ C : ℝ, ∀ L X : ℕ, 2 ≤ X →
    ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * X / Real.log X := by
  obtain ⟨Cpp0, hCpp0⟩ := primePow_count_le
  set Cpp : ℝ := max Cpp0 0 with hCppdef
  have hCppnn : 0 ≤ Cpp := le_max_right _ _
  have hCpp : ∀ Y : ℕ, 2 ≤ Y →
      (((Finset.Icc 1 Y).filter (fun n => IsPrimePow n)).card : ℝ) ≤ Cpp * (Y : ℝ) / Real.log Y := by
    intro Y hY
    have hYlogpos : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
    have hmono : Cpp0 * (Y : ℝ) / Real.log Y ≤ Cpp * (Y : ℝ) / Real.log Y := by
      gcongr
      exact le_max_left _ _
    exact (hCpp0 Y hY).trans hmono
  refine ⟨20 * Cpp, fun L X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  set Y : ℕ := ⌈(X : ℝ) ^ ((10 : ℝ) / 11)⌉₊ with hYdef
  set F : Finset ℕ := ((Finset.Icc 1 Y).filter (fun q => IsPrimePow q)).biUnion
      (fun q => (Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
        (fun m => {q * m, q * m + 1})) with hFdef
  -- Facts about `Y = ⌈X^(10/11)⌉₊`.
  have hYrpos : (0 : ℝ) < (X : ℝ) ^ ((10 : ℝ) / 11) := Real.rpow_pos_of_pos hXpos _
  have hYrgt1 : (1 : ℝ) < (X : ℝ) ^ ((10 : ℝ) / 11) := Real.one_lt_rpow hX1 (by norm_num)
  have hYge_real : (X : ℝ) ^ ((10 : ℝ) / 11) ≤ (Y : ℝ) := Nat.le_ceil _
  have hYge2 : 2 ≤ Y := by
    have h1 : (1 : ℝ) < (Y : ℝ) := hYrgt1.trans_le hYge_real
    have h2 : 1 < Y := by exact_mod_cast h1
    omega
  have hYle_real : (Y : ℝ) ≤ 2 * (X : ℝ) ^ ((10 : ℝ) / 11) := by
    have h1 : (Y : ℝ) < (X : ℝ) ^ ((10 : ℝ) / 11) + 1 := Nat.ceil_lt_add_one hYrpos.le
    linarith
  have hYlogpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hYlog_ge : (10 : ℝ) / 11 * Real.log X ≤ Real.log Y := by
    have h1 : Real.log ((X : ℝ) ^ ((10 : ℝ) / 11)) ≤ Real.log Y :=
      Real.log_le_log hYrpos hYge_real
    rwa [Real.log_rpow hXpos] at h1
  -- The endpoint set is contained in the explicit finset `F`.
  have hsub : Pstar L ∩ Set.Icc 1 X ⊆ (F : Set ℕ) := by
    rintro n ⟨⟨q, m, hIPP, hLq, hm1, hm2, hn⟩, hn1, hnX⟩
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hIPP.pos
    have hqm_le : q * m ≤ X := by rcases hn with h | h <;> omega
    have hqmR : (q : ℝ) * (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hqm_le
    have hq_pow : (q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 10) ≤ (q : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hqpos.le
    have hqX : (q : ℝ) ^ ((11 : ℝ) / 10) ≤ (X : ℝ) := by
      have he : (q : ℝ) ^ ((11 : ℝ) / 10) = (q : ℝ) * (q : ℝ) ^ ((1 : ℝ) / 10) := by
        rw [show (11 : ℝ) / 10 = 1 + (1 : ℝ) / 10 by norm_num, Real.rpow_add hqpos, Real.rpow_one]
      rw [he]; linarith
    have hq_le : (q : ℝ) ≤ (X : ℝ) ^ ((10 : ℝ) / 11) := by
      have h1 := Real.rpow_le_rpow (by positivity) hqX (by norm_num : (0 : ℝ) ≤ (10 : ℝ) / 11)
      rwa [← Real.rpow_mul hqpos.le, show (11 : ℝ) / 10 * ((10 : ℝ) / 11) = 1 by norm_num,
        Real.rpow_one] at h1
    have hq_le_Y : q ≤ Y := by
      have h2 : (q : ℝ) ≤ (Y : ℝ) := hq_le.trans hYge_real
      exact_mod_cast h2
    have hqmem : q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hIPP.pos, hq_le_Y⟩, hIPP⟩
    have hmmem : m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊ := by
      simp only [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hm1, Nat.le_floor hm2⟩
    have hnF : n ∈ F := by
      rw [hFdef]
      refine Finset.mem_biUnion.mpr ⟨q, hqmem, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨m, hmmem, ?_⟩
      rcases hn with h | h
      · simp [h]
      · simp [h]
    exact hnF
  -- Cardinality bound for the inner `m`-interval.
  have hIccbound : ∀ q : ℕ, 1 ≤ q →
      ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card : ℝ)
        ≤ (q : ℝ) ^ ((1 : ℝ) / 10) + 2 := by
    intro q _
    set a := ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ with hadef
    set b := ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊ with hbdef
    rcases Nat.lt_or_ge (b + 1) a with hab | hab
    · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [hempty]
      simp
      positivity
    · have hcard : (Finset.Icc a b).card = b + 1 - a := Nat.card_Icc _ _
      have hcast : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
        have := Nat.cast_sub (R := ℝ) hab
        push_cast at this ⊢
        linarith
      rw [hcard, hcast]
      have hb_le : (b : ℝ) ≤ 2 * (q : ℝ) ^ ((1 : ℝ) / 10) := Nat.floor_le (by positivity)
      have ha_ge : (q : ℝ) ^ ((1 : ℝ) / 10) ≤ (a : ℝ) := Nat.le_ceil _
      linarith
  -- `q ≤ Y` gives a uniform bound `q^(1/10) ≤ 2 X^(1/11)`.
  have hq_pow_le : ∀ q : ℕ, q ≤ Y → (q : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 11) := by
    intro q hqY
    have h1 : (q : ℝ) ^ ((1 : ℝ) / 10) ≤ (Y : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqY) (by norm_num)
    have h2 : (Y : ℝ) ^ ((1 : ℝ) / 10) ≤ (2 * (X : ℝ) ^ ((10 : ℝ) / 11)) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hYle_real (by norm_num)
    have h3 : (2 * (X : ℝ) ^ ((10 : ℝ) / 11)) ^ ((1 : ℝ) / 10)
        = (2 : ℝ) ^ ((1 : ℝ) / 10) * (X : ℝ) ^ ((1 : ℝ) / 11) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hXpos.le,
        show (10 : ℝ) / 11 * ((1 : ℝ) / 10) = (1 : ℝ) / 11 by norm_num]
    have h4 : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h5 : (2 : ℝ) ^ ((1 : ℝ) / 10) * (X : ℝ) ^ ((1 : ℝ) / 11) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 11) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    calc (q : ℝ) ^ ((1 : ℝ) / 10) ≤ (Y : ℝ) ^ ((1 : ℝ) / 10) := h1
      _ ≤ (2 * (X : ℝ) ^ ((10 : ℝ) / 11)) ^ ((1 : ℝ) / 10) := h2
      _ = (2 : ℝ) ^ ((1 : ℝ) / 10) * (X : ℝ) ^ ((1 : ℝ) / 11) := h3
      _ ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 11) := h5
  have hX111 : (1 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 11) := Real.one_le_rpow hX1.le (by norm_num)
  -- Uniform bound on the number of endpoints contributed by each prime power `q`.
  have hinner_le : ∀ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      (((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
        (fun m => {q * m, q * m + 1})).card : ℝ) ≤ 8 * (X : ℝ) ^ ((1 : ℝ) / 11) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqY⟩, _⟩ := hq
    have hcardpairs : ∀ m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊,
        ({q * m, q * m + 1} : Finset ℕ).card ≤ 2 :=
      fun m _ => le_trans (Finset.card_insert_le _ _) (by simp)
    have hbiUnion_le :
        ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
          (fun m => {q * m, q * m + 1})).card
        ≤ ∑ m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊,
            ({q * m, q * m + 1} : Finset ℕ).card :=
      Finset.card_biUnion_le
    have hsum_le : ∑ m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊,
        ({q * m, q * m + 1} : Finset ℕ).card
        ≤ ∑ _m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊, 2 :=
      Finset.sum_le_sum hcardpairs
    have hsum_eq : (∑ _m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊,
        2 : ℕ)
        = 2 * (Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hIcc_r : ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card : ℝ)
        ≤ (q : ℝ) ^ ((1 : ℝ) / 10) + 2 := hIccbound q hq1
    have hqp_le : (q : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / 11) := hq_pow_le q hqY
    have hchain : ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
          (fun m => {q * m, q * m + 1})).card
        ≤ 2 * (Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card := by
      calc ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
              (fun m => {q * m, q * m + 1})).card
          ≤ ∑ m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊,
              ({q * m, q * m + 1} : Finset ℕ).card := hbiUnion_le
        _ ≤ ∑ _m ∈ Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊, 2 := hsum_le
        _ = 2 * (Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card := hsum_eq
    have hchainR : (((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
          (fun m => {q * m, q * m + 1})).card : ℝ)
        ≤ 2 * ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).card : ℝ) := by
      exact_mod_cast hchain
    nlinarith [hchainR, hIcc_r, hqp_le, hX111]
  -- Sum the uniform per-`q` bound over the prime powers `q ≤ Y`.
  have hF_le : (F.card : ℝ)
      ≤ (((Finset.Icc 1 Y).filter (fun q => IsPrimePow q)).card : ℝ) * (8 * (X : ℝ) ^ ((1 : ℝ) / 11)) := by
    have step1 : F.card
        ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
            ((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
              (fun m => {q * m, q * m + 1})).card := by
      rw [hFdef]; exact Finset.card_biUnion_le
    have step1R : (F.card : ℝ)
        ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
            (((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
              (fun m => {q * m, q * m + 1})).card : ℝ) := by
      exact_mod_cast step1
    have step2 : (∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
        (((Finset.Icc ⌈(q : ℝ) ^ ((1 : ℝ) / 10)⌉₊ ⌊2 * (q : ℝ) ^ ((1 : ℝ) / 10)⌋₊).biUnion
          (fun m => {q * m, q * m + 1})).card : ℝ))
        ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (8 * (X : ℝ) ^ ((1 : ℝ) / 11)) :=
      Finset.sum_le_sum hinner_le
    have step3 : (∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (8 * (X : ℝ) ^ ((1 : ℝ) / 11)))
        = (((Finset.Icc 1 Y).filter (fun q => IsPrimePow q)).card : ℝ) * (8 * (X : ℝ) ^ ((1 : ℝ) / 11)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith [step1R, step2, step3]
  have hFcard_le : (F.card : ℝ) ≤ Cpp * (Y : ℝ) / Real.log Y * (8 * (X : ℝ) ^ ((1 : ℝ) / 11)) := by
    refine hF_le.trans ?_
    exact mul_le_mul_of_nonneg_right (hCpp Y hYge2) (by positivity)
  have hncard_le : ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) ≤ (F.card : ℝ) := by
    have hle : (Pstar L ∩ Set.Icc 1 X).ncard ≤ F.card := by
      have h := Set.ncard_le_ncard hsub
      rwa [Set.ncard_coe_finset] at h
    exact_mod_cast hle
  -- Final analytic estimate: `Cpp Y / log Y · 8 X^(1/11) ≤ 20 Cpp X / log X`.
  have hXrpow_sum : (X : ℝ) ^ ((10 : ℝ) / 11) * (X : ℝ) ^ ((1 : ℝ) / 11) = (X : ℝ) := by
    rw [← Real.rpow_add hXpos, show (10 : ℝ) / 11 + (1 : ℝ) / 11 = 1 by norm_num, Real.rpow_one]
  have hcore_num : 8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11) ≤ 16 * (X : ℝ) := by
    calc 8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11)
        ≤ 8 * (2 * (X : ℝ) ^ ((10 : ℝ) / 11)) * (X : ℝ) ^ ((1 : ℝ) / 11) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hYle_real (by norm_num)
      _ = 16 * ((X : ℝ) ^ ((10 : ℝ) / 11) * (X : ℝ) ^ ((1 : ℝ) / 11)) := by ring
      _ = 16 * (X : ℝ) := by rw [hXrpow_sum]
  have hcore : 8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11) * Real.log X ≤ 20 * (X : ℝ) * Real.log Y := by
    have h1 : 8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11) * Real.log X ≤ 16 * (X : ℝ) * Real.log X :=
      mul_le_mul_of_nonneg_right hcore_num hlogXpos.le
    have h3 : 16 * (X : ℝ) * Real.log X ≤ 20 * (X : ℝ) * ((10 : ℝ) / 11 * Real.log X) := by
      nlinarith [hXpos, hlogXpos]
    have h4 : 20 * (X : ℝ) * ((10 : ℝ) / 11 * Real.log X) ≤ 20 * (X : ℝ) * Real.log Y :=
      mul_le_mul_of_nonneg_left hYlog_ge (by positivity)
    linarith
  have hfinal_core : 8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11) / Real.log Y ≤ 20 * (X : ℝ) / Real.log X := by
    rw [div_le_div_iff₀ hYlogpos hlogXpos]
    linarith [hcore]
  have hfinal : Cpp * (Y : ℝ) / Real.log Y * (8 * (X : ℝ) ^ ((1 : ℝ) / 11))
      ≤ 20 * Cpp * (X : ℝ) / Real.log X := by
    have heq1 : Cpp * (Y : ℝ) / Real.log Y * (8 * (X : ℝ) ^ ((1 : ℝ) / 11))
        = Cpp * (8 * (Y : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 11) / Real.log Y) := by ring
    have heq2 : 20 * Cpp * (X : ℝ) / Real.log X = Cpp * (20 * (X : ℝ) / Real.log X) := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hfinal_core hCppnn
  linarith [hncard_le, hFcard_le, hfinal]

/-- Asymptotic domination: for `e1 < e2`, `q ^ e1 ≤ ε * q ^ e2` once `q` is large enough
(depending on `e1, e2, ε`). -/
theorem rpow_dominated (e1 e2 : ℝ) (he : e1 < e2) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ q : ℝ, Q₀ ≤ q → q ^ e1 ≤ ε * q ^ e2 := by
  set d : ℝ := e2 - e1 with hddef
  have hdpos : 0 < d := by rw [hddef]; linarith
  set Q₀ : ℝ := (1 / ε) ^ (1 / d) with hQ0def
  have hQ0pos : 0 < Q₀ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Q₀, hQ0pos, fun q hq => ?_⟩
  have hqpos : 0 < q := lt_of_lt_of_le hQ0pos hq
  have hQ0d : Q₀ ^ d = 1 / ε := by
    rw [hQ0def, ← Real.rpow_mul (by positivity), show (1 : ℝ) / d * d = 1 by field_simp,
      Real.rpow_one]
  have hqd_ge : Q₀ ^ d ≤ q ^ d := Real.rpow_le_rpow hQ0pos.le hq hdpos.le
  rw [hQ0d] at hqd_ge
  have hqdpos : 0 < q ^ d := Real.rpow_pos_of_pos hqpos d
  have hinv : 1 / (q ^ d) ≤ 1 / (1 / ε) := one_div_le_one_div_of_le (by positivity) hqd_ge
  rw [one_div_one_div] at hinv
  have hqnegd : q ^ (-d) ≤ ε := by
    rw [Real.rpow_neg hqpos.le, inv_eq_one_div]; exact hinv
  have heq : q ^ e1 = q ^ e2 * q ^ (-d) := by
    rw [← Real.rpow_add hqpos, hddef]
    congr 1
    ring
  rw [heq]
  have hq2nn : (0:ℝ) ≤ q ^ e2 := Real.rpow_nonneg hqpos.le _
  calc q ^ e2 * q ^ (-d) ≤ q ^ e2 * ε := mul_le_mul_of_nonneg_left hqnegd hq2nn
    _ = ε * q ^ e2 := mul_comm _ _

/-- Real cast of truncated nat subtraction is always at least the naive real difference. -/
theorem nat_sub_cast_ge (a b : ℕ) : (b : ℝ) + 1 - (a : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by
  by_cases h : a ≤ b + 1
  · rw [Nat.cast_sub h]; push_cast; linarith
  · push Not at h
    have hz : b + 1 - a = 0 := by omega
    rw [hz]
    have hlt : (a : ℝ) > (b : ℝ) + 1 := by exact_mod_cast h
    push_cast
    linarith

/-- The number of elements of `Cand` within (symmetric) nat-distance `r` of some point of `S`
is at most `(2r+1) * S.card`. -/
theorem card_near_le (Cand S : Finset ℕ) (r : ℕ) :
    (Cand.filter (fun a => ∃ n ∈ S, a ≤ n + r ∧ n ≤ a + r)).card ≤ (2 * r + 1) * S.card := by
  classical
  have hsub : (Cand.filter (fun a => ∃ n ∈ S, a ≤ n + r ∧ n ≤ a + r))
      ⊆ S.biUnion (fun n => Finset.Icc (n - r) (n + r)) := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨_, n, hnS, ha1, ha2⟩ := ha
    exact Finset.mem_biUnion.mpr ⟨n, hnS, Finset.mem_Icc.mpr ⟨by omega, ha1⟩⟩
  calc (Cand.filter (fun a => ∃ n ∈ S, a ≤ n + r ∧ n ≤ a + r)).card
      ≤ (S.biUnion (fun n => Finset.Icc (n - r) (n + r))).card := Finset.card_le_card hsub
    _ ≤ ∑ n ∈ S, (Finset.Icc (n - r) (n + r)).card := Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ S, (2 * r + 1) := by
        apply Finset.sum_le_sum
        intro n _
        rw [Nat.card_Icc]
        omega
    _ = (2 * r + 1) * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- For fixed exponent `e > 0`, `q ^ e` eventually exceeds any target real `X₀`. -/
theorem exists_ge_rpow_ge (X₀ : ℝ) (e : ℝ) (he : 0 < e) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ q : ℝ, Q ≤ q → X₀ ≤ q ^ e := by
  set M : ℝ := max X₀ 0 with hMdef
  have hMnn : 0 ≤ M := le_max_right _ _
  refine ⟨M ^ (1 / e) + 1, by positivity, fun q hq => ?_⟩
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq
  have h1 : M ^ (1 / e) ≤ q := by linarith
  have h2 : (M ^ (1 / e)) ^ e ≤ q ^ e :=
    Real.rpow_le_rpow (Real.rpow_nonneg hMnn _) h1 he.le
  have h3 : (M ^ (1 / e)) ^ e = M := by
    rw [← Real.rpow_mul hMnn, show (1 / e) * e = 1 by field_simp, Real.rpow_one]
  rw [h3] at h2
  have h4 : X₀ ≤ M := le_max_left _ _
  linarith

/-- `log q` eventually exceeds any target real `M`. -/
theorem exists_log_ge (M : ℝ) : ∃ Q : ℝ, 0 < Q ∧ ∀ q : ℝ, Q ≤ q → M ≤ Real.log q := by
  refine ⟨Real.exp M + 1, by positivity, fun q hq => ?_⟩
  have hqpos : 0 < q := by nlinarith [Real.exp_pos M]
  have h1 : Real.exp M ≤ q := by linarith
  exact (Real.le_log_iff_exp_le hqpos).mpr h1

/-- Real cast of `n - 1` is always at least the naive real difference. -/
theorem nat_sub_one_cast_ge (n : ℕ) : (n : ℝ) - 1 ≤ ((n - 1 : ℕ) : ℝ) := by
  by_cases h : 1 ≤ n
  · rw [Nat.cast_sub h]; norm_num
  · interval_cases n; norm_num

/-- The mathematical core of Lemma 5: for `q` a large enough prime power (larger than a fixed
threshold `Q₀`, independent of `L`), given that all earlier stages `Prev q'` (`q' < q`) have
cardinality at most `s q'`, there is a stage-`q` finset `T` of exactly `s q` pairs meeting all
the requirements of `AuxFamily.F` at `q`, separated both from `PstarPairs L` and from all
earlier stages. -/
theorem stage_exists :
    ∃ Q₀ : ℕ, ∀ L q : ℕ, L < q → Q₀ ≤ q → IsPrimePow q →
      ∀ Prev : ℕ → Finset ℕ, (∀ q' < q, (Prev q').card ≤ s q') →
      ∃ T : Finset ℕ,
        T.card = s q ∧
        (∀ a ∈ T, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
        (∀ a ∈ T, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
        (∀ a ∈ T, 4 ∣ a) ∧
        (∀ a ∈ T, Powersmooth (q / 2) a) ∧
        (∀ a ∈ T, Powersmooth (q / 2) (a + 1)) ∧
        (∀ a ∈ T, ∀ J ∈ PstarPairs L, Iv.Sep (Iv.pair a) J) ∧
        (∀ q' < q, ∀ a ∈ T, ∀ a' ∈ Prev q', Iv.Sep (Iv.pair a) (Iv.pair a')) := by
  classical
  obtain ⟨η, hηpos, X₀, hX₀⟩ := lemma4 (10 / 11) 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (1 / 1000) (by norm_num)
  obtain ⟨C1, hC1⟩ := Pstar_count
  set C1' : ℝ := max C1 0 + 1 with hC1'def
  have hC1'pos : 0 < C1' := by positivity
  have hC1le : ∀ L X : ℕ, 2 ≤ X → ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) ≤ C1' * X / Real.log X := by
    intro L X hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    have hmono : C1 * (X : ℝ) / Real.log X ≤ C1' * (X : ℝ) / Real.log X := by
      gcongr
      linarith [le_max_left C1 0]
    exact (hC1 L X hX).trans hmono
  -- Thresholds gathered from the various asymptotic facts we need.
  obtain ⟨Q1, hQ1pos, hQ1⟩ := exists_ge_rpow_ge X₀ ((11 : ℝ) / 10) (by norm_num)
  obtain ⟨Q2, hQ2pos, hQ2⟩ := exists_ge_rpow_ge (120 : ℝ) ((11 : ℝ) / 10) (by norm_num)
  obtain ⟨Q3, hQ3pos, hQ3⟩ :=
    rpow_dominated (1 - (11 / 10) * η) 1 (by linarith) (1 / 4) (by norm_num)
  obtain ⟨Q5, hQ5pos, hQ5⟩ := exists_log_ge (1500 * C1' / 1.1)
  obtain ⟨Q6, hQ6pos, hQ6⟩ :=
    rpow_dominated ((21 : ℝ) / 20) ((22 : ℝ) / 20) (by norm_num) (0.002) (by norm_num)
  obtain ⟨Q7, hQ7pos, hQ7⟩ :=
    rpow_dominated ((1 : ℝ) / 20) ((22 : ℝ) / 20) (by norm_num) (0.01) (by norm_num)
  set Q0real : ℝ := max (max (max Q1 Q2) (max Q3 Q5)) (max (max Q6 Q7) 4) with hQ0realdef
  refine ⟨⌈Q0real⌉₊ + 1, fun L q hLq hQq hqpp Prev hPrev => ?_⟩
  have hqRge : Q0real ≤ (q : ℝ) := by
    have h1 : Q0real ≤ (⌈Q0real⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Q0real⌉₊ + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQq
    push_cast at h2
    linarith
  have hQ1' : X₀ ≤ (q : ℝ) ^ ((11 : ℝ) / 10) := hQ1 q (by
    calc Q1 ≤ max Q1 Q2 := le_max_left _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_left _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ2' : (120 : ℝ) ≤ (q : ℝ) ^ ((11 : ℝ) / 10) := hQ2 q (by
    calc Q2 ≤ max Q1 Q2 := le_max_right _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_left _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ3' : (q:ℝ) ^ (1 - (11 / 10) * η) ≤ (1 / 4) * (q:ℝ) ^ (1:ℝ) := hQ3 q (by
    calc Q3 ≤ max Q3 Q5 := le_max_left _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_right _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ5' : (1500 * C1' / 1.1 : ℝ) ≤ Real.log q := hQ5 q (by
    calc Q5 ≤ max Q3 Q5 := le_max_right _ _
    _ ≤ max (max Q1 Q2) (max Q3 Q5) := le_max_right _ _
    _ ≤ Q0real := le_max_left _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ6' : (q:ℝ) ^ ((21:ℝ)/20) ≤ 0.002 * (q:ℝ) ^ ((22:ℝ)/20) := hQ6 q (by
    calc Q6 ≤ max Q6 Q7 := le_max_left _ _
    _ ≤ max (max Q6 Q7) 4 := le_max_left _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge)
  have hQ7' : (q:ℝ) ^ ((1:ℝ)/20) ≤ 0.01 * (q:ℝ) ^ ((22:ℝ)/20) := hQ7 q (by
    calc Q7 ≤ max Q6 Q7 := le_max_right _ _
    _ ≤ max (max Q6 Q7) 4 := le_max_left _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge)
  have hqge4 : (4:ℝ) ≤ (q:ℝ) := by
    calc (4:ℝ) ≤ max (max Q6 Q7) 4 := le_max_right _ _
    _ ≤ Q0real := le_max_right _ _
    _ ≤ (q:ℝ) := hqRge
  have hqRpos : (0:ℝ) < (q:ℝ) := by linarith
  set X : ℝ := (q:ℝ) ^ ((11:ℝ)/10) with hXdef
  have hXpos : 0 < X := Real.rpow_pos_of_pos hqRpos _
  have hXge120 : (120:ℝ) ≤ X := hQ2'
  -- Window bound for `y := q/2` inside `[X^(θ-η), X^(θ+η)]`.
  have hqdiv2_ge : (q:ℝ)/2 - 1 ≤ ((q/2:ℕ):ℝ) := by
    have hkey : 2*(q/2) + 1 ≥ q := by omega
    have hcast : (q:ℝ) ≤ 2*((q/2:ℕ):ℝ) + 1 := by exact_mod_cast hkey
    linarith
  have hqdiv2_le : ((q/2:ℕ):ℝ) ≤ (q:ℝ)/2 := Nat.cast_div_le
  have hXthetalo_eq : X ^ ((10:ℝ)/11 - η) = (q:ℝ) ^ (1 - (11/10)*η) := by
    rw [hXdef, ← Real.rpow_mul hqRpos.le]
    congr 1
    ring
  have hXthetahi_eq : X ^ ((10:ℝ)/11 + η) = (q:ℝ) ^ (1 + (11/10)*η) := by
    rw [hXdef, ← Real.rpow_mul hqRpos.le]
    congr 1
    ring
  have hwindow_lo : X ^ ((10:ℝ)/11 - η) ≤ ((q/2:ℕ):ℝ) := by
    rw [hXthetalo_eq]
    have hQ3copy := hQ3'
    rw [Real.rpow_one] at hQ3copy
    have hstep : (1/4:ℝ)*(q:ℝ) ≤ (q:ℝ)/2 - 1 := by linarith [hqge4]
    calc (q:ℝ) ^ (1 - (11/10)*η) ≤ (1/4)*(q:ℝ) := hQ3copy
      _ ≤ (q:ℝ)/2 - 1 := hstep
      _ ≤ ((q/2:ℕ):ℝ) := hqdiv2_ge
  have hwindow_hi : ((q/2:ℕ):ℝ) ≤ X ^ ((10:ℝ)/11 + η) := by
    rw [hXthetahi_eq]
    have hexp : (1:ℝ) ≤ 1 + (11/10)*η := by nlinarith [hηpos]
    have hbase : (1:ℝ) ≤ (q:ℝ) := by linarith [hqge4]
    have h1 : (q:ℝ) ≤ (q:ℝ) ^ (1 + (11/10)*η) := by
      calc (q:ℝ) = (q:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ (q:ℝ)^(1+(11/10)*η) := Real.rpow_le_rpow_of_exponent_le hbase hexp
    linarith [hqdiv2_le]
  -- The candidate range `[A, B]` and the multiples-of-4 candidates `Cand`.
  set A : ℕ := ⌈X⌉₊ with hAdef
  set B : ℕ := ⌊2*X⌋₊ with hBdef
  have hA_ge : X ≤ (A:ℝ) := Nat.le_ceil _
  have hA_lt : (A:ℝ) < X + 1 := Nat.ceil_lt_add_one hXpos.le
  have hB_le : (B:ℝ) ≤ 2*X := Nat.floor_le (by positivity)
  have hB_gt : 2*X < (B:ℝ) + 1 := Nat.lt_floor_add_one _
  have hBge200 : (200:ℝ) ≤ (B:ℝ) := by nlinarith [hB_gt, hXge120]
  set k1 : ℕ := ⌈(A:ℝ)/4⌉₊ with hk1def
  set k2 : ℕ := ⌊((B-1:ℕ):ℝ)/4⌋₊ with hk2def
  have hk1_lt : (k1:ℝ) < (A:ℝ)/4 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk1_ge : (A:ℝ)/4 ≤ (k1:ℝ) := Nat.le_ceil _
  have hk2_gt : ((B-1:ℕ):ℝ)/4 - 1 < (k2:ℝ) := by
    have h := Nat.lt_floor_add_one (((B-1:ℕ):ℝ)/4)
    linarith
  have hk2_le : (k2:ℝ) ≤ ((B-1:ℕ):ℝ)/4 := Nat.floor_le (by positivity)
  set Cand : Finset ℕ := (Finset.Icc k1 k2).image (fun k => 4*k) with hCanddef
  have hinj4 : Function.Injective (fun k : ℕ => 4 * k) := by
    intro a b h
    simp only at h
    omega
  have hCand_card : Cand.card = k2 + 1 - k1 := by
    rw [hCanddef, Finset.card_image_of_injective _ hinj4, Nat.card_Icc]
  have hCand_card_real : (Cand.card:ℝ) ≥ X/4 - 2 := by
    rw [hCand_card]
    have h1 := nat_sub_cast_ge k1 k2
    have hBsub1 := nat_sub_one_cast_ge B
    have e1 : (k2:ℝ) > X/2 - 3/2 := by nlinarith [hk2_gt, hBsub1, hB_gt]
    have e2 : (k1:ℝ) < X/4 + 5/4 := by nlinarith [hk1_lt, hA_lt]
    nlinarith [h1, e1, e2]
  have hCandsub : ∀ a ∈ Cand, a + 1 ≤ B ∧ A ≤ a ∧ 4 ∣ a := by
    intro a ha
    rw [hCanddef, Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [Finset.mem_Icc] at hk
    have h4k2 : 4*k2 ≤ B - 1 := by
      have hr : (4*k2:ℝ) ≤ ((B-1:ℕ):ℝ) := by nlinarith [hk2_le]
      exact_mod_cast hr
    have hAk1 : A ≤ 4*k1 := by
      have hr : (A:ℝ) ≤ 4*(k1:ℝ) := by nlinarith [hk1_ge]
      exact_mod_cast hr
    refine ⟨?_, ?_, ⟨k, rfl⟩⟩
    · have hBge : (200:ℕ) ≤ B := by exact_mod_cast hBge200
      omega
    · omega
  set y : ℕ := q/2 with hydef
  -- Non-`y`-powersmooth candidates, via `lemma4`.
  have hNeq : notSmooth y 1 2 X = (Finset.Icc A B).filter (fun n => ¬ Powersmooth y n) := by
    unfold notSmooth
    rw [one_mul, ← hAdef, ← hBdef]
  have hNcard : ((notSmooth y 1 2 X).card : ℝ) ≤ (Real.log (11/10) + 1/1000) * X := by
    have hraw := hX₀ X hQ1' y hwindow_lo hwindow_hi
    have heq : ((2:ℝ)-1)*Real.log (1/(10/11)) + 1/1000 = Real.log ((11:ℝ)/10) + 1/1000 := by
      norm_num
    rwa [heq] at hraw
  have hlog1110 : Real.log ((11:ℝ)/10) ≤ 1/10 := by
    have h0 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/10 by norm_num)
    linarith [h0]
  set BadSmooth : Finset ℕ := Cand.filter (fun a => ¬ Powersmooth y a ∨ ¬ Powersmooth y (a+1))
    with hBadSmoothdef
  have hBadSmooth_le : BadSmooth.card ≤ 2 * (notSmooth y 1 2 X).card := by
    have hsub1 : Cand.filter (fun a => ¬ Powersmooth y a) ⊆ notSmooth y 1 2 X := by
      intro a ha
      simp only [Finset.mem_filter] at ha
      obtain ⟨haC, hns⟩ := ha
      obtain ⟨ha1, ha2, _⟩ := hCandsub a haC
      rw [hNeq]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ha2, by omega⟩, hns⟩
    have hsub2 : (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card ≤ (notSmooth y 1 2 X).card := by
      have hmap : (Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)
          ⊆ notSmooth y 1 2 X := by
        intro n hn
        simp only [Finset.mem_image, Finset.mem_filter] at hn
        obtain ⟨a, ⟨haC, hns⟩, rfl⟩ := hn
        obtain ⟨ha1, ha2, _⟩ := hCandsub a haC
        rw [hNeq]
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, ha1⟩, hns⟩
      have hinjsucc : Function.Injective (fun a : ℕ => a + 1) := by
        intro a b h; simp only at h; omega
      have hcardeq : ((Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)).card
          = (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card :=
        Finset.card_image_of_injective _ hinjsucc
      calc (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card
          = ((Cand.filter (fun a => ¬ Powersmooth y (a+1))).image (·+1)).card := hcardeq.symm
        _ ≤ (notSmooth y 1 2 X).card := Finset.card_le_card hmap
    have hBadsub : BadSmooth ⊆ (Cand.filter (fun a => ¬ Powersmooth y a))
        ∪ (Cand.filter (fun a => ¬ Powersmooth y (a+1))) := by
      intro a ha
      rw [hBadSmoothdef, Finset.mem_filter] at ha
      obtain ⟨haC, hor⟩ := ha
      rcases hor with h|h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haC, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haC, h⟩)
    calc BadSmooth.card
        ≤ ((Cand.filter (fun a => ¬ Powersmooth y a))
            ∪ (Cand.filter (fun a => ¬ Powersmooth y (a+1)))).card := Finset.card_le_card hBadsub
      _ ≤ (Cand.filter (fun a => ¬ Powersmooth y a)).card
          + (Cand.filter (fun a => ¬ Powersmooth y (a+1))).card := Finset.card_union_le _ _
      _ ≤ (notSmooth y 1 2 X).card + (notSmooth y 1 2 X).card :=
          Nat.add_le_add (Finset.card_le_card hsub1) hsub2
      _ = 2 * (notSmooth y 1 2 X).card := by ring
  have hBadSmooth_realle : (BadSmooth.card:ℝ) ≤ 0.202 * X := by
    have h1 : (BadSmooth.card:ℝ) ≤ 2*((notSmooth y 1 2 X).card:ℝ) := by exact_mod_cast hBadSmooth_le
    nlinarith [hNcard, hlog1110, h1]
  -- Candidates near a possible correction pair (`Pstar L`).
  have hfinPstar : (Pstar L ∩ Set.Icc 1 (B+2)).Finite :=
    Set.Finite.subset (Set.finite_Icc 1 (B+2)) Set.inter_subset_right
  set PstarFin : Finset ℕ := hfinPstar.toFinset with hPstarFindef
  have hPstarFin_card : (PstarFin.card:ℝ) ≤ C1' * (B+2:ℕ) / Real.log (B+2:ℕ) := by
    have heq : PstarFin.card = (Pstar L ∩ Set.Icc 1 (B+2)).ncard := by
      rw [hPstarFindef, ← Set.ncard_eq_toFinset_card _ hfinPstar]
    rw [heq]
    exact hC1le L (B+2) (by omega)
  set BadPstar : Finset ℕ := Cand.filter (fun a => ∃ n ∈ PstarFin, a ≤ n+2 ∧ n ≤ a+2)
    with hBadPstardef
  have hBadPstar_le : BadPstar.card ≤ 5 * PstarFin.card := by
    rw [hBadPstardef]
    have h := card_near_le Cand PstarFin 2
    omega
  have hlogqpos : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith [hqge4])
  have hBadPstar_realle : (BadPstar.card:ℝ) ≤ 0.01 * X := by
    have h1 : (BadPstar.card:ℝ) ≤ 5*(PstarFin.card:ℝ) := by exact_mod_cast hBadPstar_le
    have hB2X : (((B:ℕ)+2:ℕ):ℝ) ≤ 3*X := by push_cast; nlinarith [hB_le, hXge120]
    have hB2gtX : X < (((B:ℕ)+2:ℕ):ℝ) := by push_cast; nlinarith [hB_gt]
    have hlogge : (1.1:ℝ)*Real.log q ≤ Real.log (((B:ℕ)+2:ℕ):ℝ) := by
      have hlt : Real.log X < Real.log (((B:ℕ)+2:ℕ):ℝ) := Real.log_lt_log hXpos hB2gtX
      have hlogXeq : Real.log X = 1.1 * Real.log q := by
        rw [hXdef, Real.log_rpow hqRpos]; norm_num
      linarith [hlt, hlogXeq]
    have hQ5'' : (1500*C1':ℝ) ≤ Real.log q * 1.1 :=
      (div_le_iff₀ (by norm_num : (0:ℝ) < 1.1)).mp hQ5'
    have hlogbig : (1500*C1':ℝ) ≤ Real.log (((B:ℕ)+2:ℕ):ℝ) := by
      nlinarith [hlogge, hQ5'']
    have hlogpos2 : 0 < Real.log (((B:ℕ)+2:ℕ):ℝ) := by linarith [hlogge, hlogqpos]
    have hfrac_le : (((B:ℕ)+2:ℕ):ℝ)/Real.log (((B:ℕ)+2:ℕ):ℝ) ≤ 3*X/(1500*C1') := by
      gcongr
    have h5C1frac : 5*C1'*((((B:ℕ)+2:ℕ):ℝ)/Real.log (((B:ℕ)+2:ℕ):ℝ)) ≤ 5*C1'*(3*X/(1500*C1')) :=
      mul_le_mul_of_nonneg_left hfrac_le (by positivity)
    have hsimpl : 5*C1'*(3*X/(1500*C1')) = 0.01*X := by
      field_simp
      ring
    have hPstarFrac_le : 5*(PstarFin.card:ℝ) ≤ 0.01*X := by
      calc 5*(PstarFin.card:ℝ)
          ≤ 5*(C1'*(((B:ℕ)+2:ℕ):ℝ)/Real.log (((B:ℕ)+2:ℕ):ℝ)) :=
            mul_le_mul_of_nonneg_left hPstarFin_card (by norm_num)
        _ = 5*C1'*((((B:ℕ)+2:ℕ):ℝ)/Real.log (((B:ℕ)+2:ℕ):ℝ)) := by ring
        _ ≤ 5*C1'*(3*X/(1500*C1')) := h5C1frac
        _ = 0.01*X := hsimpl
    linarith [h1, hPstarFrac_le]
  -- Candidates near an earlier reserved stage.
  set ReservedFin : Finset ℕ := (Finset.range q).biUnion (fun q' => Prev q') with hResFindef
  have hResFin_card_le : (ReservedFin.card:ℝ) ≤ (q:ℝ)^((21:ℝ)/20) := by
    have hstep0 : ReservedFin.card ≤ ∑ q' ∈ Finset.range q, (Prev q').card := by
      rw [hResFindef]; exact Finset.card_biUnion_le
    have hstep1 : (ReservedFin.card:ℝ) ≤ ∑ q' ∈ Finset.range q, ((Prev q').card:ℝ) := by
      exact_mod_cast hstep0
    have hstep2 : (∑ q' ∈ Finset.range q, ((Prev q').card:ℝ))
        ≤ ∑ q' ∈ Finset.range q, (s q' : ℝ) := by
      apply Finset.sum_le_sum
      intro q' hq'
      exact_mod_cast hPrev q' (Finset.mem_range.mp hq')
    have hstep3 : (∑ q' ∈ Finset.range q, (s q':ℝ))
        ≤ ∑ _q' ∈ Finset.range q, (q:ℝ)^((1:ℝ)/20) := by
      apply Finset.sum_le_sum
      intro q' hq'
      have hq'q : q' < q := Finset.mem_range.mp hq'
      have h1 : (s q':ℝ) ≤ (q':ℝ)^((1:ℝ)/20) := Nat.floor_le (by positivity)
      have h2 : (q':ℝ)^((1:ℝ)/20) ≤ (q:ℝ)^((1:ℝ)/20) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq'q.le) (by norm_num)
      linarith
    have hstep4 : (∑ _q' ∈ Finset.range q, (q:ℝ)^((1:ℝ)/20)) = (q:ℝ)*(q:ℝ)^((1:ℝ)/20) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep5 : (q:ℝ)^((21:ℝ)/20) = (q:ℝ)*(q:ℝ)^((1:ℝ)/20) := by
      rw [show (21:ℝ)/20 = 1 + (1:ℝ)/20 by norm_num, Real.rpow_add hqRpos, Real.rpow_one]
    linarith [hstep1, hstep2, hstep3, hstep4, hstep5]
  set BadReserved : Finset ℕ := Cand.filter (fun a => ∃ n ∈ ReservedFin, a ≤ n+2 ∧ n ≤ a+2)
    with hBadReserveddef
  have hBadReserved_le : BadReserved.card ≤ 5 * ReservedFin.card := by
    rw [hBadReserveddef]
    have h := card_near_le Cand ReservedFin 2
    omega
  have hBadReserved_realle : (BadReserved.card:ℝ) ≤ 0.01*X := by
    have h1 : (BadReserved.card:ℝ) ≤ 5*(ReservedFin.card:ℝ) := by exact_mod_cast hBadReserved_le
    have hXeq22 : X = (q:ℝ)^((22:ℝ)/20) := by rw [hXdef]; norm_num
    have h2 : (ReservedFin.card:ℝ) ≤ 0.002*X := by
      calc (ReservedFin.card:ℝ) ≤ (q:ℝ)^((21:ℝ)/20) := hResFin_card_le
        _ ≤ 0.002*(q:ℝ)^((22:ℝ)/20) := hQ6'
        _ = 0.002*X := by rw [hXeq22]
    linarith [h1, h2]
  have hsq_le : (s q:ℝ) ≤ 0.01*X := by
    have hXeq22 : X = (q:ℝ)^((22:ℝ)/20) := by rw [hXdef]; norm_num
    have h1 : (s q:ℝ) ≤ (q:ℝ)^((1:ℝ)/20) := Nat.floor_le (by positivity)
    calc (s q:ℝ) ≤ (q:ℝ)^((1:ℝ)/20) := h1
      _ ≤ 0.01*(q:ℝ)^((22:ℝ)/20) := hQ7'
      _ = 0.01*X := by rw [hXeq22]
  -- Assemble the surviving candidates and extract a subfamily of size `s q`.
  set GoodCand : Finset ℕ := Cand \ (BadSmooth ∪ BadPstar ∪ BadReserved) with hGoodCanddef
  have hGoodCand_ge : Cand.card ≤ GoodCand.card + (BadSmooth ∪ BadPstar ∪ BadReserved).card := by
    rw [hGoodCanddef]; exact Finset.card_le_card_sdiff_add_card
  have hUnion_le : (BadSmooth ∪ BadPstar ∪ BadReserved).card
      ≤ BadSmooth.card + BadPstar.card + BadReserved.card := by
    calc (BadSmooth ∪ BadPstar ∪ BadReserved).card
        ≤ (BadSmooth ∪ BadPstar).card + BadReserved.card := Finset.card_union_le _ _
      _ ≤ (BadSmooth.card + BadPstar.card) + BadReserved.card := by
          have := Finset.card_union_le BadSmooth BadPstar
          omega
      _ = BadSmooth.card + BadPstar.card + BadReserved.card := by ring
  have hGoodCand_realge : (GoodCand.card:ℝ) ≥ X/100 := by
    have h1 : (Cand.card:ℝ) ≤ (GoodCand.card:ℝ) + ((BadSmooth ∪ BadPstar ∪ BadReserved).card:ℝ) := by
      exact_mod_cast hGoodCand_ge
    have h2 : ((BadSmooth ∪ BadPstar ∪ BadReserved).card:ℝ)
        ≤ (BadSmooth.card:ℝ)+(BadPstar.card:ℝ)+(BadReserved.card:ℝ) := by
      exact_mod_cast hUnion_le
    nlinarith [hCand_card_real, h1, h2, hBadSmooth_realle, hBadPstar_realle, hBadReserved_realle,
      hXge120]
  have hGoodCand_ge_sq : s q ≤ GoodCand.card := by
    have h1 : (s q:ℝ) ≤ (GoodCand.card:ℝ) := by linarith [hGoodCand_realge, hsq_le]
    exact_mod_cast h1
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hGoodCand_ge_sq
  have hGoodCand_mem : ∀ a ∈ GoodCand, a ∈ Cand ∧ a ∉ BadSmooth ∧ a ∉ BadPstar ∧ a ∉ BadReserved := by
    intro a ha
    rw [hGoodCanddef] at ha
    simp only [Finset.mem_sdiff, Finset.mem_union] at ha
    tauto
  refine ⟨T, hTcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨_, ha2, _⟩ := hCandsub a haC
    calc X ≤ (A:ℝ) := hA_ge
      _ ≤ (a:ℝ) := by exact_mod_cast ha2
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨ha1, _, _⟩ := hCandsub a haC
    calc ((a+1:ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast ha1
      _ ≤ 2*X := hB_le
  · intro a ha
    obtain ⟨haC, _, _, _⟩ := hGoodCand_mem a (hTsub ha)
    exact (hCandsub a haC).2.2
  · intro a ha
    obtain ⟨haC, hBS, _, _⟩ := hGoodCand_mem a (hTsub ha)
    by_contra hns
    apply hBS
    rw [hBadSmoothdef]
    exact Finset.mem_filter.mpr ⟨haC, Or.inl hns⟩
  · intro a ha
    obtain ⟨haC, hBS, _, _⟩ := hGoodCand_mem a (hTsub ha)
    by_contra hns
    apply hBS
    rw [hBadSmoothdef]
    exact Finset.mem_filter.mpr ⟨haC, Or.inr hns⟩
  · intro a ha J hJ
    obtain ⟨haC, _, hBP, _⟩ := hGoodCand_mem a (hTsub ha)
    obtain ⟨ha1, _, _⟩ := hCandsub a haC
    obtain ⟨q', m', hq'pp, hLq', hm1, hm2, hJeq⟩ := hJ
    subst hJeq
    set n : ℕ := q' * m' with hndef
    have hq'pos : 0 < q' := hq'pp.pos
    have hq'Rpos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'pos
    have hm'ge1 : 1 ≤ m' := by
      have h1 : (1:ℝ) ≤ (q':ℝ)^((1:ℝ)/10) := Real.one_le_rpow (by exact_mod_cast hq'pos) (by norm_num)
      have h2 : (1:ℝ) ≤ (m':ℝ) := le_trans h1 hm1
      exact_mod_cast h2
    have hnge1 : 1 ≤ n := by rw [hndef]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    by_cases hcase : n ≤ B + 2
    · have hnPstar : n ∈ Pstar L := ⟨q', m', hq'pp, hLq', hm1, hm2, Or.inl rfl⟩
      have hnPstarFin : n ∈ PstarFin := by
        rw [hPstarFindef, Set.Finite.mem_toFinset]
        exact ⟨hnPstar, Set.mem_Icc.mpr ⟨hnge1, hcase⟩⟩
      have hnnotnear : ¬(a ≤ n+2 ∧ n ≤ a+2) := by
        intro hcon
        apply hBP
        rw [hBadPstardef]
        exact Finset.mem_filter.mpr ⟨haC, n, hnPstarFin, hcon⟩
      unfold Iv.Sep Iv.pair
      simp only
      omega
    · push Not at hcase
      unfold Iv.Sep Iv.pair
      simp only
      omega
  · intro q' hq'lt a ha a' ha'
    obtain ⟨haC, _, _, hBR⟩ := hGoodCand_mem a (hTsub ha)
    have ha'Res : a' ∈ ReservedFin := by
      rw [hResFindef]
      exact Finset.mem_biUnion.mpr ⟨q', Finset.mem_range.mpr hq'lt, ha'⟩
    have hnotnear : ¬(a ≤ a'+2 ∧ a' ≤ a+2) := by
      intro hcon
      apply hBR
      rw [hBadReserveddef]
      exact Finset.mem_filter.mpr ⟨haC, a', ha'Res, hcon⟩
    unfold Iv.Sep Iv.pair
    simp only
    omega

/-- Truncating a finset to satisfy a cardinality cap is a no-op exactly when the cap already
holds, and always yields a finset within the cap. -/
theorem truncate_card_le {α : Type*} [DecidableEq α] (T : Finset α) (m : ℕ) :
    (if T.card ≤ m then T else (∅ : Finset α)).card ≤ m := by
  split
  · assumption
  · simp

/-- A fixed threshold witnessing `stage_exists`, used uniformly for every cutoff `L`. -/
noncomputable def stageQ₀ : ℕ := stage_exists.choose

theorem stageQ₀_spec : ∀ L q : ℕ, L < q → stageQ₀ ≤ q → IsPrimePow q →
    ∀ Prev : ℕ → Finset ℕ, (∀ q' < q, (Prev q').card ≤ s q') →
    ∃ T : Finset ℕ,
      T.card = s q ∧
      (∀ a ∈ T, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
      (∀ a ∈ T, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
      (∀ a ∈ T, 4 ∣ a) ∧
      (∀ a ∈ T, Powersmooth (q / 2) a) ∧
      (∀ a ∈ T, Powersmooth (q / 2) (a + 1)) ∧
      (∀ a ∈ T, ∀ J ∈ PstarPairs L, Iv.Sep (Iv.pair a) J) ∧
      (∀ q' < q, ∀ a ∈ T, ∀ a' ∈ Prev q', Iv.Sep (Iv.pair a) (Iv.pair a')) :=
  stage_exists.choose_spec

/-- The recursive construction of the auxiliary family: `Fconstr L q` processes prime powers
`q > max L stageQ₀` in increasing order, each stage choosing its finset via `stageQ₀_spec`
relative to (a safety-truncated copy of) all strictly earlier stages. -/
noncomputable def Fconstr (L : ℕ) (q : ℕ) : Finset ℕ :=
  Nat.strongRecOn q (fun q ih =>
    if h : IsPrimePow q ∧ L < q ∧ stageQ₀ ≤ q then
      Classical.choose (stageQ₀_spec L q h.2.1 h.2.2 h.1
        (fun q' => if hlt : q' < q then (if (ih q' hlt).card ≤ s q' then ih q' hlt else ∅) else ∅)
        (fun q' hq' => by
          rw [dite_eq_left_of_eq_true (eq_true hq')]
          exact truncate_card_le (ih q' hq') (s q')))
    else ∅)

theorem Fconstr_eq (L q : ℕ) :
    Fconstr L q =
      if h : IsPrimePow q ∧ L < q ∧ stageQ₀ ≤ q then
        Classical.choose (stageQ₀_spec L q h.2.1 h.2.2 h.1
          (fun q' => if _hlt : q' < q then
              (if (Fconstr L q').card ≤ s q' then Fconstr L q' else ∅) else ∅)
          (fun q' hq' => by
            rw [dite_eq_left_of_eq_true (eq_true hq')]
            exact truncate_card_le (Fconstr L q') (s q')))
      else ∅ := by
  conv_lhs => rw [Fconstr]
  exact WellFounded.fix_eq Nat.lt_wfRel.wf _ q

theorem Fconstr_card_le (L q : ℕ) : (Fconstr L q).card ≤ s q := by
  rw [Fconstr_eq]
  split
  · next h =>
    exact (Classical.choose_spec (stageQ₀_spec L q h.2.1 h.2.2 h.1
      (fun q' => if hlt : q' < q then (if (Fconstr L q').card ≤ s q' then Fconstr L q' else ∅) else ∅)
      (fun q' hq' => by
        rw [dite_eq_left_of_eq_true (eq_true hq')]
        exact truncate_card_le (Fconstr L q') (s q')))).1.le
  · simp

/-- The main specification of `Fconstr L q` at a valid stage. -/
theorem Fconstr_spec (L q : ℕ) (hqpp : IsPrimePow q) (hLq : L < q) (hQq : stageQ₀ ≤ q) :
    (Fconstr L q).card = s q ∧
    (∀ a ∈ Fconstr L q, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a) ∧
    (∀ a ∈ Fconstr L q, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)) ∧
    (∀ a ∈ Fconstr L q, 4 ∣ a) ∧
    (∀ a ∈ Fconstr L q, Powersmooth (q / 2) a) ∧
    (∀ a ∈ Fconstr L q, Powersmooth (q / 2) (a + 1)) ∧
    (∀ a ∈ Fconstr L q, ∀ J ∈ PstarPairs L, Iv.Sep (Iv.pair a) J) ∧
    (∀ q' < q, ∀ a ∈ Fconstr L q, ∀ a' ∈ Fconstr L q', Iv.Sep (Iv.pair a) (Iv.pair a')) := by
  have hraw := Classical.choose_spec (stageQ₀_spec L q hLq hQq hqpp
    (fun q' => if hlt : q' < q then (if (Fconstr L q').card ≤ s q' then Fconstr L q' else ∅) else ∅)
    (fun q' hq' => by
      rw [dite_eq_left_of_eq_true (eq_true hq')]
      exact truncate_card_le (Fconstr L q') (s q')))
  have heq : Fconstr L q = Classical.choose (stageQ₀_spec L q hLq hQq hqpp
      (fun q' => if hlt : q' < q then (if (Fconstr L q').card ≤ s q' then Fconstr L q' else ∅) else ∅)
      (fun q' hq' => by
        rw [dite_eq_left_of_eq_true (eq_true hq')]
        exact truncate_card_le (Fconstr L q') (s q'))) := by
    rw [Fconstr_eq]
    rw [dite_eq_left_of_eq_true (eq_true (⟨hqpp, hLq, hQq⟩ : IsPrimePow q ∧ L < q ∧ stageQ₀ ≤ q))]
  rw [← heq] at hraw
  obtain ⟨hcard, hlower, hupper, hdvd, hsmoothlo, hsmoothhi, hsepcorr, hsepaux⟩ := hraw
  refine ⟨hcard, hlower, hupper, hdvd, hsmoothlo, hsmoothhi, hsepcorr, ?_⟩
  intro q' hq'lt a ha a' ha'
  have htrunc : (if hlt : q' < q then (if (Fconstr L q').card ≤ s q' then Fconstr L q' else ∅)
      else ∅) = Fconstr L q' := by
    rw [dite_eq_left_of_eq_true (eq_true hq'lt),
      ite_eq_left_of_eq_true _ _ (eq_true (Fconstr_card_le L q'))]
  rw [← htrunc] at ha'
  exact hsepaux q' hq'lt a ha a' ha'

/-- If `Fconstr L q` is nonempty, `q` must have already reached the threshold `stageQ₀`. -/
theorem Fconstr_mem_imp (L q a : ℕ) (_hqpp : IsPrimePow q) (_hLq : L < q) (ha : a ∈ Fconstr L q) :
    stageQ₀ ≤ q := by
  by_contra hQq
  have hempty : Fconstr L q = ∅ := by
    rw [Fconstr_eq, dite_eq_right_of_eq_false (eq_false (fun h => hQq h.2.2))]
  rw [hempty] at ha
  exact absurd ha (Finset.notMem_empty a)

/-- **(4.4)**-type bound for the constructed family: `|F* ∩ [1, X]| = O(X^(21/22))`. -/
theorem Fconstr_count (L : ℕ) :
    ∃ C : ℝ, ∀ X : ℕ, ((Fstar L (Fconstr L) ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * (X:ℝ)^((21:ℝ)/22) := by
  refine ⟨100, fun X => ?_⟩
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0
    simp
  have hXposR : (0:ℝ) < (X:ℝ) := by exact_mod_cast hXpos
  set Y : ℕ := ⌈(X:ℝ)^((10:ℝ)/11)⌉₊ with hYdef
  set FX : Finset ℕ := ((Finset.Icc 1 Y).filter (fun q => IsPrimePow q)).biUnion
      (fun q => (Fconstr L q).biUnion (fun a => ({a, a+1} : Finset ℕ))) with hFXdef
  have hsub : Fstar L (Fconstr L) ∩ Set.Icc 1 X ⊆ (FX : Set ℕ) := by
    rintro n ⟨⟨q, hqpp, hLq, a, ha, hn⟩, hn1, hnX⟩
    have hQq : stageQ₀ ≤ q := Fconstr_mem_imp L q a hqpp hLq ha
    have hlower := (Fconstr_spec L q hqpp hLq hQq).2.1 a ha
    have hqle : q ≤ Y := by
      have hqX : (q:ℝ)^((11:ℝ)/10) ≤ (X:ℝ) := by
        rcases hn with h | h
        · rw [h] at hnX; exact hlower.trans (by exact_mod_cast hnX)
        · rw [h] at hnX
          have hle1 : (a:ℝ) ≤ ((a+1:ℕ):ℝ) := by push_cast; linarith
          exact hlower.trans (hle1.trans (by exact_mod_cast hnX))
      have hqR : (q:ℝ) ≤ (X:ℝ)^((10:ℝ)/11) := by
        have h1 := Real.rpow_le_rpow (by positivity) hqX (by norm_num : (0:ℝ) ≤ (10:ℝ)/11)
        rwa [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (q:ℝ)),
          show (11:ℝ)/10*((10:ℝ)/11) = 1 by norm_num, Real.rpow_one] at h1
      exact_mod_cast hqR.trans (Nat.le_ceil _)
    have hqmem : q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hqpp.pos, hqle⟩, hqpp⟩
    rw [hFXdef]
    refine Finset.mem_biUnion.mpr ⟨q, hqmem, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    rcases hn with h | h <;> simp [h]
  have hncard_le : ((Fstar L (Fconstr L) ∩ Set.Icc 1 X).ncard:ℝ) ≤ (FX.card:ℝ) := by
    have hle : (Fstar L (Fconstr L) ∩ Set.Icc 1 X).ncard ≤ FX.card := by
      have h := Set.ncard_le_ncard hsub
      rwa [Set.ncard_coe_finset] at h
    exact_mod_cast hle
  have hstep1 : FX.card ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((Fconstr L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card := by
    rw [hFXdef]; exact Finset.card_biUnion_le
  have hstep2 : ∀ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((Fconstr L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card ≤ 2*(Fconstr L q).card := by
    intro q _
    calc ((Fconstr L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card
        ≤ ∑ a ∈ Fconstr L q, ({a,a+1}:Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Fconstr L q, 2 :=
          Finset.sum_le_sum (fun a _ => le_trans (Finset.card_insert_le _ _) (by simp))
      _ = 2*(Fconstr L q).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hstep3 : ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
      ((Fconstr L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card
      ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), 2*(Fconstr L q).card :=
    Finset.sum_le_sum hstep2
  have hstep5 : ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (Fconstr L q).card
      ≤ ∑ q ∈ (Finset.Icc 1 Y).filter IsPrimePow, s q :=
    Finset.sum_le_sum (fun q _ => Fconstr_card_le L q)
  have hstep6 : (∑ q ∈ (Finset.Icc 1 Y).filter IsPrimePow, (s q:ℕ) : ℝ) ≤ (Y:ℝ)^((21:ℝ)/20) := by
    have h := sum_rpow_le 0 Y
    simp only [zero_add] at h
    push_cast at h
    exact h
  have hFXcard_le : (FX.card:ℝ) ≤ 2 * (Y:ℝ)^((21:ℝ)/20) := by
    have hn : FX.card ≤ 2 * ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (Fconstr L q).card := by
      calc FX.card
          ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
              ((Fconstr L q).biUnion (fun a => ({a,a+1}:Finset ℕ))).card := hstep1
        _ ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), 2*(Fconstr L q).card := hstep3
        _ = 2 * ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (Fconstr L q).card := by
            rw [Finset.mul_sum]
    have hcast : (FX.card:ℝ) ≤ 2*(∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q),
        (Fconstr L q).card : ℝ) := by exact_mod_cast hn
    have hcast2 : (∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (Fconstr L q).card : ℝ)
        ≤ ∑ q ∈ (Finset.Icc 1 Y).filter (fun q => IsPrimePow q), (s q :ℝ) := by exact_mod_cast hstep5
    linarith [hcast, hcast2, hstep6]
  have hX1 : (1:ℝ) ≤ (X:ℝ)^((10:ℝ)/11) := Real.one_le_rpow (by exact_mod_cast hXpos) (by norm_num)
  have hYle : (Y:ℝ) < (X:ℝ)^((10:ℝ)/11) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hYle2 : (Y:ℝ) ≤ 2*(X:ℝ)^((10:ℝ)/11) := by linarith [hYle, hX1]
  have hYpow_le : (Y:ℝ)^((21:ℝ)/20) ≤ (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) :=
    Real.rpow_le_rpow (by positivity) hYle2 (by norm_num)
  have heq2 : (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) = 2^((21:ℝ)/20) * (X:ℝ)^((21:ℝ)/22) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity : (0:ℝ)≤(X:ℝ))]
    norm_num
  have h2pow_le : (2:ℝ)^((21:ℝ)/20) ≤ 40 := by
    calc (2:ℝ)^((21:ℝ)/20) ≤ (2:ℝ)^(2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
      _ ≤ 40 := by norm_num
  have hfinal : (Y:ℝ)^((21:ℝ)/20) ≤ 40*(X:ℝ)^((21:ℝ)/22) := by
    calc (Y:ℝ)^((21:ℝ)/20) ≤ (2*(X:ℝ)^((10:ℝ)/11))^((21:ℝ)/20) := hYpow_le
      _ = 2^((21:ℝ)/20) * (X:ℝ)^((21:ℝ)/22) := heq2
      _ ≤ 40*(X:ℝ)^((21:ℝ)/22) := by
          apply mul_le_mul_of_nonneg_right h2pow_le (by positivity)
  linarith [hncard_le, hFXcard_le, hfinal]

/-- **Lemma 5** of the paper: for every sufficiently large `L` an auxiliary family exists. -/
theorem lemma5 : ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → Nonempty (AuxFamily L) := by
  refine ⟨stageQ₀, fun L hL => ⟨⟨Fconstr L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).1
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.1
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.1
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.1
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.1
  · intro q hqpp hLq
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.1
  · intro q q' hqpp hLq hq'pp hLq' a ha a' ha' hne
    rcases lt_trichotomy q q' with hlt | heq | hgt
    · have h7 := (Fconstr_spec L q' hq'pp hLq' (le_trans hL hLq'.le)).2.2.2.2.2.2.2
      exact (h7 q hlt a' ha' a ha).symm
    · subst heq
      have hdvd := (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.1
      have hane : a ≠ a' := fun hcon => hne (by rw [hcon])
      exact sep_pair_of_four_dvd (hdvd a ha) (hdvd a' ha') hane
    · have h7 := (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.2.2
      exact h7 q' hgt a ha a' ha'
  · intro q hqpp hLq a ha J hJ
    exact (Fconstr_spec L q hqpp hLq (le_trans hL hLq.le)).2.2.2.2.2.2.1 a ha J hJ
  · exact Fconstr_count L

/-- The set `U = P* ∪ F*` of all endpoints that could be used by the correction procedure. -/
def U (L : ℕ) (A : AuxFamily L) : Set ℕ := Pstar L ∪ Fstar L A.F

/-- Elementary log bound: `log x ≤ x^ε / ε` for `x, ε > 0`. -/
theorem log_le_rpow_div (x ε : ℝ) (hx : 0 < x) (hε : 0 < ε) :
    Real.log x ≤ x ^ ε / ε := by
  have h1 : Real.log (x ^ ε) = ε * Real.log x := Real.log_rpow hx ε
  have h2 : Real.log (x ^ ε) ≤ x ^ ε - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [h1] at h2
  rw [le_div_iff₀ hε]
  nlinarith [h2]

/-- `X^(21/22) ≤ 22 * X / log X` for `X ≥ 2` (real `X ≥ 2`, i.e. `X > 1`). -/
theorem rpow_21_22_le (X : ℝ) (hX : 1 < X) :
    X ^ ((21 : ℝ) / 22) ≤ 22 * X / Real.log X := by
  have hXpos : 0 < X := lt_trans one_pos hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hX
  have hb : Real.log X ≤ 22 * X ^ ((1 : ℝ) / 22) := by
    have h := log_le_rpow_div X (1 / 22) hXpos (by norm_num)
    have heq : X ^ ((1 : ℝ) / 22) / (1 / 22) = 22 * X ^ ((1 : ℝ) / 22) := by ring
    rwa [heq] at h
  rw [le_div_iff₀ hlogXpos]
  have hsplit : X ^ ((21 : ℝ) / 22) * X ^ ((1 : ℝ) / 22) = X := by
    rw [← Real.rpow_add hXpos, show (21 : ℝ) / 22 + (1 : ℝ) / 22 = 1 by norm_num, Real.rpow_one]
  have hpownn : (0 : ℝ) ≤ X ^ ((21 : ℝ) / 22) := Real.rpow_nonneg hXpos.le _
  nlinarith [mul_le_mul_of_nonneg_left hb hpownn, hsplit]

/-- **(4.5)**: `|U ∩ [1, X]| = O(X / log X)`. -/
theorem U_count (L : ℕ) (A : AuxFamily L) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ((U L A ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * X / Real.log X := by
  obtain ⟨C1, hC1⟩ := Pstar_count
  obtain ⟨C2, hC2⟩ := A.count
  set C2' : ℝ := max C2 0 with hC2'def
  have hC2'nn : 0 ≤ C2' := le_max_right _ _
  refine ⟨C1 + 22 * C2', fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hUeq : U L A ∩ Set.Icc 1 X = (Pstar L ∩ Set.Icc 1 X) ∪ (Fstar L A.F ∩ Set.Icc 1 X) := by
    rw [U, Set.union_inter_distrib_right]
  have hfin1 : (Pstar L ∩ Set.Icc 1 X).Finite :=
    Set.Finite.subset (Set.finite_Icc 1 X) Set.inter_subset_right
  have hfin2 : (Fstar L A.F ∩ Set.Icc 1 X).Finite :=
    Set.Finite.subset (Set.finite_Icc 1 X) Set.inter_subset_right
  have hcard_le : (U L A ∩ Set.Icc 1 X).ncard
      ≤ (Pstar L ∩ Set.Icc 1 X).ncard + (Fstar L A.F ∩ Set.Icc 1 X).ncard := by
    rw [hUeq]; exact Set.ncard_union_le _ _
  have hcard_leR : ((U L A ∩ Set.Icc 1 X).ncard : ℝ)
      ≤ ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) + ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) := by
    exact_mod_cast hcard_le
  have h1 : ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) ≤ C1 * X / Real.log X := hC1 L X hX
  have h2 : ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C2 * (X : ℝ) ^ ((21 : ℝ) / 22) := hC2 X
  have h2' : ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C2' * (X : ℝ) ^ ((21 : ℝ) / 22) := by
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hXpos.le _))
    exact le_max_left _ _
  have hxpow : (X : ℝ) ^ ((21 : ℝ) / 22) ≤ 22 * (X : ℝ) / Real.log X := rpow_21_22_le X hX1
  have h2'' : ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C2' * (22 * (X : ℝ) / Real.log X) := by
    refine h2'.trans (mul_le_mul_of_nonneg_left hxpow hC2'nn)
  calc ((U L A ∩ Set.Icc 1 X).ncard : ℝ)
      ≤ ((Pstar L ∩ Set.Icc 1 X).ncard : ℝ) + ((Fstar L A.F ∩ Set.Icc 1 X).ncard : ℝ) := hcard_leR
    _ ≤ C1 * X / Real.log X + C2' * (22 * (X : ℝ) / Real.log X) := add_le_add h1 h2''
    _ = (C1 + 22 * C2') * X / Real.log X := by ring

end Erdos289
