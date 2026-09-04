import Erdos289.Defs
import Erdos289.Lemma4

/-!
# Lemma 5: auxiliary pairs with a predetermined count per stage

For a sufficiently large cutoff `L`, fix simultaneously for every prime power `q > L` a family
`F_q` of exactly `s(q) = ⌊q^(1/20)⌋` pairs `[a, a+1]` with `q^(11/10) ≤ a`, `a + 1 ≤ 2 q^(11/10)`,
`4 ∣ a`, both endpoints `(q/2)`-powersmooth, all auxiliary pairs mutually separated and
separated from every possible correction pair, with `|F* ∩ [1, X]| = O(X^(21/22))`.
-/

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

/-- **Lemma 5** of the paper: for every sufficiently large `L` an auxiliary family exists. -/
theorem lemma5 : ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → Nonempty (AuxFamily L) := by
  sorry

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
