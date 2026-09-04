module

public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.Basic
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.ExponentialSums
public import SolveMath.Corpus.Analysis.UnitFractionFourierAnalysis.MajorArcs

@[expose] public section

namespace UnitFractions

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Real
open _root_.Finset

noncomputable section

lemma count_multiples {m n : ℕ} (_hm : 1 ≤ m) :
    ((Finset.Icc 1 n).filter fun k => m ∣ k).card = n / m := by
  have h := Nat.Ioc_filter_dvd_card_eq_div n m
  rw [← Finset.Icc_add_one_left_eq_Ioc] at h
  exact h

lemma count_multiples' {m : ℕ} {n : ℝ} (hm : 1 ≤ m) (hn : 0 ≤ n) :
    ↑((Finset.Icc 1 ⌊n⌋₊).filter fun k => m ∣ k).card ≤ n / m := by
  rw [count_multiples hm]
  refine (Nat.cast_div_le).trans ?_
  exact div_le_div_of_nonneg_right (Nat.floor_le hn) (by positivity)

lemma count_real_multiples' {m : ℕ} {x y : ℝ} (hxy : x ≤ y) (hm : 1 ≤ m) :
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ (y - x) / m + 1 := by
  let s : Finset ℤ := integer_range ((x + y) / (2 * (m : ℝ))) ((y - x) / (2 * (m : ℝ)))
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hsub :
      (Finset.Icc ⌈x⌉ ⌊y⌋).filter (fun k => (m : ℤ) ∣ k) ⊆
        s.image fun z : ℤ => (m : ℤ) * z := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkdiv⟩
    rcases Finset.mem_Icc.mp hkIcc with ⟨hkx, hky⟩
    rcases hkdiv with ⟨z, rfl⟩
    refine Finset.mem_image.mpr ⟨z, ?_, by simp⟩
    rw [mem_integer_range_iff, abs_le]
    have hx' : x ≤ (m : ℝ) * z := by
      have hx'' : x ≤ (((m : ℤ) * z : ℤ) : ℝ) := Int.ceil_le.mp hkx
      simpa using hx''
    have hy' : (m : ℝ) * z ≤ y := by
      have hy'' : ((((m : ℤ) * z : ℤ) : ℝ)) ≤ y := Int.le_floor.mp hky
      simpa using hy''
    constructor
    · field_simp [hm0']
      linarith
    · field_simp [hm0']
      linarith
  have hcard1 :
      ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤
        (s.image fun z : ℤ => (m : ℤ) * z).card :=
    Finset.card_le_card hsub
  have hcard2 : (s.image fun z : ℤ => (m : ℤ) * z).card ≤ s.card := Finset.card_image_le
  have hcard : ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ s.card :=
    Nat.le_trans hcard1 hcard2
  calc
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ ↑s.card := by
      exact_mod_cast hcard
    _ ≤ 2 * ((y - x) / (2 * (m : ℝ))) + 1 := by
      simpa [s] using
        (card_integer_range_le (x := (x + y) / (2 * (m : ℝ)))
          (y := (y - x) / (2 * (m : ℝ)))
          (by exact div_nonneg (sub_nonneg.mpr hxy) (by positivity)))
    _ = (y - x) / m + 1 := by ring_nf

lemma count_real_multiples {m : ℕ} {K : ℝ} {t : ℤ} (hK : 0 < K) (hm : 1 ≤ m) :
    ↑((integer_range t K).filter fun k => (m : ℤ) ∣ k).card ≤ (2 * K) / m + 1 := by
  simpa [integer_range, two_mul] using
    (count_real_multiples' (x := (t : ℝ) - K) (y := (t : ℝ) + K)
      (show (t : ℝ) - K ≤ (t : ℝ) + K by linarith) hm)

lemma candidate_count_one {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (_hN : 2 ≤ N) (_hA : 0 ∉ A) (hK : 1 ≤ K) (_hL : 0 < L) (hk : k ≠ 0)
    (_hKN : K ≤ ↑N)
    (_hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by
  classical
  let R : ℝ := ((k : ℝ) * lcmA A + K) / 2
  let s : Finset ℤ := (integer_range 0 R).filter fun x => (lcmA D : ℤ) ∣ x
  let f : ℤ → Finset ℤ := fun x => (j A).filter fun h => x ∈ I h K k
  have hDsub : D ⊆ ppowers_in_set A := (Finset.mem_ssubsets.1 hD).1
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hDsub h0)
  have hlcmD : 1 ≤ lcmA D := Nat.one_le_iff_ne_zero.2
    ((Finset.lcm_ne_zero_iff (s := D) (f := id)).2
      (by intro x hx hx0; exact hD0 (hx0 ▸ hx)))
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hsubset :
      (minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D) ⊆
        s.biUnion f := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hhminor, hrare⟩
    rcases z h hhminor with ⟨x, hxI, hxdiv⟩
    have hhj : h ∈ j A := by
      rw [minor_arc₂, Finset.mem_sdiff] at hhminor
      exact (Finset.mem_sdiff.mp hhminor.1).1
    have hxdiv' : (lcmA D : ℤ) ∣ x := by
      simpa [hrare] using hxdiv
    have hxI' : (|(h * k : ℝ) - x|) ≤ K / 2 := by
      exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hxI
    have hhbound : |(h * k : ℝ)| ≤ (k : ℝ) * lcmA A / 2 := by
      calc
        |(h * k : ℝ)| = |(h : ℝ)| * (k : ℝ) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ k by positivity)]
        _ ≤ ((lcmA A : ℝ) / 2) * (k : ℝ) := by
          gcongr
          exact bound_of_mem_j A h hhj
        _ = (k : ℝ) * lcmA A / 2 := by ring
    have hxbound : |(x : ℝ)| ≤ R := by
      dsimp [R]
      calc
        |(x : ℝ)| = |((x : ℝ) - h * k) + h * k| := by ring_nf
        _ ≤ |(x : ℝ) - h * k| + |(h * k : ℝ)| := abs_add_le _ _
        _ ≤ K / 2 + (k : ℝ) * lcmA A / 2 := by
          exact add_le_add (by simpa [abs_sub_comm] using hxI') hhbound
        _ = ((k : ℝ) * lcmA A + K) / 2 := by ring
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact
        ⟨(mem_integer_range_iff (x := 0) (y := R) (z := x)).2 (by simpa [R] using hxbound),
          hxdiv'⟩
    · rw [Finset.mem_filter]
      exact ⟨hhj, hxI⟩
  have hfiber :
      ∀ x ∈ s, (((f x).card : ℝ)) ≤ K + 1 := by
    intro x hx
    have hsubx : f x ⊆ integer_range ((x : ℝ) / k) (K / (2 * k)) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [mem_integer_range_iff]
      have hxI : |(h * k : ℝ) - x| ≤ K / 2 := by
        exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hh.2
      have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
        field_simp [hk0]
      rw [hdiv]
      apply (le_div_iff₀ hkpos).2
      calc
        |(x : ℝ) / k - h| * (k : ℝ) = |(x : ℝ) / k - h| * |(k : ℝ)| := by
          rw [abs_of_pos hkpos]
        _ = |((x : ℝ) / k - h) * k| := by rw [← abs_mul]
        _ = |(x : ℝ) - h * k| := by
          congr 1
          field_simp [hk0]
        _ = |(h * k : ℝ) - x| := by rw [abs_sub_comm]
        _ ≤ K / 2 := hxI
    calc
      (((f x).card : ℝ)) ≤ ((integer_range ((x : ℝ) / k) (K / (2 * k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubx
      _ ≤ 2 * (K / (2 * k)) + 1 := by
        apply card_integer_range_le
        positivity
      _ = K / k + 1 := by
        field_simp [hk0]
      _ ≤ K + 1 := by
        have hdivle : K / k ≤ K := by
          apply (div_le_iff₀ (show (0 : ℝ) < k by exact_mod_cast Nat.pos_of_ne_zero hk)).2
          have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        linarith
  have hs : ((s.card : ℝ)) ≤ ((k : ℝ) * lcmA A + K) / lcmA D + 1 := by
    simpa [s, R, two_mul] using
      (count_real_multiples (m := lcmA D) (K := R) (t := 0) hRpos hlcmD)
  calc
    ((((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℕ) : ℝ)
        ≤ ((s.biUnion f).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ x ∈ s, (((f x).card : ℝ)) := by
          exact_mod_cast (Finset.card_biUnion_le (s := s) (t := f))
    _ ≤ ∑ x ∈ s, (K + 1) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hfiber x hx
    _ = (s.card : ℝ) * (K + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((((k : ℝ) * lcmA A + K) / lcmA D + 1) : ℝ) * (K + 1) := by
          exact mul_le_mul_of_nonneg_right hs (by linarith)
    _ = (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by ring

lemma candidate_count {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (hN : 2 ≤ N) (hA : 0 ∉ A) (hK : 1 ≤ K) (hL : 0 < L) (hk : k ≠ 0) (hKN : K ≤ ↑N)
    (hA' : ∀ n ∈ A, n ≤ N)
    (hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
  refine (candidate_count_one hN hA hK hL hk hKN hq z hD).trans ?_
  rw [Finset.mem_ssubsets] at hD
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hD.1 h0)
  have hlcmDpos_nat : 0 < lcmA D := Nat.pos_iff_ne_zero.2
    ((Finset.lcm_ne_zero_iff (s := D) (f := id)).2
      (by intro x hx hx0; exact hD0 (hx0 ▸ hx)))
  have h₁ :
      (lcmA A : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by
    have hprod :
        Finset.prod (ppowers_in_set A \ D) (fun q => q) ≤ N ^ (ppowers_in_set A \ D).card := by
      simpa using
        (Finset.prod_le_pow_card (s := ppowers_in_set A \ D) (f := fun q => q) (n := N)
          (fun q hq => (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).2))
    have hdiv :
        lcmA A ∣ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      rw [← lcm_Q hA]
      refine Finset.lcm_dvd_iff.2 ?_
      intro q hq
      by_cases hqD : q ∈ D
      · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
      · exact dvd_mul_of_dvd_left (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _
    have hnat :
        lcmA A ≤ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      refine Nat.le_of_dvd ?_ hdiv
      refine Nat.mul_pos (Finset.prod_pos ?_) hlcmDpos_nat
      intro q hq
      exact (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).1
    exact_mod_cast hnat.trans (Nat.mul_le_mul_right _ hprod)
  have h₂ : K + 1 ≤ 2 * N := by
    linarith
  have h₃ : (1 : ℝ) ≤ lcmA D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 ((Finset.lcm_ne_zero_iff (s := D) (f := id)).2
      (by intro x hx hx0; exact hD0 (hx0 ▸ hx)))
  have h₄ : (1 : ℝ) ≤ k := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hdiff_nonempty : (ppowers_in_set A \ D).Nonempty := by
    refine Finset.sdiff_nonempty.2 ?_
    intro hsub
    exact hD.2 hsub
  have h₅ : (N : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N by omega)
    have hcard1 : 1 ≤ (ppowers_in_set A \ D).card := by
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr hdiff_nonempty)
    simpa [pow_one] using (pow_le_pow_right₀ hN1 hcard1)
  have hlcmDpos : 0 < (lcmA D : ℝ) := by
    exact_mod_cast hlcmDpos_nat
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by positivity
  have hterm_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by positivity
  have hmul₁ :
      (k : ℝ) * lcmA A ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    exact mul_le_mul_of_nonneg_left h₁ hk_nonneg
  have hmul₂ : K ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    refine (hKN.trans h₅).trans ?_
    refine (le_mul_of_one_le_right hpow_nonneg h₃).trans ?_
    exact le_mul_of_one_le_left hterm_nonneg h₄
  have hdivbound :
      (((k : ℝ) * lcmA A + K) / lcmA D) ≤
        2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) := by
    apply (_root_.div_le_iff₀ hlcmDpos).2
    have hsum :
        (k : ℝ) * lcmA A + K ≤
          2 * ((k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D)) := by
      linarith
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  have hmain :
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
        4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
    have hinner :
        (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
          2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1 := by
      linarith
    calc
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1)
          ≤ (2 * N) * (2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1) := by
            refine mul_le_mul h₂ hinner ?_ ?_
            · positivity
            · linarith
      _ = 4 * (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * N) + 2 * N := by
            ring
      _ = 4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
            congr 2
            rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ]
  refine hmain.trans ?_
  have hNle :
      (N : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card := by
      refine one_le_mul_of_one_le_of_one_le h₄ ?_
      exact (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)).trans h₅
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ, ← mul_assoc]
    simpa [mul_assoc, mul_left_comm, mul_comm] using (le_mul_of_one_le_right hNnonneg hN1)
  linarith

lemma minor2_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K L T : ℝ} {k : ℕ} {A : Finset ℕ},
      0 ∉ A → 1 ≤ K → 0 < L → k ≠ 0 → k ≤ N / 192 → K ≤ N →
        (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) →
      (∀ (t : ℝ) (I : Finset ℤ), I = Finset.Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
        T ≤ (A.filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card ∨
          ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, (q : ℤ) ∣ x) →
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with
    N hN K L T k A hA hK hL hk hkN hKN hA' hq hI
  have hgood :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ∀ q ∈ interval_rare_ppowers (I h K k) A L, (q : ℤ) ∣ x := by
    intro h hh
    refine (hI (t := (h * k : ℝ)) (I := I h K k) (by simp [I, integer_range])).resolve_left ?_
    rw [minor_arc₂_eq, Finset.mem_filter] at hh
    let : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) =
          (((A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card : ℝ)) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    have hh' : (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) < T := by
      rw [hcardeq]
      exact hh.2
    simpa [sZ] using (not_le.mpr hh')
  have hz :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x := by
    intro h hh
    rcases hgood h hh with ⟨x, hx, hx'⟩
    exact ⟨x, hx, cast_lcm_dvd hx'⟩
  have hcard :
      ∀ D ∈ (ppowers_in_set A).ssubsets,
        (((minor_arc₂ A k K T).filter
            fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
          6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    intro D hD
    exact candidate_count hN hA hK hL hk hKN hA' hq hz hD
  have hsumD :
      ∀ D,
        D ∈ (ppowers_in_set A).ssubsets →
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)) ≤
            6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card := by
    intro D hD
    refine
      (Finset.sum_le_card_nsmul
        _ _ ((N : ℝ) ^ (-4 * (ppowers_in_set A \ D).card : ℝ)) ?_).trans ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      rw [← hh.2]
      refine minor2_ind_bound (I h K k) hA (by linarith) hA' hN ?_ hq
      simp [I, integer_range]
    · rw [nsmul_eq_mul]
      refine (mul_le_mul_of_nonneg_right (hcard D hD)
        (Real.rpow_nonneg (show 0 ≤ (N : ℝ) by positivity) _)).trans ?_
      have hNpos : 0 < (N : ℝ) := by
        exact_mod_cast zero_lt_two.trans_le hN
      rw [mul_assoc, ← Real.rpow_add hNpos, mul_assoc (6 * (k : ℝ)), ← Real.rpow_neg_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (by positivity))
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast one_le_two.trans hN
      · have hcard1 : (1 : ℝ) ≤ (ppowers_in_set A \ D).card := by
          rw [Nat.one_le_cast, Nat.succ_le_iff, Finset.card_pos, Finset.sdiff_nonempty]
          rw [Finset.mem_ssubsets] at hD
          exact hD.2
        linarith
  have hsum :
      Finset.sum (ppowers_in_set A).ssubsets
          (fun D =>
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)))
        ≤
          Finset.sum (ppowers_in_set A).ssubsets
            (fun D =>
              6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card) := by
    refine Finset.sum_le_sum ?_
    intro D hD
    exact hsumD D hD
  simp only [Finset.sum_filter] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_ssubsets] at hsum
  rw [← Finset.sum_filter, d_strict_subset hA hk hz, ← Finset.mul_sum] at hsum
  exact hsum.trans (minor2_bound_end N hN hkN hA')

theorem circle_method_prop2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ {K L M T : ℝ} {k : ℕ} {A : Finset ℕ},
        0 < T → 0 < L → 8 ≤ K → K < M → M ≤ N → k ≠ 0 → (k : ℝ) ≤ M / 192 →
        (∀ n ∈ A, M ≤ ↑n) → (∀ n ∈ A, n ≤ N) → rec_sum A < 2 / k →
        (2 : ℝ) / k - 1 / M ≤ rec_sum A → k ∣ (A.lcm id : ℕ) →
        (∀ q ∈ ppowers_in_set A,
          ↑q ≤
            min (L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2))
              (min (c * M / k) (T * K ^ 2 / (N ^ 2 * log N)))) →
        good_condition A K T L → ∃ S ⊆ A, rec_sum S = 1 / k := by
  obtain ⟨C, hC₀, hClcm⟩ := smooth_lcm
  let C' : ℝ := max C 1
  let c : ℝ := log 2 / C'
  have hC'ge : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hC'one : (1 : ℝ) ≤ C' := by
    dsimp [C']
    exact le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one hC'one
  have hc₀ : 0 < c := by
    dsimp [c]
    exact div_pos (Real.log_pos one_lt_two) hC'pos
  refine ⟨c, hc₀, ?_⟩
  filter_upwards [minor1_bound, minor2_bound] with
    N hm1 hm2 K L M T k A hT hL hK hKM hMN hk hkM hA₁ hA₂ hA₃ hA₄ hkA hq hI
  have hM₀ : 0 < M := by
    linarith
  have hk₀ : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hk₀ne : (k : ℝ) ≠ 0 := hk₀.ne'
  have hcCkM : C * (c * M / k) / log 2 / M + 1 / M + 1 / M ≤ 2 / k := by
    have hterm1 : C * (c * M / k) / log 2 / M ≤ (1 : ℝ) / k := by
      have hEq : C * (c * M / k) / log 2 / M = (C / C') / k := by
        dsimp [c]
        field_simp [hk₀ne, hM₀.ne', hC'pos.ne', (Real.log_pos one_lt_two).ne']
      calc
        C * (c * M / k) / log 2 / M = (C / C') / k := hEq
        _ ≤ 1 / k := by
          have hdiv : C / C' ≤ 1 := by
            rw [div_le_iff₀ hC'pos]
            simpa using hC'ge
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hdiv (inv_nonneg.2 hk₀.le)
    have hterm2 : 1 / M + 1 / M ≤ (1 : ℝ) / k := by
      have hkM2 : (2 : ℝ) * k ≤ M := by
        nlinarith
      have hdiv : (2 : ℝ) / M ≤ (1 : ℝ) / k := by
        exact (div_le_div_iff₀ hM₀ hk₀).2 (by simpa [mul_comm] using hkM2)
      simpa [two_mul, div_eq_mul_inv] using hdiv
    have hsum : C * (c * M / k) / log 2 / M + (1 / M + 1 / M) ≤ 1 / k + 1 / k := by
      exact add_le_add hterm1 hterm2
    calc
      C * (c * M / k) / log 2 / M + 1 / M + 1 / M
          = C * (c * M / k) / log 2 / M + (1 / M + 1 / M) := by ring
      _ ≤ 1 / k + 1 / k := hsum
      _ = 2 / k := by ring
  have hA₅ : A.Nonempty := by
    by_contra hA₅
    rw [Finset.not_nonempty_iff_eq_empty] at hA₅
    subst hA₅
    have hA₄' : (2 : ℝ) / k - 1 / M ≤ 0 := by
      simpa [rec_sum] using hA₄
    have hbad'' : (2 : ℝ) / k ≤ 1 / M := by
      linarith
    have hbad' : (2 : ℝ) * M ≤ k := by
      simpa using (div_le_div_iff₀ hk₀ hM₀).mp hbad''
    nlinarith
  have hq' :
      ∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) ∧
          (q : ℝ) ≤ c * M / k ∧ (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    simpa [le_min_iff, and_assoc] using hq
  have hq₁ :
      ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := by
    intro q hqpp
    exact (hq' q hqpp).1
  have hq₂ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
    intro q hqpp
    exact (hq' q hqpp).2.1
  have hq₃ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    intro q hqpp
    exact (hq' q hqpp).2.2
  have hm1' :
      (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm1 (K := K) (M := M) (T := T) (k := k) (A := A) (hK.trans hKM.le) hA₅ hA₁
      (by linarith) hT hA₂ hq₃
  have hA₆ : 0 ∉ A := by
    intro ht
    have : M ≤ 0 := by simpa using hA₁ 0 ht
    linarith
  have hkN : k ≤ N / 192 := by
    have hkN' : 192 * k ≤ N := by
      exact_mod_cast (show (192 : ℝ) * k ≤ N by nlinarith)
    omega
  have h0K : 0 < K := by
    linarith
  have hA₄' : (2 : ℝ) - k / M ≤ k * rec_sum A := by
    have hmul := mul_le_mul_of_nonneg_left hA₄ hk₀.le
    simpa [div_eq_mul_inv, mul_sub, hk₀ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hA₃' : (k : ℝ) * rec_sum A < 2 := by
    have hkQ : (0 : ℚ) < k := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hA₃Q : (k : ℚ) * rec_sum A < 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (_root_.lt_div_iff₀ hkQ).1 hA₃
    exact_mod_cast hA₃Q
  have hAlcm : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ) := by
    have hClcm_nonneg : 0 ≤ c * M / k := by
      refine div_nonneg ?_ (Nat.cast_nonneg k)
      exact mul_nonneg hc₀.le hM₀.le
    have hClcm_bound : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
      intro q hqpp
      exact hq₂ q hqpp
    have hClcmA := hClcm (c * M / k) hClcm_nonneg A hA₆ hClcm_bound
    refine hClcmA.trans ?_
    have hpowpos : 0 < (2 : ℝ) ^ (A.card - 1 : ℤ) := by
      rw [← Real.rpow_intCast]
      exact Real.rpow_pos_of_pos zero_lt_two _
    have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₅
    rw [← Real.log_le_log_iff (Real.exp_pos _) hpowpos, Real.log_exp]
    rw [show (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ (((A.card - 1 : ℤ) : ℝ)) by
      rw [← Real.rpow_intCast]]
    rw [Real.log_rpow zero_lt_two]
    rw [← div_le_iff₀ (Real.log_pos one_lt_two)]
    push_cast
    have hscaled : C * (c * M / k) / log 2 / M + 1 / M ≤ A.card / M := by
      refine le_trans ?_ (rec_sum_le_card_div hM₀ hA₁)
      refine le_trans ?_ hA₄
      linarith
    have hscaled' : C * (c * M / k) / log 2 + 1 ≤ A.card := by
      have hscaled2 : (C * (c * M / k) / log 2 + 1) / M ≤ A.card / M := by
        simpa [add_div] using hscaled
      have hmul := mul_le_mul_of_nonneg_right hscaled2 hM₀.le
      simpa [div_eq_mul_inv, hM₀.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  have hm2' :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm2 (K := K) (L := L) (T := T) (k := k) (A := A) hA₆
      ((by norm_num : (1 : ℝ) ≤ 8).trans hK) hL hk hkN (hKM.le.trans hMN) hA₂ hq₁ hI
  by_contra hS
  have hS' : ∀ S ⊆ A, rec_sum S ≠ 1 / k := by
    intro S hSA hrec
    exact hS ⟨S, hSA, hrec⟩
  have hminorl := minor_lbound hA₁ h0K hKM hkA hk hA₄' hA₃' hA₅ hS' hAlcm
  have hminors : minor_arc₂ A k K T ∪ minor_arc₁ A k K T = j A \ major_arc A k K := by
    rw [minor_arc₂]
    exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hminorl' :
      1 / 2 ≤
        (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) := by
    have htmp := hminorl
    rw [← hminors] at htmp
    rw [minor_arc₂] at htmp
    have hdisj : Disjoint ((j A \ major_arc A k K) \ minor_arc₁ A k K T) (minor_arc₁ A k K T) :=
      (Finset.disjoint_sdiff : Disjoint (minor_arc₁ A k K T)
        ((j A \ major_arc A k K) \ minor_arc₁ A k K T)).symm
    rw [Finset.sum_union hdisj] at htmp
    simpa [minor_arc₂, add_comm, add_left_comm, add_assoc] using htmp
  have hupper :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) < 1 / 2 := by
    calc
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k))
          ≤ 8⁻¹ + 8⁻¹ := add_le_add hm2' hm1'
      _ < 1 / 2 := by norm_num
  exact (not_lt_of_ge hminorl') hupper

end

end UnitFractions
