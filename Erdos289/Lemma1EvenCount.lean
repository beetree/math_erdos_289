import Erdos289.Lemma1EquidistStmt

/-!
# Lemma 1: the even-case count (open)
-/

namespace Erdos289

open Finset Filter Topology

set_option maxHeartbeats 1000000

/-! ## Helper lemmas about `rOf` and `invCand` used to relate moduli `U ∣ U'` -/

/-- The defining congruence for `rOf`: `rOf U t` is a genuine inverse of `t` mod `U`. -/
theorem evenCount_rOf_spec {U t : ℕ} (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    rOf U t * t ≡ 1 [MOD U] := by
  have hval : ((rOf U t * t : ℕ) : ZMod U) = ((1 : ℕ) : ZMod U) := by
    push_cast; exact ZMod.val_inv_mul hcop
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hval

theorem evenCount_rOf_lt {U t : ℕ} (hU : 0 < U) : rOf U t < U := by
  have : NeZero U := ⟨by omega⟩
  exact ZMod.val_lt _

/-- Uniqueness of the canonical inverse representative: any `r < U` with `r * t ≡ 1 [MOD U]`
must equal `rOf U t`. -/
theorem evenCount_rOf_unique {U t r : ℕ} (hU1 : 1 < U) (hcop : Nat.Coprime t U) (hr : r < U)
    (hmod : r * t ≡ 1 [MOD U]) : rOf U t = r := by
  have h1 : rOf U t * t ≡ 1 [MOD U] := evenCount_rOf_spec hU1 hcop
  have h2 : rOf U t * t ≡ r * t [MOD U] := h1.trans hmod.symm
  have h3 : rOf U t ≡ r [MOD U] := Nat.ModEq.cancel_right_of_coprime hcop.symm h2
  have hrOflt : rOf U t < U := evenCount_rOf_lt (by omega)
  have h4 : rOf U t % U = r % U := h3
  rwa [Nat.mod_eq_of_lt hrOflt, Nat.mod_eq_of_lt hr] at h4

/-- `c ≤ q^ε` eventually, for fixed `c` and `ε > 0`. -/
theorem evenCount_rpow_ge_eventually (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ q : ℕ in atTop, c ≤ (q:ℝ)^ε := by
  have h := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- If `S ⊆ invCand U1 T1 T2 α ℓ` and, for each `t ∈ S`, `t` is coprime to a bigger modulus `U2
≥ U1` and `rOf U1 t * t ≡ 1 [MOD U2]` (i.e. the inverse "lifts" unchanged from `U1` to `U2`),
then `S ⊆ invCand U2 T1 T2 α ℓ` too (same absolute residue interval). -/
theorem evenCount_invCand_bad_subset {U1 U2 : ℕ} (hU1_1 : 1 < U1) (hU2_1 : 1 < U2) (hU12 : U1 ≤ U2)
    (α ℓ T1 T2 : ℕ) (S : Finset ℕ) (hSsub : S ⊆ invCand U1 T1 T2 α ℓ)
    (hcop2 : ∀ t ∈ S, Nat.Coprime t U2)
    (hbadmod : ∀ t ∈ S, (rOf U1 t) * t ≡ 1 [MOD U2]) :
    S ⊆ invCand U2 T1 T2 α ℓ := by
  intro t htS
  have hin1 := hSsub htS
  simp only [invCand, mem_filter, mem_Ico] at hin1 ⊢
  obtain ⟨htIoc, _, hrIco⟩ := hin1
  have hr1lt : rOf U1 t < U2 := lt_of_lt_of_le (evenCount_rOf_lt (by omega)) hU12
  have hreq : rOf U2 t = rOf U1 t := evenCount_rOf_unique hU2_1 (hcop2 t htS) hr1lt (hbadmod t htS)
  refine ⟨htIoc, hcop2 t htS, ?_⟩
  rw [hreq]; exact hrIco

/-- **Even case count** (paper: "The count of such `t` is `M/40 + o(M)`. Among them, `2 ∣ m`
iff the inverse modulo `2q` belongs to the same absolute interval; their count is
`M/80 + o(M)`. Thus `M/80 + o(M)` choices have odd `m`."). Stated as the lower bound needed
downstream; proved (in the paper) from `equidist_inverse` applied at moduli `q` and `2q`. -/
theorem even_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ a : ℕ, 0 < a → q = 2 ^ a →
      (q : ℝ) ^ ε / 80 - κ * (q : ℝ) ^ ε ≤
        ((evenCandT q ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  intro κ hκ
  have hκ'pos : (0:ℝ) < κ/6 := by linarith
  filter_upwards [equidist_inverse ε hε0 hε1 (κ/6) hκ'pos,
      rpow_le_div_eventually ε hε1 100 (by norm_num), eventually_ge_atTop 100,
      evenCount_rpow_ge_eventually ε hε0 (10/κ), evenCount_rpow_ge_eventually ε hε0 10]
    with q heqdq hMq hq100 hM1000 hM10
  intro a ha hqeq
  set M : ℝ := (q:ℝ)^ε with hMdef
  set T1 : ℕ := ⌊4*M⌋₊ with hT1def
  set T2 : ℕ := ⌊5*M⌋₊ with hT2def
  set A0 : ℕ := ⌈3*(q:ℝ)/10⌉₊ with hA0def
  set B0 : ℕ := ⌊7*(q:ℝ)/20⌋₊ with hB0def
  set L : ℕ := B0 + 1 - A0 with hLdef
  have hqR1 : (100:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq100
  have hMR : M ≤ (q:ℝ)/100 := hMq
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- basic facts about T1, T2, A0, B0, L
  have hT1R : (T1:ℝ) ≤ 4*M := Nat.floor_le (by positivity)
  have hT1R2 : 4*M - 1 < (T1:ℝ) := by
    have := Nat.lt_floor_add_one (4*M); linarith [this]
  have hT2R : (T2:ℝ) ≤ 5*M := Nat.floor_le (by positivity)
  have hT2R2 : 5*M - 1 < (T2:ℝ) := by
    have := Nat.lt_floor_add_one (5*M); linarith [this]
  have hA0R : 3*(q:ℝ)/10 ≤ (A0:ℝ) := Nat.le_ceil _
  have hA0R2 : (A0:ℝ) < 3*(q:ℝ)/10 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB0R : (B0:ℝ) ≤ 7*(q:ℝ)/20 := Nat.floor_le (by positivity)
  have hB0R2 : 7*(q:ℝ)/20 - 1 < (B0:ℝ) := by
    have := Nat.lt_floor_add_one (7*(q:ℝ)/20); linarith [this]
  have hA0leB0 : A0 ≤ B0 + 1 := by
    have : (A0:ℝ) ≤ (B0:ℝ) + 1 := by linarith [hA0R2, hB0R]
    exact_mod_cast this
  have hLR : (L:ℝ) = (B0:ℝ) + 1 - (A0:ℝ) := by
    rw [hLdef]
    have : (((B0+1-A0 : ℕ)):ℝ) = (B0:ℝ) + 1 - (A0:ℝ) := by
      have h1 : A0 ≤ B0 + 1 := hA0leB0
      exact_mod_cast (Nat.cast_sub h1 : ((B0+1-A0:ℕ):ℝ) = ((B0+1:ℕ):ℝ) - (A0:ℝ))
    linarith [this]
  have hT1leT2 : T1 ≤ T2 := Nat.floor_le_floor (by linarith [hMpos])
  have hB0ltq : (B0:ℝ) < (q:ℝ) := by linarith [hB0R, hqR1]
  have hALleq : A0 + L ≤ q := by
    have : (A0:ℝ) + (L:ℝ) ≤ (q:ℝ) := by rw [hLR]; linarith [hB0ltq]
    exact_mod_cast this
  have hALle2q : A0 + L ≤ 2*q := by omega
  have hqpos : 0 < q := by omega
  have hq0 : q ≠ 0 := by omega
  -- apply equidist_inverse at U = q and U = 2*q
  have hT2Mbound : (T2:ℝ) ≤ 5*(q:ℝ)^ε := by rw [← hMdef]; exact hT2R
  have hbound1 := heqdq 2 a Nat.prime_two ha hqeq q (Or.inl rfl) T1 T2 hT1leT2 hT2Mbound
      A0 L hALleq
  have hbound2 := heqdq 2 a Nat.prime_two ha hqeq (2*q) (Or.inr (Or.inl rfl)) T1 T2 hT1leT2
      hT2Mbound A0 L hALle2q
  -- φ(q)/q = 1/2 and φ(2q)/(2q) = 1/2, since q = 2^a
  obtain ⟨n, hn⟩ : ∃ n, a = n + 1 := ⟨a-1, by omega⟩
  have hφq : (q.totient : ℝ) / (q:ℝ) = 1/2 := by
    have hφeq : q.totient = 2^n := by
      rw [hqeq, hn, Nat.totient_prime_pow_succ Nat.prime_two n]; norm_num
    have hqeq2 : q = 2 * 2^n := by rw [hqeq, hn, pow_succ]; ring
    rw [hφeq, hqeq2]
    have h2n : (2:ℝ)^n ≠ 0 := by positivity
    push_cast
    field_simp
  have hφ2q : ((2*q).totient : ℝ) / ((2*q:ℕ):ℝ) = 1/2 := by
    have h2qeq : 2*q = 2^(n+2) := by
      rw [hqeq, hn]; ring
    have hφ2qeq : (2*q).totient = 2^(n+1) := by
      rw [h2qeq, Nat.totient_prime_pow_succ Nat.prime_two (n+1)]; norm_num
    rw [hφ2qeq, h2qeq]
    have h2n : (2:ℝ)^n ≠ 0 := by positivity
    push_cast
    rw [pow_succ]
    field_simp
    ring
  -- evenCandT q T1 T2 = C1.filter (Odd ∘ mOf q q) where C1 = invCand q T1 T2 A0 L
  have hAL_eq : A0 + L = B0 + 1 := by omega
  have hIcoEq : Finset.Ico A0 (A0+L) = Finset.Icc A0 B0 := by
    rw [hAL_eq]
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  have hriff : ∀ r : ℕ, r ∈ Finset.Ico A0 (A0+L) ↔
      (3*(q:ℝ)/10 ≤ (r:ℝ) ∧ (r:ℝ) ≤ 7*(q:ℝ)/20) := by
    intro r
    rw [hIcoEq, Finset.mem_Icc]
    rw [hA0def, hB0def, Nat.ceil_le, Nat.le_floor_iff (by positivity)]
  set C1 : Finset ℕ := invCand q T1 T2 A0 L with hC1def
  have hevenSplit : evenCandT q T1 T2 = C1.filter (fun t => Odd (mOf q q t)) := by
    rw [hC1def]
    unfold invCand evenCandT
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _
    rw [hriff]
    tauto
  -- C2 := C1.filter (Even ∘ m) ⊆ D2 := invCand (2*q) T1 T2 A0 L
  have hqR2 : (1:ℝ) < (q:ℝ) := by linarith
  have hq1lt : 1 < q := by exact_mod_cast hqR2
  have h2q1lt : 1 < 2*q := by omega
  set C2 : Finset ℕ := C1.filter (fun t => Even (mOf q q t)) with hC2def
  have hC2subC1 : C2 ⊆ C1 := Finset.filter_subset _ _
  have h2dvdq : (2:ℕ) ∣ q := by rw [hqeq]; exact dvd_pow_self 2 ha.ne'
  have hC1cop : ∀ t ∈ C1, Nat.Coprime t q := by
    intro t htC1
    rw [hC1def, invCand, mem_filter] at htC1
    exact htC1.2.1
  have hnot2dvd : ∀ t ∈ C1, ¬ (2:ℕ) ∣ t := by
    intro t htC1 h2t
    have hcopt := hC1cop t htC1
    have hdvdgcd : (2:ℕ) ∣ Nat.gcd t q := Nat.dvd_gcd h2t h2dvdq
    rw [hcopt] at hdvdgcd
    have := Nat.le_of_dvd (by norm_num) hdvdgcd
    omega
  have hcop2 : ∀ t ∈ C2, Nat.Coprime t (2*q) := by
    intro t htC2
    have htC1 := hC2subC1 htC2
    have hc2 : Nat.Coprime t 2 := (Nat.prime_two.coprime_iff_not_dvd.2 (hnot2dvd t htC1)).symm
    exact Nat.Coprime.mul_right hc2 (hC1cop t htC1)
  have hbadmod : ∀ t ∈ C2, (rOf q t) * t ≡ 1 [MOD 2*q] := by
    intro t htC2
    have htC1 := hC2subC1 htC2
    have heven : Even (mOf q q t) := by
      rw [hC2def, mem_filter] at htC2; exact htC2.2
    obtain ⟨m', hm'⟩ := heven
    have hspec : q * mOf q q t + 1 = rOf q t * t := mOf_spec (dvd_refl q) hq1lt (hC1cop t htC1)
    have heq2 : rOf q t * t - 1 = 2*q*m' := by
      have h := hspec.symm
      rw [h, hm']
      have hcancel : q*(m'+m')+1-1 = q*(m'+m') := by omega
      rw [hcancel]; ring
    have h1le : 1 ≤ rOf q t * t := by omega
    have hdvd : (2*q) ∣ (rOf q t * t - 1) := ⟨m', heq2⟩
    exact ((Nat.modEq_iff_dvd' h1le).2 hdvd).symm
  have hC2subD2 : C2 ⊆ invCand (2*q) T1 T2 A0 L :=
    evenCount_invCand_bad_subset hq1lt h2q1lt (by omega) A0 L T1 T2 C2 hC2subC1 hcop2 hbadmod
  set D2 : Finset ℕ := invCand (2*q) T1 T2 A0 L with hD2def
  -- card(evenCandT) = card(C1) - card(C2), via C1 \ C2 = evenCandT
  have hC1sdiff : C1 \ C2 = evenCandT q T1 T2 := by
    rw [hevenSplit, hC2def]
    apply Finset.ext
    intro t
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact h2 ⟨h1, hev⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨_, hev⟩
      rw [← Nat.not_even_iff_odd] at h2
      exact h2 hev
  have hcardsdiff : (C1 \ C2).card = C1.card - C2.card := Finset.card_sdiff_of_subset hC2subC1
  have hC2leC1 : C2.card ≤ C1.card := Finset.card_le_card hC2subC1
  have hevencardeq : ((evenCandT q T1 T2).card : ℝ) = (C1.card : ℝ) - (C2.card : ℝ) := by
    rw [← hC1sdiff, hcardsdiff]
    exact Nat.cast_sub hC2leC1
  have hC2leD2 : C2.card ≤ D2.card := Finset.card_le_card hC2subD2
  have hevenge : ((evenCandT q T1 T2).card : ℝ) ≥ (C1.card : ℝ) - (D2.card : ℝ) := by
    rw [hevencardeq]
    have : (C2.card:ℝ) ≤ (D2.card:ℝ) := by exact_mod_cast hC2leD2
    linarith
  -- expected values
  rw [hφq] at hbound1
  rw [hφ2q] at hbound2
  have hExp1 : (C1.card : ℝ) ≥ 1/2 * ((T2-T1:ℕ):ℝ) * (L:ℝ) / q - κ/6*M := by
    have := (abs_le.mp hbound1).1; linarith [this]
  have hcast2q : ((2*q:ℕ):ℝ) = 2*(q:ℝ) := by push_cast; ring
  have hExp2 : (D2.card : ℝ) ≤ 1/2 * ((T2-T1:ℕ):ℝ) * (L:ℝ) / (2*(q:ℝ)) + κ/6*M := by
    rw [← hcast2q]
    have := (abs_le.mp hbound2).2; linarith [this]
  -- numeric bounds
  have hXcast : ((T2-T1:ℕ):ℝ) = (T2:ℝ) - (T1:ℝ) := by
    exact_mod_cast (Nat.cast_sub hT1leT2 : ((T2-T1:ℕ):ℝ) = (T2:ℝ) - (T1:ℝ))
  have hXlow : M - 1 < ((T2-T1:ℕ):ℝ) := by
    rw [hXcast]; linarith [hT2R2, hT1R]
  have hXhigh : ((T2-T1:ℕ):ℝ) < M + 1 := by
    rw [hXcast]; linarith [hT2R, hT1R2]
  have hLlow : (q:ℝ)/20 - 2 < (L:ℝ) := by
    rw [hLR]; linarith [hB0R2, hA0R2]
  have hLhigh : (L:ℝ) ≤ (q:ℝ)/20 + 1 := by
    rw [hLR]; linarith [hB0R, hA0R]
  have hκM : (10:ℝ) ≤ κ * M := by
    calc (10:ℝ) = κ * (10/κ) := by field_simp
      _ ≤ κ * M := mul_le_mul_of_nonneg_left hM1000 hκ.le
  have hprodlow : (M-1)*((q:ℝ)/20-2) < ((T2-T1:ℕ):ℝ) * (L:ℝ) :=
    mul_lt_mul'' hXlow hLlow (by linarith [hM10]) (by linarith [hqR1])
  have hqpos' : (0:ℝ) < (q:ℝ) := by linarith
  have hstep1 : (M-1)*((q:ℝ)/20-2)/(4*(q:ℝ)) < ((T2-T1:ℕ):ℝ)*(L:ℝ)/(4*(q:ℝ)) := by
    gcongr
  have hstep2 : M/80 - M/(2*(q:ℝ)) - 1/80 + 1/(2*(q:ℝ)) = (M-1)*((q:ℝ)/20-2)/(4*(q:ℝ)) := by
    field_simp
    ring
  have hMq2 : M/(2*(q:ℝ)) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*(q:ℝ))]
    linarith [hMR, hqR1]
  have h1q2 : 0 ≤ 1/(2*(q:ℝ)) := by positivity
  have hfinal : M/80 - κ/6*M ≤ ((T2-T1:ℕ):ℝ) * (L:ℝ) / (4*(q:ℝ)) := by
    rw [← hstep2] at hstep1
    linarith [hstep1, hMq2, h1q2, hκM]
  have hXLq : ((T2-T1:ℕ):ℝ) * (L:ℝ) / (4*(q:ℝ)) = (1/2)*((T2-T1:ℕ):ℝ)*(L:ℝ)/(q:ℝ)
      - (1/2)*((T2-T1:ℕ):ℝ)*(L:ℝ)/(2*(q:ℝ)) := by
    field_simp
    ring
  rw [hXLq] at hfinal
  linarith [hevenge, hExp1, hExp2, hfinal]

end Erdos289
