import Erdos289.Lemma1EquidistStmt

/-!
# Lemma 1: the odd-case count (open)
-/

set_option maxHeartbeats 1000000

namespace Erdos289

open Finset Filter Topology

/-! ## Helpers about `rOf` (uniqueness of the inverse representative, lifting between moduli) -/

theorem rOf_spec {U t : ℕ} (hU1 : 1 < U) (hcop : Nat.Coprime t U) :
    rOf U t * t ≡ 1 [MOD U] := by
  have hval : ((rOf U t * t : ℕ) : ZMod U) = ((1 : ℕ) : ZMod U) := by
    push_cast; exact ZMod.val_inv_mul hcop
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hval

theorem rOf_lt {U t : ℕ} (hU : 0 < U) : rOf U t < U := by
  haveI : NeZero U := ⟨by omega⟩
  exact ZMod.val_lt _

theorem rOf_unique {U t r : ℕ} (hU1 : 1 < U) (hcop : Nat.Coprime t U) (hr : r < U)
    (hmod : r * t ≡ 1 [MOD U]) : rOf U t = r := by
  have h1 : rOf U t * t ≡ 1 [MOD U] := rOf_spec hU1 hcop
  have h2 : rOf U t * t ≡ r * t [MOD U] := h1.trans hmod.symm
  have h3 : rOf U t ≡ r [MOD U] := Nat.ModEq.cancel_right_of_coprime hcop.symm h2
  have hrOflt : rOf U t < U := rOf_lt (by omega)
  have h4 : rOf U t % U = r % U := h3
  rwa [Nat.mod_eq_of_lt hrOflt, Nat.mod_eq_of_lt hr] at h4

/-- If `S ⊆ invCand U1 T1 T2 α ℓ` and, for each `t ∈ S`, `t` is coprime to a bigger modulus `U2
≥ U1` and `rOf U1 t * t ≡ 1 [MOD U2]` (i.e. the inverse "lifts" unchanged from `U1` to `U2`),
then `S ⊆ invCand U2 T1 T2 α ℓ` too (same absolute residue interval). -/
theorem invCand_bad_subset {U1 U2 : ℕ} (hU1_1 : 1 < U1) (hU2_1 : 1 < U2) (hU12 : U1 ≤ U2)
    (α ℓ T1 T2 : ℕ) (S : Finset ℕ) (hSsub : S ⊆ invCand U1 T1 T2 α ℓ)
    (hcop2 : ∀ t ∈ S, Nat.Coprime t U2)
    (hbadmod : ∀ t ∈ S, (rOf U1 t) * t ≡ 1 [MOD U2]) :
    S ⊆ invCand U2 T1 T2 α ℓ := by
  intro t htS
  have hin1 := hSsub htS
  simp only [invCand, mem_filter, mem_Ico] at hin1 ⊢
  obtain ⟨htIoc, _, hrIco⟩ := hin1
  have hr1lt : rOf U1 t < U2 := lt_of_lt_of_le (rOf_lt (by omega)) hU12
  have hreq : rOf U2 t = rOf U1 t := rOf_unique hU2_1 (hcop2 t htS) hr1lt (hbadmod t htS)
  refine ⟨htIoc, hcop2 t htS, ?_⟩
  rw [hreq]; exact hrIco

/-- `c ≤ q^ε` eventually, for fixed `c` and `ε > 0`. -/
theorem rpow_ge_eventually (ε : ℝ) (hε : 0 < ε) (c : ℝ) :
    ∀ᶠ q : ℕ in atTop, c ≤ (q : ℝ) ^ ε := by
  have h := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **Odd case count** (paper display (2.2)): "Since `4 ∣ m`, the additional condition `p ∣ m`
is equivalent to `rt ≡ 1 (mod 4pq)` ... Subtracting leaves `(1-1/p)² M / 160 + o(M) ≥ M/360 +
o(M)`." Stated as the lower bound needed downstream (using `p ≥ 3`, so `(1-1/p)² ≥ 4/9`);
proved (in the paper) from `equidist_inverse` applied at moduli `4q` and `4pq`. -/
theorem odd_case_count (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ q : ℕ in atTop, ∀ p a : ℕ, p.Prime → Odd p → 0 < a → q = p ^ a →
      (q : ℝ) ^ ε / 360 - κ * (q : ℝ) ^ ε ≤
        ((oddCandT q p ⌊4 * (q : ℝ) ^ ε⌋₊ ⌊5 * (q : ℝ) ^ ε⌋₊).card : ℝ) := by
  intro κ hκ
  have hκ'pos : (0 : ℝ) < κ / 6 := by linarith
  filter_upwards [equidist_inverse ε hε0 hε1 (κ / 6) hκ'pos,
      rpow_le_div_eventually ε hε1 100 (by norm_num), eventually_ge_atTop 100,
      rpow_ge_eventually ε hε0 (10 / κ), rpow_ge_eventually ε hε0 10]
    with q heqdq hMq hq100 hM1000 hM10
  intro p a hp hpodd ha hqeq
  set M : ℝ := (q : ℝ) ^ ε with hMdef
  set T1 : ℕ := ⌊4 * M⌋₊ with hT1def
  set T2 : ℕ := ⌊5 * M⌋₊ with hT2def
  set A0 : ℕ := ⌈3 * (q : ℝ) / 10⌉₊ with hA0def
  set B0 : ℕ := ⌊7 * (q : ℝ) / 20⌋₊ with hB0def
  set L : ℕ := B0 + 1 - A0 with hLdef
  have hqR1 : (100 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq100
  have hMR : M ≤ (q : ℝ) / 100 := hMq
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- basic facts about T1, T2, A0, B0, L
  have hT1R : (T1 : ℝ) ≤ 4 * M := Nat.floor_le (by positivity)
  have hT1R2 : 4 * M - 1 < (T1 : ℝ) := by
    have := Nat.lt_floor_add_one (4 * M); linarith [this]
  have hT2R : (T2 : ℝ) ≤ 5 * M := Nat.floor_le (by positivity)
  have hT2R2 : 5 * M - 1 < (T2 : ℝ) := by
    have := Nat.lt_floor_add_one (5 * M); linarith [this]
  have hA0R : 3 * (q : ℝ) / 10 ≤ (A0 : ℝ) := Nat.le_ceil _
  have hA0R2 : (A0 : ℝ) < 3 * (q : ℝ) / 10 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB0R : (B0 : ℝ) ≤ 7 * (q : ℝ) / 20 := Nat.floor_le (by positivity)
  have hB0R2 : 7 * (q : ℝ) / 20 - 1 < (B0 : ℝ) := by
    have := Nat.lt_floor_add_one (7 * (q : ℝ) / 20); linarith [this]
  have hA0leB0 : A0 ≤ B0 + 1 := by
    have : (A0 : ℝ) ≤ (B0 : ℝ) + 1 := by linarith [hA0R2, hB0R]
    exact_mod_cast this
  have hLR : (L : ℝ) = (B0 : ℝ) + 1 - (A0 : ℝ) := by
    rw [hLdef]
    have : (((B0 + 1 - A0 : ℕ)) : ℝ) = (B0 : ℝ) + 1 - (A0 : ℝ) := by
      have h1 : A0 ≤ B0 + 1 := hA0leB0
      exact_mod_cast (Nat.cast_sub h1 : ((B0 + 1 - A0 : ℕ) : ℝ) = ((B0 + 1 : ℕ) : ℝ) - (A0 : ℝ))
    linarith [this]
  have hT1leT2 : T1 ≤ T2 := Nat.floor_le_floor (by linarith [hMpos])
  have hB0ltq : (B0 : ℝ) < (q : ℝ) := by linarith [hB0R, hqR1]
  have hALleq : A0 + L ≤ q := by
    have : (A0 : ℝ) + (L : ℝ) ≤ (q : ℝ) := by rw [hLR]; linarith [hB0ltq]
    exact_mod_cast this
  have hqpos : 0 < q := by omega
  have hq0 : q ≠ 0 := by omega
  have hqR2 : (1 : ℝ) < (q : ℝ) := by linarith
  have hq1lt : 1 < q := by exact_mod_cast hqR2
  -- p is an odd prime, so p ≥ 3
  have hp2le : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hpodd; omega
  have hppos : 0 < p := by omega
  -- q is odd (a power of the odd prime p)
  have hqodd : Odd q := by rw [hqeq]; exact hpodd.pow
  have hqnot2dvd : ¬ (2 : ℕ) ∣ q := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hqodd
  have hcop4q : Nat.Coprime 4 q := by
    have hcop2q : Nat.Coprime 2 q := (Nat.prime_two.coprime_iff_not_dvd).2 hqnot2dvd
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4eq]; exact hcop2q.pow_left 2
  have h4q1lt : 1 < 4 * q := by omega
  have hqle4pq : q ≤ 4 * p * q := Nat.le_mul_of_pos_left q (by positivity)
  have h4pq1lt : 1 < 4 * p * q := by omega
  have hALleU1 : A0 + L ≤ 4 * q := by omega
  have hALleU2 : A0 + L ≤ 4 * p * q := by omega
  -- coprimality: coprime to `4*q` is the same as coprime to `2*p`
  have hcop_iff : ∀ t : ℕ, Nat.Coprime t (4 * q) ↔ Nat.Coprime t (2 * p) := by
    intro t
    rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    constructor
    · rintro ⟨h4, hq⟩
      refine ⟨?_, ?_⟩
      · rw [h4eq, Nat.coprime_pow_right_iff (by norm_num)] at h4; exact h4
      · rw [hqeq, Nat.coprime_pow_right_iff ha] at hq; exact hq
    · rintro ⟨h2, hp'⟩
      refine ⟨?_, ?_⟩
      · rw [h4eq, Nat.coprime_pow_right_iff (by norm_num)]; exact h2
      · rw [hqeq, Nat.coprime_pow_right_iff ha]; exact hp'
  -- interval bookkeeping (same as the even case)
  have hAL_eq : A0 + L = B0 + 1 := by omega
  have hIcoEq : Finset.Ico A0 (A0 + L) = Finset.Icc A0 B0 := by
    rw [hAL_eq]; ext x; simp only [mem_Ico, mem_Icc]; omega
  have hriff : ∀ r : ℕ, r ∈ Finset.Ico A0 (A0 + L) ↔
      (3 * (q : ℝ) / 10 ≤ (r : ℝ) ∧ (r : ℝ) ≤ 7 * (q : ℝ) / 20) := by
    intro r
    rw [hIcoEq, Finset.mem_Icc]
    rw [hA0def, hB0def, Nat.ceil_le, Nat.le_floor_iff (by positivity)]
  set C1 : Finset ℕ := invCand (4 * q) T1 T2 A0 L with hC1def
  -- `oddCandT q p T1 T2 = C1.filter (fun t => ¬ p ∣ mOf q (4*q) t)`
  have hOddSplit : oddCandT q p T1 T2 = C1.filter (fun t => ¬ p ∣ mOf q (4 * q) t) := by
    rw [hC1def]
    unfold invCand oddCandT
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _
    rw [hriff, hcop_iff t]
    tauto
  have hC1cop : ∀ t ∈ C1, Nat.Coprime t (4 * q) := by
    intro t htC1
    rw [hC1def, invCand, mem_filter] at htC1
    exact htC1.2.1
  -- `C2` := the "bad" subset of `C1` where `p ∣ m`; show `C2 ⊆ invCand (4pq) ...`
  set C2 : Finset ℕ := C1.filter (fun t => p ∣ mOf q (4 * q) t) with hC2def
  have hC2subC1 : C2 ⊆ C1 := Finset.filter_subset _ _
  have hcop4p : Nat.Coprime 4 p := by
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4eq, Nat.coprime_pow_left_iff (by norm_num)]
    exact (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  have hcopU2 : ∀ t ∈ C2, Nat.Coprime t (4 * p * q) := by
    intro t htC2
    have htC1 := hC2subC1 htC2
    have hcop4q_t := hC1cop t htC1
    have hcop2p_t : Nat.Coprime t (2 * p) := (hcop_iff t).1 hcop4q_t
    have h4q_split := Nat.coprime_mul_iff_right.1 hcop4q_t
    have h2p_split := Nat.coprime_mul_iff_right.1 hcop2p_t
    have h4p : Nat.Coprime t (4 * p) := Nat.coprime_mul_iff_right.2 ⟨h4q_split.1, h2p_split.2⟩
    exact Nat.coprime_mul_iff_right.2 ⟨h4p, h4q_split.2⟩
  have hbadmod : ∀ t ∈ C2, (rOf (4 * q) t) * t ≡ 1 [MOD (4 * p * q)] := by
    intro t htC2
    have htC1 := hC2subC1 htC2
    have hcopt := hC1cop t htC1
    have hspec : q * mOf q (4 * q) t + 1 = rOf (4 * q) t * t :=
      mOf_spec ⟨4, by ring⟩ h4q1lt hcopt
    have hrspec : rOf (4 * q) t * t ≡ 1 [MOD (4 * q)] := rOf_spec h4q1lt hcopt
    have h1le : 1 ≤ rOf (4 * q) t * t := by omega
    have heq : rOf (4 * q) t * t - 1 = q * mOf q (4 * q) t := by omega
    have hdvd4q : (4 * q) ∣ (rOf (4 * q) t * t - 1) := (Nat.modEq_iff_dvd' h1le).1 hrspec.symm
    rw [heq] at hdvd4q
    have h4dvdm : (4 : ℕ) ∣ mOf q (4 * q) t := by
      obtain ⟨k, hk⟩ := hdvd4q
      have hk' : q * mOf q (4 * q) t = q * (4 * k) := by rw [hk]; ring
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hqpos hk'⟩
    have hpdvdm : p ∣ mOf q (4 * q) t := by
      rw [hC2def, mem_filter] at htC2; exact htC2.2
    have h4pdvdm : (4 * p) ∣ mOf q (4 * q) t := hcop4p.mul_dvd_of_dvd_of_dvd h4dvdm hpdvdm
    obtain ⟨m', hm'⟩ := h4pdvdm
    have heq2 : rOf (4 * q) t * t - 1 = 4 * p * q * m' := by rw [heq, hm']; ring
    have hdvdU2 : (4 * p * q) ∣ (rOf (4 * q) t * t - 1) := ⟨m', heq2⟩
    exact ((Nat.modEq_iff_dvd' h1le).2 hdvdU2).symm
  have hU12 : 4 * q ≤ 4 * p * q := by
    have h1 : q ≤ p * q := Nat.le_mul_of_pos_left q (by omega)
    calc 4 * q ≤ 4 * (p * q) := by omega
      _ = 4 * p * q := by ring
  have hC2subD2 : C2 ⊆ invCand (4 * p * q) T1 T2 A0 L :=
    invCand_bad_subset h4q1lt h4pq1lt hU12 A0 L T1 T2 C2 hC2subC1 hcopU2 hbadmod
  set D2 : Finset ℕ := invCand (4 * p * q) T1 T2 A0 L with hD2def
  -- `card(oddCandT) = card(C1) - card(C2) ≥ card(C1) - card(D2)`
  have hC1sdiff : C1 \ C2 = oddCandT q p T1 T2 := by
    rw [hOddSplit, hC2def]
    apply Finset.ext
    intro t
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hpdvd => h2 ⟨h1, hpdvd⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun ⟨_, hpdvd⟩ => h2 hpdvd⟩
  have hcardsdiff : (C1 \ C2).card = C1.card - C2.card := Finset.card_sdiff_of_subset hC2subC1
  have hC2leC1 : C2.card ≤ C1.card := Finset.card_le_card hC2subC1
  have hoddcardeq : ((oddCandT q p T1 T2).card : ℝ) = (C1.card : ℝ) - (C2.card : ℝ) := by
    rw [← hC1sdiff, hcardsdiff]; exact Nat.cast_sub hC2leC1
  have hC2leD2 : C2.card ≤ D2.card := Finset.card_le_card hC2subD2
  have hoddge : ((oddCandT q p T1 T2).card : ℝ) ≥ (C1.card : ℝ) - (D2.card : ℝ) := by
    rw [hoddcardeq]
    have : (C2.card : ℝ) ≤ (D2.card : ℝ) := by exact_mod_cast hC2leD2
    linarith
  -- totient computations: `φ(4q)/(4q) = φ(4pq)/(4pq) = (p-1)/(2p)`
  obtain ⟨n, hn⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hqeq' : q = p ^ (n + 1) := by rw [hqeq, hn]
  have h4tot : Nat.totient 4 = 2 := by decide
  have hqtot : q.totient = p ^ n * (p - 1) := by
    rw [hqeq']; exact Nat.totient_prime_pow_succ hp n
  have h4qtot : (4 * q).totient = 2 * (p ^ n * (p - 1)) := by
    rw [Nat.totient_mul hcop4q, h4tot, hqtot]
  have hpqeq' : p * q = p ^ (n + 2) := by
    rw [hqeq']; ring
  have hpqtot : (p * q).totient = p ^ (n + 1) * (p - 1) := by
    rw [hpqeq']; exact Nat.totient_prime_pow_succ hp (n + 1)
  have hpqodd : Odd (p * q) := by rw [hpqeq']; exact hpodd.pow
  have hnot2dvd' : ¬ (2 : ℕ) ∣ (p * q) := by
    rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hpqodd
  have hcop4pq : Nat.Coprime 4 (p * q) := by
    have hcop2 : Nat.Coprime 2 (p * q) := (Nat.prime_two.coprime_iff_not_dvd).2 hnot2dvd'
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4eq]; exact hcop2.pow_left 2
  have h4pqtot : (4 * p * q).totient = 2 * (p ^ (n + 1) * (p - 1)) := by
    rw [show (4 * p * q) = 4 * (p * q) from by ring, Nat.totient_mul hcop4pq, h4tot, hpqtot]
  -- cross-multiplied nat identities avoiding cast/subtraction issues
  have hp1 : 1 ≤ p := by omega
  have hφ4q_cross : (4 * q).totient * (2 * p) = (p - 1) * (4 * q) := by
    rw [h4qtot, hqeq']; ring
  have hφ4pq_cross : (4 * p * q).totient * (2 * p) = (p - 1) * (4 * p * q) := by
    rw [h4pqtot, hqeq']; ring
  have hpR1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1]; norm_num
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hφ4qR : ((4 * q).totient : ℝ) * (2 * (p : ℝ)) = ((p : ℝ) - 1) * ((4 * q : ℕ) : ℝ) := by
    have h := hφ4q_cross
    have hc : (((4 * q).totient * (2 * p) : ℕ) : ℝ) = (((p - 1) * (4 * q) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [hpR1] at hc
    push_cast
    linarith [hc]
  have hφ4pqR : ((4 * p * q).totient : ℝ) * (2 * (p : ℝ)) =
      ((p : ℝ) - 1) * ((4 * p * q : ℕ) : ℝ) := by
    have h := hφ4pq_cross
    have hc : (((4 * p * q).totient * (2 * p) : ℕ) : ℝ) = (((p - 1) * (4 * p * q) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [hpR1] at hc
    push_cast
    linarith [hc]
  have hφ4q_ratio : ((4 * q).totient : ℝ) / ((4 * q : ℕ) : ℝ) = ((p : ℝ) - 1) / (2 * (p : ℝ)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linarith [hφ4qR]
  have hφ4pq_ratio : ((4 * p * q).totient : ℝ) / ((4 * p * q : ℕ) : ℝ) =
      ((p : ℝ) - 1) / (2 * (p : ℝ)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linarith [hφ4pqR]
  -- apply `equidist_inverse` at `U = 4q` and `U = 4pq`
  have hT2Mbound : (T2 : ℝ) ≤ 5 * (q : ℝ) ^ ε := by rw [← hMdef]; exact hT2R
  have hbound1 := heqdq p a hp ha hqeq (4 * q) (Or.inr (Or.inr (Or.inl rfl))) T1 T2 hT1leT2
      hT2Mbound A0 L hALleU1
  have hbound2 := heqdq p a hp ha hqeq (4 * p * q) (Or.inr (Or.inr (Or.inr rfl))) T1 T2 hT1leT2
      hT2Mbound A0 L hALleU2
  rw [← hC1def, hφ4q_ratio] at hbound1
  rw [← hD2def, hφ4pq_ratio] at hbound2
  have hExp1 : (C1.card : ℝ) ≥
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / ((4 * q : ℕ) : ℝ)
        - κ / 6 * M := by
    have := (abs_le.mp hbound1).1; linarith [this]
  have hExp2 : (D2.card : ℝ) ≤
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / ((4 * p * q : ℕ) : ℝ)
        + κ / 6 * M := by
    have := (abs_le.mp hbound2).2; linarith [this]
  -- numeric bounds on `X := T2 - T1` and `L` (identical to the even-case computation)
  have hXcast : ((T2 - T1 : ℕ) : ℝ) = (T2 : ℝ) - (T1 : ℝ) := by
    exact_mod_cast (Nat.cast_sub hT1leT2 : ((T2 - T1 : ℕ) : ℝ) = (T2 : ℝ) - (T1 : ℝ))
  have hXlow : M - 1 < ((T2 - T1 : ℕ) : ℝ) := by
    rw [hXcast]; linarith [hT2R2, hT1R]
  have hXhigh : ((T2 - T1 : ℕ) : ℝ) < M + 1 := by
    rw [hXcast]; linarith [hT2R, hT1R2]
  have hLlow : (q : ℝ) / 20 - 2 < (L : ℝ) := by
    rw [hLR]; linarith [hB0R2, hA0R2]
  have hLhigh : (L : ℝ) ≤ (q : ℝ) / 20 + 1 := by
    rw [hLR]; linarith [hB0R, hA0R]
  have hκM : (10 : ℝ) ≤ κ * M := by
    calc (10 : ℝ) = κ * (10 / κ) := by field_simp
      _ ≤ κ * M := mul_le_mul_of_nonneg_left hM1000 hκ.le
  have hprodlow : (M - 1) * ((q : ℝ) / 20 - 2) < ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) :=
    mul_lt_mul'' hXlow hLlow (by linarith [hM10]) (by linarith [hqR1])
  have hqpos' : (0 : ℝ) < (q : ℝ) := by linarith
  have hstep1 : (M - 1) * ((q : ℝ) / 20 - 2) / (4 * (q : ℝ))
      < ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / (4 * (q : ℝ)) := by
    gcongr
  have hstep2 : M / 80 - M / (2 * (q : ℝ)) - 1 / 80 + 1 / (2 * (q : ℝ))
      = (M - 1) * ((q : ℝ) / 20 - 2) / (4 * (q : ℝ)) := by
    field_simp; ring
  have hMq2 : M / (2 * (q : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (q : ℝ))]
    linarith [hMR, hqR1]
  have h1q2 : 0 ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hfinal : M / 80 - κ / 6 * M ≤ ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / (4 * (q : ℝ)) := by
    rw [← hstep2] at hstep1
    linarith [hstep1, hMq2, h1q2, hκM]
  -- combine: `oddCand.card ≥ C1.card - D2.card`, using the density identity at `4q`, `4pq`
  set Y : ℝ := ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / (4 * (q : ℝ)) with hYdef
  have hYnonneg : 0 ≤ Y := by rw [hYdef]; positivity
  have hYlb : M / 80 - κ / 6 * M ≤ Y := hfinal
  have hDenomEq1 : ((4 * q : ℕ) : ℝ) = 4 * (q : ℝ) := by push_cast; ring
  have hDenomEq2 : ((4 * p * q : ℕ) : ℝ) = (4 * (q : ℝ)) * (p : ℝ) := by push_cast; ring
  rw [hDenomEq1] at hExp1
  rw [hDenomEq2] at hExp2
  have hD2Yrel : ((p : ℝ) - 1) / (2 * (p : ℝ)) * ((T2 - T1 : ℕ) : ℝ) * (L : ℝ)
      / (4 * (q : ℝ) * (p : ℝ)) = ((p : ℝ) - 1) / (2 * (p : ℝ)) * (Y / (p : ℝ)) := by
    rw [hYdef]; field_simp
  rw [hD2Yrel] at hExp2
  have hC1Yrel : ((p : ℝ) - 1) / (2 * (p : ℝ)) * ((T2 - T1 : ℕ) : ℝ) * (L : ℝ) / (4 * (q : ℝ))
      = ((p : ℝ) - 1) / (2 * (p : ℝ)) * Y := by
    rw [hYdef]; ring
  rw [hC1Yrel] at hExp1
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hcoef : (2 : ℝ) / 9 ≤
      ((p : ℝ) - 1) / (2 * (p : ℝ)) - (((p : ℝ) - 1) / (2 * (p : ℝ))) / (p : ℝ) := by
    have heq : ((p : ℝ) - 1) / (2 * (p : ℝ)) - (((p : ℝ) - 1) / (2 * (p : ℝ))) / (p : ℝ)
        = ((p : ℝ) - 1) ^ 2 / (2 * (p : ℝ) ^ 2) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    nlinarith [hp3R, sq_nonneg ((p : ℝ) - 3)]
  have hstepA : (2 : ℝ) / 9 * Y ≤
      ((p : ℝ) - 1) / (2 * (p : ℝ)) * Y - ((p : ℝ) - 1) / (2 * (p : ℝ)) * (Y / (p : ℝ)) := by
    have heq : ((p : ℝ) - 1) / (2 * (p : ℝ)) * Y - ((p : ℝ) - 1) / (2 * (p : ℝ)) * (Y / (p : ℝ))
        = (((p : ℝ) - 1) / (2 * (p : ℝ)) - (((p : ℝ) - 1) / (2 * (p : ℝ))) / (p : ℝ)) * Y := by
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hcoef hYnonneg
  have hstepB : (2 : ℝ) / 9 * (M / 80 - κ / 6 * M) ≤ (2 : ℝ) / 9 * Y :=
    mul_le_mul_of_nonneg_left hYlb (by norm_num)
  have hMpos' : (0 : ℝ) ≤ M := hMpos.le
  nlinarith [hoddge, hExp1, hExp2, hstepA, hstepB, hMpos', hκ]

end Erdos289
