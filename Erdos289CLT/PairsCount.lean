import Erdos289CLT.PairsCore
import Erdos289CLT.SqRoots

/-!
# Counting the exceptional carriers and the fibres `b ↦ m` (paper Lemma 1, counting)

* `card_bad_b_le`: carriers with `b ∣ T` number at most `8 Dc`: then `T = j b` with
  `1 ≤ j < Dc`, so `d j b² ≡ ±1 (mod q)`, and each of these congruences has at most four
  roots `b < q` (`card_sq_roots_le_four`; none if `p ∣ d j`).
* `card_bad_two_le`: for odd `p`, carriers with `2^{⌊log₂ q⌋ - 2} ∣ T` number at most `16`:
  there are at most `7` such `T < q`, and `8 b T ≡ ±1 (mod q)` determines `b < q`.
* `carriers_per_m_le_four`: at most four carriers share the same `m`: such a `b` divides
  `q m + 1` or `q m - 1`, numbers below `q²` with at most two prime factors above `q/Dc`
  once `q > Dc³`.
-/

namespace Erdos289.CLT

open Finset

/-- `dOf p` is coprime to any power of `p`. -/
private lemma dOf_coprime {p α : ℕ} (hp : p.Prime) (hα : 0 < α) :
    Nat.Coprime (dOf p) (p ^ α) := by
  unfold dOf
  split
  · simp
  · rename_i hpne
    rw [Nat.coprime_pow_right_iff hα]
    have hcop_p2 : Nat.Coprime p 2 :=
      hp.coprime_iff_not_dvd.mpr (fun hdvd => hpne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd))
    have hcop_2p : Nat.Coprime 2 p := hcop_p2.symm
    have : Nat.Coprime (2 ^ 3) p := hcop_2p.pow_left 3
    norm_num at this
    exact this

/-- Converts a congruence `x + 1 ≡ 0` into `x ≡ q - 1`. -/
private lemma modEq_pred_of_succ_modEq_zero {x q : ℕ} (hq : 0 < q) (h : x + 1 ≡ 0 [MOD q]) :
    x ≡ q - 1 [MOD q] := by
  have h2 := h.add_right (q - 1)
  have e1 : x + 1 + (q - 1) = x + q := by omega
  have e2 : (0 : ℕ) + (q - 1) = q - 1 := by omega
  rw [e1, e2] at h2
  exact Nat.add_modulus_modEq_iff.mp h2

/-- `Coprime (q-1) q`. -/
private lemma coprime_pred_self {q : ℕ} (hq : 0 < q) : Nat.Coprime (q - 1) q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)

/-- If `c` is not coprime to `p ^ α` then `p ∣ c`. -/
private lemma p_dvd_of_not_coprime_pow {p α c : ℕ} (hp : p.Prime) (hα : 0 < α)
    (h : ¬ Nat.Coprime c (p ^ α)) : p ∣ c := by
  rw [Nat.coprime_pow_right_iff hα] at h
  rw [Nat.coprime_comm] at h
  rw [hp.coprime_iff_not_dvd] at h
  exact not_not.mp h

/-- A version of `card_sq_roots_le_four` that does not require the coprimality of `c`:
if `c` is not coprime to `p^α`, the congruence has no solutions at all. -/
private lemma card_c_sq_eq_r_le {p α c r : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hr : Nat.Coprime r (p ^ α)) :
    ((range (p ^ α)).filter (fun b => c * b ^ 2 ≡ r [MOD p ^ α])).card ≤ 4 := by
  by_cases hc : Nat.Coprime c (p ^ α)
  · exact card_sq_roots_le_four hp hα hc hr
  · have hpc : p ∣ c := p_dvd_of_not_coprime_pow hp hα hc
    have hpr : ¬ p ∣ r := by
      intro hpr
      have hnc : ¬ Nat.Coprime r (p ^ α) := by
        rw [Nat.coprime_pow_right_iff hα, Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact not_not.mpr hpr
      exact hnc hr
    have hempty : (range (p ^ α)).filter (fun b => c * b ^ 2 ≡ r [MOD p ^ α]) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun {b} _ hbmod => by
        have hpq : p ∣ p ^ α := dvd_pow_self p hα.ne'
        have hmodp : c * b ^ 2 ≡ r [MOD p] := hbmod.of_dvd hpq
        have hcb0 : c * b ^ 2 ≡ 0 [MOD p] := (hpc.mul_right (b ^ 2)).modEq_zero_nat
        exact hpr (Nat.modEq_zero_iff_dvd.mp (hmodp.symm.trans hcb0)))
    rw [hempty]; simp

theorem card_bad_b_le {p α Dc : ℕ} (hp : p.Prime) (hα : 0 < α) (hD : 16 < Dc)
    (hq : Dc ^ 3 < p ^ α) (carriers : Finset ℕ)
    (hcar : ∀ b ∈ carriers, b.Prime ∧ b ≠ p ∧ p ^ α / Dc < b ∧ b < p ^ α / 16) :
    (carriers.filter (fun b => b ∣ TOf p (p ^ α) b)).card ≤ 8 * Dc := by
  set q := p ^ α with hqdef
  have hqpos : 0 < q := pow_pos hp.pos α
  set S : ℕ → Finset ℕ := fun j =>
    (range q).filter (fun b => dOf p * j * b ^ 2 ≡ 1 [MOD q]) ∪
      (range q).filter (fun b => dOf p * j * b ^ 2 ≡ q - 1 [MOD q]) with hSdef
  have hScard : ∀ j, (S j).card ≤ 8 := by
    intro j
    have hc1 : ((range q).filter (fun b => dOf p * j * b ^ 2 ≡ 1 [MOD q])).card ≤ 4 :=
      card_c_sq_eq_r_le hp hα (Nat.coprime_one_left q)
    have hc2 : ((range q).filter (fun b => dOf p * j * b ^ 2 ≡ q - 1 [MOD q])).card ≤ 4 :=
      card_c_sq_eq_r_le hp hα (coprime_pred_self hqpos)
    calc (S j).card ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ 4 + 4 := add_le_add hc1 hc2
      _ = 8 := by norm_num
  have hsub : carriers.filter (fun b => b ∣ TOf p q b) ⊆ (Ico 1 Dc).biUnion S := by
    intro b hb
    simp only [mem_filter] at hb
    obtain ⟨hbc, hbdvd⟩ := hb
    obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
    obtain ⟨hm1, hm2, hm3, hm4, hm5, hT1, hT2, hT3, h8, hcong⟩ :=
      carrier_props hp hα hD hq hbp hbne hb1 hb2
    rw [← hqdef] at hT1 hT2 hT3 hcong
    have hbq : b < q := lt_of_lt_of_le hb2 (Nat.div_le_self q 16)
    obtain ⟨j, hj⟩ := hbdvd
    have hbpos : 0 < b := hbp.pos
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp at hj; omega
      · exact h
    have hbDc : q < b * Dc := (Nat.div_lt_iff_lt_mul (by omega)).mp hb1
    have hjDc : j < Dc := by
      have hlt : b * j < b * Dc := by
        calc b * j = TOf p q b := hj.symm
          _ < q := hT2
          _ < b * Dc := hbDc
      exact Nat.lt_of_mul_lt_mul_left hlt
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjDc⟩, ?_⟩
    have heq : dOf p * b * TOf p q b = dOf p * j * b ^ 2 := by rw [hj]; ring
    simp only [hSdef, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    rcases hcong with hc | hc
    · exact Or.inl ⟨hbq, heq ▸ hc⟩
    · exact Or.inr ⟨hbq, heq ▸ modEq_pred_of_succ_modEq_zero hqpos hc⟩
  calc (carriers.filter (fun b => b ∣ TOf p q b)).card
      ≤ ((Ico 1 Dc).biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Ico 1 Dc, (S j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Ico 1 Dc, 8 := Finset.sum_le_sum (fun j _ => hScard j)
    _ = (Ico 1 Dc).card * 8 := by rw [Finset.sum_const, smul_eq_mul]
    _ = (Dc - 1) * 8 := by rw [Nat.card_Ico]
    _ ≤ 8 * Dc := by omega

theorem card_bad_two_le {p α Dc : ℕ} (hp : p.Prime) (hα : 0 < α) (hD : 16 < Dc)
    (hq : Dc ^ 3 < p ^ α) (_hp2 : p ≠ 2) (carriers : Finset ℕ)
    (hcar : ∀ b ∈ carriers, b.Prime ∧ b ≠ p ∧ p ^ α / Dc < b ∧ b < p ^ α / 16) :
    (carriers.filter (fun b => 2 ^ (Nat.log 2 (p ^ α) - 2) ∣ TOf p (p ^ α) b)).card ≤ 16 := by
  set q := p ^ α with hqdef
  have hqpos : 0 < q := pow_pos hp.pos α
  have hDc17 : 17 ≤ Dc := by omega
  have hDc3 : (17 : ℕ) ^ 3 ≤ Dc ^ 3 := Nat.pow_le_pow_left hDc17 3
  have hq4096 : (4096 : ℕ) ≤ q := by
    have h173 : (17 : ℕ) ^ 3 = 4913 := by norm_num
    omega
  have h212 : (2 : ℕ) ^ 12 ≤ q := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hlog12 : 12 ≤ Nat.log 2 q := (Nat.le_log_iff_pow_le (by norm_num) hqpos.ne').mpr h212
  have hlogsub : Nat.log 2 q - 2 + 3 = Nat.log 2 q + 1 := by omega
  set P := 2 ^ (Nat.log 2 q - 2) with hPdef
  have h8P : q < 8 * P := by
    have hlt : q < 2 ^ (Nat.log 2 q).succ := Nat.lt_pow_succ_log_self (by norm_num) q
    rw [Nat.succ_eq_add_one, ← hlogsub, pow_add] at hlt
    have h23 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h23] at hlt
    rw [← hPdef] at hlt
    omega
  have hPpos : 0 < P := pow_pos (by norm_num) _
  set target : Finset (ℕ × ℕ) := Icc 1 7 ×ˢ ({0, 1} : Finset ℕ) with htargetdef
  set φ : ℕ → ℕ × ℕ := fun b =>
    (TOf p q b / P, if dOf p * b * TOf p q b ≡ 1 [MOD q] then (0 : ℕ) else 1) with hφdef
  have hmapsto : Set.MapsTo φ (carriers.filter (fun b => P ∣ TOf p q b) : Set ℕ) target := by
    intro b hb
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb
    obtain ⟨hbc, hPT⟩ := hb
    obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
    obtain ⟨hm1, hm2, hm3, hm4, hm5, hT1, hT2, hT3, h8, hcong⟩ :=
      carrier_props hp hα hD hq hbp hbne hb1 hb2
    rw [← hqdef] at hT1 hT2 hT3 hcong
    have hPT_le : P ≤ TOf p q b := Nat.le_of_dvd (by omega) hPT
    have hj1 : 1 ≤ TOf p q b / P := by
      rw [Nat.le_div_iff_mul_le hPpos]
      omega
    have hTP_le : TOf p q b / P * P ≤ TOf p q b := Nat.div_mul_le_self _ _
    have hlt8P : TOf p q b / P * P < 8 * P := by omega
    have hj7lt : TOf p q b / P < 8 := Nat.lt_of_mul_lt_mul_right hlt8P
    have hj7 : TOf p q b / P ≤ 7 := by omega
    exact Finset.mk_mem_product (Finset.mem_Icc.mpr ⟨hj1, hj7⟩) (by split_ifs <;> simp)
  have hinjOn : Set.InjOn φ (carriers.filter (fun b => P ∣ TOf p q b) : Set ℕ) := by
    intro b hb b' hb' heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb hb'
    obtain ⟨hbc, hPT⟩ := hb
    obtain ⟨hbc', hPT'⟩ := hb'
    obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
    obtain ⟨hbp', hbne', hb1', hb2'⟩ := hcar b' hbc'
    obtain ⟨hm1, hm2, hm3, hm4, hm5, hT1, hT2, hT3, h8, hcong⟩ :=
      carrier_props hp hα hD hq hbp hbne hb1 hb2
    obtain ⟨hm1', hm2', hm3', hm4', hm5', hT1', hT2', hT3', h8', hcong'⟩ :=
      carrier_props hp hα hD hq hbp' hbne' hb1' hb2'
    rw [← hqdef] at hT1 hT2 hT3 hcong hT1' hT2' hT3' hcong'
    have hbq : b < q := lt_of_lt_of_le hb2 (Nat.div_le_self q 16)
    have hbq' : b' < q := lt_of_lt_of_le hb2' (Nat.div_le_self q 16)
    have heqj : TOf p q b / P = TOf p q b' / P := congrArg Prod.fst heq
    have heqsign : (if dOf p * b * TOf p q b ≡ 1 [MOD q] then (0 : ℕ) else 1) =
        (if dOf p * b' * TOf p q b' ≡ 1 [MOD q] then (0 : ℕ) else 1) := congrArg Prod.snd heq
    have hTeq : TOf p q b = TOf p q b' := by
      have e1 : TOf p q b = TOf p q b / P * P := (Nat.div_mul_cancel hPT).symm
      have e2 : TOf p q b' = TOf p q b' / P * P := (Nat.div_mul_cancel hPT').symm
      rw [e1, e2, heqj]
    have hcop : Nat.Coprime (dOf p * TOf p q b) q :=
      Nat.coprime_mul_iff_left.mpr ⟨dOf_coprime hp hα, hT3⟩
    have hcancel : ∀ x y : ℕ, dOf p * TOf p q b * x ≡ dOf p * TOf p q b * y [MOD q] →
        x ≡ y [MOD q] := fun x y h => Nat.ModEq.cancel_left_of_coprime hcop.symm h
    have hbmod : b ≡ b' [MOD q] := by
      by_cases h1 : dOf p * b * TOf p q b ≡ 1 [MOD q]
      · by_cases h2 : dOf p * b' * TOf p q b' ≡ 1 [MOD q]
        · -- both first congruence
          have e1 : dOf p * TOf p q b * b ≡ 1 [MOD q] := by
            have hcomm : dOf p * b * TOf p q b = dOf p * TOf p q b * b := by ring
            rwa [hcomm] at h1
          have e2 : dOf p * TOf p q b * b' ≡ 1 [MOD q] := by
            have hcomm : dOf p * b' * TOf p q b' = dOf p * TOf p q b' * b' := by ring
            rw [hcomm, ← hTeq] at h2
            exact h2
          exact hcancel b b' (e1.trans e2.symm)
        · simp [h1, h2] at heqsign
      · by_cases h2 : dOf p * b' * TOf p q b' ≡ 1 [MOD q]
        · simp [h1, h2] at heqsign
        · -- both second congruence
          have hc1 : dOf p * b * TOf p q b + 1 ≡ 0 [MOD q] := hcong.resolve_left h1
          have hc2 : dOf p * b' * TOf p q b' + 1 ≡ 0 [MOD q] := hcong'.resolve_left h2
          have e1 : dOf p * TOf p q b * b ≡ q - 1 [MOD q] := by
            have hcomm : dOf p * b * TOf p q b = dOf p * TOf p q b * b := by ring
            rw [hcomm] at hc1
            exact modEq_pred_of_succ_modEq_zero hqpos hc1
          have e2 : dOf p * TOf p q b * b' ≡ q - 1 [MOD q] := by
            have hcomm : dOf p * b' * TOf p q b' = dOf p * TOf p q b' * b' := by ring
            rw [hcomm, ← hTeq] at hc2
            exact modEq_pred_of_succ_modEq_zero hqpos hc2
          exact hcancel b b' (e1.trans e2.symm)
    have hmodeq : b % q = b' % q := hbmod
    rwa [Nat.mod_eq_of_lt hbq, Nat.mod_eq_of_lt hbq'] at hmodeq
  calc (carriers.filter (fun b => P ∣ TOf p q b)).card
      ≤ target.card := Finset.card_le_card_of_injOn φ hmapsto hinjOn
    _ = 14 := by rw [htargetdef, Finset.card_product]; simp
    _ ≤ 16 := by norm_num

/-- At most two primes above `q/Dc` can divide a fixed `N < q²` once `Dc³ < q`. -/
private lemma card_primes_gt_div_dvd_le_two {Dc q N : ℕ} (hDc0 : 0 < Dc) (hq : Dc ^ 3 < q)
    (hN0 : 0 < N) (hN2 : N < q ^ 2) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b.Prime ∧ q / Dc < b ∧ b ∣ N) : S.card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcon
  obtain ⟨hap, haq, had⟩ := hS a ha
  obtain ⟨hbp, hbq, hbd⟩ := hS b hb
  obtain ⟨hcp, hcq, hcd⟩ := hS c hc
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · norm_num at hN2
    · exact h
  have hqa : q < a * Dc := (Nat.div_lt_iff_lt_mul hDc0).mp haq
  have hqb : q < b * Dc := (Nat.div_lt_iff_lt_mul hDc0).mp hbq
  have hqc : q < c * Dc := (Nat.div_lt_iff_lt_mul hDc0).mp hcq
  have hab' : Nat.Coprime a b := (Nat.coprime_primes hap hbp).mpr hab
  have hac' : Nat.Coprime a c := (Nat.coprime_primes hap hcp).mpr hac
  have hbc' : Nat.Coprime b c := (Nat.coprime_primes hbp hcp).mpr hbc
  have habN : a * b ∣ N := hab'.mul_dvd_of_dvd_of_dvd had hbd
  have habc_cop : Nat.Coprime (a * b) c := Nat.coprime_mul_iff_left.mpr ⟨hac', hbc'⟩
  have habcN : a * b * c ∣ N := habc_cop.mul_dvd_of_dvd_of_dvd habN hcd
  have hle : a * b * c ≤ N := Nat.le_of_dvd hN0 habcN
  have haDcpos : 0 < a * Dc := Nat.mul_pos hap.pos hDc0
  have hbDcpos : 0 < b * Dc := Nat.mul_pos hbp.pos hDc0
  have e1 : q * q < (a * Dc) * (b * Dc) := by
    calc q * q < (a * Dc) * q := mul_lt_mul_of_pos_right hqa hqpos
      _ < (a * Dc) * (b * Dc) := mul_lt_mul_of_pos_left hqb haDcpos
  have e2 : q * q * q < (a * Dc) * (b * Dc) * (c * Dc) := by
    calc q * q * q < ((a * Dc) * (b * Dc)) * q := mul_lt_mul_of_pos_right e1 hqpos
      _ < ((a * Dc) * (b * Dc)) * (c * Dc) :=
        mul_lt_mul_of_pos_left hqc (Nat.mul_pos haDcpos hbDcpos)
  have e3 : q ^ 3 < Dc ^ 3 * (a * b * c) := by
    have eqL : q ^ 3 = q * q * q := by ring
    have eqR : Dc ^ 3 * (a * b * c) = a * Dc * (b * Dc) * (c * Dc) := by ring
    rw [eqL, eqR]; exact e2
  have e4 : Dc ^ 3 * (a * b * c) ≤ Dc ^ 3 * N := Nat.mul_le_mul (le_refl _) hle
  have e5 : Dc ^ 3 * N < Dc ^ 3 * q ^ 2 := mul_lt_mul_of_pos_left hN2 (by positivity)
  have e6 : Dc ^ 3 * q ^ 2 < q * q ^ 2 := mul_lt_mul_of_pos_right hq (by positivity)
  have e7 : q * q ^ 2 = q ^ 3 := by ring
  have hfin : q ^ 3 < q ^ 3 := by
    calc q ^ 3 < Dc ^ 3 * (a * b * c) := e3
      _ ≤ Dc ^ 3 * N := e4
      _ < Dc ^ 3 * q ^ 2 := e5
      _ < q * q ^ 2 := e6
      _ = q ^ 3 := e7
  exact absurd hfin (lt_irrefl _)

theorem carriers_per_m_le_four {p α Dc : ℕ} (hp : p.Prime) (hα : 0 < α) (hD : 16 < Dc)
    (hq : Dc ^ 3 < p ^ α) (carriers : Finset ℕ)
    (hcar : ∀ b ∈ carriers, b.Prime ∧ b ≠ p ∧ p ^ α / Dc < b ∧ b < p ^ α / 16) (m : ℕ) :
    (carriers.filter (fun b => mOf p (p ^ α) b = m)).card ≤ 4 := by
  set q := p ^ α with hqdef
  rcases (carriers.filter (fun b => mOf p q b = m)).eq_empty_or_nonempty with hemp | ⟨b0, hb0⟩
  · rw [hemp]; simp
  · simp only [mem_filter] at hb0
    obtain ⟨hb0c, hb0eq⟩ := hb0
    obtain ⟨hb0p, hb0ne, hb01, hb02⟩ := hcar b0 hb0c
    obtain ⟨hm01, hm02, hm03, hm04, hm05, hT01, hT02, hT03, h08, hcong0⟩ :=
      carrier_props hp hα hD hq hb0p hb0ne hb01 hb02
    rw [← hqdef] at hm01 hm02
    have hmpos : 1 ≤ m := hb0eq ▸ hm01
    have hmlt : m < q := hb0eq ▸ hm02
    have hqpos : 0 < q := pow_pos hp.pos α
    have hq2 : 2 ≤ q := by
      have := Nat.one_lt_pow hα.ne' hp.one_lt
      rw [← hqdef] at this
      omega
    have hm1q : m + 1 ≤ q := hmlt
    have hN1lt : q * m + 1 < q ^ 2 := by
      have hle : q * (m + 1) ≤ q * q := Nat.mul_le_mul (le_refl q) hm1q
      have hexp : q * (m + 1) = q * m + q := by ring
      have hsq : q ^ 2 = q * q := by ring
      rw [hexp] at hle
      omega
    have hN2lt : q * m - 1 < q ^ 2 := by omega
    have hN2pos : 0 < q * m - 1 := by
      have : 2 ≤ q * m := by nlinarith [hq2, hmpos]
      omega
    have hN1pos : 0 < q * m + 1 := by omega
    set N1 := q * m + 1 with hN1def
    set N2 := q * m - 1 with hN2def
    have hdvd_or : ∀ b ∈ carriers.filter (fun b => mOf p q b = m), b ∣ N1 ∨ b ∣ N2 := by
      intro b hb
      simp only [mem_filter] at hb
      obtain ⟨hbc, hbeq⟩ := hb
      obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
      obtain ⟨hbm1, hbm2, hbm3, hbm4, hbm5, hbT1, hbT2, hbT3, hb8, hbcong⟩ :=
        carrier_props hp hα hD hq hbp hbne hb1 hb2
      rw [← hqdef] at hbm4 hbm5
      have hbdvd_comp : b ∣ companion q (loOf p q b) (mOf p q b) :=
        ⟨dOf p * TOf p q b, by rw [hbm5]; ring⟩
      have hcomp_cases : companion q (loOf p q b) (mOf p q b) = q * mOf p q b + 1 ∨
          companion q (loOf p q b) (mOf p q b) = q * mOf p q b - 1 := by
        unfold companion
        rcases hbm4 with h | h
        · left; omega
        · right; omega
      rcases hcomp_cases with h | h
      · left
        have hbdvd' : b ∣ q * mOf p q b + 1 := h ▸ hbdvd_comp
        rw [hbeq] at hbdvd'
        rwa [hN1def]
      · right
        have hbdvd' : b ∣ q * mOf p q b - 1 := h ▸ hbdvd_comp
        rw [hbeq] at hbdvd'
        rwa [hN2def]
    have hsub : carriers.filter (fun b => mOf p q b = m) ⊆
        carriers.filter (fun b => b ∣ N1) ∪ carriers.filter (fun b => b ∣ N2) := by
      intro b hb
      have hb' := hb
      simp only [mem_filter] at hb'
      rcases hdvd_or b hb with h | h
      · exact Finset.mem_union_left _ (mem_filter.mpr ⟨hb'.1, h⟩)
      · exact Finset.mem_union_right _ (mem_filter.mpr ⟨hb'.1, h⟩)
    have hT1card : (carriers.filter (fun b => b ∣ N1)).card ≤ 2 :=
      card_primes_gt_div_dvd_le_two (by omega) hq hN1pos hN1lt _
        (fun b hb => by
          simp only [mem_filter] at hb
          obtain ⟨hbc, hbd⟩ := hb
          obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
          exact ⟨hbp, hb1, hbd⟩)
    have hT2card : (carriers.filter (fun b => b ∣ N2)).card ≤ 2 :=
      card_primes_gt_div_dvd_le_two (by omega) hq hN2pos hN2lt _
        (fun b hb => by
          simp only [mem_filter] at hb
          obtain ⟨hbc, hbd⟩ := hb
          obtain ⟨hbp, hbne, hb1, hb2⟩ := hcar b hbc
          exact ⟨hbp, hb1, hbd⟩)
    calc (carriers.filter (fun b => mOf p q b = m)).card
        ≤ (carriers.filter (fun b => b ∣ N1) ∪ carriers.filter (fun b => b ∣ N2)).card :=
          Finset.card_le_card hsub
      _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ 2 + 2 := add_le_add hT1card hT2card
      _ = 4 := by norm_num

end Erdos289.CLT
