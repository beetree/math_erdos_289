import Erdos289CLT.Basic

/-!
# Square roots modulo a prime power

The congruence `c · b² ≡ r (mod p^α)` with `c, r` units has at most four solutions
`b < p^α`: dividing two solutions reduces to `z² ≡ 1 (mod p^α)`, and
`(z-1)(z+1) ≡ 0` forces `z ≡ ±1 (mod p^α)` for odd `p`, or `z ≡ ±1 (mod 2^{α-1})`
for `p = 2`.
-/

namespace Erdos289.CLT

open Finset

private lemma mem_sq_filter_iff {M z : ℕ} :
    z ∈ (range M).filter (fun z => z ^ 2 ≡ 1 [MOD M]) ↔ z < M ∧ z ^ 2 ≡ 1 [MOD M] := by
  simp [Finset.mem_filter, Finset.mem_range]

private lemma odd_square_one_cases {p α z : ℕ} (hp : p.Prime) (hpne : p ≠ 2)
    (hα : 0 < α) (hz : z < p ^ α) (h : z ^ 2 ≡ 1 [MOD p ^ α]) :
    z = 1 ∨ z = p ^ α - 1 := by
  have hM1 : 1 < p ^ α := ((Nat.one_lt_pow_iff hα.ne').mpr hp.one_lt)
  have hzpos : 0 < z := by
    rcases Nat.eq_zero_or_pos z with rfl | hz0
    · exfalso
      rw [zero_pow (two_ne_zero)] at h
      have hd : p ^ α ∣ 1 := Nat.modEq_zero_iff_dvd.mp h.symm
      exact absurd (Nat.le_of_dvd one_pos hd) (by omega)
    · exact hz0
  have hd : p ^ α ∣ z ^ 2 - 1 :=
    (Nat.modEq_iff_dvd' (by nlinarith)).mp h.symm
  have hkey : (z - 1) * (z + 1) + 1 = z ^ 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, z = n + 1 := ⟨z - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have heq : z ^ 2 - 1 = (z - 1) * (z + 1) := by omega
  have hfactor : p ^ α ∣ (z - 1) * (z + 1) := heq ▸ hd
  have hpM : p ∣ p ^ α := dvd_pow_self p (Nat.ne_of_gt hα)
  rcases Nat.Prime.dvd_or_dvd hp (hpM.trans hfactor) with hd1 | hd2
  · have hd2' : ¬p ∣ z + 1 := by
      intro hd2
      have h2 : p ∣ 2 := by
        have e1 : (z - 1) ≡ 0 [MOD p] := hd1.modEq_zero_nat
        have e2 : (z + 1) ≡ 0 [MOD p] := hd2.modEq_zero_nat
        have heq2 : z - 1 + 2 = z + 1 := by omega
        have e12 := e1.add_right 2
        rw [heq2] at e12
        exact Nat.modEq_zero_iff_dvd.mp (e12.symm.trans e2)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd h hp.ne_one
      · exact absurd h hpne
    have hdvd := (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_right α hd2' hfactor
    have hzero : z - 1 = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hd1' : ¬p ∣ z - 1 := by
      intro hd1
      have h2 : p ∣ 2 := by
        have e1 : (z - 1) ≡ 0 [MOD p] := hd1.modEq_zero_nat
        have e2 : (z + 1) ≡ 0 [MOD p] := hd2.modEq_zero_nat
        have heq2 : z - 1 + 2 = z + 1 := by omega
        have e12 := e1.add_right 2
        rw [heq2] at e12
        exact Nat.modEq_zero_iff_dvd.mp (e12.symm.trans e2)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd h hp.ne_one
      · exact absurd h hpne
    have hfb : p ^ α ∣ (z + 1) * (z - 1) := by rw [mul_comm]; exact hfactor
    have hdvd := (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_right α hd1' hfb
    have hzp1 : z + 1 ≤ p ^ α := by omega
    have hzp0 : 0 < z + 1 := by omega
    have : z + 1 = p ^ α := Nat.le_antisymm hzp1 (Nat.le_of_dvd hzp0 hdvd)
    omega

/-- If `A ∣ x` and `x ≤ 2 * A` then `x ∈ {0, A, 2 * A}`. -/
private lemma eq_cases_of_dvd_of_le_two_mul {A x : ℕ} (hdvd : A ∣ x) (hx : x ≤ 2 * A) :
    x = 0 ∨ x = A ∨ x = 2 * A := by
  obtain ⟨c, rfl⟩ := hdvd
  by_cases hA0 : A = 0
  · left; simp [hA0]
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA0
    have hc : c ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have h3 : 3 * A ≤ A * c := by
        calc 3 * A ≤ c * A := Nat.mul_le_mul_right A hcon
          _ = A * c := mul_comm c A
      omega
    interval_cases c
    · left; ring
    · right; left; ring
    · right; right; ring

/-- Solutions of `z ^ 2 ≡ 1 [MOD 2 ^ (k + 2)]` with `z < 2 ^ (k + 2)` lie in a fixed
four-element set. -/
private lemma two_sq_one_cases {k z : ℕ} (hz : z < 2 ^ (k + 2))
    (h : z ^ 2 ≡ 1 [MOD 2 ^ (k + 2)]) :
    z = 1 ∨ z = 2 ^ (k + 2) - 1 ∨ z = 2 ^ (k + 1) - 1 ∨ z = 2 ^ (k + 1) + 1 := by
  have h2 : z ^ 2 ≡ 1 [MOD 2] := h.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero _))
  have hzodd : Odd z := by
    rcases Nat.even_or_odd z with he | ho
    · exfalso
      have : Even (z ^ 2) := (Nat.even_pow' two_ne_zero).mpr he
      have h20 : z ^ 2 % 2 = 0 := (Nat.even_iff).mp this
      have h21 : z ^ 2 % 2 = 1 % 2 := h2
      omega
    · exact ho
  obtain ⟨u, rfl⟩ := hzodd
  have hu : u < 2 ^ (k + 1) := by
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    omega
  have hzpos : 0 < 2 * u + 1 := by omega
  have hd : 2 ^ (k + 2) ∣ (2 * u + 1) ^ 2 - 1 :=
    (Nat.modEq_iff_dvd' (by nlinarith)).mp h.symm
  have hkey : 4 * (u * (u + 1)) + 1 = (2 * u + 1) ^ 2 := by ring
  have heq : (2 * u + 1) ^ 2 - 1 = 4 * (u * (u + 1)) := by omega
  have hfactor4 : 2 ^ (k + 2) ∣ 4 * (u * (u + 1)) := heq ▸ hd
  have hfactor : 2 ^ k ∣ u * (u + 1) := by
    have h4 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
    rw [h4] at hfactor4
    exact (mul_dvd_mul_iff_left (by norm_num : (4:ℕ) ≠ 0)).mp hfactor4
  have hcop : Nat.Coprime u (u + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right u)
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have h2k2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
  rcases Nat.even_or_odd u with hue | huo
  · -- u even, u+1 odd: 2^k ∣ u
    have hcop2 : Nat.Coprime (2 ^ k) (u + 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (by
        rcases hue with ⟨m, rfl⟩; exact ⟨m, by ring⟩))
    have hdu : 2 ^ k ∣ u := hcop2.dvd_of_dvd_mul_right hfactor
    rcases eq_cases_of_dvd_of_le_two_mul hdu (by omega) with h0 | hA | h2A
    · left; omega
    · right; right; right; omega
    · omega
  · -- u odd, u+1 even: 2^k ∣ u+1
    have hcop2 : Nat.Coprime (2 ^ k) u :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr huo)
    have hfactor' : 2 ^ k ∣ (u + 1) * u := by rw [mul_comm]; exact hfactor
    have hdu : 2 ^ k ∣ (u + 1) := hcop2.dvd_of_dvd_mul_right hfactor'
    rcases eq_cases_of_dvd_of_le_two_mul hdu (by omega) with h0 | hA | h2A
    · omega
    · right; right; left; omega
    · right; left; omega

theorem card_sq_eq_one_le_four {p α : ℕ} (hp : p.Prime) (hα : 0 < α) :
    ((range (p ^ α)).filter (fun z => z ^ 2 ≡ 1 [MOD p ^ α])).card ≤ 4 := by
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.lt_or_ge α 2 with hα1 | hα2
    · -- α = 1
      have hα1' : α = 1 := by omega
      subst hα1'
      have hsub : (range (2 ^ 1)).filter (fun z => z ^ 2 ≡ 1 [MOD 2 ^ 1]) ⊆ ({1} : Finset ℕ) := by
        intro z hz
        simp only [mem_filter, mem_range] at hz
        obtain ⟨hzlt, hzmod⟩ := hz
        simp only [mem_singleton]
        interval_cases z <;> simp_all [Nat.ModEq]
      calc ((range (2 ^ 1)).filter (fun z => z ^ 2 ≡ 1 [MOD 2 ^ 1])).card
          ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 4 := by simp
    · -- α ≥ 2
      obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
      have hsub : (range (2 ^ (k + 2))).filter (fun z => z ^ 2 ≡ 1 [MOD 2 ^ (k + 2)]) ⊆
          ({1, 2 ^ (k + 2) - 1, 2 ^ (k + 1) - 1, 2 ^ (k + 1) + 1} : Finset ℕ) := by
        intro z hz
        simp only [mem_filter, mem_range] at hz
        obtain ⟨hzlt, hzmod⟩ := hz
        have := two_sq_one_cases hzlt hzmod
        simp only [mem_insert, mem_singleton]
        tauto
      calc ((range (2 ^ (k + 2))).filter (fun z => z ^ 2 ≡ 1 [MOD 2 ^ (k + 2)])).card
          ≤ ({1, 2 ^ (k + 2) - 1, 2 ^ (k + 1) - 1, 2 ^ (k + 1) + 1} : Finset ℕ).card :=
            Finset.card_le_card hsub
        _ ≤ 4 := by
            refine (Finset.card_insert_le _ _).trans ?_
            refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
            refine Nat.succ_le_succ (Finset.card_insert_le _ _)
  · have hodd : p ≠ 2 := hp2
    have hsub : (range (p ^ α)).filter (fun z => z ^ 2 ≡ 1 [MOD p ^ α]) ⊆
        ({1, p ^ α - 1} : Finset ℕ) := by
      intro z hz
      simp only [mem_filter, mem_range] at hz
      obtain ⟨hzlt, hzmod⟩ := hz
      have := odd_square_one_cases hp hodd hα hzlt hzmod
      simp only [mem_insert, mem_singleton]
      exact this
    calc ((range (p ^ α)).filter (fun z => z ^ 2 ≡ 1 [MOD p ^ α])).card
        ≤ ({1, p ^ α - 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 4 := by
          refine (Finset.card_insert_le _ _).trans ?_
          simp

theorem card_sq_roots_le_four {p α c r : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hc : Nat.Coprime c (p ^ α)) (hr : Nat.Coprime r (p ^ α)) :
    ((range (p ^ α)).filter (fun b => c * b ^ 2 ≡ r [MOD p ^ α])).card ≤ 4 := by
  set n := p ^ α with hn
  set S := (range n).filter (fun b => c * b ^ 2 ≡ r [MOD n]) with hSdef
  rcases S.eq_empty_or_nonempty with hempty | ⟨b0, hb0S⟩
  · rw [hempty]; simp
  · have hb0S' := mem_filter.mp hb0S
    have hb0lt : b0 < n := mem_range.mp hb0S'.1
    have hb0mod : c * b0 ^ 2 ≡ r [MOD n] := hb0S'.2
    have hnpos : 0 < n := pow_pos hp.pos α
    have : NeZero n := ⟨hnpos.ne'⟩
    have hb0cop : Nat.Coprime b0 n := by
      have hgcd : Nat.gcd (c * b0 ^ 2) n = Nat.gcd r n := hb0mod.gcd_eq
      have hcop_prod : Nat.Coprime (c * b0 ^ 2) n := by
        show Nat.gcd (c * b0 ^ 2) n = 1
        rw [hgcd]; exact hr
      have hcop_sq : Nat.Coprime (b0 ^ 2) n :=
        (Nat.coprime_mul_iff_left.mp hcop_prod).2
      exact (Nat.coprime_pow_left_iff (by norm_num) b0 n).mp hcop_sq
    have hcunit : IsUnit (c : ZMod n) := (ZMod.isUnit_iff_coprime c n).mpr hc
    have hb0unit : (b0 : ZMod n) * (b0 : ZMod n)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b0 hb0cop
    have hb0unit' : (b0 : ZMod n)⁻¹ * (b0 : ZMod n) = 1 := by rw [mul_comm]; exact hb0unit
    set f : ℕ → ℕ := fun b => ((b : ZMod n) * (b0 : ZMod n)⁻¹).val with hfdef
    have hcast : ∀ b : ℕ, ((f b : ℕ) : ZMod n) = (b : ZMod n) * (b0 : ZMod n)⁻¹ :=
      fun b => ZMod.natCast_rightInverse _
    have hmapsto : Set.MapsTo f (S : Set ℕ) ((range n).filter (fun z => z ^ 2 ≡ 1 [MOD n])) := by
      intro b hbS
      simp only [Finset.mem_coe, hSdef, mem_filter, mem_range] at hbS
      obtain ⟨hblt, hbmod⟩ := hbS
      simp only [Finset.mem_coe, mem_filter, mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      have heqcast : (c : ZMod n) * (b : ZMod n) ^ 2 = (c : ZMod n) * (b0 : ZMod n) ^ 2 := by
        have h1 : ((c * b ^ 2 : ℕ) : ZMod n) = ((r : ℕ) : ZMod n) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr hbmod
        have h2 : ((c * b0 ^ 2 : ℕ) : ZMod n) = ((r : ℕ) : ZMod n) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr hb0mod
        push_cast at h1 h2
        rw [h1, h2]
      have heqb2 : (b : ZMod n) ^ 2 = (b0 : ZMod n) ^ 2 := by
        have hx : (b : ZMod n) ^ 2 * (c : ZMod n) = (b0 : ZMod n) ^ 2 * (c : ZMod n) := by
          rw [mul_comm ((b : ZMod n) ^ 2), mul_comm ((b0 : ZMod n) ^ 2)]; exact heqcast
        exact hcunit.mul_left_inj.mp hx
      have hfsq : ((b : ZMod n) * (b0 : ZMod n)⁻¹) ^ 2 = 1 := by
        rw [mul_pow, heqb2, ← mul_pow, hb0unit, one_pow]
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [hcast]
      simpa using hfsq
    have hinj : Set.InjOn f (S : Set ℕ) := by
      intro b1 hb1S b2 hb2S heq
      simp only [Finset.mem_coe, hSdef, mem_filter, mem_range] at hb1S hb2S
      have hb1lt : b1 < n := hb1S.1
      have hb2lt : b2 < n := hb2S.1
      have hval : ((f b1 : ℕ) : ZMod n) = ((f b2 : ℕ) : ZMod n) := by rw [heq]
      rw [hcast, hcast] at hval
      have hval2 :
          (b1 : ZMod n) * (b0 : ZMod n)⁻¹ * (b0 : ZMod n) =
            (b2 : ZMod n) * (b0 : ZMod n)⁻¹ * (b0 : ZMod n) := by rw [hval]
      rw [mul_assoc, mul_assoc, hb0unit', mul_one, mul_one] at hval2
      have : (b1 : ZMod n).val = (b2 : ZMod n).val := by rw [hval2]
      rwa [ZMod.val_cast_of_lt hb1lt, ZMod.val_cast_of_lt hb2lt] at this
    calc S.card ≤ ((range n).filter (fun z => z ^ 2 ≡ 1 [MOD n])).card :=
          Finset.card_le_card_of_injOn f hmapsto hinj
      _ ≤ 4 := card_sq_eq_one_le_four hp hα

end Erdos289.CLT
