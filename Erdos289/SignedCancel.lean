import Erdos289.SignedDefs
import Erdos289.Cancel
import Erdos289.DenBound
import Erdos289.Lemma2

/-!
# Signed correction fibers: cancellation and denominator bookkeeping

Elementary replacement (`docs/elementary_replacements.md`, Section 4, display (D3) and the
"strictly below `q`" bookkeeping) for the signed correction pairs `{q m, q m + σ}`,
`σ ∈ {1, -1}`. This mirrors `Erdos289.Cancel` and the `cancel_or_trivial` step of
`Erdos289.Descent`, replacing the fixed neighbor `q * m + 1` by the signed neighbor
`neighbor q m σ = q * m + σ`.
-/

namespace Erdos289

namespace SignedCancel

open Finset

/-- `q ≥ 2` whenever `q = p ^ a` for a prime `p` and `0 < a`. -/
theorem two_le_prime_pow {p a q : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a) : 2 ≤ q := by
  rw [hq]
  have h1 : p ≤ p ^ a := le_self_pow hp.one_lt.le ha.ne'
  have h2 := hp.two_le
  omega

/-- `2 ≤ q * m` whenever `q = p ^ a` for a prime `p`, `0 < a`, and `0 < m`. -/
theorem two_le_mul {p a q m : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a) (hm : 0 < m) :
    2 ≤ q * m := by
  have hq2 := two_le_prime_pow hp ha hq
  have hm1 : 1 ≤ m := hm
  calc 2 = 2 * 1 := (mul_one 2).symm
    _ ≤ q * m := Nat.mul_le_mul hq2 hm1

/-- `neighbor q m σ`, cast to `ℚ`, equals `q * m + σ` (for `σ = ±1`, `2 ≤ q * m`). -/
theorem neighbor_cast {q m : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m) :
    ((neighbor q m σ : ℕ) : ℚ) = (q * m : ℚ) + (σ : ℚ) := by
  rcases hσ with rfl | rfl
  · unfold neighbor
    rw [ite_eq_left rfl]
    push_cast
    ring
  · unfold neighbor
    rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 1)]
    have h1 : 1 ≤ q * m := by omega
    have hc : ((q * m - 1 : ℕ) : ℚ) = (q * m : ℚ) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hc]
    push_cast
    ring

/-- `neighbor q m σ` is a positive natural number (for `σ = ±1`, `2 ≤ q * m`). -/
theorem neighbor_pos {q m : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m) :
    0 < neighbor q m σ := by
  rcases hσ with rfl | rfl <;> unfold neighbor
  · rw [ite_eq_left rfl]; omega
  · rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 1)]; omega

/-- If `p ∣ q * m`, then `p` does not divide the signed neighbor `neighbor q m σ`
(for `σ = ±1`, `2 ≤ q * m`): the two endpoints of a signed correction pair are consecutive
integers. -/
theorem not_dvd_neighbor {p q m : ℕ} {σ : ℤ} (hp : p.Prime) (hσ : σ = 1 ∨ σ = -1)
    (h2 : 2 ≤ q * m) (hpqm : p ∣ q * m) : ¬ p ∣ neighbor q m σ := by
  intro hcontra
  rcases hσ with rfl | rfl
  · unfold neighbor at hcontra
    rw [ite_eq_left rfl] at hcontra
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpqm).mp hcontra
    exact hp.ne_one (Nat.dvd_one.mp h1)
  · unfold neighbor at hcontra
    rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 1)] at hcontra
    have heq : q * m = (q * m - 1) + 1 := by omega
    rw [heq] at hpqm
    have h1 : p ∣ 1 := (Nat.dvd_add_right hcontra).mp hpqm
    exact hp.ne_one (Nat.dvd_one.mp h1)

/-- `wSigned q m σ = 1 / (q * m) + 1 / (neighbor q m σ)` (for `σ = ±1`, `2 ≤ q * m`), the
natural-number form of the signed pair mass used to mirror the unsigned `cancel_step`.
Both terms are stated as casts of natural numbers (`((q * m : ℕ) : ℚ)`, not `(q : ℚ) * (m : ℚ)`)
to match `den_div_dvd` and `DenBound.one_div`. -/
theorem wSigned_eq_neighbor {q m : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m) :
    wSigned q m σ = 1 / ((q * m : ℕ) : ℚ) + 1 / ((neighbor q m σ : ℕ) : ℚ) := by
  unfold wSigned
  rw [neighbor_cast hσ h2]
  push_cast
  ring

/-- `Powersmooth` is monotone in its smoothness bound. -/
theorem powersmooth_mono {y z n : ℕ} (h : Powersmooth y n) (hyz : y ≤ z) : Powersmooth z n :=
  fun l e hl he hle => (h l e hl he hle).trans hyz

end SignedCancel

open SignedCancel

/-! ## Target 1: `wSigned` as an interval mass -/

/-- `wSigned q m σ` is the reciprocal mass of the signed pair `signedPair q m σ`
(for `σ = ±1`, `2 ≤ q * m`). -/
theorem wSigned_eq {q m : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m) :
    wSigned q m σ = (signedPair q m σ).mass := by
  rcases hσ with rfl | rfl
  · unfold signedPair
    rw [ite_eq_left rfl]
    have heq : (Iv.pair (q * m)).mass = w (q * m) := mass_pair (q * m)
    rw [heq]
    unfold wSigned w
    push_cast
    ring
  · unfold signedPair
    rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 1)]
    have heq : (Iv.pair (q * m - 1)).mass = w (q * m - 1) := mass_pair (q * m - 1)
    rw [heq]
    have h1 : 1 ≤ q * m := by omega
    have hc : ((q * m - 1 : ℕ) : ℚ) = (q * m : ℚ) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    unfold wSigned w
    rw [hc]
    push_cast
    ring

/-! ## Target 2: the signed cancellation step -/

/-- The signed prime-power cancellation step: exactly `Erdos289.cancel_step`, with
`w (q * m)` replaced by `wSigned q m (σ m)` for a chosen sign function `σ`. -/
theorem cancel_step_signed {p a q : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a)
    {u : ℤ} {v : ℕ} (hv : 0 < v) (hpv : ¬ p ∣ v)
    (S : Finset ℕ) (σ : ℕ → ℤ) (hσ : ∀ m ∈ S, σ m = 1 ∨ σ m = -1) (hS0 : ∀ m ∈ S, 0 < m)
    (hSp : ∀ m ∈ S, ¬ p ∣ m)
    (hcong : (∑ m ∈ S, ((m : ZMod q)⁻¹)) = (u : ZMod q) * ((v : ZMod q)⁻¹)) :
    ¬ p ∣ ((u : ℚ) / (q * v) - ∑ m ∈ S, wSigned q m (σ m)).den := by
  classical
  have hpq : p ∣ q := by rw [hq]; exact dvd_pow_self p ha.ne'
  have hq0 : 0 < q := by rw [hq]; exact pow_pos hp.pos a
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hv0' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hcv : Nat.Coprime p v := hp.coprime_iff_not_dvd.mpr hpv
  have hcvq : Nat.Coprime v q := by rw [hq]; exact hcv.symm.pow_right a
  have hcm : ∀ m ∈ S, Nat.Coprime m q := fun m hm => by
    rw [hq]; exact (hp.coprime_iff_not_dvd.mpr (hSp m hm)).symm.pow_right a
  have hqm2 : ∀ m ∈ S, 2 ≤ q * m := fun m hm => SignedCancel.two_le_mul hp ha hq (hS0 m hm)
  -- `p` doesn't divide the signed neighbor `neighbor q m (σ m)` for `m ∈ S`
  have hnf1 : ∀ m ∈ S, ¬ p ∣ neighbor q m (σ m) := fun m hm =>
    SignedCancel.not_dvd_neighbor hp (hσ m hm) (hqm2 m hm) (hpq.mul_right m)
  have hnf : ∀ m ∈ S, ¬ p ∣ (m * neighbor q m (σ m)) := fun m hm hcontra =>
    (hp.dvd_mul.mp hcontra).elim (hSp m hm) (hnf1 m hm)
  -- `D` is the auxiliary common denominator
  set D : ℕ := v * ∏ m ∈ S, (m * neighbor q m (σ m)) with hDdef
  have hprodpos : 0 < ∏ m ∈ S, (m * neighbor q m (σ m)) :=
    Finset.prod_pos (fun m hm =>
      Nat.mul_pos (hS0 m hm) (SignedCancel.neighbor_pos (hσ m hm) (hqm2 m hm)))
  have hDpos : 0 < D := Nat.mul_pos hv hprodpos
  have hD0' : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hDp : ¬ p ∣ D := fun hcontra =>
    (hp.dvd_mul.mp hcontra).elim hpv (fun h2 => hp.prime.not_dvd_finsetProd hnf h2)
  -- divisibility facts needed for exact natural number division
  have hvD : v ∣ D := dvd_mul_right v _
  have hmD : ∀ m ∈ S, m ∣ D := fun m hm =>
    ((dvd_mul_right m (neighbor q m (σ m))).trans
      (Finset.dvd_prod_of_mem (fun k => k * neighbor q k (σ k)) hm)).mul_left v
  have hnbrD : ∀ m ∈ S, neighbor q m (σ m) ∣ D := fun m hm =>
    ((dvd_mul_left (neighbor q m (σ m)) m).trans
      (Finset.dvd_prod_of_mem (fun k => k * neighbor q k (σ k)) hm)).mul_left v
  -- key ZMod inverse identity for exact natural-number divisions
  have hdiv_zmod : ∀ {k : ℕ}, Nat.Coprime k q → k ∣ D →
      ((D / k : ℕ) : ZMod q) = (D : ZMod q) * (k : ZMod q)⁻¹ := by
    intro k hkq hkD
    have h1 : (D / k : ℕ) * k = D := Nat.div_mul_cancel hkD
    have h2 : ((D / k : ℕ) : ZMod q) * (k : ZMod q) = (D : ZMod q) := by
      rw [← Nat.cast_mul, h1]
    calc ((D / k : ℕ) : ZMod q)
        = ((D / k : ℕ) : ZMod q) * 1 := (mul_one _).symm
      _ = ((D / k : ℕ) : ZMod q) * ((k : ZMod q) * (k : ZMod q)⁻¹) := by
          rw [ZMod.coe_mul_inv_eq_one k hkq]
      _ = (((D / k : ℕ) : ZMod q) * (k : ZMod q)) * (k : ZMod q)⁻¹ := by ring
      _ = (D : ZMod q) * (k : ZMod q)⁻¹ := by rw [h2]
  -- the integer `N` witnessing `q * D * X`
  set N : ℤ :=
    u * ((D / v : ℕ) : ℤ) - (∑ m ∈ S, ((D / m : ℕ) : ℤ)) -
      (q : ℤ) * (∑ m ∈ S, ((D / (neighbor q m (σ m)) : ℕ) : ℤ)) with hNdef
  have hqN : (q : ℤ) ∣ N := by
    have hz : (N : ZMod q) = 0 := by
      rw [hNdef]
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
      rw [hdiv_zmod hcvq hvD,
        show (∑ m ∈ S, ((D / m : ℕ) : ZMod q)) = ∑ m ∈ S, (D : ZMod q) * (m : ZMod q)⁻¹ from
          Finset.sum_congr rfl (fun m hm => hdiv_zmod (hcm m hm) (hmD m hm)),
        ZMod.natCast_self, ← Finset.mul_sum, hcong]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd N q).mp hz
  obtain ⟨N', hN'⟩ := hqN
  -- the rational identity `q * D * X = N`
  have key1 : (q : ℚ) * (D : ℚ) * ((u : ℚ) / (q * v)) = (u : ℚ) * ((D : ℚ) / (v : ℚ)) := by
    field_simp
  have key2 : ∀ m ∈ S, (q : ℚ) * (D : ℚ) * wSigned q m (σ m) =
      (D : ℚ) / (m : ℚ) + (q : ℚ) * ((D : ℚ) / ((neighbor q m (σ m) : ℕ) : ℚ)) := by
    intro m hm
    have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (hS0 m hm).ne'
    have hqm2m := hqm2 m hm
    have hqm0' : ((q * m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : q * m ≠ 0)
    have hnbr0' : ((neighbor q m (σ m) : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (SignedCancel.neighbor_pos (hσ m hm) (hqm2 m hm)).ne'
    rw [SignedCancel.wSigned_eq_neighbor (hσ m hm) (hqm2 m hm)]
    field_simp
    push_cast
    ring
  have hqDX : (q : ℚ) * (D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, wSigned q m (σ m)) = (N : ℚ) := by
    rw [mul_sub, key1, Finset.mul_sum, Finset.sum_congr rfl key2,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcv1 : (D : ℚ) / (v : ℚ) = ((D / v : ℕ) : ℚ) := (Nat.cast_div hvD hv0').symm
    have hcm1 : ∀ m ∈ S, (D : ℚ) / (m : ℚ) = ((D / m : ℕ) : ℚ) := fun m hm => by
      have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (hS0 m hm).ne'
      exact (Nat.cast_div (hmD m hm) hm0').symm
    have hcm2 : ∀ m ∈ S, (D : ℚ) / ((neighbor q m (σ m) : ℕ) : ℚ) =
        ((D / (neighbor q m (σ m)) : ℕ) : ℚ) := fun m hm => by
        have hnbr0' : ((neighbor q m (σ m) : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast (SignedCancel.neighbor_pos (hσ m hm) (hqm2 m hm)).ne'
        exact (Nat.cast_div (hnbrD m hm) hnbr0').symm
    rw [hcv1, Finset.sum_congr rfl hcm1, Finset.sum_congr rfl hcm2, hNdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    ring
  -- conclude
  have hDXeq : (D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, wSigned q m (σ m)) = (N' : ℚ) := by
    have heq : (q : ℚ) * ((D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, wSigned q m (σ m))) =
        (q : ℚ) * (N' : ℚ) := by
      rw [← mul_assoc, hqDX, hN']
      push_cast
      ring
    exact mul_left_cancel₀ hq0' heq
  have hXeq : (u : ℚ) / (q * v) - ∑ m ∈ S, wSigned q m (σ m) = (N' : ℚ) / (D : ℚ) := by
    rw [eq_div_iff hD0']
    linear_combination hDXeq
  rw [hXeq]
  exact not_dvd_div_den hDp

/-! ## Target 3: denominator bookkeeping for `wSigned` -/

/-- The denominator of `wSigned q m σ` divides `(q * m) * neighbor q m σ`
(for `σ = ±1`, `2 ≤ q * m`). -/
theorem wSigned_den_dvd {q m : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (h2 : 2 ≤ q * m) :
    (wSigned q m σ).den ∣ (q * m) * neighbor q m σ := by
  have h1 : (((1 : ℤ) : ℚ) / ((q * m : ℕ) : ℚ)).den ∣ q * m := den_div_dvd 1 (q * m)
  have h2' : (((1 : ℤ) : ℚ) / ((neighbor q m σ : ℕ) : ℚ)).den ∣ neighbor q m σ :=
    den_div_dvd 1 (neighbor q m σ)
  have hw : wSigned q m σ =
      ((1 : ℤ) : ℚ) / ((q * m : ℕ) : ℚ) + ((1 : ℤ) : ℚ) / ((neighbor q m σ : ℕ) : ℚ) := by
    rw [SignedCancel.wSigned_eq_neighbor hσ h2]
    push_cast
    ring
  rw [hw]
  exact (Rat.add_den_dvd _ _).trans (mul_dvd_mul h1 h2')

/-- If a prime power `p ^ e` divides the denominator of `wSigned q m σ`, it divides
`q * m` or `neighbor q m σ` (since these are consecutive integers). -/
theorem primePow_dvd_den_wSigned {q m p e : ℕ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (h2 : 2 ≤ q * m) (hp : p.Prime) (h : p ^ e ∣ (wSigned q m σ).den) :
    p ^ e ∣ q * m ∨ p ^ e ∣ neighbor q m σ := by
  have hmul : p ^ e ∣ (q * m) * neighbor q m σ := h.trans (wSigned_den_dvd hσ h2)
  by_cases hpn : p ∣ q * m
  · left
    have hnotp1 : ¬ p ∣ neighbor q m σ := SignedCancel.not_dvd_neighbor hp hσ h2 hpn
    have hcop : Nat.Coprime (p ^ e) (neighbor q m σ) :=
      Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr hnotp1)
    exact hcop.dvd_of_dvd_mul_right hmul
  · right
    have hcop : Nat.Coprime (p ^ e) (q * m) := Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr hpn)
    exact hcop.dvd_of_dvd_mul_left hmul

/-! ## Target 4: denominator descent for a signed correction step -/

/-- The signed analogue of `Erdos289.cancel_or_trivial`: given a candidate multiplier set
`I` (a signed fiber's underlying set, subject to the listed range/coprimality/smoothness
conditions) and a covering hypothesis producing a congruence-satisfying subset whenever
`q` divides the denominator of `r`, one can choose `S ⊆ I` (the empty set when `q` does not
divide `r.den`) so that subtracting `∑_{m ∈ S} wSigned q m (σ m)` from `r` clears the full
`p`-power `q` from the denominator, dropping the denominator bound from `q` to `q - 1`. -/
theorem DenBound_sub_signed {p a q : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a)
    (I : Finset ℕ) (σ : ℕ → ℤ)
    (hIp : ∀ m ∈ I, ¬ p ∣ m) (hIlt : ∀ m ∈ I, m < q) (hI0 : ∀ m ∈ I, 0 < m)
    (hIσ : ∀ m ∈ I, σ m = 1 ∨ σ m = -1)
    (hIsmooth : ∀ m ∈ I, Powersmooth (q - 1) (neighbor q m (σ m)))
    {r : ℚ} (hr : DenBound q r)
    (hcover : q ∣ r.den → ∃ S ⊆ I,
      (∑ m ∈ S, ((m : ZMod q)⁻¹)) = (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹) :
    ∃ S ⊆ I, DenBound (q - 1) (r - ∑ m ∈ S, wSigned q m (σ m)) := by
  classical
  have hq2 : 2 ≤ q := SignedCancel.two_le_prime_pow hp ha hq
  have hq0 : 0 < q := by omega
  by_cases hqdvd : q ∣ r.den
  · -- Case A: `q` divides the denominator; cancel it using the covering hypothesis.
    obtain ⟨S, hS_sub, hS_cong⟩ := hcover hqdvd
    obtain ⟨v, hv_eq⟩ := hqdvd
    have hden_pos : 0 < r.den := Rat.pos r
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with rfl | h
      · simp at hv_eq
      · exact h
    have hpv : ¬ p ∣ v := by
      intro hpvdvd
      obtain ⟨v', hv'⟩ := hpvdvd
      have heq2 : r.den = p ^ (a + 1) * v' := by rw [hv_eq, hv', hq]; ring
      have hdvd2 : p ^ (a + 1) ∣ r.den := ⟨v', heq2⟩
      have hple : p ^ (a + 1) ≤ q := hr p (a + 1) hp (by omega) hdvd2
      rw [hq, pow_succ] at hple
      have hpapos : 0 < p ^ a := pow_pos hp.pos a
      nlinarith [hp.two_le]
    have hveq : r.den / q = v := by rw [hv_eq]; exact Nat.mul_div_cancel_left v hq0
    rw [hveq] at hS_cong
    have hS0 : ∀ m ∈ S, 0 < m := fun m hm => hI0 m (hS_sub hm)
    have hSp : ∀ m ∈ S, ¬ p ∣ m := fun m hm => hIp m (hS_sub hm)
    have hSlt : ∀ m ∈ S, m < q := fun m hm => hIlt m (hS_sub hm)
    have hSσ : ∀ m ∈ S, σ m = 1 ∨ σ m = -1 := fun m hm => hIσ m (hS_sub hm)
    have hcancel := cancel_step_signed hp ha hq hv0 hpv S σ hSσ hS0 hSp hS_cong
    have hden_cast : (r.den : ℚ) = (q : ℚ) * (v : ℚ) := by exact_mod_cast hv_eq
    have hreq : r = (r.num : ℚ) / ((q : ℚ) * (v : ℚ)) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [hden_cast]
    have hcancel' : ¬ p ∣ (r - ∑ m ∈ S, wSigned q m (σ m)).den := by rw [hreq]; exact hcancel
    have hDB1 : DenBound q (r - ∑ m ∈ S, wSigned q m (σ m)) := by
      apply hr.sub
      apply DenBound.sum
      intro m hm
      have hm0 : 0 < m := hS0 m hm
      have hpmm : ¬ p ∣ m := hSp m hm
      have hmq' : m < p ^ a := hq ▸ hSlt m hm
      have hqm2 : 2 ≤ q * m := SignedCancel.two_le_mul hp ha hq hm0
      have hsmooth1 : Powersmooth q (q * m) := by
        intro l e hl he hdvd
        rw [hq] at hdvd
        have := primePow_dvd_mul_le hp hpmm hmq' hm0 hl he hdvd
        rwa [← hq] at this
      have hsmooth2 : Powersmooth q (neighbor q m (σ m)) :=
        SignedCancel.powersmooth_mono (hIsmooth m (hS_sub hm)) (by omega)
      rw [SignedCancel.wSigned_eq_neighbor (hSσ m hm) hqm2]
      exact (DenBound.one_div hsmooth1).add (DenBound.one_div hsmooth2)
    exact ⟨S, hS_sub, DenBound.of_not_dvd_of_le hDB1 hq hp hcancel'⟩
  · -- Case B: `q` already does not divide the denominator.
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simp only [Finset.sum_empty, sub_zero]
    intro l e hl he hle
    have hlq : l ^ e ≤ q := hr l e hl he hle
    have hne : l ^ e ≠ q := by rintro rfl; exact hqdvd hle
    omega

/-! ## Target 5: mass bound for `wSigned` -/

/-- The mass of a signed correction pair is at most `3 / (q * m)` (for `σ = ±1`,
`2 ≤ q * m`): the plus pair has mass at most `2 / (q * m)`, the minus pair at most
`3 / (q * m)`. -/
theorem wSigned_le {q m : ℕ} {σ : ℤ} (h2 : 2 ≤ q * m) (hσ : σ = 1 ∨ σ = -1) :
    wSigned q m σ ≤ 3 / (q * m : ℚ) := by
  have hx0 : (0 : ℚ) < (q * m : ℚ) := by exact_mod_cast (by omega : 0 < q * m)
  rw [SignedCancel.wSigned_eq_neighbor hσ h2]
  push_cast
  rcases hσ with rfl | rfl
  · have hn : neighbor q m 1 = q * m + 1 := by unfold neighbor; rw [ite_eq_left rfl]
    rw [hn]
    have hxn0 : (0 : ℚ) < ((q * m + 1 : ℕ) : ℚ) := by positivity
    rw [div_add_div _ _ (ne_of_gt hx0) (ne_of_gt hxn0),
      div_le_div_iff₀ (mul_pos hx0 hxn0) hx0]
    push_cast
    nlinarith
  · have hn : neighbor q m (-1) = q * m - 1 := by
      unfold neighbor; rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 1)]
    rw [hn]
    have h1 : 1 ≤ q * m := by omega
    have hxn0 : (0 : ℚ) < ((q * m - 1 : ℕ) : ℚ) := by
      have : 0 < q * m - 1 := by omega
      exact_mod_cast this
    rw [div_add_div _ _ (ne_of_gt hx0) (ne_of_gt hxn0),
      div_le_div_iff₀ (mul_pos hx0 hxn0) hx0]
    have hc : ((q * m - 1 : ℕ) : ℚ) = (q * m : ℚ) - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hc]
    have hx2 : (2 : ℚ) ≤ (q * m : ℚ) := by exact_mod_cast h2
    nlinarith

end Erdos289
