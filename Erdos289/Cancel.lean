import Erdos289.Defs

/-!
# Prime-power cancellation step (Section 4)

This file formalizes the elementary "prime-power cancellation" calculation from
Section 4 of the paper: if `q = p ^ a` is the full power of `p` in the denominator
of the current deficit `u / (q * v)`, and `S` is a finite set of positive integers
coprime to `p` with `∑_{m ∈ S} m⁻¹ ≡ u * v⁻¹ (mod q)`, then subtracting
`∑_{m ∈ S} w (q * m)` from the deficit produces a rational number whose denominator
is coprime to `p`.
-/

namespace Erdos289

open Finset

/-! ## Denominator bookkeeping lemmas -/

/-- If `p` doesn't divide the denominators of `x` and `y`, it doesn't divide the
denominator of `x + y`. -/
theorem not_dvd_add_den {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : ¬ p ∣ x.den)
    (hy : ¬ p ∣ y.den) : ¬ p ∣ (x + y).den := by
  intro h
  rcases hp.dvd_mul.mp (h.trans (Rat.add_den_dvd x y)) with h' | h'
  · exact hx h'
  · exact hy h'

/-- If `p` doesn't divide the denominators of `x` and `y`, it doesn't divide the
denominator of `x - y`. -/
theorem not_dvd_sub_den {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : ¬ p ∣ x.den)
    (hy : ¬ p ∣ y.den) : ¬ p ∣ (x - y).den := by
  intro h
  rcases hp.dvd_mul.mp (h.trans (Rat.sub_den_dvd x y)) with h' | h'
  · exact hx h'
  · exact hy h'

/-- The denominator of a finite sum divides the product of the denominators. -/
theorem den_sum_dvd (f : ℕ → ℚ) (S : Finset ℕ) :
    (∑ i ∈ S, f i).den ∣ ∏ i ∈ S, (f i).den := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- If `p` doesn't divide any of the denominators `(f i).den` for `i ∈ S`, it doesn't
divide the denominator of `∑ i ∈ S, f i`. -/
theorem not_dvd_sum_den {p : ℕ} (hp : p.Prime) {f : ℕ → ℚ} {S : Finset ℕ}
    (hf : ∀ i ∈ S, ¬ p ∣ (f i).den) : ¬ p ∣ (∑ i ∈ S, f i).den := by
  classical
  induction S using Finset.induction with
  | empty => simpa using hp.ne_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact not_dvd_add_den hp (hf a (mem_insert_self a s))
      (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- The denominator of `(z : ℚ) / (D : ℚ)` divides `D`, for `z : ℤ` and `D : ℕ`. -/
theorem den_div_dvd (z : ℤ) (D : ℕ) : ((z : ℚ) / (D : ℚ)).den ∣ D := by
  have hcast : (z : ℚ) / (D : ℚ) = Rat.divInt z (D : ℤ) := by
    rw [show ((D : ℚ)) = ((D : ℤ) : ℚ) by push_cast; ring, Rat.intCast_div_eq_divInt]
  rw [hcast]
  have h := Rat.den_dvd z (D : ℤ)
  exact_mod_cast h

/-- If `¬ p ∣ D`, then `p` doesn't divide the denominator of `(z : ℚ) / (D : ℚ)`. -/
theorem not_dvd_div_den {p : ℕ} {z : ℤ} {D : ℕ} (hD : ¬ p ∣ D) :
    ¬ p ∣ ((z : ℚ) / (D : ℚ)).den := fun h => hD (h.trans (den_div_dvd z D))

/-! ## The cancellation theorem -/

/-- The prime-power cancellation step: if `q = p ^ a` is the full power of `p` in the
denominator of the current deficit `u / (q * v)` (with `v` coprime to `p`), and `S` is
a finite set of positive integers coprime to `p` such that
`∑_{m ∈ S} m⁻¹ ≡ u * v⁻¹ (mod q)`, then the corrected deficit
`u / (q * v) - ∑_{m ∈ S} w (q * m)` has denominator coprime to `p`. -/
theorem cancel_step {p a q : ℕ} (hp : p.Prime) (ha : 0 < a) (hq : q = p ^ a)
    {u : ℤ} {v : ℕ} (hv : 0 < v) (hpv : ¬ p ∣ v)
    (S : Finset ℕ) (hS0 : ∀ m ∈ S, 0 < m) (hSp : ∀ m ∈ S, ¬ p ∣ m)
    (hcong : (∑ m ∈ S, ((m : ZMod q)⁻¹)) = (u : ZMod q) * ((v : ZMod q)⁻¹)) :
    ¬ p ∣ ((u : ℚ) / (q * v) - ∑ m ∈ S, w (q * m)).den := by
  classical
  -- basic facts about `q`
  have hpq : p ∣ q := by rw [hq]; exact dvd_pow_self p ha.ne'
  have hq0 : 0 < q := by rw [hq]; exact pow_pos hp.pos a
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hv0' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  -- coprimality facts
  have hcv : Nat.Coprime p v := hp.coprime_iff_not_dvd.mpr hpv
  have hcvq : Nat.Coprime v q := by rw [hq]; exact hcv.symm.pow_right a
  have hcm : ∀ m ∈ S, Nat.Coprime m q := fun m hm => by
    rw [hq]; exact (hp.coprime_iff_not_dvd.mpr (hSp m hm)).symm.pow_right a
  -- `D` is the auxiliary common denominator
  set D : ℕ := v * ∏ m ∈ S, (m * (q * m + 1)) with hDdef
  have hprodpos : 0 < ∏ m ∈ S, (m * (q * m + 1)) :=
    Finset.prod_pos (fun m hm => Nat.mul_pos (hS0 m hm) (Nat.succ_pos _))
  have hDpos : 0 < D := Nat.mul_pos hv hprodpos
  have hD0' : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  -- `p` doesn't divide `q * m + 1` for `m ∈ S`
  have hnf1 : ∀ m ∈ S, ¬ p ∣ (q * m + 1) := by
    intro m hm hcontra
    have hpqm : p ∣ q * m := hpq.mul_right m
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpqm).mp hcontra
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have hnf : ∀ m ∈ S, ¬ p ∣ (m * (q * m + 1)) := fun m hm hcontra =>
    (hp.dvd_mul.mp hcontra).elim (hSp m hm) (hnf1 m hm)
  have hDp : ¬ p ∣ D := fun hcontra =>
    (hp.dvd_mul.mp hcontra).elim hpv (fun h2 => hp.prime.not_dvd_finsetProd hnf h2)
  -- divisibility facts needed for exact natural number division
  have hvD : v ∣ D := dvd_mul_right v _
  have hmD : ∀ m ∈ S, m ∣ D := fun m hm =>
    ((dvd_mul_right m (q * m + 1)).trans
      (Finset.dvd_prod_of_mem (fun k => k * (q * k + 1)) hm)).mul_left v
  have hm1D : ∀ m ∈ S, (q * m + 1) ∣ D := fun m hm =>
    ((dvd_mul_left (q * m + 1) m).trans
      (Finset.dvd_prod_of_mem (fun k => k * (q * k + 1)) hm)).mul_left v
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
      (q : ℤ) * (∑ m ∈ S, ((D / (q * m + 1) : ℕ) : ℤ)) with hNdef
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
  have key2 : ∀ m ∈ S, (q : ℚ) * (D : ℚ) * w (q * m) =
      (D : ℚ) / (m : ℚ) + (q : ℚ) * ((D : ℚ) / ((q * m + 1 : ℕ) : ℚ)) := by
    intro m hm
    have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (hS0 m hm).ne'
    have hqm0 : ((q * m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    unfold w
    push_cast
    field_simp
  have hqDX : (q : ℚ) * (D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, w (q * m)) = (N : ℚ) := by
    rw [mul_sub, key1, Finset.mul_sum, Finset.sum_congr rfl key2,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcv1 : (D : ℚ) / (v : ℚ) = ((D / v : ℕ) : ℚ) := (Nat.cast_div hvD hv0').symm
    have hcm1 : ∀ m ∈ S, (D : ℚ) / (m : ℚ) = ((D / m : ℕ) : ℚ) := fun m hm => by
      have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (hS0 m hm).ne'
      exact (Nat.cast_div (hmD m hm) hm0').symm
    have hcm2 : ∀ m ∈ S, (D : ℚ) / ((q * m + 1 : ℕ) : ℚ) = ((D / (q * m + 1) : ℕ) : ℚ) :=
      fun m hm => by
        have hqm0 : ((q * m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        exact (Nat.cast_div (hm1D m hm) hqm0).symm
    rw [hcv1, Finset.sum_congr rfl hcm1, Finset.sum_congr rfl hcm2, hNdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    ring
  -- conclude
  have hDXeq : (D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, w (q * m)) = (N' : ℚ) := by
    have heq : (q : ℚ) * ((D : ℚ) * ((u : ℚ) / (q * v) - ∑ m ∈ S, w (q * m))) =
        (q : ℚ) * (N' : ℚ) := by
      rw [← mul_assoc, hqDX, hN']
      push_cast
      ring
    exact mul_left_cancel₀ hq0' heq
  have hXeq : (u : ℚ) / (q * v) - ∑ m ∈ S, w (q * m) = (N' : ℚ) / (D : ℚ) := by
    rw [eq_div_iff hD0']
    linear_combination hDXeq
  rw [hXeq]
  exact not_dvd_div_den hDp

/-! ## Bookkeeping: new prime powers introduced by `w` are smaller -/

/-- The denominator of `w n = 1/n + 1/(n+1)` divides `n * (n + 1)`. -/
theorem w_den_dvd (n : ℕ) : (w n).den ∣ n * (n + 1) := by
  have h1 : (((1 : ℤ) : ℚ) / (n : ℚ)).den ∣ n := den_div_dvd 1 n
  have h2 : (((1 : ℤ) : ℚ) / ((n + 1 : ℕ) : ℚ)).den ∣ (n + 1) := den_div_dvd 1 (n + 1)
  have hw : w n = ((1 : ℤ) : ℚ) / (n : ℚ) + ((1 : ℤ) : ℚ) / ((n + 1 : ℕ) : ℚ) := by
    unfold w; push_cast; ring
  rw [hw]
  exact (Rat.add_den_dvd _ _).trans (mul_dvd_mul h1 h2)

/-- If a prime power `p ^ e` divides the denominator of `w n`, it divides `n` or `n + 1`
(since `n` and `n + 1` are coprime, and `p ^ e ∣ n * (n + 1)`). -/
theorem primePow_dvd_den_w {n p e : ℕ} (hp : p.Prime) (h : p ^ e ∣ (w n).den) :
    p ^ e ∣ n ∨ p ^ e ∣ (n + 1) := by
  have hmul : p ^ e ∣ n * (n + 1) := h.trans (w_den_dvd n)
  by_cases hpn : p ∣ n
  · left
    have hnotp1 : ¬ p ∣ (n + 1) := by
      intro hcontra
      have h1 : p ∣ 1 := (Nat.dvd_add_right hpn).mp hcontra
      exact hp.ne_one (Nat.dvd_one.mp h1)
    have hcop : Nat.Coprime (p ^ e) (n + 1) :=
      Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr hnotp1)
    exact hcop.dvd_of_dvd_mul_right hmul
  · right
    have hcop : Nat.Coprime (p ^ e) n := Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr hpn)
    exact hcop.dvd_of_dvd_mul_left hmul
