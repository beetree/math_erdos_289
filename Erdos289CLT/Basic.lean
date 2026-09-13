import Mathlib
import Erdos289.Defs

/-!
# Separated intervals with reciprocal sum one: basic definitions

Formalization of the Cambie–Land–Tang proof (`erdos_289_CLT_proof.tex`).
This file fixes the shared vocabulary: configurations, the groups `G_n`,
the quota `s(q) = ⌈q^{3/4}⌉`, the largest prime-power divisor, and the
elementary separation facts used by every later file.

Conventions.  A rational `x` is "in `G_n`" when `x · D_n ∈ ℤ`, where
`D_n = lcm(1,…,n)`; this is the predicate `InG n x` on `ℚ` standing for
membership of the class of `x` in `D_n⁻¹ℤ/ℤ ⊂ ℚ/ℤ`.  Intervals are
`Erdos289.Iv` (inclusive endpoints) with reciprocal mass `Iv.mass` and the
symmetric separation `Iv.Sep` from `Erdos289.Defs`.
-/

namespace Erdos289.CLT

open Finset

/-- Length of an integer interval. -/
def ivLen (I : Iv) : ℕ := I.hi + 1 - I.lo

/-- `D n = lcm(1, …, n)`. -/
abbrev D (n : ℕ) : ℕ := Nat.lcmUpto n

/-- `x ∈ G_n = D_n⁻¹ℤ/ℤ`, as a predicate on rationals. -/
def InG (n : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, x * (D n : ℚ) = z

/-- The quota `s(q) = ⌈q^{3/4}⌉`. -/
noncomputable def s (q : ℕ) : ℕ := ⌈(q : ℝ) ^ ((3 : ℝ) / 4)⌉₊

/-- The largest prime power dividing `n` (`0` if there is none, e.g. `n = 1`). -/
def lpp (n : ℕ) : ℕ := ((range (n + 1)).filter (fun d => IsPrimePow d ∧ d ∣ n)).sup id

/-- The companion of `q m` in the pair `[lo, lo + 1]` (the other element). -/
def companion (q lo m : ℕ) : ℕ := 2 * lo + 1 - q * m

/-- The centre of the pair `[lo, lo+1]` at stage `q`: `q m` for even `q`, the companion
for odd `q`. -/
def ctr (q lo m : ℕ) : ℕ := if Even q then q * m else companion q lo m

/-- A configuration: a finite family of integer intervals inside `{2, 3, …}`,
each of length at least two, pairwise separated by at least one unused integer. -/
structure Config where
  F : Finset Iv
  two_le : ∀ I ∈ F, 2 ≤ I.lo
  len_ge : ∀ I ∈ F, I.lo + 1 ≤ I.hi
  sep : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Iv.Sep I J

namespace Config

/-- The reciprocal sum `w(F)`. -/
def w (C : Config) : ℚ := ∑ I ∈ C.F, I.mass

/-- The number of intervals `ν(F)`. -/
def nu (C : Config) : ℕ := C.F.card

end Config

/-- Theorem `main` of the paper: every sufficiently large `k` admits a configuration
with `k` intervals and reciprocal sum `1`; all intervals have length `2`, `3` or `4`,
and those longer than two belong to a fixed finite set `S` independent of `k`. -/
def MainStatement : Prop :=
  ∃ S : Finset Iv, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ C : Config, C.nu = k ∧ C.w = 1 ∧
      (∀ I ∈ C.F, ivLen I ≤ 4) ∧ (∀ I ∈ C.F, ivLen I ≠ 2 → I ∈ S)

/-! ## Masses -/

theorem mass_nonneg (I : Iv) : 0 ≤ I.mass := by
  unfold Iv.mass Erdos289.mass
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem mass_pos {I : Iv} (h1 : 1 ≤ I.lo) (h2 : I.lo ≤ I.hi) : 0 < I.mass := by
  unfold Iv.mass Erdos289.mass
  refine Finset.sum_pos' (fun _ _ => by positivity) ⟨I.lo, Finset.mem_Icc.mpr ⟨le_refl _, h2⟩, ?_⟩
  positivity

theorem pair_mass (a : ℕ) : (Iv.pair a).mass = 1 / (a : ℚ) + 1 / ((a : ℚ) + 1) := by
  simp only [Iv.pair, Iv.mass, Erdos289.mass]
  exact mass_pair a

theorem triple_mass (a : ℕ) :
    (Iv.triple a).mass = 1 / (a : ℚ) + 1 / ((a : ℚ) + 1) + 1 / ((a : ℚ) + 2) := by
  show Erdos289.mass a (a + 2) = _
  rw [Erdos289.mass_triple, Erdos289.w]
  push_cast
  ring

theorem pair_mass_le {a : ℕ} (ha : 1 ≤ a) : (Iv.pair a).mass ≤ 2 / (a : ℚ) := by
  rw [pair_mass]
  have hinv : (1 : ℚ) / ((a : ℚ) + 1) ≤ 1 / (a : ℚ) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc (1 : ℚ) / (a : ℚ) + 1 / ((a : ℚ) + 1)
      = 1 / ((a : ℚ) + 1) + 1 / (a : ℚ) := add_comm _ _
    _ ≤ 1 / (a : ℚ) + 1 / (a : ℚ) := add_le_add_left hinv _
    _ = 2 / (a : ℚ) := by ring

/-- The mass of a pair `{a, a+1}` is at most `2/a`, in real form. -/
theorem pair_mass_le_real {a : ℕ} (ha : 1 ≤ a) : ((Iv.pair a).mass : ℝ) ≤ 2 / (a : ℝ) := by
  rw [pair_mass]
  push_cast
  have hrinv : (1 : ℝ) / ((a : ℝ) + 1) ≤ 1 / (a : ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.le_succ a)
  calc (1 : ℝ) / (a : ℝ) + 1 / ((a : ℝ) + 1)
      = 1 / ((a : ℝ) + 1) + 1 / (a : ℝ) := add_comm _ _
    _ ≤ 1 / (a : ℝ) + 1 / (a : ℝ) := add_le_add_left hrinv _
    _ = 2 / (a : ℝ) := by ring

/-! ## Separation -/

/-- Intervals lying in distinct blocks `[a-1, a+2]`, `[b-1, b+2]` with `8 ∣ a`, `8 ∣ b`,
`a ≠ b` are separated. -/
theorem sep_of_blocks {I J : Iv} {a b : ℕ} (ha : 8 ∣ a) (hb : 8 ∣ b) (hab : a ≠ b)
    (hI : a ≤ I.lo + 1 ∧ I.hi ≤ a + 2) (hJ : b ≤ J.lo + 1 ∧ J.hi ≤ b + 2) : Iv.Sep I J := by
  have ha0 : a % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp ha
  have hb0 : b % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp hb
  rcases lt_trichotomy a b with hlt | rfl | hlt
  · left
    have h8 : a + 8 ≤ b := by omega
    omega
  · exact absurd rfl hab
  · right
    have h8 : b + 8 ≤ a := by omega
    omega

/-- An interval ending at most at `6` is separated from one starting at `8` or later. -/
theorem sep_small {I J : Iv} (hI : I.hi ≤ 6) (hJ : 8 ≤ J.lo) : Iv.Sep I J := by
  left; omega

theorem Sep.ne {I J : Iv} (h : Iv.Sep I J) (hI : I.lo ≤ I.hi) (hJ : J.lo ≤ J.hi) : I ≠ J := by
  intro hEq
  subst hEq
  rcases h with h | h
  · omega
  · omega

theorem pair_sep_pair {a b : ℕ} (h : a + 3 ≤ b) : Iv.Sep (Iv.pair a) (Iv.pair b) := by
  show Iv.Sep ⟨a, a + 1⟩ ⟨b, b + 1⟩
  exact Or.inl h

/-- Separation passes to subintervals. -/
theorem Sep.of_sub {I J J' : Iv} (h : Iv.Sep I J) (hJ' : J.lo ≤ J'.lo ∧ J'.hi ≤ J.hi) :
    Iv.Sep I J' := by
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## The groups `G_n` -/

theorem D_pos (n : ℕ) : 0 < D n := Nat.lcmUpto_pos n

theorem D_dvd_D {n n' : ℕ} (h : n ≤ n') : D n ∣ D n' := by
  unfold D Nat.lcmUpto
  refine Finset.lcm_dvd (fun m hm => Finset.dvd_lcm ?_)
  simpa using Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, ((Finset.mem_Icc.mp hm).2).trans h⟩

/-- `a ∣ D n` iff every prime power dividing `a` is at most `n`. -/
theorem dvd_D_iff {n a : ℕ} (ha : 0 < a) : a ∣ D n ↔ Powersmooth n a := by
  have hD := D_pos n
  have hD0 : D n ≠ 0 := hD.ne'
  constructor
  · intro hdiv p e hp he0 hpow
    have h : p ^ e ∣ D n := hpow.trans hdiv
    have hfac : e ≤ (D n).factorization p := by
      exact (hp.pow_dvd_iff_le_factorization hD0).mp h
    rw [Nat.factorization_lcmUpto n hp] at hfac
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : a ∣ 1 := by
        simpa [D, Nat.lcmUpto] using hdiv
      have h1eq : a = 1 := Nat.dvd_one.mp h1
      subst h1eq
      have hpeq := Nat.dvd_one.mp hpow
      exact absurd ((pow_eq_one_iff.mp hpeq).resolve_right he0.ne') hp.ne_one
    exact (Nat.le_log_iff_pow_le hp.one_lt hn0).mp hfac
  · intro hps
    have hiff : a.factorization ≤ (D n).factorization ↔ a ∣ D n := by
      exact @Nat.factorization_le_iff_dvd a (D n) (show a ≠ 0 by omega) hD0
    refine hiff.mp ?_
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_lcmUpto n hp]
      by_cases h0 : a.factorization p = 0
      · simp [h0]
      · have he0 : 0 < a.factorization p := by omega
        have hpow : p ^ (a.factorization p) ∣ a := Nat.ordProj_dvd a p
        have hle : p ^ (a.factorization p) ≤ n := hps p _ hp he0 hpow
        have hnpos : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) hle
        exact (Nat.le_log_iff_pow_le hp.one_lt hnpos.ne').mpr hle
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `D (n+1) = D n` unless `n + 1` is a prime power. -/
theorem D_succ_of_not_isPrimePow {n : ℕ} (h : ¬ IsPrimePow (n + 1)) : D (n + 1) = D n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [D, Nat.lcmUpto]
  apply Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _) (Nat.lcmUpto_ne_zero _)
  intro p
  by_cases hp : Nat.Prime p
  · show (Nat.lcmUpto (n + 1)).factorization p = (Nat.lcmUpto n).factorization p
    rw [Nat.factorization_lcmUpto (n + 1) hp, Nat.factorization_lcmUpto n hp]
    have hiff := Nat.log_eq_log_succ_iff hp.one_lt hn0.ne'
    refine (hiff.mpr ?_).symm
    intro heq
    have hpos : 0 < Nat.log p (n + 1) := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0, pow_zero] at heq
      omega
    exact h ((isPrimePow_nat_iff _).mpr ⟨p, Nat.log p (n + 1), hp, hpos, heq⟩)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem InG.add {n : ℕ} {x y : ℚ} (hx : InG n x) (hy : InG n y) : InG n (x + y) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  exact ⟨z + w, by rw [add_mul, hz, hw]; push_cast; ring⟩

theorem InG.neg {n : ℕ} {x : ℚ} (hx : InG n x) : InG n (-x) := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨-z, by rw [neg_mul, hz]; push_cast; ring⟩

theorem InG.sub {n : ℕ} {x y : ℚ} (hx : InG n x) (hy : InG n y) : InG n (x - y) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  exact ⟨z - w, by rw [sub_mul, hz, hw]; push_cast; ring⟩

theorem InG_intCast (n : ℕ) (z : ℤ) : InG n (z : ℚ) := by
  exact ⟨z * (D n : ℤ), by push_cast; ring⟩

theorem InG_zero (n : ℕ) : InG n 0 := by
  exact ⟨0, by simp⟩

theorem InG.mono {n n' : ℕ} (h : n ≤ n') {x : ℚ} (hx : InG n x) : InG n' x := by
  obtain ⟨k, hk⟩ := D_dvd_D h
  obtain ⟨z, hz⟩ := hx
  refine ⟨z * k, ?_⟩
  rw [hk]
  push_cast
  rw [← mul_assoc, hz]

theorem InG_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, InG n (f i)) :
    InG n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact InG_zero n
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem InG_one_div_iff {n a : ℕ} (ha : 0 < a) : InG n (1 / (a : ℚ)) ↔ a ∣ D n := by
  have hapos : (0 : ℚ) < (a : ℚ) := by positivity
  constructor
  · rintro ⟨z, hz⟩
    have hcast : ((D n : ℕ) : ℚ) = (z : ℚ) * (a : ℚ) := by
      rw [← hz]
      field_simp
    have hprod : (0 : ℚ) ≤ (z : ℚ) * (a : ℚ) := by
      rw [← hcast]
      positivity
    have hz0 : 0 ≤ z := Int.cast_nonneg_iff.mp ((mul_nonneg_iff_of_pos_right hapos).mp hprod)
    have hzi : ((z.toNat : ℤ) : ℚ) = (z : ℚ) := by
      exact congrArg Int.cast (Int.toNat_of_nonneg hz0)
    have hzint : ((z.toNat : ℕ) : ℚ) = (z : ℚ) := hzi
    have hnat : ((D n : ℕ) : ℚ) = ((a * z.toNat : ℕ) : ℚ) := by
      rw [hcast, ← hzint]
      push_cast
      ring
    exact ⟨z.toNat, Nat.cast_injective hnat⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    field_simp

theorem InG_one_div_of_powersmooth {n a : ℕ} (ha : 0 < a) (h : Powersmooth n a) :
    InG n (1 / (a : ℚ)) :=
  (InG_one_div_iff ha).2 ((dvd_D_iff ha).2 h)

/-- Every element of `G_n` lies in `[0,1)` after subtracting its integer part. -/
theorem InG_fract {n : ℕ} {x : ℚ} (hx : InG n x) : InG n (Int.fract x) := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨z - Int.floor x * (D n : ℤ), by
    rw [Int.fract, sub_mul, hz]
    push_cast
    ring⟩

/-- Passing from `G_q` to `G_{q-1}`: every `x ∈ G_q` is `j/q` plus an element of `G_{q-1}`. -/
theorem InG_step {q : ℕ} (hq : 0 < q) {x : ℚ} (hx : InG q x) :
    ∃ j : ℤ, InG (q - 1) (x - (j : ℚ) / q) := by
  have hset : Icc 1 q = insert q (Icc 1 (q - 1)) := by
    ext a
    simp only [mem_Icc, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge a q with hlt | hle
      · exact Or.inr ⟨h1, by omega⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, by omega⟩
      · exact ⟨h1, by omega⟩
  have hDq : D q = Nat.lcm (D (q - 1)) q := by
    unfold D Nat.lcmUpto
    rw [hset, Finset.lcm_insert]
    exact Nat.lcm_comm q ((Icc 1 (q - 1)).lcm id)
  set p : ℕ := D (q - 1) with hpp
  set A : ℤ := Nat.gcdA p q with hA
  set B : ℤ := Nat.gcdB p q with hB
  set g : ℕ := Nat.gcd p q with hg
  have hprod : g * D q = p * q := by
    rw [hDq, hg, Nat.gcd_mul_lcm]
  have hp0 : (0 : ℚ) < (p : ℕ) := by
    have := D_pos (q - 1)
    positivity
  have hD0 : (0 : ℚ) < (D q : ℚ) := by
    have := D_pos q
    positivity
  have hbez : ((g : ℕ) : ℚ) = ((p : ℕ) : ℚ) * A + (q : ℚ) * B := by
    exact_mod_cast Nat.gcd_eq_gcd_ab p q
  have hb2 : (A : ℚ) * ((p : ℕ) : ℚ) + (q : ℚ) * B = ((g : ℕ) : ℚ) := by
    rw [hbez]
    ring
  have hkey : ((1 : ℚ) / (D q : ℚ)) = (A : ℚ) / (q : ℚ) + (B : ℚ) / ((p : ℕ) : ℚ) := by
    have hc : ((g : ℚ) * (D q : ℚ)) = ((p : ℕ) : ℚ) * (q : ℚ) := by
      exact_mod_cast hprod
    field_simp
    rw [hb2, mul_comm ((q : ℕ) : ℚ) ((p : ℕ) : ℚ), ← hc]
    ring
  obtain ⟨z, hz⟩ := hx
  have hxval : x = (z : ℚ) / (D q : ℚ) := by
    exact (eq_div_iff hD0.ne').mpr hz
  refine ⟨z * A, ?_⟩
  have hmem : InG (q - 1) ((z : ℚ) * (B : ℚ) / ((p : ℕ) : ℚ)) := by
    refine ⟨z * B, ?_⟩
    field_simp
    rw [← hpp]
    push_cast
    exact mul_comm ((z : ℚ) * (B : ℚ)) ((p : ℕ) : ℚ)
  have heq : x - (z : ℚ) * (A : ℚ) / (q : ℚ) = (z : ℚ) * (B : ℚ) / ((p : ℕ) : ℚ) := by
    rw [hxval, show ((z : ℚ) / (D q : ℚ)) = (z : ℚ) * ((1 : ℚ) / (D q : ℚ)) by ring, hkey]
    field_simp
    ring
  rw [Int.cast_mul (z : ℤ) (A : ℤ), heq]
  exact hmem

/-- If `n+1` is not a prime power then `G_{n+1} = G_n`. -/
theorem InG_succ_iff_of_not_isPrimePow {n : ℕ} (h : ¬ IsPrimePow (n + 1)) {x : ℚ} :
    InG (n + 1) x ↔ InG n x := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := hx
    rw [D_succ_of_not_isPrimePow h] at hz
    exact ⟨z, hz⟩
  · intro hx
    exact hx.mono (by omega)

/-- Every rational lies in some `G_n`. -/
theorem exists_InG (x : ℚ) : ∃ n : ℕ, InG n x := by
  refine ⟨x.den, ?_⟩
  have hdvd : x.den ∣ D x.den :=
    Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨x.pos, Nat.le_refl _⟩)
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨x.num * k, ?_⟩
  rw [hk]
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

/-! ## The quota `s` -/

theorem s_pos {q : ℕ} (hq : 0 < q) : 0 < s q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hexp : (0 : ℝ) < (3 : ℝ) / 4 := by norm_num
  unfold s
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hq0 ((3 : ℝ) / 4))

theorem s_mono {q q' : ℕ} (h : q ≤ q') : s q ≤ s q' := by
  have hexp : (0 : ℝ) ≤ (3 : ℝ) / 4 := by norm_num
  have hstep : (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (q' : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) (Nat.cast_le.mpr h) hexp
  unfold s
  exact Nat.ceil_le.mpr (hstep.trans (Nat.le_ceil _))

theorem s_two_mul_le (q : ℕ) : s (2 * q) ≤ 2 * s q := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqpow : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hq0 _
  have hbase : ((1 : ℝ) ≤ ((2 : ℕ) : ℝ)) := by norm_num
  have hexp : ((3 : ℝ) / 4) ≤ 1 := by norm_num
  have h2base : ((2 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 :=
    Real.rpow_le_self_of_one_le hbase hexp
  have h1 : ((2 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) * ((q : ℝ) ^ ((3 : ℝ) / 4)) ≤
      (2 : ℝ) * ((q : ℝ) ^ ((3 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_right h2base hqpow
  have h2 : ((2 * q : ℕ) : ℝ) ^ ((3 : ℝ) / 4) =
      ((2 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) * ((q : ℝ) ^ ((3 : ℝ) / 4)) := by
    push_cast
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hq0
  unfold s
  refine Nat.ceil_le.mpr ?_
  rw [h2, Nat.cast_mul]
  exact le_trans (mul_le_mul_of_nonneg_right h2base hqpow)
    (mul_le_mul_of_nonneg_left (Nat.le_ceil ((q : ℝ) ^ ((3 : ℝ) / 4)))
      (by norm_num : (0 : ℝ) ≤ 2))

theorem rpow_le_s (q : ℕ) : (q : ℝ) ^ ((3 : ℝ) / 4) ≤ s q := by
  unfold s
  exact Nat.le_ceil _

theorem s_le_rpow_add_one (q : ℕ) : (s q : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 4) + 1 := by
  unfold s
  exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg q) ((3 : ℝ) / 4)))

/-! ## Largest prime-power divisor -/

theorem lpp_eq {q n : ℕ} (hq : IsPrimePow q) (hqn : q ∣ n) (hn : 0 < n)
    (hps : Powersmooth q n) : lpp n = q := by
  unfold lpp
  have hqnle : q ≤ n := Nat.le_of_dvd hn hqn
  have hmem : q ∈ (range (n + 1)).filter (fun d => IsPrimePow d ∧ d ∣ n) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨hq, hqn⟩⟩
  refine le_antisymm (Finset.sup_le (fun d hd => ?_)) ?_
  · obtain ⟨_, hd2⟩ := Finset.mem_filter.mp hd
    obtain ⟨hp, hd3⟩ := hd2
    obtain ⟨p, e, hpp, hpe, rfl⟩ := (isPrimePow_nat_iff d).mp hp
    exact hps p e hpp (by omega) hd3
  · exact Finset.le_sup (f := id) hmem

/-- The prime powers `q ≤ n` all divide `D n`; conversely every prime power dividing
`q * m` with `m < q` and `p ∤ m` is at most `q`. -/
theorem powersmooth_mul_of_lt {p α m : ℕ} (hp : p.Prime) (_hα : 0 < α)
    (hm : m < p ^ α) (hpm : ¬ p ∣ m) (hm0 : 0 < m) : Powersmooth (p ^ α) (p ^ α * m) := by
  intro ℓ e hℓ he0 hdvd
  by_cases hℓp : ℓ = p
  · subst hℓp
    have hprime : _root_.Prime ℓ := Nat.prime_iff.mp hp
    have hd : ℓ ^ e ∣ ℓ ^ α :=
      Prime.pow_dvd_of_dvd_mul_right hprime e hpm hdvd
    exact Nat.le_of_dvd (Nat.pow_pos hp.pos) hd
  · have hc : Nat.Coprime (ℓ ^ e) (p ^ α) := Nat.coprime_pow_primes _ _ hℓ hp hℓp
    have hd : ℓ ^ e ∣ m := hc.dvd_of_dvd_mul_left hdvd
    obtain ⟨c, hc⟩ := hd
    have hc0 : 0 < c := by
      have : c ≠ 0 := by
        rintro rfl
        exact hm0.ne hc.symm
      exact Nat.pos_of_ne_zero this
    have hle : ℓ ^ e ≤ m := by
      rw [hc]
      exact Nat.le_mul_of_pos_right _ hc0
    exact le_trans hle hm.le

/-! ## Configurations -/

theorem Config.w_pos (C : Config) (h : C.F.Nonempty) : 0 < C.w := by
  unfold Config.w
  refine Finset.sum_pos (fun I hI => ?_) h
  have hle : I.lo ≤ I.hi := by
    have := C.len_ge I hI
    omega
  exact mass_pos (by have := C.two_le I hI; omega) hle

theorem Config.lo_le_hi (C : Config) {I : Iv} (hI : I ∈ C.F) : I.lo ≤ I.hi := by
  have := C.len_ge I hI
  omega

