import Erdos289CLT.Basic
import Erdos289.External

/-!
# Chebyshev's lower bound and primes in `(x/D, x/16)`

`primeCounting_lower` is `π(x) ≫ x / log x` (e.g. from the central binomial
coefficient: `4^n < n · C(2n,n)` and `C(2n,n) ≤ (2n)^{π(2n)}` via
`Nat.pow_factorization_choose_le`).  Together with an upper bound
`π(x) ≪ x / log x` (derivable from `Chebyshev.theta_le_log4_mul_x` in Mathlib)
it yields `≫ x / log x` primes in `(x/D, x/16)` for a suitable fixed `D`.
-/

namespace Erdos289.CLT

open Finset

theorem log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  have hexp : Real.exp (Real.log 4) = 4 := Real.exp_log (by positivity)
  have h1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by positivity)).mpr h2

theorem centralBinom_le_pow_primeCounting (n : ℕ) :
    (Nat.centralBinom n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ Nat.primeCounting (2 * n) := by
  classical
  set S : Finset ℕ := Nat.primesLE (2 * n) with hS
  have hzero : ∀ p ∈ Finset.range (2 * n + 1), p ∉ S →
      p ^ (Nat.centralBinom n).factorization p = 1 := by
    intro p hp hpS
    by_cases hpP : p.Prime
    · exfalso
      have hp2 : p ≤ 2 * n := by
        have hplt := Finset.mem_range.mp hp
        omega
      exact hpS (Nat.mem_primesLE.mpr ⟨hp2, hpP⟩)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hpP]
  have hsub : S ⊆ Finset.range (2 * n + 1) := by
    intro p hp
    have := Nat.le_of_mem_primesLE hp
    exact Finset.mem_range.mpr (by omega)
  have hprodSrange : (∏ p ∈ S, p ^ (Nat.centralBinom n).factorization p) =
      ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p :=
    Finset.prod_subset hsub hzero
  have hle : ∀ p ∈ S, ((p ^ (Nat.centralBinom n).factorization p : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    intro p hp
    have hp2 : p ≤ 2 * n := Nat.le_of_mem_primesLE hp
    have hpP : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp1 : 2 ≤ p := hpP.two_le
    have hbase : (0 : ℕ) < 2 * n := by omega
    have hfac : p ^ (Nat.centralBinom n).factorization p ≤ 2 * n :=
      @Nat.pow_factorization_choose_le p (2 * n) n hbase
    exact_mod_cast hfac
  have hprodle : ∏ p ∈ S, ((p ^ (Nat.centralBinom n).factorization p : ℕ) : ℝ) ≤
      ((2 * n : ℕ) : ℝ) ^ S.card := by
    have hconst : ∏ p ∈ S, ((2 * n : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) ^ S.card :=
      Finset.prod_const (b := ((2 * n : ℕ) : ℝ))
    refine le_trans (Finset.prod_le_prod (fun p _ => Nat.cast_nonneg _) hle) ?_
    rw [hconst]
  have hcard : S.card = Nat.primeCounting (2 * n) := by
    rw [hS, Nat.primesLE_card_eq_primeCounting]
  calc (Nat.centralBinom n : ℝ)
      = ((∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p : ℕ) : ℝ) :=
        by rw [Nat.prod_pow_factorization_centralBinom]
    _ = ∏ p ∈ S, ((p ^ (Nat.centralBinom n).factorization p : ℕ) : ℝ) := by
        rw [← hprodSrange, Nat.cast_prod]
    _ ≤ ((2 * n : ℕ) : ℝ) ^ S.card := hprodle
    _ = ((2 * n : ℕ) : ℝ) ^ Nat.primeCounting (2 * n) := by rw [hcard]

theorem primeCounting_two_mul_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (2 * n : ℕ) / Real.log (2 * n : ℕ) ≤ (Nat.primeCounting (2 * n) : ℝ) := by
  have hApos : (0 : ℝ) < Real.log 4 - 1 := by linarith [log_four_gt_one]
  refine ⟨(Real.log 4 - 1) / 4, div_pos hApos four_pos, 4, fun n hn => ?_⟩
  set A : ℝ := Real.log 4 - 1 with hAdef
  have hNpos : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (by omega : 0 < 2 * n)
  have hN1 : (1 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (by omega : 1 < 2 * n)
  have hlogpos : 0 < Real.log (2 * n : ℕ) := Real.log_pos hN1
  have hcentral := centralBinom_le_pow_primeCounting n
  have hfour := Nat.four_pow_lt_mul_centralBinom n hn
  have hcast : ((4 ^ n : ℕ) : ℝ) < (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast hfour
  have hlt : ((4 ^ n : ℕ) : ℝ) < (n : ℝ) * ((2 * n : ℕ) : ℝ) ^ Nat.primeCounting (2 * n) := by
    calc ((4 ^ n : ℕ) : ℝ) < (n : ℝ) * (Nat.centralBinom n : ℝ) := hcast
      _ ≤ (n : ℝ) * ((2 * n : ℕ) : ℝ) ^ Nat.primeCounting (2 * n) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
  have hlog : (n : ℝ) * Real.log 4 <
      Real.log (n : ℝ) + (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n : ℕ) := by
    have hpos1 : (0 : ℝ) < ((4 ^ n : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < (n : ℝ) * ((2 * n : ℕ) : ℝ) ^ Nat.primeCounting (2 * n) := by
      positivity
    have hloglt := Real.log_lt_log hpos1 hlt
    rw [Nat.cast_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at hloglt
    exact hloglt
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have hn0 : (0 : ℕ) < n := by omega
    have h := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
    linarith
  have hkey0 : (A / 2) * n ≤ (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * n : ℕ) := by
    rw [hAdef]
    nlinarith
  have hkey := hkey0
  have htarget : A * (n : ℝ) / (2 * Real.log (2 * n : ℕ)) ≤
      (Nat.primeCounting (2 * n) : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (2 * n : ℕ))]
    linarith [hAdef]
  have hEq : ((A / 4) * (2 * n : ℕ) : ℝ) / Real.log (2 * n : ℕ) =
      A * (n : ℝ) / (2 * Real.log (2 * n : ℕ)) := by
    push_cast
    ring
  rw [hEq]
  exact htarget

theorem primeCounting_lower : ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x / Real.log x ≤ (Nat.primeCounting x : ℝ) := by
  obtain ⟨c, hc, n₀, hn⟩ := primeCounting_two_mul_lower
  refine ⟨c / 2, by positivity, 2 * n₀ + 4, fun x hx => ?_⟩
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk := hn k (by omega)
    rw [show (2 : ℕ) * k = k + k from by omega] at hk
    have hcast : (((k + k : ℕ) : ℝ)) = 2 * (k : ℝ) := by push_cast; ring
    have hnum : (c / 2) * (2 * (k : ℝ)) ≤ c * (2 * (k : ℝ)) := by
      nlinarith [hc.le]
    set L : ℝ := Real.log ((k + k : ℕ) : ℝ) with hL
    have hLpos : (0 : ℝ) < L := by
      rw [hL]
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < k + k))
    have hfrac : (c / 2) * (2 * (k : ℝ)) / L ≤ c * (2 * (k : ℝ)) / L := by
      exact (div_le_div_iff₀ hLpos hLpos).mpr (mul_le_mul_of_nonneg_right hnum hLpos.le)
    rw [hcast] at hk
    have hk2 : c * (2 * (k : ℝ)) / L ≤ (Nat.primeCounting (k + k) : ℝ) := hk
    calc (c / 2) * ((k + k : ℕ) : ℝ) / Real.log ((k + k : ℕ) : ℝ)
        = (c / 2) * (2 * (k : ℝ)) / Real.log ((k + k : ℕ) : ℝ) := by rw [hcast]
      _ ≤ c * (2 * (k : ℝ)) / Real.log ((k + k : ℕ) : ℝ) := hfrac
      _ ≤ (Nat.primeCounting (k + k) : ℝ) := hk2
  · have hk := hn k (by omega)
    have hk1 : (1 : ℕ) ≤ k := by omega
    have hk1real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hygt : (1 : ℝ) < ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 < 2 * k)
    have hxgt : (1 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 < 2 * k + 1)
    have hlogxpos : 0 < Real.log ((2 * k + 1 : ℕ) : ℝ) :=
      Real.log_pos hxgt
    have hlogypos : 0 < Real.log ((2 * k : ℕ) : ℝ) :=
      Real.log_pos hygt
    have hlogle : Real.log ((2 * k : ℕ) : ℝ) ≤ Real.log ((2 * k + 1 : ℕ) : ℝ) := by
      exact Real.log_le_log (lt_trans zero_lt_one hygt)
        (by exact_mod_cast (by omega : (2 : ℕ) * k ≤ 2 * k + 1))
    have hmono := Nat.monotone_primeCounting (show (2 : ℕ) * k ≤ 2 * k + 1 by omega)
    have hcastA : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    have hcastB : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
    have hnum : (c / 2) * (2 * (k : ℝ) + 1) ≤ c * (2 * (k : ℝ)) := by
      nlinarith [hc.le, hk1real]
    have hnum2 : (c / 2) * ((2 * k + 1 : ℕ) : ℝ) ≤ c * ((2 * k : ℕ) : ℝ) := by
      rw [hcastA, hcastB]; exact hnum
    have hcomp1 : (c / 2) * ((2 * k + 1 : ℕ) : ℝ) / Real.log ((2 * k + 1 : ℕ) : ℝ) ≤
        c * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k + 1 : ℕ) : ℝ) := by
      exact (div_le_div_iff₀ hlogxpos hlogxpos).mpr
        (mul_le_mul_of_nonneg_right hnum2 hlogxpos.le)
    have hcomp2 : c * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k + 1 : ℕ) : ℝ) ≤
        c * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left (by positivity) hlogypos hlogle
    calc (c / 2) * ((2 * k + 1 : ℕ) : ℝ) / Real.log ((2 * k + 1 : ℕ) : ℝ)
        ≤ c * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k + 1 : ℕ) : ℝ) := hcomp1
      _ ≤ c * ((2 * k : ℕ) : ℝ) / Real.log ((2 * k : ℕ) : ℝ) := hcomp2
      _ ≤ (Nat.primeCounting (2 * k) : ℝ) := hk
      _ ≤ (Nat.primeCounting (2 * k + 1) : ℝ) := by exact_mod_cast hmono

theorem primeCounting_upper : ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
    (Nat.primeCounting x : ℝ) ≤ C * x / Real.log x := by
  obtain ⟨C, hC⟩ := Erdos289.primeCounting_le
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hxpos : (0 : ℝ) ≤ (x : ℝ) := by positivity
  refine le_trans (hC x hx) ?_
  gcongr
  · exact le_max_left C 1

theorem primeCounting_ioc_card {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card = Nat.primeCounting b := by
  have hIccIic : ∀ n : ℕ, Finset.Icc 0 n = Finset.Iic n := by
    intro n; ext p; simp
  have ha : Nat.primesLE a = Finset.filter Nat.Prime (Finset.Iic a) := by
    rw [Nat.primesLE_eq_filter_Icc_zero, hIccIic]
  have hb : Nat.primesLE b = Finset.filter Nat.Prime (Finset.Iic b) := by
    rw [Nat.primesLE_eq_filter_Icc_zero, hIccIic]
  have hunion : Finset.Iic b = Finset.Iic a ∪ Finset.Ioc a b := (Finset.Iic_union_Ioc_eq_Iic hab).symm
  have hdisj : Disjoint (Finset.Iic a) (Finset.Ioc a b) := Finset.Iic_disjoint_Ioc (le_refl a)
  have hcard : (Finset.filter Nat.Prime (Finset.Iic b)).card =
      (Finset.filter Nat.Prime (Finset.Iic a)).card + (Finset.filter Nat.Prime (Finset.Ioc a b)).card := by
    rw [hunion, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  rw [← Nat.primesLE_card_eq_primeCounting a, ← Nat.primesLE_card_eq_primeCounting b, ha, hb]
  omega

theorem card_Ioc_le_card_Ioo_succ (a b : ℕ) :
    ((Finset.Ioc a b).filter Nat.Prime).card ≤ ((Finset.Ioo a b).filter Nat.Prime).card + 1 := by
  have hsub : Finset.Ioc a b ⊆ insert b (Finset.Ioo a b) := by
    intro p hp
    rcases eq_or_ne p b with rfl | hne
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioc.mp hp).1,
          lt_of_le_of_ne (Finset.mem_Ioc.mp hp).2 hne⟩)
  have h1 : (Finset.Ioc a b).filter Nat.Prime ⊆ insert b ((Finset.Ioo a b).filter Nat.Prime) := by
    intro p hp
    have hp' := Finset.mem_of_mem_filter p hp
    have hpP := (Finset.mem_filter.mp hp).2
    rcases Finset.mem_insert.mp (hsub hp') with rfl | hp''
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp'', hpP⟩)
  calc ((Finset.Ioc a b).filter Nat.Prime).card
      ≤ (insert b ((Finset.Ioo a b).filter Nat.Prime)).card := Finset.card_le_card h1
    _ ≤ ((Finset.Ioo a b).filter Nat.Prime).card + 1 := Finset.card_insert_le _ _

theorem nat_div_cast_lower (m n : ℕ) (hn : 0 < n) :
    (m : ℝ) / n - 1 < ((m / n : ℕ) : ℝ) := by
  have hdm : m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
  have hmod : m % n < n := Nat.mod_lt m hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_sub_one hn'.ne', div_lt_iff₀ hn']
  have heq : (m : ℝ) = (n : ℝ) * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by exact_mod_cast hdm
  have hmod' : ((m % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
  nlinarith

set_option maxHeartbeats 1600000 in
/-- For a suitable fixed `Dc > 16`, the open range `(x/Dc, x/16)` (natural-number
division) contains `≫ x / log x` primes. -/
theorem primes_in_range : ∃ Dc : ℕ, 16 < Dc ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c₁ * x / Real.log x ≤ (((Finset.Ioo (x / Dc) (x / 16)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨c, hc, x₀lo, hlo⟩ := primeCounting_lower
  obtain ⟨C, hC, hup⟩ := primeCounting_upper
  set Dc : ℕ := max 17 (⌈128 * C / c⌉₊ + 1) with hDcdef
  have hDc16 : 16 < Dc := by
    have : 17 ≤ Dc := le_max_left _ _
    omega
  have hDc0 : (0 : ℕ) < Dc := by omega
  have hDcC : 128 * C / c ≤ (Dc : ℝ) := by
    have h1 : (⌈128 * C / c⌉₊ : ℕ) + 1 ≤ Dc := le_max_right _ _
    have h2 : (128 * C / c : ℝ) ≤ (⌈128 * C / c⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈128 * C / c⌉₊ : ℕ) : ℝ) + 1 ≤ (Dc : ℝ) := by exact_mod_cast h1
    linarith
  set X0 : ℝ := max (max (max (max (32 : ℝ) (2 * (Dc : ℝ)))
      ((2 * (Dc : ℝ)) ^ 2 + 1)) ((256 / c) ^ 2 + 1)) (16 * ((x₀lo : ℝ) + 1)) with hX0def
  refine ⟨Dc, hDc16, c / 128, by positivity, ⌈X0⌉₊ + 1, fun x hx => ?_⟩
  have hXge : X0 ≤ (x : ℝ) := by
    have h1 : (⌈X0⌉₊ : ℕ) + 1 ≤ x := hx
    have h2 : X0 ≤ (⌈X0⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈X0⌉₊ : ℕ) : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast h1
    linarith
  set X : ℝ := (x : ℝ) with hXdef
  have hX32 : (32 : ℝ) ≤ X := by
    refine le_trans ?_ hXge
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
  have hX2Dc : 2 * (Dc : ℝ) ≤ X := by
    refine le_trans ?_ hXge
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
  have hXDcsq : (2 * (Dc : ℝ)) ^ 2 + 1 ≤ X := by
    refine le_trans ?_ hXge
    exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hXcsq : (256 / c) ^ 2 + 1 ≤ X := by
    refine le_trans ?_ hXge
    exact le_max_of_le_left (le_max_right _ _)
  have hXlo : 16 * ((x₀lo : ℝ) + 1) ≤ X := by
    refine le_trans ?_ hXge
    exact le_max_right _ _
  set a : ℕ := x / Dc with hadef
  set b : ℕ := x / 16 with hbdef
  have hab : a ≤ b := Nat.div_le_div_left hDc16.le (by norm_num)
  set A : ℝ := (a : ℝ) with hAdef
  set B : ℝ := (b : ℝ) with hBdef
  have hAub : A ≤ X / Dc := Nat.cast_div_le
  have hAlb : X / Dc - 1 < A := nat_div_cast_lower x Dc hDc0
  have hBub : B ≤ X / 16 := Nat.cast_div_le
  have hBlb : X / 16 - 1 < B := nat_div_cast_lower x 16 (by norm_num)
  -- basic positivity facts
  have hXpos : (0 : ℝ) < X := by linarith
  have hcpos : 0 < c := hc
  have hDcpos : (0 : ℝ) < (Dc : ℝ) := by exact_mod_cast hDc0
  -- `a ≥ 2`
  have ha2 : 2 ≤ a := by
    have h0 : (2 : ℝ) ≤ X / Dc := (le_div_iff₀ hDcpos).mpr (by linarith [hX2Dc])
    have h1 : (1 : ℝ) < A := by linarith
    rw [hAdef] at h1
    have h2 : (1 : ℕ) < a := by exact_mod_cast h1
    omega
  -- `b ≥ x₀lo`
  have hblo : x₀lo ≤ b := by
    have h0 : ((x₀lo : ℝ) + 1) ≤ X / 16 := (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr (by linarith [hXlo])
    have h1 : (x₀lo : ℝ) < B := by linarith
    rw [hBdef] at h1
    have h2 : (x₀lo : ℕ) < b := by exact_mod_cast h1
    omega
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith : (1 : ℝ) < X)
  -- N: the quantity we want to lower-bound
  set N : ℕ := ((Finset.Ioo a b).filter Nat.Prime).card with hNdef
  have hNle : Nat.primeCounting b ≤ Nat.primeCounting a + N + 1 := by
    have e1 := primeCounting_ioc_card hab
    have e2 := card_Ioc_le_card_Ioo_succ a b
    omega
  have hlob := hlo b hblo
  have hupa := hup a ha2
  rw [← hBdef] at hlob
  rw [← hAdef] at hupa
  have hkey : c * B / Real.log B ≤ C * A / Real.log A + (N : ℝ) + 1 := by
    have : (Nat.primeCounting b : ℝ) ≤ (Nat.primeCounting a : ℝ) + (N : ℝ) + 1 := by
      exact_mod_cast hNle
    linarith
  -- term1 : c * B / log B ≥ (c/32) * X / log X
  have hXfrac1 : X / 32 ≤ X / 16 - 1 := by nlinarith [hX32]
  have hBgeX32 : X / 32 ≤ B := by linarith [hBlb]
  have hBpos : 0 < B := by nlinarith [hX32]
  have hBleX : B ≤ X := by nlinarith [hBub, hXpos]
  have hlogBpos : 0 < Real.log B := Real.log_pos (by nlinarith [hBgeX32, hX32])
  have hlogBleX : Real.log B ≤ Real.log X := Real.log_le_log hBpos hBleX
  have hterm1a : B / Real.log X ≤ B / Real.log B :=
    div_le_div_of_nonneg_left hBpos.le hlogBpos hlogBleX
  have hterm1b : X / 32 / Real.log X ≤ B / Real.log X :=
    div_le_div_of_nonneg_right hBgeX32 hlogXpos.le
  have hterm1 : c * (X / 32 / Real.log X) ≤ c * B / Real.log B := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (le_trans hterm1b hterm1a) hc.le
  have hterm1' : (c / 32) * X / Real.log X ≤ c * B / Real.log B := by
    have heq : c * (X / 32 / Real.log X) = (c / 32) * X / Real.log X := by ring
    linarith [hterm1, heq.symm.le, heq.le]
  -- term2 : C * A / log A ≤ (c/64) * X / log X
  have hXeq : X / (2 * (Dc : ℝ)) + X / (2 * (Dc : ℝ)) = X / Dc := by
    field_simp
    ring
  have hh1 : (1 : ℝ) ≤ X / (2 * Dc) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Dc : ℝ))).mpr (by linarith [hX2Dc])
  have hXfrac2 : X / (2 * Dc) ≤ X / Dc - 1 := by linarith [hXeq, hh1]
  have hAgeXDc2 : X / (2 * Dc) ≤ A := by linarith [hAlb, hXfrac2]
  have hXDc2pos : (0 : ℝ) < X / (2 * Dc) := by positivity
  have hApos : 0 < A := lt_of_lt_of_le hXDc2pos hAgeXDc2
  have hDcsqpos : (0 : ℝ) < (2 * (Dc : ℝ)) ^ 2 := by positivity
  have hXDcsq' : (2 * (Dc : ℝ)) ^ 2 ≤ X := by linarith [hXDcsq]
  have hlog2Dcsq : Real.log ((2 * (Dc : ℝ)) ^ 2) ≤ Real.log X :=
    Real.log_le_log hDcsqpos hXDcsq'
  have hlog2Dcpow : Real.log ((2 * (Dc : ℝ)) ^ 2) = 2 * Real.log (2 * (Dc : ℝ)) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog2Dc_le : Real.log (2 * (Dc : ℝ)) ≤ Real.log X / 2 := by linarith [hlog2Dcsq, hlog2Dcpow]
  have hlogAgeXDc2 : Real.log (X / (2 * Dc)) ≤ Real.log A :=
    Real.log_le_log hXDc2pos hAgeXDc2
  have hlogdiv : Real.log (X / (2 * (Dc : ℝ))) = Real.log X - Real.log (2 * (Dc : ℝ)) :=
    Real.log_div hXpos.ne' (by positivity)
  have hlogA_lb : Real.log X / 2 ≤ Real.log A := by
    rw [hlogdiv] at hlogAgeXDc2
    linarith [hlog2Dc_le]
  have hlogApos : 0 < Real.log A := by linarith [hlogA_lb, hlogXpos]
  have hCApos : (0 : ℝ) ≤ C * A := by positivity
  have hCXDcpos : (0 : ℝ) ≤ C * (X / Dc) := by positivity
  have hterm2a : C * A / Real.log A ≤ C * (X / Dc) / Real.log A :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAub hC.le) hlogApos.le
  have hterm2b : C * (X / Dc) / Real.log A ≤ C * (X / Dc) / (Real.log X / 2) :=
    div_le_div_of_nonneg_left hCXDcpos (by linarith [hlogXpos]) hlogA_lb
  have hterm2eq : C * (X / Dc) / (Real.log X / 2) = 2 * C / Dc * X / Real.log X := by
    field_simp
  have hcDc : 128 * C ≤ (Dc : ℝ) * c := by
    have h := hDcC
    rw [div_le_iff₀ hcpos] at h
    linarith [h]
  have hratio : 2 * C / Dc ≤ c / 64 := by
    rw [div_le_div_iff₀ hDcpos (by norm_num : (0 : ℝ) < 64)]
    nlinarith [hcDc]
  have hXlogXnn : (0 : ℝ) ≤ X / Real.log X := by positivity
  have hterm2c : 2 * C / Dc * X / Real.log X ≤ c / 64 * X / Real.log X := by
    have := mul_le_mul_of_nonneg_right hratio hXpos.le
    calc 2 * C / Dc * X / Real.log X = 2 * C / Dc * X / Real.log X := rfl
      _ ≤ c / 64 * X / Real.log X := by
          rw [div_le_div_iff₀ hlogXpos hlogXpos]
          nlinarith [this]
  have hterm2 : C * A / Real.log A ≤ c / 64 * X / Real.log X := by
    calc C * A / Real.log A ≤ C * (X / Dc) / Real.log A := hterm2a
      _ ≤ C * (X / Dc) / (Real.log X / 2) := hterm2b
      _ = 2 * C / Dc * X / Real.log X := hterm2eq
      _ ≤ c / 64 * X / Real.log X := hterm2c
  -- `X / log X` is large: `128 ≤ c * (X / log X)`.
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hlogsqrtX : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hXpos.le
  have hlogXle2sqrt : Real.log X ≤ 2 * Real.sqrt X := by
    have h1 := Real.log_le_sub_one_of_pos hsqrtXpos
    rw [hlogsqrtX] at h1
    linarith
  have hsqrtXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
  have hsqrtXge : 256 / c ≤ Real.sqrt X := by
    have h1 : (256 / c) ^ 2 ≤ X := by linarith [hXcsq]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 256 / c)] at h2
  have hcsqrtX : (256 : ℝ) ≤ c * Real.sqrt X := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtXge hc.le
    have heq : c * (256 / c) = 256 := by field_simp
    linarith [hmul, heq]
  have hcXge : 256 * Real.sqrt X ≤ c * X := by
    nlinarith [hcsqrtX, Real.sqrt_nonneg X, hsqrtXsq]
  have hcXlogX : 128 * Real.log X ≤ c * X := by linarith [hcXge, hlogXle2sqrt]
  have hYbig : (128 : ℝ) ≤ c * (X / Real.log X) := by
    have step : (128 : ℝ) ≤ c * X / Real.log X := (le_div_iff₀ hlogXpos).mpr (by linarith [hcXlogX])
    rwa [mul_div_assoc] at step
  -- combine everything
  have hc32 : c / 32 * X / Real.log X = c / 32 * (X / Real.log X) := by ring
  have hc64 : c / 64 * X / Real.log X = c / 64 * (X / Real.log X) := by ring
  have hc128 : c / 128 * X / Real.log X = c / 128 * (X / Real.log X) := by ring
  rw [hc32] at hterm1'
  rw [hc64] at hterm2
  rw [hc128]
  nlinarith [hterm1', hterm2, hkey, hYbig]

end Erdos289.CLT
