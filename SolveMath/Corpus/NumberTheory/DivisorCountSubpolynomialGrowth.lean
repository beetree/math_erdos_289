module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

/-!
# The divisor-counting function grows subpolynomially

The number `τ(n) = #n.divisors` of positive divisors of `n` satisfies
`τ(n) = n ^ o(1)`: for every `ε > 0`, `τ(n) ≤ n ^ ε` for all large enough `n`.

The proof bounds `τ(n)` by an arbitrary `K`-th root power
`n ^ (1 / K) * K ^ (2 ^ K)` (via a factor-by-factor comparison against the
exact divisor-count product formula, using a Bernoulli-type inequality), then
optimizes the choice of `K` in terms of `log log n` to make the bound
`n ^ (o(1))`.
-/

namespace DivisorCountSubpolynomialGrowth

open Filter Real Asymptotics

noncomputable section

theorem tendsto_log_coe_atTop : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_coe_atTop : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_coe_atTop

theorem divisorCount_le_self {n : ℕ} : (n.divisors.card : ℝ) ≤ n :=
  by exact_mod_cast Nat.card_divisors_le_self n

private theorem exp_sub_mul {x c : ℝ} (hc : 0 ≤ c) : c - c * log c ≤ exp x - c * x := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp [(Real.exp_pos _).le]
  suffices hmain : Real.exp (Real.log c) - c * Real.log c ≤ Real.exp x - c * x by
    rwa [Real.exp_log hc] at hmain
  have h₁ : Differentiable ℝ (fun x ↦ Real.exp x - c * x) :=
    Real.differentiable_exp.sub (differentiable_id.const_mul _)
  have h₂ : ∀ t, deriv (fun y ↦ Real.exp y - c * y) t = Real.exp t - c := by
    intro t
    change deriv (Real.exp - fun y : ℝ ↦ c * y) t = Real.exp t - c
    simpa using ((Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul c)).deriv
  cases le_total (Real.log c) x with
  | inl hx =>
      have hmono : MonotoneOn (fun y ↦ Real.exp y - c * y) (Set.Icc (Real.log c) x) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (Real.log c) x) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonneg, ← Real.log_le_iff_le_exp hc]
            exact hy.1.le
      exact hmono (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx
  | inr hx =>
      have hanti : AntitoneOn (fun y ↦ Real.exp y - c * y) (Set.Icc x (Real.log c)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x (Real.log c)) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonpos, ← Real.le_log_iff_exp_le hc]
            exact hy.2.le
      exact hanti (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx

private theorem div_bound_aux1 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ^ K ≤ n) (h2 : 0 < K) :
    (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) := by
  transitivity (2 : ℝ) ^ (r : ℝ)
  · have hpow : (1 + (1 : ℝ)) ^ r = (2 : ℝ) ^ (r : ℝ) := by norm_num
    rw [← hpow, add_comm]
    simpa using (one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num : -2 ≤ (1 : ℝ)) r)
  · have hnonneg : 0 ≤ (2 : ℝ) ^ K := by positivity
    refine le_trans ?_ (Real.rpow_le_rpow hnonneg h1 ?_)
    · rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_div_cancel₀ _ h2.ne']
    · exact div_nonneg (Nat.cast_nonneg _) h2.le

private theorem bernoulli_aux (x : ℝ) : x + 1 / 2 ≤ 2 ^ x := by
  have h : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have h₁ :
      1 / Real.log 2 - 1 / Real.log 2 * Real.log (1 / Real.log 2) ≤
        Real.exp (Real.log 2 * x) - 1 / Real.log 2 * (Real.log 2 * x) := by
    apply exp_sub_mul
    simp only [one_div, inv_nonneg]
    exact h.le
  rw [Real.rpow_def_of_pos zero_lt_two, ← le_sub_iff_add_le']
  rw [← mul_assoc, div_mul_cancel₀ _ h.ne', one_mul] at h₁
  apply le_trans ?_ h₁
  rw [one_div (Real.log 2), Real.log_inv]
  simp only [one_div, mul_neg, sub_neg_eq_add]
  suffices h2 : Real.log 2 / 2 - 1 ≤ Real.log (Real.log 2) by
    field_simp [h]
    linarith
  transitivity (-1 / 2 : ℝ)
  · linarith [Real.log_two_lt_d9]
  · have hlog : (-1 : ℝ) ≤ 2 * Real.log (Real.log 2) := by
      simpa [Real.log_rpow h] using
        (Real.le_log_iff_exp_le (Real.rpow_pos_of_pos h _)).2 (by
          apply Real.exp_neg_one_lt_d9.le.trans
          apply le_trans _ (Real.rpow_le_rpow (by positivity) Real.log_two_gt_d9.le zero_le_two)
          · rw [Real.rpow_two]
            norm_num)
    nlinarith

private theorem div_bound_aux2 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ≤ n) (h2 : 2 ≤ K) :
    (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) * K := by
  have h4 : ((r : ℝ) + 1) / K ≤ 2 ^ ((r : ℝ) / K) := by
    transitivity (r : ℝ) / K + 1 / 2
    · rw [add_div]
      simp only [one_div, add_le_add_iff_left]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 h2
    · exact bernoulli_aux _
  have hK0 : 0 < K := by positivity
  transitivity (2 : ℝ) ^ ((r : ℝ) / K) * K
  · rwa [← div_le_iff₀ hK0]
  · apply mul_le_mul_of_nonneg_right _ hK0.le
    exact Real.rpow_le_rpow (by positivity) h1 (div_nonneg (Nat.cast_nonneg _) hK0.le)

private theorem divisorCount_div_pow_eq {n : ℕ} (K : ℝ) (hn : n ≠ 0) :
    (n.divisors.card : ℝ) / (n : ℝ) ^ K⁻¹ =
      n.factorization.prod (fun p k ↦ (k + 1) / ((p : ℝ) ^ ((k : ℝ) / K))) := by
  change
      (n.divisors.card : ℝ) / (n : ℝ) ^ K⁻¹ =
        n.primeFactors.prod
          (fun p ↦ (n.factorization p + 1) / ((p : ℝ) ^ ((n.factorization p : ℝ) / K)))
  rw [div_eq_mul_inv]
  have hsigma : (n.divisors.card : ℝ) =
      n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) := by
    exact_mod_cast Nat.card_divisors hn
  rw [hsigma]
  have hpow : (n : ℝ) ^ K⁻¹ =
      n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
    calc
      (n : ℝ) ^ K⁻¹ = (((n.factorization.prod fun p k => p ^ k : ℕ) : ℕ) : ℝ) ^ K⁻¹ := by
        rw [Nat.prod_factorization_pow_eq_self hn]
      _ = (n.primeFactors.prod fun p ↦ ((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹ := by
        simp [Finsupp.prod]
      _ = n.primeFactors.prod (fun p ↦ (((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹) := by
        symm
        exact Real.finsetProd_rpow _ (fun p => ((p : ℕ) : ℝ) ^ (n.factorization p))
          (by intro p hp; positivity) _
      _ = n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
        congr with p
        rw [← Real.rpow_natCast, ← Real.rpow_mul, div_eq_mul_inv]
        positivity
  rw [hpow]
  simpa [div_eq_mul_inv] using (show
    n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) *
        n.primeFactors.prod (fun p ↦ ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) =
      n.primeFactors.prod
        (fun p ↦ (n.factorization p + 1 : ℝ) * ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) by
      rw [← Finset.prod_mul_distrib])

private theorem divisorCount_le_rpow_mul_rpow (n : ℕ) {K : ℝ} (hK : 2 ≤ K) :
    (n.divisors.card : ℝ) ≤ (n : ℝ) ^ (1 / K) * K ^ ((2 : ℝ) ^ K) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity
  rw [show (n : ℝ) ^ (1 / K) = (n : ℝ) ^ K⁻¹ by rw [one_div], mul_comm]
  rw [← div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)]
  rw [divisorCount_div_pow_eq _ hn.ne']
  let s : Finset ℕ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ K)
  have hsubset : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine (Finset.prod_le_prod_of_subset_of_le_one hsubset ?_ ?_).trans ?_
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp hp'
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpbound : (2 : ℝ) ^ K ≤ p := by
      apply le_of_not_gt
      intro hlt
      exact hp' (by simp [s, hp, hlt])
    rw [div_le_iff₀]
    · simpa using div_bound_aux1 (p : ℝ) (n.factorization p) K hpbound (by linarith)
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  refine (Finset.prod_le_prod ?_ ?_).trans ((Finset.prod_const K).trans_le ?_)
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors (hsubset hp)
    rw [div_le_iff₀]
    · simpa [mul_comm] using
        div_bound_aux2 (p : ℝ) (n.factorization p) K
          (by exact_mod_cast hpprime.two_le) hK
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  · rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have hsIcc : s ⊆ Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊ := by
      intro p hp
      have hp' : p ∈ n.primeFactors ∧ (p : ℝ) < (2 : ℝ) ^ K := by
        simpa [s] using hp
      rw [Finset.mem_Icc]
      refine ⟨Nat.pos_of_mem_primeFactors hp'.1, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hp'.2.le
    have hsle : s.card ≤ ⌊((2 : ℝ) ^ K)⌋₊ := by
      calc
        s.card ≤ (Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊).card := Finset.card_le_card hsIcc
        _ = ⌊((2 : ℝ) ^ K)⌋₊ := by
          rw [Nat.card_Icc]
          omega
    exact le_trans (by exact_mod_cast hsle) (Nat.floor_le (by positivity))

private theorem log_log_mul_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ log (log x) * log x / x ^ ε) atTop (nhds 0) := by
  refine IsLittleO.tendsto_div_nhds_zero ?_
  refine ((isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (Asymptotics.isBigO_refl _ _)).trans ?_
  refine ((isLittleO_log_rpow_atTop (half_pos hε)).pow two_pos).congr' ?_ ?_
  · filter_upwards with x using by simp [sq]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_two, ← Real.rpow_mul hx, div_mul_cancel₀ ε two_ne_zero]

private theorem divisorCount_le_rpow_aux {ε : ℝ} (hε1 : 0 < ε) (hε2 : ε ≤ 1) :
    ∀ᶠ (n : ℕ) in atTop,
      (n.divisors.card : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_coe_atTop
  have hx :
      Tendsto
        (fun n : ℕ =>
          2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3)))
        atTop (nhds 0) := by
    simpa using
      ((log_log_mul_log_div_rpow (div_pos hε1 zero_lt_three)).comp hl).const_mul 2
  have hε : 0 < Real.log 2 * ε / 2 := by
    exact half_pos (mul_pos (Real.log_pos one_lt_two) hε1)
  filter_upwards
    [tendsto_log_log_coe_atTop (eventually_ge_atTop ((Real.log 2 * (1 + ε / 2))⁻¹)),
      tendsto_log_log_coe_atTop (eventually_gt_atTop (0 : ℝ)),
      hl (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_log_coe_atTop (eventually_ge_atTop (2 * Real.log 2 * (1 + ε / 2))),
      h (eventually_gt_atTop (0 : ℝ)),
      hx (Metric.closedBall_mem_nhds 0 hε)] with
    n hlln' hlln hln hlln'' hn hx'
  dsimp at hlln hlln' hln hlln'' hn
  set K : ℝ := log (log (n : ℝ)) / (Real.log 2 * (1 + ε / 2)) with hK
  have hpowK_pos : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos zero_lt_two _
  have hε' : 0 < Real.log 2 * (1 + ε / 2) := by
    exact mul_pos (Real.log_pos one_lt_two) (by linarith)
  have hpowK : (2 : ℝ) ^ K ≤ Real.log n ^ (1 - ε / 3) := by
    refine (Real.log_le_log_iff hpowK_pos (Real.rpow_pos_of_pos hln _)).mp ?_
    rw [Real.log_rpow zero_lt_two,
      Real.log_rpow hln, hK, mul_comm (Real.log 2), ← div_div,
      div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne', div_le_iff₀]
    · have hfactor : 1 ≤ (1 - ε / 3) * (1 + ε / 2) := by
        nlinarith [hε1, hε2]
      have hmain :
          log (log (n : ℝ)) ≤
            ((1 - ε / 3) * (1 + ε / 2)) * log (log (n : ℝ)) :=
        le_mul_of_one_le_left hlln.le hfactor
      nlinarith [hmain]
    · linarith
  have hlogK : log K ≤ 2 * log (log (Real.log n)) := by
    have haux : log ((Real.log 2 * (1 + ε / 2))⁻¹) ≤ log (log (Real.log n)) := by
      exact (Real.log_le_log_iff (inv_pos.2 hε')
        (lt_of_lt_of_le (inv_pos.2 hε') hlln')).2 hlln'
    rw [hK, div_eq_mul_inv, Real.log_mul hlln.ne' (inv_ne_zero (ne_of_gt hε')), two_mul]
    linarith
  have hK₂ : 2 ≤ K := by
    rwa [le_div_iff₀ hε', ← mul_assoc]
  have hK₀ : 0 < K := zero_lt_two.trans_le hK₂
  have hK' : 0 < K ^ ((2 : ℝ) ^ K) := Real.rpow_pos_of_pos hK₀ _
  refine (divisorCount_le_rpow_mul_rpow n hK₂).trans ?_
  refine (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hn _) hK')
    (Real.rpow_pos_of_pos hn _)).mp ?_
  rw [
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' hK'.ne', Real.log_rpow hn, Real.log_rpow hK₀,
    Real.log_rpow hn]
  have hmul :
      (2 : ℝ) ^ K * log K ≤
        Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) :=
    mul_le_mul hpowK hlogK (Real.log_nonneg (one_le_two.trans hK₂)) (Real.rpow_nonneg hln.le _)
  have hsum :
      1 / K * log (n : ℝ) + (2 : ℝ) ^ K * log K ≤
        1 / K * log (n : ℝ) +
          Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hmul (1 / K * log (n : ℝ))
  refine hsum.trans ?_
  rw [hK, one_div_div, ← div_mul_eq_mul_div]
  suffices hs :
      Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) ≤
        Real.log 2 / log (log (n : ℝ)) * (ε / 2) * log (n : ℝ) by
    linarith
  suffices hs' :
      2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / (log (n : ℝ) ^ (ε / 3))) ≤
        Real.log 2 * ε / 2 by
    rw [Real.rpow_sub hln, div_eq_mul_one_div, Real.rpow_one, div_mul_eq_mul_div,
      mul_comm _ (log (n : ℝ)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hln.le
    rw [le_div_iff₀ hlln]
    field_simp at hs' ⊢
    simpa [mul_assoc] using hs'
  have hx'' :
      |2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3))| ≤
        Real.log 2 * ε / 2 := by
    simpa [mem_closedBall_zero_iff, norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hln _)] using hx'
  exact le_of_abs_le hx''

private theorem divisorCount_le_rpow {ε : ℝ} (hε1 : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop,
      (n.divisors.card : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  rcases le_total ε 1 with hε2 | hε2
  · exact divisorCount_le_rpow_aux hε1 hε2
  · filter_upwards
      [divisorCount_le_rpow_aux zero_lt_one le_rfl,
        tendsto_log_log_coe_atTop (eventually_ge_atTop (0 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with n hn hn' hn''
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn'') ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hn')

/-- Quantified `τ(n) = n ^ o(1)`: every fixed positive power eventually
dominates the divisor count. -/
theorem eventually_divisorCount_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  rcases le_total (1 : ℝ) ε with hε1 | hε1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine divisorCount_le_self.trans ?_
    have := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε1
    simpa using this
  · have hx : Tendsto (fun n : ℕ => Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹) atTop (nhds 0) := by
      simpa [mul_assoc] using
        (tendsto_log_log_coe_atTop.inv_tendsto_atTop).const_mul (Real.log 2 * 2)
    filter_upwards
      [divisorCount_le_rpow zero_lt_one,
        eventually_ge_atTop (1 : ℕ),
        hx (Metric.closedBall_mem_nhds 0 hε)] with n hn hn' hx'
    have hx'' : |Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹| ≤ ε := by
      simpa [mem_closedBall_zero_iff, norm_eq_abs] using hx'
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn') ?_)
    rw [div_mul_eq_mul_div, div_eq_mul_inv]
    simpa [one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using le_of_abs_le hx''

end

end DivisorCountSubpolynomialGrowth
