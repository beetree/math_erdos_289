import Erdos289CLT.Basic

/-!
# Subset sums of many units cover `ℤ/nℤ` (paper Lemma 2, `subsets`)

For large `n`, the subset sums of any `N ≥ n^{3/4}` distinct units modulo `n`
cover every residue.  Proof by roots of unity: with `ζ = e^{2πi/n}`,
`n R(b) = ∑_{t<n} ζ^{-bt} ∏_{a∈A} (1 + ζ^{ta})`; for `0 < t < n` at least `N/2`
of the residues `ta` are at distance `≥ N/(4n)` from `0` (as fractions of `n`),
`|1 + ζ^x| = 2|cos(πx/n)|` and `|cos πy| ≤ e^{-2‖y‖²}` (via Jordan's inequality
`Real.mul_le_sin`), so each such term is at most `2^N e^{-N³/(16n²)}`, while the
`t = 0` term is `2^N`.
-/

namespace Erdos289.CLT

open Finset Complex Real

theorem cos_eq_one_sub_two_sin_sq (x : ℝ) : Real.cos (2*x) = 1 - 2 * (Real.sin x)^2 := by
  rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x]

theorem cos_pi_mul_le_exp (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    Real.cos (π * y) ≤ Real.exp (-2 * y^2) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcos0 := cos_eq_one_sub_two_sin_sq (π*y/2)
  have harg : 2 * (π*y/2) = π * y := by ring
  rw [harg] at hcos0
  have hrange1 : (0:ℝ) ≤ π*y/2 := by positivity
  have hrange2 : π*y/2 ≤ π/2 := by nlinarith
  have hjordan := Real.mul_le_sin hrange1 hrange2
  have hy_le : y ≤ Real.sin (π*y/2) := by
    have heq : (2/π) * (π*y/2) = y := by field_simp
    linarith [heq ▸ hjordan]
  have hsin_nonneg : 0 ≤ Real.sin (π*y/2) := Real.sin_nonneg_of_nonneg_of_le_pi hrange1 (by linarith)
  have hsq : y^2 ≤ (Real.sin (π*y/2))^2 := by nlinarith
  rw [hcos0]
  have := Real.add_one_le_exp (-2*y^2)
  nlinarith

theorem norm_one_add_exp_mul_I (θ : ℝ) : ‖(1 : ℂ) + Complex.exp (θ * I)‖ = 2 * |Real.cos (θ/2)| := by
  have key : (1 : ℂ) + Complex.exp (θ * I) = 2 * Complex.cos (θ/2 : ℝ) * Complex.exp ((θ/2 : ℝ) * I) := by
    have h : Complex.cos ((θ/2:ℝ):ℂ) = (Complex.exp ((θ/2:ℝ)*I) + Complex.exp (-((θ/2:ℝ)*I)))/2 := by
      rw [Complex.cos]; push_cast; ring_nf
    rw [h]
    have e1 : Complex.exp (((θ/2:ℝ):ℂ)*I) * Complex.exp (((θ/2:ℝ):ℂ)*I) = Complex.exp ((θ:ℝ)*I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : Complex.exp (((θ/2:ℝ):ℂ)*I) * Complex.exp (-(((θ/2:ℝ):ℂ)*I)) = 1 := by
      rw [← Complex.exp_add]; simp
    have expand : (2:ℂ) * ((Complex.exp (((θ/2:ℝ):ℂ)*I) + Complex.exp (-(((θ/2:ℝ):ℂ)*I)))/2) * Complex.exp (((θ/2:ℝ):ℂ)*I)
        = Complex.exp (((θ/2:ℝ):ℂ)*I) * Complex.exp (((θ/2:ℝ):ℂ)*I) + Complex.exp (((θ/2:ℝ):ℂ)*I) * Complex.exp (-(((θ/2:ℝ):ℂ)*I)) := by
      ring
    rw [expand, e1, e2]; ring
  rw [key, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one, ← ofReal_cos, Complex.norm_real]
  norm_num

/-- The key per-element bound: if `r/n` is at distance `≥ y` from `0` and `1`, then
`|1 + ζ^r| ≤ 2 exp(-2y²)`, where `ζ = exp(2πI/n)`. -/
theorem norm_one_add_zeta_pow (n r : ℕ) (hn : 0 < n) (hr : r < n) (y : ℝ) (hy0 : 0 ≤ y) (_hy1 : y ≤ 1/2)
    (hlo : y * n ≤ r) (hhi : (r:ℝ) ≤ n - y * n) :
    ‖(1:ℂ) + Complex.exp ((2*π*I/n)) ^ r‖ ≤ 2 * Real.exp (-2 * y^2) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpow : Complex.exp ((2*π*I/n)) ^ r = Complex.exp (((2*π*r/n : ℝ)) * I) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hpow, norm_one_add_exp_mul_I]
  have harg : (2*π*(r:ℝ)/n)/2 = π * ((r:ℝ)/n) := by ring
  rw [harg]
  rcases lt_or_ge (2*r) (n+1) with hcase | hcase
  · -- r/n ≤ 1/2, and r/n ≥ y
    have hy_le : y ≤ (r:ℝ)/n := by
      rw [le_div_iff₀ hnpos]; linarith
    have hle_half : (r:ℝ)/n ≤ 1/2 := by
      rw [div_le_iff₀ hnpos]
      have : (2*r : ℝ) ≤ n := by exact_mod_cast (by omega : 2*r ≤ n)
      linarith
    have hcos_nonneg : 0 ≤ Real.cos (π * ((r:ℝ)/n)) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [abs_of_nonneg hcos_nonneg]
    have hmono : Real.cos (π * ((r:ℝ)/n)) ≤ Real.exp (-2 * ((r:ℝ)/n)^2) :=
      cos_pi_mul_le_exp _ (by positivity) hle_half
    have hexp_mono : Real.exp (-2 * ((r:ℝ)/n)^2) ≤ Real.exp (-2*y^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hy_le, hy0]
    linarith
  · -- r/n ≥ 1/2, use 1-r/n
    set z : ℝ := 1 - (r:ℝ)/n with hz_def
    have hnr : (n:ℝ) - r = n * z := by rw [hz_def]; field_simp
    have hrn : (r:ℝ) ≤ n := by exact_mod_cast hr.le
    have hz0 : 0 ≤ z := by
      rw [hz_def]
      have := div_le_one_of_le₀ hrn hnpos.le
      linarith
    have hz_le : y ≤ z := by
      rw [hz_def]
      nlinarith [hhi, hnr]
    have h2rn : (n:ℝ) + 1 ≤ 2*r := by exact_mod_cast hcase
    have hz_half : z ≤ 1/2 := by
      have hrn2 : (1:ℝ)/2 ≤ (r:ℝ)/n := by
        rw [le_div_iff₀ hnpos]; linarith
      rw [hz_def]; linarith
    have hswap : π * ((r:ℝ)/n) = π - π * z := by rw [hz_def]; ring
    rw [hswap, Real.cos_pi_sub, abs_neg]
    have hcos_nonneg : 0 ≤ Real.cos (π * z) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [abs_of_nonneg hcos_nonneg]
    have hmono : Real.cos (π * z) ≤ Real.exp (-2 * z^2) := cos_pi_mul_le_exp _ hz0 hz_half
    have hexp_mono : Real.exp (-2 * z^2) ≤ Real.exp (-2*y^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hz_le, hy0]
    linarith

/-- For fixed `t, n, r`, the elements of `range n` mapping to `r` under `a ↦ t*a % n` number at
most `gcd t n`. -/
theorem fiber_bound (n t : ℕ) (hn : 0 < n) (r : ℕ) :
    ((range n).filter (fun a => t * a % n = r)).card ≤ Nat.gcd t n := by
  set g := Nat.gcd t n with hg
  set n' := n / g with hn'
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right t hn
  have hgdvd : g ∣ n := Nat.gcd_dvd_right t n
  have hnn' : n = g * n' := (Nat.mul_div_cancel' hgdvd).symm
  by_cases hne : ((range n).filter (fun a => t * a % n = r)).Nonempty
  · obtain ⟨a0, ha0⟩ := hne
    simp only [mem_filter, mem_range] at ha0
    have hsub : (range n).filter (fun a => t * a % n = r) ⊆
        (range n).filter (fun a => a ≡ a0 [MOD n']) := by
      intro a ha
      simp only [mem_filter, mem_range] at ha ⊢
      refine ⟨ha.1, ?_⟩
      have heq : t * a ≡ t * a0 [MOD n] := by
        unfold Nat.ModEq
        rw [ha.2, ha0.2]
      have hcanc := heq.cancel_left_div_gcd hn
      rw [Nat.gcd_comm] at hcanc
      exact hcanc
    calc ((range n).filter (fun a => t * a % n = r)).card
        ≤ ((range n).filter (fun a => a ≡ a0 [MOD n'])).card := Finset.card_le_card hsub
      _ = g := by
          rw [← Nat.count_eq_card_filter_range]
          have hn'pos : 0 < n' := by
            rw [hn']; exact Nat.div_pos (Nat.le_of_dvd hn hgdvd) hgpos
          rw [Nat.count_modEq_card _ hn'pos]
          have hmod0 : n % n' = 0 := by
            rw [hnn']; exact Nat.mul_mod_left g n'
          have hdiv : n / n' = g := by
            rw [hnn', Nat.mul_div_cancel g hn'pos]
          rw [hmod0, hdiv]
          simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

theorem card_pos_multiples_lt (n g X : ℕ) (hg : 0 < g) :
    ((range n).filter (fun r => 0 < r ∧ g ∣ r ∧ 4 * r < X)).card ≤ X / (4 * g) := by
  have hcard_eq : (Finset.Icc 1 (X / (4*g))).card = X / (4*g) := by
    rw [Nat.card_Icc]; exact Nat.add_sub_cancel _ _
  rw [← hcard_eq]
  apply Finset.card_le_card_of_injOn (fun r => r / g)
  · intro r hr
    simp only [Finset.mem_coe, mem_filter, mem_range] at hr
    obtain ⟨_, hr0, ⟨k, hk⟩, hrX⟩ := hr
    have hkeq : r / g = k := by rw [hk]; exact Nat.mul_div_cancel_left k hg
    show r / g ∈ ↑(Icc 1 (X / (4*g)))
    rw [hkeq, mem_Icc]
    constructor
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso; rw [hk, h0, mul_zero] at hr0; omega
      · exact h0
    · rw [Nat.le_div_iff_mul_le (by positivity)]
      rw [hk] at hrX
      nlinarith
  · intro a ha b hb hab
    simp only [Finset.mem_coe, mem_filter, mem_range] at ha hb
    obtain ⟨_, _, ⟨ka, hka⟩, _⟩ := ha
    obtain ⟨_, _, ⟨kb, hkb⟩, _⟩ := hb
    have e1 : a / g = ka := by rw [hka]; exact Nat.mul_div_cancel_left ka hg
    have e2 : b / g = kb := by rw [hkb]; exact Nat.mul_div_cancel_left kb hg
    simp only [e1, e2] at hab
    rw [hka, hkb, hab]

theorem card_pos_multiples_near (n g X : ℕ) (hg : 0 < g) (hgn : g ∣ n) (hXn : X ≤ 4 * n) :
    ((range n).filter (fun r => g ∣ r ∧ 4 * n < 4 * r + X)).card ≤ X / (4 * g) := by
  refine le_trans ?_ (card_pos_multiples_lt n g X hg)
  apply Finset.card_le_card_of_injOn (fun r => n - r)
  · intro r hr
    simp only [Finset.mem_coe, mem_filter, mem_range] at hr
    obtain ⟨hrn, ⟨k, hk⟩, hrX⟩ := hr
    have hr0 : 0 < r := by omega
    obtain ⟨m, hm⟩ := hgn
    have hkm : k < m := by
      apply Nat.lt_of_mul_lt_mul_left (a := g)
      rw [← hk, ← hm]; exact hrn
    show n - r ∈ ↑((range n).filter (fun r => 0 < r ∧ g ∣ r ∧ 4 * r < X))
    simp only [mem_filter, mem_range]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · refine ⟨m - k, ?_⟩
      rw [hm, hk, Nat.mul_sub]
    · omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, mem_filter, mem_range] at ha hb
    simp only at hab
    omega

theorem gcd_dvd_mod (n t a : ℕ) : Nat.gcd t n ∣ (t * a % n) := by
  have h1 : Nat.gcd t n ∣ t * a := (Nat.gcd_dvd_left t n).mul_right a
  have h2 : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
  exact (Nat.dvd_mod_iff h2).mpr h1

theorem mod_ne_zero_of_coprime (n t a : ℕ) (ht0 : 0 < t) (htn : t < n) (hcop : Nat.Coprime a n) :
    t * a % n ≠ 0 := by
  intro h
  have hdvd : n ∣ t * a := Nat.dvd_of_mod_eq_zero h
  have hcop' : Nat.Coprime n a := hcop.symm
  have hnt : n ∣ t := (Nat.Coprime.dvd_of_dvd_mul_right hcop' hdvd)
  have := Nat.le_of_dvd ht0 hnt
  omega

/-- For `0 < t < n`, at most half (as a real bound) of the elements of `A` have `t*a % n`
close to `0` or `n`. -/
theorem badA_card_le (n t : ℕ) (hn : 0 < n) (ht0 : 0 < t) (htn : t < n)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a < n ∧ Nat.Coprime a n) :
    ((A.filter (fun a => 4 * (t * a % n) < A.card ∨ 4 * n < 4 * (t * a % n) + A.card)).card : ℝ)
      ≤ (A.card : ℝ) / 2 := by
  set N := A.card with hN
  set g := Nat.gcd t n with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right t hn
  have hgdvd : g ∣ n := Nat.gcd_dvd_right t n
  set badA := A.filter (fun a => 4 * (t * a % n) < N ∨ 4 * n < 4 * (t * a % n) + N) with hbadA
  set badRes := (range n).filter
      (fun r => 0 < r ∧ g ∣ r ∧ (4 * r < N ∨ 4 * n < 4 * r + N)) with hbadRes
  have hmaps : Set.MapsTo (fun a => t * a % n) (↑badA) (↑badRes) := by
    intro a ha
    simp only [hbadA, mem_coe, mem_filter] at ha
    obtain ⟨haA, hbad⟩ := ha
    have hlt : a < n := (hA a haA).1
    have hcop : Nat.Coprime a n := (hA a haA).2
    simp only [hbadRes, mem_coe, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ hn, ⟨Nat.pos_of_ne_zero (mod_ne_zero_of_coprime n t a ht0 htn hcop),
      gcd_dvd_mod n t a, hbad⟩⟩
  have hcardeq : badA.card = ∑ r ∈ badRes, (badA.filter (fun a => t * a % n = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ r ∈ badRes, (badA.filter (fun a => t * a % n = r)).card ≤ g := by
    intro r _
    calc (badA.filter (fun a => t * a % n = r)).card
        ≤ (A.filter (fun a => t * a % n = r)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      _ ≤ ((range n).filter (fun a => t * a % n = r)).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [mem_filter] at ha ⊢
          exact ⟨mem_range.mpr (hA a ha.1).1, ha.2⟩
      _ ≤ g := fiber_bound n t hn r
  have hsum_le : badA.card ≤ badRes.card * g := by
    rw [hcardeq]
    calc ∑ r ∈ badRes, (badA.filter (fun a => t * a % n = r)).card
        ≤ ∑ _r ∈ badRes, g := Finset.sum_le_sum hbound
      _ = badRes.card * g := by rw [Finset.sum_const, smul_eq_mul]
  have hbadRes_split : badRes ⊆
      ((range n).filter (fun r => 0 < r ∧ g ∣ r ∧ 4 * r < N)) ∪
      ((range n).filter (fun r => g ∣ r ∧ 4 * n < 4 * r + N)) := by
    intro r hr
    simp only [hbadRes, mem_filter, mem_range] at hr
    obtain ⟨hrn, hr0, hgr, hor⟩ := hr
    rcases hor with h1 | h2
    · exact Finset.mem_union_left _ (by simp only [mem_filter, mem_range]; exact ⟨hrn, hr0, hgr, h1⟩)
    · exact Finset.mem_union_right _ (by simp only [mem_filter, mem_range]; exact ⟨hrn, hgr, h2⟩)
  have hNn : N ≤ n := by
    rw [hN]
    calc A.card ≤ (range n).card := by
          apply Finset.card_le_card
          intro a ha
          exact mem_range.mpr (hA a ha).1
      _ = n := Finset.card_range n
  have hbadRes_card : badRes.card ≤ N / (4*g) + N / (4*g) := by
    calc badRes.card
        ≤ (((range n).filter (fun r => 0 < r ∧ g ∣ r ∧ 4 * r < N)) ∪
            ((range n).filter (fun r => g ∣ r ∧ 4 * n < 4 * r + N))).card :=
          Finset.card_le_card hbadRes_split
      _ ≤ ((range n).filter (fun r => 0 < r ∧ g ∣ r ∧ 4 * r < N)).card +
            ((range n).filter (fun r => g ∣ r ∧ 4 * n < 4 * r + N)).card :=
          Finset.card_union_le _ _
      _ ≤ N / (4*g) + N / (4*g) :=
          add_le_add (card_pos_multiples_lt n g N hgpos)
            (card_pos_multiples_near n g N hgpos hgdvd (by omega))
  -- combine to real inequality
  have hreal : (badA.card : ℝ) ≤ (badRes.card : ℝ) * g := by exact_mod_cast hsum_le
  have hreal2 : (badRes.card : ℝ) ≤ (N:ℝ) / (4*g) + (N:ℝ)/(4*g) := by
    have := hbadRes_card
    have hcast : (badRes.card : ℝ) ≤ ((N / (4*g) : ℕ):ℝ) + ((N/(4*g):ℕ):ℝ) := by exact_mod_cast this
    refine hcast.trans ?_
    have hb1 : ((N / (4*g) : ℕ):ℝ) ≤ (N:ℝ)/(4*g) := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := 4*g)
      push_cast at this ⊢
      convert this using 2
    linarith
  have hgR : (0:ℝ) < (g:ℝ) := by exact_mod_cast hgpos
  calc (badA.card : ℝ) ≤ (badRes.card : ℝ) * g := hreal
    _ ≤ ((N:ℝ)/(4*g) + (N:ℝ)/(4*g)) * g := by
        apply mul_le_mul_of_nonneg_right hreal2 hgR.le
    _ = (N:ℝ)/2 := by field_simp; ring

theorem norm_one_add_zeta_pow_le_two (n r : ℕ) (_hn : 0 < n) :
    ‖(1:ℂ) + Complex.exp ((2*π*I/n)) ^ r‖ ≤ 2 := by
  have hz : ‖Complex.exp ((2*π*I/n)) ^ r‖ = 1 := by
    rw [norm_pow]
    have : (2*π*I/(n:ℂ)) = ((2*π/n : ℝ):ℂ) * I := by push_cast; ring
    rw [this, norm_exp_ofReal_mul_I]
    norm_num
  calc ‖(1:ℂ) + Complex.exp ((2*π*I/n)) ^ r‖ ≤ ‖(1:ℂ)‖ + ‖Complex.exp ((2*π*I/n)) ^ r‖ := norm_add_le _ _
    _ = 2 := by rw [hz]; norm_num

/-- Splitting the product over `A` into a "bad" part (bounded by `2` per factor) and a "good"
part (bounded by `2 exp(-2y²)` per factor, given `hgoodbound`) gives an overall bound
`2^|A| exp(-2y²|good|)`. -/
theorem prod_bound (n t : ℕ) (hn : 0 < n) (_ht0 : 0 < t) (_htn : t < n)
    (A : Finset ℕ) (_hA : ∀ a ∈ A, a < n)
    (badA good : Finset ℕ) (hpart : ∀ a ∈ A, a ∈ badA ↔ ¬ (a ∈ good))
    (_hbadA : badA ⊆ A) (hgood : good ⊆ A) (hunion : badA ∪ good = A)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hgoodbound : ∀ a ∈ good, y * n ≤ (t * a % n : ℕ) ∧ ((t * a % n : ℕ):ℝ) ≤ n - y * n) :
    ‖∏ a ∈ A, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖ ≤
      2 ^ A.card * Real.exp (-2 * y^2 * good.card) := by
  have hdisj : Disjoint badA good := by
    rw [Finset.disjoint_left]
    intro a haB haG
    have haA : a ∈ A := hgood haG
    exact (hpart a haA).mp haB haG
  have hsplit : ∏ a ∈ A, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n)) =
      (∏ a ∈ badA, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))) *
      (∏ a ∈ good, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))) := by
    rw [← hunion, Finset.prod_union hdisj]
  rw [hsplit, norm_mul]
  have hbad_le : ‖∏ a ∈ badA, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖ ≤ 2 ^ badA.card := by
    calc ‖∏ a ∈ badA, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖
        ≤ ∏ a ∈ badA, ‖(1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n)‖ := norm_prod_le _ _
      _ ≤ ∏ _a ∈ badA, (2:ℝ) := Finset.prod_le_prod (fun a _ => norm_nonneg _)
          (fun a _ => norm_one_add_zeta_pow_le_two n _ hn)
      _ = 2 ^ badA.card := by rw [Finset.prod_const]
  have hgood_le : ‖∏ a ∈ good, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖ ≤
      (2 * Real.exp (-2*y^2)) ^ good.card := by
    calc ‖∏ a ∈ good, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖
        ≤ ∏ a ∈ good, ‖(1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n)‖ := norm_prod_le _ _
      _ ≤ ∏ _a ∈ good, (2 * Real.exp (-2*y^2)) := by
          apply Finset.prod_le_prod (fun a _ => norm_nonneg _)
          intro a ha
          exact norm_one_add_zeta_pow n _ hn (Nat.mod_lt _ hn) y hy0 hy1
            (hgoodbound a ha).1 (hgoodbound a ha).2
      _ = (2 * Real.exp (-2*y^2)) ^ good.card := by rw [Finset.prod_const]
  have hcombine : (2:ℝ) ^ badA.card * (2 * Real.exp (-2*y^2)) ^ good.card =
      2 ^ A.card * Real.exp (-2*y^2 * good.card) := by
    rw [mul_pow]
    rw [show (2:ℝ) ^ badA.card * (2 ^ good.card * Real.exp (-2*y^2) ^ good.card)
        = (2 ^ badA.card * 2 ^ good.card) * Real.exp (-2*y^2) ^ good.card from by ring]
    rw [← pow_add, ← hunion, Finset.card_union_of_disjoint hdisj]
    congr 1
    rw [← Real.exp_nat_mul]
    ring_nf
  calc ‖∏ a ∈ badA, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖ *
        ‖∏ a ∈ good, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖
      ≤ (2:ℝ) ^ badA.card * (2 * Real.exp (-2*y^2)) ^ good.card := by
        apply mul_le_mul hbad_le hgood_le (norm_nonneg _) (by positivity)
    _ = 2 ^ A.card * Real.exp (-2*y^2 * good.card) := hcombine

/-- The main analytic bound: for `0 < t < n`, `‖∏_{a∈A} (1 + ζ^{ta})‖ ≤ 2^{|A|} exp(-|A|³/(16n²))`. -/
theorem full_prod_bound (n t : ℕ) (hn : 0 < n) (ht0 : 0 < t) (htn : t < n)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a < n ∧ Nat.Coprime a n) :
    ‖∏ a ∈ A, ((1:ℂ) + Complex.exp ((2*π*I/n)) ^ (t * a % n))‖ ≤
      2 ^ A.card * Real.exp (-((A.card:ℝ)^3 / (16 * n^2))) := by
  set N := A.card with hN
  set badA := A.filter (fun a => 4 * (t * a % n) < N ∨ 4 * n < 4 * (t * a % n) + N) with hbadA
  set good := A.filter (fun a => ¬ (4 * (t * a % n) < N ∨ 4 * n < 4 * (t * a % n) + N)) with hgood
  have hbadcard := badA_card_le n t hn ht0 htn A hA
  have hpartcard : badA.card + good.card = N := by
    rw [hbadA, hgood, hN]
    exact Finset.card_filter_add_card_filter_not _
  have hNn : N ≤ n := by
    rw [hN]
    calc A.card ≤ (range n).card := by
          apply Finset.card_le_card; intro a ha; exact Finset.mem_range.mpr (hA a ha).1
      _ = n := Finset.card_range n
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set y : ℝ := (N:ℝ) / (4*n) with hy_def
  have hy0 : 0 ≤ y := by rw [hy_def]; positivity
  have hy1 : y ≤ 1/2 := by
    have hNle : (N:ℝ) ≤ n := by exact_mod_cast hNn
    rw [hy_def]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*(n:ℝ))]
    nlinarith
  have hgoodbound : ∀ a ∈ good, y * n ≤ (t * a % n : ℕ) ∧ ((t * a % n : ℕ):ℝ) ≤ n - y * n := by
    intro a ha
    simp only [hgood, mem_filter, not_or, not_lt] at ha
    obtain ⟨_, h1, h2⟩ := ha
    have e1 : (N:ℝ) ≤ 4 * (t*a%n : ℕ) := by exact_mod_cast h1
    have e2' : (4:ℝ) * (t*a%n : ℕ) + N ≤ 4*n := by exact_mod_cast h2
    have hyn : y * n = N/4 := by rw [hy_def]; field_simp; try ring
    constructor
    · rw [hyn]; linarith
    · rw [hyn]; linarith
  have hbound := prod_bound n t hn ht0 htn A (fun a ha => (hA a ha).1) badA good
    (by intro a ha; simp only [hbadA, hgood, mem_filter]; tauto)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (by rw [hbadA, hgood]; exact Finset.filter_union_filter_not_eq _ _)
    y hy0 hy1 hgoodbound
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2 ^ N)
  rw [Real.exp_le_exp]
  have hgc : (N:ℝ)/2 ≤ good.card := by
    have : (badA.card : ℝ) + good.card = N := by exact_mod_cast hpartcard
    linarith [hbadcard]
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hyy : y^2 * (16 * n^2) = N^2 := by rw [hy_def]; field_simp; try ring
  have hprod : (N:ℝ)/2 * N^2 ≤ (good.card:ℝ) * N^2 :=
    mul_le_mul_of_nonneg_right hgc (sq_nonneg (N:ℝ))
  have hn2pos : (0:ℝ) < 16 * (n:ℝ)^2 := by positivity
  have key : (N:ℝ)^3 / (16*n^2) ≤ 2 * y^2 * good.card := by
    rw [div_le_iff₀ hn2pos]
    nlinarith [hprod, hyy]
  linarith [key]

theorem geom_orthogonality (n : ℕ) (_hn : 0 < n) (z : ℂ) (hzn : z^n = 1) :
    ∑ t ∈ range n, z^t = if z = 1 then (n:ℂ) else 0 := by
  by_cases hz1 : z = 1
  · simp [hz1]
  · rw [ite_eq_right hz1]
    rw [geom_sum_eq hz1 n, hzn]
    simp

theorem exp_pow_eq_iff_modEq_le (n s b : ℕ) (_hn : 0 < n) (hprim : IsPrimitiveRoot (Complex.exp (2*π*I/n)) n)
    (hne : Complex.exp (2*π*I/n) ≠ 0) (hsb : b ≤ s) :
    (Complex.exp (2*π*I/n))^s = (Complex.exp (2*π*I/n))^b ↔ s ≡ b [MOD n] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hsb
  constructor
  · intro h
    rw [pow_add] at h
    have hb0 : (Complex.exp (2*π*I/n))^b ≠ 0 := pow_ne_zero _ hne
    have hk1 : (Complex.exp (2*π*I/n))^k = 1 := by
      apply mul_right_cancel₀ hb0
      rw [one_mul, mul_comm]
      exact h
    have hdvd : n ∣ k := (hprim.pow_eq_one_iff_dvd k).mp hk1
    exact (Nat.add_modEq_left_iff).mpr hdvd
  · intro h
    have hdvd : n ∣ k := (Nat.add_modEq_left_iff).mp h
    have hk1 : (Complex.exp (2*π*I/n))^k = 1 := (hprim.pow_eq_one_iff_dvd k).mpr hdvd
    rw [pow_add, hk1, mul_one]

theorem exp_pow_eq_iff_modEq (n s b : ℕ) (hn : 0 < n) :
    (Complex.exp (2*π*I/n))^s = (Complex.exp (2*π*I/n))^b ↔ s ≡ b [MOD n] := by
  have hprim : IsPrimitiveRoot (Complex.exp (2*π*I/n)) n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hne : Complex.exp (2*π*I/n) ≠ 0 := Complex.exp_ne_zero _
  rcases le_total b s with hsb | hbs
  · exact exp_pow_eq_iff_modEq_le n s b hn hprim hne hsb
  · rw [eq_comm, exp_pow_eq_iff_modEq_le n b s hn hprim hne hbs, Nat.ModEq.comm]

/-- The orthogonality identity: `n · R(b) = ∑_{t<n} ζ^{-bt} ∏_{a∈A} (1 + ζ^{ta})`, where `R(b)`
counts subsets of `A` whose sum is `≡ b (mod n)`. -/
theorem sum_eq_card_R (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (b : ℕ) :
    ∑ t ∈ range n, (Complex.exp (2*π*I/n))⁻¹ ^ (t*b) *
        ∏ a ∈ A, ((1:ℂ) + Complex.exp (2*π*I/n) ^ (t * a)) =
      (n : ℂ) * (A.powerset.filter (fun P => (∑ a ∈ P, a) ≡ b [MOD n])).card := by
  set ζ := Complex.exp (2*π*I/n) with hζ
  have hne : ζ ≠ 0 := Complex.exp_ne_zero _
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hζn : ζ^n = 1 := hprim.pow_eq_one
  have step1 : ∀ t : ℕ, ζ⁻¹ ^ (t*b) * ∏ a ∈ A, ((1:ℂ) + ζ ^ (t * a)) =
      ∑ P ∈ A.powerset, (ζ ^ (∑ a ∈ P, a) * ζ⁻¹^b)^t := by
    intro t
    rw [Finset.prod_one_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hprodpow : ∏ a ∈ P, ζ ^ (t*a) = ζ ^ (∑ a ∈ P, t*a) := by
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [hprodpow]
    have hsumeq : (∑ a ∈ P, t*a) = t * (∑ a ∈ P, a) := by rw [Finset.mul_sum]
    rw [hsumeq]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun t _ => step1 t)]
  rw [Finset.sum_comm]
  have step2 : ∀ P ∈ A.powerset, ∑ t ∈ range n, (ζ ^ (∑ a ∈ P, a) * ζ⁻¹^b)^t =
      if (∑ a ∈ P, a) ≡ b [MOD n] then (n:ℂ) else 0 := by
    intro P _
    have hζinvn : ζ⁻¹^n = 1 := by rw [inv_pow, hζn, inv_one]
    have hpow_n : (ζ ^ (∑ a ∈ P, a) * ζ⁻¹^b)^n = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (∑ a ∈ P, a) n, mul_comm b n, pow_mul, pow_mul,
        hζn, hζinvn, one_pow, one_pow, one_mul]
    rw [geom_orthogonality n hn _ hpow_n]
    congr 1
    have : (ζ ^ (∑ a ∈ P, a) * ζ⁻¹^b = 1) ↔ (∑ a ∈ P, a) ≡ b [MOD n] := by
      rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hne)]
      exact exp_pow_eq_iff_modEq n _ b hn
    simp only [eq_iff_iff]
    exact this
  rw [Finset.sum_congr rfl step2]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_split_bound (n : ℕ) (hn : 1 ≤ n) (g : ℕ → ℂ) (B : ℝ) (_hBnn : 0 ≤ B)
    (hB : ∀ t, 1 ≤ t → t < n → ‖g t‖ ≤ B) :
    ‖(∑ t ∈ range n, g t) - g 0‖ ≤ (n-1) * B := by
  have hsplit : ∑ t ∈ range n, g t = g 0 + ∑ t ∈ Ico 1 n, g t := by
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive g (Nat.zero_le 1) hn]
    congr 1
    rw [show Ico 0 1 = {0} from rfl]
    simp
  rw [hsplit]
  simp only [add_sub_cancel_left]
  calc ‖∑ t ∈ Ico 1 n, g t‖ ≤ ∑ t ∈ Ico 1 n, ‖g t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ Ico 1 n, B := by
        apply Finset.sum_le_sum
        intro t ht
        rw [mem_Ico] at ht
        exact hB t ht.1 ht.2
    _ = (n-1) * B := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        rw [Nat.cast_sub hn]
        ring

/-- Eventually `n - 1 < exp(n^{1/4}/16)`, via the elementary bound `exp x ≥ x^8/8!`. -/
theorem exists_n0 : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → (n:ℝ) - 1 < Real.exp ((n:ℝ)^((1:ℝ)/4)/16) := by
  set C : ℝ := (16:ℝ)^8 * (Nat.factorial 8) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, (2*C : ℝ) ≤ n0 := exists_nat_ge (2*C)
  refine ⟨n0, fun n hn => ?_⟩
  have hn0n : (2*C:ℝ) ≤ n := hn0.trans (by exact_mod_cast hn)
  have hnpos : (0:ℝ) < (n:ℝ) := by nlinarith [hCpos]
  set x : ℝ := (n:ℝ)^((1:ℝ)/4)/16 with hx_def
  have hx0 : 0 ≤ x := by rw [hx_def]; positivity
  have hbound := Real.pow_div_factorial_le_exp x hx0 8
  have hxpow : x^8 = (n:ℝ)^2 / (16:ℝ)^8 := by
    rw [hx_def, div_pow, ← Real.rpow_natCast ((n:ℝ)^((1:ℝ)/4)) 8, ← Real.rpow_mul hnpos.le]
    norm_num
  rw [hxpow] at hbound
  have hCeq : (n:ℝ)^2 / (16:ℝ)^8 / (Nat.factorial 8) = (n:ℝ)^2 / C := by
    rw [hC]; ring
  rw [hCeq] at hbound
  have key : (n:ℝ) - 1 < (n:ℝ)^2 / C := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [hn0n, hCpos]
  linarith [key, hbound]

/-- `N ≥ n^{3/4}` implies `N³/(16n²) ≥ n^{1/4}/16`. -/
theorem rpow_bound (n : ℕ) (hn : 0 < n) (N : ℝ) (_hN0 : 0 ≤ N) (hN : (n:ℝ)^((3:ℝ)/4) ≤ N) :
    (n:ℝ)^((1:ℝ)/4) / 16 ≤ N^3 / (16 * n^2) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : ((n:ℝ)^((3:ℝ)/4))^(3:ℕ) ≤ N^3 := by
    apply pow_le_pow_left₀ (by positivity) hN
  have h2 : ((n:ℝ)^((3:ℝ)/4))^(3:ℕ) = (n:ℝ) ^ ((9:ℝ)/4) := by
    rw [← Real.rpow_natCast ((n:ℝ) ^ ((3:ℝ)/4)) 3, ← Real.rpow_mul hnpos.le]
    norm_num
  rw [h2] at h1
  have h3 : (n:ℝ)^((9:ℝ)/4) = (n:ℝ)^((1:ℝ)/4) * (n:ℝ)^2 := by
    rw [← Real.rpow_natCast (n:ℝ) 2, ← Real.rpow_add hnpos]
    norm_num
  rw [h3] at h1
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 16) (by positivity : (0:ℝ) < 16 * (n:ℝ)^2)]
  nlinarith [h1]

theorem subsets_lemma : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset ℕ,
    (∀ a ∈ A, a < n ∧ Nat.Coprime a n) → (n : ℝ) ^ ((3 : ℝ) / 4) ≤ A.card →
    ∀ b : ℕ, ∃ Cs ⊆ A, (∑ a ∈ Cs, a) ≡ b [MOD n] := by
  obtain ⟨n0, hn0⟩ := exists_n0
  refine ⟨max n0 2, fun n hn A hA hAcard b => ?_⟩
  have hn0' : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := by omega
  set N := A.card with hN
  set ζ := Complex.exp (2*π*I/n) with hζ
  set g : ℕ → ℂ := fun t => ζ⁻¹ ^ (t*b) * ∏ a ∈ A, ((1:ℂ) + ζ ^ (t * a)) with hg
  set R := (A.powerset.filter (fun P => (∑ a ∈ P, a) ≡ b [MOD n])).card with hR
  have hsum : ∑ t ∈ range n, g t = (n:ℂ) * R := sum_eq_card_R n hnpos A b
  have hg0 : g 0 = 2 ^ N := by simp [hg]; norm_num; rw [hN]
  set B : ℝ := 2 ^ N * Real.exp (-((N:ℝ)^3 / (16 * (n:ℝ)^2))) with hB_def
  have hBnn : 0 ≤ B := by rw [hB_def]; positivity
  have hBbound : ∀ t, 1 ≤ t → t < n → ‖g t‖ ≤ B := by
    intro t ht1 htn
    show ‖ζ⁻¹ ^ (t*b) * ∏ a ∈ A, ((1:ℂ) + ζ ^ (t * a))‖ ≤ B
    rw [norm_mul]
    have hnorm1 : ‖ζ⁻¹ ^ (t*b)‖ = 1 := by
      rw [norm_pow, norm_inv]
      have : ‖ζ‖ = 1 := by
        rw [hζ, show (2*π*I/(n:ℂ)) = ((2*π/n:ℝ):ℂ) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I]
      rw [this]; norm_num
    rw [hnorm1, one_mul]
    have hperiod : ∀ a ∈ A, ζ ^ (t*a) = ζ ^ (t*a % n) := by
      intro a _
      have hζn : ζ^n = 1 := by
        rw [hζ]; exact (Complex.isPrimitiveRoot_exp n hnpos.ne').pow_eq_one
      conv_lhs => rw [← Nat.div_add_mod (t*a) n]
      rw [pow_add, pow_mul, hζn, one_pow, one_mul]
    have hprodeq : (∏ a ∈ A, ((1:ℂ) + ζ ^ (t * a))) = ∏ a ∈ A, ((1:ℂ) + ζ ^ (t * a % n)) :=
      Finset.prod_congr rfl (fun a ha => by rw [hperiod a ha])
    rw [hprodeq]
    exact full_prod_bound n t hnpos ht1 htn A hA
  have hsplit := sum_split_bound n (by omega) g B hBnn hBbound
  rw [hsum, hg0] at hsplit
  -- derive R ≠ 0
  have hNle : (N:ℝ) ≤ n := by
    rw [hN]
    calc (A.card:ℝ) ≤ ((range n).card:ℝ) := by
          exact_mod_cast Finset.card_le_card (fun a ha => Finset.mem_range.mpr (hA a ha).1)
      _ = n := by rw [Finset.card_range]
  have hNnn : (0:ℝ) ≤ N := by positivity
  have hNcube : (n:ℝ)^((1:ℝ)/4)/16 ≤ (N:ℝ)^3/(16*(n:ℝ)^2) := rpow_bound n hnpos N hNnn hAcard
  have hlt := hn0 n hn0'
  have hfinal : (n:ℝ) - 1 < Real.exp ((N:ℝ)^3/(16*(n:ℝ)^2)) :=
    lt_of_lt_of_le hlt (Real.exp_le_exp.mpr hNcube)
  have hexppos : 0 < Real.exp ((N:ℝ)^3/(16*(n:ℝ)^2)) := Real.exp_pos _
  have hprodlt : ((n:ℝ)-1) * Real.exp (-((N:ℝ)^3 / (16 * (n:ℝ)^2))) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one hexppos]
    exact hfinal
  have hBlt : ((n:ℝ)-1) * B < 2^N := by
    rw [hB_def]
    have : ((n:ℝ)-1) * (2^N * Real.exp (-((N:ℝ)^3 / (16 * (n:ℝ)^2)))) =
        2^N * (((n:ℝ)-1) * Real.exp (-((N:ℝ)^3 / (16 * (n:ℝ)^2)))) := by ring
    rw [this]
    calc (2:ℝ)^N * (((n:ℝ)-1) * Real.exp (-((N:ℝ)^3 / (16 * (n:ℝ)^2)))) <
        2^N * 1 := by
          apply mul_lt_mul_of_pos_left hprodlt (by positivity)
      _ = 2^N := mul_one _
  have hRne : R ≠ 0 := by
    intro hR0
    rw [hR0] at hsplit
    simp only [Nat.cast_zero, mul_zero, zero_sub, norm_neg] at hsplit
    have : (2:ℝ)^N ≤ ((n:ℝ)-1) * B := by
      have hnorm2N : ‖(2:ℂ)^N‖ = (2:ℝ)^N := by
        rw [norm_pow]; norm_num
      rw [hnorm2N] at hsplit
      exact hsplit
    linarith [hBlt, this]
  obtain ⟨P, hP⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hRne)
  simp only [mem_filter, mem_powerset] at hP
  exact ⟨P, hP.1, hP.2⟩

end Erdos289.CLT
