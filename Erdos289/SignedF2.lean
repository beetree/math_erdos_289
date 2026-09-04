import Erdos289.SignedDefs
import Erdos289.Lemma2

/-!
# Lemma F2: simultaneous nonadjacency for a finite family of signed fibers

This file formalizes Lemma F2 of `docs/elementary_replacements.md` (Section 2, displays
(F9)-(F12)): given the signed fibers of Lemma F1 for all prime-power labels `q ∈ (L, H]`,
one can thin each fiber to a quarter of its size so that *all* the retained signed pairs,
over all labels, are pairwise separated (disjoint and nonadjacent).

The proof is the finite counting (probabilistic-method) argument of the document.

* Every signed pair `{q m, q m + σ}` is either `[y, y+1]` or `[y-1, y]` for its slot `y`
  (the endpoint divisible by `4`); which one is recorded by the *orientation bit*
  `ori q m σ` (`Erdos289.SignedF2.ori`).
* One considers all `2 ^ |S|` assignments of a bit to each of the finitely many slots `S`
  occurring for labels in `(L, H]`. Here an assignment is encoded as a subset `A ⊆ S`.
  A candidate is *retained* if its orientation agrees with its slot's bit.
* Since slots are distinct within a fiber, the finite average identity
  `∑_A u ^ B_q(A) = (1 + u)^{N_q} 2^{|S| - N_q}` holds (`sum_powerset_pow`); with
  `u = (3/4)^4` a Markov/Chernoff step gives `#{A : B_q(A) < N_q/4} ≤ 2^{|S|} (9/10)^{N_q}`
  (`card_bad_le`).
* With `N_q ≥ q^{15ε/16}` and `L` large, `(9/10)^{N_q} ≤ 1/(2q^2)`, and the telescoping
  bound `∑_{q > L} 1/q^2 ≤ 1/L` makes the union bound over labels strictly smaller than
  `2^{|S|}`. Hence some assignment is good for every fiber.
* Separation: at distinct slots `y ≠ z` (both multiples of `4`) the pairs are separated by
  `omega`; at a common slot the two retained pairs coincide, and the largest prime power
  dividing an endpoint of a pair is its label, so the labels and multipliers coincide.
-/

namespace Erdos289

namespace SignedF2

open Finset

/-! ## 1. Orientations, slots and separation -/

/-- The orientation bit of the signed pair with label `(q, m)` and sign `σ`: `true` if the
pair is the right pair `[y, y+1]` around its slot `y`, `false` if it is `[y-1, y]`. -/
def ori (q m : ℕ) (σ : ℤ) : Bool := decide (4 ∣ q * m) == decide (σ = 1)

/-- A signed pair is the right or the left pair around its slot, according to its
orientation bit. -/
lemma signedPair_eq (q m : ℕ) (σ : ℤ) :
    signedPair q m σ =
      if ori q m σ = true then Iv.pair (slot q m σ) else Iv.pair (slot q m σ - 1) := by
  unfold ori signedPair slot neighbor
  by_cases h4 : (4 : ℕ) ∣ q * m <;> by_cases hs : σ = 1 <;> simp [h4, hs]

lemma hi_le_slot_add_one (q m : ℕ) (σ : ℤ) :
    (signedPair q m σ).hi ≤ slot q m σ + 1 := by
  rw [signedPair_eq]
  by_cases hb : ori q m σ = true <;> simp [hb, Iv.pair]

lemma slot_le_lo_add_one (q m : ℕ) (σ : ℤ) :
    slot q m σ ≤ (signedPair q m σ).lo + 1 := by
  rw [signedPair_eq]
  by_cases hb : ori q m σ = true
  · simp [hb, Iv.pair]
  · simp [hb, Iv.pair]
    omega

/-- Two signed pairs sitting at distinct slots (both multiples of `4`) are separated:
the earlier pair ends at most at `y + 1` and the later one starts at least at `y + 3`. -/
lemma sep_of_slot_ne {q m q' m' : ℕ} {σ σ' : ℤ}
    (hd : 4 ∣ slot q m σ) (hd' : 4 ∣ slot q' m' σ')
    (hne : slot q m σ ≠ slot q' m' σ') :
    Iv.Sep (signedPair q m σ) (signedPair q' m' σ') := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨l, hl⟩ := hd'
  have h1 := hi_le_slot_add_one q m σ
  have h2 := slot_le_lo_add_one q m σ
  have h3 := hi_le_slot_add_one q' m' σ'
  have h4 := slot_le_lo_add_one q' m' σ'
  unfold Iv.Sep
  omega

/-- The two endpoints of a signed pair are `q m` and the neighbour `q m + σ`, in one of the
two possible orders. -/
lemma signedPair_lo_hi (q m : ℕ) (σ : ℤ) (h2 : 2 ≤ q * m) :
    ((signedPair q m σ).lo = q * m ∧ (signedPair q m σ).hi = neighbor q m σ) ∨
      ((signedPair q m σ).lo = neighbor q m σ ∧ (signedPair q m σ).hi = q * m) := by
  by_cases hs : σ = 1
  · left
    refine ⟨?_, ?_⟩ <;> simp [signedPair, neighbor, Iv.pair, hs]
  · right
    refine ⟨?_, ?_⟩
    · simp [signedPair, neighbor, Iv.pair, hs]
    · simp [signedPair, Iv.pair, hs]
      omega

/-- If two signed pairs are equal as intervals, then either they have the same `q m`
endpoint and the same neighbour, or the roles of the two endpoints are exchanged. -/
lemma endpoints_cases {q m q' m' : ℕ} {σ σ' : ℤ} (h2 : 2 ≤ q * m) (h2' : 2 ≤ q' * m')
    (heq : signedPair q m σ = signedPair q' m' σ') :
    (q * m = q' * m' ∧ neighbor q m σ = neighbor q' m' σ') ∨
      (q * m = neighbor q' m' σ' ∧ neighbor q m σ = q' * m') := by
  have h1 := signedPair_lo_hi q m σ h2
  have h2b := signedPair_lo_hi q' m' σ' h2'
  rw [heq] at h1
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h2b with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> omega

/-- Two signed pairs (from fibers with prime-power labels) that are equal as intervals have
the same label and the same multiplier: the largest prime power dividing an endpoint of a
pair is its label. -/
lemma label_eq_of_pair_eq {ε : ℝ} {q q' : ℕ} (Fq : SignedFiber ε q) (Fq' : SignedFiber ε q')
    (hq : IsPrimePow q) (hq' : IsPrimePow q')
    {m m' : ℕ} (hm : m ∈ Fq.I) (hm' : m' ∈ Fq'.I)
    (heq : signedPair q m (Fq.σ m) = signedPair q' m' (Fq'.σ m')) :
    q = q' ∧ m = m' := by
  obtain ⟨p, a, hp, ha, hpa⟩ := hq
  obtain ⟨p', a', hp', ha', hpa'⟩ := hq'
  subst hpa; subst hpa'
  have hpN : Nat.Prime p := Nat.prime_iff.2 hp
  have hpN' : Nat.Prime p' := Nat.prime_iff.2 hp'
  have h2 : 2 ≤ p ^ a * m := Fq.two_le m hm
  have h2' : 2 ≤ p' ^ a' * m' := Fq'.two_le m' hm'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at h2; omega
    · exact h
  have hm0' : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, Nat.mul_zero] at h2'; omega
    · exact h
  have hmlt : m < p ^ a := Fq.lt m hm
  have hmlt' : m' < p' ^ a' := Fq'.lt m' hm'
  have hpm : ¬ p ∣ m :=
    (Nat.Prime.coprime_iff_not_dvd hpN).1
      ((Nat.Coprime.coprime_dvd_right (dvd_pow_self p ha.ne') (Fq.coprime m hm)).symm)
  have hpm' : ¬ p' ∣ m' :=
    (Nat.Prime.coprime_iff_not_dvd hpN').1
      ((Nat.Coprime.coprime_dvd_right (dvd_pow_self p' ha'.ne') (Fq'.coprime m' hm')).symm)
  have hQ2 : 2 ≤ p ^ a := le_trans hpN.two_le (Nat.le_self_pow ha.ne' p)
  have hQ2' : 2 ≤ p' ^ a' := le_trans hpN'.two_le (Nat.le_self_pow ha'.ne' p')
  rcases endpoints_cases h2 h2' heq with ⟨e1, _⟩ | ⟨e1, e2⟩
  · exact eq_of_mul_eq hpN hpN' ha ha' hpm hpm' hmlt hmlt' hm0 hm0' e1
  · -- the two labels would each have to be smaller than the other
    exfalso
    have hA : p ^ a ≤ p' ^ a' - 1 := by
      have hs := Fq'.smooth m' hm'
      rw [← e1] at hs
      exact hs p a hpN ha ⟨m, rfl⟩
    have hB : p' ^ a' ≤ p ^ a - 1 := by
      have hs := Fq.smooth m hm
      rw [e2] at hs
      exact hs p' a' hpN' ha' ⟨m', rfl⟩
    omega

/-! ## 2. The finite counting argument -/

section Counting

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
private lemma prod_ite_const (u : ℝ) (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∏ y ∈ s, (if p y then u else (1 : ℝ)) = u ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- The number of elements of `T` whose membership bit in `A` agrees with the prescribed
orientation `o`: the retained count of the fiber whose slot set is `T`. -/
def retCount (T : Finset ι) (o : ι → Prop) [DecidablePred o] (A : Finset ι) : ℕ :=
  (T.filter (fun y => (y ∈ A ↔ o y))).card

private lemma card_split {S T A : Finset ι} (hTS : T ⊆ S) (_hAS : A ⊆ S)
    (o : ι → Prop) [DecidablePred o] :
    (A.filter (fun y => y ∈ T ∧ o y)).card
        + ((S \ A).filter (fun y => y ∈ T ∧ ¬ o y)).card
      = retCount T o A := by
  unfold retCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hyA, hyT, ho⟩ | ⟨⟨hyS, hyA⟩, hyT, ho⟩)
      · exact ⟨hyT, by tauto⟩
      · exact ⟨hyT, by tauto⟩
    · rintro ⟨hyT, hiff⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyT, hiff.1 hyA⟩
      · exact Or.inr ⟨⟨hTS hyT, hyA⟩, hyT, fun ho => hyA (hiff.2 ho)⟩
  · rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hy hy'
    exact hy'.1.2 hy.1

/-- **The finite average identity (F11).** Summing `u ^ B(A)` over all subsets `A ⊆ S`,
where `B(A) = retCount T o A`, expands as a product over `S`. -/
lemma sum_powerset_pow (S T : Finset ι) (hTS : T ⊆ S) (o : ι → Prop) [DecidablePred o]
    (u : ℝ) :
    ∑ A ∈ S.powerset, u ^ retCount T o A = (1 + u) ^ T.card * 2 ^ (S.card - T.card) := by
  have hkey := Finset.prod_add (fun y => if y ∈ T ∧ o y then u else (1 : ℝ))
      (fun y => if y ∈ T ∧ ¬ o y then u else (1 : ℝ)) S
  have hL : ∏ y ∈ S, ((if y ∈ T ∧ o y then u else (1 : ℝ))
        + (if y ∈ T ∧ ¬ o y then u else (1 : ℝ)))
      = (1 + u) ^ T.card * 2 ^ (S.card - T.card) := by
    have h1 : ∀ y ∈ S,
        ((if y ∈ T ∧ o y then u else (1 : ℝ)) + (if y ∈ T ∧ ¬ o y then u else (1 : ℝ)))
          = if y ∈ T then 1 + u else 2 := by
      intro y _
      by_cases hy : y ∈ T
      · by_cases ho : o y
        · simp [hy, ho]
          ring
        · simp [hy, ho]
      · simp [hy]
        norm_num
    rw [Finset.prod_congr rfl h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hfil : S.filter (fun y => y ∈ T) = T := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hTS]
    have hcard : (S.filter (fun y => ¬ y ∈ T)).card = S.card - T.card := by
      have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun y => y ∈ T)
      rw [hfil] at h
      omega
    rw [hfil, hcard]
  rw [hL] at hkey
  rw [hkey]
  refine Finset.sum_congr rfl ?_
  intro A hA
  rw [Finset.mem_powerset] at hA
  rw [prod_ite_const, prod_ite_const, ← pow_add, card_split hTS hA o]

/-- **Markov / Chernoff step (F11).** The number of bit assignments retaining fewer than a
quarter of the slots of `T` is at most `2 ^ |S| (9/10) ^ |T|`. -/
lemma card_bad_le (S T : Finset ι) (hTS : T ⊆ S) (o : ι → Prop) [DecidablePred o] :
    ((S.powerset.filter (fun A => 4 * retCount T o A < T.card)).card : ℝ)
      ≤ 2 ^ S.card * (9 / 10) ^ T.card := by
  have hNS : T.card ≤ S.card := Finset.card_le_card hTS
  have hstep : ((S.powerset.filter (fun A => 4 * retCount T o A < T.card)).card : ℝ)
        * (3 / 4) ^ T.card
      ≤ ∑ A ∈ S.powerset, (81 / 256 : ℝ) ^ retCount T o A := by
    have h1 : ∀ A ∈ S.powerset.filter (fun A => 4 * retCount T o A < T.card),
        ((3 : ℝ) / 4) ^ T.card ≤ (81 / 256 : ℝ) ^ retCount T o A := by
      intro A hA
      have h4 : 4 * retCount T o A ≤ T.card := le_of_lt (Finset.mem_filter.1 hA).2
      have he : (81 / 256 : ℝ) ^ retCount T o A
          = ((3 : ℝ) / 4) ^ (4 * retCount T o A) := by
        rw [pow_mul]; norm_num
      rw [he]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h4
    calc ((S.powerset.filter (fun A => 4 * retCount T o A < T.card)).card : ℝ)
            * (3 / 4) ^ T.card
        = ∑ _A ∈ S.powerset.filter (fun A => 4 * retCount T o A < T.card),
            ((3 : ℝ) / 4) ^ T.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ A ∈ S.powerset.filter (fun A => 4 * retCount T o A < T.card),
            (81 / 256 : ℝ) ^ retCount T o A := Finset.sum_le_sum h1
      _ ≤ ∑ A ∈ S.powerset, (81 / 256 : ℝ) ^ retCount T o A := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro A _ _
          positivity
  rw [sum_powerset_pow S T hTS o] at hstep
  have hpos : (0 : ℝ) < (3 / 4) ^ T.card * 2 ^ T.card := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  have e1 : ((3 : ℝ) / 4) ^ T.card * 2 ^ T.card = (3 / 2 : ℝ) ^ T.card := by
    rw [← mul_pow]; norm_num
  have e2 : (2 : ℝ) ^ (S.card - T.card) * 2 ^ T.card = 2 ^ S.card := by
    rw [← pow_add]; congr 1; omega
  calc ((S.powerset.filter (fun A => 4 * retCount T o A < T.card)).card : ℝ)
          * ((3 / 4) ^ T.card * 2 ^ T.card)
      = (((S.powerset.filter (fun A => 4 * retCount T o A < T.card)).card : ℝ)
          * (3 / 4) ^ T.card) * 2 ^ T.card := by ring
    _ ≤ ((1 + 81 / 256 : ℝ) ^ T.card * 2 ^ (S.card - T.card)) * 2 ^ T.card :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = (337 / 256 : ℝ) ^ T.card * 2 ^ S.card := by rw [mul_assoc, e2]; norm_num
    _ ≤ (27 / 20 : ℝ) ^ T.card * 2 ^ S.card := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = 2 ^ S.card * (9 / 10) ^ T.card * ((3 / 4) ^ T.card * 2 ^ T.card) := by
        have e3 : ((9 : ℝ) / 10) * (3 / 2) = 27 / 20 := by norm_num
        rw [e1, mul_assoc, ← mul_pow, e3]
        ring

end Counting

/-! ## 3. Two elementary estimates -/

open Filter in
/-- `log 2 + 2 log q ≤ c q^δ` eventually, for any `δ, c > 0`. -/
theorem log_bound_eventually (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop, Real.log 2 + 2 * Real.log q ≤ c * (q : ℝ) ^ δ := by
  have hlo : Real.log =o[atTop] fun x : ℝ => x ^ δ := isLittleO_log_rpow_atTop hδ
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (c / 4) * ‖x ^ δ‖ := hlo.def (by positivity)
  have h1' : ∀ᶠ q : ℕ in atTop, ‖Real.log q‖ ≤ (c / 4) * ‖(q : ℝ) ^ δ‖ :=
    tendsto_natCast_atTop_atTop.eventually h1
  have h2 : Tendsto (fun q : ℕ => (q : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have h3 : ∀ᶠ q : ℕ in atTop, 2 * Real.log 2 ≤ c * (q : ℝ) ^ δ :=
    (h2.const_mul_atTop hc).eventually_ge_atTop _
  filter_upwards [h1', h3, eventually_ge_atTop 1] with q hq1 hq3 hq4
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1R
  have hrp : (0 : ℝ) ≤ (q : ℝ) ^ δ := Real.rpow_nonneg (by linarith) δ
  rw [Real.norm_of_nonneg hlogq, Real.norm_of_nonneg hrp] at hq1
  linarith

open Filter in
/-- For `q` large, `(9/10) ^ N ≤ 1 / (2 q^2)` whenever `N ≥ q^δ`.  This is the threshold
that makes the union bound (F12) work. -/
theorem geom_le_inv_sq (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, ∀ N : ℕ, (q : ℝ) ^ δ ≤ (N : ℝ) →
      ((9 : ℝ) / 10) ^ N ≤ 1 / (2 * (q : ℝ) ^ 2) := by
  have hc : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  filter_upwards [log_bound_eventually δ (Real.log (10 / 9)) hδ hc,
    eventually_ge_atTop 1] with q hq hq1 N hN
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hmul : (q : ℝ) ^ δ * Real.log (10 / 9) ≤ (N : ℝ) * Real.log (10 / 9) :=
    mul_le_mul_of_nonneg_right hN hc.le
  have hstep : Real.log 2 + 2 * Real.log q ≤ (N : ℝ) * Real.log (10 / 9) := by linarith
  have hA : (2 : ℝ) * (q : ℝ) ^ 2 ≤ (10 / 9 : ℝ) ^ N := by
    have e1 : (2 : ℝ) * (q : ℝ) ^ 2 = Real.exp (Real.log 2 + 2 * Real.log q) := by
      rw [Real.exp_add, Real.exp_log (by norm_num),
        show (2 : ℝ) * Real.log q = Real.log ((q : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (pow_pos hqpos 2)]
    have e2 : (10 / 9 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (10 / 9)) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [e1, e2]
    exact Real.exp_le_exp.2 hstep
  have h9 : ((9 : ℝ) / 10) ^ N = 1 / ((10 / 9 : ℝ) ^ N) := by
    rw [one_div, ← inv_pow]; norm_num
  rw [h9]
  exact one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2 * (q:ℝ)^2) hA

/-- The telescoping tail bound `∑_{L < q ≤ H} 1/q^2 ≤ 1/L - 1/H`. -/
theorem sum_inv_sq_le (L : ℕ) (hL : 1 ≤ L) (H : ℕ) (hLH : L ≤ H) :
    ∑ q ∈ Finset.Icc (L + 1) H, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (L : ℝ) - 1 / (H : ℝ) := by
  induction H, hLH using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; simp
  | succ H hH ih =>
      have hins : Finset.Icc (L + 1) (H + 1) = insert (H + 1) (Finset.Icc (L + 1) H) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (H + 1) ∉ Finset.Icc (L + 1) H := by simp
      rw [hins, Finset.sum_insert hnot]
      have hH0 : (0 : ℝ) < (H : ℝ) := by
        have : 0 < H := by omega
        exact_mod_cast this
      have hH1 : (0 : ℝ) < (H : ℝ) + 1 := by linarith
      have hcast : (((H + 1 : ℕ) : ℝ)) = (H : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hkey : (1 : ℝ) / ((H : ℝ) + 1) ^ 2 ≤ 1 / (H : ℝ) - 1 / ((H : ℝ) + 1) := by
        have heq : (1 : ℝ) / (H : ℝ) - 1 / ((H : ℝ) + 1) = 1 / ((H : ℝ) * ((H : ℝ) + 1)) := by
          field_simp; ring
        rw [heq]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith

end SignedF2

/-! ## 4. Lemma F2 -/

open Finset SignedF2

/-- The slot of the pair chosen at multiplier `m` in the fiber `Fq`. -/
def fslot {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (m : ℕ) : ℕ := slot q m (Fq.σ m)

/-- The orientation bit of the pair chosen at multiplier `m` in the fiber `Fq`. -/
def fori {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (m : ℕ) : Bool := ori q m (Fq.σ m)

lemma fsignedPair_eq {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (m : ℕ) :
    signedPair q m (Fq.σ m) =
      if fori Fq m = true then Iv.pair (fslot Fq m) else Iv.pair (fslot Fq m - 1) :=
  signedPair_eq q m (Fq.σ m)

/-- The set of slots occupied by the fiber `Fq`. -/
def fT {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) : Finset ℕ := Fq.I.image (fslot Fq)

/-- The orientation attached to a slot of the fiber `Fq` (slots are distinct within a
fiber, so this recovers the orientation of the unique candidate sitting at that slot). -/
def fob {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (y : ℕ) : Bool :=
  decide (∃ m ∈ Fq.I, fslot Fq m = y ∧ fori Fq m = true)

/-- The fiber `Fq` thinned by the bit assignment encoded by `A`. -/
def fJ {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (A : Finset ℕ) : Finset ℕ :=
  Fq.I.filter (fun m => (fslot Fq m ∈ A ↔ fori Fq m = true))

lemma fob_eq {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) {m : ℕ} (hm : m ∈ Fq.I) :
    (fob Fq (fslot Fq m) = true) ↔ (fori Fq m = true) := by
  unfold fob
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨m2, hm2, hslot, hori⟩
    have : m2 = m := Fq.slot_inj (Finset.mem_coe.2 hm2) (Finset.mem_coe.2 hm) hslot
    rwa [this] at hori
  · intro h; exact ⟨m, hm, rfl, h⟩

lemma fT_card {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) : (fT Fq).card = Fq.I.card :=
  Finset.card_image_of_injOn Fq.slot_inj

lemma fJ_card {ε : ℝ} {q : ℕ} (Fq : SignedFiber ε q) (A : Finset ℕ) :
    retCount (fT Fq) (fun y => fob Fq y = true) A = (fJ Fq A).card := by
  have hsub : fJ Fq A ⊆ Fq.I := Finset.filter_subset _ _
  have h1 : (fT Fq).filter (fun y => (y ∈ A ↔ fob Fq y = true)) = (fJ Fq A).image (fslot Fq) := by
    unfold fT fJ
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro m hm
    rw [fob_eq Fq hm]
  have hinj : Set.InjOn (fslot Fq) (fJ Fq A) :=
    Fq.slot_inj.mono (Finset.coe_subset.2 hsub)
  unfold retCount
  rw [h1, Finset.card_image_of_injOn hinj]

/-- **Lemma F2** (`docs/elementary_replacements.md`, Section 2, displays (F9)-(F12)).
For every `0 < ε < 1` there is a cutoff `L₀` such that, for every `L ≥ L₀`, every `H ≥ L`
and every family of signed fibers with `|I_q| ≥ q^{15ε/16}` for the prime powers
`L < q ≤ H`, one can retain at least a quarter of every fiber so that all the retained
signed pairs, across all labels, are pairwise separated. -/
theorem lemmaF2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ H : ℕ, L ≤ H →
      ∀ F : (q : ℕ) → SignedFiber ε q,
        (∀ q, IsPrimePow q → L < q → q ≤ H → (q : ℝ) ^ (15 * ε / 16) ≤ ((F q).I.card : ℝ)) →
        ∃ J : ℕ → Finset ℕ,
          (∀ q, J q ⊆ (F q).I) ∧
          (∀ q, IsPrimePow q → L < q → q ≤ H → ((F q).I.card : ℝ) / 4 ≤ ((J q).card : ℝ)) ∧
          (∀ q q' : ℕ, IsPrimePow q → L < q → q ≤ H → IsPrimePow q' → L < q' → q' ≤ H →
            ∀ m ∈ J q, ∀ m' ∈ J q', (q, m) ≠ (q', m') →
              Iv.Sep (signedPair q m ((F q).σ m)) (signedPair q' m' ((F q').σ m'))) := by
  have hδ : (0 : ℝ) < 15 * ε / 16 := by linarith
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 (geom_le_inv_sq _ hδ)
  refine ⟨max L₁ 1, ?_⟩
  intro L hL H hLH F hI
  have hL1 : 1 ≤ L := le_trans (le_max_right L₁ 1) hL
  -- the finite set of labels and the finite set of slots
  set Q : Finset ℕ := (Finset.Icc (L + 1) H).filter (fun q => IsPrimePow q) with hQdef
  have hmemQ : ∀ q, q ∈ Q ↔ (IsPrimePow q ∧ L < q ∧ q ≤ H) := by
    intro q
    rw [hQdef, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, by omega, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h3⟩, h1⟩
  set S : Finset ℕ := Q.biUnion (fun q => fT (F q)) with hSdef
  set Bad : ℕ → Finset (Finset ℕ) := fun q =>
    S.powerset.filter (fun A =>
      4 * retCount (fT (F q)) (fun y => fob (F q) y = true) A < (fT (F q)).card) with hBaddef
  have hTsub : ∀ q ∈ Q, fT (F q) ⊆ S := by
    intro q hq
    rw [hSdef]
    exact Finset.subset_biUnion_of_mem (fun q => fT (F q)) hq
  -- each label fails for few bit assignments
  have hbad : ∀ q ∈ Q, ((Bad q).card : ℝ) ≤ 2 ^ S.card * (1 / (2 * (q : ℝ) ^ 2)) := by
    intro q hq
    obtain ⟨hpp, hLq, hqH⟩ := (hmemQ q).1 hq
    have h1 := card_bad_le S (fT (F q)) (hTsub q hq) (fun y => fob (F q) y = true)
    have hNq : (q : ℝ) ^ (15 * ε / 16) ≤ ((fT (F q)).card : ℝ) := by
      rw [fT_card]; exact hI q hpp hLq hqH
    have hqL1 : L₁ ≤ q := le_trans (le_trans (le_max_left L₁ 1) hL) (by omega)
    have h2 : ((9 : ℝ) / 10) ^ (fT (F q)).card ≤ 1 / (2 * (q : ℝ) ^ 2) :=
      hL₁ q hqL1 _ hNq
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- union bound
  have hcardlt : (Q.biUnion Bad).card < S.powerset.card := by
    have h1 : ((Q.biUnion Bad).card : ℝ) ≤ ∑ q ∈ Q, ((Bad q).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ q ∈ Q, ((Bad q).card : ℝ)
        ≤ ∑ q ∈ Q, (2 : ℝ) ^ S.card * (1 / (2 * (q : ℝ) ^ 2)) := Finset.sum_le_sum hbad
    have h3 : ∑ q ∈ Q, (2 : ℝ) ^ S.card * (1 / (2 * (q : ℝ) ^ 2))
        = (2 : ℝ) ^ S.card * ∑ q ∈ Q, (1 / (2 * (q : ℝ) ^ 2)) := by rw [Finset.mul_sum]
    have h4 : ∑ q ∈ Q, (1 : ℝ) / (2 * (q : ℝ) ^ 2) ≤ 1 / 2 := by
      have hsub : ∑ q ∈ Q, (1 : ℝ) / (2 * (q : ℝ) ^ 2)
          ≤ ∑ q ∈ Finset.Icc (L + 1) H, (1 : ℝ) / (2 * (q : ℝ) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · rw [hQdef]; exact Finset.filter_subset _ _
        · intro q _ _; positivity
      have hhalf : ∑ q ∈ Finset.Icc (L + 1) H, (1 : ℝ) / (2 * (q : ℝ) ^ 2)
          = (1 / 2) * ∑ q ∈ Finset.Icc (L + 1) H, (1 : ℝ) / (q : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro q _
        ring
      have hmain := sum_inv_sq_le L hL1 H hLH
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
      have hHpos : (0 : ℝ) ≤ 1 / (H : ℝ) := by positivity
      have hLone : (1 : ℝ) / (L : ℝ) ≤ 1 := by
        rw [div_le_one hLpos]
        exact_mod_cast hL1
      rw [hhalf] at hsub
      linarith
    have h5 : ((Q.biUnion Bad).card : ℝ) ≤ (2 : ℝ) ^ S.card * (1 / 2) := by
      refine le_trans h1 (le_trans h2 ?_)
      rw [h3]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : ((Q.biUnion Bad).card : ℝ) < (2 : ℝ) ^ S.card := by
      have : (0 : ℝ) < (2 : ℝ) ^ S.card := by positivity
      linarith
    have h7 : (Q.biUnion Bad).card < 2 ^ S.card := by exact_mod_cast h6
    rwa [Finset.card_powerset]
  have hnsub : ¬ (S.powerset ⊆ Q.biUnion Bad) := by
    intro hsub
    exact absurd (Finset.card_le_card hsub) (by omega)
  obtain ⟨A, hAmem, hAnot⟩ := Finset.not_subset.1 hnsub
  have hquarter : ∀ q, IsPrimePow q → L < q → q ≤ H →
      (((F q).I.card : ℝ)) / 4 ≤ ((fJ (F q) A).card : ℝ) := by
    intro q hpp hLq hqH
    have hqQ : q ∈ Q := (hmemQ q).2 ⟨hpp, hLq, hqH⟩
    have hnb : A ∉ Bad q := fun h => hAnot (Finset.mem_biUnion.2 ⟨q, hqQ, h⟩)
    have hge : (fT (F q)).card
        ≤ 4 * retCount (fT (F q)) (fun y => fob (F q) y = true) A := by
      by_contra hcon
      refine hnb ?_
      simp only [hBaddef, Finset.mem_filter]
      exact ⟨hAmem, by omega⟩
    rw [fJ_card, fT_card] at hge
    have hR : (((F q).I.card : ℝ)) ≤ 4 * ((fJ (F q) A).card : ℝ) := by exact_mod_cast hge
    linarith
  have hsep : ∀ q q' : ℕ, IsPrimePow q → L < q → q ≤ H → IsPrimePow q' → L < q' → q' ≤ H →
      ∀ m ∈ fJ (F q) A, ∀ m' ∈ fJ (F q') A, (q, m) ≠ (q', m') →
        Iv.Sep (signedPair q m ((F q).σ m)) (signedPair q' m' ((F q').σ m')) := by
    intro q q' hpp hLq hqH hpp' hLq' hq'H m hm m' hm' hne
    simp only [fJ, Finset.mem_filter] at hm hm'
    obtain ⟨hmI, hmA⟩ := hm
    obtain ⟨hm'I, hm'A⟩ := hm'
    by_cases hslot : fslot (F q) m = fslot (F q') m'
    · exfalso
      have hiff : (fori (F q) m = true) ↔ (fori (F q') m' = true) := by
        rw [← hmA, ← hm'A, hslot]
      have hor : fori (F q) m = fori (F q') m' := by
        rcases hb : fori (F q) m with _ | _
        · rcases hb' : fori (F q') m' with _ | _
          · rfl
          · rw [hb, hb'] at hiff; simp at hiff
        · rcases hb' : fori (F q') m' with _ | _
          · rw [hb, hb'] at hiff; simp at hiff
          · rfl
      have hpair : signedPair q m ((F q).σ m) = signedPair q' m' ((F q').σ m') := by
        rw [fsignedPair_eq, fsignedPair_eq, hor, hslot]
      obtain ⟨h1, h2⟩ := label_eq_of_pair_eq (F q) (F q') hpp hpp' hmI hm'I hpair
      exact hne (by rw [h1, h2])
    · exact sep_of_slot_ne ((F q).four m hmI) ((F q').four m' hm'I) hslot
  exact ⟨fun q => fJ (F q) A, fun q => Finset.filter_subset _ _, hquarter, hsep⟩

end Erdos289
