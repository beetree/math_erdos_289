import Erdos289.Defs
import Erdos289.External

/-!
# Lemma 4: powersmooth supply

For fixed `0 < θ < 1` and `0 < a < b`, if `y = x^(θ + o(1))` then the number of integers in
`[a x, b x]` that are not `y`-powersmooth is at most `((b - a) log (1/θ) + o(1)) x`.

The `o(1)` conditions are made explicit: for every slack `δ > 0` there is an exponent window
`η > 0` and a threshold `X₀` such that the bound holds for all `x ≥ X₀` and all
`y ∈ [x^(θ-η), x^(θ+η)]`.
-/

namespace Erdos289

open Finset Filter Topology

open Classical in
/-- The integers in the real interval `[a x, b x]` that are not `y`-powersmooth. -/
noncomputable def notSmooth (y : ℕ) (a b x : ℝ) : Finset ℕ :=
  (Icc ⌈a * x⌉₊ ⌊b * x⌋₊).filter (fun n => ¬ Powersmooth y n)

/-! ## Counting multiples in an interval -/

/-- The number of multiples of `d` in `Icc A B` (with `A ≤ B`) is at most `(B - A) / d + 2`,
as a real inequality (`d ≥ 1`). Proved by injecting multiples `n` into `Icc (A / d) (B / d)`
via `n ↦ n / d`. -/
lemma card_filter_dvd_Icc_le (A B d : ℕ) (hd : 0 < d) (hAB : A ≤ B) :
    (((Icc A B).filter (d ∣ ·)).card : ℝ) ≤ (B : ℝ) / d - (A : ℝ) / d + 2 := by
  have hmap : ∀ n ∈ (Icc A B).filter (d ∣ ·), n / d ∈ Icc (A / d) (B / d) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hA, hB⟩, _⟩ := hn
    exact mem_Icc.mpr ⟨Nat.div_le_div_right hA, Nat.div_le_div_right hB⟩
  have hinj : Set.InjOn (fun n => n / d) ((Icc A B).filter (d ∣ ·) : Finset ℕ) := by
    intro n1 hn1 n2 hn2 heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_Icc] at hn1 hn2
    obtain ⟨_, hd1⟩ := hn1
    obtain ⟨_, hd2⟩ := hn2
    have e1 : n1 = d * (n1 / d) := (Nat.mul_div_cancel' hd1).symm
    have e2 : n2 = d * (n2 / d) := (Nat.mul_div_cancel' hd2).symm
    rw [e1, e2]
    exact congrArg (d * ·) heq
  have hcard : ((Icc A B).filter (d ∣ ·)).card ≤ (Icc (A / d) (B / d)).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  have hcard2 : (Icc (A / d) (B / d)).card = B / d + 1 - A / d := Nat.card_Icc _ _
  rw [hcard2] at hcard
  have hle : A / d ≤ B / d + 1 := le_trans (Nat.div_le_div_right hAB) (Nat.le_succ _)
  have hR : ((B / d + 1 - A / d : ℕ) : ℝ) = (B / d : ℕ) - (A / d : ℕ) + 1 := by
    have := Nat.cast_sub (R := ℝ) hle
    push_cast at this ⊢
    linarith
  have hBd : ((B / d : ℕ) : ℝ) ≤ (B : ℝ) / d := Nat.cast_div_le
  have hAd : (A : ℝ) / d - 1 ≤ ((A / d : ℕ) : ℝ) := by
    have hlt : A < d * (A / d) + d := by
      have hmod : A % d < d := Nat.mod_lt A hd
      have heq : d * (A / d) + A % d = A := Nat.div_add_mod A d
      omega
    have h2 : (A : ℝ) < ((A / d : ℕ) : ℝ) * d + d := by
      have : (A : ℝ) < (d : ℝ) * ((A / d : ℕ) : ℝ) + d := by exact_mod_cast hlt
      linarith
    have h3 : (A : ℝ) / d < ((A / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast hd)]
      linarith
    linarith
  calc (((Icc A B).filter (d ∣ ·)).card : ℝ)
      ≤ ((B / d + 1 - A / d : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (B / d : ℕ) - (A / d : ℕ) + 1 := hR
    _ ≤ (B : ℝ) / d - ((A : ℝ) / d - 1) + 1 := by linarith
    _ = (B : ℝ) / d - (A : ℝ) / d + 2 := by ring

/-! ## Covering non-powersmooth integers by multiples -/

open Classical in
/-- Every non-`y`-powersmooth `n ∈ [ax, bx]` is a multiple of some prime `p ∈ (y, bx]`, or a
multiple of `u_p := p ^ (⌊log_p y⌋ + 1)` (the smallest power of `p` exceeding `y`) for some
prime `p ≤ y`. -/
lemma notSmooth_subset (y : ℕ) (a b x : ℝ) (hax : 0 < a * x) :
    notSmooth y a b x ⊆
      ((Finset.Ioc y ⌊b * x⌋₊).filter Nat.Prime).biUnion
          (fun p => (Icc ⌈a * x⌉₊ ⌊b * x⌋₊).filter (p ∣ ·)) ∪
      ((Finset.Icc 1 y).filter Nat.Prime).biUnion
          (fun p => (Icc ⌈a * x⌉₊ ⌊b * x⌋₊).filter ((p ^ (Nat.log p y + 1)) ∣ ·)) := by
  intro n hn
  simp only [notSmooth, mem_filter, mem_Icc] at hn
  obtain ⟨⟨hnA, hnB⟩, hnp⟩ := hn
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.ceil_pos.mpr hax) hnA
  unfold Powersmooth at hnp
  push_neg at hnp
  obtain ⟨p, e, hp, he, hpe, hgt⟩ := hnp
  rw [Finset.mem_union]
  by_cases hpy : p ≤ y
  · right
    have hp2 : 2 ≤ p := hp.two_le
    have hy0 : y ≠ 0 := by
      rintro rfl
      omega
    have hple : p ^ Nat.log p y ≤ y := Nat.pow_log_le_self p hy0
    have hlogsucc : Nat.log p y + 1 ≤ e := by
      by_contra hcon
      push_neg at hcon
      have hcon' : e ≤ Nat.log p y := by omega
      have : p ^ e ≤ p ^ Nat.log p y := Nat.pow_le_pow_right hp.one_lt.le hcon'
      omega
    have hdvd : p ^ (Nat.log p y + 1) ∣ n := dvd_trans (pow_dvd_pow p hlogsucc) hpe
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpy⟩, hp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnA, hnB⟩, hdvd⟩
  · left
    have hpy' : y < p := by omega
    have hpdvd : p ∣ n := dvd_trans (dvd_pow_self p he.ne') hpe
    have hpB : p ≤ n := Nat.le_of_dvd hn0 hpdvd
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpy', hpB.trans hnB⟩, hp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnA, hnB⟩, hpdvd⟩

/-- Real-valued card bound on `notSmooth`, splitting into the two sums from
`notSmooth_subset`. -/
lemma notSmooth_card_le (y : ℕ) (a b x : ℝ) (hax : 0 < a * x)
    (hAB : ⌈a * x⌉₊ ≤ ⌊b * x⌋₊) :
    ((notSmooth y a b x).card : ℝ) ≤
      (∑ p ∈ (Finset.Ioc y ⌊b * x⌋₊).filter Nat.Prime,
          (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / p + 2)) +
      (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
          (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / (p ^ (Nat.log p y + 1)) + 2)) := by
  set A := ⌈a * x⌉₊ with hAdef
  set B := ⌊b * x⌋₊ with hBdef
  have hcardU : (notSmooth y a b x).card ≤
      (((Finset.Ioc y B).filter Nat.Prime).biUnion (fun p => (Icc A B).filter (p ∣ ·))).card +
      (((Finset.Icc 1 y).filter Nat.Prime).biUnion
        (fun p => (Icc A B).filter ((p ^ (Nat.log p y + 1)) ∣ ·))).card :=
    le_trans (Finset.card_le_card (notSmooth_subset y a b x hax)) (Finset.card_union_le _ _)
  have hb1 : (((Finset.Ioc y B).filter Nat.Prime).biUnion (fun p => (Icc A B).filter (p ∣ ·))).card
      ≤ ∑ p ∈ (Finset.Ioc y B).filter Nat.Prime, ((Icc A B).filter (p ∣ ·)).card :=
    Finset.card_biUnion_le
  have hb2 : (((Finset.Icc 1 y).filter Nat.Prime).biUnion
        (fun p => (Icc A B).filter ((p ^ (Nat.log p y + 1)) ∣ ·))).card
      ≤ ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
          ((Icc A B).filter ((p ^ (Nat.log p y + 1)) ∣ ·)).card :=
    Finset.card_biUnion_le
  have hcardN : (notSmooth y a b x).card ≤
      (∑ p ∈ (Finset.Ioc y B).filter Nat.Prime, ((Icc A B).filter (p ∣ ·)).card) +
      (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
          ((Icc A B).filter ((p ^ (Nat.log p y + 1)) ∣ ·)).card) := by
    omega
  have hcardR : ((notSmooth y a b x).card : ℝ) ≤
      (∑ p ∈ (Finset.Ioc y B).filter Nat.Prime, (((Icc A B).filter (p ∣ ·)).card : ℝ)) +
      (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
          (((Icc A B).filter ((p ^ (Nat.log p y + 1)) ∣ ·)).card : ℝ)) := by
    exact_mod_cast hcardN
  refine hcardR.trans (add_le_add ?_ ?_)
  · apply Finset.sum_le_sum
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    rw [sub_div]
    exact card_filter_dvd_Icc_le A B p (by omega) hAB
  · apply Finset.sum_le_sum
    intro p hp
    simp only [mem_filter, mem_Icc] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    rw [sub_div, ← Nat.cast_pow]
    exact card_filter_dvd_Icc_le A B (p ^ (Nat.log p y + 1)) (by positivity) hAB

/-! ## An asymptotic gap estimate from Mertens' second theorem -/

/-- Consequence of `mertens_second`: for `X₁ ≤ y ≤ z`, the sum of reciprocals of primes in
`(y, z]` is at most `log(log z / log y) + ε`. -/
lemma mertens_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ X₁ : ℕ, 2 ≤ X₁ ∧ ∀ y z : ℕ, X₁ ≤ y → y ≤ z →
      (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / p) ≤
        Real.log (Real.log z / Real.log y) + ε := by
  obtain ⟨B₁, hB⟩ := mertens_second
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hB (ε / 2) (by linarith)
  refine ⟨max N 2, le_max_right _ _, fun y z hy hyz => ?_⟩
  have hyN : N ≤ y := le_trans (le_max_left _ _) hy
  have hzN : N ≤ z := le_trans hyN hyz
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hy
  have hz2 : 2 ≤ z := le_trans hy2 hyz
  have hdy := hN y hyN
  have hdz := hN z hzN
  rw [Real.dist_eq] at hdy hdz
  set S : ℕ → ℝ := fun x => ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p with hSdef
  have hsplit : (Finset.range (z + 1)).filter Nat.Prime =
      (Finset.range (y + 1)).filter Nat.Prime ∪ (Finset.Ioc y z).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hp1, hp2⟩
      by_cases hc : p < y + 1
      · exact Or.inl ⟨hc, hp2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp2⟩
    · rintro (⟨hp1, hp2⟩ | ⟨⟨hp1, hp2⟩, hp3⟩)
      · exact ⟨by omega, hp2⟩
      · exact ⟨by omega, hp3⟩
  have hdisj : Disjoint ((Finset.range (y + 1)).filter Nat.Prime)
      ((Finset.Ioc y z).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [mem_filter, mem_range] at hp1
    simp only [mem_filter, mem_Ioc] at hp2
    omega
  have hSsplit : S z = S y + ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / p := by
    simp only [hSdef, hsplit]
    rw [Finset.sum_union hdisj]
  have habs : |(S z - Real.log (Real.log z)) - (S y - Real.log (Real.log y))| < ε := by
    calc |(S z - Real.log (Real.log z)) - (S y - Real.log (Real.log y))|
        = |(S z - Real.log (Real.log z) - B₁) - (S y - Real.log (Real.log y) - B₁)| := by ring_nf
      _ ≤ |S z - Real.log (Real.log z) - B₁| + |S y - Real.log (Real.log y) - B₁| :=
          abs_sub _ _
      _ < ε := by linarith
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast hy2
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlogdiv : Real.log (Real.log z) - Real.log (Real.log y)
      = Real.log (Real.log z / Real.log y) := (Real.log_div hlogz.ne' hlogy.ne').symm
  have := abs_lt.mp habs
  rw [hSsplit] at this
  have hfin : ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / p
      ≤ (Real.log (Real.log z) - Real.log (Real.log y)) + ε := by linarith [this.2]
  rw [hlogdiv] at hfin
  exact hfin

set_option maxHeartbeats 4000000 in
/-- **Lemma 4** of the paper (powersmooth supply). -/
theorem lemma4 (θ a b : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a) (hab : a < b)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ y : ℕ,
      x ^ (θ - η) ≤ y → (y : ℝ) ≤ x ^ (θ + η) →
      ((notSmooth y a b x).card : ℝ) ≤ ((b - a) * Real.log (1 / θ) + δ) * x := by
  have hb0 : 0 < b := lt_trans ha hab
  have hba : 0 < b - a := sub_pos.mpr hab
  obtain ⟨C, hC⟩ := primeCounting_le
  obtain ⟨C', hC'def⟩ : ∃ C', C' = max C 1 := ⟨max C 1, rfl⟩
  have hC'pos : (0:ℝ) < C' := by rw [hC'def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC2 : ∀ x : ℕ, 2 ≤ x → (Nat.primeCounting x : ℝ) ≤ C' * x / Real.log x := by
    intro x hx
    have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
    have hlogpos : 0 < Real.log (x:ℝ) := Real.log_pos hx1
    have hxnn : (0:ℝ) ≤ (x:ℝ) := by positivity
    calc (Nat.primeCounting x : ℝ) ≤ C * x / Real.log x := hC x hx
      _ ≤ C' * x / Real.log x := by
          gcongr
          rw [hC'def]; exact le_max_left _ _
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = δ / (4 * (b - a)) := ⟨δ / (4 * (b - a)), rfl⟩
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨η, hηdef⟩ : ∃ η, η = min (θ / 2) (min ((1 - θ) / 2) (θ * κ / 6)) := ⟨min (θ / 2) (min ((1 - θ) / 2) (θ * κ / 6)), rfl⟩
  have hηpos : 0 < η := by
    rw [hηdef]
    have h1 : 0 < θ / 2 := by positivity
    have h2 : 0 < (1 - θ) / 2 := by linarith
    have h3 : 0 < θ * κ / 6 := by positivity
    exact lt_min h1 (lt_min h2 h3)
  have hη1 : η ≤ θ / 2 := by rw [hηdef]; exact min_le_left _ _
  have hη2 : η ≤ (1 - θ) / 2 := by rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη3 : η ≤ θ * κ / 6 := by rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨X₁, hX₁2, hgap⟩ := mertens_gap (κ / 3) (by positivity)
  refine ⟨η, hηpos, ?_⟩
  obtain ⟨M1, hM1def⟩ : ∃ M1, M1 = 2 * Real.log X₁ / θ := ⟨2 * Real.log X₁ / θ, rfl⟩
  obtain ⟨M4, hM4def⟩ : ∃ M4, M4 = 2 * max (Real.log (2 / b)) 0 / (1 - θ) := ⟨2 * max (Real.log (2 / b)) 0 / (1 - θ), rfl⟩
  obtain ⟨M5, hM5def⟩ : ∃ M5, M5 = 2 * C' / (θ * κ) := ⟨2 * C' / (θ * κ), rfl⟩
  obtain ⟨M6, hM6def⟩ : ∃ M6, M6 = 8 * C' * b / δ - Real.log b + Real.log 2 := ⟨8 * C' * b / δ - Real.log b + Real.log 2, rfl⟩
  obtain ⟨M7a, hM7adef⟩ : ∃ M7a, M7a = 2 / θ := ⟨2 / θ, rfl⟩
  obtain ⟨M7b, hM7bdef⟩ : ∃ M7b, M7b = 2 * max (Real.log (8 * C' / δ)) 0 / (1 - θ) := ⟨2 * max (Real.log (8 * C' / δ)) 0 / (1 - θ), rfl⟩
  obtain ⟨M9, hM9def⟩ : ∃ M9, M9 = 6 * max (Real.log b) 0 / (θ * κ) := ⟨6 * max (Real.log b) 0 / (θ * κ), rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = max M1 (max M4 (max M5 (max M6 (max M7a (max M7b M9))))) := ⟨max M1 (max M4 (max M5 (max M6 (max M7a (max M7b M9))))), rfl⟩
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = max (Real.exp M) (max (4 / b) (2 / (b - a))) := ⟨max (Real.exp M) (max (4 / b) (2 / (b - a))), rfl⟩
  refine ⟨X₀, fun x hxX0 y hy1 hy2 => ?_⟩
  have hX1pos : (1:ℝ) < X₁ := by exact_mod_cast hX₁2
  have hM1pos : 0 < M1 := by
    rw [hM1def]
    have : 0 < Real.log X₁ := Real.log_pos hX1pos
    positivity
  have hMpos : 0 < M := by rw [hMdef]; exact lt_of_lt_of_le hM1pos (le_max_left _ _)
  have hxX0' : max (Real.exp M) (max (4 / b) (2 / (b - a))) ≤ x := hX₀def ▸ hxX0
  have hxgeexp : Real.exp M ≤ x := le_trans (le_max_left _ _) hxX0'
  have hx2 : max (4 / b) (2 / (b - a)) ≤ x := le_trans (le_max_right _ _) hxX0'
  have hxge2b : 4 / b ≤ x := le_trans (le_max_left _ _) hx2
  have hxge2ba : 2 / (b - a) ≤ x := le_trans (le_max_right _ _) hx2
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos M) hxgeexp
  have hM1M : M1 ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM4M : M4 ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM5M : M5 ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM6M : M6 ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM7aM : M7a ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM7bM : M7b ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hM9M : M9 ≤ M := by rw [hMdef]; simp [le_max_iff]
  have hlogx : M ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxgeexp
  have hx1 : 1 < x := by
    have : (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
    rw [this]
    exact lt_of_lt_of_le (Real.exp_lt_exp.mpr hMpos) hxgeexp
  have hθηpos : 0 < θ - η := by linarith
  have hθηpos' : 0 < θ + η := by linarith
  have hxθηgt1 : 1 < x ^ (θ - η) :=
    (Real.one_lt_rpow_iff_of_pos hxpos).mpr (Or.inl ⟨hx1, hθηpos⟩)
  have hy1lt : (1:ℝ) < (y:ℝ) := lt_of_lt_of_le hxθηgt1 hy1
  have hy2nat : 2 ≤ y := by exact_mod_cast hy1lt
  have hypos' : (0:ℝ) < (y:ℝ) := by linarith
  have h1θη2 : 0 < 1 - θ - η := by linarith
  have hbig1 : (θ / 2) * M ≤ (θ - η) * Real.log x := by
    have s1 : (θ / 2) * M ≤ (θ - η) * M := mul_le_mul_of_nonneg_right (by linarith) hMpos.le
    have s2 : (θ - η) * M ≤ (θ - η) * Real.log x := mul_le_mul_of_nonneg_left hlogx hθηpos.le
    linarith
  have hbig2 : ((1 - θ) / 2) * M ≤ (1 - θ - η) * Real.log x := by
    have s1 : ((1 - θ) / 2) * M ≤ (1 - θ - η) * M := mul_le_mul_of_nonneg_right (by linarith) hMpos.le
    have s2 : (1 - θ - η) * M ≤ (1 - θ - η) * Real.log x := mul_le_mul_of_nonneg_left hlogx h1θη2.le
    linarith
  have hlogy_ge : (θ - η) * Real.log x ≤ Real.log y := by
    have h1 : Real.log (x ^ (θ - η)) ≤ Real.log y :=
      Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hy1
    rwa [Real.log_rpow hxpos] at h1
  have hlogy_le : Real.log y ≤ (θ + η) * Real.log x := by
    have h1 : Real.log y ≤ Real.log (x ^ (θ + η)) :=
      Real.log_le_log hypos' hy2
    rwa [Real.log_rpow hxpos] at h1
  -- y ≥ X₁
  have hX1pos' : (0:ℝ) < (X₁:ℝ) := by linarith
  have eM1 : (θ / 2) * M1 = Real.log X₁ := by rw [hM1def]; field_simp
  have hyX1 : X₁ ≤ y := by
    have s1 : (θ / 2) * M1 ≤ (θ / 2) * M := mul_le_mul_of_nonneg_left hM1M (by positivity)
    have : Real.log X₁ ≤ Real.log y := by linarith
    have := (Real.log_le_log_iff hX1pos' hypos').mp this
    exact_mod_cast this
  -- B ≥ b*x/2, from x ≥ 4/b
  have hbxge4 : 4 ≤ b * x := by
    rw [div_le_iff₀ hb0] at hxge2b
    linarith
  have hBge : b * x / 2 ≤ (⌊b * x⌋₊ : ℝ) := by
    have h1 : b * x - 1 ≤ (⌊b * x⌋₊ : ℝ) := by
      have := Nat.sub_one_lt_floor (b * x)
      linarith
    linarith
  have hBpos : (0:ℝ) < (⌊b * x⌋₊ : ℝ) := by
    have : (0:ℝ) < b * x / 2 := by positivity
    linarith
  have hB2 : (2:ℝ) ≤ (⌊b * x⌋₊ : ℝ) := by linarith
  have hB2nat : 2 ≤ ⌊b * x⌋₊ := by exact_mod_cast hB2
  -- y ≤ B
  have h1θ0 : (0:ℝ) < 1 - θ := by linarith
  have eM4 : ((1 - θ) / 2) * M4 = max (Real.log (2 / b)) 0 := by rw [hM4def]; field_simp
  have hlog2b_le : Real.log (2 / b) ≤ (1 - θ - η) * Real.log x := by
    have s1 : ((1 - θ) / 2) * M4 ≤ ((1 - θ) / 2) * M := mul_le_mul_of_nonneg_left hM4M (by positivity)
    have s2 : max (Real.log (2 / b)) 0 ≤ (1 - θ - η) * Real.log x := by
      rw [← eM4]; linarith
    linarith [le_max_left (Real.log (2 / b)) 0]
  have hxpow_neg_le : x ^ (θ + η - 1) ≤ b / 2 := by
    have hb2pos : (0:ℝ) < b / 2 := by positivity
    have hxpowpos : (0:ℝ) < x ^ (θ + η - 1) := Real.rpow_pos_of_pos hxpos _
    rw [← Real.log_le_log_iff hxpowpos hb2pos, Real.log_rpow hxpos]
    have hlogb2 : Real.log (b / 2) = -Real.log (2 / b) := by
      rw [show b / 2 = (2 / b)⁻¹ by field_simp, Real.log_inv]
    rw [hlogb2]
    linarith
  have hxpow_eq : x ^ (θ + η - 1) = x ^ (θ + η) / x := Real.rpow_sub_one hxpos.ne' _
  have hyB : (y:ℝ) ≤ (⌊b * x⌋₊ : ℝ) := by
    have h1 : x ^ (θ + η) ≤ b / 2 * x := by
      rw [hxpow_eq] at hxpow_neg_le
      rw [div_le_iff₀ hxpos] at hxpow_neg_le
      linarith
    have h2 : b / 2 * x = b * x / 2 := by ring
    linarith [hy2, hBge]
  have hynatB : y ≤ ⌊b * x⌋₊ := by exact_mod_cast hyB
  -- A ≤ B
  have hax_nonneg : (0:ℝ) ≤ a * x := by positivity
  have hA_lt : (⌈a * x⌉₊ : ℝ) < a * x + 1 := Nat.ceil_lt_add_one hax_nonneg
  have hB_gt : b * x - 1 < (⌊b * x⌋₊ : ℝ) := Nat.sub_one_lt_floor (b * x)
  have hba_x : 2 ≤ x * (b - a) := by
    rw [div_le_iff₀ hba] at hxge2ba
    exact hxge2ba
  have hba_x' : 2 ≤ b * x - a * x := by
    have e : x * (b - a) = b * x - a * x := by ring
    linarith only [hba_x, e]
  have hAB : ⌈a * x⌉₊ ≤ ⌊b * x⌋₊ := by
    have : (⌈a * x⌉₊ : ℝ) ≤ (⌊b * x⌋₊ : ℝ) := by linarith only [hA_lt, hB_gt, hba_x']
    exact_mod_cast this
  have hax : (0:ℝ) < a * x := by positivity
  -- primeCounting cardinality facts
  have hpc : ∀ n : ℕ, ((Finset.range (n + 1)).filter Nat.Prime).card = Nat.primeCounting n := by
    intro n
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hcardB : ((Finset.Ioc y ⌊b * x⌋₊).filter Nat.Prime).card ≤ Nat.primeCounting ⌊b * x⌋₊ := by
    rw [← hpc]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro p hp
    simp only [mem_Ioc, mem_range] at hp ⊢
    omega
  have hcardy : ((Finset.Icc 1 y).filter Nat.Prime).card ≤ Nat.primeCounting y := by
    rw [← hpc]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro p hp
    simp only [mem_Icc, mem_range] at hp ⊢
    omega
  have hA_ge : a * x ≤ (⌈a * x⌉₊ : ℝ) := Nat.le_ceil _
  have hB_le : (⌊b * x⌋₊ : ℝ) ≤ b * x := Nat.floor_le (by positivity)
  have hBAle : (⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ) ≤ (b - a) * x := by
    have e : (b - a) * x = b * x - a * x := by ring
    linarith only [hA_ge, hB_le, e]
  obtain ⟨S1, hS1def⟩ : ∃ S1, S1 = (Finset.Ioc y ⌊b * x⌋₊).filter Nat.Prime := ⟨(Finset.Ioc y ⌊b * x⌋₊).filter Nat.Prime, rfl⟩
  obtain ⟨S2, hS2def⟩ : ∃ S2, S2 = (Finset.Icc 1 y).filter Nat.Prime := ⟨(Finset.Icc 1 y).filter Nat.Prime, rfl⟩
  have hSum1 : (∑ p ∈ S1, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / p + 2)) ≤
      (b - a) * x * (∑ p ∈ S1, (1 : ℝ) / p) + 2 * S1.card := by
    have step1 : (∑ p ∈ S1, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / p + 2)) ≤
        ∑ p ∈ S1, ((b - a) * x / p + 2) := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [hS1def, mem_filter, mem_Ioc] at hp
      have hppos : (0:ℝ) < (p:ℝ) := by
        have : 0 < p := hp.2.pos
        exact_mod_cast this
      gcongr
    have step2 : (∑ p ∈ S1, ((b - a) * x / p + 2)) =
        (b - a) * x * (∑ p ∈ S1, (1 : ℝ) / p) + 2 * S1.card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro p _
        ring
      · ring
    linarith [step1, step2]
  have hcnn : (0:ℝ) ≤ (⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ) := by
    have : (⌈a * x⌉₊ : ℝ) ≤ (⌊b * x⌋₊ : ℝ) := by exact_mod_cast hAB
    linarith
  have hSum2 : (∑ p ∈ S2, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / (p ^ (Nat.log p y + 1)) + 2)) ≤
      (b - a) * x / y * S2.card + 2 * S2.card := by
    have step1 : (∑ p ∈ S2, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / (p ^ (Nat.log p y + 1)) + 2)) ≤
        ∑ p ∈ S2, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / y + 2) := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [hS2def, mem_filter, mem_Icc] at hp
      have hp2 : 2 ≤ p := hp.2.two_le
      have hu : y < p ^ (Nat.log p y + 1) := Nat.lt_pow_succ_log_self (by omega) y
      have huR : (y:ℝ) ≤ (p:ℝ) ^ (Nat.log p y + 1) := by exact_mod_cast hu.le
      have hyRpos : (0:ℝ) < (y:ℝ) := hypos'
      gcongr
    have step2 : (∑ p ∈ S2, (((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / y + 2)) =
        ((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / y * S2.card + 2 * S2.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      ring
    have step3 : ((⌊b * x⌋₊ : ℝ) - (⌈a * x⌉₊ : ℝ)) / y * S2.card ≤ (b - a) * x / y * S2.card := by
      gcongr
    linarith [step1, step2, step3]
  have log_add_le : ∀ u t : ℝ, 0 < u → 0 ≤ t → Real.log (u + t) ≤ Real.log u + t / u := by
    intro u t hu ht
    have hut : (0:ℝ) < 1 + t / u := by positivity
    have e1 : u + t = u * (1 + t / u) := by field_simp
    rw [e1, Real.log_mul hu.ne' hut.ne']
    have h2 : Real.log (1 + t / u) ≤ (1 + t / u) - 1 := Real.log_le_sub_one_of_pos hut
    linarith
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le hMpos hlogx
  have hprodpos : 0 < (θ - η) * Real.log x := mul_pos hθηpos hlogxpos
  have hlogypos : 0 < Real.log y := lt_of_lt_of_le hprodpos hlogy_ge
  have hB2R : (1:ℝ) < (⌊b * x⌋₊ : ℝ) := by exact_mod_cast hB2nat
  have hlogB_le : Real.log (⌊b * x⌋₊:ℝ) ≤ Real.log b + Real.log x := by
    have h1 : Real.log (⌊b * x⌋₊:ℝ) ≤ Real.log (b * x) := Real.log_le_log hBpos hB_le
    rwa [Real.log_mul hb0.ne' hxpos.ne'] at h1
  have hlogbx_pos : 0 < Real.log b + Real.log x :=
    lt_of_lt_of_le (Real.log_pos hB2R) hlogB_le
  -- log b / ((θ-η) log x) ≤ κ/3
  have eq9 : θ / 2 * M9 = 3 * max (Real.log b) 0 / κ := by rw [hM9def]; field_simp; ring
  have step_a : θ / 2 * M9 ≤ (θ - η) * Real.log x :=
    le_trans (mul_le_mul_of_nonneg_left hM9M (by positivity)) hbig1
  have hYX : 3 * max (Real.log b) 0 / κ ≤ (θ - η) * Real.log x := eq9 ▸ step_a
  have step_b : κ / 3 * (3 * max (Real.log b) 0 / κ) ≤ κ / 3 * ((θ - η) * Real.log x) :=
    mul_le_mul_of_nonneg_left hYX (by positivity)
  have eq_simp : κ / 3 * (3 * max (Real.log b) 0 / κ) = max (Real.log b) 0 := by
    field_simp
  have hlogb_term : Real.log b / ((θ - η) * Real.log x) ≤ κ / 3 := by
    rw [div_le_iff₀ hprodpos]
    linarith only [step_b, eq_simp.symm.le, eq_simp.le, le_max_left (Real.log b) 0]
  have step_div : (Real.log b + Real.log x) / Real.log y ≤
      (Real.log b + Real.log x) / ((θ - η) * Real.log x) := by
    gcongr
  have step_eq : (Real.log b + Real.log x) / ((θ - η) * Real.log x) =
      1 / (θ - η) + Real.log b / ((θ - η) * Real.log x) := by
    field_simp
    ring
  have hratio_le : (Real.log b + Real.log x) / Real.log y ≤ 1 / (θ - η) + κ / 3 := by
    rw [step_eq] at step_div
    linarith only [step_div, hlogb_term]
  have hlogBy_le : Real.log (⌊b * x⌋₊:ℝ) / Real.log y ≤ 1 / (θ - η) + κ / 3 := by
    have step_div2 : Real.log (⌊b * x⌋₊:ℝ) / Real.log y ≤
        (Real.log b + Real.log x) / Real.log y := by
      gcongr
    linarith only [step_div2, hratio_le]
  have hratio_pos : 0 < Real.log (⌊b * x⌋₊:ℝ) / Real.log y := div_pos (Real.log_pos hB2R) hlogypos
  have step_logmono : Real.log (Real.log (⌊b * x⌋₊:ℝ) / Real.log y) ≤
      Real.log (1 / (θ - η) + κ / 3) :=
    Real.log_le_log hratio_pos hlogBy_le
  have hstep1 : Real.log (1 / (θ - η) + κ / 3) ≤
      Real.log (1 / (θ - η)) + (κ / 3) / (1 / (θ - η)) :=
    log_add_le (1 / (θ - η)) (κ / 3) (by positivity) (by positivity)
  have heq1 : (κ / 3) / (1 / (θ - η)) = κ / 3 * (θ - η) := by
    field_simp
  have heq2 : 1 / (θ - η) = 1 / θ + η / (θ * (θ - η)) := by
    field_simp
    ring
  have hstep2 : Real.log (1 / θ + η / (θ * (θ - η))) ≤
      Real.log (1 / θ) + (η / (θ * (θ - η))) / (1 / θ) :=
    log_add_le (1 / θ) (η / (θ * (θ - η))) (by positivity) (by positivity)
  have heq3 : (η / (θ * (θ - η))) / (1 / θ) = η / (θ - η) := by
    field_simp
  have hetaterm : η / (θ - η) ≤ 2 * η / θ := by
    have hgc : η / (θ - η) ≤ η / (θ / 2) := by gcongr; linarith only [hη1]
    have e : η / (θ / 2) = 2 * η / θ := by field_simp
    linarith only [hgc, e.le, e.symm.le]
  have h2etatheta : 2 * η / θ ≤ κ / 3 := by
    rw [div_le_iff₀ hθ0]
    have ebridge : κ / 3 * θ = 2 * (θ * κ / 6) := by ring
    linarith only [hη3, ebridge]
  have hcterm : κ / 3 * (θ - η) ≤ κ / 3 := by
    have hθη_lt1 : θ - η < 1 := by linarith
    have := mul_le_mul_of_nonneg_left hθη_lt1.le (by positivity : (0:ℝ) ≤ κ / 3)
    linarith only [this]
  have hA1 : Real.log (1 / (θ - η)) ≤ Real.log (1 / θ) + η / (θ - η) := by
    rw [heq3] at hstep2
    rw [heq2]
    exact hstep2
  have hA2 : Real.log (1 / (θ - η) + κ / 3) ≤ Real.log (1 / (θ - η)) + κ / 3 * (θ - η) := by
    rw [heq1] at hstep1
    exact hstep1
  have hlogratio : Real.log (Real.log (⌊b * x⌋₊:ℝ) / Real.log y) ≤ Real.log (1 / θ) + 2 * κ / 3 := by
    linarith only [step_logmono, hA2, hA1, hetaterm, hcterm, h2etatheta]
  have hgapB := hgap y ⌊b * x⌋₊ hyX1 hynatB
  have hT1 : (∑ p ∈ S1, (1:ℝ) / p) ≤ Real.log (1 / θ) + κ := by
    rw [hS1def]
    linarith only [hgapB, hlogratio]
  -- π(y)/y ≤ κ
  have eq5 : θ / 2 * M5 = C' / κ := by rw [hM5def]; field_simp
  have step_a5 : θ / 2 * M5 ≤ (θ - η) * Real.log x :=
    le_trans (mul_le_mul_of_nonneg_left hM5M (by positivity)) hbig1
  have hlogy_Cκ : C' / κ ≤ Real.log y := by
    rw [← eq5]; linarith only [step_a5, hlogy_ge]
  have hCley : C' ≤ Real.log y * κ := (div_le_iff₀ hκpos).mp hlogy_Cκ
  have hπy_le : (Nat.primeCounting y : ℝ) ≤ C' * y / Real.log y := hC2 y hy2nat
  have hπy_div : (Nat.primeCounting y : ℝ) / y ≤ κ := by
    rw [div_le_iff₀ hypos']
    have hstep : C' * y / Real.log y ≤ κ * y := by
      rw [div_le_iff₀ hlogypos]
      have hstep2 : C' * y ≤ Real.log y * κ * y := mul_le_mul_of_nonneg_right hCley hypos'.le
      have ering : Real.log y * κ * y = κ * y * Real.log y := by ring
      linarith only [hstep2, ering.le, ering.symm.le]
    linarith only [hπy_le, hstep]
  -- (b-a)x/y * S2.card ≤ (δ/4) x
  have hcardy_le : (S2.card:ℝ) ≤ (Nat.primeCounting y : ℝ) := by
    rw [hS2def]; exact_mod_cast hcardy
  have hterm_B : (b - a) * x / y * S2.card ≤ δ / 4 * x := by
    have h1 : (b - a) * x / y * S2.card ≤ (b - a) * x / y * (Nat.primeCounting y : ℝ) :=
      mul_le_mul_of_nonneg_left hcardy_le (by positivity)
    have h2 : (b - a) * x / y * (Nat.primeCounting y : ℝ)
        = (b - a) * x * ((Nat.primeCounting y : ℝ) / y) := by ring
    have h3 : (b - a) * x * ((Nat.primeCounting y : ℝ) / y) ≤ (b - a) * x * κ :=
      mul_le_mul_of_nonneg_left hπy_div (by positivity)
    have h4 : (b - a) * x * κ = δ / 4 * x := by rw [hκdef]; field_simp
    linarith only [h1, h2.le, h2.symm.le, h3, h4.le, h4.symm.le]
  -- 2 π(B) ≤ (δ/4) x
  have hlogB_ge : Real.log b - Real.log 2 + Real.log x ≤ Real.log (⌊b * x⌋₊:ℝ) := by
    have h1 : Real.log (b * x / 2) ≤ Real.log (⌊b * x⌋₊:ℝ) := Real.log_le_log (by positivity) hBge
    have h2 : Real.log (b * x / 2) = Real.log b - Real.log 2 + Real.log x := by
      rw [Real.log_div (by positivity) (two_ne_zero), Real.log_mul hb0.ne' hxpos.ne']
      ring
    linarith only [h1, h2.le, h2.symm.le]
  have hlogB_ge6 : 8 * C' * b / δ ≤ Real.log (⌊b * x⌋₊:ℝ) := by
    have hM6x : M6 ≤ Real.log x := le_trans hM6M hlogx
    rw [hM6def] at hM6x
    linarith only [hM6x, hlogB_ge]
  have hlogBpos : 0 < Real.log (⌊b * x⌋₊:ℝ) := Real.log_pos hB2R
  have hratio2 : 2 * C' * b / Real.log (⌊b * x⌋₊:ℝ) ≤ δ / 4 := by
    rw [div_le_iff₀ hlogBpos]
    have hm := mul_le_mul_of_nonneg_right hlogB_ge6 (by positivity : (0:ℝ) ≤ δ / 4)
    have e : 8 * C' * b / δ * (δ / 4) = 2 * C' * b := by field_simp; ring
    linarith only [hm, e.le, e.symm.le]
  have hπB_le : (Nat.primeCounting ⌊b * x⌋₊ : ℝ) ≤ C' * ⌊b * x⌋₊ / Real.log ⌊b * x⌋₊ :=
    hC2 _ hB2nat
  have hterm_C : 2 * (Nat.primeCounting ⌊b * x⌋₊ : ℝ) ≤ δ / 4 * x := by
    have h1 : 2 * (Nat.primeCounting ⌊b * x⌋₊ : ℝ) ≤ 2 * (C' * ⌊b * x⌋₊ / Real.log ⌊b * x⌋₊) :=
      mul_le_mul_of_nonneg_left hπB_le (by norm_num)
    have h2 : 2 * (C' * (⌊b * x⌋₊:ℝ) / Real.log ⌊b * x⌋₊) ≤ 2 * (C' * (b * x) / Real.log ⌊b * x⌋₊) := by
      gcongr
    have h3 : 2 * (C' * (b * x) / Real.log (⌊b * x⌋₊:ℝ)) = (2 * C' * b / Real.log (⌊b * x⌋₊:ℝ)) * x := by
      ring
    have h4 : (2 * C' * b / Real.log (⌊b * x⌋₊:ℝ)) * x ≤ (δ / 4) * x :=
      mul_le_mul_of_nonneg_right hratio2 hxpos.le
    linarith only [h1, h2, h3.le, h3.symm.le, h4]
  -- 2 π(y) ≤ (δ/4) x
  have eq7a : θ / 2 * M7a = 1 := by rw [hM7adef]; field_simp
  have step_a7a : θ / 2 * M7a ≤ (θ - η) * Real.log x :=
    le_trans (mul_le_mul_of_nonneg_left hM7aM (by positivity)) hbig1
  have hlogy_ge1 : 1 ≤ Real.log y := by
    rw [← eq7a]; linarith only [step_a7a, hlogy_ge]
  have eq7b : (1 - θ) / 2 * M7b = max (Real.log (8 * C' / δ)) 0 := by rw [hM7bdef]; field_simp
  have step_a7b : (1 - θ) / 2 * M7b ≤ (1 - θ - η) * Real.log x :=
    le_trans (mul_le_mul_of_nonneg_left hM7bM (by positivity)) hbig2
  have hlog8Cδ_le : Real.log (8 * C' / δ) ≤ (1 - θ - η) * Real.log x := by
    have hmx := le_max_left (Real.log (8 * C' / δ)) 0
    linarith only [step_a7b, eq7b.le, eq7b.symm.le, hmx]
  have hxpow78_le : x ^ (θ + η - 1) ≤ δ / (8 * C') := by
    have hb2pos : (0:ℝ) < δ / (8 * C') := by positivity
    have hxpowpos : (0:ℝ) < x ^ (θ + η - 1) := Real.rpow_pos_of_pos hxpos _
    rw [← Real.log_le_log_iff hxpowpos hb2pos, Real.log_rpow hxpos]
    have hlogeq : Real.log (δ / (8 * C')) = -Real.log (8 * C' / δ) := by
      rw [show δ / (8 * C') = (8 * C' / δ)⁻¹ by field_simp, Real.log_inv]
    rw [hlogeq]
    linarith only [hlog8Cδ_le]
  have hπy_le2 : (Nat.primeCounting y : ℝ) ≤ C' * y := by
    have h2 : C' * (y:ℝ) / Real.log y ≤ C' * y := by
      rw [div_le_iff₀ hlogypos]
      have hnn : (0:ℝ) ≤ C' * y := by positivity
      have := mul_le_mul_of_nonneg_left hlogy_ge1 hnn
      linarith only [this]
    linarith only [hπy_le, h2]
  have hxpow_eq2 : x ^ (θ + η - 1) * x = x ^ (θ + η) := by
    rw [hxpow_eq]; field_simp
  have hy_le_pow : (y:ℝ) ≤ x ^ (θ + η - 1) * x := by rw [hxpow_eq2]; exact hy2
  have hπy_le3 : (Nat.primeCounting y : ℝ) ≤ C' * (x ^ (θ + η - 1) * x) := by
    have := mul_le_mul_of_nonneg_left hy_le_pow hC'pos.le
    linarith only [hπy_le2, this]
  have hπy_le4 : (Nat.primeCounting y : ℝ) ≤ δ / (8 * C') * C' * x := by
    have hmono : x ^ (θ + η - 1) * x ≤ δ / (8 * C') * x :=
      mul_le_mul_of_nonneg_right hxpow78_le hxpos.le
    have h1 : C' * (x ^ (θ + η - 1) * x) ≤ C' * (δ / (8 * C') * x) :=
      mul_le_mul_of_nonneg_left hmono hC'pos.le
    have e : C' * (δ / (8 * C') * x) = δ / (8 * C') * C' * x := by ring
    linarith only [hπy_le3, h1, e.le, e.symm.le]
  have heq_final : δ / (8 * C') * C' = δ / 8 := by field_simp
  have hπy_le5 : (Nat.primeCounting y : ℝ) ≤ δ / 8 * x := by
    rw [heq_final] at hπy_le4; exact hπy_le4
  have hterm_D : 2 * (Nat.primeCounting y : ℝ) ≤ δ / 4 * x := by linarith only [hπy_le5]
  -- final assembly
  have hcard0 := notSmooth_card_le y a b x hax hAB
  rw [← hS1def, ← hS2def] at hcard0
  have hS1_le_piB : (S1.card:ℝ) ≤ (Nat.primeCounting ⌊b * x⌋₊ : ℝ) := by
    rw [hS1def]; exact_mod_cast hcardB
  have h2S1 : 2 * (S1.card:ℝ) ≤ δ / 4 * x := by linarith only [hS1_le_piB, hterm_C]
  have h2S2 : 2 * (S2.card:ℝ) ≤ δ / 4 * x := by linarith only [hcardy_le, hterm_D]
  have hbaxT1 : (b - a) * x * (∑ p ∈ S1, (1:ℝ) / p) ≤ (b - a) * x * (Real.log (1 / θ) + κ) :=
    mul_le_mul_of_nonneg_left hT1 (by positivity)
  have hbaκ : (b - a) * κ = δ / 4 := by rw [hκdef]; field_simp
  have hfinal_eq : (b - a) * x * (Real.log (1 / θ) + κ) = (b - a) * Real.log (1 / θ) * x + δ / 4 * x := by
    rw [show (b - a) * x * (Real.log (1 / θ) + κ) = (b - a) * Real.log (1 / θ) * x + (b - a) * κ * x from by ring,
      hbaκ]
  have htarget_eq : ((b - a) * Real.log (1 / θ) + δ) * x
      = (b - a) * Real.log (1 / θ) * x + δ / 4 * x + δ / 4 * x + δ / 4 * x + δ / 4 * x := by ring
  rw [htarget_eq]
  linarith only [hcard0, hSum1, hSum2, hbaxT1, h2S1, hterm_B, h2S2, hfinal_eq]

end Erdos289
