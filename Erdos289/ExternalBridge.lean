import Erdos289.External
import Erdos289.ErdosTuran
import Erdos289.ExternalAxioms

/-!
# Bridging the author's audited external axioms to our statements

This file proves our six external axioms (`Erdos289.liu_sawhney`, `Erdos289.cfhmpsv_structure`,
`Erdos289.bourgain_garaev`, `Erdos289.erdos_turan`, `Erdos289.mertens_second`,
`Erdos289.divisor_bound`) as theorems from the author's independently-audited axiom module
`Erdos289.External.Assumed`, so that `#print axioms` on downstream results shows only the
audited `Erdos289.External.Assumed.*` axioms.
-/

namespace Erdos289

open Filter Finset
open scoped BigOperators

theorem bridge_liu_sawhney (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      (1 - 1 / Real.exp 1 + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ D ⊆ A, ∑ d ∈ D, (1 : ℚ) / d = 1 := by
  obtain ⟨N₀, hN₀, h⟩ := Erdos289.External.Assumed.liu_sawhney ζ hζ0 hζ1
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun N hN A hA hcard => ?_⟩
  have hcard' : (1 - Real.exp (-1) + ζ) * (N : ℝ) ≤ (A.card : ℝ) := by
    simpa [Real.exp_neg, one_div] using hcard
  exact h N hN A hA hcard'

theorem bridge_mertens_second :
    ∃ B₁ : ℝ, Tendsto
      (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x)) atTop (nhds B₁) := by
  obtain ⟨B₁, hB₁⟩ := Erdos289.External.Assumed.mertens_second
  refine ⟨B₁, ?_⟩
  have hcomp := hB₁.comp tendsto_natCast_atTop_atTop
  have heq : (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x))
      = (fun x : ℝ => Erdos289.External.primeReciprocalSum x - Real.log (Real.log x)) ∘
        (Nat.cast : ℕ → ℝ) := by
    funext n
    simp only [Function.comp_apply, Erdos289.External.primeReciprocalSum, Nat.floor_natCast]
  rw [heq]
  exact hcomp

theorem bridge_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨n₀, hn₀, h⟩ := Erdos289.External.Assumed.divisor_bound ε hε
  rw [Filter.eventually_atTop]
  exact ⟨n₀, fun n hn => h n hn⟩

/-! ## Shared periodicity lemma for the Erdős–Turán and Bourgain–Garaev bridges.

Both `expPhase U w` (the author's character, using the canonical `ZMod U` representative) and
`e U n` (our character, using an arbitrary integer representative) are `Complex.exp` of
`2πi * (representative) / U`; they agree whenever the two integer representatives are congruent
mod `U`, by periodicity of `Complex.exp` at multiples of `2πi`. -/

private theorem exp_div_U_eq (U : ℕ) (hU : 0 < U) (a b : ℤ) (h : a ≡ b [ZMOD (U : ℤ)]) :
    Complex.exp (2 * Real.pi * Complex.I * a / U) = Complex.exp (2 * Real.pi * Complex.I * b / U) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  have hb : (b : ℂ) = (a : ℂ) + (U : ℂ) * (k : ℂ) := by
    have hb' : (b : ℤ) = a + U * k := by linarith [hk]
    exact_mod_cast hb'
  have hUne : (U : ℂ) ≠ 0 := by exact_mod_cast hU.ne'
  rw [hb]
  rw [show (2 : ℂ) * Real.pi * Complex.I * (a + U * k) / U
      = 2 * Real.pi * Complex.I * a / U + (k : ℂ) * (2 * Real.pi * Complex.I) by field_simp]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The author's `expPhase U ((h : ZMod U) * z)` and our `e U (h * z.val)` compute the same
value, since `((h : ZMod U) * z).val ≡ h * z.val (mod U)`. -/
private theorem expPhase_eq_e {U : ℕ} (hU : 0 < U) (h : ℕ) (z : ZMod U) :
    Erdos289.External.expPhase U ((h : ZMod U) * z) = Erdos289.e U ((h : ℤ) * (z.val : ℤ)) := by
  have : NeZero U := ⟨hU.ne'⟩
  have hval : (((h : ZMod U) * z).val) ≡ (h * z.val) [MOD U] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_rightInverse ((h : ZMod U) * z)]
    push_cast
    rw [ZMod.natCast_rightInverse z]
  have hvalZ : ((((h : ZMod U) * z).val : ℤ)) ≡ ((h : ℤ) * (z.val : ℤ)) [ZMOD (U : ℤ)] := by
    have hz := Int.natCast_modEq_iff.mpr hval
    push_cast at hz
    exact hz
  unfold Erdos289.External.expPhase Erdos289.e
  push_cast
  convert exp_div_U_eq U hU (((h : ZMod U) * z).val : ℤ) ((h : ℤ) * (z.val : ℤ)) hvalZ using 2 <;>
    push_cast <;> ring

theorem bridge_erdos_turan :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ), 0 < U → ∀ (N : ℕ) (x : Fin N → ZMod U) (H : ℕ), 0 < H →
      ∀ α ℓ : ℕ, α + ℓ ≤ U →
        |((univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card : ℝ)
              - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
          ≤ C * ((N : ℝ) / (H : ℝ)
              + ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
                  ‖∑ j, e U (h * ((x j).val : ℤ))‖) := by
  obtain ⟨C, hC, h⟩ := Erdos289.External.Assumed.erdos_turan
  refine ⟨C, hC, fun U hU N x H hH α ℓ hαℓ => ?_⟩
  have h1U : 1 ≤ U := hU
  have h1H : 1 ≤ H := hH
  have hres : Erdos289.External.residueIntervalCount x α ℓ
      = (univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card := by
    unfold Erdos289.External.residueIntervalCount
    congr 1
    apply Finset.filter_congr
    intro j _
    rw [Finset.mem_Ico]
  have hfour : ∀ hh : ℕ, Erdos289.External.fourierSum x hh = ∑ j, e U (hh * ((x j).val : ℤ)) := by
    intro hh
    unfold Erdos289.External.fourierSum
    apply Finset.sum_congr rfl
    intro j _
    exact expPhase_eq_e hU hh (x j)
  have hkey := h U h1U N x H h1H α ℓ hαℓ
  rw [hres] at hkey
  simp only [hfour] at hkey
  exact hkey

theorem bridge_bourgain_garaev :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → (N : ℝ) < (m : ℝ) →
        ∀ a : ℕ, Nat.Coprime a m →
          ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
              e m (a * ((n : ZMod m)⁻¹).val)‖ ≤ ε * (N : ℝ) := by
  obtain ⟨c₀, hc₀, h⟩ := Erdos289.External.Assumed.bourgain_garaev
  refine ⟨c₀, hc₀, fun c hc hcc₀ ε hε => ?_⟩
  obtain ⟨m₀, hm₀, hmm⟩ := h c hc hcc₀ ε hε
  rw [Filter.eventually_atTop]
  refine ⟨m₀, fun m hm N hN1 hN2 a ha => ?_⟩
  have hmU : 0 < m := by omega
  have hunit : IsUnit ((a : ZMod m)) := (ZMod.isUnit_iff_coprime a m).mpr ha
  have hN2' : N < m := by exact_mod_cast hN2
  have hkey := hmm m hm N hN1 hN2' (a : ZMod m) hunit
  unfold Erdos289.External.inversePrefix at hkey
  have heq : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
      Erdos289.External.expPhase m ((a : ZMod m) * (n : ZMod m)⁻¹)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n m),
        e m (a * ((n : ZMod m)⁻¹).val) := by
    apply Finset.sum_congr rfl
    intro n _
    exact expPhase_eq_e hmU a ((n : ZMod m)⁻¹)
  rw [heq] at hkey
  exact hkey

/-! ## The CFHMPSV structure bridge.

`Erdos289.External.Assumed.cfhmpsv_structure` and `Erdos289.cfhmpsv_structure` package the same
mathematical content (Conlon–Fox–Pham Theorem 1.5 / CFHMPSV Theorem 3) with two conventions that
must be reconciled:

* the size threshold `s` is compared against `c * m / logTwo m` (author) versus `c * m / log m`
  (ours), where `logTwo x = log x / log 2`; setting our reported constant to `c * log 2` makes
  these two bounds (and the two matching cardinality-loss bounds `s * logTwo m / c` versus
  `s * log m / c⁻¹`) literally equal, since `log 2 > 0`;
* a `GAPRepresentation` (rank/step/lower/upper, real-valued coordinate dilation `coordinateBox`)
  translates directly into a `GAP` (`D`/`d`/`α`/`β`) with `carrierAt t = (dilate t P).set` and
  `properAt t` translating to `Proper` (+ nonemptiness) of the dilate at scale `t`, for every
  real `t`; integer finsets translate via `Int.toNat`/`Nat.cast` on the (necessarily nonnegative)
  elements of a subset of `[1, n]`.

Both translations above are complete and proved below (`toGAP`, `carrierAt_eq`, `properAt_iff`,
`toNat_injOn_nonneg`, and the arithmetic identities for the threshold/cardinality bounds).

However, reconciling the *dilation scale* itself runs into a genuine mismatch that these
translations cannot paper over. Our target's conclusion must hold at the dilate scale `c' * s`
for our reported constant `c' = c * log 2`; the author's theorem, instantiated at that same
natural number `s`, only certifies properness/nonemptiness/subset-sums at the dilate scale
`c * s` (the author's own `c`, with no `log 2` factor: the `log 2` only enters the *threshold*
inequality on `s`, not the dilation argument). Since `log 2 ≠ 1`, `c' * s = c * log 2 * s ≠ c * s`
for `s > 0`, so these are honestly different real dilation scales.

There is no freedom left to fix this: the base-case scale (`properAt 1` / `P.Proper`) forces any
GAP we return to literally be `toGAP P` (undilated) rather than some rescaling of it (else the
`J ⊆ P.set` and `0 ∈ P.set` facts, only known at the author's scale `1`, would not transfer), and
having fixed that, matching the dilation scale forces `c' = c` on the nose, while matching the
threshold range on `s` forces `c' = c * log 2` on the nose — both cannot hold since `log 2 ≠ 1`.
(Salvaging this would need extra structure not present in the `Prop`-level axiom statement, e.g.
that properness/nonemptiness at scale `c * s` propagates down to every smaller scale in `(0, c*s]`
— true if every coordinate's bounds straddle the origin, `lower i ≤ 0 ≤ upper i`, which is
plausible for the actual CFP/CFHMPSV construction but is not implied by `properAt`/`carrierAt`
alone: `0 ∈ carrierAt 1` only asserts *some* coordinate vector evaluates to `0`, not that the
all-zero vector is admissible coordinatewise.)

The three fields below that depend on the dilation scale are therefore left as `sorry`; every
other field (`J ⊆ A`, `P.Proper`, `P.D ≤ d₀`, `J' ⊆ J`, the cardinality bound, `J ⊆ P.set`,
`0 ∈ P.set`, `J'.card ≤ s`) is proved in full from the author's axiom. -/

private theorem toNat_injOn_nonneg {S : Finset ℤ} (hS : ∀ x ∈ S, 0 ≤ x) :
    Set.InjOn Int.toNat (S : Set ℤ) := by
  intro x hx y hy hxy
  have hx0 := hS x hx
  have hy0 := hS y hy
  have := congrArg (fun n : ℕ => (n : ℤ)) hxy
  simpa [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] using this

/-- Converts an author's `GAPRepresentation` (rank/step/lower/upper) into our `GAP`
(`D`/`d`/`α`/`β`); the underlying coordinate data is identical. -/
private def toGAP (P : Erdos289.External.GAPRepresentation) : Erdos289.GAP where
  D := P.rank
  d := P.step
  α := P.lower
  β := P.upper

/-- The author's `carrierAt t` and our `(dilate t ·).set` agree, for every real `t`, since both
unfold to "images under `eval`/`∑ n i * d i` of the coordinate box `[t * lower, t * upper]`". -/
private theorem carrierAt_eq (P : Erdos289.External.GAPRepresentation) (t : ℝ) :
    P.carrierAt t = (Erdos289.GAP.dilate t (toGAP P)).set := by
  unfold Erdos289.External.GAPRepresentation.carrierAt Erdos289.External.GAPRepresentation.eval
    Erdos289.External.GAPRepresentation.coordinateBox Erdos289.GAP.dilate Erdos289.GAP.set toGAP
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩

private theorem dilate_one (P : Erdos289.GAP) : Erdos289.GAP.dilate 1 P = P := by
  simp [Erdos289.GAP.dilate]

/-- The author's `properAt t` (nonemptiness of the coordinate box, plus injectivity of `eval` on
it) matches nonemptiness plus `Proper` of our dilate at the same scale `t`. -/
private theorem properAt_iff (P : Erdos289.External.GAPRepresentation) (t : ℝ) :
    P.properAt t ↔ (P.coordinateBox t).Nonempty ∧ (Erdos289.GAP.dilate t (toGAP P)).Proper := by
  unfold Erdos289.External.GAPRepresentation.properAt Erdos289.GAP.Proper
    Erdos289.External.GAPRepresentation.coordinateBox Erdos289.External.GAPRepresentation.eval
    Erdos289.GAP.dilate toGAP
  constructor
  · rintro ⟨hne, hinj⟩; exact ⟨hne, fun n m hn hm heq => hinj hn hm heq⟩
  · rintro ⟨hne, hinj⟩; exact ⟨hne, fun n hn m hm heq => hinj n m hn hm heq⟩

theorem bridge_cfhmpsv_structure (β : ℝ) (hβ : 1 < β) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) ^ β →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = m →
        ∀ s : ℕ, (m : ℝ) ^ η ≤ (s : ℝ) → (s : ℝ) ≤ c * (m : ℝ) / Real.log m →
          ∃ (J : Finset ℕ) (P : GAP) (J' : Finset ℕ),
            J ⊆ A ∧ P.Proper ∧ (GAP.dilate (c * (s : ℝ)) P).Proper ∧
            (GAP.dilate (c * (s : ℝ)) P).set.Nonempty ∧ P.D ≤ d₀ ∧ J' ⊆ J ∧
            (m : ℝ) - c⁻¹ * s * Real.log m ≤ (J.card : ℝ) ∧
            (∀ x ∈ J, (x : ℤ) ∈ P.set) ∧ (0 : ℤ) ∈ P.set ∧
            J'.card ≤ s ∧
            ∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (s : ℝ)) P).set, x + y ∈ subsetSums J' := by
  obtain ⟨c, hc, d₀, m₀, hm₀, h⟩ := Erdos289.External.Assumed.cfhmpsv_structure β η hβ hη0 hη1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c * Real.log 2, by positivity, d₀, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨m₀, fun m hm n hn A hAsub hAcard s hsη hsc => ?_⟩
  have hm2 : 2 ≤ m := le_trans hm₀ hm
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hlogm : (0 : ℝ) < Real.log m := Real.log_pos hm1
  have hcast_inj : Function.Injective (Nat.cast : ℕ → ℤ) := fun a b hab => by exact_mod_cast hab
  set A' : Finset ℤ := A.image (Nat.cast : ℕ → ℤ) with hA'def
  have hA'card : A'.card = A.card := Finset.card_image_of_injective A hcast_inj
  have hA'sub : A' ⊆ Finset.Icc (1 : ℤ) (n : ℤ) := by
    intro x hx
    simp only [hA'def, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have := hAsub ha
    rw [Finset.mem_Icc] at this ⊢
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hA'nn : ∀ x ∈ A', 0 ≤ x := by
    intro x hx
    simp only [hA'def, Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    positivity
  have hlogTwo : Erdos289.External.logTwo (m : ℝ) = Real.log m / Real.log 2 := rfl
  have hs_hi : (s : ℝ) ≤ c * (m : ℝ) / Erdos289.External.logTwo (m : ℝ) := by
    rw [hlogTwo, show c * (m : ℝ) / (Real.log m / Real.log 2)
        = c * Real.log 2 * (m : ℝ) / Real.log m by field_simp]
    exact hsc
  obtain ⟨J, P, J', hJA', hcardJ, hrankP, hproper1, hunion, hJ'J, hJ'card, hproperCS, z, hz⟩ :=
    h m n s A' hm hA'sub (hA'card.trans hAcard) hn hsη hs_hi
  have hJnn : ∀ x ∈ J, 0 ≤ x := fun x hx => hA'nn x (hJA' hx)
  have hJ'nn : ∀ x ∈ J', 0 ≤ x := fun x hx => hJnn x (hJ'J hx)
  set Jℕ : Finset ℕ := J.image Int.toNat with hJndef
  set J'ℕ : Finset ℕ := J'.image Int.toNat with hJ'ndef
  have hJcard : Jℕ.card = J.card := Finset.card_image_of_injOn (toNat_injOn_nonneg hJnn)
  have hJ'card' : J'ℕ.card = J'.card := Finset.card_image_of_injOn (toNat_injOn_nonneg hJ'nn)
  have hJℕA : Jℕ ⊆ A := by
    intro x hx
    simp only [hJndef, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjA' := hJA' hj
    simp only [hA'def, Finset.mem_image] at hjA'
    obtain ⟨a, ha, hae⟩ := hjA'
    rw [← hae, Int.toNat_natCast]
    exact ha
  have hJ'ℕJℕ : J'ℕ ⊆ Jℕ := Finset.image_subset_image hJ'J
  have hcardbound : (m : ℝ) - (c * Real.log 2)⁻¹ * (s : ℝ) * Real.log m ≤ (Jℕ.card : ℝ) := by
    rw [hJcard]
    have heq : (c * Real.log 2)⁻¹ * (s : ℝ) * Real.log m
        = (s : ℝ) * Erdos289.External.logTwo (m : ℝ) / c := by
      rw [hlogTwo]; field_simp
    rw [heq]; exact hcardJ
  have hProperOne : (toGAP P).Proper := by
    have := ((properAt_iff P 1).mp hproper1).2
    rwa [dilate_one] at this
  refine ⟨Jℕ, toGAP P, J'ℕ, hJℕA, hProperOne, ?_, ?_, hrankP, hJ'ℕJℕ, hcardbound, ?_, ?_,
      hJ'card'.trans_le hJ'card, ?_⟩
  · sorry -- Dilation-scale mismatch (`c * log 2 * s` needed, `c * s` known); see the module
          -- docstring above for why this cannot be closed from the `Prop`-level axiom alone.
  · sorry -- Same mismatch, for nonemptiness of the dilate.
  · intro x hx
    simp only [hJndef, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj1 : (j : ℤ) ∈ P.carrierAt 1 := hunion (Set.mem_union_left _ hj)
    rw [carrierAt_eq, dilate_one] at hj1
    rwa [Int.toNat_of_nonneg (hJnn j hj)]
  · have h01 : (0 : ℤ) ∈ P.carrierAt 1 := hunion (Set.mem_union_right _ rfl)
    rwa [carrierAt_eq, dilate_one] at h01
  · sorry -- Same mismatch: the subset-sum conclusion is stated for the dilate at scale `c*log2*s`.

#print axioms bridge_liu_sawhney
#print axioms bridge_mertens_second
#print axioms bridge_divisor_bound
#print axioms bridge_erdos_turan
#print axioms bridge_bourgain_garaev
#print axioms bridge_cfhmpsv_structure

end Erdos289
