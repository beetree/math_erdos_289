import Erdos289.External
import Erdos289.ExternalAxioms
import SolveMath.Ported.DivisorBound
import SolveMath.Ported.MertensSecond
import SolveMath.Ported.LiuSawhney
import Erdos289.CFPBridge

/-!
# The literature inputs, supplied by proved (vendored) theorems

This file connects the working statements used by the construction
(`Erdos289.liu_sawhney`, `Erdos289.cfhmpsv_structure`, `Erdos289.mertens_second`,
`Erdos289.divisor_bound`) to their proofs:

* `liu_sawhney`, `mertens_second`, `divisor_bound` are aliases of the ported proofs
  `Erdos289.Ported.liu_sawhney`, `Erdos289.Ported.mertens_second`, `Erdos289.Ported.divisor_bound`
  (`SolveMath/Ported/*.lean`); the audited-form statements are `Erdos289.Ported.*_audited` in the
  same files.
* `cfhmpsv_structure` is `bridge_cfhmpsv_structure` below, proved from
  `Erdos289.Ported.cfhmpsv_structure_audited` (`Erdos289/CFPBridge.lean`, vendored CFP proof).

The declarations `bridge_liu_sawhney`, `bridge_mertens_second`, `bridge_divisor_bound` and
`bridge_bourgain_garaev` below are **historical**: they derive the same statements from the
archived axiom module `Erdos289.External.Assumed` (`Erdos289/ExternalAxioms.lean`). They are not
the active aliases and are not in the dependency chain of the terminal theorem
`Erdos289.candidateStatement`, whose axiom report is `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos289

open Filter Finset
open scoped BigOperators

/-! ## Historical bridges from the archived axiom module (not used by the terminal theorem) -/

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
mathematical content (Conlon–Fox–Pham Theorem 1.5 / CFHMPSV Theorem 3) with the *same* logarithm
convention (`Erdos289.External.logTwo`, base-two, in both the threshold `s ≤ c * m / logTwo m`
and the cardinality-loss bound `m - c⁻¹ * s * logTwo m ≤ |J|`) and hence the *same* reported
constant `c` and dilation scale `c * s` throughout, so the two conventions that must be
reconciled are purely about the data representation:

* a `GAPRepresentation` (rank/step/lower/upper, real-valued coordinate dilation `coordinateBox`)
  translates directly into a `GAP` (`D`/`d`/`α`/`β`) with `carrierAt t = (dilate t P).set` and
  `properAt t` translating to `Proper` (+ nonemptiness) of the dilate at scale `t`, for every
  real `t` (`toGAP`, `carrierAt_eq`, `properAt_iff`);
* integer finsets translate via `Int.toNat`/`Nat.cast` on the (necessarily nonnegative) elements
  of a subset of `[1, n]` (`toNat_injOn_nonneg`);
* the audited `integerSubsetSums` (sums of subsets of a `Finset ℤ`) translates to our
  `subsetSums` (sums of subsets of a `Finset ℕ`, cast to `ℤ`) along the same `Int.toNat`
  correspondence.

Since the dilation scale `c * s` and the threshold/cardinality bounds now agree on the nose (no
rescaling needed), every field of the conclusion transfers directly from the author's axiom;
nothing is left as `sorry`. -/

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
        ∀ s : ℕ, (m : ℝ) ^ η ≤ (s : ℝ) → (s : ℝ) ≤ c * (m : ℝ) / Erdos289.External.logTwo m →
          ∃ (J : Finset ℕ) (P : GAP) (J' : Finset ℕ),
            J ⊆ A ∧ P.Proper ∧ (GAP.dilate (c * (s : ℝ)) P).Proper ∧
            (GAP.dilate (c * (s : ℝ)) P).set.Nonempty ∧ P.D ≤ d₀ ∧ J' ⊆ J ∧
            (m : ℝ) - c⁻¹ * s * Erdos289.External.logTwo m ≤ (J.card : ℝ) ∧
            (∀ x ∈ J, (x : ℤ) ∈ P.set) ∧ (0 : ℤ) ∈ P.set ∧
            J'.card ≤ s ∧
            ∃ x : ℤ, ∀ y ∈ (GAP.dilate (c * (s : ℝ)) P).set, x + y ∈ subsetSums J' := by
  obtain ⟨c, hc, d₀, m₀, hm₀, h⟩ := Erdos289.Ported.cfhmpsv_structure_audited β η hβ hη0 hη1
  refine ⟨c, hc, d₀, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨m₀, fun m hm n hn A hAsub hAcard s hsη hsc => ?_⟩
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
  obtain ⟨J, P, J', hJA', hcardJ, hrankP, hproper1, hunion, hJ'J, hJ'card, hproperCS, z, hz⟩ :=
    h m n s A' hm hA'sub (hA'card.trans hAcard) hn hsη hsc
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
  have hcardbound : (m : ℝ) - c⁻¹ * (s : ℝ) * Erdos289.External.logTwo m ≤ (Jℕ.card : ℝ) := by
    rw [hJcard]
    have heq : c⁻¹ * (s : ℝ) * Erdos289.External.logTwo m
        = (s : ℝ) * Erdos289.External.logTwo (m : ℝ) / c := by ring
    rw [heq]; exact hcardJ
  have hProperOne : (toGAP P).Proper := by
    have := ((properAt_iff P 1).mp hproper1).2
    rwa [dilate_one] at this
  have hCSne : (P.coordinateBox (c * (s : ℝ))).Nonempty := hproperCS.1
  have hCSproper : (Erdos289.GAP.dilate (c * (s : ℝ)) (toGAP P)).Proper :=
    ((properAt_iff P (c * (s : ℝ))).mp hproperCS).2
  have hCSsetNonempty : (Erdos289.GAP.dilate (c * (s : ℝ)) (toGAP P)).set.Nonempty := by
    have : (P.carrierAt (c * (s : ℝ))).Nonempty := hCSne.image _
    rwa [carrierAt_eq] at this
  have hIntSubsetSums_sub : Erdos289.External.integerSubsetSums J' ⊆ subsetSums J'ℕ := by
    rintro x ⟨B, hBJ', rfl⟩
    refine ⟨B.image Int.toNat, Finset.image_subset_image hBJ', ?_⟩
    rw [Finset.sum_image
      (fun a ha b hb hab => toNat_injOn_nonneg (fun y hy => hJ'nn y (hBJ' hy)) ha hb hab)]
    exact Finset.sum_congr rfl (fun a ha => (Int.toNat_of_nonneg (hJ'nn a (hBJ' ha))).symm)
  refine ⟨Jℕ, toGAP P, J'ℕ, hJℕA, hProperOne, hCSproper, hCSsetNonempty, hrankP, hJ'ℕJℕ,
      hcardbound, ?_, ?_, hJ'card'.trans_le hJ'card, ?_⟩
  · intro x hx
    simp only [hJndef, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj1 : (j : ℤ) ∈ P.carrierAt 1 := hunion (Set.mem_union_left _ hj)
    rw [carrierAt_eq, dilate_one] at hj1
    rwa [Int.toNat_of_nonneg (hJnn j hj)]
  · have h01 : (0 : ℤ) ∈ P.carrierAt 1 := hunion (Set.mem_union_right _ rfl)
    rwa [carrierAt_eq, dilate_one] at h01
  · refine ⟨z, fun y hy => ?_⟩
    have hy' : y ∈ P.carrierAt (c * (s : ℝ)) := by rw [carrierAt_eq]; exact hy
    exact hIntSubsetSums_sub (hz y hy')


/-! ## The six input statements, now theorems derived from the audited axioms -/

/-- **Liu–Sawhney**, *On further questions regarding unit fractions*, Theorem 1.3.

For every fixed `0 < ζ < 1/2`, for all sufficiently large `N`, every subset `A` of
`[1, N]` with density at least `1 - 1/e + ζ` contains a subset `D` whose reciprocals sum
to exactly `1`.

Supplied by the ported proof `Erdos289.Ported.liu_sawhney` (`SolveMath/Ported/LiuSawhney.lean`);
the audited-form statement is `Erdos289.Ported.liu_sawhney_audited`. The historical
`bridge_liu_sawhney` above (from the archived axiom) is not the active alias. -/
alias liu_sawhney := Ported.liu_sawhney

/-- **Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte**, *A question of Erdős and Graham on
Egyptian fractions* (arXiv:2404.16016), Theorem 3, derived there from Conlon–Fox–Pham,
*Homogeneous structures in subset sums and non-averaging sets*, Theorem 1.5.

Fix `β > 1` and `0 < η < 1`. There are constants `c > 0` and `d₀ : ℕ` such that, for all
sufficiently large `m`, for every `n ≤ m ^ β`, every `A ⊆ [1, n]` with `|A| = m`, and
every integer `s` with `m ^ η ≤ s ≤ c m / log₂ m`, there are `J ⊆ A`, a proper GAP `P` of
rank at most `d₀`, and `J' ⊆ J` such that `|J| ≥ m - s log₂ m / c`, `J ∪ {0} ⊆ P`,
`|J'| ≤ s`, and the subset sums of `J'` contain a translate of the proper dilate `(c s) • P`.
The dilate `(c s) • P` is itself asserted to be proper and nonempty (the paper's phrases
"the proper dilate `csP`" and "the supplied proper GAP `csP` is nonempty"; both are needed
for the face count in the proof of Lemma 3). The logarithm here is the source-native base-two
`log₂ x = log x / log 2` (`Erdos289.External.logTwo`), matching the audited
`CFHMPSVStructureStatement` in `ExternalAxioms.lean` on the nose, so that the bridge in
`ExternalBridge.lean` can use the very same constant `c`.

Derived from the ported theorem `Erdos289.Ported.cfhmpsv_structure_audited` (Conlon–Fox–Pham, vendored in `ErdosProblems/`) via the bridge above. -/
alias cfhmpsv_structure := bridge_cfhmpsv_structure

/-- **Bourgain–Garaev**, *Kloosterman sums in residue rings*, Theorem 5.

For every sufficiently small fixed `c > 0`, the short Kloosterman-type sum
`∑_{n ≤ N, (n,m)=1} e_m(a n⁻¹)` is `o(N)` as the modulus `m → ∞`, uniformly in
`m^c < N < m` and in coefficients `a` coprime to `m`.

Historical: derived from the archived axiom `Erdos289.External.Assumed.bourgain_garaev` via the
bridge above. Not used by the terminal theorem (the signed-fiber construction replaces the
equidistribution argument). -/
alias bourgain_garaev := bridge_bourgain_garaev

/-- **Mertens' second theorem**: `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)` for a constant
`B₁`. Mathlib does not currently contain this asymptotic (checked: no lemma involving
`Mertens`, and `Nat.primeCounting`/Chebyshev files only give prime-counting bounds, not
the reciprocal-prime sum). Supplied by the ported proof `Erdos289.Ported.mertens_second`
(`SolveMath/Ported/MertensSecond.lean`); the audited-form statement is
`Erdos289.Ported.mertens_second_audited`. The historical `bridge_mertens_second` above is not the
active alias. -/
alias mertens_second := Ported.mertens_second

/-- The uniform divisor bound `τ(n) = n^{o(1)}`. Mathlib does not currently contain this
(checked: only the trivial bound `Nat.card_divisors_le_self : n.divisors.card ≤ n`, no
`n^ε`-type divisor bound). Supplied by the ported proof `Erdos289.Ported.divisor_bound`
(`SolveMath/Ported/DivisorBound.lean`); the audited-form statement is
`Erdos289.Ported.divisor_bound_audited`. The historical `bridge_divisor_bound` above is not the
active alias. -/
alias divisor_bound := Ported.divisor_bound

end Erdos289
