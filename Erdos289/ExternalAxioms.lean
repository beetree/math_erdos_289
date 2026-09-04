import Mathlib

/-!
Six external axiom specifications for Erdős Problem 289 (4 September 2026).

This file defines six propositions and explicitly assumes them as axioms in the
`Assumed` namespace. They are external mathematical assumptions, not proofs.
The file has NOT been compiled in the authoring environment (Lean/Lake absent).
Intended baseline: Lean 4.19.0 and mathlib v4.19.0. Read the matching six
faithfulness statements with these exact helper definitions. No final theorem
about Erdos 289 is asserted here.

The GAP input deliberately uses source-native base-two logarithms and fixed
real-coordinate dilation. Do not silently substitute natural logs or sumsets.
-/

open scoped BigOperators

namespace Erdos289.External

noncomputable section

/-- Exact reciprocal mass in the rational numbers. The external density theorem
below only applies to sets of strictly positive natural numbers. -/
def rationalMass (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, (1 : ℚ) / (d : ℚ)

/-- The additive character `exp(2πi * z.val / U)`. Applications below require
`U ≥ 1`, so `z.val` is the canonical representative in `[0,U)`. -/
def expPhase (U : ℕ) (z : ZMod U) : ℂ :=
  Complex.exp
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (z.val : ℂ) / (U : ℂ))

/-- An incomplete inverse sum over precisely the integers `1 ≤ n ≤ N` that
are coprime to the modulus. Inversion occurs in `ZMod U`. -/
def inversePrefix (U N : ℕ) (a : ZMod U) : ℂ := by
  classical
  exact ∑ n ∈ ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n U)),
    expPhase U (a * (n : ZMod U)⁻¹)

/-- A sequence's unnormalized Fourier sum at the natural frequency `h`. -/
def fourierSum {U N : ℕ} (x : Fin N → ZMod U) (h : ℕ) : ℂ :=
  ∑ j : Fin N, expPhase U ((h : ZMod U) * x j)

/-- Number of sequence entries whose canonical residue lies in the half-open
interval `[α, α + ℓ)`. Multiplicities in the sequence are counted. -/
def residueIntervalCount {U N : ℕ} (x : Fin N → ZMod U)
    (α ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin N =>
    α ≤ (x j).val ∧ (x j).val < α + ℓ)).card

/-- Sum of reciprocals of primes at most the real number `x`. For `x ≥ 0`,
the upper cutoff is exactly `floor x`; negative inputs are irrelevant to the
limit at positive infinity. -/
def primeReciprocalSum (x : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime),
    (1 : ℝ) / (p : ℝ)

/-- Number of positive divisors when `n > 0`. Mathlib sets `Nat.divisors 0`
to the empty finset; the theorem below explicitly avoids this convention. -/
def divisorCount (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- Liu–Sawhney, Theorem 1.3, in its eventual finite-set threshold form.
The threshold `N₀` depends on `ζ` and is uniform over all subsequent sets `A`. -/
def LiuSawhneyStatement : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < (1 : ℝ) / 2 →
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
          (1 - Real.exp (-1) + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
          ∃ D : Finset ℕ, D ⊆ A ∧ rationalMass D = 1

/-- Bourgain–Garaev, Theorem 5: only its uniform `o(N)` consequence is
asserted. `m₀` is chosen before `m`, `N`, and `a`; it can depend only on the
fixed exponent `c` and error tolerance `ε`. All real powers are real powers. -/
def BourgainGaraevStatement : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ε : ℝ, 0 < ε →
        ∃ m₀ : ℕ, 2 ≤ m₀ ∧
          ∀ m : ℕ, m₀ ≤ m →
            ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → N < m →
              ∀ a : ZMod m, IsUnit a →
                ‖inversePrefix m N a‖ ≤ ε * (N : ℝ)

/-- The Erdős–Turán inequality specialized to a sequence in `ZMod U` and a
non-wrapping half-open residue interval. There is one absolute positive
constant. The frequency range is exactly `1 ≤ h ≤ H`, and all divisions
and the discrepancy subtraction take place in the real numbers. -/
def ErdosTuranStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ U : ℕ, 1 ≤ U →
      ∀ N : ℕ, ∀ x : Fin N → ZMod U,
        ∀ H : ℕ, 1 ≤ H →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |(residueIntervalCount x α ℓ : ℝ) -
                (N : ℝ) * (ℓ : ℝ) / (U : ℝ)| ≤
              C * ((N : ℝ) / (H : ℝ) +
                (∑ h ∈ Finset.Icc 1 H,
                  (1 : ℝ) / (h : ℝ) * ‖fourierSum x h‖))

/-- Mertens' second theorem. The sum includes precisely the natural primes
`p ≤ x`, both logarithms are natural, and `x` tends to positive infinity. -/
def MertensSecondStatement : Prop :=
  ∃ B₁ : ℝ,
    Filter.Tendsto
      (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      Filter.atTop (nhds B₁)

/-- The coefficient-one eventual divisor estimate. For each positive real
exponent a threshold is chosen uniformly for all larger positive integers. -/
def DivisorBoundStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → (divisorCount n : ℝ) ≤ (n : ℝ) ^ ε


/-- Source-native logarithm convention for the CFP structural theorem only.
Every other logarithm in this file is the natural logarithm. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- A fixed homogeneous coordinate representation. Bounds are real, coordinates
and generators are integral, and the dimension is finite. No symmetry or choice
of a new representation is built into this data type. -/
structure GAPRepresentation where
  rank : ℕ
  step : Fin rank → ℤ
  lower : Fin rank → ℝ
  upper : Fin rank → ℝ

namespace GAPRepresentation

/-- Evaluation has no affine offset; an allowed translate appears separately
in the subset-sum conclusion of the structural input. -/
def eval (P : GAPRepresentation) (v : Fin P.rank → ℤ) : ℤ :=
  ∑ i, v i * P.step i

/-- Coordinate dilation, uniformly for every positive real scale. The axioms
below use only positive scales. Integer hulls are imposed by `v i : ℤ`. -/
def coordinateBox (P : GAPRepresentation) (t : ℝ) :
    Set (Fin P.rank → ℤ) :=
  {v | ∀ i, t * P.lower i ≤ (v i : ℝ) ∧
    (v i : ℝ) ≤ t * P.upper i}

def carrierAt (P : GAPRepresentation) (t : ℝ) : Set ℤ :=
  P.eval '' P.coordinateBox t

/-- Properness here includes nonemptiness, so an empty dilate cannot satisfy
this predicate vacuously. The source correspondence separately justifies this
nonemptiness using the supplied centered construction. -/
def properAt (P : GAPRepresentation) (t : ℝ) : Prop :=
  (P.coordinateBox t).Nonempty ∧ Set.InjOn P.eval (P.coordinateBox t)

end GAPRepresentation

/-- Sums of genuine finite subsets, including the empty subset. Repetition of
an element is not allowed. -/
def integerSubsetSums (A : Finset ℤ) : Set ℤ :=
  {z | ∃ B : Finset ℤ, B ⊆ A ∧ (∑ b ∈ B, b) = z}

/-- CFP Theorem 1.5, as restated in CFHMPSV Theorem 3, with integer `s`, a
harmless large-size threshold, source-native log2, and the same fixed coordinate
representation at scales 1 and c*s. The translating integer's extra homogeneity
condition is omitted; allowing rank zero and non-strict bounds also weakens the
source's representation requirements. -/
def CFHMPSVStructureStatement : Prop :=
  ∀ β η : ℝ, 1 < β → 0 < η → η < 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (m n s : ℕ) (A : Finset ℤ),
        m₀ ≤ m →
        A ⊆ Finset.Icc (1 : ℤ) (n : ℤ) →
        A.card = m →
        (n : ℝ) ≤ (m : ℝ) ^ β →
        (m : ℝ) ^ η ≤ (s : ℝ) →
        (s : ℝ) ≤ c * (m : ℝ) / logTwo (m : ℝ) →
        ∃ (J : Finset ℤ) (P : GAPRepresentation) (J' : Finset ℤ),
          J ⊆ A ∧
          (m : ℝ) - (s : ℝ) * logTwo (m : ℝ) / c ≤ (J.card : ℝ) ∧
          P.rank ≤ d₀ ∧
          P.properAt 1 ∧
          ((J : Set ℤ) ∪ {0}) ⊆ P.carrierAt 1 ∧
          J' ⊆ J ∧ J'.card ≤ s ∧
          P.properAt (c * (s : ℝ)) ∧
          ∃ z : ℤ, ∀ x ∈ P.carrierAt (c * (s : ℝ)),
            z + x ∈ integerSubsetSums J'

/-- An explicit collection of hypotheses for a future conditional proof.
Defining this structure does not prove that an instance exists. -/
structure ExternalInputs : Prop where
  liu_sawhney : LiuSawhneyStatement
  cfhmpsv_structure : CFHMPSVStructureStatement
  bourgain_garaev : BourgainGaraevStatement
  erdos_turan : ErdosTuranStatement
  mertens_second : MertensSecondStatement
  divisor_bound : DivisorBoundStatement

namespace Assumed

/-- ASSUMED: Liu–Sawhney, arXiv:2404.07113v1, Theorem 1.3. -/
axiom liu_sawhney : LiuSawhneyStatement

/-- ASSUMED: CFP arXiv:2311.01416v1 Theorem 1.5 with its fixed-coordinate
conventions; CFHMPSV arXiv:2404.16016v2 Theorem 3 is the cross-reference. -/
axiom cfhmpsv_structure : CFHMPSVStructureStatement

/-- ASSUMED: Bourgain–Garaev, arXiv:1309.1124v1, Theorem 5,
only the uniform small-exponent o(N) consequence. -/
axiom bourgain_garaev : BourgainGaraevStatement

/-- ASSUMED: classical Erdős–Turán discrepancy inequality, specialized
from the unit circle to canonical residues. -/
axiom erdos_turan : ErdosTuranStatement

/-- ASSUMED: the convergent form of Mertens' second theorem. -/
axiom mertens_second : MertensSecondStatement

/-- ASSUMED: the eventual subpolynomial divisor bound;
Hardy–Wright, Theorem 315, implies this coefficient-one form. -/
axiom divisor_bound : DivisorBoundStatement

/-- Packages exactly the six external assumptions. This is not a proof of
Erdos 289; a future main theorem must prove the implication from these inputs. -/
def inputs : ExternalInputs where
  liu_sawhney := liu_sawhney
  cfhmpsv_structure := cfhmpsv_structure
  bourgain_garaev := bourgain_garaev
  erdos_turan := erdos_turan
  mertens_second := mertens_second
  divisor_bound := divisor_bound

end Assumed

end

end Erdos289.External
