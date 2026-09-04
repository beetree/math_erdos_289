import Erdos289.Defs
import Erdos289.ExternalBridge
import Erdos289.Lemma5

/-!
# Signed correction fibers: shared definitions

Definitions for the elementary replacement of Lemma 1 (`docs/elementary_replacements.md`,
Sections 2–3). Correction pairs are `{q m, q m + σ}` with a sign `σ ∈ {-1, +1}`; the multiplier
range is `[q^ε / E(q), 8 q^ε]` where `E(q) = V(q)^2 log q` and `V(q)` is the divisor envelope
`max_{n ≤ ⌈25 q^{1+ε}⌉} τ(n)`.
-/

namespace Erdos289

open Finset

/-- The finite divisor envelope `V(q) = max_{1 ≤ n ≤ ⌈25 q^{1+ε}⌉} τ(n)` (display (F1)). -/
noncomputable def Venv (ε : ℝ) (q : ℕ) : ℕ :=
  (Icc 1 ⌈25 * (q : ℝ) ^ (1 + ε)⌉₊).sup (fun n => n.divisors.card)

/-- `E(q) = V(q)^2 log q` (display (F1)). -/
noncomputable def Eenv (ε : ℝ) (q : ℕ) : ℝ := (Venv ε q : ℝ) ^ 2 * Real.log q

/-- The lower multiplier bound `R(q) = q^ε / E(q)` (display (F1)). -/
noncomputable def Rq (ε : ℝ) (q : ℕ) : ℝ := (q : ℝ) ^ ε / Eenv ε q

/-- The signed correction pair `{q m, q m + σ}` as an interval: `[q m, q m + 1]` if `σ = 1`,
`[q m - 1, q m]` if `σ = -1`. -/
def signedPair (q m : ℕ) (σ : ℤ) : Iv :=
  if σ = 1 then Iv.pair (q * m) else Iv.pair (q * m - 1)

/-- The neighbor endpoint `q m + σ` as a natural number (for `q m ≥ 1`). -/
def neighbor (q m : ℕ) (σ : ℤ) : ℕ := if σ = 1 then q * m + 1 else q * m - 1

/-- The slot of a signed pair: the endpoint that is a multiple of `4` (the pair is then
`[y - 1, y]` or `[y, y + 1]`). Defined as `q m` if `4 ∣ q m`, else the neighbor. -/
def slot (q m : ℕ) (σ : ℤ) : ℕ := if 4 ∣ q * m then q * m else neighbor q m σ

/-- The enlarged deterministic superset of possible correction endpoints (display (D1)):
`{q m - 1, q m, q m + 1}` for prime powers `q > L` and `R(q) ≤ m ≤ 8 q^ε`. -/
def PstarSigned (ε : ℝ) (L : ℕ) : Set ℕ :=
  {n | ∃ q m : ℕ, IsPrimePow q ∧ L < q ∧ Rq ε q ≤ m ∧ (m : ℝ) ≤ 8 * (q : ℝ) ^ ε ∧
    (n = q * m - 1 ∨ n = q * m ∨ n = q * m + 1)}

/-- The data of one signed fiber at label `q` (Lemma F1's conclusion, per prime power). -/
structure SignedFiber (ε : ℝ) (q : ℕ) where
  /-- The multipliers. -/
  I : Finset ℕ
  /-- The sign attached to each multiplier. -/
  σ : ℕ → ℤ
  sign : ∀ m ∈ I, σ m = 1 ∨ σ m = -1
  lower : ∀ m ∈ I, Rq ε q ≤ m
  upper : ∀ m ∈ I, (m : ℝ) ≤ 8 * (q : ℝ) ^ ε
  lt : ∀ m ∈ I, m < q
  /-- Multipliers are coprime to the label (i.e. not divisible by its prime). -/
  coprime : ∀ m ∈ I, Nat.Coprime m q
  /-- `q m ≥ 2`, so the neighbor `q m - 1` is a positive natural. -/
  two_le : ∀ m ∈ I, 2 ≤ q * m
  /-- The neighbor `q m + σ` is strictly `q`-powersmooth. -/
  smooth : ∀ m ∈ I, Powersmooth (q - 1) (neighbor q m (σ m))
  /-- One endpoint of the pair is a multiple of four (the slot). -/
  four : ∀ m ∈ I, 4 ∣ slot q m (σ m)
  /-- Slots are distinct within the fiber. -/
  slot_inj : Set.InjOn (fun m => slot q m (σ m)) I


/-- Auxiliary family for the signed construction (docs Section 4): as `AuxFamily`, except that the
auxiliary pairs avoid the enlarged endpoint set `PstarSigned ε L` by distance two, hence are
separated from every possible signed correction pair. -/
structure AuxFamilyS (ε : ℝ) (L : ℕ) where
  /-- Left endpoints of the auxiliary pairs at stage `q`. -/
  F : ℕ → Finset ℕ
  card_eq : ∀ q, IsPrimePow q → L < q → (F q).card = s q
  lower : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, (q : ℝ) ^ ((11 : ℝ) / 10) ≤ a
  upper : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, ((a + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ ((11 : ℝ) / 10)
  four_dvd : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, 4 ∣ a
  smooth_lo : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, Powersmooth (q / 2) a
  smooth_hi : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, Powersmooth (q / 2) (a + 1)
  sep_aux : ∀ q q', IsPrimePow q → L < q → IsPrimePow q' → L < q' →
    ∀ a ∈ F q, ∀ a' ∈ F q', (q, a) ≠ (q', a') → Iv.Sep (Iv.pair a) (Iv.pair a')
  /-- Every auxiliary endpoint is at distance more than two from the enlarged endpoint set. -/
  avoid : ∀ q, IsPrimePow q → L < q → ∀ a ∈ F q, ∀ n ∈ PstarSigned ε L, n + 2 < a ∨ a + 2 < n
  count : ∃ C : ℝ, ∀ X : ℕ, ((Fstar L F ∩ Set.Icc 1 X).ncard : ℝ) ≤ C * (X : ℝ) ^ ((21 : ℝ) / 22)

/-- The protected set `U = P* ∪ F*` for the signed construction. -/
def USigned (ε : ℝ) (L : ℕ) (A : AuxFamilyS ε L) : Set ℕ := PstarSigned ε L ∪ Fstar L A.F

/-- The signed pair mass `w_σ(q m) = 1/(q m) + 1/(q m + σ)` (docs display (D3)). -/
def wSigned (q m : ℕ) (σ : ℤ) : ℚ := 1 / (q * m : ℚ) + 1 / ((q * m : ℚ) + σ)

end Erdos289
