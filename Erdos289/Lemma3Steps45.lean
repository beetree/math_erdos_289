import Erdos289.Lemma3Basic
import Erdos289.ExternalBridge

/-!
# Lemma 3: steps 4-5

The simultaneous-approximation / divisor-bound step (3.2) of Section 3 of
`erdos_289_full_proof.pdf`, isolated for parallel work. Both lemmas here are proved in
full; there is no `sorry` in this file.

* `box_prod_lt`: the pigeonhole box count of the paper (Section 3, lines 238-252).
* `paper_steps_4_5`: the quantitative form of the paper's steps 4-5, i.e. `(3.2)`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Erdos289

open Finset Filter Real Topology

/-- **Pigeonhole box count** (paper, Section 3, lines 238-252). If the reals `u i`,
`i ∈ A`, all exceed `1/4` and their product is exactly `q / 4 ^ |A|`, then the number of
boxes `∏ i ∈ A, ⌈u i⌉₊` is `< q`.

This is the paper's count "Ignore coordinates with `B i ≥ q`, and partition each remaining
coordinate into intervals of length `B i`", read through `u i = q / B i`: a *kept*
coordinate (`u i ≥ 1`, i.e. `B i ≤ q`) contributes `⌈u i⌉₊ ≤ 2 u i`, while an *ignored* one
(`u i < 1`, i.e. `B i > q`) contributes `⌈u i⌉₊ = 1 ≤ 4 u i` — this is where the paper's
"`B i ≤ 4q` for ignored coordinates because `V < q` and `a i ≥ 1`", i.e. `u i > 1/4`, is
used. Since `∏ i ∈ A, u i = q / 4 ^ |A|`, keeping at least one coordinate costs at most
`(1/2) · 4 ^ |A| · ∏ u i = q / 2 < q`; if no coordinate is kept, every factor is `1` and
the product is `1 < q`. -/
lemma box_prod_lt {q : ℕ} (hq2 : 2 ≤ q) {D : ℕ} (A : Finset (Fin D))
    (u : Fin D → ℝ) (hu : ∀ i ∈ A, 1 / 4 < u i)
    (hprod : ∏ i ∈ A, u i = (q : ℝ) / 4 ^ A.card) :
    (∏ i ∈ A, (⌈u i⌉₊ : ℝ)) < (q : ℝ) := by
  classical
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hupos : ∀ i ∈ A, 0 < u i := fun i hi => lt_trans (by norm_num) (hu i hi)
  have h4 : ∀ i ∈ A, (⌈u i⌉₊ : ℝ) ≤ 4 * u i := by
    intro i hi
    rcases le_or_gt 1 (u i) with h | h
    · have := Nat.ceil_lt_add_one (le_of_lt (hupos i hi))
      linarith
    · have h1 : (⌈u i⌉₊ : ℝ) ≤ 1 := by
        have : ⌈u i⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast h.le)
        exact_mod_cast this
      linarith [hu i hi]
  rcases Finset.eq_empty_or_nonempty (A.filter (fun i => 1 ≤ u i)) with hK | hK
  · have hex : ∀ i ∈ A, u i < 1 := by
      intro i hi
      by_contra hcon
      have hmem : i ∈ A.filter (fun i => 1 ≤ u i) :=
        Finset.mem_filter.mpr ⟨hi, not_lt.mp hcon⟩
      rw [hK] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    have hle : (∏ i ∈ A, (⌈u i⌉₊ : ℝ)) ≤ ∏ _i ∈ A, (1 : ℝ) := by
      refine Finset.prod_le_prod (fun i _ => by positivity) ?_
      intro i hi
      have : ⌈u i⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast (hex i hi).le)
      exact_mod_cast this
    simp only [Finset.prod_const_one] at hle
    linarith
  · obtain ⟨i₀, hi₀mem⟩ := hK
    rw [Finset.mem_filter] at hi₀mem
    obtain ⟨hi₀A, hi₀⟩ := hi₀mem
    have h2 : (⌈u i₀⌉₊ : ℝ) ≤ 2 * u i₀ := by
      have := Nat.ceil_lt_add_one (le_of_lt (hupos i₀ hi₀A)); linarith
    have e1 : (∏ i ∈ A, (⌈u i⌉₊ : ℝ)) = (⌈u i₀⌉₊ : ℝ) * ∏ i ∈ A.erase i₀, (⌈u i⌉₊ : ℝ) :=
      (Finset.mul_prod_erase A _ hi₀A).symm
    have e2 : (∏ i ∈ A.erase i₀, (⌈u i⌉₊ : ℝ)) ≤ ∏ i ∈ A.erase i₀, (4 * u i) :=
      Finset.prod_le_prod (fun i _ => by positivity)
        (fun i hi => h4 i (Finset.mem_of_mem_erase hi))
    have e3 : (∏ i ∈ A, (4 * u i)) = (4 * u i₀) * ∏ i ∈ A.erase i₀, (4 * u i) :=
      (Finset.mul_prod_erase A _ hi₀A).symm
    have e4 : (∏ i ∈ A, (4 * u i)) = (q : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hprod]
      have h40 : (4 : ℝ) ^ A.card ≠ 0 := by positivity
      field_simp
    calc (∏ i ∈ A, (⌈u i⌉₊ : ℝ))
        = (⌈u i₀⌉₊ : ℝ) * ∏ i ∈ A.erase i₀, (⌈u i⌉₊ : ℝ) := e1
      _ ≤ (2 * u i₀) * ∏ i ∈ A.erase i₀, (4 * u i) := by
          refine mul_le_mul h2 e2 (Finset.prod_nonneg (fun i _ => by positivity)) (by linarith)
      _ = (1 / 2) * ((4 * u i₀) * ∏ i ∈ A.erase i₀, (4 * u i)) := by ring
      _ = (1 / 2) * (q : ℝ) := by rw [← e3, e4]
      _ < (q : ℝ) := by linarith

/-- **Paper's steps 4-5, quantitative form (`(3.2)`).** For a proper GAP `P` representing `0`
via `v` and every `j ∈ J` (`J` a set of naturals `< q`, each with a small modular-inverse
witness `i j ≤ C q^ε` for a fixed `C ≥ 1`, `|J| ≥ q^(7ε/8)/2`), the active-coordinate count
`d ≥ 1` and product `V` of active extents satisfy `V ≥ q^(1 - dε/8 - dε/500) / (16Cd)^d`.
(The paper's Lemma 3 is the case `C = 2`, where the constant is the stated `(32d)^d`.)

This is the paper's simultaneous-approximation / divisor-bound argument (Section 3,
steps 4-5). The proof:

* If `V ≥ q` the bound is trivial (the exponent is `≤ 1` and `(16Cd)^d ≥ 1`), so assume
  `V < q` and put `ρ := (V/q)^(1/d) ∈ (0,1)`.
* Apply `simultaneous_approx` with the paper's box sizes `B i := (4q/a i) ρ` on the active
  coordinates and `B i := q` on the inactive ones (whose constraint is then vacuous, the
  corresponding pigeonhole factor being `⌈q/q⌉₊ = 1`). The required box count
  `∏ i, ⌈q/B i⌉₊ < q` is exactly `box_prod_lt` applied to `u i = q/B i = a i/(4ρ)`: these
  satisfy `u i > 1/4` (because `a i ≥ 1` and `ρ < 1`) and `∏ i ∈ A, u i = V/(4ρ)^d = q/4^d`.
  Note that no upper bound on `V` beyond `V < q` is needed.
* This produces `1 ≤ T < q` and `e i ≡ T d i (mod q)` with `|e i| ≤ B i`. For `j ∈ J`,
  `gap_active_repr` writes `j = ∑ (n i - v i) d i` over the active coordinates with
  `|n i - v i| ≤ a i`, so `h j := ∑ (n i - v i) e i` satisfies `h j ≡ T j (mod q)` and
  `|h j| ≤ ∑ a i B i = 4 d q ρ =: R`.
* `divisor_count_bound`, with `Imax := C q^ε` and the divisor majorant
  `x ↦ max n₀ (x^(ε/4000))` coming from `divisor_bound`, then gives
  `|J| ≤ (8 C d q^ε ρ + 5) · q^(ε/2000)` for large `q` (using `q(Z+1) ≤ q²`).
* Comparing with `|J| ≥ q^(7ε/8)/2` and absorbing the additive `5` (the slack
  `q^(3ε/2000) ≥ 2` and `q^(7ε/8 - ε/500) ≥ 10` is what the choice `ε/4000 < ε/1000` buys)
  yields `16 C d ρ ≥ q^(-ε/8 - ε/500)`, i.e. `V = q ρ^d ≥ q^(1 - dε/8 - dε/500)/(16Cd)^d`.

All four "large `q`" thresholds are independent of `P`, `v`, `J` and of `d` (they do depend
on the fixed constants `ε`, `C`, `d₀`), so the single `Q₀` produced here is uniform over the
finitely many ranks `d ≤ d₀`. -/
lemma paper_steps_4_5 (ε c C : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (_hc : 0 < c) (hC : 1 ≤ C)
    (d₀ : ℕ) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, 2 ≤ q → Q₀ ≤ q →
      ∀ (P : GAP) (v : Fin P.D → ℤ) (J : Finset ℕ),
        P.D ≤ d₀ →
        (∀ i, P.α i ≤ (v i:ℝ) ∧ (v i:ℝ) ≤ P.β i) → (∑ i, v i * P.d i = 0) →
        (∀ j ∈ J, (j:ℤ) ∈ P.set) → (∀ j ∈ J, j < q) →
        (∀ j ∈ J, ∃ i : ℕ, 0 < i ∧ (i:ℝ) ≤ C * (q:ℝ)^ε ∧ (i:ZMod q) * (j:ZMod q) = 1) →
        (q:ℝ)^(7*ε/8) / 2 ≤ (J.card:ℝ) →
        1 ≤ (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card →
        ((∏ i ∈ Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋), (⌊P.β i⌋ - ⌈P.α i⌉).toNat : ℕ)
              : ℝ)
          ≥ (q:ℝ) ^ (1 - ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ) * ε / 8
                - ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ) * ε / 500)
            / (16 * C * ((Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card : ℝ)) ^
                (Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋)).card := by
  classical
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC
  -- The divisor-bound majorant `Dfun`.
  have hε'0 : (0:ℝ) < ε / 4000 := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (divisor_bound (ε / 4000) hε'0)
  obtain ⟨Dfun, hDval⟩ : ∃ f : ℝ → ℝ, ∀ x : ℝ, f x = max (n₀ : ℝ) (x ^ (ε / 4000)) :=
    ⟨_, fun _ => rfl⟩
  have hDmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → Dfun x ≤ Dfun y := by
    intro x y hx hxy
    rw [hDval, hDval]
    exact max_le_max le_rfl (Real.rpow_le_rpow hx hxy hε'0.le)
  have hDdiv : ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℝ)) ≤ Dfun (n : ℝ) := by
    intro n hn
    rw [hDval]
    rcases le_or_gt n₀ n with h | h
    · exact le_trans (hn₀ n h) (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      have h1 : ((n.divisors.card : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.card_divisors_le_self n
      have h2 : (n : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast h.le
      linarith
  have hDnn : ∀ x : ℝ, 0 ≤ Dfun x := by
    intro x
    rw [hDval]
    exact le_trans (by positivity) (le_max_left (n₀:ℝ) (x ^ (ε/4000)))
  -- The four "for sufficiently large `q`" estimates.
  have hEv : ∀ᶠ q : ℕ in atTop,
      ((n₀ : ℝ) ≤ (q : ℝ) ^ (ε / 2000)) ∧
      ((4 * C * (d₀ : ℝ) + 3) * (q : ℝ) ^ (1 + ε) ≤ (q : ℝ) ^ (2 : ℝ)) ∧
      ((2 : ℝ) ≤ (q : ℝ) ^ (3 * ε / 2000)) ∧
      ((10 : ℝ) ≤ (q : ℝ) ^ (7 * ε / 8 - ε / 500)) := by
    have k1 := eventually_rpow_dominates (ε / 4000) (ε / 2000) 0 (n₀ : ℝ)
      (by positivity) (by linarith)
    have k2 := eventually_rpow_dominates (1 + ε) 2 (4 * C * (d₀ : ℝ) + 3) 0
      (by linarith) (by linarith)
    have k3 := eventually_rpow_dominates (3 * ε / 4000) (3 * ε / 2000) 0 2
      (by positivity) (by linarith)
    have k4 := eventually_rpow_dominates ((7 * ε / 8 - ε / 500) / 2) (7 * ε / 8 - ε / 500) 0 10
      (by linarith) (by linarith)
    filter_upwards [k1, k2, k3, k4] with q h1 h2 h3 h4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨Q₀, ?_⟩
  intro q hq2 hqQ P v J hPD hv hv0 hJP hJq hJinv hJcard hd1
  obtain ⟨hEv1, hEv2, hEv3, hEv4⟩ := hQ₀ q hqQ
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq0
  set A : Finset (Fin P.D) := Finset.univ.filter (fun i => ⌈P.α i⌉ < ⌊P.β i⌋) with hAdef
  set V : ℕ := ∏ i ∈ A, (⌊P.β i⌋ - ⌈P.α i⌉).toNat with hVdef
  clear_value V
  clear_value A
  have hAmem : ∀ i : Fin P.D, i ∈ A ↔ ⌈P.α i⌉ < ⌊P.β i⌋ := by
    intro i; rw [hAdef]; simp
  have hAcard : A.card ≤ P.D := by simpa using Finset.card_le_univ A
  have hdcard : A.card ≤ d₀ := le_trans hAcard hPD
  obtain ⟨a, ha⟩ : ∃ a : Fin P.D → ℕ, ∀ i, a i = (⌊P.β i⌋ - ⌈P.α i⌉).toNat := ⟨_, fun _ => rfl⟩
  have hVa : V = ∏ i ∈ A, a i := by
    rw [hVdef]; exact Finset.prod_congr rfl (fun i _ => (ha i).symm)
  have ha1 : ∀ i ∈ A, 1 ≤ a i := by
    intro i hi
    have := (hAmem i).mp hi
    rw [ha i]; omega
  have haZ : ∀ i ∈ A, ((a i : ℤ)) = ⌊P.β i⌋ - ⌈P.α i⌉ := by
    intro i hi
    have := (hAmem i).mp hi
    rw [ha i]; omega
  have haR : ∀ i ∈ A, (0:ℝ) < (a i : ℝ) := by
    intro i hi
    have := ha1 i hi
    exact_mod_cast (by omega : 0 < a i)
  have hV1 : 1 ≤ V := by rw [hVa]; exact Finset.one_le_prod' ha1
  have hd1' : 1 ≤ A.card := hd1
  have hdR1 : (1:ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hd1'
  -- The constant `16 C d` of the conclusion is `≥ 1` (and in particular positive).
  have hCd1 : (1:ℝ) ≤ C * (A.card : ℝ) := by
    have := mul_le_mul hC hdR1 zero_le_one (le_trans zero_le_one hC)
    linarith [this]
  have hden1 : (1:ℝ) ≤ 16 * C * (A.card : ℝ) := by linarith
  have hden_pos : (0:ℝ) < 16 * C * (A.card : ℝ) := by linarith
  rcases le_or_gt (q:ℝ) (V:ℝ) with hVge | hVlt
  · -- Trivial case `V ≥ q`.
    have hexp : (q:ℝ) ^ (1 - (A.card:ℝ) * ε / 8 - (A.card:ℝ) * ε / 500) ≤ (q:ℝ) := by
      have h1 : (q:ℝ) ^ (1 - (A.card:ℝ) * ε / 8 - (A.card:ℝ) * ε / 500) ≤ (q:ℝ) ^ (1:ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
        nlinarith
      simpa using h1
    have hden : (1:ℝ) ≤ (16 * C * (A.card:ℝ)) ^ A.card := one_le_pow₀ hden1
    rw [ge_iff_le, div_le_iff₀ (pow_pos hden_pos _)]
    nlinarith
  · -- Main case `V < q`.
    have hVR0 : (0:ℝ) < (V:ℝ) := by exact_mod_cast (by omega : 0 < V)
    have hVne : (V:ℝ) ≠ 0 := ne_of_gt hVR0
    have hVq0 : (0:ℝ) < (V:ℝ) / (q:ℝ) := by positivity
    have hVq1 : (V:ℝ) / (q:ℝ) < 1 := by rw [div_lt_one hq0]; exact hVlt
    set ρ : ℝ := ((V:ℝ) / (q:ℝ)) ^ (((A.card : ℕ) : ℝ))⁻¹ with hρdef
    have hρpos : 0 < ρ := Real.rpow_pos_of_pos hVq0 _
    have hρlt1 : ρ < 1 := Real.rpow_lt_one hVq0.le hVq1 (by positivity)
    have hρd : ρ ^ A.card = (V:ℝ) / (q:ℝ) :=
      Real.rpow_inv_natCast_pow hVq0.le (by omega)
    clear_value ρ
    -- Box sizes.
    set B : Fin P.D → ℝ := fun i => if i ∈ A then 4 * (q:ℝ) * ρ / (a i) else (q:ℝ) with hBdef
    have hBmem : ∀ i ∈ A, B i = 4 * (q:ℝ) * ρ / (a i) := by
      intro i hi; simp only [hBdef, hi, reduceIte]
    have hBnot : ∀ i, i ∉ A → B i = (q:ℝ) := by
      intro i hi; simp only [hBdef, hi, reduceIte]
    have hBpos : ∀ i, 0 < B i := by
      intro i
      by_cases hi : i ∈ A
      · rw [hBmem i hi]; have := haR i hi; positivity
      · rw [hBnot i hi]; exact hq0
    clear_value B
    set u : Fin P.D → ℝ := fun i => (a i : ℝ) / (4 * ρ) with hudef
    have hqB : ∀ i ∈ A, (q:ℝ) / B i = u i := by
      intro i hi
      rw [hBmem i hi]
      simp only [hudef]
      have h1 := haR i hi
      field_simp
    have huq : ∀ i ∈ A, 1 / 4 < u i := by
      intro i hi
      simp only [hudef]
      have h1 : (1:ℝ) ≤ (a i : ℝ) := by exact_mod_cast ha1 i hi
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have hprodu : ∏ i ∈ A, u i = (q:ℝ) / 4 ^ A.card := by
      simp only [hudef]
      rw [Finset.prod_div_distrib, Finset.prod_const]
      have h1 : ∏ i ∈ A, ((a i : ℕ) : ℝ) = (V:ℝ) := by rw [hVa]; push_cast; ring
      rw [h1]
      have h2 : (4 * ρ) ^ A.card = 4 ^ A.card * ((V:ℝ) / (q:ℝ)) := by rw [mul_pow, hρd]
      rw [h2]
      have h3 : ((4:ℝ) ^ A.card) ≠ 0 := by positivity
      field_simp
    clear_value u
    have hboxlt : (∏ i, ⌈(q:ℝ) / B i⌉₊) < q := by
      have hlt := box_prod_lt hq2 A u huq hprodu
      have hsplit : ((∏ i, ⌈(q:ℝ) / B i⌉₊ : ℕ) : ℝ) = ∏ i ∈ A, (⌈u i⌉₊ : ℝ) := by
        rw [Nat.cast_prod]
        rw [← Finset.prod_subset (Finset.subset_univ A)
          (f := fun i => ((⌈(q:ℝ) / B i⌉₊ : ℕ) : ℝ)) ?_]
        · exact Finset.prod_congr rfl (fun i hi => by rw [hqB i hi])
        · intro x _ hx
          rw [hBnot x hx, div_self hqne]
          simp
      have hfin : ((∏ i, ⌈(q:ℝ) / B i⌉₊ : ℕ) : ℝ) < (q:ℝ) := by rw [hsplit]; exact hlt
      exact_mod_cast hfin
    obtain ⟨T, hT1, hTq, hTe⟩ := simultaneous_approx hq2 P.d B hBpos hboxlt
    choose e he1 he2 using hTe
    -- The witnesses `h j` of the paper's step 5.
    have hkey : ∀ j : ℕ, ∃ w : ℤ, j ∈ J →
        (|(w : ℝ)| ≤ 4 * (A.card : ℝ) * (q:ℝ) * ρ ∧
          ((w : ZMod q) = (T : ZMod q) * (j : ZMod q))) := by
      intro j
      by_cases hjJ : j ∈ J
      · obtain ⟨n, hn, hjeq, hbnd, hinact⟩ := gap_active_repr P v hv hv0 (j:ℤ) (hJP j hjJ)
        rw [← hAdef] at hjeq
        refine ⟨∑ i ∈ A, (n i - v i) * e i, fun _ => ⟨?_, ?_⟩⟩
        · have hcast : ((∑ i ∈ A, (n i - v i) * e i : ℤ) : ℝ)
              = ∑ i ∈ A, ((n i - v i : ℤ) : ℝ) * ((e i : ℤ) : ℝ) := by push_cast; ring
          rw [hcast]
          have hterm : ∀ i ∈ A, |((n i - v i : ℤ) : ℝ) * ((e i : ℤ) : ℝ)| ≤ (a i : ℝ) * B i := by
            intro i hi
            have hA' : ⌈P.α i⌉ < ⌊P.β i⌋ := (hAmem i).mp hi
            have h1 : |((n i - v i : ℤ) : ℝ)| ≤ ((a i : ℕ) : ℝ) := by
              have h3 : |n i - v i| ≤ (a i : ℤ) := by rw [haZ i hi]; exact hbnd i hA'
              have h4 : ((|n i - v i| : ℤ) : ℝ) ≤ ((a i : ℤ) : ℝ) := by exact_mod_cast h3
              rw [Int.cast_abs] at h4
              simpa using h4
            rw [abs_mul]
            exact mul_le_mul h1 (he2 i) (abs_nonneg _) (le_of_lt (haR i hi))
          have hsum : ∀ i ∈ A, (a i : ℝ) * B i = 4 * (q:ℝ) * ρ := by
            intro i hi
            rw [hBmem i hi]
            have := (haR i hi).ne'
            field_simp
          calc |∑ i ∈ A, ((n i - v i : ℤ) : ℝ) * ((e i : ℤ) : ℝ)|
              ≤ ∑ i ∈ A, |((n i - v i : ℤ) : ℝ) * ((e i : ℤ) : ℝ)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i ∈ A, (a i : ℝ) * B i := Finset.sum_le_sum hterm
            _ = 4 * (A.card : ℝ) * (q:ℝ) * ρ := by
                rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
                ring
        · have hh1 : ((∑ i ∈ A, (n i - v i) * e i : ℤ) : ZMod q)
              = (T : ZMod q) * ((∑ i ∈ A, (n i - v i) * P.d i : ℤ) : ZMod q) := by
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [he1 i]; ring
          rw [hh1, ← hjeq]
          push_cast
          ring
      · exact ⟨0, fun hcc => absurd hcc hjJ⟩
    choose hfun hfunspec using hkey
    have hkey2 : ∀ j : ℕ, ∃ i0 : ℕ, j ∈ J →
        (0 < i0 ∧ (i0 : ℝ) ≤ C * (q:ℝ) ^ ε ∧ ((i0 : ZMod q) * (j : ZMod q) = 1)) := by
      intro j
      by_cases hjJ : j ∈ J
      · obtain ⟨i0, h1, h2, h3⟩ := hJinv j hjJ
        exact ⟨i0, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨1, fun hcc => absurd hcc hjJ⟩
    choose i0 hi0spec using hkey2
    have hCqnn : (0:ℝ) ≤ C * (q:ℝ) ^ ε := mul_nonneg hCpos.le (Real.rpow_nonneg hq0.le ε)
    have hdcb := divisor_count_bound hq2 T hT1 hTq (4 * (A.card : ℝ) * (q:ℝ) * ρ)
      (C * (q:ℝ) ^ ε) (by positivity) hCqnn J hJq hfun hfunspec i0
      (fun j hj => (hi0spec j hj).1) (fun j hj => (hi0spec j hj).2.1)
      (fun j hj => (hi0spec j hj).2.2) Dfun hDmono hDdiv
    have hyeq : C * (q:ℝ) ^ ε * (4 * (A.card : ℝ) * (q:ℝ) * ρ) / (q:ℝ)
        = 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ := by
      field_simp
    rw [hyeq] at hdcb
    set Z : ℕ := ⌈4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 1⌉₊ with hZdef
    have hZnn : (0:ℝ) ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ := by
      have h1 : (0:ℝ) ≤ (A.card : ℝ) := by positivity
      have h2 : (0:ℝ) ≤ (q:ℝ) ^ ε := Real.rpow_nonneg hq0.le ε
      have h3 : (0:ℝ) ≤ 4 * C := by linarith
      have h4 : (0:ℝ) ≤ 4 * C * (A.card : ℝ) := mul_nonneg h3 h1
      have h5 : (0:ℝ) ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε := mul_nonneg h4 h2
      exact mul_nonneg h5 hρpos.le
    have hZle : (Z : ℝ) ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 2 := by
      rw [hZdef]
      have hnn : (0:ℝ) ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 1 := by linarith
      linarith [Nat.ceil_lt_add_one hnn]
    clear_value Z
    have hqZ : (q:ℝ) * ((Z:ℝ) + 1) ≤ (q:ℝ) ^ (2:ℝ) := by
      have hqe : (0:ℝ) ≤ (q:ℝ) ^ ε := by positivity
      have hcardR : (A.card : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast hdcard
      have hcard0 : (0:ℝ) ≤ (A.card : ℝ) := by positivity
      have hA0 : (0:ℝ) ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε :=
        mul_nonneg (mul_nonneg (by linarith) hcard0) hqe
      have h1 : 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ ≤ 4 * C * (d₀ : ℝ) * (q:ℝ) ^ ε := by
        have hstep : 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ
            ≤ 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε * 1 :=
          mul_le_mul_of_nonneg_left hρlt1.le hA0
        have hstep2 : 4 * C * (A.card : ℝ) * (q:ℝ) ^ ε ≤ 4 * C * (d₀ : ℝ) * (q:ℝ) ^ ε := by
          have hbase : 4 * C * (A.card : ℝ) ≤ 4 * C * (d₀ : ℝ) := by nlinarith
          exact mul_le_mul_of_nonneg_right hbase hqe
        linarith
      have h2 : (q:ℝ) * ((Z:ℝ) + 1) ≤ (q:ℝ) * (4 * C * (d₀ : ℝ) * (q:ℝ) ^ ε + 3) :=
        mul_le_mul_of_nonneg_left (by linarith) hq0.le
      have h3 : (q:ℝ) * (4 * C * (d₀ : ℝ) * (q:ℝ) ^ ε + 3)
          = 4 * C * (d₀ : ℝ) * ((q:ℝ) ^ (1 + ε)) + 3 * (q:ℝ) := by
        rw [Real.rpow_add hq0, Real.rpow_one]; ring
      have h4 : (q:ℝ) ≤ (q:ℝ) ^ (1 + ε) := by
        have := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : (1:ℝ) ≤ 1 + ε)
        simpa using this
      have hd₀nn : (0:ℝ) ≤ (d₀:ℝ) := by positivity
      have h5 : (0:ℝ) ≤ 4 * C * (d₀ : ℝ) := mul_nonneg (by linarith) hd₀nn
      nlinarith [hEv2]
    have hDb : Dfun ((q:ℝ) * ((Z:ℝ) + 1)) ≤ (q:ℝ) ^ (ε / 2000) := by
      rw [hDval]
      refine max_le hEv1 ?_
      have h1 : ((q:ℝ) * ((Z:ℝ) + 1)) ^ (ε / 4000) ≤ ((q:ℝ) ^ (2:ℝ)) ^ (ε / 4000) :=
        Real.rpow_le_rpow (by positivity) hqZ hε'0.le
      have h2 : ((q:ℝ) ^ (2:ℝ)) ^ (ε / 4000) = (q:ℝ) ^ (ε / 2000) := by
        rw [← Real.rpow_mul hq0.le]
        congr 1
        ring
      linarith
    have hJ2 : (J.card : ℝ)
        ≤ (8 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 5) * (q:ℝ) ^ (ε / 2000) := by
      refine le_trans hdcb ?_
      have hc1 : 2 * (Z:ℝ) + 1 ≤ 8 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 5 := by linarith [hZle]
      exact mul_le_mul hc1 hDb (hDnn _) (by linarith)
    -- Solve for `ρ`.
    have hs : (q:ℝ) ^ (7 * ε / 8)
        = (q:ℝ) ^ (7 * ε / 8 - ε / 500) * (q:ℝ) ^ (ε / 2000) * (q:ℝ) ^ (3 * ε / 2000) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 1
      ring
    have hW : (0:ℝ) < (q:ℝ) ^ (ε / 2000) := by positivity
    have hstep1 : (q:ℝ) ^ (7 * ε / 8 - ε / 500) * (q:ℝ) ^ (ε / 2000) ≤ (q:ℝ) ^ (7 * ε / 8) / 2 := by
      rw [hs]
      have hnn : (0:ℝ) ≤ (q:ℝ) ^ (7 * ε / 8 - ε / 500) * (q:ℝ) ^ (ε / 2000) := by positivity
      nlinarith [hEv3]
    have hstep2 : (q:ℝ) ^ (7 * ε / 8 - ε / 500)
        ≤ 8 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 5 := by
      have h1 : (q:ℝ) ^ (7 * ε / 8 - ε / 500) * (q:ℝ) ^ (ε / 2000)
          ≤ (8 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ + 5) * (q:ℝ) ^ (ε / 2000) := by
        linarith [hstep1, hJcard, hJ2]
      exact le_of_mul_le_mul_right h1 hW
    have hstep3 : (q:ℝ) ^ (7 * ε / 8 - ε / 500) / 2
        ≤ 8 * C * (A.card : ℝ) * (q:ℝ) ^ ε * ρ := by
      linarith [hEv4, hstep2]
    have hqeps : (0:ℝ) < (q:ℝ) ^ ε := by positivity
    have hρge : (q:ℝ) ^ (7 * ε / 8 - ε / 500 - ε) ≤ 16 * C * (A.card : ℝ) * ρ := by
      have h1 : (q:ℝ) ^ (7 * ε / 8 - ε / 500)
          = (q:ℝ) ^ (7 * ε / 8 - ε / 500 - ε) * (q:ℝ) ^ ε := by
        rw [← Real.rpow_add hq0]; congr 1; ring
      rw [h1] at hstep3
      have h2 : (q:ℝ) ^ (7 * ε / 8 - ε / 500 - ε) * (q:ℝ) ^ ε
          ≤ (16 * C * (A.card : ℝ) * ρ) * (q:ℝ) ^ ε := by nlinarith
      exact le_of_mul_le_mul_right h2 hqeps
    have hfinρ : (q:ℝ) ^ (-(ε/8) - ε/500) / (16 * C * (A.card : ℝ)) ≤ ρ := by
      have hexpeq : 7 * ε / 8 - ε / 500 - ε = -(ε/8) - ε/500 := by ring
      rw [hexpeq] at hρge
      rw [div_le_iff₀ hden_pos]
      linarith [hρge]
    have hpow : ((q:ℝ) ^ (-(ε/8) - ε/500) / (16 * C * (A.card : ℝ))) ^ A.card ≤ ρ ^ A.card :=
      pow_le_pow_left₀ (div_nonneg (Real.rpow_nonneg hq0.le _) hden_pos.le) hfinρ _
    have hVeq : (V:ℝ) = (q:ℝ) * ρ ^ A.card := by rw [hρd]; field_simp
    have hqe2 : ((q:ℝ) ^ (-(ε/8) - ε/500)) ^ A.card
        = (q:ℝ) ^ ((-(ε/8) - ε/500) * (A.card : ℝ)) := by
      rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
    have hfinal : (q:ℝ) * (((q:ℝ) ^ (-(ε/8) - ε/500) / (16 * C * (A.card : ℝ))) ^ A.card)
        = (q:ℝ) ^ (1 - (A.card : ℝ) * ε / 8 - (A.card : ℝ) * ε / 500)
            / (16 * C * (A.card : ℝ)) ^ A.card := by
      rw [div_pow, hqe2]
      rw [show (1:ℝ) - (A.card : ℝ) * ε / 8 - (A.card : ℝ) * ε / 500
            = 1 + (-(ε/8) - ε/500) * (A.card : ℝ) by ring]
      rw [Real.rpow_add hq0, Real.rpow_one]
      ring
    rw [ge_iff_le, ← hfinal, hVeq]
    exact mul_le_mul_of_nonneg_left hpow hq0.le

end Erdos289
