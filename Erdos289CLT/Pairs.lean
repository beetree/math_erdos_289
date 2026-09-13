import Erdos289CLT.Basic
import Erdos289CLT.Chebyshev
import Erdos289CLT.PairsCount

/-!
# Pairs supplying the successive quotients (paper Lemma 1, `pairs`)

For a large prime power `q = p^α` there are `≫ q / log q` values `m` with
`p ∤ m`, `m < q`, `m ≫ q / log q`, such that the pair `{q m, q m + ε}` (`ε = ±1`)
has companion `q m + ε` all of whose prime-power divisors are below `q`, and whose
centre is a multiple of `8`.

Encoding.  The pair is `Iv.pair (lo m) = [lo m, lo m + 1]` with `q m ∈ {lo m, lo m + 1}`;
its companion is the other element, `companion q (lo m) m = 2 lo m + 1 - q m`; its centre
is `q m` when `q` is even and the companion when `q` is odd (`ctr`).

Proof sketch (paper).  Take primes `b ∈ (q/D, q/16)`, `b ≠ p` (`primes_in_range`), set
`d = 8` (`p` odd) or `d = 1` (`p = 2`), `r = d b`, `t = r⁻¹ mod q`; then
`m₊ = (r t - 1)/q`, `m₋ = (r (q - t) + 1)/q` satisfy `m₊ + m₋ = r`, both in `(0, r)`,
one of them coprime to `p`; its companion is `d b T` with `T ∈ {t, q - t}`.
The construction is `PairsCore.lean` (`mOf`, `loOf`, `TOf`, `carrier_props`,
`good_carrier_powersmooth`) and the counting is `PairsCount.lean`: bad carriers number at
most `8 Dc + 16`, and each `m` arises from at most four carriers.  Here: take the carriers
from `primes_in_range` (at least `c₁ q / log q` of them for `q ≥ x₀`), remove the bad ones
and `p`, map to `m` (fibres `≤ 4`), and keep the larger half of the resulting `m`
(`M := M'.filter (M'.card / 2 ≤ ·)`), so that every retained `m ≥ M'.card / 2`.
Choose `c₀` (e.g. `c₁ / 32`) and `q₀` so that the `O(1)` losses are absorbed.
-/

namespace Erdos289.CLT

open Finset

theorem pairs_lemma : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ q₀ : ℕ, ∀ p α : ℕ, p.Prime → 0 < α → q₀ ≤ p ^ α →
    ∃ (M : Finset ℕ) (lo : ℕ → ℕ),
      c₀ * ((p ^ α : ℕ) : ℝ) / Real.log ((p ^ α : ℕ) : ℝ) ≤ M.card ∧
      ∀ m ∈ M,
        c₀ * ((p ^ α : ℕ) : ℝ) / Real.log ((p ^ α : ℕ) : ℝ) ≤ m ∧ m < p ^ α ∧
        Nat.Coprime m (p ^ α) ∧
        (lo m = p ^ α * m ∨ lo m + 1 = p ^ α * m) ∧
        Powersmooth (p ^ α - 1) (companion (p ^ α) (lo m) m) ∧
        8 ∣ ctr (p ^ α) (lo m) m := by
  classical
  obtain ⟨Dc, hDc16, c₁, hc₁, x₀, hx₀⟩ := primes_in_range
  have hDcpos : (0:ℝ) < (Dc:ℝ) := by exact_mod_cast (by omega : 0 < Dc)
  set c₀ : ℝ := c₁ / 16 with hc₀def
  have hc₀pos : 0 < c₀ := by positivity
  set K : ℝ := 2 * (17 + 8 * (Dc:ℝ)) / c₁ + 16 / c₁ with hKdef
  have hKpos : 0 < K := by positivity
  set q0R : ℝ := max (4 * K ^ 2 + 1) 4 with hq0Rdef
  set q₀ : ℕ := max x₀ (max (Dc ^ 3 + 1) (⌈q0R⌉₊)) with hq₀def
  refine ⟨c₀, hc₀pos, q₀, fun p α hp hα hqq₀ => ?_⟩
  set q : ℕ := p ^ α with hqdef
  have hqx₀ : x₀ ≤ q := le_trans (le_max_left _ _) hqq₀
  have hqDc3 : Dc ^ 3 < q := by
    have h1 : Dc ^ 3 + 1 ≤ q :=
      le_trans (le_trans (le_max_left _ (⌈q0R⌉₊)) (le_max_right x₀ _)) hqq₀
    omega
  have hq0R : q0R ≤ (q:ℝ) := by
    have h1 : ⌈q0R⌉₊ ≤ q :=
      le_trans (le_trans (le_max_right (Dc ^ 3 + 1) _) (le_max_right x₀ _)) hqq₀
    calc q0R ≤ (⌈q0R⌉₊:ℝ) := Nat.le_ceil _
      _ ≤ (q:ℝ) := by exact_mod_cast h1
  have hq4 : (4:ℝ) ≤ (q:ℝ) := le_trans (le_max_right _ _) hq0R
  have hqK2 : 4 * K ^ 2 + 1 ≤ (q:ℝ) := le_trans (le_max_left _ _) hq0R
  have hq1 : (1:ℝ) < (q:ℝ) := by linarith
  have hqposR : (0:ℝ) < (q:ℝ) := by linarith
  have hlogqpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  -- Q := q / log q, and the key growth bound K ≤ Q
  set Q : ℝ := (q:ℝ) / Real.log (q:ℝ) with hQdef
  have hsqrtq_ge : 2 * K ≤ Real.sqrt (q:ℝ) := by
    have h1 : (2 * K) ^ 2 ≤ (q:ℝ) := by nlinarith [hqK2]
    have h2 : 0 ≤ 2 * K := by linarith
    calc 2 * K = Real.sqrt ((2 * K) ^ 2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt (q:ℝ) := Real.sqrt_le_sqrt h1
  have hlog_lt : Real.log (q:ℝ) < 2 * Real.sqrt (q:ℝ) := by
    have hsqrtpos : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqposR
    have h1 : Real.log (Real.sqrt (q:ℝ)) ≤ Real.sqrt (q:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hsqrtpos
    have h2 : Real.log (Real.sqrt (q:ℝ)) = Real.log (q:ℝ) / 2 := Real.log_sqrt hqposR.le
    linarith
  have hqK : K ≤ Q := by
    rw [hQdef, le_div_iff₀ hlogqpos]
    have hstep1 : K * Real.log (q:ℝ) < K * (2 * Real.sqrt (q:ℝ)) :=
      mul_lt_mul_of_pos_left hlog_lt hKpos
    have hstep2 : K * (2 * Real.sqrt (q:ℝ)) ≤ Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) := by
      nlinarith [Real.sqrt_nonneg (q:ℝ), hsqrtq_ge]
    have hsq : Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) = (q:ℝ) := Real.mul_self_sqrt hqposR.le
    linarith
  -- the carrier set
  set base : Finset ℕ := (Finset.Ioo (q / Dc) (q / 16)).filter Nat.Prime with hbasedef
  set carriers : Finset ℕ := base.erase p with hcarriersdef
  have hcar : ∀ b ∈ carriers, b.Prime ∧ b ≠ p ∧ q / Dc < b ∧ b < q / 16 := by
    intro b hb
    rw [hcarriersdef, Finset.mem_erase] at hb
    obtain ⟨hbne, hbbase⟩ := hb
    rw [hbasedef, Finset.mem_filter, Finset.mem_Ioo] at hbbase
    exact ⟨hbbase.2, hbne, hbbase.1.1, hbbase.1.2⟩
  have hbase_card : c₁ * Q ≤ (base.card:ℝ) := by
    have h := hx₀ q hqx₀
    rw [mul_div_assoc, ← hQdef] at h
    exact h
  have hcarriers_card : (base.card:ℝ) - 1 ≤ (carriers.card:ℝ) := by
    have h1 : base.card ≤ carriers.card + 1 := by
      have := Finset.pred_card_le_card_erase (s := base) (a := p)
      rw [← hcarriersdef] at this
      omega
    have : (base.card:ℝ) ≤ (carriers.card:ℝ) + 1 := by exact_mod_cast h1
    linarith
  -- bad carriers
  set bad1 : Finset ℕ := carriers.filter (fun b => b ∣ TOf p q b) with hbad1def
  have hbad1 : bad1.card ≤ 8 * Dc := by
    rw [hbad1def]
    exact card_bad_b_le hp hα hDc16 hqDc3 carriers hcar
  set bad2 : Finset ℕ :=
    carriers.filter (fun b => p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b) with hbad2def
  have hbad2 : bad2.card ≤ 16 := by
    by_cases hp2 : p = 2
    · have : bad2 = ∅ := by
        rw [hbad2def]
        apply Finset.filter_false_of_mem
        intro b _ ⟨hne, _⟩
        exact hne hp2
      rw [this]
      simp
    · have heq : bad2 = carriers.filter (fun b => 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b) := by
        rw [hbad2def]
        apply Finset.filter_congr
        intro b _
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨hp2, h⟩
      rw [heq]
      exact card_bad_two_le hp hα hDc16 hqDc3 hp2 carriers hcar
  set good : Finset ℕ :=
    carriers.filter (fun b => ¬ b ∣ TOf p q b ∧ (p ≠ 2 → ¬ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))
    with hgooddef
  have hgood_eq : good =
      carriers.filter (fun b => ¬ (b ∣ TOf p q b ∨ (p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))) := by
    rw [hgooddef]
    apply Finset.filter_congr
    intro b _
    constructor
    · rintro ⟨h1, h2⟩ (h | ⟨hp2, h⟩)
      · exact h1 h
      · exact h2 hp2 h
    · intro h
      constructor
      · intro hb; exact h (Or.inl hb)
      · intro hp2 hb; exact h (Or.inr ⟨hp2, hb⟩)
  have hbadunion_card :
      (carriers.filter
        (fun b => b ∣ TOf p q b ∨ (p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))).card ≤
        8 * Dc + 16 := by
    rw [Finset.filter_or, ← hbad1def, ← hbad2def]
    calc (bad1 ∪ bad2).card ≤ bad1.card + bad2.card := Finset.card_union_le _ _
      _ ≤ 8 * Dc + 16 := by omega
  have hgood_card_eq :
      (carriers.filter
        (fun b => b ∣ TOf p q b ∨ (p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))).card
        + good.card = carriers.card := by
    rw [hgood_eq]
    exact Finset.card_filter_add_card_filter_not _
  have hgood_card_ge : c₁ * Q - (17 + 8 * (Dc:ℝ)) ≤ (good.card:ℝ) := by
    have h1 : ((carriers.filter
        (fun b => b ∣ TOf p q b ∨ (p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))).card : ℝ)
        + (good.card:ℝ) = (carriers.card:ℝ) := by exact_mod_cast hgood_card_eq
    have h2 : ((carriers.filter
        (fun b => b ∣ TOf p q b ∨ (p ≠ 2 ∧ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b))).card : ℝ)
        ≤ 8 * (Dc:ℝ) + 16 := by exact_mod_cast hbadunion_card
    linarith [hbase_card, hcarriers_card]
  -- each fibre of mOf on `good` has size ≤ 4
  have hfibre : ∀ m : ℕ, (good.filter (fun b => mOf p q b = m)).card ≤ 4 := by
    intro m
    have hsub : good.filter (fun b => mOf p q b = m) ⊆ carriers.filter (fun b => mOf p q b = m) :=
      Finset.filter_subset_filter _ (by rw [hgooddef]; exact Finset.filter_subset _ _)
    exact le_trans (Finset.card_le_card hsub) (carriers_per_m_le_four hp hα hDc16 hqDc3 carriers hcar m)
  set M' : Finset ℕ := good.image (mOf p q) with hM'def
  have hM'_card : (good.card:ℝ) ≤ 4 * (M'.card:ℝ) := by
    have h1 : good.card = ∑ m ∈ M', (good.filter (fun b => mOf p q b = m)).card := by
      rw [hM'def]; exact Finset.card_eq_sum_card_image (mOf p q) good
    have h2 : ∑ m ∈ M', (good.filter (fun b => mOf p q b = m)).card ≤ ∑ _m ∈ M', 4 :=
      Finset.sum_le_sum (fun m _ => hfibre m)
    have h3 : ∑ _m ∈ M', (4:ℕ) = M'.card * 4 := by
      rw [Finset.sum_const, smul_eq_mul]
    have h4 : good.card ≤ 4 * M'.card := by omega
    exact_mod_cast h4
  -- keep the larger half of M'
  set L : ℕ := M'.card / 2 with hLdef
  set M : Finset ℕ := M'.filter (fun m => L ≤ m) with hMdef
  have hMcompl_le : (M'.filter (fun m => ¬ L ≤ m)).card ≤ L := by
    have hsub : M'.filter (fun m => ¬ L ≤ m) ⊆ Finset.range L := by
      intro m hm
      have h2 := (Finset.mem_filter.mp hm).2
      simp only [not_le] at h2
      exact Finset.mem_range.mpr h2
    calc (M'.filter (fun m => ¬ L ≤ m)).card ≤ (Finset.range L).card := Finset.card_le_card hsub
      _ = L := Finset.card_range L
  have hMM'_eq : M.card + (M'.filter (fun m => ¬ L ≤ m)).card = M'.card := by
    rw [hMdef]; exact Finset.card_filter_add_card_filter_not _
  have hM_card_ge : (M'.card:ℝ) / 2 ≤ (M.card:ℝ) := by
    have h1 : (L:ℝ) ≤ (M'.card:ℝ) / 2 := by
      have : 2 * L ≤ M'.card := by rw [hLdef]; omega
      have h2 : (2 * L : ℝ) ≤ (M'.card:ℝ) := by exact_mod_cast this
      linarith
    have h2 : M'.card ≤ M.card + L := by omega
    have h3 : (M'.card:ℝ) ≤ (M.card:ℝ) + (L:ℝ) := by exact_mod_cast h2
    linarith
  have hL_ge : (M'.card:ℝ) / 2 - 1 ≤ (L:ℝ) := by
    have := nat_div_cast_lower M'.card 2 (by norm_num)
    rw [← hLdef] at this
    linarith
  -- final numeric bounds
  have hM'_ge : (c₁ * Q - (17 + 8 * (Dc:ℝ))) / 4 ≤ (M'.card:ℝ) := by
    linarith [hgood_card_ge, hM'_card]
  have hM_ge : (c₁ * Q - (17 + 8 * (Dc:ℝ))) / 8 ≤ (M.card:ℝ) := by
    linarith [hM'_ge, hM_card_ge]
  have hL_ge2 : (c₁ * Q - (17 + 8 * (Dc:ℝ))) / 8 - 1 ≤ (L:ℝ) := by
    linarith [hM'_ge, hL_ge]
  have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁
  have hKeq : c₁ * K = 2 * (17 + 8 * (Dc:ℝ)) + 16 := by
    rw [hKdef]; field_simp
  have hKc₁ : c₁ * K ≤ c₁ * Q := mul_le_mul_of_nonneg_left hqK hc₁.le
  have hCQ_ge : 2 * (17 + 8 * (Dc:ℝ)) + 16 ≤ c₁ * Q := by rw [← hKeq]; exact hKc₁
  have heqc0 : c₀ * Q = c₁ * Q / 16 := by rw [hc₀def]; ring
  have hM_final : c₀ * Q ≤ (M.card:ℝ) := by
    rw [heqc0]; linarith [hM_ge, hCQ_ge]
  have hL_final : c₀ * Q ≤ (L:ℝ) := by
    rw [heqc0]; linarith [hL_ge2, hCQ_ge]
  -- extract a lower endpoint function from witnesses
  have hMsubM' : M ⊆ M' := by rw [hMdef]; exact Finset.filter_subset _ _
  have hex : ∀ m ∈ M, ∃ b ∈ good, mOf p q b = m := by
    intro m hm
    have hm' : m ∈ M' := hMsubM' hm
    rw [hM'def] at hm'
    exact Finset.mem_image.mp hm'
  let lo : ℕ → ℕ := fun m =>
    if h : ∃ b ∈ good, mOf p q b = m then loOf p q h.choose else 0
  refine ⟨M, lo, ?_, ?_⟩
  · have heqQ : c₀ * (q:ℝ) / Real.log (q:ℝ) = c₀ * Q := by
      rw [hQdef]; exact mul_div_assoc c₀ (q:ℝ) (Real.log (q:ℝ))
    rw [heqQ]; exact hM_final
  · intro m hm
    have heqQ : c₀ * (q:ℝ) / Real.log (q:ℝ) = c₀ * Q := by
      rw [hQdef]; exact mul_div_assoc c₀ (q:ℝ) (Real.log (q:ℝ))
    have hex_m := hex m hm
    obtain ⟨hbgood, hbeq⟩ := hex_m.choose_spec
    have hlo_eq : lo m = loOf p q hex_m.choose := dite_eq_left hex_m
    set b : ℕ := hex_m.choose with hbdef
    have hbcar : b ∈ carriers := by
      rw [hgooddef, Finset.mem_filter] at hbgood
      exact hbgood.1
    obtain ⟨hbPrime, hbne, hb1, hb2⟩ := hcar b hbcar
    have hbgood' : ¬ b ∣ TOf p q b ∧ (p ≠ 2 → ¬ 2 ^ (Nat.log 2 q - 2) ∣ TOf p q b) := by
      rw [hgooddef, Finset.mem_filter] at hbgood
      exact hbgood.2
    obtain ⟨h1, h2, h3, h4, _h5, _h6, _h7, _h8, h9, _h10⟩ :=
      carrier_props hp hα hDc16 hqDc3 hbPrime hbne hb1 hb2
    have hps := good_carrier_powersmooth hp hα hDc16 hqDc3 hbPrime hbne hb1 hb2 hbgood'.1 hbgood'.2
    have hLm : L ≤ m := (Finset.mem_filter.mp hm).2
    rw [hbeq] at h2 h3 h4 h9 hps
    rw [← hlo_eq] at h4 h9 hps
    refine ⟨?_, ?_, h3, h4, hps, h9⟩
    · rw [heqQ]
      have hLmR : (L:ℝ) ≤ (m:ℝ) := by exact_mod_cast hLm
      linarith [hL_final, hLmR]
    · exact h2

end Erdos289.CLT
