import SolveMath.Corpus.NumberTheory.QuantitativeErdosTuran

namespace Erdos289.Ported

open QuantitativeErdosTuran

theorem erdos_turan_weak :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ), 0 < U → ∀ (N : ℕ) (x : Fin N → ZMod U) (H : ℕ), 0 < H →
      ∀ α ℓ : ℕ, α + ℓ ≤ U →
        |((Finset.univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card : ℝ)
              - (N : ℝ) * (ℓ : ℝ) / (U : ℝ)|
          ≤ C * ((N : ℝ) / Real.sqrt (H : ℝ)
              + ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
                  ‖∑ j, Complex.exp (2 * Real.pi * Complex.I * ((h * ((x j).val : ℤ) : ℤ) : ℂ) / (U : ℂ))‖) := by
  refine ⟨32, by norm_num, ?_⟩
  intro U hU N x H hH α ℓ hαℓ
  have : NeZero U := ⟨hU.ne'⟩
  classical
  -- Basic positivity facts.
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hH1 : 1 ≤ H := hH
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHR1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hsqrtHpos : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hHR
  have hsqrtH1 : (1 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    have hle := Real.sqrt_le_sqrt hHR1
    rwa [Real.sqrt_one] at hle
  set δ : ℝ := 1 / Real.sqrt (H : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos hsqrtHpos
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hsqrtHpos]; exact hsqrtH1
  -- The index set and the phase function.
  set s : Finset (Fin N) := Finset.univ with hsdef
  set phase : Fin N → ℝ := fun j => ((x j).val : ℝ) / (U : ℝ) with hphasedef
  have hscard : s.card = N := by rw [hsdef, Finset.card_univ, Fintype.card_fin]
  have hfract (j : Fin N) : Int.fract (phase j) = phase j := by
    apply Int.fract_eq_self.mpr
    refine ⟨by rw [hphasedef]; positivity, ?_⟩
    rw [hphasedef, div_lt_one hUR]
    exact_mod_cast (x j).val_lt
  -- Anchored counting sets `A k = #{ j : (x j).val < k }`.
  set A : ℕ → Finset (Fin N) := fun k => s.filter (fun j => (x j).val < k) with hAdef
  have hcount (k : ℕ) (hk : k ≤ U) :
      (s.filter fun j => Int.fract (phase j) < (k : ℝ) / (U : ℝ)) = A k := by
    rw [hAdef]
    apply Finset.filter_congr
    intro j _
    rw [hfract j, hphasedef]
    simp only
    rw [div_lt_div_iff_of_pos_right hUR]
    exact_mod_cast Iff.rfl
  -- The ported quantitative Erdős–Turán inequality, specialized to the anchored threshold `k / U`.
  have hmain (k : ℕ) (hk : k ≤ U) :
      |((A k).card : ℝ) - (k : ℝ) / (U : ℝ) * N| ≤
        (δ + 4 / (δ * H)) * N +
          ∑ h ∈ nonzeroFrequencyWindow H, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
    have hb0 : (0 : ℝ) ≤ (k : ℝ) / (U : ℝ) := by positivity
    have hb1 : (k : ℝ) / (U : ℝ) ≤ 1 := (div_le_one hUR).mpr (by exact_mod_cast hk)
    have hkey := erdosTuran_fract_count s phase H δ ((k : ℝ) / (U : ℝ)) hH1 hδpos hδ1 hb0 hb1
    rwa [hcount k hk, hscard] at hkey
  -- Inclusion-exclusion: the anchored residue interval count is a difference of two `A k`'s.
  have hle1 : α ≤ α + ℓ := Nat.le_add_right α ℓ
  have hle2 : α ≤ U := hle1.trans hαℓ
  have hsub : A α ⊆ A (α + ℓ) := by
    intro j hj
    rw [hAdef] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsdef] at hj ⊢
    omega
  have hset : (Finset.univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))) =
      A (α + ℓ) \ A α := by
    rw [hAdef]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_Ico,
      hsdef]
    omega
  have hcarddiff : ((Finset.univ.filter (fun j => (x j).val ∈ Finset.Ico α (α + ℓ))).card : ℝ) =
      ((A (α + ℓ)).card : ℝ) - ((A α).card : ℝ) := by
    have hinter : A α ∩ A (α + ℓ) = A α := Finset.inter_eq_left.mpr hsub
    rw [hset, Finset.card_sdiff, hinter]
    have : (A α).card ≤ (A (α + ℓ)).card := Finset.card_le_card hsub
    exact Nat.cast_sub this
  -- Note: the RHS uses `((α + ℓ : ℕ) : ℝ)` (a single cast of the `ℕ` sum), not `(α : ℝ) + (ℓ : ℝ)`,
  -- so that it is syntactically the same atom as the `↑(α + ℓ)` produced by `hmain (α + ℓ) hαℓ`
  -- below — otherwise `linarith` cannot see the two forms are equal.
  have hbdiff : (N : ℝ) * (ℓ : ℝ) / (U : ℝ) =
      ((α + ℓ : ℕ) : ℝ) / (U : ℝ) * N - (α : ℝ) / (U : ℝ) * N := by
    push_cast; ring
  -- Combine the two applications of `hmain`.
  have h1 := hmain (α + ℓ) hαℓ
  have h2 := hmain α hle2
  rw [abs_le] at h1 h2
  -- The window sum computation: fold `nonzeroFrequencyWindow H` into the target's natural sum.
  have hconj (h : ℤ) : exponentialSum s phase h = starRingEnd ℂ (exponentialSum s phase (-h)) := by
    simp only [exponentialSum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hfn : fourier (-(-h)) (phase i : UnitAddCircle) =
        starRingEnd ℂ (fourier (-h) (phase i : UnitAddCircle)) := fourier_neg
    rwa [neg_neg] at hfn
  have hnormeq (h : ℤ) : ‖exponentialSum s phase h‖ = ‖exponentialSum s phase (-h)‖ := by
    rw [hconj h, Complex.norm_conj]
  set negPart : Finset ℤ := Finset.Icc (-(H : ℤ)) (-1) with hnegdef
  set posPart : Finset ℤ := Finset.Icc (1 : ℤ) (H : ℤ) with hposdef
  have hunion : nonzeroFrequencyWindow H = negPart ∪ posPart := by
    rw [hnegdef, hposdef]
    ext h
    simp only [nonzeroFrequencyWindow, frequencyWindow, Finset.mem_erase, Finset.mem_Icc,
      Finset.mem_union]
    omega
  have hdisj : Disjoint negPart posPart := by
    rw [hnegdef, hposdef, Finset.disjoint_left]
    intro h h1' h2'
    simp only [Finset.mem_Icc] at h1' h2'
    omega
  have hpossum : ∑ n ∈ Finset.Icc (1 : ℕ) H, 8 / |((n : ℤ) : ℝ)| * ‖exponentialSum s phase (n : ℤ)‖
      = ∑ h ∈ posPart, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
    apply Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun h : ℤ => h.toNat)
    · intro n hn
      rw [hposdef]; simp only [Finset.mem_Icc] at hn ⊢; omega
    · intro h hh
      rw [hposdef] at hh; simp only [Finset.mem_Icc] at hh ⊢; omega
    · intro n _
      omega
    · intro h hh
      rw [hposdef] at hh; simp only [Finset.mem_Icc] at hh; omega
    · intro n _
      rfl
  have hnegsum : ∑ n ∈ Finset.Icc (1 : ℕ) H, 8 / |((n : ℤ) : ℝ)| * ‖exponentialSum s phase (-(n : ℤ))‖
      = ∑ h ∈ negPart, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖ := by
    apply Finset.sum_nbij' (fun n : ℕ => -(n : ℤ)) (fun h : ℤ => (-h).toNat)
    · intro n hn
      rw [hnegdef]; simp only [Finset.mem_Icc] at hn ⊢; omega
    · intro h hh
      rw [hnegdef] at hh; simp only [Finset.mem_Icc] at hh ⊢; omega
    · intro n _
      omega
    · intro h hh
      rw [hnegdef] at hh; simp only [Finset.mem_Icc] at hh; omega
    · intro n _
      simp [abs_neg]
  have hwindow : ∑ h ∈ nonzeroFrequencyWindow H, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖
      = 16 * ∑ n ∈ Finset.Icc (1 : ℕ) H, (1 : ℝ) / (n : ℝ) * ‖exponentialSum s phase (n : ℤ)‖ := by
    rw [hunion, Finset.sum_union hdisj, ← hpossum, ← hnegsum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have habsn : |((n : ℤ) : ℝ)| = (n : ℝ) := by
      have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
      rw [hcast, abs_of_pos hnR]
    rw [habsn, ← hnormeq (n : ℤ)]
    ring
  -- Character match: the ported `exponentialSum` at frequency `(n : ℤ)` equals the target sum.
  have hchar (n : ℕ) : exponentialSum s phase (n : ℤ) =
      ∑ j, Complex.exp (2 * Real.pi * Complex.I * ((n * ((x j).val : ℤ) : ℤ) : ℂ) / (U : ℂ)) := by
    simp only [exponentialSum, hsdef]
    apply Finset.sum_congr rfl
    intro j _
    rw [fourier_coe_apply]
    rw [hphasedef]
    congr 1
    push_cast
    ring
  have hwindow' : ∑ h ∈ nonzeroFrequencyWindow H, 8 / |(h : ℝ)| * ‖exponentialSum s phase h‖
      = 16 * ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
          ‖∑ j, Complex.exp (2 * Real.pi * Complex.I * ((h * ((x j).val : ℤ) : ℤ) : ℂ) / (U : ℂ))‖ := by
    rw [hwindow]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [hchar n]
  -- Coefficient bound: `2 (δ + 4/(δH)) ≤ 32 / √H`.
  have hprod : (1 / Real.sqrt (H : ℝ)) * (H : ℝ) = Real.sqrt (H : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hsqrtHpos.ne']
    exact (Real.mul_self_sqrt hHR.le).symm
  have hEq : δ + 4 / (δ * (H : ℝ)) = 5 / Real.sqrt (H : ℝ) := by
    rw [hδdef, hprod]
    ring
  -- Rewrite the coefficient `δ + 4/(δH)` in `h1`, `h2` down to `5 * (N / √H)`, so that every
  -- occurrence of the atom `N / √H` in the final goal and in `h1`, `h2` is syntactically the same
  -- term (avoids relying on `nlinarith`'s atom-matching to see through the `δ`, `H` product).
  have hringeq : (5 : ℝ) / Real.sqrt (H : ℝ) * (N : ℝ) = 5 * ((N : ℝ) / Real.sqrt (H : ℝ)) := by
    ring
  rw [hwindow'] at h1 h2
  rw [hEq, hringeq] at h1 h2
  -- Fold the two remaining transcendental atoms `N / √H` and the target sum into named local
  -- constants: `set` rewrites both the (still-original-shaped) goal and the existing hypotheses
  -- `h1`, `h2` at once, so afterwards every occurrence is literally the same local constant and
  -- `nlinarith` cannot fail to recognize them as equal atoms.
  set Q : ℝ := (N : ℝ) / Real.sqrt (H : ℝ) with hQdef
  set Tsum : ℝ := ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) *
      ‖∑ j, Complex.exp (2 * Real.pi * Complex.I * ((h * ((x j).val : ℤ) : ℤ) : ℂ) / (U : ℂ))‖
    with hTsumdef
  have hQnonneg : (0 : ℝ) ≤ Q := by rw [hQdef]; exact div_nonneg (Nat.cast_nonneg N) hsqrtHpos.le
  -- Assemble. (`rw [hsdef]` unfolds `s` back to `Finset.univ` in the goal so that the target's
  -- own `∑ j, ...` sum, never touched by the earlier `set s`, syntactically matches `h1`/`h2`.)
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rw [hsdef, abs_le, hcarddiff, hbdiff]
  constructor <;> linarith

end Erdos289.Ported
