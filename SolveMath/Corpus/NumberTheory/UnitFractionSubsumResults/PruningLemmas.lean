module

public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.GoodProperties

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

lemma pruning_lemma_one_prec (A : Finset ℕ) (ε : ℝ) (i : ℕ) :
    ∃ A_i ⊆ A, ∃ Q_i ⊆ ppowers_in_set A,
      Disjoint Q_i (ppowers_in_set A_i) ∧
      ((rec_sum A : ℝ) - ε * rec_sum Q_i ≤ rec_sum A_i) ∧
      (i ≤ (A \ A_i).card ∨ ∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) := by
  induction i with
  | zero =>
      exact ⟨A, Finset.Subset.rfl, ∅, by simp⟩
  | succ i ih =>
      obtain ⟨A', hA', Q', hQ', hQA', hr, hi⟩ := ih
      by_cases hq : ∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q
      · exact ⟨A', hA', Q', hQ', hQA', hr, Or.inr hq⟩
      · have hq_neg := hq
        push Not at hq
        obtain ⟨q', hq', h4⟩ := hq
        have hq'zero : q' ≠ 0 := ne_of_mem_of_not_mem hq' zero_not_mem_ppowers_in_set
        have hq'zero' : (q' : ℚ) ≠ 0 := by
          exact_mod_cast hq'zero
        let A'' := A'.filter fun n ↦ ¬ (q' ∣ n ∧ Nat.Coprime q' (n / q'))
        let Q'' := insert q' Q'
        have hq'' : q' ∉ Q' := by
          rw [Finset.disjoint_left] at hQA'
          exact fun hmem ↦ hQA' hmem hq'
        refine ⟨A'', (Finset.filter_subset _ _).trans hA', Q'', ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (ppowers_in_set_subset hA' hq') hQ'
        · refine Finset.disjoint_insert_left.2 ⟨?_, ?_⟩
          · intro hmem
            rcases (mem_ppowers_in_set.mp hmem).2 with ⟨x, hx⟩
            rcases (mem_local_part (A := A'') (q := q') x).mp hx with ⟨hxA'', hxdvd, hxcop⟩
            exact (Finset.mem_filter.mp hxA'').2 ⟨hxdvd, hxcop⟩
          · exact hQA'.mono_right (ppowers_in_set_subset (Finset.filter_subset _ _))
        · have hrs : (rec_sum Q'' : ℝ) = rec_sum Q' + 1 / (q' : ℝ) := by
            have hrsQ : rec_sum Q'' = rec_sum Q' + (1 : ℚ) / q' := by
              simp [Q'', rec_sum, hq'', add_comm]
            simpa [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
              congrArg (fun x : ℚ ↦ (x : ℝ)) hrsQ
          have hsplit : Disjoint (local_part A' q') A'' := by
            rw [Finset.disjoint_left]
            intro n hnlocal hnA''
            rcases (mem_local_part (A := A') (q := q') n).mp hnlocal with ⟨_, hndvd, hncop⟩
            exact (Finset.mem_filter.mp hnA'').2 ⟨hndvd, hncop⟩
          have hunion : local_part A' q' ∪ A'' = A' := by
            ext n
            constructor
            · intro hn
              rcases Finset.mem_union.mp hn with hn | hn
              · exact (mem_local_part (A := A') (q := q') n).mp hn |>.1
              · exact (Finset.mem_filter.mp hn).1
            · intro hnA
              by_cases hp : q' ∣ n ∧ Nat.Coprime q' (n / q')
              · exact Finset.mem_union.mpr <| Or.inl <|
                  (mem_local_part (A := A') (q := q') n).2 ⟨hnA, hp.1, hp.2⟩
              · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hnA, hp⟩
          have hlocaleq : rec_sum_local A' q' / q' = rec_sum (local_part A' q') := by
            rw [rec_sum_local, rec_sum, Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hn0 : n = 0
            · simp [hn0]
            · field_simp [hn0, hq'zero']
          have hrs2a : rec_sum A'' + rec_sum_local A' q' / q' = rec_sum A' := by
            calc
              rec_sum A'' + rec_sum_local A' q' / q' =
                  rec_sum A'' + rec_sum (local_part A' q') := by
                rw [hlocaleq]
              _ = rec_sum (local_part A' q' ∪ A'') := by
                rw [add_comm, ← rec_sum_disjoint hsplit]
              _ = rec_sum A' := by
                rw [hunion]
          have hrs2a_real : (rec_sum A'' : ℝ) + rec_sum_local A' q' / (q' : ℝ) = rec_sum A' := by
            exact_mod_cast hrs2a
          have hrs3 : (rec_sum A' : ℝ) ≤ rec_sum A'' + ε * (1 / (q' : ℝ)) := by
            rw [← hrs2a_real, div_eq_mul_one_div]
            have hqnonneg : 0 ≤ (q' : ℝ) := by
              exact_mod_cast Nat.zero_le q'
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_right h4 <| one_div_nonneg.mpr hqnonneg) (rec_sum A'' : ℝ)
          have hmain : (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) ≤ rec_sum A'' := by
            linarith [hr, hrs3]
          have hrewrite :
              (rec_sum A : ℝ) - ε * rec_sum Q'' =
                (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) := by
            rw [hrs]
            ring
          rw [hrewrite]
          exact hmain
        · left
          rw [Nat.succ_le_iff]
          refine (hi.resolve_right hq_neg).trans_lt ?_
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset
            (Finset.sdiff_subset_sdiff Finset.Subset.rfl (Finset.filter_subset _ _))]
          simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors,
            and_assoc] at hq'
          obtain ⟨x, hx₁, hx₂, hx₃, -, hx₅⟩ := hq'
          refine ⟨x, ?_⟩
          simp [hx₁, hx₂, hx₅, hA' hx₁]

lemma pruning_lemma_one :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ ε : ℝ, 0 < ε →
      ∃ B ⊆ A,
        ((rec_sum A : ℝ) - ε * 2 * log (log N) ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [explicit_mertens] with N hN A hA ε hε
  obtain ⟨B, hB, Q, hQ, haux, h_recsums, h_local⟩ := pruning_lemma_one_prec A ε (A.card + 1)
  refine ⟨B, hB, ?_, ?_⟩
  · have hQu : Q ⊆ (Finset.range (N + 1)).filter IsPrimePow := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_range]
      have hqA : q ∈ ppowers_in_set A := hQ hq
      simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter] at hqA
      obtain ⟨a, ha, hqa, hq', hq''⟩ := hqA
      exact ⟨(Nat.divisor_le hqa).trans_lt (Finset.mem_range.mp (hA ha)), hq'⟩
    have hQt :
        (rec_sum Q : ℝ) ≤
          ((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) := by
      simp only [rec_sum, Rat.cast_sum, one_div, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hQu (by simp)
    nlinarith
  · rcases h_local with hcard | hlocal
    · exfalso
      rw [Nat.succ_le_iff] at hcard
      exact not_lt_of_ge (Finset.card_le_card Finset.sdiff_subset) hcard
    · exact hlocal

lemma pruning_lemma_two_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 4 * ε * log (log N) < α → (∀ n ∈ A, M ≤ ↑n) →
      α ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A q) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A,
          (α - 1 / M ≤ rec_sum A_i) ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (i ≤ (A \ A_i).card ∨ (rec_sum A_i : ℝ) < α) := by
  filter_upwards [pruning_lemma_one] with N hN M α ε A hA hM hMN hε hεα hMA hrec hsmooth i
  induction i with
  | zero =>
      refine ⟨A, Finset.Subset.rfl, ?_, ?_, Or.inl zero_le⟩
      · exact (sub_le_self _ (by simp only [hM.le, one_div, inv_nonneg])).trans hrec
      · intro q hq
        exact (hsmooth _ hq).2
  | succ i ih =>
      obtain ⟨A_i, hA_i, ih1, ih2, ih3⟩ := ih
      by_cases hr : (rec_sum A_i : ℝ) < α
      · exact ⟨A_i, hA_i, ih1, ih2, Or.inr hr⟩
      · have hA_ir : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        let ε' := 2 * ε
        obtain ⟨B, hB, hN1, hN2⟩ := hN A_i hA_ir ε' (mul_pos zero_lt_two hε)
        have ht0 : α ≤ rec_sum A_i := not_lt.mp hr
        have hBexists : B.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          simp only [rec_sum_empty, Rat.cast_zero, sub_nonpos] at hN1
          have ht1 : 4 * ε * log (log N) < ε' * 2 * log (log N) := by
            exact hεα.trans_le (ht0.trans hN1)
          rw [mul_right_comm 2 ε] at ht1
          linarith only [ht1]
        rcases hBexists with ⟨x, hx⟩
        have hxA1 : x ∈ A_i := hB hx
        have hxA2 : x ∈ A := hA_i hxA1
        let A_i' := A_i.erase x
        have h3 : A_i' ⊆ A_i := Finset.erase_subset _ _
        refine ⟨A_i', h3.trans hA_i, ?_, ?_, ?_⟩
        · have hrs2 : (rec_sum A_i : ℝ) - 1 / x = rec_sum A_i' := by
            simp only [A_i', rec_sum, sub_eq_iff_eq_add, Rat.cast_sum, one_div, Rat.cast_inv,
              Rat.cast_natCast, Finset.sum_erase_add _ _ hxA1]
          linarith only [ht0, one_div_le_one_div_of_le hM (hMA x (hA_i (hB hx))), hrs2]
        · intro q hq
          by_cases hxq : q ∣ x ∧ Nat.Coprime q (x / q)
          · have hlocalpart : local_part A_i' q = (local_part A_i q).erase x := by
              exact Finset.filter_erase _ _ _
            have hlocal : rec_sum_local A_i q = rec_sum_local A_i' q + q / x := by
              rw [rec_sum_local, rec_sum_local, hlocalpart, Finset.sum_erase_add]
              rw [local_part, Finset.mem_filter]
              exact ⟨hB hx, hxq⟩
            have hlocal2 : rec_sum_local A_i q - q / x = rec_sum_local A_i' q := by
              rwa [sub_eq_iff_eq_add]
            rw [← hlocal2]
            push_cast
            have hppB : q ∈ ppowers_in_set B := by
              rw [ppowers_in_set, Finset.mem_biUnion]
              refine ⟨x, hx, Finset.mem_filter.2 ?_⟩
              refine ⟨Nat.mem_divisors.2 ⟨hxq.1, ?_⟩, (mem_ppowers_in_set.1 hq).1, hxq.2⟩
              rintro rfl
              exact not_le_of_gt hM (by simpa only [Nat.cast_zero] using hMA _ hxA2)
            have hlocal3 : (rec_sum_local B q : ℝ) ≤ rec_sum_local A_i q :=
              Rat.cast_le.2 (rec_sum_local_mono hB)
            have hll : ε + ε < rec_sum_local A_i q := by
              rw [← two_mul ε]
              exact (hN2 q hppB).trans_le hlocal3
            have hll2 : (q : ℝ) / x ≤ ε := by
              rw [div_le_iff₀ (hM.trans_le (hMA x hxA2))]
              have hppA : ppowers_in_set A_i' ⊆ ppowers_in_set A :=
                ppowers_in_set_subset (h3.trans hA_i)
              exact (hsmooth q (hppA hq)).1.trans (mul_le_mul_of_nonneg_left (hMA x hxA2) hε.le)
            rw [lt_sub_iff_add_lt]
            linarith
          · have hrecl : rec_sum_local A_i q = rec_sum_local A_i' q := by
              have hlocalaux : local_part A_i q = local_part A_i' q := by
                ext n
                by_cases hnx : n = x
                · subst hnx
                  simp [A_i', local_part, hxA1, hxq]
                · simp [A_i', local_part, hnx]
              rw [rec_sum_local, rec_sum_local, hlocalaux]
            rw [← hrecl]
            exact ih2 q (ppowers_in_set_subset h3 hq)
        · left
          have hcard : (A \ A_i).card < (A \ A_i').card := by
            rw [Finset.card_sdiff_of_subset hA_i, Finset.card_sdiff_of_subset (h3.trans hA_i),
              tsub_lt_tsub_iff_left_of_le (Finset.card_le_card hA_i)]
            exact Finset.card_erase_lt_of_mem hxA1
          have hcard' : (A \ A_i).card + 1 ≤ (A \ A_i').card := Nat.succ_le_iff.2 hcard
          cases ih3 with
          | inl hf1 =>
              linarith
          | inr hf2 =>
              exfalso
              linarith

lemma pruning_lemma_two :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → ε > 0 → 4 * ε * log (log N) < α →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      α + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      ∃ B ⊆ A,
        ((rec_sum B : ℝ) < α) ∧
        (α - 1 / M ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [pruning_lemma_one, pruning_lemma_two_ind] with
    N h₁ h₂ M α ε A hA hM hMN hε hεα hMA hrec hsmooth
  obtain ⟨A', hA', hA'₁, hA'₃⟩ := h₁ A hA ε hε
  have hA'range : A' ⊆ Finset.range (N + 1) := hA'.trans hA
  have hMA' : ∀ n ∈ A', M ≤ (n : ℝ) := fun n hn => hMA n (hA' hn)
  have hrecA' : α ≤ rec_sum A' := by
    have hA'₁' : ((rec_sum A : ℝ) - 2 * ε * log (log N) ≤ rec_sum A') := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hA'₁
    nlinarith
  have hsmooth' : ∀ q ∈ ppowers_in_set A', (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A' q := by
    intro q hq
    exact ⟨hsmooth q (ppowers_in_set_subset hA' hq), hA'₃ q hq⟩
  let i := A'.card + 1
  obtain ⟨B, hB, hB₁, hB₂, hB₃⟩ := h₂ M α ε A' hA'range hM hMN hε hεα hMA' hrecA' hsmooth' i
  refine ⟨B, hB.trans hA', ?_, hB₁, hB₂⟩
  refine hB₃.resolve_left ?_
  dsimp [i]
  intro hcard
  exact not_le_of_gt (Nat.lt_succ_self A'.card)
    (hcard.trans (Finset.card_le_card Finset.sdiff_subset))

lemma main_tech_lemma_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → w < 2 * M → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / w ^ 2 →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ (d : ℝ) ≤ w ∧ d ∣ n) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A, ∃ d_i : ℕ,
          y ≤ d_i ∧ d_i ≤ ⌈y⌉₊ + i ∧ d_i ≤ ⌊w⌋₊ ∧
          rec_sum A_i < 2 / d_i ∧ (2 : ℝ) / d_i - 1 / M ≤ rec_sum A_i ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (∀ n ∈ A_i, ∀ k, k ∣ n → k < d_i → (k : ℝ) < y) ∧
          ((∃ n ∈ A_i, d_i ∣ n) ∨
            (∀ n ∈ A_i, ∀ k, k ∣ n → k ≤ ⌈y⌉₊ + i → k ≤ ⌊w⌋₊ → (k : ℝ) < y)) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [pruning_lemma_two, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw2 hNw hMA hrec hsmooth hdiv i
  have hy01 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hy12 : 2 ≤ y + 1 := by linarith
  have hceil_lt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy01.le
  have hwzero : 0 < w := lt_of_lt_of_le zero_lt_two h2w
  have hfloor_le : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
  have hεNaux : 4 * ε * log (log N) < 2 * (3 * ε * log (log N)) := by
    nlinarith [hε, hloglog_pos]
  have hεNaux2 : 2 * (3 * ε * log (log N)) ≤ 2 * (2 / w ^ 2) := by
    nlinarith [hNw]
  have hwaux : 2 * w ≤ w ^ 2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right h2w hwzero.le
  induction i with
  | zero =>
      let α : ℚ := 2 / ⌈y⌉₊
      have hαaux : (α : ℝ) = 2 / ⌈y⌉₊ := by
        simp [α]
      have hceil_le_w : (⌈y⌉₊ : ℝ) ≤ w := (Nat.cast_le.mpr hyw2).trans hfloor_le
      have hceil_pos : 0 < (⌈y⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_pos.mpr hy01
      have hα : 4 * ε * log (log N) < α := by
        have hα1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / ⌈y⌉₊ := by
          have hα1' : (4 : ℝ) / w ^ 2 ≤ 2 / ⌈y⌉₊ := by
            refine (div_le_div_iff₀ (by positivity) hceil_pos).2 ?_
            nlinarith [hceil_le_w, hwaux]
          simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hα1'
        rw [hαaux]
        exact hεNaux.trans_le (hεNaux2.trans hα1)
      have hrec2 : (α : ℝ) + 2 * ε * log (log N) ≤ rec_sum A := by
        rw [hαaux]
        have hdivaux : (2 : ℝ) / ⌈y⌉₊ ≤ 2 / y :=
          div_le_div_of_nonneg_left zero_le_two hy01 (Nat.le_ceil y)
        linarith
      obtain ⟨B, hB, hB', hB'', hN'⟩ := hN M α ε A hA hM hMN hε hα hMA hrec2 hsmooth
      refine ⟨B, hB, ⌈y⌉₊, ?_, Nat.le_refl _, hyw2, ?_, ?_, hN', ?_, ?_⟩
      · exact Nat.le_ceil y
      · exact_mod_cast hB'
      · simpa [hαaux] using hB''
      · intro n hn k hk1 hk2
        exact Nat.lt_ceil.mp hk2
      · refine or_iff_not_imp_left.2 ?_
        intro hp n hn k hk1 hk2 hk3
        have hklt : k < ⌈y⌉₊ := by
          refine lt_of_le_of_ne hk2 ?_
          intro hk
          apply hp
          exact ⟨n, hn, hk ▸ hk1⟩
        exact Nat.lt_ceil.mp hklt
  | succ i ih =>
      rcases ih with ⟨A_i, hA_i, d_i, hyi, hdiy, hdiw, hrec_lt, hrec_ge, hsmooth_i, hsmall, hfinal⟩
      by_cases hdiv2 : ∃ n ∈ A_i, d_i ∣ n
      · exact ⟨A_i, hA_i, d_i, hyi, hdiy.trans (Nat.le_succ _), hdiw, hrec_lt, hrec_ge,
          hsmooth_i, hsmall, Or.inl hdiv2⟩
      · let dNext := min (⌈y⌉₊ + i + 1) ⌊w⌋₊
        have hdNext : d_i + 1 ≤ dNext := by
          change d_i + 1 ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
          rw [le_min_iff]
          refine ⟨Nat.succ_le_succ hdiy, ?_⟩
          refine lt_of_le_of_ne hdiw ?_
          intro hdEq
          have hA_in : A_i.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hAi
            have hrec_nonpos : (rec_sum A_i : ℝ) ≤ 0 := by
              simp [hAi]
            have hlower : (2 : ℝ) / d_i - 1 / M ≤ 0 := le_trans hrec_ge hrec_nonpos
            have hdipos : 0 < (d_i : ℝ) := hy01.trans_le hyi
            have hdi_le_w : (d_i : ℝ) ≤ w := (Nat.cast_le.mpr hdiw).trans hfloor_le
            have hMw' : 2 * M ≤ w := by
              have hMd : 2 * M ≤ (d_i : ℝ) := by
                have hlower' := hlower
                field_simp [hdipos.ne', hM.ne'] at hlower'
                nlinarith
              linarith
            exact (not_lt_of_ge hMw') hMw
          obtain ⟨x, hx⟩ := hA_in
          obtain ⟨d, hd1, hd2, hd3⟩ := hdiv x (hA_i hx)
          have hdle : d ≤ ⌊w⌋₊ := Nat.le_floor hd2
          have hdle' : d ≤ d_i := by simpa [hdEq] using hdle
          have hlt : d < d_i := by
            refine lt_of_le_of_ne hdle' ?_
            intro hdEq'
            apply hdiv2
            exact ⟨x, hx, hdEq' ▸ hd3⟩
          exact (not_le_of_gt (hsmall x hx d hd3 hlt)) hd1
        let αNext : ℚ := 2 / dNext
        have hαNextaux : (αNext : ℝ) = 2 / (dNext : ℝ) := by
          simp [αNext]
        have hdNext_le_floor : dNext ≤ ⌊w⌋₊ := by
          simp [dNext]
        have hdNext_le_w : (dNext : ℝ) ≤ w := (Nat.cast_le.mpr hdNext_le_floor).trans hfloor_le
        have hdipos_real : 0 < (d_i : ℝ) := hy01.trans_le hyi
        have hdipos_nat : 0 < d_i := Nat.cast_pos.mp hdipos_real
        have hOneLt_dNext : (1 : ℝ) < dNext := by
          exact_mod_cast lt_of_lt_of_le (Nat.succ_lt_succ hdipos_nat) hdNext
        have hαNext : 4 * ε * log (log N) < αNext := by
          have hαNext1' : (4 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) := by
            refine (div_le_div_iff₀ (by positivity) (zero_lt_one.trans hOneLt_dNext)).2 ?_
            nlinarith [hdNext_le_w, hwaux]
          have hαNext1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / (dNext : ℝ) := by
            simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hαNext1'
          rw [hαNextaux]
          exact hεNaux.trans_le (hεNaux2.trans hαNext1)
        have hrec2 : (αNext : ℝ) + 2 * ε * log (log N) ≤ rec_sum A_i := by
          rw [hαNextaux]
          have hrec3p : (d_i : ℝ) ≤ (dNext : ℝ) - 1 := by
            have hdNext' : (d_i : ℝ) + 1 ≤ dNext := by exact_mod_cast hdNext
            linarith
          have hrec3 : (2 : ℝ) / ((dNext : ℝ) - 1) - 1 / M ≤ rec_sum A_i := by
            have hrec3' : (2 : ℝ) / ((dNext : ℝ) - 1) ≤ 2 / d_i :=
              div_le_div_of_nonneg_left zero_le_two hdipos_real hrec3p
            exact le_trans (sub_le_sub_right hrec3' _) hrec_ge
          have hrec5 : (2 : ℝ) / (dNext : ℝ) ^ 2 ≤ 2 / ((dNext : ℝ) - 1) - 2 / (dNext : ℝ) := by
            have hdNext_pos : 0 < (dNext : ℝ) := zero_lt_one.trans hOneLt_dNext
            have hsubpos : 0 < (dNext : ℝ) - 1 := sub_pos.mpr hOneLt_dNext
            field_simp [hdNext_pos.ne', hsubpos.ne']
            nlinarith
          have hrec6 : (2 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_left zero_le_two (by positivity) ?_
            nlinarith [hdNext_le_w, hwzero]
          linarith [hMN2, hNw, hrec3, hrec5, hrec6]
        have hA_i' : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        have hMA' : ∀ n ∈ A_i, M ≤ (n : ℝ) := fun n hn => hMA n (hA_i hn)
        have hsmooth' : ∀ q ∈ ppowers_in_set A_i, (q : ℝ) ≤ ε * M := by
          intro q hq
          exact hsmooth q (ppowers_in_set_subset hA_i hq)
        obtain ⟨B, hB, hBlt, hBge, hBsm⟩ :=
          hN M αNext ε A_i hA_i' hM hMN hε hαNext hMA' hrec2 hsmooth'
        refine ⟨B, hB.trans hA_i, dNext, ?_, ?_, hdNext_le_floor, ?_, ?_, hBsm, ?_, ?_⟩
        · exact hyi.trans (Nat.cast_le.mpr <| (Nat.le_succ _).trans hdNext)
        · simp [dNext]
        · exact_mod_cast hBlt
        · simpa [hαNextaux] using hBge
        · intro n hn k hk1 hk2
          have hn2 : n ∈ A_i := hB hn
          cases hfinal with
          | inl h =>
              exfalso
              exact hdiv2 h
          | inr hnew2 =>
              have hk2' : k ≤ ⌈y⌉₊ + i := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact Nat.le_of_lt_succ hk2.1
              have hk2'' : k ≤ ⌊w⌋₊ := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact le_of_lt hk2.2
              exact hnew2 n hn2 k hk1 hk2' hk2''
        · by_cases hdNextDiv : ∃ n ∈ B, dNext ∣ n
          · exact Or.inl hdNextDiv
          · right
            intro n hn k hk1 hk2 hk3
            have hn2 : n ∈ A_i := hB hn
            cases hfinal with
            | inl h =>
                exfalso
                exact hdiv2 h
            | inr hnew2 =>
                have hk2' : k ≤ dNext := by
                  change k ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
                  rw [le_min_iff]
                  exact ⟨hk2, hk3⟩
                have hk2'' : k < dNext := by
                  refine lt_of_le_of_ne hk2' ?_
                  intro hkEq
                  apply hdNextDiv
                  exact ⟨n, hn, hkEq ▸ hk1⟩
                have hk2''' : k ≤ ⌈y⌉₊ + i := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact Nat.le_of_lt_succ hk2''.1
                have hk2'''' : k ≤ ⌊w⌋₊ := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact le_of_lt hk2''.2
                exact hnew2 n hn2 k hk1 hk2''' hk2''''

lemma main_tech_lemma :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 2 * M > w → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / (w ^ 2) →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ w) ∧ d ∣ n) →
      ∃ A' ⊆ A, ∃ d : ℕ,
        A' ≠ ∅ ∧ y ≤ d ∧ ((d : ℝ) ≤ w) ∧ rec_sum A' < 2 / d ∧
        (2 : ℝ) / d - 1 / M ≤ rec_sum A' ∧
        (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q) ∧
        (∃ n ∈ A', d ∣ n) ∧
        (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k : ℝ) < y) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [main_tech_lemma_ind, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv
  have hy01 : 0 < y := by
    exact lt_of_lt_of_le zero_lt_one hy
  have hwzero : 0 < w := by
    exact lt_of_lt_of_le zero_lt_two h2w
  let i := ⌊w⌋₊ - ⌈y⌉₊
  specialize hN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv i
  rcases hN with ⟨A', hA', d, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  refine ⟨A', hA', d, ?_⟩
  have hdw : (d : ℝ) ≤ w := by
    have hfloorw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
    have hdfloor : (d : ℝ) ≤ (⌊w⌋₊ : ℝ) := by
      exact_mod_cast hd3
    exact hdfloor.trans hfloorw
  have hA'ne : A' ≠ ∅ := by
    intro hA'em
    have hreczero : rec_sum A' = 0 := by
      simp [hA'em, rec_sum]
    have hlow : (2 : ℝ) / d - 1 / M ≤ 0 := by
      rw [hreczero] at hd5
      simpa using hd5
    have haux1 : (2 : ℝ) / d ≤ 1 / M := by
      exact sub_nonpos.mp hlow
    have haux2 : (2 : ℝ) / w ≤ 2 / d := by
      refine div_le_div_of_nonneg_left zero_le_two ?_ ?_
      · exact hy01.trans_le hd1
      · exact hdw
    have haux3 : (2 : ℝ) / w ^ 2 ≤ 2 / w := by
      field_simp [hwzero.ne']
      nlinarith [h2w, hwzero]
    have haux4 : 3 * ε * log (log N) < ε * log (log N) := by
      exact lt_of_le_of_lt hNw <| lt_of_le_of_lt haux3 <| lt_of_le_of_lt haux2 <|
        lt_of_le_of_lt haux1 hMN2
    have hthree_lt_one : (3 : ℝ) < 1 := by
      nlinarith [haux4, hε, hloglog_pos]
    linarith
  refine ⟨hA'ne, hd1, hdw, hd4, hd5, hd6, ?_, hd7⟩
  · cases hd8 with
    | inl h =>
        exact h
    | inr h =>
        exfalso
        have hAexists : ∃ x : ℕ, x ∈ A' := by
          by_contra h
          apply hA'ne
          apply Finset.not_nonempty_iff_eq_empty.mp
          simpa [Finset.Nonempty] using h
        rcases hAexists with ⟨x, hx⟩
        have hxA : x ∈ A := hA' hx
        rcases hdiv x hxA with ⟨m, hm1, hm2, hm3⟩
        have htempw : m ≤ ⌊w⌋₊ := Nat.le_floor hm2
        have htemp : m ≤ ⌈y⌉₊ + i := by
          have hobvious : ⌈y⌉₊ + i = ⌊w⌋₊ := by
            dsimp [i]
            exact Nat.add_sub_of_le hyw
          rw [hobvious]
          exact htempw
        have := h x hx m hm3 htemp htempw
        linarith

end UnitFractions
