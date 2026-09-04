module

public import SolveMath.Corpus.NumberTheory.UnitFractionSubsumResults.Basic

@[expose] public section

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter _root_.Finset Real
open _root_.Finset

lemma force_good_properties_two_values_case
    (N : ℕ) (M c : ℝ) (A A_I E : Finset ℕ) (I : Finset ℤ) (x1 x2 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (h0A : 0 ∉ A)
    (h0M : 0 < M)
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ))
    (hrecA : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A)
    (hlarge0 : 0 < log N)
    (hlarge5 :
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6)
    (hlarge3 : 0 < log (log N))
    (hnum : (502 / 500 : ℝ) - c ≤ 2 / 3)
    (hzI : ¬ (0 : ℤ) ∈ I)
    (hP :
      ↑(((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
          fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card) <
        M / log N)
    (hnoB :
      ¬ ∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))
    (hdiv :
      ∀ n : ℕ,
        n ≤ N ^ 2 →
          (ArithmeticFunction.sigma 0 n : ℝ) ≤
            N ^ (2 * log 2 / log (log (N : ℝ)) * (1 + 1 / 3)))
    (hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N)
    (hA_I : A_I = A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x)
    (hE :
      E =
        (ppowers_in_set A).filter
          (fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q))
    (hf :
      ∀ q ∈ E,
        f q ∈ I ∧
          ((q : ℤ) ∣ f q) ∧
            c * log (log N) ≤
              ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f q).sum
                (fun r : ℕ => (1 / r : ℝ)))
    (hx1E : x1 ∈ E)
    (hx2E : x2 ∈ E)
    (hclose12 : |(f x2 : ℝ) - f x1| ≤ N)
    (htwoxs : f x2 ≠ f x1)
    (hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2) :
    (x2 : ℤ) ∣ f x1 := by
  classical
  exfalso
  let A1 := A.filter fun n : ℕ => (n : ℤ) ∣ f x1
  let A2 := A.filter fun n : ℕ => (n : ℤ) ∣ f x2
  let A0 := A \ (A1 ∪ A2)
  have hf1 := hf x1 hx1E
  have hf2 := hf x2 hx2E
  have h3rec : rec_sum A ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
    refine le_trans ?_ rec_sum_le_three
    refine rec_sum_mono ?_
    intro n hn
    rw [Finset.mem_union]
    by_cases htemp : n ∈ A1 ∪ A2
    · exact Or.inl htemp
    · exact Or.inr <| Finset.mem_sdiff.mpr ⟨hn, htemp⟩
  by_cases hAlarge : rec_sum A ≤ 3 * rec_sum A1 ∨ rec_sum A ≤ 3 * rec_sum A2
  · apply hnoB
    let P1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
    let P2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
    let P12 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1 ∧ (n : ℤ) ∣ f x2
    have hrecAs :
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) ≤
          (502 / 500 : ℝ) * log (log N) := by
      have hunion :
          P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
        dsimp [P1, P2, P12]
        have h :=
          (Finset.sum_union_inter
            (s₁ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1)
            (s₂ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2)
            (f := fun q : ℕ => (1 : ℝ) / q)).symm
        simpa [Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
          and_left_comm, and_right_comm, and_assoc, add_comm, add_left_comm, add_assoc] using h
      have hunion_subset : P1 ∪ P2 ⊆ ppowers_in_set A := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq | hq
        · exact Finset.mem_of_mem_filter _ hq
        · exact Finset.mem_of_mem_filter _ hq
      calc
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := hunion
        _ ≤ (ppower_rec_sum A : ℝ) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
              rw [add_le_add_iff_right, ppower_rec_sum]
              push_cast
              exact Finset.sum_le_sum_of_subset_of_nonneg hunion_subset fun i _ _ => by
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (ppower_rec_sum A : ℝ) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_left]
              refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) htwoxs hclose12))
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro r hr
                rw [Finset.mem_filter] at hr
                rw [Finset.mem_filter]
                rw [ppowers_in_set, Finset.mem_biUnion] at hr
                rcases hr.1 with ⟨m, hmA, hmq⟩
                rw [Finset.mem_filter, Nat.mem_divisors] at hmq
                refine ⟨?_, hmq.2.1, hr.2.2, hr.2.1⟩
                rw [Finset.mem_range]
                exact lt_of_le_of_lt
                  (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
                  (by
                    rw [← Finset.mem_range]
                    exact hA hmA)
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (501 / 500 : ℝ) * log (log N) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_right]
              exact hsum4
        _ = (502 / 500 : ℝ) * log (log N) := by
              ring_nf
    rcases hAlarge with hA1large | hA2large
    · refine ⟨A1, Finset.filter_subset _ _, hA1large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A1).sum fun q : ℕ => (1 : ℝ) / q) ≤ P1.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A1) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A1]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf2.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
    · refine ⟨A2, Finset.filter_subset _ _, hA2large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A2).sum fun q : ℕ => (1 : ℝ) / q) ≤ P2.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A2) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A2]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le, add_comm]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf1.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
  · let A' := A0.filter fun n : ℕ => n ∈ A_I ∧ ∀ q ∈ ppowers_in_set A0, n ∈ local_part A_I q → q ∈ E
    have hP' : ((A \ A_I).card : ℝ) < M / log N := by
      let F : Finset ℤ := (A.image fun n : ℕ => (n : ℤ)).filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x
      have hsubset : (A \ A_I).image (fun n : ℕ => (n : ℤ)) ⊆ F := by
        intro z hz
        rw [Finset.mem_image] at hz
        rcases hz with ⟨n, hn, rfl⟩
        rw [Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨n, (Finset.mem_sdiff.mp hn).1, rfl⟩, ?_⟩
        intro x hx hnx
        apply (Finset.mem_sdiff.mp hn).2
        rw [hA_I, Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.mp hn).1, ⟨x, hx, hnx⟩⟩
      have hcardle : (((A \ A_I).image (fun n : ℕ => (n : ℤ))).card : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hcardeq : ((A \ A_I).image (fun n : ℕ => (n : ℤ))).card = (A \ A_I).card := by
        exact Finset.card_image_of_injective _ Nat.cast_injective
      have hF :
          F =
            ((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
              fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x) := by
        ext z
        simp [F, Finset.mem_image]
      have hPstd : (F.card : ℝ) < M / log N := by
        rw [hF]
        exact hP
      exact lt_of_le_of_lt (by simpa [hcardeq] using hcardle) hPstd
    have hrecaux' : 1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤
            1 / log N + (((ppowers_in_set A0) \ E).sum fun q => (rec_sum_local A_I q) / q) := by
              rw [add_le_add_iff_left]
              norm_cast
              refine rec_sum_split A0 A_I A' E ?_ ?_
              · intro hzA
                apply h0A
                rw [hA_I] at hzA
                exact Finset.mem_of_mem_filter 0 hzA
              · rfl
        _ ≤
            1 / log N +
              (1 / (2 * log N ^ ((1 : ℝ) / 100))) *
                (((ppowers_in_set A0) \ E).sum fun q => (1 : ℝ) / q) := by
              norm_cast
              rw [add_le_add_iff_left, Rat.cast_sum, Finset.mul_sum]
              simp_rw [Rat.cast_div, Rat.cast_natCast]
              refine Finset.sum_le_sum ?_
              intro q hq
              have hle : (rec_sum_local A_I q : ℝ) ≤ 1 / (2 * log N ^ ((1 : ℝ) / 100)) := by
                rw [← not_lt]
                intro nlt
                rw [Finset.mem_sdiff] at hq
                apply hq.2
                rw [hE, Finset.mem_filter]
                refine ⟨(ppowers_in_set_subset Finset.sdiff_subset) hq.1,
                  le_of_lt nlt⟩
              exact
                (by
                  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                    (mul_le_mul_of_nonneg_right hle
                      (inv_nonneg.mpr (Nat.cast_nonneg q))))
        _ ≤ 1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) := by
              rw [add_le_add_iff_left]
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · refine le_trans ?_ hsum4
                rw [ppower_rec_sum]
                push_cast
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
                · exact Finset.sdiff_subset.trans
                    (ppowers_in_set_subset Finset.sdiff_subset)
                · intro i _ _
                  rw [one_div_nonneg]
                  exact Nat.cast_nonneg i
              · positivity
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hlarge5
    have hrecA0 : (log N) ^ (-(1 / 101 : ℝ)) / 3 ≤ rec_sum A0 := by
      have hAlarge1 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A1) := by
        intro h
        apply hAlarge
        exact Or.inl (by exact_mod_cast h)
      have hAlarge2 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A2) := by
        intro h
        apply hAlarge
        exact Or.inr (by exact_mod_cast h)
      have hA1small : (rec_sum A1 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA1small
        apply hAlarge1
        nlinarith
      have hA2small : (rec_sum A2 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA2small
        apply hAlarge2
        nlinarith
      have hA0big : (rec_sum A : ℝ) / 3 ≤ rec_sum A0 := by
        have h3rec' : (rec_sum A : ℝ) ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
          exact_mod_cast h3rec
        by_contra hA0big
        have hA0small : (rec_sum A0 : ℝ) < rec_sum A / 3 := lt_of_not_ge hA0big
        nlinarith [h3rec', hA1small, hA2small, hA0small]
      nlinarith [hrecA, hA0big]
    have hrecaux : (rec_sum (A0 \ A') : ℝ) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        (rec_sum (A0 \ A') : ℝ) = rec_sum ((A0 \ A') \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          norm_cast
          rw [← rec_sum_disjoint (Finset.disjoint_sdiff_inter _ _),
            Finset.sdiff_union_inter]
        _ ≤ rec_sum (A \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          norm_cast
          refine rec_sum_mono ?_
          intro n hn
          rw [Finset.mem_sdiff] at hn ⊢
          have hnA0 : n ∈ A0 := (Finset.mem_sdiff.mp hn.1).1
          have hnA : n ∈ A := by
            dsimp [A0] at hnA0
            exact (Finset.mem_sdiff.mp hnA0).1
          exact ⟨hnA, hn.2⟩
        _ ≤ ((A \ A_I).card : ℝ) / M + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          exact rec_sum_le_card_div h0M fun n hn => hMA n (Finset.mem_sdiff.mp hn).1
        _ ≤ 1 / log N + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          have htmp : ((A \ A_I).card : ℝ) / M < 1 / log N := by
            rw [_root_.div_lt_iff₀ h0M]
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hP'
          exact le_of_lt htmp
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hrecaux'
    have hrecA' : (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤ rec_sum A' := by
      calc
        (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤
            (log N) ^ (-(1 / 101 : ℝ)) / 3 - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          nlinarith
        _ ≤ (rec_sum A0 : ℝ) - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          rw [sub_le_sub_iff_right]
          exact hrecA0
        _ ≤ (rec_sum A0 : ℝ) - rec_sum (A0 \ A') := by
          rw [sub_le_sub_iff_left]
          exact hrecaux
        _ = rec_sum A' := by
          rw [sub_eq_iff_eq_add]
          norm_cast
          rw [← rec_sum_disjoint, Finset.union_sdiff_of_subset]
          · exact Finset.filter_subset _ _
          · exact Finset.disjoint_sdiff
    have hA'size : M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) ≤ A'.card := by
      have htmp : (rec_sum A' : ℝ) ≤ A'.card / M := by
        refine rec_sum_le_card_div h0M ?_
        intro n hn
        have hnA0 : n ∈ A0 := (Finset.mem_filter.mp hn).1
        have hnA : n ∈ A := by
          dsimp [A0] at hnA0
          exact (Finset.mem_sdiff.mp hnA0).1
        exact hMA n hnA
      have htmp' : ((log N) ^ (-(1 / 101 : ℝ)) / 6) * M ≤ (A'.card : ℝ) := by
        exact (_root_.le_div_iff₀ h0M).mp (hrecA'.trans htmp)
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp'
    have hIne : I.Nonempty := ⟨f x1, hf1.1⟩
    have hbadx :
        ∃ x ∈ I,
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
            (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card := by
      by_contra h
      rw [← not_lt] at hA'size
      apply hA'size
      have hA'union : A' = I.biUnion fun x : ℤ => A'.filter fun n : ℕ => (n : ℤ) ∣ x := by
        ext a
        constructor
        · intro hn
          have hn' := hn
          rw [Finset.mem_filter, hA_I, Finset.mem_filter] at hn
          rcases hn.2.1.2 with ⟨x, hx1, hx2⟩
          rw [Finset.mem_biUnion]
          exact ⟨x, hx1, by
            rw [Finset.mem_filter]
            exact ⟨hn', hx2⟩⟩
        · intro hn
          rw [Finset.mem_biUnion] at hn
          rcases hn with ⟨x, hx1, hx2⟩
          exact Finset.mem_of_mem_filter a hx2
      rw [hA'union]
      refine
        lt_of_lt_of_le
          (card_bUnion_lt_card_mul_real
            (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ)) ?_ hIne)
          ?_
      · intro x hx
        rw [← not_le]
        intro hnle
        apply h
        exact ⟨x, hx, hnle⟩
      · rw [show ((I.card : ℝ) * (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))) =
            M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) by
            field_simp [show (I.card : ℝ) ≠ 0 by
              exact_mod_cast (Finset.card_ne_zero.mpr hIne)]]
    rcases hbadx with ⟨x, hx1, hx2⟩
    let m := Nat.gcd (Int.natAbs x) (Int.natAbs (f x1 * f x2))
    have hmsmall : m ≤ N ^ 2 := by
      have hbadx' : ∃ n ∈ A', (n : ℤ) ∣ x := by
        have hA'temp : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).Nonempty := by
          rw [← Finset.card_pos, Nat.pos_iff_ne_zero]
          intro hz
          rw [hz] at hx2
          have hpos : 0 < M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
            refine div_pos ?_ ?_
            · refine mul_pos h0M ?_
              refine div_pos ?_ ?_
              · exact Real.rpow_pos_of_pos hlarge0 _
              · norm_num1
            · exact_mod_cast (Finset.card_pos.mpr hIne)
          linarith
        rcases hA'temp with ⟨n, hn⟩
        rw [Finset.mem_filter] at hn
        exact ⟨n, hn.1, hn.2⟩
      rcases hbadx' with ⟨ns, hns1, hns2⟩
      rw [Finset.mem_filter] at hns1
      have hns3 := hns1.1
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hns3
      rw [not_or] at hns3
      refine le_trans (nat_gcd_prod_le_diff ?_ ?_) ?_
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.1 ⟨hns3.1, hns2⟩
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.2 ⟨hns3.1, hns2⟩
      · rw [sq]
        refine Nat.mul_le_mul ?_ ?_
        · exact hIclose x hx1 (f x1) hf1.1
        · exact hIclose x hx1 (f x2) hf2.1
    have hdivm : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card ≤ ArithmeticFunction.sigma 0 m := by
      rw [ArithmeticFunction.sigma_zero_apply]
      refine Finset.card_le_card ?_
      intro n hn
      rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [dvd_iff_ppowers_dvd' n m]
        · intro q hq1 hq2
          rw [Nat.dvd_gcd_iff]
          rcases Finset.mem_filter.mp hn with ⟨hnA', hnx⟩
          rcases Finset.mem_filter.mp hnA' with ⟨hnA0, hnAI, hprop⟩
          refine ⟨?_, ?_⟩
          · have hqx : (q : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.mpr hq1) hnx
            exact Int.natCast_dvd.mp <| by
              simpa using Int.dvd_natAbs.mpr hqx
          · have hqE : q ∈ E := by
              have hnA : n ∈ A := by
                dsimp [A0] at hnA0
                exact (Finset.mem_sdiff.mp hnA0).1
              have hn0 : n ≠ 0 := by
                intro hnz
                apply h0A
                simpa [hnz] using hnA
              exact hprop q (by
                rw [ppowers_in_set, Finset.mem_biUnion]
                refine ⟨n, hnA0, ?_⟩
                rw [Finset.mem_filter, Nat.mem_divisors]
                exact ⟨⟨hq1, hn0⟩, hq2.1, hq2.2⟩) (by
                rw [local_part, Finset.mem_filter]
                exact ⟨hnAI, hq1, hq2.2⟩)
            have hfq := hf q hqE
            rcases hthreexs q hqE with hqfx1 | hqfx2
            · have hqx1 : (q : ℤ) ∣ f x1 := by simpa [hqfx1] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x1) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx1
              simpa [Int.natAbs_mul] using dvd_mul_of_dvd_left hqabs (Int.natAbs (f x2))
            · have hqx2 : (q : ℤ) ∣ f x2 := by simpa [hqfx2] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x2) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx2
              simpa [Int.natAbs_mul, Nat.mul_comm] using
                dvd_mul_of_dvd_right hqabs (Int.natAbs (f x1))
        · intro hnz
          apply h0A
          have hbah : A'.filter fun n : ℕ => (n : ℤ) ∣ x ⊆ A := by
            intro k hk
            have hkA' : k ∈ A' := (Finset.mem_filter.mp hk).1
            have hkA0 : k ∈ A0 := (Finset.mem_filter.mp hkA').1
            dsimp [A0] at hkA0
            exact (Finset.mem_sdiff.mp hkA0).1
          rw [hnz] at hn
          exact hbah hn
      · intro hmz
        rw [Nat.gcd_eq_zero_iff] at hmz
        have hmz' : x = 0 := by simpa using hmz.1
        rw [hmz'] at hx1
        exact hzI hx1
    specialize hdiv m hmsmall
    have hsigma_lt :
        (ArithmeticFunction.sigma 0 m : ℝ) <
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) :=
      lt_of_le_of_lt hdiv hlarge9
    have hsigma_ge :
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
          ArithmeticFunction.sigma 0 m := by
      exact le_trans hx2 (by exact_mod_cast hdivm)
    exact (not_lt_of_ge hsigma_ge) hsigma_lt

end UnitFractions
