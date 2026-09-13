import Erdos289CLT.Basic

/-!
# Realized families and the transfer step (paper §4, display (transfer))

A `Fam` records a set of configurations (the predicate `P`) together with:
its finite support `supp` (every interval of every configuration lies in it),
the fixed finite set `S` of admissible long intervals, the rational translate `β`,
the group level `n`, the count interval `[u, v]`, and a strict weight bound.
`realizes` says that every residue in `β + G_n` occurs at every count in `[u, v]`.

`transfer` is the elementary observation of §4: a new pool of pairs, separated
internally and from the support, whose `cover` part has subset sums covering
`G_{n'}/G_n`, enlarges the group level to `n'` and the count interval to
`[u + |cover|, v + |further|]` provided `v - u ≥ |cover|`.
-/

namespace Erdos289.CLT

open Finset

/-- A family realizing `(β + G_n) × [u, v]`. -/
structure Fam where
  P : Config → Prop
  supp : Finset Iv
  S : Finset Iv
  β : ℚ
  n : ℕ
  u : ℕ
  v : ℕ
  bound : ℚ
  mem_supp : ∀ C, P C → ∀ I ∈ C.F, I ∈ supp
  supp_len : ∀ I ∈ supp, ivLen I ≤ 4
  supp_long : ∀ I ∈ supp, ivLen I ≠ 2 → I ∈ S
  w_lt : ∀ C, P C → C.w < bound
  realizes : ∀ z : ℚ, InG n (z - β) → ∀ c : ℕ, u ≤ c → c ≤ v →
    ∃ C : Config, P C ∧ C.nu = c ∧ ∃ j : ℤ, C.w = z + j

/-- Adjoin a set of new pair-intervals to an old configuration. -/
private def unionConfig (C₀ : Config) (B pool : Finset Iv)
    (hB : ∀ I ∈ B, I ∈ pool)
    (hpair : ∀ I ∈ pool, 2 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hsep : ∀ I ∈ pool, ∀ J ∈ pool, I ≠ J → Iv.Sep I J)
    (hsep_old : ∀ I ∈ C₀.F, ∀ J ∈ pool, Iv.Sep I J) : Config where
  F := C₀.F ∪ B
  two_le := by
    intro I hI
    rcases Finset.mem_union.mp hI with h | h
    · exact C₀.two_le I h
    · exact (hpair I (hB I h)).1
  len_ge := by
    intro I hI
    rcases Finset.mem_union.mp hI with h | h
    · exact C₀.len_ge I h
    · have := (hpair I (hB I h)).2
      omega
  sep := by
    intro I hI J hJ hIJ
    rcases Finset.mem_union.mp hI with hI0 | hIB <;>
      rcases Finset.mem_union.mp hJ with hJ0 | hJB
    · exact C₀.sep I hI0 J hJ0 hIJ
    · exact hsep_old I hI0 J (hB J hJB)
    · exact (hsep_old J hJ0 I (hB I hIB)).symm
    · exact hsep I (hB I hIB) J (hB J hJB) hIJ

/-- The transfer step (paper §4). -/
theorem transfer (Fm : Fam) {n' : ℕ} (hn : Fm.n ≤ n') (cover further : Finset Iv)
    (hdisj : Disjoint cover further)
    (hpair : ∀ I ∈ cover ∪ further, 2 ≤ I.lo ∧ I.hi = I.lo + 1)
    (hsep : ∀ I ∈ cover ∪ further, ∀ J ∈ cover ∪ further, I ≠ J → Iv.Sep I J)
    (hsep_old : ∀ I ∈ Fm.supp, ∀ J ∈ cover ∪ further, Iv.Sep I J)
    (hG : ∀ J ∈ cover ∪ further, InG n' J.mass)
    (hcover : ∀ z : ℚ, InG n' z → ∃ Cs ⊆ cover, InG Fm.n (z - ∑ J ∈ Cs, J.mass))
    (hwidth : Fm.u + cover.card ≤ Fm.v) :
    ∃ Fm' : Fam, Fm'.β = Fm.β ∧ Fm'.n = n' ∧ Fm'.u = Fm.u + cover.card ∧
      Fm'.v = Fm.v + further.card ∧ Fm'.supp = Fm.supp ∪ (cover ∪ further) ∧
      Fm'.S = Fm.S ∧ Fm'.bound = Fm.bound + ∑ J ∈ cover ∪ further, J.mass := by
  let P' : Config → Prop := fun C => ∃ C₀ : Config, Fm.P C₀ ∧ ∃ A ⊆ further,
    ∃ Cs ⊆ cover, C.F = C₀.F ∪ (A ∪ Cs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  exact { P := P',
          supp := Fm.supp ∪ (cover ∪ further),
          S := Fm.S,
          β := Fm.β,
          n := n',
          u := Fm.u + cover.card,
          v := Fm.v + further.card,
          bound := Fm.bound + ∑ J ∈ cover ∪ further, J.mass,
          mem_supp := by
            intro C hC I hI
            obtain ⟨C₀, hP₀, A, hA, Cs, hCs, hF⟩ := hC
            rw [hF] at hI
            rcases Finset.mem_union.mp hI with hI0 | hIB
            · exact Finset.mem_union_left _ (Fm.mem_supp C₀ hP₀ I hI0)
            · rcases Finset.mem_union.mp hIB with hIA | hICs
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ (hA hIA))
              · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hCs hICs))
          supp_len := by
            intro I hI
            rcases Finset.mem_union.mp hI with hI0 | hIB
            · exact Fm.supp_len I hI0
            · have h := (hpair I hIB).2
              simp only [ivLen]
              omega
          supp_long := by
            intro I hI hlen
            rcases Finset.mem_union.mp hI with hI0 | hIB
            · exact Fm.supp_long I hI0 hlen
            · have h := (hpair I hIB).2
              simp only [ivLen] at hlen
              omega
          w_lt := by
            intro C hC
            obtain ⟨C₀, hP₀, A, hA, Cs, hCs, hF⟩ := hC
            have hlohi : ∀ I ∈ cover ∪ further, I.lo ≤ I.hi := by
              intro I hI
              have h := hpair I hI
              omega
            have hdisj0 : Disjoint C₀.F (A ∪ Cs) := by
              rw [Finset.disjoint_left]
              intro I hI0 hIB
              have hsupp : I ∈ Fm.supp := Fm.mem_supp C₀ hP₀ I hI0
              rcases Finset.mem_union.mp hIB with hIA | hICs
              · have hm : I ∈ cover ∪ further := Finset.mem_union_right cover (hA hIA)
                exact absurd rfl (Sep.ne (hsep_old I hsupp I hm) (hlohi I hm)
                  (hlohi I hm))
              · have hm : I ∈ cover ∪ further := Finset.mem_union_left further (hCs hICs)
                exact absurd rfl (Sep.ne (hsep_old I hsupp I hm) (hlohi I hm)
                  (hlohi I hm))
            have hAC : Disjoint A Cs := by
              have hdisjPool := hdisj
              rw [Finset.disjoint_left] at hdisjPool
              rw [Finset.disjoint_left]
              intro I hIA hICs
              exact hdisjPool (hCs hICs) (hA hIA)
            have hsum : C.w = C₀.w + ∑ J ∈ A, J.mass + ∑ J ∈ Cs, J.mass := by
              show ∑ J ∈ C.F, J.mass = _
              rw [hF, Finset.sum_union hdisj0, Finset.sum_union hAC]
              simp only [Config.w]
              ring
            have hsub : A ∪ Cs ⊆ cover ∪ further := Finset.union_subset
              (fun I hI => Finset.mem_union_right _ (hA hI))
              (fun I hI => Finset.mem_union_left _ (hCs hI))
            have hle : ∑ J ∈ A ∪ Cs, J.mass ≤ ∑ J ∈ cover ∪ further, J.mass :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ => mass_nonneg I
            have hC₀ := Fm.w_lt C₀ hP₀
            have hsplit : ∑ J ∈ A, J.mass + ∑ J ∈ Cs, J.mass ≤
                ∑ J ∈ cover ∪ further, J.mass := by
              rw [← Finset.sum_union hAC]
              exact hle
            rw [hsum]
            linarith
          realizes := by
            intro z hz c hc1 hc2
            have hrexists : ∃ r : ℕ, r ≤ further.card ∧
                Fm.u + cover.card ≤ c - r ∧ c - r ≤ Fm.v ∧
                c - r = min c Fm.v ∧ r ≤ c := by
              refine ⟨c - min c Fm.v, ?_, ?_, ?_, ?_, Nat.sub_le _ _⟩ <;> omega
            obtain ⟨r, hrle, hrlow, hrhigh, hcr, hrlec⟩ := hrexists
            obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hrle
            have hsumA : InG n' (∑ J ∈ A, J.mass) :=
              InG_sum A Iv.mass fun I hI =>
                hG I (Finset.mem_union_right cover (hA hI))
            have hcov : InG n' ((z - Fm.β) - ∑ J ∈ A, J.mass) :=
              hz.sub hsumA
            obtain ⟨Cs, hCs, hInGCs⟩ := hcover (z - Fm.β - ∑ J ∈ A, J.mass) hcov
            have hcscard : Cs.card ≤ cover.card := Finset.card_le_card hCs
            have hc0le : c - r - Cs.card ≤ Fm.v := by omega
            have hc0ge : Fm.u ≤ c - r - Cs.card := by omega
            obtain ⟨C₀, hC₀P, hC₀card, j, hC₀w⟩ :=
              Fm.realizes (z - ∑ J ∈ A, J.mass - ∑ J ∈ Cs, J.mass) (by
                have hEq : (z - ∑ J ∈ A, J.mass - ∑ J ∈ Cs, J.mass) - Fm.β =
                    (z - Fm.β - ∑ J ∈ A, J.mass) - ∑ J ∈ Cs, J.mass := by ring
                rw [hEq]
                exact hInGCs) (c - r - Cs.card) hc0ge hc0le
            have hAC : Disjoint A Cs := by
              have hdisjPool := hdisj
              rw [Finset.disjoint_left] at hdisjPool
              rw [Finset.disjoint_left]
              intro I hIA hICs
              exact hdisjPool (hCs hICs) (hA hIA)
            have hdisj0 : Disjoint C₀.F (A ∪ Cs) := by
              rw [Finset.disjoint_left]
              intro I hI0 hIB
              have hIB' : I ∈ cover ∪ further := by
                rcases Finset.mem_union.mp hIB with hIA | hICs
                · exact Finset.mem_union_right cover (hA hIA)
                · exact Finset.mem_union_left further (hCs hICs)
              have hsupp : I ∈ Fm.supp := Fm.mem_supp C₀ hC₀P I hI0
              have hlohi : I.lo ≤ I.hi := by
                have h := hpair I hIB'
                omega
              exact absurd rfl (Sep.ne (hsep_old I hsupp I hIB') hlohi hlohi)
            have hBpool : ∀ I ∈ A ∪ Cs, I ∈ cover ∪ further := fun I hI => by
              rcases Finset.mem_union.mp hI with hIA | hICs
              · exact Finset.mem_union_right cover (hA hIA)
              · exact Finset.mem_union_left further (hCs hICs)
            have hsep_old0 : ∀ I ∈ C₀.F, ∀ J ∈ cover ∪ further, Iv.Sep I J :=
              fun I hI J hJ => hsep_old I (Fm.mem_supp C₀ hC₀P I hI) J hJ
            have hrle_c : r ≤ c := hrlec
            have hC₀card' : C₀.F.card = c - r - Cs.card := hC₀card
            have hC₀w' : ∑ I ∈ C₀.F, I.mass =
                z - ∑ J ∈ A, J.mass - ∑ J ∈ Cs, J.mass + j := hC₀w
            let C := unionConfig C₀ (A ∪ Cs) (cover ∪ further) hBpool hpair hsep hsep_old0
            refine ⟨C, ⟨C₀, hC₀P, A, hA, Cs, hCs, rfl⟩, ?_, j, ?_⟩
            · show (C₀.F ∪ (A ∪ Cs)).card = c
              rw [Finset.card_union_of_disjoint hdisj0,
                Finset.card_union_of_disjoint hAC, hC₀card', hAcard]
              omega
            · show ∑ I ∈ (C₀.F ∪ (A ∪ Cs)), I.mass = z + j
              rw [Finset.sum_union hdisj0, Finset.sum_union hAC, hC₀w']
              ring
            }
  repeat rfl

end Erdos289.CLT
