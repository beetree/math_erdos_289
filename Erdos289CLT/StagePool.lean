import Erdos289CLT.Pairs
import Erdos289CLT.Subsets
import Erdos289CLT.Asymptotics

/-!
# Properties of a stage pool

Given the data of `pairs_lemma` at a prime power `q` and any `T ⊆ M`, the pool
`T.image (fun m => Iv.pair (lo m))` consists of pairs in the blocks of their centres,
with masses in `G_q`; distinct `m` give distinct centres; each centre `a` has
`q ∈ {lpp(a-1), lpp a, lpp(a+1)}`; and (paper, after Lemma 2) modulo `G_{q-1}` the
mass of the pair of `m` is `u/q` with `u = m⁻¹ (mod q)`, so by `subsets_lemma` any
`s(q)` of the pairs have subset sums covering `G_q/G_{q-1}`.
-/

namespace Erdos289.CLT

open Finset

/-- The pool pair of `m`. -/
def poolIv (lo : ℕ → ℕ) (m : ℕ) : Iv := Iv.pair (lo m)

/-- Multiplying an element of `G_n` by an integer stays in `G_n`. -/
theorem InG.int_mul {n : ℕ} (k : ℤ) {x : ℚ} (hx : InG n x) : InG n ((k : ℚ) * x) := by
  obtain ⟨c, hc⟩ := hx
  exact ⟨k * c, by rw [mul_assoc, hc]; push_cast; ring⟩

theorem stage_pool_props (q : ℕ) (hq : IsPrimePow q) (hq9 : 9 ≤ q)
    (M : Finset ℕ) (lo : ℕ → ℕ)
    (hM : ∀ m ∈ M, 1 ≤ m ∧ m < q ∧ Nat.Coprime m q ∧ (lo m = q * m ∨ lo m + 1 = q * m) ∧
      Powersmooth (q - 1) (companion q (lo m) m) ∧ 8 ∣ ctr q (lo m) m)
    (hsub : ∀ A : Finset ℕ, (∀ a ∈ A, a < q ∧ Nat.Coprime a q) →
      (q : ℝ) ^ ((3 : ℝ) / 4) ≤ A.card → ∀ b : ℕ, ∃ Cs ⊆ A, (∑ a ∈ Cs, a) ≡ b [MOD q])
    (T : Finset ℕ) (hT : T ⊆ M) :
    Set.InjOn (poolIv lo) T ∧
    (∀ m ∈ T, 8 ≤ (poolIv lo m).lo ∧ (poolIv lo m).hi = (poolIv lo m).lo + 1 ∧
      InG q (poolIv lo m).mass ∧
      ctr q (lo m) m ≤ (poolIv lo m).lo + 1 ∧ (poolIv lo m).hi ≤ ctr q (lo m) m + 2 ∧
      (lpp (ctr q (lo m) m - 1) = q ∨ lpp (ctr q (lo m) m) = q ∨
        lpp (ctr q (lo m) m + 1) = q)) ∧
    (∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → ctr q (lo m) m ≠ ctr q (lo m') m') ∧
    (∀ T' ⊆ T, s q ≤ T'.card → ∀ z : ℚ, InG q z →
      ∃ Cs ⊆ T'.image (poolIv lo), InG (q - 1) (z - ∑ J ∈ Cs, J.mass)) := by
  have hdata : ∀ m ∈ T, 1 ≤ m ∧ m < q ∧ Nat.Coprime m q ∧ (lo m = q * m ∨ lo m + 1 = q * m) ∧
      Powersmooth (q - 1) (companion q (lo m) m) ∧ 8 ∣ ctr q (lo m) m :=
    fun m hm => hM m (hT hm)
  obtain ⟨p, α, hp, hα, hpq⟩ := (isPrimePow_nat_iff q).mp hq
  -- `q * m ≥ q` for `m ∈ T`.
  have hqm_ge : ∀ m ∈ T, q ≤ q * m := by
    intro m hm
    obtain ⟨hm1, -, -, -, -, -⟩ := hdata m hm
    calc q = q * 1 := (mul_one q).symm
      _ ≤ q * m := Nat.mul_le_mul_left q hm1
  -- Distinct multiples of `q` are at least `q` apart.
  have hfar : ∀ a b : ℕ, a < b → q * a + q ≤ q * b := by
    intro a b hab
    have h1 : q * (a + 1) ≤ q * b := Nat.mul_le_mul_left q hab
    have h2 : q * (a + 1) = q * a + q := by ring
    omega
  have hlo_ge : ∀ m ∈ T, 8 ≤ lo m := by
    intro m hm
    obtain ⟨-, -, -, hlom, -, -⟩ := hdata m hm
    have hge := hqm_ge m hm
    omega
  -- `companion` equals whichever of `lo m, lo m + 1` is not `q * m`.
  have hcase : ∀ m ∈ T, (lo m = q * m ∧ companion q (lo m) m = lo m + 1) ∨
      (lo m + 1 = q * m ∧ companion q (lo m) m = lo m) := by
    intro m hm
    obtain ⟨-, -, -, hlom, -, -⟩ := hdata m hm
    rcases hlom with h | h
    · left; refine ⟨h, ?_⟩; unfold companion; omega
    · right; refine ⟨h, ?_⟩; unfold companion; omega
  have hcomp_pos : ∀ m ∈ T, 0 < companion q (lo m) m := by
    intro m hm
    have hge := hlo_ge m hm
    rcases hcase m hm with ⟨-, hc⟩ | ⟨-, hc⟩ <;> omega
  -- `ctr` is one of `lo m, lo m + 1`.
  have hctr_mem : ∀ m ∈ T, ctr q (lo m) m = lo m ∨ ctr q (lo m) m = lo m + 1 := by
    intro m hm
    have hc := hcase m hm
    unfold ctr
    split_ifs with hqe
    · rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; omega
      · right; omega
    · rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩
      · right; omega
      · left; omega
  -- `q * m` is `q`-powersmooth.
  have hqm_pow : ∀ m ∈ T, Powersmooth q (q * m) := by
    intro m hm
    obtain ⟨hm1, hmq, hcop, -, -, -⟩ := hdata m hm
    have hpdvd_q : p ∣ q := hpq ▸ dvd_pow_self p hα.ne'
    have hpm : ¬ p ∣ m := by
      intro hpdvd
      have hgcd1 : p ∣ Nat.gcd m q := Nat.dvd_gcd hpdvd hpdvd_q
      rw [hcop] at hgcd1
      exact hp.one_lt.ne' (Nat.dvd_one.mp hgcd1)
    have hmlt : m < p ^ α := hpq ▸ hmq
    have hres := powersmooth_mul_of_lt hp hα hmlt hpm hm1
    rwa [hpq] at hres
  have hqm_pos : ∀ m ∈ T, 0 < q * m := by
    intro m hm; have := hqm_ge m hm; omega
  have hlpp_qm : ∀ m ∈ T, lpp (q * m) = q := by
    intro m hm
    exact lpp_eq hq (dvd_mul_right q m) (hqm_pos m hm) (hqm_pow m hm)
  have h_qm_InG : ∀ m ∈ T, InG q (1 / ((q * m : ℕ) : ℚ)) := by
    intro m hm
    exact InG_one_div_of_powersmooth (hqm_pos m hm) (hqm_pow m hm)
  have h_comp_InG : ∀ m ∈ T, InG q (1 / ((companion q (lo m) m : ℕ) : ℚ)) := by
    intro m hm
    obtain ⟨-, -, -, -, hpow, -⟩ := hdata m hm
    exact (InG_one_div_of_powersmooth (hcomp_pos m hm) hpow).mono (by omega)
  have hmass_eq : ∀ m ∈ T, (poolIv lo m).mass =
      1 / ((q * m : ℕ) : ℚ) + 1 / ((companion q (lo m) m : ℕ) : ℚ) := by
    intro m hm
    show (Iv.pair (lo m)).mass = _
    rw [pair_mass]
    rcases hcase m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, ← h1]; push_cast; ring
    · rw [h2, ← h1]; push_cast; ring
  -- Part 1: `poolIv lo` is injective on `T`.
  have part1 : Set.InjOn (poolIv lo) T := by
    intro m hm m' hm' heq
    have hloeq : lo m = lo m' := congrArg Iv.lo heq
    obtain ⟨-, -, -, hlom, -, -⟩ := hdata m hm
    obtain ⟨-, -, -, hlom', -, -⟩ := hdata m' hm'
    rcases hlom with h1 | h1 <;> rcases hlom' with h2 | h2
    · exact Nat.eq_of_mul_eq_mul_left (by omega) (show q * m = q * m' by omega)
    · exfalso
      rcases lt_trichotomy m m' with hlt | heqm | hgt
      · have hf := hfar m m' hlt; omega
      · subst heqm; omega
      · have hf := hfar m' m hgt; omega
    · exfalso
      rcases lt_trichotomy m m' with hlt | heqm | hgt
      · have hf := hfar m m' hlt; omega
      · subst heqm; omega
      · have hf := hfar m' m hgt; omega
    · exact Nat.eq_of_mul_eq_mul_left (by omega) (show q * m = q * m' by omega)
  -- Part 2: per-`m` properties of the pool pair.
  have hlpp_ctr : ∀ m ∈ T, lpp (ctr q (lo m) m - 1) = q ∨ lpp (ctr q (lo m) m) = q ∨
      lpp (ctr q (lo m) m + 1) = q := by
    intro m hm
    have hl := hlpp_qm m hm
    rcases hcase m hm with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hctr_mem m hm with h3 | h3
    · right; left; have heq : ctr q (lo m) m = q * m := by omega
      rw [heq]; exact hl
    · left; have heq : ctr q (lo m) m - 1 = q * m := by omega
      rw [heq]; exact hl
    · right; right; have heq : ctr q (lo m) m + 1 = q * m := by omega
      rw [heq]; exact hl
    · right; left; have heq : ctr q (lo m) m = q * m := by omega
      rw [heq]; exact hl
  have part2 : ∀ m ∈ T, 8 ≤ (poolIv lo m).lo ∧ (poolIv lo m).hi = (poolIv lo m).lo + 1 ∧
      InG q (poolIv lo m).mass ∧
      ctr q (lo m) m ≤ (poolIv lo m).lo + 1 ∧ (poolIv lo m).hi ≤ ctr q (lo m) m + 2 ∧
      (lpp (ctr q (lo m) m - 1) = q ∨ lpp (ctr q (lo m) m) = q ∨
        lpp (ctr q (lo m) m + 1) = q) := by
    intro m hm
    have hlo8 : 8 ≤ (poolIv lo m).lo := hlo_ge m hm
    have hhi : (poolIv lo m).hi = (poolIv lo m).lo + 1 := rfl
    have hctr := hctr_mem m hm
    refine ⟨hlo8, hhi, ?_, ?_, ?_, hlpp_ctr m hm⟩
    · rw [show (poolIv lo m).mass = _ from hmass_eq m hm]
      exact (h_qm_InG m hm).add (h_comp_InG m hm)
    · show ctr q (lo m) m ≤ lo m + 1
      rcases hctr with h | h <;> omega
    · show lo m + 1 ≤ ctr q (lo m) m + 2
      rcases hctr with h | h <;> omega
  -- Part 3: distinct `m` in `T` give distinct centres.
  have part3 : ∀ m ∈ T, ∀ m' ∈ T, m ≠ m' → ctr q (lo m) m ≠ ctr q (lo m') m' := by
    intro m hm m' hm' hne heq
    have h1 : ctr q (lo m) m = q * m ∨ ctr q (lo m) m = q * m + 1 ∨
        ctr q (lo m) m + 1 = q * m := by
      rcases hcase m hm with ⟨hh1, -⟩ | ⟨hh1, -⟩ <;> rcases hctr_mem m hm with hh3 | hh3
      · left; omega
      · right; left; omega
      · right; right; omega
      · left; omega
    have h2 : ctr q (lo m') m' = q * m' ∨ ctr q (lo m') m' = q * m' + 1 ∨
        ctr q (lo m') m' + 1 = q * m' := by
      rcases hcase m' hm' with ⟨hh1, -⟩ | ⟨hh1, -⟩ <;> rcases hctr_mem m' hm' with hh3 | hh3
      · left; omega
      · right; left; omega
      · right; right; omega
      · left; omega
    rcases lt_trichotomy m m' with hlt | heqm | hgt
    · have hf := hfar m m' hlt; omega
    · exact hne heqm
    · have hf := hfar m' m hgt; omega
  -- Part 4: covering.
  have part4 : ∀ T' ⊆ T, s q ≤ T'.card → ∀ z : ℚ, InG q z →
      ∃ Cs ⊆ T'.image (poolIv lo), InG (q - 1) (z - ∑ J ∈ Cs, J.mass) := by
    intro T' hT'T hscard z hz
    have hq0 : 0 < q := by omega
    have : NeZero q := ⟨hq0.ne'⟩
    obtain ⟨j, hj⟩ := InG_step hq0 hz
    set u : ℕ → ℕ := fun m => ((m : ZMod q)⁻¹).val with hudef
    have hu_modeq : ∀ m ∈ T, u m * m ≡ 1 [MOD q] := by
      intro m hm
      obtain ⟨-, -, hcop, -, -, -⟩ := hdata m hm
      have h1 : ((u m : ZMod q)) * (m : ZMod q) = 1 := ZMod.val_inv_mul hcop
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      push_cast
      exact h1
    have hu_cop : ∀ m ∈ T, Nat.Coprime (u m) q := by
      intro m hm
      have h1 : (u m : ZMod q) * (m : ZMod q) = 1 := by
        have h2 := (ZMod.natCast_eq_natCast_iff (u m * m) 1 q).mpr (hu_modeq m hm)
        push_cast at h2; exact h2
      exact (ZMod.isUnit_iff_coprime (u m) q).mp (IsUnit.of_mul_eq_one _ h1)
    have hu_lt : ∀ m ∈ T, u m < q := fun m _ => ZMod.val_lt _
    have hu_inj : Set.InjOn u T' := by
      intro m hm m' hm' heq
      have hm1 := hT'T hm
      have hm'1 := hT'T hm'
      have h1 := hu_modeq m hm1
      have h2 := hu_modeq m' hm'1
      rw [heq] at h1
      have hcop := hu_cop m' hm'1
      have hgcd : Nat.gcd q (u m') = 1 := hcop.symm
      have hmm : m ≡ m' [MOD q] := Nat.ModEq.cancel_left_of_coprime hgcd (h1.trans h2.symm)
      have hltm := (hdata m hm1).2.1
      have hltm' := (hdata m' hm'1).2.1
      unfold Nat.ModEq at hmm
      rwa [Nat.mod_eq_of_lt hltm, Nat.mod_eq_of_lt hltm'] at hmm
    set A : Finset ℕ := T'.image u with hAdef
    have hAmem : ∀ a ∈ A, a < q ∧ Nat.Coprime a q := by
      intro a ha
      obtain ⟨m, hm, rfl⟩ := mem_image.mp ha
      exact ⟨hu_lt m (hT'T hm), hu_cop m (hT'T hm)⟩
    have hAcard : (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (A.card : ℝ) := by
      have h1 := rpow_le_s q
      have h2 : (s q : ℝ) ≤ (T'.card : ℝ) := by exact_mod_cast hscard
      have h3 : A.card = T'.card := by rw [hAdef]; exact Finset.card_image_of_injOn hu_inj
      rw [h3]; linarith
    set b : ℕ := (j % (q : ℤ)).toNat with hbdef
    obtain ⟨Cs', hCs'sub, hCs'sum⟩ := hsub A hAmem hAcard b
    set T'' : Finset ℕ := T'.filter (fun m => u m ∈ Cs') with hT''def
    have hT''subT' : T'' ⊆ T' := Finset.filter_subset _ _
    have hT''subT : T'' ⊆ T := hT''subT'.trans hT'T
    have hT''image : T''.image u = Cs' := by
      ext a
      simp only [hT''def, mem_image, mem_filter]
      constructor
      · rintro ⟨m, ⟨hmT, hmCs⟩, rfl⟩; exact hmCs
      · intro ha
        obtain ⟨m, hmT, rfl⟩ := mem_image.mp (hCs'sub ha)
        exact ⟨m, ⟨hmT, ha⟩, rfl⟩
    have hu_sum : (∑ m ∈ T'', u m : ℤ) = ∑ a ∈ Cs', (a : ℤ) := by
      have hsi := Finset.sum_image (f := (fun a : ℕ => (a : ℤ))) (g := u) (s := T'')
        (by intro x hx y hy hxy; exact hu_inj (hT''subT' hx) (hT''subT' hy) hxy)
      rw [hT''image] at hsi
      rw [← hsi]
    -- Cs is the image of T'' under poolIv lo.
    refine ⟨T''.image (poolIv lo), ?_, ?_⟩
    · exact Finset.image_subset_image hT''subT'
    · have hmass_sum : ∑ J ∈ T''.image (poolIv lo), J.mass = ∑ m ∈ T'', (poolIv lo m).mass := by
        exact Finset.sum_image (fun x hx y hy hxy => part1 (hT''subT hx) (hT''subT hy) hxy)
      rw [hmass_sum]
      have hmass_sum2 : ∑ m ∈ T'', (poolIv lo m).mass =
          ∑ m ∈ T'', (1 / ((q * m : ℕ) : ℚ) + 1 / ((companion q (lo m) m : ℕ) : ℚ)) :=
        Finset.sum_congr rfl (fun m hm => hmass_eq m (hT''subT hm))
      rw [hmass_sum2]
      -- term X1 : z - j/q
      have hX1 : InG (q - 1) (z - (j : ℚ) / q) := hj
      -- term X2 : j/q - ∑ u m / q
      have hX2 : InG (q - 1) ((j : ℚ) / q - ∑ m ∈ T'', (u m : ℚ) / q) := by
        set bb : ℕ := (j % (q : ℤ)).toNat with hbbdef
        have hbnn : 0 ≤ j % (q : ℤ) := Int.emod_nonneg j (by exact_mod_cast hq0.ne')
        have hbcast : (bb : ℤ) = j % (q : ℤ) := Int.toNat_of_nonneg hbnn
        have h1 : ((∑ a ∈ Cs', a : ℕ) : ℤ) ≡ (bb : ℤ) [ZMOD (q : ℤ)] :=
          Int.natCast_modEq_iff.mpr hCs'sum
        have h2 : (j : ℤ) ≡ (bb : ℤ) [ZMOD (q : ℤ)] := by
          rw [hbcast]; exact Int.ModEq.symm (Int.mod_modEq j q)
        have h3 : (j : ℤ) ≡ ((∑ a ∈ Cs', a : ℕ) : ℤ) [ZMOD (q : ℤ)] := h2.trans h1.symm
        obtain ⟨k, hk⟩ := h3.dvd
        have hcast : ((∑ a ∈ Cs', a : ℕ) : ℤ) = ∑ a ∈ Cs', (a : ℤ) := by push_cast; ring
        rw [hcast, ← hu_sum] at hk
        have heq : (j : ℚ) / q - ∑ m ∈ T'', (u m : ℚ) / q = ((-k : ℤ) : ℚ) := by
          rw [← Finset.sum_div]
          have hkQ : ((∑ m ∈ T'', u m : ℤ) : ℚ) - (j : ℚ) = (q : ℚ) * k := by exact_mod_cast hk
          have hsumQ : ((∑ m ∈ T'', u m : ℤ) : ℚ) = ∑ m ∈ T'', (u m : ℚ) := by push_cast; ring
          push_cast
          field_simp
          linarith [hkQ, hsumQ]
        rw [heq]
        exact InG_intCast (q - 1) (-k)
      -- term X3 : ∑ (u m / q - 1/(q m))
      have hX3 : InG (q - 1)
          (∑ m ∈ T'', ((u m : ℚ) / q - 1 / ((q * m : ℕ) : ℚ))) := by
        refine InG_sum T'' _ (fun m hm => ?_)
        have hmT := hT''subT hm
        obtain ⟨hm1, hmq, -, -, -, -⟩ := hdata m hmT
        have hmod := hu_modeq m hmT
        have h1 : ((u m * m : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD q] := Int.natCast_modEq_iff.mpr hmod
        push_cast at h1
        obtain ⟨c, hc⟩ := h1.dvd
        set k : ℤ := -c with hkdef
        have hk : (u m : ℤ) * m - 1 = k * q := by rw [hkdef]; linarith [hc]
        have hmdvd : m ∣ D (q - 1) := by
          unfold D Nat.lcmUpto
          exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hm1, by omega⟩)
        have hm_InG : InG (q - 1) (1 / (m : ℚ)) := (InG_one_div_iff hm1).2 hmdvd
        have heq : (u m : ℚ) / q - 1 / ((q * m : ℕ) : ℚ) = (k : ℚ) * (1 / (m : ℚ)) := by
          have hmQ : (m : ℚ) ≠ 0 := by positivity
          have hqQ : (q : ℚ) ≠ 0 := by positivity
          have hkQ : (u m : ℚ) * m - 1 = (k : ℚ) * q := by exact_mod_cast hk
          push_cast
          field_simp
          linarith [hkQ]
        rw [heq]
        exact InG.int_mul k hm_InG
      -- term X4 : ∑ 1/companion
      have hX4 : InG (q - 1) (∑ m ∈ T'', (1 / ((companion q (lo m) m : ℕ) : ℚ))) := by
        refine InG_sum T'' _ (fun m hm => ?_)
        have hmT := hT''subT hm
        obtain ⟨-, -, -, -, hpow, -⟩ := hdata m hmT
        exact InG_one_div_of_powersmooth (hcomp_pos m hmT) hpow
      have hcombine : z - ∑ m ∈ T'', (1 / ((q * m : ℕ) : ℚ) + 1 / ((companion q (lo m) m : ℕ) : ℚ)) =
          (z - (j : ℚ) / q) + ((j : ℚ) / q - ∑ m ∈ T'', (u m : ℚ) / q) +
          (∑ m ∈ T'', ((u m : ℚ) / q - 1 / ((q * m : ℕ) : ℚ))) -
          ∑ m ∈ T'', (1 / ((companion q (lo m) m : ℕ) : ℚ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring
      rw [hcombine]
      exact ((hX1.add hX2).add hX3).sub hX4
  exact ⟨part1, part2, part3, part4⟩

end Erdos289.CLT
