import ErdosProblems.Erdos186.CFP.IntegerHigherDimensionalFinal
import Erdos289.ExternalAxioms

/-!
# Bridge: the ported CFP structure theorem implies the audited CFHMPSV statement

This file transports `Erdos186.CFP.nonemptyIntegerTheorem15` (proved in the ported
development under `ErdosProblems.Erdos186.CFP`) into the exact shape of
`Erdos289.External.CFHMPSVStructureStatement` (the real-coordinate, fixed
`GAPRepresentation` encoding audited in `Erdos289/ExternalAxioms.lean`).

The two sides describe the same mathematical object at ambient dimension `1`:
`Erdos186.LatticePoint 1 = Fin 1 → ℤ` is canonically identified with `ℤ` via
evaluation at the unique coordinate (`proj`), and a `Symmetric` (centered)
one-dimensional `GAP` is re-presented as a `GAPRepresentation` by recording its
step vector and its radii as real lower/upper bounds.
-/

open Erdos186 Erdos186.CFP Erdos186.GAP Erdos289.External

namespace Erdos289.Ported

/-! ## The projection identifying `LatticePoint 1` with `ℤ` -/

/-- Evaluation at the unique coordinate of a one-dimensional lattice point. -/
def proj (x : LatticePoint 1) : ℤ := x 0

@[simp] lemma proj_integerPoint (a : ℤ) : proj (integerPoint a) = a := rfl

@[simp] lemma proj_zero : proj (0 : LatticePoint 1) = 0 := rfl

lemma integerPoint_proj (x : LatticePoint 1) : integerPoint (proj x) = x := by
  funext i
  simp [integerPoint, proj, Subsingleton.elim i 0]

/-- `proj` is a global bijection `LatticePoint 1 ≃ ℤ` (inverse `integerPoint`); in
particular it is injective everywhere, not just on some ambient finite set. -/
lemma proj_injective : Function.Injective proj := fun x y hxy => by
  rw [← integerPoint_proj x, ← integerPoint_proj y, hxy]

lemma proj_mem_of_mem_integerPoints {A : Finset ℤ} {x : LatticePoint 1}
    (hx : x ∈ integerPoints A) : proj x ∈ A := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  simpa using ha

/-- `Real.logb 2` and the audited `logTwo` are the same function by definition. -/
lemma logTwo_eq_logb (x : ℝ) : Erdos289.External.logTwo x = Real.logb 2 x := rfl

/-! ## Centered rank-`rho` progressions versus integer coefficient boxes -/

/-- The centered integer coefficient box with radii `radii`. -/
def intBox {rho : ℕ} (radii : Fin rho → ℕ) : Set (Fin rho → ℤ) :=
  {z | ∀ i, -(radii i : ℤ) ≤ z i ∧ z i ≤ (radii i : ℤ)}

lemma zero_mem_intBox {rho : ℕ} (radii : Fin rho → ℕ) :
    (0 : Fin rho → ℤ) ∈ intBox radii := by
  intro i
  constructor <;> simp

/-- The coefficient tuple of a centered `GAP` recovered from a point of its
integer coefficient box. -/
def coordOfZ {rho : ℕ} (Q : GAP 1 rho) (radii : Fin rho → ℕ) (hQ : Q.Centered radii)
    (z : Fin rho → ℤ) (hz : z ∈ intBox radii) : Q.Coord :=
  fun i => ⟨(z i + radii i).toNat, by
    have hnn : 0 ≤ z i + (radii i : ℤ) := by linarith [(hz i).1]
    have h3 := (hz i).2
    have h4 := hQ.width_eq i
    zify [hnn]
    omega⟩

lemma coordOfZ_spec {rho : ℕ} (Q : GAP 1 rho) (radii : Fin rho → ℕ) (hQ : Q.Centered radii)
    (z : Fin rho → ℤ) (hz : z ∈ intBox radii) (i : Fin rho) :
    ((coordOfZ Q radii hQ z hz i : ℕ) : ℤ) - radii i = z i := by
  have hnn : 0 ≤ z i + (radii i : ℤ) := by linarith [(hz i).1]
  show (((z i + radii i).toNat : ℕ) : ℤ) - radii i = z i
  rw [Int.toNat_of_nonneg hnn]; ring

/-- The image of a centered `GAP`'s carrier under evaluation at the unique
coordinate equals the image of its flat linear form on the integer
coefficient box. -/
lemma proj_image_centered {rho : ℕ} (Q : GAP 1 rho) (radii : Fin rho → ℕ)
    (hQ : Q.Centered radii) :
    proj '' (Q.carrier : Set (LatticePoint 1)) =
      (fun z : Fin rho → ℤ => ∑ i, z i * Q.steps i 0) '' intBox radii := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
    refine ⟨fun i => ((n i : ℕ) : ℤ) - radii i, ?_, ?_⟩
    · intro i
      dsimp only
      have h1 : (n i : ℕ) < Q.widths i := (n i).isLt
      have h2 := hQ.width_eq i
      omega
    · have h := congrFun (hQ.coordPoint_eq n) 0
      simpa [proj] using h.symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Q.coordPoint (coordOfZ Q radii hQ z hz), Q.coordPoint_mem_carrier _, ?_⟩
    have h := congrFun (hQ.coordPoint_eq (coordOfZ Q radii hQ z hz)) 0
    show (Q.coordPoint (coordOfZ Q radii hQ z hz)) 0 = ∑ i, z i * Q.steps i 0
    rw [h]
    exact Finset.sum_congr rfl (fun i _ => by rw [coordOfZ_spec Q radii hQ z hz i])

/-- A proper centered `GAP`'s flat linear form is injective on the integer
coefficient box. -/
lemma injOn_intBox {rho : ℕ} (Q : GAP 1 rho) (radii : Fin rho → ℕ)
    (hQ : Q.Centered radii) (hQP : Q.Proper) :
    Set.InjOn (fun z : Fin rho → ℤ => ∑ i, z i * Q.steps i 0) (intBox radii) := by
  intro z1 hz1 z2 hz2 heq
  set n1 := coordOfZ Q radii hQ z1 hz1 with hn1
  set n2 := coordOfZ Q radii hQ z2 hz2 with hn2
  have e1 : Q.coordPoint n1 0 = ∑ i, z1 i * Q.steps i 0 := by
    rw [congrFun (hQ.coordPoint_eq n1) 0]
    exact Finset.sum_congr rfl (fun i _ => by rw [coordOfZ_spec Q radii hQ z1 hz1 i])
  have e2 : Q.coordPoint n2 0 = ∑ i, z2 i * Q.steps i 0 := by
    rw [congrFun (hQ.coordPoint_eq n2) 0]
    exact Finset.sum_congr rfl (fun i _ => by rw [coordOfZ_spec Q radii hQ z2 hz2 i])
  have hp : proj (Q.coordPoint n1) = proj (Q.coordPoint n2) := by
    show Q.coordPoint n1 0 = Q.coordPoint n2 0
    rw [e1, e2]; exact heq
  have hcp : Q.coordPoint n1 = Q.coordPoint n2 := proj_injective hp
  have hnn : n1 = n2 := hQP hcp
  funext i
  have hii : coordOfZ Q radii hQ z1 hz1 i = coordOfZ Q radii hQ z2 hz2 i := congrFun hnn i
  rw [← coordOfZ_spec Q radii hQ z1 hz1 i, ← coordOfZ_spec Q radii hQ z2 hz2 i, hii]

/-! ## Isolated real-number bookkeeping

These are pure numeric lemmas with no reference to the ambient witness data,
kept separate so that `nlinarith` searches over a small, fixed set of
hypotheses instead of the large context accumulated inside the main proof. -/

/-- The base-two-logarithm threshold inequality survives shrinking the scale
constant from `scaleNum / scaleDen` down to `c`. -/
lemma threshold_bound (c s m scaleNum scaleDen L : ℝ) (hden : 0 < scaleDen) (hm : 1 ≤ m)
    (e1 : s * L ≤ c * m) (e2 : c * scaleDen ≤ scaleNum) :
    scaleDen * s * L ≤ scaleNum * m := by
  calc scaleDen * s * L = scaleDen * (s * L) := by ring
    _ ≤ scaleDen * (c * m) := mul_le_mul_of_nonneg_left e1 hden.le
    _ = (c * scaleDen) * m := by ring
    _ ≤ scaleNum * m := mul_le_mul_of_nonneg_right e2 (by linarith)

/-- The rational scale lower bound `scaleNum * s ≤ scaleDen * k` transports the
shrunk scale constant `c ≤ scaleNum / scaleDen` into `c * s ≤ k`. -/
lemma dilate_scale_bound (c s k scaleNum scaleDen : ℝ) (hden : 0 < scaleDen) (hs : 0 ≤ s)
    (e2 : c * scaleDen ≤ scaleNum) (hSL : scaleNum * s ≤ scaleDen * k) : c * s ≤ k := by
  have e3 : (c * s) * scaleDen ≤ k * scaleDen := by
    calc (c * s) * scaleDen = (c * scaleDen) * s := by ring
      _ ≤ scaleNum * s := mul_le_mul_of_nonneg_right e2 hs
      _ ≤ scaleDen * k := hSL
      _ = k * scaleDen := by ring
  exact le_of_mul_le_mul_right e3 hden

/-- The loss bound `loss ≤ lossConstant * s * L + 1` transports along
`c ≤ 1 / (lossConstant + 1)` into the form needed for the audited cardinality
bound, using only `s ≥ 1` and `L ≥ 1` to absorb the additive `1`. -/
lemma loss_final_bound (c s L loss lossConstant : ℝ) (hc : 0 < c) (hs1 : 1 ≤ s) (hL1 : 1 ≤ L)
    (hlc : 0 ≤ lossConstant) (hcLe : c ≤ 1 / (lossConstant + 1))
    (hloss : loss ≤ lossConstant * s * L + 1) :
    loss ≤ s * L / c := by
  have hprod1 : (1 : ℝ) ≤ s * L := by nlinarith [hs1, hL1]
  have hcLe' : lossConstant + 1 ≤ 1 / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact (le_div_iff₀ (show (0 : ℝ) < lossConstant + 1 by linarith)).mp hcLe
  have step1 : lossConstant * s * L + 1 ≤ (lossConstant + 1) * (s * L) := by nlinarith [hprod1]
  have step2 : (lossConstant + 1) * (s * L) ≤ (1 / c) * (s * L) :=
    mul_le_mul_of_nonneg_right hcLe' (by linarith [hprod1])
  have step3 : (1 / c) * (s * L) = s * L / c := by ring
  linarith [hloss, step1, step2, step3]

/-! ## The main transport theorem -/

set_option maxHeartbeats 1000000 in
theorem cfhmpsv_structure_audited : Erdos289.External.CFHMPSVStructureStatement := by
  intro β η hβ hη hη1
  obtain ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden, hlossC, hout⟩ :=
    Erdos186.CFP.nonemptyIntegerTheorem15 β η hβ hη hη1
  have hnum' : (0 : ℝ) < (scaleNum : ℝ) := by exact_mod_cast hnum
  have hden' : (0 : ℝ) < (scaleDen : ℝ) := by exact_mod_cast hden
  have hlossC' : (0 : ℝ) < (lossConstant : ℝ) := by exact_mod_cast hlossC
  set c : ℝ := min ((scaleNum : ℝ) / scaleDen) (1 / ((lossConstant : ℝ) + 1)) with hc_def
  have hc_pos : 0 < c := lt_min (by positivity) (by positivity)
  have hc_le1 : c ≤ (scaleNum : ℝ) / scaleDen := min_le_left _ _
  have hc_le2 : c ≤ 1 / ((lossConstant : ℝ) + 1) := min_le_right _ _
  refine ⟨c, hc_pos, D, 2, le_refl 2, ?_⟩
  intro m n s A hm hAsub hAcard hn hs_lower hs_upper
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hAcard_m : (A.card : ℝ) = (m : ℝ) := by exact_mod_cast hAcard
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hlogb_ge1 : (1 : ℝ) ≤ Real.logb 2 (m : ℝ) := by
    have h1 := Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num)
      (show (0 : ℝ) < 2 by norm_num) hm2
    rwa [Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num)] at h1
  have hlogb_pos : (0 : ℝ) < Real.logb 2 (m : ℝ) := by linarith
  have hs_ge1 : (1 : ℝ) ≤ (s : ℝ) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) ^ η := Real.one_le_rpow hm1 hη.le
    linarith [hs_lower]
  have hthresh_m : (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (m : ℝ) ≤ (scaleNum : ℝ) * (m : ℝ) := by
    have e1 : (s : ℝ) * Real.logb 2 (m : ℝ) ≤ c * (m : ℝ) := by
      rw [logTwo_eq_logb] at hs_upper
      rwa [le_div_iff₀ hlogb_pos] at hs_upper
    have e2 : c * (scaleDen : ℝ) ≤ (scaleNum : ℝ) := (le_div_iff₀ hden').mp hc_le1
    exact threshold_bound c s m scaleNum scaleDen (Real.logb 2 (m : ℝ)) hden' hm1 e1 e2
  have hn' : (n : ℝ) ≤ Real.rpow (A.card : ℝ) β := by rw [hAcard_m]; exact hn
  have hs_lower' : Real.rpow (A.card : ℝ) η ≤ (s : ℝ) := by rw [hAcard_m]; exact hs_lower
  have hthresh' : (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) ≤
      (scaleNum : ℝ) * (A.card : ℝ) := by rw [hAcard_m]; exact hthresh_m
  obtain ⟨k, loss, hWnon, hlossbound⟩ := hout n A s hA_ne hAsub hn' hs_lower' hthresh'
  obtain ⟨W⟩ := hWnon
  set E := W.enhanced with hE_def
  have hscaleLower : scaleNum * s ≤ scaleDen * k := W.scale_lower
  have hscaleLower' : (scaleNum : ℝ) * (s : ℝ) ≤ (scaleDen : ℝ) * (k : ℝ) := by
    exact_mod_cast hscaleLower
  set r := E.symmetryRadii with hr_def
  have hCentered : E.progression.Centered r := E.symmetryCentered
  set P : Erdos289.External.GAPRepresentation :=
    { rank := E.rank
      step := fun i => E.progression.steps i 0
      lower := fun i => -(r i : ℝ)
      upper := fun i => (r i : ℝ) } with hP_def
  have hP_lower : ∀ i, P.lower i = -(r i : ℝ) := fun _ => rfl
  have hP_upper : ∀ i, P.upper i = (r i : ℝ) := fun _ => rfl
  set J := E.core.image proj with hJ_def
  set J' := E.reserved.image proj with hJ'_def
  have hJ_sub : J ⊆ A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact proj_mem_of_mem_integerPoints (E.core_subset hx)
  have hJcard : J.card = E.core.card := Finset.card_image_of_injective _ proj_injective
  have hJ'_sub_J : J' ⊆ J := Finset.image_subset_image E.reserved_subset_core
  have hJ'card : J'.card ≤ s :=
    le_trans Finset.card_image_le E.reserved_small
  have hm_le_nat : m ≤ E.core.card + loss := by
    have h1 : (integerPoints A).card ≤ E.core.card + loss := E.core_large
    rwa [card_integerPoints, hAcard] at h1
  have hm_le' : (m : ℝ) ≤ (E.core.card : ℝ) + (loss : ℝ) := by exact_mod_cast hm_le_nat
  have hcoreJ : (E.core.card : ℝ) = (J.card : ℝ) := by exact_mod_cast hJcard.symm
  have hlossbound_m : (loss : ℝ) ≤ (lossConstant : ℝ) * (s : ℝ) * Real.logb 2 (m : ℝ) + 1 := by
    rw [← hAcard_m]; exact hlossbound
  have hloss_le : (loss : ℝ) ≤ (s : ℝ) * Real.logb 2 (m : ℝ) / c :=
    loss_final_bound c s (Real.logb 2 (m : ℝ)) loss lossConstant hc_pos hs_ge1 hlogb_ge1
      hlossC'.le hc_le2 hlossbound_m
  have hCardBound : (m : ℝ) - (s : ℝ) * Erdos289.External.logTwo (m : ℝ) / c ≤ (J.card : ℝ) := by
    rw [logTwo_eq_logb]
    linarith [hm_le', hcoreJ, hloss_le]
  have hRankBound : P.rank ≤ D := E.rank_le
  have hBox1_eq : P.coordinateBox 1 = intBox r := by
    ext v
    constructor
    · intro hv i
      have h1 := (hv i).1
      have h2 := (hv i).2
      simp only [hP_lower, hP_upper, one_mul] at h1 h2
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · intro hv i
      have h1 := (hv i).1
      have h2 := (hv i).2
      simp only [hP_lower, hP_upper, one_mul]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hBox1_sub : P.coordinateBox 1 ⊆ intBox r := hBox1_eq.subset
  have hProperAt1 : P.properAt 1 := by
    constructor
    · refine ⟨0, fun i => ?_⟩
      have hri : (0 : ℝ) ≤ (r i : ℝ) := Nat.cast_nonneg _
      constructor
      · simp only [hP_lower, Pi.zero_apply, Int.cast_zero, one_mul]
        exact neg_nonpos_of_nonneg hri
      · simp only [hP_upper, Pi.zero_apply, Int.cast_zero, one_mul]
        exact hri
    · have hInj : Set.InjOn (fun z : Fin E.rank → ℤ => ∑ i, z i * E.progression.steps i 0)
          (intBox r) := injOn_intBox E.progression r hCentered E.progression_proper
      exact hInj.mono hBox1_sub
  have hCarrierEq1 : proj '' (E.progression.carrier : Set (LatticePoint 1)) = P.carrierAt 1 := by
    show proj '' (E.progression.carrier : Set (LatticePoint 1)) = P.eval '' P.coordinateBox 1
    rw [hBox1_eq]
    exact proj_image_centered E.progression r hCentered
  have hSubsetCarrier1 : ((J : Set ℤ) ∪ {0}) ⊆ P.carrierAt 1 := by
    rw [← hCarrierEq1]
    rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ⟨x, Finset.mem_coe.mpr (E.core_zero_subset (Finset.mem_insert_of_mem hx)), rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨0, Finset.mem_coe.mpr (E.core_zero_subset (Finset.mem_insert_self _ _)), proj_zero⟩
  have hk_real : c * (s : ℝ) ≤ (k : ℝ) := by
    have e2 : c * (scaleDen : ℝ) ≤ scaleNum := (le_div_iff₀ hden').mp hc_le1
    exact dilate_scale_bound c s k scaleNum scaleDen hden' (by linarith [hs_ge1]) e2 hscaleLower'
  have hDilateCentered : (E.progression.dilate k).Centered (fun i => k * r i) := hCentered.dilate k
  have hBoxCS_sub : P.coordinateBox (c * (s : ℝ)) ⊆ intBox (fun i => k * r i) := by
    intro v hv i
    dsimp only
    have h1 := (hv i).1
    have h2 := (hv i).2
    rw [hP_lower] at h1
    rw [hP_upper] at h2
    have hri : (0 : ℝ) ≤ (r i : ℝ) := Nat.cast_nonneg _
    have hkr : (c * (s : ℝ)) * (r i : ℝ) ≤ (k : ℝ) * (r i : ℝ) :=
      mul_le_mul_of_nonneg_right hk_real hri
    have hcast : (k : ℝ) * (r i : ℝ) = ((k * r i : ℕ) : ℝ) := by push_cast; ring
    refine ⟨?_, ?_⟩
    · have h3 : -((k : ℝ) * (r i : ℝ)) ≤ (v i : ℝ) := by linarith [h1, hkr]
      rw [hcast] at h3
      exact_mod_cast h3
    · have h3 : (v i : ℝ) ≤ (k : ℝ) * (r i : ℝ) := le_trans h2 hkr
      rw [hcast] at h3
      exact_mod_cast h3
  have hProperAtCS : P.properAt (c * (s : ℝ)) := by
    constructor
    · refine ⟨0, fun i => ?_⟩
      have hri : (0 : ℝ) ≤ (r i : ℝ) := Nat.cast_nonneg _
      have hcs : (0 : ℝ) ≤ c * (s : ℝ) := by positivity
      constructor
      · simp only [hP_lower, Pi.zero_apply, Int.cast_zero, mul_neg]
        exact neg_nonpos_of_nonneg (mul_nonneg hcs hri)
      · simp only [hP_upper, Pi.zero_apply, Int.cast_zero]
        exact mul_nonneg hcs hri
    · have hInj : Set.InjOn
          (fun z : Fin E.rank → ℤ => ∑ i, z i * (E.progression.dilate k).steps i 0)
          (intBox (fun i => k * r i)) :=
        injOn_intBox (E.progression.dilate k) (fun i => k * r i) hDilateCentered E.dilate_proper
      exact hInj.mono hBoxCS_sub
  have hCarrierEqDilate : proj '' ((E.progression.dilate k).carrier : Set (LatticePoint 1)) =
      (fun z : Fin E.rank → ℤ => ∑ i, z i * (E.progression.dilate k).steps i 0) ''
        intBox (fun i => k * r i) :=
    proj_image_centered (E.progression.dilate k) (fun i => k * r i) hDilateCentered
  have hCarrierCS_sub : P.carrierAt (c * (s : ℝ)) ⊆
      proj '' ((E.progression.dilate k).carrier : Set (LatticePoint 1)) := by
    rw [hCarrierEqDilate]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, hBoxCS_sub hv, rfl⟩
  refine ⟨J, P, J', hJ_sub, hCardBound, hRankBound, hProperAt1, hSubsetCarrier1, hJ'_sub_J,
    hJ'card, hProperAtCS, proj E.translatePoint, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hCarrierCS_sub hx
  have hy' : E.translatePoint + y ∈
      translate E.translatePoint (E.progression.dilate k).carrier :=
    Finset.mem_image.mpr ⟨y, Finset.mem_coe.mp hy, rfl⟩
  have hy2 := E.covered hy'
  obtain ⟨S, hS_sub, hS_sum⟩ := GAP.mem_subsetSums_iff.mp hy2
  have hsum_proj : proj (∑ b ∈ S, b) = ∑ b ∈ S, proj b := by
    simp [proj, Finset.sum_apply]
  have hsum_image : (∑ b ∈ S, proj b) = ∑ c ∈ S.image proj, c := by
    rw [Finset.sum_image (fun a _ b _ h => proj_injective h)]
  have key : proj E.translatePoint + x = ∑ c ∈ S.image proj, c := by
    have hadd : proj (E.translatePoint + y) = proj E.translatePoint + proj y := rfl
    rw [← hyx, ← hadd, ← hS_sum, hsum_proj, hsum_image]
  exact ⟨S.image proj, Finset.image_subset_image hS_sub, key.symm⟩

end Erdos289.Ported
