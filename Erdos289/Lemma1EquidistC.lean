import Erdos289.External
import Erdos289.ErdosTuran

namespace Erdos289

open Filter Finset Topology

theorem div_sub_div_error (T₁ T₂ d : ℕ) (hT : T₁ ≤ T₂) (hd : 0 < d) :
    |((T₂ / d - T₁ / d : ℕ) : ℝ) - ((T₂ - T₁ : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have heq2 : T₂ = d * (T₂ / d) + T₂ % d := (Nat.div_add_mod T₂ d).symm
  have heq1 : T₁ = d * (T₁ / d) + T₁ % d := (Nat.div_add_mod T₁ d).symm
  have hmod2 : T₂ % d < d := Nat.mod_lt T₂ hd
  have hmod1 : T₁ % d < d := Nat.mod_lt T₁ hd
  have hT1div_le : T₁ / d ≤ T₂ / d := Nat.div_le_div_right hT
  have hsub_div : ((T₂ / d - T₁ / d : ℕ) : ℝ) = ((T₂ / d : ℕ) : ℝ) - ((T₁ / d : ℕ) : ℝ) :=
    Nat.cast_sub hT1div_le
  have hsub_T : ((T₂ - T₁ : ℕ) : ℝ) = (T₂ : ℝ) - (T₁ : ℝ) :=
    Nat.cast_sub hT
  have hT2R : (T₂ : ℝ) = (d : ℝ) * ((T₂ / d : ℕ) : ℝ) + ((T₂ % d : ℕ) : ℝ) := by
    nth_rw 1 [heq2]; push_cast; ring
  have hT1R : (T₁ : ℝ) = (d : ℝ) * ((T₁ / d : ℕ) : ℝ) + ((T₁ % d : ℕ) : ℝ) := by
    nth_rw 1 [heq1]; push_cast; ring
  rw [hsub_div, hsub_T, hT2R, hT1R]
  have hdiff : ((T₂ / d : ℕ) : ℝ) - ((T₁ / d : ℕ) : ℝ) -
      ((d : ℝ) * ((T₂ / d : ℕ) : ℝ) + ((T₂ % d : ℕ) : ℝ) - ((d : ℝ) * ((T₁ / d : ℕ) : ℝ) + ((T₁ % d : ℕ) : ℝ))) / (d : ℝ)
      = - (((T₂ % d : ℕ) : ℝ) - ((T₁ % d : ℕ) : ℝ)) / (d : ℝ) := by
    field_simp; ring
  rw [hdiff]
  rw [show -(((T₂ % d : ℕ) : ℝ) - ((T₁ % d : ℕ) : ℝ)) / (d : ℝ) = - ((((T₂ % d : ℕ) : ℝ) - ((T₁ % d : ℕ) : ℝ)) / (d : ℝ)) by ring]
  rw [abs_neg, abs_div, abs_of_pos hdR, div_le_one₀ hdR]
  have hm2R : 0 ≤ ((T₂ % d : ℕ) : ℝ) := by positivity
  have hm1R : 0 ≤ ((T₁ % d : ℕ) : ℝ) := by positivity
  have hm2lt : ((T₂ % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod2
  have hm1lt : ((T₁ % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod1
  rw [abs_le]
  constructor <;> linarith

end Erdos289
