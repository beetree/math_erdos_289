module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-- For real `x ≥ 2`, replacing `x` by `x - 1` in a reciprocal costs at most
a factor of two. -/
theorem one_div_sub_one_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    1 / (x - 1) ≤ 2 / x := by
  have hx_pos : 0 < x := by linarith
  have hhalf : x / 2 ≤ x - 1 := by linarith
  have hhalf_pos : 0 < x / 2 := by positivity
  calc
    1 / (x - 1) ≤ 1 / (x / 2) := one_div_le_one_div_of_le hhalf_pos hhalf
    _ = 2 / x := by field_simp [hx_pos.ne']
