import Mathlib

/-!
# Elementary real inequalities used in the rate computations of Section 3
-/

namespace LearningGuided.Sec3

theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `log B ≤ (B/2) log 2` for `B ≥ 4`. -/
theorem log_le_half_mul_log_two {B : ℝ} (hB : 4 ≤ B) : Real.log B ≤ B / 2 * Real.log 2 := by
  have ht : 1 ≤ B / 4 := by linarith
  have hB' : B = 4 * (B / 4) := by ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogt : Real.log (B / 4) ≤ B / 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h1 := one_lt_log_four
  calc Real.log B = Real.log 4 + Real.log (B / 4) := by
        rw [hB', Real.log_mul (by norm_num) (by linarith)]
        ring_nf
    _ ≤ Real.log 4 + (B / 4 - 1) := by linarith
    _ ≤ Real.log 4 + (B / 4 - 1) * Real.log 4 := by nlinarith
    _ = B / 2 * Real.log 2 := by rw [h4]; ring

/-- `log₂ B ≤ B/2` for `B ≥ 4`. -/
theorem logb_two_le_half {B : ℝ} (hB : 4 ≤ B) : Real.logb 2 B ≤ B / 2 := by
  rw [Real.logb, div_le_iff₀ log_two_pos']
  exact log_le_half_mul_log_two hB

/-- For `y ≥ 1` and `s = ⌊log₂ y⌋`, `2^s ≤ y < 2^{s+1}`. -/
theorem floor_logb_two_spec {y : ℝ} (hy : 1 ≤ y) :
    (2 : ℝ) ^ ⌊Real.logb 2 y⌋₊ ≤ y ∧ y < (2 : ℝ) ^ (⌊Real.logb 2 y⌋₊ + 1) := by
  have hL : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy
  have hy0 : 0 < y := by linarith
  have hrp : (2 : ℝ) ^ Real.logb 2 y = y := Real.rpow_logb (by norm_num) (by norm_num) hy0
  constructor
  · calc (2 : ℝ) ^ ⌊Real.logb 2 y⌋₊ = (2 : ℝ) ^ (⌊Real.logb 2 y⌋₊ : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ Real.logb 2 y := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Nat.floor_le hL)
      _ = y := hrp
  · calc y = (2 : ℝ) ^ Real.logb 2 y := hrp.symm
      _ < (2 : ℝ) ^ ((⌊Real.logb 2 y⌋₊ + 1 : ℕ) : ℝ) := by
          refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
          push_cast
          exact Nat.lt_floor_add_one _
      _ = (2 : ℝ) ^ (⌊Real.logb 2 y⌋₊ + 1) := Real.rpow_natCast _ _

/-- `z/2 ≤ log(1+z)` for `0 ≤ z ≤ 1`. -/
theorem half_le_log_one_add {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : z / 2 ≤ Real.log (1 + z) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 1 + z) (by linarith)
  have : z / 2 ≤ 1 - (1 + z)⁻¹ := by
    rw [show 1 - (1 + z)⁻¹ = z / (1 + z) by field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

theorem ceil_le_add_one {x : ℝ} (hx : 0 ≤ x) : (⌈x⌉₊ : ℝ) ≤ x + 1 :=
  (Nat.ceil_lt_add_one hx).le

end LearningGuided.Sec3
