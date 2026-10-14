import LearningGuided.Cuts

/-!
# Parameters of the table construction (Appendix B)

This file fixes the parameters of Theorem `pw-thm:parameter`: `r = 2^p ≥ 8` is a power of two
and `ℓ ≥ 2`. It defines `W = r²`, `k = log₂ W = 2 log₂ r`, `d = k + ℓ`, `N = 1 + r d`,
`m_± = W/2 ± r`, the normalizers `A_± = 2W + m_±/2 = 9W/4 ± r/2`, `A_∘ = 9W/4` and
`Z = A_+^r + A_-^r` of `pw-eq:normalizers`, and proves the numeric facts used later:
the tail ratio `pw-eq:tail-ratio` and the root gap of `pw-eq:rootgap`.
-/

namespace LearningGuided.PointwiseLB

/-- The parameters of Theorem `pw-thm:parameter`: `r = 2^p` with `p ≥ 3` (so `r ≥ 8`), and
`ℓ ≥ 2`. -/
structure Prm where
  /-- `log₂ r`. -/
  p : ℕ
  /-- The number of hiding locations per row. -/
  ℓ : ℕ
  hp : 3 ≤ p
  hℓ : 2 ≤ ℓ

namespace Prm

variable (P : Prm)

/-- `r = 2^p`. -/
def r : ℕ := 2 ^ P.p
/-- `k = log₂ W = 2 log₂ r`, the number of address bits. -/
def k : ℕ := 2 * P.p
/-- `W = r² = 2^k`, the number of rows of each table. -/
def W : ℕ := 2 ^ P.k
/-- `d = k + ℓ`, the block length. -/
def d : ℕ := P.k + P.ℓ
/-- `N = 1 + r d = 1 + r (2 log₂ r + ℓ)`, the string length. -/
def N : ℕ := 1 + P.r * P.d
/-- `m_+ = W/2 + r`. -/
def mPlus : ℕ := P.W / 2 + P.r
/-- `m₋ = W/2 - r`. -/
def mMinus : ℕ := P.W / 2 - P.r
/-- `A_∘ = 9W/4`. -/
noncomputable def Acirc : ℝ := 9 * (P.W : ℝ) / 4
/-- `A_+ = 2W + m_+/2`. -/
noncomputable def Aplus : ℝ := 2 * (P.W : ℝ) + (P.mPlus : ℝ) / 2
/-- `A₋ = 2W + m₋ / 2`. -/
noncomputable def Aminus : ℝ := 2 * (P.W : ℝ) + (P.mMinus : ℝ) / 2
/-- `Z = A_+^r + A_-^r`. -/
noncomputable def Z : ℝ := P.Aplus ^ P.r + P.Aminus ^ P.r
/-- `M₀ = 2 (2ℓ)^{2W}`, the bound on the class size. -/
def M0 : ℕ := 2 * (2 * P.ℓ) ^ (2 * P.W)

theorem eight_le_r : 8 ≤ P.r := by
  unfold r
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ P.p := Nat.pow_le_pow_right (by norm_num) P.hp

theorem r_pos : 0 < P.r := by have := P.eight_le_r; omega

theorem W_eq : P.W = P.r * P.r := by
  unfold W k r; rw [← pow_add]; ring_nf

theorem two_r_le_W : 2 * P.r ≤ P.W / 2 := by
  have h8 := P.eight_le_r
  rw [W_eq]
  have : 4 * P.r ≤ P.r * P.r := Nat.mul_le_mul_right _ (by omega)
  omega

theorem W_even : P.W / 2 * 2 = P.W := by
  rw [W_eq]
  have : 2 ∣ P.r := by unfold r; exact dvd_pow_self 2 (by have := P.hp; omega)
  obtain ⟨c, hc⟩ := this
  rw [hc]
  have : 2 * c * (2 * c) = (2 * c * c) * 2 := by ring
  rw [this, Nat.mul_div_cancel _ (by norm_num)]

theorem r_le_W8 : 8 * P.r ≤ P.W := by
  have h8 := P.eight_le_r
  rw [W_eq]; exact Nat.mul_le_mul_right _ h8

theorem W8_mul : P.W / 8 * 8 = P.W := by
  rw [W_eq]
  have : 8 ∣ P.r := by
    unfold r
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this]; exact Nat.pow_dvd_pow 2 P.hp
  obtain ⟨c, hc⟩ := this
  rw [hc]
  have : 8 * c * (8 * c) = (8 * c * c) * 8 := by ring
  rw [this, Nat.mul_div_cancel _ (by norm_num)]

theorem cast_r : (P.r : ℝ) = 2 ^ P.p := by simp [r]

theorem cast_W : (P.W : ℝ) = (P.r : ℝ) * P.r := by rw [W_eq]; push_cast; ring

theorem cast_r_ge : (8 : ℝ) ≤ P.r := by exact_mod_cast P.eight_le_r

theorem cast_W_half : ((P.W / 2 : ℕ) : ℝ) = (P.W : ℝ) / 2 := by
  have := P.W_even
  have h : ((P.W / 2 : ℕ) : ℝ) * 2 = P.W := by exact_mod_cast this
  linarith

theorem cast_mPlus : (P.mPlus : ℝ) = (P.W : ℝ) / 2 + P.r := by
  unfold mPlus; push_cast; rw [cast_W_half]

theorem cast_mMinus : (P.mMinus : ℝ) = (P.W : ℝ) / 2 - P.r := by
  unfold mMinus
  rw [Nat.cast_sub (by have := P.two_r_le_W; omega), cast_W_half]

theorem mMinus_lt_mPlus : P.mMinus < P.mPlus := by
  have h1 : (P.mMinus : ℝ) < P.mPlus := by
    rw [cast_mPlus, cast_mMinus]; have := P.cast_r_ge; linarith
  exact_mod_cast h1

theorem mPlus_le_W : P.mPlus ≤ P.W := by
  have h1 : (P.mPlus : ℝ) ≤ P.W := by
    rw [cast_mPlus, cast_W]; have := P.cast_r_ge; nlinarith
  exact_mod_cast h1

theorem Aplus_eq : P.Aplus = P.Acirc + (P.r : ℝ) / 2 := by
  unfold Aplus Acirc; rw [cast_mPlus]; ring

theorem Aminus_eq : P.Aminus = P.Acirc - (P.r : ℝ) / 2 := by
  unfold Aminus Acirc; rw [cast_mMinus]; ring

theorem Acirc_pos : 0 < P.Acirc := by
  unfold Acirc; have : (0 : ℝ) < P.W := by rw [cast_W]; have := P.cast_r_ge; nlinarith
  positivity

/-- `x = 2/(9r)`, so that `A_± = A_∘ (1 ± x)`. -/
noncomputable def xr : ℝ := 2 / (9 * (P.r : ℝ))

theorem xr_pos : 0 < P.xr := by unfold xr; have := P.cast_r_ge; positivity

theorem r_mul_xr : (P.r : ℝ) * P.xr = 2 / 9 := by
  unfold xr; have := P.cast_r_ge; field_simp

theorem xr_le : P.xr ≤ 1 / 36 := by
  unfold xr; have := P.cast_r_ge
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

theorem Aplus_eq_mul : P.Aplus = P.Acirc * (1 + P.xr) := by
  rw [Aplus_eq]; unfold Acirc xr; rw [cast_W]; have := P.cast_r_ge; field_simp; ring

theorem Aminus_eq_mul : P.Aminus = P.Acirc * (1 - P.xr) := by
  rw [Aminus_eq]; unfold Acirc xr; rw [cast_W]; have := P.cast_r_ge; field_simp; ring

theorem Aminus_pos : 0 < P.Aminus := by
  rw [Aminus_eq_mul]; have := P.xr_le; have := P.Acirc_pos
  exact mul_pos this (by linarith)

theorem Aplus_pos : 0 < P.Aplus := by
  rw [Aplus_eq_mul]; have := P.xr_pos; have := P.Acirc_pos; positivity

theorem Z_pos : 0 < P.Z := by
  unfold Z; have := P.Aplus_pos; have := P.Aminus_pos; positivity

/-- `(1 + x)^r ≤ 9/7`. -/
theorem one_add_xr_pow_le : (1 + P.xr) ^ P.r ≤ 9 / 7 := by
  have h1 : (1 + P.xr) ^ P.r ≤ Real.exp P.xr ^ P.r := by
    gcongr
    · linarith [P.xr_pos]
    · linarith [Real.add_one_le_exp P.xr]
  rw [← Real.exp_nat_mul, P.r_mul_xr] at h1
  have h2 := Real.add_one_le_exp (-(2 / 9))
  rw [Real.exp_neg] at h2
  have h3 : 0 < Real.exp (2 / 9) := Real.exp_pos _
  have h4 : Real.exp (2 / 9) ≤ 9 / 7 := by
    rw [← inv_inv (Real.exp (2 / 9))]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num at h2 ⊢; linarith
  linarith

/-- `(1 - x)^r ≥ 7/9`. -/
theorem one_sub_xr_pow_ge : 7 / 9 ≤ (1 - P.xr) ^ P.r := by
  have h := one_add_mul_le_pow (a := -P.xr) (by linarith [P.xr_le]) P.r
  rw [mul_neg, P.r_mul_xr, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
  norm_num at h ⊢; linarith

/-- `pw-eq:tail-ratio` at `A_a = A_+`: `3/4 ≤ (A_∘/A_+)^s ≤ 4/3` for
`0 ≤ s ≤ r`. -/
theorem tail_ratio_plus {e : ℕ} (he : e ≤ P.r) :
    3 / 4 ≤ (P.Acirc / P.Aplus) ^ e ∧ (P.Acirc / P.Aplus) ^ e ≤ 4 / 3 := by
  have hA := P.Acirc_pos
  have hx := P.xr_pos
  have hq : P.Acirc / P.Aplus = (1 + P.xr)⁻¹ := by
    rw [Aplus_eq_mul]; field_simp
  rw [hq]
  have hle1 : (1 + P.xr)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hpos : 0 < (1 + P.xr)⁻¹ := by positivity
  constructor
  · calc (3 : ℝ) / 4 ≤ ((1 + P.xr) ^ P.r)⁻¹ := by
          rw [le_inv_comm₀ (by norm_num) (by positivity)]
          have := P.one_add_xr_pow_le; linarith
      _ = (1 + P.xr)⁻¹ ^ P.r := by rw [inv_pow]
      _ ≤ (1 + P.xr)⁻¹ ^ e := pow_le_pow_of_le_one hpos.le hle1 he
  · calc (1 + P.xr)⁻¹ ^ e ≤ 1 := pow_le_one₀ hpos.le hle1
      _ ≤ 4 / 3 := by norm_num

/-- `pw-eq:tail-ratio` at `A_a = A_-`: `3/4 ≤ (A_∘/A_-)^s ≤ 4/3` for
`0 ≤ s ≤ r`. -/
theorem tail_ratio_minus {e : ℕ} (he : e ≤ P.r) :
    3 / 4 ≤ (P.Acirc / P.Aminus) ^ e ∧ (P.Acirc / P.Aminus) ^ e ≤ 4 / 3 := by
  have hA := P.Acirc_pos
  have hx := P.xr_pos
  have hx1 := P.xr_le
  have hq : P.Acirc / P.Aminus = (1 - P.xr)⁻¹ := by
    rw [Aminus_eq_mul]; have : 1 - P.xr ≠ 0 := by linarith
    field_simp
  rw [hq]
  have hge1 : 1 ≤ (1 - P.xr)⁻¹ := one_le_inv₀ (by linarith) |>.mpr (by linarith)
  constructor
  · calc (3 : ℝ) / 4 ≤ 1 := by norm_num
      _ ≤ (1 - P.xr)⁻¹ ^ e := one_le_pow₀ hge1
  · calc (1 - P.xr)⁻¹ ^ e ≤ (1 - P.xr)⁻¹ ^ P.r := pow_le_pow_right₀ hge1 he
      _ = ((1 - P.xr) ^ P.r)⁻¹ := by rw [inv_pow]
      _ ≤ 4 / 3 := by
          rw [inv_le_comm₀ (by have := P.one_sub_xr_pow_ge; linarith) (by norm_num)]
          have := P.one_sub_xr_pow_ge; linarith

/-- Second-order Bernoulli inequality. -/
theorem one_add_pow_ge_quad {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    1 + n * x + (n : ℝ) * ((n : ℝ) - 1) / 2 * x ^ 2 ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (1 + x) n]
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * x ^ 3 + 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · have : (1 : ℝ) ≤ n := by exact_mod_cast h
          have : 0 ≤ (n : ℝ) - 1 := by linarith
          positivity
      nlinarith [mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)]

/-- The root odds: `(1 + x)^{2r} ≥ 3/2`. -/
theorem one_add_xr_pow_two_r : 3 / 2 ≤ (1 + P.xr) ^ (2 * P.r) := by
  have h := one_add_pow_ge_quad P.xr_pos.le (2 * P.r)
  have hr := P.cast_r_ge
  have hrx := P.r_mul_xr
  push_cast at h
  have hx2 : (2 * (P.r : ℝ)) * (2 * P.r - 1) / 2 * P.xr ^ 2 =
      2 * ((P.r : ℝ) * P.xr) ^ 2 - (P.r : ℝ) * P.xr * P.xr := by ring
  rw [hx2, hrx] at h
  have : 2 * (P.r : ℝ) * P.xr = 4 / 9 := by linarith
  rw [this] at h
  have hxl := P.xr_le
  have hxp := P.xr_pos
  nlinarith

/-- `pw-eq:rootgap` in normalized form: `A_+^r / Z ≥ 3/5`. -/
theorem root_gap : 3 / 5 ≤ P.Aplus ^ P.r / P.Z := by
  rw [le_div_iff₀ P.Z_pos]
  unfold Z
  rw [Aplus_eq_mul, Aminus_eq_mul, mul_pow, mul_pow]
  have hA : 0 < P.Acirc ^ P.r := pow_pos P.Acirc_pos _
  have hx := P.xr_pos
  have hx1 := P.xr_le
  have h2 := P.one_add_xr_pow_two_r
  have hprod : ((1 - P.xr) * (1 + P.xr)) ^ P.r ≤ 1 :=
    pow_le_one₀ (by nlinarith) (by nlinarith)
  rw [mul_pow] at hprod
  have hp1 : 0 ≤ (1 - P.xr) ^ P.r := pow_nonneg (by linarith) _
  have hp2 : 0 < (1 + P.xr) ^ P.r := pow_pos (by linarith) _
  rw [mul_comm 2 P.r, pow_mul'] at h2
  rw [pow_two, mul_pow] at h2
  -- 3 (1-x)^r ≤ 2 (1+x)^r
  have key : 3 * (1 - P.xr) ^ P.r ≤ 2 * (1 + P.xr) ^ P.r := by
    by_contra hc
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hc) hp2
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hA.le]

end Prm

end LearningGuided.PointwiseLB
