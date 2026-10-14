import LearningGuided.Sec2.Tools

/-!
# The hard family of Section `sec:construction`

For an integer `m ≥ 3` put `M = 4^m`, `k = 2m`, `n = 3m + 2`, `α = 2^{-m}`, `a = 1 - α`.
Keys are `θ ∈ {0,1}^k`, the distinguished string is `x_θ = θ 0^{m+2}`, and the target is
`μ_θ = a U_n + α δ_{x_θ}` (equation `eq:target`). The guide (equation `eq:guide`) is
`h_θ(u) = 2^{-t}` for `|u| = t ≤ k` and `h_θ(u) = (1-β_j) 2^{-t} + β_j 1{u ⪯ x_θ}` for
`t = k + j`, `1 ≤ j ≤ m + 2`, with `β_j = 2^{j-1}/(2M)`.

This file sets up the definitions and the arithmetic of `α`, `β_j` and `2^{-t}`.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec4

open Sec2

/-- `α = 2^{-m}`. -/
noncomputable def alpha (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

/-- The accuracy `δ_m = α/4`. -/
noncomputable def deltaM (m : ℕ) : ℝ := alpha m / 4

/-- The distinguished string `x_θ = θ 0^{m+2}`. -/
def xθ (m : ℕ) (θ : Str (2 * m)) : Str (3 * m + 2) :=
  fun i => if h : i.1 < 2 * m then θ ⟨i.1, h⟩ else false

/-- The target `μ_θ = (1-α) U_n + α δ_{x_θ}` of `eq:target`. -/
noncomputable def muθ (m : ℕ) (θ : Str (2 * m)) : Str (3 * m + 2) → ℝ :=
  mixD (unif (3 * m + 2)) (alpha m) (xθ m θ)

/-- The padding weights: `0` up to depth `k = 2m`, and `β_j = 2^{j-1}/(2M) = 2^j/(4M)` at depth
`k + j`. -/
noncomputable def bet (m t : ℕ) : ℝ :=
  if t ≤ 2 * m then 0 else (2 : ℝ) ^ (t - 2 * m) / (4 * 4 ^ m)

open Classical in
/-- The guide `h_θ` of `eq:guide` (zero on words longer than `n`). -/
noncomputable def hθ (m : ℕ) (θ : Str (2 * m)) : Guide := fun u =>
  if u.length ≤ 3 * m + 2 then
    (1 - bet m u.length) * ((2 : ℝ) ^ u.length)⁻¹ +
      bet m u.length * (if IsPre u (xθ m θ) then 1 else 0)
  else 0

/-- The class `F_m = {μ_θ}`. -/
def Fm (m : ℕ) : Set (Str (3 * m + 2) → ℝ) := Set.range (muθ m)

/-- The minimum coherent correction mass `d_m = α - (5/4 + α)/M` of `eq:dstar`. -/
noncomputable def dm (m : ℕ) : ℝ := alpha m - (5 / 4 + alpha m) / 4 ^ m

/-- The capacity value `C_m = 2 + α - 2α² - α³ + α⁴` of `eq:capacity-value`. -/
noncomputable def Cm (m : ℕ) : ℝ :=
  2 + alpha m - 2 * alpha m ^ 2 - alpha m ^ 3 + alpha m ^ 4

/-! ### Arithmetic of `α` -/

theorem alpha_pos (m : ℕ) : 0 < alpha m := by unfold alpha; positivity

theorem alpha_mul (m : ℕ) : alpha m * 2 ^ m = 1 := by
  unfold alpha; field_simp

theorem four_pow (m : ℕ) : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem alpha_sq (m : ℕ) : alpha m ^ 2 = ((4 : ℝ) ^ m)⁻¹ := by
  unfold alpha; rw [four_pow, inv_pow]

theorem alpha_le_eighth {m : ℕ} (hm : 3 ≤ m) : alpha m ≤ 1 / 8 := by
  unfold alpha
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  calc (1 / 8 : ℝ)⁻¹ = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm

theorem alpha_le_one (m : ℕ) : alpha m ≤ 1 := by
  unfold alpha
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- `α M = 2^m`. -/
theorem alpha_mul_M (m : ℕ) : alpha m * 4 ^ m = 2 ^ m := by
  unfold alpha; rw [four_pow]; field_simp

/-- `2^{-t}` -/
theorem two_pow_inv_two_m (m : ℕ) : ((2 : ℝ) ^ (2 * m))⁻¹ = alpha m ^ 2 := by
  rw [alpha_sq, pow_mul]; norm_num

theorem two_pow_inv_le_of_le {s t : ℕ} (h : s ≤ t) : ((2 : ℝ) ^ t)⁻¹ ≤ ((2 : ℝ) ^ s)⁻¹ :=
  inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- At depth at most `k`, `2^{-t} ≥ α²`. -/
theorem alpha_sq_le_pp {m t : ℕ} (h : t ≤ 2 * m) : alpha m ^ 2 ≤ ((2 : ℝ) ^ t)⁻¹ := by
  rw [← two_pow_inv_two_m]; exact two_pow_inv_le_of_le h

/-- At depth at least `k`, `2^{-t} ≤ α²`. -/
theorem pp_le_alpha_sq {m t : ℕ} (h : 2 * m ≤ t) : ((2 : ℝ) ^ t)⁻¹ ≤ alpha m ^ 2 := by
  rw [← two_pow_inv_two_m]; exact two_pow_inv_le_of_le h

/-- At depth at least `m + 3`, `2^{-t} ≤ α/8`. -/
theorem pp_le_alpha_eighth {m t : ℕ} (h : m + 3 ≤ t) : ((2 : ℝ) ^ t)⁻¹ ≤ alpha m / 8 := by
  calc ((2 : ℝ) ^ t)⁻¹ ≤ ((2 : ℝ) ^ (m + 3))⁻¹ := two_pow_inv_le_of_le h
    _ = alpha m / 8 := by unfold alpha; rw [pow_add]; norm_num; ring

/-! ### The padding weights -/

theorem bet_of_le {m t : ℕ} (h : t ≤ 2 * m) : bet m t = 0 := by simp [bet, h]

theorem bet_of_gt {m t : ℕ} (h : 2 * m < t) :
    bet m t = (2 : ℝ) ^ (t - 2 * m) * alpha m ^ 2 / 4 := by
  simp only [bet, show ¬ t ≤ 2 * m by omega, ite_false, alpha_sq]
  field_simp

theorem bet_nonneg (m t : ℕ) : 0 ≤ bet m t := by
  unfold bet; split_ifs <;> positivity

theorem bet_first (m : ℕ) : bet m (2 * m + 1) = alpha m ^ 2 / 2 := by
  rw [bet_of_gt (by omega), show 2 * m + 1 - 2 * m = 1 by omega]; ring

theorem bet_last (m : ℕ) : bet m (3 * m + 2) = alpha m := by
  rw [bet_of_gt (by omega), show 3 * m + 2 - 2 * m = m + 2 by omega, pow_add]
  have h := alpha_mul m
  have : alpha m ^ 2 * 2 ^ m = alpha m := by rw [sq, mul_assoc, h, mul_one]
  calc (2 : ℝ) ^ m * 2 ^ 2 * alpha m ^ 2 / 4 = alpha m ^ 2 * 2 ^ m := by ring
    _ = alpha m := this

theorem bet_succ {m t : ℕ} (h : 2 * m < t) : bet m (t + 1) = 2 * bet m t := by
  rw [bet_of_gt h, bet_of_gt (by omega), show t + 1 - 2 * m = (t - 2 * m) + 1 by omega, pow_succ]
  ring

theorem bet_mono {m s t : ℕ} (hst : s ≤ t) : bet m s ≤ bet m t := by
  by_cases hs : s ≤ 2 * m
  · rw [bet_of_le hs]; exact bet_nonneg m t
  · rw [bet_of_gt (by omega), bet_of_gt (by omega)]
    have : (2 : ℝ) ^ (s - 2 * m) ≤ 2 ^ (t - 2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
    have := sq_nonneg (alpha m)
    nlinarith

theorem bet_le_alpha {m t : ℕ} (h : t ≤ 3 * m + 2) : bet m t ≤ alpha m :=
  (bet_mono h).trans (bet_last m).le

theorem alpha_sq_le_bet {m t : ℕ} (h : 2 * m + 2 ≤ t) : alpha m ^ 2 ≤ bet m t := by
  have : bet m (2 * m + 2) = alpha m ^ 2 := by
    rw [bet_of_gt (by omega), show 2 * m + 2 - 2 * m = 2 by omega]; ring
  rw [← this]; exact bet_mono h

theorem bet_lt_one {m t : ℕ} (hm : 3 ≤ m) (h : t ≤ 3 * m + 2) : bet m t < 1 :=
  lt_of_le_of_lt (bet_le_alpha h) (lt_of_le_of_lt (alpha_le_eighth hm) (by norm_num))

/-! ### Masses and guide values -/

theorem isDist_muθ (m : ℕ) (θ : Str (2 * m)) : IsDist (muθ m θ) :=
  isDist_mixD (isDist_unif _) (alpha_pos m).le (alpha_le_one m) _

theorem mass_muθ (m : ℕ) (θ : Str (2 * m)) {u : List Bool} (hu : u.length ≤ 3 * m + 2) :
    mass (muθ m θ) u = (1 - alpha m) * ((2 : ℝ) ^ u.length)⁻¹ +
      alpha m * (if IsPre u (xθ m θ) then 1 else 0) := by
  rw [muθ, mass_mixD, mass_unif hu]

theorem hθ_of_le (m : ℕ) (θ : Str (2 * m)) {u : List Bool} (hu : u.length ≤ 3 * m + 2) :
    hθ m θ u = (1 - bet m u.length) * ((2 : ℝ) ^ u.length)⁻¹ +
      bet m u.length * (if IsPre u (xθ m θ) then 1 else 0) := by
  simp [hθ, hu]

theorem hθ_of_gt (m : ℕ) (θ : Str (2 * m)) {u : List Bool} (hu : 3 * m + 2 < u.length) :
    hθ m θ u = 0 := by
  simp [hθ, show ¬ u.length ≤ 3 * m + 2 by omega]

theorem xθ_injective (m : ℕ) : Function.Injective (xθ m) := by
  intro θ θ' h
  funext i
  have := congrFun h ⟨i.1, by omega⟩
  simpa [xθ, i.2] using this

theorem alpha_lt_one {m : ℕ} (hm : 1 ≤ m) : alpha m < 1 := by
  unfold alpha
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))

theorem muθ_pos {m : ℕ} (hm : 1 ≤ m) (θ : Str (2 * m)) (x : Str (3 * m + 2)) :
    0 < muθ m θ x := by
  unfold muθ mixD unif
  have h1 : 0 < 1 - alpha m := by linarith [alpha_lt_one hm]
  have h2 : 0 ≤ alpha m * dirac (xθ m θ) x := by
    have := alpha_pos m
    unfold dirac; split_ifs <;> simp [this.le]
  have h3 : 0 < (1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹ := by positivity
  linarith

theorem muθ_injective (m : ℕ) : Function.Injective (muθ m) := by
  intro θ θ' h
  have h1 := congrFun h (xθ m θ)
  simp only [muθ, mixD, dirac, ite_true] at h1
  by_contra hne
  have hne' : xθ m θ ≠ xθ m θ' := fun e => hne (xθ_injective m e)
  rw [ite_eq_right hne'] at h1
  have := alpha_pos m
  linarith

end Sec4
end LearningGuided
