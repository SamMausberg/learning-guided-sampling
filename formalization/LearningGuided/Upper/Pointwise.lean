import LearningGuided.Branching.Corollary

/-!
# The upper half of `thm:pointwise`

The finite-class upper bound of Golowich, Moitra and Rohatgi (their Theorem 3.2, applied with
ratio `9/4`, binary alphabet and error `1/16`) is not proved here. It enters only as the explicit
hypothesis `GMRUpperBound`. Under it we prove:

* `pw_upper` (Proposition `pw-prop:upper`, `pw-eq:upper`):
  `Q(n,M) ≤ min{M - 1, C n √(log M) log(2 + log M), C n²}`, where the `M - 1` term is exact
  identification (`Upper/Identify.lean`) and the `n²` term is `thm:branching`
  (`Branching/Corollary.lean`, cap `82944 n²`), both proved here.
* `pw_main_upper` (the upper inequalities of `eq:pw-main`):
  `Q_pw(n,M,1/16) ≤ c₁ min{M, n√(log M) log(2 + log M), n²} ≤ c₂ L_n K(n,M)`, including the case
  analysis on which term attains `K(n,M)`.
* `pw_expn_upper` (the right inequality of `eq:pw-expn`):
  `Q_pw(n,⌊eⁿ⌋,1/16) ≤ c₁ n^{3/2} log(2n)`, for every `n ≥ 2` and with the same `c₁`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Upper

/-- The Golowich–Moitra–Rohatgi finite-class upper bound at error `δ` (their Theorem 3.2 with
ratio `9/4` and binary alphabet; it holds for every error level), taken as an explicit hypothesis:
there is a constant `C₀` such that for all `n, M ≥ 2`, every class of at most `M` distributions on
`n` bits is solvable in the pointwise factor-`9/4` model at error `δ` with a deterministic cap at
most `C₀ n √(log M) log(2 + log M)`. -/
def GMRUpperBoundAt (δ : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ n M : ℕ, 2 ≤ n → 2 ≤ M → ∀ F : Finset (Str n → ℝ), F.card ≤ M →
    (∀ μ ∈ F, IsDist μ) → ∃ q A, Solves (PwLegal (9 / 4)) (F : Set (Str n → ℝ)) δ q A ∧
      (q : ℝ) ≤ C₀ * n * Real.sqrt (Real.log M) * Real.log (2 + Real.log M)

/-- The Golowich–Moitra–Rohatgi bound at error `1/16`, the case used in Theorem
`thm:pointwise`. -/
def GMRUpperBound : Prop := GMRUpperBoundAt (1 / 16)

/-- `K(n,M) = min{M, n√(log M), n²}` of `eq:K`. -/
noncomputable def Krate (n M : ℕ) : ℝ :=
  min (M : ℝ) (min (n * Real.sqrt (Real.log M)) ((n : ℝ) ^ 2))

/-- `L_n = log(2n)` of `eq:K`. -/
noncomputable def Ln (n : ℕ) : ℝ := Real.log (2 * n)

/-- The middle term `n √(log M) log(2 + log M)`. -/
noncomputable def gmrRate (n M : ℕ) : ℝ :=
  n * Real.sqrt (Real.log M) * Real.log (2 + Real.log M)

variable {n : ℕ}

/-- The worst case is attained by some class of at most `M` distributions. -/
theorem QpwNM_attained (n M : ℕ) :
    ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
      Qpw (F : Set (Str n → ℝ)) (1 / 16) = QpwNM n M (1 / 16) := by
  have hmem := Nat.sSup_mem (s := {q | ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧
    (∀ μ ∈ F, IsDist μ) ∧ Qcx (PwLegal (9 / 4)) (F : Set (Str n → ℝ)) (1 / 16) = q})
    ⟨_, ∅, by simp, by simp, rfl⟩ ⟨M - 1, by
      rintro q ⟨G, hGM, hG, rfl⟩
      exact Qpw_le_sub_one hG hGM (by norm_num)⟩
  obtain ⟨F, hFM, hF, hq⟩ := hmem
  exact ⟨F, hFM, hF, hq⟩

/-- A real bound on every class of at most `M` distributions bounds the worst case. -/
theorem QpwNM_le_of_forall {M : ℕ} {B : ℝ}
    (hB : ∀ F : Finset (Str n → ℝ), F.card ≤ M → (∀ μ ∈ F, IsDist μ) →
      (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) ≤ B) : (QpwNM n M (1 / 16) : ℝ) ≤ B := by
  obtain ⟨F, hFM, hF, hq⟩ := QpwNM_attained n M
  rw [← hq]
  exact hB F hFM hF

/-- `pw-prop:upper`, equation `pw-eq:upper`: under `GMRUpperBound`, there is an absolute constant
`C` with `Q(F,1/16) ≤ min{M - 1, C n√(log M) log(2 + log M), C n²}` for every class of at most
`M` distributions on `n` bits, `n, M ≥ 2`, hence the same bound for `Q(n,M) = Q_pw(n,M,1/16)`.
The first and last terms are proved here without the hypothesis. -/
theorem pw_upper (hGMR : GMRUpperBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
      (∀ F : Finset (Str n → ℝ), F.card ≤ M → (∀ μ ∈ F, IsDist μ) →
        (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) ≤
          min ((M : ℝ) - 1) (min (C * gmrRate n M) (C * (n : ℝ) ^ 2))) ∧
      (QpwNM n M (1 / 16) : ℝ) ≤ min ((M : ℝ) - 1) (min (C * gmrRate n M) (C * (n : ℝ) ^ 2)) := by
  obtain ⟨C₀, hC₀⟩ := hGMR
  refine ⟨max C₀ 82944, by simp, fun n M hn hM => ?_⟩
  have hclass : ∀ F : Finset (Str n → ℝ), F.card ≤ M → (∀ μ ∈ F, IsDist μ) →
      (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) ≤
        min ((M : ℝ) - 1) (min (max C₀ 82944 * gmrRate n M) (max C₀ 82944 * (n : ℝ) ^ 2)) := by
    intro F hFM hF
    have hrate : 0 ≤ gmrRate n M := by
      unfold gmrRate
      have : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
      have : 0 ≤ Real.log (2 + Real.log M) := Real.log_nonneg (by linarith)
      positivity
    refine le_min ?_ (le_min ?_ ?_)
    · have := Qpw_le_sub_one hF hFM (δ := 1 / 16) (by norm_num)
      have h1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [← h1]
      exact_mod_cast this
    · obtain ⟨q, A, hA, hq⟩ := hC₀ n M hn hM F hFM hF
      have h1 : (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) ≤ q := by exact_mod_cast Qcx_le hA
      have h2 : C₀ * n * Real.sqrt (Real.log M) * Real.log (2 + Real.log M) =
          C₀ * gmrRate n M := by unfold gmrRate; ring
      have h3 : C₀ * gmrRate n M ≤ max C₀ 82944 * gmrRate n M :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hrate
      linarith
    · have := Branching.Qpw_le_sq (by omega) (F : Set (Str n → ℝ)) hF
      have h1 : (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) ≤ 82944 * (n : ℝ) ^ 2 := by
        exact_mod_cast this
      have h2 : 82944 * (n : ℝ) ^ 2 ≤ max C₀ 82944 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      linarith
  exact ⟨hclass, QpwNM_le_of_forall fun F hFM hF => hclass F hFM hF⟩

theorem half_le_Ln (hn : 2 ≤ n) : 1 ≤ 2 * Ln n := by
  unfold Ln
  have h2 : Real.log 2 ≤ Real.log (2 * n) :=
    Real.log_le_log (by norm_num) (by have : (2 : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
  have := Real.log_two_gt_d9
  linarith

/-- If `n√(log M) ≤ n²` then `log(2 + log M) ≤ 2 log(2n)`. -/
theorem log_two_add_le (hn : 2 ≤ n) {M : ℕ} (hM : 1 ≤ M)
    (hX : (n : ℝ) * Real.sqrt (Real.log M) ≤ (n : ℝ) ^ 2) :
    Real.log (2 + Real.log M) ≤ 2 * Ln n := by
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := (by exact_mod_cast hn); linarith
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hs : Real.sqrt (Real.log M) ≤ n := by
    rw [sq] at hX
    exact le_of_mul_le_mul_left hX hnpos
  have hlogM : Real.log M ≤ (n : ℝ) ^ 2 := by
    have := Real.sq_sqrt hlog0
    nlinarith [Real.sqrt_nonneg (Real.log M)]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 2 + Real.log M ≤ (2 * (n : ℝ)) ^ 2 := by nlinarith
  unfold Ln
  calc Real.log (2 + Real.log M) ≤ Real.log ((2 * (n : ℝ)) ^ 2) :=
        Real.log_le_log (by linarith) h1
    _ = 2 * Real.log (2 * n) := by rw [Real.log_pow]; norm_num

/-- `thm:pointwise` (upper bound proof): the case analysis "If `K(n,M) = M` ... `= n²` ...
`= n√(log M)`": the three-term minimum
with the `log(2 + log M)` factor is at most `2 L_n K(n,M)`. -/
theorem min_rate_le (hn : 2 ≤ n) {M : ℕ} (hM : 1 ≤ M) :
    min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ 2 * Ln n * Krate n M := by
  have hL := half_le_Ln hn
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hX0 : 0 ≤ (n : ℝ) * Real.sqrt (Real.log M) := by positivity
  have hK0 : 0 ≤ Krate n M := by unfold Krate; positivity
  unfold Krate
  rcases min_choice (M : ℝ) (min ((n : ℝ) * Real.sqrt (Real.log M)) ((n : ℝ) ^ 2)) with hk | hk
  · rw [hk]
    calc min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ M := min_le_left _ _
      _ ≤ 2 * Ln n * M := le_mul_of_one_le_left (by positivity) hL
  · rw [hk]
    rcases min_choice ((n : ℝ) * Real.sqrt (Real.log M)) ((n : ℝ) ^ 2) with hk' | hk'
    · rw [hk']
      have hXN : (n : ℝ) * Real.sqrt (Real.log M) ≤ (n : ℝ) ^ 2 := by
        rw [← hk']; exact min_le_right _ _
      have hl := log_two_add_le hn hM hXN
      calc min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ gmrRate n M :=
            (min_le_right _ _).trans (min_le_left _ _)
        _ = (n : ℝ) * Real.sqrt (Real.log M) * Real.log (2 + Real.log M) := rfl
        _ ≤ (n : ℝ) * Real.sqrt (Real.log M) * (2 * Ln n) :=
            mul_le_mul_of_nonneg_left hl hX0
        _ = 2 * Ln n * ((n : ℝ) * Real.sqrt (Real.log M)) := by ring
    · rw [hk']
      calc min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ (n : ℝ) ^ 2 :=
            (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ 2 * Ln n * (n : ℝ) ^ 2 := le_mul_of_one_le_left (by positivity) hL

/-- `thm:pointwise`, equation `eq:pw-main` (upper inequalities): under `GMRUpperBound`, there are
absolute constants `c₁, c₂ > 0` such that for all `n, M ≥ 2`,
`Q_pw(n,M,1/16) ≤ c₁ min{M, n√(log M) log(2 + log M), n²} ≤ c₂ L_n K(n,M)`. -/
theorem pw_main_upper (hGMR : GMRUpperBound) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
      (QpwNM n M (1 / 16) : ℝ) ≤ c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ∧
      c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ c₂ * Ln n * Krate n M := by
  obtain ⟨C, hC, hup⟩ := pw_upper hGMR
  refine ⟨C, 2 * C, by linarith, by linarith, fun n M hn hM => ⟨?_, ?_⟩⟩
  · refine (hup n M hn hM).2.trans ?_
    rw [mul_min_of_nonneg _ _ (by linarith), mul_min_of_nonneg _ _ (by linarith)]
    refine min_le_min ?_ le_rfl
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  · have := min_rate_le hn (by omega : 1 ≤ M)
    calc C * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2))
        ≤ C * (2 * Ln n * Krate n M) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = 2 * C * Ln n * Krate n M := by ring

/-- `eq:pw-main` (upper bound): the form `Q_pw(n,M,1/16) ≤ c₂ L_n K(n,M)`. -/
theorem pw_upper_Ln_K (hGMR : GMRUpperBound) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
      (QpwNM n M (1 / 16) : ℝ) ≤ c₂ * Ln n * Krate n M := by
  obtain ⟨c₁, c₂, -, hc₂, h⟩ := pw_main_upper hGMR
  exact ⟨c₂, hc₂, fun n M hn hM => (h n M hn hM).1.trans (h n M hn hM).2⟩

theorem two_le_floor_exp (hn : 1 ≤ n) : 2 ≤ ⌊Real.exp n⌋₊ := by
  apply Nat.le_floor
  have h1 : Real.exp 1 ≤ Real.exp n := Real.exp_le_exp.mpr (by exact_mod_cast hn)
  have := Real.exp_one_gt_d9
  push_cast
  linarith

theorem log_floor_exp_le (hn : 1 ≤ n) : Real.log ⌊Real.exp n⌋₊ ≤ n := by
  have hpos : (0 : ℝ) < ⌊Real.exp n⌋₊ := by
    have := two_le_floor_exp hn
    positivity
  calc Real.log ⌊Real.exp n⌋₊ ≤ Real.log (Real.exp n) :=
        Real.log_le_log hpos (Nat.floor_le (Real.exp_pos _).le)
    _ = n := Real.log_exp _

theorem rpow_three_halves (x : ℝ) (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `thm:pointwise`, the right inequality of `eq:pw-expn`, with the constant `c₁` of
`eq:pw-main`: under `GMRUpperBound`, `Q_pw(n,⌊eⁿ⌋,1/16) ≤ c₁ n^{3/2} log(2n)` for every `n ≥ 2`
(in particular for all sufficiently large `n`). -/
theorem pw_expn_upper (hGMR : GMRUpperBound) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
        (QpwNM n M (1 / 16) : ℝ) ≤ c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ∧
        c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ c₂ * Ln n * Krate n M) ∧
      ∀ n : ℕ, 2 ≤ n →
        (QpwNM n ⌊Real.exp n⌋₊ (1 / 16) : ℝ) ≤ c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * n) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := pw_main_upper hGMR
  refine ⟨c₁, c₂, hc₁, hc₂, h, fun n hn => ?_⟩
  set M := ⌊Real.exp n⌋₊
  have hM := two_le_floor_exp (n := n) (by omega)
  have hlogM := log_floor_exp_le (n := n) (by omega)
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := (by exact_mod_cast hn); linarith
  have hrate : gmrRate n M ≤ (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * n) := by
    rw [rpow_three_halves _ hnpos]
    unfold gmrRate
    have h1 : Real.sqrt (Real.log M) ≤ Real.sqrt n := Real.sqrt_le_sqrt hlogM
    have h2 : Real.log (2 + Real.log M) ≤ Real.log (2 * n) :=
      Real.log_le_log (by linarith) (by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
    have h3 : 0 ≤ Real.log (2 + Real.log M) := Real.log_nonneg (by linarith)
    calc (n : ℝ) * Real.sqrt (Real.log M) * Real.log (2 + Real.log M)
        ≤ (n : ℝ) * Real.sqrt n * Real.log (2 + Real.log M) := by gcongr
      _ ≤ (n : ℝ) * Real.sqrt n * Real.log (2 * n) := by gcongr
  calc (QpwNM n M (1 / 16) : ℝ) ≤ c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) :=
        (h n M hn hM).1
    _ ≤ c₁ * gmrRate n M :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hc₁.le
    _ ≤ c₁ * ((n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * n)) :=
        mul_le_mul_of_nonneg_left hrate hc₁.le
    _ = c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * n) := by ring

end Upper
end LearningGuided
