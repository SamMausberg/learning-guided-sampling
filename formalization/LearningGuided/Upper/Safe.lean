import LearningGuided.Frontier.Theorem
import LearningGuided.Branching.Corollary

/-!
# The three safe-model upper bounds with deterministic caps

Section `sec:remaining` (`eq:fixed-gap`) uses three upper bounds for `Q_safe`: exact
identification (`M - 1`), the frontier learner of Appendix `app:frontier` (cap `2n(J₀T + J)`,
of order `n log M` up to logarithms at fixed `δ`, `R`, `C`), and `thm:branching` (order `n²`).
This file collects them for a class of at most `M` distributions in the safe model with general
`R`, `C`, and bounds the frontier cap explicitly.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Upper

variable {n : ℕ}

/-- `eq:fixed-gap` (upper bounds): the three safe-model upper bounds; for `n ≥ 1`, `M ≥ 2`,
`0 < δ < 1` and every class of at
most `M` distributions, `Q_safe ≤ M - 1`, `Q_safe ≤ 2n(J₀T + J)` and
`Q_safe ≤ ⌈4⌈Cn/δ²⌉Rn/δ⌉`. -/
theorem safe_upper_bounds {R C : ℝ} (hn : 1 ≤ n) {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (F : Finset (Str n → ℝ)) (hFM : F.card ≤ M) (hF : ∀ μ ∈ F, IsDist μ) :
    Qcx (SafeLegal R C) (F : Set (Str n → ℝ)) δ ≤ M - 1 ∧
    Qcx (SafeLegal R C) (F : Set (Str n → ℝ)) δ ≤ Frontier.frontierCap n M δ R C ∧
    Qcx (SafeLegal R C) (F : Set (Str n → ℝ)) δ ≤ Branching.branchQ (R * n) (C * n) δ :=
  ⟨Qcx_le_sub_one (fun _ _ hl => hl.1) hF hFM hδ0.le,
    Qcx_le (Frontier.frontier hM hδ0 hδ1 F hFM hF),
    Branching.Qcx_safe_le_branchQ hn (F : Set (Str n → ℝ)) hF hδ0 hδ1⟩

/-- `app:frontier`: the frontier cap explicitly,
`2n(J₀T + J) ≤ 2n(J₀(32RC δ⁻² log(4J₀/δ) + 1) + 4R log(4/δ) + 1)` with `J₀ = 1 + ⌈log₂ M⌉`. -/
theorem frontierCap_le {R C : ℝ} (hR : 0 < R) (hC : 0 < C) (M : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    (Frontier.frontierCap n M δ R C : ℝ) ≤
      2 * n * (Frontier.J0 M * (32 * R * C / δ ^ 2 * Real.log (4 * Frontier.J0 M / δ) + 1) +
        (4 * R * Real.log (4 / δ) + 1)) := by
  have hJ0 : (1 : ℝ) ≤ Frontier.J0 M := by
    unfold Frontier.J0; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈Real.logb 2 M⌉₊]
  have hlog1 : 0 ≤ Real.log (4 * Frontier.J0 M / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]; linarith)
  have hlog2 : 0 ≤ Real.log (4 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hp0 : (Frontier.p0 δ R C)⁻¹ = 32 * R * C / δ ^ 2 := by unfold Frontier.p0; rw [inv_div]
  have hT : (Frontier.Tsc M δ R C : ℝ) ≤
      32 * R * C / δ ^ 2 * Real.log (4 * Frontier.J0 M / δ) + 1 := by
    unfold Frontier.Tsc
    rw [hp0]
    have := Nat.ceil_lt_add_one (R := ℝ) (a := 32 * R * C / δ ^ 2 *
      Real.log (4 * Frontier.J0 M / δ)) (by positivity)
    exact this.le
  have hJ : (Frontier.Jpr δ R : ℝ) ≤ 4 * R * Real.log (4 / δ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  unfold Frontier.frontierCap
  push_cast
  have hn0 : (0 : ℝ) ≤ 2 * n := by positivity
  gcongr

end Upper
end LearningGuided
