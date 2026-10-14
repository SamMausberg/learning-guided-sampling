import LearningGuided.Sec2.Tools

/-!
# Repair by a coherent correction (the display before Theorem `thm:main`)

For `R > 1`, a coherent correction `λ` of mass `B` (a nonnegative additive measure with
`λ(u) ≥ d_R(u)` at every prefix) yields the pointwise factor-`R` guide
`h̄ = (h + λ/(R-1)) / (1 + B/(R-1))` for `μ̄ = (μ + λ/(R-1)) / (1 + B/(R-1))`, exact at the leaves,
with `TV(μ̄, μ) ≤ B/(R - 1 + B)`.

The root condition `h̄(∅) = 1` holds because the mass of the correction is exactly `B = λ(∅)`;
with a correction of mass strictly less than the normalizer `B` the root value would be below one.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec4

open Sec2

variable {n : ℕ}

/-- The repaired guide `h̄ = (h + λ/(R-1))/(1 + B/(R-1))`. -/
noncomputable def repairGuide (R : ℝ) (h : Guide) (lam : Str n → ℝ) (B : ℝ) : Guide :=
  fun u => (h u + mass lam u / (R - 1)) / (1 + B / (R - 1))

/-- The repaired target `μ̄ = (μ + λ/(R-1))/(1 + B/(R-1))`. -/
noncomputable def repairTarget (R : ℝ) (μ lam : Str n → ℝ) (B : ℝ) : Str n → ℝ :=
  fun x => (μ x + lam x / (R - 1)) / (1 + B / (R - 1))

theorem mass_repairTarget (R : ℝ) (μ lam : Str n → ℝ) (B : ℝ) (u : List Bool) :
    mass (repairTarget R μ lam B) u = (mass μ u + mass lam u / (R - 1)) / (1 + B / (R - 1)) := by
  have : repairTarget R μ lam B = fun x => (1 + B / (R - 1))⁻¹ * μ x +
      ((R - 1)⁻¹ * (1 + B / (R - 1))⁻¹) * lam x := by
    funext x; unfold repairTarget; ring
  rw [this, mass_linear]
  ring

/-- `sec:construction` (repair display before `thm:main`): for `R > 1`, a guide satisfying the
access conditions for `μ`, and a coherent correction `λ` of mass exactly `B`, the repaired target
`μ̄` is a distribution, `h̄` is a pointwise factor-`R` guide for `μ̄` (in particular `h̄(∅) = 1` and
the leaves are exact), and `TV(μ̄, μ) ≤ B/(R - 1 + B)`. -/
theorem correction_repair {R : ℝ} (hR : 1 < R) {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hh : IsOracle μ h) {lam : Str n → ℝ} (hlam : IsCorrection R μ h lam) {B : ℝ}
    (hB : ∑ x, lam x = B) :
    IsDist (repairTarget R μ lam B) ∧ PwLegal R (repairTarget R μ lam B) (repairGuide R h lam B) ∧
      (∀ x : Str n, repairGuide R h lam B (List.ofFn x) = repairTarget R μ lam B x) ∧
      tv (repairTarget R μ lam B) μ ≤ B / (R - 1 + B) := by
  have hR1 : 0 < R - 1 := by linarith
  have hB0 : 0 ≤ B := hB ▸ Finset.sum_nonneg fun x _ => hlam.1 x
  have hD : 0 < 1 + B / (R - 1) := by positivity
  have hlam0 : ∀ u, 0 ≤ mass lam u := mass_nonneg hlam.1
  have hmass_nil : mass lam [] = B := by rw [mass_nil, hB]
  have hleaf : ∀ x : Str n, repairGuide R h lam B (List.ofFn x) = repairTarget R μ lam B x := by
    intro x
    simp only [repairGuide, repairTarget, hh.leaf, mass_ofFn]
  refine ⟨⟨fun x => ?_, ?_⟩, ⟨⟨fun u => ?_, ?_, hleaf, fun u hu => ?_⟩, fun u hu => ?_⟩,
    hleaf, ?_⟩
  · unfold repairTarget
    have := hμ.1 x; have := hlam.1 x
    positivity
  · unfold repairTarget
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, hμ.2, hB]
    exact div_self (ne_of_gt hD)
  · unfold repairGuide
    have := hh.nonneg u; have := hlam0 u
    positivity
  · unfold repairGuide
    rw [hh.root, hmass_nil]
    exact div_self (ne_of_gt hD)
  · unfold repairGuide
    rw [hh.long u hu, mass_eq_zero_of_long lam hu]
    simp
  · have hd := hlam.2 u hu
    unfold defect at hd
    have h1 : h u - R * mass μ u ≤ mass lam u := (le_max_left _ _).trans
      ((le_max_right _ _).trans hd)
    have h2 : mass μ u - R * h u ≤ mass lam u := (le_max_right _ _).trans
      ((le_max_right _ _).trans hd)
    rw [mass_repairTarget]
    unfold repairGuide
    have hR0 : 0 < R := by linarith
    set l := mass lam u
    set mu := mass μ u
    set hv := h u
    constructor
    · have key : (hv + l / (R - 1)) / (1 + B / (R - 1)) -
          (mu + l / (R - 1)) / (1 + B / (R - 1)) / R =
          (R * hv + l - mu) / (R * (1 + B / (R - 1))) := by
        field_simp; ring
      have : 0 ≤ (R * hv + l - mu) / (R * (1 + B / (R - 1))) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · have key : R * ((mu + l / (R - 1)) / (1 + B / (R - 1))) -
          (hv + l / (R - 1)) / (1 + B / (R - 1)) = (R * mu + l - hv) / (1 + B / (R - 1)) := by
        field_simp; ring
      have : 0 ≤ (R * mu + l - hv) / (1 + B / (R - 1)) := div_nonneg (by linarith) hD.le
      linarith
  · have hdiff : ∀ x, repairTarget R μ lam B x - μ x = (lam x - B * μ x) / (R - 1 + B) := by
      intro x
      unfold repairTarget
      field_simp
      ring
    unfold tv
    simp_rw [hdiff, abs_div, abs_of_pos (show 0 < R - 1 + B by linarith)]
    rw [← Finset.sum_div]
    have hsum : ∑ x, |lam x - B * μ x| ≤ 2 * B := by
      calc ∑ x, |lam x - B * μ x| ≤ ∑ x, (lam x + B * μ x) :=
            Finset.sum_le_sum fun x _ => by
              have := hlam.1 x; have := hμ.1 x
              rw [abs_le]; constructor <;> nlinarith
        _ = 2 * B := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.2, hB]; ring
    rw [div_div, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith

end Sec4
end LearningGuided
