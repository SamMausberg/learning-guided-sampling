import LearningGuided.Sec4.Certification
import LearningGuided.Sec4.Repair

/-!
# Theorem `thm:main`: precision and certificate access

The statement collected from `Sampling.lean`, `Capacity.lean` and `Certification.lean`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec4

open Sec2

variable {m : ℕ}

theorem Fm_ncard (m : ℕ) : (Fm m).ncard = 4 ^ m := by
  unfold Fm
  rw [← Set.image_univ, Set.ncard_image_of_injective _ (muθ_injective m), Set.ncard_univ,
    Nat.card_eq_fintype_card, card_keys]

/-- `thm:main`: for every integer `m ≥ 3`, with `M = 4^m`, `n = 3m + 2`, `α = 2^{-m}` and
`δ_m = α/4`, the explicit class `F_m` has `M` full-support members and
* `eq:point-exact`: `m ≤ Q_pw(F_m,δ_m) ≤ Q_pw(F_m,0) ≤ m + 5`;
* `eq:safe-exact`: `Q_safe(F_m,δ_m) = 3·2^{m-2}` and `Q_safe(F_m,0) = 2^m`;
* the hard safe guides are positive, have mass one at every depth, satisfy `h(ub) ≤ 2h(u)`,
  `h ≤ 2μ`, and are legal with `R = C = 9/4`;
* `eq:dstar`: the minimum coherent correction mass is `d_m = α - (5/4 + α)/M > 0`;
* `eq:cert-tradeoff`: for `B ≥ d_m` and every cap `q`, the largest uniformly guaranteed success
  probability of returning a valid correction of mass at most `B` is exactly
  `min {1, (q + ⌊B/d_m⌋)/M}`;
* producing an optimal-mass correction with certainty requires exactly `M - 1` queries. -/
theorem thm_main (hm : 3 ≤ m) :
    (Fm m).ncard = 4 ^ m ∧ (∀ μ ∈ Fm m, IsDist μ ∧ ∀ x, 0 < μ x) ∧
    (m ≤ Qpw (Fm m) (deltaM m) ∧ Qpw (Fm m) (deltaM m) ≤ Qpw (Fm m) 0 ∧
      Qpw (Fm m) 0 ≤ m + 5) ∧
    (Qsafe (Fm m) (deltaM m) = 3 * 2 ^ (m - 2) ∧ Qsafe (Fm m) 0 = 2 ^ m) ∧
    (∀ θ : Str (2 * m), (∀ u : List Bool, u.length ≤ 3 * m + 2 → 0 < hθ m θ u) ∧
      (∀ t ≤ 3 * m + 2, ∑ u ∈ words t, hθ m θ u = 1) ∧
      (∀ u : List Bool, u.length < 3 * m + 2 → ∀ c : Bool, hθ m θ (u ++ [c]) ≤ 2 * hθ m θ u) ∧
      (∀ u : List Bool, u.length ≤ 3 * m + 2 → hθ m θ u ≤ 2 * mass (muθ m θ) u) ∧
      SafeLegal (9 / 4) (9 / 4) (muθ m θ) (hθ m θ)) ∧
    (dm m = alpha m - (5 / 4 + alpha m) / 4 ^ m ∧ 0 < dm m ∧ ∀ θ : Str (2 * m),
      (∃ κ, IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ ∧ ∑ x, κ x = dm m) ∧
      ∀ κ, IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ → dm m ≤ ∑ x, κ x) ∧
    (∀ B : ℝ, dm m ≤ B → ∀ q : ℕ,
      (∀ A : Alg (Str (3 * m + 2) → ℝ), (∀ θ, A.Within (hθ m θ) q) →
        ∃ θ, (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal ≤
          min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m)) ∧
      ∃ A : Alg (Str (3 * m + 2) → ℝ), (∀ θ, A.Within (hθ m θ) q) ∧
        ∀ θ, (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal =
          min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m)) ∧
    QcertHard m = 4 ^ m - 1 := by
  refine ⟨Fm_ncard m, fun μ hμ => ?_, point_exact hm, safe_exact hm, fun θ => ?_,
    ⟨rfl, dm_pos hm, fun θ => ⟨⟨optCorr m θ, isCorrection_optCorr hm θ, sum_optCorr θ⟩,
      fun _ hκ => correction_mass_ge hm θ hκ⟩⟩,
    fun B hB q => cert_tradeoff hm B hB q, cert_certainty hm⟩
  · obtain ⟨θ, rfl⟩ := hμ
    exact ⟨isDist_muθ m θ, muθ_pos (by omega) θ⟩
  · obtain ⟨-, hpos, hlev, h2, hgr, -⟩ := lem_capacity hm θ
    exact ⟨hpos, hlev, hgr, h2, safeLegal_hθ hm θ⟩

/-- Remark after `thm:main`: at tolerance `δ ≥ α` the class needs no queries, since the uniform
background is within `α` of every target: `Q_pw(F_m,δ) = Q_safe(F_m,δ) = 0`. -/
theorem zero_queries {δ : ℝ} (hδ : alpha m ≤ δ) : Qpw (Fm m) δ = 0 ∧ Qsafe (Fm m) δ = 0 := by
  have htv : ∀ θ : Str (2 * m), tv (unif (3 * m + 2)) (muθ m θ) ≤ alpha m := by
    intro θ
    have e : unif (3 * m + 2) = mixD (unif (3 * m + 2)) 0 (xθ m θ) := by
      funext x; simp [mixD]
    rw [e, muθ]
    refine (tv_mixD_le (isDist_unif _) _ _ _).trans ?_
    rw [zero_sub, abs_neg, abs_of_pos (alpha_pos m)]
  have hsolve : ∀ Legal : (Str (3 * m + 2) → ℝ) → Guide → Prop,
      Solves Legal (Fm m) δ 0 (drawUnif (3 * m + 2)) := by
    rintro Legal μ ⟨θ, rfl⟩ h _
    exact ⟨within_drawUnif _ h, by rw [lawR_drawUnif]; exact (htv θ).trans hδ⟩
  exact ⟨Nat.le_zero.mp (Qcx_le (hsolve _)), Nat.le_zero.mp (Qcx_le (hsolve _))⟩

end Sec4
end LearningGuided
