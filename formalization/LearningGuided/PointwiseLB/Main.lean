import LearningGuided.PointwiseLB.Smoothing
import LearningGuided.PointwiseLB.Injective

/-!
# Final statements of the Appendix B lower bounds

* `thm_pointwise_main_lower`: the left inequality of `eq:pw-main`,
  `(c₀/L_n) K(n,M) ≤ q` with `K(n,M) = min{M, n √(log M), n²}` and `L_n = log(2n)`.
* `thm_pointwise_expn_lower`: the left inequality of `eq:pw-expn`.
* `thm_pointwise_lower`: both with one constant `c₀ = 2^{-22}`.
* `cor_fixed_cert_smoothed_lower`: the smoothed hard class used in Corollary `cor:fixed-cert`.
* `le_Qpw_of_lower`: transfer of an "every valid algorithm" bound to `Q_pw`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-- `thm:pointwise`, left inequality of `eq:pw-main`: there is an absolute constant `c₀ > 0`
such that for all `n, M ≥ 2` there is a class of at most `M` distributions on `n` bits on which
every algorithm solving the class at error `1/16` in the pointwise factor-`9/4` model with cap
`q` satisfies `(c₀ / log(2n)) · min{M, n √(log M), n²} ≤ q`. -/
theorem thm_pointwise_main_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
      ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
        ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
          c₀ / Real.log (2 * n) *
              min (M : ℝ) (min (n * Real.sqrt (Real.log M)) ((n : ℝ) ^ 2)) ≤ q := by
  refine ⟨1 / 2 ^ 22, by norm_num, fun n M hn hM => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := Regimes.pw_main_lower n M hn hM
  refine ⟨F, h1, h2, fun q A hA => ?_⟩
  have := h3 q A hA
  unfold Regimes.Kfun at this
  rwa [min_assoc] at this

/-- `thm:pointwise`, left inequality of `eq:pw-expn`: there is an absolute constant `c₀ > 0`
such that for all sufficiently large `n` there is a class of at most `⌊eⁿ⌋` distributions on
`n` bits on which every algorithm solving the class at error `1/16` in the pointwise model with
cap `q` satisfies `c₀ n^{3/2} / √(log(2n)) ≤ q`. -/
theorem thm_pointwise_expn_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ F : Finset (Str n → ℝ), F.card ≤ ⌊Real.exp n⌋₊ ∧ (∀ μ ∈ F, IsDist μ) ∧
        ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
          c₀ * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n)) ≤ q := by
  obtain ⟨c₀, hc₀, -, hexp⟩ := Regimes.thm_pointwise_lower
  exact ⟨c₀, hc₀, hexp⟩

/-- `thm:pointwise`, both lower bounds with one absolute constant `c₀` (here `c₀ = 2^{-22}`):
the left inequality of `eq:pw-main` for all `n, M ≥ 2`, and the left inequality of
`eq:pw-expn` for all `n ≥ 4096`. -/
theorem thm_pointwise_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
        ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
          ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
            c₀ / Real.log (2 * n) *
              min (M : ℝ) (min (n * Real.sqrt (Real.log M)) ((n : ℝ) ^ 2)) ≤ q) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ F : Finset (Str n → ℝ), F.card ≤ ⌊Real.exp n⌋₊ ∧ (∀ μ ∈ F, IsDist μ) ∧
          ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
            c₀ * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n)) ≤ q := by
  obtain ⟨c₀, hc₀, hmain, hexp⟩ := Regimes.thm_pointwise_lower
  refine ⟨c₀, hc₀, fun n M hn hM => ?_, hexp⟩
  obtain ⟨F, h1, h2, h3⟩ := hmain n M hn hM
  refine ⟨F, h1, h2, fun q A hA => ?_⟩
  have := h3 q A hA
  unfold Regimes.Kfun at this
  rwa [min_assoc] at this

/-- `cor:fixed-cert`, smoothing step: there are `c₀ > 0` and `m₀` such that for every
`m ≥ m₀` there is a nonempty class of at most `e^m` full-support distributions on `m` bits (the
`7/8` mixtures `(7/8) μ_θ + (1/8) U_m` of the padded table class, with guides
`(7/8) h_θ + (1/8) 2^{-|u|}`) on which every algorithm solving the class at error `1/16` in the
pointwise factor-`9/4` model with cap `q` satisfies `c₀ m^{3/2} / √(log(2m)) ≤ q`. -/
theorem cor_fixed_cert_smoothed_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ Pc : Finset (Str m → ℝ), Pc.Nonempty ∧ (∀ μ ∈ Pc, IsDist μ ∧ ∀ y, 0 < μ y) ∧
        (Pc.card : ℝ) ≤ Real.exp m ∧
        ∀ (q : ℕ) (A : Alg (Str m)), Solves (PwLegal (9 / 4)) ↑Pc (1 / 16) q A →
          c₀ * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m)) ≤ q := by
  refine ⟨1 / 2 ^ 19, by norm_num, 4096, fun m hm => ?_⟩
  obtain ⟨F, hne, hcard, hfs, hlow⟩ := expn_smooth m hm
  refine ⟨F, hne, hfs, ?_, fun q A hA => ?_⟩
  · exact le_trans (by exact_mod_cast hcard) (Nat.floor_le (Real.exp_pos _).le)
  · have := hlow q A hA
    have hL : 0 < Real.sqrt (Real.log (2 * m)) := Real.sqrt_pos.mpr (Real.log_pos (by
      have : (4096 : ℝ) ≤ m := by exact_mod_cast hm
      linarith))
    calc 1 / 2 ^ 19 * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m))
        = (m : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt (Real.log (2 * m))) := by
          field_simp
      _ ≤ (q : ℝ) := this

/-- Transfer to `Q_pw`: a lower bound valid for every solving algorithm is a lower bound on
`Q_pw(F, 1/16)`, provided some solver exists. -/
theorem le_Qpw_of_lower {n : ℕ} {F : Set (Str n → ℝ)} {x : ℝ}
    (hex : ∃ q A, Solves (PwLegal (9 / 4)) F (1 / 16) q A)
    (h : ∀ q A, Solves (PwLegal (9 / 4)) F (1 / 16) q A → x ≤ q) : x ≤ Qpw F (1 / 16) := by
  have := le_Qcx hex (b := ⌈x⌉₊) fun q A hA => Nat.ceil_le.mpr (h q A hA)
  exact (Nat.le_ceil x).trans (by exact_mod_cast this)

end LearningGuided.PointwiseLB
