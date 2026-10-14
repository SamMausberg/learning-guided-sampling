import LearningGuided.PointwiseLB.Main
import LearningGuided.Upper.Pointwise
import LearningGuided.Upper.Safe
import LearningGuided.Sec5.FixedCert

/-!
# The headline statements, assembled

This file combines the lower bounds of Appendix `app:pointwise` (`PointwiseLB`) with the upper
bounds (`Upper`, `Branching`, `Frontier`) and the composition corollary (`Sec5`).

* `thm_pointwise_lower_Q`: the lower halves of `eq:pw-main` and `eq:pw-expn` for the worst-case
  complexity `Q_pw(n,M,1/16)`, unconditionally.
* `thm_pointwise`: Theorem `thm:pointwise` in full. Its upper half uses the explicit hypothesis
  `Upper.GMRUpperBound` (Golowich, Moitra and Rohatgi, Theorem 3.2, at error `1/16`).
* `cor_fixed_cert_instance`: Corollary `cor:fixed-cert` for the smoothed class of Appendix
  `app:pointwise`. Its upper half on `Q_⊗` uses `Upper.GMRUpperBoundAt (1/32)`.
* `fixed_gap`: the bounds `eq:fixed-gap` of Section `sec:remaining`, unconditionally.
-/

open scoped BigOperators

namespace LearningGuided
namespace Main

open Upper

/-- A lower bound that holds for every solver of a class of at most `M` distributions is a lower
bound on the worst-case complexity `Q_pw(n,M,1/16)`. -/
theorem le_QpwNM_of_lower {n M : ℕ} {F : Finset (Str n → ℝ)} (hFM : F.card ≤ M)
    (hF : ∀ μ ∈ F, IsDist μ) {x : ℝ}
    (h : ∀ q A, Solves (PwLegal (9 / 4)) (F : Set (Str n → ℝ)) (1 / 16) q A → x ≤ q) :
    x ≤ (QpwNM n M (1 / 16) : ℝ) := by
  have hex := exists_solves_finite (Legal := PwLegal (9 / 4)) (fun _ _ hl => hl.1) F hF
    (δ := 1 / 16) (by norm_num)
  have h1 : x ≤ (Qpw (F : Set (Str n → ℝ)) (1 / 16) : ℝ) := PointwiseLB.le_Qpw_of_lower hex h
  have h2 : Qpw (F : Set (Str n → ℝ)) (1 / 16) ≤ QpwNM n M (1 / 16) :=
    le_QcxNM (Legal := PwLegal (9 / 4)) (fun _ _ hl => hl.1) (by norm_num) hFM hF
  exact h1.trans (by exact_mod_cast h2)

/-- `thm:pointwise`, equations `eq:pw-main` and `eq:pw-expn` (lower inequalities), for the
worst-case complexity: there is an absolute `c₀ > 0` with
`(c₀/L_n) K(n,M) ≤ Q_pw(n,M,1/16)` for all `n, M ≥ 2`, and
`c₀ n^{3/2}/√(log(2n)) ≤ Q_pw(n,⌊eⁿ⌋,1/16)` for all sufficiently large `n`. No hypothesis. -/
theorem thm_pointwise_lower_Q :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ n M : ℕ, 2 ≤ n → 2 ≤ M → c₀ / Ln n * Krate n M ≤ (QpwNM n M (1 / 16) : ℝ)) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c₀ * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n)) ≤
          (QpwNM n ⌊Real.exp n⌋₊ (1 / 16) : ℝ) := by
  obtain ⟨c₀, hc₀, hmain, n₀, hexp⟩ := PointwiseLB.thm_pointwise_lower
  refine ⟨c₀, hc₀, fun n M hn hM => ?_, n₀, fun n hn => ?_⟩
  · obtain ⟨F, hFM, hF, hlow⟩ := hmain n M hn hM
    exact le_QpwNM_of_lower hFM hF hlow
  · obtain ⟨F, hFM, hF, hlow⟩ := hexp n hn
    exact le_QpwNM_of_lower hFM hF hlow

/-- `thm:pointwise` (Theorem 1.1), equations `eq:pw-main` and `eq:pw-expn`, under the explicit
hypothesis `GMRUpperBound` (Golowich–Moitra–Rohatgi, Theorem 3.2, at ratio `9/4`, binary
alphabet and error `1/16`): there are absolute constants `c₀, c₁, c₂ > 0` with
`(c₀/L_n) K(n,M) ≤ Q_pw(n,M,1/16) ≤ c₁ min{M, n√(log M) log(2+log M), n²} ≤ c₂ L_n K(n,M)` for all
`n, M ≥ 2`, and `c₀ n^{3/2}/√(log(2n)) ≤ Q_pw(n,⌊eⁿ⌋,1/16) ≤ c₁ n^{3/2} log(2n)` for all
sufficiently large `n`. The lower bounds do not use the hypothesis
(`thm_pointwise_lower_Q`). -/
theorem thm_pointwise (hGMR : GMRUpperBound) :
    ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
        c₀ / Ln n * Krate n M ≤ (QpwNM n M (1 / 16) : ℝ) ∧
        (QpwNM n M (1 / 16) : ℝ) ≤ c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ∧
        c₁ * min (M : ℝ) (min (gmrRate n M) ((n : ℝ) ^ 2)) ≤ c₂ * Ln n * Krate n M) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c₀ * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n)) ≤
          (QpwNM n ⌊Real.exp n⌋₊ (1 / 16) : ℝ) ∧
        (QpwNM n ⌊Real.exp n⌋₊ (1 / 16) : ℝ) ≤ c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * n) := by
  obtain ⟨c₀, hc₀, hlow, n₀, hlowe⟩ := thm_pointwise_lower_Q
  obtain ⟨c₁, c₂, hc₁, hc₂, hmain, hexp⟩ := pw_expn_upper hGMR
  refine ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, fun n M hn hM => ⟨hlow n M hn hM, hmain n M hn hM⟩,
    max n₀ 2, fun n hn => ⟨hlowe n (le_of_max_le_left hn), hexp n (le_of_max_le_right hn)⟩⟩

/-- The upper input of `cor:fixed-cert`: under `GMRUpperBoundAt δ`, every nonempty class of at
most `eᵐ` distributions on `m ≥ 2` bits has `Q_pw` at error `δ` at most `c₁ m^{3/2} log(2m)`. -/
theorem qpw_upper_of_gmr {δ : ℝ} (hδ : 0 ≤ δ) (hG : GMRUpperBoundAt δ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ m : ℕ, 2 ≤ m → ∀ P : Finset (Str m → ℝ), P.Nonempty →
      (∀ μ ∈ P, IsDist μ) → (P.card : ℝ) ≤ Real.exp m →
      (Qcx (PwLegal (9 / 4)) (P : Set (Str m → ℝ)) δ : ℝ) ≤
        c₁ * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m) := by
  obtain ⟨C₀, hC₀⟩ := hG
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun m hm P hne hP hcard => ?_⟩
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog2m : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  have hpow : (m : ℝ) ^ ((3 : ℝ) / 2) = m * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hm0.le (by norm_num)]
    norm_num
  have hrhs : 0 ≤ max C₀ 1 * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m) :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (by positivity)) hlog2m
  rcases Nat.lt_or_ge P.card 2 with hc | hc
  · obtain ⟨μ, hμ⟩ := hne
    have hPμ : P = {μ} := by
      have h1 : P.card = 1 := by have := Finset.card_pos.mpr ⟨μ, hμ⟩; omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      rw [ha] at hμ ⊢
      rw [Finset.mem_singleton.mp hμ]
    rw [hPμ, Finset.coe_singleton, Upper.Qcx_singleton (hP μ hμ) hδ]
    simpa using hrhs
  · obtain ⟨q, A, hA, hq⟩ := hC₀ m P.card hm hc P le_rfl hP
    have hQ : (Qcx (PwLegal (9 / 4)) (P : Set (Str m → ℝ)) δ : ℝ) ≤ q := by
      exact_mod_cast Qcx_le hA
    have hc2 : (2 : ℝ) ≤ P.card := by exact_mod_cast hc
    have hlogc : 0 < Real.log P.card := Real.log_pos (by linarith)
    have hlogm : Real.log P.card ≤ m := by
      rw [Real.log_le_iff_le_exp (by linarith)]
      exact hcard
    have hsq : Real.sqrt (Real.log P.card) ≤ Real.sqrt m := Real.sqrt_le_sqrt hlogm
    have hl2 : Real.log (2 + Real.log P.card) ≤ Real.log (2 * m) :=
      Real.log_le_log (by linarith) (by linarith)
    have hl2pos : 0 ≤ Real.log (2 + Real.log P.card) := Real.log_nonneg (by linarith)
    have hX : (m : ℝ) * Real.sqrt (Real.log P.card) * Real.log (2 + Real.log P.card) ≤
        (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m) := by
      rw [hpow]
      have := mul_le_mul_of_nonneg_left hsq hm0.le
      exact mul_le_mul this hl2 hl2pos (by positivity)
    have hX0 : 0 ≤ (m : ℝ) * Real.sqrt (Real.log P.card) * Real.log (2 + Real.log P.card) := by
      positivity
    calc (Qcx (PwLegal (9 / 4)) (P : Set (Str m → ℝ)) δ : ℝ) ≤ q := hQ
      _ ≤ C₀ * m * Real.sqrt (Real.log P.card) * Real.log (2 + Real.log P.card) := hq
      _ = C₀ * ((m : ℝ) * Real.sqrt (Real.log P.card) * Real.log (2 + Real.log P.card)) := by
          ring
      _ ≤ max C₀ 1 * ((m : ℝ) * Real.sqrt (Real.log P.card) *
            Real.log (2 + Real.log P.card)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
      _ ≤ max C₀ 1 * ((m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m)) :=
          mul_le_mul_of_nonneg_left hX (le_trans zero_le_one (le_max_right _ _))
      _ = max C₀ 1 * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m) := by ring

/-- The uniform distribution has full support. -/
theorem unif_pos (m : ℕ) (y : Str m) : 0 < unif m y := by
  unfold unif; positivity

open Sec2 Sec4 Sec5 in
/-- `cor:fixed-cert` (Corollary 5.3), instantiated with the smoothed class of Appendix
`app:pointwise` (`PointwiseLB.cor_fixed_cert_smoothed_lower`) and, for its upper half, the
explicit hypothesis `GMRUpperBoundAt (1/32)` (Golowich–Moitra–Rohatgi, Theorem 3.2, at error
`1/32`). There are full-support classes `𝒫_m` on `m` bits with `1 ≤ |𝒫_m| ≤ eᵐ`, absolute
constants `c₀, c₁ > 0` and `m₀` such that for every `m ≥ m₀` the product class `{ν ⊗ μ_θ}` on
`4m + 2` bits has full support, between `4^m` and `4^m eᵐ` members, safe product guides with
`R = C = 9/4`, `c₀ m^{3/2}/√(log(2m)) ≤ Q_⊗(𝒫_m,m,1/16) ≤ c₁ m^{3/2} log(2m)`, defect
`D_{9/4} = d_m` at every instance with `d_m → 0`, optimal-mass certification with certainty
between `M - 1` and `M + |𝒫_m| - 2` queries (between `4^m/2` and `2·4^m`), and the fixed-budget
bound `q ≥ (1-ζ)4^m - 2B 2^m`. -/
theorem cor_fixed_cert_instance (hG : GMRUpperBoundAt (1 / 32)) :
    ∃ (Pf : ∀ m : ℕ, Finset (Str m → ℝ)) (c₀ c₁ : ℝ) (m₀ : ℕ), 0 < c₀ ∧ 0 < c₁ ∧
      (∀ m, ∀ ν ∈ Pf m, IsDist ν ∧ ∀ x, 0 < ν x) ∧ (∀ m, (Pf m).Nonempty) ∧
      (∀ m : ℕ, ((Pf m).card : ℝ) ≤ Real.exp m) ∧
      Filter.Tendsto dm Filter.atTop (nhds 0) ∧
      ∀ m ≥ m₀,
      m + (3 * m + 2) = 4 * m + 2 ∧
      (∀ μ ∈ prodClass (Pf m : Set (Str m → ℝ)) m, IsDist μ ∧ ∀ z, 0 < μ z) ∧
      ((4 : ℝ) ^ m ≤ (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ∧
        ((prodClass (Pf m : Set (Str m → ℝ)) m).ncard : ℝ) ≤ 4 ^ m * Real.exp m) ∧
      (m * Real.log 4 ≤ Real.log (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ∧
        Real.log (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ≤ m * (Real.log 4 + 1)) ∧
      (∀ μ H, ProdLegal (Pf m : Set (Str m → ℝ)) m μ H → SafeLegal (9 / 4) (9 / 4) μ H) ∧
      (c₀ * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m)) ≤
          (Qprod (Pf m : Set (Str m → ℝ)) m (1 / 16) : ℝ) ∧
        (Qprod (Pf m : Set (Str m → ℝ)) m (1 / 16) : ℝ) ≤
          c₁ * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m)) ∧
      (∀ μ H, ProdLegal (Pf m : Set (Str m → ℝ)) m μ H → DefectEq (9 / 4) μ H (dm m)) ∧
      (4 ^ m - 1 ≤ QcertProd (Pf m) m ∧ QcertProd (Pf m) m ≤ 4 ^ m + (Pf m).card - 2) ∧
      ((4 : ℝ) ^ m / 2 ≤ QcertProd (Pf m) m ∧ (QcertProd (Pf m) m : ℝ) ≤ 2 * 4 ^ m) ∧
      (∀ ν ∈ Pf m, ∀ g, PwLegal (9 / 4) ν g → ∀ (B : ℝ), 0 ≤ B → ∀ (ζ : ℝ) (q : ℕ)
        (A : Alg (Str (m + (3 * m + 2)) → ℝ)),
        (∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q) →
        (∀ θ : Str (2 * m),
          1 - ζ ≤ (probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ B)).toReal) →
        (1 - ζ) * 4 ^ m - 2 * B * 2 ^ m ≤ q) := by
  classical
  obtain ⟨c₀, hc₀, m₁, hsm⟩ := PointwiseLB.cor_fixed_cert_smoothed_lower
  obtain ⟨c₁, hc₁, hup⟩ := qpw_upper_of_gmr (by norm_num) hG
  let Pf : ∀ m : ℕ, Finset (Str m → ℝ) := fun m =>
    if h : m₁ ≤ m then Classical.choose (hsm m h) else {unif m}
  have hPf : ∀ m, (∀ ν ∈ Pf m, IsDist ν ∧ ∀ x, 0 < ν x) ∧ (Pf m).Nonempty ∧
      ((Pf m).card : ℝ) ≤ Real.exp m := by
    intro m
    by_cases h : m₁ ≤ m
    · have hs := Classical.choose_spec (hsm m h)
      simp only [Pf, h, ↓reduceDIte]
      exact ⟨hs.2.1, hs.1, hs.2.2.1⟩
    · simp only [Pf, h, ↓reduceDIte]
      refine ⟨fun ν hν => ?_, Finset.singleton_nonempty _, ?_⟩
      · rw [Finset.mem_singleton.mp hν]
        exact ⟨isDist_unif m, unif_pos m⟩
      · simp only [Finset.card_singleton, Nat.cast_one]
        exact Real.one_le_exp (Nat.cast_nonneg m)
  have hlow : ∀ m ≥ max m₁ 2, c₀ * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m)) ≤
      (Qpw (Pf m : Set (Str m → ℝ)) (1 / 16) : ℝ) := by
    intro m hm
    have h : m₁ ≤ m := le_of_max_le_left hm
    have hs := Classical.choose_spec (hsm m h)
    have hP : Pf m = Classical.choose (hsm m h) := by simp only [Pf, h, ↓reduceDIte]
    rw [hP]
    have hex := exists_solves_finite (Legal := PwLegal (9 / 4)) (fun _ _ hl => hl.1)
      (Classical.choose (hsm m h)) (fun μ hμ => (hs.2.1 μ hμ).1) (δ := 1 / 16) (by norm_num)
    exact PointwiseLB.le_Qpw_of_lower hex hs.2.2.2
  have hupp : ∀ m ≥ max m₁ 2, (Qpw (Pf m : Set (Str m → ℝ)) (1 / 32) : ℝ) ≤
      c₁ * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m) := by
    intro m hm
    exact hup m (le_of_max_le_right hm) (Pf m) (hPf m).2.1 (fun μ hμ => ((hPf m).1 μ hμ).1)
      (hPf m).2.2
  refine ⟨Pf, c₀, c₁, max (max m₁ 2) 5, hc₀, hc₁, fun m => (hPf m).1, fun m => (hPf m).2.1,
    fun m => (hPf m).2.2, dm_tendsto, ?_⟩
  exact cor_fixed_cert Pf (fun m ν hν => ((hPf m).1 ν hν).1) (fun m ν hν => ((hPf m).1 ν hν).2)
    (fun m => (hPf m).2.1) (fun m => (hPf m).2.2) c₀ c₁ (max m₁ 2) hlow hupp

/-- `sec:remaining`, equation `eq:fixed-gap`: for `R = C = 9/4` and `0 < δ ≤ 1/16`, there is an
absolute `c₀ > 0` with `(c₀/L_n) K(n,M) ≤ Q_safe(n,M,δ)` for all `n, M ≥ 2` (from the pointwise
submodel), and `Q_safe(n,M,δ)` is at most each of `M - 1` (exact identification), the frontier
learner's cap `2n(J₀T+J)` of Appendix `app:frontier`, and the branching cap of Theorem
`thm:branching` with `A = B = 9n/4`. No hypothesis. -/
theorem fixed_gap :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 → ∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
      c₀ / Ln n * Krate n M ≤ (QsafeNM n M δ : ℝ) ∧
      QsafeNM n M δ ≤ M - 1 ∧
      QsafeNM n M δ ≤ Frontier.frontierCap n M δ (9 / 4) (9 / 4) ∧
      QsafeNM n M δ ≤ Branching.branchQ (9 / 4 * n) (9 / 4 * n) δ := by
  obtain ⟨c₀, hc₀, hmain, -⟩ := PointwiseLB.thm_pointwise_lower
  refine ⟨c₀, hc₀, fun δ hδ0 hδ n M hn hM => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨F, hFM, hF, hlow⟩ := hmain n M hn hM
    have hex := exists_solves_finite (Legal := SafeLegal (9 / 4) (9 / 4)) (fun _ _ hl => hl.1) F
      hF hδ0.le
    have h1 : c₀ / Ln n * Krate n M ≤ (Qsafe (F : Set (Str n → ℝ)) δ : ℝ) := by
      obtain ⟨A, hA⟩ := Sec2.exists_solver_Qcx hex
      refine hlow _ A fun μ hμ h hl => ?_
      have hs := hA μ hμ h (hl.safeLegal (by norm_num) (hF μ hμ))
      exact ⟨hs.1, hs.2.trans hδ⟩
    have h2 : Qsafe (F : Set (Str n → ℝ)) δ ≤ QsafeNM n M δ :=
      le_QcxNM (Legal := SafeLegal (9 / 4) (9 / 4)) (fun _ _ hl => hl.1) hδ0.le hFM hF
    exact h1.trans (by exact_mod_cast h2)
  · exact QcxNM_le fun F hFM hF =>
      (safe_upper_bounds (by omega) hM hδ0 (by linarith) F hFM hF).1
  · exact QcxNM_le fun F hFM hF =>
      (safe_upper_bounds (by omega) hM hδ0 (by linarith) F hFM hF).2.1
  · exact QcxNM_le fun F hFM hF =>
      (safe_upper_bounds (by omega) hM hδ0 (by linarith) F hFM hF).2.2

end Main
end LearningGuided
