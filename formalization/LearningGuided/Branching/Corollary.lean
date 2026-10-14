import LearningGuided.Branching.Theorem

/-!
# Consequences of `thm:branching` in the safe and pointwise models

* Safety `h ≤ Rμ` bounds each level sum of `h` by `R`, and each level is a cut, so stopped
  capacity at most `C` bounds each level's reciprocal sum by `C`: `A = Rn`, `B = Cn`
  (`SafeLegal.moment_A`, `SafeLegal.moment_B`).
* The branching sampler therefore solves every class of distributions in the safe model, with cap
  `q = ⌈4⌈Cn/δ²⌉Rn/δ⌉ ≤ 4RCn²/δ³ + 4Rn/δ + 1`, i.e. `O(RCn²/δ³ + Rn/δ)` queries
  (`branching_safe_solves`, `branchQ_safe_le`, `branchQ_safe_le_O`).
* A pointwise factor-`9/4` guide is safe with `R = C = 9/4`, so the cap at error `1/16` is
  exactly `82944 n²` (`branchQ_pw`, `Qpw_le_sq`, `Qsafe_le_sq`): the `n²` bound of
  `pw-prop:upper`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Branching

open Upper

variable {n : ℕ} {μ : Str n → ℝ} {h : Guide}

/-- `thm:branching` (corollary): safe legality gives the hypotheses of the theorem. -/
theorem SafeLegal.branchHyp {R C : ℝ} (hμ : IsDist μ) (hl : SafeLegal R C μ h) :
    BranchHyp μ h := by
  refine ⟨hμ, hl.1.nonneg, hl.1.root, fun u hu => ⟨fun h0 => ?_, fun hm => ?_⟩, hl.1.leaf⟩
  · by_contra hm
    exact hl.2.2.1 u hu hm h0
  · have := hl.2.1 u hu
    rw [hm, mul_zero] at this
    exact le_antisymm this (hl.1.nonneg u)

/-- `thm:branching` (corollary): safety bounds each level sum of `h` by `R`, so `A = Rn`. -/
theorem SafeLegal.moment_A {R C : ℝ} (hμ : IsDist μ) (hl : SafeLegal R C μ h) :
    ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ R * n := by
  have hlev : ∀ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ R := by
    intro t ht
    have htn : t ≤ n := (Finset.mem_range.mp ht).le
    calc ∑ u ∈ words t, h u ≤ ∑ u ∈ words t, R * mass μ u :=
          Finset.sum_le_sum fun u hu => hl.2.1 u (by rw [mem_words.mp hu]; exact htn)
      _ = R := by rw [← Finset.mul_sum, sum_mass_words μ htn, hμ.2, mul_one]
  calc ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ ∑ _t ∈ Finset.range n, R :=
        Finset.sum_le_sum hlev
    _ = R * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- `thm:branching` (corollary): each level is a cut, so capacity bounds each level's reciprocal
sum by `C`: `B = Cn`. -/
theorem SafeLegal.moment_B {R C : ℝ} (hl : SafeLegal R C μ h) :
    ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ C * n := by
  calc ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ ∑ _t ∈ Finset.Icc 1 n, C :=
        Finset.sum_le_sum fun t ht => hl.2.2.2 (words t) (isCut_words (Finset.mem_Icc.mp ht).2)
    _ = C * n := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp

/-- `thm:branching` in the safe model: with `A = Rn` and `B = Cn`, the branching sampler solves
every class of distributions at error `δ` with cap `q = ⌈4⌈Cn/δ²⌉Rn/δ⌉`. -/
theorem branching_safe_solves {R C : ℝ} (hn : 1 ≤ n) (F : Set (Str n → ℝ))
    (hF : ∀ μ ∈ F, IsDist μ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Solves (SafeLegal R C) F δ (branchQ (R * n) (C * n) δ) (branchAlg n (R * n) (C * n) δ) := by
  intro μ hμF h hl
  have H := SafeLegal.branchHyp (hF μ hμF) hl
  exact branching hn H.dist H.nonneg H.root H.supp H.leaf (SafeLegal.moment_A (hF μ hμF) hl)
    (SafeLegal.moment_B hl) hδ0 hδ1

/-- `thm:branching` (corollary): the cap in the safe model, `q ≤ 4RCn²/δ³ + 4Rn/δ + 1`. -/
theorem branchQ_safe_le {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    (branchQ (R * n) (C * n) δ : ℝ) ≤
      4 * R * C * (n : ℝ) ^ 2 / δ ^ 3 + 4 * R * n / δ + 1 := by
  have hP : (branchP (C * n) δ : ℝ) ≤ C * n / δ ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hq : (branchQ (R * n) (C * n) δ : ℝ) ≤ 4 * branchP (C * n) δ * (R * n) / δ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have h1 : 4 * (branchP (C * n) δ : ℝ) * (R * n) / δ ≤ 4 * (C * n / δ ^ 2 + 1) * (R * n) / δ := by
    gcongr
  have h2 : 4 * (C * n / δ ^ 2 + 1) * (R * n) / δ =
      4 * R * C * (n : ℝ) ^ 2 / δ ^ 3 + 4 * R * n / δ := by
    field_simp
  linarith

/-- `thm:branching` (corollary): the `O(RCn²/δ³ + Rn/δ)` form of the cap, for `R ≥ 1`, `C ≥ 0`,
`n ≥ 1` and `0 < δ ≤ 1`. -/
theorem branchQ_safe_le_O {R C : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hn : 1 ≤ n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (branchQ (R * n) (C * n) δ : ℝ) ≤ 5 * (R * C * (n : ℝ) ^ 2 / δ ^ 3 + R * n / δ) := by
  have h := branchQ_safe_le (n := n) (R := R) (C := C) (by linarith) hC hδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ R * n / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have h2 : 0 ≤ R * C * (n : ℝ) ^ 2 / δ ^ 3 := by
    have : 0 ≤ R := by linarith
    positivity
  have e1 : 4 * R * C * (n : ℝ) ^ 2 / δ ^ 3 = 4 * (R * C * (n : ℝ) ^ 2 / δ ^ 3) := by ring
  have e2 : 4 * R * (n : ℝ) / δ = 4 * (R * n / δ) := by ring
  linarith

/-- `thm:branching` (corollary): the safe-model complexity of every class of distributions is at
most the branching cap. -/
theorem Qcx_safe_le_branchQ {R C : ℝ} (hn : 1 ≤ n) (F : Set (Str n → ℝ))
    (hF : ∀ μ ∈ F, IsDist μ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Qcx (SafeLegal R C) F δ ≤ branchQ (R * n) (C * n) δ :=
  Qcx_le (branching_safe_solves hn F hF hδ0 hδ1)

/-- `pw-prop:upper` (last bound): with `R = C = 9/4` and `δ = 1/16`, the cap is `q = 82944 n²`
(`P = 576 n`). -/
theorem branchQ_pw (n : ℕ) :
    branchQ ((9 / 4 : ℝ) * n) ((9 / 4 : ℝ) * n) (1 / 16) = 82944 * n ^ 2 := by
  have hP : branchP ((9 / 4 : ℝ) * n) (1 / 16) = 576 * n := by
    unfold branchP
    have : (9 / 4 : ℝ) * n / (1 / 16) ^ 2 = ((576 * n : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.ceil_natCast]
  unfold branchQ
  rw [hP]
  have : 4 * ((576 * n : ℕ) : ℝ) * ((9 / 4 : ℝ) * n) / (1 / 16) = ((82944 * n ^ 2 : ℕ) : ℝ) := by
    push_cast; ring
  rw [this, Nat.ceil_natCast]

/-- `thm:branching` (corollary): the safe model at `R = C = 9/4`, `Q_safe(F,1/16) ≤ 82944 n²` for
every class of
distributions. -/
theorem Qsafe_le_sq (hn : 1 ≤ n) (F : Set (Str n → ℝ)) (hF : ∀ μ ∈ F, IsDist μ) :
    Qsafe F (1 / 16) ≤ 82944 * n ^ 2 := by
  have := Qcx_safe_le_branchQ (R := 9 / 4) (C := 9 / 4) (δ := 1 / 16) hn F hF (by norm_num)
    (by norm_num)
  rwa [branchQ_pw] at this

/-- `pw-prop:upper` (last bound): the pointwise branching solver; a pointwise factor-`9/4` guide is
safe with `R = C = 9/4`,
so the branching sampler solves every class at error `1/16` with cap `82944 n²`. -/
theorem branching_pw_solves (hn : 1 ≤ n) (F : Set (Str n → ℝ)) (hF : ∀ μ ∈ F, IsDist μ) :
    Solves (PwLegal (9 / 4)) F (1 / 16) (82944 * n ^ 2)
      (branchAlg n ((9 / 4 : ℝ) * n) ((9 / 4 : ℝ) * n) (1 / 16)) := by
  intro μ hμF h hl
  have := branching_safe_solves (R := 9 / 4) (C := 9 / 4) hn F hF (δ := 1 / 16) (by norm_num)
    (by norm_num) μ hμF h (hl.safeLegal (by norm_num) (hF μ hμF))
  rwa [branchQ_pw] at this

/-- `pw-prop:upper` (last bound): `Q_pw(F,1/16) ≤ 82944 n²` for every class of
distributions on `n ≥ 1` bits. -/
theorem Qpw_le_sq (hn : 1 ≤ n) (F : Set (Str n → ℝ)) (hF : ∀ μ ∈ F, IsDist μ) :
    Qpw F (1 / 16) ≤ 82944 * n ^ 2 :=
  Qcx_le (branching_pw_solves hn F hF)

end Branching
end LearningGuided
