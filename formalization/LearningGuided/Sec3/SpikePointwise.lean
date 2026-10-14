import LearningGuided.Sec3.LocalLower

/-!
# Corollary `cor:spike-pointwise`: the pointwise comparison on the same class

With a pointwise factor-`R` guide, the group depth is the smallest `d` with `2^d ≥ 2R²a/α`; an
occupied prefix of depth at least `d` has `h ≥ α/R` and an empty one has `h ≤ α/(2R)`. Searching
`⌈α2^d⌉ = O(1)` groups and recovering the remaining `k-d ≤ log₂(αM)` key bits gives the upper
bound; `eq:local-information` and the zero-query obstruction give the lower bound:
`Q_pw(𝓕_{n,k,α},δ) = Θ(1 + log₂(1+αM))`.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-- The pointwise group depth: the smallest `d` with `2^d ≥ 2R²a/α`. -/
noncomputable def pwDepth (R α : ℝ) : ℕ := depthFor (2 * R ^ 2 * (1 - α) / α)

/-- `cor:spike-pointwise`, test: with a pointwise factor-`R` guide the test `h(v) ≥ α/R` is exact at
depth `≥ d`. -/
theorem pw_valid {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1) {x : Str n} {h : Guide}
    (hl : PwLegal R (atomTarget (unif n) α x) h) :
    ∀ v : List Bool, pwDepth R α ≤ v.length → v.length ≤ n → (α / R ≤ h v ↔ IsPre v x) := by
  intro v hv hvn
  refine pw_test (isDist_unif n) hR hα1.le hl hvn ?_
  rw [mass_unif hvn]
  exact pw_gap hR hα hα1 ((depthFor_spec _).trans (pow_le_pow_right₀ (by norm_num) hv))

/-- `cor:spike-pointwise`, sampler: the pointwise sampler solves `𝓕_{n,k,α}` at accuracy `δ`, with
the cap of `spikeCap` at the pointwise depth, against every pointwise factor-`R` guide. -/
theorem solves_spikeSampler_pw {R α δ : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) {k : ℕ} (hk : k ≤ n) :
    Solves (PwLegal R) (spikeClass n k α) δ (spikeCap k (pwDepth R α) (α - δ))
      (spikeSampler n k (pwDepth R α) (α / R) α (α - δ)) := by
  rintro μ ⟨θ, rfl⟩ h hl
  refine ⟨within_spikeSampler hk _ _ (by linarith) h, ?_⟩
  have hlaw : lawR ((spikeSampler n k (pwDepth R α) (α / R) α (α - δ)).run h) =
      atomTarget (unif n) (α - δ) (spikeAtom n θ) := by
    unfold spikeSampler
    split_ifs with hc
    · exact lawR_groupSpike hc.1 hk (by linarith) (by linarith) θ (pw_valid hR hα hα1 hl)
    · exact lawR_leafSampler (isDist_unif n) hα (by linarith) (by linarith) (mem_spikeSet θ) hl.1
  rw [hlaw, tv_local_output (by linarith)]
  have : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  nlinarith

/-- `cor:spike-pointwise`, upper bound for exact sampling:
`Q_pw(𝓕_{n,k,α},δ) ≤ 22 (1 + log₂(1+αM))` for every `δ ≥ 0`. -/
theorem spike_pointwise_upper {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ) {k : ℕ}
    (hk : k ≤ n) :
    (Qpw (spikeClass n k α) δ : ℝ) ≤ 22 * (1 + Real.logb 2 (1 + α * 2 ^ k)) := by
  have hsolve := solves_mono_delta hδ0 (solves_spikeSampler_pw (n := n)
    (by norm_num : (0 : ℝ) < 9 / 4) hα0 (by linarith) le_rfl hα0.le hk)
  have hQ : (Qpw (spikeClass n k α) δ : ℝ) ≤ spikeCap k (pwDepth (9 / 4) α) (α - 0) := by
    exact_mod_cast Qcx_le hsolve
  refine hQ.trans ?_
  rw [sub_zero]
  set d := pwDepth (9 / 4) α with hd
  set X : ℝ := 2 * (9 / 4) ^ 2 * (1 - α) / α with hX
  have hαX : α * X = 81 / 8 * (1 - α) := by
    rw [hX]
    field_simp
    ring
  have hA0 : 0 < α * 2 ^ k := by positivity
  have hL0 : 0 ≤ Real.logb 2 (1 + α * 2 ^ k) := Real.logb_nonneg (by norm_num) (by linarith)
  have hleaf : (⌈α * 2 ^ k⌉₊ : ℝ) ≤ α * 2 ^ k + 1 := ceil_le_add_one hA0.le
  unfold spikeCap
  split_ifs with hdk
  · have hX1 : 1 ≤ 2 * X := by
      have : (1 : ℝ) / 2 ≤ X := by
        rw [hX, le_div_iff₀ hα0]
        nlinarith
      linarith
    have h2d : (2 : ℝ) ^ d ≤ 2 * X := two_pow_depthFor_le hX1
    have hXα : α⁻¹ ≤ (2 : ℝ) ^ d := by
      refine le_trans ?_ (depthFor_spec _)
      rw [← hX, inv_le_iff_one_le_mul₀ hα0, mul_comm, hαX]
      nlinarith
    have hc1 : (⌈α * 2 ^ d⌉₊ : ℝ) ≤ 85 / 4 := by
      have h1 := ceil_le_add_one (x := α * 2 ^ d) (by positivity)
      have : α * 2 ^ d ≤ 81 / 4 := by
        calc α * 2 ^ d ≤ α * (2 * X) := mul_le_mul_of_nonneg_left h2d hα0.le
          _ = 2 * (α * X) := by ring
          _ ≤ 81 / 4 := by rw [hαX]; nlinarith
      linarith
    have hc2 : ((k - d : ℕ) : ℝ) ≤ Real.logb 2 (1 + α * 2 ^ k) := by
      rw [Nat.cast_sub hdk]
      have h1 : Real.logb 2 α⁻¹ ≤ d := by
        have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (inv_pos.mpr hα0) hXα
        rwa [logb_two_pow] at this
      have h2 : Real.logb 2 (α * 2 ^ k) = Real.logb 2 α + k := by
        rw [Real.logb_mul hα0.ne' (by positivity), logb_two_pow]
      have h3 : Real.logb 2 (α * 2 ^ k) ≤ Real.logb 2 (1 + α * 2 ^ k) :=
        Real.logb_le_logb_of_le (by norm_num) hA0 (by linarith)
      rw [Real.logb_inv] at h1
      linarith
    have : ((min ⌈α * 2 ^ k⌉₊ (⌈α * 2 ^ d⌉₊ + (k - d)) : ℕ) : ℝ) ≤
        ⌈α * 2 ^ d⌉₊ + ((k - d : ℕ) : ℝ) := by
      push_cast
      exact min_le_right _ _
    linarith
  · have hkX : (2 : ℝ) ^ k < X := by
      by_contra hc
      exact hdk (depthFor_le (not_lt.mp hc))
    have : α * 2 ^ k ≤ 81 / 8 := by
      have := mul_le_mul_of_nonneg_left hkX.le hα0.le
      rw [hαX] at this
      nlinarith
    linarith

/-- `cor:spike-pointwise`, lower bound: every `δ`-accurate algorithm with cap `q` in the
pointwise model has `1 + log₂(1+αM) ≤ 3q`. -/
theorem spike_pointwise_lower {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδα : δ ≤ α / 4)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {q : ℕ} {A : Alg (Str n)}
    (hA : Solves (PwLegal (9 / 4)) (spikeClass n k α) δ q A) :
    1 + Real.logb 2 (1 + α * 2 ^ k) ≤ 3 * q := by
  have hex : ∀ θ : Str k, PwLegal (9 / 4) (atomTarget (unif n) α (spikeAtom n θ))
      (exactGuide (atomTarget (unif n) α (spikeAtom n θ))) := fun θ =>
    pwLegal_exactGuide (by norm_num) (isDist_atomTarget (isDist_unif n) hα0.le (by linarith) _)
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast spike_zero_query hk1 hk hα0.le (by linarith) hex hA
  have hinfo := spike_information hk hα0.le (by linarith) hex hA
  have hA0 : 0 < α * 2 ^ k := by positivity
  have h1 : 1 + α * 2 ^ k ≤ 2 ^ (q + 1) := by
    rw [pow_succ]
    nlinarith
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) h1
  rw [logb_two_pow] at this
  push_cast at this
  linarith

/-- `cor:spike-pointwise`: for `R = 9/4`, uniformly over `n ≥ k ≥ 1`, `0 < α ≤ 1/4`,
`0 ≤ δ ≤ α/4`, `Q_pw(𝓕_{n,k,α},δ) = Θ(1 + log₂(1+αM))` with `M = 2^k`, with the absolute
constants `1/3` and `22`; the upper bound holds for exact sampling. -/
theorem spike_pointwise : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n k : ℕ) (α δ : ℝ), 1 ≤ k → k ≤ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ → δ ≤ α / 4 →
      c₁ * (1 + Real.logb 2 (1 + α * 2 ^ k)) ≤ (Qpw (spikeClass n k α) δ : ℝ) ∧
      (Qpw (spikeClass n k α) δ : ℝ) ≤ c₂ * (1 + Real.logb 2 (1 + α * 2 ^ k)) := by
  refine ⟨1 / 3, 22, by norm_num, by norm_num, fun n k α δ hk1 hk hα0 hα hδ0 hδα => ⟨?_,
    spike_pointwise_upper hα0 hα hδ0 hk⟩⟩
  have hex : ∃ q A, Solves (PwLegal (9 / 4)) (spikeClass n k α) δ q A :=
    ⟨_, _, solves_spikeSampler_pw (by norm_num) hα0 (by linarith) hδ0 (by linarith) hk⟩
  have hlow : ∀ q A, Solves (PwLegal (9 / 4)) (spikeClass n k α) δ q A →
      ⌈1 / 3 * (1 + Real.logb 2 (1 + α * 2 ^ k))⌉₊ ≤ q := by
    intro q A hA
    rw [Nat.ceil_le]
    have := spike_pointwise_lower hα0 hα hδα hk1 hk hA
    linarith
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_Qcx hex hlow)

end LearningGuided.Sec3
