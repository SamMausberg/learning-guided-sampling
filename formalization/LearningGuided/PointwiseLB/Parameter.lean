import LearningGuided.PointwiseLB.Sim

/-!
# The parameterized lower bound (Theorem `pw-thm:parameter`)

Every algorithm that is `1/16`-accurate with cap `q` against every target of the class of
Appendix B together with its oracle `h_θ` satisfies `q > 2^{-16} (ℓ-1) r²`; the same holds on
`{0,1}^n` for every `n ≥ N` (padding with zeros). The argument: the first output bit predicts
the root `B` with probability at least `3/5 - 1/16 = 1/2 + 3/80` for every instance
(`pw-lem:size-root`), hence under the hard prior the output laws for the two roots differ by
at least `3/40` on the event `X₁ = 1`, while Lemma `pw-lem:information` gives at most
`8√η + 32η ≤ 8/256 + 32/65536 = 65/2048 < 3/40` when `q ≤ 2^{-16}(ℓ-1)W`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-- The first bit of a string of positive length. -/
def bit0 {n : ℕ} (hn : 0 < n) (x : Str n) : Bool := x ⟨0, hn⟩

theorem isPre_single_iff {n : ℕ} (hn : 0 < n) (x : Str n) (b : Bool) :
    IsPre [b] x ↔ bit0 hn x = b := by
  have hne : List.ofFn x ≠ [] := by rw [Ne, List.ofFn_eq_nil_iff]; omega
  have hcons : List.ofFn x = bit0 hn x :: (List.ofFn x).tail := by
    conv_lhs => rw [← List.cons_head_tail hne]
    rw [List.head_ofFn]; rfl
  unfold IsPre
  rw [hcons, List.cons_prefix_cons]
  simp [eq_comm]

theorem mass_single_eq_sum' {n : ℕ} (hn : 0 < n) (μ : Str n → ℝ) (b : Bool) :
    mass μ [b] = ∑ x ∈ Finset.univ.filter (fun x => bit0 hn x = b), μ x := by
  unfold mass
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by simp only [isPre_single_iff hn]

theorem probE_add_compl {β : Type} (p : PMF β) (E : Set β) :
    (probE p E).toReal + (probE p Eᶜ).toReal = 1 := by
  have h : probE p E + probE p Eᶜ = 1 := by
    unfold probE
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    simp_rw [Set.indicator_self_add_compl_apply]
    exact p.tsum_coe
  rw [← ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)), h, ENNReal.toReal_one]

/-- The probability of the root event from accuracy: a `δ`-accurate output law gives
`P(X₁ = b) ≥ μ([b]) - δ`. -/
theorem root_prob_ge {n : ℕ} (hn : 0 < n) {μ : Str n → ℝ} (hμ : IsDist μ) {p : PMF (Str n)}
    {δ : ℝ} (hδ : tv (lawR p) μ ≤ δ) (b : Bool) :
    mass μ [b] - δ ≤ (probE p {x | bit0 hn x = b}).toReal := by
  have := prob_ge_of_tv hμ hδ (Finset.univ.filter fun x => bit0 hn x = b)
  rw [← mass_single_eq_sum' hn] at this
  convert this using 3
  ext x; simp

namespace Prm

variable (P : Prm)

/-- `pw-thm:parameter`, distinguishing step: if an algorithm with cap `q` against every `h_θ` reads
off the root `B` from its output with probability at least `1/2 + ε` for every instance, then `2ε ≤
8√η + 32η` (Lemma `pw-lem:information` and the test of a uniform bit). -/
theorem advantage_bound {β : Type} [Finite β] (f : β → Bool) (A : Alg β) (q : ℕ) (ε : ℝ)
    (hA : ∀ B T, P.Valid B T → A.Within (P.oracle T) q ∧
      1 / 2 + ε ≤ (probE (A.run (P.oracle T)) {x | f x = B}).toReal) :
    2 * ε ≤ 8 * Real.sqrt (P.eta q) + 32 * P.eta q := by
  have hinfo := P.information A q (fun B T hv => (hA B T hv).1) {x | f x = true}
  have hge : ∀ b : Bool, 1 / 2 + ε ≤ P.avgA A b {x | f x = b} := by
    intro b
    unfold avgA
    have hpos : (0 : ℝ) < (P.Theta b).card := by
      obtain ⟨T, hT⟩ := P.exists_valid b
      exact_mod_cast Finset.card_pos.mpr ⟨T, by simp [Theta, hT]⟩
    rw [le_div_iff₀ hpos]
    calc (1 / 2 + ε) * (P.Theta b).card = ∑ _T ∈ P.Theta b, (1 / 2 + ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun T hT =>
          (hA b T (Finset.mem_filter.mp hT).2).2
  have hcompl : ∀ b : Bool, P.avgA A b {x | f x = true} + P.avgA A b {x | f x = false} = 1 := by
    intro b
    unfold avgA
    have hpos : (0 : ℝ) < (P.Theta b).card := by
      obtain ⟨T, hT⟩ := P.exists_valid b
      exact_mod_cast Finset.card_pos.mpr ⟨T, by simp [Theta, hT]⟩
    rw [← add_div, ← Finset.sum_add_distrib, div_eq_one_iff_eq hpos.ne']
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    have : {x | f x = false} = {x | f x = true}ᶜ := by ext x; simp
    rw [this, probE_add_compl]; simp
  have h1 := hge true
  have h0 := hge false
  have hc := hcompl false
  rw [abs_le] at hinfo
  linarith [hinfo.1]

/-- `pw-thm:parameter`, numerical step: if
`q ≤ 2^{-16}(ℓ-1)W` then `8√η + 32η ≤ 8/256 + 32/65536 = 65/2048`. -/
theorem eta_small {q : ℕ} (hq : (q : ℝ) ≤ ((P.ℓ : ℝ) - 1) * P.W / 2 ^ 16) :
    8 * Real.sqrt (P.eta q) + 32 * P.eta q ≤ 65 / 2048 := by
  have hℓ : (1 : ℝ) < P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 < P.ℓ)
  have hWp : (0 : ℝ) < P.W := by have := P.cast_W; have := P.cast_r_ge; nlinarith
  have hpos : (0 : ℝ) < ((P.ℓ : ℝ) - 1) * P.W := by nlinarith
  have he : P.eta q ≤ 1 / 2 ^ 16 := by
    unfold eta; rw [div_le_iff₀ hpos]; linarith
  have hs : Real.sqrt (P.eta q) ≤ 1 / 2 ^ 8 := by
    calc Real.sqrt (P.eta q) ≤ Real.sqrt ((1 / 2 ^ 8) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num at he ⊢; linarith)
      _ = 1 / 2 ^ 8 := Real.sqrt_sq (by norm_num)
  norm_num at hs he ⊢
  linarith

theorem q_gt_of_adv {q : ℕ} {ε : ℝ} (h : 2 * ε ≤ 8 * Real.sqrt (P.eta q) + 32 * P.eta q)
    (hε : 65 / 2048 < 2 * ε) : ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  by_contra hc
  have hq : (q : ℝ) ≤ ((P.ℓ : ℝ) - 1) * P.W / 2 ^ 16 := by
    rw [P.cast_W, ← sq]; exact le_of_not_gt hc
  have := P.eta_small hq
  linarith

/-- `pw-thm:parameter` on `N = 1 + r(2 log₂ r + ℓ)` bits: every algorithm with cap `q`
that is `1/16`-accurate against every target `μ_θ` of the class with its oracle `h_θ`
satisfies `q > 2^{-16} (ℓ-1) r²`. -/
theorem parameter_N (A : Alg (Str P.N)) (q : ℕ)
    (hA : ∀ B T, P.Valid B T → A.Within (P.oracle T) q ∧
      tv (lawR (A.run (P.oracle T))) (P.target T) ≤ 1 / 16) :
    ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  have hadv := P.advantage_bound (bit0 P.N_pos) A q (3 / 80) fun B T hv => by
    refine ⟨(hA B T hv).1, ?_⟩
    have h1 := root_prob_ge P.N_pos (P.isDist_target hv) (hA B T hv).2 B
    have h2 := P.root_mass_ge hv
    linarith
  exact P.q_gt_of_adv hadv (by norm_num)

/-- `pw-thm:parameter` on `N` bits, class form: the class `targetClass` has at most `M₀`
distributions, and every algorithm solving it at error `1/16` in the pointwise factor-`9/4`
model with cap `q` has `q > 2^{-16} (ℓ-1) r²`. -/
theorem pw_thm_parameter_N :
    P.targetClass.card ≤ P.M0 ∧ (∀ μ ∈ P.targetClass, IsDist μ) ∧
      ∀ (q : ℕ) (A : Alg (Str P.N)), Solves (PwLegal (9 / 4)) ↑P.targetClass (1 / 16) q A →
        ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  have hmem : ∀ B T, P.Valid B T → P.target T ∈ P.targetClass := fun B T hv =>
    Finset.mem_image.mpr ⟨(B, T), by simp [instances, hv], rfl⟩
  refine ⟨P.card_targetClass_le, fun μ hμ => ?_, fun q A hA => ?_⟩
  · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hμ
    exact P.isDist_target (Finset.mem_filter.mp hθ).2
  · exact P.parameter_N A q fun B T hv => hA _ (hmem B T hv) _ (P.oracle_pwLegal hv)

/-- The class of Theorem `pw-thm:parameter` on `n ≥ N` bits: the targets of Appendix B padded
with zeros. -/
noncomputable def padClass (n : ℕ) (hNn : P.N ≤ n) : Finset (Str n → ℝ) :=
  P.instances.image fun θ => padT hNn (P.target θ.2)

theorem card_padClass_le (n : ℕ) (hNn : P.N ≤ n) : (P.padClass n hNn).card ≤ P.M0 :=
  Finset.card_image_le.trans ((Finset.card_le_univ _).trans P.card_inst.le)

theorem mem_padClass {n : ℕ} {hNn : P.N ≤ n} {μ : Str n → ℝ} :
    μ ∈ P.padClass n hNn ↔ ∃ B T, P.Valid B T ∧ μ = padT hNn (P.target T) := by
  unfold padClass instances
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨B, T⟩, hv, rfl⟩; exact ⟨B, T, hv, rfl⟩
  · rintro ⟨B, T, hv, rfl⟩; exact ⟨⟨B, T⟩, hv, rfl⟩

theorem padClass_isDist {n : ℕ} {hNn : P.N ≤ n} {μ : Str n → ℝ} (hμ : μ ∈ P.padClass n hNn) :
    IsDist μ := by
  obtain ⟨B, T, hv, rfl⟩ := P.mem_padClass.mp hμ
  exact isDist_padT hNn (P.isDist_target hv)

/-- `pw-thm:parameter`, extension to `n ≥ N`: the padded oracle `h_θ` on `n ≥ N` bits is a pointwise
factor-`9/4` guide for the padded target. -/
theorem padOracle_pwLegal {n : ℕ} (hNn : P.N ≤ n) {B : Bool} {T : P.Tables} (hv : P.Valid B T) :
    PwLegal (9 / 4) (padT hNn (P.target T)) (padO P.N n (P.oracle T)) :=
  pad_pwLegal hNn (P.oracle_pwLegal hv)

/-- `pw-thm:parameter` on `n ≥ N` bits: every algorithm with cap `q` that is
`1/16`-accurate against every padded target with its padded oracle satisfies
`q > 2^{-16} (ℓ-1) r²`. Each padded query is simulated by at most one query to `h_θ`. -/
theorem parameter_pad {n : ℕ} (hNn : P.N ≤ n) (A : Alg (Str n)) (q : ℕ)
    (hA : ∀ B T, P.Valid B T → A.Within (padO P.N n (P.oracle T)) q ∧
      tv (lawR (A.run (padO P.N n (P.oracle T)))) (padT hNn (P.target T)) ≤ 1 / 16) :
    ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  have hn : 0 < n := lt_of_lt_of_le P.N_pos hNn
  have hS : ∀ T : P.Tables, ∀ u, padO P.N n (P.oracle T) u = (padSim P.N n u).eval (P.oracle T) :=
    fun T u => padO_eval _ u
  have hadv := P.advantage_bound (bit0 hn) (simAlg (padSim P.N n) A) q (3 / 80) fun B T hv => by
    refine ⟨within_simAlg (hS T) A q (hA B T hv).1, ?_⟩
    rw [run_simAlg (hS T)]
    have h1 := root_prob_ge hn (isDist_padT hNn (P.isDist_target hv)) (hA B T hv).2 B
    have h2 := P.root_mass_ge hv
    rw [mass_padT_short hNn _ (by simp [N])] at h1
    linarith
  exact P.q_gt_of_adv hadv (by norm_num)

/-- `pw-thm:parameter`: for `r = 2^p ≥ 8` and `ℓ ≥ 2`, and every `n ≥ N`, there is a
class of at most `M₀ = 2(2ℓ)^{2r²}` distributions on `{0,1}^n` (the padded targets
`padClass`), each with a fixed pointwise factor-`9/4` oracle, such that every algorithm solving
the class at error `1/16` with cap `q` in the pointwise model has `q > 2^{-16}(ℓ-1)r²`. -/
theorem pw_thm_parameter (n : ℕ) (hNn : P.N ≤ n) :
    (P.padClass n hNn).card ≤ P.M0 ∧ (∀ μ ∈ P.padClass n hNn, IsDist μ) ∧
      ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑(P.padClass n hNn) (1 / 16) q A →
        ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  refine ⟨P.card_padClass_le n hNn, fun μ hμ => P.padClass_isDist hμ, fun q A hA => ?_⟩
  refine P.parameter_pad hNn A q fun B T hv => ?_
  exact hA _ (P.mem_padClass.mpr ⟨B, T, hv, rfl⟩) _ (P.padOracle_pwLegal hNn hv)

end Prm

end LearningGuided.PointwiseLB
