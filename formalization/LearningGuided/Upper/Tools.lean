import LearningGuided.Cuts

/-!
# Tools for upper bounds: composition, query counts, caps and output distances

* `bindA A k` runs `A` and continues with `k` applied to its output.
* `runQ h A` is the joint law of the output and the number of guide queries made against `h`.
* `capAlg fb q A` aborts before the `(q+1)`-st query and returns the fixed fallback `fb`. It
  respects the cap `q` against every guide, and its output law is that of `A` with the output
  replaced by `fb` whenever `A` would make more than `q` queries.
* `expect p f` is the expectation of a `[0,∞]`-valued function under a `PMF`.
* `absDiff a b = (a - b) + (b - a)` is the distance of two extended reals; for finite values it is
  `|a - b|`.
* `tv_bind_le` bounds the distance of a mixture to a target that is itself a mixture of
  (possibly unnormalized) measures; `tv_map_le` is the coupling bound for two output maps of one
  law, and `prob_lt_le_expect` is Markov's inequality.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Upper

variable {α β γ : Type}

/-! ### Sequential composition and query counts -/

/-- Sequential composition of algorithms: run `A`, then continue with `k` at its output. -/
def bindA : Alg α → (α → Alg β) → Alg β
  | .ret a, k => k a
  | .query u f, k => .query u fun v => bindA (f v) k
  | .sample p f, k => .sample p fun g => bindA (f g) k

/-- The joint law of the output and the number of queries made against `h`. -/
noncomputable def runQ (h : Guide) : Alg β → PMF (β × ℕ)
  | .ret b => PMF.pure (b, 0)
  | .query u k => (runQ h (k (h u))).map fun bc => (bc.1, bc.2 + 1)
  | .sample p k => p.bind fun g => runQ h (k g)

@[simp] theorem runQ_ret (h : Guide) (b : β) : runQ h (.ret b) = PMF.pure (b, 0) := rfl

@[simp] theorem runQ_query (h : Guide) (u : List Bool) (k : ℝ → Alg β) :
    runQ h (.query u k) = (runQ h (k (h u))).map fun bc => (bc.1, bc.2 + 1) := rfl

@[simp] theorem runQ_sample (h : Guide) {γ : Type} (p : PMF γ) (k : γ → Alg β) :
    runQ h (.sample p k) = p.bind fun g => runQ h (k g) := rfl

/-- The output law is the first marginal of `runQ`. -/
theorem run_eq_map_runQ (h : Guide) (A : Alg β) : A.run h = (runQ h A).map Prod.fst := by
  induction A with
  | ret b => simp [PMF.pure_map]
  | query u k ih => simp [ih (h u), PMF.map_comp, Function.comp_def]
  | sample p k ih => simp [ih, PMF.map_bind]

theorem run_bindA (h : Guide) (A : Alg α) (k : α → Alg β) :
    (bindA A k).run h = (A.run h).bind fun a => (k a).run h := by
  induction A with
  | ret a => simp [bindA]
  | query u f ih => simp [bindA, ih]
  | sample p f ih => simp [bindA, ih, PMF.bind_bind]

theorem runQ_bindA (h : Guide) (A : Alg α) (k : α → Alg β) :
    runQ h (bindA A k) =
      (runQ h A).bind fun ac => (runQ h (k ac.1)).map fun bc => (bc.1, ac.2 + bc.2) := by
  induction A with
  | ret a =>
      simp only [bindA, runQ_ret, PMF.pure_bind, zero_add]
      exact (PMF.map_id _).symm
  | query u f ih =>
      simp only [bindA, runQ_query, ih, PMF.map_bind, PMF.bind_map]
      congr 1; ext1 ac
      simp only [Function.comp_apply, PMF.map_comp]
      congr 1; ext1 bc
      simp only [Function.comp_apply]
      congr 1
      ring
  | sample p f ih => simp [bindA, ih, PMF.bind_bind]

/-- Caps add under sequential composition. -/
theorem within_bindA {h : Guide} {A : Alg α} {k : α → Alg β} {q₁ q₂ : ℕ}
    (hA : A.Within h q₁) (hk : ∀ a, (k a).Within h q₂) : (bindA A k).Within h (q₁ + q₂) := by
  induction hA with
  | ret a q => exact (hk a).mono (by omega)
  | query u f q _ ih =>
      have := Alg.Within.query u (fun v => bindA (f v) k) (q + q₂) ih
      simpa [bindA, Nat.add_right_comm] using this
  | sample p f q _ ih => exact Alg.Within.sample p _ _ fun g hg => ih g hg

/-- A cap is the same as a bound on the query count over the support of `runQ`. -/
theorem within_of_runQ {h : Guide} (A : Alg β) :
    ∀ q, (∀ bc ∈ (runQ h A).support, bc.2 ≤ q) → A.Within h q := by
  induction A with
  | ret b => intro q _; exact Alg.Within.ret b q
  | query u k ih =>
      intro q hq
      obtain ⟨bc, hbc⟩ := (runQ h (k (h u))).support_nonempty
      have h1 : bc.2 + 1 ≤ q := hq (bc.1, bc.2 + 1) (by
        rw [runQ_query, PMF.mem_support_map_iff]; exact ⟨bc, hbc, rfl⟩)
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      refine Alg.Within.query u k r (ih (h u) r fun bc' hbc' => ?_)
      have := hq (bc'.1, bc'.2 + 1) (by
        rw [runQ_query, PMF.mem_support_map_iff]; exact ⟨bc', hbc', rfl⟩)
      simp only at this
      omega
  | sample p k ih =>
      intro q hq
      refine Alg.Within.sample p k q fun g hg => ih g q fun bc hbc => hq bc ?_
      rw [runQ_sample, PMF.mem_support_bind_iff]
      exact ⟨g, hg, hbc⟩

/-! ### Aborting before the `(q+1)`-st query -/

/-- Abort before the `(q+1)`-st query and return the fallback `fb`. -/
def capAlg (fb : β) : ℕ → Alg β → Alg β
  | _, .ret b => .ret b
  | 0, .query _ _ => .ret fb
  | q + 1, .query u k => .query u fun v => capAlg fb q (k v)
  | q, .sample p k => .sample p fun g => capAlg fb q (k g)

/-- The capped algorithm makes at most `q` queries against every guide. -/
theorem within_capAlg (h : Guide) (fb : β) (A : Alg β) : ∀ q, (capAlg fb q A).Within h q := by
  induction A with
  | ret b => intro q; cases q <;> exact Alg.Within.ret b _
  | query u k ih =>
      intro q
      cases q with
      | zero => exact Alg.Within.ret fb 0
      | succ q => exact Alg.Within.query u _ q (ih (h u) q)
  | sample p k ih =>
      intro q
      cases q <;> exact Alg.Within.sample p _ _ fun g _ => ih g _

/-- The output law of the capped algorithm: the fallback replaces the output exactly when the
uncapped algorithm would make more than `q` queries. -/
theorem run_capAlg (h : Guide) (fb : β) (A : Alg β) : ∀ q,
    (capAlg fb q A).run h = (runQ h A).map fun bc => if bc.2 ≤ q then bc.1 else fb := by
  induction A with
  | ret b => intro q; cases q <;> simp [capAlg, PMF.pure_map]
  | query u k ih =>
      intro q
      cases q with
      | zero =>
          simp only [capAlg, Alg.run_ret, runQ_query, PMF.map_comp]
          have : ((fun bc : β × ℕ => if bc.2 ≤ 0 then bc.1 else fb) ∘
              fun bc : β × ℕ => (bc.1, bc.2 + 1)) = Function.const _ fb := by
            ext bc; simp
          rw [this, PMF.map_const]
      | succ q =>
          simp only [capAlg, Alg.run_query, ih (h u) q, runQ_query, PMF.map_comp]
          congr 1; ext bc; simp
  | sample p k ih =>
      intro q
      cases q <;> simp [capAlg, ih, PMF.map_bind]

/-! ### Expectations of `[0,∞]`-valued functions -/

/-- The expectation of a `[0,∞]`-valued function under a law. -/
noncomputable def expect (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

theorem expect_pure (a : α) (f : α → ℝ≥0∞) : expect (PMF.pure a) f = f a := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

theorem expect_bind (p : PMF α) (k : α → PMF β) (f : β → ℝ≥0∞) :
    expect (p.bind k) f = expect p fun a => expect (k a) f := by
  unfold expect
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; ext a; congr 1; ext b
  ring

theorem expect_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expect (p.map g) f = expect p (f ∘ g) := by
  rw [← PMF.bind_pure_comp, expect_bind]
  simp only [Function.comp_apply, expect_pure]
  rfl

theorem expect_add (p : PMF α) (f g : α → ℝ≥0∞) :
    expect p (fun a => f a + g a) = expect p f + expect p g := by
  unfold expect
  simp_rw [mul_add]
  exact ENNReal.tsum_add

theorem expect_const_mul (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun a => c * f a) = c * expect p f := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext a; ring

theorem expect_mul_const (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun a => f a * c) = expect p f * c := by
  unfold expect
  rw [← ENNReal.tsum_mul_right]
  congr 1; ext a; ring

theorem expect_const (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  unfold expect
  rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem expect_mono (p : PMF α) {f g : α → ℝ≥0∞} (hfg : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hfg a) _

theorem expect_mono_support (p : PMF α) {f g : α → ℝ≥0∞}
    (hfg : ∀ a ∈ p.support, f a ≤ g a) : expect p f ≤ expect p g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (hfg a ha) _
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

theorem expect_congr_support (p : PMF α) {f g : α → ℝ≥0∞}
    (hfg : ∀ a ∈ p.support, f a = g a) : expect p f = expect p g :=
  le_antisymm (expect_mono_support p fun a ha => (hfg a ha).le)
    (expect_mono_support p fun a ha => (hfg a ha).ge)

theorem expect_finset_sum {ι : Type} (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expect p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect p (f i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- A function with zero expectation vanishes on the support. -/
theorem eq_zero_of_expect_eq_zero (p : PMF α) {f : α → ℝ≥0∞} (hf : expect p f = 0) :
    ∀ a ∈ p.support, f a = 0 := by
  intro a ha
  have := (ENNReal.tsum_eq_zero.mp hf) a
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h ha
  · exact h

/-- The probability of an event is the expectation of its indicator. -/
theorem probE_eq_expect (p : PMF α) (E : Set α) [DecidablePred (· ∈ E)] :
    probE p E = expect p fun a => if a ∈ E then 1 else 0 := by
  unfold probE expect
  rw [PMF.toOuterMeasure_apply]
  congr 1; ext a
  by_cases ha : a ∈ E <;> simp [Set.indicator, ha]

/-- Markov's inequality: `(q+1) P(c > q) ≤ E c`. -/
theorem prob_lt_le_expect (p : PMF α) (c : α → ℕ) (q : ℕ) :
    ((q : ℝ≥0∞) + 1) * probE p {a | q < c a} ≤ expect p fun a => (c a : ℝ≥0∞) := by
  classical
  rw [probE_eq_expect, ← expect_const_mul]
  refine expect_mono p fun a => ?_
  by_cases ha : q < c a
  · simp only [Set.mem_ofPred_eq, ha, ↓reduceIte, mul_one]
    exact_mod_cast ha
  · simp [ha]

/-- `E[X]^2 ≤ E[X^2]` for a `[0,∞]`-valued random variable with finite mean. -/
theorem expect_sq_le (p : PMF α) (f : α → ℝ≥0∞) :
    expect p f ^ 2 ≤ expect p fun a => f a ^ 2 := by
  by_cases htop : expect p f = ∞
  · -- then `E[f^2] = ∞` as well
    have h2 : expect p f ≤ expect p (fun a => f a ^ 2) + 1 := by
      rw [← expect_const p 1, ← expect_add]
      refine expect_mono p fun a => ?_
      rcases le_total (f a) 1 with h | h
      · exact h.trans le_add_self
      · calc f a = f a * 1 := (mul_one _).symm
          _ ≤ f a * f a := mul_le_mul_right h _
          _ = f a ^ 2 := (sq _).symm
          _ ≤ f a ^ 2 + 1 := le_self_add
    rw [htop, top_le_iff, ENNReal.add_eq_top] at h2
    simp only [ENNReal.one_ne_top, or_false] at h2
    rw [h2]; exact le_top
  · set m := expect p f
    have key : ∀ a, 2 * m * f a ≤ f a ^ 2 + m ^ 2 := by
      intro a
      by_cases hfa : f a = ∞
      · rw [hfa]; simp
      · have h1 : (2 * m * f a).toReal ≤ (f a ^ 2 + m ^ 2).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (by simp [hfa])
            (by simp [htop])]
          simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          nlinarith [sq_nonneg ((f a).toReal - m.toReal)]
        rwa [ENNReal.toReal_le_toReal
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) htop) hfa)
          (by simp [htop, hfa])] at h1
    have h2 : 2 * m * m ≤ expect p (fun a => f a ^ 2) + m ^ 2 := by
      calc 2 * m * m = expect p (fun a => 2 * m * f a) := (expect_const_mul p _ f).symm
        _ ≤ expect p (fun a => f a ^ 2 + m ^ 2) := expect_mono p key
        _ = expect p (fun a => f a ^ 2) + m ^ 2 := by rw [expect_add, expect_const]
    have h3 : m ^ 2 + m ^ 2 ≤ expect p (fun a => f a ^ 2) + m ^ 2 := by
      calc m ^ 2 + m ^ 2 = 2 * m * m := by ring
        _ ≤ _ := h2
    exact (ENNReal.add_le_add_iff_right (by simp [htop])).mp h3

/-! ### Distances of output laws -/

/-- The distance of two extended reals, `(a - b) + (b - a)`. -/
noncomputable def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) + (b - a)

theorem absDiff_comm (a b : ℝ≥0∞) : absDiff a b = absDiff b a := add_comm _ _

theorem absDiff_eq_ofReal {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    absDiff a b = ENNReal.ofReal |a.toReal - b.toReal| := by
  unfold absDiff
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr ((ENNReal.toReal_le_toReal ha hb).mpr h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal ha]
  · rw [tsub_eq_zero_of_le h, add_zero,
      abs_of_nonneg (sub_nonneg.mpr ((ENNReal.toReal_le_toReal hb ha).mpr h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
      ENNReal.ofReal_toReal ha]

/-- The distance of two mixtures is at most the mixture of the distances. -/
theorem absDiff_tsum_le (p : PMF α) (f g : α → ℝ≥0∞) :
    absDiff (∑' a, p a * f a) (∑' a, p a * g a) ≤ ∑' a, p a * absDiff (f a) (g a) := by
  unfold absDiff
  have h1 : (∑' a, p a * f a) - ∑' a, p a * g a ≤ ∑' a, p a * (f a - g a) := by
    rw [tsub_le_iff_left, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    exact mul_le_mul_right le_add_tsub _
  have h2 : (∑' a, p a * g a) - ∑' a, p a * f a ≤ ∑' a, p a * (g a - f a) := by
    rw [tsub_le_iff_left, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    exact mul_le_mul_right le_add_tsub _
  calc _ ≤ ∑' a, p a * (f a - g a) + ∑' a, p a * (g a - f a) := add_le_add h1 h2
    _ = ∑' a, p a * ((f a - g a) + (g a - f a)) := by
        rw [← ENNReal.tsum_add]; congr 1; ext a; ring

variable {n : ℕ}

/-- Twice the distance of a law to a nonnegative function, as a sum of `absDiff`s. -/
theorem ofReal_two_mul_tv (p : PMF (Str n)) {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) :
    ENNReal.ofReal (2 * tv (lawR p) μ) = ∑ x, absDiff (p x) (ENNReal.ofReal (μ x)) := by
  unfold tv lawR
  rw [mul_div_cancel₀ _ two_ne_zero,
    ENNReal.ofReal_sum_of_nonneg fun x _ => abs_nonneg _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [absDiff_eq_ofReal (p.apply_ne_top x) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (hμ x)]

/-- The output distance of a mixture `p.bind f` to a target that is the mixture of the
(possibly unnormalized) measures `ν a`: at most half the expected `ℓ¹` distance between `f a` and
`ν a`. -/
theorem tv_bind_le (p : PMF α) (f : α → PMF (Str n)) (ν : α → Str n → ℝ≥0∞)
    {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, ENNReal.ofReal (μ x) = ∑' a, p a * ν a x) :
    ENNReal.ofReal (2 * tv (lawR (p.bind f)) μ) ≤
      ∑' a, p a * ∑ x, absDiff (f a x) (ν a x) := by
  rw [ofReal_two_mul_tv _ hμ]
  calc ∑ x, absDiff ((p.bind f) x) (ENNReal.ofReal (μ x))
      ≤ ∑ x, ∑' a, p a * absDiff (f a x) (ν a x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [PMF.bind_apply, hν x]
        exact absDiff_tsum_le p _ _
    _ = ∑' a, p a * ∑ x, absDiff (f a x) (ν a x) := by
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        congr 1; ext a
        rw [Finset.mul_sum]

/-- Convexity of the output distance in the law. -/
theorem tv_bind_le_of_le (p : PMF α) (f : α → PMF (Str n)) {μ : Str n → ℝ} (hμ : IsDist μ)
    (g : α → ℝ) (hg : ∀ a ∈ p.support, tv (lawR (f a)) μ ≤ g a) :
    ENNReal.ofReal (tv (lawR (p.bind f)) μ) ≤ ∑' a, p a * ENNReal.ofReal (g a) := by
  have h := tv_bind_le p f (fun _ x => ENNReal.ofReal (μ x)) hμ.1 (fun x => by
    rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul])
  have h2 : ∀ a, ∑ x, absDiff (f a x) (ENNReal.ofReal (μ x)) =
      ENNReal.ofReal (2 * tv (lawR (f a)) μ) := fun a => (ofReal_two_mul_tv _ hμ.1).symm
  simp_rw [h2] at h
  have h3 : ENNReal.ofReal (2 * tv (lawR (p.bind f)) μ) =
      2 * ENNReal.ofReal (tv (lawR (p.bind f)) μ) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h3] at h
  have h4 : ∑' a, p a * ENNReal.ofReal (2 * tv (lawR (f a)) μ) ≤
      2 * ∑' a, p a * ENNReal.ofReal (g a) := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ p.support
    · rw [ENNReal.ofReal_mul (by norm_num)]
      calc p a * (ENNReal.ofReal 2 * ENNReal.ofReal (tv (lawR (f a)) μ))
          ≤ p a * (ENNReal.ofReal 2 * ENNReal.ofReal (g a)) := by
            gcongr; exact hg a ha
        _ = 2 * (p a * ENNReal.ofReal (g a)) := by simp; ring
    · rw [PMF.mem_support_iff, not_not] at ha
      simp [ha]
  have := h.trans h4
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp this

/-- Coupling: two output maps of one law differ in distance by at most the probability that they
disagree. -/
theorem tv_map_le (p : PMF α) (f g : α → Str n) :
    ENNReal.ofReal (tv (lawR (p.map f)) (lawR (p.map g))) ≤ probE p {a | f a ≠ g a} := by
  classical
  have hg : ∀ x, ENNReal.ofReal (lawR (p.map g) x) = ∑' a, p a * (PMF.pure (g a)) x := by
    intro x
    rw [lawR, ENNReal.ofReal_toReal (PMF.apply_ne_top _ x), ← PMF.bind_pure_comp,
      PMF.bind_apply]
    rfl
  have h := tv_bind_le p (fun a => PMF.pure (f a)) (fun a x => PMF.pure (g a) x)
    (fun x => ENNReal.toReal_nonneg) hg
  rw [← Function.comp_def, PMF.bind_pure_comp] at h
  change ENNReal.ofReal (2 * tv (lawR (PMF.map f p)) (lawR (PMF.map g p))) ≤ _ at h
  have h2 : ∀ a, ∑ x, absDiff (PMF.pure (f a) x) (PMF.pure (g a) x) =
      2 * (if a ∈ {a | f a ≠ g a} then 1 else 0) := by
    intro a
    by_cases hfg : f a = g a
    · simp [hfg, absDiff]
    · rw [ite_eq_left (show a ∈ {a | f a ≠ g a} from hfg), mul_one]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (f a)),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hfg, Finset.mem_univ (g a)⟩)]
      have h0 : ∑ x ∈ ((Finset.univ.erase (f a)).erase (g a)),
          absDiff (PMF.pure (f a) x) (PMF.pure (g a) x) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx1 := Finset.ne_of_mem_erase hx
        have hx2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
        simp [absDiff, PMF.pure_apply, hx1, hx2]
      rw [h0]
      simp [absDiff, PMF.pure_apply, hfg, Ne.symm hfg]
      norm_num
  simp_rw [h2] at h
  have h3 : ENNReal.ofReal (2 * tv (lawR (p.map f)) (lawR (p.map g))) =
      2 * ENNReal.ofReal (tv (lawR (p.map f)) (lawR (p.map g))) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h3] at h
  have h4 : ∑' a, p a * (2 * if a ∈ {a | f a ≠ g a} then (1 : ℝ≥0∞) else 0) =
      2 * probE p {a | f a ≠ g a} := by
    rw [probE_eq_expect, ← expect_const_mul]
    rfl
  rw [h4] at h
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h

/-- The output law of the capped algorithm is within the abort probability of the uncapped
output law. -/
theorem tv_capAlg_le (h : Guide) (fb : Str n) (A : Alg (Str n)) (q : ℕ) :
    ENNReal.ofReal (tv (lawR ((capAlg fb q A).run h)) (lawR (A.run h))) ≤
      probE (runQ h A) {bc | q < bc.2} := by
  rw [run_capAlg, run_eq_map_runQ]
  refine (tv_map_le _ _ _).trans ?_
  unfold probE
  refine (runQ h A).toOuterMeasure.mono fun bc hbc => ?_
  simp only [Set.mem_ofPred_eq] at hbc ⊢
  by_contra hle
  exact hbc (by simp [not_lt.mp hle])

end Upper
end LearningGuided
