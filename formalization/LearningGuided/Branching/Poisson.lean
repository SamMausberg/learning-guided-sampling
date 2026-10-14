import LearningGuided.Upper.Tools

/-!
# The Poisson law: mean and second moment

`poisPMF r` is Mathlib's Poisson distribution `poissonMeasure r` as a `PMF`. We prove its mean
`E K = r` and second moment `E K² = r + r²`, as expectations of `[0,∞]`-valued functions.
-/

open scoped BigOperators ENNReal NNReal Nat

namespace LearningGuided
namespace Branching

open Upper

/-- The Poisson law with rate `r`, as a `PMF` on `ℕ`. -/
noncomputable def poisPMF (r : ℝ≥0) : PMF ℕ := (ProbabilityTheory.poissonMeasure r).toPMF

theorem poisPMF_apply (r : ℝ≥0) (k : ℕ) :
    poisPMF r k = ENNReal.ofReal (Real.exp (-r) * r ^ k / k !) := by
  rw [poisPMF, MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.poissonMeasure_singleton]

theorem poisPMF_zero_rate : poisPMF 0 = PMF.pure 0 := by
  ext k
  rw [poisPMF_apply, PMF.pure_apply]
  rcases k with _ | k
  · simp
  · simp

/-- The real Poisson weights. -/
noncomputable def pw (r : ℝ≥0) (k : ℕ) : ℝ := Real.exp (-r) * r ^ k / k !

theorem pw_nonneg (r : ℝ≥0) (k : ℕ) : 0 ≤ pw r k := by unfold pw; positivity

theorem hasSum_pw (r : ℝ≥0) : HasSum (pw r) 1 := ProbabilityTheory.hasSum_one_poissonMeasure r

theorem pw_succ (r : ℝ≥0) (k : ℕ) : ((k + 1 : ℕ) : ℝ) * pw r (k + 1) = r * pw r k := by
  unfold pw
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp

/-- The first moment: `∑ k pw_r(k) = r`. -/
theorem hasSum_mul_pw (r : ℝ≥0) : HasSum (fun k : ℕ => (k : ℝ) * pw r k) r := by
  have h := (hasSum_pw r).mul_left (r : ℝ)
  rw [mul_one] at h
  have h' : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * pw r (k + 1)) r := by
    simpa only [pw_succ] using h
  have := (hasSum_nat_add_iff (f := fun k : ℕ => (k : ℝ) * pw r k) 1).mp h'
  simpa using this

/-- The second factorial moment: `∑ k(k-1) pw_r(k) = r²`. -/
theorem hasSum_mul_mul_pw (r : ℝ≥0) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * pw r k) ((r : ℝ) ^ 2) := by
  have h := (hasSum_mul_pw r).mul_left (r : ℝ)
  have h' : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) * pw r (k + 1))
      ((r : ℝ) * r) := by
    refine h.congr_fun fun k => ?_
    rw [mul_assoc, mul_comm (((k + 1 : ℕ) : ℝ) - 1), ← mul_assoc, pw_succ]
    push_cast
    ring
  have := (hasSum_nat_add_iff (f := fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * pw r k) 1).mp h'
  simpa [sq] using this

/-- The second moment: `∑ k² pw_r(k) = r + r²`. -/
theorem hasSum_sq_pw (r : ℝ≥0) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * pw r k) ((r : ℝ) + (r : ℝ) ^ 2) := by
  have := (hasSum_mul_pw r).add (hasSum_mul_mul_pw r)
  refine this.congr_fun fun k => ?_
  ring

theorem poisPMF_eq_ofReal_pw (r : ℝ≥0) (k : ℕ) : poisPMF r k = ENNReal.ofReal (pw r k) :=
  poisPMF_apply r k

theorem expect_poisPMF_of_hasSum (r : ℝ≥0) {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {a : ℝ}
    (ha : HasSum (fun k => f k * pw r k) a) :
    expect (poisPMF r) (fun k => ENNReal.ofReal (f k)) = ENNReal.ofReal a := by
  unfold expect
  rw [← ha.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hf k) (pw_nonneg r k))
    ha.summable]
  congr 1; ext k
  rw [poisPMF_eq_ofReal_pw, ← ENNReal.ofReal_mul (pw_nonneg r k), mul_comm]

/-- Mean of the Poisson law: `E K = r`. -/
theorem expect_poisPMF_id (r : ℝ≥0) : expect (poisPMF r) (fun k => (k : ℝ≥0∞)) = r := by
  have := expect_poisPMF_of_hasSum r (f := fun k => (k : ℝ)) (fun k => Nat.cast_nonneg k)
    (hasSum_mul_pw r)
  simpa [ENNReal.ofReal_natCast] using this

/-- Second moment of the Poisson law: `E K² = r + r²`. -/
theorem expect_poisPMF_sq (r : ℝ≥0) :
    expect (poisPMF r) (fun k => (k : ℝ≥0∞) ^ 2) = r + (r : ℝ≥0∞) ^ 2 := by
  have := expect_poisPMF_of_hasSum r (f := fun k => (k : ℝ) ^ 2) (fun k => by positivity)
    (hasSum_sq_pw r)
  rw [ENNReal.ofReal_add (by positivity) (by positivity)] at this
  simpa [ENNReal.ofReal_pow, ENNReal.ofReal_natCast] using this

end Branching
end LearningGuided
