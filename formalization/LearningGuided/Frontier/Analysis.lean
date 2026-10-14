import LearningGuided.Frontier.Learner

/-!
# Analysis of the safe frontier learner: runs of the components

Against a fixed guide `h` and version space `G` with mixture `η`:

* `run_scanA`: a scan is a free draw `X ∼ η` followed by the deterministic scan of its path.
* `run_stageA_none`: all `k` scans of a stage pass with probability `(1 - p)^k`, where `1 - p` is
  the `η`-probability that a scan passes; `stageA_support`: a reported violation `(v, a)` has
  `a = h(v) > 2Rη(v)` and `|v| ≤ n`.
* `run_trialA_some`: the probability that a production trial outputs `y`.
* `lawR_produceA_succ`: the production law satisfies `L_{j+1} = (1 - α) L_j + w`, where `w(y)` is
  the probability that a trial outputs `y` and `α = ∑ w`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Frontier

open Upper

variable {n : ℕ}

theorem run_scanA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    (scanA R G).run h = (toPMF (mix G)).map fun x => (x, scanFn h R (mix G) x) := by
  simp only [scanA, Alg.run_sample, run_bindA, run_scanPath, PMF.pure_bind, Alg.run_ret]
  rfl

open Classical in
/-- The pass probability `1 - p` of one scan. -/
noncomputable def passE (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) : ℝ≥0∞ :=
  ∑' x, toPMF (mix G) x * (if Stops h R (mix G) x then 0 else 1)

theorem scanFn_inl_stops {h : Guide} {R : ℝ} {η : Str n → ℝ} {x : Str n} {va : List Bool × ℝ}
    (hs : scanFn h R η x = .inl va) : Stops h R η x :=
  (scanFn_isLeft_iff h R η x).mp (by simp [hs])

theorem scanFn_inr_not_stops {h : Guide} {R : ℝ} {η : Str n → ℝ} {x : Str n} {a : ℝ}
    (hs : scanFn h R η x = .inr a) : ¬ Stops h R η x := fun hst => by
  have := (scanFn_isLeft_iff h R η x).mpr hst
  simp [hs] at this

open Classical in
/-- All `k` scans of a stage pass with probability `(1 - p)^k`. -/
theorem run_stageA_none (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    ∀ k, (stageA R G k).run h none = passE h R G ^ k
  | 0 => by simp [stageA, PMF.pure_apply]
  | k + 1 => by
      simp only [stageA, run_bindA, run_scanA, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_apply, pow_succ]
      have e : passE h R G ^ k * passE h R G = ∑' x, passE h R G ^ k *
          (toPMF (mix G) x * (if Stops h R (mix G) x then 0 else 1)) := by
        rw [ENNReal.tsum_mul_left]; rfl
      rw [e]
      congr 1; ext x
      rcases hs : scanFn h R (mix G) x with va | a
      · simp [scanFn_inl_stops hs, PMF.pure_apply]
      · simp [scanFn_inr_not_stops hs, run_stageA_none h R G k, mul_comm]

/-- A violation reported by a stage satisfies `a = h(v) > 2Rη(v)` and `|v| ≤ n`. -/
theorem stageA_support (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    ∀ k (va : List Bool × ℝ), some va ∈ ((stageA R G k).run h).support →
      va.2 = h va.1 ∧ 2 * R * mass (mix G) va.1 < va.2 ∧ va.1.length ≤ n
  | 0, va, hva => by simp [stageA] at hva
  | k + 1, va, hva => by
      simp only [stageA, run_bindA, run_scanA, PMF.bind_map, Function.comp_def,
        PMF.mem_support_bind_iff] at hva
      obtain ⟨x, -, hx⟩ := hva
      rcases hs : scanFn h R (mix G) x with va' | a
      · have key := scanPathFn_inl h R (mix G) (List.ofFn x) [] 1 va'.1 va'.2 hs
        rw [hs] at hx
        simp only [Sum.elim_inl, Alg.run_ret, PMF.support_pure, Set.mem_singleton_iff,
          Option.some.injEq] at hx
        rw [hx]
        simpa using key
      · rw [hs] at hx
        exact stageA_support h R G k va hx

/-- The run of a production trial. -/
theorem run_trialA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    (trialA R G).run h = (toPMF (mix G)).bind fun x =>
      Sum.elim (fun _ => PMF.pure none)
        (fun a => (coin (a / (2 * R * mix G x))).bind fun acc =>
          PMF.pure (if acc then some x else none)) (scanFn h R (mix G) x) := by
  simp only [trialA, run_bindA, run_scanA, PMF.bind_map, Function.comp_def]
  congr 1; ext1 x
  rcases scanFn h R (mix G) x with va | a <;> rfl

/-- The probability that a trial outputs `y`. -/
theorem run_trialA_some (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) (y : Str n) :
    (trialA R G).run h (some y) = toPMF (mix G) y *
      Sum.elim (fun _ => 0) (fun a => ENNReal.ofReal (clip (a / (2 * R * mix G y))))
        (scanFn h R (mix G) y) := by
  classical
  rw [run_trialA, PMF.bind_apply, tsum_eq_single y]
  · congr 1
    rcases scanFn h R (mix G) y with va | a
    · simp [PMF.pure_apply]
    · simp only [Sum.elim_inr, PMF.bind_apply, tsum_fintype, Fintype.sum_bool, ↓reduceIte,
        PMF.pure_apply, Bool.false_eq_true, reduceCtorEq, mul_zero, add_zero, mul_one]
      rfl
  · intro x hxy
    rcases scanFn h R (mix G) x with va | a
    · simp [PMF.pure_apply]
    · simp [PMF.bind_apply, tsum_fintype, PMF.pure_apply, Ne.symm hxy]

end Frontier
end LearningGuided
