import LearningGuided.Frontier.Cut

/-!
# The safe frontier learner as a query algorithm (Appendix `app:frontier`)

* `scanA R G`: draw `X ∼ η` (the uniform mixture of the version space `G`) for free and scan its
  path (at most `2n` queries).
* `stageA R G k`: run at most `k` independent scans; return the first violation `(v, h(v))`, or
  `none` if all pass (then the version space is frozen).
* `trialA R G`: a production trial; a stopped scan is rejected, and a passing scan with leaf `x`
  is accepted with probability `h(x)/(2Rη(x))`, using the leaf value queried by the scan.
* `produceA R G J`: at most `J` trials; the fixed fallback on exhaustion.
* `learnA R T J s G`: a singleton (or empty) version space is sampled directly; otherwise run a
  stage of `T` scans, and on a violation at `v` retain the candidates `φ` with `φ(v) ≥ h(v)/R`
  and continue with one stage fewer; if all scans pass, produce. The stage budget `s` caps the
  number of stages.
* `frontierAlg M δ R C F` uses the constants `J₀ = 1 + ⌈log₂ M⌉`, `p₀ = δ²/(32RC)`,
  `T = ⌈p₀⁻¹ log(4J₀/δ)⌉`, `J = ⌈4R log(4/δ)⌉` and the budget `J₀`; its cap is
  `2n(J₀T + J)` against every guide (`within_frontierAlg`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Frontier

open Upper

variable {n : ℕ}

/-- One scan: a free draw `X ∼ η` and the scan of its path. -/
noncomputable def scanA (R : ℝ) (G : Finset (Str n → ℝ)) : Alg (Str n × ScanRes) :=
  .sample (toPMF (mix G)) fun x =>
    bindA (scanPath R (mix G) [] (List.ofFn x) 1) fun r => .ret (x, r)

/-- A stage of at most `k` scans: the first violation, or `none` if all scans pass. -/
noncomputable def stageA (R : ℝ) (G : Finset (Str n → ℝ)) : ℕ → Alg (Option (List Bool × ℝ))
  | 0 => .ret none
  | k + 1 => bindA (scanA R G) fun xr =>
      Sum.elim (fun va => .ret (some va)) (fun _ => stageA R G k) xr.2

/-- The clipped probability `min 1 (max 0 p)`. -/
noncomputable def clip (p : ℝ) : ℝ := min 1 (max 0 p)

theorem clip_nonneg (p : ℝ) : 0 ≤ clip p := le_min zero_le_one (le_max_left _ _)

theorem clip_le_one (p : ℝ) : clip p ≤ 1 := min_le_left _ _

theorem clip_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : clip p = p := by
  simp [clip, h0, h1]

theorem sum_coin (p : ℝ) :
    ∑ b : Bool, (if b then ENNReal.ofReal (clip p) else ENNReal.ofReal (1 - clip p)) = 1 := by
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [← ENNReal.ofReal_add (clip_nonneg p) (by linarith [clip_le_one p])]
  simp

/-- A coin with success probability `min 1 (max 0 p)`. -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal (clip p) else ENNReal.ofReal (1 - clip p))
    (sum_coin p)

/-- One production trial: reject a stopped scan; accept a passing scan with leaf `x` and leaf
value `a = h(x)` with probability `a/(2Rη(x))`. -/
noncomputable def trialA (R : ℝ) (G : Finset (Str n → ℝ)) : Alg (Option (Str n)) :=
  bindA (scanA R G) fun xr =>
    Sum.elim (fun _ => .ret none)
      (fun a => .sample (coin (a / (2 * R * mix G xr.1))) fun acc =>
        .ret (if acc then some xr.1 else none)) xr.2

/-- Production with at most `j` trials and the fixed fallback on exhaustion. -/
noncomputable def produceA (R : ℝ) (G : Finset (Str n → ℝ)) : ℕ → Alg (Str n)
  | 0 => .ret (fbStr n)
  | j + 1 => bindA (trialA R G) fun o => Option.elim o (produceA R G j) .ret

/-- The version space after a violation `(v, a)`: the candidates with `φ(v) ≥ a/R`. -/
noncomputable def update (R : ℝ) (G : Finset (Str n → ℝ)) (va : List Bool × ℝ) :
    Finset (Str n → ℝ) :=
  G.filter fun φ => va.2 / R ≤ mass φ va.1

/-- The learner with stage budget `s`. -/
noncomputable def learnA (R : ℝ) (T J : ℕ) : ℕ → Finset (Str n → ℝ) → Alg (Str n)
  | 0, G => if G.card ≤ 1 then sampleSet G else .ret (fbStr n)
  | s + 1, G => if G.card ≤ 1 then sampleSet G else
      bindA (stageA R G T) fun o =>
        Option.elim o (produceA R G J) fun va => learnA R T J s (update R G va)

/-- `J₀ = 1 + ⌈log₂ M⌉`. -/
noncomputable def J0 (M : ℕ) : ℕ := 1 + ⌈Real.logb 2 M⌉₊

/-- `p₀ = δ²/(32RC)`. -/
noncomputable def p0 (δ R C : ℝ) : ℝ := δ ^ 2 / (32 * R * C)

/-- `T = ⌈p₀⁻¹ log(4J₀/δ)⌉`. -/
noncomputable def Tsc (M : ℕ) (δ R C : ℝ) : ℕ := ⌈(p0 δ R C)⁻¹ * Real.log (4 * J0 M / δ)⌉₊

/-- `J = ⌈4R log(4/δ)⌉`. -/
noncomputable def Jpr (δ R : ℝ) : ℕ := ⌈4 * R * Real.log (4 / δ)⌉₊

/-- The safe frontier learner for a finite class `F` of at most `M` distributions. -/
noncomputable def frontierAlg (M : ℕ) (δ R C : ℝ) (F : Finset (Str n → ℝ)) : Alg (Str n) :=
  learnA R (Tsc M δ R C) (Jpr δ R) (J0 M) F

/-- The cap `2n(J₀T + J)`. -/
noncomputable def frontierCap (n M : ℕ) (δ R C : ℝ) : ℕ :=
  2 * n * (J0 M * Tsc M δ R C + Jpr δ R)

/-! ### Caps -/

theorem within_scanA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    (scanA R G).Within h (2 * n) := by
  refine Alg.Within.sample _ _ _ fun x _ => ?_
  have := within_bindA (within_scanPath h R (mix G) (List.ofFn x) [] 1)
    (k := fun r => Alg.ret (x, r)) (q₂ := 0) fun r => Alg.Within.ret _ _
  simpa using this

theorem within_stageA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    ∀ k, (stageA R G k).Within h (2 * n * k)
  | 0 => Alg.Within.ret _ _
  | k + 1 => by
      have := within_bindA (within_scanA h R G) (q₂ := 2 * n * k)
        (k := fun xr => Sum.elim (fun va => Alg.ret (some va)) (fun _ => stageA R G k) xr.2)
        fun xr => by
          rcases xr with ⟨x, _ | _⟩
          · exact Alg.Within.ret _ _
          · exact within_stageA h R G k
      rw [show 2 * n * (k + 1) = 2 * n + 2 * n * k by ring]
      exact this

theorem within_trialA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    (trialA R G).Within h (2 * n) := by
  have := within_bindA (within_scanA h R G) (q₂ := 0)
    (k := fun xr => Sum.elim (fun _ => Alg.ret none)
      (fun a => Alg.sample (coin (a / (2 * R * mix G xr.1))) fun acc =>
        Alg.ret (if acc then some xr.1 else none)) xr.2) fun xr => by
      rcases xr with ⟨x, _ | _⟩
      · exact Alg.Within.ret _ _
      · exact Alg.Within.sample _ _ _ fun _ _ => Alg.Within.ret _ _
  exact this

theorem within_produceA (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) :
    ∀ j, (produceA R G j).Within h (2 * n * j)
  | 0 => Alg.Within.ret _ _
  | j + 1 => by
      have := within_bindA (within_trialA h R G) (q₂ := 2 * n * j)
        (k := fun o => Option.elim o (produceA R G j) Alg.ret) fun o => by
          rcases o with _ | x
          · exact within_produceA h R G j
          · exact Alg.Within.ret _ _
      rw [show 2 * n * (j + 1) = 2 * n + 2 * n * j by ring]
      exact this

theorem within_sampleSet' (h : Guide) (G : Finset (Str n → ℝ)) (q : ℕ) :
    (sampleSet G).Within h q := within_sampleSet h G q

/-- The learner with budget `s` makes at most `2n(sT + J)` queries against every guide. -/
theorem within_learnA (h : Guide) (R : ℝ) (T J : ℕ) :
    ∀ (s : ℕ) (G : Finset (Str n → ℝ)), (learnA R T J s G).Within h (2 * n * (s * T + J))
  | 0, G => by
      unfold learnA
      split_ifs
      · exact within_sampleSet h G _
      · exact Alg.Within.ret _ _
  | s + 1, G => by
      unfold learnA
      split_ifs
      · exact within_sampleSet h G _
      · have := within_bindA (within_stageA h R G T) (q₂ := 2 * n * (s * T + J))
          (k := fun o => Option.elim o (produceA R G J) fun va => learnA R T J s (update R G va))
          fun o => by
            rcases o with _ | va
            · exact (within_produceA h R G J).mono
                (Nat.mul_le_mul_left (2 * n) (Nat.le_add_left J (s * T)))
            · exact within_learnA h R T J s _
        rw [show 2 * n * ((s + 1) * T + J) = 2 * n * T + 2 * n * (s * T + J) by ring]
        exact this

/-- `app:frontier`: the cap `2n(J₀T + J)` holds against every guide. -/
theorem within_frontierAlg (h : Guide) (M : ℕ) (δ R C : ℝ) (F : Finset (Str n → ℝ)) :
    (frontierAlg M δ R C F).Within h (frontierCap n M δ R C) :=
  within_learnA h R _ _ _ F

end Frontier
end LearningGuided
