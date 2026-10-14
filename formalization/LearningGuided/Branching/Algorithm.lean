import LearningGuided.Branching.Process
import LearningGuided.Upper.Identify

/-!
# The Poisson branching sampler as a query algorithm

The sampler of `thm:branching`. Particles carry their position and the guide value retained from
their creation; the `P` independent trees are generated together, depth by depth, starting from
`P` particles at the root, whose value `h(∅) = 1` is known without a query.

* `genA` processes one generation: a particle `(u, v)` at a nonleaf queries both children
  `h(u0)`, `h(u1)` (two queries per processed particle; repeated calls are counted separately),
  draws independent Poisson numbers of children with means `h(ub)/v`, and its children retain the
  queried values. A zero-valued child gets no particles because its Poisson mean is zero.
* `levelsA t` runs `t` generations; `outA` draws the output from the uniform empirical measure of
  the pooled terminal particles, or returns a fixed point mass if there are none.
* `branchU n P` is the untruncated sampler with `P` trees, and `branchAlg n A B δ` aborts before
  query `q + 1` with the fixed fallback, for `P = ⌈B/δ²⌉`, `q = ⌈4PA/δ⌉` (`eq:branch-cap`).

Processing the pooled population depth by depth instead of tree by tree changes neither the
queries made (two per processed particle), nor the joint law of the generated forest (every
particle reproduces independently), nor the abort event (the total query count exceeds `q`).

Against a fixed guide `h`, the joint law of the output and the query count is computed from the
process `levelsP` of `Process.lean` (`runQ_branchU`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Branching

open Upper

/-- A particle: its position and the guide value retained from its creation. -/
abbrev Particle := List Bool × ℝ

/-- One generation of the branching sampler. -/
noncomputable def genA : List Particle → Alg (List Particle)
  | [] => .ret []
  | (u, v) :: rest =>
      .query (u ++ [false]) fun a0 =>
      .query (u ++ [true]) fun a1 =>
      .sample (poisPMF (a0 / v).toNNReal) fun K0 =>
      .sample (poisPMF (a1 / v).toNNReal) fun K1 =>
      bindA (genA rest) fun rest' =>
        .ret (List.replicate K0 (u ++ [false], a0) ++ List.replicate K1 (u ++ [true], a1) ++ rest')

/-- `t` generations. -/
noncomputable def levelsA : ℕ → List Particle → Alg (List Particle)
  | 0, pop => .ret pop
  | t + 1, pop => bindA (levelsA t pop) genA

variable {n : ℕ}

/-- The number of terminal particles at the leaf `x`. -/
def leafCount (pop : List (List Bool)) (x : Str n) : ℕ := pop.count (List.ofFn x)

/-- The total number `T` of terminal particles. -/
def total (n : ℕ) (pop : List (List Bool)) : ℕ := ∑ x : Str n, leafCount pop x

theorem sum_leafCount_div {pop : List (List Bool)} (hT : total n pop ≠ 0) :
    ∑ x : Str n, (leafCount pop x : ℝ≥0∞) / total n pop = 1 := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have : ∑ x : Str n, (leafCount pop x : ℝ≥0∞) = total n pop := by simp [total]
  rw [this, ENNReal.mul_inv_cancel (by exact_mod_cast hT) (ENNReal.natCast_ne_top _)]

open Classical in
/-- The output law `ρ`: the uniform empirical measure of the terminal particles if `T > 0`, and a
fixed point mass if `T = 0`. -/
noncomputable def outLaw (n : ℕ) (pop : List (List Bool)) : PMF (Str n) :=
  if hT : total n pop = 0 then PMF.pure (fbStr n)
  else PMF.ofFintype (fun x => (leafCount pop x : ℝ≥0∞) / total n pop) (sum_leafCount_div hT)

/-- The output step: a free draw from `ρ`. -/
noncomputable def outA (n : ℕ) (pop : List Particle) : Alg (Str n) :=
  .sample (outLaw n (pop.map Prod.fst)) .ret

/-- The untruncated sampler with `P` trees. -/
noncomputable def branchU (n P : ℕ) : Alg (Str n) :=
  bindA (levelsA n (List.replicate P ([], 1))) (outA n)

/-- The number of trees `P = ⌈B/δ²⌉` of `eq:branch-cap`. -/
noncomputable def branchP (B δ : ℝ) : ℕ := ⌈B / δ ^ 2⌉₊

/-- The cap `q = ⌈4PA/δ⌉` of `eq:branch-cap`. -/
noncomputable def branchQ (A B δ : ℝ) : ℕ := ⌈4 * branchP B δ * A / δ⌉₊

/-- The sampler of `thm:branching`: abort before query `q + 1` and return the fixed fallback. -/
noncomputable def branchAlg (n : ℕ) (A B δ : ℝ) : Alg (Str n) :=
  capAlg (fbStr n) (branchQ A B δ) (branchU n (branchP B δ))

/-! ### The run against a fixed guide -/

/-- Attach the guide value to a position. -/
def tag (h : Guide) (w : List Bool) : Particle := (w, h w)

theorem runQ_genA (h : Guide) : ∀ pop : List (List Bool),
    runQ h (genA (pop.map (tag h))) =
      (genP h pop).map fun p => (p.map (tag h), 2 * pop.length)
  | [] => by simp [genA, genP, PMF.pure_map]
  | u :: rest => by
      simp only [List.map_cons, tag, genA, runQ_query, runQ_sample, runQ_bindA, runQ_ret]
      have ih := runQ_genA h rest
      rw [ih]
      simp only [genP, offspring, lam, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.pure_bind,
        PMF.map_comp, Function.comp_def, PMF.pure_map, kids, List.map_append, List.map_replicate,
        List.length_cons]
      congr 1

theorem runQ_levelsA (h : Guide) : ∀ (t : ℕ) (pop : List (List Bool)),
    runQ h (levelsA t (pop.map (tag h))) =
      (levelsP h t pop).map fun pc => (pc.1.map (tag h), pc.2)
  | 0, pop => by simp [levelsA, levelsP, PMF.pure_map]
  | t + 1, pop => by
      simp only [levelsA, levelsP, runQ_bindA, runQ_levelsA h t pop, PMF.bind_map,
        PMF.map_bind, Function.comp_def, runQ_genA, PMF.map_comp]

theorem runQ_outA (h : Guide) (pop : List Particle) :
    runQ h (outA n pop) = (outLaw n (pop.map Prod.fst)).map fun x => (x, 0) := by
  simp [outA]
  rfl

/-- The joint law of the output and the query count of the untruncated sampler. -/
theorem runQ_branchU {h : Guide} (hroot : h [] = 1) (P : ℕ) :
    runQ h (branchU n P) =
      (levelsP h n (List.replicate P [])).bind fun pc =>
        (outLaw n pc.1).map fun x => (x, pc.2) := by
  have hpop : List.replicate P (([] : List Bool), (1 : ℝ)) =
      (List.replicate P ([] : List Bool)).map (tag h) := by
    simp [List.map_replicate, tag, hroot]
  rw [branchU, hpop, runQ_bindA, runQ_levelsA, PMF.bind_map]
  congr 1; ext1 pc
  simp only [Function.comp_apply, runQ_outA, PMF.map_comp, List.map_map]
  have : Prod.fst ∘ tag h = id := by ext1 w; rfl
  rw [this, List.map_id]
  rfl

/-- The output law of the untruncated sampler. -/
theorem run_branchU {h : Guide} (hroot : h [] = 1) (P : ℕ) :
    (branchU n P).run h = (levelsP h n (List.replicate P [])).bind fun pc => outLaw n pc.1 := by
  rw [run_eq_map_runQ, runQ_branchU hroot, PMF.map_bind]
  congr 1; ext1 pc
  rw [PMF.map_comp]
  exact PMF.map_id _

/-- The abort event of the capped sampler has the probability that the generated forest has more
than `q` queries. -/
theorem probE_branchU_count {h : Guide} (hroot : h [] = 1) (P q : ℕ) :
    probE (runQ h (branchU n P)) {bc | q < bc.2} =
      probE (levelsP h n (List.replicate P [])) {pc | q < pc.2} := by
  rw [runQ_branchU hroot]
  unfold probE
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  congr 1; ext1 pc
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hpc : q < pc.2
  · have : (fun x : Str n => (x, pc.2)) ⁻¹' {bc | q < bc.2} = Set.univ := by
      ext x; simp [hpc]
    rw [this, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)]
    simp [Set.indicator, hpc]
  · have : (fun x : Str n => (x, pc.2)) ⁻¹' {bc | q < bc.2} = ∅ := by
      ext x; simp [hpc]
    rw [this]
    simp [Set.indicator, hpc]

/-- The cap of `eq:branch-cap` holds against every guide. -/
theorem within_branchAlg (h : Guide) (A B δ : ℝ) :
    (branchAlg n A B δ).Within h (branchQ A B δ) :=
  within_capAlg h _ _ _

end Branching
end LearningGuided
