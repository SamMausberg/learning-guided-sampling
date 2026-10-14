import LearningGuided.Frontier.Scan

/-!
# The first-violation frontier and the weighted Cauchy–Schwarz bound

For a fixed stage (fixed guide `h`, factor `R` and mixture `η`), let `A` be the set of possible
first-violation parents: for each string `x` whose scan stops, the prefix `x_{1:t}` at its first
violation depth `t`. Then

* `A` is prefix-free (`isCut_frontierSet`), and a string lies below an element of `A` exactly when
  its scan stops (`card_filter_frontierSet`), so `ν(A) = ν(stop)` for every `ν`
  (`sum_mass_frontierSet`);
* `h(u) ≤ 2Rη(u)` at every `u ∈ A` (`h_le_frontierSet`): the root has `h = η = 1`, and every other
  element of `A` is a child of a non-violating parent;
* weighted Cauchy–Schwarz: `μ(A)² ≤ (∑_{u∈A} μ(u)²/h(u)) (∑_{u∈A} h(u))` (`sq_sum_le_frontier`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Frontier

open Upper

variable {n : ℕ} (h : Guide) (R : ℝ) (η : Str n → ℝ)

open Classical in
/-- The first violation depth of the scan of `x` (zero if the scan does not stop). -/
noncomputable def firstViol (x : Str n) : ℕ := if hx : Stops h R η x then Nat.find hx else 0

variable {h R η}

theorem firstViol_spec {x : Str n} (hx : Stops h R η x) :
    firstViol h R η x < n ∧ ViolAt h R η (pre x (firstViol h R η x)) := by
  classical
  have := Nat.find_spec hx
  simp only [firstViol, hx, ↓reduceDIte]
  convert this

theorem firstViol_min {x : Str n} (hx : Stops h R η x) {t : ℕ} (ht : t < n)
    (hv : ViolAt h R η (pre x t)) : firstViol h R η x ≤ t := by
  classical
  simp only [firstViol, hx, ↓reduceDIte]
  exact Nat.find_min' hx ⟨ht, hv⟩

variable (h R η)

open Classical in
/-- The first-violation frontier `A`. -/
noncomputable def frontierSet : Finset (List Bool) :=
  (Finset.univ.filter (Stops h R η)).image fun x => pre x (firstViol h R η x)

variable {h R η}

theorem mem_frontierSet {u : List Bool} :
    u ∈ frontierSet h R η ↔ ∃ x, Stops h R η x ∧ pre x (firstViol h R η x) = u := by
  classical
  simp [frontierSet]

theorem pre_eq_of_isPre {u : List Bool} {x : Str n} (hu : IsPre u x) : u = pre x u.length :=
  isPre_iff_pre.mp hu

theorem isPre_of_prefix {u v : List Bool} {x : Str n} (huv : u <+: v) (hv : IsPre v x) :
    IsPre u x := huv.trans hv

/-- `A` is prefix-free. -/
theorem isCut_frontierSet : IsCut n (frontierSet h R η) := by
  refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := mem_frontierSet.mp hu
    rw [length_pre x (firstViol_spec hx).1.le]
    exact (firstViol_spec hx).1.le
  · obtain ⟨x, hx, rfl⟩ := mem_frontierSet.mp hu
    obtain ⟨y, hy, rfl⟩ := mem_frontierSet.mp hv
    have hxn := (firstViol_spec hx).1
    have hyn := (firstViol_spec hy).1
    have hl := huv.length_le
    rw [length_pre x hxn.le, length_pre y hyn.le] at hl
    have hpy : IsPre (pre x (firstViol h R η x)) y := isPre_of_prefix huv (isPre_pre y _)
    have heq := pre_eq_of_isPre hpy
    rw [length_pre x hxn.le] at heq
    have hvy : ViolAt h R η (pre y (firstViol h R η x)) := heq ▸ (firstViol_spec hx).2
    have hle := firstViol_min hy hxn hvy
    have hte : firstViol h R η x = firstViol h R η y := le_antisymm hl hle
    refine huv.eq_of_length ?_
    rw [length_pre x hxn.le, length_pre y hyn.le, hte]

open Classical in
/-- A string lies below an element of `A` exactly when its scan stops. -/
theorem card_filter_frontierSet (x : Str n) :
    ((frontierSet h R η).filter fun u => IsPre u x).card = if Stops h R η x then 1 else 0 := by
  by_cases hx : Stops h R η x
  · rw [ite_eq_left hx]
    refine le_antisymm (isCut_frontierSet.card_filter_isPre_le_one x) ?_
    refine Finset.card_pos.mpr ⟨pre x (firstViol h R η x), Finset.mem_filter.mpr
      ⟨mem_frontierSet.mpr ⟨x, hx, rfl⟩, isPre_pre x _⟩⟩
  · rw [ite_eq_right hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu hux
    obtain ⟨y, hy, rfl⟩ := mem_frontierSet.mp hu
    have hyn := (firstViol_spec hy).1
    have heq := pre_eq_of_isPre hux
    rw [length_pre y hyn.le] at heq
    exact hx ⟨_, hyn, heq ▸ (firstViol_spec hy).2⟩

open Classical in
/-- `ν(A) = ν(stop)`. -/
theorem sum_mass_frontierSet (ν : Str n → ℝ) :
    ∑ u ∈ frontierSet h R η, mass ν u = ∑ x, if Stops h R η x then ν x else 0 := by
  rw [cut_mass_sum_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [card_filter_frontierSet]
  split_ifs <;> simp

theorem pre_succ (x : Str n) {t : ℕ} (ht : t < n) : pre x (t + 1) = pre x t ++ [x ⟨t, ht⟩] := by
  unfold pre
  rw [List.take_add_one, List.getElem?_ofFn]
  simp [ht]

/-- `h(u) ≤ 2Rη(u)` on the frontier. -/
theorem h_le_frontierSet (hroot : h [] = 1) (hη : mass η [] = 1) (hR : 1 ≤ 2 * R) {u : List Bool}
    (hu : u ∈ frontierSet h R η) : h u ≤ 2 * R * mass η u := by
  obtain ⟨x, hx, rfl⟩ := mem_frontierSet.mp hu
  rcases hk : firstViol h R η x with _ | t
  · simp only [pre, List.take_zero, hroot, hη, mul_one]
    exact hR
  · have htn : t < n := by have := (firstViol_spec hx).1; omega
    have hnv : ¬ ViolAt h R η (pre x t) := fun hv => by
      have := firstViol_min hx htn hv
      omega
    rw [pre_succ x htn]
    unfold ViolAt at hnv
    push Not at hnv
    cases x ⟨t, htn⟩
    · exact hnv.1
    · exact hnv.2

/-- Weighted Cauchy–Schwarz on a set of words: `(∑ μ(u))² ≤ (∑ μ(u)²/h(u)) (∑ h(u))`, when
`h ≥ 0` and `h(u) = 0` forces `μ(u) = 0`. -/
theorem sq_sum_le_frontier {μ : Str n → ℝ} (A : Finset (List Bool)) (hnn : ∀ u, 0 ≤ h u)
    (hsupp : ∀ u ∈ A, h u = 0 → mass μ u = 0) :
    (∑ u ∈ A, mass μ u) ^ 2 ≤ cutSum μ h A * ∑ u ∈ A, h u := by
  unfold cutSum
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A (fun u _ => div_nonneg (sq_nonneg _) (hnn u))
    (fun u _ => hnn u) fun u hu => ?_
  rcases eq_or_ne (h u) 0 with h0 | h0
  · rw [hsupp u hu h0, h0]; simp
  · rw [div_mul_cancel₀ _ h0]

end Frontier
end LearningGuided
