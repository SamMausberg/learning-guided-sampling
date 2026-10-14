import LearningGuided.PointwiseLB.Params

/-!
# Generic helpers for Appendix B

* `mass_eq_of_additive`: a function on words that is additive over children and agrees with
  `μ` at complete strings is the prefix mass of `μ`.
* `mass_const`, `mass_mono`: prefix masses of constants and monotonicity.
* List prefix facts used to compute block masses.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-- The string of length `n` spelled by a word of length `n`. -/
def strOf {n : ℕ} (u : List Bool) (hu : u.length = n) : Str n := fun i => u[i.1]'(by omega)

theorem ofFn_strOf {n : ℕ} (u : List Bool) (hu : u.length = n) :
    List.ofFn (strOf u hu) = u := by
  apply List.ext_getElem (by simp [hu])
  intro i h1 h2
  simp [strOf]

theorem mass_word_full {n : ℕ} (μ : Str n → ℝ) (u : List Bool) (hu : u.length = n) :
    mass μ u = μ (strOf u hu) := by
  conv_lhs => rw [← ofFn_strOf u hu]
  exact mass_ofFn μ _

/-- A function on words that is additive over the two children below depth `n` and agrees with
`μ` at complete strings is the prefix mass of `μ`. -/
theorem mass_eq_of_additive {n : ℕ} (μ : Str n → ℝ) (F : List Bool → ℝ)
    (hleaf : ∀ x : Str n, F (List.ofFn x) = μ x)
    (hadd : ∀ u : List Bool, u.length < n → F u = F (u ++ [false]) + F (u ++ [true])) :
    ∀ u : List Bool, u.length ≤ n → mass μ u = F u := by
  intro u hu
  obtain ⟨m, hm⟩ : ∃ m, n - u.length = m := ⟨_, rfl⟩
  induction m generalizing u with
  | zero =>
      have hl : u.length = n := by omega
      rw [mass_word_full μ u hl, ← hleaf, ofFn_strOf]
  | succ m ih =>
      have hlt : u.length < n := by omega
      rw [mass_children μ hlt, hadd u hlt, ih (u ++ [false]) (by simp; omega) (by simp; omega),
        ih (u ++ [true]) (by simp; omega) (by simp; omega)]

theorem mass_mono {n : ℕ} {μ ν : Str n → ℝ} (h : ∀ x, μ x ≤ ν x) (u : List Bool) :
    mass μ u ≤ mass ν u :=
  Finset.sum_le_sum fun x _ => by split_ifs <;> simp [h x]

theorem mass_smul {n : ℕ} (c : ℝ) (μ : Str n → ℝ) (u : List Bool) :
    mass (fun x => c * μ x) u = c * mass μ u := by
  unfold mass; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp

/-- The prefix mass of a constant function: `c · 2^{n - |u|}`. -/
theorem mass_const {n : ℕ} (c : ℝ) {u : List Bool} (hu : u.length ≤ n) :
    mass (fun _ : Str n => c) u = c * 2 ^ (n - u.length) := by
  have h1 : (fun _ : Str n => c) = fun x => (c * 2 ^ n) * unif n x := by
    funext x; simp [unif]
  rw [h1, mass_smul, mass_unif hu]
  have : (2 : ℝ) ^ n = 2 ^ (n - u.length) * 2 ^ u.length := by
    rw [← pow_add, Nat.sub_add_cancel hu]
  rw [this]; field_simp

/-- Extending a prefix of a word by one letter. -/
theorem prefix_append_singleton_iff {u L : List Bool} {b : Bool} :
    (u ++ [b]) <+: L ↔ u <+: L ∧ L[u.length]? = some b := by
  constructor
  · intro h
    refine ⟨(List.prefix_append u [b]).trans h, ?_⟩
    have := (List.prefix_iff_getElem?.mp h) u.length (by simp)
    simpa using this
  · rintro ⟨hu, hb⟩
    rw [List.prefix_iff_getElem?]
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i u.length with h | h
    · rw [List.getElem_append_left h]
      exact (List.prefix_iff_getElem?.mp hu) i h
    · have hi' : i = u.length := by omega
      subst hi'
      simpa using hb

/-- For a word shorter than `L`, exactly one of its two children is a prefix of `L` when the
word itself is. -/
theorem prefix_children_indicator {u L : List Bool} (hu : u.length < L.length) :
    (if u <+: L then (1 : ℝ) else 0) =
      (if (u ++ [false]) <+: L then 1 else 0) + (if (u ++ [true]) <+: L then 1 else 0) := by
  simp only [prefix_append_singleton_iff]
  have hget : L[u.length]? = some L[u.length] := List.getElem?_eq_getElem hu
  rw [hget]
  by_cases h : u <+: L <;> cases L[u.length] <;> simp [h]

/-- Real value of a label. -/
def yv (b : Bool) : ℝ := if b then 1 else 0

theorem yv_nonneg (b : Bool) : 0 ≤ yv b := by unfold yv; split_ifs <;> norm_num

theorem yv_le_one (b : Bool) : yv b ≤ 1 := by unfold yv; split_ifs <;> norm_num

end LearningGuided.PointwiseLB
