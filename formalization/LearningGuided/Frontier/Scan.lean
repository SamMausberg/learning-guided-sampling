import LearningGuided.Upper.Identify

/-!
# Scans of the safe frontier learner (Appendix `app:frontier`)

A scan follows the path of a string `x` (drawn for free from the uniform mixture `η` of the
version space), querying both children at each internal prefix, and stops at the first parent
having a child `v` with `h(v) > 2Rη(v)`. It returns the violating child and its value, or, if no
parent violates, the value at the leaf (the root value `1 = h(∅)` is known without a query).

* `scanPath R η u rest val` is the query algorithm; it makes exactly two queries per internal
  prefix, hence at most `2n` per scan (`within_scanPath`).
* Against a fixed guide its run is the point mass at `scanPathFn h R η u rest val`
  (`run_scanPath`).
* `Stops h R η x`: some prefix `x_{1:t}`, `t < n`, has a violating child. The scan of `x` stops
  exactly when `Stops` holds (`scanPathFn_isLeft_iff`); a returned violation `(v,a)` has
  `a = h(v) > 2Rη(v)` (`scanPathFn_inl`); a passing scan returns the leaf value and certifies
  `h(x) ≤ 2Rη(x)` (`scanPathFn_inr`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Frontier

open Upper

variable {n : ℕ}

/-- The uniform mixture `η` of a finite class. -/
noncomputable def mix (G : Finset (Str n → ℝ)) : Str n → ℝ := fun x => (∑ φ ∈ G, φ x) / G.card

theorem mass_mix (G : Finset (Str n → ℝ)) (u : List Bool) :
    mass (mix G) u = (∑ φ ∈ G, mass φ u) / G.card := by
  unfold mass mix
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem isDist_mix {G : Finset (Str n → ℝ)} (hne : G.Nonempty) (hG : ∀ φ ∈ G, IsDist φ) :
    IsDist (mix G) := by
  have hc : (0 : ℝ) < G.card := by exact_mod_cast hne.card_pos
  refine ⟨fun x => div_nonneg (Finset.sum_nonneg fun φ hφ => (hG φ hφ).1 x) hc.le, ?_⟩
  unfold mix
  rw [← Finset.sum_div, Finset.sum_comm, Finset.sum_congr rfl fun φ hφ => (hG φ hφ).2]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact div_self hc.ne'

/-- The result of a scan: a violating child with its value, or the value at the leaf. -/
abbrev ScanRes := (List Bool × ℝ) ⊕ ℝ

/-- Follow the remaining path `rest` from the prefix `u`, whose value is `val`: query both
children, stop at a violating child, and otherwise move to the next prefix on the path. -/
noncomputable def scanPath (R : ℝ) (η : Str n → ℝ) : List Bool → List Bool → ℝ → Alg ScanRes
  | _, [], val => .ret (.inr val)
  | u, b :: rest, _ =>
      .query (u ++ [false]) fun a0 =>
      .query (u ++ [true]) fun a1 =>
        if 2 * R * mass η (u ++ [false]) < a0 then .ret (.inl (u ++ [false], a0))
        else if 2 * R * mass η (u ++ [true]) < a1 then .ret (.inl (u ++ [true], a1))
        else scanPath R η (u ++ [b]) rest (if b then a1 else a0)

/-- The result of a scan against a fixed guide. -/
noncomputable def scanPathFn (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    List Bool → List Bool → ℝ → ScanRes
  | _, [], val => .inr val
  | u, b :: rest, _ =>
      if 2 * R * mass η (u ++ [false]) < h (u ++ [false]) then .inl (u ++ [false], h (u ++ [false]))
      else if 2 * R * mass η (u ++ [true]) < h (u ++ [true]) then
        .inl (u ++ [true], h (u ++ [true]))
      else scanPathFn h R η (u ++ [b]) rest (h (u ++ [b]))

theorem run_scanPath (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    ∀ (rest u : List Bool) (val : ℝ),
      (scanPath R η u rest val).run h = PMF.pure (scanPathFn h R η u rest val)
  | [], u, val => rfl
  | b :: rest, u, val => by
      have hb : (if b = true then h (u ++ [true]) else h (u ++ [false])) = h (u ++ [b]) := by
        cases b <;> rfl
      simp only [scanPath, scanPathFn, Alg.run_query, hb]
      split_ifs
      · rfl
      · rfl
      · exact run_scanPath h R η rest _ _

/-- A scan makes two queries per internal prefix. -/
theorem within_scanPath (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    ∀ (rest u : List Bool) (val : ℝ), (scanPath R η u rest val).Within h (2 * rest.length)
  | [], u, val => Alg.Within.ret _ _
  | b :: rest, u, val => by
      simp only [scanPath, List.length_cons]
      have : 2 * (rest.length + 1) = (2 * rest.length + 1) + 1 := by ring
      rw [this]
      refine Alg.Within.query _ _ _ (Alg.Within.query _ _ _ ?_)
      split_ifs
      all_goals first
        | exact Alg.Within.ret _ _
        | exact within_scanPath h R η rest _ _

/-- A parent `u` has a violating child. -/
def ViolAt (h : Guide) (R : ℝ) (η : Str n → ℝ) (u : List Bool) : Prop :=
  2 * R * mass η (u ++ [false]) < h (u ++ [false]) ∨ 2 * R * mass η (u ++ [true]) < h (u ++ [true])

/-- The scan of `x` stops: some prefix `x_{1:t}`, `t < n`, has a violating child. -/
def Stops (h : Guide) (R : ℝ) (η : Str n → ℝ) (x : Str n) : Prop :=
  ∃ t < n, ViolAt h R η (pre x t)

theorem scanPathFn_inl (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    ∀ (rest u : List Bool) (val : ℝ) (v : List Bool) (a : ℝ),
      scanPathFn h R η u rest val = .inl (v, a) →
        a = h v ∧ 2 * R * mass η v < a ∧ v.length ≤ u.length + rest.length
  | [], u, val, v, a, hs => by simp [scanPathFn] at hs
  | b :: rest, u, val, v, a, hs => by
      simp only [scanPathFn] at hs
      split_ifs at hs with h0 h1
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨rfl, h0, by simp⟩
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨rfl, h1, by simp⟩
      · obtain ⟨e1, e2, e3⟩ := scanPathFn_inl h R η rest _ _ v a hs
        refine ⟨e1, e2, ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at e3 ⊢
        omega

theorem scanPathFn_isLeft_iff (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    ∀ (rest u : List Bool) (val : ℝ),
      (scanPathFn h R η u rest val).isLeft ↔
        ∃ k < rest.length, ViolAt h R η (u ++ rest.take k)
  | [], u, val => by simp [scanPathFn]
  | b :: rest, u, val => by
      simp only [scanPathFn]
      by_cases hv : ViolAt h R η u
      · have hv' := hv
        rcases hv with h0 | h1
        · simp only [h0, ↓reduceIte, Sum.isLeft_inl, true_iff]
          exact ⟨0, by simp, by simpa using hv'⟩
        · by_cases h0 : 2 * R * mass η (u ++ [false]) < h (u ++ [false])
          · simp only [h0, ↓reduceIte, Sum.isLeft_inl, true_iff]
            exact ⟨0, by simp, by simpa using hv'⟩
          · simp only [h0, ↓reduceIte, h1, Sum.isLeft_inl, true_iff]
            exact ⟨0, by simp, by simpa using hv'⟩
      · have h0 : ¬ 2 * R * mass η (u ++ [false]) < h (u ++ [false]) := fun h0 => hv (Or.inl h0)
        have h1 : ¬ 2 * R * mass η (u ++ [true]) < h (u ++ [true]) := fun h1 => hv (Or.inr h1)
        simp only [h0, ↓reduceIte, h1]
        rw [scanPathFn_isLeft_iff h R η rest]
        constructor
        · rintro ⟨k, hk, hvk⟩
          refine ⟨k + 1, by simp; omega, ?_⟩
          simpa [List.take_succ_cons] using hvk
        · rintro ⟨k, hk, hvk⟩
          rcases k with _ | k
          · exact absurd (by simpa using hvk) hv
          · refine ⟨k, by simp at hk; omega, ?_⟩
            simpa [List.take_succ_cons] using hvk

theorem scanPathFn_inr (h : Guide) (R : ℝ) (η : Str n → ℝ) :
    ∀ (rest u : List Bool) (val a : ℝ), scanPathFn h R η u rest val = .inr a →
      (rest = [] ∧ a = val) ∨
        (rest ≠ [] ∧ a = h (u ++ rest) ∧ h (u ++ rest) ≤ 2 * R * mass η (u ++ rest))
  | [], u, val, a, hs => by simp only [scanPathFn, Sum.inr.injEq] at hs; exact Or.inl ⟨rfl, hs.symm⟩
  | b :: rest, u, val, a, hs => by
      simp only [scanPathFn] at hs
      split_ifs at hs with h0 h1
      have h0' := not_lt.mp h0
      have h1' := not_lt.mp h1
      refine Or.inr ⟨by simp, ?_⟩
      rcases scanPathFn_inr h R η rest _ _ a hs with ⟨rfl, rfl⟩ | ⟨_, e1, e2⟩
      · refine ⟨rfl, ?_⟩
        cases b
        · exact h0'
        · exact h1'
      · simp only [List.append_assoc, List.cons_append, List.nil_append] at e1 e2
        exact ⟨e1, e2⟩

/-- The scan of `x` from the root. -/
noncomputable def scanFn (h : Guide) (R : ℝ) (η : Str n → ℝ) (x : Str n) : ScanRes :=
  scanPathFn h R η [] (List.ofFn x) 1

theorem scanFn_isLeft_iff (h : Guide) (R : ℝ) (η : Str n → ℝ) (x : Str n) :
    (scanFn h R η x).isLeft ↔ Stops h R η x := by
  rw [scanFn, scanPathFn_isLeft_iff, List.length_ofFn]
  simp only [List.nil_append, Stops, pre]

end Frontier
end LearningGuided
