import LearningGuided.PointwiseLB.Information

/-!
# Simulating one guide by another, and padding with zeros

* `simAlg`: if every query to a guide `h'` can be answered either by a known constant or by one
  query to another guide `h` followed by a known post-processing, then every algorithm against
  `h'` is turned into an algorithm against `h` with the same output law and no larger cap.
* Padding (the extension of Theorem `pw-thm:parameter` from `N` to `n ≥ N` bits): a target on
  `N` bits is extended by deterministic zeros; the oracle keeps its values on prefixes of length
  at most `N`, returns the old leaf value on longer prefixes whose padding bits are zero, and `0`
  otherwise. The padded oracle is legal for the padded target, and every query is simulated by at
  most one old query.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-- One simulated query. -/
inductive SimStep : Type where
  /-- A known answer. -/
  | const : ℝ → SimStep
  /-- One query to the old guide at `u`, post-processed by `f`. -/
  | ask : List Bool → (ℝ → ℝ) → SimStep

/-- The answer produced by a simulated query. -/
def SimStep.eval (h : Guide) : SimStep → ℝ
  | const v => v
  | ask u f => f (h u)

/-- The simulating algorithm. -/
noncomputable def simAlg {β : Type} (S : List Bool → SimStep) : Alg β → Alg β
  | .ret b => .ret b
  | .sample p k => .sample p fun g => simAlg S (k g)
  | .query u k =>
      match S u with
      | .const v => simAlg S (k v)
      | .ask u' f => .query u' fun x => simAlg S (k (f x))

theorem run_simAlg {β : Type} {S : List Bool → SimStep} {h h' : Guide}
    (hS : ∀ u, h' u = (S u).eval h) (A : Alg β) : (simAlg S A).run h = A.run h' := by
  induction A with
  | ret b => rfl
  | sample p k ih =>
      simp only [simAlg, Alg.run_sample]
      congr 1; funext g; exact ih g
  | query u k ih =>
      simp only [simAlg, Alg.run_query]
      have := hS u
      cases hSu : S u with
      | const v =>
          rw [hSu] at this; simp only [SimStep.eval] at this
          simp only; rw [ih, this]
      | ask u' f =>
          rw [hSu] at this; simp only [SimStep.eval] at this
          simp only [Alg.run_query]; rw [ih, this]

theorem within_simAlg {β : Type} {S : List Bool → SimStep} {h h' : Guide}
    (hS : ∀ u, h' u = (S u).eval h) (A : Alg β) :
    ∀ q, A.Within h' q → (simAlg S A).Within h q := by
  induction A with
  | ret b => intro q _; exact Alg.Within.ret b q
  | sample p k ih =>
      intro q hq
      exact Alg.Within.sample p _ q fun g hg => ih g q (Alg.within_sample_iff.mp hq g hg)
  | query u k ih =>
      intro q hq
      obtain ⟨r, rfl, hr⟩ := Alg.within_query_iff.mp hq
      have := hS u
      simp only [simAlg]
      cases hSu : S u with
      | const v =>
          rw [hSu] at this; simp only [SimStep.eval] at this
          simp only
          rw [this] at hr
          exact (ih v r hr).mono (Nat.le_succ r)
      | ask u' f =>
          rw [hSu] at this; simp only [SimStep.eval] at this
          simp only
          refine Alg.Within.query u' _ r ?_
          rw [this] at hr
          exact ih _ r hr

/-! ### Padding with zeros -/

section Pad

variable {N n : ℕ}

/-- The first `N` bits of a string of length `n ≥ N`. -/
def trunc (hNn : N ≤ n) (x : Str n) : Str N := fun i => x ⟨i.1, lt_of_lt_of_le i.2 hNn⟩

/-- All padding bits are zero. -/
def PadZero (x : Str n) : Prop := ∀ i : Fin n, N ≤ i.1 → x i = false

instance (x : Str n) : Decidable (PadZero (N := N) x) := by unfold PadZero; infer_instance

/-- The padded target: the old target followed by deterministic zeros. -/
noncomputable def padT (hNn : N ≤ n) (μ : Str N → ℝ) (x : Str n) : ℝ :=
  if PadZero (N := N) x then μ (trunc hNn x) else 0

/-- The padded oracle. -/
noncomputable def padO (N n : ℕ) (h : Guide) (u : List Bool) : ℝ :=
  if u.length ≤ N then h u
  else if u.length ≤ n ∧ ∀ b ∈ u.drop N, b = false then h (u.take N) else 0

/-- The simulation of the padded oracle by one old query. -/
noncomputable def padSim (N n : ℕ) (u : List Bool) : SimStep :=
  if u.length ≤ N then .ask u id
  else if u.length ≤ n ∧ ∀ b ∈ u.drop N, b = false then .ask (u.take N) id else .const 0

theorem padO_eval (h : Guide) (u : List Bool) : padO N n h u = (padSim N n u).eval h := by
  unfold padO padSim
  split_ifs <;> rfl

/-- The mass formula of the padded target. -/
noncomputable def padF (μ : Str N → ℝ) (u : List Bool) : ℝ :=
  if u.length ≤ N then mass μ u
  else if ∀ b ∈ u.drop N, b = false then mass μ (u.take N) else 0

theorem padZero_iff (x : Str n) :
    PadZero (N := N) x ↔ ∀ b ∈ (List.ofFn x).drop N, b = false := by
  constructor
  · intro h b hb
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_drop, List.getElem_ofFn]
    exact h _ (Nat.le_add_right _ _)
  · intro h i hi
    have hlt : i.1 - N < ((List.ofFn x).drop N).length := by simp; omega
    have := h _ (List.getElem_mem hlt)
    rw [List.getElem_drop, List.getElem_ofFn] at this
    have e : (⟨N + (i.1 - N), by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
    rwa [e] at this

theorem take_ofFn_trunc (hNn : N ≤ n) (x : Str n) :
    (List.ofFn x).take N = List.ofFn (trunc hNn x) := by
  apply List.ext_getElem (by simp; omega)
  intro m h1 h2
  simp [trunc]

theorem mass_padT (hNn : N ≤ n) (μ : Str N → ℝ) {u : List Bool} (hu : u.length ≤ n) :
    mass (padT hNn μ) u = padF μ u := by
  refine mass_eq_of_additive (padT hNn μ) (padF μ) (fun x => ?_) (fun v hv => ?_) u hu
  · unfold padF padT
    simp only [List.length_ofFn]
    by_cases hN : n ≤ N
    · have hnN : n = N := le_antisymm hN hNn
      subst hnN
      rw [ite_eq_left le_rfl, mass_ofFn]
      have hz : PadZero (N := n) x := fun i hi => absurd i.2 (by omega)
      rw [ite_eq_left hz]
      rfl
    · rw [ite_eq_right hN]
      by_cases hz : PadZero (N := N) x
      · rw [ite_eq_left ((padZero_iff x).mp hz), ite_eq_left hz, take_ofFn_trunc hNn,
          mass_ofFn]
      · rw [ite_eq_right (mt (padZero_iff x).mpr hz), ite_eq_right hz]
  · unfold padF
    have hl : ∀ x : Bool, (v ++ [x]).length = v.length + 1 := fun x => by simp
    by_cases h1 : v.length + 1 ≤ N
    · rw [ite_eq_left (show v.length ≤ N by omega),
        ite_eq_left (show (v ++ [false]).length ≤ N by rw [hl]; exact h1),
        ite_eq_left (show (v ++ [true]).length ≤ N by rw [hl]; exact h1)]
      exact mass_children μ (by omega)
    · rw [ite_eq_right (show ¬ (v ++ [false]).length ≤ N by rw [hl]; exact h1),
        ite_eq_right (show ¬ (v ++ [true]).length ≤ N by rw [hl]; exact h1)]
      have hd : ∀ x : Bool, (v ++ [x]).drop N = v.drop N ++ [x] := fun x =>
        List.drop_append_of_le_length (by omega)
      have ht : ∀ x : Bool, (v ++ [x]).take N = v.take N := fun x =>
        List.take_append_of_le_length (by omega)
      rw [hd, hd, ht, ht]
      have hfalse : ¬ ∀ b ∈ v.drop N ++ [true], b = false := fun h => by
        simpa using h true (by simp)
      rw [ite_eq_right hfalse, add_zero]
      have hiff : (∀ b ∈ v.drop N ++ [false], b = false) ↔ ∀ b ∈ v.drop N, b = false := by
        simp
      by_cases hN : v.length ≤ N
      · have hvl : v.length = N := by omega
        rw [ite_eq_left hN, List.take_of_length_le hN]
        have : v.drop N = [] := List.drop_of_length_le hvl.le
        rw [this, ite_eq_left (by simp)]
      · rw [ite_eq_right hN]
        by_cases hz : ∀ b ∈ v.drop N, b = false
        · rw [ite_eq_left hz, ite_eq_left (hiff.mpr hz)]
        · rw [ite_eq_right hz, ite_eq_right (mt hiff.mp hz)]

theorem isDist_padT (hNn : N ≤ n) {μ : Str N → ℝ} (hμ : IsDist μ) : IsDist (padT hNn μ) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold padT; split_ifs
    · exact hμ.1 _
    · exact le_rfl
  · rw [← mass_nil, mass_padT hNn μ (by simp)]
    unfold padF; rw [ite_eq_left (by simp), mass_nil, hμ.2]

theorem mass_padT_short (hNn : N ≤ n) (μ : Str N → ℝ) {u : List Bool} (hu : u.length ≤ N) :
    mass (padT hNn μ) u = mass μ u := by
  rw [mass_padT hNn μ (hu.trans hNn)]; unfold padF; rw [ite_eq_left hu]

/-- `pw-thm:parameter`, extension to `n ≥ N`: padding preserves legality: the padded oracle is a
pointwise factor-`R` guide for the padded target, exact at the new leaves. -/
theorem pad_pwLegal (hNn : N ≤ n) {R : ℝ} {μ : Str N → ℝ} {h : Guide}
    (hl : PwLegal R μ h) : PwLegal R (padT hNn μ) (padO N n h) := by
  obtain ⟨⟨hnn, hroot, hleaf, hlong⟩, hb⟩ := hl
  have hleafm : ∀ v : List Bool, v.length = N → h v = mass μ v := fun v hv => by
    rw [mass_word_full μ v hv, ← hleaf, ofFn_strOf]
  refine ⟨⟨fun u => ?_, ?_, fun x => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
  · unfold padO; split_ifs
    · exact hnn _
    · exact hnn _
    · exact le_rfl
  · unfold padO; rw [ite_eq_left (by simp)]; exact hroot
  · rw [← mass_ofFn (padT hNn μ) x, mass_padT hNn μ (by simp)]
    unfold padO padF
    simp only [List.length_ofFn]
    by_cases hN : n ≤ N
    · rw [ite_eq_left hN, ite_eq_left hN]; exact hleafm _ (by simp; omega)
    · rw [ite_eq_right hN, ite_eq_right hN]
      by_cases hz : ∀ b ∈ (List.ofFn x).drop N, b = false
      · rw [ite_eq_left (show n ≤ n ∧ ∀ b ∈ (List.ofFn x).drop N, b = false from
          ⟨le_rfl, hz⟩), ite_eq_left hz]
        exact hleafm _ (by simp; omega)
      · rw [ite_eq_right (show ¬ (n ≤ n ∧ ∀ b ∈ (List.ofFn x).drop N, b = false) from
          fun h => hz h.2), ite_eq_right hz]
  · unfold padO
    rw [ite_eq_right (show ¬ u.length ≤ N by omega),
      ite_eq_right (show ¬ (u.length ≤ n ∧ ∀ b ∈ u.drop N, b = false) from fun h => by omega)]
  · rw [mass_padT hNn μ hu]
    unfold padO padF
    by_cases h1 : u.length ≤ N
    · rw [ite_eq_left h1, ite_eq_left h1]; exact hb u h1
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases hz : ∀ b ∈ u.drop N, b = false
      · rw [ite_eq_left (show u.length ≤ n ∧ ∀ b ∈ u.drop N, b = false from ⟨hu, hz⟩),
          ite_eq_left hz]
        exact hb _ (by simp)
      · rw [ite_eq_right (show ¬ (u.length ≤ n ∧ ∀ b ∈ u.drop N, b = false) from
          fun h => hz h.2), ite_eq_right hz]
        simp

end Pad

end LearningGuided.PointwiseLB
