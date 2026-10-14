import LearningGuided.Sec3.Common

/-!
# Guides with public answers on selected prefixes

The lower-bound guides of Section 3 answer a fixed set `Pub` of proper prefixes with the known
background mass `ν(u)` and every other word exactly. This is the construction of Lemma
`lem:public-capacity`; the facts needed here are proved directly:

* `pubGuide_isOracle`, `pubGuide_le`: the guide satisfies `eq:oracle` and `h ≤ (4/3)μ`;
* `pubGuide_pathValue`, `pubGuide_capLE`: the path reduction of `Cuts.lean` bounds the stopped
  capacity by the largest public path value `1 + α - 2α² - aαν(u) + α²/ν(u)`;
* `pubGuide_pwLegal`: if every public word has `ν(u) ≥ 3α`, the guide is pointwise factor `4/3`;
* `eqStructure_pub`: if every nonpublic word is a prefix of at most one possible atom, every
  query is simulated by at most one equality test.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

open Classical in
/-- Public background answers `ν(u)` on the words of `Pub`, exact answers elsewhere. -/
noncomputable def pubGuide (ν : Str n → ℝ) (α : ℝ) (x : Str n) (Pub : List Bool → Prop) :
    Guide :=
  fun u => if Pub u then mass ν u else mass (atomTarget ν α x) u

theorem pubGuide_pub {ν : Str n → ℝ} {α : ℝ} {x : Str n} {Pub : List Bool → Prop}
    {u : List Bool} (hu : Pub u) : pubGuide ν α x Pub u = mass ν u := by
  classical
  simp [pubGuide, hu]

theorem pubGuide_nonpub {ν : Str n → ℝ} {α : ℝ} {x : Str n} {Pub : List Bool → Prop}
    {u : List Bool} (hu : ¬ Pub u) : pubGuide ν α x Pub u = mass (atomTarget ν α x) u := by
  classical
  simp [pubGuide, hu]

theorem pubGuide_isOracle {ν : Str n → ℝ} (hν : IsDist ν) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x : Str n) {Pub : List Bool → Prop} (hPub : ∀ u, Pub u → u.length < n) :
    IsOracle (atomTarget ν α x) (pubGuide ν α x Pub) where
  nonneg u := by
    by_cases hu : Pub u
    · rw [pubGuide_pub hu]
      exact mass_nonneg hν.1 u
    · rw [pubGuide_nonpub hu]
      exact mass_nonneg (isDist_atomTarget hν hα0 hα1 x).1 u
  root := by
    by_cases hu : Pub []
    · rw [pubGuide_pub hu, mass_nil, hν.2]
    · rw [pubGuide_nonpub hu, mass_nil, (isDist_atomTarget hν hα0 hα1 x).2]
  leaf y := by
    have : ¬ Pub (List.ofFn y) := fun hp => by have := hPub _ hp; simp at this
    rw [pubGuide_nonpub this, mass_ofFn]
  long u hu := by
    have : ¬ Pub u := fun hp => by have := hPub _ hp; omega
    rw [pubGuide_nonpub this, mass_eq_zero_of_long _ hu]

/-- `lem:public-capacity`, safety with factor `4/3`: `h ≤ μ/a ≤ (4/3)μ` on public words, since
`μ ≥ aν`. -/
theorem pubGuide_le {ν : Str n → ℝ} (hν : IsDist ν) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4)
    (x : Str n) (Pub : List Bool → Prop) (u : List Bool) :
    pubGuide ν α x Pub u ≤ 4 / 3 * mass (atomTarget ν α x) u := by
  have hm := mass_nonneg hν.1 u
  by_cases hu : Pub u
  · rw [pubGuide_pub hu, mass_atomTarget]
    have : (0 : ℝ) ≤ α * (if IsPre u x then 1 else 0) := by
      split_ifs <;> simp [hα0]
    nlinarith
  · rw [pubGuide_nonpub hu]
    have := mass_nonneg (isDist_atomTarget hν hα0 (by linarith) x).1 u
    linarith

/-- The value `1 - μ(u) + μ(u)²/ν(u)` of the path cut at a public ancestor `u` of the atom. -/
theorem pubGuide_pathValue {ν : Str n → ℝ} {α : ℝ} {x : Str n} {Pub : List Bool → Prop}
    {u : List Bool} (hu : Pub u) (hux : IsPre u x) (hpos : 0 < mass ν u) :
    1 - mass (atomTarget ν α x) u + mass (atomTarget ν α x) u ^ 2 / pubGuide ν α x Pub u =
      1 + α - 2 * α ^ 2 - (1 - α) * α * mass ν u + α ^ 2 / mass ν u := by
  rw [pubGuide_pub hu, mass_atomTarget, ite_eq_left hux]
  field_simp
  ring

theorem sq_div_le_of_le {m h : ℝ} (hm : 0 ≤ m) (hmh : m ≤ h) : m ^ 2 / h ≤ m := by
  rcases eq_or_lt_of_le (hm.trans hmh) with h0 | hpos
  · rw [← h0, div_zero]
    exact hm
  · rw [div_le_iff₀ hpos]
    nlinarith

theorem mass_pos_of_full {ν : Str n → ℝ} (hν : IsDist ν) (hfull : ∀ y, 0 < ν y)
    {u : List Bool} (hu : u.length ≤ n) : 0 < mass ν u := by
  classical
  have hy : IsPre u (strOf n u) := by
    unfold IsPre
    rw [List.prefix_iff_getElem?]
    intro i hi
    have hin : i < n := by omega
    simp [strOf, hin, hi, List.getD_eq_getElem?_getD]
  unfold mass
  refine lt_of_lt_of_le (hfull (strOf n u)) ?_
  calc ν (strOf n u) = if IsPre u (strOf n u) then ν (strOf n u) else 0 := by rw [ite_eq_left hy]
    _ ≤ ∑ y, if IsPre u y then ν y else 0 :=
        Finset.single_le_sum (f := fun y => if IsPre u y then ν y else 0)
          (fun y _ => by split_ifs <;> simp [hν.1 y]) (Finset.mem_univ _)

/-- `lem:public-capacity`, upper bound: the stopped capacity of the public-answer guide is at most
`F` whenever every public path value `1 + α - 2α² - aαν(u) + α²/ν(u)` is at most `F ≥ 1` (path
reduction). -/
theorem pubGuide_capLE {ν : Str n → ℝ} (hν : IsDist ν) (hfull : ∀ y, 0 < ν y) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x : Str n) {Pub : List Bool → Prop} {F : ℝ} (hF : 1 ≤ F)
    (hpath : ∀ t ≤ n, Pub (pre x t) →
      1 + α - 2 * α ^ 2 - (1 - α) * α * mass ν (pre x t) + α ^ 2 / mass ν (pre x t) ≤ F) :
    CapLE (atomTarget ν α x) (pubGuide ν α x Pub) F := by
  have hμ := isDist_atomTarget hν hα0 hα1 x
  refine ⟨fun u hu hz => ?_, cutSum_le_of_path hμ x hF (fun u hu hux => ?_) (fun t ht => ?_)⟩
  · by_cases hp : Pub u
    · rw [pubGuide_pub hp]
      exact (mass_pos_of_full hν hfull hu).ne'
    · rw [pubGuide_nonpub hp]
      exact hz
  · by_cases hp : Pub u
    · rw [pubGuide_pub hp]
      have hm : mass (atomTarget ν α x) u = (1 - α) * mass ν u := by
        rw [mass_atomTarget, ite_eq_right hux]
        ring
      have h0 := mass_nonneg hν.1 u
      refine sq_div_le_of_le (mass_nonneg hμ.1 u) ?_
      rw [hm]
      nlinarith
    · rw [pubGuide_nonpub hp]
      exact sq_div_self_le (mass_nonneg hμ.1 u)
  · by_cases hp : Pub (pre x t)
    · rw [pubGuide_pathValue hp (isPre_pre x t)
        (mass_pos_of_full hν hfull ((length_pre x ht).le.trans ht))]
      exact hpath t ht hp
    · rw [pubGuide_nonpub hp, sq_div_self_eq]
      linarith

/-- The public-answer guide is pointwise factor `4/3` when every public word has background mass
at least `3α` (and `α ≤ 1/4`). -/
theorem pubGuide_pwLegal {ν : Str n → ℝ} (hν : IsDist ν) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ 1 / 4) (x : Str n) {Pub : List Bool → Prop} (hPub : ∀ u, Pub u → u.length < n)
    (hheavy : ∀ u, Pub u → 3 * α ≤ mass ν u) :
    PwLegal (4 / 3) (atomTarget ν α x) (pubGuide ν α x Pub) := by
  have hμ := isDist_atomTarget hν hα0 (by linarith) x
  refine ⟨pubGuide_isOracle hν hα0 (by linarith) x hPub, fun u _ => ⟨?_, pubGuide_le hν hα0 hα
    x Pub u⟩⟩
  by_cases hp : Pub u
  · rw [pubGuide_pub hp, mass_atomTarget]
    have h3 := hheavy u hp
    have : α * (if IsPre u x then (1 : ℝ) else 0) ≤ α := by
      split_ifs <;> simp [hα0]
    have hm := mass_nonneg hν.1 u
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  · rw [pubGuide_nonpub hp]
    have := mass_nonneg hμ.1 u
    linarith

/-- If every nonpublic word is a prefix of at most one possible atom, the family of public-answer
guides has equality structure: each query is simulated by at most one equality test. -/
theorem eqStructure_pub {Θ : Type} (ν : Str n → ℝ) (α : ℝ) (X : Θ → Str n)
    (Pub : List Bool → Prop)
    (huniq : ∀ u, ¬ Pub u → ∀ θ θ', IsPre u (X θ) → IsPre u (X θ') → θ = θ') :
    EqualityStructure fun θ => pubGuide ν α (X θ) Pub := by
  classical
  intro u
  by_cases hp : Pub u
  · exact ⟨none, mass ν u, fun θ _ => pubGuide_pub hp⟩
  · by_cases hex : ∃ θ, IsPre u (X θ)
    · refine ⟨some hex.choose, (1 - α) * mass ν u, fun θ hθ => ?_⟩
      have hn : ¬ IsPre u (X θ) := fun h =>
        hθ (congrArg some (huniq u hp _ _ hex.choose_spec h))
      beta_reduce
      rw [pubGuide_nonpub hp, mass_atomTarget, ite_eq_right hn]
      ring
    · refine ⟨none, (1 - α) * mass ν u, fun θ _ => ?_⟩
      have hn : ¬ IsPre u (X θ) := fun h => hex ⟨θ, h⟩
      beta_reduce
      rw [pubGuide_nonpub hp, mass_atomTarget, ite_eq_right hn]
      ring

end LearningGuided.Sec3
