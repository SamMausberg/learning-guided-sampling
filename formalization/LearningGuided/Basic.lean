import Mathlib

/-!
# Strings, prefix masses, guides and the two guidance models

This file fixes the access model of Section 1.1 of the paper.

* A target is a probability distribution `μ : Str n → ℝ` on `{0,1}^n` (`IsDist`).
* `mass μ u = μ(u) = ∑_{x ⪰ u} μ(x)` is its prefix mass.
* A guide is a function `h : List Bool → ℝ`. Its domain in the paper is `{0,1}^{≤ n}`; here
  words longer than `n` are allowed as queries but always answer `0` (`IsOracle.long`), so they
  carry no information.
* `PwLegal R μ h` is the pointwise factor-`R` model and `SafeLegal R C μ h` the model
  `h ≤ R μ`, `CC(μ,h) ≤ C` of equation `eq:capacity-model`.
* `CapLE`, `CapEq` express the stopped reciprocal capacity `CC(μ,h)` of `eq:capacity-model`,
  `defect` and `DefectEq` the stopped additive defect of `eq:defect`, and `IsCorrection` a
  coherent correction.
-/

open scoped BigOperators

namespace LearningGuided

/-- Binary strings of length `n`. -/
abbrev Str (n : ℕ) := Fin n → Bool

/-- `IsPre u x`: the word `u` is a prefix of the string `x` (written `u ⪯ x` in the paper). -/
def IsPre {n : ℕ} (u : List Bool) (x : Str n) : Prop := u <+: List.ofFn x

instance {n : ℕ} (u : List Bool) (x : Str n) : Decidable (IsPre u x) :=
  inferInstanceAs (Decidable (u <+: List.ofFn x))

/-- Prefix mass `μ(u) = ∑_{x ⪰ u} μ(x)`. -/
noncomputable def mass {n : ℕ} (μ : Str n → ℝ) (u : List Bool) : ℝ :=
  ∑ x : Str n, if IsPre u x then μ x else 0

/-- `μ` is a probability distribution on `{0,1}^n`. -/
def IsDist {n : ℕ} (μ : Str n → ℝ) : Prop := (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The uniform distribution `U_n`. -/
noncomputable def unif (n : ℕ) : Str n → ℝ := fun _ => ((2 : ℝ) ^ n)⁻¹

/-- The point mass `δ_x`. -/
def dirac {n : ℕ} (x : Str n) : Str n → ℝ := fun y => if y = x then 1 else 0

/-- Total variation distance `TV(μ,ν) = ½ ∑_x |μ(x) - ν(x)|`. -/
noncomputable def tv {n : ℕ} (μ ν : Str n → ℝ) : ℝ := (∑ x, |μ x - ν x|) / 2

/-- A guide: one fixed function on words. -/
abbrev Guide := List Bool → ℝ

/-- The access conditions `eq:oracle`, together with the domain conventions of Section 1.1:
values are nonnegative, the root has value one, complete strings are answered exactly, and words
longer than `n` (outside the domain `{0,1}^{≤ n}`) answer `0`. -/
structure IsOracle {n : ℕ} (μ : Str n → ℝ) (h : Guide) : Prop where
  nonneg : ∀ u, 0 ≤ h u
  root : h [] = 1
  leaf : ∀ x : Str n, h (List.ofFn x) = μ x
  long : ∀ u : List Bool, n < u.length → h u = 0

/-- The pointwise factor-`R` model: `μ/R ≤ h ≤ R μ` on `{0,1}^{≤ n}`. -/
def PwLegal (R : ℝ) {n : ℕ} (μ : Str n → ℝ) (h : Guide) : Prop :=
  IsOracle μ h ∧ ∀ u : List Bool, u.length ≤ n → mass μ u / R ≤ h u ∧ h u ≤ R * mass μ u

/-- A cut: a prefix-free finite set of words of length at most `n` (cuts of mixed depths
are allowed). -/
def IsCut (n : ℕ) (A : Finset (List Bool)) : Prop :=
  (∀ u ∈ A, u.length ≤ n) ∧ ∀ u ∈ A, ∀ v ∈ A, u <+: v → u = v

/-- The reciprocal sum `∑_{u ∈ A} μ(u)²/h(u)` over a set of words. Lean's convention
`x / 0 = 0` gives the paper's convention that `0/0` contributes zero; positive numerators over
zero are excluded separately by `SameSupport`. -/
noncomputable def cutSum {n : ℕ} (μ : Str n → ℝ) (h : Guide) (A : Finset (List Bool)) : ℝ :=
  ∑ u ∈ A, mass μ u ^ 2 / h u

/-- A positive numerator over zero has infinite cost: finite capacity requires `h(u) ≠ 0`
whenever `μ(u) ≠ 0`. -/
def SameSupport {n : ℕ} (μ : Str n → ℝ) (h : Guide) : Prop :=
  ∀ u : List Bool, u.length ≤ n → mass μ u ≠ 0 → h u ≠ 0

/-- `CC(μ,h) ≤ C` for the stopped reciprocal capacity of `eq:capacity-model`. -/
def CapLE {n : ℕ} (μ : Str n → ℝ) (h : Guide) (C : ℝ) : Prop :=
  SameSupport μ h ∧ ∀ A, IsCut n A → cutSum μ h A ≤ C

/-- `CC(μ,h) = C`: the capacity is finite, at most `C`, and some cut attains `C`. -/
def CapEq {n : ℕ} (μ : Str n → ℝ) (h : Guide) (C : ℝ) : Prop :=
  CapLE μ h C ∧ ∃ A, IsCut n A ∧ cutSum μ h A = C

/-- The safe model `h ≤ R μ`, `CC(μ,h) ≤ C` of `eq:capacity-model`. -/
def SafeLegal (R C : ℝ) {n : ℕ} (μ : Str n → ℝ) (h : Guide) : Prop :=
  IsOracle μ h ∧ (∀ u : List Bool, u.length ≤ n → h u ≤ R * mass μ u) ∧ CapLE μ h C

/-- The local additive defect `d_R(u) = max{0, h(u) - R μ(u), μ(u) - R h(u)}` of `eq:defect`. -/
noncomputable def defect (R : ℝ) {n : ℕ} (μ : Str n → ℝ) (h : Guide) (u : List Bool) : ℝ :=
  max 0 (max (h u - R * mass μ u) (mass μ u - R * h u))

/-- `D_R(μ,h) = D`: the maximum over cuts of the summed defects equals `D`. -/
def DefectEq (R : ℝ) {n : ℕ} (μ : Str n → ℝ) (h : Guide) (D : ℝ) : Prop :=
  (∀ A, IsCut n A → ∑ u ∈ A, defect R μ h u ≤ D) ∧
    ∃ A, IsCut n A ∧ ∑ u ∈ A, defect R μ h u = D

/-- A coherent correction: a nonnegative additive measure `κ` on strings with
`κ(u) ≥ d_R(u)` at every prefix. Its mass is `∑_x κ(x)`. -/
def IsCorrection (R : ℝ) {n : ℕ} (μ : Str n → ℝ) (h : Guide) (κ : Str n → ℝ) : Prop :=
  (∀ x, 0 ≤ κ x) ∧ ∀ u : List Bool, u.length ≤ n → defect R μ h u ≤ mass κ u

/-! ### Elementary facts -/

theorem mass_nil {n : ℕ} (μ : Str n → ℝ) : mass μ [] = ∑ x, μ x := by
  simp [mass, IsPre]

theorem mass_ofFn {n : ℕ} (μ : Str n → ℝ) (x : Str n) : mass μ (List.ofFn x) = μ x := by
  unfold mass
  rw [Finset.sum_eq_single x]
  · simp [IsPre]
  · intro y _ hy
    have : ¬ IsPre (List.ofFn x) y := by
      intro hp
      apply hy
      have hl : (List.ofFn x).length = (List.ofFn y).length := by simp
      exact (List.ofFn_injective (hp.eq_of_length hl)).symm
    simp [this]
  · simp

theorem mass_nonneg {n : ℕ} {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) (u : List Bool) :
    0 ≤ mass μ u :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hμ x]

theorem tv_comm {n : ℕ} (μ ν : Str n → ℝ) : tv μ ν = tv ν μ := by
  unfold tv
  congr 1
  exact Finset.sum_congr rfl fun x _ => abs_sub_comm _ _

theorem tv_nonneg {n : ℕ} (μ ν : Str n → ℝ) : 0 ≤ tv μ ν :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_triangle {n : ℕ} (μ ν ρ : Str n → ℝ) : tv μ ρ ≤ tv μ ν + tv ν ρ := by
  unfold tv
  rw [← add_div, ← Finset.sum_add_distrib]
  gcongr with x
  exact abs_sub_le _ _ _

/-- If `TV(p, μ) ≤ δ` for two distributions, then every event loses at most `δ`. -/
theorem sum_le_sum_add_tv {n : ℕ} {p μ : Str n → ℝ} (hp : ∑ x, p x = 1) (hμ : ∑ x, μ x = 1)
    (E : Finset (Str n)) : ∑ x ∈ E, μ x ≤ ∑ x ∈ E, p x + tv p μ := by
  classical
  have hsplit : ∀ f : Str n → ℝ, ∑ x, f x = ∑ x ∈ E, f x + ∑ x ∈ Eᶜ, f x := fun f => by
    rw [Finset.sum_add_sum_compl]
  have h1 : ∑ x ∈ E, (μ x - p x) = ∑ x ∈ Eᶜ, (p x - μ x) := by
    have := hsplit p; have := hsplit μ
    simp only [Finset.sum_sub_distrib]; linarith
  have h2 : ∑ x ∈ E, (μ x - p x) ≤ ∑ x ∈ E, |p x - μ x| :=
    Finset.sum_le_sum fun x _ => by rw [abs_sub_comm]; exact le_abs_self _
  have h3 : ∑ x ∈ Eᶜ, (p x - μ x) ≤ ∑ x ∈ Eᶜ, |p x - μ x| :=
    Finset.sum_le_sum fun x _ => le_abs_self _
  have h4 : ∑ x, |p x - μ x| = ∑ x ∈ E, |p x - μ x| + ∑ x ∈ Eᶜ, |p x - μ x| := hsplit _
  have h5 : ∑ x ∈ E, (μ x - p x) ≤ tv p μ := by unfold tv; linarith
  simp only [Finset.sum_sub_distrib] at h5
  linarith

end LearningGuided
