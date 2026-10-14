import LearningGuided.Cuts

/-!
# Section 3 preliminaries: composition of algorithms, output laws, atom targets

Shared tools for the formalization of Section 3 (`local-access.tex` and `background.tex`):

* `bindA`: sequential composition of algorithms, with its output law and cap;
* real-valued output laws of point masses, binds over finite types, the uniform law, a coin with
  a prescribed success probability, and a sampler for a known distribution;
* atom targets `(1-α)ν + αδ_x`, their prefix masses, and the classes of Section 3;
* the one-query membership test of Lemma `lem:local-test` and its pointwise analogue.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided.Sec3

open LearningGuided

/-! ### Sequential composition -/

/-- Run `A`, then continue with `f` applied to its output. -/
def bindA {β γ : Type} : Alg β → (β → Alg γ) → Alg γ
  | .ret b, f => f b
  | .query u k, f => .query u fun r => bindA (k r) f
  | .sample p k, f => .sample p fun g => bindA (k g) f

theorem run_bindA {β γ : Type} (h : Guide) (A : Alg β) (f : β → Alg γ) :
    (bindA A f).run h = (A.run h).bind fun b => (f b).run h := by
  induction A with
  | ret b => simp [bindA]
  | query u k ih => simp [bindA, ih]
  | sample p k ih => simp [bindA, ih, PMF.bind_bind]

theorem within_bindA {β γ : Type} {h : Guide} {A : Alg β} {q : ℕ} (hA : A.Within h q)
    {f : β → Alg γ} {r : ℕ} (hf : ∀ b, (f b).Within h r) : (bindA A f).Within h (q + r) := by
  induction hA with
  | ret b q => exact (hf b).mono (by omega)
  | query u k q _ ih =>
      rw [show q + 1 + r = (q + r) + 1 by omega]
      exact Alg.Within.query u _ _ ih
  | sample p k q _ ih => exact Alg.Within.sample p _ _ fun g hg => ih g hg

/-! ### Real-valued output laws -/

theorem lawR_pure {n : ℕ} (x : Str n) : lawR (PMF.pure x) = dirac x := by
  funext y
  simp only [lawR, dirac, PMF.pure_apply]
  split_ifs <;> simp

theorem lawR_bind {γ β : Type} [Fintype γ] (p : PMF γ) (f : γ → PMF β) (y : β) :
    lawR (p.bind f) y = ∑ g, lawR p g * lawR (f g) y := by
  simp only [lawR, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro g _
    exact ENNReal.mul_ne_top (p.apply_ne_top g) ((f g).apply_ne_top y)

theorem lawR_uniformOfFintype {γ : Type} [Fintype γ] [Nonempty γ] (g : γ) :
    lawR (PMF.uniformOfFintype γ) g = (Fintype.card γ : ℝ)⁻¹ := by
  simp [lawR, PMF.uniformOfFintype_apply]

theorem lawR_nonneg {β : Type} (p : PMF β) (b : β) : 0 ≤ lawR p b := ENNReal.toReal_nonneg

/-- A PMF built from a real function. -/
noncomputable def ofReal {γ : Type} [Fintype γ] [Nonempty γ] (f : γ → ℝ) : PMF γ :=
  if hf : (∀ g, 0 ≤ f g) ∧ ∑ g, f g = 1 then
    PMF.ofFintype (fun g => ENNReal.ofReal (f g)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun g _ => hf.1 g, hf.2, ENNReal.ofReal_one])
  else PMF.pure (Classical.arbitrary γ)

theorem lawR_ofReal {γ : Type} [Fintype γ] [Nonempty γ] {f : γ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (h1 : ∑ g, f g = 1) : lawR (ofReal f) = f := by
  funext g
  rw [ofReal, dite_eq_left ⟨h0, h1⟩]
  simp [lawR, PMF.ofFintype_apply, ENNReal.toReal_ofReal (h0 g)]

/-- A coin with success probability `c` (clipped to `[0,1]`). -/
noncomputable def coin (c : ℝ) : PMF Bool :=
  ofReal fun b => if b then max 0 (min c 1) else 1 - max 0 (min c 1)

theorem lawR_coin {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (b : Bool) :
    lawR (coin c) b = if b then c else 1 - c := by
  have hm : max 0 (min c 1) = c := by rw [min_eq_left hc1, max_eq_right hc0]
  rw [coin, lawR_ofReal]
  · simp [hm]
  · intro b
    cases b <;> simp [hc0, hc1]
  · simp

/-- Output a fresh draw from a known distribution `ν`. -/
noncomputable def drawA {n : ℕ} (ν : Str n → ℝ) : Alg (Str n) := .sample (ofReal ν) .ret

theorem lawR_drawA {n : ℕ} {ν : Str n → ℝ} (hν : IsDist ν) (h : Guide) :
    lawR ((drawA ν).run h) = ν := by
  simp only [drawA, Alg.run_sample, Alg.run_ret]
  rw [PMF.bind_pure]
  exact lawR_ofReal hν.1 hν.2

theorem within_drawA {n : ℕ} (ν : Str n → ℝ) (h : Guide) (q : ℕ) : (drawA ν).Within h q :=
  Alg.Within.sample _ _ _ fun g _ => Alg.Within.ret g q

/-! ### Strings from words -/

/-- The string of length `n` whose first bits are those of `u`, padded with zeros. -/
def strOf (n : ℕ) (u : List Bool) : Str n := fun i => u.getD i false

theorem strOf_ofFn {n : ℕ} (y : Str n) : strOf n (List.ofFn y) = y := by
  funext i
  simp [strOf]

theorem ofFn_strOf {n : ℕ} {u : List Bool} (hu : u.length = n) : List.ofFn (strOf n u) = u := by
  apply List.ext_getElem (by simp [hu])
  intro i h1 h2
  simp [strOf, List.getD_eq_getElem?_getD, h2]

theorem eq_strOf_of_isPre {n : ℕ} {u : List Bool} {x : Str n} (hu : u.length = n)
    (hx : IsPre u x) : strOf n u = x := by
  have h1 : u = List.ofFn x := hx.eq_of_length (by simp [hu])
  rw [h1, strOf_ofFn]

/-! ### Atom targets and classes -/

variable {n : ℕ}

/-- The target `(1-α)ν + αδ_x`: a known background `ν` and an atom of weight `α` at `x`. -/
noncomputable def atomTarget (ν : Str n → ℝ) (α : ℝ) (x : Str n) : Str n → ℝ :=
  fun y => (1 - α) * ν y + α * dirac x y

/-- The class `{(1-α)ν + αδ_x : x ∈ S}` of a known background and a known candidate set. -/
def atomClass (ν : Str n → ℝ) (S : Finset (Str n)) (α : ℝ) : Set (Str n → ℝ) :=
  {μ | ∃ x ∈ S, μ = atomTarget ν α x}

theorem mass_atomTarget (ν : Str n → ℝ) (α : ℝ) (x : Str n) (u : List Bool) :
    mass (atomTarget ν α x) u = (1 - α) * mass ν u + α * (if IsPre u x then 1 else 0) := by
  unfold atomTarget
  rw [mass_linear, mass_dirac]

theorem isDist_atomTarget {ν : Str n → ℝ} (hν : IsDist ν) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x : Str n) : IsDist (atomTarget ν α x) :=
  isDist_mix hν (isDist_dirac x) hα0 hα1

theorem atomTarget_apply (ν : Str n → ℝ) (α : ℝ) (x y : Str n) :
    atomTarget ν α x y = (1 - α) * ν y + α * (if y = x then 1 else 0) := rfl

/-- Two atom targets with distinct atoms are at total variation distance `α`. -/
theorem tv_atomTarget {ν : Str n → ℝ} {α : ℝ} (hα : 0 ≤ α) {x x' : Str n} (hxx : x ≠ x') :
    tv (atomTarget ν α x) (atomTarget ν α x') = α := by
  classical
  unfold tv
  have hterm : ∀ y, |atomTarget ν α x y - atomTarget ν α x' y| =
      α * ((if y = x then 1 else 0) + (if y = x' then 1 else 0)) := by
    intro y
    simp only [atomTarget_apply]
    by_cases h1 : y = x <;> by_cases h2 : y = x'
    · exact absurd (h1.symm.trans h2) hxx
    · subst h1
      simp [hxx, abs_of_nonneg hα]
    · subst h2
      simp [Ne.symm hxx, abs_of_nonneg hα]
    · simp [h1, h2]
  simp only [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-! ### One-query membership tests -/

/-- `lem:local-test` (membership test). If a known prefix group either
contains a hidden component of mass `α > 0` (so `μ(u) ≥ α`) or contains none of it (so `μ(u)` is
a known number `b`), and `h(u) ≤ R μ(u)`, `μ(u)² ≤ C h(u)`, `C > 0`, `R b < α²/C`, then the group
contains the component exactly when `h(u) ≥ α²/C`. -/
theorem local_test {R C α b m hu : ℝ} {P : Prop} (hα : 0 < α) (hC : 0 < C)
    (hsafe : hu ≤ R * m) (hcap : m ^ 2 ≤ C * hu) (hgap : R * b < α ^ 2 / C)
    (hP : P → α ≤ m) (hnP : ¬ P → m = b) : P ↔ α ^ 2 / C ≤ hu := by
  constructor
  · intro hp
    have hm := hP hp
    rw [div_le_iff₀ hC]
    nlinarith
  · intro hle
    by_contra hp
    rw [hnP hp] at hsafe
    linarith

/-- `lem:local-test` in the safe model: by the singleton consequence of capacity,
`μ(u)² ≤ C h(u)`, for an atom target `h(u) ≥ α²/C` holds exactly when `u` is a prefix of the atom,
as soon as `R (1-α) ν(u) < α²/C`. -/
theorem safe_test {R C α : ℝ} {ν : Str n → ℝ} (hν : IsDist ν) {x : Str n} {h : Guide}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 < C) (hl : SafeLegal R C (atomTarget ν α x) h)
    {v : List Bool} (hv : v.length ≤ n) (hgap : R * ((1 - α) * mass ν v) < α ^ 2 / C) :
    α ^ 2 / C ≤ h v ↔ IsPre v x := by
  have hb := mass_nonneg hν.1 v
  refine (local_test (P := IsPre v x) hα hC (hl.2.1 v hv)
    (hl.2.2.sq_le hl.1.nonneg hv) hgap ?_ ?_).symm
  · intro hp
    rw [mass_atomTarget, ite_eq_left hp]
    nlinarith
  · intro hp
    rw [mass_atomTarget, ite_eq_right hp]
    ring

/-- `cor:spike-pointwise`, pointwise analogue of `lem:local-test`: for a pointwise factor-`R` guide
of an atom target, `h(u) ≥ α/R` exactly when `u` is a prefix of the atom, as soon as
`R (1-α) ν(u) < α/R`. -/
theorem pw_test {R α : ℝ} {ν : Str n → ℝ} (hν : IsDist ν) {x : Str n} {h : Guide}
    (hR : 0 < R) (hα1 : α ≤ 1) (hl : PwLegal R (atomTarget ν α x) h)
    {v : List Bool} (hv : v.length ≤ n) (hgap : R * ((1 - α) * mass ν v) < α / R) :
    α / R ≤ h v ↔ IsPre v x := by
  have hb := mass_nonneg hν.1 v
  have h1 := (hl.2 v hv).1
  have h2 := (hl.2 v hv).2
  rw [mass_atomTarget] at h1 h2
  constructor
  · intro hle
    by_contra hp
    rw [ite_eq_right hp] at h2
    linarith
  · intro hp
    rw [ite_eq_left hp] at h1
    refine le_trans ?_ h1
    gcongr
    nlinarith

/-- Exact leaves detect the atom: `h(x') = (1-α)ν(x') + α` exactly when `x' = x`. -/
theorem leaf_test {α : ℝ} {ν : Str n → ℝ} {x : Str n} {h : Guide} (hα : 0 < α)
    (hl : IsOracle (atomTarget ν α x) h) (y : Str n) :
    (1 - α) * mass ν (List.ofFn y) + α ≤ h (List.ofFn y) ↔ y = x := by
  rw [hl.leaf, mass_ofFn, atomTarget_apply]
  constructor
  · intro hle
    by_contra hy
    rw [ite_eq_right hy] at hle
    linarith
  · intro hy
    rw [ite_eq_left hy]
    linarith

end LearningGuided.Sec3
