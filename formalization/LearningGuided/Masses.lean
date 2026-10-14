import LearningGuided.Alg

/-!
# Prefix masses: additivity, mixtures, uniform and point masses

Shared facts about `mass μ u = μ(u)` used throughout the formalization.
-/

open scoped BigOperators

namespace LearningGuided

variable {n : ℕ}

/-- The length-`t` prefix `x_{1:t}` of a string. -/
def pre (x : Str n) (t : ℕ) : List Bool := (List.ofFn x).take t

/-- Words of length exactly `t`. -/
noncomputable def words (t : ℕ) : Finset (List Bool) :=
  Finset.univ.image (fun y : Str t => List.ofFn y)

theorem mem_words {t : ℕ} {u : List Bool} : u ∈ words t ↔ u.length = t := by
  constructor
  · intro hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
    simp
  · intro hu
    subst hu
    exact Finset.mem_image.mpr ⟨fun i => u[i], Finset.mem_univ _, List.ofFn_getElem⟩

theorem IsPre.length_le {u : List Bool} {x : Str n} (h : IsPre u x) : u.length ≤ n := by
  simpa using List.IsPrefix.length_le h

theorem isPre_iff_pre {u : List Bool} {x : Str n} : IsPre u x ↔ u = pre x u.length :=
  List.prefix_iff_eq_take

theorem isPre_pre (x : Str n) (t : ℕ) : IsPre (pre x t) x := List.take_prefix _ _

theorem length_pre (x : Str n) {t : ℕ} (ht : t ≤ n) : (pre x t).length = t := by
  simp [pre, ht]

theorem isPre_nil (x : Str n) : IsPre [] x := List.nil_prefix

theorem isPre_ofFn_iff {x y : Str n} : IsPre (List.ofFn y) x ↔ y = x := by
  constructor
  · intro h
    have hl : (List.ofFn y).length = (List.ofFn x).length := by simp
    exact List.ofFn_injective (h.eq_of_length hl)
  · rintro rfl
    exact List.prefix_refl _

/-- Two prefixes of the same string are comparable. -/
theorem IsPre.comparable {u v : List Bool} {x : Str n} (hu : IsPre u x) (hv : IsPre v x) :
    u <+: v ∨ v <+: u := by
  rcases le_total u.length v.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hu hv h)
  · exact Or.inr (List.prefix_of_prefix_length_le hv hu h)

theorem isPre_append_singleton {u : List Bool} {b : Bool} {x : Str n} :
    IsPre (u ++ [b]) x ↔ IsPre u x ∧ (List.ofFn x)[u.length]? = some b := by
  unfold IsPre
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

/-- Additivity of prefix masses over the two children. -/
theorem mass_children (μ : Str n → ℝ) {u : List Bool} (hu : u.length < n) :
    mass μ u = mass μ (u ++ [false]) + mass μ (u ++ [true]) := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : (List.ofFn x)[u.length]? = some (x ⟨u.length, hu⟩) := by simp [hu]
  by_cases h : IsPre u x
  · cases hb : x ⟨u.length, hu⟩ <;> simp [isPre_append_singleton, h, hx, hb]
  · simp [isPre_append_singleton, h]

theorem mass_eq_zero_of_long (μ : Str n → ℝ) {u : List Bool} (hu : n < u.length) :
    mass μ u = 0 := by
  unfold mass
  refine Finset.sum_eq_zero fun x _ => ?_
  have : ¬ IsPre u x := fun h => by have := h.length_le; omega
  simp [this]

theorem mass_linear (μ ν : Str n → ℝ) (a b : ℝ) (u : List Bool) :
    mass (fun x => a * μ x + b * ν x) u = a * mass μ u + b * mass ν u := by
  unfold mass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem mass_dirac (x : Str n) (u : List Bool) :
    mass (dirac x) u = if IsPre u x then 1 else 0 := by
  unfold mass dirac
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · simp

/-- The sum of the masses of the words of length `t ≤ n` is the total mass. -/
theorem sum_mass_words (μ : Str n → ℝ) {t : ℕ} (ht : t ≤ n) :
    ∑ u ∈ words t, mass μ u = ∑ x, μ x := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have : (words t).filter (fun u => IsPre u x) = {pre x t} := by
    ext u
    simp only [Finset.mem_filter, mem_words, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, hp⟩
      rw [isPre_iff_pre, hl] at hp
      exact hp
    · rintro rfl
      exact ⟨length_pre x ht, isPre_pre x t⟩
  rw [this]
  simp

/-- The mass of the uniform distribution at a word of length at most `n`. -/
theorem mass_unif {u : List Bool} (hu : u.length ≤ n) :
    mass (unif n) u = ((2 : ℝ) ^ u.length)⁻¹ := by
  obtain ⟨k, hk⟩ : ∃ k, n - u.length = k := ⟨_, rfl⟩
  induction k generalizing u with
  | zero =>
      have hl : u.length = n := by omega
      set y : Str n := fun i => u[i.1]'(by omega) with hy
      have hu' : u = List.ofFn y := by
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        simp [hy]
      rw [hu', mass_ofFn]
      simp [unif]
  | succ k ih =>
      have hlt : u.length < n := by omega
      rw [mass_children _ hlt, ih (by simp; omega) (by simp; omega),
        ih (by simp; omega) (by simp; omega)]
      simp only [List.length_append, List.length_singleton, pow_succ]
      field_simp
      norm_num

theorem isDist_unif (n : ℕ) : IsDist (unif n) := by
  refine ⟨fun _ => by unfold unif; positivity, ?_⟩
  simp [unif, Finset.card_univ, Fintype.card_bool]

theorem isDist_dirac (x : Str n) : IsDist (dirac x) := by
  refine ⟨fun y => by unfold dirac; split_ifs <;> norm_num, ?_⟩
  simp [dirac]

/-- A convex combination of two distributions is a distribution. -/
theorem isDist_mix {μ ν : Str n → ℝ} (hμ : IsDist μ) (hν : IsDist ν) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : IsDist (fun x => (1 - a) * μ x + a * ν x) := by
  refine ⟨fun x => ?_, ?_⟩
  · have := hμ.1 x; have := hν.1 x
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμ.2, hν.2]
    ring

/-- Total variation between two mixtures with the same components. -/
theorem tv_mix (μ ν : Str n → ℝ) (a b : ℝ) :
    tv (fun x => (1 - a) * μ x + a * ν x) (fun x => (1 - b) * μ x + b * ν x) =
      |a - b| * tv μ ν := by
  unfold tv
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← abs_mul, ← abs_neg]
  congr 1
  ring

theorem tv_le_one {μ ν : Str n → ℝ} (hμ : IsDist μ) (hν : IsDist ν) : tv μ ν ≤ 1 := by
  unfold tv
  have : ∑ x, |μ x - ν x| ≤ ∑ x, (μ x + ν x) :=
    Finset.sum_le_sum fun x _ => by
      have := hμ.1 x; have := hν.1 x
      rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, hμ.2, hν.2] at this
  linarith

theorem tv_self (μ : Str n → ℝ) : tv μ μ = 0 := by simp [tv]

/-- `TV(U_n, δ_x) = 1 - 2^{-n}`. -/
theorem tv_unif_dirac (x : Str n) : tv (unif n) (dirac x) = 1 - ((2 : ℝ) ^ n)⁻¹ := by
  classical
  unfold tv
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hpos : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h1 : |unif n x - dirac x x| = 1 - ((2 : ℝ) ^ n)⁻¹ := by
    simp only [unif, dirac, ↓reduceIte]
    rw [abs_of_nonpos (by linarith)]
    ring
  have h2 : ∑ y ∈ Finset.univ.erase x, |unif n y - dirac x y| =
      ((2 : ℝ) ^ n - 1) * ((2 : ℝ) ^ n)⁻¹ := by
    rw [Finset.sum_congr rfl fun y hy => by
      rw [show dirac x y = 0 by simp [dirac, Finset.ne_of_mem_erase hy]]]
    simp only [unif, sub_zero, abs_inv, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ x), Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    rw [abs_of_pos (by positivity)]
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    ring
  rw [h1, h2]
  field_simp
  ring

end LearningGuided
