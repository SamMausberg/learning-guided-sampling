import LearningGuided.Masses

/-!
# Cuts and the stopped reciprocal capacity

Shared facts about prefix-free sets (`IsCut`) and the capacity `CC(μ,h)`:

* at most one element of a cut is a prefix of a given string, so the masses of a cut sum to at
  most one;
* a pointwise factor-`R` guide has capacity at most `R`, hence is legal in the safe model with
  `C = R` (the "pointwise submodel");
* an exact guide has capacity one;
* the path reduction used in Lemmas `lem:public-capacity`, `lem:capacity` and in
  `eq:local-hard-capacity`: if every node off the path to a string `x` has `μ(u)²/h(u) ≤ μ(u)`,
  then the capacity is the largest value `1 - μ(u_t) + μ(u_t)²/h(u_t)` along the path, and that
  value is attained by `{u_t}` together with all leaves outside `u_t`.
-/

open scoped BigOperators

namespace LearningGuided

variable {n : ℕ}

/-- At most one element of a prefix-free set is a prefix of a given string. -/
theorem IsCut.card_filter_isPre_le_one {A : Finset (List Bool)} (hA : IsCut n A) (x : Str n) :
    (A.filter fun u => IsPre u x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  simp only [Finset.mem_filter] at hu hv
  rcases hu.2.comparable hv.2 with h | h
  · exact hA.2 u hu.1 v hv.1 h
  · exact (hA.2 v hv.1 u hu.1 h).symm

/-- The masses of a set of words, counted with multiplicity. -/
theorem cut_mass_sum_eq (μ : Str n → ℝ) (A : Finset (List Bool)) :
    ∑ u ∈ A, mass μ u = ∑ x, μ x * ((A.filter fun u => IsPre u x).card : ℝ) := by
  unfold mass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The masses of a cut sum to at most the total mass. -/
theorem IsCut.mass_sum_le {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) {A : Finset (List Bool)}
    (hA : IsCut n A) : ∑ u ∈ A, mass μ u ≤ ∑ x, μ x := by
  rw [cut_mass_sum_eq]
  refine Finset.sum_le_sum fun x _ => ?_
  have := hA.card_filter_isPre_le_one x
  calc μ x * ((A.filter fun u => IsPre u x).card : ℝ) ≤ μ x * 1 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast this) (hμ x)
    _ = μ x := mul_one _

/-- In a cut containing `u`, the other masses sum to at most `1 - μ(u)`. -/
theorem IsCut.mass_sum_erase_le {μ : Str n → ℝ} (hμ : IsDist μ) {A : Finset (List Bool)}
    (hA : IsCut n A) {u : List Bool} (hu : u ∈ A) :
    ∑ v ∈ A.erase u, mass μ v ≤ 1 - mass μ u := by
  have := hA.mass_sum_le hμ.1
  rw [← Finset.add_sum_erase A _ hu, hμ.2] at this
  linarith

/-- Subsets of cuts are cuts. -/
theorem IsCut.subset {A B : Finset (List Bool)} (hA : IsCut n A) (hBA : B ⊆ A) : IsCut n B :=
  ⟨fun u hu => hA.1 u (hBA hu), fun u hu v hv h => hA.2 u (hBA hu) v (hBA hv) h⟩

/-- Each level `{0,1}^t`, `t ≤ n`, is a cut. -/
theorem isCut_words {t : ℕ} (ht : t ≤ n) : IsCut n (words t) := by
  refine ⟨fun u hu => by rw [mem_words.mp hu]; exact ht, fun u hu v hv h => ?_⟩
  exact h.eq_of_length (by rw [mem_words.mp hu, mem_words.mp hv])

/-- A single word of length at most `n` is a cut. -/
theorem isCut_singleton {u : List Bool} (hu : u.length ≤ n) : IsCut n {u} :=
  ⟨fun v hv => by rw [Finset.mem_singleton.mp hv]; exact hu,
    fun v hv w hw _ => by rw [Finset.mem_singleton.mp hv, Finset.mem_singleton.mp hw]⟩

/-- The singleton consequence of capacity: `μ(u)² ≤ C h(u)` (used in Lemma `lem:local-test`). -/
theorem CapLE.sq_le {μ : Str n → ℝ} {h : Guide} {C : ℝ} (hc : CapLE μ h C)
    (hh : ∀ u, 0 ≤ h u) {u : List Bool} (hu : u.length ≤ n) : mass μ u ^ 2 ≤ C * h u := by
  have h1 := hc.2 {u} (isCut_singleton hu)
  simp only [cutSum, Finset.sum_singleton] at h1
  by_cases hz : mass μ u = 0
  · rw [hz]
    have : 0 ≤ C := le_trans (by rw [hz]; simp) h1
    simpa using mul_nonneg this (hh u)
  · have hpos : 0 < h u := lt_of_le_of_ne (hh u) (Ne.symm (hc.1 u hu hz))
    rwa [div_le_iff₀ hpos] at h1

theorem sq_div_le_mul_of_le {m h R : ℝ} (hm : 0 ≤ m) (hR : 0 < R) (hh : m / R ≤ h) :
    m ^ 2 / h ≤ R * m := by
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hhpos : 0 < h := lt_of_lt_of_le (div_pos hpos hR) hh
    rw [div_le_iff₀ hhpos]
    have := mul_le_mul_of_nonneg_left hh (le_of_lt (mul_pos hR hpos))
    calc m ^ 2 = R * m * (m / R) := by field_simp
      _ ≤ R * m * h := this

/-- A pointwise factor-`R` guide has stopped capacity at most `R`. -/
theorem PwLegal.capLE {R : ℝ} (hR : 0 < R) {μ : Str n → ℝ} {h : Guide} (hμ : IsDist μ)
    (hl : PwLegal R μ h) : CapLE μ h R := by
  refine ⟨fun u hu hz => ?_, fun A hA => ?_⟩
  · have hpos : 0 < mass μ u := lt_of_le_of_ne (mass_nonneg hμ.1 u) (Ne.symm hz)
    exact ne_of_gt (lt_of_lt_of_le (div_pos hpos hR) (hl.2 u hu).1)
  · unfold cutSum
    calc ∑ u ∈ A, mass μ u ^ 2 / h u ≤ ∑ u ∈ A, R * mass μ u :=
          Finset.sum_le_sum fun u hu =>
            sq_div_le_mul_of_le (mass_nonneg hμ.1 u) hR (hl.2 u (hA.1 u hu)).1
      _ = R * ∑ u ∈ A, mass μ u := by rw [Finset.mul_sum]
      _ ≤ R * 1 := by
          gcongr
          exact (hA.mass_sum_le hμ.1).trans hμ.2.le
      _ = R := mul_one R

/-- The pointwise submodel: a pointwise factor-`R` guide is legal in the safe model with
`C = R`. -/
theorem PwLegal.safeLegal {R : ℝ} (hR : 0 < R) {μ : Str n → ℝ} {h : Guide} (hμ : IsDist μ)
    (hl : PwLegal R μ h) : SafeLegal R R μ h :=
  ⟨hl.1, fun u hu => (hl.2 u hu).2, hl.capLE hR hμ⟩

/-- `m²/m ≤ m` for `m ≥ 0`, with `0/0 = 0`. -/
theorem sq_div_self_le {m : ℝ} (hm : 0 ≤ m) : m ^ 2 / m ≤ m := by
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [sq, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

theorem sq_div_self_eq (m : ℝ) : m ^ 2 / m = m := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0]; simp
  · rw [sq, mul_div_assoc, div_self h0, mul_one]

/-- A guide equal to the exact prefix masses has capacity at most one. -/
theorem capLE_of_exact {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hex : ∀ u : List Bool, u.length ≤ n → h u = mass μ u) : CapLE μ h 1 := by
  refine ⟨fun u hu hz => by rwa [hex u hu], fun A hA => ?_⟩
  unfold cutSum
  calc ∑ u ∈ A, mass μ u ^ 2 / h u = ∑ u ∈ A, mass μ u :=
        Finset.sum_congr rfl fun u hu => by rw [hex u (hA.1 u hu), sq_div_self_eq]
    _ ≤ ∑ x, μ x := hA.mass_sum_le hμ.1
    _ = 1 := hμ.2

/-- The path reduction (upper bound). If every word off the path to `x` contributes at most its
mass, the capacity is at most the largest path value `1 - μ(u_t) + μ(u_t)²/h(u_t)`. -/
theorem cutSum_le_of_path {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide} (x : Str n) {F : ℝ}
    (hF : 1 ≤ F)
    (hoff : ∀ u : List Bool, u.length ≤ n → ¬ IsPre u x → mass μ u ^ 2 / h u ≤ mass μ u)
    (hpath : ∀ t ≤ n, 1 - mass μ (pre x t) + mass μ (pre x t) ^ 2 / h (pre x t) ≤ F) :
    ∀ A, IsCut n A → cutSum μ h A ≤ F := by
  intro A hA
  unfold cutSum
  by_cases hex : ∃ u ∈ A, IsPre u x
  · obtain ⟨u, huA, hux⟩ := hex
    rw [← Finset.add_sum_erase A _ huA]
    have hrest : ∀ v ∈ A.erase u, ¬ IsPre v x := by
      intro v hv hvx
      have h1 := hA.card_filter_isPre_le_one x
      rw [Finset.card_le_one] at h1
      exact (Finset.ne_of_mem_erase hv)
        (h1 v (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hv, hvx⟩) u
          (Finset.mem_filter.mpr ⟨huA, hux⟩))
    have h2 : ∑ v ∈ A.erase u, mass μ v ^ 2 / h v ≤ ∑ v ∈ A.erase u, mass μ v :=
      Finset.sum_le_sum fun v hv =>
        hoff v (hA.1 v (Finset.mem_of_mem_erase hv)) (hrest v hv)
    have h3 := hA.mass_sum_erase_le hμ huA
    have h4 := hpath u.length (hA.1 u huA)
    rw [← isPre_iff_pre.mp hux] at h4
    linarith
  · simp only [not_exists, not_and] at hex
    calc ∑ u ∈ A, mass μ u ^ 2 / h u ≤ ∑ u ∈ A, mass μ u :=
          Finset.sum_le_sum fun u hu => hoff u (hA.1 u hu) (hex u hu)
      _ ≤ ∑ x, μ x := hA.mass_sum_le hμ.1
      _ = 1 := hμ.2
      _ ≤ F := hF

/-- The path reduction (attainment): the cut consisting of `u_t = x_{1:t}` and all leaves
outside it has value `1 - μ(u_t) + μ(u_t)²/h(u_t)` when the leaves are exact. -/
theorem exists_path_cut {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hleaf : ∀ y : Str n, h (List.ofFn y) = μ y) (x : Str n) {t : ℕ} (ht : t ≤ n) :
    ∃ A, IsCut n A ∧
      cutSum μ h A = 1 - mass μ (pre x t) + mass μ (pre x t) ^ 2 / h (pre x t) := by
  classical
  set u := pre x t with hu
  set L := (Finset.univ.filter fun y : Str n => ¬ IsPre u y).image (fun y => List.ofFn y)
    with hL
  have hulen : u.length = t := length_pre x ht
  have huL : u ∉ L := by
    intro hmem
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hmem
    exact (Finset.mem_filter.mp hy).2 (by rw [← hyu]; exact List.prefix_refl _)
  refine ⟨insert u L, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · omega
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hv
      simp
  · intro v hv w hw hvw
    rcases Finset.mem_insert.mp hv with rfl | hv <;> rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      exact absurd hvw (Finset.mem_filter.mp hy).2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      have hl : (List.ofFn y).length ≤ u.length := hvw.length_le
      simp only [List.length_ofFn] at hl
      have heq : List.ofFn y = u := hvw.eq_of_length (by simp; omega)
      exact absurd (show u <+: List.ofFn y by rw [heq]) (Finset.mem_filter.mp hy).2
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hw
      exact hvw.eq_of_length (by simp)
  · unfold cutSum
    rw [Finset.sum_insert huL, Finset.sum_image (fun y _ z _ hyz => List.ofFn_injective hyz)]
    have hleaves : ∑ y ∈ Finset.univ.filter (fun y : Str n => ¬ IsPre u y),
        mass μ (List.ofFn y) ^ 2 / h (List.ofFn y) = 1 - mass μ u := by
      rw [Finset.sum_congr rfl fun y _ => by rw [mass_ofFn, hleaf, sq_div_self_eq]]
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : Str n => IsPre u y)
        μ
      rw [hμ.2] at hsplit
      have hm : mass μ u = ∑ y ∈ Finset.univ.filter (fun y : Str n => IsPre u y), μ y := by
        unfold mass; rw [Finset.sum_filter]
      linarith
    rw [hleaves]
    ring

end LearningGuided
