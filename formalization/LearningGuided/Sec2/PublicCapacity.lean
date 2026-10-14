import LearningGuided.Sec2.Tools

/-!
# Public answers on selected prefixes (Lemma `lem:public-capacity`)

For a full-support background `ν`, a target `μ_x = (1-α) ν + α δ_x` with `0 < α ≤ 1/4`, and any
set `𝓑` of proper prefixes, the guide that answers `ν(u)` on `𝓑` and `μ_x(u)` elsewhere is safe
with factor `4/3`, exact at the leaves, and has stopped capacity equal to
`max {1, max_{u ∈ 𝓑, u ⪯ x} (1 + α - 2α² - aαν(u) + α²/ν(u))}` (equation `eq:public-capacity`).
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec2

variable {n : ℕ}

open Classical in
/-- The guide of Lemma `lem:public-capacity`: the public background mass `ν(u)` on `𝓑` and the
exact target mass `μ_x(u)` elsewhere. -/
noncomputable def pubGuide (ν : Str n → ℝ) (α : ℝ) (B : Set (List Bool)) (x : Str n) : Guide :=
  fun u => if u ∈ B then mass ν u else mass (mixD ν α x) u

/-- The cut value `1 + α - 2α² - aαν(u) + α²/ν(u)` of a public ancestor with background mass
`v = ν(u)`, where `a = 1 - α`. -/
noncomputable def ancVal (α v : ℝ) : ℝ := 1 + α - 2 * α ^ 2 - (1 - α) * α * v + α ^ 2 / v

open Classical in
/-- The public ancestors of `x`: members of `𝓑` that are proper prefixes of `x`. -/
noncomputable def pubAnc (B : Set (List Bool)) (x : Str n) : Finset (List Bool) :=
  ((Finset.range n).image (pre x)).filter (· ∈ B)

/-- The right side of `eq:public-capacity`: the maximum of `1` and the ancestor values (an empty
inner maximum leaves the value `1`). -/
noncomputable def pubCap (ν : Str n → ℝ) (α : ℝ) (B : Set (List Bool)) (x : Str n) : ℝ :=
  (insert 1 ((pubAnc B x).image fun u => ancVal α (mass ν u))).max' (Finset.insert_nonempty _ _)

theorem mem_pubAnc {B : Set (List Bool)} (hB : ∀ u ∈ B, u.length < n) {x : Str n}
    {u : List Bool} : u ∈ pubAnc B x ↔ u ∈ B ∧ IsPre u x := by
  classical
  unfold pubAnc
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨t, -, rfl⟩, hB'⟩
    exact ⟨hB', isPre_pre x t⟩
  · rintro ⟨hu, hux⟩
    exact ⟨⟨u.length, hB u hu, (isPre_iff_pre.mp hux).symm⟩, hu⟩

theorem exists_of_mem_pubAnc {B : Set (List Bool)} {x : Str n} {u : List Bool}
    (hu : u ∈ pubAnc B x) : ∃ t < n, u = pre x t ∧ pre x t ∈ B := by
  classical
  unfold pubAnc at hu
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hu
  obtain ⟨⟨t, ht, rfl⟩, hB'⟩ := hu
  exact ⟨t, ht, rfl, hB'⟩

theorem one_le_pubCap (ν : Str n → ℝ) (α : ℝ) (B : Set (List Bool)) (x : Str n) :
    1 ≤ pubCap ν α B x :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem ancVal_le_pubCap (ν : Str n → ℝ) (α : ℝ) {B : Set (List Bool)} (x : Str n)
    {u : List Bool} (hu : u ∈ pubAnc B x) : ancVal α (mass ν u) ≤ pubCap ν α B x :=
  Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun u => ancVal α (mass ν u)) hu))

/-- `lem:public-capacity`, equation `eq:public-capacity` (empty inner maximum): without public
ancestors the capacity value is `1`. -/
theorem pubCap_of_empty (ν : Str n → ℝ) (α : ℝ) (B : Set (List Bool)) (x : Str n)
    (h : pubAnc B x = ∅) : pubCap ν α B x = 1 := by
  unfold pubCap
  simp [h]

/-- `lem:public-capacity`, equation `eq:public-capacity`: with public ancestors, the value is `max
{1, max_u (ancestor value)}`. -/
theorem pubCap_of_nonempty (ν : Str n → ℝ) (α : ℝ) (B : Set (List Bool)) (x : Str n)
    (h : (pubAnc B x).Nonempty) :
    pubCap ν α B x = max 1 ((pubAnc B x).sup' h fun u => ancVal α (mass ν u)) := by
  classical
  unfold pubCap
  rw [Finset.max'_insert _ _ (h.image _), Finset.max'_eq_sup', Finset.sup'_image]
  rfl

/-- A full-support distribution has positive mass at every word of length at most `n`. -/
theorem mass_pos_of_full {ν : Str n → ℝ} (hν : IsDist ν) (hfull : ∀ y, 0 < ν y)
    {u : List Bool} (hu : u.length ≤ n) : 0 < mass ν u := by
  set z : Str n := fun i => if h : i.1 < u.length then u[i.1] else false with hz
  have hpre : IsPre u z := by
    rw [isPre_iff_getElem]
    exact ⟨hu, fun i hi => by simp [hz, hi]⟩
  exact lt_of_lt_of_le (hfull z) (le_mass_of_isPre hν.1 hpre)

theorem pre_self (x : Str n) : pre x n = List.ofFn x := by
  unfold pre
  exact List.take_of_length_le (by simp)

/-- The ancestor value as a cut value: `1 - μ(u) + μ(u)²/ν(u)` with `μ(u) = aν(u) + α`. -/
theorem ancVal_eq {α v : ℝ} (hv : v ≠ 0) :
    1 - ((1 - α) * v + α) + ((1 - α) * v + α) ^ 2 / v = ancVal α v := by
  unfold ancVal
  field_simp
  ring

theorem sq_div_le_of_le {m v : ℝ} (hm : 0 ≤ m) (hmv : m ≤ v) (hv : 0 < v) : m ^ 2 / v ≤ m := by
  rw [div_le_iff₀ hv]
  nlinarith

/-- `lem:public-capacity`: for a full-support background `ν`, `0 < α ≤ 1/4`, and any set `𝓑` of
proper prefixes, the guide `h_x` answering `ν(u)` on `𝓑` and `μ_x(u)` elsewhere satisfies the
access conditions (exact leaves, root one), is safe with `h_x ≤ (4/3) μ_x`, and has stopped
reciprocal capacity exactly the value of `eq:public-capacity`. -/
theorem lem_public_capacity {ν : Str n → ℝ} (hν : IsDist ν) (hfull : ∀ y, 0 < ν y) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 1 / 4) {B : Set (List Bool)} (hB : ∀ u ∈ B, u.length < n)
    (x : Str n) :
    IsOracle (mixD ν α x) (pubGuide ν α B x) ∧
      (∀ u : List Bool, u.length ≤ n → pubGuide ν α B x u ≤ 4 / 3 * mass (mixD ν α x) u) ∧
      CapEq (mixD ν α x) (pubGuide ν α B x) (pubCap ν α B x) := by
  classical
  set μ := mixD ν α x with hμdef
  set h := pubGuide ν α B x with hhdef
  have hμ : IsDist μ := isDist_mixD hν hα0.le (by linarith) x
  have hmass : ∀ u, mass μ u = (1 - α) * mass ν u + α * (if IsPre u x then 1 else 0) :=
    fun u => mass_mixD ν α x u
  have hnotB : ∀ u : List Bool, n ≤ u.length → u ∉ B := fun u hu hB' => by
    have := hB u hB'; omega
  have hleaf : ∀ y : Str n, h (List.ofFn y) = μ y := by
    intro y
    simp only [hhdef, pubGuide, ite_eq_right (hnotB _ (by simp : n ≤ (List.ofFn y).length))]
    exact mass_ofFn μ y
  have horacle : IsOracle μ h := by
    refine ⟨fun u => ?_, ?_, hleaf, fun u hu => ?_⟩
    · simp only [hhdef, pubGuide]
      split_ifs
      · exact mass_nonneg hν.1 u
      · exact mass_nonneg hμ.1 u
    · simp only [hhdef, pubGuide]
      split_ifs
      · rw [mass_nil, hν.2]
      · rw [mass_nil, hμ.2]
    · simp only [hhdef, pubGuide, ite_eq_right (hnotB u hu.le)]
      exact mass_eq_zero_of_long μ hu
  -- values of the guide
  have hB_val : ∀ u ∈ B, h u = mass ν u := fun u hu => by simp [hhdef, pubGuide, hu]
  have hnB_val : ∀ u ∉ B, h u = mass μ u := fun u hu => by simp [hhdef, pubGuide, hu, hμdef]
  refine ⟨horacle, fun u hu => ?_, ?_⟩
  · by_cases huB : u ∈ B
    · rw [hB_val u huB, hmass u]
      have h0 := mass_nonneg hν.1 u
      have h1 : (0 : ℝ) ≤ α * (if IsPre u x then 1 else 0) := by
        split_ifs <;> linarith
      nlinarith
    · rw [hnB_val u huB]
      have := mass_nonneg hμ.1 u
      linarith
  -- capacity
  have hsupp : SameSupport μ h := by
    intro u hu hz
    by_cases huB : u ∈ B
    · rw [hB_val u huB]
      exact ne_of_gt (mass_pos_of_full hν hfull hu)
    · rwa [hnB_val u huB]
  have hoff : ∀ u : List Bool, u.length ≤ n → ¬ IsPre u x → mass μ u ^ 2 / h u ≤ mass μ u := by
    intro u hu hux
    by_cases huB : u ∈ B
    · rw [hB_val u huB]
      have hpos := mass_pos_of_full hν hfull hu
      have hm : mass μ u = (1 - α) * mass ν u := by rw [hmass u, ite_eq_right hux]; ring
      refine sq_div_le_of_le (mass_nonneg hμ.1 u) ?_ hpos
      rw [hm]; nlinarith
    · rw [hnB_val u huB]
      exact sq_div_self_le (mass_nonneg hμ.1 u)
  have hpath_val : ∀ t ≤ n, pre x t ∈ B →
      1 - mass μ (pre x t) + mass μ (pre x t) ^ 2 / h (pre x t) = ancVal α (mass ν (pre x t)) := by
    intro t ht htB
    rw [hB_val _ htB, hmass, ite_eq_left (isPre_pre x t), mul_one]
    have hlen : (pre x t).length ≤ n := (isPre_pre x t).length_le
    exact ancVal_eq (ne_of_gt (mass_pos_of_full hν hfull hlen))
  have hpath : ∀ t ≤ n,
      1 - mass μ (pre x t) + mass μ (pre x t) ^ 2 / h (pre x t) ≤ pubCap ν α B x := by
    intro t ht
    by_cases htB : pre x t ∈ B
    · rw [hpath_val t ht htB]
      exact ancVal_le_pubCap ν α x ((mem_pubAnc hB).mpr ⟨htB, isPre_pre x t⟩)
    · rw [hnB_val _ htB, sq_div_self_eq]
      simpa using one_le_pubCap ν α B x
  refine ⟨⟨hsupp, cutSum_le_of_path hμ x (one_le_pubCap ν α B x) hoff hpath⟩, ?_⟩
  -- attainment
  have hmem := Finset.max'_mem (insert 1 ((pubAnc B x).image fun u => ancVal α (mass ν u)))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hmem with h1 | h2
  · obtain ⟨A, hA, hval⟩ := exists_path_cut hμ hleaf x (le_refl n)
    refine ⟨A, hA, ?_⟩
    rw [hval, pre_self, hleaf, mass_ofFn, sq_div_self_eq]
    unfold pubCap
    rw [h1]
    ring
  · obtain ⟨u, hu, hval⟩ := Finset.mem_image.mp h2
    obtain ⟨t, ht, rfl, htB⟩ := exists_of_mem_pubAnc hu
    obtain ⟨A, hA, hcut⟩ := exists_path_cut hμ hleaf x ht.le
    refine ⟨A, hA, ?_⟩
    rw [hcut, hpath_val t ht.le htB]
    unfold pubCap
    rw [← hval]

end Sec2
end LearningGuided
