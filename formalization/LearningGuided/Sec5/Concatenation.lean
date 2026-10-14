import LearningGuided.Sec5.Product

/-!
# Capacity under concatenation (Lemma `lem:capacity-concatenation`)

For an outer pair `(ν, g)` on `d` bits and an inner pair `(σ, h)` on `n` bits, the product guide
`H` of `eq:composition-guide` satisfies

`CC(ν ⊗ σ, H) = C_in + max_{A ⊆ {0,1}^{<d} prefix-free} ∑_{u ∈ A} (ν(u)²/g(u) - C_in ν(u))`

(equation `eq:capacity-concatenation`; the empty set is allowed), which is at most
`C_out + C_in - 1`, and at most `max {R, C_in}` when `g ≥ ν/R`.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec5

open Sec2

variable {d n : ℕ}

/-! ### Outer prefix-free sets -/

/-- Words of length less than `d`. -/
noncomputable def wordsLT (d : ℕ) : Finset (List Bool) := (Finset.range d).biUnion words

theorem mem_wordsLT {u : List Bool} : u ∈ wordsLT d ↔ u.length < d := by
  simp [wordsLT, mem_words]

/-- Prefix-freeness. -/
def PF (A : Finset (List Bool)) : Prop := ∀ u ∈ A, ∀ v ∈ A, u <+: v → u = v

open Classical in
/-- The prefix-free subsets of `{0,1}^{<d}` (the empty set included). -/
noncomputable def outerCuts (d : ℕ) : Finset (Finset (List Bool)) :=
  (wordsLT d).powerset.filter PF

theorem mem_outerCuts {A : Finset (List Bool)} :
    A ∈ outerCuts d ↔ (∀ u ∈ A, u.length < d) ∧ PF A := by
  classical
  unfold outerCuts
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu => mem_wordsLT.mp (h1 hu), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu => mem_wordsLT.mpr (h1 u hu), h2⟩

theorem empty_mem_outerCuts : (∅ : Finset (List Bool)) ∈ outerCuts d :=
  mem_outerCuts.mpr ⟨by simp, by simp [PF]⟩

/-- The outer value `max_{A} ∑_{u ∈ A} (ν(u)²/g(u) - C ν(u))` over prefix-free
`A ⊆ {0,1}^{<d}`. -/
noncomputable def outerVal (ν : Str d → ℝ) (g : Guide) (C : ℝ) : ℝ :=
  (outerCuts d).sup' ⟨∅, empty_mem_outerCuts⟩
    fun A => ∑ u ∈ A, (mass ν u ^ 2 / g u - C * mass ν u)

theorem outerCuts_isCut {A : Finset (List Bool)} (hA : A ∈ outerCuts d) : IsCut d A :=
  ⟨fun u hu => ((mem_outerCuts.mp hA).1 u hu).le, (mem_outerCuts.mp hA).2⟩

/-! ### Covered outer leaves -/

/-- The mass of a cut is the mass of the leaves it covers. -/
theorem mass_sum_eq_covered {μ : Str d → ℝ} {A : Finset (List Bool)} (hA : IsCut d A) :
    ∑ u ∈ A, mass μ u = ∑ x, (if ∃ u ∈ A, IsPre u x then μ x else 0) := by
  classical
  rw [cut_mass_sum_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 := hA.card_filter_isPre_le_one x
  split_ifs with hex
  · obtain ⟨u, hu, hux⟩ := hex
    have : (A.filter fun u => IsPre u x).card = 1 := by
      have : 0 < (A.filter fun u => IsPre u x).card :=
        Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hux⟩⟩
      omega
    rw [this]; simp
  · push Not at hex
    have : (A.filter fun u => IsPre u x) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact hex u
    rw [this]; simp

theorem sq_mul_div_mul (a b c : ℝ) : (a * b) ^ 2 / (a * c) = a * (b ^ 2 / c) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  field_simp

/-! ### The upper bound -/

theorem cut_lengths_split {A : Finset (List Bool)} (hA : IsCut (d + n) A) :
    IsCut d (A.filter fun u => u.length < d) :=
  ⟨fun _ hu => (Finset.mem_filter.mp hu).2.le, (hA.subset (Finset.filter_subset _ _)).2⟩

/-- `lem:capacity-concatenation` (cut reduction behind `eq:capacity-concatenation`): in every outer
leaf subtree not covered by the outer part `A_out` of a cut, the inner part contributes at most `C
ν(x)`. -/
theorem cutSum_prod_le {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) (hg : ∀ x : Str d, g (List.ofFn x) = ν x) (hroot : h [] = 1) {C : ℝ}
    (hC : ∀ B, IsCut n B → cutSum σ h B ≤ C) {A : Finset (List Bool)}
    (hA : IsCut (d + n) A) :
    cutSum (prodDist ν σ) (prodGuide ν g h) A ≤
      C + ∑ u ∈ A.filter (fun u => u.length < d), (mass ν u ^ 2 / g u - C * mass ν u) := by
  classical
  set Aout := A.filter fun u => u.length < d with hAout
  set Ain := A.filter fun u => ¬ u.length < d with hAin
  have hAoutCut : IsCut d Aout := cut_lengths_split hA
  unfold cutSum
  rw [← Finset.sum_filter_add_sum_filter_not A (fun u => u.length < d)]
  -- the outer part
  have hout : ∑ u ∈ Aout, mass (prodDist ν σ) u ^ 2 / prodGuide ν g h u =
      ∑ u ∈ Aout, mass ν u ^ 2 / g u := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hl := (Finset.mem_filter.mp hu).2.le
    rw [mass_prod_short hσ.2 hl, prodGuide_short ν g h hl]
  -- the inner part, outer leaf by outer leaf
  set cov : Str d → Prop := fun x => ∃ u ∈ Aout, IsPre u x with hcov
  have hfiber : ∀ x : Str d, ∑ u ∈ Ain with headS d u = x,
      mass (prodDist ν σ) u ^ 2 / prodGuide ν g h u ≤ if cov x then 0 else ν x * C := by
    intro x
    set Fx := Ain.filter fun u => headS d u = x with hFx
    have hFmem : ∀ u ∈ Fx, u ∈ A ∧ d ≤ u.length ∧ u = List.ofFn x ++ u.drop d := by
      intro u hu
      have h1 := Finset.mem_filter.mp hu
      have h2 := Finset.mem_filter.mp h1.1
      have hl : d ≤ u.length := by omega
      refine ⟨h2.1, hl, ?_⟩
      conv_lhs => rw [eq_append_headS hl]
      rw [h1.2]
    by_cases hc : cov x
    · rw [ite_eq_left hc]
      have : Fx = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        obtain ⟨huA, hl, hux⟩ := hFmem u hu
        obtain ⟨u', hu', hu'x⟩ := hc
        have hu'A := (Finset.mem_filter.mp hu').1
        have hu'l := (Finset.mem_filter.mp hu').2
        have hpre : u' <+: u := by
          rw [hux]; exact hu'x.trans (List.prefix_append _ _)
        have := hA.2 u' hu'A u huA hpre
        rw [← this] at hl; omega
      rw [this]; simp
    · rw [ite_eq_right hc]
      set Bx := Fx.image (List.drop d) with hBx
      have hinj : Set.InjOn (List.drop d) (Fx : Set (List Bool)) := by
        intro u hu v hv huv
        rw [(hFmem u hu).2.2, (hFmem v hv).2.2]
        exact congrArg _ huv
      have hBcut : IsCut n Bx := by
        refine ⟨fun w hw => ?_, fun w hw w' hw' hww => ?_⟩
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
          have := hA.1 u (hFmem u hu).1
          simp; omega
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hw'
          have hpre : u <+: u' := by
            rw [(hFmem u hu).2.2, (hFmem u' hu').2.2]
            exact (List.prefix_append_right_inj _).mpr hww
          rw [hA.2 u (hFmem u hu).1 u' (hFmem u' hu').1 hpre]
      have hterm : ∀ u ∈ Fx, mass (prodDist ν σ) u ^ 2 / prodGuide ν g h u =
          ν x * (mass σ (u.drop d) ^ 2 / h (u.drop d)) := by
        intro u hu
        rw [(hFmem u hu).2.2, mass_prod_append, prodGuide_append hg hroot, sq_mul_div_mul,
          List.drop_left' (by simp)]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have : ∑ u ∈ Fx, mass σ (u.drop d) ^ 2 / h (u.drop d) = cutSum σ h Bx := by
        unfold cutSum
        rw [Finset.sum_image hinj]
      rw [this]
      exact mul_le_mul_of_nonneg_left (hC Bx hBcut) (hν.1 x)
  have hin : ∑ u ∈ Ain, mass (prodDist ν σ) u ^ 2 / prodGuide ν g h u ≤
      C * (1 - ∑ u ∈ Aout, mass ν u) := by
    rw [← Finset.sum_fiberwise Ain (headS d)]
    calc ∑ x, ∑ u ∈ Ain with headS d u = x, mass (prodDist ν σ) u ^ 2 / prodGuide ν g h u
        ≤ ∑ x : Str d, (if cov x then 0 else ν x * C) := Finset.sum_le_sum fun x _ => hfiber x
      _ = C * (1 - ∑ u ∈ Aout, mass ν u) := by
        rw [mass_sum_eq_covered hAoutCut, ← hν.2, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hc : cov x
        · rw [ite_eq_left hc, ite_eq_left hc]; ring
        · rw [ite_eq_right hc, ite_eq_right hc]; ring
  rw [hout]
  have : ∑ u ∈ Aout, (mass ν u ^ 2 / g u - C * mass ν u) =
      ∑ u ∈ Aout, mass ν u ^ 2 / g u - C * ∑ u ∈ Aout, mass ν u := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [this]
  linarith

/-! ### Attainment -/

/-- The cut that fills every outer leaf subtree not covered by an outer prefix-free set `A'`
with a copy of the inner cut `B`. -/
noncomputable def fillCut (A' B : Finset (List Bool)) : Finset (List Bool) := by
  classical
  exact A' ∪ ((Finset.univ.filter fun x : Str d => ¬ ∃ u ∈ A', IsPre u x) ×ˢ B).image
    fun p => List.ofFn p.1 ++ p.2

theorem fillCut_isCut {A' B : Finset (List Bool)} (hA' : A' ∈ outerCuts d) (hB : IsCut n B) :
    IsCut (d + n) (fillCut (d := d) A' B) := by
  classical
  have hA'c := mem_outerCuts.mp hA'
  unfold fillCut
  refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_⟩
  · rcases Finset.mem_union.mp hu with hu | hu
    · have := hA'c.1 u hu; omega
    · obtain ⟨⟨x, w⟩, hp, rfl⟩ := Finset.mem_image.mp hu
      have := hB.1 w (Finset.mem_product.mp hp).2
      simp; omega
  · rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact hA'c.2 u hu v hv huv
    · exfalso
      obtain ⟨⟨x, w⟩, hp, rfl⟩ := Finset.mem_image.mp hv
      have hx := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      apply hx
      refine ⟨u, hu, ?_⟩
      exact List.prefix_of_prefix_length_le huv (List.prefix_append _ _)
        (by have := hA'c.1 u hu; simp; omega)
    · exfalso
      obtain ⟨⟨x, w⟩, hp, rfl⟩ := Finset.mem_image.mp hu
      have := huv.length_le
      have := hA'c.1 v hv
      simp at *; omega
    · obtain ⟨⟨x, w⟩, hp, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨⟨x', w'⟩, hp', rfl⟩ := Finset.mem_image.mp hv
      have hxx : List.ofFn x = List.ofFn x' :=
        (List.prefix_of_prefix_length_le ((List.prefix_append _ _).trans huv)
          (List.prefix_append _ _) (by simp)).eq_of_length (by simp)
      rw [hxx] at huv ⊢
      rw [hB.2 w (Finset.mem_product.mp hp).2 w' (Finset.mem_product.mp hp').2
        ((List.prefix_append_right_inj _).mp huv)]

theorem cutSum_fillCut {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) (hg : ∀ x : Str d, g (List.ofFn x) = ν x) (hroot : h [] = 1)
    {A' B : Finset (List Bool)} (hA' : A' ∈ outerCuts d) :
    cutSum (prodDist ν σ) (prodGuide ν g h) (fillCut (d := d) A' B) =
      ∑ u ∈ A', mass ν u ^ 2 / g u + cutSum σ h B * (1 - ∑ u ∈ A', mass ν u) := by
  classical
  have hA'c := mem_outerCuts.mp hA'
  set X := Finset.univ.filter fun x : Str d => ¬ ∃ u ∈ A', IsPre u x with hX
  have hdisj : Disjoint A' ((X ×ˢ B).image fun p => List.ofFn p.1 ++ p.2) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨⟨x, w⟩, -, rfl⟩ := Finset.mem_image.mp hu'
    have := hA'c.1 _ hu
    simp at this
  have hinj : Set.InjOn (fun p : Str d × List Bool => List.ofFn p.1 ++ p.2)
      ((X ×ˢ B : Finset (Str d × List Bool)) : Set (Str d × List Bool)) := by
    rintro ⟨x, w⟩ _ ⟨x', w'⟩ _ h
    simp only at h
    have hx : List.ofFn x = List.ofFn x' := by
      have := congrArg (List.take d) h
      rwa [List.take_left' (by simp), List.take_left' (by simp)] at this
    have hx' := List.ofFn_injective hx
    rw [hx] at h
    rw [hx', List.append_cancel_left h]
  unfold fillCut cutSum
  rw [Finset.sum_union hdisj, Finset.sum_image hinj, Finset.sum_product]
  congr 1
  · refine Finset.sum_congr rfl fun u hu => ?_
    have hl := (hA'c.1 u hu).le
    rw [mass_prod_short hσ.2 hl, prodGuide_short ν g h hl]
  · have : ∀ x ∈ X, ∑ w ∈ B, mass (prodDist ν σ) (List.ofFn x ++ w) ^ 2 /
        prodGuide ν g h (List.ofFn x ++ w) = ν x * cutSum σ h B := by
      intro x _
      unfold cutSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mass_prod_append, prodGuide_append hg hroot, sq_mul_div_mul]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, mul_comm]
    congr 1
    rw [mass_sum_eq_covered (outerCuts_isCut hA'), ← hν.2, hX, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp_all

/-- An outer prefix-free set completed by the outer leaves it does not cover. -/
noncomputable def leafFill (A' : Finset (List Bool)) : Finset (List Bool) := by
  classical
  exact A' ∪ (Finset.univ.filter fun x : Str d => ¬ ∃ u ∈ A', IsPre u x).image List.ofFn

theorem leafFill_isCut {A' : Finset (List Bool)} (hA' : A' ∈ outerCuts d) :
    IsCut d (leafFill (d := d) A') := by
  classical
  have hA'c := mem_outerCuts.mp hA'
  unfold leafFill
  refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_⟩
  · rcases Finset.mem_union.mp hu with hu | hu
    · exact (hA'c.1 u hu).le
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu; simp
  · rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact hA'c.2 u hu v hv huv
    · exfalso
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hx).2 ⟨u, hu, huv⟩
    · exfalso
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
      have := huv.length_le
      have := hA'c.1 v hv
      simp at *; omega
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨x', -, rfl⟩ := Finset.mem_image.mp hv
      exact huv.eq_of_length (by simp)

theorem cutSum_leafFill {ν : Str d → ℝ} {g : Guide} (hν : IsDist ν)
    (hg : ∀ x : Str d, g (List.ofFn x) = ν x) {A' : Finset (List Bool)}
    (hA' : A' ∈ outerCuts d) :
    cutSum ν g (leafFill (d := d) A') =
      ∑ u ∈ A', mass ν u ^ 2 / g u + (1 - ∑ u ∈ A', mass ν u) := by
  classical
  have hA'c := mem_outerCuts.mp hA'
  have hdisj : Disjoint A'
      ((Finset.univ.filter fun x : Str d => ¬ ∃ u ∈ A', IsPre u x).image List.ofFn) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu'
    have := hA'c.1 _ hu
    simp at this
  unfold leafFill cutSum
  rw [Finset.sum_union hdisj, Finset.sum_image fun a _ b _ hab => List.ofFn_injective hab]
  congr 1
  simp only [mass_ofFn, hg, sq_div_self_eq]
  rw [mass_sum_eq_covered (outerCuts_isCut hA'), ← hν.2, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp_all

/-! ### The lemma -/

theorem one_le_of_capEq {σ : Str n → ℝ} {h : Guide} (hσ : IsDist σ) (hh : IsOracle σ h)
    {C : ℝ} (hC : ∀ B, IsCut n B → cutSum σ h B ≤ C) : 1 ≤ C := by
  have := hC (words n) (isCut_words le_rfl)
  have e : cutSum σ h (words n) = 1 := by
    unfold cutSum words
    rw [Finset.sum_image fun a _ b _ hab => List.ofFn_injective hab]
    simp only [mass_ofFn, hh.leaf, sq_div_self_eq]
    exact hσ.2
  linarith

/-- The product of two legal pairs is again a distribution with a guide satisfying the access
conditions (root one, exact leaves, nonnegative, zero beyond the length), so the lemma can be
iterated. -/
theorem prod_isOracle {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hg : IsOracle ν g)
    (hh : IsOracle σ h) : IsOracle (prodDist ν σ) (prodGuide ν g h) := by
  have hν0 : ∀ x, 0 ≤ ν x := fun x => by rw [← hg.leaf]; exact hg.nonneg _
  refine ⟨fun u => ?_, ?_, fun z => ?_, fun u hu => ?_⟩
  · unfold prodGuide
    split_ifs
    · exact hg.nonneg u
    · exact mul_nonneg (hν0 _) (hh.nonneg _)
  · rw [prodGuide_short ν g h (by simp)]; exact hg.root
  · rw [ofFn_split, prodGuide_append hg.leaf hh.root, hh.leaf]; rfl
  · unfold prodGuide
    rw [ite_eq_right (by omega), hh.long _ (by simp; omega), mul_zero]

/-- `lem:capacity-concatenation`, equation `eq:capacity-concatenation`: for outer and inner guides
with root value one, exact leaves and finite capacities `C_out = CC(ν,g)`, `C_in = CC(σ,h)`, the
product guide has capacity exactly
`C_in + max_{A ⊆ {0,1}^{<d} prefix-free} ∑_{u ∈ A} (ν(u)²/g(u) - C_in ν(u))`, and this value is at
most `C_out + C_in - 1`. -/
theorem lem_capacity_concatenation {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide}
    (hν : IsDist ν) (hσ : IsDist σ) (hg : IsOracle ν g) (hh : IsOracle σ h) {Cout Cin : ℝ}
    (hCout : CapEq ν g Cout) (hCin : CapEq σ h Cin) :
    CapEq (prodDist ν σ) (prodGuide ν g h) (Cin + outerVal ν g Cin) ∧
      Cin + outerVal ν g Cin ≤ Cout + Cin - 1 := by
  classical
  have hCin1 : 1 ≤ Cin := one_le_of_capEq hσ hh hCin.1.2
  refine ⟨⟨⟨fun u hu hz => ?_, fun A hA => ?_⟩, ?_⟩, ?_⟩
  · -- same supports
    by_cases hud : u.length ≤ d
    · rw [prodGuide_short ν g h hud]
      rw [mass_prod_short hσ.2 hud] at hz
      exact hCout.1.1 u hud hz
    · have hl : d ≤ u.length := by omega
      rw [eq_append_headS hl] at hz ⊢
      rw [prodGuide_append hg.leaf hh.root]
      rw [mass_prod_append] at hz
      have h1 : ν (headS d u) ≠ 0 := left_ne_zero_of_mul hz
      have h2 : mass σ (u.drop d) ≠ 0 := right_ne_zero_of_mul hz
      exact mul_ne_zero h1 (hCin.1.1 _ (by simp; omega) h2)
  · -- upper bound
    refine (cutSum_prod_le hν hσ hg.leaf hh.root hCin.1.2 hA).trans ?_
    have hmem : A.filter (fun u => u.length < d) ∈ outerCuts d :=
      mem_outerCuts.mpr ⟨fun u hu => (Finset.mem_filter.mp hu).2,
        (cut_lengths_split hA).2⟩
    have := Finset.le_sup' (fun A => ∑ u ∈ A, (mass ν u ^ 2 / g u - Cin * mass ν u)) hmem
    unfold outerVal
    linarith
  · -- attainment
    obtain ⟨A', hA', hval⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_outerCuts⟩
      fun A => ∑ u ∈ A, (mass ν u ^ 2 / g u - Cin * mass ν u)
    obtain ⟨B, hB, hBval⟩ := hCin.2
    refine ⟨fillCut A' B, fillCut_isCut hA' hB, ?_⟩
    rw [cutSum_fillCut hν hσ hg.leaf hh.root hA', hBval]
    unfold outerVal
    rw [hval, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  · -- `C_out + C_in - 1`
    unfold outerVal
    suffices hs : (outerCuts d).sup' ⟨∅, empty_mem_outerCuts⟩
        (fun A => ∑ u ∈ A, (mass ν u ^ 2 / g u - Cin * mass ν u)) ≤ Cout - 1 by linarith
    refine Finset.sup'_le _ _ fun A' hA' => ?_
    -- the outer cut `A'` completed by uncovered outer leaves
    have hout := hCout.1.2 _ (leafFill_isCut hA')
    rw [cutSum_leafFill hν hg.leaf hA'] at hout
    have hm0 : 0 ≤ ∑ u ∈ A', mass ν u := Finset.sum_nonneg fun u _ => mass_nonneg hν.1 u
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith

theorem convex_max_bound {R C t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    C + (R - C) * t ≤ max R C := by
  rcases le_total C R with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

/-- The outer sum of a prefix-free outer set against a pointwise outer guide:
`∑_{u ∈ A} (ν(u)²/g(u) - C ν(u)) ≤ (R - C) ν(A)` when `g ≥ ν/R`. -/
theorem outer_sum_le {ν : Str d → ℝ} {g : Guide} (hν : IsDist ν) {R C : ℝ} (hR : 0 < R)
    (hgR : ∀ u : List Bool, u.length < d → mass ν u / R ≤ g u) {A : Finset (List Bool)}
    (hA : ∀ u ∈ A, u.length < d) :
    ∑ u ∈ A, (mass ν u ^ 2 / g u - C * mass ν u) ≤ (R - C) * ∑ u ∈ A, mass ν u := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  have := sq_div_le_mul_of_le (mass_nonneg hν.1 u) hR (hgR u (hA u hu))
  linarith

/-- `lem:capacity-concatenation` (pointwise outer guide): if moreover `g ≥ ν/R` on the proper outer
prefixes, the capacity of the product guide is at most `max {R, C_in}`. -/
theorem capacity_concatenation_max {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide}
    (hν : IsDist ν) (hσ : IsDist σ) (hg : IsOracle ν g) (hh : IsOracle σ h) {Cout Cin : ℝ}
    (hCout : CapEq ν g Cout) (hCin : CapEq σ h Cin) {R : ℝ} (hR : 0 < R)
    (hgR : ∀ u : List Bool, u.length < d → mass ν u / R ≤ g u) :
    CapEq (prodDist ν σ) (prodGuide ν g h) (Cin + outerVal ν g Cin) ∧
      Cin + outerVal ν g Cin ≤ max R Cin := by
  refine ⟨(lem_capacity_concatenation hν hσ hg hh hCout hCin).1, ?_⟩
  unfold outerVal
  suffices hs : (outerCuts d).sup' ⟨∅, empty_mem_outerCuts⟩
      (fun A => ∑ u ∈ A, (mass ν u ^ 2 / g u - Cin * mass ν u)) ≤ max R Cin - Cin by linarith
  refine Finset.sup'_le _ _ fun A hA => ?_
  have h1 := outer_sum_le (C := Cin) hν hR hgR (mem_outerCuts.mp hA).1
  have h2 := (outerCuts_isCut hA).mass_sum_le hν.1
  rw [hν.2] at h2
  have h3 : 0 ≤ ∑ u ∈ A, mass ν u := Finset.sum_nonneg fun u _ => mass_nonneg hν.1 u
  have := convex_max_bound (R := R) (C := Cin) h3 h2
  linarith

/-- `lem:capacity-concatenation`, `thm:composition`: the capacity bound `max {R, C}`; only an upper
bound `C` on the inner capacity is assumed, and the outer guide is pointwise factor `R` on
`{0,1}^{≤ d}`. -/
theorem capLE_prod {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) (hg : IsOracle ν g) (hh : IsOracle σ h) {R C : ℝ} (hR : 0 < R)
    (hgR : ∀ u : List Bool, u.length ≤ d → mass ν u / R ≤ g u) (hC : CapLE σ h C) :
    CapLE (prodDist ν σ) (prodGuide ν g h) (max R C) := by
  classical
  refine ⟨fun u hu hz => ?_, fun A hA => ?_⟩
  · by_cases hud : u.length ≤ d
    · rw [prodGuide_short ν g h hud]
      rw [mass_prod_short hσ.2 hud] at hz
      have hpos : 0 < mass ν u := lt_of_le_of_ne (mass_nonneg hν.1 u) (Ne.symm hz)
      exact ne_of_gt (lt_of_lt_of_le (div_pos hpos hR) (hgR u hud))
    · have hl : d ≤ u.length := by omega
      rw [eq_append_headS hl] at hz ⊢
      rw [prodGuide_append hg.leaf hh.root]
      rw [mass_prod_append] at hz
      exact mul_ne_zero (left_ne_zero_of_mul hz)
        (hC.1 _ (by simp; omega) (right_ne_zero_of_mul hz))
  · refine (cutSum_prod_le hν hσ hg.leaf hh.root hC.2 hA).trans ?_
    have hAout := cut_lengths_split hA
    have h1 := outer_sum_le (C := C) hν hR (fun u hu => hgR u hu.le)
      (A := A.filter fun u => u.length < d) (fun u hu => (Finset.mem_filter.mp hu).2)
    have h2 := hAout.mass_sum_le hν.1
    rw [hν.2] at h2
    have h3 : 0 ≤ ∑ u ∈ A.filter (fun u => u.length < d), mass ν u :=
      Finset.sum_nonneg fun u _ => mass_nonneg hν.1 u
    have := convex_max_bound (R := R) (C := C) h3 h2
    linarith

/-- `lem:capacity-concatenation` (repeated concatenation): the product is again a distribution
with a guide satisfying the access conditions and finite capacity, whose excess over one is at most
the sum of the two excesses; by induction, repeated concatenation adds at most the capacities'
excesses above one. -/
theorem capacity_concatenation_iter {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide}
    (hν : IsDist ν) (hσ : IsDist σ) (hg : IsOracle ν g) (hh : IsOracle σ h) {Cout Cin : ℝ}
    (hCout : CapEq ν g Cout) (hCin : CapEq σ h Cin) :
    IsDist (prodDist ν σ) ∧ IsOracle (prodDist ν σ) (prodGuide ν g h) ∧
      ∃ C', CapEq (prodDist ν σ) (prodGuide ν g h) C' ∧ C' - 1 ≤ (Cout - 1) + (Cin - 1) := by
  obtain ⟨h1, h2⟩ := lem_capacity_concatenation hν hσ hg hh hCout hCin
  exact ⟨isDist_prodDist hν hσ, prod_isOracle hg hh, _, h1, by linarith⟩

end Sec5
end LearningGuided
