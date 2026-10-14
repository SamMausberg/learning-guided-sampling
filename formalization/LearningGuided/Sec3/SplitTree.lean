import LearningGuided.Sec3.Arbitrary

/-!
# The split tree of a known mass

Lemma `lem:background-partition`: starting at the root, split a prefix when its mass exceeds `τ`
and its depth is less than `n`. The leaves of the resulting binary tree partition `{0,1}^n`.
The leaf containing a string `x` is `splitGroup w τ x = x_{1:t}`, where `t` is the first depth at
which `x_{1:t}` is terminal (mass at most `τ`, or depth `n`).

* `splitGroup_part`: the leaves are prefix-free (a leaf is a prefix of `y` only if it is the leaf
  of `y`);
* `splitGroup_light`: a nonleaf terminal group has mass at most `τ`;
* `card_splitGroups_le`: the number of leaves is at most one plus the number of internal nodes,
  and there are at most `min{2^t, τ⁻¹}` internal nodes at depth `t`, giving `eq:partition-count`.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-- `x_{1:t}` is terminal: depth `n`, or mass at most `τ`. -/
def Term (w : Str n → ℝ) (τ : ℝ) (x : Str n) (t : ℕ) : Prop := n ≤ t ∨ mass w (pre x t) ≤ τ

theorem exists_term (w : Str n → ℝ) (τ : ℝ) (x : Str n) : ∃ t, Term w τ x t :=
  ⟨n, Or.inl le_rfl⟩

open Classical in
/-- The depth of the leaf of the split tree containing `x`. -/
noncomputable def splitDepth (w : Str n → ℝ) (τ : ℝ) (x : Str n) : ℕ :=
  Nat.find (exists_term w τ x)

/-- The leaf of the split tree containing `x`. -/
noncomputable def splitGroup (w : Str n → ℝ) (τ : ℝ) (x : Str n) : List Bool :=
  pre x (splitDepth w τ x)

theorem splitDepth_le (w : Str n → ℝ) (τ : ℝ) (x : Str n) : splitDepth w τ x ≤ n := by
  classical
  exact Nat.find_min' (exists_term w τ x) (Or.inl le_rfl)

theorem splitDepth_spec (w : Str n → ℝ) (τ : ℝ) (x : Str n) :
    Term w τ x (splitDepth w τ x) := by
  classical
  exact Nat.find_spec (exists_term w τ x)

theorem not_term_of_lt {w : Str n → ℝ} {τ : ℝ} {x : Str n} {s : ℕ} (hs : s < splitDepth w τ x) :
    ¬ Term w τ x s := by
  classical
  exact Nat.find_min (exists_term w τ x) hs

theorem length_splitGroup (w : Str n → ℝ) (τ : ℝ) (x : Str n) :
    (splitGroup w τ x).length = splitDepth w τ x :=
  length_pre x (splitDepth_le w τ x)

theorem isPre_splitGroup (w : Str n → ℝ) (τ : ℝ) (x : Str n) : IsPre (splitGroup w τ x) x :=
  isPre_pre x _

/-- A nonleaf terminal group has mass at most `τ`. -/
theorem splitGroup_light (w : Str n → ℝ) (τ : ℝ) (x : Str n)
    (hlen : (splitGroup w τ x).length < n) : mass w (splitGroup w τ x) ≤ τ := by
  rw [length_splitGroup] at hlen
  rcases splitDepth_spec w τ x with h | h
  · omega
  · exact h

theorem pre_eq_of_pre_eq {x y : Str n} {t s : ℕ} (hst : s ≤ t) (h : pre y t = pre x t) :
    pre y s = pre x s := by
  have hy : pre y s = (pre y t).take s := by
    simp only [pre, List.take_take, min_eq_left hst]
  have hx : pre x s = (pre x t).take s := by
    simp only [pre, List.take_take, min_eq_left hst]
  rw [hy, hx, h]

/-- `lem:background-partition`: the leaves partition the strings: if the leaf of `x` is a prefix of
`y`, it is the leaf of `y`. -/
theorem splitGroup_part {w : Str n → ℝ} {τ : ℝ} {x y : Str n}
    (h : IsPre (splitGroup w τ x) y) : splitGroup w τ y = splitGroup w τ x := by
  classical
  set t := splitDepth w τ x with ht
  have hpre : pre y t = pre x t := by
    have := isPre_iff_pre.mp h
    rw [length_splitGroup] at this
    exact this.symm
  have hterm : ∀ s ≤ t, (Term w τ y s ↔ Term w τ x s) := by
    intro s hs
    unfold Term
    rw [pre_eq_of_pre_eq hs hpre]
  have hdy : splitDepth w τ y = t := by
    rw [splitDepth, Nat.find_eq_iff]
    refine ⟨(hterm t le_rfl).2 (splitDepth_spec w τ x), fun s hs => ?_⟩
    rw [hterm s hs.le]
    exact not_term_of_lt hs
  unfold splitGroup
  rw [hdy, hpre]

/-- A group is a prefix of a candidate exactly when it is that candidate's group. -/
theorem splitGroup_isPre_iff {w : Str n → ℝ} {τ : ℝ} {x y : Str n} :
    IsPre (splitGroup w τ y) x ↔ splitGroup w τ y = splitGroup w τ x := by
  constructor
  · intro h
    exact (splitGroup_part h).symm
  · intro h
    rw [h]
    exact isPre_splitGroup w τ x

/-- Prefix masses decrease along descendants. -/
theorem mass_le_of_prefix {w : Str n → ℝ} (hw : ∀ y, 0 ≤ w y) {g v : List Bool}
    (hgv : g <+: v) : mass w v ≤ mass w g := by
  unfold mass
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hv : IsPre v y
  · have hg : IsPre g y := hgv.trans hv
    rw [ite_eq_left hv, ite_eq_left hg]
  · rw [ite_eq_right hv]
    split_ifs <;> simp [hw y]

/-! ### Counting the leaves -/

/-- The internal (heavy) nodes: words of length less than `n` with mass more than `τ`. -/
noncomputable def heavyWords (n : ℕ) (w : Str n → ℝ) (τ : ℝ) : Finset (List Bool) :=
  ((Finset.range n).biUnion fun t => words t).filter fun v => τ < mass w v

theorem mem_heavyWords {w : Str n → ℝ} {τ : ℝ} {v : List Bool} :
    v ∈ heavyWords n w τ ↔ v.length < n ∧ τ < mass w v := by
  simp [heavyWords, mem_words]

theorem prefix_append_of_prefix_ne {u v : List Bool} (h : u <+: v) (hne : u ≠ v) :
    ∃ b : Bool, u ++ [b] <+: v := by
  obtain ⟨r, rfl⟩ := h
  rcases r with _ | ⟨b, r⟩
  · simp at hne
  · exact ⟨b, ⟨r, by simp⟩⟩

theorem isPre_children {u : List Bool} {y : Str n} (hu : IsPre u y) (hlen : u.length < n) :
    IsPre (u ++ [false]) y ∨ IsPre (u ++ [true]) y := by
  by_cases hf : IsPre (u ++ [false]) y
  · exact Or.inl hf
  · exact Or.inr (isPre_append_true_of_not_false hu hlen hf)

/-- The main counting step, by induction on the height: below a node `u` of the split tree, the
number of leaves is at most one plus the number of heavy words below `u`. -/
theorem card_below_le (w : Str n → ℝ) (τ : ℝ) :
    ∀ (j : ℕ) (u : List Bool), n - u.length = j → u.length ≤ n →
      (∀ s < u.length, s < n ∧ τ < mass w (u.take s)) →
      ((Finset.univ.filter (IsPre u)).image (splitGroup w τ)).card ≤
        1 + ((heavyWords n w τ).filter fun v => u <+: v).card := by
  classical
  intro j
  induction j with
  | zero =>
      intro u hj hun hnode
      have hlen : u.length = n := by omega
      refine le_trans ?_ (Nat.le_add_right _ _)
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hb
      have h1 := (Finset.mem_filter.mp hy).2
      have h2 := (Finset.mem_filter.mp hy').2
      have e1 : u = List.ofFn y := h1.eq_of_length (by simp [hlen])
      have e2 : u = List.ofFn y' := h2.eq_of_length (by simp [hlen])
      rw [List.ofFn_injective (e1.symm.trans e2)]
  | succ j ih =>
      intro u hj hun hnode
      have hlt : u.length < n := by omega
      have hpre : ∀ y : Str n, IsPre u y → ∀ s < u.length, ¬ Term w τ y s := by
        intro y hy s hs
        have hps : pre y s = u.take s := by
          rw [isPre_iff_pre.mp hy]
          simp only [pre, List.take_take, min_eq_left hs.le]
        unfold Term
        rw [hps]
        have := hnode s hs
        push Not
        exact ⟨by omega, this.2⟩
      by_cases hterm : τ < mass w u
      · -- an internal node: split into the two children
        have hchild : ∀ b : Bool, ∀ s < (u ++ [b]).length,
            s < n ∧ τ < mass w ((u ++ [b]).take s) := by
          intro b s hs
          simp only [List.length_append, List.length_singleton] at hs
          rcases Nat.lt_or_ge s u.length with h | h
          · rw [List.take_append_of_le_length h.le]
            exact hnode s h
          · have : s = u.length := by omega
            subst this
            rw [List.take_left]
            exact ⟨hlt, hterm⟩
        have hsplit : (Finset.univ.filter (IsPre u)).image (splitGroup w τ) ⊆
            (Finset.univ.filter (IsPre (u ++ [false]))).image (splitGroup w τ) ∪
              (Finset.univ.filter (IsPre (u ++ [true]))).image (splitGroup w τ) := by
          intro g hg
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg
          rcases isPre_children (Finset.mem_filter.mp hy).2 hlt with h | h
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [h]))
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [h]))
        have h0 := ih (u ++ [false]) (by simp; omega) (by simp; omega) (hchild false)
        have h1 := ih (u ++ [true]) (by simp; omega) (by simp; omega) (hchild true)
        have hH : ((heavyWords n w τ).filter fun v => u ++ [false] <+: v) ∪
            ((heavyWords n w τ).filter fun v => u ++ [true] <+: v) ∪ {u} ⊆
            (heavyWords n w τ).filter fun v => u <+: v := by
          intro v hv
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hv
          rcases hv with (⟨hv, hp⟩ | ⟨hv, hp⟩) | rfl
          · exact Finset.mem_filter.mpr ⟨hv, (List.prefix_append _ _).trans hp⟩
          · exact Finset.mem_filter.mpr ⟨hv, (List.prefix_append _ _).trans hp⟩
          · exact Finset.mem_filter.mpr ⟨mem_heavyWords.mpr ⟨hlt, hterm⟩, List.prefix_rfl⟩
        have hdisj1 : Disjoint ((heavyWords n w τ).filter fun v => u ++ [false] <+: v)
            ((heavyWords n w τ).filter fun v => u ++ [true] <+: v) := by
          rw [Finset.disjoint_left]
          intro v hv hv'
          have p1 := (Finset.mem_filter.mp hv).2
          have p2 := (Finset.mem_filter.mp hv').2
          rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
          · have := h.eq_of_length (by simp)
            simp at this
          · have := h.eq_of_length (by simp)
            simp at this
        have hdisj2 : Disjoint (((heavyWords n w τ).filter fun v => u ++ [false] <+: v) ∪
            ((heavyWords n w τ).filter fun v => u ++ [true] <+: v)) {u} := by
          rw [Finset.disjoint_singleton_right]
          intro hu
          rcases Finset.mem_union.mp hu with h | h
          · have := (Finset.mem_filter.mp h).2.length_le
            simp at this
          · have := (Finset.mem_filter.mp h).2.length_le
            simp at this
        have hc := Finset.card_le_card hH
        rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
          Finset.card_singleton] at hc
        have hc' := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
        omega
      · -- a terminal node: every string below `u` has the leaf `u`
        have hsub : (Finset.univ.filter (IsPre u)).image (splitGroup w τ) ⊆ {u} := by
          intro g hg
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg
          have hyu := (Finset.mem_filter.mp hy).2
          have hdepth : splitDepth w τ y = u.length := by
            classical
            rw [splitDepth, Nat.find_eq_iff]
            refine ⟨Or.inr ?_, fun s hs => hpre y hyu s hs⟩
            rw [← isPre_iff_pre.mp hyu]
            exact not_lt.mp hterm
          rw [Finset.mem_singleton, splitGroup, hdepth, ← isPre_iff_pre.mp hyu]
        exact (Finset.card_le_card hsub).trans (by simp)

/-- `lem:background-partition`: the number of leaves of the split tree is at most one plus the
number of heavy words. -/
theorem card_splitGroups_le_heavy (w : Str n → ℝ) (τ : ℝ) (S : Finset (Str n)) :
    (S.image (splitGroup w τ)).card ≤ 1 + (heavyWords n w τ).card := by
  have h := card_below_le w τ _ [] rfl (Nat.zero_le n) (fun s hs => absurd hs (by simp))
  simp only [List.nil_prefix, Finset.filter_true] at h
  refine le_trans (Finset.card_le_card ?_) (h.trans ?_)
  · exact Finset.image_subset_image (fun y _ => by simp [isPre_nil])
  · rfl

/-- `lem:background-partition`: at depth `t` there are at most `min{2^t, τ⁻¹}` heavy words. -/
theorem card_heavy_level_le {w : Str n → ℝ} (hw : IsDist w) {τ : ℝ} (hτ : 0 < τ) {t : ℕ}
    (ht : t ≤ n) :
    (((words t).filter fun v => τ < mass w v).card : ℝ) ≤ min ((2 : ℝ) ^ t) τ⁻¹ := by
  refine le_min ?_ ?_
  · have := (Finset.card_filter_le (words t) fun v => τ < mass w v).trans (card_words t).le
    exact_mod_cast this
  · set c := ((words t).filter fun v => τ < mass w v).card with hcdef
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, Nat.cast_zero]
      positivity
    · have hc : (0 : ℝ) < c := by exact_mod_cast hpos
      have hsum : ∑ v ∈ (words t).filter (fun v => τ < mass w v), τ ≤
          ∑ v ∈ (words t).filter (fun v => τ < mass w v), mass w v :=
        Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2.le
      have htot : ∑ v ∈ (words t).filter (fun v => τ < mass w v), mass w v ≤ 1 := by
        rw [← hw.2, ← sum_mass_words w ht]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun v _ _ => mass_nonneg hw.1 v
      rw [Finset.sum_const, nsmul_eq_mul, ← hcdef] at hsum
      have hcτ : (c : ℝ) * τ ≤ 1 := by linarith
      calc (c : ℝ) = c * τ * τ⁻¹ := by field_simp
        _ ≤ 1 * τ⁻¹ := by gcongr
        _ = τ⁻¹ := one_mul _

/-- `eq:partition-count`: the number of nonempty groups is at most
`min{M, 1 + ∑_{t<n} min{2^t, τ⁻¹}}`. -/
theorem card_splitGroups_le {w : Str n → ℝ} (hw : IsDist w) {τ : ℝ} (hτ : 0 < τ)
    (S : Finset (Str n)) :
    ((S.image (splitGroup w τ)).card : ℝ) ≤
      min (S.card : ℝ) (1 + ∑ t ∈ Finset.range n, min ((2 : ℝ) ^ t) τ⁻¹) := by
  classical
  refine le_min (by exact_mod_cast Finset.card_image_le) ?_
  have h1 := card_splitGroups_le_heavy w τ S
  have h2 : (heavyWords n w τ).card =
      ∑ t ∈ Finset.range n, ((words t).filter fun v => τ < mass w v).card := by
    rw [heavyWords, Finset.filter_biUnion, Finset.card_biUnion]
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hva hvb
    have := mem_words.mp (Finset.mem_filter.mp hva).1
    have := mem_words.mp (Finset.mem_filter.mp hvb).1
    omega
  have h3 : ((heavyWords n w τ).card : ℝ) ≤ ∑ t ∈ Finset.range n, min ((2 : ℝ) ^ t) τ⁻¹ := by
    rw [h2]
    push_cast
    exact Finset.sum_le_sum fun t ht =>
      card_heavy_level_le hw hτ (Finset.mem_range.mp ht).le
  have : ((S.image (splitGroup w τ)).card : ℝ) ≤ 1 + (heavyWords n w τ).card := by
    exact_mod_cast h1
  linarith

end LearningGuided.Sec3
