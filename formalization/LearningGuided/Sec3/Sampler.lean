import LearningGuided.Sec3.Prelim

/-!
# Search with thinning

The generic sampler of Section 3 ("Search with thinning"). Known
prefix groups are indexed by `Fin G`. A uniformly shifted cyclic block of `q` consecutive group
indices is chosen, so that every group is included with probability `q/G`. The algorithm queries
these groups until a test passes. On a hit it flips a coin with success probability `c`, and on
success runs a recovery procedure. Every other branch outputs a fresh draw from a known fallback
law.

* `thinSearch`: the sampler on `G` indexed groups, with its output law `lawR_thinSearch` and its
  deterministic cap `within_thinSearch`;
* `partSampler`: the same sampler on the groups `{grp x : x ∈ S}` of a candidate set, with
  `q = ⌈βG⌉` and coin `βG/q`; its output law is exactly `(1-β)ν + βδ_x`
  (`lawR_partSampler`) and its cap is `⌈βG⌉ + r` (`within_partSampler`);
* `branch_balance`: equation `eq:branch-balance`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### Sequential search over a list of groups -/

open Classical in
/-- Query the groups of a list in order until a test passes; return the first passing group. -/
noncomputable def searchL {ι : Type} (w : ι → List Bool) (test : ι → ℝ → Prop) :
    List ι → Alg (Option ι)
  | [] => .ret none
  | i :: L => .query (w i) fun r => if test i r then .ret (some i) else searchL w test L

theorem within_searchL {ι : Type} (w : ι → List Bool) (test : ι → ℝ → Prop) (h : Guide) :
    ∀ L : List ι, (searchL w test L).Within h L.length
  | [] => Alg.Within.ret _ _
  | i :: L => by
      refine Alg.Within.query _ _ _ ?_
      by_cases ht : test i (h (w i))
      · simp only [ht, ite_true]
        exact Alg.Within.ret _ _
      · simp only [ht, ite_false]
        exact within_searchL w test h L

theorem run_searchL {ι : Type} [DecidableEq ι] (w : ι → List Bool) (test : ι → ℝ → Prop)
    {h : Guide} {i₀ : ι} (htest : ∀ i, test i (h (w i)) ↔ i = i₀) :
    ∀ L : List ι, (searchL w test L).run h = PMF.pure (if i₀ ∈ L then some i₀ else none)
  | [] => by simp [searchL]
  | i :: L => by
      simp only [searchL, Alg.run_query]
      by_cases hi : i = i₀
      · subst hi
        simp [(htest i).2 rfl]
      · have ht : ¬ test i (h (w i)) := fun ht => hi ((htest i).1 ht)
        simp only [ht, ite_false, run_searchL w test htest L, List.mem_cons]
        congr 1
        by_cases hm : i₀ ∈ L
        · simp [hm]
        · simp [hm, Ne.symm hi]

/-! ### Uniformly shifted cyclic blocks -/

/-- The cyclic block `{s, s+1, …, s+q-1}` (modulo `G`) of group indices. -/
noncomputable def block {G : ℕ} (q : ℕ) (s : Fin G) : List (Fin G) :=
  (Finset.univ.filter fun g : Fin G => (g - s).val < q).toList

theorem mem_block {G : ℕ} {q : ℕ} {s g : Fin G} : g ∈ block q s ↔ (g - s).val < q := by
  simp [block]

theorem length_block {G : ℕ} [NeZero G] (q : ℕ) (s : Fin G) : (block q s).length ≤ q := by
  rw [block, Finset.length_toList]
  have : (Finset.univ.filter fun g : Fin G => (g - s).val < q).card =
      (Finset.univ.filter fun t : Fin G => t.val < q).card :=
    Finset.card_equiv (Equiv.subRight s) fun i => by simp
  rw [this, Fin.card_filter_val_lt]
  exact min_le_right _ _

/-- `eq:branch-balance`, equal inclusion: every group lies in exactly `q` of the `G` shifted blocks
(`q ≤ G`), so a uniformly shifted block includes each group with probability `q/G`. -/
theorem card_block_mem {G : ℕ} [NeZero G] {q : ℕ} (hq : q ≤ G) (g : Fin G) :
    (Finset.univ.filter fun s : Fin G => g ∈ block q s).card = q := by
  have : (Finset.univ.filter fun s : Fin G => g ∈ block q s).card =
      (Finset.univ.filter fun t : Fin G => t.val < q).card :=
    Finset.card_equiv (Equiv.subLeft g) fun i => by simp [mem_block]
  rw [this, Fin.card_filter_val_lt, min_eq_right hq]

/-! ### The thinned search -/

open Classical in
/-- Search a uniformly shifted cyclic block of `q` of the `G` groups `w g` with the tests
`test g`; on a hit at `g`, continue with `rec g` with probability `c`; every other branch runs
the fallback `fb`. -/
noncomputable def thinSearch {G : ℕ} [NeZero G] (q : ℕ) (w : Fin G → List Bool)
    (test : Fin G → ℝ → Prop) (c : ℝ) (rec : Fin G → Alg (Str n)) (fb : Alg (Str n)) :
    Alg (Str n) :=
  .sample (PMF.uniformOfFintype (Fin G)) fun s =>
    bindA (searchL w test (block q s)) fun o =>
      match o with
      | none => fb
      | some g => .sample (coin c) fun b => if b then rec g else fb

/-- The deterministic cap of the thinned search: `q` search queries plus the recovery cap. -/
theorem within_thinSearch {G : ℕ} [NeZero G] (q : ℕ) (w : Fin G → List Bool)
    (test : Fin G → ℝ → Prop) (c : ℝ) (rec : Fin G → Alg (Str n)) (fb : Alg (Str n))
    {h : Guide} {r : ℕ} (hrec : ∀ g, (rec g).Within h r) (hfb : fb.Within h 0) :
    (thinSearch q w test c rec fb).Within h (q + r) := by
  refine Alg.Within.sample _ _ _ fun s _ => ?_
  refine within_bindA ((within_searchL w test h _).mono (length_block q s)) fun o => ?_
  rcases o with _ | g
  · exact hfb.mono (Nat.zero_le _)
  · refine Alg.Within.sample _ _ _ fun b _ => ?_
    cases b
    · exact hfb.mono (Nat.zero_le _)
    · exact hrec g

/-- The output law of the thinned search. If exactly the group `g₀` passes its test, the
recovery from `g₀` outputs `x`, and the fallback has law `ν`, then the complete output law is
`(1 - qc/G) ν + (qc/G) δ_x`. -/
theorem lawR_thinSearch {G : ℕ} [NeZero G] {q : ℕ} (hq : q ≤ G) (w : Fin G → List Bool)
    (test : Fin G → ℝ → Prop) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (rec : Fin G → Alg (Str n)) (fb : Alg (Str n)) {h : Guide} {g₀ : Fin G} {x : Str n}
    {ν : Str n → ℝ} (htest : ∀ g, test g (h (w g)) ↔ g = g₀) (hrec : (rec g₀).run h = PMF.pure x)
    (hfb : lawR (fb.run h) = ν) (y : Str n) :
    lawR ((thinSearch q w test c rec fb).run h) y =
      (1 - q * c / G) * ν y + q * c / G * dirac x y := by
  classical
  have hG : (0 : ℝ) < G := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne G)
  have hstep : ∀ s : Fin G, lawR (((fun o : Option (Fin G) =>
      match o with
      | none => fb
      | some g => Alg.sample (coin c) fun b => if b then rec g else fb)
        (if g₀ ∈ block q s then some g₀ else none)).run h) y =
      if g₀ ∈ block q s then c * dirac x y + (1 - c) * ν y else ν y := by
    intro s
    by_cases hs : g₀ ∈ block q s
    · simp only [hs, ite_true, Alg.run_sample]
      rw [lawR_bind, Fintype.sum_bool, lawR_coin hc0 hc1, lawR_coin hc0 hc1]
      simp [hrec, lawR_pure, hfb]
    · simp [hs, hfb]
  simp only [thinSearch, Alg.run_sample]
  rw [lawR_bind]
  simp only [run_bindA, run_searchL w test htest, PMF.pure_bind]
  simp only [hstep, lawR_uniformOfFintype, Fintype.card_fin]
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul]
  have hc := card_block_mem hq g₀
  have hc' : (Finset.univ.filter fun s : Fin G => ¬ g₀ ∈ block q s).card = G - q := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hc,
      Finset.card_univ, Fintype.card_fin]
  rw [hc, hc', Nat.cast_sub hq]
  field_simp
  ring

/-- `eq:branch-balance`: with `q = ⌈βG⌉` and coin `βG/q`, the atom-output branch has
probability `(q/G)(βG/q) = β`; the coin is a probability when `0 ≤ β ≤ 1`. -/
theorem branch_balance {β : ℝ} (hβ0 : 0 ≤ β) {G : ℕ} (hG : 0 < G) :
    (⌈β * G⌉₊ : ℝ) * (β * G / ⌈β * G⌉₊) / G = β ∧ 0 ≤ β * G / ⌈β * G⌉₊ ∧
      β * G / ⌈β * G⌉₊ ≤ 1 := by
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  refine ⟨?_, div_nonneg (mul_nonneg hβ0 hGr.le) (Nat.cast_nonneg _), ?_⟩
  · rcases eq_or_lt_of_le (Nat.zero_le ⌈β * G⌉₊) with h0 | hpos
    · rw [← h0]
      have : β * G ≤ 0 := Nat.ceil_eq_zero.mp h0.symm
      have hβ : β = 0 := by nlinarith
      simp [hβ]
    · have : (0 : ℝ) < ⌈β * G⌉₊ := by exact_mod_cast hpos
      field_simp
  · rcases eq_or_lt_of_le (Nat.zero_le ⌈β * G⌉₊) with h0 | hpos
    · rw [← h0]; simp
    · have : (0 : ℝ) < ⌈β * G⌉₊ := by exact_mod_cast hpos
      rw [div_le_one this]
      exact Nat.le_ceil _

theorem ceil_le_of_le_one {β : ℝ} (hβ1 : β ≤ 1) (G : ℕ) : ⌈β * G⌉₊ ≤ G := by
  rw [Nat.ceil_le]
  have : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  nlinarith

/-! ### The sampler on the groups of a candidate set -/

/-- Enumeration of the groups `{grp x : x ∈ S}`. -/
noncomputable def groupWord (grp : Str n → List Bool) (S : Finset (Str n))
    (g : Fin (S.image grp).card) : List Bool :=
  ((S.image grp).equivFin.symm g).1

theorem groupWord_mem (grp : Str n → List Bool) (S : Finset (Str n))
    (g : Fin (S.image grp).card) : groupWord grp S g ∈ S.image grp :=
  ((S.image grp).equivFin.symm g).2

theorem groupWord_injective (grp : Str n → List Bool) (S : Finset (Str n)) :
    Function.Injective (groupWord grp S) := fun _ _ hg =>
  (S.image grp).equivFin.symm.injective (Subtype.ext hg)

/-- The sampler of Section 3 on the groups `{grp x : x ∈ S}` of a candidate set. With
`G` groups, it searches `q = ⌈βG⌉` groups of a uniformly shifted block with the tests `test`,
proceeds on a hit with probability `βG/q` to the recovery `rec`, and otherwise runs the fallback
`fb` (a fresh draw from the background). -/
noncomputable def partSampler (grp : Str n → List Bool) (S : Finset (Str n)) (β : ℝ)
    (test : List Bool → ℝ → Prop) (rec : List Bool → Alg (Str n)) (fb : Alg (Str n)) :
    Alg (Str n) :=
  if hG : (S.image grp).card = 0 then fb
  else
    haveI : NeZero (S.image grp).card := ⟨hG⟩
    thinSearch ⌈β * (S.image grp).card⌉₊ (groupWord grp S)
      (fun g r => test (groupWord grp S g) r)
      (β * (S.image grp).card / ⌈β * (S.image grp).card⌉₊)
      (fun g => rec (groupWord grp S g)) fb

/-- The deterministic cap of `partSampler`: `⌈βG⌉` search queries plus the recovery cap. -/
theorem within_partSampler (grp : Str n → List Bool) (S : Finset (Str n)) (β : ℝ)
    (test : List Bool → ℝ → Prop) (rec : List Bool → Alg (Str n)) (fb : Alg (Str n))
    {h : Guide} {r : ℕ} (hrec : ∀ u ∈ S.image grp, (rec u).Within h r) (hfb : fb.Within h 0) :
    (partSampler grp S β test rec fb).Within h (⌈β * (S.image grp).card⌉₊ + r) := by
  unfold partSampler
  split_ifs with hG
  · exact hfb.mono (Nat.zero_le _)
  · have : NeZero (S.image grp).card := ⟨hG⟩
    exact within_thinSearch _ _ _ _ _ _ (fun g => hrec _ (groupWord_mem grp S g)) hfb

/-- The exact output law of `partSampler` (equation `eq:local-output` in general form). If the
groups separate the hidden atom `x ∈ S` (a group is a prefix of `x` exactly when it is the group
of `x`), the group tests are exact, the recovery from the group of `x` outputs `x`, and the
fallback has law `ν`, then the complete output law is `(1-β)ν + βδ_x`. -/
theorem lawR_partSampler (grp : Str n → List Bool) {S : Finset (Str n)} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (test : List Bool → ℝ → Prop) (rec : List Bool → Alg (Str n))
    (fb : Alg (Str n)) {h : Guide} {x : Str n} {ν : Str n → ℝ} (hx : x ∈ S)
    (hpart : ∀ y ∈ S, IsPre (grp y) x ↔ grp y = grp x)
    (htest : ∀ u ∈ S.image grp, test u (h u) ↔ IsPre u x)
    (hrec : (rec (grp x)).run h = PMF.pure x) (hfb : lawR (fb.run h) = ν) :
    lawR ((partSampler grp S β test rec fb).run h) = atomTarget ν β x := by
  have hGpos : 0 < (S.image grp).card :=
    Finset.card_pos.mpr ⟨grp x, Finset.mem_image_of_mem grp hx⟩
  have hG : (S.image grp).card ≠ 0 := Nat.pos_iff_ne_zero.mp hGpos
  have : NeZero (S.image grp).card := ⟨hG⟩
  set G := (S.image grp).card with hGdef
  have hxmem : grp x ∈ S.image grp := Finset.mem_image_of_mem grp hx
  set g₀ : Fin G := (S.image grp).equivFin ⟨grp x, hxmem⟩ with hg₀
  have hw₀ : groupWord grp S g₀ = grp x := by
    simp [groupWord, hg₀]
  have htest' : ∀ g, test (groupWord grp S g) (h (groupWord grp S g)) ↔ g = g₀ := by
    intro g
    obtain ⟨y, hy, hyg⟩ := Finset.mem_image.mp (groupWord_mem grp S g)
    rw [htest _ (groupWord_mem grp S g), ← hyg, hpart y hy]
    constructor
    · intro he
      apply groupWord_injective grp S
      rw [hw₀, ← he, hyg]
    · intro he
      rw [he, hw₀] at hyg
      exact hyg
  obtain ⟨hbal, hc0, hc1⟩ := branch_balance hβ0 hGpos
  funext y
  unfold partSampler
  rw [dite_eq_right hG]
  rw [lawR_thinSearch (ceil_le_of_le_one hβ1 G) _ _ hc0 hc1 _ fb (g₀ := g₀) htest'
    (by simpa [hw₀] using hrec) hfb y, hbal]
  rfl

end LearningGuided.Sec3
