import LearningGuided.Sec3.Sampler

/-!
# Recovering the atom after a hit

Two recovery procedures used on the atom-output branch:

* `bitRec`: recovery of the remaining key bits by zero-child queries (Section 3.2), one query per
  bit;
* `balRec`: recovery by balanced prefix tests inside a group (Proposition
  `prop:arbitrary-locations` and Lemma `lem:background-partition`): some descendant prefix of the
  group contains between `N/3` and `2N/3` of the `N ≥ 2` remaining candidates, so each query
  retains at most `2N/3` of them, and `⌈log_{3/2} M⌉` queries suffice for `M` candidates.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### Zero-child recovery of key bits -/

open Classical in
/-- Starting from a known prefix `u`, recover `m` further bits: query the zero child and move to
it when the test passes, otherwise to the one child. Returns the word reached. -/
noncomputable def bitRec (test : ℝ → Prop) : List Bool → ℕ → Alg (List Bool)
  | u, 0 => .ret u
  | u, m + 1 => .query (u ++ [false]) fun r =>
      if test r then bitRec test (u ++ [false]) m else bitRec test (u ++ [true]) m

theorem within_bitRec (test : ℝ → Prop) (h : Guide) :
    ∀ (u : List Bool) (m : ℕ), (bitRec test u m).Within h m
  | u, 0 => Alg.Within.ret _ _
  | u, m + 1 => by
      refine Alg.Within.query _ _ _ ?_
      by_cases ht : test (h (u ++ [false]))
      · simp only [ht, ite_true]
        exact within_bitRec test h _ m
      · simp only [ht, ite_false]
        exact within_bitRec test h _ m

theorem isPre_append_true_of_not_false {u : List Bool} {x : Str n} (hu : IsPre u x)
    (hlen : u.length < n) (hf : ¬ IsPre (u ++ [false]) x) : IsPre (u ++ [true]) x := by
  rw [isPre_append_singleton] at hf ⊢
  have hx : (List.ofFn x)[u.length]? = some (x ⟨u.length, hlen⟩) := by simp [hlen]
  refine ⟨hu, ?_⟩
  rw [hx] at hf ⊢
  cases hb : x ⟨u.length, hlen⟩
  · exact absurd ⟨hu, by rw [hb]⟩ hf
  · rfl

/-- Correctness of zero-child recovery: if the test is exact at every word longer than the
current prefix, the procedure returns the prefix of the atom of the target length. -/
theorem run_bitRec (test : ℝ → Prop) {h : Guide} {x : Str n} :
    ∀ (m : ℕ) (u : List Bool), IsPre u x → u.length + m ≤ n →
      (∀ v : List Bool, u.length < v.length → v.length ≤ n → (test (h v) ↔ IsPre v x)) →
      (bitRec test u m).run h = PMF.pure (pre x (u.length + m))
  | 0, u, hu, _, _ => by
      simp only [bitRec, Alg.run_ret, add_zero]
      rw [← isPre_iff_pre.mp hu]
  | m + 1, u, hu, hlen, htest => by
      simp only [bitRec, Alg.run_query]
      have hl0 : (u ++ [false]).length = u.length + 1 := by simp
      have hl1 : (u ++ [true]).length = u.length + 1 := by simp
      have htest' : ∀ b : Bool, ∀ v : List Bool, (u ++ [b]).length < v.length →
          v.length ≤ n → (test (h v) ↔ IsPre v x) := fun b v hv hvn =>
        htest v (by simp at hv; omega) hvn
      by_cases hf : IsPre (u ++ [false]) x
      · have ht : test (h (u ++ [false])) := (htest _ (by simp) (by simp; omega)).2 hf
        simp only [ht, ite_true]
        rw [run_bitRec test m _ hf (by rw [hl0]; omega) (htest' false), hl0]
        congr 2
        omega
      · have ht : ¬ test (h (u ++ [false])) := fun ht =>
          hf ((htest _ (by simp) (by simp; omega)).1 ht)
        simp only [ht, ite_false]
        have h1 := isPre_append_true_of_not_false hu (by omega) hf
        rw [run_bitRec test m _ h1 (by rw [hl1]; omega) (htest' true), hl1]
        congr 2
        omega

/-! ### Balanced prefix tests -/

/-- The number of candidates of `T` below the word `v`. -/
def cnt (T : Finset (Str n)) (v : List Bool) : ℕ := (T.filter (IsPre v)).card

/-- `v` is a balanced prefix for the candidates `T` inside the group `g`: a descendant of `g`
containing more than `N/3` and at most `2N/3` of the `N` candidates. -/
def Bal (g : List Bool) (T : Finset (Str n)) (v : List Bool) : Prop :=
  g <+: v ∧ v.length ≤ n ∧ T.card < 3 * cnt T v ∧ 3 * cnt T v ≤ 2 * T.card

theorem cnt_children (T : Finset (Str n)) {u : List Bool} (hu : u.length < n) :
    cnt T u = cnt T (u ++ [false]) + cnt T (u ++ [true]) := by
  unfold cnt
  rw [← Finset.card_filter_add_card_filter_not
    (s := T.filter (IsPre u)) (fun y : Str n => y ⟨u.length, hu⟩ = false)]
  have hx : ∀ y : Str n, (List.ofFn y)[u.length]? = some (y ⟨u.length, hu⟩) := by
    intro y; simp [hu]
  congr 1
  · congr 1
    ext y
    simp only [Finset.mem_filter, isPre_append_singleton, hx, Option.some.injEq]
    tauto
  · congr 1
    ext y
    simp only [Finset.mem_filter, isPre_append_singleton, hx, Option.some.injEq,
      Bool.not_eq_false]
    tauto

theorem cnt_le_one (T : Finset (Str n)) {u : List Bool} (hu : n ≤ u.length) : cnt T u ≤ 1 := by
  unfold cnt
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  have h1 : u = List.ofFn a := ha.2.eq_of_length (by have := ha.2.length_le; simp; omega)
  have h2 : u = List.ofFn b := hb.2.eq_of_length (by have := hb.2.length_le; simp; omega)
  exact List.ofFn_injective (h1.symm.trans h2)

theorem cnt_le_card (T : Finset (Str n)) (v : List Bool) : cnt T v ≤ T.card :=
  Finset.card_filter_le _ _

/-- The walk along largest children: from a descendant `u` of the group with more than `N/3`
candidates there is a balanced descendant. -/
theorem exists_bal_aux {g : List Bool} {T : Finset (Str n)} (h2 : 2 ≤ T.card) :
    ∀ (j : ℕ) (u : List Bool), n - u.length = j → g <+: u → u.length ≤ n →
      T.card < 3 * cnt T u → ∃ v, Bal g T v := by
  intro j
  induction j with
  | zero =>
      intro u hj hgu hun hc
      refine ⟨u, hgu, hun, hc, ?_⟩
      have := cnt_le_one T (u := u) (by omega)
      omega
  | succ j ih =>
      intro u hj hgu hun hc
      by_cases hb : 3 * cnt T u ≤ 2 * T.card
      · exact ⟨u, hgu, hun, hc, hb⟩
      · have hlt : u.length < n := by omega
        have hsplit := cnt_children T hlt
        have hpre : ∀ b : Bool, g <+: u ++ [b] := fun b => hgu.trans (List.prefix_append _ _)
        rcases le_total (cnt T (u ++ [true])) (cnt T (u ++ [false])) with hle | hle
        · exact ih (u ++ [false]) (by simp; omega) (hpre false) (by simp; omega) (by omega)
        · exact ih (u ++ [true]) (by simp; omega) (hpre true) (by simp; omega) (by omega)

/-- `prop:arbitrary-locations`: some descendant prefix of the group contains between `N/3` and
`2N/3` of the `N ≥ 2` remaining candidates. -/
theorem exists_bal {g : List Bool} (hg : g.length ≤ n) {T : Finset (Str n)}
    (hT : ∀ y ∈ T, IsPre g y) (h2 : 2 ≤ T.card) : ∃ v, Bal g T v := by
  have hcg : cnt T g = T.card := by
    unfold cnt
    rw [Finset.filter_true_of_mem hT]
  exact exists_bal_aux h2 _ g rfl List.prefix_rfl hg (by omega)

open Classical in
/-- A balanced prefix for `T` inside the group `g` (the group itself if none exists). -/
noncomputable def balPre (g : List Bool) (T : Finset (Str n)) : List Bool :=
  if hb : ∃ v, Bal g T v then Classical.choose hb else g

/-- Some element of `T` (an arbitrary string if `T` is empty). -/
noncomputable def pick (T : Finset (Str n)) : Str n :=
  if hT : T.Nonempty then hT.choose else fun _ => false

theorem pick_eq {T : Finset (Str n)} {x : Str n} (hx : x ∈ T) (h1 : T.card ≤ 1) : pick T = x := by
  have hne : T.Nonempty := ⟨x, hx⟩
  rw [pick, dite_eq_left hne]
  exact Finset.card_le_one.mp h1 _ hne.choose_spec _ hx

open Classical in
/-- Recovery by balanced prefix tests inside the group `g`, with at most `m` queries: while at
least two candidates remain, query a balanced prefix and retain the side indicated by the test. -/
noncomputable def balRec (g : List Bool) (test : ℝ → Prop) : Finset (Str n) → ℕ → Alg (Str n)
  | T, 0 => .ret (pick T)
  | T, m + 1 =>
      if T.card ≤ 1 then .ret (pick T)
      else
        .query (balPre g T) fun r =>
          if test r then balRec g test (T.filter (IsPre (balPre g T))) m
          else balRec g test (T.filter fun y => ¬ IsPre (balPre g T) y) m

theorem within_balRec (g : List Bool) (test : ℝ → Prop) (h : Guide) :
    ∀ (T : Finset (Str n)) (m : ℕ), (balRec g test T m).Within h m
  | T, 0 => Alg.Within.ret _ _
  | T, m + 1 => by
      unfold balRec
      split_ifs with hT
      · exact Alg.Within.ret _ _
      · refine Alg.Within.query _ _ _ ?_
        by_cases ht : test (h (balPre g T))
        · simp only [ht, ite_true]
          exact within_balRec g test h _ m
        · simp only [ht, ite_false]
          exact within_balRec g test h _ m

/-- `prop:arbitrary-locations`, correctness of balanced recovery: if the test is exact at every
descendant of the group, the atom is a candidate, all candidates lie in the group, and
`2^m N < 2·3^m` for the number `N` of candidates, then the procedure outputs the atom. -/
theorem run_balRec {g : List Bool} (hg : g.length ≤ n) (test : ℝ → Prop) {h : Guide}
    {x : Str n} (htest : ∀ v : List Bool, g <+: v → v.length ≤ n → (test (h v) ↔ IsPre v x)) :
    ∀ (m : ℕ) (T : Finset (Str n)), x ∈ T → (∀ y ∈ T, IsPre g y) →
      2 ^ m * T.card < 2 * 3 ^ m → (balRec g test T m).run h = PMF.pure x
  | 0, T, hx, _, hcard => by
      simp only [balRec, Alg.run_ret]
      rw [pick_eq hx (by simpa using hcard)]
  | m + 1, T, hx, hT, hcard => by
      unfold balRec
      by_cases h1 : T.card ≤ 1
      · rw [ite_eq_left h1, Alg.run_ret, pick_eq hx h1]
      · rw [ite_eq_right h1, Alg.run_query]
        have h2 : 2 ≤ T.card := by omega
        have hex := exists_bal hg hT h2
        have hb : Bal g T (balPre g T) := by
          rw [balPre, dite_eq_left hex]
          exact Classical.choose_spec hex
        obtain ⟨hgv, hvn, hlo, hhi⟩ := hb
        have hsum := Finset.card_filter_add_card_filter_not (s := T)
          (IsPre (balPre g T))
        have hstep : ∀ T' : Finset (Str n), 3 * T'.card ≤ 2 * T.card →
            2 ^ m * T'.card < 2 * 3 ^ m := by
          intro T' hT'
          refine Nat.lt_of_mul_lt_mul_left (a := 3) ?_
          calc 3 * (2 ^ m * T'.card) = 2 ^ m * (3 * T'.card) := by ring
            _ ≤ 2 ^ m * (2 * T.card) := Nat.mul_le_mul_left _ hT'
            _ = 2 ^ (m + 1) * T.card := by ring
            _ < 2 * 3 ^ (m + 1) := hcard
            _ = 3 * (2 * 3 ^ m) := by ring
        by_cases hv : IsPre (balPre g T) x
        · have ht : test (h (balPre g T)) := (htest _ hgv hvn).2 hv
          rw [ite_eq_left ht]
          refine run_balRec hg test htest m _ (Finset.mem_filter.mpr ⟨hx, hv⟩)
            (fun y hy => hT y (Finset.mem_filter.mp hy).1) (hstep _ hhi)
        · have ht : ¬ test (h (balPre g T)) := fun ht => hv ((htest _ hgv hvn).1 ht)
          rw [ite_eq_right ht]
          refine run_balRec hg test htest m _ (Finset.mem_filter.mpr ⟨hx, hv⟩)
            (fun y hy => hT y (Finset.mem_filter.mp hy).1) (hstep _ ?_)
          change cnt T (balPre g T) + _ = _ at hsum
          omega

/-- With `t = ⌈log_{3/2} N⌉` queries, `(3/2)^t ≥ N`. -/
theorem le_pow_ceil_logb {N : ℝ} (hN : 1 ≤ N) :
    N ≤ (3 / 2 : ℝ) ^ ⌈Real.logb (3 / 2) N⌉₊ := by
  have hpos : (0 : ℝ) < N := by linarith
  calc N = (3 / 2 : ℝ) ^ Real.logb (3 / 2) N :=
        (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
    _ ≤ (3 / 2 : ℝ) ^ (⌈Real.logb (3 / 2) N⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = (3 / 2 : ℝ) ^ ⌈Real.logb (3 / 2) N⌉₊ := Real.rpow_natCast _ _

/-- `prop:arbitrary-locations`: the fuel `⌈log_{3/2} N⌉` suffices for at most `N` candidates. -/
theorem fuel_ok {N : ℝ} (hN : 1 ≤ N) {T : Finset (Str n)} (hT : (T.card : ℝ) ≤ N) :
    2 ^ ⌈Real.logb (3 / 2) N⌉₊ * T.card < 2 * 3 ^ ⌈Real.logb (3 / 2) N⌉₊ := by
  set t := ⌈Real.logb (3 / 2) N⌉₊
  have h1 := le_pow_ceil_logb hN
  have h3 : (0 : ℝ) < 3 ^ t := by positivity
  have h2 : ((2 : ℝ) ^ t * T.card) < 2 * 3 ^ t := by
    calc (2 : ℝ) ^ t * T.card ≤ 2 ^ t * N := by gcongr
      _ ≤ 2 ^ t * (3 / 2) ^ t := by gcongr
      _ = 3 ^ t := by rw [← mul_pow]; norm_num
      _ < 2 * 3 ^ t := by linarith
  exact_mod_cast h2

end LearningGuided.Sec3
