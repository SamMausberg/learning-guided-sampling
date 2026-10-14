import LearningGuided.PointwiseLB.Oracle

/-!
# The first-failure batch oracle and the simulation of prefix queries

The stronger oracle of Definition `pw-def:batch` is modelled by *test trees* (`TT`): adaptive
randomized procedures whose only access to the hidden tables is the elementary test of a guess
`I_{a,j} = i`, which reports failure, or success together with the label `Y_{a,j}`. A batch
(`batch`) tests an ordered list of guesses in one table, stops at the first failure, and reports
all labels if every guess succeeds. The cost of a test tree is its number of failures, which is
at most its number of batches.

Lemma `pw-lem:simulation`: every query to `h_θ` (including complete strings and words of any
length) is answered by one batch with no other access to the instance: `h_θ(u)` is a public
coefficient times a product of factors `[I_{a,j} = i] (1 + Y_{a,j}/2)` over the guesses
demanded by `u` (`oracle_factor`). Consequently every algorithm `A` is converted into a test
tree `conv A` with the same output law against every instance (`run_conv`) and with at most as
many failures as `A` has queries (`within_conv`).
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm)

/-! ### Symbolic factors of the oracle -/

/-- A guess `I_{a,j} = i` (the table `a` is fixed by the query's root bit). -/
abbrev Guess := Str P.k × Fin P.ℓ

/-- The value of a guess: `[I_{a,j} = i] (1 + Y_{a,j}/2)`. -/
noncomputable def gval (T : P.Tables) (a : Bool) (g : P.Guess) : ℝ :=
  if T.1 a g.1 = g.2 then 1 + yv (T.2 a g.1) / 2 else 0

/-- The value of an optional guess (`1` if there is none). -/
noncomputable def ogval (T : P.Tables) (a : Bool) : Option P.Guess → ℝ
  | none => 1
  | some g => P.gval T a g

/-- Public coefficient of a complete block. -/
noncomputable def wCoef (z : List Bool) : ℝ :=
  if z.drop P.k = P.cstr then 1 else if ∃ i : Fin P.ℓ, z.drop P.k = P.stair i then 1 else 0

open Classical in
/-- The guess demanded by a complete block `(j, s_i)`. -/
noncomputable def wGuess (z : List Bool) : Option P.Guess :=
  if h : z.drop P.k ≠ P.cstr ∧ ∃ i : Fin P.ℓ, z.drop P.k = P.stair i then
    some (P.toRow z, Classical.choose h.2)
  else none

/-- The pattern `1^i 0^{m-i}`. -/
def pat (m i : ℕ) : List Bool := List.replicate i true ++ List.replicate (m - i) false

/-- Public coefficient of the local factor `g_a(j,s)`. -/
noncomputable def gCoef (s : List Bool) : ℝ :=
  if s = List.replicate s.length true then 3 / 2
  else if ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧ s = pat s.length i then 1 else 0

open Classical in
/-- The guess demanded by a partial block `(j, 1^i 0^{|s|-i})`. -/
noncomputable def gGuess (j : Str P.k) (s : List Bool) : Option P.Guess :=
  if h : s ≠ List.replicate s.length true ∧
      ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧ s = pat s.length i then
    some (j, Classical.choose h.2)
  else none

theorem w_factor (T : P.Tables) (a : Bool) (z : List Bool) :
    P.w T a z = P.wCoef z * P.ogval T a (P.wGuess z) := by
  unfold w wCoef wGuess
  by_cases h1 : z.drop P.k = P.cstr
  · simp [h1, ogval]
  · by_cases h2 : ∃ i : Fin P.ℓ, z.drop P.k = P.stair i
    · have hh : z.drop P.k ≠ P.cstr ∧ ∃ i : Fin P.ℓ, z.drop P.k = P.stair i := ⟨h1, h2⟩
      rw [dite_eq_left hh, ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, one_mul]
      simp only [ogval, gval]
      have hc := Classical.choose_spec hh.2
      generalize Classical.choose hh.2 = i₀ at hc ⊢
      have hiff : z.drop P.k = P.stair (T.1 a (P.toRow z)) ↔ T.1 a (P.toRow z) = i₀ := by
        rw [hc]
        constructor
        · intro h; exact (Fin.ext (P.stair_injective (Fin.isLt _).le (Fin.isLt _).le h)).symm
        · intro h; rw [h]
      by_cases h3 : T.1 a (P.toRow z) = i₀
      · rw [ite_eq_left (hiff.mpr h3), ite_eq_left h3]
      · rw [ite_eq_right (mt hiff.mp h3), ite_eq_right h3]
    · have hh : ¬ (z.drop P.k ≠ P.cstr ∧ ∃ i : Fin P.ℓ, z.drop P.k = P.stair i) :=
        fun h => h2 h.2
      rw [dite_eq_right hh, ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, zero_mul]
      rw [ite_eq_right (fun h => h2 ⟨_, h⟩)]

theorem pat_getElem? {m i q : ℕ} (hi : i ≤ m) (hq : q < m) :
    (pat m i)[q]? = some (decide (q < i)) := by
  unfold pat
  by_cases h : q < i
  · rw [List.getElem?_append_left (by simpa using h)]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    have : q - (List.replicate i true).length < m - i := by simp; omega
    simp only [List.getElem?_replicate, this, h]
    simp

theorem pat_injective {m i i' : ℕ} (hi : i < m) (hi' : i' < m) (h : pat m i = pat m i') :
    i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := pat_getElem? hi.le (q := i) hi
    rw [h, pat_getElem? hi'.le hi] at h1
    simp [hlt] at h1
  · have h1 := pat_getElem? hi.le (q := i') hi'
    rw [h, pat_getElem? hi'.le hi'] at h1
    simp [hlt] at h1

theorem gloc_factor (T : P.Tables) (a : Bool) (j : Str P.k) (s : List Bool) :
    P.gloc T a j s = P.gCoef s * P.ogval T a (P.gGuess j s) := by
  unfold gloc gCoef gGuess
  by_cases h1 : s = List.replicate s.length true
  · rw [ite_eq_left h1, ite_eq_left h1, dite_eq_right (fun h => h.1 h1)]; simp [ogval]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧ s = pat s.length i
    · have hh : s ≠ List.replicate s.length true ∧
          ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧ s = pat s.length i := ⟨h1, h2⟩
      rw [dite_eq_left hh, ite_eq_left h2, one_mul]
      simp only [ogval, gval]
      obtain ⟨hc1, hc2⟩ := Classical.choose_spec hh.2
      have hiff : (∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧
          s = List.replicate i true ++ List.replicate (s.length - i) false ∧ T.1 a j = i) ↔
          T.1 a j = Classical.choose hh.2 := by
        constructor
        · rintro ⟨i, hi, hs, rfl⟩
          exact Fin.ext (pat_injective hi hc1 (hs.symm.trans hc2))
        · intro h; exact ⟨_, hc1, hc2, h⟩
      by_cases h3 : T.1 a j = Classical.choose hh.2
      · rw [ite_eq_left (hiff.mpr h3), ite_eq_left h3]
      · rw [ite_eq_right (mt hiff.mp h3), ite_eq_right h3]
    · have hh : ¬ (s ≠ List.replicate s.length true ∧
          ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧ s = pat s.length i) := fun h => h2 h.2
      rw [dite_eq_right hh, ite_eq_right h2, zero_mul]
      rw [ite_eq_right]
      rintro ⟨i, hi, hs, -⟩
      exact h2 ⟨i, hi, hs⟩

/-- The root bit of a query (irrelevant for the root and for words without guesses). -/
def root : List Bool → Bool
  | [] => false
  | a :: _ => a

/-- The optional tail factor guess of a nonempty query. -/
noncomputable def tailGuess (rest : List Bool) : Option P.Guess :=
  if P.part rest = [] then none
  else if (P.part rest).length < P.k then none
  else P.gGuess (P.toRow (P.part rest)) ((P.part rest).drop P.k)

/-- The public tail coefficient of a nonempty query. -/
noncomputable def tailCoef (rest : List Bool) : ℝ :=
  if P.part rest = [] then P.Acirc ^ (P.r - P.nb rest) / P.Z
  else if (P.part rest).length < P.k then
    9 / 4 * 2 ^ (P.k - (P.part rest).length) * P.Acirc ^ (P.r - P.nb rest - 1) / P.Z
  else P.gCoef ((P.part rest).drop P.k) * P.Acirc ^ (P.r - P.nb rest - 1) / P.Z

/-- The guesses demanded by a query (`pw-lem:simulation`). -/
noncomputable def guesses : List Bool → List P.Guess
  | [] => []
  | _ :: rest =>
      if P.r * P.d < rest.length then []
      else (List.range (P.nb rest)).filterMap (fun b => P.wGuess (P.blk rest b)) ++
        (P.tailGuess rest).toList

/-- The public coefficient of a query (`pw-lem:simulation`). -/
noncomputable def qcoef : List Bool → ℝ
  | [] => 1
  | _ :: rest =>
      if P.r * P.d < rest.length then 0
      else (∏ b ∈ Finset.range (P.nb rest), P.wCoef (P.blk rest b)) * P.tailCoef rest

/-- `pw-lem:simulation`, batch length: a query demands at most `r` guesses (a nonempty partial
block leaves at most `r - 1` complete blocks). -/
theorem length_guesses_le (u : List Bool) : (P.guesses u).length ≤ P.r := by
  cases u with
  | nil => simp [guesses]
  | cons a rest =>
      simp only [guesses]
      by_cases hl : P.r * P.d < rest.length
      · simp [hl]
      · rw [ite_eq_right hl, List.length_append]
        have h1 : ((List.range (P.nb rest)).filterMap
            (fun b => P.wGuess (P.blk rest b))).length ≤ P.nb rest :=
          (List.length_filterMap_le _ _).trans (by simp)
        have hle := P.length_eq_nb rest
        unfold tailGuess
        by_cases h0 : P.part rest = []
        · rw [ite_eq_left h0]
          have : P.nb rest * P.d ≤ P.r * P.d := by omega
          have := Nat.le_of_mul_le_mul_right this P.d_pos
          simp only [Option.toList_none, List.length_nil]; omega
        · have hpos : 0 < (P.part rest).length := List.length_pos_iff.mpr h0
          have : P.nb rest * P.d < P.r * P.d := by omega
          have := Nat.lt_of_mul_lt_mul_right this
          rw [ite_eq_right h0]
          have h2 : (Option.toList (if (P.part rest).length < P.k then none
              else P.gGuess (P.toRow (P.part rest)) ((P.part rest).drop P.k))).length ≤ 1 := by
            split_ifs
            · simp
            · cases P.gGuess (P.toRow (P.part rest)) ((P.part rest).drop P.k) <;> simp
          omega

theorem prod_filterMap_gval (T : P.Tables) (a : Bool) {α : Type} (o : α → Option P.Guess)
    (l : List α) :
    ((l.filterMap o).map (P.gval T a)).prod = (l.map fun x => P.ogval T a (o x)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      cases h : o x with
      | none => simp [h, ih, ogval]
      | some g => simp [h, ih, ogval]

theorem finset_prod_range_eq_list {M : Type} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∏ b ∈ Finset.range t, f b = ((List.range t).map f).prod := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.prod_range_succ, ih, List.range_succ, List.map_append,
      List.prod_append]; simp

/-- `pw-lem:simulation` (factorization): every oracle answer is a public coefficient times the
product of the values of the demanded guesses, all in the table of the query's root bit. -/
theorem oracle_factor (T : P.Tables) (u : List Bool) :
    P.oracle T u = P.qcoef u * ((P.guesses u).map (P.gval T (root u))).prod := by
  cases u with
  | nil => simp [oracle, qcoef, guesses]
  | cons a rest =>
      simp only [oracle, qcoef, guesses, root]
      by_cases hl : P.r * P.d < rest.length
      · simp [hl]
      · rw [ite_eq_right hl, ite_eq_right hl, ite_eq_right hl, List.map_append,
          List.prod_append, prod_filterMap_gval, ← finset_prod_range_eq_list]
        have hPw : P.Pw T a rest = (∏ b ∈ Finset.range (P.nb rest), P.wCoef (P.blk rest b)) *
            ∏ b ∈ Finset.range (P.nb rest), P.ogval T a (P.wGuess (P.blk rest b)) := by
          unfold Pw; rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun b _ => P.w_factor T a _
        rw [hPw]
        unfold tailCoef tailGuess
        by_cases h0 : P.part rest = []
        · simp only [ite_eq_left h0]; simp; ring
        · simp only [ite_eq_right h0]
          by_cases hk : (P.part rest).length < P.k
          · simp only [ite_eq_left hk]; simp; ring
          · simp only [ite_eq_right hk]
            rw [P.gloc_factor]
            cases P.gGuess (P.toRow (P.part rest)) ((P.part rest).drop P.k) with
            | none => simp [ogval]; ring
            | some g => simp [ogval]; ring

end Prm

/-! ### Test trees -/

/-- Adaptive randomized procedures against the elementary test oracle: return, draw from a
known law, or test a guess `I_{a,j} = i` and continue on failure or on success with the
reported label `Y_{a,j}`. -/
inductive TT (P : Prm) (β : Type) : Type 1 where
  /-- Return a known value. -/
  | ret : β → TT P β
  /-- Draw from a known law. -/
  | sample {γ : Type} : PMF γ → (γ → TT P β) → TT P β
  /-- Test the guess `I_{a,j} = i`: continue with `kf` on failure, or with `ks Y_{a,j}` on
  success. -/
  | test : Bool → Str P.k → Fin P.ℓ → TT P β → (Bool → TT P β) → TT P β

namespace TT

variable {P : Prm} {β : Type}

/-- The output law of a test tree against the hidden tables `T`. -/
noncomputable def run (T : P.Tables) : TT P β → PMF β
  | ret b => PMF.pure b
  | sample p k => p.bind fun g => run T (k g)
  | test a j i kf ks => if T.1 a j = i then run T (ks (T.2 a j)) else run T kf

/-- `Within T t q`: every execution of `t` against `T` with positive probability has at most
`q` failed tests. -/
def Within (T : P.Tables) : TT P β → ℕ → Prop
  | ret _, _ => True
  | sample p k, q => ∀ g ∈ p.support, Within T (k g) q
  | test a j i kf ks, q =>
      if T.1 a j = i then Within T (ks (T.2 a j)) q else ∃ q', q = q' + 1 ∧ Within T kf q'

theorem Within.mono {T : P.Tables} {t : TT P β} {q q' : ℕ} (h : Within T t q) (hq : q ≤ q') :
    Within T t q' := by
  induction t generalizing q q' with
  | ret b => trivial
  | sample p k ih => exact fun g hg => ih g (h g hg) hq
  | test a j i kf ks ihf ihs =>
      simp only [Within] at h ⊢
      split_ifs with hc
      · rw [ite_eq_left hc] at h; exact ihs _ h hq
      · rw [ite_eq_right hc] at h
        obtain ⟨r, rfl, hr⟩ := h
        exact ⟨q' - 1, by omega, ihf hr (by omega)⟩

/-- `pw-def:batch`: the first-failure batch; test the guesses of table `a` in
order; the first failure ends the batch (continuation `kf`); if all succeed, all labels are
reported (continuation `ks`). -/
def batch (a : Bool) : List P.Guess → TT P β → (List Bool → TT P β) → TT P β
  | [], _, ks => ks []
  | g :: gs, kf, ks => test a g.1 g.2 kf (fun y => batch a gs kf (fun ys => ks (y :: ys)))

open Classical in
theorem run_batch (T : P.Tables) (a : Bool) (gs : List P.Guess) (kf : TT P β)
    (ks : List Bool → TT P β) :
    run T (batch a gs kf ks) =
      if ∀ g ∈ gs, T.1 a g.1 = g.2 then run T (ks (gs.map fun g => T.2 a g.1)) else run T kf := by
  induction gs generalizing ks with
  | nil => simp [batch]
  | cons g gs ih =>
      simp only [batch, run]
      by_cases hg : T.1 a g.1 = g.2
      · rw [ite_eq_left hg, ih]
        simp [hg]
      · rw [ite_eq_right hg]
        simp [hg]

open Classical in
theorem within_batch (T : P.Tables) (a : Bool) (gs : List P.Guess) (kf : TT P β)
    (ks : List Bool → TT P β) (q : ℕ)
    (hs : (∀ g ∈ gs, T.1 a g.1 = g.2) → Within T (ks (gs.map fun g => T.2 a g.1)) q)
    (hf : ¬ (∀ g ∈ gs, T.1 a g.1 = g.2) → ∃ q', q = q' + 1 ∧ Within T kf q') :
    Within T (batch a gs kf ks) q := by
  induction gs generalizing ks with
  | nil => exact hs (by simp)
  | cons g gs ih =>
      simp only [batch, Within]
      by_cases hg : T.1 a g.1 = g.2
      · rw [ite_eq_left hg]
        apply ih
        · intro h; exact hs (List.forall_mem_cons.mpr ⟨hg, h⟩)
        · intro h; exact hf (fun hall => h (List.forall_mem_cons.mp hall).2)
      · rw [ite_eq_right hg]
        exact hf (by simp [hg])

end TT

namespace Prm

variable (P : Prm) {β : Type}

/-- The answer computed from the labels of a fully successful batch. -/
noncomputable def ansOf (u : List Bool) (ys : List Bool) : ℝ :=
  P.qcoef u * (ys.map fun y => 1 + yv y / 2).prod

/-- The conversion of an algorithm into a test tree: each query `u` becomes one batch of the
guesses demanded by `u` (`pw-lem:simulation`). -/
noncomputable def conv : Alg β → TT P β
  | .ret b => .ret b
  | .sample p k => .sample p fun g => conv (k g)
  | .query u k =>
      TT.batch (root u) (P.guesses u) (conv (k 0)) fun ys => conv (k (P.ansOf u ys))

theorem oracle_of_all (T : P.Tables) (u : List Bool)
    (h : ∀ g ∈ P.guesses u, T.1 (root u) g.1 = g.2) :
    P.ansOf u ((P.guesses u).map fun g => T.2 (root u) g.1) = P.oracle T u := by
  rw [oracle_factor, ansOf, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro g hg
  simp [gval, h g hg]

theorem oracle_of_not_all (T : P.Tables) (u : List Bool)
    (h : ¬ ∀ g ∈ P.guesses u, T.1 (root u) g.1 = g.2) : P.oracle T u = 0 := by
  rw [oracle_factor]
  push Not at h
  obtain ⟨g, hg, hne⟩ := h
  have : P.gval T (root u) g = 0 := by simp [gval, hne]
  rw [List.prod_eq_zero (List.mem_map.mpr ⟨g, hg, this⟩), mul_zero]

/-- `pw-lem:simulation`: against every instance, the converted test tree has exactly the output
law of the algorithm run against `h_θ`. -/
theorem run_conv (T : P.Tables) (A : Alg β) : (P.conv A).run T = A.run (P.oracle T) := by
  classical
  induction A with
  | ret b => rfl
  | sample p k ih =>
      simp only [conv, TT.run, Alg.run_sample]
      congr 1; funext g; exact ih g
  | query u k ih =>
      simp only [conv, Alg.run_query]
      rw [TT.run_batch]
      split_ifs with h
      · rw [ih, P.oracle_of_all T u h]
      · rw [ih, P.oracle_of_not_all T u h]

/-- `pw-lem:simulation`, cost: an algorithm with cap `q` against `h_θ` becomes a test tree
with at most `q` failures (one batch per query, at most one failure per batch). -/
theorem within_conv (T : P.Tables) (A : Alg β) :
    ∀ q, A.Within (P.oracle T) q → (P.conv A).Within T q := by
  classical
  induction A with
  | ret b => intro q _; trivial
  | sample p k ih =>
      intro q hq
      exact fun g hg => ih g q (Alg.within_sample_iff.mp hq g hg)
  | query u k ih =>
      intro q hq
      obtain ⟨q', rfl, hq'⟩ := Alg.within_query_iff.mp hq
      apply TT.within_batch
      · intro h
        rw [P.oracle_of_all T u h]
        exact (ih _ q' hq').mono (Nat.le_succ q')
      · intro h
        rw [← P.oracle_of_not_all T u h]
        exact ⟨q', rfl, ih _ q' hq'⟩

end Prm

end LearningGuided.PointwiseLB
