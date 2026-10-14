import LearningGuided.PointwiseLB.TestTree

/-!
# Enhanced transcripts and the conditional law (Lemma `pw-lem:posterior`)

The information revealed by the elementary tests is summarized by a *state*: for each row
`(a, j)` either it is *discovered* (its location `i` and label `y` were reported by a successful
test), or it is undiscovered with a set `E` of excluded locations (failed tests). The set of
tables consistent with a state is a product set, and this file proves the two counting facts of
Lemma `pw-lem:posterior` for the hard prior (uniform on the valid tables with root `B = b`):

* `card_fiber` (locations): for an undiscovered row with `f = |E|` excluded locations, each of
  the `ℓ - f` remaining locations carries the same number of consistent tables, so the location
  is uniform on the remaining locations;
* `card_label` (labels): given the location of a fresh row, the number of consistent tables
  with label one at that row, times the number `W - t_a` of undiscovered rows of the table,
  equals the number of all of them times `m_{a,b} - s_a`, where `t_a` labels of table `a` were
  exposed, `s_a` of them equal to one. So the label is one with probability
  `(m_{a,b} - s_a)/(W - t_a)`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-- The status of a row in an enhanced transcript. -/
inductive RowSt (ℓ : ℕ) : Type where
  /-- Discovered, with its location and label. -/
  | disc : Fin ℓ → Bool → RowSt ℓ
  /-- Undiscovered, with the set of excluded locations. -/
  | undisc : Finset (Fin ℓ) → RowSt ℓ

namespace RowSt

variable {ℓ : ℕ}

/-- `1` for a discovered row. -/
def discN : RowSt ℓ → ℕ
  | disc _ _ => 1
  | undisc _ => 0

/-- `1` for a discovered row with label one. -/
def oneN : RowSt ℓ → ℕ
  | disc _ y => if y then 1 else 0
  | undisc _ => 0

/-- The number of excluded locations of an undiscovered row. -/
def exclN : RowSt ℓ → ℕ
  | disc _ _ => 0
  | undisc E => E.card

/-- Consistency of a location and a label with a row status. -/
def Cons : RowSt ℓ → Fin ℓ → Bool → Prop
  | disc i₀ y₀, i, y => i = i₀ ∧ y = y₀
  | undisc E, i, _ => i ∉ E

instance (st : RowSt ℓ) (i : Fin ℓ) (y : Bool) : Decidable (st.Cons i y) := by
  cases st <;> unfold Cons <;> infer_instance

theorem discN_le_one (st : RowSt ℓ) : st.discN ≤ 1 := by cases st <;> simp [discN]

theorem oneN_le_discN (st : RowSt ℓ) : st.oneN ≤ st.discN := by
  cases st with
  | disc i y => cases y <;> simp [oneN, discN]
  | undisc E => simp [oneN, discN]

end RowSt

namespace Prm

variable (P : Prm)

/-- An enhanced-transcript state. -/
abbrev State := Bool → Str P.k → RowSt P.ℓ

/-- The initial state: nothing discovered, nothing excluded. -/
def σ0 : P.State := fun _ _ => .undisc ∅

/-- Replace the status of row `(a, j)`. -/
def upd (σ : P.State) (a : Bool) (j : Str P.k) (st : RowSt P.ℓ) : P.State :=
  Function.update σ a (Function.update (σ a) j st)

/-- Record a successful test with label `y` at row `(a, j)`, location `i`. -/
def setDisc (σ : P.State) (a : Bool) (j : Str P.k) (i : Fin P.ℓ) (y : Bool) : P.State :=
  P.upd σ a j (.disc i y)

/-- Record a failed fresh test of location `i` at the undiscovered row `(a, j)` with excluded
set `E`. -/
def setExcl (σ : P.State) (a : Bool) (j : Str P.k) (E : Finset (Fin P.ℓ)) (i : Fin P.ℓ) :
    P.State :=
  P.upd σ a j (.undisc (insert i E))

theorem upd_apply (σ : P.State) (a : Bool) (j : Str P.k) (st : RowSt P.ℓ) (a' : Bool)
    (j' : Str P.k) : P.upd σ a j st a' j' = if a' = a ∧ j' = j then st else σ a' j' := by
  unfold upd
  by_cases ha : a' = a
  · subst ha; by_cases hj : j' = j
    · subst hj; simp
    · simp [hj]
  · simp [ha]

/-- The number `D` of discovered rows. -/
def D (σ : P.State) : ℕ := ∑ p : Bool × Str P.k, (σ p.1 p.2).discN

/-- The number `t_a` of discovered rows of table `a`. -/
def tA (σ : P.State) (a : Bool) : ℕ := ∑ j, (σ a j).discN

/-- The number `s_a` of discovered rows of table `a` with label one. -/
def sA (σ : P.State) (a : Bool) : ℕ := ∑ j, (σ a j).oneN

/-- The total number of excluded locations of undiscovered rows. -/
def exclSum (σ : P.State) : ℕ := ∑ p : Bool × Str P.k, (σ p.1 p.2).exclN

theorem sum_pairs_upd (f : RowSt P.ℓ → ℕ) (σ : P.State) (a : Bool) (j : Str P.k)
    (st : RowSt P.ℓ) :
    (∑ p : Bool × Str P.k, f (P.upd σ a j st p.1 p.2)) + f (σ a j) =
      (∑ p : Bool × Str P.k, f (σ p.1 p.2)) + f st := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (a, j)),
    ← Finset.add_sum_erase _ (fun p : Bool × Str P.k => f (σ p.1 p.2)) (Finset.mem_univ (a, j))]
  have hrest : ∑ p ∈ Finset.univ.erase (a, j), f (P.upd σ a j st p.1 p.2) =
      ∑ p ∈ Finset.univ.erase (a, j), f (σ p.1 p.2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hne := Finset.ne_of_mem_erase hp
    rw [upd_apply, ite_eq_right]
    rintro ⟨h1, h2⟩; exact hne (Prod.ext h1 h2)
  rw [hrest, upd_apply, ite_eq_left ⟨rfl, rfl⟩]
  ring

theorem sum_row_upd (f : RowSt P.ℓ → ℕ) (σ : P.State) (a : Bool) (j : Str P.k)
    (st : RowSt P.ℓ) (a' : Bool) :
    (∑ j', f (P.upd σ a j st a' j')) + (if a' = a then f (σ a j) else 0) =
      (∑ j', f (σ a' j')) + (if a' = a then f st else 0) := by
  classical
  by_cases ha : a' = a
  · subst ha
    rw [ite_eq_left rfl, ite_eq_left rfl,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ (fun j' => f (σ a' j')) (Finset.mem_univ j)]
    have hrest : ∑ j' ∈ Finset.univ.erase j, f (P.upd σ a' j st a' j') =
        ∑ j' ∈ Finset.univ.erase j, f (σ a' j') := by
      refine Finset.sum_congr rfl fun j' hj' => ?_
      rw [upd_apply, ite_eq_right]
      rintro ⟨-, h2⟩; exact Finset.ne_of_mem_erase hj' h2
    rw [hrest, upd_apply, ite_eq_left ⟨rfl, rfl⟩]
    ring
  · rw [ite_eq_right ha, ite_eq_right ha]
    congr 1
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [upd_apply, ite_eq_right]
    rintro ⟨h1, -⟩; exact ha h1

theorem D_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) (y : Bool) : P.D (P.setDisc σ a j i y) = P.D σ + 1 := by
  have := P.sum_pairs_upd RowSt.discN σ a j (.disc i y)
  rw [hσ] at this
  simp only [RowSt.discN, add_zero] at this
  exact this

theorem D_setExcl {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) : P.D (P.setExcl σ a j E i) = P.D σ := by
  have := P.sum_pairs_upd RowSt.discN σ a j (.undisc (insert i E))
  rw [hσ] at this
  simp only [RowSt.discN, add_zero] at this
  exact this

theorem exclSum_setExcl {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) :
    P.exclSum (P.setExcl σ a j E i) = P.exclSum σ + 1 := by
  have := P.sum_pairs_upd RowSt.exclN σ a j (.undisc (insert i E))
  rw [hσ] at this
  have h1 : (RowSt.undisc E : RowSt P.ℓ).exclN = E.card := rfl
  have h2 : (RowSt.undisc (insert i E) : RowSt P.ℓ).exclN = E.card + 1 := by
    simp [RowSt.exclN, Finset.card_insert_of_notMem hi]
  rw [h1, h2] at this
  unfold exclSum setExcl; omega

theorem exclSum_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) (y : Bool) :
    P.exclSum (P.setDisc σ a j i y) + E.card = P.exclSum σ := by
  have := P.sum_pairs_upd RowSt.exclN σ a j (.disc i y)
  rw [hσ] at this
  simp only [RowSt.exclN, add_zero] at this
  exact this

theorem tA_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) (y : Bool) (a' : Bool) :
    P.tA (P.setDisc σ a j i y) a' = P.tA σ a' + if a' = a then 1 else 0 := by
  have := P.sum_row_upd RowSt.discN σ a j (.disc i y) a'
  rw [hσ] at this
  simp only [RowSt.discN, ite_self, add_zero] at this
  exact this

theorem sA_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) (y : Bool) (a' : Bool) :
    P.sA (P.setDisc σ a j i y) a' = P.sA σ a' + if a' = a ∧ y = true then 1 else 0 := by
  have := P.sum_row_upd RowSt.oneN σ a j (.disc i y) a'
  rw [hσ] at this
  simp only [RowSt.oneN, ite_self, add_zero] at this
  rw [show (if a' = a ∧ y = true then 1 else 0) = if a' = a then (if y then 1 else 0) else 0 by
    by_cases ha : a' = a <;> cases y <;> simp [ha]]
  exact this

theorem tA_le_D (σ : P.State) (a : Bool) : P.tA σ a ≤ P.D σ := by
  unfold tA D
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun a => ∑ j, (σ a j).discN) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)

theorem sA_le_tA (σ : P.State) (a : Bool) : P.sA σ a ≤ P.tA σ a :=
  Finset.sum_le_sum fun j _ => (σ a j).oneN_le_discN

theorem D_le (σ : P.State) : P.D σ ≤ 2 * P.W := by
  unfold D
  calc ∑ p : Bool × Str P.k, (σ p.1 p.2).discN ≤ ∑ _p : Bool × Str P.k, 1 :=
        Finset.sum_le_sum fun p _ => (σ p.1 p.2).discN_le_one
    _ = 2 * P.W := by simp [Fintype.card_prod, P.card_rows]

theorem D_σ0 : P.D P.σ0 = 0 := by simp [D, σ0, RowSt.discN]

theorem exclSum_σ0 : P.exclSum P.σ0 = 0 := by simp [exclSum, σ0, RowSt.exclN]

/-! ### Consistent tables -/

/-- Tables consistent with a state. -/
def Consistent (σ : P.State) (T : P.Tables) : Prop := ∀ a j, (σ a j).Cons (T.1 a j) (T.2 a j)

instance (σ : P.State) (T : P.Tables) : Decidable (P.Consistent σ T) := by
  unfold Consistent; infer_instance

/-- `m_{a,b}`: the number of ones of table `a` when the root is `b`. -/
def mab (b a : Bool) : ℕ := if a = b then P.mPlus else P.mMinus

/-- The valid tables with root `b` that are consistent with `σ` (the support of the hard prior
conditioned on the enhanced transcript). -/
noncomputable def Sb (b : Bool) (σ : P.State) : Finset P.Tables :=
  Finset.univ.filter fun T => P.Valid b T ∧ P.Consistent σ T

/-- The consistent valid tables for either root. -/
noncomputable def Cset (σ : P.State) : Finset P.Tables := P.Sb false σ ∪ P.Sb true σ

theorem ones_valid {b : Bool} {T : P.Tables} (hv : P.Valid b T) (a : Bool) :
    ones (T.2 a) = P.mab b a := by
  unfold mab
  by_cases h : a = b
  · subst h; rw [ite_eq_left rfl]; exact hv.1
  · rw [ite_eq_right h]
    have : a = !b := by cases a <;> cases b <;> simp_all
    subst this; exact hv.2

theorem consistent_split {σ : P.State} {T : P.Tables} (a : Bool) (j : Str P.k) :
    P.Consistent σ T ↔
      (∀ a' j', ¬ (a' = a ∧ j' = j) → (σ a' j').Cons (T.1 a' j') (T.2 a' j')) ∧
        (σ a j).Cons (T.1 a j) (T.2 a j) := by
  constructor
  · intro h; exact ⟨fun a' j' _ => h a' j', h a j⟩
  · rintro ⟨h1, h2⟩ a' j'
    by_cases hc : a' = a ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := hc; exact h2
    · exact h1 a' j' hc

theorem consistent_upd {σ : P.State} {T : P.Tables} {a : Bool} {j : Str P.k}
    {st : RowSt P.ℓ} :
    P.Consistent (P.upd σ a j st) T ↔
      (∀ a' j', ¬ (a' = a ∧ j' = j) → (σ a' j').Cons (T.1 a' j') (T.2 a' j')) ∧
        st.Cons (T.1 a j) (T.2 a j) := by
  rw [P.consistent_split a j]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a' j' hc => ?_, ?_⟩
    · have := h1 a' j' hc; rwa [upd_apply, ite_eq_right hc] at this
    · rwa [upd_apply, ite_eq_left ⟨rfl, rfl⟩] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun a' j' hc => ?_, ?_⟩
    · rw [upd_apply, ite_eq_right hc]; exact h1 a' j' hc
    · rw [upd_apply, ite_eq_left ⟨rfl, rfl⟩]; exact h2

theorem consistent_setExcl {σ : P.State} {T : P.Tables} {a : Bool} {j : Str P.k}
    {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (i : Fin P.ℓ) :
    P.Consistent (P.setExcl σ a j E i) T ↔ P.Consistent σ T ∧ T.1 a j ≠ i := by
  rw [setExcl, consistent_upd, P.consistent_split a j, hσ]
  simp only [RowSt.Cons, Finset.mem_insert, not_or]
  tauto

theorem consistent_setDisc {σ : P.State} {T : P.Tables} {a : Bool} {j : Str P.k}
    {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) (y : Bool) :
    P.Consistent (P.setDisc σ a j i y) T ↔ P.Consistent σ T ∧ T.1 a j = i ∧ T.2 a j = y := by
  rw [setDisc, consistent_upd, P.consistent_split a j, hσ]
  simp only [RowSt.Cons]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by rw [h2]; exact hi⟩, h2, h3⟩
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩

theorem Sb_setExcl {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) :
    P.Sb b (P.setExcl σ a j E i) = (P.Sb b σ).filter fun T => T.1 a j ≠ i := by
  ext T
  simp only [Sb, Finset.mem_filter, Finset.mem_univ, true_and, P.consistent_setExcl hσ]
  tauto

theorem Sb_setDisc {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) (y : Bool) :
    P.Sb b (P.setDisc σ a j i y) = (P.Sb b σ).filter fun T => T.1 a j = i ∧ T.2 a j = y := by
  ext T
  simp only [Sb, Finset.mem_filter, Finset.mem_univ, true_and, P.consistent_setDisc hσ hi]
  tauto

theorem Sb_σ0 (b : Bool) : P.Sb b P.σ0 = Finset.univ.filter fun T => P.Valid b T := by
  ext T
  simp [Sb, Consistent, σ0, RowSt.Cons]

theorem Cset_setExcl {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) {T : P.Tables} (hT : T ∈ P.Cset (P.setExcl σ a j E i)) :
    T ∈ P.Cset σ ∧ T.1 a j ≠ i := by
  unfold Cset at *
  rw [P.Sb_setExcl hσ, P.Sb_setExcl hσ] at hT
  simp only [Finset.mem_union, Finset.mem_filter] at hT ⊢
  tauto

theorem Cset_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) (y : Bool) {T : P.Tables}
    (hT : T ∈ P.Cset (P.setDisc σ a j i y)) : T ∈ P.Cset σ ∧ T.1 a j = i ∧ T.2 a j = y := by
  unfold Cset at *
  rw [P.Sb_setDisc hσ hi, P.Sb_setDisc hσ hi] at hT
  simp only [Finset.mem_union, Finset.mem_filter] at hT ⊢
  tauto

theorem cons_of_mem_Cset {σ : P.State} {T : P.Tables} (hT : T ∈ P.Cset σ) (a : Bool)
    (j : Str P.k) : (σ a j).Cons (T.1 a j) (T.2 a j) := by
  unfold Cset Sb at hT
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  rcases hT with h | h
  · exact h.2 a j
  · exact h.2 a j

/-! ### Locations are uniform on the remaining locations -/

/-- Change the location of row `(a, j)`. -/
def setI (T : P.Tables) (a : Bool) (j : Str P.k) (i : Fin P.ℓ) : P.Tables :=
  (Function.update T.1 a (Function.update (T.1 a) j i), T.2)

theorem setI_fst (T : P.Tables) (a : Bool) (j : Str P.k) (i : Fin P.ℓ) (a' : Bool)
    (j' : Str P.k) : (P.setI T a j i).1 a' j' = if a' = a ∧ j' = j then i else T.1 a' j' := by
  unfold setI
  by_cases ha : a' = a
  · subst ha; by_cases hj : j' = j
    · subst hj; simp
    · simp [hj]
  · simp [ha]

theorem setI_setI (T : P.Tables) (a : Bool) (j : Str P.k) (i i' : Fin P.ℓ) :
    P.setI (P.setI T a j i) a j i' = P.setI T a j i' := by
  apply Prod.ext
  · funext a' j'; simp only [setI_fst]; split_ifs <;> rfl
  · rfl

theorem setI_self (T : P.Tables) (a : Bool) (j : Str P.k) : P.setI T a j (T.1 a j) = T := by
  apply Prod.ext
  · funext a' j'; simp only [setI_fst]; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rfl
  · rfl

theorem setI_mem_Sb {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) {T : P.Tables} (hT : T ∈ P.Sb b σ) :
    P.setI T a j i ∈ P.Sb b σ := by
  unfold Sb at *
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
  refine ⟨hT.1, ?_⟩
  rw [P.consistent_split a j] at hT ⊢
  refine ⟨fun a' j' hc => ?_, ?_⟩
  · rw [setI_fst, ite_eq_right hc]; exact hT.2.1 a' j' hc
  · rw [setI_fst, ite_eq_left ⟨rfl, rfl⟩, hσ]; exact hi

theorem card_fiber_eq {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i i' : Fin P.ℓ} (hi : i ∉ E) (hi' : i' ∉ E) :
    ((P.Sb b σ).filter fun T => T.1 a j = i).card =
      ((P.Sb b σ).filter fun T => T.1 a j = i').card := by
  refine Finset.card_nbij' (fun T => P.setI T a j i') (fun T => P.setI T a j i) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hT ⊢
    exact ⟨P.setI_mem_Sb hσ hi' hT.1, by rw [setI_fst, ite_eq_left ⟨rfl, rfl⟩]⟩
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hT ⊢
    exact ⟨P.setI_mem_Sb hσ hi hT.1, by rw [setI_fst, ite_eq_left ⟨rfl, rfl⟩]⟩
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hT
    change P.setI (P.setI T a j i') a j i = T
    rw [setI_setI, ← hT.2, setI_self]
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hT
    change P.setI (P.setI T a j i) a j i' = T
    rw [setI_setI, ← hT.2, setI_self]

/-- `pw-lem:posterior`, locations: at an undiscovered row with excluded set `E`, every remaining
location carries the same number of consistent tables, so `|S| = (ℓ - |E|) |S ∩ {I_{a,j} = i}|`
and the location is uniform on the `ℓ - |E|` remaining locations. -/
theorem card_fiber {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) :
    (P.Sb b σ).card = (P.ℓ - E.card) * ((P.Sb b σ).filter fun T => T.1 a j = i).card := by
  classical
  have hmaps : ((P.Sb b σ : Finset P.Tables) : Set P.Tables).MapsTo (fun T => T.1 a j)
      (Finset.univ \ E : Finset (Fin P.ℓ)) := by
    intro T hT
    have hc := (Finset.mem_filter.mp hT).2.2 a j
    rw [hσ] at hc
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, true_and,
      Finset.mem_coe]
    exact hc
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [Finset.sum_congr rfl fun i' hi' => P.card_fiber_eq hσ (Finset.mem_sdiff.mp hi').2 hi]
  rw [Finset.sum_const, Finset.card_univ_sdiff, Fintype.card_fin, smul_eq_mul]

/-! ### Labels: sampling without replacement -/

/-- The undiscovered rows of table `a`. -/
def U (σ : P.State) (a : Bool) : Finset (Str P.k) :=
  Finset.univ.filter fun j => (σ a j).discN = 0

theorem card_U (σ : P.State) (a : Bool) : (P.U σ a).card + P.tA σ a = P.W := by
  unfold U tA
  rw [Finset.card_filter, ← Finset.sum_add_distrib, ← P.card_rows, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases σ a j <;> simp [RowSt.discN]

theorem ones_split {b : Bool} {σ : P.State} {T : P.Tables} (hT : T ∈ P.Sb b σ) (a : Bool) :
    ((P.U σ a).filter fun j => T.2 a j = true).card + P.sA σ a = ones (T.2 a) := by
  have hc := (Finset.mem_filter.mp hT).2.2
  unfold U sA ones
  rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcj := hc a j
  cases h : σ a j with
  | disc i₀ y₀ =>
      rw [h] at hcj
      simp only [RowSt.Cons] at hcj
      rw [hcj.2]
      cases y₀ <;> simp [RowSt.discN, RowSt.oneN]
  | undisc E => simp [RowSt.discN, RowSt.oneN]

/-- Exchange the labels of rows `j` and `j'` of table `a`. -/
def swapY (T : P.Tables) (a : Bool) (j j' : Str P.k) : P.Tables :=
  (T.1, Function.update T.2 a fun x => T.2 a (Equiv.swap j j' x))

theorem swapY_snd (T : P.Tables) (a : Bool) (j j' : Str P.k) (a' : Bool) (x : Str P.k) :
    (P.swapY T a j j').2 a' x = if a' = a then T.2 a (Equiv.swap j j' x) else T.2 a' x := by
  unfold swapY
  by_cases h : a' = a
  · subst h; simp
  · simp [h]

theorem swapY_swapY (T : P.Tables) (a : Bool) (j j' : Str P.k) :
    P.swapY (P.swapY T a j j') a j j' = T := by
  apply Prod.ext
  · rfl
  · funext a' x
    by_cases h : a' = a
    · subst h
      rw [swapY_snd, ite_eq_left rfl, swapY_snd, ite_eq_left rfl, Equiv.swap_apply_self]
    · rw [swapY_snd, ite_eq_right h, swapY_snd, ite_eq_right h]

theorem ones_comp_swap {k : ℕ} (y : Str k → Bool) (j j' : Str k) :
    ones (fun x => y (Equiv.swap j j' x)) = ones y := by
  unfold ones
  exact Finset.card_equiv (Equiv.swap j j') (fun x => by simp)

theorem swapY_mem_Sb {b : Bool} {σ : P.State} {a : Bool} {j j' : Str P.k}
    {E E' : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (hσ' : σ a j' = .undisc E')
    {T : P.Tables} (hT : T ∈ P.Sb b σ) : P.swapY T a j j' ∈ P.Sb b σ := by
  unfold Sb at *
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
  obtain ⟨hv, hc⟩ := hT
  have hones : ∀ a', ones ((P.swapY T a j j').2 a') = ones (T.2 a') := by
    intro a'
    by_cases h : a' = a
    · subst h
      have : (P.swapY T a' j j').2 a' = fun x => T.2 a' (Equiv.swap j j' x) := by
        funext x; rw [swapY_snd, ite_eq_left rfl]
      rw [this, ones_comp_swap]
    · have : (P.swapY T a j j').2 a' = T.2 a' := by funext x; rw [swapY_snd, ite_eq_right h]
      rw [this]
  refine ⟨⟨by rw [hones]; exact hv.1, by rw [hones]; exact hv.2⟩, fun a' x => ?_⟩
  have hcx := hc a' x
  rw [swapY_snd]
  change (σ a' x).Cons (T.1 a' x) _
  split_ifs with h
  · subst h
    by_cases hx : x = j
    · subst hx; rw [hσ] at hcx ⊢; exact hcx
    · by_cases hx' : x = j'
      · subst hx'; rw [hσ'] at hcx ⊢; exact hcx
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; exact hcx
  · exact hcx

/-- `pw-lem:posterior`, labels: given the location of a fresh row `(a, j)`, the consistent
tables with label one at that row, counted `W - t_a` times, are as many as all of them counted
`m_{a,b} - s_a` times (stated without subtraction). Hence the label is one with conditional
probability `(m_{a,b} - s_a)/(W - t_a)`. -/
theorem card_label {b : Bool} {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) :
    (((P.Sb b σ).filter fun T => T.1 a j = i).filter fun T => T.2 a j = true).card *
        (P.U σ a).card + ((P.Sb b σ).filter fun T => T.1 a j = i).card * P.sA σ a =
      ((P.Sb b σ).filter fun T => T.1 a j = i).card * P.mab b a := by
  classical
  set S' := (P.Sb b σ).filter fun T => T.1 a j = i with hS'
  -- symmetry: every undiscovered row has the same count
  have hsym : ∀ j' ∈ P.U σ a, (S'.filter fun T => T.2 a j' = true).card =
      (S'.filter fun T => T.2 a j = true).card := by
    intro j' hj'
    have hd : (σ a j').discN = 0 := (Finset.mem_filter.mp hj').2
    obtain ⟨E', hE'⟩ : ∃ E', σ a j' = .undisc E' := by
      cases h : σ a j' with
      | disc _ _ => rw [h] at hd; simp [RowSt.discN] at hd
      | undisc E' => exact ⟨E', rfl⟩
    refine Finset.card_nbij' (fun T => P.swapY T a j j') (fun T => P.swapY T a j j') ?_ ?_ ?_ ?_
    · intro T hT
      simp only [hS', Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter] at hT ⊢
      refine ⟨⟨P.swapY_mem_Sb hσ hE' hT.1.1, hT.1.2⟩, ?_⟩
      rw [swapY_snd, ite_eq_left rfl, Equiv.swap_apply_left]; exact hT.2
    · intro T hT
      simp only [hS', Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter] at hT ⊢
      refine ⟨⟨P.swapY_mem_Sb hσ hE' hT.1.1, hT.1.2⟩, ?_⟩
      rw [swapY_snd, ite_eq_left rfl, Equiv.swap_apply_right]; exact hT.2
    · intro T _; exact P.swapY_swapY T a j j'
    · intro T _; exact P.swapY_swapY T a j j'
  -- double counting
  have hdc : ∑ j' ∈ P.U σ a, (S'.filter fun T => T.2 a j' = true).card =
      ∑ T ∈ S', ((P.U σ a).filter fun j' => T.2 a j' = true).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl hsym, Finset.sum_const, smul_eq_mul] at hdc
  have hsum : ∑ T ∈ S', (((P.U σ a).filter fun j' => T.2 a j' = true).card + P.sA σ a) =
      ∑ _T ∈ S', P.mab b a := by
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ∈ P.Sb b σ := (Finset.mem_filter.mp hT).1
    rw [P.ones_split hTS a, P.ones_valid (Finset.mem_filter.mp hTS).2.1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    ← hdc] at hsum
  rw [mul_comm]; exact hsum

end Prm

end LearningGuided.PointwiseLB
