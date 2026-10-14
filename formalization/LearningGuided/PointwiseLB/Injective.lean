import LearningGuided.PointwiseLB.Construction

/-!
# Distinct instances give distinct targets (Lemma `pw-lem:size-root`)

A target determines its tables: holding all but one block at a common string exposes each
block weight `w_a(j,s)` through `pw-eq:target`. The weight at `s = s_i` is positive exactly
when `I_{a,j} = i`, and then equals `1 + Y_{a,j}/2`. Finally the root `B` is the table with
`m_+` ones.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm)

/-- A common block: all ones. -/
def cblk : List Bool := List.replicate P.d true

theorem w_cblk (T : P.Tables) (a : Bool) : P.w T a P.cblk = 1 := by
  unfold w cblk cstr
  rw [List.drop_replicate, show P.d - P.k = P.ℓ by unfold d; omega, ite_eq_left rfl]

/-- The probe string `(a, z, c, …, c)`. -/
def probe (a : Bool) (z : List Bool) : List Bool :=
  a :: (z ++ List.replicate ((P.r - 1) * P.d) true)

theorem length_probe (a : Bool) {z : List Bool} (hz : z.length = P.d) :
    (P.probe a z).length = P.N := by
  unfold probe N
  simp only [List.length_cons, List.length_append, List.length_replicate, hz]
  have := P.r_pos
  have : P.d + (P.r - 1) * P.d = P.r * P.d := by
    obtain ⟨r', hr'⟩ : ∃ r', P.r = r' + 1 := ⟨P.r - 1, by omega⟩
    rw [hr', Nat.add_sub_cancel, Nat.succ_mul]; ring
  omega

theorem blk_probe_zero {z : List Bool} (hz : z.length = P.d) :
    P.blk (z ++ List.replicate ((P.r - 1) * P.d) true) 0 = z := by
  unfold blk
  simp only [zero_mul, List.drop_zero]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem blk_probe_succ {z : List Bool} (hz : z.length = P.d) {t : ℕ} (ht : t + 1 < P.r) :
    P.blk (z ++ List.replicate ((P.r - 1) * P.d) true) (t + 1) = P.cblk := by
  unfold blk cblk
  rw [List.drop_append, List.drop_of_length_le (by rw [hz]; nlinarith), List.nil_append,
    List.drop_replicate, List.take_replicate, hz]
  congr 1
  have : (t + 1) * P.d - P.d = t * P.d := by rw [Nat.succ_mul]; omega
  rw [this]
  have : (t + 1) * P.d ≤ (P.r - 1) * P.d := Nat.mul_le_mul_right _ (by omega)
  have : P.d ≤ (P.r - 1) * P.d - t * P.d := by rw [Nat.succ_mul] at this; omega
  omega

theorem target_probe (T : P.Tables) (a : Bool) {z : List Bool} (hz : z.length = P.d) :
    P.target T (strOf (P.probe a z) (P.length_probe a hz)) = P.w T a z / P.Z := by
  unfold target
  have hofn := ofFn_strOf (P.probe a z) (P.length_probe a hz)
  have hx0 : P.x0 (strOf (P.probe a z) (P.length_probe a hz)) = a := by
    unfold x0 strOf probe; simp
  rw [hx0, hofn]
  congr 1
  unfold probe
  simp only [List.tail_cons]
  obtain ⟨r', hr'⟩ : ∃ r', P.r = r' + 1 := ⟨P.r - 1, by have := P.r_pos; omega⟩
  rw [show Finset.range P.r = Finset.range (r' + 1) by rw [hr'], Finset.prod_range_succ',
    P.blk_probe_zero hz]
  rw [Finset.prod_congr rfl fun t ht => by
    rw [P.blk_probe_succ hz (by rw [hr']; have := Finset.mem_range.mp ht; omega), w_cblk]]
  simp

/-- The block with row `j` and special string `s_i`. -/
def sblk (j : Str P.k) (i : ℕ) : List Bool := List.ofFn j ++ P.stair i

theorem length_sblk (j : Str P.k) {i : ℕ} (hi : i ≤ P.ℓ) : (P.sblk j i).length = P.d := by
  unfold sblk d; rw [List.length_append, List.length_ofFn, P.length_stair hi]

theorem w_sblk (T : P.Tables) (a : Bool) (j : Str P.k) (i : Fin P.ℓ) :
    P.w T a (P.sblk j i) = if T.1 a j = i then 1 + yv (T.2 a j) / 2 else 0 := by
  have hrow : P.toRow (P.sblk j i) = j := by
    unfold sblk
    rw [P.toRow_append (by simp), P.toRow_eq_strOf (by simp)]
    funext q; simp [strOf]
  have hdrop : (P.sblk j i).drop P.k = P.stair i := by
    unfold sblk; rw [List.drop_append_of_le_length (by simp)]; simp
  unfold w
  rw [hrow, hdrop, ite_eq_right (Ne.symm (P.cstr_ne_stair i.isLt))]
  by_cases h : T.1 a j = i
  · rw [ite_eq_left (by rw [h]), ite_eq_left h]
  · rw [ite_eq_right (fun he => h (Fin.ext (P.stair_injective i.isLt.le (Fin.isLt _).le he).symm)),
      ite_eq_right h]

/-- `pw-lem:size-root`, injectivity: distinct valid instances give distinct targets. -/
theorem target_injective {B B' : Bool} {T T' : P.Tables} (hv : P.Valid B T)
    (hv' : P.Valid B' T') (h : P.target T = P.target T') : (B, T) = (B', T') := by
  have hZ := P.Z_pos
  have hw : ∀ a z, z.length = P.d → P.w T a z = P.w T' a z := by
    intro a z hz
    have := congrFun h (strOf (P.probe a z) (P.length_probe a hz))
    rw [P.target_probe T a hz, P.target_probe T' a hz] at this
    field_simp at this
    exact this
  have hT : T = T' := by
    have key : ∀ a j, T.1 a j = T'.1 a j ∧ T.2 a j = T'.2 a j := by
      intro a j
      have e := hw a (P.sblk j (T.1 a j)) (P.length_sblk j (T.1 a j).isLt.le)
      rw [P.w_sblk, P.w_sblk, ite_eq_left rfl] at e
      have hy := yv_nonneg (T.2 a j)
      by_cases h1 : T'.1 a j = T.1 a j
      · rw [ite_eq_left h1] at e
        refine ⟨h1.symm, ?_⟩
        have : yv (T.2 a j) = yv (T'.2 a j) := by linarith
        unfold yv at this
        cases h2 : T.2 a j <;> cases h3 : T'.2 a j <;> simp_all
      · rw [ite_eq_right h1] at e; linarith
    apply Prod.ext <;> funext a j
    · exact (key a j).1
    · exact (key a j).2
  subst hT
  have hB : B = B' := by
    by_contra hne
    have : B' = !B := by cases B <;> cases B' <;> simp_all
    rw [this] at hv'
    have := hv.2.symm.trans hv'.1
    exact absurd this (Nat.ne_of_lt P.mMinus_lt_mPlus)
  rw [hB]

end Prm

end LearningGuided.PointwiseLB
