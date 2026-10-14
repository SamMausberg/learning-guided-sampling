import LearningGuided.PointwiseLB.Util

/-!
# The table construction of Appendix B (`pw-sec:construction`)

An instance `θ = (B, I, Y)` consists of a root bit `B`, two location tables `I_{a,j} ∈ [ℓ]` and
two label tables `Y_{a,j} ∈ {0,1}`, `a ∈ {0,1}`, `j ∈ [W]`. Rows are indexed by their `k`-bit
addresses (`Str k`, with `2^k = W`); locations are indexed from `0`, so the location `i` of the
paper is `i - 1` here and the special string `s_i = 1^{i-1} 0^{ℓ-i+1}` is `stair (i-1)`.
The label table at root `B` has exactly `m_+` ones, the other exactly `m_-` ones (`Valid`).

A complete string is `x = (a, z_1, …, z_r)` with blocks `z = (j, s)` of length `d = k + ℓ`, and
`μ_θ(x) = Z⁻¹ ∏_t w_a(z_t)` (`pw-eq:target`) with block weights `pw-eq:block`.

The main results are the exact prefix masses `pw-eq:prefix-exact` (`mass_target`) and
Lemma `pw-lem:size-root` (`card_targetClass_le`, `target_injective`, `root_mass_ge`).
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm)

/-- Hidden tables `(I, Y)`: locations `I a j ∈ Fin ℓ` and labels `Y a j`. -/
abbrev Tables := (Bool → Str P.k → Fin P.ℓ) × (Bool → Str P.k → Bool)

/-- An instance `θ = (B, I, Y)`. -/
abbrev Inst := Bool × P.Tables

/-- The number of ones of a label table. -/
def ones {k : ℕ} (y : Str k → Bool) : ℕ := (Finset.univ.filter fun j => y j = true).card

/-- Validity of an instance: the label table at root `B` has `m_+` ones and the other `m_-`. -/
def Valid (B : Bool) (T : P.Tables) : Prop :=
  ones (T.2 B) = P.mPlus ∧ ones (T.2 (!B)) = P.mMinus

instance (B : Bool) (T : P.Tables) : Decidable (P.Valid B T) := by
  unfold Valid; infer_instance

/-- The common string `c = 1^ℓ`. -/
def cstr : List Bool := List.replicate P.ℓ true

/-- The special strings: `stair i = 1^i 0^{ℓ-i}` (the paper's `s_{i+1}`). -/
def stair (i : ℕ) : List Bool := List.replicate i true ++ List.replicate (P.ℓ - i) false

/-- The row address of a word: its first `k` letters. -/
def toRow (v : List Bool) : Str P.k := fun i => v.getD i false

/-- The block weight `w_a(j,s)` of `pw-eq:block`, for a block `z = (j, s)` given as a word. -/
noncomputable def w (T : P.Tables) (a : Bool) (z : List Bool) : ℝ :=
  if z.drop P.k = P.cstr then 1
  else if z.drop P.k = P.stair (T.1 a (P.toRow z)) then 1 + yv (T.2 a (P.toRow z)) / 2
  else 0

/-! ### Parsing a word into complete blocks and a partial block -/

/-- The number of complete blocks of the word following the root bit. -/
def nb (rest : List Bool) : ℕ := rest.length / P.d

/-- The `b`-th block of the word following the root bit. -/
def blk (rest : List Bool) (b : ℕ) : List Bool := (rest.drop (b * P.d)).take P.d

/-- The partial block `v` (possibly empty) after the complete blocks. -/
def part (rest : List Bool) : List Bool := rest.drop (P.nb rest * P.d)

/-- The product `P = ∏_{b ≤ t} w_a(z_b)` over the complete blocks. -/
noncomputable def Pw (T : P.Tables) (a : Bool) (rest : List Bool) : ℝ :=
  ∏ b ∈ Finset.range (P.nb rest), P.w T a (P.blk rest b)

theorem N_pos : 0 < P.N := by unfold N; omega

theorem d_pos : 0 < P.d := by unfold d; have := P.hℓ; omega

theorem k_lt_d : P.k < P.d := by unfold d; have := P.hℓ; omega

/-- The first bit of a complete string. -/
def x0 (x : Str P.N) : Bool := x ⟨0, P.N_pos⟩

/-- The target `μ_θ(x) = Z⁻¹ ∏_{t=1}^r w_a(z_t)` of `pw-eq:target` (it depends only on the
tables). -/
noncomputable def target (T : P.Tables) (x : Str P.N) : ℝ :=
  (∏ t ∈ Finset.range P.r, P.w T (P.x0 x) (P.blk (List.ofFn x).tail t)) / P.Z

/-- Row weights `2 + Y_{a,j}/2` (the total weight of the blocks of row `j`). -/
noncomputable def rowW (T : P.Tables) (a : Bool) : Str P.k → ℝ := fun j => 2 + yv (T.2 a j) / 2

/-- Block weights as a function on `{0,1}^d`. -/
noncomputable def blockW (T : P.Tables) (a : Bool) : Str P.d → ℝ := fun z => P.w T a (List.ofFn z)

/-- `b_a(v)`: the sum of the weights of the blocks extending a partial block `v`. -/
noncomputable def bmass (T : P.Tables) (a : Bool) (v : List Bool) : ℝ := mass (P.blockW T a) v

/-- `A_a = ∑_z w_a(z)`. -/
noncomputable def Asum (T : P.Tables) (a : Bool) : ℝ := P.bmass T a []

/-- The exact prefix mass formula `pw-eq:prefix-exact`. -/
noncomputable def massF (T : P.Tables) : List Bool → ℝ
  | [] => 1
  | a :: rest =>
      if P.r * P.d < rest.length then 0
      else if P.part rest = [] then P.Pw T a rest * P.Asum T a ^ (P.r - P.nb rest) / P.Z
      else P.Pw T a rest * P.bmass T a (P.part rest) * P.Asum T a ^ (P.r - P.nb rest - 1) / P.Z

/-- The exact local mass at a fully specified address: `[s = 1^{|s|}] + [s ⪯ s_I](1 + Y/2)`. -/
noncomputable def locMass (T : P.Tables) (a : Bool) (j : Str P.k) (s : List Bool) : ℝ :=
  (if s = List.replicate s.length true then 1 else 0) +
    (1 + yv (T.2 a j) / 2) * (if s <+: P.stair (T.1 a j) then 1 else 0)

/-- The formula for `b_a(v)`: row weights summed over compatible rows for a partial address, and
the local mass `locMass` for a fully specified address. -/
noncomputable def bForm (T : P.Tables) (a : Bool) (v : List Bool) : ℝ :=
  if v.length ≤ P.k then mass (P.rowW T a) v else P.locMass T a (P.toRow v) (v.drop P.k)

/-! ### Elementary facts about the strings -/

theorem length_stair {i : ℕ} (hi : i ≤ P.ℓ) : (P.stair i).length = P.ℓ := by
  simp [stair]; omega

theorem length_cstr : P.cstr.length = P.ℓ := by simp [cstr]

theorem stair_getElem? {i : ℕ} (hi : i ≤ P.ℓ) (q : ℕ) (hq : q < P.ℓ) :
    (P.stair i)[q]? = some (decide (q < i)) := by
  unfold stair
  by_cases h : q < i
  · rw [List.getElem?_append_left (by simpa using h)]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    have : q - (List.replicate i true).length < P.ℓ - i := by simp; omega
    simp only [List.getElem?_replicate, this, h]
    simp

theorem cstr_ne_stair {i : ℕ} (hi : i < P.ℓ) : P.cstr ≠ P.stair i := by
  intro h
  have h1 := P.stair_getElem? hi.le i hi
  rw [← h] at h1
  simp [cstr, hi] at h1

theorem stair_injective {i i' : ℕ} (hi : i ≤ P.ℓ) (hi' : i' ≤ P.ℓ) (h : P.stair i = P.stair i') :
    i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := P.stair_getElem? hi i (by omega)
    rw [h, P.stair_getElem? hi' i (by omega)] at h1
    simp [hlt] at h1
  · have h1 := P.stair_getElem? hi i' (by omega)
    rw [h, P.stair_getElem? hi' i' (by omega)] at h1
    simp [hlt] at h1

theorem toRow_append {v : List Bool} (hv : P.k ≤ v.length) (u : List Bool) :
    P.toRow (v ++ u) = P.toRow v := by
  funext i
  unfold toRow
  rw [List.getD_append _ _ _ _ (by omega)]

theorem w_nonneg (T : P.Tables) (a : Bool) (z : List Bool) : 0 ≤ P.w T a z := by
  unfold w; have := yv_nonneg (T.2 a (P.toRow z))
  split_ifs <;> linarith

theorem w_le (T : P.Tables) (a : Bool) (z : List Bool) : P.w T a z ≤ 3 / 2 := by
  unfold w; have := yv_le_one (T.2 a (P.toRow z))
  split_ifs <;> linarith

/-! ### Parsing lemmas -/

theorem length_part (rest : List Bool) : (P.part rest).length = rest.length % P.d := by
  unfold part nb
  rw [List.length_drop, Nat.mod_eq_sub_mul_div, Nat.mul_comm]

theorem nb_mul_le (rest : List Bool) : P.nb rest * P.d ≤ rest.length := by
  unfold nb; exact Nat.div_mul_le_self _ _

theorem length_eq_nb (rest : List Bool) :
    rest.length = P.nb rest * P.d + (P.part rest).length := by
  rw [length_part]; unfold nb
  have := Nat.div_add_mod rest.length P.d
  rw [Nat.mul_comm] at this; omega

theorem blk_append {rest : List Bool} {c : ℕ} (hc : c < P.nb rest) (u : List Bool) :
    P.blk (rest ++ u) c = P.blk rest c := by
  unfold blk
  have h1 : (c + 1) * P.d ≤ P.nb rest * P.d := Nat.mul_le_mul_right _ hc
  have h2 := P.nb_mul_le rest
  rw [List.drop_append_of_le_length (by rw [Nat.add_mul] at h1; omega)]
  rw [List.take_append_of_le_length (by rw [List.length_drop, Nat.add_mul] at *; omega)]

theorem length_blk {rest : List Bool} {c : ℕ} (hc : c < P.nb rest) :
    (P.blk rest c).length = P.d := by
  unfold blk
  have h1 : (c + 1) * P.d ≤ P.nb rest * P.d := Nat.mul_le_mul_right _ hc
  have h2 := P.nb_mul_le rest
  rw [List.length_take, List.length_drop, Nat.add_mul] at *
  omega

/-- Appending a letter inside a partial block keeps the complete blocks. -/
theorem parse_append_same {rest : List Bool} (h : (P.part rest).length + 1 < P.d) (x : Bool) :
    P.nb (rest ++ [x]) = P.nb rest ∧ P.part (rest ++ [x]) = P.part rest ++ [x] := by
  have hl := P.length_eq_nb rest
  have hd := P.d_pos
  have hnb : P.nb (rest ++ [x]) = P.nb rest := by
    change (rest ++ [x]).length / P.d = P.nb rest
    rw [List.length_append, List.length_singleton,
      show rest.length + 1 = ((P.part rest).length + 1) + P.nb rest * P.d by omega,
      Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h, zero_add]
  refine ⟨hnb, ?_⟩
  unfold part; rw [hnb]
  rw [List.drop_append_of_le_length (P.nb_mul_le rest)]

/-- Appending the last letter of a partial block completes it. -/
theorem parse_append_full {rest : List Bool} (h : (P.part rest).length + 1 = P.d) (x : Bool) :
    P.nb (rest ++ [x]) = P.nb rest + 1 ∧ P.part (rest ++ [x]) = [] ∧
      P.blk (rest ++ [x]) (P.nb rest) = P.part rest ++ [x] := by
  have hl := P.length_eq_nb rest
  have hd := P.d_pos
  have hnb : P.nb (rest ++ [x]) = P.nb rest + 1 := by
    change (rest ++ [x]).length / P.d = P.nb rest + 1
    rw [List.length_append, List.length_singleton,
      show rest.length + 1 = (P.nb rest + 1) * P.d by rw [Nat.add_mul]; omega,
      Nat.mul_div_cancel _ hd]
  refine ⟨hnb, ?_, ?_⟩
  · unfold part; rw [hnb]
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_drop, List.length_append, List.length_singleton, Nat.add_mul, one_mul]
    omega
  · unfold blk part
    rw [List.drop_append_of_le_length (P.nb_mul_le rest)]
    apply List.take_of_length_le
    rw [List.length_append, List.length_drop, List.length_singleton]
    omega

theorem Pw_append_same {T : P.Tables} {a : Bool} {rest : List Bool}
    (h : (P.part rest).length + 1 < P.d) (x : Bool) :
    P.Pw T a (rest ++ [x]) = P.Pw T a rest := by
  unfold Pw
  rw [(P.parse_append_same h x).1]
  exact Finset.prod_congr rfl fun c hc => by
    rw [P.blk_append (Finset.mem_range.mp hc)]

theorem Pw_append_full {T : P.Tables} {a : Bool} {rest : List Bool}
    (h : (P.part rest).length + 1 = P.d) (x : Bool) :
    P.Pw T a (rest ++ [x]) = P.Pw T a rest * P.w T a (P.part rest ++ [x]) := by
  obtain ⟨h1, -, h3⟩ := P.parse_append_full h x
  unfold Pw
  rw [h1, Finset.prod_range_succ, h3]
  congr 1
  exact Finset.prod_congr rfl fun c hc => by
    rw [P.blk_append (Finset.mem_range.mp hc)]

theorem Pw_nonneg (T : P.Tables) (a : Bool) (rest : List Bool) : 0 ≤ P.Pw T a rest :=
  Finset.prod_nonneg fun _ _ => P.w_nonneg T a _

/-! ### Exact block masses -/

theorem allOnes_append_false (s : List Bool) :
    s ++ [false] ≠ List.replicate (s ++ [false]).length true := by
  intro h
  have := congrArg List.getLast? h
  simp [List.getLast?_replicate] at this

theorem allOnes_append_true (s : List Bool) :
    (s ++ [true] = List.replicate (s ++ [true]).length true) ↔
      s = List.replicate s.length true := by
  rw [List.length_append, List.length_singleton, List.replicate_succ']
  constructor
  · intro h; exact List.append_cancel_right h
  · intro h; rw [← h]

theorem allOnes_children (s : List Bool) :
    (if s = List.replicate s.length true then (1 : ℝ) else 0) =
      (if s ++ [false] = List.replicate (s ++ [false]).length true then 1 else 0) +
        (if s ++ [true] = List.replicate (s ++ [true]).length true then 1 else 0) := by
  rw [ite_eq_right (allOnes_append_false s)]
  simp only [allOnes_append_true, zero_add]

theorem locMass_full (T : P.Tables) (a : Bool) (j : Str P.k) {s : List Bool}
    (hs : s.length = P.ℓ) :
    P.locMass T a j s =
      if s = P.cstr then 1 else if s = P.stair (T.1 a j) then 1 + yv (T.2 a j) / 2 else 0 := by
  unfold locMass
  have hI := (T.1 a j).isLt
  have hlen : (P.stair (T.1 a j)).length = P.ℓ := P.length_stair hI.le
  have hpre : (s <+: P.stair (T.1 a j)) ↔ s = P.stair (T.1 a j) :=
    ⟨fun h => h.eq_of_length (by rw [hs, hlen]), fun h => h ▸ List.prefix_refl _⟩
  have e1 : (if s = List.replicate s.length true then (1 : ℝ) else 0) =
      if s = P.cstr then 1 else 0 := by
    rw [hs]; rfl
  have e2 : (if s <+: P.stair (T.1 a j) then (1 : ℝ) else 0) =
      if s = P.stair (T.1 a j) then 1 else 0 := by
    by_cases h : s = P.stair (T.1 a j)
    · rw [ite_eq_left (hpre.mpr h), ite_eq_left h]
    · rw [ite_eq_right (mt hpre.mp h), ite_eq_right h]
  rw [e1, e2]
  by_cases h1 : s = P.cstr
  · have h2 : s ≠ P.stair (T.1 a j) := by rw [h1]; exact P.cstr_ne_stair hI
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1]; ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : s = P.stair (T.1 a j)
    · rw [ite_eq_left h2, ite_eq_left h2]; ring
    · rw [ite_eq_right h2, ite_eq_right h2]; ring

theorem toRow_eq_strOf {v : List Bool} (hv : v.length = P.k) : P.toRow v = strOf v hv := by
  funext i
  have hi : i.1 < v.length := by omega
  exact List.getD_eq_getElem _ _ hi

/-- Exact block masses: `b_a(v) = bForm`, valid for every partial block `|v| ≤ d`. -/
theorem bmass_eq (T : P.Tables) (a : Bool) {v : List Bool} (hv : v.length ≤ P.d) :
    P.bmass T a v = P.bForm T a v := by
  refine mass_eq_of_additive (P.blockW T a) (P.bForm T a) ?_ ?_ v hv
  · intro z
    have hlen : (List.ofFn z).length = P.d := List.length_ofFn
    unfold bForm
    rw [ite_eq_right (by have := P.k_lt_d; omega)]
    rw [P.locMass_full T a _ (by rw [List.length_drop, hlen]; unfold d; omega)]
    rfl
  · intro u hu
    unfold bForm
    rcases lt_trichotomy u.length P.k with h | h | h
    · rw [ite_eq_left h.le, ite_eq_left (by simp; omega), ite_eq_left (by simp; omega)]
      exact mass_children _ h
    · rw [ite_eq_left h.le, ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
      rw [mass_word_full _ u h, P.toRow_append h.ge, P.toRow_append h.ge,
        List.drop_append_of_le_length h.ge, List.drop_append_of_le_length h.ge,
        List.drop_of_length_le h.le, List.nil_append, List.nil_append, ← P.toRow_eq_strOf h]
      unfold locMass rowW
      have hI := (T.1 a (P.toRow u)).isLt
      have hlen := P.length_stair hI.le
      have := prefix_children_indicator (u := []) (L := P.stair (T.1 a (P.toRow u)))
        (by rw [hlen]; have := P.hℓ; simp; omega)
      simp only [List.nil_append, List.nil_prefix, ite_true] at this
      simp only [List.length_singleton, List.replicate_one, List.cons.injEq, and_true,
        Bool.false_eq_true, ite_false, ite_true, zero_add]
      linear_combination (1 + yv (T.2 a (P.toRow u)) / 2) * this
    · rw [ite_eq_right (by omega), ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
      rw [P.toRow_append h.le, P.toRow_append h.le, List.drop_append_of_le_length h.le,
        List.drop_append_of_le_length h.le]
      unfold locMass
      have hI := (T.1 a (P.toRow u)).isLt
      have hlen := P.length_stair hI.le
      have hpc := prefix_children_indicator (u := u.drop P.k) (L := P.stair (T.1 a (P.toRow u)))
        (by rw [hlen, List.length_drop]; unfold d at hu; omega)
      rw [allOnes_children (u.drop P.k), hpc]
      ring

theorem bmass_full (T : P.Tables) (a : Bool) {v : List Bool} (hv : v.length = P.d) :
    P.bmass T a v = P.w T a v := by
  unfold bmass; rw [mass_word_full _ v hv]; unfold blockW; rw [ofFn_strOf]

theorem bmass_children (T : P.Tables) (a : Bool) {v : List Bool} (hv : v.length < P.d) :
    P.bmass T a v = P.bmass T a (v ++ [false]) + P.bmass T a (v ++ [true]) :=
  mass_children _ hv

/-- For an incomplete address, `2J ≤ b_a(v) ≤ (5/2)J` with `J = 2^{k-|v|}` compatible rows. -/
theorem bmass_address_bounds (T : P.Tables) (a : Bool) {v : List Bool} (hv : v.length ≤ P.k) :
    2 * 2 ^ (P.k - v.length) ≤ P.bmass T a v ∧ P.bmass T a v ≤ 5 / 2 * 2 ^ (P.k - v.length) := by
  rw [P.bmass_eq T a (by have := P.k_lt_d; omega)]
  unfold bForm; rw [ite_eq_left hv]
  rw [← mass_const 2 hv, ← mass_const (5 / 2) hv]
  constructor
  · exact mass_mono (fun j => by unfold rowW; have := yv_nonneg (T.2 a j); linarith) v
  · exact mass_mono (fun j => by unfold rowW; have := yv_le_one (T.2 a j); linarith) v

theorem sum_yv_eq_ones {k : ℕ} (y : Str k → Bool) : ∑ j, yv (y j) = (ones y : ℝ) := by
  unfold yv ones
  rw [Finset.sum_boole]

theorem card_rows : Fintype.card (Str P.k) = P.W := by simp [W]

/-- `A_a = ∑_z w_a(z) = 2W + (number of ones of Y_a)/2`. -/
theorem Asum_eq (T : P.Tables) (a : Bool) :
    P.Asum T a = 2 * (P.W : ℝ) + (ones (T.2 a) : ℝ) / 2 := by
  unfold Asum
  rw [P.bmass_eq T a (by simp), bForm, ite_eq_left (by simp), mass_nil]
  unfold rowW
  rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_yv_eq_ones]
  simp only [Finset.sum_const, Finset.card_univ, card_rows, nsmul_eq_mul]
  ring

theorem Asum_valid {B : Bool} {T : P.Tables} (hv : P.Valid B T) (a : Bool) :
    P.Asum T a = if a = B then P.Aplus else P.Aminus := by
  rw [Asum_eq]
  by_cases h : a = B
  · subst h; rw [ite_eq_left rfl, hv.1]; rfl
  · have : a = !B := by cases a <;> cases B <;> simp_all
    subst this
    rw [ite_eq_right h, hv.2]; rfl

theorem Asum_pos {B : Bool} {T : P.Tables} (hv : P.Valid B T) (a : Bool) : 0 < P.Asum T a := by
  rw [P.Asum_valid hv]; split_ifs
  · exact P.Aplus_pos
  · exact P.Aminus_pos

/-! ### The exact prefix masses `pw-eq:prefix-exact` -/

theorem massF_cons_add (T : P.Tables) (a : Bool) {rest : List Bool}
    (h : rest.length < P.r * P.d) :
    P.massF T (a :: rest) =
      P.massF T (a :: (rest ++ [false])) + P.massF T (a :: (rest ++ [true])) := by
  have hlen : ∀ x : Bool, ¬ P.r * P.d < (rest ++ [x]).length := fun x => by simp; omega
  simp only [massF, ite_eq_right (hlen false), ite_eq_right (hlen true),
    ite_eq_right (show ¬ P.r * P.d < rest.length by omega)]
  have hρ := P.length_part rest
  have hρd : (P.part rest).length < P.d := by rw [hρ]; exact Nat.mod_lt _ P.d_pos
  have hl := P.length_eq_nb rest
  rcases Nat.lt_or_ge ((P.part rest).length + 1) P.d with h1 | h1
  · -- the partial block stays partial
    have hs := fun x => P.parse_append_same h1 x
    have hP := fun x => P.Pw_append_same (T := T) (a := a) h1 x
    rw [(hs false).2, (hs true).2, (hs false).1, (hs true).1, hP false, hP true]
    have hc : ∀ x : Bool, P.part rest ++ [x] ≠ [] := fun x => by simp
    rw [ite_eq_right (hc false), ite_eq_right (hc true)]
    by_cases h0 : P.part rest = []
    · rw [ite_eq_left h0, h0]
      have ht : P.nb rest < P.r := by
        rw [h0, List.length_nil, add_zero] at hl
        by_contra hc
        have : P.r * P.d ≤ P.nb rest * P.d := Nat.mul_le_mul_right _ (by omega)
        omega
      have hpow : P.Asum T a ^ (P.r - P.nb rest) =
          P.Asum T a * P.Asum T a ^ (P.r - P.nb rest - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow]
      have := P.bmass_children T a (v := []) P.d_pos
      simp only [List.nil_append] at this
      unfold Asum
      rw [this]; simp only [List.nil_append]; ring
    · rw [ite_eq_right h0, P.bmass_children T a hρd]; ring
  · have h1' : (P.part rest).length + 1 = P.d := by omega
    have hs := fun x => P.parse_append_full h1' x
    have hP := fun x => P.Pw_append_full (T := T) (a := a) h1' x
    rw [(hs false).2.1, (hs true).2.1, (hs false).1, (hs true).1, hP false, hP true]
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hne : P.part rest ≠ [] := by
      intro h0; rw [h0, List.length_nil, zero_add] at h1'; unfold d at h1'; have := P.hℓ
      omega
    rw [ite_eq_right hne, P.bmass_children T a hρd,
      P.bmass_full T a (by simp; omega), P.bmass_full T a (by simp; omega)]
    rw [show P.r - (P.nb rest + 1) = P.r - P.nb rest - 1 by omega]
    ring

theorem ofFn_eq_cons (x : Str P.N) : List.ofFn x = P.x0 x :: (List.ofFn x).tail := by
  have hne : List.ofFn x ≠ [] := by
    rw [Ne, List.ofFn_eq_nil_iff]; have := P.N_pos; omega
  conv_lhs => rw [← List.cons_head_tail hne]
  rw [List.head_ofFn]; rfl

theorem length_tail_ofFn (x : Str P.N) : (List.ofFn x).tail.length = P.r * P.d := by
  rw [List.length_tail, List.length_ofFn]; unfold N; omega

theorem massF_ofFn (T : P.Tables) (x : Str P.N) : P.massF T (List.ofFn x) = P.target T x := by
  rw [P.ofFn_eq_cons x]
  have hl := P.length_tail_ofFn x
  have hnb : P.nb (List.ofFn x).tail = P.r := by
    unfold nb; rw [hl, Nat.mul_div_cancel _ P.d_pos]
  have hpart : P.part (List.ofFn x).tail = [] := by
    unfold part; rw [hnb, ← hl]; exact List.drop_of_length_le le_rfl
  simp only [massF, ite_eq_right (show ¬ P.r * P.d < (List.ofFn x).tail.length by omega),
    ite_eq_left hpart, hnb, Nat.sub_self, pow_zero, mul_one]
  unfold Pw target; rw [hnb]

theorem massF_nil_add {B : Bool} {T : P.Tables} (hv : P.Valid B T) :
    P.massF T [] = P.massF T [false] + P.massF T [true] := by
  have hpart : P.part [] = [] := by simp [part]
  have hnb : P.nb [] = 0 := by simp [nb]
  simp only [massF, List.length_nil, ite_eq_right (show ¬ P.r * P.d < 0 by omega),
    ite_eq_left hpart, hnb, Nat.sub_zero]
  simp only [Pw, hnb, Finset.range_zero, Finset.prod_empty, one_mul]
  rw [← add_div, P.Asum_valid hv, P.Asum_valid hv]
  have hsum : (if false = B then P.Aplus else P.Aminus) ^ P.r +
      (if true = B then P.Aplus else P.Aminus) ^ P.r = P.Z := by
    unfold Z; cases B <;> simp [add_comm]
  rw [hsum, div_self P.Z_pos.ne']

/-- `pw-eq:prefix-exact`: the exact prefix masses, `μ_θ(u) = massF(u)` for `|u| ≤ N`. -/
theorem mass_target {B : Bool} {T : P.Tables} (hv : P.Valid B T) {u : List Bool}
    (hu : u.length ≤ P.N) : mass (P.target T) u = P.massF T u := by
  refine mass_eq_of_additive (P.target T) (P.massF T) (P.massF_ofFn T) ?_ u hu
  intro u hu
  cases u with
  | nil => exact P.massF_nil_add hv
  | cons a rest =>
      simp only [List.cons_append]
      exact P.massF_cons_add T a (by simp [N] at hu; omega)

theorem target_nonneg (T : P.Tables) (x : Str P.N) : 0 ≤ P.target T x :=
  div_nonneg (Finset.prod_nonneg fun _ _ => P.w_nonneg T _ _) P.Z_pos.le

/-- Each target is a probability distribution (the total weight is `Z`). -/
theorem isDist_target {B : Bool} {T : P.Tables} (hv : P.Valid B T) : IsDist (P.target T) := by
  refine ⟨P.target_nonneg T, ?_⟩
  rw [← mass_nil, P.mass_target hv (by simp)]
  rfl

theorem massF_single (T : P.Tables) (a : Bool) : P.massF T [a] = P.Asum T a ^ P.r / P.Z := by
  have hpart : P.part [] = [] := by simp [part]
  have hnb : P.nb [] = 0 := by simp [nb]
  simp only [massF, List.length_nil, ite_eq_right (show ¬ P.r * P.d < 0 by omega),
    ite_eq_left hpart, hnb, Nat.sub_zero]
  simp [Pw, hnb]

theorem isPre_single (x : Str P.N) (b : Bool) : IsPre [b] x ↔ P.x0 x = b := by
  unfold IsPre
  rw [P.ofFn_eq_cons x, List.cons_prefix_cons]
  simp [eq_comm]

/-- The probability of the event `X₁ = b` is the prefix mass at `[b]`. -/
theorem mass_single_eq_sum (μ : Str P.N → ℝ) (b : Bool) :
    mass μ [b] = ∑ x ∈ Finset.univ.filter (fun x => P.x0 x = b), μ x := by
  unfold mass
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by simp only [P.isPre_single]

/-- `pw-lem:size-root`, `pw-eq:rootgap`: every target has `μ_θ(X₁ = B) ≥ 3/5`. -/
theorem root_mass_ge {B : Bool} {T : P.Tables} (hv : P.Valid B T) :
    3 / 5 ≤ mass (P.target T) [B] := by
  rw [P.mass_target hv (by simp [N]), massF_single, P.Asum_valid hv, ite_eq_left rfl]
  exact P.root_gap

/-! ### The class and its size (`pw-lem:size-root`) -/

/-- The valid instances `θ = (B, I, Y)`. -/
noncomputable def instances : Finset P.Inst := Finset.univ.filter fun θ => P.Valid θ.1 θ.2

/-- The class of targets on `N` bits. -/
noncomputable def targetClass : Finset (Str P.N → ℝ) :=
  P.instances.image fun θ => P.target θ.2

theorem card_inst : Fintype.card P.Inst = P.M0 := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, M0, W]
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ P.k) 2]
  ring

/-- `pw-lem:size-root`, class size: the class has at most `M₀ = 2(2ℓ)^{2W}` targets. -/
theorem card_targetClass_le : P.targetClass.card ≤ P.M0 := by
  calc P.targetClass.card ≤ P.instances.card := Finset.card_image_le
    _ ≤ Fintype.card P.Inst := Finset.card_le_univ _
    _ = P.M0 := P.card_inst

end Prm

end LearningGuided.PointwiseLB
