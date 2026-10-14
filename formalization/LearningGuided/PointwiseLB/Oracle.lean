import LearningGuided.PointwiseLB.Construction

/-!
# The fixed approximate-prefix oracle `h_θ` (Appendix B, Lemma `pw-lem:oracle`)

`h_θ(∅) = 1`. For a nonempty prefix `u = (a, z_1, …, z_t, v)` with `|v| < d`, let
`P = ∏_{b ≤ t} w_a(z_b)`. Then (`pw-eq:h-boundary`, `pw-eq:h-address`, `pw-eq:h-comb`)

* `h_θ(u) = P A_∘^{r-t} / Z` if `v = ∅`,
* `h_θ(u) = P (9/4) J A_∘^{r-t-1} / Z` with `J = 2^{k-|v|}` if `0 < |v| < k`,
* `h_θ(u) = P g_a(j,s) A_∘^{r-t-1} / Z` if `v = (j, s)` with `|s| < ℓ`, where `g_a` is
  `pw-eq:local`.

(The case `P = 0` of the paper is included: the formulas give `0`.) Words longer than `N`
answer `0`. Lemma `pw-lem:oracle`: `(9/20) μ_θ ≤ h_θ ≤ (20/9) μ_θ` at every prefix, with
equality at complete strings; hence `h_θ` is a pointwise factor-`9/4` guide.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm)

/-- `g_a(j,s)` of `pw-eq:local` (locations indexed from `0`: the paper's
`s = 1^{i-1} 0^{|s|-i+1}`, `i ≤ |s|`, is `s = 1^i 0^{|s|-i}`, `i < |s|` here). -/
noncomputable def gloc (T : P.Tables) (a : Bool) (j : Str P.k) (s : List Bool) : ℝ :=
  if s = List.replicate s.length true then 3 / 2
  else if ∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧
      s = List.replicate i true ++ List.replicate (s.length - i) false ∧ T.1 a j = i then
    1 + yv (T.2 a j) / 2
  else 0

/-- The oracle `h_θ` of `pw-eq:h-boundary`, `pw-eq:h-address`, `pw-eq:local`,
`pw-eq:h-comb`. It depends only on the tables `(I, Y)`. -/
noncomputable def oracle (T : P.Tables) : Guide
  | [] => 1
  | a :: rest =>
      if P.r * P.d < rest.length then 0
      else if P.part rest = [] then P.Pw T a rest * P.Acirc ^ (P.r - P.nb rest) / P.Z
      else if (P.part rest).length < P.k then
        P.Pw T a rest * (9 / 4 * 2 ^ (P.k - (P.part rest).length)) *
          P.Acirc ^ (P.r - P.nb rest - 1) / P.Z
      else
        P.Pw T a rest * P.gloc T a (P.toRow (P.part rest)) ((P.part rest).drop P.k) *
          P.Acirc ^ (P.r - P.nb rest - 1) / P.Z

theorem gloc_nonneg (T : P.Tables) (a : Bool) (j : Str P.k) (s : List Bool) :
    0 ≤ P.gloc T a j s := by
  unfold gloc; have := yv_nonneg (T.2 a j); split_ifs <;> linarith

theorem oracle_nonneg (T : P.Tables) (u : List Bool) : 0 ≤ P.oracle T u := by
  have hZ := P.Z_pos.le
  have hA := P.Acirc_pos.le
  have hP := fun a rest => P.Pw_nonneg T a rest
  cases u with
  | nil => simp [oracle]
  | cons a rest =>
      simp only [oracle]
      have := P.gloc_nonneg T a (P.toRow (P.part rest)) ((P.part rest).drop P.k)
      split_ifs
      · exact le_rfl
      · exact div_nonneg (mul_nonneg (hP a rest) (pow_nonneg hA _)) hZ
      · exact div_nonneg (mul_nonneg (mul_nonneg (hP a rest) (by positivity))
          (pow_nonneg hA _)) hZ
      · exact div_nonneg (mul_nonneg (mul_nonneg (hP a rest) this) (pow_nonneg hA _)) hZ

/-- `pw-eq:local`, pattern lemma: a partial string with a zero is a prefix of the
special string `s_I` exactly when it has the form `1^I 0^{|s|-I}` with `I < |s|`. -/
theorem stair_pattern_iff {s : List Bool} (hs : s.length < P.ℓ)
    (hne : s ≠ List.replicate s.length true) (I : Fin P.ℓ) :
    (∃ i : Fin P.ℓ, (i : ℕ) < s.length ∧
        s = List.replicate i true ++ List.replicate (s.length - i) false ∧ I = i) ↔
      s <+: P.stair I := by
  have hI := I.isLt
  have htake : ∀ m : ℕ, (P.stair I).take m =
      List.replicate (min m I) true ++ List.replicate (min (m - I) (P.ℓ - I)) false := by
    intro m
    unfold stair
    rw [List.take_append, List.take_replicate, List.take_replicate, List.length_replicate]
  constructor
  · rintro ⟨i, hi, hs', rfl⟩
    rw [List.prefix_iff_eq_take, htake, hs']
    simp only [List.length_append, List.length_replicate]
    rw [Nat.min_eq_right (by omega), Nat.min_eq_left (by omega)]
    congr 2; omega
  · intro h
    rw [List.prefix_iff_eq_take, htake] at h
    by_cases hlt : (I : ℕ) < s.length
    · refine ⟨I, hlt, ?_, rfl⟩
      rw [h]; simp only [List.length_append, List.length_replicate]
      rw [Nat.min_eq_right hlt.le, Nat.min_eq_left (by omega)]
      congr 2
      have := congrArg List.length h
      simp only [List.length_append, List.length_replicate] at this
      omega
    · exfalso; apply hne
      rw [h]; simp only [List.length_append, List.length_replicate]
      rw [Nat.min_eq_left (by omega), show s.length - I = 0 by omega]
      simp

/-- `pw-lem:oracle`, local factor: `g_a` agrees with the exact local mass when the partial string
contains a zero. -/
theorem gloc_eq_locMass {T : P.Tables} {a : Bool} {j : Str P.k} {s : List Bool}
    (hs : s.length < P.ℓ) (hne : s ≠ List.replicate s.length true) :
    P.gloc T a j s = P.locMass T a j s := by
  unfold gloc locMass
  rw [ite_eq_right hne, ite_eq_right hne, zero_add]
  by_cases h : s <+: P.stair (T.1 a j)
  · rw [ite_eq_left ((P.stair_pattern_iff hs hne _).mpr h), ite_eq_left h, mul_one]
  · rw [ite_eq_right (mt (P.stair_pattern_iff hs hne _).mp h), ite_eq_right h, mul_zero]

/-- `pw-lem:oracle`, local factor: at an all-ones partial string the exact local mass is one of `1,
2, 5/2`, and `3/2` approximates it within the factor `5/3`. -/
theorem locMass_allOnes_bounds {T : P.Tables} {a : Bool} {j : Str P.k} {s : List Bool}
    (hs : s = List.replicate s.length true) :
    1 ≤ P.locMass T a j s ∧ P.locMass T a j s ≤ 5 / 2 := by
  unfold locMass
  rw [ite_eq_left hs]
  have h1 := yv_nonneg (T.2 a j)
  have h2 := yv_le_one (T.2 a j)
  split_ifs <;> constructor <;> nlinarith

/-- `b_a(v)` at a fully specified address `|v| ≥ k`. -/
theorem bmass_loc (T : P.Tables) (a : Bool) {v : List Bool} (hk : P.k ≤ v.length)
    (hd : v.length ≤ P.d) :
    P.bmass T a v = P.locMass T a (P.toRow v) (v.drop P.k) := by
  rw [P.bmass_eq T a hd]
  unfold bForm
  rcases hk.lt_or_eq with h | h
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_left h.ge, mass_word_full _ v h.symm, ← P.toRow_eq_strOf h.symm]
    rw [List.drop_of_length_le h.ge]
    unfold locMass rowW
    simp [List.nil_prefix]
    ring

/-- The common shape of the comparison: `h = P X' Y'/Z` and `μ = P X Y/Z`. -/
theorem ratio_shape {Pw X X' Y Y' ρ α β Z : ℝ} (hPw : 0 ≤ Pw) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 < Z) (hα : 0 ≤ α) (hX1 : α * X ≤ X') (hX2 : X' ≤ β * X) (hYY : Y' = Y * ρ)
    (hρ1 : 3 / 4 ≤ ρ) (hρ2 : ρ ≤ 4 / 3) :
    α * (3 / 4) * (Pw * X * Y / Z) ≤ Pw * X' * Y' / Z ∧
      Pw * X' * Y' / Z ≤ β * (4 / 3) * (Pw * X * Y / Z) := by
  subst hYY
  have hXY : 0 ≤ X * Y := mul_nonneg hX hY
  have hX' : 0 ≤ X' := le_trans (mul_nonneg hα hX) hX1
  constructor
  · have : α * X * (Y * (3 / 4)) ≤ X' * (Y * ρ) :=
      mul_le_mul hX1 (by nlinarith) (by positivity) hX'
    have key : α * (3 / 4) * (Pw * X * Y) ≤ Pw * X' * (Y * ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left this hPw]
    calc α * (3 / 4) * (Pw * X * Y / Z) = (α * (3 / 4) * (Pw * X * Y)) / Z := by ring
      _ ≤ Pw * X' * (Y * ρ) / Z := div_le_div_of_nonneg_right key hZ.le
  · have : X' * (Y * ρ) ≤ β * X * (Y * (4 / 3)) :=
      mul_le_mul hX2 (by nlinarith) (by nlinarith) (le_trans hX' hX2)
    have key : Pw * X' * (Y * ρ) ≤ β * (4 / 3) * (Pw * X * Y) := by
      nlinarith [mul_le_mul_of_nonneg_left this hPw]
    calc Pw * X' * (Y * ρ) / Z ≤ (β * (4 / 3) * (Pw * X * Y)) / Z :=
          div_le_div_of_nonneg_right key hZ.le
      _ = β * (4 / 3) * (Pw * X * Y / Z) := by ring

theorem tail_ratio {B : Bool} {T : P.Tables} (hv : P.Valid B T) (a : Bool) {e : ℕ}
    (he : e ≤ P.r) :
    3 / 4 ≤ (P.Acirc / P.Asum T a) ^ e ∧ (P.Acirc / P.Asum T a) ^ e ≤ 4 / 3 := by
  rw [P.Asum_valid hv]
  split_ifs
  · exact P.tail_ratio_plus he
  · exact P.tail_ratio_minus he

theorem Acirc_pow_eq {B : Bool} {T : P.Tables} (hv : P.Valid B T) (a : Bool) (e : ℕ) :
    P.Acirc ^ e = P.Asum T a ^ e * (P.Acirc / P.Asum T a) ^ e := by
  rw [div_pow, mul_div_cancel₀ _ (pow_pos (P.Asum_pos hv a) e).ne']

/-- `pw-lem:oracle`: for every valid instance and every prefix `u` with `|u| ≤ N`,
`(9/20) μ_θ(u) ≤ h_θ(u) ≤ (20/9) μ_θ(u)`. -/
theorem oracle_bounds {B : Bool} {T : P.Tables} (hv : P.Valid B T) {u : List Bool}
    (hu : u.length ≤ P.N) :
    9 / 20 * mass (P.target T) u ≤ P.oracle T u ∧
      P.oracle T u ≤ 20 / 9 * mass (P.target T) u := by
  rw [P.mass_target hv hu]
  cases u with
  | nil => simp [oracle, massF]; norm_num
  | cons a rest =>
      have hrest : ¬ P.r * P.d < rest.length := by simp [N] at hu; omega
      simp only [oracle, massF, ite_eq_right hrest]
      have hPw := P.Pw_nonneg T a rest
      have hZ := P.Z_pos
      have hAs := (P.Asum_pos hv a).le
      have hl := P.length_eq_nb rest
      have ht : P.nb rest ≤ P.r := by
        by_contra hc
        have : (P.r + 1) * P.d ≤ P.nb rest * P.d := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this; have := P.d_pos; omega
      by_cases h0 : P.part rest = []
      · rw [ite_eq_left h0, ite_eq_left h0]
        obtain ⟨h1, h2⟩ := P.tail_ratio hv a (e := P.r - P.nb rest) (by omega)
        have := ratio_shape (Pw := P.Pw T a rest) (X := 1) (X' := 1) (α := 1) (β := 1)
          hPw zero_le_one (pow_nonneg hAs _) hZ zero_le_one (by norm_num) (by norm_num)
          (P.Acirc_pow_eq hv a _) h1 h2
        simp only [mul_one] at this
        constructor <;> nlinarith [this.1, this.2,
          div_nonneg (mul_nonneg hPw (pow_nonneg hAs (P.r - P.nb rest))) hZ.le]
      · rw [ite_eq_right h0, ite_eq_right h0]
        have hpd : (P.part rest).length < P.d := by
          rw [P.length_part]; exact Nat.mod_lt _ P.d_pos
        have htr : P.nb rest < P.r := by
          by_contra hc
          have hpos : 0 < (P.part rest).length := List.length_pos_iff.mpr h0
          have : P.r * P.d ≤ P.nb rest * P.d := Nat.mul_le_mul_right _ (by omega)
          omega
        obtain ⟨h1, h2⟩ := P.tail_ratio hv a (e := P.r - P.nb rest - 1) (by omega)
        have hb0 : 0 ≤ P.bmass T a (P.part rest) := by
          rw [P.bmass_eq T a hpd.le]; unfold bForm
          split_ifs
          · exact mass_nonneg (fun j => by unfold rowW; have := yv_nonneg (T.2 a j); linarith) _
          · unfold locMass; have := yv_nonneg (T.2 a (P.toRow (P.part rest)))
            split_ifs <;> linarith
        have hMF : 0 ≤ P.Pw T a rest * P.bmass T a (P.part rest) *
            P.Asum T a ^ (P.r - P.nb rest - 1) / P.Z := by positivity
        by_cases hk : (P.part rest).length < P.k
        · rw [ite_eq_left hk]
          obtain ⟨hb1, hb2⟩ := P.bmass_address_bounds T a hk.le
          set J : ℝ := 2 ^ (P.k - (P.part rest).length)
          have hJ : 0 < J := by positivity
          have := ratio_shape (Pw := P.Pw T a rest) (X := P.bmass T a (P.part rest))
            (X' := 9 / 4 * J) (α := 9 / 10) (β := 9 / 8) hPw hb0 (pow_nonneg hAs _) hZ
            (by norm_num) (by nlinarith) (by nlinarith) (P.Acirc_pow_eq hv a _) h1 h2
          constructor <;> nlinarith [this.1, this.2]
        · rw [ite_eq_right hk]
          have hk' : P.k ≤ (P.part rest).length := by omega
          rw [P.bmass_loc T a hk' hpd.le] at hb0 hMF ⊢
          set s := (P.part rest).drop P.k
          have hsl : s.length < P.ℓ := by
            simp only [s, List.length_drop]; unfold d at hpd; omega
          by_cases hs1 : s = List.replicate s.length true
          · obtain ⟨hl1, hl2⟩ := P.locMass_allOnes_bounds (T := T) (a := a)
              (j := P.toRow (P.part rest)) hs1
            have hg : P.gloc T a (P.toRow (P.part rest)) s = 3 / 2 := by
              unfold gloc; rw [ite_eq_left hs1]
            rw [hg]
            have := ratio_shape (Pw := P.Pw T a rest)
              (X := P.locMass T a (P.toRow (P.part rest)) s)
              (X' := 3 / 2) (α := 3 / 5) (β := 3 / 2) hPw hb0 (pow_nonneg hAs _) hZ
              (by norm_num) (by nlinarith) (by nlinarith) (P.Acirc_pow_eq hv a _) h1 h2
            constructor <;> nlinarith [this.1, this.2]
          · rw [P.gloc_eq_locMass hsl hs1]
            have := ratio_shape (Pw := P.Pw T a rest)
              (X := P.locMass T a (P.toRow (P.part rest)) s)
              (X' := P.locMass T a (P.toRow (P.part rest)) s) (α := 1) (β := 1) hPw hb0
              (pow_nonneg hAs _) hZ zero_le_one (by linarith) (by linarith)
              (P.Acirc_pow_eq hv a _) h1 h2
            constructor <;> nlinarith [this.1, this.2]

/-- `pw-lem:oracle`, exactness at complete strings: `h_θ(x) = μ_θ(x)` for `|x| = N`. -/
theorem oracle_leaf (T : P.Tables) (x : Str P.N) :
    P.oracle T (List.ofFn x) = P.target T x := by
  rw [← P.massF_ofFn T x, P.ofFn_eq_cons x]
  have hl := P.length_tail_ofFn x
  have hnb : P.nb (List.ofFn x).tail = P.r := by
    unfold nb; rw [hl, Nat.mul_div_cancel _ P.d_pos]
  have hpart : P.part (List.ofFn x).tail = [] := by
    unfold part; rw [hnb, ← hl]; exact List.drop_of_length_le le_rfl
  simp only [oracle, massF, ite_eq_right (show ¬ P.r * P.d < (List.ofFn x).tail.length by omega),
    ite_eq_left hpart, hnb, Nat.sub_self, pow_zero, mul_one]

theorem oracle_long (T : P.Tables) {u : List Bool} (hu : P.N < u.length) : P.oracle T u = 0 := by
  cases u with
  | nil => simp at hu
  | cons a rest =>
      simp only [oracle]
      rw [ite_eq_left (by simp [N] at hu; omega)]

/-- `pw-lem:oracle`: the fixed oracle `h_θ` is a pointwise factor-`9/4` guide for `μ_θ`
(`eq:pw-model`), since `9/20 > 4/9` and `20/9 < 9/4`. -/
theorem oracle_pwLegal {B : Bool} {T : P.Tables} (hv : P.Valid B T) :
    PwLegal (9 / 4) (P.target T) (P.oracle T) := by
  refine ⟨⟨P.oracle_nonneg T, rfl, P.oracle_leaf T, fun u hu => P.oracle_long T hu⟩, ?_⟩
  intro u hu
  obtain ⟨h1, h2⟩ := P.oracle_bounds hv hu
  have hm := mass_nonneg (P.target_nonneg T) u
  constructor <;> nlinarith

end Prm

end LearningGuided.PointwiseLB
