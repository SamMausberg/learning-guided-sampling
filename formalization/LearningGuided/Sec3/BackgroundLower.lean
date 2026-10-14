import LearningGuided.Sec3.Background
import LearningGuided.Sec3.Comb

/-!
# Arbitrary known backgrounds: the lower bound and Theorem `thm:background`

The hard background of the lower bounds of `thm:background` and `prop:background-pointwise`:
for `d < n` and `ℓ = n - d`,
`ν = (15/16)(U_d ⊗ δ_{0^ℓ}) + (1/16)U_n` (full support), with the `K = 2^d ℓ` atom locations
`x_{y,j} = y0^{j-1}10^{ℓ-j}`. The guides answer every word of length at most `d` and every proper
prefix `y0^t` with the background mass (Lemma `lem:public-capacity`) and every other word exactly.

* `blockBg_mass_pub`: every public word has background mass at least `15/(16H)`, `H = 2^d`;
* `blockGuide_safe`: safety with factor `4/3` and capacity at most `263/120 < 9/4` when
  `α²H ≤ 1`; `blockGuide_pw`: pointwise factor `4/3` when `αH ≤ 1/4`;
* `block_lower`: equality counting and the zero-query obstruction give
  `q ≥ (3/16)(1 + α m)` for the `m` selected atoms;
* `two_regime` (the comparison `αK ≍ α⁻¹ log(1+2^nα²)`), `background_lower`, `background_rate`
  (Theorem `thm:background`), and `Qatom` with `Qatom_rate`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### The hard background -/

/-- `U_d ⊗ δ_{0^{n-d}}`: uniform on the first `d` bits, zeros afterwards. -/
noncomputable def padUnif (n d : ℕ) : Str n → ℝ :=
  fun y => ∑ θ : Str d, ((2 : ℝ) ^ d)⁻¹ * dirac (spikeAtom n θ) y

/-- `ν = (15/16)(U_d ⊗ δ_{0^ℓ}) + (1/16)U_n`. -/
noncomputable def blockBg (n d : ℕ) : Str n → ℝ :=
  fun y => 15 / 16 * padUnif n d y + 1 / 16 * unif n y

theorem padUnif_nonneg (d : ℕ) (y : Str n) : 0 ≤ padUnif n d y :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (by positivity) ((isDist_dirac _).1 y)

theorem isDist_padUnif (n d : ℕ) : IsDist (padUnif n d) := by
  refine ⟨padUnif_nonneg d, ?_⟩
  unfold padUnif
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (isDist_dirac _).2, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem isDist_blockBg (n d : ℕ) : IsDist (blockBg n d) := by
  have := isDist_mix (isDist_padUnif n d) (isDist_unif n) (a := 1 / 16) (by norm_num)
    (by norm_num)
  convert this using 2
  norm_num [blockBg]

theorem blockBg_pos (d : ℕ) (y : Str n) : 0 < blockBg n d y := by
  unfold blockBg unif
  have := padUnif_nonneg (n := n) d y
  have : (0 : ℝ) < 1 / 16 * ((2 : ℝ) ^ n)⁻¹ := by positivity
  linarith

/-- If `u` is a prefix of some padded string `θ0^{n-d}`, then `ν(u) ≥ 15/(16·2^d)`. -/
theorem blockBg_mass_ge {d : ℕ} {u : List Bool} {θ : Str d} (hu : IsPre u (spikeAtom n θ)) :
    15 / 16 * ((2 : ℝ) ^ d)⁻¹ ≤ mass (blockBg n d) u := by
  have h1 : ((2 : ℝ) ^ d)⁻¹ ≤ padUnif n d (spikeAtom n θ) := by
    unfold padUnif
    calc ((2 : ℝ) ^ d)⁻¹ = ((2 : ℝ) ^ d)⁻¹ * dirac (spikeAtom n θ) (spikeAtom n θ) := by
          simp [dirac]
      _ ≤ ∑ θ' : Str d, ((2 : ℝ) ^ d)⁻¹ * dirac (spikeAtom n θ') (spikeAtom n θ) :=
          Finset.single_le_sum (f := fun θ' => ((2 : ℝ) ^ d)⁻¹ * dirac (spikeAtom n θ')
            (spikeAtom n θ)) (fun θ' _ => mul_nonneg (by positivity) ((isDist_dirac _).1 _))
            (Finset.mem_univ θ)
  have h2 : blockBg n d (spikeAtom n θ) ≤ mass (blockBg n d) u := by
    unfold mass
    calc blockBg n d (spikeAtom n θ) =
        if IsPre u (spikeAtom n θ) then blockBg n d (spikeAtom n θ) else 0 := by
          rw [ite_eq_left hu]
      _ ≤ ∑ y, if IsPre u y then blockBg n d y else 0 :=
          Finset.single_le_sum (f := fun y => if IsPre u y then blockBg n d y else 0)
            (fun y _ => by split_ifs <;> simp [(isDist_blockBg n d).1 y]) (Finset.mem_univ _)
  have h3 : 15 / 16 * padUnif n d (spikeAtom n θ) ≤ blockBg n d (spikeAtom n θ) := by
    unfold blockBg unif
    have : (0 : ℝ) ≤ 1 / 16 * ((2 : ℝ) ^ n)⁻¹ := by positivity
    linarith
  linarith

/-- The public words: proper prefixes of the form `w` (`|w| ≤ d`) or `y0^t`. -/
def blockPub (n d : ℕ) (u : List Bool) : Prop :=
  u.length < n ∧ ∀ i (hi : i < u.length), d ≤ i → u[i] = false

theorem blockPub_isPre {d : ℕ} {u : List Bool} (hu : blockPub n d u) :
    IsPre u (spikeAtom n (strOf d u)) := by
  unfold IsPre
  rw [List.prefix_iff_getElem?]
  intro i hi
  have hin : i < n := by have := hu.1; omega
  have key : spikeAtom n (strOf d u) ⟨i, hin⟩ = u[i] := by
    rw [spikeAtom_apply]
    by_cases hid : i < d
    · rw [dite_eq_left hid]
      simp [strOf, List.getD_eq_getElem?_getD, hi]
    · rw [dite_eq_right hid]
      exact (hu.2 i hi (by omega)).symm
  simp [hin, key]

/-- `thm:background`: every public word has background mass at least `15/(16H)`. -/
theorem blockBg_mass_pub {d : ℕ} {u : List Bool} (hu : blockPub n d u) :
    15 / 16 * ((2 : ℝ) ^ d)⁻¹ ≤ mass (blockBg n d) u :=
  blockBg_mass_ge (blockPub_isPre hu)

/-- The atom `x_{y,j} = y0^{j-1}10^{ℓ-j}` (with `j` counted from `0`). -/
def blockAtom (n d : ℕ) (θ : Str d × Fin (n - d)) : Str n :=
  fun i => if h : i.val < d then θ.1 ⟨i.val, h⟩ else decide (i.val = d + θ.2.val)

theorem blockAtom_injective {d : ℕ} (hd : d ≤ n) : Function.Injective (blockAtom n d) := by
  rintro ⟨y, j⟩ ⟨y', j'⟩ h
  have hj : j = j' := by
    have := congrFun h ⟨d + j.val, by omega⟩
    simp only [blockAtom, show ¬ d + j.val < d by omega, ↓reduceDIte, decide_true] at this
    exact Fin.ext (by simpa using this.symm)
  subst hj
  have hy : y = y' := by
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [blockAtom, i.2] using this
  rw [hy]

/-- The atom key a public prefix cannot single out: each nonpublic word is a prefix of at most
one atom. -/
theorem blockAtom_uniq {d : ℕ} (hd : d ≤ n) (u : List Bool) (hu : ¬ blockPub n d u)
    (θ θ' : Str d × Fin (n - d)) (h1 : IsPre u (blockAtom n d θ))
    (h2 : IsPre u (blockAtom n d θ')) : θ = θ' := by
  have hlen := h1.length_le
  by_cases hfull : u.length = n
  · have e1 : u = List.ofFn (blockAtom n d θ) := h1.eq_of_length (by simp [hfull])
    have e2 : u = List.ofFn (blockAtom n d θ') := h2.eq_of_length (by simp [hfull])
    exact blockAtom_injective hd (List.ofFn_injective (e1.symm.trans e2))
  · have hex : ∃ i, ∃ hi : i < u.length, d ≤ i ∧ u[i] = true := by
      by_contra hno
      refine hu ⟨by omega, fun i hi hdi => ?_⟩
      cases hb : u[i]
      · rfl
      · exact absurd ⟨i, hi, hdi, hb⟩ hno
    obtain ⟨i, hi, hdi, hti⟩ := hex
    obtain ⟨y, j⟩ := θ
    obtain ⟨y', j'⟩ := θ'
    have e1 := isPre_getElem h1 hi
    have e2 := isPre_getElem h2 hi
    rw [hti] at e1 e2
    simp only [blockAtom, show ¬ i < d by omega, ↓reduceDIte] at e1 e2
    have hj1 : i = d + j.val := by simpa using e1.symm
    have hj2 : i = d + j'.val := by simpa using e2.symm
    have hj : j = j' := Fin.ext (by omega)
    subst hj
    have hy : y = y' := by
      funext k
      have f1 := isPre_getElem h1 (i := k.val) (by have := k.2; omega)
      have f2 := isPre_getElem h2 (i := k.val) (by have := k.2; omega)
      simp only [blockAtom, k.2, ↓reduceDIte] at f1 f2
      exact f1.symm.trans f2
    rw [hy]

/-- The hard guide for the key `θ`. -/
noncomputable def blockGuide (n d : ℕ) (α : ℝ) (θ : Str d × Fin (n - d)) : Guide :=
  pubGuide (blockBg n d) α (blockAtom n d θ) (blockPub n d)

theorem eqStructure_block {d : ℕ} (hd : d ≤ n) (α : ℝ) :
    EqualityStructure fun θ : Str d × Fin (n - d) => blockGuide n d α θ :=
  eqStructure_pub (blockBg n d) α (blockAtom n d) (blockPub n d)
    fun u hu θ θ' h1 h2 => blockAtom_uniq hd u hu θ θ' h1 h2

/-- `lem:public-capacity` for the hard guide of `thm:background`: factor `4/3`, and stopped
capacity at most `1 + α - 2α² + 16α²H/15 ≤ 263/120 < 9/4` when `α²H ≤ 1`. -/
theorem blockGuide_safe {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hH : α ^ 2 * 2 ^ d ≤ 1) (θ : Str d × Fin (n - d)) :
    IsOracle (atomTarget (blockBg n d) α (blockAtom n d θ)) (blockGuide n d α θ) ∧
    (∀ u, blockGuide n d α θ u ≤ 4 / 3 * mass (atomTarget (blockBg n d) α (blockAtom n d θ)) u) ∧
    CapLE (atomTarget (blockBg n d) α (blockAtom n d θ)) (blockGuide n d α θ) (263 / 120) := by
  refine ⟨pubGuide_isOracle (isDist_blockBg n d) hα0.le (by linarith) _ fun u hu => hu.1,
    fun u => pubGuide_le (isDist_blockBg n d) hα0.le hα _ _ u, ?_⟩
  refine pubGuide_capLE (isDist_blockBg n d) (blockBg_pos d) hα0.le (by linarith) _
    (by norm_num) fun t _ hp => ?_
  have hm := blockBg_mass_pub hp
  set m := mass (blockBg n d) (pre (blockAtom n d θ) t)
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm
  have h1 : α ^ 2 / m ≤ 16 / 15 := by
    rw [div_le_iff₀ hmpos]
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    have : α ^ 2 ≤ ((2 : ℝ) ^ d)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) h2d] at *
      rw [← one_div, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  have h2 : 0 ≤ (1 - α) * α * m := by
    have : 0 ≤ (1 - α) * α := mul_nonneg (by linarith) hα0.le
    positivity
  nlinarith

theorem blockGuide_legal_safe {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hH : α ^ 2 * 2 ^ d ≤ 1) (θ : Str d × Fin (n - d)) :
    SafeLegal (9 / 4) (9 / 4) (atomTarget (blockBg n d) α (blockAtom n d θ))
      (blockGuide n d α θ) := by
  obtain ⟨h1, h2, h3⟩ := blockGuide_safe hα0 hα hH θ
  refine ⟨h1, fun u _ => (h2 u).trans ?_, CapLE.mono h3 (by norm_num)⟩
  have := mass_nonneg (isDist_atomTarget (isDist_blockBg n d) hα0.le (by linarith)
    (blockAtom n d θ)).1 u
  linarith

/-- `prop:background-pointwise`: the hard guide is pointwise factor `4/3` when `αH ≤ 1/4`. -/
theorem blockGuide_pw {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hH : α * 2 ^ d ≤ 1 / 4) (θ : Str d × Fin (n - d)) :
    PwLegal (4 / 3) (atomTarget (blockBg n d) α (blockAtom n d θ)) (blockGuide n d α θ) := by
  refine pubGuide_pwLegal (isDist_blockBg n d) hα0.le hα _ (fun u hu => hu.1) fun u hu => ?_
  have hm := blockBg_mass_pub hu
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have : 3 * α ≤ 15 / 16 * ((2 : ℝ) ^ d)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ h2d]
    nlinarith
  linarith

theorem blockGuide_legal_pw {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hH : α * 2 ^ d ≤ 1 / 4) (θ : Str d × Fin (n - d)) :
    PwLegal (9 / 4) (atomTarget (blockBg n d) α (blockAtom n d θ)) (blockGuide n d α θ) :=
  PwLegal.mono (by norm_num) (by norm_num)
    (isDist_atomTarget (isDist_blockBg n d) hα0.le (by linarith) _) (blockGuide_pw hα0 hα hH θ)

/-! ### The counting lower bound -/

/-- The zero-query obstruction for any atom class with two distinct atoms. -/
theorem atom_zero_query {Legal : (Str n → ℝ) → Guide → Prop} {ν : Str n → ℝ}
    {S : Finset (Str n)} {α δ : ℝ} (hS : 2 ≤ S.card) (hα0 : 0 ≤ α) (hδ : 2 * δ < α)
    (hex : ∀ x : Str n, Legal (atomTarget ν α x) (exactGuide (atomTarget ν α x)))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (atomClass ν S α) δ q A) : 1 ≤ q := by
  by_contra hq
  have hq0 : q = 0 := by omega
  subst hq0
  obtain ⟨x, hx, x', hx', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have h1 := hA _ ⟨x, hx, rfl⟩ _ (hex x)
  have h2 := hA _ ⟨x', hx', rfl⟩ _ (hex x')
  exact zero_query_obstruction (by rw [tv_atomTarget hα0 hne]; exact hδ) A h1.1 h2.1 h1.2 h2.2

theorem block_overlap {d : ℕ} (hd : d ≤ n) (T : Finset (Str d × Fin (n - d))) (y : Str n) :
    (T.filter fun θ => y ∈ (({blockAtom n d θ} : Finset (Str n)) : Set (Str n))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
  exact blockAtom_injective hd (ha.2.symm.trans hb.2)

/-- The keys whose atoms belong to the candidate set. -/
noncomputable def blockSel (n d : ℕ) (S : Finset (Str n)) : Finset (Str d × Fin (n - d)) :=
  Finset.univ.filter fun θ => blockAtom n d θ ∈ S

/-- `thm:background`, counting bound: equality counting on the selected atoms plus the zero-query
obstruction: in any model in which the hard guides of the selected keys and the exact guides are
legal, a `δ`-accurate algorithm (`δ ≤ α/4`) for a class over the hard background containing `m` hard
atoms has `q ≥ (3/16)(1 + αm)`. -/
theorem block_lower {Legal : (Str n → ℝ) → Guide → Prop} {d : ℕ} (hd : d ≤ n) {α δ : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδα : δ ≤ α / 4) {S : Finset (Str n)} (hS : 2 ≤ S.card)
    (hlegal : ∀ θ ∈ blockSel n d S,
      Legal (atomTarget (blockBg n d) α (blockAtom n d θ)) (blockGuide n d α θ))
    (hex : ∀ x : Str n, Legal (atomTarget (blockBg n d) α x)
      (exactGuide (atomTarget (blockBg n d) α x)))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (atomClass (blockBg n d) S α) δ q A) :
    3 / 16 * (1 + α * (blockSel n d S).card) ≤ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast atom_zero_query hS hα0.le (by linarith) hex hA
  have hmem : ∀ θ ∈ blockSel n d S,
      atomTarget (blockBg n d) α (blockAtom n d θ) ∈ atomClass (blockBg n d) S α :=
    fun θ hθ => ⟨_, (Finset.mem_filter.mp hθ).2, rfl⟩
  have hsum := equality_counting (fun θ => blockGuide n d α θ) (eqStructure_block hd α)
    (fun θ => (({blockAtom n d θ} : Finset (Str n)) : Set (Str n))) 1 A (blockSel n d S) q
    (fun y => by convert block_overlap hd (blockSel n d S) y)
    (fun θ hθ => (hA _ (hmem θ hθ) _ (hlegal θ hθ)).1)
  have hp : ∀ θ ∈ blockSel n d S, α - δ ≤ (probE (A.run (blockGuide n d α θ))
      (({blockAtom n d θ} : Finset (Str n)) : Set (Str n))).toReal := by
    intro θ hθ
    have := prob_ge_of_tv (isDist_atomTarget (isDist_blockBg n d) hα0.le (by linarith) _)
      (hA _ (hmem θ hθ) _ (hlegal θ hθ)).2 {blockAtom n d θ}
    rw [Finset.sum_singleton, atomTarget_apply, ite_eq_left rfl] at this
    have : 0 ≤ (1 - α) * blockBg n d (blockAtom n d θ) :=
      mul_nonneg (by linarith) ((isDist_blockBg n d).1 _)
    linarith
  have h := card_mul_le_of_sum (blockSel n d S) _ (by simp) (fun θ => probE_le_one _ _) hsum hp
  have h2 : ((q : ℝ≥0∞) + ((1 : ℕ) : ℝ≥0∞)).toReal = q + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [h2] at h
  have hc0 : (0 : ℝ) ≤ (blockSel n d S).card := Nat.cast_nonneg _
  nlinarith

/-- A candidate set of size `M` (with `2 ≤ M ≤ 2^n`) containing `min{M, K}` hard atoms. -/
theorem exists_block_set {d : ℕ} (hd : d ≤ n) {M : ℕ} (hMn : M ≤ 2 ^ n) :
    ∃ S : Finset (Str n), S.card = M ∧ min M (2 ^ d * (n - d)) ≤ (blockSel n d S).card := by
  classical
  set L := Finset.univ.image (blockAtom n d) with hL
  have hLcard : L.card = 2 ^ d * (n - d) := by
    rw [hL, Finset.card_image_of_injective _ (blockAtom_injective hd)]
    simp
  rcases le_total M L.card with hML | hML
  · obtain ⟨S, hSL, hScard⟩ := Finset.exists_subset_card_eq hML
    refine ⟨S, hScard, ?_⟩
    have : (blockSel n d S).image (blockAtom n d) = S := by
      ext x
      simp only [Finset.mem_image, blockSel, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨θ, hθ, rfl⟩
        exact hθ
      · intro hx
        obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp (hSL hx)
        exact ⟨θ, hx, rfl⟩
    have hc := Finset.card_image_of_injective (blockSel n d S) (blockAtom_injective hd)
    rw [this, hScard] at hc
    rw [← hc]
    exact min_le_left _ _
  · have huniv : (Finset.univ : Finset (Str n)).card = 2 ^ n := by simp
    obtain ⟨S, hLS, -, hScard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ L) hML
      (by rw [huniv]; exact hMn)
    refine ⟨S, hScard, ?_⟩
    have : blockSel n d S = Finset.univ := by
      ext θ
      simp only [blockSel, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hLS (Finset.mem_image_of_mem _ (Finset.mem_univ θ))
    rw [this, ← hLcard, Finset.card_univ, ← Finset.card_univ]
    calc min M L.card ≤ L.card := min_le_right _ _
      _ = (Finset.univ.image (blockAtom n d)).card := rfl
      _ ≤ _ := Finset.card_image_le

/-! ### The two-regime comparison -/

/-- The depth `d = min{n-1, ⌊log₂ B²⌋}`, `B = α⁻¹`, of the lower bound of `thm:background`. -/
noncomputable def bgDepth (n : ℕ) (α : ℝ) : ℕ := min (n - 1) ⌊Real.logb 2 (α⁻¹ ^ 2)⌋₊

theorem log_le_two_mul {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 2 ^ ℓ) :
    Real.log (1 + z) ≤ 2 * ℓ := by
  have h1 : 1 + z ≤ 2 ^ (ℓ + 1) := by
    have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have h2 := Real.log_le_log (by linarith) h1
  rw [Real.log_pow] at h2
  have h3 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  push_cast at h2
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- `thm:background`, two-regime comparison: with `d = min{n-1, ⌊log₂ B²⌋}`,
`B = α⁻¹`, `H = 2^d`, `ℓ = n - d`, `K = Hℓ` and `z = 2^nα²`,
`(1/4) B log(1+z) ≤ αK ≤ 3 B log(1+z)`. -/
theorem two_regime {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hn : 1 ≤ n) :
    1 / 4 * (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)) ≤
      α * (2 ^ bgDepth n α * (n - bgDepth n α : ℕ)) ∧
    α * (2 ^ bgDepth n α * (n - bgDepth n α : ℕ)) ≤
      3 * (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)) := by
  set B := α⁻¹ with hB
  set z : ℝ := 2 ^ n * α ^ 2 with hz
  have hαB : α * B = 1 := mul_inv_cancel₀ hα0.ne'
  have hB4 : 4 ≤ B := by
    rw [hB, le_inv_comm₀ (by norm_num) hα0]
    linarith
  have hy : 1 ≤ B ^ 2 := by nlinarith
  obtain ⟨hf1, hf2⟩ := floor_logb_two_spec hy
  set L := ⌊Real.logb 2 (B ^ 2)⌋₊ with hL
  have hz0 : 0 < z := by positivity
  have hlog0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  unfold bgDepth
  rw [← hB, ← hL]
  rcases le_or_gt (n - 1) L with h | h
  · rw [min_eq_left h, show n - (n - 1) = 1 by omega]
    have hn1 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hαK : α * (2 ^ (n - 1) * ((1 : ℕ) : ℝ)) = B * z / 2 := by
      rw [hz, hn1, hB]
      field_simp
      ring
    have hzle : z ≤ 2 := by
      have : (2 : ℝ) ^ (n - 1) ≤ B ^ 2 := (pow_le_pow_right₀ (by norm_num) h).trans hf1
      rw [hz, hn1]
      have hα2 : α ^ 2 * B ^ 2 = 1 := by rw [← mul_pow, hαB, one_pow]
      nlinarith
    rw [hαK]
    have hBpos : 0 < B := by linarith
    constructor
    · have := Real.log_le_sub_one_of_pos (x := 1 + z) (by linarith)
      nlinarith
    · have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 + z) (by linarith)
      have h2 : z / 3 ≤ 1 - (1 + z)⁻¹ := by
        rw [show 1 - (1 + z)⁻¹ = z / (1 + z) by field_simp; ring]
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        nlinarith
      nlinarith
  · rw [min_eq_right h.le]
    set ℓ := n - L with hℓ
    have hℓ2 : 2 ≤ ℓ := by omega
    have hnL : (2 : ℝ) ^ n = 2 ^ L * 2 ^ ℓ := by
      rw [← pow_add]
      congr 1
      omega
    have hα2 : α ^ 2 * B ^ 2 = 1 := by rw [← mul_pow, hαB, one_pow]
    have hBpos : 0 < B := by linarith
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    -- `2^{ℓ-1} < z ≤ 2^ℓ`
    have hzle : z ≤ 2 ^ ℓ := by
      rw [hz, hnL]
      have : (2 : ℝ) ^ L * α ^ 2 ≤ 1 := by nlinarith
      have h2ℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
      nlinarith
    have hzgt : 2 ^ ℓ < 2 * z := by
      rw [hz, hnL]
      have h1 : 1 < 2 * (2 : ℝ) ^ L * α ^ 2 := by
        have e : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
        rw [e] at hf2
        nlinarith
      have h2ℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
      nlinarith
    have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
    constructor
    · -- `αK > Bℓ/2 ≥ B log(1+z)/4`
      have hK : B * ℓ / 2 ≤ α * (2 ^ L * (ℓ : ℝ)) := by
        have : B ^ 2 / 2 ≤ (2 : ℝ) ^ L := by
          have e : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
          rw [e] at hf2
          linarith
        have e : α * (B ^ 2 / 2 * ℓ) = B * ℓ / 2 := by
          rw [show α * (B ^ 2 / 2 * ℓ) = (α * B) * B * ℓ / 2 by ring, hαB]
          ring
        rw [← e]
        gcongr
      have hlog := log_le_two_mul (by omega : 1 ≤ ℓ) hz0.le hzle
      nlinarith
    · -- `αK ≤ Bℓ ≤ 3 B log(1+z)`
      have hK : α * (2 ^ L * (ℓ : ℝ)) ≤ B * ℓ := by
        have e : α * (B ^ 2 * ℓ) = B * ℓ := by
          rw [show α * (B ^ 2 * ℓ) = (α * B) * B * ℓ by ring, hαB, one_mul]
        rw [← e]
        gcongr
      have hz2 : 2 ≤ z := by
        have : (4 : ℝ) ≤ 2 ^ ℓ := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ2
        linarith
      -- `(ℓ - 1) log 2 < log z`
      have hlz : ((ℓ : ℝ) - 1) * Real.log 2 ≤ Real.log z := by
        have h1 : (2 : ℝ) ^ (ℓ - 1) ≤ z := by
          have : (2 : ℝ) ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          linarith
        have := Real.log_le_log (by positivity) h1
        rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ ℓ)] at this
        push_cast at this
        linarith
      have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hlogz2 : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
      have hz1 : Real.log z ≤ Real.log (1 + z) := Real.log_le_log hz0 (by linarith)
      have hℓlog : (ℓ : ℝ) ≤ 3 * Real.log (1 + z) := by
        have hlz2 : (ℓ : ℝ) * Real.log 2 ≤ 2 * Real.log z := by nlinarith
        nlinarith
      nlinarith

/-! ### Theorem `thm:background` -/

/-- `thm:background`, lower bound: there are a full-support background and a set of `M`
atoms for which every `δ`-accurate algorithm in the safe model has
`q ≥ (3/64)(1 + min{αM, α⁻¹ log(1+2^nα²)})`. -/
theorem background_lower {M : ℕ} {α δ : ℝ} (hn : 1 ≤ n) (hM : 2 ≤ M) (hMn : M ≤ 2 ^ n)
    (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α / 4) :
    ∃ S : Finset (Str n), S.card = M ∧
      3 / 64 * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) ≤
        (Qsafe (atomClass (blockBg n (bgDepth n α)) S α) δ : ℝ) := by
  set d := bgDepth n α with hd
  have hdn : d < n := by
    have : d ≤ n - 1 := min_le_left _ _
    omega
  obtain ⟨S, hScard, hsel⟩ := exists_block_set hdn.le hMn
  refine ⟨S, hScard, ?_⟩
  have hH : α ^ 2 * 2 ^ d ≤ 1 := by
    have hy : 1 ≤ α⁻¹ ^ 2 := by
      have : 4 ≤ α⁻¹ := by rw [le_inv_comm₀ (by norm_num) hα0]; linarith
      nlinarith
    have h1 := (floor_logb_two_spec hy).1
    have h2 : (2 : ℝ) ^ d ≤ 2 ^ ⌊Real.logb 2 (α⁻¹ ^ 2)⌋₊ :=
      pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
    have h3 : α ^ 2 * α⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hα0.ne', one_pow]
    have : (0 : ℝ) ≤ α ^ 2 := by positivity
    nlinarith
  have hdist : ∀ x : Str n, IsDist (atomTarget (blockBg n d) α x) := fun x =>
    isDist_atomTarget (isDist_blockBg n d) hα0.le (by linarith) x
  have hS2 : 2 ≤ S.card := by omega
  have hex : ∃ q A, Solves (SafeLegal (9 / 4) (9 / 4)) (atomClass (blockBg n d) S α) δ q A :=
    ⟨_, _, solves_mono_delta hδ0 (background_partition (by norm_num) (by norm_num) hα0
      (by linarith) (isDist_blockBg n d) (Finset.card_pos.mp (by omega))).2.2.2⟩
  have hlow := le_Qcx (b := ⌈3 / 16 * (1 + α * (blockSel n d S).card)⌉₊) hex fun q A hA => by
    rw [Nat.ceil_le]
    exact block_lower hdn.le hα0 hα hδα hS2 (fun θ _ => blockGuide_legal_safe hα0 hα hH θ)
      (fun x => safeLegal_exactGuide (by norm_num) (by norm_num) (hdist x)) hA
  have hQ : 3 / 16 * (1 + α * (blockSel n d S).card) ≤
      (Qsafe (atomClass (blockBg n d) S α) δ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlow)
  obtain ⟨hcmp, -⟩ := two_regime hα0 hα hn
  rw [← hd] at hcmp
  have hsel' : (min (M : ℝ) (2 ^ d * (n - d : ℕ))) ≤ (blockSel n d S).card := by
    exact_mod_cast hsel
  have hAM : 0 ≤ α * M := by positivity
  have hz0 : (0 : ℝ) ≤ 2 ^ n * α ^ 2 := by positivity
  have hlog0 : 0 ≤ α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2) :=
    mul_nonneg (inv_nonneg.mpr hα0.le) (Real.log_nonneg (by linarith))
  have hmin0 : 0 ≤ min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)) := le_min hAM hlog0
  have hmin : 1 / 4 * min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)) ≤
      α * (blockSel n d S).card := by
    have h1 : 1 / 4 * min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)) ≤
        min (α * M) (α * (2 ^ d * (n - d : ℕ))) := by
      have m1 := min_le_left (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))
      have m2 := min_le_right (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))
      exact le_min (by linarith) (by linarith)
    calc 1 / 4 * min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))
        ≤ min (α * M) (α * (2 ^ d * (n - d : ℕ))) := h1
      _ = α * min (M : ℝ) (2 ^ d * (n - d : ℕ)) := (mul_min_of_nonneg _ _ hα0.le).symm
      _ ≤ α * (blockSel n d S).card := mul_le_mul_of_nonneg_left hsel' hα0.le
  linarith

/-- `thm:background`: for `n ≥ 1`, `2 ≤ M ≤ 2^n`, `0 < α ≤ 1/4`, `0 ≤ δ ≤ α/4`, with the
absolute constants `c₁ = 3/64`, `c₂ = 75`: every known background `ν` and every known set `S` of
`M` distinct atoms have `Q_safe ≤ c₂(1 + min{αM, α⁻¹ log(1+2^nα²)})` (by an exact sampler), and
some full-support background and some set of `M` atoms have `Q_safe ≥ c₁(…)`. -/
theorem background_rate : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n M : ℕ) (α δ : ℝ), 1 ≤ n → 2 ≤ M → M ≤ 2 ^ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ →
      δ ≤ α / 4 →
      (∀ ν : Str n → ℝ, IsDist ν → ∀ S : Finset (Str n), S.card = M →
        (Qsafe (atomClass ν S α) δ : ℝ) ≤
          c₂ * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)))) ∧
      (∃ ν : Str n → ℝ, IsDist ν ∧ (∀ y, 0 < ν y) ∧ ∃ S : Finset (Str n), S.card = M ∧
        c₁ * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) ≤
          (Qsafe (atomClass ν S α) δ : ℝ)) := by
  refine ⟨3 / 64, 75, by norm_num, by norm_num,
    fun n M α δ hn hM hMn hα0 hα hδ0 hδα => ⟨fun ν hν S hS => ?_, ?_⟩⟩
  · have := background_upper hα0 hα hδ0 hν (S := S) (by omega)
    rwa [hS] at this
  · obtain ⟨S, hS, hlow⟩ := background_lower hn hM hMn hα0 hα hδ0 hδα
    exact ⟨_, isDist_blockBg n _, blockBg_pos _, S, hS, hlow⟩

/-- `Q_atom(n,M,α,δ)`: the supremum of `Q_safe` over known backgrounds `ν` on `{0,1}^n` and
known sets `S` of `M` distinct atoms. -/
noncomputable def Qatom (n M : ℕ) (α δ : ℝ) : ℕ :=
  sSup {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n), IsDist ν ∧ S.card = M ∧
    q = Qsafe (atomClass ν S α) δ}

/-- `thm:background`, `eq:background-rate`, for the supremum `Q_atom` itself:
`Q_atom(n,M,α,δ) = Θ(1 + min{αM, α⁻¹ log(1+2^nα²)})` with absolute constants. -/
theorem Qatom_rate : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n M : ℕ) (α δ : ℝ), 1 ≤ n → 2 ≤ M → M ≤ 2 ^ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ →
      δ ≤ α / 4 →
      c₁ * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) ≤ (Qatom n M α δ : ℝ) ∧
      (Qatom n M α δ : ℝ) ≤ c₂ * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := background_rate
  refine ⟨c₁, c₂, hc₁, hc₂, fun n M α δ hn hM hMn hα0 hα hδ0 hδα => ?_⟩
  obtain ⟨hup, ν₀, hν₀, -, S₀, hS₀, hlow⟩ := h n M α δ hn hM hMn hα0 hα hδ0 hδα
  set r := c₂ * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2)))
  have hbdd : BddAbove {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n), IsDist ν ∧ S.card = M ∧
      q = Qsafe (atomClass ν S α) δ} := by
    refine ⟨⌊r⌋₊, fun q ⟨ν, S, hν, hS, hq⟩ => ?_⟩
    rw [hq]
    exact Nat.le_floor (hup ν hν S hS)
  have hmem : Qsafe (atomClass ν₀ S₀ α) δ ∈ {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n),
      IsDist ν ∧ S.card = M ∧ q = Qsafe (atomClass ν S α) δ} := ⟨ν₀, S₀, hν₀, hS₀, rfl⟩
  constructor
  · exact hlow.trans (by exact_mod_cast le_csSup hbdd hmem)
  · have : Qatom n M α δ ≤ ⌊r⌋₊ := csSup_le ⟨_, hmem⟩ fun q ⟨ν, S, hν, hS, hq⟩ => by
      rw [hq]
      exact Nat.le_floor (hup ν hν S hS)
    have hr : (0 : ℝ) ≤ r := by
      have := hup ν₀ hν₀ S₀ hS₀
      exact (Nat.cast_nonneg _).trans this
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hr)

end LearningGuided.Sec3
