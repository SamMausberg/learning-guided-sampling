import LearningGuided.Sec2.PublicCapacity

/-!
# The class `𝓗_ℓ` of Theorem `thm:fixed-class`

For `ℓ ≥ 1`, strings have length `n = ℓ + 4`. For `y ∈ {0,1}^4` and `1 ≤ j ≤ ℓ` the atom is
`x_{y,j} = y 0^{j-1} 1 0^{ℓ-j}`; here the index is shifted to `j ∈ {0,…,ℓ-1}` (`Fin ℓ`), so the
atom has its one at position `4 + j`. The background is
`ν = (15/16)(U_4 ⊗ δ_{0^ℓ}) + (1/16) U_n` and the targets are
`μ_{y,j} = (3/4) ν + (1/4) δ_{x_{y,j}}`.
The hard safe guides use Lemma `lem:public-capacity` with public answers on every word of length
at most four and on every proper prefix `y 0^t`.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec2

/-- The background block `y 0^ℓ`. -/
def zblk (ℓ : ℕ) (y : Str 4) : Str (ℓ + 4) :=
  fun i => if h : i.1 < 4 then y ⟨i.1, h⟩ else false

/-- The atom `y 0^j 1 0^{ℓ-j-1}`, i.e. the paper's `x_{y,j+1}`. -/
def atomF (ℓ : ℕ) (y : Str 4) (j : ℕ) : Str (ℓ + 4) :=
  fun i => if h : i.1 < 4 then y ⟨i.1, h⟩ else decide (i.1 = 4 + j)

/-- `U_4 ⊗ δ_{0^ℓ}`. -/
noncomputable def rhoF (ℓ : ℕ) : Str (ℓ + 4) → ℝ :=
  fun x => ∑ y : Str 4, (1 / 16 : ℝ) * dirac (zblk ℓ y) x

/-- The background `ν = (15/16)(U_4 ⊗ δ_{0^ℓ}) + (1/16) U_n`. -/
noncomputable def nuF (ℓ : ℕ) : Str (ℓ + 4) → ℝ :=
  fun x => 15 / 16 * rhoF ℓ x + 1 / 16 * unif (ℓ + 4) x

/-- Keys `(y, j)`, `y ∈ {0,1}^4`, `j ∈ {0,…,ℓ-1}`; there are `M = 16ℓ` of them. -/
abbrev KeyF (ℓ : ℕ) := Str 4 × Fin ℓ

/-- The atom of a key. -/
def atomK (ℓ : ℕ) (κ : KeyF ℓ) : Str (ℓ + 4) := atomF ℓ κ.1 κ.2.1

/-- The target `μ_{y,j} = (3/4) ν + (1/4) δ_{x_{y,j}}`. -/
noncomputable def muF (ℓ : ℕ) (κ : KeyF ℓ) : Str (ℓ + 4) → ℝ := mixD (nuF ℓ) (1 / 4) (atomK ℓ κ)

/-- The class `𝓗_ℓ`. -/
def classF (ℓ : ℕ) : Set (Str (ℓ + 4) → ℝ) := Set.range (muF ℓ)

/-- The public prefixes: all proper prefixes whose bits after position four are zero, i.e. the
words of length at most four and the words `y 0^t`, `t < ℓ`. -/
def pubSetF (ℓ : ℕ) : Set (List Bool) :=
  {u | u.length < ℓ + 4 ∧ ∀ i (hi : i < u.length), 4 ≤ i → u[i] = false}

/-- The hard safe guide of a key (Lemma `lem:public-capacity` with `α = 1/4`). -/
noncomputable def hardF (ℓ : ℕ) (κ : KeyF ℓ) : Guide :=
  pubGuide (nuF ℓ) (1 / 4) (pubSetF ℓ) (atomK ℓ κ)

/-- The probe word `y 0^t`. -/
def grpWord (y : Str 4) (t : ℕ) : List Bool := List.ofFn y ++ List.replicate t false

/-! ### Elementary facts -/

theorem card_KeyF (ℓ : ℕ) : Fintype.card (KeyF ℓ) = 16 * ℓ := by
  simp [Fintype.card_prod]

theorem isDist_rhoF (ℓ : ℕ) : IsDist (rhoF ℓ) := by
  refine ⟨fun x => Finset.sum_nonneg fun y _ => ?_, ?_⟩
  · unfold dirac; split_ifs <;> norm_num
  · unfold rhoF
    rw [Finset.sum_comm]
    have : ∀ y : Str 4, ∑ x : Str (ℓ + 4), (1 / 16 : ℝ) * dirac (zblk ℓ y) x = 1 / 16 := by
      intro y
      rw [← Finset.mul_sum, (isDist_dirac (zblk ℓ y)).2, mul_one]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    norm_num

theorem mass_rhoF (ℓ : ℕ) (u : List Bool) :
    mass (rhoF ℓ) u = ∑ y : Str 4, (1 / 16 : ℝ) * (if IsPre u (zblk ℓ y) then 1 else 0) := by
  unfold rhoF
  rw [mass_finsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mass_smul, mass_dirac]

theorem isDist_nuF (ℓ : ℕ) : IsDist (nuF ℓ) := by
  have h := isDist_mix (isDist_rhoF ℓ) (isDist_unif (ℓ + 4)) (a := 1 / 16) (by norm_num)
    (by norm_num)
  have : nuF ℓ = fun x => (1 - 1 / 16) * rhoF ℓ x + 1 / 16 * unif (ℓ + 4) x := by
    funext x; unfold nuF; norm_num
  rw [this]; exact h

theorem nuF_ge (ℓ : ℕ) (x : Str (ℓ + 4)) : 1 / 16 * ((2 : ℝ) ^ (ℓ + 4))⁻¹ ≤ nuF ℓ x := by
  unfold nuF
  have := (isDist_rhoF ℓ).1 x
  simp only [unif]
  linarith

theorem nuF_pos (ℓ : ℕ) (x : Str (ℓ + 4)) : 0 < nuF ℓ x :=
  lt_of_lt_of_le (by positivity) (nuF_ge ℓ x)

theorem mass_nuF (ℓ : ℕ) (u : List Bool) :
    mass (nuF ℓ) u = 15 / 16 * mass (rhoF ℓ) u + 1 / 16 * mass (unif (ℓ + 4)) u :=
  mass_linear _ _ _ _ u

theorem isPre_zblk_unique {ℓ : ℕ} {u : List Bool} (hu : 4 ≤ u.length) {y y' : Str 4}
    (h : IsPre u (zblk ℓ y)) (h' : IsPre u (zblk ℓ y')) : y = y' := by
  rw [isPre_iff_getElem] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  funext i
  have e1 := h i.1 (by omega)
  have e2 := h' i.1 (by omega)
  simp only [zblk, i.2, dite_true] at e1 e2
  rw [← e1, ← e2]

/-- `U_4 ⊗ δ_{0^ℓ}` gives mass at most `1/16` to every word of length at least four. -/
theorem mass_rhoF_le {ℓ : ℕ} {u : List Bool} (hu : 4 ≤ u.length) :
    mass (rhoF ℓ) u ≤ 1 / 16 := by
  classical
  rw [mass_rhoF, ← Finset.mul_sum]
  have hcard : (Finset.univ.filter fun y : Str 4 => IsPre u (zblk ℓ y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact isPre_zblk_unique hu ha.2 hb.2
  rw [Finset.sum_boole]
  have : ((Finset.univ.filter fun y : Str 4 => IsPre u (zblk ℓ y)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  linarith

theorem mass_rhoF_ge {ℓ : ℕ} {u : List Bool} {y : Str 4} (h : IsPre u (zblk ℓ y)) :
    1 / 16 ≤ mass (rhoF ℓ) u := by
  rw [mass_rhoF]
  calc (1 / 16 : ℝ) = 1 / 16 * (if IsPre u (zblk ℓ y) then 1 else 0) := by simp [h]
    _ ≤ ∑ y : Str 4, (1 / 16 : ℝ) * (if IsPre u (zblk ℓ y) then 1 else 0) :=
        Finset.single_le_sum (f := fun y : Str 4 => (1 / 16 : ℝ) *
          (if IsPre u (zblk ℓ y) then 1 else 0))
          (fun y _ => by split_ifs <;> norm_num) (Finset.mem_univ y)

/-- Every public ancestor of an atom has background mass at least `15/256`. -/
theorem mass_nuF_ge_of_isPre_zblk {ℓ : ℕ} {u : List Bool} {y : Str 4}
    (h : IsPre u (zblk ℓ y)) : 15 / 256 ≤ mass (nuF ℓ) u := by
  rw [mass_nuF]
  have h1 := mass_rhoF_ge h
  have h2 := mass_nonneg (isDist_unif (ℓ + 4)).1 u
  linarith

theorem mass_nuF_le {ℓ : ℕ} {u : List Bool} (hu : 4 ≤ u.length) (hn : u.length ≤ ℓ + 4) :
    mass (nuF ℓ) u ≤ 1 / 16 := by
  rw [mass_nuF, mass_unif hn]
  have h1 := mass_rhoF_le (ℓ := ℓ) hu
  have h2 : ((2 : ℝ) ^ u.length)⁻¹ ≤ 1 / 16 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    calc (1 / 16 : ℝ)⁻¹ = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ u.length := pow_le_pow_right₀ (by norm_num) hu
  linarith

theorem atomF_apply_lt {ℓ : ℕ} (y : Str 4) (j : ℕ) (i : Fin (ℓ + 4)) (hi : i.1 < 4) :
    atomF ℓ y j i = y ⟨i.1, hi⟩ := by
  simp [atomF, hi]

theorem atomF_apply_ge {ℓ : ℕ} (y : Str 4) (j : ℕ) (i : Fin (ℓ + 4)) (hi : 4 ≤ i.1) :
    atomF ℓ y j i = decide (i.1 = 4 + j) := by
  simp [atomF, show ¬ i.1 < 4 by omega]

theorem atomK_injective (ℓ : ℕ) : Function.Injective (atomK ℓ) := by
  rintro ⟨y, j⟩ ⟨y', j'⟩ h
  simp only [atomK] at h
  have hy : y = y' := by
    funext i
    have := congrFun h ⟨i.1, by omega⟩
    simpa [atomF, i.2] using this
  have hj : j.1 = j'.1 := by
    have := congrFun h ⟨4 + j.1, by omega⟩
    rw [atomF_apply_ge _ _ _ (by simp), atomF_apply_ge _ _ _ (by simp)] at this
    simp only [decide_true] at this
    have := of_decide_eq_true this.symm
    omega
  subst hy
  rw [Prod.mk.injEq]
  exact ⟨rfl, Fin.ext hj⟩

theorem isDist_muF (ℓ : ℕ) (κ : KeyF ℓ) : IsDist (muF ℓ κ) :=
  isDist_mixD (isDist_nuF ℓ) (by norm_num) (by norm_num) _

theorem muF_pos (ℓ : ℕ) (κ : KeyF ℓ) (x : Str (ℓ + 4)) : 0 < muF ℓ κ x := by
  unfold muF mixD
  have := nuF_pos ℓ x
  have : 0 ≤ dirac (atomK ℓ κ) x := by unfold dirac; split_ifs <;> norm_num
  nlinarith

theorem muF_injective (ℓ : ℕ) : Function.Injective (muF ℓ) := by
  intro κ κ' h
  have h1 := congrFun h (atomK ℓ κ)
  simp only [muF, mixD, dirac, ite_true] at h1
  by_contra hne
  have hne' : atomK ℓ κ ≠ atomK ℓ κ' := fun e => hne (atomK_injective ℓ e)
  rw [ite_eq_right hne'] at h1
  linarith

theorem mass_muF (ℓ : ℕ) (κ : KeyF ℓ) (u : List Bool) :
    mass (muF ℓ κ) u = 3 / 4 * mass (nuF ℓ) u + 1 / 4 * (if IsPre u (atomK ℓ κ) then 1 else 0) := by
  rw [muF, mass_mixD]; norm_num

/-- The atom carries mass `1/4 + (3/4) ν(x) ≥ 1/4 + 3/(64 · 2^n)`. -/
theorem muF_atom_ge (ℓ : ℕ) (κ : KeyF ℓ) :
    1 / 4 + 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) ≤ muF ℓ κ (atomK ℓ κ) := by
  rw [muF, mixD_apply_self]
  have := nuF_ge ℓ (atomK ℓ κ)
  have e : 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) = 3 / 4 * (1 / 16 * ((2 : ℝ) ^ (ℓ + 4))⁻¹) := by
    field_simp; norm_num
  rw [e]
  linarith

/-! ### Prefix structure -/

theorem grpWord_length (y : Str 4) (t : ℕ) : (grpWord y t).length = 4 + t := by
  simp [grpWord]; omega

theorem grpWord_getElem (y : Str 4) (t i : ℕ) (hi : i < (grpWord y t).length) :
    (grpWord y t)[i] = if h : i < 4 then y ⟨i, h⟩ else false := by
  unfold grpWord at hi ⊢
  by_cases h : i < 4
  · rw [List.getElem_append_left (by simpa using h), List.getElem_ofFn]
    simp [h]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [h]

/-- `y 0^t ⪯ x_{y',j}` exactly when `y = y'` and `t ≤ j` (for `t ≤ ℓ`). -/
theorem isPre_grpWord_atomF {ℓ : ℕ} (y y' : Str 4) {t j : ℕ} (ht : t ≤ ℓ) :
    IsPre (grpWord y t) (atomF ℓ y' j) ↔ y = y' ∧ t ≤ j := by
  rw [isPre_iff_getElem]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨?_, ?_⟩
    · funext i
      have := h i.1 (by rw [grpWord_length]; omega)
      rw [grpWord_getElem, atomF_apply_lt (ℓ := ℓ) _ _ ⟨i.1, by omega⟩ i.2] at this
      simpa [i.2] using this
    · by_contra hlt
      push Not at hlt
      have := h (4 + j) (by rw [grpWord_length]; omega)
      rw [grpWord_getElem, atomF_apply_ge (ℓ := ℓ) _ _ ⟨4 + j, by omega⟩ (by simp)] at this
      simp at this
  · rintro ⟨rfl, htj⟩
    refine ⟨by rw [grpWord_length]; omega, fun i hi => ?_⟩
    rw [grpWord_getElem]
    by_cases h4 : i < 4
    · rw [atomF_apply_lt (ℓ := ℓ) _ _ ⟨i, by rw [grpWord_length] at hi; omega⟩ h4]
      simp [h4]
    · rw [atomF_apply_ge (ℓ := ℓ) _ _ ⟨i, by rw [grpWord_length] at hi; omega⟩ (by simp; omega)]
      rw [grpWord_length] at hi
      simp only [h4, dite_false]
      symm
      simp only [decide_eq_false_iff_not]
      omega

theorem isPre_grpWord_zblk {ℓ : ℕ} (y : Str 4) {t : ℕ} (ht : t ≤ ℓ) :
    IsPre (grpWord y t) (zblk ℓ y) := by
  rw [isPre_iff_getElem]
  refine ⟨by rw [grpWord_length]; omega, fun i hi => ?_⟩
  rw [grpWord_getElem]
  by_cases h4 : i < 4
  · simp [zblk, h4]
  · simp [zblk, h4]

/-- A public word below an atom lies below the corresponding background block. -/
theorem isPre_zblk_of_pub {ℓ : ℕ} {u : List Bool} (hu : u ∈ pubSetF ℓ) {κ : KeyF ℓ}
    (h : IsPre u (atomK ℓ κ)) : IsPre u (zblk ℓ κ.1) := by
  rw [isPre_iff_getElem] at h ⊢
  obtain ⟨hl, h⟩ := h
  refine ⟨hl, fun i hi => ?_⟩
  by_cases h4 : i < 4
  · rw [h i hi]
    simp [atomK, atomF, zblk, h4]
  · rw [hu.2 i hi (by omega)]
    simp [zblk, h4]

/-- Outside the public set, at most one atom lies below a word. -/
theorem atom_unique_of_not_pub {ℓ : ℕ} {u : List Bool} (hu : u ∉ pubSetF ℓ) {κ κ' : KeyF ℓ}
    (h : IsPre u (atomK ℓ κ)) (h' : IsPre u (atomK ℓ κ')) : κ = κ' := by
  have hl := h.length_le
  simp only [pubSetF, Set.mem_ofPred_eq, not_and, not_forall] at hu
  by_cases hlen : u.length < ℓ + 4
  · obtain ⟨i, hi, h4, hti⟩ := hu hlen
    have hut : u[i] = true := by simpa using hti
    rw [isPre_iff_getElem] at h h'
    obtain ⟨_, h⟩ := h
    obtain ⟨_, h'⟩ := h'
    obtain ⟨y, j⟩ := κ
    obtain ⟨y', j'⟩ := κ'
    have e1 := h i hi
    have e2 := h' i hi
    simp only [atomK] at e1 e2
    rw [atomF_apply_ge (ℓ := ℓ) _ _ _ (by simpa using h4)] at e1 e2
    rw [hut] at e1 e2
    have hj : i = 4 + j.1 := of_decide_eq_true e1.symm
    have hj' : i = 4 + j'.1 := of_decide_eq_true e2.symm
    have hy : y = y' := by
      funext k
      have f1 := h k.1 (by omega)
      have f2 := h' k.1 (by omega)
      simp only [atomK] at f1 f2
      rw [atomF_apply_lt (ℓ := ℓ) _ _ ⟨k.1, by omega⟩ k.2] at f1 f2
      rw [← f1, ← f2]
    subst hy
    rw [Prod.mk.injEq]
    exact ⟨rfl, Fin.ext (by omega)⟩
  · have hn : u.length = ℓ + 4 := by omega
    have e1 : u = List.ofFn (atomK ℓ κ) := h.eq_of_length (by simp [hn])
    have e2 : u = List.ofFn (atomK ℓ κ') := h'.eq_of_length (by simp [hn])
    exact atomK_injective ℓ (List.ofFn_injective (e1.symm.trans e2))

end Sec2
end LearningGuided
