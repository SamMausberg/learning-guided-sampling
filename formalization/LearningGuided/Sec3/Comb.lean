import LearningGuided.Sec3.LocalLower

/-!
# Proposition `prop:comb`: dependence on the background

`n = M`, `ν = (3/4)δ_{0^n} + (1/4)U_n`, atoms `x_j = 0^{j-1}10^{n-j}`. The hard guides answer
every proper all-zero prefix with `ν(u)` and every other word exactly. They are pointwise
factor `4/3` (hence of capacity at most `4/3`), and every nonpublic query names at most one
atom, so equality counting forces `q ≥ M(α - δ + a/(4·2^n)) - 1`. Exact-leaf search gives the
matching cap `⌈αM⌉`. Both `Q_pw` and `Q_safe` are `Θ(1 + αM)`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided.Sec3

open LearningGuided

/-- The all-zero string `0^n`. -/
def zeroStr (n : ℕ) : Str n := fun _ => false

/-- The comb background `ν = (3/4)δ_{0^n} + (1/4)U_n`. -/
noncomputable def combBg (n : ℕ) : Str n → ℝ :=
  fun y => 3 / 4 * dirac (zeroStr n) y + 1 / 4 * unif n y

/-- The atom `x_j = 0^{j-1}10^{n-j}`. -/
def combAtom {n : ℕ} (j : Fin n) : Str n := fun i => decide (i = j)

/-- The `M = n` atom locations. -/
noncomputable def combSet (n : ℕ) : Finset (Str n) := Finset.univ.image combAtom

/-- The class `𝓗 = {(1-α)ν + αδ_{x_j} : 1 ≤ j ≤ M}` on `M` bits. -/
def combClass (M : ℕ) (α : ℝ) : Set (Str M → ℝ) := atomClass (combBg M) (combSet M) α

variable {n : ℕ}

theorem isDist_combBg (n : ℕ) : IsDist (combBg n) := by
  have := isDist_mix (isDist_dirac (zeroStr n)) (isDist_unif n) (a := 1 / 4) (by norm_num)
    (by norm_num)
  convert this using 2
  norm_num [combBg]

theorem combBg_pos (y : Str n) : 0 < combBg n y := by
  unfold combBg dirac unif
  have : (0 : ℝ) < 1 / 4 * ((2 : ℝ) ^ n)⁻¹ := by positivity
  split_ifs <;> linarith

theorem combAtom_injective : Function.Injective (combAtom (n := n)) := by
  intro j j' h
  have := congrFun h j
  simpa [combAtom, eq_comm] using this

theorem card_combSet : (combSet n).card = n := by
  rw [combSet, Finset.card_image_of_injective _ combAtom_injective]
  simp

theorem combAtom_ne_zero (j : Fin n) : combAtom j ≠ zeroStr n := by
  intro h
  have := congrFun h j
  simp [combAtom, zeroStr] at this

theorem combBg_atom (j : Fin n) : combBg n (combAtom j) = 1 / 4 * ((2 : ℝ) ^ n)⁻¹ := by
  simp [combBg, dirac, combAtom_ne_zero j, unif]

/-- A proper all-zero prefix: the public words of the hard guide. -/
def combPub (n : ℕ) (u : List Bool) : Prop := u.length < n ∧ ∀ b ∈ u, b = false

theorem isPre_zeroStr {u : List Bool} (hu : u.length ≤ n) (hz : ∀ b ∈ u, b = false) :
    IsPre u (zeroStr n) := by
  unfold IsPre
  rw [List.prefix_iff_getElem?]
  intro i hi
  have hin : i < n := by omega
  have := hz u[i] (List.getElem_mem hi)
  simp [zeroStr, hin, this]

theorem combBg_pub {u : List Bool} (hu : combPub n u) : 3 / 4 ≤ mass (combBg n) u := by
  have h := mass_linear (dirac (zeroStr n)) (unif n) (3 / 4) (1 / 4) u
  have h1 : mass (fun x => 3 / 4 * dirac (zeroStr n) x + 1 / 4 * unif n x) u =
      mass (combBg n) u := rfl
  rw [h1, mass_dirac, ite_eq_left (isPre_zeroStr hu.1.le hu.2)] at h
  have := mass_nonneg (isDist_unif n).1 u
  linarith

/-- The hard guide for the atom `x_j`. -/
noncomputable def combGuide (α : ℝ) (j : Fin n) : Guide :=
  pubGuide (combBg n) α (combAtom j) (combPub n)

/-- `prop:comb`: the lower-bound guides are pointwise factor `4/3`. -/
theorem combGuide_pwLegal {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) (j : Fin n) :
    PwLegal (4 / 3) (atomTarget (combBg n) α (combAtom j)) (combGuide α j) :=
  pubGuide_pwLegal (isDist_combBg n) hα0 hα _ (fun _ hu => hu.1)
    (fun u hu => by have := combBg_pub hu; linarith)

/-- `prop:comb`: the lower-bound guides have stopped capacity at most `4/3`. -/
theorem combGuide_capLE {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) (j : Fin n) :
    CapLE (atomTarget (combBg n) α (combAtom j)) (combGuide α j) (4 / 3) :=
  (combGuide_pwLegal hα0 hα j).capLE (by norm_num)
    (isDist_atomTarget (isDist_combBg n) hα0 (by linarith) _)

theorem combGuide_legal_pw {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) (j : Fin n) :
    PwLegal (9 / 4) (atomTarget (combBg n) α (combAtom j)) (combGuide α j) :=
  PwLegal.mono (by norm_num) (by norm_num)
    (isDist_atomTarget (isDist_combBg n) hα0 (by linarith) _) (combGuide_pwLegal hα0 hα j)

theorem combGuide_legal_safe {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) (j : Fin n) :
    SafeLegal (9 / 4) (9 / 4) (atomTarget (combBg n) α (combAtom j)) (combGuide α j) :=
  SafeLegal.mono (by norm_num) (by norm_num)
    (isDist_atomTarget (isDist_combBg n) hα0 (by linarith) _)
    ((combGuide_pwLegal hα0 hα j).safeLegal (by norm_num)
      (isDist_atomTarget (isDist_combBg n) hα0 (by linarith) _))

/-- `prop:comb`: every nonpublic query specifies its first one, so it is simulated by one equality
test. -/
theorem eqStructure_comb (α : ℝ) : EqualityStructure fun j : Fin n => combGuide α j := by
  refine eqStructure_pub (combBg n) α (fun j : Fin n => combAtom j) (combPub n) ?_
  intro u hu j j' h1 h2
  have hone : ∃ i, ∃ hi : i < u.length, u[i] = true := by
    by_contra hno
    have hz : ∀ b ∈ u, b = false := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      cases hb' : u[i]
      · rfl
      · exact absurd ⟨i, hi, hb'⟩ hno
    have hlen : u.length = n := by
      have := h1.length_le
      by_contra hne
      exact hu ⟨by omega, hz⟩
    have := isPre_getElem h1 (i := j.val) (by omega)
    rw [hz _ (List.getElem_mem _)] at this
    simp [combAtom] at this
  obtain ⟨i, hi, hti⟩ := hone
  have e1 := isPre_getElem h1 hi
  have e2 := isPre_getElem h2 hi
  rw [hti] at e1 e2
  have f1 : (⟨i, by have := h1.length_le; omega⟩ : Fin n) = j := by
    simpa [combAtom] using e1.symm
  have f2 : (⟨i, by have := h1.length_le; omega⟩ : Fin n) = j' := by
    simpa [combAtom] using e2.symm
  exact f1.symm.trans f2

theorem comb_overlap (S : Finset (Fin n)) (y : Str n) :
    (S.filter fun j => y ∈ (({combAtom j} : Finset (Str n)) : Set (Str n))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
  exact combAtom_injective (ha.2.symm.trans hb.2)

/-- `prop:comb`, equality counting: in any model containing the hard guides,
`q ≥ M(α - δ + a/(4·2^n)) - 1`. -/
theorem comb_search {Legal : (Str n → ℝ) → Guide → Prop} {α δ : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ 1 / 4)
    (hlegal : ∀ j : Fin n, Legal (atomTarget (combBg n) α (combAtom j)) (combGuide α j))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (combClass n α) δ q A) :
    n * (α - δ + (1 - α) / (4 * 2 ^ n)) - 1 ≤ q := by
  have hmem : ∀ j : Fin n, atomTarget (combBg n) α (combAtom j) ∈ combClass n α := fun j =>
    ⟨combAtom j, Finset.mem_image_of_mem _ (Finset.mem_univ j), rfl⟩
  have hsum := equality_counting (fun j : Fin n => combGuide α j) (eqStructure_comb α)
    (fun j => (({combAtom j} : Finset (Str n)) : Set (Str n))) 1 A Finset.univ q
    (fun y => by convert comb_overlap Finset.univ y) (fun j _ => (hA _ (hmem j) _ (hlegal j)).1)
  have hp : ∀ j ∈ (Finset.univ : Finset (Fin n)), α + (1 - α) / (4 * 2 ^ n) - δ ≤
      (probE (A.run (combGuide α j)) (({combAtom j} : Finset (Str n)) : Set (Str n))).toReal := by
    intro j _
    have := prob_ge_of_tv (isDist_atomTarget (isDist_combBg n) hα0 (by linarith) _)
      (hA _ (hmem j) _ (hlegal j)).2 {combAtom j}
    rw [Finset.sum_singleton, atomTarget_apply, combBg_atom, ite_eq_left rfl] at this
    have e : (1 - α) * (1 / 4 * ((2 : ℝ) ^ n)⁻¹) + α * 1 = α + (1 - α) / (4 * 2 ^ n) := by
      field_simp
      ring
    linarith
  have h := card_mul_le_of_sum Finset.univ _ (by simp) (fun j => probE_le_one _ _) hsum hp
  have h2 : ((q : ℝ≥0∞) + ((1 : ℕ) : ℝ≥0∞)).toReal = q + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [h2, Finset.card_univ, Fintype.card_fin] at h
  linarith

/-- `prop:comb`, the zero-query obstruction for the comb class (`n ≥ 2`). -/
theorem comb_zero_query {Legal : (Str n → ℝ) → Guide → Prop} {α δ : ℝ} (hn : 2 ≤ n)
    (hα0 : 0 ≤ α) (hδ : 2 * δ < α)
    (hex : ∀ x : Str n, Legal (atomTarget (combBg n) α x) (exactGuide (atomTarget (combBg n) α x)))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (combClass n α) δ q A) : 1 ≤ q := by
  by_contra hq
  have hq0 : q = 0 := by omega
  subst hq0
  have hne : combAtom (⟨0, by omega⟩ : Fin n) ≠ combAtom ⟨1, by omega⟩ := fun h =>
    absurd (combAtom_injective h) (by simp)
  have h1 := hA _ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩), rfl⟩ _ (hex _)
  have h2 := hA _ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨1, by omega⟩), rfl⟩ _ (hex _)
  exact zero_query_obstruction (by rw [tv_atomTarget hα0 hne]; exact hδ) A h1.1 h2.1 h1.2 h2.2

/-- `prop:comb`, the lower bound `Ω(1+αM)` in any model containing the hard and the exact guides. -/
theorem comb_lower {Legal : (Str n → ℝ) → Guide → Prop} {α δ : ℝ} (hn : 2 ≤ n) (hα0 : 0 < α)
    (hα : α ≤ 1 / 4) (hδα : δ ≤ α / 4)
    (hlegal : ∀ j : Fin n, Legal (atomTarget (combBg n) α (combAtom j)) (combGuide α j))
    (hex : ∀ x : Str n, Legal (atomTarget (combBg n) α x) (exactGuide (atomTarget (combBg n) α x)))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (combClass n α) δ q A) :
    3 / 16 * (1 + α * n) ≤ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast comb_zero_query hn hα0.le (by linarith) hex hA
  have h := comb_search hα0.le hα hlegal hA
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (0 : ℝ) ≤ (1 - α) / (4 * 2 ^ n) := div_nonneg (by linarith) (by positivity)
  nlinarith

/-- `prop:comb`, upper bound: exact-leaf search solves the comb class exactly with cap `⌈αM⌉` in
every model whose guides satisfy `eq:oracle`. -/
theorem comb_upper {Legal : (Str n → ℝ) → Guide → Prop}
    (hLegal : ∀ μ h, Legal μ h → IsOracle μ h) {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) : (Qcx Legal (combClass n α) δ : ℝ) ≤ 1 + α * n := by
  have hs := solves_mono_delta hδ0 (solves_leafSampler hLegal (isDist_combBg n) (combSet n) hα0
    (by linarith) le_rfl hα0.le)
  have := Qcx_le hs
  rw [sub_zero, card_combSet] at this
  have h2 : (Qcx Legal (combClass n α) δ : ℝ) ≤ ⌈α * n⌉₊ := by exact_mod_cast this
  have := ceil_le_add_one (x := α * n) (by positivity)
  linarith

/-- `prop:comb`: for every `M ≥ 2` and `0 < α ≤ 1/4` the known full-support
background `ν = (3/4)δ_{0^M} + (1/4)U_M` on `M` bits with the atoms `x_j = 0^{j-1}10^{M-j}` has
`Q_pw(𝓗,δ) = Θ(1+αM)` and `Q_safe(𝓗,δ) = Θ(1+αM)` for `0 ≤ δ ≤ α/4`, with the absolute
constants `3/16` and `1`. The lower-bound guides are pointwise factor `4/3`
(`combGuide_pwLegal`) with capacity at most `4/3` (`combGuide_capLE`). -/
theorem comb : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) (α δ : ℝ), 2 ≤ M → 0 < α → α ≤ 1 / 4 → 0 ≤ δ → δ ≤ α / 4 →
      (∀ y, 0 < combBg M y) ∧ (combSet M).card = M ∧
      c₁ * (1 + α * M) ≤ (Qpw (combClass M α) δ : ℝ) ∧
      (Qpw (combClass M α) δ : ℝ) ≤ c₂ * (1 + α * M) ∧
      c₁ * (1 + α * M) ≤ (Qsafe (combClass M α) δ : ℝ) ∧
      (Qsafe (combClass M α) δ : ℝ) ≤ c₂ * (1 + α * M) := by
  refine ⟨3 / 16, 1, by norm_num, by norm_num, fun M α δ hM hα0 hα hδ0 hδα => ?_⟩
  have hdist : ∀ x : Str M, IsDist (atomTarget (combBg M) α x) := fun x =>
    isDist_atomTarget (isDist_combBg M) hα0.le (by linarith) x
  have hpw_ex : ∃ q A, Solves (PwLegal (9 / 4)) (combClass M α) δ q A :=
    ⟨_, _, solves_leafSampler (fun _ _ h => h.1) (isDist_combBg M) (combSet M) hα0
      (by linarith) hδ0 (by linarith)⟩
  have hsafe_ex : ∃ q A, Solves (SafeLegal (9 / 4) (9 / 4)) (combClass M α) δ q A :=
    ⟨_, _, solves_leafSampler (fun _ _ h => h.1) (isDist_combBg M) (combSet M) hα0
      (by linarith) hδ0 (by linarith)⟩
  refine ⟨combBg_pos, card_combSet, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [one_mul]
    exact comb_upper (Legal := PwLegal (9 / 4)) (fun _ _ h => h.1) hα0 hα hδ0
  rotate_left
  · rw [one_mul]
    exact comb_upper (Legal := SafeLegal (9 / 4) (9 / 4)) (fun _ _ h => h.1) hα0 hα hδ0
  · have := le_Qcx (b := ⌈3 / 16 * (1 + α * M)⌉₊) hpw_ex fun q A hA => by
      rw [Nat.ceil_le]
      exact comb_lower hM hα0 hα hδα (combGuide_legal_pw hα0.le hα)
        (fun x => pwLegal_exactGuide (by norm_num) (hdist x)) hA
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  · have := le_Qcx (b := ⌈3 / 16 * (1 + α * M)⌉₊) hsafe_ex fun q A hA => by
      rw [Nat.ceil_le]
      exact comb_lower hM hα0 hα hδα (combGuide_legal_safe hα0.le hα)
        (fun x => safeLegal_exactGuide (by norm_num) (by norm_num) (hdist x)) hA
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)

end LearningGuided.Sec3
