import LearningGuided.Sec3.LocalLower

/-!
# Proposition `prop:arbitrary-locations`: arbitrary known locations, uniform background

For an arbitrary known set `S` of `M ≥ 2` candidate atoms under the uniform background, search
the `G' ≤ 2^d` depth-`d` groups containing candidates (`d` from `eq:resolution`), test membership
with Lemma `lem:local-test`, and recover the atom on the atom-output branch with balanced prefix
tests (`⌈log_{3/2} M⌉` queries). Compared with exact-leaf search (`⌈αM⌉`), exact sampling uses
`O(1 + min{αM, RC/α + log M})` queries with an absolute constant for `R, C ≥ 1`, `0 < α ≤ 1/4`.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-- The balanced-recovery fuel `⌈log_{3/2} M⌉`. -/
noncomputable def balFuel (M : ℕ) : ℕ := ⌈Real.logb (3 / 2) M⌉₊

/-- Search the depth-`d` groups that contain candidates, then recover the atom by balanced prefix
tests inside the hit group. -/
noncomputable def arbGroup (S : Finset (Str n)) (d : ℕ) (θ₀ β : ℝ) : Alg (Str n) :=
  partSampler (fun x => pre x d) S β (fun _ r => θ₀ ≤ r)
    (fun u => balRec u (fun r => θ₀ ≤ r) (S.filter (IsPre u)) (balFuel S.card)) (drawA (unif n))

theorem within_arbGroup (S : Finset (Str n)) {d : ℕ} (hd : d ≤ n) (θ₀ : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (h : Guide) :
    (arbGroup S d θ₀ β).Within h (⌈β * 2 ^ d⌉₊ + balFuel S.card) := by
  have hw := within_partSampler (fun x => pre x d) S β (fun _ r => θ₀ ≤ r)
    (fun u => balRec u (fun r => θ₀ ≤ r) (S.filter (IsPre u)) (balFuel S.card))
    (drawA (unif n)) (h := h) (r := balFuel S.card)
    (fun u _ => within_balRec u _ h _ _) (within_drawA _ h 0)
  refine hw.mono (Nat.add_le_add_right (Nat.ceil_mono ?_) _)
  have h' : ((S.image fun x => pre x d).card : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast card_image_pre_le S hd
  exact mul_le_mul_of_nonneg_left h' hβ

theorem lawR_arbGroup {S : Finset (Str n)} {d : ℕ} (hd : d ≤ n) {θ₀ β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) {x : Str n} (hx : x ∈ S) {h : Guide}
    (hvalid : ∀ v : List Bool, d ≤ v.length → v.length ≤ n → (θ₀ ≤ h v ↔ IsPre v x)) :
    lawR ((arbGroup S d θ₀ β).run h) = atomTarget (unif n) β x := by
  refine lawR_partSampler _ hβ0 hβ1 _ _ _ hx (fun y _ => ?_) (fun u hu => ?_) ?_
    (lawR_drawA (isDist_unif n) h)
  · rw [isPre_iff_pre, length_pre y hd]
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
    exact hvalid _ (by rw [length_pre y hd]) (by rw [length_pre y hd]; exact hd)
  · have hM : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
    refine run_balRec (by rw [length_pre x hd]; exact hd) _ (fun v hv hvn => ?_) _ _
      (Finset.mem_filter.mpr ⟨hx, isPre_pre x d⟩)
      (fun y hy => (Finset.mem_filter.mp hy).2)
      (fuel_ok hM (by exact_mod_cast Finset.card_filter_le _ _))
    refine hvalid v ?_ hvn
    have := hv.length_le
    rw [length_pre x hd] at this
    exact this

/-- `prop:arbitrary-locations`, the cap: `min{⌈αM⌉, ⌈α2^d⌉ + ⌈log_{3/2} M⌉}` if `d ≤ n`, and
`⌈αM⌉` otherwise. -/
noncomputable def arbCap (M d n : ℕ) (β : ℝ) : ℕ :=
  if d ≤ n then min ⌈β * M⌉₊ (⌈β * 2 ^ d⌉₊ + balFuel M) else ⌈β * M⌉₊

open Classical in
/-- The sampler of `prop:arbitrary-locations`: the cheaper of the group search with balanced
recovery and exact-leaf search. -/
noncomputable def arbSampler (S : Finset (Str n)) (d : ℕ) (θ₀ α β : ℝ) : Alg (Str n) :=
  if d ≤ n ∧ ⌈β * 2 ^ d⌉₊ + balFuel S.card ≤ ⌈β * S.card⌉₊ then arbGroup S d θ₀ β
  else leafSampler (unif n) S α β

theorem within_arbSampler (S : Finset (Str n)) (d : ℕ) (θ₀ α : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (h : Guide) : (arbSampler S d θ₀ α β).Within h (arbCap S.card d n β) := by
  have hleaf := within_leafSampler (unif n) S α β h
  unfold arbSampler arbCap
  by_cases hd : d ≤ n
  · by_cases hc : ⌈β * 2 ^ d⌉₊ + balFuel S.card ≤ ⌈β * S.card⌉₊
    · rw [ite_eq_left ⟨hd, hc⟩, ite_eq_left hd, min_eq_right hc]
      exact within_arbGroup S hd θ₀ hβ h
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_left hd, min_eq_left (by omega)]
      exact hleaf
  · rw [ite_eq_right (fun h => hd h.1), ite_eq_right hd]
    exact hleaf

/-- `prop:arbitrary-locations`, exact sampler: against every guide legal in the safe model with
constants `R, C > 0`, the sampler at the resolution depth outputs exactly `(1-α)U_n + αδ_x`,
with the cap `arbCap`. -/
theorem solves_arbSampler (S : Finset (Str n)) {R C α : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hα : 0 < α) (hα1 : α < 1) :
    Solves (SafeLegal R C) (atomClass (unif n) S α) 0 (arbCap S.card (resDepth R C α) n α)
      (arbSampler S (resDepth R C α) (α ^ 2 / C) α α) := by
  refine solves_of_law (β := α) (isDist_unif n) (by simp)
    (fun h => within_arbSampler S _ _ _ hα.le h) fun x hx h hl => ?_
  unfold arbSampler
  split_ifs with hc
  · exact lawR_arbGroup hc.1 hα.le hα1.le hx (safe_valid hR hC hα hα1 hl)
  · exact lawR_leafSampler (isDist_unif n) hα hα.le hα1.le hx hl.1

theorem log_three_halves_ge : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num)
  norm_num at this ⊢
  linarith

/-- `⌈log_{3/2} M⌉ ≤ 1 + 3 log M`. -/
theorem balFuel_le {M : ℕ} (hM : 1 ≤ M) : (balFuel M : ℝ) ≤ 1 + 3 * Real.log M := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM'
  have hb : Real.logb (3 / 2) M ≤ 3 * Real.log M := by
    rw [Real.logb, div_le_iff₀ (by linarith [log_three_halves_ge])]
    nlinarith [log_three_halves_ge]
  have := ceil_le_add_one (Real.logb_nonneg (b := 3 / 2) (by norm_num) hM')
  unfold balFuel
  linarith

/-- `prop:arbitrary-locations`: there is an absolute constant `c` (here `c = 4`)
such that for every known set `S` of `M ≥ 2` strings, every `R, C ≥ 1` and `0 < α ≤ 1/4`, exact
sampling from `{(1-α)U_n + αδ_x : x ∈ S}` under `eq:capacity-model` uses at most
`c (1 + min{αM, RC/α + log M})` queries. -/
theorem arbitrary_locations : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (S : Finset (Str n)) (R C α : ℝ), 2 ≤ S.card → 1 ≤ R → 1 ≤ C → 0 < α →
      α ≤ 1 / 4 →
      (Qcx (SafeLegal R C) (atomClass (unif n) S α) 0 : ℝ) ≤
        c * (1 + min (α * S.card) (R * C / α + Real.log S.card)) := by
  refine ⟨4, by norm_num, fun n S R C α hM hR hC hα0 hα => ?_⟩
  have hQ : (Qcx (SafeLegal R C) (atomClass (unif n) S α) 0 : ℝ) ≤
      arbCap S.card (resDepth R C α) n α := by
    exact_mod_cast Qcx_le (solves_arbSampler S (by linarith) (by linarith) hα0 (by linarith))
  refine hQ.trans ?_
  set M := S.card with hMdef
  set d := resDepth R C α with hd
  set X : ℝ := 2 * R * C * (1 - α) / α ^ 2 with hX
  have hRC : 1 ≤ R * C := by nlinarith
  have hαX : α * X = 2 * (R * C) * ((1 - α) / α) := by
    rw [hX]
    field_simp
  have hB : (1 - α) / α ≤ α⁻¹ := by
    rw [div_le_iff₀ hα0, inv_mul_cancel₀ hα0.ne']
    linarith
  have hRCα : R * C * ((1 - α) / α) ≤ R * C / α := by
    rw [div_eq_mul_inv (R * C)]
    exact mul_le_mul_of_nonneg_left hB (by linarith)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hRCpos : 0 ≤ R * C / α := by positivity
  have hleaf : (⌈α * M⌉₊ : ℝ) ≤ α * M + 1 := ceil_le_add_one (by positivity)
  have hAM0 : 0 ≤ α * M := by positivity
  unfold arbCap
  split_ifs with hdn
  · have hX1 : 1 ≤ 2 * X := by
      have : (1 : ℝ) / 2 ≤ X := by
        rw [hX, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have h2d : (2 : ℝ) ^ d ≤ 2 * X := two_pow_depthFor_le hX1
    have hgroup : (⌈α * 2 ^ d⌉₊ : ℝ) + balFuel M ≤ 4 * (1 + (R * C / α + Real.log M)) := by
      have h1 := ceil_le_add_one (x := α * 2 ^ d) (by positivity)
      have h2 : α * 2 ^ d ≤ 4 * (R * C / α) := by
        calc α * 2 ^ d ≤ α * (2 * X) := mul_le_mul_of_nonneg_left h2d hα0.le
          _ = 2 * (α * X) := by ring
          _ ≤ 4 * (R * C / α) := by rw [hαX]; nlinarith
      have h3 := balFuel_le (by omega : 1 ≤ M)
      nlinarith
    have hmin : ((min ⌈α * M⌉₊ (⌈α * 2 ^ d⌉₊ + balFuel M) : ℕ) : ℝ) ≤
        min (α * M + 1) (4 * (1 + (R * C / α + Real.log M))) := by
      push_cast
      exact min_le_min hleaf hgroup
    refine hmin.trans ?_
    rcases le_total (α * M) (R * C / α + Real.log M) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact min_le_right _ _
  · have hnX : (2 : ℝ) ^ n < X := by
      by_contra hc
      exact hdn (depthFor_le (not_lt.mp hc))
    have hMn : (M : ℝ) ≤ 2 ^ n := by
      have : M ≤ 2 ^ n := by
        have := Finset.card_le_univ S
        simpa using this
      exact_mod_cast this
    have hAM : α * M ≤ 2 * (R * C / α) := by
      have : α * M ≤ α * X := mul_le_mul_of_nonneg_left (hMn.trans hnX.le) hα0.le
      rw [hαX] at this
      nlinarith
    have : α * M ≤ 2 * min (α * M) (R * C / α + Real.log M) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_min (by linarith) (by linarith)
    have hmin0 : 0 ≤ min (α * M) (R * C / α + Real.log M) := le_min hAM0 (by positivity)
    linarith

end LearningGuided.Sec3
