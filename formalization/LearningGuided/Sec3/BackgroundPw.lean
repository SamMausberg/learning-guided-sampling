import LearningGuided.Sec3.BackgroundLower

/-!
# Proposition `prop:background-pointwise`: the pointwise counterpart

Upper bound: with `η` uniform on the known candidates and `w = (ν+η)/2`, split the prefix tree
by the known mass `w` at threshold `τ = α/(4R²(1-α))`. A nonleaf group has `ν(u) ≤ 2τ`, so an
empty group has `h(u) ≤ α/(2R)` while an occupied one has `h(u) ≥ α/R`, at every descendant as
well; it contains at most `2τM ≤ αM` candidates. The thinned search over the groups costs
`O(1 + log(1+2^nα))`, and direct leaf search costs `⌈αM⌉`.

Lower bound: the hard background of `thm:background` with
`d = min{n-1, ⌊log₂(1/(4α))⌋}`; the hard guides are pointwise factor `4/3`.

`Q_atom,pw(n,M,α,δ) = Θ(1 + min{αM, log(1+2^nα)})`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### The splitting mass -/

open Classical in
/-- The uniform distribution `η` on the known candidates. -/
noncomputable def candUnif (S : Finset (Str n)) : Str n → ℝ :=
  fun y => if y ∈ S then (S.card : ℝ)⁻¹ else 0

theorem isDist_candUnif {S : Finset (Str n)} (hS : S.Nonempty) : IsDist (candUnif S) := by
  classical
  refine ⟨fun y => by unfold candUnif; split_ifs <;> positivity, ?_⟩
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  unfold candUnif
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_inv_cancel₀ hc]

theorem mass_candUnif (S : Finset (Str n)) (g : List Bool) :
    mass (candUnif S) g = (S.filter (IsPre g)).card * (S.card : ℝ)⁻¹ := by
  classical
  unfold mass candUnif
  have h : ∀ y, (if IsPre g y then (if y ∈ S then (S.card : ℝ)⁻¹ else 0) else 0) =
      if y ∈ S.filter (IsPre g) then (S.card : ℝ)⁻¹ else 0 := by
    intro y
    by_cases h1 : IsPre g y <;> by_cases h2 : y ∈ S <;> simp [h1, h2]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- The splitting mass `w = (ν + η)/2`. -/
noncomputable def pwMix (ν : Str n → ℝ) (S : Finset (Str n)) : Str n → ℝ :=
  fun y => 1 / 2 * ν y + 1 / 2 * candUnif S y

theorem isDist_pwMix {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hS : S.Nonempty) :
    IsDist (pwMix ν S) := by
  have := isDist_mix hν (isDist_candUnif hS) (a := 1 / 2) (by norm_num) (by norm_num)
  convert this using 2
  norm_num [pwMix]

/-- The pointwise threshold `τ = α/(4R²(1-α))`. -/
noncomputable def pwTau (R α : ℝ) : ℝ := α / (4 * R ^ 2 * (1 - α))

/-- The recovery fuel `⌈log_{3/2}(1 + 2τM)⌉` (a light group has at most `2τM` candidates). -/
noncomputable def pwFuel (M : ℕ) (R α : ℝ) : ℕ := ⌈Real.logb (3 / 2) (1 + 2 * pwTau R α * M)⌉₊

theorem pwTau_pos {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1) : 0 < pwTau R α := by
  unfold pwTau
  have : 0 < 1 - α := by linarith
  positivity

open Classical in
/-- The pointwise sampler: the partition sampler on the split tree of `w` with the threshold
`α/R`, or direct leaf search if that is cheaper. -/
noncomputable def pwBgSampler (ν : Str n → ℝ) (S : Finset (Str n)) (R α : ℝ) : Alg (Str n) :=
  if ⌈α * (S.image (splitGroup (pwMix ν S) (pwTau R α))).card⌉₊ + pwFuel S.card R α ≤
      ⌈α * S.card⌉₊ then
    splitSampler ν (pwMix ν S) (pwTau R α) S α (α / R) (pwFuel S.card R α)
  else leafSampler ν S α α

/-- `prop:background-pointwise`: the background mass of a light group of `w` is at most `2τ`, and it
holds at most `2τM` candidates. -/
theorem pw_light {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hS : S.Nonempty)
    {τ : ℝ} {g : List Bool} (hg : mass (pwMix ν S) g ≤ τ) :
    mass ν g ≤ 2 * τ ∧ ((S.filter (IsPre g)).card : ℝ) ≤ 2 * τ * S.card := by
  have hm : mass (pwMix ν S) g = 1 / 2 * mass ν g + 1 / 2 * mass (candUnif S) g :=
    mass_linear ν (candUnif S) (1 / 2) (1 / 2) g
  have h1 := mass_nonneg hν.1 g
  have h2 := mass_nonneg (isDist_candUnif hS).1 g
  refine ⟨by linarith, ?_⟩
  have hc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have h3 : mass (candUnif S) g ≤ 2 * τ := by linarith
  rw [mass_candUnif, ← div_eq_mul_inv, div_le_iff₀ hc] at h3
  exact h3

/-- `prop:background-pointwise`, sampler: exact against every pointwise factor-`R` guide, with the
cap `min{⌈αM⌉, ⌈αG⌉ + ⌈log_{3/2}(1+2τM)⌉}`. -/
theorem solves_pwBgSampler {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1)
    {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hS : S.Nonempty) :
    Solves (PwLegal R) (atomClass ν S α) 0
      (min ⌈α * S.card⌉₊ (⌈α * (S.image (splitGroup (pwMix ν S) (pwTau R α))).card⌉₊ +
        pwFuel S.card R α)) (pwBgSampler ν S R α) := by
  refine solves_of_law (β := α) hν (by simp) (fun h => ?_) (fun x hx h hl => ?_)
  · unfold pwBgSampler
    split_ifs with hc
    · rw [min_eq_right hc]
      exact within_splitSampler _ _ _ _ _ _ h
    · rw [min_eq_left (by omega)]
      exact within_leafSampler _ _ _ _ h
  · unfold pwBgSampler
    split_ifs
    · refine lawR_splitSampler hν hα hα1.le hx hl.1 (fun y _ hlen v hv hvn => ?_)
        (fun y _ hlen => ?_)
      · have hg := (pw_light hν hS (splitGroup_light _ _ y hlen)).1
        refine pw_test hν hR hα1.le hl hvn ?_
        have hvm := (mass_le_of_prefix hν.1 hv).trans hg
        have ha : 0 < 1 - α := by linarith
        have h2 : R * ((1 - α) * mass ν v) ≤ R * ((1 - α) * (2 * pwTau R α)) := by
          gcongr
        have h3 : R * ((1 - α) * (2 * pwTau R α)) = α / (2 * R) := by
          unfold pwTau
          field_simp
          ring
        have h4 : α / (2 * R) < α / R := by
          rw [div_lt_div_iff₀ (by positivity) hR]
          nlinarith
        linarith
      · have hc := (pw_light hν hS (splitGroup_light _ _ y hlen)).2
        have h0 : (0 : ℝ) ≤ 2 * pwTau R α * S.card := by
          have := (pwTau_pos hR hα hα1).le
          positivity
        exact fuel_ok (by linarith) (by linarith)
    · exact lawR_leafSampler hν hα hα.le hα1.le hx hl.1

/-- `⌈log_{3/2} N⌉ ≤ 1 + 3 log N` for `N ≥ 1`. -/
theorem fuelN_le {N : ℝ} (hN : 1 ≤ N) :
    (⌈Real.logb (3 / 2) N⌉₊ : ℝ) ≤ 1 + 3 * Real.log N := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hb : Real.logb (3 / 2) N ≤ 3 * Real.log N := by
    rw [Real.logb, div_le_iff₀ (by linarith [log_three_halves_ge])]
    nlinarith [log_three_halves_ge]
  have := ceil_le_add_one (Real.logb_nonneg (b := 3 / 2) (by norm_num) hN)
  linarith

/-- `prop:background-pointwise`, upper bound for exact sampling, at `R = 9/4`: for every
known background and every known set of `M` atoms, `Q_pw ≤ 130 (1 + min{αM, log(1+2^nα)})`. -/
theorem background_pw_upper {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ)
    {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hM : 2 ≤ S.card) :
    (Qpw (atomClass ν S α) δ : ℝ) ≤
      130 * (1 + min (α * S.card) (Real.log (1 + 2 ^ n * α))) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hQ := Qcx_le (solves_mono_delta hδ0 (solves_pwBgSampler (by norm_num : (0 : ℝ) < 9 / 4)
    hα0 (by linarith) hν hS))
  set M := S.card with hMdef
  set G := (S.image (splitGroup (pwMix ν S) (pwTau (9 / 4) α))).card with hGdef
  have hQ' : (Qpw (atomClass ν S α) δ : ℝ) ≤
      ((min ⌈α * M⌉₊ (⌈α * G⌉₊ + pwFuel M (9 / 4) α) : ℕ) : ℝ) := by exact_mod_cast hQ
  rw [Nat.cast_min, Nat.cast_add] at hQ'
  refine hQ'.trans ?_
  set z : ℝ := 2 ^ n * α with hz
  have hMn : (M : ℝ) ≤ 2 ^ n := by
    have := Finset.card_le_univ S
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  have hz0 : 0 < z := by positivity
  have hAM0 : 0 ≤ α * M := by positivity
  have hαMz : α * M ≤ z := by
    rw [hz, mul_comm _ α]
    exact mul_le_mul_of_nonneg_left hMn hα0.le
  have hleaf : (⌈α * M⌉₊ : ℝ) ≤ α * M + 1 := ceil_le_add_one hAM0
  have hlog0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  rcases le_total z 1 with hz1 | hz1
  · have hlz := half_le_log_one_add hz0.le hz1
    have : α * M ≤ 2 * min (α * M) (Real.log (1 + z)) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_min (by linarith) (by linarith)
    have hmin0 : 0 ≤ min (α * M) (Real.log (1 + z)) := le_min hAM0 hlog0
    have := min_le_left (⌈α * M⌉₊ : ℝ) (⌈α * G⌉₊ + pwFuel M (9 / 4) α)
    linarith
  · set T := (pwTau (9 / 4) α)⁻¹ with hT
    have hTe : T = 81 / 4 * (1 - α) * α⁻¹ := by
      rw [hT, pwTau]
      field_simp
      ring
    have hTge : α⁻¹ ≤ T := by
      rw [hTe]
      have : 0 ≤ α⁻¹ := by positivity
      nlinarith
    have hαT : α * T ≤ 81 / 4 := by
      rw [hTe, show α * (81 / 4 * (1 - α) * α⁻¹) = 81 / 4 * (1 - α) * (α * α⁻¹) by ring,
        mul_inv_cancel₀ hα0.ne']
      nlinarith
    have hB4 : 4 ≤ α⁻¹ := by rw [le_inv_comm₀ (by norm_num) hα0]; linarith
    have hlogz0 : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hz1
    have hnT : (n : ℝ) - Real.logb 2 T ≤ Real.logb 2 z := by
      have h1 : Real.logb 2 α⁻¹ ≤ Real.logb 2 T :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hTge
      have h2 : Real.logb 2 z = n - Real.logb 2 α⁻¹ := by
        rw [hz, Real.logb_mul (by positivity) hα0.ne', logb_two_pow, Real.logb_inv]
        ring
      linarith
    have hsum := sum_min_pow_le (T := T) (by linarith) n hlogz0 hnT
    have hcount := card_splitGroups_le (isDist_pwMix hν hS)
      (pwTau_pos (R := 9 / 4) (by norm_num) hα0 (by linarith)) S
    have hG : (G : ℝ) ≤ 1 + (2 * T + T * Real.logb 2 z) :=
      (le_min_iff.mp hcount).2.trans (by linarith)
    have hlogb_le : Real.logb 2 z ≤ 2 * Real.log z := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have := log_two_gt_half
      have : 0 ≤ Real.log z := Real.log_nonneg hz1
      nlinarith
    have hGb : α * G ≤ 1 / 4 + 81 / 4 * (2 + 2 * Real.log z) := by
      have h1 : α * G ≤ α * (1 + (2 * T + T * Real.logb 2 z)) :=
        mul_le_mul_of_nonneg_left hG hα0.le
      have h3 : α * (1 + (2 * T + T * Real.logb 2 z)) = α + α * T * (2 + Real.logb 2 z) := by
        ring
      have h4 : α * T * (2 + Real.logb 2 z) ≤ 81 / 4 * (2 + Real.logb 2 z) :=
        mul_le_mul_of_nonneg_right hαT (by linarith)
      nlinarith
    have hfuel : (pwFuel M (9 / 4) α : ℝ) ≤ 1 + 3 * Real.log (1 + z) := by
      have h2τ : 2 * pwTau (9 / 4) α * M ≤ α * M := by
        have : 2 * pwTau (9 / 4) α ≤ α := by
          unfold pwTau
          rw [mul_div_assoc', div_le_iff₀ (by nlinarith)]
          nlinarith
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hτ0 : 0 ≤ 2 * pwTau (9 / 4) α * M := by
        have := (pwTau_pos (by norm_num : (0 : ℝ) < 9 / 4) hα0 (by linarith)).le
        positivity
      have h1 := fuelN_le (N := 1 + 2 * pwTau (9 / 4) α * M) (by linarith)
      have h2 := Real.log_le_log (by linarith) (by linarith :
        1 + 2 * pwTau (9 / 4) α * M ≤ 1 + z)
      unfold pwFuel
      linarith
    have hceil := ceil_le_add_one (x := α * G) (by positivity)
    have hl1 : Real.log z ≤ Real.log (1 + z) := Real.log_le_log hz0 (by linarith)
    have hl2 : 1 / 2 ≤ Real.log (1 + z) := by
      have := Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ 1 + z)
      linarith [log_two_gt_half]
    have hpart : (min (⌈α * M⌉₊ : ℝ) (⌈α * G⌉₊ + pwFuel M (9 / 4) α)) ≤
        130 * Real.log (1 + z) := by
      refine (min_le_right _ _).trans ?_
      nlinarith
    have hmin0 : 0 ≤ min (α * M) (Real.log (1 + z)) := le_min hAM0 hlog0
    have hleaf' := (min_le_left (⌈α * M⌉₊ : ℝ) (⌈α * G⌉₊ + pwFuel M (9 / 4) α)).trans hleaf
    rcases le_total (α * M) (Real.log (1 + z)) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith

/-! ### The lower bound -/

/-- The depth `d = min{n-1, ⌊log₂(1/(4α))⌋}` of the pointwise lower bound. -/
noncomputable def bgPwDepth (n : ℕ) (α : ℝ) : ℕ := min (n - 1) ⌊Real.logb 2 (1 / (4 * α))⌋₊

/-- `prop:background-pointwise`, comparison: `αK ≥ (1/16) log(1+2^nα)` at the pointwise depth,
together with `αH ≤ 1/4`. -/
theorem pw_regime {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hn : 1 ≤ n) :
    α * 2 ^ bgPwDepth n α ≤ 1 / 4 ∧
    1 / 16 * Real.log (1 + 2 ^ n * α) ≤
      α * (2 ^ bgPwDepth n α * (n - bgPwDepth n α : ℕ)) := by
  have hy : 1 ≤ 1 / (4 * α) := by rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨hf1, hf2⟩ := floor_logb_two_spec hy
  set L := ⌊Real.logb 2 (1 / (4 * α))⌋₊ with hL
  have hαL : α * 2 ^ L ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hf1
    linarith
  have hαL' : 1 / 8 < α * 2 ^ L := by
    have e : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
    rw [e, div_lt_iff₀ (by positivity)] at hf2
    linarith
  set z : ℝ := 2 ^ n * α with hz
  have hz0 : 0 < z := by positivity
  unfold bgPwDepth
  rw [← hL]
  refine ⟨?_, ?_⟩
  · have : (2 : ℝ) ^ min (n - 1) L ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
    nlinarith
  rcases le_or_gt (n - 1) L with h | h
  · rw [min_eq_left h, show n - (n - 1) = 1 by omega]
    have hn1 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hzle : z ≤ 2 * (α * 2 ^ (n - 1)) := by rw [hz, hn1]; ring_nf; rfl
    have := Real.log_le_sub_one_of_pos (x := 1 + z) (by linarith)
    have : (0 : ℝ) ≤ α * 2 ^ (n - 1) := by positivity
    push_cast
    nlinarith
  · rw [min_eq_right h.le]
    set ℓ := n - L with hℓ
    have hnL : (2 : ℝ) ^ n = 2 ^ L * 2 ^ ℓ := by
      rw [← pow_add]
      congr 1
      omega
    have hzle : z ≤ 2 ^ ℓ := by
      rw [hz, hnL]
      have : (0 : ℝ) < 2 ^ ℓ := by positivity
      nlinarith
    have hlog := log_le_two_mul (by omega : 1 ≤ ℓ) hz0.le hzle
    have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    nlinarith

/-- `prop:background-pointwise`, lower bound: there are a full-support background and a
set of `M` atoms with `Q_pw ≥ (3/256)(1 + min{αM, log(1+2^nα)})`. -/
theorem background_pw_lower {M : ℕ} {α δ : ℝ} (hn : 1 ≤ n) (hM : 2 ≤ M) (hMn : M ≤ 2 ^ n)
    (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α / 4) :
    ∃ S : Finset (Str n), S.card = M ∧
      3 / 256 * (1 + min (α * M) (Real.log (1 + 2 ^ n * α))) ≤
        (Qpw (atomClass (blockBg n (bgPwDepth n α)) S α) δ : ℝ) := by
  set d := bgPwDepth n α with hd
  have hdn : d < n := by
    have : d ≤ n - 1 := min_le_left _ _
    omega
  obtain ⟨S, hScard, hsel⟩ := exists_block_set hdn.le hMn
  refine ⟨S, hScard, ?_⟩
  obtain ⟨hH, hcmp⟩ := pw_regime hα0 hα hn
  rw [← hd] at hH hcmp
  have hdist : ∀ x : Str n, IsDist (atomTarget (blockBg n d) α x) := fun x =>
    isDist_atomTarget (isDist_blockBg n d) hα0.le (by linarith) x
  have hS2 : 2 ≤ S.card := by omega
  have hex : ∃ q A, Solves (PwLegal (9 / 4)) (atomClass (blockBg n d) S α) δ q A :=
    ⟨_, _, solves_mono_delta hδ0 (solves_pwBgSampler (by norm_num) hα0 (by linarith)
      (isDist_blockBg n d) (Finset.card_pos.mp (by omega)))⟩
  have hlow := le_Qcx (b := ⌈3 / 16 * (1 + α * (blockSel n d S).card)⌉₊) hex fun q A hA => by
    rw [Nat.ceil_le]
    exact block_lower hdn.le hα0 hα hδα hS2 (fun θ _ => blockGuide_legal_pw hα0 hα hH θ)
      (fun x => pwLegal_exactGuide (by norm_num) (hdist x)) hA
  have hQ : 3 / 16 * (1 + α * (blockSel n d S).card) ≤
      (Qpw (atomClass (blockBg n d) S α) δ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlow)
  have hsel' : (min (M : ℝ) (2 ^ d * (n - d : ℕ))) ≤ (blockSel n d S).card := by
    exact_mod_cast hsel
  have hAM : 0 ≤ α * M := by positivity
  have hz0 : (0 : ℝ) ≤ 2 ^ n * α := by positivity
  have hlog0 : 0 ≤ Real.log (1 + 2 ^ n * α) := Real.log_nonneg (by linarith)
  have hmin0 : 0 ≤ min (α * M) (Real.log (1 + 2 ^ n * α)) := le_min hAM hlog0
  have hmin : 1 / 16 * min (α * M) (Real.log (1 + 2 ^ n * α)) ≤ α * (blockSel n d S).card := by
    have h1 : 1 / 16 * min (α * M) (Real.log (1 + 2 ^ n * α)) ≤
        min (α * M) (α * (2 ^ d * (n - d : ℕ))) := by
      have m1 := min_le_left (α * M) (Real.log (1 + 2 ^ n * α))
      have m2 := min_le_right (α * M) (Real.log (1 + 2 ^ n * α))
      exact le_min (by linarith) (by linarith)
    calc 1 / 16 * min (α * M) (Real.log (1 + 2 ^ n * α))
        ≤ min (α * M) (α * (2 ^ d * (n - d : ℕ))) := h1
      _ = α * min (M : ℝ) (2 ^ d * (n - d : ℕ)) := (mul_min_of_nonneg _ _ hα0.le).symm
      _ ≤ α * (blockSel n d S).card := mul_le_mul_of_nonneg_left hsel' hα0.le
  linarith

/-- `prop:background-pointwise`: under the assumptions of `thm:background`, with the
absolute constants `c₁ = 3/256`, `c₂ = 130`: every known background and every known set of `M`
atoms have `Q_pw ≤ c₂(1 + min{αM, log(1+2^nα)})` (by an exact sampler), and some full-support
background and some set of `M` atoms have `Q_pw ≥ c₁(…)`. -/
theorem background_pointwise : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n M : ℕ) (α δ : ℝ), 1 ≤ n → 2 ≤ M → M ≤ 2 ^ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ →
      δ ≤ α / 4 →
      (∀ ν : Str n → ℝ, IsDist ν → ∀ S : Finset (Str n), S.card = M →
        (Qpw (atomClass ν S α) δ : ℝ) ≤ c₂ * (1 + min (α * M) (Real.log (1 + 2 ^ n * α)))) ∧
      (∃ ν : Str n → ℝ, IsDist ν ∧ (∀ y, 0 < ν y) ∧ ∃ S : Finset (Str n), S.card = M ∧
        c₁ * (1 + min (α * M) (Real.log (1 + 2 ^ n * α))) ≤ (Qpw (atomClass ν S α) δ : ℝ)) := by
  refine ⟨3 / 256, 130, by norm_num, by norm_num,
    fun n M α δ hn hM hMn hα0 hα hδ0 hδα => ⟨fun ν hν S hS => ?_, ?_⟩⟩
  · have := background_pw_upper hα0 hα hδ0 hν (S := S) (by omega)
    rwa [hS] at this
  · obtain ⟨S, hS, hlow⟩ := background_pw_lower hn hM hMn hα0 hα hδ0 hδα
    exact ⟨_, isDist_blockBg n _, blockBg_pos _, S, hS, hlow⟩

/-- `Q_atom,pw(n,M,α,δ)`: the supremum of `Q_pw` over known backgrounds and known sets of `M`
atoms. -/
noncomputable def QatomPw (n M : ℕ) (α δ : ℝ) : ℕ :=
  sSup {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n), IsDist ν ∧ S.card = M ∧
    q = Qpw (atomClass ν S α) δ}

/-- `eq:background-pointwise` for the supremum `Q_atom,pw` itself. -/
theorem QatomPw_rate : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n M : ℕ) (α δ : ℝ), 1 ≤ n → 2 ≤ M → M ≤ 2 ^ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ →
      δ ≤ α / 4 →
      c₁ * (1 + min (α * M) (Real.log (1 + 2 ^ n * α))) ≤ (QatomPw n M α δ : ℝ) ∧
      (QatomPw n M α δ : ℝ) ≤ c₂ * (1 + min (α * M) (Real.log (1 + 2 ^ n * α))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := background_pointwise
  refine ⟨c₁, c₂, hc₁, hc₂, fun n M α δ hn hM hMn hα0 hα hδ0 hδα => ?_⟩
  obtain ⟨hup, ν₀, hν₀, -, S₀, hS₀, hlow⟩ := h n M α δ hn hM hMn hα0 hα hδ0 hδα
  set r := c₂ * (1 + min (α * M) (Real.log (1 + 2 ^ n * α)))
  have hbdd : BddAbove {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n), IsDist ν ∧ S.card = M ∧
      q = Qpw (atomClass ν S α) δ} := by
    refine ⟨⌊r⌋₊, fun q ⟨ν, S, hν, hS, hq⟩ => ?_⟩
    rw [hq]
    exact Nat.le_floor (hup ν hν S hS)
  have hmem : Qpw (atomClass ν₀ S₀ α) δ ∈ {q | ∃ ν : Str n → ℝ, ∃ S : Finset (Str n),
      IsDist ν ∧ S.card = M ∧ q = Qpw (atomClass ν S α) δ} := ⟨ν₀, S₀, hν₀, hS₀, rfl⟩
  constructor
  · exact hlow.trans (by exact_mod_cast le_csSup hbdd hmem)
  · have : QatomPw n M α δ ≤ ⌊r⌋₊ := csSup_le ⟨_, hmem⟩ fun q ⟨ν, S, hν, hS, hq⟩ => by
      rw [hq]
      exact Nat.le_floor (hup ν hν S hS)
    have hr : (0 : ℝ) ≤ r := (Nat.cast_nonneg _).trans (hup ν₀ hν₀ S₀ hS₀)
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hr)

end LearningGuided.Sec3
