import LearningGuided.Sec3.SplitTree

/-!
# Arbitrary known backgrounds: the partition sampler and the upper bound

* `splitSampler`: search the groups of the split tree of a known mass `w` at threshold `τ`, test
  light groups with a threshold and leaf groups exactly, recover by balanced prefix tests, draw
  from the background on every other branch (exact output law `lawR_splitSampler`);
* `background_partition` (Lemma `lem:background-partition`): with `τ = α²/(2RCa)` and the split
  tree of the background, the partition properties, the count `eq:partition-count`, and an exact
  sampler with the deterministic cap `eq:background-cap` under `eq:capacity-model`;
* `background_upper` (upper bound of Theorem `thm:background`) for every known background and
  every known set of `M` atoms, at `R = C = 9/4`.
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### The partition sampler on the split tree -/

open Classical in
/-- Test of a group: exact detection at a leaf group, the threshold `θ₀` otherwise. -/
noncomputable def bgTest (n : ℕ) (ν : Str n → ℝ) (α θ₀ : ℝ) (u : List Bool) (r : ℝ) : Prop :=
  if u.length = n then (1 - α) * mass ν u + α ≤ r else θ₀ ≤ r

open Classical in
/-- Recovery inside a group: nothing to do at a leaf group, balanced prefix tests otherwise. -/
noncomputable def bgRec (S : Finset (Str n)) (θ₀ : ℝ) (fuel : ℕ) (u : List Bool) :
    Alg (Str n) :=
  if u.length = n then .ret (strOf n u) else balRec u (fun r => θ₀ ≤ r) (S.filter (IsPre u)) fuel

/-- The partition sampler on the leaves of the split tree of `w` at threshold `τ`. -/
noncomputable def splitSampler (ν w : Str n → ℝ) (τ : ℝ) (S : Finset (Str n)) (α θ₀ : ℝ)
    (fuel : ℕ) : Alg (Str n) :=
  partSampler (splitGroup w τ) S α (bgTest n ν α θ₀) (bgRec S θ₀ fuel) (drawA ν)

theorem within_splitSampler (ν w : Str n → ℝ) (τ : ℝ) (S : Finset (Str n)) {α : ℝ} (θ₀ : ℝ)
    (fuel : ℕ) (h : Guide) :
    (splitSampler ν w τ S α θ₀ fuel).Within h
      (⌈α * (S.image (splitGroup w τ)).card⌉₊ + fuel) := by
  refine within_partSampler _ _ _ _ _ _ (fun u _ => ?_) (within_drawA _ h 0)
  unfold bgRec
  split_ifs
  · exact Alg.Within.ret _ _
  · exact within_balRec _ _ h _ _

theorem isPre_iff_strOf {u : List Bool} (hu : u.length = n) {x : Str n} :
    IsPre u x ↔ strOf n u = x := by
  constructor
  · exact eq_strOf_of_isPre hu
  · intro h
    rw [← h, ← ofFn_strOf hu, strOf_ofFn, isPre_ofFn_iff]

/-- `lem:background-partition`, output law of the partition sampler: if the threshold test is exact
below every nonleaf group of a candidate and the fuel suffices for every group, the output law is
`(1-α)ν + αδ_x` for every guide satisfying `eq:oracle`. -/
theorem lawR_splitSampler {ν w : Str n → ℝ} (hν : IsDist ν) {τ : ℝ} {S : Finset (Str n)}
    {α θ₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {fuel : ℕ} {x : Str n} (hx : x ∈ S) {h : Guide}
    (hl : IsOracle (atomTarget ν α x) h)
    (hvalid : ∀ y ∈ S, (splitGroup w τ y).length < n → ∀ v : List Bool,
      splitGroup w τ y <+: v → v.length ≤ n → (θ₀ ≤ h v ↔ IsPre v x))
    (hfuel : ∀ y ∈ S, (splitGroup w τ y).length < n →
      2 ^ fuel * (S.filter (IsPre (splitGroup w τ y))).card < 2 * 3 ^ fuel) :
    lawR ((splitSampler ν w τ S α θ₀ fuel).run h) = atomTarget ν α x := by
  refine lawR_partSampler _ hα.le hα1 _ _ _ hx (fun y _ => splitGroup_isPre_iff)
    (fun u hu => ?_) ?_ (lawR_drawA hν h)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
    unfold bgTest
    split_ifs with hlen
    · rw [isPre_iff_strOf hlen, ← ofFn_strOf hlen, leaf_test hα hl, ofFn_strOf hlen]
    · have hlt : (splitGroup w τ y).length < n := by
        have := length_splitGroup w τ y ▸ splitDepth_le w τ y
        omega
      exact hvalid y hy hlt _ List.prefix_rfl (by omega)
  · unfold bgRec
    split_ifs with hlen
    · rw [Alg.run_ret, eq_strOf_of_isPre hlen (isPre_splitGroup w τ x)]
    · have hlt : (splitGroup w τ x).length < n := by
        have := length_splitGroup w τ x ▸ splitDepth_le w τ x
        omega
      exact run_balRec hlt.le _ (fun v hv hvn => hvalid x hx hlt v hv hvn) _ _
        (Finset.mem_filter.mpr ⟨hx, isPre_splitGroup w τ x⟩)
        (fun y hy => (Finset.mem_filter.mp hy).2) (hfuel x hx hlt)

/-! ### Lemma `lem:background-partition` -/

/-- The threshold `τ = α²/(2RCa)`, `a = 1-α`. -/
noncomputable def bgTau (R C α : ℝ) : ℝ := α ^ 2 / (2 * R * C * (1 - α))

theorem bgTau_pos {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1) :
    0 < bgTau R C α := by
  unfold bgTau
  have : 0 < 1 - α := by linarith
  positivity

/-- In a light group the background contributes too little: `R a ν(v) ≤ α²/(2C) < α²/C`. -/
theorem bg_gap {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1) {m : ℝ}
    (hm : m ≤ bgTau R C α) : R * ((1 - α) * m) < α ^ 2 / C := by
  have ha : 0 < 1 - α := by linarith
  unfold bgTau at hm
  rw [le_div_iff₀ (by positivity)] at hm
  rw [lt_div_iff₀ hC]
  have : 0 < α ^ 2 := by positivity
  nlinarith

/-- `lem:background-partition`, test: the threshold test is exact below every light group of the
split tree of the background. -/
theorem bg_valid {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1)
    {ν : Str n → ℝ} (hν : IsDist ν) {x : Str n} {h : Guide}
    (hl : SafeLegal R C (atomTarget ν α x) h) (y : Str n)
    (hlen : (splitGroup ν (bgTau R C α) y).length < n) (v : List Bool)
    (hv : splitGroup ν (bgTau R C α) y <+: v) (hvn : v.length ≤ n) :
    α ^ 2 / C ≤ h v ↔ IsPre v x :=
  safe_test hν hα hα1.le hC hl hvn (bg_gap hR hC hα hα1
    ((mass_le_of_prefix hν.1 hv).trans (splitGroup_light ν _ y hlen)))

/-- The cap `eq:background-cap`: `min{⌈αM⌉, ⌈αG⌉ + ⌈log_{3/2} M⌉}`. -/
noncomputable def bgCap (M G : ℕ) (α : ℝ) : ℕ := min ⌈α * M⌉₊ (⌈α * G⌉₊ + balFuel M)

open Classical in
/-- The exact sampler of `lem:background-partition`: the cheaper of the partition sampler and
direct leaf search. -/
noncomputable def bgSampler (ν : Str n → ℝ) (S : Finset (Str n)) (R C α : ℝ) : Alg (Str n) :=
  if ⌈α * (S.image (splitGroup ν (bgTau R C α))).card⌉₊ + balFuel S.card ≤ ⌈α * S.card⌉₊ then
    splitSampler ν ν (bgTau R C α) S α (α ^ 2 / C) (balFuel S.card)
  else leafSampler ν S α α

theorem fuel_ok_filter (S : Finset (Str n)) (hS : S.Nonempty) (g : List Bool) :
    2 ^ balFuel S.card * (S.filter (IsPre g)).card < 2 * 3 ^ balFuel S.card := by
  have hM : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
  exact fuel_ok hM (by exact_mod_cast Finset.card_filter_le _ _)

/-- `lem:background-partition`: let `R, C > 0`, `0 < α < 1`, `a = 1-α`,
`τ = α²/(2RCa)`, `ν` a known background and `S` a known nonempty candidate set. The leaves of the
split tree of `ν` partition the strings (every group of a candidate is a prefix of exactly the
candidates in it), every group is light (`ν(g) ≤ τ`) or a single leaf, the number `G` of groups
containing candidates satisfies `eq:partition-count`, and `bgSampler` is an exact sampler under
`eq:capacity-model` with the deterministic cap `eq:background-cap`. -/
theorem background_partition {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1)
    {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hS : S.Nonempty) :
    (∀ x y : Str n, IsPre (splitGroup ν (bgTau R C α) x) y →
      splitGroup ν (bgTau R C α) y = splitGroup ν (bgTau R C α) x) ∧
    (∀ x : Str n, (splitGroup ν (bgTau R C α) x).length = n ∨
      mass ν (splitGroup ν (bgTau R C α) x) ≤ bgTau R C α) ∧
    (((S.image (splitGroup ν (bgTau R C α))).card : ℝ) ≤
      min (S.card : ℝ) (1 + ∑ t ∈ Finset.range n, min ((2 : ℝ) ^ t) (bgTau R C α)⁻¹)) ∧
    Solves (SafeLegal R C) (atomClass ν S α) 0
      (bgCap S.card (S.image (splitGroup ν (bgTau R C α))).card α) (bgSampler ν S R C α) := by
  refine ⟨fun x y h => splitGroup_part h, fun x => ?_,
    card_splitGroups_le hν (bgTau_pos hR hC hα hα1) S, ?_⟩
  · by_cases hlen : (splitGroup ν (bgTau R C α) x).length < n
    · exact Or.inr (splitGroup_light ν _ x hlen)
    · left
      have := length_splitGroup ν (bgTau R C α) x ▸ splitDepth_le ν (bgTau R C α) x
      omega
  · refine solves_of_law (β := α) hν (by simp) (fun h => ?_) (fun x hx h hl => ?_)
    · unfold bgSampler bgCap
      split_ifs with hc
      · rw [min_eq_right hc]
        exact within_splitSampler _ _ _ _ _ _ h
      · rw [min_eq_left (by omega)]
        exact within_leafSampler _ _ _ _ h
    · unfold bgSampler
      split_ifs
      · exact lawR_splitSampler hν hα hα1.le hx hl.1
          (fun y _ hlen v hv hvn => bg_valid hR hC hα hα1 hν hl y hlen v hv hvn)
          (fun _ _ _ => fuel_ok_filter S hS _)
      · exact lawR_leafSampler hν hα hα.le hα1.le hx hl.1

/-! ### The rate computation -/

/-- `∑_{t<n} min{2^t, T} ≤ 2T + T L` whenever `T ≥ 1/2`, `L ≥ 0` and `n - log₂ T ≤ L`. -/
theorem sum_min_pow_le {T : ℝ} (hT : 1 / 2 ≤ T) (n : ℕ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : (n : ℝ) - Real.logb 2 T ≤ L) :
    ∑ t ∈ Finset.range n, min ((2 : ℝ) ^ t) T ≤ 2 * T + T * L := by
  classical
  set m := depthFor T with hm
  have h2m : (2 : ℝ) ^ m ≤ 2 * T := two_pow_depthFor_le (by linarith)
  have hTm : T ≤ (2 : ℝ) ^ m := depthFor_spec T
  have hlogm : Real.logb 2 T ≤ m := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hTm
    rwa [logb_two_pow] at this
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun t => t < m)]
  have h1 : ∑ t ∈ (Finset.range n).filter (fun t => t < m), min ((2 : ℝ) ^ t) T ≤ 2 * T := by
    calc ∑ t ∈ (Finset.range n).filter (fun t => t < m), min ((2 : ℝ) ^ t) T
        ≤ ∑ t ∈ Finset.range m, (2 : ℝ) ^ t := by
          refine (Finset.sum_le_sum fun t _ => min_le_left _ _).trans ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => by positivity
          exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
      _ = 2 ^ m - 1 := by
          rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
          ring
      _ ≤ 2 * T := by linarith
  have h2 : ∑ t ∈ (Finset.range n).filter (fun t => ¬ t < m), min ((2 : ℝ) ^ t) T ≤ T * L := by
    have hsub : (Finset.range n).filter (fun t => ¬ t < m) ⊆ Finset.Ico m n := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      exact Finset.mem_Ico.mpr ⟨by omega, ht.1⟩
    have hcard : (((Finset.range n).filter (fun t => ¬ t < m)).card : ℝ) ≤ L := by
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hc
      rcases le_total m n with hmn | hmn
      · have : (((Finset.range n).filter (fun t => ¬ t < m)).card : ℝ) ≤ (n : ℝ) - m := by
          rw [← Nat.cast_sub hmn]
          exact_mod_cast hc
        linarith
      · have : n - m = 0 := by omega
        rw [this] at hc
        have : ((Finset.range n).filter (fun t => ¬ t < m)).card = 0 := by omega
        rw [this, Nat.cast_zero]
        exact hL0
    calc ∑ t ∈ (Finset.range n).filter (fun t => ¬ t < m), min ((2 : ℝ) ^ t) T
        ≤ ∑ t ∈ (Finset.range n).filter (fun t => ¬ t < m), T :=
          Finset.sum_le_sum fun t _ => min_le_right _ _
      _ = ((Finset.range n).filter (fun t => ¬ t < m)).card * T := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L * T := by gcongr
      _ = T * L := by ring
  linarith

theorem log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- `thm:background`, upper rate from the cap `eq:background-cap` and the count
`eq:partition-count`, at `R = C = 9/4`. -/
theorem bgCap_le_rate {n M G : ℕ} {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hM : 2 ≤ M)
    (hMn : (M : ℝ) ≤ 2 ^ n)
    (hG : (G : ℝ) ≤ 1 + ∑ t ∈ Finset.range n,
      min ((2 : ℝ) ^ t) (bgTau (9 / 4) (9 / 4) α)⁻¹) :
    (bgCap M G α : ℝ) ≤ 75 * (1 + min (α * M) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) := by
  set B := α⁻¹ with hB
  set z : ℝ := 2 ^ n * α ^ 2 with hz
  have hB4 : 4 ≤ B := by
    rw [hB, le_inv_comm₀ (by norm_num) hα0]
    linarith
  have hαB : α * B = 1 := mul_inv_cancel₀ hα0.ne'
  have hz0 : 0 < z := by positivity
  have hAM0 : 0 ≤ α * M := by positivity
  have hαMz : α * M ≤ B * z := by
    have : α * M ≤ α * 2 ^ n := mul_le_mul_of_nonneg_left hMn hα0.le
    have e : B * z = α * 2 ^ n := by
      rw [hz, hB]
      field_simp
    linarith
  have hleaf : (⌈α * M⌉₊ : ℝ) ≤ α * M + 1 := ceil_le_add_one hAM0
  have hcapleaf : (bgCap M G α : ℝ) ≤ α * M + 1 := by
    unfold bgCap
    push_cast
    exact (min_le_left _ _).trans hleaf
  have hlog0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  rcases le_total z 1 with hz1 | hz1
  · -- `z ≤ 1`: leaf search
    have hlz := half_le_log_one_add hz0.le hz1
    have : α * M ≤ 2 * min (α * M) (B * Real.log (1 + z)) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      refine le_min (by linarith) ?_
      have : B * z ≤ 2 * (B * Real.log (1 + z)) := by nlinarith
      linarith
    have hmin0 : 0 ≤ min (α * M) (B * Real.log (1 + z)) := le_min hAM0 (by positivity)
    linarith
  · -- `z ≥ 1`: the partition sampler
    set T := (bgTau (9 / 4) (9 / 4) α)⁻¹ with hT
    have hTe : T = 81 / 8 * (1 - α) * B ^ 2 := by
      rw [hT, bgTau, hB]
      field_simp
      ring
    have hTge : B ^ 2 ≤ T := by
      rw [hTe]
      have : 0 ≤ B ^ 2 := by positivity
      nlinarith
    have hTle : T ≤ 81 / 8 * B ^ 2 := by
      rw [hTe]
      have : 0 ≤ B ^ 2 := by positivity
      nlinarith
    have hlogz0 : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hz1
    have hnB : (n : ℝ) = Real.logb 2 z + 2 * Real.logb 2 B := by
      have e : z = 2 ^ n * (B ^ 2)⁻¹ := by
        rw [hz, hB]
        field_simp
      rw [e, Real.logb_mul (by positivity) (by positivity), logb_two_pow, Real.logb_inv,
        Real.logb_pow]
      push_cast
      ring
    have hlogT : 2 * Real.logb 2 B ≤ Real.logb 2 T := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hTge
      rwa [Real.logb_pow] at this
    have hsum := sum_min_pow_le (T := T) (by nlinarith) n hlogz0 (by linarith)
    have hGb : α * G ≤ 1 / 4 + 81 / 8 * B * (2 + Real.logb 2 z) := by
      have h1 : α * G ≤ α * (1 + (2 * T + T * Real.logb 2 z)) :=
        mul_le_mul_of_nonneg_left (hG.trans (by linarith)) hα0.le
      have h2 : α * T ≤ 81 / 8 * B := by
        have : α * T ≤ α * (81 / 8 * B ^ 2) := mul_le_mul_of_nonneg_left hTle hα0.le
        have e : α * (81 / 8 * B ^ 2) = 81 / 8 * B := by
          rw [show α * (81 / 8 * B ^ 2) = 81 / 8 * B * (α * B) by ring, hαB, mul_one]
        linarith
      have h3 : α * (1 + (2 * T + T * Real.logb 2 z)) = α + α * T * (2 + Real.logb 2 z) := by
        ring
      rw [h3] at h1
      have : α * T * (2 + Real.logb 2 z) ≤ 81 / 8 * B * (2 + Real.logb 2 z) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      linarith
    have hlogb_le : Real.logb 2 z ≤ 2 * Real.log z := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have := log_two_gt_half
      have : 0 ≤ Real.log z := Real.log_nonneg hz1
      nlinarith
    have hlogM : Real.log M ≤ Real.log z + B := by
      have h1 : Real.log M ≤ n * Real.log 2 := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hMn
      have h2 : Real.logb 2 z * Real.log 2 = Real.log z := by
        rw [Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
      have h3 := logb_two_le_half hB4
      have h4 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      rw [hnB] at h1
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hfuel := balFuel_le (by omega : 1 ≤ M)
    have hceil := ceil_le_add_one (x := α * G) (by positivity)
    have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hl1 : Real.log z ≤ Real.log (1 + z) := Real.log_le_log hz0 (by linarith)
    have hl2 : 1 / 2 ≤ Real.log (1 + z) := by
      have := Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ 1 + z)
      linarith [log_two_gt_half]
    have hpart : (bgCap M G α : ℝ) ≤ 75 * (B * Real.log (1 + z)) := by
      unfold bgCap
      push_cast
      refine (min_le_right _ _).trans ?_
      have hBlz : 0 ≤ B * Real.log z := by positivity
      nlinarith
    have hmin0 : 0 ≤ min (α * M) (B * Real.log (1 + z)) := le_min hAM0 (by positivity)
    rcases le_total (α * M) (B * Real.log (1 + z)) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith

/-- `thm:background`, upper bound for exact sampling: for every known background
`ν` and every known set `S` of `M` distinct atoms (`2 ≤ M ≤ 2^n`, `0 < α ≤ 1/4`), and every
`δ ≥ 0`, `Q_safe ≤ 75 (1 + min{αM, α⁻¹ log(1 + 2^n α²)})`. -/
theorem background_upper {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ)
    {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} (hM : 2 ≤ S.card) :
    (Qsafe (atomClass ν S α) δ : ℝ) ≤
      75 * (1 + min (α * S.card) (α⁻¹ * Real.log (1 + 2 ^ n * α ^ 2))) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨-, -, hcount, hsolve⟩ := background_partition (n := n) (by norm_num : (0 : ℝ) < 9 / 4)
    (by norm_num : (0 : ℝ) < 9 / 4) hα0 (by linarith) hν hS
  have hQ := Qcx_le (solves_mono_delta hδ0 hsolve)
  have hQ' : (Qsafe (atomClass ν S α) δ : ℝ) ≤
      bgCap S.card (S.image (splitGroup ν (bgTau (9 / 4) (9 / 4) α))).card α := by
    exact_mod_cast hQ
  refine hQ'.trans (bgCap_le_rate hα0 hα hM ?_ ((le_min_iff.mp hcount).2))
  have := Finset.card_le_univ S
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  exact_mod_cast this

end LearningGuided.Sec3
