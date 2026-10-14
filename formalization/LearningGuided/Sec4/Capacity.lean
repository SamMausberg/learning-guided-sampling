import LearningGuided.Sec4.HardFamily
import LearningGuided.Sec2.PublicCapacity

/-!
# Lemma `lem:capacity`: properties of the hard guide

The guide `h_θ` is positive, level-normalized, exact at leaves, satisfies `h ≤ 2μ` and
`h(ub) ≤ 2h(u)`, has stopped reciprocal capacity exactly `C_m = 2 + α - 2α² - α³ + α⁴ ≤ 17/8`,
and stopped additive defect `D_{9/4} = d_m`; `d_m δ_{x_θ}` is a coherent correction and every
coherent correction has mass at least `d_m`.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec4

open Sec2

variable {m : ℕ}

theorem dm_eq (m : ℕ) : dm m = alpha m - (5 / 4 + alpha m) * alpha m ^ 2 := by
  rw [dm, alpha_sq]; ring

theorem dm_pos (hm : 3 ≤ m) : 0 < dm m := by
  rw [dm_eq]
  have h1 := alpha_pos m
  have h2 := alpha_le_eighth hm
  nlinarith

/-- `d_m ≥ α/2` for `m ≥ 3` (used for `eq:fixed-B`). -/
theorem dm_ge_half_alpha (hm : 3 ≤ m) : alpha m / 2 ≤ dm m := by
  rw [dm_eq]
  have h1 := alpha_pos m
  have h2 := alpha_le_eighth hm
  nlinarith

theorem Cm_le (hm : 3 ≤ m) : Cm m ≤ 17 / 8 := by
  unfold Cm
  have h1 := alpha_pos m
  have h2 := alpha_le_eighth hm
  nlinarith [sq_nonneg (alpha m - 1 / 4), pow_pos h1 3]

theorem one_le_Cm (hm : 3 ≤ m) : 1 ≤ Cm m := by
  unfold Cm
  have h1 := alpha_pos m
  have h2 := alpha_le_eighth hm
  nlinarith [pow_pos h1 3, pow_pos h1 4]

/-! ### Values on and off the distinguished path -/

theorem pp_succ (t : ℕ) : ((2 : ℝ) ^ (t + 1))⁻¹ = ((2 : ℝ) ^ t)⁻¹ / 2 := by
  rw [pow_succ]; field_simp

theorem hθ_nonneg (hm : 3 ≤ m) (θ : Str (2 * m)) (u : List Bool) : 0 ≤ hθ m θ u := by
  by_cases hu : u.length ≤ 3 * m + 2
  · rw [hθ_of_le m θ hu]
    have := bet_lt_one hm hu
    have := bet_nonneg m u.length
    have : (0 : ℝ) ≤ if IsPre u (xθ m θ) then 1 else 0 := by split_ifs <;> norm_num
    positivity
  · rw [hθ_of_gt m θ (by omega)]

theorem hθ_pos (hm : 3 ≤ m) (θ : Str (2 * m)) {u : List Bool} (hu : u.length ≤ 3 * m + 2) :
    0 < hθ m θ u := by
  rw [hθ_of_le m θ hu]
  have h1 := bet_lt_one hm hu
  have h2 := bet_nonneg m u.length
  have h3 : (0 : ℝ) ≤ if IsPre u (xθ m θ) then 1 else 0 := by split_ifs <;> norm_num
  have h4 : 0 < (1 - bet m u.length) * ((2 : ℝ) ^ u.length)⁻¹ := by
    apply mul_pos (by linarith); positivity
  nlinarith

theorem isOracle_hθ (hm : 3 ≤ m) (θ : Str (2 * m)) : IsOracle (muθ m θ) (hθ m θ) := by
  refine ⟨hθ_nonneg hm θ, ?_, fun y => ?_, fun u hu => hθ_of_gt m θ hu⟩
  · rw [hθ_of_le m θ (by simp)]
    simp [bet_of_le (Nat.zero_le (2 * m))]
  · rw [hθ_of_le m θ (by simp)]
    simp only [List.length_ofFn, bet_last, isPre_ofFn_iff]
    simp [muθ, mixD, unif, dirac]

/-- `lem:capacity` (level normalization): the level sums of the guide are one. -/
theorem level_hθ (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    ∑ u ∈ words t, hθ m θ u = 1 := by
  have hval : ∀ u ∈ words t, hθ m θ u = (1 - bet m t) * mass (unif (3 * m + 2)) u +
      bet m t * mass (dirac (xθ m θ)) u := by
    intro u hu
    have hl := mem_words.mp hu
    rw [hθ_of_le m θ (by omega), mass_unif (by omega), mass_dirac, hl]
  rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_mass_words _ ht, sum_mass_words _ ht, (isDist_unif _).2, (isDist_dirac _).2]
  ring

theorem hθ_le_two_mu (hm : 3 ≤ m) (θ : Str (2 * m)) {u : List Bool}
    (hu : u.length ≤ 3 * m + 2) : hθ m θ u ≤ 2 * mass (muθ m θ) u := by
  rw [hθ_of_le m θ hu, mass_muθ m θ hu]
  have hb := bet_le_alpha (m := m) hu
  have hb0 := bet_nonneg m u.length
  have ha := alpha_le_eighth hm
  have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ u.length)⁻¹ := by positivity
  have hI : (0 : ℝ) ≤ if IsPre u (xθ m θ) then 1 else 0 := by split_ifs <;> norm_num
  nlinarith

theorem isPre_of_isPre_append {n : ℕ} {u : List Bool} {c : Bool} {x : Str n}
    (h : IsPre (u ++ [c]) x) : IsPre u x :=
  (List.prefix_append u [c]).trans h

/-- `lem:capacity` (bounded local growth): `h(ub) ≤ 2 h(u)`. -/
theorem hθ_growth (hm : 3 ≤ m) (θ : Str (2 * m)) {u : List Bool}
    (hu : u.length < 3 * m + 2) (c : Bool) : hθ m θ (u ++ [c]) ≤ 2 * hθ m θ u := by
  have hlen : (u ++ [c]).length = u.length + 1 := by simp
  rw [hθ_of_le m θ (by omega), hθ_of_le m θ hu.le, hlen, pp_succ]
  set t := u.length with ht
  set p := ((2 : ℝ) ^ t)⁻¹ with hp
  have hp0 : 0 ≤ p := by positivity
  set I := (if IsPre u (xθ m θ) then (1 : ℝ) else 0) with hI
  set I' := (if IsPre (u ++ [c]) (xθ m θ) then (1 : ℝ) else 0) with hI'
  have hI0 : 0 ≤ I' := by rw [hI']; split_ifs <;> norm_num
  have hII : I' ≤ I := by
    rw [hI, hI']
    by_cases h' : IsPre (u ++ [c]) (xθ m θ)
    · simp [h', isPre_of_isPre_append h']
    · simp only [h', ite_false]; split_ifs <;> norm_num
  have hI1 : I' ≤ 1 := by rw [hI']; split_ifs <;> norm_num
  have hb0 := bet_nonneg m t
  have hb1 := bet_le_alpha (m := m) hu.le
  have ha := alpha_le_eighth hm
  have ha0 := alpha_pos m
  rcases lt_trichotomy t (2 * m) with hlt | heq | hgt
  · rw [bet_of_le (by omega), bet_of_le (by omega)]
    nlinarith
  · rw [heq, bet_first, bet_of_le le_rfl]
    have hpv : p = alpha m ^ 2 := by rw [hp, heq, two_pow_inv_two_m]
    rw [hpv]
    have : 0 ≤ alpha m ^ 2 := sq_nonneg _
    nlinarith
  · rw [bet_succ hgt]
    nlinarith

/-- The value of the path cut at depth `t`. -/
noncomputable def pathF (m : ℕ) (θ : Str (2 * m)) (t : ℕ) : ℝ :=
  1 - mass (muθ m θ) (pre (xθ m θ) t) + mass (muθ m θ) (pre (xθ m θ) t) ^ 2 /
    hθ m θ (pre (xθ m θ) t)

theorem length_pre_x (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    (pre (xθ m θ) t).length = t := length_pre _ ht

theorem mass_path (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    mass (muθ m θ) (pre (xθ m θ) t) = (1 - alpha m) * ((2 : ℝ) ^ t)⁻¹ + alpha m := by
  rw [mass_muθ m θ (by rw [length_pre_x θ ht]; exact ht), length_pre_x θ ht,
    ite_eq_left (isPre_pre _ t)]
  ring

theorem hθ_path (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    hθ m θ (pre (xθ m θ) t) = (1 - bet m t) * ((2 : ℝ) ^ t)⁻¹ + bet m t := by
  rw [hθ_of_le m θ (by rw [length_pre_x θ ht]; exact ht), length_pre_x θ ht,
    ite_eq_left (isPre_pre _ t)]
  ring

/-- `C_m` is the value of the path cut at depth `k = 2m`. -/
theorem pathF_k (θ : Str (2 * m)) : pathF m θ (2 * m) = Cm m := by
  unfold pathF
  rw [mass_path θ (by omega), hθ_path θ (by omega), bet_of_le le_rfl, two_pow_inv_two_m]
  have h := alpha_pos m
  unfold Cm
  field_simp
  ring

theorem pathF_le (hm : 3 ≤ m) (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    pathF m θ t ≤ Cm m := by
  unfold pathF
  rw [mass_path θ ht, hθ_path θ ht]
  set α := alpha m with hα
  have ha0 : 0 < α := alpha_pos m
  have ha := alpha_le_eighth hm
  set p := ((2 : ℝ) ^ t)⁻¹ with hp
  have hp0 : 0 < p := by positivity
  rcases lt_trichotomy t (2 * m + 1) with hlt | heq | hgt
  · -- depths up to `k`
    rw [bet_of_le (by omega)]
    have hpa : α ^ 2 ≤ p := alpha_sq_le_pp (by omega)
    have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have e : ((1 - α) * p + α) ^ 2 / ((1 - 0) * p + 0) =
        (1 - α) ^ 2 * p + 2 * (1 - α) * α + α ^ 2 / p := by field_simp; ring
    rw [e]
    have h1 : α ^ 2 / p ≤ 1 := (div_le_one hp0).mpr (hpa.trans (by nlinarith))
    have h2 : 0 ≤ (1 - α) * α * (p - α ^ 2) := by
      apply mul_nonneg (mul_nonneg (by linarith) ha0.le) (by linarith)
    unfold Cm
    nlinarith
  · -- the first padding step
    rw [heq, bet_first, ← hα]
    have hpv : p = α ^ 2 / 2 := by
      rw [hp, heq, pp_succ, two_pow_inv_two_m]
    rw [hpv]
    set μ1 := (1 - α) * (α ^ 2 / 2) + α with hμ1
    set h1 := (1 - α ^ 2 / 2) * (α ^ 2 / 2) + α ^ 2 / 2 with hh1
    have hh1pos : 0 < h1 := by
      have h2 : 0 < α ^ 2 := by positivity
      have h3 : α ^ 2 ≤ 1 := by nlinarith
      rw [hh1]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have key : (Cm m - 1 + μ1) * h1 - μ1 ^ 2 =
        α ^ 3 * (2 - α) * (1 + α) * (2 * α ^ 3 - α ^ 2 - 6 * α + 4) / 8 := by
      rw [hμ1, hh1]; unfold Cm; ring
    have hpoly : 0 < 2 * α ^ 3 - α ^ 2 - 6 * α + 4 := by nlinarith
    have hnn : 0 ≤ α ^ 3 * (2 - α) * (1 + α) * (2 * α ^ 3 - α ^ 2 - 6 * α + 4) / 8 := by
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
        hpoly.le
    have : μ1 ^ 2 / h1 ≤ Cm m - 1 + μ1 := by
      rw [div_le_iff₀ hh1pos]; linarith
    linarith
  · -- later padding steps
    have hb : α ^ 2 ≤ bet m t := alpha_sq_le_bet (by omega)
    have hb1 : bet m t < 1 := bet_lt_one hm ht
    have hpa : p ≤ α ^ 2 := pp_le_alpha_sq (by omega)
    set μ := (1 - α) * p + α with hμ
    set hv := (1 - bet m t) * p + bet m t with hhv
    have hhv : α ^ 2 ≤ hv := by
      rw [hhv]; nlinarith
    have hα2 : 0 < α ^ 2 := by positivity
    have hμ0 : 0 ≤ μ := by rw [hμ]; nlinarith
    have hstep : μ ^ 2 / hv ≤ μ ^ 2 / α ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg μ) hα2 hhv
    set μk := (1 - α) * α ^ 2 + α with hμk
    have hμle : μ ≤ μk := by rw [hμ, hμk]; nlinarith
    have hsum : α ^ 2 ≤ μk + μ := by rw [hμ, hμk]; nlinarith
    have key : (Cm m - 1 + μ) * α ^ 2 - μ ^ 2 = (μk - μ) * (μk + μ - α ^ 2) := by
      rw [hμk]; unfold Cm; ring
    have hnn : 0 ≤ (μk - μ) * (μk + μ - α ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    have : μ ^ 2 / α ^ 2 ≤ Cm m - 1 + μ := by
      rw [div_le_iff₀ hα2]; linarith
    linarith

/-- Off the distinguished path the guide dominates the target. -/
theorem off_path (θ : Str (2 * m)) {u : List Bool} (hu : u.length ≤ 3 * m + 2)
    (hux : ¬ IsPre u (xθ m θ)) :
    mass (muθ m θ) u = (1 - alpha m) * ((2 : ℝ) ^ u.length)⁻¹ ∧
      hθ m θ u = (1 - bet m u.length) * ((2 : ℝ) ^ u.length)⁻¹ ∧
      mass (muθ m θ) u ≤ hθ m θ u := by
  rw [mass_muθ m θ hu, hθ_of_le m θ hu, ite_eq_right hux]
  refine ⟨by ring, by ring, ?_⟩
  have := bet_le_alpha (m := m) hu
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ u.length)⁻¹ := by positivity
  nlinarith

/-- `lem:capacity`, equation `eq:capacity-value` (capacity part): `CC(μ_θ,h_θ) = C_m`. -/
theorem capEq_hθ (hm : 3 ≤ m) (θ : Str (2 * m)) : CapEq (muθ m θ) (hθ m θ) (Cm m) := by
  have hμ := isDist_muθ m θ
  have hor := isOracle_hθ hm θ
  refine ⟨⟨fun u hu _ => ne_of_gt (hθ_pos hm θ hu), ?_⟩, ?_⟩
  · refine cutSum_le_of_path hμ (xθ m θ) (one_le_Cm hm) (fun u hu hux => ?_)
      (fun t ht => pathF_le hm θ ht)
    obtain ⟨_, _, hle⟩ := off_path θ hu hux
    exact sq_div_le_of_le (mass_nonneg hμ.1 u) hle (hθ_pos hm θ hu)
  · obtain ⟨A, hA, hval⟩ := exists_path_cut hμ hor.leaf (xθ m θ) (t := 2 * m) (by omega)
    exact ⟨A, hA, hval.trans (pathF_k θ)⟩

/-! ### Defects -/

theorem defect_off_path (hm : 3 ≤ m) (θ : Str (2 * m)) {u : List Bool}
    (hu : u.length ≤ 3 * m + 2) (hux : ¬ IsPre u (xθ m θ)) :
    defect (9 / 4) (muθ m θ) (hθ m θ) u = 0 := by
  obtain ⟨_, _, hle⟩ := off_path θ hu hux
  have h2 := hθ_le_two_mu hm θ hu
  have h0 := mass_nonneg (isDist_muθ m θ).1 u
  have h0' := hθ_nonneg hm θ u
  unfold defect
  apply le_antisymm _ (le_max_left _ _)
  refine max_le le_rfl (max_le (by linarith) (by linarith))

theorem path_demand_le (hm : 3 ≤ m) (θ : Str (2 * m)) {t : ℕ} (ht : t ≤ 3 * m + 2) :
    mass (muθ m θ) (pre (xθ m θ) t) - 9 / 4 * hθ m θ (pre (xθ m θ) t) ≤ dm m := by
  rw [mass_path θ ht, hθ_path θ ht, dm_eq]
  set α := alpha m with hα
  have ha0 : 0 < α := alpha_pos m
  have ha := alpha_le_eighth hm
  set p := ((2 : ℝ) ^ t)⁻¹ with hp
  have hp0 : 0 < p := by positivity
  rcases lt_trichotomy t (2 * m + 1) with hlt | heq | hgt
  · rw [bet_of_le (by omega)]
    have hpa : α ^ 2 ≤ p := alpha_sq_le_pp (by omega)
    nlinarith
  · rw [heq, bet_first, ← hα]
    have hpv : p = α ^ 2 / 2 := by
      rw [hp, heq, pp_succ, two_pow_inv_two_m]
    rw [hpv]
    have key : α - (5 / 4 + α) * α ^ 2 -
        ((1 - α) * (α ^ 2 / 2) + α - 9 / 4 * ((1 - α ^ 2 / 2) * (α ^ 2 / 2) + α ^ 2 / 2)) =
        α ^ 2 * (8 - 8 * α - 9 * α ^ 2) / 16 := by ring
    have : 0 ≤ α ^ 2 * (8 - 8 * α - 9 * α ^ 2) / 16 := by
      apply div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) (by norm_num)
    linarith
  · have hb : α ^ 2 ≤ bet m t := alpha_sq_le_bet (by omega)
    have hb1 : bet m t < 1 := bet_lt_one hm ht
    have hpa : p ≤ α ^ 2 := pp_le_alpha_sq (by omega)
    nlinarith

theorem path_demand_k (θ : Str (2 * m)) :
    mass (muθ m θ) (pre (xθ m θ) (2 * m)) - 9 / 4 * hθ m θ (pre (xθ m θ) (2 * m)) = dm m := by
  rw [mass_path θ (by omega), hθ_path θ (by omega), dm_eq, bet_of_le le_rfl, two_pow_inv_two_m]
  ring

/-- Every demand is dominated by `d_m 1{u ⪯ x_θ}`. -/
theorem defect_le (hm : 3 ≤ m) (θ : Str (2 * m)) {u : List Bool}
    (hu : u.length ≤ 3 * m + 2) :
    defect (9 / 4) (muθ m θ) (hθ m θ) u ≤ dm m * (if IsPre u (xθ m θ) then 1 else 0) := by
  by_cases hux : IsPre u (xθ m θ)
  · rw [ite_eq_left hux, mul_one]
    have hu' : u = pre (xθ m θ) u.length := isPre_iff_pre.mp hux
    have h2 := hθ_le_two_mu hm θ hu
    have h0 := mass_nonneg (isDist_muθ m θ).1 u
    have hd := path_demand_le hm θ hu
    rw [← hu'] at hd
    have := dm_pos hm
    unfold defect
    exact max_le (dm_pos hm).le (max_le (by linarith) hd)
  · rw [defect_off_path hm θ hu hux, ite_eq_right hux, mul_zero]

theorem defect_k (hm : 3 ≤ m) (θ : Str (2 * m)) :
    defect (9 / 4) (muθ m θ) (hθ m θ) (pre (xθ m θ) (2 * m)) = dm m := by
  have hle := defect_le hm θ (u := pre (xθ m θ) (2 * m))
    (by rw [length_pre_x θ (by omega)]; omega)
  rw [ite_eq_left (isPre_pre _ _), mul_one] at hle
  refine le_antisymm hle ?_
  unfold defect
  rw [← path_demand_k θ]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- `lem:capacity`, equation `eq:capacity-value` (defect part): `D_{9/4}(μ_θ,h_θ) = d_m`. -/
theorem defectEq_hθ (hm : 3 ≤ m) (θ : Str (2 * m)) :
    DefectEq (9 / 4) (muθ m θ) (hθ m θ) (dm m) := by
  classical
  refine ⟨fun A hA => ?_, ⟨{pre (xθ m θ) (2 * m)},
    isCut_singleton (by rw [length_pre_x θ (by omega)]; omega), by simp [defect_k hm θ]⟩⟩
  calc ∑ u ∈ A, defect (9 / 4) (muθ m θ) (hθ m θ) u
      ≤ ∑ u ∈ A, dm m * (if IsPre u (xθ m θ) then 1 else 0) :=
        Finset.sum_le_sum fun u hu => defect_le hm θ (hA.1 u hu)
    _ = dm m * (A.filter fun u => IsPre u (xθ m θ)).card := by
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ dm m * 1 := by
        gcongr
        · exact (dm_pos hm).le
        · exact_mod_cast hA.card_filter_isPre_le_one _
    _ = dm m := mul_one _

/-- The optimal correction `d_m δ_{x_θ}`. -/
noncomputable def optCorr (m : ℕ) (θ : Str (2 * m)) : Str (3 * m + 2) → ℝ :=
  fun x => dm m * dirac (xθ m θ) x

theorem mass_optCorr (θ : Str (2 * m)) (u : List Bool) :
    mass (optCorr m θ) u = dm m * (if IsPre u (xθ m θ) then 1 else 0) := by
  unfold optCorr; rw [mass_smul, mass_dirac]

theorem sum_optCorr (θ : Str (2 * m)) : ∑ x, optCorr m θ x = dm m := by
  unfold optCorr; rw [← Finset.mul_sum, (isDist_dirac _).2, mul_one]

theorem isCorrection_optCorr (hm : 3 ≤ m) (θ : Str (2 * m)) :
    IsCorrection (9 / 4) (muθ m θ) (hθ m θ) (optCorr m θ) := by
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · unfold optCorr dirac
    have := (dm_pos hm).le
    split_ifs <;> simp [this]
  · rw [mass_optCorr]; exact defect_le hm θ hu

/-- `lem:capacity`: every coherent correction puts mass at least `d_m` on the depth-`k` prefix
naming the key. -/
theorem correction_mass_k (hm : 3 ≤ m) (θ : Str (2 * m)) {κ : Str (3 * m + 2) → ℝ}
    (hκ : IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ) :
    dm m ≤ mass κ (pre (xθ m θ) (2 * m)) := by
  rw [← defect_k hm θ]
  exact hκ.2 _ (by rw [length_pre_x θ (by omega)]; omega)

theorem correction_mass_ge (hm : 3 ≤ m) (θ : Str (2 * m)) {κ : Str (3 * m + 2) → ℝ}
    (hκ : IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ) : dm m ≤ ∑ x, κ x :=
  (correction_mass_k hm θ hκ).trans (mass_le_total hκ.1 _)

/-- `lem:capacity`: the guide `h_θ` is positive and level-normalized, satisfies the access
conditions (in particular it is exact at the leaves), `h ≤ 2μ` and `h(ub) ≤ 2h(u)`; its stopped
reciprocal capacity is exactly `C_m = 2 + α - 2α² - α³ + α⁴ ≤ 17/8 < 9/4`, its stopped additive
defect at factor `9/4` is exactly `d_m`, `d_m δ_{x_θ}` is a coherent correction of mass `d_m`, and
every coherent correction has mass at least `d_m`. -/
theorem lem_capacity (hm : 3 ≤ m) (θ : Str (2 * m)) :
    IsOracle (muθ m θ) (hθ m θ) ∧
      (∀ u : List Bool, u.length ≤ 3 * m + 2 → 0 < hθ m θ u) ∧
      (∀ t ≤ 3 * m + 2, ∑ u ∈ words t, hθ m θ u = 1) ∧
      (∀ u : List Bool, u.length ≤ 3 * m + 2 → hθ m θ u ≤ 2 * mass (muθ m θ) u) ∧
      (∀ u : List Bool, u.length < 3 * m + 2 → ∀ c : Bool,
        hθ m θ (u ++ [c]) ≤ 2 * hθ m θ u) ∧
      CapEq (muθ m θ) (hθ m θ) (Cm m) ∧ Cm m ≤ 17 / 8 ∧ (17 / 8 : ℝ) < 9 / 4 ∧
      DefectEq (9 / 4) (muθ m θ) (hθ m θ) (dm m) ∧
      IsCorrection (9 / 4) (muθ m θ) (hθ m θ) (optCorr m θ) ∧ ∑ x, optCorr m θ x = dm m ∧
      ∀ κ, IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ → dm m ≤ ∑ x, κ x :=
  ⟨isOracle_hθ hm θ, fun _ hu => hθ_pos hm θ hu, fun _ ht => level_hθ θ ht,
    fun _ hu => hθ_le_two_mu hm θ hu, fun _ hu c => hθ_growth hm θ hu c, capEq_hθ hm θ,
    Cm_le hm, by norm_num, defectEq_hθ hm θ, isCorrection_optCorr hm θ, sum_optCorr θ,
    fun _ hκ => correction_mass_ge hm θ hκ⟩

/-- `lem:capacity`, `thm:main`: the hard guides are legal in the safe model with `R = C = 9/4`. -/
theorem safeLegal_hθ (hm : 3 ≤ m) (θ : Str (2 * m)) :
    SafeLegal (9 / 4) (9 / 4) (muθ m θ) (hθ m θ) := by
  refine ⟨isOracle_hθ hm θ, fun u hu => ?_, ⟨(capEq_hθ hm θ).1.1, fun A hA => ?_⟩⟩
  · have := hθ_le_two_mu hm θ hu
    have := mass_nonneg (isDist_muθ m θ).1 u
    linarith
  · have := (capEq_hθ hm θ).1.2 A hA
    have := Cm_le hm
    linarith

end Sec4
end LearningGuided
