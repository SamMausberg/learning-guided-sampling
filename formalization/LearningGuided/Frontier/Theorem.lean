import LearningGuided.Frontier.Analysis

/-!
# The safe frontier learner: error analysis (Appendix `app:frontier`)

Fix a target `μ`, a guide `h` with `SafeLegal R C μ h`, and a version space `G ∋ μ` with mixture
`η`. Write `p` for the `η`-probability that a scan stops and `b = μ(stop)`.

* `update_mem`, `two_mul_card_update_lt`: after a violation, the target survives (by safety) and
  strictly fewer than half of the candidates remain.
* `stop_sq_le`: `b² ≤ 2RCp` (weighted Cauchy–Schwarz on the prefix-free first-violation
  frontier); hence `p ≤ p₀ = δ²/(32RC)` gives `b ≤ δ/4`.
* `stage_none_le`: all `T` scans of a stage pass with probability `(1-p)^T ≤ e^{-pT}`.
* `tv_produceA_le`: the production law: the accepted law is `μ` conditioned on the good leaves,
  a trial accepts with probability `(1-b)/(2R) ≥ 1/(4R)`, exhaustion has probability at most
  `e^{-J/(4R)}`, and the output is within `b + e^{-J/(4R)}` of `μ`.
* `tv_learnA_le`: with stage budget `s` and `|G| ≤ 2^s`, the output is within
  `s ε + δ/2` of `μ`, where `ε ≥ e^{-p₀T}` bounds a false pass at a heavy frontier.
* `frontier`: the learner of Appendix `app:frontier` solves every class of at most `M`
  distributions in the safe model with cap `2n(J₀T + J)` and error `3δ/4 ≤ δ`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Frontier

open Upper

variable {n : ℕ}

/-! ### Version-space updates -/

/-- `app:frontier`: the target survives an update at a violation `(v, h(v))`, by safety. -/
theorem update_mem {R C : ℝ} (hR : 0 < R) {μ : Str n → ℝ} {h : Guide} (hl : SafeLegal R C μ h)
    {G : Finset (Str n → ℝ)} (hμG : μ ∈ G) {va : List Bool × ℝ} (ha : va.2 = h va.1)
    (hv : va.1.length ≤ n) : μ ∈ update R G va := by
  refine Finset.mem_filter.mpr ⟨hμG, ?_⟩
  rw [ha, div_le_iff₀ hR, mul_comm]
  exact hl.2.1 _ hv

/-- `app:frontier`: strict halving; every retained candidate has mass strictly greater than twice
the mixture
mass, so fewer than half of the candidates remain. -/
theorem two_mul_card_update_lt {R : ℝ} (hR : 0 < R) {G : Finset (Str n → ℝ)}
    (hG : ∀ φ ∈ G, IsDist φ) (hne : G.Nonempty) {va : List Bool × ℝ}
    (hviol : 2 * R * mass (mix G) va.1 < va.2) : 2 * (update R G va).card < G.card := by
  have hc : (0 : ℝ) < G.card := by exact_mod_cast hne.card_pos
  have hη0 : 0 ≤ mass (mix G) va.1 := mass_nonneg (isDist_mix hne hG).1 _
  have ha : 0 < va.2 / R := by
    apply div_pos _ hR
    nlinarith
  have h1 : ((update R G va).card : ℝ) * (va.2 / R) ≤ ∑ φ ∈ update R G va, mass φ va.1 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun φ hφ => (Finset.mem_filter.mp hφ).2
  have h2 : ∑ φ ∈ update R G va, mass φ va.1 ≤ ∑ φ ∈ G, mass φ va.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun φ hφ _ => mass_nonneg (hG φ hφ).1 _
  have h3 : ∑ φ ∈ G, mass φ va.1 = G.card * mass (mix G) va.1 := by
    rw [mass_mix]; field_simp
  have h4 : mass (mix G) va.1 < va.2 / R / 2 := by
    rw [div_div, lt_div_iff₀ (by positivity)]; linarith
  have h5 : ((update R G va).card : ℝ) * (va.2 / R) < G.card * (va.2 / R / 2) := by
    calc ((update R G va).card : ℝ) * (va.2 / R) ≤ G.card * mass (mix G) va.1 := by linarith
      _ < G.card * (va.2 / R / 2) := mul_lt_mul_of_pos_left h4 hc
  have h6 : (2 * (update R G va).card : ℝ) < G.card := by
    have : ((update R G va).card : ℝ) * (va.2 / R) * 2 < G.card * (va.2 / R) := by
      have := h5; field_simp at this ⊢; linarith
    nlinarith
  exact_mod_cast h6

/-! ### Frontier mass -/

open Classical in
/-- `b = μ(stop)`. -/
noncomputable def stopMass (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) (ν : Str n → ℝ) : ℝ :=
  ∑ x, if Stops h R (mix G) x then ν x else 0

/-- `app:frontier`: weighted Cauchy–Schwarz on the first-violation frontier, `b² ≤ 2RCp`. -/
theorem stop_sq_le {R C : ℝ} {μ : Str n → ℝ} {h : Guide} (hl : SafeLegal R C μ h)
    (hR : 1 ≤ 2 * R) {G : Finset (Str n → ℝ)} (hG : ∀ φ ∈ G, IsDist φ) (hne : G.Nonempty) :
    stopMass h R G μ ^ 2 ≤ 2 * R * C * stopMass h R G (mix G) := by
  have hη := isDist_mix hne hG
  have hA := isCut_frontierSet (h := h) (R := R) (η := mix G)
  have e1 := sum_mass_frontierSet (h := h) (R := R) (η := mix G) μ
  have e2 := sum_mass_frontierSet (h := h) (R := R) (η := mix G) (mix G)
  unfold stopMass
  rw [← e1, ← e2]
  have hcs := sq_sum_le_frontier (μ := μ) (frontierSet h R (mix G)) hl.1.nonneg
    fun u hu h0 => by
      by_contra hm
      exact hl.2.2.1 u (hA.1 u hu) hm h0
  have hcap : cutSum μ h (frontierSet h R (mix G)) ≤ C := hl.2.2.2 _ hA
  have hcut0 : 0 ≤ cutSum μ h (frontierSet h R (mix G)) :=
    Finset.sum_nonneg fun u _ => div_nonneg (sq_nonneg _) (hl.1.nonneg u)
  have hh : ∑ u ∈ frontierSet h R (mix G), h u ≤
      2 * R * ∑ u ∈ frontierSet h R (mix G), mass (mix G) u := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => h_le_frontierSet hl.1.root ?_ hR hu
    rw [mass_nil, hη.2]
  have hh0 : 0 ≤ ∑ u ∈ frontierSet h R (mix G), h u := Finset.sum_nonneg fun u _ => hl.1.nonneg u
  calc (∑ u ∈ frontierSet h R (mix G), mass μ u) ^ 2
      ≤ cutSum μ h (frontierSet h R (mix G)) * ∑ u ∈ frontierSet h R (mix G), h u := hcs
    _ ≤ C * (2 * R * ∑ u ∈ frontierSet h R (mix G), mass (mix G) u) :=
        mul_le_mul hcap hh hh0 (hcut0.trans hcap)
    _ = 2 * R * C * ∑ u ∈ frontierSet h R (mix G), mass (mix G) u := by ring

theorem stopMass_nonneg (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) {ν : Str n → ℝ}
    (hν : ∀ x, 0 ≤ ν x) : 0 ≤ stopMass h R G ν :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hν x]

open Classical in
theorem stopMass_add_good (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) {ν : Str n → ℝ}
    (hν : IsDist ν) :
    stopMass h R G ν + ∑ x, (if Stops h R (mix G) x then 0 else ν x) = 1 := by
  unfold stopMass
  rw [← Finset.sum_add_distrib, ← hν.2]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- `app:frontier`: a light frontier, `p ≤ p₀ = δ²/(32RC)`, has `b ≤ δ/4`. -/
theorem stopMass_le_of_light {R C δ : ℝ} {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hl : SafeLegal R C μ h) (hR : 1 ≤ R) (hC : 0 < C) (hδ : 0 < δ) {G : Finset (Str n → ℝ)}
    (hG : ∀ φ ∈ G, IsDist φ)
    (hne : G.Nonempty) (hp : stopMass h R G (mix G) ≤ p0 δ R C) :
    stopMass h R G μ ≤ δ / 4 := by
  have h1 := stop_sq_le hl (by linarith) hG hne
  have h2 : 2 * R * C * stopMass h R G (mix G) ≤ 2 * R * C * p0 δ R C :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  have h3 : 2 * R * C * p0 δ R C = (δ / 4) ^ 2 := by
    unfold p0; field_simp; ring
  have hb0 : 0 ≤ stopMass h R G μ := stopMass_nonneg h R G hμ.1
  nlinarith [sq_nonneg (stopMass h R G μ - δ / 4), sq_nonneg (stopMass h R G μ + δ / 4)]

/-! ### Production -/

open Classical in
/-- `w(y)`: the probability that a production trial outputs `y`, `μ(y)/(2R)` on good leaves. -/
noncomputable def wgt (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) (μ : Str n → ℝ)
    (y : Str n) : ℝ :=
  if Stops h R (mix G) y then 0 else μ y / (2 * R)

theorem wgt_nonneg {μ : Str n → ℝ} (hμ : IsDist μ) {R : ℝ} (hR : 0 < R) (h : Guide)
    (G : Finset (Str n → ℝ)) (y : Str n) : 0 ≤ wgt h R G μ y := by
  unfold wgt; split_ifs
  · exact le_rfl
  · exact div_nonneg (hμ.1 y) (by positivity)

/-- `app:frontier`: a production trial outputs `y` with probability `w(y)`: a passing scan certifies
`μ(y) = h(y) ≤ 2Rη(y)`, so acceptance with probability `h(y)/(2Rη(y))` gives `μ(y)/(2R)`. -/
theorem run_trialA_some_eq (hn : 1 ≤ n) {R C : ℝ} (hR : 0 < R) {μ : Str n → ℝ} (hμ : IsDist μ)
    {h : Guide} (hl : SafeLegal R C μ h) {G : Finset (Str n → ℝ)} (hG : ∀ φ ∈ G, IsDist φ)
    (hne : G.Nonempty) (y : Str n) :
    (trialA R G).run h (some y) = ENNReal.ofReal (wgt h R G μ y) := by
  have hη := isDist_mix hne hG
  rw [run_trialA_some]
  rcases hs : scanFn h R (mix G) y with va | a
  · simp [wgt, scanFn_inl_stops hs]
  · have hst := scanFn_inr_not_stops hs
    simp only [Sum.elim_inr, wgt, hst, ↓reduceIte, toPMF_apply hη]
    rcases scanPathFn_inr h R (mix G) (List.ofFn y) [] 1 a hs with ⟨h0, -⟩ | ⟨-, ha, hle⟩
    · exfalso
      have := congrArg List.length h0
      simp only [List.length_ofFn, List.length_nil] at this
      omega
    · simp only [List.nil_append] at ha hle
      rw [hl.1.leaf, mass_ofFn] at hle
      rw [hl.1.leaf] at ha
      subst ha
      rw [← ENNReal.ofReal_mul (hη.1 y)]
      congr 1
      rcases (hη.1 y).eq_or_lt with h0 | hpos
      · have : μ y = 0 := le_antisymm (by rw [← h0, mul_zero] at hle; exact hle) (hμ.1 y)
        rw [← h0, this]; simp
      · rw [clip_eq (div_nonneg (hμ.1 y) (by positivity))
          (by rw [div_le_one (by positivity)]; exact hle)]
        field_simp

theorem option_pmf_sum {α : Type} [Fintype α] (P : PMF (Option α)) :
    P none + ∑ y, P (some y) = 1 := by
  have := P.tsum_coe
  rwa [tsum_fintype, Fintype.sum_option] at this

theorem run_produceA_succ (h : Guide) (R : ℝ) (G : Finset (Str n → ℝ)) (j : ℕ) :
    (produceA R G (j + 1)).run h =
      ((trialA R G).run h).bind fun o => Option.elim o ((produceA R G j).run h) PMF.pure := by
  simp only [produceA, run_bindA]
  congr 1; ext1 o
  rcases o with _ | x <;> rfl

/-- `app:frontier`: the production law, `L_{j+1} = (1 - α) L_j + w` with `α = ∑ w`. -/
theorem lawR_produceA_succ (hn : 1 ≤ n) {R C : ℝ} (hR : 0 < R) {μ : Str n → ℝ}
    (hμ : IsDist μ) {h : Guide} (hl : SafeLegal R C μ h) {G : Finset (Str n → ℝ)}
    (hG : ∀ φ ∈ G, IsDist φ) (hne : G.Nonempty) (j : ℕ) (y : Str n) :
    lawR ((produceA R G (j + 1)).run h) y =
      (1 - ∑ x, wgt h R G μ x) * lawR ((produceA R G j).run h) y + wgt h R G μ y := by
  classical
  set P := (trialA R G).run h
  have hP : ∀ x, P (some x) = ENNReal.ofReal (wgt h R G μ x) :=
    run_trialA_some_eq hn hR hμ hl hG hne
  have hsum := option_pmf_sum P
  have hnone : (P none).toReal = 1 - ∑ x, wgt h R G μ x := by
    have := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _)
      (ENNReal.sum_ne_top.mpr fun x _ => PMF.apply_ne_top _ _), ENNReal.toReal_sum
      (fun x _ => PMF.apply_ne_top _ _), ENNReal.toReal_one] at this
    simp_rw [hP, ENNReal.toReal_ofReal (wgt_nonneg hμ hR h G _)] at this
    linarith
  rw [run_produceA_succ, lawR, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  simp only [Option.elim]
  rw [Finset.sum_eq_single y (fun x _ hxy => by simp [PMF.pure_apply, Ne.symm hxy])
    (by simp), PMF.pure_apply, ite_eq_left rfl, mul_one, ENNReal.toReal_add
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)) (PMF.apply_ne_top _ _),
    ENNReal.toReal_mul, hnone, hP, ENNReal.toReal_ofReal (wgt_nonneg hμ hR h G y)]
  rfl

/-- `app:frontier`: the total acceptance probability `α = (1 - b)/(2R)`. -/
theorem sum_wgt {R : ℝ} {μ : Str n → ℝ} (hμ : IsDist μ) (h : Guide) (G : Finset (Str n → ℝ)) :
    ∑ x, wgt h R G μ x = (1 - stopMass h R G μ) / (2 * R) := by
  classical
  have := stopMass_add_good h R G hμ
  rw [show 1 - stopMass h R G μ = ∑ x, (if Stops h R (mix G) x then 0 else μ x) by linarith,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wgt; split_ifs <;> simp

/-- `app:frontier`: the production law approaches `ν = w/α` (`μ` conditioned on the good leaves)
geometrically:
`TV(L_j, ν) ≤ (1 - α)^j`. -/
theorem tv_produceA_nu (hn : 1 ≤ n) {R C : ℝ} (hR : 0 < R) {μ : Str n → ℝ}
    (hμ : IsDist μ) {h : Guide} (hl : SafeLegal R C μ h) {G : Finset (Str n → ℝ)}
    (hG : ∀ φ ∈ G, IsDist φ) (hne : G.Nonempty) (hα : 0 < ∑ x, wgt h R G μ x)
    (hα1 : ∑ x, wgt h R G μ x ≤ 1) :
    ∀ j, tv (lawR ((produceA R G j).run h)) (fun y => wgt h R G μ y / ∑ x, wgt h R G μ x) ≤
      (1 - ∑ x, wgt h R G μ x) ^ j := by
  set α := ∑ x, wgt h R G μ x with hαdef
  set ν : Str n → ℝ := fun y => wgt h R G μ y / α with hν
  have hνd : IsDist ν := by
    refine ⟨fun y => div_nonneg (wgt_nonneg hμ hR h G y) hα.le, ?_⟩
    rw [hν, ← Finset.sum_div, ← hαdef, div_self hα.ne']
  intro j
  induction j with
  | zero => simpa using tv_le_one (lawR_isDist _) hνd
  | succ j ih =>
      have hL : lawR ((produceA R G (j + 1)).run h) =
          fun y => (1 - α) * lawR ((produceA R G j).run h) y + α * ν y := by
        ext y
        rw [lawR_produceA_succ hn hR hμ hl hG hne j y, ← hαdef, hν]
        simp only
        rw [mul_div_cancel₀ _ hα.ne']
      have key := tv_mix (lawR ((produceA R G j).run h)) ν α 1
      have hν' : (fun x => (1 - 1) * lawR ((produceA R G j).run h) x + 1 * ν x) = ν := by
        ext x; ring
      rw [hν'] at key
      rw [hL, key, abs_of_nonpos (by linarith), pow_succ]
      calc -(α - 1) * tv (lawR ((produceA R G j).run h)) ν
          = (1 - α) * tv (lawR ((produceA R G j).run h)) ν := by ring
        _ ≤ (1 - α) * (1 - α) ^ j := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - α) ^ j * (1 - α) := by ring

/-- `app:frontier`: `TV(ν, μ) = b`; conditioning on the good leaves moves the law by the stopped
mass. -/
theorem tv_nu_mu {R : ℝ} (hR : 0 < R) {μ : Str n → ℝ} (hμ : IsDist μ) (h : Guide)
    (G : Finset (Str n → ℝ)) (hb : stopMass h R G μ < 1) :
    tv (fun y => wgt h R G μ y / ∑ x, wgt h R G μ x) μ = stopMass h R G μ := by
  classical
  set b := stopMass h R G μ with hbdef
  have hg : 0 < 1 - b := by linarith
  have hsum := stopMass_add_good h R G hμ
  rw [sum_wgt hμ h G, ← hbdef]
  unfold tv
  have e : ∀ y, |wgt h R G μ y / ((1 - b) / (2 * R)) - μ y| =
      (if Stops h R (mix G) y then μ y else 0) +
        (if Stops h R (mix G) y then 0 else μ y) * (1 / (1 - b) - 1) := by
    intro y
    unfold wgt
    by_cases hy : Stops h R (mix G) y
    · simp [hy, abs_of_nonneg (hμ.1 y)]
    · simp only [hy, ↓reduceIte, zero_add]
      have : μ y / (2 * R) / ((1 - b) / (2 * R)) - μ y = μ y * (1 / (1 - b) - 1) := by
        field_simp
      rw [this, abs_of_nonneg (mul_nonneg (hμ.1 y) ?_)]
      rw [sub_nonneg, le_div_iff₀ hg]
      linarith [stopMass_nonneg h R G hμ.1]
  beta_reduce
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hgood : ∑ x, (if Stops h R (mix G) x then 0 else μ x) = 1 - b := by linarith
  rw [hgood]
  change (b + (1 - b) * (1 / (1 - b) - 1)) / 2 = b
  field_simp
  ring

/-- `app:frontier`: production at a light frontier; if `b ≤ δ/4` and `e^{-J/(4R)} ≤ δ/4`, the
production law is
within `δ/2` of `μ`. -/
theorem tv_produceA_le (hn : 1 ≤ n) {R C δ : ℝ} (hR : 0 < R) {μ : Str n → ℝ} (hμ : IsDist μ)
    {h : Guide} (hl : SafeLegal R C μ h) {G : Finset (Str n → ℝ)} (hG : ∀ φ ∈ G, IsDist φ)
    (hne : G.Nonempty) (hδ1 : δ < 1) (hb : stopMass h R G μ ≤ δ / 4) {J : ℕ}
    (hJ : Real.exp (-(J / (4 * R))) ≤ δ / 4) :
    tv (lawR ((produceA R G J).run h)) μ ≤ δ / 2 := by
  set b := stopMass h R G μ
  have hb0 : 0 ≤ b := stopMass_nonneg h R G hμ.1
  have hb1 : b < 1 := by linarith
  set α := ∑ x, wgt h R G μ x with hαdef
  have hαe : α = (1 - b) / (2 * R) := sum_wgt hμ h G
  have hαlow : 1 / (4 * R) ≤ α := by
    rw [hαe, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hαlow
  have hα1 : α ≤ 1 := by
    rw [hαe, div_le_one (by positivity)]
    have : 1 ≤ R := by
      have := hl.2.1 [] (by simp)
      rw [hl.1.root, mass_nil, hμ.2, mul_one] at this
      exact this
    linarith
  have h1 := tv_produceA_nu hn hR hμ hl hG hne hαpos hα1 J
  have h2 := tv_nu_mu hR hμ h G hb1
  have h3 : (1 - α) ^ J ≤ Real.exp (-(J / (4 * R))) := by
    calc (1 - α) ^ J ≤ Real.exp (-α) ^ J :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg α) J
      _ = Real.exp (-(α * J)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(J / (4 * R))) := by
          apply Real.exp_le_exp.mpr
          have : (J : ℝ) / (4 * R) = 1 / (4 * R) * J := by ring
          rw [this]
          have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
          nlinarith
  have := tv_triangle (lawR ((produceA R G J).run h))
    (fun y => wgt h R G μ y / ∑ x, wgt h R G μ x) μ
  linarith

/-! ### Stages -/

open Classical in
theorem passE_toReal {h : Guide} {R : ℝ} {G : Finset (Str n → ℝ)} (hG : ∀ φ ∈ G, IsDist φ)
    (hne : G.Nonempty) : (passE h R G).toReal = 1 - stopMass h R G (mix G) := by
  have hη := isDist_mix hne hG
  have hsum := stopMass_add_good h R G hη
  rw [passE, tsum_fintype, ENNReal.toReal_sum fun x _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (by split_ifs <;> simp)]
  have : ∀ x, (toPMF (mix G) x * (if Stops h R (mix G) x then 0 else 1)).toReal =
      if Stops h R (mix G) x then 0 else mix G x := by
    intro x
    rw [toPMF_apply hη]
    split_ifs <;> simp [ENNReal.toReal_ofReal (hη.1 x)]
  simp_rw [this]
  linarith

open Classical in
/-- `app:frontier`: a false pass; all `T` scans of a stage pass with probability
`(1 - p)^T ≤ e^{-pT}`. -/
theorem stage_none_le {h : Guide} {R : ℝ} {G : Finset (Str n → ℝ)} (hG : ∀ φ ∈ G, IsDist φ)
    (hne : G.Nonempty) (T : ℕ) :
    ((stageA R G T).run h none).toReal ≤ Real.exp (-(stopMass h R G (mix G) * T)) := by
  have hη := isDist_mix hne hG
  set p := stopMass h R G (mix G)
  have hp1 : p ≤ 1 := by
    have := stopMass_add_good h R G hη
    have : 0 ≤ ∑ x, (if Stops h R (mix G) x then 0 else mix G x) :=
      Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hη.1 x]
    linarith
  rw [run_stageA_none, ENNReal.toReal_pow, passE_toReal hG hne]
  calc (1 - p) ^ T ≤ Real.exp (-p) ^ T := pow_le_pow_left₀ (by linarith)
        (Real.one_sub_le_exp_neg p) T
    _ = Real.exp (-(p * T)) := by rw [← Real.exp_nat_mul]; ring_nf

/-! ### The learner -/

theorem eq_singleton_of_card_le_one {G : Finset (Str n → ℝ)} {μ : Str n → ℝ} (hμG : μ ∈ G)
    (hc : G.card ≤ 1) : G = {μ} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨hμG, fun φ hφ => Finset.card_le_one.mp hc φ hφ μ hμG⟩

/-- On `{0,1}^0` there is only one distribution. -/
theorem dist_unique_zero {μ ν : Str 0 → ℝ} (hμ : IsDist μ) (hν : IsDist ν) : μ = ν := by
  ext x
  have h1 := hμ.2
  have h2 := hν.2
  rw [Fintype.sum_unique] at h1 h2
  have e1 : μ x = 1 := by rw [← h1]; congr 1; exact Subsingleton.elim _ _
  have e2 : ν x = 1 := by rw [← h2]; congr 1; exact Subsingleton.elim _ _
  rw [e1, e2]

theorem card_le_one_of_n_zero (hn : n = 0) {G : Finset (Str n → ℝ)}
    (hG : ∀ φ ∈ G, IsDist φ) : G.card ≤ 1 := by
  subst hn
  exact Finset.card_le_one.mpr fun a ha b hb => dist_unique_zero (hG a ha) (hG b hb)

/-- The legal factor satisfies `R ≥ 1` (root safety). -/
theorem one_le_R {R C : ℝ} {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hl : SafeLegal R C μ h) : 1 ≤ R := by
  have := hl.2.1 [] (by simp)
  rwa [hl.1.root, mass_nil, hμ.2, mul_one] at this

/-- The legal capacity satisfies `C ≥ 1` (the leaf cut has value one). -/
theorem one_le_C {R C : ℝ} {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hl : SafeLegal R C μ h) : 1 ≤ C := by
  have := hl.2.2.2 (words n) (isCut_words le_rfl)
  have e : cutSum μ h (words n) = 1 := by
    unfold cutSum
    have e2 : ∀ u ∈ words n, mass μ u ^ 2 / h u = mass μ u := by
      intro u hu
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
      rw [hl.1.leaf, ← mass_ofFn μ y, sq_div_self_eq]
    rw [Finset.sum_congr rfl e2, sum_mass_words μ le_rfl, hμ.2]
  linarith

/-- `app:frontier`: the error of the learner; with stage budget `s` and `|G| ≤ 2^s`, the output is
within
`s ε + δ/2` of `μ`, where `ε ≥ e^{-p₀T}` bounds a false pass at a frontier with `p > p₀`
(union bound over the stages), and `δ/2` bounds the production error at a light frontier. -/
theorem tv_learnA_le {R C δ ε : ℝ} {T J : ℕ} (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 ≤ ε) (hT : Real.exp (-(p0 δ R C * T)) ≤ ε) (hJ : Real.exp (-(J / (4 * R))) ≤ δ / 4)
    {F : Finset (Str n → ℝ)} (hF : ∀ φ ∈ F, IsDist φ) {μ : Str n → ℝ} (hμF : μ ∈ F) {h : Guide}
    (hl : SafeLegal R C μ h) :
    ∀ (s : ℕ) (G : Finset (Str n → ℝ)), μ ∈ G → G ⊆ F → G.card ≤ 2 ^ s →
      tv (lawR ((learnA R T J s G).run h)) μ ≤ s * ε + δ / 2 := by
  have hμ := hF μ hμF
  have hR := one_le_R hμ hl
  have hR0 : 0 < R := by linarith
  have exact_case : ∀ (s : ℕ) (G : Finset (Str n → ℝ)), μ ∈ G → G.card ≤ 1 →
      tv (lawR ((sampleSet G).run h)) μ ≤ s * ε + δ / 2 := by
    intro s G hμG hc
    rw [run_sampleSet_of_eq h (eq_singleton_of_card_le_one hμG hc), lawR_toPMF hμ, tv_self]
    positivity
  intro s
  induction s with
  | zero =>
      intro G hμG _ hcard
      have hc1 : G.card ≤ 1 := by simpa using hcard
      simp only [learnA, hc1, ↓reduceIte]
      exact exact_case 0 G hμG hc1
  | succ s ih =>
      intro G hμG hGF hcard
      by_cases hc1 : G.card ≤ 1
      · simp only [learnA, hc1, ↓reduceIte]
        exact exact_case (s + 1) G hμG hc1
      have hG : ∀ φ ∈ G, IsDist φ := fun φ hφ => hF φ (hGF hφ)
      have hn : 1 ≤ n := by
        by_contra hn0
        exact hc1 (card_le_one_of_n_zero (by omega) hG)
      have hne : G.Nonempty := ⟨μ, hμG⟩
      simp only [learnA, hc1, ↓reduceIte, run_bindA]
      set p := stopMass h R G (mix G)
      set K : ℝ := s * ε + δ / 2 with hK
      have hK0 : 0 ≤ K := by positivity
      have hsε : 0 ≤ (s : ℝ) * ε := by positivity
      set c : ℝ := if p ≤ p0 δ R C then 0 else 1 with hc
      have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> norm_num
      have key := tv_bind_le_of_le ((stageA R G T).run h)
        (fun o => (Option.elim o (produceA R G J) fun va => learnA R T J s (update R G va)).run h)
        hμ (fun o => K + if o = none then c else 0) (by
          intro o ho
          rcases o with _ | va
          · simp only [Option.elim, ↓reduceIte]
            by_cases hp : p ≤ p0 δ R C
            · have hb := stopMass_le_of_light hμ hl hR hC hδ0 hG hne hp
              have := tv_produceA_le hn hR0 hμ hl hG hne hδ1 hb hJ
              rw [hc, ite_eq_left hp]
              linarith
            · rw [hc, ite_eq_right hp]
              have := tv_le_one (lawR_isDist ((produceA R G J).run h)) hμ
              linarith
          · obtain ⟨ha, hviol, hlen⟩ := stageA_support h R G T va ho
            simp only [Option.elim, reduceCtorEq, ↓reduceIte, add_zero]
            have hμ' := update_mem hR0 hl hμG ha hlen
            have hlt := two_mul_card_update_lt hR0 hG hne hviol
            have hsub : update R G va ⊆ F := (Finset.filter_subset _ _).trans hGF
            have hcard' : (update R G va).card ≤ 2 ^ s := by
              rw [pow_succ] at hcard; omega
            exact ih _ hμ' hsub hcard')
      have hsum : ∑' o, (stageA R G T).run h o *
          ENNReal.ofReal (K + if o = none then c else 0) =
          ENNReal.ofReal K + (stageA R G T).run h none * ENNReal.ofReal c := by
        have e : ∀ o : Option (List Bool × ℝ), ENNReal.ofReal (K + if o = none then c else 0) =
            ENNReal.ofReal K + (if o = none then ENNReal.ofReal c else 0) := by
          intro o
          rw [ENNReal.ofReal_add hK0 (by split_ifs <;> simp [hc0])]
          split_ifs <;> simp
        simp_rw [e, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          tsum_eq_single none (fun o ho => by simp [ho])]
        simp
      rw [hsum] at key
      by_cases hp : p ≤ p0 δ R C
      · rw [hc, ite_eq_left hp, ENNReal.ofReal_zero, mul_zero, add_zero,
          ENNReal.ofReal_le_ofReal_iff hK0] at key
        push_cast
        linarith
      · rw [hc, ite_eq_right hp, ENNReal.ofReal_one, mul_one] at key
        have hpass := stage_none_le (h := h) (R := R) hG hne T
        have hp' : p0 δ R C * T ≤ p * T :=
          mul_le_mul_of_nonneg_right (le_of_lt (not_le.mp hp)) (Nat.cast_nonneg T)
        have hexp : Real.exp (-(p * T)) ≤ Real.exp (-(p0 δ R C * T)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hnone : (stageA R G T).run h none ≤ ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ none)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        have := key.trans (add_le_add le_rfl hnone)
        rw [← ENNReal.ofReal_add hK0 hε, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
        push_cast
        linarith

theorem le_two_pow_ceil_logb {M : ℕ} (hM : 1 ≤ M) : M ≤ 2 ^ ⌈Real.logb 2 M⌉₊ := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (M : ℝ) = (2 : ℝ) ^ Real.logb 2 M := (Real.rpow_logb (by norm_num) (by norm_num)
    hMpos).symm
  have h2 : (2 : ℝ) ^ Real.logb 2 M ≤ (2 : ℝ) ^ (⌈Real.logb 2 M⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h2
  have h3 : (M : ℝ) ≤ (2 : ℝ) ^ ⌈Real.logb 2 M⌉₊ := by
    calc (M : ℝ) = (2 : ℝ) ^ Real.logb 2 M := h1
      _ ≤ _ := h2
  exact_mod_cast h3

/-! ### The number of stages -/

theorem bind_congr_support {α β : Type} (p : PMF α) {f g : α → PMF β}
    (hfg : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [hfg a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

theorem learnA_of_card_le_one (R : ℝ) (T J : ℕ) (s : ℕ) {G : Finset (Str n → ℝ)}
    (hc : G.card ≤ 1) : learnA R T J s G = sampleSet G := by
  cases s <;> simp [learnA, hc]

/-- `app:frontier` (number of stages): the stage budget beyond `s` is never used when `|G| ≤ 2^s`:
by strict halving and target
survival, a version space of size at most `2^s` needs at most `s` stages (violation stages and
the final frozen stage together). With `|F| ≤ M ≤ 2^{⌈log₂ M⌉}`, the learner with the paper's
budget `J₀ = 1 + ⌈log₂ M⌉` has the same output law as with budget `⌈log₂ M⌉ = J₀ - 1`. -/
theorem run_learnA_budget {R C : ℝ} {T J : ℕ} {F : Finset (Str n → ℝ)}
    (hF : ∀ φ ∈ F, IsDist φ) {μ : Str n → ℝ} (hμF : μ ∈ F) {h : Guide}
    (hl : SafeLegal R C μ h) :
    ∀ (s : ℕ) (G : Finset (Str n → ℝ)), μ ∈ G → G ⊆ F → G.card ≤ 2 ^ s →
      ∀ s', s ≤ s' → (learnA R T J s' G).run h = (learnA R T J s G).run h := by
  have hR0 : 0 < R := by linarith [one_le_R (hF μ hμF) hl]
  intro s
  induction s with
  | zero =>
      intro G _ _ hcard s' _
      have hc1 : G.card ≤ 1 := by simpa using hcard
      rw [learnA_of_card_le_one R T J s' hc1, learnA_of_card_le_one R T J 0 hc1]
  | succ s ih =>
      intro G hμG hGF hcard s' hss'
      by_cases hc1 : G.card ≤ 1
      · rw [learnA_of_card_le_one R T J s' hc1, learnA_of_card_le_one R T J (s + 1) hc1]
      obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by omega⟩
      have hG : ∀ φ ∈ G, IsDist φ := fun φ hφ => hF φ (hGF hφ)
      have hne : G.Nonempty := ⟨μ, hμG⟩
      simp only [learnA, hc1, ↓reduceIte, run_bindA]
      refine bind_congr_support _ fun o ho => ?_
      rcases o with _ | va
      · rfl
      · obtain ⟨ha, hviol, hlen⟩ := stageA_support h R G T va ho
        have hlt := two_mul_card_update_lt hR0 hG hne hviol
        have hcard' : (update R G va).card ≤ 2 ^ s := by
          rw [pow_succ] at hcard; omega
        exact ih _ (update_mem hR0 hl hμG ha hlen) ((Finset.filter_subset _ _).trans hGF)
          hcard' s'' (by omega)

/-- `app:frontier` (number of stages): with the budget `J₀`, at most `⌈log₂ M⌉ = J₀ - 1` stages are
ever run, so the error
bound of `frontier_tv` improves to `(J₀ - 1) δ/(4J₀) + δ/2`. -/
theorem frontier_stages {M : ℕ} (hM : 1 ≤ M) {δ R C : ℝ} (F : Finset (Str n → ℝ))
    (hFM : F.card ≤ M) (hF : ∀ μ ∈ F, IsDist μ) {μ : Str n → ℝ} (hμF : μ ∈ F) {h : Guide}
    (hl : SafeLegal R C μ h) :
    (frontierAlg M δ R C F).run h =
      (learnA R (Tsc M δ R C) (Jpr δ R) ⌈Real.logb 2 M⌉₊ F).run h := by
  have hcard : F.card ≤ 2 ^ ⌈Real.logb 2 M⌉₊ := hFM.trans (le_two_pow_ceil_logb hM)
  exact run_learnA_budget hF hμF hl _ F hμF subset_rfl hcard (J0 M) (by unfold J0; omega)

/-! ### The main statement -/

theorem exp_neg_p0_T_le {M : ℕ} {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 < C) :
    Real.exp (-(p0 δ R C * Tsc M δ R C)) ≤ δ / (4 * J0 M) := by
  have hp0 : 0 < p0 δ R C := by unfold p0; positivity
  have hJ0 : (0 : ℝ) < J0 M := by unfold J0; positivity
  have hT : (p0 δ R C)⁻¹ * Real.log (4 * J0 M / δ) ≤ Tsc M δ R C := Nat.le_ceil _
  have h1 : Real.log (4 * J0 M / δ) ≤ p0 δ R C * Tsc M δ R C := by
    have := mul_le_mul_of_nonneg_left hT hp0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul] at this
  calc Real.exp (-(p0 δ R C * Tsc M δ R C)) ≤ Real.exp (-Real.log (4 * J0 M / δ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = δ / (4 * J0 M) := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

theorem exp_neg_J_le {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    Real.exp (-(Jpr δ R / (4 * R))) ≤ δ / 4 := by
  have hJ : 4 * R * Real.log (4 / δ) ≤ Jpr δ R := Nat.le_ceil _
  have h1 : Real.log (4 / δ) ≤ Jpr δ R / (4 * R) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc Real.exp (-(Jpr δ R / (4 * R))) ≤ Real.exp (-Real.log (4 / δ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = δ / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

/-- `app:frontier`: for `0 < δ < 1` and `M ≥ 2`, the safe frontier learner, with
`J₀ = 1 + ⌈log₂ M⌉`, `p₀ = δ²/(32RC)`, `T = ⌈p₀⁻¹ log(4J₀/δ)⌉` and `J = ⌈4R log(4/δ)⌉`, has cap
`2n(J₀T + J)` and output error at most `3δ/4` against every guide satisfying `eq:oracle` and
`eq:capacity-model` (`SafeLegal R C`) for every target in a class of at most `M` distributions. -/
theorem frontier_tv {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {R C : ℝ}
    (F : Finset (Str n → ℝ)) (hFM : F.card ≤ M) (hF : ∀ μ ∈ F, IsDist μ) {μ : Str n → ℝ}
    (hμF : μ ∈ F) {h : Guide} (hl : SafeLegal R C μ h) :
    (frontierAlg M δ R C F).Within h (frontierCap n M δ R C) ∧
      tv (lawR ((frontierAlg M δ R C F).run h)) μ ≤ 3 * δ / 4 := by
  refine ⟨within_frontierAlg h M δ R C F, ?_⟩
  have hμ := hF μ hμF
  have hR := one_le_R hμ hl
  have hC := one_le_C hμ hl
  have hJ0 : (0 : ℝ) < J0 M := by unfold J0; positivity
  have hcard : F.card ≤ 2 ^ J0 M := by
    calc F.card ≤ M := hFM
      _ ≤ 2 ^ ⌈Real.logb 2 M⌉₊ := le_two_pow_ceil_logb (by omega)
      _ ≤ 2 ^ J0 M := Nat.pow_le_pow_right (by norm_num) (by unfold J0; omega)
  have := tv_learnA_le (by linarith) hδ0 hδ1 (by positivity)
    (exp_neg_p0_T_le (M := M) hδ0 (by linarith) (by linarith))
    (exp_neg_J_le hδ0 (by linarith)) hF hμF hl (J0 M) F hμF subset_rfl hcard
  have e : (J0 M : ℝ) * (δ / (4 * J0 M)) + δ / 2 = 3 * δ / 4 := by field_simp; ring
  unfold frontierAlg
  linarith

/-- `app:frontier` (number of stages): since at most `⌈log₂ M⌉ = J₀ - 1` stages are run, the
union bound needs only `J₀ - 1` terms: the error is at most `⌈log₂ M⌉ δ/(4J₀) + δ/2 < 3δ/4`. -/
theorem frontier_tv_sharp {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {R C : ℝ}
    (F : Finset (Str n → ℝ)) (hFM : F.card ≤ M) (hF : ∀ μ ∈ F, IsDist μ) {μ : Str n → ℝ}
    (hμF : μ ∈ F) {h : Guide} (hl : SafeLegal R C μ h) :
    tv (lawR ((frontierAlg M δ R C F).run h)) μ ≤
      ⌈Real.logb 2 M⌉₊ * (δ / (4 * J0 M)) + δ / 2 := by
  have hμ := hF μ hμF
  have hR := one_le_R hμ hl
  have hC := one_le_C hμ hl
  have hJ0 : (0 : ℝ) < J0 M := by unfold J0; positivity
  rw [frontier_stages (by omega) F hFM hF hμF hl]
  exact tv_learnA_le (by linarith) hδ0 hδ1 (by positivity)
    (exp_neg_p0_T_le (M := M) hδ0 (by linarith) (by linarith))
    (exp_neg_J_le hδ0 (by linarith)) hF hμF hl _ F hμF subset_rfl
    (hFM.trans (le_two_pow_ceil_logb (by omega)))

/-- `app:frontier`: the safe frontier learner solves every class of at most `M`
distributions at error `δ` with cap `2n(J₀T + J)`. -/
theorem frontier {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {R C : ℝ}
    (F : Finset (Str n → ℝ)) (hFM : F.card ≤ M) (hF : ∀ μ ∈ F, IsDist μ) :
    Solves (SafeLegal R C) (F : Set (Str n → ℝ)) δ (frontierCap n M δ R C)
      (frontierAlg M δ R C F) := by
  intro μ hμF h hl
  obtain ⟨hw, htv⟩ := frontier_tv hM hδ0 hδ1 F hFM hF hμF hl
  exact ⟨hw, htv.trans (by linarith)⟩

end Frontier
end LearningGuided
