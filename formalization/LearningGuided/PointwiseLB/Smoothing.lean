import LearningGuided.PointwiseLB.Regimes

/-!
# Smoothing the hard class (proof of Corollary `cor:fixed-cert`, first paragraph)

Each target `μ` on `m` bits is replaced by its `7/8` mixture with `U_m`,
`μ̃ = (7/8) μ + (1/8) U_m`, and each guide by the same mixture with the exact uniform prefix
masses, `h̃(u) = (7/8) h(u) + (1/8) 2^{-|u|}`. Then

* `h̃` is still a pointwise factor-`9/4` guide for `μ̃` (`smooth_pwLegal`), `μ̃` has full
  support, and each query to `h̃` is simulated by one query to `h` (`smoothO_eval`);
* the root of a smoothed target predicts the hidden bit with probability at least
  `(7/8)(3/5) + 1/16 = 47/80` (`smooth_root`);
* error `1/16` then gives advantage `47/80 - 1/16 - 1/2 = 1/40`, i.e. a transcript distance at
  least `1/20 > 65/2048`, so the bound `q > 2^{-16}(ℓ-1)r²` survives smoothing
  (`parameter_smooth`), and so does the exponential-size bound (`expn_smooth`).
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

section Smooth

variable {m : ℕ}

/-- The smoothed target `(7/8) μ + (1/8) U_m`. -/
noncomputable def smoothT (μ : Str m → ℝ) : Str m → ℝ := fun x => 7 / 8 * μ x + 1 / 8 * unif m x

/-- The smoothed guide `(7/8) h(u) + (1/8) 2^{-|u|}` on `{0,1}^{≤ m}`. -/
noncomputable def smoothO (m : ℕ) (h : Guide) (u : List Bool) : ℝ :=
  if u.length ≤ m then 7 / 8 * h u + 1 / 8 * ((2 : ℝ) ^ u.length)⁻¹ else 0

/-- One smoothed query is one original query. -/
noncomputable def smoothSim (m : ℕ) (u : List Bool) : SimStep :=
  if u.length ≤ m then .ask u fun v => 7 / 8 * v + 1 / 8 * ((2 : ℝ) ^ u.length)⁻¹ else .const 0

theorem smoothO_eval (h : Guide) (u : List Bool) : smoothO m h u = (smoothSim m u).eval h := by
  unfold smoothO smoothSim; split_ifs <;> rfl

theorem mass_smoothT (μ : Str m → ℝ) {u : List Bool} (hu : u.length ≤ m) :
    mass (smoothT μ) u = 7 / 8 * mass μ u + 1 / 8 * ((2 : ℝ) ^ u.length)⁻¹ := by
  unfold smoothT
  rw [mass_linear, mass_unif hu]

theorem isDist_smoothT {μ : Str m → ℝ} (hμ : IsDist μ) : IsDist (smoothT μ) := by
  have := isDist_mix hμ (isDist_unif m) (a := 1 / 8) (by norm_num) (by norm_num)
  convert this using 2
  unfold smoothT; ring

/-- `cor:fixed-cert`, smoothing: the smoothed targets have full support. -/
theorem smoothT_pos {μ : Str m → ℝ} (hμ : IsDist μ) (x : Str m) : 0 < smoothT μ x := by
  unfold smoothT unif
  have := hμ.1 x
  positivity

/-- `cor:fixed-cert`, smoothing: the smoothed guide is a pointwise factor-`9/4` guide for the
smoothed target. -/
theorem smooth_pwLegal {μ : Str m → ℝ} (hμ : IsDist μ) {h : Guide}
    (hl : PwLegal (9 / 4) μ h) : PwLegal (9 / 4) (smoothT μ) (smoothO m h) := by
  obtain ⟨⟨hnn, hroot, hleaf, hlong⟩, hb⟩ := hl
  refine ⟨⟨fun u => ?_, ?_, fun x => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
  · unfold smoothO; split_ifs
    · have := hnn u; positivity
    · exact le_rfl
  · unfold smoothO; rw [ite_eq_left (by simp), hroot]; norm_num
  · unfold smoothO smoothT unif
    rw [ite_eq_left (by simp), hleaf, List.length_ofFn]
  · unfold smoothO; rw [ite_eq_right (by omega)]
  · rw [mass_smoothT μ hu]
    unfold smoothO
    rw [ite_eq_left hu]
    obtain ⟨h1, h2⟩ := hb u hu
    have hU : (0 : ℝ) ≤ ((2 : ℝ) ^ u.length)⁻¹ := by positivity
    have hm := mass_nonneg hμ.1 u
    constructor <;> nlinarith

/-- `cor:fixed-cert`, smoothing: the root of a smoothed target: `μ̃(X₁ = b) ≥ (7/8)(3/5) + 1/16 =
47/80` when `μ(X₁ = b) ≥ 3/5`. -/
theorem smooth_root {μ : Str m → ℝ} (hm : 1 ≤ m) {b : Bool} (hb : 3 / 5 ≤ mass μ [b]) :
    47 / 80 ≤ mass (smoothT μ) [b] := by
  rw [mass_smoothT μ (by simpa using hm)]
  norm_num at hb ⊢; linarith

end Smooth

namespace Prm

variable (P : Prm)

/-- The smoothed padded class on `n ≥ N` bits. -/
noncomputable def smoothClass (n : ℕ) (hNn : P.N ≤ n) : Finset (Str n → ℝ) :=
  P.instances.image fun θ => smoothT (padT hNn (P.target θ.2))

theorem mem_smoothClass {n : ℕ} {hNn : P.N ≤ n} {μ : Str n → ℝ} :
    μ ∈ P.smoothClass n hNn ↔ ∃ B T, P.Valid B T ∧ μ = smoothT (padT hNn (P.target T)) := by
  unfold smoothClass instances
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨B, T⟩, hv, rfl⟩; exact ⟨B, T, hv, rfl⟩
  · rintro ⟨B, T, hv, rfl⟩; exact ⟨⟨B, T⟩, hv, rfl⟩

theorem card_smoothClass_le (n : ℕ) (hNn : P.N ≤ n) : (P.smoothClass n hNn).card ≤ P.M0 :=
  Finset.card_image_le.trans ((Finset.card_le_univ _).trans P.card_inst.le)

/-- Every member of the smoothed class is a full-support distribution. -/
theorem smoothClass_fullSupport {n : ℕ} {hNn : P.N ≤ n} {μ : Str n → ℝ}
    (hμ : μ ∈ P.smoothClass n hNn) : IsDist μ ∧ ∀ x, 0 < μ x := by
  obtain ⟨B, T, hv, rfl⟩ := P.mem_smoothClass.mp hμ
  have hd := isDist_padT hNn (P.isDist_target hv)
  exact ⟨isDist_smoothT hd, smoothT_pos hd⟩

/-- The smoothed oracles are pointwise factor-`9/4` guides for the smoothed targets. -/
theorem smoothOracle_pwLegal {n : ℕ} (hNn : P.N ≤ n) {B : Bool} {T : P.Tables}
    (hv : P.Valid B T) :
    PwLegal (9 / 4) (smoothT (padT hNn (P.target T))) (smoothO n (padO P.N n (P.oracle T))) :=
  smooth_pwLegal (isDist_padT hNn (P.isDist_target hv)) (P.padOracle_pwLegal hNn hv)

/-- `cor:fixed-cert`, lower bound for the smoothed class: every algorithm with cap `q`
that is `1/16`-accurate against every smoothed target with its smoothed oracle satisfies
`q > 2^{-16}(ℓ-1)r²` (now via `1/20 > 65/2048`). -/
theorem parameter_smooth {n : ℕ} (hNn : P.N ≤ n) (A : Alg (Str n)) (q : ℕ)
    (hA : ∀ B T, P.Valid B T → A.Within (smoothO n (padO P.N n (P.oracle T))) q ∧
      tv (lawR (A.run (smoothO n (padO P.N n (P.oracle T))))) (smoothT (padT hNn (P.target T)))
        ≤ 1 / 16) :
    ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  have hn : 0 < n := lt_of_lt_of_le P.N_pos hNn
  set A' := simAlg (padSim P.N n) (simAlg (smoothSim n) A)
  have hS1 : ∀ T : P.Tables, ∀ u, smoothO n (padO P.N n (P.oracle T)) u =
      (smoothSim n u).eval (padO P.N n (P.oracle T)) := fun T u => smoothO_eval _ u
  have hS2 : ∀ T : P.Tables, ∀ u, padO P.N n (P.oracle T) u =
      (padSim P.N n u).eval (P.oracle T) := fun T u => padO_eval _ u
  have hadv := P.advantage_bound (bit0 hn) A' q (1 / 40) fun B T hv => by
    refine ⟨within_simAlg (hS2 T) _ q (within_simAlg (hS1 T) A q (hA B T hv).1), ?_⟩
    rw [run_simAlg (hS2 T), run_simAlg (hS1 T)]
    have hd := isDist_smoothT (isDist_padT hNn (P.isDist_target hv))
    have h1 := root_prob_ge hn hd (hA B T hv).2 B
    have h2 : 47 / 80 ≤ mass (smoothT (padT hNn (P.target T))) [B] := by
      apply smooth_root (by omega)
      rw [mass_padT_short hNn _ (by simp [N])]
      exact P.root_mass_ge hv
    linarith
  exact P.q_gt_of_adv hadv (by norm_num)

/-- `cor:fixed-cert`, the smoothed class in the pointwise model: at most `M₀` full-support
distributions on `n ≥ N` bits, and every algorithm solving it at error `1/16` with cap `q` has `q >
2^{-16}(ℓ-1)r²`. -/
theorem smooth_class_lower (n : ℕ) (hNn : P.N ≤ n) :
    (P.smoothClass n hNn).card ≤ P.M0 ∧ (∀ μ ∈ P.smoothClass n hNn, IsDist μ ∧ ∀ x, 0 < μ x) ∧
      ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑(P.smoothClass n hNn) (1 / 16) q A →
        ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 < q := by
  refine ⟨P.card_smoothClass_le n hNn, fun μ hμ => P.smoothClass_fullSupport hμ,
    fun q A hA => P.parameter_smooth hNn A q fun B T hv => ?_⟩
  exact hA _ (P.mem_smoothClass.mpr ⟨B, T, hv, rfl⟩) _ (P.smoothOracle_pwLegal hNn hv)

end Prm

/-- `cor:fixed-cert`, smoothing in the exponential-size regime: for every `m ≥ 4096` there is
a class of at most `⌊e^m⌋` full-support distributions on `m` bits on which every algorithm
solving the class at error `1/16` in the pointwise model with cap `q` has
`q ≥ 2^{-19} m^{3/2} / √(log(2m))`. -/
theorem expn_smooth (m : ℕ) (hm : 4096 ≤ m) :
    ∃ F : Finset (Str m → ℝ), F.Nonempty ∧ F.card ≤ ⌊Real.exp m⌋₊ ∧
      (∀ μ ∈ F, IsDist μ ∧ ∀ x, 0 < μ x) ∧
      ∀ (q : ℕ) (A : Alg (Str m)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
        (m : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt (Real.log (2 * m))) ≤ q := by
  have hnr : (4096 : ℝ) ≤ m := by exact_mod_cast hm
  set L := Real.log (2 * (m : ℝ)) with hLdef
  have hL1 : 1 ≤ L := Regimes.one_le_log_two_mul (by linarith)
  have hLpos : 0 < L := by linarith
  have h256 : 256 * L ≤ m := Regimes.log_bound_4096 hnr
  set Rb := Real.sqrt ((m : ℝ) / (4 * L)) with hRbdef
  have hRbsq : Rb ^ 2 = m / (4 * L) := Real.sq_sqrt (by positivity)
  have h8 : 8 ≤ Rb := by
    rw [hRbdef, show (8 : ℝ) = Real.sqrt (8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ (by positivity)]; linarith
  have hRb : Rb ≤ m / (16 * L) := by
    have hpos : 0 < (m : ℝ) / (16 * L) := by positivity
    rw [← Real.sqrt_sq hpos.le, hRbdef]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h64 : 64 * L ≤ m := by linarith
    have := mul_le_mul_of_nonneg_left h64 (by positivity : (0 : ℝ) ≤ 4 * m * L)
    nlinarith
  obtain ⟨P, hN, hℓn, hrRb, hRbr, hℓ1⟩ := Regimes.choose_params (by omega) h8 hRb
  obtain ⟨hcard, hfs, hlow⟩ := P.smooth_class_lower m hN
  have hne : (P.smoothClass m hN).Nonempty := by
    obtain ⟨T, hT⟩ := P.exists_valid true
    exact ⟨_, P.mem_smoothClass.mpr ⟨true, T, hT, rfl⟩⟩
  refine ⟨P.smoothClass m hN, hne, ?_, hfs, fun q A hA => ?_⟩
  · refine hcard.trans (Regimes.nat_le_floor_exp_of_log_le (Regimes.M0_pos P) ?_)
    have h1 := Regimes.log_M0_le P hℓn
    have hr2 : (P.r : ℝ) ^ 2 ≤ m / (4 * L) := by
      rw [← hRbsq]; exact pow_le_pow_left₀ (by positivity) hrRb 2
    have : 2 * (P.r : ℝ) ^ 2 * L ≤ m / 2 := by
      have := mul_le_mul_of_nonneg_right hr2 (by linarith : (0 : ℝ) ≤ 2 * L)
      have e : (m : ℝ) / (4 * L) * (2 * L) = m / 2 := by field_simp; ring
      nlinarith
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  · have hq := hlow q A hA
    have hr : (0 : ℝ) < P.r := by have := P.cast_r_ge; linarith
    have hstep : (m : ℝ) * P.r / 2 ^ 17 ≤ ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 := by
      have := mul_le_mul_of_nonneg_right hℓ1 (by positivity : (0 : ℝ) ≤ (P.r : ℝ) ^ 2)
      have e : (m : ℝ) / (2 * P.r) * (P.r : ℝ) ^ 2 = m * P.r / 2 := by field_simp
      rw [e] at this
      have : (m : ℝ) * P.r / 2 ^ 17 = m * P.r / 2 / 2 ^ 16 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hnR : (m : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt L) = m * Rb / 2 ^ 18 := by
      rw [Regimes.rpow_three_halves (by positivity), hRbdef, Regimes.sqrt_div_four hLpos]
      have : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
      field_simp
    rw [hnR]
    have : (m : ℝ) * Rb / 2 ^ 18 ≤ m * P.r / 2 ^ 17 := by
      have : (m : ℝ) * Rb ≤ m * (2 * P.r) := mul_le_mul_of_nonneg_left (by linarith)
        (Nat.cast_nonneg m)
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith

end LearningGuided.PointwiseLB
