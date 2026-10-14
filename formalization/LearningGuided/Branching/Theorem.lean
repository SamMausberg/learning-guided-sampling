import LearningGuided.Branching.Algorithm

/-!
# `thm:branching`: branching with an explicit cap

Under the hypotheses of `thm:branching` (`BranchHyp`), for the pooled population of `P` trees:

* `E Y(x) = P μ(x)` (`expect_leafCount`) and `E T = P` (`expect_total`); for one tree these are
  `eq:branch-unbiased` (`branch_unbiased`), and `E N(u) = h(u)` is `expect_count_word`.
* `E T² = P² + P S` with `S = ∑_{t=1}^{n} ∑_{|v|=t} μ(v)²/h(v)` (`expect_total_sq`), hence
  `E (T - P)² = P S ≤ P B` (`expect_dev_sq`); for one tree `Var L = S ≤ B` (`branch_var`).
* `E[(T/P) ρ] = μ` (`expect_total_mul_outLaw`).
* the untruncated output law is within `δ/2` of `μ` (`tv_branchU_le`), the expected number of
  queries is at most `2PA` (`expect_count_le`), the abort probability is at most `δ/2`
  (`abort_le`), and the capped sampler has error at most `δ` with deterministic cap
  `q = ⌈4PA/δ⌉` (`branching`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Branching

open Upper

variable {n : ℕ} {μ : Str n → ℝ} {h : Guide}

theorem leafCount_eq_lin (pop : List (List Bool)) (x : Str n) :
    (leafCount pop x : ℝ≥0∞) = lin (fun w => if w = List.ofFn x then 1 else 0) pop := by
  rw [lin_indicator]; rfl

theorem total_eq_lin (pop : List (List Bool)) :
    (total n pop : ℝ≥0∞) = lin (fun w => if w.length = n then 1 else 0) pop := by
  simp only [total, Nat.cast_sum, leafCount_eq_lin]
  rw [← lin_finset_sum]
  congr 1; ext w
  exact sum_ite_ofFn_eq w 1

/-- `thm:branching` (proof): `E Y(x) = P μ(x)` for the pooled population of `P` trees. -/
theorem expect_leafCount (H : BranchHyp μ h) (P : ℕ) (x : Str n) :
    expect (levelsP h n (List.replicate P [])) (fun pc => (leafCount pc.1 x : ℝ≥0∞)) =
      P * ENNReal.ofReal (μ x) := by
  simp_rw [leafCount_eq_lin]
  rw [expect_levelsP_lin H P n le_rfl]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', ite_eq_left (mem_words.mpr (List.length_ofFn)), H.leaf]

/-- `thm:branching` (proof): `E T = P`. -/
theorem expect_total (H : BranchHyp μ h) (P : ℕ) :
    expect (levelsP h n (List.replicate P [])) (fun pc => (total n pc.1 : ℝ≥0∞)) = P := by
  simp_rw [total_eq_lin]
  rw [expect_levelsP_lin H P n le_rfl]
  have : ∑ w ∈ words n, (if w.length = n then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (h w) = 1 := by
    rw [Finset.sum_congr rfl fun w hw => by
      rw [ite_eq_left (mem_words.mp hw), one_mul, H.leaf_mass (mem_words.mp hw)]]
    rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => mass_nonneg H.dist.1 w,
      sum_mass_words μ le_rfl, H.dist.2, ENNReal.ofReal_one]
  rw [this, mul_one]

/-- Almost surely no particle sits at a zero-valued word. -/
theorem support_ne_zero (H : BranchHyp μ h) (P : ℕ) :
    ∀ pc ∈ (levelsP h n (List.replicate P [])).support, ∀ w ∈ pc.1, h w ≠ 0 := by
  classical
  have hE := expect_levelsP_lin H P n le_rfl (fun w => if h w = 0 then 1 else 0)
  have h0 : ∑ w ∈ words n, (if h w = 0 then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (h w) = 0 :=
    Finset.sum_eq_zero fun w _ => by
      by_cases hw : h w = 0 <;> simp [hw]
  rw [h0, mul_zero] at hE
  intro pc hpc w hw hzero
  have := lin_eq_zero (eq_zero_of_expect_eq_zero _ hE pc hpc) w hw
  simp [hzero] at this

/-- On the support, the terminal count is the martingale value `Z_n`. -/
theorem total_eq_Z (H : BranchHyp μ h) (P : ℕ) :
    ∀ pc ∈ (levelsP h n (List.replicate P [])).support,
      (total n pc.1 : ℝ≥0∞) = lin (zc μ h n) pc.1 := by
  intro pc hpc
  rw [total_eq_lin]
  refine lin_congr fun w hw => ?_
  unfold zc
  by_cases hl : w.length = n
  · rw [ite_eq_left hl, ite_eq_left hl, ← H.leaf_mass hl,
      div_self (support_ne_zero H P pc hpc w hw), ENNReal.ofReal_one]
  · rw [ite_eq_right hl, ite_eq_right hl]

/-- The reciprocal moment `S = ∑_{t=1}^{n} ∑_{|v|=t} μ(v)²/h(v)` (in `[0,∞]`). -/
noncomputable def recipSum (n : ℕ) (μ : Str n → ℝ) (h : Guide) : ℝ≥0∞ :=
  ∑ s ∈ Finset.range n, ∑ v ∈ words (s + 1), ENNReal.ofReal (mass μ v ^ 2 / h v)

/-- `thm:branching` (proof): `E T² = P² + P S`. -/
theorem expect_total_sq (H : BranchHyp μ h) (P : ℕ) :
    expect (levelsP h n (List.replicate P [])) (fun pc => (total n pc.1 : ℝ≥0∞) ^ 2) =
      (P : ℝ≥0∞) ^ 2 + P * recipSum n μ h := by
  rw [expect_congr_support _ fun pc hpc => by rw [total_eq_Z H P pc hpc]]
  exact expect_levelsP_Zsq H P n le_rfl

theorem ofReal_sq_sub_add (T P : ℕ) :
    ENNReal.ofReal (((T : ℝ) - P) ^ 2) + 2 * P * T = (T : ℝ≥0∞) ^ 2 + (P : ℝ≥0∞) ^ 2 := by
  have h1 : (2 * P * T : ℝ≥0∞) = ENNReal.ofReal (2 * P * T) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp
  have h2 : (T : ℝ≥0∞) ^ 2 + (P : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((T : ℝ) ^ 2 + (P : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow (by positivity)]
    simp
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- `thm:branching` (proof): `E (T - P)² = P S`, the variance of `T` (with `E T = P`). -/
theorem expect_dev_sq (H : BranchHyp μ h) (P : ℕ) :
    expect (levelsP h n (List.replicate P []))
      (fun pc => ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) - P) ^ 2)) = P * recipSum n μ h := by
  set p := levelsP h n (List.replicate P [])
  have key : expect p (fun pc => ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) - P) ^ 2)) +
      2 * P * P = (P : ℝ≥0∞) ^ 2 + P * recipSum n μ h + (P : ℝ≥0∞) ^ 2 := by
    have e := congrArg (fun f => expect p f) (funext fun pc => ofReal_sq_sub_add (total n pc.1) P)
    rw [expect_add, expect_const_mul, expect_total H P, expect_add, expect_const,
      expect_total_sq H P] at e
    exact e
  have h2 : (2 * P * P : ℝ≥0∞) = (P : ℝ≥0∞) ^ 2 + (P : ℝ≥0∞) ^ 2 := by ring
  rw [h2, ← add_assoc] at key
  have hne : (P : ℝ≥0∞) ^ 2 ≠ ∞ := by simp
  have := (ENNReal.add_left_inj hne).mp key
  rw [add_comm] at this
  exact (ENNReal.add_right_inj hne).mp this

/-- The mean absolute deviation: `(E|T - P|)² ≤ P S`. -/
theorem expect_abs_dev_sq_le (H : BranchHyp μ h) (P : ℕ) :
    expect (levelsP h n (List.replicate P []))
      (fun pc => ENNReal.ofReal |((total n pc.1 : ℕ) : ℝ) - P|) ^ 2 ≤ P * recipSum n μ h := by
  rw [← expect_dev_sq H P]
  refine (expect_sq_le _ _).trans (le_of_eq ?_)
  congr 1; ext pc
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem absDiff_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    absDiff (ENNReal.ofReal a) (ENNReal.ofReal b) = ENNReal.ofReal |a - b| := by
  rw [absDiff_eq_ofReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb]

theorem natCast_div_eq_ofReal (a b : ℕ) (hb : b ≠ 0) :
    (a : ℝ≥0∞) / b = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp

/-- The `ℓ¹` distance between `ρ` and the unnormalized measure `Y/P` is `|T - P|/P`, including
the extinction case `T = 0`. -/
theorem sum_absDiff_outLaw (pop : List (List Bool)) {P : ℕ} (hP : P ≠ 0) :
    ∑ x : Str n, absDiff (outLaw n pop x) ((leafCount pop x : ℝ≥0∞) / P) =
      ENNReal.ofReal |((total n pop : ℕ) : ℝ) - P| / P := by
  by_cases hT : total n pop = 0
  · have hG : ∀ x : Str n, leafCount pop x = 0 := fun x =>
      (Finset.sum_eq_zero_iff.mp hT) x (Finset.mem_univ x)
    simp only [outLaw, hT, ↓reduceDIte, hG, Nat.cast_zero, ENNReal.zero_div]
    have h1 : ∀ x : Str n, absDiff (PMF.pure (fbStr n) x) 0 = PMF.pure (fbStr n) x := by
      intro x; simp [absDiff]
    simp_rw [h1]
    have h2 : ∑ x : Str n, PMF.pure (fbStr n) x = 1 := by
      have := PMF.tsum_coe (PMF.pure (fbStr n))
      rwa [tsum_fintype] at this
    rw [h2, zero_sub, abs_neg, abs_of_nonneg (by positivity), ENNReal.ofReal_natCast,
      ENNReal.div_self (by exact_mod_cast hP) (ENNReal.natCast_ne_top P)]
  · simp only [outLaw, hT, ↓reduceDIte, PMF.ofFintype_apply]
    rw [Finset.sum_congr rfl fun x _ => by
      rw [natCast_div_eq_ofReal _ _ hT, natCast_div_eq_ofReal _ _ hP,
        absDiff_ofReal (by positivity) (by positivity)]]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => abs_nonneg _, ← ENNReal.ofReal_natCast P,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    have hTpos : (0 : ℝ) < total n pop := by positivity
    have hPpos : (0 : ℝ) < P := by positivity
    have e1 : ∀ x : Str n, |(leafCount pop x : ℝ) / total n pop - (leafCount pop x : ℝ) / P| =
        (leafCount pop x : ℝ) * |1 / (total n pop : ℝ) - 1 / P| := by
      intro x
      rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (leafCount pop x)), ← abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (leafCount pop x))]
      congr 1; ring
    simp_rw [e1]
    rw [← Finset.sum_mul]
    have e2 : ∑ x : Str n, (leafCount pop x : ℝ) = total n pop := by simp [total]
    rw [e2, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos]
    have e3 : (total n pop : ℝ) * (1 / (total n pop : ℝ) - 1 / P) = (P - total n pop) / P := by
      field_simp
    rw [e3, abs_div, abs_of_pos hPpos, abs_sub_comm]

/-- `thm:branching` (proof): `E[(T/P) ρ] = μ`; the unnormalized empirical measure is unbiased,
including extinction. -/
theorem expect_total_mul_outLaw (H : BranchHyp μ h) {P : ℕ} (hP : P ≠ 0) (x : Str n) :
    expect (levelsP h n (List.replicate P []))
      (fun pc => (total n pc.1 : ℝ≥0∞) / P * outLaw n pc.1 x) = ENNReal.ofReal (μ x) := by
  have e : ∀ pc : List (List Bool) × ℕ, (total n pc.1 : ℝ≥0∞) / P * outLaw n pc.1 x =
      (leafCount pc.1 x : ℝ≥0∞) * (P : ℝ≥0∞)⁻¹ := by
    intro pc
    by_cases hT : total n pc.1 = 0
    · have hG : leafCount pc.1 x = 0 :=
        (Finset.sum_eq_zero_iff.mp hT) x (Finset.mem_univ x)
      simp [hT, hG]
    · simp only [outLaw, hT, ↓reduceDIte, PMF.ofFintype_apply]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hT' : (total n pc.1 : ℝ≥0∞) ≠ 0 := by exact_mod_cast hT
      calc (total n pc.1 : ℝ≥0∞) * (P : ℝ≥0∞)⁻¹ *
            ((leafCount pc.1 x : ℝ≥0∞) * (total n pc.1 : ℝ≥0∞)⁻¹)
          = (leafCount pc.1 x : ℝ≥0∞) * (P : ℝ≥0∞)⁻¹ *
              ((total n pc.1 : ℝ≥0∞) * (total n pc.1 : ℝ≥0∞)⁻¹) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel hT' (ENNReal.natCast_ne_top _), mul_one]
  simp_rw [e]
  rw [expect_mul_const, expect_leafCount H P x, mul_comm, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hP) (ENNReal.natCast_ne_top P), one_mul]

/-! ### The moment hypotheses `eq:branch-moments` -/

theorem sum_Icc_one_eq {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ t ∈ Finset.Icc 1 n, f t = ∑ t ∈ Finset.range n, f (t + 1)
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_one_eq f n, Finset.sum_range_succ]

theorem recipSum_le (H : BranchHyp μ h) {B : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) :
    recipSum n μ h ≤ ENNReal.ofReal B := by
  have hnn : ∀ u, 0 ≤ mass μ u ^ 2 / h u := fun u => div_nonneg (sq_nonneg _) (H.nonneg u)
  unfold recipSum
  rw [← sum_Icc_one_eq (fun t => ∑ v ∈ words t, ENNReal.ofReal (mass μ v ^ 2 / h v)) n]
  have : ∑ t ∈ Finset.Icc 1 n, ∑ v ∈ words t, ENNReal.ofReal (mass μ v ^ 2 / h v) =
      ENNReal.ofReal (∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => Finset.sum_nonneg fun u _ => hnn u]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun u _ => hnn u]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hB

/-- The level-`n` reciprocal sum is one, so `B ≥ 1`. -/
theorem one_le_B (H : BranchHyp μ h) (hn : 1 ≤ n) {B : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) : 1 ≤ B := by
  have hnn : ∀ u, 0 ≤ mass μ u ^ 2 / h u := fun u => div_nonneg (sq_nonneg _) (H.nonneg u)
  have h1 : ∑ u ∈ words n, mass μ u ^ 2 / h u = 1 := by
    rw [Finset.sum_congr rfl fun u hu => by rw [H.leaf_mass (mem_words.mp hu), sq_div_self_eq],
      sum_mass_words μ le_rfl, H.dist.2]
  have h2 := Finset.single_le_sum (f := fun t => ∑ u ∈ words t, mass μ u ^ 2 / h u)
    (fun t _ => Finset.sum_nonneg fun u _ => hnn u) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  linarith

theorem one_le_branchP (H : BranchHyp μ h) (hn : 1 ≤ n) {B δ : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) (hδ : 0 < δ) :
    1 ≤ branchP B δ := by
  have := one_le_B H hn hB
  unfold branchP
  exact Nat.one_le_iff_ne_zero.mpr fun h0 => by
    rw [Nat.ceil_eq_zero] at h0
    have : 0 < B / δ ^ 2 := by positivity
    linarith

/-! ### The untruncated output law -/

/-- `thm:branching` (proof): the untruncated output law is within half the mean relative deviation
of `T`. -/
theorem tv_branchU_le (H : BranchHyp μ h) {P : ℕ} (hP : P ≠ 0) :
    ENNReal.ofReal (2 * tv (lawR ((branchU n P).run h)) μ) ≤
      expect (levelsP h n (List.replicate P []))
        (fun pc => ENNReal.ofReal |((total n pc.1 : ℕ) : ℝ) - P|) / P := by
  rw [run_branchU H.root]
  have hν : ∀ x, ENNReal.ofReal (μ x) = ∑' pc, levelsP h n (List.replicate P []) pc *
      ((leafCount pc.1 x : ℝ≥0∞) / P) := by
    intro x
    have := expect_leafCount H P x
    simp_rw [div_eq_mul_inv]
    change _ = expect (levelsP h n (List.replicate P []))
      (fun pc : List (List Bool) × ℕ => (leafCount pc.1 x : ℝ≥0∞) * (P : ℝ≥0∞)⁻¹)
    rw [expect_mul_const, this, mul_comm, ← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast hP) (ENNReal.natCast_ne_top P), one_mul]
  refine (tv_bind_le _ _ _ H.dist.1 hν).trans (le_of_eq ?_)
  simp_rw [sum_absDiff_outLaw _ hP, div_eq_mul_inv]
  exact expect_mul_const _ _ _

/-- `thm:branching` (proof): the untruncated sampler has error at most `δ/2`
(`Var(T/P) ≤ B/P ≤ δ²`). -/
theorem tv_branchU_le_half (H : BranchHyp μ h) (hn : 1 ≤ n) {B δ : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) (hδ : 0 < δ) :
    tv (lawR ((branchU n (branchP B δ)).run h)) μ ≤ δ / 2 := by
  set P := branchP B δ with hPdef
  have hP1 : 1 ≤ P := one_le_branchP H hn hB hδ
  have hP0 : P ≠ 0 := by omega
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP1
  set e := expect (levelsP h n (List.replicate P []))
    (fun pc => ENNReal.ofReal |((total n pc.1 : ℕ) : ℝ) - P|) with he
  have he2 : e ^ 2 ≤ P * ENNReal.ofReal B :=
    (expect_abs_dev_sq_le H P).trans (mul_le_mul_right (recipSum_le H hB) _)
  have hetop : e ≠ ∞ := by
    intro htop
    rw [htop] at he2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow, top_le_iff] at he2
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top P) ENNReal.ofReal_ne_top he2
  have h1 := tv_branchU_le H hP0
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top hetop (by exact_mod_cast hP0)),
    ENNReal.toReal_div, ENNReal.toReal_natCast] at h1
  have h2 : e.toReal ^ 2 ≤ P * B := by
    have := (ENNReal.toReal_le_toReal (by simp [hetop])
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top P) ENNReal.ofReal_ne_top)).mpr he2
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by linarith [one_le_B H hn hB])] at this
  have h3 : B ≤ δ ^ 2 * P := by
    have : B / δ ^ 2 ≤ (P : ℝ) := Nat.le_ceil (B / δ ^ 2)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h4 : e.toReal ≤ δ * P := by
    have : e.toReal ^ 2 ≤ (δ * P) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg (by positivity) two_ne_zero).mp this
  have h5 : e.toReal / P ≤ δ := by rw [div_le_iff₀ hPpos]; linarith
  linarith

/-! ### Queries and the abort event -/

/-- `thm:branching` (proof): the expected number of queries of the `P` trees is at most `2PA`. -/
theorem expect_count_le (H : BranchHyp μ h) {A : ℝ}
    (hA : ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ A) (P : ℕ) :
    expect (levelsP h n (List.replicate P [])) (fun pc => (pc.2 : ℝ≥0∞)) ≤
      2 * P * ENNReal.ofReal A := by
  rw [expect_levelsP_count H P n le_rfl]
  gcongr
  have : ∑ s ∈ Finset.range n, ∑ w ∈ words s, ENNReal.ofReal (h w) =
      ENNReal.ofReal (∑ t ∈ Finset.range n, ∑ u ∈ words t, h u) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => Finset.sum_nonneg fun u _ => H.nonneg u]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun u _ => H.nonneg u]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hA

/-- `thm:branching` (proof): Markov's inequality for the abort event: the probability that the
forest needs more than
`q = ⌈4PA/δ⌉` queries is at most `2PA/(q+1) ≤ δ/2`. -/
theorem abort_le (H : BranchHyp μ h) {A B δ : ℝ}
    (hA : ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ A) (hδ : 0 < δ) :
    (probE (levelsP h n (List.replicate (branchP B δ) []))
      {pc | branchQ A B δ < pc.2}).toReal ≤ δ / 2 := by
  set P := branchP B δ
  set q := branchQ A B δ with hqdef
  set pr := probE (levelsP h n (List.replicate P [])) {pc | q < pc.2}
  have hA0 : 0 ≤ A :=
    (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun u _ => H.nonneg u).trans hA
  have h1 := (prob_lt_le_expect (levelsP h n (List.replicate P [])) Prod.snd q).trans
    (expect_count_le H hA P)
  have hprtop : pr ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)
  have h2 : ((q : ℝ) + 1) * pr.toReal ≤ 2 * P * A := by
    have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hprtop)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
        ENNReal.ofReal_ne_top)).mpr h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0,
      ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at this
  have h3 : 4 * P * A / δ ≤ q := Nat.le_ceil _
  have h4 : 2 * P * A ≤ δ / 2 * ((q : ℝ) + 1) := by
    rw [div_le_iff₀ hδ] at h3
    nlinarith
  have h5 : ((q : ℝ) + 1) * pr.toReal ≤ ((q : ℝ) + 1) * (δ / 2) := by linarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- `thm:branching`, equation `eq:branch-cap`: under `h(∅) = 1`, equal supports at every prefix,
exact leaves and the moment bounds `eq:branch-moments`, the capped Poisson branching sampler with
`P = ⌈B/δ²⌉` trees has deterministic cap `q = ⌈4PA/δ⌉` and unconditional error at most `δ`. -/
theorem branching (hn : 1 ≤ n) (hμ : IsDist μ) (hnn : ∀ u, 0 ≤ h u) (hroot : h [] = 1)
    (hsupp : ∀ u : List Bool, u.length ≤ n → (h u = 0 ↔ mass μ u = 0))
    (hleaf : ∀ x : Str n, h (List.ofFn x) = μ x) {A B : ℝ}
    (hA : ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ A)
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1) :
    (branchAlg n A B δ).Within h (branchQ A B δ) ∧
      tv (lawR ((branchAlg n A B δ).run h)) μ ≤ δ := by
  have H : BranchHyp μ h := ⟨hμ, hnn, hroot, hsupp, hleaf⟩
  refine ⟨within_branchAlg h A B δ, ?_⟩
  have hcap := tv_capAlg_le h (fbStr n) (branchU n (branchP B δ)) (branchQ A B δ)
  rw [probE_branchU_count hroot] at hcap
  have hab := abort_le H (B := B) hA hδ0
  have h1 : tv (lawR ((branchAlg n A B δ).run h)) (lawR ((branchU n (branchP B δ)).run h)) ≤
      δ / 2 := by
    have hne : probE (levelsP h n (List.replicate (branchP B δ) []))
        {pc | branchQ A B δ < pc.2} ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)
    have := (ENNReal.ofReal_le_iff_le_toReal hne).mp hcap
    exact this.trans hab
  have h2 := tv_branchU_le_half H hn hB hδ0
  have := tv_triangle (lawR ((branchAlg n A B δ).run h)) (lawR ((branchU n (branchP B δ)).run h)) μ
  linarith

/-! ### Single-tree statements -/

/-- `thm:branching` (proof): `E N(u) = h(u)` for one tree. -/
theorem expect_count_word (H : BranchHyp μ h) {t : ℕ} (ht : t ≤ n) {u : List Bool}
    (hu : u.length = t) :
    expect (levelsP h t [[]]) (fun pc => (pc.1.count u : ℝ≥0∞)) = ENNReal.ofReal (h u) := by
  have := expect_levelsP_lin H 1 t ht (fun w => if w = u then 1 else 0)
  simp only [List.replicate_one, lin_indicator, Nat.cast_one, one_mul, ite_mul, zero_mul] at this
  rw [this, Finset.sum_ite_eq', ite_eq_left (mem_words.mpr hu)]

/-- `eq:branch-unbiased`: for one tree, `E Y(x) = μ(x)` and `E L = 1`. -/
theorem branch_unbiased (H : BranchHyp μ h) :
    (∀ x : Str n, expect (levelsP h n [[]]) (fun pc => (leafCount pc.1 x : ℝ≥0∞)) =
      ENNReal.ofReal (μ x)) ∧
    expect (levelsP h n [[]]) (fun pc => (total n pc.1 : ℝ≥0∞)) = 1 := by
  refine ⟨fun x => ?_, ?_⟩
  · have := expect_leafCount H 1 x
    rwa [List.replicate_one, Nat.cast_one, one_mul] at this
  · have := expect_total H 1
    rwa [List.replicate_one, Nat.cast_one] at this

/-- `thm:branching` (proof): the martingale property `E[Z_{t+1} | population at depth t] = Z_t`. -/
theorem martingale_step (H : BranchHyp μ h) {t : ℕ} (ht : t < n) (pop : List (List Bool)) :
    expect (genP h pop) (lin (zc μ h (t + 1))) = lin (zc μ h t) pop := by
  rw [expect_genP_lin, H.pull_zc ht]

/-- `thm:branching` (proof): the martingale variance identity
`E Z_{t+1}² = E Z_t² + P ∑_{|v|=t+1} μ(v)²/h(v)`, i.e. the
squared increments have expectation `∑_{|v|=t+1} μ(v)²/h(v)` per root particle. -/
theorem martingale_increment (H : BranchHyp μ h) (P : ℕ) {t : ℕ} (ht : t < n) :
    expect (levelsP h (t + 1) (List.replicate P []))
        (fun pc => lin (zc μ h (t + 1)) pc.1 ^ 2) =
      expect (levelsP h t (List.replicate P [])) (fun pc => lin (zc μ h t) pc.1 ^ 2) +
        P * ∑ v ∈ words (t + 1), ENNReal.ofReal (mass μ v ^ 2 / h v) := by
  rw [expect_levelsP_Zsq H P (t + 1) ht, expect_levelsP_Zsq H P t ht.le, Finset.sum_range_succ,
    mul_add, add_assoc]

/-- `thm:branching` (proof): the expected query count of one tree is
`2 ∑_{t<n} ∑_{|u|=t} h(u) ≤ 2A`: two queries per
processed particle, and the root value is known without a query. -/
theorem branch_tree_queries (H : BranchHyp μ h) {A : ℝ}
    (hA : ∑ t ∈ Finset.range n, ∑ u ∈ words t, h u ≤ A) :
    expect (levelsP h n [[]]) (fun pc => (pc.2 : ℝ≥0∞)) =
      2 * ∑ t ∈ Finset.range n, ∑ u ∈ words t, ENNReal.ofReal (h u) ∧
    expect (levelsP h n [[]]) (fun pc => (pc.2 : ℝ≥0∞)) ≤ 2 * ENNReal.ofReal A := by
  have e := expect_levelsP_count H 1 n le_rfl
  have b := expect_count_le H hA 1
  simp only [List.replicate_one, Nat.cast_one, mul_one] at e b
  exact ⟨e, b⟩

/-- `thm:branching` (proof): `Var(T/P) = S/P ≤ B/P` for the pooled count of `P` independent trees.
-/
theorem var_total_div (H : BranchHyp μ h) {P : ℕ} (hP : P ≠ 0) {B : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) :
    expect (levelsP h n (List.replicate P []))
      (fun pc => ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) / P - 1) ^ 2)) =
        recipSum n μ h / P ∧ recipSum n μ h / P ≤ ENNReal.ofReal B / P := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero hP
  have e : ∀ pc : List (List Bool) × ℕ,
      ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) / P - 1) ^ 2) =
        ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) - P) ^ 2) * ((P : ℝ≥0∞) ^ 2)⁻¹ := by
    intro pc
    have : (((total n pc.1 : ℕ) : ℝ) / P - 1) ^ 2 =
        (((total n pc.1 : ℕ) : ℝ) - P) ^ 2 / (P : ℝ) ^ 2 := by
      field_simp
    rw [this, ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv,
      ENNReal.ofReal_pow hPpos.le, ENNReal.ofReal_natCast]
  simp_rw [e]
  rw [expect_mul_const, expect_dev_sq H P]
  refine ⟨?_, ENNReal.div_le_div_right (recipSum_le H hB) _⟩
  have hP' : (P : ℝ≥0∞) ≠ 0 := by exact_mod_cast hP
  rw [sq, ENNReal.mul_inv (Or.inl hP') (Or.inl (ENNReal.natCast_ne_top P)), div_eq_mul_inv]
  calc (P : ℝ≥0∞) * recipSum n μ h * ((P : ℝ≥0∞)⁻¹ * (P : ℝ≥0∞)⁻¹)
      = recipSum n μ h * (P : ℝ≥0∞)⁻¹ * ((P : ℝ≥0∞) * (P : ℝ≥0∞)⁻¹) := by ring
    _ = recipSum n μ h * (P : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hP' (ENNReal.natCast_ne_top P), mul_one]

/-- `thm:branching` (proof): for one tree,
`Var L = E (L - 1)² = ∑_{t=1}^{n} ∑_{|v|=t} μ(v)²/h(v) ≤ B`. -/
theorem branch_var (H : BranchHyp μ h) {B : ℝ}
    (hB : ∑ t ∈ Finset.Icc 1 n, ∑ u ∈ words t, mass μ u ^ 2 / h u ≤ B) :
    expect (levelsP h n [[]]) (fun pc => ENNReal.ofReal ((((total n pc.1 : ℕ) : ℝ) - 1) ^ 2)) =
      recipSum n μ h ∧ recipSum n μ h ≤ ENNReal.ofReal B := by
  have := expect_dev_sq H 1
  simp only [List.replicate_one, Nat.cast_one, one_mul] at this
  exact ⟨this, recipSum_le H hB⟩

end Branching
end LearningGuided
