import LearningGuided.Sec4.Sampling

/-!
# The certificate tradeoff (Theorem `thm:main`, certification part)

A certification procedure is an algorithm `Alg (Str n → ℝ)` returning a fully specified measure.
It succeeds against the hidden key `θ` when the returned measure is a coherent correction at
factor `9/4` for `(μ_θ, h_θ)` with mass at most `B`.

* `eq:dstar`: the minimum coherent correction mass is `d_m = α - (5/4 + α)/M > 0`.
* `eq:cert-tradeoff`: for `B ≥ d_m` the largest uniformly guaranteed success probability with
  cap `q` is exactly `min {1, (q + ⌊B/d_m⌋)/M}`.
* Producing an optimal-mass correction with certainty needs exactly `M - 1` queries.
* The success threshold `q + ⌊B/d_m⌋ ≥ ⌈(1-ζ)M⌉` and the fixed-budget bound `eq:fixed-B`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec4

open Sec2

variable {m : ℕ}

/-! ### Probabilities of events under binds -/

open Classical in
theorem probE_pure {β : Type} (b : β) (E : Set β) :
    probE (PMF.pure b) E = if b ∈ E then 1 else 0 := by
  classical
  unfold probE
  rw [PMF.toOuterMeasure_pure_apply]

theorem probE_ne_top {β : Type} (p : PMF β) (E : Set β) : probE p E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)

theorem probE_bind_toReal {γ β : Type} [Fintype γ] (p : PMF γ) (f : γ → PMF β) (E : Set β) :
    (probE (p.bind f) E).toReal = ∑ g, lawR p g * (probE (f g) E).toReal := by
  unfold probE
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, lawR]
  · intro g _
    exact ENNReal.mul_ne_top (p.apply_ne_top g) (probE_ne_top _ _)

theorem sum_lawR_congr_support {γ : Type} [Fintype γ] (p : PMF γ) (F G : γ → ℝ)
    (h : ∀ g ∈ p.support, F g = G g) : ∑ g, lawR p g * F g = ∑ g, lawR p g * G g := by
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g ∈ p.support
  · rw [h g hg]
  · rw [PMF.mem_support_iff, not_not] at hg
    simp [lawR, hg]

theorem probE_toReal_le_one {β : Type} (p : PMF β) (E : Set β) : (probE p E).toReal ≤ 1 := by
  have := probE_le_one p E
  have h := ENNReal.toReal_mono ENNReal.one_ne_top this
  simpa using h

/-! ### Success events -/

/-- Success of a certification procedure: the returned measure is a coherent correction at factor
`9/4` for the hidden target and guide, with mass at most `B`. -/
def certSucc (m : ℕ) (θ : Str (2 * m)) (B : ℝ) : Set (Str (3 * m + 2) → ℝ) :=
  {κ | IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ ∧ ∑ x, κ x ≤ B}

theorem pre_key (θ : Str (2 * m)) : pre (xθ m θ) (2 * m) = List.ofFn θ := by
  have h := isPre_iff_pre.mp (isPre_key_xθ (m := m) θ)
  rw [List.length_ofFn] at h
  exact h.symm

/-- `eq:dstar`: `d_m = α - (5/4 + α)/M > 0`, and the minimum coherent correction mass is `d_m`:
the correction `d_m δ_{x_θ}` has mass `d_m`, and every coherent correction has mass at least
`d_m`. In particular no valid certificate of mass below `d_m` exists. -/
theorem dstar (hm : 3 ≤ m) (θ : Str (2 * m)) :
    dm m = alpha m - (5 / 4 + alpha m) / 4 ^ m ∧ 0 < dm m ∧
      (IsCorrection (9 / 4) (muθ m θ) (hθ m θ) (optCorr m θ) ∧ ∑ x, optCorr m θ x = dm m) ∧
      (∀ κ, IsCorrection (9 / 4) (muθ m θ) (hθ m θ) κ → dm m ≤ ∑ x, κ x) ∧
      ∀ B < dm m, certSucc m θ B = ∅ :=
  ⟨rfl, dm_pos hm, ⟨isCorrection_optCorr hm θ, sum_optCorr θ⟩,
    fun _ hκ => correction_mass_ge hm θ hκ, fun B hB => by
      ext κ
      simp only [certSucc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hκ hsum
      linarith [correction_mass_ge hm θ hκ]⟩

open Classical in
/-- `sec:certification`: a single additive measure certifies at most `⌊B/d_m⌋` keys: valid
corrections put mass at least `d_m` on the disjoint depth-`k` prefixes naming their keys. -/
theorem cert_overlap (hm : 3 ≤ m) (B : ℝ) (κ : Str (3 * m + 2) → ℝ) :
    (Finset.univ.filter fun θ : Str (2 * m) => κ ∈ certSucc m θ B).card ≤ ⌊B / dm m⌋₊ := by
  classical
  set S := Finset.univ.filter fun θ : Str (2 * m) => κ ∈ certSucc m θ B with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨θ₀, hθ₀⟩
  · rw [h0]; simp
  have hκ0 : ∀ x, 0 ≤ κ x := ((Finset.mem_filter.mp hθ₀).2).1.1
  have hsumB : ∑ x, κ x ≤ B := ((Finset.mem_filter.mp hθ₀).2).2
  have hdm := dm_pos hm
  set W := S.image fun θ => List.ofFn θ with hW
  have hWcut : IsCut (3 * m + 2) W := by
    refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_⟩
    · obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hu; simp; omega
    · obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨θ', -, rfl⟩ := Finset.mem_image.mp hv
      exact huv.eq_of_length (by simp)
  have hWsum : ∑ u ∈ W, mass κ u = ∑ θ ∈ S, mass κ (List.ofFn θ) :=
    Finset.sum_image fun a _ b _ hab => List.ofFn_injective hab
  have hge : ∀ θ ∈ S, dm m ≤ mass κ (List.ofFn θ) := by
    intro θ hθ
    rw [← pre_key θ]
    exact correction_mass_k hm θ (Finset.mem_filter.mp hθ).2.1
  have h1 : (S.card : ℝ) * dm m ≤ B := by
    calc (S.card : ℝ) * dm m = ∑ θ ∈ S, dm m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ θ ∈ S, mass κ (List.ofFn θ) := Finset.sum_le_sum hge
      _ = ∑ u ∈ W, mass κ u := hWsum.symm
      _ ≤ ∑ x, κ x := hWcut.mass_sum_le hκ0
      _ ≤ B := hsumB
  exact Nat.le_floor ((le_div_iff₀ hdm).mpr h1)

/-- `eq:cert-tradeoff` (upper bound): every certification procedure with cap `q` against the hard
guides has worst-case success probability over the keys at most `min {1, (q + ⌊B/d_m⌋)/M}`.
The proof uses only that each query is simulated by one equality test. -/
theorem cert_upper (hm : 3 ≤ m) (B : ℝ) (q : ℕ) (A : Alg (Str (3 * m + 2) → ℝ))
    (hA : ∀ θ, A.Within (hθ m θ) q) :
    ∃ θ, (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal ≤
      min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m) := by
  classical
  have h1 := equality_counting (hθ m) (equality_hθ m) (fun θ => certSucc m θ B) ⌊B / dm m⌋₊ A
    Finset.univ q (fun κ => cert_overlap hm B κ) (fun θ _ => hA θ)
  have h2 := toReal_sum_probE_le Finset.univ (fun θ => A.run (hθ m θ))
    (fun θ => certSucc m θ B) (by simp) h1
  rw [ENNReal.toReal_add (by simp) (by simp)] at h2
  simp only [ENNReal.toReal_natCast] at h2
  by_contra hcon
  push Not at hcon
  have hlt : ∀ θ : Str (2 * m), ((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m <
      (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal := by
    intro θ
    have := hcon θ
    have hle1 := probE_toReal_le_one (A.run (hθ m θ)) (certSucc m θ B)
    rcases le_total 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m) with hc | hc
    · rw [min_eq_left hc] at this; linarith
    · rwa [min_eq_right hc] at this
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun θ _ => hlt θ
  rw [Finset.sum_const, Finset.card_univ, card_keys, nsmul_eq_mul] at hsum
  push_cast at hsum
  rw [mul_div_cancel₀ _ (by positivity)] at hsum
  linarith

/-! ### The attaining procedure -/

/-- The measure `d_m ∑_{κ ∈ T} δ_{x_κ}` certifying every key of `T`. -/
noncomputable def multiCorr (m : ℕ) (T : Finset (Str (2 * m))) : Str (3 * m + 2) → ℝ :=
  fun x => dm m * ∑ κ ∈ T, dirac (xθ m κ) x

theorem mass_multiCorr (T : Finset (Str (2 * m))) (u : List Bool) :
    mass (multiCorr m T) u = dm m * ∑ κ ∈ T, (if IsPre u (xθ m κ) then 1 else 0) := by
  unfold multiCorr
  rw [mass_smul, mass_finsum]
  simp_rw [mass_dirac]

theorem sum_multiCorr (T : Finset (Str (2 * m))) : ∑ x, multiCorr m T x = dm m * T.card := by
  unfold multiCorr
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp [(isDist_dirac _).2]

theorem multiCorr_mem_iff (hm : 3 ≤ m) (θ : Str (2 * m)) {B : ℝ} (T : Finset (Str (2 * m)))
    (hT : dm m * T.card ≤ B) : multiCorr m T ∈ certSucc m θ B ↔ θ ∈ T := by
  classical
  have hdm := dm_pos hm
  constructor
  · rintro ⟨hc, -⟩
    by_contra hθT
    have h1 := correction_mass_k hm θ hc
    rw [mass_multiCorr, pre_key] at h1
    have : ∑ κ ∈ T, (if IsPre (List.ofFn θ) (xθ m κ) then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun κ hκ => ?_
      have : ¬ IsPre (List.ofFn θ) (xθ m κ) := by
        intro h
        have := keyOf_eq h (by simp)
        have e : keyOf m (List.ofFn θ) = θ := keyOf_eq (isPre_key_xθ θ) (by simp)
        exact hθT (by rw [← e, this]; exact hκ)
      simp [this]
    rw [this, mul_zero] at h1
    linarith
  · intro hθT
    refine ⟨⟨fun x => ?_, fun u hu => ?_⟩, by rw [sum_multiCorr]; exact hT⟩
    · unfold multiCorr
      refine mul_nonneg hdm.le (Finset.sum_nonneg fun κ _ => ?_)
      unfold dirac; split_ifs <;> norm_num
    · rw [mass_multiCorr]
      refine (defect_le hm θ hu).trans ?_
      gcongr
      exact Finset.single_le_sum (f := fun κ => if IsPre u (xθ m κ) then (1 : ℝ) else 0)
        (fun κ _ => by split_ifs <;> norm_num) hθT

theorem optCorr_mem (hm : 3 ≤ m) (θ : Str (2 * m)) {B : ℝ} (hB : dm m ≤ B) :
    optCorr m θ ∈ certSucc m θ B :=
  ⟨isCorrection_optCorr hm θ, by rw [sum_optCorr]; exact hB⟩

/-- The attaining procedure: test `min{q, M}` uniformly chosen keys at their complete strings; on
a hit return `d_m δ_{x_θ}`; otherwise choose uniformly `min{⌊B/d_m⌋, #untested}` untested keys
and put mass `d_m` on each of their distinguished strings. -/
noncomputable def certAlg (m q K : ℕ) : Alg (Str (3 * m + 2) → ℝ) :=
  searchAlg (min q (4 ^ m)) (by rw [card_keys]; exact min_le_right _ _)
    (fun κ => List.ofFn (xθ m κ)) (fun _ r => (1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹ < r)
    (fun κ => Alg.ret (optCorr m κ))
    (fun S => Alg.sample (subsetsPMF (Finset.univ \ S) (min K (Finset.univ \ S).card)
      (min_le_right _ _)) (fun T => Alg.ret (multiCorr m T)))

theorem within_certAlg (m q K : ℕ) (h : Guide) : (certAlg m q K).Within h q := by
  have := within_searchAlg (min q (4 ^ m)) (by rw [card_keys]; exact min_le_right _ _)
    (fun κ => List.ofFn (xθ m κ)) (fun _ r => (1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹ < r)
    (fun κ => Alg.ret (optCorr m κ))
    (fun S => Alg.sample (subsetsPMF (Finset.univ \ S) (min K (Finset.univ \ S).card)
      (min_le_right _ _)) (fun T => Alg.ret (multiCorr m T))) h 0
    (fun _ => Alg.Within.ret _ 0)
    (fun _ => Alg.Within.sample _ _ _ fun g _ => Alg.Within.ret _ 0)
  exact this.mono (by omega)

theorem certAlg_success (hm : 3 ≤ m) (B : ℝ) (hB : dm m ≤ B) (q : ℕ) (θ : Str (2 * m)) :
    (probE ((certAlg m q ⌊B / dm m⌋₊).run (hθ m θ)) (certSucc m θ B)).toReal =
      min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m) := by
  classical
  set K := ⌊B / dm m⌋₊ with hK
  set M := 4 ^ m with hMdef
  set q' := min q M with hq'
  have hdm := dm_pos hm
  have hKB : dm m * K ≤ B := by
    have := Nat.floor_le (div_nonneg (hdm.le.trans hB) hdm.le)
    rw [← hK] at this
    rw [le_div_iff₀ hdm] at this
    linarith
  have hleaf := (isOracle_hθ hm θ).leaf
  set c : ℝ := (min K (M - q') : ℕ) / ((M - q' : ℕ) : ℝ) with hc
  unfold certAlg
  rw [run_searchAlg _ _ _ _ _ _ (hθ m θ) θ (leaf_test hleaf), probE_bind_toReal]
  refine (sum_lawR_congr_support _ _ (fun S => if θ ∈ S then (1 : ℝ) else c)
    fun S hS => ?_).trans ?_
  · have hScard := (mem_support_subsetsPMF hS).2
    by_cases hθS : θ ∈ S
    · simp only [hθS, ite_true, Alg.run_ret, probE_pure, optCorr_mem hm θ hB,
        ENNReal.toReal_one]
    · simp only [hθS, ite_false, Alg.run_sample]
      rw [probE_bind_toReal]
      have hcompl : (Finset.univ \ S).card = M - q' := by
        rw [Finset.card_sdiff, Finset.card_univ, card_keys, Finset.inter_univ, hScard]
      refine (sum_lawR_congr_support _ _ (fun T => if θ ∈ T then (1 : ℝ) else 0)
        fun T hT => ?_).trans ?_
      · have hTcard := (mem_support_subsetsPMF hT).2
        have hTB : dm m * T.card ≤ B := by
          rw [hTcard]
          calc dm m * (min K (Finset.univ \ S).card : ℕ) ≤ dm m * K := by
                gcongr; exact_mod_cast min_le_left _ _
            _ ≤ B := hKB
        rw [Alg.run_ret, probE_pure]
        by_cases hθT : θ ∈ T
        · simp only [(multiCorr_mem_iff hm θ T hTB).mpr hθT, hθT, ite_true,
            ENNReal.toReal_one]
        · have : multiCorr m T ∉ certSucc m θ B :=
            fun h' => hθT ((multiCorr_mem_iff hm θ T hTB).mp h')
          simp only [this, hθT, ite_false, ENNReal.toReal_zero]
      · rw [prob_mem_subsetsPMF _ _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ θ, hθS⟩), hcompl]
  · rw [sum_lawR_ite, prob_mem_subsetsPMF _ _ _ (Finset.mem_univ θ), Finset.card_univ,
      card_keys]
    -- arithmetic
    have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
    have hMcast : ((M : ℕ) : ℝ) = (4 : ℝ) ^ m := by rw [hMdef]; push_cast; rfl
    change (q' : ℝ) / (M : ℝ) * 1 + (1 - (q' : ℝ) / (M : ℝ)) * c =
      min 1 (((q : ℝ) + K) / 4 ^ m)
    rw [← hMcast]
    rcases le_or_gt M q with hqM | hqM
    · have : q' = M := by rw [hq']; exact min_eq_right hqM
      rw [this, div_self (ne_of_gt hMpos), sub_self, zero_mul, add_zero, mul_one]
      symm
      rw [min_eq_left]
      rw [le_div_iff₀ hMpos, one_mul]
      have : (M : ℝ) ≤ q := by exact_mod_cast hqM
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    · have hq'q : q' = q := by rw [hq']; exact min_eq_left hqM.le
      rw [hq'q] at hc ⊢
      have hMq : (0 : ℝ) < ((M - q : ℕ) : ℝ) := by
        have : 0 < M - q := by omega
        exact_mod_cast this
      have hcast : ((M - q : ℕ) : ℝ) = (M : ℝ) - q := by
        rw [Nat.cast_sub hqM.le]
      rw [hc]
      have key : (q : ℝ) / M * 1 + (1 - (q : ℝ) / M) *
          (((min K (M - q) : ℕ) : ℝ) / ((M - q : ℕ) : ℝ)) =
          ((q : ℝ) + (min K (M - q) : ℕ)) / M := by
        rw [hcast] at hMq ⊢
        field_simp
      rw [key]
      rcases le_total K (M - q) with hKq | hKq
      · rw [min_eq_left hKq, min_eq_right]
        rw [div_le_one hMpos]
        have : ((K : ℕ) : ℝ) ≤ ((M - q : ℕ) : ℝ) := by exact_mod_cast hKq
        rw [hcast] at this
        linarith
      · rw [min_eq_right hKq, min_eq_left]
        · rw [hcast]; field_simp; ring
        · rw [le_div_iff₀ hMpos, one_mul]
          have : ((M - q : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKq
          rw [hcast] at this
          linarith

/-- `thm:main`, equation `eq:cert-tradeoff`: for `B ≥ d_m` and every cap `q`, the largest
uniformly guaranteed probability of returning a valid coherent correction of mass at most `B` is
exactly `min {1, (q + ⌊B/d_m⌋)/M}`: every procedure with cap `q` (against the hard guides) fails
to exceed it for some key, and `certAlg` attains it for every key. -/
theorem cert_tradeoff (hm : 3 ≤ m) (B : ℝ) (hB : dm m ≤ B) (q : ℕ) :
    (∀ A : Alg (Str (3 * m + 2) → ℝ), (∀ θ, A.Within (hθ m θ) q) →
      ∃ θ, (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal ≤
        min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m)) ∧
    ∃ A : Alg (Str (3 * m + 2) → ℝ), (∀ θ, A.Within (hθ m θ) q) ∧
      ∀ θ, (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal =
        min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m) :=
  ⟨fun A hA => cert_upper hm B q A hA, certAlg m q ⌊B / dm m⌋₊,
    fun θ => within_certAlg m q _ (hθ m θ), fun θ => certAlg_success hm B hB q θ⟩

/-- The certification complexity at optimal mass: the least cap of a procedure that returns a
valid correction of mass at most `d_m` with probability one for every key. -/
noncomputable def QcertHard (m : ℕ) : ℕ :=
  sInf {q | ∃ A : Alg (Str (3 * m + 2) → ℝ), ∀ θ, A.Within (hθ m θ) q ∧
    probE (A.run (hθ m θ)) (certSucc m θ (dm m)) = 1}

/-- `thm:main`: producing an optimal-mass correction with certainty requires exactly `M - 1`
queries. -/
theorem cert_certainty (hm : 3 ≤ m) : QcertHard m = 4 ^ m - 1 := by
  have hdm := dm_pos hm
  have hK : ⌊dm m / dm m⌋₊ = 1 := by rw [div_self (ne_of_gt hdm)]; simp
  have hM1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hsure : ∀ θ, probE ((certAlg m (4 ^ m - 1) 1).run (hθ m θ)) (certSucc m θ (dm m)) = 1 := by
    intro θ
    have := certAlg_success hm (dm m) le_rfl (4 ^ m - 1) θ
    rw [hK] at this
    have e : (((4 ^ m - 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) / 4 ^ m = 1 := by
      rw [Nat.cast_sub hM1]; push_cast; field_simp; ring
    rw [e, min_self] at this
    exact (ENNReal.toReal_eq_one_iff _).mp this
  have hmem : 4 ^ m - 1 ∈ {q | ∃ A : Alg (Str (3 * m + 2) → ℝ), ∀ θ, A.Within (hθ m θ) q ∧
      probE (A.run (hθ m θ)) (certSucc m θ (dm m)) = 1} :=
    ⟨certAlg m (4 ^ m - 1) 1, fun θ => ⟨within_certAlg _ _ _ _, hsure θ⟩⟩
  apply le_antisymm (Nat.sInf_le hmem)
  refine le_csInf ⟨_, hmem⟩ ?_
  rintro q ⟨A, hA⟩
  obtain ⟨θ, hθ⟩ := cert_upper hm (dm m) q A (fun θ => (hA θ).1)
  rw [(hA θ).2, hK, ENNReal.toReal_one] at hθ
  have h1 : 1 ≤ ((q : ℝ) + ((1 : ℕ) : ℝ)) / 4 ^ m := hθ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity), one_mul] at h1
  have : (4 ^ m : ℕ) ≤ q + 1 := by exact_mod_cast h1
  omega

/-- `thm:main` (success threshold): for `B ≥ d_m` and `ζ ≥ 0`, success probability at least
`1 - ζ` for every key is possible with cap `q` exactly when `q + ⌊B/d_m⌋ ≥ ⌈(1-ζ)M⌉`. -/
theorem cert_threshold (hm : 3 ≤ m) (B : ℝ) (hB : dm m ≤ B) (q : ℕ) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    (∃ A : Alg (Str (3 * m + 2) → ℝ), (∀ θ, A.Within (hθ m θ) q) ∧
      ∀ θ, 1 - ζ ≤ (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal) ↔
      ⌈(1 - ζ) * 4 ^ m⌉₊ ≤ q + ⌊B / dm m⌋₊ := by
  have hMpos : (0 : ℝ) < 4 ^ m := by positivity
  constructor
  · rintro ⟨A, hW, hS⟩
    obtain ⟨θ, hθ⟩ := cert_upper hm B q A hW
    have h1 : 1 - ζ ≤ ((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m := (hS θ).trans (hθ.trans (min_le_right _ _))
    rw [le_div_iff₀ hMpos] at h1
    exact Nat.ceil_le.mpr (by push_cast; exact h1)
  · intro h
    refine ⟨certAlg m q ⌊B / dm m⌋₊, fun θ => within_certAlg m q _ _, fun θ => ?_⟩
    rw [certAlg_success hm B hB q θ]
    refine le_min (by linarith) ?_
    rw [le_div_iff₀ hMpos]
    have := Nat.le_ceil ((1 - ζ) * 4 ^ m)
    have h' : (⌈(1 - ζ) * 4 ^ m⌉₊ : ℝ) ≤ ((q + ⌊B / dm m⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith

/-- `thm:main`, equation `eq:fixed-B`: for every budget `B ≥ 0`, a procedure with cap `q` whose
success probability is at least `1 - ζ` for every key satisfies `q ≥ (1-ζ)M - 2B√M`. -/
theorem fixed_B (hm : 3 ≤ m) (B : ℝ) (hB : 0 ≤ B) (ζ : ℝ) (q : ℕ)
    (A : Alg (Str (3 * m + 2) → ℝ)) (hW : ∀ θ, A.Within (hθ m θ) q)
    (hS : ∀ θ, 1 - ζ ≤ (probE (A.run (hθ m θ)) (certSucc m θ B)).toReal) :
    (1 - ζ) * 4 ^ m - 2 * B * Real.sqrt (4 ^ m) ≤ q := by
  have hMpos : (0 : ℝ) < 4 ^ m := by positivity
  have hsqrt : Real.sqrt ((4 : ℝ) ^ m) = 2 ^ m := by
    rw [four_pow, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  obtain ⟨θ, hθ⟩ := cert_upper hm B q A hW
  have h1 : 1 - ζ ≤ ((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m := (hS θ).trans (hθ.trans (min_le_right _ _))
  rw [le_div_iff₀ hMpos] at h1
  have hdm := dm_pos hm
  have hfl : (⌊B / dm m⌋₊ : ℝ) ≤ B / dm m := Nat.floor_le (div_nonneg hB hdm.le)
  have hhalf := dm_ge_half_alpha hm
  have hα := alpha_pos m
  have h2 : B / dm m ≤ 2 * B * 2 ^ m := by
    rw [div_le_iff₀ hdm]
    have e : alpha m * 2 ^ m = 1 := alpha_mul m
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have : 0 ≤ 2 * B * 2 ^ m * (dm m - alpha m / 2) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 2 * B * 2 ^ m * dm m - B = 2 * B * 2 ^ m * (dm m - alpha m / 2) +
        B * (alpha m * 2 ^ m - 1) := by ring
    rw [e, sub_self, mul_zero, add_zero] at e2
    linarith
  linarith

end Sec4
end LearningGuided
