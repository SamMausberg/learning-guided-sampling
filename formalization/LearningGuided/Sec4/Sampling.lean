import LearningGuided.Sec4.Capacity

/-!
# Safe and pointwise sampling caps (Theorem `thm:main`, sampling part)

* Every query to `h_θ` is simulated by one equality test of a key (`equality_hθ`).
* `eq:search-lower`: a `δ`-accurate safe sampler has `q ≥ α(M-1) - δM`.
* `eq:search-law`: testing `q` uniformly chosen keys and otherwise drawing from `U_n` has output
  law `(1 - q/M) U_n + (q/M) δ_{x_θ}` for every guide with exact leaves.
* `eq:binary-lower`: a `δ`-accurate pointwise sampler has `2^q ≥ M(α - δ) + a`.
* The eight-group sampler is exact for every pointwise factor-`9/4` guide with cap `m + 5`.
* `eq:point-exact` and `eq:safe-exact`.
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec4

open Sec2

variable {m : ℕ}

theorem card_keys (m : ℕ) : Fintype.card (Str (2 * m)) = 4 ^ m := by
  simp [pow_mul]

/-! ### Equality access -/

/-- The key named by the first `k = 2m` bits of a word. -/
def keyOf (m : ℕ) (u : List Bool) : Str (2 * m) := fun i => u.getD i.1 false

theorem keyOf_eq {θ : Str (2 * m)} {u : List Bool} (h : IsPre u (xθ m θ))
    (hu : 2 * m ≤ u.length) : keyOf m u = θ := by
  rw [isPre_iff_getElem] at h
  obtain ⟨_, h⟩ := h
  funext i
  have := h i.1 (by omega)
  simp only [keyOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i.1 < u.length
    by omega), Option.getD_some, this, xθ, i.2, dite_true]

/-- `lem:equality` (equality access for `h_θ`): every query to `h_θ` is answered by a public value
unless the key it names is `θ`. -/
theorem equality_hθ (m : ℕ) : EqualityStructure (hθ m) := by
  intro u
  refine ⟨some (keyOf m u),
    if u.length ≤ 3 * m + 2 then (1 - bet m u.length) * ((2 : ℝ) ^ u.length)⁻¹ else 0,
    fun θ hθk => ?_⟩
  by_cases hn : u.length ≤ 3 * m + 2
  · rw [hθ_of_le m θ hn, ite_eq_left hn]
    by_cases hk : u.length ≤ 2 * m
    · rw [bet_of_le hk]; ring
    · have : ¬ IsPre u (xθ m θ) := fun h =>
        hθk (congrArg some (keyOf_eq h (by omega)))
      rw [ite_eq_right this]; ring
  · rw [hθ_of_gt m θ (by omega), ite_eq_right hn]

/-- The event "the first `k` bits equal `θ`". -/
noncomputable def keyEvent (m : ℕ) (θ : Str (2 * m)) : Finset (Str (3 * m + 2)) :=
  Finset.univ.filter fun x => IsPre (List.ofFn θ) x

theorem isPre_key_xθ (θ : Str (2 * m)) : IsPre (List.ofFn θ) (xθ m θ) := by
  rw [isPre_iff_getElem]
  refine ⟨by simp; omega, fun i hi => ?_⟩
  simp only [List.length_ofFn] at hi
  simp [xθ, hi]

theorem sum_keyEvent (θ : Str (2 * m)) :
    ∑ x ∈ keyEvent m θ, muθ m θ x = (1 - alpha m) * alpha m ^ 2 + alpha m := by
  have : ∑ x ∈ keyEvent m θ, muθ m θ x = mass (muθ m θ) (List.ofFn θ) := by
    unfold keyEvent mass; rw [Finset.sum_filter]
  rw [this, mass_muθ m θ (by simp; omega), ite_eq_left (isPre_key_xθ θ), List.length_ofFn,
    two_pow_inv_two_m]
  ring

theorem keyEvent_overlap (m : ℕ) (x : Str (3 * m + 2)) :
    (Finset.univ.filter fun θ : Str (2 * m) => x ∈ keyEvent m θ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, keyEvent, Finset.mem_univ, true_and] at ha hb
  rcases ha.comparable hb with h | h
  · exact List.ofFn_injective (h.eq_of_length (by simp))
  · exact (List.ofFn_injective (h.eq_of_length (by simp))).symm

/-- `eq:search-lower`: every sampler with cap `q` and accuracy `δ` for `F_m` in the safe model
(against the hard guides) satisfies `q ≥ α(M-1) - δM`. -/
theorem search_lower (δ : ℝ) (q : ℕ) (A : Alg (Str (3 * m + 2)))
    (hm : 3 ≤ m) (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (Fm m) δ q A) :
    alpha m * ((4 : ℝ) ^ m - 1) - δ * 4 ^ m ≤ q := by
  have hbound := sampling_equality_bound (hθ m) (equality_hθ m) (muθ m) (isDist_muθ m)
    (keyEvent m) (keyEvent_overlap m) A q δ
    (fun θ => hA (muθ m θ) ⟨θ, rfl⟩ (hθ m θ) (safeLegal_hθ hm θ))
  simp only [sum_keyEvent, Finset.sum_const, Finset.card_univ, card_keys, nsmul_eq_mul] at hbound
  push_cast at hbound
  have h2 : alpha m ^ 2 * (4 : ℝ) ^ m = 1 := by rw [alpha_sq]; field_simp
  rw [show (4 : ℝ) ^ m * ((1 - alpha m) * alpha m ^ 2 + alpha m - δ) =
    (1 - alpha m) * (alpha m ^ 2 * 4 ^ m) + alpha m * 4 ^ m - δ * 4 ^ m by ring, h2] at hbound
  linarith

/-- `eq:binary-lower`: every pointwise sampler with cap `q` and accuracy `δ` for `F_m` satisfies
`2^q ≥ M(α - δ) + a` (using the exact guides `h = μ_θ`). -/
theorem binary_lower (δ : ℝ) (q : ℕ) (A : Alg (Str (3 * m + 2)))
    (hA : Solves (PwLegal (9 / 4)) (Fm m) δ q A) :
    (4 : ℝ) ^ m * (alpha m - δ) + (1 - alpha m) ≤ 2 ^ q := by
  have hbin : BinaryAnswers (fun θ : Str (2 * m) => fun u => mass (muθ m θ) u) := by
    intro u
    refine ⟨(1 - alpha m) * mass (unif (3 * m + 2)) u,
      (1 - alpha m) * mass (unif (3 * m + 2)) u + alpha m, fun θ => ?_⟩
    simp only [muθ, mass_mixD]
    split_ifs
    · right; ring
    · left; ring
  have hbound := sampling_binary_bound _ hbin (muθ m) (isDist_muθ m)
    (keyEvent m) (keyEvent_overlap m) A q δ
    (fun θ => hA (muθ m θ) ⟨θ, rfl⟩ _ (pwLegal_exact (isDist_muθ m θ) (by norm_num)))
  simp only [sum_keyEvent, Finset.sum_const, Finset.card_univ, card_keys, nsmul_eq_mul] at hbound
  push_cast at hbound
  have h2 : alpha m ^ 2 * (4 : ℝ) ^ m = 1 := by rw [alpha_sq]; field_simp
  rw [show (4 : ℝ) ^ m * ((1 - alpha m) * alpha m ^ 2 + alpha m - δ) =
    (1 - alpha m) * (alpha m ^ 2 * 4 ^ m) + alpha m * 4 ^ m - δ * 4 ^ m by ring, h2] at hbound
  linarith

/-! ### The safe search -/

/-- A fresh draw from `U_n`. -/
noncomputable def drawUnif (n : ℕ) : Alg (Str n) :=
  Alg.sample (PMF.uniformOfFintype (Str n)) Alg.ret

theorem lawR_drawUnif (n : ℕ) (h : Guide) : lawR ((drawUnif n).run h) = unif n := by
  funext x
  simp only [drawUnif, Alg.run_sample, Alg.run_ret, PMF.bind_pure, lawR,
    PMF.uniformOfFintype_apply, unif]
  simp

theorem within_drawUnif (n : ℕ) (h : Guide) : (drawUnif n).Within h 0 :=
  Alg.Within.sample _ _ _ fun g _ => Alg.Within.ret g 0

/-- The search sampler: test `q` uniformly chosen distinct keys at their complete strings `x_κ`;
on a hit output that string, otherwise output a fresh draw from `U_n`. -/
noncomputable def searchSampler (m q : ℕ) (hq : q ≤ 4 ^ m) : Alg (Str (3 * m + 2)) :=
  searchAlg q (by rw [card_keys]; exact hq) (fun κ => List.ofFn (xθ m κ))
    (fun _ r => (1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹ < r) (fun κ => Alg.ret (xθ m κ))
    (fun _ => drawUnif (3 * m + 2))

theorem leaf_test {θ : Str (2 * m)} {h : Guide}
    (hleaf : ∀ x : Str (3 * m + 2), h (List.ofFn x) = muθ m θ x) (κ : Str (2 * m)) :
    ((1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹ < h (List.ofFn (xθ m κ))) ↔ κ = θ := by
  rw [hleaf, muθ, mixD]
  have ha := alpha_pos m
  by_cases hk : κ = θ
  · subst hk; simp [dirac, unif, ha]
  · have : xθ m κ ≠ xθ m θ := fun e => hk (xθ_injective m e)
    simp [dirac, this, hk, unif]

/-- `eq:search-law`: for every guide with exact leaves (in particular every guide satisfying
`eq:oracle`), the output law of the search sampler is `(1 - q/M) U_n + (q/M) δ_{x_θ}`. -/
theorem search_law (q : ℕ) (hq : q ≤ 4 ^ m) (θ : Str (2 * m)) (h : Guide)
    (hleaf : ∀ x : Str (3 * m + 2), h (List.ofFn x) = muθ m θ x) :
    lawR ((searchSampler m q hq).run h) =
      mixD (unif (3 * m + 2)) ((q : ℝ) / 4 ^ m) (xθ m θ) := by
  unfold searchSampler
  rw [lawR_searchAlg q _ _ _ _ _ h θ (leaf_test hleaf) (xθ m θ) rfl _
    (lawR_drawUnif _ h), card_keys]
  push_cast
  rfl

theorem within_searchSampler (q : ℕ) (hq : q ≤ 4 ^ m) (h : Guide) :
    (searchSampler m q hq).Within h q :=
  within_searchAlg q _ _ _ _ _ h 0 (fun _ => Alg.Within.ret _ 0)
    (fun _ => within_drawUnif _ h)

theorem tv_search (q : ℕ) (θ : Str (2 * m)) :
    tv (mixD (unif (3 * m + 2)) ((q : ℝ) / 4 ^ m) (xθ m θ)) (muθ m θ) =
      |(q : ℝ) / 4 ^ m - alpha m| * (1 - ((2 : ℝ) ^ (3 * m + 2))⁻¹) := by
  rw [muθ, tv_mixD, tv_unif_dirac]

theorem searchSampler_solves (q : ℕ) (hq : q ≤ 4 ^ m) (δ : ℝ)
    (hδ : |(q : ℝ) / 4 ^ m - alpha m| ≤ δ) :
    Solves (SafeLegal (9 / 4) (9 / 4)) (Fm m) δ q (searchSampler m q hq) := by
  rintro μ ⟨θ, rfl⟩ h hl
  refine ⟨within_searchSampler q hq h, ?_⟩
  rw [search_law q hq θ h hl.1.leaf, tv_search q θ]
  have h1 : 0 ≤ 1 - ((2 : ℝ) ^ (3 * m + 2))⁻¹ :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have h2 : 1 - ((2 : ℝ) ^ (3 * m + 2))⁻¹ ≤ 1 := by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ (3 * m + 2))⁻¹ := by positivity
    linarith
  calc |(q : ℝ) / 4 ^ m - alpha m| * (1 - ((2 : ℝ) ^ (3 * m + 2))⁻¹)
      ≤ |(q : ℝ) / 4 ^ m - alpha m| * 1 := by gcongr
    _ ≤ δ := by rw [mul_one]; exact hδ

theorem three_quarters (hm : 3 ≤ m) :
    ((3 * 2 ^ (m - 2) : ℕ) : ℝ) / 4 ^ m = 3 / 4 * alpha m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  rw [show r + 2 - 2 = r by omega]
  unfold alpha
  rw [four_pow]
  push_cast
  field_simp
  ring

theorem two_pow_div (m : ℕ) : ((2 ^ m : ℕ) : ℝ) / 4 ^ m = alpha m := by
  unfold alpha; rw [four_pow]; push_cast; field_simp

/-! ### The eight-group pointwise sampler -/

/-- The group of a key: its first `m + 3` bits. -/
def grpOf (m : ℕ) (θ : Str (2 * m)) : Str (m + 3) :=
  fun i => if h : i.1 < 2 * m then θ ⟨i.1, h⟩ else false

/-- The completion `w 0^{m+2}` of a key word. -/
def complete (m : ℕ) (w : List Bool) : Str (3 * m + 2) :=
  fun i => if i.1 < 2 * m then w.getD i.1 false else false

theorem complete_eq {θ : Str (2 * m)} {w : List Bool} (hw : IsPre w (xθ m θ))
    (hl : w.length = 2 * m) : complete m w = xθ m θ := by
  rw [isPre_iff_getElem] at hw
  obtain ⟨_, hw⟩ := hw
  funext i
  unfold complete
  by_cases hi : i.1 < 2 * m
  · rw [ite_eq_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some, hw i.1 (by omega)]
  · simp [hi, xθ]

/-- `sec:pointwise` (threshold `α/3`): the test at key prefixes of depth between `m + 3` and `k`:
for every pointwise factor-`9/4` guide, `h(u) > α/3` exactly when `u ⪯ x_θ`. -/
theorem key_test (hm : 3 ≤ m) {θ : Str (2 * m)} {h : Guide}
    (hl : PwLegal (9 / 4) (muθ m θ) h) {u : List Bool} (hu1 : m + 3 ≤ u.length)
    (hu2 : u.length ≤ 2 * m) : alpha m / 3 < h u ↔ IsPre u (xθ m θ) := by
  have hb := hl.2 u (by omega)
  have ha := alpha_pos m
  have ha8 := alpha_le_eighth hm
  have hp := pp_le_alpha_eighth (m := m) hu1
  have hp0 : (0 : ℝ) ≤ ((2 : ℝ) ^ u.length)⁻¹ := by positivity
  rw [mass_muθ m θ (by omega)] at hb
  constructor
  · intro h3
    by_contra hp'
    rw [ite_eq_right hp'] at hb
    nlinarith [hb.2]
  · intro hp'
    rw [ite_eq_left hp'] at hb
    nlinarith [hb.1]

theorem isPre_grp (hm : 3 ≤ m) (θ : Str (2 * m)) (g : Str (m + 3)) :
    IsPre (List.ofFn g) (xθ m θ) ↔ g = grpOf m θ := by
  rw [isPre_iff_getElem]
  constructor
  · rintro ⟨_, h⟩
    funext i
    have := h i.1 (by rw [List.length_ofFn]; exact i.2)
    rw [List.getElem_ofFn] at this
    rw [this]
    rfl
  · rintro rfl
    refine ⟨by simp; omega, fun i hi => ?_⟩
    rw [List.getElem_ofFn]
    rfl

open Classical in
/-- Recover the remaining key bits one at a time: query the zero child and keep it when its value
exceeds `α/3`. -/
noncomputable def descend (m : ℕ) : ℕ → List Bool → Alg (Str (3 * m + 2))
  | 0, w => Alg.ret (complete m w)
  | s + 1, w => Alg.query (w ++ [false]) (fun r =>
      if alpha m / 3 < r then descend m s (w ++ [false]) else descend m s (w ++ [true]))

theorem within_descend (m : ℕ) (h : Guide) : ∀ s w, (descend m s w).Within h s := by
  intro s
  induction s with
  | zero => intro w; exact Alg.Within.ret _ 0
  | succ s ih =>
      intro w
      refine Alg.Within.query _ _ _ ?_
      split_ifs
      · exact ih _
      · exact ih _

theorem run_descend (hm : 3 ≤ m) {θ : Str (2 * m)} {h : Guide}
    (hl : PwLegal (9 / 4) (muθ m θ) h) :
    ∀ s w, IsPre w (xθ m θ) → m + 3 ≤ w.length → w.length + s = 2 * m →
      (descend m s w).run h = PMF.pure (xθ m θ) := by
  intro s
  induction s with
  | zero =>
      intro w hw _ hl'
      simp only [descend, Alg.run_ret]
      rw [complete_eq hw (by omega)]
  | succ s ih =>
      intro w hw h1 h2
      simp only [descend, Alg.run_query]
      have hlen : (w ++ [false]).length = w.length + 1 := by simp
      by_cases hf : IsPre (w ++ [false]) (xθ m θ)
      · rw [ite_eq_left ((key_test hm hl (by omega) (by omega)).mpr hf)]
        exact ih _ hf (by simp; omega) (by simp; omega)
      · rw [ite_eq_right (fun h' => hf ((key_test hm hl (by omega) (by omega)).mp h'))]
        have ht : IsPre (w ++ [true]) (xθ m θ) := by
          rw [isPre_append_singleton] at hf ⊢
          refine ⟨hw, ?_⟩
          have hlt : w.length < (List.ofFn (xθ m θ)).length := by simp; omega
          rw [List.getElem?_eq_getElem hlt] at hf ⊢
          simp only [Option.some.injEq] at hf ⊢
          cases hb : (List.ofFn (xθ m θ))[w.length] with
          | false => exact absurd ⟨hw, hb⟩ hf
          | true => rfl
        exact ih _ ht (by simp; omega) (by simp; omega)

theorem card_groups (m : ℕ) : 8 ≤ Fintype.card (Str (m + 3)) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_add]
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

/-- The eight-group sampler: partition `{0,1}^n` by the first `d = m + 3` bits into `2^d = 8/α`
groups, choose eight distinct groups uniformly and query their prefixes; on a hit recover the
remaining `m - 3` key bits one at a time and output `x_θ`, otherwise output a fresh draw from
`U_n`. -/
noncomputable def eightSampler (m : ℕ) : Alg (Str (3 * m + 2)) :=
  searchAlg 8 (card_groups m) (fun g : Str (m + 3) => List.ofFn g) (fun _ r => alpha m / 3 < r)
    (fun g => descend m (m - 3) (List.ofFn g)) (fun _ => drawUnif (3 * m + 2))

theorem within_eightSampler (hm : 3 ≤ m) (h : Guide) : (eightSampler m).Within h (m + 5) := by
  have := within_searchAlg 8 (card_groups m) (fun g : Str (m + 3) => List.ofFn g)
    (fun _ r => alpha m / 3 < r) (fun g => descend m (m - 3) (List.ofFn g))
    (fun _ => drawUnif (3 * m + 2)) h (m - 3) (fun g => within_descend m h _ _)
    (fun _ => (within_drawUnif _ h).mono (Nat.zero_le _))
  rwa [show 8 + (m - 3) = m + 5 by omega] at this

/-- `sec:pointwise`, `thm:main`: the eight-group sampler is exact for every pointwise factor-`9/4`
guide: its unconditional output law is `(1-α) U_n + α δ_{x_θ} = μ_θ`. -/
theorem lawR_eightSampler (hm : 3 ≤ m) {θ : Str (2 * m)} {h : Guide}
    (hl : PwLegal (9 / 4) (muθ m θ) h) : lawR ((eightSampler m).run h) = muθ m θ := by
  have htest : ∀ g : Str (m + 3), (alpha m / 3 < h (List.ofFn g)) ↔ g = grpOf m θ := by
    intro g
    rw [key_test hm hl (by simp) (by simp; omega), isPre_grp hm]
  have hhit : (descend m (m - 3) (List.ofFn (grpOf m θ))).run h = PMF.pure (xθ m θ) :=
    run_descend hm hl _ _ ((isPre_grp hm θ _).mpr rfl) (by simp) (by simp; omega)
  unfold eightSampler
  rw [lawR_searchAlg 8 _ _ _ _ _ h (grpOf m θ) htest (xθ m θ) hhit _ (lawR_drawUnif _ h), muθ]
  congr 1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  unfold alpha
  push_cast
  rw [pow_add]
  field_simp
  norm_num

theorem eightSampler_solves (hm : 3 ≤ m) :
    Solves (PwLegal (9 / 4)) (Fm m) 0 (m + 5) (eightSampler m) := by
  rintro μ ⟨θ, rfl⟩ h hl
  exact ⟨within_eightSampler hm h, by rw [lawR_eightSampler hm hl, tv_self]⟩

theorem Fm_dist (m : ℕ) : ∀ μ ∈ Fm m, IsDist μ := by
  rintro μ ⟨θ, rfl⟩; exact isDist_muθ m θ

theorem deltaM_nonneg (m : ℕ) : 0 ≤ deltaM m := by unfold deltaM; linarith [alpha_pos m]

/-- `thm:main`, equation `eq:point-exact`: `m ≤ Q_pw(F_m,δ_m) ≤ Q_pw(F_m,0) ≤ m+5`. -/
theorem point_exact (hm : 3 ≤ m) :
    m ≤ Qpw (Fm m) (deltaM m) ∧ Qpw (Fm m) (deltaM m) ≤ Qpw (Fm m) 0 ∧
      Qpw (Fm m) 0 ≤ m + 5 := by
  refine ⟨?_, Qpw_anti (Fm_dist m) le_rfl (deltaM_nonneg m), Qcx_le (eightSampler_solves hm)⟩
  refine le_Qcx ⟨_, _, solves_mono_delta (eightSampler_solves hm) (deltaM_nonneg m)⟩
    fun q A hA => ?_
  have hb := binary_lower (deltaM m) q A hA
  unfold deltaM at hb
  have h1 := alpha_mul_M m
  have ha1 := alpha_lt_one (m := m) (by omega)
  have h34 : 3 / 4 * (2 : ℝ) ^ m < 2 ^ q := by nlinarith
  by_contra hq
  push Not at hq
  have : (2 : ℝ) ^ q ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have e : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (0 : ℝ) < 2 ^ (m - 1) := by positivity
  nlinarith

/-- `thm:main`: in the exact case even `q ≥ m + 1` for every pointwise sampler. -/
theorem point_exact_zero (hm : 3 ≤ m) : m + 1 ≤ Qpw (Fm m) 0 := by
  refine le_Qcx ⟨_, _, eightSampler_solves hm⟩ fun q A hA => ?_
  have hb := binary_lower 0 q A hA
  have h1 := alpha_mul_M m
  have ha1 := alpha_lt_one (m := m) (by omega)
  have h34 : (2 : ℝ) ^ m < 2 ^ q := by nlinarith
  have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h34
  omega

/-- `thm:main`, equation `eq:safe-exact`: `Q_safe(F_m,δ_m) = 3·2^{m-2}` and
`Q_safe(F_m,0) = 2^m`. The upper bounds hold for every legal guide; the lower bounds use the hard
guides. -/
theorem safe_exact (hm : 3 ≤ m) :
    Qsafe (Fm m) (deltaM m) = 3 * 2 ^ (m - 2) ∧ Qsafe (Fm m) 0 = 2 ^ m := by
  have hM : (3 * 2 ^ (m - 2) : ℕ) ≤ 4 ^ m := by
    have : 2 ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
    have : 4 * 2 ^ (m - 2) = 2 ^ m := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    omega
  have hM' : 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
  have h1 := alpha_mul_M m
  have ha0 := alpha_pos m
  have ha1 := alpha_lt_one (m := m) (by omega)
  constructor
  · refine Qcx_eq (searchSampler_solves _ hM _ ?_) fun q A hA => ?_
    · rw [three_quarters hm, deltaM, show 3 / 4 * alpha m - alpha m = -(alpha m / 4) by ring,
        abs_neg, abs_of_pos (by positivity)]
    · have hs := search_lower (deltaM m) q A hm hA
      unfold deltaM at hs
      have e : (3 * 2 ^ (m - 2) : ℕ) = (3 / 4 : ℝ) * 2 ^ m := by
        have : (2 : ℝ) ^ m = 4 * 2 ^ (m - 2) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
        push_cast; rw [this]; ring
      have : ((3 * 2 ^ (m - 2) : ℕ) : ℝ) < q + 1 := by rw [e]; nlinarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · refine Qcx_eq (searchSampler_solves _ hM' _ ?_) fun q A hA => ?_
    · rw [two_pow_div, sub_self, abs_zero]
    · have hs := search_lower 0 q A hm hA
      have : ((2 ^ m : ℕ) : ℝ) < q + 1 := by push_cast; nlinarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

end Sec4
end LearningGuided
