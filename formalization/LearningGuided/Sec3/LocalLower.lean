import LearningGuided.Sec3.LocalUpper
import LearningGuided.Sec3.PublicGuide
import LearningGuided.Sec3.RealAux

/-!
# Matching lower bounds for `𝓕_{n,k,α}` and Theorem `thm:local-rate`

* `spike_information` (`eq:local-information`): with the exact guide every prefix has at most two
  answers, so `2^q ≥ (α-δ)M + a`;
* `spike_zero_query`: zero queries are impossible for `δ ≤ α/4`;
* `hardSpike_capacity` (`eq:local-hard-capacity`): the restricted hard guide, public through
  depth `s` and exact below, has stopped capacity exactly
  `1 + α - 2α² - aα/H + α²H ≤ 17/8`;
* `spike_search` and `spike_search_min` (`eq:local-search`);
* `local_lower` (the combination, with the constant `9`), `local_upper_rate` and `local_rate`
  (Theorem `thm:local-rate`).
-/

open scoped BigOperators ENNReal

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### The information bound -/

theorem mass_spike_key {k : ℕ} (hk : k ≤ n) (α : ℝ) (θ : Str k) :
    mass (atomTarget (unif n) α (spikeAtom n θ)) (List.ofFn θ) = (1 - α) * ((2 : ℝ) ^ k)⁻¹ + α := by
  rw [mass_atomTarget, mass_unif (by simp [hk]), ite_eq_left (isPre_spikeAtom hk θ),
    List.length_ofFn, mul_one]

/-- With exact guides each prefix has at most two answers as the key varies. -/
theorem binaryAnswers_exact_spike (n k : ℕ) (α : ℝ) :
    BinaryAnswers fun θ : Str k => exactGuide (atomTarget (unif n) α (spikeAtom n θ)) := by
  intro u
  refine ⟨(1 - α) * mass (unif n) u, (1 - α) * mass (unif n) u + α, fun θ => ?_⟩
  simp only [exactGuide, mass_atomTarget]
  split_ifs <;> simp

/-- The event that the output extends the key `θ`. -/
noncomputable def keyEvent (n : ℕ) {k : ℕ} (θ : Str k) : Finset (Str n) :=
  Finset.univ.filter (IsPre (List.ofFn θ))

theorem keyEvent_overlap {k : ℕ} (S : Finset (Str k)) (y : Str n) :
    (S.filter fun θ : Str k => y ∈ (keyEvent n θ : Set (Str n))).card ≤ 1 := by
  simp only [Finset.mem_coe]
  exact card_filter_isPre_ofFn_le_one S y

theorem keyEvent_prob {k : ℕ} (hk : k ≤ n) {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (θ : Str k)
    {p : PMF (Str n)} (hp : tv (lawR p) (atomTarget (unif n) α (spikeAtom n θ)) ≤ δ) :
    (1 - α) * ((2 : ℝ) ^ k)⁻¹ + α - δ ≤ (probE p (keyEvent n θ : Set (Str n))).toReal := by
  have := prob_ge_of_tv (isDist_atomTarget (isDist_unif n) hα0 hα1 _) hp (keyEvent n θ)
  rwa [keyEvent, ← mass_eq_sum_filter, mass_spike_key hk] at this

/-- `eq:local-information`, in exponential form: in any model in which the exact guide is legal,
an algorithm with cap `q` that is `δ`-accurate on `𝓕_{n,k,α}` has `2^q ≥ (α-δ)M + a`. -/
theorem spike_information {Legal : (Str n → ℝ) → Guide → Prop} {α δ : ℝ} {k : ℕ} (hk : k ≤ n)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hex : ∀ θ : Str k, Legal (atomTarget (unif n) α (spikeAtom n θ))
      (exactGuide (atomTarget (unif n) α (spikeAtom n θ))))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (spikeClass n k α) δ q A) :
    (α - δ) * 2 ^ k + (1 - α) ≤ 2 ^ q := by
  have hsum := binary_counting (fun θ : Str k => exactGuide (atomTarget (unif n) α
    (spikeAtom n θ))) (binaryAnswers_exact_spike n k α) (fun θ => (keyEvent n θ : Set (Str n)))
    1 A Finset.univ q (fun y => by convert keyEvent_overlap (n := n) Finset.univ y)
    (fun θ _ => (hA _ ⟨θ, rfl⟩ _ (hex θ)).1)
  have h := card_mul_le_of_sum Finset.univ _ (by simp) (fun θ => probE_le_one _ _) hsum
    (fun θ _ => keyEvent_prob hk hα0 hα1 θ (hA _ ⟨θ, rfl⟩ _ (hex θ)).2)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have h2 : ((2 : ℝ≥0∞) ^ q * ((1 : ℕ) : ℝ≥0∞)).toReal = 2 ^ q := by simp
  rw [h2] at h
  push_cast at h
  have : (2 : ℝ) ^ k * ((1 - α) * ((2 : ℝ) ^ k)⁻¹ + α - δ) = (α - δ) * 2 ^ k + (1 - α) := by
    field_simp
    ring
  linarith

/-- `eq:local-information`: `q ≥ log₂((α-δ)M + a)` in the safe model (`R = C = 9/4`). -/
theorem local_information {α δ : ℝ} {k : ℕ} (hk : k ≤ n) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hδα : δ ≤ α) {q : ℕ} {A : Alg (Str n)}
    (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A) :
    Real.logb 2 ((α - δ) * 2 ^ k + (1 - α)) ≤ q := by
  have h := spike_information hk hα0 hα1.le (fun θ => safeLegal_exactGuide (by norm_num)
    (by norm_num) (isDist_atomTarget (isDist_unif n) hα0 hα1.le _)) hA
  have hpos : 0 < (α - δ) * 2 ^ k + (1 - α) := by
    have : 0 ≤ (α - δ) * (2 : ℝ) ^ k := mul_nonneg (by linarith) (by positivity)
    linarith
  rw [Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast]
  exact h

/-! ### The zero-query obstruction -/

/-- `thm:local-rate`, zero-query obstruction: two distinct targets of `𝓕_{n,k,α}` (`k ≥ 1`) are at
distance `α > 2δ`, so no algorithm without queries is `δ`-accurate for `δ < α/2`. -/
theorem spike_zero_query {Legal : (Str n → ℝ) → Guide → Prop} {α δ : ℝ} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ n) (hα0 : 0 ≤ α) (hδ : 2 * δ < α)
    (hex : ∀ θ : Str k, Legal (atomTarget (unif n) α (spikeAtom n θ))
      (exactGuide (atomTarget (unif n) α (spikeAtom n θ))))
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal (spikeClass n k α) δ q A) : 1 ≤ q := by
  by_contra hq
  have hq0 : q = 0 := by omega
  subst hq0
  set θ₁ : Str k := fun _ => false
  set θ₂ : Str k := fun i => decide (i.val = 0)
  have hne : θ₁ ≠ θ₂ := by
    intro he
    have := congrFun he ⟨0, hk1⟩
    simp [θ₁, θ₂] at this
  have hxne : spikeAtom n θ₁ ≠ spikeAtom n θ₂ := fun he => hne (spikeAtom_injective hk he)
  have h1 := hA _ ⟨θ₁, rfl⟩ _ (hex θ₁)
  have h2 := hA _ ⟨θ₂, rfl⟩ _ (hex θ₂)
  exact zero_query_obstruction (by rw [tv_atomTarget hα0 hxne]; exact hδ) A h1.1 h2.1 h1.2 h2.2

/-! ### The restricted hard guide -/

/-- The restricted hard guide for the coarse key `ϑ ∈ {0,1}^s`: `2^{-|u|}` through depth `s`,
exact target masses below. -/
noncomputable def hardSpike (n s : ℕ) (α : ℝ) (ϑ : Str s) : Guide :=
  pubGuide (unif n) α (spikeAtom n ϑ) fun u => u.length ≤ s

theorem hardSpike_public {s : ℕ} (hs : s ≤ n) (α : ℝ) (ϑ : Str s) {u : List Bool}
    (hu : u.length ≤ s) : hardSpike n s α ϑ u = ((2 : ℝ) ^ u.length)⁻¹ := by
  rw [hardSpike, pubGuide_pub hu, mass_unif (hu.trans hs)]

/-- The path value at depth `t ≤ s`: `a + 2aα - aα2^{-t} + α²2^t`. -/
theorem hardSpike_pathValue {s : ℕ} (hs : s < n) (α : ℝ) (ϑ : Str s) {t : ℕ} (ht : t ≤ s) :
    1 - mass (atomTarget (unif n) α (spikeAtom n ϑ)) (pre (spikeAtom n ϑ) t) +
      mass (atomTarget (unif n) α (spikeAtom n ϑ)) (pre (spikeAtom n ϑ) t) ^ 2 /
        hardSpike n s α ϑ (pre (spikeAtom n ϑ) t) =
      1 + α - 2 * α ^ 2 - (1 - α) * α * ((2 : ℝ) ^ t)⁻¹ + α ^ 2 * 2 ^ t := by
  have htn : t ≤ n := by omega
  have hlen : (pre (spikeAtom n ϑ) t).length = t := length_pre _ htn
  have hl : (pre (spikeAtom n ϑ) t).length ≤ s := by rw [hlen]; exact ht
  have hm : mass (unif n) (pre (spikeAtom n ϑ) t) = ((2 : ℝ) ^ t)⁻¹ := by
    rw [mass_unif (by rw [hlen]; exact htn), hlen]
  have hpos : 0 < mass (unif n) (pre (spikeAtom n ϑ) t) := by rw [hm]; positivity
  rw [hardSpike, pubGuide_pathValue (Pub := fun u => u.length ≤ s) hl (isPre_pre _ t) hpos, hm,
    div_inv_eq_mul]

/-- The path values increase with the depth `t ≤ s`. -/
theorem hardSpike_path_mono {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {s t : ℕ} (ht : t ≤ s) :
    1 + α - 2 * α ^ 2 - (1 - α) * α * ((2 : ℝ) ^ t)⁻¹ + α ^ 2 * 2 ^ t ≤
      1 + α - 2 * α ^ 2 - (1 - α) * α * ((2 : ℝ) ^ s)⁻¹ + α ^ 2 * 2 ^ s := by
  have h1 : (2 : ℝ) ^ t ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) ht
  have h2 : ((2 : ℝ) ^ s)⁻¹ ≤ ((2 : ℝ) ^ t)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : 0 ≤ (1 - α) * α := mul_nonneg (by linarith) hα0
  nlinarith [sq_nonneg α]

/-- `eq:local-hard-capacity`: the restricted hard guide is legal in the safe model with factor
`4/3`, and its stopped capacity is exactly `1 + α - 2α² - aα/H + α²H` with `H = 2^s`; when
`α²H ≤ 1` this is at most `17/8 < 9/4`. -/
theorem hardSpike_capacity {s : ℕ} (hs : s < n) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (ϑ : Str s) :
    IsOracle (atomTarget (unif n) α (spikeAtom n ϑ)) (hardSpike n s α ϑ) ∧
    (∀ u, hardSpike n s α ϑ u ≤ 4 / 3 * mass (atomTarget (unif n) α (spikeAtom n ϑ)) u) ∧
    CapEq (atomTarget (unif n) α (spikeAtom n ϑ)) (hardSpike n s α ϑ)
      (1 + α - 2 * α ^ 2 - (1 - α) * α / 2 ^ s + α ^ 2 * 2 ^ s) ∧
    (α ^ 2 * 2 ^ s ≤ 1 →
      1 + α - 2 * α ^ 2 - (1 - α) * α / 2 ^ s + α ^ 2 * 2 ^ s ≤ 17 / 8) := by
  have hν := isDist_unif n
  have hμ := isDist_atomTarget hν hα0.le (by linarith) (spikeAtom n ϑ)
  have hF : 1 + α - 2 * α ^ 2 - (1 - α) * α / 2 ^ s + α ^ 2 * 2 ^ s =
      1 + α - 2 * α ^ 2 - (1 - α) * α * ((2 : ℝ) ^ s)⁻¹ + α ^ 2 * 2 ^ s := by
    rw [div_eq_mul_inv]
  have hF1 : 1 ≤ 1 + α - 2 * α ^ 2 - (1 - α) * α * ((2 : ℝ) ^ s)⁻¹ + α ^ 2 * 2 ^ s := by
    have := hardSpike_path_mono hα0.le (by linarith) (Nat.zero_le s)
    simp only [pow_zero, inv_one, mul_one] at this
    nlinarith
  refine ⟨pubGuide_isOracle hν hα0.le (by linarith) _ (fun u hu => by
      change u.length ≤ s at hu; omega),
    fun u => pubGuide_le hν hα0.le hα _ _ u, ⟨?_, ?_⟩, ?_⟩
  · rw [hF]
    refine pubGuide_capLE hν (fun _ => by unfold unif; positivity) hα0.le (by linarith) _ hF1
      (fun t ht hp => ?_)
    change (pre (spikeAtom n ϑ) t).length ≤ s at hp
    rw [length_pre _ ht] at hp
    rw [mass_unif (by rw [length_pre _ ht]; exact ht), length_pre _ ht, div_inv_eq_mul]
    exact hardSpike_path_mono hα0.le (by linarith) hp
  · obtain ⟨A, hA, hval⟩ := exists_path_cut hμ (pubGuide_isOracle hν hα0.le (by linarith) _
      (fun u hu => by change u.length ≤ s at hu; omega)).leaf (spikeAtom n ϑ) hs.le
    refine ⟨A, hA, ?_⟩
    unfold hardSpike
    rw [hval, hF]
    exact hardSpike_pathValue hs α ϑ le_rfl
  · intro hH
    have : 0 ≤ (1 - α) * α / 2 ^ s := by
      have : 0 ≤ (1 - α) * α := mul_nonneg (by linarith) hα0.le
      positivity
    nlinarith

/-! ### The search obstruction -/

/-- The key `ϑ0^{k-s}` of length `k`. -/
def padKey (k : ℕ) {s : ℕ} (ϑ : Str s) : Str k := strOf k (List.ofFn ϑ)

theorem spikeAtom_padKey {k s : ℕ} (hsk : s ≤ k) (ϑ : Str s) :
    spikeAtom n (padKey k ϑ) = spikeAtom n ϑ := by
  funext i
  rw [spikeAtom_apply, spikeAtom_apply]
  unfold padKey
  by_cases hk : i.val < k
  · rw [dite_eq_left hk]
    have := spikeAtom_apply (n := k) ϑ ⟨i.val, hk⟩
    exact this
  · rw [dite_eq_right hk, dite_eq_right (by omega)]

theorem isPre_getElem {u : List Bool} {x : Str n} (hu : IsPre u x) {i : ℕ} (hi : i < u.length) :
    u[i] = x ⟨i, by have := hu.length_le; omega⟩ := by
  have := (List.prefix_iff_getElem?.mp hu) i hi
  have hin : i < n := by have := hu.length_le; omega
  simp [hin] at this
  exact this.symm

/-- Every query longer than `s` names at most one coarse key. -/
theorem eqStructure_hardSpike (n : ℕ) {s : ℕ} (α : ℝ) :
    EqualityStructure fun ϑ : Str s => hardSpike n s α ϑ := by
  refine eqStructure_pub (unif n) α (fun ϑ : Str s => spikeAtom n ϑ) _ ?_
  intro u hu ϑ ϑ' h1 h2
  change ¬ u.length ≤ s at hu
  funext i
  have e1 := isPre_getElem h1 (i := i.val) (by omega)
  have e2 := isPre_getElem h2 (i := i.val) (by omega)
  have hi : i.val < s := i.2
  rw [e1, spikeAtom_apply, dite_eq_left hi] at e2
  rw [spikeAtom_apply, dite_eq_left hi] at e2
  exact e2

/-- `eq:local-search` (first inequality): for `s < k` with `α²2^s ≤ 1`, a `δ`-accurate algorithm
for `𝓕_{n,k,α}` in the safe model has `q ≥ (α-δ)2^s - α`. -/
theorem spike_search {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) {k s : ℕ} (hsk : s < k)
    (hk : k ≤ n) (hH : α ^ 2 * 2 ^ s ≤ 1) {q : ℕ} {A : Alg (Str n)}
    (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A) :
    (α - δ) * 2 ^ s - α ≤ q := by
  have hsn : s < n := by omega
  have hmem : ∀ ϑ : Str s, atomTarget (unif n) α (spikeAtom n ϑ) ∈ spikeClass n k α :=
    fun ϑ => ⟨padKey k ϑ, by beta_reduce; rw [spikeAtom_padKey hsk.le]⟩
  have hlegal : ∀ ϑ : Str s, SafeLegal (9 / 4) (9 / 4) (atomTarget (unif n) α (spikeAtom n ϑ))
      (hardSpike n s α ϑ) := by
    intro ϑ
    obtain ⟨h1, h2, h3, h4⟩ := hardSpike_capacity hsn hα0 hα ϑ
    refine ⟨h1, fun u _ => (h2 u).trans ?_, CapLE.mono h3.1 ((h4 hH).trans (by norm_num))⟩
    have := mass_nonneg (isDist_atomTarget (isDist_unif n) hα0.le (by linarith)
      (spikeAtom n ϑ)).1 u
    linarith
  have hsum := equality_counting (fun ϑ : Str s => hardSpike n s α ϑ)
    (eqStructure_hardSpike n α) (fun ϑ => (keyEvent n ϑ : Set (Str n))) 1 A Finset.univ q
    (fun y => by convert keyEvent_overlap (n := n) Finset.univ y)
    (fun ϑ _ => (hA _ (hmem ϑ) _ (hlegal ϑ)).1)
  have h := card_mul_le_of_sum Finset.univ _ (by simp) (fun θ => probE_le_one _ _) hsum
    (fun ϑ _ => keyEvent_prob hsn.le hα0.le (by linarith) ϑ (hA _ (hmem ϑ) _ (hlegal ϑ)).2)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have h2 : ((q : ℝ≥0∞) + ((1 : ℕ) : ℝ≥0∞)).toReal = q + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [h2] at h
  push_cast at h
  have : (2 : ℝ) ^ s * ((1 - α) * ((2 : ℝ) ^ s)⁻¹ + α - δ) = (α - δ) * 2 ^ s + (1 - α) := by
    field_simp
    ring
  linarith

/-- The coarse depth `s = min{k-1, ⌊log₂ α⁻²⌋}` of the search obstruction. -/
noncomputable def coarseDepth (k : ℕ) (α : ℝ) : ℕ := min (k - 1) ⌊Real.logb 2 (α ^ 2)⁻¹⌋₊

/-- `eq:local-search` (second inequality): with `s = min{k-1, ⌊log₂ α⁻²⌋}` and `δ ≤ α/4`,
`q ≥ (α-δ)2^s - α ≥ (3/8) min{αM, α⁻¹} - 1/4`. -/
theorem spike_search_min {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδα : δ ≤ α / 4) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ n) {q : ℕ} {A : Alg (Str n)}
    (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A) :
    (α - δ) * 2 ^ coarseDepth k α - α ≤ q ∧
      3 / 8 * min (α * 2 ^ k) α⁻¹ - 1 / 4 ≤ (α - δ) * 2 ^ coarseDepth k α - α := by
  have hy : 1 ≤ (α ^ 2)⁻¹ := by
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  obtain ⟨hf1, hf2⟩ := floor_logb_two_spec hy
  set L := ⌊Real.logb 2 (α ^ 2)⁻¹⌋₊ with hL
  have hs_le : (2 : ℝ) ^ coarseDepth k α ≤ 2 ^ L :=
    pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
  have hH : α ^ 2 * 2 ^ coarseDepth k α ≤ 1 := by
    have : α ^ 2 * (α ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have h0 : 0 ≤ α ^ 2 := by positivity
    nlinarith
  refine ⟨spike_search hα0 hα (by unfold coarseDepth; omega) hk hH hA, ?_⟩
  have hHge : min ((2 : ℝ) ^ k) (α ^ 2)⁻¹ / 2 ≤ 2 ^ coarseDepth k α := by
    unfold coarseDepth
    rcases le_total (k - 1) L with h | h
    · rw [min_eq_left h]
      have : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have := min_le_left ((2 : ℝ) ^ k) (α ^ 2)⁻¹
      linarith
    · rw [min_eq_right h]
      have : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ']
      have := min_le_right ((2 : ℝ) ^ k) (α ^ 2)⁻¹
      linarith
  have hmin : α * min ((2 : ℝ) ^ k) (α ^ 2)⁻¹ = min (α * 2 ^ k) α⁻¹ := by
    rw [mul_min_of_nonneg _ _ hα0.le]
    congr 1
    field_simp
  have h1 : 3 / 4 * α ≤ α - δ := by linarith
  have h2 : 0 ≤ min ((2 : ℝ) ^ k) (α ^ 2)⁻¹ := le_min (by positivity) (by positivity)
  have h3 : 3 / 8 * min (α * 2 ^ k) α⁻¹ ≤ (α - δ) * 2 ^ coarseDepth k α := by
    rw [← hmin]
    calc 3 / 8 * (α * min ((2 : ℝ) ^ k) (α ^ 2)⁻¹)
        = 3 / 4 * α * (min ((2 : ℝ) ^ k) (α ^ 2)⁻¹ / 2) := by ring
      _ ≤ (α - δ) * 2 ^ coarseDepth k α := by
          apply mul_le_mul h1 hHge (by positivity) (by linarith)
  linarith

/-! ### Theorem `thm:local-rate` -/

/-- `thm:local-rate`, lower bound with the constant `9`: every `δ`-accurate algorithm with
cap `q` on `𝓕_{n,k,α}` in the safe model has `1 + min{αM, α⁻¹ + log₂ M} ≤ 9q`. -/
theorem local_lower {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδα : δ ≤ α / 4)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) {q : ℕ} {A : Alg (Str n)}
    (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A) :
    1 + min (α * 2 ^ k) (α⁻¹ + Real.logb 2 (2 ^ k)) ≤ 9 * q := by
  have hex : ∀ θ : Str k, SafeLegal (9 / 4) (9 / 4) (atomTarget (unif n) α (spikeAtom n θ))
      (exactGuide (atomTarget (unif n) α (spikeAtom n θ))) := fun θ =>
    safeLegal_exactGuide (by norm_num) (by norm_num)
      (isDist_atomTarget (isDist_unif n) hα0.le (by linarith) _)
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast spike_zero_query hk1 hk hα0.le (by linarith) hex hA
  rw [logb_two_pow]
  set B := α⁻¹ with hB
  have hB4 : 4 ≤ B := by
    rw [hB, le_inv_comm₀ (by norm_num) hα0]
    linarith
  by_cases hk2 : k = 1
  · have h1 : min (α * 2 ^ k) (B + k) ≤ α * 2 ^ k := min_le_left _ _
    have h2 : α * (2 : ℝ) ^ k = 2 * α := by rw [hk2]; ring
    linarith
  have hk2' : 2 ≤ k := by omega
  -- the information bound gives `k ≤ q + log₂ B + 1`
  have hinfo := spike_information hk hα0.le (by linarith) hex hA
  have hpow : (2 : ℝ) ^ k ≤ 2 ^ (q + 1) * B := by
    have h1 : 3 / 4 * α * 2 ^ k ≤ 2 ^ q := by
      have : 0 ≤ 1 - α := by linarith
      have : 3 / 4 * α ≤ α - δ := by linarith
      have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
      nlinarith
    have hαB : α * B = 1 := mul_inv_cancel₀ hα0.ne'
    rw [pow_succ]
    have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
    have hq0 : (0 : ℝ) ≤ 2 ^ q := by positivity
    nlinarith
  have hkL : (k : ℝ) ≤ q + 1 + Real.logb 2 B := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpow
    rw [logb_two_pow, Real.logb_mul (by positivity) (by positivity), logb_two_pow] at this
    push_cast at this
    linarith
  have hLB := logb_two_le_half hB4
  obtain ⟨hs, hsearch⟩ := spike_search_min hα0 hα hδα hk1 hk hA
  have hAB : min (α * 2 ^ k) B ≤ 4 * q := by
    have : 3 / 8 * min (α * 2 ^ k) B - 1 / 4 ≤ q := hsearch.trans hs
    linarith
  rcases le_total (α * 2 ^ k) B with h | h
  · have : min (α * 2 ^ k) (B + k) ≤ α * 2 ^ k := min_le_left _ _
    rw [min_eq_left h] at hAB
    linarith
  · rw [min_eq_right h] at hAB
    have : min (α * 2 ^ k) (B + k) ≤ B + k := min_le_right _ _
    linarith

/-- `thm:local-rate`, upper bound for exact sampling: with the combined sampler at
`R = C = 9/4`, `Q_safe(𝓕_{n,k,α},δ) ≤ Q_safe(𝓕_{n,k,α},0)`-cap
`≤ (81/4)(1 + min{αM, α⁻¹ + log₂ M})` for every `δ ≥ 0`. -/
theorem local_upper_rate {α δ : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) (hδ0 : 0 ≤ δ) {k : ℕ}
    (hk : k ≤ n) :
    (Qsafe (spikeClass n k α) δ : ℝ) ≤ 81 / 4 * (1 + min (α * 2 ^ k) (α⁻¹ + Real.logb 2 (2 ^ k)))
    := by
  have hsolve := solves_mono_delta hδ0 (solves_spikeSampler (n := n) (by norm_num : (0 : ℝ) < 9 / 4)
    (by norm_num : (0 : ℝ) < 9 / 4) hα0 (by linarith) le_rfl hα0.le hk)
  have hQ : (Qsafe (spikeClass n k α) δ : ℝ) ≤ spikeCap k (resDepth (9 / 4) (9 / 4) α) (α - 0) :=
    by exact_mod_cast Qcx_le hsolve
  refine hQ.trans ?_
  rw [sub_zero, logb_two_pow]
  set d := resDepth (9 / 4) (9 / 4) α with hd
  set X : ℝ := 2 * (9 / 4) * (9 / 4) * (1 - α) / α ^ 2 with hX
  have hαX : α * X = 81 / 8 * ((1 - α) / α) := by
    rw [hX]
    field_simp
    ring
  have hB : (1 - α) / α ≤ α⁻¹ := by
    rw [div_le_iff₀ hα0, inv_mul_cancel₀ hα0.ne']
    linarith
  have hBpos : 0 < α⁻¹ := inv_pos.mpr hα0
  have hleaf : (⌈α * 2 ^ k⌉₊ : ℝ) ≤ α * 2 ^ k + 1 := ceil_le_add_one (by positivity)
  unfold spikeCap
  split_ifs with hdk
  · -- `d ≤ k`
    have hX1 : 1 ≤ 2 * X := by
      have : (1 : ℝ) / 2 ≤ X := by
        rw [hX, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have h2d : (2 : ℝ) ^ d ≤ 2 * X := two_pow_depthFor_le hX1
    have hgroup : (⌈α * 2 ^ d⌉₊ : ℝ) + ((k - d : ℕ) : ℝ) ≤ 81 / 4 * α⁻¹ + 1 + k := by
      have h1 := ceil_le_add_one (x := α * 2 ^ d) (by positivity)
      have h2 : α * 2 ^ d ≤ 81 / 4 * α⁻¹ := by
        calc α * 2 ^ d ≤ α * (2 * X) := mul_le_mul_of_nonneg_left h2d hα0.le
          _ = 2 * (α * X) := by ring
          _ ≤ 81 / 4 * α⁻¹ := by rw [hαX]; linarith
      have h3 : ((k - d : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k d
      linarith
    have hmin : ((min ⌈α * 2 ^ k⌉₊ (⌈α * 2 ^ d⌉₊ + (k - d)) : ℕ) : ℝ) ≤
        min (α * 2 ^ k + 1) (81 / 4 * α⁻¹ + 1 + k) := by
      push_cast
      exact min_le_min hleaf hgroup
    refine hmin.trans ?_
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rcases le_total (α * 2 ^ k) (α⁻¹ + k) with h | h
    · rw [min_eq_left h]
      have : α * 2 ^ k + 1 ≤ 81 / 4 * (1 + α * 2 ^ k) := by
        have : (0 : ℝ) ≤ α * 2 ^ k := by positivity
        linarith
      exact (min_le_left _ _).trans this
    · rw [min_eq_right h]
      have : 81 / 4 * α⁻¹ + 1 + k ≤ 81 / 4 * (1 + (α⁻¹ + k)) := by linarith
      exact (min_le_right _ _).trans this
  · -- `d > k`: then `2^k < X`
    have hkX : (2 : ℝ) ^ k < X := by
      by_contra hc
      exact hdk (depthFor_le (not_lt.mp hc))
    have hAM : α * 2 ^ k ≤ 81 / 8 * α⁻¹ := by
      have : α * 2 ^ k ≤ α * X := mul_le_mul_of_nonneg_left hkX.le hα0.le
      rw [hαX] at this
      linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA0 : (0 : ℝ) ≤ α * 2 ^ k := by positivity
    have : α * 2 ^ k ≤ 81 / 8 * min (α * 2 ^ k) (α⁻¹ + k) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 81 / 8)]
      exact le_min (by linarith) (by linarith)
    have hmin0 : 0 ≤ min (α * 2 ^ k) (α⁻¹ + k) := le_min hA0 (by positivity)
    linarith

/-- `thm:local-rate`: uniformly over `n ≥ k ≥ 1`, `0 < α ≤ 1/4`, `0 ≤ δ ≤ α/4`,
`Q_safe(𝓕_{n,k,α},δ) = Θ(1 + min{αM, α⁻¹ + log₂ M})`, `M = 2^k`, with the absolute constants
`c₁ = 1/9` and `c₂ = 81/4`. The upper bound holds for exact sampling. -/
theorem local_rate : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n k : ℕ) (α δ : ℝ), 1 ≤ k → k ≤ n → 0 < α → α ≤ 1 / 4 → 0 ≤ δ → δ ≤ α / 4 →
      c₁ * (1 + min (α * 2 ^ k) (α⁻¹ + Real.logb 2 (2 ^ k))) ≤ (Qsafe (spikeClass n k α) δ : ℝ) ∧
      (Qsafe (spikeClass n k α) δ : ℝ) ≤ c₂ * (1 + min (α * 2 ^ k) (α⁻¹ + Real.logb 2 (2 ^ k)))
    := by
  refine ⟨1 / 9, 81 / 4, by norm_num, by norm_num, fun n k α δ hk1 hk hα0 hα hδ0 hδα => ⟨?_,
    local_upper_rate hα0 hα hδ0 hk⟩⟩
  have hex : ∃ q A, Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A :=
    ⟨_, _, solves_spikeSampler (by norm_num) (by norm_num) hα0 (by linarith) hδ0 (by linarith) hk⟩
  have hlow : ∀ q A, Solves (SafeLegal (9 / 4) (9 / 4)) (spikeClass n k α) δ q A →
      ⌈1 / 9 * (1 + min (α * 2 ^ k) (α⁻¹ + Real.logb 2 (2 ^ k)))⌉₊ ≤ q := by
    intro q A hA
    rw [Nat.ceil_le]
    have := local_lower hα0 hα hδα hk1 hk hA
    linarith
  have := le_Qcx hex hlow
  exact (Nat.le_ceil _).trans (by exact_mod_cast this)

end LearningGuided.Sec3
