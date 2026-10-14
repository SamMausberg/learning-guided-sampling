import LearningGuided.Sec3.Common

/-!
# Local access from the guide itself: the class `𝓕_{n,k,α}` and its sampler

Section 3 of the paper (`local-access.tex`), upper bounds:

* `spikeClass n k α`: the class `𝓕_{n,k,α}` of `eq:spike-class`;
* `resDepth R C α`: the resolution depth `d` of `eq:resolution`;
* `groupSpike`: search `q = ⌈β2^d⌉` of the `2^d` depth-`d` groups with the test of
  Lemma `lem:local-test`, thin with the coin `β2^d/q`, recover the remaining `k-d` key bits by
  zero-child queries, and draw from `U_n` on every other branch;
* `spikeSampler`: the cheaper of `groupSpike` and exact-leaf search;
* `lawR_spikeSampler_safe` (`eq:local-output`), `within_spikeSampler`, and `local_cap`
  (`eq:local-cap`).
-/

open scoped BigOperators

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### The class -/

/-- The atom `θ0^{n-k}` of a key `θ ∈ {0,1}^k`. -/
def spikeAtom (n : ℕ) {k : ℕ} (θ : Str k) : Str n := strOf n (List.ofFn θ)

/-- `eq:spike-class`: `𝓕_{n,k,α} = {(1-α)U_n + αδ_{θ0^{n-k}} : θ ∈ {0,1}^k}`. -/
def spikeClass (n k : ℕ) (α : ℝ) : Set (Str n → ℝ) :=
  Set.range fun θ : Str k => atomTarget (unif n) α (spikeAtom n θ)

/-- The candidate atoms `θ0^{n-k}`. -/
noncomputable def spikeSet (n k : ℕ) : Finset (Str n) :=
  Finset.univ.image fun θ : Str k => spikeAtom n θ

theorem spikeClass_eq (n k : ℕ) (α : ℝ) :
    spikeClass n k α = atomClass (unif n) (spikeSet n k) α := by
  ext μ
  simp only [spikeClass, atomClass, spikeSet, Set.mem_range, Set.mem_ofPred_eq,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨_, ⟨θ, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨θ, rfl⟩, rfl⟩
    exact ⟨θ, rfl⟩

theorem spikeAtom_apply {k : ℕ} (θ : Str k) (i : Fin n) :
    spikeAtom n θ i = if h : i.val < k then θ ⟨i.val, h⟩ else false := by
  simp only [spikeAtom, strOf, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> simp

theorem pre_spikeAtom {k : ℕ} (hk : k ≤ n) (θ : Str k) :
    pre (spikeAtom n θ) k = List.ofFn θ := by
  apply List.ext_getElem (by simp [pre, hk])
  intro i h1 h2
  simp only [List.length_ofFn] at h2
  simp [pre, spikeAtom_apply, h2]

theorem isPre_spikeAtom {k : ℕ} (hk : k ≤ n) (θ : Str k) :
    IsPre (List.ofFn θ) (spikeAtom n θ) := by
  rw [← pre_spikeAtom hk θ]
  exact isPre_pre _ _

theorem spikeAtom_injective {k : ℕ} (hk : k ≤ n) :
    Function.Injective fun θ : Str k => spikeAtom n θ := by
  intro θ θ' he
  have := pre_spikeAtom hk θ
  rw [show spikeAtom n θ = spikeAtom n θ' from he, pre_spikeAtom hk θ'] at this
  exact (List.ofFn_injective this).symm

theorem card_spikeSet {k : ℕ} (hk : k ≤ n) : (spikeSet n k).card = 2 ^ k := by
  rw [spikeSet, Finset.card_image_of_injective _ (spikeAtom_injective hk)]
  simp

theorem mem_spikeSet {k : ℕ} (θ : Str k) : spikeAtom n θ ∈ spikeSet n k :=
  Finset.mem_image_of_mem _ (Finset.mem_univ θ)

theorem strOf_pre_spikeAtom {k : ℕ} (hk : k ≤ n) (θ : Str k) :
    strOf n (pre (spikeAtom n θ) k) = spikeAtom n θ := by
  rw [pre_spikeAtom hk]
  rfl

theorem card_words (t : ℕ) : (words t).card = 2 ^ t := by
  rw [words, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- At most `2^d` groups of depth `d`. -/
theorem card_image_pre_le (S : Finset (Str n)) {d : ℕ} (hd : d ≤ n) :
    (S.image fun x => pre x d).card ≤ 2 ^ d := by
  rw [← card_words d]
  refine Finset.card_le_card fun u hu => ?_
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
  exact mem_words.mpr (length_pre y hd)

/-! ### The resolution depth -/

theorem exists_two_pow_ge (X : ℝ) : ∃ d : ℕ, X ≤ (2 : ℝ) ^ d :=
  (pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le

open Classical in
/-- The smallest `d ≥ 0` with `2^d ≥ X`. -/
noncomputable def depthFor (X : ℝ) : ℕ := Nat.find (exists_two_pow_ge X)

theorem depthFor_spec (X : ℝ) : X ≤ (2 : ℝ) ^ depthFor X := by
  classical
  exact Nat.find_spec (exists_two_pow_ge X)

theorem depthFor_le {X : ℝ} {m : ℕ} (hm : X ≤ (2 : ℝ) ^ m) : depthFor X ≤ m := by
  classical
  exact Nat.find_min' (exists_two_pow_ge X) hm

/-- Minimality: if `d > 0` then `2^d < 2X`. -/
theorem depthFor_lt {X : ℝ} (hd : 0 < depthFor X) : (2 : ℝ) ^ depthFor X < 2 * X := by
  classical
  have h1 : ¬ X ≤ (2 : ℝ) ^ (depthFor X - 1) :=
    Nat.find_min (exists_two_pow_ge X) (Nat.sub_lt hd one_pos)
  have h2 : (2 : ℝ) ^ depthFor X = 2 * 2 ^ (depthFor X - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2]
  linarith [not_le.mp h1]

/-- `2^d ≤ max(1, 2X)`, in the form used for the rates. -/
theorem two_pow_depthFor_le {X : ℝ} (hX : 1 ≤ 2 * X) : (2 : ℝ) ^ depthFor X ≤ 2 * X := by
  rcases Nat.eq_zero_or_pos (depthFor X) with h0 | hpos
  · rw [h0, pow_zero]
    exact hX
  · exact (depthFor_lt hpos).le

/-- `eq:resolution`: the resolution depth `d`, the smallest `d ≥ 0` with
`2^d ≥ 2RCa/α²`, `a = 1-α`. -/
noncomputable def resDepth (R C α : ℝ) : ℕ := depthFor (2 * R * C * (1 - α) / α ^ 2)

/-- At depth `j ≥ d` the background part of a group is too light to pass the test:
`R (1-α) 2^{-j} < α²/C`. -/
theorem safe_gap {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1) {j : ℕ}
    (hj : 2 * R * C * (1 - α) / α ^ 2 ≤ (2 : ℝ) ^ j) :
    R * ((1 - α) * ((2 : ℝ) ^ j)⁻¹) < α ^ 2 / C := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have ha : 0 < 1 - α := by linarith
  rw [div_le_iff₀ (by positivity)] at hj
  rw [lt_div_iff₀ hC, ← mul_assoc, mul_comm _ C, ← mul_assoc, mul_inv_lt_iff₀ h2]
  nlinarith [mul_pos (mul_pos hR hC) ha]

/-- Pointwise gap: if `2^j ≥ 2R²a/α`, then `R (1-α) 2^{-j} ≤ α/(2R) < α/R`. -/
theorem pw_gap {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1) {j : ℕ}
    (hj : 2 * R ^ 2 * (1 - α) / α ≤ (2 : ℝ) ^ j) :
    R * ((1 - α) * ((2 : ℝ) ^ j)⁻¹) < α / R := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have ha : 0 < 1 - α := by linarith
  rw [div_le_iff₀ hα] at hj
  rw [lt_div_iff₀ hR, mul_comm _ R, ← mul_assoc, ← mul_assoc, mul_inv_lt_iff₀ h2]
  nlinarith [mul_pos (mul_pos hR hR) ha]

/-- `lem:local-test` at the resolution depth: the test is exact at every word of depth at least
`d`. -/
theorem safe_valid {R C α : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α) (hα1 : α < 1)
    {x : Str n} {h : Guide} (hl : SafeLegal R C (atomTarget (unif n) α x) h) :
    ∀ v : List Bool, resDepth R C α ≤ v.length → v.length ≤ n →
      (α ^ 2 / C ≤ h v ↔ IsPre v x) := by
  intro v hv hvn
  refine safe_test (isDist_unif n) hα hα1.le hC hl hvn ?_
  rw [mass_unif hvn]
  refine safe_gap hR hC hα hα1 ((depthFor_spec _).trans ?_)
  exact pow_le_pow_right₀ (by norm_num) hv

/-! ### The group sampler -/

/-- Search `⌈β G⌉` of the `G ≤ 2^d` depth-`d` groups with the threshold test `θ₀ ≤ h(u)`, thin
with the coin, recover the remaining `k-d` key bits with zero-child queries, output the atom
`θ0^{n-k}`; every other branch draws from `U_n`. -/
noncomputable def groupSpike (n k d : ℕ) (θ₀ β : ℝ) : Alg (Str n) :=
  partSampler (fun x => pre x d) (spikeSet n k) β (fun _ r => θ₀ ≤ r)
    (fun u => bindA (bitRec (fun r => θ₀ ≤ r) u (k - d)) fun v => .ret (strOf n v))
    (drawA (unif n))

/-- `eq:local-cap`, group term: the deterministic cap `q + k - d` of the group sampler,
`q = ⌈β2^d⌉`, against every guide. -/
theorem within_groupSpike {k d : ℕ} (hd : d ≤ n) (θ₀ : ℝ) {β : ℝ} (hβ : 0 ≤ β) (h : Guide) :
    (groupSpike n k d θ₀ β).Within h (⌈β * 2 ^ d⌉₊ + (k - d)) := by
  have hw := within_partSampler (fun x => pre x d) (spikeSet n k) β (fun _ r => θ₀ ≤ r)
    (fun u => bindA (bitRec (fun r => θ₀ ≤ r) u (k - d)) fun v => .ret (strOf n v))
    (drawA (unif n)) (h := h) (r := k - d)
    (fun u _ => by
      have := within_bindA (within_bitRec (fun r => θ₀ ≤ r) h u (k - d))
        (f := fun v => (Alg.ret (strOf n v) : Alg (Str n))) (r := 0)
        (fun _ => Alg.Within.ret _ _)
      simpa using this)
    (within_drawA _ h 0)
  refine hw.mono (Nat.add_le_add_right (Nat.ceil_mono ?_) _)
  have := card_image_pre_le (spikeSet n k) hd
  have h' : ((spikeSet n k).image fun x => pre x d).card ≤ (2 : ℝ) ^ d := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left h' hβ

/-- The exact output law of the group sampler whenever the threshold test is exact at every
word of depth at least `d`. -/
theorem lawR_groupSpike {k d : ℕ} (hd : d ≤ k) (hk : k ≤ n) {θ₀ β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (θ : Str k) {h : Guide}
    (hvalid : ∀ v : List Bool, d ≤ v.length → v.length ≤ n →
      (θ₀ ≤ h v ↔ IsPre v (spikeAtom n θ))) :
    lawR ((groupSpike n k d θ₀ β).run h) = atomTarget (unif n) β (spikeAtom n θ) := by
  have hdn : d ≤ n := hd.trans hk
  refine lawR_partSampler _ hβ0 hβ1 _ _ _ (mem_spikeSet θ) (fun y _ => ?_) (fun u hu => ?_) ?_
    (lawR_drawA (isDist_unif n) h)
  · rw [isPre_iff_pre, length_pre y hdn]
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
    exact hvalid _ (by rw [length_pre y hdn]) (by rw [length_pre y hdn]; exact hdn)
  · rw [run_bindA, run_bitRec _ (k - d) _ (isPre_pre _ d) (by rw [length_pre _ hdn]; omega)
      (fun v hv hvn => hvalid v (by rw [length_pre _ hdn] at hv; omega) hvn)]
    rw [PMF.pure_bind, length_pre _ hdn, show d + (k - d) = k by omega, Alg.run_ret,
      strOf_pre_spikeAtom hk]

/-! ### The combined sampler and `eq:local-cap` -/

/-- The cap `min{⌈βM⌉, ⌈β2^d⌉ + k - d}` when `d ≤ k`, and `⌈βM⌉` otherwise (`M = 2^k`). -/
noncomputable def spikeCap (k d : ℕ) (β : ℝ) : ℕ :=
  if d ≤ k then min ⌈β * 2 ^ k⌉₊ (⌈β * 2 ^ d⌉₊ + (k - d)) else ⌈β * 2 ^ k⌉₊

open Classical in
/-- The sampler of Section 3.2: the group sampler at depth `d` when `d ≤ k` and it is cheaper,
exact-leaf search otherwise. -/
noncomputable def spikeSampler (n k d : ℕ) (θ₀ α β : ℝ) : Alg (Str n) :=
  if d ≤ k ∧ ⌈β * 2 ^ d⌉₊ + (k - d) ≤ ⌈β * 2 ^ k⌉₊ then groupSpike n k d θ₀ β
  else leafSampler (unif n) (spikeSet n k) α β

/-- `eq:local-cap`: the deterministic cap of the combined sampler against every guide. -/
theorem within_spikeSampler {k d : ℕ} (hk : k ≤ n) (θ₀ α : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (h : Guide) : (spikeSampler n k d θ₀ α β).Within h (spikeCap k d β) := by
  have hleaf : (leafSampler (unif n) (spikeSet n k) α β).Within h ⌈β * 2 ^ k⌉₊ := by
    have := within_leafSampler (unif n) (spikeSet n k) α β h
    rwa [card_spikeSet hk, Nat.cast_pow, Nat.cast_ofNat] at this
  unfold spikeSampler spikeCap
  by_cases hd : d ≤ k
  · by_cases hc : ⌈β * 2 ^ d⌉₊ + (k - d) ≤ ⌈β * 2 ^ k⌉₊
    · rw [ite_eq_left ⟨hd, hc⟩, ite_eq_left hd, min_eq_right hc]
      exact within_groupSpike (hd.trans hk) θ₀ hβ h
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_left hd, min_eq_left (by omega)]
      exact hleaf
  · rw [ite_eq_right (fun h => hd h.1), ite_eq_right hd]
    exact hleaf

/-- `eq:local-output`: against every guide legal in the safe model with constants `R, C > 0`,
the combined sampler at the resolution depth has output law exactly
`(1-β)U_n + βδ_{θ0^{n-k}}`. -/
theorem lawR_spikeSampler_safe {R C α β : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {k : ℕ} (hk : k ≤ n) (θ : Str k) {h : Guide}
    (hl : SafeLegal R C (atomTarget (unif n) α (spikeAtom n θ)) h) :
    lawR ((spikeSampler n k (resDepth R C α) (α ^ 2 / C) α β).run h) =
      atomTarget (unif n) β (spikeAtom n θ) := by
  unfold spikeSampler
  split_ifs with hc
  · exact lawR_groupSpike hc.1 hk hβ0 hβ1 θ (safe_valid hR hC hα hα1 hl)
  · exact lawR_leafSampler (isDist_unif n) hα hβ0 hβ1 (mem_spikeSet θ) hl.1

/-- `eq:local-output`, distance: the law `(1-β)U_n + βδ_x` is at distance `(α-β)(1-2^{-n})` from
the target. -/
theorem tv_local_output {α β : ℝ} (hβα : β ≤ α) (x : Str n) :
    tv (atomTarget (unif n) β x) (atomTarget (unif n) α x) = (α - β) * (1 - ((2 : ℝ) ^ n)⁻¹) := by
  rw [tv_atomTarget_unif, abs_of_nonpos (by linarith)]
  ring

/-- `eq:local-cap`, sampler form: the combined sampler with `β = α - δ` solves `𝓕_{n,k,α}` at
accuracy `δ` in the safe model with any constants `R, C > 0`, with the cap
`min{⌈βM⌉, ⌈β2^d⌉ + k - d}` (or `⌈βM⌉` if `d > k`). -/
theorem solves_spikeSampler {R C α δ : ℝ} (hR : 0 < R) (hC : 0 < C) (hα : 0 < α)
    (hα1 : α < 1) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) {k : ℕ} (hk : k ≤ n) :
    Solves (SafeLegal R C) (spikeClass n k α) δ (spikeCap k (resDepth R C α) (α - δ))
      (spikeSampler n k (resDepth R C α) (α ^ 2 / C) α (α - δ)) := by
  rintro μ ⟨θ, rfl⟩ h hl
  refine ⟨within_spikeSampler hk _ _ (by linarith) h, ?_⟩
  rw [lawR_spikeSampler_safe hR hC hα hα1 (by linarith) (by linarith) hk θ hl,
    tv_local_output (by linarith)]
  have : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  nlinarith

/-- `eq:local-cap`: for `0 ≤ δ ≤ α < 1`, `β = α - δ` and the resolution depth `d` of
`eq:resolution` at `R = C = 9/4`,
`Q_safe(𝓕_{n,k,α},δ) ≤ min{⌈βM⌉, ⌈β2^d⌉ + k - d}` when `d ≤ k`, and `≤ ⌈βM⌉` when `d > k`. -/
theorem local_cap {α δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) {k : ℕ}
    (hk : k ≤ n) :
    Qsafe (spikeClass n k α) δ ≤ spikeCap k (resDepth (9 / 4) (9 / 4) α) (α - δ) :=
  Qcx_le (solves_spikeSampler (by norm_num) (by norm_num) hα hα1 hδ0 hδα hk)

end LearningGuided.Sec3
