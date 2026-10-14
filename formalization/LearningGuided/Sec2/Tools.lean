import LearningGuided.Cuts

/-!
# Shared tools for Sections 2, 4 and 5

* `toPMF`: a real distribution on `{0,1}^n` as a `PMF`, used for free fallback draws.
* `mixD ν a z = (1-a) ν + a δ_z` and its prefix masses.
* `subsetsPMF U q`: a uniformly random `q`-subset of a finite set, and its inclusion
  probability `q/|U|`.
* `scan`: query a list of candidate words one after another, stopping at the first passing
  test; `searchAlg`: the paper's "choose `q` distinct candidates uniformly and test them"
  algorithm built from `scan`.
* `exhaustAlg`: query every leaf and sample exactly; it shows that solvers always exist, so
  `Qcx` is monotone in the accuracy.
* Real-valued forms of the counting lemmas `equality_counting` and `binary_counting`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec2

variable {n : ℕ}

/-! ### Real laws -/

/-- A real distribution as a `PMF`. -/
noncomputable def toPMF (μ : Str n → ℝ) (hμ : IsDist μ) : PMF (Str n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hμ.1 x), hμ.2, ENNReal.ofReal_one])

theorem lawR_toPMF (μ : Str n → ℝ) (hμ : IsDist μ) : lawR (toPMF μ hμ) = μ := by
  funext x
  simp [lawR, toPMF, ENNReal.toReal_ofReal (hμ.1 x)]

theorem lawR_nonneg {β : Type} (p : PMF β) (b : β) : 0 ≤ lawR p b := ENNReal.toReal_nonneg

theorem sum_lawR {β : Type} [Fintype β] (p : PMF β) : ∑ b, lawR p b = 1 := by
  unfold lawR
  rw [← ENNReal.toReal_sum (fun b _ => p.apply_ne_top b)]
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  simp [h]

theorem lawR_pure {β : Type} [DecidableEq β] (a b : β) :
    lawR (PMF.pure a) b = if b = a then 1 else 0 := by
  unfold lawR
  rw [PMF.pure_apply]
  split_ifs <;> simp

theorem lawR_pure_eq_dirac (z x : Str n) : lawR (PMF.pure z) x = dirac z x := by
  rw [lawR_pure]; rfl

theorem lawR_bind {γ β : Type} [Fintype γ] (p : PMF γ) (f : γ → PMF β) (b : β) :
    lawR (p.bind f) b = ∑ g, lawR p g * lawR (f g) b := by
  simp only [lawR, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun g _ => ENNReal.mul_ne_top (p.apply_ne_top g)
    ((f g).apply_ne_top b))]
  simp [ENNReal.toReal_mul]

theorem lawR_map {γ β : Type} [Fintype γ] [DecidableEq β] (p : PMF γ) (f : γ → β) (b : β) :
    lawR (p.map f) b = ∑ g, if f g = b then lawR p g else 0 := by
  rw [← PMF.bind_pure_comp, lawR_bind]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.comp_apply, lawR_pure]
  by_cases h : f g = b
  · simp [h]
  · have : b ≠ f g := fun e => h e.symm
    simp [h, this]

/-- Splitting a finite average over a predicate. -/
theorem sum_lawR_ite {γ : Type} [Fintype γ] (p : PMF γ) (E : γ → Prop) [DecidablePred E]
    (a b : ℝ) :
    ∑ g, lawR p g * (if E g then a else b) =
      (∑ g, lawR p g * (if E g then 1 else 0)) * a +
        (1 - ∑ g, lawR p g * (if E g then 1 else 0)) * b := by
  have h1 := sum_lawR p
  have : ∑ g, lawR p g * (if E g then a else b) =
      ∑ g, (lawR p g * (if E g then 1 else 0) * a +
        (lawR p g - lawR p g * (if E g then 1 else 0)) * b) :=
    Finset.sum_congr rfl fun g _ => by split_ifs <;> ring
  rw [this, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
    h1]

/-! ### Mixtures with a point mass -/

/-- `mixD ν a z = (1-a) ν + a δ_z`. -/
noncomputable def mixD (ν : Str n → ℝ) (a : ℝ) (z : Str n) : Str n → ℝ :=
  fun x => (1 - a) * ν x + a * dirac z x

theorem mass_mixD (ν : Str n → ℝ) (a : ℝ) (z : Str n) (u : List Bool) :
    mass (mixD ν a z) u = (1 - a) * mass ν u + a * (if IsPre u z then 1 else 0) := by
  unfold mixD
  rw [mass_linear, mass_dirac]

theorem isDist_mixD {ν : Str n → ℝ} (hν : IsDist ν) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (z : Str n) : IsDist (mixD ν a z) :=
  isDist_mix hν (isDist_dirac z) ha0 ha1

theorem tv_mixD (ν : Str n → ℝ) (a b : ℝ) (z : Str n) :
    tv (mixD ν a z) (mixD ν b z) = |a - b| * tv ν (dirac z) :=
  tv_mix ν (dirac z) a b

theorem tv_mixD_le {ν : Str n → ℝ} (hν : IsDist ν) (a b : ℝ) (z : Str n) :
    tv (mixD ν a z) (mixD ν b z) ≤ |a - b| := by
  rw [tv_mixD]
  have := tv_le_one hν (isDist_dirac z)
  have := abs_nonneg (a - b)
  nlinarith [tv_nonneg ν (dirac z)]

theorem mixD_apply_self (ν : Str n → ℝ) (a : ℝ) (z : Str n) :
    mixD ν a z z = (1 - a) * ν z + a := by
  simp [mixD, dirac]

theorem mass_finsum {ι : Type} (s : Finset ι) (f : ι → Str n → ℝ) (u : List Bool) :
    mass (fun x => ∑ i ∈ s, f i x) u = ∑ i ∈ s, mass (f i) u := by
  unfold mass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem mass_smul (c : ℝ) (μ : Str n → ℝ) (u : List Bool) :
    mass (fun x => c * μ x) u = c * mass μ u := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- Prefix mass dominates the mass of any string below the prefix. -/
theorem le_mass_of_isPre {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) {u : List Bool} {z : Str n}
    (hz : IsPre u z) : μ z ≤ mass μ u := by
  classical
  unfold mass
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z), ite_eq_left hz]
  have : 0 ≤ ∑ x ∈ Finset.univ.erase z, (if IsPre u x then μ x else 0) :=
    Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hμ x]
  linarith

/-- The total mass dominates every prefix mass. -/
theorem mass_le_total {μ : Str n → ℝ} (hμ : ∀ x, 0 ≤ μ x) (u : List Bool) :
    mass μ u ≤ ∑ x, μ x :=
  Finset.sum_le_sum fun x _ => by split_ifs <;> simp [hμ x]

/-- Prefix relation through the coordinates of a string. -/
theorem isPre_iff_getElem {u : List Bool} {x : Str n} :
    IsPre u x ↔ ∃ h : u.length ≤ n, ∀ i (hi : i < u.length), u[i] = x ⟨i, by omega⟩ := by
  unfold IsPre
  rw [List.prefix_iff_getElem]
  simp

/-! ### Uniformly random subsets -/

theorem card_filter_mem_powersetCard {K : Type} [DecidableEq K] (U : Finset K) {θ : K}
    (hθ : θ ∈ U) (q : ℕ) :
    ((U.powersetCard (q + 1)).filter (fun S => θ ∈ S)).card = (U.card - 1).choose q := by
  rw [← Finset.card_erase_of_mem hθ, ← Finset.card_powersetCard]
  refine Finset.card_bij' (fun S _ => S.erase θ) (fun T _ => insert θ T) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    simp only [Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase θ hS.1.1, ?_⟩
    rw [Finset.card_erase_of_mem hS.2, hS.1.2]
    rfl
  · intro T hT
    simp only [Finset.mem_powersetCard] at hT
    have hθT : θ ∉ T := fun h => by simpa using hT.1 h
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.insert_subset hθ (hT.1.trans (Finset.erase_subset θ U)), ?_⟩,
      Finset.mem_insert_self θ T⟩
    rw [Finset.card_insert_of_notMem hθT, hT.2]
  · intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2
  · intro T hT
    simp only [Finset.mem_powersetCard] at hT
    have hθT : θ ∉ T := fun h => by simpa using hT.1 h
    exact Finset.erase_insert hθT

/-- The number of `q`-subsets containing a given element, times `|U|`, is `q` times the
number of `q`-subsets. -/
theorem card_filter_mem_powersetCard_mul {K : Type} [DecidableEq K] (U : Finset K) {θ : K}
    (hθ : θ ∈ U) (q : ℕ) :
    ((U.powersetCard q).filter (fun S => θ ∈ S)).card * U.card = q * U.card.choose q := by
  rcases q with _ | q
  · simp
  · rw [card_filter_mem_powersetCard U hθ q]
    obtain ⟨N, hN⟩ : ∃ N, U.card = N + 1 := ⟨U.card - 1, by
      have := Finset.card_pos.mpr ⟨θ, hθ⟩; omega⟩
    rw [hN, Nat.add_sub_cancel, mul_comm, Nat.add_one_mul_choose_eq, mul_comm]

/-- A uniformly random `q`-subset of `U`. -/
noncomputable def subsetsPMF {K : Type} [DecidableEq K] (U : Finset K) (q : ℕ)
    (hq : q ≤ U.card) : PMF (Finset K) :=
  PMF.uniformOfFinset (U.powersetCard q) (Finset.powersetCard_nonempty.mpr hq)

theorem lawR_subsetsPMF {K : Type} [DecidableEq K] (U : Finset K) (q : ℕ) (hq : q ≤ U.card)
    (S : Finset K) :
    lawR (subsetsPMF U q hq) S =
      if S ∈ U.powersetCard q then ((U.card.choose q : ℕ) : ℝ)⁻¹ else 0 := by
  unfold lawR subsetsPMF
  rw [PMF.uniformOfFinset_apply, Finset.card_powersetCard]
  split_ifs <;> simp

theorem mem_support_subsetsPMF {K : Type} [DecidableEq K] {U : Finset K} {q : ℕ}
    {hq : q ≤ U.card} {S : Finset K} (hS : S ∈ (subsetsPMF U q hq).support) :
    S ⊆ U ∧ S.card = q := by
  unfold subsetsPMF at hS
  rw [PMF.mem_support_uniformOfFinset_iff, Finset.mem_powersetCard] at hS
  exact hS

/-- Inclusion probability of a uniformly random `q`-subset: `P(θ ∈ S) = q/|U|`. -/
theorem prob_mem_subsetsPMF {K : Type} [DecidableEq K] [Fintype K] (U : Finset K) (q : ℕ)
    (hq : q ≤ U.card) {θ : K} (hθ : θ ∈ U) :
    ∑ S, lawR (subsetsPMF U q hq) S * (if θ ∈ S then 1 else 0) = (q : ℝ) / U.card := by
  classical
  have hU : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr ⟨θ, hθ⟩
  have hC : (0 : ℝ) < (U.card.choose q : ℕ) := by exact_mod_cast Nat.choose_pos hq
  simp_rw [lawR_subsetsPMF]
  have : ∑ S : Finset K, (if S ∈ U.powersetCard q then ((U.card.choose q : ℕ) : ℝ)⁻¹ else 0) *
      (if θ ∈ S then 1 else 0) =
      ∑ S ∈ (U.powersetCard q).filter (fun S => θ ∈ S), ((U.card.choose q : ℕ) : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    rw [← Finset.sum_subset (Finset.subset_univ (U.powersetCard q))]
    · refine Finset.sum_congr rfl fun S hS => ?_
      rw [ite_eq_left hS]
      split_ifs <;> simp
    · intro S _ hS
      simp [hS]
  rw [this, Finset.sum_const, nsmul_eq_mul]
  have key := card_filter_mem_powersetCard_mul U hθ q
  have key' : (((U.powersetCard q).filter (fun S => θ ∈ S)).card : ℝ) * U.card =
      q * (U.card.choose q : ℕ) := by exact_mod_cast key
  field_simp
  linarith

/-! ### Scanning candidates -/

open Classical in
/-- Query the words of a list of candidates in order; the first candidate whose answer passes
`test` continues with `hit`; if none passes, continue with `miss`. -/
noncomputable def scan {K β : Type} (leaf : K → List Bool) (test : K → ℝ → Prop)
    (hit : K → Alg β) (miss : Alg β) : List K → Alg β
  | [] => miss
  | κ :: L => Alg.query (leaf κ) (fun r => if test κ r then hit κ else scan leaf test hit miss L)

open Classical in
theorem run_scan {K β : Type} (leaf : K → List Bool) (test : K → ℝ → Prop) (hit : K → Alg β)
    (miss : Alg β) (h : Guide) (θ : K) (htest : ∀ κ, test κ (h (leaf κ)) ↔ κ = θ) :
    ∀ L : List K, (scan leaf test hit miss L).run h =
      if θ ∈ L then (hit θ).run h else miss.run h := by
  classical
  intro L
  induction L with
  | nil => simp [scan]
  | cons κ L ih =>
      simp only [scan, Alg.run_query]
      by_cases hk : κ = θ
      · subst hk
        rw [ite_eq_left ((htest κ).mpr rfl)]
        simp
      · rw [ite_eq_right (fun h' => hk ((htest κ).mp h')), ih]
        have : θ ∈ κ :: L ↔ θ ∈ L := by
          simp only [List.mem_cons]
          exact ⟨fun h' => h'.resolve_left (fun e => hk e.symm), Or.inr⟩
        simp only [this]

theorem within_scan {K β : Type} (leaf : K → List Bool) (test : K → ℝ → Prop) (hit : K → Alg β)
    (miss : Alg β) (h : Guide) (c : ℕ) (hhit : ∀ κ, (hit κ).Within h c)
    (hmiss : miss.Within h c) : ∀ L : List K, (scan leaf test hit miss L).Within h (L.length + c)
  | [] => by simpa [scan] using hmiss
  | κ :: L => by
      classical
      have := within_scan leaf test hit miss h c hhit hmiss L
      simp only [scan, List.length_cons]
      rw [show L.length + 1 + c = (L.length + c) + 1 by omega]
      refine Alg.Within.query _ _ _ ?_
      split_ifs
      · exact (hhit κ).mono (by omega)
      · exact this

/-- The paper's search: choose `q` distinct candidates uniformly at random and test them in
turn. `miss S` continues after all candidates of `S` fail. -/
noncomputable def searchAlg {K β : Type} [Fintype K] [DecidableEq K] (q : ℕ)
    (hq : q ≤ Fintype.card K) (leaf : K → List Bool) (test : K → ℝ → Prop) (hit : K → Alg β)
    (miss : Finset K → Alg β) : Alg β :=
  Alg.sample (subsetsPMF Finset.univ q (by simpa using hq))
    (fun S => scan leaf test hit (miss S) S.toList)

theorem run_searchAlg {K β : Type} [Fintype K] [DecidableEq K] (q : ℕ)
    (hq : q ≤ Fintype.card K) (leaf : K → List Bool) (test : K → ℝ → Prop) (hit : K → Alg β)
    (miss : Finset K → Alg β) (h : Guide) (θ : K) (htest : ∀ κ, test κ (h (leaf κ)) ↔ κ = θ) :
    (searchAlg q hq leaf test hit miss).run h =
      (subsetsPMF Finset.univ q (by simpa using hq)).bind
        (fun S => if θ ∈ S then (hit θ).run h else (miss S).run h) := by
  unfold searchAlg
  rw [Alg.run_sample]
  congr 1
  funext S
  rw [run_scan leaf test hit (miss S) h θ htest]
  by_cases hθ : θ ∈ S <;> simp [hθ]

theorem within_searchAlg {K β : Type} [Fintype K] [DecidableEq K] (q : ℕ)
    (hq : q ≤ Fintype.card K) (leaf : K → List Bool) (test : K → ℝ → Prop) (hit : K → Alg β)
    (miss : Finset K → Alg β) (h : Guide) (c : ℕ) (hhit : ∀ κ, (hit κ).Within h c)
    (hmiss : ∀ S, (miss S).Within h c) :
    (searchAlg q hq leaf test hit miss).Within h (q + c) := by
  unfold searchAlg
  refine Alg.Within.sample _ _ _ fun S hS => ?_
  have hc := (mem_support_subsetsPMF hS).2
  have := within_scan leaf test hit (miss S) h c hhit (hmiss S) S.toList
  rwa [Finset.length_toList, hc] at this

/-- The output law of the search with a fixed fallback law: `(1 - q/|K|) ν + (q/|K|) δ_z`. -/
theorem lawR_searchAlg {K : Type} [Fintype K] [DecidableEq K] (q : ℕ)
    (hq : q ≤ Fintype.card K) (leaf : K → List Bool) (test : K → ℝ → Prop)
    (hit : K → Alg (Str n)) (fallback : Alg (Str n)) (h : Guide) (θ : K)
    (htest : ∀ κ, test κ (h (leaf κ)) ↔ κ = θ) (z : Str n) (hz : (hit θ).run h = PMF.pure z)
    (ν : Str n → ℝ) (hν : lawR (fallback.run h) = ν) :
    lawR ((searchAlg q hq leaf test hit (fun _ => fallback)).run h) =
      mixD ν ((q : ℝ) / Fintype.card K) z := by
  classical
  funext x
  rw [run_searchAlg q hq leaf test hit _ h θ htest, lawR_bind]
  have : ∀ S : Finset K, lawR (if θ ∈ S then (hit θ).run h else fallback.run h) x =
      if θ ∈ S then dirac z x else ν x := by
    intro S
    split_ifs
    · rw [hz, lawR_pure_eq_dirac]
    · rw [hν]
  simp_rw [this]
  rw [sum_lawR_ite, prob_mem_subsetsPMF _ _ _ (Finset.mem_univ θ), Finset.card_univ, mixD]
  ring

/-! ### Exhaustive exact sampling and monotonicity of `Qcx` -/

open Classical in
/-- Sample from a collected table when it is a distribution. -/
noncomputable def finishAlg (f : Str n → ℝ) : Alg (Str n) :=
  if hf : IsDist f then Alg.sample (toPMF f hf) Alg.ret else Alg.ret (fun _ => false)

/-- Query the leaves of a list one at a time, recording the answers. -/
noncomputable def collectAlg : List (Str n) → (Str n → ℝ) → Alg (Str n)
  | [], f => finishAlg f
  | x :: L, f => Alg.query (List.ofFn x) (fun r => collectAlg L (Function.update f x r))

/-- Query every leaf and sample from the recorded exact leaf values. -/
noncomputable def exhaustAlg (n : ℕ) : Alg (Str n) :=
  collectAlg (Finset.univ : Finset (Str n)).toList (fun _ => 0)

theorem run_collectAlg {μ : Str n → ℝ} {h : Guide} (hleaf : ∀ x : Str n, h (List.ofFn x) = μ x) :
    ∀ (L : List (Str n)) (f : Str n → ℝ), (collectAlg L f).run h =
      (finishAlg (fun y => if y ∈ L then μ y else f y)).run h := by
  classical
  intro L
  induction L with
  | nil => intro f; simp [collectAlg]
  | cons x L ih =>
      intro f
      simp only [collectAlg, Alg.run_query, hleaf, ih]
      congr 3
      funext y
      by_cases hy : y ∈ L
      · simp [hy]
      · by_cases hyx : y = x
        · subst hyx; simp
        · simp [hy, hyx]

theorem within_collectAlg (h : Guide) :
    ∀ (L : List (Str n)) (f : Str n → ℝ), (collectAlg L f).Within h L.length := by
  intro L
  induction L with
  | nil =>
      intro f
      simp only [collectAlg, finishAlg, List.length_nil]
      split_ifs
      · exact Alg.Within.sample _ _ _ fun g _ => Alg.Within.ret g 0
      · exact Alg.Within.ret _ 0
  | cons x L ih =>
      intro f
      exact Alg.Within.query _ _ _ (ih _)

theorem run_exhaustAlg {μ : Str n → ℝ} (hμ : IsDist μ) {h : Guide}
    (hleaf : ∀ x : Str n, h (List.ofFn x) = μ x) : lawR ((exhaustAlg n).run h) = μ := by
  classical
  unfold exhaustAlg
  rw [run_collectAlg hleaf]
  have : (fun y => if y ∈ (Finset.univ : Finset (Str n)).toList then μ y else 0) = μ := by
    funext y; simp
  rw [this]
  simp only [finishAlg, dite_eq_left hμ, Alg.run_sample, Alg.run_ret]
  rw [PMF.bind_pure, lawR_toPMF]

/-- Exhaustive leaf queries solve every class of distributions exactly, with cap `2^n`, in every
model whose guides satisfy the access conditions. -/
theorem exists_solver {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ : ℝ}
    (hF : ∀ μ ∈ F, IsDist μ) (hL : ∀ μ h, Legal μ h → IsOracle μ h) (hδ : 0 ≤ δ) :
    ∃ q A, Solves Legal F δ q A := by
  refine ⟨(Finset.univ : Finset (Str n)).toList.length, exhaustAlg n, fun μ hμ h hl => ?_⟩
  refine ⟨within_collectAlg h _ _, ?_⟩
  rw [run_exhaustAlg (hF μ hμ) (hL μ h hl).leaf, tv_self]
  exact hδ

theorem solves_mono_delta {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)}
    {δ δ' : ℝ} {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal F δ q A) (hδ : δ ≤ δ') :
    Solves Legal F δ' q A :=
  fun μ hμ h hl => ⟨(hA μ hμ h hl).1, (hA μ hμ h hl).2.trans hδ⟩

/-- The minimal cap is attained when some solver exists. -/
theorem exists_solver_Qcx {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ : ℝ}
    (hex : ∃ q A, Solves Legal F δ q A) : ∃ A, Solves Legal F δ (Qcx Legal F δ) A :=
  Nat.sInf_mem (s := {q | ∃ A, Solves Legal F δ q A}) hex

/-- Transfer of solvers: if every solver of the first problem yields a solver of the second
with the same cap, and the first problem has a solver, then the second minimax complexity is at
most the first. -/
theorem Qcx_le_of_transfer {m : ℕ} {Legal₁ : (Str n → ℝ) → Guide → Prop}
    {F₁ : Set (Str n → ℝ)} {δ₁ : ℝ} {Legal₂ : (Str m → ℝ) → Guide → Prop}
    {F₂ : Set (Str m → ℝ)} {δ₂ : ℝ} (hex : ∃ q A, Solves Legal₁ F₁ δ₁ q A)
    (htr : ∀ q A, Solves Legal₁ F₁ δ₁ q A → ∃ A', Solves Legal₂ F₂ δ₂ q A') :
    Qcx Legal₂ F₂ δ₂ ≤ Qcx Legal₁ F₁ δ₁ := by
  obtain ⟨A, hA⟩ := exists_solver_Qcx hex
  obtain ⟨A', hA'⟩ := htr _ A hA
  exact Qcx_le hA'

/-- Monotonicity in the accuracy. -/
theorem Qcx_anti {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ δ' : ℝ}
    (hex : ∃ q A, Solves Legal F δ q A) (hδ : δ ≤ δ') : Qcx Legal F δ' ≤ Qcx Legal F δ :=
  Qcx_le_of_transfer hex fun _ A hA => ⟨A, solves_mono_delta hA hδ⟩

theorem Qpw_anti {F : Set (Str n → ℝ)} (hF : ∀ μ ∈ F, IsDist μ) {δ δ' : ℝ} (h0 : 0 ≤ δ)
    (hδ : δ ≤ δ') : Qpw F δ' ≤ Qpw F δ :=
  Qcx_anti (exists_solver hF (fun _ _ hl => hl.1) h0) hδ

theorem Qsafe_anti {F : Set (Str n → ℝ)} (hF : ∀ μ ∈ F, IsDist μ) {δ δ' : ℝ} (h0 : 0 ≤ δ)
    (hδ : δ ≤ δ') : Qsafe F δ' ≤ Qsafe F δ :=
  Qcx_anti (exists_solver hF (fun _ _ hl => hl.1) h0) hδ

/-! ### Real-valued counting bounds -/

theorem toReal_sum_probE_le {β Θ : Type} (S : Finset Θ) (P : Θ → PMF β) (E : Θ → Set β)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : ∑ θ ∈ S, probE (P θ) (E θ) ≤ c) :
    ∑ θ ∈ S, (probE (P θ) (E θ)).toReal ≤ c.toReal := by
  have hfin : ∀ θ ∈ S, probE (P θ) (E θ) ≠ ⊤ := fun θ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)
  rw [← ENNReal.toReal_sum hfin]
  exact ENNReal.toReal_mono hc h

/-- The equality-counting lower bound in the form used for sampling: if each query is simulated
by one equality test and the events `E θ` are disjoint, then a `δ`-accurate sampler with cap `q`
satisfies `∑_θ (μ_θ(E_θ) - δ) ≤ q + 1`. -/
theorem sampling_equality_bound {Θ : Type} [Fintype Θ] (H : Θ → Guide)
    (hH : EqualityStructure H) (μ : Θ → Str n → ℝ) (hμ : ∀ θ, IsDist (μ θ))
    (E : Θ → Finset (Str n))
    (hE : ∀ x, (Finset.univ.filter fun θ => x ∈ E θ).card ≤ 1) (A : Alg (Str n)) (q : ℕ)
    (δ : ℝ) (hA : ∀ θ, A.Within (H θ) q ∧ tv (lawR (A.run (H θ))) (μ θ) ≤ δ) :
    ∑ θ, (∑ x ∈ E θ, μ θ x - δ) ≤ q + 1 := by
  classical
  have h1 := equality_counting H hH (fun θ => (E θ : Set (Str n))) 1 A Finset.univ q
    (fun b => by simpa using hE b) (fun θ _ => (hA θ).1)
  have h2 := toReal_sum_probE_le Finset.univ (fun θ => A.run (H θ))
    (fun θ => (E θ : Set (Str n))) (by simp) h1
  have h3 : ∀ θ, ∑ x ∈ E θ, μ θ x - δ ≤ (probE (A.run (H θ)) (E θ : Set (Str n))).toReal :=
    fun θ => prob_ge_of_tv (hμ θ) (hA θ).2 (E θ)
  calc ∑ θ, (∑ x ∈ E θ, μ θ x - δ)
      ≤ ∑ θ, (probE (A.run (H θ)) (E θ : Set (Str n))).toReal :=
        Finset.sum_le_sum fun θ _ => h3 θ
    _ ≤ ((q : ℝ≥0∞) + ((1 : ℕ) : ℝ≥0∞)).toReal := h2
    _ = q + 1 := by rw [ENNReal.toReal_add (by simp) (by simp)]; simp

/-- The transcript-counting lower bound in the form used for sampling: with at most two answers
per query and disjoint events, a `δ`-accurate sampler with cap `q` satisfies
`∑_θ (μ_θ(E_θ) - δ) ≤ 2^q`. -/
theorem sampling_binary_bound {Θ : Type} [Fintype Θ] (H : Θ → Guide)
    (hH : BinaryAnswers H) (μ : Θ → Str n → ℝ) (hμ : ∀ θ, IsDist (μ θ))
    (E : Θ → Finset (Str n))
    (hE : ∀ x, (Finset.univ.filter fun θ => x ∈ E θ).card ≤ 1) (A : Alg (Str n)) (q : ℕ)
    (δ : ℝ) (hA : ∀ θ, A.Within (H θ) q ∧ tv (lawR (A.run (H θ))) (μ θ) ≤ δ) :
    ∑ θ, (∑ x ∈ E θ, μ θ x - δ) ≤ 2 ^ q := by
  classical
  have h1 := binary_counting H hH (fun θ => (E θ : Set (Str n))) 1 A Finset.univ q
    (fun b => by simpa using hE b) (fun θ _ => (hA θ).1)
  have h2 := toReal_sum_probE_le Finset.univ (fun θ => A.run (H θ))
    (fun θ => (E θ : Set (Str n))) (by simp) h1
  have h3 : ∀ θ, ∑ x ∈ E θ, μ θ x - δ ≤ (probE (A.run (H θ)) (E θ : Set (Str n))).toReal :=
    fun θ => prob_ge_of_tv (hμ θ) (hA θ).2 (E θ)
  calc ∑ θ, (∑ x ∈ E θ, μ θ x - δ)
      ≤ ∑ θ, (probE (A.run (H θ)) (E θ : Set (Str n))).toReal :=
        Finset.sum_le_sum fun θ _ => h3 θ
    _ ≤ ((2 : ℝ≥0∞) ^ q * ((1 : ℕ) : ℝ≥0∞)).toReal := h2
    _ = 2 ^ q := by simp

/-- The exact prefix masses form a pointwise factor-`R` guide for every `R ≥ 1`. -/
theorem pwLegal_exact {μ : Str n → ℝ} (hμ : IsDist μ) {R : ℝ} (hR : 1 ≤ R) :
    PwLegal R μ (fun u => mass μ u) := by
  refine ⟨⟨fun u => mass_nonneg hμ.1 u, by rw [mass_nil, hμ.2], fun x => mass_ofFn μ x,
    fun u hu => mass_eq_zero_of_long μ hu⟩, fun u _ => ?_⟩
  have h0 := mass_nonneg hμ.1 u
  refine ⟨div_le_self h0 hR, ?_⟩
  nlinarith

end Sec2
end LearningGuided
