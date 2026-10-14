import LearningGuided.Sec3.Recovery

/-!
# Common tools for the atom classes of Section 3

* exact guides and monotonicity of the two guidance models in their constants;
* the exact-leaf sampler `leafSampler` (search `⌈βM⌉` candidate leaves with the thinning coin,
  output a fresh background draw on every other branch), valid for every guide satisfying
  `eq:oracle`;
* `solves_of_law`: an exact output law `(1-β)ν + βδ_x` gives accuracy `|α-β|`;
* helpers turning the counting lemmas of `Alg.lean` into real inequalities.
-/

open scoped BigOperators ENNReal

namespace LearningGuided.Sec3

open LearningGuided

variable {n : ℕ}

/-! ### Exact guides and monotonicity of the models -/

/-- The exact guide `h(u) = μ(u)` (zero on words longer than `n`). -/
noncomputable def exactGuide (μ : Str n → ℝ) : Guide := fun u => mass μ u

theorem isOracle_exactGuide {μ : Str n → ℝ} (hμ : IsDist μ) : IsOracle μ (exactGuide μ) where
  nonneg u := mass_nonneg hμ.1 u
  root := by simp [exactGuide, mass_nil, hμ.2]
  leaf x := mass_ofFn μ x
  long u hu := mass_eq_zero_of_long μ hu

theorem CapLE.mono {μ : Str n → ℝ} {h : Guide} {C C' : ℝ} (hc : CapLE μ h C) (hCC : C ≤ C') :
    CapLE μ h C' :=
  ⟨hc.1, fun A hA => (hc.2 A hA).trans hCC⟩

theorem PwLegal.mono {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') {μ : Str n → ℝ} (hμ : IsDist μ)
    {h : Guide} (hl : PwLegal R μ h) : PwLegal R' μ h := by
  refine ⟨hl.1, fun u hu => ⟨?_, ?_⟩⟩
  · have hm := mass_nonneg hμ.1 u
    exact (div_le_div_of_nonneg_left hm hR hRR).trans (hl.2 u hu).1
  · have hm := mass_nonneg hμ.1 u
    exact (hl.2 u hu).2.trans (by nlinarith)

theorem SafeLegal.mono {R R' C C' : ℝ} (hRR : R ≤ R') (hCC : C ≤ C') {μ : Str n → ℝ}
    (hμ : IsDist μ) {h : Guide} (hl : SafeLegal R C μ h) : SafeLegal R' C' μ h := by
  refine ⟨hl.1, fun u hu => ?_, CapLE.mono hl.2.2 hCC⟩
  have hm := mass_nonneg hμ.1 u
  exact (hl.2.1 u hu).trans (by nlinarith)

theorem pwLegal_exactGuide {R : ℝ} (hR : 1 ≤ R) {μ : Str n → ℝ} (hμ : IsDist μ) :
    PwLegal R μ (exactGuide μ) := by
  refine ⟨isOracle_exactGuide hμ, fun u _ => ⟨?_, ?_⟩⟩
  · have hm := mass_nonneg hμ.1 u
    exact div_le_self hm hR
  · have hm := mass_nonneg hμ.1 u
    change mass μ u ≤ R * mass μ u
    nlinarith

theorem safeLegal_exactGuide {R C : ℝ} (hR : 1 ≤ R) (hC : 1 ≤ C) {μ : Str n → ℝ}
    (hμ : IsDist μ) : SafeLegal R C μ (exactGuide μ) :=
  ⟨isOracle_exactGuide hμ, fun u hu => ((pwLegal_exactGuide hR hμ).2 u hu).2,
    CapLE.mono (capLE_of_exact hμ fun _ _ => rfl) hC⟩

/-! ### Accuracy from an exact output law -/

theorem tv_atomTarget_le {ν : Str n → ℝ} (hν : IsDist ν) (α β : ℝ) (x : Str n) :
    tv (atomTarget ν β x) (atomTarget ν α x) ≤ |β - α| := by
  unfold atomTarget
  rw [tv_mix]
  have := tv_le_one hν (isDist_dirac x)
  have := tv_nonneg ν (dirac x)
  have := abs_nonneg (β - α)
  nlinarith

/-- For the uniform background the distance is exactly `(α-β)(1-2^{-n})` (`eq:local-output`). -/
theorem tv_atomTarget_unif (α β : ℝ) (x : Str n) :
    tv (atomTarget (unif n) β x) (atomTarget (unif n) α x) =
      |β - α| * (1 - ((2 : ℝ) ^ n)⁻¹) := by
  unfold atomTarget
  rw [tv_mix, tv_unif_dirac]

/-- An algorithm whose output law is exactly `(1-β)ν + βδ_x` against every legal guide of every
target of the class, and which respects the cap `q` against every guide, solves the class at
accuracy `δ ≥ |α - β|`. -/
theorem solves_of_law {Legal : (Str n → ℝ) → Guide → Prop} {ν : Str n → ℝ} (hν : IsDist ν)
    {S : Finset (Str n)} {α β δ : ℝ} (hδ : |β - α| ≤ δ) {q : ℕ} {A : Alg (Str n)}
    (hcap : ∀ h, A.Within h q)
    (hlaw : ∀ x ∈ S, ∀ h, Legal (atomTarget ν α x) h → lawR (A.run h) = atomTarget ν β x) :
    Solves Legal (atomClass ν S α) δ q A := by
  rintro μ ⟨x, hx, rfl⟩ h hl
  refine ⟨hcap h, ?_⟩
  rw [hlaw x hx h hl]
  exact (tv_atomTarget_le hν α β x).trans hδ

theorem solves_mono_delta {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)}
    {δ δ' : ℝ} (hδ : δ ≤ δ') {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal F δ q A) :
    Solves Legal F δ' q A := fun μ hμ h hl =>
  ⟨(hA μ hμ h hl).1, (hA μ hμ h hl).2.trans hδ⟩

theorem solves_mono_cap {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)}
    {δ : ℝ} {q q' : ℕ} (hq : q ≤ q') {A : Alg (Str n)} (hA : Solves Legal F δ q A) :
    Solves Legal F δ q' A := fun μ hμ h hl =>
  ⟨(hA μ hμ h hl).1.mono hq, (hA μ hμ h hl).2⟩

/-! ### The exact-leaf sampler -/

/-- Exact-leaf search: the candidate leaves are the groups. A leaf query detects the additional
mass `α` exactly, and the recovery needs no query. -/
noncomputable def leafSampler (ν : Str n → ℝ) (S : Finset (Str n)) (α β : ℝ) : Alg (Str n) :=
  partSampler (fun x => List.ofFn x) S β (fun u r => (1 - α) * mass ν u + α ≤ r)
    (fun u => .ret (strOf n u)) (drawA ν)

theorem card_image_ofFn (S : Finset (Str n)) : (S.image fun x => List.ofFn x).card = S.card :=
  Finset.card_image_of_injective _ List.ofFn_injective

/-- The deterministic cap `⌈βM⌉` of exact-leaf search, against every guide. -/
theorem within_leafSampler (ν : Str n → ℝ) (S : Finset (Str n)) (α β : ℝ) (h : Guide) :
    (leafSampler ν S α β).Within h ⌈β * S.card⌉₊ := by
  have := within_partSampler (fun x => List.ofFn x) S β (fun u r => (1 - α) * mass ν u + α ≤ r)
    (fun u => .ret (strOf n u)) (drawA ν) (h := h) (r := 0) (fun _ _ => Alg.Within.ret _ _)
    (within_drawA ν h 0)
  rw [card_image_ofFn, add_zero] at this
  exact this

/-- The exact output law of exact-leaf search: `(1-β)ν + βδ_x` for every guide satisfying
`eq:oracle`. -/
theorem lawR_leafSampler {ν : Str n → ℝ} (hν : IsDist ν) {S : Finset (Str n)} {α β : ℝ}
    (hα : 0 < α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {x : Str n} (hx : x ∈ S) {h : Guide}
    (hl : IsOracle (atomTarget ν α x) h) :
    lawR ((leafSampler ν S α β).run h) = atomTarget ν β x := by
  refine lawR_partSampler _ hβ0 hβ1 _ _ _ hx (fun y _ => ?_) (fun u hu => ?_) ?_
    (lawR_drawA hν h)
  · rw [isPre_ofFn_iff]
    exact ⟨fun h => by rw [h], fun h => List.ofFn_injective h⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
    rw [leaf_test hα hl y, isPre_ofFn_iff]
  · simp [strOf_ofFn]

/-- Exact-leaf search solves every atom class in every model whose guides satisfy `eq:oracle`,
at accuracy `δ` with cap `⌈(α-δ)M⌉`. -/
theorem solves_leafSampler {Legal : (Str n → ℝ) → Guide → Prop}
    (hLegal : ∀ μ h, Legal μ h → IsOracle μ h) {ν : Str n → ℝ} (hν : IsDist ν)
    (S : Finset (Str n)) {α δ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) :
    Solves Legal (atomClass ν S α) δ ⌈(α - δ) * S.card⌉₊ (leafSampler ν S α (α - δ)) :=
  solves_of_law hν (by rw [abs_of_nonpos (by linarith)]; linarith)
    (fun h => within_leafSampler ν S α (α - δ) h)
    (fun _ hx h hl => lawR_leafSampler hν hα (by linarith) (by linarith) hx (hLegal _ _ hl))

/-! ### From counting lemmas to real inequalities -/

theorem sum_toReal_le_of_le {ι : Type} (S : Finset ι) (P : ι → ℝ≥0∞) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hP : ∀ i, P i ≤ 1) (hsum : ∑ i ∈ S, P i ≤ B) :
    ∑ i ∈ S, (P i).toReal ≤ B.toReal := by
  rw [← ENNReal.toReal_sum fun i _ => ne_top_of_le_ne_top ENNReal.one_ne_top (hP i)]
  exact ENNReal.toReal_mono hB hsum

/-- If every term is at least `p` and the summed probabilities are at most `B`, then
`|S| p ≤ B`. -/
theorem card_mul_le_of_sum {ι : Type} (S : Finset ι) (P : ι → ℝ≥0∞) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hP : ∀ i, P i ≤ 1) (hsum : ∑ i ∈ S, P i ≤ B) {p : ℝ}
    (hp : ∀ i ∈ S, p ≤ (P i).toReal) : S.card * p ≤ B.toReal := by
  have h1 := sum_toReal_le_of_le S P hB hP hsum
  have h2 : ∑ _i ∈ S, p ≤ ∑ i ∈ S, (P i).toReal := Finset.sum_le_sum hp
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

/-- The mass of a word as the probability of the event "the output extends `u`". -/
theorem mass_eq_sum_filter (μ : Str n → ℝ) (u : List Bool) :
    mass μ u = ∑ y ∈ Finset.univ.filter (IsPre u), μ y := by
  rw [Finset.sum_filter]
  rfl

/-- Distinct words of the same length have disjoint cylinders. -/
theorem card_filter_isPre_ofFn_le_one {k : ℕ} (S : Finset (Str k)) (y : Str n) :
    (S.filter fun θ => y ∈ (Finset.univ.filter (IsPre (List.ofFn θ)) : Finset (Str n))).card
      ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases ha.2.comparable hb.2 with h | h
  · exact List.ofFn_injective (h.eq_of_length (by simp))
  · exact (List.ofFn_injective (h.eq_of_length (by simp))).symm

end LearningGuided.Sec3
