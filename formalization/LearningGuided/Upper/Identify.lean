import LearningGuided.Upper.Tools

/-!
# Exact identification of a finite class

The first bound of Proposition `pw-prop:upper` and the remark "Exact identification costs at most
`M-1` queries" of Section 1.2: maintain the candidates consistent with all queried leaf values;
while two distinct candidates remain, query a leaf on which two of them differ. Exact leaves keep
the target and remove at least one candidate, so at most `|F| - 1` queries identify the target,
and sampling from the identified distribution is free. The algorithm samples exactly (`δ = 0`)
against every guide with exact leaves, in any model whose legal guides satisfy `eq:oracle`.

We also define the worst-case complexities `Q(n,M,δ)` over classes of at most `M` distributions
(`QcxNM`, `QpwNM`, `QsafeNM`) and record that they are at most `M - 1`.
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Upper

variable {n : ℕ}

/-- A fixed string, used as a fallback output. -/
def fbStr (n : ℕ) : Str n := fun _ => false

theorem sum_ofReal_eq_one {μ : Str n → ℝ} (hμ : IsDist μ) :
    ∑ x, ENNReal.ofReal (μ x) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hμ.1 x), hμ.2, ENNReal.ofReal_one]

open Classical in
/-- The law of a known distribution on `{0,1}^n` (a fixed point mass for other functions). -/
noncomputable def toPMF (μ : Str n → ℝ) : PMF (Str n) :=
  if hμ : IsDist μ then PMF.ofFintype (fun x => ENNReal.ofReal (μ x)) (sum_ofReal_eq_one hμ)
  else PMF.pure (fbStr n)

theorem toPMF_apply {μ : Str n → ℝ} (hμ : IsDist μ) (x : Str n) :
    toPMF μ x = ENNReal.ofReal (μ x) := by
  simp [toPMF, hμ, PMF.ofFintype_apply]

theorem lawR_toPMF {μ : Str n → ℝ} (hμ : IsDist μ) : lawR (toPMF μ) = μ := by
  ext x
  rw [lawR, toPMF_apply hμ, ENNReal.toReal_ofReal (hμ.1 x)]

/-- Sampling from a known distribution makes no queries. -/
noncomputable def sampleDist (μ : Str n → ℝ) : Alg (Str n) := .sample (toPMF μ) .ret

theorem run_sampleDist (h : Guide) (μ : Str n → ℝ) : (sampleDist μ).run h = toPMF μ := by
  simp [sampleDist, PMF.bind_pure]

theorem within_sampleDist (h : Guide) (μ : Str n → ℝ) : (sampleDist μ).Within h 0 :=
  Alg.Within.sample _ _ _ fun x _ => Alg.Within.ret x 0

open Classical in
/-- A leaf on which two members of `S` differ (a fixed string if there is none). -/
noncomputable def splitLeaf (S : Finset (Str n → ℝ)) : Str n :=
  if h : ∃ x : Str n, ∃ μ₁ ∈ S, ∃ μ₂ ∈ S, μ₁ x ≠ μ₂ x then h.choose else fbStr n

open Classical in
/-- Sample from some member of `S` (a fixed output if `S` is empty). -/
noncomputable def sampleSet (S : Finset (Str n → ℝ)) : Alg (Str n) :=
  if h : S.Nonempty then sampleDist h.choose else .ret (fbStr n)

open Classical in
/-- Exact identification with a budget of `k` queries: while two distinct candidates remain and
budget is left, query a leaf where two candidates differ and keep the consistent candidates. -/
noncomputable def identify : ℕ → Finset (Str n → ℝ) → Alg (Str n)
  | 0, S => sampleSet S
  | k + 1, S =>
      if ∃ μ₁ ∈ S, ∃ μ₂ ∈ S, μ₁ ≠ μ₂ then
        .query (List.ofFn (splitLeaf S)) fun v =>
          identify k (S.filter fun ν => ν (splitLeaf S) = v)
      else sampleSet S

/-- The identification algorithm for a finite class, with budget `|F| - 1`. -/
noncomputable def identAlg (F : Finset (Str n → ℝ)) : Alg (Str n) := identify (F.card - 1) F

theorem within_sampleSet (h : Guide) (S : Finset (Str n → ℝ)) (q : ℕ) :
    (sampleSet S).Within h q := by
  unfold sampleSet
  split_ifs
  · exact (within_sampleDist h _).mono (Nat.zero_le q)
  · exact Alg.Within.ret _ q

/-- The budget is a cap against every guide. -/
theorem within_identify (h : Guide) : ∀ (k : ℕ) (S : Finset (Str n → ℝ)),
    (identify k S).Within h k
  | 0, S => within_sampleSet h S 0
  | k + 1, S => by
      unfold identify
      split_ifs
      · exact Alg.Within.query _ _ k (within_identify h k _)
      · exact within_sampleSet h S (k + 1)

theorem run_sampleSet_of_eq (h : Guide) {S : Finset (Str n → ℝ)} {μ : Str n → ℝ}
    (hS : S = {μ}) : (sampleSet S).run h = toPMF μ := by
  have hne : S.Nonempty := by rw [hS]; exact Finset.singleton_nonempty μ
  have hch : hne.choose = μ := by
    have := hne.choose_spec
    exact Finset.mem_singleton.mp (hS ▸ this)
  simp only [sampleSet, hne, ↓reduceDIte, hch, run_sampleDist]

/-- Exactness: if the target lies in `S`, the leaves are exact and the budget is at least
`|S| - 1`, the output law is exactly the target. -/
theorem run_identify {h : Guide} {μ : Str n → ℝ} (hleaf : ∀ x : Str n, h (List.ofFn x) = μ x) :
    ∀ (k : ℕ) (S : Finset (Str n → ℝ)), μ ∈ S → S.card ≤ k + 1 →
      (identify k S).run h = toPMF μ
  | 0, S, hμS, hcard => by
      have hS : S = {μ} := (Finset.card_le_one_iff_subset_singleton.mp hcard).elim
        fun a ha => by
          have := ha hμS
          rw [Finset.mem_singleton] at this
          subst this
          exact Finset.Subset.antisymm ha (Finset.singleton_subset_iff.mpr hμS)
      exact run_sampleSet_of_eq h hS
  | k + 1, S, hμS, hcard => by
      classical
      unfold identify
      split_ifs with hdist
      · obtain ⟨μ₁, h₁, μ₂, h₂, h12⟩ := hdist
        have hex : ∃ x : Str n, ∃ μ₁ ∈ S, ∃ μ₂ ∈ S, μ₁ x ≠ μ₂ x := by
          obtain ⟨x, hx⟩ := Function.ne_iff.mp h12
          exact ⟨x, μ₁, h₁, μ₂, h₂, hx⟩
        set x := splitLeaf S with hx
        have hxdef : x = hex.choose := by simp only [hx, splitLeaf, hex, ↓reduceDIte]
        obtain ⟨ν₁, hν₁, ν₂, hν₂, hne⟩ := hxdef ▸ hex.choose_spec
        rw [Alg.run_query, hleaf x]
        set S' := S.filter fun ν => ν x = μ x
        have hμS' : μ ∈ S' := Finset.mem_filter.mpr ⟨hμS, rfl⟩
        have hlt : S'.card < S.card := by
          refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
          have e1 := (Finset.mem_filter.mp (hsub hν₁)).2
          have e2 := (Finset.mem_filter.mp (hsub hν₂)).2
          exact hne (e1.trans e2.symm)
        exact run_identify hleaf k S' hμS' (by omega)
      · push Not at hdist
        have hS : S = {μ} := by
          ext ν
          rw [Finset.mem_singleton]
          exact ⟨fun hν => hdist ν hν μ hμS, fun hν => hν ▸ hμS⟩
        exact run_sampleSet_of_eq h hS

/-- `pw-prop:upper` (first bound): exact identification. For every finite class `F` of
distributions and every model whose legal guides satisfy `eq:oracle`, the identification
algorithm samples exactly with cap `|F| - 1`. -/
theorem identAlg_solves {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) (F : Finset (Str n → ℝ))
    (hF : ∀ μ ∈ F, IsDist μ) : Solves Legal (F : Set (Str n → ℝ)) 0 (F.card - 1) (identAlg F) := by
  intro μ hμ h hl
  have hμF : μ ∈ F := hμ
  refine ⟨within_identify h _ F, ?_⟩
  have hcard : F.card ≤ F.card - 1 + 1 := by
    have := Finset.card_pos.mpr ⟨μ, hμF⟩
    omega
  rw [identAlg, run_identify (hL μ h hl).leaf _ F hμF hcard, lawR_toPMF (hF μ hμF), tv_self]

/-- Exact identification at any accuracy `δ ≥ 0`. -/
theorem identAlg_solves_of_nonneg {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) (F : Finset (Str n → ℝ))
    (hF : ∀ μ ∈ F, IsDist μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Solves Legal (F : Set (Str n → ℝ)) δ (F.card - 1) (identAlg F) := fun μ hμ h hl =>
  ⟨(identAlg_solves hL F hF μ hμ h hl).1, (identAlg_solves hL F hF μ hμ h hl).2.trans hδ⟩

/-- Every finite class of distributions is solvable at every accuracy `δ ≥ 0`, in every model
whose legal guides satisfy `eq:oracle`. -/
theorem exists_solves_finite {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) (F : Finset (Str n → ℝ))
    (hF : ∀ μ ∈ F, IsDist μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ q A, Solves Legal (F : Set (Str n → ℝ)) δ q A :=
  ⟨_, _, identAlg_solves_of_nonneg hL F hF hδ⟩

/-- `pw-prop:upper` (first bound) and Section 1.2: exact identification costs at most `M - 1`
queries, `Q(F,δ) ≤ M - 1` for every class of at most `M` distributions and every `δ ≥ 0`. -/
theorem Qcx_le_sub_one {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) {F : Finset (Str n → ℝ)}
    (hF : ∀ μ ∈ F, IsDist μ) {M : ℕ} (hM : F.card ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) :
    Qcx Legal (F : Set (Str n → ℝ)) δ ≤ M - 1 :=
  (Qcx_le (identAlg_solves_of_nonneg hL F hF hδ)).trans (by omega)

/-- The same bound for a finite class given as a set. -/
theorem Qcx_le_sub_one_of_finite {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) {F : Set (Str n → ℝ)} (hfin : F.Finite)
    (hF : ∀ μ ∈ F, IsDist μ) {M : ℕ} (hM : F.ncard ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) :
    Qcx Legal F δ ≤ M - 1 := by
  have h := Qcx_le_sub_one (F := hfin.toFinset) hL (fun μ hμ => hF μ (hfin.mem_toFinset.mp hμ))
    (M := M) (by rwa [← Set.ncard_eq_toFinset_card F hfin]) hδ
  rwa [Set.Finite.coe_toFinset] at h

/-- `thm:pointwise`: a singleton class requires no queries, in every model and at every accuracy
`δ ≥ 0`. -/
theorem Qcx_singleton {Legal : (Str n → ℝ) → Guide → Prop} {μ : Str n → ℝ} (hμ : IsDist μ)
    {δ : ℝ} (hδ : 0 ≤ δ) : Qcx Legal {μ} δ = 0 := by
  have hA : Solves Legal {μ} δ 0 (sampleDist μ) := by
    intro ν hν h _
    rw [Set.mem_singleton_iff] at hν
    subst hν
    refine ⟨within_sampleDist h ν, ?_⟩
    rw [run_sampleDist, lawR_toPMF hμ, tv_self]
    exact hδ
  exact Nat.eq_zero_of_le_zero (Qcx_le hA)

theorem Qpw_singleton {μ : Str n → ℝ} (hμ : IsDist μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Qpw {μ} δ = 0 := Qcx_singleton hμ hδ

theorem Qsafe_singleton {μ : Str n → ℝ} (hμ : IsDist μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Qsafe {μ} δ = 0 := Qcx_singleton hμ hδ

/-- Exact identification in the pointwise model: `Q_pw(F,δ) ≤ M - 1`. -/
theorem Qpw_le_sub_one {F : Finset (Str n → ℝ)} (hF : ∀ μ ∈ F, IsDist μ) {M : ℕ}
    (hM : F.card ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) : Qpw (F : Set (Str n → ℝ)) δ ≤ M - 1 :=
  Qcx_le_sub_one (fun _ _ hl => hl.1) hF hM hδ

/-- Exact identification in the safe model: `Q_safe(F,δ) ≤ M - 1`. -/
theorem Qsafe_le_sub_one {F : Finset (Str n → ℝ)} (hF : ∀ μ ∈ F, IsDist μ) {M : ℕ}
    (hM : F.card ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) : Qsafe (F : Set (Str n → ℝ)) δ ≤ M - 1 :=
  Qcx_le_sub_one (fun _ _ hl => hl.1) hF hM hδ

/-! ### Worst cases over classes of at most `M` distributions -/

/-- The worst-case complexity `Q(n,M,δ)` over classes of at most `M` distributions on `n` bits. -/
noncomputable def QcxNM {n : ℕ} (Legal : (Str n → ℝ) → Guide → Prop) (M : ℕ) (δ : ℝ) : ℕ :=
  sSup {q | ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
    Qcx Legal (F : Set (Str n → ℝ)) δ = q}

/-- `Q_pw(n,M,δ)`. -/
noncomputable def QpwNM (n M : ℕ) (δ : ℝ) : ℕ := QcxNM (n := n) (PwLegal (9 / 4)) M δ

/-- `Q_safe(n,M,δ)`. -/
noncomputable def QsafeNM (n M : ℕ) (δ : ℝ) : ℕ := QcxNM (n := n) (SafeLegal (9 / 4) (9 / 4)) M δ

/-- An upper bound on every class of at most `M` distributions bounds the worst case. -/
theorem QcxNM_le {Legal : (Str n → ℝ) → Guide → Prop} {M : ℕ} {δ : ℝ} {b : ℕ}
    (hb : ∀ F : Finset (Str n → ℝ), F.card ≤ M → (∀ μ ∈ F, IsDist μ) →
      Qcx Legal (F : Set (Str n → ℝ)) δ ≤ b) : QcxNM Legal M δ ≤ b := by
  refine csSup_le ⟨_, ∅, by simp, by simp, rfl⟩ ?_
  rintro q ⟨F, hFM, hF, rfl⟩
  exact hb F hFM hF

/-- Each class of at most `M` distributions is bounded by the worst case. -/
theorem le_QcxNM {Legal : (Str n → ℝ) → Guide → Prop} (hL : ∀ μ h, Legal μ h → IsOracle μ h)
    {M : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {F : Finset (Str n → ℝ)} (hFM : F.card ≤ M)
    (hF : ∀ μ ∈ F, IsDist μ) : Qcx Legal (F : Set (Str n → ℝ)) δ ≤ QcxNM Legal M δ := by
  refine le_csSup ⟨M - 1, ?_⟩ ⟨F, hFM, hF, rfl⟩
  rintro q ⟨G, hGM, hG, rfl⟩
  exact Qcx_le_sub_one hL hG hGM hδ

/-- The worst case is at most `M - 1`. -/
theorem QcxNM_le_sub_one {Legal : (Str n → ℝ) → Guide → Prop}
    (hL : ∀ μ h, Legal μ h → IsOracle μ h) {M : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    QcxNM Legal M δ ≤ M - 1 :=
  QcxNM_le fun _ hFM hF => Qcx_le_sub_one hL hF hFM hδ

theorem QpwNM_le_sub_one (n M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : QpwNM n M δ ≤ M - 1 :=
  QcxNM_le_sub_one (fun _ _ hl => hl.1) hδ

theorem QsafeNM_le_sub_one (n M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : QsafeNM n M δ ≤ M - 1 :=
  QcxNM_le_sub_one (fun _ _ hl => hl.1) hδ

end Upper
end LearningGuided
