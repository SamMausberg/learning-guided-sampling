import LearningGuided.Basic

/-!
# Adaptive randomized query algorithms

An algorithm is a tree whose nodes either return an output, query the guide at a word and
continue with a function of the real answer, or draw from a known law (`PMF`) and continue with a
function of the draw. Randomness and computation on known data are free; only `query` nodes are
charged. Sampling from a known distribution at the end ("output a fresh draw from `U_n`") is a
`sample` node followed by `ret`.

* `Alg.run h A` is the complete (unconditional) output law of `A` against the guide `h`.
* `Alg.Within h A q`: every execution of `A` against `h` makes at most `q` queries. This is the
  deterministic cap of Section 1.1 (all executions with positive probability).
* `Solves Legal F δ q A`: against every target `μ ∈ F` and every legal guide `h` for `μ`, the
  algorithm `A` respects the cap `q` and its output law is within total variation `δ` of `μ`.
* `Qcx Legal F δ` is the minimax capped query complexity: the least such `q`.
  `Qpw F δ` and `Qsafe F δ` are `Q_pw(F,δ)` and `Q_safe(F,δ)` with `R = C = 9/4`.

The generic counting lemmas `equality_counting` (Lemma `lem:equality` and its uses) and
`binary_counting` (the `2^q` transcript bound) and the zero-query obstruction are proved here.

Two remarks on the model. First, randomness is a `PMF`, so it has countable support. This loses
nothing for the lower bounds: each lower bound is proved against a finite family of hard guides,
and its proof averages a bound that holds for every deterministic tree. Second, `Qcx` is an
infimum over `ℕ`, so it would be `0` for an unsolvable class. This never happens for the classes
in the paper: every class of distributions is solvable at every `δ ≥ 0` in every model whose legal
guides satisfy `IsOracle`, by querying all leaves (`Sec2.exists_solver`), and every upper bound in
this library is proved from an explicit solver.
-/

open scoped BigOperators ENNReal

namespace LearningGuided

/-- Adaptive randomized query algorithms with outputs in `β`. -/
inductive Alg (β : Type) : Type 1 where
  /-- Return a known value. -/
  | ret : β → Alg β
  /-- Query the guide at a word and continue with the answer. -/
  | query : List Bool → (ℝ → Alg β) → Alg β
  /-- Draw from a known law (free randomness) and continue with the draw. -/
  | sample {γ : Type} : PMF γ → (γ → Alg β) → Alg β

namespace Alg

variable {β : Type}

/-- The output law of an algorithm against a fixed guide. -/
noncomputable def run (h : Guide) : Alg β → PMF β
  | ret b => PMF.pure b
  | query u k => run h (k (h u))
  | sample p k => p.bind fun g => run h (k g)

@[simp] theorem run_ret (h : Guide) (b : β) : run h (ret b) = PMF.pure b := rfl

@[simp] theorem run_query (h : Guide) (u : List Bool) (k : ℝ → Alg β) :
    run h (query u k) = run h (k (h u)) := rfl

@[simp] theorem run_sample (h : Guide) {γ : Type} (p : PMF γ) (k : γ → Alg β) :
    run h (sample p k) = p.bind fun g => run h (k g) := rfl

/-- `Within h A q`: every execution of `A` against `h` with positive probability makes at most
`q` guide queries. -/
inductive Within (h : Guide) : Alg β → ℕ → Prop
  | ret (b : β) (q : ℕ) : Within h (ret b) q
  | query (u : List Bool) (k : ℝ → Alg β) (q : ℕ) :
      Within h (k (h u)) q → Within h (query u k) (q + 1)
  | sample {γ : Type} (p : PMF γ) (k : γ → Alg β) (q : ℕ) :
      (∀ g ∈ p.support, Within h (k g) q) → Within h (sample p k) q

theorem Within.mono {h : Guide} {A : Alg β} {q q' : ℕ} (hA : Within h A q) (hq : q ≤ q') :
    Within h A q' := by
  induction hA generalizing q' with
  | ret b q => exact Within.ret b q'
  | query u k q _ ih =>
      obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
      exact Within.query u k r (ih (by omega))
  | sample p k q _ ih => exact Within.sample p k q' fun g hg => ih g hg hq

theorem within_query_iff {h : Guide} {u : List Bool} {k : ℝ → Alg β} {q : ℕ} :
    Within h (query u k) q ↔ ∃ r, q = r + 1 ∧ Within h (k (h u)) r := by
  constructor
  · intro hw
    cases hw with
    | query _ _ r hr => exact ⟨r, rfl, hr⟩
  · rintro ⟨r, rfl, hr⟩
    exact Within.query u k r hr

theorem within_sample_iff {h : Guide} {γ : Type} {p : PMF γ} {k : γ → Alg β} {q : ℕ} :
    Within h (sample p k) q ↔ ∀ g ∈ p.support, Within h (k g) q := by
  constructor
  · intro hw
    cases hw with
    | sample _ _ _ hg => exact hg
  · intro hg
    exact Within.sample p k q hg

end Alg

/-- The output law as a real-valued function. -/
noncomputable def lawR {β : Type} (p : PMF β) : β → ℝ := fun b => (p b).toReal

theorem lawR_isDist {n : ℕ} (p : PMF (Str n)) : IsDist (lawR p) := by
  refine ⟨fun x => ENNReal.toReal_nonneg, ?_⟩
  unfold lawR
  rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)]
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  simp [h]

/-- `A` solves the class `F` at accuracy `δ` with cap `q` in the model `Legal`. -/
def Solves {n : ℕ} (Legal : (Str n → ℝ) → Guide → Prop) (F : Set (Str n → ℝ)) (δ : ℝ) (q : ℕ)
    (A : Alg (Str n)) : Prop :=
  ∀ μ ∈ F, ∀ h, Legal μ h → A.Within h q ∧ tv (lawR (A.run h)) μ ≤ δ

/-- Minimax capped query complexity of a specified class in a given model. -/
noncomputable def Qcx {n : ℕ} (Legal : (Str n → ℝ) → Guide → Prop) (F : Set (Str n → ℝ))
    (δ : ℝ) : ℕ :=
  sInf {q | ∃ A, Solves Legal F δ q A}

/-- `Q_pw(F,δ)`: pointwise factor `R = 9/4`. -/
noncomputable def Qpw {n : ℕ} (F : Set (Str n → ℝ)) (δ : ℝ) : ℕ :=
  Qcx (PwLegal (9 / 4)) F δ

/-- `Q_safe(F,δ)`: safety and stopped capacity with `R = C = 9/4`. -/
noncomputable def Qsafe {n : ℕ} (F : Set (Str n → ℝ)) (δ : ℝ) : ℕ :=
  Qcx (SafeLegal (9 / 4) (9 / 4)) F δ

theorem Qcx_le {n : ℕ} {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ : ℝ}
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal F δ q A) : Qcx Legal F δ ≤ q :=
  Nat.sInf_le ⟨A, hA⟩

theorem le_Qcx {n : ℕ} {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ : ℝ}
    {b : ℕ} (hex : ∃ q A, Solves Legal F δ q A)
    (hlow : ∀ q A, Solves Legal F δ q A → b ≤ q) : b ≤ Qcx Legal F δ := by
  obtain ⟨q, A, hA⟩ := hex
  exact le_csInf ⟨q, A, hA⟩ fun q' ⟨A', hA'⟩ => hlow q' A' hA'

theorem Qcx_eq {n : ℕ} {Legal : (Str n → ℝ) → Guide → Prop} {F : Set (Str n → ℝ)} {δ : ℝ}
    {q : ℕ} {A : Alg (Str n)} (hA : Solves Legal F δ q A)
    (hlow : ∀ q' A', Solves Legal F δ q' A' → q ≤ q') : Qcx Legal F δ = q :=
  le_antisymm (Qcx_le hA) (le_Qcx ⟨q, A, hA⟩ hlow)

/-! ### Probability of an event under an output law -/

/-- An event's probability under the output law, in `ℝ≥0∞`. -/
noncomputable def probE {β : Type} (p : PMF β) (E : Set β) : ℝ≥0∞ := p.toOuterMeasure E

theorem probE_le_one {β : Type} (p : PMF β) (E : Set β) : probE p E ≤ 1 := by
  unfold probE
  calc p.toOuterMeasure E ≤ p.toOuterMeasure Set.univ := by gcongr; exact Set.subset_univ E
    _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).2 (Set.subset_univ _)

open Classical in
/-- Bounded overlap: every outcome lies in at most `K` of the events `E θ`, `θ ∈ S`, so the
probabilities of the events sum to at most `K` under any single law. -/
theorem sum_probE_le_of_overlap {β Θ : Type} (p : PMF β) (S : Finset Θ) (E : Θ → Set β)
    (K : ℕ) (hK : ∀ b, (S.filter fun θ => b ∈ E θ).card ≤ K) :
    ∑ θ ∈ S, probE p (E θ) ≤ K := by
  simp only [probE, PMF.toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc ∑' b, ∑ θ ∈ S, (E θ).indicator p b
      = ∑' b, p b * ((S.filter fun θ => b ∈ E θ).card : ℝ≥0∞) := by
        congr 1; ext b
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        by_cases hb : b ∈ E θ <;> simp [Set.indicator, hb]
    _ ≤ ∑' b, p b * (K : ℝ≥0∞) := by
        gcongr with b
        exact_mod_cast hK b
    _ = K := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-! ### Counting lemmas -/

/-- A family of guides indexed by hidden keys has *equality structure* if every query is
answered by a public value except possibly for one key: equivalently, each query can be simulated
by at most one equality test of a proposed key. -/
def EqualityStructure {Θ : Type} (H : Θ → Guide) : Prop :=
  ∀ u : List Bool, ∃ e : Option Θ, ∃ v : ℝ, ∀ θ, e ≠ some θ → H θ u = v

open Classical in
/-- Equality-query counting (Lemma `lem:equality`, in the summed form used throughout).
If every query is simulated by at most one equality test and every outcome lies in at most `K`
of the success events, then an algorithm with cap `q` against every guide `H θ`, `θ ∈ S`,
has summed success probability at most `q + K`. With `K = 1` and a uniform prior on `S` this is
the bound `(q+1)/|S|`. -/
theorem equality_counting {β Θ : Type} (H : Θ → Guide) (hH : EqualityStructure H)
    (E : Θ → Set β) (K : ℕ) (A : Alg β) :
    ∀ (S : Finset Θ) (q : ℕ), (∀ b, (S.filter fun θ => b ∈ E θ).card ≤ K) →
      (∀ θ ∈ S, A.Within (H θ) q) →
      ∑ θ ∈ S, probE (A.run (H θ)) (E θ) ≤ q + K := by
  classical
  induction A with
  | ret b =>
      intro S q hK _
      calc ∑ θ ∈ S, probE ((Alg.ret b).run (H θ)) (E θ)
          = ∑ θ ∈ S, probE (PMF.pure b) (E θ) := rfl
        _ ≤ K := sum_probE_le_of_overlap _ S E K hK
        _ ≤ q + K := le_add_self
  | query u k ih =>
      intro S q hK hW
      obtain ⟨e, v, hv⟩ := hH u
      by_cases hS : S.Nonempty
      · obtain ⟨θ₀, hθ₀⟩ := hS
        obtain ⟨r, hr, -⟩ := Alg.within_query_iff.mp (hW θ₀ hθ₀)
        subst hr
        set S' := S.filter fun θ => e ≠ some θ with hS'
        have hS'sub : S' ⊆ S := Finset.filter_subset _ _
        have hrest : (S.filter fun θ => ¬ e ≠ some θ).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, ne_eq, not_not] at ha hb
          exact Option.some_injective _ (ha.2.symm.trans hb.2)
        have hW' : ∀ θ ∈ S', (k v).Within (H θ) r := by
          intro θ hθ
          have hθ' := Finset.mem_filter.mp hθ
          obtain ⟨r', hr', hw⟩ := Alg.within_query_iff.mp (hW θ hθ'.1)
          have : r' = r := by omega
          subst this
          rwa [hv θ hθ'.2] at hw
        have hK' : ∀ b, (S'.filter fun θ => b ∈ E θ).card ≤ K := fun b =>
          (Finset.card_le_card (Finset.filter_subset_filter _ hS'sub)).trans (hK b)
        have h1 : ∑ θ ∈ S', probE ((Alg.query u k).run (H θ)) (E θ) ≤ r + K := by
          calc ∑ θ ∈ S', probE ((Alg.query u k).run (H θ)) (E θ)
              = ∑ θ ∈ S', probE ((k v).run (H θ)) (E θ) := by
                refine Finset.sum_congr rfl fun θ hθ => ?_
                rw [Alg.run_query, hv θ (Finset.mem_filter.mp hθ).2]
            _ ≤ r + K := ih v S' r hK' hW'
        have h2 : ∑ θ ∈ S.filter (fun θ => ¬ e ≠ some θ),
            probE ((Alg.query u k).run (H θ)) (E θ) ≤ 1 :=
          calc _ ≤ ∑ θ ∈ S.filter (fun θ => ¬ e ≠ some θ), (1 : ℝ≥0∞) :=
                Finset.sum_le_sum fun θ _ => probE_le_one _ _
            _ = (S.filter fun θ => ¬ e ≠ some θ).card := by simp
            _ ≤ 1 := by exact_mod_cast hrest
        rw [← Finset.sum_filter_add_sum_filter_not S (fun θ => e ≠ some θ)]
        calc _ ≤ (r + K : ℝ≥0∞) + 1 := add_le_add h1 h2
          _ = ((r + 1 : ℕ) : ℝ≥0∞) + K := by push_cast; ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
        simp
  | sample p k ih =>
      intro S q hK hW
      have hW' : ∀ g ∈ p.support, ∀ θ ∈ S, (k g).Within (H θ) q := fun g hg θ hθ =>
        Alg.within_sample_iff.mp (hW θ hθ) g hg
      calc ∑ θ ∈ S, probE ((Alg.sample p k).run (H θ)) (E θ)
          = ∑ θ ∈ S, ∑' g, p g * probE ((k g).run (H θ)) (E θ) := by
            refine Finset.sum_congr rfl fun θ _ => ?_
            simp [probE, PMF.toOuterMeasure_bind_apply]
        _ = ∑' g, p g * ∑ θ ∈ S, probE ((k g).run (H θ)) (E θ) := by
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            congr 1; ext g
            rw [Finset.mul_sum]
        _ ≤ ∑' g, p g * ((q : ℝ≥0∞) + K) := by
            refine ENNReal.tsum_le_tsum fun g => ?_
            by_cases hg : g ∈ p.support
            · exact mul_le_mul_right (ih g S q hK (hW' g hg)) _
            · rw [PMF.mem_support_iff, not_not] at hg
              simp [hg]
        _ = q + K := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- A family of guides has *binary answers* if each query has at most two possible answers as
the hidden key varies. -/
def BinaryAnswers {Θ : Type} (H : Θ → Guide) : Prop :=
  ∀ u : List Bool, ∃ v₀ v₁ : ℝ, ∀ θ, H θ u = v₀ ∨ H θ u = v₁

open Classical in
/-- The transcript-counting bound: with at most two answers per query, an algorithm with cap `q`
has at most `2^q` transcripts, so its summed success probability is at most `2^q K`. -/
theorem binary_counting {β Θ : Type} (H : Θ → Guide) (hH : BinaryAnswers H)
    (E : Θ → Set β) (K : ℕ) (A : Alg β) :
    ∀ (S : Finset Θ) (q : ℕ), (∀ b, (S.filter fun θ => b ∈ E θ).card ≤ K) →
      (∀ θ ∈ S, A.Within (H θ) q) →
      ∑ θ ∈ S, probE (A.run (H θ)) (E θ) ≤ 2 ^ q * K := by
  classical
  induction A with
  | ret b =>
      intro S q hK _
      calc ∑ θ ∈ S, probE ((Alg.ret b).run (H θ)) (E θ)
          = ∑ θ ∈ S, probE (PMF.pure b) (E θ) := rfl
        _ ≤ K := sum_probE_le_of_overlap _ S E K hK
        _ ≤ 2 ^ q * K := le_mul_of_one_le_left (zero_le) (one_le_pow₀ (by norm_num))
  | query u k ih =>
      intro S q hK hW
      obtain ⟨v₀, v₁, hv⟩ := hH u
      by_cases hS : S.Nonempty
      · obtain ⟨θ₀, hθ₀⟩ := hS
        obtain ⟨r, hr, -⟩ := Alg.within_query_iff.mp (hW θ₀ hθ₀)
        subst hr
        have hpart : ∀ (w : ℝ) (T : Finset Θ), T ⊆ S → (∀ θ ∈ T, H θ u = w) →
            ∑ θ ∈ T, probE ((Alg.query u k).run (H θ)) (E θ) ≤ 2 ^ r * K := by
          intro w T hT hTw
          have hWT : ∀ θ ∈ T, (k w).Within (H θ) r := by
            intro θ hθ
            obtain ⟨r', hr', hw⟩ := Alg.within_query_iff.mp (hW θ (hT hθ))
            have : r' = r := by omega
            subst this
            rwa [hTw θ hθ] at hw
          have hKT : ∀ b, (T.filter fun θ => b ∈ E θ).card ≤ K := fun b =>
            (Finset.card_le_card (Finset.filter_subset_filter _ hT)).trans (hK b)
          calc ∑ θ ∈ T, probE ((Alg.query u k).run (H θ)) (E θ)
              = ∑ θ ∈ T, probE ((k w).run (H θ)) (E θ) := by
                refine Finset.sum_congr rfl fun θ hθ => ?_
                rw [Alg.run_query, hTw θ hθ]
            _ ≤ 2 ^ r * K := ih w T r hKT hWT
        rw [← Finset.sum_filter_add_sum_filter_not S (fun θ => H θ u = v₀)]
        have h0 := hpart v₀ (S.filter fun θ => H θ u = v₀) (Finset.filter_subset _ _)
          (fun θ hθ => (Finset.mem_filter.mp hθ).2)
        have h1 := hpart v₁ (S.filter fun θ => ¬ H θ u = v₀) (Finset.filter_subset _ _)
          (fun θ hθ => ((hv θ).resolve_left (Finset.mem_filter.mp hθ).2))
        calc _ ≤ 2 ^ r * (K : ℝ≥0∞) + 2 ^ r * K := add_le_add h0 h1
          _ = 2 ^ (r + 1) * K := by ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
        simp
  | sample p k ih =>
      intro S q hK hW
      have hW' : ∀ g ∈ p.support, ∀ θ ∈ S, (k g).Within (H θ) q := fun g hg θ hθ =>
        Alg.within_sample_iff.mp (hW θ hθ) g hg
      calc ∑ θ ∈ S, probE ((Alg.sample p k).run (H θ)) (E θ)
          = ∑ θ ∈ S, ∑' g, p g * probE ((k g).run (H θ)) (E θ) := by
            refine Finset.sum_congr rfl fun θ _ => ?_
            simp [probE, PMF.toOuterMeasure_bind_apply]
        _ = ∑' g, p g * ∑ θ ∈ S, probE ((k g).run (H θ)) (E θ) := by
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
            congr 1; ext g
            rw [Finset.mul_sum]
        _ ≤ ∑' g, p g * (2 ^ q * (K : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun g => ?_
            by_cases hg : g ∈ p.support
            · exact mul_le_mul_right (ih g S q hK (hW' g hg)) _
            · rw [PMF.mem_support_iff, not_not] at hg
              simp [hg]
        _ = 2 ^ q * K := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- With zero queries, the output law does not depend on the guide. -/
theorem run_eq_of_within_zero {β : Type} (A : Alg β) :
    ∀ {h h' : Guide}, A.Within h 0 → A.Within h' 0 → A.run h = A.run h' := by
  induction A with
  | ret b => intro h h' _ _; rfl
  | query u k _ =>
      intro h h' hw _
      obtain ⟨r, hr, -⟩ := Alg.within_query_iff.mp hw
      omega
  | sample p k ih =>
      intro h h' hw hw'
      simp only [Alg.run_sample]
      ext b
      simp only [PMF.bind_apply]
      refine tsum_congr fun g => ?_
      by_cases hg : g ∈ p.support
      · rw [ih g (Alg.within_sample_iff.mp hw g hg) (Alg.within_sample_iff.mp hw' g hg)]
      · rw [PMF.mem_support_iff, not_not] at hg
        simp [hg]

/-- The zero-query obstruction: if two targets are farther apart than `2δ` in total variation,
no algorithm that makes no queries against their legal guides is `δ`-accurate for both. -/
theorem zero_query_obstruction {n : ℕ} {μ₁ μ₂ : Str n → ℝ} {h₁ h₂ : Guide} {δ : ℝ}
    (hfar : 2 * δ < tv μ₁ μ₂) (A : Alg (Str n)) (hw₁ : A.Within h₁ 0) (hw₂ : A.Within h₂ 0)
    (hacc₁ : tv (lawR (A.run h₁)) μ₁ ≤ δ) (hacc₂ : tv (lawR (A.run h₂)) μ₂ ≤ δ) : False := by
  rw [run_eq_of_within_zero A hw₁ hw₂] at hacc₁
  have := tv_triangle μ₁ (lawR (A.run h₂)) μ₂
  rw [tv_comm] at hacc₁
  linarith

/-- The probability that the output lies in a finite set, as a real number. -/
theorem probE_finset_toReal {n : ℕ} (p : PMF (Str n)) (E : Finset (Str n)) :
    (probE p (E : Set (Str n))).toReal = ∑ x ∈ E, lawR p x := by
  classical
  simp only [probE, lawR]
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ← ENNReal.toReal_sum]
  · congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ E)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => x ∉ E), (E : Set (Str n)).indicator p x = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp [Set.indicator, (Finset.mem_filter.mp hx).2]
    rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_congr rfl fun x hx => by simp [Set.indicator, hx]
  · intro x _; exact p.apply_ne_top x

/-- Accuracy transfers event probabilities: if `TV(law, μ) ≤ δ`, then every finite event has law
probability at least `μ(E) - δ`. -/
theorem prob_ge_of_tv {n : ℕ} {p : PMF (Str n)} {μ : Str n → ℝ} (hμ : IsDist μ) {δ : ℝ}
    (hδ : tv (lawR p) μ ≤ δ) (E : Finset (Str n)) :
    ∑ x ∈ E, μ x - δ ≤ (probE p (E : Set (Str n))).toReal := by
  rw [probE_finset_toReal]
  have := sum_le_sum_add_tv (lawR_isDist p).2 hμ.2 E
  linarith

end LearningGuided
