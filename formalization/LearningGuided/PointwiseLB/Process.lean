import LearningGuided.PointwiseLB.State

/-!
# The lazily sampled transcript process

For a test tree `t`, a state `σ` and a *label kernel* `K` (the probability `K σ a` that a newly
revealed label of table `a` equals one), `val K L g t σ` is the expected payoff `g` of the
process that runs `t` from the state `σ`, where

* a fresh test of location `i` at an undiscovered row with excluded set `E` succeeds with
  probability `1/(ℓ - |E|)` (Lemma `pw-lem:posterior`), and on success reveals a label drawn
  from `K`;
* a test whose outcome is determined by the state does not change the state;
* the process is stopped as soon as `L ≤ D` rows are discovered (payoff `g σ none`).

With `L = 2W + 1` the process is never stopped. For the hard prior with root `b` the kernel is
`kap b`, the sampling-without-replacement probability `(m_{a,b} - s_a)/(W - t_a)`, and
`avg_eq_val` proves that `val` is exactly the average over the consistent tables of the true
output probabilities (the lazy-sampling form of Lemma `pw-lem:posterior`).
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

/-! ### Real-valued facts about PMFs -/

theorem pmf_summable_toReal {γ : Type} (p : PMF γ) : Summable fun x => (p x).toReal :=
  ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)

theorem pmf_tsum_toReal {γ : Type} (p : PMF γ) : ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe, ENNReal.toReal_one]

theorem summable_pmf_mul {γ : Type} (p : PMF γ) {v : γ → ℝ} {M : ℝ} (hv : ∀ x, |v x| ≤ M) :
    Summable fun x => (p x).toReal * v x := by
  refine Summable.of_norm_bounded (g := fun x => (p x).toReal * M)
    ((pmf_summable_toReal p).mul_right M) fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hv x) ENNReal.toReal_nonneg

theorem tsum_pmf_const {γ : Type} (p : PMF γ) (c : ℝ) : ∑' x, (p x).toReal * c = c := by
  rw [tsum_mul_right, pmf_tsum_toReal, one_mul]

theorem tsum_pmf_le {γ : Type} (p : PMF γ) {v : γ → ℝ} {M c : ℝ} (hv : ∀ x, |v x| ≤ M)
    (hc : ∀ x, p x ≠ 0 → v x ≤ c) : ∑' x, (p x).toReal * v x ≤ c := by
  have hle : ∀ x, (p x).toReal * v x ≤ (p x).toReal * c := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left (hc x hx) ENNReal.toReal_nonneg
  calc ∑' x, (p x).toReal * v x ≤ ∑' x, (p x).toReal * c :=
        Summable.tsum_le_tsum hle (summable_pmf_mul p hv)
          ((pmf_summable_toReal p).mul_right c)
    _ = c := tsum_pmf_const p c

theorem le_tsum_pmf {γ : Type} (p : PMF γ) {v : γ → ℝ} {M c : ℝ} (hv : ∀ x, |v x| ≤ M)
    (hc : ∀ x, p x ≠ 0 → c ≤ v x) : c ≤ ∑' x, (p x).toReal * v x := by
  have := tsum_pmf_le p (v := fun x => -v x) (M := M) (c := -c) (by simpa using hv)
    (fun x hx => by have := hc x hx; linarith)
  simp only [mul_neg] at this
  rw [tsum_neg] at this
  linarith

theorem abs_tsum_pmf_le {γ : Type} (p : PMF γ) {v : γ → ℝ} {M : ℝ} (hv : ∀ x, |v x| ≤ M) :
    |∑' x, (p x).toReal * v x| ≤ M := by
  rw [abs_le]
  constructor
  · exact le_tsum_pmf p hv fun x _ => by have := hv x; rw [abs_le] at this; linarith
  · exact tsum_pmf_le p hv fun x _ => by have := hv x; rw [abs_le] at this; linarith

namespace Prm

variable (P : Prm) {β : Type}

/-- `d' = ℓ - |E|`, the number of remaining locations, as a real. -/
noncomputable def dd (E : Finset (Fin P.ℓ)) : ℝ := (P.ℓ : ℝ) - E.card

theorem card_lt_of_notMem {E : Finset (Fin P.ℓ)} {i : Fin P.ℓ} (hi : i ∉ E) : E.card < P.ℓ := by
  have h1 : E ⊆ Finset.univ.erase i := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hx), Finset.mem_univ _⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h2
  have := P.hℓ
  omega

theorem one_le_dd {E : Finset (Fin P.ℓ)} {i : Fin P.ℓ} (hi : i ∉ E) : 1 ≤ P.dd E := by
  unfold dd
  have := P.card_lt_of_notMem hi
  have h : ((E.card + 1 : ℕ) : ℝ) ≤ P.ℓ := by exact_mod_cast this
  push_cast at h; linarith

/-- One fresh test: success with probability `1/d'`, then label one with probability `κ`. -/
noncomputable def mixF (κ d v1 v0 vf : ℝ) : ℝ := (κ * v1 + (1 - κ) * v0) / d + (d - 1) / d * vf

theorem mixF_le {κ d v1 v0 vf c1 c0 cf : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hd : 1 ≤ d)
    (h1 : 0 < κ → v1 ≤ c1) (h0 : κ < 1 → v0 ≤ c0) (hf : 1 < d → vf ≤ cf) :
    mixF κ d v1 v0 vf ≤ mixF κ d c1 c0 cf := by
  unfold mixF
  have hdpos : 0 < d := by linarith
  have e1 : κ * v1 ≤ κ * c1 := by
    rcases hκ0.lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (h1 h) hκ0
    · rw [← h]; simp
  have e0 : (1 - κ) * v0 ≤ (1 - κ) * c0 := by
    rcases hκ1.lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (h0 h) (by linarith)
    · rw [h]; simp
  have ef : (d - 1) / d * vf ≤ (d - 1) / d * cf := by
    rcases hd.lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (hf h) (div_nonneg (by linarith) hdpos.le)
    · rw [← h]; simp
  have := div_le_div_of_nonneg_right (add_le_add e1 e0) hdpos.le
  linarith

theorem mixF_const {κ d c : ℝ} (hd : d ≠ 0) : mixF κ d c c c = c := by
  unfold mixF; field_simp; ring

theorem mixF_add (κ d v1 v0 vf w1 w0 wf : ℝ) :
    mixF κ d (v1 + w1) (v0 + w0) (vf + wf) = mixF κ d v1 v0 vf + mixF κ d w1 w0 wf := by
  unfold mixF; ring

theorem mixF_smul (κ d c v1 v0 vf : ℝ) :
    mixF κ d (c * v1) (c * v0) (c * vf) = c * mixF κ d v1 v0 vf := by
  unfold mixF; ring

/-- The expected payoff of the lazily sampled, possibly stopped, process. -/
noncomputable def val (K : P.State → Bool → ℝ) (L : ℕ) (g : P.State → Option β → ℝ) :
    TT P β → P.State → ℝ
  | .ret b, σ => if L ≤ P.D σ then g σ none else g σ (some b)
  | .sample p k, σ =>
      if L ≤ P.D σ then g σ none else ∑' x, (p x).toReal * val K L g (k x) σ
  | .test a j i kf ks, σ =>
      if L ≤ P.D σ then g σ none else
        match σ a j with
        | .disc i₀ y₀ => if i = i₀ then val K L g (ks y₀) σ else val K L g kf σ
        | .undisc E =>
            if i ∈ E then val K L g kf σ else
              mixF (K σ a) (P.dd E) (val K L g (ks true) (P.setDisc σ a j i true))
                (val K L g (ks false) (P.setDisc σ a j i false))
                (val K L g kf (P.setExcl σ a j E i))

section Equations

variable {P} {K : P.State → Bool → ℝ} {L : ℕ} {g : P.State → Option β → ℝ}

theorem val_stop {σ : P.State} (h : L ≤ P.D σ) (t : TT P β) : P.val K L g t σ = g σ none := by
  cases t <;> simp [val, h]

theorem val_ret {σ : P.State} (h : ¬ L ≤ P.D σ) (b : β) :
    P.val K L g (.ret b) σ = g σ (some b) := by simp [val, h]

theorem val_sample {σ : P.State} (h : ¬ L ≤ P.D σ) {γ : Type} (p : PMF γ) (k : γ → TT P β) :
    P.val K L g (.sample p k) σ = ∑' x, (p x).toReal * P.val K L g (k x) σ := by
  simp [val, h]

theorem val_test_disc {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k} {i i₀ : Fin P.ℓ}
    {y₀ : Bool} (hσ : σ a j = .disc i₀ y₀) (kf : TT P β) (ks : Bool → TT P β) :
    P.val K L g (.test a j i kf ks) σ =
      if i = i₀ then P.val K L g (ks y₀) σ else P.val K L g kf σ := by
  simp only [val, h, ite_false, hσ]

theorem val_test_mem {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k} {i : Fin P.ℓ}
    {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (hi : i ∈ E) (kf : TT P β)
    (ks : Bool → TT P β) : P.val K L g (.test a j i kf ks) σ = P.val K L g kf σ := by
  simp only [val, h, ite_false, hσ, hi, ite_true]

theorem val_test_fresh {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k} {i : Fin P.ℓ}
    {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (hi : i ∉ E) (kf : TT P β)
    (ks : Bool → TT P β) :
    P.val K L g (.test a j i kf ks) σ =
      mixF (K σ a) (P.dd E) (P.val K L g (ks true) (P.setDisc σ a j i true))
        (P.val K L g (ks false) (P.setDisc σ a j i false))
        (P.val K L g kf (P.setExcl σ a j E i)) := by
  simp only [val, h, ite_false, hσ, hi]

end Equations

/-- A label kernel takes values in `[0,1]`. -/
def KerOK (K : P.State → Bool → ℝ) : Prop := ∀ σ a, 0 ≤ K σ a ∧ K σ a ≤ 1

theorem val_abs_le {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ)
    {g : P.State → Option β → ℝ} {M : ℝ} (hg : ∀ σ o, |g σ o| ≤ M) :
    ∀ (t : TT P β) σ, |P.val K L g t σ| ≤ M := by
  intro t
  induction t with
  | ret b => intro σ; simp only [val]; split_ifs <;> exact hg _ _
  | sample p k ih =>
      intro σ; simp only [val]; split_ifs
      · exact hg _ _
      · exact abs_tsum_pmf_le p fun x => ih x σ
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [val]; split_ifs
      · exact hg _ _
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · rename_i E _
          split_ifs with hi
          · exact ihf _
          · have hd := P.one_le_dd hi
            have hM : 0 ≤ M := le_trans (abs_nonneg _) (hg σ none)
            obtain ⟨hk0, hk1⟩ := hK σ a
            rw [abs_le]
            constructor
            · have := mixF_le (v1 := -M) (v0 := -M) (vf := -M)
                (c1 := P.val K L g (ks true) (P.setDisc σ a j i true))
                (c0 := P.val K L g (ks false) (P.setDisc σ a j i false))
                (cf := P.val K L g kf (P.setExcl σ a j E i)) hk0 hk1 hd
                (fun _ => (abs_le.mp (ihs true _)).1) (fun _ => (abs_le.mp (ihs false _)).1)
                (fun _ => (abs_le.mp (ihf _)).1)
              rwa [mixF_const (by linarith)] at this
            · have := mixF_le (c1 := M) (c0 := M) (cf := M)
                (v1 := P.val K L g (ks true) (P.setDisc σ a j i true))
                (v0 := P.val K L g (ks false) (P.setDisc σ a j i false))
                (vf := P.val K L g kf (P.setExcl σ a j E i)) hk0 hk1 hd
                (fun _ => le_of_abs_le (ihs true _)) (fun _ => le_of_abs_le (ihs false _))
                (fun _ => le_of_abs_le (ihf _))
              rwa [mixF_const (by linarith)] at this

theorem val_add {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ)
    {g₁ g₂ : P.State → Option β → ℝ} {M₁ M₂ : ℝ} (h1 : ∀ σ o, |g₁ σ o| ≤ M₁)
    (h2 : ∀ σ o, |g₂ σ o| ≤ M₂) :
    ∀ (t : TT P β) σ, P.val K L (fun σ o => g₁ σ o + g₂ σ o) t σ =
      P.val K L g₁ t σ + P.val K L g₂ t σ := by
  intro t
  induction t with
  | ret b => intro σ; simp only [val]; split_ifs <;> rfl
  | sample p k ih =>
      intro σ; simp only [val]; split_ifs
      · rfl
      · simp_rw [ih, mul_add]
        exact Summable.tsum_add (summable_pmf_mul p fun x => P.val_abs_le hK L h1 (k x) σ)
          (summable_pmf_mul p fun x => P.val_abs_le hK L h2 (k x) σ)
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [val]; split_ifs
      · rfl
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · split_ifs
          · exact ihf _
          · rw [ihs, ihs, ihf, mixF_add]

theorem val_smul {K : P.State → Bool → ℝ} (L : ℕ) (c : ℝ) (g : P.State → Option β → ℝ) :
    ∀ (t : TT P β) σ, P.val K L (fun σ o => c * g σ o) t σ = c * P.val K L g t σ := by
  intro t
  induction t with
  | ret b => intro σ; simp only [val]; split_ifs <;> rfl
  | sample p k ih =>
      intro σ; simp only [val]; split_ifs
      · rfl
      · simp_rw [ih, mul_left_comm _ c]
        exact tsum_mul_left
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [val]; split_ifs
      · rfl
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · split_ifs
          · exact ihf _
          · rw [ihs, ihs, ihf, mixF_smul]

theorem val_const {K : P.State → Bool → ℝ} (L : ℕ) {g : P.State → Option β → ℝ} {c : ℝ}
    (hg : ∀ σ o, g σ o = c) : ∀ (t : TT P β) σ, P.val K L g t σ = c := by
  intro t
  induction t with
  | ret b => intro σ; simp only [val]; split_ifs <;> exact hg _ _
  | sample p k ih =>
      intro σ; simp only [val]; split_ifs
      · exact hg _ _
      · simp_rw [ih]; exact tsum_pmf_const p c
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [val]; split_ifs
      · exact hg _ _
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · rename_i E _
          split_ifs with hi
          · exact ihf _
          · rw [ihs, ihs, ihf, mixF_const (by linarith [P.one_le_dd hi])]

theorem val_mono {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ)
    {g₁ g₂ : P.State → Option β → ℝ} {M₁ M₂ : ℝ} (h1 : ∀ σ o, |g₁ σ o| ≤ M₁)
    (h2 : ∀ σ o, |g₂ σ o| ≤ M₂) (hnone : ∀ σ, L ≤ P.D σ → g₁ σ none ≤ g₂ σ none)
    (hsome : ∀ σ b, g₁ σ (some b) ≤ g₂ σ (some b)) :
    ∀ (t : TT P β) σ, P.val K L g₁ t σ ≤ P.val K L g₂ t σ := by
  intro t
  induction t with
  | ret b =>
      intro σ; simp only [val]; split_ifs with h
      · exact hnone σ h
      · exact hsome σ b
  | sample p k ih =>
      intro σ; simp only [val]; split_ifs with h
      · exact hnone σ h
      · exact Summable.tsum_le_tsum
          (fun x => mul_le_mul_of_nonneg_left (ih x σ) ENNReal.toReal_nonneg)
          (summable_pmf_mul p fun x => P.val_abs_le hK L h1 (k x) σ)
          (summable_pmf_mul p fun x => P.val_abs_le hK L h2 (k x) σ)
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [val]; split_ifs with h
      · exact hnone σ h
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · rename_i E _
          split_ifs with hi
          · exact ihf _
          · exact mixF_le (hK σ a).1 (hK σ a).2 (P.one_le_dd hi) (fun _ => ihs _ _)
              (fun _ => ihs _ _) (fun _ => ihf _)

theorem val_sum {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ) {ι : Type} (s : Finset ι)
    (g : ι → P.State → Option β → ℝ) {M : ℝ} (hg : ∀ i σ o, |g i σ o| ≤ M) (t : TT P β)
    (σ : P.State) :
    P.val K L (fun σ o => ∑ i ∈ s, g i σ o) t σ = ∑ i ∈ s, P.val K L (g i) t σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact P.val_const L (fun _ _ => rfl) t σ
  | insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      rw [P.val_add hK L (M₁ := M) (M₂ := s.card * M) (hg x) (fun σ o => ?_), ih]
      calc |∑ i ∈ s, g i σ o| ≤ ∑ i ∈ s, |g i σ o| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ s, M := Finset.sum_le_sum fun i _ => hg i σ o
        _ = s.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The hard-prior kernel and the lazy-sampling identity -/

/-- The label kernel of the hard prior with root `b`: a fresh label of table `a` is one with
probability `(m_{a,b} - s_a)/(W - t_a)` (capped at `1` for unreachable states). -/
noncomputable def kap (b : Bool) (σ : P.State) (a : Bool) : ℝ :=
  min 1 (((P.mab b a - P.sA σ a : ℕ) : ℝ) / ((P.W - P.tA σ a : ℕ) : ℝ))

theorem kap_ok (b : Bool) : P.KerOK (P.kap b) := fun _ _ =>
  ⟨le_min zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), min_le_left _ _⟩

theorem cast_sub_card {E : Finset (Fin P.ℓ)} {i : Fin P.ℓ} (hi : i ∉ E) :
    ((P.ℓ - E.card : ℕ) : ℝ) = P.dd E := by
  rw [Nat.cast_sub (P.card_lt_of_notMem hi).le]; rfl

/-- The posterior probabilities of the three outcomes of a fresh test, in counting form. -/
theorem fresh_counts (b : Bool) {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) :
    (((P.Sb b σ).filter fun T => T.1 a j = i ∧ T.2 a j = true).card : ℝ) =
        ((P.Sb b σ).filter fun T => T.1 a j = i).card * P.kap b σ a ∧
      (((P.Sb b σ).filter fun T => T.1 a j = i ∧ T.2 a j = false).card : ℝ) =
        ((P.Sb b σ).filter fun T => T.1 a j = i).card * (1 - P.kap b σ a) ∧
      (((P.Sb b σ).filter fun T => T.1 a j ≠ i).card : ℝ) =
        (P.dd E - 1) * ((P.Sb b σ).filter fun T => T.1 a j = i).card ∧
      ((P.Sb b σ).card : ℝ) = P.dd E * ((P.Sb b σ).filter fun T => T.1 a j = i).card := by
  classical
  set S := P.Sb b σ
  set F := S.filter fun T => T.1 a j = i
  have hS : (S.card : ℝ) = P.dd E * F.card := by
    rw [P.card_fiber hσ hi, Nat.cast_mul, P.cast_sub_card hi]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun T => T.1 a j = i)
  have h1eq : S.filter (fun T => T.1 a j = i ∧ T.2 a j = true) =
      F.filter fun T => T.2 a j = true := by rw [Finset.filter_filter]
  have h0eq : S.filter (fun T => T.1 a j = i ∧ T.2 a j = false) =
      F.filter fun T => ¬ T.2 a j = true := by
    rw [Finset.filter_filter]; exact Finset.filter_congr fun T _ => by simp
  have hsplitF := Finset.card_filter_add_card_filter_not (s := F) (fun T => T.2 a j = true)
  have hlab : (F.filter fun T => T.2 a j = true).card * (P.U σ a).card + F.card * P.sA σ a =
      F.card * P.mab b a := P.card_label (b := b) hσ i
  have hU := P.card_U σ a
  -- the main ratio
  have hkey : ((F.filter fun T => T.2 a j = true).card : ℝ) = F.card * P.kap b σ a := by
    rcases Nat.eq_zero_or_pos F.card with hF | hF
    · have : (F.filter fun T => T.2 a j = true).card = 0 :=
        Nat.eq_zero_of_le_zero (hF ▸ Finset.card_filter_le _ _)
      rw [this, hF]; simp
    · have hsm : P.sA σ a ≤ P.mab b a := by
        by_contra hc
        have : F.card * P.mab b a < F.card * P.sA σ a := Nat.mul_lt_mul_of_pos_left
          (by omega) hF
        omega
      have hUpos : 0 < (P.U σ a).card := by
        apply Finset.card_pos.mpr
        exact ⟨j, by unfold U; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by
          rw [hσ]; rfl⟩⟩
      have hle : (F.filter fun T => T.2 a j = true).card ≤ F.card := Finset.card_filter_le _ _
      have hlab' : (F.filter fun T => T.2 a j = true).card * (P.U σ a).card =
          F.card * (P.mab b a - P.sA σ a) := by
        rw [Nat.mul_sub]; omega
      have hms : P.mab b a - P.sA σ a ≤ (P.U σ a).card := by
        by_contra hc
        have : F.card * (P.U σ a).card < F.card * (P.mab b a - P.sA σ a) :=
          Nat.mul_lt_mul_of_pos_left (by omega) hF
        have : (F.filter fun T => T.2 a j = true).card * (P.U σ a).card ≤
            F.card * (P.U σ a).card := Nat.mul_le_mul_right _ hle
        omega
      have hW : P.W - P.tA σ a = (P.U σ a).card := by omega
      unfold kap
      rw [hW]
      have hUr : (0 : ℝ) < (P.U σ a).card := by exact_mod_cast hUpos
      rw [min_eq_right (by rw [div_le_one hUr]; exact_mod_cast hms)]
      field_simp
      exact_mod_cast hlab'
  refine ⟨by rw [h1eq]; exact hkey, ?_, ?_, hS⟩
  · rw [h0eq]
    have : ((F.filter fun T => ¬ T.2 a j = true).card : ℝ) =
        F.card - (F.filter fun T => T.2 a j = true).card := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hsplitF; push_cast at this; linarith
    rw [this, hkey]; ring
  · have := congrArg (fun n : ℕ => (n : ℝ)) hsplit
    push_cast at this
    have hFS : (F.card : ℝ) = (S.filter fun T => T.1 a j = i).card := rfl
    rw [show (S.filter fun T => T.1 a j ≠ i) = S.filter fun T => ¬ T.1 a j = i from rfl]
    linarith

/-- The payoff of an event `E` of outputs (a stopped run pays `0`). -/
noncomputable def gE (E : Set β) : P.State → Option β → ℝ := fun _ o =>
  match o with
  | none => 0
  | some b => (probE (PMF.pure b) E).toReal

/-- The average, over the consistent valid tables with root `b`, of the true probability that
the test tree outputs an element of `E`. -/
noncomputable def avgE (b : Bool) (σ : P.State) (t : TT P β) (E : Set β) : ℝ :=
  (∑ T ∈ P.Sb b σ, (probE (t.run T) E).toReal) / (P.Sb b σ).card

theorem probE_toReal_le_one {γ : Type} (p : PMF γ) (E : Set γ) : (probE p E).toReal ≤ 1 := by
  have := probE_le_one p E
  calc (probE p E).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top this
    _ = 1 := ENNReal.toReal_one

theorem gE_abs_le (E : Set β) (σ : P.State) (o : Option β) : |P.gE E σ o| ≤ 1 := by
  cases o with
  | none => simp [gE]
  | some b =>
      simp only [gE]
      rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact probE_toReal_le_one _ _

theorem probE_bind_toReal {γ δ : Type} (p : PMF γ) (f : γ → PMF δ) (E : Set δ) :
    (probE (p.bind f) E).toReal = ∑' x, (p x).toReal * (probE (f x) E).toReal := by
  unfold probE
  rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.toReal_mul]
  · intro x
    exact ENNReal.mul_ne_top (p.apply_ne_top x)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _))

theorem D_lt_top (σ : P.State) : ¬ 2 * P.W + 1 ≤ P.D σ := by have := P.D_le σ; omega

theorem sum_eq_card_mul_avg (b : Bool) (σ : P.State) (t : TT P β) (E : Set β) :
    ∑ T ∈ P.Sb b σ, (probE (t.run T) E).toReal = (P.Sb b σ).card * P.avgE b σ t E := by
  unfold avgE
  rcases Nat.eq_zero_or_pos (P.Sb b σ).card with h | h
  · rw [Finset.card_eq_zero.mp h]; simp
  · rw [mul_div_cancel₀ _ (by exact_mod_cast h.ne')]

/-- `pw-lem:posterior`, lazy-sampling form: under the uniform prior on the valid
tables with root `b` that are consistent with a reachable state, the average true probability
that a test tree outputs an element of `E` equals the expected payoff of the lazily sampled,
unstopped process with the kernel `kap b`. -/
theorem avg_eq_val (b : Bool) (E : Set β) :
    ∀ (t : TT P β) (σ : P.State), (P.Sb b σ).Nonempty →
      P.avgE b σ t E = P.val (P.kap b) (2 * P.W + 1) (P.gE E) t σ := by
  intro t
  induction t with
  | ret c =>
      intro σ hne
      simp only [val, ite_eq_right (P.D_lt_top σ), avgE, TT.run, gE]
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _
        (by exact_mod_cast (Finset.card_pos.mpr hne).ne')]
  | sample p k ih =>
      intro σ hne
      simp only [val, ite_eq_right (P.D_lt_top σ), avgE, TT.run]
      simp_rw [probE_bind_toReal]
      have hsum : ∀ T ∈ P.Sb b σ,
          Summable fun x => (p x).toReal * (probE ((k x).run T) E).toReal := fun T _ =>
        summable_pmf_mul p (M := 1) fun x => by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact probE_toReal_le_one _ _
      rw [← Summable.tsum_finsetSum hsum, div_eq_mul_inv, ← tsum_mul_right]
      refine tsum_congr fun x => ?_
      rw [← ih x σ hne, avgE, ← Finset.mul_sum]
      ring
  | test a j i kf ks ihf ihs =>
      intro σ hne
      simp only [val, ite_eq_right (P.D_lt_top σ)]
      have hcons : ∀ T ∈ P.Sb b σ, (σ a j).Cons (T.1 a j) (T.2 a j) := fun T hT =>
        (Finset.mem_filter.mp hT).2.2 a j
      split
      · rename_i i₀ y₀ hσ
        have hrun : ∀ T ∈ P.Sb b σ, (TT.test a j i kf ks).run T =
            (if i = i₀ then ks y₀ else kf).run T := by
          intro T hT
          have hc := hcons T hT
          rw [hσ] at hc
          obtain ⟨h1, h2⟩ := hc
          simp only [TT.run, h1, h2]
          by_cases h : i = i₀
          · rw [ite_eq_left h.symm, ite_eq_left h]
          · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
        have : P.avgE b σ (TT.test a j i kf ks) E =
            P.avgE b σ (if i = i₀ then ks y₀ else kf) E := by
          unfold avgE; rw [Finset.sum_congr rfl fun T hT => by rw [hrun T hT]]
        rw [this]
        split_ifs
        · exact ihs y₀ σ hne
        · exact ihf σ hne
      · rename_i E' hσ
        split_ifs with hiE
        · have : P.avgE b σ (TT.test a j i kf ks) E = P.avgE b σ kf E := by
            unfold avgE
            refine congrArg (· / _) (Finset.sum_congr rfl fun T hT => ?_)
            have hc := hcons T hT
            rw [hσ] at hc
            have : T.1 a j ≠ i := fun h => hc (h ▸ hiE)
            simp only [TT.run, ite_eq_right this]
          rw [this]; exact ihf σ hne
        · obtain ⟨c1, c0, cf, cS⟩ := P.fresh_counts b hσ hiE
          set S := P.Sb b σ
          set F := S.filter fun T => T.1 a j = i
          have hFpos : (0 : ℝ) < F.card := by
            have h1 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
            rw [cS] at h1
            have := P.one_le_dd hiE
            exact pos_of_mul_pos_right h1 (by linarith)
          -- split the sum into the three outcomes
          have hsplit : ∑ T ∈ S, (probE ((TT.test a j i kf ks).run T) E).toReal =
              ∑ T ∈ P.Sb b (P.setDisc σ a j i true), (probE ((ks true).run T) E).toReal +
              ∑ T ∈ P.Sb b (P.setDisc σ a j i false), (probE ((ks false).run T) E).toReal +
              ∑ T ∈ P.Sb b (P.setExcl σ a j E' i), (probE (kf.run T) E).toReal := by
            rw [P.Sb_setDisc hσ hiE, P.Sb_setDisc hσ hiE, P.Sb_setExcl hσ]
            rw [← Finset.sum_filter_add_sum_filter_not S (fun T => T.1 a j = i)]
            congr 1
            · rw [← Finset.sum_filter_add_sum_filter_not (S.filter fun T => T.1 a j = i)
                (fun T => T.2 a j = true), Finset.filter_filter, Finset.filter_filter]
              congr 1
              · refine Finset.sum_congr rfl fun T hT => ?_
                obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hT
                simp only [TT.run, h1, h2, ite_true]
              · rw [show (S.filter fun T => T.1 a j = i ∧ ¬ T.2 a j = true) =
                    S.filter fun T => T.1 a j = i ∧ T.2 a j = false from
                    Finset.filter_congr fun T _ => by simp]
                refine Finset.sum_congr rfl fun T hT => ?_
                obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hT
                simp only [TT.run, h1, h2, ite_true]
            · refine Finset.sum_congr rfl fun T hT => ?_
              obtain ⟨-, h1⟩ := Finset.mem_filter.mp hT
              simp only [TT.run, ite_eq_right h1]
          have hchild : ∀ (σ' : P.State) (t' : TT P β),
              ((P.Sb b σ').Nonempty → P.avgE b σ' t' E = P.val (P.kap b) (2 * P.W + 1)
                (P.gE E) t' σ') →
              ∑ T ∈ P.Sb b σ', (probE (t'.run T) E).toReal =
                (P.Sb b σ').card * P.val (P.kap b) (2 * P.W + 1) (P.gE E) t' σ' := by
            intro σ' t' hih
            rw [P.sum_eq_card_mul_avg]
            rcases (P.Sb b σ').eq_empty_or_nonempty with h | h
            · rw [h]; simp
            · rw [hih h]
          unfold avgE
          rw [hsplit, hchild _ _ (ihs true _), hchild _ _ (ihs false _), hchild _ _ (ihf _)]
          rw [P.Sb_setDisc hσ hiE, P.Sb_setDisc hσ hiE, P.Sb_setExcl hσ, c1, c0, cf, cS]
          unfold mixF
          have hd := P.one_le_dd hiE
          field_simp

end Prm

end LearningGuided.PointwiseLB
