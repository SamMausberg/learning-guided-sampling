import LearningGuided.PointwiseLB.Hellinger

/-!
# The information bound (Lemma `pw-lem:information`)

For every test tree with failure budget `q` (in particular every converted algorithm with cap
`q`), put `η = q/((ℓ-1)W)`. Under the hard prior with root `b` (uniform on the valid tables with
root `b`), the probabilities of every output event differ by at most `8√η + 32η`
(`pw-eq:transcript`). The proof stops the process at `W/8` discoveries, bounds the stopping
probability by `16η` with Markov's inequality and Lemma `pw-lem:search`, and bounds the
distance of the stopped laws with the Hellinger affinity (`Hellinger.lean`): the per-step
deficit is at most `16/W` and the expected number of revealed labels is at most `2q/(ℓ-1)`
under the geometric-mean process.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm) {β : Type}

/-! ### Stopping -/

/-- The stopped process differs from the unstopped one only after stopping (lower bound). -/
theorem val_stop_lower {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ) (E : Set β) :
    ∀ (t : TT P β) σ, P.val K L (P.gE E) t σ ≤ P.val K (2 * P.W + 1) (P.gE E) t σ := by
  have hb := P.gE_abs_le E
  have hnn : ∀ (t : TT P β) σ, 0 ≤ P.val K (2 * P.W + 1) (P.gE E) t σ := fun t σ => by
    have := P.val_mono hK (2 * P.W + 1) (g₁ := fun _ _ => (0 : ℝ)) (M₁ := 0) (M₂ := 1)
      (fun _ _ => by simp) hb (fun σ _ => by simp [gE]) (fun σ b => by
        simp only [gE]; exact ENNReal.toReal_nonneg) t σ
    rwa [P.val_const _ (fun _ _ => rfl)] at this
  intro t
  induction t with
  | ret c =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h]; exact hnn _ σ
      · rw [val_ret h, val_ret (P.D_lt_top σ)]
  | sample p k ih =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h]; exact hnn _ σ
      · rw [val_sample h, val_sample (P.D_lt_top σ)]
        exact Summable.tsum_le_tsum
          (fun x => mul_le_mul_of_nonneg_left (ih x σ) ENNReal.toReal_nonneg)
          (summable_pmf_mul p fun x => P.val_abs_le hK L hb (k x) σ)
          (summable_pmf_mul p fun x => P.val_abs_le hK _ hb (k x) σ)
  | test a j i kf ks ihf ihs =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h]; exact hnn _ σ
      · cases hσ : σ a j with
        | disc i₀ y₀ =>
            rw [val_test_disc h hσ, val_test_disc (P.D_lt_top σ) hσ]
            split_ifs
            · exact ihs _ _
            · exact ihf _
        | undisc E' =>
            by_cases hi : i ∈ E'
            · rw [val_test_mem h hσ hi, val_test_mem (P.D_lt_top σ) hσ hi]; exact ihf _
            · rw [val_test_fresh h hσ hi, val_test_fresh (P.D_lt_top σ) hσ hi]
              exact mixF_le (hK σ a).1 (hK σ a).2 (P.one_le_dd hi) (fun _ => ihs _ _)
                (fun _ => ihs _ _) (fun _ => ihf _)

/-- The stopped process differs from the unstopped one only after stopping (upper bound). -/
theorem val_stop_upper {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ) (E : Set β) :
    ∀ (t : TT P β) σ, P.val K (2 * P.W + 1) (P.gE E) t σ ≤
      P.val K L (fun σ o => P.gE E σ o + P.gpt none σ o) t σ := by
  have hb := P.gE_abs_le E
  have hb2 : ∀ σ o, |P.gE E σ o + P.gpt none σ o| ≤ 2 := fun σ o => by
    have := abs_add_le (P.gE E σ o) (P.gpt none σ o)
    have := P.abs_gpt_le none σ o
    linarith [hb σ o]
  intro t
  induction t with
  | ret c =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h, val_ret (P.D_lt_top σ)]
        simp only [gE, gpt, ite_true, zero_add]
        exact probE_toReal_le_one _ _
      · rw [val_ret h, val_ret (P.D_lt_top σ)]
        simp [gpt]
  | sample p k ih =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h]
        simp only [gE, gpt, ite_true, zero_add]
        exact le_of_abs_le (P.val_abs_le hK _ hb _ σ)
      · rw [val_sample h, val_sample (P.D_lt_top σ)]
        exact Summable.tsum_le_tsum
          (fun x => mul_le_mul_of_nonneg_left (ih x σ) ENNReal.toReal_nonneg)
          (summable_pmf_mul p fun x => P.val_abs_le hK _ hb (k x) σ)
          (summable_pmf_mul p fun x => P.val_abs_le hK L hb2 (k x) σ)
  | test a j i kf ks ihf ihs =>
      intro σ
      by_cases h : L ≤ P.D σ
      · rw [val_stop h]
        simp only [gE, gpt, ite_true, zero_add]
        exact le_of_abs_le (P.val_abs_le hK _ hb _ σ)
      · cases hσ : σ a j with
        | disc i₀ y₀ =>
            rw [val_test_disc h hσ, val_test_disc (P.D_lt_top σ) hσ]
            split_ifs
            · exact ihs _ _
            · exact ihf _
        | undisc E' =>
            by_cases hi : i ∈ E'
            · rw [val_test_mem h hσ hi, val_test_mem (P.D_lt_top σ) hσ hi]; exact ihf _
            · rw [val_test_fresh h hσ hi, val_test_fresh (P.D_lt_top σ) hσ hi]
              exact mixF_le (hK σ a).1 (hK σ a).2 (P.one_le_dd hi) (fun _ => ihs _ _)
                (fun _ => ihs _ _) (fun _ => ihf _)

/-- Markov's inequality for the stopping event: `L · P(stopped) ≤ E D`. -/
theorem stop_markov {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ) (t : TT P β)
    (σ : P.State) : (L : ℝ) * P.val K L (P.gpt none) t σ ≤ P.val K L P.gD t σ := by
  rw [← P.val_smul L]
  refine P.val_mono hK L (M₁ := L) (M₂ := 2 * P.W) (fun σ o => ?_) (fun σ o => P.abs_gD_le σ o)
    (fun σ h => ?_) (fun σ b => ?_) t σ
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
    have := P.abs_gpt_le none σ o
    nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  · simp only [gpt, ite_true, mul_one, gD]; exact_mod_cast h
  · simp only [gpt, reduceCtorEq, ite_false, mul_zero, gD]; exact Nat.cast_nonneg _

/-! ### Reachability -/

theorem reach_children (b : Bool) {σ : P.State} (hne : (P.Sb b σ).Nonempty) {a : Bool}
    {j : Str P.k} {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) :
    (1 < P.dd E → (P.Sb b (P.setExcl σ a j E i)).Nonempty) ∧
      (0 < P.kap b σ a → (P.Sb b (P.setDisc σ a j i true)).Nonempty) ∧
      (P.kap b σ a < 1 → (P.Sb b (P.setDisc σ a j i false)).Nonempty) := by
  obtain ⟨c1, c0, cf, cS⟩ := P.fresh_counts b hσ hi
  have hFpos : (0 : ℝ) < ((P.Sb b σ).filter fun T => T.1 a j = i).card := by
    have h1 : (0 : ℝ) < (P.Sb b σ).card := by exact_mod_cast Finset.card_pos.mpr hne
    rw [cS] at h1
    have := P.one_le_dd hi
    exact pos_of_mul_pos_right h1 (by linarith)
  have key : ∀ s : Finset P.Tables, (0 : ℝ) < s.card → s.Nonempty := fun s h =>
    Finset.card_pos.mp (by exact_mod_cast h)
  refine ⟨fun hd => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [P.Sb_setExcl hσ]; apply key; rw [cf]; nlinarith
  · rw [P.Sb_setDisc hσ hi]; apply key; rw [c1]; positivity
  · rw [P.Sb_setDisc hσ hi]; apply key; rw [c0]; nlinarith

theorem Sb_sub_Cset (b : Bool) (σ : P.State) : P.Sb b σ ⊆ P.Cset σ := by
  unfold Cset; cases b
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- `E D ≤ 2q/(ℓ-1)` under the hard prior with root `b` (`pw-eq:discoveries`), for every
stopping level. -/
theorem discoveries_root (b : Bool) (L : ℕ) (t : TT P β) (q : ℕ) (h0 : (P.Sb b P.σ0).Nonempty)
    (hW : ∀ T ∈ P.Cset P.σ0, t.Within T q) :
    P.val (P.kap b) L P.gD t P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) :=
  P.discoveries_le (P.kap_ok b) L (fun σ => (P.Sb b σ).Nonempty)
    (fun σ h => h.mono (P.Sb_sub_Cset b σ))
    (fun _ _ _ _ _ hR _ hσ hi hd => (P.reach_children b hR hσ hi).1 hd)
    (fun _ _ _ _ _ hR _ hσ hi => (P.reach_children b hR hσ hi).2) t q h0 hW

/-- `E_Ĝ D ≤ 2q/(ℓ-1)` for the geometric-mean process stopped at `L ≤ W/8`. -/
theorem discoveries_geo {L : ℕ} (hL : L ≤ P.W / 8) (t : TT P β) (q : ℕ)
    (h0 : (P.Sb false P.σ0).Nonempty ∧ (P.Sb true P.σ0).Nonempty)
    (hW : ∀ T ∈ P.Cset P.σ0, t.Within T q) :
    P.val P.kG L P.gD t P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) := by
  refine P.discoveries_le P.kG_ok L
    (fun σ => (P.Sb false σ).Nonempty ∧ (P.Sb true σ).Nonempty)
    (fun σ h => h.1.mono (P.Sb_sub_Cset false σ))
    (fun _ _ _ _ _ hR _ hσ hi hd =>
      ⟨(P.reach_children false hR.1 hσ hi).1 hd, (P.reach_children true hR.2 hσ hi).1 hd⟩)
    (fun σ a _ _ _ hR hstop hσ hi => ?_) t q h0 hW
  obtain ⟨-, h0a, h0b⟩ := P.kap_eq_ratio hL hstop false a
  obtain ⟨-, h1a, h1b⟩ := P.kap_eq_ratio hL hstop true a
  have rf := P.reach_children false hR.1 hσ hi
  have rt := P.reach_children true hR.2 hσ hi
  exact ⟨fun _ => ⟨rf.2.1 (by linarith), rt.2.1 (by linarith)⟩,
    fun _ => ⟨rf.2.2 (by linarith), rt.2.2 (by linarith)⟩⟩

/-! ### Valid tables exist -/

theorem exists_table_ones {m : ℕ} (hm : m ≤ P.W) : ∃ y : Str P.k → Bool, ones y = m := by
  classical
  let e := Fintype.equivFin (Str P.k)
  refine ⟨fun j => decide ((e j : ℕ) < m), ?_⟩
  unfold ones
  have h1 : (Finset.univ.filter fun j : Str P.k => decide ((e j : ℕ) < m) = true).card =
      (Finset.univ.filter fun i : Fin (Fintype.card (Str P.k)) => (i : ℕ) < m).card :=
    Finset.card_equiv e (fun j => by simp)
  rw [h1, Fin.card_filter_val_lt, P.card_rows, min_eq_right hm]

theorem exists_valid (b : Bool) : ∃ T : P.Tables, P.Valid b T := by
  obtain ⟨yp, hp⟩ := P.exists_table_ones P.mPlus_le_W
  obtain ⟨ym, hm⟩ := P.exists_table_ones (P.mMinus_lt_mPlus.le.trans P.mPlus_le_W)
  refine ⟨(fun _ _ => ⟨0, by have := P.hℓ; omega⟩, fun a => if a = b then yp else ym), ?_, ?_⟩
  · simp [hp]
  · simp [hm]

theorem Sb_σ0_nonempty (b : Bool) : (P.Sb b P.σ0).Nonempty := by
  obtain ⟨T, hT⟩ := P.exists_valid b
  exact ⟨T, by rw [Sb_σ0]; simp [hT]⟩

/-! ### The information bound -/

/-- The parameter `η = q/((ℓ-1)W)`. -/
noncomputable def eta (q : ℕ) : ℝ := (q : ℝ) / (((P.ℓ : ℝ) - 1) * P.W)

theorem eta_nonneg (q : ℕ) : 0 ≤ P.eta q := by
  unfold eta
  have : (1 : ℝ) ≤ P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 ≤ P.ℓ)
  have : (0 : ℝ) ≤ P.W := Nat.cast_nonneg _
  apply div_nonneg (Nat.cast_nonneg q); nlinarith

theorem one_sided [Finite β] (t : TT P β) (q : ℕ) (hW : ∀ T ∈ P.Cset P.σ0, t.Within T q)
    (E : Set β) (b : Bool) :
    P.avgE b P.σ0 t E - P.avgE (!b) P.σ0 t E ≤ 8 * Real.sqrt (P.eta q) + 16 * P.eta q := by
  classical
  have := Fintype.ofFinite β
  set L := P.W / 8
  have hL : L ≤ P.W / 8 := le_rfl
  have hLpos : (8 : ℝ) ≤ L := by
    have h1 := P.r_le_W8; have h2 := P.eight_le_r; have h3 := P.W8_mul
    have : 8 ≤ P.W / 8 := by omega
    exact_mod_cast this
  have hℓ : (1 : ℝ) < P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 < P.ℓ)
  have hWp : (0 : ℝ) < P.W := by have := P.cast_W; have := P.cast_r_ge; nlinarith
  have hLW : (L : ℝ) = P.W / 8 := by
    have h3 := P.W8_mul
    have : (L : ℝ) * 8 = P.W := by exact_mod_cast h3
    linarith
  -- the unstopped averages
  rw [P.avg_eq_val b E t P.σ0 (P.Sb_σ0_nonempty b),
    P.avg_eq_val (!b) E t P.σ0 (P.Sb_σ0_nonempty (!b))]
  have hup := P.val_stop_upper (P.kap_ok b) L E t P.σ0
  have hlo := P.val_stop_lower (P.kap_ok (!b)) L E t P.σ0
  rw [P.val_add (P.kap_ok b) L (M₁ := 1) (M₂ := 1) (P.gE_abs_le E) (P.abs_gpt_le none)] at hup
  -- stopping probability
  have hstop : P.val (P.kap b) L (P.gpt none) t P.σ0 ≤ 16 * P.eta q := by
    have h1 := P.stop_markov (P.kap_ok b) L t P.σ0
    have h2 := P.discoveries_root b L t q (P.Sb_σ0_nonempty b) hW
    have h3 : P.val (P.kap b) L (P.gpt none) t P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) / L := by
      rw [le_div_iff₀ (by linarith)]; linarith
    calc P.val (P.kap b) L (P.gpt none) t P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) / L := h3
      _ = 16 * P.eta q := by
          rw [hLW]; unfold eta; field_simp; ring
  -- events as sums of point laws
  set FE : Finset (Option β) := Finset.univ.filter fun o => ∃ x ∈ E, o = some x
  have hgE : ∀ σ o, P.gE E σ o = ∑ o' ∈ FE, P.gpt o' σ o := by
    intro σ o
    rw [Finset.sum_congr rfl fun o' _ => show P.gpt o' σ o = if o = o' then 1 else 0 from rfl,
      Finset.sum_ite_eq]
    cases o with
    | none => simp [gE, FE]
    | some x =>
        simp only [gE, FE, Finset.mem_filter, Finset.mem_univ, true_and, Option.some.injEq,
          exists_eq_right', probE, PMF.toOuterMeasure_pure_apply]
        split_ifs <;> simp
  have hsumE : ∀ b', P.val (P.kap b') L (P.gE E) t P.σ0 = ∑ o ∈ FE, P.Lpt b' L t P.σ0 o := by
    intro b'
    change _ = ∑ o ∈ FE, P.val (P.kap b') L (P.gpt o) t P.σ0
    rw [← P.val_sum (P.kap_ok b') L FE (fun o => P.gpt o) (fun o => P.abs_gpt_le o)]
    exact congrArg (fun g => P.val (P.kap b') L g t P.σ0) (funext fun σ => funext fun o => hgE σ o)
  -- the affinity bound
  have hBC : 1 - ∑ o, Real.sqrt (P.Lpt false L t P.σ0 o * P.Lpt true L t P.σ0 o) ≤
      32 * P.eta q := by
    have h1 := P.bc_le_affinity L t P.σ0
    have h2 := P.one_sub_bcRec_le hL t P.σ0
    have h3 := P.discoveries_geo hL t q ⟨P.Sb_σ0_nonempty false, P.Sb_σ0_nonempty true⟩ hW
    rw [P.D_σ0, Nat.cast_zero, sub_zero] at h2
    have : 16 / (P.W : ℝ) * P.val P.kG L P.gD t P.σ0 ≤ 16 / (P.W : ℝ) *
        (2 * q / ((P.ℓ : ℝ) - 1)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : 16 / (P.W : ℝ) * (2 * q / ((P.ℓ : ℝ) - 1)) = 32 * P.eta q := by
      unfold eta; field_simp; ring
    linarith
  have hdiff : ∑ o ∈ FE, P.Lpt b L t P.σ0 o - ∑ o ∈ FE, P.Lpt (!b) L t P.σ0 o ≤
      8 * Real.sqrt (P.eta q) := by
    have hev := event_diff_le_affinity (P.Lpt_nonneg b L t P.σ0) (P.Lpt_nonneg (!b) L t P.σ0)
      (P.sum_Lpt b L t P.σ0) (P.sum_Lpt (!b) L t P.σ0) FE
    have hsymm : ∑ o, Real.sqrt (P.Lpt b L t P.σ0 o * P.Lpt (!b) L t P.σ0 o) =
        ∑ o, Real.sqrt (P.Lpt false L t P.σ0 o * P.Lpt true L t P.σ0 o) := by
      cases b
      · rfl
      · exact Finset.sum_congr rfl fun o _ => by rw [mul_comm]; rfl
    rw [hsymm] at hev
    refine hev.trans ?_
    calc Real.sqrt (2 * (1 - ∑ o, Real.sqrt (P.Lpt false L t P.σ0 o * P.Lpt true L t P.σ0 o)))
        ≤ Real.sqrt (2 * (32 * P.eta q)) := Real.sqrt_le_sqrt (by linarith)
      _ = 8 * Real.sqrt (P.eta q) := by
          rw [show 2 * (32 * P.eta q) = 8 ^ 2 * P.eta q by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hsumE b] at hup
  rw [hsumE (!b)] at hlo
  linarith

/-- `pw-lem:information`, `pw-eq:transcript`, for test trees: for every test tree whose
executions against all valid tables have at most `q` failures, and every output event `E`, the
hard-prior probabilities of `E` under the two roots differ by at most `8√η + 32η`,
`η = q/((ℓ-1)W)`. (The proof gives `8√η + 16η`.) -/
theorem information_tt [Finite β] (t : TT P β) (q : ℕ)
    (hW : ∀ T ∈ P.Cset P.σ0, t.Within T q) (E : Set β) :
    |P.avgE false P.σ0 t E - P.avgE true P.σ0 t E| ≤
      8 * Real.sqrt (P.eta q) + 32 * P.eta q := by
  have h1 := P.one_sided t q hW E false
  have h2 := P.one_sided t q hW E true
  simp only [Bool.not_false, Bool.not_true] at h1 h2
  have := P.eta_nonneg q
  rw [abs_le]; constructor <;> linarith

/-! ### Algorithms against the true oracles -/

/-- The valid tables with root `b`. -/
noncomputable def Theta (b : Bool) : Finset P.Tables := Finset.univ.filter fun T => P.Valid b T

/-- The hard-prior probability that the algorithm's output lies in `E`, given root `b`: the
average over the valid tables with root `b` of the true output law of `A` against `h_θ`. -/
noncomputable def avgA (A : Alg β) (b : Bool) (E : Set β) : ℝ :=
  (∑ T ∈ P.Theta b, (probE (A.run (P.oracle T)) E).toReal) / (P.Theta b).card

theorem avgA_eq (A : Alg β) (b : Bool) (E : Set β) :
    P.avgA A b E = P.avgE b P.σ0 (P.conv A) E := by
  unfold avgA avgE Theta
  rw [P.Sb_σ0 b]
  congr 1
  exact Finset.sum_congr rfl fun T _ => by rw [P.run_conv]

theorem within_conv_all {A : Alg β} {q : ℕ}
    (hA : ∀ B : Bool, ∀ T : P.Tables, P.Valid B T → A.Within (P.oracle T) q) :
    ∀ T ∈ P.Cset P.σ0, (P.conv A).Within T q := by
  intro T hT
  unfold Cset Sb at hT
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  rcases hT with h | h
  · exact P.within_conv T A q (hA false T h.1)
  · exact P.within_conv T A q (hA true T h.1)

/-- `pw-lem:information`, for algorithms: if `A` makes at most `q` queries against every
oracle `h_θ` of the class, the hard-prior output probabilities of every event `E` under the two
roots differ by at most `8√η + 32η`. -/
theorem information [Finite β] (A : Alg β) (q : ℕ)
    (hA : ∀ B : Bool, ∀ T : P.Tables, P.Valid B T → A.Within (P.oracle T) q) (E : Set β) :
    |P.avgA A false E - P.avgA A true E| ≤ 8 * Real.sqrt (P.eta q) + 32 * P.eta q := by
  rw [P.avgA_eq, P.avgA_eq]
  exact P.information_tt (P.conv A) q (P.within_conv_all hA) E

/-- `pw-lem:search`, `pw-eq:discoveries`, for algorithms: if `A` makes at most `q` queries
against every oracle `h_θ`, then under either root `b` the expected number of discovered rows of
its batch simulation, stopped at any level `L` or not, is at most `2q/(ℓ-1)`. -/
theorem discoveries_alg {β : Type} (A : Alg β) (q : ℕ)
    (hA : ∀ B : Bool, ∀ T : P.Tables, P.Valid B T → A.Within (P.oracle T) q) (b : Bool)
    (L : ℕ) : P.val (P.kap b) L P.gD (P.conv A) P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) :=
  P.discoveries_root b L (P.conv A) q (P.Sb_σ0_nonempty b) (P.within_conv_all hA)

/-- The hard-prior output law of `A` given root `b`: the average over the valid tables with
root `b` of the true output law against `h_θ`. -/
noncomputable def avgLaw {n : ℕ} (A : Alg (Str n)) (b : Bool) : Str n → ℝ := fun x =>
  (∑ T ∈ P.Theta b, lawR (A.run (P.oracle T)) x) / (P.Theta b).card

theorem avgA_finset {n : ℕ} (A : Alg (Str n)) (b : Bool) (E : Finset (Str n)) :
    P.avgA A b (E : Set (Str n)) = ∑ x ∈ E, P.avgLaw A b x := by
  unfold avgA avgLaw
  simp_rw [probE_finset_toReal]
  rw [Finset.sum_comm, Finset.sum_div]

theorem sum_avgLaw {n : ℕ} (A : Alg (Str n)) (b : Bool) : ∑ x, P.avgLaw A b x = 1 := by
  have hpos : (0 : ℝ) < (P.Theta b).card := by
    obtain ⟨T, hT⟩ := P.exists_valid b
    exact_mod_cast Finset.card_pos.mpr ⟨T, by simp [Theta, hT]⟩
  unfold avgLaw
  rw [← Finset.sum_div, Finset.sum_comm, div_eq_one_iff_eq hpos.ne']
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  exact Finset.sum_congr rfl fun T _ => by rw [(lawR_isDist _).2]; simp

theorem avgLaw_nonneg {n : ℕ} (A : Alg (Str n)) (b : Bool) (x : Str n) :
    0 ≤ P.avgLaw A b x :=
  div_nonneg (Finset.sum_nonneg fun _ _ => (lawR_isDist _).1 x) (Nat.cast_nonneg _)

/-- `pw-lem:information`, `pw-eq:transcript`, total variation form: for an algorithm with
outputs in `{0,1}^n` and cap `q` against every `h_θ`, the hard-prior output laws under the two
roots satisfy `TV ≤ 8√η + 32η`. -/
theorem information_tv {n : ℕ} (A : Alg (Str n)) (q : ℕ)
    (hA : ∀ B : Bool, ∀ T : P.Tables, P.Valid B T → A.Within (P.oracle T) q) :
    tv (P.avgLaw A false) (P.avgLaw A true) ≤ 8 * Real.sqrt (P.eta q) + 32 * P.eta q := by
  classical
  set E := Finset.univ.filter fun x => P.avgLaw A true x ≤ P.avgLaw A false x
  have hinfo := P.information A q hA (E : Set (Str n))
  rw [P.avgA_finset, P.avgA_finset] at hinfo
  have hsplit : ∀ f : Str n → ℝ, ∑ x, f x = ∑ x ∈ E, f x + ∑ x ∈ Eᶜ, f x := fun f => by
    rw [Finset.sum_add_sum_compl]
  have h0 := P.sum_avgLaw A false
  have h1 := P.sum_avgLaw A true
  have habs : ∑ x, |P.avgLaw A false x - P.avgLaw A true x| =
      2 * (∑ x ∈ E, P.avgLaw A false x - ∑ x ∈ E, P.avgLaw A true x) := by
    rw [hsplit]
    have eE : ∑ x ∈ E, |P.avgLaw A false x - P.avgLaw A true x| =
        ∑ x ∈ E, (P.avgLaw A false x - P.avgLaw A true x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonneg (by
        have := (Finset.mem_filter.mp hx).2; linarith)
    have eC : ∑ x ∈ Eᶜ, |P.avgLaw A false x - P.avgLaw A true x| =
        ∑ x ∈ Eᶜ, (P.avgLaw A true x - P.avgLaw A false x) :=
      Finset.sum_congr rfl fun x hx => by
        rw [abs_sub_comm]
        refine abs_of_nonneg ?_
        have : ¬ P.avgLaw A true x ≤ P.avgLaw A false x := by
          simpa [E] using hx
        linarith
    rw [eE, eC, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have := hsplit (P.avgLaw A false); have := hsplit (P.avgLaw A true)
    linarith
  unfold tv
  rw [habs]
  have := (abs_le.mp hinfo).2
  linarith

end Prm

end LearningGuided.PointwiseLB
