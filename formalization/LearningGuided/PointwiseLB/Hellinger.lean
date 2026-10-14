import LearningGuided.PointwiseLB.Affinity

/-!
# The information bound via the Hellinger affinity

This file replaces the KL chain rule and Pinsker's inequality of Lemma `pw-lem:information` by
the Hellinger affinity, which gives a slightly better constant.

* `kap_bounds`, `kap_diff_sq`: before the stopping level `W/8`, the label probabilities under
  the two roots lie in `[1/4, 3/4]` and differ by at most `4/r`, so the per-step affinity
  deficit is at most `(p - p')² ≤ 16/W`.
* `bcRec`: the recursively defined affinity of the two stopped transcript processes.
* `bc_le_affinity` (concavity under mixtures): the affinity of the two stopped output laws is
  at least `bcRec`.
* `one_sub_bcRec_le` (chain rule): `1 - bcRec ≤ (16/W) E_Ĝ D`, where `Ĝ` is the process whose
  label kernel is the normalized geometric mean of the two kernels; since `Ĝ` has the same
  location-test probabilities, Lemma `pw-lem:search` bounds `E_Ĝ D`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm) {β : Type}

/-- `w_b(y)`: the probability of label `y` under the kernel of root `b`. -/
noncomputable def kw (b : Bool) (σ : P.State) (a : Bool) (y : Bool) : ℝ :=
  if y then P.kap b σ a else 1 - P.kap b σ a

/-- The geometric mean `γ_y = √(w_0(y) w_1(y))`. -/
noncomputable def gam (σ : P.State) (a : Bool) (y : Bool) : ℝ :=
  Real.sqrt (P.kw false σ a y * P.kw true σ a y)

/-- The normalized geometric-mean kernel `Ĝ`. -/
noncomputable def kG (σ : P.State) (a : Bool) : ℝ :=
  P.gam σ a true / (P.gam σ a true + P.gam σ a false)

theorem kw_nonneg (b : Bool) (σ : P.State) (a y : Bool) : 0 ≤ P.kw b σ a y := by
  unfold kw; have := P.kap_ok b σ a; split_ifs <;> linarith

theorem gam_nonneg (σ : P.State) (a y : Bool) : 0 ≤ P.gam σ a y := Real.sqrt_nonneg _

theorem gam_sum_le (σ : P.State) (a : Bool) : P.gam σ a true + P.gam σ a false ≤ 1 := by
  have h := fun y => sqrt_mul_le_avg (P.kw_nonneg false σ a y) (P.kw_nonneg true σ a y) one_pos
  have h1 := h true; have h0 := h false
  simp only [one_mul, div_one] at h1 h0
  unfold gam; simp only [kw, ite_true, Bool.false_eq_true, ite_false] at h1 h0 ⊢
  linarith

theorem kG_ok : P.KerOK P.kG := fun σ a => by
  unfold kG
  have h1 := P.gam_nonneg σ a true
  have h0 := P.gam_nonneg σ a false
  constructor
  · positivity
  · rcases (add_nonneg h1 h0).eq_or_lt with h | h
    · rw [← h, div_zero]; norm_num
    · rw [div_le_one h]; linarith

/-! ### The kernels before the stopping level -/

theorem ratio_bounds {Wr rr t s m : ℝ} (hW : Wr = rr * rr) (hr : 8 ≤ rr) (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht : t < Wr / 8) (hm : m = Wr / 2 + rr ∨ m = Wr / 2 - rr) :
    1 / 4 ≤ (m - s) / (Wr - t) ∧ (m - s) / (Wr - t) ≤ 3 / 4 := by
  have hpos : 0 < Wr - t := by nlinarith
  have hr8 : 8 * rr ≤ Wr := by nlinarith
  rw [le_div_iff₀ hpos, div_le_iff₀ hpos]
  rcases hm with hm | hm <;> subst hm <;> constructor <;> nlinarith

theorem cast_m_sub {b : Bool} {σ : P.State} {a : Bool} (hs : P.sA σ a ≤ P.mab b a) :
    ((P.mab b a - P.sA σ a : ℕ) : ℝ) = (P.mab b a : ℝ) - P.sA σ a := Nat.cast_sub hs

theorem mab_cases (b a : Bool) :
    (P.mab b a : ℝ) = P.W / 2 + P.r ∨ (P.mab b a : ℝ) = P.W / 2 - P.r := by
  unfold mab; split_ifs
  · exact Or.inl P.cast_mPlus
  · exact Or.inr P.cast_mMinus

theorem stop_facts {L : ℕ} (hL : L ≤ P.W / 8) {σ : P.State} (hD : ¬ L ≤ P.D σ) (a : Bool) :
    (P.tA σ a : ℝ) < P.W / 8 ∧ (P.sA σ a : ℝ) ≤ P.tA σ a := by
  have h1 := P.tA_le_D σ a
  have h2 := P.sA_le_tA σ a
  have h3 := P.W8_mul
  have : 8 * P.tA σ a < P.W := by omega
  constructor
  · have : (8 * P.tA σ a : ℝ) < P.W := by exact_mod_cast this
    linarith
  · exact_mod_cast h2

theorem kap_eq_ratio {L : ℕ} (hL : L ≤ P.W / 8) {σ : P.State} (hD : ¬ L ≤ P.D σ) (b a : Bool) :
    P.kap b σ a = ((P.mab b a : ℝ) - P.sA σ a) / ((P.W : ℝ) - P.tA σ a) ∧
      1 / 4 ≤ P.kap b σ a ∧ P.kap b σ a ≤ 3 / 4 := by
  obtain ⟨ht, hst⟩ := P.stop_facts hL hD a
  have hs0 : (0 : ℝ) ≤ P.sA σ a := Nat.cast_nonneg _
  have hb := ratio_bounds P.cast_W P.cast_r_ge hs0 hst ht (P.mab_cases b a)
  have hsm : P.sA σ a ≤ P.mab b a := by
    have hm := P.mab_cases b a
    have : (P.sA σ a : ℝ) ≤ P.mab b a := by
      have := P.cast_r_ge; have := P.cast_W
      rcases hm with hm | hm <;> rw [hm] <;> nlinarith
    exact_mod_cast this
  have htW : P.tA σ a ≤ P.W := by
    have : (P.tA σ a : ℝ) ≤ P.W := by
      have := P.cast_r_ge; have := P.cast_W; nlinarith
    exact_mod_cast this
  have heq : P.kap b σ a = ((P.mab b a : ℝ) - P.sA σ a) / ((P.W : ℝ) - P.tA σ a) := by
    unfold kap
    rw [P.cast_m_sub hsm, Nat.cast_sub htW, min_eq_right (by linarith)]
  rw [heq]
  exact ⟨rfl, hb⟩

/-- Before the stopping level, the two label probabilities differ by at most `4/r`, so their
squared difference is at most `16/W`. -/
theorem kap_diff_sq {L : ℕ} (hL : L ≤ P.W / 8) {σ : P.State} (hD : ¬ L ≤ P.D σ) (a : Bool) :
    (P.kap false σ a - P.kap true σ a) ^ 2 ≤ 16 / (P.W : ℝ) := by
  rw [(P.kap_eq_ratio hL hD false a).1, (P.kap_eq_ratio hL hD true a).1]
  obtain ⟨ht, -⟩ := P.stop_facts hL hD a
  have hW := P.cast_W
  have hr := P.cast_r_ge
  have hpos : (0 : ℝ) < P.W - P.tA σ a := by nlinarith
  have hdiff : ((P.mab false a : ℝ) - P.sA σ a) / ((P.W : ℝ) - P.tA σ a) -
      ((P.mab true a : ℝ) - P.sA σ a) / ((P.W : ℝ) - P.tA σ a) =
      ((P.mab false a : ℝ) - P.mab true a) / ((P.W : ℝ) - P.tA σ a) := by
    field_simp; ring
  have hm : ((P.mab false a : ℝ) - P.mab true a) ^ 2 = 4 * (P.r : ℝ) ^ 2 := by
    unfold mab
    cases a
    · simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [P.cast_mPlus, P.cast_mMinus]; ring
    · simp only [ite_true, Bool.true_eq_false, ite_false]
      rw [P.cast_mPlus, P.cast_mMinus]; ring
  have hWp : (0 : ℝ) < P.W := by rw [hW]; nlinarith
  rw [hdiff, div_pow, hm, div_le_div_iff₀ (pow_pos hpos 2) hWp]
  have h7 : 7 * (P.W : ℝ) / 8 ≤ P.W - P.tA σ a := by linarith
  have hsq : (7 * (P.W : ℝ) / 8) ^ 2 ≤ ((P.W : ℝ) - P.tA σ a) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h7 2
  rw [hW] at hsq ⊢
  nlinarith

/-- The per-step affinity deficit before the stopping level: `1 - γ_1 - γ_0 ≤ 16/W`. -/
theorem gam_deficit {L : ℕ} (hL : L ≤ P.W / 8) {σ : P.State} (hD : ¬ L ≤ P.D σ) (a : Bool) :
    1 - (P.gam σ a true + P.gam σ a false) ≤ 16 / (P.W : ℝ) := by
  obtain ⟨-, h0a, h0b⟩ := P.kap_eq_ratio hL hD false a
  obtain ⟨-, h1a, h1b⟩ := P.kap_eq_ratio hL hD true a
  have := bernoulli_affinity h0a h0b h1a h1b
  have hd := P.kap_diff_sq hL hD a
  unfold gam kw; simp only [ite_true, Bool.false_eq_true, ite_false]
  linarith

theorem gam_pos {L : ℕ} (hL : L ≤ P.W / 8) {σ : P.State} (hD : ¬ L ≤ P.D σ) (a y : Bool) :
    0 < P.gam σ a y := by
  obtain ⟨-, h0a, h0b⟩ := P.kap_eq_ratio hL hD false a
  obtain ⟨-, h1a, h1b⟩ := P.kap_eq_ratio hL hD true a
  unfold gam kw
  apply Real.sqrt_pos.mpr
  cases y <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> nlinarith

/-! ### The recursive affinity -/

/-- The affinity of the two stopped transcript processes, defined recursively. -/
noncomputable def bcRec (L : ℕ) : TT P β → P.State → ℝ
  | .ret _, _ => 1
  | .sample p k, σ => if L ≤ P.D σ then 1 else ∑' x, (p x).toReal * bcRec L (k x) σ
  | .test a j i kf ks, σ =>
      if L ≤ P.D σ then 1 else
        match σ a j with
        | .disc i₀ y₀ => if i = i₀ then bcRec L (ks y₀) σ else bcRec L kf σ
        | .undisc E =>
            if i ∈ E then bcRec L kf σ else
              (P.gam σ a true * bcRec L (ks true) (P.setDisc σ a j i true) +
                  P.gam σ a false * bcRec L (ks false) (P.setDisc σ a j i false)) / P.dd E +
                (P.dd E - 1) / P.dd E * bcRec L kf (P.setExcl σ a j E i)

theorem bcRec_mem (L : ℕ) : ∀ (t : TT P β) σ, 0 ≤ P.bcRec L t σ ∧ P.bcRec L t σ ≤ 1 := by
  intro t
  induction t with
  | ret b => intro σ; simp [bcRec]
  | sample p k ih =>
      intro σ; simp only [bcRec]; split_ifs
      · norm_num
      · have hb : ∀ x, |P.bcRec L (k x) σ| ≤ 1 := fun x => by
          rw [abs_le]; constructor <;> linarith [(ih x σ).1, (ih x σ).2]
        exact ⟨le_tsum_pmf p hb fun x _ => (ih x σ).1, tsum_pmf_le p hb fun x _ => (ih x σ).2⟩
  | test a j i kf ks ihf ihs =>
      intro σ; simp only [bcRec]; split_ifs
      · norm_num
      · split
        · split_ifs
          · exact ihs _ _
          · exact ihf _
        · rename_i E _
          split_ifs with hi
          · exact ihf _
          · have hd := P.one_le_dd hi
            have hdp : 0 < P.dd E := by linarith
            have g1 := P.gam_nonneg σ a true
            have g0 := P.gam_nonneg σ a false
            have gs := P.gam_sum_le σ a
            obtain ⟨b1, b1'⟩ := ihs true (P.setDisc σ a j i true)
            obtain ⟨b0, b0'⟩ := ihs false (P.setDisc σ a j i false)
            obtain ⟨bf, bf'⟩ := ihf (P.setExcl σ a j E i)
            have hw : 0 ≤ (P.dd E - 1) / P.dd E := div_nonneg (by linarith) hdp.le
            constructor
            · positivity
            · have : P.gam σ a true * P.bcRec L (ks true) (P.setDisc σ a j i true) +
                  P.gam σ a false * P.bcRec L (ks false) (P.setDisc σ a j i false) ≤ 1 := by
                nlinarith
              have e1 : (P.gam σ a true * P.bcRec L (ks true) (P.setDisc σ a j i true) +
                  P.gam σ a false * P.bcRec L (ks false) (P.setDisc σ a j i false)) / P.dd E ≤
                  1 / P.dd E := div_le_div_of_nonneg_right this hdp.le
              have e2 : (P.dd E - 1) / P.dd E * P.bcRec L kf (P.setExcl σ a j E i) ≤
                  (P.dd E - 1) / P.dd E := by nlinarith
              have : 1 / P.dd E + (P.dd E - 1) / P.dd E = 1 := by field_simp; ring
              linarith

/-! ### Equations for `bcRec` -/

section Equations

variable {P} {L : ℕ}

theorem bcRec_stop {σ : P.State} (h : L ≤ P.D σ) (t : TT P β) : P.bcRec L t σ = 1 := by
  cases t <;> simp [bcRec, h]

theorem bcRec_sample {σ : P.State} (h : ¬ L ≤ P.D σ) {γ : Type} (p : PMF γ) (k : γ → TT P β) :
    P.bcRec L (.sample p k) σ = ∑' x, (p x).toReal * P.bcRec L (k x) σ := by
  simp [bcRec, h]

theorem bcRec_test_disc {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k}
    {i i₀ : Fin P.ℓ} {y₀ : Bool} (hσ : σ a j = .disc i₀ y₀) (kf : TT P β) (ks : Bool → TT P β) :
    P.bcRec L (.test a j i kf ks) σ = if i = i₀ then P.bcRec L (ks y₀) σ else P.bcRec L kf σ := by
  simp only [bcRec, h, ite_false, hσ]

theorem bcRec_test_mem {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k} {i : Fin P.ℓ}
    {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (hi : i ∈ E) (kf : TT P β)
    (ks : Bool → TT P β) : P.bcRec L (.test a j i kf ks) σ = P.bcRec L kf σ := by
  simp only [bcRec, h, ite_false, hσ, hi, ite_true]

theorem bcRec_test_fresh {σ : P.State} (h : ¬ L ≤ P.D σ) {a : Bool} {j : Str P.k}
    {i : Fin P.ℓ} {E : Finset (Fin P.ℓ)} (hσ : σ a j = .undisc E) (hi : i ∉ E) (kf : TT P β)
    (ks : Bool → TT P β) :
    P.bcRec L (.test a j i kf ks) σ =
      (P.gam σ a true * P.bcRec L (ks true) (P.setDisc σ a j i true) +
          P.gam σ a false * P.bcRec L (ks false) (P.setDisc σ a j i false)) / P.dd E +
        (P.dd E - 1) / P.dd E * P.bcRec L kf (P.setExcl σ a j E i) := by
  simp only [bcRec, h, ite_false, hσ, hi]

end Equations

/-! ### Stopped output laws -/

open Classical in
/-- The point payoff `[o' = o]`. -/
noncomputable def gpt (o : Option β) : P.State → Option β → ℝ := fun _ o' => if o' = o then 1 else 0

/-- The stopped output law under root `b` (stopping outputs `none`). -/
noncomputable def Lpt (b : Bool) (L : ℕ) (t : TT P β) (σ : P.State) (o : Option β) : ℝ :=
  P.val (P.kap b) L (P.gpt o) t σ

theorem abs_gpt_le (o : Option β) (σ : P.State) (o' : Option β) : |P.gpt o σ o'| ≤ 1 := by
  unfold gpt; split_ifs <;> norm_num

theorem Lpt_nonneg (b : Bool) (L : ℕ) (t : TT P β) (σ : P.State) (o : Option β) :
    0 ≤ P.Lpt b L t σ o := by
  have h := P.val_mono (P.kap_ok b) L (g₁ := fun _ _ => (0 : ℝ)) (g₂ := P.gpt o) (M₁ := 0)
    (M₂ := 1) (fun _ _ => by simp) (P.abs_gpt_le o) (fun σ _ => by unfold gpt; split_ifs <;>
      norm_num) (fun σ b => by unfold gpt; split_ifs <;> norm_num) t σ
  rwa [P.val_const L (fun _ _ => rfl)] at h

theorem Lpt_le_one (b : Bool) (L : ℕ) (t : TT P β) (σ : P.State) (o : Option β) :
    P.Lpt b L t σ o ≤ 1 :=
  le_of_abs_le (P.val_abs_le (P.kap_ok b) L (P.abs_gpt_le o) t σ)

theorem sum_Lpt [Fintype β] (b : Bool) (L : ℕ) (t : TT P β) (σ : P.State) :
    ∑ o, P.Lpt b L t σ o = 1 := by
  classical
  unfold Lpt
  rw [← P.val_sum (P.kap_ok b) L Finset.univ (fun o => P.gpt o) (fun o => P.abs_gpt_le o)]
  exact P.val_const L (fun σ o' => by simp [gpt]) t σ

theorem sum_sqrt_gpt [Fintype β] (o₀ : Option β) (σ : P.State) :
    ∑ o : Option β, Real.sqrt (P.gpt o σ o₀ * P.gpt o σ o₀) = 1 := by
  classical
  have : ∀ o, Real.sqrt (P.gpt o σ o₀ * P.gpt o σ o₀) = if o₀ = o then 1 else 0 := by
    intro o; unfold gpt; split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun o _ => this o, Finset.sum_ite_eq]
  simp

theorem sqrt_prod4 {c c' x y : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    Real.sqrt (c * x * (c' * y)) = Real.sqrt (c * c') * Real.sqrt (x * y) := by
  rw [← Real.sqrt_mul (mul_nonneg hc hc')]; congr 1; ring

theorem sqrt_div_sq {x x' d : ℝ} (hd : 0 < d) : Real.sqrt (x / d * (x' / d)) =
    Real.sqrt (x * x') / d := by
  rw [show x / d * (x' / d) = x * x' / d ^ 2 by ring, Real.sqrt_div' _ (sq_nonneg d),
    Real.sqrt_sq hd.le]

theorem sqrt_Lpt_le_one (L : ℕ) (t : TT P β) (σ : P.State) (o : Option β) :
    Real.sqrt (P.Lpt false L t σ o * P.Lpt true L t σ o) ≤ 1 :=
  calc Real.sqrt (P.Lpt false L t σ o * P.Lpt true L t σ o) ≤ Real.sqrt (1 * 1) :=
        Real.sqrt_le_sqrt (mul_le_mul (P.Lpt_le_one false L t σ o)
          (P.Lpt_le_one true L t σ o) (P.Lpt_nonneg true L t σ o) zero_le_one)
    _ = 1 := by simp

/-- `pw-lem:information`, mixture step (concavity of the affinity under mixtures): the
affinity of the two stopped output laws is at least `bcRec`. -/
theorem bc_le_affinity [Fintype β] (L : ℕ) : ∀ (t : TT P β) σ,
    P.bcRec L t σ ≤ ∑ o : Option β, Real.sqrt (P.Lpt false L t σ o * P.Lpt true L t σ o) := by
  classical
  intro t
  induction t with
  | ret c =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · simp only [Lpt, val_stop hstop, bcRec_stop hstop]; rw [sum_sqrt_gpt]
      · simp only [Lpt, val_ret hstop, bcRec]; rw [sum_sqrt_gpt]
  | sample p k ih =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · simp only [Lpt, val_stop hstop, bcRec_stop hstop]; rw [sum_sqrt_gpt]
      · rw [bcRec_sample hstop]
        have hL : ∀ b o, P.Lpt b L (.sample p k) σ o =
            ∑' x, (p x).toReal * P.Lpt b L (k x) σ o := fun b o => by
          simp only [Lpt, val_sample hstop]
        simp only [hL]
        have hb := fun b x o => P.Lpt_nonneg b L (k x) σ o
        have hb1 := fun b x o => P.Lpt_le_one b L (k x) σ o
        -- termwise Cauchy–Schwarz
        have hcs : ∀ o, ∑' x, (p x).toReal *
            Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o) ≤
            Real.sqrt ((∑' x, (p x).toReal * P.Lpt false L (k x) σ o) *
              ∑' x, (p x).toReal * P.Lpt true L (k x) σ o) := by
          intro o
          have hsa : Summable fun x => (p x).toReal * P.Lpt false L (k x) σ o :=
            summable_pmf_mul p (M := 1) fun x => by
              rw [abs_of_nonneg (hb false x o)]; exact hb1 false x o
          have hsb : Summable fun x => (p x).toReal * P.Lpt true L (k x) σ o :=
            summable_pmf_mul p (M := 1) fun x => by
              rw [abs_of_nonneg (hb true x o)]; exact hb1 true x o
          have := tsum_sqrt_mul_le (fun x => mul_nonneg ENNReal.toReal_nonneg (hb false x o))
            (fun x => mul_nonneg ENNReal.toReal_nonneg (hb true x o)) hsa hsb
          rw [← Real.sqrt_mul (tsum_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg
            (hb false x o))] at this
          refine le_trans (le_of_eq (tsum_congr fun x => ?_)) this
          rw [sqrt_mul_mul_sqrt ENNReal.toReal_nonneg]
        have hsx : ∀ o, Summable fun x => (p x).toReal *
            Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o) := fun o =>
          summable_pmf_mul p (M := 1) fun x => by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact P.sqrt_Lpt_le_one L (k x) σ o
        have hswap : ∑ o, ∑' x, (p x).toReal *
            Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o) =
            ∑' x, (p x).toReal * ∑ o, Real.sqrt (P.Lpt false L (k x) σ o *
              P.Lpt true L (k x) σ o) := by
          rw [← Summable.tsum_finsetSum fun o _ => hsx o]
          exact tsum_congr fun x => by rw [Finset.mul_sum]
        have hBCb : ∀ x, |∑ o, Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o)| ≤
            Fintype.card (Option β) := fun x => by
          rw [abs_of_nonneg (Finset.sum_nonneg fun o _ => Real.sqrt_nonneg _)]
          calc ∑ o, Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o)
              ≤ ∑ _o : Option β, (1 : ℝ) :=
                Finset.sum_le_sum fun o _ => P.sqrt_Lpt_le_one L (k x) σ o
            _ = Fintype.card (Option β) := by simp
        have hbc : ∀ x, |P.bcRec L (k x) σ| ≤ 1 := fun x => by
          rw [abs_le]; constructor <;> linarith [(P.bcRec_mem L (k x) σ).1,
            (P.bcRec_mem L (k x) σ).2]
        calc ∑' x, (p x).toReal * P.bcRec L (k x) σ
            ≤ ∑' x, (p x).toReal * ∑ o, Real.sqrt (P.Lpt false L (k x) σ o *
                P.Lpt true L (k x) σ o) :=
              Summable.tsum_le_tsum
                (fun x => mul_le_mul_of_nonneg_left (ih x σ) ENNReal.toReal_nonneg)
                (summable_pmf_mul p hbc) (summable_pmf_mul p hBCb)
          _ = ∑ o, ∑' x, (p x).toReal *
                Real.sqrt (P.Lpt false L (k x) σ o * P.Lpt true L (k x) σ o) := hswap.symm
          _ ≤ _ := Finset.sum_le_sum fun o _ => hcs o
  | test a j i kf ks ihf ihs =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · simp only [Lpt, val_stop hstop, bcRec_stop hstop]; rw [sum_sqrt_gpt]
      · cases hσ : σ a j with
        | disc i₀ y₀ =>
            rw [bcRec_test_disc hstop hσ]
            simp only [Lpt, val_test_disc hstop hσ]
            split_ifs
            · exact ihs _ _
            · exact ihf _
        | undisc E =>
            by_cases hi : i ∈ E
            · rw [bcRec_test_mem hstop hσ hi]
              simp only [Lpt, val_test_mem hstop hσ hi]
              exact ihf _
            · rw [bcRec_test_fresh hstop hσ hi]
              have hfr : ∀ b o, P.Lpt b L (.test a j i kf ks) σ o =
                  mixF (P.kap b σ a) (P.dd E) (P.Lpt b L (ks true) (P.setDisc σ a j i true) o)
                    (P.Lpt b L (ks false) (P.setDisc σ a j i false) o)
                    (P.Lpt b L kf (P.setExcl σ a j E i) o) := fun b o => by
                simp only [Lpt, val_test_fresh hstop hσ hi]
              simp only [hfr]
              have hd := P.one_le_dd hi
              have hdp : 0 < P.dd E := by linarith
              set d := P.dd E
              have hk := fun b => P.kap_ok b σ a
              set v1 := fun b o => P.Lpt b L (ks true) (P.setDisc σ a j i true) o
              set v0 := fun b o => P.Lpt b L (ks false) (P.setDisc σ a j i false) o
              set vf := fun b o => P.Lpt b L kf (P.setExcl σ a j E i) o
              have hv1 := fun b o => P.Lpt_nonneg b L (ks true) (P.setDisc σ a j i true) o
              have hv0 := fun b o => P.Lpt_nonneg b L (ks false) (P.setDisc σ a j i false) o
              have hvf := fun b o => P.Lpt_nonneg b L kf (P.setExcl σ a j E i) o
              have hmix : ∀ b o, mixF (P.kap b σ a) d (v1 b o) (v0 b o) (vf b o) =
                  P.kap b σ a / d * v1 b o + (1 - P.kap b σ a) / d * v0 b o +
                    (d - 1) / d * vf b o := fun b o => by unfold mixF; ring
              have hterm : ∀ o, P.gam σ a true / d * Real.sqrt (v1 false o * v1 true o) +
                  P.gam σ a false / d * Real.sqrt (v0 false o * v0 true o) +
                  (d - 1) / d * Real.sqrt (vf false o * vf true o) ≤
                  Real.sqrt (mixF (P.kap false σ a) d (v1 false o) (v0 false o) (vf false o) *
                    mixF (P.kap true σ a) d (v1 true o) (v0 true o) (vf true o)) := by
                intro o
                rw [hmix, hmix]
                have c1 : 0 ≤ P.kap false σ a / d := div_nonneg (hk false).1 hdp.le
                have c1' : 0 ≤ P.kap true σ a / d := div_nonneg (hk true).1 hdp.le
                have c0 : 0 ≤ (1 - P.kap false σ a) / d :=
                  div_nonneg (by linarith [hk false]) hdp.le
                have c0' : 0 ≤ (1 - P.kap true σ a) / d :=
                  div_nonneg (by linarith [hk true]) hdp.le
                have cf : 0 ≤ (d - 1) / d := div_nonneg (by linarith) hdp.le
                refine le_trans (le_of_eq ?_) (sqrt_three_le (mul_nonneg c1 (hv1 false o))
                  (mul_nonneg c0 (hv0 false o)) (mul_nonneg cf (hvf false o))
                  (mul_nonneg c1' (hv1 true o)) (mul_nonneg c0' (hv0 true o))
                  (mul_nonneg cf (hvf true o)))
                rw [sqrt_prod4 c1 c1', sqrt_prod4 c0 c0', sqrt_prod4 cf cf, sqrt_div_sq hdp,
                  sqrt_div_sq hdp, Real.sqrt_mul_self cf]
                unfold gam kw
                simp only [ite_true, Bool.false_eq_true, ite_false]
              calc (P.gam σ a true * P.bcRec L (ks true) (P.setDisc σ a j i true) +
                    P.gam σ a false * P.bcRec L (ks false) (P.setDisc σ a j i false)) / d +
                    (d - 1) / d * P.bcRec L kf (P.setExcl σ a j E i)
                  ≤ (P.gam σ a true * ∑ o, Real.sqrt (v1 false o * v1 true o) +
                    P.gam σ a false * ∑ o, Real.sqrt (v0 false o * v0 true o)) / d +
                    (d - 1) / d * ∑ o, Real.sqrt (vf false o * vf true o) := by
                    have g1 := P.gam_nonneg σ a true
                    have g0 := P.gam_nonneg σ a false
                    have cf : 0 ≤ (d - 1) / d := div_nonneg (by linarith) hdp.le
                    have i1 := mul_le_mul_of_nonneg_left (ihs true (P.setDisc σ a j i true)) g1
                    have i0 := mul_le_mul_of_nonneg_left
                      (ihs false (P.setDisc σ a j i false)) g0
                    have i2 := mul_le_mul_of_nonneg_left (ihf (P.setExcl σ a j E i)) cf
                    have := div_le_div_of_nonneg_right (add_le_add i1 i0) hdp.le
                    linarith
                _ = ∑ o, (P.gam σ a true / d * Real.sqrt (v1 false o * v1 true o) +
                    P.gam σ a false / d * Real.sqrt (v0 false o * v0 true o) +
                    (d - 1) / d * Real.sqrt (vf false o * vf true o)) := by
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
                      ← Finset.mul_sum, ← Finset.mul_sum]
                    ring
                _ ≤ _ := Finset.sum_le_sum fun o _ => hterm o

/-- `pw-lem:information`, chain-rule step (with the Hellinger affinity in place of the KL
divergence): `1 - bcRec ≤ (16/W) (E_Ĝ D - D)` for the process stopped at `L ≤ W/8`. -/
theorem one_sub_bcRec_le {L : ℕ} (hL : L ≤ P.W / 8) : ∀ (t : TT P β) σ,
    1 - P.bcRec L t σ ≤ 16 / (P.W : ℝ) * (P.val P.kG L P.gD t σ - P.D σ) := by
  have hWp : (0 : ℝ) < P.W := by have := P.cast_W; have := P.cast_r_ge; nlinarith
  have hcH : 0 < 16 / (P.W : ℝ) := by positivity
  intro t
  induction t with
  | ret c =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · rw [bcRec_stop hstop, val_stop hstop]; simp [gD]
      · rw [val_ret hstop]; simp [bcRec, gD]
  | sample p k ih =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · rw [bcRec_stop hstop, val_stop hstop]; simp [gD]
      · rw [bcRec_sample hstop, val_sample hstop]
        set cH := 16 / (P.W : ℝ)
        have hv : ∀ x, |P.val P.kG L P.gD (k x) σ| ≤ 2 * P.W := fun x =>
          P.val_abs_le P.kG_ok L (fun σ o => P.abs_gD_le σ o) (k x) σ
        have hbc : ∀ x, |P.bcRec L (k x) σ| ≤ 1 := fun x => by
          rw [abs_le]; constructor <;> linarith [(P.bcRec_mem L (k x) σ).1,
            (P.bcRec_mem L (k x) σ).2]
        have hs1 := summable_pmf_mul p hv
        have hle : ∀ x, (p x).toReal * (1 + cH * P.D σ) - cH * ((p x).toReal *
            P.val P.kG L P.gD (k x) σ) ≤ (p x).toReal * P.bcRec L (k x) σ := fun x => by
          have := mul_le_mul_of_nonneg_left (ih x σ) (ENNReal.toReal_nonneg (a := p x))
          nlinarith
        have hsum := Summable.tsum_le_tsum hle
          (((pmf_summable_toReal p).mul_right _).sub (hs1.mul_left cH))
          (summable_pmf_mul p hbc)
        rw [Summable.tsum_sub ((pmf_summable_toReal p).mul_right _) (hs1.mul_left cH),
          tsum_pmf_const, tsum_mul_left] at hsum
        nlinarith
  | test a j i kf ks ihf ihs =>
      intro σ
      by_cases hstop : L ≤ P.D σ
      · rw [bcRec_stop hstop, val_stop hstop]; simp [gD]
      · cases hσ : σ a j with
        | disc i₀ y₀ =>
            rw [bcRec_test_disc hstop hσ, val_test_disc hstop hσ]
            split_ifs
            · exact ihs _ _
            · exact ihf _
        | undisc E =>
            by_cases hi : i ∈ E
            · rw [bcRec_test_mem hstop hσ hi, val_test_mem hstop hσ hi]; exact ihf _
            · rw [bcRec_test_fresh hstop hσ hi, val_test_fresh hstop hσ hi]
              set cH := 16 / (P.W : ℝ)
              have hd := P.one_le_dd hi
              have hdp : 0 < P.dd E := by linarith
              set d := P.dd E
              have g1 := P.gam_pos hL hstop a true
              have g0 := P.gam_pos hL hstop a false
              have gs := P.gam_sum_le σ a
              have gdef := P.gam_deficit hL hstop a
              set γ1 := P.gam σ a true
              set γ0 := P.gam σ a false
              have hkG : P.kG σ a = γ1 / (γ1 + γ0) := rfl
              set B1 := P.bcRec L (ks true) (P.setDisc σ a j i true)
              set B0 := P.bcRec L (ks false) (P.setDisc σ a j i false)
              set Bf := P.bcRec L kf (P.setExcl σ a j E i)
              set v1 := P.val P.kG L P.gD (ks true) (P.setDisc σ a j i true)
              set v0 := P.val P.kG L P.gD (ks false) (P.setDisc σ a j i false)
              set vf := P.val P.kG L P.gD kf (P.setExcl σ a j E i)
              have i1 : 1 - B1 ≤ cH * (v1 - (P.D σ + 1)) := by
                have := ihs true (P.setDisc σ a j i true)
                rw [P.D_setDisc hσ] at this; push_cast at this; exact this
              have i0 : 1 - B0 ≤ cH * (v0 - (P.D σ + 1)) := by
                have := ihs false (P.setDisc σ a j i false)
                rw [P.D_setDisc hσ] at this; push_cast at this; exact this
              have iF : 1 - Bf ≤ cH * (vf - P.D σ) := by
                have := ihf (P.setExcl σ a j E i)
                rw [P.D_setExcl hσ] at this; exact this
              have hB1 := (P.bcRec_mem L (ks true) (P.setDisc σ a j i true)).2
              have hB0 := (P.bcRec_mem L (ks false) (P.setDisc σ a j i false)).2
              have hβ : 0 < γ1 + γ0 := by linarith
              have hX : 1 - (γ1 * B1 + γ0 * B0) ≤
                  cH * (γ1 / (γ1 + γ0) * v1 + (1 - γ1 / (γ1 + γ0)) * v0 - P.D σ) := by
                have k1 : γ1 * (1 - B1) ≤ γ1 / (γ1 + γ0) * (1 - B1) := by
                  apply mul_le_mul_of_nonneg_right _ (by linarith)
                  rw [le_div_iff₀ hβ]; nlinarith
                have k0 : γ0 * (1 - B0) ≤ (1 - γ1 / (γ1 + γ0)) * (1 - B0) := by
                  apply mul_le_mul_of_nonneg_right _ (by linarith)
                  rw [show 1 - γ1 / (γ1 + γ0) = γ0 / (γ1 + γ0) by field_simp; ring,
                    le_div_iff₀ hβ]
                  nlinarith
                have w1 : 0 ≤ γ1 / (γ1 + γ0) := by positivity
                have w0 : 0 ≤ 1 - γ1 / (γ1 + γ0) := by
                  rw [show 1 - γ1 / (γ1 + γ0) = γ0 / (γ1 + γ0) by field_simp; ring]
                  positivity
                have m1 := mul_le_mul_of_nonneg_left i1 w1
                have m0 := mul_le_mul_of_nonneg_left i0 w0
                nlinarith
              rw [hkG]
              unfold mixF
              have hw : 0 ≤ (d - 1) / d := div_nonneg (by linarith) hdp.le
              have mF := mul_le_mul_of_nonneg_left iF hw
              have e1 : 1 - ((γ1 * B1 + γ0 * B0) / d + (d - 1) / d * Bf) =
                  (1 - (γ1 * B1 + γ0 * B0)) / d + (d - 1) / d * (1 - Bf) := by
                field_simp; ring
              have e2 : cH * ((γ1 / (γ1 + γ0) * v1 + (1 - γ1 / (γ1 + γ0)) * v0) / d +
                  (d - 1) / d * vf - P.D σ) =
                  cH * (γ1 / (γ1 + γ0) * v1 + (1 - γ1 / (γ1 + γ0)) * v0 - P.D σ) / d +
                    (d - 1) / d * (cH * (vf - P.D σ)) := by
                field_simp; ring
              rw [e1, e2]
              have := div_le_div_of_nonneg_right hX hdp.le
              linarith

end Prm

end LearningGuided.PointwiseLB
