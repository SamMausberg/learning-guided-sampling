import LearningGuided.PointwiseLB.Process

/-!
# The search potential (Lemma `pw-lem:search`)

The potential `Φ = ((ℓ-1)/2) D + (1/2) ∑_{undiscovered (a,j)} f_{a,j}` of `pw-eq:potential`
increases in expectation by exactly the failure probability of a fresh test, and does not change
at a test whose outcome is determined. Since a test tree with failure budget `q` fails at most
`q` times on every execution, `E Φ ≤ Φ(start) + q`, and hence `E D ≤ 2q/(ℓ-1)`
(`pw-eq:discoveries`). The statement holds for every label kernel (in particular under either
root `b`), with or without stopping, and so also for a process stopped partway through a batch.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Prm

variable (P : Prm) {β : Type}

/-- The potential `pw-eq:potential`. -/
noncomputable def Phi (σ : P.State) : ℝ :=
  ((P.ℓ : ℝ) - 1) / 2 * P.D σ + 1 / 2 * P.exclSum σ

/-- The payoff `Φ` of the final state. -/
noncomputable def gPhi : P.State → Option β → ℝ := fun σ _ => P.Phi σ

/-- The payoff `D` of the final state. -/
noncomputable def gD : P.State → Option β → ℝ := fun σ _ => (P.D σ : ℝ)

theorem exclSum_le (σ : P.State) : P.exclSum σ ≤ 2 * P.W * P.ℓ := by
  unfold exclSum
  calc ∑ p : Bool × Str P.k, (σ p.1 p.2).exclN ≤ ∑ _p : Bool × Str P.k, P.ℓ :=
        Finset.sum_le_sum fun p _ => by
          cases σ p.1 p.2 with
          | disc _ _ => simp [RowSt.exclN]
          | undisc E => simpa [RowSt.exclN] using Finset.card_le_univ E
    _ = 2 * P.W * P.ℓ := by simp [Fintype.card_prod, P.card_rows]

theorem Phi_nonneg (σ : P.State) : 0 ≤ P.Phi σ := by
  unfold Phi
  have : (1 : ℝ) ≤ P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 ≤ P.ℓ)
  have : (0 : ℝ) ≤ ((P.ℓ : ℝ) - 1) / 2 := by linarith
  positivity

/-- A uniform bound on `Φ`. -/
noncomputable def PhiMax : ℝ := ((P.ℓ : ℝ) - 1) / 2 * (2 * P.W) + 1 / 2 * (2 * P.W * P.ℓ)

theorem abs_Phi_le (σ : P.State) : |P.Phi σ| ≤ P.PhiMax := by
  rw [abs_of_nonneg (P.Phi_nonneg σ)]
  unfold Phi PhiMax
  have h1 : (P.D σ : ℝ) ≤ 2 * P.W := by exact_mod_cast P.D_le σ
  have h2 : (P.exclSum σ : ℝ) ≤ 2 * P.W * P.ℓ := by exact_mod_cast P.exclSum_le σ
  have : (1 : ℝ) ≤ P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 ≤ P.ℓ)
  have : (0 : ℝ) ≤ ((P.ℓ : ℝ) - 1) / 2 := by linarith
  nlinarith

theorem abs_gD_le (σ : P.State) (o : Option β) : |P.gD σ o| ≤ 2 * P.W := by
  unfold gD; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast P.D_le σ

theorem Phi_setDisc {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) (i : Fin P.ℓ) (y : Bool) :
    P.Phi (P.setDisc σ a j i y) = P.Phi σ + (P.dd E - 1) / 2 := by
  unfold Phi dd
  rw [P.D_setDisc hσ]
  have h := P.exclSum_setDisc hσ i y
  have h' : (P.exclSum (P.setDisc σ a j i y) : ℝ) + E.card = P.exclSum σ := by
    exact_mod_cast h
  push_cast
  linarith

theorem Phi_setExcl {σ : P.State} {a : Bool} {j : Str P.k} {E : Finset (Fin P.ℓ)}
    (hσ : σ a j = .undisc E) {i : Fin P.ℓ} (hi : i ∉ E) :
    P.Phi (P.setExcl σ a j E i) = P.Phi σ + 1 / 2 := by
  unfold Phi
  rw [P.D_setExcl hσ, P.exclSum_setExcl hσ hi]
  push_cast
  ring

theorem D_le_Phi (σ : P.State) : ((P.ℓ : ℝ) - 1) / 2 * P.D σ ≤ P.Phi σ := by
  unfold Phi; have : (0 : ℝ) ≤ P.exclSum σ := Nat.cast_nonneg _; linarith

theorem within_test_succ {T : P.Tables} {a : Bool} {j : Str P.k} {i : Fin P.ℓ}
    {kf : TT P β} {ks : Bool → TT P β} {q : ℕ} (h : (TT.test a j i kf ks).Within T q)
    (hT : T.1 a j = i) : (ks (T.2 a j)).Within T q := by
  simp only [TT.Within, ite_eq_left hT] at h; exact h

theorem within_test_fail {T : P.Tables} {a : Bool} {j : Str P.k} {i : Fin P.ℓ}
    {kf : TT P β} {ks : Bool → TT P β} {q : ℕ} (h : (TT.test a j i kf ks).Within T q)
    (hT : T.1 a j ≠ i) : ∃ q', q = q' + 1 ∧ kf.Within T q' := by
  simp only [TT.Within, ite_eq_right hT] at h; exact h

/-- `pw-lem:search`, potential form: for every label kernel `K`, every stopping level `L`
and every reachability predicate compatible with the process, a test tree whose executions
against all consistent valid tables have at most `q` failures satisfies `E Φ ≤ Φ(σ) + q`. -/
theorem potential {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ)
    (Reach : P.State → Prop)
    (hR1 : ∀ σ, Reach σ → (P.Cset σ).Nonempty)
    (hR2 : ∀ σ a j E i, Reach σ → ¬ L ≤ P.D σ → σ a j = .undisc E → i ∉ E → 1 < P.dd E →
      Reach (P.setExcl σ a j E i))
    (hR3 : ∀ σ a j E i, Reach σ → ¬ L ≤ P.D σ → σ a j = .undisc E → i ∉ E →
      (0 < K σ a → Reach (P.setDisc σ a j i true)) ∧
        (K σ a < 1 → Reach (P.setDisc σ a j i false))) :
    ∀ (t : TT P β) (σ : P.State) (q : ℕ), Reach σ → (∀ T ∈ P.Cset σ, t.Within T q) →
      P.val K L P.gPhi t σ ≤ P.Phi σ + q := by
  intro t
  induction t with
  | ret b =>
      intro σ q _ _
      simp only [val, gPhi]; split_ifs <;> linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  | sample p k ih =>
      intro σ q hR hW
      simp only [val]
      split_ifs
      · simp only [gPhi]; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      · refine tsum_pmf_le p (M := P.PhiMax)
          (fun x => P.val_abs_le hK L (fun σ _ => P.abs_Phi_le σ) (k x) σ) fun x hx => ?_
        exact ih x σ q hR fun T hT => hW T hT x ((PMF.mem_support_iff p x).mpr hx)
  | test a j i kf ks ihf ihs =>
      intro σ q hR hW
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      simp only [val]
      split_ifs with hstop
      · simp only [gPhi]; linarith
      · -- a failed test against every consistent table lowers the budget by one
        have hfail : (∀ T ∈ P.Cset σ, T.1 a j ≠ i) →
            P.val K L P.gPhi kf σ ≤ P.Phi σ + q := by
          intro hne
          obtain ⟨T₀, hT₀⟩ := hR1 σ hR
          obtain ⟨q₀, hq₀, -⟩ := P.within_test_fail (hW T₀ hT₀) (hne T₀ hT₀)
          have hb : ∀ T ∈ P.Cset σ, kf.Within T q₀ := by
            intro T hT
            obtain ⟨q₁, hq₁, hW₁⟩ := P.within_test_fail (hW T hT) (hne T hT)
            have : q₁ = q₀ := by omega
            rwa [this] at hW₁
          have := ihf σ q₀ hR hb
          have : (q₀ : ℝ) ≤ q := by exact_mod_cast (by omega : q₀ ≤ q)
          linarith
        split
        · rename_i i₀ y₀ hσ
          have hcons : ∀ T ∈ P.Cset σ, T.1 a j = i₀ ∧ T.2 a j = y₀ := by
            intro T hT; have := P.cons_of_mem_Cset hT a j; rw [hσ] at this; exact this
          split_ifs with hii
          · refine ihs y₀ σ q hR fun T hT => ?_
            have := P.within_test_succ (hW T hT) ((hcons T hT).1.trans hii.symm)
            rwa [(hcons T hT).2] at this
          · exact hfail fun T hT h => hii (h ▸ (hcons T hT).1)
        · rename_i E hσ
          have hcons : ∀ T ∈ P.Cset σ, T.1 a j ∉ E := by
            intro T hT; have := P.cons_of_mem_Cset hT a j; rw [hσ] at this; exact this
          split_ifs with hiE
          · exact hfail fun T hT h => hcons T hT (h ▸ hiE)
          · have hd := P.one_le_dd hiE
            obtain ⟨hk0, hk1⟩ := hK σ a
            have hsucc : ∀ y : Bool, Reach (P.setDisc σ a j i y) →
                P.val K L P.gPhi (ks y) (P.setDisc σ a j i y) ≤
                  P.Phi σ + (P.dd E - 1) / 2 + q := by
              intro y hRy
              have := ihs y (P.setDisc σ a j i y) q hRy fun T hT => by
                obtain ⟨hT', h1, h2⟩ := P.Cset_setDisc hσ hiE y hT
                have := P.within_test_succ (hW T hT') h1
                rwa [h2] at this
              rw [P.Phi_setDisc hσ] at this
              exact this
            have hexcl : 1 < P.dd E → P.val K L P.gPhi kf (P.setExcl σ a j E i) ≤
                P.Phi σ + 1 / 2 + ((q : ℝ) - 1) := by
              intro hd1
              have hRe := hR2 σ a j E i hR hstop hσ hiE hd1
              obtain ⟨T₀, hT₀⟩ := hR1 _ hRe
              obtain ⟨hT₀', hne₀⟩ := P.Cset_setExcl hσ i hT₀
              obtain ⟨q₀, hq₀, -⟩ := P.within_test_fail (hW T₀ hT₀') hne₀
              have hb : ∀ T ∈ P.Cset (P.setExcl σ a j E i), kf.Within T q₀ := by
                intro T hT
                obtain ⟨hT', hne⟩ := P.Cset_setExcl hσ i hT
                obtain ⟨q₁, hq₁, hW₁⟩ := P.within_test_fail (hW T hT') hne
                have : q₁ = q₀ := by omega
                rwa [this] at hW₁
              have := ihf _ q₀ hRe hb
              rw [P.Phi_setExcl hσ hiE] at this
              have : (q : ℝ) = q₀ + 1 := by exact_mod_cast hq₀
              linarith
            have hR3' := hR3 σ a j E i hR hstop hσ hiE
            calc mixF (K σ a) (P.dd E) (P.val K L P.gPhi (ks true) (P.setDisc σ a j i true))
                  (P.val K L P.gPhi (ks false) (P.setDisc σ a j i false))
                  (P.val K L P.gPhi kf (P.setExcl σ a j E i))
                ≤ mixF (K σ a) (P.dd E) (P.Phi σ + (P.dd E - 1) / 2 + q)
                  (P.Phi σ + (P.dd E - 1) / 2 + q) (P.Phi σ + 1 / 2 + ((q : ℝ) - 1)) :=
                  mixF_le hk0 hk1 hd (fun h => hsucc true (hR3'.1 h))
                    (fun h => hsucc false (hR3'.2 h)) hexcl
              _ = P.Phi σ + q := by
                  unfold mixF
                  field_simp
                  ring

/-- `pw-eq:discoveries`: under the same hypotheses, started from the initial state, the
expected number of discovered rows satisfies `E D ≤ 2q/(ℓ-1)`. -/
theorem discoveries_le {K : P.State → Bool → ℝ} (hK : P.KerOK K) (L : ℕ)
    (Reach : P.State → Prop)
    (hR1 : ∀ σ, Reach σ → (P.Cset σ).Nonempty)
    (hR2 : ∀ σ a j E i, Reach σ → ¬ L ≤ P.D σ → σ a j = .undisc E → i ∉ E → 1 < P.dd E →
      Reach (P.setExcl σ a j E i))
    (hR3 : ∀ σ a j E i, Reach σ → ¬ L ≤ P.D σ → σ a j = .undisc E → i ∉ E →
      (0 < K σ a → Reach (P.setDisc σ a j i true)) ∧
        (K σ a < 1 → Reach (P.setDisc σ a j i false)))
    (t : TT P β) (q : ℕ) (h0 : Reach P.σ0) (hW : ∀ T ∈ P.Cset P.σ0, t.Within T q) :
    P.val K L P.gD t P.σ0 ≤ 2 * q / ((P.ℓ : ℝ) - 1) := by
  have hℓ : (1 : ℝ) < P.ℓ := by exact_mod_cast (by have := P.hℓ; omega : 1 < P.ℓ)
  have hc : (0 : ℝ) < ((P.ℓ : ℝ) - 1) / 2 := by linarith
  have hpot := P.potential hK L Reach hR1 hR2 hR3 t P.σ0 q h0 hW
  have hΦ0 : P.Phi P.σ0 = 0 := by simp [Phi, D_σ0, exclSum_σ0]
  rw [hΦ0, zero_add] at hpot
  have hmono := P.val_mono hK L (g₁ := fun σ o => ((P.ℓ : ℝ) - 1) / 2 * P.gD σ o)
    (g₂ := P.gPhi) (M₁ := ((P.ℓ : ℝ) - 1) / 2 * (2 * P.W)) (M₂ := P.PhiMax)
    (fun σ o => by
      rw [abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (P.abs_gD_le σ o) hc.le)
    (fun σ _ => P.abs_Phi_le σ) (fun σ _ => P.D_le_Phi σ) (fun σ _ => P.D_le_Phi σ) t P.σ0
  rw [P.val_smul L] at hmono
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Prm

end LearningGuided.PointwiseLB
