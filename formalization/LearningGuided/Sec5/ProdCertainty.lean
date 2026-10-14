import LearningGuided.Sec5.Composition

/-!
# Optimal-mass certification with certainty on the product (Theorem `thm:composition`)

The complexity of producing an optimal-mass correction with certainty on every product instance
lies between `M - 1` and `M + |𝒫| - 2`: identify `ν` with at most `|𝒫| - 1` distinguishing queries
at depth `d`, then identify the inner key below a known positive-mass outer leaf with at most
`M - 1` queries, and return `ν ⊗ d_m δ_{x_θ}`. The fixed-budget bound `q ≥ (1-ζ)M - 2B√M` also
transfers to the product.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec5

open Sec2 Sec4

variable {d : ℕ}

/-! ### Identifying the outer target -/

open Classical in
/-- A member of a finite set of candidates (any member if there are several). -/
noncomputable def pickD (C : Finset (Str d → ℝ)) : Str d → ℝ :=
  if h : C.Nonempty then h.choose else fun _ => 0

theorem pickD_eq {C : Finset (Str d → ℝ)} {ν : Str d → ℝ} (hν : ν ∈ C) (hC : C.card ≤ 1) :
    pickD C = ν := by
  have hne : C.Nonempty := ⟨ν, hν⟩
  unfold pickD
  rw [dite_eq_left hne]
  exact Finset.card_le_one.mp hC _ hne.choose_spec _ hν

theorem exists_sep {C : Finset (Str d → ℝ)} (h : 1 < C.card) :
    ∃ x : Str d, ∃ ν₁ ∈ C, ∃ ν₂ ∈ C, ν₁ x ≠ ν₂ x := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
  exact ⟨x, a, ha, b, hb, hx⟩

open Classical in
/-- An outer leaf at which two remaining candidates differ. -/
noncomputable def sepPoint (C : Finset (Str d → ℝ)) : Str d :=
  if h : 1 < C.card then (exists_sep h).choose else fun _ => false

open Classical in
/-- Identify the outer target among the candidates `C` by exact outer-leaf queries, then continue
with `cont`. Each query eliminates at least one candidate. -/
noncomputable def identify {β : Type} (cont : (Str d → ℝ) → Alg β) :
    ℕ → Finset (Str d → ℝ) → Alg β
  | 0, C => cont (pickD C)
  | f + 1, C =>
      if 1 < C.card then
        Alg.query (List.ofFn (sepPoint C))
          (fun r => identify cont f (C.filter fun ν => ν (sepPoint C) = r))
      else cont (pickD C)

theorem within_identify {β : Type} (cont : (Str d → ℝ) → Alg β) (H : Guide) (c : ℕ)
    (hc : ∀ ν, (cont ν).Within H c) : ∀ f C, (identify cont f C).Within H (f + c) := by
  intro f
  induction f with
  | zero => intro C; simpa [identify] using hc _
  | succ f ih =>
      intro C
      simp only [identify]
      split_ifs
      · rw [show f + 1 + c = (f + c) + 1 by omega]
        exact Alg.Within.query _ _ _ (ih _)
      · exact (hc _).mono (by omega)

theorem run_identify {β : Type} (cont : (Str d → ℝ) → Alg β) {H : Guide} {ν : Str d → ℝ}
    (hH : ∀ x : Str d, H (List.ofFn x) = ν x) :
    ∀ f C, ν ∈ C → C.card ≤ f + 1 → (identify cont f C).run H = (cont ν).run H := by
  classical
  intro f
  induction f with
  | zero =>
      intro C hν hC
      simp only [identify]
      rw [pickD_eq hν (by omega)]
  | succ f ih =>
      intro C hν hC
      simp only [identify]
      split_ifs with h1
      · rw [Alg.run_query, hH]
        refine ih (C.filter fun ν' => ν' (sepPoint C) = ν (sepPoint C))
          (Finset.mem_filter.mpr ⟨hν, rfl⟩) ?_
        obtain ⟨ν₁, h₁, ν₂, h₂, hne⟩ := (exists_sep h1).choose_spec
        have hsep : sepPoint C = (exists_sep h1).choose := by
          unfold sepPoint; rw [dite_eq_left h1]
        rw [← hsep] at hne
        have hlt : (C.filter fun ν' => ν' (sepPoint C) = ν (sepPoint C)).card < C.card := by
          apply Finset.card_lt_card
          refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
          by_cases e : ν₁ (sepPoint C) = ν (sepPoint C)
          · have := (Finset.mem_filter.mp (hsub h₂)).2
            exact hne (e.trans this.symm)
          · exact e (Finset.mem_filter.mp (hsub h₁)).2
        omega
      · rw [pickD_eq hν (by omega)]

/-! ### Identifying the inner key -/

theorem exists_pos {ν : Str d → ℝ} (hν : IsDist ν) : ∃ x, 0 < ν x := by
  by_contra h
  push Not at h
  have : ∑ x, ν x ≤ 0 := Finset.sum_nonpos fun x _ => h x
  rw [hν.2] at this
  linarith

open Classical in
/-- A positive-mass outer leaf. -/
noncomputable def posLeaf (ν : Str d → ℝ) : Str d :=
  if h : ∃ x, 0 < ν x then h.choose else fun _ => false

theorem posLeaf_pos {ν : Str d → ℝ} (hν : IsDist ν) : 0 < ν (posLeaf ν) := by
  have h := exists_pos hν
  unfold posLeaf
  rw [dite_eq_left h]
  exact h.choose_spec

/-- The optimal product correction `ν ⊗ d_m δ_{x_θ}`. -/
noncomputable def corrProd (m : ℕ) (ν : Str d → ℝ) (θ : Str (2 * m)) :
    Str (d + (3 * m + 2)) → ℝ :=
  prodDist ν (optCorr m θ)

/-- The reference key. -/
def key0 (m : ℕ) : Str (2 * m) := fun _ => false

/-- Below the known positive-mass outer leaf, test the complete strings of all keys but one; on a
hit, or by elimination, return the optimal correction for the identified key. -/
noncomputable def keyScanProd (m : ℕ) (ν : Str d → ℝ) : Alg (Str (d + (3 * m + 2)) → ℝ) :=
  scan (fun κ : Str (2 * m) => List.ofFn (posLeaf ν) ++ List.ofFn (xθ m κ))
    (fun _ r => ν (posLeaf ν) * ((1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹) < r)
    (fun κ => Alg.ret (corrProd m ν κ)) (Alg.ret (corrProd m ν (key0 m)))
    (Finset.univ.erase (key0 m)).toList

theorem within_keyScanProd (m : ℕ) (ν : Str d → ℝ) (H : Guide) :
    (keyScanProd m ν).Within H (4 ^ m - 1) := by
  have := within_scan (fun κ : Str (2 * m) => List.ofFn (posLeaf ν) ++ List.ofFn (xθ m κ))
    (fun _ r => ν (posLeaf ν) * ((1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹) < r)
    (fun κ => Alg.ret (corrProd m ν κ)) (Alg.ret (corrProd m ν (key0 m))) H 0
    (fun _ => Alg.Within.ret _ 0) (Alg.Within.ret _ 0) (Finset.univ.erase (key0 m)).toList
  rwa [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_keys, add_zero] at this

theorem run_keyScanProd {m : ℕ} (hm : 3 ≤ m) {ν : Str d → ℝ} (hν : IsDist ν) {g : Guide}
    (hg : PwLegal (9 / 4) ν g) (θ : Str (2 * m)) :
    (keyScanProd m ν).run (prodGuide ν g (hθ m θ)) = PMF.pure (corrProd m ν θ) := by
  classical
  have hor := isOracle_hθ hm θ
  have hpos := posLeaf_pos hν
  have htest : ∀ κ : Str (2 * m),
      (ν (posLeaf ν) * ((1 - alpha m) * ((2 : ℝ) ^ (3 * m + 2))⁻¹) <
        prodGuide ν g (hθ m θ) (List.ofFn (posLeaf ν) ++ List.ofFn (xθ m κ))) ↔ κ = θ := by
    intro κ
    rw [prodGuide_append hg.1.leaf hor.root, mul_lt_mul_iff_right₀ hpos]
    exact leaf_test hor.leaf κ
  unfold keyScanProd
  rw [run_scan _ _ _ _ _ θ htest]
  by_cases hθ : θ ∈ (Finset.univ.erase (key0 m)).toList
  · rw [ite_eq_left hθ]; rfl
  · rw [ite_eq_right hθ]
    have : θ = key0 m := by
      by_contra hne
      exact hθ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩))
    rw [this]; rfl

/-- The certification procedure with certainty: identify `ν`, then the inner key. -/
noncomputable def certProdAlg (Pc : Finset (Str d → ℝ)) (m : ℕ) :
    Alg (Str (d + (3 * m + 2)) → ℝ) :=
  identify (keyScanProd m) (Pc.card - 1) Pc

/-- The certification complexity with certainty at optimal mass over all product instances. -/
noncomputable def QcertProd (Pc : Finset (Str d → ℝ)) (m : ℕ) : ℕ :=
  sInf {q | ∃ A : Alg (Str (d + (3 * m + 2)) → ℝ), ∀ ν ∈ Pc, ∀ g, PwLegal (9 / 4) ν g →
    ∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q ∧
      probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ (dm m)) = 1}

/-- `thm:composition` (certainty): optimal-mass certification with certainty on the product class
has query complexity between `M - 1` and `M + |𝒫| - 2`. -/
theorem composition_certainty {m : ℕ} (hm : 3 ≤ m) {Pc : Finset (Str d → ℝ)}
    (hPc : ∀ ν ∈ Pc, IsDist ν) (hne : Pc.Nonempty) :
    4 ^ m - 1 ≤ QcertProd Pc m ∧ QcertProd Pc m ≤ 4 ^ m + Pc.card - 2 := by
  classical
  have hcard : 1 ≤ Pc.card := Finset.card_pos.mpr hne
  have hM1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hmem : 4 ^ m + Pc.card - 2 ∈ {q | ∃ A : Alg (Str (d + (3 * m + 2)) → ℝ), ∀ ν ∈ Pc,
      ∀ g, PwLegal (9 / 4) ν g → ∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q ∧
        probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ (dm m)) = 1} := by
    refine ⟨certProdAlg Pc m, fun ν hν g hg θ => ⟨?_, ?_⟩⟩
    · have := within_identify (keyScanProd m) (prodGuide ν g (hθ m θ)) (4 ^ m - 1)
        (fun ν' => within_keyScanProd m ν' _) (Pc.card - 1) Pc
      exact this.mono (by omega)
    · have hH : ∀ x : Str d, prodGuide ν g (hθ m θ) (List.ofFn x) = ν x := fun x => by
        rw [prodGuide_short ν g _ (by simp)]; exact hg.1.leaf x
      unfold certProdAlg
      rw [run_identify (keyScanProd m) hH _ _ hν (by omega), run_keyScanProd hm (hPc ν hν) hg,
        probE_pure, ite_eq_left]
      obtain ⟨h1, h2, -⟩ := prod_min_correction hm (hPc ν hν) hg θ
      exact ⟨h1, h2.le⟩
  refine ⟨le_csInf ⟨_, hmem⟩ ?_, Nat.sInf_le hmem⟩
  rintro q ⟨A, hA⟩
  obtain ⟨ν, hν⟩ := hne
  have hg := pwLegal_exact (hPc ν hν) (R := 9 / 4) (by norm_num)
  obtain ⟨θ, hθ⟩ := composition_cert hm (hPc ν hν) hg (dm m) q A (fun θ => (hA ν hν _ hg θ).1)
  rw [(hA ν hν _ hg θ).2, ENNReal.toReal_one] at hθ
  have hK : ⌊dm m / dm m⌋₊ = 1 := by rw [div_self (ne_of_gt (dm_pos hm))]; simp
  rw [hK] at hθ
  have h1 : 1 ≤ ((q : ℝ) + ((1 : ℕ) : ℝ)) / 4 ^ m := hθ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity), one_mul] at h1
  have : (4 ^ m : ℕ) ≤ q + 1 := by exact_mod_cast h1
  omega

/-- `cor:fixed-cert` (fixed budget, from `eq:composition-cert`): for `B ≥ 0`, a procedure with cap
`q` whose success probability is at least `1 - ζ` for every key (with `ν` and `g` fixed publicly)
satisfies `q ≥ (1-ζ)M - 2B√M`. -/
theorem composition_fixed_B {m : ℕ} (hm : 3 ≤ m) {ν : Str d → ℝ} (hν : IsDist ν) {g : Guide}
    (hg : PwLegal (9 / 4) ν g) (B : ℝ) (hB : 0 ≤ B) (ζ : ℝ) (q : ℕ)
    (A : Alg (Str (d + (3 * m + 2)) → ℝ))
    (hW : ∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q)
    (hS : ∀ θ : Str (2 * m),
      1 - ζ ≤ (probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ B)).toReal) :
    (1 - ζ) * 4 ^ m - 2 * B * Real.sqrt (4 ^ m) ≤ q := by
  have hMpos : (0 : ℝ) < 4 ^ m := by positivity
  have hsqrt : Real.sqrt ((4 : ℝ) ^ m) = 2 ^ m := by
    rw [four_pow, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  obtain ⟨θ, hθ⟩ := composition_cert hm hν hg B q A hW
  have h1 : 1 - ζ ≤ ((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m := (hS θ).trans (hθ.trans (min_le_right _ _))
  rw [le_div_iff₀ hMpos] at h1
  have hdm := dm_pos hm
  have hfl : (⌊B / dm m⌋₊ : ℝ) ≤ B / dm m := Nat.floor_le (div_nonneg hB hdm.le)
  have hhalf := dm_ge_half_alpha hm
  have h2 : B / dm m ≤ 2 * B * 2 ^ m := by
    rw [div_le_iff₀ hdm]
    have e : alpha m * 2 ^ m = 1 := alpha_mul m
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have : 0 ≤ 2 * B * 2 ^ m * (dm m - alpha m / 2) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 2 * B * 2 ^ m * dm m - B = 2 * B * 2 ^ m * (dm m - alpha m / 2) +
        B * (alpha m * 2 ^ m - 1) := by ring
    rw [e, sub_self, mul_zero, add_zero] at e2
    linarith
  linarith

end Sec5
end LearningGuided
