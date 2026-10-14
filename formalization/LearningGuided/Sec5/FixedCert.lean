import LearningGuided.Sec5.ProdCertainty

/-!
# Corollary `cor:fixed-cert`: fixed-error sampling with an exponential certificate cost

The corollary is proved in an abstract form. Its two inputs about the outer classes come from
Theorem `thm:pointwise` and Appendix `app:pointwise` (the smoothed pointwise hard class on
`d = m` bits) and appear as explicit hypotheses:

* `hlow`: `Q_pw(𝒫_m, 1/16) ≥ c₀ m^{3/2} / √(log(2m))` for `m ≥ m₀`;
* `hupp`: `Q_pw(𝒫_m, 1/32) ≤ c₁ m^{3/2} log(2m)` for `m ≥ m₀`;

together with the stated structure of the outer classes: distributions with full support, at
least one and at most `e^m` members. Everything else is proved here.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec5

open Sec2 Sec4 Filter Topology

theorem prodDist_injective {d m : ℕ} {ν ν' : Str d → ℝ} (hν : IsDist ν) (hν' : IsDist ν')
    {θ θ' : Str (2 * m)} (h : prodDist ν (muθ m θ) = prodDist ν' (muθ m θ')) :
    ν = ν' ∧ θ = θ' := by
  have hmarg : ∀ (μ : Str d → ℝ) (σ : Str (3 * m + 2) → ℝ), ∑ v, σ v = 1 →
      ∀ x, ∑ v, prodDist μ σ (appS x v) = μ x := by
    intro μ σ hσ x
    simp only [prodDist_appS, ← Finset.mul_sum, hσ, mul_one]
  have hνν : ν = ν' := by
    funext x
    rw [← hmarg ν _ (isDist_muθ m θ).2 x, ← hmarg ν' _ (isDist_muθ m θ').2 x, h]
  subst hνν
  refine ⟨rfl, muθ_injective m ?_⟩
  obtain ⟨x, hx⟩ := exists_pos hν
  funext v
  have := congrFun h (appS x v)
  simp only [prodDist_appS] at this
  exact mul_left_cancel₀ (ne_of_gt hx) this

theorem prodClass_eq {d m : ℕ} (Pc : Finset (Str d → ℝ)) :
    prodClass (Pc : Set (Str d → ℝ)) m =
      ((Pc ×ˢ (Finset.univ : Finset (Str (2 * m)))).image
        fun p => prodDist p.1 (muθ m p.2) : Finset _) := by
  classical
  ext μ
  simp only [prodClass, Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_product, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨ν, hν, θ, rfl⟩; exact ⟨ν, θ, hν, rfl⟩
  · rintro ⟨ν, θ, hν, rfl⟩; exact ⟨ν, hν, θ, rfl⟩

theorem ncard_prodClass {d m : ℕ} {Pc : Finset (Str d → ℝ)} (hPc : ∀ ν ∈ Pc, IsDist ν) :
    (prodClass (Pc : Set (Str d → ℝ)) m).ncard = Pc.card * 4 ^ m := by
  classical
  rw [prodClass_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_product,
    Finset.card_univ, card_keys]
  rintro ⟨ν, θ⟩ hp ⟨ν', θ'⟩ hp' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
  obtain ⟨e1, e2⟩ := prodDist_injective (hPc ν hp.1) (hPc ν' hp'.1) h
  simp only at e2
  rw [e1, e2]

theorem alpha_le_32 {m : ℕ} (hm : 5 ≤ m) : alpha m ≤ 1 / 32 := by
  unfold alpha
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  calc (1 / 32 : ℝ)⁻¹ = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm

/-- `cor:fixed-cert`: `D_{9/4} = d_m → 0`. -/
theorem dm_tendsto : Tendsto dm atTop (𝓝 0) := by
  have hα : Tendsto alpha atTop (𝓝 0) := by
    unfold alpha
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have e : dm = fun m => alpha m - (5 / 4 + alpha m) * alpha m ^ 2 := funext dm_eq
  rw [e]
  have := hα.sub ((tendsto_const_nhds (x := (5 / 4 : ℝ)).add hα).mul (hα.pow 2))
  simpa using this

/-- `cor:fixed-cert` (abstract form). Let `𝒫_m` be classes of full-support distributions on
`d = m` bits with `1 ≤ |𝒫_m| ≤ e^m` such that, for `m ≥ m₀`,
`Q_pw(𝒫_m,1/16) ≥ c₀ m^{3/2}/√(log(2m))` and `Q_pw(𝒫_m,1/32) ≤ c₁ m^{3/2} log(2m)` (the inputs from
Theorem `thm:pointwise` and Appendix `app:pointwise`). Then for every `m ≥ max(m₀, 5)` the product
class `{ν ⊗ μ_θ}` lives on `4m + 2` bits, has full support, between `4^m` and `4^m e^m` members
(logarithmic cardinality between `m log 4` and `m (log 4 + 1)`), its product guides are safe with
`R = C = 9/4`, `c₀ m^{3/2}/√(log(2m)) ≤ Q_⊗(1/16) ≤ c₁ m^{3/2} log(2m)`, every instance has
`D_{9/4} = d_m` (and `d_m → 0`, see `dm_tendsto`), optimal-mass certification with certainty costs
between `4^m/2` and `2·4^m` queries, and every procedure succeeding with probability at least
`1 - ζ` with mass budget `B ≥ 0` needs `q ≥ (1-ζ)4^m - 2B 2^m` queries. -/
theorem cor_fixed_cert (Pf : ∀ m : ℕ, Finset (Str m → ℝ))
    (hdist : ∀ m, ∀ ν ∈ Pf m, IsDist ν) (hfull : ∀ m, ∀ ν ∈ Pf m, ∀ x, 0 < ν x)
    (hne : ∀ m, (Pf m).Nonempty) (hcard : ∀ m : ℕ, ((Pf m).card : ℝ) ≤ Real.exp m)
    (c₀ c₁ : ℝ) (m₀ : ℕ)
    (hlow : ∀ m ≥ m₀, c₀ * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m)) ≤
      (Qpw (Pf m : Set (Str m → ℝ)) (1 / 16) : ℝ))
    (hupp : ∀ m ≥ m₀, (Qpw (Pf m : Set (Str m → ℝ)) (1 / 32) : ℝ) ≤
      c₁ * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m)) :
    ∀ m ≥ max m₀ 5,
      m + (3 * m + 2) = 4 * m + 2 ∧
      (∀ μ ∈ prodClass (Pf m : Set (Str m → ℝ)) m, IsDist μ ∧ ∀ z, 0 < μ z) ∧
      ((4 : ℝ) ^ m ≤ (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ∧
        ((prodClass (Pf m : Set (Str m → ℝ)) m).ncard : ℝ) ≤ 4 ^ m * Real.exp m) ∧
      (m * Real.log 4 ≤ Real.log (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ∧
        Real.log (prodClass (Pf m : Set (Str m → ℝ)) m).ncard ≤ m * (Real.log 4 + 1)) ∧
      (∀ μ H, ProdLegal (Pf m : Set (Str m → ℝ)) m μ H → SafeLegal (9 / 4) (9 / 4) μ H) ∧
      (c₀ * (m : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * m)) ≤
          (Qprod (Pf m : Set (Str m → ℝ)) m (1 / 16) : ℝ) ∧
        (Qprod (Pf m : Set (Str m → ℝ)) m (1 / 16) : ℝ) ≤
          c₁ * (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log (2 * m)) ∧
      (∀ μ H, ProdLegal (Pf m : Set (Str m → ℝ)) m μ H → DefectEq (9 / 4) μ H (dm m)) ∧
      (4 ^ m - 1 ≤ QcertProd (Pf m) m ∧ QcertProd (Pf m) m ≤ 4 ^ m + (Pf m).card - 2) ∧
      ((4 : ℝ) ^ m / 2 ≤ QcertProd (Pf m) m ∧ (QcertProd (Pf m) m : ℝ) ≤ 2 * 4 ^ m) ∧
      (∀ ν ∈ Pf m, ∀ g, PwLegal (9 / 4) ν g → ∀ (B : ℝ), 0 ≤ B → ∀ (ζ : ℝ) (q : ℕ)
        (A : Alg (Str (m + (3 * m + 2)) → ℝ)),
        (∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q) →
        (∀ θ : Str (2 * m),
          1 - ζ ≤ (probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ B)).toReal) →
        (1 - ζ) * 4 ^ m - 2 * B * 2 ^ m ≤ q) := by
  intro m hm
  have hm0 : m₀ ≤ m := le_of_max_le_left hm
  have hm5 : 5 ≤ m := le_of_max_le_right hm
  have hm3 : 3 ≤ m := by omega
  have hP := hdist m
  have hα32 := alpha_le_32 hm5
  have hα0 := alpha_pos m
  have hcardP : 1 ≤ (Pf m).card := Finset.card_pos.mpr (hne m)
  have hncard := ncard_prodClass (m := m) (hdist m)
  have he4 : Real.exp m ≤ (4 : ℝ) ^ m := by
    rw [← Real.exp_one_rpow, ← Real.rpow_natCast (4 : ℝ) m]
    exact Real.rpow_le_rpow (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) (Nat.cast_nonneg m)
  refine ⟨by ring, ?_, ?_, ?_, ?_, ?_, ?_, composition_certainty hm3 hP (hne m), ?_, ?_⟩
  · rintro μ ⟨ν, hν, θ, rfl⟩
    refine ⟨isDist_prodDist (hP ν hν) (isDist_muθ m θ), fun z => ?_⟩
    exact mul_pos (hfull m ν hν _) (muθ_pos (by omega) θ _)
  · rw [hncard]
    push_cast
    have := hcard m
    have h1 : (1 : ℝ) ≤ (Pf m).card := by exact_mod_cast hcardP
    constructor <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]
  · rw [hncard]
    push_cast
    have h1 : (1 : ℝ) ≤ (Pf m).card := by exact_mod_cast hcardP
    have hpos : (0 : ℝ) < (Pf m).card := by linarith
    rw [Real.log_mul (ne_of_gt hpos) (by positivity), Real.log_pow]
    have hl0 : 0 ≤ Real.log (Pf m).card := Real.log_nonneg h1
    have hl1 : Real.log (Pf m).card ≤ m := by
      have := Real.log_le_log hpos (hcard m)
      rwa [Real.log_exp] at this
    constructor <;> linarith
  · rintro μ H ⟨ν, hν, g, hg, θ, rfl, rfl⟩
    obtain ⟨-, -, -, hs, -⟩ := composition_budgets (hP ν hν) (isDist_muθ m θ)
      (by norm_num : (0 : ℝ) < 9 / 4) hg (safeLegal_hθ hm3 θ)
    simpa using hs
  · constructor
    · refine (hlow m hm0).trans ?_
      exact_mod_cast composition_sampling_lower hP hm3 (by norm_num)
    · have h1 := composition_sampling_upper (Pc := (Pf m : Set (Str m → ℝ))) hP
        (m := m) (δ := 1 / 16) (by linarith)
      have h2 := Qpw_anti (F := (Pf m : Set (Str m → ℝ))) hP (δ := 1 / 32)
        (δ' := 1 / 16 - alpha m) (by norm_num) (by linarith)
      have h3 : (Qprod (Pf m : Set (Str m → ℝ)) m (1 / 16) : ℝ) ≤
          Qpw (Pf m : Set (Str m → ℝ)) (1 / 32) := by exact_mod_cast h1.trans h2
      exact h3.trans (hupp m hm0)
  · rintro μ H ⟨ν, hν, g, hg, θ, rfl, rfl⟩
    exact (prod_min_correction hm3 (hP ν hν) hg θ).2.2.2
  · obtain ⟨h1, h2⟩ := composition_certainty hm3 hP (hne m)
    have hM1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    constructor
    · have : ((4 ^ m - 1 : ℕ) : ℝ) ≤ QcertProd (Pf m) m := by exact_mod_cast h1
      rw [Nat.cast_sub hM1] at this
      push_cast at this
      have : (2 : ℝ) ≤ 4 ^ m := by
        calc (2 : ℝ) ≤ 4 ^ 1 := by norm_num
          _ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    · have : (QcertProd (Pf m) m : ℝ) ≤ ((4 ^ m + (Pf m).card - 2 : ℕ) : ℝ) := by
        exact_mod_cast h2
      have hsub : ((4 ^ m + (Pf m).card - 2 : ℕ) : ℝ) ≤ (4 : ℝ) ^ m + (Pf m).card := by
        have : 4 ^ m + (Pf m).card - 2 ≤ 4 ^ m + (Pf m).card := Nat.sub_le _ _
        exact_mod_cast this
      have := hcard m
      linarith
  · intro ν hν g hg B hB ζ q A hW hS
    have := composition_fixed_B hm3 (hP ν hν) hg B hB ζ q A hW hS
    rwa [show Real.sqrt ((4 : ℝ) ^ m) = 2 ^ m by
      rw [four_pow, Real.sqrt_sq (by positivity)]] at this

end Sec5
end LearningGuided
