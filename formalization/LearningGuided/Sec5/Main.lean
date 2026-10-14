import LearningGuided.Sec5.FixedCert

/-!
# Theorem `thm:composition`: sequential composition

The statement collected from `Composition.lean` and `ProdCertainty.lean`.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec5

open Sec2 Sec4

variable {d : ℕ}

/-- `thm:composition`. For a finite class `𝒫` of distributions on `{0,1}^d` (nonempty) and
`m ≥ 3`, with the inner pair `(μ_θ, h_θ)` of Section `sec:construction` and `R = 9/4`:
* every product guide is legal in the safe model with `R = C = 9/4`, and `D_{9/4}(μ,H) = d_m`;
* `eq:composition-sampling`: for `α < δ < 1`, `Q_pw(𝒫,δ) ≤ Q_⊗(𝒫,m,δ) ≤ Q_pw(𝒫,δ-α)`;
* every product instance has minimum coherent correction mass `d_m`;
* `eq:composition-cert`: for every product instance and every procedure with cap `q`, some key
  has success probability at most `min {1, (q + ⌊B/d_m⌋)/M}`;
* optimal-mass certification with certainty costs between `M - 1` and `M + |𝒫| - 2` queries.
The general budgets `eq:composition-budgets` for arbitrary `R`, `C` are
`Sec5.composition_budgets`. -/
theorem thm_composition {m : ℕ} (hm : 3 ≤ m) (Pc : Finset (Str d → ℝ))
    (hPc : ∀ ν ∈ Pc, IsDist ν) (hne : Pc.Nonempty) :
    (∀ μ H, ProdLegal (Pc : Set (Str d → ℝ)) m μ H →
      SafeLegal (9 / 4) (9 / 4) μ H ∧ DefectEq (9 / 4) μ H (dm m)) ∧
    (∀ δ : ℝ, alpha m < δ → δ < 1 →
      Qpw (Pc : Set (Str d → ℝ)) δ ≤ Qprod (Pc : Set (Str d → ℝ)) m δ ∧
        Qprod (Pc : Set (Str d → ℝ)) m δ ≤ Qpw (Pc : Set (Str d → ℝ)) (δ - alpha m)) ∧
    (∀ ν ∈ Pc, ∀ g, PwLegal (9 / 4) ν g → ∀ θ : Str (2 * m),
      (∃ κ, IsCorrection (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ)) κ ∧
        ∑ z, κ z = dm m) ∧
      ∀ κ, IsCorrection (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ)) κ →
        dm m ≤ ∑ z, κ z) ∧
    (∀ ν ∈ Pc, ∀ g, PwLegal (9 / 4) ν g → ∀ (B : ℝ) (q : ℕ)
      (A : Alg (Str (d + (3 * m + 2)) → ℝ)),
      (∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q) →
      ∃ θ : Str (2 * m),
        (probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ B)).toReal ≤
          min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m)) ∧
    (4 ^ m - 1 ≤ QcertProd Pc m ∧ QcertProd Pc m ≤ 4 ^ m + Pc.card - 2) := by
  refine ⟨?_, fun δ h1 h2 => composition_sampling hPc hm h1 h2, ?_,
    fun ν hν g hg B q A hA => composition_cert hm (hPc ν hν) hg B q A hA,
    composition_certainty hm hPc hne⟩
  · rintro μ H ⟨ν, hν, g, hg, θ, rfl, rfl⟩
    obtain ⟨-, -, -, hs, -⟩ := composition_budgets (hPc ν hν) (isDist_muθ m θ)
      (by norm_num : (0 : ℝ) < 9 / 4) hg (safeLegal_hθ hm θ)
    exact ⟨by simpa using hs, (prod_min_correction hm (hPc ν hν) hg θ).2.2.2⟩
  · intro ν hν g hg θ
    obtain ⟨h1, h2, h3, -⟩ := prod_min_correction hm (hPc ν hν) hg θ
    exact ⟨⟨_, h1, h2⟩, h3⟩

end Sec5
end LearningGuided
