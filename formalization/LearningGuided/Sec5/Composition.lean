import LearningGuided.Sec5.Concatenation

/-!
# Sequential composition (Theorem `thm:composition`)

General part (`eq:composition-budgets`): for an outer distribution `ν` with a pointwise factor-`R`
guide `g` and an inner distribution `σ` with a safe guide `h` (`h ≤ Rσ`, exact leaves, capacity at
most `C`), the product guide satisfies `H ≤ Rμ`, `CC(μ,H) ≤ max{R,C}` and `D_R(μ,H) = D_R(σ,h)`.

Specialized part: `R = 9/4`, `(σ,h) = (μ_θ,h_θ)` from Section `sec:construction`. The minimax
complexity over precisely the product guides is `Qprod 𝒫 m δ`, and
`Q_pw(𝒫,δ) ≤ Qprod 𝒫 m δ ≤ Q_pw(𝒫,δ-α)` (equation `eq:composition-sampling`); every product
instance has minimum coherent correction mass `d_m`; certification success is at most
`min{1,(q+⌊B/d_m⌋)/M}` (equation `eq:composition-cert`); optimal-mass certification with
certainty needs between `M-1` and `M+|𝒫|-2` queries.
-/

open scoped BigOperators ENNReal

namespace LearningGuided
namespace Sec5

open Sec2 Sec4

variable {d n : ℕ}

/-! ### Defects of the product -/

theorem defect_prod_short {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hσ : IsDist σ)
    {R : ℝ} (hR : 0 < R) (hg : PwLegal R ν g) {u : List Bool} (hu : u.length ≤ d) :
    defect R (prodDist ν σ) (prodGuide ν g h) u = 0 := by
  rw [defect, mass_prod_short hσ.2 hu, prodGuide_short ν g h hu]
  have h1 := (hg.2 u hu).1
  have h2 := (hg.2 u hu).2
  rw [div_le_iff₀ hR] at h1
  apply le_antisymm _ (le_max_left _ _)
  exact max_le le_rfl (max_le (by linarith) (by linarith))

theorem defect_prod_append {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide}
    (hg : ∀ x : Str d, g (List.ofFn x) = ν x) (hroot : h [] = 1) (hν0 : ∀ x, 0 ≤ ν x)
    (R : ℝ) (x : Str d) (w : List Bool) :
    defect R (prodDist ν σ) (prodGuide ν g h) (List.ofFn x ++ w) = ν x * defect R σ h w := by
  rw [defect, defect, mass_prod_append, prodGuide_append hg hroot, mul_max_of_nonneg _ _ (hν0 x),
    mul_max_of_nonneg _ _ (hν0 x), mul_zero]
  congr 2 <;> ring

/-- The cut `{x w : x ∈ {0,1}^d, w ∈ B}`. -/
theorem sum_fillCut_empty (B : Finset (List Bool)) (F : List Bool → ℝ) :
    ∑ u ∈ fillCut (d := d) ∅ B, F u = ∑ x : Str d, ∑ w ∈ B, F (List.ofFn x ++ w) := by
  classical
  have hinj : Set.InjOn (fun p : Str d × List Bool => List.ofFn p.1 ++ p.2)
      (((Finset.univ.filter fun x : Str d => ¬ ∃ u ∈ (∅ : Finset (List Bool)), IsPre u x) ×ˢ B :
        Finset (Str d × List Bool)) : Set (Str d × List Bool)) := by
    rintro ⟨x, w⟩ _ ⟨x', w'⟩ _ h
    simp only at h
    have hx : List.ofFn x = List.ofFn x' := by
      have := congrArg (List.take d) h
      rwa [List.take_left' (by simp), List.take_left' (by simp)] at this
    have hx' := List.ofFn_injective hx
    rw [hx] at h
    rw [hx', List.append_cancel_left h]
  unfold fillCut
  rw [Finset.empty_union, Finset.sum_image hinj, Finset.sum_product]
  simp

/-- `thm:composition`, equation `eq:composition-budgets` (defect transfer): if `D_R(σ,h) = D`, then
`D_R(ν ⊗ σ, H) = D`. -/
theorem defectEq_prod {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) {R : ℝ} (hR : 0 < R) (hg : PwLegal R ν g) (hh : IsOracle σ h) {D : ℝ}
    (hD : DefectEq R σ h D) : DefectEq R (prodDist ν σ) (prodGuide ν g h) D := by
  classical
  have hdef0 : ∀ u, 0 ≤ defect R σ h u := fun u => le_max_left _ _
  have hD0 : 0 ≤ D := by
    obtain ⟨B, -, hB⟩ := hD.2
    rw [← hB]; exact Finset.sum_nonneg fun u _ => hdef0 u
  refine ⟨fun A hA => ?_, ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not A (fun u => u.length < d)]
    have hout : ∑ u ∈ A.filter (fun u => u.length < d),
        defect R (prodDist ν σ) (prodGuide ν g h) u = 0 :=
      Finset.sum_eq_zero fun u hu =>
        defect_prod_short hσ hR hg (Finset.mem_filter.mp hu).2.le
    rw [hout, zero_add, ← Finset.sum_fiberwise _ (headS d)]
    calc ∑ x, ∑ u ∈ A.filter (fun u => ¬ u.length < d) with headS d u = x,
          defect R (prodDist ν σ) (prodGuide ν g h) u
        ≤ ∑ x : Str d, ν x * D := by
          refine Finset.sum_le_sum fun x _ => ?_
          set Fx := (A.filter fun u => ¬ u.length < d).filter fun u => headS d u = x
          have hFmem : ∀ u ∈ Fx, u ∈ A ∧ u = List.ofFn x ++ u.drop d := by
            intro u hu
            have h1 := Finset.mem_filter.mp hu
            have h2 := Finset.mem_filter.mp h1.1
            have hl : d ≤ u.length := by omega
            refine ⟨h2.1, ?_⟩
            conv_lhs => rw [eq_append_headS hl]
            rw [h1.2]
          have hinj : Set.InjOn (List.drop d) (Fx : Set (List Bool)) := by
            intro u hu v hv huv
            rw [(hFmem u hu).2, (hFmem v hv).2]
            exact congrArg _ huv
          have hBcut : IsCut n (Fx.image (List.drop d)) := by
            refine ⟨fun w hw => ?_, fun w hw w' hw' hww => ?_⟩
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
              have := hA.1 u (hFmem u hu).1
              simp; omega
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
              obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hw'
              have hpre : u <+: u' := by
                rw [(hFmem u hu).2, (hFmem u' hu').2]
                exact (List.prefix_append_right_inj _).mpr hww
              rw [hA.2 u (hFmem u hu).1 u' (hFmem u' hu').1 hpre]
          have hterm : ∀ u ∈ Fx, defect R (prodDist ν σ) (prodGuide ν g h) u =
              ν x * defect R σ h (u.drop d) := by
            intro u hu
            rw [(hFmem u hu).2, defect_prod_append hg.1.leaf hh.root
              (fun y => by rw [← hg.1.leaf]; exact hg.1.nonneg _), List.drop_left' (by simp)]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_image hinj]
          exact mul_le_mul_of_nonneg_left (hD.1 _ hBcut) (hν.1 x)
      _ = D := by rw [← Finset.sum_mul, hν.2, one_mul]
  · obtain ⟨B, hB, hBval⟩ := hD.2
    refine ⟨fillCut ∅ B, fillCut_isCut empty_mem_outerCuts hB, ?_⟩
    rw [sum_fillCut_empty]
    have : ∀ x : Str d, ∑ w ∈ B, defect R (prodDist ν σ) (prodGuide ν g h) (List.ofFn x ++ w) =
        ν x * D := by
      intro x
      rw [← hBval, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => defect_prod_append hg.1.leaf hh.root
        (fun y => by rw [← hg.1.leaf]; exact hg.1.nonneg _) R x w
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_mul, hν.2, one_mul]

/-- `thm:composition`: an inner correction `λ` gives the product correction `ν ⊗ λ`, of the same
mass. -/
theorem isCorrection_prod {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) {R : ℝ} (hR : 0 < R) (hg : PwLegal R ν g) (hh : IsOracle σ h)
    {lam : Str n → ℝ} (hlam : IsCorrection R σ h lam) :
    IsCorrection R (prodDist ν σ) (prodGuide ν g h) (prodDist ν lam) ∧
      ∑ z, prodDist ν lam z = ∑ v, lam v := by
  refine ⟨⟨fun z => mul_nonneg (hν.1 _) (hlam.1 _), fun u hu => ?_⟩, by
    rw [sum_prodDist, hν.2, one_mul]⟩
  by_cases hud : u.length ≤ d
  · rw [defect_prod_short hσ hR hg hud]
    exact mass_nonneg (fun z => mul_nonneg (hν.1 _) (hlam.1 _)) u
  · have hl : d ≤ u.length := by omega
    rw [eq_append_headS hl, defect_prod_append hg.1.leaf hh.root hν.1, mass_prod_append]
    exact mul_le_mul_of_nonneg_left (hlam.2 _ (by simp; omega)) (hν.1 _)

/-- `thm:composition`, equation `eq:composition-budgets`: for a pointwise factor-`R` outer guide
and a safe inner guide with `h ≤ Rσ`, exact leaves and capacity at most `C`, the product guide
satisfies the access conditions, `H ≤ Rμ`, `CC(μ,H) ≤ max{R,C}` (so it is legal in the safe model
with constants `R` and `max{R,C}`), and `D_R(μ,H) = D_R(σ,h)`. -/
theorem composition_budgets {ν : Str d → ℝ} {σ : Str n → ℝ} {g h : Guide} (hν : IsDist ν)
    (hσ : IsDist σ) {R C : ℝ} (hR : 0 < R) (hg : PwLegal R ν g) (hh : SafeLegal R C σ h) :
    IsOracle (prodDist ν σ) (prodGuide ν g h) ∧
      (∀ u : List Bool, u.length ≤ d + n →
        prodGuide ν g h u ≤ R * mass (prodDist ν σ) u) ∧
      CapLE (prodDist ν σ) (prodGuide ν g h) (max R C) ∧
      SafeLegal R (max R C) (prodDist ν σ) (prodGuide ν g h) ∧
      ∀ D, DefectEq R σ h D → DefectEq R (prodDist ν σ) (prodGuide ν g h) D := by
  have hor := prod_isOracle hg.1 hh.1
  have hsafe : ∀ u : List Bool, u.length ≤ d + n →
      prodGuide ν g h u ≤ R * mass (prodDist ν σ) u := by
    intro u hu
    by_cases hud : u.length ≤ d
    · rw [prodGuide_short ν g h hud, mass_prod_short hσ.2 hud]
      exact (hg.2 u hud).2
    · have hl : d ≤ u.length := by omega
      rw [eq_append_headS hl, prodGuide_append hg.1.leaf hh.1.root, mass_prod_append]
      have h1 := hh.2.1 (u.drop d) (by simp; omega)
      have h0 : 0 ≤ ν (headS d u) := by rw [← hg.1.leaf]; exact hg.1.nonneg _
      nlinarith
  have hcap := capLE_prod hν hσ hg.1 hh.1 hR (fun u hu => (hg.2 u hu).1) hh.2.2
  exact ⟨hor, hsafe, hcap, ⟨hor, hsafe, hcap⟩,
    fun D hD => defectEq_prod hν hσ hR hg hh.1 hD⟩

/-! ### The specialized product class -/

/-- The product class `{ν ⊗ μ_θ : ν ∈ Pc, θ ∈ {0,1}^{2m}}` on `d + (3m+2)` bits. -/
def prodClass (Pc : Set (Str d → ℝ)) (m : ℕ) : Set (Str (d + (3 * m + 2)) → ℝ) :=
  {μ | ∃ ν ∈ Pc, ∃ θ, μ = prodDist ν (muθ m θ)}

/-- Precisely the product guides `eq:composition-guide`: `H` is the product of an arbitrary
pointwise factor-`9/4` guide `g` of `ν` with the hard guide `h_θ`. -/
def ProdLegal (Pc : Set (Str d → ℝ)) (m : ℕ) (μ : Str (d + (3 * m + 2)) → ℝ) (H : Guide) :
    Prop :=
  ∃ ν ∈ Pc, ∃ g, PwLegal (9 / 4) ν g ∧ ∃ θ, μ = prodDist ν (muθ m θ) ∧
    H = prodGuide ν g (hθ m θ)

/-- `Q_⊗(Pc,m,δ)`: minimax capped query complexity over precisely the product guides. -/
noncomputable def Qprod (Pc : Set (Str d → ℝ)) (m : ℕ) (δ : ℝ) : ℕ :=
  Qcx (ProdLegal Pc m) (prodClass Pc m) δ

theorem prodLegal_oracle {Pc : Set (Str d → ℝ)} {m : ℕ} (hm : 3 ≤ m) {μ : Str (d + (3 * m + 2)) → ℝ}
    {H : Guide} (hl : ProdLegal Pc m μ H) : IsOracle μ H := by
  obtain ⟨ν, -, g, hg, θ, rfl, rfl⟩ := hl
  exact prod_isOracle hg.1 (isOracle_hθ hm θ)

theorem prodClass_dist {Pc : Set (Str d → ℝ)} (hPc : ∀ ν ∈ Pc, IsDist ν) (m : ℕ) :
    ∀ μ ∈ prodClass Pc m, IsDist μ := by
  rintro μ ⟨ν, hν, θ, rfl⟩
  exact isDist_prodDist (hPc ν hν) (isDist_muθ m θ)

theorem tv_unif_muθ (m : ℕ) (θ : Str (2 * m)) : tv (unif (3 * m + 2)) (muθ m θ) ≤ alpha m := by
  have e : unif (3 * m + 2) = mixD (unif (3 * m + 2)) 0 (xθ m θ) := by
    funext x; simp [mixD]
  rw [e, muθ]
  refine (tv_mixD_le (isDist_unif _) _ _ _).trans ?_
  rw [zero_sub, abs_neg, abs_of_pos (alpha_pos m)]

/-- `thm:composition`, equation `eq:composition-sampling` (upper bound): sampling the outer
target to error `δ - α` with outer queries and appending a free draw from `U_n` gives
`Q_⊗(Pc,m,δ) ≤ Q_pw(Pc,δ-α)` for `α ≤ δ`. -/
theorem composition_sampling_upper {Pc : Set (Str d → ℝ)} (hPc : ∀ ν ∈ Pc, IsDist ν) {m : ℕ}
    {δ : ℝ} (hδ : alpha m ≤ δ) : Qprod Pc m δ ≤ Qpw Pc (δ - alpha m) := by
  refine Qcx_le_of_transfer (exists_solver hPc (fun _ _ hl => hl.1) (by linarith))
    fun q A hA => ⟨outerLift (3 * m + 2) A, ?_⟩
  rintro μ hμ H ⟨ν, hνPc, g, hg, θ, rfl, rfl⟩
  have hshort : ∀ u : List Bool, u.length ≤ d → prodGuide ν g (hθ m θ) u = g u :=
    fun u hu => prodGuide_short ν g _ hu
  have hlong : ∀ u : List Bool, d < u.length → g u = 0 := fun u hu => hg.1.long u hu
  obtain ⟨hW, hacc⟩ := hA ν hνPc g hg
  refine ⟨within_outerLift hshort hlong A q hW, ?_⟩
  rw [run_outerLift hshort hlong, lawR_outerLift_bind]
  have h1 := tv_prodDist_le (p := lawR (A.run g)) (hPc ν hνPc) (isDist_unif (3 * m + 2))
    (σ' := muθ m θ)
  have h2 := tv_unif_muθ m θ
  linarith

/-- `thm:composition`, equation `eq:composition-sampling` (lower bound): with the key fixed
publicly, each product query is simulated by at most one outer query, and projecting the output
gives `Q_pw(Pc,δ) ≤ Q_⊗(Pc,m,δ)` for `δ ≥ 0`. -/
theorem composition_sampling_lower {Pc : Set (Str d → ℝ)} (hPc : ∀ ν ∈ Pc, IsDist ν) {m : ℕ}
    (hm : 3 ≤ m) {δ : ℝ} (hδ : 0 ≤ δ) : Qpw Pc δ ≤ Qprod Pc m δ := by
  set θ₀ : Str (2 * m) := fun _ => false
  refine Qcx_le_of_transfer (exists_solver (prodClass_dist hPc m)
    (fun _ _ hl => prodLegal_oracle hm hl) hδ)
    fun q A hA => ⟨innerSim (hθ m θ₀) A, ?_⟩
  intro ν hν g hg
  have hl : ProdLegal Pc m (prodDist ν (muθ m θ₀)) (prodGuide ν g (hθ m θ₀)) :=
    ⟨ν, hν, g, hg, θ₀, rfl, rfl⟩
  obtain ⟨hW, hacc⟩ := hA _ ⟨ν, hν, θ₀, rfl⟩ _ hl
  refine ⟨within_innerSim hg.1.leaf _ A q hW, ?_⟩
  rw [run_innerSim hg.1.leaf]
  exact (tv_proj_le (isDist_muθ m θ₀).2).trans hacc

/-- `thm:composition`, equation `eq:composition-sampling`: for `α < δ < 1`,
`Q_pw(Pc,δ) ≤ Q_⊗(Pc,m,δ) ≤ Q_pw(Pc,δ-α)`. -/
theorem composition_sampling {Pc : Set (Str d → ℝ)} (hPc : ∀ ν ∈ Pc, IsDist ν) {m : ℕ}
    (hm : 3 ≤ m) {δ : ℝ} (hδ : alpha m < δ) (_hδ1 : δ < 1) :
    Qpw Pc δ ≤ Qprod Pc m δ ∧ Qprod Pc m δ ≤ Qpw Pc (δ - alpha m) :=
  ⟨composition_sampling_lower hPc hm (by linarith [alpha_pos m]),
    composition_sampling_upper hPc hδ.le⟩

/-! ### Corrections of product instances -/

/-- The demand at the depth-`k` prefix naming the key is `d_m`. -/
theorem defect_key {m : ℕ} (hm : 3 ≤ m) (θ : Str (2 * m)) :
    defect (9 / 4) (muθ m θ) (hθ m θ) (List.ofFn θ) = dm m := by
  rw [← pre_key]; exact defect_k hm θ

/-- `thm:composition`: every product instance has minimum coherent correction mass `d_m`;
`ν ⊗ d_m δ_{x_θ}` is a correction of mass `d_m`, and the stopped defect is `D_{9/4} = d_m`. -/
theorem prod_min_correction {m : ℕ} (hm : 3 ≤ m) {ν : Str d → ℝ} (hν : IsDist ν) {g : Guide}
    (hg : PwLegal (9 / 4) ν g) (θ : Str (2 * m)) :
    IsCorrection (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ))
        (prodDist ν (optCorr m θ)) ∧ ∑ z, prodDist ν (optCorr m θ) z = dm m ∧
      (∀ κ, IsCorrection (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ)) κ →
        dm m ≤ ∑ z, κ z) ∧
      DefectEq (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ)) (dm m) := by
  classical
  have hor := isOracle_hθ hm θ
  obtain ⟨h1, h2⟩ := isCorrection_prod hν (isDist_muθ m θ) (by norm_num) hg hor
    (isCorrection_optCorr hm θ)
  refine ⟨h1, h2.trans (sum_optCorr θ), fun κ hκ => ?_,
    defectEq_prod hν (isDist_muθ m θ) (by norm_num) hg hor (defectEq_hθ hm θ)⟩
  have hge : ∀ x : Str d, ν x * dm m ≤ mass κ (List.ofFn x ++ List.ofFn θ) := by
    intro x
    have := hκ.2 (List.ofFn x ++ List.ofFn θ) (by simp; omega)
    rwa [defect_prod_append hg.1.leaf hor.root hν.1, defect_key hm θ] at this
  set W := (Finset.univ : Finset (Str d)).image fun x => List.ofFn x ++ List.ofFn θ
  have hWcut : IsCut (d + (3 * m + 2)) W := by
    refine ⟨fun u hu => ?_, fun u hu v hv huv => huv.eq_of_length ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu; simp; omega
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hv
      simp
  have hinj : ∀ a ∈ (Finset.univ : Finset (Str d)), ∀ b ∈ (Finset.univ : Finset (Str d)),
      List.ofFn a ++ List.ofFn θ = List.ofFn b ++ List.ofFn θ → a = b :=
    fun a _ b _ hab => List.ofFn_injective (List.append_cancel_right hab)
  calc dm m = ∑ x, ν x * dm m := by rw [← Finset.sum_mul, hν.2, one_mul]
    _ ≤ ∑ x, mass κ (List.ofFn x ++ List.ofFn θ) := Finset.sum_le_sum fun x _ => hge x
    _ = ∑ u ∈ W, mass κ u := (Finset.sum_image hinj).symm
    _ ≤ ∑ z, κ z := hWcut.mass_sum_le hκ.1

/-! ### Certification on the product -/

/-- Success of a certification procedure on a product instance. -/
def prodSucc {m : ℕ} (ν : Str d → ℝ) (g : Guide) (θ : Str (2 * m)) (B : ℝ) :
    Set (Str (d + (3 * m + 2)) → ℝ) :=
  {κ | IsCorrection (9 / 4) (prodDist ν (muθ m θ)) (prodGuide ν g (hθ m θ)) κ ∧ ∑ z, κ z ≤ B}

theorem equality_prod {m : ℕ} (ν : Str d → ℝ) (g : Guide) :
    EqualityStructure fun θ : Str (2 * m) => prodGuide ν g (hθ m θ) := by
  intro u
  by_cases hud : u.length ≤ d
  · exact ⟨none, g u, fun θ _ => prodGuide_short ν g _ hud⟩
  · obtain ⟨e, v, hv⟩ := equality_hθ m (u.drop d)
    refine ⟨e, ν (headS d u) * v, fun θ hθ => ?_⟩
    simp only [prodGuide, hud, ite_false, hv θ hθ]

open Classical in
theorem prod_cert_overlap {m : ℕ} (hm : 3 ≤ m) {ν : Str d → ℝ} (hν : IsDist ν) {g : Guide}
    (hg : PwLegal (9 / 4) ν g) (B : ℝ) (κ : Str (d + (3 * m + 2)) → ℝ) :
    (Finset.univ.filter fun θ : Str (2 * m) => κ ∈ prodSucc ν g θ B).card ≤ ⌊B / dm m⌋₊ := by
  set S := Finset.univ.filter fun θ : Str (2 * m) => κ ∈ prodSucc ν g θ B with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨θ₀, hθ₀⟩
  · rw [h0]; simp
  have hκ0 : ∀ z, 0 ≤ κ z := ((Finset.mem_filter.mp hθ₀).2).1.1
  have hsumB : ∑ z, κ z ≤ B := ((Finset.mem_filter.mp hθ₀).2).2
  have hdm := dm_pos hm
  have hor : ∀ θ : Str (2 * m), IsOracle (muθ m θ) (hθ m θ) := isOracle_hθ hm
  set W := (Finset.univ ×ˢ S).image fun p : Str d × Str (2 * m) => List.ofFn p.1 ++ List.ofFn p.2
  have hWcut : IsCut (d + (3 * m + 2)) W := by
    refine ⟨fun u hu => ?_, fun u hu v hv huv => huv.eq_of_length ?_⟩
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hu; simp; omega
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hv
      simp
  have hinj : Set.InjOn (fun p : Str d × Str (2 * m) => List.ofFn p.1 ++ List.ofFn p.2)
      ((Finset.univ ×ˢ S : Finset (Str d × Str (2 * m))) : Set (Str d × Str (2 * m))) := by
    rintro ⟨x, θ⟩ _ ⟨x', θ'⟩ _ h
    simp only at h
    have hx : List.ofFn x = List.ofFn x' := by
      have := congrArg (List.take d) h
      rwa [List.take_left' (by simp), List.take_left' (by simp)] at this
    rw [hx] at h
    rw [List.ofFn_injective hx, List.ofFn_injective (List.append_cancel_left h)]
  have hge : ∀ θ ∈ S, dm m ≤ ∑ x : Str d, mass κ (List.ofFn x ++ List.ofFn θ) := by
    intro θ hθ
    have hc := ((Finset.mem_filter.mp hθ).2).1
    calc dm m = ∑ x, ν x * dm m := by rw [← Finset.sum_mul, hν.2, one_mul]
      _ ≤ ∑ x : Str d, mass κ (List.ofFn x ++ List.ofFn θ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have := hc.2 (List.ofFn x ++ List.ofFn θ) (by simp; omega)
        rwa [defect_prod_append hg.1.leaf (hor θ).root hν.1, defect_key hm θ] at this
  have h1 : (S.card : ℝ) * dm m ≤ B := by
    calc (S.card : ℝ) * dm m = ∑ θ ∈ S, dm m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ θ ∈ S, ∑ x : Str d, mass κ (List.ofFn x ++ List.ofFn θ) := Finset.sum_le_sum hge
      _ = ∑ u ∈ W, mass κ u := by
        rw [Finset.sum_image hinj, Finset.sum_product, Finset.sum_comm]
      _ ≤ ∑ z, κ z := hWcut.mass_sum_le hκ0
      _ ≤ B := hsumB
  exact Nat.le_floor ((le_div_iff₀ hdm).mpr h1)

/-- Averaging: if the success probabilities over the `M = 4^m` keys sum to at most `c`, some key
has success at most `min {1, c/M}`. -/
theorem exists_key_le {β : Type} {m : ℕ} (P : Str (2 * m) → PMF β) (E : Str (2 * m) → Set β)
    {c : ℝ} (hsum : ∑ θ, (probE (P θ) (E θ)).toReal ≤ c) :
    ∃ θ, (probE (P θ) (E θ)).toReal ≤ min 1 (c / 4 ^ m) := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ θ, c / 4 ^ m < (probE (P θ) (E θ)).toReal := by
    intro θ
    have := hcon θ
    have hle1 := probE_toReal_le_one (P θ) (E θ)
    rcases le_total 1 (c / 4 ^ m) with hc | hc
    · rw [min_eq_left hc] at this; linarith
    · rwa [min_eq_right hc] at this
  have hs := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun θ _ => hlt θ
  rw [Finset.sum_const, Finset.card_univ, card_keys, nsmul_eq_mul] at hs
  push_cast at hs
  rw [mul_div_cancel₀ _ (by positivity)] at hs
  linarith

/-- `thm:composition`, equation `eq:composition-cert`: for every product instance (outer target
`ν` with any pointwise factor-`9/4` guide `g`, fixed publicly) and every procedure with cap `q`,
some key has success probability at most `min {1, (q + ⌊B/d_m⌋)/M}`; hence so is the uniformly
guaranteed success. -/
theorem composition_cert {m : ℕ} (hm : 3 ≤ m) {ν : Str d → ℝ} (hν : IsDist ν) {g : Guide}
    (hg : PwLegal (9 / 4) ν g) (B : ℝ) (q : ℕ) (A : Alg (Str (d + (3 * m + 2)) → ℝ))
    (hA : ∀ θ : Str (2 * m), A.Within (prodGuide ν g (hθ m θ)) q) :
    ∃ θ : Str (2 * m), (probE (A.run (prodGuide ν g (hθ m θ))) (prodSucc ν g θ B)).toReal ≤
      min 1 (((q : ℝ) + ⌊B / dm m⌋₊) / 4 ^ m) := by
  classical
  have h1 := equality_counting (fun θ : Str (2 * m) => prodGuide ν g (hθ m θ))
    (equality_prod ν g) (fun θ => prodSucc ν g θ B) ⌊B / dm m⌋₊ A Finset.univ q
    (fun κ => prod_cert_overlap hm hν hg B κ) (fun θ _ => hA θ)
  have h2 := toReal_sum_probE_le Finset.univ (fun θ => A.run (prodGuide ν g (hθ m θ)))
    (fun θ => prodSucc ν g θ B) (by simp) h1
  rw [ENNReal.toReal_add (by simp) (by simp)] at h2
  simp only [ENNReal.toReal_natCast] at h2
  exact exists_key_le _ _ h2

end Sec5
end LearningGuided
