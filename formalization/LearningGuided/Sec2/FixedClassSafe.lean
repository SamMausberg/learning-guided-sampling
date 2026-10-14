import LearningGuided.Sec2.FixedClass

/-!
# Theorem `thm:fixed-class`: the safe model

The hard safe guides of `𝓗_ℓ` are positive, satisfy `h ≤ (4/3) μ`, and have stopped capacity
at most `263/120 < 9/4`. Every query to them is simulated by one equality test of a key, which
gives the lower bound `eq:fixed-equality`; testing `q` uniformly chosen candidate leaves gives
the matching caps. Together: `Q_safe(𝓗_ℓ,1/16) = 3ℓ` and `Q_safe(𝓗_ℓ,0) = 4ℓ`
(equation `eq:fixed-safe`).
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec2

theorem pubSetF_lt (ℓ : ℕ) : ∀ u ∈ pubSetF ℓ, u.length < ℓ + 4 := fun _ hu => hu.1

theorem CapLE.mono {n : ℕ} {μ : Str n → ℝ} {h : Guide} {C C' : ℝ} (hc : CapLE μ h C)
    (hCC : C ≤ C') : CapLE μ h C' :=
  ⟨hc.1, fun A hA => (hc.2 A hA).trans hCC⟩

/-- The ancestor value at `α = 1/4` is at most `263/120` once `ν(u) ≥ 15/256`. -/
theorem ancVal_quarter_le {v : ℝ} (hv : 15 / 256 ≤ v) : ancVal (1 / 4) v ≤ 263 / 120 := by
  unfold ancVal
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have h1 : (1 / 4 : ℝ) ^ 2 / v ≤ (1 / 4) ^ 2 / (15 / 256) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv
  nlinarith

/-- The capacity value of the hard guides is at most `263/120`. -/
theorem pubCap_hardF_le (ℓ : ℕ) (κ : KeyF ℓ) :
    pubCap (nuF ℓ) (1 / 4) (pubSetF ℓ) (atomK ℓ κ) ≤ 263 / 120 := by
  unfold pubCap
  refine Finset.max'_le _ _ _ fun c hc => ?_
  rcases Finset.mem_insert.mp hc with rfl | hc
  · norm_num
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hpub, hpre⟩ := (mem_pubAnc (pubSetF_lt ℓ)).mp hu
    exact ancVal_quarter_le (mass_nuF_ge_of_isPre_zblk (isPre_zblk_of_pub hpub hpre))

/-- `thm:fixed-class` (hard safe guides): each hard guide satisfies the access conditions, is
positive on `{0,1}^{≤n}`, satisfies `h ≤ (4/3) μ`, and its stopped reciprocal capacity is the
value of `eq:public-capacity`, which is at most `263/120 < 9/4`. In particular it is legal in the
safe model with `R = C = 9/4`. -/
theorem hardF_props (ℓ : ℕ) (κ : KeyF ℓ) :
    IsOracle (muF ℓ κ) (hardF ℓ κ) ∧
      (∀ u : List Bool, u.length ≤ ℓ + 4 → 0 < hardF ℓ κ u) ∧
      (∀ u : List Bool, u.length ≤ ℓ + 4 → hardF ℓ κ u ≤ 4 / 3 * mass (muF ℓ κ) u) ∧
      CapEq (muF ℓ κ) (hardF ℓ κ) (pubCap (nuF ℓ) (1 / 4) (pubSetF ℓ) (atomK ℓ κ)) ∧
      pubCap (nuF ℓ) (1 / 4) (pubSetF ℓ) (atomK ℓ κ) ≤ 263 / 120 ∧
      (263 / 120 : ℝ) < 9 / 4 ∧
      SafeLegal (9 / 4) (9 / 4) (muF ℓ κ) (hardF ℓ κ) := by
  classical
  obtain ⟨hor, hsafe, hcap⟩ := lem_public_capacity (isDist_nuF ℓ) (nuF_pos ℓ) (α := 1 / 4)
    (by norm_num) (le_refl _) (pubSetF_lt ℓ) (atomK ℓ κ)
  have hle := pubCap_hardF_le ℓ κ
  refine ⟨hor, fun u hu => ?_, hsafe, hcap, hle, by norm_num, hor, fun u hu => ?_, ?_⟩
  · simp only [hardF, pubGuide]
    split_ifs
    · exact mass_pos_of_full (isDist_nuF ℓ) (nuF_pos ℓ) hu
    · exact mass_pos_of_full (isDist_muF ℓ κ) (muF_pos ℓ κ) hu
  · have h1 := hsafe u hu
    have h2 := mass_nonneg (isDist_muF ℓ κ).1 u
    unfold hardF
    unfold muF at h2 ⊢
    linarith
  · exact CapLE.mono hcap.1 (by linarith)

/-- `thm:fixed-class` (equality access): every query to the hard guides is simulated by one equality
test of a key. -/
theorem equality_hardF (ℓ : ℕ) : EqualityStructure (hardF ℓ) := by
  classical
  intro u
  by_cases hu : u ∈ pubSetF ℓ
  · exact ⟨none, mass (nuF ℓ) u, fun θ _ => by simp [hardF, pubGuide, hu]⟩
  · have hval : ∀ θ : KeyF ℓ, ¬ IsPre u (atomK ℓ θ) → hardF ℓ θ u = 3 / 4 * mass (nuF ℓ) u := by
      intro θ hθ
      simp only [hardF, pubGuide, hu, ite_false, mass_mixD, hθ]
      norm_num
    by_cases hex : ∃ κ, IsPre u (atomK ℓ κ)
    · refine ⟨some hex.choose, 3 / 4 * mass (nuF ℓ) u, fun θ hθ => hval θ fun h => ?_⟩
      exact hθ (congrArg some (atom_unique_of_not_pub hu hex.choose_spec h))
    · push Not at hex
      exact ⟨none, 3 / 4 * mass (nuF ℓ) u, fun θ _ => hval θ (hex θ)⟩

theorem atom_overlap (ℓ : ℕ) (x : Str (ℓ + 4)) :
    (Finset.univ.filter fun κ : KeyF ℓ => x ∈ ({atomK ℓ κ} : Finset (Str (ℓ + 4)))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_singleton] at ha hb
  exact atomK_injective ℓ (ha.2.symm.trans hb.2)

/-- `thm:fixed-class`, equation `eq:fixed-equality`: every sampler with cap `q` and accuracy `δ`
for `𝓗_ℓ` in the safe model (against the hard guides) satisfies
`q ≥ 16ℓ(1/4 - δ + 3/(64·2^n)) - 1`. -/
theorem fixed_equality (ℓ : ℕ) (δ : ℝ) (q : ℕ) (A : Alg (Str (ℓ + 4)))
    (hA : Solves (SafeLegal (9 / 4) (9 / 4)) (classF ℓ) δ q A) :
    16 * ℓ * (1 / 4 - δ + 3 / (64 * (2 : ℝ) ^ (ℓ + 4))) - 1 ≤ q := by
  have hbound := sampling_equality_bound (hardF ℓ) (equality_hardF ℓ) (muF ℓ) (isDist_muF ℓ)
    (fun κ => {atomK ℓ κ}) (atom_overlap ℓ) A q δ
    (fun κ => hA (muF ℓ κ) ⟨κ, rfl⟩ (hardF ℓ κ) (hardF_props ℓ κ).2.2.2.2.2.2)
  simp only [Finset.sum_singleton] at hbound
  have hsum : ∑ κ : KeyF ℓ, (1 / 4 + 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) - δ) ≤
      ∑ κ : KeyF ℓ, (muF ℓ κ (atomK ℓ κ) - δ) :=
    Finset.sum_le_sum fun κ _ => by linarith [muF_atom_ge ℓ κ]
  rw [Finset.sum_const, Finset.card_univ, card_KeyF, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- The fallback draw from `ν`. -/
noncomputable def drawNuF (ℓ : ℕ) : Alg (Str (ℓ + 4)) :=
  Alg.sample (toPMF (nuF ℓ) (isDist_nuF ℓ)) Alg.ret

theorem lawR_drawNuF (ℓ : ℕ) (h : Guide) : lawR ((drawNuF ℓ).run h) = nuF ℓ := by
  simp only [drawNuF, Alg.run_sample, Alg.run_ret]
  rw [PMF.bind_pure, lawR_toPMF]

theorem within_drawNuF (ℓ : ℕ) (h : Guide) : (drawNuF ℓ).Within h 0 :=
  Alg.Within.sample _ _ _ fun g _ => Alg.Within.ret g 0

/-- The safe sampler of `thm:fixed-class`: test a uniformly chosen set of `q` distinct candidate
leaves; on a hit output that atom, otherwise draw independently from `ν`. -/
noncomputable def safeSearchF (ℓ q : ℕ) (hq : q ≤ 16 * ℓ) : Alg (Str (ℓ + 4)) :=
  searchAlg q (by rw [card_KeyF]; exact hq) (fun κ => List.ofFn (atomK ℓ κ))
    (fun κ r => 3 / 4 * nuF ℓ (atomK ℓ κ) < r) (fun κ => Alg.ret (atomK ℓ κ))
    (fun _ => drawNuF ℓ)

/-- `thm:fixed-class` (safe sampler law): against any guide with exact leaves the output law is
`(1 - q/M) ν + (q/M) δ_{x_{y,j}}`. -/
theorem lawR_safeSearchF (ℓ q : ℕ) (hq : q ≤ 16 * ℓ) (θ : KeyF ℓ) (h : Guide)
    (hleaf : ∀ x : Str (ℓ + 4), h (List.ofFn x) = muF ℓ θ x) :
    lawR ((safeSearchF ℓ q hq).run h) = mixD (nuF ℓ) ((q : ℝ) / (16 * ℓ)) (atomK ℓ θ) := by
  have htest : ∀ κ : KeyF ℓ, (3 / 4 * nuF ℓ (atomK ℓ κ) < h (List.ofFn (atomK ℓ κ))) ↔ κ = θ := by
    intro κ
    rw [hleaf, muF, mixD]
    by_cases hk : κ = θ
    · subst hk; simp only [dirac, ite_true, mul_one, iff_true]; norm_num
    · have : atomK ℓ κ ≠ atomK ℓ θ := fun e => hk (atomK_injective ℓ e)
      simp only [dirac, this, ite_false, mul_zero, add_zero, hk, iff_false, not_lt]
      norm_num
  unfold safeSearchF
  rw [lawR_searchAlg q _ _ _ _ _ h θ htest (atomK ℓ θ) rfl (nuF ℓ) (lawR_drawNuF ℓ h),
    card_KeyF]
  push_cast
  rfl

theorem within_safeSearchF (ℓ q : ℕ) (hq : q ≤ 16 * ℓ) (h : Guide) :
    (safeSearchF ℓ q hq).Within h q := by
  have := within_searchAlg q (by rw [card_KeyF]; exact hq) (fun κ => List.ofFn (atomK ℓ κ))
    (fun κ r => 3 / 4 * nuF ℓ (atomK ℓ κ) < r) (fun κ => Alg.ret (atomK ℓ κ))
    (fun _ => drawNuF ℓ) h 0 (fun κ => Alg.Within.ret _ 0) (fun _ => within_drawNuF ℓ h)
  exact this

theorem safeSearchF_solves (ℓ q : ℕ) (hq : q ≤ 16 * ℓ) (δ : ℝ)
    (hδ : |(q : ℝ) / (16 * ℓ) - 1 / 4| ≤ δ) :
    Solves (SafeLegal (9 / 4) (9 / 4)) (classF ℓ) δ q (safeSearchF ℓ q hq) := by
  rintro μ ⟨θ, rfl⟩ h hl
  refine ⟨within_safeSearchF ℓ q hq h, ?_⟩
  rw [lawR_safeSearchF ℓ q hq θ h hl.1.leaf, muF]
  exact (tv_mixD_le (isDist_nuF ℓ) _ _ _).trans hδ

/-- `thm:fixed-class`, equation `eq:fixed-safe`: `Q_safe(𝓗_ℓ, 1/16) = 3ℓ` and
`Q_safe(𝓗_ℓ, 0) = 4ℓ`. The upper bounds hold for every legal guide; the lower bounds use the hard
guides. -/
theorem fixed_safe (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Qsafe (classF ℓ) (1 / 16) = 3 * ℓ ∧ Qsafe (classF ℓ) 0 = 4 * ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpow : (0 : ℝ) < 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) := by positivity
  constructor
  · refine Qcx_eq (safeSearchF_solves ℓ (3 * ℓ) (by omega) _ ?_) fun q' A' hA' => ?_
    · push_cast
      rw [show (3 * (ℓ : ℝ)) / (16 * ℓ) - 1 / 4 = -(1 / 16) by field_simp; ring]
      norm_num
    · have := fixed_equality ℓ (1 / 16) q' A' hA'
      have h3 : (3 * ℓ : ℝ) - 1 < q' := by nlinarith
      have : (3 * ℓ : ℝ) < q' + 1 := by linarith
      exact_mod_cast (show 3 * ℓ < q' + 1 by exact_mod_cast this) |> Nat.lt_succ_iff.mp
  · refine Qcx_eq (safeSearchF_solves ℓ (4 * ℓ) (by omega) _ ?_) fun q' A' hA' => ?_
    · push_cast
      rw [show (4 * (ℓ : ℝ)) / (16 * ℓ) - 1 / 4 = 0 by field_simp; ring]
      norm_num
    · have := fixed_equality ℓ 0 q' A' hA'
      have h3 : (4 * ℓ : ℝ) - 1 < q' := by nlinarith
      have : (4 * ℓ : ℝ) < q' + 1 := by linarith
      exact_mod_cast (show 4 * ℓ < q' + 1 by exact_mod_cast this) |> Nat.lt_succ_iff.mp

/-- `thm:fixed-class` (the class): `𝓗_ℓ` has exactly `M = 16ℓ` members, all with full support,
on `n = ℓ + 4` bits. -/
theorem classF_props (ℓ : ℕ) :
    (classF ℓ).ncard = 16 * ℓ ∧ ∀ μ ∈ classF ℓ, IsDist μ ∧ ∀ x, 0 < μ x := by
  refine ⟨?_, ?_⟩
  · unfold classF
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (muF_injective ℓ), Set.ncard_univ,
      Nat.card_eq_fintype_card, card_KeyF]
  · rintro μ ⟨κ, rfl⟩
    exact ⟨isDist_muF ℓ κ, muF_pos ℓ κ⟩

end Sec2
end LearningGuided
