import LearningGuided.PointwiseLB.Parameter

/-!
# The small-class lower bound (Lemma `pw-lem:comb`)

For `n, M ≥ 2` put `S = min{M, n}`, `v_i = 1^i 0^{n-i}` (`0 ≤ i < S`), `v_n = 1^n` and
`μ_i = ½ δ_{v_i} + ½ δ_{v_n}`. The oracle `h_i` is `1/2` on nonempty prefixes of `v_i` or `v_n`,
`0` elsewhere, and `1` at the root; it is a factor-two (hence factor-`9/4`) pointwise guide,
exact at the leaves. Every query to `h_i` is answered by a public value except for at most one
index, so Lemma `lem:equality` (`equality_counting`) gives `S · 7/16 ≤ q + 1`; together with the
zero-query obstruction this gives `q ≥ (3/16) min{M, n}`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Comb

variable {n : ℕ}

/-- `v_i = 1^i 0^{n-i}`. -/
def vstr (n i : ℕ) : Str n := fun p => decide (p.1 < i)

/-- `v_n = 1^n`. -/
def vtop (n : ℕ) : Str n := fun _ => true

/-- `μ_i = ½ δ_{v_i} + ½ δ_{v_n}`. -/
noncomputable def mu (n i : ℕ) : Str n → ℝ := fun x => 1 / 2 * dirac (vstr n i) x +
  1 / 2 * dirac (vtop n) x

open Classical in
/-- The comb oracle. -/
noncomputable def orc (n i : ℕ) (u : List Bool) : ℝ :=
  if u = [] then 1
  else if u.length ≤ n ∧ (IsPre u (vstr n i) ∨ IsPre u (vtop n)) then 1 / 2 else 0

theorem vstr_ne_vtop {i : ℕ} (hi : i < n) : vstr n i ≠ vtop n := by
  intro h
  have := congrFun h ⟨i, hi⟩
  simp [vstr, vtop] at this

theorem vstr_injective {i j : ℕ} (hi : i < n) (hj : j < n) (h : vstr n i = vstr n j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := congrFun h ⟨i, hi⟩; simp [vstr, hlt] at this
  · have := congrFun h ⟨j, hj⟩; simp [vstr, hlt] at this

theorem isDist_mu (i : ℕ) : IsDist (mu n i) := by
  have := isDist_mix (isDist_dirac (vstr n i)) (isDist_dirac (vtop n))
    (a := 1 / 2) (by norm_num) (by norm_num)
  convert this using 2
  unfold mu; ring

theorem mass_mu (i : ℕ) (u : List Bool) :
    mass (mu n i) u = 1 / 2 * (if IsPre u (vstr n i) then 1 else 0) +
      1 / 2 * (if IsPre u (vtop n) then 1 else 0) := by
  unfold mu
  rw [mass_linear, mass_dirac, mass_dirac]

theorem orc_pwLegal (hn : 1 ≤ n) {i : ℕ} (hi : i < n) : PwLegal (9 / 4) (mu n i) (orc n i) := by
  classical
  refine ⟨⟨fun u => ?_, by simp [orc], fun x => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
  · unfold orc; split_ifs <;> norm_num
  · have hne : List.ofFn x ≠ [] := by rw [Ne, List.ofFn_eq_nil_iff]; omega
    unfold orc mu dirac
    rw [ite_eq_right hne]
    simp only [List.length_ofFn, le_refl, true_and, isPre_ofFn_iff]
    by_cases h1 : x = vstr n i
    · subst h1
      have : vstr n i ≠ vtop n := vstr_ne_vtop hi
      simp [this]
    · by_cases h2 : x = vtop n
      · subst h2; simp [h1]
      · simp [h1, h2]
  · have hne : u ≠ [] := by rintro rfl; simp at hu
    unfold orc
    rw [ite_eq_right hne, ite_eq_right (fun h => by omega)]
  · rw [mass_mu]
    unfold orc
    by_cases h0 : u = []
    · subst h0; simp [isPre_nil]; norm_num
    · rw [ite_eq_right h0]
      by_cases h1 : IsPre u (vstr n i) <;> by_cases h2 : IsPre u (vtop n) <;>
        simp [h1, h2, hu] <;> norm_num

theorem isPre_iff_get {u : List Bool} {x : Str n} :
    IsPre u x ↔ ∃ hl : u.length ≤ n, ∀ p (hp : p < u.length), u[p] = x ⟨p, by omega⟩ := by
  unfold IsPre
  rw [List.prefix_iff_getElem]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨by simpa using hl, fun p hp => ?_⟩
    rw [h p hp, List.getElem_ofFn]
  · rintro ⟨hl, h⟩
    refine ⟨by simpa using hl, fun p hp => ?_⟩
    rw [h p hp, List.getElem_ofFn]

/-- A word that is not a prefix of `1^n` is a prefix of at most one `v_i`. -/
theorem unique_key {u : List Bool} (htop : ¬ IsPre u (vtop n)) {i j : ℕ}
    (hi : IsPre u (vstr n i)) (hj : IsPre u (vstr n j)) : i = j := by
  obtain ⟨hl, hi'⟩ := isPre_iff_get.mp hi
  obtain ⟨hl2, hj'⟩ := isPre_iff_get.mp hj
  have hall : ∀ k, u.length ≤ k → IsPre u (vstr n k) → IsPre u (vtop n) := by
    intro k hk hk'
    obtain ⟨hl', hk''⟩ := isPre_iff_get.mp hk'
    refine isPre_iff_get.mpr ⟨hl', fun p hp => ?_⟩
    rw [hk'' p hp]; simp [vstr, vtop]; omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · by_cases hu : u.length ≤ i
    · exact htop (hall i hu hi)
    · have h1 := hi' i (by omega)
      have h2 := hj' i (by omega)
      rw [h1] at h2; simp [vstr, hlt] at h2
  · by_cases hu : u.length ≤ j
    · exact htop (hall j hu hj)
    · have h1 := hi' j (by omega)
      have h2 := hj' j (by omega)
      rw [h1] at h2; simp [vstr, hlt] at h2

theorem equalityStructure (S : ℕ) :
    EqualityStructure (fun i : Fin S => orc n i) := by
  classical
  intro u
  by_cases h0 : u = []
  · exact ⟨none, 1, fun i _ => by simp [orc, h0]⟩
  by_cases hl : u.length ≤ n
  swap
  · exact ⟨none, 0, fun i _ => by simp [orc, h0, hl]⟩
  by_cases htop : IsPre u (vtop n)
  · exact ⟨none, 1 / 2, fun i _ => by simp [orc, h0, hl, htop]⟩
  by_cases hex : ∃ i : Fin S, IsPre u (vstr n i)
  · refine ⟨some hex.choose, 0, fun i hi => ?_⟩
    have : ¬ IsPre u (vstr n i) := fun h =>
      hi (congrArg some (Fin.ext (unique_key htop hex.choose_spec h)))
    simp [orc, h0, this, htop]
  · push Not at hex
    exact ⟨none, 0, fun i _ => by simp [orc, h0, hex i, htop]⟩

/-- `pw-lem:comb`: for every `n, M ≥ 2` there is a class of at most `M` distributions on
`n` bits on which every algorithm solving the class at error `1/16` in the pointwise model with
cap `q` has `q ≥ (3/16) min{M, n}`. -/
theorem pw_lem_comb (n M : ℕ) (hn : 2 ≤ n) (hM : 2 ≤ M) :
    ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
      ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
        (3 / 16 : ℝ) * (min M n : ℕ) ≤ q := by
  classical
  set S := min M n with hSdef
  have hS2 : 2 ≤ S := le_min hM hn
  have hSn : S ≤ n := min_le_right _ _
  refine ⟨Finset.univ.image (fun i : Fin S => mu n i), ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans
      (by simp only [Finset.card_univ, Fintype.card_fin]; exact min_le_left _ _)
  · intro μ hμ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
    exact isDist_mu i
  intro q A hA
  have hval : ∀ i : Fin S, A.Within (orc n i) q ∧ tv (lawR (A.run (orc n i))) (mu n i) ≤ 1 / 16 :=
    fun i => hA _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) _
      (orc_pwLegal (by omega) (by omega))
  -- q ≥ 1 from the zero-query obstruction
  have hq1 : 1 ≤ q := by
    by_contra hq0
    have hq : q = 0 := by omega
    subst hq
    have i0 : (0 : ℕ) < S := by omega
    have i1 : (1 : ℕ) < S := by omega
    refine zero_query_obstruction (μ₁ := mu n 0) (μ₂ := mu n 1) ?_ A
      (hval ⟨0, i0⟩).1 (hval ⟨1, i1⟩).1 (hval ⟨0, i0⟩).2 (hval ⟨1, i1⟩).2
    -- TV(μ₀, μ₁) ≥ 1/4
    have hv0 : vstr n 0 ≠ vstr n 1 := fun h => by
      have := vstr_injective (n := n) (by omega) (by omega) h; omega
    have h0top : vstr n 0 ≠ vtop n := vstr_ne_vtop (by omega)
    have hterm : |mu n 0 (vstr n 0) - mu n 1 (vstr n 0)| = 1 / 2 := by
      simp [mu, dirac, hv0, h0top]
    have : |mu n 0 (vstr n 0) - mu n 1 (vstr n 0)| ≤ ∑ x, |mu n 0 x - mu n 1 x| :=
      Finset.single_le_sum (f := fun x => |mu n 0 x - mu n 1 x|) (fun x _ => abs_nonneg _)
        (Finset.mem_univ _)
    unfold tv; rw [hterm] at this; linarith
  -- the equality-counting bound
  have hcount := equality_counting (fun i : Fin S => orc n i) (equalityStructure S)
    (fun i : Fin S => ({vstr n i} : Set (Str n))) 1 A Finset.univ q
    (fun x => by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff] at ha hb
      exact Fin.ext (vstr_injective (by omega) (by omega) (ha.symm.trans hb)))
    (fun i _ => (hval i).1)
  have hprob : ∀ i : Fin S, (7 / 16 : ℝ) ≤
      (probE (A.run (orc n i)) ({vstr n i} : Set (Str n))).toReal := by
    intro i
    have h := prob_ge_of_tv (isDist_mu (n := n) i) (hval i).2 {vstr n i}
    have hne : vstr n i ≠ vtop n := vstr_ne_vtop (by omega)
    simp only [Finset.sum_singleton, Finset.coe_singleton] at h
    have : mu n i (vstr n i) = 1 / 2 := by simp [mu, dirac, hne]
    rw [this] at h; linarith
  have hsum : (S : ℝ) * (7 / 16) ≤ q + 1 := by
    have hfin : ∀ i ∈ (Finset.univ : Finset (Fin S)),
        probE (A.run (orc n i)) ({vstr n i} : Set (Str n)) ≠ ⊤ := fun i _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (probE_le_one _ _)
    have h1 := ENNReal.toReal_mono (by simp) hcount
    rw [ENNReal.toReal_sum hfin] at h1
    have h2 : ((q : ENNReal) + ((1 : ℕ) : ENNReal)).toReal = q + 1 := by
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top q) (ENNReal.natCast_ne_top 1)]; simp
    rw [h2] at h1
    calc (S : ℝ) * (7 / 16) = ∑ _i : Fin S, (7 / 16 : ℝ) := by simp
      _ ≤ ∑ i : Fin S, (probE (A.run (orc n i)) ({vstr n i} : Set (Str n))).toReal :=
          Finset.sum_le_sum fun i _ => hprob i
      _ ≤ q + 1 := h1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  by_cases hS4 : 4 ≤ S
  · have : (4 : ℝ) ≤ S := by exact_mod_cast hS4
    nlinarith
  · have : (S : ℝ) ≤ 3 := by exact_mod_cast (by omega : S ≤ 3)
    nlinarith

end Comb

end LearningGuided.PointwiseLB
