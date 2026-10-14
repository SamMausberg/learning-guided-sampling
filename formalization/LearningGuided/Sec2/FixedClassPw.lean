import LearningGuided.Sec2.FixedClassSafe

/-!
# Theorem `thm:fixed-class`: the pointwise model

Every pointwise factor-`9/4` guide separates the probe words `y 0^t`, `t < ℓ`, at threshold `1/8`:
an excluded atom gives `h ≤ 27/256 < 1/8`, an included atom gives `h ≥ 301/2304 > 1/8`. Selecting
four of the sixteen groups uniformly, then binary searching the position of the one, samples
`𝓗_ℓ` exactly with cap `4 + ⌈log₂ ℓ⌉`. The exact guides have at most two answers per prefix, so
`2^q > 3ℓ` at error `1/16`. Together, `Q_pw(𝓗_ℓ,1/16) = Θ(log(2+ℓ))` (equation `eq:fixed-point`).
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec2

/-- The exact guides `h = μ_{y,j}`. -/
noncomputable def exactF (ℓ : ℕ) (κ : KeyF ℓ) : Guide := fun u => mass (muF ℓ κ) u

theorem binary_exactF (ℓ : ℕ) : BinaryAnswers (exactF ℓ) := by
  intro u
  refine ⟨3 / 4 * mass (nuF ℓ) u, 3 / 4 * mass (nuF ℓ) u + 1 / 4, fun κ => ?_⟩
  simp only [exactF, mass_muF]
  split_ifs
  · right; ring
  · left; ring

/-- `thm:fixed-class` (transcript counting for `𝓗_ℓ`): a pointwise sampler with cap `q` and accuracy
`δ` satisfies `16ℓ(1/4 - δ + 3/(64·2^n)) ≤ 2^q`. -/
theorem fixed_binary (ℓ : ℕ) (δ : ℝ) (q : ℕ) (A : Alg (Str (ℓ + 4)))
    (hA : Solves (PwLegal (9 / 4)) (classF ℓ) δ q A) :
    16 * ℓ * (1 / 4 - δ + 3 / (64 * (2 : ℝ) ^ (ℓ + 4))) ≤ 2 ^ q := by
  have hbound := sampling_binary_bound (exactF ℓ) (binary_exactF ℓ) (muF ℓ) (isDist_muF ℓ)
    (fun κ => {atomK ℓ κ}) (atom_overlap ℓ) A q δ
    (fun κ => hA (muF ℓ κ) ⟨κ, rfl⟩ (exactF ℓ κ) (pwLegal_exact (isDist_muF ℓ κ) (by norm_num)))
  simp only [Finset.sum_singleton] at hbound
  have hsum : ∑ κ : KeyF ℓ, (1 / 4 + 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) - δ) ≤
      ∑ κ : KeyF ℓ, (muF ℓ κ (atomK ℓ κ) - δ) :=
    Finset.sum_le_sum fun κ _ => by linarith [muF_atom_ge ℓ κ]
  rw [Finset.sum_const, Finset.card_univ, card_KeyF, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- `thm:fixed-class` (threshold `1/8`): the test at a probe word `y 0^t`, `t < ℓ`: for every
pointwise factor-`9/4` guide, `h(y 0^t) > 1/8` exactly when `y 0^t` lies above the atom. -/
theorem probe_test {ℓ : ℕ} {θ : KeyF ℓ} {h : Guide} (hl : PwLegal (9 / 4) (muF ℓ θ) h)
    (y : Str 4) {t : ℕ} (ht : t < ℓ) :
    1 / 8 < h (grpWord y t) ↔ IsPre (grpWord y t) (atomK ℓ θ) := by
  have hlen : (grpWord y t).length ≤ ℓ + 4 := by rw [grpWord_length]; omega
  have hb := hl.2 _ hlen
  have hlo := mass_nuF_ge_of_isPre_zblk (isPre_grpWord_zblk (ℓ := ℓ) y ht.le)
  have hhi := mass_nuF_le (ℓ := ℓ) (by rw [grpWord_length]; omega) hlen
  rw [mass_muF] at hb
  constructor
  · intro h8
    by_contra hp
    rw [ite_eq_right hp] at hb
    linarith [hb.2]
  · intro hp
    rw [ite_eq_left hp] at hb
    linarith [hb.1]

open Classical in
/-- Binary search for the position of the one inside the group `y`, with `f` remaining queries,
on the index interval `[lo, hi)`. -/
noncomputable def bsearch (ℓ : ℕ) (y : Str 4) : ℕ → ℕ → ℕ → Alg (Str (ℓ + 4))
  | 0, lo, _ => Alg.ret (atomF ℓ y lo)
  | f + 1, lo, hi =>
      if hi ≤ lo + 1 then Alg.ret (atomF ℓ y lo)
      else Alg.query (grpWord y ((lo + hi) / 2)) (fun r =>
        if 1 / 8 < r then bsearch ℓ y f ((lo + hi) / 2) hi else bsearch ℓ y f lo ((lo + hi) / 2))

theorem within_bsearch (ℓ : ℕ) (y : Str 4) (h : Guide) :
    ∀ f lo hi, (bsearch ℓ y f lo hi).Within h f := by
  intro f
  induction f with
  | zero => intro lo hi; exact Alg.Within.ret _ 0
  | succ f ih =>
      intro lo hi
      simp only [bsearch]
      split_ifs
      · exact Alg.Within.ret _ _
      · refine Alg.Within.query _ _ _ ?_
        split_ifs
        · exact ih _ _
        · exact ih _ _

theorem clog_half_le {s f : ℕ} (hs : 2 ≤ s) (hf : Nat.clog 2 s ≤ f + 1) {r : ℕ}
    (hr : r ≤ (s + 1) / 2) : Nat.clog 2 r ≤ f := by
  rw [Nat.clog_of_two_le (by norm_num) hs, show s + 2 - 1 = s + 1 by omega] at hf
  exact (Nat.clog_mono_right 2 hr).trans (by omega)

/-- Correctness of the binary search: if the probe answers reveal whether `t ≤ j`, the search
started on an interval containing `j` with enough remaining queries returns the atom. -/
theorem run_bsearch (ℓ : ℕ) (y : Str 4) (h : Guide) (j : ℕ)
    (htest : ∀ t < ℓ, 1 / 8 < h (grpWord y t) ↔ t ≤ j) :
    ∀ f lo hi, lo ≤ j → j < hi → hi ≤ ℓ → Nat.clog 2 (hi - lo) ≤ f →
      (bsearch ℓ y f lo hi).run h = PMF.pure (atomF ℓ y j) := by
  intro f
  induction f with
  | zero =>
      intro lo hi hlo hhi _ hf
      have : hi - lo ≤ 1 := by
        by_contra hc
        have := Nat.clog_pos (b := 2) (by norm_num) (show 1 < hi - lo by omega)
        omega
      have : j = lo := by omega
      subst this
      rfl
  | succ f ih =>
      intro lo hi hlo hhi hℓ hf
      simp only [bsearch]
      split_ifs with hsmall
      · have : j = lo := by omega
        subst this
        rfl
      · rw [Alg.run_query]
        have hmid1 : lo < (lo + hi) / 2 := by omega
        have hmid2 : (lo + hi) / 2 < hi := by omega
        by_cases hm : (lo + hi) / 2 ≤ j
        · rw [ite_eq_left ((htest _ (by omega)).mpr hm)]
          exact ih _ _ hm hhi hℓ (clog_half_le (by omega) hf (by omega))
        · rw [ite_eq_right (fun h' => hm ((htest _ (by omega)).mp h'))]
          exact ih _ _ hlo (by omega) (by omega) (clog_half_le (by omega) hf (by omega))

/-- The pointwise sampler of `thm:fixed-class`: select four of the sixteen groups uniformly
(inclusion probability `1/4`), query them until a hit, binary search the position of the one in
the hit group, and otherwise draw independently from `ν`. -/
noncomputable def pwSearchF (ℓ : ℕ) : Alg (Str (ℓ + 4)) :=
  searchAlg 4 (by simp) (fun y : Str 4 => List.ofFn y) (fun _ r => 1 / 8 < r)
    (fun y => bsearch ℓ y (Nat.clog 2 ℓ) 0 ℓ) (fun _ => drawNuF ℓ)

theorem within_pwSearchF (ℓ : ℕ) (h : Guide) : (pwSearchF ℓ).Within h (4 + Nat.clog 2 ℓ) :=
  within_searchAlg 4 _ _ _ _ _ h _ (fun y => within_bsearch ℓ y h _ _ _)
    (fun _ => (within_drawNuF ℓ h).mono (Nat.zero_le _))

theorem grpWord_zero (y : Str 4) : grpWord y 0 = List.ofFn y := by simp [grpWord]

/-- `thm:fixed-class`, equation `eq:fixed-point`: the pointwise sampler is exact: its output law is
`μ_{y,j}` for every pointwise factor-`9/4` guide. -/
theorem lawR_pwSearchF {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {θ : KeyF ℓ} {h : Guide}
    (hl : PwLegal (9 / 4) (muF ℓ θ) h) : lawR ((pwSearchF ℓ).run h) = muF ℓ θ := by
  have htest : ∀ y : Str 4, (1 / 8 < h (List.ofFn y)) ↔ y = θ.1 := by
    intro y
    rw [← grpWord_zero, probe_test hl y (by omega), atomK,
      isPre_grpWord_atomF y θ.1 (Nat.zero_le _)]
    simp
  have hhit : (bsearch ℓ θ.1 (Nat.clog 2 ℓ) 0 ℓ).run h = PMF.pure (atomK ℓ θ) := by
    refine run_bsearch ℓ θ.1 h θ.2.1 (fun t ht => ?_) _ 0 ℓ (Nat.zero_le _) θ.2.2 le_rfl
      (by simp)
    rw [probe_test hl θ.1 ht, atomK, isPre_grpWord_atomF θ.1 θ.1 ht.le]
    simp
  unfold pwSearchF
  rw [lawR_searchAlg 4 _ _ _ _ _ h θ.1 htest (atomK ℓ θ) hhit (nuF ℓ) (lawR_drawNuF ℓ h), muF]
  congr 1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  norm_num

theorem pwSearchF_solves (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Solves (PwLegal (9 / 4)) (classF ℓ) 0 (4 + Nat.clog 2 ℓ) (pwSearchF ℓ) := by
  rintro μ ⟨θ, rfl⟩ h hl
  refine ⟨within_pwSearchF ℓ h, ?_⟩
  rw [lawR_pwSearchF hℓ hl, tv_self]

theorem natCeil_logb_two (ℓ : ℕ) : ⌈Real.logb 2 ℓ⌉₊ = Nat.clog 2 ℓ := by
  have := Real.natCeil_logb_natCast 2 ℓ
  simpa using this

/-- `thm:fixed-class`, equation `eq:fixed-point` (exact sampling): `Q_pw(𝓗_ℓ,0) ≤ 4 + ⌈log₂ ℓ⌉`,
by the four-group search followed by binary search, with exact output law. -/
theorem fixed_point_exact (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Qpw (classF ℓ) 0 ≤ 4 + ⌈Real.logb 2 ℓ⌉₊ := by
  rw [natCeil_logb_two]
  exact Qcx_le (pwSearchF_solves ℓ hℓ)

/-- `thm:fixed-class`: at error `1/16` every pointwise sampler of `𝓗_ℓ` has `2^q > 3ℓ`. -/
theorem fixed_point_binary (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (q : ℕ) (A : Alg (Str (ℓ + 4)))
    (hA : Solves (PwLegal (9 / 4)) (classF ℓ) (1 / 16) q A) : (3 * ℓ : ℝ) < 2 ^ q := by
  have := fixed_binary ℓ (1 / 16) q A hA
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpow : (0 : ℝ) < 3 / (64 * (2 : ℝ) ^ (ℓ + 4)) := by positivity
  nlinarith

theorem one_le_log_two_add {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 1 ≤ Real.log (2 + ℓ) := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have he : Real.exp 1 ≤ 2 + ℓ := by linarith
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) he

/-- `thm:fixed-class`, equation `eq:fixed-point` (fixed error): `Q_pw(𝓗_ℓ,1/16) = Θ(log(2+ℓ))`
with absolute constants: `log(2+ℓ) ≤ Q_pw(𝓗_ℓ,1/16) ≤ 7 log(2+ℓ)` for every `ℓ ≥ 1`. -/
theorem fixed_point_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      c₁ * Real.log (2 + ℓ) ≤ (Qpw (classF ℓ) (1 / 16) : ℝ) ∧
        (Qpw (classF ℓ) (1 / 16) : ℝ) ≤ c₂ * Real.log (2 + ℓ) := by
  refine ⟨1, 7, by norm_num, by norm_num, fun ℓ hℓ => ⟨?_, ?_⟩⟩
  · have hle : ∀ q A, Solves (PwLegal (9 / 4)) (classF ℓ) (1 / 16) q A →
        Real.log (2 + ℓ) ≤ q := by
      intro q A hA
      have h3 := fixed_point_binary ℓ hℓ q A hA
      have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      have hlt : (2 + ℓ : ℝ) < 2 ^ q := by linarith
      have := Real.log_lt_log (by positivity) hlt
      rw [Real.log_pow] at this
      have hl2 := Real.log_two_lt_d9
      have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    have hex : ∃ q A, Solves (PwLegal (9 / 4)) (classF ℓ) (1 / 16) q A :=
      ⟨_, _, solves_mono_delta (pwSearchF_solves ℓ hℓ) (by norm_num)⟩
    obtain ⟨A, hA⟩ := exists_solver_Qcx hex
    rw [one_mul]
    exact hle _ A hA
  · have h1 : Qpw (classF ℓ) (1 / 16) ≤ 4 + Nat.clog 2 ℓ :=
      Qcx_le (solves_mono_delta (pwSearchF_solves ℓ hℓ) (by norm_num))
    have h2 : (Nat.clog 2 ℓ : ℝ) < Real.logb 2 ℓ + 1 := by
      rw [← natCeil_logb_two]
      exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast hℓ))
    have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have h3 : Real.logb 2 ℓ ≤ 2 * Real.log (2 + ℓ) := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have hl2 := Real.log_two_gt_d9
      have hlog : Real.log ℓ ≤ Real.log (2 + ℓ) :=
        Real.log_le_log (by linarith) (by linarith)
      have h0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓr
      nlinarith
    have h4 := one_le_log_two_add hℓ
    have h1' : (Qpw (classF ℓ) (1 / 16) : ℝ) ≤ 4 + Nat.clog 2 ℓ := by exact_mod_cast h1
    linarith

/-- The rate `K(n,M) = min{M, n √(log M), n²}` of `eq:K`. -/
noncomputable def Krate (n M : ℕ) : ℝ := min (M : ℝ) (min (n * Real.sqrt (Real.log M)) (n ^ 2))

/-- `thm:fixed-class` (remark on `eq:K`): for `n = ℓ + 4` and `M = 16ℓ`,
`ℓ ≤ K(n,M) ≤ 16ℓ`, so `K(n,M) = Θ(ℓ)`. -/
theorem Krate_fixed (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (ℓ : ℝ) ≤ Krate (ℓ + 4) (16 * ℓ) ∧ Krate (ℓ + 4) (16 * ℓ) ≤ 16 * ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  refine ⟨?_, ?_⟩
  · unfold Krate
    push_cast
    have hlog : 1 ≤ Real.log (16 * ℓ) := by
      have := one_le_log_two_add (ℓ := 14) (by norm_num)
      calc (1 : ℝ) ≤ Real.log (2 + 14) := by exact_mod_cast this
        _ ≤ Real.log (16 * ℓ) := Real.log_le_log (by norm_num) (by linarith)
    have hsq : 1 ≤ Real.sqrt (Real.log (16 * ℓ)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hlog
    refine le_min (by linarith) (le_min ?_ ?_)
    · nlinarith
    · nlinarith
  · unfold Krate
    push_cast
    exact min_le_left _ _

/-- `thm:fixed-class`: for every `ℓ ≥ 1` the class `𝓗_ℓ` has `M = 16ℓ` full-support members on
`n = ℓ + 4` bits, `Q_pw(𝓗_ℓ,0) ≤ 4 + ⌈log₂ ℓ⌉`, `Q_safe(𝓗_ℓ,1/16) = 3ℓ`, `Q_safe(𝓗_ℓ,0) = 4ℓ`
(equations `eq:fixed-point`, `eq:fixed-safe`), and the hard safe guides are positive with
`h ≤ (4/3) μ` and capacity at most `263/120 < 9/4`; moreover
`Q_pw(𝓗_ℓ,1/16) = Θ(log(2+ℓ))` with absolute constants. -/
theorem thm_fixed_class :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      c₁ * Real.log (2 + ℓ) ≤ (Qpw (classF ℓ) (1 / 16) : ℝ) ∧
        (Qpw (classF ℓ) (1 / 16) : ℝ) ≤ c₂ * Real.log (2 + ℓ)) ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      (classF ℓ).ncard = 16 * ℓ ∧ (∀ μ ∈ classF ℓ, IsDist μ ∧ ∀ x, 0 < μ x) ∧
      Qpw (classF ℓ) 0 ≤ 4 + ⌈Real.logb 2 ℓ⌉₊ ∧
      Qsafe (classF ℓ) (1 / 16) = 3 * ℓ ∧ Qsafe (classF ℓ) 0 = 4 * ℓ ∧
      ∀ κ : KeyF ℓ, (∀ u : List Bool, u.length ≤ ℓ + 4 → 0 < hardF ℓ κ u) ∧
        (∀ u : List Bool, u.length ≤ ℓ + 4 → hardF ℓ κ u ≤ 4 / 3 * mass (muF ℓ κ) u) ∧
        CapLE (muF ℓ κ) (hardF ℓ κ) (263 / 120) ∧ (263 / 120 : ℝ) < 9 / 4 ∧
        SafeLegal (9 / 4) (9 / 4) (muF ℓ κ) (hardF ℓ κ) := by
  refine ⟨fixed_point_theta, fun ℓ hℓ => ⟨(classF_props ℓ).1, (classF_props ℓ).2,
    fixed_point_exact ℓ hℓ, (fixed_safe ℓ hℓ).1, (fixed_safe ℓ hℓ).2, fun κ => ?_⟩⟩
  obtain ⟨-, hpos, hsafe, hcap, hle, hlt, hlegal⟩ := hardF_props ℓ κ
  exact ⟨hpos, hsafe, CapLE.mono hcap.1 hle, hlt, hlegal⟩

end Sec2
end LearningGuided
