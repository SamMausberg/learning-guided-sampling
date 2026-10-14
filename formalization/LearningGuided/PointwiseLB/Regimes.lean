import LearningGuided.PointwiseLB.Comb

/-!
# Dependence on string length and class size (`pw-sec:parameters`)

* `choose_params`: the table parameters used in both regimes. For a bound `8 ≤ R ≤ n/(16 L)`
  with `L = log(2n)`, `r` is the largest power of two at most `R` and
  `ℓ = ⌊(n-1)/r⌋ - 2 log₂ r`; then `N ≤ n`, `ℓ ≤ n`, `R/2 < r ≤ R` and `ℓ - 1 ≥ n/(2r)`.
* `pw_expn_lower`: the exponential-size regime (left inequality of `eq:pw-expn`).
* `pw_main_lower`: the lower bound of Theorem `thm:pointwise` (left inequality of
  `eq:pw-main`), following the case analysis of the paper (`n ≥ 1024` with `R_* ≥ 8` or
  `R_* < 8`, and `n < 1024`).
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

namespace Regimes

theorem log_two_mul_le {x x₀ : ℝ} (h0 : 0 < x₀) (hx : x₀ ≤ x) :
    Real.log (2 * x) ≤ Real.log (2 * x₀) + x / x₀ - 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le h0 hx
  have e : 2 * x = (2 * x₀) * (x / x₀) := by field_simp
  rw [e, Real.log_mul (by positivity) (by positivity)]
  have := Real.log_le_sub_one_of_pos (show 0 < x / x₀ by positivity)
  linarith

theorem log_two_pow_le (k : ℕ) : Real.log (2 ^ k) ≤ k * 0.6931471808 := by
  rw [Real.log_pow]
  have := Real.log_two_lt_d9
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- For `n ≥ 1024`, `128 log(2n) ≤ n`, i.e. `n/(16 log(2n)) ≥ 8`. -/
theorem log_bound_1024 {n : ℝ} (hn : 1024 ≤ n) : 128 * Real.log (2 * n) ≤ n := by
  have h := log_two_mul_le (x₀ := 1024) (by norm_num) hn
  have h2 : Real.log (2 * 1024) ≤ 11 * 0.6931471808 := by
    have := log_two_pow_le 11; norm_num at this ⊢; exact this
  have : n / 1024 * 128 = n / 8 := by ring
  nlinarith

/-- For `n ≥ 4096`, `256 log(2n) ≤ n`. -/
theorem log_bound_4096 {n : ℝ} (hn : 4096 ≤ n) : 256 * Real.log (2 * n) ≤ n := by
  have h := log_two_mul_le (x₀ := 4096) (by norm_num) hn
  have h2 : Real.log (2 * 4096) ≤ 13 * 0.6931471808 := by
    have := log_two_pow_le 13; norm_num at this ⊢; exact this
  have : n / 4096 * 256 = n / 16 := by ring
  nlinarith

theorem one_le_log_two_mul {n : ℝ} (hn : 2 ≤ n) : 1 ≤ Real.log (2 * n) := by
  have h4 : Real.log 4 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  norm_num at this
  linarith

/-- `pw-sec:parameters`, `pw-eq:expn-parameters`: the choice of parameters. -/
theorem choose_params {n : ℕ} (hn : 2 ≤ n) {Rb : ℝ} (h8 : 8 ≤ Rb)
    (hRb : Rb ≤ n / (16 * Real.log (2 * n))) :
    ∃ P : Prm, P.N ≤ n ∧ P.ℓ ≤ n ∧ (P.r : ℝ) ≤ Rb ∧ Rb / 2 < P.r ∧
      (n : ℝ) / (2 * P.r) ≤ (P.ℓ : ℝ) - 1 := by
  set L := Real.log (2 * (n : ℝ)) with hLdef
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := one_le_log_two_mul hn2
  have hLpos : 0 < L := by linarith
  have hnL : 128 * L ≤ n := by
    rw [le_div_iff₀ (by positivity)] at hRb; nlinarith
  -- r: the largest power of two at most Rb
  set m := ⌊Rb⌋₊ with hmdef
  have hm8 : 8 ≤ m := Nat.le_floor (by exact_mod_cast h8)
  have hmRb : (m : ℝ) ≤ Rb := Nat.floor_le (by linarith)
  have hRbm : Rb < m + 1 := Nat.lt_floor_add_one Rb
  set p := Nat.log 2 m with hpdef
  have hp3 : 3 ≤ p := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hrm : 2 ^ p ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hmr : m < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  set r := 2 ^ p with hrdef
  have hr8 : 8 ≤ r := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  set ρ : ℝ := (r : ℝ) with hρdef
  have hρ8 : (8 : ℝ) ≤ ρ := by rw [hρdef]; exact_mod_cast hr8
  have hρRb : ρ ≤ Rb := le_trans (by rw [hρdef]; exact_mod_cast hrm) hmRb
  have hRb2 : Rb / 2 < ρ := by
    have : (m : ℝ) + 1 ≤ 2 * ρ := by
      have : m + 1 ≤ 2 * r := by rw [hrdef, ← pow_succ']; omega
      rw [hρdef]; exact_mod_cast this
    linarith
  have hρL : ρ * (16 * L) ≤ n := by
    have := hρRb.trans hRb
    rwa [le_div_iff₀ (by positivity)] at this
  -- log₂ r ≤ 1.45 L
  have hpL : (p : ℝ) ≤ 1.45 * L := by
    have h1 : (p : ℝ) * Real.log 2 = Real.log ρ := by
      rw [hρdef, hrdef]; push_cast; rw [Real.log_pow]
    have h2 : Real.log ρ ≤ Real.log n := Real.log_le_log (by positivity) (by nlinarith)
    have h3 : Real.log n ≤ L := Real.log_le_log (by positivity) (by linarith)
    have := Real.log_two_gt_d9
    norm_num at this
    nlinarith
  -- the quotient Q = ⌊(n-1)/r⌋
  set Q := (n - 1) / r with hQdef
  have hQ1 : Q * r ≤ n - 1 := Nat.div_mul_le_self _ _
  have hQ2 : n - 1 < Q * r + r := Nat.lt_div_mul_add (by omega)
  have hQ2r : (n : ℝ) - 1 < (Q + 1) * ρ := by
    have : ((n - 1 : ℕ) : ℝ) < (Q * r + r : ℕ) := by exact_mod_cast hQ2
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this
    rw [hρdef]; linarith
  have hkey : (2 * (p : ℝ) + 2) * ρ ≤ (n : ℝ) / 2 - 1 := by nlinarith
  have hQreal : (n : ℝ) / (2 * ρ) + 2 * p + 1 < Q := by
    have hρpos : 0 < ρ := by linarith
    have : ((n : ℝ) / (2 * ρ) + 2 * p + 1) * ρ < Q * ρ := by
      have e : ((n : ℝ) / (2 * ρ) + 2 * p + 1) * ρ = n / 2 + (2 * p + 1) * ρ := by
        field_simp; ring
      rw [e]; nlinarith
    exact lt_of_mul_lt_mul_right this hρpos.le
  have hnρ : 8 ≤ (n : ℝ) / (2 * ρ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hQp : 2 * p + 2 ≤ Q := by
    have : ((2 * p + 2 : ℕ) : ℝ) < Q + 1 := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  set ℓ := Q - 2 * p with hℓdef
  have hℓr : (ℓ : ℝ) = Q - 2 * p := by
    rw [hℓdef, Nat.cast_sub (by omega)]; push_cast; ring
  have hℓ2 : 2 ≤ ℓ := by omega
  refine ⟨⟨p, ℓ, hp3, hℓ2⟩, ?_, ?_, hρRb, hRb2, ?_⟩
  · change 1 + r * (2 * p + ℓ) ≤ n
    have : 2 * p + ℓ = Q := by omega
    rw [this, Nat.mul_comm r Q]; omega
  · change ℓ ≤ n
    have : Q ≤ n - 1 := by
      calc Q = Q * 1 := (mul_one Q).symm
        _ ≤ Q * r := Nat.mul_le_mul_left _ (by omega)
        _ ≤ n - 1 := hQ1
    omega
  · change (n : ℝ) / (2 * ((2 ^ p : ℕ) : ℝ)) ≤ (ℓ : ℝ) - 1
    rw [hℓr]
    have : ((2 ^ p : ℕ) : ℝ) = ρ := rfl
    rw [this]; linarith

theorem log_M0_le (P : Prm) {n : ℕ} (hℓn : P.ℓ ≤ n) :
    Real.log (P.M0 : ℝ) ≤ Real.log 2 + 2 * (P.r : ℝ) ^ 2 * Real.log (2 * n) := by
  have hℓ : (2 : ℝ) ≤ P.ℓ := by exact_mod_cast P.hℓ
  have hc : ((P.M0 : ℕ) : ℝ) = 2 * (2 * (P.ℓ : ℝ)) ^ (2 * P.W) := by unfold Prm.M0; push_cast; rfl
  rw [hc, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h1 : Real.log (2 * (P.ℓ : ℝ)) ≤ Real.log (2 * n) :=
    Real.log_le_log (by positivity) (by have : (P.ℓ : ℝ) ≤ n := by exact_mod_cast hℓn
                                        linarith)
  have h0 : 0 ≤ Real.log (2 * (P.ℓ : ℝ)) := Real.log_nonneg (by linarith)
  have hW : ((2 * P.W : ℕ) : ℝ) = 2 * (P.r : ℝ) ^ 2 := by push_cast; rw [P.cast_W]; ring
  rw [hW]
  have : 0 ≤ 2 * (P.r : ℝ) ^ 2 := by positivity
  nlinarith

theorem M0_pos (P : Prm) : 0 < P.M0 := by
  unfold Prm.M0; have := P.hℓ; positivity

theorem nat_le_of_log_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log (a : ℝ) ≤ Real.log (b : ℝ)) : a ≤ b := by
  have := (Real.log_le_log_iff (by exact_mod_cast ha) (by exact_mod_cast hb)).mp h
  exact_mod_cast this

theorem nat_le_floor_exp_of_log_le {a : ℕ} (ha : 0 < a) {x : ℝ} (h : Real.log (a : ℝ) ≤ x) :
    a ≤ ⌊Real.exp x⌋₊ := by
  apply Nat.le_floor
  rw [← Real.exp_log (by exact_mod_cast ha : (0 : ℝ) < a)]
  exact Real.exp_le_exp.mpr h

theorem sqrt_le_self_of_one_le {L : ℝ} (hL : 1 ≤ L) : Real.sqrt L ≤ L := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

theorem sqrt_div_four {H L : ℝ} (hL : 0 < L) :
    Real.sqrt (H / (4 * L)) = Real.sqrt H / (2 * Real.sqrt L) := by
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

theorem rpow_three_halves {n : ℝ} (hn : 0 < n) : n ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `eq:pw-expn`, left inequality, with the explicit constant `2^{-19}`: for every
`n ≥ 4096` there is a class of at most `⌊eⁿ⌋` distributions on `n` bits (the padded table
class with `r` the largest power of two at most `√(n/(4 log(2n)))`) on which every algorithm
solving the class at error `1/16` in the pointwise model with cap `q` has
`q ≥ 2^{-19} n^{3/2} / √(log(2n))`. -/
theorem pw_expn_lower (n : ℕ) (hn : 4096 ≤ n) :
    ∃ F : Finset (Str n → ℝ), F.card ≤ ⌊Real.exp n⌋₊ ∧ (∀ μ ∈ F, IsDist μ) ∧
      ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
        (n : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt (Real.log (2 * n))) ≤ q := by
  have hnr : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log (2 * (n : ℝ)) with hLdef
  have hL1 : 1 ≤ L := one_le_log_two_mul (by linarith)
  have hLpos : 0 < L := by linarith
  have h256 : 256 * L ≤ n := log_bound_4096 hnr
  set Rb := Real.sqrt ((n : ℝ) / (4 * L)) with hRbdef
  have hRbsq : Rb ^ 2 = n / (4 * L) := Real.sq_sqrt (by positivity)
  have hRb0 : 0 ≤ Rb := Real.sqrt_nonneg _
  have h8 : 8 ≤ Rb := by
    rw [hRbdef, show (8 : ℝ) = Real.sqrt (8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ (by positivity)]; linarith
  have hRb : Rb ≤ n / (16 * L) := by
    have hpos : 0 < (n : ℝ) / (16 * L) := by positivity
    rw [← Real.sqrt_sq hpos.le, hRbdef]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h64 : 64 * L ≤ n := by linarith
    have := mul_le_mul_of_nonneg_left h64 (by positivity : (0 : ℝ) ≤ 4 * n * L)
    nlinarith
  obtain ⟨P, hN, hℓn, hrRb, hRbr, hℓ1⟩ := choose_params (by omega) h8 hRb
  refine ⟨P.padClass n hN, ?_, fun μ hμ => P.padClass_isDist hμ, fun q A hA => ?_⟩
  · refine (P.card_padClass_le n hN).trans (nat_le_floor_exp_of_log_le (M0_pos P) ?_)
    have h1 := log_M0_le P hℓn
    have hr2 : (P.r : ℝ) ^ 2 ≤ n / (4 * L) := by
      rw [← hRbsq]; exact pow_le_pow_left₀ (by positivity) hrRb 2
    have : 2 * (P.r : ℝ) ^ 2 * L ≤ n / 2 := by
      have := mul_le_mul_of_nonneg_right hr2 (by linarith : (0 : ℝ) ≤ 2 * L)
      have e : (n : ℝ) / (4 * L) * (2 * L) = n / 2 := by field_simp; ring
      nlinarith
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  · have hq := ((P.pw_thm_parameter n hN).2.2 q A hA)
    have hr : (0 : ℝ) < P.r := by have := P.cast_r_ge; linarith
    have hstep : (n : ℝ) * P.r / 2 ^ 17 ≤ ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 := by
      have := mul_le_mul_of_nonneg_right hℓ1 (by positivity : (0 : ℝ) ≤ (P.r : ℝ) ^ 2)
      have e : (n : ℝ) / (2 * P.r) * (P.r : ℝ) ^ 2 = n * P.r / 2 := by field_simp
      rw [e] at this
      have : (n : ℝ) * P.r / 2 ^ 17 = n * P.r / 2 / 2 ^ 16 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hnR : (n : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt L) = n * Rb / 2 ^ 18 := by
      rw [rpow_three_halves (by positivity), hRbdef, sqrt_div_four hLpos]
      have : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
      field_simp
    rw [hnR]
    have : (n : ℝ) * Rb / 2 ^ 18 ≤ n * P.r / 2 ^ 17 := by
      have : (n : ℝ) * Rb ≤ n * (2 * P.r) := mul_le_mul_of_nonneg_left (by linarith)
        (Nat.cast_nonneg n)
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith

/-- `K(n,M) = min{M, n √(log M), n²}` of `eq:K`. -/
noncomputable def Kfun (n M : ℕ) : ℝ := min (min (M : ℝ) (n * Real.sqrt (Real.log M))) ((n : ℝ) ^ 2)

theorem Kfun_le_M (n M : ℕ) : Kfun n M ≤ M := (min_le_left _ _).trans (min_le_left _ _)

theorem Kfun_le_nH (n M : ℕ) : Kfun n M ≤ n * Real.sqrt (Real.log M) :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem Kfun_le_nsq (n M : ℕ) : Kfun n M ≤ (n : ℝ) ^ 2 := min_le_right _ _

theorem Kfun_nonneg {n M : ℕ} (hM : 1 ≤ M) : 0 ≤ Kfun n M := by
  unfold Kfun
  have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  apply le_min (le_min (by positivity) (by positivity)) (by positivity)

/-- `thm:pointwise`, `eq:pw-main` (left inequality), in the "every
valid algorithm" form, with `c₀ = 2^{-22}`: for all `n, M ≥ 2` there is a class of at most `M`
distributions on `n` bits such that every algorithm solving it at error `1/16` in the pointwise
model with cap `q` satisfies `(c₀ / log(2n)) K(n,M) ≤ q`. -/
theorem pw_main_lower (n M : ℕ) (hn : 2 ≤ n) (hM : 2 ≤ M) :
    ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
      ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
        1 / 2 ^ 22 / Real.log (2 * n) * Kfun n M ≤ q := by
  set L := Real.log (2 * (n : ℝ)) with hLdef
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := one_le_log_two_mul hn2
  have hLpos : 0 < L := by linarith
  set H := Real.log (M : ℝ) with hHdef
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hH0 : 0 < H := Real.log_pos (by linarith)
  have hK0 := Kfun_nonneg (n := n) (by omega : 1 ≤ M)
  have hsL := sqrt_le_self_of_one_le hL1
  have hsLpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  -- the comb class bound, used in two cases
  obtain ⟨Fc, hFc1, hFc2, hFc3⟩ := Comb.pw_lem_comb n M hn hM
  by_cases hn1024 : 1024 ≤ n
  · have hnr : (1024 : ℝ) ≤ n := by exact_mod_cast hn1024
    have h128 : 128 * L ≤ n := log_bound_1024 hnr
    set A0 := Real.sqrt (H / (4 * L)) with hA0
    set B0 := (n : ℝ) / (16 * L) with hB0
    have hB8 : 8 ≤ B0 := by rw [hB0, le_div_iff₀ (by positivity)]; linarith
    by_cases hR : 8 ≤ min A0 B0
    · -- the table construction
      obtain ⟨P, hN, hℓn, hrRb, hRbr, hℓ1⟩ := choose_params hn hR (min_le_right _ _)
      have hA8 : 8 ≤ A0 := hR.trans (min_le_left _ _)
      have hH256 : 256 * L ≤ H := by
        have h := Real.sq_sqrt (show 0 ≤ H / (4 * L) by positivity)
        rw [← hA0] at h
        have : (64 : ℝ) ≤ H / (4 * L) := by nlinarith
        rw [le_div_iff₀ (by positivity)] at this; linarith
      refine ⟨P.padClass n hN, ?_, fun μ hμ => P.padClass_isDist hμ, fun q A hA => ?_⟩
      · refine (P.card_padClass_le n hN).trans (nat_le_of_log_le (M0_pos P) (by omega) ?_)
        have h1 := log_M0_le P hℓn
        have hr2 : (P.r : ℝ) ^ 2 ≤ H / (4 * L) := by
          have := (pow_le_pow_left₀ (by positivity) (hrRb.trans (min_le_left _ _)) 2)
          rwa [hA0, Real.sq_sqrt (by positivity)] at this
        have : 2 * (P.r : ℝ) ^ 2 * L ≤ H / 2 := by
          have := mul_le_mul_of_nonneg_right hr2 (by linarith : (0 : ℝ) ≤ 2 * L)
          have e : H / (4 * L) * (2 * L) = H / 2 := by field_simp; ring
          nlinarith
        have := Real.log_two_lt_d9
        norm_num at this
        rw [← hHdef]; linarith
      · have hq := ((P.pw_thm_parameter n hN).2.2 q A hA)
        have hr : (0 : ℝ) < P.r := by have := P.cast_r_ge; linarith
        have hstep : (n : ℝ) * P.r / 2 ^ 17 ≤ ((P.ℓ : ℝ) - 1) * (P.r : ℝ) ^ 2 / 2 ^ 16 := by
          have := mul_le_mul_of_nonneg_right hℓ1 (by positivity : (0 : ℝ) ≤ (P.r : ℝ) ^ 2)
          have e : (n : ℝ) / (2 * P.r) * (P.r : ℝ) ^ 2 = n * P.r / 2 := by field_simp
          rw [e] at this
          have : (n : ℝ) * P.r / 2 ^ 17 = n * P.r / 2 / 2 ^ 16 := by ring
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
        -- K/L ≤ 16 n R_*
        have hKA : Kfun n M / L ≤ 16 * n * A0 := by
          rw [hA0, sqrt_div_four hLpos, div_le_iff₀ hLpos]
          have h1 := Kfun_le_nH n M
          have e : 16 * (n : ℝ) * (Real.sqrt H / (2 * Real.sqrt L)) * L =
              8 * n * Real.sqrt H * (L / Real.sqrt L) := by field_simp; norm_num
          rw [e]
          have hLs : 1 ≤ L / Real.sqrt L := by rw [le_div_iff₀ hsLpos]; linarith
          have : 0 ≤ (n : ℝ) * Real.sqrt H := by positivity
          nlinarith
        have hKB : Kfun n M / L ≤ 16 * n * B0 := by
          rw [hB0, div_le_iff₀ hLpos]
          have h1 := Kfun_le_nsq n M
          have e : 16 * (n : ℝ) * (n / (16 * L)) * L = (n : ℝ) ^ 2 := by field_simp
          rw [e]; exact h1
        have hKR : Kfun n M / L ≤ 16 * n * min A0 B0 := by
          rw [mul_min_of_nonneg _ _ (by positivity)]; exact le_min hKA hKB
        have hRr : min A0 B0 ≤ 2 * P.r := by linarith
        have : 1 / 2 ^ 22 / L * Kfun n M = (Kfun n M / L) / 2 ^ 22 := by ring
        rw [this]
        have h3 : (Kfun n M / L) / 2 ^ 22 ≤ 16 * n * (2 * P.r) / 2 ^ 22 :=
          div_le_div_of_nonneg_right (hKR.trans (mul_le_mul_of_nonneg_left hRr
            (by positivity))) (by norm_num)
        have h4 : 16 * (n : ℝ) * (2 * P.r) / 2 ^ 22 = n * P.r / 2 ^ 17 := by ring
        linarith
    · -- R_* < 8: the comb class
      have hA8 : A0 < 8 := by
        by_contra hc; exact hR (le_min (le_of_not_gt hc) hB8)
      have hH256 : H < 256 * L := by
        have h := Real.sq_sqrt (show 0 ≤ H / (4 * L) by positivity)
        rw [← hA0] at h
        have : H / (4 * L) < 64 := by nlinarith [Real.sqrt_nonneg (H / (4 * L))]
        rw [div_lt_iff₀ (by positivity)] at this; linarith
      refine ⟨Fc, hFc1, hFc2, fun q A hA => ?_⟩
      have hq := hFc3 q A hA
      have : 1 / 2 ^ 22 / L * Kfun n M = (Kfun n M / L) / 2 ^ 22 := by ring
      rw [this]
      by_cases hMn : M ≤ n
      · rw [Nat.min_eq_left hMn] at hq
        have h1 : Kfun n M / L ≤ M :=
          (div_le_self hK0 hL1).trans (Kfun_le_M n M)
        have : (M : ℝ) / 2 ^ 22 ≤ 3 / 16 * M := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith
        have := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 ^ 22)
        linarith
      · rw [Nat.min_eq_right (by omega)] at hq
        have hsH : Real.sqrt H ≤ 16 * Real.sqrt L := by
          rw [show (16 : ℝ) * Real.sqrt L = Real.sqrt (256 * L) by
            rw [Real.sqrt_mul (by norm_num), show (256 : ℝ) = 16 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt hH256.le
        have h1 : Kfun n M / L ≤ 16 * n := by
          rw [div_le_iff₀ hLpos]
          have := Kfun_le_nH n M
          have : (n : ℝ) * Real.sqrt H ≤ n * (16 * Real.sqrt L) :=
            mul_le_mul_of_nonneg_left hsH (Nat.cast_nonneg n)
          nlinarith
        have := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 ^ 22)
        have : 16 * (n : ℝ) / 2 ^ 22 ≤ 3 / 16 * n := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith
        linarith
  · -- small n
    refine ⟨Fc, hFc1, hFc2, fun q A hA => ?_⟩
    have hq := hFc3 q A hA
    have hmin : (2 : ℝ) ≤ (min M n : ℕ) := by exact_mod_cast le_min hM hn
    have hq1 : (1 : ℝ) ≤ q := by
      have : (0 : ℝ) < q := by nlinarith
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')
    have hn' : (n : ℝ) ≤ 1024 := by exact_mod_cast (by omega : n ≤ 1024)
    have h1 : Kfun n M / L ≤ (n : ℝ) ^ 2 := (div_le_self hK0 hL1).trans (Kfun_le_nsq n M)
    have : 1 / 2 ^ 22 / L * Kfun n M = (Kfun n M / L) / 2 ^ 22 := by ring
    rw [this]
    have h2 : (n : ℝ) ^ 2 ≤ 1024 ^ 2 := pow_le_pow_left₀ (by positivity) hn' 2
    have := div_le_div_of_nonneg_right (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 2 ^ 22)
    norm_num at this
    linarith

/-- `thm:pointwise`: the lower bounds with one absolute constant `c₀ = 2^{-22}`:
the left inequality of `eq:pw-main` for all `n, M ≥ 2`, and the left inequality of `eq:pw-expn`
for all `n ≥ 4096`. -/
theorem thm_pointwise_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ n M : ℕ, 2 ≤ n → 2 ≤ M →
        ∃ F : Finset (Str n → ℝ), F.card ≤ M ∧ (∀ μ ∈ F, IsDist μ) ∧
          ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
            c₀ / Real.log (2 * n) * Kfun n M ≤ q) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ F : Finset (Str n → ℝ), F.card ≤ ⌊Real.exp n⌋₊ ∧ (∀ μ ∈ F, IsDist μ) ∧
          ∀ (q : ℕ) (A : Alg (Str n)), Solves (PwLegal (9 / 4)) ↑F (1 / 16) q A →
            c₀ * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n)) ≤ q := by
  refine ⟨1 / 2 ^ 22, by norm_num, fun n M hn hM => pw_main_lower n M hn hM, 4096,
    fun n hn => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := pw_expn_lower n hn
  refine ⟨F, h1, h2, fun q A hA => ?_⟩
  have := h3 q A hA
  have hL : 0 < Real.sqrt (Real.log (2 * n)) := Real.sqrt_pos.mpr (Real.log_pos (by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith))
  have hpos : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  calc 1 / 2 ^ 22 * (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (Real.log (2 * n))
      ≤ (n : ℝ) ^ ((3 : ℝ) / 2) / (2 ^ 19 * Real.sqrt (Real.log (2 * n))) := by
        rw [div_le_div_iff₀ hL (by positivity)]
        nlinarith
    _ ≤ (q : ℝ) := this

end Regimes

end LearningGuided.PointwiseLB
