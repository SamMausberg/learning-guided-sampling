import LearningGuided.PointwiseLB.Potential

/-!
# Affinity inequalities on finite and countable sums

Elementary facts used in place of the KL chain rule and Pinsker's inequality:

* `tsum_sqrt_mul_le`: Cauchy–Schwarz for countable sums, `∑ √(a b) ≤ √(∑ a) √(∑ b)` (the
  Hellinger affinity is jointly concave under mixtures);
* `sqrt_three_le`: the same for three terms;
* `bernoulli_affinity`: for `p, p' ∈ [1/4, 3/4]`,
  `1 - √(p p') - √((1-p)(1-p')) ≤ (p - p')²`;
* `event_diff_le_affinity`: for two distributions on a finite set with affinity
  `BC = ∑ √(P Q)`, every event satisfies `P(E) - Q(E) ≤ √(2(1 - BC))` (Le Cam's inequality
  `TV ≤ √(1 - BC²)`).

We also record the Bernoulli divergence bound `kl_bernoulli_le` of `pw-sec:information`.
-/

open scoped BigOperators

namespace LearningGuided.PointwiseLB

theorem sqrt_mul_le_avg {x y lam : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hl : 0 < lam) :
    Real.sqrt (x * y) ≤ (lam * x + y / lam) / 2 := by
  have h1 : Real.sqrt (x * y) = Real.sqrt (lam * x) * Real.sqrt (y / lam) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  rw [h1]
  have := Real.sq_sqrt (show 0 ≤ lam * x by positivity)
  have := Real.sq_sqrt (show 0 ≤ y / lam by positivity)
  nlinarith [sq_nonneg (Real.sqrt (lam * x) - Real.sqrt (y / lam))]

/-- Cauchy–Schwarz for countable sums of nonnegative summable families. -/
theorem tsum_sqrt_mul_le {γ : Type} {a b : γ → ℝ} (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hsa : Summable a) (hsb : Summable b) :
    ∑' x, Real.sqrt (a x * b x) ≤ Real.sqrt (∑' x, a x) * Real.sqrt (∑' x, b x) := by
  have hA : 0 ≤ ∑' x, a x := tsum_nonneg ha
  have hB : 0 ≤ ∑' x, b x := tsum_nonneg hb
  have hsum : ∀ lam : ℝ, 0 < lam → Summable fun x => (lam * a x + b x / lam) / 2 := fun lam _ =>
    ((hsa.mul_left lam).add (hsb.div_const lam)).div_const 2
  have hs : Summable fun x => Real.sqrt (a x * b x) :=
    Summable.of_nonneg_of_le (fun x => Real.sqrt_nonneg _)
      (fun x => sqrt_mul_le_avg (ha x) (hb x) one_pos) (hsum 1 one_pos)
  have key : ∀ lam : ℝ, 0 < lam →
      ∑' x, Real.sqrt (a x * b x) ≤ (lam * ∑' x, a x + (∑' x, b x) / lam) / 2 := by
    intro lam hl
    calc ∑' x, Real.sqrt (a x * b x) ≤ ∑' x, (lam * a x + b x / lam) / 2 :=
          Summable.tsum_le_tsum (fun x => sqrt_mul_le_avg (ha x) (hb x) hl) hs (hsum lam hl)
      _ = (lam * ∑' x, a x + (∑' x, b x) / lam) / 2 := by
          rw [tsum_div_const, Summable.tsum_add (hsa.mul_left lam) (hsb.div_const lam),
            tsum_mul_left, tsum_div_const]
  rcases hA.eq_or_lt with hA0 | hA0
  · have : ∀ x, a x = 0 := fun x =>
      le_antisymm (by rw [hA0]; exact hsa.le_tsum x fun y _ => ha y) (ha x)
    simp [this]
  rcases hB.eq_or_lt with hB0 | hB0
  · have : ∀ x, b x = 0 := fun x =>
      le_antisymm (by rw [hB0]; exact hsb.le_tsum x fun y _ => hb y) (hb x)
    simp [this]
  have hlam : 0 < Real.sqrt (∑' x, b x) / Real.sqrt (∑' x, a x) :=
    div_pos (Real.sqrt_pos.mpr hB0) (Real.sqrt_pos.mpr hA0)
  have := key _ hlam
  have e1 := Real.sq_sqrt hA
  have e2 := Real.sq_sqrt hB
  have hsa' := Real.sqrt_pos.mpr hA0
  have hsb' := Real.sqrt_pos.mpr hB0
  have : (Real.sqrt (∑' x, b x) / Real.sqrt (∑' x, a x) * ∑' x, a x +
      (∑' x, b x) / (Real.sqrt (∑' x, b x) / Real.sqrt (∑' x, a x))) / 2 =
      Real.sqrt (∑' x, a x) * Real.sqrt (∑' x, b x) := by
    field_simp
    nlinarith
  linarith

theorem sqrt_two_le {a1 a2 b1 b2 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1)
    (hb2 : 0 ≤ b2) :
    Real.sqrt (a1 * b1) + Real.sqrt (a2 * b2) ≤ Real.sqrt ((a1 + a2) * (b1 + b2)) := by
  apply Real.le_sqrt_of_sq_le
  have e1 := Real.sq_sqrt (mul_nonneg ha1 hb1)
  have e2 := Real.sq_sqrt (mul_nonneg ha2 hb2)
  have hprod : Real.sqrt (a1 * b1) * Real.sqrt (a2 * b2) = Real.sqrt (a1 * b2 * (a2 * b1)) := by
    rw [← Real.sqrt_mul (mul_nonneg ha1 hb1)]; congr 1; ring
  have hamgm : Real.sqrt (a1 * b2 * (a2 * b1)) ≤ (a1 * b2 + a2 * b1) / 2 := by
    have := sqrt_mul_le_avg (mul_nonneg ha1 hb2) (mul_nonneg ha2 hb1) one_pos
    simpa using this
  nlinarith

theorem sqrt_three_le {a1 a2 a3 b1 b2 b3 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) :
    Real.sqrt (a1 * b1) + Real.sqrt (a2 * b2) + Real.sqrt (a3 * b3) ≤
      Real.sqrt ((a1 + a2 + a3) * (b1 + b2 + b3)) :=
  calc Real.sqrt (a1 * b1) + Real.sqrt (a2 * b2) + Real.sqrt (a3 * b3)
      ≤ Real.sqrt ((a1 + a2) * (b1 + b2)) + Real.sqrt (a3 * b3) := by
        gcongr; exact sqrt_two_le ha1 ha2 hb1 hb2
    _ ≤ Real.sqrt ((a1 + a2 + a3) * (b1 + b2 + b3)) :=
        sqrt_two_le (by positivity) ha3 (by positivity) hb3

theorem sqrt_mul_mul_sqrt {c x y : ℝ} (hc : 0 ≤ c) :
    Real.sqrt (c * x * (c * y)) = c * Real.sqrt (x * y) := by
  rw [show c * x * (c * y) = c ^ 2 * (x * y) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hc]

/-- The per-step Hellinger bound for two Bernoulli laws with parameters in `[1/4, 3/4]`:
`1 - √(p p') - √((1-p)(1-p')) ≤ (p - p')²`. -/
theorem bernoulli_affinity {p p' : ℝ} (hp1 : 1 / 4 ≤ p) (hp2 : p ≤ 3 / 4) (hq1 : 1 / 4 ≤ p')
    (hq2 : p' ≤ 3 / 4) :
    1 - Real.sqrt (p * p') - Real.sqrt ((1 - p) * (1 - p')) ≤ (p - p') ^ 2 := by
  set u := Real.sqrt p
  set u' := Real.sqrt p'
  set v := Real.sqrt (1 - p)
  set v' := Real.sqrt (1 - p')
  have hu : u ^ 2 = p := Real.sq_sqrt (by linarith)
  have hu' : u' ^ 2 = p' := Real.sq_sqrt (by linarith)
  have hv : v ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hv' : v' ^ 2 = 1 - p' := Real.sq_sqrt (by linarith)
  have h1 : Real.sqrt (p * p') = u * u' := Real.sqrt_mul (by linarith) _
  have h2 : Real.sqrt ((1 - p) * (1 - p')) = v * v' := Real.sqrt_mul (by linarith) _
  rw [h1, h2]
  have hu0 : 1 / 2 ≤ u := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp1
  have hu0' : 1 / 2 ≤ u' := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hq1
  have hv0 : 1 / 2 ≤ v := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hv0' : 1 / 2 ≤ v' := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  -- 1 - uu' - vv' = ((u-u')² + (v-v')²)/2 and (u-u')² ≤ (u-u')²(u+u')² = (p-p')²
  have ha : (u - u') ^ 2 ≤ (p - p') ^ 2 := by
    have : (p - p') ^ 2 = (u - u') ^ 2 * (u + u') ^ 2 := by rw [← hu, ← hu']; ring
    rw [this]
    have : 1 ≤ (u + u') ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u - u')]
  have hb : (v - v') ^ 2 ≤ (p - p') ^ 2 := by
    have : (p - p') ^ 2 = (v - v') ^ 2 * (v + v') ^ 2 := by
      have : p - p' = -((v ^ 2) - (v' ^ 2)) := by rw [hv, hv']; ring
      rw [this]; ring
    rw [this]
    have : 1 ≤ (v + v') ^ 2 := by nlinarith
    nlinarith [sq_nonneg (v - v')]
  nlinarith

/-- Le Cam's inequality in event form: for two nonnegative functions on a finite set with total
mass one and affinity `BC = ∑ √(P Q)`, every event satisfies `P(E) - Q(E) ≤ √(2(1 - BC))`. -/
theorem event_diff_le_affinity {α : Type} [Fintype α] {Pf Qf : α → ℝ} (hP : ∀ x, 0 ≤ Pf x)
    (hQ : ∀ x, 0 ≤ Qf x) (hP1 : ∑ x, Pf x = 1) (hQ1 : ∑ x, Qf x = 1) (E : Finset α) :
    ∑ x ∈ E, Pf x - ∑ x ∈ E, Qf x ≤
      Real.sqrt (2 * (1 - ∑ x, Real.sqrt (Pf x * Qf x))) := by
  classical
  set BC := ∑ x, Real.sqrt (Pf x * Qf x)
  have hsq : ∀ x, Real.sqrt (Pf x * Qf x) = Real.sqrt (Pf x) * Real.sqrt (Qf x) := fun x =>
    Real.sqrt_mul (hP x) _
  have hsP : ∀ x, Real.sqrt (Pf x) ^ 2 = Pf x := fun x => Real.sq_sqrt (hP x)
  have hsQ : ∀ x, Real.sqrt (Qf x) ^ 2 = Qf x := fun x => Real.sq_sqrt (hQ x)
  -- the total variation sum
  have habs : ∀ x, |Pf x - Qf x| =
      |Real.sqrt (Pf x) - Real.sqrt (Qf x)| * (Real.sqrt (Pf x) + Real.sqrt (Qf x)) := by
    intro x
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (Pf x) + Real.sqrt (Qf x)), ← abs_mul]
    congr 1; linear_combination (-1 : ℝ) * hsP x + hsQ x
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun x => |Real.sqrt (Pf x) - Real.sqrt (Qf x)|) (fun x => Real.sqrt (Pf x) + Real.sqrt (Qf x))
  simp only [sq_abs] at hcs
  have hm : ∑ x, (Real.sqrt (Pf x) - Real.sqrt (Qf x)) ^ 2 = 2 * (1 - BC) := by
    have : ∀ x, (Real.sqrt (Pf x) - Real.sqrt (Qf x)) ^ 2 =
        Pf x + Qf x - 2 * Real.sqrt (Pf x * Qf x) := fun x => by
      rw [hsq]; nlinarith [hsP x, hsQ x]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hP1, hQ1]
    ring
  have hp : ∑ x, (Real.sqrt (Pf x) + Real.sqrt (Qf x)) ^ 2 = 2 * (1 + BC) := by
    have : ∀ x, (Real.sqrt (Pf x) + Real.sqrt (Qf x)) ^ 2 =
        Pf x + Qf x + 2 * Real.sqrt (Pf x * Qf x) := fun x => by
      rw [hsq]; nlinarith [hsP x, hsQ x]
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hP1, hQ1]
    ring
  have hBC1 : BC ≤ 1 := by
    have : ∀ x, Real.sqrt (Pf x * Qf x) ≤ (Pf x + Qf x) / 2 := fun x => by
      have := sqrt_mul_le_avg (hP x) (hQ x) one_pos; simpa using this
    calc BC ≤ ∑ x, (Pf x + Qf x) / 2 := Finset.sum_le_sum fun x _ => this x
      _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hP1, hQ1]; norm_num
  have hBC0 : 0 ≤ BC := Finset.sum_nonneg fun x _ => Real.sqrt_nonneg _
  have htv : ∑ x, |Pf x - Qf x| ≤ 2 * Real.sqrt (2 * (1 - BC)) := by
    rw [Finset.sum_congr rfl fun x _ => habs x]
    refine hcs.trans ?_
    rw [hm, hp]
    have : Real.sqrt (2 * (1 + BC)) ≤ 2 :=
      calc Real.sqrt (2 * (1 + BC)) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 := Real.sqrt_sq (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 * (1 - BC))]
  -- events
  have hsplit : ∀ f : α → ℝ, ∑ x, f x = ∑ x ∈ E, f x + ∑ x ∈ Eᶜ, f x := fun f => by
    rw [Finset.sum_add_sum_compl]
  have h1 : ∑ x ∈ E, (Pf x - Qf x) = ∑ x ∈ Eᶜ, (Qf x - Pf x) := by
    have := hsplit Pf; have := hsplit Qf
    simp only [Finset.sum_sub_distrib]; linarith
  have h2 : ∑ x ∈ E, (Pf x - Qf x) ≤ ∑ x ∈ E, |Pf x - Qf x| :=
    Finset.sum_le_sum fun x _ => le_abs_self _
  have h3 : ∑ x ∈ Eᶜ, (Qf x - Pf x) ≤ ∑ x ∈ Eᶜ, |Pf x - Qf x| :=
    Finset.sum_le_sum fun x _ => by rw [abs_sub_comm]; exact le_abs_self _
  have h4 := hsplit fun x => |Pf x - Qf x|
  simp only [Finset.sum_sub_distrib] at h1 h2 h3
  linarith

/-- `pw-lem:information`, Bernoulli divergence bound: from `log x ≤ x - 1`,
`KL(Ber(p) ‖ Ber(p')) ≤ (p - p')² / (p'(1-p'))`; with `p, p' ∈ [1/4, 3/4]` and
`|p - p'| < 3/r`, this is at most `48/W ≤ 64/W`. -/
theorem kl_bernoulli_le {p p' : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < p') (hq1 : p' < 1) :
    p * Real.log (p / p') + (1 - p) * Real.log ((1 - p) / (1 - p')) ≤
      (p - p') ^ 2 / (p' * (1 - p')) := by
  have e1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have e2 := Real.log_le_sub_one_of_pos
    (div_pos (by linarith : 0 < 1 - p) (by linarith : 0 < 1 - p'))
  have h1 : p * Real.log (p / p') ≤ p * (p / p' - 1) := mul_le_mul_of_nonneg_left e1 hp0.le
  have h2 : (1 - p) * Real.log ((1 - p) / (1 - p')) ≤ (1 - p) * ((1 - p) / (1 - p') - 1) :=
    mul_le_mul_of_nonneg_left e2 (by linarith)
  have h3 : p * (p / p' - 1) + (1 - p) * ((1 - p) / (1 - p') - 1) =
      (p - p') ^ 2 / (p' * (1 - p')) := by
    have : (1 - p') ≠ 0 := by linarith
    field_simp; ring
  linarith

/-- `pw-lem:information`, numeric Bernoulli bound: `p, p' ∈ [1/4, 3/4]` and `|p - p'| ≤ 3/r` give a
Bernoulli divergence at most `48/W ≤ 64/W` with `W = r²`. -/
theorem kl_bernoulli_numeric {p p' r : ℝ} (hr : 0 < r) (hq1 : 1 / 4 ≤ p') (hq2 : p' ≤ 3 / 4)
    (hd : |p - p'| ≤ 3 / r) : (p - p') ^ 2 / (p' * (1 - p')) ≤ 48 / r ^ 2 ∧
      48 / r ^ 2 ≤ 64 / r ^ 2 := by
  have hpq : 3 / 16 ≤ p' * (1 - p') := by nlinarith
  have hsq : (p - p') ^ 2 ≤ 9 / r ^ 2 := by
    have := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
    calc (p - p') ^ 2 ≤ (3 / r) ^ 2 := this
      _ = 9 / r ^ 2 := by ring
  refine ⟨?_, by gcongr; norm_num⟩
  rw [div_le_iff₀ (by linarith)]
  calc (p - p') ^ 2 ≤ 9 / r ^ 2 := hsq
    _ = 48 / r ^ 2 * (3 / 16) := by ring
    _ ≤ 48 / r ^ 2 * (p' * (1 - p')) := by gcongr

end LearningGuided.PointwiseLB
