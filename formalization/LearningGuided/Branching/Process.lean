import LearningGuided.Branching.Poisson

/-!
# The Poisson branching process against a fixed guide

Against a fixed guide `h`, a particle at a nonleaf `u` has, independently for each `b`, a Poisson
number of children at `ub` with mean `h(ub)/h(u)`. A population is the list of particle positions.

* `genP h pop` is the law of the next generation of the population `pop`.
* `levelsP h t pop` is the joint law of the population after `t` generations and of the number of
  guide queries made (two per processed particle).
* `lin c pop = ∑_{particles} c(position)` is a linear functional of the population; one generation
  maps its mean to `lin (pull c)` and its second moment to `lin (pull c)² + lin (pull (c²))`
  (`expect_genP_lin`, `expect_genP_sq`).

Under the hypotheses of `thm:branching` (`BranchHyp`), starting from `P` particles at the root,
we prove `E N(u) = P h(u)` (`expect_levelsP_lin`, the root-pooled form of `E N(u) = h(u)`), the
martingale second-moment identity `E Z_t² = P² + P ∑_{s ≤ t} ∑_{|v|=s} μ(v)²/h(v)`
(`expect_levelsP_Zsq`), and the expected query count `2 P ∑_{t<n} ∑_{|u|=t} h(u)`
(`expect_levelsP_count`).
-/

open scoped BigOperators ENNReal NNReal

namespace LearningGuided
namespace Branching

open Upper

/-! ### Words of consecutive lengths -/

theorem append_singleton_inj {w w' : List Bool} {b b' : Bool} (h : w ++ [b] = w' ++ [b']) :
    w = w' ∧ b = b' := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

/-- Summing over words of length `t+1` is summing over words of length `t` and a last bit. -/
theorem sum_words_succ {M : Type} [AddCommMonoid M] (t : ℕ) (f : List Bool → M) :
    ∑ v ∈ words (t + 1), f v = ∑ w ∈ words t, (f (w ++ [false]) + f (w ++ [true])) := by
  classical
  have himg : words (t + 1) = (words t ×ˢ (Finset.univ : Finset Bool)).image
      (fun wb => wb.1 ++ [wb.2]) := by
    ext v
    simp only [mem_words, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
      Prod.exists]
    constructor
    · intro hv
      refine ⟨v.dropLast, v.getLast (List.ne_nil_of_length_pos (by omega)), ?_, ?_⟩
      · simp [hv]
      · exact List.dropLast_append_getLast _
    · rintro ⟨w, b, hw, rfl⟩
      simp [hw]
  rw [himg, Finset.sum_image, Finset.sum_product]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_bool, add_comm]
  · intro x _ y _ hxy
    obtain ⟨h1, h2⟩ := append_singleton_inj hxy
    exact Prod.ext h1 h2

/-- `∑_x 1{w = x} g(w) = 1{|w| = n} g(w)`. -/
theorem sum_ite_ofFn_eq {n : ℕ} {M : Type} [AddCommMonoid M] (w : List Bool) (g : M) :
    ∑ x : Str n, (if w = List.ofFn x then g else 0) = if w.length = n then g else 0 := by
  classical
  by_cases hw : w.length = n
  · rw [ite_eq_left hw]
    set y : Str n := fun i => w[i.1]'(by omega) with hy
    have hwy : w = List.ofFn y := by
      apply List.ext_getElem (by simp [hw])
      intro i h1 h2
      simp [hy]
    rw [Finset.sum_eq_single y]
    · rw [ite_eq_left hwy]
    · intro x _ hxy
      rw [ite_eq_right]
      intro hx
      exact hxy (List.ofFn_injective (hx.symm.trans hwy))
    · simp
  · rw [ite_eq_right hw]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [ite_eq_right]
    intro hx
    exact hw (by rw [hx]; simp)

/-! ### Linear functionals of populations -/

/-- `lin c pop = ∑_{particles p} c(p)`. -/
noncomputable def lin (c : List Bool → ℝ≥0∞) (pop : List (List Bool)) : ℝ≥0∞ := (pop.map c).sum

@[simp] theorem lin_nil (c : List Bool → ℝ≥0∞) : lin c [] = 0 := rfl

@[simp] theorem lin_cons (c : List Bool → ℝ≥0∞) (u : List Bool) (pop : List (List Bool)) :
    lin c (u :: pop) = c u + lin c pop := by simp [lin]

theorem lin_append (c : List Bool → ℝ≥0∞) (p q : List (List Bool)) :
    lin c (p ++ q) = lin c p + lin c q := by simp [lin]

theorem lin_replicate (c : List Bool → ℝ≥0∞) (k : ℕ) (w : List Bool) :
    lin c (List.replicate k w) = k * c w := by
  simp [lin, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

theorem lin_add (c d : List Bool → ℝ≥0∞) (pop : List (List Bool)) :
    lin (fun w => c w + d w) pop = lin c pop + lin d pop := by
  induction pop with
  | nil => simp
  | cons u pop ih => simp only [lin_cons, ih]; ring

theorem lin_finset_sum {ι : Type} (s : Finset ι) (c : ι → List Bool → ℝ≥0∞)
    (pop : List (List Bool)) : lin (fun w => ∑ i ∈ s, c i w) pop = ∑ i ∈ s, lin (c i) pop := by
  induction pop with
  | nil => simp
  | cons u pop ih => simp only [lin_cons, ih, Finset.sum_add_distrib]

theorem lin_congr {c d : List Bool → ℝ≥0∞} {pop : List (List Bool)}
    (h : ∀ w ∈ pop, c w = d w) : lin c pop = lin d pop := by
  unfold lin
  rw [List.map_congr_left h]

theorem lin_const_one (pop : List (List Bool)) : lin (fun _ => 1) pop = pop.length := by
  induction pop with
  | nil => simp
  | cons u pop ih => simp only [lin_cons, ih, List.length_cons]; push_cast; ring

theorem lin_indicator (a : List Bool) (pop : List (List Bool)) :
    lin (fun w => if w = a then 1 else 0) pop = pop.count a := by
  induction pop with
  | nil => simp
  | cons u pop ih =>
      rw [lin_cons, ih, List.count_cons]
      by_cases hu : u = a <;> simp [hu, add_comm]

theorem lin_eq_zero {c : List Bool → ℝ≥0∞} {pop : List (List Bool)} (h : lin c pop = 0) :
    ∀ w ∈ pop, c w = 0 := by
  induction pop with
  | nil => simp
  | cons u pop ih =>
      rw [lin_cons, add_eq_zero] at h
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h.1
      · exact ih h.2 w hw

/-! ### One generation -/

variable (h : Guide)

/-- Offspring mean `h(ub)/h(u)` at the child `ub` of a particle at `u`. -/
noncomputable def lam (u : List Bool) (b : Bool) : ℝ≥0 := (h (u ++ [b]) / h u).toNNReal

/-- The positions of the children of a particle at `u` with offspring numbers `K`. -/
def kids (u : List Bool) (K : ℕ × ℕ) : List (List Bool) :=
  List.replicate K.1 (u ++ [false]) ++ List.replicate K.2 (u ++ [true])

/-- The offspring numbers of one particle at `u`: independent Poisson draws for the two
children. -/
noncomputable def offspring (u : List Bool) : PMF (ℕ × ℕ) :=
  (poisPMF (lam h u false)).bind fun K0 => (poisPMF (lam h u true)).bind fun K1 =>
    PMF.pure (K0, K1)

/-- One generation: every particle of `pop` reproduces independently. -/
noncomputable def genP : List (List Bool) → PMF (List (List Bool))
  | [] => PMF.pure []
  | u :: rest => (offspring h u).bind fun K => (genP rest).map fun p => kids u K ++ p

/-- The joint law of the population after `t` generations and the number of queries made. -/
noncomputable def levelsP : ℕ → List (List Bool) → PMF (List (List Bool) × ℕ)
  | 0, pop => PMF.pure (pop, 0)
  | t + 1, pop => (levelsP t pop).bind fun pc =>
      (genP h pc.1).map fun p => (p, pc.2 + 2 * pc.1.length)

/-- The pulled-back coefficient: `pull c (u) = ∑_b c(ub) h(ub)/h(u)`. -/
noncomputable def pull (c : List Bool → ℝ≥0∞) (u : List Bool) : ℝ≥0∞ :=
  c (u ++ [false]) * lam h u false + c (u ++ [true]) * lam h u true

theorem lin_kids (c : List Bool → ℝ≥0∞) (u : List Bool) (K : ℕ × ℕ) :
    lin c (kids u K) = K.1 * c (u ++ [false]) + K.2 * c (u ++ [true]) := by
  simp [kids, lin_append, lin_replicate]

theorem expect_offspring_lin (u : List Bool) (a b : ℝ≥0∞) :
    expect (offspring h u) (fun K => K.1 * a + K.2 * b) = a * lam h u false + b * lam h u true := by
  unfold offspring
  simp only [expect_bind, expect_pure]
  simp_rw [expect_add, expect_const, expect_mul_const, expect_poisPMF_id]
  ring

theorem expect_offspring_sq (u : List Bool) (a b : ℝ≥0∞) :
    expect (offspring h u) (fun K => (K.1 * a + K.2 * b) ^ 2) =
      (a * lam h u false + b * lam h u true) ^ 2 +
        (a ^ 2 * lam h u false + b ^ 2 * lam h u true) := by
  unfold offspring
  simp only [expect_bind, expect_pure]
  have e1 : ∀ K0 : ℕ, expect (poisPMF (lam h u true))
      (fun K1 => ((K0 : ℝ≥0∞) * a + K1 * b) ^ 2) =
      (K0 : ℝ≥0∞) ^ 2 * a ^ 2 + 2 * a * b * lam h u true * K0 +
        b ^ 2 * (lam h u true + (lam h u true : ℝ≥0∞) ^ 2) := by
    intro K0
    have : ∀ K1 : ℕ, ((K0 : ℝ≥0∞) * a + K1 * b) ^ 2 =
        (K0 : ℝ≥0∞) ^ 2 * a ^ 2 + (2 * a * b * K0) * (K1 : ℝ≥0∞) + b ^ 2 * (K1 : ℝ≥0∞) ^ 2 :=
      fun K1 => by ring
    simp_rw [this, expect_add, expect_const, expect_const_mul, expect_poisPMF_id,
      expect_poisPMF_sq]
    ring
  simp_rw [e1, expect_add, expect_const, expect_mul_const, expect_const_mul, expect_poisPMF_id,
    expect_poisPMF_sq]
  ring

/-- One generation maps the mean of `lin c` to `lin (pull c)`. -/
theorem expect_genP_lin (c : List Bool → ℝ≥0∞) :
    ∀ pop, expect (genP h pop) (lin c) = lin (pull h c) pop
  | [] => by simp [genP, expect_pure]
  | u :: rest => by
      simp only [genP, expect_bind, expect_map, Function.comp_def, lin_append, lin_kids]
      have e1 : ∀ K : ℕ × ℕ, expect (genP h rest)
          (fun p => (K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true]) + lin c p) =
          (K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true]) + lin (pull h c) rest :=
        fun K => by rw [expect_add, expect_const, expect_genP_lin c rest]
      simp_rw [e1]
      rw [expect_add, expect_const, expect_offspring_lin, lin_cons, pull]

/-- One generation maps the second moment of `lin c` to `lin (pull c)² + lin (pull c²)`. -/
theorem expect_genP_sq (c : List Bool → ℝ≥0∞) :
    ∀ pop, expect (genP h pop) (fun p => lin c p ^ 2) =
      lin (pull h c) pop ^ 2 + lin (pull h fun w => c w ^ 2) pop
  | [] => by simp [genP, expect_pure]
  | u :: rest => by
      simp only [genP, expect_bind, expect_map, Function.comp_def, lin_append, lin_kids]
      have e1 : ∀ K : ℕ × ℕ, expect (genP h rest)
          (fun p => ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true]) + lin c p) ^ 2) =
          ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])) ^ 2 +
            2 * ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])) *
              lin (pull h c) rest +
            (lin (pull h c) rest ^ 2 + lin (pull h fun w => c w ^ 2) rest) := by
        intro K
        set X := (K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])
        have : ∀ p, (X + lin c p) ^ 2 = X ^ 2 + (2 * X) * lin c p + lin c p ^ 2 :=
          fun p => by ring
        simp_rw [this, expect_add, expect_const, expect_const_mul, expect_genP_lin,
          expect_genP_sq c rest]
      simp_rw [e1]
      rw [expect_add, expect_add, expect_const, expect_offspring_sq]
      have e2 : expect (offspring h u) (fun K =>
          2 * ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])) * lin (pull h c) rest) =
          2 * (c (u ++ [false]) * lam h u false + c (u ++ [true]) * lam h u true) *
            lin (pull h c) rest := by
        have : ∀ K : ℕ × ℕ, 2 * ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])) *
            lin (pull h c) rest = (2 * lin (pull h c) rest) *
              ((K.1 : ℝ≥0∞) * c (u ++ [false]) + K.2 * c (u ++ [true])) := fun K => by ring
        simp_rw [this, expect_const_mul, expect_offspring_lin]
        ring
      rw [e2, lin_cons, lin_cons, pull, pull]
      ring

/-! ### Moments under the hypotheses of `thm:branching` -/

variable {h}

/-- The hypotheses of `thm:branching` on the target and the guide: `μ` is a distribution, the
guide is nonnegative with `h(∅) = 1`, has the same support as `μ` at every prefix, and its leaves
are exact. -/
structure BranchHyp {n : ℕ} (μ : Str n → ℝ) (h : Guide) : Prop where
  dist : IsDist μ
  nonneg : ∀ u, 0 ≤ h u
  root : h [] = 1
  supp : ∀ u : List Bool, u.length ≤ n → (h u = 0 ↔ mass μ u = 0)
  leaf : ∀ x : Str n, h (List.ofFn x) = μ x

variable {n : ℕ} {μ : Str n → ℝ}

theorem words_zero : words 0 = {[]} := by
  ext w
  simp [mem_words, List.length_eq_zero_iff]

theorem BranchHyp.child_zero (H : BranchHyp μ h) {u : List Bool} (hu : u.length < n)
    (h0 : h u = 0) (b : Bool) : h (u ++ [b]) = 0 := by
  have hm : mass μ u = 0 := (H.supp u hu.le).mp h0
  have hc := mass_children μ hu
  have h1 := mass_nonneg H.dist.1 (u ++ [false])
  have h2 := mass_nonneg H.dist.1 (u ++ [true])
  refine (H.supp (u ++ [b]) (by simp; omega)).mpr ?_
  cases b <;> linarith

theorem BranchHyp.lam_mul (H : BranchHyp μ h) {u : List Bool} (hu : u.length < n) (b : Bool) :
    (lam h u b : ℝ≥0∞) * ENNReal.ofReal (h u) = ENNReal.ofReal (h (u ++ [b])) := by
  rw [lam, ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul (div_nonneg (H.nonneg _) (H.nonneg _))]
  rcases eq_or_ne (h u) 0 with h0 | h0
  · rw [h0, H.child_zero hu h0 b, mul_zero]
  · rw [div_mul_cancel₀ _ h0]

theorem BranchHyp.pull_sum (H : BranchHyp μ h) {t : ℕ} (ht : t < n) (c : List Bool → ℝ≥0∞) :
    ∑ w ∈ words t, pull h c w * ENNReal.ofReal (h w) =
      ∑ v ∈ words (t + 1), c v * ENNReal.ofReal (h v) := by
  rw [sum_words_succ]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwl : w.length < n := by rw [mem_words.mp hw]; exact ht
  rw [pull, add_mul, mul_assoc, mul_assoc, H.lam_mul hwl, H.lam_mul hwl]

theorem BranchHyp.leaf_mass (H : BranchHyp μ h) {w : List Bool} (hw : w.length = n) :
    h w = mass μ w := by
  set y : Str n := fun i => w[i.1]'(by omega) with hy
  have hwy : w = List.ofFn y := by
    apply List.ext_getElem (by simp [hw])
    intro i h1 h2
    simp [hy]
  rw [hwy, H.leaf, mass_ofFn]

/-- `E N(u) = P h(u)`: the mean of every linear functional of the depth-`t` population started
from `P` particles at the root. -/
theorem expect_levelsP_lin (H : BranchHyp μ h) (P : ℕ) :
    ∀ t ≤ n, ∀ c : List Bool → ℝ≥0∞,
      expect (levelsP h t (List.replicate P [])) (fun pc => lin c pc.1) =
        P * ∑ w ∈ words t, c w * ENNReal.ofReal (h w)
  | 0, _, c => by
      simp [levelsP, expect_pure, lin_replicate, words_zero, H.root]
  | t + 1, ht, c => by
      simp only [levelsP, expect_bind, expect_map, Function.comp_def, expect_genP_lin]
      rw [expect_levelsP_lin H P t (by omega) (pull h c), H.pull_sum (by omega)]

/-- The normalized martingale coefficient at depth `t`: `z(u) = μ(u)/h(u)` for `|u| = t`. -/
noncomputable def zc (μ : Str n → ℝ) (h : Guide) (t : ℕ) (w : List Bool) : ℝ≥0∞ :=
  if w.length = t then ENNReal.ofReal (mass μ w / h w) else 0

/-- The martingale property: a particle at `u` has expected child contribution `z(u)`. -/
theorem BranchHyp.pull_zc (H : BranchHyp μ h) {t : ℕ} (ht : t < n) :
    pull h (zc μ h (t + 1)) = zc μ h t := by
  ext u
  unfold pull zc
  by_cases hu : u.length = t
  · have hul : u.length < n := by omega
    simp only [List.length_append, List.length_singleton, hu, ↓reduceIte]
    rcases eq_or_ne (h u) 0 with h0 | h0
    · simp [lam, h0]
    · have hpos : 0 < h u := lt_of_le_of_ne (H.nonneg u) (Ne.symm h0)
      have key : ∀ b : Bool, ENNReal.ofReal (mass μ (u ++ [b]) / h (u ++ [b])) * lam h u b =
          ENNReal.ofReal (mass μ (u ++ [b]) / h u) := by
        intro b
        rw [lam, ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul (div_nonneg
          (mass_nonneg H.dist.1 _) (H.nonneg _))]
        rcases eq_or_ne (h (u ++ [b])) 0 with hb | hb
        · have hm : mass μ (u ++ [b]) = 0 := (H.supp _ (by simp; omega)).mp hb
          simp [hm]
        · congr 1
          field_simp
      rw [key, key, ← ENNReal.ofReal_add (div_nonneg (mass_nonneg H.dist.1 _) hpos.le)
        (div_nonneg (mass_nonneg H.dist.1 _) hpos.le), ← add_div, ← mass_children μ hul]
  · have h1 : ¬ (u ++ [false]).length = t + 1 := by simp; omega
    have h2 : ¬ (u ++ [true]).length = t + 1 := by simp; omega
    simp only [h1, h2, hu, ↓reduceIte, zero_mul, add_zero]

/-- The reciprocal term: `z(v)² h(v) = μ(v)²/h(v)`. -/
theorem BranchHyp.zc_sq_mul (H : BranchHyp μ h) {t : ℕ} {v : List Bool} (hv : v.length = t) :
    zc μ h t v ^ 2 * ENNReal.ofReal (h v) = ENNReal.ofReal (mass μ v ^ 2 / h v) := by
  unfold zc
  rw [ite_eq_left hv, ← ENNReal.ofReal_pow (div_nonneg (mass_nonneg H.dist.1 _) (H.nonneg _)),
    ← ENNReal.ofReal_mul (by positivity)]
  rcases eq_or_ne (h v) 0 with h0 | h0
  · simp [h0]
  · congr 1
    field_simp

/-- The martingale variance identity, summed over generations:
`E Z_t² = P² + P ∑_{s=1}^{t} ∑_{|v|=s} μ(v)²/h(v)` for the population started from `P` root
particles, where `Z_t = ∑_{|u|=t} N(u) z(u)`. -/
theorem expect_levelsP_Zsq (H : BranchHyp μ h) (P : ℕ) :
    ∀ t ≤ n, expect (levelsP h t (List.replicate P [])) (fun pc => lin (zc μ h t) pc.1 ^ 2) =
      (P : ℝ≥0∞) ^ 2 + P * ∑ s ∈ Finset.range t, ∑ v ∈ words (s + 1),
        ENNReal.ofReal (mass μ v ^ 2 / h v)
  | 0, _ => by
      have hz : zc μ h 0 [] = 1 := by
        simp [zc, mass_nil, H.dist.2, H.root]
      simp [levelsP, expect_pure, lin_replicate, hz]
  | t + 1, ht => by
      simp only [levelsP, expect_bind, expect_map, Function.comp_def, expect_genP_sq]
      rw [expect_add, H.pull_zc (by omega), expect_levelsP_Zsq H P t (by omega),
        expect_levelsP_lin H P t (by omega), H.pull_sum (by omega), Finset.sum_range_succ,
        mul_add, add_assoc]
      congr 3
      refine Finset.sum_congr rfl fun v hv => ?_
      exact H.zc_sq_mul (mem_words.mp hv)

/-- The expected number of queries: two per processed particle, `2 P ∑_{s<t} ∑_{|u|=s} h(u)`. -/
theorem expect_levelsP_count (H : BranchHyp μ h) (P : ℕ) :
    ∀ t ≤ n, expect (levelsP h t (List.replicate P [])) (fun pc => (pc.2 : ℝ≥0∞)) =
      2 * P * ∑ s ∈ Finset.range t, ∑ w ∈ words s, ENNReal.ofReal (h w)
  | 0, _ => by simp [levelsP, expect_pure]
  | t + 1, ht => by
      simp only [levelsP, expect_bind, expect_map, Function.comp_def, expect_const]
      have e : ∀ pc : List (List Bool) × ℕ, ((pc.2 + 2 * pc.1.length : ℕ) : ℝ≥0∞) =
          (pc.2 : ℝ≥0∞) + 2 * lin (fun _ => 1) pc.1 := by
        intro pc; rw [lin_const_one]; push_cast; ring
      simp_rw [e]
      rw [expect_add, expect_const_mul, expect_levelsP_count H P t (by omega),
        expect_levelsP_lin H P t (by omega), Finset.sum_range_succ]
      simp only [one_mul]
      ring

end Branching
end LearningGuided
