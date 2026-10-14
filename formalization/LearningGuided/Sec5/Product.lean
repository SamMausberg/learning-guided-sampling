import LearningGuided.Sec4.Certification

/-!
# Products of an outer and an inner problem

Strings of length `d + n` are concatenations `x v` of an outer string `x ∈ {0,1}^d` and an inner
string `v ∈ {0,1}^n` (`Fin.append`). This file sets up

* `prodDist ν σ = ν ⊗ σ` and its prefix masses;
* the product guide `H` of `eq:composition-guide`: `H(u) = g(u)` for `|u| ≤ d` and
  `H(xv) = ν(x) h(v)` for `|x| = d`;
* total-variation facts for products and projections;
* the two simulations used in Theorem `thm:composition`: lifting an outer sampler (answering
  long outer queries by `0` and appending a free draw from `U_n`), and simulating a product
  algorithm with outer queries only (for a publicly fixed inner guide).
-/

open scoped BigOperators

namespace LearningGuided
namespace Sec5

open Sec2

variable {d n : ℕ}

/-- The outer part `x` of `z = x v`. -/
def fstS (z : Str (d + n)) : Str d := fun i => z (Fin.castAdd n i)

/-- The inner part `v` of `z = x v`. -/
def sndS (z : Str (d + n)) : Str n := fun i => z (Fin.natAdd d i)

/-- Concatenation `x v`. -/
def appS (x : Str d) (v : Str n) : Str (d + n) := Fin.append x v

@[simp] theorem fstS_appS (x : Str d) (v : Str n) : fstS (appS x v) = x := by
  funext i; simp [fstS, appS, Fin.append_left]

@[simp] theorem sndS_appS (x : Str d) (v : Str n) : sndS (appS x v) = v := by
  funext i; simp [sndS, appS, Fin.append_right]

@[simp] theorem appS_fst_snd (z : Str (d + n)) : appS (fstS z) (sndS z) = z := by
  unfold appS fstS sndS
  exact Fin.append_castAdd_natAdd

theorem ofFn_appS (x : Str d) (v : Str n) :
    List.ofFn (appS x v) = List.ofFn x ++ List.ofFn v := List.ofFn_fin_append x v

theorem ofFn_split (z : Str (d + n)) : List.ofFn z = List.ofFn (fstS z) ++ List.ofFn (sndS z) := by
  conv_lhs => rw [← appS_fst_snd z]
  exact ofFn_appS _ _

theorem appS_injective {x x' : Str d} {v v' : Str n} (h : appS x v = appS x' v') :
    x = x' ∧ v = v' := by
  have h1 := congrArg fstS h
  have h2 := congrArg sndS h
  simp only [fstS_appS, sndS_appS] at h1 h2
  exact ⟨h1, h2⟩

theorem sum_split {M : Type} [AddCommMonoid M] (f : Str (d + n) → M) :
    ∑ z, f z = ∑ x : Str d, ∑ v : Str n, f (appS x v) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (Fin.appendEquiv d n) f).symm

/-! ### Product distributions -/

/-- `ν ⊗ σ`. -/
def prodDist (ν : Str d → ℝ) (σ : Str n → ℝ) : Str (d + n) → ℝ :=
  fun z => ν (fstS z) * σ (sndS z)

@[simp] theorem prodDist_appS (ν : Str d → ℝ) (σ : Str n → ℝ) (x : Str d) (v : Str n) :
    prodDist ν σ (appS x v) = ν x * σ v := by simp [prodDist]

theorem sum_prodDist (ν : Str d → ℝ) (σ : Str n → ℝ) :
    ∑ z, prodDist ν σ z = (∑ x, ν x) * ∑ v, σ v := by
  rw [sum_split, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  simp

theorem isDist_prodDist {ν : Str d → ℝ} {σ : Str n → ℝ} (hν : IsDist ν) (hσ : IsDist σ) :
    IsDist (prodDist ν σ) :=
  ⟨fun z => mul_nonneg (hν.1 _) (hσ.1 _), by rw [sum_prodDist, hν.2, hσ.2, mul_one]⟩

/-! ### Words of the product -/

/-- The outer leaf named by the first `d` bits of a word. -/
def headS (d : ℕ) (u : List Bool) : Str d := fun i => u.getD i.1 false

@[simp] theorem headS_ofFn_append (x : Str d) (w : List Bool) :
    headS d (List.ofFn x ++ w) = x := by
  funext i
  simp only [headS, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp

theorem take_eq_ofFn_headS {u : List Bool} (hu : d ≤ u.length) :
    u.take d = List.ofFn (headS d u) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_ofFn, headS, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp at h1; omega)]
  simp

theorem eq_append_headS {u : List Bool} (hu : d ≤ u.length) :
    u = List.ofFn (headS d u) ++ u.drop d := by
  rw [← take_eq_ofFn_headS hu, List.take_append_drop]

theorem isPre_short {u : List Bool} (hu : u.length ≤ d) (z : Str (d + n)) :
    IsPre u z ↔ IsPre u (fstS z) := by
  unfold IsPre
  rw [ofFn_split]
  constructor
  · intro h
    exact List.prefix_of_prefix_length_le h (List.prefix_append _ _) (by simpa using hu)
  · intro h
    exact h.trans (List.prefix_append _ _)

theorem isPre_append (x : Str d) (w : List Bool) (z : Str (d + n)) :
    IsPre (List.ofFn x ++ w) z ↔ fstS z = x ∧ IsPre w (sndS z) := by
  unfold IsPre
  rw [ofFn_split]
  constructor
  · intro h
    have hx : List.ofFn x = List.ofFn (fstS z) :=
      (List.prefix_of_prefix_length_le ((List.prefix_append _ _).trans h)
        (List.prefix_append _ _) (by simp)).eq_of_length (by simp)
    have hx' : x = fstS z := List.ofFn_injective hx
    refine ⟨hx'.symm, ?_⟩
    rw [hx] at h
    exact (List.prefix_append_right_inj _).mp h
  · rintro ⟨hx, hw⟩
    rw [hx]
    exact (List.prefix_append_right_inj _).mpr hw

theorem isPre_append_appS (x x' : Str d) (w : List Bool) (v : Str n) :
    IsPre (List.ofFn x ++ w) (appS x' v) ↔ x' = x ∧ IsPre w v := by
  rw [isPre_append]; simp

/-- Masses of the product above an outer word of length at most `d`. -/
theorem mass_prod_short {ν : Str d → ℝ} {σ : Str n → ℝ} (hσ : ∑ v, σ v = 1)
    {u : List Bool} (hu : u.length ≤ d) : mass (prodDist ν σ) u = mass ν u := by
  unfold mass
  rw [sum_split]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [isPre_short hu, fstS_appS, prodDist_appS]
  split_ifs
  · rw [← Finset.mul_sum, hσ, mul_one]
  · simp

/-- Masses of the product below an outer leaf: `μ(x w) = ν(x) σ(w)`. -/
theorem mass_prod_append (ν : Str d → ℝ) (σ : Str n → ℝ) (x : Str d) (w : List Bool) :
    mass (prodDist ν σ) (List.ofFn x ++ w) = ν x * mass σ w := by
  classical
  unfold mass
  rw [sum_split, Finset.sum_eq_single x]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [isPre_append_appS, true_and, prodDist_appS]
    split_ifs <;> simp
  · intro x' _ hx'
    refine Finset.sum_eq_zero fun v _ => ?_
    simp [isPre_append_appS, hx']
  · simp

/-! ### The product guide -/

/-- The product guide of `eq:composition-guide`: `H(u) = g(u)` for `|u| ≤ d` and
`H(xv) = ν(x) h(v)` for `|x| = d`. -/
noncomputable def prodGuide (ν : Str d → ℝ) (g h : Guide) : Guide :=
  fun u => if u.length ≤ d then g u else ν (headS d u) * h (u.drop d)

theorem prodGuide_short (ν : Str d → ℝ) (g h : Guide) {u : List Bool} (hu : u.length ≤ d) :
    prodGuide ν g h u = g u := by simp [prodGuide, hu]

/-- `eq:composition-guide`: the two definitions agree at `|u| = d` because the outer leaves are
exact and `h(∅) = 1`. -/
theorem prodGuide_append {ν : Str d → ℝ} {g h : Guide}
    (hg : ∀ x : Str d, g (List.ofFn x) = ν x) (hroot : h [] = 1) (x : Str d) (w : List Bool) :
    prodGuide ν g h (List.ofFn x ++ w) = ν x * h w := by
  unfold prodGuide
  cases w with
  | nil => simp [hg, hroot]
  | cons b w' =>
      have : ¬ (List.ofFn x ++ b :: w').length ≤ d := by simp
      rw [ite_eq_right this, headS_ofFn_append]
      congr 2
      exact List.drop_left' (by simp)

/-! ### Total variation -/

theorem tv_prodDist_le {p ν : Str d → ℝ} {σ σ' : Str n → ℝ} (hν : IsDist ν) (hσ : IsDist σ) :
    tv (prodDist p σ) (prodDist ν σ') ≤ tv p ν + tv σ σ' := by
  unfold tv
  rw [← add_div]
  gcongr
  rw [sum_split]
  calc ∑ x, ∑ v, |prodDist p σ (appS x v) - prodDist ν σ' (appS x v)|
      ≤ ∑ x, ∑ v, (|p x - ν x| * σ v + ν x * |σ v - σ' v|) := by
        gcongr with x _ v _
        simp only [prodDist_appS]
        rw [show p x * σ v - ν x * σ' v = (p x - ν x) * σ v + ν x * (σ v - σ' v) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hσ.1 v), abs_of_nonneg (hν.1 x)]
    _ = ∑ x, |p x - ν x| + ∑ v, |σ v - σ' v| := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hσ.2, mul_one]
        rw [← Finset.sum_mul, hν.2, one_mul]

/-- Projection onto the outer part does not increase total variation. -/
theorem tv_proj_le {p : PMF (Str (d + n))} {ν : Str d → ℝ} {σ : Str n → ℝ}
    (hσ : ∑ v, σ v = 1) : tv (lawR (p.map fstS)) ν ≤ tv (lawR p) (prodDist ν σ) := by
  classical
  have hmap : ∀ x, lawR (p.map fstS) x = ∑ v, lawR p (appS x v) := by
    intro x
    rw [lawR_map, sum_split, Finset.sum_eq_single x]
    · simp
    · intro x' _ hx'
      simp [hx']
    · simp
  unfold tv
  gcongr
  rw [sum_split]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [hmap]
  have : ν x = ∑ v, prodDist ν σ (appS x v) := by
    simp only [prodDist_appS, ← Finset.mul_sum, hσ, mul_one]
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ### Simulations -/

/-- Lift an outer algorithm to the product: outer queries are forwarded, queries longer than `d`
are answered `0` for free (as the outer guide would), and the output is followed by a free draw
from `U_n`. -/
noncomputable def outerLift (n : ℕ) : Alg (Str d) → Alg (Str (d + n))
  | .ret x => .sample (PMF.uniformOfFintype (Str n)) (fun v => .ret (appS x v))
  | .query u k => if u.length ≤ d then .query u (fun r => outerLift n (k r)) else outerLift n (k 0)
  | .sample p k => .sample p (fun a => outerLift n (k a))

theorem run_outerLift {g H : Guide} (hshort : ∀ u : List Bool, u.length ≤ d → H u = g u)
    (hlong : ∀ u : List Bool, d < u.length → g u = 0) (A : Alg (Str d)) :
    (outerLift n A).run H = (A.run g).bind
      (fun x => (PMF.uniformOfFintype (Str n)).bind fun v => PMF.pure (appS x v)) := by
  induction A with
  | ret x => simp [outerLift]
  | query u k ih =>
      simp only [outerLift]
      split_ifs with hu
      · rw [Alg.run_query, Alg.run_query, hshort u hu, ih]
      · rw [ih, Alg.run_query, hlong u (by omega)]
  | sample p k ih =>
      simp only [outerLift, Alg.run_sample, ih, PMF.bind_bind]

theorem within_outerLift {g H : Guide} (hshort : ∀ u : List Bool, u.length ≤ d → H u = g u)
    (hlong : ∀ u : List Bool, d < u.length → g u = 0) (A : Alg (Str d)) :
    ∀ q, A.Within g q → (outerLift n A).Within H q := by
  induction A with
  | ret x =>
      intro q _
      exact Alg.Within.sample _ _ _ fun v _ => Alg.Within.ret _ q
  | query u k ih =>
      intro q hq
      obtain ⟨r, rfl, hr⟩ := Alg.within_query_iff.mp hq
      simp only [outerLift]
      split_ifs with hu
      · refine Alg.Within.query _ _ _ ?_
        rw [hshort u hu]
        exact ih _ r hr
      · rw [hlong u (by omega)] at hr
        exact (ih 0 r hr).mono (Nat.le_succ r)
  | sample p k ih =>
      intro q hq
      exact Alg.Within.sample _ _ _ fun a ha => ih a q (Alg.within_sample_iff.mp hq a ha)

theorem lawR_outerLift_bind (P : PMF (Str d)) :
    lawR (P.bind fun x => (PMF.uniformOfFintype (Str n)).bind fun v => PMF.pure (appS x v)) =
      prodDist (lawR P) (unif n) := by
  classical
  funext z
  rw [lawR_bind]
  rw [Finset.sum_eq_single (fstS z)]
  · rw [lawR_bind, Finset.sum_eq_single (sndS z)]
    · simp [prodDist, lawR, PMF.uniformOfFintype_apply, unif]
    · intro v _ hv
      rw [lawR_pure, ite_eq_right, mul_zero]
      intro h
      apply hv
      rw [h, sndS_appS]
    · simp
  · intro x _ hx
    rw [lawR_bind]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun v _ => ?_)
    rw [lawR_pure, ite_eq_right, mul_zero]
    intro h
    apply hx
    rw [h, fstS_appS]
  · simp

/-- Simulate a product algorithm with outer queries only, for a publicly fixed inner guide `hv`:
a query of length at most `d` is forwarded, a longer query `x v` is answered by
`g(x) hv(v)` using one outer query at the outer leaf `x`, and the output is projected onto its
outer part. -/
noncomputable def innerSim (hv : Guide) : Alg (Str (d + n)) → Alg (Str d)
  | .ret z => .ret (fstS z)
  | .query u k =>
      if u.length ≤ d then .query u (fun r => innerSim hv (k r))
      else .query (u.take d) (fun r => innerSim hv (k (r * hv (u.drop d))))
  | .sample p k => .sample p (fun a => innerSim hv (k a))

theorem prodGuide_long_eq {ν : Str d → ℝ} {g : Guide} (hg : ∀ x : Str d, g (List.ofFn x) = ν x)
    (hv : Guide) {u : List Bool} (hu : ¬ u.length ≤ d) :
    g (u.take d) * hv (u.drop d) = prodGuide ν g hv u := by
  rw [take_eq_ofFn_headS (by omega), hg]
  simp [prodGuide, hu]

theorem run_innerSim {ν : Str d → ℝ} {g : Guide} (hg : ∀ x : Str d, g (List.ofFn x) = ν x)
    (hv : Guide) (A : Alg (Str (d + n))) :
    (innerSim hv A).run g = (A.run (prodGuide ν g hv)).map fstS := by
  induction A with
  | ret z => simp [innerSim, PMF.pure_map]
  | query u k ih =>
      simp only [innerSim]
      split_ifs with hu
      · rw [Alg.run_query, Alg.run_query, ih, prodGuide_short ν g hv hu]
      · rw [Alg.run_query, Alg.run_query, ih, prodGuide_long_eq hg hv hu]
  | sample p k ih =>
      simp only [innerSim, Alg.run_sample, ih, PMF.map_bind]

theorem within_innerSim {ν : Str d → ℝ} {g : Guide} (hg : ∀ x : Str d, g (List.ofFn x) = ν x)
    (hv : Guide) (A : Alg (Str (d + n))) :
    ∀ q, A.Within (prodGuide ν g hv) q → (innerSim hv A).Within g q := by
  induction A with
  | ret z => intro q _; exact Alg.Within.ret _ q
  | query u k ih =>
      intro q hq
      obtain ⟨r, rfl, hr⟩ := Alg.within_query_iff.mp hq
      simp only [innerSim]
      split_ifs with hu
      · refine Alg.Within.query _ _ _ ?_
        rw [← prodGuide_short ν g hv hu]
        exact ih _ r hr
      · refine Alg.Within.query _ _ _ ?_
        rw [prodGuide_long_eq hg hv hu]
        exact ih _ r hr
  | sample p k ih =>
      intro q hq
      exact Alg.Within.sample _ _ _ fun a ha => ih a q (Alg.within_sample_iff.mp hq a ha)

end Sec5
end LearningGuided
