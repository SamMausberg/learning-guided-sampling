# Lean formalization

This directory contains a Lean 4 and Mathlib formalization of the paper *Learning-guided
sampling: finite classes and one-sided reliability*. The library is `LearningGuided`, with
about 20,000 lines in 70 modules. It builds with warnings treated as errors and with Mathlib's
standard linters. Every declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Build and check

```sh
lake exe cache get   # prebuilt Mathlib
python3 verify.py    # writes lean-verification.json
```

`verify.py` performs five checks:

1. It scans the sources for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
   `implemented_by`, `@[extern]` and `maxHeartbeats 0`.
2. It checks that `LearningGuided.lean` imports every module.
3. It runs `lake build`.
4. It runs `AxiomAudit.lean`, which collects the axioms of every declaration defined in the
   library.
5. It checks that every TeX label cited in a theorem's docstring exists in `../paper`.

The toolchain (`leanprover/lean4:v4.34.0-rc2`) and the Mathlib revision (`2631d1cc`) are pinned
in `lean-toolchain` and `lake-manifest.json`.

## The model

`Basic.lean`, `Alg.lean`, `Masses.lean` and `Cuts.lean` fix the access model of Section 1.1.

**Targets, guides and the two models.**
- A target is a distribution `μ : Str n → ℝ` on `{0,1}^n`, and `mass μ u` is its prefix mass
  `μ(u)`.
- A guide is a function on words. `IsOracle` encodes `eq:oracle`. It also makes guide values
  nonnegative and words longer than `n` answer `0`, so such queries carry no information.
- `PwLegal R` is the pointwise model.
- `SafeLegal R C` is the model `eq:capacity-model`. `CapLE` is the stopped reciprocal capacity
  `CC(μ,h) ≤ C`, with the paper's conventions for zero denominators.

**Algorithms and complexity.**
- An algorithm `Alg β` is a tree of guide queries with real answers, free random draws from known
  laws (`PMF`), and outputs.
- `Alg.run h A` is its unconditional output law against the guide `h`.
- `Alg.Within h A q` says that every execution with positive probability makes at most `q`
  queries.
- `Solves Legal F δ q A` asks for the cap and for total variation at most `δ` against every
  target in `F` and every legal guide.
- `Qpw`, `Qsafe` and `Qcx` are the minimax capped complexities. `Upper.QpwNM` and
  `Upper.QsafeNM` are the worst cases over classes of at most `M` distributions.

Algorithms in the upper bounds are explicit `Alg` terms with proved output laws. Lower bounds
quantify over every `Alg`.

## Paper results and Lean theorems

Numbers refer to the compiled PDF. All names are in the namespace `LearningGuided`.

| Paper | Lean | Notes |
| --- | --- | --- |
| Theorem 1.1, `eq:pw-main`, `eq:pw-expn` | `Main.thm_pointwise`, `Main.thm_pointwise_lower_Q` | The lower bounds are unconditional. The upper bounds assume `Upper.GMRUpperBound` (GMR Theorem 3.2). The upper half of `eq:pw-expn` holds for every `n ≥ 2`. |
| Theorem 2.1 | `Sec2.thm_fixed_class`, `Sec2.fixed_safe`, `Sec2.fixed_point_exact`, `Sec2.fixed_point_theta` | `Q_safe = 3ℓ` and `4ℓ` exactly, `Q_pw(·,0) ≤ 4+⌈log₂ℓ⌉`, `log(2+ℓ) ≤ Q_pw(·,1/16) ≤ 7 log(2+ℓ)`. |
| Lemma 2.2 | `Sec2.lem_public_capacity` | Exact capacity value. |
| Theorem 3.1 | `Sec3.local_rate`, `Sec3.local_cap`, `Sec3.local_lower` | Constants `1/9` and `81/4`. |
| Lemma 3.2 | `Sec3.local_test`, `CapLE.sq_le` | |
| Proposition 3.3 | `Sec3.arbitrary_locations` | General `R, C ≥ 1`. |
| Corollary 3.4 | `Sec3.spike_pointwise` | |
| Proposition 3.5 | `Sec3.comb` | |
| Theorem 3.6 | `Sec3.background_rate`, `Sec3.Qatom_rate`, `Sec3.two_regime` | Constants `3/64` and `75`. |
| Lemma 3.7 | `Sec3.background_partition` | Holds for all `R, C > 0`. |
| Proposition 3.8 | `Sec3.background_pointwise`, `Sec3.QatomPw_rate` | |
| Repair display in Section 4 | `Sec4.correction_repair` | The correction must have mass exactly `B`. |
| Theorem 4.1 | `Sec4.thm_main`, `Sec4.point_exact`, `Sec4.safe_exact`, `Sec4.cert_tradeoff`, `Sec4.cert_certainty`, `Sec4.cert_threshold`, `Sec4.fixed_B` | Both directions of `eq:cert-tradeoff`, attained exactly. |
| Lemma 4.2 | `Sec4.lem_capacity` | `CC = C_m`, `D_{9/4} = d_m`, optimal correction. |
| Lemma 4.3 | `equality_counting` | Summed form with overlap `K`. |
| Lemma 5.1 | `Sec5.lem_capacity_concatenation`, `Sec5.capacity_concatenation_max`, `Sec5.capacity_concatenation_iter` | |
| Theorem 5.2 | `Sec5.thm_composition`, `Sec5.composition_budgets`, `Sec5.composition_certainty` | |
| Corollary 5.3 | `Main.cor_fixed_cert_instance`, `Sec5.cor_fixed_cert` | Lower bound from Appendix B. The upper bound on `Q_⊗` assumes `Upper.GMRUpperBoundAt (1/32)`. |
| Section 6, `eq:fixed-gap` | `Main.fixed_gap` | The upper bounds are the explicit caps `M-1`, `2n(J₀T+J)` and the branching cap. |
| Appendix A | `Frontier.frontier`, `Frontier.frontier_tv` | Error `3δ/4`. |
| Theorem B.1 | `PointwiseLB.Prm.pw_thm_parameter` | `q > 2^{-16}(ℓ-1)r²`, on every `n ≥ N`. |
| Lemmas B.2, B.3 | `PointwiseLB.Prm.card_targetClass_le`, `PointwiseLB.Prm.root_mass_ge`, `PointwiseLB.Prm.oracle_bounds`, `PointwiseLB.Prm.oracle_pwLegal` | |
| Definition B.4, Lemma B.5 | `PointwiseLB.TT`, `PointwiseLB.Prm.run_conv`, `PointwiseLB.Prm.within_conv` | Batches may be of any length and cost one per failure, which only strengthens the batch oracle. |
| Lemma B.6 | `PointwiseLB.Prm.card_fiber`, `PointwiseLB.Prm.card_label`, `PointwiseLB.Prm.avg_eq_val` | Counting and lazy-sampling identities. |
| Lemma B.7 | `PointwiseLB.Prm.discoveries_alg` | Stated for the lazy-sampling process, for every label kernel. |
| Lemma B.8 | `PointwiseLB.Prm.information_tv` | Stated for every output event of every algorithm, against the true prior. Proved with the Hellinger affinity; see below. |
| Lemma B.9 | `PointwiseLB.Comb.pw_lem_comb` | |
| Proposition B.10 | `Upper.pw_upper`, `Upper.identAlg_solves`, `Branching.Qpw_le_sq` | The middle term assumes `Upper.GMRUpperBound`. |
| Theorem C.1 | `Branching.branching`, `Branching.branching_safe_solves`, `Branching.branchQ_safe_le_O` | |

## Hypotheses and differences from the paper

**The only external input.** It is the finite-class upper bound of Golowich, Moitra and Rohatgi
(arXiv:2606.11437, Theorem 3.2). It enters as the explicit hypothesis `Upper.GMRUpperBoundAt δ`,
at `δ = 1/16` for Theorem 1.1 and at `δ = 1/32` for Corollary 5.3. It is never an axiom. Every
other theorem, lemma, proposition and corollary is proved without hypotheses beyond the paper's
own.

**Where proofs depart from the text.** The statements are unchanged, apart from the form of Lemma B.8 noted in the table.
- **Lemma B.8.** The proof bounds the Hellinger affinity of the two transcript laws and applies Le
  Cam's inequality, where the paper uses the KL chain rule and Pinsker's inequality. It gives
  `TV ≤ 8√η + 16η`, which implies the paper's `8√η + 32η`.
- **Branching sampler.** It processes the pooled particles depth by depth. The queries, the
  output law and the abort event are those of the paper's sampler.
- **Frontier scan.** When both children of a parent violate the threshold, the scan reports the
  first child.

**Not formalized.**
- The remark in Section 3.2 that the expected number of recovery queries is `β(k-d)`. The
  framework has no notion of expected query count; the deterministic cap is formalized.
- The `Õ` forms in `eq:fixed-gap`. The explicit caps are formalized; their asymptotic
  simplification is not.
- The discussion in Section 6 and the comparison with other sampling models.
