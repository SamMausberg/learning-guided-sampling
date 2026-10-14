# Learning-guided sampling: finite classes and one-sided reliability

**Samuel Mausberg**

Manuscript, Lean 4 formalization, and finite executable checks.

**[Read the paper](paper/learning-guided-sampling.pdf)** · **[Cite it](CITATION.cff)** ·
**[Lean map](formalization/README.md)**

## Results

The paper studies sampling from an unknown member of a known class of at most `M` distributions
on `{0,1}^n`. The only information about the target is an approximate guide to its prefix
masses, and every guide query is charged.

- Under pointwise guidance with a constant factor, the worst-case query complexity is
  `min{M, n√(log M), n²}` up to logarithmic factors. The lower bound reuses one hidden table
  across output blocks and allows arbitrary prefix queries.
- A guide that is only one-sided safe with bounded stopped reciprocal capacity can make a
  specified class much more expensive. There is a class whose pointwise cost is logarithmic in
  its size, while its safe cost is linear, with exact caps at fixed error and for exact sampling.
- For a known background plus an unknown atom of weight `α`, the worst-case rate over backgrounds
  is `Θ(1 + min{αM, α⁻¹ log(1 + 2ⁿα²)})` at error at most `α/4`. A uniform background admits a
  sharper rate, and there is a pointwise counterpart.
- A composition theorem keeps a hard fixed-error sampling task and adds a certificate that costs
  exponentially more to produce. A self-contained Poisson branching sampler gives a quadratic
  upper bound under the weak guide.

## Contents

| Path | Contents |
| --- | --- |
| [`paper/`](paper/) | LaTeX source and PDF (26 pages). `build.sh` builds it. |
| [`formalization/`](formalization/) | Lean 4 library `LearningGuided` with Mathlib, the axiom audit `AxiomAudit.lean`, and `verify.py`. [`formalization/README.md`](formalization/README.md) maps each result of the paper to its Lean theorems. |
| [`checks/`](checks/) | Exact-arithmetic finite checks of the constructions and samplers, with their recorded output. |
| [`tools/`](tools/) | Structural checks of the manuscript build and of the recorded check output. |

## Verification

- [x] The manuscript builds with no overfull or underfull boxes, LaTeX warnings, or unresolved
  references and citations.
- [x] Every bibliography entry and every pinpoint reference was checked against the primary
  source.
- [x] The Lean library builds with warnings treated as errors and with Mathlib's style linters.
  Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Every
  theorem, lemma, proposition and corollary of the paper has a Lean counterpart that cites it
  by TeX label.
- [x] The finite checks reproduce their recorded output.

The finite-class upper bound of Golowich, Moitra and Rohatgi (arXiv:2606.11437, Theorem 3.2) is
used in Theorem 1.1 and Corollary 5.3. It enters the formalization as an explicit hypothesis and
is the only result not proved there. The [Lean map](formalization/README.md) lists the coverage
statement by statement.

## Building

```sh
make paper     # pdfLaTeX; writes paper/learning-guided-sampling.pdf and paper/build.log
make checks    # reruns the finite checks and compares them with the recorded output
make lean      # in formalization/: run `lake exe cache get` first; builds and audits axioms
make lint      # ruff and CITATION.cff validation (pip install -r requirements-dev.txt)
```

The Lean toolchain (`leanprover/lean4:v4.34.0-rc2`) and the Mathlib revision are pinned in
`formalization/`. The finite checks need only the Python standard library. Continuous
integration runs all four targets.

## Citation

```bibtex
@unpublished{mausberg2026learningguided,
  author = {Samuel Mausberg},
  title  = {Learning-guided sampling: finite classes and one-sided reliability},
  year   = {2026},
  note   = {Manuscript},
  url    = {https://github.com/SamMausberg/learning-guided-sampling}
}
```

## License

The manuscript and written material are licensed under [CC BY 4.0](LICENSES/CC-BY-4.0.txt).
The Lean formalization, the Python checks and the build scripts are licensed under
[MIT](LICENSES/MIT.txt). See [LICENSE](LICENSE).

This work was developed with AI assistance from GPT-6 Astra Pro and Claude models.
