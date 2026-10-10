# Quantitative permanence and recovery with vanishing reverse rates

Quantitative permanence and recovery bounds are established for mass-action systems with vanishing reverse rates. For a finite weakly reversible network with rates proportional to powers of epsilon, eventual concentration bounds depend on the spread of the rate exponents, with geometric constants chosen before the individual rates. For an explicit three-species network, a prepared region admits global positive solutions with three distinct concentration scales. Every prepared solution reaches and remains in a smaller target by time (31/10)/(p^2 h^7), while an explicit prepared solution cannot enter before 400/(1313 p^2 h^7). Inventory inequalities give additional necessary restoration and depletion times from arbitrary positive initial states. A continuous reverse-exponent family retains arbitrary admitted prefactors and yields matching worst-case prepared recovery orders, together with exact common-clock transport, preparation identities and cumulative reverse-reaction bounds. Abstract constant-capacity and open-range state-dependent inventory comparisons are included without assuming monotone inventories.

The general construction builds on the attributed [affine permanence development](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Permanence-in-Weakly-Reversible-Mass-Action-Systems-October-5-2026). Source provenance and acknowledgments are recorded in [NOTICE](NOTICE) and [UPSTREAM_PROVENANCE.json](UPSTREAM_PROVENANCE.json).

- [Manuscript](paper/main.pdf) and [LaTeX source](paper/main.tex)
- [Formal statements](Challenge.lean) and [proof entry point](Solution.lean)
- [Theorem-to-manuscript correspondence](CLAIM_MAP.md)
- [Reproduction instructions](BUILD.md) and [verification evidence](verification/local-check.json)

All eighteen selected declarations passed statement comparison and six kernel checks under Lean 4.35.0-rc2. The manuscript distinguishes the selected deterministic results from its conventional stochastic arguments and numerical illustrations.

The contribution is distributed under [Apache-2.0](LICENSE), with upstream attribution retained.
