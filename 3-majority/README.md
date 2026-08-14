# 3-majority dynamics: a Lean 4 formalization

A complete, `sorry`-free Lean 4 + Mathlib formalization of the **3-majority**
opinion-dynamics process on `n` fully-mixing agents:

> **Theorem.** Each of `n` agents holds one of two opinions and, every round,
> simultaneously resamples three agents uniformly at random (with
> replacement) and adopts the majority of their opinions. If one opinion
> starts with at least a `60%` share, then after `O(log n)` rounds **all**
> agents hold that opinion with probability `1 - O(1/n)`.

Formally (`ThreeMajority.majority3_consensus_whp` in
[ThreeMajority/Main.lean](ThreeMajority/Main.lean)): if `log n ≥ 30` and the
initial opinion-`1` set `I₀` satisfies `|I₀| ≥ (3/5)n`, then after
`10 + (⌈6 log n⌉ + 2)` rounds the probability that consensus has *not* been
reached is at most `500/n`. The constants are deliberately crude in exchange
for a minimal analytic toolkit.

A self-contained paper proof, written to mirror the formalization
lemma-for-lemma, is in [latex/three_majority.tex](latex/three_majority.tex).

**[Blueprint](https://leanamycs.github.io/leanamycs/3-majority/blueprint/)** ·
**[Blueprint as pdf](https://leanamycs.github.io/leanamycs/3-majority/blueprint.pdf)** ·
**[Dependency graph](https://leanamycs.github.io/leanamycs/3-majority/blueprint/dep_graph_document.html)** ·
**[API docs](https://leanamycs.github.io/leanamycs/rumor_spread/docs/)**

The blueprint ([blueprint/src/content.tex](blueprint/src/content.tex)) states
every lemma with a `\lean{}` tag pointing to its Lean declaration and a
`\uses{}` tag recording its dependencies, so the web version renders a
dependency graph and a formalization-progress view; `leanblueprint
checkdecls` (run in CI) fails the build if a tagged declaration doesn't
exist.

## Design

Like the sister [rumor_spread](../rumor_spread) development, this one avoids
measure theory, `PMF`, `ENNReal`, kernels and martingales entirely — all
randomness is uniform over finite types. The one deliberate difference is
that a Chernoff bound *is* needed here, and so is proved from scratch:

- **Probability** ([Prob.lean](ThreeMajority/Prob.lean)): `avg` is a sum
  divided by a cardinality; `expList α T F` — the expectation of a
  trajectory functional over `T` i.i.d. uniform rounds — is defined by
  recursion on `T`, which makes conditioning on a round a definitional
  unfolding. New relative to `rumor_spread`: `avg_prod_pi`, the
  independence fact that the average of a product of functions of distinct
  coordinates factors as the product of the averages.
- **Model** ([Model.lean](ThreeMajority/Model.lean)): a round is
  `Tgt3 n := Fin n → Fin n × Fin n × Fin n` (every agent draws an ordered
  triple with replacement); `step I r` keeps the agents at least two of
  whose samples lie in `I`. `step_mono` is the monotone coupling — `step`
  is monotone in `I` for fixed `r`, though **not** in the round index.
- **One-round drift** ([OneRound.lean](ThreeMajority/OneRound.lean)): the
  exact cubic majority map `p(x) = 3x² - 2x³`, via the polynomial identity
  `maj(a,b,c) = ab+bc+ac-2abc` on `{0,1}`, plus the per-agent `{0,1}`
  decomposition of `(step I r).card` that the Chernoff bounds consume.
- **Chernoff** ([Chernoff.lean](ThreeMajority/Chernoff.lean)): the only
  concentration tool, built from `1 + x ≤ exp x` and `avg_prod_pi` alone —
  the exponential-moment bound `𝔼[exp(tX)] ≤ exp(μ(eᵗ-1))`, Markov applied
  to `exp(tX)`, and the closed forms at the optimal `t = log(k/μ)`. These
  are *mean-scaled*, which is what keeps them useful once few dissenting
  agents remain.
- **Growth phase** ([Growth.lean](ThreeMajority/Growth.lean)): while the
  opinion-`1` fraction is in `[3/5, 3/4]` the majority map amplifies the
  bias by `≥ 5/4` per round in expectation; `10` rounds take the fraction
  past `3/4` except with probability `≤ 10 exp(-c₁n)`.
- **Saturation phase** ([Saturation.lean](ThreeMajority/Saturation.lean)):
  the dissent count contracts by `5/8` per round, in three stages —
  geometric descent to a `Θ(log n)` floor over `⌈6 log n⌉` rounds, one
  round from that floor to a fixed constant `10`, and one final Markov step
  to exactly `0`.
- **Elementary inequalities** ([Bounds.lean](ThreeMajority/Bounds.lean)):
  quadratically-tight lower bounds on `log` near `1`, `xᵏ/k! ≤ exp x`, and
  tangent-line bounds used to keep the threshold on `log n` modest.

Because the opinion count is not monotone in the round index, there is no
"good rounds" counting argument available (the device that carries
`rumor_spread`'s growth phase); every round genuinely needs concentration.

## Building

```bash
lake exe cache get   # download prebuilt Mathlib oleans (once)
lake build           # verifies every proof
```

Toolchain: see [lean-toolchain](lean-toolchain). The main theorem depends only
on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
