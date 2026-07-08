# Rumor spreading: a Lean 4 formalization

A complete, `sorry`-free Lean 4 + Mathlib formalization of the classical
rumor-spreading result in distributed computing:

> **Theorem.** In the uniform *push* model on the complete graph `K_n`, if one
> node is informed initially, then after `O(log n)` rounds **all** nodes are
> informed with high probability.

Formally (`RumorPush.push_informs_all_whp` in
[RumorSpread/Main.lean](RumorSpread/Main.lean)): for `n ≥ 2`, after
`T = (⌈117 ln n⌉ + 23) + ⌈6 ln n⌉` rounds the probability that some node is
still uninformed is at most `2/n`. The constants are deliberately crude — the
sharp threshold is `log₂ n + ln n` (Frieze–Grimmett 1985, Pittel 1987) — in
exchange for a minimal analytic toolkit.

A self-contained paper proof, written to mirror the formalization
lemma-for-lemma, is in [latex/rumor_push.tex](latex/rumor_push.tex).

**[Blueprint](https://aakash-verse.github.io/Rumor_Spreading_on_Kn/blueprint/)** ·
**[Blueprint as pdf](https://aakash-verse.github.io/Rumor_Spreading_on_Kn/blueprint.pdf)** ·
**[Dependency graph](https://aakash-verse.github.io/Rumor_Spreading_on_Kn/blueprint/dep_graph_document.html)** ·
**[API docs](https://aakash-verse.github.io/Rumor_Spreading_on_Kn/docs/)**

The blueprint ([blueprint/src/content.tex](blueprint/src/content.tex)) states
every lemma with a `\lean{}` tag pointing to its Lean declaration and a
`\uses{}` tag recording its dependencies, so the web version renders a
dependency graph and a formalization-progress view; `leanblueprint
checkdecls` (run in CI) fails the build if a tagged declaration doesn't
exist.

## Design

The development avoids measure theory, `PMF`, `ENNReal`, the exponential
function, Chernoff bounds and martingales entirely:

- **Probability** ([Prob.lean](RumorSpread/Prob.lean)): all randomness is
  uniform over finite types. `avg` is a sum divided by a cardinality;
  `expList α T F` — the expectation of a trajectory functional over `T`
  i.i.d. uniform rounds — is defined by recursion on `T`, which makes
  conditioning on a round a definitional unfolding.
  [Equivalence.lean](RumorSpread/Equivalence.lean) proves this equals the
  uniform average over the product space of all round sequences.
- **Model** ([Model.lean](RumorSpread/Model.lean)): a round is
  `Tgt n := ∀ v : Fin n, {u // u ≠ v}` (every node picks a target ≠ itself);
  `step I r = I ∪ I.image r`; trajectories are lists of rounds.
- **One computed probability** ([OneRound.lean](RumorSpread/OneRound.lean)):
  a fixed uninformed node is missed by all pushes with probability exactly
  `(1 - 1/(n-1))^|I|`, by counting a product of subtypes.
- **Growth phase** ([Growth.lean](RumorSpread/Growth.lean)): while `|I| ≤ n/2`
  a round grows `|I|` by a factor `9/8` with probability `≥ 1/8`
  (expected growth + reverse Markov); the only concentration tool is the
  exponential-moment induction `𝔼[(1/2)^(good rounds)] ≤ (15/16)^T`.
- **Saturation phase** ([Saturation.lean](RumorSpread/Saturation.lean)): above
  `n/2` the expected uninformed count contracts by `2/3` per round; Markov
  finishes.
- **Elementary inequalities** ([Bounds.lean](RumorSpread/Bounds.lean)):
  Bernoulli's inequality and its consequences; `1 - 1/x ≤ log x`.

## Building

```bash
lake exe cache get   # download prebuilt Mathlib oleans (once)
lake build           # verifies every proof
```

Toolchain: see [lean-toolchain](lean-toolchain). The main theorem depends only
on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
