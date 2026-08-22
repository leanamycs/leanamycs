---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: default
usemathjax: true
---

**Leanamycs** is a collection of Lean 4 + Mathlib formalizations of classical
results on opinion dynamics and related distributed processes, each paired
with a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) page
connecting the paper proof to the Lean code statement-by-statement. Both
developments below are complete and `sorry`-free, and both are built on a
minimal finite-probability layer — no measure theory, no `PMF`/`ENNReal`, no
martingales. More protocols are expected to join over time.

## Rumor spreading (uniform push)

In the uniform *push* model on the complete graph $K_n$, every informed node
sends the rumor to a uniformly random other node each round. Starting from a
single informed node, after $O(\log n)$ rounds **all** nodes are informed
with high probability. The main theorem is `RumorPush.push_informs_all_whp`.

* [Blueprint]({{ '/rumor_spread/blueprint/' | relative_url }}) · [as pdf]({{ '/rumor_spread/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/rumor_spread/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/rumor_spread/docs/' | relative_url }})
* [Source](https://github.com/leanamycs/leanamycs/tree/main/rumor_spread)
   
## 3-majority dynamics

In the *3-majority* model on $n$ fully-mixing agents, each agent holds one of
two opinions and every round adopts the majority opinion among three agents
sampled uniformly at random. Starting from an imbalance of at least $60\%$
vs. $40\%$, after $O(\log n)$ rounds **all** agents hold the initial majority
opinion with probability $1 - O(1/n)$. The main theorem is
`ThreeMajority.majority3_consensus_whp`.

* [Blueprint]({{ '/3-majority/blueprint/' | relative_url }}) · [as pdf]({{ '/3-majority/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/3-majority/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/3-majority/docs/' | relative_url }})
* [Source](https://github.com/leanamycs/leanamycs/tree/main/3-majority)

---

Each project is an independent Lean package (its own `lakefile.toml` and
toolchain) living in its own subdirectory of the repository; this page is the
shared landing page linking out to both. See each subdirectory's own
`README.md` for build instructions.
