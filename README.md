# Leanamycs

Lean 4 + Mathlib formalizations of classical results on opinion dynamics and
related distributed processes. Each project is paired with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) connecting the
paper proof to the Lean code statement-by-statement.

**[leanamycs.github.io/leanamycs/](leanamycs.github.io/leanamycs/)** — landing
page, blueprints, dependency graphs and API docs for everything below.

| Project | Result | Main theorem |
| --- | --- | --- |
| [`rumor_spread/`](rumor_spread) | In the uniform *push* model on the complete graph `K_n`, one initially informed node informs all `n` nodes within `O(log n)` rounds w.h.p. | `RumorPush.push_informs_all_whp` |
| [`3-majority/`](3-majority) | `n` fully-mixing agents, each adopting the majority opinion among three uniformly sampled agents, reach consensus within `O(log n)` rounds with probability `1 - O(1/n)` from a `60%` initial majority. | `ThreeMajority.majority3_consensus_whp` |

Both developments are complete and `sorry`-free, and both are built on a
minimal finite-probability layer: no measure theory, no `PMF`/`ENNReal`, no
martingales, no appeal to Mathlib's `ProbabilityTheory` library. The two sit
in different regimes — the push protocol's informed set only grows, so a
counting argument over "good rounds" suffices, whereas the 3-majority opinion
count is not monotone in the round index and so needs genuine concentration
in every round, supplied by a self-contained Chernoff bound proved from
`1 + x ≤ exp x`.

## Layout

Every project is an **independent Lake package** with its own `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`, resolved separately from its
siblings; there is no root-level Lake package. Each has the same shape:

```
<project>/
  README.md            what it proves, how it is proved, how to build it
  CLAUDE.md            orientation for automated contributors
  lakefile.toml        the Lake package (Mathlib + checkdecls)
  lean-toolchain       the pinned Lean version
  <Lib>.lean, <Lib>/   the formalization
  blueprint/src/       the leanblueprint sources
  latex/               a standalone paper proof mirroring the formalization
```

Shared at the repository root:

```
home_page/             the Jekyll landing page, deployed at the Pages root
.github/workflows/     per-project build CI, plus the shared Pages deployment
```

To work on one project, `cd` into it and use Lake as usual:

```bash
cd rumor_spread        # or: cd 3-majority
lake exe cache get     # download prebuilt Mathlib oleans (once)
lake build             # verifies every proof in that project
```

## Continuous integration

- `.github/workflows/rumor_spread-ci.yml`, `.github/workflows/three_majority-ci.yml` —
  `lake build` + lint for one project each, triggered only by changes under
  that project's directory.
- `.github/workflows/pages.yml` — builds every project's blueprint (web and
  pdf) and API docs, checks that every declaration named in a blueprint
  actually exists (`lake exe checkdecls`), assembles them under `home_page/`
  and deploys the result to GitHub Pages:

  ```
  /                         home_page/index.md
  /<project>/blueprint/     leanblueprint web version
  /<project>/blueprint.pdf  leanblueprint pdf version
  /<project>/docs/          doc-gen4 API docs
  ```

  This requires Pages to be enabled for the repository with **Source: GitHub
  Actions** (Settings → Pages).

## Adding a project

Copy the layout above into a new top-level directory, then add a
`<project>-ci.yml` workflow and one entry to the `matrix.include` list in
`pages.yml` (its directory, its Lake package name, and the `lean_lib` whose
docs to build). Set `\home{../..}` and `\dochome{../docs}` in the project's
`blueprint/src/web.tex`, since blueprints are served one level below the
landing page, and add a section for it to `home_page/index.md`.
