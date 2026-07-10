# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

> **Note:** this project lives in the `rumor_spread/` subdirectory of the
> `Leanamycs` monorepo. GitHub only reads workflow files from the true repo
> root, so the active CI is `/.github/workflows/rumor_spread-ci.yml` (build +
> lint only, scoped here via `lake-package-directory: rumor_spread`). The
> `.github/workflows/*.yml` files inside *this* directory (referenced below)
> are inert reference copies from this project's original standalone repo —
> they describe the full setup (including blueprint/API-docs → GitHub Pages
> deployment) but aren't run by GitHub from this location.

## Overview

A complete (`sorry`-free) Lean 4 + Mathlib formalization of the **rumor-spreading (uniform push) protocol** on the complete graph: starting from one informed node, after `O(log n)` rounds all `n` nodes are informed with probability `≥ 1 - 2/n`. The main theorem is `RumorPush.push_informs_all_whp` in [RumorSpread/Main.lean](RumorSpread/Main.lean). A paper proof written to mirror the formalization lemma-for-lemma lives in [latex/rumor_push.tex](latex/rumor_push.tex) (compile with `latexmk -pdf` inside `latex/`).

Module structure (all under the `RumorPush` namespace, dependency order):

- `Bounds.lean` — elementary real inequalities (Bernoulli & friends, `1 - 1/x ≤ log x`).
- `Prob.lean` — finite uniform probability: `avg` (sum / cardinality) and `expList α T F` (expectation over `T` i.i.d. uniform draws, defined by recursion on `T`). Markov/union bounds are pointwise inequalities pushed through `expList_le_expList`.
- `Model.lean` — round configurations `Tgt n`, the `step` and `run` (list-of-rounds) dynamics, good rounds, and the deterministic growth lemma.
- `OneRound.lean` — the one *computed* probability (`avg_not_contacted`, by counting a product of subtypes) and the per-round estimates.
- `Growth.lean` / `Saturation.lean` — the two phases; the only concentration tool is the exponential-moment induction `expList_half_pow_goodCount`.
- `Main.lean` — numeric lemmas (`numeric_A/B/C`) and the main theorem.
- `Equivalence.lean` — `expList` equals the uniform average over the product space `Fin T → α` (faithfulness of the model).

Design constraint to preserve: **no measure theory, no `PMF`/`ENNReal`, no Chernoff/martingales**; everything is finite sums plus `Real.log`/`Real.exp` only in `Main.lean` numerics.

Toolchain is pinned in [lean-toolchain](lean-toolchain); the single dependency is Mathlib (see [lakefile.toml](lakefile.toml)).

## Commands

```bash
lake build              # build all targets (compiles + checks all proofs)
lake build RumorSpread.Main   # check a single module
lake exe cache get      # download prebuilt Mathlib oleans (run after toolchain/dep changes — avoids hours of compiling)
lake update             # update dependencies and regenerate lake-manifest.json
```

There is no test suite or linter beyond the Lean elaborator itself: `lake build` *is* the check — if it succeeds, every proof in the project is verified. For a quick single-file check without producing oleans: `lake env lean RumorSpread/Foo.lean`. To verify the main theorem uses no extra axioms: `#print axioms RumorPush.push_informs_all_whp` should report only `propext, Classical.choice, Quot.sound`.

CI ([.github/workflows/lean_action_ci.yml](.github/workflows/lean_action_ci.yml)) runs `lake build` via `leanprover/lean-action` and generates docs via `docgen-action` on every push/PR; with `blueprint: true, homepage: home_page` it also builds the blueprint below and deploys the combined site (home page + `/docs/` API docs + `/blueprint/` web blueprint + `/blueprint.pdf`) to GitHub Pages.

## Blueprint

[blueprint/src/content.tex](blueprint/src/content.tex) is a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style companion to `latex/rumor_push.tex`: the same statements, but every `theorem`/`lemma`/`definition` carries a `\lean{...}` tag (the corresponding Lean declaration(s)) and a `\uses{...}` tag (its dependencies), which drives a formalization-progress dependency graph on the web version. `blueprint/lean_decls` and `blueprint/web/`, `blueprint/print/` are build artifacts (gitignored), not committed.

- When adding or renaming a Lean declaration that has a blueprint counterpart, update the matching `\lean{}` in `content.tex` in the same change — CI's `leanblueprint checkdecls` step fails the build if a tagged name no longer exists.
- Local build (inside a venv with `pip install leanblueprint` — needs `graphviz`/`libgraphviz-dev` for the dependency graph):
  ```bash
  leanblueprint web              # -> blueprint/web/ (also (re)writes blueprint/lean_decls)
  leanblueprint pdf              # -> blueprint/print/print.pdf (needs latexmk + xelatex)
  lake exe checkdecls blueprint/lean_decls   # verify every \lean{} name exists (needs `lake build checkdecls` first)
  ```
- `home_page/` is the Jekyll landing page (deployed at the Pages root) linking to the blueprint, its pdf, the dependency graph, and the API docs; edit `home_page/index.md` for content changes.
- Do not add `doc-gen4` as a direct dependency in `lakefile.toml` — the CI docs build resolves it in an isolated `docbuild/` directory to avoid forcing a Mathlib/toolchain bump in the main project; only `checkdecls` is a real dependency here (needed for `lake exe checkdecls`).

## Working in this codebase

- **Module wiring:** Every new `.lean` file under `RumorSpread/` must be imported (directly or transitively) from the root [RumorSpread.lean](RumorSpread.lean), otherwise `lake build` won't compile it.
- **`relaxedAutoImplicit = false`** is set, so undeclared lowercase identifiers are NOT auto-bound as implicit arguments. Declare all variables explicitly (e.g. `{n k : ℕ}` in the lemma signature) — a typo'd variable name is an error here, not a silent new implicit.
- **`weak.linter.mathlibStandardSet = true`** applies Mathlib's style linters (e.g. unused section variables, unused simp args, missing `end` are warnings); follow Mathlib naming conventions (snake_case lemma names describing the conclusion).
- `avg`, `expList` and everything downstream is `noncomputable` (real-valued).
- Lemmas needing a nonempty sample space take `(hn : 2 ≤ n)` and start with `haveI := tgt_nonempty hn`.
- An MCP server `lean-lsp` (via `uvx lean-lsp-mcp`) is configured for this project for interactive goal inspection.
