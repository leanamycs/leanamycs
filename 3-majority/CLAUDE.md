# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

> **Note:** this project lives in the `3-majority/` subdirectory of the
> `Leanamycs` monorepo and is an independent Lake package (its own
> `lakefile.toml`, `lake-manifest.json` and toolchain, resolved separately
> from the sibling `rumor_spread/`). GitHub only reads workflow files from
> the true repo root, so CI for this directory is
> `/.github/workflows/three_majority-ci.yml` (build + lint, scoped here via
> `lake-package-directory: 3-majority`) plus `/.github/workflows/pages.yml`,
> which builds this project's blueprint and API docs and publishes them
> under `/3-majority/` of the shared Pages site.

## Overview

A complete (`sorry`-free) Lean 4 + Mathlib formalization of the **3-majority opinion-dynamics process** on `n` fully-mixing agents: each agent holds one of two opinions and, every round, resamples three agents uniformly at random (with replacement) and adopts the majority of their opinions. Starting from a `60%` majority, consensus is reached within `O(log n)` rounds with probability `≥ 1 - 500/n`. The main theorem is `ThreeMajority.majority3_consensus_whp` in [ThreeMajority/Main.lean](ThreeMajority/Main.lean). A paper proof written to mirror the formalization lemma-for-lemma lives in [latex/three_majority.tex](latex/three_majority.tex) (compile with `latexmk -pdf` inside `latex/`).

Module structure (all under the `ThreeMajority` namespace, dependency order):

- `Bounds.lean` — elementary real inequalities: a quadratically-tight lower bound on `log` near `1` (the crude `1 - 1/x ≤ log x` is *exactly* tangent at `x = 1` and so gives a useless `0` in the Chernoff exponent), `xᵏ/k! ≤ exp x`, and tangent-line bounds on `log` at an arbitrary reference point.
- `Prob.lean` — finite uniform probability: `avg` (sum / cardinality) and `expList α T F` (expectation over `T` i.i.d. uniform draws, defined by recursion on `T`). Largely shared with `rumor_spread/RumorSpread/Prob.lean`; the addition here is `avg_prod_pi`, the independence fact for products over distinct coordinates.
- `Model.lean` — round configurations `Tgt3 n := Fin n → Fin n × Fin n × Fin n`, the `step`/`run` dynamics, and `step_mono` (monotone in `I` for fixed `r`).
- `Chernoff.lean` — the exponential-moment bound `𝔼[exp(tX)] ≤ exp(μ(eᵗ-1))` and the closed-form tail bounds at the optimal `t = log(k/μ)`, from `1 + x ≤ exp x` plus `avg_prod_pi`.
- `OneRound.lean` — the exact cubic majority map `p(x) = 3x² - 2x³` (`avg_card_step`), via `maj(a,b,c) = ab+bc+ac-2abc` on `{0,1}`, plus the per-agent `{0,1}` decomposition `Y_maj` that the Chernoff bounds consume.
- `Growth.lean` — bias amplification by `≥ 5/4` per round while the opinion-`1` fraction is in `[3/5, 3/4]`; `10` rounds get past `3/4`.
- `Saturation.lean` — three stages taking the dissent count `U_t` from `≤ n/4` to exactly `0` (geometric descent over `T2a n = ⌈6 log n⌉` rounds to a `Θ(log n)` floor; one round to a fixed constant `10`; one Markov step to `0`).
- `Main.lean` — glues growth to saturation via the `expList`-conditioning idiom and states the main theorem.

Design constraint to preserve: **no measure theory, no `PMF`/`ENNReal`, no martingales**, and no appeal to Mathlib's `ProbabilityTheory` library — everything is finite uniform sums. Unlike the sibling `rumor_spread`, a Chernoff bound *is* required (the opinion count is not monotone in the round index, so no "good rounds" counting argument is available), but it is proved from scratch in `Chernoff.lean` rather than imported.

Toolchain is pinned in [lean-toolchain](lean-toolchain); the dependencies are Mathlib and `checkdecls` (see [lakefile.toml](lakefile.toml)).

## Commands

```bash
lake build                      # build all targets (compiles + checks all proofs)
lake build ThreeMajority.Main   # check a single module
lake exe cache get              # download prebuilt Mathlib oleans (run after toolchain/dep changes — avoids hours of compiling)
lake update                     # update dependencies and regenerate lake-manifest.json
```

There is no test suite or linter beyond the Lean elaborator itself: `lake build` *is* the check — if it succeeds, every proof in the project is verified. For a quick single-file check without producing oleans: `lake env lean ThreeMajority/Foo.lean`. To verify the main theorem uses no extra axioms: `#print axioms ThreeMajority.majority3_consensus_whp` should report only `propext, Classical.choice, Quot.sound`.

## Blueprint

[blueprint/src/content.tex](blueprint/src/content.tex) is a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style companion to `latex/three_majority.tex`: the same statements, but every `theorem`/`lemma`/`definition` carries a `\lean{...}` tag (the corresponding Lean declaration(s)) and a `\uses{...}` tag (its dependencies), which drives a formalization-progress dependency graph on the web version. `blueprint/lean_decls` and `blueprint/web/`, `blueprint/print/` are build artifacts (gitignored), not committed.

- When adding or renaming a Lean declaration that has a blueprint counterpart, update the matching `\lean{}` in `content.tex` in the same change — the `checkdecls` step in `/.github/workflows/pages.yml` fails the build if a tagged name no longer exists.
- Local build (inside a venv with `pip install leanblueprint` — needs `graphviz`/`libgraphviz-dev` for the dependency graph). **Do not use the `leanblueprint web` / `leanblueprint pdf` subcommands here**: that CLI resolves the lakefile and the blueprint directory relative to the *git* root (`Repo(".", search_parent_directories=True)`), so inside this monorepo it looks for `/lakefile.toml` and `/blueprint` and bails out with "Could not find a Lean project". Run the two commands it wraps directly instead — the `leanblueprint` install is still required, for the plasTeX plugin that `blueprint/src/plastex.cfg` loads:
  ```bash
  cd blueprint/src
  mkdir -p ../web ../print
  plastex -c plastex.cfg web.tex      # -> blueprint/web/ (also (re)writes blueprint/lean_decls)
  latexmk -output-directory=../print  # -> blueprint/print/print.pdf (needs latexmk + xelatex)
  cd ../..
  lake exe checkdecls blueprint/lean_decls   # verify every \lean{} name exists
  ```
- There is no `home_page/` here: the monorepo has a single Jekyll landing page at `/home_page/` (repo root) that links to both projects' blueprints and API docs. `blueprint/src/web.tex` sets `\home{../..}` accordingly, since this project's blueprint is deployed at `/3-majority/blueprint/`.
- Do not add `doc-gen4` as a direct dependency in `lakefile.toml` — the CI docs build resolves it in an isolated `docbuild/` directory (gitignored) to avoid forcing a Mathlib/toolchain bump in the main project; only `checkdecls` is a real dependency here (needed for `lake exe checkdecls`).

## Working in this codebase

- **Module wiring:** Every new `.lean` file under `ThreeMajority/` must be imported (directly or transitively) from the root [ThreeMajority.lean](ThreeMajority.lean), otherwise `lake build` won't compile it.
- **`relaxedAutoImplicit = false`** is set, so undeclared lowercase identifiers are NOT auto-bound as implicit arguments. Declare all variables explicitly (e.g. `{n k : ℕ}` in the lemma signature) — a typo'd variable name is an error here, not a silent new implicit.
- **`weak.linter.mathlibStandardSet = true`** applies Mathlib's style linters (e.g. unused section variables, unused simp args, missing `end` are warnings); follow Mathlib naming conventions (snake_case lemma names describing the conclusion).
- `avg`, `expList` and everything downstream is `noncomputable` (real-valued).
- Lemmas needing a nonempty sample space take `(hn : 1 ≤ n)` and start with `haveI := tgt3_nonempty hn`.
- An MCP server `lean-lsp` (via `uvx lean-lsp-mcp`) is configured for this project for interactive goal inspection.
