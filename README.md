# lean4-analysis-formalization

A compact Lean 4 + mathlib project that translates a selection of real
analysis and point-set topology statements into executable theorems.
Every theorem presented as executable is compiled; the repository does
not use `sorry`, `admit`, or custom axioms.

## Purpose

The project records how standard analysis claims are expressed in
current mathlib APIs: `ℝ`, `Filter.atTop`, `Tendsto`, `nhds`,
`Continuous` / `ContinuousAt` / `ContinuousOn`, `IsOpen` / `IsClosed`,
`IsCompact`, and `HasDerivAt`. The emphasis is on faithful domains,
quantifier order, and the assumptions that make a statement true.

## Mathematical scope

Covered topics:

- real inequalities, absolute values, coercions, and division
- sequences `ℕ → ℝ`, boundedness, monotonicity, eventual properties
- filter limits and the ε-N correspondence
- continuity, including restriction to subsets
- open and closed sets, interiors, closures, neighborhoods
- compactness, continuous images, extrema, Heine–Borel on `ℝ`
- elementary derivatives
- Rolle, Lagrange's mean value theorem, and Cauchy's mean value theorem
- order bounds and monotone convergence

The project does not develop a new analysis library. It specializes
and assembles existing mathlib theorems, with a few self-contained
ε-N and counterexample proofs.

## Environment

Pinned in this repository:

| Item | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0` (`lean-toolchain`) |
| mathlib tag | `v4.33.0` (`lakefile.toml`) |
| mathlib revision | `db584cd6d46c92f209a44c0f1c829460d327499d` (`lake-manifest.json`) |

These three files must stay in lockstep. Updating mathlib without
updating `lean-toolchain` will not build.

## Repository architecture

```
AnalysisFormalization.lean          root import
AnalysisFormalization/
  Basic.lean                        shared sequence helpers
  Inequalities.lean                 absolute values, bounds, division
  Sequences.lean                    boundedness, monotonicity, tails
  Filters.lean                      Tendsto, atTop, nhds, uniqueness
  Continuity.lean                   Continuous / ContinuousAt / ContinuousOn
  Topology.lean                     open, closed, interior, closure
  Compactness.lean                  IsCompact, EVT, Heine–Borel
  Calculus.lean                     HasDerivAt examples
  NamedTheorems.lean                Rolle, Lagrange MVT, Cauchy MVT
  OrderBounds.lean                  LUB, maxima, monotone convergence
  ReviewerCases.lean                defective-candidate repairs
  Discovery.lean                    #check of the reused mathlib APIs
CASE_INDEX.md                       case matrix
AUDIT_CHECKLIST.md                  verification record
scripts/                            local build and placeholder checks
.github/workflows/ci.yml            GitHub Actions
```

`OrderBounds.lean` is an extra module: order and supremum statements
are cleaner there than mixed into inequalities or compactness.

## Formalization ideas

- A sequence limit is `Tendsto u atTop (nhds L)`, not a `nhds`
  statement on the domain `ℕ`.
- `Metric.tendsto_atTop` plus `Real.dist_eq` recovers the textbook
  ε-N formula.
- `Continuous`, `ContinuousAt`, and `ContinuousOn` are different
  predicates. Inversion is continuous on `{0}ᶜ`, not on all of `ℝ`.
- Compactness on `ℝ` is closed and bounded. `(0, 1)` is not compact;
  `[0, 1]` is.
- `closure (Ioo a b) = Icc a b` needs `a ≠ b`.
- Pointwise convergence (`∀ x, Tendsto ...`) is not
  `TendstoUniformly`.
- Continuity on `ℝ` does not imply `UniformContinuous`; Heine–Cantor
  needs a compact domain.

Broken candidates appear only in comments in `ReviewerCases.lean`.

## How to build

Requires `elan` ([Lean installation](https://lean-lang.org/install/)).

```bash
lake exe cache get
lake build
```

`lake exe cache get` downloads precompiled mathlib oleans. Without it,
`lake build` will compile mathlib from source.

The helper script runs the placeholder check and then the build:

```bash
bash scripts/build_and_check.sh
```

## Verification

1. `bash scripts/check_no_sorry.sh` rejects `sorry`, `admit`, and
   custom `axiom` declarations in project `.lean` files (`.lake` is
   excluded).
2. `lake build` compiles `AnalysisFormalization` and all of its
   modules.
3. CI (`.github/workflows/ci.yml`) runs the same placeholder check
   and `leanprover/lean-action@v1` with `build: true` and the mathlib
   cache. `nanoda` is not enabled.

`AnalysisFormalization/Discovery.lean` contains `#check` commands.
They compile and print declaration types as informational output;
they are not build failures.

## CASE_INDEX

[CASE_INDEX.md](CASE_INDEX.md) lists each documented case with its
mathematical topic, Lean API, assumptions, failure mode, difficulty,
and source file. Every row names a compiling declaration.

Difficulty labels:

- **Foundational** — a direct specialization of a mathlib lemma, or a
  one-step algebraic identity
- **Intermediate** — a short argument that combines a few APIs
- **Advanced** — a correspondence, a compactness/calculus theorem, or
  a faithfulness counterexample

## Known limitations

- The project is a selection of cases, not a course in real analysis.
- Several theorems reuse mathlib proofs rather than reconstructing
  them. That is intentional; the corresponding CASE_INDEX rows say so.
- Suprema appear only for intervals and monotone sequences, where the
  mathlib statement is a direct match.
- Elementary derivative examples remain `id`, `x^2`, `exp`, and
  `x * exp x`. Rolle and the mean value theorems are proved in
  `NamedTheorems.lean` from EVT and Fermat's interior-extremum
  lemma, not by quoting the mathlib one-liners.
- `#check` in `Discovery.lean` emits info lines during `lake build`.
- CI status on GitHub is not known until the workflow has run on the
  default branch or a pull request.

## Reproducibility

Clone the repository and use the committed `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Then:

```bash
lake exe cache get
lake build
```

The mathlib revision is the commit recorded in `lake-manifest.json`,
not “whatever `v4.33.0` points to later” after a force-push of that
tag. If the cache is unavailable, `lake build` still works but will
compile mathlib locally.
