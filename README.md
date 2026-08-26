# lean4-analysis-formalization

Real analysis and a bit of point-set topology, written against current mathlib APIs rather than against a textbook layout. Executable theorems are compiled. No `sorry`, `admit`, or custom axioms.

The files record how the usual claims look in Lean: `ℝ`, `Filter.atTop`, `Tendsto`, `nhds`, `Continuous` / `ContinuousAt` / `ContinuousOn`, `IsOpen` / `IsClosed`, `IsCompact`, `HasDerivAt`. I care about domains, quantifier order, and the hypotheses that make a statement true. This is not a new analysis library; it specialises existing mathlib theorems, with a few self-contained ε-N and counterexample proofs.

## Scope

- real inequalities, absolute values, coercions, and division
- sequences `ℕ → ℝ`, boundedness, monotonicity, eventual properties
- filter limits and the ε-N correspondence
- continuity, including restriction to subsets
- open and closed sets, interiors, closures, neighborhoods
- compactness, continuous images, extrema, Heine–Borel on `ℝ`
- elementary derivatives (`id`, `x^2`, `exp`, `x * exp x`)
- order bounds and monotone convergence

## Toolchain

| Item | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0` (`lean-toolchain`) |
| mathlib tag | `v4.33.0` (`lakefile.toml`) |
| mathlib revision | `db584cd6d46c92f209a44c0f1c829460d327499d` (`lake-manifest.json`) |

These three files must stay in lockstep. Updating mathlib without updating `lean-toolchain` will not build. The mathlib revision is the commit in `lake-manifest.json`, not “whatever `v4.33.0` points to later” after a force-push of that tag.

## Layout

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
  OrderBounds.lean                  LUB, maxima, monotone convergence
  ReviewerCases.lean                defective-candidate repairs
  Discovery.lean                    #check of the reused mathlib APIs
CASE_INDEX.md
AUDIT_CHECKLIST.md
```

`OrderBounds.lean` exists because order and supremum statements were cleaner there than mixed into inequalities or compactness.

## Things that are easy to get wrong

- A sequence limit is `Tendsto u atTop (nhds L)`, not a `nhds` statement on the domain `ℕ`.
- `Metric.tendsto_atTop` plus `Real.dist_eq` recovers the textbook ε-N formula.
- `Continuous`, `ContinuousAt`, and `ContinuousOn` are different predicates. Inversion is continuous on `{0}ᶜ`, not on all of `ℝ`.
- Compactness on `ℝ` is closed and bounded. `(0, 1)` is not compact; `[0, 1]` is.
- `closure (Ioo a b) = Icc a b` needs `a ≠ b`.
- Pointwise convergence (`∀ x, Tendsto ...`) is not `TendstoUniformly`.
- Continuity on `ℝ` does not imply `UniformContinuous`; Heine–Cantor needs a compact domain. The counterexample for `x^2` on `ℝ` is in `ReviewerCases.lean`. Uniform continuity of `x^2` on `[a, b]` is taken from compactness (`uniformContinuousOn_of_continuous`); the general Heine–Cantor argument is not reconstructed.

Broken candidates appear only in comments in `ReviewerCases.lean`.

## Build

Requires `elan` ([Lean installation](https://lean-lang.org/install/)).

```bash
lake exe cache get
lake build
```

Without the cache, `lake build` compiles mathlib from source. Helper: `bash scripts/build_and_check.sh`.

`bash scripts/check_no_sorry.sh` rejects `sorry`, `admit`, and custom `axiom` in project `.lean` files (`.lake` excluded). CI runs the same check and `leanprover/lean-action@v1` with `build: true` and the mathlib cache. `nanoda` is not enabled.

`Discovery.lean` contains `#check` commands. They compile and print declaration types; they are not build failures.

## Case index

[CASE_INDEX.md](CASE_INDEX.md) lists each documented case with topic, Lean API, assumptions, failure mode, difficulty, and source file. Every row names a compiling declaration.

## Limits

- A selection of cases, not a course in real analysis.
- Several theorems reuse mathlib proofs rather than reconstructing them. The corresponding CASE_INDEX rows say so.
- Suprema appear only for intervals and monotone sequences, where the mathlib statement is a direct match.
- Derivatives stop at `id`, `x^2`, `exp`, and the product `x * exp x`.
- `#check` in `Discovery.lean` emits info lines during `lake build`.
