# Audit checklist

Record of the verification steps required by the repository
specification. Dates refer to the audit that produced this file.

## Toolchain

- [x] Exact pinned Lean version: `leanprover/lean4:v4.33.0`
  (`lean-toolchain`)
- [x] Exact mathlib revision: `db584cd6d46c92f209a44c0f1c829460d327499d`
  (tag `v4.33.0` in `lakefile.toml` and `lake-manifest.json`)
- [x] `lake-manifest.json` committed for reproducibility

## Build

- [x] Mathlib cache fetched with `lake update` / `lake exe cache get`
  (8690 files decompressed; mathlib was not rebuilt from source)
- [x] Targeted `lake build` of individual modules during development
- [x] Full `lake build` of `AnalysisFormalization` succeeded
- [x] Full `lake build` repeated after the documentation and script
  files were added (Lean sources unchanged in that step)

## Placeholders and axioms

- [x] No `sorry` in project `.lean` files excluding `.lake`
- [x] No `admit` in project `.lean` files excluding `.lake`
- [x] No custom `axiom` declarations in project sources
- [x] `scripts/check_no_sorry.sh` enforces the three checks above

## Semantic audit

- [x] Domain audit: inversion and `1/(n+1)` avoid a zero denominator;
  `sqrt` identities carry `0 ≤ x`
- [x] Assumption audit: EVT uses `a ≤ b`; closure of `Ioo` uses
  `a ≠ b`; division cancellation uses `b ≠ 0`
- [x] Quantifier audit: sequential limits use `∃ N, ∀ n ≥ N`; the
  swapped order is recorded as a defective candidate
- [x] Statement-faithfulness audit: `Continuous` / `ContinuousAt` /
  `ContinuousOn`, `atTop` vs `nhds`, compact vs closed, pointwise vs
  uniform, existing vs named limits

## Documentation consistency

- [x] Every CASE_INDEX row names a declaration that exists in the
  listed file
- [x] README environment pins match `lean-toolchain`, `lakefile.toml`,
  and `lake-manifest.json`
- [x] README architecture list matches the files in the repository
- [x] `NamedTheorems.lean` records Rolle, Lagrange MVT, and Cauchy MVT
  as reconstructed arguments, with matching CASE_INDEX rows A09–A12 and I21
- [x] README does not claim a green CI badge before the workflow has
  run on GitHub

## CI

- [x] `.github/workflows/ci.yml` triggers on push and pull requests to
  `main`
- [x] Workflow checks out the repository
- [x] Workflow rejects `sorry` and `admit`
- [x] Workflow uses `leanprover/lean-action@v1` with `build: true`
- [x] Workflow does not enable `nanoda`
- [x] Workflow sets `use-mathlib-cache: true`
- [ ] GitHub Actions status on `main` is not claimed here; it depends
  on a run after the workflow file is on GitHub

## Known warnings and info

- `AnalysisFormalization/Discovery.lean` emits informational `#check`
  output during `lake build`. These are not errors.
- No linter warnings remained in the last successful full build of the
  library modules.

## Limitations

- See README “Known limitations”.
- The audit does not independently re-typecheck mathlib; it relies on
  the cached oleans for revision
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
