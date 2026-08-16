/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import AnalysisFormalization.Basic
import AnalysisFormalization.Sequences

/-!
# Filters and sequential limits

A real sequence `u : ℕ → ℝ` converges to `L` when
`Tendsto u atTop (nhds L)`. The filter `atTop` encodes "for all
sufficiently large `n`"; `nhds L` encodes "in every neighborhood of
`L`". The ε-N formulation is recovered as `Metric.tendsto_atTop`.
-/

namespace AnalysisFormalization.Filters

open Filter Topology AnalysisFormalization

/-!
## Case A01 — ε-N convergence is `Tendsto` along `atTop`

MATHEMATICAL INTENT: `u n → L` iff
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - L| < ε`.
LEAN REPRESENTATION: `Tendsto u atTop (nhds L)` ↔ the ε-N statement,
using `dist x y = |x - y|` on `ℝ`.
ASSUMPTIONS: `u : ℕ → ℝ`, `L : ℝ`.
PROOF ARCHITECTURE: `Metric.tendsto_atTop` plus `Real.dist_eq`.
KEY MATHLIB API: `Metric.tendsto_atTop`, `Real.dist_eq`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: using `nhds 0` as the domain filter, or writing
`∃ n, ∀ ε` / `∀ N, ∃ n` in place of `∃ N, ∀ n ≥ N`.
-/
theorem tendsto_iff_metric_epsilon (u : ℕ → ℝ) (L : ℝ) :
    Tendsto u atTop (nhds L) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - L| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]

/-!
## Case I06 — `1/(n+1) → 0` as a filter limit

MATHEMATICAL INTENT: `1/(n+1)` tends to `0`.
LEAN REPRESENTATION: `Tendsto oneDivSucc atTop (nhds 0)`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: apply Case A01 and the eventual bound from
`Sequences.eventually_oneDivSucc_lt`.
KEY MATHLIB API: `Metric.tendsto_atTop`, `eventually_atTop`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: proving the statement for `1/n` as a function of
a real variable without restricting away from `0`.
-/
theorem tendsto_oneDivSucc :
    Tendsto oneDivSucc atTop (nhds 0) := by
  rw [tendsto_iff_metric_epsilon]
  intro ε hε
  have h := Sequences.eventually_oneDivSucc_lt hε
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  simpa [sub_zero] using hN n hn

/-!
## Case I07 — membership in `atTop`

MATHEMATICAL INTENT: a set of naturals contains all sufficiently large
indices iff it belongs to `atTop`.
LEAN REPRESENTATION: `s ∈ atTop ↔ ∃ N, ∀ n ≥ N, n ∈ s`.
ASSUMPTIONS: `s : Set ℕ`.
PROOF ARCHITECTURE: reuse `mem_atTop_sets`.
KEY MATHLIB API: `Filter.mem_atTop_sets`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: confusing `atTop` with `nhds` of a point, or with
the cofinite filter on a finite type.
-/
theorem mem_atTop_iff (s : Set ℕ) :
    s ∈ atTop ↔ ∃ N : ℕ, ∀ n ≥ N, n ∈ s :=
  mem_atTop_sets

/-!
## Case I08 — sums of convergent sequences

MATHEMATICAL INTENT: if `u n → L` and `v n → M` then `u n + v n → L + M`.
LEAN REPRESENTATION: `Tendsto.add`.
ASSUMPTIONS: the two given `Tendsto` hypotheses.
PROOF ARCHITECTURE: reuse `Tendsto.add`; addition is continuous.
KEY MATHLIB API: `Tendsto.add`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming the same for quotients without a
nonzero-limit hypothesis on the denominator.
-/
theorem tendsto_add_sequences {u v : ℕ → ℝ} {L M : ℝ}
    (hu : Tendsto u atTop (nhds L)) (hv : Tendsto v atTop (nhds M)) :
    Tendsto (fun n => u n + v n) atTop (nhds (L + M)) :=
  hu.add hv

/-!
## Case A07 — uniqueness of sequential limits

MATHEMATICAL INTENT: a sequence has at most one limit in `ℝ`.
LEAN REPRESENTATION: `Tendsto u atTop (nhds L)` and
`Tendsto u atTop (nhds M)` imply `L = M`.
ASSUMPTIONS: the two `Tendsto` hypotheses. The argument uses that `ℝ`
is Hausdorff (`T2Space`).
PROOF ARCHITECTURE: reuse `tendsto_nhds_unique`.
KEY MATHLIB API: `tendsto_nhds_unique`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: treating `∃ L, Tendsto u atTop (nhds L)` as if it
identified a specific limit. Existence of some limit is weaker than
convergence to a named value.
-/
theorem tendsto_unique_real {u : ℕ → ℝ} {L M : ℝ}
    (hL : Tendsto u atTop (nhds L)) (hM : Tendsto u atTop (nhds M)) :
    L = M :=
  tendsto_nhds_unique hL hM

end AnalysisFormalization.Filters
