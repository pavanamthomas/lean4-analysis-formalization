/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Theorem and API discovery

This module records the library-navigation steps used to choose
canonical mathlib statements. The `#check` commands compile and print
types in the infoview; they are not proofs.

Typical interactive commands, used while writing the other modules:

* `#check name` — confirm a candidate's type
* `exact?` — search for a closing lemma once the goal is in canonical form
* `apply?` — search for a lemma that matches the goal's head
* `simp?` — see which simp lemmas fire
* `#loogle` / documentation search — locate a lemma by approximate type

The executable theorems below are thin wrappers that make the
discovered API visible in the build.
-/

namespace AnalysisFormalization.Discovery

open Filter Set Topology

#check abs_add_le
#check abs_lt
#check Metric.tendsto_atTop
#check tendsto_const_nhds
#check continuous_id
#check Continuous.comp
#check continuousOn_inv₀
#check isOpen_Ioo
#check isClosed_Icc
#check isCompact_Icc
#check IsCompact.exists_isMinOn
#check Metric.isCompact_iff_isClosed_bounded
#check hasDerivAt_id
#check hasDerivAt_pow
#check Real.hasDerivAt_exp
#check tendsto_atTop_ciSup
#check closure_Ioo
#check interior_Icc

/-- Discovered by `#check abs_add_le` and reused in `Inequalities`. -/
theorem discovered_abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le x y

/-- Discovered by `#check Metric.tendsto_atTop`. -/
theorem discovered_tendsto_atTop (u : ℕ → ℝ) (L : ℝ) :
    Tendsto u atTop (nhds L) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) L < ε :=
  Metric.tendsto_atTop

/-- Discovered by `#check IsCompact.exists_isMinOn`. -/
theorem discovered_exists_isMinOn {s : Set ℝ} {f : ℝ → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x :=
  hs.exists_isMinOn hne hf

end AnalysisFormalization.Discovery
