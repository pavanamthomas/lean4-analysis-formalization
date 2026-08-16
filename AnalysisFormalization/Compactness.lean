/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Compactness on `ℝ`

Closed bounded intervals are compact. Continuous images of compact
sets are compact. A continuous real function on a nonempty compact set
attains its minimum and maximum. Heine–Borel characterizes compactness
in `ℝ`.
-/

namespace AnalysisFormalization.Compactness

open Set Filter Topology

/-!
## Case I13 — a closed interval is compact

MATHEMATICAL INTENT: `[a, b]` is compact in `ℝ`.
LEAN REPRESENTATION: `IsCompact (Icc a b)`.
ASSUMPTIONS: none. If `b < a` the interval is empty, and `∅` is compact.
PROOF ARCHITECTURE: reuse `isCompact_Icc` from `CompactIccSpace ℝ`.
KEY MATHLIB API: `isCompact_Icc`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming `Ioo a b` is compact when `a < b`.
-/
theorem isCompact_Icc_real (a b : ℝ) : IsCompact (Icc a b) :=
  isCompact_Icc

/-!
## Case A03 — continuous images preserve compactness

MATHEMATICAL INTENT: the image of a compact set under a continuous map
is compact.
LEAN REPRESENTATION: `IsCompact s → Continuous f → IsCompact (f '' s)`.
ASSUMPTIONS: `s` compact and `f` globally continuous. The
`ContinuousOn` variant is `IsCompact.image_of_continuousOn`.
PROOF ARCHITECTURE: reuse `IsCompact.image`.
KEY MATHLIB API: `IsCompact.image`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: dropping continuity, or applying the statement to
an image `f '' s` when `f` is only continuous on a set that does not
contain `s`.
-/
theorem isCompact_continuous_image {s : Set ℝ} {f : ℝ → ℝ}
    (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) :=
  hs.image hf

/-!
## Case A04 — extreme value theorem on `[a, b]`

MATHEMATICAL INTENT: a continuous real function on a nonempty compact
interval attains its minimum.
LEAN REPRESENTATION: `a ≤ b` makes `Icc a b` nonempty; `ContinuousOn f`
on that interval yields `∃ x ∈ Icc a b, IsMinOn f (Icc a b) x`.
ASSUMPTIONS: `a ≤ b` and `ContinuousOn f (Icc a b)`. Continuity on an
open interval, or compactness of an unbounded closed set, is not
enough for the same conclusion.
PROOF ARCHITECTURE: `isCompact_Icc` plus `IsCompact.exists_isMinOn`.
KEY MATHLIB API: `IsCompact.exists_isMinOn`, `nonempty_Icc`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: applying the theorem on `Ioo a b`, or omitting
nonemptiness (`a ≤ b`).
-/
theorem extreme_value_min_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, IsMinOn f (Icc a b) x :=
  isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf

theorem extreme_value_max_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x :=
  isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf

/-!
## Case A05 — Heine–Borel on `ℝ`

MATHEMATICAL INTENT: a subset of `ℝ` is compact iff it is closed and
bounded.
LEAN REPRESENTATION: `IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s`.
ASSUMPTIONS: the ambient space is `ℝ`, which is a proper metric space.
The same statement is false in infinite-dimensional normed spaces.
PROOF ARCHITECTURE: reuse `Metric.isCompact_iff_isClosed_bounded`.
KEY MATHLIB API: `Metric.isCompact_iff_isClosed_bounded`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: dropping closedness (open balls are bounded but
not compact) or dropping boundedness (`ℝ` itself is closed but not
compact).
-/
theorem heine_borel_real (s : Set ℝ) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

end AnalysisFormalization.Compactness
