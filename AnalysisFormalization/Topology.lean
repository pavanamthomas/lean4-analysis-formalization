/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Point-set topology on `ℝ`

Open and closed intervals, interiors, closures, and neighborhood
membership. Interval identities are sensitive to whether the endpoints
are distinct.
-/

namespace AnalysisFormalization.Topology

open Set

/-!
## Case F09 — open intervals are open

MATHEMATICAL INTENT: `(a, b)` is an open subset of `ℝ`.
LEAN REPRESENTATION: `IsOpen (Ioo a b)`.
ASSUMPTIONS: none. If `b ≤ a` the set is empty, and `∅` is open.
PROOF ARCHITECTURE: reuse `isOpen_Ioo`.
KEY MATHLIB API: `isOpen_Ioo`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming `Icc a b` is open, or `Ioo a b` is
closed, without extra hypotheses.
-/
theorem isOpen_Ioo_real (a b : ℝ) : IsOpen (Ioo a b) :=
  isOpen_Ioo

/-!
## Case F10 — closed intervals are closed

MATHEMATICAL INTENT: `[a, b]` is a closed subset of `ℝ`.
LEAN REPRESENTATION: `IsClosed (Icc a b)`.
ASSUMPTIONS: none. If `b < a` the set is empty, and `∅` is closed.
PROOF ARCHITECTURE: reuse `isClosed_Icc`.
KEY MATHLIB API: `isClosed_Icc`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: using `IsClosed` and `IsCompact` interchangeably.
Closedness is one half of Heine–Borel on `ℝ`; boundedness is the other.
-/
theorem isClosed_Icc_real (a b : ℝ) : IsClosed (Icc a b) :=
  isClosed_Icc

/-!
## Case I11 — interior of a closed interval

MATHEMATICAL INTENT: the interior of `[a, b]` is `(a, b)`.
LEAN REPRESENTATION: `interior (Icc a b) = Ioo a b`.
ASSUMPTIONS: none. The identity holds on `ℝ` because `ℝ` has no
minimum or maximum.
PROOF ARCHITECTURE: reuse `interior_Icc`.
KEY MATHLIB API: `interior_Icc`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `interior (Icc a b) = Icc a b`, which
would say that a nonempty closed interval is open.
-/
theorem interior_Icc_eq_Ioo (a b : ℝ) : interior (Icc a b) = Ioo a b :=
  interior_Icc

/-!
## Case I12 — closure of an open interval

MATHEMATICAL INTENT: if `a ≠ b` then the closure of `(a, b)` is
`[a, b]`.
LEAN REPRESENTATION: `a ≠ b → closure (Ioo a b) = Icc a b`.
ASSUMPTIONS: `a ≠ b`. If `a = b` then `Ioo a a = ∅` while
`Icc a a = {a}`, so the identity fails.
PROOF ARCHITECTURE: reuse `closure_Ioo`.
KEY MATHLIB API: `closure_Ioo`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: omitting `a ≠ b`. See `ReviewerCases`.
-/
theorem closure_Ioo_eq_Icc {a b : ℝ} (hab : a ≠ b) :
    closure (Ioo a b) = Icc a b :=
  closure_Ioo hab

/-!
## Case I16 — every set is contained in its closure

MATHEMATICAL INTENT: `s ⊆ cl(s)`.
LEAN REPRESENTATION: `s ⊆ closure s`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `subset_closure`.
KEY MATHLIB API: `subset_closure`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: confusing `s ⊆ closure s` with `s = closure s`
(i.e. closedness).
-/
theorem subset_closure_self (s : Set ℝ) : s ⊆ closure s :=
  subset_closure

/-!
## Case I20 — a point of an open set is an interior point

MATHEMATICAL INTENT: if `U` is open and `x ∈ U` then `U` is a
neighborhood of `x`.
LEAN REPRESENTATION: `IsOpen U → x ∈ U → U ∈ nhds x`.
ASSUMPTIONS: `U` open and `x ∈ U`.
PROOF ARCHITECTURE: reuse `IsOpen.mem_nhds`.
KEY MATHLIB API: `IsOpen.mem_nhds`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: concluding `U ∈ nhds x` from `x ∈ U` alone,
without openness (or a stronger neighborhood criterion).
-/
theorem mem_nhds_of_mem_open {U : Set ℝ} {x : ℝ} (hU : IsOpen U) (hx : x ∈ U) :
    U ∈ nhds x :=
  hU.mem_nhds hx

end AnalysisFormalization.Topology
