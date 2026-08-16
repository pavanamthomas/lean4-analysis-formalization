/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Order, bounds, and monotone convergence

Upper bounds, greatest elements, strict monotonicity, and the
monotone-convergence theorem for real sequences. Suprema are used only
where the mathlib API is a direct match for the intended statement.
-/

namespace AnalysisFormalization.OrderBounds

open Filter Set Topology

/-!
## Case F11 — least upper bound of `(-∞, a]`

MATHEMATICAL INTENT: `a` is the least upper bound of `{x | x ≤ a}`.
LEAN REPRESENTATION: `IsLUB (Iic a) a`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `isLUB_Iic`.
KEY MATHLIB API: `isLUB_Iic`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `IsGLB (Iic a) a` (wrong end of the
order) or `IsLUB (Iio a) a` without a density hypothesis.
-/
theorem isLUB_Iic_real (a : ℝ) : IsLUB (Iic a) a :=
  isLUB_Iic

/-!
## Case I18 — translation is strictly monotone

MATHEMATICAL INTENT: `x ↦ x + c` is strictly increasing for every
real `c`.
LEAN REPRESENTATION: `StrictMono fun x : ℝ ↦ x + c`.
ASSUMPTIONS: none on `c`.
PROOF ARCHITECTURE: `add_lt_add_right`.
KEY MATHLIB API: `add_lt_add_right`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming `x ↦ c - x` is strictly increasing, or
confusing `Monotone` with `StrictMono`.
-/
theorem strictMono_add_const (c : ℝ) : StrictMono fun x : ℝ => x + c :=
  fun _ _ h => by linarith

/-!
## Case I19 — a closed interval has a greatest element

MATHEMATICAL INTENT: if `a ≤ b` then `b` is the maximum of `[a, b]`.
LEAN REPRESENTATION: `IsGreatest (Icc a b) b`.
ASSUMPTIONS: `a ≤ b`, so that `b ∈ Icc a b`.
PROOF ARCHITECTURE: reuse `isGreatest_Icc`.
KEY MATHLIB API: `isGreatest_Icc`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming `IsGreatest (Ioo a b) b`, which is false
because `b ∉ Ioo a b`.
-/
theorem isGreatest_Icc_real {a b : ℝ} (hab : a ≤ b) : IsGreatest (Icc a b) b :=
  isGreatest_Icc hab

theorem csSup_Icc_real {a b : ℝ} (hab : a ≤ b) : sSup (Icc a b) = b :=
  (isGreatest_Icc hab).csSup_eq

/-!
## Case A08 — monotone convergence theorem

MATHEMATICAL INTENT: a monotone bounded-above real sequence converges
to the supremum of its range.
LEAN REPRESENTATION: `Monotone u → BddAbove (range u) →
Tendsto u atTop (nhds (⨆ n, u n))`.
ASSUMPTIONS: monotonicity and an upper bound for the image. Without
the bound the sequence may diverge to `+∞`.
PROOF ARCHITECTURE: reuse `tendsto_atTop_ciSup`.
KEY MATHLIB API: `tendsto_atTop_ciSup`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: omitting `BddAbove`, or concluding convergence
from boundedness alone (without monotonicity).
-/
theorem monotone_bddAbove_tendsto {u : ℕ → ℝ}
    (hmono : Monotone u) (hbdd : BddAbove (range u)) :
    Tendsto u atTop (nhds (⨆ n, u n)) :=
  tendsto_atTop_ciSup hmono hbdd

end AnalysisFormalization.OrderBounds
