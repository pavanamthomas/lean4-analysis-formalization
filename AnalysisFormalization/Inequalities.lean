/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import AnalysisFormalization.Basic

/-!
# Real inequalities, absolute values, and coercions

Foundational identities used throughout the later modules. Several
statements are specializations of existing mathlib lemmas; they are
recorded here to make the intended real-analysis reading explicit.
-/

namespace AnalysisFormalization.Inequalities

open AnalysisFormalization

/-!
## Case F01 — triangle inequality

MATHEMATICAL INTENT: `|x + y| ≤ |x| + |y|` for real `x, y`.
LEAN REPRESENTATION: the same inequality on `ℝ`, using mathlib `|·|`.
ASSUMPTIONS: none beyond the ordered-group structure of `ℝ`.
PROOF ARCHITECTURE: reuse `abs_add_le` rather than reproving the
lattice-ordered-group argument.
KEY MATHLIB API: `abs_add_le`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing the inequality for a type that is not an
ordered additive group, or dropping the absolute values on the right.
-/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le x y

/-!
## Case F02 — absolute-value characterization of an ε-neighborhood

MATHEMATICAL INTENT: `|x| < ε` if and only if `-ε < x < ε`.
LEAN REPRESENTATION: `abs_lt : |x| < ε ↔ -ε < x ∧ x < ε`.
ASSUMPTIONS: `ε` is an arbitrary real; the equivalence does not require
`0 < ε` (if `ε ≤ 0` both sides are false).
PROOF ARCHITECTURE: reuse `abs_lt`.
KEY MATHLIB API: `abs_lt`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `|x| < ε ↔ x < ε`, which drops the lower
bound and is false for negative `x`.
-/
theorem abs_lt_iff (x ε : ℝ) : |x| < ε ↔ -ε < x ∧ x < ε :=
  abs_lt

/-!
## Case F03 — positivity of a quotient

MATHEMATICAL INTENT: a quotient of two positive reals is positive.
LEAN REPRESENTATION: `0 < a → 0 < b → 0 < a / b`.
ASSUMPTIONS: both numerator and denominator are strictly positive. The
denominator hypothesis also supplies the required nonzero condition.
PROOF ARCHITECTURE: reuse `div_pos`.
KEY MATHLIB API: `div_pos`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: omitting `0 < b` (or `b ≠ 0`) so that `a / b` is
not the intended field quotient.
-/
theorem div_pos_of_pos_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  div_pos ha hb

/-!
## Case F04 — coercion `ℕ → ℝ` preserves order

MATHEMATICAL INTENT: `n ≤ m` as natural numbers if and only if the
corresponding reals satisfy the same inequality.
LEAN REPRESENTATION: `Nat.cast_le` specialized to `ℝ`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `Nat.cast_le`.
KEY MATHLIB API: `Nat.cast_le`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: treating a `ℕ` bound as already a real bound
without an explicit coercion, or reversing the inequality direction.
-/
theorem nat_cast_le_iff {n m : ℕ} : (n : ℝ) ≤ m ↔ n ≤ m :=
  Nat.cast_le

/-!
## Case I01 — algebraic bound for a linear combination

MATHEMATICAL INTENT: `|a x + b y| ≤ |a| |x| + |b| |y|`.
LEAN REPRESENTATION: the same inequality on `ℝ`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: triangle inequality followed by `abs_mul`.
KEY MATHLIB API: `abs_add_le`, `abs_mul`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: dropping the absolute values of the coefficients,
which fails when `a` or `b` is negative.
-/
theorem abs_linear_le (a b x y : ℝ) : |a * x + b * y| ≤ |a| * |x| + |b| * |y| := by
  calc
    |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by simp [abs_mul]

/-!
## Case I02 — reverse triangle inequality

MATHEMATICAL INTENT: `| |x| - |y| | ≤ |x - y|`.
LEAN REPRESENTATION: `abs_abs_sub_abs_le` on `ℝ`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse the mathlib reverse-triangle lemma.
KEY MATHLIB API: `abs_abs_sub_abs_le`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `|x| - |y| ≤ |x - y|` without the outer
absolute value; that form requires an extra hypothesis to stay
nonnegative on the left.
-/
theorem reverse_triangle (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| :=
  abs_abs_sub_abs_le x y

/-!
## Case F12 — division cancellation with an explicit nonzero hypothesis

MATHEMATICAL INTENT: `(a / b) * b = a` whenever `b ≠ 0`.
LEAN REPRESENTATION: `div_mul_cancel₀`.
ASSUMPTIONS: `b ≠ 0`. Lean's field division is a total function, so the
identity is not true at `b = 0`.
PROOF ARCHITECTURE: reuse `div_mul_cancel₀`.
KEY MATHLIB API: `div_mul_cancel₀`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: stating `∀ a b, a / b * b = a` with no nonzero
assumption. See `ReviewerCases.div_mul_cancel_of_ne`.
-/
theorem div_mul_cancel_of_ne (a b : ℝ) (hb : b ≠ 0) : a / b * b = a :=
  div_mul_cancel₀ a hb

end AnalysisFormalization.Inequalities
