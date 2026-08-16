/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Elementary calculus

`HasDerivAt f f' x` is the statement that `f` has derivative `f'` at
`x`. It is stronger than mere differentiability, because it names the
derivative. The examples below stay inside stable mathlib APIs for
polynomials and the real exponential.
-/

namespace AnalysisFormalization.Calculus

open scoped Topology

/-!
## Case I14 — derivative of the identity

MATHEMATICAL INTENT: the derivative of `x ↦ x` is `1`.
LEAN REPRESENTATION: `HasDerivAt (id : ℝ → ℝ) 1 x`.
ASSUMPTIONS: none on `x`.
PROOF ARCHITECTURE: reuse `hasDerivAt_id`.
KEY MATHLIB API: `hasDerivAt_id`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `deriv id x = 1` without a
differentiability side condition; `HasDerivAt` packages both.
-/
theorem hasDerivAt_id_real (x : ℝ) : HasDerivAt (id : ℝ → ℝ) 1 x :=
  hasDerivAt_id x

/-!
## Case I15 — derivative of `x ↦ x^2`

MATHEMATICAL INTENT: the derivative of `x ↦ x^2` is `2x`.
LEAN REPRESENTATION: `HasDerivAt (fun y ↦ y ^ 2) (2 * x) x`.
ASSUMPTIONS: none on `x`.
PROOF ARCHITECTURE: specialize `hasDerivAt_pow 2` and simplify the
resulting `2 * x ^ 1`.
KEY MATHLIB API: `hasDerivAt_pow`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: using `n * x ^ n` instead of `n * x ^ (n - 1)`,
or ignoring that `n - 1` on `ℕ` is `0` when `n = 0`.
-/
theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  refine (hasDerivAt_pow (𝕜 := ℝ) 2 x).congr_deriv ?_
  simp [pow_one]

/-!
## Case I17 — derivative of the real exponential

MATHEMATICAL INTENT: the derivative of `exp` at `x` is `exp x`.
LEAN REPRESENTATION: `HasDerivAt Real.exp (Real.exp x) x`.
ASSUMPTIONS: none on `x`.
PROOF ARCHITECTURE: reuse `Real.hasDerivAt_exp`.
KEY MATHLIB API: `Real.hasDerivAt_exp`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: mixing `Real.exp` with `Complex.exp` and
expecting the same type.
-/
theorem hasDerivAt_exp_real (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x :=
  Real.hasDerivAt_exp x

theorem differentiable_exp_real : Differentiable ℝ Real.exp :=
  Real.differentiable_exp

/-!
## Case A06 — product rule for `x ↦ x * exp x`

MATHEMATICAL INTENT: the derivative of `x e^x` is `e^x + x e^x`.
LEAN REPRESENTATION: `HasDerivAt (fun y ↦ y * Real.exp y) (Real.exp x + x * Real.exp x) x`.
ASSUMPTIONS: none on `x`.
PROOF ARCHITECTURE: product rule applied to `hasDerivAt_id` and
`Real.hasDerivAt_exp`.
KEY MATHLIB API: `HasDerivAt.mul`, `hasDerivAt_id`, `Real.hasDerivAt_exp`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing the product rule as `f' * g'` (missing
the cross terms), or using `HasDerivAt.comp` when the maps are
multiplied rather than composed.
-/
theorem hasDerivAt_mul_id_exp (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.exp y) (Real.exp x + x * Real.exp x) x := by
  refine ((hasDerivAt_id' (x := x)).mul (Real.hasDerivAt_exp x)).congr_deriv ?_
  ring

/-- Differentiability follows from a named derivative. -/
theorem differentiableAt_mul_id_exp (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ ↦ y * Real.exp y) x :=
  (hasDerivAt_mul_id_exp x).differentiableAt

end AnalysisFormalization.Calculus
