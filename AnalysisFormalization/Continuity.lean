/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Continuity

`Continuous f` is global continuity. `ContinuousAt f x` is continuity
at a specified point. `ContinuousOn f s` is continuity at every point
of `s` relative to `s`. These three predicates are not interchangeable.
-/

namespace AnalysisFormalization.Continuity

open Filter Topology Set

/-!
## Case F07 — the identity is continuous

MATHEMATICAL INTENT: `x ↦ x` is continuous on `ℝ`.
LEAN REPRESENTATION: `Continuous (id : ℝ → ℝ)`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `continuous_id`.
KEY MATHLIB API: `continuous_id`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: stating continuity of `id` on a subtype and then
using the statement on all of `ℝ`.
-/
theorem continuous_id_real : Continuous (id : ℝ → ℝ) :=
  continuous_id

/-!
## Case F08 — constant functions are continuous

MATHEMATICAL INTENT: `x ↦ c` is continuous on `ℝ`.
LEAN REPRESENTATION: `Continuous fun _ : ℝ ↦ c`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `continuous_const`.
KEY MATHLIB API: `continuous_const`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: none of mathematical substance; the statement is
recorded because it is the other generator, with `id`, of the
continuous-function algebra.
-/
theorem continuous_const_real (c : ℝ) : Continuous fun _ : ℝ ↦ c :=
  continuous_const

/-!
## Case I09 — composition of continuous functions

MATHEMATICAL INTENT: the composite of continuous maps is continuous.
LEAN REPRESENTATION: `Continuous g → Continuous f → Continuous (g ∘ f)`.
ASSUMPTIONS: both maps are globally continuous.
PROOF ARCHITECTURE: reuse `Continuous.comp`.
KEY MATHLIB API: `Continuous.comp`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: composing `ContinuousOn` maps without checking
that the image of the first domain lands in the second domain.
-/
theorem continuous_comp {f g : ℝ → ℝ} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  hg.comp hf

/-!
## Case I10 — a polynomial is continuous at a point

MATHEMATICAL INTENT: `x ↦ x^2 + 1` is continuous at every real, hence
in particular at a given `a`.
LEAN REPRESENTATION: `ContinuousAt (fun x ↦ x ^ 2 + 1) a`.
ASSUMPTIONS: none on `a`.
PROOF ARCHITECTURE: `fun_prop` closes global continuity; 
`Continuous.continuousAt` specializes to a point.
KEY MATHLIB API: `fun_prop`, `Continuous.continuousAt`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `ContinuousAt (fun x ↦ x ^ 2 + 1)` with
no point, which is not a well-formed proposition.
-/
theorem continuous_quadratic : Continuous fun x : ℝ ↦ x ^ 2 + 1 := by
  fun_prop

theorem continuousAt_quadratic (a : ℝ) :
    ContinuousAt (fun x : ℝ ↦ x ^ 2 + 1) a :=
  continuous_quadratic.continuousAt

/-!
## Case A02 — inversion is continuous away from zero

MATHEMATICAL INTENT: `x ↦ 1/x` is continuous on `ℝ \ {0}`.
LEAN REPRESENTATION: `ContinuousOn (fun x : ℝ ↦ x⁻¹) {0}ᶜ`.
ASSUMPTIONS: the domain is the complement of `{0}`, not all of `ℝ`.
PROOF ARCHITECTURE: reuse `continuousOn_inv₀`.
KEY MATHLIB API: `continuousOn_inv₀`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: stating `Continuous (fun x : ℝ ↦ x⁻¹)`, which
claims continuity at `0`. See `ReviewerCases`.
-/
theorem continuousOn_inv_ne_zero :
    ContinuousOn (fun x : ℝ ↦ x⁻¹) ({0}ᶜ : Set ℝ) :=
  continuousOn_inv₀

/-- Global continuity of inversion on the subtype `{x // x ≠ 0}`.
This is the same mathematics as `continuousOn_inv_ne_zero`, encoded
by changing the domain type rather than using `ContinuousOn`. -/
theorem continuous_inv_subtype :
    Continuous fun x : { x : ℝ // x ≠ 0 } ↦ (x : ℝ)⁻¹ :=
  continuousOn_iff_continuous_domRestrict.mp continuousOn_inv_ne_zero

end AnalysisFormalization.Continuity
