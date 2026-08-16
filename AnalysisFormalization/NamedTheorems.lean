/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Named calculus theorems

Rolle's theorem, Lagrange's mean value theorem, and Cauchy's mean
value theorem, reconstructed from the extreme value theorem and
Fermat's interior-extremum lemma rather than invoked as one-liners.

mathlib already contains these results (`exists_hasDerivAt_eq_zero`,
`exists_hasDerivAt_eq_slope`, `exists_ratio_hasDerivAt_eq_ratio_slope`).
This module records the classical argument: an interior extremum on
`[a, b]` when the endpoint values agree, a vanishing derivative at that
point, and an affine correction that reduces the mean value theorems to
Rolle.

The reconstruction is the point of the module. Closing the same goals
with the mathlib names above would not exercise the argument.
-/

namespace AnalysisFormalization.NamedTheorems

open Set Filter Topology

variable {f f' g g' : ℝ → ℝ} {a b : ℝ}

/-- Midpoint of a nonempty open interval. -/
lemma mem_Ioo_midpoint (hab : a < b) : (a + b) / 2 ∈ Ioo a b := by
  constructor
  · have : (0 : ℝ) < 2 := two_pos
    rw [lt_div_iff₀ this, mul_two]
    linarith
  · have : (0 : ℝ) < 2 := two_pos
    rw [div_lt_iff₀ this, mul_two]
    linarith

/-!
## Case A09 — interior extremum when the endpoint values agree

MATHEMATICAL INTENT: a continuous real function on `[a, b]` with
`f(a) = f(b)` attains a local extremum at some point of `(a, b)`.
LEAN REPRESENTATION: `∃ c ∈ Ioo a b, IsLocalExtr f c`.
ASSUMPTIONS: `a < b`, `ContinuousOn f (Icc a b)`, and `f a = f b`.
Without `a < b` the open interval is empty. Continuity on the open
interval alone does not give compactness, so extrema need not exist.
PROOF ARCHITECTURE: EVT supplies a global min and max on the compact
interval. If both are equal to the common endpoint value, `f` is
constant and the midpoint is a local minimum. Otherwise the strict
extremum cannot occur at an endpoint, so it lies in `(a, b)` and is
local because `[a, b]` is a neighbourhood of every interior point.
KEY MATHLIB API: `IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`,
`IsMinOn.isLocalMin`, `IsMaxOn.isLocalMax`, `Icc_mem_nhds`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: applying EVT on `Ioo a b`, or claiming an
interior extremum without `f a = f b`.
-/
theorem exists_isLocalExtr_of_eq_ends (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfI : f a = f b) : ∃ c ∈ Ioo a b, IsLocalExtr f c := by
  obtain ⟨c, cmem, hcmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hfc
  obtain ⟨C, Cmem, hcmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le) hfc
  by_cases hmin : f c = f a
  · by_cases hmax : f C = f a
    · have hconst : ∀ x ∈ Icc a b, f x = f a := fun x hx =>
        le_antisymm (hmax ▸ hcmax hx) (hmin ▸ hcmin hx)
      have hmid : (a + b) / 2 ∈ Ioo a b := mem_Ioo_midpoint hab
      refine ⟨(a + b) / 2, hmid, Or.inl ?_⟩
      have hmin' : IsMinOn f (Icc a b) ((a + b) / 2) := by
        intro x hx
        simp [hconst x hx, hconst _ (Ioo_subset_Icc_self hmid)]
      exact hmin'.isLocalMin (Icc_mem_nhds hmid.1 hmid.2)
    · have hCne_a : C ≠ a := fun h => hmax (by rw [h])
      have hCne_b : C ≠ b := fun h => hmax (by rw [h, hfI])
      have hCint : C ∈ Ioo a b :=
        ⟨lt_of_le_of_ne Cmem.1 hCne_a.symm, lt_of_le_of_ne Cmem.2 hCne_b⟩
      exact ⟨C, hCint, Or.inr (hcmax.isLocalMax (Icc_mem_nhds hCint.1 hCint.2))⟩
  · have hcne_a : c ≠ a := fun h => hmin (by rw [h])
    have hcne_b : c ≠ b := fun h => hmin (by rw [h, hfI])
    have hcint : c ∈ Ioo a b :=
      ⟨lt_of_le_of_ne cmem.1 hcne_a.symm, lt_of_le_of_ne cmem.2 hcne_b⟩
    exact ⟨c, hcint, Or.inl (hcmin.isLocalMin (Icc_mem_nhds hcint.1 hcint.2))⟩

/-!
## Case A10 — Rolle's theorem

MATHEMATICAL INTENT: if `f` is continuous on `[a, b]`, differentiable
on `(a, b)`, and `f(a) = f(b)`, then `f'(c) = 0` for some `c ∈ (a, b)`.
LEAN REPRESENTATION: `HasDerivAt` names the derivative; the conclusion
is `∃ c ∈ Ioo a b, f' c = 0`.
ASSUMPTIONS: `a < b`, continuity on the closed interval, a named
derivative at every interior point, and equal endpoint values.
Differentiability at the endpoints is not required.
PROOF ARCHITECTURE: the previous theorem supplies an interior local
extremum; Fermat's theorem (`IsLocalExtr.hasDerivAt_eq_zero`) forces
the derivative to vanish there.
KEY MATHLIB API: `IsLocalExtr.hasDerivAt_eq_zero`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: omitting `f a = f b`, or writing the conclusion
as `deriv f c = 0` without a differentiability hypothesis (`deriv`
returns `0` at non-differentiable points by definition).
-/
theorem rolle (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 := by
  obtain ⟨c, hc, hextr⟩ := exists_isLocalExtr_of_eq_ends hab hfc hfI
  exact ⟨c, hc, hextr.hasDerivAt_eq_zero (hff' c hc)⟩

/-- Affine correction used to reduce Lagrange's theorem to Rolle. -/
lemma hasDerivAt_const_mul_sub (k c x : ℝ) :
    HasDerivAt (fun t : ℝ => k * (t - c)) k x := by
  simpa using ((hasDerivAt_id' x).sub (hasDerivAt_const x c)).const_mul k

/-!
## Case A11 — Lagrange's mean value theorem

MATHEMATICAL INTENT: if `f` is continuous on `[a, b]` and differentiable
on `(a, b)`, then for some `c ∈ (a, b)` the derivative equals the
secant slope `(f(b) - f(a)) / (b - a)`.
LEAN REPRESENTATION: `∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a)`.
ASSUMPTIONS: `a < b`, `ContinuousOn f (Icc a b)`, and a named
derivative on `(a, b)`. Equal endpoint values are not assumed; they
are the special case that recovers Rolle.
PROOF ARCHITECTURE: apply Rolle to
`x ↦ f x - ((f b - f a) / (b - a)) * (x - a)`. The correction term is
chosen so that the new function has equal values at `a` and `b`. Its
derivative is `f' -` the secant slope, so a vanishing derivative is
the mean value identity.
KEY MATHLIB API: `HasDerivAt.sub`, `HasDerivAt.const_mul`,
`hasDerivAt_id'`, `hasDerivAt_const`, `div_mul_cancel₀`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: dividing by `b - a` without `a < b`, or
differentiating the correction as if it were constant.
-/
theorem lagrange_mean_value (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  set k := (f b - f a) / (b - a)
  let F : ℝ → ℝ := fun x => f x - k * (x - a)
  have hFcont : ContinuousOn F (Icc a b) :=
    hfc.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hFends : F a = F b := by
    have hk : k * (b - a) = f b - f a :=
      div_mul_cancel₀ (f b - f a) (sub_ne_zero.2 hab.ne')
    calc
      F a = f a - k * (a - a) := rfl
      _ = f a := by simp
      _ = f b - (f b - f a) := by ring
      _ = f b - k * (b - a) := by rw [hk]
      _ = F b := rfl
  have hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x - k) x := fun x hx =>
    (hff' x hx).sub (hasDerivAt_const_mul_sub k a x)
  obtain ⟨c, hc, hc0⟩ := rolle hab hFcont hFends hFderiv
  exact ⟨c, hc, sub_eq_zero.mp hc0⟩

/-!
## Case A12 — Cauchy's mean value theorem

MATHEMATICAL INTENT: if `f` and `g` are continuous on `[a, b]` and
differentiable on `(a, b)`, then for some `c ∈ (a, b)`
`f'(c) (g(b) - g(a)) = g'(c) (f(b) - f(a))`.
LEAN REPRESENTATION: the product form, which does not require
`g' c ≠ 0`.
ASSUMPTIONS: `a < b` and the same continuity / interior
differentiability hypotheses on both maps. The identity form
`f'(c) / g'(c) = (f(b) - f(a)) / (g(b) - g(a))` needs an extra
`g' c ≠ 0` that this statement avoids.
PROOF ARCHITECTURE: apply Rolle to
`x ↦ f x * (g b - g a) - g x * (f b - f a)`.
KEY MATHLIB API: `HasDerivAt.mul_const`, `HasDerivAt.sub`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing the quotient form without a nonzero
denominator, or applying Lagrange separately to `f` and `g` and
dividing the two identities (that argument also needs `g' c ≠ 0` at
the *same* point `c`).
-/
theorem cauchy_mean_value (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) :
    ∃ c ∈ Ioo a b, f' c * (g b - g a) = g' c * (f b - f a) := by
  let F : ℝ → ℝ := fun x => f x * (g b - g a) - g x * (f b - f a)
  have hFcont : ContinuousOn F (Icc a b) :=
    (hfc.mul continuousOn_const).sub (hgc.mul continuousOn_const)
  have hFends : F a = F b := by
    dsimp [F]
    ring
  have hFderiv :
      ∀ x ∈ Ioo a b, HasDerivAt F (f' x * (g b - g a) - g' x * (f b - f a)) x :=
    fun x hx => ((hff' x hx).mul_const (g b - g a)).sub ((hgg' x hx).mul_const (f b - f a))
  obtain ⟨c, hc, hc0⟩ := rolle hab hFcont hFends hFderiv
  exact ⟨c, hc, sub_eq_zero.mp hc0⟩

/-!
## Case I21 — mean value identity for `x ↦ x^2`

MATHEMATICAL INTENT: on `[a, b]` the mean value theorem for `x^2`
produces a point `c` with `2c = (b^2 - a^2) / (b - a)`.
LEAN REPRESENTATION: specialize `lagrange_mean_value` to `hasDerivAt_pow`.
ASSUMPTIONS: `a < b`.
PROOF ARCHITECTURE: continuity of `x ↦ x^2` and the derivative `2x`.
KEY MATHLIB API: `continuous_pow`, `hasDerivAt_pow`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: simplifying the slope to `a + b` and then
claiming `c = (a + b) / 2` without recording that this `c` is the
unique solution of `2c = a + b`.
-/
theorem mean_value_sq (hab : a < b) :
    ∃ c ∈ Ioo a b, 2 * c = (b ^ 2 - a ^ 2) / (b - a) := by
  have hcont : ContinuousOn (fun y : ℝ => y ^ 2) (Icc a b) :=
    (continuous_pow 2).continuousOn
  have hdiff : ∀ x ∈ Ioo a b, HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := fun x _ => by
    refine (hasDerivAt_pow (𝕜 := ℝ) 2 x).congr_deriv ?_
    simp [pow_one]
  exact lagrange_mean_value hab hcont hdiff

end AnalysisFormalization.NamedTheorems
