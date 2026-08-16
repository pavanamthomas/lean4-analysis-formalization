/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import AnalysisFormalization.Basic
import AnalysisFormalization.Filters
import AnalysisFormalization.Sequences

/-!
# Formalization-faithfulness cases

Each case records a natural-language analysis claim, a defective Lean
candidate (comments only), the exact defect, a corrected executable
statement, and a compiling proof. Defective candidates are not
compiled and do not use incomplete-proof placeholders.
-/

namespace AnalysisFormalization.ReviewerCases

open Filter Set Topology AnalysisFormalization

noncomputable section

/-!
## Case R01 — wrong domain for inversion

MATHEMATICAL INTENT: `x |-> 1/x` is continuous where it is defined.
DEFECTIVE CANDIDATE:
  `Continuous (fun x : Real => x^{-1})`
EXACT DEFECT: the domain is all of `Real`, so the claim includes
continuity at `0`. Lean's inversion is a total function with
`0^{-1} = 0`, which is not continuous at `0`.
CORRECTED LEAN STATEMENT: `ContinuousOn (fun x : Real => x^{-1}) {0}ᶜ`
and equivalently continuity on the subtype `{x // x ≠ 0}`.
WHY THE CORRECTION IS FAITHFUL: the intended domain of the reciprocal
is the nonzero reals, encoded either as `ContinuousOn` or as a
subtype domain.
-/
theorem not_continuous_inv_on_real : ¬ Continuous fun x : ℝ => x⁻¹ := by
  intro hf
  have hseq : Tendsto (fun n : ℕ => (oneDivSucc n)⁻¹) atTop (nhds (0 : ℝ)⁻¹) :=
    hf.continuousAt.tendsto.comp Filters.tendsto_oneDivSucc
  have hsimp : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop (nhds 0) := by
    simpa [oneDivSucc, inv_div] using hseq
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact not_tendsto_nhds_of_tendsto_atTop htop 0 hsimp

theorem continuousOn_inv_ne_zero :
    ContinuousOn (fun x : ℝ => x⁻¹) ({0}ᶜ : Set ℝ) :=
  continuousOn_inv₀

theorem continuous_inv_subtype :
    Continuous fun x : { x : ℝ // x ≠ 0 } => (x : ℝ)⁻¹ :=
  continuousOn_iff_continuous_domRestrict.mp continuousOn_inv_ne_zero

/-!
## Case R02 — missing nonnegativity for `sqrt`

MATHEMATICAL INTENT: `(√x)² = x` for real `x`.
DEFECTIVE CANDIDATE:
  `∀ x : Real, Real.sqrt x ^ 2 = x`
EXACT DEFECT: missing `0 ≤ x`. For `x < 0`, mathlib defines
`Real.sqrt x = 0`, so the identity fails.
CORRECTED LEAN STATEMENT: `0 ≤ x → Real.sqrt x ^ 2 = x`.
WHY THE CORRECTION IS FAITHFUL: the real square-root identity is
stated only on the domain where the square root is inverse to
squaring.
-/
theorem sqrt_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ^ 2 = x :=
  Real.sq_sqrt hx

theorem not_sqrt_sq_of_neg {x : ℝ} (hx : x < 0) : Real.sqrt x ^ 2 ≠ x := by
  have : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx.le
  simp [this]
  exact hx.ne'

/-!
## Case R03 — `Continuous` versus `ContinuousAt`

MATHEMATICAL INTENT: continuity at a single point is not global
continuity.
DEFECTIVE CANDIDATE:
  treating `ContinuousAt f` as a complete statement, or inferring
  `Continuous f` from `ContinuousAt f x` at one `x`.
EXACT DEFECT: `ContinuousAt` requires a point; one-point continuity
does not imply global continuity.
CORRECTED LEAN STATEMENT: `Continuous f ↔ ∀ x, ContinuousAt f x`,
together with a step function that is continuous at `1` but not at `0`.
WHY THE CORRECTION IS FAITHFUL: it keeps the point argument and
separates local from global continuity.
-/
theorem continuous_iff_continuousAt_real (f : ℝ → ℝ) :
    Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt

def stepFn (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

theorem continuousAt_stepFn_one : ContinuousAt stepFn 1 := by
  have hstep : stepFn 1 = 1 := by simp [stepFn]
  have heq : ∀ᶠ y in nhds (1 : ℝ), (1 : ℝ) = stepFn y := by
    rw [eventually_nhds_iff]
    refine ⟨Ioo 0 2, ?_, isOpen_Ioo, by norm_num⟩
    intro y hy
    simp [stepFn, hy.1.le]
  rw [ContinuousAt, hstep]
  exact tendsto_const_nhds.congr' heq

theorem not_continuousAt_stepFn_zero : ¬ ContinuousAt stepFn 0 := by
  intro h
  have hseq : Tendsto (fun n : ℕ => -oneDivSucc n) atTop (nhds 0) := by
    simpa using Filters.tendsto_oneDivSucc.neg
  have hval : ∀ n, stepFn (-oneDivSucc n) = 0 := by
    intro n
    have : ¬ 0 ≤ -oneDivSucc n := not_le.mpr (neg_lt_zero.mpr (oneDivSucc_pos n))
    simp [stepFn, this]
  have hcomp : Tendsto (fun n : ℕ => stepFn (-oneDivSucc n)) atTop (nhds (stepFn 0)) :=
    h.tendsto.comp hseq
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (stepFn 0)) := by
    simpa [hval] using hcomp
  have : stepFn 0 = 0 := tendsto_nhds_unique hzero tendsto_const_nhds
  simp [stepFn] at this

/-!
## Case R04 — swapped quantifiers for sequential limits

MATHEMATICAL INTENT: `u n → L` means: for every `ε > 0` there exists
`N` such that every later term is within `ε` of `L`.
DEFECTIVE CANDIDATE:
  `∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - L| < ε`
EXACT DEFECT: the `∃ n` is inside the `∀ N`, so the statement only
says that `L` is approached infinitely often, not eventually.
CORRECTED LEAN STATEMENT: `∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - L| < ε`,
i.e. `Tendsto u atTop (nhds L)`.
WHY THE CORRECTION IS FAITHFUL: it restores the standard quantifier
order. The oscillating sequence `(-1)^n` is infinitely often near `1`
but does not tend to `1`.
-/
def infinitelyOftenNear (u : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |u n - L| < ε

def oscillating (n : ℕ) : ℝ := (-1 : ℝ) ^ n

theorem oscillating_infinitely_often_one : infinitelyOftenNear oscillating 1 := by
  intro ε hε N
  refine ⟨2 * N, Nat.le_mul_of_pos_left N (by norm_num : (0 : ℕ) < 2), ?_⟩
  have hEven : Even (2 * N) := even_two_mul N
  simp [oscillating, hEven.neg_one_pow, hε]

theorem not_tendsto_oscillating_one : ¬ Tendsto oscillating atTop (nhds 1) := by
  intro h
  rw [Filters.tendsto_iff_metric_epsilon] at h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have hodd := hN (2 * N + 1) (by lia)
  have : Odd (2 * N + 1) := odd_two_mul_add_one N
  simp [oscillating, this.neg_one_pow] at hodd
  norm_num at hodd

/-!
## Case R05 — compactness of an open interval

MATHEMATICAL INTENT: the unit interval used for extreme-value
arguments is compact.
DEFECTIVE CANDIDATE:
  `IsCompact (Ioo (0 : Real) 1)`
EXACT DEFECT: a nonempty open interval in `Real` is not compact.
CORRECTED LEAN STATEMENT: `IsCompact (Icc (0 : Real) 1)` and
`¬ IsCompact (Ioo (0 : Real) 1)`.
WHY THE CORRECTION IS FAITHFUL: extreme-value theorems need a compact
domain; `[0, 1]` is compact and `(0, 1)` is not.
-/
theorem isCompact_unit_Icc : IsCompact (Icc (0 : ℝ) 1) :=
  isCompact_Icc

theorem not_isCompact_unit_Ioo : ¬ IsCompact (Ioo (0 : ℝ) 1) := by
  rw [isCompact_Ioo_iff]
  norm_num

/-!
## Case R06 — closure of an open interval without `a ≠ b`

MATHEMATICAL INTENT: the closure of `(a, b)` is `[a, b]`.
DEFECTIVE CANDIDATE:
  `∀ a b : Real, closure (Ioo a b) = Icc a b`
EXACT DEFECT: if `a = b` then `Ioo a a = ∅` while `Icc a a = {a}`.
CORRECTED LEAN STATEMENT: `a ≠ b → closure (Ioo a b) = Icc a b`.
WHY THE CORRECTION IS FAITHFUL: it keeps the identity exactly when
the open interval is nonempty or the reverse-ordered empty case with
`a ≠ b` (then both sides are empty after `closure_Ioo`).
-/
theorem closure_Ioo_of_eq (a : ℝ) : closure (Ioo a a) = (∅ : Set ℝ) := by
  simp

theorem Icc_of_eq (a : ℝ) : Icc a a = ({a} : Set ℝ) := by
  simp

theorem closure_Ioo_ne_Icc_of_eq (a : ℝ) : closure (Ioo a a) ≠ Icc a a := by
  simp

theorem closure_Ioo_of_ne {a b : ℝ} (hab : a ≠ b) : closure (Ioo a b) = Icc a b :=
  closure_Ioo hab

/-!
## Case R07 — wrong filter for a sequential limit

MATHEMATICAL INTENT: a sequence indexed by `ℕ` tends to `L` as
`n → ∞`.
DEFECTIVE CANDIDATE:
  `Tendsto u (nhds 0) (nhds L)` for `u : ℕ → Real`
EXACT DEFECT: `nhds 0` is a filter on `Real`, so the statement is
type-incorrect for a sequence. Even after coercing the index, `nhds 0`
describes a real variable near `0`, not an index going to infinity.
CORRECTED LEAN STATEMENT: `Tendsto u atTop (nhds L)` for sequences,
and `Tendsto (fun x : Real => x^{-1}) atTop (nhds 0)` for a real
variable tending to `+∞`.
WHY THE CORRECTION IS FAITHFUL: `atTop` is the filter of cofinal
tails, which is the Lean encoding of `n → ∞`.
-/
theorem sequence_limit_uses_atTop {u : ℕ → ℝ} {L : ℝ} :
    Tendsto u atTop (nhds L) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - L| < ε :=
  Filters.tendsto_iff_metric_epsilon u L

theorem inv_tendsto_atTop_nhds_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero

/-!
## Case R08 — pointwise versus uniform convergence

MATHEMATICAL INTENT: `f_n → 0` uniformly means one `N` works for all
`x` at once.
DEFECTIVE CANDIDATE:
  interpreting `∀ x, Tendsto (fun n => f n x) atTop (nhds 0)` as
  uniform convergence.
EXACT DEFECT: the `∀ x` is outside `Tendsto`, so each `x` may have its
own tail. That is pointwise convergence.
CORRECTED LEAN STATEMENT: pointwise convergence of the spike sequence,
together with failure of `TendstoUniformly`.
WHY THE CORRECTION IS FAITHFUL: `TendstoUniformly` places the `∀ x`
inside the eventual quantifier.
-/
def spike (n : ℕ) (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 / (n + 1 : ℝ) then 1 else 0

theorem spike_eq_zero_of_nonpos {n : ℕ} {x : ℝ} (hx : x ≤ 0) : spike n x = 0 := by
  unfold spike
  rw [if_neg]
  exact fun h => hx.not_gt h.1

theorem spike_eq_zero_of_large {n : ℕ} {x : ℝ} (_hx : 0 < x)
    (hle : 1 / (n + 1 : ℝ) ≤ x) : spike n x = 0 := by
  unfold spike
  rw [if_neg]
  exact fun h => (not_lt.mpr hle) h.2

theorem spike_eq_one {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hlt : x < 1 / (n + 1 : ℝ)) : spike n x = 1 := by
  unfold spike
  rw [if_pos ⟨hx, hlt⟩]

theorem spike_pointwise (x : ℝ) :
    Tendsto (fun n : ℕ => spike n x) atTop (nhds 0) := by
  rcases le_or_gt x 0 with hx | hx
  · have : (fun n : ℕ => spike n x) = fun _ => 0 :=
      funext fun _ => spike_eq_zero_of_nonpos hx
    simp [this]
  · have hEv : ∀ᶠ n : ℕ in atTop, spike n x = 0 := by
      rw [eventually_atTop]
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / x)
      refine ⟨N, fun n hn => ?_⟩
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have hle : 1 / (n + 1 : ℝ) ≤ x := by
        rw [one_div_le hpos hx]
        have : (1 : ℝ) / x < N := hN
        have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
        linarith
      exact spike_eq_zero_of_large hx hle
    exact Tendsto.congr' (hEv.mono fun _ h => h.symm) tendsto_const_nhds

theorem not_tendstoUniformly_spike :
    ¬ TendstoUniformly spike (fun _ : ℝ => (0 : ℝ)) atTop := by
  intro h
  rw [Metric.tendstoUniformly_iff] at h
  have hε := h (1 / 2) (by norm_num)
  rw [eventually_atTop] at hε
  obtain ⟨N, hN⟩ := hε
  let x : ℝ := 1 / (2 * (N + 1 : ℝ))
  have hxpos : 0 < x := by
    unfold x
    positivity
  have hxlt : x < 1 / (N + 1 : ℝ) := by
    unfold x
    have hpos : (0 : ℝ) < N + 1 := by positivity
    rw [one_div_lt_one_div (by positivity) hpos]
    linarith
  have hspike : spike N x = 1 := spike_eq_one hxpos hxlt
  have hdist := hN N le_rfl x
  simp [hspike] at hdist
  norm_num at hdist

/-!
## Case R09 — existence of a limit versus a named limit

MATHEMATICAL INTENT: the constant sequence `2` converges to `2`.
DEFECTIVE CANDIDATE:
  `∃ L, Tendsto (fun _ : ℕ => (2 : Real)) atTop (nhds L)`
  offered as a formalization of "the sequence tends to `0`".
EXACT DEFECT: existence of some limit is weaker than convergence to a
specified value.
CORRECTED LEAN STATEMENT: the sequence tends to `2` and does not tend
to `0`.
WHY THE CORRECTION IS FAITHFUL: the intended limit is part of the
claim, not an existentially bound variable.
-/
theorem const_two_tendsto_two :
    Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
  tendsto_const_nhds

theorem const_two_has_a_limit :
    ∃ L : ℝ, Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds L) :=
  ⟨2, const_two_tendsto_two⟩

theorem const_two_not_tendsto_zero :
    ¬ Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 0) := by
  intro h
  have := tendsto_nhds_unique h const_two_tendsto_two
  norm_num at this

/-!
## Case R10 — continuity does not imply uniform continuity on `Real`

MATHEMATICAL INTENT: `x |-> x^2` is continuous, and uniformly
continuous on compact intervals.
DEFECTIVE CANDIDATE:
  `Continuous (fun x : Real => x ^ 2) → UniformContinuous (fun x : Real => x ^ 2)`
EXACT DEFECT: the conclusion is stronger than the hypothesis. Global
uniform continuity on `Real` fails for `x^2`.
CORRECTED LEAN STATEMENT: `x^2` is continuous, not uniformly
continuous on `Real`, and uniformly continuous on every `[a, b]`.
WHY THE CORRECTION IS FAITHFUL: Heine–Cantor supplies uniform
continuity only after a compactness assumption.
-/
theorem continuous_sq : Continuous fun x : ℝ => x ^ 2 := by
  fun_prop

theorem not_uniformContinuous_sq : ¬ UniformContinuous fun x : ℝ => x ^ 2 := by
  rw [Metric.uniformContinuous_iff]
  intro h
  obtain ⟨δ, hδ, hδmap⟩ := h 1 one_pos
  let x : ℝ := 1 / δ
  let y : ℝ := x + δ / 2
  have hxpos : 0 < x := one_div_pos.mpr hδ
  have hydiff : y - x = δ / 2 := by simp [y]
  have hdist : dist x y < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hδ.le])]
    linarith
  have hsq : 1 ≤ dist (x ^ 2) (y ^ 2) := by
    have hprod : dist (x ^ 2) (y ^ 2) = |x - y| * |x + y| := by
      rw [Real.dist_eq, sq_sub_sq, abs_mul, mul_comm]
    have hsum : x + y = 2 / δ + δ / 2 := by
      simp [y, x]; ring
    rw [hprod, abs_sub_comm, abs_of_nonneg (by linarith [hδ.le] : 0 ≤ y - x),
      abs_of_nonneg (by nlinarith : 0 ≤ x + y), hydiff, hsum]
    have : δ / 2 * (2 / δ + δ / 2) = 1 + δ ^ 2 / 4 := by
      field_simp
      ring
    rw [this]
    nlinarith
  have : dist (x ^ 2) (y ^ 2) < 1 := hδmap hdist
  linarith

theorem uniformContinuousOn_sq_Icc (a b : ℝ) :
    UniformContinuousOn (fun x : ℝ => x ^ 2) (Icc a b) :=
  isCompact_Icc.uniformContinuousOn_of_continuous continuous_sq.continuousOn

end

end AnalysisFormalization.ReviewerCases
