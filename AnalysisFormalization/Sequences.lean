/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import AnalysisFormalization.Basic

/-!
# Real sequences

Sequences are functions `ℕ → ℝ`. Boundedness and monotonicity are
stated with mathlib order predicates; convergence is deferred to the
filter module, except for the constant-sequence example.
-/

namespace AnalysisFormalization.Sequences

open Filter AnalysisFormalization

/-!
## Case F05 — a constant sequence is bounded

MATHEMATICAL INTENT: the constant sequence `n ↦ c` is bounded.
LEAN REPRESENTATION: `BoundedSeq (fun _ ↦ c)`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: the explicit bound `|c|` works for every index.
KEY MATHLIB API: `le_rfl` on `|c|`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: quantifying the bound after the index
(`∀ n, ∃ M, |u n| ≤ M`), which is true of every sequence.
-/
theorem boundedSeq_const (c : ℝ) : BoundedSeq fun _ : ℕ ↦ c :=
  ⟨|c|, fun _ => le_rfl⟩

/-!
## Case F06 — `1 / (n + 1)` is bounded

MATHEMATICAL INTENT: `0 < 1/(n+1) ≤ 1`, hence the sequence is bounded.
LEAN REPRESENTATION: `BoundedSeq oneDivSucc`.
ASSUMPTIONS: none; the `+ 1` keeps every denominator nonzero.
PROOF ARCHITECTURE: the uniform bound `1` follows from `n + 1 ≥ 1`.
KEY MATHLIB API: `div_le_one`, `positivity`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing `1 / n` as a function `ℕ → ℝ` and
evaluating at `0`.
-/
theorem boundedSeq_oneDivSucc : BoundedSeq oneDivSucc :=
  ⟨1, fun n => (abs_oneDivSucc n).le.trans (oneDivSucc_le_one n)⟩

/-!
## Case I03 — monotonicity of `1 - 1/(n+1)`

MATHEMATICAL INTENT: `n ↦ 1 - 1/(n+1)` is increasing.
LEAN REPRESENTATION: `Monotone (fun n ↦ 1 - oneDivSucc n)`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: `oneDivSucc` is antitone, and subtracting from a
constant reverses the inequality.
KEY MATHLIB API: `Antitone`, `sub_le_sub_left`, `gcongr`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: claiming *strict* monotonicity without checking
the successor step, or reversing the inequality when subtracting.
-/
theorem antitone_oneDivSucc : Antitone oneDivSucc := by
  intro n m hnm
  unfold oneDivSucc
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [one_div_le_one_div hm hn]
  exact_mod_cast Nat.succ_le_succ hnm

theorem monotone_one_sub_oneDivSucc : Monotone fun n : ℕ ↦ (1 : ℝ) - oneDivSucc n :=
  fun _ _ hnm => sub_le_sub_left (antitone_oneDivSucc hnm) 1

/-!
## Case I04 — an eventual bound for `1/(n+1)`

MATHEMATICAL INTENT: for every `ε > 0` there exists `N` such that
`n ≥ N` implies `|1/(n+1)| < ε`.
LEAN REPRESENTATION: `∀ᶠ n in atTop, |oneDivSucc n| < ε`.
ASSUMPTIONS: `0 < ε`.
PROOF ARCHITECTURE: choose `N` larger than `1/ε` by Archimedeanness.
KEY MATHLIB API: `exists_nat_gt`, `eventually_atTop`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: swapping the quantifiers to
`∀ N, ∃ n ≥ N, |u n| < ε`, which is an infinitely-often statement.
-/
theorem eventually_oneDivSucc_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |oneDivSucc n| < ε := by
  rw [eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hNε : (1 : ℝ) / ε < N := hN
  have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [abs_oneDivSucc, oneDivSucc, one_div_lt hpos hε]
  linarith

/-!
## Case I05 — a constant sequence converges

MATHEMATICAL INTENT: `n ↦ c` converges to `c`.
LEAN REPRESENTATION: `Tendsto (fun _ ↦ c) atTop (nhds c)`.
ASSUMPTIONS: none.
PROOF ARCHITECTURE: reuse `tendsto_const_nhds`.
KEY MATHLIB API: `tendsto_const_nhds`
VALIDATION: compiles in this module.
COMMON FAILURE MODE: writing the limit filter as `atTop` in the
codomain, or using `nhds` on the domain (a sequence is not a
real-variable germ at a finite point).
-/
theorem tendsto_const_seq (c : ℝ) :
    Tendsto (fun _ : ℕ ↦ c) atTop (nhds c) :=
  tendsto_const_nhds

end AnalysisFormalization.Sequences
