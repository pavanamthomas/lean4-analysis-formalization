/-
Copyright (c) 2026 The AnalysisFormalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Shared definitions

Textbook-facing names used across the modules. The surrounding theorems
use current mathlib types (`ℝ`, `Filter`, `Tendsto`, `IsCompact`, …)
rather than a parallel analysis library.
-/

namespace AnalysisFormalization

noncomputable section

/-- Textbook boundedness of a real sequence. Equivalent in intent to
`Bornology.IsBounded (Set.range u)`, but written with an explicit bound. -/
def BoundedSeq (u : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n, |u n| ≤ M

/-- The standard example sequence `n ↦ 1 / (n + 1)`. The shift avoids
division by zero at `n = 0` without changing the limit. -/
def oneDivSucc (n : ℕ) : ℝ := (1 : ℝ) / (n + 1)

lemma oneDivSucc_pos (n : ℕ) : 0 < oneDivSucc n := by
  unfold oneDivSucc
  positivity

lemma oneDivSucc_nonneg (n : ℕ) : 0 ≤ oneDivSucc n :=
  (oneDivSucc_pos n).le

lemma oneDivSucc_le_one (n : ℕ) : oneDivSucc n ≤ 1 := by
  unfold oneDivSucc
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_one hpos]
  exact_mod_cast Nat.le_add_left 1 n

lemma abs_oneDivSucc (n : ℕ) : |oneDivSucc n| = oneDivSucc n :=
  abs_of_pos (oneDivSucc_pos n)

end

end AnalysisFormalization
