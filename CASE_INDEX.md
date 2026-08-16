# Case index

Every row names a compiling declaration. Helper lemmas that exist only
to support a listed case are omitted.

Difficulty: **F** foundational, **I** intermediate, **A** advanced.

| Case | Topic | Lean API | Important assumptions | Failure mode addressed | Diff. | Source |
| --- | --- | --- | --- | --- | --- | --- |
| F01 | Triangle inequality | `abs_add_le` | none | dropping absolute values on the right | F | `Inequalities.lean` / `triangle_inequality` |
| F02 | Absolute-value neighborhood | `abs_lt` | none; both sides false if `ε ≤ 0` | writing `\|x\| < ε ↔ x < ε` | F | `Inequalities.lean` / `abs_lt_iff` |
| F03 | Positive quotient | `div_pos` | `0 < a` and `0 < b` | omitting positivity of the denominator | F | `Inequalities.lean` / `div_pos_of_pos_pos` |
| F04 | `ℕ → ℝ` order coercion | `Nat.cast_le` | none | treating a `ℕ` bound as already a real | F | `Inequalities.lean` / `nat_cast_le_iff` |
| F12 | Division cancellation | `div_mul_cancel₀` | `b ≠ 0` | `a / b * b = a` at `b = 0` | F | `Inequalities.lean` / `div_mul_cancel_of_ne` |
| I01 | Linear combination bound | `abs_add_le`, `abs_mul` | none | dropping `\|a\|`, `\|b\|` | I | `Inequalities.lean` / `abs_linear_le` |
| I02 | Reverse triangle | `abs_abs_sub_abs_le` | none | omitting the outer absolute value | I | `Inequalities.lean` / `reverse_triangle` |
| F05 | Constant sequence bounded | `BoundedSeq` | none | `∀ n, ∃ M` instead of `∃ M, ∀ n` | F | `Sequences.lean` / `boundedSeq_const` |
| F06 | `1/(n+1)` bounded | `BoundedSeq`, `oneDivSucc` | `n + 1 ≠ 0` by construction | `1/n` at `n = 0` | F | `Sequences.lean` / `boundedSeq_oneDivSucc` |
| I03 | Monotone `1 - 1/(n+1)` | `Monotone`, `Antitone` | none | reversing the inequality after subtraction | I | `Sequences.lean` / `monotone_one_sub_oneDivSucc` |
| I04 | Eventual `1/(n+1) < ε` | `eventually_atTop`, `exists_nat_gt` | `0 < ε` | infinitely-often quantifiers | I | `Sequences.lean` / `eventually_oneDivSucc_lt` |
| I05 | Constant sequence limit | `tendsto_const_nhds` | none | using `nhds` as the domain filter | I | `Sequences.lean` / `tendsto_const_seq` |
| A01 | ε-N ↔ `Tendsto` | `Metric.tendsto_atTop`, `Real.dist_eq` | `u : ℕ → ℝ` | wrong filter or swapped quantifiers | A | `Filters.lean` / `tendsto_iff_metric_epsilon` |
| I06 | `1/(n+1) → 0` | `Tendsto`, `atTop`, `nhds` | none | treating `1/x` as a real germ at `0` | I | `Filters.lean` / `tendsto_oneDivSucc` |
| I07 | Membership in `atTop` | `mem_atTop_sets` | `s : Set ℕ` | confusing `atTop` with `nhds` | I | `Filters.lean` / `mem_atTop_iff` |
| I08 | Sum of limits | `Tendsto.add` | two `Tendsto` hypotheses | quotient without a nonzero limit | I | `Filters.lean` / `tendsto_add_sequences` |
| A07 | Unique sequential limits | `tendsto_nhds_unique` | Hausdorff `ℝ` | `∃ L` as if it named the limit | A | `Filters.lean` / `tendsto_unique_real` |
| F07 | Identity continuous | `continuous_id` | none | using a subtype identity on all of `ℝ` | F | `Continuity.lean` / `continuous_id_real` |
| F08 | Constant continuous | `continuous_const` | none | none of mathematical substance | F | `Continuity.lean` / `continuous_const_real` |
| I09 | Continuous composition | `Continuous.comp` | both maps globally continuous | `ContinuousOn` without image landing | I | `Continuity.lean` / `continuous_comp` |
| I10 | Polynomial at a point | `fun_prop`, `Continuous.continuousAt` | none on the point | `ContinuousAt f` with no point | I | `Continuity.lean` / `continuousAt_quadratic` |
| A02 | Inversion off zero | `continuousOn_inv₀` | domain `{0}ᶜ` | `Continuous` of `x⁻¹` on all of `ℝ` | A | `Continuity.lean` / `continuousOn_inv_ne_zero` |
| F09 | Open interval open | `isOpen_Ioo` | none; empty if `b ≤ a` | claiming `Icc` is open | F | `Topology.lean` / `isOpen_Ioo_real` |
| F10 | Closed interval closed | `isClosed_Icc` | none | treating closed as compact | F | `Topology.lean` / `isClosed_Icc_real` |
| I11 | Interior of `[a, b]` | `interior_Icc` | `ℝ` has no min/max | `interior (Icc a b) = Icc a b` | I | `Topology.lean` / `interior_Icc_eq_Ioo` |
| I12 | Closure of `(a, b)` | `closure_Ioo` | `a ≠ b` | identity at `a = b` | I | `Topology.lean` / `closure_Ioo_eq_Icc` |
| I16 | Set ⊆ closure | `subset_closure` | none | confusing subset with equality | I | `Topology.lean` / `subset_closure_self` |
| I20 | Open set is a neighborhood | `IsOpen.mem_nhds` | `U` open and `x ∈ U` | `x ∈ U` without openness | I | `Topology.lean` / `mem_nhds_of_mem_open` |
| I13 | `[a, b]` compact | `isCompact_Icc` | none; empty if `b < a` | compactness of `Ioo a b` | I | `Compactness.lean` / `isCompact_Icc_real` |
| A03 | Continuous image of compact | `IsCompact.image` | `s` compact, `f` continuous | dropping continuity | A | `Compactness.lean` / `isCompact_continuous_image` |
| A04 | Extreme value on `[a, b]` | `IsCompact.exists_isMinOn` | `a ≤ b`, `ContinuousOn f` | EVT on an open interval | A | `Compactness.lean` / `extreme_value_min_Icc` |
| A05 | Heine–Borel on `ℝ` | `Metric.isCompact_iff_isClosed_bounded` | proper metric space `ℝ` | dropping closed or bounded | A | `Compactness.lean` / `heine_borel_real` |
| I14 | Derivative of `id` | `hasDerivAt_id` | none | `deriv` without differentiability | I | `Calculus.lean` / `hasDerivAt_id_real` |
| I15 | Derivative of `x^2` | `hasDerivAt_pow` | none | `n * x^n` instead of `n * x^(n-1)` | I | `Calculus.lean` / `hasDerivAt_sq` |
| I17 | Derivative of `exp` | `Real.hasDerivAt_exp` | none | mixing `Real.exp` and `Complex.exp` | I | `Calculus.lean` / `hasDerivAt_exp_real` |
| A06 | Product rule `x e^x` | `HasDerivAt.mul` | none | product rule as `f' * g'` | A | `Calculus.lean` / `hasDerivAt_mul_id_exp` |
| F11 | LUB of `(-∞, a]` | `isLUB_Iic` | none | `IsGLB (Iic a) a` | F | `OrderBounds.lean` / `isLUB_Iic_real` |
| I18 | Translation strictly monotone | `StrictMono` | none | claiming `c - x` is increasing | I | `OrderBounds.lean` / `strictMono_add_const` |
| I19 | Maximum of `[a, b]` | `isGreatest_Icc` | `a ≤ b` | `IsGreatest (Ioo a b) b` | I | `OrderBounds.lean` / `isGreatest_Icc_real` |
| A08 | Monotone convergence | `tendsto_atTop_ciSup` | `Monotone`, `BddAbove` | boundedness without monotonicity | A | `OrderBounds.lean` / `monotone_bddAbove_tendsto` |
| R01 | Wrong domain for `1/x` | `ContinuousOn`, `¬ Continuous` | domain `{0}ᶜ` | global continuity of inversion | A | `ReviewerCases.lean` / `not_continuous_inv_on_real` |
| R02 | Missing nonnegativity of `sqrt` | `Real.sq_sqrt` | `0 ≤ x` | `(√x)² = x` for `x < 0` | I | `ReviewerCases.lean` / `sqrt_sq_of_nonneg` |
| R03 | `Continuous` vs `ContinuousAt` | `continuous_iff_continuousAt` | a specified point | inferring global from one point | I | `ReviewerCases.lean` / `continuousAt_stepFn_one` |
| R04 | Swapped limit quantifiers | `Tendsto` vs infinitely often | `∃ N, ∀ n ≥ N` | `∀ N, ∃ n ≥ N` | A | `ReviewerCases.lean` / `not_tendsto_oscillating_one` |
| R05 | Compactness of `(0, 1)` | `isCompact_Ioo_iff` | `a < b` implies not compact | `IsCompact (Ioo 0 1)` | A | `ReviewerCases.lean` / `not_isCompact_unit_Ioo` |
| R06 | Closure without `a ≠ b` | `closure_Ioo` | `a ≠ b` | `closure (Ioo a a) = Icc a a` | I | `ReviewerCases.lean` / `closure_Ioo_ne_Icc_of_eq` |
| R07 | Wrong filter for sequences | `atTop` vs `nhds` | sequences use `atTop` | `Tendsto u (nhds 0)` | A | `ReviewerCases.lean` / `sequence_limit_uses_atTop` |
| R08 | Pointwise vs uniform | `Tendsto` vs `TendstoUniformly` | `∀ x` outside vs inside | reading pointwise as uniform | A | `ReviewerCases.lean` / `not_tendstoUniformly_spike` |
| R09 | Existing vs named limit | `tendsto_nhds_unique` | a specified `L` | `∃ L` for “tends to 0” | I | `ReviewerCases.lean` / `const_two_not_tendsto_zero` |
| R10 | Continuity vs uniform continuity | `UniformContinuous`, Heine–Cantor | compact domain for UC | `x^2` uniformly continuous on `ℝ` | A | `ReviewerCases.lean` / `not_uniformContinuous_sq` |
| D01 | API discovery | `#check` of reused lemmas | none | inventing a parallel lemma | F | `Discovery.lean` / `discovered_tendsto_atTop` |

## Counts

| Difficulty | Cases |
| --- | ---: |
| Foundational | 13 |
| Intermediate | 24 |
| Advanced | 14 |
| **Total** | **51** |

| Topic | Cases |
| --- | ---: |
| Inequalities / order-algebra | 7 |
| Sequences | 5 |
| Filters / limits | 5 |
| Continuity | 5 |
| Topology | 6 |
| Compactness | 4 |
| Calculus | 4 |
| Order / bounds | 4 |
| Reviewer / faithfulness | 10 |
| Discovery | 1 |

Topic counts treat each case once, under its primary module.
