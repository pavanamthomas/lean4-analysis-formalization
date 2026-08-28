# Roadmap

Uniform convergence (`TendstoUniformly`) is the obvious gap next to the pointwise limit cases in `Filters.lean`. The counterexample machinery is already there; a positive theorem on a compact domain would pair with the Heine–Cantor note in `ReviewerCases.lean`.

A full Heine–Cantor reconstruction (continuous on compact ⇒ uniformly continuous) is deliberately out of scope for now. The `x^2` on `ℝ` counterexample stays in comments. If that changes, it should be one file, not a scatter of aliases.

Derivatives stop at `id`, `x^2`, `exp`, and `x * exp x`. Chain rule on a composed elementary function is the next calculus row I would add, provided the mathlib `HasDerivAt` API at the pin still matches.
