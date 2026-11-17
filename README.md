# Bias-variance decomposition in Lean 4

Authors: Henry O'Connor, Ari Aceves, Nick Pierce, Milena Yared

**Goal.** Formalize the bias-variance decomposition of mean squared error.

**Main result** (`BiasVariance.bias_variance` in `BiasVariance/Basic.lean`): for a
probability space `(Ω, μ)`, an estimator `X : Ω → ℝ` with `MemLp X 2 μ`, and a
parameter `θ : ℝ`,

    E[(X - θ)^2] = Var(X) + (E[X] - θ)^2.

Corollaries: `mse_eq_variance_of_unbiased`, `variance_le_mse`.

**External inputs.** No additional external axioms are used beyond the stated
theorem hypotheses and the standard Lean/mathlib foundations.

**Files.** All the mathematics is in `BiasVariance/Basic.lean`.
`BiasVariance.lean` just imports it. `lean-toolchain` and `lake-manifest.json`
pin the Lean and mathlib versions.

**Build.**
1. Install Lean via elan: https://lean-lang.org/install/
2. In the project folder, run:
```
lake exe cache get
lake build
```