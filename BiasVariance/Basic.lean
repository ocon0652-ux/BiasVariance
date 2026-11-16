import Mathlib

/-!
# Bias-variance decomposition of mean squared error

Setting: `μ` is a probability measure on `Ω`, `X : Ω → ℝ` is an estimator
(a random variable) with finite second moment, and `θ : ℝ` is the true parameter.

Main result (`bias_variance`):
  E[(X - θ)^2] = Var(X) + (E[X] - θ)^2.

No external axioms are used.
-/

open MeasureTheory ProbabilityTheory

namespace BiasVariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Variance written as `E[X^2] - (E[X])^2` with explicit integrals. -/
lemma variance_eq_integral_sq_sub (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    Var[X; μ] = ∫ ω, X ω ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2 := by
  simpa [Pi.pow_apply] using variance_eq_sub hX

/-- Expansion of the second moment about `θ`. -/
lemma integral_sq_sub_const (X : Ω → ℝ) (hX : MemLp X 2 μ) (θ : ℝ) :
    ∫ ω, (X ω - θ) ^ 2 ∂μ
      = ∫ ω, X ω ^ 2 ∂μ - 2 * θ * ∫ ω, X ω ∂μ + θ ^ 2 := by
  have h1 : Integrable X μ := hX.integrable one_le_two
  have h2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have h3 : Integrable (fun ω => 2 * θ * X ω) μ := h1.const_mul (2 * θ)
  have hfun : (fun ω => (X ω - θ) ^ 2)
      = fun ω => (X ω ^ 2 - 2 * θ * X ω) + θ ^ 2 := by
    funext ω; ring
  have e1 : ∫ ω, ((X ω ^ 2 - 2 * θ * X ω) + θ ^ 2) ∂μ
      = ∫ ω, (X ω ^ 2 - 2 * θ * X ω) ∂μ + ∫ _ω, θ ^ 2 ∂μ :=
    integral_add (h2.sub h3) (integrable_const _)
  have e2 : ∫ ω, (X ω ^ 2 - 2 * θ * X ω) ∂μ
      = ∫ ω, X ω ^ 2 ∂μ - ∫ ω, 2 * θ * X ω ∂μ :=
    integral_sub h2 h3
  have e3 : ∫ ω, 2 * θ * X ω ∂μ = 2 * θ * ∫ ω, X ω ∂μ :=
    integral_const_mul _ _
  rw [hfun, e1, e2, e3]
  simp

/-- **Bias-variance decomposition.**
`MSE(X, θ) = Var(X) + Bias(X, θ)^2`, where `Bias = E[X] - θ`. -/
theorem bias_variance (X : Ω → ℝ) (hX : MemLp X 2 μ) (θ : ℝ) :
    ∫ ω, (X ω - θ) ^ 2 ∂μ = Var[X; μ] + (∫ ω, X ω ∂μ - θ) ^ 2 := by
  rw [integral_sq_sub_const X hX θ, variance_eq_integral_sq_sub X hX]
  ring

/-- Corollary: for an unbiased estimator, MSE equals the variance. -/
theorem mse_eq_variance_of_unbiased (X : Ω → ℝ) (hX : MemLp X 2 μ) (θ : ℝ)
    (hunb : ∫ ω, X ω ∂μ = θ) :
    ∫ ω, (X ω - θ) ^ 2 ∂μ = Var[X; μ] := by
  rw [bias_variance X hX θ, hunb]
  simp

/-- Corollary: MSE is at least the variance. -/
theorem variance_le_mse (X : Ω → ℝ) (hX : MemLp X 2 μ) (θ : ℝ) :
    Var[X; μ] ≤ ∫ ω, (X ω - θ) ^ 2 ∂μ := by
  rw [bias_variance X hX θ]
  nlinarith [sq_nonneg (∫ ω, X ω ∂μ - θ)]

end BiasVariance
