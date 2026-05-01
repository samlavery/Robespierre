import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour

/-!
# Pair Test Continuity and Boundary Values

Unconditional lemmas about the boundary behavior of `pair_cosh_gauss_test β`.
Supporting infrastructure for IBP machinery.

## Delivered

* `pair_cosh_gauss_test_continuous` — the pair test is continuous on `ℝ`.
* `pair_cosh_gauss_test_at_zero` — `pair_cosh_gauss_test β 0 = 0`.
* `pair_cosh_gauss_test_tendsto_zero_atTop` — `pair_cosh_gauss_test β t → 0` as `t → ∞`.

All axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Pair test is continuous on ℝ.** Uses the sinh² factorization for a clean
compositional proof. -/
theorem pair_cosh_gauss_test_continuous (β : ℝ) :
    Continuous (pair_cosh_gauss_test β) := by
  have h_eq : pair_cosh_gauss_test β =
      fun t => 4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
          Real.sinh ((β - 1/2) * t)^2 * (ψ_gaussian t)^2 := by
    funext t; exact pair_cosh_gauss_test_sinh_factor β t
  rw [h_eq]
  unfold ψ_gaussian
  fun_prop

/-- **Pair test vanishes at t = 0.** By the sinh² factorization: each sinh²(c·t)
vanishes at t = 0, hence the product is zero. -/
theorem pair_cosh_gauss_test_at_zero (β : ℝ) : pair_cosh_gauss_test β 0 = 0 := by
  rw [pair_cosh_gauss_test_sinh_factor β 0]
  -- 4 · sinh²((1/2 - π/6) · 0) · sinh²((β - 1/2) · 0) · (ψ_gaussian 0)²
  -- = 4 · sinh²(0) · sinh²(0) · ψ(0)²
  -- = 4 · 0 · 0 · 1 = 0.
  simp [Real.sinh_zero]

#print axioms pair_cosh_gauss_test_continuous
#print axioms pair_cosh_gauss_test_at_zero

/-- **Pair test as a cast to ℂ is O(exp(-t)) at infinity.** Direct via the five-
term cosh expansion and `coshGauss_isBigO_exp_neg_atTop`. -/
theorem pair_cosh_gauss_test_isBigO_exp_neg_atTop (β : ℝ) :
    (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
  have h_expand : (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        ((1/2 : ℝ) : ℂ) * ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)
        + ((1/2 : ℝ) : ℂ) *
          ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)
        - ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)
        - ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)
        + ((Real.cosh (0 * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) := by
    funext t
    rw [pair_cosh_gauss_test_cosh_expansion β t]
    simp [Real.cosh_zero]
    push_cast
    ring
  rw [h_expand]
  have h1 := coshGauss_isBigO_exp_neg_atTop (2*β - Real.pi/3)
  have h2 := coshGauss_isBigO_exp_neg_atTop (2 - Real.pi/3 - 2*β)
  have h3 := coshGauss_isBigO_exp_neg_atTop (1 - Real.pi/3)
  have h4 := coshGauss_isBigO_exp_neg_atTop (2*β - 1)
  have h5 := coshGauss_isBigO_exp_neg_atTop 0
  exact ((((h1.const_mul_left _).add (h2.const_mul_left _)).sub h3).sub h4).add h5

/-- **Pair test tendsto 0 at ∞.** Combining the O(exp(-t)) bound with
`Real.exp_neg → 0` at infinity. -/
theorem pair_cosh_gauss_test_tendsto_zero_atTop (β : ℝ) :
    Filter.Tendsto (pair_cosh_gauss_test β) atTop (nhds 0) := by
  -- Recast via the complex IsBigO: norm bound gives the real tendsto.
  have h_bigO := pair_cosh_gauss_test_isBigO_exp_neg_atTop β
  have h_exp : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) := by
    have h_neg : Filter.Tendsto (fun t : ℝ => -t) atTop Filter.atBot :=
      tendsto_neg_atTop_atBot
    exact Real.tendsto_exp_atBot.comp h_neg
  have h_complex : Filter.Tendsto
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) atTop (nhds 0) :=
    h_bigO.trans_tendsto h_exp
  -- Extract the real limit.
  have h_re : Filter.Tendsto
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ).re) atTop (nhds 0) := by
    have := Complex.continuous_re.continuousAt.tendsto.comp h_complex
    simpa using this
  -- ((x : ℝ) : ℂ).re = x.
  have h_simp : (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ).re) =
      pair_cosh_gauss_test β := by
    funext t; exact Complex.ofReal_re _
  rw [h_simp] at h_re
  exact h_re

#print axioms pair_cosh_gauss_test_isBigO_exp_neg_atTop
#print axioms pair_cosh_gauss_test_tendsto_zero_atTop

/-- **Pair test differentiability.** `pair_cosh_gauss_test β` is differentiable
on all of ℝ — product of smooth functions via the sinh² factorization. -/
theorem pair_cosh_gauss_test_differentiable (β : ℝ) :
    Differentiable ℝ (pair_cosh_gauss_test β) := by
  have h_eq : pair_cosh_gauss_test β =
      fun t => 4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
          Real.sinh ((β - 1/2) * t)^2 * (ψ_gaussian t)^2 := by
    funext t; exact pair_cosh_gauss_test_sinh_factor β t
  rw [h_eq]
  unfold ψ_gaussian
  fun_prop

/-- **Pair test `ContDiff` (smooth to any order).** -/
theorem pair_cosh_gauss_test_contDiff (β : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (pair_cosh_gauss_test β) := by
  have h_eq : pair_cosh_gauss_test β =
      fun t => 4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
          Real.sinh ((β - 1/2) * t)^2 * (ψ_gaussian t)^2 := by
    funext t; exact pair_cosh_gauss_test_sinh_factor β t
  rw [h_eq]
  unfold ψ_gaussian
  fun_prop

#print axioms pair_cosh_gauss_test_differentiable
#print axioms pair_cosh_gauss_test_contDiff

end Contour
end WeilPositivity
end ZD

end
