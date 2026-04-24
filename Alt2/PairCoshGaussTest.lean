import Mathlib
import RequestProject.GaussianDetectorPair

/-!
# Pair Cosh-Gauss Test Function — unconditional

Sugar-only replacement for the test function previously sitting in
`WeilPairFormula.lean`.  No sorries, no consumers of sorries; this file
is strictly the pointwise product `pairDetectorSqDiff · ψ_gaussian²`
renamed, together with the three trivial unconditional theorems about
it.

The load-bearing classical-Weil-positivity theorem that used to live in
`WeilPairFormula.lean` has been deleted.  That deletion is intentional:
it carried a tracked sorry which was the wrong Weil-agent target
(see `feedback_excess_sum_does_not_vanish.md` memorial).
-/

open Real MeasureTheory Set

noncomputable section

namespace ZD
namespace WeilPositivity

/-- **Pair cosh-Gauss test.**  The pointwise product of the pair
detector squared difference and the squared Gaussian weight.  This is
the integrand of `gaussianPairDefect β`. -/
def pair_cosh_gauss_test (β : ℝ) : ℝ → ℝ :=
  fun t => pairDetectorSqDiff β t * (ψ_gaussian t)^2

/-- **Pointwise non-negativity.**  Product of two non-negative factors. -/
theorem pair_cosh_gauss_test_nonneg (β : ℝ) (t : ℝ) :
    0 ≤ pair_cosh_gauss_test β t := by
  unfold pair_cosh_gauss_test pairDetectorSqDiff
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Sinh-factored form.**  Lift of `pairDetectorSqDiff_sinh_factor`
through the `(ψ_gaussian t)^2` factor. -/
theorem pair_cosh_gauss_test_sinh_factor (β t : ℝ) :
    pair_cosh_gauss_test β t =
      4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
          Real.sinh ((β - 1/2) * t)^2 * (ψ_gaussian t)^2 := by
  unfold pair_cosh_gauss_test
  rw [pairDetectorSqDiff_sinh_factor]

/-- **Integral equals `gaussianPairDefect`.**  `rfl` against the defect
definition in `GaussianDetectorPair.lean`. -/
theorem pair_cosh_gauss_test_integral_eq_gaussianPairDefect (β : ℝ) :
    ∫ t in Ioi (0:ℝ), pair_cosh_gauss_test β t = gaussianPairDefect β := by
  unfold pair_cosh_gauss_test gaussianPairDefect
  rfl

end WeilPositivity
end ZD

end
