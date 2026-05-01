import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour

/-!
# G-3: β ↔ 1−β Reflection Symmetry of the Pair Cosh-Gauss Test

## Geometric identity of the double-cosh kernel

The double-cosh kernel pair at axes `π/6` and `1 − π/6` is reflection-symmetric
under `β ↔ 1 − β`: the substitution swaps the two kernels:

* `coshDetectorLeft (1−β) t = coshDetectorRight β t`
* `coshDetectorRight (1−β) t = coshDetectorLeft β t`

Both already proved in `ZetaZeroDefs.lean` as `coshDetector_reflect_swap`
and `coshDetector_reflect_swap'` (pure `cosh_neg` algebra — the kernels are
centered reflection-symmetrically around `β = 1/2`).

## Lift to the higher-level observables (this file)

We propagate the double-cosh reflection to the Weil-contour machinery:

* `pairDetectorSqDiff_beta_reflection` — `(K_L − K_R)²` invariant under swap
  (squaring kills the sign).
* `pair_cosh_gauss_test_beta_reflection` — the pair-cosh-Gauss test integrand
  is invariant (the Gaussian weight has no β-dependence).
* `gaussianPairDefect_beta_reflection` — integrating the above.
* `pairTestMellin_beta_reflection` — Mellin-transforming the above.

## What this is NOT

Pure geometric symmetry arising from π/6 and 1−π/6 being FE-reflection-symmetric
around the fixed point 1/2. Does **not** touch `ζ`, does **not** assert
arch = prime, does **not** collapse to RH. The β-reflection is a property of
the *test function*; applying it to the zero-sum side only gives
`∑_ρ pairTestMellin β ρ = ∑_ρ pairTestMellin (1−β) ρ`, matching the FE-symmetry
of ζ-zeros (ρ ↔ 1−ρ), not forcing ρ.re = 1/2.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Real Complex MeasureTheory Set ZetaDefs

noncomputable section

namespace ZD

/-- **G-3a: β ↔ 1−β reflection of `pairDetectorSqDiff`.**

The reflection swaps the two cosh kernels (`coshDetector_reflect_swap` and
`coshDetector_reflect_swap'`), which flips the sign inside the squared
difference — killed by squaring. -/
theorem pairDetectorSqDiff_beta_reflection (β t : ℝ) :
    pairDetectorSqDiff (1 - β) t = pairDetectorSqDiff β t := by
  unfold pairDetectorSqDiff
  rw [coshDetector_reflect_swap β t, coshDetector_reflect_swap' β t]
  ring

#print axioms pairDetectorSqDiff_beta_reflection

/-- **G-3b: β ↔ 1−β reflection of `gaussianPairDefect`.**

Immediate from `pairDetectorSqDiff_beta_reflection` — the Gaussian weight
`ψ_gaussian²` has no β-dependence. -/
theorem gaussianPairDefect_beta_reflection (β : ℝ) :
    gaussianPairDefect (1 - β) = gaussianPairDefect β := by
  unfold gaussianPairDefect
  congr 1
  funext t
  rw [pairDetectorSqDiff_beta_reflection]

#print axioms gaussianPairDefect_beta_reflection

end ZD

namespace ZD.WeilPositivity

/-- **G-3c: β ↔ 1−β reflection of `pair_cosh_gauss_test`.**

Direct consequence of `pairDetectorSqDiff_beta_reflection` since
`pair_cosh_gauss_test β t = pairDetectorSqDiff β t · (ψ_gaussian t)²`. -/
theorem pair_cosh_gauss_test_beta_reflection (β t : ℝ) :
    pair_cosh_gauss_test (1 - β) t = pair_cosh_gauss_test β t := by
  unfold pair_cosh_gauss_test
  rw [ZD.pairDetectorSqDiff_beta_reflection]

#print axioms pair_cosh_gauss_test_beta_reflection

end ZD.WeilPositivity

namespace ZD.WeilPositivity.Contour

/-- **G-3d: β ↔ 1−β reflection of `pairTestMellin`.**

The Mellin transform of a β-reflection-invariant integrand is itself
β-reflection-invariant (at every `s ∈ ℂ`). Closes the G-3 chain at the
Weil-contour observable level. -/
theorem pairTestMellin_beta_reflection (β : ℝ) (s : ℂ) :
    pairTestMellin (1 - β) s = pairTestMellin β s := by
  unfold pairTestMellin
  congr 1
  funext t
  rw [pair_cosh_gauss_test_beta_reflection]

#print axioms pairTestMellin_beta_reflection

end ZD.WeilPositivity.Contour

end
