import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilPoleAtOne
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilRectangleDecompositionMult
import RequestProject.WeilRectangleResidueSumFull
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilFinalAssembly

/-!
# Discharge of `rectangleResidueIdentity_target β` at σL = -1, σR = 2

Applies `rectResidueTheorem_multi_pole_unconditional` using the full
decomposition `weilIntegrand_eq_polar_plus_global_full` to produce the
finite-T rectangle residue identity.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open Contour

/-- **`weilRemainderGlobalFull` is differentiable on the closed rectangle** at
`σL = -1, σR = 2`, for the cosh-pair Gauss test, for any compatible (Z, order)
covering all nontrivial zeros strictly inside. -/
theorem weilRemainderGlobalFull_differentiableOn_rect_neg_one_two
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (T : ℝ) (_hT : 0 < T)
    (hh_an : ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T), AnalyticAt ℂ h s)
    (hζ_ne_off_Z : ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T),
        s ∉ Z → s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z)
      (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  by_cases hsZ : s ∈ Z
  · exact (weilRemainderGlobalFull_analyticAt_zero hB hZ_ne_one hh1 h1_not_Z hh_an_Z hsZ
      ).differentiableAt.differentiableWithinAt
  · by_cases hs1 : s = 1
    · subst hs1
      exact (weilRemainderGlobalFull_analyticAt_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z
        ).differentiableAt.differentiableWithinAt
    · have hζ_ne : riemannZeta s ≠ 0 := hζ_ne_off_Z s hs hsZ hs1
      have hh_s : AnalyticAt ℂ h s := hh_an s hs
      exact (weilRemainderGlobalFull_analyticAt_off_poles hB hZ_ne_one hh1 h1_not_Z hh_an_Z
        hs1 hsZ hζ_ne hh_s).differentiableAt.differentiableWithinAt

#print axioms weilRemainderGlobalFull_differentiableOn_rect_neg_one_two

end FinalAssembly
end WeilPositivity
end ZD

end
