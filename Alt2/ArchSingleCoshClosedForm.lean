import Mathlib
import RequestProject.WeilReflectedPrimeVanishingWeilside

/-!
# IBP-transformed closed form for `archSingleCosh c`
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour
open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ArchSingleCoshClosedForm

/-- **IBP×2 form of `archSingleCosh c` at `σ = 2`.**

Substituting the proved
`coshGaussMellin c (2 + it) = 1 / ((2 + it)(3 + it))
  · mellin (coshGaussDeriv2Val c) (4 + it)`
into the integrand of `archSingleCosh c`, the integral re-expresses on
the vertical line `σ = 4`, where Stirling's bound on
`Γℝ' / Γℝ` is sharper.  This is the natural starting form for any
explicit-formula computation that uses `StirlingBound`.

Axiom footprint matches `h1_coshGaussMellin_ibp_twice`. -/
theorem archSingleCosh_ibp_at_two (c : ℝ) :
    archSingleCosh c =
      ∫ t : ℝ,
        (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
            ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
            (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
        (1 /
            (((2 : ℂ) + (t : ℂ) * I) *
              (((2 : ℂ) + (t : ℂ) * I) + 1)) *
          mellin
            (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
            ((4 : ℂ) + (t : ℂ) * I)) := by
  unfold archSingleCosh
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only []
  have hs_re : (0 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  have h_ibp := h1_coshGaussMellin_ibp_twice c hs_re
  have h_eq : ((2 : ℂ) + (t : ℂ) * I) + 2 = (4 : ℂ) + (t : ℂ) * I := by ring
  rw [h_ibp, h_eq]

#print axioms archSingleCosh_ibp_at_two

end ArchSingleCoshClosedForm
end WeilPositivity
end ZD

end
