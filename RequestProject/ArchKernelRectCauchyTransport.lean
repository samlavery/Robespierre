import RequestProject.ArchKernelRectShift
import RequestProject.PairComboResidueAtZero
import RequestProject.WeilArchAtNegOne
import RequestProject.WeilArchPrimeIdentity
import RequestProject.GaussianDetectorPair
import RequestProject.ArchOperatorBound

/-!
# Rectangle Cauchy transport: assembled building blocks (axiom-clean)

The "rectangle Cauchy" identity that the H3 reduction asks for is

```
(∫ t, archIntegrand β 2 t) - (∫ y, archIntegrand β (-1) y)
   = (2π i) · (Res_{s=0} F(s) + Res_{s=1} F(s))
```

where `F(s) := archKernel s · pairTestMellin β s` is the IBP-shifted-form arch
kernel paired with `pairTestMellin β`.

The discharge composes three pieces:

  (P1) Closed-rectangle Cauchy with two interior poles `{0, 1}` excised,
       boundary integrals identified with `2π i · (Res_0 + Res_1)` as
       the excision radii shrink to `0`. Built via mathlib's
       `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
       plus a hand-rolled deformation around interior poles using
       `Complex.differentiableOn_update_limUnder_of_isLittleO`.
  (P2) Top/bottom edge decay as `T → ∞`. Composes Stirling bounds
       (`betaUpperDecay_from_stirling`, `betaLowerDecay_from_stirling`,
       `gamma_stirling_bound`, `stirling_unit_strip`,
       `reflection_norm_product`) with `pairTestMellin_decay_on_strip_neg`
       and the FE identity `archKernel = -ζ'/ζ - ζ'/ζ(1-·)`
       (using `leftOfCriticalStrip_holds`, `rightOfCriticalStrip_holds`).
  (P3) The identification `pairTestMellin β 0 = R β` — discharged
       axiom-clean via `RBetaIdentity.pairTestMellin_at_zero_eq_R_beta`.

This file consolidates the axiom-clean building blocks that the
rectangle-Cauchy identity rests on. Downstream code can refer to
`archDiff_eq_residue_sum_target` and obtain the named boundary
identifications, residue limits, and integrability witnesses below.

## Main results

* `archDiff_eq_residue_sum_target` — Prop statement of the rectangle
  identity in its `pairTestMellin β 0` form (the `R β` form is
  equivalent modulo P3 above).
* `F_at_two_eq_archIntegrand` — `F(2 + iy) = archIntegrand β 2 y`.
* `F_at_neg_one_eq_archIntegrand` — `F(-1 + iy) = archIntegrand β (-1) y`.
* `F_residue_at_zero_eq_neg_pairTestMellin_zero` — `lim_{s → 0, s ≠ 0}
  s · F(s) = -pairTestMellin β 0`.
* `F_residue_at_one_eq_gaussianPairDefect` — `lim_{s → 1, s ≠ 1}
  (s - 1) · F(s) = gaussianPairDefect β`.
* `archIntegrand_at_two_integrable` — `archIntegrand β 2` is Bochner
  integrable on ℝ.
* `archIntegrand_at_neg_one_integrable` — `archIntegrand β (-1)` is
  Bochner integrable on ℝ.

-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelRectCauchyTransport

open ZD.WeilArchKernelResidues
open ZD.WeilPositivity.Contour
open ZD.ArchKernelRectShift

/-! ## The named target -/

/-- **Rectangle-Cauchy target (P3-form).** The identity that closing
the rectangle Cauchy contour for `F = archKernel · pairTestMellin β` on
`[-1, 2] × [-T, T]` (with `T → ∞`) would deliver, expressed in terms of
the residue values `-pairTestMellin β 0` (residue at `s = 0`) and
`gaussianPairDefect β` (residue at `s = 1`).

The right-hand side uses `2π i`, matching the orientation of the
counter-clockwise rectangle contour and the standard residue theorem
sign convention for the difference `(top edge) − (bottom edge)`. -/
def archDiff_eq_residue_sum_target (β : ℝ) : Prop :=
  (∫ t : ℝ, archIntegrand β 2 t) - (∫ y : ℝ, archIntegrand β (-1) y) =
    (2 * ((Real.pi : ℝ) : ℂ)) * I *
      ((-pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ))

/-! ## Axiom-clean building block (1): integrand bridges -/

/-- Right edge: `F(2 + iy) = archIntegrand β 2 y`. Direct re-export of
`F_eq_archIntegrand_at_two`. -/
theorem F_at_two_eq_archIntegrand (β : ℝ) (y : ℝ) :
    pairTestMellin_archKernel_product β ((2 : ℂ) + (y : ℂ) * I)
      = archIntegrand β 2 y :=
  F_eq_archIntegrand_at_two β y

/-- Left edge: `F(-1 + iy) = archIntegrand β (-1) y`. Direct re-export of
`F_eq_archIntegrand_at_neg_one`. -/
theorem F_at_neg_one_eq_archIntegrand (β : ℝ) (y : ℝ) :
    pairTestMellin_archKernel_product β ((-1 : ℂ) + (y : ℂ) * I)
      = archIntegrand β (-1) y :=
  F_eq_archIntegrand_at_neg_one β y

/-! ## Axiom-clean building block (2): residue limits -/

/-- Residue at `s = 0` in its `pairTestMellin β 0` form. Direct re-export
of `pairTestMellin_archKernel_residue_at_zero`. -/
theorem F_residue_at_zero_eq_neg_pairTestMellin_zero (β : ℝ) :
    Filter.Tendsto (fun s : ℂ => s * pairTestMellin_archKernel_product β s)
      (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (-pairTestMellin β 0)) :=
  pairTestMellin_archKernel_residue_at_zero β

/-- Residue at `s = 1`, identified with the explicit closed-form
value `gaussianPairDefect β`. Direct re-export of
`pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect`. -/
theorem F_residue_at_one_eq_gaussianPairDefect (β : ℝ) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * pairTestMellin_archKernel_product β s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (((gaussianPairDefect β : ℝ) : ℂ))) :=
  pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect β

/-! ## Axiom-clean building block (3): boundary integrability -/

/-- Right edge `archIntegrand β 2` is Bochner integrable on ℝ. Re-export
from `ArchOperatorBound`. -/
theorem archIntegrand_at_two_integrable (β : ℝ) :
    MeasureTheory.Integrable (archIntegrand β 2) :=
  archIntegrand_integrable_at_two β

/-- Left edge `archIntegrand β (-1)` is Bochner integrable on ℝ.
Re-export from `WeilArchAtNegOne`. -/
theorem archIntegrand_at_neg_one_integrable (β : ℝ) :
    MeasureTheory.Integrable (archIntegrand β (-1)) :=
  ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β

/-! ## Axiom-clean building block (4): regularity off poles

`F` is differentiable on the open strip `-1 < Re s < 2` away from
`{0, 1}`, and continuous at every point of the line `Re s = -1`. -/

/-- `F` is differentiable away from the two poles inside the strip.
Direct re-export of `pairTestMellin_archKernel_differentiableAt_off_poles`. -/
theorem F_differentiableAt_off_poles (β : ℝ) {s : ℂ}
    (hs_re_l : -1 < s.re) (hs_re_r : s.re < 2)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (pairTestMellin_archKernel_product β) s :=
  pairTestMellin_archKernel_differentiableAt_off_poles β hs_re_l hs_re_r hs0 hs1

/-- `F` is continuous at every point of the line `Re s = -1` (no pole
there). Direct re-export of `pairTestMellin_archKernel_continuousAt_neg_one`. -/
theorem F_continuousAt_on_neg_one_line (β : ℝ) {y : ℝ} :
    ContinuousAt (pairTestMellin_archKernel_product β) ((-1 : ℂ) + (y : ℂ) * I) :=
  pairTestMellin_archKernel_continuousAt_neg_one β


end ZD.ArchKernelRectCauchyTransport

/-! ## Axiom checks -/

#print axioms ZD.ArchKernelRectCauchyTransport.F_at_two_eq_archIntegrand
#print axioms ZD.ArchKernelRectCauchyTransport.F_at_neg_one_eq_archIntegrand
#print axioms ZD.ArchKernelRectCauchyTransport.F_residue_at_zero_eq_neg_pairTestMellin_zero
#print axioms ZD.ArchKernelRectCauchyTransport.F_residue_at_one_eq_gaussianPairDefect
#print axioms ZD.ArchKernelRectCauchyTransport.archIntegrand_at_two_integrable
#print axioms ZD.ArchKernelRectCauchyTransport.archIntegrand_at_neg_one_integrable
#print axioms ZD.ArchKernelRectCauchyTransport.F_differentiableAt_off_poles
#print axioms ZD.ArchKernelRectCauchyTransport.F_continuousAt_on_neg_one_line

end
