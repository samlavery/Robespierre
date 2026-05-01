/-
# Pair-combo rectangle Cauchy: edge integrability (Scope Level 3)

The rectangle Cauchy contour for the five-term pair-combo

  `f(s) = archKernel s · combo(s)`

where `combo(s)` is the linear combination of `coshGaussMellinExt c` factors
arising from `pairTestMellin_cosh_expansion`, has four edges. The two
*horizontal* edges (`Re s = 2` and `Re s = -1`) carry continuous-in-`y`
integrands, hence are interval-integrable on any compact `[-T, T]`.

This file proves exactly that — the cleanest closeable scope, since a full
residue-extraction Cauchy identity would require Laurent-series
infrastructure for `c`-dependent removable-singularity certificates that is
not currently available.

## Main results

* `pairCombo` — the five-term linear combination of `coshGaussMellinExt`
  factors with coefficients `[1/2, 1/2, -1, -1, 1]` whose `s = 0`
  leading-order pole vanishes (cf. `PairComboLeadingTelescope`).
* `archKernel_pairCombo_continuous_on_two_line` — continuity of the
  right-edge integrand `y ↦ archKernel (2 + iy) · pairCombo β (2 + iy)`.
* `archKernel_pairCombo_continuous_on_neg_one_line` — continuity of the
  left-edge integrand `y ↦ archKernel (-1 + iy) · pairCombo β (-1 + iy)`.
* `archKernel_pairCombo_intervalIntegrable_on_two_line` — interval
  integrability of the right-edge integrand on `[-T, T]`.
* `archKernel_pairCombo_intervalIntegrable_on_neg_one_line` — interval
  integrability of the left-edge integrand on `[-T, T]`.

Each result is a direct consequence of
`archKernel_coshGaussExt_continuous_on_two_line` /
`archKernel_coshGaussExt_continuous_on_neg_one_line` together with linearity
of continuity, plus `Continuous.intervalIntegrable`.

All proofs are axiom-clean.
-/

import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation
import RequestProject.ArchKernelCoshGaussRectCauchy
import RequestProject.ArchKernelCoshGaussRectCauchyNegOne

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.PairComboRectCauchy

open ZD.WeilArchKernelResidues ZD.CoshGaussMellinContinuation
  ZD.ArchKernelCoshGaussRectCauchy ZD.ArchKernelCoshGaussRectCauchyNegOne

/-- The five-term linear combination of `coshGaussMellinExt c` factors that
appears in `pairTestMellin_cosh_expansion`. The combo coefficients are
`[1/2, 1/2, -1, -1, 1]` and the `c`-values are
`[2β - π/3, 2 - π/3 - 2β, 1 - π/3, 2β - 1, 0]`.

This is the *Mellin-side* analogue of the pair test integrand whose `s = 0`
leading-order pole vanishes (`pairCombo_archKernel_coshGaussExt_leading_telescope`)
and whose `s = 1` simple-pole residue is the gaussian pair defect
(`pairCombo_archKernel_coshGaussExt_residue_at_one`). -/
def pairCombo (β : ℝ) (s : ℂ) : ℂ :=
  (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s
    + (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s
    - coshGaussMellinExt (1 - Real.pi/3) s
    - coshGaussMellinExt (2*β - 1) s
    + coshGaussMellinExt 0 s

/-! ### Right edge `Re s = 2`: continuity and integrability -/

/-- The right-edge integrand `y ↦ archKernel (2 + iy) · pairCombo β (2 + iy)`
is continuous on all of `ℝ`. This follows by linearity from the five
single-`c` continuity statements
`archKernel_coshGaussExt_continuous_on_two_line`. -/
theorem archKernel_pairCombo_continuous_on_two_line (β : ℝ) :
    Continuous (fun y : ℝ =>
      archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        pairCombo β ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
  -- The combo is `Σᵢ αᵢ · coshGaussMellinExt cᵢ` so
  -- `archKernel · combo = Σᵢ αᵢ · (archKernel · coshGaussMellinExt cᵢ)`.
  have h1 := archKernel_coshGaussExt_continuous_on_two_line (2*β - Real.pi/3)
  have h2 := archKernel_coshGaussExt_continuous_on_two_line (2 - Real.pi/3 - 2*β)
  have h3 := archKernel_coshGaussExt_continuous_on_two_line (1 - Real.pi/3)
  have h4 := archKernel_coshGaussExt_continuous_on_two_line (2*β - 1)
  have h5 := archKernel_coshGaussExt_continuous_on_two_line 0
  -- Combine via linearity of `Continuous`.
  have h12 : Continuous (fun y : ℝ =>
      (1/2 : ℂ) * (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt (2*β - Real.pi/3) ((2 : ℂ) + (y : ℂ) * Complex.I)) +
      (1/2 : ℂ) * (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt (2 - Real.pi/3 - 2*β) ((2 : ℂ) + (y : ℂ) * Complex.I))) :=
    (continuous_const.mul h1).add (continuous_const.mul h2)
  have h_sum : Continuous (fun y : ℝ =>
      ((1/2 : ℂ) * (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2*β - Real.pi/3) ((2 : ℂ) + (y : ℂ) * Complex.I)) +
        (1/2 : ℂ) * (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2 - Real.pi/3 - 2*β) ((2 : ℂ) + (y : ℂ) * Complex.I))) -
        (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (1 - Real.pi/3) ((2 : ℂ) + (y : ℂ) * Complex.I)) -
        (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2*β - 1) ((2 : ℂ) + (y : ℂ) * Complex.I)) +
        (archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt 0 ((2 : ℂ) + (y : ℂ) * Complex.I))) :=
    (((h12.sub h3).sub h4).add h5)
  -- Match the shape with `archKernel · pairCombo`.
  refine h_sum.congr (fun y => ?_)
  unfold pairCombo
  ring

/-- Interval-integrability of the right-edge integrand on `[-T, T]`. -/
theorem archKernel_pairCombo_intervalIntegrable_on_two_line
    (β : ℝ) (T : ℝ) :
    IntervalIntegrable
      (fun y : ℝ =>
        archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
          pairCombo β ((2 : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (-T) T :=
  (archKernel_pairCombo_continuous_on_two_line β).intervalIntegrable (-T) T

/-! ### Left edge `Re s = -1`: continuity and integrability -/

/-- The left-edge integrand `y ↦ archKernel (-1 + iy) · pairCombo β (-1 + iy)`
is continuous on all of `ℝ`. -/
theorem archKernel_pairCombo_continuous_on_neg_one_line (β : ℝ) :
    Continuous (fun y : ℝ =>
      archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
        pairCombo β ((-1 : ℂ) + (y : ℂ) * Complex.I)) := by
  have h1 := archKernel_coshGaussExt_continuous_on_neg_one_line (2*β - Real.pi/3)
  have h2 := archKernel_coshGaussExt_continuous_on_neg_one_line (2 - Real.pi/3 - 2*β)
  have h3 := archKernel_coshGaussExt_continuous_on_neg_one_line (1 - Real.pi/3)
  have h4 := archKernel_coshGaussExt_continuous_on_neg_one_line (2*β - 1)
  have h5 := archKernel_coshGaussExt_continuous_on_neg_one_line 0
  have h12 : Continuous (fun y : ℝ =>
      (1/2 : ℂ) * (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt (2*β - Real.pi/3) ((-1 : ℂ) + (y : ℂ) * Complex.I)) +
      (1/2 : ℂ) * (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt (2 - Real.pi/3 - 2*β) ((-1 : ℂ) + (y : ℂ) * Complex.I))) :=
    (continuous_const.mul h1).add (continuous_const.mul h2)
  have h_sum : Continuous (fun y : ℝ =>
      ((1/2 : ℂ) * (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2*β - Real.pi/3) ((-1 : ℂ) + (y : ℂ) * Complex.I)) +
        (1/2 : ℂ) * (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2 - Real.pi/3 - 2*β) ((-1 : ℂ) + (y : ℂ) * Complex.I))) -
        (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (1 - Real.pi/3) ((-1 : ℂ) + (y : ℂ) * Complex.I)) -
        (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt (2*β - 1) ((-1 : ℂ) + (y : ℂ) * Complex.I)) +
        (archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          coshGaussMellinExt 0 ((-1 : ℂ) + (y : ℂ) * Complex.I))) :=
    (((h12.sub h3).sub h4).add h5)
  refine h_sum.congr (fun y => ?_)
  unfold pairCombo
  ring

/-- Interval-integrability of the left-edge integrand on `[-T, T]`. -/
theorem archKernel_pairCombo_intervalIntegrable_on_neg_one_line
    (β : ℝ) (T : ℝ) :
    IntervalIntegrable
      (fun y : ℝ =>
        archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
          pairCombo β ((-1 : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (-T) T :=
  (archKernel_pairCombo_continuous_on_neg_one_line β).intervalIntegrable (-T) T

/-! ### Axiom check -/

#print axioms archKernel_pairCombo_continuous_on_two_line
#print axioms archKernel_pairCombo_intervalIntegrable_on_two_line
#print axioms archKernel_pairCombo_continuous_on_neg_one_line
#print axioms archKernel_pairCombo_intervalIntegrable_on_neg_one_line

end ZD.PairComboRectCauchy

end
