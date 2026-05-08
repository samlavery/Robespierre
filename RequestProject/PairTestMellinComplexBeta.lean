import Mathlib
import RequestProject.PairTestMellinAnalytic
import RequestProject.CoshGaussIBPComplexC
import RequestProject.PairTestMellinUniformBound

/-!
# Complex-`β` extension of `pairTestMellin`

The project's existing `pairTestMellin (β : ℝ) (s : ℂ) : ℂ` is the
Mellin transform of the **pair-cosh-Gauss test** at real β.  This file
introduces the natural extension to **complex** β,

```
pairTestMellinC (β : ℂ) (ρ : ℂ) : ℂ
  := (1/2)·coshGaussMellinC(2β−π/3) ρ + (1/2)·coshGaussMellinC(2−π/3−2β) ρ
     − coshGaussMellinC(1−π/3) ρ − coshGaussMellinC(2β−1) ρ + gaussMellin ρ
```

via the cosh-expansion of `pair_cosh_gauss_test`.  The new function is

* **entire in β** for each `ρ` with `0 < ρ.re` (each `coshGaussMellinC`
  is entire in its `c`-argument by `coshGaussMellinC_differentiable_in_c`,
  composed with affine maps `β ↦ aβ+b` which are entire).
* **agreeing with the original** `pairTestMellin β ρ` for real β,
  via `coshGaussMellinC_ofReal` + `pairTestMellin_cosh_expansion`.

This is the **β-side** companion to the existing `coshGaussMellinC`
(complex-`c` extension) and is the key bridge to the Field-3
Weierstrass step in the K-route admissibility chain.

Axiom footprint of all proved theorems: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Real Set MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Complex-β pair-cosh-Gauss Mellin.**  The cosh-expansion of
`pair_cosh_gauss_test` lifted to complex β, with each `coshGaussMellin`
replaced by its complex-`c` counterpart `coshGaussMellinC`. -/
noncomputable def pairTestMellinC (β : ℂ) (ρ : ℂ) : ℂ :=
  (1/2 : ℂ) * coshGaussMellinC (2*β - (Real.pi/3 : ℂ)) ρ +
  (1/2 : ℂ) * coshGaussMellinC ((2 : ℂ) - (Real.pi/3 : ℂ) - 2*β) ρ -
  coshGaussMellinC ((1 : ℂ) - (Real.pi/3 : ℂ)) ρ -
  coshGaussMellinC (2*β - 1) ρ +
  gaussMellin ρ

/-- **Agreement with the real-β version** for `0 < ρ.re`.

Both sides equal the cosh expansion: the real-side via
`pairTestMellin_cosh_expansion`; the complex-side via
`coshGaussMellinC_ofReal` (matching at every `c`-coordinate, since the
β-affine maps are real for real β). -/
theorem pairTestMellinC_ofReal_eq (β : ℝ) (ρ : ℂ) (hρ : 0 < ρ.re) :
    pairTestMellinC ((β : ℂ)) ρ = pairTestMellin β ρ := by
  -- Real-β cosh expansion.
  have h_pt :
      pairTestMellin β ρ =
        (1/2 : ℂ) * coshGaussMellin (2*β - Real.pi/3) ρ +
        (1/2 : ℂ) * coshGaussMellin (2 - Real.pi/3 - 2*β) ρ -
        coshGaussMellin (1 - Real.pi/3) ρ -
        coshGaussMellin (2*β - 1) ρ +
        gaussMellin ρ := by
    refine pairTestMellin_cosh_expansion β ρ
      (mellinConvergent_coshGauss _ hρ)
      (mellinConvergent_coshGauss _ hρ)
      (mellinConvergent_coshGauss _ hρ)
      (mellinConvergent_coshGauss _ hρ) ?_
    have := mellinConvergent_coshGauss 0 hρ
    have h_eq : (fun t : ℝ =>
        ((Real.cosh (0 * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =
        (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
      funext t; simp [Real.cosh_zero]
    rw [h_eq] at this
    exact this
  -- Match coshGaussMellinC at the four c-points to coshGaussMellin.
  unfold pairTestMellinC
  have hc1 : coshGaussMellinC (2*((β : ℂ)) - (Real.pi/3 : ℂ)) ρ =
      coshGaussMellin (2*β - Real.pi/3) ρ := by
    rw [show (2*((β : ℂ)) - (Real.pi/3 : ℂ)) = (((2*β - Real.pi/3 : ℝ)) : ℂ) by push_cast; ring]
    exact coshGaussMellinC_ofReal _ ρ
  have hc2 : coshGaussMellinC ((2 : ℂ) - (Real.pi/3 : ℂ) - 2*((β : ℂ))) ρ =
      coshGaussMellin (2 - Real.pi/3 - 2*β) ρ := by
    rw [show ((2 : ℂ) - (Real.pi/3 : ℂ) - 2*((β : ℂ))) =
            (((2 - Real.pi/3 - 2*β : ℝ)) : ℂ) by push_cast; ring]
    exact coshGaussMellinC_ofReal _ ρ
  have hc3 : coshGaussMellinC ((1 : ℂ) - (Real.pi/3 : ℂ)) ρ =
      coshGaussMellin (1 - Real.pi/3) ρ := by
    rw [show ((1 : ℂ) - (Real.pi/3 : ℂ)) = (((1 - Real.pi/3 : ℝ)) : ℂ) by push_cast; ring]
    exact coshGaussMellinC_ofReal _ ρ
  have hc4 : coshGaussMellinC (2*((β : ℂ)) - 1) ρ = coshGaussMellin (2*β - 1) ρ := by
    rw [show (2*((β : ℂ)) - 1) = (((2*β - 1 : ℝ)) : ℂ) by push_cast; ring]
    exact coshGaussMellinC_ofReal _ ρ
  rw [hc1, hc2, hc3, hc4]
  exact h_pt.symm

/-- **Affine-in-β maps are entire.** -/
private lemma differentiable_2β_sub_pi3 :
    Differentiable ℂ (fun β : ℂ => 2*β - (Real.pi/3 : ℂ)) :=
  (differentiable_const _).mul differentiable_id |>.sub (differentiable_const _)

private lemma differentiable_2_sub_pi3_sub_2β :
    Differentiable ℂ (fun β : ℂ => (2 : ℂ) - (Real.pi/3 : ℂ) - 2*β) := by
  exact (differentiable_const _).sub
    ((differentiable_const _).mul differentiable_id)

private lemma differentiable_2β_sub_one :
    Differentiable ℂ (fun β : ℂ => 2*β - 1) :=
  (differentiable_const _).mul differentiable_id |>.sub (differentiable_const _)

/-- **`pairTestMellinC` is entire in β** for `0 < ρ.re`.  Each
`coshGaussMellinC` is entire in `c` and the c-arguments are affine in
β, so the composition is entire. -/
theorem pairTestMellinC_differentiable_in_β (ρ : ℂ) (hρ : 0 < ρ.re) :
    Differentiable ℂ (fun β : ℂ => pairTestMellinC β ρ) := by
  unfold pairTestMellinC
  have h_M : Differentiable ℂ (fun c : ℂ => coshGaussMellinC c ρ) :=
    coshGaussMellinC_differentiable_in_c ρ hρ
  -- Compose each summand with affine-in-β c-argument.
  have hM1 : Differentiable ℂ (fun β : ℂ => coshGaussMellinC (2*β - (Real.pi/3 : ℂ)) ρ) :=
    h_M.comp differentiable_2β_sub_pi3
  have hM2 : Differentiable ℂ
      (fun β : ℂ => coshGaussMellinC ((2 : ℂ) - (Real.pi/3 : ℂ) - 2*β) ρ) :=
    h_M.comp differentiable_2_sub_pi3_sub_2β
  have hM3 : Differentiable ℂ
      (fun _ : ℂ => coshGaussMellinC ((1 : ℂ) - (Real.pi/3 : ℂ)) ρ) :=
    differentiable_const _
  have hM4 : Differentiable ℂ (fun β : ℂ => coshGaussMellinC (2*β - 1) ρ) :=
    h_M.comp differentiable_2β_sub_one
  have hG : Differentiable ℂ (fun _ : ℂ => gaussMellin ρ) := differentiable_const _
  exact (((((differentiable_const _).mul hM1).add ((differentiable_const _).mul hM2)).sub
    hM3).sub hM4).add hG

/-- **`pairTestMellinC` is `AnalyticOnNhd ℂ` on `Set.univ` in β** for
`0 < ρ.re`. -/
theorem pairTestMellinC_analyticOnNhd_in_β (ρ : ℂ) (hρ : 0 < ρ.re) :
    AnalyticOnNhd ℂ (fun β : ℂ => pairTestMellinC β ρ) Set.univ :=
  (pairTestMellinC_differentiable_in_β ρ hρ).differentiableOn.analyticOnNhd isOpen_univ

#print axioms pairTestMellinC_ofReal_eq
#print axioms pairTestMellinC_differentiable_in_β
#print axioms pairTestMellinC_analyticOnNhd_in_β

end Contour
end WeilPositivity
end ZD

end
