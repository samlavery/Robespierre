/-
# Leading-coefficient residue for the product `archKernel · coshGaussMellinExt c`
at the double pole `s = 0`.

Both factors have a simple pole at `s = 0` with known residues:

* `archKernel s` : residue `-1`  (i.e. `s · archKernel s → -1` along `nhdsWithin 0 {0}ᶜ`)
* `coshGaussMellinExt c s` : residue `+1`  (i.e. `s · coshGaussMellinExt c s → 1`)

Their product therefore has a double pole at `s = 0` with leading coefficient
(coefficient of `s⁻²`) equal to `(-1) · 1 = -1`. Equivalently:

  `s² · (archKernel s · coshGaussMellinExt c s) → -1`  along `nhdsWithin 0 {0}ᶜ`.

This is the cleanest analog of the simple-pole "residue exists" statement; the
true Laurent residue (coefficient of `s⁻¹`) would require constant-term data of
both factors.

The proof simply factors `s² = s · s` and applies `Filter.Tendsto.mul` to the
two simple-pole residue statements that already live in the project.
-/

import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation

open Filter Topology Complex
open ZD.WeilArchKernelResidues
open ZD.CoshGaussMellinContinuation

namespace ZD.ArchKernelCoshGaussResidue

/-- **Leading-coefficient residue at the double pole `s = 0`.** Multiplying the
product `archKernel s · coshGaussMellinExt c s` by `s²` cancels the double
pole and produces the limit `(-1) · 1 = -1`. -/
theorem archKernel_coshGaussExt_residue_at_zero (c : ℝ) :
    Filter.Tendsto
      (fun s : ℂ => s^2 * (ZD.WeilArchKernelResidues.archKernel s *
                            ZD.CoshGaussMellinContinuation.coshGaussMellinExt c s))
      (nhdsWithin 0 {0}ᶜ) (nhds (-1 : ℂ)) := by
  -- Two known simple-pole residues.
  have h1 :
      Filter.Tendsto (fun s : ℂ => s * ZD.WeilArchKernelResidues.archKernel s)
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (-1 : ℂ)) :=
    ZD.WeilArchKernelResidues.archKernel_residue_at_zero
  have h2 :
      Filter.Tendsto
        (fun s : ℂ => s * ZD.CoshGaussMellinContinuation.coshGaussMellinExt c s)
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (1 : ℂ)) :=
    ZD.CoshGaussMellinContinuation.coshGaussMellinExt_residue_at_zero c
  -- Their product tends to `(-1) · 1 = -1`.
  have h_prod := h1.mul h2
  -- Numerical normalization of the limit value.
  have h_eq_lim : (-1 : ℂ) * (1 : ℂ) = (-1 : ℂ) := by ring
  rw [h_eq_lim] at h_prod
  -- Pointwise rearrangement: `(s · K) · (s · F) = s² · (K · F)`.
  refine h_prod.congr ?_
  intro s
  ring

#print axioms ZD.ArchKernelCoshGaussResidue.archKernel_coshGaussExt_residue_at_zero

/-! ## Bonus: simple-pole residue at `s = 1`

`coshGaussMellinExt c` is regular at `s = 1` (its only poles in the strip
`Re s > -2` are at `s = 0`; in fact across `ℂ` they sit at `s = 0, -2, -4, …`).
Meanwhile `archKernel s` has a simple pole at `s = 1` with residue `+1`. Hence
the product has a simple pole at `s = 1` with residue `coshGaussMellinExt c 1`.
-/

/-- `gaussMellinClosed` is differentiable at `s = 1`. The factor `Γ(s/2)`
evaluates to `Γ(1/2)`, which is regular since `1/2 ≠ -m` for every `m : ℕ`. -/
private lemma gaussMellinClosed_differentiableAt_one :
    DifferentiableAt ℂ ZD.CoshGaussMellinContinuation.gaussMellinClosed 1 := by
  unfold ZD.CoshGaussMellinContinuation.gaussMellinClosed
  have h_id : DifferentiableAt ℂ (fun s : ℂ => s) (1 : ℂ) := differentiableAt_id
  have h_div : DifferentiableAt ℂ (fun s : ℂ => s / 2) (1 : ℂ) := h_id.div_const _
  have h_neg : DifferentiableAt ℂ (fun s : ℂ => -(s / 2)) (1 : ℂ) := h_div.neg
  have h_cpow : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (-(s / 2))) (1 : ℂ) :=
    h_neg.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have h_const : DifferentiableAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) (1 : ℂ) :=
    differentiableAt_const _
  have h_mul1 : DifferentiableAt ℂ
      (fun s : ℂ => (1 / 2 : ℂ) * (2 : ℂ) ^ (-(s / 2))) (1 : ℂ) := h_const.mul h_cpow
  have h_gamma_at_half : DifferentiableAt ℂ Complex.Gamma ((1 : ℂ) / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hcontra
    -- 1/2 = -m as complex; take real parts and force m = 0, then derive contradiction.
    have hre : ((1 : ℂ) / 2).re = (-(m : ℂ)).re := by rw [hcontra]
    simp at hre
    have h_nonneg : (0 : ℝ) ≤ -(m : ℝ) := by rw [← hre]; norm_num
    have hm_le0 : (m : ℝ) ≤ 0 := by linarith
    have hm_eq0 : (m : ℝ) = 0 :=
      le_antisymm hm_le0 (by exact_mod_cast Nat.zero_le m)
    rw [hm_eq0] at hre
    norm_num at hre
  have h_gamma_comp :
      DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) (1 : ℂ) :=
    h_gamma_at_half.comp 1 h_div
  exact h_mul1.mul h_gamma_comp

/-- `coshGaussMellinExt c` is continuous at `s = 1` (it is, in fact, analytic
there: `s = 1` is not among the poles `0, -2, -4, …`). -/
private lemma coshGaussMellinExt_continuousAt_one (c : ℝ) :
    ContinuousAt (ZD.CoshGaussMellinContinuation.coshGaussMellinExt c) 1 := by
  have h_g : DifferentiableAt ℂ ZD.CoshGaussMellinContinuation.gaussMellinClosed 1 :=
    gaussMellinClosed_differentiableAt_one
  have h_d :
      AnalyticAt ℂ (mellin (ZD.CoshGaussMellinContinuation.coshDiff c)) 1 := by
    apply ZD.CoshGaussMellinContinuation.coshDiffMellin_analyticAt
    show (-2 : ℝ) < (1 : ℂ).re
    simp; norm_num
  have h_d' :
      DifferentiableAt ℂ (mellin (ZD.CoshGaussMellinContinuation.coshDiff c)) 1 :=
    h_d.differentiableAt
  have h_sum : DifferentiableAt ℂ
      (fun s : ℂ => ZD.CoshGaussMellinContinuation.gaussMellinClosed s +
        mellin (ZD.CoshGaussMellinContinuation.coshDiff c) s) (1 : ℂ) :=
    h_g.add h_d'
  have h_eq : ZD.CoshGaussMellinContinuation.coshGaussMellinExt c =
      (fun s : ℂ => ZD.CoshGaussMellinContinuation.gaussMellinClosed s +
        mellin (ZD.CoshGaussMellinContinuation.coshDiff c) s) := by
    funext s; rfl
  rw [h_eq]
  exact h_sum.continuousAt

/-- **Simple-pole residue at `s = 1`.** Since `archKernel` has a simple pole
at `s = 1` with residue `+1` and `coshGaussMellinExt c` is regular there,
the product has a simple pole at `s = 1` with residue `coshGaussMellinExt c 1`.
-/
theorem archKernel_coshGaussExt_residue_at_one (c : ℝ) :
    Filter.Tendsto
      (fun s : ℂ => (s - 1) *
        (ZD.WeilArchKernelResidues.archKernel s *
         ZD.CoshGaussMellinContinuation.coshGaussMellinExt c s))
      (nhdsWithin 1 {1}ᶜ)
      (nhds (ZD.CoshGaussMellinContinuation.coshGaussMellinExt c 1)) := by
  have h_arch :
      Filter.Tendsto (fun s : ℂ => (s - 1) * ZD.WeilArchKernelResidues.archKernel s)
        (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (1 : ℂ)) :=
    ZD.WeilArchKernelResidues.archKernel_residue_at_one
  have h_cont : ContinuousAt (ZD.CoshGaussMellinContinuation.coshGaussMellinExt c) 1 :=
    coshGaussMellinExt_continuousAt_one c
  have h_cgm_tend :
      Filter.Tendsto (fun s : ℂ => ZD.CoshGaussMellinContinuation.coshGaussMellinExt c s)
        (nhdsWithin (1 : ℂ) {1}ᶜ)
        (nhds (ZD.CoshGaussMellinContinuation.coshGaussMellinExt c 1)) := by
    have hh := h_cont
    rw [ContinuousAt] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have h_prod := h_arch.mul h_cgm_tend
  have h_lim : (1 : ℂ) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt c 1 =
      ZD.CoshGaussMellinContinuation.coshGaussMellinExt c 1 := by ring
  rw [h_lim] at h_prod
  refine h_prod.congr ?_
  intro s
  ring

#print axioms ZD.ArchKernelCoshGaussResidue.archKernel_coshGaussExt_residue_at_one

end ZD.ArchKernelCoshGaussResidue
