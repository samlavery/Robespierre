/-
# Pair-combo leading-order telescoping at `s = 0` and residue at `s = 1`.

By the cosh-expansion of the pair test Mellin transform, the five-term combo
with coefficients `[1/2, 1/2, -1, -1, 1]` of `coshGaussMellinExt` factors has
a vanishing leading-order coefficient at `s = 0`:

  `(1/2) · (-1) + (1/2) · (-1) + (-1) · (-1) + (-1) · (-1) + (1) · (-1)`
    `= -1/2 - 1/2 + 1 + 1 - 1 = 0`.

Each individual product `s² · archKernel s · coshGaussMellinExt c s` tends to
`-1` (proved in `ArchKernelCoshGaussResidue.lean`). Linearity of `Tendsto`
together with the vanishing coefficient sum gives the leading telescope.

At `s = 1`, `archKernel` has a simple pole (residue `+1`) while
`coshGaussMellinExt c` is regular, so `(s - 1) · archKernel s · cGM c s →
cGM c 1`. Linearity again gives the residue value of the pair combo.
-/

import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation
import RequestProject.ArchKernelCoshGaussResidue

open Filter Topology Complex
open ZD.WeilArchKernelResidues
open ZD.CoshGaussMellinContinuation
open ZD.ArchKernelCoshGaussResidue

namespace ZD.PairComboLeadingTelescope

/-- **Pair-combo leading-order telescope at `s = 0`.** The five-term linear
combination of `coshGaussMellinExt` factors with coefficients `[1/2, 1/2, -1,
-1, 1]` (whose sum is zero) makes the leading-order `s⁻²` singularity of the
product `archKernel · combo` vanish. Concretely, the rescaled product
`s² · archKernel s · combo` tends to `0` as `s → 0`. -/
theorem pairCombo_archKernel_coshGaussExt_leading_telescope (β : ℝ) :
    Filter.Tendsto
      (fun s : ℂ =>
        s^2 * ZD.WeilArchKernelResidues.archKernel s *
        ((1/2 : ℂ) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2*β - Real.pi/3) s
         + (1/2) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2 - Real.pi/3 - 2*β) s
         - ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (1 - Real.pi/3) s
         - ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2*β - 1) s
         + ZD.CoshGaussMellinContinuation.coshGaussMellinExt 0 s))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  -- Five individual residue limits at `s = 0`, each tending to `-1`.
  have h1 := archKernel_coshGaussExt_residue_at_zero (2*β - Real.pi/3)
  have h2 := archKernel_coshGaussExt_residue_at_zero (2 - Real.pi/3 - 2*β)
  have h3 := archKernel_coshGaussExt_residue_at_zero (1 - Real.pi/3)
  have h4 := archKernel_coshGaussExt_residue_at_zero (2*β - 1)
  have h5 := archKernel_coshGaussExt_residue_at_zero 0
  -- Scale each by its coefficient.
  have h1' := h1.const_mul ((1/2 : ℂ))
  have h2' := h2.const_mul ((1/2 : ℂ))
  -- Combine.
  have h_sum :=
    (((h1'.add h2').sub h3).sub h4).add h5
  -- Compute the limit numerical value: (1/2)·(-1)+(1/2)·(-1)-(-1)-(-1)+(-1) = 0.
  have h_lim_val :
      ((1/2 : ℂ) * (-1) + (1/2 : ℂ) * (-1) - (-1) - (-1) + (-1)) = (0 : ℂ) := by
    ring
  rw [h_lim_val] at h_sum
  -- Pointwise rearrangement: distributivity of `s² · archK` over the linear combo.
  refine h_sum.congr ?_
  intro s
  ring

#print axioms ZD.PairComboLeadingTelescope.pairCombo_archKernel_coshGaussExt_leading_telescope

/-- **Pair-combo simple-pole residue at `s = 1`.** Since `archKernel` has a
simple pole at `s = 1` (residue `+1`) and each `coshGaussMellinExt c` is
regular there, the rescaled product `(s - 1) · archKernel s · combo` tends to
the corresponding linear combination of values `coshGaussMellinExt c 1`. -/
theorem pairCombo_archKernel_coshGaussExt_residue_at_one (β : ℝ) :
    Filter.Tendsto
      (fun s : ℂ =>
        (s - 1) * ZD.WeilArchKernelResidues.archKernel s *
        ((1/2 : ℂ) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2*β - Real.pi/3) s
         + (1/2) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2 - Real.pi/3 - 2*β) s
         - ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (1 - Real.pi/3) s
         - ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2*β - 1) s
         + ZD.CoshGaussMellinContinuation.coshGaussMellinExt 0 s))
      (nhdsWithin 1 {1}ᶜ)
      (nhds (
        (1/2 : ℂ) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2*β - Real.pi/3) 1
        + (1/2) * ZD.CoshGaussMellinContinuation.coshGaussMellinExt
            (2 - Real.pi/3 - 2*β) 1
        - ZD.CoshGaussMellinContinuation.coshGaussMellinExt (1 - Real.pi/3) 1
        - ZD.CoshGaussMellinContinuation.coshGaussMellinExt (2*β - 1) 1
        + ZD.CoshGaussMellinContinuation.coshGaussMellinExt 0 1)) := by
  have h1 := archKernel_coshGaussExt_residue_at_one (2*β - Real.pi/3)
  have h2 := archKernel_coshGaussExt_residue_at_one (2 - Real.pi/3 - 2*β)
  have h3 := archKernel_coshGaussExt_residue_at_one (1 - Real.pi/3)
  have h4 := archKernel_coshGaussExt_residue_at_one (2*β - 1)
  have h5 := archKernel_coshGaussExt_residue_at_one 0
  have h1' := h1.const_mul ((1/2 : ℂ))
  have h2' := h2.const_mul ((1/2 : ℂ))
  have h_sum :=
    (((h1'.add h2').sub h3).sub h4).add h5
  refine h_sum.congr ?_
  intro s
  ring

#print axioms ZD.PairComboLeadingTelescope.pairCombo_archKernel_coshGaussExt_residue_at_one

end ZD.PairComboLeadingTelescope
