import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.MellinPathToXi
import RequestProject.CoshZetaSymmetry
import RequestProject.ExplicitFormulaBridgeOfRH

/-!
# ⚠️ LEGACY — superseded by `WeilCoshPairPositivity.lean` + `WeilZeroOrthogonality.lean`.

Kept only for backward import compatibility. The theorem
`zero_forces_critical_re` here takes `RiemannHypothesis` as a hypothesis
to derive `ρ.re = 1/2` — it is **circular** as a route to RH. The
current architecture proves the conditional cosh-side closure
`WeilVanishesOnZeros → RiemannHypothesis` directly in
`WeilCoshPairPositivity.lean` without taking RH as input.

Do NOT extend this file. New cosh-side wrappers belong in
`WeilCoshPairPositivity.lean`.

## (Legacy) Detector difference identity.

With `a := 1/2 − π/6`, `u := ρ.re − 1/2`, and `t := log p`:

  coshDetectorLeft  ρ.re t = cosh((u + a)·t)
  coshDetectorRight ρ.re t = cosh((u − a)·t)

Their difference equals `2·sinh(a·t)·sinh(u·t)`, which vanishes iff
`sinh(u·t) = 0` (since `a ≠ 0` and `t = log p ≠ 0` for prime `p ≥ 2`),
iff `u = 0`, iff `ρ.re = 1/2`. This is `coshDetectors_agree_iff`.
-/

open Real Complex ZetaDefs

noncomputable section

namespace ZD

-- This is false as stated and needs to go
theorem averageEnergyDefect_gaussian_zero_forces_half
    (β : ℝ) (h : averageEnergyDefect gaussianKernel β = 0) :
    β = 1 / 2 := by
  by_contra hne
  have hP : 0 < averageEnergyDefect gaussianKernel β :=
    gaussianKernel_averageEnergyDefect_pos_offline β hne
  linarith





end ZD

end
