import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.MellinPathToXi
import RequestProject.CoshZetaSymmetry
import RequestProject.RiemannHypothesisBridge
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


-- this needs to go
theorem zero_forces_critical_re (hRH : RiemannHypothesis) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2 := by
  intro ρ hρ
  -- Single-call wrapper in place of the removed axiom.
  have hB : BalancedChannel gaussianKernel ρ :=
    balanced_channel_of_RiemannHypothesis hRH ρ hρ
  have hE : averageEnergyDefect gaussianKernel ρ.re = 0 :=
    averageEnergyDefect_of_BalancedChannel gaussianKernel ρ hB
  exact averageEnergyDefect_gaussian_zero_forces_half ρ.re hE

/-- **Target theorem.** Cosh-pair balance at every nontrivial zero at
every prime, given `hRH : RiemannHypothesis`. Proof reduces by the
cosh-pair-difference identity to `ρ.re = 1/2`. -/
theorem H_zero_forces_detector_balance
    (hRH : RiemannHypothesis)
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros)
    (p : ℕ) (hp : Nat.Prime p) :
    coshDetectorLeft ρ.re (Real.log p) =
      coshDetectorRight ρ.re (Real.log p) := by
  have hre : ρ.re = 1 / 2 := zero_forces_critical_re hRH ρ hρ
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne_one
  exact (coshDetectors_agree_iff hlog).mpr hre


/-! ### Axiom hygiene -/

#print axioms H_zero_forces_detector_balance
#print axioms zero_forces_critical_re

end ZD

end
