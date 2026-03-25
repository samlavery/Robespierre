import Mathlib
import RequestProject.Defs
/-!
# No Off-Axis Zeros of the Robespierre Zeta Function

This file introduces the statement that the Robespierre zeta function has no zeros
off the critical line Re(s) = arcsin(1/2) within the θ-native critical strip
0 < Re(s) < 1 + (π - 3) / 3, equivalently 0 < Re(s) < 2θ,
where θ = arcsin(1/2) = π/6.

In the θ-native coordinate system the critical strip is
(0, 1 + (π - 3) / 3) = (0, 2θ), centered at θ, rather than the classical
(0, 1). The critical line is Re(s) = θ = arcsin(1/2).
-/
open Complex CircleNative

/-- The alternative Robespierre zeta function used for the classical bridge:
    it is classical `riemannZeta` transported from the classical strip
    `(0, 1)` to the θ-native strip `(0, 2θ)` by the linear rescaling
    `σ ↦ σ / (2θ)` on real parts, keeping the height fixed. -/
noncomputable def RobespierreZetaO (s : ℂ) : ℂ :=
  riemannZeta ⟨s.re / (2 * θ), s.im⟩

noncomputable def RobespierreZeta (s : ℂ) : ℂ :=
  CircleNative.ΞInfinite s

/-- The Robespierre zeta function has no zeros in the θ-native critical strip
    off the critical line. That is, if
    `0 < Re(s) < 1 + (π - 3) / 3` (equivalently `0 < Re(s) < 2θ`)
    and `ζ(s) = 0`, then `Re(s) = arcsin(1/2)`. -/
def NoOffAxisZeros : Prop :=
  ∀ (s : ℂ), RobespierreZeta s = 0 → 0 < s.re → s.re < 2 * θ → s.re = Real.arcsin (1 / 2)

def RobespierreHypothesis : Prop :=
  ∀ (s : ℂ), RobespierreZeta s = 0 → 0 < s.re → s.re < 2 * θ → s.re = Real.arcsin (1 / 2)
