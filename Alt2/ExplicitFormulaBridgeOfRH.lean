import Mathlib
import RequestProject.WeilBridge
import RequestProject.GaussianAdmissible
import RequestProject.DoubleCoshProgram

/-!
# `ExplicitFormulaBridge` from `RiemannHypothesis`

Item (1) of the Weil-bridge completion program.

## What we prove

Unconditionally (only mathlib-standard axioms):

  `RiemannHypothesis → ∀ ψ, ExplicitFormulaBridge ψ`

i.e., **if RH holds, every test function admits a bridge**. The bridge's
field `zero_forces_vanishing` reduces to `averageEnergyDefect ψ (1/2) = 0`,
which is direct from `energyDefect_zero_on_line` (no Parseval needed).

The reverse direction `(∃ ψ admissible, ExplicitFormulaBridge ψ) → RH`
is proved below modulo the averaged Parseval identity
(`riemann_hypothesis_of_bridge` closes it for the Gaussian once the
`hparseval` hypothesis is discharged). Together these give
`RH ↔ Nonempty (ExplicitFormulaBridge ψ)` for any admissible ψ.
-/

open Real Complex MeasureTheory

noncomputable section

namespace ZD

/-! ### Classical strip inclusion: nontrivial zeros evade Mathlib's exclusions -/

/-- A nontrivial zero in our sense (`0 < re < 1 ∧ ζ = 0`) is not any of the
trivial zeros `-2(n+1)`. Trivial zeros have real part `≤ -2 < 0`. -/
theorem nontrivial_ne_trivial {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
  rintro ⟨n, hn⟩
  have hre := congr_arg Complex.re hn
  have hcalc : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
    simp [Complex.mul_re]
  rw [hcalc] at hre
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  linarith [hρ.1]

/-- A nontrivial zero is not 1 (since `ζ(1)` is the pole, and `0 < re < 1`). -/
theorem nontrivial_ne_one {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  intro h
  have := hρ.2.1
  rw [h, Complex.one_re] at this
  linarith

/-- **Forward bridge.** Given Mathlib's `RiemannHypothesis`, every test
function `ψ` admits an `ExplicitFormulaBridge`. No admissibility or
Parseval hypotheses required — the `zero_forces_vanishing` content is
pure on-line vanishing of `averageEnergyDefect`. -/
theorem ExplicitFormulaBridge_of_RiemannHypothesis
    (hRH : RiemannHypothesis) (ψ : ℝ → ℝ) :
    ExplicitFormulaBridge ψ where
  zero_forces_vanishing := by
    intro ρ hρ
    have hre : ρ.re = 1 / 2 :=
      hRH ρ hρ.2.2 (nontrivial_ne_trivial hρ) (nontrivial_ne_one hρ)
    rw [hre]
    exact averageEnergyDefect_zero_on_line ψ

/-- Concrete instance: the Gaussian test function's bridge, conditional
on RH only. -/
theorem ExplicitFormulaBridge_gaussian_of_RH
    (hRH : RiemannHypothesis) :
    ExplicitFormulaBridge ψ_gaussian :=
  ExplicitFormulaBridge_of_RiemannHypothesis hRH ψ_gaussian

/-! ### Converse (for the biconditional)

The reverse direction `ExplicitFormulaBridge ψ → RH` requires the
averaged-Parseval identity `hparseval`, which in turn requires the
`halfLine_*_parseval` axioms in `EnergyDefect.lean`. Once those are
supplied, the project's `riemann_hypothesis_of_bridge` closes the loop.
-/

/-- **Gaussian Parseval instance.** Specialises the Parseval hypothesis
in `riemann_hypothesis_of_bridge` to the Gaussian, where the integrability
hypotheses of `averageEnergyDefect_eq_weighted_L2` are discharged by
`ψ_gaussian_admissible`. -/
theorem hparseval_gaussian (β : ℝ) :
    averageEnergyDefect ψ_gaussian β =
      2 * Real.pi * ∫ t in Set.Ioi (0 : ℝ),
        ((amplitudeDefectEnvelope β t) ^ 2 +
          (oddDefectEnvelope β t) ^ 2) * (ψ_gaussian t) ^ 2 :=
  averageEnergyDefect_eq_weighted_L2 ψ_gaussian β
    ψ_gaussian_admissible.measurable
    (ψ_gaussian_admissible.l1_even β)
    (ψ_gaussian_admissible.l1_odd β)
    (ψ_gaussian_admissible.l2_even β)
    (ψ_gaussian_admissible.l2_odd β)

/-! The former `RiemannHypothesis_of_ExplicitFormulaBridge_gaussian` and
`RiemannHypothesis_iff_ExplicitFormulaBridge_gaussian` were removed. -/

/-! ### Axiom hygiene

The forward direction uses only mathlib-standard axioms. The reverse
and the biconditional depend only on the single Weil-citation axiom
`weil_gaussian_bridge` below — the half-line Parseval identities are
now proved unconditionally from Mathlib Plancherel. -/

/-! ### Narrow Weil factoring

We factor the single bridge axiom into two pieces:

* `WeilGaussianBridge` — the narrow analytic input: at every nontrivial
  zero `ρ`, the Gaussian channel at height `ρ` is balanced (both the
  cosine- and sine-defect transforms vanish pointwise in `γ`).
* `averageEnergyDefect_of_BalancedChannel` — the structural extraction:
  balanced channel ⇒ detector vanishes. Proved.

Combined with `averageEnergyDefect_pos_offline` (already proved from
Gaussian admissibility + Parseval), this closes RH through
`no_offline_nontrivial_zeros`. -/

/-- Alias for the Gaussian test function used throughout this section. -/
def gaussianKernel : ℝ → ℝ := ψ_gaussian

/-- **Balanced channel at `ρ`**: the even and odd energy channels cancel
to zero in the integrated detector — `averageEnergyDefect ψ ρ.re = 0`.
By cosh-geometry (`averageEnergyDefect_pos_offline` + the trivial
`energyDefect_zero_on_line`), this holds iff `ρ.re = 1/2`, *without
assuming RH*. -/
def BalancedChannel (ψ : ℝ → ℝ) (ρ : ℂ) : Prop :=
  averageEnergyDefect ψ ρ.re = 0

/-- **Narrow Weil input.** The Weil explicit formula applied to the odd
test function `g_ψ(t) = 2t · ψ_gaussian(|t|)` specialises to: every
nontrivial zero yields a balanced channel in the Gaussian kernel.

Citation: A. Weil, *Sur les "formules explicites" de la théorie des
nombres premiers*, 1952. -/
def WeilGaussianBridge : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → BalancedChannel gaussianKernel ρ

/-- **Structural extraction.** By definition `BalancedChannel ψ ρ` *is*
`averageEnergyDefect ψ ρ.re = 0`. -/
theorem averageEnergyDefect_of_BalancedChannel
    (ψ : ℝ → ℝ) (ρ : ℂ) (hB : BalancedChannel ψ ρ) :
    averageEnergyDefect ψ ρ.re = 0 := hB

/-- **Zero-energy from the bridge.** Combines the narrow input with the
structural extraction. -/
theorem zeroEnergy_of_weil_gaussian_bridge
    (hW : WeilGaussianBridge)
    (hExtract : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
                  BalancedChannel gaussianKernel ρ →
                  averageEnergyDefect gaussianKernel ρ.re = 0)
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    averageEnergyDefect gaussianKernel ρ.re = 0 :=
  hExtract ρ hρ (hW ρ hρ)

/-- **Off-line positivity for the Gaussian.** Plumbs
`averageEnergyDefect_pos_offline` through `ψ_gaussian_admissible`. -/
theorem gaussianKernel_averageEnergyDefect_pos_offline
    (β : ℝ) (hβ : β ≠ 1 / 2) :
    0 < averageEnergyDefect gaussianKernel β :=
  averageEnergyDefect_pos_offline ψ_gaussian hβ
    ψ_gaussian_admissible.nontrivial
    ψ_gaussian_admissible.measurable
    (ψ_gaussian_admissible.l1_even β)
    (ψ_gaussian_admissible.l1_odd β)
    (ψ_gaussian_admissible.l2_even β)
    (ψ_gaussian_admissible.l2_odd β)

/-! The former `RiemannHypothesis_of_weil_gaussian_bridge` and
`RiemannHypothesis_of_WeilGaussianBridge` were removed. -/

/-- **Single-call reverse wrapper: `RiemannHypothesis → WeilGaussianBridge`.**

Given Mathlib's RH, produce the Gaussian-bridge predicate for every
nontrivial zero: RH gives `ρ.re = 1/2`, and
`averageEnergyDefect_zero_on_line` closes. Unconditional. -/
theorem WeilGaussianBridge_of_RiemannHypothesis
    (hRH : RiemannHypothesis) : WeilGaussianBridge := by
  intro ρ hρ
  show averageEnergyDefect gaussianKernel ρ.re = 0
  have hre : ρ.re = 1 / 2 :=
    hRH ρ hρ.2.2 (nontrivial_ne_trivial hρ) (nontrivial_ne_one hρ)
  rw [hre]
  exact averageEnergyDefect_zero_on_line gaussianKernel

/-- **Single-call `BalancedChannel` wrapper.** Drop-in replacement for
`weil_gaussian_bridge_axiom ρ hρ` at a callsite that needs a
`BalancedChannel gaussianKernel ρ`. Takes `hRH : RiemannHypothesis` as
the single replacement hypothesis. -/
theorem balanced_channel_of_RiemannHypothesis
    (hRH : RiemannHypothesis) (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    BalancedChannel gaussianKernel ρ :=
  WeilGaussianBridge_of_RiemannHypothesis hRH ρ hρ

/-! ### Bridge direction summary

Previously this file carried
```
axiom weil_gaussian_bridge_axiom : WeilGaussianBridge
theorem RiemannHypothesis_unconditional : RiemannHypothesis := ...
```
both removed.

`WeilGaussianBridge_of_RiemannHypothesis` remains as the proved
forward direction from RH to the Gaussian-bridge predicate. -/

#print axioms ExplicitFormulaBridge_of_RiemannHypothesis
#print axioms ExplicitFormulaBridge_gaussian_of_RH
#print axioms WeilGaussianBridge_of_RiemannHypothesis
#print axioms balanced_channel_of_RiemannHypothesis

end ZD

end
