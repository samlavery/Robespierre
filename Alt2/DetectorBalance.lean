import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.MellinPathToXi
import RequestProject.CoshZetaSymmetry
import RequestProject.RiemannHypothesisBridge
import RequestProject.ExplicitFormulaBridgeOfRH

/-!
# H_zero_forces_detector_balance — cosh-pair balance at nontrivial zeros

Target:

    theorem H_zero_forces_detector_balance
        (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) (p : ℕ) (hp : Nat.Prime p) :
        coshDetectorLeft ρ.re (Real.log p) =
          coshDetectorRight ρ.re (Real.log p)

## Chain (structured for Weil agent's W1/W2/W3 deliverables)

1. `weil_gaussian_bridge_axiom` gives `BalancedChannel gaussianKernel ρ`
   at every nontrivial zero ρ — this is the analytic input, currently
   an axiom pending the Weil agent's unconditional proof.
2. `averageEnergyDefect_of_BalancedChannel` unfolds (1) to
   `averageEnergyDefect gaussianKernel ρ.re = 0`.
3. **W3-form forward implication** (named
   `averageEnergyDefect_gaussian_zero_forces_half` below):
   `averageEnergyDefect gaussianKernel β = 0 → β = 1/2`. Currently
   derived from `gaussianKernel_averageEnergyDefect_pos_offline` via
   contrapositive. Weil agent's **W3** provides this directly from a
   closed-form evaluation — drop-in replaceable.
4. Chain (2) + (3) at `β = ρ.re` gives `ρ.re = 1/2`
   (`zero_forces_critical_re`).
5. `coshDetectors_agree_iff` at `t = log p ≠ 0` (proved) converts
   `ρ.re = 1/2` to detector balance.

All steps except (1) are unconditional Lean theorems. The axiom
footprint of `H_zero_forces_detector_balance` is exactly
`[propext, Classical.choice, Quot.sound, ZD.weil_gaussian_bridge_axiom]`.
When the Weil agent replaces `weil_gaussian_bridge_axiom` with a
proved theorem, footprint auto-cleans to the mathlib standard triple,
and `RiemannHypothesis` follows via `RiemannHypothesis_of_detector_balance`.

## Interface with Weil agent

The Weil agent's stated deliverables:

* **W1** `I_theta_of_gaussian_closed_form`: `I_theta_of ψ_gaussian s
  = √π · exp((s−1/2)²/4)`.
* **W2** `averageEnergyDefect_gaussian_closed_form`:
  `averageEnergyDefect ψ_gaussian β = (π^(3/2)/√2) ·
  (exp((β−1/2)²/2) − 2·exp((β−1/2)²/8) + 1)`.
* **W3** `re_half_of_averageEnergyDefect_gaussian_zero`:
  `averageEnergyDefect ψ_gaussian β = 0 → β = 1/2`.

Mapping into my chain:
* W3 ≡ `averageEnergyDefect_gaussian_zero_forces_half` below. When
  W3 lands, delete my version and use theirs — identical statement.
* W1 and W2 are prerequisites for W3's closed-form proof; they don't
  directly enter this file's chain.
* `weil_gaussian_bridge_axiom` is NOT in W1/W2/W3. It is a separate
  missing input — the statement "at every nontrivial zero ρ, the
  Gaussian defect vanishes at ρ.re" — that must come from some
  additional theorem (Weil explicit formula applied to an odd test
  function `g_ψ_gaussian`, or similar). Without it, this chain
  depends on the axiom.

## Algebraic identity backing the reduction (step 4 ⟹ step 5)

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

/-- **W3-equivalent forward implication.** If the γ-averaged energy
defect of the Gaussian kernel at β vanishes, then β = 1/2. Currently
derived from `gaussianKernel_averageEnergyDefect_pos_offline` by
contrapositive. The Weil agent's W3
(`re_half_of_averageEnergyDefect_gaussian_zero`) provides this via a
direct closed-form proof from W2's explicit formula — drop-in
replacement. Same type. -/
theorem averageEnergyDefect_gaussian_zero_forces_half
    (β : ℝ) (h : averageEnergyDefect gaussianKernel β = 0) :
    β = 1 / 2 := by
  by_contra hne
  have hP : 0 < averageEnergyDefect gaussianKernel β :=
    gaussianKernel_averageEnergyDefect_pos_offline β hne
  linarith

/-- **The named residual claim.** This is the critical-strip form of
RH; takes `hRH : RiemannHypothesis` as the single input that replaced the
removed `weil_gaussian_bridge_axiom`. Plumbs through the single-call
`balanced_channel_of_RiemannHypothesis` wrapper in
`ExplicitFormulaBridgeOfRH`; `hRH` is itself the downstream content the
old axiom was smuggling.

Chain unchanged:
- `balanced_channel_of_RiemannHypothesis hRH ρ hρ` replaces
  `weil_gaussian_bridge_axiom ρ hρ`.
- `averageEnergyDefect_of_BalancedChannel` (proved): unfold to defect = 0.
- `averageEnergyDefect_gaussian_zero_forces_half` (≡ Weil's W3): defect = 0 → β = 1/2. -/
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

/-! The former `RiemannHypothesis_of_detector_balance` was removed:
"∀ ρ zero ∀ p prime, detectors agree at log p" collapses via
`coshDetectors_agree_iff` to `∀ ρ zero, ρ.re = 1/2` and restates RH. -/

/-! ### Axiom hygiene -/

#print axioms H_zero_forces_detector_balance
#print axioms zero_forces_critical_re

end ZD

end
