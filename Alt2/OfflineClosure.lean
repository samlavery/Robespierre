import RequestProject.HarmonicDiagnostics
import RequestProject.ZetaZeroDefs
import RequestProject.OfflineAmplitudeMethods
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.WeilContour
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilFinalAssembly
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.GaussianClosedForm
import RequestProject.KleinForcerTheorem
import RequestProject.OfflineDetectorProof

/-!
# Offline Closure

This file is the non-circular offline endpoint assembly.

The cosh/Klein/Gaussian side proves the classifier and positivity facts: an
off-line real part has positive detector defect, and detector-defect vanishing
forces `ρ.re = 1/2`.  It does not, by itself, prove the Weil-side vanishing
target.  The Weil-side vanishing target is supplied here as the explicit
per-zero forcing input.

The per-c explicit-formula work is used exactly once: it turns the two named H3
closure identities into `WeilExplicitFormula_pair_cosh_gauss_target β`.
-/

open Complex Set ZetaDefs

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineClosure

open ZD.WeilPositivity.FinalAssembly

/-- The cosh-detector package used by the offline argument.  For every
nontrivial zero it records:
* the prime-by-prime envelope bridge into `coshDetector`,
* strict cosh detection off the critical line,
* finite-prime no-cancellation of the positive excesses.

This is the cosh side only; it contains no Weil explicit-formula input. -/
def CoshDetectorInputs : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    (∀ p : ℕ, Nat.Prime p →
      (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
        balancedEnvelope (↑p) * coshDetector ρ.re (Real.log (↑p))) ∧
    (ρ.re ≠ 1 / 2 →
      (∀ p : ℕ, Nat.Prime p → 1 < coshDetector ρ.re (Real.log (↑p))) ∧
      (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
        0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1)))

/-- The cosh-detector side is already unconditional. -/
theorem coshDetectorInputs_unconditional : CoshDetectorInputs :=
  ZD.WeilPositivity.Contour.CoshReflectedClassifier.offline_detected_no_cancellation

/-- The `(★)`/left-edge form of the cosh-pair explicit formula, uniformly in
`β ∈ (0, 1)`.  This is the H3 closure input used by
`WeilExplicitFormula_pair_cosh_gauss_target_of_star`. -/
def StarIdentityTarget : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
    ZD.WeilPositivity.FinalAssembly.weil_explicit_formula_cosh_pair_target β

/-- The arch-prime pair identity at `σ = 2`, uniformly in `β ∈ (0, 1)`.
By `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`, this is the
same H3 closure content as whole-line reflected-prime cancellation. -/
def ArchPairTarget : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
    ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β

/-- The genuine per-zero forcing input: once the cosh-pair Weil explicit formula
is available for all `β ∈ (0, 1)`, every nontrivial zero has vanishing Gaussian
pair defect.  The downstream cosh classifier then converts this to RH. -/
def PerZeroForcingTarget : Prop :=
  (∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β) →
    ZD.WeilPositivity.WeilVanishesOnZeros

/-- Per-c explicit formula assembly from the two named H3 closure inputs. -/
theorem weil_explicit_formula_of_star_and_archPair
    (h_star : StarIdentityTarget) (h_arch : ArchPairTarget) :
    ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β := by
  intro β hβ
  exact ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target_of_star
    β hβ (h_star β hβ) (h_arch β hβ)

/-- Weil-vanishing on zeros from the explicit-formula inputs plus per-zero
forcing.  This is the precise place where the analytic forcing theorem is
consumed; no RH-level conclusion is hidden in the cosh side. -/
theorem WeilVanishesOnZeros_of_offline_closure
    (h_star : StarIdentityTarget) (h_arch : ArchPairTarget)
    (h_force : PerZeroForcingTarget) :
    ZD.WeilPositivity.WeilVanishesOnZeros :=
  h_force (weil_explicit_formula_of_star_and_archPair h_star h_arch)

/-- Final offline endpoint from the explicit H3 closure inputs and the genuine
per-zero forcing input.  The last line is only the already-proved cosh
classifier `WeilVanishesOnZeros → RiemannHypothesis`. -/
theorem RiemannHypothesis_of_offline_closure
    (_h_cosh : CoshDetectorInputs)
    (h_star : StarIdentityTarget) (h_arch : ArchPairTarget)
    (h_force : PerZeroForcingTarget) :
    RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    (WeilVanishesOnZeros_of_offline_closure h_star h_arch h_force)

/-- Same endpoint with the cosh-detector provider filled in.  The remaining
parameters are the two H3 explicit-formula closures and the genuine per-zero
forcing theorem. -/
theorem RiemannHypothesis_of_offline_closure_unconditional_cosh
    (h_star : StarIdentityTarget) (h_arch : ArchPairTarget)
    (h_force : PerZeroForcingTarget) :
    RiemannHypothesis :=
  RiemannHypothesis_of_offline_closure
    coshDetectorInputs_unconditional h_star h_arch h_force

#print axioms coshDetectorInputs_unconditional
#print axioms weil_explicit_formula_of_star_and_archPair
#print axioms WeilVanishesOnZeros_of_offline_closure
#print axioms RiemannHypothesis_of_offline_closure
#print axioms RiemannHypothesis_of_offline_closure_unconditional_cosh

end OfflineClosure
end WeilPositivity
end ZD

end
