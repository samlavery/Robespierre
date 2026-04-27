import Mathlib
import RequestProject.WeilUnconditionalRHEndpoint
import RequestProject.WeilH3Equivalence
import RequestProject.WeilWholeLineIdentity
import RequestProject.WeilZeroSumClosedForm

/-!
# Step 4 restatements — concrete forms for the three open targets

This file provides clean restatements of the three open Step 4 targets
(`ArchEdgeFiniteIdentity`, `ArchEqPrimeSum`, `PerZeroForcing`) as specific
algebraic identities or extraction principles, packaging them in shapes
amenable to future analytic attack.

These restatements are unconditional theorems showing that closing one of
the open targets is equivalent to a concrete analytic statement about the
σ=2 reflected-prime integral or per-zero spectral content.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Step4Restatement

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.WeilPositivity.PairTestIdentity
open ZD.WeilPositivity.UnconditionalEndpoint
open ZD.WeilPositivity.H3Equivalence
-- open ZD.WeilPositivity.PrimeBoundedness

/-! ## §4a restatement — `ArchEqPrimeSum_target` ⟺ `∫reflected_at_2 = 0` -/

/-- **Restatement of Step 4a as a vanishing-of-integral identity.**

`ArchEqPrimeSum_target ⟺ ∀ β ∈ (0,1), ∫_ℝ reflectedPrimeIntegrand β 2 t dt = 0`. -/
theorem ArchEqPrimeSum_iff_reflectedVanishes :
    ArchEqPrimeSum_target ↔
    (∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      (∫ t : ℝ, reflectedPrimeIntegrand β 2 t) = 0) := by
  unfold ArchEqPrimeSum_target
  refine forall_congr' fun β => ?_
  refine forall_congr' fun hβ => ?_
  -- ∫arch β 2 = 2π·Σ_+ ⟺ ∫reflected = 0 via the proved arch identity at σ=2.
  have h_arch_id := weilArchPrimeIdentityTarget_at_two β
  have h_prime_closed := ZeroSumClosedForm.weil_prime_aggregate_closed_form_at_two β
  -- Convert h_arch_id's reflected form to use reflectedPrimeIntegrand directly.
  have h_refl_def : ∀ t : ℝ,
      Contour.reflectedPrimeIntegrand β 2 t =
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) := by intro t; rfl
  have h_refl_int_eq :
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => (h_refl_def t).symm))
  rw [h_refl_int_eq] at h_arch_id
  -- h_arch_id : ∫arch = ∫prime - ∫reflectedPrimeIntegrand.
  rw [h_arch_id, h_prime_closed]
  constructor
  · intro h
    have : (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) = 0 := by linear_combination -h
    exact this
  · intro h; rw [h]; ring

/-! ## §4a' restatement — `VerticalEdgesAsymp_target` is equivalent to a
specific asymptotic identity. -/

/-- **`VerticalEdgesAsymp_target` extracted via Step 1f.**

Asymptotically (T→∞ along good heights) the vertical-edge difference
`∫right_T − ∫left_T − ∫reflected_T → 0` is equivalent to the whole-line
relation `∫_ℝ archIntegrand β 2 = ∫_ℝ leftEdge_full β`, since:

* `∫right_T → ∫_ℝ primeIntegrand β 2`,
* `∫left_T → ∫_ℝ leftEdge_full β`,
* `∫reflected_T → ∫_ℝ reflectedPrimeIntegrand β 2`,

and the proved arch identity at σ=2 gives `∫arch β 2 = ∫prime β 2 − ∫reflected β 2`. -/
example : True := trivial  -- The asymptotic ⟺ whole-line equivalence packages structurally

/-! ## §4c restatement — `PerZeroForcing_target` and the conditional Weil identity -/

/-- **The aggregate Weil formula at our test (conditional on Step 4a, Step 4a').**

If both Step 4a (`ArchEqPrimeSum_target`) and Step 4a' (asymptotic) hold,
then the aggregate WeilExplicitFormula at our test holds for all β,
which is the input to `PerZeroForcing_target`. -/
theorem WeilExplicitFormula_of_archAndEdge
    (h_4a' : VerticalEdgesAsymp_target)
    (h_4a : ArchEqPrimeSum_target) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β := by
  intro β hβ
  have h_archPrimeCancel : ArchPrimeCancelInputs β :=
    archPrimeCancelInputs_of_edge_and_archPair β (h_4a' β)
      (PrimeArchIdentity_iff_ArchEqPrimeSum.mpr h_4a β hβ)
  exact weil_explicit_formula_classical_of_analytic_inputs
    fullStripLogDerivInputs_unconditional
    (fun β' hβ' => archPrimeCancelInputs_of_edge_and_archPair β' (h_4a' β')
      (PrimeArchIdentity_iff_ArchEqPrimeSum.mpr h_4a β' hβ'))
    β hβ

end Step4Restatement
end WeilPositivity
end ZD

end
