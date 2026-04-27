import Mathlib
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.WeilCoshPairPositivity
import RequestProject.RiemannHypothesisBridge
import RequestProject.WeilH3Equivalence


open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace UnconditionalEndpoint

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly

/-! ## §4a target spec — concrete arch/prime identity at σ = 2 (Step 4a)

By **Step 3d** (`H3_iff_arch_eq_prime_sum`, proved), the H3 sorry is
**equivalent** to a concrete identity between the σ=2 arch integral and the
prime-sum Σ_+(β):

```
H3(β) ⟺ ∫_ℝ archIntegrand β 2 t dt = 2π · Σ_n Λ(n)·pair_cosh_gauss_test β n
```

This refactor uses the cleaner equation form as the Step 4a target. -/

/-- **Target for Step 4a (refactored via Step 3d).** The concrete identity
at σ = 2 between the arch integral and the prime sum. Discharging this
unconditionally gives H3 unconditionally (via Step 3d's iff). -/
def ArchEqPrimeSum_target : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    (∫ t : ℝ, ZD.WeilPositivity.Contour.archIntegrand β 2 t) =
      (2 * ((Real.pi : ℝ) : ℂ)) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)

/-- **Target for Step 4a (legacy form).** Equivalent to `ArchEqPrimeSum_target`
via Step 3d but kept for the existing chain compatibility. -/
def PrimeArchIdentity_target : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β

/-- **Step 3d-based equivalence**: the two target forms are interchangeable. -/
theorem PrimeArchIdentity_iff_ArchEqPrimeSum :
    PrimeArchIdentity_target ↔ ArchEqPrimeSum_target := by
  unfold PrimeArchIdentity_target ArchEqPrimeSum_target
  refine forall_congr' (fun β => ?_)
  refine forall_congr' (fun _ => ?_)
  exact ZD.WeilPositivity.H3Equivalence.H3_iff_arch_eq_prime_sum β

/-! ## §4a' target spec — finite-T arch/edge identity (legacy + asymptotic forms) -/

/-- **Legacy target for Step 4a'.** The finite-`T` rectangle-Cauchy identity
`∫_(-T)^T archIntegrand β 2 y dy = ∫_(-T)^T weilIntegrand at σ=-1 dy`
on good heights. -/
def ArchEdgeFiniteIdentity_target : Prop :=
  ∀ β : ℝ, archIntegrand_interval_eq_left_edge_integral_target β

/-- **Asymptotic target for Step 4a' (cleaner form).** The asymptotic
vertical-edge cancellation `verticalEdges_eq_reflectedPrime_target β` holds
for every β. By
`verticalEdges_eq_reflectedPrime_of_archIntegrand_interval_eq`, the legacy
finite-T form implies this asymptotic form, so `ArchEdgeFiniteIdentity_target`
implies the asymptotic version. -/
def VerticalEdgesAsymp_target : Prop :=
  ∀ β : ℝ, verticalEdges_eq_reflectedPrime_target β

/-- **Step 4a' (legacy) ⟹ Step 4a' (asymptotic).** -/
theorem ArchEdgeFiniteIdentity_implies_VerticalEdgesAsymp
    (h : ArchEdgeFiniteIdentity_target) : VerticalEdgesAsymp_target :=
  fun β => verticalEdges_eq_reflectedPrime_of_archIntegrand_interval_eq β (h β)

/-! ## §4c target spec — per-zero forcing (Step 4c) -/

/-- The per-zero forcing target: aggregate Weil formula implies vanishing on zeros. -/
def PerZeroForcing_target : Prop :=
  (∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β) →
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → gaussianPairDefect ρ.re = 0

/-! ## §4 endpoint composition -/

/-- Conditional endpoint: from the three analytic targets, delivers `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_targets
    (h_4a' : ArchEdgeFiniteIdentity_target)
    (h_4a : PrimeArchIdentity_target)
    (h_4c : PerZeroForcing_target) :
    RiemannHypothesis := by
  -- Step 4b': verticalEdges_eq_reflectedPrime from h_4a'.
  have h_edge : ∀ β : ℝ, verticalEdges_eq_reflectedPrime_target β :=
    fun β => verticalEdges_eq_reflectedPrime_of_archIntegrand_interval_eq β (h_4a' β)
  -- Step 4b: build ArchPrimeCancelInputs β from h_edge + h_4a.
  have h_archPrimeCancel : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → ArchPrimeCancelInputs β :=
    fun β hβ =>
      archPrimeCancelInputs_of_edge_and_archPair β (h_edge β) (h_4a β hβ)
  -- Run the unconditional explicit-formula chain with the new inputs.
  have h_weilFormula : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
    weil_explicit_formula_classical_of_analytic_inputs
      fullStripLogDerivInputs_unconditional
      h_archPrimeCancel
  -- Step 4c: extract per-zero vanishing.
  have h_weilVanishes : WeilVanishesOnZeros := h_4c h_weilFormula
  -- Step 4d: route to RH via the existing cosh-side bridge.
  exact RiemannHypothesis_of_WeilVanishesOnZeros h_weilVanishes

/-! ## Endpoint via the cleaner asymptotic vertical-edge target -/

/-- **Cleanest endpoint** — uses the asymptotic vertical-edge target directly,
which is naturally produced by the kind of arguments Step 1f's infrastructure
supports. Doesn't require the strict finite-T form (`ArchEdgeFiniteIdentity_target`). -/
theorem RiemannHypothesis_of_asymp_targets
    (h_edges : VerticalEdgesAsymp_target)
    (h_4a_concrete : ArchEqPrimeSum_target)
    (h_4c : PerZeroForcing_target) :
    RiemannHypothesis := by
  have h_archPrimeCancel : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → ArchPrimeCancelInputs β :=
    fun β hβ =>
      archPrimeCancelInputs_of_edge_and_archPair β (h_edges β)
        (PrimeArchIdentity_iff_ArchEqPrimeSum.mpr h_4a_concrete β hβ)
  have h_weilFormula : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
    weil_explicit_formula_classical_of_analytic_inputs
      fullStripLogDerivInputs_unconditional
      h_archPrimeCancel
  exact RiemannHypothesis_of_WeilVanishesOnZeros (h_4c h_weilFormula)

/-! ## Refactored endpoint via Step 3d -/

/-- **Refactored conditional endpoint** using the concrete arch=prime-sum
target instead of the H3 form. By Step 3d's equivalence, this is the same
content but in a cleaner shape. -/
theorem RiemannHypothesis_of_concrete_targets
    (h_4a' : ArchEdgeFiniteIdentity_target)
    (h_4a_concrete : ArchEqPrimeSum_target)
    (h_4c : PerZeroForcing_target) :
    RiemannHypothesis :=
  RiemannHypothesis_of_targets h_4a'
    (PrimeArchIdentity_iff_ArchEqPrimeSum.mpr h_4a_concrete)
    h_4c


end UnconditionalEndpoint
end WeilPositivity
end ZD

end
