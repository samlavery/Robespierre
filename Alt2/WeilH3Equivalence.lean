import Mathlib
import RequestProject.WeilReflectedPrimeVanishingWeilside
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilZeroSumClosedForm
-- import RequestProject.OfflineDetectorProof



/-!
# Step 3d: H3 ⟺ specific identity between closed-form quantities
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace H3Equivalence

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing
--open ZD.WeilPositivity.PrimeBoundedness

/-- **Step 3d — H3 ⟺ ∫arch β 2 = 2π · Σ_+(β).**

The H3 sorry is exactly equivalent (algebraically, unconditionally) to a
specific identity between the σ=2 arch integral `∫_ℝ archIntegrand β 2 t dt`
and the prime sum `2π · Σ_n Λ(n)·pair_cosh_gauss_test β n`. -/
theorem H3_iff_arch_eq_prime_sum (β : ℝ) :
    archPair_eq_primePair_at_two_target β ↔
    (∫ t : ℝ, archIntegrand β 2 t) =
      (2 * ((Real.pi : ℝ) : ℂ)) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  -- Forward: H3 ⟹ arch=prime_sum.
  -- Backward: arch=prime_sum ⟹ H3.
  -- Both directions go through:
  --   archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes : H3 ⟺ ∫reflected = 0.
  --   weilArchPrimeIdentityTarget_at_two : ∫arch = ∫prime - ∫reflected.
  --   weil_prime_aggregate_closed_form_at_two : ∫prime = 2π · Σ_+.
  rw [archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes]
  have h_arch_id := weilArchPrimeIdentityTarget_at_two β
  -- h_arch_id : ∫arch = ∫prime - ∫reflected (with reflected as ζ'/ζ form).
  have h_prime_closed := ZeroSumClosedForm.weil_prime_aggregate_closed_form_at_two β
  -- h_prime_closed : ∫prime = 2π · Σ_+.
  -- Convert reflected form in h_arch_id to use reflectedPrimeIntegrand.
  have h_refl_def : ∀ t : ℝ,
      Contour.reflectedPrimeIntegrand β 2 t =
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) := by
    intro t; rfl
  have h_refl_int_eq :
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => (h_refl_def t).symm))
  rw [h_refl_int_eq] at h_arch_id
  -- h_arch_id : ∫arch = ∫prime - ∫reflectedPrimeIntegrand.
  -- Algebraic equivalence: ∫reflected = 0 ⟺ ∫arch = ∫prime ⟺ ∫arch = 2π · Σ_+.
  rw [h_arch_id]
  rw [h_prime_closed]
  constructor
  · intro h; rw [h]; ring
  · intro h
    -- h : 2π·Σ - ∫reflected = 2π·Σ. Subtract: -∫reflected = 0 ⟹ ∫reflected = 0.
    have : -(∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) = 0 := by linear_combination h
    linear_combination -this

end H3Equivalence
end WeilPositivity
end ZD

end
