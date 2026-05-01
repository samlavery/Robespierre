import Mathlib
-- import RequestProject.PairComboClosureScaffold
import RequestProject.WeilLeftEdgePrimeSum
import RequestProject.WeilZeroSumSplitClosedForm
import RequestProject.WeilWholeLineIdentity
import RequestProject.WeilArchAtNegOne

/-!
# Closure paths through Forms A, B, C
-/

namespace ZD.WeilPositivity.PairComboClosurePaths

theorem form_C_iff_archEqPrimeSum (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, ZD.WeilPositivity.Contour.reflectedPrimeIntegrand β 2 t) = 0 ↔
    (∫ t : ℝ, ZD.WeilPositivity.Contour.archIntegrand β 2 t) =
      (2 * ((Real.pi : ℝ) : ℂ)) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((ZD.WeilPositivity.pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  -- ∫arch = ∫prime - ∫reflected (proved); ∫prime = 2π·Σ (proved).
  have h_decomp := ZD.WeilPositivity.Contour.weilArchPrimeIdentityTarget_at_two β
  have h_prime := ZD.WeilPositivity.Contour.primeIntegrand_integral_eq_prime_sum β 2
    (by norm_num : (1 : ℝ) < 2)
  have h_cast : (∫ t : ℝ,
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) *
      ZD.WeilPositivity.Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, ZD.WeilPositivity.Contour.reflectedPrimeIntegrand β 2 t := by
    rfl
  rw [h_cast] at h_decomp
  rw [h_decomp, h_prime]
  constructor
  · intro h_ref_zero
    rw [h_ref_zero, sub_zero]
  · intro h_arch_eq
    have : (2 * ((Real.pi : ℝ) : ℂ)) *
            ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((ZD.WeilPositivity.pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) -
          (∫ t : ℝ, ZD.WeilPositivity.Contour.reflectedPrimeIntegrand β 2 t) =
          (2 * ((Real.pi : ℝ) : ℂ)) *
            ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((ZD.WeilPositivity.pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := h_arch_eq
    linear_combination -this

end ZD.WeilPositivity.PairComboClosurePaths
