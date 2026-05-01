import Mathlib
import RequestProject.WeilZeroSumClosedForm
import RequestProject.WeilLeftEdgePrimeSum
import RequestProject.WeilArchAtNegOne

/-!
# Step 3c: split closed form for Σ'

Refines `zeroSum_closed_form_modulo_leftEdge` (Step 2c) by splitting the
left-edge integral `leftInt` into `∫archIntegrand β (-1) + ∫reflectedPrime`,
then substituting `leftEdge_reflectedPrime_eq_sum` (Step 2b) for the reflected
piece. Output:

```
Σ'(β) = pairTestMellin β 1
        − Σ_n Λ(n)·pair_cosh_gauss_test β n
        − Σ_n Λ(n)/n · pair_cosh_gauss_test β (1/n)
        + (1/(2π)) · ∫_ℝ archIntegrand β (-1) y dy
```

Unconditional, modulo the σ=-1 archIntegrand integral (which Step 3b will
close in turn).
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroSumSplit

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.PairTestIdentity
open ZD.WeilPositivity.LeftEdgePrimeSum
open ZD.WeilPositivity.ArchAtNegOne
open ZD.WeilPositivity.ZeroSumClosedForm

/-- **Step 3c — split closed form for Σ'.** Substitutes Step 2b's
reflected-prime closed form into Step 2c, leaving the σ=-1 arch integral as
the only remaining opaque quantity.

```
Σ' = pairTestMellin β 1 − Σ_+(β) − Σ_-(β) + (1/(2π)) · ∫archIntegrand β (-1)
```

where `Σ_+(β) := Σ_n Λ(n)·pair_cosh_gauss_test β n` and
`Σ_-(β) := Σ_n Λ(n)/n · pair_cosh_gauss_test β (1/n)`. -/
theorem zeroSum_closed_form_split (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        pairTestMellin β ρ.val)
    = pairTestMellin β 1 -
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) -
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                 ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)) +
      (1 / (2 * ((Real.pi : ℝ) : ℂ))) *
        (∫ y : ℝ, archIntegrand β (-1) y) := by
  -- Step 2c gives Σ' in terms of leftInt.
  have h_2c := zeroSum_closed_form_modulo_leftEdge β hβ
  -- Split leftInt = ∫arch + ∫reflected using leftEdge_integrand_decomposition + Integrable.sub.
  have h_split :
      (∫ y : ℝ, hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
                pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      (∫ y : ℝ, archIntegrand β (-1) y) +
      (∫ y : ℝ,
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
         riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
    rw [← MeasureTheory.integral_add (archIntegrand_at_neg_one_integrable β)
        (reflectedPrimeIntegrand_at_neg_one_integrable β)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    exact leftEdge_integrand_decomposition β y
  -- Substitute h_split into h_2c.
  rw [h_split] at h_2c
  -- Substitute Step 2b's closed form for the reflected piece.
  have h_2b := leftEdge_reflectedPrime_eq_sum β
  rw [h_2b] at h_2c
  -- Algebraic rearrangement.
  have h_πne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h_2c]
  field_simp
  ring

end ZeroSumSplit
end WeilPositivity
end ZD

end
