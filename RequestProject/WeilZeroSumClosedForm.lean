import Mathlib
import RequestProject.WeilWholeLineIdentity

/-!
# Step 2c: Σ' closed form (modulo the unsplit left-edge integral)

Composes Step 1f (whole-line Weil identity) + Step 2a (right edge closed form)
into an unconditional expression for `Σ' n(ρ)·pairTestMellin β ρ` in terms of
`Σ_+(β) := Σ_n Λ(n)·pair_cosh_gauss_test β n` and the still-opaque
left-edge integral `∫leftEdge β`.

```
Σ'(β) = pairTestMellin β 1 − Σ_+(β) + (1/(2π)) · ∫leftEdge β
```

where `∫leftEdge β := ∫_ℝ hadamardArchBoundaryTerm(-1+iy) · pairTestMellin β (-1+iy) dy`.

Step 3 splits `∫leftEdge` into `∫archIntegrand β (-1) + ∫reflectedPrime β (-1)`
and substitutes the closed forms (Step 2b proved the reflected piece;
Step 3b proves the arch piece).

This is unconditional. -/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroSumClosedForm

theorem weil_prime_aggregate_closed_form_at_two (β : ℝ) :
    ∫ t : ℝ, Contour.primeIntegrand β 2 t =
      (2 * Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) :=
  Contour.primeIntegrand_integral_eq_prime_sum β 2 (by norm_num : (1 : ℝ) < 2)

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.PairTestIdentity
-- open ZD.WeilPositivity.PrimeBoundedness

/-- **Step 2c — closed form for Σ' modulo left-edge integral (unconditional).**

```
Σ' n(ρ)·pairTestMellin β ρ = pairTestMellin β 1
  − Σ_n Λ(n)·pair_cosh_gauss_test β n
  + (1/(2π)) · ∫_ℝ hadamardArchBoundaryTerm(-1+iy)·pairTestMellin β (-1+iy) dy
```

Proof: algebraic rearrangement of Step 1f, with `∫primeIntegrand β 2`
substituted by Step 2a's closed form. The left-edge integral remains opaque
(to be split by Step 3). -/
theorem zeroSum_closed_form_modulo_leftEdge (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        pairTestMellin β ρ.val)
    = pairTestMellin β 1 -
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) +
      (1 / (2 * ((Real.pi : ℝ) : ℂ))) *
        (∫ y : ℝ,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  -- (1) Step 1f gives the whole-line identity.
  have h_1f := wholeLineWeilIdentity β hβ
  -- (2) Step 2a: closed form for ∫primeIntegrand β 2.
  have h_2a := weil_prime_aggregate_closed_form_at_two β
  -- Substitute h_2a into h_1f to obtain the simpler form.
  rw [h_2a] at h_1f
  -- Convert smul to mul for ring tactics.
  simp only [smul_eq_mul] at h_1f
  -- Algebraic solve for Σ'.
  have h_2pi_ne : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) hpi
  have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_2piI_ne : (2 * ((Real.pi : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero h_2pi_ne h_I_ne
  -- linear_combination after rearrangement.
  -- From h_1f: I·(2π·Σ_+) − I·∫left = 2πI·(h(1) − Σ').
  -- Divide by 2πI: Σ_+ − (1/(2π))·∫left = h(1) − Σ'.
  -- Solve: Σ' = h(1) − Σ_+ + (1/(2π))·∫left.
  set Sum_plus : ℂ :=
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) with hSum_plus_def
  set leftInt : ℂ :=
    ∫ y : ℝ, hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
             pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hleftInt_def
  set Sigma' : ℂ :=
    ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (((Classical.choose
        (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
      pairTestMellin β ρ.val with hSigma'_def
  -- h_1f after substitutions.
  change I • (2 * ((Real.pi : ℝ) : ℂ) * Sum_plus) - I • leftInt =
         2 * ((Real.pi : ℝ) : ℂ) * I * (pairTestMellin β 1 - Sigma') at h_1f
  -- Goal restate.
  show Sigma' = pairTestMellin β 1 - Sum_plus +
       (1 / (2 * ((Real.pi : ℝ) : ℂ))) * leftInt
  -- Convert smul to mul.
  simp only [smul_eq_mul] at h_1f
  -- Step 1: factor I and divide.
  have h_div_I : 2 * ((Real.pi : ℝ) : ℂ) * Sum_plus - leftInt =
                 2 * ((Real.pi : ℝ) : ℂ) * (pairTestMellin β 1 - Sigma') := by
    have h_factored : I * (2 * ((Real.pi : ℝ) : ℂ) * Sum_plus - leftInt) =
                      I * (2 * ((Real.pi : ℝ) : ℂ) * (pairTestMellin β 1 - Sigma')) := by
      linear_combination h_1f
    exact mul_left_cancel₀ h_I_ne h_factored
  -- Step 2: solve for Sigma' explicitly.
  -- h_div_I : 2π · Sum_plus − leftInt = 2π · (h(1) − Σ').
  -- Rearrange: Σ' = h(1) − Sum_plus + leftInt/(2π).
  have h_πne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h_2π_ne : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := h_2pi_ne
  -- Direct algebra: divide h_div_I by 2π, rearrange.
  have h_step : Sigma' = pairTestMellin β 1 - Sum_plus +
                         leftInt / (2 * ((Real.pi : ℝ) : ℂ)) := by
    have h_eq : 2 * ((Real.pi : ℝ) : ℂ) * Sigma' =
                2 * ((Real.pi : ℝ) : ℂ) *
                  (pairTestMellin β 1 - Sum_plus +
                   leftInt / (2 * ((Real.pi : ℝ) : ℂ))) := by
      have h := h_div_I
      field_simp
      linear_combination h_div_I
    exact mul_left_cancel₀ h_2π_ne h_eq
  rw [h_step]; ring

end ZeroSumClosedForm
end WeilPositivity
end ZD

end
