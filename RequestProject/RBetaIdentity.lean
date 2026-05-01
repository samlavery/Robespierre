import Mathlib
import RequestProject.PairComboResidueAtZero
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.GaussianAdmissible
import RequestProject.ZetaZeroDefs
import RequestProject.WeilContour
import RequestProject.H3SubstantiveContent
import RequestProject.WeilZeroSumSplitClosedForm
import RequestProject.ArchKernelRectCauchyTransport

/-!
# `R(β)` identification with the σ=0 Mellin value, and the H3 reduction

Proves `pairTestMellin β 0 = R_beta β` (P3 closure) and the iff
`H3(β) ⟺ R(β) = Σ'(β) + Σ_-(β)` under the rectangle Cauchy identity.
-/

open Complex MeasureTheory Set Real Filter

noncomputable section

namespace ZD
namespace RBetaIdentity

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.PairComboResidueAtZero
open ZD.WeilPositivity.H3SubstantiveContent
open ZD.WeilPositivity.ZeroSumSplit
open ZetaDefs

/-! ## (A) Closure of P3: `pairTestMellin β 0 = ((R_beta β : ℝ) : ℂ)` -/

/-- Pointwise cosh-pair factorization: the test function `pair_cosh_gauss_test β`
matches the `R_beta` integrand up to the `1/t` factor. Specifically,

```
pair_cosh_gauss_test β t = (cosh((1-π/3)·t) − 1)·(cosh((2β-1)·t) − 1)·exp(-2t²).
```

Derivation: `pair_cosh_gauss_test = (K_L − K_R)² · exp(-t²)²`, where
`K_L = cosh((β-π/6)·t)` and `K_R = cosh((β-(1-π/6))·t)`. Using
`cosh(a+b) ± cosh(a-b)` with `a = (β-1/2)·t`, `b = (1/2-π/6)·t`:
`K_L = cosh(a+b)`, `K_R = cosh(a-b)`, `K_L − K_R = 2·sinh(a)·sinh(b)`,
hence `(K_L − K_R)² = 4·sinh²(a)·sinh²(b) = (cosh(2a)-1)·(cosh(2b)-1)`
where `2a = (2β-1)·t`, `2b = (1-π/3)·t`. -/
private lemma pair_cosh_gauss_test_eq_R_integrand_times_t (β t : ℝ) :
    pair_cosh_gauss_test β t =
      (Real.cosh ((1 - Real.pi/3) * t) - 1) *
      (Real.cosh ((2 * β - 1) * t) - 1) *
      Real.exp (-2 * t^2) := by
  unfold pair_cosh_gauss_test pairDetectorSqDiff coshDetectorLeft coshDetectorRight
    ψ_gaussian
  have h_exp : Real.exp (-t^2)^2 = Real.exp (-2 * t^2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h_exp]
  have ha : (β - Real.pi/6) * t = (β - 1/2)*t + (1/2 - Real.pi/6)*t := by ring
  have hb : (β - (1 - Real.pi/6)) * t = (β - 1/2)*t - (1/2 - Real.pi/6)*t := by ring
  rw [ha, hb]
  set u := (β - 1/2) * t
  set v := (1/2 - Real.pi/6) * t
  have h1 : (1 - Real.pi/3) * t = 2 * v := by simp [v]; ring
  have h2 : (2 * β - 1) * t = 2 * u := by simp [u]; ring
  rw [h1, h2]
  rw [Real.cosh_add, Real.cosh_sub, Real.cosh_two_mul, Real.cosh_two_mul]
  ring_nf
  rw [Real.cosh_sq, Real.cosh_sq]; ring

/-- **(A) Closure of P3.** The Mellin transform of the cosh-pair Gaussian
test at `s = 0` equals the explicit β-dependent product integral
`R_beta β`. -/
theorem pairTestMellin_at_zero_eq_R_beta (β : ℝ) :
    pairTestMellin β 0 = ((R_beta β : ℝ) : ℂ) := by
  unfold pairTestMellin mellin
  -- ∫ t in Ioi 0, t^(0-1) • (pcgt β t : ℂ) → ((pcgt β t / t : ℝ) : ℂ).
  have h_simp : ∀ t : ℝ, t ∈ Ioi (0:ℝ) →
      (t : ℂ) ^ ((0:ℂ) - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
      (((pair_cosh_gauss_test β t / t : ℝ) : ℂ)) := by
    intro t ht
    have hpos : (0:ℝ) < t := ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [zero_sub, Complex.cpow_neg_one, smul_eq_mul]
    push_cast; field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h_simp]
  rw [integral_complex_ofReal]
  congr 1
  unfold R_beta
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show pair_cosh_gauss_test β t / t = _
  rw [pair_cosh_gauss_test_eq_R_integrand_times_t β t]

/-! ## (B) The `R(β)`-form of the rectangle Cauchy identity

The rectangle Cauchy identity for `F(s) := archKernel(s) · pairTestMellin β s`
on the strip `[-1, 2] × [-T, T]` (with `T → ∞`), counter-clockwise contour,
poles excised at `{0, 1}`, contributes the residue sum

```
(∫_ℝ archIntegrand β 2 t dt) − (∫_ℝ archIntegrand β (-1) y dy)
  = 2π · ((-pairTestMellin β 0) + pairTestMellin β 1).
```

Note: the factor is `2π` (no `I`), matching the `H3SubstantiveContent`
convention. Step 1f (`wholeLineWeilIdentity`) shows the `I·dy`
parametrization cancels with the `i` in `2πi · Σ Res`, leaving real
factor `2π` for the bare `∫_y f(σ + iy) dy` form (consistent with the
sign convention in `archDiff_eq_zeroSumComplement`).

Using (A), the right-hand side becomes `2π · (M(1) − R(β))` where
`M(1) := pairTestMellin β 1`. -/

/-- **The `R(β)`-form of the rectangle Cauchy identity.** This is the
contour-shift identity that closing P1+P2 of `ArchKernelRectCauchyTransport`
would deliver, simplified using (A) to express `pairTestMellin β 0` as
`R_beta β`. -/
def rectCauchyIdentity_R_form (β : ℝ) : Prop :=
  (∫ t : ℝ, archIntegrand β 2 t) - (∫ y : ℝ, archIntegrand β (-1) y) =
    (2 * ((Real.pi : ℝ) : ℂ)) *
      (pairTestMellin β 1 - ((R_beta β : ℝ) : ℂ))

/-! ## (B) The substantive iff -/

/-- The H3 iff under the rectangle Cauchy identity. -/
theorem H3_iff_R_beta_eq_zeroSum_under_rectCauchy
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (h_rect : rectCauchyIdentity_R_form β) :
    (∫ t : ℝ, reflectedPrimeIntegrand β 2 t) = 0 ↔
    (((R_beta β : ℝ) : ℂ) =
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        pairTestMellin β ρ.val) +
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ))) := by
  -- Step 1: H3 ⟺ archDiff_eq_zeroSumComplement (existing axiom-clean iff).
  rw [H3_iff_archDiff β hβ]
  -- Step 2: unfold archDiff_eq_zeroSumComplement and rectCauchyIdentity_R_form.
  unfold archDiff_eq_zeroSumComplement at *
  unfold rectCauchyIdentity_R_form at h_rect
  -- Step 3: substitute h_rect into the LHS.
  rw [h_rect]
  -- Step 4: now the iff is purely algebraic on the RHS.
  -- Goal: 2π·(M(1) - R) = 2π·(M(1) - Σ' - Σ_-)  ⟺  R = Σ' + Σ_-.
  have h_pi_ne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h_2pi_ne : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) h_pi_ne
  -- Abbreviate the sum Σ' + Σ_- to keep equations readable.
  set SumPair : ℂ :=
    (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (((Classical.choose
        (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
      pairTestMellin β ρ.val) +
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
      ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)) with hSumPair_def
  -- Rewrite the archDiff RHS using SumPair via a manual substitution.
  have h_rhs_rw :
      (pairTestMellin β 1 -
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
          pairTestMellin β ρ.val) -
        (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ))) =
      pairTestMellin β 1 - SumPair := by
    rw [hSumPair_def]; ring
  rw [h_rhs_rw]
  constructor
  · intro h_eq
    -- 2π·(M(1) - R) = 2π·(M(1) - SumPair) ⟹ R = SumPair.
    have h_cancel : pairTestMellin β 1 - ((R_beta β : ℝ) : ℂ) =
        pairTestMellin β 1 - SumPair :=
      mul_left_cancel₀ h_2pi_ne h_eq
    linear_combination -h_cancel
  · intro h_R
    -- R = SumPair ⟹ 2π·(M(1) - R) = 2π·(M(1) - SumPair).
    rw [h_R]

end RBetaIdentity
end ZD

end

/-! ## Axiom checks -/

#print axioms ZD.RBetaIdentity.pairTestMellin_at_zero_eq_R_beta
#print axioms ZD.RBetaIdentity.H3_iff_R_beta_eq_zeroSum_under_rectCauchy
