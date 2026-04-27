import Mathlib
import RequestProject.XiHadamardFactorization
import RequestProject.XiProductMultPartialFraction
import RequestProject.LogDerivIdentity
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilArchKernelResidues
import RequestProject.H3SubstantiveContent

-- import RequestProject.WeilReflectedPrimeCoshExpansion

/-!
# H3 via the Hadamard factorization of ξ
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD.WeilPositivity.H3ViaHadamard

theorem zeta_logDeriv_hadamard_expansion :
    ∃ A : ℂ, ∀ (s : ℂ),
      s ≠ 0 → s ≠ 1 → riemannZeta s ≠ 0 → Complex.Gammaℝ s ≠ 0 →
      s ∉ ZD.NontrivialZeros →
      deriv riemannZeta s / riemannZeta s =
        A
        + (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
        - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
  obtain ⟨A, hA⟩ := xi_logDeriv_sub_product_const_off_zeros
  refine ⟨A, ?_⟩
  intro s hs0 hs1 hζ hΓ hsNZ
  have hbridge :=
    riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ_of_ne s hs0 hs1 hζ hΓ
  have hxi : deriv riemannXi s / riemannXi s
              - logDeriv xiProductMult s = A := hA s hsNZ
  have hpf :=
    logDeriv_xiProductMult_partial_fraction (s := s) hsNZ
  have hxiLog : deriv riemannXi s / riemannXi s
              = A + logDeriv xiProductMult s := by linear_combination hxi
  rw [hbridge, hxiLog, hpf]

/-- Convenience name for the Hadamard zero-sum. -/
def hadamardZeroSum (s : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)

/-- Compact restatement of the Hadamard expansion using `hadamardZeroSum`. -/
theorem zeta_logDeriv_hadamard_expansion' :
    ∃ A : ℂ, ∀ (s : ℂ),
      s ≠ 0 → s ≠ 1 → riemannZeta s ≠ 0 → Complex.Gammaℝ s ≠ 0 →
      s ∉ ZD.NontrivialZeros →
      deriv riemannZeta s / riemannZeta s =
        A + hadamardZeroSum s
        - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s :=
  zeta_logDeriv_hadamard_expansion

theorem reflectedPrimeIntegrand_hadamard_pointwise (β : ℝ) :
    ∃ A : ℂ, ∀ (t : ℝ),
      (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 →
      (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 1 →
      riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 →
      Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 →
      (1 - ((2 : ℂ) + (t : ℂ) * I)) ∉ ZD.NontrivialZeros →
      Contour.reflectedPrimeIntegrand β 2 t =
        (A + hadamardZeroSum (1 - ((2 : ℂ) + (t : ℂ) * I))
            - 1 / (1 - ((2 : ℂ) + (t : ℂ) * I))
            - 1 / ((1 - ((2 : ℂ) + (t : ℂ) * I)) - 1)
            - logDeriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I))) *
        pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) := by
  obtain ⟨A, hA⟩ := zeta_logDeriv_hadamard_expansion'
  refine ⟨A, ?_⟩
  intro t hs0 hs1 hζ hΓ hsNZ
  have h := hA (1 - ((2 : ℂ) + (t : ℂ) * I)) hs0 hs1 hζ hΓ hsNZ
  show deriv riemannZeta (1 - ((2:ℂ) + (t:ℂ) * I))
        / riemannZeta (1 - ((2:ℂ) + (t:ℂ) * I))
       * pairTestMellin β ((2:ℂ) + (t:ℂ) * I) = _
  rw [h]

def H3_HadamardFubini (β : ℝ) (A : ℂ) : Prop :=
  (∫ t : ℝ, (A + hadamardZeroSum (1 - ((2:ℂ) + (t:ℂ) * I))
            - 1 / (1 - ((2:ℂ) + (t:ℂ) * I))
            - 1 / ((1 - ((2:ℂ) + (t:ℂ) * I)) - 1)
            - logDeriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ) * I))) *
        pairTestMellin β ((2:ℂ) + (t:ℂ) * I))
  = (∫ t : ℝ, A * pairTestMellin β ((2:ℂ) + (t:ℂ) * I))
  + (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) *
        ∫ t : ℝ, (1 / ((1 - ((2:ℂ) + (t:ℂ) * I)) - ρ.val) + 1 / ρ.val) *
                  pairTestMellin β ((2:ℂ) + (t:ℂ) * I))
  + (∫ t : ℝ, (- 1 / (1 - ((2:ℂ) + (t:ℂ) * I))
              - 1 / ((1 - ((2:ℂ) + (t:ℂ) * I)) - 1)
              - logDeriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ) * I))) *
              pairTestMellin β ((2:ℂ) + (t:ℂ) * I))

def H3_HadamardCauchy (β : ℝ) : Prop :=
  ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    ∃ c_ρ : ℂ,
      (∫ t : ℝ, (1 / ((1 - ((2:ℂ) + (t:ℂ) * I)) - ρ.val) + 1 / ρ.val) *
        pairTestMellin β ((2:ℂ) + (t:ℂ) * I)) =
      c_ρ * pairTestMellin β ρ.val

def H3_via_hadamard_target (β : ℝ) : Prop :=
  ∃ A : ℂ, H3_HadamardFubini β A ∧ H3_HadamardCauchy β

end ZD.WeilPositivity.H3ViaHadamard

end
