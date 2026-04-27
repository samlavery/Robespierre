import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilIdentityAtPairTest
import RequestProject.WeilLeftEdgePointwiseSplit

/-!
# Vertical-edge difference limit in `archIntegrand + reflectedPrimeIntegrand` form

`verticalEdgeDifference_limit` (in `WeilIdentityAtPairTest.lean`) states the
asymptotic identity along good heights `T → ∞`:

```
I • ∫_(-T)^T LSeries_Λ(2+iy) · pairTestMellin β (2+iy) dy
  − I • ∫_(-T)^T hadamardArchBoundaryTerm(-1+iy) · pairTestMellin β (-1+iy) dy
  → 2πi · (pairTestMellin β 1 − Σ' n(ρ) · pairTestMellin β ρ)
```

Both vertical-edge integrands admit pointwise rewrites in the
`archIntegrand + reflectedPrimeIntegrand` form:

* Right edge (`σ = 2`):
  `LSeries_Λ(2+iy) · pairTestMellin β (2+iy) = primeIntegrand β 2 y =
    archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y` —
  the second equality is just a rearrangement of
  `archIntegrand_eq_primeIntegrand_minus_reflected` at `σ₀ = 2`, which holds
  unconditionally on the line `Re s = 2`.
* Left edge (`σ = -1`):
  `hadamardArchBoundaryTerm(-1+iy) · pairTestMellin β (-1+iy) =
    archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y` —
  this is `leftEdge_integrand_eq_arch_plus_reflected` (already proved by
  unfolding).

Substituting both pointwise identities under `intervalIntegral.integral_congr`
into `verticalEdgeDifference_limit` gives the same Tendsto-style identity but
with both integrands written in the `archIntegrand + reflectedPrimeIntegrand`
form. No new analytic content is needed — this is a pure algebraic
recombination of three already-proved lemmas.
-/

noncomputable section

open Complex MeasureTheory

namespace ZD
namespace WeilPositivity
namespace PairTestIdentity

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZetaDefs

/-- **Right edge pointwise: prime = arch + reflected at σ = 2.**
`primeIntegrand β 2 y = archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y`
pointwise, holding unconditionally on the line `Re s = 2 > 1`. Mirrors the
left-edge analogue `leftEdge_integrand_eq_arch_plus_reflected` (which is at
`σ = -1` and uses the `hadamardArchBoundaryTerm` form). -/
theorem primeIntegrand_two_eq_arch_plus_reflected (β : ℝ) (y : ℝ) :
    primeIntegrand β 2 y
      = archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y := by
  set s : ℂ := (((2:ℝ):ℂ) + (y:ℂ) * I) with hs_def
  have hs_re : s.re = 2 := by simp [s]
  have h1s_re : (1 - s).re = -1 := by simp [s]; ring
  -- Side conditions on the line σ = 2 (mirroring `WeilLeftEdgePointwiseSplit`).
  have hne_zero : s ≠ 0 := fun h => by
    have hh : s.re = (0:ℂ).re := by rw [h]
    rw [hs_re] at hh; norm_num at hh
  have hne_one : s ≠ 1 := fun h => by
    have hh : s.re = (1:ℂ).re := by rw [h]
    rw [hs_re] at hh; norm_num at hh
  have hre2 : (1:ℝ) < s.re := by rw [hs_re]; norm_num
  have hζ_s : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre2
  have hΓ_s : s.Gammaℝ ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [hs_re]; norm_num
  have hΓ_1s : (1 - s).Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : (1 - s).re = (-(2 * (n:ℂ))).re := by rw [hn]
    rw [h1s_re] at hre
    simp at hre
    have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n:ℝ)) = 1)
    omega
  have h1s_ne_zero : (1 - s) ≠ 0 := by
    intro h
    have hh : (1 - s).re = (0:ℂ).re := by rw [h]
    rw [h1s_re] at hh; norm_num at hh
  have hζ_1s : riemannZeta (1 - s) ≠ 0 := by
    have h_xi_s : completedRiemannZeta s = s.Gammaℝ * riemannZeta s :=
      Contour.completed_eq_gammaℝ_mul_zeta hne_zero hΓ_s
    have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
      rw [h_xi_s]; exact mul_ne_zero hΓ_s hζ_s
    have h_xi_1s : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
      completedRiemannZeta_one_sub s
    have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by
      rw [h_xi_1s]; exact h_xi_s_ne
    have h_zeta_1s_eq :
        riemannZeta (1 - s) = completedRiemannZeta (1 - s) / (1 - s).Gammaℝ :=
      riemannZeta_def_of_ne_zero h1s_ne_zero
    rw [h_zeta_1s_eq]
    exact div_ne_zero h_xi_1s_ne hΓ_1s
  -- Apply the pointwise arch=prime-reflected identity at σ₀ = 2.
  have h_arch :=
    Contour.archIntegrand_eq_primeIntegrand_minus_reflected
      β (σ₀ := 2) (by norm_num : (1:ℝ) < 2) y
      hne_zero hne_one hζ_s hζ_1s hΓ_s hΓ_1s
  -- h_arch : archIntegrand β 2 y = primeIntegrand β 2 y -
  --   (deriv riemannZeta (1-s) / riemannZeta (1-s)) * pairTestMellin β s
  -- The subtracted term is exactly `reflectedPrimeIntegrand β 2 y` by definition.
  -- Rearrange to: primeIntegrand = archIntegrand + reflectedPrime.
  have h_ref_unfold : reflectedPrimeIntegrand β 2 y =
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) *
        pairTestMellin β s := by
    show Contour.reflectedPrimeIntegrand β 2 y =
        deriv riemannZeta (1 - (((2:ℝ):ℂ) + (y:ℂ) * I)) /
          riemannZeta (1 - (((2:ℝ):ℂ) + (y:ℂ) * I)) *
        pairTestMellin β (((2:ℝ):ℂ) + (y:ℂ) * I)
    unfold Contour.reflectedPrimeIntegrand
    rfl
  rw [h_ref_unfold]
  linear_combination -h_arch

/-- **Right edge integral identification (arch+reflected form).** Finite-`T`
right-edge integral expressed in `archIntegrand + reflectedPrimeIntegrand`
form. -/
theorem rightEdge_integral_eq_arch_plus_reflected_integral (β : ℝ) (T : ℝ) :
    (∫ y : ℝ in (-T : ℝ)..T,
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((2 : ℂ) + (y : ℂ) * I) *
          pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ in (-T : ℝ)..T,
          archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y := by
  apply intervalIntegral.integral_congr
  intro y _
  show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((2 : ℂ) + (y : ℂ) * I) *
        pairTestMellin β ((2 : ℂ) + (y : ℂ) * I)
      = archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y
  rw [rightEdge_integrand_eq_primeIntegrand]
  exact primeIntegrand_two_eq_arch_plus_reflected β y

/-- **Step 1c (arch+reflected form).** Vertical-edge difference limit, expressed
with both edges in the `archIntegrand + reflectedPrimeIntegrand` form. Mirrors
`verticalEdgeDifference_limit` with the right-edge `LSeries_Λ · pairTestMellin`
rewritten as `archIntegrand β 2 + reflectedPrimeIntegrand β 2` and the
left-edge `hadamardArchBoundaryTerm · pairTestMellin` rewritten as
`archIntegrand β (-1) + reflectedPrimeIntegrand β (-1)`. -/
theorem verticalEdgeDifference_limit_archForm
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖(I • (∫ y : ℝ in (-T : ℝ)..T,
              archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y) -
          I • (∫ y : ℝ in (-T : ℝ)..T,
              archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y)) -
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (((Classical.choose
                (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
                : ℕ) : ℂ)) *
              pairTestMellin β ρ.val)‖ < ε := by
  intro ε hε
  -- Source: vertical-edge difference limit in LSeries / hadamard form.
  obtain ⟨T₀, hT₀_pos, hT₀⟩ := verticalEdgeDifference_limit β hβ ε hε
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hsrc := hT₀ T hT hGood
  -- Rewrite both vertical-edge integrals via the pointwise splits.
  have h_right :
      (∫ y : ℝ in (-T : ℝ)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((2 : ℂ) + (y : ℂ) * I) *
            pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T : ℝ)..T,
            archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y :=
    rightEdge_integral_eq_arch_plus_reflected_integral β T
  have h_left :
      (∫ y : ℝ in (-T : ℝ)..T,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
            pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T : ℝ)..T,
            archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y :=
    leftEdge_integral_eq_arch_plus_reflected_integral β T
  -- Substitute and conclude.
  rw [h_right, h_left] at hsrc
  exact hsrc

#print axioms verticalEdgeDifference_limit_archForm

end PairTestIdentity
end WeilPositivity
end ZD
