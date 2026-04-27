import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilFinalAssembly
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.CoshGaussMellinContinuation
import RequestProject.RectCauchyNegLogDerivZetaCoshGaussExt
import RequestProject.WeilRectResidueIdentityDischarge
import RequestProject.WeilRectangleZerosFull
import RequestProject.XiOrderSummable
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.ZetaZeroDefs
import RequestProject.WeilExplicitFormulaPlaceholder

/-!
# Weil Explicit Formula from the 5-Component Per-c Rect-Cauchy Sum

This file derives `WeilExplicitFormula_pair_cosh_gauss_target β` by summing the per-c theorem
`rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum`
over the five cosh-pair components

  c ∈ {2β − π/3,  2 − π/3 − 2β,  1 − π/3,  2β − 1,  0}

with weights {1/2, 1/2, −1, −1, 1}.

## Key structural observations

1. **negLogDerivZeta0 cancels**: the weights sum to 1/2 + 1/2 − 1 − 1 + 1 = 0,
   so the `negLogDerivZeta0` residue at s = 0 drops out.

2. **LHS identifies with pairTestMellin**: the five-weight combination
   `Σ wᵢ · coshGaussMellinExt cᵢ = pairTestMellin β` for all `Re s > -2`,
   proved by writing each `coshGaussMellinExt c = gaussMellinClosed + mellin(coshDiff c)`,
   cancelling the `gaussMellinClosed` parts (weight sum = 0), and applying
   analytic continuation from the agreement on `Re s > 0`.

3. **RHS at s = 1**: weighted sum collapses to `pairTestMellin β 1 = gaussianPairDefect β`.

4. **RHS zero-sum**: for nontrivial zeros ρ (Re ρ > 0), weighted sum equals `pairTestMellin β ρ`.

## Axiom footprint

`rectangleResidueIdentity_from_perC` is fully axiom-clean (`[propext,
Classical.choice, Quot.sound]`), providing an explicit per-c decomposition
proof of the finite-T rectangle residue identity.

`WeilExplicitFormula_pair_cosh_gauss_target_of_star` is also axiom-clean but
conditional on two explicit H3-closure hypotheses:
- `h_star  : weil_explicit_formula_cosh_pair_target β` — the authorized `(★)`
  placeholder (`WeilExplicitFormulaPlaceholder.lean:65`), equivalent to the
  Weil explicit formula in arch-vs-left-edge integral form.
- `h_refl_zero : archPair_eq_primePair_at_two_target β` — the parallel H3
  sorry (`WeilReflectedPrimeVanishingWeilside.lean:1098`), equivalent to
  `∫reflectedPrimeIntegrand β 2 = 0`.

Both hypotheses ride on the same open H3-closure obligation; once either is
proved the other follows. When both are supplied the proof is a short
algebraic combination via `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum`
and `weilIntegrand_left_edge_integral_value`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.CoshGaussMellinContinuation

/-! ## §1 The 5-weight combo of coshGaussMellinExt equals pairTestMellin everywhere on Re s > -2 -/

/-- On `Re s > 0`, `coshGaussMellinExt c s = coshGaussMellin c s`. -/
private lemma coshGaussMellinExt_eq_on_pos (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    coshGaussMellinExt c s = coshGaussMellin c s :=
  coshGaussMellinExt_eq_coshGaussMellin c hs

/-- The five-weight combo of `coshGaussMellinExt` equals `pairTestMellin β s` on `Re s > 0`. -/
private lemma pairTestMellin_eq_sum_coshGaussMellinExt_pos (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairTestMellin β s =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s -
      coshGaussMellinExt (1 - Real.pi/3) s -
      coshGaussMellinExt (2*β - 1) s +
      coshGaussMellinExt 0 s := by
  rw [coshGaussMellinExt_eq_on_pos _ hs, coshGaussMellinExt_eq_on_pos _ hs,
      coshGaussMellinExt_eq_on_pos _ hs, coshGaussMellinExt_eq_on_pos _ hs,
      coshGaussMellinExt_eq_on_pos _ hs, coshGaussMellin_zero]
  exact pairTestMellin_cosh_expansion β s
    (mellinConvergent_coshGauss _ hs) (mellinConvergent_coshGauss _ hs)
    (mellinConvergent_coshGauss _ hs) (mellinConvergent_coshGauss _ hs)
    (by have h := mellinConvergent_coshGauss (0:ℝ) hs
        have heq : (fun t : ℝ => ((Real.cosh (0 * t) * Real.exp (-2 * t ^ 2) : ℝ) : ℂ)) =
                   (fun t : ℝ => ((Real.exp (-2 * t ^ 2) : ℝ) : ℂ)) := by
          funext t; norm_cast; simp [Real.cosh_zero]
        rwa [heq] at h)

/-- The five-weight combo of `coshGaussMellinExt` is analytic on `{Re s > -2}`.

Key: write `coshGaussMellinExt c s = gaussMellinClosed s + mellin (coshDiff c) s`.
The weighted sum of `gaussMellinClosed` vanishes (weight-sum = 0), leaving
`Σ wᵢ · mellin (coshDiff cᵢ)` which is analytic on `{Re s > -2}`. -/
private lemma pairCombo_analyticAt (β : ℝ) {s : ℂ} (hs : -2 < s.re) :
    AnalyticAt ℂ (fun s =>
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s -
      coshGaussMellinExt (1 - Real.pi/3) s -
      coshGaussMellinExt (2*β - 1) s +
      coshGaussMellinExt 0 s) s := by
  -- Write the combo in terms of mellin(coshDiff) only, cancelling gaussMellinClosed.
  have h_eq : (fun s : ℂ =>
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s -
      coshGaussMellinExt (1 - Real.pi/3) s -
      coshGaussMellinExt (2*β - 1) s +
      coshGaussMellinExt 0 s) = (fun s : ℂ =>
      (1/2 : ℂ) * mellin (coshDiff (2*β - Real.pi/3)) s +
      (1/2 : ℂ) * mellin (coshDiff (2 - Real.pi/3 - 2*β)) s -
      mellin (coshDiff (1 - Real.pi/3)) s -
      mellin (coshDiff (2*β - 1)) s +
      mellin (coshDiff 0) s) := by
    funext z
    simp only [coshGaussMellinExt]
    ring
  rw [h_eq]
  -- Each mellin (coshDiff c) is analytic on {Re s > -2}.
  have h1 := coshDiffMellin_analyticAt (2*β - Real.pi/3) hs
  have h2 := coshDiffMellin_analyticAt (2 - Real.pi/3 - 2*β) hs
  have h3 := coshDiffMellin_analyticAt (1 - Real.pi/3) hs
  have h4 := coshDiffMellin_analyticAt (2*β - 1) hs
  have h5 := coshDiffMellin_analyticAt (0 : ℝ) hs
  exact ((((analyticAt_const.mul h1).add (analyticAt_const.mul h2)).sub h3).sub h4).add h5

/-- The five-weight combo equals `pairTestMellin β` for ALL `Re s > -2`,
by analytic continuation from the agreement on `Re s > 0`. -/
theorem pairTestMellin_eq_sum_coshGaussMellinExt (β : ℝ) {s : ℂ} (hs : -2 < s.re) :
    pairTestMellin β s =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s -
      coshGaussMellinExt (1 - Real.pi/3) s -
      coshGaussMellinExt (2*β - 1) s +
      coshGaussMellinExt 0 s := by
  -- Set up: f = pairTestMellin β, g = combo. Both analytic on U = {Re s > -2}.
  set U : Set ℂ := {z | -2 < z.re}
  set g : ℂ → ℂ := fun s =>
    (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) s +
    (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) s -
    coshGaussMellinExt (1 - Real.pi/3) s -
    coshGaussMellinExt (2*β - 1) s +
    coshGaussMellinExt 0 s
  -- f is analytic on U (it's analytic on {Re s > -4}).
  have hf_an : AnalyticOnNhd ℂ (pairTestMellin β) U := by
    intro z (hz : -2 < z.re)
    apply DifferentiableOn.analyticAt (s := {w | -4 < w.re})
    · intro w hw
      exact (pairTestMellin_differentiableAt_re_gt_neg_four β hw).differentiableWithinAt
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show -4 < z.re by linarith)
  -- g is analytic on U.
  have hg_an : AnalyticOnNhd ℂ g U := fun z hz => pairCombo_analyticAt β hz
  -- U is preconnected (it's a right half-plane, hence convex).
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt (r := -2)).isPreconnected
  -- Both agree on {Re s > 0} ∋ 2, hence f - g vanishes near (2 : ℂ).
  have hz₀_mem : (2 : ℂ) ∈ U := by simp [U]
  have h_diff_eventuallyEq : (pairTestMellin β - g) =ᶠ[nhds (2 : ℂ)] 0 := by
    apply Filter.eventually_of_mem
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (2 : ℂ).re by norm_num)
    · intro z hz
      simp only [Pi.sub_apply, Pi.zero_apply]
      exact sub_eq_zero.mpr (pairTestMellin_eq_sum_coshGaussMellinExt_pos β hz)
  -- By the identity theorem: (f - g) = 0 on all of U.
  exact sub_eq_zero.mp
    ((hf_an.sub hg_an).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hU_conn hz₀_mem h_diff_eventuallyEq hs)

/-! ## §2 Weighted sum of per-c identities gives rectangleResidueIdentity_target β -/

/-- **Proof of `rectangleResidueIdentity_target β` via the per-c decomposition.**

Sums the per-c theorem over 5 c-values with weights {1/2, 1/2, −1, −1, 1}.
The `negLogDerivZeta0` terms cancel (weight-sum = 0), and the five
`coshGaussMellinExt cᵢ` combine into `pairTestMellin β` by
`pairTestMellin_eq_sum_coshGaussMellinExt`. -/
theorem rectangleResidueIdentity_from_perC
    (β : ℝ) (_hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    rectangleResidueIdentity_target β := by
  intro T hT hGood n Z hZ_mem hZ_complete
  -- Step 1: Get the per-c identity at each of the 5 c-values.
  have h_c1 := rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    (2*β - Real.pi/3) hT hGood n Z hZ_mem hZ_complete
  have h_c2 := rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    (2 - Real.pi/3 - 2*β) hT hGood n Z hZ_mem hZ_complete
  have h_c3 := rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    (1 - Real.pi/3) hT hGood n Z hZ_mem hZ_complete
  have h_c4 := rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    (2*β - 1) hT hGood n Z hZ_mem hZ_complete
  have h_c5 := rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    0 hT hGood n Z hZ_mem hZ_complete
  -- Step 2: pairTestMellin β at s = 1 and at each zero ρ ∈ Z.
  have h_at1 : pairTestMellin β 1 =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) 1 +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) 1 -
      coshGaussMellinExt (1 - Real.pi/3) 1 -
      coshGaussMellinExt (2*β - 1) 1 +
      coshGaussMellinExt 0 1 :=
    pairTestMellin_eq_sum_coshGaussMellinExt β (by norm_num)
  have h_at_rho : ∀ ρ ∈ Z, pairTestMellin β ρ =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) ρ +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ -
      coshGaussMellinExt (1 - Real.pi/3) ρ -
      coshGaussMellinExt (2*β - 1) ρ +
      coshGaussMellinExt 0 ρ := by
    intro ρ hρ
    obtain ⟨hNZ, _, _, _, _, _⟩ := hZ_mem ρ hρ
    exact pairTestMellin_eq_sum_coshGaussMellinExt β (by linarith [hNZ.1])
  -- Step 3: Expand the zero-sum via linearity.
  have h_sum_eq :
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * pairTestMellin β ρ =
      (1/2 : ℂ) * ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) ρ +
      (1/2 : ℂ) * ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ -
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt (1 - Real.pi/3) ρ -
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt (2*β - 1) ρ +
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt 0 ρ := by
    have h_term : ∀ ρ ∈ Z, (↑(n ρ) : ℂ) * pairTestMellin β ρ =
        (1/2:ℂ) * ((↑(n ρ) : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) ρ) +
        (1/2:ℂ) * ((↑(n ρ) : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ) -
        (↑(n ρ) : ℂ) * coshGaussMellinExt (1 - Real.pi/3) ρ -
        (↑(n ρ) : ℂ) * coshGaussMellinExt (2*β - 1) ρ +
        (↑(n ρ) : ℂ) * coshGaussMellinExt 0 ρ := fun ρ hρ => by
      rw [h_at_rho ρ hρ]; ring
    rw [Finset.sum_congr rfl h_term]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Step 4: Show rectContourIntegral of weilIntegrand(pairTestMellin β) equals the
  -- linear combination of the five per-c integrals.
  -- Since weilIntegrand h s = (-ζ'/ζ)(s) * h(s), linearity in h gives pointwise equality;
  -- then integral linearity follows from intervalIntegral.integral_congr.
  have h_ptwise_re : ∀ z : ℂ, -2 < z.re →
      weilIntegrand (pairTestMellin β) z =
        (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) z +
        (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) z -
        weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) z -
        weilIntegrand (coshGaussMellinExt (2*β - 1)) z +
        weilIntegrand (coshGaussMellinExt 0) z := by
    intro z hz
    simp only [weilIntegrand]
    rw [pairTestMellin_eq_sum_coshGaussMellinExt β hz]
    ring
  -- All rectangle boundary points have Re z ≥ -1 > -2.
  have h_integ_eq :
      rectContourIntegral (-1) 2 T (weilIntegrand (pairTestMellin β)) =
      (1/2 : ℂ) * rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3))) +
      (1/2 : ℂ) * rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β))) -
      rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt (1 - Real.pi/3))) -
      rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt (2*β - 1))) +
      rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt 0)) := by
    -- Unfold rectContourIntegral and use integral_congr on each of the 4 edges.
    unfold rectContourIntegral
    -- On the bottom edge: z = x + (-T)*I where x ∈ [-1, 2], Re z = x ≥ -1 > -2.
    have h_bot : ∀ x ∈ Set.uIcc (-1:ℝ) 2,
        weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I) =
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) ((x : ℂ) + (-T : ℝ) * I) +
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) ((x : ℂ) + (-T : ℝ) * I) -
          weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) ((x : ℂ) + (-T : ℝ) * I) -
          weilIntegrand (coshGaussMellinExt (2*β - 1)) ((x : ℂ) + (-T : ℝ) * I) +
          weilIntegrand (coshGaussMellinExt 0) ((x : ℂ) + (-T : ℝ) * I) := by
      intro x hx
      apply h_ptwise_re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx; linarith [hx.1]
    have h_top : ∀ x ∈ Set.uIcc (-1:ℝ) 2,
        weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I) =
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) ((x : ℂ) + (T : ℝ) * I) +
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) ((x : ℂ) + (T : ℝ) * I) -
          weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) ((x : ℂ) + (T : ℝ) * I) -
          weilIntegrand (coshGaussMellinExt (2*β - 1)) ((x : ℂ) + (T : ℝ) * I) +
          weilIntegrand (coshGaussMellinExt 0) ((x : ℂ) + (T : ℝ) * I) := by
      intro x hx
      apply h_ptwise_re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx; linarith [hx.1]
    have h_right : ∀ y ∈ Set.uIcc (-T) T,
        weilIntegrand (pairTestMellin β) (((2:ℝ) : ℂ) + (y : ℂ) * I) =
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) (((2:ℝ) : ℂ) + (y : ℂ) * I) +
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) (((2:ℝ) : ℂ) + (y : ℂ) * I) -
          weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) (((2:ℝ) : ℂ) + (y : ℂ) * I) -
          weilIntegrand (coshGaussMellinExt (2*β - 1)) (((2:ℝ) : ℂ) + (y : ℂ) * I) +
          weilIntegrand (coshGaussMellinExt 0) (((2:ℝ) : ℂ) + (y : ℂ) * I) :=
      fun y _ => h_ptwise_re _ (by norm_num)
    have h_left : ∀ y ∈ Set.uIcc (-T) T,
        weilIntegrand (pairTestMellin β) (((-1:ℝ) : ℂ) + (y : ℂ) * I) =
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) +
          (1/2 : ℂ) * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) -
          weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) -
          weilIntegrand (coshGaussMellinExt (2*β - 1)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) +
          weilIntegrand (coshGaussMellinExt 0) (((-1:ℝ) : ℂ) + (y : ℂ) * I) :=
      fun y _ => h_ptwise_re _ (by norm_num)
    rw [intervalIntegral.integral_congr h_bot,
        intervalIntegral.integral_congr h_top,
        intervalIntegral.integral_congr h_right,
        intervalIntegral.integral_congr h_left]
    -- Now each integral is of a linear combination; distribute.
    -- Step 4a: prove DifferentiableAt for coshGaussMellinExt c at any s with Re s > -2, s ≠ 0.
    have h_cgm_diff : ∀ (c : ℝ) (s : ℂ), -2 < s.re → s ≠ 0 →
        DifferentiableAt ℂ (coshGaussMellinExt c) s := fun c s hre hs0 => by
      unfold coshGaussMellinExt
      -- gaussMellinClosed is differentiable: poles of Gamma(s/2) at s = -2m,
      -- but Re s > -2 forces m = 0 (i.e. s = 0), excluded by s ≠ 0.
      have h_gne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := fun m hm => by
        rcases Nat.eq_zero_or_pos m with rfl | hm_pos
        · simp only [Nat.cast_zero, neg_zero] at hm
          have : s = 0 := by field_simp at hm; simp at hm; exact hm
          exact hs0 this
        · have hre_half : (s / 2).re = -(m : ℝ) := by rw [hm]; simp
          have hdiv : (s / 2).re = s.re / 2 := by simp
          rw [hdiv] at hre_half
          linarith [show (1 : ℝ) ≤ m from by exact_mod_cast hm_pos]
      have h_pow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-(z / 2))) s :=
        (differentiableAt_id.div_const (2 : ℂ)).neg.const_cpow (Or.inl (by norm_num))
      have h_gam : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
        (Complex.differentiableAt_Gamma (s / 2) h_gne).comp s
          (differentiableAt_id.div_const (2 : ℂ))
      have h_gmc : DifferentiableAt ℂ gaussMellinClosed s := by
        unfold gaussMellinClosed
        exact ((differentiableAt_const (1 / 2 : ℂ)).mul h_pow).mul h_gam
      exact h_gmc.add (ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c hre)
    -- Step 4b: ζ ≠ 0 on bottom/top edges (Im = ±T) from goodHeight.
    have h_zeta_horiz : ∀ (x t : ℝ), (t = T ∨ t = -T) →
        riemannZeta ((x : ℂ) + (t : ℝ) * I) ≠ 0 := fun x t ht hζ => by
      have h_nt : ∀ n : ℕ, (x : ℂ) + t * I ≠ -2 * (↑n + 1) := fun n hn => by
        have := congr_arg Complex.im hn; push_cast at this; simp at this
        rcases ht with rfl | rfl <;> linarith
      obtain ⟨hlo, hhi⟩ := riemannZeta_nontrivial_zero_re_bounds hζ h_nt
      have hmem : (x : ℂ) + t * I ∈ ZD.NontrivialZeros :=
        ⟨hlo, hhi, hζ⟩
      have him : ((x : ℂ) + (t : ℝ) * I).im = t := by push_cast; simp
      rcases ht with heq | heq
      · exact (hGood.1 _ hmem).1 (him.trans heq)
      · exact (hGood.1 _ hmem).2 (him.trans heq)
    -- Step 4c: ζ ≠ 0 on left edge (Re = -1) because nontrivial zeros have Re ∈ (0,1).
    have h_zeta_left : ∀ (y : ℝ), riemannZeta ((-1 : ℂ) + y * I) ≠ 0 := fun y hζ => by
      have h_nt : ∀ n : ℕ, (-1 : ℂ) + y * I ≠ -2 * (↑n + 1) := fun n hn => by
        have := congr_arg Complex.re hn; push_cast at this; simp at this
        linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      linarith [(riemannZeta_nontrivial_zero_re_bounds hζ h_nt).1,
                show ((-1 : ℂ) + y * I).re = -1 from by push_cast; simp]
    -- Step 4d: build IntervalIntegrable for each c on each edge.
    have h_wii : ∀ (c : ℝ),
        IntervalIntegrable
          (fun x : ℝ => weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (-T : ℝ) * I))
          MeasureTheory.volume (-1 : ℝ) 2 ∧
        IntervalIntegrable
          (fun x : ℝ => weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (T : ℝ) * I))
          MeasureTheory.volume (-1 : ℝ) 2 ∧
        IntervalIntegrable
          (fun y : ℝ => weilIntegrand (coshGaussMellinExt c) (((2 : ℝ) : ℂ) + (y : ℂ) * I))
          MeasureTheory.volume (-T) T ∧
        IntervalIntegrable
          (fun y : ℝ => weilIntegrand (coshGaussMellinExt c) (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
          MeasureTheory.volume (-T) T := fun c => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- bottom edge: z = x + (-T)*I, Re z = x ∈ [-1, 2], Im z = -T ≠ 0
        apply ContinuousOn.intervalIntegrable; intro x hx
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
        have hre2 : -2 < ((x : ℂ) + (-T : ℝ) * I).re := by simp; linarith [hx.1]
        have hs0 : (x : ℂ) + (-T : ℝ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hs1 : (x : ℂ) + (-T : ℝ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hζ : riemannZeta ((x : ℂ) + (-T : ℝ) * I) ≠ 0 :=
          h_zeta_horiz x (-T) (Or.inr rfl)
        apply ContinuousAt.continuousWithinAt
        rw [ContinuousAt]
        exact (weilIntegrand_differentiableAt hs1 hζ (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp
          (Complex.continuous_ofReal.add continuous_const).continuousAt
      · -- top edge: z = x + T*I
        apply ContinuousOn.intervalIntegrable; intro x hx
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
        have hre2 : -2 < ((x : ℂ) + (T : ℝ) * I).re := by simp; linarith [hx.1]
        have hs0 : (x : ℂ) + (T : ℝ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hs1 : (x : ℂ) + (T : ℝ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hζ : riemannZeta ((x : ℂ) + (T : ℝ) * I) ≠ 0 :=
          h_zeta_horiz x T (Or.inl rfl)
        apply ContinuousAt.continuousWithinAt
        rw [ContinuousAt]
        exact (weilIntegrand_differentiableAt hs1 hζ (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp
          (Complex.continuous_ofReal.add continuous_const).continuousAt
      · -- right edge: z = 2 + y*I, Re z = 2 > 1, so ζ(z) ≠ 0
        apply ContinuousOn.intervalIntegrable; intro y _hy
        have hre2 : -2 < (((2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
        have hs0 : ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hs1 : ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hζ : riemannZeta (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 :=
          riemannZeta_ne_zero_of_one_lt_re (by simp)
        apply ContinuousAt.continuousWithinAt
        rw [ContinuousAt]
        exact (weilIntegrand_differentiableAt hs1 hζ (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      · -- left edge: z = -1 + y*I, ζ(z) ≠ 0 since nontrivial zeros have Re ∈ (0,1)
        apply ContinuousOn.intervalIntegrable; intro y _hy
        have hre2 : -2 < (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
        have hs0 : ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hs1 : ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.re h; simp at this; linarith
        have hζ_left' : riemannZeta (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
          have := h_zeta_left y
          have heq : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = ((-1 : ℂ) + (y : ℂ) * I) := by push_cast; ring
          rw [heq]; exact this
        apply ContinuousAt.continuousWithinAt
        rw [ContinuousAt]
        exact (weilIntegrand_differentiableAt hs1 hζ_left'
          (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    -- Extract the 4 × 5 = 20 integrability witnesses.
    obtain ⟨hwii_b1, hwii_t1, hwii_r1, hwii_l1⟩ := h_wii (2 * β - Real.pi / 3)
    obtain ⟨hwii_b2, hwii_t2, hwii_r2, hwii_l2⟩ := h_wii (2 - Real.pi / 3 - 2 * β)
    obtain ⟨hwii_b3, hwii_t3, hwii_r3, hwii_l3⟩ := h_wii (1 - Real.pi / 3)
    obtain ⟨hwii_b4, hwii_t4, hwii_r4, hwii_l4⟩ := h_wii (2 * β - 1)
    obtain ⟨hwii_b5, hwii_t5, hwii_r5, hwii_l5⟩ := h_wii 0
    -- Helper: split ∫(1/2*f1 + 1/2*f2 - f3 - f4 + f5) = 1/2*∫f1 + 1/2*∫f2 - ∫f3 - ∫f4 + ∫f5.
    have h_5split : ∀ (f1 f2 f3 f4 f5 : ℝ → ℂ) (a b : ℝ)
        (h1 : IntervalIntegrable f1 MeasureTheory.volume a b)
        (h2 : IntervalIntegrable f2 MeasureTheory.volume a b)
        (h3 : IntervalIntegrable f3 MeasureTheory.volume a b)
        (h4 : IntervalIntegrable f4 MeasureTheory.volume a b)
        (h5 : IntervalIntegrable f5 MeasureTheory.volume a b),
        ∫ x in a..b, ((1/2 : ℂ) * f1 x + (1/2 : ℂ) * f2 x - f3 x - f4 x + f5 x) =
        (1/2 : ℂ) * (∫ x in a..b, f1 x) + (1/2 : ℂ) * (∫ x in a..b, f2 x)
          - (∫ x in a..b, f3 x) - (∫ x in a..b, f4 x) + (∫ x in a..b, f5 x) :=
      fun f1 f2 f3 f4 f5 a b h1 h2 h3 h4 h5 => by
        have hc1 : IntervalIntegrable (fun x => (1/2 : ℂ) * f1 x) MeasureTheory.volume a b :=
          h1.const_mul (1/2 : ℂ)
        have hc2 : IntervalIntegrable (fun x => (1/2 : ℂ) * f2 x) MeasureTheory.volume a b :=
          h2.const_mul (1/2 : ℂ)
        rw [intervalIntegral.integral_add ((hc1.add hc2).sub h3 |>.sub h4) h5,
            intervalIntegral.integral_sub (hc1.add hc2 |>.sub h3) h4,
            intervalIntegral.integral_sub (hc1.add hc2) h3,
            intervalIntegral.integral_add hc1 hc2]
        have e1 : ∫ x in a..b, (1/2 : ℂ) * f1 x = (1/2 : ℂ) * ∫ x in a..b, f1 x :=
          intervalIntegral.integral_const_mul _ f1
        have e2 : ∫ x in a..b, (1/2 : ℂ) * f2 x = (1/2 : ℂ) * ∫ x in a..b, f2 x :=
          intervalIntegral.integral_const_mul _ f2
        rw [e1, e2]
    -- Apply the 5-split to all four edges.
    rw [h_5split _ _ _ _ _ _ _ hwii_b1 hwii_b2 hwii_b3 hwii_b4 hwii_b5,
        h_5split _ _ _ _ _ _ _ hwii_t1 hwii_t2 hwii_t3 hwii_t4 hwii_t5,
        h_5split _ _ _ _ _ _ _ hwii_r1 hwii_r2 hwii_r3 hwii_r4 hwii_r5,
        h_5split _ _ _ _ _ _ _ hwii_l1 hwii_l2 hwii_l3 hwii_l4 hwii_l5]
    simp only [smul_eq_mul]
    ring
  -- Step 5: Combine. LHS = h_integ_eq's RHS = (1/2)*h_c1 + ... rearranged.
  rw [h_integ_eq, h_c1, h_c2, h_c3, h_c4, h_c5, h_at1, h_sum_eq]
  ring

#print axioms rectangleResidueIdentity_from_perC

/-! ## §3 Final theorem -/

/-- **`WeilExplicitFormula_pair_cosh_gauss_target β` from the two H3-closure hypotheses.**

Given:
- `h_star  : weil_explicit_formula_cosh_pair_target β` — the `(★)` placeholder
  (`∫arch β 2 = ∫weilIntegrand(pairTestMellin β)(-1+iy)`), the authorized H3
  placeholder (`WeilExplicitFormulaPlaceholder.lean:65`).
- `h_refl_zero : archPair_eq_primePair_at_two_target β` — the parallel H3
  sorry, equivalent to `∫reflectedPrimeIntegrand β 2 = 0`.

Proof sketch (all steps axiom-clean):
1. `h_refl_zero` + `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`
   → `R := ∫reflected = 0`.
2. `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum`: `A + R = 2π·S`,
   so `A = 2π·S` (since R = 0).
3. `h_star`: `A = W`, `weilIntegrand_left_edge_integral_value`:
   `W = 2π·(S − M(1) + Sres)`.
4. `A = W` gives `2π·S = 2π·(S − M(1) + Sres)`, so `Sres = M(1)`.
5. `pairTestMellin_at_one`: `M(1) = gaussianPairDefect β`. QED. -/
theorem WeilExplicitFormula_pair_cosh_gauss_target_of_star
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (h_star : weil_explicit_formula_cosh_pair_target β)
    (h_refl_zero :
      Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β) :
    WeilExplicitFormula_pair_cosh_gauss_target β := by
  unfold WeilExplicitFormula_pair_cosh_gauss_target
  -- Step 1: ∫reflected = 0
  have h_refl_zero' :=
    (Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes
      β).mp h_refl_zero
  -- Step 2: ∫arch + ∫reflected = 2π·S  (axiom-clean)
  have h_arch_prime := archIntegrand_plus_reflectedPrime_integral_eq_prime_sum β
  -- Step 3: ∫weil(-1+iy) = 2π·(S − M(1) + Sres)  (axiom-clean)
  have h_left := weilIntegrand_left_edge_integral_value β hβ
  -- Step 5: M(1) = gaussianPairDefect β  (axiom-clean)
  have hm1 := Contour.pairTestMellin_at_one β
  set A : ℂ := ∫ y : ℝ, Contour.archIntegrand β 2 y
  set W : ℂ := ∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
      ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)
  set R : ℂ := ∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val
  -- A = 2π·S (since R = 0)
  have hA : A = 2 * (Real.pi : ℂ) * S := by
    have h := h_arch_prime; rw [h_refl_zero', add_zero] at h; exact h
  -- Sres = M(1) via A = W and cancellation
  have hSres : Sres = Contour.pairTestMellin β 1 := by
    have hAW : A = W := h_star
    rw [hA, h_left] at hAW
    have h2π_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hcancel : S = S - Contour.pairTestMellin β 1 + Sres :=
      mul_left_cancel₀ h2π_ne hAW
    linear_combination -hcancel
  rw [hSres, hm1]

#print axioms WeilExplicitFormula_pair_cosh_gauss_target_of_star

end FinalAssembly
end WeilPositivity
end ZD

end
