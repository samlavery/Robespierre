import Mathlib
import RequestProject.WeilIdentityAtPairTest
import RequestProject.WeilLeftEdgePrimeSum
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilLogDerivZetaBound

/-!
# Steps 3a + 3b: archIntegrand at σ = -1

## Step 3a — integrability

`archIntegrand β (-1) y` is integrable on ℝ. Strategy: use that the FULL
left-edge boundary integrand `hadamardArchBoundaryTerm(-1+iy)·pairTestMellin β (-1+iy)`
is integrable (Step 1e: `leftEdge_pairTestMellin_integrable`), AND that the
reflected-prime piece `(ζ'/ζ)(2-iy) · pairTestMellin β (-1+iy)` is integrable
(extractable from Step 2b's `leftEdge_reflectedPrime_eq_sum` proof). Then the
arch piece = full − reflected is integrable as the difference.

## Step 3b — closed form

`∫_ℝ archIntegrand β (-1) y dy` has a closed form via Mellin inversion at σ = -1
(reusing `pairTestMellin_inversion_at_neg_one` from Step 2b). Mirrors the
reflected-prime closed form but for the Γℝ' / Γℝ pieces instead of ζ' / ζ.

The closed form involves Mellin transforms of `Γℝ'/Γℝ(-1+iy)` and
`Γℝ'/Γℝ(2-iy)` — these are concrete Γ-derivative integrals.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ArchAtNegOne

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.PairTestIdentity
open ZD.WeilPositivity.LeftEdgePrimeSum
open ArithmeticFunction

/-! ## Step 3a — archIntegrand β (-1) integrability -/

/-- **Reflected-prime piece at σ=-1 is integrable on ℝ.** The integrand
`(ζ'/ζ)(2-iy) · pairTestMellin β (-1+iy)` is bounded by an integrable
majorant: `LSeries(Λ)` is bounded on `Re s = 2` (constant), and
`pairTestMellin β (-1+iy)` has quartic decay (extended). Product is
integrable. -/
theorem reflectedPrimeIntegrand_at_neg_one_integrable (β : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ =>
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
       riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  -- Rephrase via 1 - (-1 + y*I) = 2 - y*I = line₂ y
  set line₂ : ℝ → ℂ := fun y => (2 : ℂ) + (-y : ℂ) * I
  have h_1s_eq : ∀ y : ℝ, 1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) = line₂ y := by
    intro y; simp [line₂]; ring
  have h_rw : (fun y : ℝ =>
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
       riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
    (fun y : ℝ => (deriv riemannZeta (line₂ y) / riemannZeta (line₂ y)) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
    funext y; rw [h_1s_eq]
  rw [h_rw]
  -- Get uniform LSeries(Λ) bound on Re s ≥ 2
  obtain ⟨C_L, hC_L_nn, hL_bd⟩ :=
    LSeries_vonMangoldt_bounded_of_right_of_one 2 (by norm_num)
  -- Get quadratic decay of pairTestMellin β (-1+y*I)
  obtain ⟨K, hK_nn, hK_bd⟩ := pairTestMellin_left_edge_global_quadratic_bound β
  -- Continuity of logDeriv factor: rewrite to -LSeries(Λ)(line₂ y)
  have h_logderiv_cont :
      Continuous (fun y : ℝ => deriv riemannZeta (line₂ y) / riemannZeta (line₂ y)) := by
    set f := fun n => (vonMangoldt n : ℂ)
    have h_eq : ∀ y : ℝ, deriv riemannZeta (line₂ y) / riemannZeta (line₂ y) =
        -LSeries f (line₂ y) := fun y => by
      have hre : (1 : ℝ) < (line₂ y).re := by simp [line₂]
      rw [vonMangoldt_LSeries_eq_neg_logDeriv_zeta hre]; ring
    have h_Lser_cont : Continuous (fun y : ℝ => LSeries f (line₂ y)) := by
      have h_line_c : Continuous line₂ := by simp [line₂]; fun_prop
      apply continuous_iff_continuousAt.mpr; intro y
      have h_re : LSeries.abscissaOfAbsConv f < ↑(line₂ y).re := by
        have h1 : (line₂ y).re = 2 := by simp [line₂]
        rw [h1]
        calc LSeries.abscissaOfAbsConv f
            ≤ (1 : EReal) := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
                  (fun σ hσ => LSeriesSummable_vonMangoldt (by exact_mod_cast hσ))
          _ < (2 : ℝ) := by norm_cast
      exact ((LSeries_differentiableOn f).differentiableAt
          (isOpen_re_gt_EReal _ |>.mem_nhds h_re)).continuousAt.comp h_line_c.continuousAt
    exact h_Lser_cont.neg.congr (fun y => (h_eq y).symm)
  -- Continuity of pairTestMellin β (-1+y*I)
  have h_pair_cont : Continuous (fun y : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    pairTestMellin_left_edge_continuous β
  -- Pointwise norm bound ‖·‖ ≤ C_L · K · (1 + y²)⁻¹
  have h_bound : ∀ y : ℝ,
      ‖(deriv riemannZeta (line₂ y) / riemannZeta (line₂ y)) *
       pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C_L * K * (1 + y ^ 2)⁻¹ := by
    intro y
    rw [norm_mul]
    have hre : (1 : ℝ) < (line₂ y).re := by simp [line₂]
    have h_norm_eq : ‖deriv riemannZeta (line₂ y) / riemannZeta (line₂ y)‖ =
        ‖LSeries (fun n => (vonMangoldt n : ℂ)) (line₂ y)‖ := by
      rw [vonMangoldt_LSeries_eq_neg_logDeriv_zeta hre]; simp [norm_neg]
    rw [h_norm_eq]
    calc ‖LSeries (fun n => (vonMangoldt n : ℂ)) (line₂ y)‖ *
          ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ C_L * (K * (1 + y ^ 2)⁻¹) :=
          mul_le_mul (hL_bd _ (by simp [line₂])) (hK_bd y) (norm_nonneg _) hC_L_nn
      _ = C_L * K * (1 + y ^ 2)⁻¹ := by ring
  -- Apply dominated convergence: majorant C_L·K·(1+y²)⁻¹ is integrable
  exact (integrable_inv_one_add_sq.const_mul (C_L * K)).mono'
    (h_logderiv_cont.mul h_pair_cont).aestronglyMeasurable
    (ae_of_all _ h_bound)

/-- **Step 3a — `archIntegrand β (-1)` integrable on ℝ.** Obtained by
subtracting the reflected-prime piece from the full left-edge boundary
integrand (both proved integrable). -/
theorem archIntegrand_at_neg_one_integrable (β : ℝ) :
    MeasureTheory.Integrable (archIntegrand β (-1)) := by
  -- Full left-edge integrand integrable (Step 1e).
  have h_full := leftEdge_pairTestMellin_integrable β
  -- Reflected piece integrable (helper above).
  have h_refl := reflectedPrimeIntegrand_at_neg_one_integrable β
  -- archIntegrand β (-1) = full - reflected (pointwise via leftEdge_integrand_decomposition).
  have h_diff : ∀ y : ℝ,
      archIntegrand β (-1) y =
        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) -
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
         riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
    intro y
    have h := leftEdge_integrand_decomposition β y
    -- h : full = arch + refl; rearrange over ℂ to arch = full - refl
    linear_combination -h
  refine (h_full.sub h_refl).congr ?_
  exact Filter.Eventually.of_forall (fun y => (h_diff y).symm)

/-! ## Step 3b — DEFERRED

A direct closed form for `∫_ℝ archIntegrand β (-1) y dy` was investigated.
Conclusions:

* The arch integrand uses `Γℝ'/Γℝ` (digamma), which lacks a Dirichlet-series
  expansion (no LSeries form like `ζ'/ζ`). So the per-prime closed form via
  Mellin inversion (analogous to `leftEdge_reflectedPrime_eq_sum`) does not
  yield a clean prime-side sum.
* Recovering `∫arch β (-1)` via the Step 1f whole-line identity circles back
  to Step 3c (tautological).
* The natural FE-relation `∫arch β (-1) = ∫arch β 2` does NOT hold —
  `pair_cosh_gauss_test β` is not FE-symmetric in `t`.

The architecture proceeds without an explicit Step 3b: Step 3c supplies the
unconditional closed form for `Σ'(β)` with `∫arch β (-1)` as a named
integral. -/
example : True := trivial

end ArchAtNegOne
end WeilPositivity
end ZD

end
