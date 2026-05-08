import Mathlib
import RequestProject.CauchyKPairTestLimit
import RequestProject.CauchyWeilDefectScratch
import RequestProject.OfflineDetectorProof
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilLeftEdgePointwiseSplit
import RequestProject.WeilArchAtNegOne
import RequestProject.ArchOperatorBound

/-!
# Discharge: vertical-edge integrability for `gaussianDefectEntireKernel_local · w(M)`

Discharges
`K_pairTestMellin_vertical_at_two_integrable gaussianDefectEntireKernel_local β`
unconditionally for every real `β`.

Strategy: `K(2+iy)` is bounded uniformly in `y` (Gaussian decay of the two
exponential summands plus the bounded `+1` term), and
`primeIntegrand β 2 y = weilIntegrand(pairTestMellin β)(2+iy)` is integrable
on `ℝ` via `WeilPairIBP.primeIntegrand_integrable`. Apply
`MeasureTheory.Integrable.bdd_mul`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

/-- **Uniform bound on `K = gaussianDefectEntireKernel_local` on the line `Re s = 2`.** -/
private lemma gaussianDefectEntireKernel_bounded_on_re_two :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  set Cprefac : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hCprefac_def
  have hCprefac_nn : 0 ≤ Cprefac := by
    rw [hCprefac_def]
    exact mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  refine ⟨Cprefac * (Real.exp (9/8) + 2 * Real.exp (9/32) + 1), fun y => ?_⟩
  unfold gaussianDefectEntireKernel_local
  rw [norm_mul]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg hCprefac_nn]
  apply mul_le_mul_of_nonneg_left _ hCprefac_nn
  -- Bound ‖exp((s-1/2)²/2) - 2·exp((s-1/2)²/8) + 1‖.
  set s : ℂ := ((2 : ℝ) : ℂ) + (y : ℂ) * I with hs_def
  have h_sub_sq : (s - (1/2 : ℂ))^2 = ((9/4 - y^2 : ℝ) : ℂ) + ((3 * y : ℝ) : ℂ) * I := by
    rw [hs_def]
    have hyc : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = -((y^2 : ℝ) : ℂ) := by
      have : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ)^2 * Complex.I^2 := by ring
      rw [this, Complex.I_sq]; push_cast; ring
    have : ((2 : ℝ) : ℂ) + (y : ℂ) * I - (1/2 : ℂ) = (3/2 : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [this, sq]
    rw [show ((3/2 : ℂ) + (y : ℂ) * I) * ((3/2 : ℂ) + (y : ℂ) * I) =
        (9/4 : ℂ) + (3 * y : ℂ) * I + (y : ℂ) * I * ((y : ℂ) * I) by ring]
    rw [hyc]; push_cast; ring
  have h_sub_sq_re : ((s - (1/2 : ℂ))^2).re = 9/4 - y^2 := by
    rw [h_sub_sq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  -- ‖exp((s-1/2)²/2)‖ = exp((9/4 - y²)/2) ≤ exp(9/8).
  have h_exp2_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ ≤ Real.exp (9/8) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h_re : ((s - (1/2 : ℂ))^2 / 2).re = (9/4 - y^2) / 2 := by
      rw [show ((s - (1/2 : ℂ))^2 / 2) = ((s - (1/2 : ℂ))^2) * (1/2 : ℂ) by ring]
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, h_sub_sq_re]
      have him : ((s - (1/2 : ℂ))^2).im = 3 * y := by
        rw [h_sub_sq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      linarith [him]
    rw [h_re]
    have hy_sq_nn : (0 : ℝ) ≤ y^2 := sq_nonneg y
    linarith
  have h_exp8_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ ≤ Real.exp (9/32) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h_re : ((s - (1/2 : ℂ))^2 / 8).re = (9/4 - y^2) / 8 := by
      rw [show ((s - (1/2 : ℂ))^2 / 8) = ((s - (1/2 : ℂ))^2) * (1/8 : ℂ) by ring]
      rw [show (1/8 : ℂ) = ((1/8 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, h_sub_sq_re]
      have him : ((s - (1/2 : ℂ))^2).im = 3 * y := by
        rw [h_sub_sq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      linarith [him]
    rw [h_re]
    have hy_sq_nn : (0 : ℝ) ≤ y^2 := sq_nonneg y
    linarith
  -- Triangle inequality.
  calc ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
        2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8) + 1‖
      ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ +
          ‖2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp (9/8) +
          (2 * Real.exp (9/32)) + 1 := by
        rw [show (1 : ℝ) = ‖(1 : ℂ)‖ from by simp]
        gcongr
        rw [norm_mul]
        simp only [Complex.norm_ofNat]
        gcongr

/-- **Discharge of `K_pairTestMellin_vertical_at_two_integrable`** for
`K = gaussianDefectEntireKernel_local`. -/
theorem K_pairTestMellin_vertical_at_two_integrable_holds (β : ℝ) :
    K_pairTestMellin_vertical_at_two_integrable
      gaussianDefectEntireKernel_local β := by
  unfold K_pairTestMellin_vertical_at_two_integrable
  -- Translate to primeIntegrand form via weilIntegrand_eq_primeIntegrand_on_right_edge.
  have h_eq : (fun y : ℝ => gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun y : ℝ => gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.primeIntegrand β 2 y) := by
    funext y
    rw [Contour.weilIntegrand_eq_primeIntegrand_on_right_edge β
      (show (1:ℝ) < 2 by norm_num) y]
  rw [h_eq]
  -- Apply Integrable.bdd_mul: K is bounded, primeIntegrand β 2 is integrable.
  obtain ⟨C, hCbd⟩ := gaussianDefectEntireKernel_bounded_on_re_two
  have hPI : Integrable (Contour.primeIntegrand β 2) :=
    Contour.primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)
  have h_K_meas : AEStronglyMeasurable
      (fun y : ℝ => gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume := by
    have hK_diff : Differentiable ℂ gaussianDefectEntireKernel_local := by
      unfold gaussianDefectEntireKernel_local
      have h1 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 2)) :=
        (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
      have h2 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 8)) :=
        (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
      exact (differentiable_const _).mul (((h1.sub ((differentiable_const _).mul h2)).add
        (differentiable_const _)))
    have hpath : Continuous (fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact (hK_diff.continuous.comp hpath).aestronglyMeasurable
  exact hPI.bdd_mul h_K_meas (Filter.Eventually.of_forall hCbd)

/-! ## Discharge of vertical-edge integrability at `Re = -1` -/

/-- **Uniform bound on `K = gaussianDefectEntireKernel_local` on the line `Re s = -1`.** -/
private lemma gaussianDefectEntireKernel_bounded_on_re_neg_one :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  set Cprefac : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hCprefac_def
  have hCprefac_nn : 0 ≤ Cprefac := by
    rw [hCprefac_def]
    exact mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  -- At s = -1+iy: (s-1/2) = -3/2+iy, (s-1/2)² = 9/4 - y² - 3iy.
  -- Same modulus bounds as on Re = 2.
  refine ⟨Cprefac * (Real.exp (9/8) + 2 * Real.exp (9/32) + 1), fun y => ?_⟩
  unfold gaussianDefectEntireKernel_local
  rw [norm_mul]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg hCprefac_nn]
  apply mul_le_mul_of_nonneg_left _ hCprefac_nn
  set s : ℂ := ((-1 : ℝ) : ℂ) + (y : ℂ) * I with hs_def
  have h_sub_sq : (s - (1/2 : ℂ))^2 = ((9/4 - y^2 : ℝ) : ℂ) + ((-3 * y : ℝ) : ℂ) * I := by
    rw [hs_def]
    have hyc : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = -((y^2 : ℝ) : ℂ) := by
      have : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ)^2 * Complex.I^2 := by ring
      rw [this, Complex.I_sq]; push_cast; ring
    have : ((-1 : ℝ) : ℂ) + (y : ℂ) * I - (1/2 : ℂ) = (-3/2 : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [this, sq]
    rw [show ((-3/2 : ℂ) + (y : ℂ) * I) * ((-3/2 : ℂ) + (y : ℂ) * I) =
        (9/4 : ℂ) + (-3 * y : ℂ) * I + (y : ℂ) * I * ((y : ℂ) * I) by ring]
    rw [hyc]; push_cast; ring
  have h_sub_sq_re : ((s - (1/2 : ℂ))^2).re = 9/4 - y^2 := by
    rw [h_sub_sq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have h_exp2_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ ≤ Real.exp (9/8) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h_re : ((s - (1/2 : ℂ))^2 / 2).re = (9/4 - y^2) / 2 := by
      rw [show ((s - (1/2 : ℂ))^2 / 2) = ((s - (1/2 : ℂ))^2) * (1/2 : ℂ) by ring]
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.mul_re]
      simp
      have him : ((s - (1/2 : ℂ))^2).im = -3 * y := by
        rw [h_sub_sq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      linarith [him, h_sub_sq_re]
    rw [h_re]
    have hy_sq_nn : (0 : ℝ) ≤ y^2 := sq_nonneg y
    linarith
  have h_exp8_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ ≤ Real.exp (9/32) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h_re : ((s - (1/2 : ℂ))^2 / 8).re = (9/4 - y^2) / 8 := by
      rw [show ((s - (1/2 : ℂ))^2 / 8) = ((s - (1/2 : ℂ))^2) * (1/8 : ℂ) by ring]
      rw [show (1/8 : ℂ) = ((1/8 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.mul_re]
      simp
      have him : ((s - (1/2 : ℂ))^2).im = -3 * y := by
        rw [h_sub_sq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      linarith [him, h_sub_sq_re]
    rw [h_re]
    have hy_sq_nn : (0 : ℝ) ≤ y^2 := sq_nonneg y
    linarith
  calc ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
        2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8) + 1‖
      ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ +
          ‖2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp (9/8) +
          (2 * Real.exp (9/32)) + 1 := by
        rw [show (1 : ℝ) = ‖(1 : ℂ)‖ from by simp]
        gcongr
        rw [norm_mul]
        simp only [Complex.norm_ofNat]
        gcongr

/-- **Discharge of `K_pairTestMellin_vertical_at_neg_one_integrable`** for
`K = gaussianDefectEntireKernel_local`. -/
theorem K_pairTestMellin_vertical_at_neg_one_integrable_holds (β : ℝ) :
    K_pairTestMellin_vertical_at_neg_one_integrable
      gaussianDefectEntireKernel_local β := by
  unfold K_pairTestMellin_vertical_at_neg_one_integrable
  -- weilIntegrand(M)(-1+iy) = archIntegrand(-1, y) + reflectedPrimeIntegrand(-1, y).
  have h_wI_eq : (fun y : ℝ =>
        Contour.weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun y : ℝ => Contour.archIntegrand β (-1) y + Contour.reflectedPrimeIntegrand β (-1) y) := by
    funext y
    exact ZD.WeilPositivity.FinalAssembly.weilIntegrand_pair_left_edge_neg_one_split β y
  -- Sum is integrable.
  have h_arch_int : Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_refl_int : Integrable (Contour.reflectedPrimeIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.reflectedPrimeIntegrand_at_neg_one_integrable β
  have h_wI_int : Integrable (fun y : ℝ =>
      Contour.weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    rw [h_wI_eq]
    exact h_arch_int.add h_refl_int
  -- Apply Integrable.bdd_mul.
  obtain ⟨C, hCbd⟩ := gaussianDefectEntireKernel_bounded_on_re_neg_one
  have h_K_meas : AEStronglyMeasurable
      (fun y : ℝ => gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume := by
    have hK_diff : Differentiable ℂ gaussianDefectEntireKernel_local := by
      unfold gaussianDefectEntireKernel_local
      have h1 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 2)) :=
        (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
      have h2 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 8)) :=
        (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
      exact (differentiable_const _).mul (((h1.sub ((differentiable_const _).mul h2)).add
        (differentiable_const _)))
    have hpath : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact (hK_diff.continuous.comp hpath).aestronglyMeasurable
  exact h_wI_int.bdd_mul h_K_meas (Filter.Eventually.of_forall hCbd)

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_pairTestMellin_vertical_at_two_integrable_holds
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_pairTestMellin_vertical_at_neg_one_integrable_holds
