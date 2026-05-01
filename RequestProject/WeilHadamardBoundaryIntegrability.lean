import Mathlib
import RequestProject.ArchOperatorBound
import RequestProject.WeilHadamardBoundaryDecomposition
import RequestProject.WeilHadamardKernel
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilPairIBP

/-!
# Vertical-line integrability for the Hadamard kernel

This file isolates the easy analytic half of the Hadamard boundary-limit
argument: on the fixed vertical edges `Re z = 2` and `Re z = -1`, the kernel
`K_s(z) = 1 / (s - z) + 1 / z` has global quadratic decay in the imaginary
direction. Combined with the existing uniform right-half-plane bound on
`-ζ'/ζ = LSeries Λ`, this gives unconditional integrability of the right-edge
Hadamard boundary term.
-/

open Complex Set Filter ArithmeticFunction

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

private lemma vertical_line_continuous (σ : ℝ) :
    Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

private lemma two_plus_tI_ne_zero (t : ℝ) : ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have hre : (((2 : ℂ) + (t : ℂ) * I)).re = (0 : ℂ).re := by simpa [h]
  norm_num at hre

private lemma neg_one_plus_tI_ne_zero (t : ℝ) : (((-1 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have hre : (((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)).re = (0 : ℂ).re := by simpa using congrArg Complex.re h
  norm_num at hre

private lemma two_plus_tI_ne_s {s : ℂ} (hs_re : s.re < 1) (t : ℝ) :
    ((2 : ℂ) + (t : ℂ) * I) ≠ s := by
  intro h
  have hre : (((2 : ℂ) + (t : ℂ) * I)).re = s.re := by simpa using congrArg Complex.re h
  simp at hre
  linarith

private lemma neg_one_plus_tI_ne_s {s : ℂ} (hs_re : -1 < s.re) (t : ℝ) :
    (((-1 : ℝ) : ℂ) + (t : ℂ) * I) ≠ s := by
  intro h
  have hre : (((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)).re = s.re := by
    simpa using congrArg Complex.re h
  simp at hre
  linarith

private theorem hadamardKernel_right_edge_continuous {s : ℂ} (hs_re : s.re < 1) :
    Continuous (fun t : ℝ => hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)) := by
  unfold hadamardKernel
  have hline : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) := vertical_line_continuous 2
  have hleft : Continuous (fun t : ℝ => 1 / (s - ((2 : ℂ) + (t : ℂ) * I))) := by
    simpa [one_div] using
      (continuous_const.sub hline).inv₀ (fun t => sub_ne_zero.mpr (two_plus_tI_ne_s hs_re t).symm)
  have hright : Continuous (fun t : ℝ => 1 / (((2 : ℂ) + (t : ℂ) * I))) := by
    simpa [one_div] using hline.inv₀ two_plus_tI_ne_zero
  exact hleft.add hright

private theorem hadamardKernel_left_edge_continuous {s : ℂ} (hs_re : -1 < s.re) :
    Continuous (fun t : ℝ => hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)) := by
  unfold hadamardKernel
  have hline : Continuous (fun t : ℝ => (((-1 : ℝ) : ℂ)) + (t : ℂ) * I) :=
    vertical_line_continuous (-1)
  have hleft :
      Continuous (fun t : ℝ => 1 / (s - ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I))) := by
    simpa [one_div] using
      (continuous_const.sub hline).inv₀ (fun t =>
        sub_ne_zero.mpr (neg_one_plus_tI_ne_s hs_re t).symm)
  have hright : Continuous (fun t : ℝ => 1 / ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)) := by
    simpa [one_div] using hline.inv₀ neg_one_plus_tI_ne_zero
  exact hleft.add hright

private theorem hadamardKernel_right_edge_tail_bound {s : ℂ} (hs_re : s.re < 1)
    {t : ℝ} (hlarge : 2 * ‖s‖ ≤ |t|) :
    ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hz : z ≠ 0 := two_plus_tI_ne_zero t
  have hsz : s ≠ z := (two_plus_tI_ne_s hs_re t).symm
  have hlarge_z : 2 * ‖s‖ ≤ ‖z‖ := by
    calc
      2 * ‖s‖ ≤ |t| := hlarge
      _ ≤ ‖z‖ := by
        simpa [z] using (Complex.abs_im_le_norm z)
  have hbase :
      ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ / ‖z‖ ^ 2 := by
    simpa [z] using
      (ZD.WeilPositivity.Contour.hadamardKernel_norm_le_two_mul_norm_div_sq hz hsz hlarge_z)
  have hz_sq_ge : 1 + t ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply]
    nlinarith
  calc
    ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ / ‖z‖ ^ 2 := hbase
    _ ≤ 2 * ‖s‖ / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * ‖s‖)
      positivity
      exact hz_sq_ge
    _ = 2 * ‖s‖ * (1 + t ^ 2)⁻¹ := by ring

private theorem hadamardKernel_left_edge_tail_bound {s : ℂ} (hs_re : -1 < s.re)
    {t : ℝ} (hlarge : 2 * ‖s‖ ≤ |t|) :
    ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤
      2 * ‖s‖ * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (((-1 : ℝ) : ℂ)) + (t : ℂ) * I
  have hz : z ≠ 0 := neg_one_plus_tI_ne_zero t
  have hsz : s ≠ z := (neg_one_plus_tI_ne_s hs_re t).symm
  have hlarge_z : 2 * ‖s‖ ≤ ‖z‖ := by
    calc
      2 * ‖s‖ ≤ |t| := hlarge
      _ ≤ ‖z‖ := by
        simpa [z] using (Complex.abs_im_le_norm z)
  have hbase :
      ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ / ‖z‖ ^ 2 := by
    simpa [z] using
      (ZD.WeilPositivity.Contour.hadamardKernel_norm_le_two_mul_norm_div_sq hz hsz hlarge_z)
  have hz_sq_eq : ‖z‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply]
    ring
  calc
    ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ / ‖z‖ ^ 2 := hbase
    _ = 2 * ‖s‖ / (1 + t ^ 2) := by rw [hz_sq_eq]
    _ = 2 * ‖s‖ * (1 + t ^ 2)⁻¹ := by ring

/-- Along `Re z = 2`, the Hadamard kernel has a global quadratic majorant. -/
theorem hadamardKernel_right_edge_global_quadratic_bound {s : ℂ} (hs_re : s.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ K * (1 + t ^ 2)⁻¹ := by
  let f : ℝ → ℝ := fun t => (1 + t ^ 2) * ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖
  let R : ℝ := max (2 * ‖s‖) 1
  have h_cont : Continuous f := by
    unfold f
    exact (continuous_const.add (continuous_id.pow 2)).mul
      (hadamardKernel_right_edge_continuous hs_re).norm
  have h_compact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have h_bdd : BddAbove (f '' Set.Icc (-R) R) := h_compact.bddAbove_image h_cont.continuousOn
  let M : ℝ := sSup (f '' Set.Icc (-R) R)
  have hM_nn : 0 ≤ M := by
    have hR_nn : 0 ≤ R := by
      exact le_trans (by positivity : (0 : ℝ) ≤ 1) (le_max_right _ _)
    have h0_mem : (0 : ℝ) ∈ Set.Icc (-R) R := by
      exact ⟨by linarith, hR_nn⟩
    have h0_le : f 0 ≤ M := le_csSup h_bdd (Set.mem_image_of_mem _ h0_mem)
    have hf0_nn : 0 ≤ f 0 := by
      unfold f
      positivity
    linarith
  refine ⟨max M (2 * ‖s‖), le_trans hM_nn (le_max_left _ _), fun t => ?_⟩
  by_cases ht : |t| ≤ R
  · have ht_mem : t ∈ Set.Icc (-R) R := by
      exact ⟨by linarith [abs_le.mp ht |>.1], by linarith [abs_le.mp ht |>.2]⟩
    have hMt : f t ≤ M := le_csSup h_bdd (Set.mem_image_of_mem _ ht_mem)
    have h_one_t_pos : 0 < 1 + t ^ 2 := by positivity
    have h_local :
        ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      rw [show M * (1 + t ^ 2)⁻¹ = M / (1 + t ^ 2) by ring]
      refine (le_div_iff₀ h_one_t_pos).2 ?_
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using hMt
    have h_inv_nn : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    calc
      ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ M * (1 + t ^ 2)⁻¹ := h_local
      _ ≤ max M (2 * ‖s‖) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h_inv_nn
  · have ht' : R < |t| := lt_of_not_ge ht
    have hlarge : 2 * ‖s‖ ≤ |t| := le_trans (le_max_left _ _) (le_of_lt ht')
    have h_tail := hadamardKernel_right_edge_tail_bound hs_re hlarge
    have h_inv_nn : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    calc
      ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ * (1 + t ^ 2)⁻¹ := h_tail
      _ ≤ max M (2 * ‖s‖) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) h_inv_nn

/-- Along `Re z = -1`, the Hadamard kernel has a global quadratic majorant. -/
theorem hadamardKernel_left_edge_global_quadratic_bound {s : ℂ} (hs_re : -1 < s.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ K * (1 + t ^ 2)⁻¹ := by
  let f : ℝ → ℝ := fun t =>
    (1 + t ^ 2) * ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖
  let R : ℝ := max (2 * ‖s‖) 1
  have h_cont : Continuous f := by
    unfold f
    exact (continuous_const.add (continuous_id.pow 2)).mul
      (hadamardKernel_left_edge_continuous hs_re).norm
  have h_compact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have h_bdd : BddAbove (f '' Set.Icc (-R) R) := h_compact.bddAbove_image h_cont.continuousOn
  let M : ℝ := sSup (f '' Set.Icc (-R) R)
  have hM_nn : 0 ≤ M := by
    have hR_nn : 0 ≤ R := by
      exact le_trans (by positivity : (0 : ℝ) ≤ 1) (le_max_right _ _)
    have h0_mem : (0 : ℝ) ∈ Set.Icc (-R) R := by
      exact ⟨by linarith, hR_nn⟩
    have h0_le : f 0 ≤ M := le_csSup h_bdd (Set.mem_image_of_mem _ h0_mem)
    have hf0_nn : 0 ≤ f 0 := by
      unfold f
      positivity
    linarith
  refine ⟨max M (2 * ‖s‖), le_trans hM_nn (le_max_left _ _), fun t => ?_⟩
  by_cases ht : |t| ≤ R
  · have ht_mem : t ∈ Set.Icc (-R) R := by
      exact ⟨by linarith [abs_le.mp ht |>.1], by linarith [abs_le.mp ht |>.2]⟩
    have hMt : f t ≤ M := le_csSup h_bdd (Set.mem_image_of_mem _ ht_mem)
    have h_one_t_pos : 0 < 1 + t ^ 2 := by positivity
    have h_local :
        ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      rw [show M * (1 + t ^ 2)⁻¹ = M / (1 + t ^ 2) by ring]
      refine (le_div_iff₀ h_one_t_pos).2 ?_
      simpa [f, mul_assoc, mul_left_comm, mul_comm] using hMt
    have h_inv_nn : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    calc
      ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ M * (1 + t ^ 2)⁻¹ := h_local
      _ ≤ max M (2 * ‖s‖) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h_inv_nn
  · have ht' : R < |t| := lt_of_not_ge ht
    have hlarge : 2 * ‖s‖ ≤ |t| := le_trans (le_max_left _ _) (le_of_lt ht')
    have h_tail := hadamardKernel_left_edge_tail_bound hs_re hlarge
    have h_inv_nn : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    calc
      ‖hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I)‖ ≤ 2 * ‖s‖ * (1 + t ^ 2)⁻¹ :=
        h_tail
      _ ≤ max M (2 * ‖s‖) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) h_inv_nn

/-- The right-edge Hadamard boundary term is integrable on `ℝ`. -/
theorem hadamardKernel_right_edge_integrable {s : ℂ} (hs_re : s.re < 1) :
    MeasureTheory.Integrable (fun t : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I) *
        hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C_L, hC_L_nn, h_L_bd⟩ := LSeries_vonMangoldt_bounded_of_right_of_one 2 (by norm_num)
  obtain ⟨K, hK_nn, hK_bd⟩ := hadamardKernel_right_edge_global_quadratic_bound hs_re
  have h_cont :
      Continuous (fun t : ℝ =>
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I) *
          hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)) := by
    exact (LSeries_vonMangoldt_continuous_along_vertical 2 (by norm_num)).mul
      (hadamardKernel_right_edge_continuous hs_re)
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul (C_L * K))
    h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have hL : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I)‖
      ≤ C_L := by
    have h_re : (2 : ℝ) ≤ (((2 : ℂ) + (t : ℂ) * I)).re := by simp
    exact h_L_bd _ h_re
  have hK_t := hK_bd t
  have h_rhs_nn : 0 ≤ C_L * K * (1 + t ^ 2)⁻¹ := by positivity
  rw [Real.norm_of_nonneg h_rhs_nn, norm_mul]
  calc
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I)‖ *
        ‖hadamardKernel s ((2 : ℂ) + (t : ℂ) * I)‖
      ≤ C_L * (K * (1 + t ^ 2)⁻¹) := by
        exact mul_le_mul hL hK_t (norm_nonneg _) hC_L_nn
    _ = C_L * K * (1 + t ^ 2)⁻¹ := by ring

private def hadamardLeftLine (t : ℝ) : ℂ :=
  (((-1 : ℝ) : ℂ)) + (t : ℂ) * I

private def hadamardReflectedRightLine (t : ℝ) : ℂ :=
  (2 : ℂ) + (((-t : ℝ) : ℂ)) * I

private def hadamardArchPairReflected (t : ℝ) : ℂ :=
  deriv Complex.Gammaℝ (hadamardReflectedRightLine t) / (hadamardReflectedRightLine t).Gammaℝ +
    deriv Complex.Gammaℝ (1 - hadamardReflectedRightLine t) /
      (1 - hadamardReflectedRightLine t).Gammaℝ

private lemma gammaR_ne_zero_neg_one_line (t : ℝ) :
    (hadamardLeftLine t).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : (hadamardLeftLine t).re = (-(2 * (n : ℂ))).re := by rw [hn]
  simp [hadamardLeftLine] at hre
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
  omega

private lemma gammaR_ne_zero_reflected_right_line (t : ℝ) :
    (hadamardReflectedRightLine t).Gammaℝ ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp [hadamardReflectedRightLine]

private lemma gammaR_ne_zero_reflected_right_line_reflect (t : ℝ) :
    (1 - hadamardReflectedRightLine t).Gammaℝ ≠ 0 := by
  have hEq : 1 - hadamardReflectedRightLine t = hadamardLeftLine t := by
    simp [hadamardLeftLine, hadamardReflectedRightLine]
    ring
  rw [hEq]
  exact gammaR_ne_zero_neg_one_line t

private lemma hadamardReflectedRightLine_continuous :
    Continuous hadamardReflectedRightLine := by
  exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_neg).mul continuous_const)

private lemma gammaR_ne_zero_isOpen : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun z : ℂ => z.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} = (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {z : ℂ | z ≠ 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine ⟨inv_ne_zero, fun hz hz0 => ?_⟩
    exact hz (by simpa [hz0])
  rw [h_eq]
  exact IsOpen.preimage h_cont isOpen_ne

private lemma gammaR_analyticOnNhd :
    AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
  · exact gammaR_ne_zero_isOpen

private lemma deriv_gammaR_analyticOnNhd :
    AnalyticOnNhd ℂ (deriv Complex.Gammaℝ) {z : ℂ | z.Gammaℝ ≠ 0} :=
  gammaR_analyticOnNhd.deriv

private lemma gammaR_continuousOn :
    ContinuousOn Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} :=
  gammaR_analyticOnNhd.continuousOn

private lemma deriv_gammaR_continuousOn :
    ContinuousOn (deriv Complex.Gammaℝ) {z : ℂ | z.Gammaℝ ≠ 0} :=
  deriv_gammaR_analyticOnNhd.continuousOn

private lemma hadamardArchPairReflected_continuous :
    Continuous hadamardArchPairReflected := by
  have h_line : Continuous hadamardReflectedRightLine := hadamardReflectedRightLine_continuous
  have h_refl : Continuous (fun t : ℝ => 1 - hadamardReflectedRightLine t) :=
    continuous_const.sub h_line
  have hGamma_line : Continuous (fun t : ℝ => (hadamardReflectedRightLine t).Gammaℝ) :=
    gammaR_continuousOn.comp_continuous h_line gammaR_ne_zero_reflected_right_line
  have hGamma_refl : Continuous (fun t : ℝ => (1 - hadamardReflectedRightLine t).Gammaℝ) :=
    gammaR_continuousOn.comp_continuous h_refl gammaR_ne_zero_reflected_right_line_reflect
  have hDeriv_line : Continuous (fun t : ℝ => deriv Complex.Gammaℝ (hadamardReflectedRightLine t)) :=
    deriv_gammaR_continuousOn.comp_continuous h_line gammaR_ne_zero_reflected_right_line
  have hDeriv_refl :
      Continuous (fun t : ℝ => deriv Complex.Gammaℝ (1 - hadamardReflectedRightLine t)) :=
    deriv_gammaR_continuousOn.comp_continuous h_refl gammaR_ne_zero_reflected_right_line_reflect
  exact
    (hDeriv_line.div hGamma_line gammaR_ne_zero_reflected_right_line).add
      (hDeriv_refl.div hGamma_refl gammaR_ne_zero_reflected_right_line_reflect)

private lemma hadamardReflectedRightLine_LSeries_continuous :
    Continuous (fun t : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t)) := by
  let f : ℝ → ℂ := fun u =>
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (u : ℂ) * I)
  have hf : Continuous f := LSeries_vonMangoldt_continuous_along_vertical 2 (by norm_num)
  have hEq : (fun t : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t)) =
      f ∘ fun t : ℝ => -t := by
    funext t
    simp [f, hadamardReflectedRightLine]
  rw [hEq]
  exact hf.comp continuous_neg

private lemma hadamardArchBoundaryTerm_left_line_eq (t : ℝ) :
    hadamardArchBoundaryTerm (hadamardLeftLine t) =
      hadamardArchPairReflected t -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t) :=
    by
  have h_re : 1 < (hadamardReflectedRightLine t).re := by
    simp [hadamardReflectedRightLine]
  have hL :
      deriv riemannZeta (hadamardReflectedRightLine t) / riemannZeta (hadamardReflectedRightLine t) =
        -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t) :=
    by
      have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h_re
      have hneg :
          -(deriv riemannZeta (hadamardReflectedRightLine t) /
              riemannZeta (hadamardReflectedRightLine t)) =
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t) := by
        simpa [neg_div] using h.symm
      calc
        deriv riemannZeta (hadamardReflectedRightLine t) / riemannZeta (hadamardReflectedRightLine t) =
            -(-(deriv riemannZeta (hadamardReflectedRightLine t) /
                riemannZeta (hadamardReflectedRightLine t))) := by simp
        _ = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t) := by
            rw [hneg]
  have hleft_eq : hadamardLeftLine t = 1 - hadamardReflectedRightLine t := by
    simp [hadamardLeftLine, hadamardReflectedRightLine]
    ring
  rw [show hadamardLeftLine t = 1 - hadamardReflectedRightLine t from hleft_eq]
  simpa [hadamardArchBoundaryTerm, hadamardArchPairReflected, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc, hL]

/-- **Key comparison**: `(1 + |t|)^2 ≤ 2 * (1 + t^2)` on `ℝ`. -/
private lemma one_plus_abs_sq_le (t : ℝ) : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
  have h_t_sq : |t|^2 = t^2 := sq_abs t
  have h_twoabs : 2 * |t| ≤ 1 + |t|^2 := by
    nlinarith [sq_nonneg (|t| - 1)]
  nlinarith [h_t_sq, h_twoabs]

/-- **Majorant comparison**:
`(1 + |t|)^N / (1 + t^2) ≤ 2^(N / 2) * (1 + t^2)^((N - 2) / 2)` for `N ≥ 0`. -/
private lemma pow_div_le_rpow (t : ℝ) {N : ℝ} (hN_nn : 0 ≤ N) :
    (1 + |t|)^N / (1 + t^2) ≤ 2^(N / 2) * (1 + t^2)^((N - 2) / 2) := by
  have h_base_nn : (0 : ℝ) ≤ 1 + |t| := by positivity
  have h_t_sq_nn : (0 : ℝ) ≤ 1 + t^2 := by positivity
  have h_t_sq_pos : (0 : ℝ) < 1 + t^2 := by positivity
  have h_pow_bd : (1 + |t|)^N ≤ 2^(N / 2) * (1 + t^2)^(N / 2) := by
    have h_sq_le : (1 + |t|)^2 ≤ 2 * (1 + t^2) := one_plus_abs_sq_le t
    have hN_half_nn : (0 : ℝ) ≤ N / 2 := by linarith
    have h_lhs_eq : ((1 + |t|)^2)^(N / 2) = (1 + |t|)^N := by
      rw [show ((1 + |t|)^2 : ℝ) = (1 + |t|)^(2 : ℕ) from rfl]
      rw [← Real.rpow_natCast (1 + |t|) 2]
      rw [← Real.rpow_mul h_base_nn]
      congr 1
      push_cast
      ring
    have h_rhs_eq : (2 * (1 + t^2))^(N / 2) = 2^(N / 2) * (1 + t^2)^(N / 2) :=
      Real.mul_rpow (by norm_num) h_t_sq_nn
    rw [← h_lhs_eq, ← h_rhs_eq]
    exact Real.rpow_le_rpow (by positivity) h_sq_le hN_half_nn
  have h_split :
      2^(N / 2) * (1 + t^2)^(N / 2) / (1 + t^2) =
        2^(N / 2) * (1 + t^2)^((N - 2) / 2) := by
    rw [mul_div_assoc]
    congr 1
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (1 + t^2), ← Real.rpow_add h_t_sq_pos]
    congr 1
    ring
  calc
    (1 + |t|)^N / (1 + t^2) ≤ 2^(N / 2) * (1 + t^2)^(N / 2) / (1 + t^2) := by
      exact div_le_div_of_nonneg_right h_pow_bd h_t_sq_nn
    _ = 2^(N / 2) * (1 + t^2)^((N - 2) / 2) := h_split

/-- The left-edge Hadamard boundary term is integrable on `ℝ`. -/
theorem hadamardKernel_left_edge_archBoundary_integrable {s : ℂ} (hs_re : -1 < s.re) :
    MeasureTheory.Integrable (fun t : ℝ =>
      hadamardArchBoundaryTerm (hadamardLeftLine t) * hadamardKernel s (hadamardLeftLine t)) := by
  obtain ⟨C_A, N, hC_A_nn, hN_nn, hN_lt_1, hA_bd⟩ := arch_subunit_bound_at_two
  obtain ⟨C_L, hC_L_nn, hL_bd⟩ := LSeries_vonMangoldt_bounded_of_right_of_one 2 (by norm_num)
  obtain ⟨K, hK_nn, hK_bd⟩ := hadamardKernel_left_edge_global_quadratic_bound hs_re
  let g : ℝ → ℂ := fun t =>
    (hadamardArchPairReflected t -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t)) *
      hadamardKernel s (hadamardLeftLine t)
  have h_cont : Continuous g := by
    unfold g
    exact (hadamardArchPairReflected_continuous.sub hadamardReflectedRightLine_LSeries_continuous).mul
      (hadamardKernel_left_edge_continuous hs_re)
  let α : ℝ := (N - 2) / 2
  have h_r_gt_one : (1 : ℝ) < 2 - N := by linarith
  have h_rpow_integrable :
      MeasureTheory.Integrable
        (fun t : ℝ => (1 + ‖t‖^2)^(-(2 - N) / 2)) MeasureTheory.volume := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [Module.finrank_self]
    exact_mod_cast h_r_gt_one
  have h_rpow_integrable' :
      MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)^α) := by
    refine h_rpow_integrable.congr (MeasureTheory.ae_of_all _ ?_)
    intro t
    change (1 + ‖t‖ ^ 2) ^ (-(2 - N) / 2) = (1 + t^2)^α
    have h_norm_sq : ‖t‖^2 = t^2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [h_norm_sq]
    congr 1
    change (-(2 - N) / 2) = α
    simp [α]
  have h_arch_majorant_int :
      MeasureTheory.Integrable (fun t : ℝ => C_A * K * (2^(N / 2) * (1 + t^2)^α)) := by
    refine ((h_rpow_integrable'.const_mul (2^(N / 2))).const_mul (C_A * K)).congr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro t
    ring
  have h_prime_majorant_int :
      MeasureTheory.Integrable (fun t : ℝ => C_L * K * (1 + t^2)⁻¹) := by
    exact (integrable_inv_one_add_sq).const_mul (C_L * K)
  have h_majorant_int :
      MeasureTheory.Integrable
        (fun t : ℝ => C_A * K * (2^(N / 2) * (1 + t^2)^α) + C_L * K * (1 + t^2)⁻¹) := by
    exact h_arch_majorant_int.add h_prime_majorant_int
  have h_ptwise :
      ∀ t : ℝ,
        ‖g t‖ ≤ C_A * K * (2^(N / 2) * (1 + t^2)^α) + C_L * K * (1 + t^2)⁻¹ := by
    intro t
    have hArch : ‖hadamardArchPairReflected t‖ ≤ C_A * (1 + |t|)^N := by
      simpa [hadamardArchPairReflected, hadamardReflectedRightLine, abs_neg] using hA_bd (-t)
    have hL : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t)‖
        ≤ C_L := by
      have h_re : (2 : ℝ) ≤ (hadamardReflectedRightLine t).re := by
        simp [hadamardReflectedRightLine]
      exact hL_bd _ h_re
    have hK : ‖hadamardKernel s (hadamardLeftLine t)‖ ≤ K * (1 + t^2)⁻¹ := hK_bd t
    have h_sum_nn : 0 ≤ C_A * (1 + |t|)^N + C_L := by
      have hArch_rhs_nn : 0 ≤ C_A * (1 + |t|)^N := by
        exact mul_nonneg hC_A_nn (Real.rpow_nonneg (by positivity) _)
      linarith
    rw [norm_mul]
    calc
      ‖hadamardArchPairReflected t -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (hadamardReflectedRightLine t)‖ *
          ‖hadamardKernel s (hadamardLeftLine t)‖
        ≤ (C_A * (1 + |t|)^N + C_L) * (K * (1 + t^2)⁻¹) := by
          refine mul_le_mul ?_ hK (norm_nonneg _) h_sum_nn
          calc
            ‖hadamardArchPairReflected t -
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  (hadamardReflectedRightLine t)‖
              ≤ ‖hadamardArchPairReflected t‖ +
                  ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    (hadamardReflectedRightLine t)‖ := by
                    simpa using norm_sub_le (hadamardArchPairReflected t)
                      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                        (hadamardReflectedRightLine t))
            _ ≤ C_A * (1 + |t|)^N + C_L := by linarith
      _ = C_A * K * ((1 + |t|)^N / (1 + t^2)) + C_L * K * (1 + t^2)⁻¹ := by ring
      _ ≤ C_A * K * (2^(N / 2) * (1 + t^2)^α) + C_L * K * (1 + t^2)⁻¹ := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left (pow_div_le_rpow t hN_nn) (mul_nonneg hC_A_nn hK_nn)
  have h_int_g : MeasureTheory.Integrable g := by
    refine h_majorant_int.mono' h_cont.aestronglyMeasurable ?_
    exact MeasureTheory.ae_of_all _ h_ptwise
  refine h_int_g.congr ?_
  refine MeasureTheory.ae_of_all _ ?_
  intro t
  simp only [g]
  rw [hadamardArchBoundaryTerm_left_line_eq]

/-- The symmetric right-edge interval integrals converge to the whole-line integral. -/
theorem tendsto_intervalIntegral_hadamardKernel_right_edge {s : ℂ} (hs_re : s.re < 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in (-T)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I) *
            hadamardKernel s ((2 : ℂ) + (t : ℂ) * I))
      atTop
      (nhds (∫ t : ℝ,
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((2 : ℂ) + (t : ℂ) * I) *
          hadamardKernel s ((2 : ℂ) + (t : ℂ) * I))) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (hadamardKernel_right_edge_integrable hs_re) tendsto_neg_atTop_atBot tendsto_id

/-- The symmetric left-edge interval integrals converge to the whole-line integral. -/
theorem tendsto_intervalIntegral_hadamardKernel_left_edge_archBoundary {s : ℂ} (hs_re : -1 < s.re) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in (-T)..T,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I) *
            hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I))
      atTop
      (nhds (∫ t : ℝ,
        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I) *
          hadamardKernel s ((((-1 : ℝ) : ℂ)) + (t : ℂ) * I))) := by
  simpa [hadamardLeftLine] using
    (MeasureTheory.intervalIntegral_tendsto_integral
      (hadamardKernel_left_edge_archBoundary_integrable hs_re)
      tendsto_neg_atTop_atBot tendsto_id)

end Contour
end WeilPositivity
end ZD

end
