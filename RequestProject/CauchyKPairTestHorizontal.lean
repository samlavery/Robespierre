import Mathlib
import RequestProject.CauchyKPairTestLimit
import RequestProject.CauchyKPairTestResidueSum
import RequestProject.WeilFinalAssembly
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.WeilHorizontalDecay
import RequestProject.OfflineDetectorProof

/-!
# Discharge: horizontal vanishing for the K-twisted Cauchy/Weil identity

Discharges
`K_pairTestMellin_horizontal_vanishes_target gaussianDefectEntireKernel_local β`
unconditionally for every real `β`.

Strategy: pointwise bound

  ‖K(s) · weilIntegrand(M)(s)‖ ≤ M_K · ‖weilIntegrand(M)(s)‖

where `M_K = π·√(π/2) · (exp(9/8) + 2·exp(9/32) + 1)` bounds `K` on the
strip `[-1, 2] × ℝ`. Then the un-twisted pointwise bound
`‖weilIntegrand(M)(σ+iT)‖ ≤ C·T^(N-4)` (from full-strip ζ'/ζ Landau bound +
quartic Mellin decay) yields

  ‖K · w(M)‖(σ+iT) ≤ M_K · C · T^(N-4) → 0.

Integrate over `σ ∈ [-1, 2]` and take T large.

The same template applies at the bottom edge (`-T` instead of `+T`),
using `_neg_unconditional`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly

/-- **Uniform bound on `K` on the strip `[-1, 2] × ℝ`.** Computed for
arbitrary `(σ, T)` with `σ ∈ [-1, 2]`: `(σ - 1/2)² ≤ 9/4`, so the
exponential factors are bounded by `exp(9/(4k))`. -/
private lemma gaussianDefectEntireKernel_bounded_on_strip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ T : ℝ, σ ∈ Set.Icc (-1:ℝ) 2 →
      ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C := by
  set Cprefac : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hCprefac_def
  have hCprefac_nn : 0 ≤ Cprefac := mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  refine ⟨Cprefac * (Real.exp (9/8) + 2 * Real.exp (9/32) + 1), ?_, fun σ T hσ => ?_⟩
  · have h_exp_pos₁ : 0 ≤ Real.exp (9/8) := (Real.exp_pos _).le
    have h_exp_pos₂ : 0 ≤ Real.exp (9/32) := (Real.exp_pos _).le
    apply mul_nonneg hCprefac_nn
    linarith
  unfold gaussianDefectEntireKernel_local
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCprefac_nn]
  apply mul_le_mul_of_nonneg_left _ hCprefac_nn
  obtain ⟨h1, h2⟩ := hσ
  -- Compute (s - 1/2)^2 = (σ-1/2 + iT)^2 = (σ-1/2)² - T² + 2i(σ-1/2)T.
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have h_sub_sq : (s - (1/2 : ℂ))^2 =
      (((σ - 1/2)^2 - T^2 : ℝ) : ℂ) + ((2 * (σ - 1/2) * T : ℝ) : ℂ) * I := by
    rw [hs_def]
    have hyc : (T : ℂ) * Complex.I * ((T : ℂ) * Complex.I) = -((T^2 : ℝ) : ℂ) := by
      have : (T : ℂ) * Complex.I * ((T : ℂ) * Complex.I) = (T : ℂ)^2 * Complex.I^2 := by ring
      rw [this, Complex.I_sq]; push_cast; ring
    have h_sub : (σ : ℂ) + (T : ℂ) * I - (1/2 : ℂ) = ((σ - 1/2 : ℝ) : ℂ) + (T : ℂ) * I := by
      push_cast; ring
    rw [h_sub, sq]
    rw [show (((σ - 1/2 : ℝ) : ℂ) + (T : ℂ) * I) * (((σ - 1/2 : ℝ) : ℂ) + (T : ℂ) * I) =
        (((σ - 1/2 : ℝ) : ℂ))^2 + (2 * (σ - 1/2 : ℝ) * (T : ℂ)) * I +
          (T : ℂ) * I * ((T : ℂ) * I) by ring]
    rw [hyc]; push_cast; ring
  have h_sub_re : ((s - (1/2 : ℂ))^2).re = (σ - 1/2)^2 - T^2 := by
    rw [h_sub_sq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  -- (σ - 1/2)² ≤ 9/4 since -1 ≤ σ ≤ 2 ⟹ -3/2 ≤ σ - 1/2 ≤ 3/2.
  have h_sigma_bd : (σ - 1/2)^2 ≤ 9/4 := by
    have hl : -(3/2 : ℝ) ≤ σ - 1/2 := by linarith
    have hh : σ - 1/2 ≤ 3/2 := by linarith
    have habs : |σ - 1/2| ≤ 3/2 := abs_le.mpr ⟨hl, hh⟩
    nlinarith [abs_nonneg (σ - 1/2), sq_abs (σ - 1/2)]
  have hT_sq_nn : (0 : ℝ) ≤ T^2 := sq_nonneg _
  -- Bound exp /2.
  have h_exp2_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ ≤ Real.exp (9/8) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have h_div_re : ((s - (1/2 : ℂ))^2 / 2).re = ((s - (1/2 : ℂ))^2).re / 2 := by
      simp [Complex.div_re]
    rw [h_div_re, h_sub_re]; linarith
  have h_exp8_norm : ‖Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ ≤ Real.exp (9/32) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have h_div_re : ((s - (1/2 : ℂ))^2 / 8).re = ((s - (1/2 : ℂ))^2).re / 8 := by
      simp [Complex.div_re]
    rw [h_div_re, h_sub_re]; linarith
  -- Triangle.
  calc ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
        2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8) + 1‖
      ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ +
          ‖2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp (9/8) + (2 * Real.exp (9/32)) + 1 := by
        have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h_norm_one]
        have h_2_norm : ‖2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ ≤ 2 * Real.exp (9/32) := by
          rw [norm_mul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          have hnn : 0 ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ := norm_nonneg _
          linarith [h_exp8_norm]
        linarith [h_exp2_norm]

/-- **K-twisted top horizontal edge vanishes.** -/
theorem K_pairTestMellin_topEdgeVanishes (β : ℝ) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖∫ x : ℝ in (-1:ℝ)..2,
          gaussianDefectEntireKernel_local ((x : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ < ε := by
  obtain ⟨M_K, hM_K_nn, hM_K_bd⟩ := gaussianDefectEntireKernel_bounded_on_strip
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt, hLD⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_unconditional
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := uniform_pairMellin_quartic_target_pos β
  -- Total constant.
  set Ktot : ℝ := M_K * C_ζ * C_M * 3 + 1 with hKtot_def
  have hKtot_pos : 0 < Ktot := by
    rw [hKtot_def]
    have h_pos : 0 ≤ M_K * C_ζ * C_M * 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hM_K_nn hC_ζ_pos.le) hC_M_nn) (by norm_num)
    linarith
  intro ε hε
  have h4mN_pos : 0 < 4 - N := by linarith
  have hKε : 0 < Ktot / ε := div_pos hKtot_pos hε
  set Tbig : ℝ := (Ktot / ε) ^ (1 / (4 - N)) with hTbig_def
  have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
  set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hT_ge_Tζ : T₀_ζ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_ge_TM : T₀_M ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_ge_Tbig : Tbig ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_ge_2 : (2 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT_pos : 0 < T := by linarith
  -- Pointwise bound on each σ ∈ [-1, 2].
  have h_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
      ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (T : ℝ) * I)‖ ≤
        M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc (-1:ℝ) 2 = Set.Ioc (-1:ℝ) 2 :=
      Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have hKbd : ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (T : ℝ) * I)‖ ≤ M_K := by
      have h_eq : ((T : ℝ) : ℂ) = ((T : ℝ) : ℂ) := rfl
      have hspec := hM_K_bd σ T hσ_Icc
      convert hspec using 2
    have hζ_bd := hLD T hT_ge_Tζ hGood σ hσ_Icc
    have hM_bd := hM T hT_ge_TM σ hσ_Icc
    rw [norm_mul]
    rw [Contour.weilIntegrand_norm_factored]
    -- Bound: M_K · (C_ζ T^N · C_M / T^4).
    have h_W_nn : 0 ≤ ‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
          ((σ : ℂ) + (T : ℝ) * I)‖ := by positivity
    have h_W_bd : ‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
          ((σ : ℂ) + (T : ℝ) * I)‖ ≤
        C_ζ * T ^ N * (C_M / T ^ 4) := by
      apply mul_le_mul hζ_bd hM_bd (norm_nonneg _)
      exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
    calc ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (T : ℝ) * I)‖ *
          (‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
              ((σ : ℂ) + (T : ℝ) * I)‖)
        ≤ M_K * (‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
              ((σ : ℂ) + (T : ℝ) * I)‖) :=
          mul_le_mul_of_nonneg_right hKbd h_W_nn
      _ ≤ M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) :=
          mul_le_mul_of_nonneg_left h_W_bd hM_K_nn
  -- Integrate.
  have h_int : ‖∫ x : ℝ in (-1:ℝ)..2,
      gaussianDefectEntireKernel_local ((x : ℂ) + (T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ ≤
      (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * |2 - (-1:ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_inner
  have habs : |2 - (-1:ℝ)| = 3 := by norm_num
  rw [habs] at h_int
  -- Final algebra: M_K · C_ζ · C_M · 3 / T^(4-N) < ε.
  have hT4_pos : 0 < T ^ 4 := by positivity
  have hTN_nn : 0 ≤ T ^ N := Real.rpow_nonneg hT_pos.le _
  have h_simp :
      (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * 3 =
        M_K * C_ζ * C_M * 3 * T ^ (N - 4) := by
    have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) =
        M_K * C_ζ * C_M * (T ^ N / T ^ 4) := by ring
    rw [this, hdiv]; ring
  rw [h_simp] at h_int
  have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
    rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
  have hT_pow_ge : (Ktot / ε) ≤ T ^ (4 - N) := by
    have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
      Real.rpow_le_rpow hTbig_pos.le hT_ge_Tbig h4mN_pos.le
    have h_Tbig_pow : Tbig ^ (4 - N) = Ktot / ε := by
      rw [hTbig_def, ← Real.rpow_mul hKε.le]
      have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
  have h_final : M_K * C_ζ * C_M * 3 * T ^ (N - 4) < ε := by
    rw [h_pow_neg]
    have h_lt_K : M_K * C_ζ * C_M * 3 < Ktot := by rw [hKtot_def]; linarith
    have hstep1 : M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N)) <
        Ktot * (1 / T ^ (4 - N)) := by
      apply mul_lt_mul_of_pos_right h_lt_K
      exact div_pos one_pos hT_pow_pos
    have hstep2 : Ktot * (1 / T ^ (4 - N)) ≤ Ktot * (ε / Ktot) := by
      apply mul_le_mul_of_nonneg_left _ hKtot_pos.le
      rw [div_le_div_iff₀ hT_pow_pos hKtot_pos]
      have h := (div_le_iff₀ hε).mp hT_pow_ge
      nlinarith
    have hstep3 : Ktot * (ε / Ktot) = ε := by field_simp
    calc M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N))
        < Ktot * (1 / T ^ (4 - N)) := hstep1
      _ ≤ Ktot * (ε / Ktot) := hstep2
      _ = ε := hstep3
  linarith [h_int]

/-- **K-twisted bottom horizontal edge vanishes.** -/
theorem K_pairTestMellin_bottomEdgeVanishes (β : ℝ) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖∫ x : ℝ in (-1:ℝ)..2,
          gaussianDefectEntireKernel_local ((x : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ < ε := by
  obtain ⟨M_K, hM_K_nn, hM_K_bd⟩ := gaussianDefectEntireKernel_bounded_on_strip
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt, hLD⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := uniform_pairMellin_quartic_target_neg β
  set Ktot : ℝ := M_K * C_ζ * C_M * 3 + 1 with hKtot_def
  have hKtot_pos : 0 < Ktot := by
    rw [hKtot_def]
    have : 0 ≤ M_K * C_ζ * C_M * 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hM_K_nn hC_ζ_pos.le) hC_M_nn) (by norm_num)
    linarith
  intro ε hε
  have h4mN_pos : 0 < 4 - N := by linarith
  have hKε : 0 < Ktot / ε := div_pos hKtot_pos hε
  set Tbig : ℝ := (Ktot / ε) ^ (1 / (4 - N)) with hTbig_def
  have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
  set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hT_ge_Tζ : T₀_ζ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_ge_TM : T₀_M ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_ge_Tbig : Tbig ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_ge_2 : (2 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT_pos : 0 < T := by linarith
  have h_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
      ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (-T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
        M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc (-1:ℝ) 2 = Set.Ioc (-1:ℝ) 2 :=
      Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have hKbd : ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (-T : ℝ) * I)‖ ≤ M_K :=
      hM_K_bd σ (-T) hσ_Icc
    have hζ_bd := hLD T hT_ge_Tζ hGood σ hσ_Icc
    have hM_bd := hM T hT_ge_TM σ hσ_Icc
    rw [norm_mul]
    rw [Contour.weilIntegrand_norm_factored]
    have h_W_nn : 0 ≤ ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
          ((σ : ℂ) + (-T : ℝ) * I)‖ := by positivity
    have h_W_bd : ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
          ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
        C_ζ * T ^ N * (C_M / T ^ 4) := by
      have hζ_bd' : ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ ≤ C_ζ * T ^ N := by
        have h_eq : ((-T : ℝ) : ℂ) = ((-T : ℂ)) := by push_cast; ring
        rw [h_eq]
        exact hLD T hT_ge_Tζ hGood σ hσ_Icc
      have hM_bd' : ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
          C_M / T ^ 4 := by
        have h_eq : ((-T : ℝ) : ℂ) = ((-T : ℂ)) := by push_cast; ring
        rw [h_eq]
        exact hM T hT_ge_TM σ hσ_Icc
      apply mul_le_mul hζ_bd' hM_bd' (norm_nonneg _)
      exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
    calc ‖gaussianDefectEntireKernel_local ((σ : ℂ) + (-T : ℝ) * I)‖ *
          (‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
              ((σ : ℂ) + (-T : ℝ) * I)‖)
        ≤ M_K * (‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
              ((σ : ℂ) + (-T : ℝ) * I)‖) :=
          mul_le_mul_of_nonneg_right hKbd h_W_nn
      _ ≤ M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) :=
          mul_le_mul_of_nonneg_left h_W_bd hM_K_nn
  have h_int : ‖∫ x : ℝ in (-1:ℝ)..2,
      gaussianDefectEntireKernel_local ((x : ℂ) + (-T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ ≤
      (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * |2 - (-1:ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_inner
  have habs : |2 - (-1:ℝ)| = 3 := by norm_num
  rw [habs] at h_int
  have hT4_pos : 0 < T ^ 4 := by positivity
  have h_simp :
      (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * 3 =
        M_K * C_ζ * C_M * 3 * T ^ (N - 4) := by
    have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) =
        M_K * C_ζ * C_M * (T ^ N / T ^ 4) := by ring
    rw [this, hdiv]; ring
  rw [h_simp] at h_int
  have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
    rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
  have hT_pow_ge : (Ktot / ε) ≤ T ^ (4 - N) := by
    have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
      Real.rpow_le_rpow hTbig_pos.le hT_ge_Tbig h4mN_pos.le
    have h_Tbig_pow : Tbig ^ (4 - N) = Ktot / ε := by
      rw [hTbig_def, ← Real.rpow_mul hKε.le]
      have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
  have h_final : M_K * C_ζ * C_M * 3 * T ^ (N - 4) < ε := by
    rw [h_pow_neg]
    have h_lt_K : M_K * C_ζ * C_M * 3 < Ktot := by rw [hKtot_def]; linarith
    have hstep1 : M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N)) <
        Ktot * (1 / T ^ (4 - N)) := by
      apply mul_lt_mul_of_pos_right h_lt_K
      exact div_pos one_pos hT_pow_pos
    have hstep2 : Ktot * (1 / T ^ (4 - N)) ≤ Ktot * (ε / Ktot) := by
      apply mul_le_mul_of_nonneg_left _ hKtot_pos.le
      rw [div_le_div_iff₀ hT_pow_pos hKtot_pos]
      have h := (div_le_iff₀ hε).mp hT_pow_ge
      nlinarith
    have hstep3 : Ktot * (ε / Ktot) = ε := by field_simp
    calc M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N))
        < Ktot * (1 / T ^ (4 - N)) := hstep1
      _ ≤ Ktot * (ε / Ktot) := hstep2
      _ = ε := hstep3
  linarith [h_int]

/-- **Final discharge of `K_pairTestMellin_horizontal_vanishes_target`** for
`K = gaussianDefectEntireKernel_local`. Combines top-edge and bottom-edge
vanishing via triangle inequality. -/
theorem K_pairTestMellin_horizontal_vanishes_target_holds (β : ℝ) :
    K_pairTestMellin_horizontal_vanishes_target gaussianDefectEntireKernel_local β := by
  unfold K_pairTestMellin_horizontal_vanishes_target
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨T_top, hT_top_pos, hT_top⟩ := K_pairTestMellin_topEdgeVanishes β (ε/2) hε2
  obtain ⟨T_bot, hT_bot_pos, hT_bot⟩ := K_pairTestMellin_bottomEdgeVanishes β (ε/2) hε2
  refine ⟨max T_top T_bot, lt_of_lt_of_le hT_top_pos (le_max_left _ _), fun T hT hGood => ?_⟩
  have hT_ge_top : T_top ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_bot : T_bot ≤ T := le_trans (le_max_right _ _) hT
  have h_top_bd := hT_top T hT_ge_top hGood
  have h_bot_bd := hT_bot T hT_ge_bot hGood
  -- Triangle inequality.
  calc ‖(∫ x : ℝ in (-1:ℝ)..2,
        gaussianDefectEntireKernel_local ((x : ℂ) + (-T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
       (∫ x : ℝ in (-1:ℝ)..2,
        gaussianDefectEntireKernel_local ((x : ℂ) + (T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖
      ≤ ‖(∫ x : ℝ in (-1:ℝ)..2,
            gaussianDefectEntireKernel_local ((x : ℂ) + (-T : ℝ) * I) *
            weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I))‖ +
        ‖(∫ x : ℝ in (-1:ℝ)..2,
            gaussianDefectEntireKernel_local ((x : ℂ) + (T : ℝ) * I) *
            weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ :=
        norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_pairTestMellin_horizontal_vanishes_target_holds
