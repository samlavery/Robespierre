import Mathlib
import RequestProject.ArchKernelRectShift
import RequestProject.WeilArchKernelResidues
import RequestProject.UniformArchKernelBound
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.DigammaVerticalBound

/-!
# Horizontal edge decay for `archKernel · pairTestMellin β`

As `T → ±∞`, the horizontal-edge integrals of `F = archKernel · pairTestMellin β`
over `x ∈ [-1, 2]` go to `0`.

## Strategy

* **archKernel log bound** (full strip, T ≥ 2): Uniform `‖archKernel(σ+iT)‖ ≤ C·log(1+T)`
  via a single digamma shift `ψ(z) = ψ(z+1) - z⁻¹` applied at each half-argument.
  For σ ∈ [-1,2], the shifted half-argument `z+1` lands in `[1/2, 2]` × {T/2·I},
  covered by `digamma_log_bound_uniform_compact`.

* **Product decay** (T ≥ 2): Combined with `pairTestMellin_quartic_bound_extended`
  (decay C/T^4), the product `‖F‖ ≤ C·log(T)/T^4 → 0`.

* **Integral decay**: `‖∫ F(x+iT) dx‖ ≤ 3 · C · log(T)/T^4 → 0` by
  `intervalIntegral.norm_integral_le_of_norm_le_const` + `squeeze_zero_norm'`.

* **T → -∞**: Apply conjugation symmetry of `‖F(σ+i(-T))‖ = ‖F(σ+iT)‖`, reducing
  to `atTop` via composition with negation.
-/

open Complex Real MeasureTheory Set Filter
open scoped Real

noncomputable section

namespace ZD.ArchKernelRectShift

open ZD.WeilArchKernelResidues ZD.WeilPositivity.Contour
open ZD.WeilPositivity.HorizontalTailsDischarge

set_option maxHeartbeats 800000

/-! ## Uniform log bound on archKernel for σ ∈ [-1, 2], T ≥ 2 -/

private lemma archKernel_log_bound_full_strip :
    ∃ C : ℝ, 0 < C ∧
    ∀ σ : ℝ, σ ∈ Set.Icc (-1 : ℝ) 2 →
    ∀ T : ℝ, 2 ≤ T →
      ‖archKernel ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * Real.log (1 + T) := by
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ :=
    digamma_log_bound_uniform_compact (1/2) 2 (by norm_num) (by norm_num)
  have h_logpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi + Cd + 1, by linarith, fun σ hσ T hT => ?_⟩
  have hT_pos : 0 < T := by linarith
  have hT_ne : T ≠ 0 := hT_pos.ne'
  -- Γℝ(σ+iT) ≠ 0 (zeros at -2k have Im = 0)
  have h_GR_ne : ∀ u : ℂ, u.im ≠ 0 → u.Gammaℝ ≠ 0 := by
    intro u hu hzero
    rcases Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp [Complex.neg_im, Complex.mul_im, Complex.natCast_im] at him
    exact hu him
  have hs_im : ((σ : ℂ) + (T : ℂ) * I).im = T := by simp
  have h1s_im : (1 - ((σ : ℂ) + (T : ℂ) * I)).im = -T := by simp
  have hs_GR_ne : ((σ : ℂ) + (T : ℂ) * I).Gammaℝ ≠ 0 :=
    h_GR_ne _ (by rw [hs_im]; exact hT_ne)
  have h1s_GR_ne : (1 - ((σ : ℂ) + (T : ℂ) * I)).Gammaℝ ≠ 0 :=
    h_GR_ne _ (by rw [h1s_im]; linarith)
  have hs_ne_2n : ∀ n : ℕ, ((σ : ℂ) + (T : ℂ) * I) ≠ -(2 * (n : ℂ)) := fun n h =>
    hs_GR_ne (Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have h1s_ne_2n : ∀ n : ℕ, (1 - ((σ : ℂ) + (T : ℂ) * I)) ≠ -(2 * (n : ℂ)) := fun n h =>
    h1s_GR_ne (Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  -- Triangle inequality on archKernel = (Γℝ'/Γℝ)(s) + (Γℝ'/Γℝ)(1-s)
  have h_tri : ‖archKernel ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      ‖deriv Gammaℝ ((σ : ℂ) + (T : ℂ) * I) / ((σ : ℂ) + (T : ℂ) * I).Gammaℝ‖ +
      ‖deriv Gammaℝ (1 - ((σ : ℂ) + (T : ℂ) * I)) / (1 - ((σ : ℂ) + (T : ℂ) * I)).Gammaℝ‖ :=
    norm_add_le _ _
  -- Helper: bound ‖-logπ/2 + (1/2)·(ψ₁ - z⁻¹)‖ ≤ logπ/2 + (1/2)·(ψ_bd + inv_bd)
  have h_logpi_bd : ‖-(Complex.log ↑Real.pi) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg,
      show Complex.log ↑Real.pi = ((Real.log Real.pi : ℝ) : ℂ) from
        (Complex.ofReal_log Real.pi_pos.le).symm,
      Complex.norm_real, Real.norm_of_nonneg h_logpi_nn, show ‖(2:ℂ)‖ = 2 by norm_num]
  have h_half_c : ‖(1/2:ℂ)‖ = 1/2 := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, Complex.norm_real]; norm_num
  have h_single_bd : ∀ (ψ_bd inv_bd : ℝ) (ψ_v zinv : ℂ),
      ‖ψ_v‖ ≤ ψ_bd → ‖zinv‖ ≤ inv_bd →
      ‖-(Complex.log ↑Real.pi) / 2 + 1/2 * (ψ_v - zinv)‖ ≤
        Real.log Real.pi / 2 + 1/2 * (ψ_bd + inv_bd) := fun ψ_bd inv_bd ψ_v zinv hψ hinv => by
    calc ‖-(Complex.log ↑Real.pi) / 2 + 1/2 * (ψ_v - zinv)‖
        ≤ ‖-(Complex.log ↑Real.pi) / 2‖ + ‖1/2 * (ψ_v - zinv)‖ := norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + 1/2 * (ψ_bd + inv_bd) := by
            apply add_le_add (h_logpi_bd ▸ le_refl _)
            rw [norm_mul, h_half_c]
            exact mul_le_mul_of_nonneg_left
              (le_trans (norm_sub_le _ _) (add_le_add hψ hinv)) (by norm_num)
  -- Shared data: half-argument shifts
  have hT2_ge : 1 ≤ |T/2| := by rw [abs_of_pos (by linarith)]; linarith
  have hnT2_ge : 1 ≤ |-T/2| := by
    rw [show -T/2 = -(T/2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith
  -- z₁ = (σ/2) + (T/2)·I
  set z₁ : ℂ := ((σ/2:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I with hz₁
  have hz₁_im_ne : z₁.im ≠ 0 := by simp [hz₁]; linarith
  have hz₁_ne_nat : ∀ m : ℕ, z₁ ≠ -(m:ℂ) := fun m h => hz₁_im_ne (by rw [h]; simp)
  have h_shift₁ := Complex.digamma_apply_add_one z₁ hz₁_ne_nat
  have hz₁p1_eq : z₁ + 1 = ((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I := by
    simp [hz₁]; push_cast; ring
  have hσ2p1_mem : σ/2+1 ∈ Set.Icc (1/2:ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have h_psi₁ : ‖deriv Complex.Gamma (((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I) /
      Complex.Gamma (((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I)‖ ≤ Cd * Real.log (1 + |T/2|) :=
    hCd_bd (σ/2+1) hσ2p1_mem (T/2) hT2_ge
  have hz₁_inv_bd : ‖z₁⁻¹‖ ≤ 2/T := by
    rw [norm_inv]
    apply inv_le_of_inv_le₀ (by positivity)
    rw [inv_div]
    have h_im : z₁.im = T/2 := by simp [hz₁]
    have h1 : T/2 ≤ ‖z₁‖ := by
      have := Complex.abs_im_le_norm z₁
      rw [h_im] at this; linarith [abs_of_pos (show 0 < T/2 by linarith)]
    linarith
  -- z₂ = ((1-σ)/2) + (-T/2)·I
  set z₂ : ℂ := (((1-σ)/2:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I with hz₂
  have hz₂_im_ne : z₂.im ≠ 0 := by simp [hz₂]; linarith
  have hz₂_ne_nat : ∀ m : ℕ, z₂ ≠ -(m:ℂ) := fun m h => hz₂_im_ne (by rw [h]; simp)
  have h_shift₂ := Complex.digamma_apply_add_one z₂ hz₂_ne_nat
  have hz₂p1_eq : z₂ + 1 = (((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I := by
    simp [hz₂]; push_cast; ring
  have h1σ2p1_mem : (1-σ)/2+1 ∈ Set.Icc (1/2:ℝ) 2 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have h_psi₂ : ‖deriv Complex.Gamma ((((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I) /
      Complex.Gamma ((((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I)‖ ≤ Cd * Real.log (1 + |-T/2|) :=
    hCd_bd ((1-σ)/2+1) h1σ2p1_mem (-T/2) hnT2_ge
  have hz₂_inv_bd : ‖z₂⁻¹‖ ≤ 2/T := by
    rw [norm_inv]
    apply inv_le_of_inv_le₀ (by positivity)
    rw [inv_div]
    have h_im : z₂.im = -T/2 := by simp [hz₂]
    have h1 : T/2 ≤ ‖z₂‖ := by
      have h := Complex.abs_im_le_norm z₂
      rw [h_im] at h
      have : |-T/2| = T/2 := by rw [show -T/2 = -(T/2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith [this ▸ h]
    linarith
  -- Bound ‖(Γℝ'/Γℝ)(σ+iT)‖ using digamma shift
  have h_term1 : ‖deriv Gammaℝ ((σ:ℂ) + (T:ℂ) * I) / ((σ:ℂ) + (T:ℂ) * I).Gammaℝ‖ ≤
      Real.log Real.pi / 2 + 1/2 * (Cd * Real.log (1 + |T/2|) + 2/T) := by
    have h_form₁ := gammaℝ_logDeriv_digamma_form ((σ:ℂ) + (T:ℂ) * I) hs_GR_ne hs_ne_2n
    rw [h_form₁]
    have hs_half : ((σ:ℂ) + (T:ℂ) * I) / 2 = z₁ := by simp [hz₁]; push_cast; ring
    rw [hs_half]
    -- Now goal: ‖-log π/2 + 1/2*(Γ'(z₁)/Γ(z₁))‖ ≤ ...
    have h_pred : deriv Complex.Gamma z₁ / Complex.Gamma z₁ =
        deriv Complex.Gamma (z₁+1) / Complex.Gamma (z₁+1) - z₁⁻¹ := by
      have h := Complex.digamma_apply_add_one z₁ hz₁_ne_nat
      simp only [Complex.digamma_def, logDeriv_apply] at h
      linear_combination -h
    rw [h_pred, hz₁p1_eq]
    exact h_single_bd _ _ _ _ h_psi₁ hz₁_inv_bd
  -- Bound ‖(Γℝ'/Γℝ)(1-σ-iT)‖ using digamma shift
  have h_term2 : ‖deriv Gammaℝ (1 - ((σ:ℂ) + (T:ℂ) * I)) / (1 - ((σ:ℂ) + (T:ℂ) * I)).Gammaℝ‖ ≤
      Real.log Real.pi / 2 + 1/2 * (Cd * Real.log (1 + |-T/2|) + 2/T) := by
    have h_form₂ := gammaℝ_logDeriv_digamma_form (1 - ((σ:ℂ) + (T:ℂ) * I)) h1s_GR_ne h1s_ne_2n
    rw [h_form₂]
    have h1s_half : (1 - ((σ:ℂ) + (T:ℂ) * I)) / 2 = z₂ := by simp [hz₂]; push_cast; ring
    rw [h1s_half]
    have h_pred : deriv Complex.Gamma z₂ / Complex.Gamma z₂ =
        deriv Complex.Gamma (z₂+1) / Complex.Gamma (z₂+1) - z₂⁻¹ := by
      have h := Complex.digamma_apply_add_one z₂ hz₂_ne_nat
      simp only [Complex.digamma_def, logDeriv_apply] at h
      linear_combination -h
    rw [h_pred, hz₂p1_eq]
    exact h_single_bd _ _ _ _ h_psi₂ hz₂_inv_bd
  -- Combine: use log(1+T/2) ≤ log(1+T), |±T/2| = T/2, and 2/T ≤ 1
  have h_abs₁ : |T/2| = T/2 := abs_of_pos (by linarith)
  have h_abs₂ : |-T/2| = T/2 := by rw [show -T/2 = -(T/2) by ring, abs_neg, h_abs₁]
  have h_logT2 : Real.log (1 + T/2) ≤ Real.log (1 + T) :=
    Real.log_le_log (by linarith) (by linarith)
  have h_2T : 2/T ≤ 1 := (div_le_one hT_pos).mpr (by linarith)
  have h_logT_ge1 : 1 ≤ Real.log (1 + T) := by
    have h3 : (3 : ℝ) ≤ 1 + T := by linarith
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ Real.log (1 + T) := Real.log_le_log (by norm_num) h3
  have h_log_abs1 : Real.log (1 + |T / 2|) ≤ Real.log (1 + T) := by
    rw [h_abs₁]; exact h_logT2
  have h_log_abs2 : Real.log (1 + |-T / 2|) ≤ Real.log (1 + T) := by
    rw [h_abs₂]; exact h_logT2
  nlinarith [h_tri, h_term1, h_term2, hCd_pos.le, h_log_abs1, h_log_abs2,
    Real.log_nonneg (show 1 ≤ 1 + T by linarith)]

/-! ## Decay of the product F for T ≥ 2 -/

private lemma F_product_decay (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T →
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      ‖pairTestMellin_archKernel_product β ((σ : ℂ) + (T : ℂ) * I)‖ ≤
        C * Real.log (1 + T) / T ^ 4 := by
  obtain ⟨Ca, hCa_pos, hCa_bd⟩ := archKernel_log_bound_full_strip
  obtain ⟨Cp, hCp_nn, hCp_bd⟩ := pairTestMellin_quartic_bound_extended β
  refine ⟨Ca * Cp, mul_nonneg hCa_pos.le hCp_nn, fun T hT σ hσ => ?_⟩
  have hT_pos : 0 < T := by linarith
  unfold pairTestMellin_archKernel_product
  rw [norm_mul]
  calc ‖archKernel ((σ:ℂ) + (T:ℂ) * I)‖ * ‖pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)‖
      ≤ Ca * Real.log (1 + T) * (Cp / T ^ 4) :=
        mul_le_mul (hCa_bd σ hσ T hT) (hCp_bd σ hσ T (by linarith))
          (norm_nonneg _)
          (mul_nonneg hCa_pos.le (Real.log_nonneg (by linarith)))
    _ = Ca * Cp * Real.log (1 + T) / T ^ 4 := by ring

/-! ## Neg-T archKernel log bound and product decay -/

private lemma archKernel_log_bound_full_strip_neg :
    ∃ C : ℝ, 0 < C ∧
    ∀ σ : ℝ, σ ∈ Set.Icc (-1 : ℝ) 2 →
    ∀ T : ℝ, T ≤ -2 →
      ‖archKernel ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * Real.log (1 + (-T)) := by
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ :=
    digamma_log_bound_uniform_compact (1/2) 2 (by norm_num) (by norm_num)
  have h_logpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi + Cd + 1, by linarith, fun σ hσ T hT => ?_⟩
  have hT_neg : T < 0 := by linarith
  have hT_ne : T ≠ 0 := hT_neg.ne
  have hN : 0 < -T := by linarith
  -- Γℝ(σ+iT) ≠ 0 (Im = T ≠ 0)
  have h_GR_ne : ∀ u : ℂ, u.im ≠ 0 → u.Gammaℝ ≠ 0 := by
    intro u hu hzero
    rcases Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp [Complex.neg_im, Complex.mul_im, Complex.natCast_im] at him
    exact hu him
  have hs_im : ((σ : ℂ) + (T : ℂ) * I).im = T := by simp
  have h1s_im : (1 - ((σ : ℂ) + (T : ℂ) * I)).im = -T := by simp
  have hs_GR_ne : ((σ : ℂ) + (T : ℂ) * I).Gammaℝ ≠ 0 :=
    h_GR_ne _ (by rw [hs_im]; exact hT_ne)
  have h1s_GR_ne : (1 - ((σ : ℂ) + (T : ℂ) * I)).Gammaℝ ≠ 0 :=
    h_GR_ne _ (by rw [h1s_im]; linarith)
  have hs_ne_2n : ∀ n : ℕ, ((σ : ℂ) + (T : ℂ) * I) ≠ -(2 * (n : ℂ)) := fun n h =>
    hs_GR_ne (Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have h1s_ne_2n : ∀ n : ℕ, (1 - ((σ : ℂ) + (T : ℂ) * I)) ≠ -(2 * (n : ℂ)) := fun n h =>
    h1s_GR_ne (Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have h_tri : ‖archKernel ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      ‖deriv Gammaℝ ((σ : ℂ) + (T : ℂ) * I) / ((σ : ℂ) + (T : ℂ) * I).Gammaℝ‖ +
      ‖deriv Gammaℝ (1 - ((σ : ℂ) + (T : ℂ) * I)) / (1 - ((σ : ℂ) + (T : ℂ) * I)).Gammaℝ‖ :=
    norm_add_le _ _
  have h_logpi_bd : ‖-(Complex.log ↑Real.pi) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg,
      show Complex.log ↑Real.pi = ((Real.log Real.pi : ℝ) : ℂ) from
        (Complex.ofReal_log Real.pi_pos.le).symm,
      Complex.norm_real, Real.norm_of_nonneg h_logpi_nn, show ‖(2:ℂ)‖ = 2 by norm_num]
  have h_half_c : ‖(1/2:ℂ)‖ = 1/2 := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, Complex.norm_real]; norm_num
  have h_single_bd : ∀ (ψ_bd inv_bd : ℝ) (ψ_v zinv : ℂ),
      ‖ψ_v‖ ≤ ψ_bd → ‖zinv‖ ≤ inv_bd →
      ‖-(Complex.log ↑Real.pi) / 2 + 1/2 * (ψ_v - zinv)‖ ≤
        Real.log Real.pi / 2 + 1/2 * (ψ_bd + inv_bd) := fun ψ_bd inv_bd ψ_v zinv hψ hinv => by
    calc ‖-(Complex.log ↑Real.pi) / 2 + 1/2 * (ψ_v - zinv)‖
        ≤ ‖-(Complex.log ↑Real.pi) / 2‖ + ‖1/2 * (ψ_v - zinv)‖ := norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + 1/2 * (ψ_bd + inv_bd) := by
            apply add_le_add (h_logpi_bd ▸ le_refl _)
            rw [norm_mul, h_half_c]
            exact mul_le_mul_of_nonneg_left
              (le_trans (norm_sub_le _ _) (add_le_add hψ hinv)) (by norm_num)
  -- |T/2| ≥ 1 and |-T/2| ≥ 1 (both work since |T| ≥ 2)
  have hT2_ge : 1 ≤ |T/2| := by rw [abs_of_neg (by linarith)]; linarith
  have hnT2_ge : 1 ≤ |-T/2| := by
    rw [show -T/2 = -(T/2) by ring, abs_neg, abs_of_neg (by linarith)]; linarith
  -- z₁ = (σ/2) + (T/2)·I, Im = T/2 < 0
  set z₁ : ℂ := ((σ/2:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I with hz₁
  have hz₁_im_ne : z₁.im ≠ 0 := by simp [hz₁]; linarith
  have hz₁_ne_nat : ∀ m : ℕ, z₁ ≠ -(m:ℂ) := fun m h => hz₁_im_ne (by rw [h]; simp)
  have h_shift₁ := Complex.digamma_apply_add_one z₁ hz₁_ne_nat
  have hz₁p1_eq : z₁ + 1 = ((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I := by
    simp [hz₁]; push_cast; ring
  have hσ2p1_mem : σ/2+1 ∈ Set.Icc (1/2:ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have h_psi₁ : ‖deriv Complex.Gamma (((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I) /
      Complex.Gamma (((σ/2+1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I)‖ ≤ Cd * Real.log (1 + |T/2|) :=
    hCd_bd (σ/2+1) hσ2p1_mem (T/2) hT2_ge
  have hz₁_inv_bd : ‖z₁⁻¹‖ ≤ 2/(-T) := by
    rw [norm_inv]
    apply inv_le_of_inv_le₀ (by positivity)
    rw [inv_div]
    have h_im : z₁.im = T/2 := by simp [hz₁]
    have h1 : (-T)/2 ≤ ‖z₁‖ := by
      have := Complex.abs_im_le_norm z₁
      rw [h_im] at this
      rw [abs_of_neg (show T/2 < 0 by linarith)] at this; linarith
    linarith
  -- z₂ = ((1-σ)/2) + (-T/2)·I, Im = -T/2 > 0
  set z₂ : ℂ := (((1-σ)/2:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I with hz₂
  have hz₂_im_ne : z₂.im ≠ 0 := by simp [hz₂]; linarith
  have hz₂_ne_nat : ∀ m : ℕ, z₂ ≠ -(m:ℂ) := fun m h => hz₂_im_ne (by rw [h]; simp)
  have h_shift₂ := Complex.digamma_apply_add_one z₂ hz₂_ne_nat
  have hz₂p1_eq : z₂ + 1 = (((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I := by
    simp [hz₂]; push_cast; ring
  have h1σ2p1_mem : (1-σ)/2+1 ∈ Set.Icc (1/2:ℝ) 2 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have h_psi₂ : ‖deriv Complex.Gamma ((((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I) /
      Complex.Gamma ((((1-σ)/2+1:ℝ):ℂ) + ((-T/2:ℝ):ℂ) * I)‖ ≤ Cd * Real.log (1 + |-T/2|) :=
    hCd_bd ((1-σ)/2+1) h1σ2p1_mem (-T/2) hnT2_ge
  have hz₂_inv_bd : ‖z₂⁻¹‖ ≤ 2/(-T) := by
    rw [norm_inv]
    apply inv_le_of_inv_le₀ (by positivity)
    rw [inv_div]
    have h_im : z₂.im = -T/2 := by simp [hz₂]
    have h1 : (-T)/2 ≤ ‖z₂‖ := by
      have h := Complex.abs_im_le_norm z₂
      rw [h_im] at h
      have : |-T/2| = -T/2 := by rw [show -T/2 = -(T/2) by ring, abs_neg, abs_of_neg (show T/2 < 0 by linarith)]
      linarith [this ▸ h]
    linarith
  have h_term1 : ‖deriv Gammaℝ ((σ:ℂ) + (T:ℂ) * I) / ((σ:ℂ) + (T:ℂ) * I).Gammaℝ‖ ≤
      Real.log Real.pi / 2 + 1/2 * (Cd * Real.log (1 + |T/2|) + 2/(-T)) := by
    have h_form₁ := gammaℝ_logDeriv_digamma_form ((σ:ℂ) + (T:ℂ) * I) hs_GR_ne hs_ne_2n
    rw [h_form₁]
    have hs_half : ((σ:ℂ) + (T:ℂ) * I) / 2 = z₁ := by simp [hz₁]; push_cast; ring
    rw [hs_half]
    have h_pred : deriv Complex.Gamma z₁ / Complex.Gamma z₁ =
        deriv Complex.Gamma (z₁+1) / Complex.Gamma (z₁+1) - z₁⁻¹ := by
      have h := Complex.digamma_apply_add_one z₁ hz₁_ne_nat
      simp only [Complex.digamma_def, logDeriv_apply] at h
      linear_combination -h
    rw [h_pred, hz₁p1_eq]; exact h_single_bd _ _ _ _ h_psi₁ hz₁_inv_bd
  have h_term2 : ‖deriv Gammaℝ (1 - ((σ:ℂ) + (T:ℂ) * I)) / (1 - ((σ:ℂ) + (T:ℂ) * I)).Gammaℝ‖ ≤
      Real.log Real.pi / 2 + 1/2 * (Cd * Real.log (1 + |-T/2|) + 2/(-T)) := by
    have h_form₂ := gammaℝ_logDeriv_digamma_form (1 - ((σ:ℂ) + (T:ℂ) * I)) h1s_GR_ne h1s_ne_2n
    rw [h_form₂]
    have h1s_half : (1 - ((σ:ℂ) + (T:ℂ) * I)) / 2 = z₂ := by simp [hz₂]; push_cast; ring
    rw [h1s_half]
    have h_pred : deriv Complex.Gamma z₂ / Complex.Gamma z₂ =
        deriv Complex.Gamma (z₂+1) / Complex.Gamma (z₂+1) - z₂⁻¹ := by
      have h := Complex.digamma_apply_add_one z₂ hz₂_ne_nat
      simp only [Complex.digamma_def, logDeriv_apply] at h
      linear_combination -h
    rw [h_pred, hz₂p1_eq]; exact h_single_bd _ _ _ _ h_psi₂ hz₂_inv_bd
  have h_abs₁ : |T/2| = -T/2 := by
    rw [show -T/2 = -(T/2) by ring]
    exact abs_of_neg (div_neg_of_neg_of_pos hT_neg two_pos)
  have h_abs₂ : |-T/2| = -T/2 := by
    rw [show -T/2 = -(T/2) by ring, abs_neg, abs_of_neg (show T/2 < 0 by linarith)]
  -- Substitute absolute values in terms bounds
  have h_logT2 : Real.log (1 + (-T/2)) ≤ Real.log (1 + (-T)) :=
    Real.log_le_log (by linarith) (by linarith)
  have h_2T : 2/(-T) ≤ 1 := (div_le_one hN).mpr (by linarith)
  have h_logT_ge1 : 1 ≤ Real.log (1 + (-T)) := by
    have h3 : (3 : ℝ) ≤ 1 + (-T) := by linarith
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ Real.log (1 + (-T)) := Real.log_le_log (by norm_num) h3
  have h_log_abs1 : Real.log (1 + |T / 2|) ≤ Real.log (1 + (-T)) := by
    rw [h_abs₁]; exact h_logT2
  have h_log_abs2 : Real.log (1 + |-T / 2|) ≤ Real.log (1 + (-T)) := by
    rw [h_abs₂]; exact h_logT2
  nlinarith [h_tri, h_term1, h_term2, hCd_pos.le, h_log_abs1, h_log_abs2,
    Real.log_nonneg (show 1 ≤ 1 + (-T) by linarith)]

-- Norm symmetry for pairTestMellin under negation of imaginary part
private lemma pairTestMellin_norm_neg_im' (β : ℝ) (σ T : ℝ) :
    ‖pairTestMellin β ((σ:ℂ) - (T:ℂ) * I)‖ = ‖pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)‖ := by
  have h_eq : pairTestMellin β ((σ:ℂ) - (T:ℂ) * I) =
      star (pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)) := by
    simp only [pairTestMellin, mellin]
    rw [show star (∫ t in Set.Ioi (0:ℝ), (t:ℂ) ^ ((σ:ℂ) + (T:ℂ) * I - 1) •
          (ZD.WeilPositivity.pair_cosh_gauss_test β t : ℂ)) =
        ∫ t in Set.Ioi (0:ℝ), star ((t:ℂ) ^ ((σ:ℂ) + (T:ℂ) * I - 1) •
          (ZD.WeilPositivity.pair_cosh_gauss_test β t : ℂ)) from integral_conj.symm]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t (ht : 0 < t)
    simp only [star_smul]
    congr 1
    · have h_key : (t : ℂ) ^ (starRingEnd ℂ ((σ:ℂ) + (T:ℂ) * I - 1)) =
          starRingEnd ℂ ((t:ℂ) ^ ((σ:ℂ) + (T:ℂ) * I - 1)) := by
        rw [Complex.cpow_conj (hx := by
          rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne)]
        rw [Complex.conj_ofReal]
      simp only [starRingEnd_apply] at h_key
      convert h_key using 2
      apply Complex.ext <;> simp
    · exact (Complex.conj_ofReal _).symm
  rw [h_eq]; exact norm_star _

private lemma F_product_decay_neg (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, T ≤ -2 →
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      ‖pairTestMellin_archKernel_product β ((σ : ℂ) + (T : ℂ) * I)‖ ≤
        C * Real.log (1 + (-T)) / (-T) ^ 4 := by
  obtain ⟨Ca, hCa_pos, hCa_bd⟩ := archKernel_log_bound_full_strip_neg
  obtain ⟨Cp, hCp_nn, hCp_bd⟩ := pairTestMellin_quartic_bound_extended β
  refine ⟨Ca * Cp, mul_nonneg hCa_pos.le hCp_nn, fun T hT σ hσ => ?_⟩
  have hN_pos : 0 < -T := by linarith
  have hN_ge : 2 ≤ -T := by linarith
  -- Use norm symmetry and quartic bound for -T ≥ 2
  have h_pair_bd : ‖pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)‖ ≤ Cp / (-T)^4 := by
    -- σ + T*I = σ - (-T)*I, and pairTestMellin_norm_neg_im' gives norm symmetry
    have h_sym := pairTestMellin_norm_neg_im' β σ (-T)
    -- h_sym : ‖pairTestMellin β (σ - (-T)*I)‖ = ‖pairTestMellin β (σ + (-T)*I)‖
    have h_eq : ((σ:ℂ) + (T:ℂ) * I) = (σ:ℂ) - ((-T:ℝ):ℂ) * I := by
      simp [Complex.ofReal_neg]
    rw [h_eq, h_sym]; exact hCp_bd σ hσ (-T) (by linarith)
  unfold pairTestMellin_archKernel_product
  rw [norm_mul]
  calc ‖archKernel ((σ:ℂ) + (T:ℂ) * I)‖ * ‖pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)‖
      ≤ Ca * Real.log (1 + (-T)) * (Cp / (-T)^4) :=
        mul_le_mul (hCa_bd σ hσ T hT) h_pair_bd
          (norm_nonneg _)
          (mul_nonneg hCa_pos.le (Real.log_nonneg (by linarith)))
    _ = Ca * Cp * Real.log (1 + (-T)) / (-T)^4 := by ring

/-- `C · log(1+T) / T^4 → 0` as `T → +∞`. -/
private lemma log_div_T4_tendsto_zero (C : ℝ) :
    Filter.Tendsto (fun T : ℝ => C * Real.log (1 + T) / T ^ 4) Filter.atTop (nhds 0) := by
  -- Use squeeze: log(1+T) ≤ T, so C*log(1+T)/T^4 ≤ C*(1/T^3) or -C*(1/T^3) → 0
  have hkey : Filter.Tendsto (fun T : ℝ => Real.log (1 + T) / T ^ 4) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (tendsto_const_nhds.div_atTop (Filter.tendsto_pow_atTop (n := 3) (by norm_num)))
    · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT
      exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT
      have hlogT : Real.log (1 + T) ≤ T := by
        have : 1 + T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
        calc Real.log (1 + T) ≤ Real.log (Real.exp T) := Real.log_le_log (by linarith) this
          _ = T := Real.log_exp T
      have hT0 : T ≠ 0 := by linarith
      calc Real.log (1 + T) / T ^ 4
          ≤ T / T ^ 4 := div_le_div_of_nonneg_right hlogT (by positivity)
        _ = 1 / T ^ 3 := by field_simp
  simpa [mul_div_assoc] using hkey.const_mul C

theorem F_horizontal_edge_tendsto_zero (β : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC_nn, hC_bd⟩ := F_product_decay β
  -- Bound ‖∫ F(x+iT) dx‖ ≤ 3 · C · log(1+T) / T^4 for T ≥ 2, then → 0
  apply squeeze_zero_norm'
  · filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with T hT
    have h_bnd : ∀ x ∈ Set.uIoc (-1:ℝ) 2,
        ‖pairTestMellin_archKernel_product β ((x:ℂ) + (T:ℂ) * I)‖ ≤
          C * Real.log (1 + T) / T ^ 4 := by
      intro x hx
      have hx_mem : x ∈ Set.Icc (-1:ℝ) 2 := by
        rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx
        exact Set.Ioc_subset_Icc_self hx
      exact hC_bd T hT x hx_mem
    calc ‖∫ x in (-1:ℝ)..2, pairTestMellin_archKernel_product β ((x:ℂ) + (T:ℂ) * I)‖
        ≤ C * Real.log (1 + T) / T ^ 4 * |2 - (-1)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_bnd
      _ = 3 * (C * Real.log (1 + T) / T ^ 4) := by norm_num; ring
      _ = 3 * C * Real.log (1 + T) / T ^ 4 := by ring
  · -- 3 * C * log(1+T) / T^4 → 0
    have := log_div_T4_tendsto_zero (3 * C)
    simpa [mul_div_assoc, mul_assoc]

theorem F_horizontal_edge_tendsto_zero_neg (β : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℂ) * Complex.I))
      Filter.atBot (nhds 0) := by
  -- Reduce to atTop via T ↦ -T: atBot = map Neg.neg atTop
  rw [show Filter.atBot (α := ℝ) = Filter.map Neg.neg Filter.atTop from
    Filter.map_neg_atTop.symm]
  rw [Filter.tendsto_map'_iff]
  simp only [Function.comp_def]
  -- Now: Tendsto (fun T => ∫ F(x + i(-T)) dx) atTop (nhds 0)
  obtain ⟨C, hC_nn, hC_bd⟩ := F_product_decay_neg β
  apply squeeze_zero_norm'
  · filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with T hT
    -- For T ≥ 2: -T ≤ -2, so F_product_decay_neg applies
    have hNT : (-T) ≤ -2 := by linarith
    have h_bnd : ∀ x ∈ Set.uIoc (-1:ℝ) 2,
        ‖pairTestMellin_archKernel_product β ((x:ℂ) + (-(T:ℂ)) * I)‖ ≤
          C * Real.log (1 + T) / T ^ 4 := by
      intro x hx
      have hx_mem : x ∈ Set.Icc (-1:ℝ) 2 := by
        rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx
        exact Set.Ioc_subset_Icc_self hx
      have h_bd := hC_bd (-T) hNT x hx_mem
      simp only [neg_neg] at h_bd
      convert h_bd using 2 <;> push_cast <;> ring_nf
    have h_neg_cast : ∀ x : ℝ, (x : ℂ) + (↑(-T) : ℂ) * I = (x : ℂ) + (-(T:ℂ)) * I := by
      intro x; push_cast; ring
    simp_rw [h_neg_cast]
    calc ‖∫ x in (-1:ℝ)..2, pairTestMellin_archKernel_product β ((x:ℂ) + (-(T:ℂ)) * I)‖
        ≤ C * Real.log (1 + T) / T ^ 4 * |2 - (-1)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_bnd
      _ = 3 * (C * Real.log (1 + T) / T ^ 4) := by norm_num; ring
      _ = 3 * C * Real.log (1 + T) / T ^ 4 := by ring
  · -- 3 * C * log(1+T) / T^4 → 0
    have := log_div_T4_tendsto_zero (3 * C)
    simpa [mul_div_assoc, mul_assoc]

#check @F_horizontal_edge_tendsto_zero
#check @F_horizontal_edge_tendsto_zero_neg

end ZD.ArchKernelRectShift
end
