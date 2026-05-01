import Mathlib
import RequestProject.UniformGammaRBound
import RequestProject.DigammaVerticalBound
import RequestProject.WeilContour

/-!
# Vertical integrability of `archFactor / (s · (s+1))` at `σ = 2`

This file extends `digamma_log_bound_uniform_sigma01` to include `σ = 1`
(closed right endpoint) and uses the resulting bound, together with
`Complex.digamma_vertical_log_bound`, to prove that the integrand of the
inverse Mellin transform of the arch factor at `σ = 2`,

  `archFactor(s) / (s · (s + 1))`,

is integrable along the vertical line `Re s = 2`.  This is the analytic
input the inverse-Mellin agent needs to make `mellinInv 2 _` well-defined
in the Bochner sense.

## Main results

* `digamma_log_bound_uniform_sigma01_closed_right` —
  `∃ C, ∀ σ ∈ (0, 1], ∀ τ : ℝ, |τ| ≥ 1, ‖ψ(σ + iτ)‖ ≤ C · log(1+|τ|)`.

* `archFactor_div_quadratic_verticalIntegrable_at_two` —
  the function `T ↦ ((2+iT)·(3+iT))⁻¹ · archFactor(2+iT)` is `Integrable` on `ℝ`.

The second result feeds the inverse-Mellin step at `σ = 2`.

## Strategy

* `archFactor(2+iT) = Γℝ'/Γℝ(2+iT) + Γℝ'/Γℝ(-1-iT)`.
* For each piece, write `Γℝ'/Γℝ(s) = -(log π)/2 + (1/2)·ψ(s/2)`
  via `ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form`.
* Bound the digamma values via `Complex.digamma_vertical_log_bound`,
  reducing the negative-Re case via `Complex.digamma_apply_add_one`
  twice (shift `-1/2 - iT/2` up to `3/2 - iT/2`).
* Combine to get `‖archFactor(2+iT)‖ ≤ K · log(2 + |T|)` for `|T| ≥ 2`,
  extended by continuity to all `T`.
* Divide by `s · (s+1)` to get `O(log(2+|T|) / (1+T²)) = O((1+T²)^(-3/4))`,
  which is integrable on `ℝ` via
  `MeasureTheory.integrable_rpow_neg_one_add_norm_sq`.
-/

open Complex MeasureTheory Filter Asymptotics

noncomputable section

namespace ArchFactorVerticalIntegrable

/-! ## Phase 1: σ = 1 closure of the σ-uniform digamma bound -/

/-- **σ-uniform digamma log bound, extended to the closed right endpoint `σ = 1`.**

Combining `digamma_log_bound_uniform_sigma01` (for `σ < 1`, uniform constant)
with the single-`σ` bound `Complex.digamma_vertical_log_bound 1` (for `σ = 1`
itself) yields a uniform constant on the closed interval `(0, 1]`. -/
theorem digamma_log_bound_uniform_sigma01_closed_right :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 → ∀ τ : ℝ, 1 ≤ |τ| →
      ‖deriv Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ C * Real.log (1 + |τ|) := by
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := ZD.UniformGammaR.digamma_log_bound_uniform_sigma01
  obtain ⟨C₂, hC₂_pos, hC₂_bd⟩ := Complex.digamma_vertical_log_bound 1 (by norm_num)
  refine ⟨max C₁ C₂, le_trans hC₁_pos.le (le_max_left _ _), ?_⟩
  intro σ hσ τ hτ
  have h_log_nn : 0 ≤ Real.log (1 + |τ|) :=
    Real.log_nonneg (by linarith [abs_nonneg τ])
  rcases lt_or_eq_of_le hσ.2 with hσlt | hσeq
  · refine (hC₁_bd σ ⟨hσ.1, hσlt⟩ τ hτ).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_log_nn
  · subst hσeq
    refine (hC₂_bd τ hτ).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) h_log_nn

/-! ## Phase 2: continuity of the archimedean factor along `Re s = 2` -/

/-- `Gammaℝ` is analytic at any point where it is nonzero. -/
private lemma analyticAt_Gammaℝ_of_ne_zero {s : ℂ} (hs : s.Gammaℝ ≠ 0) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have h_diff : DifferentiableAt ℂ Complex.Gammaℝ s :=
    ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero hs
  have h_cont : ContinuousAt Complex.Gammaℝ s := h_diff.continuousAt
  have h_ev_ne : ∀ᶠ z in nhds s, z.Gammaℝ ≠ 0 := h_cont.eventually_ne hs
  rcases Metric.eventually_nhds_iff.mp h_ev_ne with ⟨ε, hε_pos, hε⟩
  have h_diff_on : DifferentiableOn ℂ Complex.Gammaℝ (Metric.ball s ε) := by
    intro z hz
    exact (ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero
      (hε hz)).differentiableWithinAt
  exact h_diff_on.analyticAt (Metric.ball_mem_nhds s hε_pos)

/-- The point `1 - (2 + iT) = -1 - iT` is never a non-positive even integer,
hence `Gammaℝ` is nonzero there. -/
private lemma Gammaℝ_one_sub_ne_zero (T : ℝ) :
    ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  have him := congrArg Complex.im hn
  simp at him
  subst him
  have hre := congrArg Complex.re hn
  simp at hre
  have h1 : 2 * (n : ℝ) = 1 := by linarith
  have h2 : (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [h2] at h1
  have : 2 * n = 1 := by exact_mod_cast h1
  omega

/-- Continuity of the affine map `T ↦ 2 + iT`. -/
private lemma continuous_two_add_T_I :
    Continuous (fun T : ℝ => ((2 : ℂ) + (T : ℂ) * Complex.I)) := by
  refine continuous_const.add ?_
  exact Complex.continuous_ofReal.mul continuous_const

/-- Continuity of the affine map `T ↦ 1 - (2 + iT)`. -/
private lemma continuous_one_sub_two_add_T_I :
    Continuous (fun T : ℝ => (1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)) :=
  continuous_const.sub continuous_two_add_T_I

/-- `T ↦ Γℝ(2 + iT)` is continuous (analytic locus). -/
private lemma continuous_Gammaℝ_at_two :
    Continuous (fun T : ℝ => ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ) := by
  refine continuous_iff_continuousAt.mpr (fun T₀ => ?_)
  have hs_re_pos : 0 < ((2 : ℂ) + (T₀ : ℂ) * I).re := by simp
  have h_ne : ((2 : ℂ) + (T₀ : ℂ) * I).Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  have h_cont_C : ContinuousAt Complex.Gammaℝ ((2 : ℂ) + (T₀ : ℂ) * I) :=
    (ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero h_ne).continuousAt
  exact ContinuousAt.comp (x := T₀) h_cont_C continuous_two_add_T_I.continuousAt

/-- `T ↦ Γℝ(1 - (2 + iT))` is continuous (analytic locus). -/
private lemma continuous_Gammaℝ_one_sub_at_two :
    Continuous (fun T : ℝ => ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ) := by
  refine continuous_iff_continuousAt.mpr (fun T₀ => ?_)
  have h_ne : ((1 : ℂ) - ((2 : ℂ) + (T₀ : ℂ) * I)).Gammaℝ ≠ 0 :=
    Gammaℝ_one_sub_ne_zero T₀
  have h_cont_C : ContinuousAt Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T₀ : ℂ) * I)) :=
    (ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero h_ne).continuousAt
  exact ContinuousAt.comp (x := T₀) h_cont_C continuous_one_sub_two_add_T_I.continuousAt

/-- `T ↦ Γℝ'(2 + iT)` is continuous via analyticity of `Γℝ`. -/
private lemma continuous_deriv_Gammaℝ_at_two :
    Continuous (fun T : ℝ => deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun T₀ => ?_)
  have hs_re_pos : 0 < ((2 : ℂ) + (T₀ : ℂ) * I).re := by simp
  have h_ne : ((2 : ℂ) + (T₀ : ℂ) * I).Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  have h_ana : AnalyticAt ℂ Complex.Gammaℝ ((2 : ℂ) + (T₀ : ℂ) * I) :=
    analyticAt_Gammaℝ_of_ne_zero h_ne
  have h_deriv_cont : ContinuousAt (deriv Complex.Gammaℝ) ((2 : ℂ) + (T₀ : ℂ) * I) :=
    h_ana.deriv.continuousAt
  exact ContinuousAt.comp (x := T₀) h_deriv_cont continuous_two_add_T_I.continuousAt

/-- `T ↦ Γℝ'(1 - (2 + iT))` is continuous via analyticity of `Γℝ`. -/
private lemma continuous_deriv_Gammaℝ_one_sub_at_two :
    Continuous (fun T : ℝ =>
      deriv Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I))) := by
  refine continuous_iff_continuousAt.mpr (fun T₀ => ?_)
  have h_ne : ((1 : ℂ) - ((2 : ℂ) + (T₀ : ℂ) * I)).Gammaℝ ≠ 0 :=
    Gammaℝ_one_sub_ne_zero T₀
  have h_ana : AnalyticAt ℂ Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T₀ : ℂ) * I)) :=
    analyticAt_Gammaℝ_of_ne_zero h_ne
  have h_deriv_cont : ContinuousAt (deriv Complex.Gammaℝ)
      ((1 : ℂ) - ((2 : ℂ) + (T₀ : ℂ) * I)) :=
    h_ana.deriv.continuousAt
  exact ContinuousAt.comp (x := T₀) h_deriv_cont continuous_one_sub_two_add_T_I.continuousAt

/-- The integrand of the inverse Mellin transform of `archFactor / (s · (s+1))`
along `Re s = 2`, expressed as a function of the imaginary coordinate `T`. -/
private def integrand (T : ℝ) : ℂ :=
  ((2 : ℂ) + (T : ℂ) * Complex.I)⁻¹ * (((2 : ℂ) + (T : ℂ) * Complex.I) + 1)⁻¹ *
    (deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
        ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
        (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ)

/-- The integrand is continuous on `ℝ`. -/
private lemma continuous_integrand : Continuous integrand := by
  unfold integrand
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · refine continuous_two_add_T_I.inv₀ (fun T => ?_)
    intro h
    have := congrArg Complex.re h
    simp at this
  · have h_cont : Continuous (fun T : ℝ => ((2 : ℂ) + (T : ℂ) * Complex.I) + 1) :=
      continuous_two_add_T_I.add continuous_const
    refine h_cont.inv₀ (fun T => ?_)
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  · refine Continuous.add ?_ ?_
    · refine continuous_deriv_Gammaℝ_at_two.div continuous_Gammaℝ_at_two ?_
      intro T
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp
    · refine continuous_deriv_Gammaℝ_one_sub_at_two.div
        continuous_Gammaℝ_one_sub_at_two ?_
      intro T
      exact Gammaℝ_one_sub_ne_zero T

/-! ## Phase 3: tail bound on `archFactor(2 + iT)` -/

/-- For `|T| ≥ 2`, the first arch term obeys
`‖Γℝ'/Γℝ(2+iT)‖ ≤ A · log(1+|T|) + B`. -/
private lemma archFactor_left_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ T : ℝ, 2 ≤ |T| →
      ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
        ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ‖ ≤ A * Real.log (1 + |T|) + B := by
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ := Complex.digamma_vertical_log_bound 1 (by norm_num)
  have h_logπ_nn : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Cd / 2, Real.log Real.pi / 2, by positivity, by linarith, ?_⟩
  intro T hT
  set s : ℂ := (2 : ℂ) + (T : ℂ) * I with hs_def
  have hs_re_pos : 0 < s.re := by simp [hs_def]
  have hs_GammaR_ne : s.Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  have h_ne_2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
    intro n h
    have hre := congrArg Complex.re h
    simp [hs_def] at hre
    have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    linarith
  have h_form := ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form s hs_GammaR_ne h_ne_2n
  rw [h_form]
  have h_logπ_cast : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) := by
    rw [Complex.ofReal_log Real.pi_pos.le]
  rw [h_logπ_cast]
  have hs_half : s / 2 = ((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I := by
    rw [hs_def]; push_cast; ring
  rw [hs_half]
  have hT2_abs : 1 ≤ |T / 2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have h_psi_bd := hCd_bd (T/2) hT2_abs
  have h_log_T2_le_log_T : Real.log (1 + |T / 2|) ≤ Real.log (1 + |T|) := by
    apply Real.log_le_log (by linarith [abs_nonneg (T/2)])
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [abs_nonneg T]
  calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 +
          (1 / 2 : ℂ) *
            (deriv Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I))‖
      ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ +
          ‖(1 / 2 : ℂ) *
            (deriv Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I))‖ := norm_add_le _ _
    _ = Real.log Real.pi / 2 +
          (1/2) * ‖deriv Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((1 : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I)‖ := by
        rw [norm_mul, norm_div, norm_neg]
        congr 1
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_logπ_nn,
              show ‖(2 : ℂ)‖ = 2 from by norm_num]
        · rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
          norm_num
    _ ≤ Real.log Real.pi / 2 + (1/2) * (Cd * Real.log (1 + |T/2|)) := by
        have hh : (0:ℝ) ≤ 1/2 := by norm_num
        nlinarith [h_psi_bd]
    _ ≤ Real.log Real.pi / 2 + (1/2) * (Cd * Real.log (1 + |T|)) := by
        have hCd_nn : 0 ≤ Cd := hCd_pos.le
        have : (1/2 : ℝ) * (Cd * Real.log (1 + |T/2|)) ≤
            (1/2) * (Cd * Real.log (1 + |T|)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
          exact mul_le_mul_of_nonneg_left h_log_T2_le_log_T hCd_nn
        linarith
    _ = Cd / 2 * Real.log (1 + |T|) + Real.log Real.pi / 2 := by ring

/-- For `|T| ≥ 2`, the second arch term obeys
`‖Γℝ'/Γℝ(1−(2+iT))‖ ≤ A · log(1+|T|) + B`.

Reduces via `Complex.digamma_apply_add_one` to the digamma at `1/2 − iT/2`,
which has `Re = 1/2 > 0`. -/
private lemma archFactor_right_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ T : ℝ, 2 ≤ |T| →
      ‖deriv Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
        ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖ ≤
        A * Real.log (1 + |T|) + B := by
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ := Complex.digamma_vertical_log_bound (1/2) (by norm_num)
  have h_logπ_nn : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Cd / 2, Real.log Real.pi / 2 + 1, by positivity, by linarith, ?_⟩
  intro T hT
  set s : ℂ := (1 : ℂ) - ((2 : ℂ) + (T : ℂ) * I) with hs_def
  have hs_GammaR_ne : s.Gammaℝ ≠ 0 := by
    rw [hs_def]
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    rcases h with ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp at him
    subst him
    have hre := congrArg Complex.re hn
    simp at hre
    have h2 : (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
    have h1 : 2 * (n : ℝ) = 1 := by linarith
    rw [h2] at h1
    have : 2 * n = 1 := by exact_mod_cast h1
    omega
  have h_ne_2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
    intro n h
    apply hs_GammaR_ne
    rw [Complex.Gammaℝ_eq_zero_iff]; exact ⟨n, h⟩
  have h_form := ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form s hs_GammaR_ne h_ne_2n
  rw [h_form]
  have h_logπ_cast : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) := by
    rw [Complex.ofReal_log Real.pi_pos.le]
  rw [h_logπ_cast]
  have hs_half : s / 2 = ((-1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I := by
    rw [hs_def]; push_cast; ring
  rw [hs_half]
  set z : ℂ := ((-1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I with hz_def
  have hT_ne_zero : T ≠ 0 := by intro h; rw [h] at hT; norm_num at hT
  have h_z_ne_neg_nat : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    rw [hz_def] at h
    have him := congrArg Complex.im h
    simp at him
    have : T = 0 := by linarith
    exact hT_ne_zero this
  have h_zp1 : z + 1 = ((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I := by
    rw [hz_def]; push_cast; ring
  have h_Gz_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero h_z_ne_neg_nat
  have h_dG_z : deriv Complex.Gamma z / Complex.Gamma z = Complex.digamma z := by
    rw [Complex.digamma_def, logDeriv_apply]
  rw [h_dG_z]
  have hh := Complex.digamma_apply_add_one z h_z_ne_neg_nat
  have h_psi_z : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by
    have : Complex.digamma (z + 1) - z⁻¹ = Complex.digamma z := by rw [hh]; ring
    exact this.symm
  rw [h_psi_z, h_zp1]
  -- digamma at 1/2 + (-T/2) I = deriv Gamma / Gamma there
  have h_dG_zp1 : Complex.digamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) =
      deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
      Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) := by
    rw [Complex.digamma_def, logDeriv_apply]
  rw [h_dG_zp1]
  -- Bound for the digamma at 1/2 + (-T/2) I
  have hT2_abs : 1 ≤ |-T/2| := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have h_psi_bd_raw := hCd_bd (-T/2) hT2_abs
  have h_psi_bd : ‖deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
      Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I)‖ ≤
      Cd * Real.log (1 + |-T/2|) := h_psi_bd_raw
  have h_log_bd : Real.log (1 + |-T/2|) ≤ Real.log (1 + |T|) := by
    apply Real.log_le_log (by linarith [abs_nonneg (-T/2)])
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have : |T| / 2 ≤ |T| := by linarith [abs_nonneg T]
    linarith
  -- ‖z⁻¹‖ ≤ 2
  have h_z_inv_norm : ‖z⁻¹‖ ≤ 2 := by
    rw [norm_inv, hz_def, Complex.norm_def, Complex.normSq_add_mul_I]
    rw [show ((-1/2 : ℝ)^2 + (-T/2)^2) = (1/4 + T^2/4 : ℝ) by ring]
    have h_sqrt_pos : 0 < Real.sqrt (1/4 + T^2/4) := Real.sqrt_pos.mpr (by positivity)
    rw [inv_le_iff_one_le_mul₀ h_sqrt_pos]
    have h_le : Real.sqrt (1/4) ≤ Real.sqrt (1/4 + T^2/4) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg T])
    have h_sqrt_quarter : Real.sqrt (1/4) = 1/2 := by
      rw [show (1/4 : ℝ) = (1/2)^2 from by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h_sqrt_quarter] at h_le
    linarith
  -- Combine: ‖-log π/2 + (1/2)(ψ(z+1) - z⁻¹)‖ ≤ log π/2 + (1/2)·Cd·log(1+|T|) + (1/2)·2
  have h_logπ_norm :
      ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, show ‖(2 : ℂ)‖ = 2 from by norm_num,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_logπ_nn]
  have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    norm_num
  calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 +
          (1/2 : ℂ) *
            (deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) - z⁻¹)‖
      ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ +
          ‖(1/2 : ℂ) *
            (deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) - z⁻¹)‖ :=
              norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 +
          (1/2) * (‖deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I)‖ + ‖z⁻¹‖) := by
        rw [h_logπ_norm]
        gcongr
        rw [norm_mul, h_half_norm]
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.log Real.pi / 2 +
          (1/2) * (Cd * Real.log (1 + |T|) + 2) := by
        have hCd_nn : 0 ≤ Cd := hCd_pos.le
        have h1 : ‖deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I)‖
            ≤ Cd * Real.log (1 + |T|) :=
          h_psi_bd.trans (mul_le_mul_of_nonneg_left h_log_bd hCd_nn)
        have h2 : ‖z⁻¹‖ ≤ 2 := h_z_inv_norm
        gcongr
    _ = Cd / 2 * Real.log (1 + |T|) + (Real.log Real.pi / 2 + 1) := by ring

/-! ## Phase 4: global log bound on `archFactor(2 + iT)` -/

/-- `‖archFactor(2 + iT)‖ ≤ K · log(2 + |T|)` for all `T : ℝ`. The
small-`T` behaviour is handled via continuity + compactness of `[-2, 2]`,
and the tail `|T| ≥ 2` via `archFactor_left_bound` + `archFactor_right_bound`. -/
private lemma archFactor_global_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
      ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
          ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
        deriv Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
          ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖
        ≤ K * Real.log (2 + |T|) := by
  obtain ⟨A₁, B₁, hA₁_nn, hB₁_nn, h_left⟩ := archFactor_left_bound
  obtain ⟨A₂, B₂, hA₂_nn, hB₂_nn, h_right⟩ := archFactor_right_bound
  -- Continuous function and compact set [-2, 2] yield a bound on the small-|T| part.
  set f : ℝ → ℂ := fun T : ℝ =>
    deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
      ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
    deriv Complex.Gammaℝ ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
      ((1 : ℂ) - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ with hf_def
  have hf_cont : Continuous f := by
    refine Continuous.add ?_ ?_
    · refine continuous_deriv_Gammaℝ_at_two.div continuous_Gammaℝ_at_two ?_
      intro T; apply Complex.Gammaℝ_ne_zero_of_re_pos; simp
    · refine continuous_deriv_Gammaℝ_one_sub_at_two.div
        continuous_Gammaℝ_one_sub_at_two ?_
      intro T; exact Gammaℝ_one_sub_ne_zero T
  -- M₀ = sup of ‖f‖ on [-2, 2]
  have h_compact : IsCompact (Set.Icc (-2 : ℝ) 2) := isCompact_Icc
  have h_norm_cont : ContinuousOn (fun T : ℝ => ‖f T‖) (Set.Icc (-2 : ℝ) 2) :=
    (continuous_norm.comp hf_cont).continuousOn
  have h_nonempty : (Set.Icc (-2 : ℝ) 2).Nonempty := ⟨0, by simp⟩
  obtain ⟨T₀, hT₀, h_max⟩ :=
    h_compact.exists_isMaxOn h_nonempty h_norm_cont
  set M₀ := ‖f T₀‖ with hM₀_def
  have hM₀_nn : 0 ≤ M₀ := norm_nonneg _
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- K = (A₁ + A₂) + (M₀ + B₁ + B₂) / log 2
  set K : ℝ := (A₁ + A₂) + (M₀ + B₁ + B₂) / Real.log 2 with hK_def
  have hK_nn : 0 ≤ K := by
    refine add_nonneg (by linarith) (div_nonneg (by linarith) h_log2_pos.le)
  refine ⟨K, hK_nn, ?_⟩
  intro T
  have h_log_2T_pos : 0 < Real.log (2 + |T|) := by
    apply Real.log_pos; linarith [abs_nonneg T]
  have h_log_2T_ge_log2 : Real.log 2 ≤ Real.log (2 + |T|) := by
    apply Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  -- (B₁ + B₂) ≤ (M₀ + B₁ + B₂)/log 2 · log(2+|T|)
  have h_const_bd : (B₁ + B₂) ≤ (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) := by
    have h_factor_nn : 0 ≤ (M₀ + B₁ + B₂) / Real.log 2 :=
      div_nonneg (by linarith) h_log2_pos.le
    calc (B₁ + B₂) ≤ M₀ + B₁ + B₂ := by linarith
      _ = (M₀ + B₁ + B₂) / Real.log 2 * Real.log 2 := by
          rw [div_mul_cancel₀ _ h_log2_pos.ne']
      _ ≤ (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) :=
          mul_le_mul_of_nonneg_left h_log_2T_ge_log2 h_factor_nn
  -- M₀ ≤ (M₀ + B₁ + B₂)/log 2 · log(2+|T|)
  have h_M0_bd : M₀ ≤ (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) := by
    have h_factor_nn : 0 ≤ (M₀ + B₁ + B₂) / Real.log 2 :=
      div_nonneg (by linarith) h_log2_pos.le
    calc M₀ ≤ M₀ + B₁ + B₂ := by linarith
      _ = (M₀ + B₁ + B₂) / Real.log 2 * Real.log 2 := by
          rw [div_mul_cancel₀ _ h_log2_pos.ne']
      _ ≤ (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) :=
          mul_le_mul_of_nonneg_left h_log_2T_ge_log2 h_factor_nn
  by_cases hT : 2 ≤ |T|
  · -- Tail case
    have hf_split : ‖f T‖ ≤ (A₁ * Real.log (1 + |T|) + B₁) +
        (A₂ * Real.log (1 + |T|) + B₂) :=
      (norm_add_le _ _).trans (add_le_add (h_left T hT) (h_right T hT))
    have h_log_le : Real.log (1 + |T|) ≤ Real.log (2 + |T|) := by
      apply Real.log_le_log (by linarith [abs_nonneg T]); linarith
    have h_A_log : (A₁ + A₂) * Real.log (1 + |T|) ≤
        (A₁ + A₂) * Real.log (2 + |T|) :=
      mul_le_mul_of_nonneg_left h_log_le (by linarith)
    calc ‖f T‖
        ≤ (A₁ + A₂) * Real.log (1 + |T|) + (B₁ + B₂) := by linarith
      _ ≤ (A₁ + A₂) * Real.log (2 + |T|) +
            (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) := by linarith
      _ = K * Real.log (2 + |T|) := by rw [hK_def]; ring
  · -- Small case: |T| < 2
    have hT : |T| < 2 := lt_of_not_ge hT
    have h_T_in : T ∈ Set.Icc (-2 : ℝ) 2 := by
      have := abs_le.mp (le_of_lt hT)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hf_T_le : ‖f T‖ ≤ M₀ := h_max h_T_in
    have h_extra_nn : 0 ≤ (A₁ + A₂) * Real.log (2 + |T|) :=
      mul_nonneg (by linarith) h_log_2T_pos.le
    calc ‖f T‖
        ≤ M₀ := hf_T_le
      _ ≤ (M₀ + B₁ + B₂) / Real.log 2 * Real.log (2 + |T|) := h_M0_bd
      _ ≤ K * Real.log (2 + |T|) := by rw [hK_def]; nlinarith

/-! ## Phase 5: integrability of the inverse-Mellin integrand at `σ = 2` -/

/-- For all `T : ℝ`, `Real.log (2 + |T|) ≤ 4 · (1 + T²)^(1/4)`.

This is the global "log dominated by `(1+T²)^(1/4)`" inequality used
to push the bound on `archFactor(2+iT)` into a globally integrable
upper bound `K · (1+T²)^(-3/4)`. -/
private lemma log_le_quartic_root (T : ℝ) :
    Real.log (2 + |T|) ≤ 4 * (1 + T^2)^(1/4 : ℝ) := by
  have h_T_abs_nn : 0 ≤ |T| := abs_nonneg T
  -- Step 1: log(2+|T|) ≤ 2 √(2+|T|) (using log x ≤ 2(√x - 1))
  have h_log_le_sqrt : Real.log (2 + |T|) ≤ 2 * Real.sqrt (2 + |T|) := by
    have h_2T_ge_one : 1 ≤ 2 + |T| := by linarith
    have h_sqrt_pos : 0 < Real.sqrt (2 + |T|) := Real.sqrt_pos.mpr (by linarith)
    have h_log_sqrt :
        Real.log (2 + |T|) = 2 * Real.log (Real.sqrt (2 + |T|)) := by
      have hsq : (2 + |T|) = (Real.sqrt (2 + |T|))^2 := by
        rw [sq, Real.mul_self_sqrt (by linarith)]
      conv_lhs => rw [hsq]
      rw [Real.log_pow]; push_cast; ring
    rw [h_log_sqrt]
    have h1 : Real.log (Real.sqrt (2 + |T|)) ≤ Real.sqrt (2 + |T|) - 1 :=
      Real.log_le_sub_one_of_pos h_sqrt_pos
    linarith
  -- Step 2: √(2+|T|) ≤ 2 (1+T²)^(1/4)
  have h_sqrt_le : Real.sqrt (2 + |T|) ≤ 2 * (1 + T^2)^(1/4 : ℝ) := by
    have h_rhs_nn : 0 ≤ 2 * (1 + T^2)^(1/4 : ℝ) := by positivity
    rw [Real.sqrt_le_left h_rhs_nn]
    have h_sq : (2 * (1 + T^2)^(1/4 : ℝ))^2 = 4 * Real.sqrt (1 + T^2) := by
      rw [mul_pow]
      rw [← Real.rpow_natCast ((1+T^2)^(1/4 : ℝ)) 2,
          ← Real.rpow_mul (by positivity)]
      rw [show ((1/4 : ℝ) * (2 : ℕ)) = (1/2 : ℝ) by norm_num,
          ← Real.sqrt_eq_rpow]
      norm_num
    rw [h_sq]
    have h_T2_nn : (0:ℝ) ≤ 1 + T^2 := by positivity
    have h_sqrt_T : (2 + |T|) / 4 ≤ Real.sqrt (1 + T^2) := by
      rw [Real.le_sqrt (by linarith) h_T2_nn]
      have hT2 : T^2 = |T|^2 := (sq_abs T).symm
      nlinarith [sq_nonneg (|T| - 2), abs_nonneg T]
    linarith
  linarith

/-- The integrand of the inverse Mellin transform of
`archFactor / (s · (s+1))` at `σ = 2` is integrable along the vertical
line `Re s = 2`.

This is the analytic input downstream callers need to make sense of
the inverse-Mellin contour integral as a Bochner integral. -/
theorem archFactor_div_quadratic_verticalIntegrable_at_two :
    Integrable (fun T : ℝ =>
      ((2 : ℂ) + (T : ℂ) * Complex.I)⁻¹ *
        (((2 : ℂ) + (T : ℂ) * Complex.I) + 1)⁻¹ *
        (deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
            ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
            (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ)) volume := by
  obtain ⟨K, hK_nn, hK_bd⟩ := archFactor_global_log_bound
  -- Bounding function: g(T) = 4 K · (1 + T²)^(-3/4)
  set g : ℝ → ℝ := fun T => 4 * K * (1 + T^2)^(-(3/4 : ℝ)) with hg_def
  have hg_int : Integrable g volume := by
    refine Integrable.const_mul ?_ (4 * K)
    have h : Integrable (fun x : ℝ => (1 + ‖x‖^2)^(-(3/2 : ℝ)/2))
        (volume : Measure ℝ) :=
      integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 3/2)
        (by simp; norm_num)
    have h_eq : (fun T : ℝ => (1 + T^2)^(-(3/4 : ℝ))) =
                (fun T : ℝ => (1 + ‖T‖^2)^(-(3/2 : ℝ)/2)) := by
      funext T; simp [Real.norm_eq_abs, sq_abs]; ring_nf
    rw [h_eq]; exact h
  refine Integrable.mono' hg_int ?_ ?_
  · -- AEStronglyMeasurable: from continuity
    exact continuous_integrand.aestronglyMeasurable
  · -- Pointwise bound: ‖integrand T‖ ≤ g T
    refine Filter.Eventually.of_forall (fun T => ?_)
    -- ‖integrand T‖ = ‖(2+iT)⁻¹‖ · ‖(2+iT+1)⁻¹‖ · ‖archSum‖
    rw [norm_mul, norm_mul, norm_inv, norm_inv]
    -- |2+iT| = sqrt(4+T²), |2+iT+1| = |3+iT| = sqrt(9+T²)
    have h_norm_2iT : ‖((2 : ℂ) + (T : ℂ) * Complex.I)‖ = Real.sqrt (4 + T^2) := by
      rw [show ((2 : ℂ) + (T : ℂ) * Complex.I) = ((2 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I from by push_cast; ring,
          Complex.norm_def, Complex.normSq_add_mul_I]
      norm_num
    have h_norm_3iT : ‖((2 : ℂ) + (T : ℂ) * Complex.I) + 1‖ = Real.sqrt (9 + T^2) := by
      rw [show (((2 : ℂ) + (T : ℂ) * Complex.I) + 1) =
            ((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I from by push_cast; ring,
          Complex.norm_def, Complex.normSq_add_mul_I]
      norm_num
    rw [h_norm_2iT, h_norm_3iT]
    -- ‖archSum‖ ≤ K log(2+|T|)
    have h_arch_bd := hK_bd T
    -- (1+T²)^(-3/4) = ((1+T²)^(3/4))⁻¹
    -- g T = 4K · (1+T²)^(-3/4)
    -- want: (sqrt(4+T²))⁻¹ * (sqrt(9+T²))⁻¹ * ‖archSum‖ ≤ 4K · (1+T²)^(-3/4)
    -- Equivalently: ‖archSum‖ ≤ 4K · sqrt(4+T²) · sqrt(9+T²) · (1+T²)^(-3/4)
    -- We have ‖archSum‖ ≤ K · log(2+|T|) ≤ K · 4 · (1+T²)^(1/4)
    -- And sqrt(4+T²) · sqrt(9+T²) ≥ ?
    -- It's enough to show:
    --   (sqrt(4+T²))⁻¹ · (sqrt(9+T²))⁻¹ · K log(2+|T|) ≤ 4K · (1+T²)^(-3/4)
    -- Use: sqrt(4+T²) ≥ sqrt(1+T²), sqrt(9+T²) ≥ sqrt(1+T²)
    -- So 1/(sqrt(4+T²)·sqrt(9+T²)) ≤ 1/(1+T²)
    -- And log(2+|T|) ≤ 4 (1+T²)^(1/4)
    -- Together: K log(2+|T|)/(sqrt(4+T²)·sqrt(9+T²)) ≤ K · 4 (1+T²)^(1/4) · (1+T²)⁻¹
    --   = 4K · (1+T²)^(-3/4)
    have h_sqrt4 : Real.sqrt (1 + T^2) ≤ Real.sqrt (4 + T^2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h_sqrt9 : Real.sqrt (1 + T^2) ≤ Real.sqrt (9 + T^2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h_sqrt1_pos : 0 < Real.sqrt (1 + T^2) := Real.sqrt_pos.mpr (by positivity)
    have h_sqrt4_pos : 0 < Real.sqrt (4 + T^2) := Real.sqrt_pos.mpr (by positivity)
    have h_sqrt9_pos : 0 < Real.sqrt (9 + T^2) := Real.sqrt_pos.mpr (by positivity)
    have h_inv_4 : (Real.sqrt (4 + T^2))⁻¹ ≤ (Real.sqrt (1 + T^2))⁻¹ :=
      inv_anti₀ h_sqrt1_pos h_sqrt4
    have h_inv_9 : (Real.sqrt (9 + T^2))⁻¹ ≤ (Real.sqrt (1 + T^2))⁻¹ :=
      inv_anti₀ h_sqrt1_pos h_sqrt9
    have h_log_bd := log_le_quartic_root T
    -- ‖archSum‖ ≤ K · log(2+|T|) ≤ K · 4 (1+T²)^(1/4)
    have h_arch_combined : ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
          ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
          (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖ ≤
          K * (4 * (1 + T^2)^(1/4 : ℝ)) :=
      h_arch_bd.trans (mul_le_mul_of_nonneg_left h_log_bd hK_nn)
    -- (sqrt(4+T²))⁻¹ · (sqrt(9+T²))⁻¹ ≤ (1+T²)⁻¹
    have h_inv_prod : (Real.sqrt (4 + T^2))⁻¹ * (Real.sqrt (9 + T^2))⁻¹ ≤
        (1 + T^2)⁻¹ := by
      have h_inv_prod_le : (Real.sqrt (4 + T^2))⁻¹ * (Real.sqrt (9 + T^2))⁻¹
          ≤ (Real.sqrt (1 + T^2))⁻¹ * (Real.sqrt (1 + T^2))⁻¹ := by
        apply mul_le_mul h_inv_4 h_inv_9 (le_of_lt (inv_pos.mpr h_sqrt9_pos))
        exact (inv_pos.mpr h_sqrt1_pos).le
      have h_sq_inv : (Real.sqrt (1 + T^2))⁻¹ * (Real.sqrt (1 + T^2))⁻¹ =
          (1 + T^2)⁻¹ := by
        rw [← mul_inv, ← sq, Real.sq_sqrt (by positivity)]
      rw [h_sq_inv] at h_inv_prod_le
      exact h_inv_prod_le
    -- (1+T²)⁻¹ · 4 (1+T²)^(1/4) = 4 (1+T²)^(-3/4)
    have h_pow_eq : (1 + T^2)⁻¹ * (4 * (1 + T^2)^(1/4 : ℝ)) =
        4 * (1 + T^2)^(-(3/4 : ℝ)) := by
      have h_pos : (0:ℝ) < 1 + T^2 := by positivity
      rw [show ((1 + T^2)⁻¹ : ℝ) = (1 + T^2)^(-(1 : ℝ)) from
            (Real.rpow_neg_one (1 + T^2)).symm]
      rw [show (1 + T^2)^(-(1 : ℝ)) * (4 * (1 + T^2)^(1/4 : ℝ)) =
            4 * ((1 + T^2)^(-(1 : ℝ)) * (1 + T^2)^(1/4 : ℝ)) by ring]
      rw [← Real.rpow_add h_pos]
      norm_num
    -- Combine
    have h_arch_nn : 0 ≤ ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
          ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
          (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖ := norm_nonneg _
    have h_inv_prod_nn : 0 ≤ (Real.sqrt (4 + T^2))⁻¹ * (Real.sqrt (9 + T^2))⁻¹ := by
      have := inv_pos.mpr h_sqrt4_pos
      have := inv_pos.mpr h_sqrt9_pos
      positivity
    -- g T = 4K · (1+T²)^(-3/4)
    show (Real.sqrt (4 + T^2))⁻¹ * (Real.sqrt (9 + T^2))⁻¹ *
        ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
          ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
          (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖ ≤ g T
    rw [hg_def]
    calc (Real.sqrt (4 + T^2))⁻¹ * (Real.sqrt (9 + T^2))⁻¹ *
            ‖deriv Complex.Gammaℝ ((2 : ℂ) + (T : ℂ) * Complex.I) /
                ((2 : ℂ) + (T : ℂ) * Complex.I).Gammaℝ +
              deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)) /
                (1 - ((2 : ℂ) + (T : ℂ) * Complex.I)).Gammaℝ‖
        ≤ (1 + T^2)⁻¹ *
            (K * (4 * (1 + T^2)^(1/4 : ℝ))) :=
          mul_le_mul h_inv_prod h_arch_combined h_arch_nn (by positivity)
      _ = K * ((1 + T^2)⁻¹ * (4 * (1 + T^2)^(1/4 : ℝ))) := by ring
      _ = K * (4 * (1 + T^2)^(-(3/4 : ℝ))) := by rw [h_pow_eq]
      _ = 4 * K * (1 + T^2)^(-(3/4 : ℝ)) := by ring

end ArchFactorVerticalIntegrable

end
