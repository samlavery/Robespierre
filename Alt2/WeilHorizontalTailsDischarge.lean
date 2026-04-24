import Mathlib
import RequestProject.WeilFinalAssembly
import RequestProject.WeilLogDerivLeftSlab
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilPairIBPQuartic
import RequestProject.WeilPairTestMellinExtend
import RequestProject.CriticalStripLandau
import RequestProject.WeilHorizontalDecay
import RequestProject.WeilContour

set_option maxHeartbeats 0

/-!
# Discharge of `weilHorizontalTails_vanish_target β (-1) 2` — PARTIAL

This file provides the **Mellin-side infrastructure** for the discharge.
The full top-level theorem is NOT yet proved; the remaining blocker is
a uniform polynomial bound on `ζ'/ζ(σ+iT)` for `σ ∈ [-1, 2]` at good
heights, missing sub-intervals `[-1, -3/4]`, `[-1/2, 0]`, `[1, 3/2]`
(and two endpoint slices).

## What is proved here

1. `pairDeriv4Mellin_differentiableAt_re_pos` — analyticity on `Re s > 0`.
2. `pairTestMellin_eq_ibp4_on_upper_strip` — analytic continuation of the
   IBP×4 identity from `Re s > 0` to the strip `{-4 < Re s, 1 ≤ Im s}`.
3. `pairTestMellin_quartic_bound_extended` — uniform
   `‖pairTestMellin β (σ+iT)‖ ≤ C/T^4` for `σ ∈ [-1, 2]`, `T ≥ 2`.
-/

noncomputable section

open Complex Set Filter MeasureTheory Real Asymptotics

namespace ZD
namespace WeilPositivity
namespace HorizontalTailsDischarge

open Contour FinalAssembly

/-- `pairDeriv4Mellin β` is differentiable at every `s` with `Re s > 0`. -/
theorem pairDeriv4Mellin_differentiableAt_re_pos
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (pairDeriv4Mellin β) s := by
  unfold pairDeriv4Mellin
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2) ?_ ?_ ?_ hs
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 4
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  · have h := pair_cosh_gauss_test_deriv4_isBigO_exp_neg_half_atTop β
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) =
        (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]; exact h
  · exact pair_cosh_gauss_test_deriv4_isBigO_one_nhds_zero β

#print axioms pairDeriv4Mellin_differentiableAt_re_pos

/-- **Analytic continuation of the IBP×4 identity to the upper strip.** -/
theorem pairTestMellin_eq_ibp4_on_upper_strip (β : ℝ) {s : ℂ}
    (hRe : -4 < s.re) (hIm : 1 ≤ s.im) :
    pairTestMellin β s =
      1/(s*(s+1)*(s+2)*(s+3)) * pairDeriv4Mellin β (s + 4) := by
  set U : Set ℂ := {z : ℂ | -4 < z.re ∧ 1 ≤ z.im} with hU_def
  have hU_conn : IsPreconnected U := by
    have h_convex : Convex ℝ U := by
      intro a ha b hb t s' ht hs' hts
      refine ⟨?_, ?_⟩
      · show -4 < (t • a + s' • b).re
        rw [Complex.add_re, Complex.real_smul, Complex.real_smul,
            Complex.mul_re, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rcases lt_or_eq_of_le ht with ht0 | ht0
        · rcases lt_or_eq_of_le hs' with hs0 | hs0
          · nlinarith [mul_lt_mul_of_pos_left ha.1 ht0,
                       mul_lt_mul_of_pos_left hb.1 hs0]
          · subst hs0; have : t = 1 := by linarith
            subst this; simp; linarith [ha.1]
        · subst ht0; have : s' = 1 := by linarith
          subst this; simp; linarith [hb.1]
      · show 1 ≤ (t • a + s' • b).im
        rw [Complex.add_im, Complex.real_smul, Complex.real_smul,
            Complex.mul_im, Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
        nlinarith [ha.2, hb.2]
    exact h_convex.isPreconnected
  have hs_mem : s ∈ U := ⟨hRe, hIm⟩
  set F : ℂ → ℂ := fun z => pairTestMellin β z -
    1/(z*(z+1)*(z+2)*(z+3)) * pairDeriv4Mellin β (z + 4) with hF_def
  have hF_an : AnalyticOnNhd ℂ F U := by
    intro z hz
    have hzU_re : -4 < z.re := hz.1
    have hzU_im : 1 ≤ z.im := hz.2
    set W : Set ℂ := {w | -4 < w.re ∧ 0 < w.im}
    have hW_open : IsOpen W :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hW_mem : W ∈ nhds z := hW_open.mem_nhds ⟨hzU_re, by linarith⟩
    apply DifferentiableOn.analyticAt _ hW_mem
    intro w hw
    have hwW_re : -4 < w.re := hw.1
    have hwW_im : 0 < w.im := hw.2
    have hw_diff_ptm : DifferentiableAt ℂ (pairTestMellin β) w :=
      pairTestMellin_differentiableAt_re_gt_neg_four β hwW_re
    have hw4_re : 0 < (w + 4).re := by simp; linarith
    have hw_diff_pd4 : DifferentiableAt ℂ (pairDeriv4Mellin β) (w + 4) :=
      pairDeriv4Mellin_differentiableAt_re_pos β hw4_re
    have hw_shift : DifferentiableAt ℂ (fun v : ℂ => pairDeriv4Mellin β (v + 4)) w :=
      hw_diff_pd4.comp w (by fun_prop)
    have hw_ne : w ≠ 0 := by
      intro h; rw [h] at hwW_im; simp at hwW_im
    have hw1_ne : w + 1 ≠ 0 := by
      intro h
      have : (w + 1).im = 0 := by rw [h]; simp
      simp [Complex.add_im] at this; linarith
    have hw2_ne : w + 2 ≠ 0 := by
      intro h
      have : (w + 2).im = 0 := by rw [h]; simp
      simp [Complex.add_im] at this; linarith
    have hw3_ne : w + 3 ≠ 0 := by
      intro h
      have : (w + 3).im = 0 := by rw [h]; simp
      simp [Complex.add_im] at this; linarith
    have h_prod_ne : w * (w + 1) * (w + 2) * (w + 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hw_ne hw1_ne) hw2_ne) hw3_ne
    have h_denom_diff : DifferentiableAt ℂ
        (fun v : ℂ => 1 / (v * (v + 1) * (v + 2) * (v + 3))) w :=
      (differentiableAt_const (1 : ℂ)).div (by fun_prop) h_prod_ne
    exact (hw_diff_ptm.sub (h_denom_diff.mul hw_shift)).differentiableWithinAt
  set z₀ : ℂ := 1 + 2 * I with hz₀_def
  have hz₀_mem : z₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · show -4 < z₀.re
      rw [hz₀_def]; simp; norm_num
    · show 1 ≤ z₀.im
      rw [hz₀_def]; simp
  have hF_zero_nhds : F =ᶠ[nhds z₀] 0 := by
    have h_open : IsOpen {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h_mem : z₀ ∈ {z : ℂ | 0 < z.re} := by
      rw [hz₀_def]; show 0 < (1 + 2 * I).re; simp
    have h_nhds : {z : ℂ | 0 < z.re} ∈ nhds z₀ := h_open.mem_nhds h_mem
    filter_upwards [h_nhds] with w hw
    show F w = 0
    rw [show F w = pairTestMellin β w - 1 / (w * (w + 1) * (w + 2) * (w + 3)) *
        pairDeriv4Mellin β (w + 4) from rfl,
      pairTestMellin_ibp_four_times β hw, sub_self]
  have hzero_an : AnalyticOnNhd ℂ (0 : ℂ → ℂ) U := fun _ _ => analyticAt_const
  have h_eq := hF_an.eqOn_of_preconnected_of_eventuallyEq hzero_an hU_conn hz₀_mem hF_zero_nhds
  have h_Fs : F s = 0 := h_eq hs_mem
  unfold F at h_Fs
  exact sub_eq_zero.mp h_Fs

#print axioms pairTestMellin_eq_ibp4_on_upper_strip

/-- **Quartic decay bound extended to `σ ∈ [-1, 2]` via analytic continuation.** -/
theorem pairTestMellin_quartic_bound_extended (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ ∈ Set.Icc (-1:ℝ) 2 → ∀ T : ℝ, 2 ≤ T →
      ‖pairTestMellin β ((σ:ℂ) + (T:ℂ) * I)‖ ≤ C / T^4 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    pairDeriv4Mellin_norm_bound_on_compact_strip β 3 6 (by norm_num) (by norm_num)
  refine ⟨M, hM_nn, fun σ hσ T hT => ?_⟩
  set s : ℂ := (σ:ℂ) + (T:ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = T := by simp [s]
  have hT_pos : 0 < T := by linarith
  have hs_re_gt : -4 < s.re := by rw [hs_re]; linarith [hσ.1]
  have hs_im_ge : 1 ≤ s.im := by rw [hs_im]; linarith
  have h_id := pairTestMellin_eq_ibp4_on_upper_strip β hs_re_gt hs_im_ge
  have h_re4 : (s + 4).re = σ + 4 := by rw [Complex.add_re, hs_re]; simp
  have h_bd_d4 : ‖pairDeriv4Mellin β (s + 4)‖ ≤ M :=
    hM (s + 4) (by rw [h_re4]; linarith [hσ.1]) (by rw [h_re4]; linarith [hσ.2])
  have h_sk_abs_ge_T : ∀ k : ℕ, ‖s + (k : ℂ)‖ ≥ T := by
    intro k
    have h_im : (s + (k : ℂ)).im = T := by rw [Complex.add_im, hs_im]; simp
    calc T ≤ |((s + (k : ℂ)).im)| := by rw [h_im]; exact le_abs_self T
      _ ≤ ‖s + (k : ℂ)‖ := Complex.abs_im_le_norm _
  have h_s_ge : ‖s‖ ≥ T := by have := h_sk_abs_ge_T 0; simpa using this
  have h_s1_ge : ‖s + 1‖ ≥ T := by have := h_sk_abs_ge_T 1; simpa using this
  have h_s2_ge : ‖s + 2‖ ≥ T := by have := h_sk_abs_ge_T 2; simpa using this
  have h_s3_ge : ‖s + 3‖ ≥ T := by have := h_sk_abs_ge_T 3; simpa using this
  have h_prod_ge : ‖s * (s + 1) * (s + 2) * (s + 3)‖ ≥ T^4 := by
    rw [show (s * (s + 1) * (s + 2) * (s + 3) : ℂ) =
      s * ((s + 1) * ((s + 2) * (s + 3))) by ring]
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖s‖ * (‖s+1‖ * (‖s+2‖ * ‖s+3‖))
        ≥ T * (T * (T * T)) := by
          apply mul_le_mul h_s_ge _ (by positivity) (norm_nonneg _)
          apply mul_le_mul h_s1_ge _ (by positivity) (norm_nonneg _)
          apply mul_le_mul h_s2_ge h_s3_ge hT_pos.le (norm_nonneg _)
      _ = T^4 := by ring
  have hT4_pos : 0 < T^4 := by positivity
  have h_prod_pos : 0 < ‖s * (s + 1) * (s + 2) * (s + 3)‖ :=
    lt_of_lt_of_le hT4_pos h_prod_ge
  rw [h_id, norm_mul, norm_div, norm_one]
  have h_div_bd : 1 / ‖s * (s + 1) * (s + 2) * (s + 3)‖ ≤ 1 / T^4 := by
    rw [div_le_div_iff₀ h_prod_pos hT4_pos]; linarith
  calc 1 / ‖s * (s + 1) * (s + 2) * (s + 3)‖ * ‖pairDeriv4Mellin β (s + 4)‖
      ≤ 1 / T^4 * M := mul_le_mul h_div_bd h_bd_d4 (norm_nonneg _) (by positivity)
    _ = M / T^4 := by field_simp

#print axioms pairTestMellin_quartic_bound_extended

end HorizontalTailsDischarge
end WeilPositivity
end ZD

end
