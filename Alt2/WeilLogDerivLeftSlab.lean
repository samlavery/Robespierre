import Mathlib
import RequestProject.UniformGammaRBound
import RequestProject.WeilLogDerivZetaBound

set_option maxHeartbeats 0

/-!
# Log-derivative bound for `ζ'/ζ` on a narrow left slab via FE transport

For `σ ∈ [-3/4, -1/2]` and `T ≥ 2`,
`‖ζ'/ζ(σ + iT)‖ ≤ C · (log T)^2` with a uniform constant `C`.

Strategy: from `completedRiemannZeta_one_sub` (FE of Λ) + `logDeriv_mul` on
`Λ = Γℝ · ζ`, obtain `ζ'/ζ(s) = -ζ'/ζ(1-s) - logDeriv Γℝ(s) - logDeriv Γℝ(1-s)`.
Pole bookkeeping (`1/s`, `1/(s-1)`) is avoided — those terms never appear.

* `Re(1-s) ∈ [3/2, 7/4]` ⇒ `‖ζ'/ζ(1-s)‖` bounded by a constant.
* `logDeriv Γℝ(1-s)`: ψ((1-s)/2) with Re ∈ [5/8, 7/8] — bounded directly.
* `logDeriv Γℝ(s)`: ψ(s/2) with Re ∈ [-3/8, -1/4] — shift via
  `Complex.digamma_apply_add_one` to s/2+1 with Re ∈ [5/8, 3/4], then bound.
  Shift error `‖2/s‖ ≤ 1` for T ≥ 2.
-/

open Complex

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

namespace LeftSlab

private lemma gammaℝ_diff_of_ne (z : ℂ) (h : Complex.Gammaℝ z ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ z := by
  have h_s_ne : ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) := by
    intro n hn; exact h (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩)
  have h_half_ne : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have : z = -(2 * (m : ℂ)) := by linear_combination 2 * hm
    exact h_s_ne m this
  have hΓ : DifferentiableAt ℂ Complex.Gamma (z / 2) :=
    Complex.differentiableAt_Gamma _ h_half_ne
  have hcpow : DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) z := by
    refine DifferentiableAt.const_cpow
      ((differentiableAt_id.neg).div_const 2) ?_
    left; exact_mod_cast Real.pi_pos.ne'
  have hcomp : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) z :=
    hΓ.comp z (differentiableAt_id.div_const 2)
  have h_eq :
      Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) := by
    funext t; exact Complex.Gammaℝ_def t
  rw [h_eq]; exact hcpow.mul hcomp

private lemma logDeriv_Λ_eq (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hΓ : Complex.Gammaℝ z ≠ 0) (hζ : riemannZeta z ≠ 0) :
    logDeriv completedRiemannZeta z =
      logDeriv Complex.Gammaℝ z + logDeriv riemannZeta z := by
  have hζ_diff : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz1
  have hΓ_diff : DifferentiableAt ℂ Complex.Gammaℝ z := gammaℝ_diff_of_ne z hΓ
  have hΓ_cont : ContinuousAt Complex.Gammaℝ z := hΓ_diff.continuousAt
  have hΓ_nbhd : ∀ᶠ w in nhds z, Complex.Gammaℝ w ≠ 0 := hΓ_cont.eventually_ne hΓ
  have hne0 : ∀ᶠ w in nhds z, w ≠ 0 :=
    isOpen_compl_singleton.mem_nhds (by simpa : z ∈ ({0}ᶜ : Set ℂ))
  have hΛ_ev : completedRiemannZeta =ᶠ[nhds z]
      (fun w => Complex.Gammaℝ w * riemannZeta w) := by
    filter_upwards [hΓ_nbhd, hne0] with w _ hw0
    rw [riemannZeta_def_of_ne_zero hw0]; field_simp
  have h1 := logDeriv_mul z hΓ hζ hΓ_diff hζ_diff
  simp only [logDeriv_apply] at *
  rw [Filter.EventuallyEq.deriv_eq hΛ_ev, hΛ_ev.self_of_nhds]
  exact h1

private lemma logDeriv_Λ_fe (s : ℂ)
    (h1ms0 : 1 - s ≠ 0) (h1ms1 : 1 - s ≠ 1) :
    logDeriv completedRiemannZeta s = -logDeriv completedRiemannZeta (1 - s) := by
  have hF_diff : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta h1ms0 h1ms1
  have hFE : ∀ z, completedRiemannZeta (1 - z) = completedRiemannZeta z :=
    completedRiemannZeta_one_sub
  have h_eq_nhds :
      (fun z => completedRiemannZeta (1 - z)) =ᶠ[nhds s] completedRiemannZeta :=
    Filter.Eventually.of_forall hFE
  have h_deriv_eq :
      deriv (fun z => completedRiemannZeta (1 - z)) s =
        deriv completedRiemannZeta s :=
    Filter.EventuallyEq.deriv_eq h_eq_nhds
  have h_chain :
      deriv (fun z => completedRiemannZeta (1 - z)) s =
        -deriv completedRiemannZeta (1 - s) := by
    have h_inner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1 : ℂ) s := by
      simpa using (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)
    have h_outer : HasDerivAt completedRiemannZeta
        (deriv completedRiemannZeta (1 - s)) (1 - s) := hF_diff.hasDerivAt
    have h := h_outer.comp s h_inner
    simpa [mul_comm, mul_neg] using h.deriv
  have h_deriv_fe : deriv completedRiemannZeta s =
      -deriv completedRiemannZeta (1 - s) := by
    rw [← h_deriv_eq, h_chain]
  have h_val : completedRiemannZeta (1 - s) = completedRiemannZeta s := hFE s
  simp only [logDeriv_apply]
  rw [h_deriv_fe, neg_div]; congr 1; rw [← h_val]

private lemma zeta_ne_zero_slab
    (σ : ℝ) (hσ : σ ∈ Set.Icc (-3/4 : ℝ) (-1/2))
    (T : ℝ) (hT : 2 ≤ T) :
    riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [hs_def]
  have hs_im : s.im = T := by simp [hs_def]
  have hT_pos : 0 < T := by linarith
  have hs_ne0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hs_im] at this; simp at this; linarith
  have h1ms_re : (1 - s).re = 1 - σ := by simp [hs_re]
  have h1ms_im : (1 - s).im = -T := by simp [hs_im]
  have h1ms_re_gt_one : 1 < (1 - s).re := by rw [h1ms_re]; linarith [hσ.2]
  have hΓℝ_s : Complex.Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
    have := congrArg Complex.im hn; rw [hs_im] at this; simp at this; linarith
  have hΓℝ_1ms : Complex.Gammaℝ (1 - s) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
    have := congrArg Complex.im hn; rw [h1ms_im] at this; simp at this; linarith
  have hζ_1ms : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h1ms_re_gt_one
  have h1ms_ne0 : (1 - s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [h1ms_re] at this; simp at this; linarith [hσ.2]
  have hΛ_1ms : completedRiemannZeta (1 - s) ≠ 0 := by
    have heq : completedRiemannZeta (1 - s) =
        Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) := by
      rw [riemannZeta_def_of_ne_zero h1ms_ne0]; field_simp
    rw [heq]; exact mul_ne_zero hΓℝ_1ms hζ_1ms
  have hΛ_s : completedRiemannZeta s ≠ 0 := by
    have := completedRiemannZeta_one_sub s; rw [← this]; exact hΛ_1ms
  rw [riemannZeta_def_of_ne_zero hs_ne0]
  exact div_ne_zero hΛ_s hΓℝ_s

private lemma norm_logDeriv_gammaℝ_le (z : ℂ) (B : ℝ)
    (hΓℝ : Complex.Gammaℝ z ≠ 0) (h_ne2n : ∀ n : ℕ, z ≠ -(2 * (n : ℂ)))
    (hψ : ‖deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)‖ ≤ B) :
    ‖logDeriv Complex.Gammaℝ z‖ ≤ Real.log Real.pi / 2 + (1/2) * B := by
  have h_form :=
    ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form z hΓℝ h_ne2n
  have h_rw : logDeriv Complex.Gammaℝ z =
      -(Real.log Real.pi : ℂ) / 2 +
        (1 / 2 : ℂ) * (deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) := by
    rw [logDeriv_apply, h_form]
    have h_log_eq : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    rw [h_log_eq]
  have h_logπ_nn : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h_norm_first : ‖-(Real.log Real.pi : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    rw [show (Real.log Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from rfl,
      Complex.norm_real]
    simp [abs_of_nonneg h_logπ_nn]
  have h_norm_second :
      ‖(1 / 2 : ℂ) * (deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2))‖ =
        (1/2) * ‖deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)‖ := by
    rw [norm_mul]; congr 1
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    norm_num
  rw [h_rw]
  refine le_trans (norm_add_le _ _) ?_
  rw [h_norm_first, h_norm_second]
  have h12 : (0 : ℝ) ≤ 1/2 := by norm_num
  linarith [mul_le_mul_of_nonneg_left hψ h12]

/-- **Log-derivative bound on the narrow left slab `σ ∈ [-3/4, -1/2]`.** -/
theorem logDerivZeta_bound_left_slab :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-3/4 : ℝ) (-1/2),
      ∀ T : ℝ, 2 ≤ T →
        ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I) /
         riemannZeta ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C * (Real.log T) ^ 2 := by
  obtain ⟨Cζ, hCζ_nn, hCζ_bd⟩ :=
    ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one (3/2) (by norm_num)
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ := ZD.UniformGammaR.digamma_log_bound_uniform_sigma01
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogπ_nn : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  set M : ℝ :=
    Cζ + 2 * (Real.log Real.pi / 2) + (Cd + 1) + Cd + Cd^2 with hM_def
  set C : ℝ := (M + 1) / (Real.log 2)^2 + 1 with hC_def
  have hlog2_sq_pos : 0 < (Real.log 2)^2 := by positivity
  have hM_nn : 0 ≤ M := by
    rw [hM_def]
    have h2 : 0 ≤ 2 * (Real.log Real.pi / 2) := by positivity
    have h3 : 0 ≤ Cd^2 := sq_nonneg _
    linarith [hCζ_nn, hCd_pos.le]
  refine ⟨C, ?_, ?_⟩
  · have : 0 ≤ (M + 1) / (Real.log 2)^2 := div_nonneg (by linarith) hlog2_sq_pos.le
    linarith
  intro σ hσ T hT
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [hs_def]
  have hs_im : s.im = T := by simp [hs_def]
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  have hs_ne0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hs_im] at this; simp at this; linarith
  have hs_ne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hs_im] at this; simp at this; linarith
  have h1ms_re : (1 - s).re = 1 - σ := by simp [hs_re]
  have h1ms_im : (1 - s).im = -T := by simp [hs_im]
  have h1ms_re_ge : (3/2 : ℝ) ≤ (1 - s).re := by rw [h1ms_re]; linarith [hσ.2]
  have h1ms_re_gt_one : 1 < (1 - s).re := by linarith
  have h1ms_ne0 : (1 - s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [h1ms_re] at this; simp at this; linarith [hσ.2]
  have h1ms_ne1 : (1 - s) ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [h1ms_im] at this; simp at this; linarith
  have hΓℝ_s : Complex.Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
    have := congrArg Complex.im hn; rw [hs_im] at this; simp at this; linarith
  have hΓℝ_1ms : Complex.Gammaℝ (1 - s) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
    have := congrArg Complex.im hn; rw [h1ms_im] at this; simp at this; linarith
  have hζ_s : riemannZeta s ≠ 0 := zeta_ne_zero_slab σ hσ T hT
  have hζ_1ms : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h1ms_re_gt_one
  have hA : logDeriv completedRiemannZeta s =
      logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s :=
    logDeriv_Λ_eq s hs_ne0 hs_ne1 hΓℝ_s hζ_s
  have hB : logDeriv completedRiemannZeta (1 - s) =
      logDeriv Complex.Gammaℝ (1 - s) + logDeriv riemannZeta (1 - s) :=
    logDeriv_Λ_eq (1 - s) h1ms_ne0 h1ms_ne1 hΓℝ_1ms hζ_1ms
  have hFE := logDeriv_Λ_fe s h1ms_ne0 h1ms_ne1
  have h_core :
      deriv riemannZeta s / riemannZeta s =
        -(deriv riemannZeta (1 - s) / riemannZeta (1 - s))
          - logDeriv Complex.Gammaℝ s - logDeriv Complex.Gammaℝ (1 - s) := by
    have : logDeriv riemannZeta s =
        -logDeriv riemannZeta (1 - s) - logDeriv Complex.Gammaℝ s
          - logDeriv Complex.Gammaℝ (1 - s) := by
      have heq :
          logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s =
            -(logDeriv Complex.Gammaℝ (1 - s) + logDeriv riemannZeta (1 - s)) := by
        rw [← hA, ← hB, hFE]
      linear_combination heq
    simpa [logDeriv_apply] using this
  have h_bd_zeta : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ Cζ :=
    hCζ_bd (1 - s) h1ms_re_ge
  have h_bd_Γ1ms :
      ‖logDeriv Complex.Gammaℝ (1 - s)‖ ≤
        Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T) := by
    have h_cast : (1 - s) / 2 =
        (((1 - σ) / 2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I := by
      rw [hs_def]; push_cast; ring
    have hσ' : (1 - σ) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩ <;> linarith [hσ.1, hσ.2]
    have h_abs_negT : |(-T/2 : ℝ)| = T/2 := by
      rw [abs_of_nonpos (by linarith : (-T/2 : ℝ) ≤ 0)]; ring
    have hT' : 1 ≤ |(-T/2)| := by rw [h_abs_negT]; linarith
    have hψ_bd :
        ‖deriv Complex.Gamma ((((1-σ)/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I) /
          Complex.Gamma ((((1-σ)/2 : ℝ) : ℂ) + ((-T/2 : ℝ) : ℂ) * I)‖ ≤
          Cd * Real.log (1 + |(-T/2)|) :=
      hCd_bd ((1 - σ)/2) hσ' (-T/2) hT'
    rw [h_abs_negT] at hψ_bd
    have hψ_at : ‖deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)‖
          ≤ Cd * Real.log (1 + T/2) := by
      rw [h_cast]
      exact hψ_bd
    have h_log_le : Real.log (1 + T/2) ≤ Real.log T :=
      Real.log_le_log (by linarith) (by linarith)
    have hψ_le : ‖deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)‖
          ≤ Cd * Real.log T :=
      hψ_at.trans (mul_le_mul_of_nonneg_left h_log_le hCd_pos.le)
    have h_ne2n : ∀ n : ℕ, (1 - s) ≠ -(2 * (n : ℂ)) := by
      intro n h
      exact hΓℝ_1ms (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
    exact norm_logDeriv_gammaℝ_le (1 - s) (Cd * Real.log T) hΓℝ_1ms h_ne2n hψ_le
  have h_bd_Γs :
      ‖logDeriv Complex.Gammaℝ s‖ ≤
        Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T + 1) := by
    have h_cast_shift : s / 2 + 1 =
        (((σ/2 + 1) : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I := by
      rw [hs_def]; push_cast; ring
    have hσ' : σ/2 + 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩ <;> linarith [hσ.1, hσ.2]
    have h_abs_T : |(T/2 : ℝ)| = T/2 := abs_of_pos (by linarith : (0:ℝ) < T/2)
    have hT' : 1 ≤ |(T/2)| := by rw [h_abs_T]; linarith
    have hψ_bd :
        ‖deriv Complex.Gamma ((((σ/2+1) : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I) /
          Complex.Gamma ((((σ/2+1) : ℝ) : ℂ) + ((T/2 : ℝ) : ℂ) * I)‖ ≤
          Cd * Real.log (1 + |T/2|) :=
      hCd_bd (σ/2 + 1) hσ' (T/2) hT'
    rw [h_abs_T] at hψ_bd
    have hψ_shift : ‖deriv Complex.Gamma (s/2 + 1) / Complex.Gamma (s/2 + 1)‖
          ≤ Cd * Real.log (1 + T/2) := by
      rw [h_cast_shift]
      exact hψ_bd
    have h_log_le : Real.log (1 + T/2) ≤ Real.log T :=
      Real.log_le_log (by linarith) (by linarith)
    have hψ_shift_T : ‖deriv Complex.Gamma (s/2 + 1) / Complex.Gamma (s/2 + 1)‖
          ≤ Cd * Real.log T :=
      hψ_shift.trans (mul_le_mul_of_nonneg_left h_log_le hCd_pos.le)
    have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have : s = -(2 * (m : ℂ)) := by linear_combination 2 * h
      exact hΓℝ_s (Complex.Gammaℝ_eq_zero_iff.mpr ⟨m, this⟩)
    have h_shift :
        deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2) =
          deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1) - 2 / s := by
      have h := Complex.digamma_apply_add_one (s / 2) h_half_ne
      unfold Complex.digamma logDeriv at h
      simp only [Pi.div_apply] at h
      have h2 : (s / 2)⁻¹ = 2 / s := by field_simp
      linear_combination -h - h2
    have h_2_over_s : ‖(2 : ℂ) / s‖ ≤ 1 := by
      have hs_norm_ge : T ≤ ‖s‖ := by
        have h_eq : T = |s.im| := by rw [hs_im, abs_of_pos hT_pos]
        rw [h_eq]; exact Complex.abs_im_le_norm s
      have hs_norm_pos : 0 < ‖s‖ := lt_of_lt_of_le hT_pos hs_norm_ge
      rw [norm_div]
      rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
      rw [div_le_iff₀ hs_norm_pos]; linarith
    have hψ_orig : ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖
          ≤ Cd * Real.log T + 1 := by
      rw [h_shift]
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hψ_shift_T, h_2_over_s]
    have h_ne2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
      intro n h
      exact hΓℝ_s (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
    exact norm_logDeriv_gammaℝ_le s (Cd * Real.log T + 1) hΓℝ_s h_ne2n hψ_orig
  rw [h_core]
  have h_norm_add3 :
      ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))
        - logDeriv Complex.Gammaℝ s - logDeriv Complex.Gammaℝ (1 - s)‖ ≤
      ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
        + ‖logDeriv Complex.Gammaℝ s‖ + ‖logDeriv Complex.Gammaℝ (1 - s)‖ := by
    have h1 := norm_sub_le
        (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) - logDeriv Complex.Gammaℝ s)
        (logDeriv Complex.Gammaℝ (1 - s))
    have h2 := norm_sub_le
        (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)))
        (logDeriv Complex.Gammaℝ s)
    have h3 : ‖-(deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖
        = ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := norm_neg _
    linarith
  have h_sum_bd :
      ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
        + ‖logDeriv Complex.Gammaℝ s‖ + ‖logDeriv Complex.Gammaℝ (1 - s)‖ ≤
      Cζ + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T + 1))
        + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T)) := by
    linarith [h_bd_zeta, h_bd_Γs, h_bd_Γ1ms]
  refine le_trans h_norm_add3 (le_trans h_sum_bd ?_)
  have hlog2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogT_ge_half : (1/2 : ℝ) ≤ Real.log T := le_trans hlog2_ge_half hlogT_ge_log2
  -- Final bound: sum ≤ C * (log T)^2 with C := (M+1)/(log 2)^2 + 1.
  -- Strategy:
  --   (log T)^2 ≥ (log 2)^2  (since log T ≥ log 2).
  --   C * (log 2)^2 = (M+1) + (log 2)^2.
  --   sum at logT = log 2: Cζ + logπ + Cd·log2 + 1/2.
  --   (M+1) - (Cζ + logπ + Cd·log2 + 1/2) = 2Cd + 2 - Cd·log2 - 1/2 ≥ 0.
  --   Growth: d/dlogT [sum] = Cd; d/dlogT [C·logT²] = 2C·logT ≥ 2C·log2 ≥ 2Cd (since C ≥ Cd/log2 generously).
  have hlogT_sq_ge : (Real.log 2)^2 ≤ (Real.log T)^2 := by
    have h1 : Real.log 2 ≤ Real.log T := hlogT_ge_log2
    have h2 : 0 ≤ Real.log 2 := hlog2_pos.le
    nlinarith
  have hC_nn : 0 ≤ C := by
    have : 0 ≤ (M + 1) / (Real.log 2)^2 := div_nonneg (by linarith) hlog2_sq_pos.le
    rw [hC_def]; linarith
  -- Final bound via AM-GM absorption: M absorbs Cd² so Cd·logT ≤ (logT)² + Cd² lifts cleanly.
  -- M + 1 = Cζ + logπ + 2Cd + 2 + Cd².
  have hM_eq : M + 1 = Cζ + Real.log Real.pi + 2 * Cd + 2 + Cd^2 := by rw [hM_def]; ring
  -- AM-GM: 2·Cd·logT ≤ (logT)² + Cd², from (logT - Cd)² ≥ 0.
  have h_amgm : 2 * Cd * Real.log T ≤ (Real.log T)^2 + Cd^2 := by
    nlinarith [sq_nonneg (Real.log T - Cd)]
  have h_Cd_logT_bd : Cd * Real.log T ≤ (Real.log T)^2 + Cd^2 := by
    nlinarith [h_amgm, sq_nonneg (Real.log T), sq_nonneg Cd]
  -- Algebraic split: C · (logT)² = (M+1)·(logT/log2)² + (logT)².
  have h_split :
      C * (Real.log T)^2 =
        (M + 1) * (Real.log T / Real.log 2)^2 + (Real.log T)^2 := by
    rw [hC_def]; field_simp
  -- (logT/log2)² ≥ 1 since logT ≥ log 2 > 0.
  have h_ratio_ge_one : 1 ≤ Real.log T / Real.log 2 :=
    (one_le_div hlog2_pos).mpr hlogT_ge_log2
  have h_ratio_sq_ge_one : 1 ≤ (Real.log T / Real.log 2)^2 := by
    nlinarith [h_ratio_ge_one]
  have h_MP1_ratio_sq : M + 1 ≤ (M + 1) * (Real.log T / Real.log 2)^2 := by
    nlinarith [hM_nn, h_ratio_sq_ge_one]
  -- Core algebra: Cζ + logπ + Cd·logT + 1/2 ≤ (M+1) + (logT)².
  --   (M+1) + (logT)² - (Cζ + logπ + Cd·logT + 1/2)
  --   = 2Cd + 3/2 + Cd² + (logT)² - Cd·logT
  --   ≥ 2Cd + 3/2 + 0                                   (using h_Cd_logT_bd)
  --   ≥ 0.
  have h_mid :
      Cζ + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T + 1))
        + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T)) ≤
      (M + 1) + (Real.log T)^2 := by
    rw [hM_eq]
    linarith [h_Cd_logT_bd, hCd_pos.le]
  -- Combine h_mid + h_MP1_ratio_sq + h_split.
  calc Cζ + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T + 1))
          + (Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T))
      ≤ (M + 1) + (Real.log T)^2 := h_mid
    _ ≤ (M + 1) * (Real.log T / Real.log 2)^2 + (Real.log T)^2 := by linarith [h_MP1_ratio_sq]
    _ = C * (Real.log T)^2 := h_split.symm

#print axioms logDerivZeta_bound_left_slab

end LeftSlab
end Contour
end WeilPositivity
end ZD

end
