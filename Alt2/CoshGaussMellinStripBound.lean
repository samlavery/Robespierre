import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilPairIBP
import RequestProject.WeilReflectedPrimeVanishingWeilside

/-!
# Strip extension of the σ = 2 quadratic decay bound

The file `WeilReflectedPrimeVanishingWeilside.lean` proves

```
‖coshGaussMellin c (2 + i·t)‖ ≤ K / (1 + t²)
```

via integration-by-parts twice, identifying the integrand at `(s+2)` with the
twice-differentiated cosh-Gaussian.  This file lifts that bound to a *strip*
in the σ-direction:

```
∀ σ ∈ [1, 2], ∀ y ∈ ℝ,
  ‖coshGaussMellin c (σ + i·y)‖ ≤ K · (1 + y²)⁻¹.
```

The σ-range `[1, 2]` is the largest one for which the IBP-twice formula gives
a *uniform-in-σ* bound on `1/(s·(s+1))` of order `(1 + y²)⁻¹`.

* For `σ ∈ (0, 1)` the algebraic factor `1/(s·(s+1))` does not yield the
  `(1 + y²)⁻¹` decay uniformly (as `σ → 0⁺` the bound at `y = 0` blows up).
* For `σ ≤ 0` the integral defining `coshGaussMellin` is not absolutely
  convergent; the bound would refer to an analytic continuation that the
  current repository does not provide.

So `[1, 2]` is the honest, axiom-clean σ-range that the existing
infrastructure supports.

## Strategy

Fix `c : ℝ` and write `s := σ + i·y` with `σ ∈ [1, 2]`.  By
`h1_coshGaussMellin_ibp_twice` (now public),

```
coshGaussMellin c s = 1 / (s · (s + 1)) · mellin (D²) (s + 2)
```

where `D² u := coshGaussDeriv2Val c u`.  We bound the two factors:

* `|1/(s(s+1))| ≤ 1 / (1 + y²)`.  Indeed
  `|s(s+1)|² = (σ²+y²)·((σ+1)²+y²) ≥ (1+y²)·(4+y²) ≥ (1+y²)²`.
* `‖mellin (D²) (s+2)‖ ≤ M`, where `M = ∫_{Ioi 0} (1 + u³)·|D²(u)| du`.
  Indeed `|u^(s+2-1)| = u^(σ+1)` and on `(0, 1]` we have `u^(σ+1) ≤ 1`
  (since `σ+1 ≥ 0`), while on `[1, ∞)` we have `u^(σ+1) ≤ u³`
  (since `σ+1 ≤ 3`); so `u^(σ+1) ≤ 1 + u³`.

Both pieces of the majorant `1·|D²| + u³·|D²|` are integrable on `Ioi 0`
by `h1_mellinConv_coshGaussDeriv2Val` at `s = 1` and `s = 4` respectively.
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour
open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace StripBound

/-- **Pointwise majorant for `u^(σ+1)`** on `σ ∈ [1, 2]`. -/
private lemma rpow_sigma_plus_one_le (u : ℝ) (hu : 0 < u) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1:ℝ) 2) :
    u ^ (σ + 1) ≤ 1 + u ^ (3:ℝ) := by
  rcases le_or_gt u 1 with hu1 | hu1
  · -- u ≤ 1: u^(σ+1) ≤ 1.
    have hσ_plus_one_nn : 0 ≤ σ + 1 := by have := hσ.1; linarith
    have h_le_one : u ^ (σ + 1) ≤ 1 :=
      Real.rpow_le_one hu.le hu1 hσ_plus_one_nn
    have h_u3_nn : 0 ≤ u ^ (3:ℝ) := Real.rpow_nonneg hu.le _
    linarith
  · -- u > 1: u^(σ+1) ≤ u^3.
    have hσ_plus_one_le : σ + 1 ≤ 3 := by have := hσ.2; linarith
    have h_le_u3 : u ^ (σ + 1) ≤ u ^ (3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le hσ_plus_one_le
    linarith

/-- **`|D²(u)|` is integrable on `Ioi 0`.** Specialization of
`h1_mellinConv_coshGaussDeriv2Val` at `s = 1`. -/
private lemma absD2_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ => |Contour.coshGaussDeriv2Val c u|) (Set.Ioi (0:ℝ)) := by
  have h_s1_re : (0:ℝ) < ((1:ℂ)).re := by simp
  have h_conv : IntegrableOn
      (fun u : ℝ => (u : ℂ)^((1:ℂ) - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
      (Set.Ioi 0) :=
    h1_mellinConv_coshGaussDeriv2Val c h_s1_re
  have hnorm := h_conv.norm
  refine (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).mp hnorm
  have hu_pos : (0:ℝ) < u := hu
  show ‖(u : ℂ)^((1:ℂ) - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖
      = |Contour.coshGaussDeriv2Val c u|
  have h_re_zero : ((1:ℂ) - 1).re = 0 := by simp
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, h_re_zero, Real.rpow_zero,
      Complex.norm_real, Real.norm_eq_abs, one_mul]

/-- **`u³ · |D²(u)|` is integrable on `Ioi 0`.** Specialization of
`h1_mellinConv_coshGaussDeriv2Val` at `s = 4`. -/
private lemma u3_absD2_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ => u ^ (3:ℝ) * |Contour.coshGaussDeriv2Val c u|) (Set.Ioi (0:ℝ)) := by
  have h_s4_re : (0:ℝ) < ((4:ℂ)).re := by simp
  have h_conv : IntegrableOn
      (fun u : ℝ => (u : ℂ)^((4:ℂ) - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
      (Set.Ioi 0) :=
    h1_mellinConv_coshGaussDeriv2Val c h_s4_re
  have hnorm := h_conv.norm
  refine (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).mp hnorm
  have hu_pos : (0:ℝ) < u := hu
  show ‖(u : ℂ)^((4:ℂ) - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖
      = u ^ (3:ℝ) * |Contour.coshGaussDeriv2Val c u|
  have h_re_three : ((4:ℂ) - 1).re = 3 := by
    rw [Complex.sub_re]; norm_num
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, h_re_three, Complex.norm_real,
      Real.norm_eq_abs]

/-- **Integrability of the majorant `(1 + u³)·|D²(u)|` on `Ioi 0`.** -/
private lemma majorant_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ => (1 + u ^ (3:ℝ)) * |Contour.coshGaussDeriv2Val c u|)
      (Set.Ioi (0:ℝ)) := by
  have h_sum : IntegrableOn
      (fun u : ℝ => |Contour.coshGaussDeriv2Val c u|
        + u ^ (3:ℝ) * |Contour.coshGaussDeriv2Val c u|) (Set.Ioi (0:ℝ)) :=
    (absD2_integrableOn c).add (u3_absD2_integrableOn c)
  refine (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).mp h_sum
  show |Contour.coshGaussDeriv2Val c u|
        + u ^ (3:ℝ) * |Contour.coshGaussDeriv2Val c u|
      = (1 + u ^ (3:ℝ)) * |Contour.coshGaussDeriv2Val c u|
  ring

/-- **Integrability of `u^(σ+1) · |D²(u)|` for any `σ ∈ [1, 2]`.** Bounded
by the majorant `(1 + u³) · |D²(u)|`. -/
private lemma rpow_absD2_integrableOn (c : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1:ℝ) 2) :
    IntegrableOn
      (fun u : ℝ => u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|)
      (Set.Ioi (0:ℝ)) := by
  have hσ_plus_one_nn : 0 ≤ σ + 1 := by have := hσ.1; linarith
  -- Continuity / measurability of the integrand on Ioi 0.
  have h_meas_rpow : Measurable (fun u : ℝ => u ^ (σ + 1)) :=
    (Real.continuous_rpow_const hσ_plus_one_nn).measurable
  have h_meas_d2 : Measurable
      (fun u : ℝ => |Contour.coshGaussDeriv2Val c u|) := by
    have h_cont : Continuous
        (fun u : ℝ => Contour.coshGaussDeriv2Val c u) := by
      unfold Contour.coshGaussDeriv2Val; fun_prop
    exact (continuous_abs.comp h_cont).measurable
  have h_meas : Measurable
      (fun u : ℝ => u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|) :=
    h_meas_rpow.mul h_meas_d2
  have h_aem : AEStronglyMeasurable
      (fun u : ℝ => u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    h_meas.aestronglyMeasurable
  -- Pointwise bound: u^(σ+1) · |D²(u)| ≤ (1 + u³) · |D²(u)| on Ioi 0.
  have h_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|‖ ≤
        (1 + u ^ (3:ℝ)) * |Contour.coshGaussDeriv2Val c u| := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu_pos : (0:ℝ) < u := hu
    have h_pt := rpow_sigma_plus_one_le u hu_pos hσ
    have h_abs_nn : (0:ℝ) ≤ |Contour.coshGaussDeriv2Val c u| := abs_nonneg _
    have h_lhs_nn : (0:ℝ) ≤ u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u| :=
      mul_nonneg (Real.rpow_nonneg hu_pos.le _) h_abs_nn
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    exact mul_le_mul_of_nonneg_right h_pt h_abs_nn
  exact (majorant_integrableOn c).mono' h_aem h_bound

/-- **Uniform-in-σ Mellin bound on the IBP-twice integrand.**
For `σ ∈ [1, 2]` and `y ∈ ℝ`,
`‖mellin (D²) (σ + i·y + 2)‖ ≤ M`, where `M = ∫ (1 + u³)·|D²(u)| du`. -/
private lemma coshGaussDeriv2Mellin_bound_strip (c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, σ ∈ Set.Icc (1:ℝ) 2 → ∀ y : ℝ,
      ‖mellin (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
        ((σ : ℂ) + (y : ℂ) * I + 2)‖ ≤ M := by
  set h : ℝ → ℝ := fun u : ℝ =>
    (1 + u ^ (3:ℝ)) * |Contour.coshGaussDeriv2Val c u| with h_def
  set M : ℝ := ∫ u in Set.Ioi (0:ℝ), h u with hM_def
  have hM_nn : (0:ℝ) ≤ M := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro u hu
    show 0 ≤ h u
    rw [h_def]
    refine mul_nonneg ?_ (abs_nonneg _)
    have h_u3 : 0 ≤ u ^ (3:ℝ) := Real.rpow_nonneg hu.le _
    linarith
  refine ⟨M, hM_nn, ?_⟩
  intro σ hσ y
  set s : ℂ := (σ : ℂ) + (y : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = y := by simp [s]
  set s2 : ℂ := s + 2 with hs2_def
  have hs2_re : s2.re = σ + 2 := by simp [s2, hs_re]
  -- Step 1: ‖∫ (u:ℂ)^(s2-1) • D²(u) du‖ ≤ ∫ u^(s2.re-1) · |D²(u)| du.
  have h_norm_le : ‖mellin (fun u : ℝ =>
        ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)) s2‖ ≤
      ∫ u in Set.Ioi (0:ℝ),
        u^(s2.re - 1) * |Contour.coshGaussDeriv2Val c u| := by
    unfold mellin
    calc ‖∫ u in Set.Ioi (0:ℝ),
            (u:ℂ)^(s2 - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖
        ≤ ∫ u in Set.Ioi (0:ℝ),
            ‖(u:ℂ)^(s2 - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ u in Set.Ioi (0:ℝ),
            u^(s2.re - 1) * |Contour.coshGaussDeriv2Val c u| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
          have hu_pos : (0:ℝ) < u := hu
          simp only [norm_smul]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, Complex.norm_real,
              Complex.sub_re, Complex.one_re, Real.norm_eq_abs]
  -- Step 2: rewrite s2.re - 1 = σ + 1 and bound by integral of majorant = M.
  have h_re_eq : s2.re - 1 = σ + 1 := by rw [hs2_re]; ring
  rw [h_re_eq] at h_norm_le
  -- Pointwise: u^(σ+1) · |D²| ≤ h u, and the LHS is integrable.
  have h_int_lhs : IntegrableOn
      (fun u : ℝ => u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|)
      (Set.Ioi (0:ℝ)) := rpow_absD2_integrableOn c hσ
  have h_int_majorant : IntegrableOn h (Set.Ioi (0:ℝ)) := by
    rw [h_def]; exact majorant_integrableOn c
  have h_pt : ∀ u ∈ Set.Ioi (0:ℝ),
      u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u| ≤ h u := by
    intro u hu
    have hu_pos : (0:ℝ) < u := hu
    have h_le := rpow_sigma_plus_one_le u hu_pos hσ
    have h_abs_nn : (0:ℝ) ≤ |Contour.coshGaussDeriv2Val c u| := abs_nonneg _
    show u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u| ≤
      (1 + u ^ (3:ℝ)) * |Contour.coshGaussDeriv2Val c u|
    exact mul_le_mul_of_nonneg_right h_le h_abs_nn
  have h_pt_nn : ∀ u ∈ Set.Ioi (0:ℝ),
      0 ≤ u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u| := by
    intro u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (abs_nonneg _)
  have h_int_le_M :
      (∫ u in Set.Ioi (0:ℝ), u ^ (σ + 1) * |Contour.coshGaussDeriv2Val c u|) ≤ M := by
    rw [hM_def]
    apply MeasureTheory.setIntegral_mono_on h_int_lhs h_int_majorant measurableSet_Ioi
    intro u hu; exact h_pt u hu
  exact h_norm_le.trans h_int_le_M

/-- **Uniform algebraic bound on the IBP factor `1/(s·(s+1))`** for `σ ∈ [1, 2]`.

For `s = σ + i·y` with `σ ∈ [1, 2]`,
`|s · (s + 1)| ≥ 1 + y²`, hence `1/|s·(s+1)| ≤ 1/(1 + y²)`. -/
private lemma one_over_s_s1_le (σ : ℝ) (hσ : σ ∈ Set.Icc (1:ℝ) 2) (y : ℝ) :
    let s : ℂ := (σ : ℂ) + (y : ℂ) * I
    1 + y^2 ≤ ‖s * (s + 1)‖ := by
  intro s
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = y := by simp [s]
  have h_s1_re : (s + 1).re = σ + 1 := by
    rw [Complex.add_re, hs_re]; show σ + (1:ℂ).re = σ + 1; simp
  have h_s1_im : (s + 1).im = y := by rw [Complex.add_im, hs_im]; simp
  have h_s_norm_sq : ‖s‖^2 = σ^2 + y^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hs_re, hs_im]; ring
  have h_s1_norm_sq : ‖s + 1‖^2 = (σ + 1)^2 + y^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h_s1_re, h_s1_im]; ring
  have h_prod_norm_sq : ‖s * (s + 1)‖^2 = (σ^2 + y^2) * ((σ+1)^2 + y^2) := by
    rw [norm_mul, mul_pow, h_s_norm_sq, h_s1_norm_sq]
  have hσ1 : 1 ≤ σ := hσ.1
  -- Goal: (1 + y²)² ≤ (σ²+y²) · ((σ+1)²+y²).
  have h_lower : (1 + y^2)^2 ≤ (σ^2 + y^2) * ((σ+1)^2 + y^2) := by
    have hσ_sq : 1 ≤ σ^2 := by nlinarith
    have hσ1_sq : 4 ≤ (σ+1)^2 := by nlinarith
    have h1 : 1 + y^2 ≤ σ^2 + y^2 := by linarith
    have h2 : 1 + y^2 ≤ (σ+1)^2 + y^2 := by linarith
    have h1_nn : 0 ≤ 1 + y^2 := by have := sq_nonneg y; linarith
    have h_step1 : (1 + y^2) * (1 + y^2) ≤ (σ^2 + y^2) * (1 + y^2) :=
      mul_le_mul_of_nonneg_right h1 h1_nn
    have h_pos2 : 0 ≤ σ^2 + y^2 := by have := sq_nonneg y; nlinarith
    have h_step2 : (σ^2 + y^2) * (1 + y^2) ≤ (σ^2 + y^2) * ((σ+1)^2 + y^2) :=
      mul_le_mul_of_nonneg_left h2 h_pos2
    calc (1 + y^2)^2 = (1 + y^2) * (1 + y^2) := by ring
      _ ≤ (σ^2 + y^2) * (1 + y^2) := h_step1
      _ ≤ (σ^2 + y^2) * ((σ+1)^2 + y^2) := h_step2
  have h_lower_norm_sq : (1 + y^2)^2 ≤ ‖s * (s + 1)‖^2 := by
    rw [h_prod_norm_sq]; exact h_lower
  -- Convert squared inequality to linear (both sides nonneg).
  have h_lhs_nn : 0 ≤ 1 + y^2 := by have := sq_nonneg y; linarith
  have h_rhs_nn : 0 ≤ ‖s * (s + 1)‖ := norm_nonneg _
  nlinarith [h_lower_norm_sq, sq_nonneg (1 + y^2 - ‖s * (s + 1)‖), h_lhs_nn, h_rhs_nn]

/-- **Strip-uniform quadratic decay bound for `coshGaussMellin c`.**

For `σ ∈ [1, 2]` and `y ∈ ℝ`,
`‖coshGaussMellin c (σ + i·y)‖ ≤ M · (1 + y²)⁻¹`,
where `M = ∫_{Ioi 0} (1 + u³) · |coshGaussDeriv2Val c u| du`.

Strategy: IBP-twice gives `coshGaussMellin c s = 1/(s·(s+1)) · mellin(D²)(s+2)`,
and we bound each factor uniformly in `σ ∈ [1, 2]`. -/
theorem coshGaussMellin_quadratic_bound_on_strip (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, σ ∈ Set.Icc (1:ℝ) 2 → ∀ y : ℝ,
      ‖ZD.WeilPositivity.Contour.coshGaussMellin c
          ((σ:ℂ) + (y:ℂ) * Complex.I)‖
        ≤ K * (1 + y^2)⁻¹ := by
  obtain ⟨M, hM_nn, hM_bd⟩ := coshGaussDeriv2Mellin_bound_strip c
  refine ⟨M, hM_nn, ?_⟩
  intro σ hσ y
  set s : ℂ := (σ : ℂ) + (y : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [s]
  have hσ_pos : (0:ℝ) < σ := by have := hσ.1; linarith
  have hs_re_pos : (0:ℝ) < s.re := by rw [hs_re]; exact hσ_pos
  -- IBP-twice formula.
  have h_ibp := h1_coshGaussMellin_ibp_twice c hs_re_pos
  rw [h_ibp]
  -- Set up s+2 and apply bound on mellin(D²)(s+2).
  set s2 : ℂ := s + 2 with hs2_def
  have hM_at := hM_bd σ hσ y
  -- hM_at : ‖mellin D² ((σ:ℂ) + (y:ℂ)*I + 2)‖ ≤ M; rewrite to s2.
  have h_arg_eq : (σ : ℂ) + (y : ℂ) * I + 2 = s2 := by rw [hs2_def, hs_def]
  rw [h_arg_eq] at hM_at
  -- 1 + y² > 0.
  have h_1plus_pos : (0:ℝ) < 1 + y^2 := by have := sq_nonneg y; linarith
  -- |s · (s+1)| ≥ 1 + y².
  have h_factor_lower := one_over_s_s1_le σ hσ y
  -- Show s ≠ 0 and s+1 ≠ 0, hence ‖s · (s+1)‖ > 0.
  have h_s_ne : s ≠ 0 := by
    intro h
    have h_re : s.re = 0 := by rw [h]; simp
    rw [hs_re] at h_re; linarith
  have h_s1_ne : s + 1 ≠ 0 := by
    intro h
    have h_re : (s + 1).re = 0 := by rw [h]; simp
    have h_calc : (s + 1).re = σ + 1 := by
      rw [Complex.add_re, hs_re]; show σ + (1:ℂ).re = σ + 1; simp
    rw [h_calc] at h_re; linarith
  have h_prod_pos : 0 < ‖s * (s + 1)‖ := by
    rw [norm_pos_iff]; exact mul_ne_zero h_s_ne h_s1_ne
  -- 1/|s(s+1)| ≤ 1/(1+y²).
  have h_div_bd : (1:ℝ) / ‖s * (s + 1)‖ ≤ 1 / (1 + y^2) := by
    rw [div_le_div_iff₀ h_prod_pos h_1plus_pos]
    linarith
  -- Combine: ‖1/(s·(s+1)) · mellin(D²)(s+2)‖ = (1/‖s·(s+1)‖) · ‖mellin(D²)(s+2)‖.
  rw [norm_mul, norm_div, norm_one]
  calc 1 / ‖s * (s + 1)‖ *
        ‖mellin (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)) s2‖
      ≤ 1 / ‖s * (s + 1)‖ * M :=
        mul_le_mul_of_nonneg_left hM_at (by positivity)
    _ ≤ (1 / (1 + y^2)) * M :=
        mul_le_mul_of_nonneg_right h_div_bd hM_nn
    _ = M * (1 + y^2)⁻¹ := by rw [one_div]; ring

#print axioms coshGaussMellin_quadratic_bound_on_strip

end StripBound
end Contour
end WeilPositivity
end ZD
