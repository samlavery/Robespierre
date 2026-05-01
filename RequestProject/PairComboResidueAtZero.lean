/-
# Pair-combo residue at s=0: identification with explicit β-dependent integral

For the 5-term pair-combo with weights `[1/2, 1/2, -1, -1, +1]` over the c-values
`{c₁, c₂, c₃, c₄, c₅} = {2β - π/3, 2 - π/3 - 2β, 1 - π/3, 2β - 1, 0}`, the
constant-term combination of the cosh-difference Mellin functions
`m_c := ∫₀^∞ (cosh(c·x) - 1) · exp(-2x²) / x  dx` simplifies to
`R(β) := ∫₀^∞ (cosh((1-π/3)x) - 1) · (cosh((2β-1)x) - 1) · exp(-2x²) / x dx`.

This file proves the pointwise factorisation identity and integrates both sides
to obtain the closed-form residue identification.

Key tool: `cosh(a+b) + cosh(a-b) = 2·cosh(a)·cosh(b)` (i.e.
`Real.cosh_add` + `Real.cosh_sub`), which makes
`(cosh(c₃+c₄)x + cosh(c₃-c₄)x)/2 - cosh(c₃x) - cosh(c₄x) + 1
   = (cosh(c₃x) - 1) · (cosh(c₄x) - 1)`.

Together with the c-value algebra `c₁ = c₃ + c₄`, `c₂ = c₃ - c₄`, `c₅ = 0`, this
shows the LHS combo of `coshDiffM`-values equals `R(β)`.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open MeasureTheory Set Real
open scoped Real

namespace ZD.PairComboResidueAtZero

/-! ### Definitions -/

/-- The cosh-difference half-line Mellin "constant term":
`m_c := ∫₀^∞ (cosh(c·x) - 1) · exp(-2x²) / x  dx`. -/
def coshDiffM (c : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x

/-- The β-dependent product integral
`R(β) := ∫₀^∞ (cosh((1-π/3)x) - 1) · (cosh((2β-1)x) - 1) · exp(-2x²) / x  dx`. -/
def R_beta (β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (Real.cosh ((1 - Real.pi/3) * x) - 1) *
    (Real.cosh ((2 * β - 1) * x) - 1) *
    Real.exp (-2 * x^2) / x

/-! ### Pointwise cosh identity -/

/-- The pointwise cosh-product identity:
`(1/2)(cosh((c₃+c₄)x) - 1) + (1/2)(cosh((c₃-c₄)x) - 1)
   - (cosh(c₃ x) - 1) - (cosh(c₄ x) - 1) = (cosh(c₃ x) - 1)(cosh(c₄ x) - 1)`.
Direct from `cosh(a+b) + cosh(a-b) = 2 cosh(a) cosh(b)`. -/
lemma cosh_pair_combo_pointwise (c₃ c₄ x : ℝ) :
    (1/2 : ℝ) * (Real.cosh ((c₃ + c₄) * x) - 1)
    + (1/2 : ℝ) * (Real.cosh ((c₃ - c₄) * x) - 1)
    - (Real.cosh (c₃ * x) - 1)
    - (Real.cosh (c₄ * x) - 1)
    = (Real.cosh (c₃ * x) - 1) * (Real.cosh (c₄ * x) - 1) := by
  have hadd : Real.cosh ((c₃ + c₄) * x) =
      Real.cosh (c₃ * x) * Real.cosh (c₄ * x)
        + Real.sinh (c₃ * x) * Real.sinh (c₄ * x) := by
    have : (c₃ + c₄) * x = c₃ * x + c₄ * x := by ring
    rw [this, Real.cosh_add]
  have hsub : Real.cosh ((c₃ - c₄) * x) =
      Real.cosh (c₃ * x) * Real.cosh (c₄ * x)
        - Real.sinh (c₃ * x) * Real.sinh (c₄ * x) := by
    have : (c₃ - c₄) * x = c₃ * x - c₄ * x := by ring
    rw [this, Real.cosh_sub]
  rw [hadd, hsub]; ring

/-! ### Bound: `cosh y - 1 ≤ (y²/2) · exp(y²/2)` (mirrors `CoshGaussMellinResidue`) -/

private lemma cosh_minus_one_bound_sq (y : ℝ) :
    Real.cosh y - 1 ≤ (y^2 / 2) * Real.exp (y^2 / 2) := by
  have h1 : Real.cosh y ≤ Real.exp (y^2 / 2) := Real.cosh_le_exp_half_sq _
  set z := y^2 / 2 with hz_def
  have hz_nn : 0 ≤ z := by simp only [hz_def]; positivity
  have h_int_exp : IntervalIntegrable Real.exp MeasureTheory.volume 0 z :=
    Real.continuous_exp.intervalIntegrable _ _
  have h_int_const : IntervalIntegrable (fun _ => Real.exp z) MeasureTheory.volume 0 z :=
    intervalIntegrable_const
  have h_int : ∫ u in (0:ℝ)..z, Real.exp u = Real.exp z - Real.exp 0 := integral_exp
  rw [Real.exp_zero] at h_int
  have h_bound : ∫ u in (0:ℝ)..z, Real.exp u ≤ ∫ _ in (0:ℝ)..z, Real.exp z := by
    apply intervalIntegral.integral_mono_on hz_nn h_int_exp h_int_const
    intro u hu; exact Real.exp_le_exp.mpr hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h_bound
  linarith

/-- AM-GM bound: `|c| · x ≤ c²/2 + x²/2` for all real `c, x`. -/
private lemma abs_mul_le_half_sq_add_half_sq (c x : ℝ) :
    |c * x| ≤ c^2 / 2 + x^2 / 2 := by
  nlinarith [sq_nonneg (|c| - |x|), sq_abs c, sq_abs x, abs_mul c x]

/-! ### Integrability of `(cosh(c·x) - 1) · exp(-2x²) / x` on `Ioi 0` -/

/-- Dominator near 0: `(cosh(c·x) - 1) · exp(-2x²) / x ≤ (c²/2)·exp(c²/2) · x` on `Ioc 0 1`. -/
private lemma coshDiffM_integrand_bound_near_zero (c : ℝ) {x : ℝ}
    (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    |(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x|
      ≤ (c^2 / 2) * Real.exp (c^2 / 2) := by
  have h_cosh_minus_one_nn : 0 ≤ Real.cosh (c * x) - 1 := by
    have := Real.one_le_cosh (c * x); linarith
  have h_exp_nn : 0 ≤ Real.exp (-2 * x^2) := (Real.exp_pos _).le
  have h_lhs_nn : 0 ≤ (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x :=
    div_nonneg (mul_nonneg h_cosh_minus_one_nn h_exp_nn) hx_pos.le
  rw [abs_of_nonneg h_lhs_nn]
  -- Bound (cosh(cx) - 1) ≤ (cx)²/2 · exp((cx)²/2) ≤ (cx)²/2 · exp(c²/2)
  have h_bound1 : Real.cosh (c * x) - 1 ≤ ((c * x)^2 / 2) * Real.exp ((c * x)^2 / 2) :=
    cosh_minus_one_bound_sq (c * x)
  have h_x_sq_le : x^2 ≤ 1 := by nlinarith
  have h_cx_sq_le : (c * x)^2 ≤ c^2 := by
    have : (c * x)^2 = c^2 * x^2 := by ring
    rw [this]
    calc c^2 * x^2 ≤ c^2 * 1 := mul_le_mul_of_nonneg_left h_x_sq_le (sq_nonneg _)
      _ = c^2 := by ring
  have h_exp_arg_le : (c * x)^2 / 2 ≤ c^2 / 2 := by linarith
  have h_exp_le : Real.exp ((c * x)^2 / 2) ≤ Real.exp (c^2 / 2) :=
    Real.exp_le_exp.mpr h_exp_arg_le
  have h_exp_neg2_le_one : Real.exp (-2 * x^2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := sq_nonneg x; nlinarith
  -- Chain: (cosh(cx)-1) · exp(-2x²) / x ≤ ((cx)²/2 · exp(c²/2)) · 1 / x
  --      = c² x / 2 · exp(c²/2) ≤ c²/2 · exp(c²/2)  (since x ≤ 1)
  have h_step1 :
      (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2)
        ≤ ((c * x)^2 / 2) * Real.exp ((c * x)^2 / 2) * Real.exp (-2 * x^2) :=
    mul_le_mul_of_nonneg_right h_bound1 h_exp_nn
  have h_step2 :
      ((c * x)^2 / 2) * Real.exp ((c * x)^2 / 2) * Real.exp (-2 * x^2)
        ≤ ((c * x)^2 / 2) * Real.exp (c^2 / 2) * 1 := by
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left h_exp_le; positivity
    · exact h_exp_neg2_le_one
    · exact h_exp_nn
    · positivity
  have h_step3 :
      ((c * x)^2 / 2) * Real.exp (c^2 / 2) * 1
        = (c^2 / 2) * x * Real.exp (c^2 / 2) * x := by ring
  have h_chain :
      (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2)
        ≤ (c^2 / 2) * x * Real.exp (c^2 / 2) * x :=
    le_trans h_step1 (le_trans h_step2 h_step3.le)
  rw [div_le_iff₀ hx_pos]
  calc (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2)
      ≤ (c^2 / 2) * x * Real.exp (c^2 / 2) * x := h_chain
    _ ≤ (c^2 / 2) * 1 * Real.exp (c^2 / 2) * x := by
        have : (c^2 / 2) * x * Real.exp (c^2 / 2)
             ≤ (c^2 / 2) * 1 * Real.exp (c^2 / 2) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hx_le
            positivity
          · positivity
        nlinarith [Real.exp_pos (c^2/2), sq_nonneg c, hx_pos.le]
    _ = c^2 / 2 * Real.exp (c^2 / 2) * x := by ring

/-- Dominator at infinity: `(cosh(c·x) - 1) · exp(-2x²) / x ≤ exp(c²/2) · exp(-3x²/2)`
on `Ioi 1`. -/
private lemma coshDiffM_integrand_bound_at_infty (c : ℝ) {x : ℝ}
    (hx : 1 < x) :
    |(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x|
      ≤ Real.exp (c^2 / 2) * Real.exp (-(3/2) * x^2) := by
  have h_x_pos : 0 < x := lt_trans zero_lt_one hx
  have h_cosh_minus_one_nn : 0 ≤ Real.cosh (c * x) - 1 := by
    have := Real.one_le_cosh (c * x); linarith
  have h_exp_nn : 0 ≤ Real.exp (-2 * x^2) := (Real.exp_pos _).le
  have h_lhs_nn : 0 ≤ (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x :=
    div_nonneg (mul_nonneg h_cosh_minus_one_nn h_exp_nn) h_x_pos.le
  rw [abs_of_nonneg h_lhs_nn]
  -- Bound: cosh(cx) - 1 ≤ cosh(cx) ≤ exp(|cx|) ≤ exp(c²/2 + x²/2).
  have h_cosh_bound : Real.cosh (c * x) ≤ Real.exp |c * x| := by
    rw [Real.cosh_eq]
    rcases le_total 0 (c * x) with h | h
    · rw [abs_of_nonneg h]
      linarith [Real.exp_le_exp.mpr (by linarith : -(c * x) ≤ c * x)]
    · rw [abs_of_nonpos h]
      linarith [Real.exp_le_exp.mpr (by linarith : c * x ≤ -(c * x))]
  have h_amgm : |c * x| ≤ c^2 / 2 + x^2 / 2 := abs_mul_le_half_sq_add_half_sq c x
  have h_cosh_le : Real.cosh (c * x) ≤ Real.exp (c^2 / 2 + x^2 / 2) :=
    le_trans h_cosh_bound (Real.exp_le_exp.mpr h_amgm)
  have h_diff_le : Real.cosh (c * x) - 1 ≤ Real.exp (c^2 / 2 + x^2 / 2) := by
    linarith
  have h_diff_nn := h_cosh_minus_one_nn
  -- (cosh(cx) - 1) · exp(-2x²) ≤ exp(c²/2 + x²/2) · exp(-2x²) = exp(c²/2) · exp(-3x²/2).
  have h_prod_le :
      (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2)
        ≤ Real.exp (c^2 / 2 + x^2 / 2) * Real.exp (-2 * x^2) :=
    mul_le_mul_of_nonneg_right h_diff_le h_exp_nn
  have h_simplify :
      Real.exp (c^2 / 2 + x^2 / 2) * Real.exp (-2 * x^2)
        = Real.exp (c^2 / 2) * Real.exp (-(3/2) * x^2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  -- Now divide by x ≥ 1: division by ≥ 1 only decreases.
  have h_chain :
      (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2)
        ≤ Real.exp (c^2 / 2) * Real.exp (-(3/2) * x^2) := by
    rw [← h_simplify]; exact h_prod_le
  have h_div_le : (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x
                ≤ (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / 1 := by
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg h_diff_nn h_exp_nn
    · exact zero_lt_one
    · exact hx.le
  rw [div_one] at h_div_le
  exact le_trans h_div_le h_chain

/-- Continuity of `x ↦ (cosh(c·x) - 1) · exp(-2x²) / x` on `Ioi 0`. -/
private lemma coshDiffM_integrand_continuousOn (c : ℝ) :
    ContinuousOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
      (Set.Ioi (0 : ℝ)) := by
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    refine Continuous.mul ?_ ?_
    · exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const
    · exact Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))
  · exact continuousOn_id
  · intro x hx; exact ne_of_gt hx

/-- Integrability of `coshDiffM` integrand on `Ioc 0 1` via constant bound. -/
private lemma coshDiffM_integrableOn_Ioc (c : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
      (Set.Ioc 0 1) := by
  have h_meas_Ioc : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  have h_cont :
      ContinuousOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
        (Set.Ioc 0 1) :=
    (coshDiffM_integrand_continuousOn c).mono (fun x hx => hx.1)
  have h_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
        (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    h_cont.aestronglyMeasurable h_meas_Ioc
  refine MeasureTheory.IntegrableOn.of_bound ?_ h_aestrong
    ((c^2 / 2) * Real.exp (c^2 / 2)) ?_
  · rw [Real.volume_Ioc]; simp
  · refine (MeasureTheory.ae_restrict_iff' h_meas_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have h_real_norm : ‖(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x‖
        = |(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x| := Real.norm_eq_abs _
    rw [h_real_norm]
    exact coshDiffM_integrand_bound_near_zero c hx.1 hx.2

/-- Integrability of `coshDiffM` integrand on `Ioi 1` via Gaussian dominator. -/
private lemma coshDiffM_integrableOn_Ioi_one (c : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
      (Set.Ioi 1) := by
  have h_meas_Ioi : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have h_cont :
      ContinuousOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
        (Set.Ioi 1) :=
    (coshDiffM_integrand_continuousOn c).mono
      (fun x (hx : x ∈ Set.Ioi (1:ℝ)) =>
        (Set.mem_Ioi).mpr (lt_trans zero_lt_one hx))
  have h_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
        (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
    h_cont.aestronglyMeasurable h_meas_Ioi
  refine MeasureTheory.Integrable.mono'
    (f := fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
    (g := fun x : ℝ => Real.exp (c^2 / 2) * Real.exp (-(3/2) * x^2))
    ?_ h_aestrong ?_
  · -- Dominator integrable on volume.restrict (Ioi 1).
    apply MeasureTheory.Integrable.integrableOn
    exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 3/2)).const_mul _
  · refine (MeasureTheory.ae_restrict_iff' h_meas_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have h_real_norm : ‖(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x‖
        = |(Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x| := Real.norm_eq_abs _
    rw [h_real_norm]
    exact coshDiffM_integrand_bound_at_infty c hx

/-! ### Trivial: `coshDiffM 0 = 0` -/

lemma coshDiffM_zero : coshDiffM 0 = 0 := by
  unfold coshDiffM
  have h_zero : ∀ x : ℝ, (Real.cosh (0 * x) - 1) * Real.exp (-2 * x^2) / x = 0 := by
    intro x
    rw [zero_mul, Real.cosh_zero, sub_self, zero_mul, zero_div]
  simp only [h_zero, MeasureTheory.integral_zero]

/-- The integrand of `coshDiffM` is integrable on `Ioi 0`. -/
lemma coshDiffM_integrable (c : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x)
      (Set.Ioi (0 : ℝ)) := by
  rw [show (Set.Ioi (0:ℝ)) = Set.Ioc 0 1 ∪ Set.Ioi 1 from
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)).symm]
  exact (coshDiffM_integrableOn_Ioc c).union (coshDiffM_integrableOn_Ioi_one c)

/-! ### Main identity: pair-combo of `coshDiffM` equals `R_beta` -/

/-- The pair-combo combination of `coshDiffM` values equals `R_beta β`. -/
theorem coshDiffM_pair_combo_eq_R_beta (β : ℝ) :
    (1/2 : ℝ) * coshDiffM (2 * β - Real.pi/3) +
    (1/2 : ℝ) * coshDiffM (2 - Real.pi/3 - 2 * β) -
    coshDiffM (1 - Real.pi/3) -
    coshDiffM (2 * β - 1) +
    coshDiffM 0 =
    R_beta β := by
  -- Set up the c-values: c₁ = c₃ + c₄, c₂ = c₃ - c₄ where c₃ = 1 - π/3, c₄ = 2β - 1.
  set c₃ : ℝ := 1 - Real.pi / 3 with hc3_def
  set c₄ : ℝ := 2 * β - 1 with hc4_def
  have h_c1 : 2 * β - Real.pi / 3 = c₃ + c₄ := by
    simp only [hc3_def, hc4_def]; ring
  have h_c2 : 2 - Real.pi / 3 - 2 * β = c₃ - c₄ := by
    simp only [hc3_def, hc4_def]; ring
  -- Step 1: kill the coshDiffM 0 term.
  rw [coshDiffM_zero, add_zero]
  -- Step 2: rewrite c₁, c₂.
  rw [h_c1, h_c2]
  -- Step 3: unfold coshDiffM and R_beta and use integral linearity.
  unfold coshDiffM R_beta
  -- Integrability of the four pieces.
  have h_int_c1 := coshDiffM_integrable (c₃ + c₄)
  have h_int_c2 := coshDiffM_integrable (c₃ - c₄)
  have h_int_c3 := coshDiffM_integrable c₃
  have h_int_c4 := coshDiffM_integrable c₄
  have h_int_c1h : MeasureTheory.Integrable
      (fun x : ℝ => (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) *
        Real.exp (-2 * x^2) / x))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    h_int_c1.const_mul ((1:ℝ)/2)
  have h_int_c2h : MeasureTheory.Integrable
      (fun x : ℝ => (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) *
        Real.exp (-2 * x^2) / x))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    h_int_c2.const_mul ((1:ℝ)/2)
  -- Use forward direction: ∫ (combined integrand) = sum of individual integrals.
  have h_combined :
      (∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
          (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x -
          (Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x) =
      (1/2 : ℝ) * (∫ x in Set.Ioi (0:ℝ), (Real.cosh ((c₃ + c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x) +
      (1/2 : ℝ) * (∫ x in Set.Ioi (0:ℝ), (Real.cosh ((c₃ - c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x) -
      (∫ x in Set.Ioi (0:ℝ), (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x) -
      (∫ x in Set.Ioi (0:ℝ), (Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x) := by
    -- Build up via integral_add / integral_sub from inside out.
    have step1 :
      ∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) =
      (∫ x in Set.Ioi (0:ℝ), (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x)) +
      ∫ x in Set.Ioi (0:ℝ), (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x) :=
      MeasureTheory.integral_add h_int_c1h h_int_c2h
    have step2 :
      (∫ x in Set.Ioi (0:ℝ), (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x)) =
      (1/2 : ℝ) * ∫ x in Set.Ioi (0:ℝ), (Real.cosh ((c₃ + c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x :=
      MeasureTheory.integral_const_mul _ _
    have step3 :
      (∫ x in Set.Ioi (0:ℝ), (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x)) =
      (1/2 : ℝ) * ∫ x in Set.Ioi (0:ℝ), (Real.cosh ((c₃ - c₄) * x) - 1) *
            Real.exp (-2 * x^2) / x :=
      MeasureTheory.integral_const_mul _ _
    have step4 :
      ∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
          (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x =
      (∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x))
      - ∫ x in Set.Ioi (0:ℝ), (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x :=
      MeasureTheory.integral_sub (h_int_c1h.add h_int_c2h) h_int_c3
    have step5 :
      ∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
          (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x -
          (Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x =
      (∫ x in Set.Ioi (0:ℝ),
          (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
          (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
          (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x)
      - ∫ x in Set.Ioi (0:ℝ), (Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x :=
      MeasureTheory.integral_sub
        ((h_int_c1h.add h_int_c2h).sub h_int_c3) h_int_c4
    rw [step5, step4, step1, step2, step3]
  rw [← h_combined]
  -- Step 4: now LHS = ∫ (combined integrand) and RHS = ∫ (R_beta integrand).
  -- Apply MeasureTheory.integral_congr_ae for the pointwise identity.
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  show (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
       (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
       (Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x -
       (Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x =
       (Real.cosh ((1 - Real.pi/3) * x) - 1) * (Real.cosh ((2 * β - 1) * x) - 1) *
        Real.exp (-2 * x^2) / x
  -- Use the pair-combo pointwise identity.
  have h_pt := cosh_pair_combo_pointwise c₃ c₄ x
  have h_eq :
      (1/2 : ℝ) * ((Real.cosh ((c₃ + c₄) * x) - 1) * Real.exp (-2 * x^2) / x) +
      (1/2 : ℝ) * ((Real.cosh ((c₃ - c₄) * x) - 1) * Real.exp (-2 * x^2) / x) -
      ((Real.cosh (c₃ * x) - 1) * Real.exp (-2 * x^2) / x) -
      ((Real.cosh (c₄ * x) - 1) * Real.exp (-2 * x^2) / x) =
      ((1/2 : ℝ) * (Real.cosh ((c₃ + c₄) * x) - 1) +
       (1/2) * (Real.cosh ((c₃ - c₄) * x) - 1) -
       (Real.cosh (c₃ * x) - 1) -
       (Real.cosh (c₄ * x) - 1)) * Real.exp (-2 * x^2) / x := by ring
  rw [h_eq, h_pt]

end ZD.PairComboResidueAtZero

end
