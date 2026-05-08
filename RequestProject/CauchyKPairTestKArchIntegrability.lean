import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianClosedForm
import RequestProject.CauchyKPairTestArchAudit
import RequestProject.CauchyKPairTestEngineering
import RequestProject.CauchyKPairTestKLevelEngineering

/-!
# Integrability hypotheses for `K_arch_four_bucket_target_holds`

This file discharges the four integrability hypotheses required by
`K_arch_four_bucket_target_holds` (in `CauchyKPairTestKLevelEngineering.lean`).
Each is an integrability of `Complex.exp(-2t²) · F(t, β)` on `Ioi 0`, where
`F` is one of the four bucket forms.

The strategy is uniform: each `F(t, β)` is bounded by `Real.exp(at) · poly(t)` for
constants `a`, and the Gaussian `Complex.exp(-2t²)` provides Gaussian decay
which dominates exponential growth.

Axiom footprint target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Real MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

/-! ## Auxiliary: uniform bound on `pair_cosh_gauss_test` -/

/-- **Uniform bound on `pair_cosh_gauss_test`.** For each `β`, there exists a
constant `M(β) ≥ 0` such that `0 ≤ pair_cosh_gauss_test β u ≤ M(β)` for all
`u ∈ ℝ`. The pointwise nonneg from `pair_cosh_gauss_test_nonneg`; the upper
bound uses the sinh-factored form and Gaussian dominance. -/
theorem pair_cosh_gauss_test_uniformly_bounded (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, pair_cosh_gauss_test β u ≤ M := by
  -- pair_cosh_gauss_test β u = 4 sinh²(α₁ u) sinh²(α_β u) ψ²(u)
  -- where α₁ = 1/2 - π/6, α_β = β - 1/2, ψ(u) = exp(-u²).
  -- |sinh(at)| ≤ exp(|a||t|)/2, so sinh²(at) ≤ exp(2|a||t|)/4.
  -- Product of sinh²: ≤ exp((|α₁| + |α_β|) · 2|t|) / 16.
  -- ψ²(u) = exp(-2u²). So the integrand ≤ exp(2(|α₁|+|α_β|)|t| - 2t²) / 4.
  -- The maximum of exp(at - 2t²) over t ∈ ℝ is exp(a²/8). Take a := 2(|α₁|+|α_β|).
  set α₁ : ℝ := 1/2 - Real.pi/6 with hα₁_def
  set α_β : ℝ := β - 1/2 with hα_β_def
  set a : ℝ := 2 * (|α₁| + |α_β|) with ha_def
  have ha_nn : 0 ≤ a := by
    rw [ha_def]; positivity
  refine ⟨Real.exp (a^2 / 8), Real.exp_nonneg _, fun u => ?_⟩
  -- Step 1: sinh-factor form.
  rw [pair_cosh_gauss_test, pairDetectorSqDiff_sinh_factor]
  -- 4 · sinh²(α₁ u) · sinh²(α_β u) · ψ²(u)
  show 4 * Real.sinh (α₁ * u)^2 * Real.sinh (α_β * u)^2 * (ψ_gaussian u)^2 ≤
       Real.exp (a^2 / 8)
  -- Step 2: bound sinh²(c u) ≤ exp(2|c||u|) / 4.
  have hsinh_sq : ∀ c u : ℝ, Real.sinh (c * u)^2 ≤ Real.exp (2 * |c| * |u|) / 4 := by
    intro c u
    have h_abs : |Real.sinh (c * u)| ≤ Real.exp (|c * u|) / 2 := by
      rw [Real.sinh_eq]
      have h_split : (Real.exp (c * u) - Real.exp (-(c * u))) / 2 =
          (Real.exp (c * u) - Real.exp (-(c * u))) * (1/2) := by ring
      rcases le_total 0 (c * u) with h | h
      · rw [abs_of_nonneg h]
        have h1 : Real.exp (-(c * u)) ≤ Real.exp (c * u) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ Real.exp (-(c * u)) := (Real.exp_pos _).le
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        rw [abs_sub_comm]
        rw [abs_of_nonpos (by linarith : Real.exp (-(c*u)) - Real.exp (c*u) ≤ 0)]
        ring_nf
        have : Real.exp (c*u) - Real.exp (-(c*u)) ≤ Real.exp (c*u) := by linarith
        linarith
      · rw [abs_of_nonpos h]
        have h1 : Real.exp (c * u) ≤ Real.exp (-(c * u)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ Real.exp (c * u) := (Real.exp_pos _).le
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        rw [abs_of_nonpos (by linarith : Real.exp (c*u) - Real.exp (-(c*u)) ≤ 0)]
        ring_nf
        have : Real.exp (-(c*u)) - Real.exp (c*u) ≤ Real.exp (-(c*u)) := by linarith
        linarith
    have h_sq : Real.sinh (c * u)^2 = |Real.sinh (c * u)|^2 := by
      rw [sq_abs]
    rw [h_sq]
    have h_mul_eq : |c * u| = |c| * |u| := abs_mul c u
    have h_pos : (0 : ℝ) ≤ |Real.sinh (c * u)| := abs_nonneg _
    have h_rhs_pos : (0 : ℝ) ≤ Real.exp (|c * u|) / 2 := by positivity
    calc |Real.sinh (c * u)|^2
        ≤ (Real.exp (|c * u|) / 2)^2 := by
          exact pow_le_pow_left₀ h_pos h_abs 2
      _ = Real.exp (|c * u|)^2 / 4 := by ring
      _ = Real.exp (2 * |c * u|) / 4 := by
          rw [show Real.exp (|c * u|)^2 = Real.exp (|c * u|) * Real.exp (|c * u|) from sq _]
          rw [← Real.exp_add]
          ring_nf
      _ = Real.exp (2 * |c| * |u|) / 4 := by rw [h_mul_eq]; ring_nf
  -- Step 3: combine.
  have h_α₁_bd := hsinh_sq α₁ u
  have h_α_β_bd := hsinh_sq α_β u
  have h_α₁_nn : 0 ≤ Real.sinh (α₁ * u)^2 := sq_nonneg _
  have h_α_β_nn : 0 ≤ Real.sinh (α_β * u)^2 := sq_nonneg _
  -- 4 · sinh²(α₁ u) · sinh²(α_β u) ≤ 4 · (exp(2|α₁||u|)/4) · (exp(2|α_β||u|)/4)
  --   = exp(2(|α₁|+|α_β|)|u|) / 4 = exp(a · |u|) / 4 (where a = 2(|α₁|+|α_β|)).
  have h_prod : 4 * Real.sinh (α₁ * u)^2 * Real.sinh (α_β * u)^2 ≤
      Real.exp (a * |u|) := by
    have h1 : 4 * Real.sinh (α₁ * u)^2 ≤ Real.exp (2 * |α₁| * |u|) := by
      have := h_α₁_bd
      linarith
    have h2 : Real.sinh (α_β * u)^2 ≤ Real.exp (2 * |α_β| * |u|) / 4 := h_α_β_bd
    have h_mul := mul_le_mul h1 h2 h_α_β_nn (by positivity :
        (0:ℝ) ≤ Real.exp (2 * |α₁| * |u|))
    have h_simplify : Real.exp (2 * |α₁| * |u|) * (Real.exp (2 * |α_β| * |u|) / 4) =
        Real.exp (a * |u|) / 4 := by
      rw [ha_def]
      rw [show 2 * (|α₁| + |α_β|) * |u| = 2 * |α₁| * |u| + 2 * |α_β| * |u| from by ring]
      rw [Real.exp_add]
      ring
    have h_4_chain : 4 * Real.sinh (α₁ * u)^2 * Real.sinh (α_β * u)^2 ≤
        Real.exp (a * |u|) / 4 := by
      calc 4 * Real.sinh (α₁ * u)^2 * Real.sinh (α_β * u)^2
          = (4 * Real.sinh (α₁ * u)^2) * Real.sinh (α_β * u)^2 := by ring
        _ ≤ Real.exp (2 * |α₁| * |u|) * (Real.exp (2 * |α_β| * |u|) / 4) := h_mul
        _ = Real.exp (a * |u|) / 4 := h_simplify
    have h_4_le : Real.exp (a * |u|) / 4 ≤ Real.exp (a * |u|) := by
      have := Real.exp_pos (a * |u|)
      linarith
    linarith
  -- Step 4: ψ²(u) = exp(-2u²).
  have h_psi_sq : (ψ_gaussian u)^2 = Real.exp (-2 * u^2) := by
    unfold ψ_gaussian
    rw [show Real.exp (-(u^2))^2 = Real.exp (-(u^2)) * Real.exp (-(u^2)) from sq _]
    rw [← Real.exp_add]
    ring_nf
  rw [h_psi_sq]
  have h_psi_nn : (0 : ℝ) ≤ Real.exp (-2 * u^2) := (Real.exp_pos _).le
  -- Final: 4 · sinh² · sinh² · exp(-2u²) ≤ exp(a|u|) · exp(-2u²) = exp(a|u| - 2u²) ≤ exp(a²/8).
  have h_combine : 4 * Real.sinh (α₁ * u)^2 * Real.sinh (α_β * u)^2 *
      Real.exp (-2 * u^2) ≤ Real.exp (a * |u|) * Real.exp (-2 * u^2) :=
    mul_le_mul_of_nonneg_right h_prod h_psi_nn
  refine h_combine.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- a · |u| - 2u² ≤ a²/8.
  -- Complete the square: a|u| - 2u² = -2(u² - (a/2)|u|) = -2(|u| - a/4)² + a²/8.
  -- Wait: -2(|u| - a/4)² = -2|u|² + a|u| - a²/8 = -2u² + a|u| - a²/8.
  -- So a|u| - 2u² = -2(|u| - a/4)² + a²/8 ≤ a²/8.
  have h_completing : a * |u| + -2 * u^2 = -2 * (|u| - a/4)^2 + a^2 / 8 := by
    have h_u_sq : u^2 = |u|^2 := (sq_abs u).symm
    rw [h_u_sq]
    ring
  rw [h_completing]
  -- -2 * (|u| - a/4)^2 + a^2/8 ≤ a^2/8 since -2 * (|u| - a/4)^2 ≤ 0.
  have h_neg : -2 * (|u| - a/4)^2 ≤ 0 := by
    have := sq_nonneg (|u| - a/4)
    nlinarith
  linarith

#print axioms pair_cosh_gauss_test_uniformly_bounded

/-! ## Auxiliary: Gaussian × Linear-Exponential is integrable on ℝ -/

/-- **Gaussian × linear-exp integrability on ℝ.** For any real `a`,
the function `t ↦ Real.exp (-2·t² + a·t)` is integrable on ℝ.

By completing the square: `-2t² + at = -2(t − a/4)² + a²/8`, so the integrand
is `exp(a²/8) · exp(-2(t − a/4)²)`, integrable as a translated Gaussian. -/
theorem integrable_exp_neg_two_sq_mul_linear (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-2 * t^2 + a * t)) := by
  -- exp(-2t² + at) = exp(a²/8) · exp(-2(t - a/4)²).
  have h_eq : ∀ t : ℝ, Real.exp (-2 * t^2 + a * t) =
      Real.exp (a^2 / 8) * Real.exp (-2 * (t - a/4)^2) := by
    intro t
    rw [← Real.exp_add]
    congr 1; ring
  rw [show (fun t : ℝ => Real.exp (-2 * t^2 + a * t)) =
      (fun t => Real.exp (a^2 / 8) * Real.exp (-2 * (t - a/4)^2)) from
    funext h_eq]
  -- exp(-2(t - a/4)²) integrable by translation of integrable_exp_neg_mul_sq.
  have h_base : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2)
  have h_translated : Integrable (fun t : ℝ => Real.exp (-2 * (t - a/4)^2)) := by
    have := h_base.comp_sub_right (a/4)
    simpa using this
  exact h_translated.const_mul _

#print axioms integrable_exp_neg_two_sq_mul_linear

/-- **Gaussian × bounded × linear-exp integrability on ℝ.** If `f : ℝ → ℂ`
is bounded by `C` and AEStronglyMeasurable, then
`t ↦ Complex.exp(-2t² + at) · f t` is integrable on ℝ. -/
theorem integrable_complex_exp_neg_two_sq_linear_mul_bounded
    (a : ℝ) (C : ℝ) (hC : 0 ≤ C) (f : ℝ → ℂ)
    (hf_meas : AEStronglyMeasurable f volume) (hf_bd : ∀ t : ℝ, ‖f t‖ ≤ C) :
    Integrable (fun t : ℝ => Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) * f t) := by
  -- Bound: ‖exp((-2t²+at):ℂ) · f t‖ = exp(-2t²+at) · ‖f t‖ ≤ exp(-2t²+at) · C.
  -- Dominated by C · exp(-2t² + at), which is integrable.
  apply MeasureTheory.Integrable.mono'
    (g := fun t => C * Real.exp (-2 * t^2 + a * t))
  · exact (integrable_exp_neg_two_sq_mul_linear a).const_mul C
  · -- AEStronglyMeasurable.
    have h_exp_meas : Continuous (fun t : ℝ =>
        Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ)) := by
      apply Complex.continuous_exp.comp
      apply Complex.continuous_ofReal.comp
      fun_prop
    exact h_exp_meas.aestronglyMeasurable.mul hf_meas
  · -- Pointwise bound.
    filter_upwards with t
    have h_exp_norm : ‖Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ)‖ =
        Real.exp (-2 * t^2 + a * t) := by
      rw [Complex.norm_exp]
      have h_re : ((-2 * t^2 + a * t : ℝ) : ℂ).re = -2 * t^2 + a * t :=
        Complex.ofReal_re _
      rw [h_re]
    have h_exp_nn : 0 ≤ Real.exp (-2 * t^2 + a * t) := (Real.exp_pos _).le
    rw [norm_mul, h_exp_norm]
    calc Real.exp (-2 * t^2 + a * t) * ‖f t‖
        ≤ Real.exp (-2 * t^2 + a * t) * C :=
          mul_le_mul_of_nonneg_left (hf_bd t) h_exp_nn
      _ = C * Real.exp (-2 * t^2 + a * t) := by ring

#print axioms integrable_complex_exp_neg_two_sq_linear_mul_bounded

/-! ## Auxiliary: Gaussian × exponential-of-|t| integrability -/

/-- **Gaussian × exp(c·|t|) integrability on ℝ.** For any real `c`,
the function `t ↦ Real.exp (-2·t²) · Real.exp (c·|t|)` is integrable on ℝ.

Bound: `c·|t| ≤ |c|·|t|`, and `exp(-2t² + |c|·|t|) ≤ exp(-2t² + |c|·t) + exp(-2t² + |c|·(-t))`
splits the |t| handling. Each piece is a translated Gaussian. -/
theorem integrable_exp_neg_two_sq_mul_exp_abs (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-2 * t^2) * Real.exp (|c| * |t|)) := by
  -- exp(|c|·|t|) ≤ exp(|c|·t) + exp(-|c|·t).
  apply MeasureTheory.Integrable.mono'
    (g := fun t => Real.exp (-2 * t^2 + |c| * t) + Real.exp (-2 * t^2 + (-|c|) * t))
  · exact (integrable_exp_neg_two_sq_mul_linear |c|).add
      (integrable_exp_neg_two_sq_mul_linear (-|c|))
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    have h_lhs_nn : 0 ≤ Real.exp (-2 * t^2) * Real.exp (|c| * |t|) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    have h_split : Real.exp (|c| * |t|) ≤
        Real.exp (|c| * t) + Real.exp (-|c| * t) := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]
        have h_exp_pos : 0 < Real.exp (-|c| * t) := Real.exp_pos _
        linarith
      · rw [abs_of_nonpos ht]
        have h_simplify : |c| * -t = -|c| * t := by ring
        rw [h_simplify]
        have h_exp_pos : 0 < Real.exp (|c| * t) := Real.exp_pos _
        linarith
    have h_g2_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
    have h_main : Real.exp (-2 * t^2) * Real.exp (|c| * |t|) ≤
        Real.exp (-2 * t^2) * (Real.exp (|c| * t) + Real.exp (-|c| * t)) :=
      mul_le_mul_of_nonneg_left h_split h_g2_nn
    have h_distribute : Real.exp (-2 * t^2) * (Real.exp (|c| * t) + Real.exp (-|c| * t)) =
        Real.exp (-2 * t^2 + |c| * t) + Real.exp (-2 * t^2 + (-|c|) * t) := by
      rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    rw [h_distribute] at h_main
    exact h_main

#print axioms integrable_exp_neg_two_sq_mul_exp_abs

/-! ## Auxiliary: continuity of `pair_cosh_gauss_test` -/

theorem pair_cosh_gauss_test_continuous (β : ℝ) :
    Continuous (fun u : ℝ => pair_cosh_gauss_test β u) := by
  unfold pair_cosh_gauss_test pairDetectorSqDiff
  unfold ZetaDefs.coshDetectorLeft ZetaDefs.coshDetectorRight ψ_gaussian
  fun_prop

#print axioms pair_cosh_gauss_test_continuous

/-! ## Integrability of each `Complex.exp(-2t²) · exp(linear) · pair_cosh_gauss_test β (exp(linear))` term -/

/-- **Building block lemma.** For any reals `a, b, c`:
`t ↦ Complex.exp((a·t : ℝ) : ℂ) · Real.exp(b·t) · pair_cosh_gauss_test β (Real.exp(c·t))`,
multiplied by `Complex.exp(-2t² : ℂ)`, is integrable on ℝ.

The inner factor is bounded by `M(β) · exp((a+b)·t)` (for real outer, since modulus
of `Complex.exp((a·t : ℝ) : ℂ)` is `exp(a·t)`). The Gaussian factor `exp(-2t²)`
dominates linear exponential growth. -/
theorem integrable_gaussian_pair_cosh_term
    (β : ℝ) (a b c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((-2 * t^2 + (a + b) * t : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ)) := by
  obtain ⟨M, hM_nn, hM_bd⟩ := pair_cosh_gauss_test_uniformly_bounded β
  apply integrable_complex_exp_neg_two_sq_linear_mul_bounded (a + b) M hM_nn
  · -- AEStronglyMeasurable.
    apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    exact (pair_cosh_gauss_test_continuous β).comp
      ((continuous_const.mul continuous_id).rexp)
  · -- ‖f t‖ ≤ M.
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h_nn : 0 ≤ pair_cosh_gauss_test β (Real.exp (c * t)) :=
      pair_cosh_gauss_test_nonneg β _
    rw [abs_of_nonneg h_nn]
    exact hM_bd _

#print axioms integrable_gaussian_pair_cosh_term

/-! ## Repackaged building block matching the arch closed-form term shape

The constant-carrier and rational-correction closed forms each contain terms
of shape `K_i · Complex.exp((a·t : ℝ) : ℂ) · ((Real.exp(b·t) : ℝ) : ℂ) ·
((pair_cosh_gauss_test β (Real.exp(c·t)) : ℝ) : ℂ)` (with constants `K_i`).

Multiplied by `Complex.exp(-2t² : ℂ)`, each such term is integrable on ℝ. -/
theorem integrable_gaussian_arch_term
    (β : ℝ) (a b c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
        (Complex.exp ((a * t : ℝ) : ℂ) *
          (((Real.exp (b * t) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ)))) := by
  -- Rewrite as Complex.exp((-2t² + (a+b)t : ℝ) : ℂ) · ((pair_cosh_gauss_test β (...) : ℝ) : ℂ).
  have h_eq : ∀ t : ℝ,
      Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
        (Complex.exp ((a * t : ℝ) : ℂ) *
          (((Real.exp (b * t) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ))) =
      Complex.exp ((-2 * t^2 + (a + b) * t : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ) := by
    intro t
    have h_exp_split : Complex.exp ((-2 * t^2 + (a + b) * t : ℝ) : ℂ) =
        Complex.exp ((-(2 * t^2) : ℝ) : ℂ) * Complex.exp ((a * t : ℝ) : ℂ) *
          ((Real.exp (b * t) : ℝ) : ℂ) := by
      rw [show ((-2 * t^2 + (a + b) * t : ℝ) : ℂ) =
          ((-(2 * t^2) : ℝ) : ℂ) + ((a * t : ℝ) : ℂ) + ((b * t : ℝ) : ℂ) from by
        push_cast; ring]
      rw [Complex.exp_add, Complex.exp_add]
      rw [Complex.ofReal_exp]
    rw [h_exp_split]
    ring
  rw [show (fun t : ℝ =>
      Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
        (Complex.exp ((a * t : ℝ) : ℂ) *
          (((Real.exp (b * t) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ)))) =
      (fun t : ℝ =>
        Complex.exp ((-2 * t^2 + (a + b) * t : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (c * t)) : ℝ) : ℂ)) from funext h_eq]
  exact integrable_gaussian_pair_cosh_term β a b c

#print axioms integrable_gaussian_arch_term

/-! ## Integrability of `Complex.exp(-2t²) · archConstantCarrierClosedForm t β`

Composing the 5 arch terms via `integrable_gaussian_arch_term`. -/

theorem integrable_gaussian_archConstantCarrier (β : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        archConstantCarrierClosedForm t β) := by
  -- archConstantCarrierClosedForm = -(log π + γ) · (T1 + T2 - T3 - T4 + T5).
  -- Each Tᵢ × Complex.exp(-2t²) is integrable by integrable_gaussian_arch_term
  -- (with appropriate (a,b,c)).
  -- T5 is the t=0-frozen pair_cosh_gauss_test β 1 — a constant.
  unfold archConstantCarrierClosedForm
  -- Rewrite Complex.exp(-2 * (t : ℂ)^2) = Complex.exp((-(2 * t^2) : ℝ) : ℂ).
  have h_exp_form : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) =
      Complex.exp ((-(2 * t^2) : ℝ) : ℂ) := by
    intro t
    congr 1
    push_cast
    ring
  -- Term 1: (1/2) · Complex.exp((-3t : ℝ) : ℂ) · 2π · ((Real.exp(2t) : ℝ) : ℂ) ·
  --   ((pair_cosh_gauss_test β (Real.exp(-2t)) : ℝ) : ℂ)
  --   matches integrable_gaussian_arch_term with (a, b, c) = (-3, 2, -2),
  --   times the constants (1/2) · 2π.
  have h_T1 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ((1/2 : ℂ) * Complex.exp (((-(3 * t) : ℝ)) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp (2 * t) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ)))) := by
    have h_base := integrable_gaussian_arch_term β (-3) 2 (-2)
    have h_eq : ∀ t : ℝ,
        Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
          (Complex.exp ((-3 * t : ℝ) : ℂ) *
            (((Real.exp (2 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-2 * t)) : ℝ) : ℂ))) =
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp (((-(3 * t) : ℝ)) : ℂ) *
            (((Real.exp (2 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ))) := by
      intro t
      rw [h_exp_form]
      have h_neg3 : ((-3 * t : ℝ) : ℂ) = ((-(3 * t) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h_neg3]
      have h_neg2 : Real.exp (-2 * t) = Real.exp (-(2 * t)) := by
        congr 1; ring
      rw [h_neg2]
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp (((-(3 * t) : ℝ)) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp (2 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ)))) =
        (fun t : ℝ =>
          ((1/2 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) *
          (Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
            (Complex.exp ((-3 * t : ℝ) : ℂ) *
              (((Real.exp (2 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-2 * t)) : ℝ) : ℂ))))) from by
      funext t
      rw [h_eq t]
      ring]
    exact h_base.const_mul _
  -- Term 2: (1/2) · Complex.exp((3t : ℝ) : ℂ) · 2π · ((Real.exp(-2t) : ℝ) : ℂ) ·
  --   ((pair_cosh_gauss_test β (Real.exp(2t)) : ℝ) : ℂ)
  --   matches with (a, b, c) = (3, -2, 2).
  have h_T2 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)))) := by
    have h_base := integrable_gaussian_arch_term β 3 (-2) 2
    have h_eq : ∀ t : ℝ,
        Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
          (Complex.exp ((3 * t : ℝ) : ℂ) *
            (((Real.exp (-2 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (2 * t)) : ℝ) : ℂ))) =
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((3 * t : ℝ) : ℂ) *
            (((Real.exp (-(2 * t)) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ))) := by
      intro t
      rw [h_exp_form]
      have h_neg2 : Real.exp (-2 * t) = Real.exp (-(2 * t)) := by
        congr 1; ring
      have h_negneg : Real.exp (2 * t) = Real.exp (-(-(2 * t))) := by
        congr 1; ring
      rw [h_neg2, h_negneg]
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)))) =
        (fun t : ℝ =>
          ((1/2 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) *
          (Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
            (Complex.exp ((3 * t : ℝ) : ℂ) *
              (((Real.exp (-2 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (2 * t)) : ℝ) : ℂ))))) from by
      funext t
      rw [h_eq t]
      ring]
    exact h_base.const_mul _
  -- Term 3: -Complex.exp((-(3/2)t : ℝ) : ℂ) · 2π · ((Real.exp(t) : ℝ) : ℂ) ·
  --   ((pair_cosh_gauss_test β (Real.exp(-t)) : ℝ) : ℂ)
  --   matches with (a, b, c) = (-3/2, 1, -1).
  have h_T3 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp t : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ)))) := by
    have h_base := integrable_gaussian_arch_term β (-3/2) 1 (-1)
    have h_eq : ∀ t : ℝ,
        Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
          (Complex.exp ((-3/2 * t : ℝ) : ℂ) *
            (((Real.exp (1 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-1 * t)) : ℝ) : ℂ))) =
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            (((Real.exp t : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ))) := by
      intro t
      rw [h_exp_form]
      have h_a : ((-3/2 * t : ℝ) : ℂ) = ((((-(3/2)) * t) : ℝ) : ℂ) := by
        push_cast; ring
      have h_b : Real.exp (1 * t) = Real.exp t := by congr 1; ring
      have h_c : Real.exp (-1 * t) = Real.exp (-t) := by congr 1; ring
      rw [h_a, h_b, h_c]
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp t : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ)))) =
        (fun t : ℝ =>
          ((2 * Real.pi : ℝ) : ℂ) *
          (Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
            (Complex.exp ((-3/2 * t : ℝ) : ℂ) *
              (((Real.exp (1 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-1 * t)) : ℝ) : ℂ))))) from by
      funext t
      rw [h_eq t]
      ring]
    exact h_base.const_mul _
  -- Term 4: -Complex.exp(((3/2)t : ℝ) : ℂ) · 2π · ((Real.exp(-t) : ℝ) : ℂ) ·
  --   ((pair_cosh_gauss_test β (Real.exp(t)) : ℝ) : ℂ)
  --   matches with (a, b, c) = (3/2, -1, 1).
  have h_T4 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp (-t) : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ)))) := by
    have h_base := integrable_gaussian_arch_term β (3/2) (-1) 1
    have h_eq : ∀ t : ℝ,
        Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
          (Complex.exp ((3/2 * t : ℝ) : ℂ) *
            (((Real.exp (-1 * t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (1 * t)) : ℝ) : ℂ))) =
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            (((Real.exp (-t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ))) := by
      intro t
      rw [h_exp_form]
      have h_a : ((3/2 * t : ℝ) : ℂ) = ((((3/2) * t) : ℝ) : ℂ) := by
        push_cast; ring
      have h_b : Real.exp (-1 * t) = Real.exp (-t) := by congr 1; ring
      have h_c : Real.exp (1 * t) = Real.exp (-(-t)) := by congr 1; ring
      rw [h_a, h_b, h_c]
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            (((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp (-t) : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ)))) =
        (fun t : ℝ =>
          ((2 * Real.pi : ℝ) : ℂ) *
          (Complex.exp ((-(2 * t^2) : ℝ) : ℂ) *
            (Complex.exp ((3/2 * t : ℝ) : ℂ) *
              (((Real.exp (-1 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (1 * t)) : ℝ) : ℂ))))) from by
      funext t
      rw [h_eq t]
      ring]
    exact h_base.const_mul _
  -- Term 5: 2π · ((Real.exp 0 : ℝ) : ℂ) · ((pair_cosh_gauss_test β (Real.exp(-0)) : ℝ) : ℂ)
  --   = 2π · pair_cosh_gauss_test β 1 (constant in t).
  -- Multiplied by Complex.exp(-2t² : ℂ): constant times Gaussian, integrable.
  have h_T5 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (((2 * Real.pi : ℝ) : ℂ) *
          ((Real.exp 0 : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ))) := by
    have h_const : ∀ t : ℝ,
        Complex.exp (-2 * (t : ℂ)^2) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp 0 : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp 0 : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ)) *
          Complex.exp (-2 * (t : ℂ)^2) := by
      intro t; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp 0 : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ))) =
        (fun t : ℝ => (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp 0 : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ)) *
            Complex.exp (-2 * (t : ℂ)^2)) from funext h_const]
    -- Need integrability of `t ↦ Complex.exp(-2 * (t : ℂ)^2)` on ℝ.
    -- Reduce to real-valued integrability of `Real.exp (-2 * t^2)` via Complex.ofReal_exp.
    have h_gauss : Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) := by
      have h_real : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) := by
        have := integrable_exp_neg_two_sq_mul_linear 0
        have h_eq : ∀ t : ℝ, Real.exp (-2 * t^2 + 0 * t) = Real.exp (-2 * t^2) := by
          intro t; congr 1; ring
        rw [show (fun t : ℝ => Real.exp (-2 * t^2)) =
            (fun t : ℝ => Real.exp (-2 * t^2 + 0 * t)) from
          funext (fun t => (h_eq t).symm)]
        exact this
      -- Complex integrability from real via Complex.ofReal_exp.
      have h_conv : ∀ t : ℝ,
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) = Complex.exp (-2 * (t : ℂ)^2) := by
        intro t
        rw [Complex.ofReal_exp]
        congr 1
        push_cast; ring
      rw [show (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) =
          (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) from funext (fun t => (h_conv t).symm)]
      exact h_real.ofReal
    exact h_gauss.const_mul _
  -- Sum: T1 + T2 - T3 - T4 + T5.
  -- archConstantCarrierClosedForm = -(log π + γ) · (T1_inner + T2_inner - T3_inner - T4_inner + T5_inner).
  -- Multiply by Complex.exp(-2t²) and distribute, getting:
  -- = -(log π + γ) · (T1 + T2 - T3 - T4 + T5).
  -- where Tᵢ has Complex.exp(-2t²) folded in.
  have h_combined :
      Integrable (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (2 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ)) +
            (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)) -
            Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp t : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ)) -
            Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ)) +
            ((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp 0 : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ))) := by
    -- Apply linearity: multiplication by Complex.exp(-2t²) distributes over the sum.
    have h_distribute : ∀ t : ℝ,
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (2 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ)) +
            (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)) -
            Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp t : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ)) -
            Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ)) +
            ((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp 0 : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ)) =
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (2 * t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ))) +
        Complex.exp (-2 * (t : ℂ)^2) *
          ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ))) -
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp t : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ))) -
        Complex.exp (-2 * (t : ℂ)^2) *
          (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
              (((2 * Real.pi : ℝ) : ℂ) *
                ((Real.exp (-t) : ℝ) : ℂ) *
                ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ))) +
        Complex.exp (-2 * (t : ℂ)^2) *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((Real.exp 0 : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ)) := by
      intro t; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) * _) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
                (((2 * Real.pi : ℝ) : ℂ) *
                  ((Real.exp (2 * t) : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ))) +
          Complex.exp (-2 * (t : ℂ)^2) *
            ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
                (((2 * Real.pi : ℝ) : ℂ) *
                  ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ))) -
          Complex.exp (-2 * (t : ℂ)^2) *
            (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
                (((2 * Real.pi : ℝ) : ℂ) *
                  ((Real.exp t : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ))) -
          Complex.exp (-2 * (t : ℂ)^2) *
            (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
                (((2 * Real.pi : ℝ) : ℂ) *
                  ((Real.exp (-t) : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ))) +
          Complex.exp (-2 * (t : ℂ)^2) *
            (((2 * Real.pi : ℝ) : ℂ) *
              ((Real.exp 0 : ℝ) : ℂ)
              * ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ))) from
      funext h_distribute]
    exact (((h_T1.add h_T2).sub h_T3).sub h_T4).add h_T5
  -- Multiply by outer constant -(log π + γ); apply via congr to handle bracketing.
  have h_outer := h_combined.const_mul (-(Complex.log (Real.pi : ℂ) +
      (Real.eulerMascheroniConstant : ℂ)))
  -- h_outer has shape `c * (Complex.exp(-2t²) * inner)`, but we want
  -- `Complex.exp(-2t²) * (c * inner)` — equal by associativity/commutativity.
  apply h_outer.congr
  filter_upwards with t
  ring

#print axioms integrable_gaussian_archConstantCarrier

/-! ## Uniform-in-α bound on `digammaRationalCorrectionIntegral` -/

/-- **Uniform bound on `digammaRationalCorrectionIntegral`.** For each `β`,
there is a constant `C(β) ≥ 0` such that
`‖digammaRationalCorrectionIntegral β α‖ ≤ C(β)` for every real `α`.

The bound is `∫ ‖1/((-1)+y·I) · pairTestMellin β((-1)+y·I)‖ dy`, which is
finite by `rationalCorrectionIntegrand_integrable β 0`, and independent of
`α` since the only `α`-dependence is the unimodular factor `exp(iy·α)`. -/
theorem digammaRationalCorrectionIntegral_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖digammaRationalCorrectionIntegral β α‖ ≤ C := by
  -- The α=0 form has integrand without the exp(iyα) factor (since exp(0)=1),
  -- but rationalCorrectionIntegrand_integrable takes α as parameter and yields
  -- integrability for each α; the integrand for α=0 is the un-modulated form.
  -- We use the L¹-norm of the un-modulated integrand as the uniform bound.
  set f : ℝ → ℂ := fun y =>
      Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf_def
  have hf_int : Integrable f := rationalCorrectionIntegrand_integrable β 0
  set C : ℝ := ∫ y : ℝ, ‖f y‖ with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C, hC_nn, fun α => ?_⟩
  -- ‖digammaRationalCorrectionIntegral β α‖ = ‖-∫ ...‖ = ‖∫ ...‖.
  unfold digammaRationalCorrectionIntegral
  rw [norm_neg]
  -- ‖∫ exp(iyα)·f(y) dy‖ ≤ ∫ ‖exp(iyα)·f(y)‖ dy = ∫ ‖f(y)‖ dy = C.
  have h_pointwise_eq : ∀ y : ℝ,
      ‖Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ = ‖f y‖ := by
    intro y
    rw [hf_def]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    rw [Complex.norm_exp, Complex.norm_exp]
    simp [Complex.mul_I_re, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
  -- ‖∫ g‖ ≤ ∫ ‖g‖ for integrable g.
  have h_bound :
      ‖∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      ∫ y : ℝ, ‖Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  refine h_bound.trans ?_
  apply le_of_eq
  rw [hC_def]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pointwise_eq)

#print axioms digammaRationalCorrectionIntegral_uniformly_bounded

/-! ## Continuity of `digammaRationalCorrectionIntegral β α` in `α` -/

/-- **Continuity of `digammaRationalCorrectionIntegral` in `α`.** Established
via `MeasureTheory.continuousAt_of_dominated` with dominator
`y ↦ ‖1/((-1)+y·I) · pairTestMellin β((-1)+y·I)‖`, which is integrable by
`rationalCorrectionIntegrand_integrable β 0`. -/
theorem digammaRationalCorrectionIntegral_continuous (β : ℝ) :
    Continuous (fun α : ℝ => digammaRationalCorrectionIntegral β α) := by
  -- digammaRationalCorrectionIntegral β α = -∫ y, exp((yα):ℂ * I) · ... dy.
  -- Continuous in α via dominated convergence.
  rw [continuous_iff_continuousAt]
  intro α₀
  unfold digammaRationalCorrectionIntegral
  -- Pull out the negative.
  refine ContinuousAt.neg ?_
  -- Apply continuousAt_of_dominated.
  set F : ℝ → ℝ → ℂ := fun α y =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hF_def
  set bound : ℝ → ℝ := fun y =>
      ‖(1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hbound_def
  -- AEStronglyMeasurable for each α (via existing integrability).
  have h_aemeas : ∀ᶠ (α : ℝ) in nhds α₀, AEStronglyMeasurable (F α) volume := by
    refine Filter.Eventually.of_forall (fun α => ?_)
    have h_int := rationalCorrectionIntegrand_integrable β α
    exact h_int.aestronglyMeasurable
  -- Pointwise bound: ‖F(α,y)‖ = bound(y) (since |exp(iyα)| = 1).
  have h_F_norm_eq : ∀ α y : ℝ, ‖F α y‖ = bound y := by
    intro α y
    rw [hF_def, hbound_def]
    have h_exp_norm : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h_re : (((y * α : ℝ) : ℂ) * I).re = 0 := by
        simp [Complex.mul_I_re, Complex.ofReal_im]
      rw [h_re, Real.exp_zero]
    have : ‖Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ *
        ‖(1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
      rw [show Complex.exp (((y * α : ℝ) : ℂ) * I) *
          (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
          Complex.exp (((y * α : ℝ) : ℂ) * I) *
            ((1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by
        ring]
      exact norm_mul _ _
    rw [this, h_exp_norm, one_mul]
  have h_bound : ∀ᶠ (α : ℝ) in nhds α₀, ∀ᵐ (y : ℝ) ∂volume, ‖F α y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall (fun α => ?_)
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact le_of_eq (h_F_norm_eq α y)
  -- bound integrable: use rationalCorrectionIntegrand_integrable β 0,
  -- whose integrand at α=0 is exactly `1 · (1/((-1)+yi)) · M`.
  have h_bound_int : Integrable bound := by
    have h_int_at_zero := rationalCorrectionIntegrand_integrable β 0
    -- bound y = ‖F 0 y‖ by h_F_norm_eq.
    have h_eq : ∀ y : ℝ, bound y = ‖F 0 y‖ := by
      intro y; exact (h_F_norm_eq 0 y).symm
    rw [show bound = (fun y => ‖F 0 y‖) from funext h_eq]
    -- F 0 y is the rationalCorrection integrand at α=0, which is integrable.
    rw [hF_def]
    exact h_int_at_zero.norm
  -- Pointwise continuity: F(·, y) is continuous in α.
  have h_pointwise_cont : ∀ᵐ (y : ℝ) ∂volume, ContinuousAt (fun α => F α y) α₀ := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [hF_def]
    refine ContinuousAt.mul ?_ continuousAt_const
    refine ContinuousAt.mul ?_ continuousAt_const
    -- α ↦ exp((yα):ℂ * I) is continuous in α.
    refine Complex.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)
  exact MeasureTheory.continuousAt_of_dominated h_aemeas h_bound h_bound_int
    h_pointwise_cont

#print axioms digammaRationalCorrectionIntegral_continuous

/-! ## Building block: `Complex.exp(-2t² + a·t : ℝ) · digammaRationalCorrectionIntegral β (c·t)` integrable -/

theorem integrable_gaussian_digamma_rational_term
    (β : ℝ) (a c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
        digammaRationalCorrectionIntegral β (c * t)) := by
  obtain ⟨C, hC_nn, hC_bd⟩ := digammaRationalCorrectionIntegral_uniformly_bounded β
  apply integrable_complex_exp_neg_two_sq_linear_mul_bounded a C hC_nn
  · -- AEStronglyMeasurable: t ↦ digammaRationalCorrectionIntegral β (c · t) is
    -- continuous (composition of continuous with linear), hence AEStronglyMeasurable.
    exact ((digammaRationalCorrectionIntegral_continuous β).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro t
    exact hC_bd (c * t)

#print axioms integrable_gaussian_digamma_rational_term

/-! ## Helper: reshaping a single rational-correction term -/

/-- For each `(a, c)`, the function
`t ↦ Complex.exp(-2t² : ℂ) · Complex.exp((a·t : ℝ) : ℂ) ·
  digammaRationalCorrectionIntegral β (c·t)` is integrable on ℝ. -/
private theorem integrable_gauss_outer_exp_digamma
    (β : ℝ) (a c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        digammaRationalCorrectionIntegral β (c * t)) := by
  have h_base := integrable_gaussian_digamma_rational_term β a c
  have h_eq : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        digammaRationalCorrectionIntegral β (c * t) =
      Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
        digammaRationalCorrectionIntegral β (c * t) := by
    intro t
    have h_split : Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) =
        Complex.exp (-2 * (t : ℂ)^2) * Complex.exp ((a * t : ℝ) : ℂ) := by
      rw [show ((-2 * t^2 + a * t : ℝ) : ℂ) =
          (-2 * (t : ℂ)^2) + ((a * t : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.exp_add _ _
    rw [h_split]
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        digammaRationalCorrectionIntegral β (c * t)) =
      (fun t : ℝ =>
        Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
          digammaRationalCorrectionIntegral β (c * t)) from funext h_eq]
  exact h_base

#print axioms integrable_gauss_outer_exp_digamma

/-! ## Integrability of `Complex.exp(-2t²) · archRationalCorrectionClosedForm t β` -/

theorem integrable_gaussian_archRationalCorrection (β : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        archRationalCorrectionClosedForm t β) := by
  unfold archRationalCorrectionClosedForm
  -- Each of the 5 terms in archRationalCorrectionClosedForm equals
  --   K_i · Complex.exp((a_i · t : ℝ) : ℂ) · digammaRationalCorrectionIntegral β (c_i · t)
  -- (where the `-∫` factor is absorbed into the `digammaRationalCorrectionIntegral`
  -- definition, which already contains the leading minus sign).
  -- Outer constants K_i: (1/2, 1/2, -1, -1, 1) (the ± signs in the closed form).
  -- The (a_i, c_i) pairs: (-3, 2), (3, -2), (-3/2, 1), (3/2, -1), (0, 0).

  -- Step 1: rewrite each `-∫ y, ... dy` as `digammaRationalCorrectionIntegral β (c·t)`.
  -- Pointwise reshape:
  have h_reshape : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (2 * t) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
          (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (-(2 * t)) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
          (-∫ y : ℝ, Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
            (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (2 * t))) +
      ((1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (-(2 * t)))) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          digammaRationalCorrectionIntegral β t) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          digammaRationalCorrectionIntegral β (-t)) +
      (Complex.exp (-2 * (t : ℂ)^2) *
        digammaRationalCorrectionIntegral β 0) := by
    intro t
    unfold digammaRationalCorrectionIntegral
    -- The 5 -∫ ... dy expressions match digammaRationalCorrectionIntegral β c at:
    -- c = 2t, -(2t), t, -t, 0 respectively.
    -- For term 5: (y*0 : ℝ) = 0, and there's no outer Complex.exp factor,
    -- so it matches with the `Complex.exp((0*t:ℝ):ℂ) = 1` form.
    have h5_simp : Complex.exp (-2 * (t : ℂ)^2) *
        digammaRationalCorrectionIntegral β 0 =
        Complex.exp (-2 * (t : ℂ)^2) *
          (-∫ y : ℝ, Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
            (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      rfl
    ring
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (2 * t) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
          (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (-(2 * t)) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            (-∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
              (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
          (-∫ y : ℝ, Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
            (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))) =
      (fun t : ℝ =>
        ((1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (2 * t))) +
        ((1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (-(2 * t)))) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β t) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (-t)) +
        (Complex.exp (-2 * (t : ℂ)^2) *
          digammaRationalCorrectionIntegral β 0)) from funext h_reshape]
  -- Each term integrable.
  have h_T1 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (2 * t))) := by
    have h := integrable_gauss_outer_exp_digamma β (-3) 2
    have h_match : ∀ t : ℝ,
        Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (2 * t) =
        Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (2 * t) := by
      intro t
      congr 2
      push_cast; ring_nf
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (2 * t))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (2 * t))) from
      funext (fun t => by rw [h_match t])]
    exact h.const_mul _
  have h_T2 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (-(2 * t)))) := by
    have h := integrable_gauss_outer_exp_digamma β 3 (-2)
    have h_match : ∀ t : ℝ, digammaRationalCorrectionIntegral β (-2 * t) =
        digammaRationalCorrectionIntegral β (-(2 * t)) := by
      intro t; congr 1; ring
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (-(2 * t)))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (-2 * t))) from
      funext (fun t => by rw [h_match t])]
    exact h.const_mul _
  have h_T3 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          digammaRationalCorrectionIntegral β t) := by
    have h := integrable_gauss_outer_exp_digamma β (-3/2) 1
    have h_a : ∀ t : ℝ, ((-3/2 * t : ℝ) : ℂ) = ((((-(3/2)) * t) : ℝ) : ℂ) := by
      intro t; push_cast; ring
    have h_c : ∀ t : ℝ, digammaRationalCorrectionIntegral β (1 * t) =
        digammaRationalCorrectionIntegral β t := by
      intro t; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β t) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3/2 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T4 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          digammaRationalCorrectionIntegral β (-t)) := by
    have h := integrable_gauss_outer_exp_digamma β (3/2) (-1)
    have h_a : ∀ t : ℝ, ((3/2 * t : ℝ) : ℂ) = ((((3/2) * t) : ℝ) : ℂ) := by
      intro t; push_cast; ring
    have h_c : ∀ t : ℝ, digammaRationalCorrectionIntegral β (-1 * t) =
        digammaRationalCorrectionIntegral β (-t) := by
      intro t; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            digammaRationalCorrectionIntegral β (-t)) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3/2 * t : ℝ) : ℂ) *
              digammaRationalCorrectionIntegral β (-1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T5 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        digammaRationalCorrectionIntegral β 0) := by
    -- Constant in t (digammaRationalCorrectionIntegral β 0 doesn't depend on t).
    -- Reduces to integrability of `Complex.exp(-2t²)` times a constant.
    have h_gauss : Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) := by
      have h_real : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) := by
        have := integrable_exp_neg_two_sq_mul_linear 0
        have h_eq : ∀ t : ℝ, Real.exp (-2 * t^2 + 0 * t) = Real.exp (-2 * t^2) := by
          intro t; congr 1; ring
        rw [show (fun t : ℝ => Real.exp (-2 * t^2)) =
            (fun t : ℝ => Real.exp (-2 * t^2 + 0 * t)) from
          funext (fun t => (h_eq t).symm)]
        exact this
      have h_conv : ∀ t : ℝ,
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) = Complex.exp (-2 * (t : ℂ)^2) := by
        intro t
        rw [Complex.ofReal_exp]
        congr 1
        push_cast; ring
      rw [show (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) =
          (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) from
        funext (fun t => (h_conv t).symm)]
      exact h_real.ofReal
    exact h_gauss.mul_const _
  -- Combine the 5 terms.
  exact (((h_T1.add h_T2).sub h_T3).sub h_T4).add h_T5

#print axioms integrable_gaussian_archRationalCorrection

/-! ## Generic α-parametrized integral abstraction

For the pole towers, we need continuity and uniform bound on functions
`α ↦ ∫ y, exp((y·α : ℝ) · I) · g(y) dy` for various `g`.  The proofs are all
the same template — wrap in a generic lemma. -/

/-- **Continuity of α-parametrized integral with unimodular kernel.**
For any integrable `g : ℝ → ℂ`, the function
`α ↦ ∫ y, Complex.exp((y·α : ℝ) : ℂ * I) · g(y) dy` is continuous. -/
theorem alpha_parametrized_integral_continuous (g : ℝ → ℂ) (h_g : Integrable g) :
    Continuous (fun α : ℝ =>
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y) := by
  rw [continuous_iff_continuousAt]
  intro α₀
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun y => ‖g y‖)
  · refine Filter.Eventually.of_forall (fun α => ?_)
    refine AEStronglyMeasurable.mul ?_ h_g.aestronglyMeasurable
    apply Continuous.aestronglyMeasurable
    apply Complex.continuous_exp.comp
    apply Continuous.mul _ continuous_const
    exact Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
  · refine Filter.Eventually.of_forall (fun α => ?_)
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [norm_mul]
    have h_exp : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h_re : (((y * α : ℝ) : ℂ) * I).re = 0 := by
        simp [Complex.mul_I_re]
      rw [h_re, Real.exp_zero]
    rw [h_exp, one_mul]
  · exact h_g.norm
  · refine Filter.Eventually.of_forall (fun y => ?_)
    refine ContinuousAt.mul ?_ continuousAt_const
    refine Complex.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)

#print axioms alpha_parametrized_integral_continuous

/-- **Uniform bound on α-parametrized integral with unimodular kernel.**
The L¹ norm of `g` provides an α-independent upper bound. -/
theorem alpha_parametrized_integral_uniformly_bounded
    (g : ℝ → ℂ) (h_g : Integrable g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y‖ ≤ C := by
  refine ⟨∫ y : ℝ, ‖g y‖, ?_, fun α => ?_⟩
  · exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  · refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    apply le_of_eq
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    show ‖Complex.exp (((y * α : ℝ) : ℂ) * I) * g y‖ = ‖g y‖
    rw [norm_mul]
    have h_exp : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h_re : (((y * α : ℝ) : ℂ) * I).re = 0 := by
        simp [Complex.mul_I_re]
      rw [h_re, Real.exp_zero]
    rw [h_exp, one_mul]

#print axioms alpha_parametrized_integral_uniformly_bounded

/-! ## Applying the abstraction: digamma half-arg integrals

The functions `α ↦ digammaPosHalfShiftedArchIntegralLeft β α` and
`α ↦ digammaPosHalfShiftedArchIntegralRight β α` and
`α ↦ constantLogPiShiftedArchIntegral β α` are continuous and uniformly
bounded — derived from the abstraction. -/

theorem digammaPosHalfShiftedArchIntegralLeft_continuous (β : ℝ) :
    Continuous (fun α : ℝ => digammaPosHalfShiftedArchIntegralLeft β α) := by
  unfold digammaPosHalfShiftedArchIntegralLeft
  refine Continuous.const_mul ?_ _
  -- Inner: α ↦ ∫ y, exp((y·α):ℂ * I) · ψ((1/2)+(y/2)·I) · M(β,(-1)+yi) dy.
  -- Apply alpha_parametrized_integral_continuous with
  -- g(y) = ψ((1/2)+(y/2)·I) · M(β,(-1)+yi).
  -- The integrand at α=0 is ‖∫ ψ · M‖ < ∞ by digammaPosHalfShiftedArchIntegrand_left_integrable β 0.
  set g : ℝ → ℂ := fun y =>
      Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hg_def
  have h_g_int : Integrable g := by
    have h_at_zero := digammaPosHalfShiftedArchIntegrand_left_integrable β 0
    have h_eq : ∀ y : ℝ,
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = g y := by
      intro y
      rw [hg_def]
      have h_zero : ((y * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by push_cast; ring
      rw [h_zero]
      rw [zero_mul, Complex.exp_zero, one_mul]
    rw [show g = (fun y =>
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from
      funext (fun y => (h_eq y).symm)]
    exact h_at_zero
  have h_cont := alpha_parametrized_integral_continuous g h_g_int
  -- The original integrand `exp(iyα) · ψ · M` equals `exp(iyα) · g`.
  have h_unfold : (fun α : ℝ =>
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun α : ℝ =>
        ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y) := by
    funext α
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hg_def]
    ring
  rw [h_unfold]
  exact h_cont

#print axioms digammaPosHalfShiftedArchIntegralLeft_continuous

theorem digammaPosHalfShiftedArchIntegralLeft_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖digammaPosHalfShiftedArchIntegralLeft β α‖ ≤ C := by
  set g : ℝ → ℂ := fun y =>
      Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hg_def
  have h_g_int : Integrable g := by
    have h_at_zero := digammaPosHalfShiftedArchIntegrand_left_integrable β 0
    have h_eq : ∀ y : ℝ,
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = g y := by
      intro y
      rw [hg_def]
      have h_zero : ((y * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by push_cast; ring
      rw [h_zero]
      rw [zero_mul, Complex.exp_zero, one_mul]
    rw [show g = (fun y =>
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from
      funext (fun y => (h_eq y).symm)]
    exact h_at_zero
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    alpha_parametrized_integral_uniformly_bounded g h_g_int
  refine ⟨(1/2 : ℝ) * C, by positivity, fun α => ?_⟩
  unfold digammaPosHalfShiftedArchIntegralLeft
  -- ‖(1/2) · ∫ exp(iyα) · ψ · M dy‖ = (1/2) · ‖∫ exp(iyα) · g dy‖ ≤ (1/2) · C.
  have h_unfold : ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hg_def]; ring
  rw [h_unfold]
  rw [norm_mul]
  have h_half : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    rw [show ((1/2 : ℝ) : ℝ) = (1/2 : ℝ) from rfl]
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_half]
  have h_int_le := hC_bd α
  nlinarith [h_int_le, hC_nn,
    norm_nonneg (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y)]

#print axioms digammaPosHalfShiftedArchIntegralLeft_uniformly_bounded

/-! ## constantLogPiShiftedArchIntegral continuity + uniform bound -/

/-- Integrability of `pairTestMellin β ((-1) + y·I)` in y (used as `g`). -/
private theorem pairTestMellin_neg_one_integrable (β : ℝ) :
    Integrable (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h := LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
  convert h using 1

theorem constantLogPiShiftedArchIntegral_continuous (β : ℝ) :
    Continuous (fun α : ℝ => constantLogPiShiftedArchIntegral β α) := by
  unfold constantLogPiShiftedArchIntegral
  exact alpha_parametrized_integral_continuous _ (pairTestMellin_neg_one_integrable β)

#print axioms constantLogPiShiftedArchIntegral_continuous

theorem constantLogPiShiftedArchIntegral_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖constantLogPiShiftedArchIntegral β α‖ ≤ C := by
  unfold constantLogPiShiftedArchIntegral
  exact alpha_parametrized_integral_uniformly_bounded _ (pairTestMellin_neg_one_integrable β)

#print axioms constantLogPiShiftedArchIntegral_uniformly_bounded

/-! ## digammaPosHalfShiftedArchIntegralRight continuity + uniform bound

(Mirroring digammaPosHalfShiftedArchIntegralLeft for the right pole tower.) -/

theorem digammaPosHalfShiftedArchIntegralRight_continuous (β : ℝ) :
    Continuous (fun α : ℝ => digammaPosHalfShiftedArchIntegralRight β α) := by
  unfold digammaPosHalfShiftedArchIntegralRight
  refine Continuous.const_mul ?_ _
  set g : ℝ → ℂ := fun y =>
      Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hg_def
  have h_g_int : Integrable g := by
    have h_at_zero := digammaPosHalfShiftedArchIntegrand_right_integrable β 0
    have h_eq : ∀ y : ℝ,
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = g y := by
      intro y
      rw [hg_def]
      have h_zero : ((y * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by push_cast; ring
      rw [h_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [show g = (fun y =>
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from
      funext (fun y => (h_eq y).symm)]
    exact h_at_zero
  have h_cont := alpha_parametrized_integral_continuous g h_g_int
  have h_unfold : (fun α : ℝ =>
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun α : ℝ =>
        ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y) := by
    funext α
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hg_def]; ring
  rw [h_unfold]
  exact h_cont

#print axioms digammaPosHalfShiftedArchIntegralRight_continuous

theorem digammaPosHalfShiftedArchIntegralRight_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖digammaPosHalfShiftedArchIntegralRight β α‖ ≤ C := by
  set g : ℝ → ℂ := fun y =>
      Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hg_def
  have h_g_int : Integrable g := by
    have h_at_zero := digammaPosHalfShiftedArchIntegrand_right_integrable β 0
    have h_eq : ∀ y : ℝ,
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = g y := by
      intro y
      rw [hg_def]
      have h_zero : ((y * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by push_cast; ring
      rw [h_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [show g = (fun y =>
        Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
          Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from
      funext (fun y => (h_eq y).symm)]
    exact h_at_zero
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    alpha_parametrized_integral_uniformly_bounded g h_g_int
  refine ⟨(1/2 : ℝ) * C, by positivity, fun α => ?_⟩
  unfold digammaPosHalfShiftedArchIntegralRight
  have h_unfold : ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hg_def]; ring
  rw [h_unfold]
  rw [norm_mul]
  have h_half : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_half]
  have h_int_le := hC_bd α
  nlinarith [h_int_le, hC_nn,
    norm_nonneg (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * g y)]

#print axioms digammaPosHalfShiftedArchIntegralRight_uniformly_bounded

/-! ## Tower-sum continuity + uniform bound via pole-series swap

By `digammaPosHalfLeft_pole_series_target_holds`,
`Σ' k, digammaPoleKernelLeft k β α = digammaPosHalfShiftedArchIntegralLeft β α
  + (γ/2) · constantLogPiShiftedArchIntegral β α`.
Both pieces on the RHS are continuous and uniformly bounded; hence so is the
LHS. -/

theorem tower_sum_left_continuous (β : ℝ) :
    Continuous (fun α : ℝ => ∑' k : ℕ, digammaPoleKernelLeft k β α) := by
  have h_eq : ∀ α : ℝ, ∑' k : ℕ, digammaPoleKernelLeft k β α =
      digammaPosHalfShiftedArchIntegralLeft β α +
        (Real.eulerMascheroniConstant : ℂ) / 2 *
          constantLogPiShiftedArchIntegral β α := by
    intro α
    have h := digammaPosHalfLeft_pole_series_target_holds β α
    unfold digammaPosHalfLeft_pole_series_target at h
    linear_combination -h
  rw [show (fun α : ℝ => ∑' k : ℕ, digammaPoleKernelLeft k β α) =
      (fun α : ℝ =>
        digammaPosHalfShiftedArchIntegralLeft β α +
          (Real.eulerMascheroniConstant : ℂ) / 2 *
            constantLogPiShiftedArchIntegral β α) from funext h_eq]
  refine Continuous.add (digammaPosHalfShiftedArchIntegralLeft_continuous β) ?_
  exact Continuous.const_mul (constantLogPiShiftedArchIntegral_continuous β) _

#print axioms tower_sum_left_continuous

theorem tower_sum_left_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖∑' k : ℕ, digammaPoleKernelLeft k β α‖ ≤ C := by
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    digammaPosHalfShiftedArchIntegralLeft_uniformly_bounded β
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    constantLogPiShiftedArchIntegral_uniformly_bounded β
  set γc : ℝ := |Real.eulerMascheroniConstant| / 2 with hγc_def
  have hγc_nn : 0 ≤ γc := by rw [hγc_def]; positivity
  refine ⟨C₁ + γc * C₂, by positivity, fun α => ?_⟩
  have h_eq : ∑' k : ℕ, digammaPoleKernelLeft k β α =
      digammaPosHalfShiftedArchIntegralLeft β α +
        (Real.eulerMascheroniConstant : ℂ) / 2 *
          constantLogPiShiftedArchIntegral β α := by
    have h := digammaPosHalfLeft_pole_series_target_holds β α
    unfold digammaPosHalfLeft_pole_series_target at h
    linear_combination -h
  rw [h_eq]
  refine (norm_add_le _ _).trans ?_
  have hineq1 := hC₁_bd α
  have hineq2 := hC₂_bd α
  have h_factor : ‖(Real.eulerMascheroniConstant : ℂ) / 2 *
        constantLogPiShiftedArchIntegral β α‖ ≤ γc * C₂ := by
    rw [norm_mul]
    have h_const_norm : ‖(Real.eulerMascheroniConstant : ℂ) / 2‖ = γc := by
      rw [hγc_def]
      rw [show ((Real.eulerMascheroniConstant : ℂ) / 2) =
          ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
    rw [h_const_norm]
    exact mul_le_mul_of_nonneg_left hineq2 hγc_nn
  linarith

#print axioms tower_sum_left_uniformly_bounded

theorem tower_sum_right_continuous (β : ℝ) :
    Continuous (fun α : ℝ => ∑' k : ℕ, digammaPoleKernelRight k β α) := by
  have h_eq : ∀ α : ℝ, ∑' k : ℕ, digammaPoleKernelRight k β α =
      digammaPosHalfShiftedArchIntegralRight β α +
        (Real.eulerMascheroniConstant : ℂ) / 2 *
          constantLogPiShiftedArchIntegral β α := by
    intro α
    have h := digammaPosHalfRight_pole_series_target_holds β α
    unfold digammaPosHalfRight_pole_series_target at h
    linear_combination -h
  rw [show (fun α : ℝ => ∑' k : ℕ, digammaPoleKernelRight k β α) =
      (fun α : ℝ =>
        digammaPosHalfShiftedArchIntegralRight β α +
          (Real.eulerMascheroniConstant : ℂ) / 2 *
            constantLogPiShiftedArchIntegral β α) from funext h_eq]
  refine Continuous.add (digammaPosHalfShiftedArchIntegralRight_continuous β) ?_
  exact Continuous.const_mul (constantLogPiShiftedArchIntegral_continuous β) _

#print axioms tower_sum_right_continuous

theorem tower_sum_right_uniformly_bounded (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ,
      ‖∑' k : ℕ, digammaPoleKernelRight k β α‖ ≤ C := by
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    digammaPosHalfShiftedArchIntegralRight_uniformly_bounded β
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    constantLogPiShiftedArchIntegral_uniformly_bounded β
  set γc : ℝ := |Real.eulerMascheroniConstant| / 2 with hγc_def
  have hγc_nn : 0 ≤ γc := by rw [hγc_def]; positivity
  refine ⟨C₁ + γc * C₂, by positivity, fun α => ?_⟩
  have h_eq : ∑' k : ℕ, digammaPoleKernelRight k β α =
      digammaPosHalfShiftedArchIntegralRight β α +
        (Real.eulerMascheroniConstant : ℂ) / 2 *
          constantLogPiShiftedArchIntegral β α := by
    have h := digammaPosHalfRight_pole_series_target_holds β α
    unfold digammaPosHalfRight_pole_series_target at h
    linear_combination -h
  rw [h_eq]
  refine (norm_add_le _ _).trans ?_
  have hineq1 := hC₁_bd α
  have hineq2 := hC₂_bd α
  have h_factor : ‖(Real.eulerMascheroniConstant : ℂ) / 2 *
        constantLogPiShiftedArchIntegral β α‖ ≤ γc * C₂ := by
    rw [norm_mul]
    have h_const_norm : ‖(Real.eulerMascheroniConstant : ℂ) / 2‖ = γc := by
      rw [hγc_def]
      rw [show ((Real.eulerMascheroniConstant : ℂ) / 2) =
          ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
    rw [h_const_norm]
    exact mul_le_mul_of_nonneg_left hineq2 hγc_nn
  linarith

#print axioms tower_sum_right_uniformly_bounded

/-! ## Building blocks for left/right tower terms (Gaussian × exp(linear) × tower-sum) -/

private theorem integrable_gauss_outer_exp_tower_left
    (β : ℝ) (a c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelLeft k β (c * t)) := by
  obtain ⟨C, hC_nn, hC_bd⟩ := tower_sum_left_uniformly_bounded β
  -- Reshape outer Gaussian × exp.
  have h_eq : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelLeft k β (c * t) =
      Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelLeft k β (c * t) := by
    intro t
    have h_split : Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) =
        Complex.exp (-2 * (t : ℂ)^2) * Complex.exp ((a * t : ℝ) : ℂ) := by
      rw [show ((-2 * t^2 + a * t : ℝ) : ℂ) =
          (-2 * (t : ℂ)^2) + ((a * t : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.exp_add _ _
    rw [h_split]
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelLeft k β (c * t)) =
      (fun t : ℝ =>
        Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelLeft k β (c * t)) from funext h_eq]
  apply integrable_complex_exp_neg_two_sq_linear_mul_bounded a C hC_nn
  · exact ((tower_sum_left_continuous β).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro t; exact hC_bd (c * t)

#print axioms integrable_gauss_outer_exp_tower_left

private theorem integrable_gauss_outer_exp_tower_right
    (β : ℝ) (a c : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelRight k β (c * t)) := by
  obtain ⟨C, hC_nn, hC_bd⟩ := tower_sum_right_uniformly_bounded β
  have h_eq : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelRight k β (c * t) =
      Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelRight k β (c * t) := by
    intro t
    have h_split : Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) =
        Complex.exp (-2 * (t : ℂ)^2) * Complex.exp ((a * t : ℝ) : ℂ) := by
      rw [show ((-2 * t^2 + a * t : ℝ) : ℂ) =
          (-2 * (t : ℂ)^2) + ((a * t : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.exp_add _ _
    rw [h_split]
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((a * t : ℝ) : ℂ) *
        ∑' k : ℕ, digammaPoleKernelRight k β (c * t)) =
      (fun t : ℝ =>
        Complex.exp ((-2 * t^2 + a * t : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelRight k β (c * t)) from funext h_eq]
  apply integrable_complex_exp_neg_two_sq_linear_mul_bounded a C hC_nn
  · exact ((tower_sum_right_continuous β).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro t; exact hC_bd (c * t)

#print axioms integrable_gauss_outer_exp_tower_right

/-! ## Integrability of `Complex.exp(-2t²) · ∑' k, leftPoleTowerK2Aggregator k t β` -/

theorem integrable_gaussian_archLeftPoleTower (β : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, leftPoleTowerK2Aggregator k t β)) := by
  -- Pull tsum-of-5-terms apart via tsum-linearity, then apply
  -- integrable_gauss_outer_exp_tower_left for each of the 5 (a, c) pairs.
  have h_reshape : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, leftPoleTowerK2Aggregator k t β) =
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (2 * t)) +
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t))) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelLeft k β t) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelLeft k β (-t)) +
      (Complex.exp (-2 * (t : ℂ)^2) *
        ∑' k : ℕ, digammaPoleKernelLeft k β 0) := by
    intro t
    -- Inside the tsum: 5 terms.
    -- Each summand is `c_i · digammaPoleKernelLeft k β α_i` (linear in `digammaPoleKernelLeft`),
    -- where c_i is a constant (in k) involving `Complex.exp(linear t)`.
    -- Use tsum linearity and `tsum_mul_left` to pull constants outside.
    have hsumm_2t := summable_digammaPoleKernelLeft β (2 * t)
    have hsumm_neg2t := summable_digammaPoleKernelLeft β (-(2 * t))
    have hsumm_t := summable_digammaPoleKernelLeft β t
    have hsumm_negt := summable_digammaPoleKernelLeft β (-t)
    have hsumm_0 := summable_digammaPoleKernelLeft β 0
    set k1 : ℂ := (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) with hk1_def
    set k2 : ℂ := (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) with hk2_def
    set k3 : ℂ := Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) with hk3_def
    set k4 : ℂ := Complex.exp ((((3/2) * t) : ℝ) : ℂ) with hk4_def
    -- The aggregator equals k1 · dPK_2t k + k2 · dPK_neg2t k − k3 · dPK_t k − k4 · dPK_negt k + dPK_0 k.
    have h_aggregator_def : ∀ k,
        leftPoleTowerK2Aggregator k t β =
        k1 * digammaPoleKernelLeft k β (2 * t) +
        k2 * digammaPoleKernelLeft k β (-(2 * t)) -
        k3 * digammaPoleKernelLeft k β t -
        k4 * digammaPoleKernelLeft k β (-t) +
        digammaPoleKernelLeft k β 0 := by
      intro k
      rw [hk1_def, hk2_def, hk3_def, hk4_def]
      unfold leftPoleTowerK2Aggregator
      ring
    -- ∑' k, aggregator = k1 · (∑' k, dPK_2t) + ...
    have h_tsum_split :
        ∑' k : ℕ, leftPoleTowerK2Aggregator k t β =
        k1 * (∑' k : ℕ, digammaPoleKernelLeft k β (2 * t)) +
        k2 * (∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t))) -
        k3 * (∑' k : ℕ, digammaPoleKernelLeft k β t) -
        k4 * (∑' k : ℕ, digammaPoleKernelLeft k β (-t)) +
        (∑' k : ℕ, digammaPoleKernelLeft k β 0) := by
      rw [tsum_congr h_aggregator_def]
      have h1 := hsumm_2t.mul_left k1
      have h2 := hsumm_neg2t.mul_left k2
      have h3 := hsumm_t.mul_left k3
      have h4 := hsumm_negt.mul_left k4
      rw [Summable.tsum_add ((h1.add h2).sub h3 |>.sub h4) hsumm_0]
      rw [Summable.tsum_sub (h1.add h2 |>.sub h3) h4]
      rw [Summable.tsum_sub (h1.add h2) h3]
      rw [Summable.tsum_add h1 h2]
      rw [tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    rw [h_tsum_split]
    rw [hk1_def, hk2_def, hk3_def, hk4_def]
    ring
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, leftPoleTowerK2Aggregator k t β)) =
      (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (2 * t)) +
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t))) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β t) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (-t)) +
        (Complex.exp (-2 * (t : ℂ)^2) *
          ∑' k : ℕ, digammaPoleKernelLeft k β 0)) from funext h_reshape]
  -- 5-term integrability assembly.
  have h_T1 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (2 * t))) := by
    have h := integrable_gauss_outer_exp_tower_left β (-3) 2
    have h_a : ∀ t : ℝ,
        Complex.exp ((-3 * t : ℝ) : ℂ) =
        Complex.exp ((-(3 * t) : ℝ) : ℂ) := by
      intro t; congr 1; push_cast; ring
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (2 * t))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (2 * t))) from
      funext (fun t => by rw [h_a t])]
    exact h.const_mul _
  have h_T2 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t)))) := by
    have h := integrable_gauss_outer_exp_tower_left β 3 (-2)
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelLeft k β (-2 * t)) =
        (∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t))) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (-(2 * t)))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (-2 * t))) from
      funext (fun t => by rw [h_c t])]
    exact h.const_mul _
  have h_T3 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelLeft k β t) := by
    have h := integrable_gauss_outer_exp_tower_left β (-3/2) 1
    have h_a : ∀ t : ℝ,
        Complex.exp ((-3/2 * t : ℝ) : ℂ) =
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) := by
      intro t; congr 1; push_cast; ring
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelLeft k β (1 * t)) =
        (∑' k : ℕ, digammaPoleKernelLeft k β t) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β t) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3/2 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T4 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelLeft k β (-t)) := by
    have h := integrable_gauss_outer_exp_tower_left β (3/2) (-1)
    have h_a : ∀ t : ℝ,
        Complex.exp ((3/2 * t : ℝ) : ℂ) =
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) := by
      intro t; congr 1
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelLeft k β (-1 * t)) =
        (∑' k : ℕ, digammaPoleKernelLeft k β (-t)) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelLeft k β (-t)) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3/2 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelLeft k β (-1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T5 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ∑' k : ℕ, digammaPoleKernelLeft k β 0) := by
    have h_gauss : Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) := by
      have h_real : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) := by
        have := integrable_exp_neg_two_sq_mul_linear 0
        have h_eq : ∀ t : ℝ, Real.exp (-2 * t^2 + 0 * t) = Real.exp (-2 * t^2) := by
          intro t; congr 1; ring
        rw [show (fun t : ℝ => Real.exp (-2 * t^2)) =
            (fun t : ℝ => Real.exp (-2 * t^2 + 0 * t)) from
          funext (fun t => (h_eq t).symm)]
        exact this
      have h_conv : ∀ t : ℝ,
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) = Complex.exp (-2 * (t : ℂ)^2) := by
        intro t
        rw [Complex.ofReal_exp]
        congr 1
        push_cast; ring
      rw [show (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) =
          (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) from
        funext (fun t => (h_conv t).symm)]
      exact h_real.ofReal
    exact h_gauss.mul_const _
  exact (((h_T1.add h_T2).sub h_T3).sub h_T4).add h_T5

#print axioms integrable_gaussian_archLeftPoleTower

/-! ## Integrability of `Complex.exp(-2t²) · ∑' k, rightPoleTowerK2Aggregator k t β` -/

theorem integrable_gaussian_archRightPoleTower (β : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, rightPoleTowerK2Aggregator k t β)) := by
  have h_reshape : ∀ t : ℝ,
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, rightPoleTowerK2Aggregator k t β) =
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (2 * t)) +
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t))) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelRight k β t) -
      (Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelRight k β (-t)) +
      (Complex.exp (-2 * (t : ℂ)^2) *
        ∑' k : ℕ, digammaPoleKernelRight k β 0) := by
    intro t
    have hsumm_2t := summable_digammaPoleKernelRight β (2 * t)
    have hsumm_neg2t := summable_digammaPoleKernelRight β (-(2 * t))
    have hsumm_t := summable_digammaPoleKernelRight β t
    have hsumm_negt := summable_digammaPoleKernelRight β (-t)
    have hsumm_0 := summable_digammaPoleKernelRight β 0
    set k1 : ℂ := (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) with hk1_def
    set k2 : ℂ := (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) with hk2_def
    set k3 : ℂ := Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) with hk3_def
    set k4 : ℂ := Complex.exp ((((3/2) * t) : ℝ) : ℂ) with hk4_def
    have h_aggregator_def : ∀ k,
        rightPoleTowerK2Aggregator k t β =
        k1 * digammaPoleKernelRight k β (2 * t) +
        k2 * digammaPoleKernelRight k β (-(2 * t)) -
        k3 * digammaPoleKernelRight k β t -
        k4 * digammaPoleKernelRight k β (-t) +
        digammaPoleKernelRight k β 0 := by
      intro k
      rw [hk1_def, hk2_def, hk3_def, hk4_def]
      unfold rightPoleTowerK2Aggregator
      ring
    have h_tsum_split :
        ∑' k : ℕ, rightPoleTowerK2Aggregator k t β =
        k1 * (∑' k : ℕ, digammaPoleKernelRight k β (2 * t)) +
        k2 * (∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t))) -
        k3 * (∑' k : ℕ, digammaPoleKernelRight k β t) -
        k4 * (∑' k : ℕ, digammaPoleKernelRight k β (-t)) +
        (∑' k : ℕ, digammaPoleKernelRight k β 0) := by
      rw [tsum_congr h_aggregator_def]
      have h1 := hsumm_2t.mul_left k1
      have h2 := hsumm_neg2t.mul_left k2
      have h3 := hsumm_t.mul_left k3
      have h4 := hsumm_negt.mul_left k4
      rw [Summable.tsum_add ((h1.add h2).sub h3 |>.sub h4) hsumm_0]
      rw [Summable.tsum_sub (h1.add h2 |>.sub h3) h4]
      rw [Summable.tsum_sub (h1.add h2) h3]
      rw [Summable.tsum_add h1 h2]
      rw [tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    rw [h_tsum_split]
    rw [hk1_def, hk2_def, hk3_def, hk4_def]
    ring
  rw [show (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ, rightPoleTowerK2Aggregator k t β)) =
      (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (2 * t)) +
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t))) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β t) -
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (-t)) +
        (Complex.exp (-2 * (t : ℂ)^2) *
          ∑' k : ℕ, digammaPoleKernelRight k β 0)) from funext h_reshape]
  have h_T1 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((-(3 * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (2 * t))) := by
    have h := integrable_gauss_outer_exp_tower_right β (-3) 2
    have h_a : ∀ t : ℝ,
        Complex.exp ((-3 * t : ℝ) : ℂ) =
        Complex.exp ((-(3 * t) : ℝ) : ℂ) := by
      intro t; congr 1; push_cast; ring
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-(3 * t) : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (2 * t))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (2 * t))) from
      funext (fun t => by rw [h_a t])]
    exact h.const_mul _
  have h_T2 : Integrable (fun t : ℝ =>
      (1/2 : ℂ) *
        (Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((3 * t : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t)))) := by
    have h := integrable_gauss_outer_exp_tower_right β 3 (-2)
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelRight k β (-2 * t)) =
        (∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t))) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (-(2 * t)))) =
        (fun t : ℝ => (1/2 : ℂ) *
          (Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (-2 * t))) from
      funext (fun t => by rw [h_c t])]
    exact h.const_mul _
  have h_T3 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelRight k β t) := by
    have h := integrable_gauss_outer_exp_tower_right β (-3/2) 1
    have h_a : ∀ t : ℝ,
        Complex.exp ((-3/2 * t : ℝ) : ℂ) =
        Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) := by
      intro t; congr 1; push_cast; ring
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelRight k β (1 * t)) =
        (∑' k : ℕ, digammaPoleKernelRight k β t) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β t) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((-3/2 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T4 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          ∑' k : ℕ, digammaPoleKernelRight k β (-t)) := by
    have h := integrable_gauss_outer_exp_tower_right β (3/2) (-1)
    have h_a : ∀ t : ℝ,
        Complex.exp ((3/2 * t : ℝ) : ℂ) =
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) := by
      intro t; congr 1
    have h_c : ∀ t : ℝ,
        (∑' k : ℕ, digammaPoleKernelRight k β (-1 * t)) =
        (∑' k : ℕ, digammaPoleKernelRight k β (-t)) := by
      intro t
      apply tsum_congr
      intro k; congr 1; ring
    rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
            ∑' k : ℕ, digammaPoleKernelRight k β (-t)) =
        (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2) *
            Complex.exp ((3/2 * t : ℝ) : ℂ) *
              ∑' k : ℕ, digammaPoleKernelRight k β (-1 * t)) from
      funext (fun t => by rw [h_a t, h_c t])]
    exact h
  have h_T5 : Integrable (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ∑' k : ℕ, digammaPoleKernelRight k β 0) := by
    have h_gauss : Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) := by
      have h_real : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) := by
        have := integrable_exp_neg_two_sq_mul_linear 0
        have h_eq : ∀ t : ℝ, Real.exp (-2 * t^2 + 0 * t) = Real.exp (-2 * t^2) := by
          intro t; congr 1; ring
        rw [show (fun t : ℝ => Real.exp (-2 * t^2)) =
            (fun t : ℝ => Real.exp (-2 * t^2 + 0 * t)) from
          funext (fun t => (h_eq t).symm)]
        exact this
      have h_conv : ∀ t : ℝ,
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) = Complex.exp (-2 * (t : ℂ)^2) := by
        intro t
        rw [Complex.ofReal_exp]
        congr 1
        push_cast; ring
      rw [show (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) =
          (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) from
        funext (fun t => (h_conv t).symm)]
      exact h_real.ofReal
    exact h_gauss.mul_const _
  exact (((h_T1.add h_T2).sub h_T3).sub h_T4).add h_T5

#print axioms integrable_gaussian_archRightPoleTower

/-! ## Bound on `ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local` at `Re = -1` (public)

Mirrors the private lemma in `CauchyKPairTestVerticalIntegrable.lean`; needed
publicly here for the Fubini integrability hypotheses. -/

theorem gaussianDefectEntireKernel_bounded_at_re_neg_one :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  set Cprefac : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hCprefac_def
  have hCprefac_nn : 0 ≤ Cprefac := by
    rw [hCprefac_def]
    exact mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  refine ⟨Cprefac * (Real.exp (9/8) + 2 * Real.exp (9/32) + 1), fun y => ?_⟩
  unfold ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCprefac_nn]
  apply mul_le_mul_of_nonneg_left _ hCprefac_nn
  set s : ℂ := ((-1 : ℝ) : ℂ) + (y : ℂ) * I with hs_def
  have h_sub_sq : (s - (1/2 : ℂ))^2 = ((9/4 - y^2 : ℝ) : ℂ) + ((-3 * y : ℝ) : ℂ) * I := by
    rw [hs_def]
    have hyc : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = -((y^2 : ℝ) : ℂ) := by
      have : (y : ℂ) * Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ)^2 * Complex.I^2 := by ring
      rw [this, Complex.I_sq]; push_cast; ring
    have h_sub_eq : ((-1 : ℝ) : ℂ) + (y : ℂ) * I - (1/2 : ℂ) = (-3/2 : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [h_sub_eq, sq]
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
  -- ‖exp((s-1/2)²/2) - 2·exp((s-1/2)²/8) + 1‖ ≤ exp(9/8) + 2·exp(9/32) + 1.
  have h_norm_one : ‖(1 : ℂ)‖ = 1 := norm_one
  have h_two_norm : ‖(2 : ℂ) * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ ≤ 2 * Real.exp (9/32) := by
    rw [norm_mul]
    have h_two_norm : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [h_two_norm]
    exact mul_le_mul_of_nonneg_left h_exp8_norm (by norm_num)
  calc ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8) + 1‖
      ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.exp ((s - (1/2 : ℂ))^2 / 2)‖ +
        ‖(2 : ℂ) * Complex.exp ((s - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ := by
        have := norm_sub_le
          (Complex.exp ((s - (1/2 : ℂ))^2 / 2))
          ((2 : ℂ) * Complex.exp ((s - (1/2 : ℂ))^2 / 8))
        linarith
    _ ≤ Real.exp (9/8) + 2 * Real.exp (9/32) + 1 := by
        rw [h_norm_one]
        linarith [h_exp2_norm, h_two_norm]

#print axioms gaussianDefectEntireKernel_bounded_at_re_neg_one

/-! ## Fubini integrability hypotheses for `K_rectangle_LHS_eq_pRD_minus_arch_target_holds` -/

theorem h_int_left_arch (β : ℝ) :
    Integrable (fun y : ℝ =>
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.archIntegrand β (-1) y) := by
  obtain ⟨C, hC_bd⟩ := gaussianDefectEntireKernel_bounded_at_re_neg_one
  have h_arch := ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  -- bdd_mul: bounded × integrable = integrable.
  refine h_arch.bdd_mul ?_ (Filter.Eventually.of_forall hC_bd)
  apply Continuous.aestronglyMeasurable
  -- ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local is differentiable, hence continuous.
  have h_diff : Differentiable ℂ ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local := by
    unfold ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
    have h1 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 2)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    have h2 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 8)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    exact (differentiable_const _).mul (((h1.sub ((differentiable_const _).mul h2)).add
      (differentiable_const _)))
  -- Continuous in y.
  have h_cont_input : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    fun_prop
  exact h_diff.continuous.comp h_cont_input

#print axioms h_int_left_arch

theorem h_int_left_refl (β : ℝ) :
    Integrable (fun y : ℝ =>
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.reflectedPrimeIntegrand β (-1) y) := by
  obtain ⟨C, hC_bd⟩ := gaussianDefectEntireKernel_bounded_at_re_neg_one
  have h_refl := ZD.WeilPositivity.ArchAtNegOne.reflectedPrimeIntegrand_at_neg_one_integrable β
  refine h_refl.bdd_mul ?_ (Filter.Eventually.of_forall hC_bd)
  apply Continuous.aestronglyMeasurable
  have h_diff : Differentiable ℂ ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local := by
    unfold ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
    have h1 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 2)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    have h2 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 8)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    exact (differentiable_const _).mul (((h1.sub ((differentiable_const _).mul h2)).add
      (differentiable_const _)))
  have h_cont_input : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    fun_prop
  exact h_diff.continuous.comp h_cont_input

#print axioms h_int_left_refl

/-! ## `K_arch_four_bucket_target_holds_unconditional`

Compose the 4 bucket integrability lemmas to produce
`K_arch_four_bucket_target β` axiom-clean for every `β`. -/

theorem K_arch_four_bucket_target_holds_unconditional (β : ℝ) :
    ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_arch_four_bucket_target β :=
  ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_arch_four_bucket_target_holds β
    (integrable_gaussian_archConstantCarrier β).integrableOn
    (integrable_gaussian_archRationalCorrection β).integrableOn
    (integrable_gaussian_archLeftPoleTower β).integrableOn
    (integrable_gaussian_archRightPoleTower β).integrableOn

#print axioms K_arch_four_bucket_target_holds_unconditional

/-! ## Bound on `|K_2(s, t)|` uniformly in `Im s` for `Re s ∈ {-1, 2}`

Used downstream for inner-integrability hypotheses of
`K_rectangle_LHS_eq_pRD_minus_arch_target_holds`. -/

theorem K_2_norm_le_cosh_at_re_eq (σ y t : ℝ) :
    ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((σ : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (2 * (σ - 1/2) * t) +
        2 * Real.cosh ((σ - 1/2) * t) + 1 := by
  unfold ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
  -- |cosh(a+ib)| ≤ cosh(a) for a, b real (since cosh(a+ib) = cosh(a)cos(b) + i·sinh(a)sin(b),
  -- |cosh(a+ib)|² = cosh²(a)cos²(b) + sinh²(a)sin²(b) ≤ cosh²(a)).
  have h_cosh_complex_le : ∀ (a b : ℝ), ‖Complex.cosh ((a : ℂ) + (b : ℂ) * I)‖ ≤
      Real.cosh a := by
    intro a b
    rw [Complex.cosh, show ((a : ℂ) + (b : ℂ) * I) = ((a : ℂ) + (b : ℂ) * I) from rfl]
    -- cosh z = (e^z + e^(-z))/2.
    have h : Complex.cosh ((a : ℂ) + (b : ℂ) * I) =
        (Complex.exp ((a : ℂ) + (b : ℂ) * I) +
          Complex.exp (-((a : ℂ) + (b : ℂ) * I))) / 2 := by
      rw [Complex.cosh]
    rw [show (Complex.exp ((a : ℂ) + (b : ℂ) * I) +
          Complex.exp (-((a : ℂ) + (b : ℂ) * I))) / 2 =
        (Complex.exp ((a : ℂ) + (b : ℂ) * I) +
          Complex.exp (-((a : ℂ) + (b : ℂ) * I))) * (1/2) from by ring]
    rw [norm_mul]
    have h_norm_half : ‖((1 : ℂ)/2)‖ = 1/2 := by
      rw [show ((1 : ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [h_norm_half]
    have h_pos_norm : ‖Complex.exp ((a : ℂ) + (b : ℂ) * I)‖ = Real.exp a := by
      rw [Complex.norm_exp]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
    have h_neg_norm : ‖Complex.exp (-((a : ℂ) + (b : ℂ) * I))‖ = Real.exp (-a) := by
      rw [Complex.norm_exp]
      simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have h_tri : ‖Complex.exp ((a : ℂ) + (b : ℂ) * I) +
        Complex.exp (-((a : ℂ) + (b : ℂ) * I))‖ ≤
        ‖Complex.exp ((a : ℂ) + (b : ℂ) * I)‖ +
          ‖Complex.exp (-((a : ℂ) + (b : ℂ) * I))‖ := norm_add_le _ _
    rw [h_pos_norm, h_neg_norm] at h_tri
    have h_cosh_eq : Real.cosh a = (Real.exp a + Real.exp (-a)) / 2 := Real.cosh_eq a
    rw [h_cosh_eq]
    linarith
  -- |2(s-1/2)t| at s=σ+iy: 2(σ-1/2+iy)t = 2(σ-1/2)t + 2iy·t.
  -- |cosh(2(s-1/2)t)| ≤ cosh(2(σ-1/2)t).
  have h_arg1 : 2 * ((((σ : ℝ) : ℂ) + (y : ℂ) * I) - 1/2) * (t : ℂ) =
      ((2 * (σ - 1/2) * t : ℝ) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I := by
    push_cast; ring
  have h_arg2 : ((((σ : ℝ) : ℂ) + (y : ℂ) * I) - 1/2) * (t : ℂ) =
      (((σ - 1/2) * t : ℝ) : ℂ) + ((y * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h_arg1, h_arg2]
  have h_cosh1 := h_cosh_complex_le (2 * (σ - 1/2) * t) (2 * y * t)
  have h_cosh2 := h_cosh_complex_le ((σ - 1/2) * t) (y * t)
  -- ‖cosh(...) - 2 cosh(...) + 1‖ ≤ ‖cosh(...)‖ + 2‖cosh(...)‖ + ‖1‖.
  have h_norm_one : ‖(1 : ℂ)‖ = 1 := norm_one
  have h_two_cosh_norm : ‖(2 : ℂ) * Complex.cosh (((((σ - 1/2) * t : ℝ)) : ℂ) +
      ((y * t : ℝ) : ℂ) * I)‖ ≤ 2 * Real.cosh ((σ - 1/2) * t) := by
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left h_cosh2 (by norm_num)
  calc ‖Complex.cosh ((((2 * (σ - 1/2) * t : ℝ)) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I) -
            2 * Complex.cosh (((((σ - 1/2) * t : ℝ)) : ℂ) + ((y * t : ℝ) : ℂ) * I) + 1‖
      ≤ ‖Complex.cosh ((((2 * (σ - 1/2) * t : ℝ)) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I) -
          2 * Complex.cosh (((((σ - 1/2) * t : ℝ)) : ℂ) + ((y * t : ℝ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.cosh ((((2 * (σ - 1/2) * t : ℝ)) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I)‖ +
        ‖(2 : ℂ) * Complex.cosh (((((σ - 1/2) * t : ℝ)) : ℂ) + ((y * t : ℝ) : ℂ) * I)‖ +
        ‖(1 : ℂ)‖ := by
        have := norm_sub_le
          (Complex.cosh ((((2 * (σ - 1/2) * t : ℝ)) : ℂ) + ((2 * y * t : ℝ) : ℂ) * I))
          ((2 : ℂ) * Complex.cosh (((((σ - 1/2) * t : ℝ)) : ℂ) + ((y * t : ℝ) : ℂ) * I))
        linarith
    _ ≤ Real.cosh (2 * (σ - 1/2) * t) + 2 * Real.cosh ((σ - 1/2) * t) + 1 := by
        rw [h_norm_one]
        linarith [h_cosh1, h_two_cosh_norm]

#print axioms K_2_norm_le_cosh_at_re_eq

/-! ## Strip-bound integrability against Gaussian

The function `t ↦ (cosh(3|t|) + 2·cosh(3|t|/2) + 1)·exp(-2t²)` is integrable on
`Ioi 0` (and on ℝ).  This is the dominator for joint Fubini integrability
of `K_2(s+iy,t)·exp(-2t²)·g(y)` when `s.re ∈ {-1, 2}` (so the strip
bound `K_2_norm_le_cosh_at_re_eq` applies). -/

private lemma cosh_times_gauss_integrable (a : ℝ) :
    Integrable (fun t : ℝ => Real.cosh (a * t) * Real.exp (-2 * t^2)) := by
  have h_eq : (fun t : ℝ => Real.cosh (a * t) * Real.exp (-2 * t^2)) =
      (fun t : ℝ => (Real.exp (-2 * t^2 + a * t) + Real.exp (-2 * t^2 + (-a) * t)) / 2) := by
    funext t
    rw [Real.cosh_eq]
    have h1 : Real.exp (a * t) * Real.exp (-2 * t^2) = Real.exp (-2 * t^2 + a * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(a * t)) * Real.exp (-2 * t^2) = Real.exp (-2 * t^2 + (-a) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [h1, h2, Real.exp_pos (a * t), Real.exp_pos (-(a * t)), Real.exp_pos (-2 * t ^ 2)]
  rw [h_eq]
  exact ((integrable_exp_neg_two_sq_mul_linear a).add
    (integrable_exp_neg_two_sq_mul_linear (-a))).div_const 2

theorem integrable_strip_bound_times_gaussian :
    Integrable (fun t : ℝ =>
      (Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2)) := by
  have h1 : Integrable (fun t : ℝ => Real.cosh (3 * t) * Real.exp (-2 * t^2)) :=
    cosh_times_gauss_integrable 3
  have h2 : Integrable (fun t : ℝ => Real.cosh ((3/2) * t) * Real.exp (-2 * t^2)) :=
    cosh_times_gauss_integrable (3/2)
  have h3 : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) := by
    have h_zero : (fun t : ℝ => Real.exp (-2 * t^2)) =
        (fun t : ℝ => Real.exp (-2 * t^2 + 0 * t)) := by
      funext t; ring_nf
    rw [h_zero]; exact integrable_exp_neg_two_sq_mul_linear 0
  have h_eq : (fun t : ℝ =>
      (Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2)) =
      (fun t : ℝ => Real.cosh (3 * t) * Real.exp (-2 * t^2) +
        2 * (Real.cosh ((3/2) * t) * Real.exp (-2 * t^2)) +
        Real.exp (-2 * t^2)) := by
    funext t; ring
  rw [h_eq]
  exact (h1.add (h2.const_mul 2)).add h3

#print axioms integrable_strip_bound_times_gaussian

/-! ## Joint integrability for the right edge (Re = 2)

`(t,y) ↦ K_2(2+iy,t)·exp(-2t²)·primeIntegrand β 2 y` is integrable on
`(volume.restrict (Ioi 0)).prod volume`.  Used to derive both the inner
integrability `h_int_inner_right` and the Fubini equality `h_fubini_right`. -/

theorem joint_integrable_K2_exp_primeIntegrand_right (β : ℝ) :
    Integrable (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
      Contour.primeIntegrand β 2 y))
    ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
  -- Bound: ‖K_2(2+iy,t)‖ ≤ cosh(3t) + 2 cosh(3t/2) + 1.
  -- |exp(-2t²)| = exp(-2t²).
  -- Product norm ≤ B(t) · ‖primeIntegrand y‖ where B is integrable on Ioi 0.
  have h_PI_int : Integrable (Contour.primeIntegrand β 2) :=
    Contour.primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)
  have h_B_int : IntegrableOn (fun t : ℝ =>
      (Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2))
      (Set.Ioi (0:ℝ)) :=
    integrable_strip_bound_times_gaussian.integrableOn
  -- Joint product bounding function.
  have h_prod_int : Integrable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ((Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2)) *
          ‖Contour.primeIntegrand β 2 y‖))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
    MeasureTheory.Integrable.mul_prod h_B_int h_PI_int.norm
  -- Measurability of the actual integrand: K_2 part is jointly continuous,
  -- exp part is continuous in t alone, primeIntegrand is integrable hence
  -- aestronglyMeasurable.  Combine via comp_fst / comp_snd.
  have h_meas : AEStronglyMeasurable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
    -- K_2 jointly continuous (no LSeries dependency).
    have hK2_cont : Continuous (fun (z : ℝ × ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1) := by
      unfold ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      have h_s : Continuous (fun (z : ℝ × ℝ) =>
          (((2 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) :=
        (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const)).sub continuous_const
      have h_t : Continuous (fun (z : ℝ × ℝ) => ((z.1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp continuous_fst
      have h_arg1 : Continuous (fun (z : ℝ × ℝ) =>
          (2 : ℂ) * ((((2 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        (continuous_const.mul h_s).mul h_t
      have h_arg2 : Continuous (fun (z : ℝ × ℝ) =>
          ((((2 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        h_s.mul h_t
      exact ((Complex.continuous_cosh.comp h_arg1).sub
        (continuous_const.mul (Complex.continuous_cosh.comp h_arg2))).add continuous_const
    have hExp_cont : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2)))
    have h_PI_meas : AEStronglyMeasurable (Contour.primeIntegrand β 2)
        MeasureTheory.volume := h_PI_int.aestronglyMeasurable
    have hK2_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      hK2_cont.aestronglyMeasurable
    have hExp_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ((Real.exp (-2 * z.1^2) : ℝ) : ℂ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      (hExp_cont.comp continuous_fst).aestronglyMeasurable
    have hPI_cont : Continuous (fun (z : ℝ × ℝ) => Contour.primeIntegrand β 2 z.2) := by
      have : Continuous (Contour.primeIntegrand β 2) := by
        unfold Contour.primeIntegrand
        exact (Contour.LSeries_vonMangoldt_continuous_along_vertical 2 (by norm_num)).mul
          (Contour.pairTestMellin_continuous_along_vertical β 2 (by norm_num))
      exact this.comp continuous_snd
    have hPI_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => Contour.primeIntegrand β 2 z.2)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      hPI_cont.aestronglyMeasurable
    exact (hK2_meas.mul hExp_meas).mul hPI_meas
  -- Domination.
  refine MeasureTheory.Integrable.mono' h_prod_int h_meas ?_
  refine MeasureTheory.ae_of_all _ ?_
  rintro ⟨t, y⟩
  show ‖_‖ ≤ _
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair]
  rw [norm_mul, norm_mul]
  -- ‖K_2‖ ≤ cosh(3t) + 2 cosh(3t/2) + 1; ‖exp(-2t²) : ℂ‖ = exp(-2t²).
  have h_K2_bd : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((2 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (2 * (2 - 1/2) * t) + 2 * Real.cosh ((2 - 1/2) * t) + 1 := by
    have := K_2_norm_le_cosh_at_re_eq 2 y t
    convert this using 2
  have h_K2_bd' : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((2 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    have h1 : 2 * (2 - 1/2 : ℝ) * t = 3 * t := by ring
    have h2 : (2 - 1/2 : ℝ) * t = (3/2) * t := by ring
    rw [h1, h2] at h_K2_bd
    exact h_K2_bd
  have h_exp_bd : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact (Real.exp_pos _).le
  have h_K2_nn : 0 ≤ Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    have h1 : 1 ≤ Real.cosh (3 * t) := Real.one_le_cosh _
    have h2 : 1 ≤ Real.cosh ((3/2) * t) := Real.one_le_cosh _
    linarith
  have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  rw [h_exp_bd]
  have h_pos := mul_le_mul_of_nonneg_right h_K2_bd' h_exp_nn
  exact mul_le_mul_of_nonneg_right h_pos (norm_nonneg _)

#print axioms joint_integrable_K2_exp_primeIntegrand_right

/-! ## Joint integrability for the left edge (Re = -1), arch piece

`(t,y) ↦ K_2(-1+iy,t)·exp(-2t²)·archIntegrand β (-1) y` is integrable on
`(volume.restrict (Ioi 0)).prod volume`.  Used to derive both the inner
integrability `h_int_inner_left_arch` and the Fubini equality
`h_fubini_left_arch`. -/

theorem joint_integrable_K2_exp_archIntegrand_left (β : ℝ) :
    Integrable (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
      Contour.archIntegrand β (-1) y))
    ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
  -- Bound: ‖K_2(-1+iy,t)‖ ≤ cosh(3t) + 2 cosh(3t/2) + 1 (cosh even).
  have h_arch_int : Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_B_int : IntegrableOn (fun t : ℝ =>
      (Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2))
      (Set.Ioi (0:ℝ)) :=
    integrable_strip_bound_times_gaussian.integrableOn
  have h_prod_int : Integrable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ((Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2)) *
          ‖Contour.archIntegrand β (-1) y‖))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
    MeasureTheory.Integrable.mul_prod h_B_int h_arch_int.norm
  have h_meas : AEStronglyMeasurable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.archIntegrand β (-1) y))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
    have hK2_cont : Continuous (fun (z : ℝ × ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1) := by
      unfold ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      have h_s : Continuous (fun (z : ℝ × ℝ) =>
          (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) :=
        (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const)).sub continuous_const
      have h_t : Continuous (fun (z : ℝ × ℝ) => ((z.1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp continuous_fst
      have h_arg1 : Continuous (fun (z : ℝ × ℝ) =>
          (2 : ℂ) * ((((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        (continuous_const.mul h_s).mul h_t
      have h_arg2 : Continuous (fun (z : ℝ × ℝ) =>
          ((((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        h_s.mul h_t
      exact ((Complex.continuous_cosh.comp h_arg1).sub
        (continuous_const.mul (Complex.continuous_cosh.comp h_arg2))).add continuous_const
    have hExp_cont : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2)))
    have hK2_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      hK2_cont.aestronglyMeasurable
    have hExp_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ((Real.exp (-2 * z.1^2) : ℝ) : ℂ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      (hExp_cont.comp continuous_fst).aestronglyMeasurable
    -- For archIntegrand at σ = -1, no σ>1 continuity tool — use integrability.
    have h_arch_aem : AEStronglyMeasurable (Contour.archIntegrand β (-1))
        MeasureTheory.volume := h_arch_int.aestronglyMeasurable
    have hArch_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => Contour.archIntegrand β (-1) z.2)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      h_arch_aem.comp_snd
    exact (hK2_meas.mul hExp_meas).mul hArch_meas
  refine MeasureTheory.Integrable.mono' h_prod_int h_meas ?_
  refine MeasureTheory.ae_of_all _ ?_
  rintro ⟨t, y⟩
  show ‖_‖ ≤ _
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair]
  rw [norm_mul, norm_mul]
  have h_K2_bd : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (2 * (-1 - 1/2) * t) + 2 * Real.cosh ((-1 - 1/2) * t) + 1 := by
    have := K_2_norm_le_cosh_at_re_eq (-1) y t
    convert this using 2
  have h_K2_bd' : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    -- 2(-1 - 1/2)t = -3t, |cosh(-x)| = cosh(x); (-1 - 1/2)t = -3t/2, similarly.
    have h_eq1 : Real.cosh (2 * (-1 - 1/2 : ℝ) * t) = Real.cosh (3 * t) := by
      rw [show (2 * (-1 - 1/2 : ℝ) * t) = -(3 * t) from by ring, Real.cosh_neg]
    have h_eq2 : Real.cosh ((-1 - 1/2 : ℝ) * t) = Real.cosh ((3/2) * t) := by
      rw [show ((-1 - 1/2 : ℝ) * t) = -((3/2) * t) from by ring, Real.cosh_neg]
    rw [h_eq1, h_eq2] at h_K2_bd
    exact h_K2_bd
  have h_exp_bd : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact (Real.exp_pos _).le
  have h_K2_nn : 0 ≤ Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    have h1 : 1 ≤ Real.cosh (3 * t) := Real.one_le_cosh _
    have h2 : 1 ≤ Real.cosh ((3/2) * t) := Real.one_le_cosh _
    linarith
  have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  rw [h_exp_bd]
  have h_pos := mul_le_mul_of_nonneg_right h_K2_bd' h_exp_nn
  exact mul_le_mul_of_nonneg_right h_pos (norm_nonneg _)

#print axioms joint_integrable_K2_exp_archIntegrand_left

/-! ## Joint integrability for the left edge (Re = -1), reflected-prime piece

`(t,y) ↦ K_2(-1+iy,t)·exp(-2t²)·reflectedPrimeIntegrand β (-1) y` is integrable on
`(volume.restrict (Ioi 0)).prod volume`.  Used to derive both the inner
integrability `h_int_inner_refl` and the Fubini equality `h_fubini_left_refl`. -/

theorem joint_integrable_K2_exp_reflectedPrime_left (β : ℝ) :
    Integrable (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
      Contour.reflectedPrimeIntegrand β (-1) y))
    ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
  have h_refl_int : Integrable (Contour.reflectedPrimeIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.reflectedPrimeIntegrand_at_neg_one_integrable β
  have h_B_int : IntegrableOn (fun t : ℝ =>
      (Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2))
      (Set.Ioi (0:ℝ)) :=
    integrable_strip_bound_times_gaussian.integrableOn
  have h_prod_int : Integrable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ((Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1) * Real.exp (-2 * t^2)) *
          ‖Contour.reflectedPrimeIntegrand β (-1) y‖))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
    MeasureTheory.Integrable.mul_prod h_B_int h_refl_int.norm
  have h_meas : AEStronglyMeasurable
      (Function.uncurry (fun (t : ℝ) (y : ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) := by
    have hK2_cont : Continuous (fun (z : ℝ × ℝ) =>
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1) := by
      unfold ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      have h_s : Continuous (fun (z : ℝ × ℝ) =>
          (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) :=
        (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const)).sub continuous_const
      have h_t : Continuous (fun (z : ℝ × ℝ) => ((z.1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp continuous_fst
      have h_arg1 : Continuous (fun (z : ℝ × ℝ) =>
          (2 : ℂ) * ((((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        (continuous_const.mul h_s).mul h_t
      have h_arg2 : Continuous (fun (z : ℝ × ℝ) =>
          ((((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) - (1/2 : ℂ)) * ((z.1 : ℝ) : ℂ)) :=
        h_s.mul h_t
      exact ((Complex.continuous_cosh.comp h_arg1).sub
        (continuous_const.mul (Complex.continuous_cosh.comp h_arg2))).add continuous_const
    have hExp_cont : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2)))
    have hK2_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (z.2 : ℂ) * I) z.1)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      hK2_cont.aestronglyMeasurable
    have hExp_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => ((Real.exp (-2 * z.1^2) : ℝ) : ℂ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      (hExp_cont.comp continuous_fst).aestronglyMeasurable
    have h_refl_aem : AEStronglyMeasurable (Contour.reflectedPrimeIntegrand β (-1))
        MeasureTheory.volume := h_refl_int.aestronglyMeasurable
    have hRP_meas : AEStronglyMeasurable
        (fun (z : ℝ × ℝ) => Contour.reflectedPrimeIntegrand β (-1) z.2)
        ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod MeasureTheory.volume) :=
      h_refl_aem.comp_snd
    exact (hK2_meas.mul hExp_meas).mul hRP_meas
  refine MeasureTheory.Integrable.mono' h_prod_int h_meas ?_
  refine MeasureTheory.ae_of_all _ ?_
  rintro ⟨t, y⟩
  show ‖_‖ ≤ _
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair]
  rw [norm_mul, norm_mul]
  have h_K2_bd : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (2 * (-1 - 1/2) * t) + 2 * Real.cosh ((-1 - 1/2) * t) + 1 := by
    have := K_2_norm_le_cosh_at_re_eq (-1) y t
    convert this using 2
  have h_K2_bd' : ‖ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
      (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤
      Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    have h_eq1 : Real.cosh (2 * (-1 - 1/2 : ℝ) * t) = Real.cosh (3 * t) := by
      rw [show (2 * (-1 - 1/2 : ℝ) * t) = -(3 * t) from by ring, Real.cosh_neg]
    have h_eq2 : Real.cosh ((-1 - 1/2 : ℝ) * t) = Real.cosh ((3/2) * t) := by
      rw [show ((-1 - 1/2 : ℝ) * t) = -((3/2) * t) from by ring, Real.cosh_neg]
    rw [h_eq1, h_eq2] at h_K2_bd
    exact h_K2_bd
  have h_exp_bd : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact (Real.exp_pos _).le
  have h_K2_nn : 0 ≤ Real.cosh (3 * t) + 2 * Real.cosh ((3/2) * t) + 1 := by
    have h1 : 1 ≤ Real.cosh (3 * t) := Real.one_le_cosh _
    have h2 : 1 ≤ Real.cosh ((3/2) * t) := Real.one_le_cosh _
    linarith
  have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  rw [h_exp_bd]
  have h_pos := mul_le_mul_of_nonneg_right h_K2_bd' h_exp_nn
  exact mul_le_mul_of_nonneg_right h_pos (norm_nonneg _)

#print axioms joint_integrable_K2_exp_reflectedPrime_left

/-! ## Fubini swap and inner integrability hypotheses for
`K_rectangle_LHS_eq_pRD_minus_arch_target_holds` -/

/-- Helper: `Complex.exp(-2t²) = (Real.exp(-2t²) : ℂ)`. -/
private lemma cexp_eq_rexp_neg_two_sq (t : ℝ) :
    Complex.exp (-2 * (t : ℂ)^2) = ((Real.exp (-2 * t^2) : ℝ) : ℂ) := by
  rw [show (-2 * (t : ℂ)^2 : ℂ) = (((-2 * t^2 : ℝ)) : ℂ) from by push_cast; ring]
  exact (Complex.ofReal_exp _).symm

/-- **Fubini-Plancherel relation on the right edge (Re s = 2):**
```
∫_y K(2+iy) · primeIntegrand β 2 y dy =
  2π · ∫_{Ioi 0} exp(-2t²) · (∫_y K_2(2+iy,t) · primeIntegrand β 2 y dy) dt.
```
Combines `gaussianDefectEntireKernel_eq_K2_integral` (giving
`K(s) = 2π · ∫ K_2(s,t)·exp(-2t²) dt`) with the joint Fubini swap of the
integrable triple `(t,y) ↦ K_2(2+iy,t)·exp(-2t²)·primeIntegrand β 2 y`. -/
theorem h_fubini_right (β : ℝ) :
    (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.primeIntegrand β 2 y) =
      2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          (∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) := by
  have h_K_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) =
        2 * ((Real.pi : ℝ) : ℂ) *
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Complex.exp (-2 * (t : ℂ)^2) := fun y =>
    ZD.WeilPositivity.OfflineDetectorPlancherel.gaussianDefectEntireKernel_eq_K2_integral _
  have h_joint := joint_integrable_K2_exp_primeIntegrand_right β
  -- Step A: rewrite LHS y-integrand using h_K_eq, distributing primeIntegrand inside the t-integral.
  -- Use Real-exp form to match joint integrability.
  have h_y_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.primeIntegrand β 2 y := by
    intro y
    have h1 : (∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Complex.exp (-2 * (t : ℂ)^2)) =
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      show ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t * Complex.exp (-2 * (t : ℂ)^2) =
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t * ((Real.exp (-2 * t^2) : ℝ) : ℂ)
      rw [cexp_eq_rexp_neg_two_sq t]
    have h2 : ((∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ)) * Contour.primeIntegrand β 2 y) =
      ∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y :=
      (MeasureTheory.integral_mul_const (Contour.primeIntegrand β 2 y)
        (fun t => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ))).symm
    calc ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) * Contour.primeIntegrand β 2 y
        = (2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.primeIntegrand β 2 y := by rw [h_K_eq y]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.primeIntegrand β 2 y) := by ring
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ)) * Contour.primeIntegrand β 2 y) := by rw [h1]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.primeIntegrand β 2 y := by rw [h2]
  -- Step B: apply integral_congr to LHS of the goal.
  have h_LHS :
      (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
            Contour.primeIntegrand β 2 y) =
      ∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.primeIntegrand β 2 y :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => h_y_eq y))
  -- Step C: pull out 2π.
  have h_const_mul :
      (∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.primeIntegrand β 2 y) =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ y : ℝ,
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
            Contour.primeIntegrand β 2 y :=
    MeasureTheory.integral_const_mul _ _
  -- Step D: swap integrals (apply .symm; integral_integral_swap goes ∫t∫y → ∫y∫t).
  have h_swap : (∫ y : ℝ,
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.primeIntegrand β 2 y) =
      ∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.primeIntegrand β 2 y :=
    (MeasureTheory.integral_integral_swap h_joint).symm
  -- Step E: pull cexp out of inner y-integral.
  have h_factor : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y) =
      Complex.exp (-2 * (t : ℂ)^2) *
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.primeIntegrand β 2 y) := by
    intro t
    rw [cexp_eq_rexp_neg_two_sq t]
    have h_pull : (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y) =
        ∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      ring
    rw [h_pull]
    exact MeasureTheory.integral_const_mul ((Real.exp (-2 * t^2) : ℝ) : ℂ)
      (fun y : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.primeIntegrand β 2 y)
  have h_outer :
      (∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.primeIntegrand β 2 y) =
      ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
        (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.primeIntegrand β 2 y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact h_factor t
  rw [h_LHS, h_const_mul, h_swap, h_outer]

#print axioms h_fubini_right

/-- **Fubini-Plancherel relation on the left edge (Re s = -1), arch piece:**
```
∫_y K(-1+iy) · archIntegrand β (-1) y dy =
  2π · ∫_{Ioi 0} exp(-2t²) · K_2_arch t β dt.
```
Same structure as `h_fubini_right` but at σ = -1, with the inner y-integral
collapsing to the definitionally-given `K_2_arch t β`. -/
theorem h_fubini_left_arch (β : ℝ) :
    (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.archIntegrand β (-1) y) =
      2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β := by
  have h_K_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
        2 * ((Real.pi : ℝ) : ℂ) *
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Complex.exp (-2 * (t : ℂ)^2) := fun y =>
    ZD.WeilPositivity.OfflineDetectorPlancherel.gaussianDefectEntireKernel_eq_K2_integral _
  have h_joint := joint_integrable_K2_exp_archIntegrand_left β
  have h_y_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.archIntegrand β (-1) y =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.archIntegrand β (-1) y := by
    intro y
    have h1 : (∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Complex.exp (-2 * (t : ℂ)^2)) =
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      show ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * Complex.exp (-2 * (t : ℂ)^2) =
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * ((Real.exp (-2 * t^2) : ℝ) : ℂ)
      rw [cexp_eq_rexp_neg_two_sq t]
    have h2 : ((∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ)) * Contour.archIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.archIntegrand β (-1) y :=
      (MeasureTheory.integral_mul_const (Contour.archIntegrand β (-1) y)
        (fun t : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ))).symm
    calc ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) * Contour.archIntegrand β (-1) y
        = (2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.archIntegrand β (-1) y := by
          rw [h_K_eq y]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.archIntegrand β (-1) y) := by ring
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ)) * Contour.archIntegrand β (-1) y) := by rw [h1]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.archIntegrand β (-1) y := by rw [h2]
  have h_LHS :
      (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            Contour.archIntegrand β (-1) y) =
      ∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.archIntegrand β (-1) y :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => h_y_eq y))
  have h_const_mul :
      (∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.archIntegrand β (-1) y) =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ y : ℝ,
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
            Contour.archIntegrand β (-1) y :=
    MeasureTheory.integral_const_mul _ _
  have h_swap : (∫ y : ℝ,
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.archIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.archIntegrand β (-1) y :=
    (MeasureTheory.integral_integral_swap h_joint).symm
  have h_factor : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.archIntegrand β (-1) y) =
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β := by
    intro t
    rw [cexp_eq_rexp_neg_two_sq t]
    have h_pull : (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.archIntegrand β (-1) y) =
        ∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.archIntegrand β (-1) y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      ring
    rw [h_pull]
    have h_pull2 : (∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.archIntegrand β (-1) y)) =
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          ∫ y : ℝ, (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.archIntegrand β (-1) y) :=
      MeasureTheory.integral_const_mul ((Real.exp (-2 * t^2) : ℝ) : ℂ)
        (fun y : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.archIntegrand β (-1) y)
    rw [h_pull2]
    -- K_2_arch t β = ∫ y, K_2(-1+iy, t) · archIntegrand β (-1) y by definition.
    rfl
  have h_outer :
      (∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.archIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact h_factor t
  rw [h_LHS, h_const_mul, h_swap, h_outer]

#print axioms h_fubini_left_arch

/-- **Fubini-Plancherel relation on the left edge (Re s = -1), reflected-prime piece:**
```
∫_y K(-1+iy) · reflectedPrime β (-1) y dy =
  2π · ∫_{Ioi 0} exp(-2t²) · (∫_y K_2(-1+iy,t) · reflectedPrime β (-1) y dy) dt.
```
The inner integrand `(deriv riemannZeta/riemannZeta)(1-(-1+iy)) · pairTestMellin β (-1+iy)`
is definitionally equal to `Contour.reflectedPrimeIntegrand β (-1) y` per
`def reflectedPrimeIntegrand` in `WeilPairIBP.lean`. -/
theorem h_fubini_left_refl (β : ℝ) :
    (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.reflectedPrimeIntegrand β (-1) y) =
      2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          (∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
              riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
  -- The inner form is definitionally Contour.reflectedPrimeIntegrand β (-1) y.
  -- We prove the equality with `reflectedPrimeIntegrand` form, then the final RHS
  -- is the same by `rfl` (def is `(ζ'/ζ)(1-s) · pairTestMellin β s`).
  have h_K_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
        2 * ((Real.pi : ℝ) : ℂ) *
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Complex.exp (-2 * (t : ℂ)^2) := fun y =>
    ZD.WeilPositivity.OfflineDetectorPlancherel.gaussianDefectEntireKernel_eq_K2_integral _
  have h_joint := joint_integrable_K2_exp_reflectedPrime_left β
  have h_y_eq : ∀ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.reflectedPrimeIntegrand β (-1) y =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.reflectedPrimeIntegrand β (-1) y := by
    intro y
    have h1 : (∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Complex.exp (-2 * (t : ℂ)^2)) =
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      show ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * Complex.exp (-2 * (t : ℂ)^2) =
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * ((Real.exp (-2 * t^2) : ℝ) : ℂ)
      rw [cexp_eq_rexp_neg_two_sq t]
    have h2 : ((∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ)) * Contour.reflectedPrimeIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ),
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y :=
      (MeasureTheory.integral_mul_const (Contour.reflectedPrimeIntegrand β (-1) y)
        (fun t : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ))).symm
    calc ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) * Contour.reflectedPrimeIntegrand β (-1) y
        = (2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.reflectedPrimeIntegrand β (-1) y := by
          rw [h_K_eq y]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Complex.exp (-2 * (t : ℂ)^2)) * Contour.reflectedPrimeIntegrand β (-1) y) := by ring
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ((∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ)) *
                Contour.reflectedPrimeIntegrand β (-1) y) := by rw [h1]
      _ = 2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.reflectedPrimeIntegrand β (-1) y := by rw [h2]
  have h_LHS :
      (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorEndpoint.gaussianDefectEntireKernel_local
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            Contour.reflectedPrimeIntegrand β (-1) y) =
      ∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.reflectedPrimeIntegrand β (-1) y :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => h_y_eq y))
  have h_const_mul :
      (∫ y : ℝ,
          2 * ((Real.pi : ℝ) : ℂ) *
            ∫ t in Set.Ioi (0:ℝ),
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
              Contour.reflectedPrimeIntegrand β (-1) y) =
      2 * ((Real.pi : ℝ) : ℂ) *
        ∫ y : ℝ,
          ∫ t in Set.Ioi (0:ℝ),
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
            Contour.reflectedPrimeIntegrand β (-1) y :=
    MeasureTheory.integral_const_mul _ _
  have h_swap : (∫ y : ℝ,
        ∫ t in Set.Ioi (0:ℝ),
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.reflectedPrimeIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.reflectedPrimeIntegrand β (-1) y :=
    (MeasureTheory.integral_integral_swap h_joint).symm
  have h_factor : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y) =
      Complex.exp (-2 * (t : ℂ)^2) *
        ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    intro t
    rw [cexp_eq_rexp_neg_two_sq t]
    have h_pull : (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y) =
        ∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      ring
    rw [h_pull]
    have h_pull2 : (∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y)) =
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          ∫ y : ℝ, (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y) :=
      MeasureTheory.integral_const_mul ((Real.exp (-2 * t^2) : ℝ) : ℂ)
        (fun y : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.reflectedPrimeIntegrand β (-1) y)
    rw [h_pull2]
    -- Contour.reflectedPrimeIntegrand β (-1) y = (ζ'/ζ)(1-(-1+iy)) · pairTestMellin β (-1+iy) by def.
    rfl
  have h_outer :
      (∫ t in Set.Ioi (0:ℝ), ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          Contour.reflectedPrimeIntegrand β (-1) y) =
      ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
        ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact h_factor t
  rw [h_LHS, h_const_mul, h_swap, h_outer]

#print axioms h_fubini_left_refl

/-! ## Inner integrabilities via `Integrable.integral_prod_left` -/

/-- **Inner integrability for the right edge:**
```
IntegrableOn (t ↦ exp(-2t²) · ∫_y K_2(2+iy,t)·primeIntegrand β 2 y dy) (Ioi 0).
```
Derived from `joint_integrable_K2_exp_primeIntegrand_right` via
`Integrable.integral_prod_left`. -/
theorem h_int_inner_right (β : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.primeIntegrand β 2 y) (Set.Ioi (0:ℝ)) := by
  have h_joint := joint_integrable_K2_exp_primeIntegrand_right β
  -- ∫ y, K_2 · rexp · PI dy is integrable in t.
  have h_inner_int :
      Integrable (fun t : ℝ => ∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y) (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    h_joint.integral_prod_left
  -- Now show this equals the target via h_factor.
  have h_factor : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y) =
      Complex.exp (-2 * (t : ℂ)^2) *
        (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.primeIntegrand β 2 y) := by
    intro t
    rw [cexp_eq_rexp_neg_two_sq t]
    have h_pull : (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.primeIntegrand β 2 y) =
        ∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      ring
    rw [h_pull]
    have h_pull2 : (∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y)) =
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          ∫ y : ℝ, (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) :=
      MeasureTheory.integral_const_mul ((Real.exp (-2 * t^2) : ℝ) : ℂ)
        (fun y : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.primeIntegrand β 2 y)
    rw [h_pull2]
  -- Convert h_inner_int to the target form via congr.
  have h_congr : (fun t : ℝ => ∫ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
      Contour.primeIntegrand β 2 y) =
      (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) := by
    funext t
    exact h_factor t
  rw [h_congr] at h_inner_int
  exact h_inner_int

#print axioms h_int_inner_right

/-- **Inner integrability for the left edge, reflected piece:**
```
IntegrableOn (t ↦ exp(-2t²) · ∫_y K_2(-1+iy,t) · ((ζ'/ζ)(2-iy) · pairTestMellin β (-1+iy))) (Ioi 0).
```
Derived from `joint_integrable_K2_exp_reflectedPrime_left` via
`Integrable.integral_prod_left`.  The expanded inner integrand on the target
matches `Contour.reflectedPrimeIntegrand β (-1) y` definitionally. -/
theorem h_int_inner_refl (β : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
      (Set.Ioi (0:ℝ)) := by
  have h_joint := joint_integrable_K2_exp_reflectedPrime_left β
  have h_inner_int :
      Integrable (fun t : ℝ => ∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    h_joint.integral_prod_left
  have h_factor : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y) =
      Complex.exp (-2 * (t : ℂ)^2) *
        (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    intro t
    rw [cexp_eq_rexp_neg_two_sq t]
    have h_pull : (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
        Contour.reflectedPrimeIntegrand β (-1) y) =
        ∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      ring
    rw [h_pull]
    have h_pull2 : (∫ y : ℝ, ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y)) =
        ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
          ∫ y : ℝ, (ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.reflectedPrimeIntegrand β (-1) y) :=
      MeasureTheory.integral_const_mul ((Real.exp (-2 * t^2) : ℝ) : ℂ)
        (fun y : ℝ => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.reflectedPrimeIntegrand β (-1) y)
    rw [h_pull2]
    -- The inner integrand of the target is reflectedPrimeIntegrand β (-1) y by definition.
    rfl
  have h_congr : (fun t : ℝ => ∫ y : ℝ,
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
        (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((Real.exp (-2 * t^2) : ℝ) : ℂ) *
      Contour.reflectedPrimeIntegrand β (-1) y) =
      (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
              riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    funext t
    exact h_factor t
  rw [h_congr] at h_inner_int
  exact h_inner_int

#print axioms h_int_inner_refl

/-! ## Final composition: `K_rectangle_LHS_eq_pRD_minus_arch_target_holds_unconditional` -/

/-- **Unconditional discharge** of `K_rectangle_LHS_eq_pRD_minus_arch_target β` for every
`β ∈ (0,1)`, by feeding the 7 hypotheses (3 Fubini's + 2 left-edge boundary
integrabilities + 2 inner integrabilities) into
`K_rectangle_LHS_eq_pRD_minus_arch_target_holds`. -/
theorem K_rectangle_LHS_eq_pRD_minus_arch_target_holds_unconditional
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_rectangle_LHS_eq_pRD_minus_arch_target β :=
  ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_rectangle_LHS_eq_pRD_minus_arch_target_holds
    β hβ
    (h_fubini_right β)
    (h_fubini_left_arch β)
    (h_fubini_left_refl β)
    (h_int_left_arch β)
    (h_int_left_refl β)
    (h_int_inner_right β)
    (h_int_inner_refl β)

#print axioms K_rectangle_LHS_eq_pRD_minus_arch_target_holds_unconditional

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
