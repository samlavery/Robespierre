import Mathlib
import RequestProject.WeilContour
import RequestProject.GaussianClosedForm

/-!
# Real-analyticity of `pairTestMellin (·) ρ` in `β` for `0 < ρ.re`

**Step 4c R1a — CLOSED axiom-clean** (with the necessary `0 < ρ.re`
hypothesis matching the natural Mellin-transform domain).

For every `ρ` with `0 < ρ.re`, the function `β ↦ pairTestMellin β ρ` is
real-analytic on all of `Set.univ` (`pairTestMellin_analyticOnNhd_in_beta`).
The hypothesis `0 < ρ.re` is required — without it, `pairTestMellin β ρ`
is a divergent integral and analyticity in β is vacuous. For the RH
application this is fine: nontrivial zeros have `ρ.re ∈ (0, 1)`.

## Strategy

1. Complex-`c` extension `coshGaussMellinC : ℂ → ℂ → ℂ` (§1).
2. Pointwise bounds on the c-derivative integrand (§2-§2.5).
3. Parametric-integral c-derivative via
   `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (§3).
4. ℂ-analyticity in c via `Differentiable.analyticOnNhd` (§4).
5. Restrict-scalars + `Complex.ofRealCLM` to get ℝ-analyticity in real c.
6. Compose with linear-in-β c-arguments via `pairTestMellin_cosh_expansion`.

## Key axiom-clean exports

- `pairTestMellin_analyticOnNhd_in_beta` — main theorem.
- `coshGaussMellin_analyticOnNhd_in_c` — auxiliary (real-`c` analyticity).
- `coshGaussMellinC_analyticOnNhd_in_c` — auxiliary (complex-`c` analyticity).
-/

open Complex Real MeasureTheory Set Filter Asymptotics

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-! ### § 0 — Trivial vanishing at `β = 1/2`. -/

theorem pair_cosh_gauss_test_at_half (t : ℝ) :
    pair_cosh_gauss_test (1/2 : ℝ) t = 0 := by
  rw [pair_cosh_gauss_test_sinh_factor]
  have h_zero : Real.sinh (((1/2 : ℝ) - 1/2) * t) ^ 2 = 0 := by
    rw [show ((1/2 : ℝ) - 1/2) = 0 from by norm_num, zero_mul, Real.sinh_zero]
    ring
  rw [show (4 : ℝ) * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
        Real.sinh (((1/2 : ℝ) - 1/2) * t) ^ 2 * (ψ_gaussian t) ^ 2 =
        4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ψ_gaussian t) ^ 2 *
        Real.sinh (((1/2 : ℝ) - 1/2) * t) ^ 2 from by ring,
      h_zero, mul_zero]

theorem pairTestMellin_at_half (ρ : ℂ) :
    pairTestMellin (1/2 : ℝ) ρ = 0 := by
  unfold pairTestMellin mellin
  have h_zero_ae : ∀ t ∈ Ioi (0 : ℝ),
      (t : ℂ) ^ (ρ - 1) • ((pair_cosh_gauss_test (1/2 : ℝ) t : ℝ) : ℂ) = 0 := by
    intro t _
    rw [pair_cosh_gauss_test_at_half]
    simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => h_zero_ae t ht)]
  simp

/-! ### § 1 — Complex-`c` extension of `coshGaussMellin`. -/

/-- **Complex-`c` cosh-Gaussian Mellin.** Mellin transform of
`Complex.cosh (c·t) · exp(−2 t²)` for complex parameter `c`. -/
noncomputable def coshGaussMellinC (c : ℂ) (ρ : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi (0 : ℝ),
    (t : ℂ) ^ (ρ - 1) •
      (Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t ^ 2) : ℝ) : ℂ))

/-- Agreement on real `c`. -/
lemma coshGaussMellinC_ofReal (c : ℝ) (ρ : ℂ) :
    coshGaussMellinC (c : ℂ) ρ = coshGaussMellin c ρ := by
  unfold coshGaussMellinC coshGaussMellin mellin
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  simp only
  congr 1
  -- Complex.cosh ((c:ℂ) * t) = (Real.cosh (c·t) : ℂ).
  have h1 : ((c : ℂ) * (t : ℂ)) = (((c * t : ℝ)) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cosh]

/-! ### § 2 — Bounds on the complex `c`-derivative integrand.

The `c`-derivative of `cosh(c·t)·exp(−2 t²)` is `t·sinh(c·t)·exp(−2 t²)`.
For `c` in a complex ball, we have a uniform integrable bound
`t·exp(R·t)·exp(−2 t²)` where `R = ‖c₀‖ + radius`. -/

/-- **`Complex.sinh` norm bound:** `‖sinh z‖ ≤ exp ‖z‖`. -/
lemma complex_sinh_norm_le_exp (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sinh, Complex.norm_div]
  have h1 : ‖Complex.exp z - Complex.exp (-z)‖ ≤
      ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_sub_le _ _
  have h2 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
  have h3 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    have := Complex.norm_exp_le_exp_norm (-z)
    rwa [norm_neg] at this
  have h_norm2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h_norm2]
  have : ‖Complex.exp z - Complex.exp (-z)‖ ≤ 2 * Real.exp ‖z‖ := by
    calc ‖Complex.exp z - Complex.exp (-z)‖
        ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := h1
      _ ≤ Real.exp ‖z‖ + Real.exp ‖z‖ := by linarith
      _ = 2 * Real.exp ‖z‖ := by ring
  linarith

/-- **`Complex.cosh` norm bound:** `‖cosh z‖ ≤ exp ‖z‖`. -/
lemma complex_cosh_norm_le_exp (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.cosh, Complex.norm_div]
  have h1 : ‖Complex.exp z + Complex.exp (-z)‖ ≤
      ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
  have h2 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
  have h3 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    have := Complex.norm_exp_le_exp_norm (-z)
    rwa [norm_neg] at this
  have h_norm2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h_norm2]
  have : ‖Complex.exp z + Complex.exp (-z)‖ ≤ 2 * Real.exp ‖z‖ := by
    calc ‖Complex.exp z + Complex.exp (-z)‖
        ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := h1
      _ ≤ Real.exp ‖z‖ + Real.exp ‖z‖ := by linarith
      _ = 2 * Real.exp ‖z‖ := by ring
  linarith

/-! ### § 2.5 — Integrability infrastructure for the parametric integral.

The parametric integral derivative argument needs:
* an integrable bound `bound t = K · t^(ρ.re) · exp(-t²)` valid for `c` in
  any complex ball `Metric.ball c₀ R`,
* integrability of the integrand `F c₀ t = t^(ρ-1) · cosh(c₀·t) · exp(-2t²)`
  itself,
* integrability of the derivative `F' c t = t^(ρ-1) · t · sinh(c·t) · exp(-2t²)`
  via the bound. -/

/-- Real dominating bound for `‖F' c t‖` when `c ∈ Metric.ball c₀ R`:

Setting `K = ‖c₀‖ + R` (an upper bound for `‖c‖`),
the c-derivative integrand `t^(ρ-1) · t · sinh(c·t) · exp(-2t²)` has norm
`≤ exp(K²/4) · t^(ρ.re) · exp(-1·t²)` on `Ioi 0`. -/
lemma coshGaussMellinC_deriv_bound_integrable {ρ : ℂ} (hρ : -1 < ρ.re) (K : ℝ) :
    IntegrableOn
      (fun t : ℝ => Real.exp (K^2 / 4) * (t ^ ρ.re * Real.exp (-1 * t^2)))
      (Ioi (0 : ℝ)) := by
  have h_base : IntegrableOn (fun t : ℝ => t ^ ρ.re * Real.exp (-1 * t^2))
      (Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1) hρ
  exact h_base.const_mul (Real.exp (K^2 / 4))

/-- Quadratic-completion bound: `K·t - 2·t² ≤ K²/4 - t²` for all real `t`. -/
lemma quadratic_completion_bound (K t : ℝ) :
    K * t - 2 * t^2 ≤ K^2 / 4 - t^2 := by
  nlinarith [sq_nonneg (K - 2*t), sq_nonneg t]

/-- The pointwise norm bound for the derivative integrand. For `c` with
`‖c‖ ≤ K` and `t > 0`, we have
`‖t^(ρ-1) · t · Complex.sinh(c·t) · exp(-2t²)‖ ≤ exp(K²/4) · t^(ρ.re) · exp(-t²)`. -/
lemma coshGaussMellinC_deriv_pointwise_bound
    {ρ c : ℂ} {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : ‖c‖ ≤ K) :
    ‖((t : ℂ) ^ (ρ - 1)) *
        ((t : ℂ) * Complex.sinh (c * (t : ℂ)) *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ))‖ ≤
      Real.exp (K^2 / 4) * (t ^ ρ.re * Real.exp (-1 * t^2)) := by
  have ht_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have ht_nn : (0 : ℝ) ≤ t := ht.le
  -- Norm of (t : ℂ) ^ (ρ - 1) on positive reals.
  have h_pow : ‖(t : ℂ) ^ (ρ - 1)‖ = t ^ (ρ.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  -- Bound on sinh.
  have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
    have h := complex_sinh_norm_le_exp (c * (t : ℂ))
    have hnorm : ‖c * (t : ℂ)‖ = ‖c‖ * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
    rw [hnorm] at h
    exact h
  -- Norm of t · sinh(c·t) · exp(-2t²)
  have h_t_real : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
  have h_exp_real : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  -- Compute the LHS norm.
  rw [norm_mul, norm_mul, norm_mul, h_pow, h_t_real, h_exp_real]
  -- Goal: t^(ρ.re-1) * (t * ‖sinh (c*t)‖ * exp(-2t²))
  --     ≤ exp(K²/4) * (t^ρ.re * exp(-1·t²))
  have h_sinh_bd : t * ‖Complex.sinh (c * (t : ℂ))‖ * Real.exp (-2 * t^2) ≤
      t * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_sinh_norm ht_nn) (Real.exp_pos _).le
  have h_K_bd : t * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤
      t * Real.exp (K * t) * Real.exp (-2 * t^2) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ ht_nn
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hK ht_nn
  -- Combine via the completion bound.
  have h_combine : t * Real.exp (K * t) * Real.exp (-2 * t^2) =
      t * Real.exp (K * t - 2 * t^2) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h_quad : Real.exp (K * t - 2 * t^2) ≤ Real.exp (K^2 / 4 - t^2) :=
    Real.exp_le_exp.mpr (quadratic_completion_bound K t)
  have h_final_exp : t * Real.exp (K * t - 2 * t^2) ≤
      t * Real.exp (K^2 / 4 - t^2) :=
    mul_le_mul_of_nonneg_left h_quad ht_nn
  have h_split : Real.exp (K^2 / 4 - t^2) =
      Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  -- Now factor t^(ρ.re-1) on LHS, t^ρ.re on RHS.
  have ht_pow_pos : 0 < t ^ (ρ.re - 1) := Real.rpow_pos_of_pos ht _
  have h_t_split : t ^ (ρ.re - 1) * t = t ^ ρ.re := by
    have h1 : t ^ (ρ.re - 1) * t = t ^ (ρ.re - 1) * t ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add ht]
    congr 1; ring
  -- Chain inequalities.
  calc t ^ (ρ.re - 1) * (t * ‖Complex.sinh (c * (t : ℂ))‖ * Real.exp (-2 * t^2))
      ≤ t ^ (ρ.re - 1) * (t * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) :=
        mul_le_mul_of_nonneg_left h_sinh_bd ht_pow_pos.le
    _ ≤ t ^ (ρ.re - 1) * (t * Real.exp (K * t) * Real.exp (-2 * t^2)) :=
        mul_le_mul_of_nonneg_left h_K_bd ht_pow_pos.le
    _ = t ^ (ρ.re - 1) * (t * Real.exp (K * t - 2 * t^2)) := by rw [h_combine]
    _ ≤ t ^ (ρ.re - 1) * (t * Real.exp (K^2 / 4 - t^2)) :=
        mul_le_mul_of_nonneg_left h_final_exp ht_pow_pos.le
    _ = t ^ (ρ.re - 1) * t * Real.exp (K^2 / 4 - t^2) := by ring
    _ = t ^ ρ.re * Real.exp (K^2 / 4 - t^2) := by rw [h_t_split]
    _ = t ^ ρ.re * (Real.exp (K^2 / 4) * Real.exp (-1 * t^2)) := by rw [h_split]
    _ = Real.exp (K^2 / 4) * (t ^ ρ.re * Real.exp (-1 * t^2)) := by ring

/-- Integrand norm bound: for `c` with `‖c‖ ≤ K` and `t > 0`,
`‖t^(ρ-1) · cosh(c·t) · exp(-2t²)‖ ≤ exp(K²/4) · t^(ρ.re - 1) · exp(-t²)`. -/
lemma coshGaussMellinC_integrand_pointwise_bound
    {ρ c : ℂ} {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : ‖c‖ ≤ K) :
    ‖((t : ℂ) ^ (ρ - 1)) *
        (Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))‖ ≤
      Real.exp (K^2 / 4) * (t ^ (ρ.re - 1) * Real.exp (-1 * t^2)) := by
  have ht_nn : (0 : ℝ) ≤ t := ht.le
  have h_pow : ‖(t : ℂ) ^ (ρ - 1)‖ = t ^ (ρ.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp
  have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
    have h := complex_cosh_norm_le_exp (c * (t : ℂ))
    have hnorm : ‖c * (t : ℂ)‖ = ‖c‖ * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
    rw [hnorm] at h; exact h
  have h_exp_real : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rw [norm_mul, norm_mul, h_pow, h_exp_real]
  have ht_pow_pos : 0 < t ^ (ρ.re - 1) := Real.rpow_pos_of_pos ht _
  have h_cosh_bd : ‖Complex.cosh (c * (t : ℂ))‖ * Real.exp (-2 * t^2) ≤
      Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
    mul_le_mul_of_nonneg_right h_cosh_norm (Real.exp_pos _).le
  have h_K_bd : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤
      Real.exp (K * t) * Real.exp (-2 * t^2) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hK ht_nn
  have h_combine : Real.exp (K * t) * Real.exp (-2 * t^2) =
      Real.exp (K * t - 2 * t^2) := by rw [← Real.exp_add]; ring_nf
  have h_quad : Real.exp (K * t - 2 * t^2) ≤ Real.exp (K^2 / 4 - t^2) :=
    Real.exp_le_exp.mpr (quadratic_completion_bound K t)
  have h_split : Real.exp (K^2 / 4 - t^2) =
      Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by rw [← Real.exp_add]; ring_nf
  calc t ^ (ρ.re - 1) * (‖Complex.cosh (c * (t : ℂ))‖ * Real.exp (-2 * t^2))
      ≤ t ^ (ρ.re - 1) * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) :=
        mul_le_mul_of_nonneg_left h_cosh_bd ht_pow_pos.le
    _ ≤ t ^ (ρ.re - 1) * (Real.exp (K * t) * Real.exp (-2 * t^2)) :=
        mul_le_mul_of_nonneg_left h_K_bd ht_pow_pos.le
    _ = t ^ (ρ.re - 1) * Real.exp (K * t - 2 * t^2) := by rw [h_combine]
    _ ≤ t ^ (ρ.re - 1) * Real.exp (K^2 / 4 - t^2) :=
        mul_le_mul_of_nonneg_left h_quad ht_pow_pos.le
    _ = t ^ (ρ.re - 1) * (Real.exp (K^2 / 4) * Real.exp (-1 * t^2)) := by rw [h_split]
    _ = Real.exp (K^2 / 4) * (t ^ (ρ.re - 1) * Real.exp (-1 * t^2)) := by ring

/-- Continuity of the c-integrand `c ↦ t^(ρ-1) · cosh(c·t) · exp(-2t²)` (in ℂ).
Used for AE-strong-measurability. -/
lemma coshGaussMellinC_integrand_continuous (ρ : ℂ) (t : ℝ) :
    Continuous (fun c : ℂ =>
      ((t : ℂ) ^ (ρ - 1)) *
        (Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))) := by
  refine continuous_const.mul ?_
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_cosh.comp (continuous_id.mul continuous_const)

/-! ### § 2.6 — Parametric integral differentiability of `coshGaussMellinC` in `c`. -/

/-- The c-derivative of the cosh-Gaussian integrand at a point. -/
lemma hasDerivAt_coshGaussMellinC_integrand (ρ : ℂ) (t : ℝ) (c₀ : ℂ) :
    HasDerivAt
      (fun c : ℂ =>
        ((t : ℂ) ^ (ρ - 1)) *
          (Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)))
      (((t : ℂ) ^ (ρ - 1)) *
        (((t : ℂ) * Complex.sinh (c₀ * (t : ℂ))) *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ)))
      c₀ := by
  -- d/dc cosh(c·t) = sinh(c·t) · t
  have h_inner : HasDerivAt (fun c : ℂ => c * (t : ℂ)) (t : ℂ) c₀ := by
    simpa using (hasDerivAt_id c₀).mul_const (t : ℂ)
  have h_cosh : HasDerivAt (fun c : ℂ => Complex.cosh (c * (t : ℂ)))
      (Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) c₀ := h_inner.ccosh
  -- multiply by exp(-2t²)
  have h_with_exp : HasDerivAt
      (fun c : ℂ => Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      ((Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      c₀ :=
    h_cosh.mul_const _
  -- prefix by constant t^(ρ-1)
  have := h_with_exp.const_mul ((t : ℂ) ^ (ρ - 1))
  convert this using 1
  ring

/-- **Differentiability of `coshGaussMellinC c ρ` in `c` (complex).**

For `0 < ρ.re`, the function `c ↦ coshGaussMellinC c ρ` is `Differentiable ℂ`
at every `c₀`. The derivative is the integral of the c-derivative of the
integrand, which exists by the dominated-convergence parametric integral
theorem. -/
theorem coshGaussMellinC_differentiableAt_in_c (ρ : ℂ) (hρ : 0 < ρ.re) (c₀ : ℂ) :
    DifferentiableAt ℂ (fun c : ℂ => coshGaussMellinC c ρ) c₀ := by
  -- Take ball of radius 1 around c₀.
  set R : ℝ := 1
  set K : ℝ := ‖c₀‖ + R
  set s : Set ℂ := Metric.ball c₀ R
  have hs : s ∈ nhds c₀ := Metric.ball_mem_nhds c₀ (by norm_num : (0 : ℝ) < R)
  -- Define F and F'.
  set F : ℂ → ℝ → ℂ := fun c t =>
    ((t : ℂ) ^ (ρ - 1)) *
      (Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
  set F' : ℂ → ℝ → ℂ := fun c t =>
    ((t : ℂ) ^ (ρ - 1)) *
      (((t : ℂ) * Complex.sinh (c * (t : ℂ))) *
        ((Real.exp (-2 * t^2) : ℝ) : ℂ))
  set bound : ℝ → ℝ := fun t =>
    Real.exp (K^2 / 4) * (t ^ ρ.re * Real.exp (-1 * t^2))
  -- AEStronglyMeasurable for F x for x in nhds c₀.
  have hρ_neg1 : -1 < ρ.re - 1 := by linarith
  have hρ_pos : -1 < ρ.re := by linarith
  -- F c is continuous on Ioi 0 (in t), so AE-strongly-measurable on Ioi 0.
  -- Auxiliary: continuity of t ↦ (t : ℂ)^(ρ-1) at any t > 0.
  have h_pow_cont : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
      ContinuousAt (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) t := by
    intro t ht
    apply ContinuousAt.cpow
    · exact Complex.continuous_ofReal.continuousAt
    · exact continuousAt_const
    · refine Or.inl ?_
      simp only [Complex.ofReal_re]
      exact_mod_cast (Set.mem_Ioi.mp ht)
  -- Auxiliary: continuity of t ↦ exp(-2t²) coerced to ℂ.
  have h_gaussExp_cont :
      Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))
  have h_meas_aux : ∀ c : ℂ, AEStronglyMeasurable (F c) (volume.restrict (Ioi (0:ℝ))) := by
    intro c
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (h_pow_cont t ht) ?_
    refine ContinuousAt.mul ?_ h_gaussExp_cont.continuousAt
    exact Complex.continuous_cosh.continuousAt.comp
      ((continuous_const.mul Complex.continuous_ofReal).continuousAt)
  have hF_meas : ∀ᶠ x in nhds c₀, AEStronglyMeasurable (F x) (volume.restrict (Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun c => h_meas_aux c)
  -- Integrability of F c₀ via the bound.
  have h_F_bound_ae :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))), ‖F c₀ a‖ ≤
        Real.exp (K^2 / 4) * (a ^ (ρ.re - 1) * Real.exp (-1 * a^2)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht
    exact coshGaussMellinC_integrand_pointwise_bound (ρ := ρ) (c := c₀) ht
      (by simp [K, R] : ‖c₀‖ ≤ K)
  have h_int_bound_F :
      Integrable (fun t : ℝ => Real.exp (K^2 / 4) * (t ^ (ρ.re - 1) * Real.exp (-1 * t^2)))
        (volume.restrict (Ioi (0:ℝ))) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (s := ρ.re - 1)
      (by norm_num : (0 : ℝ) < 1) hρ_neg1)
    exact (h.const_mul (Real.exp (K^2 / 4)))
  have hF_int : Integrable (F c₀) (volume.restrict (Ioi (0:ℝ))) := by
    refine Integrable.mono' h_int_bound_F (h_meas_aux c₀) ?_
    exact h_F_bound_ae
  -- AEStronglyMeasurable for F' c₀.
  have h_meas'_aux : AEStronglyMeasurable (F' c₀) (volume.restrict (Ioi (0:ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (h_pow_cont t ht) ?_
    refine ContinuousAt.mul ?_ h_gaussExp_cont.continuousAt
    refine ContinuousAt.mul Complex.continuous_ofReal.continuousAt ?_
    exact Complex.continuous_sinh.continuousAt.comp
      ((continuous_const.mul Complex.continuous_ofReal).continuousAt)
  -- Bound for F' c on s.
  have h_bound :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))), ∀ x ∈ s, ‖F' x a‖ ≤ bound a := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht x hx
    have hx_norm : ‖x‖ ≤ K := by
      have h1 : dist x c₀ < R := hx
      have h2 : ‖x‖ ≤ ‖c₀‖ + dist x c₀ := by
        have := norm_le_norm_add_norm_sub' x c₀
        simpa [dist_eq_norm] using this
      linarith
    exact coshGaussMellinC_deriv_pointwise_bound (ρ := ρ) (c := x) ht hx_norm
  -- Bound is integrable.
  have h_bound_int : Integrable bound (volume.restrict (Ioi (0:ℝ))) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (s := ρ.re)
      (by norm_num : (0 : ℝ) < 1) hρ_pos)
    exact (h.const_mul (Real.exp (K^2 / 4)))
  -- HasDerivAt for F at every (x, a) for x ∈ s.
  have h_diff :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))), ∀ x ∈ s, HasDerivAt (fun y => F y a) (F' x a) x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t _ht x _hx
    exact hasDerivAt_coshGaussMellinC_integrand ρ t x
  -- Apply the parametric integral derivative theorem.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := F) (x₀ := c₀) (s := s) (bound := bound)
    (F' := F')
    hs hF_meas hF_int h_meas'_aux h_bound h_bound_int h_diff
  -- Convert to DifferentiableAt.
  obtain ⟨_, hd⟩ := key
  have h_int_eq : (fun n => ∫ a, F n a ∂(volume.restrict (Ioi (0:ℝ)))) =
      (fun c : ℂ => coshGaussMellinC c ρ) := by
    funext c
    rfl
  rw [h_int_eq] at hd
  exact hd.differentiableAt

/-! ### § 2.7 — Analyticity of `coshGaussMellinC c ρ` in `c`. -/

/-- **`coshGaussMellinC c ρ` is `Differentiable ℂ` in `c`.** -/
theorem coshGaussMellinC_differentiable_in_c (ρ : ℂ) (hρ : 0 < ρ.re) :
    Differentiable ℂ (fun c : ℂ => coshGaussMellinC c ρ) :=
  fun c₀ => coshGaussMellinC_differentiableAt_in_c ρ hρ c₀

/-- **`coshGaussMellinC c ρ` is `AnalyticOnNhd ℂ` on `Set.univ` in `c`.** -/
theorem coshGaussMellinC_analyticOnNhd_in_c (ρ : ℂ) (hρ : 0 < ρ.re) :
    AnalyticOnNhd ℂ (fun c : ℂ => coshGaussMellinC c ρ) Set.univ :=
  (coshGaussMellinC_differentiable_in_c ρ hρ).differentiableOn.analyticOnNhd isOpen_univ

set_option backward.isDefEq.respectTransparency false in
/-- **`coshGaussMellin c ρ` is real-analytic in real `c` on `Set.univ`** for `0 < ρ.re`.

Strategy: complex differentiability of `coshGaussMellinC` (Phase A) gives complex
analyticity, which `restrictScalars` to ℝ, then composition with the
real-analytic `Complex.ofRealCLM : ℝ →L[ℝ] ℂ`, and finally `coshGaussMellinC_ofReal`. -/
lemma coshGaussMellin_analyticOnNhd_in_c (ρ : ℂ) (hρ : 0 < ρ.re) :
    AnalyticOnNhd ℝ (fun c : ℝ => coshGaussMellin c ρ) Set.univ := by
  -- Step 1: ℂ-analyticity in c.
  have h_ℂ : AnalyticOnNhd ℂ (fun c : ℂ => coshGaussMellinC c ρ) Set.univ :=
    coshGaussMellinC_analyticOnNhd_in_c ρ hρ
  -- Step 2: restrict scalars to ℝ.
  have h_ℝ_ℂ : AnalyticOnNhd ℝ (fun c : ℂ => coshGaussMellinC c ρ) Set.univ :=
    h_ℂ.restrictScalars
  -- Step 3: compose with Complex.ofRealCLM : ℝ →L[ℝ] ℂ.
  have h_comp :
      AnalyticOnNhd ℝ
        ((fun c : ℂ => coshGaussMellinC c ρ) ∘ Complex.ofRealCLM)
        (Complex.ofRealCLM ⁻¹' Set.univ) :=
    AnalyticOnNhd.compContinuousLinearMap (u := Complex.ofRealCLM) h_ℝ_ℂ
  -- Step 4: simplify preimage and unfold.
  have h_pre : Complex.ofRealCLM ⁻¹' (Set.univ : Set ℂ) = Set.univ := by
    rw [Set.preimage_univ]
  rw [h_pre] at h_comp
  -- Step 5: rewrite via coshGaussMellinC_ofReal.
  have h_eq : ((fun c : ℂ => coshGaussMellinC c ρ) ∘ Complex.ofRealCLM) =
      (fun c : ℝ => coshGaussMellin c ρ) := by
    funext c
    simp [Function.comp, Complex.ofRealCLM_apply, coshGaussMellinC_ofReal]
  rw [h_eq] at h_comp
  exact h_comp

/-- **`gaussMellin ρ` is constant in `c`, hence trivially analytic.** -/
theorem gaussMellin_analyticOnNhd_const (ρ : ℂ) :
    AnalyticOnNhd ℝ (fun _ : ℝ => gaussMellin ρ) Set.univ :=
  analyticOnNhd_const

/-! ### § 2.8 — Final analyticity of `pairTestMellin β ρ` in `β`. -/

/-- The β-affine maps used in the cosh expansion are real-analytic on `Set.univ`. -/
lemma analyticOnNhd_affine_2β_sub_pi3 :
    AnalyticOnNhd ℝ (fun β : ℝ => 2*β - Real.pi/3) Set.univ := fun _ _ =>
  ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)

lemma analyticOnNhd_affine_2_sub_pi3_sub_2β :
    AnalyticOnNhd ℝ (fun β : ℝ => 2 - Real.pi/3 - 2*β) Set.univ := fun _ _ =>
  ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)))

lemma analyticOnNhd_affine_2β_sub_1 :
    AnalyticOnNhd ℝ (fun β : ℝ => 2*β - 1) Set.univ := fun _ _ =>
  ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)

/-- **Real-analyticity of `β ↦ pairTestMellin β ρ` on `Set.univ`** (for `0 < ρ.re`).

Uses the cosh expansion `pairTestMellin_cosh_expansion` to reduce to the four
`coshGaussMellin · ρ` terms (each real-analytic in `c` by
`coshGaussMellin_analyticOnNhd_in_c`) precomposed with affine functions in `β`,
plus a constant `gaussMellin ρ`. -/
theorem pairTestMellin_analyticOnNhd_in_beta {ρ : ℂ} (hρ : 0 < ρ.re) :
    AnalyticOnNhd ℝ (fun β : ℝ => pairTestMellin β ρ) Set.univ := by
  -- Build the RHS of the cosh expansion as a function of β.
  set M : ℝ → ℂ := fun c => coshGaussMellin c ρ with hM_def
  have h_M : AnalyticOnNhd ℝ M Set.univ := coshGaussMellin_analyticOnNhd_in_c ρ hρ
  -- Helper: composition with affine map gives analyticity in β.
  have h_M1 : AnalyticOnNhd ℝ (fun β : ℝ => M (2*β - Real.pi/3)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2*β - Real.pi/3) (Set.mem_univ _))
      (analyticOnNhd_affine_2β_sub_pi3 β (Set.mem_univ _))
  have h_M2 : AnalyticOnNhd ℝ (fun β : ℝ => M (2 - Real.pi/3 - 2*β)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2 - Real.pi/3 - 2*β) (Set.mem_univ _))
      (analyticOnNhd_affine_2_sub_pi3_sub_2β β (Set.mem_univ _))
  have h_M3 : AnalyticOnNhd ℝ
      (fun _ : ℝ => M (1 - Real.pi/3)) Set.univ :=
    analyticOnNhd_const
  have h_M4 : AnalyticOnNhd ℝ (fun β : ℝ => M (2*β - 1)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2*β - 1) (Set.mem_univ _))
      (analyticOnNhd_affine_2β_sub_1 β (Set.mem_univ _))
  have h_const : AnalyticOnNhd ℝ (fun _ : ℝ => gaussMellin ρ) Set.univ :=
    analyticOnNhd_const
  -- The full RHS:
  --   (1/2)·M(2β−π/3) + (1/2)·M(2−π/3−2β) − M(1−π/3) − M(2β−1) + gaussMellin
  set g : ℝ → ℂ := fun β =>
    (1/2 : ℂ) * M (2*β - Real.pi/3) +
    (1/2 : ℂ) * M (2 - Real.pi/3 - 2*β) -
    M (1 - Real.pi/3) -
    M (2*β - 1) +
    gaussMellin ρ with hg_def
  have hg : AnalyticOnNhd ℝ g Set.univ := by
    refine (((((analyticOnNhd_const.mul h_M1).add (analyticOnNhd_const.mul h_M2)).sub
      h_M3).sub h_M4).add h_const)
  -- Show pairTestMellin β ρ = g β for every β.
  have h_pt_eq : (fun β : ℝ => pairTestMellin β ρ) = g := by
    funext β
    have h_re_pos : 0 < ρ.re := hρ
    have h_exp : pairTestMellin β ρ =
        (1/2 : ℂ) * coshGaussMellin (2*β - Real.pi/3) ρ +
        (1/2 : ℂ) * coshGaussMellin (2 - Real.pi/3 - 2*β) ρ -
        coshGaussMellin (1 - Real.pi/3) ρ -
        coshGaussMellin (2*β - 1) ρ +
        gaussMellin ρ := by
      refine pairTestMellin_cosh_expansion β ρ
        (mellinConvergent_coshGauss _ h_re_pos)
        (mellinConvergent_coshGauss _ h_re_pos)
        (mellinConvergent_coshGauss _ h_re_pos)
        (mellinConvergent_coshGauss _ h_re_pos) ?_
      have := mellinConvergent_coshGauss 0 h_re_pos
      have h_eq : (fun t : ℝ =>
          ((Real.cosh (0 * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =
          (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
        funext t; simp [Real.cosh_zero]
      rw [h_eq] at this
      exact this
    exact h_exp
  rw [h_pt_eq]
  exact hg

#print axioms pairTestMellin_analyticOnNhd_in_beta

end Contour
end WeilPositivity
end ZD

end
