import Mathlib
import RequestProject.ThetaTransport
import RequestProject.GaussianAdmissible
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.EnergyDefect

/-!
# Gaussian Closed Forms for the Theta Observable

**W1 deliverable**: The Gaussian test function `ψ_gaussian(t) = exp(-t²)`
produces a closed-form `I_theta_of`:

```
I_theta_of ψ_gaussian s = √π · exp((s - 1/2)² / 4)
```

This is an unconditional equality (no axiom, no biconditional).

## Structure

* `cosh_gaussian_integral_Ioi` — the core Gaussian-moment identity
  `∫_{Ioi 0} 2·cosh(a·t)·exp(-t²) dt = π^(1/2) · exp(a²/4)` for `a ∈ ℂ`.
* `I_theta_of_gaussian_closed_form` — the W1 target.
* Subsequent deliverables (W2, W3) build on W1 using the `γ`-integration of
  `|I_theta_of ψ_gaussian (β + iγ) - I_theta_of ψ_gaussian (1/2 + iγ)|²`.

## Provenance

The Gaussian moment `∫_ℝ exp(-t² + a·t) dt = √π · exp(a²/4)` (complex `a`)
is Mathlib's `integral_cexp_quadratic`. The half-line reduction uses the
even-split identity `∫_{Ioi 0} (f(t) + f(-t)) dt = ∫_ℝ f(t) dt`.
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helper lemmas
-- ═══════════════════════════════════════════════════════════════════════════

private lemma cexp_quadratic_integrable (a : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-(t : ℂ)^2 + a * (t : ℂ))) := by
  have h := integrable_cexp_quadratic (b := (1 : ℂ))
    (by norm_num : 0 < ((1:ℂ)).re) a 0
  have key : (fun (x : ℝ) => Complex.exp (-(1:ℂ) * (x : ℂ)^2 + a * (x : ℂ) + 0)) =
             (fun (x : ℝ) => Complex.exp (-(x : ℂ)^2 + a * (x : ℂ))) := by
    funext x; congr 1; ring
  rwa [key] at h

private lemma cexp_quadratic_integral (a : ℂ) :
    ∫ t : ℝ, Complex.exp (-(t : ℂ)^2 + a * (t : ℂ)) =
    (Real.pi : ℂ)^((1:ℂ)/2) * Complex.exp (a^2 / 4) := by
  have h := integral_cexp_quadratic (b := -1)
    (by norm_num : (-1 : ℂ).re < 0) a 0
  have key : (fun (x : ℝ) => Complex.exp (-1 * (x : ℂ)^2 + a * (x : ℂ) + 0)) =
             (fun (x : ℝ) => Complex.exp (-(x : ℂ)^2 + a * (x : ℂ))) := by
    funext x; congr 1; ring
  rw [key] at h
  rw [h]
  congr 1
  · rw [show (-(-1 : ℂ)) = 1 from by ring, div_one]
  · congr 1; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § The core Gaussian-moment identity on `Ioi 0`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Gaussian moment on `Ioi 0`**. For every `a : ℂ`:

  `∫_{t ∈ Ioi 0} 2·cosh(a·t)·exp(-t²) dt = π^(1/2) · exp(a²/4)`.

Derived from the full-line quadratic Gaussian integral by the even-split
identity `∫_{Ioi 0} (f(t) + f(-t)) dt = ∫_ℝ f(t) dt`. No axiom, no
biconditional. -/
theorem cosh_gaussian_integral_Ioi (a : ℂ) :
    ∫ t in Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-(t : ℂ)^2) =
    (Real.pi : ℂ)^((1:ℂ)/2) * Complex.exp (a^2 / 4) := by
  let f : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ)^2 + a * (t : ℂ))
  have hintegrand_eq : ∀ t ∈ Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-(t : ℂ)^2) =
      f t + f (-t) := by
    intro t _
    show _ = Complex.exp (-((t : ℂ))^2 + a * ((t : ℂ))) +
             Complex.exp (-(((-t : ℝ) : ℂ))^2 + a * ((-t : ℝ) : ℂ))
    rw [Complex.exp_add, Complex.exp_add]
    push_cast
    have h2cosh := Complex.two_cosh (a * (t : ℂ))
    have hsq : (-(t : ℂ))^2 = (t : ℂ)^2 := by ring
    rw [hsq]
    have hneg : a * (-(t : ℂ)) = -(a * (t : ℂ)) := by ring
    rw [hneg]
    linear_combination (Complex.exp (-(t : ℂ)^2)) * h2cosh
  rw [setIntegral_congr_fun measurableSet_Ioi hintegrand_eq]
  have hf_integrable : Integrable f := cexp_quadratic_integrable a
  have hf_ioi : IntegrableOn f (Ioi 0) := hf_integrable.integrableOn
  have hf_iic : IntegrableOn f (Iic 0) := hf_integrable.integrableOn
  have hf_neg_ioi : IntegrableOn (fun t : ℝ => f (-t)) (Ioi 0) := by
    have : IntegrableOn f (Iio (-(0:ℝ))) := by
      simpa using hf_integrable.integrableOn
    exact MeasureTheory.IntegrableOn.comp_neg_Ioi this
  rw [integral_add hf_ioi hf_neg_ioi, integral_comp_neg_Ioi 0 f]
  simp only [neg_zero]
  rw [add_comm]
  rw [intervalIntegral.integral_Iic_add_Ioi hf_iic hf_ioi]
  exact cexp_quadratic_integral a

-- ═══════════════════════════════════════════════════════════════════════════
-- § W1 — closed form of `I_theta_of ψ_gaussian`
-- ═══════════════════════════════════════════════════════════════════════════

private lemma pi_half_eq_sqrt_pi :
    (Real.pi : ℂ)^((1:ℂ)/2) = ((Real.sqrt Real.pi) : ℂ) := by
  rw [show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
  rw [← Complex.ofReal_cpow Real.pi_pos.le]
  rw [Real.sqrt_eq_rpow]

private lemma psi_gaussian_ofReal_eq (t : ℝ) :
    (ψ_gaussian t : ℂ) = Complex.exp (-(t : ℂ)^2) := by
  unfold ψ_gaussian
  push_cast
  ring_nf

/-- **W1**: closed form of the theta observable at the Gaussian test function.

For every `s : ℂ`:

  `I_theta_of ψ_gaussian s = √π · exp((s - 1/2)² / 4)`.

Unconditional. No axiom, no biconditional. -/
theorem I_theta_of_gaussian_closed_form (s : ℂ) :
    I_theta_of ψ_gaussian s =
      (Real.sqrt Real.pi : ℂ) * Complex.exp ((s - 1/2)^2 / 4) := by
  unfold I_theta_of
  have hinteg : ∀ t ∈ Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) *
        (ψ_gaussian t : ℂ) =
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) *
        Complex.exp (-(t : ℂ)^2) := by
    intro t _
    rw [psi_gaussian_ofReal_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi hinteg]
  rw [cosh_gaussian_integral_Ioi (s - 1/2)]
  rw [pi_half_eq_sqrt_pi]

-- ═══════════════════════════════════════════════════════════════════════════
-- § W2 — closed form of `averageEnergyDefect ψ_gaussian`
-- ═══════════════════════════════════════════════════════════════════════════

/-- Complex `b = 2` Gaussian moment. -/
private lemma cexp_quadratic_two_integrable_complex (a : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ))) := by
  have h := integrable_cexp_quadratic (b := (2 : ℂ))
    (by norm_num : 0 < ((2:ℂ)).re) a 0
  have key : (fun (x : ℝ) => Complex.exp (-(2:ℂ) * (x : ℂ)^2 + a * (x : ℂ) + 0)) =
             (fun (x : ℝ) => Complex.exp (-2 * (x : ℂ)^2 + a * (x : ℂ))) := by
    funext x; congr 1; ring
  rwa [key] at h

/-- **Complex `b = 2` cosh Gaussian integral on `Ioi 0`.** -/
private theorem cosh_gaussian_integral_Ioi_two_C (a : ℂ) :
    ∫ t in Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
    (Real.pi / 2 : ℂ)^((1:ℂ)/2) * Complex.exp (a^2 / 8) := by
  let f : ℝ → ℂ := fun t => Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ))
  have hintegrand_eq : ∀ t ∈ Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      f t + f (-t) := by
    intro t _
    show _ = Complex.exp (-2 * ((t : ℂ))^2 + a * ((t : ℂ))) +
             Complex.exp (-2 * (((-t : ℝ) : ℂ))^2 + a * ((-t : ℝ) : ℂ))
    rw [Complex.exp_add, Complex.exp_add]
    push_cast
    have h2cosh := Complex.two_cosh (a * (t : ℂ))
    have hsq : (-(t : ℂ))^2 = (t : ℂ)^2 := by ring
    rw [hsq]
    have hneg : a * (-(t : ℂ)) = -(a * (t : ℂ)) := by ring
    rw [hneg]
    linear_combination (Complex.exp (-2 * (t : ℂ)^2)) * h2cosh
  rw [setIntegral_congr_fun measurableSet_Ioi hintegrand_eq]
  have hf_integrable : Integrable f := cexp_quadratic_two_integrable_complex a
  have hf_ioi : IntegrableOn f (Ioi 0) := hf_integrable.integrableOn
  have hf_iic : IntegrableOn f (Iic 0) := hf_integrable.integrableOn
  have hf_neg_ioi : IntegrableOn (fun t : ℝ => f (-t)) (Ioi 0) := by
    have : IntegrableOn f (Iio (-(0:ℝ))) := by
      simpa using hf_integrable.integrableOn
    exact MeasureTheory.IntegrableOn.comp_neg_Ioi this
  rw [integral_add hf_ioi hf_neg_ioi, integral_comp_neg_Ioi 0 f]
  simp only [neg_zero]
  rw [add_comm]
  rw [intervalIntegral.integral_Iic_add_Ioi hf_iic hf_ioi]
  have h := integral_cexp_quadratic (b := -2)
    (by norm_num : (-2 : ℂ).re < 0) a 0
  have key : (fun (x : ℝ) => Complex.exp (-2 * (x : ℂ)^2 + a * (x : ℂ) + 0)) =
             (fun (x : ℝ) => Complex.exp (-2 * (x : ℂ)^2 + a * (x : ℂ))) := by
    funext x; congr 1; ring
  rw [key] at h
  rw [h]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-- **Real `b = 2` cosh Gaussian integral on `Ioi 0`.** -/
theorem cosh_gaussian_half (a : ℝ) :
    ∫ t in Ioi (0:ℝ), Real.cosh (a * t) * Real.exp (-2 * t^2) =
    (1/2) * Real.sqrt (Real.pi / 2) * Real.exp (a^2 / 8) := by
  have h_eq : ((∫ t in Ioi (0:ℝ), 2 * Real.cosh (a * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) =
    ((Real.sqrt (Real.pi / 2) * Real.exp (a^2 / 8) : ℝ) : ℂ) := by
    rw [show ((∫ t in Ioi (0:ℝ), 2 * Real.cosh (a * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) =
          ∫ t in Ioi (0:ℝ), ((2 * Real.cosh (a * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) from
      (integral_ofReal).symm]
    have hintegrand : ∀ t ∈ Ioi (0:ℝ),
        ((2 * Real.cosh (a * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) =
        (2 : ℂ) * Complex.cosh ((a : ℂ) * (t : ℂ)) *
          Complex.exp (-2 * (t : ℂ)^2) := by
      intro t _; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hintegrand]
    rw [cosh_gaussian_integral_Ioi_two_C (a : ℂ)]
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [← Real.sqrt_eq_rpow]
    rw [show ((a:ℂ)^2/8) = ((a^2/8 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_exp]
    push_cast; rfl
  have h_r : ∫ t in Ioi (0:ℝ), 2 * Real.cosh (a * t) * Real.exp (-2 * t^2) =
      Real.sqrt (Real.pi / 2) * Real.exp (a^2 / 8) := by
    exact_mod_cast h_eq
  have hrw : (fun t => 2 * Real.cosh (a * t) * Real.exp (-2 * t^2)) =
      (fun t => 2 * (Real.cosh (a * t) * Real.exp (-2 * t^2))) := by
    funext t; ring
  rw [hrw] at h_r
  rw [MeasureTheory.integral_const_mul] at h_r
  linarith

/-- Integrability of `cosh(at)·exp(-2t²)` over `ℝ`. -/
lemma cosh_exp_neg_two_sq_integrable (a : ℝ) :
    Integrable (fun t : ℝ => Real.cosh (a * t) * Real.exp (-2 * t^2)) := by
  apply MeasureTheory.Integrable.mono'
    (g := fun t => Real.exp (a^2/2) * Real.exp (-(3/2) * t^2))
  · exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 3/2)).const_mul _
  · apply Continuous.aestronglyMeasurable
    exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul (continuous_id.pow 2)).rexp)
  · filter_upwards with t
    have hcosh_nn : 0 ≤ Real.cosh (a * t) := le_of_lt (Real.cosh_pos _)
    have hexp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg hcosh_nn hexp_nn)]
    have hcosh_le : Real.cosh (a * t) ≤ Real.exp |a * t| := by
      rw [Real.cosh_eq]
      rcases le_total 0 (a * t) with h | h
      · rw [abs_of_nonneg h]
        have : Real.exp (-(a * t)) ≤ Real.exp (a * t) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith
      · rw [abs_of_nonpos h]
        have : Real.exp (a * t) ≤ Real.exp (-(a * t)) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith
    have hAMGM : |a * t| ≤ a^2/2 + t^2/2 := by
      have h := sq_nonneg (|a| - |t|)
      have ha : |a|^2 = a^2 := sq_abs a
      have ht : |t|^2 = t^2 := sq_abs t
      have hat : |a * t| = |a| * |t| := abs_mul _ _
      nlinarith
    calc Real.cosh (a * t) * Real.exp (-2 * t^2)
        ≤ Real.exp |a * t| * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right hcosh_le hexp_nn
      _ ≤ Real.exp (a^2/2) * Real.exp (-(3/2) * t^2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr; linarith

/-- Envelope algebraic identity: `(cosh(δt)-1)² + sinh(δt)² = cosh(2δt) -
2·cosh(δt) + 1`. -/
private lemma envelope_expand (δ t : ℝ) :
    (Real.cosh (δ * t) - 1)^2 + Real.sinh (δ * t)^2 =
    Real.cosh (2 * δ * t) - 2 * Real.cosh (δ * t) + 1 := by
  have h1 : Real.cosh (2 * δ * t) = Real.cosh (δ * t)^2 + Real.sinh (δ * t)^2 := by
    rw [show (2 * δ * t) = 2 * (δ * t) from by ring]
    exact Real.cosh_two_mul _
  linarith [h1]

/-- Envelope integral for the Gaussian test function. -/
private lemma envelope_integral_gaussian (β : ℝ) :
    ∫ t in Ioi (0:ℝ),
      ((amplitudeDefectEnvelope β t)^2 + (oddDefectEnvelope β t)^2) *
        (ψ_gaussian t)^2 =
    (1/2) * Real.sqrt (Real.pi / 2) *
      (Real.exp ((β - 1/2)^2 / 2) - 2 * Real.exp ((β - 1/2)^2 / 8) + 1) := by
  set δ := β - 1/2 with hδ_def
  have h_psi_sq : ∀ t, (ψ_gaussian t)^2 = Real.exp (-2 * t^2) := ψ_gaussian_sq_eq
  have h_integrand : ∀ t,
      ((amplitudeDefectEnvelope β t)^2 + (oddDefectEnvelope β t)^2) *
        (ψ_gaussian t)^2 =
      Real.cosh (2 * δ * t) * Real.exp (-2 * t^2)
      - 2 * (Real.cosh (δ * t) * Real.exp (-2 * t^2))
      + Real.exp (-2 * t^2) := by
    intro t
    unfold amplitudeDefectEnvelope oddDefectEnvelope
    rw [h_psi_sq t]
    rw [envelope_expand δ t]
    ring
  simp_rw [h_integrand]
  have hf1 : Integrable (fun t : ℝ =>
      Real.cosh (2 * δ * t) * Real.exp (-2 * t^2)) :=
    cosh_exp_neg_two_sq_integrable (2 * δ)
  have hf2 : Integrable (fun t : ℝ =>
      2 * (Real.cosh (δ * t) * Real.exp (-2 * t^2))) :=
    (cosh_exp_neg_two_sq_integrable δ).const_mul 2
  have hf3 : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2)
  have hAB : IntegrableOn (fun t =>
      Real.cosh (2 * δ * t) * Real.exp (-2 * t^2)
      - 2 * (Real.cosh (δ * t) * Real.exp (-2 * t^2))) (Ioi 0) :=
    hf1.integrableOn.sub hf2.integrableOn
  rw [integral_add hAB hf3.integrableOn]
  rw [integral_sub hf1.integrableOn hf2.integrableOn]
  rw [integral_const_mul]
  rw [cosh_gaussian_half (2 * δ), cosh_gaussian_half δ, integral_gaussian_Ioi 2]
  have h_exp_2delta : (2 * δ)^2 / 8 = δ^2 / 2 := by ring
  rw [h_exp_2delta]
  ring

/-- **W2**: closed-form `averageEnergyDefect` for the Gaussian kernel.

For every real `β`:

  `averageEnergyDefect ψ_gaussian β = π · √(π/2) · (exp(δ²/2) − 2·exp(δ²/8) + 1)`

with `δ = β − 1/2`. Pure equality. No axiom, no biconditional. -/
theorem averageEnergyDefect_gaussian_closed_form (β : ℝ) :
    averageEnergyDefect ψ_gaussian β =
      Real.pi * Real.sqrt (Real.pi / 2) *
      (Real.exp ((β - 1/2)^2 / 2) -
        2 * Real.exp ((β - 1/2)^2 / 8) + 1) := by
  rw [hparseval_gaussian β, envelope_integral_gaussian β]
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § W3 — forward implication
-- ═══════════════════════════════════════════════════════════════════════════

/-- **W3**: forward implication (no biconditional).

If the averaged energy defect vanishes at `β` for the Gaussian kernel, then
`β = 1/2`. Pure forward direction; discharged via the unconditional
`averageEnergyDefect_pos_offline` (from `EnergyDefect.lean`) plumbed through
`ψ_gaussian_admissible`. -/
theorem re_half_of_averageEnergyDefect_gaussian_zero (β : ℝ)
    (h : averageEnergyDefect ψ_gaussian β = 0) : β = 1/2 := by
  by_contra hne
  have hpos : 0 < averageEnergyDefect ψ_gaussian β :=
    gaussianKernel_averageEnergyDefect_pos_offline β hne
  linarith

end ZD

end
