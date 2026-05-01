import Mathlib
import RequestProject.ThetaTransport
import RequestProject.EnergyDefect

/-!
# γ-Averaged Parseval identity and unconditional offline positivity

## Main result

For `σ ∈ ℝ`, let `α := σ - 1/2`. The observable
`I_theta(σ+iγ) = ∫₀^∞ 2·cosh((α+iγ)t)·ψ(t) dt` decomposes into
real/imaginary cosine and sine transforms. Applying the half-line Parseval
identities (`EnergyDefect.halfLine_cosine_parseval` and
`EnergyDefect.halfLine_sine_parseval`) and summing gives the γ-averaged
identity
```
∫_{γ>0} ‖I_theta(σ+iγ)‖² dγ = 2π · ∫_{t>0} cosh(2αt) · ψ(t)² dt
```
and the algebraic expansion `cosh(2αt) = E² + O² + (2·cosh(αt) - 1)` with
`2·cosh(αt) - 1 ≥ 1` yields the **unconditional lower bound**
```
∫_{γ>0} ‖I_theta(σ+iγ)‖² dγ ≥ 2π·∫(E² + O²)·ψ² + 2π·∫ψ²
```
For offline `σ ≠ 1/2` (and nontrivial ψ), the RHS is strictly
positive — offline positivity without any pointwise Cauchy-Schwarz lower
bound.

## Caveat for RH closure

This gives γ-AVERAGED positivity, not pointwise. Converting this to a
contradiction at individual offline zeros requires additional analytic
structure (zero density, pair correlation, or Weil explicit formula
positivity) — the γ-averaged result alone is consistent with the
existence of isolated offline zeros (measure-zero set has no γ-integral
contribution).

## Structure

* `kernel_real_imag_decomp` — kernel algebraic split into cos/sin parts
* `gamma_averaged_normSq_eq` — main Parseval identity
* `gamma_averaged_ge_envelope_plus_L2` — unconditional lower bound
* `gamma_averaged_offline_positive` — offline positivity
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZD

/-! ### Step 1: Kernel real/imaginary decomposition

For real `σ, γ, t`:
`2·Complex.cosh((σ-1/2+iγ)·t) = 2·cosh((σ-1/2)t)·cos(γt) + i·2·sinh((σ-1/2)t)·sin(γt)`
-/

/-- The complex cosh kernel decomposes into real cosine and sine transforms. -/
theorem cosh_kernel_decomp (σ γ t : ℝ) :
    (2 : ℂ) * Complex.cosh (((σ - 1/2 : ℝ) : ℂ) * (t : ℂ) + ((γ : ℝ) : ℂ) * Complex.I * (t : ℂ)) =
      ((2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) : ℝ) : ℂ) +
      ((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) : ℝ) : ℂ) * Complex.I := by
  have h1 : ((σ - 1/2 : ℝ) : ℂ) * (t : ℂ) + ((γ : ℝ) : ℂ) * Complex.I * (t : ℂ) =
        (((σ - 1/2) * t : ℝ) : ℂ) + (((γ * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

/-! ### Step 2: Real/imaginary integral decomposition of I_theta

`I_theta(σ+iγ) = (∫ 2·cosh(αt)·cos(γt)·ψ) + i·(∫ 2·sinh(αt)·sin(γt)·ψ)`
-/

/-- Real part of the observable as a cosine transform. -/
theorem I_theta_ofReal_im_decomp (ψ : ℝ → ℝ) (σ γ : ℝ)
    (hInt_c : Integrable
        (fun t => 2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) * ψ t)
        (volume.restrict (Set.Ioi 0)))
    (hInt_s : Integrable
        (fun t => 2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t)
        (volume.restrict (Set.Ioi 0))) :
    I_theta_of ψ ((σ : ℂ) + (γ : ℂ) * Complex.I) =
      ((∫ t in Set.Ioi (0:ℝ),
          2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) * ψ t : ℝ) : ℂ) +
      ((∫ t in Set.Ioi (0:ℝ),
          2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ) : ℂ) * Complex.I := by
  unfold I_theta_of
  -- Rewrite integrand using cosh_kernel_decomp
  have h_eq : ∀ t : ℝ,
      (2 : ℂ) * Complex.cosh ((((σ : ℂ) + (γ : ℂ) * Complex.I) - (1/2 : ℂ)) * (t : ℂ)) *
        ((ψ t : ℝ) : ℂ) =
      (((2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) * ψ t : ℝ)) : ℂ) +
      (((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ)) : ℂ) *
        Complex.I := by
    intro t
    have h_arg :
        (((σ : ℂ) + (γ : ℂ) * Complex.I) - (1/2 : ℂ)) * (t : ℂ) =
        ((σ - 1/2 : ℝ) : ℂ) * (t : ℂ) + ((γ : ℝ) : ℂ) * Complex.I * (t : ℂ) := by
      push_cast; ring
    rw [h_arg, cosh_kernel_decomp]
    push_cast
    ring
  simp_rw [h_eq]
  have h_sum_int :
      ∫ t in Set.Ioi (0:ℝ),
        (((2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) * ψ t : ℝ) : ℂ) +
          ((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ) : ℂ) *
            Complex.I) =
      (∫ t in Set.Ioi (0:ℝ),
        ((2 * Real.cosh ((σ - 1/2) * t) * Real.cos (γ * t) * ψ t : ℝ) : ℂ)) +
      (∫ t in Set.Ioi (0:ℝ),
        ((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ) : ℂ) *
          Complex.I) :=
    MeasureTheory.integral_add hInt_c.ofReal (hInt_s.ofReal.mul_const _)
  rw [h_sum_int]
  rw [show (∫ t in Set.Ioi (0:ℝ),
        ((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ) : ℂ) * Complex.I)
        = (∫ t in Set.Ioi (0:ℝ),
          ((2 * Real.sinh ((σ - 1/2) * t) * Real.sin (γ * t) * ψ t : ℝ) : ℂ)) * Complex.I
        from MeasureTheory.integral_mul_const Complex.I _,
      integral_complex_ofReal, integral_complex_ofReal]

/-! ### Step 3: Parseval for each half

Apply `EnergyDefect.halfLine_cosine_parseval` to `f(t) := 2·cosh(αt)·ψ(t)`
and `EnergyDefect.halfLine_sine_parseval` to `f(t) := 2·sinh(αt)·ψ(t)`.
-/

/-- Parseval for the cosine-transform half. -/
theorem cosine_parseval_cosh_weighted (ψ : ℝ → ℝ) (σ : ℝ)
    (hf_meas : Measurable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t))
    (hf_int : Integrable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_L2 : Integrable (fun t => (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0))) :
    ∫ γ in Set.Ioi (0:ℝ),
        (∫ t in Set.Ioi (0:ℝ),
          2 * Real.cosh ((σ - 1/2) * t) * ψ t * Real.cos (γ * t))^2 =
      (Real.pi / 2) *
        ∫ t in Set.Ioi (0:ℝ), (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2 := by
  exact (halfLine_cosine_parseval _ hf_meas hf_int hf_L2).2

/-- Parseval for the sine-transform half. -/
theorem sine_parseval_sinh_weighted (ψ : ℝ → ℝ) (σ : ℝ)
    (hf_meas : Measurable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t))
    (hf_int : Integrable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_L2 : Integrable (fun t => (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0))) :
    ∫ γ in Set.Ioi (0:ℝ),
        (∫ t in Set.Ioi (0:ℝ),
          2 * Real.sinh ((σ - 1/2) * t) * ψ t * Real.sin (γ * t))^2 =
      (Real.pi / 2) *
        ∫ t in Set.Ioi (0:ℝ), (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2 := by
  exact (halfLine_sine_parseval _ hf_meas hf_int hf_L2).2

/-! ### Step 4: Sum identity

Sum the two Parseval identities and apply `cosh² + sinh² = cosh(2·)`.
-/

private lemma cosh_sq_add_sinh_sq (x : ℝ) :
    Real.cosh x ^ 2 + Real.sinh x ^ 2 = Real.cosh (2 * x) := by
  rw [Real.cosh_two_mul]

/-- The γ-integral of `‖I_theta(σ+iγ)‖²` over `Ioi 0` equals a real-valued expression.

Hypotheses abstract out integrability needed for Parseval + integral linearity. -/
theorem gamma_averaged_normSq_eq (ψ : ℝ → ℝ) (σ : ℝ)
    (hf_c_meas : Measurable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t))
    (hf_c_int : Integrable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_c_L2 : Integrable (fun t => (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_meas : Measurable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t))
    (hf_s_int : Integrable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_L2 : Integrable (fun t => (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hInt_cosh2 : Integrable (fun t => Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2)
      (volume.restrict (Set.Ioi 0))) :
    ∫ γ in Set.Ioi (0:ℝ),
        ((∫ t in Set.Ioi (0:ℝ),
            2 * Real.cosh ((σ - 1/2) * t) * ψ t * Real.cos (γ * t))^2 +
          (∫ t in Set.Ioi (0:ℝ),
            2 * Real.sinh ((σ - 1/2) * t) * ψ t * Real.sin (γ * t))^2) =
      2 * Real.pi *
        ∫ t in Set.Ioi (0:ℝ), Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2 := by
  rw [MeasureTheory.integral_add]
  · rw [cosine_parseval_cosh_weighted ψ σ hf_c_meas hf_c_int hf_c_L2,
        sine_parseval_sinh_weighted ψ σ hf_s_meas hf_s_int hf_s_L2]
    rw [show (Real.pi / 2) *
          (∫ t in Set.Ioi (0:ℝ), (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2) +
        (Real.pi / 2) *
          (∫ t in Set.Ioi (0:ℝ), (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2) =
        (Real.pi / 2) *
          ((∫ t in Set.Ioi (0:ℝ), (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2) +
          (∫ t in Set.Ioi (0:ℝ), (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2)) from by
        ring]
    rw [← MeasureTheory.integral_add hf_c_L2 hf_s_L2]
    have h_integrand_eq :
        ∀ t ∈ Set.Ioi (0:ℝ),
          (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2 +
            (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2 =
          4 * (Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2) := by
      intro t _
      have h := cosh_sq_add_sinh_sq ((σ - 1/2) * t)
      rw [show (2 : ℝ) * (σ - 1/2) * t = 2 * ((σ - 1/2) * t) from by ring]
      nlinarith [h]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_integrand_eq]
    rw [MeasureTheory.integral_const_mul]
    ring
  · -- Integrability of cosine-transform squared (needed by integral_add)
    exact (halfLine_cosine_parseval _ hf_c_meas hf_c_int hf_c_L2).1
  · -- Integrability of sine-transform squared
    exact (halfLine_sine_parseval _ hf_s_meas hf_s_int hf_s_L2).1

/-! ### Step 5: Envelope algebraic identity

`cosh(2αt) = (cosh(αt) - 1)² + sinh²(αt) + (2·cosh(αt) - 1)`

with `2·cosh(αt) - 1 ≥ 1`.

`amplitudeDefectEnvelope σ t = cosh((σ-1/2)t) - 1`
`oddDefectEnvelope σ t = sinh((σ-1/2)t)`
-/

/-- Algebraic expansion of `cosh(2αt)` in terms of envelope squares plus a positive remainder. -/
theorem cosh_two_eq_envelope_plus_positive (σ t : ℝ) :
    Real.cosh (2 * (σ - 1/2) * t) =
      (amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2 +
      (2 * Real.cosh ((σ - 1/2) * t) - 1) := by
  unfold amplitudeDefectEnvelope oddDefectEnvelope
  have h := Real.cosh_two_mul ((σ - 1/2) * t)
  have hss := Real.cosh_sq_sub_sinh_sq ((σ - 1/2) * t)
  rw [show (2 : ℝ) * (σ - 1/2) * t = 2 * ((σ - 1/2) * t) from by ring, h]
  nlinarith [hss]

/-- The positive remainder `2·cosh(αt) - 1 ≥ 1`. -/
theorem two_cosh_sub_one_ge_one (x : ℝ) : 1 ≤ 2 * Real.cosh x - 1 := by
  have := Real.one_le_cosh x
  linarith

/-! ### Step 6: Unconditional γ-averaged lower bound -/

/-- γ-averaged lower bound: the integral over `γ > 0` of `‖I_theta(σ+iγ)‖²` is bounded
below by the envelope integral plus a positive `ψ²` mass term. -/
theorem gamma_averaged_ge_envelope_plus_L2 (ψ : ℝ → ℝ) (σ : ℝ)
    (hf_c_meas : Measurable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t))
    (hf_c_int : Integrable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_c_L2 : Integrable (fun t => (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_meas : Measurable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t))
    (hf_s_int : Integrable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_L2 : Integrable (fun t => (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hInt_cosh2 : Integrable (fun t => Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2)
      (volume.restrict (Set.Ioi 0)))
    (hInt_env : Integrable
      (fun t => ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) *
        ψ t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hInt_psi2 : Integrable (fun t => ψ t ^ 2) (volume.restrict (Set.Ioi 0))) :
    ∫ γ in Set.Ioi (0:ℝ),
        ((∫ t in Set.Ioi (0:ℝ),
            2 * Real.cosh ((σ - 1/2) * t) * ψ t * Real.cos (γ * t))^2 +
          (∫ t in Set.Ioi (0:ℝ),
            2 * Real.sinh ((σ - 1/2) * t) * ψ t * Real.sin (γ * t))^2) ≥
      (2 * Real.pi * ∫ t in Set.Ioi (0:ℝ),
        ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) * ψ t ^ 2) +
      (2 * Real.pi * ∫ t in Set.Ioi (0:ℝ), ψ t ^ 2) := by
  rw [gamma_averaged_normSq_eq ψ σ hf_c_meas hf_c_int hf_c_L2
    hf_s_meas hf_s_int hf_s_L2 hInt_cosh2]
  -- Bound the integrand of the RHS using cosh_two_eq_envelope_plus_positive
  have h_ptwise : ∀ t : ℝ,
      Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2 ≥
      ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) * ψ t ^ 2 +
      ψ t ^ 2 := by
    intro t
    have h_expand := cosh_two_eq_envelope_plus_positive σ t
    have h_positive := two_cosh_sub_one_ge_one ((σ - 1/2) * t)
    have h_psi2_nn : 0 ≤ ψ t ^ 2 := sq_nonneg _
    rw [h_expand]
    nlinarith [h_positive, h_psi2_nn]
  -- Integrate the pointwise inequality
  have h_int_bound :
      (∫ t in Set.Ioi (0:ℝ), Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2) ≥
      (∫ t in Set.Ioi (0:ℝ),
        ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) * ψ t ^ 2) +
      (∫ t in Set.Ioi (0:ℝ), ψ t ^ 2) := by
    rw [← MeasureTheory.integral_add hInt_env hInt_psi2]
    apply MeasureTheory.setIntegral_mono_on
    · exact hInt_env.add hInt_psi2
    · exact hInt_cosh2
    · exact measurableSet_Ioi
    · intro t _
      exact h_ptwise t
  have h_pi_pos : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos; linarith
  have h_mul := mul_le_mul_of_nonneg_left h_int_bound h_pi_pos.le
  rw [mul_add] at h_mul
  exact ge_iff_le.mpr h_mul

/-! ### Step 7: Unconditional offline positivity -/

/-- **γ-averaged unconditional offline positivity.**

For `σ ≠ 1/2` with nontrivial `ψ ∈ L²`, the γ-integral of `‖I_theta(σ+iγ)‖²`
over `γ > 0` is strictly positive — provably, without any Cauchy-Schwarz reversal
or pointwise inequality. -/
theorem gamma_averaged_offline_positive (ψ : ℝ → ℝ) (σ : ℝ) (hσ : σ ≠ 1/2)
    (hf_c_meas : Measurable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t))
    (hf_c_int : Integrable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_c_L2 : Integrable (fun t => (2 * Real.cosh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_meas : Measurable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t))
    (hf_s_int : Integrable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ t)
      (volume.restrict (Set.Ioi 0)))
    (hf_s_L2 : Integrable (fun t => (2 * Real.sinh ((σ - 1/2) * t) * ψ t)^2)
      (volume.restrict (Set.Ioi 0)))
    (hInt_cosh2 : Integrable (fun t => Real.cosh (2 * (σ - 1/2) * t) * ψ t ^ 2)
      (volume.restrict (Set.Ioi 0)))
    (hInt_env : Integrable
      (fun t => ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) *
        ψ t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hInt_psi2 : Integrable (fun t => ψ t ^ 2) (volume.restrict (Set.Ioi 0)))
    (hψ_L2_pos : 0 < ∫ t in Set.Ioi (0:ℝ), ψ t ^ 2) :
    0 < ∫ γ in Set.Ioi (0:ℝ),
        ((∫ t in Set.Ioi (0:ℝ),
            2 * Real.cosh ((σ - 1/2) * t) * ψ t * Real.cos (γ * t))^2 +
          (∫ t in Set.Ioi (0:ℝ),
            2 * Real.sinh ((σ - 1/2) * t) * ψ t * Real.sin (γ * t))^2) := by
  have h_lower := gamma_averaged_ge_envelope_plus_L2 ψ σ hf_c_meas hf_c_int hf_c_L2
    hf_s_meas hf_s_int hf_s_L2 hInt_cosh2 hInt_env hInt_psi2
  have h_env_nn : 0 ≤ 2 * Real.pi *
      ∫ t in Set.Ioi (0:ℝ),
        ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) * ψ t ^ 2 := by
    apply mul_nonneg (by positivity)
    apply MeasureTheory.integral_nonneg
    intro t
    exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have h_psi2_pos : 0 < 2 * Real.pi * ∫ t in Set.Ioi (0:ℝ), ψ t ^ 2 :=
    mul_pos (by have := Real.pi_pos; linarith) hψ_L2_pos
  linarith

/-! ### Axiom hygiene -/

#print axioms gamma_averaged_normSq_eq
#print axioms gamma_averaged_ge_envelope_plus_L2
#print axioms gamma_averaged_offline_positive

end ZD

end
