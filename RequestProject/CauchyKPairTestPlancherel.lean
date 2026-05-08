import Mathlib
import RequestProject.OfflineDetectorProof

/-!
# Plancherel form of `gaussianDefectEntireKernel_local` at complex `s`

For every `s : ℂ`,

```
gaussianDefectEntireKernel_local s
  = 2π · ∫_{(0,∞)} (Complex.cosh (2 (s - 1/2) t) − 2 · Complex.cosh ((s - 1/2) t) + 1)
                 · Complex.exp (-2 t²) dt
```

Direct algebraic identity via Mathlib's `integral_cexp_quadratic` for complex `a`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity

/-- The cosh-pair kernel `K₂(s, t) = cosh(2(s−1/2)t) − 2·cosh((s−1/2)t) + 1`,
extended to `s : ℂ` and `t : ℝ`. -/
noncomputable def K_2 (s : ℂ) (t : ℝ) : ℂ :=
  Complex.cosh (2 * (s - 1/2) * (t : ℂ)) -
    2 * Complex.cosh ((s - 1/2) * (t : ℂ)) + 1

/-- Full-line cosh-Gaussian moment: for any complex `a`,
`∫_ℝ 2 cosh(a·t) exp(-2t²) dt = 2·√(π/2) · exp(a²/8)`. -/
private lemma two_cosh_gauss_integral_R (a : ℂ) :
    ∫ t : ℝ, (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      2 * ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp (a^2 / 8) := by
  have h_eq : ∀ t : ℝ,
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0) +
        Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0) := by
    intro t
    rw [Complex.two_cosh]
    rw [show -2 * (t : ℂ)^2 + a * (t : ℂ) + 0 = (-2 * (t : ℂ)^2) + a * (t : ℂ) from by ring]
    rw [show -2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0 =
          (-2 * (t : ℂ)^2) + (-a) * (t : ℂ) from by ring]
    rw [Complex.exp_add, Complex.exp_add]
    have hneg : (-a) * (t : ℂ) = -(a * (t : ℂ)) := by ring
    rw [hneg]
    ring
  simp_rw [h_eq]
  rw [integral_add]
  · have hb : ((-2 : ℂ)).re < 0 := by norm_num
    rw [integral_cexp_quadratic hb a 0, integral_cexp_quadratic hb (-a) 0]
    have h_simp : ∀ a' : ℂ, (Real.pi / -(-2 : ℂ)) ^ ((1:ℂ)/2) *
        Complex.exp (0 - a' ^ 2 / (4 * (-2 : ℂ))) =
        ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp (a' ^ 2 / 8) := by
      intro a'
      congr 1
      · congr 1; ring
      · congr 1; ring
    rw [h_simp a, h_simp (-a)]
    rw [show ((-a)^2 : ℂ) = a^2 from by ring]
    ring
  · exact integrable_cexp_quadratic (by norm_num : (0:ℝ) < ((2:ℂ)).re) a 0
  · exact integrable_cexp_quadratic (by norm_num : (0:ℝ) < ((2:ℂ)).re) (-a) 0

/-- Even-split: integrability of `t ↦ exp(-2t² + a·t + 0)` on `Iic 0` and `Ioi 0`. -/
private lemma cexp_quadratic_two_integrable (a : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0)) :=
  integrable_cexp_quadratic (by norm_num : (0:ℝ) < ((2:ℂ)).re) a 0

/-- Cosh-Gaussian moment on the half-line: for any complex `a`,
`∫_{Ioi 0} 2 cosh(a·t) exp(-2t²) dt = √(π/2) · exp(a²/8)`. -/
private lemma two_cosh_gauss_integral_Ioi (a : ℂ) :
    ∫ t in Ioi (0:ℝ),
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp (a^2 / 8) := by
  -- 2·cosh(a·t)·exp(-2t²) is even in t; ∫_ℝ = 2·∫_(Ioi 0) doesn't directly hold,
  -- but ∫_ℝ = ∫_{Ioi 0} f(t) dt + ∫_{Ioi 0} f(-t) dt, and for even f they coincide.
  -- We use: ∫_ℝ 2·cosh(a·t)·exp(-2t²) dt = ∫_{Iic 0} ... + ∫_{Ioi 0} ...
  -- and ∫_{Iic 0} = ∫_{Ioi 0} (by t → -t with even integrand).
  set f : ℝ → ℂ := fun t => Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0)
  set g : ℝ → ℂ := fun t => Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0)
  -- 2·cosh(a·t)·exp(-2t²) = f(t) + g(t).
  have h_eq : ∀ t : ℝ,
      (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      f t + g t := by
    intro t
    rw [Complex.two_cosh]
    show _ = Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0) +
            Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0)
    rw [show -2 * (t : ℂ)^2 + a * (t : ℂ) + 0 = (-2 * (t : ℂ)^2) + a * (t : ℂ) from by ring]
    rw [show -2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0 =
          (-2 * (t : ℂ)^2) + (-a) * (t : ℂ) from by ring]
    rw [Complex.exp_add, Complex.exp_add]
    have hneg : (-a) * (t : ℂ) = -(a * (t : ℂ)) := by ring
    rw [hneg]
    ring
  -- f(-t) = g(t).
  have hfg : ∀ t : ℝ, f (-t) = g t := by
    intro t
    show Complex.exp (-2 * ((-t : ℝ) : ℂ)^2 + a * ((-t : ℝ) : ℂ) + 0) =
         Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0)
    push_cast
    congr 1
    ring
  have hf_int : Integrable f := cexp_quadratic_two_integrable a
  have hg_int : Integrable g := cexp_quadratic_two_integrable (-a)
  have hf_ioi : IntegrableOn f (Ioi 0) := hf_int.integrableOn
  have hg_ioi : IntegrableOn g (Ioi 0) := hg_int.integrableOn
  have hf_iic : IntegrableOn f (Iic 0) := hf_int.integrableOn
  have hf_neg_ioi : IntegrableOn (fun t : ℝ => f (-t)) (Ioi 0) := by
    have : IntegrableOn f (Iio (-(0:ℝ))) := by
      simpa using hf_int.integrableOn
    exact MeasureTheory.IntegrableOn.comp_neg_Ioi this
  -- ∫_{Ioi 0} (f t + g t) = ∫_{Ioi 0} (f t + f (-t)) (using hfg)
  -- = ∫_{Iic 0} f + ∫_{Ioi 0} f = ∫_ℝ f.
  have h_ioi : ∫ t in Ioi (0:ℝ), (f t + g t) =
      ∫ t in Ioi (0:ℝ), (f t + f (-t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; show f t + g t = f t + f (-t); rw [hfg t]
  have h_R : ∫ t in Ioi (0:ℝ), (f t + f (-t)) = ∫ t : ℝ, f t := by
    rw [integral_add hf_ioi hf_neg_ioi]
    rw [integral_comp_neg_Ioi 0 f]
    simp only [neg_zero]
    rw [add_comm]
    exact intervalIntegral.integral_Iic_add_Ioi hf_iic hf_ioi
  -- ∫_ℝ f = (π/2)^(1/2) · exp(a²/8).
  have h_full : ∫ t : ℝ, f t = ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp (a^2 / 8) := by
    show ∫ t : ℝ, Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0) = _
    have hb : ((-2 : ℂ)).re < 0 := by norm_num
    rw [integral_cexp_quadratic hb a 0]
    congr 1
    · congr 1; ring
    · congr 1; ring
  -- Assemble.
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => h_eq t),
      h_ioi, h_R, h_full]

/-- **Plancherel form of `gaussianDefectEntireKernel_local`** at every `s : ℂ`:
```
gaussianDefectEntireKernel_local s = 2π · ∫_{Ioi 0} K_2(s, t) · exp(-2t²) dt.
```
-/
theorem gaussianDefectEntireKernel_eq_K2_integral (s : ℂ) :
    OfflineDetectorEndpoint.gaussianDefectEntireKernel_local s =
      2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ),
        K_2 s t * Complex.exp (-2 * (t : ℂ)^2) := by
  unfold OfflineDetectorEndpoint.gaussianDefectEntireKernel_local K_2
  -- Express K_2(s, t)·exp(-2t²) as a linear combo of cosh-gauss pieces.
  have h_integrand : ∀ t ∈ Ioi (0:ℝ),
      (Complex.cosh (2 * (s - 1/2) * (t : ℂ)) -
        2 * Complex.cosh ((s - 1/2) * (t : ℂ)) + 1) *
          Complex.exp (-2 * (t : ℂ)^2) =
      (1 / 2 : ℂ) *
        ((2 : ℂ) * Complex.cosh ((2 * (s - 1/2) : ℂ) * (t : ℂ)) *
          Complex.exp (-2 * (t : ℂ)^2)) -
      ((2 : ℂ) * Complex.cosh ((s - 1/2 : ℂ) * (t : ℂ)) *
        Complex.exp (-2 * (t : ℂ)^2)) +
      (1 / 2 : ℂ) *
        ((2 : ℂ) * Complex.exp (-2 * (t : ℂ)^2)) := by
    intro t _
    have hfac : (2 * (s - 1/2 : ℂ)) * (t : ℂ) = 2 * (s - 1/2) * (t : ℂ) := by ring
    rw [hfac]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
  -- Integrability witnesses for term-by-term integration.
  have h_int1 : IntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((2 * (s - 1/2) : ℂ) * (t : ℂ)) *
        Complex.exp (-2 * (t : ℂ)^2)) (Ioi 0) := by
    set a : ℂ := 2 * (s - 1/2)
    have h_int_R : Integrable (fun t : ℝ =>
        (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)) := by
      have hf_int : Integrable (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0)) :=
        cexp_quadratic_two_integrable a
      have hg_int : Integrable (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0)) :=
        cexp_quadratic_two_integrable (-a)
      refine (hf_int.add hg_int).congr ?_
      apply Filter.Eventually.of_forall
      intro t
      show Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0) +
        Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0) =
        (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)
      rw [Complex.two_cosh]
      rw [show -2 * (t : ℂ)^2 + a * (t : ℂ) + 0 =
            (-2 * (t : ℂ)^2) + a * (t : ℂ) from by ring]
      rw [show -2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0 =
            (-2 * (t : ℂ)^2) + (-a) * (t : ℂ) from by ring]
      rw [Complex.exp_add, Complex.exp_add]
      have hneg : (-a) * (t : ℂ) = -(a * (t : ℂ)) := by ring
      rw [hneg]
      ring
    exact h_int_R.integrableOn
  have h_int2 : IntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((s - 1/2 : ℂ) * (t : ℂ)) *
        Complex.exp (-2 * (t : ℂ)^2)) (Ioi 0) := by
    set a : ℂ := s - 1/2
    have h_int_R : Integrable (fun t : ℝ =>
        (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)) := by
      have hf_int : Integrable (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0)) :=
        cexp_quadratic_two_integrable a
      have hg_int : Integrable (fun t : ℝ =>
          Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0)) :=
        cexp_quadratic_two_integrable (-a)
      refine (hf_int.add hg_int).congr ?_
      apply Filter.Eventually.of_forall
      intro t
      show Complex.exp (-2 * (t : ℂ)^2 + a * (t : ℂ) + 0) +
        Complex.exp (-2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0) =
        (2 : ℂ) * Complex.cosh (a * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)
      rw [Complex.two_cosh]
      rw [show -2 * (t : ℂ)^2 + a * (t : ℂ) + 0 =
            (-2 * (t : ℂ)^2) + a * (t : ℂ) from by ring]
      rw [show -2 * (t : ℂ)^2 + (-a) * (t : ℂ) + 0 =
            (-2 * (t : ℂ)^2) + (-a) * (t : ℂ) from by ring]
      rw [Complex.exp_add, Complex.exp_add]
      have hneg : (-a) * (t : ℂ) = -(a * (t : ℂ)) := by ring
      rw [hneg]
      ring
    exact h_int_R.integrableOn
  have h_int3 : IntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.exp (-2 * (t : ℂ)^2)) (Ioi 0) := by
    have h_int_R : Integrable (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2 + 0 * (t : ℂ) + 0)) :=
      cexp_quadratic_two_integrable 0
    have key : ∀ t : ℝ, Complex.exp (-2 * (t : ℂ)^2 + 0 * (t : ℂ) + 0) =
        Complex.exp (-2 * (t : ℂ)^2) := by
      intro t; congr 1; ring
    have h_R : Integrable (fun t : ℝ => Complex.exp (-2 * (t : ℂ)^2)) := by
      refine h_int_R.congr ?_
      apply Filter.Eventually.of_forall key
    exact (h_R.const_mul 2).integrableOn
  -- Split linear combination into three integrals.
  set F1 : ℝ → ℂ := fun t =>
    (2 : ℂ) * Complex.cosh ((2 * (s - 1/2) : ℂ) * (t : ℂ)) *
      Complex.exp (-2 * (t : ℂ)^2) with hF1_def
  set F2 : ℝ → ℂ := fun t =>
    (2 : ℂ) * Complex.cosh ((s - 1/2 : ℂ) * (t : ℂ)) *
      Complex.exp (-2 * (t : ℂ)^2) with hF2_def
  set F3 : ℝ → ℂ := fun t =>
    (2 : ℂ) * Complex.exp (-2 * (t : ℂ)^2) with hF3_def
  -- Goal integrand is `(1/2)·F1 - F2 + (1/2)·F3` per `h_integrand`.
  have h_int_combo :
      ∫ t in Ioi (0:ℝ),
        ((1 / 2 : ℂ) * F1 t - F2 t + (1 / 2 : ℂ) * F3 t) =
      (1/2 : ℂ) * (∫ t in Ioi (0:ℝ), F1 t) -
        (∫ t in Ioi (0:ℝ), F2 t) +
        (1/2 : ℂ) * (∫ t in Ioi (0:ℝ), F3 t) := by
    have hh1 : IntegrableOn (fun t : ℝ => (1/2:ℂ) * F1 t) (Ioi 0) :=
      h_int1.const_mul (1/2 : ℂ)
    have hh3 : IntegrableOn (fun t : ℝ => (1/2:ℂ) * F3 t) (Ioi 0) :=
      h_int3.const_mul (1/2 : ℂ)
    have hsub : IntegrableOn (fun t : ℝ => (1/2:ℂ) * F1 t - F2 t) (Ioi 0) :=
      hh1.sub h_int2
    have h_eq_int : (∫ t in Ioi (0:ℝ),
          ((1 / 2 : ℂ) * F1 t - F2 t + (1 / 2 : ℂ) * F3 t)) =
        (∫ t in Ioi (0:ℝ), ((1 / 2 : ℂ) * F1 t - F2 t)) +
          (∫ t in Ioi (0:ℝ), ((1 / 2 : ℂ) * F3 t)) :=
      integral_add hsub hh3
    rw [h_eq_int]
    have h_sub_int : (∫ t in Ioi (0:ℝ), ((1 / 2 : ℂ) * F1 t - F2 t)) =
        (∫ t in Ioi (0:ℝ), (1/2:ℂ) * F1 t) - (∫ t in Ioi (0:ℝ), F2 t) :=
      integral_sub hh1 h_int2
    rw [h_sub_int]
    have hcm1 : (∫ t in Ioi (0:ℝ), (1/2:ℂ) * F1 t) = (1/2:ℂ) * ∫ t in Ioi (0:ℝ), F1 t :=
      integral_const_mul (1/2:ℂ) F1
    have hcm3 : (∫ t in Ioi (0:ℝ), (1/2:ℂ) * F3 t) = (1/2:ℂ) * ∫ t in Ioi (0:ℝ), F3 t :=
      integral_const_mul (1/2:ℂ) F3
    rw [hcm1, hcm3]
  -- Apply h_int_combo with explicit unfolding.
  show ((Real.pi * Real.sqrt (Real.pi / 2) : ℝ) : ℂ) *
        (Complex.exp ((s - (1/2 : ℂ))^2 / 2) -
          2 * Complex.exp ((s - (1/2 : ℂ))^2 / 8) + 1) =
      2 * (Real.pi : ℂ) *
        ∫ t in Ioi (0:ℝ),
          (1/2:ℂ) * F1 t - F2 t + (1/2:ℂ) * F3 t
  rw [h_int_combo]
  -- Apply closed forms for each.
  rw [show (∫ t in Ioi (0:ℝ), F1 t) =
        ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp ((s - 1/2)^2 / 2) from by
    rw [hF1_def]
    have h := two_cosh_gauss_integral_Ioi (2 * (s - 1/2))
    have h_a_sq : (2 * (s - 1/2 : ℂ))^2 / 8 = (s - 1/2)^2 / 2 := by ring
    rw [h_a_sq] at h
    exact h]
  rw [show (∫ t in Ioi (0:ℝ), F2 t) =
        ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp ((s - 1/2)^2 / 8) from by
    rw [hF2_def]; exact two_cosh_gauss_integral_Ioi (s - 1/2)]
  -- Integral 3: same closed form with a = 0.
  have h_int3_val : ∫ t in Ioi (0:ℝ), (2 : ℂ) * Complex.exp (-2 * (t : ℂ)^2) =
      ((Real.pi / 2 : ℂ))^((1:ℂ)/2) := by
    have h := two_cosh_gauss_integral_Ioi 0
    have h_cosh_zero : ∀ t : ℝ, Complex.cosh ((0 : ℂ) * (t : ℂ)) = 1 := by
      intro t; rw [zero_mul, Complex.cosh_zero]
    have h_eq : ∀ t ∈ Ioi (0:ℝ),
        (2 : ℂ) * Complex.cosh ((0 : ℂ) * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
        (2 : ℂ) * Complex.exp (-2 * (t : ℂ)^2) := by
      intro t _; rw [h_cosh_zero t]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq] at h
    rw [h, show ((0 : ℂ)^2 / 8 : ℂ) = 0 from by ring, Complex.exp_zero, mul_one]
  rw [h_int3_val]
  -- Convert (π/2)^(1/2) to (Real.sqrt (π/2)).
  have h_sqrt_eq : ((Real.pi / 2 : ℂ))^((1:ℂ)/2) =
      ((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) := by
    rw [show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [← Real.sqrt_eq_rpow]
  rw [h_sqrt_eq]
  push_cast
  ring

#print axioms gaussianDefectEntireKernel_eq_K2_integral

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
