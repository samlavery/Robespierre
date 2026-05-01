import Mathlib
import RequestProject.HalfLineParseval
import RequestProject.MellinPlancherel

/-!
# Mellin–Parseval at the critical line

This file delivers the Mellin–Parseval identity at `σ = 1/2` for real-valued
half-line functions, bridging the proved `halfLine_cosine_parseval_strong`
(via the half-line Plancherel infrastructure already established in
`HalfLineParseval.lean`) to a Mellin-shape statement usable for the H3
closure chain.

## Strategy

For real-valued `f` on `(0,∞)`, define the substituted function
`gFun (1/2) f (u) := exp(-u/2) · f(exp(-u))` on `ℝ`.  Mathlib's
`mellin_eq_fourier` gives the pointwise identity
```
mellin (↑f) (1/2 + iτ) = 𝓕 (gFun (1/2) f) (τ / (2π)).
```

Combining this with:

* `mathlib`'s L²-Plancherel for the L²-Fourier-transform
  (`MeasureTheory.Lp.norm_fourier_eq`),

* the bridge `HalfLineParseval.fourier_Lp_eq_fourierIntegral_ae`
  identifying the L²-Fourier-transform with the classical Bochner Fourier
  integral when `g ∈ L¹ ∩ L²(ℝ)`,

* the change of variables `x = exp(-u)` translating
  `∫_ℝ ‖gFun (1/2) f u‖² du = ∫_{Ioi 0} (f x)² dx`,

* the rescaling `τ ↦ 2π · v` providing the explicit `2π` factor,

we obtain the target identity
```
∫_τ ‖mellin (↑f) (1/2 + iτ)‖² dτ = (2π) · ∫_{Ioi 0} (f x)² dx.
```

## Status

Axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
-/

open Complex Set MeasureTheory Real
open scoped FourierTransform

noncomputable section

namespace MellinParsevalCosine

/-! ### The substitution function `gFun` -/

/-- The substitution function `g_f(u) := exp(-σu) · f(exp(-u))` from
`mellin_eq_fourier`, in multiplicative `ℂ`-valued form (defeq to the
`smul` form via `Complex.real_smul`). -/
def gFun (σ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℂ :=
  ((Real.exp (-σ * u) : ℝ) : ℂ) * ((f (Real.exp (-u)) : ℝ) : ℂ)

/-- `gFun σ f` agrees with the smul form used in `mellin_eq_fourier`. -/
theorem gFun_smul_eq (σ : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    (Real.exp (-σ * u) : ℝ) • ((f (Real.exp (-u)) : ℝ) : ℂ) = gFun σ f u := by
  unfold gFun; rw [Complex.real_smul]

theorem gFun_measurable (σ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (gFun σ f) := by
  unfold gFun
  refine Measurable.mul ?_ ?_
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  · exact Complex.measurable_ofReal.comp
      (hf.comp (Real.measurable_exp.comp measurable_neg))

theorem gFun_aestronglyMeasurable (σ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    AEStronglyMeasurable (gFun σ f) volume :=
  (gFun_measurable σ hf).aestronglyMeasurable

/-- Pointwise norm-squared of `gFun (1/2) f`:
`‖gFun (1/2) f u‖² = exp(-u) · f(exp(-u))²`. -/
theorem normSq_gFun_half (f : ℝ → ℝ) (u : ℝ) :
    ‖gFun (1/2) f u‖ ^ 2 = Real.exp (-u) * (f (Real.exp (-u))) ^ 2 := by
  unfold gFun
  rw [show (((Real.exp (-(1/2 : ℝ) * u) : ℝ) : ℂ) * ((f (Real.exp (-u)) : ℝ) : ℂ))
        = ((Real.exp (-(1/2 : ℝ) * u) * f (Real.exp (-u)) : ℝ) : ℂ)
          from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  congr 1
  rw [show (Real.exp (-(1/2 : ℝ) * u)) ^ 2 =
      Real.exp (-(1/2 : ℝ) * u) * Real.exp (-(1/2 : ℝ) * u) from sq _,
      ← Real.exp_add]
  congr 1; ring

/-- Change of variables `x = exp(-u)`:
`∫_ℝ ‖gFun (1/2) f u‖² du = ∫_{Ioi 0} (f x)² dx`. -/
theorem integral_normSq_gFun_half (f : ℝ → ℝ) :
    ∫ u : ℝ, ‖gFun (1/2) f u‖ ^ 2 = ∫ x in Ioi (0:ℝ), (f x) ^ 2 := by
  simp_rw [normSq_gFun_half f]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x := by
    intro x _
    exact mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have hinj : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)
  have himg : Real.exp ∘ Neg.neg '' Set.univ = Ioi (0 : ℝ) := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
        Set.image_univ, Real.range_exp]
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := Real.exp ∘ Neg.neg)
    (f' := fun x => -Real.exp (-x)) (s := Set.univ) (g := fun x => (f x) ^ 2)
    MeasurableSet.univ hderiv hinj
  rw [himg] at hcov
  rw [hcov, MeasureTheory.setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hpos : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  show Real.exp (-u) * (f (Real.exp (-u))) ^ 2 =
    |(-Real.exp (-u))| • (f (Real.exp (-u))) ^ 2
  rw [abs_neg, abs_of_pos hpos]; rfl

/-- Integrability of `‖gFun (1/2) f‖²` on `ℝ` from `f² ∈ L¹(Ioi 0)`. -/
theorem integrable_normSq_gFun_half {f : ℝ → ℝ} (_hf_meas : Measurable f)
    (hf_sq : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0:ℝ)))) :
    Integrable (fun u : ℝ => ‖gFun (1/2) f u‖ ^ 2) volume := by
  simp_rw [normSq_gFun_half f]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x := by
    intro x _
    exact mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have hinj : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)
  have himg : Real.exp ∘ Neg.neg '' Set.univ = Ioi (0 : ℝ) := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
        Set.image_univ, Real.range_exp]
  have hf_sq_Ioi : IntegrableOn (fun t => f t ^ 2) (Ioi (0 : ℝ)) volume := hf_sq
  rw [← himg] at hf_sq_Ioi
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f := Real.exp ∘ Neg.neg)
    (f' := fun x => -Real.exp (-x)) (s := Set.univ) (g := fun x => (f x) ^ 2)
    MeasurableSet.univ hderiv hinj).mp hf_sq_Ioi
  rw [integrableOn_univ] at h
  refine h.congr ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  show |(-Real.exp (-u))| • (f (Real.exp (-u))) ^ 2 =
    Real.exp (-u) * (f (Real.exp (-u))) ^ 2
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]; rfl

/-- `gFun (1/2) f ∈ L²(ℝ)` when `f² ∈ L¹(Ioi 0)`. -/
theorem memLp_gFun_half {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_sq : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0:ℝ)))) :
    MemLp (gFun (1/2) f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (gFun_aestronglyMeasurable _ hf_meas)).mpr
    (integrable_normSq_gFun_half hf_meas hf_sq)

/-! ### Mellin = Fourier identity at the critical line -/

/-- **Mellin = Fourier of `gFun` at the critical line.**
Pointwise identity: `mellin (↑f) (1/2 + iτ) = 𝓕 (gFun (1/2) f) (τ/(2π))`. -/
theorem mellin_eq_fourier_gFun (f : ℝ → ℝ) (τ : ℝ) :
    mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ((1/2 : ℂ) + τ * I) =
      FourierTransform.fourier (gFun (1/2) f) (τ / (2 * Real.pi)) := by
  have h := mellin_eq_fourier (f := fun t : ℝ => ((f t : ℝ) : ℂ))
    (s := (1/2 : ℂ) + τ * I)
  have hre : ((1/2 : ℂ) + τ * I).re = 1/2 := by simp
  have him : ((1/2 : ℂ) + τ * I).im = τ := by simp
  rw [hre, him] at h
  rw [h]; rfl

/-! ### Plancherel + scaling: `∫_τ ‖𝓕 g (τ/(2π))‖² dτ = 2π · ∫ ‖g‖²` -/

/-- **Plancherel + rescaling.** For `g ∈ L¹ ∩ L²(ℝ)`,
`∫_τ ‖𝓕 g (τ/(2π))‖² dτ = (2π) · ∫_u ‖g u‖² du`. -/
theorem integral_normSq_fourier_div_two_pi {g : ℝ → ℂ}
    (hg_int : Integrable g volume) (hg : MemLp g 2 volume) :
    ∫ τ : ℝ, ‖FourierTransform.fourier g (τ / (2 * Real.pi))‖ ^ 2 =
      (2 * Real.pi) * ∫ u : ℝ, ‖g u‖ ^ 2 := by
  -- Bridge classical 𝓕 ↔ Lp 𝓕 (a.e.)
  have hBridge :
      ((FourierTransform.fourier (hg.toLp : Lp ℂ 2 volume)) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier g :=
    HalfLineParseval.fourier_Lp_eq_fourierIntegral_ae hg.1 hg_int hg
  -- Substitution τ → 2π · v
  have hSub : ∫ τ : ℝ, ‖FourierTransform.fourier g (τ / (2 * Real.pi))‖ ^ 2 =
      (2 * Real.pi) * ∫ v : ℝ, ‖FourierTransform.fourier g v‖ ^ 2 := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (fun τ : ℝ => ‖FourierTransform.fourier g (τ / (2 * Real.pi))‖ ^ 2) =
        (fun τ : ℝ => ‖FourierTransform.fourier g ((1 / (2 * Real.pi)) * τ)‖ ^ 2)
        from by funext τ; congr 2; ring_nf]
    rw [Measure.integral_comp_mul_left
        (fun v => ‖FourierTransform.fourier g v‖ ^ 2) (1 / (2 * Real.pi))]
    rw [show ((1 / (2 * Real.pi))⁻¹ : ℝ) = 2 * Real.pi from by field_simp]
    rw [smul_eq_mul, abs_of_pos h2π]
  rw [hSub]
  -- Replace classical 𝓕 with Lp 𝓕
  have hClassicalEqLp :
      ∫ v : ℝ, ‖FourierTransform.fourier g v‖ ^ 2 =
      ∫ v : ℝ, ‖(FourierTransform.fourier (hg.toLp : Lp ℂ 2 volume) : ℝ → ℂ) v‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hBridge] with v hv
    rw [hv]
  rw [hClassicalEqLp]
  -- Plancherel for the Lp Fourier transform
  rw [← HalfLineParseval.Lp_two_sq_norm_eq_integral_sq_norm volume
        (FourierTransform.fourier (hg.toLp : Lp ℂ 2 volume))]
  rw [MeasureTheory.Lp.norm_fourier_eq]
  rw [HalfLineParseval.Lp_two_sq_norm_eq_integral_sq_norm volume
        (hg.toLp : Lp ℂ 2 volume)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with u hu
  show ‖(↑(hg.toLp) : ℝ → ℂ) u‖ ^ 2 = ‖g u‖ ^ 2
  rw [hu]

/-! ### Mellin Parseval at the critical line -/

/-- **Mellin–Parseval at `σ = 1/2`.**

For a real-valued function `f` on `(0,∞)` with:

* `f` measurable,
* `f² ∈ L¹(Ioi 0, dx)`,
* the substituted function `gFun (1/2) f` lies in `L¹(ℝ)`
  (equivalent to `f / √x ∈ L¹(Ioi 0, dx)`),

the Mellin transform `mellin (↑f) (1/2 + iτ)` viewed as a function of `τ`
satisfies the L²-isometry identity
```
∫_τ ‖mellin (↑f) (1/2 + iτ)‖² dτ = (2π) · ∫_{Ioi 0} (f x)² dx.
```

The third hypothesis encodes the L¹-side regularity needed to ensure that the
classical pointwise Mellin integral converges; for super-exponentially decaying
test functions (e.g. cosh-Gauss) it is automatic. -/
theorem mellin_parseval_critical_line {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf_sq : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0:ℝ))))
    (hg_int : Integrable (gFun (1/2) f) volume) :
    ∫ τ : ℝ, ‖mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ((1/2 : ℂ) + τ * I)‖ ^ 2 =
      (2 * Real.pi) * ∫ x in Ioi (0:ℝ), (f x) ^ 2 := by
  have hg_memLp : MemLp (gFun (1/2) f) 2 volume := memLp_gFun_half hf_meas hf_sq
  have hLHS_eq :
      (fun τ : ℝ => ‖mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ((1/2 : ℂ) + τ * I)‖ ^ 2) =
      (fun τ : ℝ => ‖FourierTransform.fourier (gFun (1/2) f) (τ / (2 * Real.pi))‖ ^ 2) := by
    funext τ; rw [mellin_eq_fourier_gFun]
  rw [show (∫ τ : ℝ, ‖mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ((1/2 : ℂ) + τ * I)‖ ^ 2) =
      ∫ τ : ℝ, ‖FourierTransform.fourier (gFun (1/2) f) (τ / (2 * Real.pi))‖ ^ 2
      from by rw [hLHS_eq]]
  rw [integral_normSq_fourier_div_two_pi hg_int hg_memLp]
  rw [integral_normSq_gFun_half]

end MellinParsevalCosine

-- Axiom verification (default mathlib triple only)
#print axioms MellinParsevalCosine.mellin_eq_fourier_gFun
#print axioms MellinParsevalCosine.integral_normSq_gFun_half
#print axioms MellinParsevalCosine.memLp_gFun_half
#print axioms MellinParsevalCosine.integral_normSq_fourier_div_two_pi
#print axioms MellinParsevalCosine.mellin_parseval_critical_line
