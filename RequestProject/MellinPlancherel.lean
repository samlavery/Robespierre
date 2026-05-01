import Mathlib

/-!
# Mellin–Plancherel bridge

This file packages the Mellin–Plancherel identity as standalone, axiom-clean
infrastructure.  All deliverables are unconditional and depend only on the
default axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main results

* `mellin_change_of_variables` and `mellin_change_of_variables_star_left` —
  the change of variables `x = exp(-u)` that transports the spatial integral
  on `Ioi 0` weighted by `x^(2σ-1)` into an integral over `ℝ` weighted by
  `exp(-(2σ) u)`.  Two variants (`f * star g` and `star f * g`) are provided
  so the lemma can be threaded against either pairing convention.

* `mellin_inner_l2_eq_spatial_integral` — for `MemLp 2` data on the real line,
  the L²(ℝ) inner product `⟪hf.toLp, hg.toLp⟫` of the Mellin-substituted
  functions equals the spatial integral
  `∫_{Ioi 0} star (f x) · g x · x^(2σ-1) dx`.  This is the bridge between the
  L² Hilbert-space machinery and the explicit spatial pairing.

* `mellin_plancherel_bridge` — combining the previous lemma with mathlib's
  L²-Plancherel `MeasureTheory.Lp.inner_fourier_eq` yields the central
  Mellin–Plancherel identity:
  ```
  ⟪𝓕 (hf.toLp), 𝓕 (hg.toLp)⟫_{L²(ℝ)} =
    ∫_{Ioi 0} star (f x) · g x · x^(2σ-1) dx.
  ```
  Together with `mellin_eq_fourier`, the LHS is the Mellin pairing along the
  vertical line `Re s = σ` (after a `2π` rescaling of the contour parameter
  and an integral / L²-Fourier identification under the additional `L¹ ∩ L²`
  hypothesis).

## Mathematical content

Given `f, g : ℝ → ℂ` and `σ : ℝ`, define the substituted functions
```
g_f(u) := exp(-σ u) · f (exp(-u)),
g_g(u) := exp(-σ u) · g (exp(-u)).
```
Mathlib's `mellin_eq_fourier` states
```
mellin f (σ + i t) = 𝓕 g_f (t / (2π)).
```
Hence the contour pairing `∫_t mellin f (σ+it) · star (mellin g (σ+it)) dt`,
after the substitution `τ = t / (2π)`, becomes
```
2π · ∫_τ 𝓕 g_f (τ) · star (𝓕 g_g (τ)) dτ.
```
The classical L²-Plancherel relation
```
∫ star (𝓕 g_f τ) · 𝓕 g_g τ dτ = ∫ star (g_f u) · g_g u du
```
is exactly `MeasureTheory.Lp.inner_fourier_eq` packaged with the L²
inner-product convention `⟨φ, ψ⟩ = ∫ star (φ a) · ψ a`.  Finally the
substitution `x = exp(-u)` translates the right-hand side into the spatial
integral on `Ioi 0` weighted by `x^(2σ-1)`.
-/

open Complex Set MeasureTheory Real
open scoped FourierTransform

namespace RequestProject

/-- Change of variables `x = exp(-u)` for the Mellin pairing.

The map `u ↦ exp(-u)` is a smooth bijection from `ℝ` onto `Ioi 0` with Jacobian
`|d(exp(-u))/du| = exp(-u)`.  Substituting in the spatial integral gives:
```
∫_0^∞ f(x) · star (g(x)) · x^(2σ-1) dx
  = ∫_ℝ exp(-(2σ) u) · f(exp(-u)) · star (g(exp(-u))) du.
```
This identity is purely formal — it does not require `f` or `g` to be
integrable — because both sides are equal as Bochner integrals over their
respective measure spaces (when finite, they agree numerically; when infinite,
both equal zero by Bochner's convention).
-/
theorem mellin_change_of_variables (f g : ℝ → ℂ) (σ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(2 * σ) * u) : ℂ) *
        (f (Real.exp (-u)) * star (g (Real.exp (-u)))) =
    ∫ x in Ioi (0:ℝ), f x * star (g x) * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun x => f x * star (g x) * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) with hdef
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
    (f' := fun x => -Real.exp (-x)) (s := Set.univ) (g := h)
    MeasurableSet.univ hderiv hinj
  rw [himg] at hcov
  rw [hcov, MeasureTheory.setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hpos : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have habs : |(-Real.exp (-u))| = Real.exp (-u) := by
    rw [abs_neg, abs_of_pos hpos]
  show (Real.exp (-(2 * σ) * u) : ℂ) * (f (Real.exp (-u)) * star (g (Real.exp (-u)))) =
    |(-Real.exp (-u))| • h (Real.exp (-u))
  rw [habs, hdef]
  show (Real.exp (-(2 * σ) * u) : ℂ) *
        (f (Real.exp (-u)) * star (g (Real.exp (-u)))) =
      (Real.exp (-u)) • (f (Real.exp (-u)) * star (g (Real.exp (-u))) *
        ((Real.exp (-u) : ℝ) : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ))
  rw [Complex.real_smul]
  have hrpow : ((Real.exp (-u) : ℝ) : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) =
      ((Real.exp (-u) ^ (2 * σ - 1 : ℝ) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hpos.le _).symm
  rw [hrpow]
  have key : Real.exp (-u) * Real.exp (-u) ^ (2 * σ - 1 : ℝ) = Real.exp (-(2*σ)*u) := by
    nth_rewrite 1 [show Real.exp (-u) = Real.exp (-u) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hpos]
    have hh : (1 : ℝ) + (2 * σ - 1) = 2 * σ := by ring
    rw [hh, ← Real.exp_mul]
    congr 1; ring
  rw [show ∀ (a b c d : ℂ), a * (b * c * d) = (a * d) * (b * c) from fun a b c d => by ring]
  rw [show (((Real.exp (-u) : ℝ) : ℂ)) * (((Real.exp (-u) ^ (2 * σ - 1 : ℝ) : ℝ) : ℂ)) =
        ((Real.exp (-(2*σ)*u) : ℝ) : ℂ) from by rw [← Complex.ofReal_mul, key]]

/-- Variant of `mellin_change_of_variables` with `star f * g` instead of
`f * star g`.  This is the form used by the L²(ℝ) inner-product convention
`⟨φ, ψ⟩ = ∫ star (φ a) · ψ a`. -/
theorem mellin_change_of_variables_star_left (f g : ℝ → ℂ) (σ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(2 * σ) * u) : ℂ) *
        (star (f (Real.exp (-u))) * g (Real.exp (-u))) =
    ∫ x in Ioi (0:ℝ), star (f x) * g x * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun x => star (f x) * g x * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) with hdef
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
    (f' := fun x => -Real.exp (-x)) (s := Set.univ) (g := h)
    MeasurableSet.univ hderiv hinj
  rw [himg] at hcov
  rw [hcov, MeasureTheory.setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hpos : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have habs : |(-Real.exp (-u))| = Real.exp (-u) := by
    rw [abs_neg, abs_of_pos hpos]
  show (Real.exp (-(2 * σ) * u) : ℂ) * (star (f (Real.exp (-u))) * g (Real.exp (-u))) =
    |(-Real.exp (-u))| • h (Real.exp (-u))
  rw [habs, hdef]
  show (Real.exp (-(2 * σ) * u) : ℂ) *
        (star (f (Real.exp (-u))) * g (Real.exp (-u))) =
      (Real.exp (-u)) • (star (f (Real.exp (-u))) * g (Real.exp (-u)) *
        ((Real.exp (-u) : ℝ) : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ))
  rw [Complex.real_smul]
  have hrpow : ((Real.exp (-u) : ℝ) : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) =
      ((Real.exp (-u) ^ (2 * σ - 1 : ℝ) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hpos.le _).symm
  rw [hrpow]
  have key : Real.exp (-u) * Real.exp (-u) ^ (2 * σ - 1 : ℝ) = Real.exp (-(2 * σ) * u) := by
    nth_rewrite 1 [show Real.exp (-u) = Real.exp (-u) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hpos]
    have hh : (1 : ℝ) + (2 * σ - 1) = 2 * σ := by ring
    rw [hh, ← Real.exp_mul]
    congr 1; ring
  rw [show ∀ (a b c d : ℂ), a * (b * c * d) = (a * d) * (b * c) from fun a b c d => by ring]
  rw [show (((Real.exp (-u) : ℝ) : ℂ)) * (((Real.exp (-u) ^ (2 * σ - 1 : ℝ) : ℝ) : ℂ)) =
        ((Real.exp (-(2 * σ) * u) : ℝ) : ℂ) from by rw [← Complex.ofReal_mul, key]]

/-- The L²(ℝ) inner product of the Mellin-substituted functions equals the
spatial integral on `Ioi 0` weighted by `x^(2σ-1)`.

Concretely, set `g_f(u) := (exp(-σ u) : ℂ) · f (exp(-u))` and similarly for
`g_g`.  Then
```
⟪hf.toLp, hg.toLp⟫_{L²(ℝ)}
  = ∫_{Ioi 0} star (f x) · g x · x^(2σ-1) dx,
```
where the L² inner product on the LHS is the standard one
`⟨φ, ψ⟩ = ∫ star (φ a) · ψ a`. -/
theorem mellin_inner_l2_eq_spatial_integral (f g : ℝ → ℂ) (σ : ℝ)
    (hf : MemLp (fun u : ℝ => (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))) 2
            (volume : Measure ℝ))
    (hg : MemLp (fun u : ℝ => (Real.exp (-σ * u) : ℂ) * g (Real.exp (-u))) 2
            (volume : Measure ℝ)) :
    (@inner ℂ _ _ (hf.toLp _) (hg.toLp _) : ℂ) =
    ∫ x in Ioi (0:ℝ), star (f x) * g x * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) := by
  have step1 : (@inner ℂ _ _ (hf.toLp _) (hg.toLp _) : ℂ) =
      ∫ a : ℝ, (Real.exp (-(2 * σ) * a) : ℂ) *
          (star (f (Real.exp (-a))) * g (Real.exp (-a))) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a haf hag
    rw [haf, hag, RCLike.inner_apply]
    rw [show (starRingEnd ℂ) ((Real.exp (-σ * a) : ℂ) * f (Real.exp (-a))) =
            (Real.exp (-σ * a) : ℂ) * star (f (Real.exp (-a))) from by
      rw [map_mul, Complex.conj_ofReal]; rfl]
    have hexp : (Real.exp (-σ * a) : ℂ) * (Real.exp (-σ * a) : ℂ) =
        (Real.exp (-(2 * σ) * a) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 1; congr 1; ring
    calc ((Real.exp (-σ * a) : ℂ) * g (Real.exp (-a))) *
            ((Real.exp (-σ * a) : ℂ) * star (f (Real.exp (-a))))
        = ((Real.exp (-σ * a) : ℂ) * (Real.exp (-σ * a) : ℂ)) *
            (star (f (Real.exp (-a))) * g (Real.exp (-a))) := by ring
      _ = (Real.exp (-(2 * σ) * a) : ℂ) *
            (star (f (Real.exp (-a))) * g (Real.exp (-a))) := by rw [hexp]
  rw [step1]
  exact mellin_change_of_variables_star_left f g σ

/-- **Mellin–Plancherel bridge.**

For `f, g : ℝ → ℂ` and `σ : ℝ`, set
```
g_f(u) := (exp(-σ u) : ℂ) · f (exp(-u)),
g_g(u) := (exp(-σ u) : ℂ) · g (exp(-u)).
```
If both `g_f` and `g_g` lie in `L²(ℝ)`, then the L²(ℝ) inner product of their
Fourier transforms equals the spatial integral on `Ioi 0` weighted by
`x^(2σ-1)`:
```
⟪𝓕 (hf.toLp), 𝓕 (hg.toLp)⟫_{L²(ℝ)}
  = ∫_{Ioi 0} star (f x) · g x · x^(2σ-1) dx.
```

By `mellin_eq_fourier`, the LHS equals (after a `2π` rescaling and an
identification of `𝓕` on `Lp` with the integral form, valid for instance when
`g_f, g_g ∈ L¹ ∩ L²`) the contour pairing of the Mellin transforms along
`Re s = σ`. -/
theorem mellin_plancherel_bridge (f g : ℝ → ℂ) (σ : ℝ)
    (hf : MemLp (fun u : ℝ => (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))) 2
            (volume : Measure ℝ))
    (hg : MemLp (fun u : ℝ => (Real.exp (-σ * u) : ℂ) * g (Real.exp (-u))) 2
            (volume : Measure ℝ)) :
    (@inner ℂ _ _ (𝓕 (hf.toLp _ : Lp ℂ 2 (volume : Measure ℝ)))
        (𝓕 (hg.toLp _ : Lp ℂ 2 (volume : Measure ℝ))) : ℂ) =
    ∫ x in Ioi (0:ℝ), star (f x) * g x * (x : ℂ) ^ ((2 * σ - 1 : ℝ) : ℂ) := by
  rw [MeasureTheory.Lp.inner_fourier_eq]
  exact mellin_inner_l2_eq_spatial_integral f g σ hf hg

end RequestProject

-- Axiom verification (default mathlib triple only)
#print axioms RequestProject.mellin_change_of_variables
#print axioms RequestProject.mellin_change_of_variables_star_left
#print axioms RequestProject.mellin_inner_l2_eq_spatial_integral
#print axioms RequestProject.mellin_plancherel_bridge
