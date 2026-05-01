import RequestProject.DoubleCoshKernelComparison

/-!
# Riemann-Integral Bridge — Following the Near-Collinearity Pointer

## The pointer

The double-cosh kernel pair has anchors at `π/6` and `1 − π/6`, with the
shift `(1 − π/6) − π/6 = 1 − π/3 ≈ 0.047` between them. This makes the
pair **nearly collinear** per prime: `K_R / K_L ≈ n^{π/3 − 1} ≈ n^{0.047}`.

Near-collinearity is not a bug — it's a pointer. The pair sum factorizes:

```
K_L^ℂ(s, t) + K_R^ℂ(s, t) = 2 · cosh((s − 1/2) · t) · cosh((1/2 − π/6) · t)
```

The β-dependence is isolated in `cosh((s − 1/2) · t)` — anchor exactly at
`s = 1/2`, the critical line. This matches **Riemann's classical integral
representation** of the completed zeta function ξ, which uses exactly
`cosh((s − 1/2) · t)` as kernel against the Jacobi theta function.

## What this file proves (pointwise, unconditional)

The **algebraic inversion**: for `t` where the β-independent calibration
`cosh((1/2 − π/6)·t)` is nonzero,

```
cosh((s − 1/2) · t) = (K_L^ℂ(s,t) + K_R^ℂ(s,t)) / (2 · cosh((1/2 − π/6) · t))
```

This means any integrand of the form `f(t) · cosh((s − 1/2) · t)` can be
rewritten as a paired-cosh form `test(t) · (K_L^ℂ + K_R^ℂ)(s, t)` with
explicit test `test(t) = f(t) / (2·cosh((1/2 − π/6)·t))`.

## Consequence (informal — for Stage C of ξ)

Riemann's classical formula (not yet formalized in our Mathlib version):

```
ξ(s) = 1/(s − 1) − 1/s + ∫₀^∞ 2·e^{u/2}·ω(e^{2u})·cosh((s − 1/2)·u) du
```

Applying the pointwise inversion under the integral:

```
ξ(s) = 1/(s − 1) − 1/s + ∫₀^∞ test_ξ(u) · (K_L^ℂ + K_R^ℂ)(s, u) du
```

with `test_ξ(u) = e^{u/2}·ω(e^{2u}) / cosh((1/2 − π/6)·u)`.

This **is the paired-cosh form of ξ**. The pointer was correct: near-
collinearity routes directly into Riemann's classical integral via the
pair-sum factorization.

## What this does NOT close

The bridge gives Stage C for ξ (completed zeta). Going from ξ to ζ
requires handling the `Γ(s/2) · π^{−s/2}` factor in `ξ = Γℝ · ζ`.
That's a separate step.
-/

open Complex ZetaDefs

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. The algebraic inversion — pointwise bridge -/

/-- **Pair-sum inversion**: for any complex `s` and real `t` with
`cosh((1/2 − π/6)·t) ≠ 0` (automatic for `t ≠ 0` since `π/6 ≠ 1/2`),
the unit-shift cosh equals the pair sum divided by the β-independent
calibration factor.

This is the key algebraic step that converts a `cosh((s − 1/2)·t)`
integral representation into paired-cosh form. -/
theorem cosh_shift_half_via_pair (s : ℂ) (t : ℝ)
    (ht : Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) ≠ 0) :
    Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) =
      (coshDetectorLeftC s t + coshDetectorRightC s t) /
        (2 * Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ))) := by
  have h2 : (2 : ℂ) * Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) ht
  rw [coshDetector_pair_sum_complex, eq_div_iff h2]
  ring

/-- **Integrand pair-sum form**: any `f(t)·cosh((s − 1/2)·t)` rewrites as
`test(t)·(K_L^ℂ + K_R^ℂ)(s, t)` with `test(t) = f(t)/(2·cosh((1/2−π/6)·t))`. -/
theorem integrand_pair_sum_form (s : ℂ) (t : ℝ)
    (ht : Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) ≠ 0)
    (f : ℝ → ℂ) :
    f t * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) =
      (f t / (2 * Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)))) *
        (coshDetectorLeftC s t + coshDetectorRightC s t) := by
  rw [cosh_shift_half_via_pair s t ht]
  have h2 : (2 : ℂ) * Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) ht
  field_simp

/-! ### §2. Calibration factor non-vanishing -/

/-- The calibration factor `cosh((1/2 − π/6) · t)` is nonzero for
every real `t`: `cosh` is never zero on real arguments. -/
theorem calibration_real_nonzero (t : ℝ) :
    Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) ≠ 0 := by
  -- The argument (1/2 − π/6)·t is real; cosh of a real is ≥ 1 > 0.
  have h_real : ((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ) =
                ((((1/2 : ℝ) - Real.pi / 6) * t : ℝ) : ℂ) := by push_cast; ring
  rw [h_real]
  have h_cosh_real : Complex.cosh ((((1/2 : ℝ) - Real.pi / 6) * t : ℝ) : ℂ) =
                     ((Real.cosh ((1/2 - Real.pi / 6) * t) : ℝ) : ℂ) := by
    exact (Complex.ofReal_cosh _).symm
  rw [h_cosh_real]
  intro h
  have : Real.cosh ((1/2 - Real.pi / 6) * t) = 0 := by
    have : ((Real.cosh ((1/2 - Real.pi / 6) * t) : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [h]; simp
    exact_mod_cast this
  have hpos : 0 < Real.cosh ((1/2 - Real.pi / 6) * t) := Real.cosh_pos _
  linarith

/-- **Integrand rewrite, unconditional on `t`**: `f(t)·cosh((s−1/2)·t)`
rewrites to paired form for every real `t`, using the real-cosh non-
vanishing of the calibration factor. -/
theorem integrand_pair_sum_form_real (s : ℂ) (t : ℝ) (f : ℝ → ℂ) :
    f t * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) =
      (f t / (2 * Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)))) *
        (coshDetectorLeftC s t + coshDetectorRightC s t) :=
  integrand_pair_sum_form s t (calibration_real_nonzero t) f

/-! ### §3. The Stage C bridge summary

For any function that admits a `cosh((s − 1/2)·t)` integral representation
on a region of s, the bridge gives an equivalent paired-cosh integral
representation. The remaining gap is:

1. **Riemann's integral formula for ξ** in our Mathlib version — a known
   classical result. When formalized (or added as a named axiom), the
   paired-cosh form of ξ drops out of `cosh_shift_half_via_pair` + linearity
   of integration.

2. **From ξ to ζ**: the Γ-factor correction. Handled separately; not
   addressed in this file.

So: near-collinearity → pair-sum factorization → inversion to `cosh((s−1/2)·t)`
→ this matches the unique-anchor cosh kernel in Riemann's integral formula
→ substituting gives paired-cosh form for ξ.

**The pointer pointed correctly.**
-/

/-! ### §4. Axiom hygiene -/

#print axioms cosh_shift_half_via_pair
#print axioms integrand_pair_sum_form
#print axioms calibration_real_nonzero
#print axioms integrand_pair_sum_form_real

end DoubleCoshExtension

end
