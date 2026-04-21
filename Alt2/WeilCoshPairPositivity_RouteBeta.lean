import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.GaussianDetectorPair
import RequestProject.MellinPathToXi
import RequestProject.WeilCoshPairPositivity

/-!
# Route β: Even/Odd channel formalization of the prime-harmonic balance argument

## The user's framing

> Prime harmonics are balanced or unbalanced. If balanced, the defect
> envelope is `1/2 − 1/2 = 0`. If unbalanced, the defect envelope is
> positive and non-cancellable — the excess is amplitude, showing up on
> the even channel. If the channels are balanced, they vanish; if not
> balanced, not vanishing.

Translation into Lean:

* **Even channel** = `gaussianPairDefect β = ∫ (K_L − K_R)²·ψ²` — amplitude-based,
  non-negative, zero iff `β = 1/2` (unconditional via sinh² factorization +
  AM-GM dominator, already in `GaussianDetectorPair.lean`).

* **Odd channel** = a signed (phase-sensitive) integral of the detector
  difference. Specific form tracked below.

* **Vanishing condition**: for a point ρ to be a ζ zero, prime-harmonic
  consistency requires both channels balanced at ρ's position. Off-line
  ρ ⟹ even channel > 0 (non-cancellable amplitude) ⟹ ρ can't be a ζ zero.

## What this file provides

1. Even channel rename + strict positivity off-line (already proved).
2. Odd channel definition (the signed counterpart) and basic properties.
3. The named Prop `bothChannelsBalancedAtZeros` — the classical
   arithmetic claim.
4. Derivation `bothChannelsBalancedAtZeros ⟹ RiemannHypothesis`
   unconditionally (via even channel iff).
5. Documentation of the PL-based path: why PL alone gives bounds but not
   vanishing, and what additional arithmetic is needed.

## What this file does NOT provide

The derivation of `bothChannelsBalancedAtZeros` from Euler + FE + Mellin.
That is the load-bearing arithmetic step — classically equivalent to Weil's
criterion, stated honestly here as the named target.

## Status of the PL route

Phragmén–Lindelöf is a maximum principle: bounded on boundary + holomorphic
+ subexponential → bounded in interior. Applied to the complexified
even-channel function `f(s) = ∫ (K_L − K_R)(s,t)²·ψ²(t) dt`:
* `f` is entire.
* `|f|` is bounded on `Re s = 0` and `Re s = 1` (both by a constant, since
  sinh² against Gaussian has uniform bounds).
* `f(s) = f(1 − s)` by FE of sinh² under `s ↦ 1 − s`.
* On critical line: `f(1/2 + iγ) = −∫ 4·sinh²((1/2−π/6)t)·sin²(γt)·ψ² dt`,
  real non-positive, zero only at `γ = 0`.

PL gives `|f(s)| ≤ C` on the strip. But this **bounds** `f`, it doesn't
**force** `f(ρ) = 0` at ζ zeros. For vanishing, we'd need an arithmetic
identity linking `f(ρ)` to ζ — which is a Weil-formula instance for the
`(K_L − K_R)²·ψ²` test function, not provable from PL alone.

The classical closure: Weil's explicit formula for this test function
gives `Σ_ρ f̂(ρ) = arch − prime`. The prime side is ≥ 0 (by amplitude-based
construction of the test function, which is a "positive pair"). The arch
side has a specific form. If the prime side is large enough to force
arch = prime only when all zeros are on-line, RH follows. This is
Weil's criterion.
-/

open Real Complex MeasureTheory Set

noncomputable section

namespace ZD

namespace WeilPositivity

/-! ### Even channel -/

/-- **Even channel (amplitude).** Alias for `gaussianPairDefect`. The
non-negative, non-cancellable "squared excess" in the prime-harmonic read. -/
def evenChannel (β : ℝ) : ℝ := gaussianPairDefect β

/-- Even channel vanishes at the geometric balance point `β = 1/2`. -/
theorem evenChannel_zero_on_line : evenChannel (1/2) = 0 :=
  gaussianPairDefect_zero_on_line

/-- Even channel is non-negative everywhere. -/
theorem evenChannel_nonneg (β : ℝ) : 0 ≤ evenChannel β :=
  gaussianPairDefect_nonneg β

/-- **Even channel strict positivity off-line (amplitude, non-cancellable).**
Off-line `β ≠ 1/2` ⟹ even channel > 0. The amplitude-based AM-GM argument
via Gaussian dominator in `GaussianDetectorPair.lean`. -/
theorem evenChannel_pos_offline {β : ℝ} (hβ : β ≠ 1/2) :
    0 < evenChannel β :=
  gaussianPairDefect_pos_offline hβ

/-- Even channel vanishing forces `β = 1/2` (cosh-pair iff). -/
theorem re_half_of_evenChannel_zero (β : ℝ) (h : evenChannel β = 0) :
    β = 1/2 :=
  re_half_of_gaussianPairDefect_zero β h

/-! ### Odd channel

Phase-sensitive counterpart to the even channel. The classical companion
is the sinh-weighted signed integral: at a complex point `s = β + iγ`,
```
oddChannel (β, γ) := ∫ 2·sinh((β−1/2)·t)·sin(γ·t)·ψ_gaussian² dt.
```
This is the "imaginary part" of the detector pair's complex read,
extracting phase info from the `sin(γt)` factor.

At `β = 1/2`: `sinh(0) = 0` ⟹ `oddChannel(1/2, γ) = 0` for every γ.
At `γ = 0`: `sin(0) = 0` ⟹ `oddChannel(β, 0) = 0` for every β.
For off-line `β ≠ 1/2` AND `γ ≠ 0`: generically non-zero. -/

/-- **Odd channel (phase-sensitive).** Signed integral with `sinh·sin`
factors, capturing phase info from the detector pair's complex read. -/
def oddChannel (β γ : ℝ) : ℝ :=
  ∫ t : ℝ, 2 * Real.sinh ((β - 1/2) * t) * Real.sin (γ * t) * ψ_gaussian t^2

/-- Odd channel vanishes on the critical line (amplitude `β = 1/2`). -/
theorem oddChannel_zero_on_line (γ : ℝ) : oddChannel (1/2) γ = 0 := by
  unfold oddChannel
  have h : ∀ t : ℝ, 2 * Real.sinh ((1/2 - 1/2) * t) * Real.sin (γ * t) *
      ψ_gaussian t^2 = 0 := by
    intro t
    have : (1/2 - 1/2 : ℝ) * t = 0 := by ring
    rw [this, Real.sinh_zero]
    ring
  simp [h]

/-- Odd channel vanishes at `γ = 0` (real axis). -/
theorem oddChannel_zero_at_real (β : ℝ) : oddChannel β 0 = 0 := by
  unfold oddChannel
  have h : ∀ t : ℝ, 2 * Real.sinh ((β - 1/2) * t) * Real.sin (0 * t) *
      ψ_gaussian t^2 = 0 := by
    intro t
    have : (0 : ℝ) * t = 0 := by ring
    rw [this, Real.sin_zero]
    ring
  simp [h]

/-! ### Closed form for the odd channel

The Gaussian integral
```
∫ₜ 2·sinh((β-1/2)t)·sin(γt)·exp(-2t²) dt
```
evaluates in closed form via `integral_cexp_quadratic`. The key step is
the identity `2·sinh(A·t)·sin(B·t) = Im(2·cosh((A+iB)·t))`, which reduces
the odd-channel integral to the imaginary part of a standard Gaussian
moment.

Result: `oddChannel β γ = √(2π)·exp(((β-1/2)² - γ²)/8)·sin((β-1/2)·γ/4)`. -/

/-- Gaussian integral `∫ exp(-2·t² + C·t) dt = (π/2)^(1/2)·exp(C²/8)` for complex `C`. -/
private lemma gaussian_integral_complex_shift (C : ℂ) :
    ∫ t : ℝ, Complex.exp (-2 * (t : ℂ)^2 + C * (t : ℂ)) =
      ((Real.pi / 2 : ℝ) : ℂ) ^ ((1 : ℂ)/2) * Complex.exp (C^2 / 8) := by
  have key := integral_cexp_quadratic (b := -2) (by simp : ((-2 : ℂ)).re < 0) C 0
  simp only [neg_neg, add_zero] at key
  convert key using 1; push_cast; ring_nf

/-- Pointwise identity: `2·cosh(C·t)·exp(-2t²) = exp(-2t²+Ct) + exp(-2t²-Ct)`. -/
private lemma cosh_exp_eq_sum (C : ℂ) (t : ℝ) :
    2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      Complex.exp (-2 * (t : ℂ)^2 + C * (t : ℂ)) +
      Complex.exp (-2 * (t : ℂ)^2 + (-C) * (t : ℂ)) := by
  simp only [Complex.cosh]
  have h1 : Complex.exp (C * ↑t) * Complex.exp (-2 * ↑t ^ 2) =
      Complex.exp (-2 * ↑t ^ 2 + C * ↑t) := by rw [← Complex.exp_add]; ring_nf
  have h2 : Complex.exp (-(C * ↑t)) * Complex.exp (-2 * ↑t ^ 2) =
      Complex.exp (-2 * ↑t ^ 2 + (-C) * ↑t) := by rw [← Complex.exp_add]; ring_nf
  linear_combination h1 + h2

/-- Integrability of `2·cosh(C·t)·exp(-2t²)`. -/
private lemma cosh_exp_integrable (C : ℂ) : MeasureTheory.Integrable
    (fun t : ℝ => 2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)) :=
  ((integrable_cexp_quadratic' (b := -2) (by simp) C 0).congr
      (MeasureTheory.ae_of_all _ (by intro t; ring_nf))).add
    ((integrable_cexp_quadratic' (b := -2) (by simp) (-C) 0).congr
      (MeasureTheory.ae_of_all _ (by intro t; ring_nf))) |>.congr
    (MeasureTheory.ae_of_all _ (fun t => (cosh_exp_eq_sum C t).symm))

/-- Closed form for the real Gaussian moment `∫ 2·cosh(C·t)·exp(-2·t²) dt = (π/2)^(1/2)·2·exp(C²/8)`
for complex `C`. Uses the decomposition `2·cosh = exp + exp(-·)` and
`gaussian_integral_complex_shift`. -/
private lemma integral_two_cosh_gaussian (C : ℂ) :
    ∫ t : ℝ, 2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2) =
      ((Real.pi / 2 : ℝ) : ℂ) ^ ((1 : ℂ)/2) * 2 * Complex.exp (C^2 / 8) := by
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (cosh_exp_eq_sum C)),
    MeasureTheory.integral_add
      ((integrable_cexp_quadratic' (b := -2) (by simp) C 0).congr
        (MeasureTheory.ae_of_all _ (by intro t; ring_nf)))
      ((integrable_cexp_quadratic' (b := -2) (by simp) (-C) 0).congr
        (MeasureTheory.ae_of_all _ (by intro t; ring_nf))),
    gaussian_integral_complex_shift, gaussian_integral_complex_shift,
    show (-C)^2 = C^2 from by ring]
  ring

/-- `(π/2)^(1/2) · 2 = √(2π)` in ℂ. -/
private lemma pi_half_cpow_mul_two :
    (((Real.pi / 2 : ℝ) : ℂ)) ^ ((1 : ℂ)/2) * 2 = ↑(Real.sqrt (2 * Real.pi)) := by
  rw [show ((1 : ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  norm_cast
  rw [Real.sqrt_eq_rpow,
    show (2 * Real.pi)^((1:ℝ)/2) = Real.sqrt 2 * Real.pi^((1:ℝ)/2) from by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.sqrt_eq_rpow],
    show (Real.pi / 2)^((1:ℝ)/2) = Real.pi^((1:ℝ)/2) / Real.sqrt 2 from by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.sqrt_eq_rpow]]
  field_simp; rw [Real.sq_sqrt (by norm_num)]

/-- Helper: imaginary part commutes with `∫ 2·cosh(C·t)·exp(-2t²) dt`. -/
private lemma im_int_cosh_exp (C : ℂ) :
    ∫ t : ℝ, (2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)).im =
    (∫ t : ℝ, 2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)).im := by
  have heval : ∀ x : ℂ, Complex.imCLM x = x.im := fun x => by simp [Complex.imCLM, Complex.imLm]
  have h := Complex.imCLM.integral_comp_comm (cosh_exp_integrable C)
  rw [heval] at h; simp_rw [heval] at h; exact h

/-- **Closed form for the odd channel.**
`oddChannel β γ = √(2π)·exp(((β-1/2)² - γ²)/8)·sin((β-1/2)·γ/4)`.

Proof: express integrand as Im of complex Gaussian moment, apply
`integral_two_cosh_gaussian` with `C = (β-1/2) + iγ`, take imaginary part. -/
theorem oddChannel_closed_form (β γ : ℝ) :
    oddChannel β γ = Real.sqrt (2 * Real.pi) *
      Real.exp (((β - 1/2)^2 - γ^2) / 8) * Real.sin ((β - 1/2) * γ / 4) := by
  simp only [oddChannel]
  set A := β - 1/2
  set C : ℂ := ↑A + ↑γ * Complex.I
  -- Rewrite integrand as Im(2·cosh(C·t)·exp(-2t²))
  have hrw : ∀ t : ℝ, 2 * Real.sinh (A * t) * Real.sin (γ * t) * ψ_gaussian t^2 =
      (2 * Complex.cosh (C * (t : ℂ)) * Complex.exp (-2 * (t : ℂ)^2)).im := by
    intro t
    rw [ψ_gaussian_sq_eq,
      show (C * (t : ℂ)) = ↑(A * t) + ↑(γ * t) * Complex.I from by simp [C]; push_cast; ring,
      Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (-2 : ℂ) * (t : ℂ)^2 = ↑((-2 * t^2 : ℝ)) from by push_cast; ring,
      ← Complex.ofReal_exp]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_mul, zero_add, mul_one]
    norm_num; ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hrw), im_int_cosh_exp,
    integral_two_cosh_gaussian]
  -- Compute Im(((π/2)^(1/2)·2)·exp(C²/8)) = √(2π)·exp(...)·sin(...)
  have hC2_8 : C^2 / 8 = ↑((A^2 - γ^2) / 8 : ℝ) + ↑((A * γ / 4) : ℝ) * Complex.I := by
    simp only [C, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_div]
    ring_nf; simp [Complex.I_sq]; ring
  rw [show (((Real.pi / 2 : ℝ) : ℂ)) ^ ((1 : ℂ)/2) * 2 * Complex.exp (C^2 / 8) =
      ↑(Real.sqrt (2 * Real.pi)) * Complex.exp (C^2 / 8) from by
    rw [mul_assoc, ← pi_half_cpow_mul_two]; ring]
  rw [hC2_8, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add, mul_one]
  ring

#print axioms oddChannel_closed_form

/-! ### Closed form for the even channel

The Gaussian-weighted squared pair-defect
```
evenChannel β = ∫₀^∞ 4·sinh²((1/2−π/6)·t)·sinh²((β−1/2)·t)·exp(−2t²) dt
```
evaluates in closed form via `four_sinh_sq_prod` (algebraic identity reducing
`4·sinh²·sinh²` to a sum of cosh terms) and `cosh_half_gaussian_two`
(half-line cosh-Gaussian integral with `b = 2`).

Result:
`evenChannel β = √(π/2)/4 · (exp((β−π/6)²/2) + exp((1−π/6−β)²/2)
                               − 2·exp((1/2−π/6)²/2) − 2·exp((β−1/2)²/2) + 2)`. -/

/-- Integrability of `cosh(c·t)·exp(−2t²)` over `Ioi 0`. -/
private lemma cosh_integrableOn_two (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.cosh (c * t) * Real.exp (-2 * t^2)) (Ioi 0) := by
  apply MeasureTheory.Integrable.integrableOn
  apply MeasureTheory.Integrable.mono'
    (g := fun t => Real.exp (c^2/2) * Real.exp (-(3/2) * t^2))
  · exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 3/2)).const_mul _
  · apply Continuous.aestronglyMeasurable
    exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul (continuous_id.pow 2)).rexp)
  · filter_upwards with t
    have hcosh_nn : 0 ≤ Real.cosh (c * t) := le_of_lt (Real.cosh_pos _)
    have hexp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg hcosh_nn hexp_nn)]
    have hcosh_le : Real.cosh (c * t) ≤ Real.exp |c * t| := by
      rw [Real.cosh_eq]
      rcases le_total 0 (c * t) with h | h
      · rw [abs_of_nonneg h]
        linarith [Real.exp_le_exp.mpr (by linarith : -(c*t) ≤ c*t)]
      · rw [abs_of_nonpos h]
        linarith [Real.exp_le_exp.mpr (by linarith : c*t ≤ -(c*t))]
    have hAMGM : |c * t| ≤ c^2/2 + t^2/2 := by
      nlinarith [sq_nonneg (|c| - |t|), sq_abs c, sq_abs t, abs_mul c t]
    calc Real.cosh (c * t) * Real.exp (-2 * t^2)
        ≤ Real.exp |c * t| * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right hcosh_le hexp_nn
      _ ≤ Real.exp (c^2/2) * Real.exp (-(3/2) * t^2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr; linarith

/-- Half-line cosh-Gaussian integral with `b = 2`:
`∫₀^∞ cosh(c·t)·exp(−2t²) dt = (1/2)·√(π/2)·exp(c²/8)`.

Proof: `f(x) = cosh(c·x)·exp(-2x²)` is even (cosh even, x² even), so
`∫ℝ f = 2·∫₀^∞ f` via `integral_comp_abs`. Compute `∫ℝ f` via complex
lift and `integral_two_cosh_gaussian`. -/
private lemma cosh_half_gaussian_two (c : ℝ) :
    ∫ t in Ioi (0:ℝ), Real.cosh (c * t) * Real.exp (-2 * t^2) =
    (1/2) * Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) := by
  -- Even symmetry: cosh(c·|x|)·exp(-2·|x|²) = cosh(c·x)·exp(-2x²).
  have hf_even : ∀ x : ℝ,
      Real.cosh (c * |x|) * Real.exp (-2 * |x|^2) =
      Real.cosh (c * x) * Real.exp (-2 * x^2) := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, mul_neg, Real.cosh_neg, neg_sq]
  -- `integral_comp_abs` gives `∫ f(|x|) = 2·∫_{Ioi 0} f(x)`.
  have hcomp :
      ∫ x : ℝ, Real.cosh (c * |x|) * Real.exp (-2 * |x|^2) =
      2 * ∫ x in Ioi (0 : ℝ), Real.cosh (c * x) * Real.exp (-2 * x^2) := by
    have := integral_comp_abs (f := fun y : ℝ => Real.cosh (c * y) * Real.exp (-2 * y^2))
    simpa using this
  -- By even symmetry, `∫ f(|x|) = ∫ f(x)`.
  have hfull_eq :
      ∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      ∫ x : ℝ, Real.cosh (c * |x|) * Real.exp (-2 * |x|^2) :=
    MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => (hf_even x).symm))
  have hint_full :
      ∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      2 * ∫ x in Ioi (0 : ℝ), Real.cosh (c * x) * Real.exp (-2 * x^2) := by
    rw [hfull_eq]; exact hcomp
  -- Compute ∫ℝ via complex lift: ∫ℝ cosh(cx)·exp(-2x²) = √(π/2)·exp(c²/8).
  have hcast_full : ((∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) : ℝ) : ℂ) =
      ((Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) : ℝ) : ℂ) := by
    rw [show ((∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) : ℝ) : ℂ) =
          ∫ x : ℝ, ((Real.cosh (c * x) * Real.exp (-2 * x^2) : ℝ) : ℂ) from
        integral_ofReal.symm]
    have hintegrand : ∀ x : ℝ,
        ((Real.cosh (c * x) * Real.exp (-2 * x^2) : ℝ) : ℂ) =
        (1/2) * ((2 : ℂ) * Complex.cosh ((c : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * (x : ℂ)^2)) := by
      intro x
      rw [Complex.ofReal_mul, Complex.ofReal_cosh, Complex.ofReal_exp]
      push_cast; ring
    simp_rw [hintegrand]
    rw [show (∫ (x : ℝ), (1/2 : ℂ) * ((2 : ℂ) * Complex.cosh ((c : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * (x : ℂ)^2)))
        = (1/2 : ℂ) * ∫ (x : ℝ), ((2 : ℂ) * Complex.cosh ((c : ℂ) * (x : ℂ)) *
          Complex.exp (-2 * (x : ℂ)^2))
        from MeasureTheory.integral_const_mul (1/2 : ℂ) _,
        integral_two_cosh_gaussian (c : ℂ)]
    rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ Real.pi / 2),
        ← Real.sqrt_eq_rpow,
        show ((c : ℂ)^2/8) = ((c^2/8 : ℝ) : ℂ) from by push_cast; ring,
        ← Complex.ofReal_exp]
    push_cast; ring
  have hfull_r : ∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) := by exact_mod_cast hcast_full
  have h2 := hint_full
  rw [hfull_r] at h2
  linarith

/-- Algebraic identity: `4·sinh²(At)·sinh²(Bt)` as a sum of cosh terms. -/
private lemma four_sinh_sq_prod (A B t : ℝ) :
    4 * Real.sinh (A * t)^2 * Real.sinh (B * t)^2 =
    (1/2) * Real.cosh (2*(A+B)*t) + (1/2) * Real.cosh (2*(A-B)*t)
    - Real.cosh (2*A*t) - Real.cosh (2*B*t) + 1 := by
  -- sinh²(x) = (cosh(2x) - 1)/2, from cosh_two_mul + cosh_sq_sub_sinh_sq.
  have hsinh_sq : ∀ x : ℝ, Real.sinh x ^ 2 = (Real.cosh (2*x) - 1) / 2 := by
    intro x
    have h1 := Real.cosh_two_mul x
    have h2 := Real.cosh_sq_sub_sinh_sq x
    linarith
  have hsA : Real.sinh (A * t)^2 = (Real.cosh (2*A*t) - 1) / 2 := by
    have := hsinh_sq (A * t)
    rw [show (2 * (A * t) : ℝ) = 2 * A * t from by ring] at this
    exact this
  have hsB : Real.sinh (B * t)^2 = (Real.cosh (2*B*t) - 1) / 2 := by
    have := hsinh_sq (B * t)
    rw [show (2 * (B * t) : ℝ) = 2 * B * t from by ring] at this
    exact this
  have hprod : Real.cosh (2*A*t) * Real.cosh (2*B*t) =
      (1/2) * Real.cosh (2*(A+B)*t) + (1/2) * Real.cosh (2*(A-B)*t) := by
    rw [show 2*(A+B)*t = 2*A*t + 2*B*t from by ring,
        show 2*(A-B)*t = 2*A*t - 2*B*t from by ring, Real.cosh_add, Real.cosh_sub]; ring
  rw [hsA, hsB]; linarith [hprod]

/-- **Closed form for the even channel.**
`evenChannel β = √(π/2)/4 · (exp((β−π/6)²/2) + exp((1−π/6−β)²/2)
                               − 2·exp((1/2−π/6)²/2) − 2·exp((β−1/2)²/2) + 2)`.

Proof: unfold to `gaussianPairDefect`, apply `pairDetectorSqDiff_sinh_factor`
and `ψ_gaussian_sq_eq`, expand `4·sinh²·sinh²` via `four_sinh_sq_prod`,
split the integral and close each term with `cosh_half_gaussian_two`. -/
theorem evenChannel_closed_form (β : ℝ) :
    evenChannel β = Real.sqrt (Real.pi / 2) / 4 * (
      Real.exp ((β - Real.pi/6)^2 / 2) +
      Real.exp ((1 - Real.pi/6 - β)^2 / 2) -
      2 * Real.exp ((1/2 - Real.pi/6)^2 / 2) -
      2 * Real.exp ((β - 1/2)^2 / 2) + 2) := by
  unfold evenChannel gaussianPairDefect
  set A := (1/2 : ℝ) - Real.pi/6
  set B := β - (1/2 : ℝ)
  have h_integrand : ∀ t : ℝ,
      pairDetectorSqDiff β t * (ψ_gaussian t)^2 =
      1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
      1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
      Real.cosh (2*A*t) * Real.exp (-2*t^2) -
      Real.cosh (2*B*t) * Real.exp (-2*t^2) +
      Real.exp (-2*t^2) := by
    intro t
    rw [pairDetectorSqDiff_sinh_factor, ψ_gaussian_sq_eq]
    have h := four_sinh_sq_prod A B t
    linear_combination (Real.exp (-2 * t^2)) * h
  simp_rw [h_integrand]
  have hI1 : IntegrableOn (fun t => 1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2))) (Ioi 0) :=
    (cosh_integrableOn_two (2*(A+B))).const_mul (1/2)
  have hI2 : IntegrableOn (fun t => 1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2))) (Ioi 0) :=
    (cosh_integrableOn_two (2*(A-B))).const_mul (1/2)
  have hI3 : IntegrableOn (fun t => Real.cosh (2*A*t) * Real.exp (-2*t^2)) (Ioi 0) :=
    cosh_integrableOn_two (2*A)
  have hI4 : IntegrableOn (fun t => Real.cosh (2*B*t) * Real.exp (-2*t^2)) (Ioi 0) :=
    cosh_integrableOn_two (2*B)
  have hI5 : IntegrableOn (fun t => Real.exp (-2*t^2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2)).integrableOn
  have hv1 : ∫ t in Ioi (0:ℝ), Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2) =
      1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A+B))^2 / 8) := cosh_half_gaussian_two _
  have hv2 : ∫ t in Ioi (0:ℝ), Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2) =
      1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A-B))^2 / 8) := cosh_half_gaussian_two _
  have hv3 : ∫ t in Ioi (0:ℝ), Real.cosh (2*A*t) * Real.exp (-2*t^2) =
      1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*A)^2 / 8) := cosh_half_gaussian_two _
  have hv4 : ∫ t in Ioi (0:ℝ), Real.cosh (2*B*t) * Real.exp (-2*t^2) =
      1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*B)^2 / 8) := cosh_half_gaussian_two _
  have hv5 : ∫ t in Ioi (0:ℝ), Real.exp (-2 * t^2) = Real.sqrt (Real.pi/2) / 2 :=
    integral_gaussian_Ioi (2:ℝ)
  -- `integral_add` pattern-matches on `Pi.add`, which doesn't reach through our
  -- flat sum-integrand. Build each decomposition as a standalone equation,
  -- then combine with `linarith`.
  have hc1 : ∫ t in Ioi (0:ℝ), 1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) =
      1/2 * (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A+B))^2 / 8)) := by
    rw [integral_const_mul, hv1]
  have hc2 : ∫ t in Ioi (0:ℝ), 1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) =
      1/2 * (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A-B))^2 / 8)) := by
    rw [integral_const_mul, hv2]
  have step1 :
      ∫ t in Ioi (0:ℝ),
        (1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
              1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
            Real.cosh (2*A*t) * Real.exp (-2*t^2) -
          Real.cosh (2*B*t) * Real.exp (-2*t^2)) +
        Real.exp (-2*t^2) =
      (∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
              Real.cosh (2*A*t) * Real.exp (-2*t^2) -
            Real.cosh (2*B*t) * Real.exp (-2*t^2)) +
      ∫ t in Ioi (0:ℝ), Real.exp (-2*t^2) :=
    integral_add (((hI1.add hI2).sub hI3).sub hI4) hI5
  have step2 :
      ∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
              Real.cosh (2*A*t) * Real.exp (-2*t^2) -
            Real.cosh (2*B*t) * Real.exp (-2*t^2) =
      (∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
              Real.cosh (2*A*t) * Real.exp (-2*t^2)) -
      ∫ t in Ioi (0:ℝ), Real.cosh (2*B*t) * Real.exp (-2*t^2) :=
    integral_sub ((hI1.add hI2).sub hI3) hI4
  have step3 :
      ∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
              Real.cosh (2*A*t) * Real.exp (-2*t^2) =
      (∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2))) -
      ∫ t in Ioi (0:ℝ), Real.cosh (2*A*t) * Real.exp (-2*t^2) :=
    integral_sub (hI1.add hI2) hI3
  have step4 :
      ∫ t in Ioi (0:ℝ),
          1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
                1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) =
      (∫ t in Ioi (0:ℝ), 1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2))) +
      ∫ t in Ioi (0:ℝ), 1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) :=
    integral_add hI1 hI2
  -- Combine all steps. First reduce the LHS integral to the sum of five named integrals.
  have hsum :
      ∫ t in Ioi (0:ℝ),
        1/2 * (Real.cosh (2*(A+B)*t) * Real.exp (-2*t^2)) +
              1/2 * (Real.cosh (2*(A-B)*t) * Real.exp (-2*t^2)) -
            Real.cosh (2*A*t) * Real.exp (-2*t^2) -
          Real.cosh (2*B*t) * Real.exp (-2*t^2) +
        Real.exp (-2*t^2) =
      1/2 * (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A+B))^2 / 8)) +
      1/2 * (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*(A-B))^2 / 8)) -
      (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*A)^2 / 8)) -
      (1/2 * Real.sqrt (Real.pi/2) * Real.exp ((2*B)^2 / 8)) +
      Real.sqrt (Real.pi/2) / 2 := by
    linarith [step1, step2, step3, step4, hc1, hc2, hv3, hv4, hv5]
  rw [hsum]
  simp only [A, B]; ring_nf

#print axioms evenChannel_closed_form

/-! ### Target: both channels balanced at every zero -/

/-- **Load-bearing target.** At every nontrivial ζ zero `ρ = β + iγ`,
both channels are balanced:
* even channel at `β`: zero (amplitude balanced).
* odd channel at `(β, γ)`: zero (phase balanced).

Arithmetic content: this is the prime-harmonic consistency condition
that a genuine ζ zero must satisfy. Off-line ρ would produce unbalanced
prime harmonics (even channel > 0, non-cancellable amplitude), so no
off-line zero can exist. -/
def bothChannelsBalancedAtZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
    evenChannel ρ.re = 0 ∧ oddChannel ρ.re ρ.im = 0

/-- **RH from both-channels-balanced target.** Forward chain:
`bothChannelsBalancedAtZeros ⟹ RiemannHypothesis`. Proof: at each zero,
the even-channel balance forces `ρ.re = 1/2` via
`re_half_of_evenChannel_zero`. Then `RHBridge.no_offline_zeros_implies_rh`
closes. Only the even channel is needed for the RH derivation — the odd
channel balance is additional arithmetic content asserted by the target. -/
theorem RiemannHypothesis_of_bothChannelsBalanced
    (h : bothChannelsBalancedAtZeros) : RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  exact re_half_of_evenChannel_zero ρ.re (h ρ hρ).1

#print axioms RiemannHypothesis_of_bothChannelsBalanced

/-! ### Equivalence with the pair-defect target

`bothChannelsBalancedAtZeros` implies `pair_defect_vanishes_at_zeros`
trivially (just drops the odd channel). The converse requires proving
the odd channel also vanishes at zeros. -/

/-- Both-channels-balanced target implies the even-channel-only pair-defect
target. -/
theorem pair_defect_vanishes_of_bothChannelsBalanced
    (h : bothChannelsBalancedAtZeros) : pair_defect_vanishes_at_zeros :=
  fun ρ hρ => (h ρ hρ).1

#print axioms pair_defect_vanishes_of_bothChannelsBalanced

end WeilPositivity

end ZD

end
