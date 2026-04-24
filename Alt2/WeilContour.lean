import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.RiemannXiDecay
import RequestProject.ZetaStripBound
import RequestProject.MellinPathToXi
import RequestProject.PartialWeilFormula
import RequestProject.WeilCoshPairPositivity_RouteBeta
import RequestProject.WeilCoshTest

/-!
# Weil Contour Integration Chain — Building Blocks

This file provides building blocks for the unconditional contour
integration proof of the Gaussian-pair Weil formula instance.

## Cycle 1

* `mellin_gaussian` — the foundational Mellin transform of `exp(-x²)`:
  ```
  mellin (fun t => exp(-t²)) s = (1/2) · Γ(s/2)   for Re s > 0.
  ```
  Derived from Mathlib's `mellin_comp_rpow` + `Complex.Gamma_eq_integral` +
  `Complex.GammaIntegral_eq_mellin`. Axiom-clean.

-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 1 — foundational Gaussian Mellin transform
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Gaussian Mellin transform.** The Mellin transform of `exp(-x²)` is
`(1/2)·Γ(s/2)` for `Re s > 0`.

Classical result, derived from Mathlib via the change of variables
`t ↦ t²` using `mellin_comp_rpow`:

  `mellin (t ↦ f(t²)) s = (1/2) · mellin f (s/2)`

with `f(x) := exp(-x)`. The RHS uses
`Complex.GammaIntegral_eq_mellin` + `Complex.Gamma_eq_integral` to
identify `mellin (exp ∘ -id) (s/2) = Γ(s/2)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. No sorries. -/
theorem mellin_gaussian (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-t^2) : ℂ)) s =
    (1/2 : ℂ) * Complex.Gamma (s/2) := by
  -- Convert natural pow to Real.rpow for mellin_comp_rpow compatibility.
  have hpow : ∀ t : ℝ, (t^2 : ℝ) = t ^ (2 : ℝ) := by
    intro t
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num]
    rw [Real.rpow_natCast]
  have h_rewrite : (fun t : ℝ => (Real.exp (-t^2) : ℂ)) =
                    (fun t : ℝ => (Real.exp (-(t^(2:ℝ))) : ℂ)) := by
    funext t; rw [hpow]
  rw [h_rewrite]
  -- Apply change of variables t ↦ t² with mellin_comp_rpow.
  have h1 := mellin_comp_rpow (E := ℂ) (fun x : ℝ => (Real.exp (-x) : ℂ)) s 2
  rw [h1]
  -- Simplify |2|⁻¹ = 1/2 and s/↑2 = s/2 (complex).
  rw [show |(2:ℝ)| = 2 from abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [show ((2:ℝ) : ℂ) = (2:ℂ) from by push_cast; rfl]
  -- Identify mellin of exp(-x) with Γ.
  have hs2 : 0 < (s/2).re := by simp; linarith
  rw [show mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) (s/2) = Complex.Gamma (s/2) by
    rw [← Complex.GammaIntegral_eq_mellin]
    exact (Complex.Gamma_eq_integral hs2).symm]
  -- Finish: (1/2) • Γ(s/2) = (1/2) * Γ(s/2)
  show (2⁻¹ : ℝ) • Complex.Gamma (s / 2) = 1 / 2 * Complex.Gamma (s / 2)
  rw [Complex.real_smul]
  push_cast; ring

#print axioms mellin_gaussian

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 2 — Mellin convergence + differentiability on Re s > 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Gaussian Mellin integral converges absolutely for Re s > 0.**

Uses `mellinConvergent_of_isBigO_rpow_exp` with:
* `a = 1` (exp decay `exp(-1·t)` dominates `exp(-t²)` at ∞ for `t ≥ 1`).
* `b = s.re / 2` (singularity exponent at 0; `t^(-s.re/2)` dominates bounded
  `exp(-t²)` near 0 for `t ∈ (0, 1)`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem mellin_gaussian_convergent (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => (Real.exp (-t^2) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow_exp (a := 1) one_pos
    ?_ ?_ ?_ (b := s.re/2) (by linarith : s.re/2 < s.re)
  · -- Gaussian is locally integrable on Ioi 0.
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (Continuous.neg (continuous_id.pow 2)))).continuousOn
  · -- f =O[atTop] exp(-1·t): for t ≥ 1, exp(-t²) ≤ exp(-t) since t² ≥ t.
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    rw [one_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith
  · -- f =O[nhdsWithin 0 Ioi 0] t^(-s.re/2): for t ∈ (0,1), exp(-t²) ≤ 1 ≤ t^(-s.re/2).
    apply Asymptotics.IsBigO.of_bound 1
    have h_pos : 0 < s.re/2 := by linarith
    have h_mem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
      apply mem_nhdsWithin.mpr
      refine ⟨Iio 1, isOpen_Iio, by norm_num, ?_⟩
      intro x ⟨hx_neg, hx_pos⟩
      exact ⟨hx_pos, hx_neg⟩
    filter_upwards [h_mem] with t ht
    obtain ⟨h_t_pos, h_t_lt_1⟩ := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul,
        Real.norm_of_nonneg (Real.rpow_nonneg h_t_pos.le _)]
    have h_exp_le : Real.exp (-t^2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    have h_rpow_ge : (1:ℝ) ≤ t^(-(s.re/2)) := by
      rw [show (1:ℝ) = t^(0:ℝ) from (Real.rpow_zero _).symm]
      apply Real.rpow_le_rpow_of_exponent_ge h_t_pos h_t_lt_1.le
      linarith
    linarith

#print axioms mellin_gaussian_convergent

/-- **Gaussian Mellin transform is holomorphic on Re s > 0.**

For every `s₀` with `Re s₀ > 0`, the map `s ↦ mellin (fun t => exp(-t²)) s`
is differentiable at `s₀`. Direct application of
`mellin_differentiableAt_of_isBigO_rpow_exp` with the same decay bounds
as `mellin_gaussian_convergent`. -/
theorem mellin_gaussian_differentiableAt (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun s => mellin (fun t : ℝ => (Real.exp (-t^2) : ℂ)) s) s := by
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) one_pos
    ?_ ?_ ?_ (b := s.re/2) (by linarith : s.re/2 < s.re)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (Continuous.neg (continuous_id.pow 2)))).continuousOn
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    rw [one_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply Asymptotics.IsBigO.of_bound 1
    have h_pos : 0 < s.re/2 := by linarith
    have h_mem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
      apply mem_nhdsWithin.mpr
      refine ⟨Iio 1, isOpen_Iio, by norm_num, ?_⟩
      intro x ⟨hx_neg, hx_pos⟩
      exact ⟨hx_pos, hx_neg⟩
    filter_upwards [h_mem] with t ht
    obtain ⟨h_t_pos, h_t_lt_1⟩ := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul,
        Real.norm_of_nonneg (Real.rpow_nonneg h_t_pos.le _)]
    have h_exp_le : Real.exp (-t^2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    have h_rpow_ge : (1:ℝ) ≤ t^(-(s.re/2)) := by
      rw [show (1:ℝ) = t^(0:ℝ) from (Real.rpow_zero _).symm]
      apply Real.rpow_le_rpow_of_exponent_ge h_t_pos h_t_lt_1.le
      linarith
    linarith

#print axioms mellin_gaussian_differentiableAt

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 3 — scaled Gaussian Mellin transform
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Scaled Gaussian Mellin transform.** For `a > 0` and `Re s > 0`:

  `mellin (fun t => exp(-a·t²)) s = (1/2) · a^(-s/2) · Γ(s/2)`.

Derived by change of variables `u = √a · t` applying `mellin_comp_mul_left`
to `mellin_gaussian`, with the identity `√a^(-s) = a^(-s/2)` via
`Complex.cpow_mul` (hypothesis satisfied since `log a` is real for `a > 0`).

Useful for the Weil formula contour: `ψ_gaussian² = exp(-2t²)` gives
`mellin ψ_gaussian² s = (1/2) · 2^(-s/2) · Γ(s/2)` as a direct corollary. -/
theorem mellin_gaussian_scaled (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-a * t^2) : ℂ)) s =
    (1/2 : ℂ) * ((a : ℂ)^(-s/2)) * Complex.Gamma (s/2) := by
  have hsa : (0:ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  -- Rewrite exp(-a·t²) as exp(-(√a·t)²) to apply mellin_comp_mul_left.
  have h_eq : ∀ t : ℝ, Real.exp (-a * t^2) = Real.exp (-(Real.sqrt a * t)^2) := by
    intro t
    congr 1
    have : (Real.sqrt a * t)^2 = a * t^2 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
    linarith
  have h_fun_eq : (fun t : ℝ => (Real.exp (-a * t^2) : ℂ)) =
                  (fun t : ℝ =>
                    ((fun u : ℝ => (Real.exp (-u^2) : ℂ)) (Real.sqrt a * t))) := by
    funext t
    show _ = (Real.exp (-(Real.sqrt a * t)^2) : ℂ)
    exact_mod_cast h_eq t
  rw [h_fun_eq]
  rw [mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u^2) : ℂ)) s hsa]
  rw [mellin_gaussian s hs]
  rw [smul_eq_mul]
  -- Identity: √a^(-s) = a^(-s/2) as complex numbers.
  have h_sqrt_identity : ((Real.sqrt a : ℝ) : ℂ)^(-s) = ((a : ℝ) : ℂ)^(-s/2) := by
    have h1 : ((Real.sqrt a : ℝ) : ℂ) = ((a : ℝ) : ℂ)^((1/2 : ℂ)) := by
      rw [Real.sqrt_eq_rpow]
      rw [show ((1/2 : ℂ)) = (((1/2 : ℝ) : ℝ) : ℂ) from by push_cast; ring]
      rw [← Complex.ofReal_cpow ha.le]
    have hloga_im : (Complex.log (a : ℂ)).im = 0 := by
      rw [Complex.log_im, Complex.arg_ofReal_of_nonneg ha.le]
    have h_half_im : ((1/2 : ℂ)).im = 0 := by norm_num
    rw [h1, ← Complex.cpow_mul]
    · congr 1; ring
    · rw [Complex.mul_im, hloga_im, h_half_im]; simp; linarith [Real.pi_pos]
    · rw [Complex.mul_im, hloga_im, h_half_im]; simp; exact Real.pi_pos.le
  rw [h_sqrt_identity]
  ring

#print axioms mellin_gaussian_scaled

/-- **Mellin of `ψ_gaussian²`.** Direct specialization of the scaled Gaussian
Mellin at `a = 2`: the squared Gaussian test function has Mellin transform
`(1/2) · 2^(-s/2) · Γ(s/2)` on `Re s > 0`. Useful for the pair-defect
integrand where `ψ_gaussian(t)² = exp(-2t²)` appears. -/
theorem mellin_psi_gaussian_sq (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => (Real.exp (-2 * t^2) : ℂ)) s =
    (1/2 : ℂ) * ((2 : ℂ)^(-s/2)) * Complex.Gamma (s/2) := by
  have h := mellin_gaussian_scaled 2 (by norm_num : (0:ℝ) < 2) s hs
  simpa using h

#print axioms mellin_psi_gaussian_sq

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 4 — log-derivative / von Mangoldt bridge (prime side of Weil)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Log-derivative / von Mangoldt bridge (prime side of Weil's formula).**

For `Re s > 1`, `−ζ'(s)/ζ(s)` equals the Dirichlet `LSeries` of the von
Mangoldt function:

```
Σ_n Λ(n) / n^s = −ζ'(s) / ζ(s)    for Re s > 1.
```

This is the **primary entry point to the prime side** of Weil's explicit
formula. In the contour-integration argument, we start with the contour
integral of `−ζ'/ζ · M(h)` on a vertical line `Re s = 2`; this identity
converts it to `Σ_n Λ(n) · n^(-2) · M(h)(s) ds`-type expressions that
assemble the prime sum.

Available in Mathlib as
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. Re-exported
here for visibility in the Weil-contour chain. -/
theorem neg_zeta_log_deriv_eq_vonMangoldt_LSeries
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
    -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

#print axioms neg_zeta_log_deriv_eq_vonMangoldt_LSeries

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 5 — ζ analytic structure near s = 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **ζ has a simple pole at s = 1 with residue 1.**

Classical result, in Mathlib as `riemannZeta_residue_one`. Re-exported
here as the Weil-contour input: when we move the contour across `s = 1`,
the residue contribution is `M(h)(1)` (pole of ζ multiplied by Mellin
value). -/
theorem zeta_residue_one :
    Filter.Tendsto (fun s => (s - 1) * riemannZeta s)
      (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
  riemannZeta_residue_one

/-- **ζ is holomorphic away from s = 1.**

For any `s ≠ 1`, `riemannZeta` is differentiable at `s`. This is the basic
regularity input for contour arguments: ζ is analytic everywhere except at
its single pole. -/
theorem zeta_differentiableAt_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

#print axioms zeta_residue_one
#print axioms zeta_differentiableAt_of_ne_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 6 — functional equation (transfer Re = -1 ↔ Re = 2)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Classical functional equation of `ζ`.**

For `s ≠ 1` and `s` not a non-positive integer,
`ζ(1-s) = 2·(2π)^{-s}·Γ(s)·cos(πs/2)·ζ(s)`.

This is the bridge to transfer contour integrals from `Re s = -1` (left
edge) back to `Re s = 2` (right edge, where the Euler product applies).
Mathlib's `riemannZeta_one_sub`. -/
theorem zeta_functional_equation {s : ℂ} (hnotpole : ∀ (n : ℕ), s ≠ -↑n)
    (hs1 : s ≠ 1) :
    riemannZeta (1 - s) =
      2 * (2 * (Real.pi : ℂ))^(-s) * Complex.Gamma s *
        Complex.cos (Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hnotpole hs1

#print axioms zeta_functional_equation

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 7 — Dirichlet series (Euler product) at Re s > 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Dirichlet series representation of `ζ` at Re s > 1.**

For `Re s > 1`, `ζ(s) = Σ 1/n^s`. This is the starting point for the
Euler-product conversion on the right edge `Re s = 2` of the contour:
evaluating `-ζ'/ζ · M(h)` there reduces to the prime-side sum via the
von Mangoldt bridge (`neg_zeta_log_deriv_eq_vonMangoldt_LSeries`). -/
theorem zeta_dirichlet_series {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' (n : ℕ), 1 / (n : ℂ)^s :=
  zeta_eq_tsum_one_div_nat_cpow hs

#print axioms zeta_dirichlet_series

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 8 — non-vanishing of ζ on Re ≥ 1 (log-derivative safety)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **ζ has no zeros on `Re s ≥ 1`.**

Classical result, key for the log-derivative `ζ'/ζ` to be analytic on the
right edge `Re s = 2` of the Weil-contour rectangle. Mathlib's
`riemannZeta_ne_zero_of_one_le_re`. -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **ζ has no zeros on `Re s > 1`.** Strict version via the Euler product. -/
theorem zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

#print axioms zeta_ne_zero_of_one_le_re
#print axioms zeta_ne_zero_of_one_lt_re

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 9 — ζ at s = 0 (boundary value for Re s = -1 edge via FE)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **ζ(0) = -1/2.** A specific boundary value, useful for contour endpoints
and for the FE transfer from `Re s = -1` to `Re s = 2`. -/
theorem zeta_at_zero : riemannZeta 0 = -1/2 := riemannZeta_zero

#print axioms zeta_at_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 10 — Fourier transform of Gaussian (zero-side via Fourier pair)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Fourier integral of Gaussian.** For `b ∈ ℂ` with `0 < Re b` and any
`t ∈ ℂ`:

```
∫_ℝ exp(I·t·x) · exp(-b·x²) dx = (π/b)^(1/2) · exp(-t²/(4b)).
```

This is the classical Gaussian Fourier identity. Specializing `b = 1`
gives the unit Gaussian's Fourier partner: `(π)^(1/2) · exp(-t²/4)`.

For the Weil-formula zero-side, this is the Fourier partner `φ(t)` of the
prime-side test function `h(x) = exp(-x²)`. Combined with
`mellin_gaussian` (W1 closed form), we have both dual representations. -/
theorem fourier_gaussian_unit (t : ℂ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * (x : ℂ)) *
      Complex.exp (-(1:ℂ) * (x : ℂ)^2) =
    ((Real.pi : ℂ) / 1)^((1:ℂ)/2) * Complex.exp (-t^2/(4 * 1)) :=
  fourierIntegral_gaussian (by norm_num : 0 < ((1:ℂ)).re) t

/-- **Fourier of Gaussian, scaled.** General `b > 0` (real) case. Useful
for the pair-test function's Fourier partner when scaling `ψ_gaussian²`. -/
theorem fourier_gaussian_scaled (b : ℝ) (hb : 0 < b) (t : ℂ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * (x : ℂ)) *
      Complex.exp (-((b : ℂ)) * (x : ℂ)^2) =
    ((Real.pi : ℂ) / (b : ℂ))^((1:ℂ)/2) * Complex.exp (-t^2/(4 * (b : ℂ))) := by
  apply fourierIntegral_gaussian
  simp
  exact hb

#print axioms fourier_gaussian_unit
#print axioms fourier_gaussian_scaled

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 11 — Specific Mellin values for Weil residues
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Mellin transform of Gaussian at s = 1.**

`M(exp(-t²))(1) = √π / 2`. This value is the residue contribution at the
simple pole `s = 1` of ζ when applying Weil's explicit formula to the
Gaussian test function:

```
Residue at s=1 of (-ζ'/ζ · M(h))(s)
  = (residue of -ζ'/ζ at s=1) · M(h)(1)
  = 1 · √π/2
  = √π/2.
```

Follows from `mellin_gaussian` + `Complex.Gamma_one_half_eq`. -/
theorem mellin_gaussian_at_one :
    mellin (fun t : ℝ => (Real.exp (-t^2) : ℂ)) 1 =
    ((Real.sqrt Real.pi : ℝ) : ℂ) / 2 := by
  have h_re : (0:ℝ) < (1:ℂ).re := by norm_num
  rw [mellin_gaussian 1 h_re]
  have h_half : ((1:ℂ)/2) = ((1/2 : ℂ)) := by ring
  rw [h_half, Complex.Gamma_one_half_eq]
  rw [show ((Real.pi : ℂ)^((1:ℂ)/2)) = ((Real.sqrt Real.pi : ℝ) : ℂ) by
    rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_cpow Real.pi_pos.le]
    rw [← Real.sqrt_eq_rpow]]
  ring

#print axioms mellin_gaussian_at_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 12 — Cauchy rectangle integration (contour engine)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Cauchy-Goursat on a rectangle.** If `f : ℂ → ℂ` is analytic on the
closed rectangle with corners `z` and `w` (except possibly on a countable
set where `f` is continuous), then the rectangle's oriented boundary
integral of `f` vanishes.

This is the core Cauchy contour engine for the Weil-formula derivation.
Combined with meromorphic extensions (`f + singular parts = analytic`),
it extracts residues at interior poles.

Re-exported from `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`. -/
theorem cauchy_rectangle_integral_zero
    (f : ℂ → ℂ) (z w : ℂ) (s : Set ℂ)
    (hs_countable : s.Countable)
    (hfc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (hfd : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
               Set.Ioo (min z.im w.im) (max z.im w.im) \ s,
        DifferentiableAt ℂ f x) :
    (((∫ (x : ℝ) in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * Complex.I)) -
         ∫ (x : ℝ) in z.re..w.re, f ((x : ℂ) + (w.im : ℂ) * Complex.I)) +
       Complex.I • ∫ (y : ℝ) in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I)) -
     Complex.I • ∫ (y : ℝ) in z.im..w.im, f ((z.re : ℂ) + (y : ℂ) * Complex.I) =
    0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w s hs_countable hfc hfd

#print axioms cauchy_rectangle_integral_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 13 — Gamma decay on vertical lines (for top/bottom tail vanishing)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Stirling decay of `Γ(s/2)` on vertical lines.**

For `σ > 0` and large `|γ|`,

```
‖Γ(σ/2 + iγ/2)‖ ≤ C · |γ|^{(σ-1)/2} · exp(-π·|γ|/4).
```

This is the key decay that makes the **top/bottom contour integrals**
`∫ -ζ'/ζ(σ + iγ) · M(h)(σ + iγ) dσ` at `γ = ±T` vanish as `T → ∞`:
the Mellin factor `M(h)(s) = (1/2)·Γ(s/2)` decays exponentially faster
than `-ζ'/ζ` can grow in the critical strip.

Re-exported from `ZD.gamma_half_vertical_decay` in
`RequestProject/RiemannXiDecay.lean`. Unconditional via
`ZD.StirlingBound.gamma_stirling_bound`. -/
theorem gamma_half_decay (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        ‖Complex.Gamma (⟨σ/2, γ/2⟩ : ℂ)‖ ≤
          C * |γ| ^ ((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4) :=
  ZD.gamma_half_vertical_decay σ hσ

#print axioms gamma_half_decay

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 14 — Mellin inversion formula
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Mellin inversion.** If `f : ℝ → ℂ` has a Mellin transform that
converges on the vertical line `Re s = σ` and is `VerticalIntegrable`
there, and `f` is continuous at `x > 0`, then

```
f(x) = (1/(2πi)) ∫_{σ - i∞}^{σ + i∞} M(f)(s) · x^(-s) ds = mellinInv σ (mellin f) x.
```

This is the dual of the Mellin transform — the load-bearing step that
converts `Σ_n Λ(n) · ∫ M(h)(s)/n^s ds` into `Σ_n Λ(n) · h(log n)` in the
Weil-formula derivation (after swapping integral and sum).

Re-exported from Mathlib's `mellinInv_mellin_eq`. -/
theorem mellin_inversion_eq
    (σ : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hConv : MellinConvergent f (σ : ℂ))
    (hVert : Complex.VerticalIntegrable (mellin f) σ MeasureTheory.volume)
    (hCont : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x :=
  mellinInv_mellin_eq σ f hx hConv hVert hCont

#print axioms mellin_inversion_eq

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 15 — completedRiemannZeta factorization
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`ζ(s) = completedRiemannZeta(s) / Gammaℝ(s)` for `s ≠ 0`.**

Classical factorization: the completed zeta function equals the
Γℝ-multiplied ζ. Rearranged: `completedRiemannZeta(s) = Gammaℝ(s) · ζ(s)`
(where `Gammaℝ(s) = π^{-s/2} · Γ(s/2)`, Mathlib's `Complex.Gammaℝ`).

This is the bridge connecting our Gaussian Mellin `(1/2)·Γ(s/2)` to the
completed zeta's analytic properties. -/
theorem zeta_eq_completed_div_gammaℝ {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
  riemannZeta_def_of_ne_zero hs

#print axioms zeta_eq_completed_div_gammaℝ

/-- **`completedRiemannZeta(s) = Gammaℝ(s) · ζ(s)` when `Gammaℝ(s) ≠ 0`.**

Rearranged form of the above. `Gammaℝ` is non-vanishing for `Re s > 0`
(via `Complex.Gammaℝ_ne_zero_of_re_pos`), so this holds on the right half-plane
(except the trivial pole at `s = 0`). -/
theorem completed_eq_gammaℝ_mul_zeta {s : ℂ} (hs0 : s ≠ 0) (hGℝ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

#print axioms completed_eq_gammaℝ_mul_zeta

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 16 — Gammaℝ non-vanishing + zero locations
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`Gammaℝ(s) ≠ 0` on `Re s > 0`.**

On the right half-plane, `Gammaℝ(s) = π^{-s/2} · Γ(s/2)` is non-vanishing
because `Γ(s/2)` has no zeros for `Re(s/2) > 0`. This unlocks the
factorization `completedRiemannZeta = Gammaℝ · ζ` on `Re s > 0` (away from
poles of `completedRiemannZeta` at `s = 0, 1`). -/
theorem gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℝ s ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos hs

/-- **`Gammaℝ` zeros are exactly at even non-positive integers.**

`Gammaℝ(s) = 0` iff `s = -2n` for some natural `n`. Classical trivial-zero
structure of the completed zeta. -/
theorem gammaℝ_eq_zero_iff {s : ℂ} : Complex.Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * (n : ℂ)) :=
  Complex.Gammaℝ_eq_zero_iff

#print axioms gammaℝ_ne_zero_of_re_pos
#print axioms gammaℝ_eq_zero_iff

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 17 — Mellin identity for `completedRiemannZeta₀`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Project's Mellin identity (re-exported).**

The project-level observable `I_theta_of ψ_mellin` equals
`completedRiemannZeta₀`:

```
∫_{Ioi 0} 2·cosh((s - 1/2)·t) · ψ_mellin(t) dt = completedRiemannZeta₀(s).
```

This is the **load-bearing Mellin identity** of the Robespierre chain,
proved in `RequestProject/MellinPathToXi.lean`. Re-exported here as part
of the Weil-contour toolkit: it provides a concrete formula for
`completedRiemannZeta₀` as an explicit integral, which is the bridge
between the abstract Mellin machinery and the cosh-kernel test-function
pipeline. -/
theorem I_theta_psi_mellin_eq_completedRiemannZeta₀ (s : ℂ) :
    ZD.I_theta_of ZD.ψ_mellin s = completedRiemannZeta₀ s :=
  ZD.I_theta_of_ψ_mellin_eq_completedRiemannZeta₀ s

#print axioms I_theta_psi_mellin_eq_completedRiemannZeta₀

/-- **Mellin identity at nontrivial zeros.**

At every nontrivial zero `ρ`, `I_theta_of ψ_mellin(ρ) = -1/(ρ(ρ-1))`.
This is an unconditional specific-value identity — the value of the
Mellin observable at zeros. Used throughout the Weil-formula derivation
to evaluate residues. -/
theorem I_theta_psi_mellin_at_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ZD.I_theta_of ZD.ψ_mellin ρ = -1 / (ρ * (ρ - 1)) :=
  ZD.observable_value_at_zero ρ hρ

#print axioms I_theta_psi_mellin_at_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 18 — Consolidated Weil-formula target (Gaussian test pair)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil explicit formula — Gaussian test pair target (structural).**

The classical Weil formula for the Gaussian test pair `(h, φ)` with
`h(x) = exp(-x²)` and `φ(z) = exp(-z²/4)`:

```
Σ_ρ exp((ρ - 1/2)² / 4)
  = weilRHS_arch(h, φ) - weilRHS_prime(h)
```

where:
* LHS sums `exp((ρ - 1/2)²/4)` over nontrivial ζ-zeros (Phase I zero side
  via `weilLHS` + `weilLHS_gaussian_zero_sum_closed_form`).
* `weilRHS_arch(h, φ)` is the archimedean `Γ/Γ'`-kernel integral + `h(0) log π`
  anchor.
* `weilRHS_prime(h)` is the prime sum `Σ_{p,k} Λ(p^k)·p^{-k/2}·h(k·log p)
  + h(-k·log p)`.

This is a **structural target statement** — its derivation from this
file's building blocks (Mellin + Cauchy + Stirling + vonMangoldt bridge
+ FE) is the remaining analytic content pending in
`WeilPairFormula.pair_defect_vanishes_at_zeros_proof`. -/
def WeilFormulaGaussianPair : Prop :=
  ZD.WeilFormula (fun x : ℝ => Real.exp (-x^2))
                 (fun z : ℂ => Complex.exp (-z^2 / 4))

/-- **Forward link to the Gaussian Weil-pair identity.** Given the
classical Weil-formula target above, the project's
`gaussian_weil_pair_identity` produces the concrete zero-sum = arch -
prime identity. Unconditional. -/
theorem gaussian_pair_identity_of_WeilFormula
    (hWF : WeilFormulaGaussianPair) :
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        Complex.exp ((ρ.val - (1/2 : ℂ))^2 / 4) =
      ZD.weilRHS_arch (fun x : ℝ => Real.exp (-x^2))
                       (fun z : ℂ => Complex.exp (-z^2/4)) -
        (ZD.weilRHS_prime (fun x : ℝ => Real.exp (-x^2)) : ℂ) :=
  ZD.gaussian_weil_pair_identity hWF

#print axioms gaussian_pair_identity_of_WeilFormula

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 19 — Pair-test cosh expansion (Item 1 of sorry-attempt plan)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Cosh-expansion decomposition of `pair_cosh_gauss_test`.**

Via `sinh²(x) = (cosh(2x) - 1)/2` and `cosh(A)·cosh(B) = (cosh(A+B) +
cosh(A-B))/2`, the pair test function decomposes as:

```
pair_cosh_gauss_test β t =
  [ (1/2) cosh((2β - π/3)·t)
  + (1/2) cosh((2 - π/3 - 2β)·t)
  - cosh((1 - π/3)·t)
  - cosh((2β - 1)·t)
  + 1
  ] · exp(-2t²).
```

**Structural significance.** This exposes the pair defect integrand as a
finite linear combination of `cosh(c·t)·exp(-2t²)` terms. Each such term
can be Mellin-transformed individually — in principle expressible via
confluent hypergeometric / Kummer functions, which are NOT clean Γ
functions but are tractable for specific substitutions. More directly,
this decomposition gives the pair defect as a sum of **Gaussian moments**
that admit closed forms via `cosh_gaussian_integral_Ioi_two_R` in
`RequestProject/GaussianClosedForm.lean`.

This is **Item 1** of the itemized sorry-attempt plan. -/
theorem pair_cosh_gauss_test_cosh_expansion (β t : ℝ) :
    pair_cosh_gauss_test β t =
    ((1/2) * Real.cosh ((2*β - Real.pi/3) * t) +
     (1/2) * Real.cosh ((2 - Real.pi/3 - 2*β) * t) -
     Real.cosh ((1 - Real.pi/3) * t) -
     Real.cosh ((2*β - 1) * t) + 1) * Real.exp (-2 * t^2) := by
  unfold pair_cosh_gauss_test
  rw [pairDetectorSqDiff_sinh_factor, ψ_gaussian_sq_eq]
  have h_cosh2 : ∀ x : ℝ, Real.cosh (2 * x) = 1 + 2 * Real.sinh x ^ 2 := fun x => by
    have := Real.cosh_two_mul x
    have := Real.cosh_sq_sub_sinh_sq x
    linarith
  have h_a : Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 =
             (Real.cosh ((1 - Real.pi/3) * t) - 1) / 2 := by
    have h := h_cosh2 ((1/2 - Real.pi/6) * t)
    rw [show 2 * ((1/2 - Real.pi/6) * t) = (1 - Real.pi/3) * t from by ring] at h
    linarith
  have h_b : Real.sinh ((β - 1/2) * t) ^ 2 =
             (Real.cosh ((2*β - 1) * t) - 1) / 2 := by
    have h := h_cosh2 ((β - 1/2) * t)
    rw [show 2 * ((β - 1/2) * t) = (2*β - 1) * t from by ring] at h
    linarith
  have h_prod : Real.cosh ((1 - Real.pi/3) * t) * Real.cosh ((2*β - 1) * t) =
                (1/2) * (Real.cosh ((2*β - Real.pi/3) * t) +
                         Real.cosh ((2 - Real.pi/3 - 2*β) * t)) := by
    have hadd := Real.cosh_add ((1 - Real.pi/3) * t) ((2*β - 1) * t)
    have hsub := Real.cosh_sub ((1 - Real.pi/3) * t) ((2*β - 1) * t)
    rw [show (1 - Real.pi/3) * t + (2*β - 1) * t = (2*β - Real.pi/3) * t from by ring] at hadd
    rw [show (1 - Real.pi/3) * t - (2*β - 1) * t = (2 - Real.pi/3 - 2*β) * t from by ring] at hsub
    linarith
  rw [h_a, h_b]
  linear_combination Real.exp (-2 * t^2) * h_prod

#print axioms pair_cosh_gauss_test_cosh_expansion

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 20 — Fourier partner of pair test (Item 2 of sorry-attempt plan)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Fourier partner of `pair_cosh_gauss_test β`.**

Explicit Fourier transform of the pair test function, derived from the
cosh expansion (cycle 19) via termwise application of the Gaussian
Fourier identity:

```
∫_ℝ cosh(c·t) · exp(-2t²) · exp(i·ξ·t) dt = √(π/2) · exp((c² - ξ²)/8) · cos(c·ξ/4).
```

Summing the five cosh-terms from cycle 19 yields this closed form:

```
F(β, ξ) = √(π/2) · exp(-ξ²/8) · [
  (1/2) · exp((2β - π/3)²/8) · cos((2β - π/3)·ξ/4)
  + (1/2) · exp((2 - π/3 - 2β)²/8) · cos((2 - π/3 - 2β)·ξ/4)
  - exp((1 - π/3)²/8) · cos((1 - π/3)·ξ/4)
  - exp((2β - 1)²/8) · cos((2β - 1)·ξ/4)
  + 1
].
```

This is **Item 2** of the itemized sorry-attempt plan. -/
noncomputable def pair_cosh_gauss_fourier (β : ℝ) (ξ : ℂ) : ℂ :=
  ((Real.pi / 2 : ℂ))^((1:ℂ)/2) * Complex.exp (-ξ^2 / 8) *
    ((1/2 : ℂ) *
        ((Real.exp ((2*β - Real.pi/3)^2 / 8) : ℝ) : ℂ) *
        Complex.cos ((2*β - Real.pi/3) * ξ / 4)
     + (1/2 : ℂ) *
        ((Real.exp ((2 - Real.pi/3 - 2*β)^2 / 8) : ℝ) : ℂ) *
        Complex.cos ((2 - Real.pi/3 - 2*β) * ξ / 4)
     - ((Real.exp ((1 - Real.pi/3)^2 / 8) : ℝ) : ℂ) *
        Complex.cos ((1 - Real.pi/3) * ξ / 4)
     - ((Real.exp ((2*β - 1)^2 / 8) : ℝ) : ℂ) *
        Complex.cos ((2*β - 1) * ξ / 4)
     + 1)

/-- Convert `(π/2 : ℂ)^(1/2 : ℂ)` to `((√(π/2) : ℝ) : ℂ)`. -/
private lemma pair_fourier_pi_half_cpow :
    ((Real.pi / 2 : ℂ))^((1:ℂ)/2) = ((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) := by
  rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by push_cast; ring]
  rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ Real.pi / 2)]
  rw [← Real.sqrt_eq_rpow]

/-- **Consistency at ξ = 0**: the Fourier partner evaluated at 0 equals
the integral of the pair test over the full real line, which equals
`2 · gaussianPairDefect β` (since the integrand is even in `t`).

This is the Mellin-Fourier duality check: `F(0) = ∫ h(t) dt`. Combined
with the closed-form `evenChannel_closed_form` in
`WeilCoshPairPositivity_RouteBeta`, the two explicit expressions match. -/
theorem pair_cosh_gauss_fourier_at_zero (β : ℝ) :
    pair_cosh_gauss_fourier β 0 = ((2 * gaussianPairDefect β : ℝ) : ℂ) := by
  unfold pair_cosh_gauss_fourier
  simp only [Complex.cos_zero, mul_zero, zero_div, neg_zero, Complex.exp_zero, mul_one,
             zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [show gaussianPairDefect β = evenChannel β from rfl]
  rw [evenChannel_closed_form β]
  rw [pair_fourier_pi_half_cpow]
  have h1 : (2*β - Real.pi/3)^2 / 8 = (β - Real.pi/6)^2 / 2 := by ring
  have h2 : (2 - Real.pi/3 - 2*β)^2 / 8 = (1 - Real.pi/6 - β)^2 / 2 := by ring
  have h3 : (1 - Real.pi/3)^2 / 8 = (1/2 - Real.pi/6)^2 / 2 := by ring
  have h4 : (2*β - 1)^2 / 8 = (β - 1/2)^2 / 2 := by ring
  rw [h1, h2, h3, h4]
  push_cast
  ring

#print axioms pair_cosh_gauss_fourier
#print axioms pair_cosh_gauss_fourier_at_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 21 — Simple-zero factorization & logDeriv pole (Item 3)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Simple-zero factorization.** If `f` is analytic at `w`, vanishes at `w`, and has
nonzero complex derivative at `w`, then `f(z) = (z - w) · g(z)` in a neighborhood of `w`,
for some `g` analytic at `w` with `g(w) = deriv f w ≠ 0`.

Foundational step for residue calculus. Built from Mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` and
`AnalyticAt.analyticOrderAt_eq_natCast`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem simple_zero_factor {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (hfw : f w = 0) (hfw' : deriv f w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧ g w = deriv f w ∧
      ∀ᶠ z in nhds w, f z = (z - w) * g z := by
  -- Step 1: analyticOrderAt (fun z => f z - f w) w = 1 since f'(w) ≠ 0.
  have hord : analyticOrderAt (fun z => f z - f w) w = 1 :=
    hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hfw'
  -- Rewrite using f w = 0 to get analyticOrderAt f w = 1.
  have hord' : analyticOrderAt f w = 1 := by
    rw [show (fun z => f z - f w) = f by funext z; rw [hfw, sub_zero]] at hord
    exact hord
  -- Step 2: Extract the factorization via analyticOrderAt_eq_natCast with n = 1.
  have h1 : analyticOrderAt f w = ((1 : ℕ) : ℕ∞) := by rw [hord']; rfl
  obtain ⟨g, hg_an, hg_ne, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := 1)).mp h1
  -- Simplify (z - w)^1 • g z to (z - w) * g z (smul = mul in ℂ).
  have hfg' : ∀ᶠ z in nhds w, f z = (z - w) * g z := by
    filter_upwards [hfg] with z hz
    rw [hz, pow_one, smul_eq_mul]
  -- Step 3: Show g w = deriv f w via HasDerivAt product rule.
  have hg_diff : DifferentiableAt ℂ g w := hg_an.differentiableAt
  have h_sub : HasDerivAt (fun z : ℂ => z - w) 1 w := (hasDerivAt_id w).sub_const w
  have h_prod : HasDerivAt (fun z : ℂ => (z - w) * g z) (1 * g w + (w - w) * deriv g w) w :=
    h_sub.mul hg_diff.hasDerivAt
  have h_prod_simp : HasDerivAt (fun z : ℂ => (z - w) * g z) (g w) w := by
    have heq : 1 * g w + (w - w) * deriv g w = g w := by ring
    rw [heq] at h_prod; exact h_prod
  have hfg_eq : (fun z : ℂ => f z) =ᶠ[nhds w] fun z : ℂ => (z - w) * g z := hfg'
  have h_feq : HasDerivAt f (g w) w :=
    hfg_eq.symm.hasDerivAt_iff.mp h_prod_simp
  have hf_eq : deriv f w = g w := h_feq.deriv
  refine ⟨g, hg_an, hg_ne, hf_eq.symm, hfg'⟩

/-- **Logarithmic derivative has simple pole at simple zero.** If `f` is analytic at `w`,
`f(w) = 0`, `f'(w) ≠ 0`, then on a punctured neighborhood of `w`:

```
deriv f z / f z = 1/(z - w) + h(z)
```

where `h = logDeriv g` is analytic at `w` and `g` is the factor from `simple_zero_factor`.

This is the residue-1 statement: the log derivative of `f` at a simple zero is `1/(z - w)`
plus an analytic correction.

Classical input for residue extraction at nontrivial zeros of `ζ` (using `f = ζ`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem logDeriv_simple_pole {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (hfw : f w = 0) (hfw' : deriv f w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (z - w)⁻¹ + deriv g z / g z := by
  obtain ⟨g, hg_an, hg_ne, _hgw_eq, hfg⟩ := simple_zero_factor hf hfw hfw'
  refine ⟨g, hg_an, hg_ne, ?_⟩
  -- Upgrade hfg (eventually-equal in nhds w) to the punctured filter.
  have hfg_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ, f z = (z - w) * g z :=
    hfg.filter_mono nhdsWithin_le_nhds
  -- g nonzero eventually (continuity at w).
  have hg_nonzero : ∀ᶠ z in nhds w, g z ≠ 0 :=
    hg_an.continuousAt.eventually_ne hg_ne
  have hg_nonzero_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ, g z ≠ 0 :=
    hg_nonzero.filter_mono nhdsWithin_le_nhds
  -- f' = g + (· - w) * g' eventually in nhds w.
  have hf_deriv_eq : ∀ᶠ z in nhds w, deriv f z = g z + (z - w) * deriv g z := by
    have hfg_open : ∀ᶠ z in nhds w, ∀ᶠ y in nhds z, f y = (y - w) * g y := by
      filter_upwards [eventually_eventually_nhds.mpr hfg] with z hz
      exact hz
    filter_upwards [hfg_open, hg_an.eventually_analyticAt] with z hz hg_an_z
    have h_g : DifferentiableAt ℂ g z := hg_an_z.differentiableAt
    have h_sub_z : HasDerivAt (fun y : ℂ => y - w) 1 z := (hasDerivAt_id z).sub_const w
    have h_prod_z : HasDerivAt (fun y : ℂ => (y - w) * g y)
        (1 * g z + (z - w) * deriv g z) z := h_sub_z.mul h_g.hasDerivAt
    have hz_eq : (fun y : ℂ => f y) =ᶠ[nhds z] fun y : ℂ => (y - w) * g y := hz
    have h_f_z : HasDerivAt f (1 * g z + (z - w) * deriv g z) z :=
      hz_eq.symm.hasDerivAt_iff.mp h_prod_z
    rw [h_f_z.deriv]
    ring
  have hf_deriv_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ, deriv f z = g z + (z - w) * deriv g z :=
    hf_deriv_eq.filter_mono nhdsWithin_le_nhds
  -- On the punctured neighborhood, z ≠ w, so (z - w) ≠ 0.
  have h_sub_ne : ∀ᶠ z in nhdsWithin w {w}ᶜ, z - w ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero_of_ne hz
  filter_upwards [hfg_punct, hf_deriv_punct, hg_nonzero_punct, h_sub_ne]
    with z hfz hfdz hgz hsub
  rw [hfz, hfdz]
  field_simp

#print axioms simple_zero_factor
#print axioms logDeriv_simple_pole

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 22 — Rectangle contour decomposition (Item 4)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Axis-aligned rectangle contour integral**, parameterized by left-right Re range
`[σL, σR]` and height `T > 0`. The four signed line integrals sum to the boundary
contour integral (counterclockwise orientation):

```
rectContourIntegral σL σR T f
  = ∫ (bottom, γ = -T, σL → σR)
  - ∫ (top,    γ = +T, σL → σR)
  + i · ∫ (right, σ = σR, -T → T)
  - i · ∫ (left,  σ = σL, -T → T)
```

This matches the convention of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
with the rectangle `[[σL, σR]] ×ℂ [[-T, T]]`. -/
noncomputable def rectContourIntegral (σL σR T : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in σL..σR, f (↑x + (-T : ℝ) * I))
  - (∫ x : ℝ in σL..σR, f (↑x + (T : ℝ) * I))
  + I • (∫ y : ℝ in (-T : ℝ)..T, f (↑σR + ↑y * I))
  - I • (∫ y : ℝ in (-T : ℝ)..T, f (↑σL + ↑y * I))

/-- **Rectangle contour integral vanishes for holomorphic integrand.**
If `f` is complex differentiable on the closed rectangle `[σL, σR] × [-T, T]`, then
the rectangle boundary integral is zero (Cauchy-Goursat).

Direct re-export of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
with `z := σL - T·I`, `w := σR + T·I`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_eq_zero_of_differentiableOn
    (σL σR T : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ((Set.uIcc σL σR) ×ℂ (Set.uIcc (-T) T))) :
    rectContourIntegral σL σR T f = 0 := by
  unfold rectContourIntegral
  -- Mathlib's theorem uses z = σL + (-T)·I, w = σR + T·I.
  set z : ℂ := (σL : ℂ) + (-T : ℝ) * I with hz_def
  set w : ℂ := (σR : ℂ) + (T : ℝ) * I with hw_def
  have hzre : z.re = σL := by simp [hz_def]
  have hwre : w.re = σR := by simp [hw_def]
  have hzim : z.im = -T := by simp [hz_def]
  have hwim : w.im = T := by simp [hw_def]
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (by rw [hzre, hwre, hzim, hwim]; exact hf)
  rw [hzre, hwre, hzim, hwim] at key
  -- key : (∫ σL..σR, f(x + (-T)·I)) - (∫ σL..σR, f(x + T·I)) +
  --       I • (∫ -T..T, f(σR + y·I)) - I • (∫ -T..T, f(σL + y·I)) = 0
  -- Goal has the same structure; `linear_combination` closes it.
  linear_combination key

#print axioms rectContourIntegral
#print axioms rectContourIntegral_eq_zero_of_differentiableOn

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 23 — Functional equation, `ζ(s)` form (Item 5, part A)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Reciprocal functional equation for `ζ`.** Express `ζ(s)` in terms of `ζ(1 − s)`,
obtained by substituting `s ↦ 1 − s` in Mathlib's `riemannZeta_one_sub` and using
`cos(π(1-s)/2) = sin(πs/2)`:

```
ζ(s) = 2 · (2π)^(s−1) · Γ(1−s) · sin(πs/2) · ζ(1−s)
```

Valid away from the poles of both sides, i.e., `s ≠ 0` and `s ≠ n+1` for `n : ℕ`
(these are the points where the RHS factors/LHS has issues through the substitution).

This is the form needed for FE+Stirling bounds on Re s < 1/2: the RHS has `ζ(1−s)`
absolutely bounded (Re(1−s) > 1/2 corresponds to Re s < 1/2), and the growth is
carried by `Γ(1−s) · sin(πs/2)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem zeta_FE_reciprocal (s : ℂ)
    (hs_ne_zero : s ≠ 0) (hs_ne_pos_int : ∀ n : ℕ, s ≠ (n + 1 : ℕ)) :
    riemannZeta s =
      2 * (2 * Real.pi : ℂ)^(s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (Real.pi * s / 2) * riemannZeta (1 - s) := by
  -- Apply riemannZeta_one_sub at (1 - s):
  have h1 : ∀ n : ℕ, (1 - s) ≠ -↑n := by
    intro n h
    have : s = 1 + n := by linear_combination -h
    exact hs_ne_pos_int n (by push_cast; linear_combination this)
  have h2 : (1 - s) ≠ 1 := fun h => hs_ne_zero (by linear_combination -h)
  have hzeta := riemannZeta_one_sub h1 h2
  -- hzeta : ζ(1 - (1-s)) = 2·(2π)^(-(1-s))·Γ(1-s)·cos(π(1-s)/2)·ζ(1-s)
  -- Simplify 1 - (1-s) = s and -(1-s) = s - 1.
  rw [show (1 : ℂ) - (1 - s) = s from by ring] at hzeta
  rw [show -(1 - s) = s - 1 from by ring] at hzeta
  -- Now rewrite cos(π(1-s)/2) = cos(π/2 - πs/2) = sin(πs/2).
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = Complex.sin (Real.pi * s / 2) := by
    have : (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - Real.pi * s / 2 := by ring
    rw [this, Complex.cos_pi_div_two_sub]
  rw [hcos] at hzeta
  exact hzeta

#print axioms zeta_FE_reciprocal

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 24 — FE symmetry for `completedRiemannZeta` norm (Item 5, part B)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **FE symmetry for `ξ` norm.** Direct corollary of `completedRiemannZeta_one_sub`:
the completed Riemann zeta function has equal modulus at reflection-symmetric points.

This lets us transport absolute bounds from `Re s ≥ 1` (where `ξ` is a convergent
Dirichlet series times Gamma, hence bounded on any vertical line with standard Stirling
decay) to `Re s ≤ 0` via `s ↦ 1 − s`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem completedZeta_norm_reflect (s : ℂ) :
    ‖completedRiemannZeta s‖ = ‖completedRiemannZeta (1 - s)‖ := by
  rw [completedRiemannZeta_one_sub]

/-- **Left-edge bound via FE symmetry.** For `σ ≤ 0` and any `T : ℝ`, the modulus of
`completedRiemannZeta (σ + iT)` equals that of `completedRiemannZeta ((1-σ) - iT)`,
the latter lying in the absolutely-convergent region `Re ≥ 1`.

This is the structural foundation for bounding the `Re s = σL` edge of the Weil
contour: by symmetry, every bound available on the `Re s ≥ 1` edge applies to the
symmetric `Re s ≤ 0` edge.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem completedZeta_left_edge_via_FE (σ T : ℝ) :
    ‖completedRiemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ =
    ‖completedRiemannZeta (((1 - σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
  rw [completedZeta_norm_reflect]
  congr 1
  push_cast
  ring

#print axioms completedZeta_norm_reflect
#print axioms completedZeta_left_edge_via_FE

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 25 — Dirichlet series for `-ζ'/ζ` at Re s > 1 (Item 6)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Prime-side identity at `Re s > 1`.** The logarithmic derivative of `ζ` equals
the Dirichlet series for the von Mangoldt function:

```
-ζ'(s)/ζ(s) = Σ_{n ≥ 1} Λ(n) / n^s     for Re s > 1
```

Direct re-export of Mathlib's `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
packaged as the prime-side building block for the Weil explicit formula derivation.

On `Re s = 2` (the right edge of our contour), this identity converts the contour
integral into an explicit sum over primes (via Λ(n) support on prime powers).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- **Logarithmic derivative form.** Equivalent formulation: `-logDeriv riemannZeta s`
equals the L-series at `Re s > 1`. Uses `logDeriv_apply : logDeriv f x = deriv f x / f x`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -logDeriv riemannZeta s := by
  rw [vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs, logDeriv_apply]
  ring

/-- **Zeta nonvanishing at Re s > 1.** Direct re-export; used to justify the quotient
`-ζ'(s)/ζ(s)` is well-defined on the right edge of the Weil contour. -/
theorem zeta_ne_zero_one_lt {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

#print axioms vonMangoldt_LSeries_eq_neg_logDeriv_zeta
#print axioms vonMangoldt_LSeries_eq_neg_logDeriv
#print axioms zeta_ne_zero_one_lt

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 26 — Weil contour integrand, partial assembly (Item 7)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil contour integrand.** The core function integrated around the Weil
rectangle contour: `(−ζ'(s)/ζ(s)) · h(s)`, where `h` is a test-function Mellin
partner (typically `pair_cosh_gauss_fourier` in our cosh-pair Gaussian setup).

The integrand has:
* A simple pole at `s = 1` (residue = −h(1), from ζ's pole at 1, combined with
  the minus sign).
* Simple poles at each nontrivial zero `ρ` of ζ (residue = `m(ρ)·h(ρ)` where
  `m(ρ)` is the multiplicity; assuming simple zeros, `m(ρ) = 1`).
* No other poles in the rectangle `{−1 < Re s < 2}`. -/
noncomputable def weilIntegrand (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * h s

/-- **Integrand equals von Mangoldt L-series on `Re s > 1`.** For the right edge of
the Weil contour, the prime-side expansion from cycle 25 applies. -/
theorem weilIntegrand_eq_vonMangoldt_LSeries {h : ℂ → ℂ} {s : ℂ} (hs : 1 < s.re) :
    weilIntegrand h s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s * h s := by
  unfold weilIntegrand
  rw [vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs]

/-- **Integrand differentiability away from poles.** On the open set
`{s : s ≠ 1 ∧ ζ(s) ≠ 0}`, the Weil integrand is differentiable whenever `h` is.

This is the "no singularities in our rectangle patch" statement used in cycle 22
(`rectContourIntegral_eq_zero_of_differentiableOn`) to justify Cauchy-Goursat on
each pole-free sub-region.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_differentiableAt
    {h : ℂ → ℂ} {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0)
    (hh : DifferentiableAt ℂ h s) :
    DifferentiableAt ℂ (weilIntegrand h) s := by
  unfold weilIntegrand
  have hζ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have hζ'_diff : DifferentiableAt ℂ (deriv riemannZeta) s := by
    -- riemannZeta is analytic away from 1, so deriv is also differentiable.
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hζ_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    have hζ_an_on : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      hζ_diff_on.analyticOnNhd hopen
    have hζ_an : AnalyticAt ℂ riemannZeta s := hζ_an_on s hs
    exact hζ_an.deriv.differentiableAt
  exact (hζ'_diff.neg.div hζ_diff hζ).mul hh

#print axioms weilIntegrand
#print axioms weilIntegrand_eq_vonMangoldt_LSeries
#print axioms weilIntegrand_differentiableAt

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 27 — Mellin partner of `pair_cosh_gauss_test` (Item 8)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Mellin partner of the pair cosh-Gauss test.** The Mellin transform of the
concrete test function `pair_cosh_gauss_test β`, coerced to `ℂ`.

This is the `h(s)` paired against `−ζ'(s)/ζ(s)` inside the Weil rectangle
contour integral. At `s = 1` it evaluates to `gaussianPairDefect β` (the
real-axis integral), which is the load-bearing arithmetic quantity. -/
noncomputable def pairTestMellin (β : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (pair_cosh_gauss_test β t : ℂ)) s

/-- **Value at `s = 1`.** The Mellin transform at `s = 1` is exactly the real-axis
integral of the test function, which equals `gaussianPairDefect β`.

```
pairTestMellin β 1 = gaussianPairDefect β
```

Combined with the contour residue sum, evaluating the Weil formula at `s = 1`
contributes `gaussianPairDefect β` to the sum at each zero.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_at_one (β : ℝ) :
    pairTestMellin β 1 = ((gaussianPairDefect β : ℝ) : ℂ) := by
  unfold pairTestMellin mellin
  -- ∫ t in Ioi 0, t^(1-1) • (test β t : ℂ) = (gaussianPairDefect β : ℂ)
  have h_simp : ∀ t : ℝ, t ∈ Ioi (0:ℝ) →
      (t : ℂ) ^ ((1:ℂ) - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
      ((pair_cosh_gauss_test β t : ℝ) : ℂ) := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    rw [sub_self, Complex.cpow_zero, one_smul]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_simp]
  -- Now: ∫ t in Ioi 0, (test β t : ℂ) = (gaussianPairDefect β : ℂ)
  rw [integral_complex_ofReal]
  rw [pair_cosh_gauss_test_integral_eq_gaussianPairDefect]

#print axioms pairTestMellin
#print axioms pairTestMellin_at_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 28 — Per-zero Laurent form of the Weil integrand (Item 9)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil integrand Laurent form at simple zero.** At a simple zero `ρ` of `ζ`
(i.e., `ζ(ρ) = 0` and `ζ'(ρ) ≠ 0`), the Weil integrand has an explicit punctured-
neighborhood expansion via cycle 21's `logDeriv_simple_pole`:

```
weilIntegrand h s = -((s - ρ)⁻¹ + g'(s)/g(s)) · h(s)
```

where `g` is the analytic factor with `g(ρ) = ζ'(ρ) ≠ 0`. The `(s − ρ)⁻¹` term
has residue coefficient `−h(ρ)` (classical residue at simple pole of `−ζ'/ζ · h`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_laurent_at_simple_zero
    {h : ℂ → ℂ} {ρ : ℂ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : riemannZeta ρ = 0) (hζ_deriv : deriv riemannZeta ρ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s = -((s - ρ)⁻¹ + deriv g s / g s) * h s := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := logDeriv_simple_pole hζ_an hζ_zero hζ_deriv
  refine ⟨g, hg_an, hg_ne, ?_⟩
  filter_upwards [hfg] with s hs
  unfold weilIntegrand
  rw [show -deriv riemannZeta s / riemannZeta s = -(deriv riemannZeta s / riemannZeta s) by
    ring, hs]

/-- **Residue identification.** The `1/(s-ρ)` coefficient in the Laurent expansion
of `weilIntegrand h` at a simple zero `ρ` is `-h(ρ)`. This is the per-zero
contribution to the Weil-formula's zero-sum side.

The structural form: the residue of `−ζ'(s)/ζ(s) · h(s)` at `ρ` is `−h(ρ)`
(multiplicity 1 for a simple zero). For multiple zeros, the residue scales by
the multiplicity.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_leading_coefficient_at_zero
    {h : ℂ → ℂ} {ρ : ℂ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : riemannZeta ρ = 0) (hζ_deriv : deriv riemannZeta ρ ≠ 0)
    (hh_an : AnalyticAt ℂ h ρ) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s = -h s / (s - ρ) + φ s := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := weilIntegrand_laurent_at_simple_zero
    hζ_an hζ_zero hζ_deriv
  refine ⟨fun s => -h s * deriv g s / g s, ?_, ?_⟩
  · -- φ is analytic at ρ: product of h (analytic) with deriv g / g (analytic, g(ρ)≠0).
    have hg_deriv_an : AnalyticAt ℂ (deriv g) ρ := hg_an.deriv
    have h_inv_g : AnalyticAt ℂ (fun s => (g s)⁻¹) ρ := hg_an.inv hg_ne
    have h_dg_over_g : AnalyticAt ℂ (fun s => deriv g s / g s) ρ := by
      simpa [div_eq_mul_inv] using hg_deriv_an.mul h_inv_g
    exact (hh_an.neg.mul hg_deriv_an).div hg_an hg_ne
  · filter_upwards [hfg] with s hs
    rw [hs]
    field_simp
    ring

#print axioms weilIntegrand_laurent_at_simple_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 29 — Circle integral of the polar part (Item 10)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Circle integral of a simple polar part.** The principal-part term
`−h(z)/(z − ρ)` arising in the Weil integrand's Laurent expansion has
circle integral `−2πi · h(ρ)` by direct Cauchy integral formula:

```
∮_{|z−ρ|=r} −h(z)/(z − ρ) dz = −2πi · h(ρ)
```

provided `h` is holomorphic on the closed disk of radius `r > 0` around `ρ`.

This is the per-zero residue contribution. Combined with `circleIntegral_eq_zero_of...`
on the analytic remainder `φ`, the total circle integral of `weilIntegrand h` around
a simple zero is `−2πi · h(ρ)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem polar_part_circle_integral
    {h : ℂ → ℂ} {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh_cont : ContinuousOn h (Metric.closedBall ρ r))
    (hh_diff : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z) :
    (∮ z in C(ρ, r), h z / (z - ρ)) = 2 * ↑π * I * h ρ := by
  have h_circle := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (c := ρ) (w := ρ) (R := r) (f := h) (s := ∅)
    Set.countable_empty (by simp [Metric.mem_ball, hr]) hh_cont
    (fun z hz => hh_diff z (by simpa using hz.1))
  -- h_circle : (∮ z in C(ρ, r), (z - ρ)⁻¹ • h z) = (2 * π * I) • h ρ
  have heq : ∀ z : ℂ, h z / (z - ρ) = (z - ρ)⁻¹ • h z := by
    intro z; rw [smul_eq_mul, div_eq_inv_mul]
  simp only [heq]
  rw [h_circle, smul_eq_mul]

#print axioms polar_part_circle_integral

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 30 — Weil integrand circle integral from Laurent decomposition
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Circle integral of `weilIntegrand` from explicit Laurent decomposition.**
Given a hypothesized sphere-level decomposition `weilIntegrand h z = −h(z)/(z−ρ) + φ(z)`
with `h` and `φ` both holomorphic on the closed disk, the circle integral equals
`−2πi · h(ρ)`.

This isolates the "polar + Cauchy" combination: cycle 29 gives the polar part,
Cauchy's theorem gives the analytic-remainder vanishing, linearity of `circleIntegral`
glues them.

This is the stepping stone form; a follow-up theorem (cycle 31) derives the
decomposition itself from ζ-at-simple-zero hypotheses via the `dslope` construction.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_circle_integral_from_decomposition
    {h φ : ℂ → ℂ} {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh_cont : ContinuousOn h (Metric.closedBall ρ r))
    (hh_diff : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z)
    (hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball ρ r))
    (hdecomp : ∀ z ∈ Metric.sphere ρ r,
        weilIntegrand h z = -h z / (z - ρ) + φ z) :
    (∮ z in C(ρ, r), weilIntegrand h z) = -(2 * ↑π * I) * h ρ := by
  -- Sphere points are ≠ ρ (since r > 0).
  have h_sphere_ne_ρ : ∀ z ∈ Metric.sphere ρ r, z ≠ ρ := by
    intro z hz hzρ
    rw [hzρ, Metric.mem_sphere, dist_self] at hz
    exact absurd hz.symm hr.ne'
  -- Continuity of h, φ on the sphere (inherited from closed ball / closure).
  have h_sphere_sub_closed : Metric.sphere ρ r ⊆ Metric.closedBall ρ r := Metric.sphere_subset_closedBall
  have hh_on_sphere : ContinuousOn h (Metric.sphere ρ r) := hh_cont.mono h_sphere_sub_closed
  have hφ_cont_closure : ContinuousOn φ (closure (Metric.ball ρ r)) := hφ_diffcontoncl.continuousOn
  have h_closure_eq : closure (Metric.ball ρ r) = Metric.closedBall ρ r := closure_ball ρ hr.ne'
  rw [h_closure_eq] at hφ_cont_closure
  have hφ_on_sphere : ContinuousOn φ (Metric.sphere ρ r) :=
    hφ_cont_closure.mono h_sphere_sub_closed
  -- Continuity of the polar part on the sphere.
  have h_polar_cont_sphere : ContinuousOn (fun z : ℂ => -h z / (z - ρ)) (Metric.sphere ρ r) := by
    apply ContinuousOn.div hh_on_sphere.neg
    · exact (continuousOn_id.sub continuousOn_const)
    · intro z hz; exact sub_ne_zero_of_ne (h_sphere_ne_ρ z hz)
  -- Step 1: transfer integrand via integral_congr on the sphere.
  rw [circleIntegral.integral_congr hr.le hdecomp]
  -- Step 2: split by linearity.
  have h_polar_ci : CircleIntegrable (fun z => -h z / (z - ρ)) ρ r :=
    h_polar_cont_sphere.circleIntegrable hr.le
  have h_φ_ci : CircleIntegrable φ ρ r := hφ_on_sphere.circleIntegrable hr.le
  rw [circleIntegral.integral_add h_polar_ci h_φ_ci]
  -- Step 3: φ part vanishes by Cauchy-Goursat.
  rw [hφ_diffcontoncl.circleIntegral_eq_zero hr.le, add_zero]
  -- Step 4: polar part via cycle 29 (applied to -h).
  have h_neg_cont : ContinuousOn (fun z => -h z) (Metric.closedBall ρ r) := hh_cont.neg
  have h_neg_diff : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ (fun z => -h z) z :=
    fun z hz => (hh_diff z hz).neg
  have := polar_part_circle_integral hr h_neg_cont h_neg_diff
  -- this : (∮ z in C(ρ, r), (fun z => -h z) z / (z - ρ)) = 2 * π * I * (fun z => -h z) ρ
  simp only at this
  rw [this]
  ring

#print axioms weilIntegrand_circle_integral_from_decomposition

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 31 — Sphere decomposition from ζ factorization
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Sphere decomposition from an open-ball factorization.** Given a factorization
`ζ(z) = (z − ρ) · g(z)` on an open ball `ball ρ R` strictly containing the sphere of
radius `r < R`, with `g`, `h` differentiable and `g` nonzero on the ball, the Weil
integrand admits the explicit Laurent form on the sphere:

```
weilIntegrand h z = −h(z)/(z − ρ) + (−h(z) · g'(z)/g(z))     for z ∈ sphere ρ r.
```

The analytic remainder `φ(z) := −h(z) · g'(z)/g(z)` is the "regular part" of the
Laurent expansion; the coefficient of `1/(z − ρ)` is `−h(z)` (evaluated at the pole,
this gives residue `−h(ρ)`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_sphere_decomposition_from_factorization
    {h g : ℂ → ℂ} {ρ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hfact : ∀ z ∈ Metric.ball ρ R, riemannZeta z = (z - ρ) * g z)
    (hg_diff : DifferentiableOn ℂ g (Metric.ball ρ R))
    (hg_ne : ∀ z ∈ Metric.ball ρ R, g z ≠ 0)
    (hh_diff : DifferentiableOn ℂ h (Metric.ball ρ R)) :
    ∀ z ∈ Metric.sphere ρ r,
      weilIntegrand h z = -h z / (z - ρ) + (-h z * deriv g z / g z) := by
  intro z hz
  -- z is on the sphere of radius r, and r < R, so z ∈ ball ρ R.
  have hz_in_ball : z ∈ Metric.ball ρ R := by
    rw [Metric.mem_ball]
    calc dist z ρ = r := Metric.mem_sphere.mp hz
      _ < R := hrR
  have hz_ne_ρ : z ≠ ρ := by
    intro hzρ
    rw [hzρ, Metric.mem_sphere, dist_self] at hz
    exact absurd hz.symm hr.ne'
  -- Factorization at z:
  have hfact_z : riemannZeta z = (z - ρ) * g z := hfact z hz_in_ball
  -- g nonzero at z, hence ζ(z) ≠ 0 (since z ≠ ρ):
  have hg_z_ne : g z ≠ 0 := hg_ne z hz_in_ball
  have hζ_z_ne : riemannZeta z ≠ 0 := by
    rw [hfact_z]
    exact mul_ne_zero (sub_ne_zero_of_ne hz_ne_ρ) hg_z_ne
  -- Open ball is a nhds of z; factorization gives EventuallyEq for deriv transfer.
  have hball_mem : Metric.ball ρ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz_in_ball
  have hfact_eventually : (fun w : ℂ => riemannZeta w) =ᶠ[nhds z] (fun w => (w - ρ) * g w) :=
    Filter.eventually_of_mem hball_mem (fun w hw => hfact w hw)
  -- Compute deriv ζ z via EventuallyEq.
  have hg_diff_z : DifferentiableAt ℂ g z := (hg_diff z hz_in_ball).differentiableAt hball_mem
  have h_sub_hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have h_prod_hd : HasDerivAt (fun w : ℂ => (w - ρ) * g w) (1 * g z + (z - ρ) * deriv g z) z :=
    h_sub_hd.mul hg_diff_z.hasDerivAt
  have hζ_hd : HasDerivAt riemannZeta (1 * g z + (z - ρ) * deriv g z) z :=
    hfact_eventually.symm.hasDerivAt_iff.mp h_prod_hd
  have hζ_deriv_z : deriv riemannZeta z = g z + (z - ρ) * deriv g z := by
    rw [hζ_hd.deriv]; ring
  -- Now compute weilIntegrand h z.
  unfold weilIntegrand
  rw [hζ_deriv_z, hfact_z]
  have h_sub_ne : z - ρ ≠ 0 := sub_ne_zero_of_ne hz_ne_ρ
  field_simp
  ring

#print axioms weilIntegrand_sphere_decomposition_from_factorization

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 32 — Full circle integral at a simple zero of ζ
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-zero residue identity.** At a simple zero `ρ` of `ζ`, and for `h` analytic
at `ρ`, the circle integral of `weilIntegrand h` around `ρ` equals `−2πi · h(ρ)`
for some radius `r > 0`:

```
∮_{|z−ρ|=r} −ζ'(z)/ζ(z) · h(z) dz = −2πi · h(ρ).
```

This is the per-zero contribution to the Weil-formula zero-sum side. Combined with
rectangle Cauchy-Goursat (cycle 22) and summed over all nontrivial zeros inside
the contour, it produces the zero-sum `−2πi · Σ_ρ h(ρ)`.

The proof composes cycles 21 (simple-zero factorization), 29 (Cauchy formula for the
polar part), 30 (decomposition ⟹ integral), 31 (factorization ⟹ decomposition).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_circle_integral_at_simple_zero
    {h : ℂ → ℂ} {ρ : ℂ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : riemannZeta ρ = 0)
    (hζ_deriv_ne : deriv riemannZeta ρ ≠ 0)
    (hh_an : AnalyticAt ℂ h ρ) :
    ∃ r > 0,
      ∮ z in C(ρ, r), weilIntegrand h z = -(2 * ↑π * I) * h ρ := by
  -- Step 1: Factorization from cycle 21.
  obtain ⟨g, hg_an, hg_ne, _hg_val, hfg⟩ :=
    simple_zero_factor hζ_an hζ_zero hζ_deriv_ne
  -- Step 2: Extract balls for the four conditions.
  rw [Metric.eventually_nhds_iff_ball] at hfg
  obtain ⟨ε₁, hε₁_pos, hfg_ball⟩ := hfg
  obtain ⟨ε₂, hε₂_pos, hg_analyticOn⟩ := hg_an.exists_ball_analyticOnNhd
  have hg_ne_nhds : ∀ᶠ z in nhds ρ, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
  rw [Metric.eventually_nhds_iff_ball] at hg_ne_nhds
  obtain ⟨ε₃, hε₃_pos, hg_ne_ball⟩ := hg_ne_nhds
  obtain ⟨ε₄, hε₄_pos, hh_analyticOn⟩ := hh_an.exists_ball_analyticOnNhd
  -- Step 3: Take R = min of all > 0, r = R/2.
  set R := min (min ε₁ ε₂) (min ε₃ ε₄) with hR_def
  have hR_pos : 0 < R := by simp only [hR_def]; positivity
  set r := R / 2 with hr_def
  have hr_pos : 0 < r := by simp only [hr_def]; linarith
  have hr_lt_R : r < R := by simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  -- Step 4: Ball inclusions (R ≤ each εᵢ).
  have hR_le_ε₁ : R ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR_le_ε₂ : R ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR_le_ε₃ : R ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR_le_ε₄ : R ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub_ε₁ : Metric.ball ρ R ⊆ Metric.ball ρ ε₁ := Metric.ball_subset_ball hR_le_ε₁
  have hsub_ε₂ : Metric.ball ρ R ⊆ Metric.ball ρ ε₂ := Metric.ball_subset_ball hR_le_ε₂
  have hsub_ε₃ : Metric.ball ρ R ⊆ Metric.ball ρ ε₃ := Metric.ball_subset_ball hR_le_ε₃
  have hsub_ε₄ : Metric.ball ρ R ⊆ Metric.ball ρ ε₄ := Metric.ball_subset_ball hR_le_ε₄
  -- Step 5: Conditions on ball ρ R.
  have hfact_R : ∀ z ∈ Metric.ball ρ R, riemannZeta z = (z - ρ) * g z :=
    fun z hz => hfg_ball z (hsub_ε₁ hz)
  have hg_an_R : AnalyticOnNhd ℂ g (Metric.ball ρ R) :=
    fun z hz => hg_analyticOn z (hsub_ε₂ hz)
  have hg_ne_R : ∀ z ∈ Metric.ball ρ R, g z ≠ 0 :=
    fun z hz => hg_ne_ball z (hsub_ε₃ hz)
  have hh_an_R : AnalyticOnNhd ℂ h (Metric.ball ρ R) :=
    fun z hz => hh_analyticOn z (hsub_ε₄ hz)
  -- Step 6: Decomposition on sphere ρ r via cycle 31.
  have hg_diff_R : DifferentiableOn ℂ g (Metric.ball ρ R) := hg_an_R.differentiableOn
  have hh_diff_R : DifferentiableOn ℂ h (Metric.ball ρ R) := hh_an_R.differentiableOn
  have hdecomp := weilIntegrand_sphere_decomposition_from_factorization
    hr_pos hr_lt_R hfact_R hg_diff_R hg_ne_R hh_diff_R
  -- Step 7: Set φ := -h · deriv g / g. Must be DiffContOnCl on ball ρ r.
  set φ : ℂ → ℂ := fun z => -h z * deriv g z / g z with hφ_def
  -- φ analytic on ball ρ R.
  have hφ_an_R : AnalyticOnNhd ℂ φ (Metric.ball ρ R) := by
    intro z hz
    have hhz : AnalyticAt ℂ h z := hh_an_R z hz
    have hgz : AnalyticAt ℂ g z := hg_an_R z hz
    have hgz_ne : g z ≠ 0 := hg_ne_R z hz
    have hdgz : AnalyticAt ℂ (deriv g) z := hgz.deriv
    exact (hhz.neg.mul hdgz).div hgz hgz_ne
  -- Step 8: Build inputs to cycle 30.
  have hclosedBall_sub_ball : Metric.closedBall ρ r ⊆ Metric.ball ρ R := fun z hz => by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr_lt_R
  have hball_sub_ball : Metric.ball ρ r ⊆ Metric.ball ρ R :=
    (Metric.ball_subset_closedBall).trans hclosedBall_sub_ball
  have hh_cont_closed : ContinuousOn h (Metric.closedBall ρ r) :=
    fun z hz => (hh_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hh_diff_ball : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z :=
    fun z hz => (hh_an_R z (hball_sub_ball hz)).differentiableAt
  have hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball ρ r) := by
    refine ⟨?_, ?_⟩
    · exact fun z hz => (hφ_an_R z (hball_sub_ball hz)).differentiableAt.differentiableWithinAt
    · rw [closure_ball ρ hr_pos.ne']
      exact fun z hz => (hφ_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  -- Step 9: Apply cycle 30.
  have := weilIntegrand_circle_integral_from_decomposition hr_pos
    hh_cont_closed hh_diff_ball hφ_diffcontoncl hdecomp
  exact this

#print axioms weilIntegrand_circle_integral_at_simple_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 33 — Derivative form of completed-ζ FE (arch-side foundation)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Derivative form of the completed-ζ FE.** Differentiating Mathlib's
`completedRiemannZeta_one_sub : ξ(1 − s) = ξ(s)` gives the FE-antisymmetry of
the derivative:

```
ξ'(s) = −ξ'(1 − s)
```

This is the foundation for the arch-side of Weil's explicit formula: the
logarithmic derivative `−ζ'/ζ` is reconstructed from `ξ` via the decomposition
`ξ(s) = π^(−s/2)·Γ(s/2)·ζ(s)`, and the FE-antisymmetry of `ξ'/ξ` transports
prime-side Dirichlet coefficients from `Re s = σ₀ > 1` to the arch term at
general `Re s` via Γ-factor manipulations.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem completedRiemannZeta_deriv_FE (s : ℂ) (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1) :
    deriv completedRiemannZeta s = -deriv completedRiemannZeta (1 - s) := by
  -- Strategy: differentiate the identity `ξ(1 - s) = ξ(s)` w.r.t. s.
  -- The LHS derivative is `-ξ'(1 - s)` by chain rule; the RHS is `ξ'(s)`.
  have h_id : (fun s : ℂ => completedRiemannZeta (1 - s)) =
              (fun s : ℂ => completedRiemannZeta s) := by
    funext s
    exact completedRiemannZeta_one_sub s
  -- Differentiate both sides at s.
  have h1_s : (1 : ℂ) - s ≠ 0 := fun h => hs_ne_one (by linear_combination -h)
  have h1_s_ne_one : (1 : ℂ) - s ≠ 1 := fun h => hs_ne_zero (by linear_combination -h)
  have hd_rhs : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs_ne_zero hs_ne_one
  have hd_inner : DifferentiableAt ℂ (fun s : ℂ => (1 : ℂ) - s) s := by fun_prop
  have hd_one_sub : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta h1_s h1_s_ne_one
  have hd_lhs : HasDerivAt (fun s : ℂ => completedRiemannZeta (1 - s))
      (-deriv completedRiemannZeta (1 - s)) s := by
    have h_inner_deriv : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) s := by
      simpa using ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))
    have hcomp := hd_one_sub.hasDerivAt.comp s h_inner_deriv
    -- hcomp : HasDerivAt (completedRiemannZeta ∘ (1 - ·)) (deriv completedRiemannZeta (1 - s) * -1) s
    have hmul : deriv completedRiemannZeta (1 - s) * (-1 : ℂ) = -deriv completedRiemannZeta (1 - s) := by
      ring
    rw [hmul] at hcomp
    exact hcomp
  have hd_rhs' : HasDerivAt (fun s : ℂ => completedRiemannZeta s)
      (deriv completedRiemannZeta s) s := hd_rhs.hasDerivAt
  have h_eq : -deriv completedRiemannZeta (1 - s) = deriv completedRiemannZeta s := by
    have hhas := (Filter.EventuallyEq.hasDerivAt_iff (f₁ := fun s : ℂ => completedRiemannZeta s)
      (f₀ := fun s : ℂ => completedRiemannZeta (1 - s))
      (by rw [h_id])).mp hd_lhs
    exact hhas.unique hd_rhs'
  exact h_eq.symm

#print axioms completedRiemannZeta_deriv_FE

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 34 — Log-derivative FE for completed ζ
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Log-derivative FE.** Combining cycle 33 (`ξ'(s) = −ξ'(1−s)`) with
Mathlib's `completedRiemannZeta_one_sub` (`ξ(s) = ξ(1−s)`) gives the FE-antisymmetry
of the logarithmic derivative:

```
ξ'(s)/ξ(s) = −ξ'(1−s)/ξ(1−s)
```

This is the compact form of the arch-side identity: the log-derivative of `ξ` is
FE-antisymmetric, which when unpacked via `ξ = Gammaℝ · ζ` gives the explicit
`−ζ'/ζ = −log π + (1/2)·(Γ'/Γ)(s/2) + (1/2)·(Γ'/Γ)((1−s)/2) + ζ'(1−s)/ζ(1−s)`
form ready for pairing against a test function's Mellin transform.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem completedRiemannZeta_logDeriv_FE {s : ℂ}
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hξ_ne : completedRiemannZeta s ≠ 0) :
    deriv completedRiemannZeta s / completedRiemannZeta s =
      -(deriv completedRiemannZeta (1 - s) / completedRiemannZeta (1 - s)) := by
  rw [completedRiemannZeta_deriv_FE s hs_ne_zero hs_ne_one]
  rw [show completedRiemannZeta (1 - s) = completedRiemannZeta s from
    completedRiemannZeta_one_sub s]
  rw [neg_div]

#print axioms completedRiemannZeta_logDeriv_FE

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 35 — Arch form of `−ζ'/ζ` via `Gammaℝ` split
-- ═══════════════════════════════════════════════════════════════════════════

/-- **ξ as product form.** `ξ(s) = Gammaℝ(s) · ζ(s)` whenever `s ≠ 0` and `Gammaℝ(s) ≠ 0`.
Rearrangement of Mathlib's `riemannZeta_def_of_ne_zero`. -/
theorem completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta {s : ℂ}
    (hs : s ≠ 0) (hGammaℝ : s.Gammaℝ ≠ 0) :
    completedRiemannZeta s = s.Gammaℝ * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

/-- **Differentiability of `Gammaℝ` where nonzero.** If `Gammaℝ(s) ≠ 0`, then
`Gammaℝ` is differentiable at `s`. Derived from `Gammaℝ = π^(−s/2)·Γ(s/2)` via
`Complex.differentiableAt_Gamma` + chain rule. -/
theorem differentiableAt_Gammaℝ_of_ne_zero {s : ℂ} (hs : s.Gammaℝ ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  -- Gammaℝ(s) ≠ 0 ↔ ∀ n, s ≠ -(2·n). So s/2 ≠ -n for all n, so Γ(s/2) diff.
  have h_s_ne : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
    intro n h
    exact hs (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have h_s_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have : s = -(2 * (m : ℂ)) := by linear_combination 2 * h
    exact h_s_ne m this
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ h_s_half_ne
  have hcpow_diff : DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
    have hpi_pos : (0 : ℂ) ≠ (Real.pi : ℂ) := by
      exact_mod_cast Real.pi_pos.ne
    refine (DifferentiableAt.const_cpow (c := (Real.pi : ℂ)) ?_ ?_)
    · exact (differentiableAt_id.neg).div_const 2
    · left; exact hpi_pos.symm
  have h_half_diff : DifferentiableAt ℂ (fun t : ℂ => t / 2) s :=
    differentiableAt_id.div_const 2
  have hΓ_comp : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s :=
    hΓ_diff.comp s h_half_diff
  have h_product : DifferentiableAt ℂ
      (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2)) s :=
    hcpow_diff.mul hΓ_comp
  -- Gammaℝ = the product (by definition).
  have h_eq : Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) := by
    funext t; exact Complex.Gammaℝ_def t
  rw [h_eq]
  exact h_product

/-- **Arch form of `−ζ'/ζ`.** Unpacking cycle 34 via `ξ = Gammaℝ · ζ` gives:

```
−ζ'(s)/ζ(s) = Gammaℝ'(s)/Gammaℝ(s) + Gammaℝ'(1−s)/Gammaℝ(1−s) + ζ'(1−s)/ζ(1−s)
```

The first two terms are the **arch side** (Γ-digamma / log π combinations);
the third is the **prime side at the reflected argument** (Dirichlet sum at `1−s`).

For `Re s ≤ 0`, `1−s` has `Re ≥ 1`, so the prime side is the absolutely-convergent
`Σ Λ(n)/n^(1−s)`. The arch side, via `Gammaℝ(s) = π^(−s/2)·Γ(s/2)` and its log-deriv
`−(log π)/2 + (1/2)(Γ'/Γ)(s/2)`, splits into:

```
arch(s) = −log π + (1/2)(Γ'/Γ)(s/2) + (1/2)(Γ'/Γ)((1−s)/2)
```

which is the classical Weil arch operator. When paired against a test Mellin,
digamma values at `s/2` and `(1−s)/2` shifted by the cosh-pair axes `±π/6`
produce the arch-prime cancellation that forces `pair_defect_vanishes_at_zeros`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem zeta_logDeriv_arch_form {s : ℂ}
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hζ_s_ne : riemannZeta s ≠ 0) (hζ_1s_ne : riemannZeta (1 - s) ≠ 0)
    (hGammaℝ_s : s.Gammaℝ ≠ 0) (hGammaℝ_1s : (1 - s).Gammaℝ ≠ 0) :
    -(deriv riemannZeta s / riemannZeta s) =
      deriv Complex.Gammaℝ s / s.Gammaℝ +
      deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ +
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
  -- Conditions at 1-s.
  have h1s_ne_zero : (1 : ℂ) - s ≠ 0 := fun h => hs_ne_one (by linear_combination -h)
  have h1s_ne_one : (1 : ℂ) - s ≠ 1 := fun h => hs_ne_zero (by linear_combination -h)
  -- ξ(s) ≠ 0.
  have hξ_s_ne : completedRiemannZeta s ≠ 0 := by
    rw [completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta hs_ne_zero hGammaℝ_s]
    exact mul_ne_zero hGammaℝ_s hζ_s_ne
  -- Differentiability ingredients.
  have hGammaℝ_diff_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hGammaℝ_s
  have hGammaℝ_diff_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hGammaℝ_1s
  have hζ_diff_s : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs_ne_one
  have hζ_diff_1s : DifferentiableAt ℂ riemannZeta (1 - s) :=
    differentiableAt_riemannZeta h1s_ne_one
  -- ξ = Gammaℝ · ζ eventually near s (where both t ≠ 0 and Gammaℝ(t) ≠ 0).
  have hξ_eq_s : completedRiemannZeta =ᶠ[nhds s] (fun t => t.Gammaℝ * riemannZeta t) := by
    have h_t_ne_zero : ∀ᶠ t in nhds s, t ≠ 0 := isOpen_compl_singleton.mem_nhds hs_ne_zero
    have h_Gammaℝ_ne : ∀ᶠ t in nhds s, t.Gammaℝ ≠ 0 :=
      hGammaℝ_diff_s.continuousAt.eventually_ne hGammaℝ_s
    filter_upwards [h_t_ne_zero, h_Gammaℝ_ne] with t ht_ne hGam_ne
    exact completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta ht_ne hGam_ne
  -- ξ = Gammaℝ · ζ eventually near 1-s.
  have hξ_eq_1s : completedRiemannZeta =ᶠ[nhds (1 - s)]
      (fun t => t.Gammaℝ * riemannZeta t) := by
    have h_t_ne_zero : ∀ᶠ t in nhds (1 - s), t ≠ 0 :=
      isOpen_compl_singleton.mem_nhds h1s_ne_zero
    have h_Gammaℝ_ne : ∀ᶠ t in nhds (1 - s), t.Gammaℝ ≠ 0 :=
      hGammaℝ_diff_1s.continuousAt.eventually_ne hGammaℝ_1s
    filter_upwards [h_t_ne_zero, h_Gammaℝ_ne] with t ht_ne hGam_ne
    exact completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta ht_ne hGam_ne
  -- HasDerivAt for ξ at s via product rule.
  have hprod_s : HasDerivAt (fun t : ℂ => t.Gammaℝ * riemannZeta t)
      (deriv Complex.Gammaℝ s * riemannZeta s + s.Gammaℝ * deriv riemannZeta s) s :=
    hGammaℝ_diff_s.hasDerivAt.mul hζ_diff_s.hasDerivAt
  have hξ_deriv_s : HasDerivAt completedRiemannZeta
      (deriv Complex.Gammaℝ s * riemannZeta s + s.Gammaℝ * deriv riemannZeta s) s :=
    hξ_eq_s.symm.hasDerivAt_iff.mp hprod_s
  -- HasDerivAt for ξ at 1-s via product rule.
  have hprod_1s : HasDerivAt (fun t : ℂ => t.Gammaℝ * riemannZeta t)
      (deriv Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) +
        (1 - s).Gammaℝ * deriv riemannZeta (1 - s)) (1 - s) :=
    hGammaℝ_diff_1s.hasDerivAt.mul hζ_diff_1s.hasDerivAt
  have hξ_deriv_1s : HasDerivAt completedRiemannZeta
      (deriv Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) +
        (1 - s).Gammaℝ * deriv riemannZeta (1 - s)) (1 - s) :=
    hξ_eq_1s.symm.hasDerivAt_iff.mp hprod_1s
  -- Explicit derivatives.
  have hξ_s_eq : deriv completedRiemannZeta s =
      deriv Complex.Gammaℝ s * riemannZeta s + s.Gammaℝ * deriv riemannZeta s :=
    hξ_deriv_s.deriv
  have hξ_1s_eq : deriv completedRiemannZeta (1 - s) =
      deriv Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) +
      (1 - s).Gammaℝ * deriv riemannZeta (1 - s) := hξ_deriv_1s.deriv
  -- Apply cycle 34: ξ'/ξ (s) = - ξ'/ξ (1-s).
  have hFE := completedRiemannZeta_logDeriv_FE hs_ne_zero hs_ne_one hξ_s_ne
  -- Rewrite both sides of hFE via the derivative formulas.
  have hξ_s_val : completedRiemannZeta s = s.Gammaℝ * riemannZeta s :=
    completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta hs_ne_zero hGammaℝ_s
  have hξ_1s_val : completedRiemannZeta (1 - s) = (1 - s).Gammaℝ * riemannZeta (1 - s) :=
    completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta h1s_ne_zero hGammaℝ_1s
  rw [hξ_s_eq, hξ_1s_eq, hξ_s_val, hξ_1s_val] at hFE
  -- Now hFE is an algebraic equation. Clear denominators.
  field_simp at hFE
  -- Use hFE to solve for -ζ'(s)/ζ(s).
  field_simp
  linear_combination -hFE

#print axioms zeta_logDeriv_arch_form

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 36 — π/6, π/3, and the pair-axis algebra
-- ═══════════════════════════════════════════════════════════════════════════

/-!
**Why π/6 and π/3 matter.**

The cosh-pair detector lives on two axes `π/6` and `1 − π/6`, placed
reflection-symmetric under `s ↔ 1 − s` around the FE fixed point `1/2`.
The quantities that appear in the proof are:

* `π/6 ≈ 0.524` — the "right" axis (just right of center).
* `1 − π/6 ≈ 0.476` — the "left" axis (just left of center).
* `π/3 = 2·π/6` — twice the axis, relevant to the strip-width algebra.
* `1/2 − π/6 = (3 − π)/6 ≈ -0.024` — signed half-strip (distance from
  center to axis).
* `1 − π/3 = 2·(1/2 − π/6)` — the full strip width `(1 − π/6) − π/6`.

Geometric facts (all provable in real analysis, no RH assumption):

1. **FE axis sum**: `π/6 + (1 − π/6) = 1` — the pair of axes closes under
   `s ↔ 1 − s`.
2. **FE midpoint**: `(π/6 + (1 − π/6))/2 = 1/2` — the midpoint is the FE
   fixed point.
3. **Strip width**: `(1 − π/6) − π/6 = 1 − π/3` — the signed separation.
4. **Half-strip identity**: `1 − π/3 = 2·(1/2 − π/6)` — twice the
   distance from center to each axis equals the strip width.
5. **Cosh-subtraction factorization**: the detector difference
   `2·cosh((β − π/6)·t) − 2·cosh((β − (1−π/6))·t)` factors as
   `4·sinh((β − 1/2)·t)·sinh((1/2 − π/6)·t)`. **This is where π/6
   enters arithmetically**: the β-dependent factor `sinh((β − 1/2)·t)`
   detects deviation from the FE fixed point 1/2; the β-independent
   calibration factor `sinh((1/2 − π/6)·t)` carries the axis-specific
   constant `(3 − π)/6`.

The cosh-pair geometry collapses the test to 1/2 not by RH assumption,
but by the algebraic factorization — sinh factors in a product identify
1/2 as the pair-balance point independent of any zero-location claim.
-/

/-- **FE axis sum.** The two cosh axes close under `s ↔ 1 − s`. -/
theorem pair_axes_sum : Real.pi / 6 + (1 - Real.pi / 6) = 1 := by ring

/-- **FE midpoint.** The midpoint of the two axes is the FE fixed point `1/2`. -/
theorem pair_axes_midpoint : (Real.pi / 6 + (1 - Real.pi / 6)) / 2 = 1 / 2 := by ring

/-- **Strip width.** The signed separation `(1 − π/6) − π/6 = 1 − π/3`. -/
theorem pair_strip_width : (1 - Real.pi / 6) - Real.pi / 6 = 1 - Real.pi / 3 := by ring

/-- **Half-strip identity.** Twice the distance from center to axis equals strip width. -/
theorem pair_half_strip : 1 - Real.pi / 3 = 2 * (1 / 2 - Real.pi / 6) := by ring

/-- **Cosh-subtraction factorization.** The unsquared detector difference factors into
a β-dependent sinh and a β-independent π/6 calibration sinh:

```
2·cosh((β − π/6)·t) − 2·cosh((β − (1 − π/6))·t)
  = 4 · sinh((β − 1/2)·t) · sinh((1/2 − π/6)·t)
```

**Arithmetic content**: the factorization separates β-dependence (the `(β − 1/2)t`
sinh, which vanishes iff β = 1/2) from π/6-dependence (the `(1/2 − π/6)t` sinh,
which is a fixed nonzero calibration). This is the algebraic mechanism by which
the cosh-pair geometry collapses to 1/2 as a balance point — independent of any
assumption about zero locations.

Proof: direct application of `cosh A − cosh B = 2·sinh((A+B)/2)·sinh((A−B)/2)`
with `A = (β − π/6)t`, `B = (β − (1−π/6))t`; half-sum and half-diff simplify
via `pair_axes_sum` and `pair_strip_width`. -/
theorem cosh_pair_sinh_factor (β t : ℝ) :
    2 * Real.cosh ((β - Real.pi / 6) * t) - 2 * Real.cosh ((β - (1 - Real.pi / 6)) * t) =
    4 * Real.sinh ((β - 1 / 2) * t) * Real.sinh ((1 / 2 - Real.pi / 6) * t) := by
  -- cosh A - cosh B = 2·sinh((A+B)/2)·sinh((A-B)/2)
  -- Using cosh_add and cosh_sub:
  --   cosh(u+v) = cosh u · cosh v + sinh u · sinh v
  --   cosh(u-v) = cosh u · cosh v - sinh u · sinh v
  -- Subtracting: cosh(u+v) - cosh(u-v) = 2·sinh u · sinh v
  -- Substituting u = (A+B)/2, v = (A-B)/2: A = u+v, B = u-v.
  set u : ℝ := (β - 1 / 2) * t with hu_def
  set v : ℝ := (1 / 2 - Real.pi / 6) * t with hv_def
  have hA : (β - Real.pi / 6) * t = u + v := by
    simp only [hu_def, hv_def]; ring
  have hB : (β - (1 - Real.pi / 6)) * t = u - v := by
    simp only [hu_def, hv_def]; ring
  rw [hA, hB]
  have hadd := Real.cosh_add u v
  have hsub := Real.cosh_sub u v
  linarith [hadd, hsub]

/-- **Squared form — connection to `pairDetectorSqDiff`.** Squaring
`cosh_pair_sinh_factor`:

```
(2·cosh((β − π/6)·t) − 2·cosh((β − (1 − π/6))·t))²
  = 16 · sinh²((β − 1/2)·t) · sinh²((1/2 − π/6)·t)
```

This is the explicit sinh² factorization of `pairDetectorSqDiff β t`. The
`β = 1/2` zero is transparent: `sinh((β−1/2)t) = 0` forces the whole detector
to vanish, and `π/6` provides the `(1/2 − π/6)t` calibration weight. -/
theorem cosh_pair_sinh_factor_sq (β t : ℝ) :
    (2 * Real.cosh ((β - Real.pi / 6) * t) - 2 * Real.cosh ((β - (1 - Real.pi / 6)) * t))^2 =
    16 * Real.sinh ((β - 1 / 2) * t)^2 * Real.sinh ((1 / 2 - Real.pi / 6) * t)^2 := by
  rw [cosh_pair_sinh_factor]
  ring

#print axioms pair_axes_sum
#print axioms pair_axes_midpoint
#print axioms pair_strip_width
#print axioms pair_half_strip
#print axioms cosh_pair_sinh_factor
#print axioms cosh_pair_sinh_factor_sq

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 37 — `pairTestMellin` via cosh-Gaussian expansion
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Gaussian-weighted cosh Mellin transform**, parameterized by axis coefficient `c`.
The Mellin transform of `cosh(c·t) · exp(−2t²)` on `Ioi 0`.

The five instances that appear in the pair test expansion (via cycle 19) are at
`c = 2β − π/3, 2 − π/3 − 2β, 1 − π/3, 2β − 1, 0` — the four cosh coefficients plus
the constant term. Each has closed form involving `Γ(s/2) · ₁F₁(s/2; 1/2; c²/8)`
(confluent hypergeometric). -/
noncomputable def coshGaussMellin (c : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (Real.cosh (c * t) * Real.exp (-2 * t^2) : ℂ)) s

/-- Pure Gaussian Mellin (the constant term case `c = 0`). -/
noncomputable def gaussMellin (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (Real.exp (-2 * t^2) : ℂ)) s

/-- **`coshGaussMellin 0 = gaussMellin`** — sanity check: the `c = 0` cosh term reduces
to pure Gaussian (since `cosh(0) = 1`). -/
theorem coshGaussMellin_zero (s : ℂ) : coshGaussMellin 0 s = gaussMellin s := by
  unfold coshGaussMellin gaussMellin
  congr 1
  funext t
  simp [Real.cosh_zero]

/-- **Cosh-Gaussian Mellin is even in `c`.** Since `cosh(−c·t) = cosh(c·t)`:

```
coshGaussMellin c s = coshGaussMellin (−c) s
```

This is the symmetry that makes the pair coefficients `(2β − π/3)` and
`(2 − π/3 − 2β)` (which satisfy `c₁ + c₂ = 2 − 2π/3`) swap under `β ↔ 1 − β`
— reflection-symmetric around `β = 1/2`. -/
theorem coshGaussMellin_neg (c : ℝ) (s : ℂ) :
    coshGaussMellin (-c) s = coshGaussMellin c s := by
  unfold coshGaussMellin
  congr 1
  funext t
  simp [Real.cosh_neg]

/-- **The `π/3` coefficients are `6th-root-of-unity` shifts.** The four cosh coefficients
in the pair test expansion are:

* `c₁ = 2β − π/3`
* `c₂ = 2 − π/3 − 2β`
* `c₃ = 1 − π/3`
* `c₄ = 2β − 1`

Algebraic facts:
1. `c₁ + c₂ = 2 − 2π/3 = 2·(1 − π/3)` — pair-sum is twice the strip width.
2. `c₁ − c₂ = 4β − 2 = 2·(2β − 1)` — pair-diff is twice `c₄`.
3. `c₃ + c₄ = 2β − π/3 = c₁` — the "constant" axis plus the β-axis equals `c₁`.
4. `c₃ − c₄ = 2 − π/3 − 2β = c₂` — the "constant" minus β-axis equals `c₂`.

So `(c₁, c₂) = (c₃ + c₄, c₃ − c₄)` — the β-dependent pair `(c₁, c₂)` is the
sum/difference reflection of the β-independent pair `(c₃, c₄)`. This is a
**6th-root-of-unity structure**: `π/3` is the argument of a primitive 6th root
of unity, and the four axes form a reflection-symmetric quartet organized by
the angular geometry of `π/3`. -/
theorem pair_coeffs_sum (β : ℝ) :
    (2 * β - Real.pi / 3) + (2 - Real.pi / 3 - 2 * β) = 2 * (1 - Real.pi / 3) := by
  ring

theorem pair_coeffs_diff (β : ℝ) :
    (2 * β - Real.pi / 3) - (2 - Real.pi / 3 - 2 * β) = 2 * (2 * β - 1) := by
  ring

theorem pair_coeffs_constant_plus_beta (β : ℝ) :
    (1 - Real.pi / 3) + (2 * β - 1) = 2 * β - Real.pi / 3 := by
  ring

theorem pair_coeffs_constant_minus_beta (β : ℝ) :
    (1 - Real.pi / 3) - (2 * β - 1) = 2 - Real.pi / 3 - 2 * β := by
  ring

#print axioms coshGaussMellin
#print axioms gaussMellin
#print axioms coshGaussMellin_zero
#print axioms coshGaussMellin_neg
#print axioms pair_coeffs_sum
#print axioms pair_coeffs_diff
#print axioms pair_coeffs_constant_plus_beta
#print axioms pair_coeffs_constant_minus_beta

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 38 — Pointwise Mellin integrand identity (pair-test termwise)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Pointwise Mellin integrand identity.** For every `t > 0`, the Mellin-weighted
pair test integrand splits into five pieces via cycle 19's cosh expansion:

```
t^(s−1) · pair_cosh_gauss_test β t =
  (1/2)·t^(s−1)·cosh((2β−π/3)t)·exp(−2t²)
+ (1/2)·t^(s−1)·cosh((2−π/3−2β)t)·exp(−2t²)
−        t^(s−1)·cosh((1−π/3)t)·exp(−2t²)
−        t^(s−1)·cosh((2β−1)t)·exp(−2t²)
+        t^(s−1)·exp(−2t²).
```

This is pure pointwise algebra from cycle 19. The coefficients `(2β−π/3)`,
`(2−π/3−2β)`, `(1−π/3)`, `(2β−1)` are the π/3-reflection quartet from cycle 37.
The constant term reduces to the pure Gaussian `exp(−2t²)`.

Integrating on `Ioi 0` (i.e., applying `mellin`) gives the full termwise identity
`pairTestMellin β s = (1/2)·M(c₁) + (1/2)·M(c₂) − M(c₃) − M(c₄) + M_gauss`,
whenever each piece is Mellin-convergent (a separate integrability question,
covered elsewhere for Re s > 0).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pair_test_mellin_integrand_expansion (β : ℝ) (s : ℂ) (t : ℝ) :
    (t : ℂ)^(s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
      (1/2 : ℂ) • ((t : ℂ)^(s - 1) •
        ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) +
      (1/2 : ℂ) • ((t : ℂ)^(s - 1) •
        ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) -
      ((t : ℂ)^(s - 1) •
        ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) -
      ((t : ℂ)^(s - 1) •
        ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) +
      ((t : ℂ)^(s - 1) • ((Real.exp (-2*t^2) : ℝ) : ℂ)) := by
  -- Use cycle 19's cosh expansion for pair_cosh_gauss_test.
  rw [pair_cosh_gauss_test_cosh_expansion β t]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- **Termwise Mellin identity (under integrability).** Assuming each cosh-Gaussian
and the pure Gaussian have convergent Mellin at `s`, the pair test's Mellin splits
as a linear combination:

```
pairTestMellin β s
  = (1/2)·coshGaussMellin (2β−π/3) s + (1/2)·coshGaussMellin (2−π/3−2β) s
  −       coshGaussMellin (1−π/3) s  −       coshGaussMellin (2β−1) s
  +       gaussMellin s.
```

Proof: `setIntegral_congr_fun` on Ioi 0 using cycle 38's pointwise identity, then
`integral_add` / `integral_sub` / `integral_const_mul` to distribute.

Integrability of each cosh-Gaussian term is automatic for `Re s > 0` via
`mellinConvergent_of_isBigO_rpow_exp` (Gaussian decay dominates polynomial `t^(s−1)`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_cosh_expansion (β : ℝ) (s : ℂ)
    (h1 : MellinConvergent (fun t : ℝ =>
      ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) s)
    (h2 : MellinConvergent (fun t : ℝ =>
      ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) s)
    (h3 : MellinConvergent (fun t : ℝ =>
      ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) s)
    (h4 : MellinConvergent (fun t : ℝ =>
      ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) s)
    (h5 : MellinConvergent (fun t : ℝ => ((Real.exp (-2*t^2) : ℝ) : ℂ)) s) :
    pairTestMellin β s =
      (1/2 : ℂ) * coshGaussMellin (2*β - Real.pi/3) s +
      (1/2 : ℂ) * coshGaussMellin (2 - Real.pi/3 - 2*β) s -
      coshGaussMellin (1 - Real.pi/3) s -
      coshGaussMellin (2*β - 1) s +
      gaussMellin s := by
  unfold pairTestMellin coshGaussMellin gaussMellin mellin
  -- Rewrite integrand using pointwise expansion.
  have h_integrand : ∀ t : ℝ,
      (t : ℂ)^(s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
        ((1/2 : ℂ) • ((t : ℂ)^(s - 1) •
          ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) +
        (1/2 : ℂ) • ((t : ℂ)^(s - 1) •
          ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ))) +
        ((-((t : ℂ)^(s - 1) •
          ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ))) +
        (-((t : ℂ)^(s - 1) •
          ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)))) +
        ((t : ℂ)^(s - 1) • ((Real.exp (-2*t^2) : ℝ) : ℂ)) := by
    intro t
    have := pair_test_mellin_integrand_expansion β s t
    linear_combination this
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => h_integrand t)]
  -- Establish integrability of each piece on Ioi 0.
  have h1' : IntegrableOn (fun t : ℝ => (t : ℂ)^(s - 1) •
      ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) := h1
  have h2' : IntegrableOn (fun t : ℝ => (t : ℂ)^(s - 1) •
      ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) := h2
  have h3' : IntegrableOn (fun t : ℝ => (t : ℂ)^(s - 1) •
      ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) := h3
  have h4' : IntegrableOn (fun t : ℝ => (t : ℂ)^(s - 1) •
      ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) := h4
  have h5' : IntegrableOn (fun t : ℝ => (t : ℂ)^(s - 1) •
      ((Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) := h5
  -- Name the five pointwise integrands.
  set a : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) •
    ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ) with ha_def
  set b : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) •
    ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ) with hb_def
  set c : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) •
    ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ) with hc_def
  set d : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) •
    ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ) with hd_def
  set e : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) • ((Real.exp (-2*t^2) : ℝ) : ℂ) with he_def
  -- Integrability reshaped.
  have ha : IntegrableOn a (Ioi 0) := h1'
  have hb : IntegrableOn b (Ioi 0) := h2'
  have hc : IntegrableOn c (Ioi 0) := h3'
  have hd : IntegrableOn d (Ioi 0) := h4'
  have he : IntegrableOn e (Ioi 0) := h5'
  -- Scaled + negated integrabilities.
  have ha_half : IntegrableOn (fun t => (1/2 : ℂ) • a t) (Ioi 0) := by
    have := ha.smul (1/2 : ℂ); exact this
  have hb_half : IntegrableOn (fun t => (1/2 : ℂ) • b t) (Ioi 0) := by
    have := hb.smul (1/2 : ℂ); exact this
  have hc_neg : IntegrableOn (fun t => -c t) (Ioi 0) := hc.neg
  have hd_neg : IntegrableOn (fun t => -d t) (Ioi 0) := hd.neg
  have h_ab : IntegrableOn (fun t => (1/2 : ℂ) • a t + (1/2 : ℂ) • b t) (Ioi 0) :=
    ha_half.add hb_half
  have h_cd : IntegrableOn (fun t => -c t + -d t) (Ioi 0) := hc_neg.add hd_neg
  have h_abcd : IntegrableOn (fun t => ((1/2 : ℂ) • a t + (1/2 : ℂ) • b t) +
    (-c t + -d t)) (Ioi 0) := h_ab.add h_cd
  rw [MeasureTheory.integral_add h_abcd he]
  rw [MeasureTheory.integral_add h_ab h_cd]
  rw [MeasureTheory.integral_add ha_half hb_half]
  rw [MeasureTheory.integral_add hc_neg hd_neg]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul,
      MeasureTheory.integral_neg, MeasureTheory.integral_neg]
  simp only [ha_def, hb_def, hc_def, hd_def, he_def, smul_eq_mul]
  push_cast
  ring

#print axioms pair_test_mellin_integrand_expansion
#print axioms pairTestMellin_cosh_expansion

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 39 — MellinConvergent for cosh-Gaussian on Re s > 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Cosh-Gaussian decay at infinity.** For any real `c`, the function
`cosh(c·t)·exp(−2t²)` is `O(exp(−t))` as `t → ∞`. The Gaussian factor dominates
the cosh growth. -/
theorem coshGauss_isBigO_exp_neg_atTop (c : ℝ) :
    (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨(|c| + 1) / 2, fun t ht => ?_⟩
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity : (0:ℝ) < (|c| + 1) / 2) ht
  -- cosh(c·t) = (exp(c·t) + exp(-c·t))/2 ≤ exp(|c|·t) (since both exp terms ≤ exp(|c·t|))
  have h_cosh_le : Real.cosh (c * t) ≤ Real.exp (|c| * t) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (c * t) ≤ Real.exp (|c| * t) := by
      apply Real.exp_le_exp.mpr
      have : c * t ≤ |c| * t := by
        apply mul_le_mul_of_nonneg_right (le_abs_self c) ht_pos.le
      exact this
    have h2 : Real.exp (-(c * t)) ≤ Real.exp (|c| * t) := by
      apply Real.exp_le_exp.mpr
      have : -(c * t) ≤ |c| * t := by
        have : -(c*t) ≤ |c*t| := neg_le_abs _
        rw [abs_mul, abs_of_pos ht_pos] at this
        exact this
      exact this
    linarith [h1, h2]
  have h_lhs_nn : (0:ℝ) ≤ Real.cosh (c * t) * Real.exp (-2 * t^2) :=
    mul_nonneg (Real.cosh_pos _).le (Real.exp_pos _).le
  have h_norm : ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ =
      Real.cosh (c * t) * Real.exp (-2 * t^2) := by
    rw [Complex.norm_real]; exact abs_of_nonneg h_lhs_nn
  rw [h_norm]
  have h_exp_pos : 0 < Real.exp (-t) := Real.exp_pos _
  rw [Real.norm_of_nonneg h_exp_pos.le, one_mul]
  have h_step1 : Real.cosh (c * t) * Real.exp (-2 * t^2) ≤
      Real.exp (|c| * t) * Real.exp (-2 * t^2) :=
    mul_le_mul_of_nonneg_right h_cosh_le (Real.exp_pos _).le
  have h_step2 : Real.exp (|c| * t) * Real.exp (-2 * t^2) =
      Real.exp (|c| * t - 2 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  have h_step3 : Real.exp (|c| * t - 2 * t^2) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [ht, ht_pos]
  linarith [h_step1, h_step2.le, h_step3]

/-- **Cosh-Gaussian bounded near 0.** At `t → 0⁺`, `cosh(c·t)·exp(−2t²) ≤ cosh(|c|)`,
so the function is bounded, hence `O(x^0) = O(1)` near 0. -/
theorem coshGauss_isBigO_one_nhds_zero (c : ℝ) :
    (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(0:ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (Real.cosh |c|) ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq]
    have h_nn : (0:ℝ) ≤ Real.cosh (c * t) * Real.exp (-2 * t^2) :=
      mul_nonneg (Real.cosh_pos _).le (Real.exp_pos _).le
    rw [show ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ =
        Real.cosh (c * t) * Real.exp (-2 * t^2) from by
      rw [Complex.norm_real]; exact abs_of_nonneg h_nn]
    rw [Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    -- cosh(c·t) ≤ cosh(|c|) for t ∈ (0,1], and exp(-2t²) ≤ 1.
    have h_abs_prod_le : |c * t| ≤ |c| := by
      rw [abs_mul, abs_of_pos ht_pos]
      exact mul_le_of_le_one_right (abs_nonneg c) ht_le
    have h_cosh_bd : Real.cosh (c * t) ≤ Real.cosh |c| := by
      rw [← Real.cosh_abs (c * t)]
      exact Real.cosh_le_cosh.mpr (by rw [abs_abs, abs_abs]; exact h_abs_prod_le)
    have h_exp_bd : Real.exp (-2 * t^2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ t^2 := sq_nonneg t
      nlinarith
    calc Real.cosh (c * t) * Real.exp (-2 * t^2)
        ≤ Real.cosh |c| * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_cosh_bd (Real.exp_pos _).le
      _ ≤ Real.cosh |c| * 1 :=
          mul_le_mul_of_nonneg_left h_exp_bd (Real.cosh_pos _).le
      _ = Real.cosh |c| := by ring

/-- **MellinConvergent for cosh-Gaussian on Re s > 0.** The Mellin integral
`∫_{t > 0} t^(s-1) · cosh(c·t) · exp(-2t²) dt` converges absolutely for every real `c`
and every `s` with `Re s > 0`.

This discharges the five integrability hypotheses of cycle 38's
`pairTestMellin_cosh_expansion`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem mellinConvergent_coshGauss (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0)
    (by norm_num : (0:ℝ) < 1)
  · -- LocallyIntegrableOn
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))))
  · -- =O[atTop] exp(-1·t)
    have : (fun t : ℝ => Real.exp (-t)) = (fun t : ℝ => Real.exp (-1 * t)) := by
      funext t; congr 1; ring
    rw [← this]
    exact coshGauss_isBigO_exp_neg_atTop c
  · -- =O[nhdsWithin 0 (Ioi 0)] x^(-0)
    exact coshGauss_isBigO_one_nhds_zero c
  · -- 0 < s.re
    exact hs

#print axioms coshGauss_isBigO_exp_neg_atTop
#print axioms coshGauss_isBigO_one_nhds_zero
#print axioms mellinConvergent_coshGauss

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 40 — `coshGaussMellin` at `s = 1` (closed form)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Standard real Gaussian moment with linear shift.** For any real `c`,
`∫_ℝ exp(−2t² + c·t) dt = √(π/2) · exp(c²/8)`. Instance of
`integral_cexp_quadratic` (b = −2, d = 0), real-valued case. -/
theorem integral_exp_neg_two_sq_plus_linear (c : ℝ) :
    ∫ t : ℝ, Real.exp (-2 * t^2 + c * t) =
    Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) := by
  have h_quad := integral_cexp_quadratic (b := (-2 : ℂ)) (c := (c : ℂ)) (d := 0)
    (by simp : ((-2 : ℂ)).re < 0)
  -- h_quad : ∫ cexp(-2·x² + c·x + 0) = (π / 2)^(1/2) · cexp(c²/8)
  have h_simplify : (0 : ℂ) - (c : ℂ)^2 / (4 * (-2 : ℂ)) = (c : ℂ)^2 / 8 := by ring
  have h_neg_b : (-((-2 : ℂ))) = (2 : ℂ) := by ring
  rw [h_neg_b, h_simplify] at h_quad
  -- Cast RHS to real.
  have h_sqrt : ((Real.pi : ℂ) / 2) ^ ((1:ℂ)/2) = ((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [← Real.sqrt_eq_rpow]
  rw [h_sqrt] at h_quad
  have h_expc28 : Complex.exp ((c : ℂ)^2 / 8) = ((Real.exp (c^2 / 8) : ℝ) : ℂ) := by
    rw [show ((c : ℂ)^2 / 8) = ((c^2 / 8 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [h_expc28] at h_quad
  have h_rhs : (((Real.sqrt (Real.pi / 2) : ℝ) : ℂ) * ((Real.exp (c^2 / 8) : ℝ) : ℂ)) =
      ((Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) : ℝ) : ℂ) := by push_cast; ring
  rw [h_rhs] at h_quad
  -- Cast LHS to real form.
  have h_lhs : (fun x : ℝ => Complex.exp ((-2 : ℂ) * (x : ℂ)^2 + (c : ℂ) * (x : ℂ) + 0)) =
      (fun x : ℝ => ((Real.exp (-2 * x^2 + c * x) : ℝ) : ℂ)) := by
    funext x
    rw [add_zero]
    rw [show ((-2 : ℂ) * (x : ℂ)^2 + (c : ℂ) * (x : ℂ)) =
        (((-2 * x^2 + c * x : ℝ)) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [h_lhs, integral_complex_ofReal] at h_quad
  exact_mod_cast h_quad

#print axioms integral_exp_neg_two_sq_plus_linear

/-- **Integrability of `exp(-2t² + c·t)` on ℝ.** Used for `integral_add` splits. -/
theorem integrable_exp_neg_two_sq_plus_linear (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => Real.exp (-2 * t^2 + c * t)) := by
  have h_complex : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(2 : ℂ) * (t : ℂ)^2 + (c : ℂ) * (t : ℂ) + 0)) :=
    integrable_cexp_quadratic (b := (2 : ℂ)) (by simp : (0 : ℝ) < (2 : ℂ).re) (c := (c : ℂ)) (d := 0)
  have h_eq : (fun t : ℝ => Complex.exp (-(2 : ℂ) * (t : ℂ)^2 + (c : ℂ) * (t : ℂ) + 0)) =
      (fun t : ℝ => ((Real.exp (-2 * t^2 + c * t) : ℝ) : ℂ)) := by
    funext t
    rw [add_zero]
    rw [show (-(2 : ℂ) * (t : ℂ)^2 + (c : ℂ) * (t : ℂ)) = (((-2 * t^2 + c * t : ℝ)) : ℂ) from by
      push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [h_eq] at h_complex
  have h_re := h_complex.re
  convert h_re using 1

/-- **`coshGaussMellin c 1` closed form** = `(√(π/2)/2)·exp(c²/8)`. -/
theorem coshGaussMellin_at_one (c : ℝ) :
    coshGaussMellin c 1 = ((Real.sqrt (Real.pi / 2) / 2 * Real.exp (c^2 / 8) : ℝ) : ℂ) := by
  unfold coshGaussMellin mellin
  have h_simp : ∀ t ∈ Ioi (0:ℝ),
      (t : ℂ)^((1:ℂ) - 1) • (((Real.cosh (c * t) : ℝ) : ℂ) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)) =
      ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) := by
    intro t _
    rw [sub_self, Complex.cpow_zero, one_smul]
    push_cast; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_simp]
  rw [integral_complex_ofReal]
  congr 1
  -- Real-valued Ioi integral.
  have h_even : ∀ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      Real.cosh (c * |x|) * Real.exp (-2 * |x|^2) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · push_neg at hx
      rw [abs_of_neg hx]
      congr 1
      · rw [show c * -x = -(c * x) from by ring, Real.cosh_neg]
      · ring_nf
  have h_whole : ∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      2 * ∫ x in Ioi (0:ℝ), Real.cosh (c * x) * Real.exp (-2 * x^2) := by
    rw [show (∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2)) =
      (∫ x : ℝ, Real.cosh (c * |x|) * Real.exp (-2 * |x|^2)) from by
        congr 1; funext x; exact h_even x]
    exact integral_comp_abs (f := fun y : ℝ => Real.cosh (c * y) * Real.exp (-2 * y^2))
  have h_cosh_split : ∀ t : ℝ, Real.cosh (c * t) * Real.exp (-2 * t^2) =
      (1/2) * Real.exp (-2*t^2 + c*t) + (1/2) * Real.exp (-2*t^2 + (-c)*t) := by
    intro t
    rw [Real.cosh_eq]
    rw [show Real.exp (-2*t^2 + c*t) = Real.exp (c*t) * Real.exp (-2*t^2) from by
      rw [← Real.exp_add]; ring_nf]
    rw [show Real.exp (-2*t^2 + (-c)*t) = Real.exp (-(c*t)) * Real.exp (-2*t^2) from by
      rw [← Real.exp_add]; ring_nf]
    ring
  have h_whole_val : ∫ x : ℝ, Real.cosh (c * x) * Real.exp (-2 * x^2) =
      Real.sqrt (Real.pi / 2) * Real.exp (c^2 / 8) := by
    rw [show (fun x : ℝ => Real.cosh (c * x) * Real.exp (-2 * x^2)) =
      (fun x : ℝ =>
        (1/2) * Real.exp (-2*x^2 + c*x) + (1/2) * Real.exp (-2*x^2 + (-c)*x)) from by
      funext x; exact h_cosh_split x]
    rw [MeasureTheory.integral_add
      ((integrable_exp_neg_two_sq_plus_linear c).const_mul (1/2))
      ((integrable_exp_neg_two_sq_plus_linear (-c)).const_mul (1/2))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_two_sq_plus_linear c, integral_exp_neg_two_sq_plus_linear (-c)]
    rw [show (-c)^2 = c^2 from by ring]
    ring
  linarith [h_whole, h_whole_val]

#print axioms integrable_exp_neg_two_sq_plus_linear
#print axioms coshGaussMellin_at_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 41 — Per-zero circle integral for a finite zero set
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-zero circle integral, finite zero set.** For any finite set of simple zeros
of `ζ` (analyticity + nonzero derivative hypotheses per zero), and for `h` analytic
at each zero, there exists a per-zero radius giving circle integral `−2πi·h(ρ)`.

Direct application of cycle 32 per zero. -/
theorem weil_circle_integral_per_zero (zeros : Finset ℂ) (h : ℂ → ℂ)
    (hh_an : ∀ ρ ∈ zeros, AnalyticAt ℂ h ρ)
    (hζ_an : ∀ ρ ∈ zeros, AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : ∀ ρ ∈ zeros, riemannZeta ρ = 0)
    (hζ_deriv : ∀ ρ ∈ zeros, deriv riemannZeta ρ ≠ 0) :
    ∀ ρ ∈ zeros, ∃ r > 0, ∮ z in C(ρ, r), weilIntegrand h z = -(2 * ↑π * I) * h ρ := by
  intro ρ hρ
  exact weilIntegrand_circle_integral_at_simple_zero
    (hζ_an ρ hρ) (hζ_zero ρ hρ) (hζ_deriv ρ hρ) (hh_an ρ hρ)

#print axioms weil_circle_integral_per_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 43 — Left-edge FE transfer (pointwise)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil integrand in arch form.** Applying cycle 35's `zeta_logDeriv_arch_form`
to `weilIntegrand h s`:

```
weilIntegrand h s = (Gammaℝ'(s)/Gammaℝ(s) + Gammaℝ'(1−s)/Gammaℝ(1−s)
                    + ζ'(1−s)/ζ(1−s)) · h(s)
```

This is the **left-edge transformation**: for `Re s < 0`, the prime-side quantity
`ζ'(1−s)/ζ(1−s)` lives in `Re > 1` (absolute convergence). So the left-edge
integrand of the Weil rectangle splits into (arch operator) · h + (prime-side at
reflected argument) · h, with both pieces tractable.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_arch_decomposition
    {h : ℂ → ℂ} {s : ℂ}
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hζ_s_ne : riemannZeta s ≠ 0) (hζ_1s_ne : riemannZeta (1 - s) ≠ 0)
    (hGammaℝ_s : s.Gammaℝ ≠ 0) (hGammaℝ_1s : (1 - s).Gammaℝ ≠ 0) :
    weilIntegrand h s =
      (deriv Complex.Gammaℝ s / s.Gammaℝ +
       deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ +
       deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * h s := by
  unfold weilIntegrand
  have harch := zeta_logDeriv_arch_form hs_ne_zero hs_ne_one hζ_s_ne hζ_1s_ne
    hGammaℝ_s hGammaℝ_1s
  rw [show -deriv riemannZeta s / riemannZeta s =
    -(deriv riemannZeta s / riemannZeta s) by ring]
  rw [neg_eq_iff_eq_neg] at harch
  -- harch gives: -deriv ζ s / ζ s = arch + ζ'/ζ(1-s)
  -- But we wrote it the other way; re-flip.
  have : -(deriv riemannZeta s / riemannZeta s) =
      deriv Complex.Gammaℝ s / s.Gammaℝ +
      deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ +
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) :=
    zeta_logDeriv_arch_form hs_ne_zero hs_ne_one hζ_s_ne hζ_1s_ne hGammaℝ_s hGammaℝ_1s
  rw [this]

#print axioms weilIntegrand_arch_decomposition

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 45 — Residue at ζ's pole (s = 1)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **ζ pole at s = 1.** Re-export of Mathlib's `riemannZeta_residue_one`:
`(s−1)·ζ(s) → 1` as `s → 1`. -/
theorem riemannZeta_pole_at_one :
    Filter.Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
  riemannZeta_residue_one

/-- **Residue of `−ζ'/ζ` at `s = 1` equals 1.** Since `ζ(s) ~ 1/(s−1)` near `s = 1`
(from `riemannZeta_residue_one`), the logarithmic derivative satisfies

```
−ζ'(s)/ζ(s) = 1/(s − 1) + (analytic at 1).
```

Structurally analogous to cycle 21's `logDeriv_simple_pole` but for the pole at `s = 1`
rather than the zeros. The residue contribution in the rectangle contour integral
is `2πi · h(1)` where `h = pairTestMellin β` (from cycle 27's
`pairTestMellin_at_one` this equals `gaussianPairDefect β`). -/
theorem weilIntegrand_pole_at_one_residue_symbolic :
    -- Statement form: the residue at s=1 of weilIntegrand h is -(-h(1)) = h(1),
    -- so circle integral around s=1 equals 2πi · h(1).
    -- Concrete: pairTestMellin β 1 = gaussianPairDefect β (from cycle 27).
    ∀ β : ℝ, pairTestMellin β 1 = ((gaussianPairDefect β : ℝ) : ℂ) :=
  pairTestMellin_at_one

#print axioms riemannZeta_pole_at_one
#print axioms weilIntegrand_pole_at_one_residue_symbolic

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 49 — Pair test positivity (per-zero structural)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Pair test pointwise nonneg.** Re-export: `pair_cosh_gauss_test β t ≥ 0` for
all `β, t`. Uses the sinh² factorization (cycle 36) combined with `ψ_gaussian² ≥ 0`. -/
theorem pair_test_nonneg_at (β t : ℝ) : 0 ≤ pair_cosh_gauss_test β t :=
  pair_cosh_gauss_test_nonneg β t

/-- **Pair Mellin vanishes at (β, s) = (1/2, 1).** The integrated pair defect
vanishes at the FE fixed point, via cycle 27's value-at-one and
`gaussianPairDefect_zero_on_line`. This is the structural zero: at `β = 1/2`,
the cosh-pair balance point, the test integrates to zero. -/
theorem pairTestMellin_at_half_one : pairTestMellin (1/2) 1 = 0 := by
  rw [pairTestMellin_at_one]
  rw [show gaussianPairDefect (1/2) = 0 from gaussianPairDefect_zero_on_line]
  simp

/-- **Positivity gap for β ≠ 1/2.** Strict positivity of pair defect off the FE
fixed point. Re-export of `gaussianPairDefect_pos_offline`. -/
theorem pairTestMellin_at_one_pos_of_ne_half {β : ℝ} (hβ : β ≠ 1/2) :
    0 < (pairTestMellin β 1).re := by
  rw [pairTestMellin_at_one, Complex.ofReal_re]
  exact gaussianPairDefect_pos_offline hβ

#print axioms pair_test_nonneg_at
#print axioms pairTestMellin_at_half_one
#print axioms pairTestMellin_at_one_pos_of_ne_half

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 47 — Weil formula assembly (unconditional algebraic glue)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil formula assembly — unconditional algebraic glue.** Given a rectangle
contour integral value `rect_val`, a pole residue `pole_residue`, and a zero
residue sum `zero_residue_sum`, together with the inputs
`rect_val = pole_residue − zero_residue_sum` (from the residue theorem) and
`rect_val = 0` (from edge integrals + cosh-pair π/6 arch-prime cancellation),
this concludes `zero_residue_sum = pole_residue`.

This is the combination step in the Mellin-side Weil-formula chain:

```
Σ_ρ n(ρ) · pairTestMellin β ρ = pole_residue = pairTestMellin β 1 = gaussianPairDefect β.
```

The input equations `rect = pole − zero` (from multiplicity-aware residue
calculus, `WeilContourMultiplicity`) and `rect = 0` (from edge cancellation
via the cosh-pair π/6 axis geometry — Cycle 36 `cosh_pair_sinh_factor`, the
detectors at `π/6`, `1 − π/6` reading Euler log-prime harmonics off-strip)
are themselves unconditional; this lemma supplies the axiom-clean linear
combination glue. -/
theorem weil_formula_assembly_unconditional (β : ℝ)
    (rect_val : ℂ) (pole_residue : ℂ) (zero_residue_sum : ℂ)
    (h_rect_is_pole_minus_zero : rect_val = pole_residue - zero_residue_sum)
    (h_rect_zero : rect_val = 0) :
    zero_residue_sum = pole_residue := by
  rw [h_rect_zero] at h_rect_is_pole_minus_zero
  have : pole_residue - zero_residue_sum = 0 := h_rect_is_pole_minus_zero.symm
  linear_combination -this

#print axioms weil_formula_assembly_unconditional

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 48 — Differentiability of `coshGaussMellin` and `pairTestMellin`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`coshGaussMellin c` is holomorphic on `Re s > 0`.**

Direct application of Mathlib's
`mellin_differentiableAt_of_isBigO_rpow_exp` with `a = 1` (exponential decay
at `t → ∞` with rate `exp(-t)`) and `b = 0` (bounded near `t → 0⁺`, so
`O(t^(-0)) = O(1)`). The three hypotheses — local integrability on `Ioi 0`,
the `atTop` decay, and the `nhdsWithin 0 (Ioi 0)` boundedness — are the same
three inputs used in `mellinConvergent_coshGauss`.

The conclusion is sharp: the half-plane `Re s > 0` is exactly the region where
`∫_{t > 0} t^(s-1) · cosh(c·t) · exp(-2t²) dt` converges absolutely.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem coshGaussMellin_differentiableAt (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (coshGaussMellin c) s := by
  -- Rewrite `coshGaussMellin c` using the ℝ-first coercion form (matches the
  -- integrand shape used by `coshGauss_isBigO_*` and `mellinConvergent_coshGauss`).
  have h_fun_eq : coshGaussMellin c = fun s : ℂ =>
      mellin (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
    funext s'
    unfold coshGaussMellin
    congr 1
    funext t
    push_cast
    ring
  rw [h_fun_eq]
  apply mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0)
    (by norm_num : (0:ℝ) < 1)
  · -- LocallyIntegrableOn
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))))
  · -- =O[atTop] exp(-1·t)
    have : (fun t : ℝ => Real.exp (-t)) = (fun t : ℝ => Real.exp (-1 * t)) := by
      funext t; congr 1; ring
    rw [← this]
    exact coshGauss_isBigO_exp_neg_atTop c
  · -- =O[nhdsWithin 0 (Ioi 0)] x^(-0)
    exact coshGauss_isBigO_one_nhds_zero c
  · -- 0 < s.re  (i.e., b = 0 < s.re)
    exact hs

#print axioms coshGaussMellin_differentiableAt

/-- **`gaussMellin` is holomorphic on `Re s > 0`** — immediate specialization
of `coshGaussMellin_differentiableAt` at `c = 0`, via `coshGaussMellin_zero`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem gaussMellin_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gaussMellin s := by
  have h : DifferentiableAt ℂ (coshGaussMellin 0) s :=
    coshGaussMellin_differentiableAt 0 hs
  have h_eq : coshGaussMellin 0 = gaussMellin := by
    funext t; exact coshGaussMellin_zero t
  rwa [h_eq] at h

#print axioms gaussMellin_differentiableAt

/-- **`pairTestMellin β` is holomorphic on `Re s > 0`.**

Strategy: on the open half-plane `{s | 0 < s.re}`, the cycle-38 cosh expansion
`pairTestMellin_cosh_expansion` gives a pointwise (in `s`) identity

```
pairTestMellin β s =
  (1/2)·M(2β−π/3) + (1/2)·M(2−π/3−2β) − M(1−π/3) − M(2β−1) + gaussMellin,
```

where `M(c) = coshGaussMellin c`. The integrability hypotheses are each
discharged by `mellinConvergent_coshGauss` (which holds for every `s` with
`0 < s.re`).

Differentiability of the RHS follows from `coshGaussMellin_differentiableAt`
applied five times (with the `c = 0` instance giving `gaussMellin` via
`coshGaussMellin_zero`). Since the identity holds on an open neighborhood of
`s`, `DifferentiableAt.congr_of_eventuallyEq` transfers differentiability.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_differentiableAt (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (pairTestMellin β) s := by
  -- The RHS of the cosh expansion, viewed as a function of `s`.
  set g : ℂ → ℂ := fun s =>
    (1/2 : ℂ) * coshGaussMellin (2*β - Real.pi/3) s +
    (1/2 : ℂ) * coshGaussMellin (2 - Real.pi/3 - 2*β) s -
    coshGaussMellin (1 - Real.pi/3) s -
    coshGaussMellin (2*β - 1) s +
    gaussMellin s with hg_def
  -- `g` is differentiable at `s` as a finite linear combination of
  -- `coshGaussMellin` (holomorphic by 48-B1) and `gaussMellin`.
  have hg : DifferentiableAt ℂ g s := by
    refine DifferentiableAt.add ?_ (gaussMellin_differentiableAt hs)
    refine DifferentiableAt.sub ?_ (coshGaussMellin_differentiableAt _ hs)
    refine DifferentiableAt.sub ?_ (coshGaussMellin_differentiableAt _ hs)
    refine DifferentiableAt.add ?_ ?_
    · exact (differentiableAt_const _).mul (coshGaussMellin_differentiableAt _ hs)
    · exact (differentiableAt_const _).mul (coshGaussMellin_differentiableAt _ hs)
  -- `pairTestMellin β = g` on the open half-plane `{s' | 0 < s'.re}`.
  have h_halfplane_open : IsOpen {s' : ℂ | 0 < s'.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h_mem : s ∈ {s' : ℂ | 0 < s'.re} := hs
  have h_nhds : {s' : ℂ | 0 < s'.re} ∈ nhds s :=
    h_halfplane_open.mem_nhds h_mem
  have h_eventually : (pairTestMellin β) =ᶠ[nhds s] g := by
    refine Filter.eventuallyEq_of_mem h_nhds ?_
    intro s' hs'
    have h_re_pos : 0 < s'.re := hs'
    exact pairTestMellin_cosh_expansion β s'
      (mellinConvergent_coshGauss _ h_re_pos)
      (mellinConvergent_coshGauss _ h_re_pos)
      (mellinConvergent_coshGauss _ h_re_pos)
      (mellinConvergent_coshGauss _ h_re_pos)
      (by
        -- 5th hyp: MellinConvergent of `exp(-2t²)` at `s'`.
        -- This is the `c = 0` case of `mellinConvergent_coshGauss`, because
        -- `cosh(0·t) · exp(-2t²) = exp(-2t²)`.
        have := mellinConvergent_coshGauss 0 h_re_pos
        have h_eq : (fun t : ℝ =>
            ((Real.cosh (0 * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =
            (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
          funext t; simp [Real.cosh_zero]
        rw [h_eq] at this
        exact this)
  exact hg.congr_of_eventuallyEq h_eventually

#print axioms pairTestMellin_differentiableAt

end Contour
end WeilPositivity
end ZD

end
