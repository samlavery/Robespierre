import Mathlib
import RequestProject.CauchyKPairTestPlancherel
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilLeftEdgePrimeSum
import RequestProject.WeilContour
import RequestProject.PairCoshGaussTest
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilArchAtNegOne
import RequestProject.DigammaVerticalBound
import RequestProject.ArchOperatorBound

/-!
# Engineering identity: per-t K_2-twisted vertical-edge analysis (step 1)

Step 1 of the engineering-identity discharge route:

```
K_2(2+iy, t) = (1/2)·e^{3t}·e^{2iyt} + (1/2)·e^{-3t}·e^{-2iyt}
             - e^{(3/2)t}·e^{iyt} - e^{-(3/2)t}·e^{-iyt} + 1
```

Five Fourier components in `y` at the right edge `Re s = 2`, with
constant-in-y coefficients depending on `t`. The analogous expansion at
`Re s = -1` follows from the FE-symmetry `K_2(1-s, t) = K_2(s, t)`.

Subsequent steps lift the existing un-twisted right-edge prime-sum identity
`primeIntegrand_integral_eq_prime_sum` through each Fourier component to
produce the per-t K_2-engineering identity; integration against `e^{-2t²}`
gives the K-engineering identity by Plancherel.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity

/-! ## Step 1: K_2 Fourier expansion at the right edge `Re s = 2` -/

/-- **Right-edge Fourier expansion of `K_2`.**

At `s = 2 + iy`, `s − 1/2 = 3/2 + iy`. Substituting into
`K_2(s,t) = cosh(2(s−1/2)t) − 2·cosh((s−1/2)t) + 1`
and using `cosh z = (e^z + e^{−z})/2` with `Complex.exp_add` to split the
real and imaginary exponential parts gives the 5-Fourier-component form:

```
K_2(2+iy, t) = (1/2)·e^{3t}·e^{2iyt} + (1/2)·e^{−3t}·e^{−2iyt}
             − e^{(3/2)t}·e^{iyt} − e^{−(3/2)t}·e^{−iyt} + 1
```

Each `e^{c·iyt}` is a Fourier component; the constant coefficients
(in `t`, not `y`) are `{(1/2)e^{3t}, (1/2)e^{−3t}, −e^{(3/2)t}, −e^{−(3/2)t}, 1}`. -/
theorem K_2_fourier_expansion_re_two (t : ℝ) (y : ℝ) :
    K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t =
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
      (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I) -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((t * y : ℝ) : ℂ) * I) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((-(t * y) : ℝ) : ℂ) * I) +
      1 := by
  unfold K_2
  -- Setup: s - 1/2 = 3/2 + iy.
  have hsm : (((2 : ℝ) : ℂ) + (y : ℂ) * I) - 1/2 = (3/2 : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  rw [hsm]
  -- 2 * (3/2 + iy) * t = 3t + 2iyt.
  have h2t : 2 * ((3/2 : ℂ) + (y : ℂ) * I) * (t : ℂ) =
      ((3 * t : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I := by push_cast; ring
  -- (3/2 + iy) * t = (3/2)t + iyt.
  have h1t : ((3/2 : ℂ) + (y : ℂ) * I) * (t : ℂ) =
      (((3/2) * t : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I := by push_cast; ring
  rw [h2t, h1t]
  -- cosh z = (exp z + exp(-z)) / 2.
  rw [Complex.cosh, Complex.cosh]
  -- Now expand exp(a + b) = exp(a) · exp(b).
  rw [show ((3 * t : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I =
      ((3 * t : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I from rfl]
  rw [Complex.exp_add]
  rw [show -(((3 * t : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I) =
      ((-(3 * t) : ℝ) : ℂ) + ((-(2 * t * y) : ℝ) : ℂ) * I from by push_cast; ring]
  rw [Complex.exp_add]
  rw [show ((((3/2) * t) : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I =
      ((((3/2) * t) : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I from rfl]
  rw [Complex.exp_add]
  rw [show -(((((3/2) * t) : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I) =
      (((-(3/2) * t) : ℝ) : ℂ) + ((-(t * y) : ℝ) : ℂ) * I from by push_cast; ring]
  rw [Complex.exp_add]
  ring

#print axioms K_2_fourier_expansion_re_two

/-- **Left-edge Fourier expansion of `K_2`.**

At `s = -1 + iy`, `s − 1/2 = -3/2 + iy`. Same y-Fourier components as the
right edge, but with t-coefficients flipped: `e^{±3t} ↔ e^{∓3t}`,
`e^{±(3/2)t} ↔ e^{∓(3/2)t}`:

```
K_2(-1+iy, t) = (1/2)·e^{-3t}·e^{2iyt} + (1/2)·e^{3t}·e^{-2iyt}
              − e^{-(3/2)t}·e^{iyt} − e^{(3/2)t}·e^{-iyt} + 1
```

This is consistent with FE-symmetry `K_2(1-s, t) = K_2(s, t)` and the
substitution `1 - (-1+iy) = 2 - iy`. -/
theorem K_2_fourier_expansion_re_neg_one (t : ℝ) (y : ℝ) :
    K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t =
      (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
          Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((t * y : ℝ) : ℂ) * I) -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((-(t * y) : ℝ) : ℂ) * I) +
      1 := by
  unfold K_2
  -- Setup: s - 1/2 = -3/2 + iy.
  have hsm : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) - 1/2 = (-3/2 : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  rw [hsm]
  -- 2 * (-3/2 + iy) * t = -3t + 2iyt.
  have h2t : 2 * ((-3/2 : ℂ) + (y : ℂ) * I) * (t : ℂ) =
      ((-(3 * t) : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I := by push_cast; ring
  -- (-3/2 + iy) * t = -(3/2)t + iyt.
  have h1t : ((-3/2 : ℂ) + (y : ℂ) * I) * (t : ℂ) =
      (((-(3/2)) * t : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I := by push_cast; ring
  rw [h2t, h1t]
  rw [Complex.cosh, Complex.cosh]
  rw [show ((-(3 * t) : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I =
      ((-(3 * t) : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I from rfl]
  rw [Complex.exp_add]
  rw [show -(((-(3 * t) : ℝ) : ℂ) + ((2 * t * y : ℝ) : ℂ) * I) =
      ((3 * t : ℝ) : ℂ) + ((-(2 * t * y) : ℝ) : ℂ) * I from by push_cast; ring]
  rw [Complex.exp_add]
  rw [show (((-(3/2)) * t : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I =
      (((-(3/2) * t) : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I from by push_cast; ring]
  rw [Complex.exp_add]
  rw [show -((((-(3/2) * t) : ℝ) : ℂ) + ((t * y : ℝ) : ℂ) * I) =
      ((((3/2) * t) : ℝ) : ℂ) + ((-(t * y) : ℝ) : ℂ) * I from by push_cast; ring]
  rw [Complex.exp_add]
  ring

#print axioms K_2_fourier_expansion_re_neg_one

/-! ## Step 3a: Shifted Mellin inversion at `Re s = 2` -/

/-- **Shifted Mellin inversion.**

```
∫_y e^{iyα}·M(β, 2+iy) dy = 2π · e^{-2α} · test_β(e^{-α})
```

Specialization of `pairTestMellin_vertical_integral_at_pos` at `x = e^{-α}`.
For any real `α`, the shift `e^{iyα}` of the right-edge Mellin pairing factors
out as `e^{-2α}·test_β(e^{-α})` after Mellin inversion. -/
theorem mellin_shifted_re_two (β : ℝ) (α : ℝ) :
    ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (Real.exp (-α)) : ℝ) : ℂ) := by
  set x : ℝ := Real.exp (-α) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have hxC_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos)
  have h_inv := Contour.pairTestMellin_vertical_integral_at_pos β 2
    (by norm_num : (0:ℝ) < 2) hx_pos
  -- log(x : ℂ) = -α (as complex).  Use ofReal_exp + log_exp.
  have hlogx : Complex.log (x : ℂ) = ((-α : ℝ) : ℂ) := by
    have hx_eq : (x : ℂ) = Complex.exp ((-α : ℝ) : ℂ) := Complex.ofReal_exp _
    rw [hx_eq]
    apply Complex.log_exp
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  -- (x:ℂ)^(-(2+yI)) = e^{2α}·e^{iyα}.
  -- cpow def: x^z = exp(log x · z).  log x = -α, z = -(2+yI),
  -- so log x · z = -α · -(2+yI) = α·(2+yI) = 2α + αyI = 2α + (yα)I.
  have hx_pow : ∀ y : ℝ,
      ((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((Real.exp (2 * α) : ℝ) : ℂ) * Complex.exp (((y * α : ℝ) : ℂ) * I) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero hxC_ne, hlogx]
    -- Goal: cexp (((-α:ℝ):ℂ) * -(2 + yI)) = ((Real.exp (2α)):ℂ) * cexp ((yα:ℂ)I)
    rw [show ((-α : ℝ) : ℂ) * (-(((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ((2 * α : ℝ) : ℂ) + ((y * α : ℝ) : ℂ) * I from by push_cast; ring]
    rw [Complex.exp_add]
    congr 1
    exact (Complex.ofReal_exp _).symm
  -- Use hx_pow to rewrite h_inv.  Match casts: 2 * ↑Real.pi vs ↑(2 * Real.pi).
  have h_inv' : ∫ y : ℝ, ((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    have h := h_inv
    push_cast at h ⊢
    linear_combination h
  -- Replace the cpow factor.
  have h_inv2 : ∫ y : ℝ, ((Real.exp (2 * α) : ℝ) : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    rw [show
      (fun y : ℝ => ((Real.exp (2 * α) : ℝ) : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I)))
      = fun y : ℝ => ((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) from by
        funext y; rw [hx_pow]; ring]
    exact h_inv'
  -- Pull out the constant from the integral.
  have h_pull : (∫ y : ℝ, ((Real.exp (2 * α) : ℝ) : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((Real.exp (2 * α) : ℝ) : ℂ) *
        ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) :=
    MeasureTheory.integral_const_mul _ _
  rw [h_pull] at h_inv2
  -- h_inv2 : e^{2α} · ∫ ... = 2π · test β(x).
  -- Divide by e^{2α}.
  have he2α_ne : ((Real.exp (2 * α) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have h_eq_eα_inv : ((Real.exp (2 * α) : ℝ) : ℂ)⁻¹ =
      ((Real.exp (-2 * α) : ℝ) : ℂ) := by
    have hr : Real.exp (-2 * α) = (Real.exp (2 * α))⁻¹ := by
      rw [show (-2 * α : ℝ) = -(2 * α) from by ring, Real.exp_neg]
    rw [hr]; push_cast; rfl
  calc ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.exp (2 * α) : ℝ) : ℂ)⁻¹ *
          (((Real.exp (2 * α) : ℝ) : ℂ) *
            ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
              Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        rw [← mul_assoc, inv_mul_cancel₀ he2α_ne, one_mul]
    _ = ((Real.exp (2 * α) : ℝ) : ℂ)⁻¹ *
          (((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ)) := by
        rw [h_inv2]
    _ = ((Real.exp (-2 * α) : ℝ) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ)) := by
        rw [h_eq_eα_inv]
    _ = ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by ring

#print axioms mellin_shifted_re_two

/-! ## Step 3b: Per-n shifted right-edge integral -/

/-- **Per-n shifted right-edge integral.**

For `n ≥ 1` and `α : ℝ`,
```
∫_t e^{itα}·Λ(n)·(n:ℂ)^(-(2+ti))·M(β, 2+ti) dt
  = 2π·e^{-2α}·Λ(n)·test_β(n·e^{-α})
```

Proof: substitute `x = n·e^{-α}` and observe
`e^{itα}·(n:ℂ)^(-(2+ti)) = e^{-2α}·(x:ℂ)^(-(2+ti))` (algebraic
identity using `log x = log n − α`), then apply
`pairTestMellin_vertical_integral_at_pos` at `x`. -/
private lemma shifted_per_n_integral (β α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ t : ℝ, Complex.exp (((t * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ) := by
  set x : ℝ := (n : ℝ) * Real.exp (-α) with hx_def
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx_pos : 0 < x := mul_pos hn_pos (Real.exp_pos _)
  have hxC_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hnC_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  -- Key algebraic identity: e^{itα}·n^{-(2+ti)} = e^{-2α}·x^{-(2+ti)}.
  have h_key : ∀ t : ℝ,
      Complex.exp (((t * α : ℝ) : ℂ) * I) *
        ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) =
      ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero hnC_ne, Complex.cpow_def_of_ne_zero hxC_ne]
    -- log n and log x as real casts.
    have hlog_n : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      have h1 : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [h1]; exact (Complex.ofReal_log (Nat.cast_nonneg _)).symm
    have hlog_x : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) :=
      (Complex.ofReal_log hx_pos.le).symm
    rw [hlog_n, hlog_x]
    -- Real.log x = Real.log n + (-α).
    have hlog_x_real : Real.log x = Real.log n + (-α) := by
      rw [hx_def]
      rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn))
          (Real.exp_ne_zero _)]
      rw [Real.log_exp]
    rw [show ((Real.log x : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) + ((-α : ℝ) : ℂ) from by
      rw [hlog_x_real]; push_cast; ring]
    -- Distribute and split the exponent.
    rw [show (((Real.log n : ℝ) : ℂ) + ((-α : ℝ) : ℂ)) *
        (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ((Real.log n : ℝ) : ℂ) * (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) +
        ((-α : ℝ) : ℂ) * (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) from by ring]
    rw [Complex.exp_add]
    -- (-α)·-(2+ti) = α(2+ti) = 2α + αt·I.
    rw [show ((-α : ℝ) : ℂ) * (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ((2 * α : ℝ) : ℂ) + ((t * α : ℝ) : ℂ) * I from by push_cast; ring]
    rw [Complex.exp_add]
    -- exp((2α : ℝ) : ℂ) = ((Real.exp (2α)) : ℂ).
    rw [show Complex.exp (((2 * α : ℝ) : ℂ)) = ((Real.exp (2 * α) : ℝ) : ℂ) from
      (Complex.ofReal_exp _).symm]
    -- Cancellation: e^{-2α}·e^{2α} = 1.
    have hcancel : ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ((Real.exp (2 * α) : ℝ) : ℂ) = 1 := by
      have hr : Real.exp (-2 * α) * Real.exp (2 * α) = 1 := by
        rw [show (-2 * α : ℝ) = -(2 * α) from by ring, Real.exp_neg,
          inv_mul_cancel₀ (Real.exp_ne_zero _)]
      exact_mod_cast hr
    -- LHS = e^{itα}·L where L = exp(log n · -(2+ti)).
    -- RHS = e^{-2α} · (L · (e^{2α} · e^{itα})). Use cancellation.
    set L : ℂ := Complex.exp (((Real.log n : ℝ) : ℂ) *
      (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) with hL_def
    set a : ℂ := Complex.exp (((t * α : ℝ) : ℂ) * I) with ha_def
    show a * L = ((Real.exp (-2 * α) : ℝ) : ℂ) *
      (L * (((Real.exp (2 * α) : ℝ) : ℂ) * a))
    calc a * L
        = (((Real.exp (-2 * α) : ℝ) : ℂ) *
            ((Real.exp (2 * α) : ℝ) : ℂ)) * (L * a) := by
            rw [hcancel]; ring
      _ = ((Real.exp (-2 * α) : ℝ) : ℂ) *
            (L * (((Real.exp (2 * α) : ℝ) : ℂ) * a)) := by ring
  -- Use h_key to rewrite the integrand.
  have h_rewrite :
      (fun t : ℝ => Complex.exp (((t * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I))) =
      (fun t : ℝ =>
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((Real.exp (-2 * α) : ℝ) : ℂ)) *
        (((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I))) := by
    funext t
    have := h_key t
    -- LHS: e^{itα} · (Λ(n) · n^{-(2+ti)} · M)
    -- RHS: (Λ(n) · e^{-2α}) · (x^{-(2+ti)} · M)
    rw [show Complex.exp (((t * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Complex.exp (((t * α : ℝ) : ℂ) * I) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I) from by ring]
    rw [this]
    ring
  rw [h_rewrite]
  -- Pull constant out of integral.
  have h_pull : ∫ t : ℝ, ((ArithmeticFunction.vonMangoldt n : ℂ) *
        ((Real.exp (-2 * α) : ℝ) : ℂ)) *
        (((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        ((Real.exp (-2 * α) : ℝ) : ℂ)) *
        ∫ t : ℝ, (((x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    MeasureTheory.integral_const_mul _ _
  rw [h_pull]
  have h_vert := Contour.pairTestMellin_vertical_integral_at_pos β 2
    (by norm_num : (0:ℝ) < 2) hx_pos
  rw [h_vert]
  push_cast
  ring

#print axioms shifted_per_n_integral

/-! ## Step 3c: Full Fubini assembly — shifted right-edge prime sum identity -/

/-- **Shifted right-edge prime-sum identity.**

For any real `α`,
```
∫_y e^{iy·α}·primeIntegrand β 2 y dy
  = 2π · e^{-2α} · Σ' n, Λ(n)·test_β(n·e^{-α})
```

The Fourier shift `e^{iy·α}` lifts the right-edge identity
`primeIntegrand_integral_eq_prime_sum` term-by-term via `shifted_per_n_integral`.
The Fubini swap is via `MeasureTheory.integral_tsum_of_summable_integral_norm`,
mirroring the un-shifted template.  Norm bound `|e^{iy·α}| = 1` makes the
integrability/summability transfer trivial. -/
theorem primeIntegrand_shifted_integral_eq_prime_sum (β α : ℝ) :
    ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ) := by
  -- Per-y integrand: the shifted F.
  set F : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (((2 : ℝ) : ℂ) + (y : ℂ) * I) n *
      Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hF_def
  set G : ℕ → ℝ → ℂ := fun n y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) * F n y with hG_def
  -- Pointwise: e^{iyα} · primeIntegrand = Σ' n, G n y.
  have hp : ∀ y : ℝ, Contour.primeIntegrand β 2 y = ∑' n : ℕ, F n y := by
    intro y
    unfold Contour.primeIntegrand
    rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) =
            ∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) n from rfl]
    rw [tsum_mul_right]
  have h_pt : ∀ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.primeIntegrand β 2 y =
        ∑' n : ℕ, G n y := by
    intro y
    rw [hp y]
    show Complex.exp (((y * α : ℝ) : ℂ) * I) * (∑' n, F n y) =
      ∑' n, Complex.exp (((y * α : ℝ) : ℂ) * I) * F n y
    rw [← tsum_mul_left]
  -- Norm: ‖G n y‖ = ‖F n y‖ since |e^{iyα}| = 1.
  have h_norm_G : ∀ n : ℕ, ∀ y : ℝ, ‖G n y‖ = ‖F n y‖ := by
    intro n y
    show ‖Complex.exp (((y * α : ℝ) : ℂ) * I) * F n y‖ = ‖F n y‖
    rw [norm_mul]
    rw [show Complex.exp (((y * α : ℝ) : ℂ) * I) =
        Complex.exp (((y * α : ℝ) : ℝ) * I) from rfl]
    have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [show ((y * α : ℝ) : ℂ) * I = (((y * α : ℝ) : ℝ) : ℂ) * I from rfl]
      rw [Complex.norm_exp]
      simp
    rw [h_unit, one_mul]
  -- Each G n integrable.
  have h_G_int : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    have h_F_int : MeasureTheory.Integrable (F n) :=
      Contour.lseries_term_pairTestMellin_integrable β 2 (by norm_num : (1:ℝ) < 2) n
    -- G n = e^{iyα} · F n; bounded multiplier on integrable function.
    have h_exp_bdd : ∀ y : ℝ,
        ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ ≤ 1 := fun y => by
      rw [Complex.norm_exp]; simp
    have h_exp_meas : MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
      have : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
        exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
            continuous_const)
      exact this.aestronglyMeasurable
    -- ‖G n y‖ ≤ 1 · ‖F n y‖.
    refine MeasureTheory.Integrable.mono h_F_int (h_exp_meas.mul h_F_int.aestronglyMeasurable) ?_
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show ‖Complex.exp (((y * α : ℝ) : ℂ) * I) * F n y‖ ≤ ‖F n y‖
    rw [norm_mul]
    have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h_unit, one_mul]
  -- Σ ∫ ‖G n‖ summable.
  have h_G_L1_summ : Summable (fun n : ℕ => ∫ y : ℝ, ‖G n y‖) := by
    have h_eq : (fun n : ℕ => ∫ y : ℝ, ‖G n y‖) =
                (fun n : ℕ => ∫ y : ℝ, ‖F n y‖) := by
      funext n
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      exact h_norm_G n y
    rw [h_eq]
    -- Use the un-shifted L¹ bound.
    obtain ⟨M, hM_nn, h_bd⟩ :=
      Contour.lseries_term_pairTestMellin_L1_bounded β 2 (by norm_num : (1:ℝ) < 2)
    have h_bound_summ : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * M) := by
      have h_div := Contour.summable_vonMangoldt_rpow 2 (by norm_num : (1:ℝ) < 2)
      have h_eq2 : (fun n : ℕ =>
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * M) =
          (fun n : ℕ =>
            (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^(2:ℝ) * M) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [ArithmeticFunction.map_zero]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
      rw [h_eq2]; exact h_div.mul_right M
    refine h_bound_summ.of_nonneg_of_le ?_ ?_
    · intro n; exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    · exact h_bd
  -- Fubini swap.
  have h_fubini : (∫ y : ℝ, ∑' n : ℕ, G n y) = ∑' n : ℕ, ∫ y : ℝ, G n y :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm h_G_int h_G_L1_summ).symm
  -- Per-n integral via shifted_per_n_integral.
  have h_per_n : ∀ n : ℕ, ∫ y : ℝ, G n y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : (fun y : ℝ => G 0 y) = (fun _ : ℝ => (0 : ℂ)) := by
        funext y
        show Complex.exp (((y * α : ℝ) : ℂ) * I) * F 0 y = 0
        rw [show F 0 y = 0 from by simp [hF_def, LSeries.term_zero]]
        ring
      rw [h_zero, MeasureTheory.integral_zero]
      simp [ArithmeticFunction.map_zero]
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have h_term_eq : ∀ y : ℝ, G n y =
          Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        intro y
        show Complex.exp (((y * α : ℝ) : ℂ) * I) * F n y =
          Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I))
        rw [show F n y = LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) n *
              Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) from rfl]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
      rw [show (fun y : ℝ => G n y) = (fun y : ℝ =>
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I))) from by
        funext y; exact h_term_eq y]
      exact shifted_per_n_integral β α n hpos
  -- Assembly.
  calc ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.primeIntegrand β 2 y
      = ∫ y : ℝ, ∑' n : ℕ, G n y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact h_pt y
    _ = ∑' n : ℕ, ∫ y : ℝ, G n y := h_fubini
    _ = ∑' n : ℕ, (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ)) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ)) := by
        apply tsum_congr
        intro n
        rw [h_per_n n]; ring
    _ = (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ)) *
          ∑' n : ℕ,
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ)) := by
        rw [← tsum_mul_left]
    _ = ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * α) : ℝ) : ℂ) *
          ∑' n : ℕ,
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-α)) : ℝ) : ℂ)) := by ring

#print axioms primeIntegrand_shifted_integral_eq_prime_sum

/-! ## Step 3d: K_2-twisted right-edge prime-sum formula

The next step assembles `∫ y, K_2(2+iy, t) · primeIntegrand β 2 y dy` by:
- substituting `K_2_fourier_expansion_re_two`,
- splitting via integral linearity into 5 pieces,
- applying `primeIntegrand_shifted_integral_eq_prime_sum` at
  `α ∈ {2t, -2t, t, -t, 0}`,
- combining `e^{(coeff·t)} · 2π · e^{-2α}` exponential factors via
  `Complex.exp_add` to get the canonical prefactors `π·e^{∓t}`,
  `2π·e^{∓t/2}`, `2π`.

The result is the explicit prime-side formula
`vert2_{K_2}(t) = π·e^{-t}·Σ Λ·test(n e^{-2t}) + π·e^{t}·Σ Λ·test(n e^{2t})
  − 2π·e^{-t/2}·Σ Λ·test(n e^{-t}) − 2π·e^{t/2}·Σ Λ·test(n e^{t})
  + 2π·Σ Λ·test(n)`
matching the user's plan. -/

/-- Helper: the prime integrand at `Re s = 2` is integrable. -/
private lemma primeIntegrand_integrable_re_two (β : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => Contour.primeIntegrand β 2 y) :=
  Contour.primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)

/-- Helper: shifted prime integrand integrable. -/
private lemma primeIntegrand_shift_integrable (β α : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y) := by
  have h_F_int := primeIntegrand_integrable_re_two β
  have h_exp_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
    have : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
          continuous_const)
    exact this.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono h_F_int
    (h_exp_meas.mul h_F_int.aestronglyMeasurable) ?_
  refine MeasureTheory.ae_of_all _ fun y => ?_
  rw [norm_mul]
  have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [h_unit, one_mul]

/-- **K_2-twisted right-edge integral via Fourier components.**

For every `t : ℝ` and `β : ℝ`, by `K_2_fourier_expansion_re_two`,
`K_2(2+iy, t) · primeIntegrand β 2 y` decomposes pointwise into
5 Fourier components.  Each component's integral is given by
`primeIntegrand_shifted_integral_eq_prime_sum`.  The full integral
linearity step + arithmetic match `(1/2)e^{3t}·2π·e^{-4t} = π·e^{-t}` etc.
combines these into the explicit prime-side formula

```
vert2_{K_2}(t) = π·e^{-t}·Σ Λ·test(n e^{-2t}) + π·e^{t}·Σ Λ·test(n e^{2t})
              − 2π·e^{-t/2}·Σ Λ·test(n e^{-t}) − 2π·e^{t/2}·Σ Λ·test(n e^{t})
              + 2π·Σ Λ·test(n).
```

The 5 individual prime-sum evaluations are below as a stepping-stone. -/
theorem vert2_K2_fourier_components (t β : ℝ) :
    (∫ y : ℝ, Complex.exp (((y * (2*t) : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (2*t)) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(2*t))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * (-(2*t)) : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (-(2*t))) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(-(2*t)))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-t)) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
        Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (-t)) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(-t))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Contour.primeIntegrand β 2 y =
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact primeIntegrand_shifted_integral_eq_prime_sum β (2*t)
  · exact primeIntegrand_shifted_integral_eq_prime_sum β (-(2*t))
  · exact primeIntegrand_shifted_integral_eq_prime_sum β t
  · exact primeIntegrand_shifted_integral_eq_prime_sum β (-t)
  · -- For α = 0: the shifted version simplifies via exp 0 = 1.
    have h_zero := primeIntegrand_shifted_integral_eq_prime_sum β 0
    have h_lhs_eq : ∫ y : ℝ, Contour.primeIntegrand β 2 y =
        ∫ y : ℝ, Complex.exp (((y * 0 : ℝ) : ℂ) * I) *
          Contour.primeIntegrand β 2 y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [show ((y * 0 : ℝ) : ℂ) * I = 0 from by push_cast; ring,
        Complex.exp_zero, one_mul]
    rw [h_lhs_eq, h_zero]
    simp [Real.exp_zero, neg_zero, mul_zero]

#print axioms vert2_K2_fourier_components

/-- **Helper: integral of 5-term linear combination splits into 5 integrals.** -/
private lemma integral_5_linear_combination (f1 f2 f3 f4 f5 : ℝ → ℂ)
    (c1 c2 c3 c4 : ℂ)
    (h1 : MeasureTheory.Integrable f1) (h2 : MeasureTheory.Integrable f2)
    (h3 : MeasureTheory.Integrable f3) (h4 : MeasureTheory.Integrable f4)
    (h5 : MeasureTheory.Integrable f5) :
    ∫ y : ℝ, c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y =
      c1 * (∫ y, f1 y) + c2 * (∫ y, f2 y) - c3 * (∫ y, f3 y) - c4 * (∫ y, f4 y) +
        (∫ y, f5 y) := by
  have hI1 : MeasureTheory.Integrable (fun y => c1 * f1 y) := h1.const_mul c1
  have hI2 : MeasureTheory.Integrable (fun y => c2 * f2 y) := h2.const_mul c2
  have hI3 : MeasureTheory.Integrable (fun y => c3 * f3 y) := h3.const_mul c3
  have hI4 : MeasureTheory.Integrable (fun y => c4 * f4 y) := h4.const_mul c4
  have hI12 : MeasureTheory.Integrable (fun y => c1 * f1 y + c2 * f2 y) := hI1.add hI2
  have hI123 : MeasureTheory.Integrable
      (fun y => c1 * f1 y + c2 * f2 y - c3 * f3 y) := hI12.sub hI3
  have hI1234 : MeasureTheory.Integrable
      (fun y => c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y) := hI123.sub hI4
  rw [MeasureTheory.integral_add hI1234 h5]
  rw [MeasureTheory.integral_sub hI123 hI4]
  rw [MeasureTheory.integral_sub hI12 hI3]
  rw [MeasureTheory.integral_add hI1 hI2]
  rw [show (∫ a : ℝ, c1 * f1 a) = c1 * ∫ y : ℝ, f1 y from
    MeasureTheory.integral_const_mul c1 f1]
  rw [show (∫ a : ℝ, c2 * f2 a) = c2 * ∫ y : ℝ, f2 y from
    MeasureTheory.integral_const_mul c2 f2]
  rw [show (∫ a : ℝ, c3 * f3 a) = c3 * ∫ y : ℝ, f3 y from
    MeasureTheory.integral_const_mul c3 f3]
  rw [show (∫ a : ℝ, c4 * f4 a) = c4 * ∫ y : ℝ, f4 y from
    MeasureTheory.integral_const_mul c4 f4]

/-- **K_2-twisted right-edge prime-sum formula.**

For every `t : ℝ` and `β : ℝ`,
```
∫_y K_2(2+iy, t) · primeIntegrand β 2 y dy
  = π·e^{-t}·Σ Λ·test(n·e^{-2t}) + π·e^{t}·Σ Λ·test(n·e^{2t})
  − 2π·e^{-t/2}·Σ Λ·test(n·e^{-t}) − 2π·e^{t/2}·Σ Λ·test(n·e^{t})
  + 2π·Σ Λ·test(n).
```

Combines `K_2_fourier_expansion_re_two`, the 5 prime-sum evaluations
in `vert2_K2_fourier_components`, and `integral_5_linear_combination` for the
linearity step, then matches prefactors via `Complex.exp_add`. -/
theorem K_2_primeIntegrand_re_two_eq (t β : ℝ) :
    ∫ y : ℝ, K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.primeIntegrand β 2 y =
      ((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(2*t))) : ℝ) : ℂ) +
      ((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (2*t)) : ℝ) : ℂ) -
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-t)) : ℝ) : ℂ) -
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp t) : ℝ) : ℂ) +
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  -- Define the 5 base shifted integrands.
  set f1 : ℝ → ℂ := fun y => Complex.exp (((y * (2*t) : ℝ) : ℂ) * I) *
      Contour.primeIntegrand β 2 y with hf1_def
  set f2 : ℝ → ℂ := fun y => Complex.exp (((y * (-(2*t)) : ℝ) : ℂ) * I) *
      Contour.primeIntegrand β 2 y with hf2_def
  set f3 : ℝ → ℂ := fun y => Complex.exp (((y * t : ℝ) : ℂ) * I) *
      Contour.primeIntegrand β 2 y with hf3_def
  set f4 : ℝ → ℂ := fun y => Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
      Contour.primeIntegrand β 2 y with hf4_def
  set f5 : ℝ → ℂ := fun y => Contour.primeIntegrand β 2 y with hf5_def
  -- Coefficients in t.
  set c1 : ℂ := (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) with hc1_def
  set c2 : ℂ := (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) with hc2_def
  set c3 : ℂ := Complex.exp ((((3/2) * t) : ℝ) : ℂ) with hc3_def
  set c4 : ℂ := Complex.exp (((-(3/2) * t) : ℝ) : ℂ) with hc4_def
  -- K_2 expansion gives K_2 · primeIntegrand = c1·f1 + c2·f2 - c3·f3 - c4·f4 + f5.
  have h_decomp : ∀ y : ℝ, K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.primeIntegrand β 2 y =
      c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y := by
    intro y
    rw [K_2_fourier_expansion_re_two t y]
    have h_match1 : ((2 * t * y : ℝ) : ℂ) = ((y * (2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match2 : ((-(2 * t * y) : ℝ) : ℂ) = ((y * -(2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match3 : ((t * y : ℝ) : ℂ) = ((y * t : ℝ) : ℂ) := by push_cast; ring
    have h_match4 : ((-(t * y) : ℝ) : ℂ) = ((y * -t : ℝ) : ℂ) := by push_cast; ring
    rw [h_match1, h_match2, h_match3, h_match4]
    show _ = c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y
    rw [hc1_def, hc2_def, hc3_def, hc4_def, hf1_def, hf2_def, hf3_def, hf4_def, hf5_def]
    ring
  -- Rewrite the integrand.
  rw [show (fun y : ℝ => K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.primeIntegrand β 2 y) =
      (fun y : ℝ => c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y) from
    funext h_decomp]
  -- Apply linearity.
  have h_int1 : MeasureTheory.Integrable f1 := primeIntegrand_shift_integrable β (2*t)
  have h_int2 : MeasureTheory.Integrable f2 := primeIntegrand_shift_integrable β (-(2*t))
  have h_int3 : MeasureTheory.Integrable f3 := primeIntegrand_shift_integrable β t
  have h_int4 : MeasureTheory.Integrable f4 := primeIntegrand_shift_integrable β (-t)
  have h_int5 : MeasureTheory.Integrable f5 := primeIntegrand_integrable_re_two β
  rw [integral_5_linear_combination f1 f2 f3 f4 f5 c1 c2 c3 c4
    h_int1 h_int2 h_int3 h_int4 h_int5]
  -- Apply per-α formulas.
  obtain ⟨he1, he2, he3, he4, he5⟩ := vert2_K2_fourier_components t β
  -- Unfold f1..f5 in the goal so he1..he5 (in unfolded form) apply.
  simp only [hf1_def, hf2_def, hf3_def, hf4_def, hf5_def]
  rw [he1, he2, he3, he4, he5]
  -- Arithmetic: combine prefactors.
  rw [hc1_def, hc2_def, hc3_def, hc4_def]
  -- Each c_i * (2π · e^{-2α_i}) = canonical prefactor.
  have he_neg_t : (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (2*t)) : ℝ) : ℂ)) =
      ((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp ((3 * t : ℝ) : ℂ) *
        ((Real.exp (-2 * (2*t)) : ℝ) : ℂ) = ((Real.exp (-t) : ℝ) : ℂ) := by
      rw [show ((Real.exp (-2 * (2*t)) : ℝ) : ℂ) =
          Complex.exp (((-2 * (2*t)) : ℝ) : ℂ) from Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((3 * t : ℝ) : ℂ) + (((-2 * (2*t)) : ℝ) : ℂ)) =
          ((-t : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination Real.pi * h_exp_combine
  have he_t : (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (-(2*t))) : ℝ) : ℂ)) =
      ((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        ((Real.exp (-2 * (-(2*t))) : ℝ) : ℂ) = ((Real.exp t : ℝ) : ℂ) := by
      rw [show ((Real.exp (-2 * (-(2*t))) : ℝ) : ℂ) =
          Complex.exp (((-2 * (-(2*t))) : ℝ) : ℂ) from Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((-(3 * t) : ℝ) : ℂ) + (((-2 * (-(2*t))) : ℝ) : ℂ)) =
          ((t : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination Real.pi * h_exp_combine
  have he_neg_t2 : Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ)) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        ((Real.exp (-2 * t) : ℝ) : ℂ) = ((Real.exp (-(t/2)) : ℝ) : ℂ) := by
      rw [show ((Real.exp (-2 * t) : ℝ) : ℂ) =
          Complex.exp (((-2 * t) : ℝ) : ℂ) from Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show ((((3/2) * t) : ℝ) : ℂ) + (((-2 * t) : ℝ) : ℂ) =
          ((-(t/2) : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination 2 * Real.pi * h_exp_combine
  have he_t2 : Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-2 * (-t)) : ℝ) : ℂ)) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        ((Real.exp (-2 * (-t)) : ℝ) : ℂ) = ((Real.exp (t/2) : ℝ) : ℂ) := by
      rw [show ((Real.exp (-2 * (-t)) : ℝ) : ℂ) =
          Complex.exp (((-2 * (-t)) : ℝ) : ℂ) from Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((-(3/2) * t) : ℝ) : ℂ) + (((-2 * (-t)) : ℝ) : ℂ) =
          ((t/2 : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination 2 * Real.pi * h_exp_combine
  -- Massage to match canonical form.
  push_cast
  push_cast at he_neg_t he_t he_neg_t2 he_t2
  -- Note: each summand has the form (c_i) * (2π·e^{-2α_i}) * Σ which equals (canonical prefactor) * Σ.
  -- And on the RHS the canonical form uses e^{-(-2t)} = e^{2t} etc.  We use ring after substitutions.
  have hsimp_neg2t : Real.exp (-(-(2*t))) = Real.exp (2*t) := by
    rw [neg_neg]
  have hsimp_negt : Real.exp (-(-t)) = Real.exp t := by rw [neg_neg]
  rw [hsimp_neg2t, hsimp_negt]
  linear_combination
    he_neg_t * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(2*t))) : ℝ) : ℂ))
    + he_t * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (2*t)) : ℝ) : ℂ))
    - he_neg_t2 * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-t)) : ℝ) : ℂ))
    - he_t2 * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp t) : ℝ) : ℂ))

#print axioms K_2_primeIntegrand_re_two_eq

/-! ## Step 4a: Generic Mellin inversion at the left edge `Re s = -1` -/

/-- **Generic Mellin inversion at `Re s = -1`.**

For any `x > 0`, `mellinInv (-1) (pairTestMellin β) x = (pair_cosh_gauss_test β x : ℂ)`.

Mirrors `mellinInv_pairTestMellin_eq` (which is at `Re s > 0`); the
left-edge version uses `mellinConvergent_pair_extended` (convergence
extends to `Re s > -4` due to the `t^4` decay of `pair_cosh_gauss_test`
at 0) and `pairTestMellin_vertical_integrable_at_neg_one`. -/
private lemma mellinInv_pairTestMellin_at_neg_one (β : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv (-1 : ℝ) (Contour.pairTestMellin β) x =
      ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
  have h_mellin_eq : mellin (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) =
      Contour.pairTestMellin β := by funext s; rfl
  have h_conv : MellinConvergent
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) :=
    LeftEdgePrimeSum.mellinConvergent_pair_extended β
      (by simp : -4 < (((-1 : ℝ) : ℂ)).re)
  have h_vint : Complex.VerticalIntegrable
      (mellin (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ))) (-1)
        MeasureTheory.volume := by
    rw [h_mellin_eq]
    exact LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
  have h_cont : ContinuousAt
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) x := by
    exact Complex.continuous_ofReal.continuousAt.comp
      (Contour.pair_cosh_gauss_test_continuous β).continuousAt
  have := mellinInv_mellin_eq (-1 : ℝ)
    (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) hx h_conv h_vint h_cont
  rw [h_mellin_eq] at this
  exact this

/-- **Vertical integral form at `Re s = -1` for any positive `x`.**

```
∫ t, (x:ℂ)^(-(-1+ti)) · M(β, -1+ti) dt = 2π · test_β(x)
```

Mirrors `pairTestMellin_vertical_integral_at_pos` at the left edge. -/
private lemma pairTestMellin_vertical_integral_at_neg_one_pos
    (β : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (t : ℂ) * I))) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I) =
    (2 * Real.pi : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
  have h_inv := mellinInv_pairTestMellin_at_neg_one β hx
  rw [mellinInv] at h_inv
  have h_inner :
      (fun y : ℝ => ((x : ℝ) : ℂ) ^ (-(((-1 : ℝ) : ℂ) + y * I)) •
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + y * I)) =
      (fun t : ℝ => ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    funext t; rfl
  rw [h_inner] at h_inv
  have h_inv' : (((1 / (2 * Real.pi) : ℝ)) : ℂ) *
      (∫ (t : ℝ), ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (t : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    rw [← Complex.real_smul]; exact h_inv
  have h_mul : ((2 * Real.pi : ℝ) : ℂ) *
      ((((1 / (2 * Real.pi) : ℝ)) : ℂ) *
        (∫ (t : ℝ), ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (t : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I))) =
      ((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by rw [h_inv']
  rw [← mul_assoc] at h_mul
  have h_cancel : ((2 * Real.pi : ℝ) : ℂ) * (((1 / (2 * Real.pi) : ℝ)) : ℂ) = 1 := by
    push_cast; field_simp
  rw [h_cancel, one_mul] at h_mul
  push_cast at h_mul ⊢
  linear_combination h_mul

/-- **Shifted Mellin inversion at the left edge.**

```
∫_y e^{iyα}·M(β, -1+iy) dy = 2π · e^α · test_β(e^{-α})
```

Specialization of `pairTestMellin_vertical_integral_at_neg_one_pos` at
`x = e^{-α}`.  Note the prefactor `e^α` (vs `e^{-2α}` at the right edge)
arises because `(e^{-α})^{-(-1+yi)} = e^{-α}·e^{iyα}`, so dividing the
identity by `e^{-α}` gives the `e^α = (e^{-α})^{-1}` prefactor. -/
theorem mellin_shifted_re_neg_one (β : ℝ) (α : ℝ) :
    ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (Real.exp (-α)) : ℝ) : ℂ) := by
  set x : ℝ := Real.exp (-α) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have hxC_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have h_inv := pairTestMellin_vertical_integral_at_neg_one_pos β hx_pos
  -- log(x : ℂ) = -α.
  have hlogx : Complex.log (x : ℂ) = ((-α : ℝ) : ℂ) := by
    have hx_eq : (x : ℂ) = Complex.exp ((-α : ℝ) : ℂ) := Complex.ofReal_exp _
    rw [hx_eq]
    apply Complex.log_exp
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  -- Algebra: x^(-(-1+yi)) = e^{-α} · e^{iyα}.
  have hx_pow : ∀ y : ℝ,
      ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((Real.exp (-α) : ℝ) : ℂ) * Complex.exp (((y * α : ℝ) : ℂ) * I) := by
    intro y
    rw [Complex.cpow_def_of_ne_zero hxC_ne, hlogx]
    rw [show ((-α : ℝ) : ℂ) * (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ((-α : ℝ) : ℂ) + ((y * α : ℝ) : ℂ) * I from by push_cast; ring]
    rw [Complex.exp_add]
    congr 1
    exact (Complex.ofReal_exp _).symm
  -- Apply hx_pow to h_inv.
  have h_inv' : ∫ y : ℝ, ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    have h := h_inv
    push_cast at h ⊢
    linear_combination h
  have h_inv2 : ∫ y : ℝ, ((Real.exp (-α) : ℝ) : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    rw [show
      (fun y : ℝ => ((Real.exp (-α) : ℝ) : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
      = fun y : ℝ => ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) from by
        funext y; rw [hx_pow]; ring]
    exact h_inv'
  -- Pull the constant.
  have h_pull : (∫ y : ℝ, ((Real.exp (-α) : ℝ) : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ((Real.exp (-α) : ℝ) : ℂ) *
        ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) :=
    MeasureTheory.integral_const_mul _ _
  rw [h_pull] at h_inv2
  -- Divide by e^{-α} ≠ 0.
  have he_ne : ((Real.exp (-α) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have h_eq_eα_inv : ((Real.exp (-α) : ℝ) : ℂ)⁻¹ = ((Real.exp α : ℝ) : ℂ) := by
    have hr : Real.exp α = (Real.exp (-α))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [hr]; push_cast; rfl
  calc ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.exp (-α) : ℝ) : ℂ)⁻¹ *
          (((Real.exp (-α) : ℝ) : ℂ) *
            ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        rw [← mul_assoc, inv_mul_cancel₀ he_ne, one_mul]
    _ = ((Real.exp (-α) : ℝ) : ℂ)⁻¹ *
          (((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ)) := by
        rw [h_inv2]
    _ = ((Real.exp α : ℝ) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ)) := by
        rw [h_eq_eα_inv]
    _ = ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by ring

#print axioms mellin_shifted_re_neg_one

/-! ## Step 4b: Per-n shifted left-edge reflected-prime integral

The reflected-prime integrand at the left edge `Re s = -1` is
`LSeries.term Λ(2-yi) n · pairTestMellin β (-1+yi)`. The K_2-Fourier-shift
applies `e^{(yα)·I}` outside.

We follow the right-edge `shifted_per_n_integral` template, with the key
difference that `(2-yi)` appears (FE-mirror image of the right-edge `(2+yi)`).
The substitution `x = (1/n)·e^{α}` converts the shifted integrand to the
un-shifted Mellin pairing at `x` on the left edge. -/

/-- **Per-n shifted left-edge reflected-prime integral.**

For `n ≥ 1` and `α : ℝ`,
```
∫_y e^{iyα}·Λ(n)·(n:ℂ)^{-(2-iy)}·M(β,-1+iy) dy
  = 2π·e^{α}·Λ(n)·(1/n)·test_β((1/n)·e^{-α})
```

Proof: substitute `x = (1/n)·e^{-α}` (positive real) into
`pairTestMellin_vertical_integral_at_neg_one_pos`.  The algebraic identity
`(x:ℂ)^{-(-1+yi)} = x · n^{yi} · e^{iyα}` factors out `x` and combines the
`n^{yi}·e^{iyα}` into `(n·e^{α})^{yi}` (which equals `n^{yi}·e^{iyα}` directly).
Then `e^{iyα}·n^{-(2-iy)} = n^{-2}·n^{iy}·e^{iyα} = n^{-2}·(x:ℂ)^{-(-1+iy)}/x`
and the un-shifted vertical integral identity gives the result. -/
private lemma shifted_per_n_integral_left (β α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 / (n : ℂ)) *
        ((pair_cosh_gauss_test β ((1/(n:ℝ)) * Real.exp (-α)) : ℝ) : ℂ) := by
  set x : ℝ := (1 / (n : ℝ)) * Real.exp (-α) with hx_def
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_inv_pos : 0 < (1 / (n : ℝ)) := by positivity
  have hx_pos : 0 < x := mul_pos hn_inv_pos (Real.exp_pos _)
  have hxC_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hnC_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  -- Key algebraic identity:
  -- e^{(yα)·I}·n^{-(2-yi)} = (1/n) · x^{-(-1+yi)}.
  -- Derivation:
  --   x^{-(-1+yi)} = x · x^{-yi} = x · exp(-yi·log x).
  --   log x = -log n - α, so -yi·log x = yi·(log n + α) = (y·(log n + α))·I.
  --   So x^{-(-1+yi)} = x · exp((y·(log n + α))·I) = x · exp((y·log n)·I) · exp((y·α)·I)
  --                   = x · n^{yi} · e^{(yα)·I}.
  --   And e^{(yα)·I}·n^{-(2-yi)} = e^{(yα)·I}·n^{-2}·n^{yi} = n^{-2}·n^{yi}·e^{(yα)·I}.
  --   Multiplying by 1/x and substituting x = (1/n)e^{-α} = e^{-α}/n:
  --     (1/x)·x^{-(-1+yi)} = n^{yi}·e^{(yα)·I}.
  --     n^{-2}·n^{yi}·e^{(yα)·I} = n^{-2}·(1/x)·x^{-(-1+yi)} = (n·e^α)·n^{-2}·x^{-(-1+yi)}/n
  --                              = (1/n)·e^α·x^{-(-1+yi)}/(n·e^α/n)... let me redo.
  -- Cleaner: set the algebraic identity directly.
  --   Multiply both sides by n²: n²·e^{(yα)·I}·n^{-(2-yi)} = n^{yi}·e^{(yα)·I}.
  --   And (1/x)·x^{-(-1+yi)} = n^{yi}·e^{(yα)·I}.
  --   So n²·e^{(yα)·I}·n^{-(2-yi)} = (1/x)·x^{-(-1+yi)}, i.e.,
  --     e^{(yα)·I}·n^{-(2-yi)} = (1/(n²·x))·x^{-(-1+yi)} = (1/(n²·(1/n)·e^{-α}))·x^{-(-1+yi)}
  --                            = (e^α/n)·x^{-(-1+yi)}.
  have h_key : ∀ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) =
      ((Real.exp α : ℝ) : ℂ) * (1 / (n : ℂ)) *
        ((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    intro y
    -- log(n : ℂ) and log(x : ℂ) as real casts.
    have hlog_n : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      have h1 : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [h1]; exact (Complex.ofReal_log (Nat.cast_nonneg _)).symm
    have hlog_x : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) :=
      (Complex.ofReal_log hx_pos.le).symm
    have hlog_x_real : Real.log x = -Real.log n - α := by
      rw [hx_def]
      rw [Real.log_mul (by positivity : (1 / (n : ℝ)) ≠ 0)
          (Real.exp_ne_zero _)]
      rw [Real.log_div one_ne_zero (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))]
      rw [Real.log_one, Real.log_exp]
      ring
    -- Express both cpows via cpow_def_of_ne_zero.
    rw [Complex.cpow_def_of_ne_zero hnC_ne, Complex.cpow_def_of_ne_zero hxC_ne, hlog_n, hlog_x]
    rw [show ((Real.log x : ℝ) : ℂ) =
        -((Real.log n : ℝ) : ℂ) - ((α : ℝ) : ℂ) from by
      rw [hlog_x_real]; push_cast; ring]
    -- Combine LHS via exp_add: e^{yα·I}·exp(...) = exp(... + yα·I).
    rw [← Complex.exp_add]
    -- Convert the multiplicative constants on RHS to exp form.
    rw [show ((Real.exp α : ℝ) : ℂ) = Complex.exp (((α : ℝ) : ℂ)) from
      Complex.ofReal_exp α]
    rw [show (1 / (n : ℂ)) = Complex.exp (-((Real.log n : ℝ) : ℂ)) from by
      rw [Complex.exp_neg]
      rw [show Complex.exp (((Real.log n : ℝ) : ℂ)) = (n : ℂ) from by
        rw [show ((Real.log n : ℝ) : ℂ) = Complex.log (n : ℂ) from hlog_n.symm]
        exact Complex.exp_log hnC_ne]
      simp]
    -- RHS now: exp(α:ℂ) · exp(-log n) · exp((-log n - α)·(-(-1+yi)))
    -- Combine all into single exp.
    rw [show ∀ (a b c : ℂ), Complex.exp a * Complex.exp b * c =
        c * Complex.exp a * Complex.exp b from fun a b c => by ring]
    rw [show ∀ (a b : ℂ), Complex.exp ((-((Real.log n : ℝ) : ℂ) - ((α : ℝ) : ℂ)) *
            (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) * a * b =
        Complex.exp ((-((Real.log n : ℝ) : ℂ) - ((α : ℝ) : ℂ)) *
            (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) * (a * b) from fun a b => by ring]
    rw [← Complex.exp_add, ← Complex.exp_add]
    -- Now both sides are exp(...) — need the exponents to be equal.
    congr 1
    push_cast; ring
  -- Use h_key to rewrite the integrand.
  have h_rewrite :
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      (fun y : ℝ =>
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          (((Real.exp α : ℝ) : ℂ) * (1 / (n : ℂ)))) *
        (((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    funext y
    have := h_key y
    rw [show Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I)))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) from by ring]
    rw [this]; ring
  rw [h_rewrite]
  -- Pull constants out of integral.
  have h_pull : ∫ y : ℝ, ((ArithmeticFunction.vonMangoldt n : ℂ) *
        (((Real.exp α : ℝ) : ℂ) * (1 / (n : ℂ)))) *
        (((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        (((Real.exp α : ℝ) : ℂ) * (1 / (n : ℂ)))) *
        ∫ y : ℝ, (((x : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    MeasureTheory.integral_const_mul _ _
  rw [h_pull]
  rw [pairTestMellin_vertical_integral_at_neg_one_pos β hx_pos]
  push_cast
  ring

#print axioms shifted_per_n_integral_left

/-! ## Step 4c: Full Fubini assembly — shifted left-edge reflected-prime identity -/

/-- **Shifted left-edge reflected-prime identity.**

For any real `α`,
```
∫_y e^{iy·α}·(ζ'(2-iy)/ζ(2-iy))·M(β,-1+iy) dy
  = -2π · e^α · Σ' n, (Λ(n)/n) · test_β((1/n)·e^{-α})
```

The Fourier shift `e^{iyα}` lifts `leftEdge_reflectedPrime_eq_sum` term-by-term
via `shifted_per_n_integral_left`.  Norm bound `|e^{iyα}| = 1` makes the
integrability/summability transfer trivial. -/
theorem leftEdge_reflectedPrime_shifted_eq_sum (β α : ℝ) :
    ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
       riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
    -2 * (Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ) *
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ) := by
  -- Set up: per-n term G and shifted G_shift.
  set s : ℝ → ℂ := fun y : ℝ => (2 : ℂ) - (y : ℂ) * I with hs_def
  set G : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (s y) n *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hG_def
  set G_shift : ℕ → ℝ → ℂ := fun n y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) * G n y with hG_shift_def
  -- Pointwise: e^{iyα}·ζ'/ζ(s y)·M(β,-1+iy) = -Σ' G_shift n y.
  have h_pt : ∀ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        -∑' n : ℕ, G_shift n y := by
    intro y
    have h_1s_eq : 1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = s y := by simp [hs_def]; ring
    rw [h_1s_eq]
    have hs_re : (1 : ℝ) < (s y).re := by simp [hs_def]
    have hL := Contour.vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs_re
    have hζ_eq : deriv riemannZeta (s y) / riemannZeta (s y) =
        -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s y) := by
      rw [hL]; ring
    rw [hζ_eq]
    rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s y) =
            ∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n from rfl]
    -- Goal: e^{iyα} · (-Σ term · M) = -Σ G_shift
    rw [show (-∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n) * Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
            -(∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n * Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by
      rw [tsum_mul_right]; ring]
    rw [show
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        -(∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            (s y) n * Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -(Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            (s y) n * Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by ring]
    congr 1
    rw [← tsum_mul_left]
  -- Norm: ‖G_shift n y‖ = ‖G n y‖.
  have h_norm_G : ∀ n : ℕ, ∀ y : ℝ, ‖G_shift n y‖ = ‖G n y‖ := by
    intro n y
    show ‖Complex.exp (((y * α : ℝ) : ℂ) * I) * G n y‖ = ‖G n y‖
    rw [norm_mul]
    have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h_unit, one_mul]
  -- The un-shifted G is integrable per n (from leftEdge_reflectedPrime_eq_sum's
  -- inner machinery). We need a private analog. Re-derive using same pattern.
  -- pairTestMellin integrable on left edge.
  have h_pair_int : MeasureTheory.Integrable
      (fun y : ℝ => Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
    unfold Complex.VerticalIntegrable at h
    exact h
  -- pairTestMellin continuous on left edge.
  have h_pair_cont : Continuous
      (fun y : ℝ => Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    LeftEdgePrimeSum.pairTestMellin_continuous_along_vertical_extended β
      (-1) (by norm_num)
  -- Each G n integrable.
  have h_G_int : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ y : ℝ, G 0 y = 0 := by
        intro y; simp [hG_def, LSeries.term_zero]
      refine (MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume).congr ?_
      exact MeasureTheory.ae_of_all _ (fun y => (h_zero y).symm)
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have hn_ne_C : (n : ℂ) ≠ 0 := by exact_mod_cast hn_ne
      have h_term : ∀ y : ℝ, G n y =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-(s y))) *
             Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        intro y
        simp only [hG_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      have h_fn_eq : (G n : ℝ → ℂ) = fun y : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-(s y))) *
             Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := funext h_term
      rw [h_fn_eq]
      apply MeasureTheory.Integrable.const_mul
      have h_cpow_cont : Continuous (fun y : ℝ => ((n : ℂ) ^ (-(s y)))) := by
        have h_exp : Continuous (fun y : ℝ => -(s y)) := by simp only [hs_def]; fun_prop
        have h_cpow_cont_z : Continuous (fun z : ℂ => (n : ℂ) ^ z) := by
          rw [continuous_iff_continuousAt]
          intro b
          exact continuousAt_const_cpow hn_ne_C
        exact h_cpow_cont_z.comp h_exp
      have h_cpow_norm : ∀ y : ℝ, ‖((n : ℂ) ^ (-(s y)))‖ = (n : ℝ) ^ (-(2:ℝ)) := by
        intro y
        rw [show -(s y) = ((-2 : ℝ) : ℂ) + (y : ℂ) * I from by simp [hs_def]; ring]
        rw [Complex.norm_natCast_cpow_of_pos hpos]
        simp
      refine (h_pair_int.norm.const_mul ((n : ℝ)^(-(2:ℝ)))).mono'
        ((h_cpow_cont.mul h_pair_cont).aestronglyMeasurable) ?_
      refine MeasureTheory.ae_of_all _ fun y => ?_
      rw [norm_mul, h_cpow_norm y]
  -- Each G_shift n integrable.
  have h_G_shift_int : ∀ n : ℕ, MeasureTheory.Integrable (G_shift n) := by
    intro n
    have h_exp_meas : MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
      have : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
        exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
            continuous_const)
      exact this.aestronglyMeasurable
    refine MeasureTheory.Integrable.mono (h_G_int n)
      (h_exp_meas.mul (h_G_int n).aestronglyMeasurable) ?_
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show ‖Complex.exp (((y * α : ℝ) : ℂ) * I) * G n y‖ ≤ ‖G n y‖
    rw [norm_mul]
    have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h_unit, one_mul]
  -- Σ ∫ ‖G_shift n‖ summable (= Σ ∫ ‖G n‖ which we need to bound).
  set I_pair : ℝ := ∫ y : ℝ, ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
    with hI_pair_def
  have h_G_L1_summ : Summable (fun n : ℕ => ∫ y : ℝ, ‖G_shift n y‖) := by
    have h_eq : (fun n : ℕ => ∫ y : ℝ, ‖G_shift n y‖) =
                (fun n : ℕ => ∫ y : ℝ, ‖G n y‖) := by
      funext n
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      exact h_norm_G n y
    rw [h_eq]
    -- Bound: ∫ ‖G n‖ ≤ Λ(n) · n^{-2} · I_pair.
    have h_bound_summ : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * I_pair) := by
      have h_div := Contour.summable_vonMangoldt_rpow (2:ℝ) (by norm_num : (1:ℝ) < 2)
      have h_eq2 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ)^(-(2:ℝ)) * I_pair) =
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
            (n : ℝ)^(2:ℝ) * I_pair) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [ArithmeticFunction.map_zero]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
      rw [h_eq2]; exact h_div.mul_right I_pair
    refine h_bound_summ.of_nonneg_of_le ?_ ?_
    · intro n; exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    · intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have h_zero : ∀ y : ℝ, ‖G 0 y‖ = 0 := by
          intro y; simp [hG_def, LSeries.term_zero]
        rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ h_zero),
          MeasureTheory.integral_zero]
        simp [ArithmeticFunction.map_zero]
      · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
        have h_bd_pt : ∀ y : ℝ,
            ‖G n y‖ ≤
            (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
              ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
          intro y
          simp only [hG_def]
          rw [LSeries.term_of_ne_zero hn_ne, norm_mul, norm_div]
          rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
                (ArithmeticFunction.vonMangoldt n : ℝ) from by
            rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
                  = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
            rw [Complex.norm_real]
            exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          rw [Complex.norm_natCast_cpow_of_pos hpos]
          have h_sy_re : (s y).re = 2 := by simp [hs_def]
          rw [h_sy_re]
          have hns_eq : (n : ℝ)^(-(2:ℝ)) = ((n : ℝ)^(2:ℝ))⁻¹ :=
            Real.rpow_neg hn_pos.le _
          rw [hns_eq, div_eq_mul_inv]
        calc ∫ y : ℝ, ‖G n y‖
            ≤ ∫ y : ℝ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
                       ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
              apply MeasureTheory.integral_mono_of_nonneg
              · exact MeasureTheory.ae_of_all _ fun _ => norm_nonneg _
              · exact h_pair_int.norm.const_mul _
              · exact MeasureTheory.ae_of_all _ h_bd_pt
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
              ∫ y : ℝ, ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
              rw [MeasureTheory.integral_const_mul]
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * I_pair := by
              rw [hI_pair_def]
  -- Fubini swap.
  have h_fubini : (∫ y : ℝ, ∑' n : ℕ, G_shift n y) = ∑' n : ℕ, ∫ y : ℝ, G_shift n y :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm h_G_shift_int h_G_L1_summ).symm
  -- Per-n integral via shifted_per_n_integral_left.
  have h_per_n : ∀ n : ℕ, ∫ y : ℝ, G_shift n y =
      (2 * Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
        ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ y : ℝ, G_shift 0 y = 0 := by
        intro y
        show Complex.exp (((y * α : ℝ) : ℂ) * I) * G 0 y = 0
        rw [show G 0 y = 0 from by simp [hG_def, LSeries.term_zero]]; ring
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ h_zero),
        MeasureTheory.integral_zero]
      simp [ArithmeticFunction.map_zero]
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have h_term_eq : ∀ y : ℝ, G_shift n y =
          Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        intro y
        show Complex.exp (((y * α : ℝ) : ℂ) * I) * G n y = _
        simp only [hG_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        have h_neg_s : (-(s y)) = -(((2 : ℝ) : ℂ) - (y : ℂ) * I) := by
          simp [hs_def]
        rw [h_neg_s]
      rw [show (fun y : ℝ => G_shift n y) = (fun y : ℝ =>
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-(((2 : ℝ) : ℂ) - (y : ℂ) * I))) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) from by
        funext y; exact h_term_eq y]
      rw [shifted_per_n_integral_left β α n hpos]
      push_cast; ring
  -- Assembly.
  calc ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ, -∑' n : ℕ, G_shift n y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact h_pt y
    _ = -∫ y : ℝ, ∑' n : ℕ, G_shift n y := by
        rw [MeasureTheory.integral_neg]
    _ = -∑' n : ℕ, ∫ y : ℝ, G_shift n y := by rw [h_fubini]
    _ = -∑' n : ℕ, (2 * Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
          ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ) := by
        congr 1
        apply tsum_congr; intro n; exact h_per_n n
    _ = -((2 * Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ)) *
          ∑' n : ℕ, ((((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
            ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ)) := by
        rw [show
          (-∑' n : ℕ, (2 * Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ) *
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
            ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ)) =
          -∑' n : ℕ, ((2 * Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ)) *
            ((((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
              ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ)) from by
          congr 1; apply tsum_congr; intro n; ring]
        rw [tsum_mul_left]; ring
    _ = -2 * (Real.pi : ℂ) * ((Real.exp α : ℝ) : ℂ) *
          ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-α)) : ℝ) : ℂ) := by
        ring

#print axioms leftEdge_reflectedPrime_shifted_eq_sum

/-! ## Step 4d: K_2-twisted left-edge reflected-prime formula

The K_2-twisted left-edge reflected-prime integral combines the
Fourier expansion `K_2_fourier_expansion_re_neg_one` with the 5 prime-sum
evaluations (each obtained from `leftEdge_reflectedPrime_shifted_eq_sum`
at `α ∈ {2t, -2t, t, -t, 0}`).

Coefficients (from K_2 expansion at `Re s = -1`, with t-coefficient flip
relative to right edge):
- `(1/2)e^{-3t}` × `α=2t`:   `(1/2)e^{-3t}·(-2π·e^{2t}) = -π·e^{-t}`
- `(1/2)e^{3t}`  × `α=-2t`:  `(1/2)e^{3t}·(-2π·e^{-2t}) = -π·e^{t}`
- `-e^{-(3/2)t}` × `α=t`:    `-e^{-(3/2)t}·(-2π·e^{t}) = 2π·e^{-t/2}`
- `-e^{(3/2)t}`  × `α=-t`:   `-e^{(3/2)t}·(-2π·e^{-t}) = 2π·e^{t/2}`
- `1`            × `α=0`:    `1·(-2π) = -2π`

Result:
```
∫_y K_2(-1+iy, t) · ζ'(2-iy)/ζ(2-iy) · M(β,-1+iy) dy
  = -π·e^{-t}·Σ Λ/n·test((1/n)·e^{-2t}) − π·e^{t}·Σ Λ/n·test((1/n)·e^{2t})
  + 2π·e^{-t/2}·Σ Λ/n·test((1/n)·e^{-t}) + 2π·e^{t/2}·Σ Λ/n·test((1/n)·e^{t})
  − 2π·Σ Λ/n·test(1/n)
```

Bundles the 5 evaluations.  Full assembly via `integral_5_linear_combination`
requires per-component integrability of the K_2-Fourier-shifted
reflected-prime integrand; this needs an integrability lemma for
`(ζ'/ζ)(2-iy)·M(β,-1+iy)` derived from per-n L¹ summability + dominated
convergence (the per-n machinery is in `leftEdge_reflectedPrime_eq_sum`'s
proof but not exposed as a separate lemma).

The 5 individual prime-sum evaluations: -/
theorem vert_neg1_K2_reflectedPrime_fourier_components (t β : ℝ) :
    (∫ y : ℝ, Complex.exp (((y * (2*t) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -2 * (Real.pi : ℂ) * ((Real.exp (2*t) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-(2*t))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * (-(2*t)) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -2 * (Real.pi : ℂ) * ((Real.exp (-(2*t)) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-(-(2*t)))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -2 * (Real.pi : ℂ) * ((Real.exp t : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-t)) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -2 * (Real.pi : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-(-t))) : ℝ) : ℂ)) ∧
    (∫ y : ℝ, (deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      -2 * (Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
          ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact leftEdge_reflectedPrime_shifted_eq_sum β (2*t)
  · exact leftEdge_reflectedPrime_shifted_eq_sum β (-(2*t))
  · exact leftEdge_reflectedPrime_shifted_eq_sum β t
  · exact leftEdge_reflectedPrime_shifted_eq_sum β (-t)
  · -- α = 0: shifted version with α=0 simplifies to un-shifted via e^{0}=1.
    have h_zero := leftEdge_reflectedPrime_shifted_eq_sum β 0
    have h_lhs_eq : ∫ y : ℝ,
        (deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
        ∫ y : ℝ, Complex.exp (((y * 0 : ℝ) : ℂ) * I) *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [show ((y * 0 : ℝ) : ℂ) * I = 0 from by push_cast; ring,
        Complex.exp_zero, one_mul]
    rw [h_lhs_eq, h_zero]
    simp [Real.exp_zero, neg_zero, mul_zero]

#print axioms vert_neg1_K2_reflectedPrime_fourier_components

/-- Helper: `(ζ'/ζ)(2-iy)·M(β,-1+iy)` is integrable. -/
private lemma reflectedPrime_integrand_integrable (β : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => (deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h_pair_int : MeasureTheory.Integrable
      (fun y : ℝ => Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
    unfold Complex.VerticalIntegrable at h
    exact h
  -- ζ'/ζ(2-yi) bounded by Σ Λ(n)/n^2 (uniform in y).
  set C : ℝ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ)) / (n : ℝ)^(2:ℝ)
  have hC_bd : ∀ y : ℝ,
      ‖deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤ C := by
    intro y
    have h_1s_eq : 1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = (2 : ℂ) - (y : ℂ) * I := by
      push_cast; ring
    rw [h_1s_eq]
    have hs_re : (1 : ℝ) < ((2 : ℂ) - (y : ℂ) * I).re := by simp
    have hL := Contour.vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs_re
    have h_eq : deriv riemannZeta ((2 : ℂ) - (y : ℂ) * I) /
        riemannZeta ((2 : ℂ) - (y : ℂ) * I) =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((2 : ℂ) - (y : ℂ) * I) := by rw [hL]; ring
    rw [h_eq, norm_neg]
    have h_ls_eq : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((2 : ℂ) - (y : ℂ) * I) =
        ∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((2 : ℂ) - (y : ℂ) * I) n := rfl
    rw [h_ls_eq]
    have h_summ_norm : Summable
        (fun n : ℕ => ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((2 : ℂ) - (y : ℂ) * I) n‖) := by
      have h_div := Contour.summable_vonMangoldt_rpow (2:ℝ) (by norm_num : (1:ℝ) < 2)
      refine h_div.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
      intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [LSeries.term_zero, ArithmeticFunction.map_zero]
      · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
        rw [LSeries.term_of_ne_zero hn_ne, norm_div]
        rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) from by
          rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
                = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
          rw [Complex.norm_real]
          exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [Complex.norm_natCast_cpow_of_pos hpos]
        simp
    refine (norm_tsum_le_tsum_norm h_summ_norm).trans ?_
    refine Summable.tsum_le_tsum ?_ h_summ_norm
      (Contour.summable_vonMangoldt_rpow 2 (by norm_num))
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [LSeries.term_zero, ArithmeticFunction.map_zero]
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      rw [LSeries.term_of_ne_zero hn_ne, norm_div]
      rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
          (ArithmeticFunction.vonMangoldt n : ℝ) from by
        rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
              = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
        rw [Complex.norm_real]
        exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      simp
  -- AE-strong-measurability of ζ'/ζ(2-yi): via continuity from analyticity.
  have h_open : IsOpen ({(1:ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h_zeta_diff : DifferentiableOn ℂ riemannZeta ({(1:ℂ)}ᶜ : Set ℂ) := by
    intro s hs
    exact (differentiableAt_riemannZeta hs).differentiableWithinAt
  have h_zeta_analyt : AnalyticOnNhd ℂ riemannZeta ({(1:ℂ)}ᶜ : Set ℂ) :=
    h_zeta_diff.analyticOnNhd h_open
  have h_zeta_cont : ContinuousOn riemannZeta ({(1:ℂ)}ᶜ : Set ℂ) :=
    h_zeta_analyt.continuousOn
  have h_zeta_deriv_cont : ContinuousOn (deriv riemannZeta) ({(1:ℂ)}ᶜ : Set ℂ) :=
    h_zeta_analyt.deriv.continuousOn
  have h_map_cont : Continuous
      (fun y : ℝ => 1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by fun_prop
  have h_map_in_dom : ∀ y : ℝ,
      1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by
    intro y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h_re : (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)).re = 2 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        mul_zero, zero_mul, sub_zero, neg_neg]
      norm_num
    rw [h] at h_re
    norm_num at h_re
  have h_zeta_cont_y : Continuous
      (fun y : ℝ => riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    h_zeta_cont.comp_continuous h_map_cont h_map_in_dom
  have h_zeta_deriv_cont_y : Continuous
      (fun y : ℝ => deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    h_zeta_deriv_cont.comp_continuous h_map_cont h_map_in_dom
  have h_zeta_ne_zero : ∀ y : ℝ,
      riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) ≠ 0 := by
    intro y
    apply riemannZeta_ne_zero_of_one_lt_re
    have h_re : (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)).re = 2 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        mul_zero, zero_mul, sub_zero, neg_neg]
      norm_num
    rw [h_re]; norm_num
  have h_div_cont : Continuous
      (fun y : ℝ => deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    h_zeta_deriv_cont_y.div h_zeta_cont_y h_zeta_ne_zero
  have h_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) MeasureTheory.volume :=
    h_div_cont.aestronglyMeasurable
  exact MeasureTheory.Integrable.bdd_mul h_pair_int h_meas
    (MeasureTheory.ae_of_all _ hC_bd)

#print axioms reflectedPrime_integrand_integrable

/-- Helper: shifted reflected-prime integrand integrable. -/
private lemma reflectedPrime_shift_integrable (β α : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
  have h_F_int := reflectedPrime_integrand_integrable β
  have h_exp_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
    have : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
          continuous_const)
    exact this.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono h_F_int
    (h_exp_meas.mul h_F_int.aestronglyMeasurable) ?_
  refine MeasureTheory.ae_of_all _ fun y => ?_
  rw [norm_mul]
  have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [h_unit, one_mul]

/-- **K_2-twisted left-edge reflected-prime formula.**

For every `t : ℝ` and `β : ℝ`,
```
∫_y K_2(-1+iy, t) · (ζ'/ζ)(2-iy) · M(β,-1+iy) dy
  = -π·e^{-t}·Σ Λ/n·test((1/n)·e^{-2t}) − π·e^{t}·Σ Λ/n·test((1/n)·e^{2t})
  + 2π·e^{-t/2}·Σ Λ/n·test((1/n)·e^{-t}) + 2π·e^{t/2}·Σ Λ/n·test((1/n)·e^{t})
  − 2π·Σ Λ/n·test(1/n)
```

Combines `K_2_fourier_expansion_re_neg_one` with `vert_neg1_K2_reflectedPrime_fourier_components`
via `integral_5_linear_combination`, then matches prefactors via `Complex.exp_add`. -/
theorem K_2_reflectedPrime_re_neg_one_eq (t β : ℝ) :
    ∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-(2*t))) : ℝ) : ℂ) -
      ((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (2*t)) : ℝ) : ℂ) +
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-t)) : ℝ) : ℂ) +
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp t) : ℝ) : ℂ) -
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
  -- Define 5 base shifted integrands.
  set f1 : ℝ → ℂ := fun y => Complex.exp (((y * (2*t) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) with hf1_def
  set f2 : ℝ → ℂ := fun y => Complex.exp (((y * (-(2*t)) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) with hf2_def
  set f3 : ℝ → ℂ := fun y => Complex.exp (((y * t : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) with hf3_def
  set f4 : ℝ → ℂ := fun y => Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) with hf4_def
  set f5 : ℝ → ℂ := fun y =>
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) with hf5_def
  -- Coefficients in t (note flipped relative to right edge).
  set c1 : ℂ := (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) with hc1_def
  set c2 : ℂ := (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) with hc2_def
  set c3 : ℂ := Complex.exp (((-(3/2) * t) : ℝ) : ℂ) with hc3_def
  set c4 : ℂ := Complex.exp ((((3/2) * t) : ℝ) : ℂ) with hc4_def
  -- K_2 Fourier expansion at Re=-1 gives the decomposition.
  have h_decomp : ∀ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y := by
    intro y
    rw [K_2_fourier_expansion_re_neg_one t y]
    have h_match1 : ((2 * t * y : ℝ) : ℂ) = ((y * (2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match2 : ((-(2 * t * y) : ℝ) : ℂ) = ((y * -(2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match3 : ((t * y : ℝ) : ℂ) = ((y * t : ℝ) : ℂ) := by push_cast; ring
    have h_match4 : ((-(t * y) : ℝ) : ℂ) = ((y * -t : ℝ) : ℂ) := by push_cast; ring
    rw [h_match1, h_match2, h_match3, h_match4]
    show _ = c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y
    rw [hc1_def, hc2_def, hc3_def, hc4_def, hf1_def, hf2_def, hf3_def, hf4_def, hf5_def]
    ring
  -- Rewrite the integrand.
  rw [show (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      (fun y : ℝ => c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y) from
    funext h_decomp]
  -- Integrability.
  have h_int1 : MeasureTheory.Integrable f1 := reflectedPrime_shift_integrable β (2*t)
  have h_int2 : MeasureTheory.Integrable f2 := reflectedPrime_shift_integrable β (-(2*t))
  have h_int3 : MeasureTheory.Integrable f3 := reflectedPrime_shift_integrable β t
  have h_int4 : MeasureTheory.Integrable f4 := reflectedPrime_shift_integrable β (-t)
  have h_int5 : MeasureTheory.Integrable f5 := reflectedPrime_integrand_integrable β
  rw [integral_5_linear_combination f1 f2 f3 f4 f5 c1 c2 c3 c4
    h_int1 h_int2 h_int3 h_int4 h_int5]
  -- Apply per-α formulas.
  obtain ⟨he1, he2, he3, he4, he5⟩ := vert_neg1_K2_reflectedPrime_fourier_components t β
  simp only [hf1_def, hf2_def, hf3_def, hf4_def, hf5_def]
  rw [he1, he2, he3, he4, he5]
  -- Arithmetic: combine prefactors.
  rw [hc1_def, hc2_def, hc3_def, hc4_def]
  -- c_i × (-2π × e^{α_i}) cancellation.
  have he_neg_t : (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      (-2 * (Real.pi : ℂ) * ((Real.exp (2*t) : ℝ) : ℂ)) =
      -((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        ((Real.exp (2*t) : ℝ) : ℂ) = ((Real.exp (-t) : ℝ) : ℂ) := by
      rw [show ((Real.exp (2*t) : ℝ) : ℂ) = Complex.exp (((2*t) : ℝ) : ℂ) from
          Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((-(3 * t) : ℝ) : ℂ) + (((2*t) : ℝ) : ℂ)) =
          ((-t : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination -Real.pi * h_exp_combine
  have he_t : (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      (-2 * (Real.pi : ℂ) * ((Real.exp (-(2*t)) : ℝ) : ℂ)) =
      -((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) := by
    have h_exp_combine : Complex.exp ((3 * t : ℝ) : ℂ) *
        ((Real.exp (-(2*t)) : ℝ) : ℂ) = ((Real.exp t : ℝ) : ℂ) := by
      rw [show ((Real.exp (-(2*t)) : ℝ) : ℂ) = Complex.exp (((-(2*t)) : ℝ) : ℂ) from
          Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((3 * t : ℝ) : ℂ) + (((-(2*t)) : ℝ) : ℂ)) =
          ((t : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination -Real.pi * h_exp_combine
  have he_neg_t2 : Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
      (-2 * (Real.pi : ℂ) * ((Real.exp t : ℝ) : ℂ)) =
      -(((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ)) := by
    have h_exp_combine : Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        ((Real.exp t : ℝ) : ℂ) = ((Real.exp (-(t/2)) : ℝ) : ℂ) := by
      rw [show ((Real.exp t : ℝ) : ℂ) = Complex.exp (((t : ℝ) : ℂ)) from
          Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show (((-(3/2) * t) : ℝ) : ℂ) + ((t : ℝ) : ℂ) =
          ((-(t/2) : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination -2 * Real.pi * h_exp_combine
  have he_t2 : Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      (-2 * (Real.pi : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)) =
      -(((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ)) := by
    have h_exp_combine : Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ) = ((Real.exp (t/2) : ℝ) : ℂ) := by
      rw [show ((Real.exp (-t) : ℝ) : ℂ) = Complex.exp (((-t) : ℝ) : ℂ) from
          Complex.ofReal_exp _]
      rw [← Complex.exp_add]
      rw [show ((((3/2) * t) : ℝ) : ℂ) + (((-t) : ℝ) : ℂ) =
          ((t/2 : ℝ) : ℂ) from by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    push_cast at h_exp_combine ⊢
    linear_combination -2 * Real.pi * h_exp_combine
  -- Note negation absorption: e^{-(-2t)} = e^{2t} etc.
  have hsimp_neg2t : Real.exp (-(-(2*t))) = Real.exp (2*t) := by rw [neg_neg]
  have hsimp_negt : Real.exp (-(-t)) = Real.exp t := by rw [neg_neg]
  rw [hsimp_neg2t, hsimp_negt]
  push_cast
  push_cast at he_neg_t he_t he_neg_t2 he_t2
  linear_combination
    he_neg_t * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1/(n:ℝ)) * Real.exp (-(2*t))) : ℝ) : ℂ))
    + he_t * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1/(n:ℝ)) * Real.exp (2*t)) : ℝ) : ℂ))
    - he_neg_t2 * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1/(n:ℝ)) * Real.exp (-t)) : ℝ) : ℂ))
    - he_t2 * (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1/(n:ℝ)) * Real.exp t) : ℝ) : ℂ))

#print axioms K_2_reflectedPrime_re_neg_one_eq

/-! ## Step 4e: K_2-twisted left-edge arch integral

The arch contribution at `Re s = -1` is
```
∫_y K_2(-1+iy, t) · (Γℝ'/Γℝ(-1+iy) + Γℝ'/Γℝ(2-iy)) · M(β,-1+iy) dy.
```

By the K_2 Fourier expansion, this decomposes into 5 shifted arch integrals
indexed by `α ∈ {2t, -2t, t, -t, 0}`. -/

/-- The shifted arch integrand: `e^{iy·α}·arch(-1+iy)·M(β,-1+iy)`. -/
private noncomputable def archShiftIntegrand (β α : ℝ) (y : ℝ) : ℂ :=
  Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.archIntegrand β (-1) y

/-- Helper: shifted arch integrand integrable. -/
private lemma archShift_integrable (β α : ℝ) :
    MeasureTheory.Integrable (archShiftIntegrand β α) := by
  unfold archShiftIntegrand
  have h_arch_int := ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_exp_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
    have : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
          continuous_const)
    exact this.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono h_arch_int
    (h_exp_meas.mul h_arch_int.aestronglyMeasurable) ?_
  refine MeasureTheory.ae_of_all _ fun y => ?_
  rw [norm_mul]
  have h_unit : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [h_unit, one_mul]

/-- **K_2-twisted left-edge arch integral identity.**

Reduces the K_2-twisted left-edge arch integral to 5 shifted arch
integrals via the Fourier expansion `K_2_fourier_expansion_re_neg_one`.

Setting `A_α(β) := ∫_y e^{iy·α} · arch(-1+iy) · M(β,-1+iy) dy` for
`α ∈ {2t, -2t, t, -t, 0}`:
```
∫_y K_2(-1+iy, t) · arch(-1+iy) · M(β,-1+iy) dy
  = (1/2)·e^{-3t}·A_{2t}(β) + (1/2)·e^{3t}·A_{-2t}(β)
  − e^{-(3/2)t}·A_{t}(β) − e^{(3/2)t}·A_{-t}(β) + A_0(β).
```
-/
theorem K_2_archIntegrand_re_neg_one_eq (t β : ℝ) :
    ∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.archIntegrand β (-1) y =
      (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        (∫ y : ℝ, archShiftIntegrand β (2*t) y) +
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        (∫ y : ℝ, archShiftIntegrand β (-(2*t)) y) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        (∫ y : ℝ, archShiftIntegrand β t y) -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        (∫ y : ℝ, archShiftIntegrand β (-t) y) +
      (∫ y : ℝ, archShiftIntegrand β 0 y) := by
  -- Define 5 base shifted integrands and constant coefficients.
  set f1 : ℝ → ℂ := fun y => archShiftIntegrand β (2*t) y with hf1_def
  set f2 : ℝ → ℂ := fun y => archShiftIntegrand β (-(2*t)) y with hf2_def
  set f3 : ℝ → ℂ := fun y => archShiftIntegrand β t y with hf3_def
  set f4 : ℝ → ℂ := fun y => archShiftIntegrand β (-t) y with hf4_def
  set f5 : ℝ → ℂ := fun y => archShiftIntegrand β 0 y with hf5_def
  set c1 : ℂ := (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) with hc1_def
  set c2 : ℂ := (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) with hc2_def
  set c3 : ℂ := Complex.exp (((-(3/2) * t) : ℝ) : ℂ) with hc3_def
  set c4 : ℂ := Complex.exp ((((3/2) * t) : ℝ) : ℂ) with hc4_def
  -- Pointwise: K_2(-1+iy, t) · arch(-1+iy)·M = c1·f1 + c2·f2 - c3·f3 - c4·f4 + f5.
  -- Note: archShiftIntegrand at α = 0 has e^{0·I} = 1, so f5 = arch·M.
  have h_decomp : ∀ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.archIntegrand β (-1) y =
      c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y := by
    intro y
    rw [K_2_fourier_expansion_re_neg_one t y]
    -- K_2 = c1·exp((2yt)·I) + c2·exp((-2yt)·I) - c3·exp((yt)·I) - c4·exp((-yt)·I) + 1.
    -- Multiply by arch·M, get the 5 components matching f_i (with f5 absorbing the "+1").
    show ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        Complex.exp (((t * y : ℝ) : ℂ) * I) -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        Complex.exp (((-(t * y) : ℝ) : ℂ) * I) +
      1) * Contour.archIntegrand β (-1) y =
      c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y
    rw [hc1_def, hc2_def, hc3_def, hc4_def]
    show _ = _ * (Complex.exp (((y * (2*t) : ℝ) : ℂ) * I) * _) +
      _ * (Complex.exp (((y * -(2*t) : ℝ) : ℂ) * I) * _) -
      _ * (Complex.exp (((y * t : ℝ) : ℂ) * I) * _) -
      _ * (Complex.exp (((y * -t : ℝ) : ℂ) * I) * _) +
      (Complex.exp (((y * 0 : ℝ) : ℂ) * I) * _)
    have h_match1 : ((2 * t * y : ℝ) : ℂ) = ((y * (2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match2 : ((-(2 * t * y) : ℝ) : ℂ) = ((y * -(2*t) : ℝ) : ℂ) := by push_cast; ring
    have h_match3 : ((t * y : ℝ) : ℂ) = ((y * t : ℝ) : ℂ) := by push_cast; ring
    have h_match4 : ((-(t * y) : ℝ) : ℂ) = ((y * -t : ℝ) : ℂ) := by push_cast; ring
    have h_zero_exp : Complex.exp (((y * 0 : ℝ) : ℂ) * I) = 1 := by
      rw [show ((y * 0 : ℝ) : ℂ) * I = 0 from by push_cast; ring, Complex.exp_zero]
    rw [h_match1, h_match2, h_match3, h_match4, h_zero_exp]
    ring
  -- Rewrite integrand pointwise.
  rw [show (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.archIntegrand β (-1) y) =
      (fun y : ℝ => c1 * f1 y + c2 * f2 y - c3 * f3 y - c4 * f4 y + f5 y) from
    funext h_decomp]
  -- Integrability of each piece.
  have h_int1 : MeasureTheory.Integrable f1 := archShift_integrable β (2*t)
  have h_int2 : MeasureTheory.Integrable f2 := archShift_integrable β (-(2*t))
  have h_int3 : MeasureTheory.Integrable f3 := archShift_integrable β t
  have h_int4 : MeasureTheory.Integrable f4 := archShift_integrable β (-t)
  have h_int5 : MeasureTheory.Integrable f5 := archShift_integrable β 0
  rw [integral_5_linear_combination f1 f2 f3 f4 f5 c1 c2 c3 c4
    h_int1 h_int2 h_int3 h_int4 h_int5]

#print axioms K_2_archIntegrand_re_neg_one_eq

/-! ## Step 4f: K_2-twisted left-edge boundary = arch + reflected-prime -/

/-- **K_2-twisted left-edge boundary integrand decomposition.**

By the project's `leftEdge_integrand_decomposition`, the boundary integrand
`hadamardArchBoundaryTerm(-1+iy) · M(β,-1+iy)` splits into the arch integrand
plus the reflected-prime piece. Multiplying through by `K_2(-1+iy, t)` and
integrating preserves the decomposition. -/
theorem K_2_leftEdge_boundary_decomposition (t β : ℝ) :
    ∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        (Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      (∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.archIntegrand β (-1) y) +
      (∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
  -- Pointwise: K_2 · (arch + refl) = K_2·arch + K_2·refl, then integrate.
  have h_ptwise : ∀ y : ℝ,
      K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        (Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * Contour.archIntegrand β (-1) y +
      K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    intro y
    have h := LeftEdgePrimeSum.leftEdge_integrand_decomposition β y
    linear_combination K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * h
  rw [show (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        (Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) =
      (fun y : ℝ =>
        K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t * Contour.archIntegrand β (-1) y +
        K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) from funext h_ptwise]
  -- Integrability of each piece via existing K_2 boundedness on the strip
  -- combined with arch / reflected-prime integrability.
  -- K_2 is bounded on the line `Re s = -1` (uniformly in y, for fixed t).
  -- Use the Fourier expansion + triangle inequality.
  have h_K2_bd : ∃ C : ℝ, ∀ y : ℝ,
      ‖K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t‖ ≤ C := by
    refine ⟨(1/2) * Real.exp (-(3 * t)) + (1/2) * Real.exp (3 * t) +
      Real.exp (-(3/2) * t) + Real.exp ((3/2) * t) + 1, fun y => ?_⟩
    rw [K_2_fourier_expansion_re_neg_one t y]
    -- Each Fourier component norm is e^{c·t} (since |e^{αy·I}| = 1).
    have hu1 : ‖Complex.exp (((2 * t * y : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hu2 : ‖Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hu3 : ‖Complex.exp (((t * y : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hu4 : ‖Complex.exp (((-(t * y) : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    -- ‖e^{c·t}‖ = Real.exp(c·t) (positive real).
    have he1 : ‖Complex.exp ((-(3 * t) : ℝ) : ℂ)‖ = Real.exp (-(3 * t)) := by
      rw [Complex.norm_exp]; simp
    have he2 : ‖Complex.exp ((3 * t : ℝ) : ℂ)‖ = Real.exp (3 * t) := by
      rw [Complex.norm_exp]; simp
    have he3 : ‖Complex.exp (((-(3/2) * t) : ℝ) : ℂ)‖ = Real.exp (-(3/2) * t) := by
      rw [Complex.norm_exp]; simp
    have he4 : ‖Complex.exp ((((3/2) * t) : ℝ) : ℂ)‖ = Real.exp ((3/2) * t) := by
      rw [Complex.norm_exp]; simp
    have hone : ‖((1:ℂ)/2)‖ = (1:ℝ)/2 := by
      rw [show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real]; simp
    have hI_norm : ‖(1 : ℂ)‖ = 1 := by simp
    have htri := norm_add_le
      ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
          Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
        (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I) -
        Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((t * y : ℝ) : ℂ) * I) -
        Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((-(t * y) : ℝ) : ℂ) * I))
      (1 : ℂ)
    have hsub1 := norm_sub_le
      ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
          Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
        (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I) -
        Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
          Complex.exp (((t * y : ℝ) : ℂ) * I))
      (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        Complex.exp (((-(t * y) : ℝ) : ℂ) * I))
    have hsub2 := norm_sub_le
      ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
          Complex.exp (((2 * t * y : ℝ) : ℂ) * I) +
        (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I))
      (Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        Complex.exp (((t * y : ℝ) : ℂ) * I))
    have hadd1 := norm_add_le
      ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        Complex.exp (((2 * t * y : ℝ) : ℂ) * I))
      ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        Complex.exp (((-(2 * t * y) : ℝ) : ℂ) * I))
    rw [norm_mul, norm_mul, hone, he1, hu1] at hadd1
    rw [norm_mul, norm_mul, hone, he2, hu2] at hadd1
    rw [norm_mul, he3, hu3] at hsub2
    rw [norm_mul, he4, hu4] at hsub1
    rw [hI_norm] at htri
    linarith
  obtain ⟨C, hC⟩ := h_K2_bd
  have h_K2_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t) MeasureTheory.volume := by
    have : Continuous (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t) := by
      unfold K_2
      have h1 : Continuous (fun y : ℝ => (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by fun_prop
      fun_prop
    exact this.aestronglyMeasurable
  -- Integrability of K_2 · arch.
  have h_int_arch : MeasureTheory.Integrable
      (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.archIntegrand β (-1) y) := by
    refine MeasureTheory.Integrable.bdd_mul
      (ArchAtNegOne.archIntegrand_at_neg_one_integrable β) h_K2_meas
      (MeasureTheory.ae_of_all _ hC)
  -- Integrability of K_2 · reflectedPrime.
  have h_int_refl : MeasureTheory.Integrable
      (fun y : ℝ => K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
    refine MeasureTheory.Integrable.bdd_mul
      (reflectedPrime_integrand_integrable β) h_K2_meas
      (MeasureTheory.ae_of_all _ hC)
  exact MeasureTheory.integral_add h_int_arch h_int_refl

#print axioms K_2_leftEdge_boundary_decomposition

/-! ## Step 4g: FE-symmetry of `K_2` and the `K_2(1, t)` normalization -/

/-- **FE-symmetry of `K_2`.** `K_2(1-s, t) = K_2(s, t)`. -/
theorem K_2_FE_symmetry (s : ℂ) (t : ℝ) : K_2 (1 - s) t = K_2 s t := by
  unfold K_2
  have h1 : (1 - s) - (1/2 : ℂ) = -(s - (1/2 : ℂ)) := by ring
  rw [h1]
  rw [show 2 * (-(s - (1/2 : ℂ))) * (t : ℂ) = -(2 * (s - (1/2 : ℂ)) * (t : ℂ)) from by ring]
  rw [show (-(s - (1/2 : ℂ))) * (t : ℂ) = -(((s - (1/2 : ℂ))) * (t : ℂ)) from by ring]
  rw [Complex.cosh_neg, Complex.cosh_neg]

/-- `K_2(-1+iy, t) = K_2(2-iy, t)` by FE-symmetry. -/
theorem K_2_neg_one_eq_two_minus_y (t : ℝ) (y : ℝ) :
    K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t = K_2 ((2 : ℂ) - (y : ℂ) * I) t := by
  have h_arg : (2 : ℂ) - (y : ℂ) * I = 1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    push_cast; ring
  rw [h_arg, K_2_FE_symmetry]

/-- **`K_2(1, t)` explicit normalization.**

```
K_2(1, t) = cosh(t) − 2·cosh(t/2) + 1.
```

Direct computation: at `s = 1`, `s − 1/2 = 1/2`, so
`2·(s−1/2)·t = t` and `(s−1/2)·t = t/2`. -/
theorem K_2_at_one (t : ℝ) :
    K_2 1 t = ((Real.cosh t : ℝ) : ℂ) - 2 * ((Real.cosh (t/2) : ℝ) : ℂ) + 1 := by
  unfold K_2
  have h1 : (1 : ℂ) - (1/2 : ℂ) = (1/2 : ℂ) := by ring
  rw [h1]
  have h2 : 2 * (1/2 : ℂ) * (t : ℂ) = ((t : ℝ) : ℂ) := by push_cast; ring
  have h3 : (1/2 : ℂ) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, h3]
  rw [show Complex.cosh ((t : ℝ) : ℂ) = ((Real.cosh t : ℝ) : ℂ) from by
    rw [Complex.ofReal_cosh]]
  rw [show Complex.cosh ((t / 2 : ℝ) : ℂ) = ((Real.cosh (t / 2) : ℝ) : ℂ) from by
    rw [Complex.ofReal_cosh]]

#print axioms K_2_FE_symmetry
#print axioms K_2_neg_one_eq_two_minus_y
#print axioms K_2_at_one

/-! ## Step 5: Load-bearing engineering target

The engineering identity in its sharpest form:
```
∫_y K_2(2+iy, t) · w(M)(2+iy) dy − ∫_y K_2(-1+iy, t) · w(M)(-1+iy) dy
  = 2π · K_2(1, t) · M(β, 1).
```
Combined with the chunk-2 unconditional K_2-twisted Weil identity, this yields
`Σ' n · K_2(ρ, t) · M(β, ρ) = 0`, the engineering identity for K_2 zeros.

In our notation:
```
RightPrime_{K_2}(t, β) − (Arch_{K_2}(t, β) + ReflectedPrime_{K_2}(t, β))
  = 2π · K_2(1, t) · M(β, 1).
```
where `RightPrime_{K_2}` = `K_2_primeIntegrand_re_two_eq` (closed form),
`ReflectedPrime_{K_2}` = `K_2_reflectedPrime_re_neg_one_eq` (closed form),
and `Arch_{K_2}` = the 5 named shifted arch integrals from
`K_2_archIntegrand_re_neg_one_eq`. -/
def K_2_engineering_target (t β : ℝ) : Prop :=
  (∫ y : ℝ, K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.primeIntegrand β 2 y) -
  ((∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.archIntegrand β (-1) y) +
   (∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))) =
  2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1

/-! ## Step 5a: Prime/reflected-prime difference closed form (no arch) -/

/-- The closed-form expression for `RightPrime_{K_2} − ReflectedPrime_{K_2}`. -/
noncomputable def primeReflectedDifference (t β : ℝ) : ℂ :=
  ((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-(2*t))) : ℝ) : ℂ)) +
  ((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (2*t)) : ℝ) : ℂ)) -
  ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp (-t)) : ℝ) : ℂ)) -
  ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β ((n : ℝ) * Real.exp t) : ℝ) : ℂ)) +
  ((2 * Real.pi : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                   ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) -
  (-((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-(2*t))) : ℝ) : ℂ)) -
  ((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (2*t)) : ℝ) : ℂ)) +
  ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp (-t)) : ℝ) : ℂ)) +
  ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β ((1 / (n : ℝ)) * Real.exp t) : ℝ) : ℂ)) -
  ((2 * Real.pi : ℝ) : ℂ) *
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)))

/-- **Prime / reflected-prime difference.** Subtracting the two K_2 closed forms
gives `primeReflectedDifference`, with no arch involvement. -/
theorem K_2_prime_reflected_difference_eq (t β : ℝ) :
    (∫ y : ℝ, K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.primeIntegrand β 2 y) -
      (∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      primeReflectedDifference t β := by
  rw [K_2_primeIntegrand_re_two_eq t β, K_2_reflectedPrime_re_neg_one_eq t β]
  unfold primeReflectedDifference
  ring

#print axioms K_2_prime_reflected_difference_eq

/-! ## Step 5b: Arch contribution required for engineering identity

Solving `K_2_engineering_target` for the arch contribution gives the exact
shape the 5 named arch integrals `A_α(β)` must produce. -/

/-- The required arch contribution for the engineering target to hold. -/
noncomputable def archRequired (t β : ℝ) : ℂ :=
  primeReflectedDifference t β -
    2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1

/-- **Engineering identity from arch contribution.** If the K_2-twisted left-edge
arch integral equals the required value `archRequired t β`, then
`K_2_engineering_target t β` holds. -/
theorem K_2_engineering_identity_of_arch_eq (t β : ℝ)
    (h_arch_eq :
      (∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.archIntegrand β (-1) y) = archRequired t β) :
    K_2_engineering_target t β := by
  unfold K_2_engineering_target
  set R : ℂ := ∫ y : ℝ, K_2 (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
      Contour.primeIntegrand β 2 y
  set Q : ℂ := ∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
      ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
  set P : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1
  -- After substitution, goal: R - (archRequired + Q) = P.
  rw [h_arch_eq]
  unfold archRequired
  -- archRequired = primeReflectedDifference - P, and primeReflectedDifference = R - Q.
  have h_diff : primeReflectedDifference t β = R - Q :=
    (K_2_prime_reflected_difference_eq t β).symm
  rw [h_diff]
  ring

#print axioms K_2_engineering_identity_of_arch_eq

/-! ## Step 5c: Generic shifted arch integral and 5-component decomposition

Per the user's prescription, factor through a generic per-α shifted arch
integral so the 5-component decomposition is a single combinator over `α`,
not 5 independent proofs. -/

/-- The generic shifted arch integral at the left edge. -/
noncomputable def shiftedArchIntegral (β α : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    Contour.archIntegrand β (-1) y

/-- The K_2-twisted left-edge arch integral as a 5-component sum
of `shiftedArchIntegral` values. -/
noncomputable def K_2_arch (t β : ℝ) : ℂ :=
  ∫ y : ℝ, K_2 (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
    Contour.archIntegrand β (-1) y

/-- **K_2 arch integral as 5-component sum of shifted arch integrals.** -/
theorem K_2_arch_eq_five_shifted (t β : ℝ) :
    K_2_arch t β =
      (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        shiftedArchIntegral β (2*t) +
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        shiftedArchIntegral β (-(2*t)) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        shiftedArchIntegral β t -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        shiftedArchIntegral β (-t) +
      shiftedArchIntegral β 0 := by
  unfold K_2_arch shiftedArchIntegral
  exact K_2_archIntegrand_re_neg_one_eq t β

#print axioms K_2_arch_eq_five_shifted

/-! ## Step 5d: Final close conditional on arch equality

If the 5-component shifted arch combination equals `archRequired t β`,
then `K_2_engineering_target t β` holds. -/

/-- **Final composition:** the engineering identity reduces to a single
algebraic identity on the 5 shifted arch integrals.

If
```
(1/2)·e^{-3t}·A_{2t} + (1/2)·e^{3t}·A_{-2t} − e^{-(3/2)t}·A_{t}
  − e^{(3/2)t}·A_{-t} + A_0 = archRequired t β
```
holds (the load-bearing analytic obligation, where `A_α := shiftedArchIntegral β α`),
then the K_2 engineering target follows. -/
theorem K_2_engineering_identity_of_shifted_arch (t β : ℝ)
    (h_shifted_arch_sum :
      (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        shiftedArchIntegral β (2*t) +
      (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        shiftedArchIntegral β (-(2*t)) -
      Complex.exp (((-(3/2) * t) : ℝ) : ℂ) *
        shiftedArchIntegral β t -
      Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        shiftedArchIntegral β (-t) +
      shiftedArchIntegral β 0 = archRequired t β) :
    K_2_engineering_target t β := by
  apply K_2_engineering_identity_of_arch_eq
  show K_2_arch t β = archRequired t β
  rw [K_2_arch_eq_five_shifted]
  exact h_shifted_arch_sum

#print axioms K_2_engineering_identity_of_shifted_arch

/-! ## Step 5e: Leftover-cancellation route

A two-channel decomposition: split `K_2_arch − archRequired` into a
prime-side leftover and an arch-side leftover that cancel.  This is
useful when the cancellation is structurally clear (FE-paired residuals
on each side) but the individual closed forms are not. -/

/-- **Engineering identity via leftover cancellation.**

If the K_2-twisted left-edge arch integral admits a decomposition
```
K_2_arch t β = (primeReflectedDifference − 2π·K_2(1,t)·M(β,1))
             + leftoverArch − leftoverPrime
```
with `leftoverPrime = leftoverArch`, then the engineering target holds. -/
theorem K_2_engineering_identity_via_leftover (t β : ℝ)
    (leftoverPrime leftoverArch : ℂ)
    (h_decomp : K_2_arch t β =
      primeReflectedDifference t β -
        2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1 +
        leftoverArch - leftoverPrime)
    (h_cancel : leftoverPrime = leftoverArch) :
    K_2_engineering_target t β := by
  apply K_2_engineering_identity_of_arch_eq
  show K_2_arch t β = archRequired t β
  rw [h_decomp, h_cancel]
  unfold archRequired
  ring

#print axioms K_2_engineering_identity_via_leftover

/-! ## Step 5f: Per-t vs t-integrated fallback

The pointwise K_2 engineering identity `Σ' n · K_2(ρ, t) · M(β,ρ) = 0`
is strictly stronger than the t-integrated K version
`Σ' n · K(ρ) · M(β,ρ) = 0`.  Per Plancherel,
```
K(s) = 2π · ∫_{Ioi 0} K_2(s, t) · e^{-2t²} dt.
```
By `K_zeroSum_eq_t_integral_inner_sum` (project), the K-twisted zero sum
equals `2π · ∫ (K_2 inner sum) · e^{-2t²} dt`.  If the per-t K_2
engineering identity fails for some t but the t-integrated K version
succeeds, the leftover-cancellation route should be applied at the K
level after Gaussian t-integration.  This file's per-t structure is
designed to compose either way. -/

/-! ## Step 6: Digamma form of `Γℝ'/Γℝ` -/

/-- **Logarithmic derivative of `Γℝ` in digamma form.**

```
(Γℝ)'(s) / Γℝ(s) = -(log π)/2 + (1/2) · Γ'(s/2) / Γ(s/2)
```

Direct differentiation of `Γℝ(s) = π^{-s/2}·Γ(s/2)` via product + chain rules. -/
theorem Gammaℝ_logDeriv_digamma_form (s : ℂ)
    (hs : ∀ m : ℕ, s ≠ -(2 * (m : ℂ))) :
    deriv Complex.Gammaℝ s / s.Gammaℝ =
      -(Complex.log Real.pi) / 2 +
        (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  -- s/2 ≠ -m for all m : ℕ.
  have hs_half : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hs m
    have h2 : s = 2 * (s / 2) := by ring
    rw [h2, h]; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπpow_ne : (Real.pi : ℂ)^(-s/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have h_Γ_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs_half
  have h_Γℝ_ne : s.Gammaℝ ≠ 0 := by
    rw [Complex.Gammaℝ_def]; exact mul_ne_zero hπpow_ne h_Γ_ne
  -- HasDerivAt (s ↦ -s/2) (-1/2) s.
  have h_neg_half : HasDerivAt (fun w : ℂ => -w / 2) (-(1 : ℂ) / 2) s := by
    have h1 : HasDerivAt (fun w : ℂ => -w) (-(1 : ℂ)) s := (hasDerivAt_id s).neg
    exact h1.div_const 2
  -- HasDerivAt (s ↦ π^{-s/2}) (π^{-s/2} · log π · (-1/2)) s.
  have h_πpow : HasDerivAt (fun w : ℂ => (Real.pi : ℂ)^(-w/2))
      ((Real.pi : ℂ)^(-s/2) * Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2)) s :=
    h_neg_half.const_cpow (Or.inl hπ)
  -- HasDerivAt (s ↦ s/2) (1/2) s.
  have h_half : HasDerivAt (fun w : ℂ => w / 2) ((1 : ℂ) / 2) s :=
    (hasDerivAt_id s).div_const 2
  -- HasDerivAt Complex.Gamma (deriv Γ at s/2) (s/2).
  have h_Γ_at : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s/2)) (s/2) :=
    (Complex.differentiableAt_Gamma (s/2) hs_half).hasDerivAt
  -- HasDerivAt (s ↦ Γ(s/2)) ((1/2)·Γ'(s/2)) s via chain rule.
  have h_Γ_comp : HasDerivAt (fun w : ℂ => Complex.Gamma (w/2))
      (deriv Complex.Gamma (s/2) * ((1 : ℂ) / 2)) s :=
    h_Γ_at.comp s h_half
  -- Product rule: HasDerivAt (s ↦ π^{-s/2} · Γ(s/2)) ... s.
  have h_prod := h_πpow.mul h_Γ_comp
  -- Match Γℝ to π^{-s/2}·Γ(s/2).
  have h_Γℝ_eq_fn : (fun w : ℂ => w.Gammaℝ) =
      (fun w : ℂ => (Real.pi : ℂ)^(-w/2) * Complex.Gamma (w/2)) := by
    funext w; exact Complex.Gammaℝ_def w
  have h_deriv_Γℝ_at : HasDerivAt (fun w : ℂ => w.Gammaℝ)
      ((Real.pi : ℂ)^(-s/2) * Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2) *
        Complex.Gamma (s/2) +
        (Real.pi : ℂ)^(-s/2) * (deriv Complex.Gamma (s/2) * ((1 : ℂ) / 2))) s := by
    rw [h_Γℝ_eq_fn]; exact h_prod
  have h_deriv_eq : deriv Complex.Gammaℝ s =
      (Real.pi : ℂ)^(-s/2) * Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2) *
        Complex.Gamma (s/2) +
        (Real.pi : ℂ)^(-s/2) * (deriv Complex.Gamma (s/2) * ((1 : ℂ) / 2)) :=
    h_deriv_Γℝ_at.deriv
  rw [h_deriv_eq, Complex.Gammaℝ_def]
  field_simp

/-! ## Step 7: Three-named-piece decomposition of `shiftedArchIntegral`

Per the audit-by-difference plan, `shiftedArchIntegral β α` decomposes via the
digamma form into three integrals over `ℝ`:

* `constantLogPiShiftedArchIntegral β α := ∫ y, exp(iyα)·M(β,-1+iy) dy`,
  the carrier of the `-log π` constant.
* `digammaLeftHalfShiftedArchIntegral β α := ∫ y, exp(iyα)·Γ'/Γ((-1+iy)/2)·M(β,-1+iy) dy`,
  the inner-edge half-argument digamma piece.
* `digammaRightHalfShiftedArchIntegral β α := ∫ y, exp(iyα)·Γ'/Γ((2-iy)/2)·M(β,-1+iy) dy`,
  the outer-edge half-argument digamma piece.

Honest status: the constant piece is closed-form (`mellin_shifted_re_neg_one`),
the two digamma pieces are the load-bearing analytic obligations.  We do
**not** guess the closed-form RHS from `archRequired`; the matching audit is
performed downstream once the digamma pieces are reduced. -/

/-- Constant-`log π` carrier: `∫ y, exp(iyα)·M(β,-1+iy) dy` (no `log π` factor;
the `-log π` is multiplied in by the decomposition). -/
noncomputable def constantLogPiShiftedArchIntegral (β α : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Inner-edge half-argument digamma shifted integral. -/
noncomputable def digammaLeftHalfShiftedArchIntegral (β α : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
       Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Outer-edge half-argument digamma shifted integral. -/
noncomputable def digammaRightHalfShiftedArchIntegral (β α : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
       Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- **Constant-piece closed form (unconditional sub-lemma).**

```
∫ y, exp(iyα)·M(β,-1+iy) dy = 2π · e^α · test_β(e^{-α})
```

Direct re-export of `mellin_shifted_re_neg_one`.  This is the sanity check on
the `-log π` carrier.  No integrability assumption is needed: the underlying
integral identity is `pairTestMellin_vertical_integral_at_neg_one_pos`, an
unconditional Mellin inversion. -/
theorem constantLogPiShiftedArchIntegral_eq (β α : ℝ) :
    constantLogPiShiftedArchIntegral β α =
      ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (Real.exp (-α)) : ℝ) : ℂ) := by
  unfold constantLogPiShiftedArchIntegral
  exact mellin_shifted_re_neg_one β α

#print axioms constantLogPiShiftedArchIntegral_eq

/-- Pole-avoidance for `s = -1 + iy`: real part `-1` is never in
the pole locus `{0, -2, -4, …}` of `Γℝ`. -/
private lemma neg_one_plus_iy_avoids_Gammaℝ_poles (y : ℝ) :
    ∀ m : ℕ, ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ -(2 * (m : ℂ)) := by
  intro m heq
  have hre := congr_arg Complex.re heq
  simp at hre
  have h2m : (2 * (m : ℝ)) = 1 := by linarith
  have h2m_nat : (2 * m : ℕ) = 1 := by exact_mod_cast h2m
  omega

/-- Pole-avoidance for `s = 2 - iy`: real part `2` is positive, never in
the pole locus `{0, -2, -4, …}` of `Γℝ`. -/
private lemma two_minus_iy_avoids_Gammaℝ_poles (y : ℝ) :
    ∀ m : ℕ, ((2 : ℝ) : ℂ) - (y : ℂ) * I ≠ -(2 * (m : ℂ)) := by
  intro m heq
  have hre := congr_arg Complex.re heq
  simp at hre
  have hnonneg : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  linarith

/-- **Pointwise digamma rewrite of `archIntegrand β (-1) y`.**

Apply `Gammaℝ_logDeriv_digamma_form` at both `s = -1 + iy` and `s = 2 - iy`,
both of which avoid the `Γℝ` pole locus, to expand the bracket factor. -/
private lemma archIntegrand_neg_one_pointwise_digamma (β y : ℝ) :
    Contour.archIntegrand β (-1) y =
      (-(Complex.log (Real.pi : ℂ)) +
        (1/2 : ℂ) *
          (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
             Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
        (1/2 : ℂ) *
          (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
             Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have h_d1 := Gammaℝ_logDeriv_digamma_form (((-1 : ℝ) : ℂ) + (y : ℂ) * I)
    (neg_one_plus_iy_avoids_Gammaℝ_poles y)
  have h_d2 := Gammaℝ_logDeriv_digamma_form (((2 : ℝ) : ℂ) - (y : ℂ) * I)
    (two_minus_iy_avoids_Gammaℝ_poles y)
  have hsub : (1 : ℂ) - (((-1 : ℝ) : ℂ) - (y : ℂ) * I) =
      ((2 : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  unfold Contour.archIntegrand
  -- Massage `1 - (((-1):ℝ):ℂ) + (y:ℂ)*I` literal in archIntegrand to `2 - yi`.
  have hreflect : (1 : ℂ) - ((((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((2 : ℝ) : ℂ) - (y : ℂ) * I := by push_cast; ring
  rw [hreflect, h_d1, h_d2]
  ring

/-- **Three-piece decomposition of `shiftedArchIntegral`.**

Conditional on integrability of each summand, the digamma form gives:
```
shiftedArchIntegral β α =
  -(log π) · constantLogPiShiftedArchIntegral β α
  + (1/2) · digammaLeftHalfShiftedArchIntegral β α
  + (1/2) · digammaRightHalfShiftedArchIntegral β α.
```
-/
theorem shiftedArchIntegral_three_piece_decomposition (β α : ℝ)
    (h_const_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_left_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :
    shiftedArchIntegral β α =
      -(Complex.log (Real.pi : ℂ)) * constantLogPiShiftedArchIntegral β α +
      (1/2 : ℂ) * digammaLeftHalfShiftedArchIntegral β α +
      (1/2 : ℂ) * digammaRightHalfShiftedArchIntegral β α := by
  -- Split via the 3-term helper; first reframe integrands.
  set f1 : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf1
  set f2 : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
         Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf2
  set f3 : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
         Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf3
  have h1 : Integrable f1 := h_const_int
  have h2 : Integrable f2 := h_left_int
  have h3 : Integrable f3 := h_right_int
  have hI1 : Integrable (fun y => -(Complex.log (Real.pi : ℂ)) * f1 y) :=
    h1.const_mul _
  have hI2 : Integrable (fun y => (1/2 : ℂ) * f2 y) := h2.const_mul _
  have hI3 : Integrable (fun y => (1/2 : ℂ) * f3 y) := h3.const_mul _
  have hI12 : Integrable (fun y => -(Complex.log (Real.pi : ℂ)) * f1 y +
      (1/2 : ℂ) * f2 y) := hI1.add hI2
  unfold shiftedArchIntegral constantLogPiShiftedArchIntegral
    digammaLeftHalfShiftedArchIntegral digammaRightHalfShiftedArchIntegral
  show ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.archIntegrand β (-1) y =
      -(Complex.log (Real.pi : ℂ)) * (∫ y, f1 y) +
      (1/2 : ℂ) * (∫ y, f2 y) + (1/2 : ℂ) * (∫ y, f3 y)
  -- Pointwise rewrite of integrand into 3-term combination.
  have h_pw : (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.archIntegrand β (-1) y) =
    (fun y => -(Complex.log (Real.pi : ℂ)) * f1 y +
              (1/2 : ℂ) * f2 y + (1/2 : ℂ) * f3 y) := by
    funext y
    rw [archIntegrand_neg_one_pointwise_digamma β y, hf1, hf2, hf3]
    ring
  rw [h_pw]
  -- Split via integral_add (twice) and integral_const_mul (three times).
  rw [MeasureTheory.integral_add hI12 hI3]
  rw [MeasureTheory.integral_add hI1 hI2]
  rw [show (∫ a : ℝ, -(Complex.log (Real.pi : ℂ)) * f1 a) =
        -(Complex.log (Real.pi : ℂ)) * ∫ y : ℝ, f1 y from
      MeasureTheory.integral_const_mul (-(Complex.log (Real.pi : ℂ))) f1,
      show (∫ a : ℝ, (1/2 : ℂ) * f2 a) = (1/2 : ℂ) * ∫ y : ℝ, f2 y from
      MeasureTheory.integral_const_mul (1/2 : ℂ) f2,
      show (∫ a : ℝ, (1/2 : ℂ) * f3 a) = (1/2 : ℂ) * ∫ y : ℝ, f3 y from
      MeasureTheory.integral_const_mul (1/2 : ℂ) f3]

#print axioms shiftedArchIntegral_three_piece_decomposition

/-- **Closed-form (partial) of `shiftedArchIntegral` with constant piece evaluated.**

Combines `shiftedArchIntegral_three_piece_decomposition` with
`constantLogPiShiftedArchIntegral_eq` to produce:
```
shiftedArchIntegral β α =
  -(log π) · 2π · e^α · test_β(e^{-α})
  + (1/2) · digammaLeftHalfShiftedArchIntegral β α
  + (1/2) · digammaRightHalfShiftedArchIntegral β α.
```
The two digamma pieces remain to be reduced (Mittag-Leffler + termwise
Mellin inversion).  This is the **derived** closed form; the audit against
`archRequired` (matching trivial-zero residues against
`primeReflectedDifference`) is downstream. -/
theorem shiftedArchIntegral_partial_closed_form (β α : ℝ)
    (h_const_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_left_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int :
      Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :
    shiftedArchIntegral β α =
      -(Complex.log (Real.pi : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-α)) : ℝ) : ℂ)) +
      (1/2 : ℂ) * digammaLeftHalfShiftedArchIntegral β α +
      (1/2 : ℂ) * digammaRightHalfShiftedArchIntegral β α := by
  rw [shiftedArchIntegral_three_piece_decomposition β α h_const_int h_left_int h_right_int,
      constantLogPiShiftedArchIntegral_eq]

#print axioms shiftedArchIntegral_partial_closed_form

/-! ## Step 7b: Unconditional 2-piece decomposition

By **`archIntegrand_at_neg_one_integrable`** (project, unconditional) and
**`pairTestMellin_vertical_integrable_at_neg_one`** (project, unconditional),
the shifted variants are integrable via `|exp(iyα)| = 1` (norm-1 multiplier).

This gives the unconditional **2-piece** decomposition

```
shiftedArchIntegral β α =
  -(log π) · constantLogPiShiftedArchIntegral β α +
  digammaSumShiftedArchIntegral β α
```

with `digammaSumShiftedArchIntegral` the consolidated digamma piece
(half-arg sum, no individual halving).  The downstream split into
`digammaLeftHalf` + `digammaRightHalf` is a separate analytic obligation
(half-argument digamma identities + Mittag-Leffler).
-/

/-- Consolidated digamma half-argument sum integral on the shifted left edge.
The half-arguments at `(-1+iy)/2` and `(2-iy)/2` are kept inside one integral;
splitting them is a separate analytic step. -/
noncomputable def digammaSumShiftedArchIntegral (β α : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    ((1/2 : ℂ) *
      (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
         Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
     (1/2 : ℂ) *
      (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
         Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Norm-1 bound on `y ↦ exp(iyα)`. -/
private lemma norm_exp_iyα_le_one (α : ℝ) :
    ∀ y : ℝ, ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ ≤ 1 := by
  intro y
  rw [show ((y * α : ℝ) : ℂ) * I = (((y * α : ℝ)) : ℂ) * I from rfl]
  -- exp of pure imaginary has norm 1.
  have h_im : (((y * α : ℝ) : ℂ) * I).re = 0 := by simp
  rw [Complex.norm_exp, h_im, Real.exp_zero]

/-- AE strong measurability of `y ↦ exp(iyα)` (it's continuous). -/
private lemma exp_iyα_aestronglyMeasurable (α : ℝ) :
    AEStronglyMeasurable
      (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) MeasureTheory.volume := by
  exact (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
      |>.mul continuous_const)).aestronglyMeasurable

/-- **Unconditional integrability of the constant-`log π` integrand.**
Reduces to `pairTestMellin_vertical_integrable_at_neg_one` via norm-1 of the
Fourier shift. -/
theorem constantLogPiShiftedArchIntegrand_integrable (β α : ℝ) :
    Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h_M : Integrable (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
    -- VerticalIntegrable f σ = Integrable (fun y => f (σ + y * I))
    convert h using 1
  exact h_M.bdd_mul (exp_iyα_aestronglyMeasurable α)
    (Filter.Eventually.of_forall (norm_exp_iyα_le_one α))

#print axioms constantLogPiShiftedArchIntegrand_integrable

/-- **Unconditional integrability of the shifted whole-arch integrand.**
Reduces to `archIntegrand_at_neg_one_integrable` via norm-1 of the
Fourier shift. -/
theorem shiftedArchIntegrand_integrable (β α : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.archIntegrand β (-1) y) := by
  have h_arch : Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  exact h_arch.bdd_mul (exp_iyα_aestronglyMeasurable α)
    (Filter.Eventually.of_forall (norm_exp_iyα_le_one α))

#print axioms shiftedArchIntegrand_integrable

/-- **Unconditional integrability of the digamma-sum integrand.**
Derived as the difference between the shifted-arch integrand and the
log π scaled constant integrand, via the pointwise digamma rewrite. -/
theorem digammaSumShiftedArchIntegrand_integrable (β α : ℝ) :
    Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
       (1/2 : ℂ) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h_arch_sh := shiftedArchIntegrand_integrable β α
  have h_const_sh := constantLogPiShiftedArchIntegrand_integrable β α
  have h_logpi_sh : Integrable (fun y : ℝ =>
      -(Complex.log (Real.pi : ℂ)) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    h_const_sh.const_mul _
  -- Rewrite arch integrand pointwise as `-log π · M-piece + digamma-sum-piece`.
  have h_pw : ∀ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.archIntegrand β (-1) y -
        -(Complex.log (Real.pi : ℂ)) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((1/2 : ℂ) *
            (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
               Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
           (1/2 : ℂ) *
            (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
               Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro y
    rw [archIntegrand_neg_one_pointwise_digamma β y]
    ring
  refine (h_arch_sh.sub h_logpi_sh).congr ?_
  exact Filter.Eventually.of_forall h_pw

#print axioms digammaSumShiftedArchIntegrand_integrable

/-- **Unconditional 2-piece decomposition of `shiftedArchIntegral`.**

```
shiftedArchIntegral β α =
  -(log π) · constantLogPiShiftedArchIntegral β α +
  digammaSumShiftedArchIntegral β α.
```

No integrability hypotheses — derived from the project-level unconditional
integrability of `archIntegrand β (-1)` and `pairTestMellin β (-1+iy)`. -/
theorem shiftedArchIntegral_two_piece_decomposition_unconditional (β α : ℝ) :
    shiftedArchIntegral β α =
      -(Complex.log (Real.pi : ℂ)) * constantLogPiShiftedArchIntegral β α +
      digammaSumShiftedArchIntegral β α := by
  unfold shiftedArchIntegral constantLogPiShiftedArchIntegral
    digammaSumShiftedArchIntegral
  set f1 : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf1
  set f2 : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
       (1/2 : ℂ) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf2
  have h1 : Integrable f1 := constantLogPiShiftedArchIntegrand_integrable β α
  have h2 : Integrable f2 := digammaSumShiftedArchIntegrand_integrable β α
  have hI1 : Integrable (fun y => -(Complex.log (Real.pi : ℂ)) * f1 y) :=
    h1.const_mul _
  show ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) * Contour.archIntegrand β (-1) y =
      -(Complex.log (Real.pi : ℂ)) * (∫ y, f1 y) + (∫ y, f2 y)
  have h_pw : (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.archIntegrand β (-1) y) =
    (fun y => -(Complex.log (Real.pi : ℂ)) * f1 y + f2 y) := by
    funext y
    rw [archIntegrand_neg_one_pointwise_digamma β y, hf1, hf2]
    ring
  rw [h_pw, MeasureTheory.integral_add hI1 h2]
  rw [show (∫ a : ℝ, -(Complex.log (Real.pi : ℂ)) * f1 a) =
        -(Complex.log (Real.pi : ℂ)) * ∫ y : ℝ, f1 y from
      MeasureTheory.integral_const_mul (-(Complex.log (Real.pi : ℂ))) f1]

#print axioms shiftedArchIntegral_two_piece_decomposition_unconditional

/-- **Unconditional 2-piece partial closed form of `shiftedArchIntegral`.**

```
shiftedArchIntegral β α =
  -(log π) · 2π · e^α · test_β(e^{-α}) + digammaSumShiftedArchIntegral β α.
```

The remaining analytic obligation is `digammaSumShiftedArchIntegral`, evaluated
via half-argument digamma identities + Mittag-Leffler termwise Mellin inversion. -/
theorem shiftedArchIntegral_two_piece_partial_closed_form_unconditional (β α : ℝ) :
    shiftedArchIntegral β α =
      -(Complex.log (Real.pi : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp α : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-α)) : ℝ) : ℂ)) +
      digammaSumShiftedArchIntegral β α := by
  rw [shiftedArchIntegral_two_piece_decomposition_unconditional β α,
      constantLogPiShiftedArchIntegral_eq]

#print axioms shiftedArchIntegral_two_piece_partial_closed_form_unconditional

/-! ## Step 8: Recurrence-based half-argument rewrite

The integrand `(1/2)·Γ'/Γ((-1+iy)/2) + (1/2)·Γ'/Γ((2-iy)/2)` mixes a
negative-real-part argument `(-1+iy)/2 = -1/2 + iy/2` with a positive-real-part
argument `(2-iy)/2 = 1 - iy/2`.  The project's `digamma_eq_series` requires
`Re s > 0`, so the digamma series cannot be applied directly to the left
half-argument.  Use the recurrence

```
ψ(z) = ψ(z+1) − 1/z
```

with `z = (-1+iy)/2`, `z + 1 = (1+iy)/2 = 1/2 + iy/2` (Re = 1/2 > 0) to
move it into the right half-plane plus an explicit rational correction.
The right half-argument is already `Re = 1`. -/

/-- `deriv Γ(s) / Γ(s) = Complex.digamma s` (definitional via `logDeriv`). -/
private lemma logDeriv_Gamma_eq_digamma (s : ℂ) :
    deriv Complex.Gamma s / Complex.Gamma s = Complex.digamma s := by
  rw [Complex.digamma_def, logDeriv_apply]

/-- Pole-avoidance for `s = (-1+iy)/2` against `{0, -1, -2, …}`.
  The pole locus of `Complex.Gamma`. -/
private lemma half_neg_one_plus_iy_avoids_neg_nat (y : ℝ) :
    ∀ m : ℕ, ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) ≠ -(m : ℂ) := by
  intro m heq
  have hre := congr_arg Complex.re heq
  simp at hre
  -- `hre : -(1/2 : ℝ) = -m`  ⇒  `2 * m = 1` (impossible for `m : ℕ`).
  have h2m : (2 * (m : ℝ)) = 1 := by linarith
  have h2m_nat : (2 * m : ℕ) = 1 := by exact_mod_cast h2m
  omega

/-- **Left half-arg digamma rewrite via the recurrence `ψ(z+1) = ψ(z) + 1/z`.**

For all `y : ℝ`,
```
ψ((-1+iy)/2) = ψ((1+iy)/2) − 1/((-1+iy)/2)
            = ψ(1/2 + iy/2) − 2/(-1+iy).
```
-/
theorem digamma_left_half_rewrite_to_positive_half (y : ℝ) :
    Complex.digamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) =
      Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) -
      1 / ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) := by
  set z : ℂ := ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) with hz
  have h_z_avoid : ∀ m : ℕ, z ≠ -(m : ℂ) :=
    half_neg_one_plus_iy_avoids_neg_nat y
  have h_recur : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ :=
    Complex.digamma_apply_add_one z h_z_avoid
  -- z + 1 = 1/2 + iy/2.
  have hz_plus_one : z + 1 = ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) := by
    rw [hz]; push_cast; ring
  rw [hz_plus_one] at h_recur
  -- Solve for `digamma z`: from `digamma(z+1) = digamma z + z⁻¹`,
  -- get `digamma z = digamma(z+1) - z⁻¹` then convert `z⁻¹ = 1/z`.
  have h_solve : Complex.digamma z =
      Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) - z⁻¹ := by
    linear_combination -h_recur
  rw [h_solve, hz, inv_eq_one_div]

#print axioms digamma_left_half_rewrite_to_positive_half

/-- **Paired half-argument rewrite into positive real parts.**

```
(1/2)·ψ((-1+iy)/2) + (1/2)·ψ((2-iy)/2) =
  (1/2)·ψ(1/2 + iy/2) + (1/2)·ψ(1 - iy/2) − (1/2)·(2/(-1+iy)).
```

The two right-hand digamma terms have positive real part `1/2` and `1`
respectively, so `digamma_eq_series` applies.  The rational correction
`(1/2)·(2/(-1+iy)) = 1/(-1+iy)` is the load-bearing residue carrier. -/
theorem digamma_pair_to_positive_real_parts (y : ℝ) :
    (1/2 : ℂ) * Complex.digamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) +
      (1/2 : ℂ) * Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) =
    (1/2 : ℂ) * Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) +
      (1/2 : ℂ) * Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) -
      (1/2 : ℂ) / ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) := by
  rw [digamma_left_half_rewrite_to_positive_half y]
  ring

#print axioms digamma_pair_to_positive_real_parts

/-- Note: `(2-iy)/2 = 1 - iy/2 = ((1:ℝ):ℂ) - ((y/2:ℝ):ℂ) * I`.
The right half-argument is already in canonical form `1 - iy/2`. -/
private lemma right_half_arg_form (y : ℝ) :
    ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) =
      ((((1 : ℝ) : ℂ)) - ((y / 2 : ℝ) : ℂ) * I) := by
  push_cast; ring

/-! ## Step 9: Three-piece isolation — rational correction named explicitly

After Step 8's recurrence rewrite, the digamma-sum integrand at every `y`
equals
```
(1/2)·exp(iyα)·ψ(1/2+iy/2)·M(β,-1+iy)
+ (1/2)·exp(iyα)·ψ(1-iy/2)·M(β,-1+iy)
- exp(iyα)·(1/(-1+iy))·M(β,-1+iy).
```

So `digammaSumShiftedArchIntegral β α` splits (integrability permitting) into
three named transforms:
- `digammaPosHalfShiftedArchIntegralLeft β α` (`(1/2)·ψ(1/2+iy/2)` carrier),
- `digammaPosHalfShiftedArchIntegralRight β α` (`(1/2)·ψ(1-iy/2)` carrier),
- `digammaRationalCorrectionIntegral β α` (the `-1/(-1+iy)` carrier).

The rational correction is **isolated as a named integral**, NOT buried in
the pole sums.  All `1/2` coefficients are visible.  No `-γ` extraction yet
(that comes at Step 10 when `digamma_eq_series` is applied to the two
positive-real-part `ψ`-pieces). -/

/-- Left positive-real-part half-arg digamma transform (Re = 1/2 after
recurrence). -/
noncomputable def digammaPosHalfShiftedArchIntegralLeft (β α : ℝ) : ℂ :=
  (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Right positive-real-part half-arg digamma transform (Re = 1, unchanged). -/
noncomputable def digammaPosHalfShiftedArchIntegralRight (β α : ℝ) : ℂ :=
  (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Rational correction integral (`-1/(-1+iy)` carrier).  Load-bearing residue
carrier from the left half-arg recurrence shift. -/
noncomputable def digammaRationalCorrectionIntegral (β α : ℝ) : ℂ :=
  -∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Pointwise rewrite: `deriv Γ s / Γ s = Complex.digamma s` under the integral
sign for the digamma-sum integrand. -/
private lemma digammaSum_integrand_eq_digamma_form (β α y : ℝ) :
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
       (1/2 : ℂ) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        Complex.digamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) +
       (1/2 : ℂ) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  rw [logDeriv_Gamma_eq_digamma, logDeriv_Gamma_eq_digamma]

/-- Pointwise three-piece expansion of the digamma-sum integrand using the
half-arg recurrence (Step 8). -/
private lemma digammaSum_integrand_three_piece_pointwise (β α y : ℝ) :
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
       (1/2 : ℂ) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
    (1/2 : ℂ) *
      (Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
    (1/2 : ℂ) *
      (Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  rw [digammaSum_integrand_eq_digamma_form, digamma_pair_to_positive_real_parts]
  -- Goal now: exp · (...) · M = (1/2)·(exp · ψ(1/2+iy/2) · M) + (1/2)·(exp · ψ((2-iy)/2) · M)
  --                              − exp · (1/(-1+iy)) · M
  -- The recurrence gives `(1/2)·(1/((-1+iy)/2)) = 1/(-1+iy)`, cleaning the rational term.
  have h_rat : (1/2 : ℂ) / ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) =
      1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
    by_cases h : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = 0
    · rw [h]; simp
    · field_simp
  rw [show ((1/2 : ℂ) *
            Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) +
           (1/2 : ℂ) *
            Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) -
            (1/2 : ℂ) / ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) =
        ((1/2 : ℂ) *
            Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) +
           (1/2 : ℂ) *
            Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) -
            1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) from by rw [h_rat]]
  ring

/-- **Three-piece decomposition of `digammaSumShiftedArchIntegral`**
(conditional on integrability of each piece).

```
digammaSumShiftedArchIntegral β α =
  digammaPosHalfShiftedArchIntegralLeft β α +
  digammaPosHalfShiftedArchIntegralRight β α +
  digammaRationalCorrectionIntegral β α.
```

The `−γ` extraction (constant Euler-Mascheroni piece) and pole-series form
come at Step 10 via `digamma_eq_series` applied to each `ψ`-piece. -/
theorem digammaSumShiftedArchIntegral_three_piece_decomposition
    (β α : ℝ)
    (h_left_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_rat_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :
    digammaSumShiftedArchIntegral β α =
      digammaPosHalfShiftedArchIntegralLeft β α +
      digammaPosHalfShiftedArchIntegralRight β α +
      digammaRationalCorrectionIntegral β α := by
  unfold digammaSumShiftedArchIntegral digammaPosHalfShiftedArchIntegralLeft
    digammaPosHalfShiftedArchIntegralRight digammaRationalCorrectionIntegral
  -- Set up named integrand functions for left/right/rational pieces.
  set fL : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hfL
  set fR : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hfR
  set fQ : ℝ → ℂ := fun y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hfQ
  have hL : Integrable fL := h_left_int
  have hR : Integrable fR := h_right_int
  have hQ : Integrable fQ := h_rat_int
  have hI_halfL : Integrable (fun y => (1/2 : ℂ) * fL y) := hL.const_mul _
  have hI_halfR : Integrable (fun y => (1/2 : ℂ) * fR y) := hR.const_mul _
  have hI_halfLR : Integrable (fun y => (1/2 : ℂ) * fL y + (1/2 : ℂ) * fR y) :=
    hI_halfL.add hI_halfR
  -- Pointwise: integrand = (1/2)·fL + (1/2)·fR − fQ.
  have h_pw : (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1/2 : ℂ) *
        (deriv Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2) /
           Complex.Gamma ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2)) +
       (1/2 : ℂ) *
        (deriv Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) /
           Complex.Gamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
    (fun y => (1/2 : ℂ) * fL y + (1/2 : ℂ) * fR y - fQ y) := by
    funext y
    rw [digammaSum_integrand_three_piece_pointwise β α y, hfL, hfR, hfQ]
  rw [h_pw]
  -- Split via integral_sub then integral_add then integral_const_mul x2.
  rw [MeasureTheory.integral_sub hI_halfLR hQ]
  rw [MeasureTheory.integral_add hI_halfL hI_halfR]
  rw [show (∫ a : ℝ, (1/2 : ℂ) * fL a) = (1/2 : ℂ) * ∫ y : ℝ, fL y from
      MeasureTheory.integral_const_mul (1/2 : ℂ) fL,
      show (∫ a : ℝ, (1/2 : ℂ) * fR a) = (1/2 : ℂ) * ∫ y : ℝ, fR y from
      MeasureTheory.integral_const_mul (1/2 : ℂ) fR]
  -- Goal: (1/2)·∫fL + (1/2)·∫fR − ∫fQ = (1/2)·∫fL + (1/2)·∫fR + (-∫fQ)
  ring

#print axioms digammaSumShiftedArchIntegral_three_piece_decomposition

/-! ## Step 10: Pole-kernel expansion via Mittag-Leffler `digamma_eq_series`

For the two positive-real-part `ψ`-pieces from Step 9, apply
`digamma_eq_series` (project, axiom-clean):
```
ψ(z) = -γ + Σ_{k≥0} (1/(k+1) - 1/(k + z)),    Re z > 0.
```

* Left piece (`z = 1/2 + iy/2`, Re = 1/2 > 0): denominators `k + 1/2 + iy/2`.
* Right piece (`z = (2-iy)/2 = 1 - iy/2`, Re = 1 > 0): denominators `k + 1 - iy/2`.

The `−γ` constants from each `(1/2)·ψ(·)` carrier combine to `−γ` exactly.
The two pole towers carry distinct index conventions (`+1/2` vs `+1`); they
are NOT merged.  The rational correction from Step 9 stays separate. -/

/-- **Left pole kernel at index `k`.** Half-coefficient `(1/2)` visible.
Denominators `k + 1` and `k + 1/2 + iy/2`. -/
noncomputable def digammaPoleKernelLeft (k : ℕ) (β α : ℝ) : ℂ :=
  (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    ((1 / ((k : ℂ) + 1)) -
     (1 / ((k : ℂ) + ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)))) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- **Right pole kernel at index `k`.** Half-coefficient `(1/2)` visible.
Denominators `k + 1` and `k + 1 - iy/2` (canonical `(2-iy)/2`). -/
noncomputable def digammaPoleKernelRight (k : ℕ) (β α : ℝ) : ℂ :=
  (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
    ((1 / ((k : ℂ) + 1)) -
     (1 / ((k : ℂ) + ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)))) *
    Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)

/-- Pole-series target for the **left** half-arg digamma transform.
Holds when the termwise integration swap `∫ Σ = Σ ∫` is justified
(via dominated convergence on partial sums or `MeasureTheory.integral_tsum`,
domination by Schwartz-decay × `Σ 1/(k+1)²` from `digamma_series_summable`).

```
digammaPosHalfShiftedArchIntegralLeft β α =
  −γ/2 · constantLogPiShiftedArchIntegral β α +
  Σ' k, digammaPoleKernelLeft k β α
```
-/
def digammaPosHalfLeft_pole_series_target (β α : ℝ) : Prop :=
  digammaPosHalfShiftedArchIntegralLeft β α =
    -(Real.eulerMascheroniConstant : ℂ) / 2 *
        constantLogPiShiftedArchIntegral β α +
    ∑' k : ℕ, digammaPoleKernelLeft k β α

/-- Pole-series target for the **right** half-arg digamma transform. -/
def digammaPosHalfRight_pole_series_target (β α : ℝ) : Prop :=
  digammaPosHalfShiftedArchIntegralRight β α =
    -(Real.eulerMascheroniConstant : ℂ) / 2 *
        constantLogPiShiftedArchIntegral β α +
    ∑' k : ℕ, digammaPoleKernelRight k β α

/-- **Pole-series form of `digammaSumShiftedArchIntegral`** (combining Step 9
and the two pole-series swaps).

Combines:
- Step 9's three-piece isolation (with three integrability hypotheses).
- Pole-series swaps for left and right half-arg transforms.

Output: the user's exact target form,
```
digammaSumShiftedArchIntegral β α =
  −γ · constantLogPiShiftedArchIntegral β α +
  (Σ' k, digammaPoleKernelLeft k β α) +
  (Σ' k, digammaPoleKernelRight k β α) +
  digammaRationalCorrectionIntegral β α.
```

The two `−γ/2` constants from the two pole-series swaps combine to the single
`−γ` carrier.  All `1/2` coefficients are absorbed into the pole-kernel
definitions; the rational correction is preserved as a named integral. -/
theorem digammaSumShiftedArchIntegral_eq_constant_plus_poles_plus_rational
    (β α : ℝ)
    (h_left_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_rat_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_left_pole : digammaPosHalfLeft_pole_series_target β α)
    (h_right_pole : digammaPosHalfRight_pole_series_target β α) :
    digammaSumShiftedArchIntegral β α =
      -(Real.eulerMascheroniConstant : ℂ) *
        constantLogPiShiftedArchIntegral β α +
      (∑' k : ℕ, digammaPoleKernelLeft k β α) +
      (∑' k : ℕ, digammaPoleKernelRight k β α) +
      digammaRationalCorrectionIntegral β α := by
  rw [digammaSumShiftedArchIntegral_three_piece_decomposition β α
        h_left_int h_right_int h_rat_int]
  rw [show digammaPosHalfLeft_pole_series_target β α =
        (digammaPosHalfShiftedArchIntegralLeft β α =
          -(Real.eulerMascheroniConstant : ℂ) / 2 *
              constantLogPiShiftedArchIntegral β α +
          ∑' k : ℕ, digammaPoleKernelLeft k β α) from rfl] at h_left_pole
  rw [show digammaPosHalfRight_pole_series_target β α =
        (digammaPosHalfShiftedArchIntegralRight β α =
          -(Real.eulerMascheroniConstant : ℂ) / 2 *
              constantLogPiShiftedArchIntegral β α +
          ∑' k : ℕ, digammaPoleKernelRight k β α) from rfl] at h_right_pole
  rw [h_left_pole, h_right_pole]
  ring

#print axioms digammaSumShiftedArchIntegral_eq_constant_plus_poles_plus_rational

/-- **First closed arch shape** — combines Step 7b's `−log π` carrier with
Step 10's `−γ` carrier into the canonical form.

```
shiftedArchIntegral β α =
  −(log π + γ) · constantLogPiShiftedArchIntegral β α +
  (Σ' k, digammaPoleKernelLeft k β α) +
  (Σ' k, digammaPoleKernelRight k β α) +
  digammaRationalCorrectionIntegral β α.
```

The constant carrier `constantLogPiShiftedArchIntegral β α =
2π · e^α · test_β(e^{-α})` is the same for both `log π` and `γ` terms.
The two pole towers and the rational correction remain explicit; no
matching against `archRequired` yet. -/
theorem shiftedArchIntegral_first_closed_arch_shape
    (β α : ℝ)
    (h_left_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_rat_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_left_pole : digammaPosHalfLeft_pole_series_target β α)
    (h_right_pole : digammaPosHalfRight_pole_series_target β α) :
    shiftedArchIntegral β α =
      -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
        constantLogPiShiftedArchIntegral β α +
      (∑' k : ℕ, digammaPoleKernelLeft k β α) +
      (∑' k : ℕ, digammaPoleKernelRight k β α) +
      digammaRationalCorrectionIntegral β α := by
  rw [shiftedArchIntegral_two_piece_decomposition_unconditional β α]
  rw [digammaSumShiftedArchIntegral_eq_constant_plus_poles_plus_rational β α
        h_left_int h_right_int h_rat_int h_left_pole h_right_pole]
  ring

#print axioms shiftedArchIntegral_first_closed_arch_shape

/-! ## Step 11: `shiftedArchClosedForm` — derived expression as a named target

**Closed shape exposed ≠ shiftedArchIntegral equals it.**  The first closed
arch shape (Step 10) is the *form* the arch integral must take if all five
analytic gates discharge.  Name this derived expression separately from
`archRequired` so the comparison `shiftedArchClosedForm = archRequired` is
performed downstream as its own audit, not conflated with the shape derivation.

This step:
1. Defines `shiftedArchClosedForm β α` as the derived expression literally.
2. Restates Step 10's first closed arch shape as
   `shiftedArchIntegral β α = shiftedArchClosedForm β α`,
   conditional on the five gates.

The equality `shiftedArchClosedForm β α = archRequired t β` (for the relevant
`t`-instantiation pattern in the K_2 engineering identity) is the **audit
target**, NOT proved here.  Constants `log π + γ` must match the project's
arch normalization exactly. -/

/-- **Shifted-arch closed form** (derived expression).

```
shiftedArchClosedForm β α :=
  −(log π + γ) · 2π · e^α · test_β(e^{-α})
  + (Σ' k, digammaPoleKernelLeft k β α)
  + (Σ' k, digammaPoleKernelRight k β α)
  + digammaRationalCorrectionIntegral β α.
```

Four mechanisms exposed in auditable pieces:
- **Constant carrier**: `2π · e^α · test_β(e^{-α})` with coefficient `−(log π + γ)`.
- **Two trivial-zero pole towers**: distinct denominator conventions
  (`k + 1/2 + iy/2` vs `k + 1 - iy/2`).
- **Rational recurrence residue**: `Q(β,α)` from the half-arg shift on
  the negative-real-part argument.
-/
noncomputable def shiftedArchClosedForm (β α : ℝ) : ℂ :=
  -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
    constantLogPiShiftedArchIntegral β α +
  (∑' k : ℕ, digammaPoleKernelLeft k β α) +
  (∑' k : ℕ, digammaPoleKernelRight k β α) +
  digammaRationalCorrectionIntegral β α

/-- **`shiftedArchIntegral β α = shiftedArchClosedForm β α`** (conditional on
the five analytic gates).

Five gates:
1. `Integrable (exp · ψ(1/2 + iy/2) · M)` (left ψ-piece).
2. `Integrable (exp · ψ((2-iy)/2) · M)` (right ψ-piece).
3. `Integrable (exp · (1/(-1+iy)) · M)` (rational correction).
4. `digammaPosHalfLeft_pole_series_target β α` (left pole-series swap).
5. `digammaPosHalfRight_pole_series_target β α` (right pole-series swap).

Once these discharge, this theorem makes the closed shape literally equal
the arch integral.  The downstream audit `shiftedArchClosedForm = archRequired`
is then a pure comparison, not entangled with shape derivation. -/
theorem shiftedArchIntegral_eq_shiftedArchClosedForm
    (β α : ℝ)
    (h_left_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_right_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_rat_int : Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    (h_left_pole : digammaPosHalfLeft_pole_series_target β α)
    (h_right_pole : digammaPosHalfRight_pole_series_target β α) :
    shiftedArchIntegral β α = shiftedArchClosedForm β α := by
  unfold shiftedArchClosedForm
  exact shiftedArchIntegral_first_closed_arch_shape β α
    h_left_int h_right_int h_rat_int h_left_pole h_right_pole

#print axioms shiftedArchIntegral_eq_shiftedArchClosedForm

/-! ## Step 12: Discharge the rational integrability gate (gate 3)

`Integrable (fun y => exp(iyα) · (1/(-1+iy)) · M(β,-1+iy))`.

Strategy: `‖1/(-1+iy)‖ ≤ 1` since `|-1+iy| = √(1+y²) ≥ 1`. Combined with
`|exp(iyα)| = 1`, the product `exp · (1/(-1+iy))` is bounded by 1 in norm.
Multiplying by integrable `M(β,-1+iy)` (from
`pairTestMellin_vertical_integrable_at_neg_one`) gives integrability via
`Integrable.bdd_mul`. -/

/-- Norm bound: `‖1/(-1+iy)‖ ≤ 1` for all `y : ℝ`. -/
private lemma norm_one_div_neg_one_plus_iy_le_one (y : ℝ) :
    ‖(1 : ℂ) / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)‖ ≤ 1 := by
  have h_norm_sq : ‖((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)‖^2 = 1 + y^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, sq]
  have h_norm_ge : (1 : ℝ) ≤ ‖((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)‖ := by
    nlinarith [h_norm_sq, sq_nonneg y, norm_nonneg
      ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I),
      sq_nonneg (‖((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)‖ - 1)]
  rw [norm_div, norm_one]
  rw [div_le_one (by linarith)]
  exact h_norm_ge

/-- Norm bound: `‖exp(iyα) · (1/(-1+iy))‖ ≤ 1`. -/
private lemma norm_exp_iyα_times_reciprocal_le_one (α y : ℝ) :
    ‖Complex.exp (((y * α : ℝ) : ℂ) * I) *
      (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))‖ ≤ 1 := by
  rw [norm_mul]
  have h1 := norm_exp_iyα_le_one α y
  have h2 := norm_one_div_neg_one_plus_iy_le_one y
  have h_nn1 : 0 ≤ ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ := norm_nonneg _
  nlinarith [h1, h2, h_nn1, norm_nonneg ((1 : ℂ) /
    ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))]

/-- AE strong measurability of `y ↦ exp(iyα) · (1/(-1+iy))` (continuous). -/
private lemma exp_iyα_times_reciprocal_aestronglyMeasurable (α : ℝ) :
    AEStronglyMeasurable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) MeasureTheory.volume := by
  refine (Continuous.aestronglyMeasurable ?_)
  refine Continuous.mul ?_ ?_
  · -- `exp(iyα)` continuous in y.
    exact (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)
       |>.mul continuous_const))
  · -- `1 / (-1 + y*I)` continuous in y (denominator never zero).
    apply Continuous.div continuous_const
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    · intro y heq
      have hre := congr_arg Complex.re heq
      simp at hre

/-- **Gate 3 — rational integrability gate (unconditional).**
```
Integrable (fun y => exp(iyα) · (1/(-1+iy)) · M(β,-1+iy)).
```
Discharged via `Integrable.bdd_mul` on `pairTestMellin_vertical_integrable_at_neg_one`. -/
theorem rationalCorrectionIntegrand_integrable (β α : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h_M : Integrable (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := LeftEdgePrimeSum.pairTestMellin_vertical_integrable_at_neg_one β
    convert h using 1
  exact h_M.bdd_mul (exp_iyα_times_reciprocal_aestronglyMeasurable α)
    (Filter.Eventually.of_forall (norm_exp_iyα_times_reciprocal_le_one α))

#print axioms rationalCorrectionIntegrand_integrable

/-! ## Step 13: Discharge the two ψ-integrability gates (gates 1 and 2)

`Integrable (fun y => exp(iyα) · ψ(σ + cyI) · M(β,-1+iy))` for the two
positive-real-part shifts arising from the Step 8 recurrence rewrite.

Strategy (uniform across both σ, c choices):
* `‖exp(iyα)‖ = 1`.
* `‖ψ(σ + cyI)‖ ≤ C·(1 + log(1+|cy|))` from
  `Contour.digamma_log_bound_all_t σ hσ` (valid for `σ > 0`, all real shifts).
* `‖M(β,-1+iy)‖ ≤ K/(1+y²)` from `pairTestMellin_left_edge_global_quadratic_bound`.
* Tame the logarithm with `Real.log_le_rpow_div` at exponent `1/4`:
  `1 + log(1+|cy|) ≤ 5·(1+|cy|)^{1/4}`.
* Split: `(1+|cy|)^{1/4} ≤ (1+|c|)^{1/4}·(1+|y|)^{1/4}` and
  `(1+|y|)^{1/4} ≤ 2^{1/8}·(1+y²)^{1/8}`.
* Net dominator: `M·(1+y²)^{-7/8} = M·(1+‖y‖²)^{-7/4 / 2}` integrable on ℝ
  via `integrable_rpow_neg_one_add_norm_sq` (since `finrank ℝ ℝ = 1 < 7/4`).

The two specific gates are then instantiations with `(σ, c) = (1/2, 1/2)` and
`(σ, c) = (1, -1/2)` respectively, plus a complex-arithmetic rewrite to align
canonical forms `(2 - yI)/2 = 1 + (-y/2)·I`. -/

/-- Continuity of `y ↦ ψ(σ + (c·y)·I)` for `σ > 0` (no pole avoidance issues
in the right half-plane). -/
private lemma digamma_shifted_continuous (σ c : ℝ) (hσ_pos : 0 < σ) :
    Continuous (fun y : ℝ =>
      Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)) := by
  have h_ne_zero : ∀ y : ℝ,
      Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) ≠ 0 := by
    intro y
    apply Complex.Gamma_ne_zero
    intro m heq
    have h_re : ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I).re = -(m : ℝ) := by
      rw [heq]; simp
    simp at h_re
    linarith [Nat.cast_nonneg m (α := ℝ)]
  have h_s_cont : Continuous (fun y : ℝ => ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)) := by
    refine continuous_const.add ?_
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp ((continuous_const).mul continuous_id)
  have h_Γ_diffOn : DifferentiableOn ℂ Complex.Gamma
      {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
    intro z hz
    exact (Complex.differentiableAt_Gamma _ hz).differentiableWithinAt
  have h_U_open : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := Contour.nonpole_isOpen
  have h_eq : ∀ y : ℝ, Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) =
      deriv Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) /
        Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) := by
    intro y; rw [Complex.digamma_def, logDeriv_apply]
  have h_derivΓ_cont : Continuous (fun y : ℝ =>
      deriv Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)) := by
    have h_derivΓ_diffOn : DifferentiableOn ℂ (deriv Complex.Gamma)
        {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := h_Γ_diffOn.deriv h_U_open
    have : Continuous ((deriv Complex.Gamma) ∘
        (fun y : ℝ => ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))) := by
      apply ContinuousOn.comp_continuous (h_derivΓ_diffOn.continuousOn) h_s_cont
      intro y m heq
      have h_re : ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I).re = -(m : ℝ) := by
        rw [heq]; simp
      simp at h_re
      linarith [Nat.cast_nonneg m (α := ℝ)]
    exact this
  have h_Γ_cont : Continuous (fun y : ℝ =>
      Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)) := by
    have : Continuous (Complex.Gamma ∘
        (fun y : ℝ => ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))) := by
      apply ContinuousOn.comp_continuous (h_Γ_diffOn.continuousOn) h_s_cont
      intro y m heq
      have h_re : ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I).re = -(m : ℝ) := by
        rw [heq]; simp
      simp at h_re
      linarith [Nat.cast_nonneg m (α := ℝ)]
    exact this
  exact (h_derivΓ_cont.div h_Γ_cont (fun y => h_ne_zero y)).congr (fun y => (h_eq y).symm)

/-- **Generic ψ-shifted integrability lemma.** For `σ > 0` and any real `c, α`,
`y ↦ exp(iyα) · ψ(σ + (c·y)·I) · M(β, -1+iy)` is integrable on ℝ.

Dominator: `M·(1+‖y‖²)^{-7/4 / 2}` from
`integrable_rpow_neg_one_add_norm_sq`, with the logarithmic factor of `ψ`
absorbed by `(1+|cy|)^{1/4}` via `Real.log_le_rpow_div`. -/
private theorem integrable_shifted_digamma_piece (β α : ℝ)
    (σ c : ℝ) (hσ_pos : 0 < σ) :
    Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)) := by
  obtain ⟨C, hC_nn, hC_bd⟩ := Contour.digamma_log_bound_all_t σ hσ_pos
  obtain ⟨K, hK_nn, hK_bd⟩ :=
    PairTestIdentity.pairTestMellin_left_edge_global_quadratic_bound β
  have h_psi_cont : Continuous (fun y : ℝ =>
      Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)) :=
    digamma_shifted_continuous σ c hσ_pos
  have h_exp_cont : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) :=
    Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
        |>.mul continuous_const)
  have h_M_cont : Continuous (fun y : ℝ =>
      Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)) :=
    PairTestIdentity.pairTestMellin_left_edge_continuous β
  have h_integrand_cont : Continuous (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)) :=
    (h_exp_cont.mul h_psi_cont).mul h_M_cont
  set M : ℝ := 5 * C * K * ((1 + |c|)^((1:ℝ)/4)) * (2^((1:ℝ)/8)) with hM_def
  have h_bound : ∀ y : ℝ,
      ‖Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)‖ ≤
      M * (1 + ‖y‖^2)^(-((7:ℝ)/4)/2) := by
    intro y
    rw [norm_mul, norm_mul]
    have h_exp_norm : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      have h_im : (((y * α : ℝ) : ℂ) * I).re = 0 := by simp
      rw [Complex.norm_exp, h_im, Real.exp_zero]
    rw [h_exp_norm, one_mul]
    have h_psi_norm : ‖Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)‖ ≤
        C * (1 + Real.log (1 + |c * y|)) := by
      have h_eq : Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) =
          deriv Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) /
            Complex.Gamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) := by
        rw [Complex.digamma_def, logDeriv_apply]
      rw [h_eq]; exact hC_bd (c * y)
    have h_M_norm := hK_bd y
    have h_log_nn : 0 ≤ Real.log (1 + |c * y|) :=
      Real.log_nonneg (by linarith [abs_nonneg (c*y)])
    have h_factor1_nn : 0 ≤ C * (1 + Real.log (1 + |c * y|)) := by positivity
    have h_M_nn : 0 ≤ ‖Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)‖ :=
      norm_nonneg _
    have h_product : ‖Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)‖ *
        ‖Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)‖ ≤
        (C * (1 + Real.log (1 + |c * y|))) * (K * (1 + y^2)⁻¹) :=
      mul_le_mul h_psi_norm h_M_norm h_M_nn h_factor1_nn
    -- log dominator: 1 + log(1+|cy|) ≤ 5·(1+|cy|)^{1/4}
    have h_log_bd : 1 + Real.log (1 + |c * y|) ≤ 5 * (1 + |c * y|)^((1:ℝ)/4) := by
      have h_nn : (0:ℝ) ≤ 1 + |c * y| := by linarith [abs_nonneg (c*y)]
      have h_ge_one : (1:ℝ) ≤ 1 + |c * y| := by linarith [abs_nonneg (c*y)]
      have h_eps_pos : (0:ℝ) < (1:ℝ)/4 := by norm_num
      have h_log_le : Real.log (1 + |c * y|) ≤ (1 + |c * y|) ^ ((1:ℝ)/4) / ((1:ℝ)/4) :=
        Real.log_le_rpow_div h_nn h_eps_pos
      have h_div : (1 + |c * y|) ^ ((1:ℝ)/4) / ((1:ℝ)/4) =
          4 * (1 + |c * y|) ^ ((1:ℝ)/4) := by field_simp
      rw [h_div] at h_log_le
      have h_rpow_ge_one : (1:ℝ) ≤ (1 + |c * y|) ^ ((1:ℝ)/4) := by
        have h1 : (1:ℝ)^((1:ℝ)/4) = 1 := Real.one_rpow _
        have h2 : (1:ℝ)^((1:ℝ)/4) ≤ (1 + |c * y|)^((1:ℝ)/4) :=
          Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h_ge_one (by norm_num : (0:ℝ) ≤ 1/4)
        linarith
      linarith
    -- (1+|cy|)^{1/4} ≤ (1+|c|)^{1/4} · (1+|y|)^{1/4}
    have h_split_cy : (1 + |c * y|)^((1:ℝ)/4) ≤
        (1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4) := by
      have h_step : 1 + |c * y| ≤ (1 + |c|) * (1 + |y|) := by
        rw [abs_mul]; nlinarith [abs_nonneg c, abs_nonneg y]
      have h1_nn : (0:ℝ) ≤ 1 + |c * y| := by linarith [abs_nonneg (c*y)]
      have h_eps_nn : (0:ℝ) ≤ (1:ℝ)/4 := by norm_num
      have h_rpow_step : (1 + |c * y|) ^ ((1:ℝ)/4) ≤ ((1 + |c|) * (1 + |y|))^((1:ℝ)/4) :=
        Real.rpow_le_rpow h1_nn h_step h_eps_nn
      have h_split : ((1 + |c|) * (1 + |y|))^((1:ℝ)/4) =
          (1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4) :=
        Real.mul_rpow (by linarith [abs_nonneg c]) (by linarith [abs_nonneg y])
      linarith
    -- (1+|y|)^{1/4} ≤ 2^{1/8} · (1+y²)^{1/8}
    have h_y_to_sq : (1 + |y|)^((1:ℝ)/4) ≤ 2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8) := by
      have h_sq : (1 + |y|)^2 ≤ 2 * (1 + y^2) := by
        have h : |y|^2 = y^2 := sq_abs y
        nlinarith [sq_nonneg (|y| - 1), abs_nonneg y, h]
      have h1_nn : (0:ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
      have h_step1 : ((1 + |y|)^2)^((1:ℝ)/8) ≤ (2 * (1 + y^2))^((1:ℝ)/8) :=
        Real.rpow_le_rpow (by positivity) h_sq (by norm_num)
      have h_lhs : ((1 + |y|)^2)^((1:ℝ)/8) = (1 + |y|)^((1:ℝ)/4) := by
        rw [show ((1 + |y|)^2) = (1 + |y|)^(2:ℕ) from rfl]
        rw [← Real.rpow_natCast (1 + |y|) 2]
        rw [← Real.rpow_mul h1_nn]
        norm_num
      have h_rhs : (2 * (1 + y^2))^((1:ℝ)/8) = 2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8) :=
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 1 + y^2)
      linarith [h_step1, h_lhs.le, h_lhs.ge, h_rhs.le, h_rhs.ge]
    -- (1+y²)^{1/8} · (1+y²)⁻¹ = (1+‖y‖²)^{(-7/4)/2}
    have h_rpow_simplify : (1 + y^2)^((1:ℝ)/8) * (1 + y^2)⁻¹ =
        (1 + ‖y‖^2)^(-((7:ℝ)/4)/2) := by
      rw [Real.norm_eq_abs, sq_abs]
      have h_pos : (0:ℝ) < 1 + y^2 := by positivity
      rw [show ((1+y^2 : ℝ)⁻¹) = (1+y^2)^(-(1:ℝ)) by rw [Real.rpow_neg_one]]
      rw [← Real.rpow_add h_pos]
      congr 1; norm_num
    have h_c_pow_nn : 0 ≤ (1 + |c|)^((1:ℝ)/4) := by
      apply Real.rpow_nonneg; linarith [abs_nonneg c]
    -- Step a: replace log factor with rpow.
    have h_a : C * (1 + Real.log (1 + |c * y|)) * (K * (1 + y^2)⁻¹) ≤
        C * (5 * (1 + |c * y|)^((1:ℝ)/4)) * (K * (1 + y^2)⁻¹) := by
      have h_inner : C * (1 + Real.log (1 + |c * y|)) ≤
          C * (5 * (1 + |c * y|)^((1:ℝ)/4)) :=
        mul_le_mul_of_nonneg_left h_log_bd hC_nn
      exact mul_le_mul_of_nonneg_right h_inner (by positivity)
    -- Step b: split |cy| factor.
    have h_b : C * (5 * (1 + |c * y|)^((1:ℝ)/4)) * (K * (1 + y^2)⁻¹) ≤
        C * (5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4))) * (K * (1 + y^2)⁻¹) := by
      have h_inner : 5 * (1 + |c * y|)^((1:ℝ)/4) ≤
          5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4)) :=
        mul_le_mul_of_nonneg_left h_split_cy (by norm_num)
      have h_inner2 : C * (5 * (1 + |c * y|)^((1:ℝ)/4)) ≤
          C * (5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4))) :=
        mul_le_mul_of_nonneg_left h_inner hC_nn
      exact mul_le_mul_of_nonneg_right h_inner2 (by positivity)
    -- Step c: rpow on (1+|y|).
    have h_c : C * (5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4))) *
        (K * (1 + y^2)⁻¹) ≤
        C * (5 * ((1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8)))) *
          (K * (1 + y^2)⁻¹) := by
      have h_inner : (1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4) ≤
          (1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8)) :=
        mul_le_mul_of_nonneg_left h_y_to_sq h_c_pow_nn
      have h_5 : 5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4)) ≤
          5 * ((1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8))) :=
        mul_le_mul_of_nonneg_left h_inner (by norm_num)
      have h_C : C * (5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4))) ≤
          C * (5 * ((1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8)))) :=
        mul_le_mul_of_nonneg_left h_5 hC_nn
      exact mul_le_mul_of_nonneg_right h_C (by positivity)
    -- Step d: rearrange to M · (rpow factor).
    have h_d : C * (5 * ((1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8)))) *
        (K * (1 + y^2)⁻¹) =
        M * ((1 + y^2)^((1:ℝ)/8) * (1 + y^2)⁻¹) := by
      simp [hM_def]; ring
    calc ‖Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)‖ *
          ‖Contour.pairTestMellin β ((((-1):ℝ):ℂ) + (y:ℂ)*I)‖
        ≤ C * (1 + Real.log (1 + |c * y|)) * (K * (1 + y^2)⁻¹) := h_product
      _ ≤ C * (5 * (1 + |c * y|)^((1:ℝ)/4)) * (K * (1 + y^2)⁻¹) := h_a
      _ ≤ C * (5 * ((1 + |c|)^((1:ℝ)/4) * (1 + |y|)^((1:ℝ)/4))) * (K * (1 + y^2)⁻¹) := h_b
      _ ≤ C * (5 * ((1 + |c|)^((1:ℝ)/4) * (2^((1:ℝ)/8) * (1 + y^2)^((1:ℝ)/8)))) *
            (K * (1 + y^2)⁻¹) := h_c
      _ = M * ((1 + y^2)^((1:ℝ)/8) * (1 + y^2)⁻¹) := h_d
      _ = M * (1 + ‖y‖^2)^(-((7:ℝ)/4)/2) := by rw [h_rpow_simplify]
  have h_dominator_int : Integrable (fun y : ℝ =>
      M * (1 + ‖y‖^2)^(-((7:ℝ)/4)/2)) := by
    apply Integrable.const_mul
    apply integrable_rpow_neg_one_add_norm_sq
    show (Module.finrank ℝ ℝ : ℝ) < 7/4
    rw [Module.finrank_self]; norm_num
  exact h_dominator_int.mono' h_integrand_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall h_bound)

#print axioms integrable_shifted_digamma_piece

/-- **Gate 1 — left ψ-shifted integrability gate (unconditional).**
```
Integrable (fun y => exp(iyα) · ψ(1/2 + iy/2) · M(β,-1+iy)).
```
Instantiation of `integrable_shifted_digamma_piece` at `(σ, c) = (1/2, 1/2)`. -/
theorem digammaPosHalfShiftedArchIntegrand_left_integrable (β α : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h := integrable_shifted_digamma_piece β α (1/2) (1/2) (by norm_num : (0:ℝ) < 1/2)
  convert h using 2 with y
  congr 1
  · congr 1
    rw [show ((y / 2 : ℝ) : ℂ) = ((1/2 * y : ℝ) : ℂ) by push_cast; ring]

#print axioms digammaPosHalfShiftedArchIntegrand_left_integrable

/-- **Gate 2 — right ψ-shifted integrability gate (unconditional).**
```
Integrable (fun y => exp(iyα) · ψ((2-iy)/2) · M(β,-1+iy)).
```
Instantiation of `integrable_shifted_digamma_piece` at `(σ, c) = (1, -1/2)`,
using `(2 - yI)/2 = 1 + (-y/2)·I` to align canonical forms. -/
theorem digammaPosHalfShiftedArchIntegrand_right_integrable (β α : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have h := integrable_shifted_digamma_piece β α 1 (-1/2) (by norm_num : (0:ℝ) < 1)
  convert h using 2 with y
  congr 1
  · congr 1
    rw [show ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2 : ℂ) =
        ((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I by push_cast; ring]

#print axioms digammaPosHalfShiftedArchIntegrand_right_integrable

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
