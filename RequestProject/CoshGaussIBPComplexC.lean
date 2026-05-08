import Mathlib
import RequestProject.WeilPairIBP
import RequestProject.WeilPairIBPQuartic
import RequestProject.PairTestMellinAnalytic

/-!
# Complex-`c` IBP×4 chain for `cosh(c·t)·exp(−2t²)`

This file extends the real-`c` IBP×4 machinery (in `WeilPairIBP.lean`,
`WeilPairIBPQuartic.lean`) to **complex** `c`.  The mathematical content
is identical: `Complex.cosh` and `Complex.sinh` satisfy the same
derivative recurrence `cosh' = sinh, sinh' = cosh`, so the explicit
polynomial-in-`(c, t)` formulas for the iterated `t`-derivatives lift
verbatim with `Complex.cosh, Complex.sinh` replacing `Real.cosh, Real.sinh`.

## Key exports

* `coshGaussValC c t := Complex.cosh (c·t) · exp(−2t²)` — base.
* `coshGaussDerivValC, coshGaussDeriv2ValC, coshGaussDeriv3ValC, coshGaussDeriv4ValC`
  — iterated `t`-derivatives, complex-c versions.
* `coshGaussC_hasDerivAt_iter{1..4}` — chain of `HasDerivAt` proofs.
* `coshGaussDerivValC_ofReal_eq` etc. — agreement with real-c versions.

The main downstream consumer: the **Field-3 Weierstrass step** in the
K-route admissibility chain, via `coshGaussMellinC_ibp_four_times` and
the resulting complex-strip uniform quartic-decay bound.

Axiom footprint of all proved theorems: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1200000

open Complex Real Set MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-! ## §1 — Chain rule helpers for `Complex.cosh, Complex.sinh` of real argument -/

/-- **`HasDerivAt` for `t ↦ Complex.cosh(c·(t:ℂ))`** (real `t`).  Derivative
is `c · Complex.sinh(c·t)`.  Proved via `Complex.cosh = (exp + exp(-·))/2`
and `HasDerivAt.cexp`. -/
lemma hasDerivAt_complex_cosh_real (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.cosh (c * (t : ℂ)))
      (c * Complex.sinh (c * (t : ℂ))) t := by
  have h_inner : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c t := by
    have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c; simpa using this
  have h_inner_neg : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := h_inner.neg
  have h_exp_pos := h_inner.cexp
  have h_exp_neg := h_inner_neg.cexp
  have h_sum : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) + Complex.exp (-(c * (t : ℂ))))
      (Complex.exp (c * (t : ℂ)) * c + Complex.exp (-(c * (t : ℂ))) * (-c)) t :=
    h_exp_pos.add h_exp_neg
  have h_div : HasDerivAt (fun t : ℝ => (Complex.exp (c * (t : ℂ)) + Complex.exp (-(c * (t : ℂ)))) / 2)
      ((Complex.exp (c * (t : ℂ)) * c + Complex.exp (-(c * (t : ℂ))) * (-c)) / 2) t :=
    h_sum.div_const 2
  have h_eq_fn : (fun t : ℝ => (Complex.exp (c * (t : ℂ)) + Complex.exp (-(c * (t : ℂ)))) / 2) =
      fun t : ℝ => Complex.cosh (c * (t : ℂ)) := by
    funext s; rw [Complex.cosh]
  rw [← h_eq_fn]
  convert h_div using 1
  rw [Complex.sinh]; ring

/-- **`HasDerivAt` for `t ↦ Complex.sinh(c·(t:ℂ))`**.  Derivative is
`c · Complex.cosh(c·t)`. -/
lemma hasDerivAt_complex_sinh_real (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.sinh (c * (t : ℂ)))
      (c * Complex.cosh (c * (t : ℂ))) t := by
  have h_inner : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c t := by
    have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c; simpa using this
  have h_inner_neg : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := h_inner.neg
  have h_exp_pos := h_inner.cexp
  have h_exp_neg := h_inner_neg.cexp
  have h_sub : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) - Complex.exp (-(c * (t : ℂ))))
      (Complex.exp (c * (t : ℂ)) * c - Complex.exp (-(c * (t : ℂ))) * (-c)) t :=
    h_exp_pos.sub h_exp_neg
  have h_div : HasDerivAt (fun t : ℝ => (Complex.exp (c * (t : ℂ)) - Complex.exp (-(c * (t : ℂ)))) / 2)
      ((Complex.exp (c * (t : ℂ)) * c - Complex.exp (-(c * (t : ℂ))) * (-c)) / 2) t :=
    h_sub.div_const 2
  have h_eq_fn : (fun t : ℝ => (Complex.exp (c * (t : ℂ)) - Complex.exp (-(c * (t : ℂ)))) / 2) =
      fun t : ℝ => Complex.sinh (c * (t : ℂ)) := by
    funext s; rw [Complex.sinh]
  rw [← h_eq_fn]
  convert h_div using 1
  rw [Complex.cosh]; ring

/-! ## §2 — Iterated derivatives of `Complex.cosh(c·t)·exp(−2t²)` (complex `c`) -/

/-- **Base value:** `cosh(c·t)·exp(−2t²)`. -/
noncomputable def coshGaussValC (c : ℂ) (t : ℝ) : ℂ :=
  Complex.cosh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)

/-- **1st derivative (complex c):**
`(c·sinh(c·t) − 4t·cosh(c·t))·exp(−2t²)`. -/
noncomputable def coshGaussDerivValC (c : ℂ) (t : ℝ) : ℂ :=
  (c * Complex.sinh (c * (t : ℂ)) - 4 * (t : ℂ) * Complex.cosh (c * (t : ℂ))) *
    ((Real.exp (-2 * t^2) : ℝ) : ℂ)

/-- **2nd derivative (complex c):**
`((c² − 4 + 16t²)·cosh(c·t) − 8c·t·sinh(c·t))·exp(−2t²)`. -/
noncomputable def coshGaussDeriv2ValC (c : ℂ) (t : ℝ) : ℂ :=
  ((c^2 - 4 + 16 * (t : ℂ)^2) * Complex.cosh (c * (t : ℂ)) -
   8 * c * (t : ℂ) * Complex.sinh (c * (t : ℂ))) *
    ((Real.exp (-2 * t^2) : ℝ) : ℂ)

/-- **3rd derivative (complex c):**
`((48t − 12tc² − 64t³)·cosh(c·t) + (c³ − 12c + 48t²c)·sinh(c·t))·exp(−2t²)`. -/
noncomputable def coshGaussDeriv3ValC (c : ℂ) (t : ℝ) : ℂ :=
  ((48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) * Complex.cosh (c * (t : ℂ)) +
    (c^3 - 12 * c + 48 * (t : ℂ)^2 * c) * Complex.sinh (c * (t : ℂ))) *
    ((Real.exp (-2 * t^2) : ℝ) : ℂ)

/-- **4th derivative (complex c):**
`((256t⁴ − 384t² + 96c²t² + c⁴ − 24c² + 48)·cosh(c·t) + (192ct − 16c³t − 256ct³)·sinh(c·t))·exp(−2t²)`. -/
noncomputable def coshGaussDeriv4ValC (c : ℂ) (t : ℝ) : ℂ :=
  ((256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4 - 24 * c^2 + 48) *
      Complex.cosh (c * (t : ℂ)) +
    (192 * c * (t : ℂ) - 16 * c^3 * (t : ℂ) - 256 * c * (t : ℂ)^3) *
      Complex.sinh (c * (t : ℂ))) *
    ((Real.exp (-2 * t^2) : ℝ) : ℂ)

/-! ## §3 — Agreement with real-`c` versions on `(c : ℝ)` -/

private lemma ofReal_complex_cosh (c : ℝ) (t : ℝ) :
    Complex.cosh (((c : ℂ)) * (t : ℂ)) = ((Real.cosh (c * t) : ℝ) : ℂ) := by
  rw [show ((c : ℂ) * (t : ℂ)) = ((c * t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cosh]

private lemma ofReal_complex_sinh (c : ℝ) (t : ℝ) :
    Complex.sinh (((c : ℂ)) * (t : ℂ)) = ((Real.sinh (c * t) : ℝ) : ℂ) := by
  rw [show ((c : ℂ) * (t : ℂ)) = ((c * t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sinh]

theorem coshGaussValC_ofReal_eq (c : ℝ) (t : ℝ) :
    coshGaussValC ((c : ℂ)) t = ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) := by
  unfold coshGaussValC
  rw [ofReal_complex_cosh]
  push_cast; ring

theorem coshGaussDerivValC_ofReal_eq (c : ℝ) (t : ℝ) :
    coshGaussDerivValC ((c : ℂ)) t = ((coshGaussDerivVal c t : ℝ) : ℂ) := by
  unfold coshGaussDerivValC coshGaussDerivVal
  rw [ofReal_complex_sinh, ofReal_complex_cosh]
  push_cast; ring

theorem coshGaussDeriv2ValC_ofReal_eq (c : ℝ) (t : ℝ) :
    coshGaussDeriv2ValC ((c : ℂ)) t = ((coshGaussDeriv2Val c t : ℝ) : ℂ) := by
  unfold coshGaussDeriv2ValC coshGaussDeriv2Val
  rw [ofReal_complex_sinh, ofReal_complex_cosh]
  push_cast; ring

theorem coshGaussDeriv3ValC_ofReal_eq (c : ℝ) (t : ℝ) :
    coshGaussDeriv3ValC ((c : ℂ)) t = ((coshGaussDeriv3Val c t : ℝ) : ℂ) := by
  unfold coshGaussDeriv3ValC coshGaussDeriv3Val
  rw [ofReal_complex_sinh, ofReal_complex_cosh]
  push_cast; ring

theorem coshGaussDeriv4ValC_ofReal_eq (c : ℝ) (t : ℝ) :
    coshGaussDeriv4ValC ((c : ℂ)) t = ((coshGaussDeriv4Val c t : ℝ) : ℂ) := by
  unfold coshGaussDeriv4ValC coshGaussDeriv4Val
  rw [ofReal_complex_sinh, ofReal_complex_cosh]
  push_cast; ring

/-! ## §4 — Iterated `HasDerivAt` chain (complex c) -/

/-- Helper: derivative of `(t:ℂ) ↦ ((Real.exp (-2t²) : ℝ) : ℂ)`. -/
private lemma hasDerivAt_exp_neg_two_sq_C (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      (((Real.exp (-2 * t^2) * (-2 * (2 * t)) : ℝ) : ℂ)) t := by
  have h_arg : HasDerivAt (fun t : ℝ => -2 * t^2) (-2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-2 : ℝ)
    simpa [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm, mul_assoc] using this
  exact (h_arg.exp).ofReal_comp

/-- Helper: derivative of `(t:ℝ) ↦ (t:ℂ)`. -/
private lemma hasDerivAt_t_to_C (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t :=
  Complex.ofRealCLM.hasDerivAt

/-- **iter1: `HasDerivAt (coshGaussValC c) (coshGaussDerivValC c t) t`**. -/
theorem coshGaussC_hasDerivAt_iter1 (c : ℂ) (t : ℝ) :
    HasDerivAt (coshGaussValC c) (coshGaussDerivValC c t) t := by
  unfold coshGaussValC coshGaussDerivValC
  have h_cosh := hasDerivAt_complex_cosh_real c t
  have h_exp_C := hasDerivAt_exp_neg_two_sq_C t
  have h_prod := h_cosh.mul h_exp_C
  convert h_prod using 1
  push_cast
  ring

/-- **iter2: `HasDerivAt (coshGaussDerivValC c) (coshGaussDeriv2ValC c t) t`**. -/
theorem coshGaussC_hasDerivAt_iter2 (c : ℂ) (t : ℝ) :
    HasDerivAt (coshGaussDerivValC c) (coshGaussDeriv2ValC c t) t := by
  unfold coshGaussDerivValC coshGaussDeriv2ValC
  have h_cosh := hasDerivAt_complex_cosh_real c t
  have h_sinh := hasDerivAt_complex_sinh_real c t
  have h_t : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := hasDerivAt_t_to_C t
  -- c * sinh(c·t) — derivative is c · (c · cosh(c·t)) = c² · cosh(c·t).
  have h_c_sinh : HasDerivAt (fun t : ℝ => c * Complex.sinh (c * (t : ℂ)))
      (c * (c * Complex.cosh (c * (t : ℂ)))) t :=
    h_sinh.const_mul c
  -- 4·(t:ℂ)·cosh(c·t) — product rule.
  have h_4t : HasDerivAt (fun t : ℝ => 4 * (t : ℂ)) 4 t := by
    have := h_t.const_mul (4 : ℂ); simpa using this
  have h_4t_cosh : HasDerivAt (fun t : ℝ => 4 * (t : ℂ) * Complex.cosh (c * (t : ℂ)))
      (4 * Complex.cosh (c * (t : ℂ)) +
       4 * (t : ℂ) * (c * Complex.sinh (c * (t : ℂ)))) t :=
    h_4t.mul h_cosh
  -- Difference.
  have h_u : HasDerivAt
      (fun t : ℝ => c * Complex.sinh (c * (t : ℂ)) - 4 * (t : ℂ) * Complex.cosh (c * (t : ℂ)))
      (c * (c * Complex.cosh (c * (t : ℂ))) -
       (4 * Complex.cosh (c * (t : ℂ)) +
        4 * (t : ℂ) * (c * Complex.sinh (c * (t : ℂ))))) t :=
    h_c_sinh.sub h_4t_cosh
  -- Multiply by exp factor.
  have h_exp_C := hasDerivAt_exp_neg_two_sq_C t
  have h_prod := h_u.mul h_exp_C
  convert h_prod using 1
  push_cast
  ring

/-- **iter3: `HasDerivAt (coshGaussDeriv2ValC c) (coshGaussDeriv3ValC c t) t`**. -/
theorem coshGaussC_hasDerivAt_iter3 (c : ℂ) (t : ℝ) :
    HasDerivAt (coshGaussDeriv2ValC c) (coshGaussDeriv3ValC c t) t := by
  unfold coshGaussDeriv2ValC coshGaussDeriv3ValC
  have h_cosh := hasDerivAt_complex_cosh_real c t
  have h_sinh := hasDerivAt_complex_sinh_real c t
  have h_t : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := hasDerivAt_t_to_C t
  -- A(t) := c² - 4 + 16·(t:ℂ)²
  have h_tsq : HasDerivAt (fun t : ℝ => (t : ℂ)^2) (2 * (t : ℂ)) t := by
    have := h_t.pow 2
    simpa [pow_succ, pow_zero, one_mul] using this
  have h_A : HasDerivAt (fun t : ℝ => c^2 - 4 + 16 * (t : ℂ)^2) (16 * (2 * (t : ℂ))) t := by
    have h1 : HasDerivAt (fun t : ℝ => 16 * (t : ℂ)^2) (16 * (2 * (t : ℂ))) t :=
      h_tsq.const_mul (16 : ℂ)
    have h_sum := (hasDerivAt_const t (c^2 - 4)).add h1
    convert h_sum using 1
    ring
  -- A · cosh(c·t)
  have h_A_cosh : HasDerivAt (fun t : ℝ => (c^2 - 4 + 16 * (t : ℂ)^2) * Complex.cosh (c * (t : ℂ)))
      ((16 * (2 * (t : ℂ))) * Complex.cosh (c * (t : ℂ)) +
       (c^2 - 4 + 16 * (t : ℂ)^2) * (c * Complex.sinh (c * (t : ℂ)))) t :=
    h_A.mul h_cosh
  -- B(t) := 8·c·(t:ℂ)
  have h_B : HasDerivAt (fun t : ℝ => 8 * c * (t : ℂ)) (8 * c) t := by
    have := h_t.const_mul (8 * c); simpa using this
  -- B · sinh(c·t)
  have h_B_sinh : HasDerivAt (fun t : ℝ => 8 * c * (t : ℂ) * Complex.sinh (c * (t : ℂ)))
      (8 * c * Complex.sinh (c * (t : ℂ)) +
       8 * c * (t : ℂ) * (c * Complex.cosh (c * (t : ℂ)))) t :=
    h_B.mul h_sinh
  have h_u : HasDerivAt
      (fun t : ℝ => (c^2 - 4 + 16 * (t : ℂ)^2) * Complex.cosh (c * (t : ℂ)) -
                    8 * c * (t : ℂ) * Complex.sinh (c * (t : ℂ)))
      ((16 * (2 * (t : ℂ))) * Complex.cosh (c * (t : ℂ)) +
       (c^2 - 4 + 16 * (t : ℂ)^2) * (c * Complex.sinh (c * (t : ℂ))) -
       (8 * c * Complex.sinh (c * (t : ℂ)) +
        8 * c * (t : ℂ) * (c * Complex.cosh (c * (t : ℂ))))) t :=
    h_A_cosh.sub h_B_sinh
  have h_exp_C := hasDerivAt_exp_neg_two_sq_C t
  have h_prod := h_u.mul h_exp_C
  convert h_prod using 1
  push_cast
  ring

/-- **iter4: `HasDerivAt (coshGaussDeriv3ValC c) (coshGaussDeriv4ValC c t) t`**. -/
theorem coshGaussC_hasDerivAt_iter4 (c : ℂ) (t : ℝ) :
    HasDerivAt (coshGaussDeriv3ValC c) (coshGaussDeriv4ValC c t) t := by
  unfold coshGaussDeriv3ValC coshGaussDeriv4ValC
  have h_cosh := hasDerivAt_complex_cosh_real c t
  have h_sinh := hasDerivAt_complex_sinh_real c t
  have h_t : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := hasDerivAt_t_to_C t
  have h_tsq : HasDerivAt (fun t : ℝ => (t : ℂ)^2) (2 * (t : ℂ)) t := by
    have := h_t.pow 2
    simpa [pow_succ, pow_zero, one_mul] using this
  have h_tcb : HasDerivAt (fun t : ℝ => (t : ℂ)^3) (3 * (t : ℂ)^2) t := by
    have := h_t.pow 3
    simpa [pow_succ, pow_zero, one_mul] using this
  -- A(t) := 48·(t:ℂ) - 12·(t:ℂ)·c² - 64·(t:ℂ)³, derivative 48 - 12·c² - 192·(t:ℂ)²
  have h_A : HasDerivAt (fun t : ℝ => 48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3)
      (48 - 12 * c^2 - 192 * (t : ℂ)^2) t := by
    have h48 : HasDerivAt (fun t : ℝ => 48 * (t : ℂ)) 48 t := by
      have := h_t.const_mul (48 : ℂ); simpa using this
    have h12 : HasDerivAt (fun t : ℝ => 12 * (t : ℂ) * c^2) (12 * c^2) t := by
      have h_inner : HasDerivAt (fun t : ℝ => 12 * (t : ℂ)) 12 t := by
        have := h_t.const_mul (12 : ℂ); simpa using this
      have := h_inner.mul_const (c^2); simpa using this
    have h64 : HasDerivAt (fun t : ℝ => 64 * (t : ℂ)^3) (192 * (t : ℂ)^2) t := by
      have := h_tcb.const_mul (64 : ℂ)
      convert this using 1
      ring
    have h_sub := (h48.sub h12).sub h64
    convert h_sub using 1
  -- A · cosh(c·t)
  have h_A_cosh : HasDerivAt
      (fun t : ℝ => (48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) *
        Complex.cosh (c * (t : ℂ)))
      ((48 - 12 * c^2 - 192 * (t : ℂ)^2) * Complex.cosh (c * (t : ℂ)) +
       (48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) *
         (c * Complex.sinh (c * (t : ℂ)))) t :=
    h_A.mul h_cosh
  -- B(t) := c³ - 12·c + 48·(t:ℂ)²·c, derivative 96·(t:ℂ)·c (treating c as constant)
  have h_B : HasDerivAt (fun t : ℝ => c^3 - 12 * c + 48 * (t : ℂ)^2 * c)
      (96 * (t : ℂ) * c) t := by
    have h48 : HasDerivAt (fun t : ℝ => 48 * (t : ℂ)^2 * c) (48 * (2 * (t : ℂ)) * c) t := by
      have h_inner : HasDerivAt (fun t : ℝ => 48 * (t : ℂ)^2) (48 * (2 * (t : ℂ))) t :=
        h_tsq.const_mul (48 : ℂ)
      have := h_inner.mul_const c; simpa using this
    have h_sum := (hasDerivAt_const t (c^3 - 12 * c)).add h48
    convert h_sum using 1
    ring
  -- B · sinh(c·t)
  have h_B_sinh : HasDerivAt
      (fun t : ℝ => (c^3 - 12 * c + 48 * (t : ℂ)^2 * c) * Complex.sinh (c * (t : ℂ)))
      ((96 * (t : ℂ) * c) * Complex.sinh (c * (t : ℂ)) +
       (c^3 - 12 * c + 48 * (t : ℂ)^2 * c) * (c * Complex.cosh (c * (t : ℂ)))) t :=
    h_B.mul h_sinh
  have h_u : HasDerivAt
      (fun t : ℝ => (48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) *
                    Complex.cosh (c * (t : ℂ)) +
                    (c^3 - 12 * c + 48 * (t : ℂ)^2 * c) * Complex.sinh (c * (t : ℂ)))
      ((48 - 12 * c^2 - 192 * (t : ℂ)^2) * Complex.cosh (c * (t : ℂ)) +
       (48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) *
         (c * Complex.sinh (c * (t : ℂ))) +
       ((96 * (t : ℂ) * c) * Complex.sinh (c * (t : ℂ)) +
        (c^3 - 12 * c + 48 * (t : ℂ)^2 * c) * (c * Complex.cosh (c * (t : ℂ))))) t :=
    h_A_cosh.add h_B_sinh
  have h_exp_C := hasDerivAt_exp_neg_two_sq_C t
  have h_prod := h_u.mul h_exp_C
  convert h_prod using 1
  push_cast
  ring

/-! ## §5 — Pointwise norm bound on `coshGaussDeriv4ValC` -/

/-- **Pointwise norm bound on `coshGaussDeriv4ValC`** for complex `c` and real `t`.
Stated using `|t|^k` (rather than `t^k`) on the right to avoid the `t^k = |t|^k`
parity case-split for odd `k`. -/
theorem norm_coshGaussDeriv4ValC_le (c : ℂ) (t : ℝ) :
    ‖coshGaussDeriv4ValC c t‖ ≤
      (256 * |t|^4 + 384 * |t|^2 + 96 * ‖c‖^2 * |t|^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
        192 * ‖c‖ * |t| + 16 * ‖c‖^3 * |t| + 256 * ‖c‖ * |t|^3) *
       Real.exp (‖c‖ * |t|) * Real.exp (-2 * t^2) := by
  unfold coshGaussDeriv4ValC
  set EE := Real.exp (‖c‖ * |t|) with hEE
  have hEE_pos : 0 < EE := Real.exp_pos _
  have h_norm_t : ‖(t : ℂ)‖ = |t| := Complex.norm_real t
  have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * |t| := by rw [norm_mul, h_norm_t]
  have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ EE := by
    have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
  have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ EE := by
    have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
  -- Norm-power identities.
  have h_norm_pow : ∀ n : ℕ, ‖(t : ℂ)^n‖ = |t|^n := fun n => by
    rw [norm_pow, h_norm_t]
  have h_norm_pow_c : ∀ n : ℕ, ‖c^n‖ = ‖c‖^n := fun n => norm_pow _ _
  -- Numeric norms.
  have h256 : ‖(256 : ℂ)‖ = 256 := by norm_num
  have h384 : ‖(384 : ℂ)‖ = 384 := by norm_num
  have h96 : ‖(96 : ℂ)‖ = 96 := by norm_num
  have h24 : ‖(24 : ℂ)‖ = 24 := by norm_num
  have h48 : ‖(48 : ℂ)‖ = 48 := by norm_num
  have h192 : ‖(192 : ℂ)‖ = 192 := by norm_num
  have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real]; exact abs_of_pos (Real.exp_pos _)
  -- A := 256·t⁴ - 384·t² + 96·c²·t² + c⁴ - 24·c² + 48
  set A : ℂ := 256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 +
                c^4 - 24 * c^2 + 48 with hA_def
  -- B := 192·c·t - 16·c³·t - 256·c·t³
  set B : ℂ := 192 * c * (t : ℂ) - 16 * c^3 * (t : ℂ) - 256 * c * (t : ℂ)^3 with hB_def
  -- Bound ‖A‖.
  set PA : ℝ := 256 * |t|^4 + 384 * |t|^2 + 96 * ‖c‖^2 * |t|^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 with hPA_def
  have h_A : ‖A‖ ≤ PA := by
    have h_step1 : ‖A‖ ≤
        ‖(256 : ℂ) * (t : ℂ)^4‖ + ‖(384 : ℂ) * (t : ℂ)^2‖ +
          ‖(96 : ℂ) * c^2 * (t : ℂ)^2‖ + ‖c^4‖ + ‖(24 : ℂ) * c^2‖ + ‖(48 : ℂ)‖ := by
      simp only [hA_def]
      calc ‖256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4 - 24 * c^2 + 48‖
          ≤ ‖256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4 - 24 * c^2‖ + ‖(48 : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ ‖256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4‖ + ‖24 * c^2‖ + ‖(48 : ℂ)‖ := by
            have := norm_sub_le (256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4) (24 * c^2)
            linarith
        _ ≤ ‖256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2‖ + ‖c^4‖ + ‖24 * c^2‖ + ‖(48 : ℂ)‖ := by
            have := norm_add_le (256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2) (c^4)
            linarith
        _ ≤ ‖256 * (t : ℂ)^4 - 384 * (t : ℂ)^2‖ + ‖96 * c^2 * (t : ℂ)^2‖ + ‖c^4‖ + ‖24 * c^2‖ + ‖(48 : ℂ)‖ := by
            have := norm_add_le (256 * (t : ℂ)^4 - 384 * (t : ℂ)^2) (96 * c^2 * (t : ℂ)^2)
            linarith
        _ ≤ ‖256 * (t : ℂ)^4‖ + ‖384 * (t : ℂ)^2‖ + ‖96 * c^2 * (t : ℂ)^2‖ + ‖c^4‖ + ‖24 * c^2‖ + ‖(48 : ℂ)‖ := by
            have := norm_sub_le (256 * (t : ℂ)^4) (384 * (t : ℂ)^2)
            linarith
    have h_eq :
        ‖(256 : ℂ) * (t : ℂ)^4‖ + ‖(384 : ℂ) * (t : ℂ)^2‖ +
          ‖(96 : ℂ) * c^2 * (t : ℂ)^2‖ + ‖c^4‖ + ‖(24 : ℂ) * c^2‖ + ‖(48 : ℂ)‖ = PA := by
      simp only [norm_mul, h_norm_pow, h_norm_pow_c, h256, h384, h96, h24, h48, hPA_def]
    linarith
  -- Bound ‖B‖.
  set PB : ℝ := 192 * ‖c‖ * |t| + 16 * ‖c‖^3 * |t| + 256 * ‖c‖ * |t|^3 with hPB_def
  have h_B : ‖B‖ ≤ PB := by
    have h_step1 : ‖B‖ ≤
        ‖(192 : ℂ) * c * (t : ℂ)‖ + ‖(16 : ℂ) * c^3 * (t : ℂ)‖ + ‖(256 : ℂ) * c * (t : ℂ)^3‖ := by
      simp only [hB_def]
      calc ‖192 * c * (t : ℂ) - 16 * c^3 * (t : ℂ) - 256 * c * (t : ℂ)^3‖
          ≤ ‖192 * c * (t : ℂ) - 16 * c^3 * (t : ℂ)‖ + ‖256 * c * (t : ℂ)^3‖ := norm_sub_le _ _
        _ ≤ ‖192 * c * (t : ℂ)‖ + ‖16 * c^3 * (t : ℂ)‖ + ‖256 * c * (t : ℂ)^3‖ := by
            have := norm_sub_le (192 * c * (t : ℂ)) (16 * c^3 * (t : ℂ))
            linarith
    have h_eq :
        ‖(192 : ℂ) * c * (t : ℂ)‖ + ‖(16 : ℂ) * c^3 * (t : ℂ)‖ + ‖(256 : ℂ) * c * (t : ℂ)^3‖ = PB := by
      simp only [norm_mul, h_norm_pow, h_norm_pow_c, h_norm_t, h192, h16, h256, hPB_def]
    linarith
  -- Combined.
  have hPA_nn : 0 ≤ PA := by simp only [hPA_def]; positivity
  have hPB_nn : 0 ≤ PB := by simp only [hPB_def]; positivity
  have h_exp_neg_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  have h_inner_bd :
      ‖A * Complex.cosh (c * (t : ℂ)) + B * Complex.sinh (c * (t : ℂ))‖ ≤ (PA + PB) * EE := by
    have hbd_A : ‖A‖ * ‖Complex.cosh (c * (t : ℂ))‖ ≤ PA * EE :=
      mul_le_mul h_A h_cosh_norm (norm_nonneg _) hPA_nn
    have hbd_B : ‖B‖ * ‖Complex.sinh (c * (t : ℂ))‖ ≤ PB * EE :=
      mul_le_mul h_B h_sinh_norm (norm_nonneg _) hPB_nn
    calc ‖A * Complex.cosh (c * (t : ℂ)) + B * Complex.sinh (c * (t : ℂ))‖
        ≤ ‖A * Complex.cosh (c * (t : ℂ))‖ + ‖B * Complex.sinh (c * (t : ℂ))‖ :=
          norm_add_le _ _
      _ = ‖A‖ * ‖Complex.cosh (c * (t : ℂ))‖ + ‖B‖ * ‖Complex.sinh (c * (t : ℂ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ PA * EE + PB * EE := by linarith
      _ = (PA + PB) * EE := by ring
  -- Final norm calc.
  calc ‖(A * Complex.cosh (c * (t : ℂ)) + B * Complex.sinh (c * (t : ℂ))) *
          ((Real.exp (-2 * t^2) : ℝ) : ℂ)‖
      = ‖A * Complex.cosh (c * (t : ℂ)) + B * Complex.sinh (c * (t : ℂ))‖ *
        Real.exp (-2 * t^2) := by rw [norm_mul, h_exp_neg_norm]
    _ ≤ ((PA + PB) * EE) * Real.exp (-2 * t^2) :=
        mul_le_mul_of_nonneg_right h_inner_bd h_exp_neg_nn
    _ = (PA + PB) * EE * Real.exp (-2 * t^2) := by ring
    _ = (256 * |t|^4 + 384 * |t|^2 + 96 * ‖c‖^2 * |t|^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
         192 * ‖c‖ * |t| + 16 * ‖c‖^3 * |t| + 256 * ‖c‖ * |t|^3) *
        Real.exp (‖c‖ * |t|) * Real.exp (-2 * t^2) := by
        simp only [hPA_def, hPB_def, hEE]; ring

/-! ## §6 — Square-completion dominator for `coshGaussDeriv4ValC c t` -/

/-- **Square-completion bound:** for `c ≥ 0` and any `t : ℝ`,
`exp(c·t - 2t²) ≤ exp(c²/4) · exp(-t²)`.  Proof: complete the square
`-2t² + ct = -t² - (t - c/2)² + c²/4 ≤ -t² + c²/4`. -/
private lemma exp_linear_minus_2sq_le (c : ℝ) (t : ℝ) :
    Real.exp (c * t - 2 * t^2) ≤ Real.exp (c^2 / 4) * Real.exp (-t^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (c/2 - t)]

/-- **Refined dominator bound on `‖coshGaussDeriv4ValC c t‖`** combining
the polynomial coefficients with the square-completed exponential.
For `t > 0`, the LHS is dominated by a polynomial in `t` (degrees 0..4)
times `exp(‖c‖²/4) · exp(-t²)`.  This is the input to Mellin
convergence (next step) — the polynomial × Gaussian × `t^(σ-1)`
integrand is the standard integrability form. -/
theorem norm_coshGaussDeriv4ValC_le_gauss (c : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖coshGaussDeriv4ValC c t‖ ≤
      Real.exp (‖c‖^2 / 4) *
      (256 * t^4 + 384 * t^2 + 96 * ‖c‖^2 * t^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
        192 * ‖c‖ * t + 16 * ‖c‖^3 * t + 256 * ‖c‖ * t^3) *
      Real.exp (-t^2) := by
  have h := norm_coshGaussDeriv4ValC_le c t
  have h_abs_t : |t| = t := abs_of_pos ht
  rw [h_abs_t] at h
  have h_exp_le : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤
      Real.exp (‖c‖^2 / 4) * Real.exp (-t^2) := by
    have := exp_linear_minus_2sq_le ‖c‖ t
    rw [show (‖c‖ * t - 2 * t^2) = ‖c‖ * t + (-2 * t^2) from by ring,
        Real.exp_add] at this
    exact this
  set P : ℝ := 256 * t^4 + 384 * t^2 + 96 * ‖c‖^2 * t^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
        192 * ‖c‖ * t + 16 * ‖c‖^3 * t + 256 * ‖c‖ * t^3 with hP_def
  have hP_nn : 0 ≤ P := by simp only [hP_def]; positivity
  calc ‖coshGaussDeriv4ValC c t‖
      ≤ P * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) := h
    _ = P * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
    _ ≤ P * (Real.exp (‖c‖^2 / 4) * Real.exp (-t^2)) :=
        mul_le_mul_of_nonneg_left h_exp_le hP_nn
    _ = Real.exp (‖c‖^2 / 4) * P * Real.exp (-t^2) := by ring

/-! ## §7 — Continuity of `coshGaussDeriv4ValC` -/

/-- **`coshGaussDeriv4ValC c` is continuous on ℝ** for any complex `c`. -/
theorem continuous_coshGaussDeriv4ValC (c : ℂ) :
    Continuous (coshGaussDeriv4ValC c) := by
  unfold coshGaussDeriv4ValC
  have h_ofReal : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
  have h_inner : Continuous (fun t : ℝ => c * (t : ℂ)) :=
    continuous_const.mul h_ofReal
  have h_cosh : Continuous (fun t : ℝ => Complex.cosh (c * (t : ℂ))) :=
    Complex.continuous_cosh.comp h_inner
  have h_sinh : Continuous (fun t : ℝ => Complex.sinh (c * (t : ℂ))) :=
    Complex.continuous_sinh.comp h_inner
  have h_exp : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have h_poly_A : Continuous (fun t : ℝ =>
      256 * (t : ℂ)^4 - 384 * (t : ℂ)^2 + 96 * c^2 * (t : ℂ)^2 + c^4 - 24 * c^2 + 48) := by
    fun_prop
  have h_poly_B : Continuous (fun t : ℝ =>
      192 * c * (t : ℂ) - 16 * c^3 * (t : ℂ) - 256 * c * (t : ℂ)^3) := by
    fun_prop
  exact ((h_poly_A.mul h_cosh).add (h_poly_B.mul h_sinh)).mul h_exp

/-- **Asymptotic decay** at infinity: `coshGaussDeriv4ValC c =O[atTop] exp(-t/2)`.
Combines the Gaussian-form pointwise bound with `isLittleO_pow_exp_pos_mul_atTop`
to dominate by `(t^4 · exp(-t)) =o[atTop] exp(-t/2)`. -/
theorem coshGaussDeriv4ValC_isBigO_exp_neg_half_atTop (c : ℂ) :
    coshGaussDeriv4ValC c =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  set cn := ‖c‖ with hcn_def
  have hcn_nn : 0 ≤ cn := norm_nonneg _
  set K : ℝ := Real.exp (cn^2 / 4)
  have hK_pos : 0 < K := Real.exp_pos _
  set M : ℝ := 256 + 384 + 96 * cn^2 + cn^4 + 24 * cn^2 + 48 +
               192 * cn + 16 * cn^3 + 256 * cn
  have hM_nn : 0 ≤ M := by show 0 ≤ _; positivity
  have h_poly_le : ∀ t : ℝ, 1 ≤ t →
      256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 + 24 * cn^2 + 48 +
      192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3 ≤ M * t^4 := by
    intro t ht
    have ht_pos : 0 < t := by linarith
    have ht2 : 1 ≤ t^2 := by nlinarith
    have ht4 : 1 ≤ t^4 := by nlinarith
    have ht4_t2 : t^2 ≤ t^4 := by nlinarith
    have ht4_t : t ≤ t^4 := by nlinarith
    have ht4_t3 : t^3 ≤ t^4 := by nlinarith
    have hcn2 : 0 ≤ cn^2 := sq_nonneg _
    have hcn3 : 0 ≤ cn^3 := by positivity
    have hcn4 : 0 ≤ cn^4 := by positivity
    have h1 : 384 * t^2 ≤ 384 * t^4 := by nlinarith
    have h2 : 96 * cn^2 * t^2 ≤ 96 * cn^2 * t^4 := by nlinarith
    have h3 : cn^4 ≤ cn^4 * t^4 := by nlinarith
    have h4 : 24 * cn^2 ≤ 24 * cn^2 * t^4 := by nlinarith
    have h5 : (48 : ℝ) ≤ 48 * t^4 := by nlinarith
    have h6 : 192 * cn * t ≤ 192 * cn * t^4 := by nlinarith
    have h7 : 16 * cn^3 * t ≤ 16 * cn^3 * t^4 := by nlinarith
    have h8 : 256 * cn * t^3 ≤ 256 * cn * t^4 := by nlinarith
    show _ ≤ M * t^4
    nlinarith [h1, h2, h3, h4, h5, h6, h7, h8]
  have h_exp_sq_le : ∀ t : ℝ, 1 ≤ t → Real.exp (-t^2) ≤ Real.exp (-t) := by
    intro t ht
    apply Real.exp_le_exp.mpr; nlinarith
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop, ‖coshGaussDeriv4ValC c t‖ ≤
      K * M * (t^4 * Real.exp (-t)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht_ge_one
    have ht_pos : 0 < t := by linarith
    have h_bd := norm_coshGaussDeriv4ValC_le_gauss c ht_pos
    have h_K_nn : 0 ≤ K := hK_pos.le
    calc ‖coshGaussDeriv4ValC c t‖
        ≤ K * (256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 + 24 * cn^2 + 48 +
              192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3) * Real.exp (-t^2) := h_bd
      _ ≤ K * (M * t^4) * Real.exp (-t) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (h_poly_le t ht_ge_one) h_K_nn)
            (h_exp_sq_le t ht_ge_one) (Real.exp_pos _).le
          positivity
      _ = K * M * (t^4 * Real.exp (-t)) := by ring
  have h_isBigO_t4_exp : coshGaussDeriv4ValC c =O[Filter.atTop]
      (fun t : ℝ => t^4 * Real.exp (-t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K * M, ?_⟩
    filter_upwards [h_eventually] with t ht_bd
    have h_t4_exp_nn : 0 ≤ t^4 * Real.exp (-t) := by positivity
    rw [Real.norm_of_nonneg h_t4_exp_nn]
    exact ht_bd
  have h_pow_lito : (fun t : ℝ => t^4) =o[Filter.atTop] (fun t : ℝ => Real.exp (t/2)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 4 (show (0:ℝ) < 1/2 from by norm_num)
    convert this using 1; funext t; congr 1; ring
  have h_t4_exp_lito : (fun t : ℝ => t^4 * Real.exp (-t)) =o[Filter.atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have h := h_pow_lito.mul_isBigO
      (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-t)) Filter.atTop)
    have h_eq : (fun t : ℝ => Real.exp (t/2) * Real.exp (-t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; rw [← Real.exp_add]; congr 1; ring
    rw [h_eq] at h
    exact h
  exact h_isBigO_t4_exp.trans_isLittleO h_t4_exp_lito |>.isBigO

/-- **Boundedness near 0** (`coshGaussDeriv4ValC c =O[nhdsWithin 0 (Ioi 0)] x^0`).
The function is bounded on `Ioc 0 1` by an explicit constant via
`norm_coshGaussDeriv4ValC_le_gauss` + `t^k ≤ 1` for `t ∈ (0,1]`. -/
theorem coshGaussDeriv4ValC_isBigO_one_nhds_zero (c : ℂ) :
    coshGaussDeriv4ValC c =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  set M : ℝ := Real.exp (‖c‖^2 / 4) *
    (256 + 384 + 96 * ‖c‖^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
     192 * ‖c‖ + 16 * ‖c‖^3 + 256 * ‖c‖) with hM_def
  refine Asymptotics.IsBigO.of_bound M ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    have h_bd := norm_coshGaussDeriv4ValC_le_gauss c ht_pos
    set cn := ‖c‖ with hcn
    have hcn_nn : 0 ≤ cn := norm_nonneg _
    have h_Q_le : 256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 + 24 * cn^2 + 48 +
                  192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3 ≤
                  256 + 384 + 96 * cn^2 + cn^4 + 24 * cn^2 + 48 +
                  192 * cn + 16 * cn^3 + 256 * cn := by
      have ht4 : t^4 ≤ 1 := pow_le_one₀ ht_pos.le ht_le
      have ht2 : t^2 ≤ 1 := pow_le_one₀ ht_pos.le ht_le
      have hcn2 : 0 ≤ cn^2 := sq_nonneg _
      have hcn3 : 0 ≤ cn^3 := by positivity
      have h_cn2_t2 : cn^2 * t^2 ≤ cn^2 := by nlinarith
      have h_cn_t : cn * t ≤ cn := by nlinarith
      have h_cn3_t : cn^3 * t ≤ cn^3 := by nlinarith
      have h_cn_t3 : cn * t^3 ≤ cn := by nlinarith
      nlinarith [ht4, ht2, ht_le, h_cn2_t2, h_cn_t, h_cn3_t, h_cn_t3]
    have h_exp_le : Real.exp (-t^2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith [sq_nonneg t]
    have h_K_nn : 0 ≤ Real.exp (cn^2 / 4) := (Real.exp_pos _).le
    have h_M_nn : 0 ≤ 256 + 384 + 96 * cn^2 + cn^4 + 24 * cn^2 + 48 +
                  192 * cn + 16 * cn^3 + 256 * cn := by positivity
    calc ‖coshGaussDeriv4ValC c t‖
        ≤ Real.exp (cn^2 / 4) * (256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 +
            24 * cn^2 + 48 + 192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3) *
            Real.exp (-t^2) := h_bd
      _ ≤ Real.exp (cn^2 / 4) * (256 + 384 + 96 * cn^2 + cn^4 + 24 * cn^2 + 48 +
            192 * cn + 16 * cn^3 + 256 * cn) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h_Q_le h_K_nn) h_exp_le
            (Real.exp_pos _).le
          positivity
      _ = M := by simp only [hM_def, hcn]; ring

#print axioms norm_coshGaussDeriv4ValC_le
#print axioms norm_coshGaussDeriv4ValC_le_gauss
#print axioms continuous_coshGaussDeriv4ValC
/-! ## §8 — Phase 2 prerequisites at level 0 (`coshGaussValC`) -/

/-- **Continuity of `coshGaussValC c`.** -/
theorem continuous_coshGaussValC (c : ℂ) : Continuous (coshGaussValC c) := by
  unfold coshGaussValC
  have h_inner : Continuous (fun t : ℝ => c * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have h_cosh : Continuous (fun t : ℝ => Complex.cosh (c * (t : ℂ))) :=
    Complex.continuous_cosh.comp h_inner
  have h_exp : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  exact h_cosh.mul h_exp

/-- **Asymptotic decay** of `coshGaussValC c` at infinity: `=O[atTop] exp(-t/2)`. -/
theorem coshGaussValC_isBigO_exp_neg_half_atTop (c : ℂ) :
    coshGaussValC c =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4)
  have hK_pos : 0 < K := Real.exp_pos _
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop, ‖coshGaussValC c t‖ ≤ K * Real.exp (-t/2) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht_ge_one
    have ht_pos : 0 < t := by linarith
    unfold coshGaussValC
    rw [norm_mul]
    have h_norm_ct : ‖c * (t:ℂ)‖ = ‖c‖ * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ))
      rw [h_norm_ct] at this; exact this
    have h_exp_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    rw [h_exp_norm]
    have h_step : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ K * Real.exp (-t/2) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      rw [show K * Real.exp (-t/2) = Real.exp (‖c‖^2 / 4 + (-t/2)) from by
          show Real.exp _ * _ = _; rw [← Real.exp_add]]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t), sq_nonneg (t - 1), ht_ge_one]
    calc ‖Complex.cosh (c * (t : ℂ))‖ * Real.exp (-2 * t^2)
        ≤ Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_cosh_norm (Real.exp_pos _).le
      _ ≤ K * Real.exp (-t/2) := h_step
  rw [Asymptotics.isBigO_iff]
  refine ⟨K, ?_⟩
  filter_upwards [h_eventually] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact ht

/-- **Boundedness near 0** of `coshGaussValC c`. -/
theorem coshGaussValC_isBigO_one_nhds_zero (c : ℂ) :
    coshGaussValC c =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4)
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    unfold coshGaussValC
    rw [norm_mul]
    have h_norm_ct : ‖c * (t:ℂ)‖ = ‖c‖ * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ))
      rw [h_norm_ct] at this; exact this
    have h_exp_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    rw [h_exp_norm]
    have h_step : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ K := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      show Real.exp _ ≤ Real.exp _
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t)]
    calc ‖Complex.cosh (c * (t : ℂ))‖ * Real.exp (-2 * t^2)
        ≤ Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_cosh_norm (Real.exp_pos _).le
      _ ≤ K := h_step

/-- **Local integrability** of `coshGaussValC c` on `Ioi 0`. -/
theorem coshGaussValC_locallyIntegrableOn (c : ℂ) :
    MeasureTheory.LocallyIntegrableOn (coshGaussValC c) (Set.Ioi 0) MeasureTheory.volume := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (continuous_coshGaussValC c).continuousOn

/-- **Mellin convergence** of `coshGaussValC c` at `s` for `Re s > 0`. -/
theorem coshGaussValC_mellinConvergent (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (coshGaussValC c) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · exact coshGaussValC_locallyIntegrableOn c
  · have h := coshGaussValC_isBigO_exp_neg_half_atTop c
    convert h using 1
    funext t; congr 1; ring
  · exact coshGaussValC_isBigO_one_nhds_zero c
  · exact hs

/-! ## §9 — Phase 2 prerequisites at level 1 (`coshGaussDerivValC`) -/

/-- **Continuity of `coshGaussDerivValC c`.** -/
theorem continuous_coshGaussDerivValC (c : ℂ) : Continuous (coshGaussDerivValC c) := by
  unfold coshGaussDerivValC
  have h_inner : Continuous (fun t : ℝ => c * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have h_cosh : Continuous (fun t : ℝ => Complex.cosh (c * (t : ℂ))) :=
    Complex.continuous_cosh.comp h_inner
  have h_sinh : Continuous (fun t : ℝ => Complex.sinh (c * (t : ℂ))) :=
    Complex.continuous_sinh.comp h_inner
  have h_exp : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have h_polyA : Continuous (fun _ : ℝ => c) := continuous_const
  have h_polyB : Continuous (fun t : ℝ => 4 * (t : ℂ)) := by fun_prop
  exact ((h_polyA.mul h_sinh).sub (h_polyB.mul h_cosh)).mul h_exp

/-- **Asymptotic decay** of `coshGaussDerivValC c` at infinity. -/
theorem coshGaussDerivValC_isBigO_exp_neg_half_atTop (c : ℂ) :
    coshGaussDerivValC c =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4)
  have hK_pos : 0 < K := Real.exp_pos _
  set M : ℝ := ‖c‖ + 4
  have hM_nn : 0 ≤ M := by show 0 ≤ _; positivity
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop, ‖coshGaussDerivValC c t‖ ≤
      K * M * (t * Real.exp (-t)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht_ge_one
    have ht_pos : 0 < t := by linarith
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDerivValC; rw [norm_mul, h_exp_neg_norm]
    have h_inner_bd : ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ ≤
        (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) := by
      calc ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖
          ≤ ‖c * Complex.sinh (c * (t:ℂ))‖ + ‖4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ := norm_sub_le _ _
        _ = ‖c‖ * ‖Complex.sinh (c * (t:ℂ))‖ + ‖(4:ℂ)‖ * ‖(t:ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ ‖c‖ * Real.exp (‖c‖ * t) + ‖(4:ℂ)‖ * t * Real.exp (‖c‖ * t) := by
            rw [h_norm_t]
            have hbd1 := mul_le_mul_of_nonneg_left h_sinh_norm (norm_nonneg c)
            have hbd2 := mul_le_mul_of_nonneg_left h_cosh_norm
              (by positivity : (0:ℝ) ≤ ‖(4:ℂ)‖ * t)
            linarith
        _ = (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) := by
            have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
            rw [h4]; ring
    have h_lin : ‖c‖ + 4 * t ≤ M * t := by
      show ‖c‖ + 4 * t ≤ (‖c‖ + 4) * t
      nlinarith [norm_nonneg c, ht_ge_one]
    have h_exp_prod : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ K * Real.exp (-t) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      rw [show K * Real.exp (-t) = Real.exp (‖c‖^2 / 4 + (-t)) from by
          show Real.exp _ * _ = _; rw [← Real.exp_add]]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t), sq_nonneg (t-1), ht_ge_one]
    calc ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (‖c‖ + 4 * t) * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (M * t) * (K * Real.exp (-t)) :=
          mul_le_mul h_lin h_exp_prod (by positivity) (by positivity)
      _ = K * M * (t * Real.exp (-t)) := by ring
  have h_isBigO_t_exp : coshGaussDerivValC c =O[Filter.atTop]
      (fun t : ℝ => t * Real.exp (-t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K * M, ?_⟩
    filter_upwards [h_eventually, Filter.eventually_ge_atTop (1:ℝ)] with t ht ht_ge_one
    have ht_pos : 0 < t := by linarith
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ t * Real.exp (-t))]
    exact ht
  have h_pow_lito : (fun t : ℝ => t) =o[Filter.atTop] (fun t : ℝ => Real.exp (t/2)) := by
    have h := isLittleO_pow_exp_pos_mul_atTop 1 (show (0:ℝ) < 1/2 from by norm_num)
    have h_eq_lhs : (fun x : ℝ => x^1) = (fun x : ℝ => x) := by funext x; ring
    have h_eq_rhs : (fun x : ℝ => Real.exp ((1/2) * x)) = (fun x : ℝ => Real.exp (x/2)) := by
      funext x; congr 1; ring
    rw [h_eq_lhs, h_eq_rhs] at h
    exact h
  have h_t_exp_lito : (fun t : ℝ => t * Real.exp (-t)) =o[Filter.atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have h := h_pow_lito.mul_isBigO
      (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-t)) Filter.atTop)
    have h_eq : (fun t : ℝ => Real.exp (t/2) * Real.exp (-t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; rw [← Real.exp_add]; congr 1; ring
    rw [h_eq] at h
    exact h
  exact h_isBigO_t_exp.trans_isLittleO h_t_exp_lito |>.isBigO

/-- **Boundedness near 0** of `coshGaussDerivValC c`. -/
theorem coshGaussDerivValC_isBigO_one_nhds_zero (c : ℂ) :
    coshGaussDerivValC c =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4) * (‖c‖ + 4)
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDerivValC; rw [norm_mul, h_exp_neg_norm]
    have h_inner_bd : ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ ≤
        (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) := by
      calc ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖
          ≤ ‖c * Complex.sinh (c * (t:ℂ))‖ + ‖4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ := norm_sub_le _ _
        _ = ‖c‖ * ‖Complex.sinh (c * (t:ℂ))‖ + ‖(4:ℂ)‖ * ‖(t:ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ ‖c‖ * Real.exp (‖c‖ * t) + ‖(4:ℂ)‖ * t * Real.exp (‖c‖ * t) := by
            rw [h_norm_t]
            have hbd1 := mul_le_mul_of_nonneg_left h_sinh_norm (norm_nonneg c)
            have hbd2 := mul_le_mul_of_nonneg_left h_cosh_norm
              (by positivity : (0:ℝ) ≤ ‖(4:ℂ)‖ * t)
            linarith
        _ = (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) := by
            have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
            rw [h4]; ring
    have h_lin_le : ‖c‖ + 4 * t ≤ ‖c‖ + 4 := by linarith
    have h_exp_le : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ Real.exp (‖c‖^2 / 4) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t)]
    calc ‖c * Complex.sinh (c * (t:ℂ)) - 4 * (t:ℂ) * Complex.cosh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (‖c‖ + 4 * t) * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (‖c‖ + 4 * t) * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (‖c‖ + 4) * Real.exp (‖c‖^2 / 4) :=
          mul_le_mul h_lin_le h_exp_le (by positivity) (by positivity)
      _ = K := by show _ = Real.exp _ * _; ring

/-- **Local integrability** of `coshGaussDerivValC c` on `Ioi 0`. -/
theorem coshGaussDerivValC_locallyIntegrableOn (c : ℂ) :
    MeasureTheory.LocallyIntegrableOn (coshGaussDerivValC c) (Set.Ioi 0)
      MeasureTheory.volume := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (continuous_coshGaussDerivValC c).continuousOn

/-- **Mellin convergence** of `coshGaussDerivValC c` at `s` for `Re s > 0`. -/
theorem coshGaussDerivValC_mellinConvergent (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (coshGaussDerivValC c) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · exact coshGaussDerivValC_locallyIntegrableOn c
  · have h := coshGaussDerivValC_isBigO_exp_neg_half_atTop c
    convert h using 1
    funext t; congr 1; ring
  · exact coshGaussDerivValC_isBigO_one_nhds_zero c
  · exact hs

/-! ## §10 — Phase 2 prerequisites at level 2 (`coshGaussDeriv2ValC`) -/

/-- **Continuity of `coshGaussDeriv2ValC c`.** -/
theorem continuous_coshGaussDeriv2ValC (c : ℂ) : Continuous (coshGaussDeriv2ValC c) := by
  unfold coshGaussDeriv2ValC
  have h_inner : Continuous (fun t : ℝ => c * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have h_cosh : Continuous (fun t : ℝ => Complex.cosh (c * (t : ℂ))) :=
    Complex.continuous_cosh.comp h_inner
  have h_sinh : Continuous (fun t : ℝ => Complex.sinh (c * (t : ℂ))) :=
    Complex.continuous_sinh.comp h_inner
  have h_exp : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have h_polyA : Continuous (fun t : ℝ => c^2 - 4 + 16 * (t : ℂ)^2) := by fun_prop
  have h_polyB : Continuous (fun t : ℝ => 8 * c * (t : ℂ)) := by fun_prop
  exact ((h_polyA.mul h_cosh).sub (h_polyB.mul h_sinh)).mul h_exp

/-- **Asymptotic decay** of `coshGaussDeriv2ValC c` at infinity. -/
theorem coshGaussDeriv2ValC_isBigO_exp_neg_half_atTop (c : ℂ) :
    coshGaussDeriv2ValC c =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4)
  set M : ℝ := ‖c‖^2 + 4 + 16 + 8 * ‖c‖
  have hM_nn : 0 ≤ M := by show 0 ≤ _; positivity
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop, ‖coshGaussDeriv2ValC c t‖ ≤
      K * M * (t^2 * Real.exp (-t)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht_ge_one
    have ht_pos : 0 < t := by linarith
    have ht2 : 1 ≤ t^2 := by nlinarith
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_norm_t2 : ‖(t:ℂ)^2‖ = t^2 := by rw [norm_pow, h_norm_t]
    have h_norm_c2 : ‖c^2‖ = ‖c‖^2 := norm_pow _ _
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDeriv2ValC; rw [norm_mul, h_exp_neg_norm]
    have h_A : ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖ ≤ ‖c‖^2 + 4 + 16 * t^2 := by
      calc ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖
          ≤ ‖(c^2 - 4 : ℂ)‖ + ‖(16 : ℂ) * (t:ℂ)^2‖ := norm_add_le _ _
        _ ≤ ‖c^2‖ + ‖(4:ℂ)‖ + ‖(16 : ℂ) * (t:ℂ)^2‖ := by
            have := norm_sub_le (c^2) (4:ℂ); linarith
        _ = ‖c‖^2 + 4 + 16 * t^2 := by
            rw [h_norm_c2, norm_mul, h_norm_t2]
            have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
            have h16 : ‖(16:ℂ)‖ = 16 := by norm_num
            rw [h4, h16]
    have h_B : ‖(8 * c * (t:ℂ) : ℂ)‖ = 8 * ‖c‖ * t := by
      rw [norm_mul, norm_mul, h_norm_t]
      have h8 : ‖(8:ℂ)‖ = 8 := by norm_num
      rw [h8]
    have h_inner_bd :
        ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
         8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖ ≤
        (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by
      calc ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
            8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖
          ≤ ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ))‖ +
            ‖(8 * c * (t:ℂ)) * Complex.sinh (c * (t:ℂ))‖ := norm_sub_le _ _
        _ = ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ +
            ‖(8 * c * (t:ℂ) : ℂ)‖ * ‖Complex.sinh (c * (t:ℂ))‖ := by rw [norm_mul, norm_mul]
        _ ≤ (‖c‖^2 + 4 + 16 * t^2) * Real.exp (‖c‖ * t) +
            (8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by
            rw [h_B]
            have hbd1 := mul_le_mul h_A h_cosh_norm (norm_nonneg _) (by positivity)
            have hbd2 := mul_le_mul_of_nonneg_left h_sinh_norm (by positivity : (0:ℝ) ≤ 8 * ‖c‖ * t)
            linarith
        _ = (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by ring
    have h_lin : ‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t ≤ M * t^2 := by
      show _ ≤ (‖c‖^2 + 4 + 16 + 8 * ‖c‖) * t^2
      have h_cn_nn : 0 ≤ ‖c‖ := norm_nonneg c
      have h1 : (‖c‖^2 + 4) * (t^2 - 1) ≥ 0 := by
        apply mul_nonneg (by positivity) (by linarith)
      have h2 : 8 * ‖c‖ * t * (t - 1) ≥ 0 := by
        apply mul_nonneg (by positivity) (by linarith)
      nlinarith [h1, h2]
    have h_exp_prod : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ K * Real.exp (-t) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      rw [show K * Real.exp (-t) = Real.exp (‖c‖^2 / 4 + (-t)) from by
          show Real.exp _ * _ = _; rw [← Real.exp_add]]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t), sq_nonneg (t-1), ht_ge_one]
    calc ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
          8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (M * t^2) * (K * Real.exp (-t)) :=
          mul_le_mul h_lin h_exp_prod (by positivity) (by positivity)
      _ = K * M * (t^2 * Real.exp (-t)) := by ring
  have h_isBigO_t2_exp : coshGaussDeriv2ValC c =O[Filter.atTop]
      (fun t : ℝ => t^2 * Real.exp (-t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K * M, ?_⟩
    filter_upwards [h_eventually] with t ht
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ t^2 * Real.exp (-t))]
    exact ht
  have h_pow_lito : (fun t : ℝ => t^2) =o[Filter.atTop] (fun t : ℝ => Real.exp (t/2)) := by
    have h := isLittleO_pow_exp_pos_mul_atTop 2 (show (0:ℝ) < 1/2 from by norm_num)
    have h_eq_rhs : (fun x : ℝ => Real.exp ((1/2) * x)) = (fun x : ℝ => Real.exp (x/2)) := by
      funext x; congr 1; ring
    rw [h_eq_rhs] at h; exact h
  have h_t2_exp_lito : (fun t : ℝ => t^2 * Real.exp (-t)) =o[Filter.atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have h := h_pow_lito.mul_isBigO
      (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-t)) Filter.atTop)
    have h_eq : (fun t : ℝ => Real.exp (t/2) * Real.exp (-t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; rw [← Real.exp_add]; congr 1; ring
    rw [h_eq] at h; exact h
  exact h_isBigO_t2_exp.trans_isLittleO h_t2_exp_lito |>.isBigO

/-- **Boundedness near 0** of `coshGaussDeriv2ValC c`. -/
theorem coshGaussDeriv2ValC_isBigO_one_nhds_zero (c : ℂ) :
    coshGaussDeriv2ValC c =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4) * (‖c‖^2 + 4 + 16 + 8 * ‖c‖)
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_norm_t2 : ‖(t:ℂ)^2‖ = t^2 := by rw [norm_pow, h_norm_t]
    have h_norm_c2 : ‖c^2‖ = ‖c‖^2 := norm_pow _ _
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDeriv2ValC; rw [norm_mul, h_exp_neg_norm]
    have h_A : ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖ ≤ ‖c‖^2 + 4 + 16 * t^2 := by
      calc ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖
          ≤ ‖(c^2 - 4 : ℂ)‖ + ‖(16 : ℂ) * (t:ℂ)^2‖ := norm_add_le _ _
        _ ≤ ‖c^2‖ + ‖(4:ℂ)‖ + ‖(16 : ℂ) * (t:ℂ)^2‖ := by
            have := norm_sub_le (c^2) (4:ℂ); linarith
        _ = ‖c‖^2 + 4 + 16 * t^2 := by
            rw [h_norm_c2, norm_mul, h_norm_t2]
            have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
            have h16 : ‖(16:ℂ)‖ = 16 := by norm_num
            rw [h4, h16]
    have h_B : ‖(8 * c * (t:ℂ) : ℂ)‖ = 8 * ‖c‖ * t := by
      rw [norm_mul, norm_mul, h_norm_t]
      have h8 : ‖(8:ℂ)‖ = 8 := by norm_num
      rw [h8]
    have h_inner_bd :
        ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
         8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖ ≤
        (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by
      calc ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
            8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖
          ≤ ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ))‖ +
            ‖(8 * c * (t:ℂ)) * Complex.sinh (c * (t:ℂ))‖ := norm_sub_le _ _
        _ = ‖(c^2 - 4 + 16 * (t:ℂ)^2 : ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ +
            ‖(8 * c * (t:ℂ) : ℂ)‖ * ‖Complex.sinh (c * (t:ℂ))‖ := by rw [norm_mul, norm_mul]
        _ ≤ (‖c‖^2 + 4 + 16 * t^2) * Real.exp (‖c‖ * t) +
            (8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by
            rw [h_B]
            have hbd1 := mul_le_mul h_A h_cosh_norm (norm_nonneg _) (by positivity)
            have hbd2 := mul_le_mul_of_nonneg_left h_sinh_norm (by positivity : (0:ℝ) ≤ 8 * ‖c‖ * t)
            linarith
        _ = (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) := by ring
    have h_lin_le : ‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t ≤ ‖c‖^2 + 4 + 16 + 8 * ‖c‖ := by
      have h_cn_nn : 0 ≤ ‖c‖ := norm_nonneg c
      have ht2_le : t^2 ≤ 1 := pow_le_one₀ ht_pos.le ht_le
      nlinarith
    have h_exp_le : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ Real.exp (‖c‖^2 / 4) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t)]
    calc ‖(c^2 - 4 + 16 * (t:ℂ)^2) * Complex.cosh (c * (t:ℂ)) -
          8 * c * (t:ℂ) * Complex.sinh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (‖c‖^2 + 4 + 16 * t^2 + 8 * ‖c‖ * t) * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (‖c‖^2 + 4 + 16 + 8 * ‖c‖) * Real.exp (‖c‖^2 / 4) :=
          mul_le_mul h_lin_le h_exp_le (by positivity) (by positivity)
      _ = K := by show _ = Real.exp _ * _; ring

/-- **Local integrability** of `coshGaussDeriv2ValC c` on `Ioi 0`. -/
theorem coshGaussDeriv2ValC_locallyIntegrableOn (c : ℂ) :
    MeasureTheory.LocallyIntegrableOn (coshGaussDeriv2ValC c) (Set.Ioi 0)
      MeasureTheory.volume := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (continuous_coshGaussDeriv2ValC c).continuousOn

/-- **Mellin convergence** of `coshGaussDeriv2ValC c` at `s` for `Re s > 0`. -/
theorem coshGaussDeriv2ValC_mellinConvergent (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (coshGaussDeriv2ValC c) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · exact coshGaussDeriv2ValC_locallyIntegrableOn c
  · have h := coshGaussDeriv2ValC_isBigO_exp_neg_half_atTop c
    convert h using 1
    funext t; congr 1; ring
  · exact coshGaussDeriv2ValC_isBigO_one_nhds_zero c
  · exact hs

/-! ## §11 — Phase 2 prerequisites at level 3 (`coshGaussDeriv3ValC`) -/

/-- **Continuity of `coshGaussDeriv3ValC c`.** -/
theorem continuous_coshGaussDeriv3ValC (c : ℂ) : Continuous (coshGaussDeriv3ValC c) := by
  unfold coshGaussDeriv3ValC
  have h_inner : Continuous (fun t : ℝ => c * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have h_cosh : Continuous (fun t : ℝ => Complex.cosh (c * (t : ℂ))) :=
    Complex.continuous_cosh.comp h_inner
  have h_sinh : Continuous (fun t : ℝ => Complex.sinh (c * (t : ℂ))) :=
    Complex.continuous_sinh.comp h_inner
  have h_exp : Continuous (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have h_polyA : Continuous (fun t : ℝ => 48 * (t : ℂ) - 12 * (t : ℂ) * c^2 - 64 * (t : ℂ)^3) := by
    fun_prop
  have h_polyB : Continuous (fun t : ℝ => c^3 - 12 * c + 48 * (t : ℂ)^2 * c) := by fun_prop
  exact ((h_polyA.mul h_cosh).add (h_polyB.mul h_sinh)).mul h_exp

/-- **Asymptotic decay** of `coshGaussDeriv3ValC c` at infinity. -/
theorem coshGaussDeriv3ValC_isBigO_exp_neg_half_atTop (c : ℂ) :
    coshGaussDeriv3ValC c =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4)
  set M : ℝ := 48 + 12 * ‖c‖^2 + 64 + ‖c‖^3 + 12 * ‖c‖ + 48 * ‖c‖
  have hM_nn : 0 ≤ M := by show 0 ≤ _; positivity
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop, ‖coshGaussDeriv3ValC c t‖ ≤
      K * M * (t^3 * Real.exp (-t)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with t ht_ge_one
    have ht_pos : 0 < t := by linarith
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_norm_t2 : ‖(t:ℂ)^2‖ = t^2 := by rw [norm_pow, h_norm_t]
    have h_norm_t3 : ‖(t:ℂ)^3‖ = t^3 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_c2 : ‖c^2‖ = ‖c‖^2 := norm_pow _ _
    have h_norm_c3 : ‖c^3‖ = ‖c‖^3 := norm_pow _ _
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDeriv3ValC; rw [norm_mul, h_exp_neg_norm]
    -- A = 48t - 12tc² - 64t³, ‖A‖ ≤ 48t + 12t‖c‖² + 64t³
    have h_A : ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3 : ℂ)‖ ≤
        48 * t + 12 * t * ‖c‖^2 + 64 * t^3 := by
      have h1 : ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 : ℂ)‖ ≤ ‖(48 * (t:ℂ) : ℂ)‖ + ‖(12 * (t:ℂ) * c^2 : ℂ)‖ :=
        norm_sub_le _ _
      have h2 := norm_sub_le (48 * (t:ℂ) - 12 * (t:ℂ) * c^2) (64 * (t:ℂ)^3)
      have h_eq1 : ‖((48:ℂ) * (t:ℂ))‖ = 48 * t := by
        rw [norm_mul, h_norm_t]
        have : ‖(48:ℂ)‖ = 48 := by norm_num
        rw [this]
      have h_eq2 : ‖((12:ℂ) * (t:ℂ) * c^2)‖ = 12 * t * ‖c‖^2 := by
        rw [norm_mul, norm_mul, h_norm_t, h_norm_c2]
        have : ‖(12:ℂ)‖ = 12 := by norm_num
        rw [this]
      have h_eq3 : ‖((64:ℂ) * (t:ℂ)^3)‖ = 64 * t^3 := by
        rw [norm_mul, h_norm_t3]
        have : ‖(64:ℂ)‖ = 64 := by norm_num
        rw [this]
      linarith
    -- B = c³ - 12c + 48t²c, ‖B‖ ≤ ‖c‖³ + 12‖c‖ + 48t²‖c‖
    have h_B : ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c : ℂ)‖ ≤
        ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖ := by
      have h1 := norm_sub_le (c^3) (12 * c)
      have h2 := norm_add_le (c^3 - 12 * c) (48 * (t:ℂ)^2 * c)
      have h_eq1 : ‖((12:ℂ) * c)‖ = 12 * ‖c‖ := by
        rw [norm_mul]
        have : ‖(12:ℂ)‖ = 12 := by norm_num
        rw [this]
      have h_eq2 : ‖((48:ℂ) * (t:ℂ)^2 * c)‖ = 48 * t^2 * ‖c‖ := by
        rw [norm_mul, norm_mul, h_norm_t2]
        have : ‖(48:ℂ)‖ = 48 := by norm_num
        rw [this]
      linarith [h_norm_c3]
    have h_inner_bd :
        ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
         (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ ≤
        (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
          Real.exp (‖c‖ * t) := by
      calc ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
            (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖
          ≤ ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ))‖ +
            ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ := norm_add_le _ _
        _ = ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3 : ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ +
            ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c : ℂ)‖ * ‖Complex.sinh (c * (t:ℂ))‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (48 * t + 12 * t * ‖c‖^2 + 64 * t^3) * Real.exp (‖c‖ * t) +
            (‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) * Real.exp (‖c‖ * t) := by
            have hbd1 := mul_le_mul h_A h_cosh_norm (norm_nonneg _) (by positivity)
            have hbd2 := mul_le_mul h_B h_sinh_norm (norm_nonneg _) (by positivity)
            linarith
        _ = (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            Real.exp (‖c‖ * t) := by ring
    have h_lin : 48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖ ≤
        M * t^3 := by
      show _ ≤ (48 + 12 * ‖c‖^2 + 64 + ‖c‖^3 + 12 * ‖c‖ + 48 * ‖c‖) * t^3
      have h_cn_nn : 0 ≤ ‖c‖ := norm_nonneg c
      have ht2 : 1 ≤ t^2 := by nlinarith
      have ht3 : 1 ≤ t^3 := by nlinarith
      have ht3_t1 : t ≤ t^3 := by nlinarith
      have ht3_t2 : t^2 ≤ t^3 := by nlinarith
      have hcn2 : 0 ≤ ‖c‖^2 := sq_nonneg _
      have hcn3 : 0 ≤ ‖c‖^3 := by positivity
      have h1 : 48 * t ≤ 48 * t^3 := by nlinarith
      have h2 : 12 * t * ‖c‖^2 ≤ 12 * ‖c‖^2 * t^3 := by nlinarith
      have h4 : ‖c‖^3 ≤ ‖c‖^3 * t^3 := by nlinarith
      have h5 : 12 * ‖c‖ ≤ 12 * ‖c‖ * t^3 := by nlinarith
      have h6 : 48 * t^2 * ‖c‖ ≤ 48 * ‖c‖ * t^3 := by nlinarith
      nlinarith [h1, h2, h4, h5, h6]
    have h_exp_prod : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ K * Real.exp (-t) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      rw [show K * Real.exp (-t) = Real.exp (‖c‖^2 / 4 + (-t)) from by
          show Real.exp _ * _ = _; rw [← Real.exp_add]]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t), sq_nonneg (t-1), ht_ge_one]
    calc ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
          (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (M * t^3) * (K * Real.exp (-t)) :=
          mul_le_mul h_lin h_exp_prod (by positivity) (by positivity)
      _ = K * M * (t^3 * Real.exp (-t)) := by ring
  have h_isBigO_t3_exp : coshGaussDeriv3ValC c =O[Filter.atTop]
      (fun t : ℝ => t^3 * Real.exp (-t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨K * M, ?_⟩
    filter_upwards [h_eventually, Filter.eventually_ge_atTop (1:ℝ)] with t ht ht_ge_one
    have ht_t3_nn : 0 ≤ t^3 := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg ht_t3_nn (Real.exp_pos _).le)]
    exact ht
  have h_pow_lito : (fun t : ℝ => t^3) =o[Filter.atTop] (fun t : ℝ => Real.exp (t/2)) := by
    have h := isLittleO_pow_exp_pos_mul_atTop 3 (show (0:ℝ) < 1/2 from by norm_num)
    have h_eq_rhs : (fun x : ℝ => Real.exp ((1/2) * x)) = (fun x : ℝ => Real.exp (x/2)) := by
      funext x; congr 1; ring
    rw [h_eq_rhs] at h; exact h
  have h_t3_exp_lito : (fun t : ℝ => t^3 * Real.exp (-t)) =o[Filter.atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have h := h_pow_lito.mul_isBigO
      (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-t)) Filter.atTop)
    have h_eq : (fun t : ℝ => Real.exp (t/2) * Real.exp (-t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; rw [← Real.exp_add]; congr 1; ring
    rw [h_eq] at h; exact h
  exact h_isBigO_t3_exp.trans_isLittleO h_t3_exp_lito |>.isBigO

/-- **Boundedness near 0** of `coshGaussDeriv3ValC c`. -/
theorem coshGaussDeriv3ValC_isBigO_one_nhds_zero (c : ℂ) :
    coshGaussDeriv3ValC c =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  set K : ℝ := Real.exp (‖c‖^2 / 4) *
    (48 + 12 * ‖c‖^2 + 64 + ‖c‖^3 + 12 * ‖c‖ + 48 * ‖c‖)
  refine Asymptotics.IsBigO.of_bound K ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_rpow_eq : t ^ (-(0:ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1), mul_one]
    have h_norm_t : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by rw [norm_mul, h_norm_t]
    have h_cosh_norm : ‖Complex.cosh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_cosh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_sinh_norm : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
      have := complex_sinh_norm_le_exp (c * (t : ℂ)); rw [h_norm_ct] at this; exact this
    have h_norm_t2 : ‖(t:ℂ)^2‖ = t^2 := by rw [norm_pow, h_norm_t]
    have h_norm_t3 : ‖(t:ℂ)^3‖ = t^3 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h_norm_c2 : ‖c^2‖ = ‖c‖^2 := norm_pow _ _
    have h_norm_c3 : ‖c^3‖ = ‖c‖^3 := norm_pow _ _
    have h_exp_neg_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (Real.exp_pos _)
    unfold coshGaussDeriv3ValC; rw [norm_mul, h_exp_neg_norm]
    have h_A : ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3 : ℂ)‖ ≤
        48 * t + 12 * t * ‖c‖^2 + 64 * t^3 := by
      have h1 : ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 : ℂ)‖ ≤ ‖(48 * (t:ℂ) : ℂ)‖ + ‖(12 * (t:ℂ) * c^2 : ℂ)‖ :=
        norm_sub_le _ _
      have h2 := norm_sub_le (48 * (t:ℂ) - 12 * (t:ℂ) * c^2) (64 * (t:ℂ)^3)
      have h_eq1 : ‖((48:ℂ) * (t:ℂ))‖ = 48 * t := by
        rw [norm_mul, h_norm_t]
        have : ‖(48:ℂ)‖ = 48 := by norm_num
        rw [this]
      have h_eq2 : ‖((12:ℂ) * (t:ℂ) * c^2)‖ = 12 * t * ‖c‖^2 := by
        rw [norm_mul, norm_mul, h_norm_t, h_norm_c2]
        have : ‖(12:ℂ)‖ = 12 := by norm_num
        rw [this]
      have h_eq3 : ‖((64:ℂ) * (t:ℂ)^3)‖ = 64 * t^3 := by
        rw [norm_mul, h_norm_t3]
        have : ‖(64:ℂ)‖ = 64 := by norm_num
        rw [this]
      linarith
    have h_B : ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c : ℂ)‖ ≤
        ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖ := by
      have h1 := norm_sub_le (c^3) (12 * c)
      have h2 := norm_add_le (c^3 - 12 * c) (48 * (t:ℂ)^2 * c)
      have h_eq1 : ‖((12:ℂ) * c)‖ = 12 * ‖c‖ := by
        rw [norm_mul]
        have : ‖(12:ℂ)‖ = 12 := by norm_num
        rw [this]
      have h_eq2 : ‖((48:ℂ) * (t:ℂ)^2 * c)‖ = 48 * t^2 * ‖c‖ := by
        rw [norm_mul, norm_mul, h_norm_t2]
        have : ‖(48:ℂ)‖ = 48 := by norm_num
        rw [this]
      linarith [h_norm_c3]
    have h_inner_bd :
        ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
         (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ ≤
        (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
          Real.exp (‖c‖ * t) := by
      calc ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
            (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖
          ≤ ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ))‖ +
            ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ := norm_add_le _ _
        _ = ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3 : ℂ)‖ * ‖Complex.cosh (c * (t:ℂ))‖ +
            ‖(c^3 - 12 * c + 48 * (t:ℂ)^2 * c : ℂ)‖ * ‖Complex.sinh (c * (t:ℂ))‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (48 * t + 12 * t * ‖c‖^2 + 64 * t^3) * Real.exp (‖c‖ * t) +
            (‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) * Real.exp (‖c‖ * t) := by
            have hbd1 := mul_le_mul h_A h_cosh_norm (norm_nonneg _) (by positivity)
            have hbd2 := mul_le_mul h_B h_sinh_norm (norm_nonneg _) (by positivity)
            linarith
        _ = (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            Real.exp (‖c‖ * t) := by ring
    have h_lin_le : 48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖ ≤
        48 + 12 * ‖c‖^2 + 64 + ‖c‖^3 + 12 * ‖c‖ + 48 * ‖c‖ := by
      have h_cn_nn : 0 ≤ ‖c‖ := norm_nonneg c
      have ht2_le : t^2 ≤ 1 := pow_le_one₀ ht_pos.le ht_le
      have ht3_le : t^3 ≤ 1 := pow_le_one₀ ht_pos.le ht_le
      have hcn2 : 0 ≤ ‖c‖^2 := sq_nonneg _
      have h_t_cn2 : t * ‖c‖^2 ≤ ‖c‖^2 := by nlinarith
      have h_t2_cn : t^2 * ‖c‖ ≤ ‖c‖ := by nlinarith
      nlinarith
    have h_exp_le : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤ Real.exp (‖c‖^2 / 4) := by
      rw [show Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) = Real.exp (‖c‖ * t - 2 * t^2) from by
          rw [← Real.exp_add]; ring_nf]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖c‖/2 - t)]
    calc ‖(48 * (t:ℂ) - 12 * (t:ℂ) * c^2 - 64 * (t:ℂ)^3) * Complex.cosh (c * (t:ℂ)) +
          (c^3 - 12 * c + 48 * (t:ℂ)^2 * c) * Complex.sinh (c * (t:ℂ))‖ * Real.exp (-2 * t^2)
        ≤ (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_inner_bd (Real.exp_pos _).le
      _ = (48 * t + 12 * t * ‖c‖^2 + 64 * t^3 + ‖c‖^3 + 12 * ‖c‖ + 48 * t^2 * ‖c‖) *
            (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ ≤ (48 + 12 * ‖c‖^2 + 64 + ‖c‖^3 + 12 * ‖c‖ + 48 * ‖c‖) * Real.exp (‖c‖^2 / 4) :=
          mul_le_mul h_lin_le h_exp_le (by positivity) (by positivity)
      _ = K := by show _ = Real.exp _ * _; ring

/-- **Local integrability** of `coshGaussDeriv3ValC c` on `Ioi 0`. -/
theorem coshGaussDeriv3ValC_locallyIntegrableOn (c : ℂ) :
    MeasureTheory.LocallyIntegrableOn (coshGaussDeriv3ValC c) (Set.Ioi 0)
      MeasureTheory.volume := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (continuous_coshGaussDeriv3ValC c).continuousOn

/-- **Mellin convergence** of `coshGaussDeriv3ValC c` at `s` for `Re s > 0`. -/
theorem coshGaussDeriv3ValC_mellinConvergent (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (coshGaussDeriv3ValC c) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · exact coshGaussDeriv3ValC_locallyIntegrableOn c
  · have h := coshGaussDeriv3ValC_isBigO_exp_neg_half_atTop c
    convert h using 1
    funext t; congr 1; ring
  · exact coshGaussDeriv3ValC_isBigO_one_nhds_zero c
  · exact hs

/-- **Local integrability** of `coshGaussDeriv4ValC c` on `Ioi 0`. -/
theorem coshGaussDeriv4ValC_locallyIntegrableOn (c : ℂ) :
    MeasureTheory.LocallyIntegrableOn (coshGaussDeriv4ValC c) (Set.Ioi 0)
      MeasureTheory.volume := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (continuous_coshGaussDeriv4ValC c).continuousOn

/-- **Mellin convergence** of `coshGaussDeriv4ValC c` at `s` for `Re s > 0`. -/
theorem coshGaussDeriv4ValC_mellinConvergent (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (coshGaussDeriv4ValC c) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · exact coshGaussDeriv4ValC_locallyIntegrableOn c
  · have h := coshGaussDeriv4ValC_isBigO_exp_neg_half_atTop c
    convert h using 1
    funext t; congr 1; ring
  · exact coshGaussDeriv4ValC_isBigO_one_nhds_zero c
  · exact hs

#print axioms coshGaussDeriv4ValC_isBigO_exp_neg_half_atTop
#print axioms coshGaussDeriv4ValC_isBigO_one_nhds_zero
#print axioms coshGaussDeriv4ValC_locallyIntegrableOn
#print axioms coshGaussDeriv4ValC_mellinConvergent
#print axioms continuous_coshGaussValC
#print axioms coshGaussValC_isBigO_exp_neg_half_atTop
#print axioms coshGaussValC_isBigO_one_nhds_zero
#print axioms coshGaussValC_locallyIntegrableOn
#print axioms coshGaussValC_mellinConvergent
#print axioms continuous_coshGaussDerivValC
#print axioms coshGaussDerivValC_isBigO_exp_neg_half_atTop
#print axioms coshGaussDerivValC_isBigO_one_nhds_zero
#print axioms coshGaussDerivValC_locallyIntegrableOn
#print axioms coshGaussDerivValC_mellinConvergent
#print axioms continuous_coshGaussDeriv2ValC
#print axioms coshGaussDeriv2ValC_isBigO_exp_neg_half_atTop
#print axioms coshGaussDeriv2ValC_isBigO_one_nhds_zero
#print axioms coshGaussDeriv2ValC_locallyIntegrableOn
#print axioms coshGaussDeriv2ValC_mellinConvergent
#print axioms continuous_coshGaussDeriv3ValC
#print axioms coshGaussDeriv3ValC_isBigO_exp_neg_half_atTop
#print axioms coshGaussDeriv3ValC_isBigO_one_nhds_zero
#print axioms coshGaussDeriv3ValC_locallyIntegrableOn
#print axioms coshGaussDeriv3ValC_mellinConvergent
#print axioms hasDerivAt_complex_cosh_real
#print axioms hasDerivAt_complex_sinh_real
#print axioms coshGaussValC_ofReal_eq
#print axioms coshGaussDerivValC_ofReal_eq
#print axioms coshGaussDeriv2ValC_ofReal_eq
#print axioms coshGaussDeriv3ValC_ofReal_eq
#print axioms coshGaussDeriv4ValC_ofReal_eq
#print axioms coshGaussC_hasDerivAt_iter1
#print axioms coshGaussC_hasDerivAt_iter2
#print axioms coshGaussC_hasDerivAt_iter3
#print axioms coshGaussC_hasDerivAt_iter4

/-! ## §12 — Generic boundary vanishing lemmas (used at all levels) -/

/-- **Generic boundary vanishing at 0:** if `f =O[nhdsWithin 0 (Ioi 0)] x^0`
(i.e. `f` is bounded near 0), then for any `s` with `Re s > 0`,
`f(t) · t^s → 0` as `t → 0⁺`. -/
lemma isBigO_one_cpow_tendsto_zero_nhdsWithin_zero
    {f : ℝ → ℂ}
    (hf : f =O[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x^(-(0:ℝ))))
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => f t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cpow_bd : (fun t : ℝ => (t : ℂ)^s) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ => t^s.re) := by
    apply Asymptotics.IsBigO.of_bound 1
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioi 0, self_mem_nhdsWithin, fun t ht => ?_⟩
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
  have h_eq_one : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
    funext t; rw [neg_zero, Real.rpow_zero]
  rw [h_eq_one] at hf
  have h_prod_bd : (fun t : ℝ => f t * (t : ℂ)^s) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ => t^s.re) := by
    have h := hf.mul h_cpow_bd
    refine h.congr_right ?_
    intro t; ring
  have h_tendsto : Filter.Tendsto (fun t : ℝ => t^s.re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (continuousAt_id.rpow_const (Or.inr hs.le) (x := (0:ℝ))).tendsto
    simp only [id] at h
    rw [show (0:ℝ)^s.re = 0 from Real.zero_rpow hs.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact h_prod_bd.trans_tendsto h_tendsto

/-- **Generic boundary vanishing at infinity:** if `f =O[atTop] exp(-t/2)`,
then for any `s : ℂ`, `f(t) · t^s → 0` as `t → ∞`. -/
lemma isBigO_exp_neg_half_cpow_tendsto_zero_atTop
    {f : ℝ → ℂ}
    (hf : f =O[Filter.atTop] (fun t : ℝ => Real.exp (-t/2)))
    (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => f t * (t : ℂ)^s) Filter.atTop (nhds 0) := by
  have h_cpow_bd : (fun t : ℝ => (t : ℂ)^s) =O[Filter.atTop] (fun t : ℝ => t^s.re) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
  have h_prod_bd : (fun t : ℝ => f t * (t : ℂ)^s) =O[Filter.atTop]
      (fun t : ℝ => Real.exp (-t/2) * t^s.re) := hf.mul h_cpow_bd
  have h_tendsto : Filter.Tendsto (fun t : ℝ => Real.exp (-t/2) * t^s.re)
      Filter.atTop (nhds 0) := by
    have h_rpow_lito : (fun t : ℝ => t^s.re) =o[Filter.atTop]
        (fun t : ℝ => Real.exp (t/4)) := by
      have := isLittleO_rpow_exp_pos_mul_atTop s.re (show (0:ℝ) < 1/4 from by norm_num)
      have h_eq : (fun x : ℝ => Real.exp ((1/4) * x)) = (fun x : ℝ => Real.exp (x/4)) := by
        funext x; congr 1; ring
      rw [h_eq] at this; exact this
    have h_prod : (fun t : ℝ => Real.exp (-t/2) * t^s.re) =o[Filter.atTop]
        (fun t : ℝ => Real.exp (-t/2) * Real.exp (t/4)) :=
      (Asymptotics.isBigO_refl _ _).mul_isLittleO h_rpow_lito
    have h_eq : (fun t : ℝ => Real.exp (-t/2) * Real.exp (t/4)) =
        (fun t : ℝ => Real.exp (-t/4)) := by
      funext t; rw [← Real.exp_add]; congr 1; ring
    rw [h_eq] at h_prod
    have h_exp_tendsto : Filter.Tendsto (fun t : ℝ => Real.exp (-t/4))
        Filter.atTop (nhds 0) := by
      have h_arg : Filter.Tendsto (fun t : ℝ => -t/4) Filter.atTop Filter.atBot := by
        have h_neg : Filter.Tendsto (fun t : ℝ => -t) Filter.atTop Filter.atBot :=
          Filter.tendsto_neg_atTop_atBot
        have h_div : Filter.Tendsto (fun x : ℝ => x/4) Filter.atBot Filter.atBot := by
          apply Filter.Tendsto.atBot_div_const (show (0:ℝ) < 4 from by norm_num)
          exact Filter.tendsto_id
        exact h_div.comp h_neg
      exact Real.tendsto_exp_atBot.comp h_arg
    exact h_prod.trans_tendsto h_exp_tendsto
  exact h_prod_bd.trans_tendsto h_tendsto

/-! ## §13 — Boundary vanishing at each level (specializations) -/

theorem coshGaussValC_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => coshGaussValC c t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  isBigO_one_cpow_tendsto_zero_nhdsWithin_zero (coshGaussValC_isBigO_one_nhds_zero c) hs

theorem coshGaussValC_cpow_tendsto_zero_atTop (c : ℂ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => coshGaussValC c t * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  isBigO_exp_neg_half_cpow_tendsto_zero_atTop (coshGaussValC_isBigO_exp_neg_half_atTop c) s

theorem coshGaussDerivValC_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => coshGaussDerivValC c t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  isBigO_one_cpow_tendsto_zero_nhdsWithin_zero (coshGaussDerivValC_isBigO_one_nhds_zero c) hs

theorem coshGaussDerivValC_cpow_tendsto_zero_atTop (c : ℂ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => coshGaussDerivValC c t * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  isBigO_exp_neg_half_cpow_tendsto_zero_atTop (coshGaussDerivValC_isBigO_exp_neg_half_atTop c) s

theorem coshGaussDeriv2ValC_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => coshGaussDeriv2ValC c t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  isBigO_one_cpow_tendsto_zero_nhdsWithin_zero (coshGaussDeriv2ValC_isBigO_one_nhds_zero c) hs

theorem coshGaussDeriv2ValC_cpow_tendsto_zero_atTop (c : ℂ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => coshGaussDeriv2ValC c t * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  isBigO_exp_neg_half_cpow_tendsto_zero_atTop (coshGaussDeriv2ValC_isBigO_exp_neg_half_atTop c) s

theorem coshGaussDeriv3ValC_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => coshGaussDeriv3ValC c t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  isBigO_one_cpow_tendsto_zero_nhdsWithin_zero (coshGaussDeriv3ValC_isBigO_one_nhds_zero c) hs

theorem coshGaussDeriv3ValC_cpow_tendsto_zero_atTop (c : ℂ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => coshGaussDeriv3ValC c t * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  isBigO_exp_neg_half_cpow_tendsto_zero_atTop (coshGaussDeriv3ValC_isBigO_exp_neg_half_atTop c) s

#print axioms isBigO_one_cpow_tendsto_zero_nhdsWithin_zero
#print axioms isBigO_exp_neg_half_cpow_tendsto_zero_atTop
#print axioms coshGaussValC_cpow_tendsto_zero_nhdsWithin_zero
#print axioms coshGaussValC_cpow_tendsto_zero_atTop
#print axioms coshGaussDerivValC_cpow_tendsto_zero_nhdsWithin_zero
#print axioms coshGaussDerivValC_cpow_tendsto_zero_atTop
#print axioms coshGaussDeriv2ValC_cpow_tendsto_zero_nhdsWithin_zero
#print axioms coshGaussDeriv2ValC_cpow_tendsto_zero_atTop
#print axioms coshGaussDeriv3ValC_cpow_tendsto_zero_nhdsWithin_zero
#print axioms coshGaussDeriv3ValC_cpow_tendsto_zero_atTop

/-! ## §14 — IBP×4 chain for `coshGaussMellinC` (complex c) -/

/-- **IBP step 0 → 1**: `coshGaussMellinC c s = -(1/s) · mellin(coshGaussDerivValC c)(s+1)`. -/
theorem coshGaussMellinC_ibp_step1 (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    coshGaussMellinC c s = -(1/s) * mellin (coshGaussDerivValC c) (s + 1) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have h_eq : coshGaussMellinC c s = mellin (coshGaussValC c) s := by
    unfold coshGaussMellinC mellin coshGaussValC
    rfl
  rw [h_eq]
  refine mellin_ibp (s := s) hs_ne (fun t _ => coshGaussC_hasDerivAt_iter1 c t) ?_ ?_ ?_ ?_
  · exact coshGaussValC_mellinConvergent c hs
  · exact coshGaussDerivValC_mellinConvergent c hs1_re
  · exact coshGaussValC_cpow_tendsto_zero_nhdsWithin_zero c hs
  · exact coshGaussValC_cpow_tendsto_zero_atTop c s

/-- **IBP step 1 → 2**. -/
theorem coshGaussMellinC_ibp_step2 (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (coshGaussDerivValC c) (s + 1) =
      -(1/(s+1)) * mellin (coshGaussDeriv2ValC c) (s + 2) := by
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have h_rewrite : s + 1 + 1 = s + 2 := by ring
  have h := mellin_ibp (s := s + 1) hs1_ne
    (fun t _ => coshGaussC_hasDerivAt_iter2 c t)
    (coshGaussDerivValC_mellinConvergent c hs1_re)
    (by rw [h_rewrite]; exact coshGaussDeriv2ValC_mellinConvergent c hs2_re)
    (coshGaussDerivValC_cpow_tendsto_zero_nhdsWithin_zero c hs1_re)
    (coshGaussDerivValC_cpow_tendsto_zero_atTop c (s + 1))
  rw [h_rewrite] at h
  exact h

/-- **IBP step 2 → 3**. -/
theorem coshGaussMellinC_ibp_step3 (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (coshGaussDeriv2ValC c) (s + 2) =
      -(1/(s+2)) * mellin (coshGaussDeriv3ValC c) (s + 3) := by
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have hs2_ne : (s + 2) ≠ 0 := fun h => by rw [h] at hs2_re; simp at hs2_re
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have h_rewrite : s + 2 + 1 = s + 3 := by ring
  have h := mellin_ibp (s := s + 2) hs2_ne
    (fun t _ => coshGaussC_hasDerivAt_iter3 c t)
    (coshGaussDeriv2ValC_mellinConvergent c hs2_re)
    (by rw [h_rewrite]; exact coshGaussDeriv3ValC_mellinConvergent c hs3_re)
    (coshGaussDeriv2ValC_cpow_tendsto_zero_nhdsWithin_zero c hs2_re)
    (coshGaussDeriv2ValC_cpow_tendsto_zero_atTop c (s + 2))
  rw [h_rewrite] at h
  exact h

/-- **IBP step 3 → 4**. -/
theorem coshGaussMellinC_ibp_step4 (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (coshGaussDeriv3ValC c) (s + 3) =
      -(1/(s+3)) * mellin (coshGaussDeriv4ValC c) (s + 4) := by
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have hs3_ne : (s + 3) ≠ 0 := fun h => by rw [h] at hs3_re; simp at hs3_re
  have hs4_re : 0 < (s + 4).re := by simp; linarith
  have h_rewrite : s + 3 + 1 = s + 4 := by ring
  have h := mellin_ibp (s := s + 3) hs3_ne
    (fun t _ => coshGaussC_hasDerivAt_iter4 c t)
    (coshGaussDeriv3ValC_mellinConvergent c hs3_re)
    (by rw [h_rewrite]; exact coshGaussDeriv4ValC_mellinConvergent c hs4_re)
    (coshGaussDeriv3ValC_cpow_tendsto_zero_nhdsWithin_zero c hs3_re)
    (coshGaussDeriv3ValC_cpow_tendsto_zero_atTop c (s + 3))
  rw [h_rewrite] at h
  exact h

/-- **Full IBP×4 identity**: for `Re s > 0`,
`coshGaussMellinC c s = (1/(s(s+1)(s+2)(s+3))) · mellin(coshGaussDeriv4ValC c)(s+4)`. -/
theorem coshGaussMellinC_ibp_four_times (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    coshGaussMellinC c s =
      1/(s * (s+1) * (s+2) * (s+3)) * mellin (coshGaussDeriv4ValC c) (s + 4) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have hs2_ne : (s + 2) ≠ 0 := fun h => by rw [h] at hs2_re; simp at hs2_re
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have hs3_ne : (s + 3) ≠ 0 := fun h => by rw [h] at hs3_re; simp at hs3_re
  rw [coshGaussMellinC_ibp_step1 c hs, coshGaussMellinC_ibp_step2 c hs,
      coshGaussMellinC_ibp_step3 c hs, coshGaussMellinC_ibp_step4 c hs]
  field_simp

#print axioms coshGaussMellinC_ibp_step1
#print axioms coshGaussMellinC_ibp_step2
#print axioms coshGaussMellinC_ibp_step3
#print axioms coshGaussMellinC_ibp_step4
#print axioms coshGaussMellinC_ibp_four_times

/-! ## §15 — Strip bound prerequisites: integrability of `(t³+t⁴) · ‖deriv4‖` -/

/-- **Integrability of `(t³+t⁴) · ‖coshGaussDeriv4ValC c t‖` on `Ioi 0`.**
The factor `t^(Reρ+3)` for ρ ∈ NTZ (Re ρ ∈ (0,1)) is bounded by `t^3 + t^4`, and
the Gaussian-form bound `‖deriv4 c t‖ ≤ K · Q(t,‖c‖) · exp(-t²)` makes the
product integrable as a sum of `t^k · exp(-t²)` monomials for `k ∈ {3,...,8}`. -/
theorem coshGaussDeriv4ValC_t34_norm_integrable (c : ℂ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖) (Set.Ioi 0) volume := by
  set cn : ℝ := ‖c‖ with hcn_def
  set K : ℝ := Real.exp (cn^2 / 4)
  have hK_pos : 0 < K := Real.exp_pos _
  have h_pow_int : ∀ (n : ℕ),
      MeasureTheory.IntegrableOn
        (fun t : ℝ => t^n * Real.exp (-t^2)) (Set.Ioi 0) volume := by
    intro n
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (s := (n : ℝ))
      (by norm_num : (0:ℝ) < 1)
      (by have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show t^((n : ℝ)) * Real.exp (-1 * t^2) = t^n * Real.exp (-t^2)
    rw [show (-1 * t^2 : ℝ) = -t^2 from by ring,
        show ((n : ℝ)) = ((n : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  set domF : ℝ → ℝ := fun t =>
    K * 256 * (t^7 * Real.exp (-t^2)) +
    K * 384 * (t^5 * Real.exp (-t^2)) +
    K * (96 * cn^2) * (t^5 * Real.exp (-t^2)) +
    K * cn^4 * (t^3 * Real.exp (-t^2)) +
    K * (24 * cn^2) * (t^3 * Real.exp (-t^2)) +
    K * 48 * (t^3 * Real.exp (-t^2)) +
    K * (192 * cn) * (t^4 * Real.exp (-t^2)) +
    K * (16 * cn^3) * (t^4 * Real.exp (-t^2)) +
    K * (256 * cn) * (t^6 * Real.exp (-t^2)) +
    K * 256 * (t^8 * Real.exp (-t^2)) +
    K * 384 * (t^6 * Real.exp (-t^2)) +
    K * (96 * cn^2) * (t^6 * Real.exp (-t^2)) +
    K * cn^4 * (t^4 * Real.exp (-t^2)) +
    K * (24 * cn^2) * (t^4 * Real.exp (-t^2)) +
    K * 48 * (t^4 * Real.exp (-t^2)) +
    K * (192 * cn) * (t^5 * Real.exp (-t^2)) +
    K * (16 * cn^3) * (t^5 * Real.exp (-t^2)) +
    K * (256 * cn) * (t^7 * Real.exp (-t^2)) with hdomF_def
  have h_domF_int : MeasureTheory.IntegrableOn domF (Set.Ioi 0) volume :=
    ((((((((((((((((((h_pow_int 7).const_mul (K * 256)).add
      ((h_pow_int 5).const_mul (K * 384))).add
      ((h_pow_int 5).const_mul (K * (96 * cn^2)))).add
      ((h_pow_int 3).const_mul (K * cn^4))).add
      ((h_pow_int 3).const_mul (K * (24 * cn^2)))).add
      ((h_pow_int 3).const_mul (K * 48))).add
      ((h_pow_int 4).const_mul (K * (192 * cn)))).add
      ((h_pow_int 4).const_mul (K * (16 * cn^3)))).add
      ((h_pow_int 6).const_mul (K * (256 * cn)))).add
      ((h_pow_int 8).const_mul (K * 256))).add
      ((h_pow_int 6).const_mul (K * 384))).add
      ((h_pow_int 6).const_mul (K * (96 * cn^2)))).add
      ((h_pow_int 4).const_mul (K * cn^4))).add
      ((h_pow_int 4).const_mul (K * (24 * cn^2)))).add
      ((h_pow_int 4).const_mul (K * 48))).add
      ((h_pow_int 5).const_mul (K * (192 * cn)))).add
      ((h_pow_int 5).const_mul (K * (16 * cn^3)))).add
      ((h_pow_int 7).const_mul (K * (256 * cn)))
  refine MeasureTheory.Integrable.mono' h_domF_int ?_ ?_
  · refine ((continuous_id.pow 3).add (continuous_id.pow 4)).aestronglyMeasurable.mul ?_
    exact (continuous_coshGaussDeriv4ValC c).norm.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht_pos : 0 < t := ht
    have h_norm_bd := norm_coshGaussDeriv4ValC_le_gauss c ht_pos
    have h_t34_nn : 0 ≤ t^3 + t^4 := by positivity
    rw [show ‖(t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖‖ =
        (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖ from
      Real.norm_of_nonneg (by positivity)]
    have h_step1 : (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖ ≤
        (t^3 + t^4) *
        (K * (256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 + 24 * cn^2 + 48 +
              192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3) *
         Real.exp (-t^2)) := mul_le_mul_of_nonneg_left h_norm_bd h_t34_nn
    have h_step2 : (t^3 + t^4) *
        (K * (256 * t^4 + 384 * t^2 + 96 * cn^2 * t^2 + cn^4 + 24 * cn^2 + 48 +
              192 * cn * t + 16 * cn^3 * t + 256 * cn * t^3) *
         Real.exp (-t^2)) = domF t := by
      simp only [hdomF_def]; ring
    linarith [h_step1, h_step2.le]

#print axioms coshGaussDeriv4ValC_t34_norm_integrable

/-! ## §16 — Strip bound on `coshGaussMellinC c ρ` (quartic-decay form) -/

/-- **Strip bound on `coshGaussMellinC c ρ` for `ρ ∈ NTZ`** (quartic form).
There exists `M(c) ≥ 0` such that
`‖coshGaussMellinC c ρ‖ ≤ M(c) / ‖ρ(ρ+1)(ρ+2)(ρ+3)‖` for all `ρ ∈ NTZ`.

The witness `M(c) = ∫ (t³+t⁴)·‖coshGaussDeriv4ValC c t‖ dt` is finite by
`coshGaussDeriv4ValC_t34_norm_integrable c`. The bound is established via:
1. IBP×4: `coshGaussMellinC c ρ = (1/(ρ(ρ+1)(ρ+2)(ρ+3))) · mellin(D⁴)(ρ+4)`.
2. `‖mellin(D⁴)(ρ+4)‖ ≤ ∫ t^(Reρ+3) · ‖D⁴‖ dt ≤ ∫ (t³+t⁴) · ‖D⁴‖ dt = M`.
3. Combine. -/
theorem coshGaussMellinC_strip_bound_quartic (c : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖coshGaussMellinC c ρ.val‖ ≤
          M * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := by
  set M : ℝ := ∫ t in Set.Ioi (0:ℝ), (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖
  have hM_nn : 0 ≤ M := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht; have ht_pos : (0:ℝ) < t := ht; positivity
  refine ⟨M, hM_nn, fun ρ => ?_⟩
  obtain ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  have h_ibp := coshGaussMellinC_ibp_four_times c (s := ρ.val) hRe_pos
  have h_mellin_bd : ‖mellin (coshGaussDeriv4ValC c) (ρ.val + 4)‖ ≤ M := by
    unfold mellin
    have h_re_eq : (ρ.val + 4 - 1).re = ρ.val.re + 3 := by
      have : (ρ.val + 4 - 1).re = ρ.val.re + 4 - 1 := by simp
      linarith
    have h_norm_eq : ∀ t > (0:ℝ),
        ‖(t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ =
        t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
      intro t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, h_re_eq]
    have h_step1 : ‖∫ t in Set.Ioi (0:ℝ),
            (t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ ≤
        ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
      calc ‖∫ t in Set.Ioi (0:ℝ),
              (t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖
          ≤ ∫ t in Set.Ioi (0:ℝ),
              ‖(t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro t ht; exact h_norm_eq t ht
    have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
        t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ ≤
        (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖ := by
      intro t ht
      have ht_pos : (0:ℝ) < t := ht
      have h_norm_nn : 0 ≤ ‖coshGaussDeriv4ValC c t‖ := norm_nonneg _
      apply mul_le_mul_of_nonneg_right _ h_norm_nn
      rcases le_or_gt 1 t with ht1 | ht1
      · have h_rpow_le : t^(ρ.val.re + 3) ≤ t^(4:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        have h_t4 : t^(4:ℝ) = t^4 := by norm_num
        rw [h_t4] at h_rpow_le
        have : 0 ≤ t^3 := by positivity
        linarith
      · have h_rpow_le : t^(ρ.val.re + 3) ≤ t^(3:ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos ht1.le (by linarith)
        have h_t3 : t^(3:ℝ) = t^3 := by norm_num
        rw [h_t3] at h_rpow_le
        have : 0 ≤ t^4 := by positivity
        linarith
    have h_t34_int := coshGaussDeriv4ValC_t34_norm_integrable c
    have h_lhs_int : MeasureTheory.IntegrableOn
        (fun t : ℝ => t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖) (Set.Ioi 0) volume := by
      refine MeasureTheory.Integrable.mono' h_t34_int ?_ ?_
      · refine (Real.continuous_rpow_const ?_).aestronglyMeasurable.mul
          (continuous_coshGaussDeriv4ValC c).norm.aestronglyMeasurable
        linarith
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        rw [Real.norm_of_nonneg (by have ht_pos : (0:ℝ) < t := ht; positivity)]
        exact h_pointwise t ht
    have h_step2 : ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ ≤
        M := MeasureTheory.setIntegral_mono_on h_lhs_int h_t34_int measurableSet_Ioi h_pointwise
    linarith
  rw [h_ibp, norm_mul, norm_div, norm_one]
  calc 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ *
      ‖mellin (coshGaussDeriv4ValC c) (ρ.val + 4)‖
      ≤ 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ * M := by
        apply mul_le_mul_of_nonneg_left h_mellin_bd; positivity
    _ = M * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := by ring

#print axioms coshGaussMellinC_strip_bound_quartic

end Contour
end WeilPositivity
end ZD

end
