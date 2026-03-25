import Mathlib
/-!
# Robespierre Cosh Kernel: Axis Reality and Zero Transport
## Overview
We prove two unconditional results about the Robespierre cosh kernel:
1. **Kernel-axis reality**: The kernel Ξ(θ + it) is real-valued for every real t,
   where θ = arcsin(1/2) = π/6.
2. **Exact zero transport**: The zeros of the Riemann zeta function on the
   critical line Re(s) = 1/2 are in exact bijection with the zeros of
   RobespierreZetaO on the θ-axis.
No use is made of the functional equation s ↦ 1 - s, the Riemann Hypothesis,
or any equivalent thereof.
-/
noncomputable section
open Complex
/-! ## Definitions -/
/-- The Robespierre theta parameter: θ = arcsin(1/2) = π/6. -/
def robθ : ℝ := Real.arcsin (1 / 2)
/-- θ is strictly positive. -/
lemma robθ_pos : robθ > 0 := Real.arcsin_pos.mpr (by norm_num)
/-- θ is nonzero. -/
lemma robθ_ne_zero : robθ ≠ 0 := ne_of_gt robθ_pos
/-- The Robespierre cosh kernel, parameterized by real coefficients `a` and
    real log-frequencies `c`. The kernel is:
      Ξ(s) = ∑' n, a(n) * (2 * cosh((s - θ) * c(n)))
    where the sum is over ℕ (or any countable index type). -/
def RobespierreXi (a : ℕ → ℝ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n, (a n : ℂ) * (2 * cosh ((s - ↑robθ) * ↑(c n)))
/-- The Robespierre zeta observable:
      RobespierreZetaO(s) = ζ(s.re / (2θ) + s.im · i)
    This maps the θ-axis to the critical line. -/
def RobespierreZetaO (s : ℂ) : ℂ :=
  riemannZeta (↑(s.re / (2 * robθ)) + ↑s.im * I)
/-! ## Part 1: Kernel-axis reality -/
/-- Each summand of the kernel at s = θ + it is real-valued.
When s = θ + it, the argument to cosh is it · c(n) = (t · c(n)) · I.
By `cosh(y · I) = cos(y)`, the summand becomes `a(n) * 2 * cos(t · c(n))`,
which is real (imaginary part zero). -/
lemma kernel_summand_real (a : ℕ → ℝ) (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ((a n : ℂ) * (2 * cosh ((↑t * I) * ↑(c n)))).im = 0 := by
  norm_num [Complex.cosh, Complex.exp_re, Complex.exp_im]
/-- **Kernel-axis reality theorem.**
For the Robespierre cosh kernel with real coefficients `a` and real
log-frequencies `c`, the value Ξ(θ + it) is real for every real t,
provided the series is summable.
**Proof**:
1. Substitute s = θ + it, so s - θ = it (purely imaginary).
2. Each summand becomes a(n) * 2 * cosh(it · c(n)).
3. By cosh(iy) = cos(y), this equals a(n) * 2 * cos(t · c(n)), which is real.
4. By summability, the infinite series of reals has imaginary part zero. -/
theorem kernel_axis_reality (a : ℕ → ℝ) (c : ℕ → ℝ) (t : ℝ)
    (hs : Summable (fun n => (a n : ℂ) * (2 * cosh ((↑t * I) * ↑(c n))))) :
    (RobespierreXi a c (↑robθ + ↑t * I)).im = 0 := by
  have key : ∀ n, ((a n : ℂ) * (2 * cosh ((↑t * I) * ↑(c n)))).im = 0 :=
    kernel_summand_real a c t
  unfold RobespierreXi
  have hrw : ∀ n, (a n : ℂ) * (2 * cosh ((↑robθ + ↑t * I - ↑robθ) * ↑(c n))) =
      (a n : ℂ) * (2 * cosh ((↑t * I) * ↑(c n))) := fun n => by
    congr 1; congr 1; congr 1; ring
  simp_rw [hrw]
  rw [Complex.im_tsum hs]
  simp [key]
/-! ## Part 2: Exact zero transport on the θ-axis -/
/-- When s = θ + t·I, the real part is θ. -/
lemma re_robθ_add_tI (t : ℝ) : (↑robθ + ↑t * I : ℂ).re = robθ := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
/-- When s = θ + t·I, the imaginary part is t. -/
lemma im_robθ_add_tI (t : ℝ) : (↑robθ + ↑t * I : ℂ).im = t := by
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
/-- θ / (2θ) = 1/2. -/
lemma robθ_div_two_robθ : robθ / (2 * robθ) = 1 / 2 := by
  have h : robθ ≠ 0 := robθ_ne_zero
  field_simp
/-- **Exact zero transport theorem.**
For every real t:
  ζ(1/2 + t·i) = 0  ↔  RobespierreZetaO(θ + t·i) = 0
**Proof**:
1. Unfold RobespierreZetaO at s = θ + t·I.
2. Compute s.re = θ and s.im = t.
3. Simplify θ/(2θ) = 1/2.
4. Both sides reduce to `riemannZeta(1/2 + t·i) = 0`. -/
theorem exact_zero_transport (t : ℝ) :
    riemannZeta (1 / 2 + ↑t * I) = 0 ↔ RobespierreZetaO (↑robθ + ↑t * I) = 0 := by
  unfold RobespierreZetaO
  rw [re_robθ_add_tI, im_robθ_add_tI, robθ_div_two_robθ]
  simp
end