import Mathlib

/-!
# Cosh Kernel at arcsin(1/2): Imaginary Vanishing and Reflection Symmetry

We prove unconditionally that:

1. **arcsin(1/2) = π/6** — this is the fundamental evaluation.

2. **The cosh kernel at arcsin(1/2) has zero imaginary part** — when we embed
   `cosh(arcsin(1/2))` into the complex numbers via `Complex.cosh`, the imaginary
   component vanishes. This is because `arcsin(1/2)` is real, and `cosh` maps reals
   to reals. In particular, any "prime harmonic" contribution of the form
   `∑ₚ f(p) · cosh(arcsin(1/2))` remains purely real, so all imaginary contributions
   cancel completely.

3. **Reflection symmetry at arcsin(1/2)** — `cosh` is an even function:
   `cosh(x) = cosh(-x)`. This means the cosh kernel is invariant under reflection
   `x ↦ -x`. Consequently, if we check vanishing at `arcsin(1/2)`, the reflected
   point `−arcsin(1/2)` gives the same value, confirming complete cancellation by
   symmetry.

The key mathematical point: `cosh` applied to any real argument produces a purely
real result. The imaginary part is *unconditionally* zero — no hypothesis about primes,
the Riemann zeta function, or any other analytic object is needed. The "absorption" of
prime harmonics into a real value is a consequence of `cosh : ℝ → ℝ` being real-valued.
-/

open Real

/-! ## Part 1: arcsin(1/2) = π/6 -/

/-
PROBLEM
The fundamental evaluation: arcsin(1/2) = π/6.

PROVIDED SOLUTION
Use Real.arcsin_eq_of_sin_eq with sin(π/6) = 1/2, and the fact that π/6 ∈ [-π/2, π/2].
-/
theorem arcsin_one_half : arcsin (1 / 2 : ℝ) = π / 6 := by
  rw [ ← Real.sin_pi_div_six, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ]

/-! ## Part 2: Imaginary part of cosh kernel vanishes at real arguments -/

/-
For any real number x, the complex cosh applied to x has zero imaginary part.
This is the core "cancellation" result: all imaginary contributions vanish.
-/
theorem cosh_real_im_zero (x : ℝ) : (Complex.cosh (↑x)).im = 0 := by
  norm_num [ Complex.cosh, Complex.exp_re, Complex.exp_im ]

/-
Specialization: the cosh kernel at arcsin(1/2) has zero imaginary part.
-/
theorem cosh_at_arcsin_half_im_zero :
    (Complex.cosh (↑(arcsin (1 / 2 : ℝ)))).im = 0 := by
      norm_num [ Complex.cosh, Complex.exp_re, Complex.exp_im ] at *

/-
PROBLEM
The cosh kernel at arcsin(1/2) is purely real: it equals its real part.

PROVIDED SOLUTION
Use Complex.ext to show re and im agree. The im part is 0 by cosh_ofReal_im.
-/
theorem cosh_at_arcsin_half_purely_real :
    Complex.cosh (↑(arcsin (1 / 2 : ℝ))) = ↑((Complex.cosh (↑(arcsin (1 / 2 : ℝ)))).re) := by
  norm_num [ Complex.ext_iff, Complex.cosh, Complex.exp_re, Complex.exp_im ]

/-! ## Part 3: Reflection symmetry — cosh(x) = cosh(-x) -/

/-
cosh is an even function: reflection symmetry.
-/
theorem cosh_reflection (x : ℝ) : Real.cosh x = Real.cosh (-x) := by
  rw [ Real.cosh_neg ]

/-
Reflection of the cosh kernel at arcsin(1/2):
    cosh(arcsin(1/2)) = cosh(-arcsin(1/2)).
    If the value vanishes at arcsin(1/2), it vanishes at the reflected point too.
-/
theorem cosh_reflection_at_arcsin_half :
    Real.cosh (arcsin (1 / 2 : ℝ)) = Real.cosh (-(arcsin (1 / 2 : ℝ))) := by
      rw [ Real.cosh_neg ]

/-
PROBLEM
Complex version of reflection: the complex cosh kernel is also reflection-symmetric.

PROVIDED SOLUTION
Use Complex.cosh_neg and the fact that ↑(-x) = -↑x.
-/
theorem complex_cosh_reflection (x : ℝ) :
    Complex.cosh (↑x) = Complex.cosh (↑(-x)) := by
      norm_num +zetaDelta at *

/-! ## Part 4: Complete cancellation — if everything vanishes, everything has cancelled -/

/-
PROBLEM
If the imaginary part of a complex number is zero and its real part is zero,
    then the number is zero — complete cancellation.

PROVIDED SOLUTION
Use Complex.ext, the re and im are both 0.
-/
theorem complete_cancellation (z : ℂ) (him : z.im = 0) (hre : z.re = 0) : z = 0 := by
  exact Complex.ext hre him

/-
The imaginary part of the cosh kernel vanishes at both arcsin(1/2)
    and its reflection −arcsin(1/2), confirming cancellation by symmetry.
-/
theorem reflection_confirms_cancellation :
    (Complex.cosh (↑(arcsin (1 / 2 : ℝ)))).im = 0 ∧
    (Complex.cosh (↑(-(arcsin (1 / 2 : ℝ))))).im = 0 := by
      norm_num [ Complex.cosh, Complex.exp_re, Complex.exp_im ]

/-
For any prime p, the imaginary part of cosh(p * arcsin(1/2)) vanishes.
    This shows that "prime harmonics" contribute zero imaginary part.
-/
theorem prime_harmonic_im_zero (p : ℕ) (hp : Nat.Prime p) :
    (Complex.cosh (↑(↑p * arcsin (1 / 2 : ℝ)))).im = 0 := by
      norm_num [ Complex.cosh, Complex.exp_re, Complex.exp_im ]

/-
PROBLEM
The sum of cosh over any finite set of primes, evaluated at arcsin(1/2),
    has zero imaginary part — all prime harmonics cancel in the imaginary direction.

PROVIDED SOLUTION
Use induction on the finset. Each term has im = 0 by cosh_ofReal_im. The sum of complex numbers with zero imaginary parts has zero imaginary part (im distributes over sums).
-/
theorem prime_harmonic_sum_im_zero (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (∑ p ∈ S, Complex.cosh (↑(↑p * arcsin (1 / 2 : ℝ)))).im = 0 := by
      norm_cast