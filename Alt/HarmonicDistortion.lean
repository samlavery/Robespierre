import Mathlib
open Complex in
/-- **Harmonic disruption drives cosh zeros off the imaginary axis.**
The zeros of `cosh` lie on the imaginary axis at `z = i·π·(n + 1/2)`.
Adding a nonzero real‐linear perturbation `a·z` ("harmonic disruption") forces
every zero off that axis: for `a ≠ 0`, the equation `cosh(iy) + a·(iy) = 0` has
no real solution `y`.
*Proof.* On the imaginary axis, `cosh(iy) = cos y`, so
`cosh(iy) + a·(iy) = cos y + i·(a·y)`. Setting real and imaginary parts to zero
gives `cos y = 0` and `a·y = 0`. Since `a ≠ 0` we get `y = 0`, but `cos 0 = 1`. -/
theorem harmonic_disruption_no_imaginary_zero
    (a : ℝ) (ha : a ≠ 0) (y : ℝ) :
    cosh (I * ↑y) + ↑a * (I * ↑y) ≠ 0 := by
  norm_num [ Complex.ext_iff, Complex.cosh, Complex.exp_re, Complex.exp_im ] at * ; aesop;
