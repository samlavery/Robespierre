import Mathlib
/-!
# Cosh has no real zeros — in particular not at π/6, even under reflection
We prove unconditionally that `Real.cosh x ≥ 1` for all real `x`,
and therefore `cosh` has no real zeros whatsoever. In particular:
* `cosh(π/6) ≠ 0`  ("cosh zeros at π/6 do not cancel distorted harmonics")
* `cosh(-π/6) ≠ 0` ("offline cosh zeros do not vanish under reflection")
These hold unconditionally because `cosh` is bounded below by 1 on the reals.
-/
open Real
/-- `cosh x ≥ 1` for every real `x`. This is the unconditional lower bound
    that prevents cosh from having any real zeros. -/
theorem cosh_ge_one (x : ℝ) : cosh x ≥ 1 :=
  Real.one_le_cosh x
/-- The reflection identity: `cosh(-x) = cosh(x)`. -/
theorem cosh_neg_eq (x : ℝ) : cosh (-x) = cosh x :=
  Real.cosh_neg x
/-- `cosh(π / 6) ≠ 0`: cosh zeros at π/6 do not cancel distorted harmonics. -/
theorem cosh_pi_div_six_ne_zero : cosh (π / 6) ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)
/-- `cosh(-π / 6) ≠ 0`: offline cosh zeros do not vanish under reflection. -/
theorem cosh_neg_pi_div_six_ne_zero : cosh (-(π / 6)) ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)
/-- Unconditionally, `cosh` has no real zeros at all. -/
theorem cosh_ne_zero (x : ℝ) : cosh x ≠ 0 :=
  ne_of_gt (Real.cosh_pos x)

