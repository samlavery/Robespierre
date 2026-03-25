import Mathlib
/-!
# Zeros of the Completed Riemann Zeta Function: Symmetry about Re(s) = 1/2
## What is proven here
We prove **unconditionally** (no assumption of the Riemann Hypothesis) that:
1. **Functional equation symmetry of zeros**: If `completedRiemannZeta s₀ = 0`, then
   `completedRiemannZeta (1 - s₀) = 0`. This is an immediate consequence of the
   functional equation `ξ(1-s) = ξ(s)`, which is already in Mathlib.
2. **Zeros at Re(s) = π/6 are paired with zeros at Re(s) = 1 - π/6 ≈ 0.4764**:
   If `s₀ = π/6 + it` is a zero, then `1 - s₀ = (1 - π/6) - it` is also a zero.
   The paired zero has the **same imaginary part** (up to sign) and lives on the
   line `Re(s) = 1 - π/6`.
3. **Non-vanishing on Re(s) ≥ 1**: The Riemann zeta function has no zeros in the
   region `Re(s) ≥ 1`, which is already in Mathlib.
## What CANNOT be proven (and why)
The claim that "zeros at Re(s) = π/6 are structurally locked to zeros at Re(s) = 1/2"
is **not a standard mathematical result** and appears to be **false** as stated:
- The functional equation relates `ξ(s)` to `ξ(1-s)`, so it pairs the line
  `Re(s) = π/6` with the line `Re(s) = 1 - π/6 ≈ 0.4764`, **not** with `Re(s) = 1/2`.
- The claim that `Im(ζ(π/6 + it)) = 0` for all `t` (i.e., that the zeta function is
  real-valued on the line `Re(s) = π/6`) is **false**. The zeta function is real-valued
  on the real axis, and Hardy's Z-function is real on the critical line `Re(s) = 1/2`,
  but there is no analogous result for `Re(s) = π/6`.
- The only known "structural locking" of zeros is:
  (a) The symmetry `s ↔ 1-s` from the functional equation.
  (b) The symmetry `s ↔ s̄` from the fact that `ζ(s̄) = ζ(s)̄`.
  Neither of these creates a link between `Re(s) = π/6` and `Re(s) = 1/2` specifically.
- If the Riemann Hypothesis is true, then there are **no** zeros at `Re(s) = π/6`
  at all (since all non-trivial zeros would be on `Re(s) = 1/2`), making the question
  vacuous.
-/
open Complex in
/-- The functional equation: zeros of the completed Riemann zeta function are
symmetric about the line `Re(s) = 1/2`. If `ξ(s₀) = 0`, then `ξ(1 - s₀) = 0`. -/
theorem completedRiemannZeta_zero_symm (s₀ : ℂ) (h : completedRiemannZeta s₀ = 0) :
    completedRiemannZeta (1 - s₀) = 0 := by
  rw [← h, completedRiemannZeta_one_sub]
open Complex in
/-- The "structural pairing" at any vertical line: if `ξ(σ + it) = 0`,
then `ξ((1-σ) + i(-t)) = 0`. Applied with `σ = π/6`, this gives a zero at
`Re(s) = 1 - π/6 ≈ 0.4764` — NOT at `Re(s) = 1/2`.
This is the correct version of "structural locking": zeros on ANY vertical line
`Re(s) = σ` are paired with zeros on `Re(s) = 1 - σ` at the negated height. -/
theorem completedRiemannZeta_zero_pairing (σ t : ℝ)
    (h : completedRiemannZeta (↑σ + ↑t * I) = 0) :
    completedRiemannZeta (↑(1 - σ) + ↑(-t) * I) = 0 := by
  have h_fun_eq : completedRiemannZeta (1 - (σ + t * Complex.I)) =
      completedRiemannZeta (σ + t * Complex.I) :=
    completedRiemannZeta_one_sub _
  convert h_fun_eq.trans h using 2; push_cast; ring
/-- The Riemann zeta function has no zeros on or to the right of `Re(s) = 1`.
This is unconditional and already in Mathlib. -/
theorem riemannZeta_nonvanishing_re_ge_one (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs