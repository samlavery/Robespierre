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