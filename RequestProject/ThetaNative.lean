import Mathlib

/-! # θ-Native Completion Framework

Formalization of the θ-native completion framework definitions and core theorems.

## Main definitions

- `theta`: The primitive angle θ = arcsin(1/2) = π/6
- `phiPrime`: Circle-native prime geometry φ(p) = 2θ·p
- `primeLogFreq`: Prime-log frequency u_p = log(φ(p))
- `thetaCoeff`: Coefficient a_p = π/6 · ((2π - 3)/π)^p
- `XiThetaFinite`: Finite θ-native kernel Ξ_{θ,P}(s)
- `criticalLineSum`: Critical-line sum C_P(t)
- `criticalLineSumDeriv`: Derivative of C_P

## Main results

- `sin_theta_eq`: sin(θ) = 1/2
- `theta_eq_pi_div_six`: θ = π/6
- `tauAngle_eq_pi`: τ = 6θ = π
- `doubleTheta_eq`: 2θ = π/3
- `XiThetaFinite_symm`: Symmetry Ξ_{θ,P}(s) = Ξ_{θ,P}(2θ - s)
- `criticalLineSum_deriv_formula`: C_P'(t) = -Σ a_p u_p sin(t u_p)
-/

open Real

noncomputable section

-- ============================================================
-- SECTION 1. PRIMITIVES / GEOMETRIC DATA
-- ============================================================

/-- The set of primes up to `P`. -/
def primesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime

/-- Primitive circle-native angle: θ = arcsin(1/2). -/
def theta : ℝ := Real.arcsin (1 / 2)

/-- Doubled angle: 2θ. -/
def doubleTheta : ℝ := 2 * theta

/-- Full turn: τ = 6θ. -/
def tauAngle : ℝ := 6 * theta

/-- Circle-native prime geometry: φ(p) = 2θ · p. -/
def phiPrime (p : ℕ) : ℝ := doubleTheta * p

/-- Prime-log frequency: u_p = log(φ(p)). -/
def primeLogFreq (p : ℕ) : ℝ := Real.log (phiPrime p)

/-- Preferred coefficient law:
    a_p = π/6 · ((2π - 3)/π)^p. -/
def thetaCoeff (p : ℕ) : ℝ :=
  Real.pi / 6 * (((2 * Real.pi - 3) / Real.pi) ^ p)

-- ============================================================
-- SECTION 2. FINITE θ-NATIVE KERNEL
-- ============================================================

/-- Finite θ-native kernel:
    Ξ_{θ,P}(s) = Σ_{p ≤ P, p prime} a_p · (φ(p)^(s-θ) + φ(p)^(-(s-θ))). -/
def XiThetaFinite (P : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ primesUpTo P,
    (thetaCoeff p : ℂ) *
      ((↑(phiPrime p) : ℂ) ^ (s - ↑theta) +
       (↑(phiPrime p) : ℂ) ^ (-(s - ↑theta)))

-- ============================================================
-- SECTION 3. CRITICAL-LINE SUM AND ITS DERIVATIVE
-- ============================================================

/-- Critical-line trigonometric sum:
    C_P(t) = Σ_{p ≤ P, p prime} a_p · cos(t · u_p). -/
def criticalLineSum (P : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo P,
    thetaCoeff p * Real.cos (t * primeLogFreq p)

/-- Derivative of the critical-line sum:
    C_P'(t) = -Σ_{p ≤ P, p prime} a_p · u_p · sin(t · u_p). -/
def criticalLineSumDeriv (P : ℕ) (t : ℝ) : ℝ :=
  -(∑ p ∈ primesUpTo P,
    thetaCoeff p * primeLogFreq p * Real.sin (t * primeLogFreq p))

-- ============================================================
-- SECTION 4. BASIC THETA FACTS
-- ============================================================

/-- sin(θ) = 1/2, since θ = arcsin(1/2). -/
theorem sin_theta_eq : Real.sin theta = 1 / 2 := by
  convert Real.sin_arcsin _ _ <;> norm_num

/-- θ = π/6. -/
theorem theta_eq_pi_div_six : theta = Real.pi / 6 := by
  unfold theta
  rw [Real.arcsin_eq_of_sin_eq] <;> norm_num [Real.sin_pi_div_six]
  · ring_nf; norm_num; constructor <;> linarith [Real.pi_pos]

/-- τ = 6θ = π. -/
theorem tauAngle_eq_pi : tauAngle = Real.pi := by
  unfold tauAngle; rw [theta_eq_pi_div_six]; ring

/-- 2θ = π/3. -/
theorem doubleTheta_eq : doubleTheta = Real.pi / 3 := by
  unfold doubleTheta; rw [theta_eq_pi_div_six]; ring

-- ============================================================
-- SECTION 5. SYMMETRY OF THE FINITE KERNEL
-- ============================================================

/-- The finite kernel is symmetric about the critical line Re(s) = θ:
    Ξ_{θ,P}(s) = Ξ_{θ,P}(2θ - s).

This follows because replacing s with 2θ - s sends the exponent (s - θ) to -(s - θ),
which simply swaps the two complex power terms in each summand. -/
theorem XiThetaFinite_symm (P : ℕ) (s : ℂ) :
    XiThetaFinite P s = XiThetaFinite P (2 * ↑theta - s) := by
  unfold XiThetaFinite
  grind

-- ============================================================
-- SECTION 6. DERIVATIVE FORMULA
-- ============================================================

/-- The derivative of the critical-line sum satisfies:
    C_P'(t) = -Σ a_p · u_p · sin(t · u_p).

Each summand t ↦ a_p cos(t u_p) is differentiable with derivative -a_p u_p sin(t u_p)
by the chain rule, and the derivative of a finite sum is the sum of derivatives. -/
theorem criticalLineSum_deriv_formula (P : ℕ) (t : ℝ) :
    HasDerivAt (criticalLineSum P) (criticalLineSumDeriv P t) t := by
  have h : HasDerivAt
      (fun t => ∑ p ∈ primesUpTo P, thetaCoeff p * Real.cos (t * primeLogFreq p))
      (∑ p ∈ primesUpTo P, thetaCoeff p * (-primeLogFreq p) * Real.sin (t * primeLogFreq p)) t := by
    convert HasDerivAt.sum fun p _ =>
      HasDerivAt.const_mul (thetaCoeff p) (HasDerivAt.cos (hasDerivAt_mul_const (primeLogFreq p)))
      using 1
    · exact funext fun _ => by rw [Finset.sum_apply]
    · exact Finset.sum_congr rfl fun _ _ => by ring
  convert h using 1
  unfold criticalLineSumDeriv
  simp [mul_assoc, mul_comm]

end
