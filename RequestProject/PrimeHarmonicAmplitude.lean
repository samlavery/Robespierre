/-
# Minimum Amplitude of a Prime Harmonic

## Mathematical Background

The Euler product for the Riemann zeta function expresses ζ(s) = ∏_p (1 - p⁻ˢ)⁻¹.
Each prime p contributes a "prime harmonic" factor.

When we evaluate the amplitude of p^(-s) using "log Euler's formula" at θ = π/3,
we set s = e^{iπ/3} = cos(π/3) + i·sin(π/3) = 1/2 + i·√3/2.

The amplitude (norm) of p^(-s) for complex s is:
  ‖p^(-s)‖ = p^(-Re(s))

Since Re(e^{iπ/3}) = cos(π/3) = 1/2, we obtain:
  ‖p^(-e^{iπ/3})‖ = p^(-1/2) = 1/√p

This is the **minimum amplitude formula for a prime harmonic**: for a prime p,
measured at the Euler phase angle π/3, the amplitude is **1/√p**.
-/
import Mathlib

open Real Complex

noncomputable section

/-! ## Key fact: cos(π/3) = 1/2 -/

theorem cos_pi_div_three_eq : Real.cos (Real.pi / 3) = 1 / 2 :=
  Real.cos_pi_div_three

/-! ## The Euler phase at π/3

  Euler's formula gives e^{iπ/3} = cos(π/3) + i·sin(π/3).
  The real part is cos(π/3) = 1/2. -/

/-- The Euler phase s = e^{iπ/3} as a complex number -/
def eulerPhase : ℂ := Complex.exp (Complex.I * ↑(Real.pi / 3))

/-
The real part of e^{iπ/3} is cos(π/3) = 1/2
-/
theorem re_eulerPhase : eulerPhase.re = 1 / 2 := by
  unfold eulerPhase; norm_num [ Complex.exp_re, Real.cos_pi_div_three ] ;

/-! ## Amplitude of the prime harmonic

  For a prime p, the prime harmonic at phase s is p^(-s).
  Its amplitude (norm) is p^(-Re(s)). -/

/-
The amplitude of p^(-s) for positive real p equals p^(-Re(s)).
-/
theorem norm_prime_cpow_neg {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    ‖(↑p : ℂ) ^ (-s)‖ = (↑p : ℝ) ^ (-s.re) := by
      rw [ Complex.norm_cpow_of_imp ] <;> aesop

/-- **Minimum Amplitude Formula**: For a prime p, the amplitude of the prime harmonic
    p^(-e^{iπ/3}) equals p^(-1/2) = 1/√p. -/
theorem min_amplitude_prime_harmonic {p : ℕ} (hp : Nat.Prime p) :
    ‖(↑p : ℂ) ^ (-eulerPhase)‖ = (↑p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_prime_cpow_neg hp]
  congr 1
  show -eulerPhase.re = -(1 / 2)
  rw [re_eulerPhase]

/-
Alternative form: the minimum amplitude equals 1/√p.
-/
theorem min_amplitude_eq_inv_sqrt {p : ℕ} (hp : Nat.Prime p) :
    ‖(↑p : ℂ) ^ (-eulerPhase)‖ = 1 / Real.sqrt p := by
      rw [ min_amplitude_prime_harmonic hp, Real.sqrt_eq_rpow, one_div, Real.rpow_neg ] ; norm_num ; linarith [ hp.one_lt ]

end