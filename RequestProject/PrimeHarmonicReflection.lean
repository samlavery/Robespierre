import Mathlib

/-!
# Prime Harmonics Are Not Invariant Under Reflection for Off-Line Zeros

## Mathematical Context

The explicit formula for the prime counting function (von Mangoldt's formula) expresses
the Chebyshev function ψ(x) as a sum over non-trivial zeros ρ of the Riemann zeta function:

  ψ(x) = x - ∑_ρ x^ρ/ρ - log(2π) - (1/2)log(1 - x⁻²)

Each term x^ρ/ρ is called a **prime harmonic**. The critical line reflection is the map
ρ ↦ 1 - ρ̄ (equivalently σ + it ↦ (1-σ) + it), which maps the critical strip symmetrically
about the line Re(s) = 1/2.

## Main Result

We prove unconditionally that for **any** complex number s with Re(s) ≠ 1/2,
the prime harmonic x^s is not invariant under the critical line reflection s ↦ 1 - s̄.
Specifically, ‖x^s‖ ≠ ‖x^(1 - s̄)‖ for x > 1.

This is because ‖x^s‖ = x^(Re s) and ‖x^(1-s̄)‖ = x^(1 - Re s), and these differ
when Re(s) ≠ 1/2 and x > 1.

This shows that if any zero of zeta were to lie off the critical line, its contribution
to the prime counting function would necessarily break the reflection symmetry of the
prime harmonics — the term x^ρ/ρ and its reflected partner x^(1-ρ̄)/(1-ρ̄) would have
different magnitudes.
-/

open ComplexConjugate

/-- The real part of the critical-line reflection 1 - conj(s) equals 1 - Re(s). -/
lemma re_one_sub_conj (s : ℂ) : (1 - conj s).re = 1 - s.re := by
  simp [Complex.conj_re, Complex.sub_re, Complex.one_re]

/-- For x > 1 and σ₁ ≠ σ₂, x ^ σ₁ ≠ x ^ σ₂ as real powers. -/
lemma rpow_ne_rpow_of_ne {x : ℝ} (hx : 1 < x) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≠ σ₂) :
    x ^ σ₁ ≠ x ^ σ₂ := by
  norm_num [Real.rpow_def_of_pos (zero_lt_one.trans hx), hσ]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Main Theorem**: For any complex number s with Re(s) ≠ 1/2 and any real x > 1,
the norm of the prime harmonic x^s differs from that of its
critical-line reflection x^(1 - conj(s)). In particular, x^s ≠ x^(1 - conj(s)),
so the prime harmonics are not invariant under the reflection. -/
theorem prime_harmonic_not_reflection_invariant
    (s : ℂ) (hs : s.re ≠ 1 / 2) (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ s‖ ≠ ‖(x : ℂ) ^ (1 - conj s)‖ := by
  contrapose! hs
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)] at hs
  grind +suggestions

/-- Corollary: the prime harmonics themselves are not equal. -/
theorem prime_harmonic_ne_of_off_line
    (s : ℂ) (hs : s.re ≠ 1 / 2) (x : ℝ) (hx : 1 < x) :
    (x : ℂ) ^ s ≠ (x : ℂ) ^ (1 - conj s) := by
  intro h_eq
  exact prime_harmonic_not_reflection_invariant s hs x hx (congrArg (‖·‖) h_eq)

/-- For any complex s and real x > 1, the ratio of the prime harmonic magnitudes
‖x^s‖/‖x^(1-s̄)‖ = x^(2·Re(s) - 1). This quantifies the asymmetry. -/
theorem prime_harmonic_magnitude_ratio
    (s : ℂ) (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ s‖ / ‖(x : ℂ) ^ (1 - conj s)‖
      = (x : ℝ) ^ (2 * s.re - 1) := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx) s
  have := Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx) (1 - (starRingEnd ℂ) s)
  simp_all +decide [Real.rpow_sub (zero_lt_one.trans hx)]; ring_nf; norm_num;
  rw [mul_two, Real.rpow_add] <;> ring_nf; linarith

/-- The magnitude ratio is not equal to 1 when Re(s) ≠ 1/2 and x > 1. -/
theorem magnitude_ratio_ne_one
    (s : ℂ) (hs : s.re ≠ 1 / 2) (x : ℝ) (hx : 1 < x) :
    (x : ℝ) ^ (2 * s.re - 1) ≠ 1 := by
  rw [Real.rpow_def_of_pos] <;> norm_num <;> try linarith
  exact ⟨⟨by linarith, by linarith, by linarith⟩, by contrapose! hs; linarith⟩
