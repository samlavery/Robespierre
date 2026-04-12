/-
# Prime-Indexed Harmonics at π/3: Character-Theoretic Decomposition

## Overview

For every prime p ≥ 5, the complex exponential e^{iπp/3} admits an exact
orthogonal decomposition into a principal (main-term) piece and a
nonprincipal (oscillatory/error) piece tied to the nontrivial Dirichlet
character χ₃ mod 3:

    e^{iπp/3} = 1/2 + i(√3/2) · χ₃(p)

where χ₃ is defined by χ₃(n) = +1 if n ≡ 1 mod 3, −1 if n ≡ 2 mod 3, 0 if 3 ∣ n.

This identity is a character-Fourier expansion: the two values e^{iπ/3} and e^{5iπ/3}
that arise from the mod-6 residue classes of primes (≡ 1 or 5 mod 6) are decomposed
into a constant average (the principal-character contribution 1/2) and a signed
fluctuation (the nonprincipal-character contribution i√3/2 · χ₃(p)).

### Structural content

- **Real part** (= 1/2): This is the principal-character main term. It is rigid,
  unconditional, and independent of the residue class of p. It is the analogue of
  the main term in the Prime Number Theorem.

- **Imaginary part** (= ±√3/2): This is the nonprincipal-character error channel.
  Its sign is exactly χ₃(p) and encodes the 1-vs-5-mod-6 prime race. Its partial
  sums ∑ χ₃(p) are controlled by the zeros of L(s, χ₃), and under GRH these sums
  are O(√N log N). This is the structural bridge to PNT-in-arithmetic-progressions
  style error theory: the imaginary part of ∑ e^{iπp/3} is literally a character
  sum over primes, and its growth rate is governed by the analytic properties of
  L(s, χ₃).

### Von Mangoldt weighting

Multiplying by Λ(p) gives the weighted version relevant to ψ-function analogues:

    Λ(p) · e^{iπp/3} = (1/2) Λ(p) + i(√3/2) Λ(p) χ₃(p)

The sums of these terms decompose analogously.

### What is implicit but now surfaced

1. The entire oscillatory structure of ∑ e^{iπp/3} lives in a single
   Dirichlet character sum. There is no further harmonic content.

2. The "real part is 1/2" theorem is not merely a trigonometric identity —
   it is the statement that the principal-character contribution is exact and
   unconditional. This is the analogue of π(x) ~ x/log x.

3. The imaginary part is not "noise" — it is a perfectly structured object
   whose growth rate is equivalent to the error term in π(x; 3, 1) − π(x; 3, 2).

4. The decomposition is orthogonal in the character-theoretic sense: the real
   and imaginary parts are projections onto the principal and nonprincipal
   character subspaces of functions on (ℤ/3ℤ)×.
-/

import Mathlib

open Nat Finset BigOperators

noncomputable section

/-! ## §1. Prime Residue Classification mod 6

Every prime p ≥ 5 is congruent to 1 or 5 modulo 6. This is because:
- p ≡ 0 mod 6 ⟹ 6 ∣ p, impossible for prime p ≥ 5
- p ≡ 2 or 4 mod 6 ⟹ 2 ∣ p, impossible for prime p ≥ 5
- p ≡ 3 mod 6 ⟹ 3 ∣ p, impossible for prime p ≥ 5
-/

/-- Every prime ≥ 5 is congruent to 1 or 5 modulo 6. -/
theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 ≠ 0 :=
    fun h => (hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h)).elim (by omega) (by omega)
  have h3 : p % 3 ≠ 0 :=
    fun h => (hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)).elim (by omega) (by omega)
  omega

/-! ## §2. The Nontrivial Dirichlet Character mod 3

We define χ₃ : ℕ → ℤ, the unique nontrivial Dirichlet character modulo 3.
This is the quadratic (Legendre-like) character:
  χ₃(n) = +1 if n ≡ 1 mod 3
  χ₃(n) = −1 if n ≡ 2 mod 3
  χ₃(n) =  0 if 3 ∣ n

For primes p ≥ 5, we always have χ₃(p) ∈ {+1, −1}, and the value encodes
exactly the 1-vs-5-mod-6 prime split.
-/

/-- The nontrivial Dirichlet character mod 3. -/
def chi3 (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1
  else if n % 3 = 2 then -1
  else 0

/-- χ₃(p) = 1 when p ≡ 1 mod 6. -/
theorem chi3_eq_one_of_mod_six_one (p : ℕ) (h : p % 6 = 1) : chi3 p = 1 := by
  simp [chi3]; omega

/-- χ₃(p) = −1 when p ≡ 5 mod 6. -/
theorem chi3_eq_neg_one_of_mod_six_five (p : ℕ) (h : p % 6 = 5) : chi3 p = -1 := by
  simp [chi3]; omega

/-- For a prime p ≥ 5, χ₃(p) is ±1. -/
theorem chi3_prime_sq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    chi3 p = 1 ∨ chi3 p = -1 := by
  rcases prime_mod_six p hp hp5 with h | h
  · exact Or.inl (chi3_eq_one_of_mod_six_one p h)
  · exact Or.inr (chi3_eq_neg_one_of_mod_six_five p h)

/-- χ₃(p)² = 1 for primes p ≥ 5. -/
theorem chi3_sq_eq_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (chi3 p) ^ 2 = 1 := by
  rcases chi3_prime_sq p hp hp5 with h | h <;> simp [h]

/-! ## §3. Trigonometric Foundations

The basic trigonometric values cos(pπ/3) and sin(pπ/3) for primes p ≥ 5,
decomposed by residue class.
-/

/-- cos(5π/3) = 1/2, a useful intermediate fact. -/
theorem cos_five_pi_div_three : Real.cos (5 * Real.pi / 3) = 1 / 2 := by
  have : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_two_pi_sub, Real.cos_pi_div_three]

/-- If p ≡ 1 mod 6, then cos(p·π/3) = 1/2. -/
theorem cos_prime_pi_div_three_of_mod_one (p : ℕ) (h : p % 6 = 1) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
      rw [ ← Nat.mod_add_div p 6, h ];
      rw [ ← Real.cos_pi_div_three ] ; ring;
      convert Real.cos_periodic.int_mul ( p / 6 ) _ using 2 ; push_cast ; ring;
      norm_num [ add_comm, mul_comm, Int.cast_div, show 6 ∣ p - 1 from Nat.dvd_of_mod_eq_zero ( by omega ) ];
      norm_cast

/-- If p ≡ 5 mod 6, then cos(p·π/3) = 1/2. -/
theorem cos_prime_pi_div_three_of_mod_five (p : ℕ) (h : p % 6 = 5) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
      convert Real.cos_pi_div_three using 1 ; rw [ ← Nat.div_add_mod p 6, h ] ; push_cast ; ring;
      rw [ ← Real.cos_sub_int_mul_two_pi _ ( p / 6 ) ] ; ring;
      convert Real.cos_two_pi_sub _ using 2 ; ring;
      norm_cast;
      ring

/-- **Real-part rigidity**: For any prime p ≥ 5, cos(p·π/3) = 1/2.
This is the principal-character main term — unconditional and uniform. -/
theorem cos_prime_pi_div_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
  rcases prime_mod_six p hp hp5 with h | h
  · exact cos_prime_pi_div_three_of_mod_one p h
  · exact cos_prime_pi_div_three_of_mod_five p h

/-- sin(5π/3) = -√3/2. -/
theorem sin_five_pi_div_three : Real.sin (5 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  have : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_two_pi_sub, Real.sin_pi_div_three]

/-- If p ≡ 1 mod 6, then sin(p·π/3) = √3/2. -/
theorem sin_prime_pi_div_three_of_mod_one (p : ℕ) (h : p % 6 = 1) :
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 := by
      convert Real.sin_pi_div_three using 1 ; rw [ ← Nat.div_add_mod p 6, h ] ; push_cast ; ring;
      convert Real.sin_periodic.int_mul ( p / 6 ) _ using 2 ; ring;
      norm_num [ add_comm, mul_comm, Int.cast_div, show 6 ∣ p - 1 from Nat.dvd_of_mod_eq_zero ( by omega ) ];
      norm_cast

/-- If p ≡ 5 mod 6, then sin(p·π/3) = -(√3/2). -/
theorem sin_prime_pi_div_three_of_mod_five (p : ℕ) (h : p % 6 = 5) :
    Real.sin (↑p * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
      rw [ ← Nat.mod_add_div p 6, h ] ; norm_num ; ring_nf ; norm_num [ mul_div ];
      rw [ show Real.pi * 5 / 3 = 2 * Real.pi - Real.pi / 3 by ring ] ; norm_num [ mul_two, Real.sin_add, Real.sin_sub ] ; ring;
      norm_num [ mul_assoc, mul_comm Real.pi ]

/-! ## §4. The Core Character-Theoretic Identity

We prove the fundamental decomposition:

  sin(pπ/3) = (√3/2) · χ₃(p)

for primes p ≥ 5. Combined with cos(pπ/3) = 1/2, this gives the complex identity:

  e^{iπp/3} = 1/2 + i(√3/2) · χ₃(p)

The real part is the principal-character piece (constant, unconditional).
The imaginary part is the nonprincipal-character piece (signed, fluctuating).
-/

/-- **Imaginary part = character value**: sin(pπ/3) = (√3/2) · χ₃(p)
for any prime p ≥ 5. This connects the oscillatory part of the harmonic
to the Dirichlet character χ₃. -/
theorem sin_prime_pi_div_three_eq_chi3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 * (chi3 p : ℝ) := by
  rcases prime_mod_six p hp hp5 with h | h
  · rw [sin_prime_pi_div_three_of_mod_one p h, chi3_eq_one_of_mod_six_one p h]; simp
  · rw [sin_prime_pi_div_three_of_mod_five p h, chi3_eq_neg_one_of_mod_six_five p h]; simp

/-- **Core decomposition (real and imaginary parts)**: For any prime p ≥ 5,
cos(pπ/3) = 1/2 and sin(pπ/3) = (√3/2)·χ₃(p). -/
theorem prime_harmonic_character_decomposition (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 ∧
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 * (chi3 p : ℝ) :=
  ⟨cos_prime_pi_div_three p hp hp5, sin_prime_pi_div_three_eq_chi3 p hp hp5⟩

/-- The prime harmonic as a complex number: a Lean-friendly packaging. -/
def primeHarmonicPiThird (p : ℕ) : ℂ :=
  Complex.exp (Complex.I * (↑(↑p * Real.pi / 3)))

/-
**Complex decomposition identity**: For any prime p ≥ 5,
  e^{iπp/3} = 1/2 + i · (√3/2) · χ₃(p).
This is the exact character-Fourier expansion.
-/
theorem prime_harmonic_complex_character_decomposition (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    primeHarmonicPiThird p =
    (1/2 : ℝ) + Complex.I * ((Real.sqrt 3 / 2 * (chi3 p : ℝ)) : ℝ) := by
      unfold primeHarmonicPiThird; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;
      exact?

/-! ## §5. Principal-Character Piece: Real-Part Rigidity

The real part cos(pπ/3) = 1/2 for all primes p ≥ 5 is the principal-character
contribution. Its sum over primes is exactly (1/2) · #{primes in [5,N]}.

This is unconditional and mirrors the main term in PNT: the principal character
χ₀ contributes a deterministic, non-oscillatory main term to every character sum.
-/

/-- **Principal-character sum** (real part): The sum of cos(pπ/3) over primes
p ∈ [5,N] equals (1/2)·#{primes in [5,N]}. Unconditional. -/
theorem real_part_harmonic_sum (N : ℕ) (hN : 5 ≤ N) :
    (((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.cos (↑p * Real.pi / 3))) =
    (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card := by
      rw [ Finset.sum_eq_card_nsmul ];
      any_goals intros; rw [ mul_comm ];
      rw [ nsmul_eq_mul ];
      rw [ mul_comm, cos_prime_pi_div_three ] <;> aesop

/-! ## §6. Nonprincipal-Character Piece: Imaginary Part as Character Sum

The imaginary part sin(pπ/3) = (√3/2)·χ₃(p) is the nonprincipal-character
contribution. Its partial sums are character sums ∑ χ₃(p) over primes,
whose growth is governed by the zeros of L(s, χ₃).

This is the residue-class fluctuation channel: it measures exactly how
unevenly primes distribute between the classes 1 mod 3 and 2 mod 3.
Under GRH for L(s, χ₃), these sums are O(√N log N).
-/

/-
**Nonprincipal-character sum** (imaginary part): The sum of sin(pπ/3) over
primes p ∈ [5,N] equals (√3/2) · ∑ χ₃(p).
-/
theorem imaginary_part_harmonic_sum_eq_chi3_sum (N : ℕ) :
    (((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.sin (↑p * Real.pi / 3))) =
    Real.sqrt 3 / 2 *
    (((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => (chi3 p : ℝ))) := by
        rw [ Finset.mul_sum, Finset.sum_congr rfl ];
        exact fun p hp => sin_prime_pi_div_three_eq_chi3 p ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hp |>.2.2 )

/-! ## §7. Summed Complex Decomposition

The full complex harmonic sum decomposes as:

  ∑_{5≤p≤N} e^{iπp/3} = (1/2)·#{primes in [5,N]} + i(√3/2)·∑_{5≤p≤N} χ₃(p)

This is the finite-sum version of the character-Fourier decomposition.
-/

/-
**Summed complex decomposition**: The sum of e^{iπp/3} over primes p ∈ [5,N]
decomposes into a principal (real, constant) term and a nonprincipal
(imaginary, character-sum) term.
-/
theorem prime_harmonic_sum_decomposition (N : ℕ) (hN : 5 ≤ N) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => primeHarmonicPiThird p) =
    (((1 : ℝ)/2 * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card : ℝ) : ℂ) +
    Complex.I * ((Real.sqrt 3 / 2 *
      ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
        (fun p => (chi3 p : ℝ)) : ℝ) : ℂ) := by
          convert Finset.sum_congr rfl fun x hx => prime_harmonic_complex_character_decomposition x ?_ ?_ using 1;
          · norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
            ring;
          · aesop;
          · aesop

/-! ## §8. Von Mangoldt Weighted Decomposition

The von Mangoldt function Λ(n) weights the Chebyshev function ψ(x) = ∑_{n≤x} Λ(n).
The weighted harmonic extraction at π/3 gives:

  Λ(p) · e^{iπp/3} = (1/2) Λ(p) + i(√3/2) Λ(p) χ₃(p)

This follows immediately from the pointwise identity by scalar multiplication.
-/

/-- **Von Mangoldt weighted pointwise decomposition**:
Λ(p) · e^{iπp/3} = (1/2)Λ(p) + i(√3/2)Λ(p)χ₃(p) for primes p ≥ 5. -/
theorem vonMangoldt_harmonic_character_decomposition (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (ArithmeticFunction.vonMangoldt p : ℝ) * Real.cos (↑p * Real.pi / 3) =
    (1/2 : ℝ) * ArithmeticFunction.vonMangoldt p ∧
    (ArithmeticFunction.vonMangoldt p : ℝ) * Real.sin (↑p * Real.pi / 3) =
    Real.sqrt 3 / 2 * ArithmeticFunction.vonMangoldt p * (chi3 p : ℝ) := by
  constructor
  · rw [cos_prime_pi_div_three p hp hp5]; ring
  · rw [sin_prime_pi_div_three_eq_chi3 p hp hp5]; ring

/-
**Von Mangoldt weighted sum decomposition** (real part):
∑ Λ(p)·cos(pπ/3) = (1/2)·∑ Λ(p) for primes p ∈ [5,N].
-/
theorem vonMangoldt_real_sum (N : ℕ) (hN : 5 ≤ N) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => ArithmeticFunction.vonMangoldt p * Real.cos (↑p * Real.pi / 3)) =
    (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => (ArithmeticFunction.vonMangoldt p : ℝ)) := by
        rw [ Finset.mul_sum _ _ _ ];
        exact Finset.sum_congr rfl fun x hx => by rw [ cos_prime_pi_div_three x ( by aesop ) ( by aesop ) ] ; ring;

/-
**Von Mangoldt weighted sum decomposition** (imaginary part):
∑ Λ(p)·sin(pπ/3) = (√3/2)·∑ Λ(p)·χ₃(p) for primes p ∈ [5,N].
-/
theorem vonMangoldt_imaginary_sum (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => ArithmeticFunction.vonMangoldt p * Real.sin (↑p * Real.pi / 3)) =
    Real.sqrt 3 / 2 * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => ArithmeticFunction.vonMangoldt p * (chi3 p : ℝ)) := by
        convert Finset.sum_congr rfl fun p hp => ?_ using 1;
        rw [ Finset.mul_sum _ _ _ ];
        rw [ sin_prime_pi_div_three_eq_chi3 p ( by aesop ) ( by aesop ) ] ; ring

/-! ## §9. Amplitude and Unit Modulus

For any prime p ≥ 5, |e^{iπp/3}| = 1 (unit amplitude). This is the
Pythagorean identity cos² + sin² = 1.
-/

/-- cos²(pπ/3) + sin²(pπ/3) = 1 for any prime p ≥ 5. -/
theorem amplitude_sq_prime_harmonic (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) ^ 2 + Real.sin (↑p * Real.pi / 3) ^ 2 = 1 := by
  rw [← Real.cos_sq_add_sin_sq (↑p * Real.pi / 3)]

/-- Alternative: verify (1/2)² + (√3/2)² = 1 concretely. -/
theorem amplitude_sq_prime_harmonic_concrete (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (1/2 : ℝ)^2 + (Real.sqrt 3/2)^2 = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [h3]

/-- Von Mangoldt amplitude: Λ(p)·|e^{ipπ/3}| = log(p) for primes p ≥ 5. -/
theorem vonMangoldt_harmonic_amplitude (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ArithmeticFunction.vonMangoldt p *
    Real.sqrt (Real.cos (↑p * Real.pi / 3) ^ 2 +
               Real.sin (↑p * Real.pi / 3) ^ 2) =
    Real.log p := by
      simp [ArithmeticFunction.vonMangoldt_apply_prime hp]

/-! ## §10. Complex Exponential Values

The exponential e^{iπ/3} has real part 1/2 and imaginary part √3/2.
-/

/-- e^{iπ/3} has real part 1/2. -/
theorem exp_i_pi_div_three_re :
    (Complex.exp (Complex.I * ↑(Real.pi / 3))).re = 1 / 2 := by
      norm_num [ Complex.exp_re ]

/-- e^{iπ/3} has imaginary part √3/2. -/
theorem exp_i_pi_div_three_im :
    (Complex.exp (Complex.I * ↑(Real.pi / 3))).im = Real.sqrt 3 / 2 := by
      norm_num [ Complex.exp_re, Complex.exp_im, Real.sin_pi_div_three ]

/-! ## §11. Conditional Results Under GRH

Under the Generalized Riemann Hypothesis for L(s, χ₃), the character sum
∑_{p≤N} χ₃(p) is O(√N log N). This controls the imaginary part of the
harmonic sum, which is proportional to this character sum.

This is the structural bridge to PNT-in-arithmetic-progressions error theory:
the bound on ∑ χ₃(p) is equivalent to the equidistribution of primes
between 1 mod 3 and 2 mod 3 (equivalently 1 and 5 mod 6) with optimal
error rate.
-/

/-- The Riemann Hypothesis: all non-trivial zeros of ζ(s) lie on Re(s) = 1/2. -/
def RH : Prop :=
  ∀ (s : ℂ), 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 → s.re = 1 / 2

/-- Count of primes ≤ N in a given residue class mod m. -/
def primeCountMod (N m r : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ n % m = r)).card

/-- GRH for characters mod 6: the prime race 1-vs-5 mod 6 has square-root fluctuation. -/
def GRH_mod6_balance : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    |(primeCountMod N 6 1 : ℤ) - (primeCountMod N 6 5 : ℤ)| ≤
      ⌈C * Real.sqrt N * Real.log N⌉₊

/-- Under GRH mod 6, the imaginary part of the harmonic sum (= the character sum
channel) is bounded by O(√N log N). This is equivalent to the character sum
∑ χ₃(p) being small: the nonprincipal piece has controlled growth. -/
theorem grh_implies_imaginary_bound (hGRH : GRH_mod6_balance) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
        (fun p => Real.sin (↑p * Real.pi / 3))| ≤
      C * Real.sqrt N * Real.log N := by
        -- From hGRH, obtain C₀ > 0 and the bound on |π₁(N) - π₅(N)| ≤ ⌈C₀√N log N⌉.
        obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ : ∃ C₀ : ℝ, C₀ > 0 ∧ ∀ N : ℕ, 2 ≤ N → |(primeCountMod N 6 1 : ℤ) - (primeCountMod N 6 5 : ℤ)| ≤ ⌈C₀ * Real.sqrt N * Real.log N⌉₊ := by
          exact?;
        -- The sin sum over primes p ≥ 5 splits: each p ≡ 1 mod 6 contributes √3/2 and each p ≡ 5 mod 6 contributes -√3/2.
        have h_split_sum : ∀ N : ℕ, (∑ p ∈ Finset.filter (fun p => p.Prime ∧ 5 ≤ p) (Finset.range (N + 1)), Real.sin ((p : ℝ) * Real.pi / 3)) = (Real.sqrt 3 / 2) * ((primeCountMod N 6 1 : ℤ) - (primeCountMod N 6 5 : ℤ)) := by
          intro N
          have h_sum_split : ∑ p ∈ Finset.filter (fun p => p.Prime ∧ 5 ≤ p) (Finset.range (N + 1)), Real.sin ((p : ℝ) * Real.pi / 3) = ∑ p ∈ Finset.filter (fun p => p.Prime ∧ 5 ≤ p ∧ p % 6 = 1) (Finset.range (N + 1)), (Real.sqrt 3 / 2) + ∑ p ∈ Finset.filter (fun p => p.Prime ∧ 5 ≤ p ∧ p % 6 = 5) (Finset.range (N + 1)), -(Real.sqrt 3 / 2) := by
            rw [ Finset.sum_filter, Finset.sum_filter, Finset.sum_filter ];
            rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
            intro x hx; split_ifs <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
            · convert sin_prime_pi_div_three_of_mod_one x ( by tauto ) using 1;
            · convert sin_prime_pi_div_three_of_mod_five x ( by tauto ) using 1;
            · have := Nat.Prime.eq_two_or_odd ( by tauto : Nat.Prime x ) ; ( have := Nat.dvd_of_mod_eq_zero ( show x % 3 = 0 from by omega ) ; rw [ Nat.dvd_prime ( by tauto ) ] at this ; aesop; );
          simp_all +decide [ Finset.sum_add_distrib, mul_comm ];
          unfold primeCountMod; ring;
          congr! 2;
          · congr! 2;
            exact congr_arg _ ( Finset.filter_congr fun x hx => by exact ⟨ fun hx' => ⟨ hx'.1, hx'.2.2 ⟩, fun hx' => ⟨ hx'.1, by contrapose! hx'; interval_cases x <;> trivial, hx'.2 ⟩ ⟩ );
          · congr! 2;
            exact congr_arg _ ( Finset.filter_congr fun x hx => by exact ⟨ fun hx' => ⟨ hx'.1, hx'.2.2 ⟩, fun hx' => ⟨ hx'.1, by contrapose! hx'; interval_cases x <;> trivial, hx'.2 ⟩ ⟩ );
        -- Therefore |sum| = (√3/2)|π₁(N) - π₅(N)| ≤ (√3/2)⌈C₀√N log N⌉ ≤ (√3/2)(C₀√N log N + 1).
        have h_bound : ∀ N : ℕ, 2 ≤ N → |(∑ p ∈ Finset.filter (fun p => p.Prime ∧ 5 ≤ p) (Finset.range (N + 1)), Real.sin ((p : ℝ) * Real.pi / 3))| ≤ (Real.sqrt 3 / 2) * (C₀ * Real.sqrt N * Real.log N + 1) := by
          -- Apply the bound from hC₀_bound to the split sum from h_split_sum.
          intros N hN
          rw [h_split_sum N]
          have h_abs : |(primeCountMod N 6 1 : ℤ) - (primeCountMod N 6 5 : ℤ)| ≤ C₀ * Real.sqrt N * Real.log N + 1 := by
            exact le_trans ( mod_cast hC₀_bound N hN ) ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt );
          rw [ abs_mul, abs_of_nonneg ( by positivity ) ] ; gcongr ; aesop;
        -- Choose $C$ such that $(\sqrt{3}/2)(C₀ + 1/\sqrt{N}\log N) \leq C$ for all $N \geq 2$.
        obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, 2 ≤ N → (Real.sqrt 3 / 2) * (C₀ + 1 / (Real.sqrt N * Real.log N)) ≤ C := by
          refine' ⟨ Real.sqrt 3 / 2 * ( C₀ + 1 / ( Real.sqrt 2 * Real.log 2 ) ), _, _ ⟩ <;> norm_num;
          · positivity;
          · intro N hN; gcongr <;> norm_cast;
        refine' ⟨ C, hC_pos, fun N hN => le_trans ( h_bound N hN ) _ ⟩;
        convert mul_le_mul_of_nonneg_right ( hC N hN ) ( show 0 ≤ Real.sqrt N * Real.log N by positivity ) using 1 ; ring;
        · norm_num [ add_comm, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( zero_lt_two.trans_le hN ) ) ), ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hN ) ) ];
        · ring

/-! ## §12. Structural Bridge to PNT-in-Progressions Error Theory

The decomposition proved above makes the following structural correspondence
explicit:

| Harmonic piece          | Character-theoretic role        | Growth behavior           |
|-------------------------|---------------------------------|---------------------------|
| Re: cos(pπ/3) = 1/2    | Principal char χ₀ contribution  | Exact, unconditional      |
| Im: sin(pπ/3) = ±√3/2  | Nonprincipal char χ₃ value      | Fluctuates, encodes race  |
| ∑ Re = (1/2)·π(N)      | Main term of PNT                | ~ N/(2 log N)             |
| ∑ Im = (√3/2)·∑χ₃(p)   | Error term / L-function channel | O(√N log N) under GRH     |

The imaginary part of ∑_{p≤N} e^{iπp/3} is literally a partial sum of a
Dirichlet character over primes. Its analytic properties (growth, sign changes,
distribution) are governed entirely by the zeros of L(s, χ₃). This is why:

1. The real-part rigidity theorem (§5) is the analogue of the unconditional
   main term in PNT.

2. The GRH bound on the imaginary part (§11) is not an ad hoc estimate — it is
   the direct consequence of zero-free regions for L(s, χ₃).

3. Any improvement to the error bound ∑ χ₃(p) would automatically improve the
   imaginary-part bound, and conversely. The two are the same object.

4. The full harmonic sum ∑ e^{iπp/3} is the superposition of exactly two
   character contributions, with no residual. This completeness is a consequence
   of φ(3) = 2 and the orthogonality of {χ₀, χ₃}.
-/

/-! ## §13. Master Theorem

We package the complete decomposition into a single theorem that records:
- The pointwise character decomposition (real and imaginary parts)
- The character-theoretic meaning (principal vs nonprincipal)
- The amplitude (unit modulus)
- The von Mangoldt weighting
- The summed decomposition (principal sum + character sum)
-/

/-
**Master theorem**: Complete character-theoretic decomposition of the prime
harmonic at π/3. For any prime p ≥ 5:

1. **Real part** (principal character, main term): cos(pπ/3) = 1/2
2. **Imaginary part** (nonprincipal character, error channel): sin(pπ/3) = (√3/2)·χ₃(p)
3. **Amplitude**: cos²(pπ/3) + sin²(pπ/3) = 1
4. **Von Mangoldt real part**: Λ(p)·cos(pπ/3) = (1/2)·Λ(p)
5. **Von Mangoldt imaginary part**: Λ(p)·sin(pπ/3) = (√3/2)·Λ(p)·χ₃(p)
6. **Character value**: χ₃(p) ∈ {+1, −1}

The real part is rigid and unconditional (principal-character piece).
The imaginary part is the residue-class fluctuation channel (nonprincipal piece),
whose partial sums are controlled by L(s, χ₃).
-/
theorem prime_harmonic_master (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    -- (1) Real part = principal character main term
    Real.cos (↑p * Real.pi / 3) = 1 / 2 ∧
    -- (2) Imaginary part = nonprincipal character error channel
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 * (chi3 p : ℝ) ∧
    -- (3) Unit amplitude
    Real.cos (↑p * Real.pi / 3) ^ 2 + Real.sin (↑p * Real.pi / 3) ^ 2 = 1 ∧
    -- (4) Von Mangoldt real part
    ArithmeticFunction.vonMangoldt p * Real.cos (↑p * Real.pi / 3) =
      (1/2 : ℝ) * ArithmeticFunction.vonMangoldt p ∧
    -- (5) Von Mangoldt imaginary part
    ArithmeticFunction.vonMangoldt p * Real.sin (↑p * Real.pi / 3) =
      Real.sqrt 3 / 2 * ArithmeticFunction.vonMangoldt p * (chi3 p : ℝ) ∧
    -- (6) Character value is ±1
    (chi3 p = 1 ∨ chi3 p = -1) := by
      exact ⟨ cos_prime_pi_div_three p hp hp5, sin_prime_pi_div_three_eq_chi3 p hp hp5, Real.cos_sq_add_sin_sq _, by rw [ cos_prime_pi_div_three p hp hp5, mul_comm ], by rw [ sin_prime_pi_div_three_eq_chi3 p hp hp5 ] ; ring, chi3_prime_sq p hp hp5 ⟩

/-- **Kept for backwards compatibility**: the original master theorem. -/
theorem prime_harmonic_at_pi_third_complete (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 ∧
    (Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 ∨
     Real.sin (↑p * Real.pi / 3) = -(Real.sqrt 3 / 2)) ∧
    Real.cos (↑p * Real.pi / 3) ^ 2 + Real.sin (↑p * Real.pi / 3) ^ 2 = 1 := by
  refine ⟨cos_prime_pi_div_three p hp hp5, ?_, ?_⟩
  · rcases prime_mod_six p hp hp5 with h | h
    · exact Or.inl (sin_prime_pi_div_three_of_mod_one p h)
    · exact Or.inr (sin_prime_pi_div_three_of_mod_five p h)
  · rw [← Real.cos_sq_add_sin_sq]

end