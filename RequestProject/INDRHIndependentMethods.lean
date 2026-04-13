/-
# Independent Methods (Unconditional)

Definitions and lemmas for the prime harmonic system at π/3
that require no analytic hypothesis (no RH/GRH).
-/

import Mathlib

open Real BigOperators

noncomputable section

/-! ## Core Definitions -/

/-- The prime harmonic phase at π/3: e^{ipπ/3}. -/
def primeHarmonicPiThird (p : ℕ) : ℂ :=
  Complex.exp (↑(↑p * Real.pi / 3) * Complex.I)

/-- The mod-3 Dirichlet character χ₃:
    χ₃(n) = 1  if n ≡ 1 mod 3,
    χ₃(n) = -1 if n ≡ 2 mod 3,
    χ₃(n) = 0  if n ≡ 0 mod 3. -/
def chi3ind (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1
  else if n % 3 = 2 then -1
  else 0

/-! ## Mod-6 Structure of Primes -/

/-- Every prime p ≥ 5 satisfies p ≡ 1 or 5 mod 6. -/
theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := by
    intro h; have := hp.eq_one_or_self_of_dvd 2 h
    omega
  have h3 : ¬ (3 ∣ p) := by
    intro h; have := hp.eq_one_or_self_of_dvd 3 h
    omega
  omega

/-! ## Trigonometric Evaluations -/

/-- cos(nπ/3) = 1/2 when n ≡ 1 mod 6. -/
theorem cos_prime_pi_div_three_of_mod_one (p : ℕ) (h : p % 6 = 1) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (by omega : (p - 1) % 6 = 0)
  have hp_eq : p = 6 * k + 1 := by omega
  rw [hp_eq]; push_cast
  have : (6 * (k : ℝ) + 1) * π / 3 = π / 3 + ↑(k : ℤ) * (2 * π) := by push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi]
  exact Real.cos_pi_div_three

/-- sin(nπ/3) = √3/2 when n ≡ 1 mod 6. -/
theorem sin_prime_pi_div_three_of_mod_one (p : ℕ) (h : p % 6 = 1) :
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (by omega : (p - 1) % 6 = 0)
  have hp_eq : p = 6 * k + 1 := by omega
  rw [hp_eq]; push_cast
  have : (6 * (k : ℝ) + 1) * π / 3 = π / 3 + ↑(k : ℤ) * (2 * π) := by push_cast; ring
  rw [this, Real.sin_add_int_mul_two_pi]
  exact Real.sin_pi_div_three

/-- cos(nπ/3) = 1/2 when n ≡ 5 mod 6. -/
theorem cos_prime_pi_div_three_of_mod_five (p : ℕ) (h : p % 6 = 5) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (by omega : (p - 5) % 6 = 0)
  have hp_eq : p = 6 * k + 5 := by omega
  rw [hp_eq]; push_cast
  have : (6 * (k : ℝ) + 5) * π / 3 = -(π / 3) + ↑((k : ℤ) + 1) * (2 * π) := by
    push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  exact Real.cos_pi_div_three

/-- sin(nπ/3) = -(√3/2) when n ≡ 5 mod 6. -/
theorem sin_prime_pi_div_three_of_mod_five (p : ℕ) (h : p % 6 = 5) :
    Real.sin (↑p * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (by omega : (p - 5) % 6 = 0)
  have hp_eq : p = 6 * k + 5 := by omega
  rw [hp_eq]; push_cast
  have : (6 * (k : ℝ) + 5) * π / 3 = -(π / 3) + ↑((k : ℤ) + 1) * (2 * π) := by
    push_cast; ring
  rw [this, Real.sin_add_int_mul_two_pi, Real.sin_neg, Real.sin_pi_div_three]

/-- cos(pπ/3) = 1/2 for all primes p ≥ 5. -/
theorem cos_prime_pi_div_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
  rcases prime_mod_six p hp hp5 with h | h
  · exact cos_prime_pi_div_three_of_mod_one p h
  · exact cos_prime_pi_div_three_of_mod_five p h

/-- χ₃(p) = 1 when p ≡ 1 mod 6. -/
theorem chi3_eq_one_of_mod_six_oneind (p : ℕ) (h : p % 6 = 1) :
    chi3ind p = 1 := by
  simp only [chi3ind]
  have : p % 3 = 1 := by omega
  simp [this]

/-- χ₃(p) = -1 when p ≡ 5 mod 6. -/
theorem chi3_eq_neg_one_of_mod_six_fiveind (p : ℕ) (h : p % 6 = 5) :
    chi3ind p = -1 := by
  simp only [chi3ind]
  have h1 : p % 3 = 2 := by omega
  have h2 : p % 3 ≠ 1 := by omega
  simp [h1]

/-- sin(pπ/3) = (√3/2)·χ₃(p) for all primes p ≥ 5. -/
theorem sin_prime_pi_div_three_eq_chi3ind (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 * (chi3ind p : ℝ) := by
  rcases prime_mod_six p hp hp5 with h | h
  · rw [sin_prime_pi_div_three_of_mod_one p h, chi3_eq_one_of_mod_six_oneind p h]
    simp
  · rw [sin_prime_pi_div_three_of_mod_five p h, chi3_eq_neg_one_of_mod_six_fiveind p h]
    simp

/-- The partial sum of Re(Q) over primes in [5,N] equals (1/2)·(number of such primes). -/
theorem real_part_harmonic_sum (N : ℕ) (_hN : 5 ≤ N) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.cos (↑p * Real.pi / 3))
    = (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card := by
  rw [Finset.sum_eq_card_nsmul (b := (1/2 : ℝ))]
  · simp [mul_comm]
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact cos_prime_pi_div_three p hp.2.1 hp.2.2

/-- The partial sum of Im(Q) equals (√3/2)·∑χ₃(p). -/
theorem imaginary_part_harmonic_sum_eq_chi3_sumind (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.sin (↑p * Real.pi / 3))
    = Real.sqrt 3 / 2 * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => (chi3ind p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact sin_prime_pi_div_three_eq_chi3ind p hp.2.1 hp.2.2

end
