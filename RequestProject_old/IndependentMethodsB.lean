/-
# Independent (Unconditional) Methods

Definitions and theorems that do not rely on RH or GRH.
Includes: chi3, primeHarmonicPiThird, mod-6 trig identities, partial sum results.
-/

import Mathlib

open Real BigOperators Complex

noncomputable section

/-! ## Dirichlet character χ₃ mod 3 -/

/-- The Dirichlet character χ₃ mod 3. -/
def chi3 (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1
  else if n % 3 = 2 then -1
  else 0

theorem chi3_eq_one_of_mod_six_one (p : ℕ) (h : p % 6 = 1) : chi3 p = 1 := by
  unfold chi3; simp [Nat.mod_def]; omega

theorem chi3_eq_neg_one_of_mod_six_five (p : ℕ) (h : p % 6 = 5) : chi3 p = -1 := by
  unfold chi3; simp [Nat.mod_def]; omega

/-! ## Prime mod 6 classification -/

theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬(2 ∣ p) := by intro h; have := hp.eq_one_or_self_of_dvd 2 h; omega
  have h3 : ¬(3 ∣ p) := by intro h; have := hp.eq_one_or_self_of_dvd 3 h; omega
  omega

/-! ## Trigonometric identities at π/3 -/

theorem cos_prime_pi_div_three_of_mod_one (n : ℕ) (h : n % 6 = 1) :
    Real.cos (↑n * Real.pi / 3) = 1 / 2 := by
      rw [ ← Nat.mod_add_div n 6, h ] ; norm_num ; ring;
      norm_num [ mul_div, mul_assoc, mul_comm Real.pi, Real.cos_add ];
      norm_num [ show 1 / 3 * Real.pi = Real.pi / 3 by ring, show ( n / 6 : ℕ ) * ( 2 * Real.pi ) = ( n / 6 : ℕ ) * Real.pi + ( n / 6 : ℕ ) * Real.pi by ring, Real.sin_add ]

theorem sin_prime_pi_div_three_of_mod_one (n : ℕ) (h : n % 6 = 1) :
    Real.sin (↑n * Real.pi / 3) = Real.sqrt 3 / 2 := by
      -- Write n as 6k + 1 for some integer k.
      obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 1 := by
        exact ⟨ n / 6, by rw [ ← h, Nat.div_add_mod ] ⟩;
      convert Real.sin_pi_div_three using 1 ; push_cast ; ring;
      convert Real.sin_periodic.int_mul k _ using 2 ; push_cast ; ring

theorem cos_prime_pi_div_three_of_mod_five (n : ℕ) (h : n % 6 = 5) :
    Real.cos (↑n * Real.pi / 3) = 1 / 2 := by
      rw [ ← Nat.mod_add_div n 6, h ] ; ring ; norm_num [ mul_div, mul_assoc, mul_comm Real.pi _, Real.cos_two_mul ] ;
      rw [ ← Real.cos_two_pi_sub ] ; ring_nf ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ];
      rw [ show 1 / 3 * Real.pi = Real.pi / 3 by ring, Real.cos_pi_div_three ]

theorem sin_prime_pi_div_three_of_mod_five (n : ℕ) (h : n % 6 = 5) :
    Real.sin (↑n * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
      rw [ ← Nat.div_add_mod n 6, h ] ; norm_num ; ring;
      norm_num [ ( by ring : Real.pi * ( 5 / 3 ) = 2 * Real.pi - Real.pi / 3 ), Real.sin_add, mul_assoc, mul_comm Real.pi ] ; ring;
      norm_num [ mul_two, Real.sin_add ]

theorem cos_prime_pi_div_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
  rcases prime_mod_six p hp hp5 with h | h
  · exact cos_prime_pi_div_three_of_mod_one p h
  · exact cos_prime_pi_div_three_of_mod_five p h

theorem sin_prime_pi_div_three_eq_chi3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Real.sin (↑p * Real.pi / 3) = Real.sqrt 3 / 2 * (chi3 p : ℝ) := by
  rcases prime_mod_six p hp hp5 with h | h
  · rw [sin_prime_pi_div_three_of_mod_one p h, chi3_eq_one_of_mod_six_one p h]; simp
  · rw [sin_prime_pi_div_three_of_mod_five p h, chi3_eq_neg_one_of_mod_six_five p h]
    push_cast; ring

/-! ## The prime harmonic at π/3 -/

def primeHarmonicPiThird (p : ℕ) : ℂ :=
  Complex.exp (↑(↑p * Real.pi / 3) * Complex.I)

/-! ## Partial sum results -/

theorem real_part_harmonic_sum (N : ℕ) (hN : 5 ≤ N) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.cos (↑p * Real.pi / 3)) =
    (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card := by
  rw [Finset.sum_eq_card_nsmul (b := (1/2 : ℝ))]
  · simp [nsmul_eq_mul]; ring
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact cos_prime_pi_div_three p hp.2.1 hp.2.2

theorem imaginary_part_harmonic_sum_eq_chi3_sum (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.sin (↑p * Real.pi / 3)) =
    Real.sqrt 3 / 2 * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => (chi3 p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp; simp only [Finset.mem_filter] at hp
  exact sin_prime_pi_div_three_eq_chi3 p hp.2.1 hp.2.2

end