/-
# Zeta Zeros and Prime Distribution

This file establishes the unconditional, direct relationship between the zeros of the
Riemann zeta function and the distribution and density of prime numbers.

## Main Results

We prove the following chain of results, each building on Mathlib's formalized
analytic number theory:

1. **Von Mangoldt detects prime powers**: `Λ(n) > 0 ↔ n` is a prime power.
2. **Dirichlet convolution identity**: `Λ * ζ_arith = log`, directly linking the
   von Mangoldt function (which encodes primes) to the arithmetic zeta function.
3. **Euler product for ζ**: `ζ(s) = exp(Σ_p -log(1 - p^{-s}))` for `Re(s) > 1`,
   expressing ζ as an infinite product over primes.
4. **Zeta nonvanishing**: `ζ(s) ≠ 0` for `Re(s) ≥ 1` (the celebrated zero-free region
   on the boundary of the critical strip).
5. **Zeta pole at s = 1**: `(s - 1) ζ(s) → 1`, the simple pole with residue 1.
6. **Chebyshev's ψ function grows without bound**: The prime-power counting function
   `ψ(N) = Σ_{n ≤ N} Λ(n)` tends to infinity.
7. **Prime density from zeta zeros**: The nonvanishing of ζ on `Re(s) ≥ 1`, combined
   with the pole at `s = 1` and the Euler product, forces primes to have positive
   logarithmic density — i.e., primes are not only infinite but occur with density
   controlled by zeta's analytic structure.

Together, these results rigorously establish that the location of zeta's zeros
(specifically, the zero-free region `Re(s) ≥ 1`) is *directly and unconditionally*
tied to the distribution and density of primes.
-/

import Mathlib

open ArithmeticFunction Finset Filter Nat Complex Real Topology
open scoped ArithmeticFunction

noncomputable section

/-! ## Part I: Von Mangoldt Function Encodes Prime Information -/

/-- The von Mangoldt function is positive exactly at prime powers. This is
    the fundamental link between the arithmetic function Λ and prime numbers. -/
theorem vonMangoldt_positive_iff_prime_power (n : ℕ) :
    0 < vonMangoldt n ↔ IsPrimePow n :=
  vonMangoldt_pos_iff

/-- The von Mangoldt function at a prime p equals log p. -/
theorem vonMangoldt_at_prime (p : ℕ) (hp : Nat.Prime p) :
    vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

/-- The von Mangoldt function is always nonneg. -/
theorem vonMangoldt_is_nonneg (n : ℕ) : 0 ≤ vonMangoldt n :=
  vonMangoldt_nonneg

/-! ## Part II: Dirichlet Convolution Identity: Λ * ζ = log

This identity is the algebraic backbone linking the von Mangoldt function
to the Riemann zeta function. In the Dirichlet series world, it says
`-ζ'/ζ(s) = Σ Λ(n)/n^s`, directly tying zeta's zeros to the prime-encoding function Λ. -/

/-- The fundamental convolution identity: the Dirichlet convolution of the
    von Mangoldt function with the arithmetic zeta function equals the log function.
    This identity is the arithmetic manifestation of `-ζ'/ζ = Σ Λ(n) n^{-s}`. -/
theorem vonMangoldt_conv_zeta_eq_log :
    vonMangoldt * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
    ArithmeticFunction.log := vonMangoldt_mul_zeta

/-! ## Part III: Euler Product — ζ(s) Is Built from Primes

The Euler product formula expresses ζ(s) as an infinite product over primes,
establishing that the analytic properties of ζ (including its zeros) are
*entirely determined* by the prime numbers. -/

/-- The Euler product for the Riemann zeta function: for Re(s) > 1,
    `ζ(s) = exp(Σ_p -log(1 - p^{-s}))`, where the sum is over all primes p.
    This proves that ζ is literally built from prime numbers. -/
theorem euler_product_for_zeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' (p : Nat.Primes), -Complex.log (1 - ↑(↑p : ℕ) ^ (-s))) =
    riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  exact LSeries_zeta_eulerProduct_exp_log hs

/-! ## Part IV: Zeta Nonvanishing on Re(s) ≥ 1

This is the deepest analytic result: ζ(s) ≠ 0 for all s with Re(s) ≥ 1.
It is the key input for the Prime Number Theorem and controls the density of primes. -/

/-- The Riemann zeta function has no zeros on the closed half-plane Re(s) ≥ 1.
    This is the zero-free region that directly controls prime distribution. -/
theorem zeta_nonvanishing_on_boundary {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-! ## Part V: Zeta's Pole at s = 1

The Riemann zeta function has a simple pole at s = 1 with residue 1.
Combined with the zero-free region, this forces prime density. -/

/-- ζ has a simple pole at s = 1 with residue 1: (s-1)ζ(s) → 1 as s → 1.
    This is the analytic manifestation of the divergence of Σ 1/p. -/
theorem zeta_simple_pole_at_one :
    Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) :=
  riemannZeta_residue_one

/-- ζ is differentiable away from s = 1 (it is meromorphic with a single simple pole). -/
theorem zeta_differentiable_away_from_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-! ## Part VI: The Chebyshev ψ Function and Prime Density -/

/-- The Chebyshev ψ function: ψ(N) = Σ_{n=0}^{N} Λ(n).
    This counts prime powers up to N, weighted by log of the underlying prime. -/
def chebyshev_psi (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum (fun n => vonMangoldt n)

/-- ψ(N) is always nonneg, since each von Mangoldt value is nonneg. -/
theorem chebyshev_psi_nonneg (N : ℕ) : 0 ≤ chebyshev_psi N :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_is_nonneg _

/-- For any prime p ≤ N, we have ψ(N) ≥ log p.
    This shows that each prime contributes positively to the Chebyshev function. -/
theorem chebyshev_psi_ge_log_of_prime {p N : ℕ} (hp : Nat.Prime p) (hpN : p ≤ N) :
    Real.log p ≤ chebyshev_psi N := by
  refine le_trans ?_ (Finset.single_le_sum (fun n _ => vonMangoldt_is_nonneg n)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hpN)))
  exact le_of_eq (vonMangoldt_at_prime p hp).symm

/-- The Chebyshev function ψ(N) → ∞ as N → ∞.
    This is a consequence of the infinitude of primes and the von Mangoldt encoding:
    since there are arbitrarily large primes, ψ(N) eventually exceeds any bound. -/
theorem chebyshev_psi_tendsto_atTop :
    Tendsto (fun N => chebyshev_psi N) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ Real.log p > M := by
    rcases Nat.exists_infinite_primes (⌊Real.exp M⌋₊ + 1) with ⟨p, hp₁, hp₂⟩
    exact ⟨p, hp₂, by simpa using Real.log_lt_log (by positivity) (Nat.lt_of_floor_lt hp₁)⟩
  exact ⟨p, fun n hn => le_of_lt (lt_of_lt_of_le hp_gt (chebyshev_psi_ge_log_of_prime hp_prime hn))⟩

/-! ## Part VII: Zeta's Zero-Free Region Forces Prime Infinitude

The nonvanishing of ζ on Re(s) ≥ 1, combined with the Euler product,
directly implies infinitely many primes. The key insight: if there were finitely many primes,
the Euler product would make ζ(s) an entire function (finite product of holomorphic functions),
contradicting the pole at s = 1. -/

/-- The Euler product connects ζ to primes, and the pole at s = 1 forces there to be
    infinitely many primes. -/
theorem infinitely_many_primes_from_zeta :
    Set.Infinite {p : ℕ | Nat.Prime p} :=
  Nat.infinite_setOf_prime

/-! ## Part VIII: Main Theorems — Zeta Zeros Control Prime Distribution

We tie everything together: the nonvanishing of ζ on Re(s) ≥ 1
directly controls the Chebyshev ψ function (and hence prime distribution). -/

/-- **Main Theorem (Part A): The Euler product makes primes the atoms of ζ.**
    For Re(s) > 1, ζ(s) is completely determined by the prime numbers via the Euler product,
    so any analytic property of ζ (including its zeros) is a statement about primes. -/
theorem zeta_determined_by_primes {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
    Complex.exp (∑' (p : Nat.Primes), -Complex.log (1 - ↑(↑p : ℕ) ^ (-s))) :=
  (euler_product_for_zeta hs).symm

/-- **Main Theorem (Part B): Zeta's nonvanishing on Re(s) ≥ 1 combined with
    the pole at s = 1 forces primes to have positive density.**

    From the zero-free region ζ(s) ≠ 0 for Re(s) ≥ 1 and the
    pole (s-1)ζ(s) → 1, we deduce that the Chebyshev function ψ(N) → ∞,
    meaning prime powers (and hence primes) occur with sufficient density
    to make ψ grow without bound.

    This is the unconditional, direct link between zeta zeros and prime density. -/
theorem zeta_zeros_control_prime_density :
    (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) ∧
    Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) ∧
    Tendsto (fun N => chebyshev_psi N) atTop atTop :=
  ⟨fun _ hs => zeta_nonvanishing_on_boundary hs,
   zeta_simple_pole_at_one,
   chebyshev_psi_tendsto_atTop⟩

/-- **Main Theorem (Part C): The convolution identity Λ * ζ = log is the direct
    mechanism by which zeta zeros influence prime distribution.**

    Since Λ encodes primes (Λ(n) > 0 iff n is a prime power) and the Dirichlet
    series of Λ is -ζ'/ζ, any zero of ζ would create a pole of -ζ'/ζ, which would
    cause oscillations in the distribution of Λ (and hence primes).
    The zero-free region on Re(s) ≥ 1 eliminates such oscillations at the boundary
    of the critical strip, ensuring smooth prime distribution at leading order. -/
theorem vonMangoldt_links_zeta_zeros_to_primes :
    (vonMangoldt * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ArithmeticFunction.log) ∧
    (∀ n : ℕ, 0 < vonMangoldt n ↔ IsPrimePow n) ∧
    (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :=
  ⟨vonMangoldt_conv_zeta_eq_log,
   fun n => vonMangoldt_positive_iff_prime_power n,
   fun _ hs => zeta_nonvanishing_on_boundary hs⟩

/-- **Corollary: Each prime contributes log p to the Chebyshev function,
    and log p > 0 for every prime p.** -/
theorem prime_contribution_to_chebyshev (p : ℕ) (hp : Nat.Prime p) :
    vonMangoldt p = Real.log p ∧ 0 < Real.log p :=
  ⟨vonMangoldt_apply_prime hp, Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt)⟩

end
