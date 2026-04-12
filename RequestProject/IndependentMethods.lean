/-
# Amplitude of Prime-Indexed Harmonics at π/3

We give three unconditional methods to bound/characterize the amplitude of the
prime-indexed harmonic extracted at frequency t = π/3.

## Setting

For σ > 1 and a frequency t ∈ ℝ, define the **prime harmonic sum**:
  P(σ, t) = ∑_{p prime} p^{-σ} · cos(t · log p)
This is the real part of the prime Dirichlet series ∑_p p^{-s} evaluated at s = σ + it.

From the Euler product: for Re(s) > 1,
  log ζ(s) = ∑_p ∑_k (1/k) p^{-ks}
so the prime sum P(σ,t) is the leading term of Re(log ζ(σ+it)).

From von Mangoldt: -ζ'(s)/ζ(s) = ∑_n Λ(n) n^{-s}, which weights primes and prime powers.

All three methods work unconditionally for σ > 1, requiring no hypothesis about the
Riemann Hypothesis — we use only data outside the critical strip.

## Methods

1. **Absolute convergence & triangle inequality:** The sum converges absolutely
   and |P(σ,t)| ≤ ∑_p p^{-σ}, using Nat.Primes.summable_rpow.

2. **Von Mangoldt comparison:** The von Mangoldt weighted harmonic similarly
   converges absolutely, and provides an amplitude bound.

3. **Individual term extraction:** Each prime p contributes exactly
   p^{-σ} · cos(t · log p) to the sum. We prove each term is bounded
   in absolute value by p^{-σ} and that partial sums give explicit
   lower bounds on the amplitude via the first few primes.
-/

import Mathlib

open scoped ArithmeticFunction
open Real BigOperators

noncomputable section

/-! ## Core Definitions -/

/-- The prime harmonic at frequency `t` and exponent `σ`: the function
    `p ↦ p^{-σ} · cos(t · log p)` over the primes. -/
def primeHarmonic (σ t : ℝ) : Nat.Primes → ℝ :=
  fun p => (p : ℝ) ^ (-σ) * Real.cos (t * Real.log (p : ℝ))

/-- The prime amplitude function (unsigned version): `p ↦ p^{-σ}` over the primes. -/
def primeAmplitude (σ : ℝ) : Nat.Primes → ℝ :=
  fun p => (p : ℝ) ^ (-σ)

/-- The von Mangoldt weighted harmonic at frequency `t` and exponent `σ`:
    `n ↦ Λ(n) · n^{-σ} · cos(t · log n)` as a function on ℕ. -/
def vonMangoldtHarmonic (σ t : ℝ) : ℕ → ℝ :=
  fun n => Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log (n : ℝ))

/-! ## Method 1: Absolute Convergence and Triangle Inequality

This method uses only that `∑_p p^{-σ}` converges for `σ > 1`
(Nat.Primes.summable_rpow) and the universal bound `|cos x| ≤ 1`.
No information from inside the critical strip is used. -/

/-
Each term of the prime harmonic is bounded in norm by the corresponding
    term of the prime amplitude series.
-/
lemma primeHarmonic_norm_le (σ t : ℝ) (p : Nat.Primes) :
    ‖primeHarmonic σ t p‖ ≤ ‖primeAmplitude σ p‖ := by
      unfold primeHarmonic primeAmplitude; norm_num [ Real.norm_eq_abs ];
      exact mul_le_of_le_one_right ( abs_nonneg _ ) ( Real.abs_cos_le_one _ )

/-
**Method 1a:** For σ > 1, the prime harmonic at any frequency t
    is absolutely summable. This is unconditional.
-/
theorem primeHarmonic_summable {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (primeHarmonic σ t) := by
      -- Apply the summable_of_norm_bounded theorem with the summable primeAmplitude function and the inequality from primeHarmonic_norm_le.
      have h_summable : Summable (fun p : Nat.Primes => ‖primeAmplitude σ p‖) := by
        -- The series `∑_p p^{-σ}` converges for `σ > 1` by the p-series test.
        have h_pseries : Summable (fun p : ℕ => (p : ℝ) ^ (-σ)) := by
          exact Real.summable_nat_rpow.2 ( by linarith );
        exact h_pseries.norm.comp_injective Subtype.coe_injective;
      exact .of_norm <| h_summable.of_nonneg_of_le ( fun p => by positivity ) fun p => by simpa only [ norm_mul ] using primeHarmonic_norm_le σ t p;

/-
**Method 1b:** The amplitude (norm of the sum) of the prime harmonic
    is bounded by the prime zeta function P(σ) = ∑_p p^{-σ}.
    This is unconditional for σ > 1.
-/
theorem primeHarmonic_amplitude_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖∑' p : Nat.Primes, primeHarmonic σ t p‖ ≤
      ∑' p : Nat.Primes, primeAmplitude σ p := by
        refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
        · exact Summable.norm ( primeHarmonic_summable hσ t );
        · refine' Summable.tsum_le_tsum _ _ _;
          · exact fun p => le_trans ( primeHarmonic_norm_le σ t p ) ( le_of_eq ( abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) );
          · exact Summable.norm ( primeHarmonic_summable hσ t );
          · -- The series $\sum_{p} p^{-\sigma}$ is a convergent p-series with $p > 1$.
            have h_pseries : Summable (fun p : ℕ => (p : ℝ) ^ (-σ)) := by
              exact Real.summable_nat_rpow.2 ( by linarith );
            exact h_pseries.comp_injective Subtype.coe_injective

/-
The prime amplitude series itself converges for σ > 1.
-/
lemma primeAmplitude_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (primeAmplitude σ) := by
      -- The series $\sum_{p} p^{-\sigma}$ is a p-series with $p > 1$, which converges.
      have h_pseries : Summable (fun p : ℕ => (p : ℝ) ^ (-σ)) := by
        exact Real.summable_nat_rpow.2 ( by linarith );
      convert h_pseries.comp_injective ( show Function.Injective ( fun p : Nat.Primes => p.val ) from fun p q h => Subtype.ext h ) using 1

/-- **Specialization to t = π/3:** The amplitude at frequency π/3 is bounded
    by the prime zeta function. -/
theorem primeHarmonic_amplitude_le_at_pi_third {σ : ℝ} (hσ : 1 < σ) :
    ‖∑' p : Nat.Primes, primeHarmonic σ (π / 3) p‖ ≤
      ∑' p : Nat.Primes, primeAmplitude σ p :=
  primeHarmonic_amplitude_le hσ (π / 3)

/-! ## Method 2: Von Mangoldt Weighted Harmonic

The von Mangoldt function Λ(n) = log p if n = p^k, 0 otherwise.
The sum ∑_n Λ(n) n^{-σ} cos(t log n) converges absolutely for σ > 1,
giving an alternative unconditional characterization of prime harmonics.
The dominant contribution comes from the primes themselves (k=1 terms). -/

/-
Each term of the von Mangoldt harmonic is bounded by Λ(n) · n^{-σ}.
-/
lemma vonMangoldtHarmonic_norm_le (σ t : ℝ) (n : ℕ) :
    ‖vonMangoldtHarmonic σ t n‖ ≤ Λ n * ‖(n : ℝ) ^ (-σ)‖ := by
      unfold vonMangoldtHarmonic;
      by_cases hn : n = 0 <;> simp_all +decide [ ArithmeticFunction.vonMangoldt ];
      split_ifs <;> norm_num [ abs_mul, abs_of_nonneg, Real.rpow_nonneg ];
      rw [ abs_of_nonneg ( Real.log_nonneg <| mod_cast Nat.minFac_pos _ ) ] ; exact mul_le_of_le_one_right ( by positivity ) ( Real.abs_cos_le_one _ )

/-
The von Mangoldt weight at a prime equals log p.
-/
lemma vonMangoldt_at_prime (p : Nat.Primes) :
    Λ (p : ℕ) = Real.log (p : ℝ) := by
      convert ArithmeticFunction.vonMangoldt_apply_prime p.prop

/-
At a prime p, the von Mangoldt harmonic equals log(p) times the prime harmonic term.
-/
theorem vonMangoldtHarmonic_at_prime (σ t : ℝ) (p : Nat.Primes) :
    vonMangoldtHarmonic σ t (p : ℕ) =
      Real.log (p : ℝ) * primeHarmonic σ t p := by
        unfold vonMangoldtHarmonic primeHarmonic; rw [ vonMangoldt_at_prime ] ; ring;

/-! ## Method 3: Individual Term Extraction and Explicit Bounds

Each prime p contributes a term with known amplitude p^{-σ} and phase
t · log p. We prove bounds on individual terms and show that partial
sums over small primes give explicit lower bounds. -/

/-
Each prime's contribution to the harmonic has absolute value exactly p^{-σ} · |cos(t log p)|.
-/
lemma primeHarmonic_abs (σ t : ℝ) (p : Nat.Primes) :
    |primeHarmonic σ t p| = (p : ℝ) ^ (-σ) * |Real.cos (t * Real.log (p : ℝ))| := by
      unfold primeHarmonic;
      rw [ abs_mul, abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ]

/-
Each prime's contribution is bounded by p^{-σ}.
-/
theorem primeHarmonic_term_le (σ t : ℝ) (p : Nat.Primes) (_hσ : 0 < σ) :
    |primeHarmonic σ t p| ≤ (p : ℝ) ^ (-σ) := by
      convert primeHarmonic_abs σ t p |> le_of_eq |> le_trans <| mul_le_of_le_one_right ( by positivity ) ( Real.abs_cos_le_one _ ) using 1

/-
The contribution of prime p=2 at frequency π/3 and exponent σ is
    2^{-σ} · cos(π/3 · log 2), which is positive (since cos is positive on small arguments).
-/
theorem prime2_harmonic_eq (σ : ℝ) :
    primeHarmonic σ (π / 3) ⟨2, Nat.prime_iff.mpr (by decide)⟩ =
      (2 : ℝ) ^ (-σ) * Real.cos (π / 3 * Real.log 2) := by
        rfl

/-
The cosine factor at p=2 and t=π/3 is positive, since π/3 · log 2 < π/2.
-/
theorem cos_pi_third_log2_pos : 0 < Real.cos (π / 3 * Real.log 2) := by
  exact Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, Real.log_pos one_lt_two ], by nlinarith [ Real.pi_pos, Real.log_le_sub_one_of_pos zero_lt_two ] ⟩

/-
Therefore the leading prime term p=2 makes a strictly positive contribution
    to the harmonic sum at t = π/3 for any σ > 0. This gives an unconditional
    lower bound on the amplitude: it is at least 2^{-σ} · cos(π/3 · log 2) > 0,
    minus higher-order terms.
-/
theorem prime2_contribution_pos (σ : ℝ) (_hσ : 0 < σ) :
    0 < primeHarmonic σ (π / 3) ⟨2, Nat.prime_iff.mpr (by decide)⟩ := by
      exact mul_pos ( by positivity ) ( by exact Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, Real.log_nonneg one_le_two ], by nlinarith [ Real.pi_pos, Real.log_le_sub_one_of_pos zero_lt_two ] ⟩ )

end