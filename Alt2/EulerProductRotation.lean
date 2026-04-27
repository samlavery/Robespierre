import Mathlib

/-!
# Euler Product Rotation Invariance

The Euler product ∏_p (1 - p⁻ˢ)⁻¹ depends on each prime p only through its
distance from the origin, i.e. |p|.  Since every prime is a positive natural
number, its value *is* its distance from 0 on the real (or complex) line, so
the product is invariant under any "rotation" (or reflection) that preserves
absolute values.

We formalise this observation in several forms:

1. **`prime_cast_eq_abs`** – For any prime p : ℕ cast to ℝ, (p : ℝ) = |(p : ℝ)|.
2. **`euler_product_rotation_invariant`** – For any f : ℝ → ℂ and any finite
   set of natural numbers S, ∏_{p ∈ S} f(p) = ∏_{p ∈ S} f(|p|).
3. **`euler_product_rotation_invariant_complex`** – The analogous statement
   for the complex norm: ∏_{p ∈ S} f(‖p‖) = ∏_{p ∈ S} f(p) when elements
   are cast to ℂ and f depends only on the norm.
4. **`euler_term_depends_on_abs`** – The individual Euler factor
   (1 - (p : ℝ)^(-s))⁻¹ equals (1 - |(p : ℝ)|^(-s))⁻¹ for any real exponent s,
   showing each term depends only on the prime's distance from the origin.
-/

open Finset

/-! ### Primes are non-negative, so value = distance from 0 -/

/-- A natural number cast to ℝ equals its own absolute value. -/
theorem nat_cast_eq_abs (n : ℕ) : (n : ℝ) = |(n : ℝ)| := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]

/-- In particular, a prime cast to ℝ equals its absolute value. -/
theorem prime_cast_eq_abs {p : ℕ} (_hp : Nat.Prime p) : (p : ℝ) = |(p : ℝ)| :=
  nat_cast_eq_abs p

/-! ### Product invariance: f(p) = f(|p|) for any function -/

/-- The product of f(p) over a finite set of naturals equals the product of
    f(|p|), since p = |p| for natural numbers. This is the core "rotation
    invariance" observation: the Euler product doesn't change if we replace
    each prime by its distance from the origin. -/
theorem euler_product_rotation_invariant (f : ℝ → ℂ) (S : Finset ℕ) :
    ∏ p ∈ S, f (p : ℝ) = ∏ p ∈ S, f (|(p : ℝ)|) := by
  simp [abs_of_nonneg]

/-! ### Complex version: the Euler product depends only on ‖p‖ -/

/-- Casting a natural number to ℂ and taking the norm recovers the cast to ℝ. -/
theorem nat_cast_complex_norm (n : ℕ) : ‖(n : ℂ)‖ = (n : ℝ) := by
  norm_num [Norm.norm]

/-- The product of g(‖p‖) over a finite set equals the product of g(p),
    showing the Euler product factors depend only on norms (distances from 0
    in the complex plane). -/
theorem euler_product_rotation_invariant_complex (g : ℝ → ℂ) (S : Finset ℕ) :
    ∏ p ∈ S, g ‖(p : ℂ)‖ = ∏ p ∈ S, g (p : ℝ) := by
  norm_num [Norm.norm]

/-! ### The specific Euler factor (1 - p^(-s))^(-1) depends only on |p| -/

/-- Each Euler product factor (1 - p⁻ˢ)⁻¹ depends on the prime p only through
    its absolute value.  Concretely, replacing p by |p| in the factor doesn't
    change anything because p = |p| for any natural number. -/
theorem euler_term_depends_on_abs (p : ℕ) (s : ℝ) :
    (1 - ((p : ℝ) ^ (-s) : ℝ))⁻¹ = (1 - (|(p : ℝ)| ^ (-s) : ℝ))⁻¹ := by
  norm_num [abs_of_nonneg]

/-- Full Euler product: the product of (1 - p^(-s))^(-1) over a finite set
    of primes equals the same product with |p| in place of p. -/
theorem euler_product_abs_invariant (S : Finset ℕ) (s : ℝ) :
    ∏ p ∈ S, (1 - ((p : ℝ) ^ (-s)))⁻¹ =
    ∏ p ∈ S, (1 - (|(p : ℝ)| ^ (-s)))⁻¹ :=
  Finset.prod_congr rfl fun x _ => by rw [abs_of_nonneg (Nat.cast_nonneg x)]
