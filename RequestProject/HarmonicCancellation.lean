import Mathlib

/-!
# Unconditional Harmonic Cancellation Theorems

We formalize the following unconditional mathematical facts:

1. **Prime harmonics are invariant**: The von Mangoldt function (encoding prime powers)
   is a fixed, deterministic arithmetic function — it generates the same "harmonics"
   regardless of observation. This is simply the fact that `Nat.ArithmeticFunction.vonMangoldt`
   is a well-defined function.

2. **The core identity `sin(arcsin(1/2)) = 1/2`**: This is the unconditional heart of the
   argument. Since `1/2 ∈ [-1, 1]`, the identity `sin(arcsin(x)) = x` applies, yielding
   exactly `1/2` — the critical line value.

3. **`arcsin(1/2) = π/6`**: The cosh kernel is centered at this value.

4. **Reflection symmetry**: `cos` is an even function, so any pair of zeros symmetric
   about a midpoint produces cancelling contributions: `cos(t) + cos(-t) = 2 cos(t)`,
   while `sin(t) + sin(-t) = 0`, killing the imaginary part.

5. **The residual value is exactly 1/2**: Any non-cancelling contribution from a cosh
   zero at arbitrary height, when projected through `sin ∘ arcsin`, lands at exactly `1/2`
   on the critical strip.

None of these results assume or imply the Riemann Hypothesis.
-/

open Real in
/-- The core unconditional identity: `sin(arcsin(1/2)) = 1/2`.
    Since `1/2 ∈ [-1, 1]`, `arcsin` is a right inverse of `sin`. -/
theorem sin_arcsin_one_half : sin (arcsin (1 / 2)) = 1 / 2 := by
  -- Apply the fact that $\sin(\arcsin(x)) = x$ for $x \in [-1, 1]$.
  apply Real.sin_arcsin; norm_num; norm_num

open Real in
/-- `arcsin(1/2) = π/6`, the center of the cosh kernel. -/
theorem arcsin_one_half_eq : arcsin (1 / 2) = π / 6 := by
  -- We know that $\sin(\pi/6) = 1/2$, so applying $\arcsin$ to both sides gives $\arcsin(\sin(\pi/6)) = \arcsin(1/2)$.
  rw [←Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-
The von Mangoldt function is a fixed, well-defined arithmetic function.
    Prime "harmonics" are deterministic and invariant — they do not depend
    on any unproven hypothesis.
-/
theorem vonMangoldt_is_fixed :
    ∀ n : ℕ, ArithmeticFunction.vonMangoldt n = ArithmeticFunction.vonMangoldt n := by
  exact fun _ => rfl

/-
Sine is odd: paired contributions reflected over a midpoint cancel
    in the imaginary component. For any height `t`, `sin(t) + sin(-t) = 0`.
-/
theorem sin_reflection_cancellation (t : ℝ) : Real.sin t + Real.sin (-t) = 0 := by
  norm_num +zetaDelta at *

/-
Cosine is even: paired contributions reflected over a midpoint reinforce
    in the real component. For any height `t`, `cos(t) + cos(-t) = 2 cos(t)`.
-/
theorem cos_reflection_reinforcement (t : ℝ) :
    Real.cos t + Real.cos (-t) = 2 * Real.cos t := by
      rw [ two_mul, Real.cos_neg ]

/-
For all values `x ∈ [-1, 1]`, the projection `sin(arcsin(x)) = x`.
    In particular, any cosh zero that doesn't cancel still maps to exactly
    `x` on the critical strip. When `x = 1/2`, this gives the critical line.
-/
theorem sin_arcsin_projection (x : ℝ) (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) :
    Real.sin (Real.arcsin x) = x := by
      rw [ Real.sin_arcsin hx₁ hx₂ ]

/-
The residual value from any non-cancelling cosh zero is exactly `1/2`,
    proven unconditionally as `sin(arcsin(1/2)) = 1/2`. This does NOT
    prove the Riemann Hypothesis — it is a tautological identity.
-/
theorem residual_value_is_one_half :
    Real.sin (Real.arcsin (1 / 2)) = 1 / 2 := by
      rw [ Real.sin_arcsin ] <;> norm_num

/-
Combined statement: if zeros come in reflected pairs (which cancels
    the imaginary part by `sin_reflection_cancellation`), and non-cancelling
    contributions are projected through `sin ∘ arcsin`, the residual real
    part is exactly `1/2`.
-/
theorem harmonic_cancellation_and_residual (t : ℝ) :
    -- Imaginary cancellation from reflected pairs
    Real.sin t + Real.sin (-t) = 0 ∧
    -- Residual value is 1/2
    Real.sin (Real.arcsin (1 / 2)) = 1 / 2 := by
      exact ⟨ by rw [ Real.sin_neg, add_neg_cancel ], by norm_num [ Real.sin_arcsin ] ⟩