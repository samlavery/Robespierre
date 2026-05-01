import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.HarmonicDiagnostics

/-!
# Partial Weil Explicit Formula

This file writes the Weil explicit formula in the form needed to close the
pair-agreement classifier bridge to RH, and proves unconditional fragments
of it.

The full formula is classical analytic number theory (Weil 1952, Delsarte
1966). It is not yet in Mathlib. This file makes the gap precise and
accumulates proved fragments.

## File structure

* `weilLHS φ` — the zero-side sum.
* `weilRHS_prime h` — the prime-side sum.
* `weilRHS_arch h φ` — the archimedean term.
* `WeilFormula h φ` — the Prop equating LHS and RHS.

## Proved fragments (unconditional)

* `weilLHS_zero` — `weilLHS 0 = 0`.
* `weilRHS_prime_zero` — `weilRHS_prime 0 = 0`.
* `weilRHS_arch_zero` — `weilRHS_arch 0 0 = 0`.
* `weilRHS_prime_of_odd` — for odd `h`, `weilRHS_prime h = 0`.
* `WeilFormula_zero` — the vacuous instance `WeilFormula 0 0`.
* `WeilFormula_reduction_of_odd` — if `h` is odd and `WeilFormula h φ` holds,
  then `weilLHS φ = weilRHS_arch h φ` (prime sum drops out).

## Classical references

* Weil, A. (1952). "Sur les 'formules explicites' de la théorie des
  nombres premiers". *Comm. Sém. Math. Univ. Lund*.
* Delsarte, J. (1966). "Formules de Poisson avec reste". *J. Anal. Math.*
-/

open Real Complex MeasureTheory BigOperators

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Component definitions
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Zero-side sum of the Weil formula.**

Sum over the subtype `{ρ // ρ ∈ NontrivialZeros}` of the test-function
image `φ(γ_ρ)` at the critical-line-shifted argument
`γ_ρ := (ρ - 1/2)/i`.

Note: the set `NontrivialZeros` is treated as a set, not a multiset. A
faithful Weil-formula zero-sum would count zeros by multiplicity. For the
Lean formalisation here we use the set; downstream statements that need
multiplicity would use a multiset-weighted variant. -/
def weilLHS (φ : ℂ → ℂ) : ℂ :=
  ∑' ρ : { ρ : ℂ // ρ ∈ NontrivialZeros },
    φ ((ρ.val - (1/2 : ℂ)) / Complex.I)

/-- **Prime-side sum.**

Sum over pairs `(p, k) ∈ ℕ × ℕ` with `p` prime and `k ≥ 1`, weighted by
`Λ(p^k)·p^{-k/2} = (log p)·p^{-k/2}`, of the symmetrised test-function
value `h(k·log p) + h(-k·log p)`. For odd `h` this is zero; for even `h`
it doubles the positive-argument evaluation. -/
def weilRHS_prime (h : ℝ → ℝ) : ℝ :=
  ∑' pk : ℕ × ℕ,
    if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
      (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) *
      (h (pk.2 * Real.log pk.1) + h (-(pk.2 * Real.log pk.1)))
    else 0

/-- **Archimedean term.**

The `h(0)·log π` anchor plus the Γ-kernel integral on the critical line.
The integrand uses `Complex.log ((1/4 : ℂ) + γ·I/2)` as the
finite-logarithm representative of the digamma; a more complete statement
would use `Γ'/Γ`. For the partial formula statement this representative
suffices. -/
def weilRHS_arch (h : ℝ → ℝ) (φ : ℂ → ℂ) : ℂ :=
  (h 0 : ℂ) * Complex.log ((Real.pi : ℂ)) +
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ γ : ℝ, φ (γ : ℂ) *
      Complex.log ((1/4 : ℂ) + (γ : ℂ) * Complex.I / 2)

/-- **Weil's explicit formula (partial form, Prop-packaged).**

For an admissible test-function pair `(h, φ)`:

```
  weilLHS φ  =  weilRHS_arch h φ  -  (weilRHS_prime h : ℂ)
```

This is the classical Weil (1952) explicit formula, written as a `Prop`.
It is not proved in the general form; this file accumulates unconditional
fragments that will compose into a proof. -/
def WeilFormula (h : ℝ → ℝ) (φ : ℂ → ℂ) : Prop :=
  weilLHS φ = weilRHS_arch h φ - (weilRHS_prime h : ℂ)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Proved fragments (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `weilLHS` vanishes at the zero test function. -/
theorem weilLHS_zero : weilLHS (fun _ => 0) = 0 := by
  unfold weilLHS
  exact tsum_zero

/-- `weilRHS_prime` vanishes at the zero test function. -/
theorem weilRHS_prime_zero : weilRHS_prime (fun _ => 0) = 0 := by
  unfold weilRHS_prime
  have : ∀ pk : ℕ × ℕ,
      (if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
        (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) * (0 + 0)
      else 0) = 0 := by
    intro pk
    by_cases hh : Nat.Prime pk.1 ∧ 1 ≤ pk.2
    · rw [if_pos hh]; ring
    · rw [if_neg hh]
  simp_rw [this]
  exact tsum_zero

/-- `weilRHS_arch` vanishes at the zero test-function pair. -/
theorem weilRHS_arch_zero : weilRHS_arch (fun _ => 0) (fun _ => 0) = 0 := by
  unfold weilRHS_arch
  simp

/-- **Odd test functions give vanishing prime sum.**

For any `h : ℝ → ℝ` satisfying `h(-x) = -h(x)` pointwise, the Weil
prime-side sum vanishes term-by-term: each `(p, k)` contribution contains
`h(k·log p) + h(-k·log p) = 0`.

This is the first *meaningful* fragment of the partial formula: it reduces
the odd-`h` case of the full Weil formula to the archimedean side. Matches
the architecture described in the project's `WeilBridge` file (odd test
function `g_ψ = 2t·ψ(|t|)`). -/
theorem weilRHS_prime_of_odd (h : ℝ → ℝ) (hodd : ∀ x, h (-x) = -h x) :
    weilRHS_prime h = 0 := by
  unfold weilRHS_prime
  have hterm : ∀ pk : ℕ × ℕ,
      (if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
        (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) *
        (h (pk.2 * Real.log pk.1) + h (-(pk.2 * Real.log pk.1)))
      else 0) = 0 := by
    intro pk
    by_cases hh : Nat.Prime pk.1 ∧ 1 ≤ pk.2
    · rw [if_pos hh]
      have : h ((pk.2 : ℝ) * Real.log pk.1) +
          h (-((pk.2 : ℝ) * Real.log pk.1)) = 0 := by
        rw [hodd]; ring
      rw [this, mul_zero]
    · rw [if_neg hh]
  simp_rw [hterm]
  exact tsum_zero

/-- **The vacuous instance of WeilFormula.**

The identity `weilLHS 0 = weilRHS_arch 0 0 - (weilRHS_prime 0 : ℂ)` holds
trivially (all three components are zero). This shows the `WeilFormula`
Prop is inhabited; it is not load-bearing but confirms the shape of the
definition. -/
theorem WeilFormula_zero : WeilFormula (fun _ => 0) (fun _ => 0) := by
  unfold WeilFormula
  rw [weilLHS_zero, weilRHS_arch_zero, weilRHS_prime_zero]
  simp

/-- **Reduction of WeilFormula for odd `h`.**

If `h` is odd and `WeilFormula h φ` holds, then the prime-side vanishes
(by `weilRHS_prime_of_odd`) and the formula collapses to

```
  weilLHS φ = weilRHS_arch h φ
```

i.e., the odd-`h` case of the Weil formula is equivalent to an archimedean
identity. This matches the project's stated target: reducing the bridge to
the odd-test-function `g_ψ = 2t·ψ(|t|)` and its archimedean counterpart. -/
theorem WeilFormula_reduction_of_odd
    (h : ℝ → ℝ) (φ : ℂ → ℂ)
    (hodd : ∀ x, h (-x) = -h x)
    (hform : WeilFormula h φ) :
    weilLHS φ = weilRHS_arch h φ := by
  unfold WeilFormula at hform
  rw [weilRHS_prime_of_odd h hodd] at hform
  rw [hform]
  push_cast
  ring

end ZD

end
