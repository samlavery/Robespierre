import Mathlib
import RequestProject.PartialWeilFormula
import RequestProject.WeilPairFormula

/-!
# G-2: Even test-function reduction of `weilRHS_prime`

For any even `h : ℝ → ℝ` (`h(-x) = h(x)`), the Weil prime-side sum
`weilRHS_prime h` simplifies termwise to `(2·log p / p^(k/2)) · h(k·log p)`
at each prime power `(p, k)`, via `h(k·log p) + h(-(k·log p)) = 2·h(k·log p)`.

Specialized to the pair-cosh-Gauss test `pair_cosh_gauss_test β` (which is
even by direct sinh²/Gaussian-squared evenness), this produces the concrete
prime-side form needed for the arch-prime integration step (G-4 / G-5).

No new custom axioms. Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Real Complex MeasureTheory BigOperators

noncomputable section

namespace ZD

/-- **Even test functions — termwise doubling.** For every `h : ℝ → ℝ`
satisfying `h(-x) = h(x)` pointwise, the Weil prime-side sum simplifies:

```
weilRHS_prime h =
  Σ_{p prime, k ≥ 1} (log p / p^(k/2)) · 2 · h(k · log p).
```

This is the even-`h` counterpart to `weilRHS_prime_of_odd`, which drops
the prime sum entirely. -/
theorem weilRHS_prime_of_even (h : ℝ → ℝ) (heven : ∀ x, h (-x) = h x) :
    weilRHS_prime h =
      ∑' pk : ℕ × ℕ,
        if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
          (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) *
            (2 * h (pk.2 * Real.log pk.1))
        else 0 := by
  unfold weilRHS_prime
  apply tsum_congr
  intro pk
  by_cases hh : Nat.Prime pk.1 ∧ 1 ≤ pk.2
  · rw [if_pos hh, if_pos hh]
    have hsum : h ((pk.2 : ℝ) * Real.log pk.1) +
                h (-((pk.2 : ℝ) * Real.log pk.1)) =
                2 * h ((pk.2 : ℝ) * Real.log pk.1) := by
      rw [heven ((pk.2 : ℝ) * Real.log pk.1)]
      ring
    rw [hsum]
  · rw [if_neg hh, if_neg hh]

#print axioms weilRHS_prime_of_even

end ZD

namespace ZD.WeilPositivity

/-- **Evenness of `pair_cosh_gauss_test β`.**

Both factors are even in `t`:
* `pairDetectorSqDiff β` factors into `sinh²((1/2 - π/6)·t) · sinh²((β - 1/2)·t)`,
  and `sinh(-·)² = sinh(·)²`.
* `ψ_gaussian(t) = exp(-t²)` is manifestly even (`(-t)² = t²`). -/
theorem pair_cosh_gauss_test_even (β t : ℝ) :
    pair_cosh_gauss_test β (-t) = pair_cosh_gauss_test β t := by
  rw [pair_cosh_gauss_test_sinh_factor, pair_cosh_gauss_test_sinh_factor]
  have h1 : Real.sinh ((1/2 - Real.pi/6) * (-t))^2 =
            Real.sinh ((1/2 - Real.pi/6) * t)^2 := by
    rw [show (1/2 - Real.pi/6) * (-t) = -((1/2 - Real.pi/6) * t) from by ring]
    rw [Real.sinh_neg]
    ring
  have h2 : Real.sinh ((β - 1/2) * (-t))^2 =
            Real.sinh ((β - 1/2) * t)^2 := by
    rw [show (β - 1/2) * (-t) = -((β - 1/2) * t) from by ring]
    rw [Real.sinh_neg]
    ring
  have h3 : ZD.ψ_gaussian (-t) = ZD.ψ_gaussian t := by
    unfold ZD.ψ_gaussian
    congr 1
    ring
  rw [h1, h2, h3]

#print axioms pair_cosh_gauss_test_even

/-- **Concrete prime sum for the pair-cosh-Gauss test.**

Combines `weilRHS_prime_of_even` with `pair_cosh_gauss_test_even`:

```
weilRHS_prime (pair_cosh_gauss_test β) =
  Σ_{p prime, k ≥ 1} (log p / p^(k/2)) · 2 · pair_cosh_gauss_test β (k · log p).
```

This is the concrete prime side of Weil's explicit formula specialized to
the pair-cosh-Gaussian test — the form needed for pairing against the arch
operator in G-4 / G-5. -/
theorem weilRHS_prime_pair_cosh_gauss_test (β : ℝ) :
    ZD.weilRHS_prime (pair_cosh_gauss_test β) =
      ∑' pk : ℕ × ℕ,
        if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
          (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) *
            (2 * pair_cosh_gauss_test β (pk.2 * Real.log pk.1))
        else 0 := by
  apply ZD.weilRHS_prime_of_even
  intro x
  exact pair_cosh_gauss_test_even β x

#print axioms weilRHS_prime_pair_cosh_gauss_test

end ZD.WeilPositivity

end
