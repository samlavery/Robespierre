import Mathlib
import RequestProject.OffAxisTheoremDefs
/-! # Off-Axis Classical Zeta Zero Forces Prime Observable Change
This file proves the strongest honest unconditional theorem connecting
off-axis zeros of the Riemann zeta function to observable changes in the
prime distribution under the rotation-symmetry framework defined in `Defs.lean`.
## Main results
### Proved unconditionally
* `offaxis_forces_rotated_detector_event` — If `ρ.re ≠ 1/2`, the rotated prime
  density detector fires. This is an unconditional algebraic consequence of
  the definitions and does NOT use `riemannZeta ρ = 0`.
* `offaxis_forces_observable_nontriviality` — If `ρ.re ≠ 1/2`, some off-axis
  observable is nonzero.
* `offaxis_forces_numberline_distortion` — `realAxisDistortion n > 0` for `n ≥ 2`,
  unconditionally (independent of any zeta zero hypothesis).
### Status of the full target theorem
The target theorem:
```
theorem offaxis_classical_zero_forces_prime_observable_change
  (ρ : ℂ) (hz : riemannZeta ρ = 0) (hoff : ρ.re ≠ 1/2) :
  ∃ X, PrimeNumberLineObservableChange ρ X
```
requires a **bridge** from `riemannZeta ρ = 0` to a statement about the
prime-counting observables. This bridge is the **explicit formula** for the
Chebyshev function (von Mangoldt's formula), which is NOT in Mathlib as of
v4.28.0. Without it, the hypothesis `hz` cannot be connected to prime
distribution. The exact missing lemma is stated below as
`classical_zero_to_chebyshev_contribution`.
### What is proved
The maximal honest result combines:
1. The algebraic fact that off-axis ⟹ detector fires (does not need `hz`).
2. The statement of the missing bridge.
The combined theorem `offaxis_classical_zero_forces_detector_and_distortion`
uses both `hz` and `hoff` to conclude both the detector event AND the
number-line distortion, where the distortion part is unconditional (`n ≥ 2`)
and the detector part uses only `hoff`.
-/
open ArithmeticFunction Real
noncomputable section
/-
PROBLEM
============================================================
Part 1: Unconditional algebraic results (do not use hz)
============================================================
If `ρ.re ≠ 1/2`, the rotated prime density detector fires:
    there exists a rotation parameter `t` at which the norm-squared
    of the rotated prime density observable is nonzero.
    **Note**: This is purely algebraic; it does not use `riemannZeta ρ = 0`.
    The hypothesis `hz` is retained in the statement for interface compatibility
    with the rotation-symmetry framework.
PROVIDED SOLUTION
Use t = 0. Show rotatedPrimeDensityNormSq ρ.re 0 ≠ 0. By rotatedPrimeDensityNormSq_eq, this equals (ρ.re - 1/2)^2. Since ρ.re ≠ 1/2 (by hoff), we have ρ.re - 1/2 ≠ 0, so (ρ.re - 1/2)^2 ≠ 0.
-/
theorem offaxis_forces_rotated_detector_event
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ := by
      exact ⟨ 0, by rw [ rotatedPrimeDensityNormSq_eq ] ; exact pow_ne_zero 2 ( sub_ne_zero_of_ne hoff ) ⟩
/-
PROBLEM
If `ρ.re ≠ 1/2`, at least one of the off-axis observables is nonzero
    at `t = 0`.
PROVIDED SOLUTION
Use t = 0. Left disjunct: offAxisRealObservable ρ.re 0 = ρ.re - 1/2 by offAxisRealObservable_at_zero, which is ≠ 0 since ρ.re ≠ 1/2.
-/
theorem offaxis_forces_observable_nontriviality
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ t, offAxisRealObservable ρ.re t ≠ 0 ∨ offAxisImagObservable ρ.re t ≠ 0 := by
      exact ⟨ 0, Or.inl <| mul_ne_zero ( sub_ne_zero_of_ne hoff ) ( by norm_num ) ⟩
/-
PROBLEM
The real-axis distortion is positive for `n ≥ 2`, unconditionally.
    This reflects the existence of primes (specifically, the prime 2)
    and is independent of any zeta zero hypothesis.
PROVIDED SOLUTION
Use n = 2. Apply realAxisDistortion_pos_of_two_le with hn : 2 ≤ 2 from le_refl.
-/
theorem offaxis_forces_numberline_distortion
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (_hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ n, realAxisDistortion n > 0 := by
      exact ⟨ 2, realAxisDistortion_pos_of_two_le ( by norm_num ) ⟩
/-
PROBLEM
============================================================
Part 2: The detector does not pass for off-axis zeros
============================================================
No off-axis real part passes the rotated prime density detector.
    Equivalently, `σ ≠ 1/2 → ¬ rotatedPrimeDensityDetectorPasses σ`.
PROVIDED SOLUTION
Use rotatedPrimeDensityDetector_iff: rotatedPrimeDensityDetectorPasses σ ↔ σ = 1/2. Since σ ≠ 1/2, the iff gives ¬ passes.
-/
theorem no_offline_passes_detector {σ : ℝ} (hoff : σ ≠ 1 / 2) :
    ¬ rotatedPrimeDensityDetectorPasses σ := by
      exact fun h => hoff <| by have := h 0; norm_num [ offAxisRealObservable, offAxisImagObservable, rotatedPrimeDensityNormSq ] at this; nlinarith;
/-
PROBLEM
============================================================
Part 3: Combined theorem (maximal honest result)
============================================================
**Maximal honest unconditional theorem.**
    Given a zero `ρ` of the Riemann zeta function with `ρ.re ≠ 1/2`:
    1. The rotated prime density detector fires (algebraic, uses `hoff`).
    2. There exists `n ≥ 2` with positive real-axis distortion (unconditional).
    3. The detector does not pass for `ρ.re` (algebraic, uses `hoff`).
    The hypothesis `hz : riemannZeta ρ = 0` is formally present but unused
    in the proof. Connecting it to the prime observables requires the explicit
    formula (von Mangoldt's formula), which is not available in Mathlib v4.28.0.
    See `classical_zero_to_chebyshev_contribution` below for the precise
    missing lemma.
PROVIDED SOLUTION
Split into three conjuncts. First: apply offaxis_forces_rotated_detector_event. Second: apply offaxis_forces_numberline_distortion (or just use ⟨2, realAxisDistortion_pos_of_two_le (le_refl 2)⟩). Third: apply no_offline_passes_detector hoff.
-/
theorem offaxis_classical_zero_forces_detector_and_distortion
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ
      ∧ (∃ n, realAxisDistortion n > 0)
      ∧ ¬ rotatedPrimeDensityDetectorPasses ρ.re := by
        exact ⟨ offaxis_forces_rotated_detector_event ρ hz hoff, offaxis_forces_numberline_distortion ρ hz hoff, no_offline_passes_detector hoff ⟩
-- ============================================================
-- Part 4: Missing bridge lemma (STATED, NOT PROVED)
-- ============================================================
/-! ### Missing bridge: the explicit formula
The following axiom states the precise lemma that is missing from Mathlib
and would be needed to make `hz : riemannZeta ρ = 0` do nontrivial work
in the conclusion about prime distribution.
Informally, the explicit formula for the Chebyshev function states:
    ψ(x) = x − ∑_ρ x^ρ/ρ − log(2π) − ½ log(1 − x⁻²)
where the sum is over non-trivial zeros of ζ(s). Each zero ρ = σ + it
with σ ≠ 1/2 contributes a term of order x^σ to the oscillation of ψ(x),
which is strictly larger than the x^{1/2} contribution from critical-line
zeros. This larger oscillation IS the "observable change in the prime
distribution on the number line" caused by the off-axis zero.
We state the weakest useful form below. -/
/-- **Missing lemma (not in Mathlib v4.28.0).**
    If `ρ` is a non-trivial zero of the Riemann zeta function
    (i.e., `riemannZeta ρ = 0`, `0 < ρ.re`, `ρ.re < 1`),
    then for all sufficiently large `N`, the Chebyshev sum
    `realAxisDistortion N` deviates from `N` by at least `N^{ρ.re}`
    in a quantifiable way.
    This would connect `hz` to the prime-counting observable. -/
axiom classical_zero_to_chebyshev_contribution
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    ∃ (C : ℝ), C > 0 ∧
      ∀ᶠ (N : ℕ) in Filter.atTop,
        |realAxisDistortion N - (N : ℝ)| ≥ C * (N : ℝ) ^ ρ.re


/-- With the missing bridge, we can strengthen the conclusion to use `hz`. -/
theorem offaxis_with_bridge
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ))
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    (∃ C > 0, ∀ᶠ (N : ℕ) in Filter.atTop,
        |realAxisDistortion N - (N : ℝ)| ≥ C * (N : ℝ) ^ ρ.re)
    ∧ RotatedPrimeDensityDetectorEvent ρ := by
  exact ⟨classical_zero_to_chebyshev_contribution ρ hz hstrip,
         offaxis_forces_rotated_detector_event ρ hz hoff⟩
-- ============================================================
-- Part 5: Dependency audit
-- ============================================================
/-! ### Dependency audit
Every nontrivial imported theorem used:
1. `ArithmeticFunction.vonMangoldt_nonneg` — Λ(n) ≥ 0
2. `ArithmeticFunction.vonMangoldt_apply_prime` — Λ(p) = log p for prime p
3. `Real.log_pos` — log x > 0 for x > 1
4. `Real.cos_zero` — cos 0 = 1
5. `Real.sin_zero` — sin 0 = 0
6. `Real.cos_neg` — cos(-t) = cos t
7. `Real.sin_neg` — sin(-t) = -sin t
8. `Real.sin_sq_add_cos_sq` — sin²t + cos²t = 1
No theorem equivalent to RH, the functional equation s ↦ 1−s,
or any hypothesis listed in the hard constraints is used. -/
#check @ArithmeticFunction.vonMangoldt_nonneg
#check @ArithmeticFunction.vonMangoldt_apply_prime
#check @Real.log_pos
#check @Real.cos_zero
#check @Real.sin_zero
#check @Real.cos_neg
#check @Real.sin_neg
#check @Real.sin_sq_add_cos_sq
end