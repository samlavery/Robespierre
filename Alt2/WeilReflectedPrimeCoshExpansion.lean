import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.ArchOperatorBound
import RequestProject.WeilReflectedPrimeVanishingWeilside

/-!
# Reflected-prime single-cosh pair expansion at σ = 2

Target downstream: close the sorry at
`WeilFinalAssemblyUnconditional.lean:archPair_eq_primePair_at_two_unconditional`.

By `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`
(`WeilReflectedPrimeVanishingWeilside.lean:1160`, proved), this target is
equivalent to

    ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0.

## Decomposition

The pair-test Mellin has the five-term cosh-Gauss expansion
(`Contour.pairTestMellin_cosh_expansion`):

```
pairTestMellin β (s)
  = (1/2)·coshGaussMellin(2β−π/3)(s) + (1/2)·coshGaussMellin(2−π/3−2β)(s)
    − coshGaussMellin(1−π/3)(s) − coshGaussMellin(2β−1)(s)
    + coshGaussMellin 0 (s).
```

So `∫ reflectedPrimeIntegrand β 2 t dt` decomposes into five integrals of the
form

    reflectedPrimeSingleCosh c := ∫ t, ζ'/ζ(1−(2+it)) · coshGaussMellin c (2+it) dt.

This file provides:

* `reflectedPrimeSingleCosh_integrable c` — integrability on ℝ.
* `reflectedPrime_integral_cosh_expansion_at_two β` — the five-term expansion.

The remaining content is the **combo-vanishing identity**

    (pair-combo of reflectedPrimeSingleCosh in β) = 0,

equivalently `archPair β = primePair β`. This is the classical Weil explicit
formula specialised to the cosh-Gauss pair test at σ = 2. It is **not** a
corollary of the algebraic pair-coefficient identities `pair_coeffs_sum` /
`pair_axes_sum` alone, nor of any other infrastructure currently in the repo;
it requires a genuine contour-shift / residue-sum analytic argument.

The scaffold here isolates the infrastructure from the content: after L1 and
L3 land, the **single** remaining open fact is the combo-vanishing, stated as
`reflectedPrime_integral_vanishes_at_two`. Downstream assembly into
`archPair_eq_primePair_at_two_proved` is then a proved-iff composition.
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace ReflectedPrimeCoshExpansion

open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing

/-! ## Definition — single-cosh reflected-prime integral

Pair `ζ'/ζ(1−(2+it))` against `coshGaussMellin c (2+it)` instead of the
pair-test Mellin `pairTestMellin β (2+it)`. The five values
`c ∈ {2β−π/3, 2−π/3−2β, 1−π/3, 2β−1, 0}` assemble to `∫ reflected β 2` by
linearity (L3 below).
-/

/-- Single-cosh version of `∫ t, reflectedPrimeIntegrand β 2 t dt`. -/
def reflectedPrimeSingleCosh (c : ℝ) : ℂ :=
  ∫ t : ℝ,
    deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
    Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)

/-! ## L1 — Integrability of the single-cosh reflected-prime integrand

The `ζ'/ζ(1 − s)` factor on `Re s = 2` is bounded (it's the log-derivative
of ζ at `Re = −1`, meromorphic with a simple structure via the FE). The
`coshGaussMellin c (2+it)` factor has `O(1/(1+t²))` quadratic decay via
IBP×2. Combined: integrable.

Route (mirroring `h1_arch_coshGaussMellin_integrable` at
`WeilReflectedPrimeVanishingWeilside.lean:569`): use the quadratic-decay
bound on `coshGaussMellin c (2+it)` together with a pointwise bound on the
`ζ'/ζ(1−(2+it))` factor (polynomial in `log|t|` is enough; even a crude
`(1 + |t|)^N` majorant for small `N` suffices, paralleling
`arch_subunit_bound_at_two`).
-/

/-- **L1**: integrability of the single-cosh reflected-prime integrand on ℝ. -/
theorem reflectedPrimeSingleCosh_integrable (c : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
  sorry

/-! ## L3 — Five-term pair expansion

By `Contour.pairTestMellin_cosh_expansion`, `pairTestMellin β (2+it)` is a
fixed linear combination of `coshGaussMellin cᵢ (2+it)` for five explicit
coefficients `cᵢ(β)`. Multiplying by the reflected factor `ζ'/ζ(1−(2+it))`
and integrating (using L1 for each `cᵢ`) gives the pair expansion.

Parallels `arch_integral_cosh_expansion_at_two` at
`WeilReflectedPrimeVanishingWeilside.lean:805`.
-/

/-- **L3**: five-term pair expansion of the reflected-prime integral. -/
theorem reflectedPrime_integral_cosh_expansion_at_two (β : ℝ) :
    (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) =
      (1/2 : ℂ) * reflectedPrimeSingleCosh (2 * β - Real.pi / 3) +
      (1/2 : ℂ) * reflectedPrimeSingleCosh (2 - Real.pi / 3 - 2 * β) -
      reflectedPrimeSingleCosh (1 - Real.pi / 3) -
      reflectedPrimeSingleCosh (2 * β - 1) +
      reflectedPrimeSingleCosh 0 := by
  sorry

/-! ## Remaining content — classical Weil at σ = 2 for the cosh-Gauss pair test

The substantive analytic content: the pair-combo above vanishes.

Not derivable from pair-coefficient algebra alone (per-c arch vs prime
disagree; see `WeilReflectedPrimeVanishingWeilside.lean:1095–1097`). Requires
a contour-shift / explicit-formula argument on the specific test function.

This sorry is **equivalent** (via
`archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`) to the downstream
sorry `archPair_eq_primePair_at_two_unconditional` — it's a relabeling, not a
reduction. Kept here only because this file's scope is the single-cosh
expansion and the combo-vanishing fits the file's subject.
-/

/-- **Remaining content**: the reflected-prime integral on σ = 2 vanishes
for the pair-cosh-Gauss test. Equivalent to `archPair_eq_primePair_at_two_target β`
via the proved iff. -/
theorem reflectedPrime_integral_vanishes_at_two (β : ℝ) :
    ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0 := by
  sorry

/-- **Downstream hookup**: produce the `archPair_eq_primePair` target from the
combo-vanishing via the proved iff. -/
theorem archPair_eq_primePair_at_two_proved (β : ℝ) :
    ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β :=
  (ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes β).mpr
    (reflectedPrime_integral_vanishes_at_two β)

end ReflectedPrimeCoshExpansion
end Contour
end WeilPositivity
end ZD

end
