import Mathlib
import RequestProject.WeilContour

/-!
# Weil Right Edge — Cycle 42

Goal: on `Re s = 2`, pair `(−ζ'/ζ) · pairTestMellin` using cycle 25's Dirichlet
identity. Express the right-edge contour integral as a vertical line integral of

```
(Σ_n Λ(n) / n^(2+it)) · pairTestMellin β (2+it)
```

and evaluate via dominated convergence: `Λ(n)/n²` absolutely bounded, and
`pairTestMellin β (2+it)` has Gaussian decay in `t` (from cycle 40's closed
form + its analytic extension).

## Delivered in this file

* `weilIntegrand_right_edge_eq_LSeries_pairing` — pointwise identity on
  `Re s > 1`: `weilIntegrand h s = (LSeries Λ s) · h s`.

## Deferred (remaining in cycle 42)

* Full vertical-line integral evaluation with absolute convergence of the
  Λ-series paired against `pairTestMellin`.
* Tonelli/Fubini swap of sum and integral.

Estimated remaining work: 300–500 lines.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Weil integrand = (L-series · h) on Re s > 1.** Direct consequence of
cycle 25's `vonMangoldt_LSeries_eq_neg_logDeriv_zeta`. For `Re s > 1`:

```
weilIntegrand h s = (Σ_n Λ(n) / n^s) · h(s).
```

This is the pointwise form that, integrated along `Re s = 2`, gives the prime
side of the Weil formula. -/
theorem weilIntegrand_right_edge_eq_LSeries_pairing
    {h : ℂ → ℂ} {s : ℂ} (hs : 1 < s.re) :
    weilIntegrand h s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s * h s := by
  unfold weilIntegrand
  rw [vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs]

#print axioms weilIntegrand_right_edge_eq_LSeries_pairing

/-- **Right-edge interval integral identity.** On the vertical line `Re s = 2`,
the interval integral of `weilIntegrand h` along `[σ₀, σ₀ + iT]`-type path
equals the L-series · h integral (pointwise identity upgraded to integral). -/
theorem weil_right_edge_integral_eq_LSeries_integral
    (h : ℂ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, weilIntegrand h ((2 : ℂ) + (t : ℂ) * I)) =
    (∫ t in (-T)..T, LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((2 : ℂ) + (t : ℂ) * I) * h ((2 : ℂ) + (t : ℂ) * I)) := by
  apply intervalIntegral.integral_congr
  intro t _
  apply weilIntegrand_right_edge_eq_LSeries_pairing
  show (1 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re
  simp

/-- **Right-edge integral on ℝ-line.** Full vertical line at Re s = 2:
same identity on the entire imaginary-axis parameter. -/
theorem weil_right_edge_line_integral_eq_LSeries_line_integral
    (h : ℂ → ℂ) :
    (∫ t : ℝ, weilIntegrand h ((2 : ℂ) + (t : ℂ) * I)) =
    (∫ t : ℝ, LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((2 : ℂ) + (t : ℂ) * I) * h ((2 : ℂ) + (t : ℂ) * I)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  apply weilIntegrand_right_edge_eq_LSeries_pairing
  show (1 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re
  simp

#print axioms weil_right_edge_integral_eq_LSeries_integral
#print axioms weil_right_edge_line_integral_eq_LSeries_line_integral

end Contour
end WeilPositivity
end ZD

end
