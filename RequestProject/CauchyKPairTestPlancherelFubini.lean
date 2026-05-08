import Mathlib
import RequestProject.CauchyKPairTestPlancherel
import RequestProject.CauchyKPairTestResidueSum

/-!
# Plancherel-Fubini swap for the K-twisted zero sum

Combines the Plancherel form
`gaussianDefectEntireKernel_eq_K2_integral` (unconditional) with the
unconditional summability `K_pairTestMellin_zeroSum_summable_holds` to
deliver the Fubini-swapped representation of the K-twisted zero sum:

```
Σ' n(ρ) · K(ρ) · M(β, ρ)
  = 2π · Σ' n(ρ) · M(β, ρ) · ∫_{Ioi 0} K_2(ρ, t) · exp(-2 t²) dt
```

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity
open ZD.WeilPositivity.OfflineDetectorEndpoint

/-- Per-zero Plancherel: `n·K(ρ)·M(β,ρ) = 2π · ∫ n·K_2(ρ,t)·M(β,ρ)·exp(-2t²) dt`. -/
private lemma per_zero_plancherel
    (β : ℝ) (n : ℂ → ℕ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ((n ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
      Contour.pairTestMellin β ρ.val =
    2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ),
      ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
        K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) := by
  rw [gaussianDefectEntireKernel_eq_K2_integral ρ.val]
  rw [show ((n ρ.val : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ), K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) *
      Contour.pairTestMellin β ρ.val =
      2 * (Real.pi : ℂ) * (((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val) *
        ∫ t in Ioi (0:ℝ), K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) from by ring]
  rw [show (2 * (Real.pi : ℂ) * (((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val)) *
        (∫ t in Ioi (0:ℝ), K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) =
      2 * (Real.pi : ℂ) *
        ((((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val) *
        ∫ t in Ioi (0:ℝ), K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) from by ring]
  congr 1
  set c : ℂ := ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val with hc_def
  have h_int_const_mul :
      c * (∫ t in Ioi (0:ℝ), K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) =
      ∫ t in Ioi (0:ℝ), c * (K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) :=
    (integral_const_mul c (fun t => K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2))).symm
  rw [h_int_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

/-- **Plancherel-Fubini swap for the K-twisted zero sum.**

Combines per-zero Plancherel with absolute summability to express
the K-twisted zero sum as a tsum of t-integrals. This is the *partial*
swap; the full Fubini swap (interchanging Σ' and ∫) requires joint
summability/integrability and is proved separately.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem K_zeroSum_eq_tsum_t_integral
    (β : ℝ) (n : ℂ → ℕ) :
    (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      ((n ρ.val : ℕ) : ℂ) *
        gaussianDefectEntireKernel_local ρ.val *
        Contour.pairTestMellin β ρ.val) =
    ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ),
        ((n ρ.val : ℕ) : ℂ) *
          Contour.pairTestMellin β ρ.val *
          K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) := by
  apply tsum_congr
  intro ρ
  exact per_zero_plancherel β n ρ

#print axioms K_zeroSum_eq_tsum_t_integral

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
