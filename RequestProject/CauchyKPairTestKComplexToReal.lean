import Mathlib
import RequestProject.CauchyWeilDefectScratch
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.OfflineDetectorProof

/-!
# Bridge: K-complex to K-real-axis (Step 31)

Per user directive (2026-05-08): convert the K-complex zero-side data into
the real-axis defect coefficient `D(Re ρ)` via FE/conj 4-tuple orbit
averaging, then L²/Plancherel projection.

## Structure

For each ρ ∈ NontrivialZeros, the 4-tuple FE/conj orbit `{ρ, ρ̄, 1-ρ, 1-ρ̄}`
collapses the K-complex sum into:

**Step 1 (FE+conj structural)**:  axiom-clean.
```
K(ρ)·M(β,ρ) + K(ρ̄)·M(β,ρ̄) + K(1-ρ)·M(β,1-ρ) + K(1-ρ̄)·M(β,1-ρ̄)
  = K(ρ)·(M(β,ρ) + M(β,1-ρ))
  + star (K(ρ)·(M(β,ρ) + M(β,1-ρ)))
  = 2·Re(K(ρ)·(M(β,ρ) + M(β,1-ρ)))   [pure FE+conj symmetry]
```

**Step 2 (L²/Plancherel)**: substantive.  Convert `Re K(ρ)·(M(β,ρ) + M(β,1-ρ))`
to `D(Re ρ)·(even pair-test channel)` using:
- `averageEnergyDefect_eq_weighted_L2`: `D(σ) = 2π · ∫ (amp²(σ,t) + odd²(σ,t)) · ψ²(t) dt`.
- The cosh-Gauss test's amp/odd decomposition identity.

Step 2 is the substantive RH-strength gate (load-bearing analytic content).

## What this file does

- **Defines** `K_4tuple_orbit_sum`, `K_paired_re_form`.
- **Proves** Step 1 axiom-clean: structural FE+conj reduction.
- **States** Step 2 as a Prop (the L²-Plancherel target).
- **Documents** the substantive analytic obligation.

Axiom footprint target for Step 1: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.OfflineDetectorEndpoint
open ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch
open ZD.WeilPositivity.FinalAssembly

/-! ## Step 31.1: 4-tuple orbit sum -/

/-- The 4-tuple FE/conj orbit sum `{ρ, ρ̄, 1-ρ, 1-ρ̄}` of `K · M`. -/
noncomputable def K_4tuple_orbit_sum (β : ℝ) (ρ : ℂ) : ℂ :=
  gaussianDefectEntireKernel_local ρ * Contour.pairTestMellin β ρ +
  gaussianDefectEntireKernel_local (star ρ) * Contour.pairTestMellin β (star ρ) +
  gaussianDefectEntireKernel_local (1 - ρ) * Contour.pairTestMellin β (1 - ρ) +
  gaussianDefectEntireKernel_local (1 - star ρ) *
    Contour.pairTestMellin β (1 - star ρ)

/-- The "paired" Re-form: K(ρ) acting on the FE-paired Mellin sum. -/
noncomputable def K_paired_complex_form (β : ℝ) (ρ : ℂ) : ℂ :=
  gaussianDefectEntireKernel_local ρ *
    (Contour.pairTestMellin β ρ + Contour.pairTestMellin β (1 - ρ))

/-! ## Step 31.2: Step 1 — FE+conj structural reduction (axiom-clean)

```
K_4tuple_orbit_sum β ρ
  = K_paired_complex_form β ρ + star (K_paired_complex_form β ρ).
```

Pure FE-symmetry `K(1-s) = K(s)` + conj-symmetry of K and pairTestMellin. -/

theorem K_4tuple_orbit_sum_eq_paired_plus_star (β : ℝ) (ρ : ℂ) :
    K_4tuple_orbit_sum β ρ =
      K_paired_complex_form β ρ + star (K_paired_complex_form β ρ) := by
  unfold K_4tuple_orbit_sum K_paired_complex_form
  -- Use FE-symm K(1-ρ) = K(ρ), K(1-ρ̄) = K(ρ̄).
  rw [gaussianDefectEntireKernel_FE ρ, gaussianDefectEntireKernel_FE (star ρ)]
  -- Use conj-symm K(ρ̄) = star(K(ρ)).
  rw [gaussianDefectEntireKernel_conj ρ]
  -- Use M(β, ρ̄) = star(M(β,ρ)) and M(β, 1-ρ̄) = star(M(β, 1-ρ)).
  rw [show Contour.pairTestMellin β (star ρ) = star (Contour.pairTestMellin β ρ) from
    pairTestMellin_conj β ρ]
  rw [show Contour.pairTestMellin β (1 - star ρ) =
       star (Contour.pairTestMellin β (1 - ρ)) from by
    have h_eq : 1 - star ρ = star (1 - ρ) := by
      simp [star_sub, star_one]
    rw [h_eq, pairTestMellin_conj β (1 - ρ)]]
  -- Goal: K(ρ)·M(β,ρ) + (star K(ρ))·(star M(β,ρ)) + K(ρ)·M(β,1-ρ) + (star K(ρ))·(star M(β,1-ρ))
  --     = K(ρ)·(M(β,ρ) + M(β,1-ρ)) + star(K(ρ)·(M(β,ρ) + M(β,1-ρ))).
  -- Unfold star on the RHS via map_add, map_mul.
  rw [show star (gaussianDefectEntireKernel_local ρ *
        (Contour.pairTestMellin β ρ + Contour.pairTestMellin β (1 - ρ))) =
      star (gaussianDefectEntireKernel_local ρ) *
        (star (Contour.pairTestMellin β ρ) + star (Contour.pairTestMellin β (1 - ρ))) from by
    rw [star_mul', star_add]]
  ring

#print axioms K_4tuple_orbit_sum_eq_paired_plus_star

/-- **Step 1 corollary**: `K_4tuple_orbit_sum β ρ` is real-valued
(it's `z + star z = 2 Re z` in ℂ). -/
theorem K_4tuple_orbit_sum_eq_2re (β : ℝ) (ρ : ℂ) :
    K_4tuple_orbit_sum β ρ =
      2 * ((((K_paired_complex_form β ρ).re : ℝ) : ℂ)) := by
  rw [K_4tuple_orbit_sum_eq_paired_plus_star]
  -- `z + star z = ↑(2 * z.re)`, push_cast to `2 * ↑z.re`.
  have h := Complex.add_conj (K_paired_complex_form β ρ)
  show K_paired_complex_form β ρ + star (K_paired_complex_form β ρ) =
      2 * ((K_paired_complex_form β ρ).re : ℂ)
  rw [show star (K_paired_complex_form β ρ) =
       (starRingEnd ℂ) (K_paired_complex_form β ρ) from rfl, h]
  push_cast
  ring

#print axioms K_4tuple_orbit_sum_eq_2re

/-! ## Step 31.3: Step 2 (substantive) — L²/Plancherel projection target

The remaining substantive content: convert `(K_paired_complex_form β ρ).re`
into a real-axis quantity proportional to `D(Re ρ)·(even pair-test channel)`.

This requires the project's `averageEnergyDefect_eq_weighted_L2` Plancherel
identity:
```
D(σ) = 2π · ∫_{Ioi 0} (amp²(σ,t) + odd²(σ,t)) · ψ_gaussian(t)² dt,
```
combined with a careful decomposition of `Re(K(σ+iτ)·(M(β,σ+iτ) + M(β,1-σ-iτ)))`
into an `(amp² + odd²)`-style positive-definite integral.

Stated as a Prop here; not proved. -/

/-- **L²-Plancherel projection target (Step 2)**: the real part of the paired
complex form `Re(K(ρ)·(M(β,ρ) + M(β,1-ρ)))` decomposes via Plancherel into
a `D(Re ρ)`-weighted positive-definite even pair-test functional.

Stated abstractly as the property that the per-`ρ` 4-tuple contribution is
**proportional to `D(Re ρ)`** — the proportionality factor being the
positive even pair-test channel.  This is the bridge to
`gaussianDefectClosedFormVanishing`.  -/
def K_paired_re_eq_realDefect_target (β : ℝ) (ρ : ℂ) : Prop :=
  ∃ EvenPairTestChannel : ℝ,
    0 ≤ EvenPairTestChannel ∧
    ((K_paired_complex_form β ρ).re : ℝ) =
      (Real.exp ((ρ.re - 1/2)^2 / 2) -
        2 * Real.exp ((ρ.re - 1/2)^2 / 8) + 1) *
      EvenPairTestChannel

/-! ## Step 31.4: Status

**Step 1 (axiom-clean)**: 4-tuple FE+conj orbit reduction collapses the
K-complex contribution at `ρ` into `2·Re(K(ρ)·(M(β,ρ) + M(β,1-ρ)))`.

**Step 2 (substantive, RH-strength-adjacent)**: convert this real-valued
expression to `D(Re ρ)·(positive even pair-test channel)` via L²/Plancherel.

If Step 2 closes, summing over ρ ∈ NontrivialZeros (with conj/FE-orbit
quotienting) gives:
```
Σ' K(ρ)·M(β,ρ) = Σ' over orbits, D(Re ρ)·(positive channel)
```
The K-complex zero sum (Track A) then EQUALS a positive linear combination
of `D(Re ρ)`-weighted contributions.  Combined with positivity + orthogonality,
this gives `gaussianDefectClosedFormVanishing` from `K_complex_zeroSum_vanishes`.

**Honest status**: Step 1 is structural and done.  Step 2 is the substantive
analytic content — equivalent to RH at K-complex level (since
`K_complex_zeroSum_vanishes` is RH-equivalent and Step 2 would derive
`gaussianDefectClosedFormVanishing` from it). -/

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
