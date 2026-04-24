import Mathlib
import RequestProject.WeilFinalAssembly
import RequestProject.WeilPairIBP
import RequestProject.WeilContour
import RequestProject.WeilCoshPairPositivity
import RequestProject.GaussianDetectorPair
import RequestProject.PairCoshGaussBetaReflection
import RequestProject.WeilBridge
import RequestProject.GaussianAdmissible
import RequestProject.ExplicitFormulaBridgeOfRH

/-!
# B.6 — `weilExtraction_target` via the energy-defect / explicit-formula-bridge route

**Target** (WeilFinalAssembly:524):
```
weilExtraction_target :=
  (∀ β ∈ (0,1), WeilExplicitFormula_pair_cosh_gauss_target β) →
  pair_defect_vanishes_at_zeros.
```

## Architecture (the whole picture — two halves)

The classical Weil-positivity proof of RH has **two analytic halves**:

### Half 1 — Weil explicit formula
Spectral ↔ geometric identity for a custom test function.  In this project
the packaged form is `WeilExplicitFormula_pair_cosh_gauss_target β` at
`WeilFinalAssembly:470`:
```
Σ_ρ n(ρ) · pairTestMellin β ρ = gaussianPairDefect β.
```

### Half 2 — Prime-harmonic → energy-defect detection bridge
The prime side of the Weil formula, viewed through Parseval, produces
specific energy-defect-packet signatures.  Offline zeta zeros *emit* an
energy-defect signature at their height (β = ρ.re, γ = Im ρ), and that
signature is *detected* by the prime harmonic sum `Σ Λ(n) · n^{-s}`
evaluated against the cosh-Gauss pair.  This half is the
`ExplicitFormulaBridge ψ_gaussian` structure at `WeilBridge.lean:87`:
```
structure ExplicitFormulaBridge (ψ : ℝ → ℝ) where
  zero_forces_vanishing : ∀ ρ ∈ NontrivialZeros,
    averageEnergyDefect ψ ρ.re = 0
```

### How they compose

Given BOTH halves plus admissibility (`ψ_gaussian_admissible`), the project
already proves `∀ ρ ∈ NontrivialZeros, ρ.re = 1/2` via
`WeilBridge.all_nontrivial_zeros_on_critical_line` (line 124) using a
one-line contradiction:
* `bridge` → `averageEnergyDefect ψ_gaussian ρ.re = 0`,
* `gaussianKernel_averageEnergyDefect_pos_offline` → `averageEnergyDefect
  ψ_gaussian β > 0` for `β ≠ 1/2`,
* so `ρ.re = 1/2`.

From `ρ.re = 1/2`, `gaussianPairDefect_zero_on_line` gives
`gaussianPairDefect ρ.re = 0`, which is `pair_defect_vanishes_at_zeros`.

## Status in this file

The assembly below closes `weilExtraction_target` **conditional on** an
`ExplicitFormulaBridge ψ_gaussian`.  That structure is currently only
available via `ExplicitFormulaBridge_of_RiemannHypothesis hRH` (which
circularly assumes RH).

**The unconditional construction of `ExplicitFormulaBridge ψ_gaussian`
is the Half-2 content** — to be scaffolded in
`WeilPrimeHarmonicDetector.lean` (a separate file).  That construction
takes as input the Weil-formula hypothesis `(∀ β ∈ (0,1),
WeilExplicitFormula_pair_cosh_gauss_target β)` and produces the bridge.

## Why the earlier F-chain scaffold was abandoned

Earlier versions of this file tried to wire the RH extraction through
`RH_from_F_chain` (WeilPairIBP:2391), which requires a witness satisfying
`Σ n(ρ) · f(ρ) = 0` with `f ≥ 0` and identification `f ρ = 0 → gaussianPairDefect ρ.re = 0`.

That framework is the **wrong shape for the cosh-Gauss pair**:
* `f(ρ) := n(ρ) · gaussianPairDefect ρ.re` has no |Im ρ|-decay → F-3
  summability fails (divergent sum n(ρ) grows like T log T).
* Hybrid witnesses (Mellin²-weighted) give summability, but F-4
  (`Σ f = 0`) isn't a direct Weil-formula output — the Weil formula
  gives `Σ n(ρ) · pairTestMellin β ρ = gaussianPairDefect β`, which is
  bilinear, not simple.

The **correct route** is the Weil-positivity direct-contradiction
framework encoded in `ExplicitFormulaBridge`: offline-ρ + positivity +
bridge = contradiction.  No F-chain sum needed.

## Re-used infrastructure (all axiom-clean in-project)

* `WeilBridge.all_nontrivial_zeros_on_critical_line` — the main lemma.
* `WeilBridge.ExplicitFormulaBridge` — structure wrapping the bridge Prop.
* `ExplicitFormulaBridgeOfRH.gaussianKernel_averageEnergyDefect_pos_offline`
  — off-line positivity of the energy defect.
* `GaussianAdmissible.ψ_gaussian_admissible` — admissibility.
* `GaussianDetectorPair.gaussianPairDefect_zero_on_line` — β=1/2 collapse.
* `WeilFinalAssembly.pair_defect_vanishes_at_zeros` — target shape.
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

-- ═══════════════════════════════════════════════════════════════════════════
-- § Part 1 — Extract RH from `ExplicitFormulaBridge ψ_gaussian`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **RH from `ExplicitFormulaBridge ψ_gaussian` + admissibility.**
Direct application of `WeilBridge.all_nontrivial_zeros_on_critical_line`
to ψ_gaussian with the supplied bridge. -/
theorem re_half_of_explicitFormulaBridge_gaussian
    (bridge : ZD.ExplicitFormulaBridge ZD.gaussianKernel) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2 :=
  ZD.all_nontrivial_zeros_on_critical_line ZD.gaussianKernel
    ψ_gaussian_admissible bridge

-- ═══════════════════════════════════════════════════════════════════════════
-- § Part 2 — pair_defect_vanishes_at_zeros from RH
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`pair_defect_vanishes_at_zeros` from RH.**
`gaussianPairDefect ρ.re = gaussianPairDefect (1/2) = 0`
(by `gaussianPairDefect_zero_on_line`). -/
theorem pair_defect_vanishes_at_zeros_of_rh
    (hRH : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1 / 2) :
    ZD.WeilPositivity.pair_defect_vanishes_at_zeros := by
  intro ρ hρ
  rw [hRH ρ hρ]
  exact gaussianPairDefect_zero_on_line

end FinalAssembly
end WeilPositivity
end ZD

end
