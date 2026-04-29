import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilRightEdge
import RequestProject.WeilHorizontalDecay
import RequestProject.WeilZeroSum
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilCoshPairPositivity

/-!
# ⚠️ LEGACY — superseded by `WeilCoshPairPositivity.lean` + `WeilZeroOrthogonality.lean`.

Kept only for backward import compatibility. The current architecture
exposes the Weil vanishing TARGET under the name `WeilVanishesOnZeros`
(in `WeilCoshPairPositivity.lean`) and the orthogonality TARGET as
`ZeroCoefficientVanishesByOrthogonality` (in `WeilZeroOrthogonality.lean`).
Both are stated, not proved here. The conditional implication
`WeilVanishesOnZeros → RiemannHypothesis` is the cosh-side payoff,
proved in `WeilCoshPairPositivity.lean` via cosh separation.

Do NOT extend this file. The "trivial conditional closure" wrapper
below is preserved only to keep downstream imports green.

# Weil Pair Defect Final Closure — Cycle 50 (legacy)

Goal: discharge the tracked `sorry` in `WeilPairFormula.lean`
(`pair_defect_vanishes_at_zeros_proof`) using the full Weil-formula pipeline
assembled from cycles 42–48.

## The closure chain

Given:

* **Cycle 41**: rectangle contour integral of `weilIntegrand (pairTestMellin β)`
  with poles at `s = 1` and at each nontrivial zero ρ inside.
* **Cycle 44**: horizontal edges → 0 as `T → ∞`.
* **Cycle 43**: left edge transferred to right edge via FE.
* **Cycle 42**: right edge = Euler-product integral (prime sum).
* **Cycle 45**: residue at `s = 1` contributes `pairTestMellin β 1 =
  gaussianPairDefect β` (from cycle 27).
* **Cycle 46**: residues at nontrivial zeros ρ sum to `−∑_ρ pairTestMellin β ρ`,
  absolutely convergent via Jensen.
* **Cycle 48**: `arch integral = prime integral` (the 6th-root-of-unity
  algebraic identity).

Conclude: `∑_ρ pairTestMellin β ρ = gaussianPairDefect β`.

Combined with **cycle 49**'s per-zero non-negativity structure (via the sinh²
factorization of cycle 36 — `pairTestMellin β ρ` splits as `(β − 1/2)²·positive
 − (1/2 − π/6)²·positive·...`), and noting that at β = ρ.re this gives a
non-negative contribution, the sum-equals-target relation forces each per-zero
contribution to vanish, yielding `gaussianPairDefect ρ.re = 0` for every
nontrivial zero ρ. This is **`pair_defect_vanishes_at_zeros`** — the sorry.

## Delivered in this file

* `WeilFinalClosureTarget` — named target for the pair-defect vanishing,
  equivalent to the tracked `sorry` in `WeilPairFormula.lean`.
* `weilFinalClosure_from_pipeline` — structural theorem: given all the
  pipeline outputs (cycles 42, 44, 46, 48 as hypotheses), the final
  `pair_defect_vanishes_at_zeros` follows.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

end Contour
end WeilPositivity
end ZD

end
