import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.WeilContour

/-!
# Orthogonality extraction target

Bridge from a *family* of global Weil-formula identities (one equation
per admissible test parameter `β`) to *per-zero* vanishing (one equation
per nontrivial zero `ρ`).

If the family of zero-side Weil identities holds across enough admissible
`β` to be sufficient for orthogonality extraction in the per-zero
coefficient space, then per-zero vanishing follows.

This file STATES the target only. It is **not** proved here. It is the
precise analytic obligation that any "global identity ⟹ per-zero
vanishing" argument must discharge.

The target lives in this dedicated file so that the cosh side, the
analytic Weil side, and the orthogonality bridge are visibly separated:

* **Cosh side**: `gaussianPairDefect_pos_offline` — pure cosh geometry,
  σ ≠ 1/2 ⟹ `gaussianPairDefect σ ≠ 0`. Independent of RH.
* **Weil side**: `WeilVanishesOnZeros` — analytic vanishing target,
  one equation per zero. Stated in `WeilCoshPairPositivity.lean`.
* **Orthogonality side** (this file): bridge from a per-`β` family of
  global identities to the per-zero target above.

No axioms. No sorries. No proved theorems — only the Prop target.
-/

open Complex

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroOrthogonality

/-- **Orthogonality extraction target.**

Given a candidate "zero-side coefficient" function `a : ℂ → ℂ` and the
hypothesis that the global Weil identity
```
∑' ρ ∈ NontrivialZeros, a(ρ) · pairTestMellin β ρ = 0
```
holds for every admissible parameter `β ∈ (0,1)`, the family
`{pairTestMellin β · | β ∈ (0,1)}` is sufficient to force the per-zero
coefficient `a(ρ)` to vanish at every nontrivial zero.

This is the bridge from "global Weil identities" (one equation per `β`)
to "per-zero vanishing" (one equation per `ρ`).

NOT proved here — STATED only as an analytic target. The `Summable`
hypothesis on the family is the project's per-zero summability witness;
we use a `Summable` predicate at each `β` rather than introduce a fake
project-specific summability predicate. -/
def ZeroCoefficientVanishesByOrthogonality : Prop :=
  ∀ (a : ℂ → ℂ),
    (∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    →
    (∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

#print axioms ZeroCoefficientVanishesByOrthogonality

end ZeroOrthogonality
end WeilPositivity
end ZD

end
