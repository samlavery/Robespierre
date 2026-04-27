import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilIdentityAtPairTest
import RequestProject.WeilVerticalEdgeArchForm

/-!
# Asymptotic boundary identity in arch+reflected form (with horizontal edges)

This file combines two already-proved building blocks:

* `verticalEdgeDifference_limit_archForm`
  (in `RequestProject/WeilVerticalEdgeArchForm.lean`):
  along good heights `T → ∞`,
  ```
  I • ∫_(-T)^T (archIntegrand β 2 + reflectedPrimeIntegrand β 2)
    − I • ∫_(-T)^T (archIntegrand β (-1) + reflectedPrimeIntegrand β (-1))
    → 2πi · (pairTestMellin β 1 − Σ' n(ρ) · pairTestMellin β ρ).
  ```
* `horizontalEdgeDifference_vanishes`
  (in `RequestProject/WeilIdentityAtPairTest.lean`):
  along good heights `T → ∞`, the bottom-minus-top horizontal edge difference
  of `weilIntegrand (pairTestMellin β)` over the contour
  `Re s ∈ [-1, 2]` tends to `0`.

By the triangle inequality, the *sum* of these two quantities is also
asymptotic to `2πi · (pairTestMellin β 1 − Σ' n(ρ) · pairTestMellin β ρ)`.
This is the cleanest algebraic recombination at the asymptotic level;
the residue-side cancellation composes externally via B4 / 4a'-B4.

The resulting identity matches the shape of the full rectangle boundary
balance — it equals the LHS of `finite_T_boundary_balance_via_integrands`
once both vertical edges are written in `arch + reflected` form — so
this is a genuine asymptotic statement about the full boundary balance.
-/

noncomputable section

open Complex MeasureTheory

namespace ZD
namespace WeilPositivity
namespace PairTestIdentity

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZetaDefs

/-- **Combined asymptotic boundary identity in arch+reflected form.**

Along good heights `T → ∞`,
```
( (∫bot − ∫top) + (I • ∫right_archform − I • ∫left_archform) )
  → 2πi · (pairTestMellin β 1 − Σ' n(ρ) · pairTestMellin β ρ),
```
where:

* `∫bot − ∫top` is the bottom-minus-top horizontal edge difference of
  `weilIntegrand (pairTestMellin β)` over `Re s ∈ [-1, 2]` at height `±T`,
* `∫right_archform = ∫_(-T)^T (archIntegrand β 2 + reflectedPrimeIntegrand β 2)`,
* `∫left_archform  = ∫_(-T)^T (archIntegrand β (-1) + reflectedPrimeIntegrand β (-1))`.

This is a pure triangle-inequality combination of
`verticalEdgeDifference_limit_archForm` and `horizontalEdgeDifference_vanishes`;
no residue-side cancellation is invoked. -/
theorem fullBoundaryBalance_archForm_asymp
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖(((∫ x : ℝ in (-1 : ℝ)..2,
              weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in (-1 : ℝ)..2,
                weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))) +
            (I • (∫ y : ℝ in (-T : ℝ)..T,
                    archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y) -
              I • (∫ y : ℝ in (-T : ℝ)..T,
                    archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y))) -
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (((Classical.choose
                (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
                : ℕ) : ℂ)) *
              pairTestMellin β ρ.val)‖ < ε := by
  intro ε hε
  -- Use ε/2 for each component.
  obtain ⟨T_vert, hT_vert_pos, hT_vert⟩ :=
    verticalEdgeDifference_limit_archForm β hβ (ε / 2) (by linarith)
  obtain ⟨T_hor, hT_hor_pos, hT_hor⟩ :=
    horizontalEdgeDifference_vanishes β (ε / 2) (by linarith)
  refine ⟨max T_vert T_hor, lt_of_lt_of_le hT_vert_pos (le_max_left _ _),
    fun T hT hGood => ?_⟩
  have hT_ge_vert : T_vert ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_hor : T_hor ≤ T := le_trans (le_max_right _ _) hT
  -- Vertical-edge bound (in arch+reflected form).
  have h_vert_lt :
      ‖(I • (∫ y : ℝ in (-T : ℝ)..T,
              archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y) -
          I • (∫ y : ℝ in (-T : ℝ)..T,
              archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y)) -
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (((Classical.choose
                (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
                : ℕ) : ℂ)) *
              pairTestMellin β ρ.val)‖ < ε / 2 :=
    hT_vert T hT_ge_vert hGood
  -- Horizontal-edge bound.
  have h_hor_lt :
      ‖(∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ < ε / 2 :=
    hT_hor T hT_ge_hor hGood
  -- Abbreviations.
  set bot := ∫ x : ℝ in (-1 : ℝ)..2,
      weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I) with hbot_def
  set top := ∫ x : ℝ in (-1 : ℝ)..2,
      weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I) with htop_def
  set rArch := ∫ y : ℝ in (-T : ℝ)..T,
      archIntegrand β 2 y + reflectedPrimeIntegrand β 2 y with hrArch_def
  set lArch := ∫ y : ℝ in (-T : ℝ)..T,
      archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y with hlArch_def
  set R : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I *
      (pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
            : ℕ) : ℂ)) *
          pairTestMellin β ρ.val) with hR_def
  -- Goal in abbreviated form: ‖((bot - top) + (I•rArch - I•lArch)) - R‖ < ε
  -- h_vert_lt : ‖(I•rArch - I•lArch) - R‖ < ε/2
  -- h_hor_lt  : ‖bot - top‖ < ε/2
  -- Algebraic identity:
  --   ((bot - top) + (I•rArch - I•lArch)) - R
  --     = (bot - top) + ((I•rArch - I•lArch) - R)
  have h_rearrange :
      (((bot - top) + (I • rArch - I • lArch)) - R)
        = (bot - top) + ((I • rArch - I • lArch) - R) := by ring
  rw [h_rearrange]
  calc ‖(bot - top) + ((I • rArch - I • lArch) - R)‖
      ≤ ‖bot - top‖ + ‖(I • rArch - I • lArch) - R‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

#print axioms fullBoundaryBalance_archForm_asymp

end PairTestIdentity
end WeilPositivity
end ZD
