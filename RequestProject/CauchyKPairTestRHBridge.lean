import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.CauchyKPairTestComplexK
import RequestProject.CauchyKPairTestK2Final
import RequestProject.CauchyKPairTestResidueSum
import RequestProject.WeilZeroOrthogonality
import RequestProject.ZeroCoefficientVanishesUnconditional

/-!
# RH bridge: K-twisted vanishing + weighted uniqueness ⟹ critical line

Composes the strip-root lemma `K_zeros_in_strip_force_critical_line` with a
*weighted* zero-coefficient uniqueness target. The standard
`ZeroCoefficientVanishesByOrthogonality` requires `Σ' ‖a ρ‖ < ∞`, which fails
for `a = n·K` because `K` has a nonzero constant floor as `|Im ρ| → ∞`
(`K(ρ) → π√(π/2)`), so `Σ' n(ρ)·‖K(ρ)‖` diverges.

The correct uniqueness hypothesis for this application is *per-β* absolute
summability of the Mellin pairings, not unweighted ℓ¹ on `a` itself:

```
WeightedZeroCoefficientVanishesByOrthogonality :=
  ∀ a, (∀β ∈ (0,1), Summable (ρ ↦ ‖a ρ · M(β,ρ)‖))
     → (∀β ∈ (0,1), ∑' ρ, a ρ · M(β,ρ) = 0)
     → ∀ ρ ∈ NontrivialZeros, a ρ = 0
```

Composing:

* **K-twisted Weil identity** (proved unconditionally,
  `rectContourIntegral_K_pairTestMellin_T_limit_unconditional`).
* **Per-β summability** (proved unconditionally,
  `K_pairTestMellin_zeroSum_summable_holds`).
* **Engineering identity** `Σ' n·K·M(β,_) = 0 ∀β ∈ (0,1)`: open, RH-strength.
* **Weighted uniqueness** `WeightedZeroCoefficientVanishesByOrthogonality_holds`:
  open. The existing `ZeroCoefficientVanishesByOrthogonality_holds` is too
  strong (requires `Σ' ‖a‖ < ∞`); a weighted refactor of
  `mellin_series_vanishes_from_integral_vanishing` is needed.
* **Strip-root** `K_zeros_in_strip_force_critical_line` (proved).

Bridge conclusion: every nontrivial zero has `Re ρ = 1/2`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]` modulo the two
open inputs above.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch

/-! ## Weighted zero-coefficient uniqueness target -/

/-- **Weighted zero-coefficient uniqueness.**

Replaces the unweighted ℓ¹ hypothesis `Summable (ρ ↦ ‖a ρ‖)` by per-β absolute
summability of the Mellin pairings `Σ' ‖a ρ · pairTestMellin β ρ‖`. This is
the natural transform-side condition: the test family `{pairTestMellin β}_{β ∈ (0,1)}`
provides the decay weight that makes the sum converge, and the orthogonality
extraction should consume only that weighted information.

The standard `ZeroCoefficientVanishesByOrthogonality` consumes the stronger
unweighted ℓ¹ hypothesis on `a` itself; for coefficients `a = n·K` where `K`
has a constant floor (does not decay over zeros), only this weighted form is
satisfiable. -/
def WeightedZeroCoefficientVanishesByOrthogonality : Prop :=
  ∀ (a : ℂ → ℂ),
    (∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖a ρ.val * Contour.pairTestMellin β ρ.val‖))
    →
    (∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-! ## Multiplicity is positive at nontrivial zeros -/

/-- The canonical multiplicity at a nontrivial zero is at least `1`. -/
private lemma nMult_pos_at_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    1 ≤ Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) := by
  have hspec :=
    Classical.choose_spec
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
  exact hspec.1

/-! ## Engineering-identity Prop -/

/-- The K-twisted per-β vanishing target: the engineering identity that needs
to be discharged unconditionally. Folding `Σ' n·K·M(β,ρ) = 0 ∀β ∈ (0,1)`. -/
def K_complex_zeroSum_vanishes : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 →
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
      gaussianDefectEntireKernel_local ρ.val *
      Contour.pairTestMellin β ρ.val = 0

/-! ## The bridge -/

/-- **Critical-line bridge** (conditional on the engineering identity and the
weighted uniqueness target).

Composes:
1. The K-twisted per-β vanishing identity `K_complex_zeroSum_vanishes`.
2. Per-β absolute summability of the K-weighted Mellin pairings (already
   proved unconditionally via `K_pairTestMellin_zeroSum_summable_holds`).
3. Weighted zero-coefficient uniqueness `WeightedZeroCoefficientVanishesByOrthogonality`.
4. The strip-root lemma `K_zeros_in_strip_force_critical_line`.

Conclusion: every nontrivial zero `ρ` has `Re ρ = 1/2`. -/
theorem critical_line_of_K_complex_zeroSum_vanishes
    (h_eng : K_complex_zeroSum_vanishes)
    (h_uniqueness : WeightedZeroCoefficientVanishesByOrthogonality) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1/2 := by
  classical
  intro ρ hρ
  -- Define a := n · K.
  set a : ℂ → ℂ := fun ρ : ℂ =>
    if hρ : ρ ∈ NontrivialZeros then
      ((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) : ℕ) : ℂ) *
        gaussianDefectEntireKernel_local ρ
    else 0 with ha_def
  -- Per-β: ‖a ρ · M(β,ρ)‖ summable (from K_pairTestMellin_zeroSum_summable_holds).
  have h_aM_summable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        ‖a ρ.val * Contour.pairTestMellin β ρ.val‖) := by
    intro β _ _
    have h_summ := K_pairTestMellin_zeroSum_summable_holds β
    unfold K_pairTestMellin_zeroSum_summable at h_summ
    have h_norm := h_summ.norm
    refine h_norm.congr (fun ρ => ?_)
    have hρ_NTZ : ρ.val ∈ NontrivialZeros := ρ.property
    have h_a_eq : a ρ.val =
        ((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
        gaussianDefectEntireKernel_local ρ.val := by
      simp [ha_def, hρ_NTZ]
    have h_choice_eq : ((fun ρ : ℂ => if hρ : ρ ∈ NontrivialZeros then
        Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
        else 0) ρ.val : ℕ) =
        Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) := by
      simp [hρ_NTZ]
    rw [h_a_eq, h_choice_eq]
  -- Per-β: Σ' a ρ · M(β,ρ) = 0 (engineering identity).
  have h_aM_vanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0 := by
    intro β hβ_pos hβ_lt
    have h_eng_β := h_eng β hβ_pos hβ_lt
    refine (tsum_congr (fun ρ => ?_)).trans h_eng_β
    have hρ_NTZ : ρ.val ∈ NontrivialZeros := ρ.property
    have h_a_eq : a ρ.val =
        ((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
        gaussianDefectEntireKernel_local ρ.val := by
      simp [ha_def, hρ_NTZ]
    rw [h_a_eq]
  -- Apply weighted uniqueness: a ρ = 0.
  have h_a_zero : a ρ = 0 := h_uniqueness a h_aM_summable h_aM_vanish ρ hρ
  -- a ρ = n · K(ρ). Since n ≥ 1 (positive integer cast nonzero),
  -- we get K(ρ) = 0.
  have h_a_eq_at_ρ : a ρ =
      ((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) : ℕ) : ℂ) *
      gaussianDefectEntireKernel_local ρ := by
    simp [ha_def, hρ]
  rw [h_a_eq_at_ρ] at h_a_zero
  have h_n_pos := nMult_pos_at_nontrivialZero hρ
  have h_n_ne : ((Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) : ℕ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℕ) <
        Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) := by
      exact lt_of_lt_of_le Nat.zero_lt_one h_n_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  have h_K_zero : gaussianDefectEntireKernel_local ρ = 0 := by
    rcases mul_eq_zero.mp h_a_zero with h | h
    · exact absurd h h_n_ne
    · exact h
  exact K_zeros_in_strip_force_critical_line hρ h_K_zero

/-! ## Statement of the open obligations -/

/-- The two open obligations remaining for unconditional RH via this bridge:

1. `K_complex_zeroSum_vanishes`: the engineering identity
   `∑' ρ, n(ρ) · K(ρ) · M(β,ρ) = 0` for all `β ∈ (0,1)`.
   Open. RH-strength. The candidate route uses the K_2 + Plancherel +
   Gaussian-moment chain.

2. `WeightedZeroCoefficientVanishesByOrthogonality`: weighted uniqueness.
   The standard `ZeroCoefficientVanishesByOrthogonality_holds` requires
   unweighted `Σ' ‖a ρ‖ < ∞`, which fails for `a = n·K`.

   To prove this weighted form, refactor
   `mellin_series_vanishes_from_integral_vanishing` (and its supporting
   pieces `zeroMellinSeries_norm_le_*`, `zeroMellinSeries_continuousOn_Ioi`,
   `swap_eq`) to consume per-β `Σ' ‖a ρ · M(β,ρ)‖ < ∞` instead of
   `Σ' ‖a ρ‖ < ∞`. The Fubini swap currently uses `realMellin β` (real-axis
   Mellin) as a bounded-below weight, which forces Σ' ‖a‖ summability; the
   refactored swap should use the actual contour-side bound directly. -/
def open_obligations_summary : Prop :=
  K_complex_zeroSum_vanishes ∧ WeightedZeroCoefficientVanishesByOrthogonality

#print axioms critical_line_of_K_complex_zeroSum_vanishes

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
