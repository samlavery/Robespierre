import Mathlib
import RequestProject.WeilIdentityAtPairTest
import RequestProject.WeilFinalAssembly

/-!
# Whole-line Weil identity at the cosh-pair-Gauss test

**Step 1f**: composes the proved finite-`T` building blocks into the
unconditional whole-line Weil identity:

```
I·∫_ℝ primeIntegrand β 2 dy − I·∫_ℝ leftEdgeIntegrand β dy
  = 2πi · (pairTestMellin β 1 − Σ' n(ρ)·pairTestMellin β ρ)
```

Proof: triangle-inequality limit-uniqueness, mirroring
`weilFormula_assembly_from_subtargets` (`WeilFinalAssembly.lean:1095`):
* `verticalEdgeDifference_limit` (Step 1c): boundary-form difference → `2πi · (...)` along good heights.
* `rightEdge_integral_tendsto` + `leftEdge_integral_tendsto` (Step 1e): each truncated edge integral converges to the whole-line integral.
* `exists_goodHeight_strong_ge`: pick a good height `T` exceeding all three threshold constants.
* Triangle inequality forces the two limits to coincide.

This is unconditional. No new mathematical content beyond composition of the
proved building blocks.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace PairTestIdentity

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZetaDefs

/-- **Step 1f — whole-line Weil identity at the cosh-pair-Gauss test (unconditional).**

```
I · ∫_ℝ primeIntegrand β 2 dy
  − I · ∫_ℝ (hadamardArchBoundaryTerm(-1+iy) · pairTestMellin β (-1+iy)) dy
= 2πi · (pairTestMellin β 1 − Σ' n(ρ)·pairTestMellin β ρ).
```

Composes Step 1c (residue-side limit along good heights) with Step 1e
(per-edge whole-line integrability, both edges) via triangle inequality
+ existence of arbitrarily large good heights. -/
theorem wholeLineWeilIdentity (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    I • (∫ y : ℝ, primeIntegrand β 2 y) -
    I • (∫ y : ℝ,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
    2 * ((Real.pi : ℝ) : ℂ) * I *
      (pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
          pairTestMellin β ρ.val) := by
  -- Set A = whole-line LHS, B = residue side RHS.
  set A : ℂ := I • (∫ y : ℝ, primeIntegrand β 2 y) -
    I • (∫ y : ℝ,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) with hA_def
  set B : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I *
    (pairTestMellin β 1 -
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        pairTestMellin β ρ.val) with hB_def
  -- Reduce to ‖A - B‖ = 0.
  suffices h_norm_zero : ‖A - B‖ = 0 by
    have h_zero : A - B = 0 := norm_eq_zero.mp h_norm_zero
    exact sub_eq_zero.mp h_zero
  -- By contradiction.
  by_contra hne
  have h_pos : 0 < ‖A - B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  set ε : ℝ := ‖A - B‖ / 2 with hε_def
  have hε_pos : 0 < ε := half_pos h_pos
  -- (1) Step 1c bound: ∃ T₁, ∀ T ≥ T₁ goodHeight, ‖truncated_T - B‖ < ε.
  obtain ⟨T₁, hT₁_pos, hT₁_bd⟩ :=
    verticalEdgeDifference_limit β hβ ε hε_pos
  -- (2) Step 1e right edge: ∫_(-T)^T primeIntegrand → ∫_ℝ primeIntegrand.
  have h_right_eventually :=
    (rightEdge_integral_tendsto β).eventually
      (Metric.ball_mem_nhds _ (half_pos hε_pos))
  rw [Filter.eventually_atTop] at h_right_eventually
  obtain ⟨T₂, hT₂_bd⟩ := h_right_eventually
  -- (3) Step 1e left edge: ∫_(-T)^T leftEdge → ∫_ℝ leftEdge.
  have h_left_eventually :=
    (leftEdge_integral_tendsto β).eventually
      (Metric.ball_mem_nhds _ (half_pos hε_pos))
  rw [Filter.eventually_atTop] at h_left_eventually
  obtain ⟨T₃, hT₃_bd⟩ := h_left_eventually
  -- Pick good height T ≥ max(T₁, T₂, T₃).
  obtain ⟨T, hT_ge, hGood⟩ :=
    exists_goodHeight_strong_ge (max T₁ (max T₂ T₃))
  have hT_ge_T₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT_ge
  have hT_ge_T₂ : T₂ ≤ T :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT_ge)
  have hT_ge_T₃ : T₃ ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT_ge)
  -- Apply bounds at T.
  have h_1c : ‖(I • (∫ y : ℝ in (-T : ℝ)..T, primeIntegrand β 2 y) -
                  I • (∫ y : ℝ in (-T : ℝ)..T,
                        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
                        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) - B‖ < ε :=
    hT₁_bd T hT_ge_T₁ hGood
  have h_right_close_raw := hT₂_bd T hT_ge_T₂
  have h_left_close_raw := hT₃_bd T hT_ge_T₃
  -- Convert dist to norm.
  rw [dist_eq_norm] at h_right_close_raw h_left_close_raw
  -- h_right_close_raw : ‖∫_(-T)^T primeIntegrand - ∫_ℝ primeIntegrand‖ < ε/2
  -- h_left_close_raw : ‖∫_(-T)^T leftEdge - ∫_ℝ leftEdge‖ < ε/2
  -- Truncated form close to A.
  set right_T : ℂ := ∫ y : ℝ in (-T : ℝ)..T, primeIntegrand β 2 y with hright_T_def
  set left_T : ℂ := ∫ y : ℝ in (-T : ℝ)..T,
      hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hleft_T_def
  set right_inf : ℂ := ∫ y : ℝ, primeIntegrand β 2 y with hright_inf_def
  set left_inf : ℂ := ∫ y : ℝ,
      hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hleft_inf_def
  -- Norms of I • _.
  have h_smul_norm_right : ‖I • right_T - I • right_inf‖ = ‖right_T - right_inf‖ := by
    rw [← smul_sub, norm_smul, Complex.norm_I, one_mul]
  have h_smul_norm_left : ‖I • left_T - I • left_inf‖ = ‖left_T - left_inf‖ := by
    rw [← smul_sub, norm_smul, Complex.norm_I, one_mul]
  -- Bound ‖truncated - A‖.
  have h_truncated_close_A :
      ‖(I • right_T - I • left_T) - A‖ < ε := by
    have hA_expand : A = I • right_inf - I • left_inf := by
      simp [hA_def, hright_inf_def, hleft_inf_def]
    rw [hA_expand]
    have h_diff_eq : (I • right_T - I • left_T) - (I • right_inf - I • left_inf) =
        (I • right_T - I • right_inf) - (I • left_T - I • left_inf) := by ring
    rw [h_diff_eq]
    calc ‖(I • right_T - I • right_inf) - (I • left_T - I • left_inf)‖
        ≤ ‖I • right_T - I • right_inf‖ + ‖I • left_T - I • left_inf‖ :=
          norm_sub_le _ _
      _ = ‖right_T - right_inf‖ + ‖left_T - left_inf‖ := by
          rw [h_smul_norm_right, h_smul_norm_left]
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- Triangle: ‖A - B‖ ≤ ‖A - truncated‖ + ‖truncated - B‖ < ε + ε = 2ε = ‖A-B‖.
  have h_triangle : ‖A - B‖ < 2 * ε := by
    have h_eq : A - B = (A - (I • right_T - I • left_T)) +
                        ((I • right_T - I • left_T) - B) := by ring
    have h_left_to_right : ‖A - (I • right_T - I • left_T)‖ =
                            ‖(I • right_T - I • left_T) - A‖ := by
      rw [← norm_neg]; congr 1; ring
    calc ‖A - B‖
        = ‖(A - (I • right_T - I • left_T)) +
            ((I • right_T - I • left_T) - B)‖ := by rw [← h_eq]
      _ ≤ ‖A - (I • right_T - I • left_T)‖ +
          ‖(I • right_T - I • left_T) - B‖ := norm_add_le _ _
      _ = ‖(I • right_T - I • left_T) - A‖ +
          ‖(I • right_T - I • left_T) - B‖ := by rw [h_left_to_right]
      _ < ε + ε := by linarith
      _ = 2 * ε := by ring
  -- 2ε = ‖A - B‖, so ‖A - B‖ < ‖A - B‖, contradiction.
  have h_2eps : 2 * ε = ‖A - B‖ := by rw [hε_def]; ring
  rw [h_2eps] at h_triangle
  exact lt_irrefl _ h_triangle

end PairTestIdentity
end WeilPositivity
end ZD

end
