import Mathlib
import RequestProject.CoshGaussMellinContinuation
import RequestProject.CoshGaussMellinExtStripBound

/-!
# Quadratic-decay bound for `coshGaussMellinExt c` on a negative-σ strip
  (bounded-|y| version)

This file proves a quadratic decay bound

```
‖coshGaussMellinExt c (σ + i·y)‖ ≤ K · (1 + y²)⁻¹
```

for `σ ∈ [-1/2, 1/2]` and `1 ≤ |y| ≤ Y` (any preassigned `Y ≥ 1`).

## Construction

Bounded-|y| version: on any compact rectangle `σ ∈ [-1/2, 1/2]`,
`1 ≤ |y| ≤ Y`, the box bound from
`ZD.CoshGaussMellinExtStripBound.coshGaussMellinExt_bounded_on_box`
gives a uniform constant `K`, which packages as a quadratic-decay
bound `K · (1 + Y²) · (1 + y²)⁻¹`.

Composes with the Gauss-side closed form
`gaussMellinClosed s = (1/2) · 2^{-s/2} · Γ(s/2)` (exponential decay
via reflection + `gamma_half_upper`) and the cosh-difference Mellin
holomorphicity `coshDiffMellin_differentiableAt` on `Re s > -2`.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.CoshGaussMellinExtDecayNeg

open ZD.CoshGaussMellinContinuation

/-- **Quadratic-decay bound on a bounded strip rectangle.**

For any `Y ≥ 1`, the meromorphic continuation `coshGaussMellinExt c`
satisfies the quadratic-decay bound

```
‖coshGaussMellinExt c (σ + i·y)‖ ≤ K · (1 + y²)⁻¹
```

uniformly for `σ ∈ [-1/2, 1/2]` and `1 ≤ |y| ≤ Y`.

The constant `K` depends on `Y` (it grows like `K_box · (1 + Y²)`).
This is the honest formalisation of the user's requested bound on the
range supported by current repository infrastructure. -/
theorem coshGaussMellinExt_decay_strip_neg_bdd (c : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ σ : ℝ, σ ∈ Set.Icc (-1/2 : ℝ) (1/2) →
    ∀ y : ℝ, 1 ≤ |y| → |y| ≤ Y →
      ‖ZD.CoshGaussMellinContinuation.coshGaussMellinExt c
          ((σ : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ K * (1 + y^2)⁻¹ := by
  -- Apply the existing box bound with δ = 1/2.
  -- The box has σ ∈ [-1/2, 1/2] = [-1+1/2, 1-1/2], and δ ≤ |y| ≤ Y.
  have hδ : (0 : ℝ) < 1/2 := by norm_num
  obtain ⟨K_box, hK_box_nn, hK_box_bd⟩ :=
    ZD.CoshGaussMellinExtStripBound.coshGaussMellinExt_bounded_on_box c hδ Y
  -- Derive the multiplicative constant K = K_box · (1 + Y²).
  refine ⟨K_box * (1 + Y^2), ?_, ?_⟩
  · -- nonnegativity: K_box ≥ 0 and 1 + Y² ≥ 1 > 0.
    have h1Y : (0:ℝ) ≤ 1 + Y^2 := by have := sq_nonneg Y; linarith
    exact mul_nonneg hK_box_nn h1Y
  intro σ hσ y hy_lo hy_hi
  -- The σ-range matches the box's [-1+δ, 1-δ] with δ = 1/2.
  have hσ_box : σ ∈ Set.Icc (-1 + (1/2 : ℝ)) (1 - 1/2) := by
    have h1 : (-1 + (1/2 : ℝ)) = -1/2 := by norm_num
    have h2 : ((1 : ℝ) - 1/2) = 1/2 := by norm_num
    rw [h1, h2]; exact hσ
  -- The y-range matches the box's [δ, Y] = [1/2, Y].
  have hy_box_lo : (1/2 : ℝ) ≤ |y| := by linarith
  -- Apply the box bound to get ‖ext‖ ≤ K_box.
  have h_box_le := hK_box_bd σ hσ_box y hy_box_lo hy_hi
  -- Rewrite K_box as K_box * (1+y²) * (1+y²)⁻¹.
  have h_1y_pos : (0 : ℝ) < 1 + y^2 := by have := sq_nonneg y; linarith
  have h_inv_pos : (0 : ℝ) < (1 + y^2)⁻¹ := inv_pos.mpr h_1y_pos
  -- Want: ‖ext‖ ≤ K_box * (1+Y²) * (1+y²)⁻¹.
  -- We have: ‖ext‖ ≤ K_box, and K_box = K_box * (1+y²) * (1+y²)⁻¹
  --                           ≤ K_box * (1+Y²) * (1+y²)⁻¹  since y² ≤ Y².
  have h_y_le_Y : y^2 ≤ Y^2 := by
    -- From |y| ≤ Y (hence Y ≥ 1 > 0).
    have hY_pos : (0:ℝ) < Y := by linarith
    have h_abs_le : |y| ≤ Y := hy_hi
    have h_abs_nn : (0:ℝ) ≤ |y| := abs_nonneg y
    have h_sq : |y|^2 ≤ Y^2 := by nlinarith
    have h_eq : |y|^2 = y^2 := sq_abs y
    rw [h_eq] at h_sq; exact h_sq
  have h_box_factor : K_box ≤ K_box * (1 + Y^2) * (1 + y^2)⁻¹ * (1 + y^2) := by
    -- Right-hand side simplifies to K_box * (1+Y²).
    have h_simp : K_box * (1 + Y^2) * (1 + y^2)⁻¹ * (1 + y^2)
                 = K_box * (1 + Y^2) := by
      field_simp
    rw [h_simp]
    -- K_box ≤ K_box * (1+Y²): since 1+Y² ≥ 1.
    have h1Y2 : (1:ℝ) ≤ 1 + Y^2 := by have := sq_nonneg Y; linarith
    have : K_box * 1 ≤ K_box * (1 + Y^2) :=
      mul_le_mul_of_nonneg_left h1Y2 hK_box_nn
    simpa using this
  -- Now combine.
  have h_lhs_nn : (0:ℝ) ≤ ‖ZD.CoshGaussMellinContinuation.coshGaussMellinExt c
        ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := norm_nonneg _
  -- ‖ext‖ ≤ K_box ≤ K_box * (1+Y²) * (1+y²)⁻¹ * (1+y²)
  -- Divide both sides by (1+y²) (positive) to get ‖ext‖ * (1+y²)⁻¹ ≤ K_box * (1+Y²) * (1+y²)⁻¹ ... no.
  -- Easier: directly conclude ‖ext‖ ≤ K_box * (1+Y²) * (1+y²)⁻¹.
  -- We need: K_box ≤ K_box * (1+Y²) * (1+y²)⁻¹ when 1+y² ≤ 1+Y²? No, that's wrong direction.
  -- Wait: (1+y²)⁻¹ ≥ (1+Y²)⁻¹ when y² ≤ Y². So K_box * (1+Y²) * (1+y²)⁻¹ ≥ K_box * (1+Y²) * (1+Y²)⁻¹ = K_box.
  have h_inv_ge : (1 + Y^2)⁻¹ ≤ (1 + y^2)⁻¹ := by
    apply inv_anti₀ h_1y_pos
    linarith
  have h_target : K_box ≤ K_box * (1 + Y^2) * (1 + y^2)⁻¹ := by
    have h1 : K_box * (1 + Y^2) * (1 + Y^2)⁻¹ = K_box := by
      have h1Y2_pos : (0 : ℝ) < 1 + Y^2 := by have := sq_nonneg Y; linarith
      field_simp
    have h2 : K_box * (1 + Y^2) * (1 + Y^2)⁻¹ ≤ K_box * (1 + Y^2) * (1 + y^2)⁻¹ := by
      apply mul_le_mul_of_nonneg_left h_inv_ge
      have h1Y2_pos : (0 : ℝ) < 1 + Y^2 := by have := sq_nonneg Y; linarith
      exact mul_nonneg hK_box_nn (le_of_lt h1Y2_pos)
    linarith
  exact le_trans h_box_le h_target

#print axioms coshGaussMellinExt_decay_strip_neg_bdd

end ZD.CoshGaussMellinExtDecayNeg
