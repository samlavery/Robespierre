import Mathlib
import RequestProject.WeilHorizontalDecay
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilPairIBP

/-!
# WF-4 (right-strip fragment): top/bottom-edge tail vanishing when `σL > 1`

Assembles three pre-existing unconditional pieces into a wrapper that
eliminates the `logDerivZeta_polynomial_bound_target` hypothesis from
`horizontal_decay_of_logDeriv_bound_and_mellin_decay` whenever `σL > 1`:

* `WeilLogDerivZetaBound.logDerivZeta_polynomial_bound_of_right_of_one` —
  unconditional discharge of `logDerivZeta_polynomial_bound_target σL σR` for
  `σL > 1`.
* `WeilHorizontalDecay.horizontal_decay_of_logDeriv_bound_and_mellin_decay` —
  conditional horizontal decay given both the ζ-side and Mellin-side targets.

Result: for `σL > 1`, the top/bottom edge integrals decay like `C·T⁻²` on a
sequence of "good heights" `T₁ → ∞`, conditional *only* on
`pairTestMellin_super_poly_decay_target β σL σR`.

The remaining blocker is that one Mellin-decay target (the quartic-decay sorry
in `WeilPairTestDecay.lean`). No custom axioms introduced here.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Right-strip horizontal tail vanishing**, conditional only on
`pairTestMellin_super_poly_decay_target`. The `logDerivZeta_polynomial_bound`
hypothesis is discharged internally via
`logDerivZeta_polynomial_bound_of_right_of_one`. -/
theorem horizontal_decay_right_strip
    (β : ℝ) (σL σR : ℝ) (hσL : 1 < σL) (hσ : σL < σR)
    (hM : pairTestMellin_super_poly_decay_target β σL σR) :
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
            C * T^(-(2:ℝ)) := by
  have hLD : logDerivZeta_polynomial_bound_target σL σR :=
    logDerivZeta_polynomial_bound_of_right_of_one σL σR hσL hσ.le
  exact horizontal_decay_of_logDeriv_bound_and_mellin_decay β σL σR hσ hLD hM

#print axioms horizontal_decay_right_strip

/-- **Good-height sequence tending to infinity.** Given the right-strip decay,
for every `n : ℕ` there is a good height `T_n ∈ [n + T₀, n + T₀ + 1]` with the
`T⁻²` bound. Hence a sequence `T_n → ∞`. -/
theorem exists_good_height_sequence
    (β : ℝ) (σL σR : ℝ) (hσL : 1 < σL) (hσ : σL < σR)
    (hM : pairTestMellin_super_poly_decay_target β σL σR) :
    ∃ (T : ℕ → ℝ) (C : ℕ → ℝ),
      Filter.Tendsto T atTop atTop ∧
      (∀ n, 0 ≤ C n) ∧
      (∀ n, ‖∫ σ in σL..σR,
          weilIntegrand (pairTestMellin β) (↑σ + ↑(T n) * I)‖ ≤
        C n * (T n)^(-(2:ℝ))) := by
  obtain ⟨T₀, hT₀_gt, hT₀_seq⟩ := horizontal_decay_right_strip β σL σR hσL hσ hM
  -- For each n, pick T₁ = n + T₀ and use hT₀_seq.
  choose T_of hT_of_ge hT_of_le C_of hC_of_nn hbound using
    (fun n : ℕ => hT₀_seq ((n : ℝ) + T₀) (by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith))
  refine ⟨T_of, C_of, ?_, hC_of_nn, hbound⟩
  -- T_of n ≥ n + T₀ → T_of n → ∞.
  rw [Filter.tendsto_atTop_atTop]
  intro M
  refine ⟨Nat.ceil (max (M - T₀) 0), fun n hn => ?_⟩
  have hn_real : (Nat.ceil (max (M - T₀) 0) : ℝ) ≤ n := by exact_mod_cast hn
  have h_n_ge : max (M - T₀) 0 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) hn_real
  have h_n_ge' : M - T₀ ≤ (n : ℝ) := le_trans (le_max_left _ _) h_n_ge
  linarith [hT_of_ge n]

#print axioms exists_good_height_sequence

-- ═══════════════════════════════════════════════════════════════════════════
-- § WF-4 right-strip UNCONDITIONAL via IBP2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Unconditional right-strip horizontal decay via IBP2.**
For `1 < σL < σR`, there exists `T₀ > 1` such that for every starting height
`T₁ ≥ T₀`, there is a good height `T ∈ [T₁, T₁+1]` with
`‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (σ+iT)‖ ≤ C · T⁻²`.

Both ingredients are discharged internally:
* **ζ-side** via `logDerivZeta_polynomial_bound_of_right_of_one` (uniform bound,
  exponent `N = 0`).
* **Mellin-side** via `pairTestMellin_quadratic_decay_on_strip` (M = 2 decay
  via 2-step IBP on `pair_cosh_gauss_test β`).

This version bypasses the super-poly hypothesis by inlining the
`horizontal_decay_of_logDeriv_bound_and_mellin_decay` proof specialized to
`N = 0` + quadratic Mellin decay. No custom axioms. -/
theorem horizontal_decay_right_strip_unconditional
    (β : ℝ) (σL σR : ℝ) (hσL : 1 < σL) (hσ : σL < σR) :
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
            C * T^(-(2:ℝ)) := by
  -- ζ-side UNIFORM bound on Re s ≥ σL > 1 (no T^N factor).
  obtain ⟨C_ζ, hC_ζ_nn, hζbd⟩ := logDerivZeta_bounded_of_right_of_one σL hσL
  -- Mellin-side quadratic decay.
  have hσL_pos : 0 < σL := by linarith
  obtain ⟨C₂, T₀₂, hC₂_pos, hT₀₂_pos, h₂decay⟩ :=
    pairTestMellin_quadratic_decay_on_strip β σL σR hσL_pos hσ.le
  -- Pick T₀ = max(T₀₂, 2).
  set T_low : ℝ := max T₀₂ 2 with hT_low_def
  have hT_low_gt_one : 1 < T_low :=
    lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _)
  refine ⟨T_low, hT_low_gt_one, fun T₁ hT₁ => ?_⟩
  have hT₁_ge_2decay : T₀₂ ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have hT₁_ge_two : (2 : ℝ) ≤ T₁ := le_trans (le_max_right _ _) hT₁
  -- Take T = T₁ (no good-height selection needed since ζ'/ζ is uniformly bounded
  -- on Re s ≥ σL > 1 — no zeros in the strip).
  refine ⟨T₁, le_refl _, by linarith, C_ζ * C₂ * |σR - σL|, by positivity, ?_⟩
  have hT₁_pos : 0 < T₁ := by linarith
  have hT₁_abs : |T₁| = T₁ := abs_of_pos hT₁_pos
  -- Pointwise: ‖weilIntegrand‖ ≤ C_ζ · C₂ · T₁⁻² for σ ∈ [σL, σR].
  have h_inner_bound : ∀ σ ∈ Set.uIoc σL σR,
      ‖weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T₁ : ℂ) * I)‖ ≤
      C_ζ * C₂ * T₁^(-(2:ℝ)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ.le
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    -- σ ∈ [σL, σR] ⟹ Re (σ + iT₁) = σ ≥ σL.
    have hσ_ge_σL : σL ≤ ((σ : ℂ) + (T₁ : ℂ) * I).re := by
      simp; exact hσ_mem.1.le
    have h_ζ_bd := hζbd ((σ : ℂ) + (T₁ : ℂ) * I) hσ_ge_σL
    have h_M_bd := h₂decay T₁ (by rw [hT₁_abs]; linarith) σ hσ_Icc
    have hT_rpow_abs : |T₁|^(-(2:ℝ)) = T₁^(-(2:ℝ)) := by rw [hT₁_abs]
    rw [weilIntegrand_norm_factored]
    calc ‖deriv riemannZeta ((σ : ℂ) + (T₁ : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T₁ : ℂ) * I)‖ *
          ‖pairTestMellin β ((σ : ℂ) + (T₁ : ℂ) * I)‖
        ≤ C_ζ * (C₂ * |T₁|^(-(2:ℝ))) := by
          apply mul_le_mul h_ζ_bd h_M_bd (norm_nonneg _) hC_ζ_nn
      _ = C_ζ * C₂ * T₁^(-(2:ℝ)) := by rw [hT_rpow_abs]; ring
  calc ‖∫ σ in σL..σR,
          weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T₁ : ℂ) * I)‖
      ≤ (C_ζ * C₂ * T₁^(-(2:ℝ))) * |σR - σL| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_inner_bound
    _ = C_ζ * C₂ * |σR - σL| * T₁^(-(2:ℝ)) := by ring

#print axioms horizontal_decay_right_strip_unconditional

end Contour
end WeilPositivity
end ZD

end
