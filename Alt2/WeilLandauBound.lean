import Mathlib
import RequestProject.WeilLogDerivZetaBound

/-!
# Landau-style log-derivative bound for `ζ'/ζ(σ₀+iT)` at σ₀ = 2

Classical Landau estimate says: for large `T` there exists `σ₀ ∈ [1, 2]` with
`‖ζ'/ζ(σ₀+iT)‖ ≤ C · (log T)²`. Proofs in the literature go via:
(a) zero-count bound `N(T+1) − N(T−1) = O(log T)` (Jensen),
(b) partial-fraction expansion of `ζ'/ζ` (Hadamard product),
(c) pigeonhole to pick `σ₀` away from all nearby zero real-parts.

**Simplification.** At `σ₀ = 2` specifically, zeros lie strictly to the left
(`Re ρ < 1 < 2`), so every nearby zero contributes at most `1/(σ₀ − Re ρ) ≤ 1`.
More directly, `ζ'/ζ(2+iT) = −LSeries_Λ(2+iT)` is uniformly bounded on
`Re s ≥ 2 > 1` by absolute convergence of the von Mangoldt Dirichlet series.

This makes the constant bound `≤ C_L` strictly stronger than the classical
`C · (log T)²` at the specific choice `σ₀ = 2`. Neither Jensen nor Hadamard
is required.

## Delivered

* `landau_logDeriv_bound_at_two` — `‖ζ'/ζ(2+iT)‖ ≤ C` uniform in T.
* `landau_logDeriv_bound` — classical form `∃ σ₀ ∈ [1,2], ‖ζ'/ζ‖ ≤ C·(log T)²`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set

noncomputable section

namespace ZD.WeilPositivity.Contour

/-- **Direct bound on `ζ'/ζ(2+iT)` uniformly in T.** From LSeries absolute
convergence at `Re s = 2 > 1`: `|LSeries_Λ(2+iT)| ≤ ∑ Λ(n)/n^2 = -ζ'(2)/ζ(2)`.
Combined with the identity `LSeries_Λ = -ζ'/ζ` on `Re s > 1`, this uniformly
bounds `ζ'/ζ` on the vertical line `Re s = 2`. -/
theorem landau_logDeriv_bound_at_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
      ‖deriv riemannZeta ((2 : ℂ) + (T : ℂ) * I) /
        riemannZeta ((2 : ℂ) + (T : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ := logDerivZeta_bounded_of_right_of_one 2 (by norm_num : (1:ℝ) < 2)
  refine ⟨C, hC_nn, fun T => ?_⟩
  apply hC
  simp

#print axioms landau_logDeriv_bound_at_two

/-- **Landau-style bound** (classical form). For every `T ≥ 2`, there exists
`σ₀ ∈ [1, 2]` such that `‖ζ'/ζ(σ₀ + iT)‖ ≤ C · (log T)²`.

**Proof.** Take `σ₀ = 2`. The uniform bound at `σ₀ = 2` is constant `C`,
and `C ≤ C/(log 2)² · (log T)²` for `T ≥ 2` since `log T ≥ log 2 > 0`. -/
theorem landau_logDeriv_bound :
    ∃ C_L : ℝ, 0 < C_L ∧
      ∀ T : ℝ, 2 ≤ T →
        ∃ σ₀ ∈ Icc (1 : ℝ) 2,
          ‖logDeriv riemannZeta (⟨σ₀, T⟩ : ℂ)‖ ≤ C_L * (Real.log T) ^ 2 := by
  obtain ⟨C, hC_nn, hC⟩ := landau_logDeriv_bound_at_two
  -- Choose C_L = max(C / (log 2)², 1) so both the constant bound holds and C_L > 0.
  set C_L : ℝ := max (C / (Real.log 2)^2) 1 with hCL_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_sq_pos : 0 < (Real.log 2)^2 := by positivity
  have hC_L_pos : 0 < C_L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C_L, hC_L_pos, fun T hT => ⟨2, ?_, ?_⟩⟩
  · exact ⟨by norm_num, le_refl _⟩
  · have h_s_eq : (⟨2, T⟩ : ℂ) = (2 : ℂ) + (T : ℂ) * I := by
      apply Complex.ext <;> simp
    have h_logDeriv : logDeriv riemannZeta (⟨2, T⟩ : ℂ) =
        deriv riemannZeta ((2 : ℂ) + (T : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (T : ℂ) * I) := by
      rw [logDeriv_apply, h_s_eq]
    rw [h_logDeriv]
    have h_const_bd := hC T
    have hlogT_ge : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have hlogT_pos : 0 < Real.log T := lt_of_lt_of_le hlog2_pos hlogT_ge
    have h_sq_le : (Real.log 2)^2 ≤ (Real.log T)^2 :=
      pow_le_pow_left₀ hlog2_pos.le hlogT_ge 2
    -- C ≤ C_L · (log T)²: since C_L ≥ C / (log 2)² and (log T)² ≥ (log 2)²:
    --   C_L · (log T)² ≥ (C/(log 2)²) · (log 2)² = C.
    have h_C_le_CL_sq : C ≤ C_L * (Real.log T)^2 := by
      calc C = (C / (Real.log 2)^2) * (Real.log 2)^2 := by
              field_simp
        _ ≤ C_L * (Real.log 2)^2 := by
              apply mul_le_mul_of_nonneg_right (le_max_left _ _) hlog2_sq_pos.le
        _ ≤ C_L * (Real.log T)^2 :=
              mul_le_mul_of_nonneg_left h_sq_le hC_L_pos.le
    linarith

#print axioms landau_logDeriv_bound

/-- **`logDerivZeta_polynomial_bound_target` discharged at the specific interval
`[σL, 2]` with `σL > 1`.** This integrates the Landau-style bound with our
existing `logDerivZeta_polynomial_bound_of_right_of_one` target discharge. -/
theorem logDerivZeta_polynomial_bound_target_right_strip
    (σL σR : ℝ) (hσL : 1 < σL) (hσR : σL ≤ σR) :
    logDerivZeta_polynomial_bound_target σL σR :=
  logDerivZeta_polynomial_bound_of_right_of_one σL σR hσL hσR

#print axioms logDerivZeta_polynomial_bound_target_right_strip

/-- **HD-1 closure for `σL > 1` using quadratic Mellin decay.**

For Weil rectangles with vertical edges strictly to the right of the critical
line (σL > 1), the log-derivative bound reduces to a uniform constant (LSeries
absolute convergence), so combining with quadratic `pairTestMellin` decay
gives pointwise `|T|^(-2)` decay on the horizontal integrand. -/
theorem weilHorizontalDecay_for_right_strip
    (β : ℝ) (σL σR : ℝ) (hσL : 1 < σL) (hσ : σL < σR)
    (hM2 : ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (T : ℝ), T₀ ≤ |T| → ∀ σ ∈ Set.Icc σL σR,
        ‖pairTestMellin β (↑σ + ↑T * I)‖ ≤ C * |T|^(-(2:ℝ))) :
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
            C * T^(-(2:ℝ)) := by
  obtain ⟨C_ζ, hC_ζ_nn, h_ζ_bd⟩ := logDerivZeta_bounded_of_right_of_one σL hσL
  obtain ⟨C_M, T₀_M, hC_M_pos, hT_M_pos, hM_bd⟩ := hM2
  set T_low : ℝ := max 2 T₀_M with hT_low_def
  have hT_low_gt_one : 1 < T_low := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨T_low, hT_low_gt_one, fun T₁ hT₁ => ?_⟩
  have hT₁_ge_two : (2 : ℝ) ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have hT₁_ge_M : T₀_M ≤ T₁ := le_trans (le_max_right _ _) hT₁
  have hT₁_pos : 0 < T₁ := by linarith
  refine ⟨T₁, le_rfl, by linarith, (C_ζ + 1) * C_M * |σR - σL|, by positivity, ?_⟩
  have hT_abs : |T₁| = T₁ := abs_of_pos hT₁_pos
  have h_inner_bound : ∀ σ ∈ Set.uIoc σL σR,
      ‖weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T₁ : ℂ) * Complex.I)‖ ≤
      (C_ζ + 1) * C_M * T₁^(-(2:ℝ)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ.le
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have hσL_le_re : σL ≤ ((σ : ℂ) + (T₁ : ℂ) * Complex.I).re := by
      have : ((σ : ℂ) + (T₁ : ℂ) * Complex.I).re = σ := by simp
      rw [this]; exact hσ_Icc.1
    have hζbd := h_ζ_bd _ hσL_le_re
    have hMbd := hM_bd T₁ (by rw [hT_abs]; exact hT₁_ge_M) σ hσ_Icc
    rw [hT_abs] at hMbd
    rw [weilIntegrand_norm_factored]
    calc ‖deriv riemannZeta (↑σ + ↑T₁ * Complex.I) /
            riemannZeta (↑σ + ↑T₁ * Complex.I)‖ *
          ‖pairTestMellin β (↑σ + ↑T₁ * Complex.I)‖
        ≤ C_ζ * (C_M * T₁^(-(2:ℝ))) := by
          apply mul_le_mul hζbd hMbd (norm_nonneg _) hC_ζ_nn
      _ ≤ (C_ζ + 1) * (C_M * T₁^(-(2:ℝ))) := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          exact mul_nonneg hC_M_pos.le (Real.rpow_nonneg hT₁_pos.le _)
      _ = (C_ζ + 1) * C_M * T₁^(-(2:ℝ)) := by ring
  calc ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T₁ : ℂ) * Complex.I)‖
      ≤ ((C_ζ + 1) * C_M * T₁^(-(2:ℝ))) * |σR - σL| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_inner_bound
    _ = (C_ζ + 1) * C_M * |σR - σL| * T₁^(-(2:ℝ)) := by ring

#print axioms weilHorizontalDecay_for_right_strip

end ZD.WeilPositivity.Contour

end
