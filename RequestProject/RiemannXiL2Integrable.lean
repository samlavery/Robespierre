import Mathlib
import RequestProject.RiemannXiDecay
import RequestProject.ZetaStripBound
import RequestProject.ThetaTransport

/-!
# L² Integrability of `riemannXi` on Vertical Lines in the Strip — Unconditional

This file closes the `riemannXi_L2_integrable_target σ` target from
`RiemannXiDecay.lean` **unconditionally** for every `σ ∈ (0, 1)`.

## Chain

1. `ZD.StripBound.zetaPolynomialBoundInStrip_from_euler_maclaurin`
   (unconditional, from Euler–Maclaurin).
2. `ZD.riemannXi_vertical_decay_of_zetaBound` feeds (1) into an
   exp-decay bound on `‖ξ(σ + iγ)‖`.
3. `ZD.riemannXi_normSq_tail_bound_of_decay` squares to
   `normSq ξ(σ + iγ) ≤ K · |γ|^(2M) · exp(-π|γ|/2)` eventually.
4. `normSq ξ =O[atTop] exp(-π·γ/4)` via `isLittleO_rpow_exp_pos_mul_atTop`
   (polynomial × stronger exp decay).
5. `integrable_of_isBigO_exp_neg` closes `IntegrableOn` on `Ioi 0` given
   continuity + exp-decay big-O.

All steps mathlib-axiom-clean. No new custom axioms, no sorries.
-/

open Complex Real MeasureTheory Set Filter Asymptotics

noncomputable section

namespace ZD

/-- **Unconditional L² integrability of `ξ` on vertical lines in the strip.**

For every `σ ∈ (0, 1)`, the function `γ ↦ normSq ξ(σ + iγ)` is integrable
on `Ioi 0`. Derived from the Euler–Maclaurin polynomial ζ bound + Γ
Stirling decay + `isLittleO_rpow_exp_pos_mul_atTop` + Mathlib's
`integrable_of_isBigO_exp_neg`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem riemannXi_L2_integrable_unconditional
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt : σ < 1) :
    riemannXi_L2_integrable_target σ := by
  unfold riemannXi_L2_integrable_target
  -- 1 + 2 + 3: get eventual polynomial × exp(-π|γ|/2) bound on normSq ξ.
  have hdecay := riemannXi_vertical_decay_of_zetaBound
    StripBound.zetaPolynomialBoundInStrip_from_euler_maclaurin
  obtain ⟨K, M, T₀, hK, hT0, hbnd⟩ :=
    riemannXi_normSq_tail_bound_of_decay hdecay σ hσ_pos hσ_lt
  -- Name the integrand.
  set f : ℝ → ℝ :=
    fun γ => Complex.normSq (riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I))
  -- Continuity of f (ξ differentiable → continuous; compose).
  have hcont : Continuous f := by
    apply Complex.continuous_normSq.comp
    apply riemannXi_differentiable.continuous.comp
    apply Continuous.add continuous_const
    apply Continuous.mul Complex.continuous_ofReal continuous_const
  -- 4: f =O[atTop] exp(-π/4 · γ) via little-o polynomial vs exp + factoring.
  have hO : f =O[atTop] fun γ : ℝ => Real.exp (-(Real.pi/4) * γ) := by
    -- Step 1: f =O[atTop] K · γ^(2M) · exp(-π·γ/2)
    have step1 : f =O[atTop]
        (fun γ : ℝ => K * γ^(2*M) * Real.exp (-Real.pi * γ / 2)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      rw [Filter.eventually_atTop]
      refine ⟨T₀, fun γ hγ => ?_⟩
      have h_abs : T₀ ≤ |γ| := le_trans hγ (le_abs_self γ)
      have hγ_pos : 0 < γ := lt_of_lt_of_le hT0 hγ
      have h_abs_eq : |γ| = γ := abs_of_pos hγ_pos
      have hbb := hbnd γ h_abs
      rw [h_abs_eq] at hbb
      have hf_nn : 0 ≤ f γ := Complex.normSq_nonneg _
      have h_rhs_nn : 0 ≤ K * γ^(2*M) * Real.exp (-Real.pi * γ / 2) := by positivity
      show ‖f γ‖ ≤ 1 * _
      rw [one_mul, Real.norm_of_nonneg hf_nn, Real.norm_of_nonneg h_rhs_nn]
      exact hbb
    -- Step 2: K · γ^(2M) · exp(-π·γ/2) =O[atTop] exp(-π·γ/4)
    have step2 : (fun γ : ℝ => K * γ^(2*M) * Real.exp (-Real.pi * γ / 2))
        =O[atTop] (fun γ : ℝ => Real.exp (-(Real.pi/4) * γ)) := by
      -- γ^(2M) · exp(-π·γ/4) is bounded at ∞ (little-o vs exp cancels)
      have h_bounded :
          (fun γ : ℝ => γ^(2*M) * Real.exp (-(Real.pi/4) * γ))
            =O[atTop] (fun _ : ℝ => (1:ℝ)) := by
        have h := isLittleO_rpow_exp_pos_mul_atTop (2*M)
          (by positivity : (0:ℝ) < Real.pi/4)
        have := h.mul_isBigO
          (g₂ := fun γ : ℝ => Real.exp (-(Real.pi/4) * γ))
          (Asymptotics.isBigO_refl _ _)
        apply this.isBigO.trans
        apply Asymptotics.IsBigO.of_bound 1
        filter_upwards with γ
        rw [show Real.exp (Real.pi/4 * γ) * Real.exp (-(Real.pi/4) * γ) =
          Real.exp (Real.pi/4 * γ + -(Real.pi/4) * γ) from (Real.exp_add _ _).symm]
        have hz : Real.pi/4 * γ + -(Real.pi/4) * γ = 0 := by ring
        rw [hz, Real.exp_zero]
        simp
      calc (fun γ : ℝ => K * γ^(2*M) * Real.exp (-Real.pi * γ / 2))
          = (fun γ : ℝ => (K * (γ^(2*M) * Real.exp (-(Real.pi/4) * γ))) *
              Real.exp (-(Real.pi/4) * γ)) := by
            funext γ
            rw [show (-Real.pi * γ / 2) =
              -(Real.pi/4) * γ + -(Real.pi/4) * γ from by ring]
            rw [Real.exp_add]
            ring
        _ =O[atTop] (fun γ : ℝ => (1:ℝ) * Real.exp (-(Real.pi/4) * γ)) :=
            (h_bounded.const_mul_left K).mul (Asymptotics.isBigO_refl _ _)
        _ = (fun γ : ℝ => Real.exp (-(Real.pi/4) * γ)) := by funext γ; rw [one_mul]
    exact step1.trans step2
  -- 5: close via Mathlib's integrable_of_isBigO_exp_neg.
  exact integrable_of_isBigO_exp_neg (by positivity : (0 : ℝ) < Real.pi/4)
    hcont.continuousOn hO

#print axioms riemannXi_L2_integrable_unconditional

/-- **Unconditional ξ vertical decay.** Drops the `zetaPolynomialBoundInStrip`
hypothesis of `riemannXi_vertical_decay_of_zetaBound` by supplying
`zetaPolynomialBoundInStrip_from_euler_maclaurin` internally. -/
theorem riemannXi_vertical_decay_unconditional :
    riemannXi_vertical_decay_target :=
  riemannXi_vertical_decay_of_zetaBound
    StripBound.zetaPolynomialBoundInStrip_from_euler_maclaurin

#print axioms riemannXi_vertical_decay_unconditional

/-- **Unconditional pointwise `|ξ|²` tail bound.** Drops the `hdecay`
hypothesis of `riemannXi_normSq_tail_bound_of_decay`. -/
theorem riemannXi_normSq_tail_bound_unconditional
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt : σ < 1) :
    ∃ (K : ℝ) (M : ℝ) (T₀ : ℝ), 0 < K ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        Complex.normSq (riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)) ≤
          K * |γ|^(2*M) * Real.exp (-Real.pi * |γ| / 2) :=
  riemannXi_normSq_tail_bound_of_decay riemannXi_vertical_decay_unconditional
    σ hσ_pos hσ_lt

#print axioms riemannXi_normSq_tail_bound_unconditional

end ZD

end
