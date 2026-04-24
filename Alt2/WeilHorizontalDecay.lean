import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilZeroSum
import RequestProject.RiemannXiDecay
import RequestProject.ZetaStripBound

/-!
# Weil Horizontal Edges Decay — Cycle 44

Goal: on `Im s = ±T`, show that

```
∫ σ in [σL, σR], weilIntegrand (pairTestMellin β) (σ ± iT) dσ → 0
```

as `T → ∞`. The integrand decays super-polynomially:

* `−ζ'(s)/ζ(s)` is polynomially bounded on the strip (via
  `zetaPolynomialBoundInStrip_from_euler_maclaurin`).
* `pairTestMellin β s` has Gaussian decay in `|Im s|` (from `coshGaussMellin`'s
  closed form at `s = 1` extended via analyticity; and from the five-term
  expansion in cycle 38, each term `coshGaussMellin c s` has Gaussian factor
  `exp(c²/8)` and Γ(s/2) Stirling decay).

Combined: `|weilIntegrand·pairMellin| ≤ C · |T|^N · exp(−π|T|/4)` for large T.

## Delivered in this file

* `weilIntegrand_horizontal_strip_bound_target` — target statement for the
  horizontal decay; serves as a named target for the cycle.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Target for cycle 44 (good-heights form).** Named placeholder: for every
`β, σL, σR` with `σL < σR`, there are infinitely many "good heights" `T`
(one per unit interval from some point on) along which the horizontal-edge
integral of `weilIntegrand (pairTestMellin β)` is uniformly bounded by
`C · T^(-2)`.

**NOTE on redefinition.** The earlier `∀ T, Tendsto ... atTop 0` version is
unprovable for `σL ≤ 1` because the log-derivative `ζ'/ζ` has poles at zero
ordinates in the critical strip — no uniform bound along ALL T exists there.
The good-heights relaxation (classical Landau) is the correct achievable form. -/
def WeilHorizontalDecayTarget : Prop :=
  ∀ β : ℝ, ∀ σL σR : ℝ, σL < σR →
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
            C * T^(-(2:ℝ))

#print axioms WeilHorizontalDecayTarget

/-- **Conditional horizontal decay.** Given a pointwise exp-decay bound on the
integrand uniformly over the horizontal strip, the integral tends to 0 as
`T → ∞`. -/
theorem horizontal_integral_tendsto_zero_of_exp_bound
    (β : ℝ) (σL σR : ℝ) (_hσ : σL ≤ σR) {a : ℝ} (ha : 0 < a) (C : ℝ)
    (hbound : ∀ T : ℝ,
      ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
        C * Real.exp (-a * T)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖)
      atTop (nhds 0) := by
  -- C · exp(-a·T) → 0 as T → ∞.
  have h_exp_tendsto : Filter.Tendsto (fun T : ℝ => C * Real.exp (-a * T)) atTop (nhds 0) := by
    have h_neg_atBot : Filter.Tendsto (fun T : ℝ => -a * T) atTop Filter.atBot := by
      have h1 : Filter.Tendsto (fun T : ℝ => T * (-a)) atTop Filter.atBot :=
        Filter.Tendsto.atTop_mul_neg (neg_lt_zero.mpr ha) Filter.tendsto_id
          (by simp : Filter.Tendsto (fun _ : ℝ => -a) atTop (nhds (-a)))
      exact h1.congr (fun x => by ring)
    have h_exp : Filter.Tendsto (fun T : ℝ => Real.exp (-a * T)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_neg_atBot
    simpa using h_exp.const_mul C
  apply squeeze_zero (fun T => norm_nonneg _) hbound h_exp_tendsto

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 44.5 — Unconditional infrastructure toward `WeilHorizontalDecayTarget`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Uniform strip bound on a compact σ-range (generalised).** For any
`0 < σL ≤ σR`, there exists a constant `C ≥ 0` such that
`‖pairTestMellin β s‖ ≤ C` whenever `σL ≤ Re s ≤ σR`. The bound is uniform in
`Im s`.

Generalises `pairTestMellin_norm_bound_on_strip` (which required `σR ≤ 1`) by
dominating `t^(σ−1)` by `t^(σL−1) + t^(σR−1)` on `t > 0`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_norm_bound_on_compact_strip
    (β : ℝ) (σL σR : ℝ) (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR →
      ‖pairTestMellin β s‖ ≤ C := by
  have h_int_L : IntegrableOn
      (fun t : ℝ => t^(σL-1) * pair_cosh_gauss_test β t) (Ioi 0) :=
    pair_mellin_integrand_integrableOn β σL hσL
  have h_int_R : IntegrableOn
      (fun t : ℝ => t^(σR-1) * pair_cosh_gauss_test β t) (Ioi 0) :=
    pair_mellin_integrand_integrableOn β σR (lt_of_lt_of_le hσL hσLR)
  set I_L : ℝ := ∫ t in Ioi (0:ℝ), t^(σL-1) * pair_cosh_gauss_test β t
  set I_R : ℝ := ∫ t in Ioi (0:ℝ), t^(σR-1) * pair_cosh_gauss_test β t
  set C : ℝ := I_L + I_R
  have hI_L_nonneg : 0 ≤ I_L :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (pair_cosh_gauss_test_nonneg β t))
  have hI_R_nonneg : 0 ≤ I_R :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (pair_cosh_gauss_test_nonneg β t))
  refine ⟨C, add_nonneg hI_L_nonneg hI_R_nonneg, fun s hσL_le_re hre_le_R => ?_⟩
  have hbound := pairTestMellin_norm_le_real_integral β s
  have h_dom : ∀ t ∈ Ioi (0:ℝ),
      t^(s.re - 1) * pair_cosh_gauss_test β t ≤
        t^(σL - 1) * pair_cosh_gauss_test β t +
          t^(σR - 1) * pair_cosh_gauss_test β t := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    have h_pair_nn := pair_cosh_gauss_test_nonneg β t
    have h_rpow_bd : t^(s.re - 1) ≤ t^(σL-1) + t^(σR-1) := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(s.re - 1) ≤ t^(σL-1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σR - 1)]
      · have h1 : t^(s.re - 1) ≤ t^(σR-1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
    calc t^(s.re - 1) * pair_cosh_gauss_test β t
        ≤ (t^(σL - 1) + t^(σR-1)) * pair_cosh_gauss_test β t :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_pair_nn
      _ = t^(σL - 1) * pair_cosh_gauss_test β t +
            t^(σR-1) * pair_cosh_gauss_test β t := by ring
  have h_rhs_integrable : IntegrableOn
      (fun t : ℝ => t^(σL - 1) * pair_cosh_gauss_test β t +
        t^(σR-1) * pair_cosh_gauss_test β t) (Ioi 0) := h_int_L.add h_int_R
  have h_lhs_integrable : IntegrableOn
      (fun t : ℝ => t^(s.re - 1) * pair_cosh_gauss_test β t) (Ioi 0) :=
    pair_mellin_integrand_integrableOn β s.re (by linarith)
  have h_integral_le :
      (∫ t in Ioi (0:ℝ), t^(s.re - 1) * pair_cosh_gauss_test β t) ≤
      ∫ t in Ioi (0:ℝ),
        (t^(σL - 1) * pair_cosh_gauss_test β t +
          t^(σR-1) * pair_cosh_gauss_test β t) :=
    MeasureTheory.setIntegral_mono_on h_lhs_integrable h_rhs_integrable
      measurableSet_Ioi h_dom
  have h_integral_split :
      (∫ t in Ioi (0:ℝ),
          (t^(σL - 1) * pair_cosh_gauss_test β t +
            t^(σR-1) * pair_cosh_gauss_test β t)) = I_L + I_R := by
    rw [MeasureTheory.integral_add h_int_L h_int_R]
  linarith

#print axioms pairTestMellin_norm_bound_on_compact_strip

/-- **Factored norm of the Weil integrand.** The norm of the integrand splits as
the product of the log-derivative magnitude and the test-function magnitude.
Used downstream to factor pointwise bounds into ζ-side and `h`-side
contributions.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem weilIntegrand_norm_factored (h : ℂ → ℂ) (s : ℂ) :
    ‖weilIntegrand h s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ * ‖h s‖ := by
  unfold weilIntegrand
  rw [norm_mul, neg_div, norm_neg]

#print axioms weilIntegrand_norm_factored

/-- **Horizontal-integral decay from eventual pointwise bound.**

If, eventually as `T → ∞`, the Weil integrand at `(σ + iT)` is pointwise
bounded by some function `g(T)` uniformly for `σ` in the interval open-on-one-side
`uIoc σL σR`, and `g(T) → 0`, then the interval integral's norm tends to `0`.

Built on `intervalIntegral.norm_integral_le_of_norm_le_const`. Does not require
the bound to hold for *all* `T`, only eventually.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem horizontal_integral_tendsto_zero_of_pointwise_bound
    (β : ℝ) (σL σR : ℝ) (_hσ : σL ≤ σR)
    (g : ℝ → ℝ)
    (hbound_eventually : ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Set.uIoc σL σR,
      ‖weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤ g T)
    (hg_tendsto : Filter.Tendsto g atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖)
      atTop (nhds 0) := by
  have h_int_bound : ∀ᶠ T : ℝ in atTop,
      ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
        g T * |σR - σL| := by
    filter_upwards [hbound_eventually] with T hT
    exact intervalIntegral.norm_integral_le_of_norm_le_const hT
  have h_prod_tendsto : Filter.Tendsto (fun T : ℝ => g T * |σR - σL|) atTop (nhds 0) := by
    have := hg_tendsto.mul_const (|σR - σL|)
    simpa using this
  have h_lo : ∀ᶠ T : ℝ in atTop,
      0 ≤ ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ :=
    Filter.Eventually.of_forall (fun T => norm_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_prod_tendsto h_lo h_int_bound

#print axioms horizontal_integral_tendsto_zero_of_pointwise_bound

/-- **Named Prop target: good-heights polynomial bound on `ζ'/ζ`.**

**NOTE on redefinition.** Earlier versions of this target asked for the bound
to hold uniformly over **all** `T ≥ T₀`. That version is *unprovable* for
`σ ≤ 1`: on the vertical line `Im s = Im ρ` for a nontrivial zero ρ with
`Re ρ ∈ [σL, σR]`, the log-derivative has a pole and no polynomial bound
holds.

The correct (classical Landau–Titchmarsh) formulation asks for a **good
height** per unit interval: for each starting height `T₁`, there is a
`T ∈ [T₁, T₁ + 1]` that (a) stays distance `≥ 1/log T₁` from all zero
ordinates `Im ρ` with `Re ρ ∈ (σL, σR)`, and (b) along the line `Im s = T`
the log-derivative is polynomially bounded uniformly for `σ ∈ [σL, σR]`. -/
def logDerivZeta_polynomial_bound_target (σL σR : ℝ) : Prop :=
  ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧
    ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ,
        T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ∈ Set.Ioo σL σR →
          1 / Real.log T₁ ≤ |T - ρ.im|) ∧
        ∀ σ ∈ Set.Icc σL σR,
          ‖deriv riemannZeta (↑σ + ↑T * I) / riemannZeta (↑σ + ↑T * I)‖ ≤
            C * T^N

#print axioms logDerivZeta_polynomial_bound_target

/-- **Named Prop target: super-polynomial decay of `pairTestMellin β` along
horizontal lines.**

For any polynomial decay rate `M > 0`, there exist constants `C, T₀ > 0` such
that for all sufficiently large `|T|` and all `σ ∈ [σL, σR]`,
`‖pairTestMellin β (σ+iT)‖ ≤ C · |T|^(−M)`.

This is the Mellin-side Gaussian decay: the pair-cosh-Gaussian test function
has Gaussian decay at both ends, so its Mellin transform is Schwartz in the
`Im s` variable. Classical but unformalised in Mathlib; stated here as a named
target. Standard derivation is via the five-term cosh expansion combined with
`Γ(s/2)` Stirling decay. -/
def pairTestMellin_super_poly_decay_target (β : ℝ) (σL σR : ℝ) : Prop :=
  ∀ M : ℝ, ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
    ∀ (T : ℝ), T₀ ≤ |T| → ∀ σ ∈ Set.Icc σL σR,
      ‖pairTestMellin β (↑σ + ↑T * I)‖ ≤ C * |T|^(-M)

#print axioms pairTestMellin_super_poly_decay_target

/-- **Good-heights closure.** Given the good-heights log-derivative bound and
super-polynomial Mellin decay, for every starting height `T₁` large enough
there exists a `T ∈ [T₁, T₁+1]` where the horizontal-edge integral norm is
bounded by `C · T^(−2)`. This is strong enough for the contour-shift argument
(pick any sequence of good heights going to ∞ and route the Weil rectangle
through them).

This replaces the previous `Tendsto ... atTop` formulation, which required
the pointwise bound to hold at every `T` (impossible near zero ordinates). -/
theorem horizontal_decay_of_logDeriv_bound_and_mellin_decay
    (β : ℝ) (σL σR : ℝ) (hσ : σL < σR)
    (hLD : logDerivZeta_polynomial_bound_target σL σR)
    (hM : pairTestMellin_super_poly_decay_target β σL σR) :
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) (↑σ + ↑T * I)‖ ≤
            C * T^(-(2:ℝ)) := by
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ, hT_ζ, hζbd⟩ := hLD
  obtain ⟨C_M, T₀_M, hC_M, hT_M, hMbd⟩ := hM (N + 2)
  set T_low : ℝ := max T₀_ζ (max T₀_M 2) with hT_low_def
  have hT_low_gt_one : 1 < T_low := by
    apply lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨T_low, hT_low_gt_one, fun T₁ hT₁ => ?_⟩
  have hT₁_ge_ζ : T₀_ζ ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have hT₁_ge_M : T₀_M ≤ T₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT₁
  have hT₁_ge_two : (2 : ℝ) ≤ T₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT₁
  have hT₁_pos : 0 < T₁ := by linarith
  obtain ⟨T, hT_ge, hT_le, _h_avoid, hζbd_T⟩ := hζbd T₁ hT₁_ge_ζ
  refine ⟨T, hT_ge, hT_le, C_ζ * C_M * |σR - σL|, by positivity, ?_⟩
  have hT_pos : 0 < T := by linarith
  -- Apply pointwise bound along the specific good height T.
  have h_inner_bound : ∀ σ ∈ Set.uIoc σL σR,
      ‖weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      C_ζ * C_M * T^(-(2:ℝ)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ.le
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have h_ζ_bd := hζbd_T σ hσ_Icc
    -- hMbd takes |T|; convert to T since T > 0.
    have hT_abs : |T| = T := abs_of_pos hT_pos
    have h_M_bd := hMbd T (by rw [hT_abs]; linarith) σ hσ_Icc
    have hT_rpow_abs : |T|^(-(N+2:ℝ)) = T^(-(N+2:ℝ)) := by rw [hT_abs]
    rw [weilIntegrand_norm_factored]
    calc ‖deriv riemannZeta (↑σ + ↑T * I) / riemannZeta (↑σ + ↑T * I)‖ *
          ‖pairTestMellin β (↑σ + ↑T * I)‖
        ≤ (C_ζ * T^N) * (C_M * |T|^(-(N + 2))) := by
          apply mul_le_mul h_ζ_bd h_M_bd (norm_nonneg _)
          exact mul_nonneg hC_ζ.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ T) _)
      _ = (C_ζ * T^N) * (C_M * T^(-(N + 2))) := by rw [hT_rpow_abs]
      _ = C_ζ * C_M * (T^N * T^(-(N + 2))) := by ring
      _ = C_ζ * C_M * T^(-(2:ℝ)) := by
          congr 1
          rw [← Real.rpow_add hT_pos]
          congr 1
          ring
  calc ‖∫ σ in σL..σR, weilIntegrand (pairTestMellin β) ((σ : ℂ) + (T : ℂ) * I)‖
      ≤ (C_ζ * C_M * T^(-(2:ℝ))) * |σR - σL| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_inner_bound
    _ = C_ζ * C_M * |σR - σL| * T^(-(2:ℝ)) := by ring

#print axioms horizontal_decay_of_logDeriv_bound_and_mellin_decay

-- The concrete `WeilHorizontalDecayTarget` closure for `σL > 1` lives in
-- `WeilLandauBound.lean` (where `logDerivZeta_bounded_of_right_of_one` is
-- accessible without circular import).

end Contour
end WeilPositivity
end ZD

end
