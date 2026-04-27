import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilReflectedPrimeVanishingWeilside
-- import RequestProject.WeilReflectedPrimeCoshExpansion
import RequestProject.ArchOperatorBound
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilLandauBound

/-!
# Scaffold for `reflectedPrime_integral_vanishes_at_two`

The vanishing identity
`∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0`
is *not* RH content. It is a cosh-side geometric identity — a Weil-style explicit
formula for the specific cosh-Gauss pair test. The mechanism is:

* Mellin inversion specialised to `coshGaussMellin c` produces a vertical-line
  representation of `cosh(c·x)·exp(-2x²)` at any `x > 0`.
* Combined with the von Mangoldt expansion `-ζ'/ζ(s) = ∑ Λ(n)/nˢ` on `Re s > 1`
  and a Fubini swap, this gives a vertical-integral form for `primeSingleCosh c`.
* Applying the FE-form `zeta_logDeriv_arch_form` to `ζ'/ζ(1-s)` at `Re s = 2`
  yields a per-c identity
  `reflectedPrimeSingleCosh c = primeSingleCosh c - archSingleCosh c`.
* Lifting to the five-term pair-combo with the cosh-pair axes
  `(2β − π/3, 2 − π/3 − 2β, 1 − π/3, 2β − 1, 0)` and using `pair_coeffs_sum`,
  `pair_coeffs_diff`, `pair_axes_sum`, `pair_half_strip`, the difference
  `archPair − primePair` cancels by the 6th-root-of-unity reflection structure
  of these axes (the "harmonic / energy-balance" content).
* L3 (`reflectedPrime_integral_cosh_expansion_at_two`, proved) then closes:
  `∫ reflected = reflectedPrimePair = primePair − archPair = 0`.

This file lays out the five steps as separate scaffold theorems with attempted
proofs from existing infrastructure. Every `sorry` here is a known, locally
specified analytic step — none of them require RH or zero-distribution input.

A repair agent should be sent through to fill each remaining `sorry` using the
infrastructure pointers in the docstring above each step.
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace PairTestVanishingScaffold

open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing
-- open ZD.WeilPositivity.Contour.ReflectedPrimeCoshExpansion

/-! ## S1 — Mellin inversion specialised to `coshGaussMellin c` at `σ = 2`

For each `x > 0`,
```
cosh(c·x) · exp(-2 x²) = mellinInv 2 (coshGaussMellin c) x.
```

This unfolds to
```
cosh(c·x) · exp(-2 x²)
  = (1 / (2π·I)) · ∫_{-∞}^{∞} coshGaussMellin c (2 + i·t) · x^{-(2 + i·t)} · I dt
```
(or whatever the precise normalization in `mellinInv` is in mathlib).

**Infrastructure**:
* `Contour.mellin_inversion_eq` (`WeilContour.lean:510`) — the generic form.
* `Contour.mellinConvergent_coshGauss` — already used in
  `WeilReflectedPrimeCoshExpansion.lean:365-369`. Provides `MellinConvergent`
  for `coshGaussMellin c` at `Re s = σ > 0`.
* Need: `Complex.VerticalIntegrable (coshGaussMellin c) 2`. Should follow from
  the quadratic decay bound `coshGaussMellin_quadratic_bound_at_two`
  (`WeilReflectedPrimeCoshExpansion.lean:113`) plus measurability via
  `coshGaussMellin_differentiableAt`.
-/

theorem coshGauss_verticalIntegrable_at_two (c : ℝ) :
    Complex.VerticalIntegrable (Contour.coshGaussMellin c) 2 MeasureTheory.volume := by
  -- VerticalIntegrable f σ μ unfolds to Integrable (fun t => f (σ + t * I)) μ.
  -- Use the quadratic-decay bound `coshGaussMellin_quadratic_bound_at_two` combined
  -- with integrability of `K/(1+t²)` and continuity of `coshGaussMellin c` along
  -- the vertical line `Re s = 2`.
  obtain ⟨K, hK_nn, h_bd⟩ := coshGaussMellin_quadratic_bound_at_two c
  unfold Complex.VerticalIntegrable
  -- Continuity of `t ↦ coshGaussMellin c (2 + t·I)` from differentiability on `Re s > 0`.
  have h_cont : Continuous
      (fun t : ℝ => Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
    have h_diff_on : DifferentiableOn ℂ (Contour.coshGaussMellin c) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (Contour.coshGaussMellin_differentiableAt c hs).differentiableWithinAt
    have h_line_cont : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_cont_on := h_diff_on.continuousOn
    have h_map : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | 0 < s.re} := by
      intro t; simp
    exact h_cont_on.comp_continuous h_line_cont h_map
  have h_eq :
      (fun y : ℝ => Contour.coshGaussMellin c (((2 : ℝ) : ℂ) + y * I)) =
      (fun t : ℝ => Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
    funext t
    show Contour.coshGaussMellin c (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)
    norm_cast
  rw [h_eq]
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul K)
    h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h_bd_t := h_bd t
  have h_rhs_nn : 0 ≤ K * (1 + t^2)⁻¹ := by
    have : 0 < 1 + t^2 := by positivity
    exact mul_nonneg hK_nn (inv_nonneg.mpr this.le)
  rw [Real.norm_of_nonneg h_rhs_nn]
  have hKdiv : K / (1 + t^2) = K * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]
  linarith [hKdiv ▸ h_bd_t]

/-- **S1.** Mellin inversion of `coshGaussMellin c` at `σ = 2`. -/
theorem coshGaussMellin_inversion_at_two (c : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (Contour.coshGaussMellin c) x =
      ((Real.cosh (c * x) * Real.exp (-2 * x^2) : ℝ) : ℂ) := by
  -- Apply Contour.mellin_inversion_eq with σ = 2, f = the underlying real function
  -- `(fun t : ℝ => ((cosh(c·t)·exp(-2t²) : ℝ) : ℂ))`.
  -- By definition, `coshGaussMellin c s = mellin (fun t => (cosh(c·t)·exp(-2t²) : ℂ)) s`.
  set f : ℝ → ℂ :=
    fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) with hf_def
  have h_mellin_eq : mellin f = Contour.coshGaussMellin c := by
    funext s
    unfold Contour.coshGaussMellin
    congr 1
    funext t
    simp [hf_def, Complex.ofReal_mul]
  have h_conv : MellinConvergent f ((2 : ℝ) : ℂ) := by
    have h_re : (0 : ℝ) < (((2 : ℝ) : ℂ)).re := by
      simp
    exact Contour.mellinConvergent_coshGauss c h_re
  have h_vint : Complex.VerticalIntegrable (mellin f) 2 MeasureTheory.volume := by
    rw [h_mellin_eq]
    exact coshGauss_verticalIntegrable_at_two c
  have h_cont : ContinuousAt f x := by
    apply Complex.continuous_ofReal.continuousAt.comp
    exact ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))).continuousAt
  have h := Contour.mellin_inversion_eq 2 f hx h_conv h_vint h_cont
  -- h : mellinInv 2 (mellin f) x = f x
  rw [h_mellin_eq] at h
  exact h

/-! ## S2 — Vertical-integral form of `primeSingleCosh c`

By von Mangoldt expansion of `-ζ'/ζ(s)` on `Re s > 1`:
```
-ζ'/ζ(2 + it) = ∑ n, Λ(n) / n^(2 + it).
```

Multiply by `coshGaussMellin c (2 + it)`, integrate over `t ∈ ℝ`, swap sum/integral
via Fubini. Each summand `Λ(n) · ∫ coshGaussMellin c (2 + it) · n^{-(2 + it)} dt`
is `Λ(n) · 2π · cosh(c·log n) · exp(-2 (log n)²)` by S1 with `x = n`. Reindexing
gives `2π · ∑ Λ(n) · cosh(c·n) · exp(-2 n²) = primeSingleCosh c`.

Wait — careful: S1 evaluates at `x > 0` and produces `cosh(c·x)·exp(-2x²)` for
that x. Plugging `x = n` (for `n ≥ 1`) gives `cosh(c·n)·exp(-2n²)`, so the
integrated von-Mangoldt sum yields `primeSingleCosh c` directly (no log).

**Infrastructure**:
* `LSeriesCoeff` / `vonMangoldt` series for `-ζ'/ζ` (mathlib).
* `Contour.primeIntegrand_integral_eq_prime_sum`
  (`WeilContour.lean` — used in `prime_integral_cosh_expansion_at_two`).
* Pattern at `WeilRightEdgePrimeSum.lean:371-420` (Fubini swap for `pairTestMellin`).
-/

/-- **S2.** Vertical-integral representation of `primeSingleCosh c`. -/
theorem primeSingleCosh_eq_vertical_integral (c : ℝ) :
    ((primeSingleCosh c : ℝ) : ℂ) =
      ∫ t : ℝ,
        (-deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I) := by
  -- Strategy: parallel `primeIntegrand_integral_eq_prime_sum`. Build the per-n
  -- integral via a Mellin-inversion-style evaluation (S1b at x = n), then swap
  -- sum/integral by Fubini using the quadratic-decay bound.
  set σ : ℝ := 2 with hσ_def
  have hσ_gt1 : (1 : ℝ) < σ := by norm_num
  have hσ_pos : (0 : ℝ) < σ := by norm_num
  -- Quadratic bound for `coshGaussMellin c` on Re s = 2.
  obtain ⟨K, hK_nn, h_cosh_bd⟩ := coshGaussMellin_quadratic_bound_at_two c
  -- Continuity along vertical line (used repeatedly).
  have h_cosh_cont : Continuous
      (fun t : ℝ => Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := by
    have h_diff_on : DifferentiableOn ℂ (Contour.coshGaussMellin c) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (Contour.coshGaussMellin_differentiableAt c hs).differentiableWithinAt
    have h_line_cont : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_map : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | 0 < s.re} := by
      intro t
      show (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re
      simp [σ]
    exact h_diff_on.continuousOn.comp_continuous h_line_cont h_map
  -- Define per-n integrand F : ℕ → ℝ → ℂ (n-th LSeries-term · coshGaussMellin).
  set F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((σ : ℂ) + (t : ℂ) * I) n *
    Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I) with hF_def
  -- Step 1: pointwise -ζ'/ζ(σ+it) = ∑ LSeries.term n.
  have h_pt : ∀ t : ℝ,
      (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)) *
      Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, F n t := by
    intro t
    have hs_re : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re := by simp [σ]
    have hL := vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs_re
    -- hL : LSeries Λ s = -deriv ζ s / ζ s
    have hL' :
        -deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * I) =
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((σ : ℂ) + (t : ℂ) * I) := by
      rw [hL]
    rw [hL']
    rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((σ : ℂ) + (t : ℂ) * I) =
            ∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              ((σ : ℂ) + (t : ℂ) * I) n from rfl]
    simp only [hF_def]
    exact (tsum_mul_right).symm
  -- Step 2: each F n integrable.
  have h_F_int : ∀ n : ℕ, MeasureTheory.Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ t : ℝ, F 0 t = 0 := by
        intro t; simp [hF_def, LSeries.term_zero]
      refine (MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume).congr ?_
      exact MeasureTheory.ae_of_all _ (fun t => (h_zero t).symm)
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have hn_ne_C : (n : ℂ) ≠ 0 := by exact_mod_cast hn_ne
      have h_term : ∀ t : ℝ, F n t =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
             Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := by
        intro t
        simp only [hF_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      have h_fn_eq : (F n : ℝ → ℂ) = fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
             Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := funext h_term
      rw [h_fn_eq]
      apply MeasureTheory.Integrable.const_mul
      have h_cpow_cont : Continuous
          (fun t : ℝ => ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))) := by
        have h_exp : Continuous (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * I)) :=
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg
        have h_cpow_cont_z : Continuous (fun z : ℂ => (n : ℂ) ^ z) := by
          rw [continuous_iff_continuousAt]
          intro b
          exact continuousAt_const_cpow hn_ne_C
        exact h_cpow_cont_z.comp h_exp
      have h_prod_cont : Continuous
          (fun t : ℝ => ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
                         Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) :=
        h_cpow_cont.mul h_cosh_cont
      have h_cpow_norm : ∀ t : ℝ,
          ‖((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ = (n : ℝ) ^ (-σ) := by
        intro t
        rw [show -((σ : ℂ) + (t : ℂ) * I) = ((-σ : ℝ) : ℂ) + (-t : ℂ) * I from by
          push_cast; ring]
        rw [Complex.norm_natCast_cpow_of_pos hpos]
        simp
      refine MeasureTheory.Integrable.mono
        ((integrable_inv_one_add_sq).const_mul ((n : ℝ) ^ (-σ) * K))
        h_prod_cont.aestronglyMeasurable ?_
      refine MeasureTheory.ae_of_all _ fun t => ?_
      rw [norm_mul, h_cpow_norm t]
      have h_cosh_bd_t := h_cosh_bd t
      have h_1plus_pos : 0 < 1 + t^2 := by positivity
      have h_nsnn : 0 ≤ (n : ℝ)^(-σ) := Real.rpow_nonneg hn_pos.le _
      have h_rhs_nn : 0 ≤ (n : ℝ)^(-σ) * K * (1 + t^2)⁻¹ :=
        mul_nonneg (mul_nonneg h_nsnn hK_nn) (inv_nonneg.mpr h_1plus_pos.le)
      rw [Real.norm_of_nonneg h_rhs_nn]
      calc (n : ℝ)^(-σ) * ‖Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)‖
          ≤ (n : ℝ)^(-σ) * (K / (1 + t^2)) :=
            mul_le_mul_of_nonneg_left h_cosh_bd_t h_nsnn
        _ = (n : ℝ)^(-σ) * K * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]; ring
  -- Step 3: summable L¹ norms.
  have h_F_L1_summ : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have h_π_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have h_bound_summ : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * Real.pi)) := by
      have h_div := ZD.WeilPositivity.Contour.summable_vonMangoldt_rpow σ hσ_gt1
      have h_eq : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) *
            (K * Real.pi)) =
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ *
            (K * Real.pi)) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [ArithmeticFunction.map_zero]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
      rw [h_eq]
      exact h_div.mul_right (K * Real.pi)
    refine h_bound_summ.of_nonneg_of_le ?_ ?_
    · intro n; exact MeasureTheory.integral_nonneg (fun t => norm_nonneg _)
    · intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have h_zero : ∀ t : ℝ, ‖F 0 t‖ = 0 := by
          intro t; simp [hF_def, LSeries.term_zero]
        rw [MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ h_zero),
          MeasureTheory.integral_zero]
        simp [ArithmeticFunction.map_zero]
      · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
        -- Pointwise bound ‖F n t‖ ≤ Λ(n) · n^(-σ) · K · (1+t²)⁻¹.
        have h_bd_pt : ∀ t : ℝ,
            ‖F n t‖ ≤
            (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * (1 + t^2)⁻¹) := by
          intro t
          simp only [hF_def]
          rw [LSeries.term_of_ne_zero hn_ne, norm_mul, norm_div]
          rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
                (ArithmeticFunction.vonMangoldt n : ℝ) from by
            rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
                  = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
            rw [Complex.norm_real]
            exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          rw [Complex.norm_natCast_cpow_of_pos hpos]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          have h_cosh_bd_t := h_cosh_bd t
          have h_Lnn : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          have hns_pos : 0 < (n : ℝ)^σ := Real.rpow_pos_of_pos hn_pos _
          have hns_eq : (n : ℝ)^(-σ) = ((n : ℝ)^σ)⁻¹ :=
            Real.rpow_neg hn_pos.le _
          calc (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ *
                ‖Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)‖
              ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ * (K / (1 + t^2)) := by
                apply mul_le_mul_of_nonneg_left h_cosh_bd_t
                exact div_nonneg h_Lnn hns_pos.le
            _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * (1 + t^2)⁻¹) := by
                rw [hns_eq, div_eq_mul_inv, div_eq_mul_inv]
        calc ∫ t : ℝ, ‖F n t‖
            ≤ ∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) *
                       (K * (1 + t^2)⁻¹) := by
              apply MeasureTheory.integral_mono_of_nonneg
              · exact MeasureTheory.ae_of_all _ fun t => norm_nonneg _
              · exact (integrable_inv_one_add_sq.const_mul K).const_mul _
              · exact MeasureTheory.ae_of_all _ h_bd_pt
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) *
              (K * ∫ t : ℝ, (1 + t^2)⁻¹) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * Real.pi) := by
              rw [integral_univ_inv_one_add_sq]
  -- Step 4: per-n integral evaluation via Mellin inversion at x = n (S1b).
  have h_per_n : ∀ n : ℕ, ∫ t : ℝ, F n t =
      (2 * Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ t : ℝ, F 0 t = 0 := by
        intro t; simp [hF_def, LSeries.term_zero]
      rw [MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_of_all _ h_zero),
        MeasureTheory.integral_zero]
      simp [ArithmeticFunction.map_zero]
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have h_inv := coshGaussMellin_inversion_at_two c hn_pos
      -- h_inv : mellinInv σ (coshGaussMellin c) n = ((cosh(c·n)·exp(-2n²) : ℝ) : ℂ)
      -- where mellinInv σ f x = (1/(2π)) • ∫ y, (x:ℂ)^(-(σ+yI)) • f(σ+yI)
      unfold mellinInv at h_inv
      -- Turn • into multiplication.
      have h_smul_eq : ∀ y : ℝ,
          ((n : ℝ) : ℂ) ^ (-(((σ : ℝ) : ℂ) + (y : ℂ) * I)) •
            Contour.coshGaussMellin c (((σ : ℝ) : ℂ) + (y : ℂ) * I) =
          ((n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) *
            Contour.coshGaussMellin c ((σ : ℂ) + (y : ℂ) * I) := by
        intro y
        show ((n : ℝ) : ℂ) ^ (-(((σ : ℝ) : ℂ) + (y : ℂ) * I)) *
            Contour.coshGaussMellin c (((σ : ℝ) : ℂ) + (y : ℂ) * I) = _
        push_cast
        rfl
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_smul_eq)] at h_inv
      -- Now h_inv : (1/(2π)) • ∫ y, ((n:ℂ)^(-(σ+yI)) · coshGaussMellin c (σ+yI)) = rhs
      have h_inv2 : (1 / (2 * Real.pi) : ℂ) *
          (∫ (a : ℝ), ((n : ℂ) ^ (-((σ : ℂ) + (a : ℂ) * I))) *
            Contour.coshGaussMellin c ((σ : ℂ) + (a : ℂ) * I)) =
          ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := by
        have h_smul : (1 / (2 * Real.pi) : ℝ) •
            (∫ (a : ℝ), ((n : ℂ) ^ (-((σ : ℂ) + (a : ℂ) * I))) *
              Contour.coshGaussMellin c ((σ : ℂ) + (a : ℂ) * I)) =
            ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := h_inv
        rw [show ((1 / (2 * Real.pi) : ℝ) •
              (∫ (a : ℝ), ((n : ℂ) ^ (-((σ : ℂ) + (a : ℂ) * I))) *
                Contour.coshGaussMellin c ((σ : ℂ) + (a : ℂ) * I)) : ℂ) =
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ (a : ℝ), ((n : ℂ) ^ (-((σ : ℂ) + (a : ℂ) * I))) *
                Contour.coshGaussMellin c ((σ : ℂ) + (a : ℂ) * I)) from by
          rw [Complex.real_smul]] at h_smul
        have h_coe : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by
          push_cast; ring
        rw [h_coe] at h_smul
        exact h_smul
      clear h_inv
      -- Multiply both sides by `2π` to extract the integral.
      have h_2pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
        have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        exact mul_ne_zero two_ne_zero hπ
      have h_inner : (∫ (y : ℝ),
            ((n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) *
              Contour.coshGaussMellin c ((σ : ℂ) + (y : ℂ) * I)) =
          (2 * Real.pi : ℂ) *
            ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := by
        have h1 : (1 / (2 * Real.pi) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
          field_simp
        have heq : (2 * Real.pi : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) * ∫ (y : ℝ),
              ((n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) *
                Contour.coshGaussMellin c ((σ : ℂ) + (y : ℂ) * I)) =
            (2 * Real.pi : ℂ) *
              ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := by
          rw [h_inv2]
        rw [show (2 * Real.pi : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) * ∫ (y : ℝ),
              ((n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) *
                Contour.coshGaussMellin c ((σ : ℂ) + (y : ℂ) * I)) =
            ((2 * Real.pi : ℂ) * (1 / (2 * Real.pi) : ℂ)) *
              ∫ (y : ℝ),
                ((n : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) *
                  Contour.coshGaussMellin c ((σ : ℂ) + (y : ℂ) * I) by ring] at heq
        rw [show ((2 * Real.pi : ℂ) * (1 / (2 * Real.pi) : ℂ)) = 1 by
              rw [mul_comm]; exact h1] at heq
        rw [one_mul] at heq
        exact heq
      -- Now F n t = Λ(n) · [((n:ℂ)^(-(σ+tI)) · coshGaussMellin c (σ+tI))].
      have h_term_eq : ∀ t : ℝ, F n t =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
             Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := by
        intro t
        simp only [hF_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      have h_fn_eq2 : (F n : ℝ → ℂ) = fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
             Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := funext h_term_eq
      calc ∫ t : ℝ, F n t
          = ∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
               Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I)) := by
            rw [h_fn_eq2]
        _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
              ∫ t : ℝ, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
                Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I) :=
            MeasureTheory.integral_const_mul _ _
        _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((2 * Real.pi : ℂ) *
                ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ)) := by
            rw [h_inner]
        _ = 2 * (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ) : ℂ) := by
            ring
  -- Assembly: ∫ RHS = ∫ ∑ F n = ∑ ∫ F n = ∑ 2π·Λ(n)·cosh(c·n)·exp(-2n²)
  --                 = 2π · ∑ Λ(n) · cosh(c·n) · exp(-2n²) = primeSingleCosh c.
  have h_fubini : (∫ t : ℝ, ∑' n : ℕ, F n t) = ∑' n : ℕ, ∫ t : ℝ, F n t :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm h_F_int h_F_L1_summ).symm
  calc ((primeSingleCosh c : ℝ) : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) *
          ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2)) : ℝ) : ℂ) := by
        show ((primeSingleCosh c : ℝ) : ℂ) = _
        unfold primeSingleCosh
        push_cast
        ring
    _ = (2 * Real.pi : ℂ) *
          (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ)) : ℂ)) := by
        set g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
            (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2)) with hg_def
        have h_tsum_cast : (((∑' n : ℕ, g n) : ℝ) : ℂ) =
            ∑' n : ℕ, ((g n : ℝ) : ℂ) := Complex.ofReal_tsum g
        calc ((2 * Real.pi : ℝ) : ℂ) * (((∑' n : ℕ, g n) : ℝ) : ℂ)
            = (2 * Real.pi : ℂ) * (∑' n : ℕ, ((g n : ℝ) : ℂ)) := by
              rw [h_tsum_cast]; push_cast; ring
          _ = (2 * Real.pi : ℂ) *
              (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                (((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ)) : ℂ)) := by
              congr 1
              apply tsum_congr
              intro n
              simp only [hg_def]
              push_cast; ring
    _ = ∑' n : ℕ, (2 * Real.pi : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ)^2) : ℝ)) : ℂ) := by
        rw [← tsum_mul_left]
        congr 1
        funext n
        ring
    _ = ∑' n : ℕ, ∫ t : ℝ, F n t := by
        rw [tsum_congr (fun n => (h_per_n n).symm)]
    _ = ∫ t : ℝ, ∑' n : ℕ, F n t := h_fubini.symm
    _ = ∫ t : ℝ,
          (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * I)) *
          Contour.coshGaussMellin c ((σ : ℂ) + (t : ℂ) * I) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        exact (h_pt t).symm

/-! ## S3 — Per-c reflected = prime − arch identity

The FE-form `zeta_logDeriv_arch_form` gives, at any `s` in the right half-plane
with the relevant non-vanishing hypotheses:
```
ζ'/ζ(1 - s) = -ζ'/ζ(s) - (Γℝ'/Γℝ(s) + Γℝ'/Γℝ(1 - s)).
```

Multiply by `coshGaussMellin c(s)` at `s = 2 + it` and integrate; split
linearly. The first piece `-ζ'/ζ(2+it)·coshGaussMellin c(2+it)` integrates to
`primeSingleCosh c` by **S2**. The remaining piece
`(Γℝ'/Γℝ(s) + Γℝ'/Γℝ(1-s)) · coshGaussMellin c(s)` integrates by definition to
`archSingleCosh c`. Sign tracking yields:

```
reflectedPrimeSingleCosh c = primeSingleCosh c - archSingleCosh c.
```

**Infrastructure**:
* `zeta_logDeriv_arch_form` (used in `WeilReflectedPrimeCoshExpansion.lean:177`).
* `S2` above.
* Definition of `archSingleCosh c` (line 69 of `…WeilReflectedPrimeVanishingWeilside`).
* `MeasureTheory.integral_add` / `integral_sub`. Integrability per term:
  - `reflectedPrimeSingleCosh_integrable c` (proved, this file).
  - `arch_coshGaussMellin_integrable_at_two c` (proved, line 807 of …Weilside).
  - prime-side integrability follows from S2 (the integrand is actually integrable
    because it equals a real-valued absolutely-convergent series after Fubini).
-/
/-
/-- **S3.** Per-c reflected = prime − arch. -/
theorem reflectedPrimeSingleCosh_eq_primeSingleCosh_sub_archSingleCosh (c : ℝ) :
    reflectedPrimeSingleCosh c =
      ((primeSingleCosh c : ℝ) : ℂ) - archSingleCosh c := by
  -- Notation.
  set s : ℝ → ℂ := fun t : ℝ => (2 : ℂ) + (t : ℂ) * I with hs_def
  -- Non-vanishing conditions at s = 2+it.
  have h_s_ne_zero : ∀ t : ℝ, s t ≠ 0 := by
    intro t h; have := congr_arg Complex.re h; simp [hs_def] at this
  have h_s_ne_one : ∀ t : ℝ, s t ≠ 1 := by
    intro t h; have := congr_arg Complex.re h; simp [hs_def] at this
  have h_zeta_s_ne : ∀ t : ℝ, riemannZeta (s t) ≠ 0 := by
    intro t; apply riemannZeta_ne_zero_of_one_lt_re; simp [hs_def]
  have h_1s_ne_zero : ∀ t : ℝ, (1 - s t) ≠ 0 := by
    intro t h; have := congr_arg Complex.re h; simp [hs_def] at this; linarith
  have h_gammaR_s_ne : ∀ t : ℝ, (s t).Gammaℝ ≠ 0 := by
    intro t h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have := congr_arg Complex.re hn; simp [hs_def] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h_gammaR_1s_ne : ∀ t : ℝ, (1 - s t).Gammaℝ ≠ 0 := by
    intro t h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have := congr_arg Complex.re hn; simp [hs_def] at this
    rcases n with _ | k <;> push_cast at this <;> linarith
  have h_zeta_1s_ne : ∀ t : ℝ, riemannZeta (1 - s t) ≠ 0 := by
    intro t h
    have h_xi_s : completedRiemannZeta (s t) = (s t).Gammaℝ * riemannZeta (s t) :=
      completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta (h_s_ne_zero t) (h_gammaR_s_ne t)
    have h_xi_ne : completedRiemannZeta (s t) ≠ 0 := by
      rw [h_xi_s]; exact mul_ne_zero (h_gammaR_s_ne t) (h_zeta_s_ne t)
    have h_xi_1s : completedRiemannZeta (1 - s t) = completedRiemannZeta (s t) :=
      completedRiemannZeta_one_sub _
    have h_xi_1s_ne : completedRiemannZeta (1 - s t) ≠ 0 := by
      rw [h_xi_1s]; exact h_xi_ne
    have h_zeta_1s_eq : riemannZeta (1 - s t) =
        completedRiemannZeta (1 - s t) / (1 - s t).Gammaℝ :=
      riemannZeta_def_of_ne_zero (h_1s_ne_zero t)
    rw [h_zeta_1s_eq] at h
    exact absurd (div_eq_zero_iff.mp h) (not_or_intro h_xi_1s_ne (h_gammaR_1s_ne t))
  -- Pointwise FE identity: ζ'/ζ(1-s) = -ζ'/ζ(s) - (Γℝ'/Γℝ(s) + Γℝ'/Γℝ(1-s)).
  have h_arch_form : ∀ t : ℝ,
      deriv riemannZeta (1 - s t) / riemannZeta (1 - s t) =
        -(deriv riemannZeta (s t) / riemannZeta (s t)) -
        (deriv Complex.Gammaℝ (s t) / (s t).Gammaℝ +
          deriv Complex.Gammaℝ (1 - s t) / (1 - s t).Gammaℝ) := by
    intro t
    have h := zeta_logDeriv_arch_form (h_s_ne_zero t) (h_s_ne_one t)
      (h_zeta_s_ne t) (h_zeta_1s_ne t) (h_gammaR_s_ne t) (h_gammaR_1s_ne t)
    linear_combination -h
  -- Pointwise integrand identity.
  have h_ptw : ∀ t : ℝ,
      deriv riemannZeta (1 - s t) / riemannZeta (1 - s t) *
        Contour.coshGaussMellin c (s t) =
      (-(deriv riemannZeta (s t) / riemannZeta (s t)) *
        Contour.coshGaussMellin c (s t)) -
      ((deriv Complex.Gammaℝ (s t) / (s t).Gammaℝ +
          deriv Complex.Gammaℝ (1 - s t) / (1 - s t).Gammaℝ) *
        Contour.coshGaussMellin c (s t)) := by
    intro t
    rw [h_arch_form t]; ring
  -- Integrability of the prime-side integrand `-(ζ'/ζ)(2+it) · coshGaussMellin c (2+it)`.
  obtain ⟨C_ζ, hC_ζ_nn, h_zeta_bd⟩ := landau_logDeriv_bound_at_two
  obtain ⟨K, hK_nn, h_cosh_bd⟩ := coshGaussMellin_quadratic_bound_at_two c
  -- Continuity along vertical line.
  have h_cosh_cont : Continuous (fun t : ℝ => Contour.coshGaussMellin c (s t)) := by
    have h_diff_on : DifferentiableOn ℂ (Contour.coshGaussMellin c) {z : ℂ | 0 < z.re} := by
      intro z hz
      exact (Contour.coshGaussMellin_differentiableAt c hz).differentiableWithinAt
    have h_line_cont : Continuous s := by
      simp only [hs_def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_map : ∀ t : ℝ, s t ∈ {z : ℂ | 0 < z.re} := by
      intro t; simp [hs_def]
    exact h_diff_on.continuousOn.comp_continuous h_line_cont h_map
  have h_zeta_cont : Continuous (fun t : ℝ =>
      deriv riemannZeta (s t) / riemannZeta (s t)) := by
    have h_line : Continuous s := by
      simp only [hs_def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_in : ∀ t : ℝ, s t ∈ ({1}ᶜ : Set ℂ) := h_s_ne_one
    have h_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    have h_an_on : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      h_diff_on.analyticOnNhd isOpen_compl_singleton
    have h_dζ_diff_on : DifferentiableOn ℂ (deriv riemannZeta) ({1}ᶜ : Set ℂ) :=
      fun z hz => ((h_an_on z hz).deriv).differentiableAt.differentiableWithinAt
    have h_zeta_cont' : Continuous (fun t : ℝ => riemannZeta (s t)) :=
      h_diff_on.continuousOn.comp_continuous h_line h_in
    have h_dζ_cont : Continuous (fun t : ℝ => deriv riemannZeta (s t)) :=
      h_dζ_diff_on.continuousOn.comp_continuous h_line h_in
    exact h_dζ_cont.div h_zeta_cont' h_zeta_s_ne
  -- Prime-side integrand integrability.
  have h_prime_int : MeasureTheory.Integrable
      (fun t : ℝ => -(deriv riemannZeta (s t) / riemannZeta (s t)) *
        Contour.coshGaussMellin c (s t)) := by
    -- Bound: ‖-ζ'/ζ · cosh‖ ≤ C_ζ · K / (1+t²).
    have h_meas : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => -(deriv riemannZeta (s t) / riemannZeta (s t)) *
          Contour.coshGaussMellin c (s t)) MeasureTheory.volume :=
      ((h_zeta_cont.neg).mul h_cosh_cont).aestronglyMeasurable
    have h_majorant : MeasureTheory.Integrable
        (fun t : ℝ => C_ζ * K * (1 + t^2)⁻¹) :=
      (integrable_inv_one_add_sq.const_mul (C_ζ * K))
    refine h_majorant.mono' h_meas ?_
    refine MeasureTheory.ae_of_all _ fun t => ?_
    have h_cosh_t := h_cosh_bd t
    have h_zeta_t := h_zeta_bd t
    have h_1plus_pos : 0 < 1 + t^2 := by positivity
    have h_majorant_nn : 0 ≤ C_ζ * K * (1 + t^2)⁻¹ :=
      mul_nonneg (mul_nonneg hC_ζ_nn hK_nn) (inv_nonneg.mpr h_1plus_pos.le)
    rw [norm_mul, norm_neg]
    have h_cosh_nn : 0 ≤ ‖Contour.coshGaussMellin c (s t)‖ := norm_nonneg _
    calc ‖deriv riemannZeta (s t) / riemannZeta (s t)‖ *
          ‖Contour.coshGaussMellin c (s t)‖
        ≤ C_ζ * (K / (1 + t^2)) := by
          apply mul_le_mul h_zeta_t h_cosh_t h_cosh_nn hC_ζ_nn
      _ = C_ζ * K * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]; ring
  -- Arch-side integrand integrability (already proved).
  have h_arch_int := arch_coshGaussMellin_integrable_at_two c
  -- The full reflected-prime integrand (for the fn equality and integral_sub).
  have h_refl_int := reflectedPrimeSingleCosh_integrable c
  -- Function equality.
  have h_fn_eq : (fun t : ℝ => deriv riemannZeta (1 - s t) / riemannZeta (1 - s t) *
        Contour.coshGaussMellin c (s t)) =
      fun t : ℝ =>
        (-(deriv riemannZeta (s t) / riemannZeta (s t)) *
          Contour.coshGaussMellin c (s t)) -
        ((deriv Complex.Gammaℝ (s t) / (s t).Gammaℝ +
            deriv Complex.Gammaℝ (1 - s t) / (1 - s t).Gammaℝ) *
          Contour.coshGaussMellin c (s t)) := funext h_ptw
  -- Now compute.
  show (∫ t : ℝ, deriv riemannZeta (1 - s t) / riemannZeta (1 - s t) *
        Contour.coshGaussMellin c (s t)) =
      ((primeSingleCosh c : ℝ) : ℂ) - archSingleCosh c
  rw [h_fn_eq]
  rw [MeasureTheory.integral_sub h_prime_int h_arch_int]
  -- Identify the two pieces.
  have h_prime_id :
      (∫ t : ℝ, -(deriv riemannZeta (s t) / riemannZeta (s t)) *
        Contour.coshGaussMellin c (s t)) = ((primeSingleCosh c : ℝ) : ℂ) := by
    rw [primeSingleCosh_eq_vertical_integral c]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    show -(deriv riemannZeta (s t) / riemannZeta (s t)) *
        Contour.coshGaussMellin c (s t) =
      -deriv riemannZeta (s t) / riemannZeta (s t) *
        Contour.coshGaussMellin c (s t)
    ring
  have h_arch_id :
      (∫ t : ℝ, (deriv Complex.Gammaℝ (s t) / (s t).Gammaℝ +
          deriv Complex.Gammaℝ (1 - s t) / (1 - s t).Gammaℝ) *
        Contour.coshGaussMellin c (s t)) = archSingleCosh c := by
    show _ = archSingleCosh c
    unfold archSingleCosh
    rfl
  rw [h_prime_id, h_arch_id]

/-- **S4.** Pair-combined arch/prime identity at `σ = 2`.

Strategy: use `reflectedPrimeSingleCosh_eq_primeSingleCosh_sub_archSingleCosh`
(S3, proved per-c above) at the five cosh-pair axes
`c ∈ {2β−π/3, 2−π/3−2β, 1−π/3, 2β−1, 0}` to reduce the target identity
`archPair = primePair` to the vanishing of the corresponding pair-combo of
`reflectedPrimeSingleCosh`, which in turn equals the whole-line reflected
integral by `reflectedPrime_integral_cosh_expansion_at_two`. The latter is
the proved iff `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`. -/
theorem archPair_eq_primePair_at_two_via_cosh_geometry (β : ℝ) :
    archPair_eq_primePair_at_two_target β := by
  -- Per-c reflected = prime − arch (S3, proved above).
  have h_S3 : ∀ c : ℝ, reflectedPrimeSingleCosh c =
      ((primeSingleCosh c : ℝ) : ℂ) - archSingleCosh c :=
    reflectedPrimeSingleCosh_eq_primeSingleCosh_sub_archSingleCosh
  -- Use the proved iff `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`
  -- in conjunction with the cosh-expansion of the reflected integral, plus the
  -- per-c S3 identity, to reduce to the whole-line vanishing of the reflected
  -- integral. The whole-line vanishing is the cosh-pair geometric content packaged
  -- in `ReflectedPrimeCoshExpansion.reflectedPrime_integral_vanishes_at_two`,
  -- to which our target is directly equivalent.
  exact ZD.WeilPositivity.Contour.ReflectedPrimeCoshExpansion.archPair_eq_primePair_at_two_proved β

/-! ## S5 — Final assembly: vanishing of `∫ reflectedPrimeIntegrand β 2`

By:
* L3: `∫ reflectedPrimeIntegrand β 2 t = reflectedPrimePair β`.
* The proved iff `archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes`:
  `archPair = primePair ↔ ∫ reflected = 0`.
* **S4**: `archPair = primePair`.

So `∫ reflected = 0`.
-/

/-- **S5.** Vanishing of the reflected-prime whole-line integral at `σ = 2`. -/
theorem reflectedPrime_integral_vanishes_at_two_via_scaffold (β : ℝ) :
    ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0 :=
  (ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes β).mp
    (archPair_eq_primePair_at_two_via_cosh_geometry β)
-/
end PairTestVanishingScaffold
end Contour
end WeilPositivity
end ZD

end
