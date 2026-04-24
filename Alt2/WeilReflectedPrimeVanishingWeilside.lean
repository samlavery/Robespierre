import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.ArchOperatorBound

/-!
# B.5.b Step 1: Reflected-prime integral vanishes at σ₀ = 2

**Target theorem**:
```
∀ β : ℝ,  ∫_ℝ reflectedPrimeIntegrand β 2 t dt  =  0.
```
equivalently (via `ArchOperatorBound.weilArchPrimeIdentityTarget_at_two`):
```
∀ β : ℝ,  ∫_ℝ archIntegrand β 2 t dt  =  ∫_ℝ primeIntegrand β 2 t dt.
```

This is the classical Weil arch–prime identity at σ = 2 for the cosh-Gauss
pair test function.  Substantive analytic content.

## Pipeline scaffold

The single 400–600 line direct proof is split into four independent helpers
followed by a trivial assembly.  Each helper is an isolated, agent-attackable
statement.

| # | Lemma                                        | Nature                    | Rough LOC |
|---|----------------------------------------------|---------------------------|-----------|
| H1 | `arch_integral_cosh_expansion_at_two`        | Linearity of integration  |  60       |
| H2 | `prime_integral_cosh_expansion_at_two`       | Linearity + `primeIntegrand_integral_eq_prime_sum` |  60       |
| H3 | `archSingleCosh_eq_primeSingleCosh`          | **Classical Weil for single cosh-Gauss** | 150–300 |
| H4 | A1 assembly from H1 + H2 + H3                | Linear combination        |  30       |

H1 and H2 are mechanical linearity applications.  **H3 is the load-bearing
analytic content** — the classical Weil explicit formula specialized to the
single test function `h_c(x) = cosh(c·x) · exp(-2x²)`.  H4 trivially assembles.

## Consumer wiring

Feeds `WeilRectangleVanishes.reflected_prime_integral_vanishes_at_two_for_cosh_pair`
(consumer form at line 125 of this file).  Downstream: B.5.b rectangle
vanishes → Field 5 of `WeilFinalAssemblyBundle`.

## Axiom footprint (target)

After H1, H2, H3 are discharged: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace ReflectedPrimeVanishing

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helper definitions — single-cosh arch and prime quantities
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Arch integral for the single cosh-Gauss test `h_c(x) = cosh(c·x)·exp(-2x²)`.**
The integral `∫_t [Γℝ'/Γℝ(2+it) + Γℝ'/Γℝ(-1-it)] · coshGaussMellin c (2+it) dt`
paired against the cosh-Gauss Mellin at `s = 2+it`. -/
noncomputable def archSingleCosh (c : ℝ) : ℂ :=
  ∫ t : ℝ,
    (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
        ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
    Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)

/-- **Prime sum for the single cosh-Gauss test.** Von Mangoldt-weighted sum
`2π · Σ_n Λ(n) · cosh(c·n) · exp(-2n²)`. Real-valued. -/
noncomputable def primeSingleCosh (c : ℝ) : ℝ :=
  2 * Real.pi *
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2))

-- ═══════════════════════════════════════════════════════════════════════════
-- § H1 — Arch-side cosh expansion at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### H1 helpers: quadratic-decay + integrability for `coshGaussMellin c (2+it)`

Build IBP×2 machinery on `h_c(t) = cosh(c·t)·exp(-2t²)` at σ = 2, paralleling
`pairTestMellin_ibp_twice`. The resulting quadratic decay
`‖coshGaussMellin c (2+it)‖ ≤ K/(1+t²)` combines with `arch_subunit_bound_at_two`
to give per-piece integrability on ℝ. -/

/-- **Mellin convergent of `coshGaussDerivVal c` on `Re s > 0`.** Continuous
everywhere (polynomial · cosh/sinh · exp), `O(exp(-t/2))` at `∞`, continuous at 0
so `O(1)` near 0⁺. -/
private theorem h1_mellinConv_coshGaussDerivVal (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    unfold Contour.coshGaussDerivVal
    fun_prop
  · have h := Contour.coshGauss_deriv_isBigO_exp_neg_half_atTop c
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]
    unfold Contour.coshGaussDerivVal
    exact h
  · -- coshGaussDerivVal c 0 = 0 · cosh 0 - 0 = 0, continuous at 0, so O(1) near 0⁺.
    have h_cont : Continuous
        (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      unfold Contour.coshGaussDerivVal
      fun_prop
    have h_tendsto : Filter.Tendsto
        (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ))
        (nhdsWithin 0 (Ioi 0))
        (nhds ((Contour.coshGaussDerivVal c 0 : ℝ) : ℂ)) :=
      (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
      funext x; rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq]
    exact h_tendsto.isBigO_one ℝ
  · exact hs

/-- **Mellin convergent of `coshGaussDeriv2Val c` on `Re s > 0`.** -/
private theorem h1_mellinConv_coshGaussDeriv2Val (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun t : ℝ => ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0)
    (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    unfold Contour.coshGaussDeriv2Val
    fun_prop
  · have h := Contour.coshGaussDeriv2Val_isBigO_exp_neg_half_atTop c
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]; exact h
  · -- continuous at 0, so O(1) near 0⁺.
    have h_cont : Continuous
        (fun t : ℝ => ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      unfold Contour.coshGaussDeriv2Val
      fun_prop
    have h_tendsto : Filter.Tendsto
        (fun t : ℝ => ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ))
        (nhdsWithin 0 (Ioi 0))
        (nhds ((Contour.coshGaussDeriv2Val c 0 : ℝ) : ℂ)) :=
      (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
      funext x; rw [neg_zero, Real.rpow_zero]
    rw [h_rpow_eq]
    exact h_tendsto.isBigO_one ℝ
  · exact hs

/-- **Boundary vanishing of `cosh(c·t)·exp(-2t²) · t^s` at `t → 0⁺`.** For `Re s > 0`.
`h_c(0) = 1`, `h_c` bounded near 0, and `|t^s| = t^Re(s) → 0`. -/
private theorem h1_coshGauss_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun t : ℝ =>
        ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cont : Continuous (fun t : ℝ =>
      ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    fun_prop
  -- Strategy: `‖f(t)·t^s‖ = ‖f(t)‖ · t^{Re s}`, `‖f‖ ≤ 2` near 0, so pick δ
  -- so that `t^{Re s} < ε/2`. Since `f(0) = 1`, we use `‖f(t) - 1‖ < 1 → ‖f(t)‖ < 2`.
  have h_f_at_zero : ((Real.cosh (c * 0) * Real.exp (-2 * 0^2) : ℝ) : ℂ) = 1 := by
    push_cast; simp [Real.cosh_zero]
  have h_tendsto_f : Filter.Tendsto (fun t : ℝ =>
      ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) (nhds 0) (nhds 1) := by
    have hcont_at := (h_cont.continuousAt (x := 0)).tendsto
    rw [show (1 : ℂ) =
      ((Real.cosh (c * 0) * Real.exp (-2 * 0^2) : ℝ) : ℂ) from h_f_at_zero.symm]
    exact hcont_at
  rw [Metric.tendsto_nhds_nhds] at h_tendsto_f
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h_tendsto_f 1 (by norm_num : (0:ℝ) < 1)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε_half_pos : (0:ℝ) < ε / 2 := by linarith
  refine ⟨min δ₁ ((ε/2) ^ (1 / s.re)),
    lt_min hδ₁_pos (Real.rpow_pos_of_pos hε_half_pos _), ?_⟩
  intro t ht_pos ht_δ
  have h_t_lt_δ₁ : dist t 0 < δ₁ := lt_of_lt_of_le ht_δ (min_le_left _ _)
  have h_t_lt_ε_rpow : dist t 0 < (ε/2) ^ (1 / s.re) :=
    lt_of_lt_of_le ht_δ (min_le_right _ _)
  have h_f_norm_lt : ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ < 2 := by
    have h_f_close : dist
        ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) 1 < 1 := hδ₁ h_t_lt_δ₁
    have h_triangle : ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ ≤
        ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) - 1) 1
      simpa using this
    have h_norm_sub : ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) - 1‖ < 1 := by
      rw [← dist_eq_norm]; exact h_f_close
    have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
    linarith
  have h_t_cpow_norm : ‖(t : ℂ)^s‖ = t^s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos s
  have h_t_lt_ε_rpow_abs : t < (ε/2) ^ (1 / s.re) := by
    rw [Real.dist_eq, sub_zero] at h_t_lt_ε_rpow
    rw [abs_of_pos ht_pos] at h_t_lt_ε_rpow
    exact h_t_lt_ε_rpow
  have h_t_rpow_lt : t ^ s.re < ε/2 := by
    calc t ^ s.re < ((ε/2) ^ (1 / s.re)) ^ s.re :=
          Real.rpow_lt_rpow (le_of_lt ht_pos) h_t_lt_ε_rpow_abs hs
      _ = (ε/2) ^ ((1 / s.re) * s.re) := by rw [← Real.rpow_mul (le_of_lt hε_half_pos)]
      _ = (ε/2) ^ (1:ℝ) := by rw [div_mul_cancel₀ _ hs.ne']
      _ = ε/2 := Real.rpow_one _
  have h_t_rpow_pos : 0 < t ^ s.re := Real.rpow_pos_of_pos ht_pos _
  calc dist (((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) * (t : ℂ)^s) 0
      = ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) * (t : ℂ)^s‖ := by
        rw [dist_zero_right]
    _ = ‖((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ * t^s.re := by
        rw [norm_mul, h_t_cpow_norm]
    _ < 2 * (ε/2) := by
        apply mul_lt_mul h_f_norm_lt h_t_rpow_lt.le h_t_rpow_pos
          (by norm_num : (0:ℝ) ≤ 2)
    _ = ε := by ring

/-- **Boundary vanishing of `cosh(c·t)·exp(-2t²) · t^s` at `t → ∞`.** The cosh-Gauss
is `O(exp(-t))` at infinity (via `coshGauss_isBigO_exp_neg_atTop`), so dominates any
polynomial `t^Re(s)`. -/
private theorem h1_coshGauss_cpow_tendsto_zero_atTop (c : ℝ) (s : ℂ) :
    Filter.Tendsto
      (fun t : ℝ =>
        ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) := by
  have h_bigO : (fun t : ℝ =>
      ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) * (t : ℂ)^s) =O[atTop]
      (fun t : ℝ => Real.exp (-t) * t^(s.re)) := by
    have h1 := Contour.coshGauss_isBigO_exp_neg_atTop c
    have h_cpow_bigO : (fun t : ℝ => (t : ℂ)^s) =O[atTop] (fun t : ℝ => t^s.re) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
    exact h1.mul h_cpow_bigO
  have h_tendsto_dom : Filter.Tendsto (fun t : ℝ => Real.exp (-t) * t^(s.re))
      atTop (nhds 0) := by
    have h_lit : (fun t : ℝ => t^s.re) =o[atTop] (fun t : ℝ => Real.exp ((1:ℝ) * t)) :=
      isLittleO_rpow_exp_pos_mul_atTop s.re (by norm_num : (0:ℝ) < 1)
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t^s.re / Real.exp ((1:ℝ) * t))
        atTop (nhds 0) := h_lit.tendsto_div_nhds_zero
    have h_eq : (fun t : ℝ => Real.exp (-t) * t^(s.re)) =
        (fun t : ℝ => t^s.re / Real.exp ((1:ℝ) * t)) := by
      funext t
      rw [show (-t : ℝ) = -((1:ℝ) * t) from by ring, Real.exp_neg]
      field_simp
    rw [h_eq]; exact h_tendsto
  exact h_bigO.trans_tendsto h_tendsto_dom

/-- **Boundary vanishing of `coshGaussDerivVal c t · t^s` at `t → 0⁺`.** For `Re s > 0`.
`coshGaussDerivVal c 0 = 0`, so the value at 0 is 0, and continuity gives tendsto. -/
private theorem h1_coshGaussDeriv_cpow_tendsto_zero_nhdsWithin_zero
    (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cont : Continuous
      (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    unfold Contour.coshGaussDerivVal
    fun_prop
  have h_val_zero : Contour.coshGaussDerivVal c 0 = 0 := by
    simp [Contour.coshGaussDerivVal, Real.sinh_zero]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h_tendsto : Filter.Tendsto (fun t : ℝ =>
      ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) (nhds 0) (nhds 0) := by
    have hcont_at := (h_cont.continuousAt (x := 0)).tendsto
    rw [show (0 : ℂ) = ((Contour.coshGaussDerivVal c 0 : ℝ) : ℂ) from by
      rw [h_val_zero]; push_cast; rfl]
    exact hcont_at
  rw [Metric.tendsto_nhds_nhds] at h_tendsto
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h_tendsto 1 (by norm_num : (0:ℝ) < 1)
  refine ⟨min δ₁ (ε ^ (1 / s.re)),
    lt_min hδ₁_pos (Real.rpow_pos_of_pos hε _), ?_⟩
  intro t ht_pos ht_δ
  have h_t_lt_δ₁ : dist t 0 < δ₁ := lt_of_lt_of_le ht_δ (min_le_left _ _)
  have h_t_lt_ε_rpow : dist t 0 < ε ^ (1 / s.re) := lt_of_lt_of_le ht_δ (min_le_right _ _)
  have h_deriv_lt : ‖((Contour.coshGaussDerivVal c t : ℝ) : ℂ)‖ < 1 := by
    have := hδ₁ h_t_lt_δ₁
    rw [dist_zero_right] at this
    exact this
  have h_t_cpow_norm : ‖(t : ℂ)^s‖ = t^s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos s
  have h_t_lt_ε_rpow_abs : t < ε ^ (1 / s.re) := by
    rw [Real.dist_eq, sub_zero] at h_t_lt_ε_rpow
    rw [abs_of_pos ht_pos] at h_t_lt_ε_rpow
    exact h_t_lt_ε_rpow
  have h_t_rpow_lt : t ^ s.re < ε := by
    calc t ^ s.re < (ε ^ (1 / s.re)) ^ s.re :=
          Real.rpow_lt_rpow (le_of_lt ht_pos) h_t_lt_ε_rpow_abs hs
      _ = ε ^ ((1 / s.re) * s.re) := by rw [← Real.rpow_mul (le_of_lt hε)]
      _ = ε ^ (1:ℝ) := by rw [div_mul_cancel₀ _ hs.ne']
      _ = ε := Real.rpow_one ε
  have h_t_rpow_pos : 0 < t ^ s.re := Real.rpow_pos_of_pos ht_pos _
  calc dist (((Contour.coshGaussDerivVal c t : ℝ) : ℂ) * (t : ℂ)^s) 0
      = ‖((Contour.coshGaussDerivVal c t : ℝ) : ℂ)‖ * t^s.re := by
        rw [dist_zero_right, norm_mul, h_t_cpow_norm]
    _ < 1 * ε := by
        apply mul_lt_mul h_deriv_lt h_t_rpow_lt.le h_t_rpow_pos
          (by norm_num : (0:ℝ) ≤ 1)
    _ = ε := by ring

/-- **Boundary vanishing of `coshGaussDerivVal c t · t^s` at `t → ∞`.** -/
private theorem h1_coshGaussDeriv_cpow_tendsto_zero_atTop (c : ℝ) (s : ℂ) :
    Filter.Tendsto
      (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) := by
  have h_bigO : (fun t : ℝ =>
      ((Contour.coshGaussDerivVal c t : ℝ) : ℂ) * (t : ℂ)^s) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) := by
    have h1 : (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
      unfold Contour.coshGaussDerivVal
      exact Contour.coshGauss_deriv_isBigO_exp_neg_half_atTop c
    have h_cpow_bigO : (fun t : ℝ => (t : ℂ)^s) =O[atTop] (fun t : ℝ => t^s.re) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
    exact h1.mul h_cpow_bigO
  have h_tendsto_dom : Filter.Tendsto (fun t : ℝ => Real.exp (-t/2) * t^(s.re))
      atTop (nhds 0) := by
    have h_lit : (fun t : ℝ => t^s.re) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) :=
      isLittleO_rpow_exp_pos_mul_atTop s.re (by norm_num : (0:ℝ) < 1/2)
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t^s.re / Real.exp ((1/2) * t))
        atTop (nhds 0) := h_lit.tendsto_div_nhds_zero
    have h_eq : (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) =
        (fun t : ℝ => t^s.re / Real.exp ((1/2) * t)) := by
      funext t
      rw [show (-t/2 : ℝ) = -((1/2) * t) from by ring, Real.exp_neg]
      field_simp
    rw [h_eq]; exact h_tendsto
  exact h_bigO.trans_tendsto h_tendsto_dom

/-- **First IBP**: `coshGaussMellin c s = -(1/s) · mellin(coshGaussDerivVal c) (s+1)` for `Re s > 0`. -/
private theorem h1_coshGaussMellin_ibp_once (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Contour.coshGaussMellin c s =
      -(1/s) * mellin (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) (s + 1) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  -- Unfold coshGaussMellin as a mellin of a specific function shape matching mellin_ibp.
  -- coshGaussMellin c s := mellin (fun t => (Real.cosh (c*t) * Real.exp (-2*t^2) : ℂ)) s.
  -- Lean often desugars the ofReal coercion as product of coercions; normalize to
  -- the uncoerced-product form via push_cast.
  have h_fun_eq : (fun t : ℝ => (Real.cosh (c * t) * Real.exp (-2 * t ^ 2) : ℂ)) =
      (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t ^ 2) : ℝ) : ℂ)) := by
    funext t; push_cast; ring
  unfold Contour.coshGaussMellin
  rw [h_fun_eq]
  -- Coerced HasDerivAt of cosh(c·t)·exp(-2t²).
  have h_cder : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => ((Real.cosh (c * u) * Real.exp (-2 * u^2) : ℝ) : ℂ))
        ((Contour.coshGaussDerivVal c t : ℝ) : ℂ) t := by
    intro t
    have h_real := Contour.coshGauss_hasDerivAt c t
    have h_real' : HasDerivAt (fun u : ℝ => Real.cosh (c * u) * Real.exp (-2 * u^2))
        (Contour.coshGaussDerivVal c t) t := by
      unfold Contour.coshGaussDerivVal; exact h_real
    exact h_real'.ofReal_comp
  refine mellin_ibp (s := s) hs_ne (fun t _ => h_cder t) ?_ ?_ ?_ ?_
  · exact Contour.mellinConvergent_coshGauss c hs
  · exact h1_mellinConv_coshGaussDerivVal c hs1_re
  · exact h1_coshGauss_cpow_tendsto_zero_nhdsWithin_zero c hs
  · exact h1_coshGauss_cpow_tendsto_zero_atTop c s

/-- **Second IBP**: `mellin(coshGaussDerivVal c) (s+1) = -(1/(s+1)) · mellin(coshGaussDeriv2Val c) (s+2)` for `Re s > 0`. -/
private theorem h1_coshGaussDerivMellin_ibp_once (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Contour.coshGaussDerivVal c t : ℝ) : ℂ)) (s + 1) =
      -(1/(s+1)) * mellin (fun t : ℝ => ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ)) (s + 2) := by
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have h_rewrite : s + 1 + 1 = s + 2 := by ring
  -- HasDerivAt for coerced coshGaussDerivVal.
  have h_cder : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => ((Contour.coshGaussDerivVal c u : ℝ) : ℂ))
        ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ) t := by
    intro t
    exact (Contour.coshGauss_hasDerivAt_iter2 c t).ofReal_comp
  have := mellin_ibp (s := s + 1) hs1_ne
    (fun t _ => h_cder t)
    (h1_mellinConv_coshGaussDerivVal c hs1_re)
    (by rw [h_rewrite]; exact h1_mellinConv_coshGaussDeriv2Val c hs2_re)
    (h1_coshGaussDeriv_cpow_tendsto_zero_nhdsWithin_zero c hs1_re)
    (h1_coshGaussDeriv_cpow_tendsto_zero_atTop c (s + 1))
  rw [h_rewrite] at this
  exact this

/-- **IBP×2**: `coshGaussMellin c s = 1/(s·(s+1)) · mellin(coshGaussDeriv2Val c) (s+2)`. -/
private theorem h1_coshGaussMellin_ibp_twice (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Contour.coshGaussMellin c s =
      1/(s * (s + 1)) *
        mellin (fun t : ℝ => ((Contour.coshGaussDeriv2Val c t : ℝ) : ℂ)) (s + 2) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  rw [h1_coshGaussMellin_ibp_once c hs, h1_coshGaussDerivMellin_ibp_once c hs]
  field_simp

/-- **Norm bound on `mellin(coshGaussDeriv2Val c)` at σ = 4**: the absolute integral
`∫_Ioi 0 u^3 · |coshGaussDeriv2Val c u| du` majorizes the Mellin norm. -/
private theorem h1_coshGaussDeriv2Mellin_bound (c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖mellin (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
        ((4 : ℂ) + (t : ℂ) * I)‖ ≤ M := by
  -- Real-valued integrand with polynomial-weighted Mellin.
  have hConv := h1_mellinConv_coshGaussDeriv2Val c
    (show (0:ℝ) < ((4:ℂ) : ℂ).re by simp)
  have hConv2 : IntegrableOn
      (fun u : ℝ => (u : ℂ)^((4 : ℂ) - 1) •
        ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)) (Ioi 0) := hConv
  -- The norm of the integrand, as a function of u, is `u^3 * |deriv2(u)|`.
  set h : ℝ → ℝ := fun u : ℝ => u^((3:ℝ)) * |Contour.coshGaussDeriv2Val c u| with h_def
  have h_h_int : IntegrableOn h (Ioi (0:ℝ)) := by
    have hnorm := hConv2.norm
    refine (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).mp hnorm
    have hu_pos : (0:ℝ) < u := hu
    show ‖(u : ℂ)^((4 : ℂ) - 1) • ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖ = h u
    simp only [norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos, Complex.norm_real, Real.norm_eq_abs]
    show u ^ ((4 : ℂ) - 1).re * |Contour.coshGaussDeriv2Val c u| = h u
    show u ^ ((4 : ℂ) - 1).re * |Contour.coshGaussDeriv2Val c u| =
      u^((3:ℝ)) * |Contour.coshGaussDeriv2Val c u|
    have h_re : ((4 : ℂ) - 1).re = 3 := by
      rw [Complex.sub_re]
      norm_num
    rw [h_re]
  set J : ℝ := ∫ u in Ioi (0:ℝ), h u with hJ_def
  have hJ_nn : (0:ℝ) ≤ J := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro u hu
    show 0 ≤ h u
    rw [h_def]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (abs_nonneg _)
  refine ⟨J, hJ_nn, fun t => ?_⟩
  set s₀ : ℂ := (4 : ℂ) + (t : ℂ) * I with hs₀_def
  have hs₀_re : s₀.re = 4 := by simp [s₀]
  have h_norm_le : ‖mellin (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)) s₀‖ ≤
      ∫ u in Ioi (0:ℝ), u^(s₀.re - 1) * |Contour.coshGaussDeriv2Val c u| := by
    unfold mellin
    calc ‖∫ u in Ioi (0:ℝ), (u:ℂ)^(s₀-1) •
            ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖
        ≤ ∫ u in Ioi (0:ℝ), ‖(u:ℂ)^(s₀-1) •
            ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ u in Ioi (0:ℝ), u^(s₀.re - 1) *
            |Contour.coshGaussDeriv2Val c u| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
          simp only [norm_smul]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
              Complex.sub_re, Complex.one_re, Real.norm_eq_abs]
  rw [hs₀_re] at h_norm_le
  have h_eq_J : (∫ u in Ioi (0:ℝ), u^((4:ℝ) - 1) * |Contour.coshGaussDeriv2Val c u|) = J := by
    show (∫ u in Ioi (0:ℝ), u^((4:ℝ) - 1) * |Contour.coshGaussDeriv2Val c u|) =
      ∫ u in Ioi (0:ℝ), h u
    apply MeasureTheory.integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u _
    show u^((4:ℝ) - 1) * |Contour.coshGaussDeriv2Val c u| =
      u^((3:ℝ)) * |Contour.coshGaussDeriv2Val c u|
    congr 2
    norm_num
  rw [h_eq_J] at h_norm_le
  -- Now h_norm_le : ‖mellin _ s₀‖ ≤ J. Target uses (4 + t·I) not s₀.
  show ‖mellin (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
      ((4 : ℂ) + (t : ℂ) * I)‖ ≤ J
  exact h_norm_le

/-- **Quadratic decay for `coshGaussMellin c` on vertical line σ = 2**:
`‖coshGaussMellin c (2+it)‖ ≤ K/(1+t²)` for some `K ≥ 0`. -/
private theorem h1_coshGaussMellin_global_quadratic_bound (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ ≤ K / (1 + t^2) := by
  -- Bound via: coshGaussMellin c (2+it) = 1/((2+it)(3+it)) · mellin(coshGaussDeriv2Val c) (4+it).
  -- |1/((2+it)(3+it))| = 1/(√(4+t²)·√(9+t²)) ≤ 1/((2+|t|)(3+|t|)) isn't quite right,
  -- but we can bound |1/(s(s+1))| by 1/max(|t|²,6) and get K/(1+t²).
  obtain ⟨M, hM_nn, hM_bd⟩ := h1_coshGaussDeriv2Mellin_bound c
  -- Need K ≥ (1 + t²) · M / |s(s+1)| for all t. For |t| ≥ 1: |s(s+1)| ≥ |t|² ≥ (1+t²)/2,
  -- giving ratio ≤ 2M. For |t| ≤ 1: |s(s+1)| = |(2+it)(3+it)| ≥ |(2)(3)| = 6,
  -- giving ratio ≤ (1+t²)·M/6 ≤ 2M/6 = M/3.
  refine ⟨2 * M, by positivity, fun t => ?_⟩
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs_def
  have hs_re : s.re = 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have h_ibp := h1_coshGaussMellin_ibp_twice c (show (0:ℝ) < s.re by rw [hs_re]; norm_num)
  -- Rewrite s + 2 to match bound form (4 + ti).
  have h_s_plus_2 : s + 2 = (4 : ℂ) + (t : ℂ) * I := by
    rw [hs_def]; push_cast; ring
  rw [h_ibp, h_s_plus_2]
  rw [norm_mul, norm_div, norm_one]
  have h_M_at_t := hM_bd t
  -- Need: 1/‖s(s+1)‖ · M ≤ 2M / (1 + t²).
  -- Equivalent: (1 + t²) ≤ 2 · ‖s(s+1)‖ when M > 0.
  have h_1plus_pos : (0:ℝ) < 1 + t^2 := by have := sq_nonneg t; linarith
  have h_s_sq_re_im : Complex.normSq s = 4 + t^2 := by
    rw [Complex.normSq_apply, hs_re, hs_im]; ring
  have h_s_norm_sq : ‖s‖^2 = 4 + t^2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact h_s_sq_re_im
  have h_s_norm_nn : 0 ≤ ‖s‖ := norm_nonneg _
  have h_s1_im : (s + 1).im = t := by rw [Complex.add_im, hs_im]; simp
  have h_s1_re : (s + 1).re = 3 := by
    rw [Complex.add_re, hs_re]
    show (2 : ℝ) + (1 : ℂ).re = 3
    simp
    norm_num
  have h_s1_norm_sq : ‖s + 1‖^2 = 9 + t^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h_s1_re, h_s1_im]; ring
  have h_s1_norm_nn : 0 ≤ ‖s + 1‖ := norm_nonneg _
  have h_prod_norm_sq : ‖s * (s + 1)‖^2 = (4 + t^2) * (9 + t^2) := by
    rw [norm_mul, mul_pow, h_s_norm_sq, h_s1_norm_sq]
  -- (4+t²)(9+t²) ≥ (1 + t²)² / 4 · 4 = (1+t²)²? Check: 4·9 = 36 ≥ (1+t²)²/... hmm.
  -- Simpler: (4+t²)(9+t²) = 36 + 13t² + t^4 ≥ 36 (always), and ≥ (1+t²)² / K for suitable K.
  -- We want: (4+t²)(9+t²) ≥ (1+t²)²/4 ⟺ 4(4+t²)(9+t²) ≥ (1+t²)² ⟺ 4(36+13t²+t^4) ≥ 1+2t²+t^4
  -- ⟺ 144 + 52t² + 4t^4 ≥ 1 + 2t² + t^4 ⟺ 3t^4 + 50t² + 143 ≥ 0 ✓.
  have h_prod_norm_ge : (1 + t^2)^2 ≤ 4 * ‖s * (s + 1)‖^2 := by
    rw [h_prod_norm_sq]
    nlinarith [sq_nonneg t, sq_nonneg (t^2)]
  have h_s_ne : s ≠ 0 := by
    intro h
    have : s.re = 0 := by rw [h]; simp
    rw [hs_re] at this; exact absurd this (by norm_num)
  have h_s1_ne : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [h_s1_re] at this; exact absurd this (by norm_num)
  have h_prod_norm_pos : 0 < ‖s * (s + 1)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero h_s_ne h_s1_ne
  have h_1plus_le : 1 + t^2 ≤ 2 * ‖s * (s + 1)‖ := by
    have h_lhs_nn : 0 ≤ 1 + t^2 := h_1plus_pos.le
    have h_sq_le : (1 + t^2)^2 ≤ (2 * ‖s * (s + 1)‖)^2 := by
      rw [mul_pow]
      have h_two_sq : (2:ℝ)^2 = 4 := by norm_num
      rw [h_two_sq]; linarith [h_prod_norm_ge]
    have h_rhs_nn : 0 ≤ 2 * ‖s * (s + 1)‖ := by positivity
    -- Both nonneg; square inequality → linear inequality.
    have h_abs_eq_lhs : |1 + t^2| = 1 + t^2 := abs_of_nonneg h_lhs_nn
    have h_abs_eq_rhs : |2 * ‖s * (s + 1)‖| = 2 * ‖s * (s + 1)‖ :=
      abs_of_nonneg h_rhs_nn
    nlinarith [h_sq_le, sq_nonneg ((1 + t^2) - 2 * ‖s * (s + 1)‖)]
  -- Use the key inequality: 1/‖s(s+1)‖ ≤ 2/(1+t²).
  have h_div_bd : (1:ℝ) / ‖s * (s + 1)‖ ≤ 2 / (1 + t^2) := by
    rw [div_le_div_iff₀ h_prod_norm_pos h_1plus_pos]
    linarith
  calc 1 / ‖s * (s + 1)‖ * ‖mellin
          (fun u : ℝ => ((Contour.coshGaussDeriv2Val c u : ℝ) : ℂ))
          ((4 : ℂ) + (t : ℂ) * I)‖
      ≤ 1 / ‖s * (s + 1)‖ * M := by
        apply mul_le_mul_of_nonneg_left h_M_at_t
        positivity
    _ ≤ (2 / (1 + t^2)) * M := by
        apply mul_le_mul_of_nonneg_right h_div_bd hM_nn
    _ = 2 * M / (1 + t^2) := by ring

/-- **Per-piece integrability**: `arch_kernel(t) · coshGaussMellin c (2+it)` integrable on ℝ. -/
private theorem h1_arch_coshGaussMellin_integrable (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
          ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C, N, hC_nn, hN_nn, hN_lt_1, h_arch_bd⟩ := arch_subunit_bound_at_two
  obtain ⟨K, hK_nn, h_pair_bd⟩ := h1_coshGaussMellin_global_quadratic_bound c
  set α : ℝ := (N - 2) / 2 with hα_def
  have h_r_gt_one : (1 : ℝ) < 2 - N := by linarith
  have h_rpow_integrable :
      MeasureTheory.Integrable
        (fun t : ℝ => (1 + ‖t‖^2)^(-(2 - N) / 2)) MeasureTheory.volume := by
    apply integrable_rpow_neg_one_add_norm_sq
    · rw [Module.finrank_self]
      exact_mod_cast h_r_gt_one
  have h_rpow_integrable' :
      MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)^α) := by
    refine h_rpow_integrable.congr (MeasureTheory.ae_of_all _ ?_)
    intro t
    show (1 + ‖t‖^2)^(-(2 - N) / 2) = (1 + t^2)^α
    have h_norm_sq : ‖t‖^2 = t^2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [h_norm_sq]; congr 1; rw [hα_def]; ring
  have h_majorant_int :
      MeasureTheory.Integrable
        (fun t : ℝ => C * K * (2^(N/2) * (1 + t^2)^α)) := by
    have h1 := h_rpow_integrable'.const_mul (2^(N/2))
    have h2 := h1.const_mul (C * K)
    refine h2.congr (MeasureTheory.ae_of_all _ ?_)
    intro t; ring
  -- Pointwise bound.
  have h_ptwise : ∀ t : ℝ,
      ‖(deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
            ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
            (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
        Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      C * K * (2^(N/2) * (1 + t^2)^α) := by
    intro t
    rw [norm_mul]
    have h_arch_t := h_arch_bd t
    -- Bridge (2:ℝ):ℂ vs (2:ℂ).
    have h_arch_t' :
        ‖deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
            ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
            (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ‖ ≤ C * (1 + |t|)^N := by
      have h_cast : ((2:ℝ) : ℂ) = (2 : ℂ) := by push_cast; rfl
      rw [← h_cast]; exact h_arch_t
    have h_pair_t := h_pair_bd t
    have h_pair_nn : (0 : ℝ) ≤ ‖Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ :=
      norm_nonneg _
    have h_arch_rhs_nn : (0 : ℝ) ≤ C * (1 + |t|)^N :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by linarith [abs_nonneg t]) _)
    have h_pair_rhs_nn : (0 : ℝ) ≤ K / (1 + t^2) := by positivity
    have h_maj_pos : (0 : ℝ) ≤ 2^(N/2) := Real.rpow_nonneg (by norm_num) _
    calc ‖deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
              ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
            deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
              (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ‖ *
            ‖Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖
        ≤ (C * (1 + |t|)^N) * (K / (1 + t^2)) :=
          mul_le_mul h_arch_t' h_pair_t h_pair_nn h_arch_rhs_nn
      _ = C * K * ((1 + |t|)^N / (1 + t^2)) := by ring
      _ ≤ C * K * (2^(N/2) * (1 + t^2)^α) := by
          -- (1+|t|)^N / (1+t²) ≤ 2^(N/2) · (1+t²)^((N-2)/2) via `(1+|t|)² ≤ 2(1+t²)`.
          have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
          have h_base_nn : (0 : ℝ) ≤ 1 + |t| := by linarith
          have h_t_sq_nn : (0 : ℝ) ≤ 1 + t^2 := by positivity
          have h_t_sq_pos : (0 : ℝ) < 1 + t^2 := by positivity
          have h_one_plus_abs_sq : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
            have h_t_sq : |t|^2 = t^2 := sq_abs t
            have h_twoabs : 2 * |t| ≤ 1 + |t|^2 := by nlinarith [sq_nonneg (|t| - 1)]
            nlinarith [h_t_sq, h_twoabs]
          have h_pow_bd : (1 + |t|)^N ≤ 2^(N/2) * (1 + t^2)^(N/2) := by
            have hN_half_nn : (0 : ℝ) ≤ N / 2 := by linarith
            have h_lhs_eq : ((1 + |t|)^2)^(N/2) = (1 + |t|)^N := by
              rw [show ((1 + |t|)^2 : ℝ) = (1 + |t|)^(2 : ℕ) from rfl]
              rw [← Real.rpow_natCast (1 + |t|) 2]
              rw [← Real.rpow_mul h_base_nn]
              congr 1; push_cast; ring
            have h_rhs_eq : (2 * (1 + t^2))^(N/2) = 2^(N/2) * (1 + t^2)^(N/2) :=
              Real.mul_rpow (by norm_num) h_t_sq_nn
            rw [← h_lhs_eq, ← h_rhs_eq]
            exact Real.rpow_le_rpow (by positivity) h_one_plus_abs_sq hN_half_nn
          have h_compare : (1 + |t|)^N / (1 + t^2) ≤ 2^(N/2) * (1 + t^2)^((N - 2) / 2) := by
            have h_split : 2^(N/2) * (1 + t^2)^(N/2) / (1 + t^2) =
                2^(N/2) * (1 + t^2)^((N - 2) / 2) := by
              rw [mul_div_assoc]
              congr 1
              rw [div_eq_mul_inv, ← Real.rpow_neg_one (1 + t^2),
                ← Real.rpow_add h_t_sq_pos]
              congr 1; ring
            calc (1 + |t|)^N / (1 + t^2)
                ≤ 2^(N/2) * (1 + t^2)^(N/2) / (1 + t^2) :=
                  div_le_div_of_nonneg_right h_pow_bd h_t_sq_nn
              _ = 2^(N/2) * (1 + t^2)^((N - 2) / 2) := h_split
          rw [hα_def]
          apply mul_le_mul_of_nonneg_left h_compare (mul_nonneg hC_nn hK_nn)
  -- Measurability via continuity. Both factors are continuous functions of t.
  have h_line_cont : Continuous (fun t : ℝ => ((2 : ℂ) + (t : ℂ) * I)) := by fun_prop
  have h_refl_line_cont : Continuous (fun t : ℝ => 1 - ((2 : ℂ) + (t : ℂ) * I)) :=
    continuous_const.sub h_line_cont
  -- Γℝ and its derivative are analytic on {Γℝ ≠ 0}, but along Re s = 2 and Re s = -1 line,
  -- we have Γℝ ≠ 0 everywhere; use Contour.differentiableAt_Gammaℝ_of_ne_zero pointwise.
  have h_Gamma_bot_ne : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := by
    intro t
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    show (0 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re
    simp
  have h_Gamma_bot_refl_ne : ∀ t : ℝ, (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0 := by
    intro t h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : (1 - ((2 : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [hn]
    simp at hre
    have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
    omega
  have h_arch_cont : Continuous (fun t : ℝ =>
      deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
          ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) := by
    -- deriv Γℝ and Γℝ are continuous on {Γℝ ≠ 0} (an open set).
    -- Use Contour.differentiableAt_Gammaℝ_of_ne_zero to get DifferentiableOn, then composition.
    have h_diff_at : ∀ s : ℂ, s.Gammaℝ ≠ 0 →
        DifferentiableAt ℂ Complex.Gammaℝ s :=
      fun s hs => Contour.differentiableAt_Gammaℝ_of_ne_zero hs
    -- Continuity of Γℝ on each line (nonzero there) via DifferentiableAt → ContinuousAt.
    have h_Γ_cont_top : Continuous (fun t : ℝ => ((2 : ℂ) + (t : ℂ) * I).Gammaℝ) := by
      refine continuous_iff_continuousAt.mpr (fun t => ?_)
      -- Composition: t ↦ (2 + tI) ↦ Γℝ(-) at target point.
      have h_diff : DifferentiableAt ℂ Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) :=
        h_diff_at _ (h_Gamma_bot_ne t)
      have h_inner_cont : Continuous (fun u : ℝ => ((2 : ℂ) + (u : ℂ) * I)) := h_line_cont
      exact ContinuousAt.comp (f := fun u : ℝ => ((2 : ℂ) + (u : ℂ) * I))
        (g := Complex.Gammaℝ) h_diff.continuousAt h_inner_cont.continuousAt
    have h_Γ_cont_refl : Continuous (fun t : ℝ => (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) := by
      refine continuous_iff_continuousAt.mpr (fun t => ?_)
      have h_diff : DifferentiableAt ℂ Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) :=
        h_diff_at _ (h_Gamma_bot_refl_ne t)
      have h_inner_cont : Continuous (fun u : ℝ => (1 - ((2 : ℂ) + (u : ℂ) * I))) :=
        h_refl_line_cont
      exact ContinuousAt.comp (f := fun u : ℝ => (1 - ((2 : ℂ) + (u : ℂ) * I)))
        (g := Complex.Gammaℝ) h_diff.continuousAt h_inner_cont.continuousAt
    -- For `deriv Γℝ`, derivative of differentiable function is continuous on open set where
    -- it's differentiable. Use `AnalyticAt.continuousAt_deriv` or equivalent.
    -- Easier: note that `deriv Γℝ s = (Γℝ)' s` and on an open set where Γℝ is differentiable,
    -- using `DifferentiableOn → ContDiff → derivative continuous`? Direct path:
    -- Γℝ is analytic on {Γℝ ≠ 0} (open), so deriv Γℝ is analytic there, hence continuous.
    have h_Γ_analytic_top : ∀ t : ℝ,
        AnalyticAt ℂ Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) := by
      intro t
      have hs_ne : ((2 : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := h_Gamma_bot_ne t
      -- Differentiable at s + open neighborhood where differentiable → analytic at s.
      -- Γℝ is differentiable on {Γℝ ≠ 0} which is open.
      have h_open : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
        have h_Γ_inv_cont : Continuous (fun s : ℂ => (s.Gammaℝ)⁻¹) := by
          -- 1/Γℝ is entire.
          exact Complex.differentiable_Gammaℝ_inv.continuous
        -- {Γℝ ≠ 0} = {s : (Γℝ s)⁻¹ ≠ 0}, image of {0}ᶜ under continuous 1/Γℝ? Hmm.
        -- Use equivalent: {s : Γℝ s ≠ 0} = {s : 1/Γℝ s ≠ 0} (both sides nonzero iff nonzero).
        -- Actually 1/Γℝ entire, so {1/Γℝ ≠ 0} = {s : 1/Γℝ s ≠ 0} = {s : Γℝ s ≠ 0 ∨ ¬Γℝ s ≠ 0}... No.
        -- 1/0 = 0 in ℂ, so {1/Γℝ ≠ 0} = {Γℝ ≠ 0}. Use preimage:
        have : {s : ℂ | s.Gammaℝ ≠ 0} = (fun s : ℂ => (s.Gammaℝ)⁻¹) ⁻¹' {0}ᶜ := by
          ext s; simp [inv_eq_zero]
        rw [this]
        exact h_Γ_inv_cont.isOpen_preimage _ isOpen_compl_singleton
      have h_diff_on : DifferentiableOn ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
        intro s hs
        exact (h_diff_at s hs).differentiableWithinAt
      exact h_diff_on.analyticAt (h_open.mem_nhds hs_ne)
    have h_Γ_analytic_refl : ∀ t : ℝ,
        AnalyticAt ℂ Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) := by
      intro t
      have hs_ne : (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0 := h_Gamma_bot_refl_ne t
      have h_open : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
        have h_Γ_inv_cont : Continuous (fun s : ℂ => (s.Gammaℝ)⁻¹) :=
          Complex.differentiable_Gammaℝ_inv.continuous
        have : {s : ℂ | s.Gammaℝ ≠ 0} = (fun s : ℂ => (s.Gammaℝ)⁻¹) ⁻¹' {0}ᶜ := by
          ext s; simp [inv_eq_zero]
        rw [this]
        exact h_Γ_inv_cont.isOpen_preimage _ isOpen_compl_singleton
      have h_diff_on : DifferentiableOn ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
        intro s hs
        exact (h_diff_at s hs).differentiableWithinAt
      exact h_diff_on.analyticAt (h_open.mem_nhds hs_ne)
    have h_dΓ_cont_top : Continuous (fun t : ℝ =>
        deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I)) := by
      refine continuous_iff_continuousAt.mpr (fun t => ?_)
      have h_pt : ContinuousAt (deriv Complex.Gammaℝ) ((2 : ℂ) + (t : ℂ) * I) :=
        ((h_Γ_analytic_top t).deriv).continuousAt
      exact ContinuousAt.comp (f := fun u : ℝ => ((2 : ℂ) + (u : ℂ) * I))
        (g := deriv Complex.Gammaℝ) h_pt h_line_cont.continuousAt
    have h_dΓ_cont_refl : Continuous (fun t : ℝ =>
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I))) := by
      refine continuous_iff_continuousAt.mpr (fun t => ?_)
      have h_pt : ContinuousAt (deriv Complex.Gammaℝ) (1 - ((2 : ℂ) + (t : ℂ) * I)) :=
        ((h_Γ_analytic_refl t).deriv).continuousAt
      exact ContinuousAt.comp (f := fun u : ℝ => (1 - ((2 : ℂ) + (u : ℂ) * I)))
        (g := deriv Complex.Gammaℝ) h_pt h_refl_line_cont.continuousAt
    exact (h_dΓ_cont_top.div h_Γ_cont_top h_Gamma_bot_ne).add
      (h_dΓ_cont_refl.div h_Γ_cont_refl h_Gamma_bot_refl_ne)
  have h_coshMellin_cont : Continuous (fun t : ℝ =>
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
    have h_dA : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (Contour.coshGaussMellin c) s :=
      fun s hs => Contour.coshGaussMellin_differentiableAt c hs
    have h_diff_on : DifferentiableOn ℂ (Contour.coshGaussMellin c) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (h_dA s hs).differentiableWithinAt
    have h_cont_on : ContinuousOn (Contour.coshGaussMellin c) {s : ℂ | 0 < s.re} :=
      h_diff_on.continuousOn
    have h_map : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | 0 < s.re} := by
      intro t; simp
    exact h_cont_on.comp_continuous h_line_cont h_map
  have h_prod_cont : Continuous (fun t : ℝ =>
      (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
          ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) :=
    h_arch_cont.mul h_coshMellin_cont
  have h_meas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
          ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) MeasureTheory.volume :=
    h_prod_cont.aestronglyMeasurable
  exact h_majorant_int.mono' h_meas
    (MeasureTheory.ae_of_all _ (fun t => h_ptwise t))

/-- **H1: arch-side cosh expansion at σ = 2.** Substitute `pairTestMellin_cosh_expansion`
into `archIntegrand β 2`, multiply through by the arch kernel, and apply linearity of
integration using per-piece integrability `h1_arch_coshGaussMellin_integrable`. -/
theorem arch_integral_cosh_expansion_at_two (β : ℝ) :
    (∫ t : ℝ, Contour.archIntegrand β 2 t) =
      (1/2 : ℂ) * archSingleCosh (2 * β - Real.pi / 3) +
      (1/2 : ℂ) * archSingleCosh (2 - Real.pi / 3 - 2 * β) -
      archSingleCosh (1 - Real.pi / 3) -
      archSingleCosh (2 * β - 1) +
      archSingleCosh 0 := by
  -- Define the arch kernel and the five (kernel·M(c)) integrands.
  set K_t : ℝ → ℂ := fun t : ℝ =>
    deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
        ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ with hK_def
  set f₁ : ℝ → ℂ := fun t => K_t t * Contour.coshGaussMellin (2*β - Real.pi/3)
    ((2 : ℂ) + (t : ℂ) * I)
  set f₂ : ℝ → ℂ := fun t => K_t t * Contour.coshGaussMellin (2 - Real.pi/3 - 2*β)
    ((2 : ℂ) + (t : ℂ) * I)
  set f₃ : ℝ → ℂ := fun t => K_t t * Contour.coshGaussMellin (1 - Real.pi/3)
    ((2 : ℂ) + (t : ℂ) * I)
  set f₄ : ℝ → ℂ := fun t => K_t t * Contour.coshGaussMellin (2*β - 1)
    ((2 : ℂ) + (t : ℂ) * I)
  set f₅ : ℝ → ℂ := fun t => K_t t * Contour.coshGaussMellin 0
    ((2 : ℂ) + (t : ℂ) * I)
  have hf₁ := h1_arch_coshGaussMellin_integrable (2*β - Real.pi/3)
  have hf₂ := h1_arch_coshGaussMellin_integrable (2 - Real.pi/3 - 2*β)
  have hf₃ := h1_arch_coshGaussMellin_integrable (1 - Real.pi/3)
  have hf₄ := h1_arch_coshGaussMellin_integrable (2*β - 1)
  have hf₅ := h1_arch_coshGaussMellin_integrable 0
  -- Pointwise expansion of the integrand.
  have h_ptwise : ∀ t : ℝ,
      Contour.archIntegrand β 2 t =
        ((1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) + (-f₃ t + -f₄ t) + f₅ t := by
    intro t
    -- Need to bridge ((2:ℝ):ℂ) ↔ (2:ℂ).
    have h_cast : ((2:ℝ) : ℂ) = (2 : ℂ) := by push_cast; rfl
    have h_re : (0 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re := by simp
    have h_expand : Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) =
        (1/2 : ℂ) * Contour.coshGaussMellin (2*β - Real.pi/3) ((2 : ℂ) + (t : ℂ) * I) +
        (1/2 : ℂ) * Contour.coshGaussMellin (2 - Real.pi/3 - 2*β) ((2 : ℂ) + (t : ℂ) * I) -
        Contour.coshGaussMellin (1 - Real.pi/3) ((2 : ℂ) + (t : ℂ) * I) -
        Contour.coshGaussMellin (2*β - 1) ((2 : ℂ) + (t : ℂ) * I) +
        Contour.gaussMellin ((2 : ℂ) + (t : ℂ) * I) := by
      apply Contour.pairTestMellin_cosh_expansion
      · exact Contour.mellinConvergent_coshGauss _ h_re
      · exact Contour.mellinConvergent_coshGauss _ h_re
      · exact Contour.mellinConvergent_coshGauss _ h_re
      · exact Contour.mellinConvergent_coshGauss _ h_re
      · -- The c=0 case for raw exp Mellin convergence.
        have h_cv := Contour.mellinConvergent_coshGauss 0 h_re
        have h_eq : (fun u : ℝ => ((Real.cosh (0 * u) * Real.exp (-2 * u ^ 2) : ℝ) : ℂ)) =
            (fun u : ℝ => ((Real.exp (-2 * u ^ 2) : ℝ) : ℂ)) := by
          funext u; rw [zero_mul, Real.cosh_zero, one_mul]
        rw [h_eq] at h_cv
        exact h_cv
    -- Convert gaussMellin to coshGaussMellin 0 via coshGaussMellin_zero.
    have h_g_eq : Contour.gaussMellin ((2 : ℂ) + (t : ℂ) * I) =
        Contour.coshGaussMellin 0 ((2 : ℂ) + (t : ℂ) * I) :=
      (Contour.coshGaussMellin_zero _).symm
    rw [h_g_eq] at h_expand
    -- archIntegrand = arch_kernel * pairTestMellin β.
    show _ = _
    unfold Contour.archIntegrand
    rw [show ((2:ℝ):ℂ) = (2:ℂ) from h_cast]
    rw [h_expand]
    show (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
            ((2 : ℂ) + (t : ℂ) * I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
            (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ) *
        ((1/2 : ℂ) * Contour.coshGaussMellin (2*β - Real.pi/3) ((2 : ℂ) + (t : ℂ) * I) +
        (1/2 : ℂ) * Contour.coshGaussMellin (2 - Real.pi/3 - 2*β) ((2 : ℂ) + (t : ℂ) * I) -
        Contour.coshGaussMellin (1 - Real.pi/3) ((2 : ℂ) + (t : ℂ) * I) -
        Contour.coshGaussMellin (2*β - 1) ((2 : ℂ) + (t : ℂ) * I) +
        Contour.coshGaussMellin 0 ((2 : ℂ) + (t : ℂ) * I)) =
      ((1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) + (-f₃ t + -f₄ t) + f₅ t
    show _ = _
    simp only [f₁, f₂, f₃, f₄, f₅, K_t]
    ring
  have h_fn_eq : Contour.archIntegrand β 2 = fun t : ℝ =>
      ((1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) + (-f₃ t + -f₄ t) + f₅ t := by
    funext t; exact h_ptwise t
  have hf₁_half : MeasureTheory.Integrable (fun t => (1/2 : ℂ) * f₁ t) :=
    hf₁.const_mul (1/2 : ℂ)
  have hf₂_half : MeasureTheory.Integrable (fun t => (1/2 : ℂ) * f₂ t) :=
    hf₂.const_mul (1/2 : ℂ)
  have hf₃_neg : MeasureTheory.Integrable (fun t => -f₃ t) := hf₃.neg
  have hf₄_neg : MeasureTheory.Integrable (fun t => -f₄ t) := hf₄.neg
  have h12 : MeasureTheory.Integrable (fun t => (1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) :=
    hf₁_half.add hf₂_half
  have h34 : MeasureTheory.Integrable (fun t => -f₃ t + -f₄ t) := hf₃_neg.add hf₄_neg
  have h1234 : MeasureTheory.Integrable (fun t =>
      ((1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) + (-f₃ t + -f₄ t)) := h12.add h34
  rw [h_fn_eq]
  rw [MeasureTheory.integral_add h1234 hf₅]
  rw [MeasureTheory.integral_add h12 h34]
  rw [MeasureTheory.integral_add hf₁_half hf₂_half]
  rw [MeasureTheory.integral_add hf₃_neg hf₄_neg]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg]
  -- Pull constants out of (1/2)·f₁ and (1/2)·f₂ integrals.
  rw [show (∫ a : ℝ, (1/2 : ℂ) * f₁ a) = (1/2 : ℂ) * ∫ a : ℝ, f₁ a from
    MeasureTheory.integral_const_mul _ _]
  rw [show (∫ a : ℝ, (1/2 : ℂ) * f₂ a) = (1/2 : ℂ) * ∫ a : ℝ, f₂ a from
    MeasureTheory.integral_const_mul _ _]
  -- Now identify each ∫ fₖ with archSingleCosh.
  show ((1/2 : ℂ) * (∫ t : ℝ, f₁ t) + (1/2 : ℂ) * ∫ t : ℝ, f₂ t) +
      (-(∫ t : ℝ, f₃ t) + -(∫ t : ℝ, f₄ t)) + ∫ t : ℝ, f₅ t =
    (1/2 : ℂ) * archSingleCosh (2 * β - Real.pi / 3) +
      (1/2 : ℂ) * archSingleCosh (2 - Real.pi / 3 - 2 * β) -
      archSingleCosh (1 - Real.pi / 3) -
      archSingleCosh (2 * β - 1) +
      archSingleCosh 0
  unfold archSingleCosh
  show ((1/2 : ℂ) * (∫ t : ℝ, f₁ t) + (1/2 : ℂ) * ∫ t : ℝ, f₂ t) +
      (-(∫ t : ℝ, f₃ t) + -(∫ t : ℝ, f₄ t)) + ∫ t : ℝ, f₅ t =
    (1/2 : ℂ) * (∫ t : ℝ, f₁ t) +
      (1/2 : ℂ) * (∫ t : ℝ, f₂ t) -
      (∫ t : ℝ, f₃ t) -
      (∫ t : ℝ, f₄ t) +
      (∫ t : ℝ, f₅ t)
  ring

/-
**H2 (mechanical linearity).** The prime integral at σ = 2 decomposes via
the same five-term cosh expansion.  Crucially, the prime side has the
already-proved closed form
`∫ primeIntegrand β 2 t dt = 2π · Σ_n Λ(n) · pair_cosh_gauss_test β n`
(`WeilRightEdgePrimeSum.primeIntegrand_integral_eq_prime_sum:379`).

Expanding `pair_cosh_gauss_test β n` via `pair_cosh_gauss_test_cosh_expansion`
(WeilContour:681) and redistributing the sum by linearity yields:

```
∫ primeIntegrand β 2 t dt
  = ((1/2)·primeSingleCosh(2β − π/3) + (1/2)·primeSingleCosh(2 − π/3 − 2β)
     − primeSingleCosh(1 − π/3) − primeSingleCosh(2β − 1)
     + primeSingleCosh(0) : ℂ).
```

**Scope**: ~60 lines.  Mechanical.
-/

/-- **Helper (H2 summability).** For any `c : ℝ`, the real series
`Σ_n Λ(n) · cosh(c·n) · exp(-2n²)` is summable, via comparison with `Λ(n)/n²`:
`cosh(c·n)·exp(-2n²) ≤ exp(c²/4)·exp(-n²) ≤ exp(c²/4)/n²` for `n ≥ 1`. -/
private lemma h2_summable_cosh_gauss (c : ℝ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2))) := by
  have hΛ_sum : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (2 : ℝ)) :=
    ZD.WeilPositivity.Contour.summable_vonMangoldt_rpow 2 (by norm_num)
  have hΛ_sum' : Summable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) := by
    convert hΛ_sum using 1
    funext n; congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hscale := hΛ_sum'.mul_left (Real.exp (c ^ 2 / 4))
  refine hscale.of_nonneg_of_le ?_ ?_
  · intro n
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.cosh_pos _).le (Real.exp_pos _).le)
  · intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ArithmeticFunction.map_zero]
    · have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h_bd1 : Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2) ≤
          Real.exp (c ^ 2 / 4) * Real.exp (-(n : ℝ) ^ 2) := by
        have hsq1 : c * (n : ℝ) - 2 * (n : ℝ) ^ 2 ≤ c ^ 2 / 4 - (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((n : ℝ) - c / 2)]
        have hsq2 : -(c * (n : ℝ)) - 2 * (n : ℝ) ^ 2 ≤ c ^ 2 / 4 - (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((n : ℝ) + c / 2)]
        have hexp1 := Real.exp_le_exp.mpr hsq1
        have hexp2 := Real.exp_le_exp.mpr hsq2
        rw [Real.cosh_eq]
        have hA : Real.exp (c * (n : ℝ) - 2 * (n : ℝ) ^ 2) =
            Real.exp (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
        have hB : Real.exp (-(c * (n : ℝ)) - 2 * (n : ℝ) ^ 2) =
            Real.exp (-(c * (n : ℝ))) * Real.exp (-2 * (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
        have hC : Real.exp (c ^ 2 / 4) * Real.exp (-(n : ℝ) ^ 2) =
            Real.exp (c ^ 2 / 4 - (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [hC]
        have heq : ((Real.exp (c * (n : ℝ)) + Real.exp (-(c * (n : ℝ)))) / 2) *
              Real.exp (-2 * (n : ℝ) ^ 2) =
            (Real.exp (c * (n : ℝ) - 2 * (n : ℝ) ^ 2) +
              Real.exp (-(c * (n : ℝ)) - 2 * (n : ℝ) ^ 2)) / 2 := by
          rw [hA, hB]; ring
        rw [heq]; linarith
      have h_bd2 : Real.exp (-(n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ^ 2 := by
        have hn2_le : (n : ℝ) ^ 2 ≤ Real.exp ((n : ℝ) ^ 2) := by
          have := Real.add_one_le_exp ((n : ℝ) ^ 2); linarith
        rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) hn2_pos]; exact hn2_le
      have hexp_pos : (0 : ℝ) < Real.exp (c ^ 2 / 4) := Real.exp_pos _
      have h_bd : Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2) ≤
          Real.exp (c ^ 2 / 4) * (1 / (n : ℝ) ^ 2) :=
        le_trans h_bd1 (mul_le_mul_of_nonneg_left h_bd2 hexp_pos.le)
      have hmul := mul_le_mul_of_nonneg_left h_bd
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      calc (ArithmeticFunction.vonMangoldt n : ℝ) *
            (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2))
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
              (Real.exp (c ^ 2 / 4) * (1 / (n : ℝ) ^ 2)) := hmul
        _ = Real.exp (c ^ 2 / 4) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2) := by ring

/-- **Helper (H2 real-level 5-way split).** Distributes the tsum of the pair-test
`2π · Σ Λ(n) · pair_cosh_gauss_test β n` into the five `primeSingleCosh`
expressions via pointwise `pair_cosh_gauss_test_cosh_expansion` and
`Summable.tsum_add`/`Summable.tsum_sub`. -/
private theorem h2_real_prime_sum_eq (β : ℝ) :
    (2 * Real.pi : ℝ) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (pair_cosh_gauss_test β (n : ℝ) : ℝ) =
    (1 / 2) * primeSingleCosh (2 * β - Real.pi / 3) +
    (1 / 2) * primeSingleCosh (2 - Real.pi / 3 - 2 * β) -
    primeSingleCosh (1 - Real.pi / 3) -
    primeSingleCosh (2 * β - 1) +
    primeSingleCosh 0 := by
  set f : ℝ → ℕ → ℝ := fun c n =>
    (ArithmeticFunction.vonMangoldt n : ℝ) *
      (Real.cosh (c * (n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ 2)) with hf_def
  have h_sum_f : ∀ c, Summable (f c) := h2_summable_cosh_gauss
  have h_pS : ∀ c, primeSingleCosh c = 2 * Real.pi * ∑' n, f c n := fun _ => rfl
  have h_ptwise : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (pair_cosh_gauss_test β (n : ℝ)) =
      (1 / 2) * f (2 * β - Real.pi / 3) n +
        (1 / 2) * f (2 - Real.pi / 3 - 2 * β) n -
        f (1 - Real.pi / 3) n - f (2 * β - 1) n + f 0 n := by
    intro n
    rw [pair_cosh_gauss_test_cosh_expansion β (n : ℝ)]
    simp only [hf_def]
    have hc0 : Real.cosh (0 * (n : ℝ)) = 1 := by rw [zero_mul, Real.cosh_zero]
    rw [hc0]; ring
  rw [tsum_congr h_ptwise]
  have hA_half : Summable (fun n => (1 / 2 : ℝ) * f (2 * β - Real.pi / 3) n) :=
    (h_sum_f _).mul_left _
  have hB_half : Summable (fun n => (1 / 2 : ℝ) * f (2 - Real.pi / 3 - 2 * β) n) :=
    (h_sum_f _).mul_left _
  have hC := h_sum_f (1 - Real.pi / 3)
  have hD := h_sum_f (2 * β - 1)
  have hE := h_sum_f 0
  have hAB := hA_half.add hB_half
  have hABC := hAB.sub hC
  have hABCD := hABC.sub hD
  rw [Summable.tsum_add hABCD hE]
  rw [Summable.tsum_sub hABC hD]
  rw [Summable.tsum_sub hAB hC]
  rw [Summable.tsum_add hA_half hB_half]
  rw [tsum_mul_left, tsum_mul_left]
  simp only [h_pS]
  ring

theorem prime_integral_cosh_expansion_at_two (β : ℝ) :
    (∫ t : ℝ, Contour.primeIntegrand β 2 t) =
      (1/2 : ℂ) * ((primeSingleCosh (2 * β - Real.pi / 3) : ℝ) : ℂ) +
      (1/2 : ℂ) * ((primeSingleCosh (2 - Real.pi / 3 - 2 * β) : ℝ) : ℂ) -
      ((primeSingleCosh (1 - Real.pi / 3) : ℝ) : ℂ) -
      ((primeSingleCosh (2 * β - 1) : ℝ) : ℂ) +
      ((primeSingleCosh 0 : ℝ) : ℂ) := by
  rw [Contour.primeIntegrand_integral_eq_prime_sum β 2 (by norm_num : (1 : ℝ) < 2)]
  have h_cast : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) =
      (((ArithmeticFunction.vonMangoldt n : ℝ) *
        pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
    intro n; push_cast; ring
  rw [tsum_congr h_cast]
  rw [← Complex.ofReal_tsum]
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_mul]
  rw [h2_real_prime_sum_eq β]
  push_cast
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § H3 — Classical Weil identity for the pair-combined cosh-Gauss test
-- ═══════════════════════════════════════════════════════════════════════════

/-- **H3 (pair-combined; substantive analytic content).** Five-term weighted
sum identity: the arch-side and prime-side pair-combo match.

**Proof route (classical Weil; ~150–300 lines)**:
1. Von Mangoldt expansion of `ζ'/ζ(2+it)` on `Re s > 1`.
2. FE expansion of `ζ'/ζ(1−(2+it))` via `zeta_logDeriv_arch_form`.
3. Mellin inversion for `coshGaussMellin c (2+it)` at `x > 0`.
4. Fubini swap + per-prime-power evaluation. Γℝ'/Γℝ arch pieces cancel against
   the `-Γℝ'/Γℝ(s) - Γℝ'/Γℝ(1-s)` from (2); `pair_coeffs_sum`,
   `pair_coeffs_diff`, `pair_axes_sum`, `pair_half_strip` give the channel-by-channel
   match in the pair-combo (per-c fails; pair-combo succeeds via π/6 axis design).

Classical harmonic / energy-balance content; not RH content. The per-c
identity `archSingleCosh c = primeSingleCosh c` does NOT hold; the weighted
pair-combo DOES by design. -/
def archPair_eq_primePair_at_two_target (β : ℝ) : Prop :=
    (1/2 : ℂ) * archSingleCosh (2 * β - Real.pi / 3) +
    (1/2 : ℂ) * archSingleCosh (2 - Real.pi / 3 - 2 * β) -
    archSingleCosh (1 - Real.pi / 3) -
    archSingleCosh (2 * β - 1) +
    archSingleCosh 0 =
    (1/2 : ℂ) * ((primeSingleCosh (2 * β - Real.pi / 3) : ℝ) : ℂ) +
    (1/2 : ℂ) * ((primeSingleCosh (2 - Real.pi / 3 - 2 * β) : ℝ) : ℂ) -
    ((primeSingleCosh (1 - Real.pi / 3) : ℝ) : ℂ) -
    ((primeSingleCosh (2 * β - 1) : ℝ) : ℂ) +
    ((primeSingleCosh 0 : ℝ) : ℂ)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Assembly — A1 from H1 + H2 + H3' (pair-combo)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **A1 assembly.** H1 + H3' + H2 ⇒ `∫ arch β 2 = ∫ prime β 2`. -/
theorem archIntegral_eq_primeIntegral_at_two_of_archPair (β : ℝ)
    (h_pair : archPair_eq_primePair_at_two_target β) :
    (∫ t : ℝ, Contour.archIntegrand β 2 t) =
      (∫ t : ℝ, Contour.primeIntegrand β 2 t) := by
  rw [arch_integral_cosh_expansion_at_two β,
      h_pair,
      ← prime_integral_cosh_expansion_at_two β]

/-- **Definitional equivalence.** `reflectedPrimeIntegrand β 2 t` unfolded. -/
theorem reflectedPrime_integrand_eq (β : ℝ) (t : ℝ) :
    deriv riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
    Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
    Contour.reflectedPrimeIntegrand β 2 t := by
  rfl

/-- **Main theorem (B.5.b Step 1): reflected-prime integral vanishes at σ₀ = 2.**
From `archIntegral_eq_primeIntegral_at_two` + `weilArchPrimeIdentityTarget_at_two`. -/
theorem reflectedPrimeIntegrand_at_two_integral_vanishes_of_archPair (β : ℝ)
    (h_pair : archPair_eq_primePair_at_two_target β) :
    ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0 := by
  have h_decomp := ZD.WeilPositivity.Contour.weilArchPrimeIdentityTarget_at_two β
  have h_match := archIntegral_eq_primeIntegral_at_two_of_archPair β h_pair
  have h_cast : ∀ t : ℝ,
      Contour.reflectedPrimeIntegrand β 2 t =
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) := by
    intro t
    show deriv riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I) = _
    norm_cast
  have h_int_eq : (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) =
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) :=
    integral_congr_ae (Filter.Eventually.of_forall h_cast)
  rw [h_int_eq]
  exact sub_eq_self.mp (h_match.symm.trans h_decomp).symm

/-- The pair-combined arch/prime identity is equivalent to vanishing of the
whole-line reflected-prime integral. This is the exact remaining analytic
content behind H3. -/
theorem archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes (β : ℝ) :
    archPair_eq_primePair_at_two_target β ↔
      ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0 := by
  constructor
  · exact reflectedPrimeIntegrand_at_two_integral_vanishes_of_archPair β
  · intro h_ref_zero
    have h_decomp := ZD.WeilPositivity.Contour.weilArchPrimeIdentityTarget_at_two β
    have h_arch_prime :
        (∫ t : ℝ, Contour.archIntegrand β 2 t) =
          (∫ t : ℝ, Contour.primeIntegrand β 2 t) := by
      have h_cast : (∫ t : ℝ,
          deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
           riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
          Contour.pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
          ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t := by
        rfl
      rw [h_cast, h_ref_zero, sub_zero] at h_decomp
      exact h_decomp
    unfold archPair_eq_primePair_at_two_target
    rw [← arch_integral_cosh_expansion_at_two β]
    rw [h_arch_prime]
    rw [prime_integral_cosh_expansion_at_two β]

/-- **Consumer form** — reflected-prime vanishing at σ=2, unfolded. -/
theorem reflected_prime_integral_vanishes_at_two_for_cosh_pair_of_archPair (β : ℝ)
    (h_pair : archPair_eq_primePair_at_two_target β) :
    (∫ t : ℝ,
      deriv riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) = 0 := by
  have h_eq : (fun t : ℝ => deriv riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
      Contour.pairTestMellin β (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
    (fun t : ℝ => Contour.reflectedPrimeIntegrand β 2 t) := by
    funext t
    exact reflectedPrime_integrand_eq β t
  rw [h_eq]
  exact reflectedPrimeIntegrand_at_two_integral_vanishes_of_archPair β h_pair

end ReflectedPrimeVanishing
end Contour
end WeilPositivity
end ZD

end
