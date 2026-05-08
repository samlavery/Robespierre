import Mathlib
import RequestProject.WeilPairTestDecay
import RequestProject.WeilPairIBPQuartic
import RequestProject.OfflineDetectorProofUnconditional

/-!
# Uniform-in-β bounds on `pair_cosh_gauss_test β` and `pairTestMellin β`

Steps toward Task #8 (`pairTestMellin_uniform_quartic_decay_on_Icc_target`).

## What this file proves (no sorries)

* `sinh_sq_uniform_bound_on_Icc`: `sinh²((β-1/2)t) ≤ sinh²(M·|t|)` for
  `β ∈ [β₀, β₁]`, `M = max(|β₀-1/2|, |β₁-1/2|)`.
* `pair_cosh_gauss_test_uniform_bound_on_Icc`: pointwise β-uniform
  domination of the test function.
* `pairTestMellin_uniform_strip_bound_on_Icc`: `‖pairTestMellin β s‖ ≤ C`
  uniformly for `β ∈ [β₀, β₁]` and `Re s ∈ [σL, 1]`.

This file contains the FUNCTIONAL bound (no derivatives, no quartic decay).
Quartic decay needs IBP×4 with a parallel uniform-D⁴ bound — the second
half of Task #8.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Real Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace BetaTower

/-! ## Step 1 — uniform `sinh²` bound -/

/-- Helper: `|β - 1/2| ≤ max |β₀ - 1/2| |β₁ - 1/2|` for `β ∈ [β₀, β₁]`. -/
private theorem abs_beta_shift_le_max_abs
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) :
    |β - 1/2| ≤ max |β₀ - 1/2| |β₁ - 1/2| := by
  rcases le_total (β - 1/2) 0 with h_neg | h_pos
  · -- β ≤ 1/2: |β - 1/2| = -(β - 1/2) = 1/2 - β.
    rw [abs_of_nonpos h_neg]
    have h_β₀_le : β₀ ≤ β := hβ.1
    have h_minus_le : -(β - 1/2) ≤ -(β₀ - 1/2) := by linarith
    calc -(β - 1/2) ≤ -(β₀ - 1/2) := h_minus_le
      _ ≤ |β₀ - 1/2| := neg_le_abs _
      _ ≤ max |β₀ - 1/2| |β₁ - 1/2| := le_max_left _ _
  · -- β ≥ 1/2: |β - 1/2| = β - 1/2.
    rw [abs_of_nonneg h_pos]
    have h_le_β₁ : β ≤ β₁ := hβ.2
    have h_le : β - 1/2 ≤ β₁ - 1/2 := by linarith
    calc β - 1/2 ≤ β₁ - 1/2 := h_le
      _ ≤ |β₁ - 1/2| := le_abs_self _
      _ ≤ max |β₀ - 1/2| |β₁ - 1/2| := le_max_right _ _

/-- For `β ∈ [β₀, β₁]` with `M := max(|β₀-1/2|, |β₁-1/2|)`,
`sinh²((β-1/2)t) ≤ sinh²(M·|t|)`.

Proof: `|sinh((β-1/2)t)| = sinh(|(β-1/2)t|) = sinh(|β-1/2|·|t|) ≤ sinh(M·|t|)`,
then square. -/
theorem sinh_sq_uniform_bound_on_Icc
    {β₀ β₁ : ℝ} {β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    Real.sinh ((β - 1/2) * t) ^ 2 ≤
      Real.sinh ((max |β₀ - 1/2| |β₁ - 1/2|) * |t|) ^ 2 := by
  set M : ℝ := max |β₀ - 1/2| |β₁ - 1/2| with hM_def
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have h_beta_abs : |β - 1/2| ≤ M := abs_beta_shift_le_max_abs hβ
  -- |(β-1/2)·t| ≤ M·|t|
  have h_arg_le : |(β - 1/2) * t| ≤ M * |t| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right h_beta_abs (abs_nonneg _)
  -- |sinh((β-1/2)t)| = sinh(|(β-1/2)t|).
  have h_abs_sinh : ∀ x : ℝ, |Real.sinh x| = Real.sinh |x| := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
    · rw [abs_of_nonpos hx, abs_of_nonpos (Real.sinh_nonpos_iff.mpr hx),
          Real.sinh_neg]
  -- sinh is monotone on ℝ.
  have h_sinh_mono : Real.sinh |((β - 1/2) * t)| ≤ Real.sinh (M * |t|) :=
    Real.sinh_le_sinh.mpr h_arg_le
  -- Combine.
  have h_M_t_nn : 0 ≤ M * |t| := mul_nonneg hM_nn (abs_nonneg _)
  have h_lhs_nn : 0 ≤ Real.sinh |((β - 1/2) * t)| :=
    Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have h_sinh_abs_eq : |Real.sinh ((β - 1/2) * t)| = Real.sinh |((β - 1/2) * t)| :=
    h_abs_sinh _
  calc Real.sinh ((β - 1/2) * t) ^ 2
      = |Real.sinh ((β - 1/2) * t)| ^ 2 := (sq_abs _).symm
    _ = Real.sinh |((β - 1/2) * t)| ^ 2 := by rw [h_sinh_abs_eq]
    _ ≤ Real.sinh (M * |t|) ^ 2 :=
        pow_le_pow_left₀ h_lhs_nn h_sinh_mono 2

#print axioms sinh_sq_uniform_bound_on_Icc

/-! ## Step 2 — uniform `pair_cosh_gauss_test` bound -/

/-- For `β ∈ [β₀, β₁]`, the test function is dominated pointwise by a
β-independent majorant:
`pair_cosh_gauss_test β t ≤ 4 · sinh²(M·|t|) · sinh²((1/2-π/6)·t) · (ψ_gaussian t)²`,
where `M = max(|β₀-1/2|, |β₁-1/2|)`. -/
theorem pair_cosh_gauss_test_uniform_bound_on_Icc
    {β₀ β₁ : ℝ} {β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    pair_cosh_gauss_test β t ≤
      4 * Real.sinh ((max |β₀ - 1/2| |β₁ - 1/2|) * |t|) ^ 2 *
        Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 := by
  rw [pair_cosh_gauss_test_sinh_factor]
  -- LHS = 4 · sinh²((1/2-π/6)t) · sinh²((β-1/2)t) · (ψ_gaussian t)²
  -- RHS = 4 · sinh²(M·|t|) · sinh²((1/2-π/6)t) · (ψ_gaussian t)²
  have h_sinh_sq_bd := sinh_sq_uniform_bound_on_Icc hβ t
  have h_inner_nn : 0 ≤ Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 := sq_nonneg _
  have h_psi_nn : 0 ≤ (ZD.ψ_gaussian t) ^ 2 := sq_nonneg _
  have h_4_nn : (0 : ℝ) ≤ 4 := by norm_num
  -- Goal: 4 · sinh²((1/2-π/6)t) · sinh²((β-1/2)t) · (ψ_gaussian t)²
  --     ≤ 4 · sinh²(M·|t|) · sinh²((1/2-π/6)t) · (ψ_gaussian t)²
  -- Reorder using ring identity.
  have h_lhs_eq : (4 : ℝ) * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
      Real.sinh ((β - 1/2) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 =
      Real.sinh ((β - 1/2) * t) ^ 2 *
        (4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
          (ZD.ψ_gaussian t) ^ 2) := by ring
  have h_rhs_eq : (4 : ℝ) *
      Real.sinh ((max |β₀ - 1/2| |β₁ - 1/2|) * |t|) ^ 2 *
        Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 =
      Real.sinh ((max |β₀ - 1/2| |β₁ - 1/2|) * |t|) ^ 2 *
        (4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
          (ZD.ψ_gaussian t) ^ 2) := by ring
  rw [h_lhs_eq, h_rhs_eq]
  have h_factor_nn :
      0 ≤ 4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 := by
    have := mul_nonneg h_4_nn h_inner_nn
    exact mul_nonneg this h_psi_nn
  exact mul_le_mul_of_nonneg_right h_sinh_sq_bd h_factor_nn

#print axioms pair_cosh_gauss_test_uniform_bound_on_Icc

/-! ## Step 3 — uniform `pair_cosh_gauss_test` bound at `β' := 1/2 + M`

The key observation: for `β ∈ [β₀, β₁]`, the test function is dominated
by `pair_cosh_gauss_test (1/2 + M) t` on `t > 0`, where
`M = max(|β₀-1/2|, |β₁-1/2|)`.  This identification reduces the
β-uniform bound to a fixed-β statement at `β' := 1/2 + M`. -/

/-- For `β ∈ [β₀, β₁]` and `t > 0`:
`pair_cosh_gauss_test β t ≤ pair_cosh_gauss_test (1/2 + M) t`,
where `M = max(|β₀-1/2|, |β₁-1/2|)`.

Proof: at `β' = 1/2 + M`, `(β'-1/2) = M ≥ 0`, so on `t > 0`:
`sinh²((β'-1/2)t) = sinh²(M·t) = sinh²(M·|t|)`, which dominates
`sinh²((β-1/2)t)` by `sinh_sq_uniform_bound_on_Icc`. -/
theorem pair_cosh_gauss_test_le_at_extreme_beta
    {β₀ β₁ : ℝ} {β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁)
    {t : ℝ} (ht : 0 < t) :
    pair_cosh_gauss_test β t ≤
      pair_cosh_gauss_test (1/2 + max |β₀ - 1/2| |β₁ - 1/2|) t := by
  rw [pair_cosh_gauss_test_sinh_factor, pair_cosh_gauss_test_sinh_factor]
  set M : ℝ := max |β₀ - 1/2| |β₁ - 1/2| with hM_def
  -- LHS = 4 · sinh²((1/2-π/6)t) · sinh²((β-1/2)t) · ψ²
  -- RHS = 4 · sinh²((1/2-π/6)t) · sinh²(((1/2+M)-1/2)t) · ψ² = 4 · ... · sinh²(M·t) · ψ²
  have h_eq : ((1/2 + M) - 1/2 : ℝ) = M := by ring
  rw [h_eq]
  -- Now compare sinh²((β-1/2)t) ≤ sinh²(M·t)
  have h_sinh_bd := sinh_sq_uniform_bound_on_Icc hβ t
  -- t > 0, so |t| = t.
  have h_abs_t : |t| = t := abs_of_pos ht
  rw [h_abs_t] at h_sinh_bd
  -- factor structure
  have h_factor_nn :
      0 ≤ 4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 := by
    have h1 : (0 : ℝ) ≤ 4 := by norm_num
    have h2 : 0 ≤ Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (ZD.ψ_gaussian t) ^ 2 := sq_nonneg _
    have := mul_nonneg h1 h2
    exact mul_nonneg this h3
  have h_lhs_eq : (4 : ℝ) * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
      Real.sinh ((β - 1/2) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 =
      Real.sinh ((β - 1/2) * t) ^ 2 *
        (4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2) := by ring
  have h_rhs_eq : (4 : ℝ) * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 *
      Real.sinh (M * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2 =
      Real.sinh (M * t) ^ 2 *
        (4 * Real.sinh ((1/2 - Real.pi/6) * t) ^ 2 * (ZD.ψ_gaussian t) ^ 2) := by ring
  rw [h_lhs_eq, h_rhs_eq]
  exact mul_le_mul_of_nonneg_right h_sinh_bd h_factor_nn

#print axioms pair_cosh_gauss_test_le_at_extreme_beta

/-! ## Step 4 — uniform Mellin strip bound on `[β₀, β₁]`

The bound: for `β ∈ [β₀, β₁]`, `σ ∈ [σL, 1]`, `s` with `Re s = σ`:
`‖pairTestMellin β s‖ ≤ I_L + I_0`, where
`I_L = ∫_(Ioi 0) t^(σL-1) · pair_cosh_gauss_test (1/2+M) t dt` and
`I_0 = ∫_(Ioi 0) pair_cosh_gauss_test (1/2+M) t dt`, both independent
of `β` (uniform) and of `σ` (uniform on the strip). -/

theorem pairTestMellin_uniform_strip_bound_on_Icc
    (β₀ β₁ : ℝ) (hβ₀ : 0 < β₀) (hβ₀₁ : β₀ ≤ β₁) (hβ₁ : β₁ < 1)
    (σL : ℝ) (hσL_pos : 0 < σL) (hσL_le : σL ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ Set.Icc β₀ β₁, ∀ s : ℂ, σL ≤ s.re → s.re ≤ 1 →
        ‖Contour.pairTestMellin β s‖ ≤ C := by
  set M : ℝ := max |β₀ - 1/2| |β₁ - 1/2| with hM_def
  set β' : ℝ := 1/2 + M with hβ'_def
  -- Direct integral bound: real Mellin of pair_cosh_gauss_test β' at strip [σL, 1].
  -- I_L := ∫ t^(σL-1) · pair_cosh_gauss_test β' t dt
  -- I_0 := ∫ pair_cosh_gauss_test β' t dt
  -- Both finite (existing project lemma).
  set I_L : ℝ := ∫ t in Set.Ioi (0:ℝ), t ^ (σL - 1) * pair_cosh_gauss_test β' t
  set I_0 : ℝ := ∫ t in Set.Ioi (0:ℝ), pair_cosh_gauss_test β' t
  have h_int_L : MeasureTheory.IntegrableOn
      (fun t => t ^ (σL - 1) * pair_cosh_gauss_test β' t) (Set.Ioi (0:ℝ)) :=
    Contour.pair_mellin_integrand_integrableOn β' σL hσL_pos
  have h_int_0_orig : MeasureTheory.IntegrableOn
      (fun t => t ^ ((1:ℝ) - 1) * pair_cosh_gauss_test β' t) (Set.Ioi (0:ℝ)) :=
    Contour.pair_mellin_integrand_integrableOn β' 1 (by norm_num)
  have h_int_0 : MeasureTheory.IntegrableOn
      (fun t => pair_cosh_gauss_test β' t) (Set.Ioi (0:ℝ)) := by
    refine (MeasureTheory.integrableOn_congr_fun
      (fun t _ => ?_) measurableSet_Ioi).mp h_int_0_orig
    simp
  have h_I_L_nn : 0 ≤ I_L :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun t ht => mul_nonneg (Real.rpow_nonneg ht.le _)
        (pair_cosh_gauss_test_nonneg _ _))
  have h_I_0_nn : 0 ≤ I_0 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun _ _ => pair_cosh_gauss_test_nonneg _ _)
  refine ⟨I_L + I_0, add_nonneg h_I_L_nn h_I_0_nn, ?_⟩
  intro β hβ s hsL hsR
  -- Step 1: ‖pairTestMellin β s‖ ≤ ∫ t^(s.re-1) · pair_cosh_gauss_test β t dt
  have h_step1 := Contour.pairTestMellin_norm_le_real_integral β s
  -- Step 2: dominate by pair_cosh_gauss_test β' on the integrand
  have h_step2 : (∫ t in Set.Ioi (0:ℝ),
        t ^ (s.re - 1) * pair_cosh_gauss_test β t) ≤
      ∫ t in Set.Ioi (0:ℝ),
        t ^ (s.re - 1) * pair_cosh_gauss_test β' t := by
    have h_le : ∀ t ∈ Set.Ioi (0:ℝ),
        t ^ (s.re - 1) * pair_cosh_gauss_test β t ≤
        t ^ (s.re - 1) * pair_cosh_gauss_test β' t := by
      intro t ht
      have ht_pos : (0:ℝ) < t := ht
      have h_t_nn : (0 : ℝ) ≤ t ^ (s.re - 1) := Real.rpow_nonneg ht_pos.le _
      exact mul_le_mul_of_nonneg_left
        (pair_cosh_gauss_test_le_at_extreme_beta hβ ht_pos) h_t_nn
    have h_int_β : MeasureTheory.IntegrableOn
        (fun t => t ^ (s.re - 1) * pair_cosh_gauss_test β t) (Set.Ioi 0) :=
      Contour.pair_mellin_integrand_integrableOn β s.re
        (lt_of_lt_of_le hσL_pos hsL)
    have h_int_β' : MeasureTheory.IntegrableOn
        (fun t => t ^ (s.re - 1) * pair_cosh_gauss_test β' t) (Set.Ioi 0) :=
      Contour.pair_mellin_integrand_integrableOn β' s.re
        (lt_of_lt_of_le hσL_pos hsL)
    exact MeasureTheory.setIntegral_mono_on h_int_β h_int_β'
      measurableSet_Ioi h_le
  -- Step 3: dominate t^(s.re-1) by t^(σL-1) + 1.
  have h_step3 : (∫ t in Set.Ioi (0:ℝ),
        t ^ (s.re - 1) * pair_cosh_gauss_test β' t) ≤ I_L + I_0 := by
    have h_dom : ∀ t ∈ Set.Ioi (0:ℝ),
        t ^ (s.re - 1) * pair_cosh_gauss_test β' t ≤
        t ^ (σL - 1) * pair_cosh_gauss_test β' t +
          pair_cosh_gauss_test β' t := by
      intro t ht
      have ht_pos : (0:ℝ) < t := ht
      have h_test_nn : 0 ≤ pair_cosh_gauss_test β' t :=
        pair_cosh_gauss_test_nonneg _ _
      have h_rpow_bd : t^(s.re - 1) ≤ t^(σL-1) + 1 := by
        rcases le_or_gt t 1 with hle | hgt
        · have h1 : t^(s.re - 1) ≤ t^(σL-1) :=
            Real.rpow_le_rpow_of_exponent_ge ht_pos hle (by linarith)
          have h2 : (0:ℝ) ≤ 1 := by norm_num
          linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
        · have h1 : t^(s.re - 1) ≤ t^((1:ℝ)-1) :=
            Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
          have h2 : t^((1:ℝ)-1) = 1 := by simp
          have h3 : (0:ℝ) ≤ t^(σL-1) := Real.rpow_nonneg ht_pos.le _
          linarith
      calc t^(s.re - 1) * pair_cosh_gauss_test β' t
          ≤ (t^(σL-1) + 1) * pair_cosh_gauss_test β' t :=
            mul_le_mul_of_nonneg_right h_rpow_bd h_test_nn
        _ = t^(σL - 1) * pair_cosh_gauss_test β' t +
              pair_cosh_gauss_test β' t := by ring
    have h_int_lhs : MeasureTheory.IntegrableOn
        (fun t => t ^ (s.re - 1) * pair_cosh_gauss_test β' t) (Set.Ioi 0) :=
      Contour.pair_mellin_integrand_integrableOn β' s.re
        (lt_of_lt_of_le hσL_pos hsL)
    have h_int_rhs : MeasureTheory.IntegrableOn
        (fun t => t ^ (σL - 1) * pair_cosh_gauss_test β' t +
          pair_cosh_gauss_test β' t) (Set.Ioi 0) :=
      h_int_L.add h_int_0
    have h_int_le := MeasureTheory.setIntegral_mono_on h_int_lhs h_int_rhs
      measurableSet_Ioi h_dom
    have h_split : (∫ t in Set.Ioi (0:ℝ),
        t ^ (σL - 1) * pair_cosh_gauss_test β' t +
          pair_cosh_gauss_test β' t) = I_L + I_0 := by
      rw [MeasureTheory.integral_add h_int_L h_int_0]
    linarith
  -- Combine.
  linarith

#print axioms pairTestMellin_uniform_strip_bound_on_Icc

/-! ## Step 5 — uniform-in-c bound on `coshGaussDeriv4Val`

For `c ∈ [-C, C]` with `C ≥ 0`, the project's explicit 4th-derivative
`coshGaussDeriv4Val c t` is dominated by a `c`-uniform majorant via
triangle inequality on the polynomial coefficients +
`|cosh(c·t)| ≤ cosh(C|t|)` + `|sinh(c·t)| ≤ cosh(C|t|)` for `|c| ≤ C`. -/

/-- Helper: `|cosh(c·t)| ≤ cosh(C·|t|)` for `|c| ≤ C`. -/
private lemma abs_cosh_le_cosh_of_abs_le
    {c C : ℝ} (hc : |c| ≤ C) (t : ℝ) :
    |Real.cosh (c * t)| ≤ Real.cosh (C * |t|) := by
  have hC_nn : 0 ≤ C := le_trans (abs_nonneg _) hc
  -- |cosh(c*t)| = cosh(c*t)
  rw [abs_of_nonneg (Real.cosh_pos _).le]
  -- cosh(c*t) = cosh(|c*t|)
  rw [show Real.cosh (c * t) = Real.cosh |c * t| from (Real.cosh_abs _).symm]
  -- cosh(|c*t|) ≤ cosh(C*|t|) iff ||c*t|| ≤ |C*|t||
  refine Real.cosh_le_cosh.mpr ?_
  rw [abs_abs, abs_of_nonneg (mul_nonneg hC_nn (abs_nonneg _)), abs_mul]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

/-- Helper: `|sinh(c·t)| ≤ cosh(C·|t|)` for `|c| ≤ C` and `0 ≤ C`. -/
private lemma abs_sinh_le_cosh_of_abs_le
    {c C : ℝ} (hc : |c| ≤ C) (t : ℝ) :
    |Real.sinh (c * t)| ≤ Real.cosh (C * |t|) := by
  have h1 : |Real.sinh (c * t)| ≤ Real.cosh (c * t) := by
    rcases le_total 0 (c * t) with hpos | hneg
    · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hpos)]
      linarith [Real.sinh_lt_cosh (c * t)]
    · rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr hneg)]
      have h_neg_sinh : -Real.sinh (c * t) = Real.sinh (-(c * t)) := by
        rw [Real.sinh_neg]
      rw [h_neg_sinh]
      have := Real.sinh_lt_cosh (-(c * t))
      rw [Real.cosh_neg] at this
      linarith
  have h2 := abs_cosh_le_cosh_of_abs_le hc t
  rw [abs_of_nonneg ((Real.cosh_pos _).le)] at h2
  linarith

/-- For `c ∈ [-C, C]` with `0 ≤ C`, the absolute value of `coshGaussDeriv4Val c t`
is bounded by a `c`-uniform majorant. -/
theorem coshGaussDeriv4Val_uniform_bound_in_c
    {c C : ℝ} (hC_nn : 0 ≤ C) (hc : |c| ≤ C) (t : ℝ) :
    |Contour.coshGaussDeriv4Val c t| ≤
      ((256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48) +
       (192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3)) *
      Real.cosh (C * |t|) * Real.exp (-2 * t^2) := by
  unfold Contour.coshGaussDeriv4Val
  set P_cosh : ℝ := 256 * t^4 - 384 * t^2 + 96 * c^2 * t^2 + c^4 - 24 * c^2 + 48
  set P_sinh : ℝ := 192 * c * t - 16 * c^3 * t - 256 * c * t^3
  set Q_cosh : ℝ := 256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48
  set Q_sinh : ℝ := 192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3
  have h_exp_pos : 0 < Real.exp (-2 * t^2) := Real.exp_pos _
  have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := h_exp_pos.le
  have h_cosh_C_t_nn : 0 ≤ Real.cosh (C * |t|) := (Real.cosh_pos _).le
  have h_C_nn : (0 : ℝ) ≤ C := hC_nn
  have h_t_sq : t^2 = |t|^2 := (sq_abs t).symm
  have h_t_4 : t^4 = |t|^4 := by
    have : t^4 = (t^2)^2 := by ring
    rw [this, h_t_sq]; ring
  have h_c_sq_le : c^2 ≤ C^2 := by
    rw [show c^2 = |c|^2 from (sq_abs c).symm]
    exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have h_c_sq_nn : (0 : ℝ) ≤ c^2 := sq_nonneg c
  have h_c_4_le : c^4 ≤ C^4 := by
    have h1 : c^4 = (c^2)^2 := by ring
    have h2 : C^4 = (C^2)^2 := by ring
    rw [h1, h2]; exact pow_le_pow_left₀ h_c_sq_nn h_c_sq_le 2
  -- Polynomial bound on |P_cosh|.
  have h_P_cosh_bd : |P_cosh| ≤ Q_cosh := by
    rw [abs_le]; constructor
    · -- -Q_cosh ≤ P_cosh
      show -(256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48) ≤
        256 * t^4 - 384 * t^2 + 96 * c^2 * t^2 + c^4 - 24 * c^2 + 48
      nlinarith [h_t_sq, h_t_4, h_c_sq_le, h_c_4_le, h_c_sq_nn,
                 sq_nonneg t, sq_nonneg c, sq_nonneg C,
                 mul_nonneg h_c_sq_nn (sq_nonneg t),
                 mul_nonneg (sq_nonneg C) (sq_nonneg t)]
    · -- P_cosh ≤ Q_cosh
      show 256 * t^4 - 384 * t^2 + 96 * c^2 * t^2 + c^4 - 24 * c^2 + 48 ≤
        256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48
      nlinarith [h_t_sq, h_t_4, h_c_sq_le, h_c_4_le, h_c_sq_nn,
                 sq_nonneg t, sq_nonneg c, sq_nonneg C,
                 mul_nonneg h_c_sq_nn (sq_nonneg t),
                 mul_nonneg (sq_nonneg C) (sq_nonneg t)]
  -- Polynomial bound on |P_sinh|.
  have h_abs_t_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_abs_t_3 : |t^3| = |t|^3 := by rw [abs_pow]
  have h_c_abs_le : |c| ≤ C := hc
  have h_P_sinh_bd : |P_sinh| ≤ Q_sinh := by
    show |192 * c * t - 16 * c^3 * t - 256 * c * t^3| ≤
      192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3
    have h_192 : |192 * c * t| ≤ 192 * C * |t| := by
      rw [show (192 * c * t : ℝ) = 192 * (c * t) from by ring, abs_mul,
          show (192 * C * |t| : ℝ) = 192 * (C * |t|) from by ring]
      have h_pos : (0 : ℝ) ≤ 192 := by norm_num
      have h_abs_192 : |(192 : ℝ)| = 192 := abs_of_nonneg h_pos
      rw [h_abs_192]
      apply mul_le_mul_of_nonneg_left _ h_pos
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have h_16 : |16 * c^3 * t| ≤ 16 * C^3 * |t| := by
      rw [show (16 * c^3 * t : ℝ) = 16 * (c^3 * t) from by ring, abs_mul,
          show (16 * C^3 * |t| : ℝ) = 16 * (C^3 * |t|) from by ring]
      have h_pos : (0 : ℝ) ≤ 16 := by norm_num
      have h_abs_16 : |(16 : ℝ)| = 16 := abs_of_nonneg h_pos
      rw [h_abs_16]
      apply mul_le_mul_of_nonneg_left _ h_pos
      rw [abs_mul]
      have h_c3_le : |c^3| ≤ C^3 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg c) hc 3
      exact mul_le_mul h_c3_le (le_refl _) (abs_nonneg _) (by positivity)
    have h_256 : |256 * c * t^3| ≤ 256 * C * |t|^3 := by
      rw [show (256 * c * t^3 : ℝ) = 256 * (c * t^3) from by ring, abs_mul,
          show (256 * C * |t|^3 : ℝ) = 256 * (C * |t|^3) from by ring]
      have h_pos : (0 : ℝ) ≤ 256 := by norm_num
      have h_abs_256 : |(256 : ℝ)| = 256 := abs_of_nonneg h_pos
      rw [h_abs_256]
      apply mul_le_mul_of_nonneg_left _ h_pos
      rw [abs_mul, h_abs_t_3]
      exact mul_le_mul hc (le_refl _) (by positivity) hC_nn
    calc |192 * c * t - 16 * c^3 * t - 256 * c * t^3|
        ≤ |192 * c * t| + |16 * c^3 * t| + |256 * c * t^3| := by
          have h1 : |192 * c * t - 16 * c^3 * t| ≤
              |192 * c * t| + |16 * c^3 * t| := by
            rw [sub_eq_add_neg, ← abs_neg (16 * c^3 * t)]
            exact abs_add_le _ _
          have h2 : |192 * c * t - 16 * c^3 * t - 256 * c * t^3| ≤
              |192 * c * t - 16 * c^3 * t| + |256 * c * t^3| := by
            rw [sub_eq_add_neg, ← abs_neg (256 * c * t^3)]
            exact abs_add_le _ _
          linarith
      _ ≤ 192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3 := by
          linarith
  -- Now bound the full expression.
  have h_cosh_bd : |Real.cosh (c * t)| ≤ Real.cosh (C * |t|) :=
    abs_cosh_le_cosh_of_abs_le hc t
  have h_sinh_bd : |Real.sinh (c * t)| ≤ Real.cosh (C * |t|) :=
    abs_sinh_le_cosh_of_abs_le hc t
  -- Goal: |((P_cosh) · cosh(c·t) + (P_sinh) · sinh(c·t)) · exp(-2t²)|
  --   ≤ (Q_cosh + Q_sinh) · cosh(C·|t|) · exp(-2t²)
  rw [abs_mul, abs_of_nonneg h_exp_nn]
  -- LHS: |P_cosh·cosh(ct) + P_sinh·sinh(ct)| · exp(-2t²)
  -- ≤ (|P_cosh|·|cosh(ct)| + |P_sinh|·|sinh(ct)|) · exp(-2t²)
  -- ≤ (Q_cosh·cosh(C|t|) + Q_sinh·cosh(C|t|)) · exp(-2t²)
  -- = (Q_cosh + Q_sinh) · cosh(C|t|) · exp(-2t²)
  have hQ_cosh_nn : 0 ≤ Q_cosh := by
    show 0 ≤ 256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48
    positivity
  have hQ_sinh_nn : 0 ≤ Q_sinh := by
    show 0 ≤ 192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3
    have : 0 ≤ C^3 := by positivity
    positivity
  have h_main :
      |P_cosh * Real.cosh (c * t) + P_sinh * Real.sinh (c * t)| ≤
      (Q_cosh + Q_sinh) * Real.cosh (C * |t|) := by
    have h_tri : |P_cosh * Real.cosh (c * t) + P_sinh * Real.sinh (c * t)| ≤
        |P_cosh * Real.cosh (c * t)| + |P_sinh * Real.sinh (c * t)| :=
      abs_add_le _ _
    have h_term1 : |P_cosh * Real.cosh (c * t)| ≤ Q_cosh * Real.cosh (C * |t|) := by
      rw [abs_mul]
      exact mul_le_mul h_P_cosh_bd h_cosh_bd (abs_nonneg _) hQ_cosh_nn
    have h_term2 : |P_sinh * Real.sinh (c * t)| ≤ Q_sinh * Real.cosh (C * |t|) := by
      rw [abs_mul]
      exact mul_le_mul h_P_sinh_bd h_sinh_bd (abs_nonneg _) hQ_sinh_nn
    have h_sum : Q_cosh * Real.cosh (C * |t|) + Q_sinh * Real.cosh (C * |t|) =
        (Q_cosh + Q_sinh) * Real.cosh (C * |t|) := by ring
    linarith
  calc |P_cosh * Real.cosh (c * t) + P_sinh * Real.sinh (c * t)| *
        Real.exp (-2 * t^2)
      ≤ ((Q_cosh + Q_sinh) * Real.cosh (C * |t|)) * Real.exp (-2 * t^2) :=
        mul_le_mul_of_nonneg_right h_main h_exp_nn
    _ = (Q_cosh + Q_sinh) * Real.cosh (C * |t|) * Real.exp (-2 * t^2) := by ring

#print axioms coshGaussDeriv4Val_uniform_bound_in_c

/-! ## Step 6 — composite uniform-D⁴ bound for `pair_cosh_gauss_test`

The C-decomposition (`pair_cosh_gauss_test_cosh_expansion`) writes
`pair_cosh_gauss_test β t` as a fixed linear combination of 5
`cosh(c_i(β)·t)·exp(-2t²)` channels.  For each, the c-uniform bound on
`coshGaussDeriv4Val` gives a t-only majorant.  Summing yields a
β-uniform majorant on `D⁴ pair_cosh_gauss_test β t`.

This step requires:
(i) computing `D⁴ pair_cosh_gauss_test β t` as a sum of `coshGaussDeriv4Val`
  values via linearity of `iteratedDeriv` over the C-decomposition,
(ii) applying the c-uniform bound to each.

Step (i) is non-trivial Lean (uses `iteratedDeriv` linearity + the
explicit cosh-Gauss identification at each c-channel).

Step (ii) uses Step 5's lemma at each of the 5 c-channels.

For β ∈ [β₀, β₁], the c-values are:
* c₁ = 2β − π/3 ∈ [2β₀−π/3, 2β₁−π/3]
* c₂ = 2 − π/3 − 2β ∈ [2−π/3−2β₁, 2−π/3−2β₀]
* c₃ = 2β − 1 ∈ [2β₀−1, 2β₁−1]
* c₄ = 1 − π/3 (β-independent)
* c₅ = 0 (β-independent)

For each, the bound `|c_i(β)| ≤ C_i` gives a uniform constant.
The maximum of all `C_i` (call it `C_max`) determines the channel-wise
bound's argument. -/

/-- Uniform-in-β maximum of |c_i(β)| over the 5 cosh-channels of
`pair_cosh_gauss_test_cosh_expansion`. -/
noncomputable def maxChannelAbs_on_Icc (β₀ β₁ : ℝ) : ℝ :=
  max (max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                     (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                (max |2 * β₀ - 1| |2 * β₁ - 1|))
           |1 - Real.pi/3|)
       0

/-- The channel c-bound is non-negative. -/
theorem maxChannelAbs_on_Icc_nonneg (β₀ β₁ : ℝ) :
    0 ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  unfold maxChannelAbs_on_Icc
  exact le_max_right _ _

/-- For β ∈ [β₀, β₁]: `|2β − π/3| ≤ maxChannelAbs_on_Icc β₀ β₁`. -/
theorem channel1_abs_le_max
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) :
    |2 * β - Real.pi/3| ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  unfold maxChannelAbs_on_Icc
  -- 2β - π/3 is monotone in β; bounded by max of endpoint values.
  have h_le : |2 * β - Real.pi/3| ≤
      max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3| := by
    rcases le_total (2 * β - Real.pi/3) 0 with h_neg | h_pos
    · rw [abs_of_nonpos h_neg]
      have : β₀ ≤ β := hβ.1
      have h_mono : -(2 * β - Real.pi/3) ≤ -(2 * β₀ - Real.pi/3) := by linarith
      calc -(2 * β - Real.pi/3) ≤ -(2 * β₀ - Real.pi/3) := h_mono
        _ ≤ |2 * β₀ - Real.pi/3| := neg_le_abs _
        _ ≤ max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3| := le_max_left _ _
    · rw [abs_of_nonneg h_pos]
      have : β ≤ β₁ := hβ.2
      have h_mono : 2 * β - Real.pi/3 ≤ 2 * β₁ - Real.pi/3 := by linarith
      calc 2 * β - Real.pi/3 ≤ 2 * β₁ - Real.pi/3 := h_mono
        _ ≤ |2 * β₁ - Real.pi/3| := le_abs_self _
        _ ≤ max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3| := le_max_right _ _
  -- Then this max is below maxChannelAbs.
  calc |2 * β - Real.pi/3|
      ≤ max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3| := h_le
    _ ≤ max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|) := le_max_left _ _
    _ ≤ max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                 (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
            (max |2 * β₀ - 1| |2 * β₁ - 1|) := le_max_left _ _
    _ ≤ max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                      (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                 (max |2 * β₀ - 1| |2 * β₁ - 1|))
            |1 - Real.pi/3| := le_max_left _ _
    _ ≤ max (max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                       (max |2 * β₀ - 1| |2 * β₁ - 1|))
                 |1 - Real.pi/3|)
            0 := le_max_left _ _

/-- For β ∈ [β₀, β₁]: `|2 - π/3 - 2β| ≤ maxChannelAbs_on_Icc β₀ β₁`. -/
theorem channel2_abs_le_max
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) :
    |2 - Real.pi/3 - 2 * β| ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  unfold maxChannelAbs_on_Icc
  have h_le : |2 - Real.pi/3 - 2 * β| ≤
      max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁| := by
    rcases le_total (2 - Real.pi/3 - 2 * β) 0 with h_neg | h_pos
    · rw [abs_of_nonpos h_neg]
      have : β ≤ β₁ := hβ.2
      have h_mono : -(2 - Real.pi/3 - 2 * β) ≤ -(2 - Real.pi/3 - 2 * β₁) := by linarith
      calc -(2 - Real.pi/3 - 2 * β) ≤ -(2 - Real.pi/3 - 2 * β₁) := h_mono
        _ ≤ |2 - Real.pi/3 - 2 * β₁| := neg_le_abs _
        _ ≤ max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁| := le_max_right _ _
    · rw [abs_of_nonneg h_pos]
      have : β₀ ≤ β := hβ.1
      have h_mono : 2 - Real.pi/3 - 2 * β ≤ 2 - Real.pi/3 - 2 * β₀ := by linarith
      calc 2 - Real.pi/3 - 2 * β ≤ 2 - Real.pi/3 - 2 * β₀ := h_mono
        _ ≤ |2 - Real.pi/3 - 2 * β₀| := le_abs_self _
        _ ≤ max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁| := le_max_left _ _
  calc |2 - Real.pi/3 - 2 * β|
      ≤ max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁| := h_le
    _ ≤ max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|) := le_max_right _ _
    _ ≤ max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                 (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
            (max |2 * β₀ - 1| |2 * β₁ - 1|) := le_max_left _ _
    _ ≤ max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                      (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                 (max |2 * β₀ - 1| |2 * β₁ - 1|))
            |1 - Real.pi/3| := le_max_left _ _
    _ ≤ max (max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                       (max |2 * β₀ - 1| |2 * β₁ - 1|))
                 |1 - Real.pi/3|)
            0 := le_max_left _ _

/-- For β ∈ [β₀, β₁]: `|2β − 1| ≤ maxChannelAbs_on_Icc β₀ β₁`. -/
theorem channel3_abs_le_max
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) :
    |2 * β - 1| ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  unfold maxChannelAbs_on_Icc
  have h_le : |2 * β - 1| ≤ max |2 * β₀ - 1| |2 * β₁ - 1| := by
    rcases le_total (2 * β - 1) 0 with h_neg | h_pos
    · rw [abs_of_nonpos h_neg]
      have : β₀ ≤ β := hβ.1
      have h_mono : -(2 * β - 1) ≤ -(2 * β₀ - 1) := by linarith
      calc -(2 * β - 1) ≤ -(2 * β₀ - 1) := h_mono
        _ ≤ |2 * β₀ - 1| := neg_le_abs _
        _ ≤ max |2 * β₀ - 1| |2 * β₁ - 1| := le_max_left _ _
    · rw [abs_of_nonneg h_pos]
      have : β ≤ β₁ := hβ.2
      have h_mono : 2 * β - 1 ≤ 2 * β₁ - 1 := by linarith
      calc 2 * β - 1 ≤ 2 * β₁ - 1 := h_mono
        _ ≤ |2 * β₁ - 1| := le_abs_self _
        _ ≤ max |2 * β₀ - 1| |2 * β₁ - 1| := le_max_right _ _
  calc |2 * β - 1|
      ≤ max |2 * β₀ - 1| |2 * β₁ - 1| := h_le
    _ ≤ max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                 (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
            (max |2 * β₀ - 1| |2 * β₁ - 1|) := le_max_right _ _
    _ ≤ max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                      (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                 (max |2 * β₀ - 1| |2 * β₁ - 1|))
            |1 - Real.pi/3| := le_max_left _ _
    _ ≤ max (max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                       (max |2 * β₀ - 1| |2 * β₁ - 1|))
                 |1 - Real.pi/3|)
            0 := le_max_left _ _

/-- `|1 − π/3| ≤ maxChannelAbs_on_Icc β₀ β₁` (β-independent channel). -/
theorem channel4_abs_le_max
    (β₀ β₁ : ℝ) :
    |1 - Real.pi/3| ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  unfold maxChannelAbs_on_Icc
  calc |1 - Real.pi/3|
      ≤ max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                      (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                 (max |2 * β₀ - 1| |2 * β₁ - 1|))
            |1 - Real.pi/3| := le_max_right _ _
    _ ≤ max (max (max (max (max |2 * β₀ - Real.pi/3| |2 * β₁ - Real.pi/3|)
                            (max |2 - Real.pi/3 - 2 * β₀| |2 - Real.pi/3 - 2 * β₁|))
                       (max |2 * β₀ - 1| |2 * β₁ - 1|))
                 |1 - Real.pi/3|)
            0 := le_max_left _ _

/-- `|0| ≤ maxChannelAbs_on_Icc β₀ β₁` (zero channel from constant 1). -/
theorem channel5_abs_le_max (β₀ β₁ : ℝ) :
    |(0 : ℝ)| ≤ maxChannelAbs_on_Icc β₀ β₁ := by
  rw [abs_zero]
  exact maxChannelAbs_on_Icc_nonneg β₀ β₁

#print axioms maxChannelAbs_on_Icc_nonneg
#print axioms channel1_abs_le_max
#print axioms channel2_abs_le_max
#print axioms channel3_abs_le_max
#print axioms channel4_abs_le_max
#print axioms channel5_abs_le_max

/-! ## Step A — channel-wise uniform-in-β D⁴ bounds

Apply `coshGaussDeriv4Val_uniform_bound_in_c` with `C := maxChannelAbs_on_Icc β₀ β₁`
to each of the 5 channels.  Result: for each `β ∈ [β₀, β₁]` and `t ∈ ℝ`,
`|coshGaussDeriv4Val(c_i(β), t)|` is bounded by a single β-independent majorant. -/

/-- Convenience: the channel D⁴ majorant. -/
noncomputable def channelD4Majorant (β₀ β₁ : ℝ) (t : ℝ) : ℝ :=
  ((256 * |t|^4 + 384 * |t|^2 + 96 * (maxChannelAbs_on_Icc β₀ β₁)^2 * |t|^2 +
    (maxChannelAbs_on_Icc β₀ β₁)^4 + 24 * (maxChannelAbs_on_Icc β₀ β₁)^2 + 48) +
   (192 * (maxChannelAbs_on_Icc β₀ β₁) * |t| +
    16 * (maxChannelAbs_on_Icc β₀ β₁)^3 * |t| +
    256 * (maxChannelAbs_on_Icc β₀ β₁) * |t|^3)) *
  Real.cosh (maxChannelAbs_on_Icc β₀ β₁ * |t|) * Real.exp (-2 * t^2)

/-- The channel D⁴ majorant is non-negative. -/
theorem channelD4Majorant_nonneg (β₀ β₁ : ℝ) (t : ℝ) :
    0 ≤ channelD4Majorant β₀ β₁ t := by
  unfold channelD4Majorant
  set C := maxChannelAbs_on_Icc β₀ β₁
  have hC_nn : 0 ≤ C := maxChannelAbs_on_Icc_nonneg β₀ β₁
  have h_cosh_nn : 0 ≤ Real.cosh (C * |t|) := (Real.cosh_pos _).le
  have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  have h_C3_nn : 0 ≤ C^3 := by positivity
  have h_poly_nn :
      0 ≤ (256 * |t|^4 + 384 * |t|^2 + 96 * C^2 * |t|^2 + C^4 + 24 * C^2 + 48) +
          (192 * C * |t| + 16 * C^3 * |t| + 256 * C * |t|^3) := by positivity
  exact mul_nonneg (mul_nonneg h_poly_nn h_cosh_nn) h_exp_nn

/-- Channel 1 (c = 2β − π/3) — uniform D⁴ bound. -/
theorem coshGaussDeriv4Val_channel1_uniform_bound
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    |Contour.coshGaussDeriv4Val (2 * β - Real.pi/3) t| ≤
      channelD4Majorant β₀ β₁ t :=
  coshGaussDeriv4Val_uniform_bound_in_c
    (maxChannelAbs_on_Icc_nonneg β₀ β₁) (channel1_abs_le_max hβ) t

/-- Channel 2 (c = 2 − π/3 − 2β) — uniform D⁴ bound. -/
theorem coshGaussDeriv4Val_channel2_uniform_bound
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    |Contour.coshGaussDeriv4Val (2 - Real.pi/3 - 2 * β) t| ≤
      channelD4Majorant β₀ β₁ t :=
  coshGaussDeriv4Val_uniform_bound_in_c
    (maxChannelAbs_on_Icc_nonneg β₀ β₁) (channel2_abs_le_max hβ) t

/-- Channel 3 (c = 2β − 1) — uniform D⁴ bound. -/
theorem coshGaussDeriv4Val_channel3_uniform_bound
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    |Contour.coshGaussDeriv4Val (2 * β - 1) t| ≤
      channelD4Majorant β₀ β₁ t :=
  coshGaussDeriv4Val_uniform_bound_in_c
    (maxChannelAbs_on_Icc_nonneg β₀ β₁) (channel3_abs_le_max hβ) t

/-- Channel 4 (c = 1 − π/3, β-independent) — uniform D⁴ bound. -/
theorem coshGaussDeriv4Val_channel4_uniform_bound
    (β₀ β₁ : ℝ) (t : ℝ) :
    |Contour.coshGaussDeriv4Val (1 - Real.pi/3) t| ≤
      channelD4Majorant β₀ β₁ t :=
  coshGaussDeriv4Val_uniform_bound_in_c
    (maxChannelAbs_on_Icc_nonneg β₀ β₁) (channel4_abs_le_max β₀ β₁) t

/-- Channel 5 (c = 0, β-independent) — uniform D⁴ bound. -/
theorem coshGaussDeriv4Val_channel5_uniform_bound
    (β₀ β₁ : ℝ) (t : ℝ) :
    |Contour.coshGaussDeriv4Val 0 t| ≤
      channelD4Majorant β₀ β₁ t :=
  coshGaussDeriv4Val_uniform_bound_in_c
    (maxChannelAbs_on_Icc_nonneg β₀ β₁) (channel5_abs_le_max β₀ β₁) t

#print axioms channelD4Majorant_nonneg
#print axioms coshGaussDeriv4Val_channel1_uniform_bound
#print axioms coshGaussDeriv4Val_channel2_uniform_bound
#print axioms coshGaussDeriv4Val_channel3_uniform_bound
#print axioms coshGaussDeriv4Val_channel4_uniform_bound
#print axioms coshGaussDeriv4Val_channel5_uniform_bound

/-! ## Step C — uniform D⁴ bound for `pair_cosh_gauss_test`

The project's `pair_cosh_gauss_test_deriv4_eq` gives the explicit
identification of `D⁴ pair_cosh_gauss_test β` with a linear
combination of 5 `coshGaussDeriv4Val` channels.  Combined with Step
A's channel bounds, we get a β-uniform bound on `|D⁴ pair_cosh_gauss_test β t|`. -/

/-- **β-uniform bound on D⁴ of `pair_cosh_gauss_test`** for β in a
compact interval.  The bound depends only on `[β₀, β₁]` and `t`. -/
theorem pair_cosh_gauss_test_deriv4_uniform_bound_on_Icc
    {β₀ β₁ β : ℝ} (hβ : β ∈ Set.Icc β₀ β₁) (t : ℝ) :
    |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| ≤
      4 * channelD4Majorant β₀ β₁ t := by
  rw [Contour.pair_cosh_gauss_test_deriv4_eq]
  -- Goal: |(1/2)·G(c₁) + (1/2)·G(c₂) − G(c₄) − G(c₃) + G(0)| ≤ 4·M
  -- where G(c) := coshGaussDeriv4Val c t and M := channelD4Majorant β₀ β₁ t.
  have h1 := coshGaussDeriv4Val_channel1_uniform_bound hβ t
  have h2 := coshGaussDeriv4Val_channel2_uniform_bound hβ t
  have h3 := coshGaussDeriv4Val_channel3_uniform_bound hβ t
  have h4 := coshGaussDeriv4Val_channel4_uniform_bound β₀ β₁ t
  have h5 := coshGaussDeriv4Val_channel5_uniform_bound β₀ β₁ t
  set G1 := Contour.coshGaussDeriv4Val (2 * β - Real.pi/3) t
  set G2 := Contour.coshGaussDeriv4Val (2 - Real.pi/3 - 2 * β) t
  set G3 := Contour.coshGaussDeriv4Val (2 * β - 1) t
  set G4 := Contour.coshGaussDeriv4Val (1 - Real.pi/3) t
  set G5 := Contour.coshGaussDeriv4Val 0 t
  set M := channelD4Majorant β₀ β₁ t with hM_def
  -- Triangle inequality: |sum| ≤ sum of |·|.
  have h_tri : |((1/2 : ℝ) * G1 + (1/2) * G2 - G4 - G3 + G5)| ≤
      |(1/2 : ℝ) * G1| + |(1/2 : ℝ) * G2| + |G4| + |G3| + |G5| := by
    have ha : |((1/2 : ℝ) * G1 + (1/2) * G2)| ≤ |(1/2 : ℝ) * G1| + |(1/2 : ℝ) * G2| :=
      abs_add_le _ _
    have hb : |((1/2 : ℝ) * G1 + (1/2) * G2) - G4| ≤
        |((1/2 : ℝ) * G1 + (1/2) * G2)| + |G4| := by
      rw [sub_eq_add_neg, ← abs_neg G4]
      exact abs_add_le _ _
    have hc : |((1/2 : ℝ) * G1 + (1/2) * G2 - G4) - G3| ≤
        |((1/2 : ℝ) * G1 + (1/2) * G2 - G4)| + |G3| := by
      rw [sub_eq_add_neg, ← abs_neg G3]
      exact abs_add_le _ _
    have hd : |((1/2 : ℝ) * G1 + (1/2) * G2 - G4 - G3) + G5| ≤
        |((1/2 : ℝ) * G1 + (1/2) * G2 - G4 - G3)| + |G5| :=
      abs_add_le _ _
    linarith
  -- Each |G_i| ≤ M, plus |(1/2)·G| = (1/2)·|G|.
  have habs1 : |(1/2 : ℝ) * G1| = (1/2 : ℝ) * |G1| := by
    rw [abs_mul]; norm_num
  have habs2 : |(1/2 : ℝ) * G2| = (1/2 : ℝ) * |G2| := by
    rw [abs_mul]; norm_num
  rw [habs1, habs2] at h_tri
  have hM_nn : 0 ≤ M := channelD4Majorant_nonneg β₀ β₁ t
  -- (1/2)·M + (1/2)·M + M + M + M = 4·M.
  have h_sum : (1/2 : ℝ) * M + (1/2 : ℝ) * M + M + M + M = 4 * M := by ring
  -- Combine: |...| ≤ (1/2)|G1| + (1/2)|G2| + |G4| + |G3| + |G5| ≤ (1/2)M·5 + ...
  have h_bd1 : (1/2 : ℝ) * |G1| ≤ (1/2 : ℝ) * M :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h_bd2 : (1/2 : ℝ) * |G2| ≤ (1/2 : ℝ) * M :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  linarith

#print axioms pair_cosh_gauss_test_deriv4_uniform_bound_on_Icc

/-! ## Step D — Mellin integrability of the channel majorant

The majorant `channelD4Majorant β₀ β₁ t = poly(C, |t|)·cosh(C·|t|)·exp(-2t²)`
is Mellin-integrable against `t^(σ-1)` on `(0, ∞)` for any `σ > 0`.

Key bound: `cosh(C·t)·exp(-2t²) ≤ exp(C²/4)·exp(-t²)` for all `t ∈ ℝ`,
proved by completing the square in `Ct - 2t²`. Then the integrand
becomes a polynomial-in-t times `exp(-t²)` times `t^(σ-1)`, integrable
by mathlib's `integrableOn_rpow_mul_exp_neg_mul_sq`. -/

/-- Key bound: `cosh(C·t)·exp(-2t²) ≤ exp(C²/4)·exp(-t²)` for all `t ∈ ℝ`. -/
theorem cosh_mul_exp_neg_two_sq_le
    (C t : ℝ) :
    Real.cosh (C * t) * Real.exp (-2 * t^2) ≤
      Real.exp (C^2 / 4) * Real.exp (-t^2) := by
  -- cosh(Ct)·exp(-2t²) = (exp(Ct - 2t²) + exp(-Ct - 2t²))/2
  -- Each ≤ exp(C²/4 - t²) by completing the square + (t ∓ C/2)² ≥ 0.
  have h1 : Real.exp (C * t - 2 * t^2) ≤ Real.exp (C^2 / 4 - t^2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (t - C/2)]
  have h2 : Real.exp (-(C * t) - 2 * t^2) ≤ Real.exp (C^2 / 4 - t^2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (t + C/2)]
  have h_cosh_eq : Real.cosh (C * t) * Real.exp (-2 * t^2) =
      (Real.exp (C * t - 2 * t^2) + Real.exp (-(C * t) - 2 * t^2)) / 2 := by
    rw [Real.cosh_eq]
    have h_e1 : Real.exp (C * t - 2 * t^2) = Real.exp (C * t) * Real.exp (-2 * t^2) := by
      rw [show (C * t - 2 * t^2 : ℝ) = C * t + (-2 * t^2) from by ring, Real.exp_add]
    have h_e2 : Real.exp (-(C * t) - 2 * t^2) =
        Real.exp (-(C * t)) * Real.exp (-2 * t^2) := by
      rw [show (-(C * t) - 2 * t^2 : ℝ) = -(C * t) + (-2 * t^2) from by ring, Real.exp_add]
    rw [h_e1, h_e2]; ring
  rw [h_cosh_eq]
  have h_factor : Real.exp (C^2 / 4) * Real.exp (-t^2) =
      Real.exp (C^2 / 4 - t^2) := by
    rw [← Real.exp_add]; ring_nf
  rw [h_factor]
  linarith

#print axioms cosh_mul_exp_neg_two_sq_le

/-! ## Step E — Mellin integrability of `channelD4Majorant`

For `σ > 0`, `t^(σ-1) · channelD4Majorant β₀ β₁ t` is integrable on
`Ioi 0`.  Strategy:
1. Bound `cosh(C·|t|) · exp(-2t²) ≤ exp(C²/4) · exp(-t²)` using
   `cosh_mul_exp_neg_two_sq_le`.
2. Distribute the polynomial: each monomial gives a term
   `c · t^(σ+k-1) · exp(-t²)` (k = 0..4), integrable by mathlib's
   `integrableOn_rpow_mul_exp_neg_mul_sq`. -/

/-- Helper: `t^(σ+k-1) · exp(-t²)` is integrable on `Ioi 0` for `σ > 0`
and `k ∈ ℕ`. -/
private theorem rpow_mul_exp_neg_sq_integrableOn_Ioi
    {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(σ + (k : ℝ) - 1) * Real.exp (-t^2)) (Set.Ioi (0:ℝ)) := by
  -- Apply integrableOn_rpow_mul_exp_neg_mul_sq with b = 1, s = σ + k - 1.
  have h : MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(σ + (k : ℝ) - 1) * Real.exp (-1 * t^2)) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      (by have : (0:ℝ) ≤ k := Nat.cast_nonneg _; linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  congr 1
  ring

#print axioms rpow_mul_exp_neg_sq_integrableOn_Ioi

/-- **Polynomial-times-Gaussian majorant for `channelD4Majorant`** on `Ioi 0`.

For any `t > 0`,
`channelD4Majorant β₀ β₁ t ≤ exp(C²/4) · poly_1(C, t) · exp(-t²)`,
where `poly_1(C, t) = (48+24C²+C⁴) + (192C+16C³)·t + (384+96C²)·t² + 256C·t³ + 256·t⁴`. -/
theorem channelD4Majorant_le_polynomial_gaussian
    (β₀ β₁ : ℝ) {t : ℝ} (ht : 0 < t) :
    channelD4Majorant β₀ β₁ t ≤
      Real.exp ((maxChannelAbs_on_Icc β₀ β₁)^2 / 4) *
      ((48 + 24 * (maxChannelAbs_on_Icc β₀ β₁)^2 +
        (maxChannelAbs_on_Icc β₀ β₁)^4) +
       (192 * (maxChannelAbs_on_Icc β₀ β₁) +
        16 * (maxChannelAbs_on_Icc β₀ β₁)^3) * t +
       (384 + 96 * (maxChannelAbs_on_Icc β₀ β₁)^2) * t^2 +
       256 * (maxChannelAbs_on_Icc β₀ β₁) * t^3 +
       256 * t^4) *
      Real.exp (-t^2) := by
  unfold channelD4Majorant
  set C : ℝ := maxChannelAbs_on_Icc β₀ β₁
  have hC_nn : 0 ≤ C := maxChannelAbs_on_Icc_nonneg β₀ β₁
  have ht_abs : |t| = t := abs_of_pos ht
  rw [ht_abs]
  have h_cosh_bd := cosh_mul_exp_neg_two_sq_le C t
  set poly : ℝ :=
    (256 * t^4 + 384 * t^2 + 96 * C^2 * t^2 + C^4 + 24 * C^2 + 48) +
    (192 * C * t + 16 * C^3 * t + 256 * C * t^3) with hpoly_def
  set poly2 : ℝ :=
    (48 + 24 * C^2 + C^4) +
    (192 * C + 16 * C^3) * t +
    (384 + 96 * C^2) * t^2 +
    256 * C * t^3 +
    256 * t^4
    with hpoly2_def
  have hpoly_nn : 0 ≤ poly := by
    show 0 ≤ (256 * t^4 + 384 * t^2 + 96 * C^2 * t^2 + C^4 + 24 * C^2 + 48) +
             (192 * C * t + 16 * C^3 * t + 256 * C * t^3)
    have hC3_nn : 0 ≤ C^3 := by positivity
    have ht_nn : 0 ≤ t := ht.le
    positivity
  have hpoly_eq : poly = poly2 := by
    show _ = _; ring
  show poly * Real.cosh (C * t) * Real.exp (-2 * t^2) ≤
      Real.exp (C^2 / 4) * poly2 * Real.exp (-t^2)
  have hpoly2_nn : 0 ≤ poly2 := hpoly_eq ▸ hpoly_nn
  calc poly * Real.cosh (C * t) * Real.exp (-2 * t^2)
      = poly * (Real.cosh (C * t) * Real.exp (-2 * t^2)) := by ring
    _ = poly2 * (Real.cosh (C * t) * Real.exp (-2 * t^2)) := by rw [hpoly_eq]
    _ ≤ poly2 * (Real.exp (C^2 / 4) * Real.exp (-t^2)) :=
        mul_le_mul_of_nonneg_left h_cosh_bd hpoly2_nn
    _ = Real.exp (C^2 / 4) * poly2 * Real.exp (-t^2) := by ring

#print axioms channelD4Majorant_le_polynomial_gaussian

/-! ## Step E3 — sum-of-monomials majorant integrability

The polynomial-times-Gaussian majorant from
`channelD4Majorant_le_polynomial_gaussian` distributes into 5 monomial
terms `c_k · t^k · exp(-t²)`, each integrable against `t^(σ-1)` on
`Ioi 0` for `σ > 0`.  We package the sum as a single integrability
result. -/

/-- **Sum-of-monomials majorant integrability.** -/
theorem polynomial_gaussian_mellin_integrableOn
    (β₀ β₁ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        Real.exp ((maxChannelAbs_on_Icc β₀ β₁)^2 / 4) *
        ((48 + 24 * (maxChannelAbs_on_Icc β₀ β₁)^2 +
          (maxChannelAbs_on_Icc β₀ β₁)^4) *
            (t^(σ + (0:ℕ) - 1) * Real.exp (-t^2)) +
         (192 * (maxChannelAbs_on_Icc β₀ β₁) +
          16 * (maxChannelAbs_on_Icc β₀ β₁)^3) *
            (t^(σ + (1:ℕ) - 1) * Real.exp (-t^2)) +
         (384 + 96 * (maxChannelAbs_on_Icc β₀ β₁)^2) *
            (t^(σ + (2:ℕ) - 1) * Real.exp (-t^2)) +
         (256 * (maxChannelAbs_on_Icc β₀ β₁)) *
            (t^(σ + (3:ℕ) - 1) * Real.exp (-t^2)) +
         256 *
            (t^(σ + (4:ℕ) - 1) * Real.exp (-t^2))))
      (Set.Ioi (0:ℝ)) := by
  have h_int_0 := rpow_mul_exp_neg_sq_integrableOn_Ioi hσ 0
  have h_int_1 := rpow_mul_exp_neg_sq_integrableOn_Ioi hσ 1
  have h_int_2 := rpow_mul_exp_neg_sq_integrableOn_Ioi hσ 2
  have h_int_3 := rpow_mul_exp_neg_sq_integrableOn_Ioi hσ 3
  have h_int_4 := rpow_mul_exp_neg_sq_integrableOn_Ioi hσ 4
  have h_sum := ((((h_int_0.const_mul
      (48 + 24 * (maxChannelAbs_on_Icc β₀ β₁)^2 +
       (maxChannelAbs_on_Icc β₀ β₁)^4)).add
      (h_int_1.const_mul
      (192 * (maxChannelAbs_on_Icc β₀ β₁) +
       16 * (maxChannelAbs_on_Icc β₀ β₁)^3))).add
      (h_int_2.const_mul
      (384 + 96 * (maxChannelAbs_on_Icc β₀ β₁)^2))).add
      (h_int_3.const_mul (256 * (maxChannelAbs_on_Icc β₀ β₁)))).add
      (h_int_4.const_mul 256)
  exact h_sum.const_mul (Real.exp ((maxChannelAbs_on_Icc β₀ β₁)^2 / 4))

#print axioms polynomial_gaussian_mellin_integrableOn

/-! ## Step E4 — measurability of the Mellin integrand on `Ioi 0`

Continuity of `t^(σ-1) · channelD4Majorant β₀ β₁ t` on `Ioi 0` gives
AEStronglyMeasurable.  This is a building block; combining with the
pointwise polynomial-Gaussian bound and the integrable majorant gives
full integrability (left as Step E5). -/

/-- **AE strongly measurable** on `volume.restrict (Ioi 0)`. -/
theorem channelD4Majorant_mul_rpow_aestronglyMeasurable
    (β₀ β₁ : ℝ) {σ : ℝ} :
    MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => t^(σ-1) * channelD4Majorant β₀ β₁ t)
      ((MeasureTheory.volume).restrict (Set.Ioi (0:ℝ))) := by
  set C : ℝ := maxChannelAbs_on_Icc β₀ β₁
  -- Step 2: AE strongly measurable (via continuity on Ioi 0).
  have h_meas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => t^(σ-1) * channelD4Majorant β₀ β₁ t)
      ((MeasureTheory.volume).restrict (Set.Ioi (0:ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul
    · -- t^(σ-1) is continuous on Ioi 0
      refine continuous_id.continuousOn.rpow_const ?_
      intro x hx; left; exact ne_of_gt hx
    · -- channelD4Majorant β₀ β₁ is continuous on ℝ (so on Ioi 0)
      apply Continuous.continuousOn
      unfold channelD4Majorant
      apply Continuous.mul
      apply Continuous.mul
      · -- polynomial in |t|
        continuity
      · -- cosh(C·|t|)
        exact Real.continuous_cosh.comp (continuous_abs.const_mul C)
      · -- exp(-2t²)
        exact Real.continuous_exp.comp ((continuous_pow 2).const_mul (-2))
  exact h_meas

#print axioms channelD4Majorant_mul_rpow_aestronglyMeasurable

/-! ## Step E5 — final integrability theorem -/

/-- Helper: rpow distribution identity for `t > 0`. -/
private lemma rpow_mul_npow_eq
    {t : ℝ} (ht : 0 < t) (σ : ℝ) (k : ℕ) :
    t^(σ-1) * (t^k : ℝ) = t^(σ + (k:ℕ) - 1) := by
  rw [show (t^k : ℝ) = (t : ℝ)^((k:ℕ) : ℝ) from (Real.rpow_natCast t k).symm,
      ← Real.rpow_add ht]
  congr 1
  push_cast
  ring

/-- **Mellin integrability of `t^(σ-1) · channelD4Majorant β₀ β₁ t`** on `Ioi 0`. -/
theorem channelD4Majorant_mul_rpow_integrableOn
    (β₀ β₁ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(σ-1) * channelD4Majorant β₀ β₁ t) (Set.Ioi (0:ℝ)) := by
  set C : ℝ := maxChannelAbs_on_Icc β₀ β₁
  have h_int_majFn := polynomial_gaussian_mellin_integrableOn β₀ β₁ hσ
  have h_meas := channelD4Majorant_mul_rpow_aestronglyMeasurable β₀ β₁ (σ := σ)
  -- Pointwise bound on Ioi 0.
  have h_bound : ∀ᵐ (t : ℝ) ∂((MeasureTheory.volume).restrict (Set.Ioi (0:ℝ))),
      ‖t^(σ-1) * channelD4Majorant β₀ β₁ t‖ ≤
      Real.exp (C^2 / 4) *
      ((48 + 24 * C^2 + C^4) * (t^(σ + (0:ℕ) - 1) * Real.exp (-t^2)) +
       (192 * C + 16 * C^3) * (t^(σ + (1:ℕ) - 1) * Real.exp (-t^2)) +
       (384 + 96 * C^2) * (t^(σ + (2:ℕ) - 1) * Real.exp (-t^2)) +
       (256 * C) * (t^(σ + (3:ℕ) - 1) * Real.exp (-t^2)) +
       256 * (t^(σ + (4:ℕ) - 1) * Real.exp (-t^2))) := by
    refine MeasureTheory.ae_restrict_iff' measurableSet_Ioi |>.mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro t ht
    have ht_pos : 0 < t := ht
    have ht_nn : 0 ≤ t := ht_pos.le
    have hC_nn : 0 ≤ C := maxChannelAbs_on_Icc_nonneg β₀ β₁
    have h_M_nn : 0 ≤ channelD4Majorant β₀ β₁ t := channelD4Majorant_nonneg β₀ β₁ t
    have h_rpow_nn : 0 ≤ t^(σ-1) := Real.rpow_nonneg ht_nn _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_rpow_nn h_M_nn)]
    have h_M_bd := channelD4Majorant_le_polynomial_gaussian β₀ β₁ ht_pos
    have h_M_bd' : t^(σ-1) * channelD4Majorant β₀ β₁ t ≤
        t^(σ-1) * (Real.exp (C^2 / 4) *
          ((48 + 24 * C^2 + C^4) +
           (192 * C + 16 * C^3) * t +
           (384 + 96 * C^2) * t^2 +
           256 * C * t^3 +
           256 * t^4) * Real.exp (-t^2)) :=
      mul_le_mul_of_nonneg_left h_M_bd h_rpow_nn
    refine le_trans h_M_bd' ?_
    -- Now distribute t^(σ-1) into the polynomial.
    have he0 : t^(σ + (0:ℕ) - 1) = t^(σ - 1) * (t^(0:ℕ) : ℝ) :=
      (rpow_mul_npow_eq ht_pos σ 0).symm
    have he1 : t^(σ + (1:ℕ) - 1) = t^(σ - 1) * (t^(1:ℕ) : ℝ) :=
      (rpow_mul_npow_eq ht_pos σ 1).symm
    have he2 : t^(σ + (2:ℕ) - 1) = t^(σ - 1) * (t^(2:ℕ) : ℝ) :=
      (rpow_mul_npow_eq ht_pos σ 2).symm
    have he3 : t^(σ + (3:ℕ) - 1) = t^(σ - 1) * (t^(3:ℕ) : ℝ) :=
      (rpow_mul_npow_eq ht_pos σ 3).symm
    have he4 : t^(σ + (4:ℕ) - 1) = t^(σ - 1) * (t^(4:ℕ) : ℝ) :=
      (rpow_mul_npow_eq ht_pos σ 4).symm
    have h_t0 : (t^(0:ℕ) : ℝ) = 1 := pow_zero t
    have h_t1 : (t^(1:ℕ) : ℝ) = t := pow_one t
    have h_t2 : (t^(2:ℕ) : ℝ) = t^2 := by norm_num
    have h_t3 : (t^(3:ℕ) : ℝ) = t^3 := by norm_num
    have h_t4 : (t^(4:ℕ) : ℝ) = t^4 := by norm_num
    rw [he0, he1, he2, he3, he4, h_t0, h_t1, h_t2, h_t3, h_t4]
    ring_nf
    exact le_refl _
  -- Apply mono' with measurability + bound + integrable majorant.
  exact h_int_majFn.mono' h_meas h_bound

#print axioms channelD4Majorant_mul_rpow_integrableOn

/-! ## Step F — uniform-in-β bound on `pairDeriv4Mellin`

Using Step C's `pair_cosh_gauss_test_deriv4_uniform_bound_on_Icc` and
Step E5's `channelD4Majorant_mul_rpow_integrableOn`, we get a
β-uniform norm bound on `pairDeriv4Mellin β s` at fixed `s.re = σ`. -/

/-- **β-uniform norm bound on `pairDeriv4Mellin`.** -/
theorem pairDeriv4Mellin_uniform_norm_bound_on_Icc
    {β₀ β₁ : ℝ} {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ Set.Icc β₀ β₁, ∀ s : ℂ, s.re = σ →
        ‖Contour.pairDeriv4Mellin β s‖ ≤ C := by
  -- The integral `∫ channelD4Majorant β₀ β₁ t * t^(σ-1) dt` is the bound.
  set integralBd : ℝ :=
    ∫ t in Set.Ioi (0:ℝ), t^(σ-1) * channelD4Majorant β₀ β₁ t with hI_def
  have h_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(σ-1) * channelD4Majorant β₀ β₁ t) (Set.Ioi (0:ℝ)) :=
    channelD4Majorant_mul_rpow_integrableOn β₀ β₁ hσ
  have h_integralBd_nn : 0 ≤ integralBd := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have : 0 ≤ t^(σ-1) := Real.rpow_nonneg ht.le _
    have : 0 ≤ channelD4Majorant β₀ β₁ t := channelD4Majorant_nonneg β₀ β₁ t
    positivity
  refine ⟨4 * integralBd, by linarith, ?_⟩
  intro β hβ s hs_re
  have h1 := Contour.pairDeriv4Mellin_norm_le_real_integral β s
  -- ‖pairDeriv4Mellin β s‖ ≤ ∫ t^(s.re-1) · |D⁴ pair_cosh_gauss_test β t|
  -- Use Step C bound: |D⁴ ...| ≤ 4 · channelD4Majorant
  -- So ∫ ... ≤ 4 · ∫ t^(σ-1) · channelD4Majorant = 4 · integralBd.
  rw [hs_re] at h1
  refine le_trans h1 ?_
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      t^(σ - 1) *
        |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| ≤
      4 * (t^(σ - 1) * channelD4Majorant β₀ β₁ t) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have h_t_nn : 0 ≤ t^(σ-1) := Real.rpow_nonneg ht_pos.le _
    have h_D4_bd := pair_cosh_gauss_test_deriv4_uniform_bound_on_Icc hβ t
    -- |D⁴ ...| ≤ 4 · channelD4Majorant β₀ β₁ t
    calc t^(σ - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|
        ≤ t^(σ - 1) * (4 * channelD4Majorant β₀ β₁ t) :=
          mul_le_mul_of_nonneg_left h_D4_bd h_t_nn
      _ = 4 * (t^(σ - 1) * channelD4Majorant β₀ β₁ t) := by ring
  have h_int_lhs : MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(σ - 1) *
        |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|)
      (Set.Ioi (0:ℝ)) := by
    -- Use Integrable.mono' (since IntegrableOn = Integrable on restricted measure).
    refine MeasureTheory.Integrable.mono' (h_int.const_mul 4) ?_ ?_
    · -- AEStronglyMeasurable: continuous on Ioi 0
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      apply ContinuousOn.mul
      · refine continuous_id.continuousOn.rpow_const ?_
        intro x hx; left; exact ne_of_gt hx
      · -- |D⁴ pair_cosh_gauss_test β| continuous
        apply Continuous.continuousOn
        apply Continuous.abs
        have h_diff : Differentiable ℝ
            (deriv (deriv (deriv (deriv (pair_cosh_gauss_test β))))) := by
          have := Contour.pair_cosh_gauss_test_iteratedDeriv_differentiable β 4
          simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
        exact h_diff.continuous
    · refine MeasureTheory.ae_restrict_iff' measurableSet_Ioi |>.mpr ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      rw [Real.norm_eq_abs]
      have h_t_nn : 0 ≤ t^(σ-1) := Real.rpow_nonneg ht.le _
      have h_D4_abs_nn : 0 ≤ |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| :=
        abs_nonneg _
      rw [abs_of_nonneg (mul_nonneg h_t_nn h_D4_abs_nn)]
      exact h_pointwise t ht
  calc (∫ t in Set.Ioi (0:ℝ),
          t^(σ - 1) *
            |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|)
      ≤ ∫ t in Set.Ioi (0:ℝ),
          4 * (t^(σ - 1) * channelD4Majorant β₀ β₁ t) := by
        refine MeasureTheory.setIntegral_mono_on h_int_lhs (h_int.const_mul 4)
          measurableSet_Ioi h_pointwise
    _ = 4 * integralBd := by
        rw [MeasureTheory.integral_const_mul]

#print axioms pairDeriv4Mellin_uniform_norm_bound_on_Icc

/-! ## Step G — pairTestMellin quartic decay (final assembly via IBP×4)

Combine Step F with the project's IBP×4 identity
`pairTestMellin β s = (1/(s(s+1)(s+2)(s+3))) · pairDeriv4Mellin β (s+4)`
to get the β-uniform quartic decay on `pairTestMellin β ρ` for `ρ ∈ NTZ`. -/

/-- **β-uniform pointwise bound** on `pairTestMellin β ρ` for `ρ ∈ NTZ` and
β in a compact interval, expressed in terms of `1/|ρ(ρ+1)(ρ+2)(ρ+3)|`. -/
theorem pairTestMellin_uniform_pointwise_bound_via_IBP4
    {β₀ β₁ : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ Set.Icc β₀ β₁,
      ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖Contour.pairTestMellin β ρ.val‖ ≤
          C * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := by
  -- Use Step F at σ = ρ.re + 4 ∈ (4, 5).  Bound the σ-dependent integral
  -- by the maximum over [4, 5] using `t^(σ-1) ≤ t^3 + t^4`.
  -- Combine integrability at σ = 4 and σ = 5 via Step E5.
  have h_int_4 := channelD4Majorant_mul_rpow_integrableOn β₀ β₁ (σ := 4) (by norm_num)
  have h_int_5 := channelD4Majorant_mul_rpow_integrableOn β₀ β₁ (σ := 5) (by norm_num)
  set I4 : ℝ := ∫ t in Set.Ioi (0:ℝ), t^((4:ℝ)-1) * channelD4Majorant β₀ β₁ t
    with hI4_def
  set I5 : ℝ := ∫ t in Set.Ioi (0:ℝ), t^((5:ℝ)-1) * channelD4Majorant β₀ β₁ t
    with hI5_def
  have hI4_nn : 0 ≤ I4 := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have : 0 ≤ t^((4:ℝ)-1) := Real.rpow_nonneg ht.le _
    have : 0 ≤ channelD4Majorant β₀ β₁ t := channelD4Majorant_nonneg β₀ β₁ t
    positivity
  have hI5_nn : 0 ≤ I5 := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have : 0 ≤ t^((5:ℝ)-1) := Real.rpow_nonneg ht.le _
    have : 0 ≤ channelD4Majorant β₀ β₁ t := channelD4Majorant_nonneg β₀ β₁ t
    positivity
  -- The total uniform bound on ‖pairDeriv4Mellin β (ρ+4)‖ is 4·(I4 + I5).
  refine ⟨4 * (I4 + I5), by linarith, ?_⟩
  intro β hβ ρ
  obtain ⟨hρ_re_pos, hρ_re_lt_one, _⟩ := ρ.property
  have hρ_re_pos' : (0 : ℝ) < ρ.val.re := hρ_re_pos
  -- Apply IBP×4: pairTestMellin β ρ = (1/...) · pairDeriv4Mellin β (ρ+4)
  have h_ibp := Contour.pairTestMellin_ibp_four_times β hρ_re_pos'
  rw [h_ibp]
  -- Bound ‖(1/...) · ...‖ ≤ (1/‖...‖) · ‖pairDeriv4Mellin β (ρ+4)‖
  rw [norm_mul, norm_div, norm_one]
  set N : ℝ := ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖
  have hN_eq : ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ = N := rfl
  -- Need: ‖pairDeriv4Mellin β (ρ.val+4)‖ ≤ 4·(I4+I5)
  have h_D4_bd := Contour.pairDeriv4Mellin_norm_le_real_integral β (ρ.val + 4)
  -- ‖pairDeriv4Mellin β (ρ.val+4)‖ ≤ ∫ t^((ρ.val+4).re - 1) · |D⁴ ...| dt
  have h_re : (ρ.val + 4).re = ρ.val.re + 4 := by simp
  rw [h_re] at h_D4_bd
  -- Use Step C bound: |D⁴ ...| ≤ 4 · channelD4Majorant
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      t^(ρ.val.re + 4 - 1) *
        |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| ≤
      4 * (t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have h_t_nn : 0 ≤ t^(ρ.val.re + 4 - 1) := Real.rpow_nonneg ht_pos.le _
    have h_D4_bd_pt := pair_cosh_gauss_test_deriv4_uniform_bound_on_Icc hβ t
    calc t^(ρ.val.re + 4 - 1) *
          |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|
        ≤ t^(ρ.val.re + 4 - 1) * (4 * channelD4Majorant β₀ β₁ t) :=
          mul_le_mul_of_nonneg_left h_D4_bd_pt h_t_nn
      _ = 4 * (t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) := by
          have : t^(ρ.val.re + 4 - 1) = t^(ρ.val.re + 3) := by congr 1; ring
          rw [this]; ring
  -- Bound t^(ρ.re + 3) by t^3 + t^4 (since ρ.re ∈ (0, 1)).
  have h_rpow_split : ∀ t ∈ Set.Ioi (0:ℝ),
      t^(ρ.val.re + 3) ≤ t^((4:ℝ) - 1) + t^((5:ℝ) - 1) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have h_3_eq : t^((4:ℝ) - 1) = t^(3:ℝ) := by congr 1; norm_num
    have h_4_eq : t^((5:ℝ) - 1) = t^(4:ℝ) := by congr 1; norm_num
    rw [h_3_eq, h_4_eq]
    rcases le_or_gt t 1 with hle | hgt
    · -- t ≤ 1: t^(ρ.re+3) ≤ t^3
      have h1 : t^(ρ.val.re + 3) ≤ t^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht_pos hle (by linarith)
      have h2 : (0 : ℝ) ≤ t^(4:ℝ) := Real.rpow_nonneg ht_pos.le _
      linarith
    · -- t > 1: t^(ρ.re+3) ≤ t^4
      have h1 : t^(ρ.val.re + 3) ≤ t^(4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
      have h2 : (0 : ℝ) ≤ t^(3:ℝ) := Real.rpow_nonneg ht_pos.le _
      linarith
  -- Combine: integrand bound + integrability + integral domination.
  have h_int_combined : MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        4 * (t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t)) (Set.Ioi (0:ℝ)) := by
    have h_base : MeasureTheory.IntegrableOn
        (fun t : ℝ => t^(ρ.val.re + 4 - 1) * channelD4Majorant β₀ β₁ t)
        (Set.Ioi (0:ℝ)) :=
      channelD4Majorant_mul_rpow_integrableOn β₀ β₁
        (σ := ρ.val.re + 4) (by linarith)
    have h_eq : (fun t : ℝ => t^(ρ.val.re + 4 - 1) * channelD4Majorant β₀ β₁ t) =
                (fun t : ℝ => t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) := by
      funext t
      have : t^(ρ.val.re + 4 - 1) = t^(ρ.val.re + 3) := by congr 1; ring
      rw [this]
    rw [h_eq] at h_base
    exact h_base.const_mul 4
  have h_int_d4 : MeasureTheory.IntegrableOn
      (fun t : ℝ => t^(ρ.val.re + 4 - 1) *
        |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|)
      (Set.Ioi (0:ℝ)) := by
    refine MeasureTheory.Integrable.mono' h_int_combined ?_ ?_
    · -- AEStronglyMeasurable
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      apply ContinuousOn.mul
      · refine continuous_id.continuousOn.rpow_const ?_
        intro x hx; left; exact ne_of_gt hx
      · apply Continuous.continuousOn
        apply Continuous.abs
        have h_diff : Differentiable ℝ
            (deriv (deriv (deriv (deriv (pair_cosh_gauss_test β))))) := by
          have := Contour.pair_cosh_gauss_test_iteratedDeriv_differentiable β 4
          simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
        exact h_diff.continuous
    · refine MeasureTheory.ae_restrict_iff' measurableSet_Ioi |>.mpr ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      rw [Real.norm_eq_abs]
      have h_t_nn : 0 ≤ t^(ρ.val.re + 4 - 1) := Real.rpow_nonneg ht.le _
      rw [abs_of_nonneg (mul_nonneg h_t_nn (abs_nonneg _))]
      exact h_pointwise t ht
  -- Final bound.
  have h_int_le : (∫ t in Set.Ioi (0:ℝ),
        t^(ρ.val.re + 4 - 1) *
          |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) ≤
      4 * (I4 + I5) := by
    have h_step1 : (∫ t in Set.Ioi (0:ℝ),
          t^(ρ.val.re + 4 - 1) *
            |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) ≤
        ∫ t in Set.Ioi (0:ℝ),
          4 * (t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) :=
      MeasureTheory.setIntegral_mono_on h_int_d4 h_int_combined
        measurableSet_Ioi h_pointwise
    have h_step2 : (∫ t in Set.Ioi (0:ℝ),
          4 * (t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t)) ≤
        4 * (I4 + I5) := by
      rw [MeasureTheory.integral_const_mul]
      have h_split_int : (∫ t in Set.Ioi (0:ℝ),
            t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) ≤
          ∫ t in Set.Ioi (0:ℝ),
            (t^((4:ℝ) - 1) + t^((5:ℝ) - 1)) * channelD4Majorant β₀ β₁ t := by
        have h_int_lhs_var : MeasureTheory.IntegrableOn
            (fun t : ℝ => t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t)
            (Set.Ioi (0:ℝ)) := by
          have h_base : MeasureTheory.IntegrableOn
              (fun t : ℝ => t^(ρ.val.re + 4 - 1) * channelD4Majorant β₀ β₁ t)
              (Set.Ioi (0:ℝ)) :=
            channelD4Majorant_mul_rpow_integrableOn β₀ β₁
              (σ := ρ.val.re + 4) (by linarith)
          have h_eq : (fun t : ℝ => t^(ρ.val.re + 4 - 1) * channelD4Majorant β₀ β₁ t) =
                      (fun t : ℝ => t^(ρ.val.re + 3) * channelD4Majorant β₀ β₁ t) := by
            funext t
            have : t^(ρ.val.re + 4 - 1) = t^(ρ.val.re + 3) := by congr 1; ring
            rw [this]
          rw [h_eq] at h_base
          exact h_base
        have h_int_rhs_split : MeasureTheory.IntegrableOn
            (fun t : ℝ =>
              (t^((4:ℝ) - 1) + t^((5:ℝ) - 1)) * channelD4Majorant β₀ β₁ t)
            (Set.Ioi (0:ℝ)) := by
          have h_sum : MeasureTheory.IntegrableOn
              (fun t : ℝ => t^((4:ℝ) - 1) * channelD4Majorant β₀ β₁ t +
                            t^((5:ℝ) - 1) * channelD4Majorant β₀ β₁ t)
              (Set.Ioi (0:ℝ)) := h_int_4.add h_int_5
          have h_eq : (fun t : ℝ => t^((4:ℝ) - 1) * channelD4Majorant β₀ β₁ t +
                                    t^((5:ℝ) - 1) * channelD4Majorant β₀ β₁ t) =
                      (fun t : ℝ => (t^((4:ℝ) - 1) + t^((5:ℝ) - 1)) *
                                    channelD4Majorant β₀ β₁ t) := by
            funext t; ring
          rw [h_eq] at h_sum
          exact h_sum
        refine MeasureTheory.setIntegral_mono_on h_int_lhs_var h_int_rhs_split
          measurableSet_Ioi ?_
        intro t ht
        have h_M_nn : 0 ≤ channelD4Majorant β₀ β₁ t := channelD4Majorant_nonneg β₀ β₁ t
        have h_split := h_rpow_split t ht
        exact mul_le_mul_of_nonneg_right h_split h_M_nn
      have h_eq : (∫ t in Set.Ioi (0:ℝ),
            (t^((4:ℝ) - 1) + t^((5:ℝ) - 1)) * channelD4Majorant β₀ β₁ t) =
          I4 + I5 := by
        have h_dist : ∀ t ∈ Set.Ioi (0:ℝ),
            (t^((4:ℝ) - 1) + t^((5:ℝ) - 1)) * channelD4Majorant β₀ β₁ t =
            t^((4:ℝ) - 1) * channelD4Majorant β₀ β₁ t +
            t^((5:ℝ) - 1) * channelD4Majorant β₀ β₁ t := fun t _ => by ring
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_dist]
        rw [MeasureTheory.integral_add h_int_4 h_int_5]
      linarith
    linarith
  -- Combine everything.
  have h_d4_bd : ‖Contour.pairDeriv4Mellin β (ρ.val + 4)‖ ≤ 4 * (I4 + I5) :=
    le_trans h_D4_bd h_int_le
  -- ‖(1/Q) · D4M‖ = ‖1‖/‖Q‖ · ‖D4M‖ ≤ ‖1‖/‖Q‖ · 4(I4+I5) = (4(I4+I5)) · (1/‖Q‖).
  have hN_pos : 0 < N := by
    show 0 < ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖
    apply norm_pos_iff.mpr
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · intro h; rw [h] at hρ_re_pos; simp at hρ_re_pos
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have h_inv_nn : 0 ≤ 1/N := one_div_nonneg.mpr hN_pos.le
  calc 1 / N * ‖Contour.pairDeriv4Mellin β (ρ.val + 4)‖
      ≤ 1 / N * (4 * (I4 + I5)) :=
        mul_le_mul_of_nonneg_left h_d4_bd h_inv_nn
    _ = 4 * (I4 + I5) * (1 / N) := by ring

#print axioms pairTestMellin_uniform_pointwise_bound_via_IBP4

/-! ## Step H — convert IBP×4 form to `Complex.normSq` form

The Field 2 obligation is in the form `1 / Complex.normSq(ρ(ρ-1))`,
while Step G gives `1 / ‖ρ(ρ+1)(ρ+2)(ρ+3)‖`.  For `ρ ∈ NTZ`,
`Complex.normSq(ρ(ρ-1)) ≤ ‖ρ(ρ+1)(ρ+2)(ρ+3)‖`, so reciprocals reverse. -/

/-- For `ρ ∈ NTZ`, `Complex.normSq(ρ(ρ-1)) ≤ ‖ρ(ρ+1)(ρ+2)(ρ+3)‖`. -/
lemma normSq_le_norm_quartic_on_NTZ
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    Complex.normSq (ρ.val * (ρ.val - 1)) ≤
      ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ := by
  obtain ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  set re : ℝ := ρ.val.re with hre_def
  set im : ℝ := ρ.val.im with him_def
  have h_re_pos : 0 < re := hRe_pos
  have h_re_lt : re < 1 := hRe_lt
  -- Squared inequality: (Re²+Im²)·((Re-1)²+Im²)² ≤ ((Re+1)²+Im²)·((Re+2)²+Im²)·((Re+3)²+Im²).
  -- Since both sides of the original inequality are non-negative, squaring is order-preserving.
  -- Compute LHS (squared norm of ρ(ρ-1)) and RHS (norm of ρ(ρ+1)(ρ+2)(ρ+3)).
  have h_normSq_lhs :
      Complex.normSq (ρ.val * (ρ.val - 1)) = (re^2 + im^2) * ((re-1)^2 + im^2) := by
    rw [Complex.normSq_mul]
    have h1 : Complex.normSq ρ.val = re^2 + im^2 := by
      rw [Complex.normSq_apply]; show _ = re^2 + im^2; ring
    have h2 : Complex.normSq (ρ.val - 1) = (re - 1)^2 + im^2 := by
      rw [Complex.normSq_apply]
      have h_re_eq : (ρ.val - 1).re = re - 1 := by
        rw [Complex.sub_re, Complex.one_re]
      have h_im_eq : (ρ.val - 1).im = im := by
        rw [Complex.sub_im, Complex.one_im, sub_zero]
      rw [h_re_eq, h_im_eq]; ring
    rw [h1, h2]
  -- For RHS, compute the norm as sqrt of normSq.
  set N : ℝ := ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖
  have hN_sq : N^2 = ((re^2 + im^2)) *
      (((re+1)^2 + im^2)) * (((re+2)^2 + im^2)) * (((re+3)^2 + im^2)) := by
    have h_eq : N^2 = Complex.normSq (ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)) :=
      Complex.sq_norm _
    rw [h_eq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
    have h_ρ : Complex.normSq ρ.val = re^2 + im^2 := by
      rw [Complex.normSq_apply]; show _ = re^2 + im^2; ring
    have h_ρ1 : Complex.normSq (ρ.val + 1) = (re + 1)^2 + im^2 := by
      rw [Complex.normSq_apply]
      have h_re_eq : (ρ.val + 1).re = re + 1 := by
        rw [Complex.add_re, Complex.one_re]
      have h_im_eq : (ρ.val + 1).im = im := by
        rw [Complex.add_im, Complex.one_im, add_zero]
      rw [h_re_eq, h_im_eq]; ring
    have h_ρ2 : Complex.normSq (ρ.val + 2) = (re + 2)^2 + im^2 := by
      rw [Complex.normSq_apply]
      have h_re_eq : (ρ.val + 2).re = re + 2 := by
        rw [Complex.add_re]; show ρ.val.re + (2:ℂ).re = re + 2
        simp; rfl
      have h_im_eq : (ρ.val + 2).im = im := by
        rw [Complex.add_im]; show ρ.val.im + (2:ℂ).im = im
        simp; rfl
      rw [h_re_eq, h_im_eq]; ring
    have h_ρ3 : Complex.normSq (ρ.val + 3) = (re + 3)^2 + im^2 := by
      rw [Complex.normSq_apply]
      have h_re_eq : (ρ.val + 3).re = re + 3 := by
        rw [Complex.add_re]; show ρ.val.re + (3:ℂ).re = re + 3
        simp; rfl
      have h_im_eq : (ρ.val + 3).im = im := by
        rw [Complex.add_im]; show ρ.val.im + (3:ℂ).im = im
        simp; rfl
      rw [h_re_eq, h_im_eq]; ring
    rw [h_ρ, h_ρ1, h_ρ2, h_ρ3]
  have hN_nn : 0 ≤ N := norm_nonneg _
  -- Goal: Complex.normSq(ρ(ρ-1)) ≤ N
  rw [h_normSq_lhs]
  -- Equivalent: (re²+im²)·((re-1)²+im²) ≤ N (where N = sqrt(...)).
  -- Show LHS² ≤ N² and use nonneg sqrt monotonicity.
  have h_lhs_nn : 0 ≤ (re^2 + im^2) * ((re-1)^2 + im^2) := by positivity
  have h_lhs_sq_le_N_sq : ((re^2 + im^2) * ((re-1)^2 + im^2))^2 ≤ N^2 := by
    rw [hN_sq]
    -- Decompose with explicit names and use monotonicity:
    -- u := re²+im², v := (re-1)²+im², a := (re+1)²+im², b := (re+2)²+im², c := (re+3)²+im².
    -- Key: u ≤ a (since re > 0 ⟹ re² ≤ (re+1)²), v ≤ b, v ≤ c (Re ∈ (0,1) ⟹ |re-1| < 1 ≤ |re+2|, |re+3|).
    -- Then (uv)² = u²v² = u·(u·v·v) ≤ u·(a·b·c).
    set u : ℝ := re^2 + im^2 with hu_def
    set v : ℝ := (re-1)^2 + im^2 with hv_def
    set a : ℝ := (re+1)^2 + im^2 with ha_def
    set b : ℝ := (re+2)^2 + im^2 with hb_def
    set c : ℝ := (re+3)^2 + im^2 with hc_def
    have hu_nn : 0 ≤ u := by simp [hu_def]; positivity
    have hv_nn : 0 ≤ v := by simp [hv_def]; positivity
    have ha_nn : 0 ≤ a := by simp [ha_def]; positivity
    have hb_nn : 0 ≤ b := by simp [hb_def]; positivity
    have hc_nn : 0 ≤ c := by simp [hc_def]; positivity
    have hu_le_a : u ≤ a := by
      have h_sq : re^2 ≤ (re+1)^2 := by nlinarith
      show re^2 + im^2 ≤ (re+1)^2 + im^2
      linarith
    have hv_le_b : v ≤ b := by
      have h_sq : (re-1)^2 ≤ (re+2)^2 := by nlinarith
      show (re-1)^2 + im^2 ≤ (re+2)^2 + im^2
      linarith
    have hv_le_c : v ≤ c := by
      have h_sq : (re-1)^2 ≤ (re+3)^2 := by nlinarith
      show (re-1)^2 + im^2 ≤ (re+3)^2 + im^2
      linarith
    have h_uv_le_ab : u * v ≤ a * b :=
      mul_le_mul hu_le_a hv_le_b hv_nn ha_nn
    have h_uvv_le_abc : u * v * v ≤ a * b * c := by
      calc u * v * v
          ≤ a * b * v := mul_le_mul_of_nonneg_right h_uv_le_ab hv_nn
        _ ≤ a * b * c := mul_le_mul_of_nonneg_left hv_le_c (mul_nonneg ha_nn hb_nn)
    show (u * v)^2 ≤ u * a * b * c
    calc (u * v)^2
        = u * (u * v * v) := by ring
      _ ≤ u * (a * b * c) := mul_le_mul_of_nonneg_left h_uvv_le_abc hu_nn
      _ = u * a * b * c := by ring
  -- Conclude via sqrt-monotonicity.
  have h_sqrt := Real.sqrt_le_sqrt h_lhs_sq_le_N_sq
  rw [Real.sqrt_sq h_lhs_nn, Real.sqrt_sq hN_nn] at h_sqrt
  exact h_sqrt

#print axioms normSq_le_norm_quartic_on_NTZ

/-- **Quartic decay (Field 2 form): `‖pairTestMellin β ρ‖ ≤ C / Complex.normSq(ρ(ρ-1))`**
uniformly for `β ∈ [β₀, β₁]` and `ρ ∈ NTZ`.  The body matches
`pairTestMellin_uniform_quartic_decay_on_Icc_target` (from
`NaturalKCoefficientAdmissible`) verbatim — that file uses this lemma to
discharge Field 2 unconditionally. -/
theorem pairTestMellin_uniform_quartic_decay_on_Icc_holds :
    ∀ β₀ β₁ : ℝ, 0 < β₀ → β₀ ≤ β₁ → β₁ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ β ∈ Set.Icc β₀ β₁, ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          ‖Contour.pairTestMellin β ρ.val‖ ≤
            C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) := by
  intro β₀ β₁ hβ₀ hβ₀₁ hβ₁
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    pairTestMellin_uniform_pointwise_bound_via_IBP4 (β₀ := β₀) (β₁ := β₁)
  refine ⟨C, hC_nn, ?_⟩
  intro β hβ ρ
  have h_step1 := hC_bd β hβ ρ
  -- h_step1 : ‖pairTestMellin β ρ.val‖ ≤ C * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖)
  have h_normSq_le := normSq_le_norm_quartic_on_NTZ ρ
  -- Need: 1 / ‖ρ(ρ+1)(ρ+2)(ρ+3)‖ ≤ 1 / Complex.normSq(ρ(ρ-1)).
  obtain ⟨hRe_pos, hRe_lt, hZeta⟩ := ρ.property
  have hρ_ne_zero : ρ.val ≠ 0 := by
    intro h; rw [h] at hRe_pos; simp at hRe_pos
  have hρ_minus_one_ne_zero : ρ.val - 1 ≠ 0 := by
    intro h
    have : ρ.val.re - 1 = 0 := by rw [show ρ.val.re - 1 = (ρ.val - 1).re from by simp, h]; simp
    linarith
  have h_normSq_pos : 0 < Complex.normSq (ρ.val * (ρ.val - 1)) := by
    rw [Complex.normSq_mul]
    apply mul_pos
    · exact Complex.normSq_pos.mpr hρ_ne_zero
    · exact Complex.normSq_pos.mpr hρ_minus_one_ne_zero
  have h_norm_pos : 0 < ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ := by
    apply norm_pos_iff.mpr
    apply mul_ne_zero; apply mul_ne_zero; apply mul_ne_zero
    · exact hρ_ne_zero
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have h_one_div_le : 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ ≤
      1 / Complex.normSq (ρ.val * (ρ.val - 1)) :=
    one_div_le_one_div_of_le h_normSq_pos h_normSq_le
  -- Combine.
  calc ‖Contour.pairTestMellin β ρ.val‖
      ≤ C * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := h_step1
    _ ≤ C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
        mul_le_mul_of_nonneg_left h_one_div_le hC_nn

#print axioms pairTestMellin_uniform_quartic_decay_on_Icc_holds

/-- **Quartic decay on an arbitrary real β-interval** — drops the `(0,1)`
constraint on β.  Same proof as `..._on_Icc_holds`; the `(0,1)` hypotheses
were not used.  Needed for the Field-3 (Weierstrass) extension to all of
`ℝ`. -/
theorem pairTestMellin_uniform_quartic_decay_on_real_Icc_holds :
    ∀ β₀ β₁ : ℝ, β₀ ≤ β₁ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ β ∈ Set.Icc β₀ β₁, ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          ‖Contour.pairTestMellin β ρ.val‖ ≤
            C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) := by
  intro β₀ β₁ _hβ₀₁
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    pairTestMellin_uniform_pointwise_bound_via_IBP4 (β₀ := β₀) (β₁ := β₁)
  refine ⟨C, hC_nn, ?_⟩
  intro β hβ ρ
  have h_step1 := hC_bd β hβ ρ
  have h_normSq_le := normSq_le_norm_quartic_on_NTZ ρ
  obtain ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  have hρ_ne_zero : ρ.val ≠ 0 := by
    intro h; rw [h] at hRe_pos; simp at hRe_pos
  have hρ_minus_one_ne_zero : ρ.val - 1 ≠ 0 := by
    intro h
    have : ρ.val.re - 1 = 0 := by rw [show ρ.val.re - 1 = (ρ.val - 1).re from by simp, h]; simp
    linarith
  have h_normSq_pos : 0 < Complex.normSq (ρ.val * (ρ.val - 1)) := by
    rw [Complex.normSq_mul]
    apply mul_pos
    · exact Complex.normSq_pos.mpr hρ_ne_zero
    · exact Complex.normSq_pos.mpr hρ_minus_one_ne_zero
  have h_one_div_le : 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ ≤
      1 / Complex.normSq (ρ.val * (ρ.val - 1)) :=
    one_div_le_one_div_of_le h_normSq_pos h_normSq_le
  calc ‖Contour.pairTestMellin β ρ.val‖
      ≤ C * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := h_step1
    _ ≤ C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
        mul_le_mul_of_nonneg_left h_one_div_le hC_nn

#print axioms pairTestMellin_uniform_quartic_decay_on_real_Icc_holds

/-- **Quartic decay on every real compact** — `IsCompact` form, the
shape needed by Field 3's `h_unif_full` hypothesis. -/
theorem pairTestMellin_uniform_quartic_decay_on_compact_holds
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ K, ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖Contour.pairTestMellin β ρ.val‖ ≤
          C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) := by
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro β hβ; rw [hK_empty] at hβ; exact absurd hβ (Set.notMem_empty β)
  have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨β₀, hβ₀_in, hβ₀_min⟩ := hK.exists_isLeast hK_nonempty
  obtain ⟨β₁, hβ₁_in, hβ₁_max⟩ := hK.exists_isGreatest hK_nonempty
  have hβ₀_le_β₁ : β₀ ≤ β₁ := hβ₁_max hβ₀_in
  obtain ⟨C, hC_nn, h_bd⟩ :=
    pairTestMellin_uniform_quartic_decay_on_real_Icc_holds β₀ β₁ hβ₀_le_β₁
  refine ⟨C, hC_nn, ?_⟩
  intro β hβ ρ
  exact h_bd β ⟨hβ₀_min hβ, hβ₁_max hβ⟩ ρ

#print axioms pairTestMellin_uniform_quartic_decay_on_compact_holds

end BetaTower
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
