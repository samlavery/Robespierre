import Mathlib
import RequestProject.CauchyKPairTestK2Weil
import RequestProject.CauchyKPairTestVerticalIntegrable
import RequestProject.CauchyKPairTestResidueSum
import RequestProject.CauchyKPairTestHorizontal
import RequestProject.WeilFinalAssembly
import RequestProject.WeilFinalAssemblyUnconditional

/-!
# Unconditional discharge of the 4 chunk-2 targets at `K = K_2_fn t`

For each fixed `t : ℝ`, discharges the 4 chunk-2 conditional targets at
the kernel `K_2_fn t` (the partially-applied cosh-pair kernel from the
Plancherel form):

1. `K_pairTestMellin_vertical_at_two_integrable (K_2_fn t) β`
2. `K_pairTestMellin_vertical_at_neg_one_integrable (K_2_fn t) β`
3. `K_pairTestMellin_zeroSum_summable (K_2_fn t) β n`
4. `K_pairTestMellin_horizontal_vanishes_target (K_2_fn t) β`

Mirrors the corresponding discharges for `gaussianDefectEntireKernel_local`,
with the strip bound `‖K_2(σ+iy, t)‖ ≤ Real.cosh(2|σ-1/2|·|t|) + 2·Real.cosh(|σ-1/2|·|t|) + 1`
in place of the Gaussian-form bound.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.WeilPositivity.OfflineDetectorEndpoint
open ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch

/-! ## Core bound: `‖Complex.cosh z‖ ≤ Real.cosh z.re` -/

/-- Norm of `Complex.cosh` is bounded by `Real.cosh` of the real part. -/
private lemma norm_cosh_le_cosh_re (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have h_two : (2 : ℂ) * Complex.cosh z = Complex.exp z + Complex.exp (-z) :=
    @Complex.two_cosh z
  have h_norm_2cosh : ‖(2 : ℂ) * Complex.cosh z‖ = 2 * ‖Complex.cosh z‖ := by
    rw [norm_mul]; simp
  have h_norm_le : ‖(2 : ℂ) * Complex.cosh z‖ ≤ 2 * Real.cosh z.re := by
    rw [h_two]
    calc ‖Complex.exp z + Complex.exp (-z)‖
        ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
      _ = Real.exp z.re + Real.exp (-z).re := by
          rw [Complex.norm_exp, Complex.norm_exp]
      _ = Real.exp z.re + Real.exp (-z.re) := by rw [Complex.neg_re]
      _ = 2 * Real.cosh z.re := by rw [Real.cosh_eq]; ring
  rw [h_norm_2cosh] at h_norm_le
  linarith

/-- For `s = σ + iτ` in the strip with `|σ - 1/2| ≤ M`, bound `‖K_2(s, t)‖`
uniformly in `τ`. -/
private lemma K_2_norm_le (t : ℝ) (s : ℂ) (M : ℝ) (h_re_bd : |s.re - 1/2| ≤ M) :
    ‖K_2 s t‖ ≤
      Real.cosh (2 * M * |t|) + 2 * Real.cosh (M * |t|) + 1 := by
  unfold K_2
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) h_re_bd
  -- ‖cosh(2(s-1/2)t)‖ ≤ Real.cosh(2 M |t|).
  have h_cosh1 : ‖Complex.cosh (2 * (s - 1/2) * (t : ℂ))‖ ≤ Real.cosh (2 * M * |t|) := by
    refine le_trans (norm_cosh_le_cosh_re _) ?_
    have h_re : (2 * (s - 1/2) * (t : ℂ)).re = 2 * (s.re - 1/2) * t := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [h_re]
    have h_abs_le : |2 * (s.re - 1/2) * t| ≤ 2 * M * |t| := by
      rw [show 2 * (s.re - 1/2) * t = 2 * ((s.re - 1/2) * t) from by ring]
      rw [abs_mul]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2, abs_mul]
      have hAbsT : 0 ≤ |t| := abs_nonneg _
      have h2_nn : 0 ≤ (2 : ℝ) := by norm_num
      calc 2 * (|s.re - 1/2| * |t|)
          ≤ 2 * (M * |t|) := by
            apply mul_le_mul_of_nonneg_left _ h2_nn
            exact mul_le_mul_of_nonneg_right h_re_bd hAbsT
        _ = 2 * M * |t| := by ring
    rw [show Real.cosh (2 * (s.re - 1/2) * t) = Real.cosh |2 * (s.re - 1/2) * t| from
        (Real.cosh_abs _).symm]
    apply (Real.cosh_le_cosh).mpr
    rw [abs_abs]
    exact le_trans h_abs_le (le_abs_self _)
  -- ‖cosh((s-1/2)t)‖ ≤ Real.cosh(M |t|).
  have h_cosh2 : ‖Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤ Real.cosh (M * |t|) := by
    refine le_trans (norm_cosh_le_cosh_re _) ?_
    have h_re : ((s - 1/2) * (t : ℂ)).re = (s.re - 1/2) * t := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [h_re]
    have h_abs_le : |(s.re - 1/2) * t| ≤ M * |t| := by
      rw [abs_mul]
      have hAbsT : 0 ≤ |t| := abs_nonneg _
      exact mul_le_mul_of_nonneg_right h_re_bd hAbsT
    rw [show Real.cosh ((s.re - 1/2) * t) = Real.cosh |(s.re - 1/2) * t| from
        (Real.cosh_abs _).symm]
    apply (Real.cosh_le_cosh).mpr
    rw [abs_abs]
    exact le_trans h_abs_le (le_abs_self _)
  calc ‖Complex.cosh (2 * (s - 1/2) * (t : ℂ)) -
        2 * Complex.cosh ((s - 1/2) * (t : ℂ)) + 1‖
      ≤ ‖Complex.cosh (2 * (s - 1/2) * (t : ℂ)) -
            2 * Complex.cosh ((s - 1/2) * (t : ℂ))‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖Complex.cosh (2 * (s - 1/2) * (t : ℂ))‖ +
          ‖2 * Complex.cosh ((s - 1/2) * (t : ℂ))‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.cosh (2 * M * |t|) + 2 * Real.cosh (M * |t|) + 1 := by
        have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h_norm_one]
        have h_2_norm : ‖2 * Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤
            2 * Real.cosh (M * |t|) := by
          rw [norm_mul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          have hnn : 0 ≤ ‖Complex.cosh ((s - 1/2) * (t : ℂ))‖ := norm_nonneg _
          linarith [h_cosh2]
        linarith [h_cosh1]

/-- For `σ ∈ [-1, 2]`, `|σ - 1/2| ≤ 3/2`. -/
private lemma re_diff_bd_strip {σ : ℝ} (hσ : σ ∈ Set.Icc (-1:ℝ) 2) :
    |σ - 1/2| ≤ 3/2 := by
  obtain ⟨h1, h2⟩ := hσ
  have hl : -(3/2 : ℝ) ≤ σ - 1/2 := by linarith
  have hh : σ - 1/2 ≤ 3/2 := by linarith
  exact abs_le.mpr ⟨hl, hh⟩

/-- `‖K_2(s, t)‖ ≤ cosh(3|t|) + 2·cosh((3/2)|t|) + 1` for `s` with `s.re ∈ [-1, 2]`. -/
private lemma K_2_norm_le_strip (t : ℝ) (s : ℂ) (hs_re : s.re ∈ Set.Icc (-1:ℝ) 2) :
    ‖K_2 s t‖ ≤ Real.cosh (3 * |t|) + 2 * Real.cosh ((3/2) * |t|) + 1 := by
  have h_re_bd : |s.re - 1/2| ≤ 3/2 := re_diff_bd_strip hs_re
  have h := K_2_norm_le t s (3/2) h_re_bd
  have h1 : 2 * (3/2 : ℝ) = 3 := by norm_num
  rw [h1] at h
  exact h

/-! ## Discharges of the 4 chunk-2 targets at `K_2_fn t` -/

/-- **Discharge of `K_pairTestMellin_vertical_at_two_integrable (K_2_fn t) β`.** -/
theorem K_2_fn_vertical_at_two_integrable (t : ℝ) (β : ℝ) :
    K_pairTestMellin_vertical_at_two_integrable (K_2_fn t) β := by
  unfold K_pairTestMellin_vertical_at_two_integrable
  have h_eq : (fun y : ℝ => K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun y : ℝ => K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        Contour.primeIntegrand β 2 y) := by
    funext y
    rw [Contour.weilIntegrand_eq_primeIntegrand_on_right_edge β
      (show (1:ℝ) < 2 by norm_num) y]
  rw [h_eq]
  set C : ℝ := Real.cosh (3 * |t|) + 2 * Real.cosh ((3/2) * |t|) + 1 with hC_def
  have hCbd : ∀ y : ℝ, ‖K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
    intro y
    apply K_2_norm_le_strip
    have : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = 2 := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [this]; exact ⟨by norm_num, le_refl _⟩
  have hPI : Integrable (Contour.primeIntegrand β 2) :=
    Contour.primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)
  have h_K_meas : AEStronglyMeasurable
      (fun y : ℝ => K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume := by
    have hpath : Continuous (fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ((K_2_fn_differentiable t).continuous.comp hpath).aestronglyMeasurable
  exact hPI.bdd_mul h_K_meas (Filter.Eventually.of_forall hCbd)

/-- **Discharge of `K_pairTestMellin_vertical_at_neg_one_integrable (K_2_fn t) β`.** -/
theorem K_2_fn_vertical_at_neg_one_integrable (t : ℝ) (β : ℝ) :
    K_pairTestMellin_vertical_at_neg_one_integrable (K_2_fn t) β := by
  unfold K_pairTestMellin_vertical_at_neg_one_integrable
  have h_wI_eq : (fun y : ℝ =>
        Contour.weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (fun y : ℝ => Contour.archIntegrand β (-1) y +
        Contour.reflectedPrimeIntegrand β (-1) y) := by
    funext y
    exact ZD.WeilPositivity.FinalAssembly.weilIntegrand_pair_left_edge_neg_one_split β y
  have h_arch_int : Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_refl_int : Integrable (Contour.reflectedPrimeIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.reflectedPrimeIntegrand_at_neg_one_integrable β
  have h_wI_int : Integrable (fun y : ℝ =>
      Contour.weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    rw [h_wI_eq]
    exact h_arch_int.add h_refl_int
  set C : ℝ := Real.cosh (3 * |t|) + 2 * Real.cosh ((3/2) * |t|) + 1 with hC_def
  have hCbd : ∀ y : ℝ, ‖K_2_fn t (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C := by
    intro y
    apply K_2_norm_le_strip
    have : (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re = -1 := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [this]; exact ⟨le_refl _, by norm_num⟩
  have h_K_meas : AEStronglyMeasurable
      (fun y : ℝ => K_2_fn t (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume := by
    have hpath : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ((K_2_fn_differentiable t).continuous.comp hpath).aestronglyMeasurable
  exact h_wI_int.bdd_mul h_K_meas (Filter.Eventually.of_forall hCbd)

/-- **Summability of the K_2-twisted multiplicity-weighted zero sum**.
For each `t`, `Σ' n(ρ)·K_2(ρ,t)·M(β,ρ)` is absolutely summable. -/
theorem K_2_fn_zeroSum_summable_holds (t : ℝ) (β : ℝ) :
    K_pairTestMellin_zeroSum_summable (K_2_fn t) β
      (fun ρ : ℂ => by
        classical
        exact if hρ : ρ ∈ NontrivialZeros then
          Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
        else 0) := by
  unfold K_pairTestMellin_zeroSum_summable
  classical
  set n : ℂ → ℕ := fun ρ : ℂ =>
    if hρ : ρ ∈ NontrivialZeros then
      Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
    else 0
    with hn_def
  have h_un_twisted : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val) :=
    ZD.WeilPositivity.FinalAssembly.h_sum_unconditional β
  set M_K : ℝ := Real.cosh (3 * |t|) + 2 * Real.cosh ((3/2) * |t|) + 1 with hM_K_def
  have hM_K_bd : ∀ ρ ∈ NontrivialZeros, ‖K_2_fn t ρ‖ ≤ M_K := by
    intro ρ hρ
    apply K_2_norm_le_strip
    obtain ⟨h1, h2, _⟩ := hρ
    exact ⟨by linarith, by linarith⟩
  have h_norm_summable : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        ‖((n ρ.val : ℕ) : ℂ) * K_2_fn t ρ.val *
          Contour.pairTestMellin β ρ.val‖) := by
    have h_un_twisted_norm : Summable
        (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
          ‖(((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
              : ℕ) : ℂ)) * Contour.pairTestMellin β ρ.val‖) :=
      h_un_twisted.norm
    have h_dominated : Summable
        (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
          M_K * ‖(((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
              : ℕ) : ℂ)) * Contour.pairTestMellin β ρ.val‖) :=
      h_un_twisted_norm.mul_left M_K
    refine h_dominated.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
    have hKbd : ‖K_2_fn t ρ.val‖ ≤ M_K := hM_K_bd ρ.val ρ.property
    have hKnn : 0 ≤ ‖K_2_fn t ρ.val‖ := norm_nonneg _
    have h_choose_eq :
        (n ρ.val : ℕ) = Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) := by
      simp [hn_def, ρ.property]
    rw [norm_mul, norm_mul, norm_mul]
    rw [h_choose_eq]
    set m : ℕ := Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
      with hm_def
    have h_n_norm : ‖((m : ℕ) : ℂ)‖ = ((m : ℕ) : ℝ) := by simp
    rw [h_n_norm]
    have h_pm_nn : 0 ≤ ‖Contour.pairTestMellin β ρ.val‖ := norm_nonneg _
    have h_n_nn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKbd h_n_nn) h_pm_nn,
      mul_nonneg h_n_nn hKnn]
  exact Summable.of_norm h_norm_summable

/-! ## Horizontal vanishing for `K_2_fn t` -/

/-- **Discharge of `K_pairTestMellin_horizontal_vanishes_target (K_2_fn t) β`.**
Mirrors `K_pairTestMellin_horizontal_vanishes_target_holds` for K. -/
theorem K_2_fn_horizontal_vanishes_target_holds (t : ℝ) (β : ℝ) :
    K_pairTestMellin_horizontal_vanishes_target (K_2_fn t) β := by
  unfold K_pairTestMellin_horizontal_vanishes_target
  intro ε hε
  -- Set up the K_2 strip bound and ζ-Mellin bounds.
  set M_K : ℝ := Real.cosh (3 * |t|) + 2 * Real.cosh ((3/2) * |t|) + 1 with hM_K_def
  have hM_K_nn : 0 ≤ M_K := by
    have h1 : (1 : ℝ) ≤ Real.cosh (3 * |t|) := Real.one_le_cosh _
    have h2 : (1 : ℝ) ≤ Real.cosh ((3/2) * |t|) := Real.one_le_cosh _
    rw [hM_K_def]; linarith
  have hM_K_bd : ∀ σ T : ℝ, σ ∈ Set.Icc (-1:ℝ) 2 →
      ‖K_2_fn t ((σ : ℂ) + (T : ℂ) * I)‖ ≤ M_K := by
    intro σ T hσ
    apply K_2_norm_le_strip
    have : ((σ : ℂ) + (T : ℂ) * I).re = σ := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [this]; exact hσ
  -- Top edge: same template as K-horizontal vanishing.
  have h_top : ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖∫ x : ℝ in (-1:ℝ)..2,
          K_2_fn t ((x : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ < ε := by
    intro ε' hε'
    obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt, hLD⟩ :=
      full_strip_logDerivZeta_bound_N_lt_4_unconditional
    obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := uniform_pairMellin_quartic_target_pos β
    set Ktot : ℝ := M_K * C_ζ * C_M * 3 + 1 with hKtot_def
    have hKtot_pos : 0 < Ktot := by
      rw [hKtot_def]
      have h_pos : 0 ≤ M_K * C_ζ * C_M * 3 :=
        mul_nonneg (mul_nonneg (mul_nonneg hM_K_nn hC_ζ_pos.le) hC_M_nn) (by norm_num)
      linarith
    have h4mN_pos : 0 < 4 - N := by linarith
    have hKε : 0 < Ktot / ε' := div_pos hKtot_pos hε'
    set Tbig : ℝ := (Ktot / ε') ^ (1 / (4 - N)) with hTbig_def
    have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
    set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
    have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
    have hT_ge_Tζ : T₀_ζ ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hT_ge_TM : T₀_M ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    have hT_ge_Tbig : Tbig ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hT_ge_2 : (2 : ℝ) ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hT_pos : 0 < T := by linarith
    have h_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
        ‖K_2_fn t ((σ : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (T : ℝ) * I)‖ ≤
          M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) := by
      intro σ hσ_mem
      have h_uIoc : Set.uIoc (-1:ℝ) 2 = Set.Ioc (-1:ℝ) 2 :=
        Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)
      rw [h_uIoc] at hσ_mem
      have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ_mem.1.le, hσ_mem.2⟩
      have hKbd : ‖K_2_fn t ((σ : ℂ) + (T : ℝ) * I)‖ ≤ M_K := by
        have hspec := hM_K_bd σ T hσ_Icc
        convert hspec using 2
      have hζ_bd := hLD T hT_ge_Tζ hGood σ hσ_Icc
      have hM_bd := hM T hT_ge_TM σ hσ_Icc
      rw [norm_mul, Contour.weilIntegrand_norm_factored]
      have h_W_nn : 0 ≤ ‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
            ((σ : ℂ) + (T : ℝ) * I)‖ := by positivity
      have h_W_bd : ‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
            ((σ : ℂ) + (T : ℝ) * I)‖ ≤ C_ζ * T ^ N * (C_M / T ^ 4) := by
        apply mul_le_mul hζ_bd hM_bd (norm_nonneg _)
        exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
      calc ‖K_2_fn t ((σ : ℂ) + (T : ℝ) * I)‖ *
            (‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
                ((σ : ℂ) + (T : ℝ) * I)‖)
          ≤ M_K * (‖deriv riemannZeta ((σ : ℂ) + (T : ℝ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
                ((σ : ℂ) + (T : ℝ) * I)‖) :=
            mul_le_mul_of_nonneg_right hKbd h_W_nn
        _ ≤ M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) :=
            mul_le_mul_of_nonneg_left h_W_bd hM_K_nn
    have h_int : ‖∫ x : ℝ in (-1:ℝ)..2,
        K_2_fn t ((x : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ ≤
        (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * |2 - (-1:ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const h_inner
    have habs : |2 - (-1:ℝ)| = 3 := by norm_num
    rw [habs] at h_int
    have h_simp :
        (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * 3 =
          M_K * C_ζ * C_M * 3 * T ^ (N - 4) := by
      have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
        rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
        rw [← Real.rpow_sub hT_pos]
      have : M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) =
          M_K * C_ζ * C_M * (T ^ N / T ^ 4) := by ring
      rw [this, hdiv]; ring
    rw [h_simp] at h_int
    have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
      rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
    have hT_pow_ge : (Ktot / ε') ≤ T ^ (4 - N) := by
      have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
        Real.rpow_le_rpow hTbig_pos.le hT_ge_Tbig h4mN_pos.le
      have h_Tbig_pow : Tbig ^ (4 - N) = Ktot / ε' := by
        rw [hTbig_def, ← Real.rpow_mul hKε.le]
        have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
    have h_final : M_K * C_ζ * C_M * 3 * T ^ (N - 4) < ε' := by
      rw [h_pow_neg]
      have h_lt_K : M_K * C_ζ * C_M * 3 < Ktot := by rw [hKtot_def]; linarith
      have hstep1 : M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N)) <
          Ktot * (1 / T ^ (4 - N)) := by
        apply mul_lt_mul_of_pos_right h_lt_K
        exact div_pos one_pos hT_pow_pos
      have hstep2 : Ktot * (1 / T ^ (4 - N)) ≤ Ktot * (ε' / Ktot) := by
        apply mul_le_mul_of_nonneg_left _ hKtot_pos.le
        rw [div_le_div_iff₀ hT_pow_pos hKtot_pos]
        have h := (div_le_iff₀ hε').mp hT_pow_ge
        nlinarith
      have hstep3 : Ktot * (ε' / Ktot) = ε' := by field_simp
      calc M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N))
          < Ktot * (1 / T ^ (4 - N)) := hstep1
        _ ≤ Ktot * (ε' / Ktot) := hstep2
        _ = ε' := hstep3
    linarith [h_int]
  -- Bottom edge: same with `-T` and the `_neg_unconditional` Landau bound.
  have h_bot : ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖∫ x : ℝ in (-1:ℝ)..2,
          K_2_fn t ((x : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ < ε := by
    intro ε' hε'
    obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt, hLD⟩ :=
      full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional
    obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := uniform_pairMellin_quartic_target_neg β
    set Ktot : ℝ := M_K * C_ζ * C_M * 3 + 1 with hKtot_def
    have hKtot_pos : 0 < Ktot := by
      rw [hKtot_def]
      have h_pos : 0 ≤ M_K * C_ζ * C_M * 3 :=
        mul_nonneg (mul_nonneg (mul_nonneg hM_K_nn hC_ζ_pos.le) hC_M_nn) (by norm_num)
      linarith
    have h4mN_pos : 0 < 4 - N := by linarith
    have hKε : 0 < Ktot / ε' := div_pos hKtot_pos hε'
    set Tbig : ℝ := (Ktot / ε') ^ (1 / (4 - N)) with hTbig_def
    have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
    set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
    have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
    have hT_ge_Tζ : T₀_ζ ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hT_ge_TM : T₀_M ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    have hT_ge_Tbig : Tbig ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hT_ge_2 : (2 : ℝ) ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hT_pos : 0 < T := by linarith
    have h_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
        ‖K_2_fn t ((σ : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
          M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) := by
      intro σ hσ_mem
      have h_uIoc : Set.uIoc (-1:ℝ) 2 = Set.Ioc (-1:ℝ) 2 :=
        Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)
      rw [h_uIoc] at hσ_mem
      have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ_mem.1.le, hσ_mem.2⟩
      have hKbd : ‖K_2_fn t ((σ : ℂ) + (-T : ℝ) * I)‖ ≤ M_K := hM_K_bd σ (-T) hσ_Icc
      rw [norm_mul, Contour.weilIntegrand_norm_factored]
      have h_W_nn : 0 ≤ ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
            ((σ : ℂ) + (-T : ℝ) * I)‖ := by positivity
      have h_W_bd : ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
            ((σ : ℂ) + (-T : ℝ) * I)‖ ≤ C_ζ * T ^ N * (C_M / T ^ 4) := by
        have hζ_bd' : ‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ ≤ C_ζ * T ^ N := by
          have h_eq : ((-T : ℝ) : ℂ) = ((-T : ℂ)) := by push_cast; ring
          rw [h_eq]
          exact hLD T hT_ge_Tζ hGood σ hσ_Icc
        have hM_bd' : ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
            C_M / T ^ 4 := by
          have h_eq : ((-T : ℝ) : ℂ) = ((-T : ℂ)) := by push_cast; ring
          rw [h_eq]
          exact hM T hT_ge_TM σ hσ_Icc
        apply mul_le_mul hζ_bd' hM_bd' (norm_nonneg _)
        exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
      calc ‖K_2_fn t ((σ : ℂ) + (-T : ℝ) * I)‖ *
            (‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
              riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
                ((σ : ℂ) + (-T : ℝ) * I)‖)
          ≤ M_K * (‖deriv riemannZeta ((σ : ℂ) + (-T : ℝ) * I) /
              riemannZeta ((σ : ℂ) + (-T : ℝ) * I)‖ * ‖Contour.pairTestMellin β
                ((σ : ℂ) + (-T : ℝ) * I)‖) :=
            mul_le_mul_of_nonneg_right hKbd h_W_nn
        _ ≤ M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) :=
            mul_le_mul_of_nonneg_left h_W_bd hM_K_nn
    have h_int : ‖∫ x : ℝ in (-1:ℝ)..2,
        K_2_fn t ((x : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ ≤
        (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * |2 - (-1:ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const h_inner
    have habs : |2 - (-1:ℝ)| = 3 := by norm_num
    rw [habs] at h_int
    have h_simp :
        (M_K * (C_ζ * T ^ N * (C_M / T ^ 4))) * 3 =
          M_K * C_ζ * C_M * 3 * T ^ (N - 4) := by
      have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
        rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
        rw [← Real.rpow_sub hT_pos]
      have : M_K * (C_ζ * T ^ N * (C_M / T ^ 4)) =
          M_K * C_ζ * C_M * (T ^ N / T ^ 4) := by ring
      rw [this, hdiv]; ring
    rw [h_simp] at h_int
    have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
      rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
    have hT_pow_ge : (Ktot / ε') ≤ T ^ (4 - N) := by
      have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
        Real.rpow_le_rpow hTbig_pos.le hT_ge_Tbig h4mN_pos.le
      have h_Tbig_pow : Tbig ^ (4 - N) = Ktot / ε' := by
        rw [hTbig_def, ← Real.rpow_mul hKε.le]
        have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
    have h_final : M_K * C_ζ * C_M * 3 * T ^ (N - 4) < ε' := by
      rw [h_pow_neg]
      have h_lt_K : M_K * C_ζ * C_M * 3 < Ktot := by rw [hKtot_def]; linarith
      have hstep1 : M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N)) <
          Ktot * (1 / T ^ (4 - N)) := by
        apply mul_lt_mul_of_pos_right h_lt_K
        exact div_pos one_pos hT_pow_pos
      have hstep2 : Ktot * (1 / T ^ (4 - N)) ≤ Ktot * (ε' / Ktot) := by
        apply mul_le_mul_of_nonneg_left _ hKtot_pos.le
        rw [div_le_div_iff₀ hT_pow_pos hKtot_pos]
        have h := (div_le_iff₀ hε').mp hT_pow_ge
        nlinarith
      have hstep3 : Ktot * (ε' / Ktot) = ε' := by field_simp
      calc M_K * C_ζ * C_M * 3 * (1 / T ^ (4 - N))
          < Ktot * (1 / T ^ (4 - N)) := hstep1
        _ ≤ Ktot * (ε' / Ktot) := hstep2
        _ = ε' := hstep3
    linarith [h_int]
  -- Combine top + bottom via triangle.
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨T_top, hT_top_pos, hT_top⟩ := h_top (ε/2) hε2
  obtain ⟨T_bot, hT_bot_pos, hT_bot⟩ := h_bot (ε/2) hε2
  refine ⟨max T_top T_bot, lt_of_lt_of_le hT_top_pos (le_max_left _ _), fun T hT hGood => ?_⟩
  have hT_ge_top : T_top ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_bot : T_bot ≤ T := le_trans (le_max_right _ _) hT
  have h_top_bd := hT_top T hT_ge_top hGood
  have h_bot_bd := hT_bot T hT_ge_bot hGood
  calc ‖(∫ x : ℝ in (-1:ℝ)..2,
        K_2_fn t ((x : ℂ) + (-T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
       (∫ x : ℝ in (-1:ℝ)..2,
        K_2_fn t ((x : ℂ) + (T : ℝ) * I) *
        weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖
      ≤ ‖(∫ x : ℝ in (-1:ℝ)..2,
            K_2_fn t ((x : ℂ) + (-T : ℝ) * I) *
            weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I))‖ +
        ‖(∫ x : ℝ in (-1:ℝ)..2,
            K_2_fn t ((x : ℂ) + (T : ℝ) * I) *
            weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ :=
        norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
#print axioms ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_fn_horizontal_vanishes_target_holds
#print axioms ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_fn_vertical_at_two_integrable
#print axioms ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_fn_vertical_at_neg_one_integrable
#print axioms ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_fn_zeroSum_summable_holds
