import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.ArchOperatorBound
import RequestProject.WeilReflectedPrimeVanishingWeilside
import RequestProject.WeilLandauBound

/-!
# Reflected-prime single-cosh pair expansion at σ = 2
-/

open Complex Set Filter MeasureTheory
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace ReflectedPrimeCoshExpansion

open ZD.WeilPositivity.Contour.ReflectedPrimeVanishing

/-! ## Definition — single-cosh reflected-prime integral

Pair `ζ'/ζ(1−(2+it))` against `coshGaussMellin c (2+it)` instead of the
pair-test Mellin `pairTestMellin β (2+it)`. The five values
`c ∈ {2β−π/3, 2−π/3−2β, 1−π/3, 2β−1, 0}` assemble to `∫ reflected β 2` by
linearity (L3 below).
-/

/-- Single-cosh version of `∫ t, reflectedPrimeIntegrand β 2 t dt`. -/
def reflectedPrimeSingleCosh (c : ℝ) : ℂ :=
  ∫ t : ℝ,
    deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
    Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)

/-! ## L1 — Integrability of the single-cosh reflected-prime integrand

The `ζ'/ζ(1 − s)` factor on `Re s = 2` is bounded (it's the log-derivative
of ζ at `Re = −1`, meromorphic with a simple structure via the FE). The
`coshGaussMellin c (2+it)` factor has `O(1/(1+t²))` quadratic decay via
IBP×2. Combined: integrable.

Route (mirroring `h1_arch_coshGaussMellin_integrable` at
`WeilReflectedPrimeVanishingWeilside.lean:569`): use the quadratic-decay
bound on `coshGaussMellin c (2+it)` together with a pointwise bound on the
`ζ'/ζ(1−(2+it))` factor (polynomial in `log|t|` is enough; even a crude
`(1 + |t|)^N` majorant for small `N` suffices, paralleling
`arch_subunit_bound_at_two`).
-/

/-- **L1**: integrability of the single-cosh reflected-prime integrand on ℝ. -/
theorem reflectedPrimeSingleCosh_integrable (c : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C_a, N, hC_a_nn, hN_nn, hN_lt_1, h_arch_bd⟩ :=
    arch_subunit_bound_at_two
  obtain ⟨C_ζ, hC_ζ_nn, h_zeta_bd⟩ := landau_logDeriv_bound_at_two
  obtain ⟨K, hK_nn, h_cosh_bd⟩ := coshGaussMellin_quadratic_bound_at_two c
  set C_tot : ℝ := (C_ζ + C_a) * K with hC_tot_def
  set α : ℝ := (N - 2) / 2 with hα_def
  have h_r_gt_one : (1 : ℝ) < 2 - N := by linarith
  have h_rpow_integrable :
      MeasureTheory.Integrable
        (fun t : ℝ => (1 + ‖t‖^2)^(-(2 - N) / 2)) MeasureTheory.volume := by
    apply integrable_rpow_neg_one_add_norm_sq
    · rw [Module.finrank_self]; exact_mod_cast h_r_gt_one
  have h_rpow_integrable' :
      MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)^α) := by
    refine h_rpow_integrable.congr (MeasureTheory.ae_of_all _ ?_)
    intro t
    show (1 + ‖t‖^2)^(-(2 - N) / 2) = (1 + t^2)^α
    have h_norm_sq : ‖t‖^2 = t^2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [h_norm_sq]; congr 1; rw [hα_def]; ring
  have h_majorant_int :
      MeasureTheory.Integrable
        (fun t : ℝ => C_tot * (2^(N/2) * (1 + t^2)^α)) := by
    exact (h_rpow_integrable'.const_mul (2^(N/2))).const_mul C_tot
  -- Non-vanishing conditions at s = 2+it.
  have h_s_ne_zero : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h; have := congr_arg Complex.re h; simp at this
  have h_s_ne_one : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h; have := congr_arg Complex.re h; simp at this
  have h_zeta_s_ne : ∀ t : ℝ, riemannZeta ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t; apply riemannZeta_ne_zero_of_one_lt_re; simp
  have h_1s_ne_zero : ∀ t : ℝ, (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
    intro t h; have := congr_arg Complex.re h; simp at this; linarith
  have h_gammaR_s_ne : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := by
    intro t h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have := congr_arg Complex.re hn; simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h_gammaR_1s_ne : ∀ t : ℝ, (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0 := by
    intro t h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have := congr_arg Complex.re hn; simp at this
    rcases n with _ | k <;> push_cast at this <;> linarith
  have h_zeta_1s_ne : ∀ t : ℝ, riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
    intro t h
    have h_xi_s : completedRiemannZeta ((2 : ℂ) + (t : ℂ) * I) =
        ((2 : ℂ) + (t : ℂ) * I).Gammaℝ * riemannZeta ((2 : ℂ) + (t : ℂ) * I) :=
      completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta (h_s_ne_zero t) (h_gammaR_s_ne t)
    have h_xi_ne : completedRiemannZeta ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      rw [h_xi_s]; exact mul_ne_zero (h_gammaR_s_ne t) (h_zeta_s_ne t)
    have h_xi_1s : completedRiemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) =
        completedRiemannZeta ((2 : ℂ) + (t : ℂ) * I) :=
      completedRiemannZeta_one_sub _
    have h_xi_1s_ne : completedRiemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
      rw [h_xi_1s]; exact h_xi_ne
    have h_zeta_1s_eq : riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) =
        completedRiemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ :=
      riemannZeta_def_of_ne_zero (h_1s_ne_zero t)
    rw [h_zeta_1s_eq] at h
    exact absurd (div_eq_zero_iff.mp h) (not_or_intro h_xi_1s_ne (h_gammaR_1s_ne t))
  -- Pointwise bound on the reflected kernel via zeta_logDeriv_arch_form.
  have h_reflected_bd : ∀ t : ℝ,
      ‖deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I))‖ ≤
      (C_ζ + C_a) * (1 + |t|)^N := by
    intro t
    set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs_def
    have h_arch := zeta_logDeriv_arch_form (h_s_ne_zero t) (h_s_ne_one t)
      (h_zeta_s_ne t) (h_zeta_1s_ne t) (h_gammaR_s_ne t) (h_gammaR_1s_ne t)
    have h_eq : deriv riemannZeta (1 - s) / riemannZeta (1 - s) =
        -(deriv riemannZeta s / riemannZeta s) -
        (deriv Complex.Gammaℝ s / s.Gammaℝ +
          deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ) := by
      linear_combination -h_arch
    rw [h_eq]
    have h_tri : ‖-(deriv riemannZeta s / riemannZeta s) -
        (deriv Complex.Gammaℝ s / s.Gammaℝ +
          deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ)‖ ≤
      ‖deriv riemannZeta s / riemannZeta s‖ +
      ‖deriv Complex.Gammaℝ s / s.Gammaℝ +
        deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := by
      calc ‖-(deriv riemannZeta s / riemannZeta s) -
              (deriv Complex.Gammaℝ s / s.Gammaℝ +
                deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ)‖
          ≤ ‖-(deriv riemannZeta s / riemannZeta s)‖ +
            ‖deriv Complex.Gammaℝ s / s.Gammaℝ +
              deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := norm_sub_le _ _
        _ = ‖deriv riemannZeta s / riemannZeta s‖ +
            ‖deriv Complex.Gammaℝ s / s.Gammaℝ +
              deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := by rw [norm_neg]
    have h_zeta_t := h_zeta_bd t
    have h_arch_t : ‖deriv Complex.Gammaℝ s / s.Gammaℝ +
        deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ ≤ C_a * (1 + |t|)^N := by
      have := h_arch_bd t; push_cast at this; exact this
    have h_base_nn : (0 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h_base_ge_one : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h_rpow_ge_one : (1 : ℝ) ≤ (1 + |t|)^N :=
      Real.one_le_rpow h_base_ge_one hN_nn
    calc ‖-(deriv riemannZeta s / riemannZeta s) -
            (deriv Complex.Gammaℝ s / s.Gammaℝ +
              deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ)‖
        ≤ ‖deriv riemannZeta s / riemannZeta s‖ +
          ‖deriv Complex.Gammaℝ s / s.Gammaℝ +
            deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := h_tri
      _ ≤ C_ζ + C_a * (1 + |t|)^N := by linarith
      _ ≤ C_ζ * (1 + |t|)^N + C_a * (1 + |t|)^N := by
          have : C_ζ ≤ C_ζ * (1 + |t|)^N := le_mul_of_one_le_right hC_ζ_nn h_rpow_ge_one
          linarith
      _ = (C_ζ + C_a) * (1 + |t|)^N := by ring
  -- Pointwise bound on the full integrand.
  have h_ptwise : ∀ t : ℝ,
      ‖deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      C_tot * (2^(N/2) * (1 + t^2)^α) := by
    intro t
    rw [norm_mul]
    have h_refl_t := h_reflected_bd t
    have h_cosh_t := h_cosh_bd t
    have h_cosh_nn : (0 : ℝ) ≤ ‖Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ :=
      norm_nonneg _
    have h_refl_nn : (0 : ℝ) ≤ (C_ζ + C_a) * (1 + |t|)^N :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [abs_nonneg t]) _)
    have h_1plus_pos : (0 : ℝ) < 1 + t^2 := by positivity
    have h_prod_bd :
        ‖deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I))‖ *
          ‖Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)‖ ≤
        (C_ζ + C_a) * (1 + |t|)^N * (K / (1 + t^2)) :=
      mul_le_mul h_refl_t h_cosh_t h_cosh_nn h_refl_nn
    have h_rearrange : (C_ζ + C_a) * (1 + |t|)^N * (K / (1 + t^2)) =
        C_tot * ((1 + |t|)^N / (1 + t^2)) := by
      rw [hC_tot_def]; ring
    rw [h_rearrange] at h_prod_bd
    -- (1+|t|)^N / (1+t²) ≤ 2^(N/2) * (1+t²)^α using (1+|t|)² ≤ 2(1+t²).
    have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
    have h_base_nn : (0 : ℝ) ≤ 1 + |t| := by linarith
    have h_t_sq_nn : (0 : ℝ) ≤ 1 + t^2 := by positivity
    have h_one_plus_abs_sq : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
      have h_t_sq : |t|^2 = t^2 := sq_abs t
      nlinarith [sq_nonneg (|t| - 1)]
    have hN_half_nn : (0 : ℝ) ≤ N / 2 := by linarith
    have h_pow_bd : (1 + |t|)^N ≤ 2^(N/2) * (1 + t^2)^(N/2) := by
      have h_lhs_eq : ((1 + |t|)^2)^(N/2) = (1 + |t|)^N := by
        rw [show ((1 + |t|)^2 : ℝ) = (1 + |t|)^(2 : ℕ) from rfl]
        rw [← Real.rpow_natCast (1 + |t|) 2]
        rw [← Real.rpow_mul h_base_nn]
        congr 1; ring
      have h_rhs_eq : (2 * (1 + t^2))^(N/2) = 2^(N/2) * (1 + t^2)^(N/2) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) h_t_sq_nn]
      rw [← h_lhs_eq, ← h_rhs_eq]
      exact Real.rpow_le_rpow (by positivity) h_one_plus_abs_sq hN_half_nn
    have h_ratio_bd : (1 + |t|)^N / (1 + t^2) ≤ 2^(N/2) * (1 + t^2)^α := by
      rw [div_le_iff₀ h_1plus_pos]
      have : 2^(N/2) * (1 + t^2)^α * (1 + t^2) = 2^(N/2) * (1 + t^2)^(N/2) := by
        rw [hα_def, show (N/2 : ℝ) = (N-2)/2 + 1 by ring,
            Real.rpow_add_one (ne_of_gt h_1plus_pos) ((N-2)/2)]
        ring
      rw [this]; exact h_pow_bd
    calc _ ≤ C_tot * ((1 + |t|)^N / (1 + t^2)) := h_prod_bd
      _ ≤ C_tot * (2^(N/2) * (1 + t^2)^α) := by
          apply mul_le_mul_of_nonneg_left h_ratio_bd
          rw [hC_tot_def]; exact mul_nonneg (by linarith) hK_nn
  -- Measurability.
  have h_cont_refl : Continuous (fun t : ℝ =>
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I))) := by
    have h_line : Continuous (fun t : ℝ => 1 - ((2 : ℂ) + (t : ℂ) * I)) := by fun_prop
    have h_in : ∀ t : ℝ, (1 - ((2 : ℂ) + (t : ℂ) * I)) ∈ ({1}ᶜ : Set ℂ) := by
      intro t hh
      have hre := congr_arg Complex.re hh
      simp at hre
    have h_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    have h_an_on : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      h_diff_on.analyticOnNhd isOpen_compl_singleton
    have h_dζ_diff_on : DifferentiableOn ℂ (deriv riemannZeta) ({1}ᶜ : Set ℂ) :=
      fun z hz => ((h_an_on z hz).deriv).differentiableAt.differentiableWithinAt
    have h_zeta_cont : Continuous (fun t : ℝ => riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I))) :=
      h_diff_on.continuousOn.comp_continuous h_line h_in
    have h_dζ_cont : Continuous
        (fun t : ℝ => deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I))) :=
      h_dζ_diff_on.continuousOn.comp_continuous h_line h_in
    exact h_dζ_cont.div h_zeta_cont (fun t => h_zeta_1s_ne t)
  have h_cont_cosh : Continuous (fun t : ℝ =>
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) := by
    have h_diff_on : DifferentiableOn ℂ (Contour.coshGaussMellin c) {s : ℂ | 0 < s.re} := by
      intro s hs
      exact (Contour.coshGaussMellin_differentiableAt c hs).differentiableWithinAt
    have h_line_cont : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_cont_on := h_diff_on.continuousOn
    have h_map : ∀ t : ℝ, ((2 : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | 0 < s.re} := by
      intro t; simp
    exact h_cont_on.comp_continuous h_line_cont h_map
  have h_meas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
      Contour.coshGaussMellin c ((2 : ℂ) + (t : ℂ) * I)) MeasureTheory.volume :=
    (h_cont_refl.mul h_cont_cosh).aestronglyMeasurable
  exact h_majorant_int.mono' h_meas (MeasureTheory.ae_of_all _ (fun t => h_ptwise t))

/-! ## L3 — Five-term pair expansion

By `Contour.pairTestMellin_cosh_expansion`, `pairTestMellin β (2+it)` is a
fixed linear combination of `coshGaussMellin cᵢ (2+it)` for five explicit
coefficients `cᵢ(β)`. Multiplying by the reflected factor `ζ'/ζ(1−(2+it))`
and integrating (using L1 for each `cᵢ`) gives the pair expansion.

Parallels `arch_integral_cosh_expansion_at_two` at
`WeilReflectedPrimeVanishingWeilside.lean:805`.
-/

/-- **L3**: five-term pair expansion of the reflected-prime integral. -/
theorem reflectedPrime_integral_cosh_expansion_at_two (β : ℝ) :
    (∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t) =
      (1/2 : ℂ) * reflectedPrimeSingleCosh (2 * β - Real.pi / 3) +
      (1/2 : ℂ) * reflectedPrimeSingleCosh (2 - Real.pi / 3 - 2 * β) -
      reflectedPrimeSingleCosh (1 - Real.pi / 3) -
      reflectedPrimeSingleCosh (2 * β - 1) +
      reflectedPrimeSingleCosh 0 := by
  set K_t : ℝ → ℂ := fun t : ℝ =>
    deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) with hK_def
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
  have hf₁ := reflectedPrimeSingleCosh_integrable (2*β - Real.pi/3)
  have hf₂ := reflectedPrimeSingleCosh_integrable (2 - Real.pi/3 - 2*β)
  have hf₃ := reflectedPrimeSingleCosh_integrable (1 - Real.pi/3)
  have hf₄ := reflectedPrimeSingleCosh_integrable (2*β - 1)
  have hf₅ := reflectedPrimeSingleCosh_integrable 0
  -- Pointwise expansion of the integrand.
  have h_ptwise : ∀ t : ℝ,
      Contour.reflectedPrimeIntegrand β 2 t =
        ((1/2 : ℂ) * f₁ t + (1/2 : ℂ) * f₂ t) + (-f₃ t + -f₄ t) + f₅ t := by
    intro t
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
      · have h_cv := Contour.mellinConvergent_coshGauss 0 h_re
        have h_eq : (fun u : ℝ => ((Real.cosh (0 * u) * Real.exp (-2 * u ^ 2) : ℝ) : ℂ)) =
            (fun u : ℝ => ((Real.exp (-2 * u ^ 2) : ℝ) : ℂ)) := by
          funext u; rw [zero_mul, Real.cosh_zero, one_mul]
        rw [h_eq] at h_cv
        exact h_cv
    have h_g_eq : Contour.gaussMellin ((2 : ℂ) + (t : ℂ) * I) =
        Contour.coshGaussMellin 0 ((2 : ℂ) + (t : ℂ) * I) :=
      (Contour.coshGaussMellin_zero _).symm
    rw [h_g_eq] at h_expand
    show _ = _
    unfold Contour.reflectedPrimeIntegrand
    rw [show ((2:ℝ):ℂ) = (2:ℂ) from h_cast]
    rw [h_expand]
    simp only [f₁, f₂, f₃, f₄, f₅, K_t]
    ring
  have h_fn_eq : Contour.reflectedPrimeIntegrand β 2 = fun t : ℝ =>
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
  rw [show (∫ a : ℝ, (1/2 : ℂ) * f₁ a) = (1/2 : ℂ) * ∫ a : ℝ, f₁ a from
    MeasureTheory.integral_const_mul _ _]
  rw [show (∫ a : ℝ, (1/2 : ℂ) * f₂ a) = (1/2 : ℂ) * ∫ a : ℝ, f₂ a from
    MeasureTheory.integral_const_mul _ _]
  show ((1/2 : ℂ) * (∫ t : ℝ, f₁ t) + (1/2 : ℂ) * ∫ t : ℝ, f₂ t) +
      (-(∫ t : ℝ, f₃ t) + -(∫ t : ℝ, f₄ t)) + ∫ t : ℝ, f₅ t =
    (1/2 : ℂ) * reflectedPrimeSingleCosh (2 * β - Real.pi / 3) +
      (1/2 : ℂ) * reflectedPrimeSingleCosh (2 - Real.pi / 3 - 2 * β) -
      reflectedPrimeSingleCosh (1 - Real.pi / 3) -
      reflectedPrimeSingleCosh (2 * β - 1) +
      reflectedPrimeSingleCosh 0
  unfold reflectedPrimeSingleCosh
  show ((1/2 : ℂ) * (∫ t : ℝ, f₁ t) + (1/2 : ℂ) * ∫ t : ℝ, f₂ t) +
      (-(∫ t : ℝ, f₃ t) + -(∫ t : ℝ, f₄ t)) + ∫ t : ℝ, f₅ t =
    (1/2 : ℂ) * (∫ t : ℝ, f₁ t) +
      (1/2 : ℂ) * (∫ t : ℝ, f₂ t) -
      (∫ t : ℝ, f₃ t) -
      (∫ t : ℝ, f₄ t) +
      (∫ t : ℝ, f₅ t)
  ring
/-
theorem reflectedPrime_integral_vanishes_at_two (β : ℝ) :
    ∫ t : ℝ, Contour.reflectedPrimeIntegrand β 2 t = 0 := by
  sorry

theorem archPair_eq_primePair_at_two_proved (β : ℝ) :
    ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β :=
  (ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes β).mpr
    (reflectedPrime_integral_vanishes_at_two β)
-/
end ReflectedPrimeCoshExpansion
end Contour
end WeilPositivity
end ZD

end
