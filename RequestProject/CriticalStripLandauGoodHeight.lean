import Mathlib
import RequestProject.CriticalStripLandau
import RequestProject.WeilFinalAssembly

/-!
# Pointwise-at-`goodHeight T` critical-strip Landau bound

Ports `ZD.criticalStripLandau` (which internally picks a separated good height
via `exists_good_height_for_near_window`) to a pointwise form that takes the
separation from the strengthened `goodHeight T` hypothesis
(`WeilFinalAssembly.lean:goodHeight`).

The strengthened `goodHeight T` carries, for every NTZ `ρ` with `|ρ.im − T| ≤ 1`,
a separation `goodHeightSepConstant / log T ≤ |ρ.im − T|` with a **fixed**
universal `goodHeightSepConstant` — so the resulting Landau constant `C` does
not depend on `T`, which is what the downstream uniform-bound target requires.
-/

open Complex Real Set Filter Topology MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open ZD ZD.WeilPositivity.Contour

set_option maxHeartbeats 4000000 in
/-- **Critical-strip Landau bound at a strong `goodHeight T`.**
Uniform `‖ζ'/ζ(σ+iT)‖ ≤ C · (log T)²` for `σ ∈ (0,1)`, `T ≥ 2`,
`goodHeight T`. -/
theorem criticalStripLandau_of_goodHeight :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Ioo (0:ℝ) 1, ∀ T : ℝ, 2 ≤ T → goodHeight T →
      ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2 := by
  -- Extract constants from dependencies.
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  obtain ⟨Cfar, hCfar_pos, hCfar_bd⟩ := xi_logDeriv_sub_far_bound
  obtain ⟨Cxi0, hCxi0_nn, hCxi0_bd⟩ := xi_logDeriv_norm_log_bound_local
  obtain ⟨CΓ, hCΓ_pos, hCΓ_bd⟩ :=
    ZD.UniformGammaR.gammaR_logDeriv_uniform_criticalStrip
  obtain ⟨Cw, hCw_pos, hCw_bd⟩ := nontrivialZeros_short_window_weighted_count_bound
  have hCsep_pos : 0 < goodHeightSepConstant := goodHeightSepConstant_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Cnear from the near-bound lemma with Csep = goodHeightSepConstant.
  set Cnear : ℝ := 5 * ((1 / goodHeightSepConstant) + 2) * Cw with hCnear_def
  have hCnear_pos : 0 < Cnear := by rw [hCnear_def]; positivity
  -- Universal constant.
  set C_total : ℝ :=
    (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 + Cnear + 1 with hC_total_def
  have hC_total_pos : 0 < C_total := by
    rw [hC_total_def]
    have h1 : 0 ≤ (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 := by
      apply div_nonneg _ hlog2_pos.le
      linarith [hCxi0_nn, hCfar_pos.le, hCΓ_pos.le, norm_nonneg A]
    linarith [hCnear_pos]
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro σ hσ T hT_ge_2 hGood
  -- Extract separation from goodHeight T at the +T side.
  have hsep : ∀ ρ ∈ NontrivialZeros, |ρ.im - T| ≤ 1 →
      goodHeightSepConstant / Real.log T ≤ |ρ.im - T| := by
    intro ρ hρ hnear
    exact (hGood.2 ρ hρ).1 hnear
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT_ge_2
  have hlogT_sq_pos : 0 < (Real.log T) ^ 2 := by positivity
  -- Near-bound at this T via the `of_sep` helper with T₀ = T and T_mem trivial.
  have hT_mem_self : T ∈ Set.Icc T (T + 1) := ⟨le_refl _, by linarith⟩
  have hNear_bd :
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ Cnear * (Real.log T) ^ 2 := by
    simpa [shortWindowFinset, Cnear, hCnear_def] using
      xi_logDeriv_sub_near_bound_of_sep
        ⟨hσ.1.le, by linarith [hσ.2]⟩ hT_ge_2 hT_mem_self hCsep_pos hCw_pos hsep
        (fun U hU => by simpa [shortWindowFinset] using hCw_bd U hU)
  -- Far-bound at this T.
  have hFar_bd :
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ Cfar * Real.log T :=
    hCfar_bd σ ⟨hσ.1.le, by linarith [hσ.2]⟩ T hT_ge_2
  -- Set up s, s₀.
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I with hs₀_def
  have hs_re : s.re = σ := by simp [hs_def]
  have hs_im : s.im = T := by simp [hs_def]
  have hs₀_re : s₀.re = 2 := by simp [hs₀_def]
  have hs₀_im : s₀.im = T := by simp [hs₀_def]
  have hσ_pos : 0 < σ := hσ.1
  have hσ_lt : σ < 1 := hσ.2
  have hs_ne_0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hs_re] at this; simp at this; linarith
  have hs_ne_1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hs_re] at this; simp at this; linarith
  -- s ∉ NontrivialZeros via goodHeight contour avoidance at +T.
  have hs_notMem : s ∉ NontrivialZeros := by
    intro hmem
    have : s.im ≠ T := (hGood.1 s hmem).1
    exact this hs_im
  have hs_ne : s.re ∉ Set.Ioo (0:ℝ) 1 ∨ riemannZeta s ≠ 0 := by
    by_cases hz : riemannZeta s = 0
    · left
      intro hmem
      exact hs_notMem ⟨hmem.1, hmem.2, hz⟩
    · right; exact hz
  have hζ_s_ne : riemannZeta s ≠ 0 := by
    rcases hs_ne with hmem | hne
    · exfalso; exact hmem (by rw [hs_re]; exact hσ)
    · exact hne
  have hΓ_s_ne : Complex.Gammaℝ s ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    show (0:ℝ) < s.re
    rw [hs_re]; exact hσ_pos
  have hs₀_notMem : s₀ ∉ NontrivialZeros := by
    intro hmem
    have h2 : (2 : ℝ) < 1 := by
      have : s₀.re < 1 := hmem.2.1
      rw [hs₀_re] at this; exact this
    linarith
  -- Γℝ bound.
  have h_Γ_s_bd : ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * Real.log T := by
    simpa [hs_def] using hCΓ_bd σ hσ T hT_ge_2
  -- Apply short-window decomposition at s and s₀.
  obtain ⟨A', hA'⟩ := xi_logDeriv_short_window_decomp
  have hdecomp_s := hA' s hs_notMem
  have hdecomp_s₀ := hA' s₀ hs₀_notMem
  have h_im_eq : s.im = s₀.im := by rw [hs_im, hs₀_im]
  have hdecomp_s₀' :
      deriv riemannXi s₀ / riemannXi s₀ =
        A' +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    rw [h_im_eq]; exact hdecomp_s₀
  have h_xi_diff :
      deriv riemannXi s / riemannXi s - deriv riemannXi s₀ / riemannXi s₀ =
        ((∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
         (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val))) +
        ((∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
         (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val))) := by
    rw [hdecomp_s, hdecomp_s₀']; ring
  -- Summability of near/far-subtype restrictions.
  have h_summ_near_s : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_summ_near_s₀ : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs₀_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_summ_far_s : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_summ_far_s₀ : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs₀_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_near_sub :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    rw [← Summable.tsum_sub h_summ_near_s h_summ_near_s₀]
    apply tsum_congr; intro ρ; ring
  have h_far_sub :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    rw [← Summable.tsum_sub h_summ_far_s h_summ_far_s₀]
    apply tsum_congr; intro ρ; ring
  -- ξ'/ξ(s) = ξ'/ξ(s₀) + near_diff + far_diff
  have h_xi_s_eq :
      deriv riemannXi s / riemannXi s =
        deriv riemannXi s₀ / riemannXi s₀ +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))) +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))) := by
    have h1 := h_xi_diff
    rw [h_near_sub, h_far_sub] at h1
    linear_combination h1
  rw [← hs_im] at hNear_bd hFar_bd
  -- Convert Real.log s.im back to Real.log T in the coefficients for linarith.
  have h_log_sim : Real.log s.im = Real.log T := by rw [hs_im]
  rw [h_log_sim] at hNear_bd hFar_bd
  -- ‖ξ'/ξ(s₀)‖ ≤ Cxi0 · log T.
  have h_xi_s₀_bd : ‖deriv riemannXi s₀ / riemannXi s₀‖ ≤ Cxi0 * Real.log T := by
    simpa [hs₀_def] using hCxi0_bd T hT_ge_2
  -- Step 1: Bound ‖ξ'/ξ(s)‖.
  have h_xi_s_norm : ‖deriv riemannXi s / riemannXi s‖ ≤
      Cxi0 * Real.log T + Cnear * (Real.log T) ^ 2 + Cfar * Real.log T := by
    rw [h_xi_s_eq]
    have h1 := norm_add_le (deriv riemannXi s₀ / riemannXi s₀ +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))))
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)))
    have h2 := norm_add_le (deriv riemannXi s₀ / riemannXi s₀)
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)))
    linarith [h1, h2, h_xi_s₀_bd, hNear_bd, hFar_bd]
  -- Step 2: Tighter bounds on 1/s and 1/(s-1): use ‖s‖ ≥ T, ‖s-1‖ ≥ T.
  have h_s_norm_ge_T : T ≤ ‖s‖ := by
    have : T = |s.im| := by rw [hs_im]; exact (abs_of_pos hT_pos).symm
    rw [this]; exact Complex.abs_im_le_norm s
  have h_sm1_norm_ge_T : T ≤ ‖s - 1‖ := by
    have him : (s - 1).im = T := by simp [hs_def]
    have : T = |(s - 1).im| := by rw [him]; exact (abs_of_pos hT_pos).symm
    rw [this]; exact Complex.abs_im_le_norm (s - 1)
  have h_inv_s_T : ‖(1 : ℂ) / s‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hT_pos h_s_norm_ge_T
  have h_inv_sm1_T : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hT_pos h_sm1_norm_ge_T
  -- Step 3: logT ≤ logT²/log 2.
  have h_logT_absorb : Real.log T ≤ (Real.log T) ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    nlinarith [hlogT_ge_log2]
  -- Step 4: 1/T ≤ logT²/log 2.
  have h_inv_T_absorb : 1 / T ≤ (Real.log T) ^ 2 / Real.log 2 := by
    have h_inv_T_le_half : 1 / T ≤ 1 / 2 := by gcongr
    have h_half_le_logT : 1 / 2 ≤ Real.log T := by
      have := Real.log_two_gt_d9
      linarith
    exact le_trans h_inv_T_le_half (le_trans h_half_le_logT h_logT_absorb)
  -- Step 5: Use generalized H9 to connect ξ'/ξ → ζ'/ζ.
  have hζ_s_eq :
      deriv riemannZeta s / riemannZeta s =
        deriv riemannXi s / riemannXi s -
          1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s :=
    riemannZeta_logDeriv_eq_generalized s hs_ne_0 hs_ne_1 hζ_s_ne hΓ_s_ne
  -- Step 6: Triangle inequality for ζ'/ζ.
  have h_zeta_tri : ‖deriv riemannXi s / riemannXi s - 1 / s - 1 / (s - 1) -
      logDeriv Complex.Gammaℝ s‖ ≤
      ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
        ‖logDeriv Complex.Gammaℝ s‖ := by
    have h_triangle : ∀ a b c d : ℂ, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      exact fun a b c d => by linarith [norm_sub_le a b, norm_sub_le (a - b) c, norm_sub_le (a - b - c) d]
    apply h_triangle
  -- Step 7: Final assembly.
  rw [hζ_s_eq]
  have h_total : ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C_total * (Real.log T) ^ 2 := by
    have hbd1 : ‖(1 : ℂ) / s‖ ≤ (Real.log T) ^ 2 / Real.log 2 :=
      le_trans h_inv_s_T h_inv_T_absorb
    have hbd2 : ‖(1 : ℂ) / (s - 1)‖ ≤ (Real.log T) ^ 2 / Real.log 2 :=
      le_trans h_inv_sm1_T h_inv_T_absorb
    have hbd3 : ‖deriv riemannXi s / riemannXi s‖ ≤
        ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by
      calc ‖deriv riemannXi s / riemannXi s‖
          ≤ Cxi0 * Real.log T + Cnear * (Real.log T) ^ 2 + Cfar * Real.log T := h_xi_s_norm
        _ ≤ Cxi0 * ((Real.log T) ^ 2 / Real.log 2) +
            Cnear * (Real.log T) ^ 2 +
            Cfar * ((Real.log T) ^ 2 / Real.log 2) := by
          nlinarith [h_logT_absorb, hCxi0_nn, hCfar_pos.le]
        _ = ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by ring
    have hbd4 : ‖logDeriv Complex.Gammaℝ s‖ ≤
        CΓ / Real.log 2 * (Real.log T) ^ 2 := by
      calc ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * Real.log T := h_Γ_s_bd
        _ ≤ CΓ * ((Real.log T) ^ 2 / Real.log 2) := by
          nlinarith [h_logT_absorb, hCΓ_pos]
        _ = CΓ / Real.log 2 * (Real.log T) ^ 2 := by ring
    calc ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖logDeriv Complex.Gammaℝ s‖
        ≤ ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 +
          (Real.log T) ^ 2 / Real.log 2 +
          (Real.log T) ^ 2 / Real.log 2 +
          CΓ / Real.log 2 * (Real.log T) ^ 2 := by linarith [hbd1, hbd2, hbd3, hbd4]
      _ = ((Cxi0 + Cfar + CΓ + 2) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by ring
      _ ≤ C_total * (Real.log T) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hlogT_sq_pos.le
          rw [hC_total_def]
          have hA_nn := norm_nonneg A
          have h_extra : 0 ≤ ‖A‖ / Real.log 2 := div_nonneg hA_nn hlog2_pos.le
          have h_sum : (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 =
              (Cxi0 + Cfar + CΓ + 2) / Real.log 2 + ‖A‖ / Real.log 2 := by ring
          linarith [h_extra, h_sum]
  linarith [h_zeta_tri, h_total]

#print axioms criticalStripLandau_of_goodHeight

end FinalAssembly
end WeilPositivity
end ZD

end
