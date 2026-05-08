import Mathlib
import RequestProject.CauchyKPairTestEngineering
import RequestProject.DigammaVerticalBound

/-!
# Pole-series swap (Step 14)

For each of the two positive-real-part half-arg digamma transforms

```
D_L(β, α) = (1/2) · ∫ y, exp(iyα) · ψ(1/2 + iy/2) · M(β, -1+iy) dy,
D_R(β, α) = (1/2) · ∫ y, exp(iyα) · ψ((2 - iy)/2) · M(β, -1+iy) dy,
```

apply the project's `digamma_eq_series` (axiom-clean):

```
ψ(z) = -γ + Σ_{k≥0} (1/(k+1) - 1/(k + z)),    Re z > 0
```

and discharge the termwise-integration swap to obtain

```
D_L(β, α) = -γ/2 · constantLogPiShiftedArchIntegral β α + Σ' k, digammaPoleKernelLeft k β α,
D_R(β, α) = -γ/2 · constantLogPiShiftedArchIntegral β α + Σ' k, digammaPoleKernelRight k β α.
```

These are gates 4 and 5 of the `shiftedArchIntegral` closed-form audit.  Once
discharged, combined with the three integrability gates already closed in
`CauchyKPairTestEngineering.lean`, the unconditional arch theorem follows.

Index conventions remain DISTINCT:
- Left tower: `k + 1/2 + iy/2`.
- Right tower: `k + 1 - iy/2`.

Do NOT merge them.  The trivial-zero residue audit downstream forces the
correct reindexing.

Axiom footprint target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity

/-! ### Conjugation symmetry helpers

Local rederivation of the conjugation identity for `pairTestMellin`, used to
symmetrise the quartic decay bound across the imaginary axis. -/

private theorem pairTestMellin_conj_local_swap (β : ℝ) (s : ℂ) :
    Contour.pairTestMellin β (star s) = star (Contour.pairTestMellin β s) := by
  unfold Contour.pairTestMellin mellin
  rw [show star (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)) =
      ∫ t : ℝ in Set.Ioi 0,
        star ((t : ℂ) ^ (s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)) from
    (integral_conj (f := fun t : ℝ =>
      (t : ℂ) ^ (s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ))).symm]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht_pos : 0 < t := ht
  have ht_arg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht_pos.le]
    exact ne_of_lt Real.pi_pos
  show (t : ℂ) ^ (star s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)
      = star ((t : ℂ) ^ (s - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ))
  rw [smul_eq_mul, smul_eq_mul, star_mul']
  have h_real_conj : star ((pair_cosh_gauss_test β t : ℝ) : ℂ)
      = ((pair_cosh_gauss_test β t : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [h_real_conj]
  congr 1
  rw [show star s - 1 = star (s - 1) from by rw [star_sub, star_one]]
  show (t : ℂ) ^ (starRingEnd ℂ (s - 1)) = starRingEnd ℂ ((t : ℂ) ^ (s - 1))
  rw [Complex.cpow_conj _ _ ht_arg, Complex.conj_ofReal]

private lemma mellin_left_edge_norm_sym_swap (β : ℝ) (y : ℝ) :
    ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ =
    ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)‖ := by
  have h_star : ((-1 : ℝ) : ℂ) + (y : ℂ) * I =
      star (((-1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [h_star, pairTestMellin_conj_local_swap, norm_star]

/-! ### Integrability of `(1+|y|)·‖M(β,-1+iy)‖`

Combines the global quadratic majorant on `|y| ≤ 2` with the quartic decay
on `|y| ≥ 2` (via conjugation symmetry on the negative side) to dominate
the moment by `K · (1+y²)⁻¹`. -/

private theorem mellin_left_edge_one_plus_abs_integrable_swap (β : ℝ) :
    Integrable (fun y : ℝ => (1 + |y|) *
      ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
  obtain ⟨C, hC_nn, h_quartic⟩ :=
    HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended β
  have h_cont : Continuous (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    PairTestIdentity.pairTestMellin_left_edge_continuous β
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (-2:ℝ)) (b := 2)) h_cont.norm.continuousOn
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  have hM_apply : ∀ y : ℝ, |y| ≤ 2 →
      ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M := by
    intro y hy
    have h := hM y (by simp [Set.mem_Icc, abs_le.mp hy])
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h
    exact h
  set K : ℝ := max (15 * M) (4 * C) with hK_def
  have hK_nn : 0 ≤ K := le_max_of_le_left (by linarith)
  have h_dom_int : Integrable (fun y : ℝ => K * (1 + y^2)⁻¹) :=
    (integrable_inv_one_add_sq).const_mul K
  apply h_dom_int.mono'
  · apply Continuous.aestronglyMeasurable; fun_prop
  · refine MeasureTheory.ae_of_all _ fun y => ?_
    have h_pos : 0 < 1 + y^2 := by positivity
    have h_inv_nn : 0 ≤ (1 + y^2)⁻¹ := inv_nonneg.mpr h_pos.le
    rw [Real.norm_of_nonneg (by positivity)]
    rcases le_or_gt |y| 2 with h_y | h_y
    · have h_pair_le := hM_apply y h_y
      have h_one_plus_nn : 0 ≤ 1 + |y| := by linarith [abs_nonneg y]
      have h_one_plus_le3 : 1 + |y| ≤ 3 := by linarith
      have h_step1 : (1 + |y|) *
          ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 3 * M :=
        calc (1 + |y|) * _
            ≤ (1 + |y|) * M := mul_le_mul_of_nonneg_left h_pair_le h_one_plus_nn
          _ ≤ 3 * M := mul_le_mul_of_nonneg_right h_one_plus_le3 hM_nn
      have h_t_sq_le : y^2 ≤ 4 := by have := sq_abs y; nlinarith
      have h_1plus_le : 1 + y^2 ≤ 5 := by linarith
      have h_inv_ge : (1:ℝ)/5 ≤ (1 + y^2)⁻¹ := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5), le_inv_mul_iff₀ h_pos]; linarith
      have h_15M_le_K : 15 * M ≤ K := le_max_left _ _
      calc (1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ 3 * M := h_step1
        _ = 15 * M * (1/5) := by ring
        _ ≤ 15 * M * (1 + y^2)⁻¹ := mul_le_mul_of_nonneg_left h_inv_ge (by linarith)
        _ ≤ K * (1 + y^2)⁻¹ := mul_le_mul_of_nonneg_right h_15M_le_K h_inv_nn
    · have h_abs_t_ge : 2 ≤ |y| := h_y.le
      have h_abs_pos : 0 < |y| := lt_of_lt_of_le (by norm_num) h_abs_t_ge
      have hσ_mem : (-1 : ℝ) ∈ Set.Icc (-1:ℝ) 2 := ⟨le_refl _, by norm_num⟩
      have h_quartic_bound :
          ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C / y^4 := by
        rcases le_or_gt 0 y with hy_nn | hy_neg
        · have h_y_ge : 2 ≤ y := by rwa [abs_of_nonneg hy_nn] at h_abs_t_ge
          exact h_quartic (-1) hσ_mem y h_y_ge
        · set T : ℝ := -y with hT_def
          have hT_ge : 2 ≤ T := by
            have h_abs : |y| = -y := abs_of_neg hy_neg
            simp [hT_def]; linarith
          rw [mellin_left_edge_norm_sym_swap]
          have h_neg_eq : ((-y : ℝ) : ℂ) = (T : ℂ) := by simp [hT_def]
          rw [h_neg_eq]
          have hT_bd := h_quartic (-1) hσ_mem T hT_ge
          have h_T4 : T^4 = y^4 := by simp [hT_def]; ring
          rw [h_T4] at hT_bd
          exact hT_bd
      have h_y_sq_ge_4 : 4 ≤ y^2 := by have := sq_abs y; nlinarith
      have h_y4_pos : 0 < y^4 := by nlinarith
      have h_one_plus_le : 1 + |y| ≤ 2 * |y| := by linarith
      have h_one_plus_nn : 0 ≤ 1 + |y| := by linarith [abs_nonneg y]
      have h_step1 : (1 + |y|) *
          ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ (1 + |y|) * (C / y^4) :=
        mul_le_mul_of_nonneg_left h_quartic_bound h_one_plus_nn
      have habs4 : |y|^4 = y^4 := by nlinarith [sq_nonneg (|y|^2 - y^2), sq_abs y]
      have h_step2 : (1 + |y|) * (C / y^4) ≤ 4 * C * (1 + y^2)⁻¹ := by
        have h_target : (1 + |y|) * (1 + y^2) ≤ 4 * y^4 := by
          have h_abs_y_ge_one : 1 ≤ |y| := by linarith
          have h_y_sq : |y|^2 = y^2 := sq_abs y
          have h_y4_eq : |y|^4 = y^4 := habs4
          nlinarith [h_y4_eq, h_abs_t_ge, h_abs_y_ge_one, sq_nonneg (|y|^2 - y^2)]
        have h_lhs_eq : (1 + |y|) * (C / y^4) = (1+|y|) * C / y^4 := by ring
        have h_rhs_eq : 4 * C * (1 + y^2)⁻¹ = 4 * C / (1 + y^2) := by field_simp
        rw [h_lhs_eq, h_rhs_eq, div_le_div_iff₀ h_y4_pos h_pos]
        nlinarith [hC_nn, h_target]
      have h_4C_le_K : 4 * C ≤ K := le_max_right _ _
      calc (1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ (1 + |y|) * (C / y^4) := h_step1
        _ ≤ 4 * C * (1 + y^2)⁻¹ := h_step2
        _ ≤ K * (1 + y^2)⁻¹ := mul_le_mul_of_nonneg_right h_4C_le_K h_inv_nn

/-! ### Pole-term norm bound

For `σ ≥ 1/2` and any real `c, y`:
```
‖1/((k:ℂ)+1) - 1/((k:ℂ) + (σ + (cy)·I))‖ ≤ 2·(|σ-1| + |c|·|y|) / (k+1)².
```

This dominates each pole-kernel summand by a `1/(k+1)²` envelope after
combining with `‖M(β,-1+iy)‖`. -/

private lemma pole_term_norm_bound_swap (σ c y : ℝ) (hσ : 1/2 ≤ σ) (k : ℕ) :
    ‖(1 : ℂ) / ((k : ℂ) + 1) -
        1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖ ≤
      2 * (|σ - 1| + |c| * |y|) / ((k : ℝ) + 1)^2 := by
  set s : ℂ := (σ : ℂ) + ((c * y : ℝ) : ℂ) * I with hs_def
  have h_s_re : s.re = σ := by simp [s]
  have h_s_pos : 0 < s.re := by rw [h_s_re]; linarith
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1_pos : (0:ℝ) < (k:ℝ) + 1 := by linarith
  have hk1_ne : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hsk_ne : (k : ℂ) + s ≠ 0 := by
    intro h
    have h1 : ((k:ℂ) + s).re = 0 := by rw [h]; simp
    simp [Complex.add_re, h_s_re] at h1
    linarith
  have h_decomp : (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s) =
      (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
    field_simp; ring
  rw [h_decomp, norm_div, norm_mul]
  have h_s_sub_norm : ‖s - 1‖ ≤ |σ - 1| + |c| * |y| := by
    have h_re : (s - 1).re = σ - 1 := by simp [s]
    have h_im : (s - 1).im = c * y := by simp [s]
    have h_norm : ‖s - 1‖ = Real.sqrt ((σ - 1)^2 + (c * y)^2) := by
      rw [Complex.norm_def, Complex.normSq_apply, h_re, h_im]; ring_nf
    rw [h_norm, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : (σ-1)^2 = |σ-1|^2 := (sq_abs _).symm
    have h2 : (c*y)^2 = |c|^2 * |y|^2 := by
      rw [show (c*y)^2 = |c*y|^2 from (sq_abs _).symm, abs_mul]; ring
    rw [h1, h2]
    have h_ab_nn : 0 ≤ |σ-1| * (|c| * |y|) := by positivity
    nlinarith [abs_nonneg (σ-1), abs_nonneg c, abs_nonneg y, h_ab_nn]
  have h_k1_norm : ‖((k:ℂ) + 1)‖ = (k:ℝ) + 1 := by
    rw [show ((k:ℂ) + 1 : ℂ) = (((k:ℝ) + 1 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    exact abs_of_pos hk1_pos
  have h_ks_norm_ge : ‖(k:ℂ) + s‖ ≥ (k:ℝ) + σ := by
    have h_re : ((k:ℂ) + s).re = (k:ℝ) + σ := by simp [Complex.add_re, h_s_re]
    have h_re_le := Complex.abs_re_le_norm ((k:ℂ) + s)
    rw [h_re] at h_re_le
    have h_pos : 0 ≤ (k:ℝ) + σ := by linarith
    rw [abs_of_nonneg h_pos] at h_re_le
    exact h_re_le
  have h_ks_ge_half : (k:ℝ) + σ ≥ ((k:ℝ) + 1) / 2 := by linarith
  have h_ks_norm_ge_half : ‖(k:ℂ) + s‖ ≥ ((k:ℝ) + 1) / 2 :=
    le_trans h_ks_ge_half h_ks_norm_ge
  have h_ks_norm_pos : 0 < ‖(k:ℂ) + s‖ := norm_pos_iff.mpr hsk_ne
  have hPdenom_pos : 0 < ‖((k:ℂ) + 1)‖ * ‖(k:ℂ) + s‖ := by
    apply mul_pos
    · rw [h_k1_norm]; exact hk1_pos
    · exact h_ks_norm_pos
  have h_target_nn : 0 ≤ |σ - 1| + |c| * |y| := by positivity
  have h_target_norm_nn : 0 ≤ ‖s - 1‖ := norm_nonneg _
  rw [div_le_div_iff₀ hPdenom_pos (by positivity : (0:ℝ) < ((k:ℝ)+1)^2)]
  have h_prod_ge : ‖((k:ℂ) + 1)‖ * ‖(k:ℂ) + s‖ ≥ ((k:ℝ)+1)^2 / 2 := by
    rw [h_k1_norm]
    have := mul_le_mul_of_nonneg_left h_ks_norm_ge_half hk1_pos.le
    have h_eq : ((k:ℝ)+1) * (((k:ℝ)+1)/2) = ((k:ℝ)+1)^2 / 2 := by ring
    linarith
  nlinarith [h_s_sub_norm, h_prod_ge, h_target_norm_nn, h_target_nn, hk1_pos]

/-! ### Generic pole-series swap (for `σ ≥ 1/2`)

Both LEFT (`σ = 1/2, c = 1/2`) and RIGHT (`σ = 1, c = -1/2`) targets are
instances of this generic swap.  The integrability gates 1/2 already
established in `CauchyKPairTestEngineering.lean` provide the LHS integrability,
and the quartic decay supplies the L¹-summability needed for
`MeasureTheory.integral_tsum_of_summable_integral_norm`. -/

private theorem digamma_pole_series_swap_pos (β α σ c : ℝ)
    (hσ_pos : 0 < σ) (hσ_half : 1/2 ≤ σ)
    (h_psi_M_int : Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :
    (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      -(Real.eulerMascheroniConstant : ℂ) / 2 *
          constantLogPiShiftedArchIntegral β α +
      ∑' k : ℕ, (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  -- Continuity prerequisites.
  have h_M_cont : Continuous (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    PairTestIdentity.pairTestMellin_left_edge_continuous β
  have h_exp_cont : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
    fun_prop
  have h_M1y_int := mellin_left_edge_one_plus_abs_integrable_swap β
  have h_M_norm_int : Integrable (fun y : ℝ =>
      ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
    -- Bounded by (1 + |y|) · ‖M‖ since 1 ≤ 1+|y|
    apply h_M1y_int.mono' h_M_cont.norm.aestronglyMeasurable
    refine MeasureTheory.ae_of_all _ fun y => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    calc ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
        = 1 * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by ring
      _ ≤ (1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
  -- Per-k function (without the (1/2) factor).
  set f : ℕ → ℝ → ℂ := fun k y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1 / ((k : ℂ) + 1)) -
       (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf_def
  -- Continuity of f k.
  have h_f_cont : ∀ k : ℕ, Continuous (f k) := by
    intro k
    have h_kernel_cont : Continuous (fun y : ℝ =>
        ((1 : ℂ) / ((k : ℂ) + 1)) -
          (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) := by
      refine Continuous.sub continuous_const ?_
      refine Continuous.div continuous_const ?_ ?_
      · fun_prop
      · intro y h
        have := congr_arg Complex.re h
        simp [Complex.add_re] at this
        linarith [Nat.cast_nonneg k (α := ℝ)]
    exact (h_exp_cont.mul h_kernel_cont).mul h_M_cont
  -- Pointwise bound on ‖f k y‖.
  have h_f_pw_bd : ∀ k : ℕ, ∀ y : ℝ,
      ‖f k y‖ ≤ (2 * (max |σ - 1| |c|)) *
        ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
        / ((k : ℝ) + 1)^2 := by
    intro k y
    rw [hf_def]
    rw [norm_mul, norm_mul]
    have h_exp_norm : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      have h_im : (((y * α : ℝ) : ℂ) * I).re = 0 := by simp
      rw [Complex.norm_exp, h_im]; exact Real.exp_zero
    rw [h_exp_norm, one_mul]
    have h_term := pole_term_norm_bound_swap σ c y hσ_half k
    have h_M_nn : 0 ≤ ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
      norm_nonneg _
    have h_max_nn : 0 ≤ max |σ - 1| |c| := le_max_of_le_left (abs_nonneg _)
    have h_target : 2 * (|σ - 1| + |c| * |y|) ≤
        2 * (max |σ - 1| |c|) * (1 + |y|) := by
      have h1 : |σ - 1| ≤ max |σ - 1| |c| := le_max_left _ _
      have h2 : |c| ≤ max |σ - 1| |c| := le_max_right _ _
      nlinarith [abs_nonneg (σ - 1), abs_nonneg c, abs_nonneg y, h_max_nn, h1, h2,
                 mul_le_mul_of_nonneg_right h2 (abs_nonneg y)]
    have h_term_le :
        ‖(1 : ℂ) / ((k : ℂ) + 1) -
            1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖
        ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 := by
      calc ‖(1 : ℂ) / ((k : ℂ) + 1) -
              1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖
          ≤ 2 * (|σ - 1| + |c| * |y|) / ((k : ℝ) + 1)^2 := h_term
        _ ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 := by
            apply div_le_div_of_nonneg_right h_target (by positivity)
    calc ‖(1 : ℂ) / ((k : ℂ) + 1) -
            1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖ *
          ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 *
            ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right h_term_le h_M_nn
      _ = 2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2 := by ring
  -- Integrability of f k.
  have h_A_nn : 0 ≤ 2 * (max |σ - 1| |c|) := by
    apply mul_nonneg (by norm_num) (le_max_of_le_left (abs_nonneg _))
  have h_f_int : ∀ k : ℕ, Integrable (f k) := by
    intro k
    have hk1_pos : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h_dom_int : Integrable (fun y : ℝ =>
        2 * (max |σ - 1| |c|) *
          ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
          / ((k : ℝ) + 1)^2) := by
      have heq : (fun y : ℝ =>
          2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2) =
          (fun y : ℝ => (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)) := by
        funext y; ring
      rw [heq]
      exact h_M1y_int.const_mul _
    refine h_dom_int.mono' (h_f_cont k).aestronglyMeasurable ?_
    refine MeasureTheory.ae_of_all _ fun y => ?_
    have h_rhs_nn : 0 ≤ 2 * (max |σ - 1| |c|) *
        ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
        / ((k : ℝ) + 1)^2 := by
      apply div_nonneg
      · apply mul_nonneg h_A_nn
        apply mul_nonneg (by linarith [abs_nonneg y]) (norm_nonneg _)
      · positivity
    show ‖f k y‖ ≤ _
    exact h_f_pw_bd k y
  -- L¹-summability of (∫ ‖f k‖) over k.
  set J : ℝ := ∫ y : ℝ, (1 + |y|) *
      ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hJ_def
  have hJ_nn : 0 ≤ J := by
    apply MeasureTheory.integral_nonneg
    intro y; positivity
  have h_per_k_int : ∀ k : ℕ,
      ∫ y : ℝ, ‖f k y‖ ≤ (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2 := by
    intro k
    have h_LHS_int : Integrable (fun y => ‖f k y‖) := (h_f_int k).norm
    have h_dom_int : Integrable (fun y : ℝ =>
        (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
          ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)) :=
      h_M1y_int.const_mul _
    have h_int_ineq := MeasureTheory.integral_mono_ae h_LHS_int h_dom_int
      (MeasureTheory.ae_of_all _ (fun y => by
        have := h_f_pw_bd k y
        have heq : 2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2 =
            (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
              ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
          ring
        rw [heq] at this; exact this))
    rw [MeasureTheory.integral_const_mul] at h_int_ineq
    have heq : (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) * J =
        (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2 := by ring
    rw [heq] at h_int_ineq
    exact h_int_ineq
  have h_summable : Summable (fun k : ℕ => ∫ y : ℝ, ‖f k y‖) := by
    apply Summable.of_nonneg_of_le (fun k => MeasureTheory.integral_nonneg
      (fun y => norm_nonneg _)) h_per_k_int
    -- Summable: ((2*max·J)/(k+1)²)
    have h_const : Summable (fun k : ℕ =>
        (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2) := by
      have heq : (fun k : ℕ => (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2) =
          fun k : ℕ => ((2 * (max |σ - 1| |c|)) * J) * (1 / ((k : ℝ) + 1)^2) := by
        funext k; ring
      rw [heq]
      apply Summable.mul_left
      have h_shift : (fun k : ℕ => 1 / ((k : ℝ) + 1)^2) =
          (fun n : ℕ => 1 / ((n : ℝ))^2) ∘ (· + 1) := by
        funext k
        show 1 / ((k : ℝ) + 1)^2 = 1 / ((k + 1 : ℕ) : ℝ)^2
        push_cast; ring
      rw [h_shift]
      exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
        (fun a b h => by simpa using h)
    exact h_const
  -- Now apply integral_tsum_of_summable_integral_norm.
  have h_swap : (∑' k : ℕ, ∫ y : ℝ, f k y) = ∫ y : ℝ, ∑' k : ℕ, f k y :=
    MeasureTheory.integral_tsum_of_summable_integral_norm h_f_int h_summable
  -- Pointwise expansion: exp · ψ · M = -γ · exp · M + Σ_k f_k.
  have h_pointwise_eq : ∀ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      -(Real.eulerMascheroniConstant : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
      ∑' k : ℕ, f k y := by
    intro y
    set sy : ℂ := (σ : ℂ) + ((c * y : ℝ) : ℂ) * I with hsy_def
    have hsy_re : sy.re = σ := by simp [sy]
    have hsy_pos : 0 < sy.re := by rw [hsy_re]; exact hσ_pos
    have h_psi := digamma_eq_series sy hsy_pos
    unfold digammaSeriesSum at h_psi
    rw [h_psi]
    have h_tsum_eq :
        (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (sy + (k : ℂ)))) =
        (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy))) := by
      apply tsum_congr; intro k; rw [add_comm sy]
    rw [h_tsum_eq]
    set E : ℂ := Complex.exp (((y * α : ℝ) : ℂ) * I)
    set Mv : ℂ := Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)
    have h_tsum_mul :
        (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy))) * (E * Mv) =
        ∑' k : ℕ, ((1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy)) * (E * Mv)) :=
      tsum_mul_right.symm
    rw [show E * (-(Real.eulerMascheroniConstant : ℂ) +
          ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy))) * Mv =
        -(Real.eulerMascheroniConstant : ℂ) * (E * Mv) +
        (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy))) * (E * Mv) from by ring]
    rw [h_tsum_mul]
    congr 1
    apply tsum_congr; intro k
    show (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy)) * (E * Mv) = f k y
    rw [hf_def]
    show (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy)) * (E * Mv) =
      E * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + sy)) * Mv
    ring
  -- Combine: integrate the pointwise expansion.
  have h_left_int : Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := h_psi_M_int
  -- Show: ∫ exp · ψ · M = -γ · ∫ (exp · M) + ∑_k ∫ f_k.
  have h_expM_int : Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    -- Bound: ‖exp · M‖ ≤ ‖M‖, and ‖M‖ integrable.
    have h_exp_M_cont : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := h_exp_cont.mul h_M_cont
    apply h_M_norm_int.mono' h_exp_M_cont.aestronglyMeasurable
    refine MeasureTheory.ae_of_all _ fun y => ?_
    rw [norm_mul]
    have h_exp_norm : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      have h_im : (((y * α : ℝ) : ℂ) * I).re = 0 := by simp
      rw [Complex.norm_exp, h_im]; exact Real.exp_zero
    rw [h_exp_norm, one_mul]
  -- Goal: (1/2)·∫ exp·ψ·M = -γ/2·∫ exp·M + ∑_k (1/2)·∫ f_k.
  -- We proceed by showing ∫ exp·ψ·M = -γ·∫ exp·M + ∑_k ∫ f_k, then multiply by 1/2.
  -- Equivalently: ∫ exp·ψ·M - (-γ)·∫ exp·M = ∑_k ∫ f_k.
  -- Step (a): integrate the pointwise expansion over y.
  have h_int_LHS_eq : (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (∫ y : ℝ, -(Real.eulerMascheroniConstant : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) +
      (∫ y : ℝ, ∑' k : ℕ, f k y) := by
    -- ∫ LHS = ∫ (-γ · exp · M + Σ f_k) by pointwise eq, then split via integrability.
    have h_neg_gamma_int : Integrable (fun y : ℝ =>
        -(Real.eulerMascheroniConstant : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) :=
      h_expM_int.const_mul _
    -- ∫ ∑' k, f k y exists by integral_tsum_of_summable_integral_norm
    -- and equals ∑' k, ∫ f k y.
    -- For the split, we need the function ∑' k, f k y to be integrable.
    -- We get this by writing it as the difference (LHS - (-γ·exp·M)).
    have h_tsum_f_pw : ∀ y, ∑' k : ℕ, f k y =
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) -
        -(Real.eulerMascheroniConstant : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      intro y
      have h := h_pointwise_eq y
      linear_combination -h
    have h_tsum_f_int : Integrable (fun y : ℝ => ∑' k : ℕ, f k y) := by
      have h_eq : (fun y : ℝ => ∑' k : ℕ, f k y) =
          (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
          (fun y : ℝ => -(Real.eulerMascheroniConstant : ℂ) *
            (Complex.exp (((y * α : ℝ) : ℂ) * I) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by
        funext y; rw [Pi.sub_apply]; exact h_tsum_f_pw y
      rw [h_eq]
      exact h_left_int.sub h_neg_gamma_int
    -- Now split the integral using the pointwise equation.
    have h_int_sum : (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Complex.digamma ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        (∫ y : ℝ, -(Real.eulerMascheroniConstant : ℂ) *
          (Complex.exp (((y * α : ℝ) : ℂ) * I) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
          (∑' k : ℕ, f k y)) := by
      apply MeasureTheory.integral_congr_ae
      refine MeasureTheory.ae_of_all _ fun y => ?_
      exact h_pointwise_eq y
    rw [h_int_sum]
    rw [MeasureTheory.integral_add h_neg_gamma_int h_tsum_f_int]
  -- Step (b): apply integral_tsum to the last term.
  have h_int_last_eq : (∫ y : ℝ, ∑' k : ℕ, f k y) = ∑' k : ℕ, ∫ y : ℝ, f k y := by
    rw [← h_swap]
  rw [h_int_last_eq] at h_int_LHS_eq
  -- Step (c): multiply by 1/2.
  -- We need: (1/2)·∫ψ·M = -γ/2·∫exp·M + ∑ (1/2)·∫f_k.
  -- ∫ exp·ψ·M = -γ·∫exp·M + ∑ ∫f_k     (h_int_LHS_eq, after simplification of constant)
  -- Multiply by (1/2):
  --   (1/2)·∫ψ·M = -γ/2·∫exp·M + (1/2)·∑ ∫f_k
  --             = -γ/2·∫exp·M + ∑ (1/2)·∫f_k.
  -- Also: -γ·∫exp·M = -γ · constantLogPi β α (definition).
  unfold constantLogPiShiftedArchIntegral
  -- Write -(γ:ℂ) * (...) = -(γ:ℂ) * ∫ exp · M
  have h_const_eq : (∫ y : ℝ, -(Real.eulerMascheroniConstant : ℂ) *
        (Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      -(Real.eulerMascheroniConstant : ℂ) *
        (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    MeasureTheory.integral_const_mul _ _
  rw [h_const_eq] at h_int_LHS_eq
  rw [h_int_LHS_eq]
  -- Goal:
  -- (1/2) * (-γ · ∫ exp·M + ∑ ∫ f_k) = -γ/2 · ∫ exp·M + ∑ (1/2)·∫ f_k
  -- We need (1/2) · ∑ ∫ f_k = ∑ (1/2) · ∫ f_k.
  rw [mul_add]
  congr 1
  · ring
  · -- (1/2) · ∑_k ∫ f_k = ∑_k (1/2) · ∫ f_k
    rw [tsum_mul_left]

/-! ## Step 14: Left pole-series swap

`digammaPosHalfShiftedArchIntegralLeft β α = -γ/2 · constantLogPi β α +
Σ' k, digammaPoleKernelLeft k β α`. -/

theorem digammaPosHalfLeft_pole_series_target_holds (β α : ℝ) :
    digammaPosHalfLeft_pole_series_target β α := by
  -- Build the integrability hypothesis from the public LEFT gate, then align
  -- coordinates via `(y/2:ℝ:ℂ) = ((1/2 * y:ℝ):ℂ)`.
  have h_psi_M_int : Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma (((1/2 : ℝ) : ℂ) + ((1/2 * y : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := digammaPosHalfShiftedArchIntegrand_left_integrable β α
    convert h using 1
    apply funext; intro y
    show _ * Complex.digamma _ * _ = _ * Complex.digamma _ * _
    congr 2; push_cast; ring_nf
  have h := digamma_pole_series_swap_pos β α (1/2) (1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 ≤ 1/2) h_psi_M_int
  unfold digammaPosHalfLeft_pole_series_target
  unfold digammaPosHalfShiftedArchIntegralLeft digammaPoleKernelLeft
  -- Align ψ integral with helper output.
  rw [show (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma (((1/2 : ℝ) : ℂ) + ((1/2 * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) from by
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * Complex.digamma _ * _ = _ * Complex.digamma _ * _
    congr 2; push_cast; ring_nf]
  -- Align tsum kernel.
  rw [show (∑' k : ℕ, (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (∑' k : ℕ, (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + (((1/2 : ℝ) : ℂ) + ((1/2 * y : ℝ) : ℂ) * I)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by
    apply tsum_congr; intro k
    congr 1
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * (_ - _) * _ = _ * (_ - _) * _
    congr 3; push_cast; ring]
  exact h

#print axioms digammaPosHalfLeft_pole_series_target_holds

/-! ## Step 15: Right pole-series swap -/

theorem digammaPosHalfRight_pole_series_target_holds (β α : ℝ) :
    digammaPosHalfRight_pole_series_target β α := by
  have h_psi_M_int : Integrable (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I) *
      Complex.digamma (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := digammaPosHalfShiftedArchIntegrand_right_integrable β α
    convert h using 1
    apply funext; intro y
    show _ * Complex.digamma _ * _ = _ * Complex.digamma _ * _
    congr 2
    rw [show (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) =
        ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2 : ℂ) from by push_cast; ring]
  have h := digamma_pole_series_swap_pos β α 1 (-1/2)
    (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ)/2 ≤ 1) h_psi_M_int
  unfold digammaPosHalfRight_pole_series_target
  unfold digammaPosHalfShiftedArchIntegralRight digammaPoleKernelRight
  rw [show (∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        Complex.digamma (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) from by
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * Complex.digamma _ * _ = _ * Complex.digamma _ * _
    congr 2
    rw [show ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2 : ℂ) =
        (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) from by push_cast; ring]]
  rw [show (∑' k : ℕ, (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (∑' k : ℕ, (1/2 : ℂ) * ∫ y : ℝ, Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by
    apply tsum_congr; intro k
    congr 1
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * (_ - _) * _ = _ * (_ - _) * _
    congr 3
    rw [show ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2 : ℂ) =
        (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) from by push_cast; ring]]
  exact h

#print axioms digammaPosHalfRight_pole_series_target_holds

/-! ## Step 15a: Pole-kernel summability (public)

The two pole-kernel sums `∑' k, digammaPoleKernelLeft k β α` and
`∑' k, digammaPoleKernelRight k β α` converge unconditionally.  This is
extracted from the L¹-summability infrastructure used inside
`digamma_pole_series_swap_pos`, which depends only on the integrability
gates already established in `CauchyKPairTestEngineering.lean` (the
`(1 + |y|) · ‖M(β, -1 + iy)‖` integrability bound) plus the pole-term
norm bound.  No `exp · ψ · M` integrability hypothesis is required
because we only assert summability of the per-`k` integrals (not the
swap identity). -/

private theorem summable_pole_kernel_swap_generic (β α σ c : ℝ)
    (hσ_pos : 0 < σ) (hσ_half : 1/2 ≤ σ) :
    Summable (fun k : ℕ => (1/2 : ℂ) * ∫ y : ℝ,
      Complex.exp (((y * α : ℝ) : ℂ) * I) *
        ((1 / ((k : ℂ) + 1)) -
         (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  -- Continuity prerequisites.
  have h_M_cont : Continuous (fun y : ℝ =>
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    PairTestIdentity.pairTestMellin_left_edge_continuous β
  have h_exp_cont : Continuous (fun y : ℝ => Complex.exp (((y * α : ℝ) : ℂ) * I)) := by
    fun_prop
  have h_M1y_int := mellin_left_edge_one_plus_abs_integrable_swap β
  -- Per-k function (without the (1/2) factor).
  set f : ℕ → ℝ → ℂ := fun k y =>
    Complex.exp (((y * α : ℝ) : ℂ) * I) *
      ((1 / ((k : ℂ) + 1)) -
       (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hf_def
  -- Continuity of f k.
  have h_f_cont : ∀ k : ℕ, Continuous (f k) := by
    intro k
    have h_kernel_cont : Continuous (fun y : ℝ =>
        ((1 : ℂ) / ((k : ℂ) + 1)) -
          (1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I)))) := by
      refine Continuous.sub continuous_const ?_
      refine Continuous.div continuous_const ?_ ?_
      · fun_prop
      · intro y h
        have := congr_arg Complex.re h
        simp [Complex.add_re] at this
        linarith [Nat.cast_nonneg k (α := ℝ)]
    exact (h_exp_cont.mul h_kernel_cont).mul h_M_cont
  -- Pointwise bound on ‖f k y‖.
  have h_f_pw_bd : ∀ k : ℕ, ∀ y : ℝ,
      ‖f k y‖ ≤ (2 * (max |σ - 1| |c|)) *
        ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
        / ((k : ℝ) + 1)^2 := by
    intro k y
    rw [hf_def]
    rw [norm_mul, norm_mul]
    have h_exp_norm : ‖Complex.exp (((y * α : ℝ) : ℂ) * I)‖ = 1 := by
      have h_im : (((y * α : ℝ) : ℂ) * I).re = 0 := by simp
      rw [Complex.norm_exp, h_im]; exact Real.exp_zero
    rw [h_exp_norm, one_mul]
    have h_term := pole_term_norm_bound_swap σ c y hσ_half k
    have h_M_nn : 0 ≤ ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
      norm_nonneg _
    have h_max_nn : 0 ≤ max |σ - 1| |c| := le_max_of_le_left (abs_nonneg _)
    have h_target : 2 * (|σ - 1| + |c| * |y|) ≤
        2 * (max |σ - 1| |c|) * (1 + |y|) := by
      have h1 : |σ - 1| ≤ max |σ - 1| |c| := le_max_left _ _
      have h2 : |c| ≤ max |σ - 1| |c| := le_max_right _ _
      nlinarith [abs_nonneg (σ - 1), abs_nonneg c, abs_nonneg y, h_max_nn, h1, h2,
                 mul_le_mul_of_nonneg_right h2 (abs_nonneg y)]
    have h_term_le :
        ‖(1 : ℂ) / ((k : ℂ) + 1) -
            1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖
        ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 := by
      calc ‖(1 : ℂ) / ((k : ℂ) + 1) -
              1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖
          ≤ 2 * (|σ - 1| + |c| * |y|) / ((k : ℝ) + 1)^2 := h_term
        _ ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 := by
            apply div_le_div_of_nonneg_right h_target (by positivity)
    calc ‖(1 : ℂ) / ((k : ℂ) + 1) -
            1 / ((k : ℂ) + ((σ : ℂ) + ((c * y : ℝ) : ℂ) * I))‖ *
          ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ 2 * (max |σ - 1| |c|) * (1 + |y|) / ((k : ℝ) + 1)^2 *
            ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right h_term_le h_M_nn
      _ = 2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2 := by ring
  -- Integrability of f k.
  have h_A_nn : 0 ≤ 2 * (max |σ - 1| |c|) := by
    apply mul_nonneg (by norm_num) (le_max_of_le_left (abs_nonneg _))
  have h_f_int : ∀ k : ℕ, Integrable (f k) := by
    intro k
    have h_dom_int : Integrable (fun y : ℝ =>
        2 * (max |σ - 1| |c|) *
          ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
          / ((k : ℝ) + 1)^2) := by
      have heq : (fun y : ℝ =>
          2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2) =
          (fun y : ℝ => (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)) := by
        funext y; ring
      rw [heq]
      exact h_M1y_int.const_mul _
    refine h_dom_int.mono' (h_f_cont k).aestronglyMeasurable ?_
    refine MeasureTheory.ae_of_all _ fun y => ?_
    have h_rhs_nn : 0 ≤ 2 * (max |σ - 1| |c|) *
        ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
        / ((k : ℝ) + 1)^2 := by
      apply div_nonneg
      · apply mul_nonneg h_A_nn
        apply mul_nonneg (by linarith [abs_nonneg y]) (norm_nonneg _)
      · positivity
    show ‖f k y‖ ≤ _
    exact h_f_pw_bd k y
  -- L¹-summability of (∫ ‖f k‖) over k.
  set J : ℝ := ∫ y : ℝ, (1 + |y|) *
      ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hJ_def
  have hJ_nn : 0 ≤ J := by
    apply MeasureTheory.integral_nonneg
    intro y; positivity
  have h_per_k_int : ∀ k : ℕ,
      ∫ y : ℝ, ‖f k y‖ ≤ (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2 := by
    intro k
    have h_LHS_int : Integrable (fun y => ‖f k y‖) := (h_f_int k).norm
    have h_dom_int : Integrable (fun y : ℝ =>
        (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
          ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)) :=
      h_M1y_int.const_mul _
    have h_int_ineq := MeasureTheory.integral_mono_ae h_LHS_int h_dom_int
      (MeasureTheory.ae_of_all _ (fun y => by
        have := h_f_pw_bd k y
        have heq : 2 * (max |σ - 1| |c|) *
            ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖)
            / ((k : ℝ) + 1)^2 =
            (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) *
              ((1 + |y|) * ‖Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
          ring
        rw [heq] at this; exact this))
    rw [MeasureTheory.integral_const_mul] at h_int_ineq
    have heq : (2 * (max |σ - 1| |c|) / ((k : ℝ) + 1)^2) * J =
        (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2 := by ring
    rw [heq] at h_int_ineq
    exact h_int_ineq
  -- Summability of ∫ ‖f k‖ via comparison with C/(k+1)².
  have h_summable_norm_int : Summable (fun k : ℕ => ∫ y : ℝ, ‖f k y‖) := by
    apply Summable.of_nonneg_of_le (fun k => MeasureTheory.integral_nonneg
      (fun y => norm_nonneg _)) h_per_k_int
    have h_const : Summable (fun k : ℕ =>
        (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2) := by
      have heq : (fun k : ℕ => (2 * (max |σ - 1| |c|)) * J / ((k : ℝ) + 1)^2) =
          fun k : ℕ => ((2 * (max |σ - 1| |c|)) * J) * (1 / ((k : ℝ) + 1)^2) := by
        funext k; ring
      rw [heq]
      apply Summable.mul_left
      have h_shift : (fun k : ℕ => 1 / ((k : ℝ) + 1)^2) =
          (fun n : ℕ => 1 / ((n : ℝ))^2) ∘ (· + 1) := by
        funext k
        show 1 / ((k : ℝ) + 1)^2 = 1 / ((k + 1 : ℕ) : ℝ)^2
        push_cast; ring
      rw [h_shift]
      exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
        (fun a b h => by simpa using h)
    exact h_const
  -- Lift to summability of ∫ f k via ‖∫ f k‖ ≤ ∫ ‖f k‖ and Summable.of_norm.
  have h_norm_int_le : ∀ k : ℕ,
      ‖∫ y : ℝ, f k y‖ ≤ ∫ y : ℝ, ‖f k y‖ := fun k =>
    MeasureTheory.norm_integral_le_integral_norm _
  have h_summable_norm : Summable (fun k : ℕ => ‖∫ y : ℝ, f k y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_norm_int_le h_summable_norm_int
  have h_summable_int : Summable (fun k : ℕ => ∫ y : ℝ, f k y) :=
    Summable.of_norm h_summable_norm
  -- Multiply by (1/2 : ℂ).
  exact h_summable_int.mul_left _

/-- **Public**: summability of the left pole-kernel series. -/
theorem summable_digammaPoleKernelLeft (β α : ℝ) :
    Summable (fun k : ℕ => digammaPoleKernelLeft k β α) := by
  have h := summable_pole_kernel_swap_generic β α (1/2) (1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 ≤ 1/2)
  -- Align the kernel via push_cast on the σ + (c·y)·I form.
  have h_eq : (fun k : ℕ => digammaPoleKernelLeft k β α) =
      (fun k : ℕ => (1/2 : ℂ) * ∫ y : ℝ,
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((1 / ((k : ℂ) + 1)) -
           (1 / ((k : ℂ) + (((1/2 : ℝ) : ℂ) +
             (((1/2 : ℝ) * y : ℝ) : ℂ) * I)))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    funext k
    unfold digammaPoleKernelLeft
    congr 1
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * (_ - _) * _ = _ * (_ - _) * _
    congr 3; push_cast; ring
  rw [h_eq]
  exact h

#print axioms summable_digammaPoleKernelLeft

/-- **Public**: summability of the right pole-kernel series. -/
theorem summable_digammaPoleKernelRight (β α : ℝ) :
    Summable (fun k : ℕ => digammaPoleKernelRight k β α) := by
  have h := summable_pole_kernel_swap_generic β α 1 (-1/2)
    (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ)/2 ≤ 1)
  -- Align kernel via (2 - iy)/2 = 1 + (-1/2 · y) · I.
  have h_eq : (fun k : ℕ => digammaPoleKernelRight k β α) =
      (fun k : ℕ => (1/2 : ℂ) * ∫ y : ℝ,
        Complex.exp (((y * α : ℝ) : ℂ) * I) *
          ((1 / ((k : ℂ) + 1)) -
           (1 / ((k : ℂ) + (((1 : ℝ) : ℂ) +
             (((-1/2 : ℝ) * y : ℝ) : ℂ) * I)))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    funext k
    unfold digammaPoleKernelRight
    congr 1
    apply MeasureTheory.integral_congr_ae
    refine MeasureTheory.ae_of_all _ fun y => ?_
    show _ * (_ - _) * _ = _ * (_ - _) * _
    congr 3
    rw [show ((((2 : ℝ) : ℂ) - (y : ℂ) * I) / 2 : ℂ) =
        (((1 : ℝ) : ℂ) + ((-1/2 * y : ℝ) : ℂ) * I) from by push_cast; ring]
  rw [h_eq]
  exact h

#print axioms summable_digammaPoleKernelRight

/-! ## Step 16: Unconditional shifted-arch closed-form theorem

All five gates closed: assemble the unconditional version. -/

theorem shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional (β α : ℝ) :
    shiftedArchIntegral β α = shiftedArchClosedForm β α := by
  exact shiftedArchIntegral_eq_shiftedArchClosedForm β α
    (digammaPosHalfShiftedArchIntegrand_left_integrable β α)
    (digammaPosHalfShiftedArchIntegrand_right_integrable β α)
    (rationalCorrectionIntegrand_integrable β α)
    (digammaPosHalfLeft_pole_series_target_holds β α)
    (digammaPosHalfRight_pole_series_target_holds β α)

#print axioms shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
