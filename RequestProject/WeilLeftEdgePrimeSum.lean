import Mathlib
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.PairCoshGaussTest
import RequestProject.WeilPairTestMellinExtend
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilZeroSum
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilHadamardBoundaryDecomposition

/-!
# Step 2b: closed form for the σ = -1 left-edge reflected-prime piece

Goal:
```
∫_ℝ (ζ'(2 − iy) / ζ(2 − iy)) · pairTestMellin β (-1 + iy) dy
  = -2π · Σ_n (Λ(n) / n) · pair_cosh_gauss_test β (1/n)
```

Mechanism: Mellin inversion of `pairTestMellin β` at `σ = -1` plus Fubini
swap of `LSeries(vonMangoldt)` at `Re s = 2`. Specifically:

* Mellin inversion at `σ = -1`: for `t > 0`,
  `pair_cosh_gauss_test β t = (1/(2π)) · ∫_ℝ pairTestMellin β (-1 + iy) · t^{1 - iy} dy`.
  Equivalent form for `t = 1/n`:
  `∫_ℝ n^{iy} · pairTestMellin β (-1 + iy) dy = 2π · n · pair_cosh_gauss_test β (1/n)`.
* `ζ'(2 − iy) / ζ(2 − iy) = -LSeries(Λ)(2 − iy) = -Σ_n Λ(n) · n^{-2} · n^{iy}` on `Re s > 1`.
* Fubini swap interchanging the `Σ_n` and the `∫_ℝ`.

Conclusion: integral = `-2π · Σ_n Λ(n)/n · pair_cosh_gauss_test β (1/n)`.

This is the substantial new analytic content for Step 2b. The proof structure
mirrors `primeSingleCosh_eq_vertical_integral` (S2) in `PairTestVanishingScaffold`,
adapted to σ = -1 instead of σ = 2.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace LeftEdgePrimeSum

open ZD.WeilPositivity.Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helper infrastructure for Mellin inversion at σ = -1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Extended Mellin convergence for the pair test on `Re s > -4`.**

Since `pair_cosh_gauss_test β t = O(t⁴)` as `t → 0⁺` (from the four-fold sinh²
factorisation) and `O(exp(-t))` as `t → ∞`, the Mellin transform converges on
`Re s > -4`. This is the convergence input for `mellinInv_mellin_eq` at
`σ = -1`. -/
theorem mellinConvergent_pair_extended (β : ℝ) {s : ℂ} (hs : -4 < s.re) :
    MellinConvergent (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -4) zero_lt_one
    (Contour.pair_cosh_gauss_test_locallyIntegrableOn_ofReal β) ?_ ?_ hs
  · have h := pair_cosh_gauss_test_isBigO_exp_neg_atTop β
    refine h.congr_right (fun t => ?_); simp [neg_mul, one_mul]
  · have h := Contour.pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero β
    refine h.congr_right (fun t => ?_); congr 1; norm_num

/-- **Continuity of `pairTestMellin β` along the vertical line `Re s = σ`** for
any `σ > -4`, via the extended differentiability lemma. -/
theorem pairTestMellin_continuous_along_vertical_extended
    (β : ℝ) (σ : ℝ) (hσ : -4 < σ) :
    Continuous (fun t : ℝ => pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) := by
  have h_diff_on : DifferentiableOn ℂ (pairTestMellin β) {s : ℂ | -4 < s.re} := by
    intro s hs
    exact (Contour.pairTestMellin_differentiableAt_re_gt_neg_four β hs).differentiableWithinAt
  have h_inner : Continuous (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I)) := by fun_prop
  have h_map : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | -4 < s.re} := by
    intro t; show -4 < ((σ : ℂ) + (t : ℂ) * I).re; simp; exact hσ
  exact h_diff_on.continuousOn.comp_continuous h_inner h_map

/-- **Conjugation of `pairTestMellin β`.** Local rederivation of the symmetry
`pairTestMellin β (star s) = star (pairTestMellin β s)`. -/
private theorem pairTestMellin_conj_local (β : ℝ) (s : ℂ) :
    pairTestMellin β (star s) = star (pairTestMellin β s) := by
  unfold pairTestMellin mellin
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

/-- **Vertical integrability of `pairTestMellin β` at `σ = -1`.** Continuity on
the compact slab `|t| ≤ 2` plus the quartic decay `‖pairTestMellin β (-1+iT)‖ ≤
C/T⁴` for `|T| ≥ 2` (using the extended IBP×4 identity). -/
theorem pairTestMellin_vertical_integrable_at_neg_one (β : ℝ) :
    Complex.VerticalIntegrable (pairTestMellin β) (-1) MeasureTheory.volume := by
  unfold Complex.VerticalIntegrable
  have h_cont : Continuous
      (fun t : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    pairTestMellin_continuous_along_vertical_extended β (-1) (by norm_num)
  have h_eq :
      (fun y : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + y * I)) =
      (fun t : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    funext t; rfl
  rw [h_eq]
  -- Gather quartic bound on |t| ≥ 2 and a compact uniform bound on |t| ≤ 2.
  obtain ⟨C, hC_nn, h_quartic⟩ :=
    ZD.WeilPositivity.HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended β
  have hσ_mem : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := ⟨le_refl _, by norm_num⟩
  -- Compact bound on |t| ≤ 2 via continuity.
  have h_compact : IsCompact (Set.Icc (-2:ℝ) 2) := isCompact_Icc
  obtain ⟨t_max, _, h_max⟩ := h_compact.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-2:ℝ) ≤ 2))
    (Continuous.continuousOn (h_cont.norm))
  set M : ℝ := ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (t_max : ℂ) * I)‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  -- Pointwise bound by `K · (1 + t²)⁻¹` with `K = max (16 · M) (16 · C)`.
  -- For `|t| ≤ 2`: `‖pair‖ ≤ M ≤ M · (1+t²)/(1+t²) ≤ (5M) · (1+t²)⁻¹` since `1+t² ≤ 5`,
  -- but we also use `1+t² ≥ 1`, so `M ≤ M · 5 · (1+t²)⁻¹` is fine — let's use `5M`.
  -- For `|t| ≥ 2`: `‖pair‖ ≤ C/t⁴ ≤ C/(t² · 4) ≤ C/(4 · (1+t²)/2) = C/(2(1+t²)) · 1`. We just take K = max(5M, 2C).
  set K : ℝ := max (5 * M) (2 * C) with hK_def
  have hK_nn : 0 ≤ K := le_max_of_le_left (by linarith)
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul K) h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h_1plus_pos : 0 < 1 + t^2 := by positivity
  have h_inv_nn : 0 ≤ (1 + t^2)⁻¹ := inv_nonneg.mpr h_1plus_pos.le
  have h_rhs_nn : 0 ≤ K * (1 + t^2)⁻¹ := mul_nonneg hK_nn h_inv_nn
  rw [Real.norm_of_nonneg h_rhs_nn]
  by_cases h_split : |t| ≤ 2
  · -- |t| ≤ 2: bound by M.
    have h_t_in : t ∈ Set.Icc (-2:ℝ) 2 := by
      rw [Set.mem_Icc]; constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have h_pair_le : ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ M := by
      have := h_max h_t_in
      simpa [hM_def] using this
    -- Now `1 + t² ≤ 5`, so `1/(1+t²) ≥ 1/5`, so `5M / (1+t²) ≥ M`.
    have h_t_sq_le : t^2 ≤ 4 := by
      have h_abs_nn : 0 ≤ |t| := abs_nonneg _
      have : |t|^2 ≤ 2^2 := pow_le_pow_left₀ h_abs_nn h_split 2
      have h_eq' : |t|^2 = t^2 := sq_abs t
      linarith
    have h_1plus_le : 1 + t^2 ≤ 5 := by linarith
    have h_inv_ge : (1:ℝ)/5 ≤ (1 + t^2)⁻¹ := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5)]
      rw [le_inv_mul_iff₀ h_1plus_pos]
      linarith
    have h_5M_le_K : 5 * M ≤ K := le_max_left _ _
    calc ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ M := h_pair_le
      _ = (5 * M) * (1/5) := by ring
      _ ≤ (5 * M) * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_left h_inv_ge (by linarith)
      _ ≤ K * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_right h_5M_le_K h_inv_nn
  · -- |t| ≥ 2: use quartic bound. Two sub-cases t ≥ 2 or t ≤ -2.
    have h_abs_t_ge : 2 ≤ |t| := (not_le.mp h_split).le
    have h_t_sq : t^2 = |t|^2 := (sq_abs t).symm
    have h_abs_pos : 0 < |t| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) h_abs_t_ge
    have h_t_sq_pos : 0 < t^2 := by rw [h_t_sq]; positivity
    have h_t_sq_ge_4 : 4 ≤ t^2 := by
      have : (2:ℝ)^2 ≤ |t|^2 := pow_le_pow_left₀ (by norm_num) h_abs_t_ge 2
      rw [h_t_sq]; linarith
    -- Quartic bound: `‖pair‖ ≤ C / t⁴` (need both signs).
    have h_quartic_bound : ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C / t^4 := by
      by_cases ht_pos : 0 ≤ t
      · -- t ≥ 2.
        have ht_ge : 2 ≤ t := by
          have h_abs_eq : |t| = t := abs_of_nonneg ht_pos
          linarith [h_abs_eq ▸ h_abs_t_ge]
        have h := h_quartic (-1) hσ_mem t ht_ge
        convert h using 2
      · -- t ≤ -2: use conjugation symmetry.
        have ht_neg : t < 0 := not_le.mp ht_pos
        have ht_neg_le : t ≤ -2 := by
          have h_abs_t : |t| = -t := abs_of_neg ht_neg
          rw [h_abs_t] at h_abs_t_ge; linarith
        set T : ℝ := -t with hT_def
        have hT_ge : 2 ≤ T := by simp [hT_def]; linarith
        -- ‖pair (-1 + tI)‖ = ‖pair (-1 + (-T)I)‖ = ‖pair (star(-1+TI))‖ = ‖star(...)‖ = ‖pair (-1+TI)‖
        have h_star_eq : ((-1 : ℝ) : ℂ) + (t : ℂ) * I =
            star (((-1 : ℝ) : ℂ) + (T : ℂ) * I) := by
          apply Complex.ext
          · simp [hT_def]
          · simp [hT_def]
        rw [h_star_eq, pairTestMellin_conj_local, norm_star]
        have hT_bound := h_quartic (-1) hσ_mem T hT_ge
        have h_T4_eq : T^4 = t^4 := by simp [hT_def]; ring
        rw [h_T4_eq] at hT_bound
        exact hT_bound
    -- Now `C / t⁴ ≤ 2C · (1+t²)⁻¹` using `t⁴ = (t²)² ≥ 2 · (1+t²)` for t² ≥ 4.
    have h_t4_ge : 2 * (1 + t^2) ≤ t^4 := by
      have h_t2_ge_4 : 4 ≤ t^2 := h_t_sq_ge_4
      have h_t4_eq : t^4 = t^2 * t^2 := by ring
      nlinarith
    have h_t4_pos : 0 < t^4 := by
      have h_t2_pos : 0 < t^2 := h_t_sq_pos
      nlinarith [sq_nonneg (t^2)]
    -- C / t⁴ ≤ 2C/(2(1+t²)) ≤ ... wait: t⁴ ≥ 2(1+t²) ⟹ 1/t⁴ ≤ 1/(2(1+t²))
    -- ⟹ C/t⁴ ≤ C/(2(1+t²)) ≤ 2C/(1+t²) [since 1/(2x) ≤ 2/x for x>0 false; need to redo]
    -- Actually: t⁴ ≥ 2(1+t²) ⟹ 1/t⁴ ≤ 1/(2(1+t²)) = (1/2)·(1+t²)⁻¹.
    -- So C/t⁴ ≤ (C/2)·(1+t²)⁻¹ ≤ 2C·(1+t²)⁻¹ (since C ≥ 0). Use 2C as bound.
    have h_div : C / t^4 ≤ (2 * C) * (1 + t^2)⁻¹ := by
      have h_inv_le : (1 : ℝ) / t^4 ≤ 1 / (2 * (1 + t^2)) := by
        apply one_div_le_one_div_of_le _ h_t4_ge
        linarith
      have h_C_div : C / t^4 = C * (1 / t^4) := by rw [mul_one_div]
      rw [h_C_div]
      have h_tar : C * (1 / t^4) ≤ C * (1 / (2 * (1 + t^2))) :=
        mul_le_mul_of_nonneg_left h_inv_le hC_nn
      apply le_trans h_tar
      have h_simp : C * (1 / (2 * (1 + t^2))) = (C / 2) * (1 + t^2)⁻¹ := by
        rw [mul_one_div, div_mul_eq_div_div, div_eq_mul_inv (C/2)]
      rw [h_simp]
      apply mul_le_mul_of_nonneg_right _ h_inv_nn
      linarith
    have h_2C_le_K : 2 * C ≤ K := le_max_right _ _
    calc ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ C / t^4 := h_quartic_bound
      _ ≤ (2 * C) * (1 + t^2)⁻¹ := h_div
      _ ≤ K * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_right h_2C_le_K h_inv_nn

/-- **Mellin inversion of `pairTestMellin β` evaluated at `t = 1/n`.**

For each natural `n ≥ 1`, the Fourier-of-Mellin inversion at the line
`Re s = -1` gives:
```
∫_ℝ n^{iy} · pairTestMellin β (-1 + iy) dy = 2π · n · pair_cosh_gauss_test β (1/n).
```

This is an instance of the Mellin inversion formula at `σ = -1`, which is
inside the convergence strip for `pairTestMellin β` (since
`pair_cosh_gauss_test β t = O(t^4)` near 0 — extending convergence to
`Re s > -4`). -/
theorem pairTestMellin_inversion_at_neg_one (β : ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ y : ℝ, (n : ℂ)^((y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) =
      2 * (Real.pi : ℂ) * (n : ℂ) *
        ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_inv_pos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  -- Build the standard Mellin inversion at σ = -1.
  set f : ℝ → ℂ := fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ) with hf_def
  have h_mellin_eq : mellin f = pairTestMellin β := by funext s; rfl
  have h_conv : MellinConvergent f (((-1 : ℝ) : ℂ)) :=
    mellinConvergent_pair_extended β (by simp : -4 < (((-1 : ℝ) : ℂ)).re)
  have h_vint : Complex.VerticalIntegrable (mellin f) (-1) MeasureTheory.volume := by
    rw [h_mellin_eq]
    exact pairTestMellin_vertical_integrable_at_neg_one β
  have h_cont_at : ContinuousAt f (1 / (n : ℝ)) := by
    apply Complex.continuous_ofReal.continuousAt.comp
    exact (pair_cosh_gauss_test_continuous β).continuousAt
  have h_inv := mellinInv_mellin_eq (-1 : ℝ) f hn_inv_pos h_conv h_vint h_cont_at
  -- h_inv : mellinInv (-1) (mellin f) (1/n) = f (1/n)
  rw [h_mellin_eq] at h_inv
  -- Unfold mellinInv:
  --   (1/(2π)) • ∫ y, ((1/n):ℂ)^(-((-1)+yI)) • pairTestMellin β ((-1)+yI) = (pair_cosh_gauss_test β (1/n) : ℂ)
  unfold mellinInv at h_inv
  -- Convert smul to multiplication and simplify the cpow.
  have h_arg_n : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact ne_of_lt Real.pi_pos
  have h_pow_simp : ∀ y : ℝ,
      ((1 / (n : ℝ) : ℝ) : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        (1 / (n : ℂ)) * (n : ℂ) ^ ((y : ℂ) * I) := by
    intro y
    have h_cast : ((1 / (n : ℝ) : ℝ) : ℂ) = 1 / (n : ℂ) := by push_cast; ring
    rw [h_cast]
    have h_neg_arg : -(((-1 : ℝ) : ℂ) + (y : ℂ) * I) = (1 : ℂ) + (-y : ℂ) * I := by
      push_cast; ring
    rw [h_neg_arg]
    have h_inv_C_ne : (1 / (n : ℂ)) ≠ 0 := by
      rw [one_div]; exact inv_ne_zero hn_ne
    rw [Complex.cpow_add _ _ h_inv_C_ne]
    rw [Complex.cpow_one]
    -- Now goal: (1/n) * ((1/n) : ℂ)^((-y)·I) = (1/n) * (n)^(y·I)
    congr 1
    -- (1/n)^(-y·I) = n^(y·I)
    rw [show (1 / (n : ℂ)) = (n : ℂ)⁻¹ from one_div _]
    rw [Complex.inv_cpow _ _ h_arg_n]
    rw [← Complex.cpow_neg]
    congr 1; ring
  -- Rewrite the integrand inside h_inv.
  have h_inv2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ (y : ℝ), (1 / (n : ℂ)) * (n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
    have h_integ_eq :
        (fun y : ℝ => ((1 / (n : ℝ) : ℝ) : ℂ) ^ (-(((-1 : ℝ) : ℂ) + y * I)) •
          pairTestMellin β (((-1 : ℝ) : ℂ) + y * I)) =
        (fun y : ℝ => (1 / (n : ℂ)) * (n : ℂ) ^ ((y : ℂ) * I) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
      funext y
      show ((1 / (n : ℝ) : ℝ) : ℂ) ^ (-(((-1 : ℝ) : ℂ) + (y : ℂ) * I)) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = _
      rw [h_pow_simp y]
    rw [h_integ_eq] at h_inv
    -- h_inv : (1/(2π)) • ∫ (y), 1/n * n^(yI) * pairTestMellin β (-1+yI) = f (1/n).
    -- Convert real smul to multiplication via Complex.real_smul.
    show ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = _
    rw [← Complex.real_smul]
    exact h_inv
  -- Pull `1/n` out of the integral.
  have h_const_pull :
      ∫ (y : ℝ), (1 / (n : ℂ)) * (n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      (1 / (n : ℂ)) * ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [show (fun y : ℝ => (1 / (n : ℂ)) * (n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        (fun y : ℝ => (1 / (n : ℂ)) * ((n : ℂ) ^ ((y : ℂ) * I) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) from by
      funext y; ring]
    exact MeasureTheory.integral_const_mul _ _
  rw [h_const_pull] at h_inv2
  -- Now h_inv2: (1/(2π)) · (1/n) · I = pair, where I = ∫ ...
  -- Solve for I = 2π · n · pair.
  have h_2pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero hπ
  -- Multiply both sides by 2π · n.
  have h_step : (2 * (Real.pi : ℂ) * (n : ℂ)) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((1 / (n : ℂ)) * ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      (2 * (Real.pi : ℂ) * (n : ℂ)) *
        ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
    rw [h_inv2]
  have h_simplify_lhs :
      (2 * (Real.pi : ℂ) * (n : ℂ)) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((1 / (n : ℂ)) * ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    have h_2pi_cast : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by
      push_cast; ring
    rw [h_2pi_cast]
    have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show (2 * (Real.pi : ℂ) * (n : ℂ)) *
        (1 / (2 * (Real.pi : ℂ)) *
          ((1 / (n : ℂ)) * ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
            pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
        ((2 * (Real.pi : ℂ) * (n : ℂ)) * (1 / (2 * (Real.pi : ℂ)) * (1 / (n : ℂ)))) *
          ∫ (y : ℝ), (n : ℂ) ^ ((y : ℂ) * I) *
            pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) by ring]
    have h_cancel : (2 * (Real.pi : ℂ) * (n : ℂ)) *
        (1 / (2 * (Real.pi : ℂ)) * (1 / (n : ℂ))) = 1 := by
      field_simp
    rw [h_cancel, one_mul]
  rw [h_simplify_lhs] at h_step
  exact h_step

/-- **Step 2b**: closed form of the reflected-prime piece of the left-edge
integrand at `σ = -1`. -/
theorem leftEdge_reflectedPrime_eq_sum (β : ℝ) :
    ∫ y : ℝ,
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
       riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) =
    -2 * (Real.pi : ℂ) *
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
  -- s := 2 - yI corresponds to 1 - (-1 + yI). Re s = 2 > 1.
  set s : ℝ → ℂ := fun y : ℝ => (2 : ℂ) - (y : ℂ) * I with hs_def
  -- Per-n term: G n y := term_Λ (s y) n · pairTestMellin β (-1+yI).
  set G : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (s y) n *
      pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hG_def
  -- Pointwise: ζ'/ζ(s y) · pairTestMellin β (-1+yI) = -∑' n, G n y, since LSeries Λ = -ζ'/ζ on Re > 1.
  have h_pt : ∀ y : ℝ,
      (deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
      -∑' n : ℕ, G n y := by
    intro y
    have h_1s_eq : 1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = s y := by
      simp [hs_def]; ring
    rw [h_1s_eq]
    have hs_re : (1 : ℝ) < (s y).re := by simp [hs_def]
    have hL := vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs_re
    -- hL : LSeries Λ (s y) = -deriv ζ (s y) / ζ (s y)
    -- so deriv ζ (s y) / ζ (s y) = -LSeries Λ (s y).
    have hζ_eq : deriv riemannZeta (s y) / riemannZeta (s y) =
        -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s y) := by
      rw [hL]; ring
    rw [hζ_eq]
    rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s y) =
            ∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n from rfl]
    rw [show (-∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n) * pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
            -(∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s y) n * pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from by
      rw [tsum_mul_right]; ring]
  -- Integrability of pairTestMellin β (-1+yI) on ℝ (vertical integrability).
  have h_pair_int : MeasureTheory.Integrable
      (fun y : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have h := pairTestMellin_vertical_integrable_at_neg_one β
    unfold Complex.VerticalIntegrable at h
    exact h
  -- Continuity of pairTestMellin β (-1+yI) along vertical line.
  have h_pair_cont : Continuous
      (fun y : ℝ => pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    pairTestMellin_continuous_along_vertical_extended β (-1) (by norm_num)
  -- Per-n integrability of G n.
  have h_G_int : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ y : ℝ, G 0 y = 0 := by
        intro y; simp [hG_def, LSeries.term_zero]
      refine (MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume).congr ?_
      exact MeasureTheory.ae_of_all _ (fun y => (h_zero y).symm)
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have hn_ne_C : (n : ℂ) ≠ 0 := by exact_mod_cast hn_ne
      -- G n y = Λ(n) · n^{-s y} · pairTestMellin β (-1+yI).
      have h_term : ∀ y : ℝ, G n y =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-(s y))) *
             pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        intro y
        simp only [hG_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      have h_fn_eq : (G n : ℝ → ℂ) = fun y : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((n : ℂ) ^ (-(s y))) *
             pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := funext h_term
      rw [h_fn_eq]
      apply MeasureTheory.Integrable.const_mul
      -- Continuity of n^{-s y}.
      have h_cpow_cont : Continuous (fun y : ℝ => ((n : ℂ) ^ (-(s y)))) := by
        have h_exp : Continuous (fun y : ℝ => -(s y)) := by
          simp only [hs_def]; fun_prop
        have h_cpow_cont_z : Continuous (fun z : ℂ => (n : ℂ) ^ z) := by
          rw [continuous_iff_continuousAt]
          intro b
          exact continuousAt_const_cpow hn_ne_C
        exact h_cpow_cont_z.comp h_exp
      -- Norm: ‖n^{-s y}‖ = n^{-2}.
      have h_cpow_norm : ∀ y : ℝ, ‖((n : ℂ) ^ (-(s y)))‖ = (n : ℝ) ^ (-(2:ℝ)) := by
        intro y
        rw [show -(s y) = ((-2 : ℝ) : ℂ) + (y : ℂ) * I from by
          simp [hs_def]; ring]
        rw [Complex.norm_natCast_cpow_of_pos hpos]
        simp
      -- Integrable: bound ‖n^(-s y) · pair‖ = n^{-2} · ‖pair‖ ≤ n^{-2} · ‖pair‖.
      -- Use that h_pair_int is integrable and norm is bounded.
      refine (h_pair_int.norm.const_mul ((n : ℝ)^(-(2:ℝ)))).mono'
        ((h_cpow_cont.mul h_pair_cont).aestronglyMeasurable) ?_
      refine MeasureTheory.ae_of_all _ fun y => ?_
      rw [norm_mul, h_cpow_norm y]
  -- Summability of ∫ ‖G n‖.
  -- Bound: ∫ ‖G n y‖ dy ≤ Λ(n) · n^{-2} · I_pair, where I_pair := ∫ ‖pairTestMellin β (-1+yI)‖.
  set I_pair : ℝ := ∫ y : ℝ, ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hI_pair_def
  have hI_pair_nn : 0 ≤ I_pair :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have h_G_L1_summ : Summable (fun n : ℕ => ∫ y : ℝ, ‖G n y‖) := by
    have h_bound_summ : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * I_pair) := by
      have h_div := summable_vonMangoldt_rpow (2:ℝ) (by norm_num : (1:ℝ) < 2)
      have h_eq : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ)^(-(2:ℝ)) * I_pair) =
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
            (n : ℝ)^(2:ℝ) * I_pair) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [ArithmeticFunction.map_zero]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
      rw [h_eq]; exact h_div.mul_right I_pair
    refine h_bound_summ.of_nonneg_of_le ?_ ?_
    · intro n; exact MeasureTheory.integral_nonneg (fun y => norm_nonneg _)
    · intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have h_zero : ∀ y : ℝ, ‖G 0 y‖ = 0 := by
          intro y; simp [hG_def, LSeries.term_zero]
        rw [MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ h_zero), MeasureTheory.integral_zero]
        simp [ArithmeticFunction.map_zero]
      · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
        -- ‖G n y‖ ≤ Λ(n) · n^{-2} · ‖pairTestMellin β (-1+yI)‖.
        have h_bd_pt : ∀ y : ℝ,
            ‖G n y‖ ≤
            (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
              ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
          intro y
          simp only [hG_def]
          rw [LSeries.term_of_ne_zero hn_ne, norm_mul, norm_div]
          rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
                (ArithmeticFunction.vonMangoldt n : ℝ) from by
            rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
                  = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
            rw [Complex.norm_real]
            exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          rw [Complex.norm_natCast_cpow_of_pos hpos]
          have h_sy_re : (s y).re = 2 := by simp [hs_def]
          rw [h_sy_re]
          have h_Lnn : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          have hns_pos : 0 < (n : ℝ)^(2:ℝ) := Real.rpow_pos_of_pos hn_pos _
          have hns_eq : (n : ℝ)^(-(2:ℝ)) = ((n : ℝ)^(2:ℝ))⁻¹ :=
            Real.rpow_neg hn_pos.le _
          rw [hns_eq]
          rw [show (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^(2:ℝ) *
              ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ)^(2:ℝ))⁻¹ *
              ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ by
            rw [div_eq_mul_inv]]
        calc ∫ y : ℝ, ‖G n y‖
            ≤ ∫ y : ℝ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
                       ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
              apply MeasureTheory.integral_mono_of_nonneg
              · exact MeasureTheory.ae_of_all _ fun _ => norm_nonneg _
              · exact h_pair_int.norm.const_mul _
              · exact MeasureTheory.ae_of_all _ h_bd_pt
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) *
              ∫ y : ℝ, ‖pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
              rw [MeasureTheory.integral_const_mul]
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-(2:ℝ)) * I_pair := by
              rw [hI_pair_def]
  -- Fubini swap.
  have h_fubini : (∫ y : ℝ, ∑' n : ℕ, G n y) = ∑' n : ℕ, ∫ y : ℝ, G n y :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm h_G_int h_G_L1_summ).symm
  -- Per-n integral evaluation.
  have h_per_n : ∀ n : ℕ, ∫ y : ℝ, G n y =
      (2 * Real.pi : ℂ) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
        ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h_zero : ∀ y : ℝ, G 0 y = 0 := by
        intro y; simp [hG_def, LSeries.term_zero]
      rw [MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_of_all _ h_zero), MeasureTheory.integral_zero]
      simp [ArithmeticFunction.map_zero]
    · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have hn_ne_C : (n : ℂ) ≠ 0 := by exact_mod_cast hn_ne
      -- G n y = Λ(n) · (n^{-2}) · n^{iy} · pairTestMellin β (-1+yI).
      have h_pow_split : ∀ y : ℝ,
          ((n : ℂ) ^ (-(s y))) =
            ((n : ℝ) : ℂ)^(-(2:ℂ)) * ((n : ℂ) ^ ((y : ℂ) * I)) := by
        intro y
        rw [show -(s y) = ((-2 : ℝ) : ℂ) + (y : ℂ) * I from by
          simp [hs_def]; ring]
        rw [Complex.cpow_add _ _ hn_ne_C]
        congr 1; push_cast; ring
      set C_n : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℝ) : ℂ)^(-(2:ℂ)) with hC_n_def
      have h_term : ∀ y : ℝ, G n y =
          C_n * (((n : ℂ) ^ ((y : ℂ) * I)) *
             pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
        intro y
        simp only [hG_def, hC_n_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
        rw [h_pow_split y]
        ring
      have h_fn_eq : (G n : ℝ → ℂ) = fun y : ℝ =>
          C_n * (((n : ℂ) ^ ((y : ℂ) * I)) *
             pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := funext h_term
      rw [h_fn_eq]
      change ∫ y : ℝ, C_n * ((n : ℂ) ^ ((y : ℂ) * I) *
        pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) = _
      rw [show (∫ y : ℝ, C_n * ((n : ℂ) ^ ((y : ℂ) * I) *
          pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
          C_n * ∫ y : ℝ, ((n : ℂ) ^ ((y : ℂ) * I) *
            pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) from
        MeasureTheory.integral_const_mul C_n _]
      rw [pairTestMellin_inversion_at_neg_one β hpos]
      -- LHS: C_n · (2π · n · pair).
      -- RHS: 2π · (Λ(n)/n) · pair.
      -- C_n = Λ(n) · n^{-2}, so C_n · n = Λ(n)/n.
      simp only [hC_n_def]
      have h_n_C2 : ((n : ℝ) : ℂ)^(-(2:ℂ)) = ((n : ℂ)^2)⁻¹ := by
        rw [show -(2 : ℂ) = -((2 : ℕ) : ℂ) from by norm_num]
        rw [Complex.cpow_neg, show ((2 : ℕ) : ℂ) = (2 : ℂ) from by norm_num,
            show (2 : ℂ) = ((2 : ℕ) : ℂ) from by norm_num, Complex.cpow_natCast]
        push_cast; rfl
      rw [h_n_C2]
      field_simp
  -- Assembly.
  calc ∫ y : ℝ,
      (deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
        riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
      pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)
      = ∫ y : ℝ, -∑' n : ℕ, G n y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact h_pt y
    _ = -∫ y : ℝ, ∑' n : ℕ, G n y := by rw [MeasureTheory.integral_neg]
    _ = -∑' n : ℕ, ∫ y : ℝ, G n y := by rw [h_fubini]
    _ = -∑' n : ℕ, (2 * Real.pi : ℂ) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)) *
          ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by
        congr 1; apply tsum_congr; intro n; rw [h_per_n n]
    _ = -((2 * Real.pi : ℂ) *
          ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)) := by
        rw [← tsum_mul_left]
        congr 1
        apply tsum_congr
        intro n
        ring
    _ = -2 * (Real.pi : ℂ) *
          ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) := by ring

/-- **Step 2b decomposition**: the full left-edge boundary integrand at σ=-1
splits as `archIntegrand β (-1) + reflectedPrime piece`, with the second piece
having the closed form proven above. -/
theorem leftEdge_integrand_decomposition (β : ℝ) (y : ℝ) :
    hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) =
      archIntegrand β (-1) y +
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
       riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
  unfold hadamardArchBoundaryTerm archIntegrand
  ring

#print axioms pairTestMellin_inversion_at_neg_one
#print axioms leftEdge_reflectedPrime_eq_sum
#print axioms leftEdge_integrand_decomposition

end LeftEdgePrimeSum
end WeilPositivity
end ZD

end

