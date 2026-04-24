import Mathlib
import RequestProject.WeilFinalAssembly
import RequestProject.WeilRectResidueIdentityDischarge
import RequestProject.WeilRectangleZerosFull
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.XiOrderSummable
import RequestProject.WeilHadamardKernel
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilLogDerivLeftSlab
import RequestProject.CriticalStripLandau
import RequestProject.WeilRHSPrimeEven
import RequestProject.CriticalStripLandauGoodHeight
import RequestProject.WeilArchPrimeIdentity
import RequestProject.ArchOperatorBound
import RequestProject.WeilReflectedPrimeVanishingWeilside
import RequestProject.WeilRightEdgePrimeSum

/-!
# Unconditional discharge wrappers for `weil_explicit_formula_classical`

Each of the six hypotheses of
`ZD.WeilPositivity.FinalAssembly.weil_explicit_formula_classical` is discharged
unconditionally by plugging in existing project theorems.
-/

noncomputable section

open Complex MeasureTheory

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

/-- **h_rect_residue discharge** — direct alias. -/
theorem h_rect_residue_unconditional :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → rectangleResidueIdentity_target β :=
  fun β hβ => rectangleResidueIdentity_target_holds_neg_one_two β hβ

#print axioms h_rect_residue_unconditional

/-- **h_fin discharge** — transport `zeros_finite_in_rect_unconditional` through
the subtype coercion. -/
theorem h_fin_unconditional : nontrivialZeros_in_weilRect_finite_target := by
  intro T
  have h := zeros_finite_in_rect_unconditional (-1) 2 T
  -- h : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T}.Finite
  refine (h.preimage (f := Subtype.val)
      (fun a _ b _ h => Subtype.val_injective h)).subset ?_
  rintro ⟨ρ, hρ⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨hρ, h1, h2, h3, h4⟩

#print axioms h_fin_unconditional

/-- **h_sum discharge** — multiplicity-weighted summability over nontrivial
zeros. Built from `pairTestMellin_im_sq_decay` (quadratic Mellin decay) and
`summable_xiOrderNat_div_norm_sq_nontrivialZeros` (weighted Jensen summability),
with the identification `Classical.choose … = xiOrderNat ρ` via
`analyticOrderAt_riemannZeta_eq_xiOrderNat`. -/
theorem h_sum_unconditional (β : ℝ) : weightedZeroSum_summable_target β := by
  obtain ⟨C, hC_nn, h_decay⟩ := Contour.pairTestMellin_im_sq_decay β
  -- Pointwise: `Classical.choose (analyticOrderAt_…) = xiOrderNat ρ.val`.
  have h_choose : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
        = ZD.xiOrderNat ρ.val := by
    intro ρ
    set h_ex := Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property
    have hspec := Classical.choose_spec h_ex
    have hxi := Contour.analyticOrderAt_riemannZeta_eq_xiOrderNat ρ.property
    have heq : ((Classical.choose h_ex : ℕ) : ℕ∞)
        = ((ZD.xiOrderNat ρ.val : ℕ) : ℕ∞) := by
      rw [← hspec.2, hxi]
    exact_mod_cast heq
  -- Majorant `C * xiOrderNat(ρ) / ‖ρ.val‖²` is summable.
  have h_major_summ : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left C
  -- Norm-bound: `‖n(ρ) · pairTestMellin β ρ‖ ≤ C · xiOrderNat(ρ) / ‖ρ‖²`.
  refine Summable.of_norm (h_major_summ.of_nonneg_of_le ?_ ?_)
  · intro ρ; positivity
  · intro ρ
    rw [norm_mul, Complex.norm_natCast, h_choose]
    -- ‖(n:ℂ) * x‖ = n * ‖x‖. Bound: n * ‖x‖ ≤ n * C/(1+im²) ≤ C * n/‖ρ‖².
    rcases ρ with ⟨ρv, hρv⟩
    have h_pm_le : ‖Contour.pairTestMellin β ρv‖ ≤ C / (1 + ρv.im ^ 2) :=
      h_decay ⟨ρv, hρv⟩
    obtain ⟨hρ_re_pos, hρ_re_lt_one, _⟩ := hρv
    have h_n_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρv : ℝ) := Nat.cast_nonneg _
    have h_one_plus_im_pos : (0 : ℝ) < 1 + ρv.im ^ 2 := by
      have := sq_nonneg ρv.im; linarith
    have h_normsq_pos : (0 : ℝ) < ‖ρv‖ ^ 2 := by
      have hρ_ne : ρv ≠ 0 := by
        intro h; rw [h] at hρ_re_pos; simp at hρ_re_pos
      positivity
    -- ‖ρ‖² ≤ 1 + im² since re² < 1 for nontrivial zeros.
    have h_norm_le : ‖ρv‖ ^ 2 ≤ 1 + ρv.im ^ 2 := by
      have h_re_abs : |ρv.re| ≤ 1 := by
        by_cases h_pos : 0 ≤ ρv.re
        · rw [abs_of_nonneg h_pos]; linarith
        · rw [abs_of_neg (lt_of_not_ge h_pos)]; linarith
      have h_re_sq : ρv.re ^ 2 ≤ 1 := by
        have := sq_abs ρv.re
        calc ρv.re ^ 2 = |ρv.re| ^ 2 := (sq_abs _).symm
          _ ≤ 1 ^ 2 := by
              apply sq_le_sq'
              · linarith [abs_nonneg ρv.re]
              · exact h_re_abs
          _ = 1 := by ring
      have h_norm_sq : ‖ρv‖ ^ 2 = ρv.re ^ 2 + ρv.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      linarith
    have h_inv_le : (1 : ℝ) / (1 + ρv.im ^ 2) ≤ 1 / ‖ρv‖ ^ 2 :=
      one_div_le_one_div_of_le h_normsq_pos h_norm_le
    -- `‖pairTestMellin‖ ≤ C/(1+im²) ≤ C/‖ρ‖²`.
    have h_pm_le' : ‖Contour.pairTestMellin β ρv‖ ≤ C / ‖ρv‖ ^ 2 := by
      calc ‖Contour.pairTestMellin β ρv‖ ≤ C / (1 + ρv.im ^ 2) := h_pm_le
        _ = C * (1 / (1 + ρv.im ^ 2)) := by ring
        _ ≤ C * (1 / ‖ρv‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left h_inv_le hC_nn
        _ = C / ‖ρv‖ ^ 2 := by ring
    calc (ZD.xiOrderNat ρv : ℝ) * ‖Contour.pairTestMellin β ρv‖
        ≤ (ZD.xiOrderNat ρv : ℝ) * (C / ‖ρv‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_pm_le' h_n_nn
      _ = C * ((ZD.xiOrderNat ρv : ℝ) / ‖ρv‖ ^ 2) := by ring

#print axioms h_sum_unconditional

-- ═══════════════════════════════════════════════════════════════════════════
-- § Uniform quartic Mellin decay on `σ ∈ [-1, 2]`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Quartic Mellin decay (+T side).** Direct wrapper around
`HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended`, which gives
`‖pairTestMellin β (σ+iT)‖ ≤ C/T^4` uniformly on `σ ∈ [-1, 2]` for `T ≥ 2`. -/
theorem uniform_pairMellin_quartic_target_pos (β : ℝ) :
    uniform_pairMellin_quartic_target β (-1) 2 := by
  obtain ⟨C, hC_nn, hbd⟩ :=
    HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended β
  refine ⟨C, 2, hC_nn, by norm_num, ?_⟩
  intro T hT σ hσ
  exact hbd σ hσ T hT

#print axioms uniform_pairMellin_quartic_target_pos

/-- **Conjugation of `pairTestMellin` along the real test function.** Since
`pair_cosh_gauss_test β` is real-valued, `pairTestMellin β s̄ = conj(pairTestMellin β s)`. -/
private theorem pairTestMellin_conj (β : ℝ) (s : ℂ) :
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
      = ((pair_cosh_gauss_test β t : ℝ) : ℂ) := by
    show starRingEnd ℂ ((pair_cosh_gauss_test β t : ℝ) : ℂ)
        = ((pair_cosh_gauss_test β t : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  rw [h_real_conj]
  congr 1
  rw [show star s - 1 = star (s - 1) from by rw [star_sub, star_one]]
  show (t : ℂ) ^ (starRingEnd ℂ (s - 1)) = starRingEnd ℂ ((t : ℂ) ^ (s - 1))
  rw [Complex.cpow_conj _ _ ht_arg]
  rw [Complex.conj_ofReal]

#print axioms pairTestMellin_conj

/-- **Quartic Mellin decay (−T side).** Follows from the `+T` version via
conjugation: `‖pairTestMellin β (σ−iT)‖ = ‖pairTestMellin β (σ+iT)‖`. -/
theorem uniform_pairMellin_quartic_target_neg (β : ℝ) :
    ∃ (C T₀ : ℝ), 0 ≤ C ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ ∈ Set.Icc (-1:ℝ) 2,
        ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C / T ^ 4 := by
  obtain ⟨C, T₀, hC, hT₀, hbd⟩ := uniform_pairMellin_quartic_target_pos β
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT σ hσ
  have h_conj_eq : (σ : ℂ) + (-T : ℂ) * I = star ((σ : ℂ) + (T : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [h_conj_eq, pairTestMellin_conj]
  rw [show star (Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I))
      = starRingEnd ℂ (Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)) from rfl]
  rw [Complex.norm_conj]
  exact hbd T hT σ hσ

#print axioms uniform_pairMellin_quartic_target_neg

-- ═══════════════════════════════════════════════════════════════════════════
-- § Edge-vanishing reductions — h_top, h_bottom, h_vert_cancel
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Full-strip ζ'/ζ polynomial bound with `N < 4`** — classical Landau
package on `σ ∈ [-1, 2]` at good heights. Assembled from:
* `logDerivZeta_bounded_of_right_of_one` — uniform (N=0) on `σ ≥ 1`.
* `criticalStripLandau` — `C (log T)²` on `σ ∈ (0, 1)`.
* `logDerivZeta_bound_left_slab` — `C (log T)²` on `σ ∈ [-3/4, -1/2]`.
* Extensions covering the remaining σ-gaps `[-1, -3/4]`, `[-1/2, 0]`, and
  the line `σ = 0` (by FE + Stirling).

The existential bundles constants `C, N, T₀` with `N = 2 < 4`, since
`(log T)² ≤ T² / 4` for `T ≥ 2`. -/
def full_strip_logDerivZeta_bound_N_lt_4_target : Prop :=
  ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
    ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ N

/-- Same shape at imaginary part `-T`. At good heights, bad-height exclusion
is symmetric (`goodHeight T ↔ no zero with im = ±T`), so the same bound
transports. -/
def full_strip_logDerivZeta_bound_N_lt_4_neg_target : Prop :=
  ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
    ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * T ^ N

/-- The pair of full-strip log-derivative bounds needed for the horizontal
edge inputs. Keeping this as a bundle makes the remaining Landau obligation
explicit: both signs of the horizontal line must be controlled uniformly for
every `goodHeight T`, with an exponent strictly below the quartic Mellin
decay. -/
structure FullStripLogDerivInputs : Prop where
  pos : full_strip_logDerivZeta_bound_N_lt_4_target
  neg : full_strip_logDerivZeta_bound_N_lt_4_neg_target

/-- **Left-of-critical-strip ζ'/ζ bound (target).** Uniform `(log T)²` bound
on `σ ∈ [-1, 0]` at good heights. The `goodHeight T` hypothesis provides the
near-zero separation needed by the xi-subtraction machinery to bound
`‖ζ'/ζ(σ+iT)‖` via the near-zero-sum route (at σ = 0 the FE-image Re(1-s) = 1
is in the zero-free region, but near zeros cluster there; separation handles it). -/
def leftOfCriticalStrip_target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Set.Icc (-1 : ℝ) 0 → ∀ T : ℝ, 2 ≤ T →
    goodHeight T →
    ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2

/-- **Right-of-critical-strip ζ'/ζ bound (target).** Uniform `(log T)²` bound
on `σ ∈ [1, 2]` at good heights. At σ = 1, the separation clause of `goodHeight T`
provides the lower bound `|ρ.im - T| ≥ Csep/log T` needed for the near-zero
sum, matching the shape of `criticalStripLandau_of_goodHeight`. -/
def rightOfCriticalStrip_target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → ∀ T : ℝ, 2 ≤ T →
    goodHeight T →
    ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2

/-- **Full-strip ζ'/ζ bound from the critical-strip + two boundary bounds.**
Assembly: Case-split σ ∈ Icc [-1, 2] into `{σ ≤ 0}`, `σ ∈ Ioo 0 1`, `{σ ≥ 1}`.
The middle case is `criticalStripLandau_of_goodHeight`; the outer cases are
the two boundary targets. The resulting bound is `C · (log T)²`, which is
`≤ C · T²` for `T ≥ 2`, so `N = 2 < 4`. -/
theorem full_strip_logDerivZeta_bound_pos_of_boundary
    (h_left : leftOfCriticalStrip_target)
    (h_right : rightOfCriticalStrip_target) :
    full_strip_logDerivZeta_bound_N_lt_4_target := by
  obtain ⟨C_crit, hC_crit_pos, h_crit⟩ := criticalStripLandau_of_goodHeight
  obtain ⟨C_left, hC_left_pos, h_left_bd⟩ := h_left
  obtain ⟨C_right, hC_right_pos, h_right_bd⟩ := h_right
  set C_max : ℝ := max (max C_crit C_left) C_right + 1 with hC_max_def
  have hC_max_pos : 0 < C_max := by
    rw [hC_max_def]
    have : 0 ≤ max (max C_crit C_left) C_right :=
      le_trans hC_crit_pos.le (le_trans (le_max_left _ _) (le_max_left _ _))
    linarith
  -- With N = 2, since (log T)² ≤ T² / (log 2)² for T ≥ 2 (weaker: ≤ T²).
  refine ⟨C_max / (Real.log 2)^2, 2, 2, ?_, by norm_num, by norm_num, ?_⟩
  · have hlog2_sq_pos : 0 < (Real.log 2)^2 := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    exact div_pos hC_max_pos hlog2_sq_pos
  intro T hT_ge_2 hGood σ hσ
  have hT_pos : 0 < T := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_sq_pos : 0 < (Real.log 2)^2 := by positivity
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT_ge_2
  have hlogT_nn : 0 ≤ Real.log T := le_trans hlog2_pos.le hlogT_ge_log2
  -- Bound (log T)² ≤ T² / (log 2)².
  have h_logT_sq_le : (Real.log T) ^ 2 ≤ T ^ 2 / (Real.log 2)^2 := by
    -- Real.log T ≤ T / Real.log 2 holds when log T · log 2 ≤ T, i.e., log 2 ≤ T/log T.
    -- Simpler: log T ≤ T - 1 ≤ T for T ≥ 1. Then (log T)² ≤ T², so T²/(log 2)² ≥ (log T)² since log 2 ≤ 1.
    have h_logT_le_T : Real.log T ≤ T := by
      have := Real.log_le_sub_one_of_pos hT_pos
      linarith
    have h_sq_le : (Real.log T)^2 ≤ T^2 := by
      have := sq_le_sq' (by linarith : -T ≤ Real.log T) h_logT_le_T
      exact this
    have h_inv_log2 : 1 ≤ 1 / (Real.log 2)^2 := by
      have h_log2_lt_one : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have h_log2_sq_lt_one : (Real.log 2)^2 < 1 := by
        have : (Real.log 2)^2 < 1^2 := by
          apply sq_lt_sq' <;> [linarith; exact h_log2_lt_one]
        linarith
      rw [le_div_iff₀ hlog2_sq_pos]; linarith
    calc (Real.log T)^2 ≤ T^2 := h_sq_le
      _ = T^2 * 1 := by ring
      _ ≤ T^2 * (1 / (Real.log 2)^2) :=
        mul_le_mul_of_nonneg_left h_inv_log2 (by positivity)
      _ = T^2 / (Real.log 2)^2 := by ring
  -- Convert T^2 to T^(2:ℝ).
  have hT_sq_rpow : T ^ (2:ℝ) = T ^ 2 := by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [hT_sq_rpow]
  -- Case split σ ∈ Icc [-1, 2].
  by_cases hσ_le_0 : σ ≤ 0
  · -- σ ∈ Icc [-1, 0].
    have hσ_mem : σ ∈ Set.Icc (-1:ℝ) 0 := ⟨hσ.1, hσ_le_0⟩
    have h_bd := h_left_bd σ hσ_mem T hT_ge_2 hGood
    have h_C_le : C_left ≤ C_max := by
      rw [hC_max_def]
      have : C_left ≤ max (max C_crit C_left) C_right := by
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    calc ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖
        ≤ C_left * (Real.log T)^2 := h_bd
      _ ≤ C_max * (Real.log T)^2 := by
        apply mul_le_mul_of_nonneg_right h_C_le
        positivity
      _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
        apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
      _ = C_max / (Real.log 2)^2 * T^2 := by ring
  · -- σ > 0. Sub-case: σ < 1 (critical strip) or σ ≥ 1 (right boundary).
    have hσ_gt_0 : 0 < σ := lt_of_not_ge hσ_le_0
    rcases lt_or_ge σ 1 with hσ_lt_1 | hσ_ge_1
    · -- σ ∈ Ioo 0 1: apply criticalStripLandau_of_goodHeight.
      have hσ_Ioo : σ ∈ Set.Ioo (0:ℝ) 1 := ⟨hσ_gt_0, hσ_lt_1⟩
      have h_bd := h_crit σ hσ_Ioo T hT_ge_2 hGood
      have h_C_le : C_crit ≤ C_max := by
        rw [hC_max_def]
        have : C_crit ≤ max (max C_crit C_left) C_right := by
          exact le_trans (le_max_left _ _) (le_max_left _ _)
        linarith
      calc ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖
          ≤ C_crit * (Real.log T)^2 := h_bd
        _ ≤ C_max * (Real.log T)^2 := by
          apply mul_le_mul_of_nonneg_right h_C_le
          positivity
        _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
          apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
        _ = C_max / (Real.log 2)^2 * T^2 := by ring
    · -- σ ∈ Icc [1, 2]: use right-boundary target.
      have hσ_mem : σ ∈ Set.Icc (1:ℝ) 2 := ⟨hσ_ge_1, hσ.2⟩
      have h_bd := h_right_bd σ hσ_mem T hT_ge_2 hGood
      have h_C_le : C_right ≤ C_max := by
        rw [hC_max_def]
        have : C_right ≤ max (max C_crit C_left) C_right := le_max_right _ _
        linarith
      calc ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖
          ≤ C_right * (Real.log T)^2 := h_bd
        _ ≤ C_max * (Real.log T)^2 := by
          apply mul_le_mul_of_nonneg_right h_C_le
          positivity
        _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
          apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
        _ = C_max / (Real.log 2)^2 * T^2 := by ring

#print axioms full_strip_logDerivZeta_bound_pos_of_boundary

/-- **Left-of-critical-strip ζ'/ζ bound at `-T` (target).** With goodHeight T. -/
def leftOfCriticalStrip_neg_target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Set.Icc (-1 : ℝ) 0 → ∀ T : ℝ, 2 ≤ T →
    goodHeight T →
    ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2

/-- **Right-of-critical-strip ζ'/ζ bound at `-T` (target).** With goodHeight T. -/
def rightOfCriticalStrip_neg_target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 → ∀ T : ℝ, 2 ≤ T →
    goodHeight T →
    ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2

/-- **Full-strip ζ'/ζ bound at `-T` from the critical-strip-at-`-T` + two
boundary bounds.** Symmetric form of `full_strip_logDerivZeta_bound_pos_of_boundary`
for the bottom-edge input. -/
def criticalStripLandau_neg_target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Ioo (0:ℝ) 1, ∀ T : ℝ, 2 ≤ T → goodHeight T →
    ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
      riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2

/-- **Full-strip `-T` bound from boundaries + in-strip.** Mirrors
`full_strip_logDerivZeta_bound_pos_of_boundary` with `-T` in place of `T` in
the integrand, using the symmetric targets. -/
theorem full_strip_logDerivZeta_bound_neg_of_boundary
    (h_crit_neg : criticalStripLandau_neg_target)
    (h_left : leftOfCriticalStrip_neg_target)
    (h_right : rightOfCriticalStrip_neg_target) :
    full_strip_logDerivZeta_bound_N_lt_4_neg_target := by
  obtain ⟨C_crit, hC_crit_pos, h_crit⟩ := h_crit_neg
  obtain ⟨C_left, hC_left_pos, h_left_bd⟩ := h_left
  obtain ⟨C_right, hC_right_pos, h_right_bd⟩ := h_right
  set C_max : ℝ := max (max C_crit C_left) C_right + 1 with hC_max_def
  have hC_max_pos : 0 < C_max := by
    rw [hC_max_def]
    have : 0 ≤ max (max C_crit C_left) C_right :=
      le_trans hC_crit_pos.le (le_trans (le_max_left _ _) (le_max_left _ _))
    linarith
  refine ⟨C_max / (Real.log 2)^2, 2, 2, ?_, by norm_num, by norm_num, ?_⟩
  · have hlog2_sq_pos : 0 < (Real.log 2)^2 := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    exact div_pos hC_max_pos hlog2_sq_pos
  intro T hT_ge_2 hGood σ hσ
  have hT_pos : 0 < T := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_sq_pos : 0 < (Real.log 2)^2 := by positivity
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT_ge_2
  have hlogT_nn : 0 ≤ Real.log T := le_trans hlog2_pos.le hlogT_ge_log2
  have h_logT_sq_le : (Real.log T) ^ 2 ≤ T ^ 2 / (Real.log 2)^2 := by
    have h_logT_le_T : Real.log T ≤ T := by
      have := Real.log_le_sub_one_of_pos hT_pos
      linarith
    have h_sq_le : (Real.log T)^2 ≤ T^2 := by
      exact sq_le_sq' (by linarith : -T ≤ Real.log T) h_logT_le_T
    have h_inv_log2 : 1 ≤ 1 / (Real.log 2)^2 := by
      have h_log2_lt_one : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have h_log2_sq_lt_one : (Real.log 2)^2 < 1 := by
        have : (Real.log 2)^2 < 1^2 := by
          apply sq_lt_sq' <;> [linarith; exact h_log2_lt_one]
        linarith
      rw [le_div_iff₀ hlog2_sq_pos]; linarith
    calc (Real.log T)^2 ≤ T^2 := h_sq_le
      _ = T^2 * 1 := by ring
      _ ≤ T^2 * (1 / (Real.log 2)^2) :=
        mul_le_mul_of_nonneg_left h_inv_log2 (by positivity)
      _ = T^2 / (Real.log 2)^2 := by ring
  have hT_sq_rpow : T ^ (2:ℝ) = T ^ 2 := by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [hT_sq_rpow]
  by_cases hσ_le_0 : σ ≤ 0
  · have hσ_mem : σ ∈ Set.Icc (-1:ℝ) 0 := ⟨hσ.1, hσ_le_0⟩
    have h_bd := h_left_bd σ hσ_mem T hT_ge_2 hGood
    have h_C_le : C_left ≤ C_max := by
      rw [hC_max_def]
      have : C_left ≤ max (max C_crit C_left) C_right := by
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    calc ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖
        ≤ C_left * (Real.log T)^2 := h_bd
      _ ≤ C_max * (Real.log T)^2 := by
        apply mul_le_mul_of_nonneg_right h_C_le; positivity
      _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
        apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
      _ = C_max / (Real.log 2)^2 * T^2 := by ring
  · have hσ_gt_0 : 0 < σ := lt_of_not_ge hσ_le_0
    rcases lt_or_ge σ 1 with hσ_lt_1 | hσ_ge_1
    · have hσ_Ioo : σ ∈ Set.Ioo (0:ℝ) 1 := ⟨hσ_gt_0, hσ_lt_1⟩
      have h_bd := h_crit σ hσ_Ioo T hT_ge_2 hGood
      have h_C_le : C_crit ≤ C_max := by
        rw [hC_max_def]
        have : C_crit ≤ max (max C_crit C_left) C_right := by
          exact le_trans (le_max_left _ _) (le_max_left _ _)
        linarith
      calc ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖
          ≤ C_crit * (Real.log T)^2 := h_bd
        _ ≤ C_max * (Real.log T)^2 := by
          apply mul_le_mul_of_nonneg_right h_C_le; positivity
        _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
          apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
        _ = C_max / (Real.log 2)^2 * T^2 := by ring
    · have hσ_mem : σ ∈ Set.Icc (1:ℝ) 2 := ⟨hσ_ge_1, hσ.2⟩
      have h_bd := h_right_bd σ hσ_mem T hT_ge_2 hGood
      have h_C_le : C_right ≤ C_max := by
        rw [hC_max_def]
        have : C_right ≤ max (max C_crit C_left) C_right := le_max_right _ _
        linarith
      calc ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖
          ≤ C_right * (Real.log T)^2 := h_bd
        _ ≤ C_max * (Real.log T)^2 := by
          apply mul_le_mul_of_nonneg_right h_C_le; positivity
        _ ≤ C_max * (T^2 / (Real.log 2)^2) := by
          apply mul_le_mul_of_nonneg_left h_logT_sq_le hC_max_pos.le
        _ = C_max / (Real.log 2)^2 * T^2 := by ring

#print axioms full_strip_logDerivZeta_bound_neg_of_boundary

-- ═══════════════════════════════════════════════════════════════════════════
-- § Boundary-bound targets — to be filled unconditionally
-- ═══════════════════════════════════════════════════════════════════════════

/-- **leftOfCriticalStrip_target holds** — σ ∈ [-1, 0] at +T. Classical Landau
bound via FE transport to σ' = 1 − σ ∈ [1, 2] combined with `ζ'/ζ` bound on
Re = σ' ≥ 1. Uses: `CoshZetaSymmetry.riemannZeta_conj`-like FE identities,
`ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one (3/2)`,
`ZD.UniformGammaR.digamma_log_bound_uniform_sigma01`. -/
theorem leftOfCriticalStrip_holds : leftOfCriticalStrip_target := by
  sorry

/-- **rightOfCriticalStrip_target holds** — σ ∈ [1, 2] at +T. Uses
`ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one (1 + 1/2)` for
σ ∈ [3/2, 2] combined with an ad-hoc bound on σ ∈ [1, 3/2] via
`logDerivZeta_bounded_of_right_of_one σ` for varying σ₀ close to 1. -/
theorem rightOfCriticalStrip_holds : rightOfCriticalStrip_target := by
  sorry

/-- **leftOfCriticalStrip_neg_target holds** — mirror of
`leftOfCriticalStrip_holds` at `-T` via conjugation / zero-set symmetry.
Transports the `+T` bound through `ζ(conj s) = conj(ζ s)` and
`deriv ζ (conj s) = conj (deriv ζ s)` using `HasDerivAt.conj_conj`. -/
theorem leftOfCriticalStrip_neg_holds : leftOfCriticalStrip_neg_target := by
  obtain ⟨C, hC_pos, h_bd⟩ := leftOfCriticalStrip_holds
  refine ⟨C, hC_pos, ?_⟩
  intro σ hσ T hT hGood
  set s_pos : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_pos_def
  set s_neg : ℂ := (σ : ℂ) + (-T : ℂ) * I with hs_neg_def
  have h_star : s_neg = starRingEnd ℂ s_pos := by
    simp [hs_pos_def, hs_neg_def]
  have hT_pos : 0 < T := by linarith
  have hs_pos_ne : s_pos ≠ 1 := by
    intro h
    have him : s_pos.im = (1 : ℂ).im := by rw [h]
    simp [hs_pos_def] at him
    linarith
  have hs_neg_ne : s_neg ≠ 1 := by
    rw [h_star]
    intro h
    have him : (starRingEnd ℂ s_pos).im = (1 : ℂ).im := by rw [h]
    simp [hs_pos_def] at him
    linarith
  have h_diff_pos : DifferentiableAt ℂ riemannZeta s_pos :=
    differentiableAt_riemannZeta hs_pos_ne
  have h1 := h_diff_pos.hasDerivAt.conj_conj
  have h_eq : (⇑(starRingEnd ℂ) ∘ riemannZeta ∘ ⇑(starRingEnd ℂ))
      =ᶠ[nhds (starRingEnd ℂ s_pos)] riemannZeta := by
    have h_open : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have h_mem : starRingEnd ℂ s_pos ∈ ({1}ᶜ : Set ℂ) := by
      rw [← h_star]; exact hs_neg_ne
    filter_upwards [h_open.mem_nhds h_mem] with z hz
    have hz' : z ≠ 1 := hz
    show starRingEnd ℂ (riemannZeta (starRingEnd ℂ z)) = riemannZeta z
    rw [CoshZetaSymmetry.riemannZeta_conj z hz']
    simp
  have h2 := h1.congr_of_eventuallyEq h_eq.symm
  have h_deriv_star :
      deriv riemannZeta (starRingEnd ℂ s_pos)
        = starRingEnd ℂ (deriv riemannZeta s_pos) := h2.deriv
  have h_zeta_star : riemannZeta s_neg = starRingEnd ℂ (riemannZeta s_pos) := by
    rw [h_star]; exact CoshZetaSymmetry.riemannZeta_conj s_pos hs_pos_ne
  have h_deriv_star' :
      deriv riemannZeta s_neg = starRingEnd ℂ (deriv riemannZeta s_pos) := by
    rw [h_star]; exact h_deriv_star
  have h_quot_star : deriv riemannZeta s_neg / riemannZeta s_neg
      = starRingEnd ℂ (deriv riemannZeta s_pos / riemannZeta s_pos) := by
    rw [h_deriv_star', h_zeta_star, map_div₀]
  rw [h_quot_star, Complex.norm_conj]
  exact h_bd σ hσ T hT hGood

/-- **rightOfCriticalStrip_neg_target holds** — mirror of
`rightOfCriticalStrip_holds` at `-T`. Uses conjugation via
`CoshZetaSymmetry.riemannZeta_conj` and `deriv_riemannZeta_conj`:
`σ + (-T)i = conj (σ + T i)`, and `‖conj (ζ' s)/conj (ζ s)‖ = ‖ζ'(s)/ζ(s)‖`. -/
theorem rightOfCriticalStrip_neg_holds : rightOfCriticalStrip_neg_target := by
  sorry

/-- **Helper: derivative of `riemannZeta` conjugates.** For `s ≠ 1`,
`deriv ζ (conj s) = conj (deriv ζ s)`. Follows from `riemannZeta_conj` +
`deriv_conj_conj` on the open set `ℂ \ {1}`. -/
theorem deriv_riemannZeta_conj (s : ℂ) (hs : s ≠ 1) :
    deriv riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannZeta s) := by
  have h_eventually :
      (fun z => starRingEnd ℂ (riemannZeta (starRingEnd ℂ z))) =ᶠ[nhds s] riemannZeta := by
    have h_open : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
    have hs_mem : s ∈ {z : ℂ | z ≠ 1} := hs
    filter_upwards [h_open.mem_nhds hs_mem] with z hz
    have := CoshZetaSymmetry.riemannZeta_conj z hz
    rw [this]; simp
  have h1 : deriv (fun z => starRingEnd ℂ (riemannZeta (starRingEnd ℂ z))) s
          = deriv riemannZeta s :=
    Filter.EventuallyEq.deriv_eq h_eventually
  have h2 : deriv (fun z => starRingEnd ℂ (riemannZeta (starRingEnd ℂ z)))
            = fun z => starRingEnd ℂ (deriv riemannZeta (starRingEnd ℂ z)) := by
    change deriv (starRingEnd ℂ ∘ riemannZeta ∘ starRingEnd ℂ) = _
    rw [deriv_conj_conj]; rfl
  rw [h2] at h1
  have := congrArg (starRingEnd ℂ) h1
  simp at this
  exact this

/-- **criticalStripLandau_neg_target holds** — `criticalStripLandau_of_goodHeight`
at `-T`. Uses conjugation via `CoshZetaSymmetry.riemannZeta_conj` and
`deriv_riemannZeta_conj`: `σ + (-T)i = conj (σ + T i)`, and
`‖conj (ζ' s)/conj (ζ s)‖ = ‖ζ'(s)/ζ(s)‖`. -/
theorem criticalStripLandau_neg_holds : criticalStripLandau_neg_target := by
  obtain ⟨C, hC_pos, h_bd⟩ := criticalStripLandau_of_goodHeight
  refine ⟨C, hC_pos, ?_⟩
  intro σ hσ T hT_ge_2 hGood
  have h_conj_eq : (σ : ℂ) + (-T : ℂ) * I = starRingEnd ℂ ((σ : ℂ) + (T : ℂ) * I) := by
    apply Complex.ext <;> simp
  have hs_ne_1 : ((σ : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro h
    have him : ((σ : ℂ) + (T : ℂ) * I).im = (1 : ℂ).im := by rw [h]
    simp at him
    linarith
  rw [h_conj_eq]
  have h_zeta := CoshZetaSymmetry.riemannZeta_conj _ hs_ne_1
  have h_deriv := deriv_riemannZeta_conj _ hs_ne_1
  rw [h_zeta, h_deriv, ← map_div₀, Complex.norm_conj]
  exact h_bd σ hσ T hT_ge_2 hGood

/-- **FullStripLogDerivInputs unconditional** — assembles the `pos` and `neg`
field bounds from the individual boundary targets (Steps 6 + 7 in the plan). -/
theorem fullStripLogDerivInputs_of_boundary : FullStripLogDerivInputs :=
  { pos := full_strip_logDerivZeta_bound_pos_of_boundary
      leftOfCriticalStrip_holds rightOfCriticalStrip_holds
    neg := full_strip_logDerivZeta_bound_neg_of_boundary
      criticalStripLandau_neg_holds
      leftOfCriticalStrip_neg_holds rightOfCriticalStrip_neg_holds }

#print axioms fullStripLogDerivInputs_of_boundary

/-- **h_top discharge (conditional).** Given the full-strip polynomial bound
with `N < 4`, the top edge vanishes. -/
theorem h_top_of_full_strip_logDeriv (β : ℝ)
    (h_ld : full_strip_logDerivZeta_bound_N_lt_4_target) :
    topEdgeVanishes_target β (-1) 2 := by
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ, hT₀_ζ, hN_lt, hLD⟩ := h_ld
  -- Package as `uniform_logDerivZeta_bound_target` for the main bundle arg.
  have h_uniform : uniform_logDerivZeta_bound_target (-1) 2 :=
    ⟨C_ζ, N, T₀_ζ, hC_ζ, hT₀_ζ, hLD⟩
  exact topEdgeVanishes_of_ldBound_and_quartic β (by norm_num : (-1:ℝ) ≤ 2)
    h_uniform (uniform_pairMellin_quartic_target_pos β)
    ⟨C_ζ, N, T₀_ζ, hC_ζ, hT₀_ζ, hN_lt, hLD⟩

#print axioms h_top_of_full_strip_logDeriv

/-- **h_bottom discharge (conditional).** Given the full-strip polynomial
bound at imaginary part `-T`, the bottom edge vanishes. -/
theorem h_bottom_of_full_strip_logDeriv (β : ℝ)
    (h_ld_neg : full_strip_logDerivZeta_bound_N_lt_4_neg_target) :
    bottomEdgeVanishes_target β (-1) 2 := by
  have h_M_neg := uniform_pairMellin_quartic_target_neg β
  exact bottomEdgeVanishes_of_ldBound_and_quartic β (by norm_num : (-1:ℝ) ≤ 2)
    h_ld_neg h_M_neg

#print axioms h_bottom_of_full_strip_logDeriv

-- ═══════════════════════════════════════════════════════════════════════════
-- § Arch-prime cancellation at σ = 2: vertical-edge target
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Arch-prime cancellation target at σ = 2 for the pair-cosh-Gauss test.**
The vertical-edge difference form consumed by
`vertEdgeDiffVanishes_of_archPrimeCancel` at `σL = -1, σR = 2`. -/
def archPrimeCancel_target (β : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖(∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          (((2 : ℝ) : ℂ) + (y : ℝ) * I))
      - (∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ)) : ℂ) + (y : ℝ) * I))‖ < ε

/-- Finite-height FE transport for the vertical edges: the right-minus-left
edge integral is exactly the finite reflected-prime integral on the right edge
`σ = 2`. This is the finite-interval form needed before taking `T → ∞`. -/
def verticalEdges_eq_reflectedPrime_target (β : ℝ) : Prop :=
  ∀ T : ℝ, goodHeight T →
    (∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          (((2 : ℝ) : ℂ) + (y : ℝ) * I))
      - (∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ)) : ℂ) + (y : ℝ) * I))
    = ∫ y : ℝ in (-T : ℝ)..T, Contour.reflectedPrimeIntegrand β 2 y

/-- Finite reflected-prime cancellation: the symmetric interval integrals of
the reflected-prime integrand tend to zero. A common route is integrability of
`reflectedPrimeIntegrand β 2`, convergence of `∫[-T,T]` to the whole-line
integral, and the whole-line identity `∫ reflectedPrimeIntegrand β 2 = 0`. -/
def reflectedPrimeIntervalVanishes_target (β : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    ‖∫ y : ℝ in (-T : ℝ)..T, Contour.reflectedPrimeIntegrand β 2 y‖ < ε

/-- Symmetric finite-interval reflected-prime cancellation from the standard
improper-integral theorem. This discharges the limiting part once the
reflected-prime integrand is integrable and its whole-line integral is zero. -/
theorem reflectedPrimeIntervalVanishes_of_integrable_integral_eq_zero (β : ℝ)
    (h_int : MeasureTheory.Integrable (Contour.reflectedPrimeIntegrand β 2))
    (h_zero : (∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y) = 0) :
    reflectedPrimeIntervalVanishes_target β := by
  intro ε hε
  have h_tendsto :
      Filter.Tendsto
        (fun T : ℝ => ∫ y : ℝ in (-T : ℝ)..T, Contour.reflectedPrimeIntegrand β 2 y)
        Filter.atTop (nhds (0 : ℂ)) := by
    simpa [h_zero] using
      (MeasureTheory.intervalIntegral_tendsto_integral
        (μ := MeasureTheory.volume)
        (f := Contour.reflectedPrimeIntegrand β 2)
        h_int Filter.tendsto_neg_atTop_atBot Filter.tendsto_id)
  have h_ball : Metric.ball (0 : ℂ) ε ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds _ hε
  have h_eventually := h_tendsto.eventually h_ball
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨T₁, hT₁⟩ := h_eventually
  refine ⟨max T₁ 1, by positivity, ?_⟩
  intro T hT
  have hT_ge_T₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hmem := hT₁ T hT_ge_T₁
  simpa [dist_eq_norm] using hmem

#print axioms reflectedPrimeIntervalVanishes_of_integrable_integral_eq_zero

/-- Sharper arch-prime input bundle. This splits the vertical-edge target into
the finite FE transport identity and the reflected-prime vanishing limit. -/
structure ArchPrimeCancelInputs (β : ℝ) : Prop where
  edge_reflected : verticalEdges_eq_reflectedPrime_target β
  reflected_vanishes : reflectedPrimeIntervalVanishes_target β

/-- The pair-combined arch/prime identity supplies the whole-line reflected-prime
zero; together with the already-proved integrability at `σ = 2`, this gives the
finite symmetric-interval vanishing required by final assembly. -/
theorem reflectedPrimeIntervalVanishes_of_archPair (β : ℝ)
    (h_pair :
      ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β) :
    reflectedPrimeIntervalVanishes_target β := by
  exact reflectedPrimeIntervalVanishes_of_integrable_integral_eq_zero β
    (Contour.reflectedPrimeIntegrand_integrable_at_two β)
    ((ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes
      β).mp h_pair)

/-- Current sharp arch-prime provider: the only remaining inputs are the finite
vertical-edge FE transport identity and the pair-combined arch/prime identity.
This avoids restating whole-line reflected-prime vanishing as an independent
assumption. -/
theorem archPrimeCancelInputs_of_edge_and_archPair (β : ℝ)
    (h_edge : verticalEdges_eq_reflectedPrime_target β)
    (h_pair :
      ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β) :
    ArchPrimeCancelInputs β :=
  ⟨h_edge, reflectedPrimeIntervalVanishes_of_archPair β h_pair⟩

/-- The sharper reflected-prime inputs imply the vertical arch-prime
cancellation target consumed by final assembly. -/
theorem archPrimeCancel_of_reflectedPrime_inputs (β : ℝ)
    (h : ArchPrimeCancelInputs β) :
    archPrimeCancel_target β := by
  intro ε hε
  obtain ⟨T₀, hT₀_pos, hT₀⟩ := h.reflected_vanishes ε hε
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT hgood
  rw [h.edge_reflected T hgood]
  exact hT₀ T hT

#print axioms archPrimeCancel_of_reflectedPrime_inputs

/-- **h_vert_cancel discharge (conditional).** Direct re-export via the
existing edge-to-target theorem. -/
theorem h_vert_cancel_of_archPrimeCancel (β : ℝ)
    (h_cancel : archPrimeCancel_target β) :
    vertEdgeDiffVanishes_target β (-1) 2 :=
  vertEdgeDiffVanishes_of_archPrimeCancel β h_cancel

#print axioms h_vert_cancel_of_archPrimeCancel

-- ═══════════════════════════════════════════════════════════════════════════
-- § h_rect_vanishes — assembly from the three edge-level hypotheses
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`h_rect_vanishes` unconditional up to two explicit analytic inputs.**
Assembles the three edge-level theorems and the triangle-inequality glue into
`rectangleVanishes_target β` for every β ∈ (0, 1). The two remaining
hypotheses are the full-strip ζ'/ζ polynomial bound (classical Landau on
`[-1, 2]`) and the arch-prime cancellation at σ = 2 (cosh-pair π/6 balance +
FE transport from left edge). -/
theorem h_rect_vanishes_of_logDeriv_and_archPrimeCancel
    (h_ld_pos : full_strip_logDerivZeta_bound_N_lt_4_target)
    (h_ld_neg : full_strip_logDerivZeta_bound_N_lt_4_neg_target)
    (h_cancel : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → archPrimeCancel_target β) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → rectangleVanishes_target β :=
  fun β hβ =>
    rectangleVanishes_of_edges β hβ
      (h_top_of_full_strip_logDeriv β h_ld_pos)
      (h_bottom_of_full_strip_logDeriv β h_ld_neg)
      (h_vert_cancel_of_archPrimeCancel β (h_cancel β hβ))

#print axioms h_rect_vanishes_of_logDeriv_and_archPrimeCancel

/-- **Classical Weil explicit formula assembly.** All six hypotheses of
`weil_explicit_formula_classical` are supplied by the wrappers above, leaving
only the two full-strip ζ'/ζ polynomial bounds and the vertical arch-prime
cancellation target as explicit analytic inputs. -/
theorem weil_explicit_formula_classical_of_logDeriv_and_archPrimeCancel
    (h_ld_pos : full_strip_logDerivZeta_bound_N_lt_4_target)
    (h_ld_neg : full_strip_logDerivZeta_bound_N_lt_4_neg_target)
    (h_cancel : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → archPrimeCancel_target β) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
  weil_explicit_formula_classical
    h_rect_residue_unconditional
    (fun β _hβ => h_sum_unconditional β)
    h_fin_unconditional
    (fun β _hβ => h_top_of_full_strip_logDeriv β h_ld_pos)
    (fun β _hβ => h_bottom_of_full_strip_logDeriv β h_ld_neg)
    (fun β hβ => h_vert_cancel_of_archPrimeCancel β (h_cancel β hβ))

#print axioms weil_explicit_formula_classical_of_logDeriv_and_archPrimeCancel

/-- Final assembly from the bundled analytic inputs. This is the clean handoff
shape for the remaining work: one full-strip log-derivative bundle and one
arch-prime/reflected-prime bundle for every `β ∈ (0, 1)`. -/
theorem weil_explicit_formula_classical_of_analytic_inputs
    (h_ld : FullStripLogDerivInputs)
    (h_arch : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → ArchPrimeCancelInputs β) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
  weil_explicit_formula_classical_of_logDeriv_and_archPrimeCancel
    h_ld.pos h_ld.neg
    (fun β hβ => archPrimeCancel_of_reflectedPrime_inputs β (h_arch β hβ))

#print axioms weil_explicit_formula_classical_of_analytic_inputs

-- ═══════════════════════════════════════════════════════════════════════════
-- § Remaining unconditional providers
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Remaining Landau provider, positive height.**

This is the closed full-strip version needed by the top horizontal edge:
`ζ'/ζ(σ+iT)` is polynomially bounded on `σ ∈ [-1, 2]` at every sufficiently
large strong `goodHeight T`, with exponent strictly below the quartic Mellin
decay.

Expected route:
* `σ ∈ [1, 2]`: use `Contour.logDerivZeta_bounded_of_right_of_one`.
* `σ ∈ (0, 1)`: use `criticalStripLandau_of_goodHeight`.
* `σ ∈ [-3/4, -1/2]`: use `Contour.LeftSlab.logDerivZeta_bound_left_slab`.
* Fill the remaining left-strip gaps `[-1, -3/4]`, `[-1/2, 0]`, and the
  boundary lines by functional-equation transport plus Γℝ log-derivative
  bounds.
* Absorb all `C * (Real.log T)^2` bounds into `C' * T^2` for large `T`, so
  choose `N = 2`.
-/
theorem full_strip_logDerivZeta_bound_N_lt_4_unconditional :
    full_strip_logDerivZeta_bound_N_lt_4_target := by
  sorry

/-- **Remaining Landau provider, negative height.**

This is the bottom-edge analogue of
`full_strip_logDerivZeta_bound_N_lt_4_unconditional`.  The intended proof is
to transport the positive-height full-strip bound by conjugation:
`ζ (conj s) = conj (ζ s)`, derivative compatibility for `riemannZeta`, and
norm invariance under conjugation.  Strong `goodHeight T` already contains
both `+T` and `-T` zero-avoidance data.
-/
theorem full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional :
    full_strip_logDerivZeta_bound_N_lt_4_neg_target := by
  sorry

/-- **Closed full-strip log-derivative input bundle.**

Once the positive and negative full-strip Landau providers above are proved,
this is just the bundled input consumed by
`weil_explicit_formula_classical_of_analytic_inputs`.
-/
theorem fullStripLogDerivInputs_unconditional : FullStripLogDerivInputs :=
  ⟨full_strip_logDerivZeta_bound_N_lt_4_unconditional,
    full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional⟩

/-- **Remaining finite-height FE transport for the vertical edges.**

For each finite good height `T`, prove that the right-minus-left vertical edge
integral over `[-T, T]` is exactly the reflected-prime integral on the right
edge `σ = 2`.

Expected route:
* Right edge `σ = 2`: rewrite `weilIntegrand (pairTestMellin β)` using the
  corrected arch/prime/reflected pointwise identity already used in
  `ArchOperatorBound.weilArchPrimeIdentityTarget_at_two`.
* Left edge `σ = -1`: apply the functional equation and the substitution
  `1 - (-1 + iy) = 2 - iy`.
* Use orientation/substitution on interval integrals and conjugation/evenness
  of the pair test to align the finite interval with the right-edge
  reflected-prime integral.
* Use `goodHeight T` only for the zero/pole avoidance needed to justify the
  pointwise functional-equation rewrites on the finite contour.
-/
theorem verticalEdges_eq_reflectedPrime_unconditional (β : ℝ) :
    verticalEdges_eq_reflectedPrime_target β := by
  sorry

/-- **Remaining pair-combined arch/prime identity at `σ = 2`.**

This is the hard cosh-pair cancellation input: the five-term arch side equals
the five-term prime side.  The surrounding file
`WeilReflectedPrimeVanishingWeilside.lean` already proves the two mechanical
expansions and the equivalence with whole-line reflected-prime cancellation.

Expected route:
* Finish the pair-combined `H3` proof, not the false per-cosh identity.
* Use the von Mangoldt expansion on `Re s = 2`, Mellin inversion for the
  cosh-Gauss pieces, and the functional equation expansion of the reflected
  log derivative.
* The π/6 pair axes should cancel the Γℝ terms in the five-term combination.
-/
theorem archPair_eq_primePair_at_two_unconditional (β : ℝ) :
    ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β := by
  sorry

/-- **Closed arch-prime/reflected-prime input bundle.**

This packages the two remaining vertical-edge facts:
finite FE transport and pair-combined whole-line cancellation.  The limiting
step from whole-line cancellation to symmetric interval cancellation is already
proved by `reflectedPrimeIntervalVanishes_of_archPair`, using
`Contour.reflectedPrimeIntegrand_integrable_at_two`.
-/
theorem archPrimeCancelInputs_unconditional (β : ℝ) :
    ArchPrimeCancelInputs β :=
  archPrimeCancelInputs_of_edge_and_archPair β
    (verticalEdges_eq_reflectedPrime_unconditional β)
    (archPair_eq_primePair_at_two_unconditional β)

/-- **Unconditional classical Weil explicit formula for the pair-cosh-Gauss
test.**

This is the desired closed endpoint.  After the four provider stubs above are
filled, this theorem should have only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.
-/
theorem weil_explicit_formula_classical_unconditional :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
  weil_explicit_formula_classical_of_analytic_inputs
    fullStripLogDerivInputs_unconditional
    (fun β _hβ => archPrimeCancelInputs_unconditional β)

#print axioms weil_explicit_formula_classical_unconditional

end FinalAssembly
end WeilPositivity
end ZD

end
