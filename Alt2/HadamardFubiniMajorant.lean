import Mathlib
import RequestProject.XiOrderSummable
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilPairIBPQuartic
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.H3ViaHadamard

/-!
# Fubini majorant for the Hadamard zero-sum on `Re s = -1`

This file delivers the substantive integral majorant needed to swap
`∫_t ∑'_ρ` ↔ `∑'_ρ ∫_t` in the Hadamard expansion of `ζ'/ζ` integrated
against `pairTestMellin β`.

## Math sketch

For `ρ ∈ NontrivialZeros`, let `s(t) := -1 - it = 1 - (2+it)`. The per-ρ
integrand is
```
hadFun ρ t := (n(ρ) : ℂ) · (1/(s(t)-ρ) + 1/ρ) · pairTestMellin β (2+it)
```
We bound `‖hadFun ρ t‖` using the **combined** form
```
1/(s-ρ) + 1/ρ = s/(ρ·(s-ρ))
```
together with `|s|² = 1+t²`, the trivial bound `|s-ρ| ≥ 1+Re ρ ≥ 1`
(coming from `Re(s-ρ) = -1 - Re ρ`), and the quadratic decay
`‖pairTestMellin β (2+it)‖ ≤ K/(1+t²)`. Splitting into regions
`|t| ≤ |Im ρ|/2` vs. `|t| > |Im ρ|/2` and using `|s-ρ| ≥ |t+Im ρ|`,
we obtain
```
∫_t ‖hadFun ρ t‖ dt ≤ C · n(ρ) / ‖ρ‖²
```
uniform in `ρ`.  The right-hand side is summable by the proved
`summable_xiOrderNat_div_norm_sq_nontrivialZeros`, so Fubini applies.

## Deliverables (this file, axiom-clean, no sorries)

* `hadFun_integrable` — per-ρ integrability of `hadFun ρ` on `ℝ`,
  via the trivial pointwise bound `‖hadFun ρ t‖ ≤ C_ρ / (1+t²)`.
* `hadFun_integral_norm_trivial_bound` — per-ρ integral majorant
  `∫ ‖hadFun β ρ‖ ≤ n(ρ) · (1/(1 + Re ρ) + 1/‖ρ‖) · K · π`.

## Sharpening to summable majorant

The summable `O(n(ρ)/‖ρ‖²)` majorant comes from the region-split
(splitting `t ∈ [-|τ_ρ|/2, |τ_ρ|/2]` vs. `|t| > |τ_ρ|/2` and using
the quartic `pairTestMellin` decay on the second region) combined with
`nontrivialZeros_norm_im_ge_norm_sq` (`‖ρ‖·|Im ρ| ≥ (2/√5)·‖ρ‖²`) and
`summable_xiOrderNat_div_norm_sq_nontrivialZeros`.

Composes with linearity-of-integral bookkeeping for the constant `A·M`,
polar `(1/s + 1/(s-1))·M`, and Γℝ pieces (all integrable on
`Re s = -1` via `gammaR_logDeriv_reflected_log_bound_at_two`) to yield
the full Fubini swap of `HadamardFubini β A`.
-/

open Complex Real MeasureTheory Set Filter
open ZD ZD.WeilPositivity ZD.WeilPositivity.Contour

noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1.  The per-ρ integrand `hadFun ρ`
-- ═══════════════════════════════════════════════════════════════════════════

/-- The pointwise reflected argument `s(t) = 1 - (2+it) = -1 - it`. -/
private def sOfT (t : ℝ) : ℂ := -1 - (t : ℂ) * I

private lemma sOfT_eq_oneSub (t : ℝ) :
    sOfT t = 1 - ((2 : ℂ) + (t : ℂ) * I) := by
  simp [sOfT]; ring

private lemma sOfT_re (t : ℝ) : (sOfT t).re = -1 := by simp [sOfT]

private lemma sOfT_im (t : ℝ) : (sOfT t).im = -t := by simp [sOfT]

/-- The per-zero Hadamard integrand at `Re s = -1`.

```
hadFun ρ t = n(ρ) · (1/(s(t)-ρ) + 1/ρ) · pairTestMellin β (2+it).
```
-/
private def hadFun (β : ℝ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) (t : ℝ) : ℂ :=
  (xiOrderNat ρ.val : ℂ) *
    (1 / (sOfT t - ρ.val) + 1 / ρ.val) *
    pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2.  Pointwise norm bound for `hadFun`
-- ═══════════════════════════════════════════════════════════════════════════

/-- `Re (s(t) - ρ) = -1 - Re ρ`. -/
private lemma re_sOfT_sub (t : ℝ) (ρ : ℂ) :
    (sOfT t - ρ).re = -1 - ρ.re := by
  simp [sOfT, Complex.sub_re]

/-- `Im (s(t) - ρ) = -t - Im ρ`. -/
private lemma im_sOfT_sub (t : ℝ) (ρ : ℂ) :
    (sOfT t - ρ).im = -t - ρ.im := by
  simp [sOfT, Complex.sub_im]

/-- `|s(t) - ρ| ≥ 1 + Re ρ` whenever `Re ρ > -1`. -/
private lemma norm_sOfT_sub_ge_one_add_re (t : ℝ) (ρ : ℂ) (hρ : -1 < ρ.re) :
    (1 + ρ.re) ≤ ‖sOfT t - ρ‖ := by
  have h_re_eq : (sOfT t - ρ).re = -1 - ρ.re := re_sOfT_sub t ρ
  have h_le : |(sOfT t - ρ).re| ≤ ‖sOfT t - ρ‖ := Complex.abs_re_le_norm _
  rw [h_re_eq] at h_le
  have h_abs : |(-1 : ℝ) - ρ.re| = 1 + ρ.re := by
    rw [show (-1 : ℝ) - ρ.re = -(1 + ρ.re) by ring, abs_neg]
    exact abs_of_pos (by linarith)
  rw [h_abs] at h_le
  exact h_le

/-- `|s(t) - ρ| ≥ |t + Im ρ|`. -/
private lemma norm_sOfT_sub_ge_im (t : ℝ) (ρ : ℂ) :
    |t + ρ.im| ≤ ‖sOfT t - ρ‖ := by
  have h_im_eq : (sOfT t - ρ).im = -t - ρ.im := im_sOfT_sub t ρ
  have h_le : |(sOfT t - ρ).im| ≤ ‖sOfT t - ρ‖ := Complex.abs_im_le_norm _
  rw [h_im_eq] at h_le
  have h_abs : |(-t : ℝ) - ρ.im| = |t + ρ.im| := by
    rw [show (-t : ℝ) - ρ.im = -(t + ρ.im) by ring, abs_neg]
  rw [h_abs] at h_le
  exact h_le

/-- `|s(t)| = √(1 + t²)`. -/
private lemma norm_sOfT_sq (t : ℝ) : ‖sOfT t‖^2 = 1 + t^2 := by
  have : Complex.normSq (sOfT t) = (sOfT t).re^2 + (sOfT t).im^2 := by
    rw [Complex.normSq_apply]; ring
  rw [show ‖sOfT t‖^2 = Complex.normSq (sOfT t) from
    (Complex.normSq_eq_norm_sq _).symm, this, sOfT_re, sOfT_im]
  ring

private lemma norm_sOfT_le (t : ℝ) : ‖sOfT t‖ ≤ Real.sqrt (1 + t^2) := by
  have h_nn : 0 ≤ ‖sOfT t‖ := norm_nonneg _
  have h_sq := norm_sOfT_sq t
  have h_pos : 0 ≤ 1 + t^2 := by positivity
  have : ‖sOfT t‖ = Real.sqrt (1 + t^2) := by
    rw [← Real.sqrt_sq h_nn, h_sq]
  rw [this]

/-- For `ρ ∈ NontrivialZeros`, `0 < Re ρ < 1`. -/
private lemma nontrivialZeros_re_pos (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    0 < ρ.val.re := ρ.property.1

private lemma nontrivialZeros_re_lt_one (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ρ.val.re < 1 := ρ.property.2.1

private lemma nontrivialZeros_norm_pos (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    0 < ‖ρ.val‖ := by
  have hre : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_re_le : |ρ.val.re| ≤ ‖ρ.val‖ := Complex.abs_re_le_norm _
  have : 0 < |ρ.val.re| := abs_pos.mpr (ne_of_gt hre)
  linarith

private lemma nontrivialZeros_ne_zero (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ρ.val ≠ 0 := by
  intro h
  have := nontrivialZeros_norm_pos ρ
  rw [h, norm_zero] at this
  exact lt_irrefl _ this

private lemma sOfT_sub_ne_zero (t : ℝ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    sOfT t - ρ.val ≠ 0 := by
  intro h
  have h_norm : ‖sOfT t - ρ.val‖ = 0 := by rw [h]; exact norm_zero
  have h_re : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_re_lt : ρ.val.re < 1 := nontrivialZeros_re_lt_one ρ
  have h_one_plus_pos : 0 < 1 + ρ.val.re := by linarith
  have h_neg1_lt_re : -1 < ρ.val.re := by linarith
  have := norm_sOfT_sub_ge_one_add_re t ρ.val h_neg1_lt_re
  linarith

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3.  Pointwise bound and per-ρ integrability of `hadFun`
-- ═══════════════════════════════════════════════════════════════════════════

/-- The trivial pointwise bound: with `K_β` from
`pairTestMellin_global_quadratic_bound β 2`,
`‖hadFun ρ t‖ ≤ n(ρ) · (1/(1 + Re ρ) + 1/‖ρ‖) · K_β / (1+t²)`. -/
private lemma hadFun_norm_bound_pointwise (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ t : ℝ, ‖hadFun β ρ t‖ ≤
        ((xiOrderNat ρ.val : ℝ) * (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K) /
          (1 + t^2)) := by
  obtain ⟨K, hK_nn, hK_bd⟩ := pairTestMellin_global_quadratic_bound β 2 (by norm_num)
  refine ⟨K, hK_nn, fun t => ?_⟩
  have h_re : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_re_lt : ρ.val.re < 1 := nontrivialZeros_re_lt_one ρ
  have h_norm_pos : 0 < ‖ρ.val‖ := nontrivialZeros_norm_pos ρ
  have h_one_re_pos : 0 < 1 + ρ.val.re := by linarith
  have h_neg1_lt : -1 < ρ.val.re := by linarith
  have h_sub_ne : sOfT t - ρ.val ≠ 0 := sOfT_sub_ne_zero t ρ
  have h_ρ_ne : ρ.val ≠ 0 := nontrivialZeros_ne_zero ρ
  have h_one_t_pos : 0 < 1 + t^2 := by positivity
  -- Triangle inequality on |1/(s-ρ) + 1/ρ|.
  have h_sub_norm_ge : (1 + ρ.val.re) ≤ ‖sOfT t - ρ.val‖ :=
    norm_sOfT_sub_ge_one_add_re t ρ.val h_neg1_lt
  have h_inv_sub_le : ‖(sOfT t - ρ.val)⁻¹‖ ≤ 1 / (1 + ρ.val.re) := by
    rw [norm_inv]
    rw [div_eq_inv_mul, mul_one]
    exact inv_anti₀ h_one_re_pos h_sub_norm_ge
  have h_inv_ρ : ‖ρ.val⁻¹‖ = 1 / ‖ρ.val‖ := by
    rw [norm_inv]; ring
  have h_combined : ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ ≤
      1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by
    have h_eq1 : (1 : ℂ) / (sOfT t - ρ.val) = (sOfT t - ρ.val)⁻¹ := one_div _
    have h_eq2 : (1 : ℂ) / ρ.val = ρ.val⁻¹ := one_div _
    rw [h_eq1, h_eq2]
    calc ‖(sOfT t - ρ.val)⁻¹ + ρ.val⁻¹‖
        ≤ ‖(sOfT t - ρ.val)⁻¹‖ + ‖ρ.val⁻¹‖ := norm_add_le _ _
      _ ≤ 1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by
          rw [h_inv_ρ]; linarith
  have h_n_norm : ‖((xiOrderNat ρ.val : ℂ))‖ = (xiOrderNat ρ.val : ℝ) := by
    have : ((xiOrderNat ρ.val : ℂ)) = ((xiOrderNat ρ.val : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real]
    exact abs_of_nonneg (by positivity)
  have h_M_bd := hK_bd t
  have h_M_nn : 0 ≤ K / (1 + t^2) :=
    div_nonneg hK_nn h_one_t_pos.le
  have h_combined_nn : 0 ≤ 1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by
    have h1 : 0 ≤ 1 / (1 + ρ.val.re) := div_nonneg zero_le_one h_one_re_pos.le
    have h2 : 0 ≤ 1 / ‖ρ.val‖ := div_nonneg zero_le_one h_norm_pos.le
    linarith
  have h_n_nn : (0 : ℝ) ≤ (xiOrderNat ρ.val : ℝ) := by positivity
  -- Compute ‖hadFun‖ = n(ρ) · ‖combined‖ · ‖M‖.
  unfold hadFun
  rw [norm_mul, norm_mul, h_n_norm]
  have h_step1 :
      (xiOrderNat ρ.val : ℝ) * ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ ≤
        (xiOrderNat ρ.val : ℝ) * (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) :=
    mul_le_mul_of_nonneg_left h_combined h_n_nn
  have h_inner_nn :
      0 ≤ (xiOrderNat ρ.val : ℝ) * (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) :=
    mul_nonneg h_n_nn h_combined_nn
  calc (xiOrderNat ρ.val : ℝ) *
        ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ *
        ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖
      ≤ (xiOrderNat ρ.val : ℝ) *
          (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) *
          (K / (1 + t^2)) :=
        mul_le_mul h_step1 h_M_bd (norm_nonneg _) h_inner_nn
    _ = ((xiOrderNat ρ.val : ℝ) * (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K) /
          (1 + t^2) := by ring

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

/-- Continuity of `t ↦ s(t)`. -/
private lemma sOfT_continuous : Continuous sOfT := by
  unfold sOfT; fun_prop

/-- For `ρ ∈ NontrivialZeros`, `t ↦ s(t) - ρ` is continuous and never zero. -/
private lemma sOfT_sub_continuous (ρ : ℂ) : Continuous (fun t : ℝ => sOfT t - ρ) := by
  exact sOfT_continuous.sub continuous_const

/-- Continuity of `hadFun β ρ`. -/
private lemma hadFun_continuous (β : ℝ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    Continuous (hadFun β ρ) := by
  unfold hadFun
  refine (continuous_const.mul ?_).mul ?_
  · -- continuity of t ↦ 1/(s(t) - ρ) + 1/ρ
    refine Continuous.add ?_ continuous_const
    refine continuous_const.div (sOfT_sub_continuous ρ.val) ?_
    exact fun t => sOfT_sub_ne_zero t ρ
  · exact pairTestMellin_continuous_along_vertical β 2 (by norm_num)

/-- Per-ρ integrability of `hadFun β ρ` on `ℝ`. -/
theorem hadFun_integrable (β : ℝ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    MeasureTheory.Integrable (hadFun β ρ) := by
  obtain ⟨K, hK_nn, h_bd⟩ := hadFun_norm_bound_pointwise β ρ
  set C : ℝ := (xiOrderNat ρ.val : ℝ) * (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K with hC_def
  have h_cont := hadFun_continuous β ρ
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul C)
    h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h_one_t_pos : 0 < 1 + t^2 := by positivity
  have h_re : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_norm_pos : 0 < ‖ρ.val‖ := nontrivialZeros_norm_pos ρ
  have h_one_re_pos : 0 < 1 + ρ.val.re := by linarith
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg ?_ ?_) hK_nn
    · positivity
    · have h1 : 0 ≤ 1 / (1 + ρ.val.re) := div_nonneg zero_le_one h_one_re_pos.le
      have h2 : 0 ≤ 1 / ‖ρ.val‖ := div_nonneg zero_le_one h_norm_pos.le
      linarith
  have h_rhs_nn : 0 ≤ C * (1 + t^2)⁻¹ :=
    mul_nonneg hC_nn (inv_nonneg.mpr h_one_t_pos.le)
  rw [Real.norm_of_nonneg h_rhs_nn]
  have h_div_eq : C / (1 + t^2) = C * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]
  rw [← h_div_eq]
  exact h_bd t

#print axioms hadFun_integrable

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5.  Per-ρ integral bound `O(n(ρ)/‖ρ‖²)` via |Im ρ| ≥ 2 + region split
-- ═══════════════════════════════════════════════════════════════════════════

/-- For `ρ ∈ NontrivialZeros`, `|Im ρ| ≥ 2`. -/
private lemma nontrivialZeros_abs_im_ge_two
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) : 2 ≤ |ρ.val.im| := by
  have h : ρ.val ∈ _root_.NontrivialZeros := ρ.property
  exact NontrivialZeros_im_ge_two h

/-- For `ρ ∈ NontrivialZeros`, `|ρ| ≤ √5 · |Im ρ| / 2`. -/
private lemma nontrivialZeros_norm_le_im
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ‖ρ.val‖ ≤ Real.sqrt 5 * |ρ.val.im| / 2 := by
  have h_im_ge : 2 ≤ |ρ.val.im| := nontrivialZeros_abs_im_ge_two ρ
  have h_re_lt : ρ.val.re < 1 := nontrivialZeros_re_lt_one ρ
  have h_re_pos : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_norm_sq : ‖ρ.val‖^2 = ρ.val.re^2 + ρ.val.im^2 := by
    rw [show ‖ρ.val‖^2 = Complex.normSq ρ.val from
      (Complex.normSq_eq_norm_sq _).symm, Complex.normSq_apply]
    ring
  have h_re_sq_le : ρ.val.re^2 ≤ 1 := by nlinarith
  have h_im_sq_ge : 4 ≤ ρ.val.im^2 := by
    have h := abs_nonneg ρ.val.im
    have : |ρ.val.im|^2 = ρ.val.im^2 := sq_abs _
    nlinarith
  have h_norm_sq_le : ‖ρ.val‖^2 ≤ (5 / 4) * ρ.val.im^2 := by
    rw [h_norm_sq]
    nlinarith
  have h_im_sq_eq : ρ.val.im^2 = |ρ.val.im|^2 := (sq_abs _).symm
  rw [h_im_sq_eq] at h_norm_sq_le
  have h_norm_nn : 0 ≤ ‖ρ.val‖ := norm_nonneg _
  have h_im_nn : 0 ≤ |ρ.val.im| := abs_nonneg _
  have h_rhs_nn : 0 ≤ Real.sqrt 5 * |ρ.val.im| / 2 := by
    have : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    positivity
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_rhs_sq : (Real.sqrt 5 * |ρ.val.im| / 2)^2 = (5 / 4) * |ρ.val.im|^2 := by
    rw [div_pow, mul_pow, h_sqrt5_sq]; ring
  have h_norm_sq_le' : ‖ρ.val‖^2 ≤ (Real.sqrt 5 * |ρ.val.im| / 2)^2 := by
    rw [h_rhs_sq]; exact h_norm_sq_le
  exact abs_le_of_sq_le_sq' h_norm_sq_le' h_rhs_nn |>.2

/-- Lower bound: `|Im ρ| ≥ 2 · ‖ρ‖ / √5`. -/
private lemma nontrivialZeros_im_ge_norm
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    2 * ‖ρ.val‖ / Real.sqrt 5 ≤ |ρ.val.im| := by
  have h := nontrivialZeros_norm_le_im ρ
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h_im_nn : 0 ≤ |ρ.val.im| := abs_nonneg _
  have h_norm_nn : 0 ≤ ‖ρ.val‖ := norm_nonneg _
  rw [div_le_iff₀ h_sqrt5_pos]
  rw [show Real.sqrt 5 * |ρ.val.im| / 2 = |ρ.val.im| * Real.sqrt 5 / 2 by ring] at h
  linarith

/-- `|ρ|·|Im ρ| ≥ (2/√5) · |ρ|²`. -/
private lemma nontrivialZeros_norm_im_ge_norm_sq
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    (2 / Real.sqrt 5) * ‖ρ.val‖^2 ≤ ‖ρ.val‖ * |ρ.val.im| := by
  have h := nontrivialZeros_im_ge_norm ρ
  have h_norm_nn : 0 ≤ ‖ρ.val‖ := norm_nonneg _
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  calc (2 / Real.sqrt 5) * ‖ρ.val‖^2
      = ‖ρ.val‖ * (2 * ‖ρ.val‖ / Real.sqrt 5) := by
        rw [sq]; field_simp
    _ ≤ ‖ρ.val‖ * |ρ.val.im| := by
        exact mul_le_mul_of_nonneg_left h h_norm_nn

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6.  Per-ρ integral of `‖hadFun β ρ‖`: trivial form
-- ═══════════════════════════════════════════════════════════════════════════

/-- The per-ρ integral of `‖hadFun β ρ‖` is bounded by
`n(ρ) · (1/(1 + Re ρ) + 1/‖ρ‖) · K · π` for some β-dependent constant `K`. -/
theorem hadFun_integral_norm_trivial_bound (β : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ∫ t : ℝ, ‖hadFun β ρ t‖ ≤
          (xiOrderNat ρ.val : ℝ) *
            (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K * Real.pi := by
  obtain ⟨K, hK_nn, hK_bd⟩ := pairTestMellin_global_quadratic_bound β 2 (by norm_num)
  refine ⟨K, hK_nn, fun ρ => ?_⟩
  -- Reuse the pointwise bound argument inline (to share the K).
  have h_re : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_re_lt : ρ.val.re < 1 := nontrivialZeros_re_lt_one ρ
  have h_norm_pos : 0 < ‖ρ.val‖ := nontrivialZeros_norm_pos ρ
  have h_one_re_pos : 0 < 1 + ρ.val.re := by linarith
  have h_neg1_lt : -1 < ρ.val.re := by linarith
  have h_n_nn : (0 : ℝ) ≤ (xiOrderNat ρ.val : ℝ) := by positivity
  have h_combined_nn : 0 ≤ 1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by
    have h1 : 0 ≤ 1 / (1 + ρ.val.re) := div_nonneg zero_le_one h_one_re_pos.le
    have h2 : 0 ≤ 1 / ‖ρ.val‖ := div_nonneg zero_le_one h_norm_pos.le
    linarith
  set C : ℝ := (xiOrderNat ρ.val : ℝ) * (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg (mul_nonneg h_n_nn h_combined_nn) hK_nn
  -- Pointwise bound on ‖hadFun‖.
  have h_pt : ∀ t : ℝ, ‖hadFun β ρ t‖ ≤ C / (1 + t^2) := by
    intro t
    have h_sub_norm_ge : (1 + ρ.val.re) ≤ ‖sOfT t - ρ.val‖ :=
      norm_sOfT_sub_ge_one_add_re t ρ.val h_neg1_lt
    have h_sub_ne : sOfT t - ρ.val ≠ 0 := sOfT_sub_ne_zero t ρ
    have h_ρ_ne : ρ.val ≠ 0 := nontrivialZeros_ne_zero ρ
    have h_one_t_pos : 0 < 1 + t^2 := by positivity
    have h_inv_sub_le : ‖(sOfT t - ρ.val)⁻¹‖ ≤ 1 / (1 + ρ.val.re) := by
      rw [norm_inv]
      rw [div_eq_inv_mul, mul_one]
      exact inv_anti₀ h_one_re_pos h_sub_norm_ge
    have h_inv_ρ : ‖ρ.val⁻¹‖ = 1 / ‖ρ.val‖ := by
      rw [norm_inv]; ring
    have h_combined : ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ ≤
        1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by
      rw [show (1 : ℂ) / (sOfT t - ρ.val) = (sOfT t - ρ.val)⁻¹ from one_div _,
          show (1 : ℂ) / ρ.val = ρ.val⁻¹ from one_div _]
      calc ‖(sOfT t - ρ.val)⁻¹ + ρ.val⁻¹‖
          ≤ ‖(sOfT t - ρ.val)⁻¹‖ + ‖ρ.val⁻¹‖ := norm_add_le _ _
        _ ≤ 1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖ := by rw [h_inv_ρ]; linarith
    have h_n_norm : ‖((xiOrderNat ρ.val : ℂ))‖ = (xiOrderNat ρ.val : ℝ) := by
      rw [show ((xiOrderNat ρ.val : ℂ)) = ((xiOrderNat ρ.val : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real]
      exact abs_of_nonneg (by positivity)
    have h_M_bd := hK_bd t
    unfold hadFun
    rw [norm_mul, norm_mul, h_n_norm]
    have h_step1 :
        (xiOrderNat ρ.val : ℝ) * ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ ≤
          (xiOrderNat ρ.val : ℝ) * (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) :=
      mul_le_mul_of_nonneg_left h_combined h_n_nn
    have h_inner_nn :
        0 ≤ (xiOrderNat ρ.val : ℝ) * (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) :=
      mul_nonneg h_n_nn h_combined_nn
    calc (xiOrderNat ρ.val : ℝ) *
          ‖1 / (sOfT t - ρ.val) + 1 / ρ.val‖ *
          ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖
        ≤ (xiOrderNat ρ.val : ℝ) *
            (1 / (1 + ρ.val.re) + 1 / ‖ρ.val‖) *
            (K / (1 + t^2)) :=
          mul_le_mul h_step1 h_M_bd (norm_nonneg _) h_inner_nn
      _ = C / (1 + t^2) := by simp [hC_def]; ring
  -- Integrate the pointwise bound.
  have h_F_int : MeasureTheory.Integrable (hadFun β ρ) := hadFun_integrable β ρ
  have h_norm_int : MeasureTheory.Integrable (fun t => ‖hadFun β ρ t‖) :=
    h_F_int.norm
  have h_dom_int :
      MeasureTheory.Integrable (fun t : ℝ => C / (1 + t^2)) := by
    have h0 : MeasureTheory.Integrable (fun t : ℝ => C * (1 + t^2)⁻¹) :=
      (integrable_inv_one_add_sq).const_mul C
    have h_eq : (fun t : ℝ => C / (1 + t^2)) = (fun t : ℝ => C * (1 + t^2)⁻¹) := by
      funext t; rw [div_eq_mul_inv]
    rw [h_eq]; exact h0
  have h_int_le :
      ∫ t : ℝ, ‖hadFun β ρ t‖ ≤ ∫ t : ℝ, C / (1 + t^2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun t => norm_nonneg _) h_dom_int ?_
    exact MeasureTheory.ae_of_all _ h_pt
  have h_dom_eval :
      ∫ t : ℝ, C / (1 + t^2) = C * Real.pi := by
    have h_eq : (fun t : ℝ => C / (1 + t^2)) = (fun t : ℝ => C * (1 + t^2)⁻¹) := by
      funext t; rw [div_eq_mul_inv]
    rw [h_eq, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  rw [h_dom_eval] at h_int_le
  calc ∫ t : ℝ, ‖hadFun β ρ t‖
      ≤ C * Real.pi := h_int_le
    _ = (xiOrderNat ρ.val : ℝ) * (1/(1 + ρ.val.re) + 1/‖ρ.val‖) * K * Real.pi := by
        rw [hC_def]

#print axioms hadFun_integral_norm_trivial_bound

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7.  Global quartic bound on `pairTestMellin` along `Re s = σ₀ > 0`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Global quartic bound on `pairTestMellin` along a vertical line `Re s = σ₀ > 0`.**
For all `t : ℝ`, `‖pairTestMellin β (σ₀+it)‖ ≤ K / (1 + t²)²` for some constant `K ≥ 0`.

Combines `pairTestMellin_quartic_decay_on_strip` (valid for `|T| ≥ T₀`) with the
continuity-bound on the compact `[-T', T']` (where `T' = max T₀ 1`).
For `|t| ≥ T'`, use the quartic decay `C/|t|⁴` and bound `1/|t|⁴ ≤ 4/(1+t²)²`
using `1+t² ≤ 2t²` for `|t| ≥ 1`. For `|t| < T'`, use the continuity max
`M_cpt` and the trivial bound `M_cpt ≤ M_cpt·(1+T'²)²/(1+t²)²`. -/
theorem pairTestMellin_global_quartic_bound (β : ℝ) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ K / (1 + t^2)^2 := by
  obtain ⟨C_decay, T₀, hC_pos, hT₀_pos, h_decay⟩ :=
    pairTestMellin_quartic_decay_on_strip β σ₀ σ₀ hσ₀ (le_refl σ₀)
  set T' : ℝ := max T₀ 1 with hT'_def
  have hT'_ge_T₀ : T₀ ≤ T' := le_max_left _ _
  have hT'_ge_one : (1 : ℝ) ≤ T' := le_max_right _ _
  have hT'_pos : 0 < T' := lt_of_lt_of_le zero_lt_one hT'_ge_one
  have h_pair_cont := pairTestMellin_continuous_along_vertical β σ₀ hσ₀
  have h_compact : IsCompact (Set.Icc (-T') T') := isCompact_Icc
  obtain ⟨t_max, _, h_max⟩ := h_compact.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith))
    (Continuous.continuousOn (h_pair_cont.norm))
  set M_cpt : ℝ := ‖pairTestMellin β ((σ₀ : ℂ) + (t_max : ℂ) * I)‖ with hMcpt_def
  have hM_cpt_nn : 0 ≤ M_cpt := norm_nonneg _
  set K : ℝ := max (4 * C_decay) (M_cpt * (1 + T'^2)^2) with hK_def
  have hK_nn : 0 ≤ K := le_max_of_le_left (by linarith : 0 ≤ 4 * C_decay)
  refine ⟨K, hK_nn, fun t => ?_⟩
  have h_1plus_pos : 0 < 1 + t^2 := by have := sq_nonneg t; linarith
  have h_1plus_sq_pos : 0 < (1 + t^2)^2 := by positivity
  by_cases h_Im : T' ≤ |t|
  · have h_T₀_le : T₀ ≤ |t| := le_trans hT'_ge_T₀ h_Im
    have h_1_le : (1 : ℝ) ≤ |t| := le_trans hT'_ge_one h_Im
    have h_d := h_decay t h_T₀_le σ₀ ⟨le_refl _, le_refl _⟩
    have h_abs_sq : |t|^2 = t^2 := sq_abs t
    have h_tpow : |t|^(-(4:ℝ)) = 1 / t^4 := by
      rw [Real.rpow_neg (abs_nonneg _),
        show ((4 : ℝ)) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show |t|^(4:ℕ) = (|t|^2)^2 from by ring, h_abs_sq, one_div]
      ring
    rw [h_tpow] at h_d
    have h_tsq_ge_1 : (1 : ℝ) ≤ t^2 := by rw [← h_abs_sq]; exact one_le_pow₀ h_1_le
    have h_tsq_pos : 0 < t^2 := by linarith
    have h_t_ne : t ≠ 0 := by
      intro h; rw [h, sq, mul_zero] at h_tsq_pos; exact lt_irrefl _ h_tsq_pos
    have h_t4_pos : 0 < t^4 := by positivity
    have h_1plus_le_2tsq : 1 + t^2 ≤ 2 * t^2 := by linarith
    -- (1+t²)² ≤ 4·t⁴
    have h_1plus_sq_le : (1 + t^2)^2 ≤ 4 * t^4 := by
      have h1 : (1 + t^2)^2 ≤ (2 * t^2)^2 := by
        apply sq_le_sq' (by linarith) h_1plus_le_2tsq
      calc (1 + t^2)^2 ≤ (2 * t^2)^2 := h1
        _ = 4 * t^4 := by ring
    -- 1/t⁴ ≤ 4/(1+t²)²
    have h_div_bd : C_decay * (1 / t^4) ≤ 4 * C_decay / (1 + t^2)^2 := by
      rw [mul_one_div, div_le_div_iff₀ h_t4_pos h_1plus_sq_pos]
      have := mul_le_mul_of_nonneg_left h_1plus_sq_le (by linarith : 0 ≤ C_decay)
      nlinarith
    have h_bd2 : 4 * C_decay / (1 + t^2)^2 ≤ K / (1 + t^2)^2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) h_1plus_sq_pos.le
    linarith [h_d, h_div_bd, h_bd2]
  · push_neg at h_Im
    have ht_mem : t ∈ Set.Icc (-T') T' := by
      refine ⟨?_, ?_⟩ <;> have := abs_le.mp h_Im.le <;> linarith
    have h_le_max := h_max ht_mem
    have h_t_sq_le : t^2 ≤ T'^2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) h_Im.le 2
    have h_1plus_le : 1 + t^2 ≤ 1 + T'^2 := by linarith
    have h_1plus_T'_pos : 0 < 1 + T'^2 := by nlinarith
    have h_1plus_T'_sq_pos : 0 < (1 + T'^2)^2 := by positivity
    have h_1plus_sq_le : (1 + t^2)^2 ≤ (1 + T'^2)^2 := by
      apply sq_le_sq' _ h_1plus_le
      have : 0 ≤ 1 + t^2 := h_1plus_pos.le
      linarith
    calc ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ M_cpt := h_le_max
      _ = M_cpt * (1 + T'^2)^2 / (1 + T'^2)^2 := by
          rw [mul_div_assoc, div_self (ne_of_gt h_1plus_T'_sq_pos), mul_one]
      _ ≤ M_cpt * (1 + T'^2)^2 / (1 + t^2)^2 := by
          apply div_le_div_of_nonneg_left (by positivity) h_1plus_sq_pos h_1plus_sq_le
      _ ≤ K / (1 + t^2)^2 := by
          apply div_le_div_of_nonneg_right _ h_1plus_sq_pos.le
          exact le_max_right _ _

#print axioms pairTestMellin_global_quartic_bound

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8.  Resonance integral bound `∫ dt/((1+t²)·((1+a)²+(t+b)²)) ≤ 4π/b²`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Pointwise resonance bound.** For `a ≥ 0` and `b ≠ 0`,
`1/((1+t²)·D) ≤ (2/b²)·(1/D + 1/(1+t²))` where `D = (1+a)² + (t+b)²`.
Key inequality: `(1+t²) + (t+b)² = 1 + 2(t+b/2)² + b²/2 ≥ b²/2`. -/
private lemma pointwise_bound_resonance (a b t : ℝ) (ha : 0 ≤ a) (hb : b ≠ 0) :
    1 / ((1 + t^2) * ((1 + a)^2 + (t + b)^2)) ≤
      (2 / b^2) * (1 / ((1 + a)^2 + (t + b)^2) + 1 / (1 + t^2)) := by
  have h_1plus_pos : (0:ℝ) < 1 + t^2 := by positivity
  have h1a_pos : (0:ℝ) < 1 + a := by linarith
  have h1a_sq_pos : (0:ℝ) < (1 + a)^2 := pow_pos h1a_pos 2
  have hD_pos : (0:ℝ) < (1 + a)^2 + (t + b)^2 := by
    have h2 : 0 ≤ (t + b)^2 := sq_nonneg _
    linarith
  have hb_sq_pos : (0:ℝ) < b^2 := by positivity
  have h_key : b^2 ≤ 2 * ((1 + t^2) + ((1 + a)^2 + (t + b)^2)) := by
    nlinarith [sq_nonneg (t + b/2), sq_nonneg (1 + a), sq_nonneg b]
  have h_RHS_eq : (2 / b^2) * (1 / ((1 + a)^2 + (t + b)^2) + 1 / (1 + t^2)) =
      (2 * ((1 + t^2) + ((1 + a)^2 + (t + b)^2))) /
        (b^2 * ((1 + t^2) * ((1 + a)^2 + (t + b)^2))) := by
    field_simp
  rw [h_RHS_eq]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (1 + t^2) * ((1 + a)^2 + (t + b)^2))
    (by positivity : (0:ℝ) < b^2 * ((1 + t^2) * ((1 + a)^2 + (t + b)^2)))]
  -- Goal: 1 * (b² * ((1+t²) * D)) ≤ 2 * ((1+t²) + D) * ((1+t²) * D)
  have h_pos : 0 < (1 + t^2) * ((1 + a)^2 + (t + b)^2) := by positivity
  nlinarith [h_key, h_pos.le]

/-- **Integrability of `(1 + (t+b)²)⁻¹`** via translation-preservation. -/
private lemma integrable_inv_one_add_shift_sq (b : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => (1 + (t + b)^2)⁻¹) := by
  have h_meas : MeasureTheory.MeasurePreserving (· + b) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      MeasureTheory.volume := MeasureTheory.measurePreserving_add_right MeasureTheory.volume b
  exact h_meas.integrable_comp_of_integrable integrable_inv_one_add_sq

/-- **Integrability of the shifted resonance kernel.** -/
private lemma integrable_inv_resonance (a b : ℝ) (ha : 0 ≤ a) :
    MeasureTheory.Integrable (fun t : ℝ => 1 / ((1 + a)^2 + (t + b)^2)) := by
  have h1a_pos : (0:ℝ) < 1 + a := by linarith
  have h1a_sq_pos : (0:ℝ) < (1 + a)^2 := pow_pos h1a_pos 2
  have h_cont : Continuous (fun t : ℝ => 1 / ((1 + a)^2 + (t + b)^2)) := by
    refine continuous_const.div (by fun_prop) (fun t => ?_)
    have h2 : 0 ≤ (t + b)^2 := sq_nonneg _
    linarith
  -- Dominated by 1/(1+(t+b)²) (using (1+a)² ≥ 1).
  have h_dom_int : MeasureTheory.Integrable (fun t : ℝ => 1 / (1 + (t + b)^2)) := by
    have h0 := integrable_inv_one_add_shift_sq b
    have h_eq : (fun t : ℝ => (1 + (t + b)^2)⁻¹) = (fun t : ℝ => 1 / (1 + (t + b)^2)) := by
      funext t; rw [one_div]
    rwa [h_eq] at h0
  refine MeasureTheory.Integrable.mono h_dom_int h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h2 : 0 ≤ (t + b)^2 := sq_nonneg _
  have hD_pos : (0:ℝ) < (1 + a)^2 + (t + b)^2 := by linarith
  have h_one_pos : (0:ℝ) < 1 + (t + b)^2 := by linarith
  have h_inv_nn : 0 ≤ 1 / ((1 + a)^2 + (t + b)^2) :=
    div_nonneg zero_le_one hD_pos.le
  have h_dom_nn : 0 ≤ 1 / (1 + (t + b)^2) :=
    div_nonneg zero_le_one h_one_pos.le
  rw [Real.norm_of_nonneg h_inv_nn, Real.norm_of_nonneg h_dom_nn]
  have ha_sq_ge : (1:ℝ) ≤ (1 + a)^2 := by
    have h1a : (1:ℝ) ≤ 1 + a := by linarith
    calc (1:ℝ) = 1^2 := by ring
      _ ≤ (1+a)^2 := by gcongr
  apply div_le_div_of_nonneg_left zero_le_one h_one_pos
  linarith

/-- **Translation invariance of `∫ 1/(1+(t+b)²) dt = π`.** -/
private lemma integral_inv_one_add_shift_sq_eq (b : ℝ) :
    ∫ t : ℝ, 1 / (1 + (t + b)^2) = Real.pi := by
  have h1 : ∫ t : ℝ, 1 / (1 + (t + b)^2) = ∫ t : ℝ, 1 / (1 + t^2) :=
    MeasureTheory.integral_add_right_eq_self (fun t : ℝ => 1 / (1 + t^2)) b
  rw [h1]
  have h_eq2 : (fun t : ℝ => 1 / (1 + t^2)) = (fun t : ℝ => (1 + t^2)⁻¹) := by
    funext t; rw [one_div]
  rw [h_eq2]
  exact integral_univ_inv_one_add_sq

/-- **Resonance integral bound.** For `a ≥ 0` and `b ≠ 0`:
`∫ dt/((1+t²)·((1+a)²+(t+b)²)) ≤ 4π/b²`. -/
private lemma integral_inv_one_add_sq_mul_resonance_bound (a b : ℝ) (ha : 0 ≤ a) (hb : b ≠ 0) :
    ∫ t : ℝ, 1 / ((1 + t^2) * ((1 + a)^2 + (t + b)^2)) ≤ 4 * Real.pi / b^2 := by
  have h1a_pos : (0:ℝ) < 1 + a := by linarith
  have h_pi_pos : (0:ℝ) < Real.pi := Real.pi_pos
  have hb_sq_pos : (0:ℝ) < b^2 := by positivity
  have h_two_b_sq_nn : (0:ℝ) ≤ 2 / b^2 := by positivity
  have h_int_inv_one_add : MeasureTheory.Integrable (fun t : ℝ => 1 / (1 + t^2)) := by
    have : MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)⁻¹) := integrable_inv_one_add_sq
    have h_eq : (fun t : ℝ => (1 + t^2)⁻¹) = (fun t : ℝ => 1 / (1 + t^2)) := by
      funext t; rw [one_div]
    rwa [h_eq] at this
  have h_int_inv_shift : MeasureTheory.Integrable (fun t : ℝ => 1 / (1 + (t + b)^2)) := by
    have h0 := integrable_inv_one_add_shift_sq b
    have h_eq : (fun t : ℝ => (1 + (t + b)^2)⁻¹) = (fun t : ℝ => 1 / (1 + (t + b)^2)) := by
      funext t; rw [one_div]
    rwa [h_eq] at h0
  have h_int_inv_res := integrable_inv_resonance a b ha
  -- Apply pointwise bound + integral_mono.
  have h_pt := fun t => pointwise_bound_resonance a b t ha hb
  have h_dom_int : MeasureTheory.Integrable
      (fun t : ℝ => (2 / b^2) *
        (1 / ((1 + a)^2 + (t + b)^2) + 1 / (1 + t^2))) :=
    (h_int_inv_res.add h_int_inv_one_add).const_mul _
  have h_int_le : ∫ t : ℝ, 1 / ((1 + t^2) * ((1 + a)^2 + (t + b)^2)) ≤
      ∫ t : ℝ, (2 / b^2) *
        (1 / ((1 + a)^2 + (t + b)^2) + 1 / (1 + t^2)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ h_dom_int ?_
    · refine MeasureTheory.ae_of_all _ fun t => ?_
      have h_1plus_pos : (0:ℝ) < 1 + t^2 := by positivity
      have h1a_sq_pos : (0:ℝ) < (1 + a)^2 := pow_pos h1a_pos 2
      have hD_pos : (0:ℝ) < (1 + a)^2 + (t + b)^2 := by
        have : 0 ≤ (t + b)^2 := sq_nonneg _; linarith
      exact div_nonneg zero_le_one (mul_pos h_1plus_pos hD_pos).le
    · exact MeasureTheory.ae_of_all _ h_pt
  -- Bound ∫ 1/D ≤ π.
  have h_inv_res_bound : ∫ t : ℝ, 1 / ((1 + a)^2 + (t + b)^2) ≤ Real.pi := by
    have h_pt2 : ∀ t, (1 : ℝ) / ((1 + a)^2 + (t + b)^2) ≤ 1 / (1 + (t + b)^2) := by
      intro t
      have h2 : 0 ≤ (t + b)^2 := sq_nonneg _
      have h1a_sq_ge : (1:ℝ) ≤ (1 + a)^2 := by
        have h1a : (1:ℝ) ≤ 1 + a := by linarith
        calc (1:ℝ) = 1^2 := by ring
          _ ≤ (1+a)^2 := by gcongr
      apply div_le_div_of_nonneg_left zero_le_one (by linarith)
      linarith
    calc ∫ t : ℝ, 1 / ((1 + a)^2 + (t + b)^2)
        ≤ ∫ t : ℝ, 1 / (1 + (t + b)^2) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · refine MeasureTheory.ae_of_all _ fun t => ?_
            have h2 : 0 ≤ (t + b)^2 := sq_nonneg _
            have h1a_sq_pos : (0:ℝ) < (1 + a)^2 := pow_pos h1a_pos 2
            have hD_pos : (0:ℝ) < (1 + a)^2 + (t + b)^2 := by linarith
            exact div_nonneg zero_le_one hD_pos.le
          · exact h_int_inv_shift
          · exact MeasureTheory.ae_of_all _ h_pt2
      _ = Real.pi := integral_inv_one_add_shift_sq_eq b
  have h_inv_one_add_eval : ∫ t : ℝ, 1 / (1 + t^2) = Real.pi := by
    have h_eq : (fun t : ℝ => 1 / (1 + t^2)) = (fun t : ℝ => (1 + t^2)⁻¹) := by
      funext t; rw [one_div]
    rw [h_eq]; exact integral_univ_inv_one_add_sq
  -- Compute the dominating integral as ≤ 4π/b².
  have h_dom_le : ∫ t : ℝ, (2 / b^2) *
        (1 / ((1 + a)^2 + (t + b)^2) + 1 / (1 + t^2)) ≤ 4 * Real.pi / b^2 := by
    rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add h_int_inv_res h_int_inv_one_add,
        h_inv_one_add_eval]
    have h_sum_le : (∫ t : ℝ, 1 / ((1 + a)^2 + (t + b)^2)) + Real.pi ≤ 2 * Real.pi := by
      linarith
    calc (2 / b^2) * ((∫ t : ℝ, 1 / ((1 + a)^2 + (t + b)^2)) + Real.pi)
        ≤ (2 / b^2) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left h_sum_le h_two_b_sq_nn
      _ = 4 * Real.pi / b^2 := by field_simp; ring
  linarith [h_int_le, h_dom_le]

end ZD.WeilPositivity.HadamardFubiniMajorant

end


noncomputable section

namespace ZD.WeilPositivity.HadamardFubiniMajorant

-- ═══════════════════════════════════════════════════════════════════════════
-- § 9.  Sharp per-ρ bound via AM-GM (Cauchy-Schwarz pointwise form)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **AM-GM in additive form.** `2αxy ≤ α²x² + y²`. -/
private lemma two_alpha_mul_le_sq_add_sq (x y α : ℝ) :
    2 * α * x * y ≤ α^2 * x^2 + y^2 := by
  nlinarith [sq_nonneg (α * x - y)]

/-- **Pointwise bound on `|hadFun β ρ|` via AM-GM.** For any `α > 0`:
`‖hadFun β ρ t‖ ≤ (n_ρ/(2‖ρ‖))·(α·|s|²·|M|² · ε + (1/α)·|M|²/|s-ρ|² · 1/ε)` — but in our
combined form, we use `|s|·|M|/|s-ρ| ≤ (α·|s|² + 1/(α·|s-ρ|²))·|M|/2`. -/
private lemma combined_le_am_gm (s_norm M_norm s_sub_rho_norm α : ℝ)
    (hα : 0 < α) (h_M_nn : 0 ≤ M_norm) (h_s_sub_pos : 0 < s_sub_rho_norm) :
    s_norm * M_norm / s_sub_rho_norm ≤
      (α * s_norm^2 * M_norm + M_norm / (α * s_sub_rho_norm^2)) / 2 := by
  -- 2·s·M/|s-ρ| ≤ α·s²·M + M/(α·|s-ρ|²)
  -- Equivalent to 0 ≤ (α·s·|s-ρ| - 1)²·M/(α·|s-ρ|²)·... not quite. Use:
  -- 2 s/|s-ρ| ≤ α·s² + 1/(α·|s-ρ|²) ⟺ 0 ≤ (α·s·|s-ρ| - 1)² (multiply through by α·|s-ρ|²)
  -- Then multiply by M ≥ 0.
  have h_α_sub_sq_pos : 0 < α * s_sub_rho_norm^2 := by positivity
  have h_2_s_le : 2 * s_norm / s_sub_rho_norm ≤ α * s_norm^2 + 1 / (α * s_sub_rho_norm^2) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < s_sub_rho_norm)]
    rw [show α * s_norm^2 + 1 / (α * s_sub_rho_norm^2) =
      (α^2 * s_sub_rho_norm^2 * s_norm^2 + 1) / (α * s_sub_rho_norm^2) from by
        field_simp]
    rw [div_mul_eq_mul_div, le_div_iff₀ h_α_sub_sq_pos]
    nlinarith [sq_nonneg (α * s_norm * s_sub_rho_norm - 1), sq_nonneg s_sub_rho_norm,
      sq_nonneg s_norm, hα.le]
  -- Multiply by M_norm/2 ≥ 0:
  have h_two : 2 * s_norm / s_sub_rho_norm * (M_norm / 2) ≤
      (α * s_norm^2 + 1 / (α * s_sub_rho_norm^2)) * (M_norm / 2) := by
    apply mul_le_mul_of_nonneg_right h_2_s_le
    linarith
  have h_LHS_eq : 2 * s_norm / s_sub_rho_norm * (M_norm / 2) = s_norm * M_norm / s_sub_rho_norm := by
    field_simp
  have h_RHS_eq : (α * s_norm^2 + 1 / (α * s_sub_rho_norm^2)) * (M_norm / 2) =
      (α * s_norm^2 * M_norm + M_norm / (α * s_sub_rho_norm^2)) / 2 := by
    field_simp
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact h_two

/-- **Sharp per-ρ bound.** `∫ ‖hadFun β ρ‖ ≤ √5·π·K_q · n_ρ / ‖ρ‖²`,
where `K_q` is the global quartic-decay constant for `pairTestMellin β` along `Re s = 2`.
Combined with `summable_xiOrderNat_div_norm_sq_nontrivialZeros`, this gives the
summable Fubini majorant. -/
theorem hadFun_integral_norm_sharp_bound (β : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ∫ t : ℝ, ‖hadFun β ρ t‖ ≤
          K * (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2 := by
  obtain ⟨K_q, hK_q_nn, h_M_bd⟩ := pairTestMellin_global_quartic_bound β 2 (by norm_num)
  refine ⟨Real.sqrt 5 * Real.pi * K_q, by positivity, ?_⟩
  intro ρ
  set n_ρ : ℝ := (xiOrderNat ρ.val : ℝ) with hn_def
  have h_n_nn : 0 ≤ n_ρ := by unfold_let ρ; positivity
  have h_re_pos : 0 < ρ.val.re := nontrivialZeros_re_pos ρ
  have h_re_nn : 0 ≤ ρ.val.re := h_re_pos.le
  have h_norm_pos : 0 < ‖ρ.val‖ := nontrivialZeros_norm_pos ρ
  have h_ρ_ne : ρ.val ≠ 0 := nontrivialZeros_ne_zero ρ
  have h_im_ge_two : 2 ≤ |ρ.val.im| := nontrivialZeros_abs_im_ge_two ρ
  have h_im_ne : ρ.val.im ≠ 0 := by
    intro h; rw [h, abs_zero] at h_im_ge_two; linarith
  have h_im_sq_pos : 0 < ρ.val.im^2 := by positivity
  have h_im_sq_ge : (4 / 5) * ‖ρ.val‖^2 ≤ ρ.val.im^2 := by
    have h_step := nontrivialZeros_norm_im_ge_norm_sq ρ
    have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    have h_im_sq_eq : ρ.val.im^2 = |ρ.val.im|^2 := (sq_abs _).symm
    have h_im_nn : 0 ≤ |ρ.val.im| := abs_nonneg _
    have h_norm_nn : 0 ≤ ‖ρ.val‖ := norm_nonneg _
    have h_lhs_nn : 0 ≤ (2 / Real.sqrt 5) * ‖ρ.val‖^2 := by positivity
    have h_rhs_nn : 0 ≤ ‖ρ.val‖ * |ρ.val.im| := by positivity
    have h_sq_ineq : ((2 / Real.sqrt 5) * ‖ρ.val‖^2)^2 ≤ (‖ρ.val‖ * |ρ.val.im|)^2 :=
      mul_self_le_mul_self h_lhs_nn h_step
    rw [h_im_sq_eq]
    nlinarith [h_sq_ineq, h_sqrt5_sq, sq_nonneg ‖ρ.val‖, h_norm_pos]
  -- Choose α = √5/‖ρ‖ for AM-GM.
  set α : ℝ := Real.sqrt 5 / ‖ρ.val‖ with hα_def
  have hα_pos : 0 < α := by
    unfold_let α
    apply div_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)) h_norm_pos
  -- Pointwise bound: ‖hadFun β ρ t‖ ≤ (n_ρ/(2‖ρ‖)) · (α·‖s‖²·‖M‖ + ‖M‖/(α·‖s-ρ‖²)).
  have h_pt : ∀ t : ℝ, ‖hadFun β ρ t‖ ≤
      n_ρ / (2 * ‖ρ.val‖) *
        (α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
         ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) := by
    intro t
    have h_M_nn : 0 ≤ ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ := norm_nonneg _
    have h_sub_ne : sOfT t - ρ.val ≠ 0 := sOfT_sub_ne_zero t ρ
    have h_s_sub_pos : 0 < ‖sOfT t - ρ.val‖ := norm_pos_iff.mpr h_sub_ne
    -- Combined form: ‖hadFun‖ = n_ρ · ‖s‖·‖M‖/(‖ρ‖·‖s-ρ‖).
    have h_combined_eq_complex : (1 : ℂ) / (sOfT t - ρ.val) + 1 / ρ.val =
        sOfT t / (ρ.val * (sOfT t - ρ.val)) := by
      field_simp
      ring
    have h_n_norm : ‖((xiOrderNat ρ.val : ℂ))‖ = n_ρ := by
      unfold_let ρ
      rw [show ((xiOrderNat ρ.val : ℂ)) = ((xiOrderNat ρ.val : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real]
      exact abs_of_nonneg (by positivity)
    have h_hadFun_eq : ‖hadFun β ρ t‖ =
        n_ρ * (‖sOfT t‖ * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ /
              (‖ρ.val‖ * ‖sOfT t - ρ.val‖)) := by
      unfold hadFun
      rw [norm_mul, norm_mul, h_n_norm, h_combined_eq_complex, norm_div, norm_mul]
      ring
    rw [h_hadFun_eq]
    have h_combined_le := combined_le_am_gm
      (‖sOfT t‖) (‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖) (‖sOfT t - ρ.val‖) α
      hα_pos h_M_nn h_s_sub_pos
    have h_fact_nn : 0 ≤ n_ρ / ‖ρ.val‖ := div_nonneg h_n_nn h_norm_pos.le
    have h_step :
        n_ρ * (‖sOfT t‖ * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ /
              (‖ρ.val‖ * ‖sOfT t - ρ.val‖)) ≤
        n_ρ / ‖ρ.val‖ *
          ((α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
            ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) / 2) := by
      have h_eq : n_ρ * (‖sOfT t‖ * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ /
            (‖ρ.val‖ * ‖sOfT t - ρ.val‖)) =
          n_ρ / ‖ρ.val‖ *
            (‖sOfT t‖ * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / ‖sOfT t - ρ.val‖) := by
        field_simp
        ring
      rw [h_eq]
      apply mul_le_mul_of_nonneg_left h_combined_le h_fact_nn
    -- Rearrange the RHS.
    have h_rearr :
        n_ρ / ‖ρ.val‖ *
          ((α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
            ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) / 2) =
        n_ρ / (2 * ‖ρ.val‖) *
          (α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
           ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) := by
      ring
    linarith [h_step, h_rearr]
  -- Bound the two integrals.
  -- A. ∫ α·‖s‖²·‖M‖ ≤ α·K_q·π.
  -- B. ∫ ‖M‖/(α·‖s-ρ‖²) ≤ K_q·4π/(α·(Im ρ)²) ≤ K_q·5π/(α·‖ρ‖²).
  -- Then ∫‖hadFun‖ ≤ (n_ρ/(2‖ρ‖)) · (A + B).
  -- With α = √5/‖ρ‖: A = √5·K_q·π/‖ρ‖, B = (‖ρ‖/√5)·K_q·5π/‖ρ‖² = √5·K_q·π/‖ρ‖.
  -- A + B = 2√5·K_q·π/‖ρ‖.
  -- ∫‖hadFun‖ ≤ (n_ρ/(2‖ρ‖)) · 2√5·K_q·π/‖ρ‖ = √5·K_q·π·n_ρ/‖ρ‖².
  -- Set up the dominating function and integrability.
  set bound : ℝ → ℝ := fun t =>
    n_ρ / (2 * ‖ρ.val‖) *
      (α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
       ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) with hbound_def
  -- Bound for ‖s‖²·‖M‖: use ‖s‖² = 1+t² and quartic ‖M‖ ≤ K_q/(1+t²)², giving K_q/(1+t²).
  have h_A_pt : ∀ t : ℝ, α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ ≤
      α * K_q / (1 + t^2) := by
    intro t
    have h_s_sq : ‖sOfT t‖^2 = 1 + t^2 := norm_sOfT_sq t
    rw [h_s_sq]
    have h_M_le : ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ ≤ K_q / (1 + t^2)^2 := h_M_bd t
    have h_1t_pos : 0 < 1 + t^2 := by positivity
    have h_1t_sq_pos : 0 < (1 + t^2)^2 := by positivity
    calc α * (1 + t^2) * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖
        ≤ α * (1 + t^2) * (K_q / (1 + t^2)^2) := by
          apply mul_le_mul_of_nonneg_left h_M_le
          exact mul_nonneg hα_pos.le h_1t_pos.le
      _ = α * K_q / (1 + t^2) := by
          field_simp
          ring
  -- Bound for ‖M‖/(α·‖s-ρ‖²): use quartic ‖M‖ ≤ K_q/(1+t²)² and 1/(1+t²)² ≤ 1/(1+t²),
  -- giving K_q/(α·(1+t²)·‖s-ρ‖²).
  have h_B_pt : ∀ t : ℝ,
      ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2) ≤
        K_q / (α * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2))) := by
    intro t
    have h_M_le : ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ ≤ K_q / (1 + t^2)^2 := h_M_bd t
    have h_1t_pos : 0 < 1 + t^2 := by positivity
    have h_1t_sq_pos : 0 < (1 + t^2)^2 := by positivity
    have h_1t_ge_1 : 1 ≤ 1 + t^2 := by have := sq_nonneg t; linarith
    have h_sub_ne : sOfT t - ρ.val ≠ 0 := sOfT_sub_ne_zero t ρ
    have h_s_sub_pos : 0 < ‖sOfT t - ρ.val‖ := norm_pos_iff.mpr h_sub_ne
    have h_s_sub_sq_pos : 0 < ‖sOfT t - ρ.val‖^2 := by positivity
    have hα_sub_sq_pos : 0 < α * ‖sOfT t - ρ.val‖^2 := by positivity
    -- ‖s-ρ‖² = (1+Re ρ)² + (t+Im ρ)²
    have h_norm_sub_sq : ‖sOfT t - ρ.val‖^2 = (1 + ρ.val.re)^2 + (t + ρ.val.im)^2 := by
      have h_re_eq : (sOfT t - ρ.val).re = -1 - ρ.val.re := re_sOfT_sub t ρ.val
      have h_im_eq : (sOfT t - ρ.val).im = -t - ρ.val.im := im_sOfT_sub t ρ.val
      have : Complex.normSq (sOfT t - ρ.val) =
          (sOfT t - ρ.val).re^2 + (sOfT t - ρ.val).im^2 := by
        rw [Complex.normSq_apply]; ring
      rw [show ‖sOfT t - ρ.val‖^2 = Complex.normSq (sOfT t - ρ.val) from
        (Complex.normSq_eq_norm_sq _).symm, this, h_re_eq, h_im_eq]
      ring
    have h_D_eq : (1 + ρ.val.re)^2 + (t + ρ.val.im)^2 = ‖sOfT t - ρ.val‖^2 := h_norm_sub_sq.symm
    rw [div_le_div_iff₀ hα_sub_sq_pos
      (by positivity : 0 < α * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)))]
    -- ‖M‖ · (α · D · (1+t²)) ≤ K_q · (α · ‖s-ρ‖²) where D = (1+Re ρ)²+(t+Im ρ)² = ‖s-ρ‖²
    rw [h_D_eq]
    -- Goal: ‖M‖ * (α * ((1+t²) * ‖s-ρ‖²)) ≤ K_q * (α * ‖s-ρ‖²)
    -- Cancel α·‖s-ρ‖² (positive): ‖M‖·(1+t²) ≤ K_q
    -- Use ‖M‖ ≤ K_q/(1+t²)² ≤ K_q/(1+t²) (since 1+t² ≥ 1):
    have h_M_le_one : ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ ≤ K_q / (1 + t^2) := by
      calc ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖
          ≤ K_q / (1 + t^2)^2 := h_M_le
        _ ≤ K_q / (1 + t^2) := by
            apply div_le_div_of_nonneg_left hK_q_nn h_1t_pos
            calc 1 + t^2 = (1 + t^2)^1 := (pow_one _).symm
              _ ≤ (1 + t^2)^2 := by
                apply pow_le_pow_right₀ h_1t_ge_1; norm_num
    have h_M_mul_le : ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ * (1 + t^2) ≤ K_q := by
      have := mul_le_mul_of_nonneg_right h_M_le_one h_1t_pos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt h_1t_pos)] at this
    -- Now multiply by α · ‖s-ρ‖² (positive):
    have h_α_sub_sq_nn : 0 ≤ α * ‖sOfT t - ρ.val‖^2 := hα_sub_sq_pos.le
    nlinarith [mul_le_mul_of_nonneg_right h_M_mul_le h_α_sub_sq_nn,
      norm_nonneg (pairTestMellin β ((2:ℂ) + (t:ℂ) * I)), h_α_sub_sq_nn,
      hα_pos.le, h_s_sub_sq_pos]
  -- Define dominating function: factor * (A_dom + B_dom) where A_dom, B_dom are integrable.
  set factor : ℝ := n_ρ / (2 * ‖ρ.val‖) with hfactor_def
  have h_factor_nn : 0 ≤ factor := by unfold_let ; positivity
  set A_dom : ℝ → ℝ := fun t => α * K_q / (1 + t^2) with hA_dom_def
  set B_dom : ℝ → ℝ := fun t =>
    K_q / (α * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2))) with hB_dom_def
  set dom : ℝ → ℝ := fun t => factor * (A_dom t + B_dom t) with hdom_def
  -- Pointwise: ‖hadFun β ρ t‖ ≤ dom t.
  have h_pt_dom : ∀ t : ℝ, ‖hadFun β ρ t‖ ≤ dom t := by
    intro t
    have h_pt_t := h_pt t
    have h_A_le := h_A_pt t
    have h_B_le := h_B_pt t
    have h_M_nn : 0 ≤ ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ := norm_nonneg _
    have h_sub_ne : sOfT t - ρ.val ≠ 0 := sOfT_sub_ne_zero t ρ
    have h_s_sub_sq_pos : 0 < ‖sOfT t - ρ.val‖^2 := by
      have h_s_sub_pos : 0 < ‖sOfT t - ρ.val‖ := norm_pos_iff.mpr h_sub_ne
      positivity
    have h_A_term_nn : 0 ≤ α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ := by
      have : 0 ≤ ‖sOfT t‖^2 := sq_nonneg _
      positivity
    have h_B_term_nn : 0 ≤ ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2) :=
      div_nonneg h_M_nn (mul_pos hα_pos h_s_sub_sq_pos).le
    have h_sum_le :
        α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
          ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2) ≤
        A_dom t + B_dom t := by
      unfold_let  B_dom
      linarith
    have h_factor_mul : factor *
        (α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
         ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) ≤
        factor * (A_dom t + B_dom t) :=
      mul_le_mul_of_nonneg_left h_sum_le h_factor_nn
    unfold_let
    have h_pt_t_eq : ‖hadFun β ρ t‖ ≤ factor *
        (α * ‖sOfT t‖^2 * ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ +
         ‖pairTestMellin β ((2:ℂ) + (t:ℂ) * I)‖ / (α * ‖sOfT t - ρ.val‖^2)) := h_pt_t
    linarith
  -- Integrability of A_dom and B_dom and dom.
  have h_intA_int : MeasureTheory.Integrable A_dom := by
    unfold_let
    have h0 : MeasureTheory.Integrable (fun t : ℝ => (1 + t^2)⁻¹) :=
      integrable_inv_one_add_sq
    have h1 := h0.const_mul (α * K_q)
    have h_eq : (fun t : ℝ => α * K_q * (1 + t^2)⁻¹) = (fun t : ℝ => α * K_q / (1 + t^2)) := by
      funext t; rw [div_eq_mul_inv]
    rwa [h_eq] at h1
  have h_intA_eval : ∫ t : ℝ, A_dom t = α * K_q * Real.pi := by
    unfold_let
    have h_eq : (fun t : ℝ => α * K_q / (1 + t^2)) = (fun t : ℝ => α * K_q * (1 + t^2)⁻¹) := by
      funext t; rw [div_eq_mul_inv]
    rw [h_eq, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  have h_resonance := integral_inv_one_add_sq_mul_resonance_bound ρ.val.re ρ.val.im h_re_nn h_im_ne
  have h_intB_int : MeasureTheory.Integrable B_dom := by
    unfold_let
    set f : ℝ → ℝ := fun t => 1 / ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)) with hf_def
    have h_f_int : MeasureTheory.Integrable f := by
      have h_cont : Continuous f := by
        unfold_let
        refine continuous_const.div (by fun_prop) (fun t => ?_)
        have h_1plus_pos : (0:ℝ) < 1 + t^2 := by positivity
        have h2 : 0 ≤ (t + ρ.val.im)^2 := sq_nonneg _
        have h1a_pos : (0:ℝ) < 1 + ρ.val.re := by linarith
        have h1a_sq_pos : (0:ℝ) < (1 + ρ.val.re)^2 := pow_pos h1a_pos 2
        have hD_pos : (0:ℝ) < (1 + ρ.val.re)^2 + (t + ρ.val.im)^2 := by linarith
        exact ne_of_gt (mul_pos h_1plus_pos hD_pos)
      refine MeasureTheory.Integrable.mono ?_ h_cont.aestronglyMeasurable ?_
      · exact integrable_inv_one_add_sq
      · refine MeasureTheory.ae_of_all _ fun t => ?_
        unfold_let
        have h_1plus_pos : (0:ℝ) < 1 + t^2 := by positivity
        have h2 : 0 ≤ (t + ρ.val.im)^2 := sq_nonneg _
        have h1a_pos : (0:ℝ) < 1 + ρ.val.re := by linarith
        have h1a_sq_ge : (1:ℝ) ≤ (1 + ρ.val.re)^2 := by
          calc (1:ℝ) = 1^2 := by ring
            _ ≤ (1+ρ.val.re)^2 := by gcongr
        have hD_ge_one : (1:ℝ) ≤ (1 + ρ.val.re)^2 + (t + ρ.val.im)^2 := by linarith
        have hD_pos : (0:ℝ) < (1 + ρ.val.re)^2 + (t + ρ.val.im)^2 := by linarith
        have h_LHS_nn : 0 ≤ 1 / ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)) :=
          div_nonneg zero_le_one (mul_pos h_1plus_pos hD_pos).le
        rw [Real.norm_of_nonneg h_LHS_nn]
        have h_inv_pos : (0:ℝ) < (1 + t^2)⁻¹ := inv_pos.mpr h_1plus_pos
        rw [Real.norm_of_nonneg h_inv_pos.le]
        rw [div_le_iff₀ (mul_pos h_1plus_pos hD_pos)]
        rw [show (1 + t^2)⁻¹ * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)) =
          ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2) by field_simp]
        linarith
    have h_eq : (fun t : ℝ => K_q / (α * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)))) =
        (fun t : ℝ => (K_q / α) * f t) := by
      unfold_let ; funext t; field_simp
    rw [h_eq]; exact h_f_int.const_mul _
  have h_intB_eval : ∫ t : ℝ, B_dom t ≤ K_q / α * (4 * Real.pi / ρ.val.im^2) := by
    unfold_let
    have h_eq : (fun t : ℝ => K_q / (α * ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)))) =
        (fun t : ℝ => (K_q / α) *
          (1 / ((1 + t^2) * ((1 + ρ.val.re)^2 + (t + ρ.val.im)^2)))) := by
      funext t; field_simp
    rw [h_eq, MeasureTheory.integral_const_mul]
    apply mul_le_mul_of_nonneg_left h_resonance
    positivity
  have h_int_dom : MeasureTheory.Integrable dom := by
    unfold_let
    exact (h_intA_int.add h_intB_int).const_mul _
  -- hadFun β ρ is integrable (by hadFun_integrable).
  have h_had_int : MeasureTheory.Integrable (hadFun β ρ) := hadFun_integrable β ρ
  have h_had_norm_int : MeasureTheory.Integrable (fun t : ℝ => ‖hadFun β ρ t‖) :=
    h_had_int.norm
  -- ∫ ‖hadFun‖ ≤ ∫ dom.
  have h_int_le : ∫ t : ℝ, ‖hadFun β ρ t‖ ≤ ∫ t : ℝ, dom t := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun t => norm_nonneg _) h_int_dom ?_
    exact MeasureTheory.ae_of_all _ h_pt_dom
  -- ∫ dom = factor · (∫A_dom + ∫B_dom) ≤ factor · (α·K_q·π + (K_q/α)·4π/Im ρ²).
  have h_dom_eval : ∫ t : ℝ, dom t = factor * (∫ t : ℝ, A_dom t + ∫ t : ℝ, B_dom t) := by
    unfold_let
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h_intA_int h_intB_int]
  have h_dom_le : ∫ t : ℝ, dom t ≤
      factor * (α * K_q * Real.pi + K_q / α * (4 * Real.pi / ρ.val.im^2)) := by
    rw [h_dom_eval]
    apply mul_le_mul_of_nonneg_left _ h_factor_nn
    rw [h_intA_eval]
    linarith [h_intB_eval]
  -- Now substitute α = √5/‖ρ‖ and bound.
  -- α·K_q·π = √5·K_q·π/‖ρ‖.
  -- (K_q/α)·4π/Im ρ² ≤ (K_q·‖ρ‖/√5)·4π·5/(4·‖ρ‖²) = (K_q·‖ρ‖·5π)/(√5·‖ρ‖²) = √5·K_q·π/‖ρ‖.
  -- Sum: 2·√5·K_q·π/‖ρ‖.
  -- factor · sum = (n_ρ/(2‖ρ‖))·2·√5·K_q·π/‖ρ‖ = √5·K_q·π·n_ρ/‖ρ‖² ✓.
  have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_α_eq : α * K_q * Real.pi = Real.sqrt 5 * K_q * Real.pi / ‖ρ.val‖ := by
    unfold_let α; field_simp; ring
  have h_4pi_im_le : 4 * Real.pi / ρ.val.im^2 ≤ 5 * Real.pi / ‖ρ.val‖^2 := by
    have h_4pi_nn : 0 ≤ 4 * Real.pi := by have := Real.pi_pos; linarith
    have h_im_sq_pos : 0 < ρ.val.im^2 := h_im_sq_pos
    have h_norm_sq_pos : 0 < ‖ρ.val‖^2 := by positivity
    rw [div_le_div_iff₀ h_im_sq_pos h_norm_sq_pos]
    -- 4π·‖ρ‖² ≤ 5π·Im ρ².
    -- Use Im ρ² ≥ (4/5)·‖ρ‖² ⟹ 5·Im ρ² ≥ 4·‖ρ‖² ⟹ 5π·Im ρ² ≥ 4π·‖ρ‖².
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    nlinarith [h_im_sq_ge, h_pi_pos.le]
  have h_B_part_le : K_q / α * (4 * Real.pi / ρ.val.im^2) ≤
      Real.sqrt 5 * K_q * Real.pi / ‖ρ.val‖ := by
    have h_K_α_nn : 0 ≤ K_q / α := by positivity
    calc K_q / α * (4 * Real.pi / ρ.val.im^2)
        ≤ K_q / α * (5 * Real.pi / ‖ρ.val‖^2) :=
          mul_le_mul_of_nonneg_left h_4pi_im_le h_K_α_nn
      _ = Real.sqrt 5 * K_q * Real.pi / ‖ρ.val‖ := by
          unfold_let α
          field_simp
          nlinarith [h_sqrt5_sq, h_sqrt5_pos.le, h_norm_pos.le]
  -- Combine.
  calc ∫ t : ℝ, ‖hadFun β ρ t‖
      ≤ ∫ t : ℝ, dom t := h_int_le
    _ ≤ factor * (α * K_q * Real.pi + K_q / α * (4 * Real.pi / ρ.val.im^2)) := h_dom_le
    _ ≤ factor * (Real.sqrt 5 * K_q * Real.pi / ‖ρ.val‖ +
                  Real.sqrt 5 * K_q * Real.pi / ‖ρ.val‖) := by
        apply mul_le_mul_of_nonneg_left _ h_factor_nn
        linarith
    _ = Real.sqrt 5 * Real.pi * K_q * (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2 := by
        unfold_let
        unfold_let ρ
        field_simp
        ring

end ZD.WeilPositivity.HadamardFubiniMajorant

end
