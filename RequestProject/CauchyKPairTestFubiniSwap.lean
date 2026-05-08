import Mathlib
import RequestProject.CauchyKPairTestPlancherelFubini
import RequestProject.CauchyKPairTestK2Discharges
import RequestProject.PairTestMellinBetaTotalality

/-!
# Joint Fubini swap: K-twisted zero sum as a t-integral of inner zero sums

Combines `K_zeroSum_eq_tsum_t_integral` (per-zero Plancherel swap) with
`MeasureTheory.integral_tsum_of_summable_integral_norm` (Fubini-Tonelli)
to deliver the **fully-swapped** representation:

```
Σ' n(ρ) · K(ρ) · M(β, ρ)
  = 2π · ∫_{Ioi 0} exp(-2t²) · [Σ' n(ρ) · K_2(ρ, t) · M(β, ρ)] dt
```

The K_2 strip bound `‖K_2(ρ, t)‖ ≤ cosh(|t|) + 2·cosh(|t|/2) + 1` for ρ in
the critical strip (`|σ - 1/2| ≤ 1/2`) makes the joint integrability
condition immediate.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity
open ZD.WeilPositivity.OfflineDetectorEndpoint

/-- `‖K_2(ρ, t)‖ ≤ cosh(|t|) + 2·cosh(|t|/2) + 1` for `ρ` a nontrivial zero
(critical strip `0 < Re ρ < 1` ⟹ `|σ - 1/2| < 1/2 ≤ 1/2`). -/
private lemma K_2_norm_le_NTZ (t : ℝ) (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    ‖K_2 ρ t‖ ≤ Real.cosh (|t|) + 2 * Real.cosh ((1/2) * |t|) + 1 := by
  obtain ⟨h_re_pos, h_re_lt_one, _⟩ := hρ
  have h_re_bd : |ρ.re - 1/2| ≤ 1/2 := by
    have h1 : -(1/2 : ℝ) ≤ ρ.re - 1/2 := by linarith
    have h2 : ρ.re - 1/2 ≤ 1/2 := by linarith
    exact abs_le.mpr ⟨h1, h2⟩
  -- Reuse the general bound `K_2_norm_le` with M = 1/2.
  -- Since K_2_norm_le is private, we recompute. We use norm_cosh_le_cosh_re indirectly.
  unfold K_2
  -- Bound each cosh term.
  have h_cosh1 : ‖Complex.cosh (2 * (ρ - 1/2) * (t : ℂ))‖ ≤ Real.cosh (|t|) := by
    have h_arg_re : (2 * (ρ - 1/2) * (t : ℂ)).re = 2 * (ρ.re - 1/2) * t := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have h_two : (2 : ℂ) * Complex.cosh (2 * (ρ - 1/2) * (t : ℂ)) =
        Complex.exp (2 * (ρ - 1/2) * (t : ℂ)) +
          Complex.exp (-(2 * (ρ - 1/2) * (t : ℂ))) := @Complex.two_cosh _
    have h_norm_2cosh : ‖(2 : ℂ) * Complex.cosh (2 * (ρ - 1/2) * (t : ℂ))‖ =
        2 * ‖Complex.cosh (2 * (ρ - 1/2) * (t : ℂ))‖ := by
      rw [norm_mul]; simp
    have h_sum_bd : ‖(2 : ℂ) * Complex.cosh (2 * (ρ - 1/2) * (t : ℂ))‖ ≤
        2 * Real.cosh |t| := by
      rw [h_two]
      calc ‖Complex.exp (2 * (ρ - 1/2) * (t : ℂ)) +
            Complex.exp (-(2 * (ρ - 1/2) * (t : ℂ)))‖
          ≤ ‖Complex.exp (2 * (ρ - 1/2) * (t : ℂ))‖ +
              ‖Complex.exp (-(2 * (ρ - 1/2) * (t : ℂ)))‖ := norm_add_le _ _
        _ = Real.exp (2 * (ρ.re - 1/2) * t) + Real.exp (-(2 * (ρ.re - 1/2) * t)) := by
            rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, h_arg_re]
        _ = 2 * Real.cosh (2 * (ρ.re - 1/2) * t) := by rw [Real.cosh_eq]; ring
        _ ≤ 2 * Real.cosh |t| := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
            rw [show Real.cosh (2 * (ρ.re - 1/2) * t) =
                Real.cosh |2 * (ρ.re - 1/2) * t| from (Real.cosh_abs _).symm]
            apply (Real.cosh_le_cosh).mpr
            rw [abs_abs]
            rw [show 2 * (ρ.re - 1/2) * t = 2 * ((ρ.re - 1/2) * t) from by ring,
                abs_mul, show |(2:ℝ)| = 2 from by norm_num]
            rw [abs_mul]
            calc 2 * (|ρ.re - 1/2| * |t|)
                ≤ 2 * ((1/2) * |t|) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
                  exact mul_le_mul_of_nonneg_right h_re_bd (abs_nonneg _)
              _ = |t| := by ring
              _ ≤ |(|t|)| := le_abs_self _
    rw [h_norm_2cosh] at h_sum_bd
    linarith
  have h_cosh2 : ‖Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ ≤ Real.cosh ((1/2) * |t|) := by
    have h_arg_re : ((ρ - 1/2) * (t : ℂ)).re = (ρ.re - 1/2) * t := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have h_two : (2 : ℂ) * Complex.cosh ((ρ - 1/2) * (t : ℂ)) =
        Complex.exp ((ρ - 1/2) * (t : ℂ)) +
          Complex.exp (-((ρ - 1/2) * (t : ℂ))) := @Complex.two_cosh _
    have h_norm_2cosh : ‖(2 : ℂ) * Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ =
        2 * ‖Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ := by
      rw [norm_mul]; simp
    have h_sum_bd : ‖(2 : ℂ) * Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ ≤
        2 * Real.cosh ((1/2) * |t|) := by
      rw [h_two]
      calc ‖Complex.exp ((ρ - 1/2) * (t : ℂ)) + Complex.exp (-((ρ - 1/2) * (t : ℂ)))‖
          ≤ ‖Complex.exp ((ρ - 1/2) * (t : ℂ))‖ +
              ‖Complex.exp (-((ρ - 1/2) * (t : ℂ)))‖ := norm_add_le _ _
        _ = Real.exp ((ρ.re - 1/2) * t) + Real.exp (-((ρ.re - 1/2) * t)) := by
            rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, h_arg_re]
        _ = 2 * Real.cosh ((ρ.re - 1/2) * t) := by rw [Real.cosh_eq]; ring
        _ ≤ 2 * Real.cosh ((1/2) * |t|) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
            have h_abs_le : |(ρ.re - 1/2) * t| ≤ (1/2) * |t| := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right h_re_bd (abs_nonneg _)
            rw [show Real.cosh ((ρ.re - 1/2) * t) =
                Real.cosh (|(ρ.re - 1/2) * t|) from (Real.cosh_abs _).symm]
            apply (Real.cosh_le_cosh).mpr
            have h_abs_id : abs (abs ((ρ.re - 1/2) * t)) = |(ρ.re - 1/2) * t| := abs_abs _
            have h_abs_id2 : abs ((1/2 : ℝ) * |t|) = (1/2) * |t| := by
              rw [abs_mul, show |(1/2:ℝ)| = 1/2 from by norm_num, abs_abs]
            rw [h_abs_id, h_abs_id2]
            exact h_abs_le
    rw [h_norm_2cosh] at h_sum_bd
    linarith
  calc ‖Complex.cosh (2 * (ρ - 1/2) * (t : ℂ)) -
        2 * Complex.cosh ((ρ - 1/2) * (t : ℂ)) + 1‖
      ≤ ‖Complex.cosh (2 * (ρ - 1/2) * (t : ℂ)) -
            2 * Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖Complex.cosh (2 * (ρ - 1/2) * (t : ℂ))‖ +
          ‖2 * Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.cosh (|t|) + 2 * Real.cosh ((1/2) * |t|) + 1 := by
        have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h_norm_one]
        have h_2_norm : ‖2 * Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ ≤
            2 * Real.cosh ((1/2) * |t|) := by
          rw [norm_mul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          have hnn : 0 ≤ ‖Complex.cosh ((ρ - 1/2) * (t : ℂ))‖ := norm_nonneg _
          linarith [h_cosh2]
        linarith [h_cosh1]

/-- Common pointwise bound function for the strip-uniform K_2 modulus. -/
private noncomputable def stripBound : ℝ → ℝ :=
  fun t => Real.cosh (|t|) + 2 * Real.cosh ((1/2) * |t|) + 1

private lemma stripBound_nn (t : ℝ) : 0 ≤ stripBound t := by
  unfold stripBound
  have h1 : (1 : ℝ) ≤ Real.cosh |t| := Real.one_le_cosh _
  have h2 : (1 : ℝ) ≤ Real.cosh ((1/2) * |t|) := Real.one_le_cosh _
  linarith

/-- `stripBound t · exp(-2t²)` is integrable on (0, ∞). -/
private lemma stripBound_mul_gauss_integrable :
    Integrable (fun t : ℝ => stripBound t * Real.exp (-2 * t^2))
      (volume.restrict (Ioi 0)) := by
  unfold stripBound
  -- Decompose into 3 integrable pieces.
  have h_cosh_int : ∀ a : ℝ, Integrable (fun t : ℝ =>
      Real.cosh (|a| * t) * Real.exp (-2 * t^2)) :=
    fun a => cosh_exp_neg_two_sq_integrable (|a|)
  have h_cosh_abs : ∀ a : ℝ, ∀ t : ℝ, Real.cosh (|a| * |t|) =
      Real.cosh (|a| * t) := by
    intro a t
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h]
    · push_neg at h
      rw [abs_of_neg h]
      rw [show |a| * (-t) = -((|a|) * t) from by ring]
      rw [Real.cosh_neg]
  have h1 : Integrable (fun t : ℝ => Real.cosh (|t|) * Real.exp (-2 * t^2)) := by
    have h := h_cosh_int 1
    have h_simp : ∀ t : ℝ, Real.cosh (|1| * t) * Real.exp (-2 * t^2) =
        Real.cosh (|t|) * Real.exp (-2 * t^2) := by
      intro t
      rw [abs_one, one_mul, Real.cosh_abs]
    refine h.congr ?_
    exact Filter.Eventually.of_forall h_simp
  have h2 : Integrable (fun t : ℝ =>
      Real.cosh ((1/2) * |t|) * Real.exp (-2 * t^2)) := by
    have h := h_cosh_int (1/2)
    have h_simp : ∀ t : ℝ, Real.cosh (|(1/2 : ℝ)| * t) * Real.exp (-2 * t^2) =
        Real.cosh ((1/2) * |t|) * Real.exp (-2 * t^2) := by
      intro t
      rw [show Real.cosh (|(1/2 : ℝ)| * t) = Real.cosh (|(1/2 : ℝ)| * |t|) from
          (h_cosh_abs (1/2) t).symm]
      rw [show |(1/2:ℝ)| = 1/2 from by norm_num]
    refine h.congr ?_
    exact Filter.Eventually.of_forall h_simp
  have h3 : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2)
  -- Combine via congr.
  have h_total_R : Integrable (fun t : ℝ =>
      (Real.cosh |t| + 2 * Real.cosh ((1/2) * |t|) + 1) * Real.exp (-2 * t^2)) := by
    have h_combo := (h1.add (h2.const_mul 2)).add h3
    refine h_combo.congr ?_
    apply Filter.Eventually.of_forall
    intro t
    show Real.cosh |t| * Real.exp (-2 * t^2) +
        2 * (Real.cosh ((1/2) * |t|) * Real.exp (-2 * t^2)) +
        Real.exp (-2 * t^2) =
        (Real.cosh |t| + 2 * Real.cosh ((1/2) * |t|) + 1) * Real.exp (-2 * t^2)
    ring
  exact h_total_R.integrableOn

/-- Pointwise bound for the per-zero norm integrand. -/
private lemma per_zero_norm_pointwise_le
    (β : ℝ) (n : ℂ → ℕ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) (t : ℝ) :
    ‖((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
      K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)‖ ≤
    ‖((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val‖ *
      (stripBound t * Real.exp (-2 * t^2)) := by
  rw [norm_mul, norm_mul]
  have hK : ‖K_2 ρ.val t‖ ≤ stripBound t := by
    unfold stripBound
    exact K_2_norm_le_NTZ t ρ.val ρ.property
  have h_exp : ‖Complex.exp (-2 * (t : ℂ)^2)‖ = Real.exp (-2 * t^2) := by
    have h_eq : (-2 : ℂ) * (t : ℂ)^2 = ((-2 * t^2 : ℝ) : ℂ) := by push_cast; ring
    rw [h_eq, Complex.norm_exp, Complex.ofReal_re]
  rw [h_exp]
  have hnn1 : 0 ≤ ‖((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val‖ := norm_nonneg _
  have hnnExp : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
  have hnnSB : 0 ≤ stripBound t := stripBound_nn t
  have hnnK : 0 ≤ ‖K_2 ρ.val t‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hK hnn1,
             mul_le_mul_of_nonneg_right
               (mul_le_mul_of_nonneg_left hK hnn1) hnnExp]

/-- Per-zero integrand is integrable on `(0,∞)`. -/
private lemma per_zero_integrable
    (β : ℝ) (n : ℂ → ℕ) (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    Integrable
      (fun t : ℝ => ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
        K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2))
      (volume.restrict (Ioi 0)) := by
  -- Bound by a constant times an integrable function.
  set c : ℝ := ‖((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val‖ with hc_def
  have hc_nn : 0 ≤ c := norm_nonneg _
  have h_dominated : Integrable
      (fun t : ℝ => c * (stripBound t * Real.exp (-2 * t^2)))
      (volume.restrict (Ioi 0)) :=
    stripBound_mul_gauss_integrable.const_mul c
  -- Measurability: K_2 and Complex.exp are continuous; constant multiplier is fine.
  have h_meas : AEStronglyMeasurable
      (fun t : ℝ => ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
        K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2))
      (volume.restrict (Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    unfold K_2
    fun_prop
  refine h_dominated.mono' h_meas ?_
  apply Filter.Eventually.of_forall
  intro t
  exact per_zero_norm_pointwise_le β n ρ t

/-- Norm-summability of the un-twisted multiplicity-weighted `M(β,·)` family.
Re-derives `h_sum_unconditional`'s internal norm-summable family. -/
private lemma summable_norm_n_M (β : ℝ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      ‖(((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val‖) := by
  obtain ⟨C, hC_nn, h_decay⟩ := Contour.pairTestMellin_im_sq_decay β
  have h_choose : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
        = ZD.xiOrderNat ρ.val := by
    intro ρ
    set h_ex := Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property
    have hspec := Classical.choose_spec h_ex
    have hxi := Contour.analyticOrderAt_riemannZeta_eq_xiOrderNat ρ.property
    have heq : ((Classical.choose h_ex : ℕ) : ℕ∞) =
        ((ZD.xiOrderNat ρ.val : ℕ) : ℕ∞) := by
      rw [← hspec.2, hxi]
    exact_mod_cast heq
  have h_major_summ : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left C
  refine h_major_summ.of_nonneg_of_le ?_ ?_
  · intro ρ; positivity
  · intro ρ
    rw [norm_mul, Complex.norm_natCast, h_choose]
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
    have h_pm_le' : ‖Contour.pairTestMellin β ρv‖ ≤ C / ‖ρv‖ ^ 2 := by
      calc ‖Contour.pairTestMellin β ρv‖ ≤ C / (1 + ρv.im ^ 2) := h_pm_le
        _ = C * (1 / (1 + ρv.im ^ 2)) := by ring
        _ ≤ C * (1 / ‖ρv‖ ^ 2) := mul_le_mul_of_nonneg_left h_inv_le hC_nn
        _ = C / ‖ρv‖ ^ 2 := by ring
    calc (ZD.xiOrderNat ρv : ℝ) * ‖Contour.pairTestMellin β ρv‖
        ≤ (ZD.xiOrderNat ρv : ℝ) * (C / ‖ρv‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_pm_le' h_n_nn
      _ = C * ((ZD.xiOrderNat ρv : ℝ) / ‖ρv‖ ^ 2) := by ring

/-- Per-zero `∫ ‖F_ρ‖ dt` summable in ρ (with canonical multiplicity), bounded by
norm-summable `n·M` family times the integrable `stripBound·exp(-2t²)`. -/
private lemma summable_per_zero_int_norm (β : ℝ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      ∫ t in Ioi (0:ℝ),
        ‖(((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
            Contour.pairTestMellin β ρ.val *
            K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)‖) := by
  set C_int : ℝ := ∫ t in Ioi (0:ℝ), stripBound t * Real.exp (-2 * t^2) with hC_int_def
  have hC_int_nn : 0 ≤ C_int := by
    apply MeasureTheory.integral_nonneg
    intro t
    simp only [Pi.zero_apply]
    exact mul_nonneg (stripBound_nn t) (Real.exp_pos _).le
  have h_majorant : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        ‖(((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
            Contour.pairTestMellin β ρ.val‖ * C_int) :=
    (summable_norm_n_M β).mul_right C_int
  refine h_majorant.of_nonneg_of_le (fun _ => MeasureTheory.integral_nonneg
    (fun _ => norm_nonneg _)) ?_
  intro ρ
  set c : ℂ := ((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
        Contour.pairTestMellin β ρ.val with hc_def
  -- Pointwise: ‖c · K_2(ρ,t) · exp(-2t²)‖ = ‖c‖ · ‖K_2(ρ,t)·exp(-2t²)‖ ≤ ‖c‖ · stripBound t · exp(-2t²).
  have h_meas_int_norm : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖c‖ * (stripBound t * Real.exp (-2 * t^2))) (Ioi 0) :=
    stripBound_mul_gauss_integrable.const_mul (‖c‖)
  have h_pointwise : ∀ t : ℝ,
      ‖c * K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)‖ ≤
        ‖c‖ * (stripBound t * Real.exp (-2 * t^2)) := by
    intro t
    rw [norm_mul, norm_mul]
    have hK : ‖K_2 ρ.val t‖ ≤ stripBound t := by
      unfold stripBound
      exact K_2_norm_le_NTZ t ρ.val ρ.property
    have h_exp : ‖Complex.exp (-2 * (t : ℂ)^2)‖ = Real.exp (-2 * t^2) := by
      have h_eq : (-2 : ℂ) * (t : ℂ)^2 = ((-2 * t^2 : ℝ) : ℂ) := by push_cast; ring
      rw [h_eq, Complex.norm_exp, Complex.ofReal_re]
    rw [h_exp]
    have hnn1 : 0 ≤ ‖c‖ := norm_nonneg _
    have hnnExp : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
    have hnnK : 0 ≤ ‖K_2 ρ.val t‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hK hnn1,
               mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hnn1) hnnExp]
  -- Per-zero integrability via dominated by stripBound·exp(-2t²).
  have h_F_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => c * K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) (Ioi 0) := by
    refine h_meas_int_norm.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold K_2
      fun_prop
    · apply Filter.Eventually.of_forall
      intro t
      exact h_pointwise t
  -- Bound the set-integral.
  have h_int_le : ∫ t in Ioi (0:ℝ), ‖c * K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)‖ ≤
      ∫ t in Ioi (0:ℝ), ‖c‖ * (stripBound t * Real.exp (-2 * t^2)) := by
    apply MeasureTheory.setIntegral_mono_on
    · exact h_F_int.norm
    · exact h_meas_int_norm
    · exact measurableSet_Ioi
    · intro t _; exact h_pointwise t
  rw [MeasureTheory.integral_const_mul] at h_int_le
  exact h_int_le

/-- **Fubini swap: K-twisted zero sum as a t-integral of inner zero sums.**

Combines `K_zeroSum_eq_tsum_t_integral` (per-zero Plancherel) with
Mathlib's `MeasureTheory.integral_tsum_of_summable_integral_norm` to
deliver the fully-swapped representation:

```
Σ' n(ρ) · K(ρ) · M(β, ρ)
  = 2π · ∫_{Ioi 0} ∑' ρ, ((n(ρ):ℂ) · M(β,ρ) · K_2(ρ, t) · exp(-2t²)) dt
```

with `n` the canonical multiplicity. Axiom footprint:
`[propext, Classical.choice, Quot.sound]`. -/
theorem K_zeroSum_eq_t_integral_inner_sum (β : ℝ) :
    (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        gaussianDefectEntireKernel_local ρ.val *
        Contour.pairTestMellin β ρ.val) =
    2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ),
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
          Contour.pairTestMellin β ρ.val *
          K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) := by
  classical
  set n : ℂ → ℕ := fun ρ : ℂ =>
    if hρ : ρ ∈ NontrivialZeros then
      Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
    else 0 with hn_def
  have hn_eq : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (n ρ.val : ℕ) = Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) := by
    intro ρ; simp [hn_def, ρ.property]
  -- Step 1: Apply K_zeroSum_eq_tsum_t_integral with this n.
  have h1 : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ((n ρ.val : ℕ) : ℂ) *
          gaussianDefectEntireKernel_local ρ.val *
          Contour.pairTestMellin β ρ.val) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        2 * (Real.pi : ℂ) * ∫ t in Ioi (0:ℝ),
          ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
            K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) :=
    K_zeroSum_eq_tsum_t_integral β n
  -- Step 2: Replace n with Classical.choose form via hn_eq.
  have h_lhs_rw : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        gaussianDefectEntireKernel_local ρ.val *
        Contour.pairTestMellin β ρ.val) =
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ((n ρ.val : ℕ) : ℂ) *
          gaussianDefectEntireKernel_local ρ.val *
          Contour.pairTestMellin β ρ.val) := by
    apply tsum_congr
    intro ρ; rw [hn_eq ρ]
  rw [h_lhs_rw, h1]
  -- Step 3: Pull `2π` out of the tsum.
  rw [tsum_mul_left]
  -- Step 4: Apply Fubini-Tonelli swap.
  congr 1
  set F : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ → ℂ := fun ρ t =>
    ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
      K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2) with hF_def
  -- Per-zero integrability.
  have hF_int : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      Integrable (F ρ) (volume.restrict (Ioi 0)) := per_zero_integrable β n
  -- Σ' ∫ ‖F‖ summable.
  have hF_sum : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      ∫ t in Ioi (0:ℝ), ‖F ρ t‖) := by
    have h := summable_per_zero_int_norm β
    refine h.congr ?_
    intro ρ
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    show ‖((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
        Contour.pairTestMellin β ρ.val *
        K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)‖ = ‖F ρ t‖
    rw [hF_def]; show _ = ‖((n ρ.val : ℕ) : ℂ) * _ * _ * _‖
    rw [hn_eq]
  -- Apply integral_tsum_of_summable_integral_norm.
  have h_swap := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  -- The LHS ∑' ∫ matches F via hn_eq.
  have h_lhs_match :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ∫ t in Ioi (0:ℝ),
          ((n ρ.val : ℕ) : ℂ) * Contour.pairTestMellin β ρ.val *
            K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, ∫ t in Ioi (0:ℝ), F ρ t := by
    apply tsum_congr
    intro ρ
    rfl
  rw [h_lhs_match, h_swap]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply tsum_congr
  intro ρ
  show F ρ t = ((Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ) *
      Contour.pairTestMellin β ρ.val *
      K_2 ρ.val t * Complex.exp (-2 * (t : ℂ)^2)
  rw [hF_def]; show ((n ρ.val : ℕ) : ℂ) * _ * _ * _ = _
  rw [hn_eq]

#print axioms K_zeroSum_eq_t_integral_inner_sum

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
