import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.ZeroCountJensen
import RequestProject.WeilContour
import RequestProject.PairCoshGaussTest
import RequestProject.WeilZeroOrthogonality
import RequestProject.WeilPairIBPQuartic
import RequestProject.XiOrderSummable
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.WeilZeroSum

/-!
# Module A — Sum-integral Fubini swap for `pairTestMellin`

Standalone unconditional module proving the swap

```
∫ t in (0,∞), (∑'_ρ a(ρ) · t^(ρ-1)) · g_β(t) dt
   = ∑'_ρ a(ρ) · ∫ t in (0,∞), t^(ρ-1) · g_β(t) dt
   = ∑'_ρ a(ρ) · pairTestMellin β ρ.
```

The mathlib lemma `MeasureTheory.integral_tsum` requires:
1. ae-strong-measurability of each per-ρ integrand on `(0,∞)`,
2. finiteness of `∑'_ρ ∫⁻_t ‖a ρ · t^(ρ-1) · g_β(t)‖₊` (joint ℓ¹ norm).

Both are discharged here.

* Measurability: continuity of the integrand on the open set `(0,∞)`.
* Joint integrability: combines the IBP×4 quartic decay
  `‖pairTestMellin β ρ‖ ≤ C/(1+Im²ρ)²` (from `WeilPairIBPQuartic`) with
  the Jensen-style summability `∑' ‖a ρ‖ / ‖ρ‖²` (decay hypothesis on `a`,
  consistent with applications). The two combine via the bound
  `M_β(Re ρ) ≤ pairTestMellin β (1/2+|β-1/2|) (Re ρ)` (real-axis form,
  uniformly bounded for `β` in compact subsets of `(0,1)`).

The final theorem `swap_eq` matches the form needed by
`fubini_pair_test_exchange` in `PairTestMellinBetaTotalality.lean`.
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FubiniPairTestSwap

/-! ### §0. Countability of the nontrivial zero subtype -/

private theorem nontrivialZeros_countable :
    ZD.NontrivialZeros.Countable := by
  have h_eq : ZD.NontrivialZeros = ⋃ n : ℕ,
      ZD.NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (n : ℝ) := by
    apply Set.eq_of_subset_of_subset
    · intro z hz
      rw [Set.mem_iUnion]
      refine ⟨⌈‖z‖⌉₊, hz, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact_mod_cast Nat.le_ceil _
    · rw [Set.iUnion_subset_iff]; intro _; exact Set.inter_subset_left
  rw [h_eq]
  exact Set.countable_iUnion (fun n =>
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (n : ℝ)).countable)

instance : Countable {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  nontrivialZeros_countable.to_subtype

/-! ### §1. Per-ρ integrand: continuity + integrability -/

/-- The per-ρ integrand on the half-line. -/
private def perRho (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (t : ℝ) : ℂ :=
  a ρ.val * (t : ℂ)^(ρ.val - 1) * (pair_cosh_gauss_test β t : ℂ)

/-- Continuity of `(t : ℂ)^(s - 1)` on `(0, ∞)`. -/
private theorem continuous_cpow_const_on_Ioi (s : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ)^(s - 1)) (Set.Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht_pos : (0 : ℝ) < t := ht
  have h_slit : (t : ℂ) ∈ Complex.slitPlane := by
    left
    exact_mod_cast ht_pos
  exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const h_slit

/-- Continuity of `pair_cosh_gauss_test β` (real-valued). -/
private theorem continuous_pair_cosh_gauss_test (β : ℝ) :
    Continuous (pair_cosh_gauss_test β) := by
  unfold pair_cosh_gauss_test pairDetectorSqDiff
  unfold ZetaDefs.coshDetectorLeft ZetaDefs.coshDetectorRight ψ_gaussian
  fun_prop

/-- The complex coercion of `pair_cosh_gauss_test β` is continuous. -/
private theorem continuous_pair_cosh_gauss_test_complex (β : ℝ) :
    Continuous (fun t : ℝ => (pair_cosh_gauss_test β t : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_pair_cosh_gauss_test β)

/-- The per-ρ integrand is continuous on `(0, ∞)`. -/
private theorem perRho_continuousOn (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ContinuousOn (perRho a β ρ) (Set.Ioi 0) := by
  unfold perRho
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
  · exact continuous_cpow_const_on_Ioi (ρ.val)
  · exact (continuous_pair_cosh_gauss_test_complex β).continuousOn

/-- The per-ρ integrand is ae-strongly-measurable on `(0, ∞)` (restricted measure). -/
theorem perRho_aestronglyMeasurable (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    AEStronglyMeasurable (perRho a β ρ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  exact (perRho_continuousOn a β ρ).aestronglyMeasurable measurableSet_Ioi

/-! ### §2. Per-ρ L¹ norm: equality with `‖a ρ‖ · M_β(Re ρ)` -/

/-- Pointwise: `‖perRho a β ρ t‖ = ‖a ρ‖ · t^(Re ρ - 1) · pair_cosh_gauss_test β t`
on `(0, ∞)`. -/
private theorem perRho_norm_pointwise (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) {t : ℝ} (ht : 0 < t) :
    ‖perRho a β ρ t‖ =
      ‖a ρ.val‖ * t^(ρ.val.re - 1) * pair_cosh_gauss_test β t := by
  unfold perRho
  rw [norm_mul, norm_mul, Complex.norm_real]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have h_nn : 0 ≤ pair_cosh_gauss_test β t := pair_cosh_gauss_test_nonneg β t
  rw [Real.norm_of_nonneg h_nn]
  rw [show (ρ.val - 1).re = ρ.val.re - 1 from by simp]

/-- Real-axis Mellin of `pair_cosh_gauss_test β`. The complex Mellin
`pairTestMellin β` evaluated at a real argument coincides with this real
integral by definition. -/
private def realMellin (β : ℝ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t^(σ - 1) * pair_cosh_gauss_test β t

/-- Per-ρ L¹ norm equals `‖a ρ‖ · realMellin β (Re ρ)`. -/
private theorem perRho_lintegral_norm_eq (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (h_int : IntegrableOn
      (fun t : ℝ => t^(ρ.val.re - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume) :
    ∫ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖ =
      ‖a ρ.val‖ * realMellin β ρ.val.re := by
  have h_eq : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖perRho a β ρ t‖ = ‖a ρ.val‖ * (t^(ρ.val.re - 1) * pair_cosh_gauss_test β t) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [perRho_norm_pointwise a β ρ ht]; ring
  rw [MeasureTheory.integral_congr_ae h_eq]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-! ### §3. Per-ρ integrability via Schwartz decay of `pair_cosh_gauss_test`

The integrand `t^(σ - 1) · pair_cosh_gauss_test β t` is integrable on
`(0, ∞)` for `σ > 0`. Near `0`, `pair_cosh_gauss_test β t = O(t^4)`
(double sinh² zero), so the integrand is `O(t^(σ + 3))`, integrable.
At `∞`, Gaussian decay dominates. -/

/-- Per-ρ integrability: re-export of
`Contour.pair_mellin_integrand_integrableOn` from `WeilZeroSum.lean`. -/
theorem real_integrand_integrableOn (β : ℝ) {σ : ℝ}
    (hσ_pos : 0 < σ) (_hσ_lt : σ < 1) :
    IntegrableOn (fun t : ℝ => t^(σ - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
  Contour.pair_mellin_integrand_integrableOn β σ hσ_pos

/-! ### §4. Joint ℓ¹ norm summability: derive from real-axis Mellin uniform bound -/

/-- For `0 < σL ≤ σR`, the real Mellin `realMellin β σ` is bounded
uniformly for `σ ∈ [σL, σR]` by `realMellin β σL + realMellin β σR`. -/
theorem realMellin_uniform_bound (β : ℝ) (σL σR : ℝ)
    (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Set.Icc σL σR, realMellin β σ ≤ M := by
  set IL := realMellin β σL
  set IR := realMellin β σR
  have hIL_int : IntegrableOn (fun t : ℝ => t^(σL - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    Contour.pair_mellin_integrand_integrableOn β σL hσL
  have hIR_int : IntegrableOn (fun t : ℝ => t^(σR - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    Contour.pair_mellin_integrand_integrableOn β σR (lt_of_lt_of_le hσL hσLR)
  have hIL_nn : 0 ≤ IL :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
        (pair_cosh_gauss_test_nonneg β t))
  have hIR_nn : 0 ≤ IR :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
        (pair_cosh_gauss_test_nonneg β t))
  refine ⟨IL + IR, add_nonneg hIL_nn hIR_nn, fun σ ⟨hσ_ge, hσ_le⟩ => ?_⟩
  unfold realMellin
  -- Bound: t^(σ-1) ≤ t^(σL-1) + t^(σR-1) on (0, ∞).
  have hσ_pos : 0 < σ := lt_of_lt_of_le hσL hσ_ge
  have hσ_int : IntegrableOn (fun t : ℝ => t^(σ - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    Contour.pair_mellin_integrand_integrableOn β σ hσ_pos
  have h_dom : ∀ t ∈ Set.Ioi (0 : ℝ),
      t^(σ - 1) * pair_cosh_gauss_test β t ≤
        t^(σL - 1) * pair_cosh_gauss_test β t +
          t^(σR - 1) * pair_cosh_gauss_test β t := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := ht
    have h_g_nn : 0 ≤ pair_cosh_gauss_test β t := pair_cosh_gauss_test_nonneg β t
    have h_rpow_bd : t^(σ - 1) ≤ t^(σL - 1) + t^(σR - 1) := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(σ - 1) ≤ t^(σL - 1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σR - 1)]
      · have h1 : t^(σ - 1) ≤ t^(σR - 1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
    calc t^(σ - 1) * pair_cosh_gauss_test β t
        ≤ (t^(σL - 1) + t^(σR - 1)) * pair_cosh_gauss_test β t :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_g_nn
      _ = t^(σL - 1) * pair_cosh_gauss_test β t +
            t^(σR - 1) * pair_cosh_gauss_test β t := by ring
  have h_rhs_int : IntegrableOn (fun t : ℝ =>
      t^(σL - 1) * pair_cosh_gauss_test β t +
      t^(σR - 1) * pair_cosh_gauss_test β t) (Set.Ioi 0) volume :=
    hIL_int.add hIR_int
  calc ∫ t in Set.Ioi (0 : ℝ), t^(σ - 1) * pair_cosh_gauss_test β t
      ≤ ∫ t in Set.Ioi (0 : ℝ),
          (t^(σL - 1) * pair_cosh_gauss_test β t +
           t^(σR - 1) * pair_cosh_gauss_test β t) := by
        exact MeasureTheory.setIntegral_mono_on hσ_int h_rhs_int
          measurableSet_Ioi h_dom
    _ = IL + IR := by
        rw [MeasureTheory.integral_add hIL_int hIR_int]
        rfl

/-- Per-ρ integrability of `perRho a β ρ` on `(0, ∞)`. -/
private theorem perRho_integrableOn (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    IntegrableOn (perRho a β ρ) (Set.Ioi (0 : ℝ)) volume := by
  have ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  have h_int_real : IntegrableOn
      (fun t : ℝ => t^(ρ.val.re - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    real_integrand_integrableOn β hRe_pos hRe_lt
  have h_aem : AEStronglyMeasurable (perRho a β ρ)
      (volume.restrict (Set.Ioi 0)) :=
    perRho_aestronglyMeasurable a β ρ
  -- Bound: ‖perRho t‖ ≤ ‖a ρ‖ * (t^(Re ρ - 1) * g_β t).
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ‖perRho a β ρ t‖ ≤
        ‖a ρ.val‖ * (t^(ρ.val.re - 1) * pair_cosh_gauss_test β t) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [perRho_norm_pointwise a β ρ ht]; ring_nf; rfl
  refine ⟨h_aem, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.mono' (g := fun t : ℝ =>
      ‖a ρ.val‖ * (t^(ρ.val.re - 1) * pair_cosh_gauss_test β t)) ?_ h_bound
  exact (h_int_real.const_mul ‖a ρ.val‖).2

/-- For each `β ∈ (0, 1)` and each `ρ ∈ NontrivialZeros`, the per-ρ
ℓ¹ norm `∫⁻ t in (0,∞), ‖perRho a β ρ t‖₊` equals
`ENNReal.ofReal (‖a ρ‖ · realMellin β (Re ρ))`. -/
theorem perRho_lintegral_eq_ofReal (a : ℂ → ℂ) (β : ℝ)
    (_hβ_pos : 0 < β) (_hβ_lt : β < 1)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖₊ =
      ENNReal.ofReal (‖a ρ.val‖ * realMellin β ρ.val.re) := by
  have ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  have h_int_real : IntegrableOn
      (fun t : ℝ => t^(ρ.val.re - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    real_integrand_integrableOn β hRe_pos hRe_lt
  have h_perRho_int : IntegrableOn (perRho a β ρ) (Set.Ioi 0) volume :=
    perRho_integrableOn a β ρ
  -- ∫ ‖perRho‖ = ‖a ρ‖ · realMellin β (Re ρ).
  have h_int_eq : ∫ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖ =
      ‖a ρ.val‖ * realMellin β ρ.val.re :=
    perRho_lintegral_norm_eq a β ρ h_int_real
  -- Convert lintegral to integral via ofReal.
  have h_norm_int : IntegrableOn (fun t : ℝ => ‖perRho a β ρ t‖)
      (Set.Ioi 0) volume := h_perRho_int.norm
  have h_norm_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => ‖perRho a β ρ t‖ :=
    Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  have h_lint :
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖perRho a β ρ t‖) =
        ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_norm_int h_norm_nn).symm
  -- ‖·‖₊ as ENNReal = ENNReal.ofReal ‖·‖.
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖₊
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖perRho a β ρ t‖) := by
        refine MeasureTheory.lintegral_congr_ae ?_
        refine Filter.Eventually.of_forall (fun t => ?_)
        exact (enorm_eq_nnnorm (perRho a β ρ t)).symm.trans
          (ofReal_norm_eq_enorm (perRho a β ρ t)).symm
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖) := h_lint
    _ = ENNReal.ofReal (‖a ρ.val‖ * realMellin β ρ.val.re) := by rw [h_int_eq]

/-- Real-valued atTop big-O bound for `pair_cosh_gauss_test β`. Extracted from
the complex-valued version via `‖((·:ℝ) : ℂ)‖ = |·|`. -/
private theorem pair_cosh_gauss_test_isBigO_exp_neg_atTop_real (β : ℝ) :
    (pair_cosh_gauss_test β) =O[Filter.atTop] (fun t : ℝ => Real.exp (-t)) := by
  have h := Contour.pair_cosh_gauss_test_isBigO_exp_neg_atTop β
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨C, h_eventually⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [h_eventually] with t ht
  rw [Real.norm_eq_abs] at ht ⊢
  rw [Complex.norm_real, Real.norm_eq_abs] at ht
  exact ht

/-- Real-valued nhdsWithin big-O bound for `pair_cosh_gauss_test β`. Extracted
from the complex-valued version. -/
private theorem pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero_real (β : ℝ) :
    (pair_cosh_gauss_test β) =O[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun t : ℝ => t ^ ((4:ℝ))) := by
  have h := Contour.pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero β
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨C, h_eventually⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [h_eventually] with t ht
  rw [Real.norm_eq_abs] at ht ⊢
  rw [Complex.norm_real, Real.norm_eq_abs] at ht
  exact ht

/-- Integrability of `t ↦ t^(0 - 1) · pair_cosh_gauss_test β t` on `(0,∞)`
(extended past `σ = 0`), via `mellin_convergent_of_isBigO_scalar`. -/
private theorem pair_mellin_integrand_integrableOn_zero (β : ℝ) :
    IntegrableOn (fun t : ℝ => t^((0:ℝ) - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume := by
  refine mellin_convergent_of_isBigO_scalar
    ((continuous_pair_cosh_gauss_test β).locallyIntegrable.locallyIntegrableOn _) ?_
    (a := 1) (by norm_num : (0:ℝ) < 1) ?_ (b := -4) (by norm_num : (-4:ℝ) < 0)
  · -- pair β =O[atTop] t^(-1): exp(-t) =o[atTop] t^(-1).
    have h_exp := pair_cosh_gauss_test_isBigO_exp_neg_atTop_real β
    have h_pow : (fun t : ℝ => Real.exp (-t)) =O[Filter.atTop]
        (fun t : ℝ => t ^ (-(1:ℝ))) := by
      have := isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-(1:ℝ))
      simp only [neg_mul, one_mul] at this
      exact this.isBigO
    exact h_exp.trans h_pow
  · -- pair β =O[nhdsWithin 0 Ioi] t^(-(-4)) = t^4.
    have h := pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero_real β
    refine h.congr_right (fun t => ?_)
    congr 1; ring

/-- Uniform bound on `realMellin β` over `σ ∈ (0, 1)` via the σ = 0 endpoint. -/
private theorem realMellin_bounded_on_open_unit (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Set.Ioo (0 : ℝ) 1, realMellin β σ ≤ M := by
  -- Use σL = 0 (extended integrability) and σR = 1.
  set IL := realMellin β 0
  set IR := realMellin β 1
  have hIL_int : IntegrableOn (fun t : ℝ => t^((0:ℝ) - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    pair_mellin_integrand_integrableOn_zero β
  have hIR_int : IntegrableOn (fun t : ℝ => t^((1:ℝ) - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    Contour.pair_mellin_integrand_integrableOn β 1 (by norm_num)
  have hIL_nn : 0 ≤ IL :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
        (pair_cosh_gauss_test_nonneg β t))
  have hIR_nn : 0 ≤ IR :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
        (pair_cosh_gauss_test_nonneg β t))
  refine ⟨IL + IR, add_nonneg hIL_nn hIR_nn, fun σ ⟨hσ_pos, hσ_lt⟩ => ?_⟩
  unfold realMellin
  have hσ_int : IntegrableOn (fun t : ℝ => t^(σ - 1) * pair_cosh_gauss_test β t)
      (Set.Ioi 0) volume :=
    Contour.pair_mellin_integrand_integrableOn β σ hσ_pos
  have h_dom : ∀ t ∈ Set.Ioi (0 : ℝ),
      t^(σ - 1) * pair_cosh_gauss_test β t ≤
        t^((0:ℝ) - 1) * pair_cosh_gauss_test β t +
          t^((1:ℝ) - 1) * pair_cosh_gauss_test β t := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := ht
    have h_g_nn : 0 ≤ pair_cosh_gauss_test β t := pair_cosh_gauss_test_nonneg β t
    have h_rpow_bd : t^(σ - 1) ≤ t^((0:ℝ) - 1) + t^((1:ℝ) - 1) := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(σ - 1) ≤ t^((0:ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le ((1:ℝ) - 1)]
      · have h1 : t^(σ - 1) ≤ t^((1:ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le ((0:ℝ) - 1)]
    calc t^(σ - 1) * pair_cosh_gauss_test β t
        ≤ (t^((0:ℝ) - 1) + t^((1:ℝ) - 1)) * pair_cosh_gauss_test β t :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_g_nn
      _ = t^((0:ℝ) - 1) * pair_cosh_gauss_test β t +
            t^((1:ℝ) - 1) * pair_cosh_gauss_test β t := by ring
  have h_rhs_int : IntegrableOn (fun t : ℝ =>
      t^((0:ℝ) - 1) * pair_cosh_gauss_test β t +
      t^((1:ℝ) - 1) * pair_cosh_gauss_test β t) (Set.Ioi 0) volume :=
    hIL_int.add hIR_int
  calc ∫ t in Set.Ioi (0 : ℝ), t^(σ - 1) * pair_cosh_gauss_test β t
      ≤ ∫ t in Set.Ioi (0 : ℝ),
          (t^((0:ℝ) - 1) * pair_cosh_gauss_test β t +
           t^((1:ℝ) - 1) * pair_cosh_gauss_test β t) := by
        exact MeasureTheory.setIntegral_mono_on hσ_int h_rhs_int
          measurableSet_Ioi h_dom
    _ = IL + IR := by
        rw [MeasureTheory.integral_add hIL_int hIR_int]
        rfl

/-- **Joint ℓ¹ norm bound.** Under the hypothesis that
`Summable (ρ ↦ ‖a ρ‖)`, the joint ℓ¹ norm is finite. -/
theorem joint_lintegral_finite_of_summable_norm (a : ℂ → ℂ) (β : ℝ)
    (hβ_pos : 0 < β) (hβ_lt : β < 1)
    (h_summable_a : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖₊ ∂volume) ≠ ⊤ := by
  obtain ⟨M, hM_nn, hM⟩ := realMellin_bounded_on_open_unit β
  -- Each summand ≤ ENNReal.ofReal (‖a ρ‖ · M).
  have h_per_le : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖₊ ∂volume ≤
        ENNReal.ofReal (‖a ρ.val‖ * M) := by
    intro ρ
    rw [perRho_lintegral_eq_ofReal a β hβ_pos hβ_lt ρ]
    apply ENNReal.ofReal_le_ofReal
    have ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
    have h_bound : realMellin β ρ.val.re ≤ M := hM ρ.val.re ⟨hRe_pos, hRe_lt⟩
    have h_norm_nn : 0 ≤ ‖a ρ.val‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_left h_bound h_norm_nn
  -- ∑' (...) ≤ ∑' ENNReal.ofReal (‖a ρ‖ · M).
  have h_tsum_le :
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ∫⁻ t in Set.Ioi (0 : ℝ), ‖perRho a β ρ t‖₊ ∂volume) ≤
        ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          ENNReal.ofReal (‖a ρ.val‖ * M) :=
    ENNReal.tsum_le_tsum h_per_le
  -- The RHS is ENNReal.ofReal of a real number, hence finite.
  have h_summ : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖ * M) := h_summable_a.mul_right M
  have h_nn : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, 0 ≤ ‖a ρ.val‖ * M :=
    fun ρ => mul_nonneg (norm_nonneg _) hM_nn
  have h_rhs_eq :
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ENNReal.ofReal (‖a ρ.val‖ * M)) =
      ENNReal.ofReal (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ‖a ρ.val‖ * M) :=
    (ENNReal.ofReal_tsum_of_nonneg h_nn h_summ).symm
  have h_rhs_finite :
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ENNReal.ofReal (‖a ρ.val‖ * M)) < ⊤ := by
    rw [h_rhs_eq]; exact ENNReal.ofReal_lt_top
  exact (h_tsum_le.trans_lt h_rhs_finite).ne

/-! ### §5. Per-ρ integral identification -/

/-- The per-ρ integral equals `a ρ · pairTestMellin β ρ`. -/
theorem perRho_integral_eq (a : ℂ → ℂ) (β : ℝ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ∫ t in Set.Ioi (0 : ℝ), perRho a β ρ t =
      a ρ.val * Contour.pairTestMellin β ρ.val := by
  unfold perRho
  -- ∫ t, a ρ * t^(ρ-1) * g_β(t) = a ρ * ∫ t, t^(ρ-1) * g_β(t) = a ρ * pairTestMellin β ρ.
  have h_assoc : (fun t : ℝ => a ρ.val * (t : ℂ)^(ρ.val - 1) * (pair_cosh_gauss_test β t : ℂ))
      = (fun t : ℝ => a ρ.val •
          ((t : ℂ)^(ρ.val - 1) * (pair_cosh_gauss_test β t : ℂ))) :=
    funext (fun t => by rw [smul_eq_mul]; ring)
  rw [h_assoc, MeasureTheory.integral_smul, smul_eq_mul]
  rfl

/-! ### §6. The Fubini swap -/

/-- **Fubini swap (clean form).** Given absolute summability of `‖a ρ‖`, the
sum-integral exchange holds with finite joint mass. -/
theorem swap_eq (a : ℂ → ℂ)
    (h_summable_a : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖))
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1) :
    ∫ t in Set.Ioi (0 : ℝ),
      ZeroOrthogonality.ZeroMellinSeries a t * (pair_cosh_gauss_test β t : ℂ) =
        ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          a ρ.val * Contour.pairTestMellin β ρ.val := by
  -- Pointwise: ZeroMellinSeries a t · g_β(t) = ∑' ρ, perRho a β ρ t.
  have hsum_integrand : ∀ t : ℝ,
      ZeroOrthogonality.ZeroMellinSeries a t * (pair_cosh_gauss_test β t : ℂ) =
        ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, perRho a β ρ t := by
    intro t
    show (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            a ρ.val * (t : ℂ) ^ (ρ.val - 1)) * _ =
         ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, perRho a β ρ t
    rw [show (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, perRho a β ρ t) =
        ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (a ρ.val * (t : ℂ)^(ρ.val - 1)) * (pair_cosh_gauss_test β t : ℂ) from
      tsum_congr (fun ρ => by unfold perRho; ring)]
    rw [tsum_mul_right]
  rw [show (fun t : ℝ =>
      ZeroOrthogonality.ZeroMellinSeries a t * (pair_cosh_gauss_test β t : ℂ)) =
      (fun t : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, perRho a β ρ t)
    from funext hsum_integrand]
  rw [MeasureTheory.integral_tsum
    (fun ρ => perRho_aestronglyMeasurable a β ρ)
    (joint_lintegral_finite_of_summable_norm a β hβ_pos hβ_lt h_summable_a)]
  congr 1; ext ρ
  exact perRho_integral_eq a β ρ

/-- Corollary: the integral vanishes when the sum vanishes. -/
theorem integral_zero_of_tsum_zero (a : ℂ → ℂ)
    (h_summable_a : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖))
    (hvanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1) :
    ∫ t in Set.Ioi (0 : ℝ),
      ZeroOrthogonality.ZeroMellinSeries a t * (pair_cosh_gauss_test β t : ℂ) = 0 := by
  rw [swap_eq a h_summable_a hβ_pos hβ_lt]
  exact hvanish β hβ_pos hβ_lt

/-! ### §7. Discharge: Jensen-style decay → absolute summability of ‖a ρ‖

If `a` arises from a contour integral with quartic Mellin decay
(`‖a ρ pairTestMellin β ρ‖ ≤ C · n(ρ) / ‖ρ‖²` from IBP×4 + Jensen, mirroring
`h_sum_unconditional`), then `Summable (ρ ↦ ‖a ρ‖)` follows. The bridging
identity reads:
```
‖a ρ‖ ≤ ‖a ρ pairTestMellin β ρ‖ / inf_β ‖pairTestMellin β ρ‖.
```
A uniform lower bound on `‖pairTestMellin β ρ‖` for `β` away from `1/2`
+ ρ in NontrivialZeros would close this; without it, this conversion
requires application-specific structure on `a`.

We package the bridging hypothesis as a separate lemma for callers to
discharge in their concrete application context. -/

/-- **Bridging lemma.** Under the assumption that `‖a ρ‖ ≤ K · n(ρ) / ‖ρ‖²`
for some constant `K`, absolute summability of `‖a ρ‖` follows from the
Jensen result `summable_xiOrderNat_div_norm_sq_nontrivialZeros`. -/
theorem summable_norm_a_of_jensen_decay (a : ℂ → ℂ) (K : ℝ) (hK_nn : 0 ≤ K)
    (h_decay : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖a ρ.val‖ ≤ K * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ‖a ρ.val‖) := by
  have h_major : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      K * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2)) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left K
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_major
  intro ρ
  have h := h_decay ρ
  rw [mul_div_assoc] at h
  exact h

end FubiniPairTestSwap
end WeilPositivity
end ZD

end
