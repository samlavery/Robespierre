import Mathlib
import RequestProject.CauchyKPairTest
import RequestProject.WeilExplicitFormulaPlaceholder

/-!
# K-twisted Cauchy/Weil identity in the `T → ∞` limit

Takes the finite-`T` K-twisted rectangle identity
(`rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum`)
to its `T → ∞` form by identifying

* horizontal-edge contributions vanish along `atTop ⊓ {goodHeight}`
  (target: `K_pairTestMellin_horizontal_vanishes_target`),
* vertical-edge integrals tend to whole-line integrals
  (targets: `K_pairTestMellin_vertical_at_two_integrable`,
  `K_pairTestMellin_vertical_at_neg_one_integrable`),
* the finset residue sum tends to the absolutely convergent zero-sum
  (target: `K_pairTestMellin_residue_sum_tendsto`).

The output is the **whole-line K-twisted Weil identity** (corrected, no spurious
`I` on the RHS):

```
(∫_ℝ K(2+iy) · weilIntegrand(pairTestMellin β)(2+iy) dy)
- (∫_ℝ K(-1+iy) · weilIntegrand(pairTestMellin β)(-1+iy) dy)
  = 2π · (K(1) · pairTestMellin β 1 − Σ' n(ρ) · K(ρ) · pairTestMellin β ρ)
```

Each target Prop is discharged separately; this file delivers the conditional
limit identity.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly

/-! ## Targets for the four T → ∞ ingredients -/

/-- Horizontal vanishing of `K · weilIntegrand(pairTestMellin β)` at `Im = ±T`,
along `atTop ⊓ {goodHeight}`. -/
def K_pairTestMellin_horizontal_vanishes_target
    (K : ℂ → ℂ) (β : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖(∫ x : ℝ in (-1 : ℝ)..2,
        K ((x : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
      (∫ x : ℝ in (-1 : ℝ)..2,
        K ((x : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ < ε

/-- Whole-line integrability of `K · weilIntegrand(pairTestMellin β)` on the
right edge `Re s = 2`. -/
def K_pairTestMellin_vertical_at_two_integrable
    (K : ℂ → ℂ) (β : ℝ) : Prop :=
  Integrable
    (fun y : ℝ => K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I))

/-- Whole-line integrability of `K · weilIntegrand(pairTestMellin β)` on the
left edge `Re s = -1`. -/
def K_pairTestMellin_vertical_at_neg_one_integrable
    (K : ℂ → ℂ) (β : ℝ) : Prop :=
  Integrable
    (fun y : ℝ => K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I))

/-- The finset residue sum tends to the absolutely-convergent zero-sum as
`T → ∞` along `atTop ⊓ {goodHeight}`. The function `Z_at : ℝ → Finset ℂ`
must (per the standard `Z_mem`/`Z_complete` shape used by
`rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum`)
return the set of nontrivial zeros enclosed by `[-1, 2] × [-T, T]`. -/
def K_pairTestMellin_residue_sum_tendsto
    (K : ℂ → ℂ) (β : ℝ) (n : ℂ → ℕ) (Z_at : ℝ → Finset ℂ) : Prop :=
  Tendsto
    (fun T : ℝ => ∑ ρ ∈ Z_at T,
        ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ)
    (atTop ⊓ Filter.principal {T : ℝ | goodHeight T})
    (nhds (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val))

/-! ## Conditional `T → ∞` identity -/

/-- **Whole-line K-twisted Weil identity (corrected, conditional).**

Given the four T → ∞ ingredients (horizontal vanishing, vertical-edge
integrability at `Re = 2` and `Re = -1`, residue-sum tendsto), the K-twisted
Weil identity holds in its `T → ∞` form:
```
∫_ℝ K(2+iy) · weilIntegrand(M)(2+iy) dy − ∫_ℝ K(-1+iy) · weilIntegrand(M)(-1+iy) dy
  = 2π · (K(1) · M(β,1) − Σ' n(ρ) · K(ρ) · M(β,ρ))
```
where `M = pairTestMellin β` and `n(ρ)` is the analytic order at `ρ`.

Mirrors `archIntegrand_diff_at_two_minus_neg_one_of_horizontal_vanishes`
exactly, but with `K · weilIntegrand(M)` in place of
`pairTestMellin_archKernel_product`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_K_pairTestMellin_T_limit
    (K : ℂ → ℂ) (hK : Differentiable ℂ K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (n : ℂ → ℕ) (Z_at : ℝ → Finset ℂ)
    (hZ_mem : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ ∈ Z_at T,
      ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ : ℂ,
      ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z_at T)
    (h_horiz : K_pairTestMellin_horizontal_vanishes_target K β)
    (h_int_pos : K_pairTestMellin_vertical_at_two_integrable K β)
    (h_int_neg : K_pairTestMellin_vertical_at_neg_one_integrable K β)
    (h_res_tendsto : K_pairTestMellin_residue_sum_tendsto K β n Z_at) :
    (∫ y : ℝ, K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y : ℝ, K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
    2 * ((Real.pi : ℝ) : ℂ) *
      (K 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val) := by
  -- Abbreviations.
  set R : ℂ := K 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val with hR_def
  set Aplus : ℂ := ∫ y : ℝ, K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I) with hAplus_def
  set Aminus : ℂ := ∫ y : ℝ, K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I) with hAminus_def
  show Aplus - Aminus = 2 * ((Real.pi : ℝ) : ℂ) * R
  -- Vertical tendstos along atTop.
  have h_pos_tendsto :
      Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T,
          K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I))
        atTop (nhds Aplus) :=
    intervalIntegral_tendsto_integral h_int_pos
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have h_neg_tendsto :
      Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T,
          K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
        atTop (nhds Aminus) :=
    intervalIntegral_tendsto_integral h_int_neg
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  -- f(T) = I·(right - left), tends to I·(Aplus - Aminus) along atTop.
  set f : ℝ → ℂ := fun T : ℝ =>
    I • ((∫ y : ℝ in (-T)..T,
          K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        (∫ y : ℝ in (-T)..T,
          K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
    with hf_def
  have h_f_atTop :
      Tendsto f atTop (nhds (I • (Aplus - Aminus))) := by
    simp only [hf_def]
    exact (h_pos_tendsto.sub h_neg_tendsto).const_smul I
  -- Target: I·(Aplus - Aminus) = 2πi·R, then cancel I.
  set Rfull : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I * R with hRfull_def
  -- Set the tsum target and per-T residue.
  set Stsum : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val with hStsum_def
  set ZsumT : ℝ → ℂ := fun T => ∑ ρ ∈ Z_at T,
      ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ with hZsumT_def
  set ΔbotT : ℝ → ℂ := fun T => (∫ x : ℝ in (-1 : ℝ)..2,
        K ((x : ℂ) + (-T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
      (∫ x : ℝ in (-1 : ℝ)..2,
        K ((x : ℂ) + (T : ℝ) * I) *
          weilIntegrand (Contour.pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))
    with hΔbotT_def
  -- Compute f(T) using the finite-T identity for T > 1, goodHeight T.
  -- Identity: I•(right − left) = 2πI·(K(1)·M(β,1) − Σ_{ρ ∈ Z_at T}) − (bot − top)
  --        = Rfull + 2πI·(Stsum − ZsumT) − ΔbotT
  -- where Rfull = 2πI·R and R = K(1)·M(β,1) − Stsum.
  have h_f_eq : ∀ T : ℝ, 1 < T → goodHeight T → f T =
      Rfull + 2 * ((Real.pi : ℝ) : ℂ) * I * (Stsum - ZsumT T) - ΔbotT T := by
    intro T hT hGood
    have h_rect := rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum
      K hK β hβ hT hGood n (Z_at T) (hZ_mem T hT hGood) (hZ_complete T hT hGood)
    simp only [Contour.rectContourIntegral, smul_eq_mul] at h_rect
    -- h_rect: (bottom - top) + I*right - I*left =
    --   2πI·(K(1)·M(β,1) - Σ_{ρ ∈ Z_at T} n(ρ)·K(ρ)·M(β,ρ))
    simp only [hf_def, hR_def, hRfull_def, hZsumT_def, hΔbotT_def, hStsum_def, smul_eq_mul]
    linear_combination h_rect
  -- Subfilter setup: along atTop ⊓ {goodHeight}, f(T) → Rfull.
  -- This uses h_horiz (horizontal vanishing) + h_res_tendsto (residue sum).
  set Sfilter : Filter ℝ := atTop ⊓ Filter.principal {T : ℝ | goodHeight T}
    with hSfilter_def
  haveI h_neBot : Sfilter.NeBot := by
    rw [hSfilter_def, ← Filter.frequently_iff_neBot, Filter.frequently_atTop]
    intro a
    obtain ⟨T, hT_ge, hT_good⟩ := exists_goodHeight_strong_ge a
    exact ⟨T, hT_ge, hT_good⟩
  -- f(T) → Rfull along Sfilter.
  have h_f_subfilter : Tendsto f Sfilter (nhds Rfull) := by
    -- Express f(T) - Rfull = 2πi·(Stsum - ZsumT) - ΔbotT, both → 0.
    have h_diff_tendsto :
        Tendsto (fun T : ℝ => f T - Rfull) Sfilter (nhds 0) := by
      have h_horiz_tendsto : Tendsto ΔbotT Sfilter (nhds 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        rw [hSfilter_def, Filter.eventually_inf_principal]
        obtain ⟨T_h, hT_h_pos, hT_h⟩ := h_horiz ε hε
        filter_upwards [Filter.eventually_ge_atTop T_h] with T hT_ge hGood
        rw [dist_zero_right]
        exact hT_h T hT_ge hGood
      have h_res_tendsto' : Tendsto (fun T => Stsum - ZsumT T) Sfilter (nhds 0) := by
        have : Tendsto ZsumT Sfilter (nhds Stsum) := by
          simp only [hZsumT_def, hStsum_def]; exact h_res_tendsto
        simpa using (tendsto_const_nhds (x := Stsum) (f := Sfilter)).sub this
      have h_eq_eventually : ∀ᶠ T in Sfilter,
          (2 * ((Real.pi : ℝ) : ℂ) * I * (Stsum - ZsumT T) - ΔbotT T) =
          (f T - Rfull) := by
        rw [hSfilter_def]
        rw [Filter.eventually_inf_principal]
        filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with T hT_gt hGood
        rw [h_f_eq T hT_gt hGood]
        ring
      apply Filter.Tendsto.congr' h_eq_eventually
      have h_2π_tendsto :
          Tendsto (fun T => 2 * ((Real.pi : ℝ) : ℂ) * I * (Stsum - ZsumT T))
              Sfilter (nhds 0) := by
        have := h_res_tendsto'.const_mul (2 * ((Real.pi : ℝ) : ℂ) * I)
        simpa using this
      simpa using h_2π_tendsto.sub h_horiz_tendsto
    have := h_diff_tendsto.add (tendsto_const_nhds (x := Rfull) (f := Sfilter))
    simpa using this
  -- f(T) → I•(Aplus - Aminus) along atTop ⊇ Sfilter.
  have h_f_subfilter_atTop : Tendsto f Sfilter (nhds (I • (Aplus - Aminus))) :=
    h_f_atTop.mono_left
      (inf_le_left : Sfilter ≤ atTop)
  -- Uniqueness of limits.
  have h_unique : I • (Aplus - Aminus) = Rfull :=
    tendsto_nhds_unique h_f_subfilter_atTop h_f_subfilter
  -- Cancel I.
  have h_target_mul : I * (2 * ((Real.pi : ℝ) : ℂ) * R) = Rfull := by
    rw [hRfull_def]; ring
  have h_IL_eq : I * (Aplus - Aminus) = Rfull := by
    have h := h_unique
    simp only [smul_eq_mul] at h
    exact h
  exact mul_left_cancel₀ Complex.I_ne_zero (h_IL_eq.trans h_target_mul.symm)

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.rectContourIntegral_K_pairTestMellin_T_limit
