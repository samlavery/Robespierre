import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleResidueSum
import RequestProject.WeilRectangleViaSubtraction
import RequestProject.WeilPairTestMellinExtend
import RequestProject.FarZeroShellBound

/-!
# Per-zero residue identification at `s = 1 − ρ`

For each nontrivial zero `ρ` of ζ, the function

```
f(s) := pairTestMellin β s / (s − (1 − ρ))
```

has a simple pole at `s = 1 − ρ` with residue `pairTestMellin β (1 − ρ)`,
and is otherwise holomorphic on the rectangle `[σL, σR] × [−T, T]`
provided `1 − ρ` is interior.

This file proves the **finite-rectangle residue identity** for that
integrand, unconditionally:

```
rectContourIntegral σL σR T (fun s => pairTestMellin β s / (s − (1 − ρ)))
  = 2 π i · pairTestMellin β (1 − ρ).
```

This is the per-zero ingredient feeding into the explicit-formula
contour analysis: combined with the σ = 2 right-edge `dt`-parametrisation
`s = 2 + i t`, `ds = i dt`, this captures the residue identification

```
∫_t (1 / ((1 − (2 + i t)) − ρ)) · pairTestMellin β (2 + i t) dt
  = − 2 π · pairTestMellin β (1 − ρ) − (left/top/bottom edge contributions).
```

## Main results

* `pairTestMellin_div_diff_decomposition` — Hermite split at `c`:
  `pairTestMellin β s / (s − c) = pairTestMellin β c / (s − c) + dslope … s`.
* `dslope_pairTestMellin_differentiableAt` — `dslope (pairTestMellin β) c`
  is differentiable at every `s` with `−4 < s.re` (provided `−4 < c.re`).
* `rectContourIntegral_pairTestMellin_div_eq_residue` — the closed-form
  finite-rectangle identity for any `c` interior to the rectangle with
  `−4 < c.re`.
* `perZero_finite_rect_residue_at_one_sub_rho` — specialisation to
  `c := 1 − ρ` for `ρ ∈ NontrivialZeros`.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-! ## §1. Hermite decomposition via `dslope` -/

/-- **Pointwise Hermite decomposition.** Off the singular point,
`pairTestMellin β s / (s − c) = pairTestMellin β c / (s − c) + dslope … s`. -/
theorem pairTestMellin_div_diff_decomposition
    (β : ℝ) (c s : ℂ) (hsc : s ≠ c) :
    pairTestMellin β s / (s - c) =
      pairTestMellin β c / (s - c) +
      dslope (pairTestMellin β) c s := by
  have hne : s - c ≠ 0 := sub_ne_zero.mpr hsc
  have h_sub : (s - c) * dslope (pairTestMellin β) c s =
      pairTestMellin β s - pairTestMellin β c :=
    sub_smul_dslope (pairTestMellin β) c s
  -- Divide both sides by (s - c) to express dslope as a divided difference.
  have h_div :
      dslope (pairTestMellin β) c s =
        (pairTestMellin β s - pairTestMellin β c) / (s - c) := by
    rw [eq_div_iff hne, mul_comm]
    exact h_sub
  rw [h_div]
  field_simp
  ring

/-- **Analyticity of `dslope (pairTestMellin β) c` at every point of the
half-plane `Re s > −4`** (assuming `Re c > −4`).

For `s ≠ c`, follow from `differentiableAt_dslope_of_ne` and pairTestMellin's
differentiability. At `s = c`, follow from `has_fpower_series_dslope_fslope`
applied to a power series of `pairTestMellin β` at `c`. -/
theorem dslope_pairTestMellin_differentiableAt
    (β : ℝ) {c : ℂ} (hc : -4 < c.re) {s : ℂ} (hs : -4 < s.re) :
    DifferentiableAt ℂ (dslope (pairTestMellin β) c) s := by
  by_cases hsc : s = c
  · -- s = c: use power series construction.
    subst hsc
    -- `pairTestMellin β` is analytic at s (since differentiable on open set
    -- {z | -4 < z.re}, hence analytic on it).
    have hopen : IsOpen ({z : ℂ | -4 < z.re}) :=
      (isOpen_Ioi).preimage Complex.continuous_re
    have hpt_diff_on : DifferentiableOn ℂ (pairTestMellin β)
        ({z : ℂ | -4 < z.re}) := fun z hz =>
      (pairTestMellin_differentiableAt_re_gt_neg_four β hz).differentiableWithinAt
    have hpt_an : AnalyticOnNhd ℂ (pairTestMellin β)
        ({z : ℂ | -4 < z.re}) := hpt_diff_on.analyticOnNhd hopen
    have hpt_an_at : AnalyticAt ℂ (pairTestMellin β) s := hpt_an s hs
    -- Extract a power series.
    obtain ⟨p, hp⟩ := hpt_an_at
    -- dslope has the fslope power series at s.
    have hfp_dslope : HasFPowerSeriesAt (dslope (pairTestMellin β) s) p.fslope s :=
      HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp
    exact hfp_dslope.analyticAt.differentiableAt
  · -- s ≠ c: dslope's differentiability ↔ f's differentiability.
    have h_iff := differentiableAt_dslope_of_ne (f := pairTestMellin β) (a := c) (b := s) hsc
    exact h_iff.mpr (pairTestMellin_differentiableAt_re_gt_neg_four β hs)

/-- **Differentiability of `dslope (pairTestMellin β) c` on the rectangle.**
Provided both vertical edges `σL` and `σR` are strictly to the right of `-4`. -/
theorem dslope_pairTestMellin_differentiableOn_rect
    (β : ℝ) {c : ℂ} (hc : -4 < c.re)
    {σL σR T : ℝ} (hσL : -4 < σL) (hσR : -4 < σR) :
    DifferentiableOn ℂ (dslope (pairTestMellin β) c)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
  intro z hz
  have hz_re_mem : z.re ∈ Set.uIcc σL σR := by
    rcases hz with ⟨hzre, _⟩
    exact hzre
  have hmin_neg4 : -4 < min σL σR := lt_min hσL hσR
  -- Set.uIcc σL σR = Icc (min σL σR) (max σL σR), so min σL σR ≤ z.re.
  have hz_re_ge : min σL σR ≤ z.re := by
    have := hz_re_mem
    rw [Set.uIcc, Set.mem_Icc] at this
    exact this.1
  have hz_re_neg4 : -4 < z.re := lt_of_lt_of_le hmin_neg4 hz_re_ge
  exact (dslope_pairTestMellin_differentiableAt β hc hz_re_neg4).differentiableWithinAt

/-! ## §1b. Interval-integrability of the integrands on each rectangle edge -/

/-- The pole-removed integrand `pairTestMellin β z / (z − c)` is continuous on
the rectangle minus `{c}`. We will use this together with the fact that `c` is
strictly interior to the rectangle (hence absent from each *edge*) to conclude
interval-integrability on each edge. -/
private theorem pairTestMellin_div_edge_continuousOn
    (β : ℝ) (c : ℂ) {σL σR T : ℝ}
    (hσL : -4 < σL) (hσR : -4 < σR) :
    ContinuousOn (fun z : ℂ => pairTestMellin β z / (z - c))
      ((Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({c} : Set ℂ)) := by
  have hopen_re : IsOpen ({z : ℂ | -4 < z.re}) :=
    (isOpen_Ioi).preimage Complex.continuous_re
  have h_pt_diff : DifferentiableOn ℂ (pairTestMellin β) ({z : ℂ | -4 < z.re}) :=
    fun z hz =>
      (pairTestMellin_differentiableAt_re_gt_neg_four β hz).differentiableWithinAt
  -- pairTestMellin β is continuous on the rectangle (subset of {-4 < re}).
  have hsub : (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({c} : Set ℂ) ⊆
      ({z : ℂ | -4 < z.re}) := by
    intro z hz
    have hz_mem := hz.1
    have hz_re_mem : z.re ∈ Set.uIcc σL σR := by
      rcases hz_mem with ⟨hzre, _⟩
      exact hzre
    have hmin_neg4 : -4 < min σL σR := lt_min hσL hσR
    have hz_re_ge : min σL σR ≤ z.re := by
      rw [Set.uIcc, Set.mem_Icc] at hz_re_mem
      exact hz_re_mem.1
    exact lt_of_lt_of_le hmin_neg4 hz_re_ge
  have h_num_cont : ContinuousOn (pairTestMellin β)
      ((Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({c} : Set ℂ)) := by
    intro z hz
    exact ((h_pt_diff z (hsub hz)).continuousWithinAt).mono hsub
  have h_den_cont : ContinuousOn (fun z : ℂ => z - c)
      ((Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({c} : Set ℂ)) :=
    Continuous.continuousOn (by fun_prop)
  refine h_num_cont.div h_den_cont ?_
  intro z hz hzero
  have hzc : z ≠ c := by
    have : z ∉ ({c} : Set ℂ) := hz.2
    simpa using this
  exact hzc (sub_eq_zero.mp hzero)

private theorem dslope_pairTestMellin_continuousOn_rect
    (β : ℝ) {c : ℂ} (hc : -4 < c.re)
    {σL σR T : ℝ} (hσL : -4 < σL) (hσR : -4 < σR) :
    ContinuousOn (dslope (pairTestMellin β) c)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
  (dslope_pairTestMellin_differentiableOn_rect β hc hσL hσR).continuousOn

/-- pairTestMellin is continuous at every point with `Re > -4`. -/
private theorem pairTestMellin_continuous_re_gt_neg_four
    (β : ℝ) {z : ℂ} (hz : -4 < z.re) :
    ContinuousAt (pairTestMellin β) z :=
  (pairTestMellin_differentiableAt_re_gt_neg_four β hz).continuousAt

/-- Bottom-edge interval-integrability of `pairTestMellin β z / (z − c)`. -/
private theorem pairTestMellin_div_bottom_edge_intervalIntegrable
    (β : ℝ) (c : ℂ) {σL σR T : ℝ}
    (hσL : -4 < σL) (hσR : -4 < σR) (hc_im : -T < c.im) :
    IntervalIntegrable
      (fun x : ℝ => pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
          (((x : ℂ) + (-T : ℝ) * I) - c))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · -- Numerator continuous via composition.
    refine ContinuousOn.comp (s := Set.uIcc σL σR)
      (t := ({z : ℂ | -4 < z.re})) ?_ (by fun_prop) ?_
    · intro z hz
      exact (pairTestMellin_continuous_re_gt_neg_four β hz).continuousWithinAt
    · intro x hx
      have hx_re : x ∈ Set.uIcc σL σR := hx
      have hmin_neg4 : -4 < min σL σR := lt_min hσL hσR
      have hx_ge : min σL σR ≤ x := by
        rw [Set.uIcc, Set.mem_Icc] at hx_re
        exact hx_re.1
      have : -4 < x := lt_of_lt_of_le hmin_neg4 hx_ge
      show -4 < ((x : ℂ) + (-T : ℝ) * I).re
      simpa
  · -- Denominator continuous: it's `z - c`.
    fun_prop
  · -- Denominator nonzero on the edge: c.im ≠ -T so the bottom-edge point ≠ c.
    intro x _ hx0
    have him : (((x : ℂ) + (-T : ℝ) * I - c).im : ℝ) = -T - c.im := by simp
    rw [hx0] at him
    simp at him
    linarith

/-- Top-edge interval-integrability of `pairTestMellin β z / (z − c)`. -/
private theorem pairTestMellin_div_top_edge_intervalIntegrable
    (β : ℝ) (c : ℂ) {σL σR T : ℝ}
    (hσL : -4 < σL) (hσR : -4 < σR) (hc_im : c.im < T) :
    IntervalIntegrable
      (fun x : ℝ => pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
          (((x : ℂ) + (T : ℝ) * I) - c))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · refine ContinuousOn.comp (s := Set.uIcc σL σR)
      (t := ({z : ℂ | -4 < z.re})) ?_ (by fun_prop) ?_
    · intro z hz
      exact (pairTestMellin_continuous_re_gt_neg_four β hz).continuousWithinAt
    · intro x hx
      have hx_re : x ∈ Set.uIcc σL σR := hx
      have hmin_neg4 : -4 < min σL σR := lt_min hσL hσR
      have hx_ge : min σL σR ≤ x := by
        rw [Set.uIcc, Set.mem_Icc] at hx_re
        exact hx_re.1
      have : -4 < x := lt_of_lt_of_le hmin_neg4 hx_ge
      show -4 < ((x : ℂ) + (T : ℝ) * I).re
      simpa
  · fun_prop
  · intro x _ hx0
    have him : (((x : ℂ) + (T : ℝ) * I - c).im : ℝ) = T - c.im := by simp
    rw [hx0] at him
    simp at him
    linarith

/-- Right-edge interval-integrability of `pairTestMellin β z / (z − c)`. -/
private theorem pairTestMellin_div_right_edge_intervalIntegrable
    (β : ℝ) (c : ℂ) {σR T : ℝ}
    (hσR : -4 < σR) (hc_re : c.re < σR) :
    IntervalIntegrable
      (fun y : ℝ => pairTestMellin β ((σR : ℂ) + (y : ℂ) * I) /
          (((σR : ℂ) + (y : ℂ) * I) - c))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · refine ContinuousOn.comp (s := Set.uIcc (-T) T)
      (t := ({z : ℂ | -4 < z.re})) ?_ (by fun_prop) ?_
    · intro z hz
      exact (pairTestMellin_continuous_re_gt_neg_four β hz).continuousWithinAt
    · intro y _hy
      show -4 < ((σR : ℂ) + (y : ℂ) * I).re
      simpa
  · fun_prop
  · intro y _ hy0
    have hre : (((σR : ℂ) + (y : ℂ) * I - c).re : ℝ) = σR - c.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

/-- Left-edge interval-integrability of `pairTestMellin β z / (z − c)`. -/
private theorem pairTestMellin_div_left_edge_intervalIntegrable
    (β : ℝ) (c : ℂ) {σL T : ℝ}
    (hσL : -4 < σL) (hc_re : σL < c.re) :
    IntervalIntegrable
      (fun y : ℝ => pairTestMellin β ((σL : ℂ) + (y : ℂ) * I) /
          (((σL : ℂ) + (y : ℂ) * I) - c))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · refine ContinuousOn.comp (s := Set.uIcc (-T) T)
      (t := ({z : ℂ | -4 < z.re})) ?_ (by fun_prop) ?_
    · intro z hz
      exact (pairTestMellin_continuous_re_gt_neg_four β hz).continuousWithinAt
    · intro y _hy
      show -4 < ((σL : ℂ) + (y : ℂ) * I).re
      simpa
  · fun_prop
  · intro y _ hy0
    have hre : (((σL : ℂ) + (y : ℂ) * I - c).re : ℝ) = σL - c.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

/-! ## §1c. Integral linearity discharge -/

/-- **Integral-linearity discharge.** For `c` strictly interior to the
rectangle with `Re c > −4` and both vertical edges past `−4`, the rectangle
contour integral splits

```
∮ pairTestMellin β z / (z − c) = ∮ pairTestMellin β c / (z − c) + ∮ dslope … c.
```
-/
private theorem rectContourIntegral_pairTestMellin_div_split
    (β : ℝ) (c : ℂ)
    {σL σR T : ℝ}
    (hσL : -4 < σL) (hσR : -4 < σR)
    (hc_re : σL < c.re ∧ c.re < σR) (hc_im : -T < c.im ∧ c.im < T) :
    rectContourIntegral σL σR T
        (fun z => pairTestMellin β z / (z - c)) =
      rectContourIntegral σL σR T (fun z => pairTestMellin β c / (z - c)) +
        rectContourIntegral σL σR T (dslope (pairTestMellin β) c) := by
  have hc_re_neg4 : -4 < c.re := lt_trans hσL hc_re.1
  -- First, rewrite the LHS using the pointwise decomposition (off the pole).
  -- Each rectangle edge is a closed segment that does NOT contain `c` (since c
  -- is strictly interior). So pointwise equality holds on each edge.
  have h_decomp_edge :
      ∀ (z : ℂ), z ≠ c →
        pairTestMellin β z / (z - c) =
          pairTestMellin β c / (z - c) + dslope (pairTestMellin β) c z :=
    fun z hzc => pairTestMellin_div_diff_decomposition β c z hzc
  -- Build per-edge equalities, then apply via `unfold` + congrArg.
  have h_bot : ∀ x ∈ Set.uIcc σL σR,
      pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
          (((x : ℂ) + (-T : ℝ) * I) - c) =
        pairTestMellin β c / (((x : ℂ) + (-T : ℝ) * I) - c) +
          dslope (pairTestMellin β) c ((x : ℂ) + (-T : ℝ) * I) := by
    intro x _
    apply h_decomp_edge
    intro heq
    have him : c.im = -T := by
      have := congrArg Complex.im heq; simpa using this.symm
    linarith [hc_im.1]
  have h_top : ∀ x ∈ Set.uIcc σL σR,
      pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
          (((x : ℂ) + (T : ℝ) * I) - c) =
        pairTestMellin β c / (((x : ℂ) + (T : ℝ) * I) - c) +
          dslope (pairTestMellin β) c ((x : ℂ) + (T : ℝ) * I) := by
    intro x _
    apply h_decomp_edge
    intro heq
    have him : c.im = T := by
      have := congrArg Complex.im heq; simpa using this.symm
    linarith [hc_im.2]
  have h_right : ∀ y ∈ Set.uIcc (-T) T,
      pairTestMellin β ((σR : ℂ) + (y : ℂ) * I) /
          (((σR : ℂ) + (y : ℂ) * I) - c) =
        pairTestMellin β c / (((σR : ℂ) + (y : ℂ) * I) - c) +
          dslope (pairTestMellin β) c ((σR : ℂ) + (y : ℂ) * I) := by
    intro y _
    apply h_decomp_edge
    intro heq
    have hre : c.re = σR := by
      have := congrArg Complex.re heq; simpa using this.symm
    linarith [hc_re.2]
  have h_left : ∀ y ∈ Set.uIcc (-T) T,
      pairTestMellin β ((σL : ℂ) + (y : ℂ) * I) /
          (((σL : ℂ) + (y : ℂ) * I) - c) =
        pairTestMellin β c / (((σL : ℂ) + (y : ℂ) * I) - c) +
          dslope (pairTestMellin β) c ((σL : ℂ) + (y : ℂ) * I) := by
    intro y _
    apply h_decomp_edge
    intro heq
    have hre : c.re = σL := by
      have := congrArg Complex.re heq; simpa using this.symm
    linarith [hc_re.1]
  have h_lhs_eq :
      rectContourIntegral σL σR T
          (fun z => pairTestMellin β z / (z - c)) =
        rectContourIntegral σL σR T
          (fun z => pairTestMellin β c / (z - c) +
              dslope (pairTestMellin β) c z) := by
    unfold rectContourIntegral
    have hb_int := intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (a := σL) (b := σR)
      (f := fun x : ℝ => pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
          (((x : ℂ) + (-T : ℝ) * I) - c))
      (g := fun x : ℝ => pairTestMellin β c / (((x : ℂ) + (-T : ℝ) * I) - c) +
          dslope (pairTestMellin β) c ((x : ℂ) + (-T : ℝ) * I))
      h_bot
    have ht_int := intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (a := σL) (b := σR)
      (f := fun x : ℝ => pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
          (((x : ℂ) + (T : ℝ) * I) - c))
      (g := fun x : ℝ => pairTestMellin β c / (((x : ℂ) + (T : ℝ) * I) - c) +
          dslope (pairTestMellin β) c ((x : ℂ) + (T : ℝ) * I))
      h_top
    have hr_int := intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (a := -T) (b := T)
      (f := fun y : ℝ => pairTestMellin β ((σR : ℂ) + (y : ℂ) * I) /
          (((σR : ℂ) + (y : ℂ) * I) - c))
      (g := fun y : ℝ => pairTestMellin β c / (((σR : ℂ) + (y : ℂ) * I) - c) +
          dslope (pairTestMellin β) c ((σR : ℂ) + (y : ℂ) * I))
      h_right
    have hl_int := intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (a := -T) (b := T)
      (f := fun y : ℝ => pairTestMellin β ((σL : ℂ) + (y : ℂ) * I) /
          (((σL : ℂ) + (y : ℂ) * I) - c))
      (g := fun y : ℝ => pairTestMellin β c / (((σL : ℂ) + (y : ℂ) * I) - c) +
          dslope (pairTestMellin β) c ((σL : ℂ) + (y : ℂ) * I))
      h_left
    rw [hb_int, ht_int, hr_int, hl_int]
  rw [h_lhs_eq]
  -- Now apply rectContourIntegral_add. Need integrability of both summands
  -- on each edge.
  have hT_pos : 0 < T := by linarith [hc_im.1, hc_im.2]
  -- Helper: continuity of dslope on the rectangle.
  have hg_cont : ContinuousOn (dslope (pairTestMellin β) c)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    dslope_pairTestMellin_continuousOn_rect β hc_re_neg4 hσL hσR
  -- Edge integrability of `dslope`.
  have hg_b : IntervalIntegrable
      (fun x : ℝ => dslope (pairTestMellin β) c ((x : ℂ) + (-T : ℝ) * I))
      MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.comp (s := Set.uIcc σL σR) (t := Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)
      hg_cont (by fun_prop) ?_
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simp
  have hg_t : IntervalIntegrable
      (fun x : ℝ => dslope (pairTestMellin β) c ((x : ℂ) + (T : ℝ) * I))
      MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.comp (s := Set.uIcc σL σR) (t := Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)
      hg_cont (by fun_prop) ?_
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simp
  have hg_r : IntervalIntegrable
      (fun y : ℝ => dslope (pairTestMellin β) c ((σR : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.comp (s := Set.uIcc (-T) T) (t := Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)
      hg_cont (by fun_prop) ?_
    intro y hy
    refine ⟨?_, ?_⟩
    · simp
    · simpa using hy
  have hg_l : IntervalIntegrable
      (fun y : ℝ => dslope (pairTestMellin β) c ((σL : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.comp (s := Set.uIcc (-T) T) (t := Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)
      hg_cont (by fun_prop) ?_
    intro y hy
    refine ⟨?_, ?_⟩
    · simp
    · simpa using hy
  -- Edge integrability of `r/(z-c)` (constant residue / linear pole).
  have hr_b : IntervalIntegrable
      (fun x : ℝ => pairTestMellin β c / ((x : ℂ) + (-T : ℝ) * I - c))
      MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x _ hx0
      have him : (((x : ℂ) + (-T : ℝ) * I - c).im : ℝ) = -T - c.im := by simp
      rw [hx0] at him; simp at him; linarith [hc_im.1]
  have hr_t : IntervalIntegrable
      (fun x : ℝ => pairTestMellin β c / ((x : ℂ) + (T : ℝ) * I - c))
      MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x _ hx0
      have him : (((x : ℂ) + (T : ℝ) * I - c).im : ℝ) = T - c.im := by simp
      rw [hx0] at him; simp at him; linarith [hc_im.2]
  have hr_r : IntervalIntegrable
      (fun y : ℝ => pairTestMellin β c / ((σR : ℂ) + (y : ℂ) * I - c))
      MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y _ hy0
      have hre : (((σR : ℂ) + (y : ℂ) * I - c).re : ℝ) = σR - c.re := by simp
      rw [hy0] at hre; simp at hre; linarith [hc_re.2]
  have hr_l : IntervalIntegrable
      (fun y : ℝ => pairTestMellin β c / ((σL : ℂ) + (y : ℂ) * I - c))
      MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro y _ hy0
      have hre : (((σL : ℂ) + (y : ℂ) * I - c).re : ℝ) = σL - c.re := by simp
      rw [hy0] at hre; simp at hre; linarith [hc_re.1]
  -- Apply additivity.
  exact rectContourIntegral_add σL σR T
    (fun z => pairTestMellin β c / (z - c))
    (dslope (pairTestMellin β) c)
    hr_b hg_b hr_t hg_t hr_r hg_r hr_l hg_l

/-! ## §2. The closed-form finite-rectangle identity -/

/-- **Finite-rectangle residue identity for `pairTestMellin β · (s − c)⁻¹`.**

Given a point `c` interior to the rectangle `[σL, σR] × [−T, T]`
and `Re c > −4`, the rectangle contour integral of
`s ↦ pairTestMellin β s / (s − c)` equals `2 π i · pairTestMellin β c`.

The hypothesis `h_integral_eq` packages the integral linearity
(`∮(r/(z − c) + g) = ∮(r/(z − c)) + ∮g`); the caller proves it by
discharging interval-integrability of each summand on each rectangle
edge. -/
theorem rectContourIntegral_pairTestMellin_div_eq_residue
    (β : ℝ) (c : ℂ)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (hσL : -4 < σL) (hσR : -4 < σR)
    (hc_re : σL < c.re ∧ c.re < σR) (hc_im : -T < c.im ∧ c.im < T)
    (h_integral_eq :
      rectContourIntegral σL σR T
          (fun z => pairTestMellin β z / (z - c)) =
        rectContourIntegral σL σR T (fun z => pairTestMellin β c / (z - c)) +
          rectContourIntegral σL σR T (dslope (pairTestMellin β) c)) :
    rectContourIntegral σL σR T (fun z => pairTestMellin β z / (z - c)) =
      2 * (Real.pi : ℂ) * I * pairTestMellin β c := by
  have hc_re_neg4 : -4 < c.re := lt_trans hσL hc_re.1
  have hg_diff :
      DifferentiableOn ℂ (dslope (pairTestMellin β) c)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    dslope_pairTestMellin_differentiableOn_rect β hc_re_neg4 hσL hσR
  have h_decomp :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({c} : Set ℂ),
        (fun z => pairTestMellin β z / (z - c)) z =
          pairTestMellin β c / (z - c) +
            dslope (pairTestMellin β) c z := by
    intro z hz
    have hzc : z ≠ c := by
      have : z ∉ ({c} : Set ℂ) := hz.2
      simpa using this
    exact pairTestMellin_div_diff_decomposition β c z hzc
  exact rectResidueTheorem_via_subtraction_unconditional hσ hT
    (fun z => pairTestMellin β z / (z - c))
    (dslope (pairTestMellin β) c)
    c (pairTestMellin β c)
    hc_re hc_im hg_diff h_decomp h_integral_eq

/-- **UNCONDITIONAL finite-rectangle residue identity.**
The integral-linearity hypothesis is discharged via
`rectContourIntegral_pairTestMellin_div_split`. -/
theorem rectContourIntegral_pairTestMellin_div_eq_residue_unconditional
    (β : ℝ) (c : ℂ)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (hσL : -4 < σL) (hσR : -4 < σR)
    (hc_re : σL < c.re ∧ c.re < σR) (hc_im : -T < c.im ∧ c.im < T) :
    rectContourIntegral σL σR T (fun z => pairTestMellin β z / (z - c)) =
      2 * (Real.pi : ℂ) * I * pairTestMellin β c :=
  rectContourIntegral_pairTestMellin_div_eq_residue β c hσ hT hσL hσR hc_re hc_im
    (rectContourIntegral_pairTestMellin_div_split β c hσL hσR hc_re hc_im)

/-! ## §3. Specialisation to `c := 1 − ρ` for `ρ` a nontrivial zeta zero -/

/-- **Per-zero finite-rectangle residue at `1 − ρ`.**

For every nontrivial zero `ρ` (`0 < Re ρ < 1`), the reflected point
`1 − ρ` lies in `(0, 1) ⊂ (−4, ∞)`, hence interior to the standard
rectangle `[−1, 2] × [−T, T]` for any `T > |Im ρ|`. -/
theorem perZero_finite_rect_residue_at_one_sub_rho
    (β : ℝ) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    {T : ℝ} (hT_im : |ρ.im| < T)
    (h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => pairTestMellin β z / (z - (1 - ρ))) =
        rectContourIntegral (-1 : ℝ) 2 T
            (fun z => pairTestMellin β (1 - ρ) / (z - (1 - ρ))) +
          rectContourIntegral (-1 : ℝ) 2 T
            (dslope (pairTestMellin β) (1 - ρ))) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun z => pairTestMellin β z / (z - (1 - ρ))) =
      2 * (Real.pi : ℂ) * I * pairTestMellin β (1 - ρ) := by
  obtain ⟨hρ_re_pos, hρ_re_lt_one, _hρ_zero⟩ := hρ
  have h1mρ_re_pos : 0 < (1 - ρ).re := by
    have h_re : (1 - ρ).re = 1 - ρ.re := by simp
    rw [h_re]; linarith
  have h1mρ_re_lt_one : (1 - ρ).re < 1 := by
    have h_re : (1 - ρ).re = 1 - ρ.re := by simp
    rw [h_re]; linarith
  have hT_pos : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg _) hT_im
  have hc_re : (-1 : ℝ) < (1 - ρ).re ∧ (1 - ρ).re < (2 : ℝ) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hc_im : (-T : ℝ) < (1 - ρ).im ∧ (1 - ρ).im < T := by
    have h_im : (1 - ρ).im = -ρ.im := by simp
    rw [h_im]
    have h_abs := abs_lt.mp hT_im
    refine ⟨?_, ?_⟩ <;> linarith
  exact rectContourIntegral_pairTestMellin_div_eq_residue β (1 - ρ)
    (by norm_num : (-1 : ℝ) < 2) hT_pos
    (by norm_num : (-4 : ℝ) < (-1 : ℝ)) (by norm_num : (-4 : ℝ) < (2 : ℝ))
    hc_re hc_im h_integral_eq

/-- **UNCONDITIONAL per-zero finite-rectangle residue at `1 − ρ`.** -/
theorem perZero_finite_rect_residue_at_one_sub_rho_unconditional
    (β : ℝ) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    {T : ℝ} (hT_im : |ρ.im| < T) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun z => pairTestMellin β z / (z - (1 - ρ))) =
      2 * (Real.pi : ℂ) * I * pairTestMellin β (1 - ρ) := by
  obtain ⟨hρ_re_pos, hρ_re_lt_one, _hρ_zero⟩ := hρ
  have h1mρ_re_pos : 0 < (1 - ρ).re := by
    have h_re : (1 - ρ).re = 1 - ρ.re := by simp
    rw [h_re]; linarith
  have h1mρ_re_lt_one : (1 - ρ).re < 1 := by
    have h_re : (1 - ρ).re = 1 - ρ.re := by simp
    rw [h_re]; linarith
  have hT_pos : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg _) hT_im
  have hc_re : (-1 : ℝ) < (1 - ρ).re ∧ (1 - ρ).re < (2 : ℝ) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hc_im : (-T : ℝ) < (1 - ρ).im ∧ (1 - ρ).im < T := by
    have h_im : (1 - ρ).im = -ρ.im := by simp
    rw [h_im]
    have h_abs := abs_lt.mp hT_im
    refine ⟨?_, ?_⟩ <;> linarith
  exact rectContourIntegral_pairTestMellin_div_eq_residue_unconditional
    β (1 - ρ)
    (by norm_num : (-1 : ℝ) < 2) hT_pos
    (by norm_num : (-4 : ℝ) < (-1 : ℝ)) (by norm_num : (-4 : ℝ) < (2 : ℝ))
    hc_re hc_im

/-! ## §4. Reformulation in terms of the σ = 2 right-edge `dt`-integral -/

/-- **Algebraic identity at the σ = 2 line.** For the user's target integrand,
`(1 / ((−1 − it) − ρ)) · pairTestMellin β (2 + it)`, we have

```
(1 / ((−1 − it) − ρ)) · pairTestMellin β (2 + it)
  = − pairTestMellin β (2 + it) / ((2 + it) − (1 − ρ))
```

since `−1 − it = 1 − (2 + it)` ⇒ `(−1 − it) − ρ = −((2 + it) − (1 − ρ))`. -/
theorem perZero_integrand_eq_neg_div
    (β : ℝ) (ρ : ℂ) (t : ℝ) :
    (1 / ((-1 - (t : ℂ) * I) - ρ)) * pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) =
      - (pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) /
          (((2 : ℂ) + (t : ℂ) * I) - (1 - ρ))) := by
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have h1 : (-1 - (t : ℂ) * I) = 1 - s := by simp [s]; ring
  have h2 : (-1 - (t : ℂ) * I) - ρ = -(s - (1 - ρ)) := by
    rw [h1]; ring
  rw [h2]
  by_cases hsd : s - (1 - ρ) = 0
  · rw [hsd]
    simp
  · have hne : -(s - (1 - ρ)) ≠ 0 := neg_ne_zero.mpr hsd
    field_simp

/-- **Right-edge integral identification.** The right edge of the rectangle
contour at `σR = 2`,

```
I • ∫_{-T}^{T} pairTestMellin β (2 + iy) / ((2 + iy) − (1 − ρ)) dy
```

is one of the four signed pieces of `rectContourIntegral (-1) 2 T (…)`.

After the σ = 2 right-edge `dt`-parametrisation `s = 2 + it, ds = i · dt`,
the user's target integral

```
J(T) := ∫_{-T}^{T} (1 / ((−1 − it) − ρ)) · pairTestMellin β (2 + it) dt
```

equals `-∫_{-T}^{T} pairTestMellin β (2 + iy) / ((2 + iy) − (1 − ρ)) dy`,
and hence

```
I • J(T) = − (right-edge contribution to rectContourIntegral).
```
-/
theorem perZero_truncated_t_integral_eq_neg_right_edge
    (β : ℝ) (ρ : ℂ) (T : ℝ) :
    (∫ t : ℝ in (-T : ℝ)..T,
        (1 / ((-1 - (t : ℂ) * I) - ρ)) *
          pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      -(∫ y : ℝ in (-T : ℝ)..T,
          pairTestMellin β ((2 : ℂ) + (y : ℂ) * I) /
            (((2 : ℂ) + (y : ℂ) * I) - (1 - ρ))) := by
  -- Pointwise rewrite via `perZero_integrand_eq_neg_div`, then negate the integral.
  have hpt : ∀ t : ℝ,
      (1 / ((-1 - (t : ℂ) * I) - ρ)) *
        pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) =
      -(pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) /
          (((2 : ℂ) + (t : ℂ) * I) - (1 - ρ))) := by
    intro t
    exact perZero_integrand_eq_neg_div β ρ t
  calc (∫ t : ℝ in (-T : ℝ)..T,
        (1 / ((-1 - (t : ℂ) * I) - ρ)) *
          pairTestMellin β ((2 : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ in (-T : ℝ)..T,
          -(pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) /
              (((2 : ℂ) + (t : ℂ) * I) - (1 - ρ))) := by
            apply intervalIntegral.integral_congr
            intro t _; exact hpt t
    _ = -(∫ y : ℝ in (-T : ℝ)..T,
            pairTestMellin β ((2 : ℂ) + (y : ℂ) * I) /
              (((2 : ℂ) + (y : ℂ) * I) - (1 - ρ))) := by
            rw [intervalIntegral.integral_neg]

/-- **Truncated per-zero `dt`-residue identity.**

Combining `perZero_finite_rect_residue_at_one_sub_rho` (the rectangle
identity) with `perZero_truncated_t_integral_eq_neg_right_edge` (the
algebraic right-edge identification) yields a closed-form expression
for `J(T)` modulo the *other three* edge contributions
(bottom, top, and left edges of the rectangle):

```
I · J(T) = 2 π i · pairTestMellin β (1 − ρ)
            − (bottom − top + I · left-edge integral).
```

Equivalently:

```
J(T) = − 2 π · pairTestMellin β (1 − ρ)
        + I · (bottom − top + I · left-edge integral).
```

The `T → ∞` limit form of the user's target follows once one shows the
right-hand-side bracket tends to zero — that is the `horizontalEdge` /
`leftEdge` decay step, available for `weilIntegrand · pairTestMellin`
in `WeilIdentityAtPairTest.lean` and adaptable here using
`pairTestMellin_decay_on_strip_neg` together with the `1/(s − c)` factor
which is bounded on the rectangle minus an ε-disk around `c`. -/
theorem perZero_truncated_t_integral_residue_form
    (β : ℝ) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    {T : ℝ} (hT_im : |ρ.im| < T)
    (h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => pairTestMellin β z / (z - (1 - ρ))) =
        rectContourIntegral (-1 : ℝ) 2 T
            (fun z => pairTestMellin β (1 - ρ) / (z - (1 - ρ))) +
          rectContourIntegral (-1 : ℝ) 2 T
            (dslope (pairTestMellin β) (1 - ρ))) :
    I * (∫ t : ℝ in (-T : ℝ)..T,
          (1 / ((-1 - (t : ℂ) * I) - ρ)) *
            pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      ((∫ x : ℝ in (-1 : ℝ)..2,
            pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
              (((x : ℂ) + (-T : ℝ) * I) - (1 - ρ))) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
              (((x : ℂ) + (T : ℝ) * I) - (1 - ρ)))) -
        I * (∫ y : ℝ in (-T : ℝ)..T,
            pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) /
              ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) - (1 - ρ))) -
        2 * (Real.pi : ℂ) * I * pairTestMellin β (1 - ρ) := by
  -- Get the rectangle identity.
  have h_rect := perZero_finite_rect_residue_at_one_sub_rho
    (β := β) (ρ := ρ) hρ hT_im h_integral_eq
  -- Get the right-edge ↔ J(T) algebraic identity.
  have h_alg := perZero_truncated_t_integral_eq_neg_right_edge β ρ T
  -- Unfold the rectangle integral on the LHS of h_rect.
  have h_unfold :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => pairTestMellin β z / (z - (1 - ρ))) =
        ((∫ x : ℝ in (-1 : ℝ)..2,
              pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
                (((x : ℂ) + (-T : ℝ) * I) - (1 - ρ))) -
          (∫ x : ℝ in (-1 : ℝ)..2,
              pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
                (((x : ℂ) + (T : ℝ) * I) - (1 - ρ)))) +
        I • (∫ y : ℝ in (-T : ℝ)..T,
              pairTestMellin β (((2 : ℝ) : ℂ) + (y : ℂ) * I) /
                ((((2 : ℝ) : ℂ) + (y : ℂ) * I) - (1 - ρ))) -
        I • (∫ y : ℝ in (-T : ℝ)..T,
              pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) /
                ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) - (1 - ρ))) := by
    unfold rectContourIntegral
    rfl
  -- Multiply h_alg by I to get I·J(T) = -I · (right edge integral).
  have h_alg_I : I * (∫ t : ℝ in (-T : ℝ)..T,
        (1 / ((-1 - (t : ℂ) * I) - ρ)) *
          pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      -(I * (∫ y : ℝ in (-T : ℝ)..T,
          pairTestMellin β ((2 : ℂ) + (y : ℂ) * I) /
            (((2 : ℂ) + (y : ℂ) * I) - (1 - ρ)))) := by
    rw [h_alg]; ring
  -- Now substitute h_unfold into h_rect; solve for the right-edge piece;
  -- then plug into h_alg_I.
  rw [h_unfold] at h_rect
  -- h_rect : ((∫bot - ∫top) + I•∫right) - I•∫left = 2πi·pairTestMellin(1-ρ)
  -- Solve: I•∫right = 2πi·pairTestMellin(1-ρ) - (∫bot - ∫top) + I•∫left
  -- Note `I • z = I * z` in ℂ.
  have h_smul_eq : ∀ z : ℂ, (I : ℂ) • z = I * z := fun z => rfl
  simp only [h_smul_eq] at h_rect
  -- Rearrange h_rect to isolate the right-edge term.
  -- The mismatches between `h_rect` and the goal are pure cast normalisations:
  -- `↑2 ↦ 2`, `↑(-1) ↦ -1`, `↑(-T) ↦ -↑T`. Apply `push_cast` to both sides.
  rw [h_alg_I]
  have h_pushed : _ := h_rect
  push_cast at h_pushed
  push_cast
  linear_combination -h_pushed

/-- **UNCONDITIONAL truncated per-zero `dt`-residue identity.**
The integral-linearity hypothesis is discharged automatically.

This is the key per-zero `dt`-form of the user's target identity, valid
at every truncation `T > |Im ρ|`. The closed-form `T → ∞` version of
the user's request

```
∫_t (1 / ((−1 − it) − ρ)) · pairTestMellin β (2 + it) dt
  = − 2 π · pairTestMellin β (1 − ρ)
```

is the limit of the right-hand side here (modulo `I` factor) as the
bottom, top, and left-edge integrals tend to zero — a step that
requires plugging in `pairTestMellin_decay_on_strip_neg` (top/bottom)
and an analogous decay/integrability fact on the left edge `σ = −1`.
The TRUNCATED form is the primary algebraic content. -/
theorem perZero_truncated_t_integral_residue_form_unconditional
    (β : ℝ) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    {T : ℝ} (hT_im : |ρ.im| < T) :
    I * (∫ t : ℝ in (-T : ℝ)..T,
          (1 / ((-1 - (t : ℂ) * I) - ρ)) *
            pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) =
      ((∫ x : ℝ in (-1 : ℝ)..2,
            pairTestMellin β ((x : ℂ) + (-T : ℝ) * I) /
              (((x : ℂ) + (-T : ℝ) * I) - (1 - ρ))) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            pairTestMellin β ((x : ℂ) + (T : ℝ) * I) /
              (((x : ℂ) + (T : ℝ) * I) - (1 - ρ)))) -
        I * (∫ y : ℝ in (-T : ℝ)..T,
            pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I) /
              ((((-1 : ℝ) : ℂ) + (y : ℂ) * I) - (1 - ρ))) -
        2 * (Real.pi : ℂ) * I * pairTestMellin β (1 - ρ) := by
  -- Discharge the integral linearity hypothesis automatically.
  have h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => pairTestMellin β z / (z - (1 - ρ))) =
        rectContourIntegral (-1 : ℝ) 2 T
            (fun z => pairTestMellin β (1 - ρ) / (z - (1 - ρ))) +
          rectContourIntegral (-1 : ℝ) 2 T
            (dslope (pairTestMellin β) (1 - ρ)) := by
    obtain ⟨hρ_re_pos, hρ_re_lt_one, _hρ_zero⟩ := hρ
    have hT_pos : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg _) hT_im
    have h1mρ_re_pos : 0 < (1 - ρ).re := by
      have h_re : (1 - ρ).re = 1 - ρ.re := by simp
      rw [h_re]; linarith
    have h1mρ_re_lt_one : (1 - ρ).re < 1 := by
      have h_re : (1 - ρ).re = 1 - ρ.re := by simp
      rw [h_re]; linarith
    have hc_re : (-1 : ℝ) < (1 - ρ).re ∧ (1 - ρ).re < (2 : ℝ) := by
      refine ⟨?_, ?_⟩ <;> linarith
    have hc_im : (-T : ℝ) < (1 - ρ).im ∧ (1 - ρ).im < T := by
      have h_im : (1 - ρ).im = -ρ.im := by simp
      rw [h_im]
      have h_abs := abs_lt.mp hT_im
      refine ⟨?_, ?_⟩ <;> linarith
    exact rectContourIntegral_pairTestMellin_div_split β (1 - ρ)
      (by norm_num : (-4 : ℝ) < (-1 : ℝ)) (by norm_num : (-4 : ℝ) < (2 : ℝ))
      hc_re hc_im
  exact perZero_truncated_t_integral_residue_form β hρ hT_im h_integral_eq

#print axioms pairTestMellin_div_diff_decomposition
#print axioms dslope_pairTestMellin_differentiableAt
#print axioms dslope_pairTestMellin_differentiableOn_rect
#print axioms rectContourIntegral_pairTestMellin_div_eq_residue
#print axioms rectContourIntegral_pairTestMellin_div_eq_residue_unconditional
#print axioms perZero_finite_rect_residue_at_one_sub_rho
#print axioms perZero_finite_rect_residue_at_one_sub_rho_unconditional
#print axioms perZero_integrand_eq_neg_div
#print axioms perZero_truncated_t_integral_eq_neg_right_edge
#print axioms perZero_truncated_t_integral_residue_form
#print axioms perZero_truncated_t_integral_residue_form_unconditional

end Contour
end WeilPositivity
end ZD

end
