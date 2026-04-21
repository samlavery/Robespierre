import Mathlib
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilWindingIntegral

/-!
# WF-3: rectangle contour integral of the Weil integrand equals the residue sum

Assembles the WF-2 decomposition (`weilIntegrand = Σ(-h(ρ))/(s-ρ) + g` with `g`
analytic on the closed rectangle, valid off `Z`) with
`rectResidueTheorem_multi_pole_unconditional` to conclude:

```
rectContourIntegral σL σR T (weilIntegrand h) = 2πi · ∑ ρ ∈ Z, (−h(ρ))
```

for a critical-strip rectangle `σL ≤ σR < 1` whose finite zero `Finset` `Z`
contains every zero of `ζ` in the (closed) rectangle.

The residual integral-linearity hypothesis is passed through as a premise; it
is the standard distribution of `rectContourIntegral` over a finite sum plus an
analytic tail. Every other condition has been made unconditional by WF-2.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **WF-3 output (conditional on integrand pointwise equality).**
Given the WF-2 decomposition data and the integral-linearity hypothesis, the
rectangle contour integral of `weilIntegrand h` equals `2πi · Σ ρ ∈ Z, -h(ρ)`.

The pointwise-agreement input `h_f_eq_decomp` packages the fact that on the
rectangle boundary (which misses all poles in `Z`), `weilIntegrand h` equals
the decomposition `∑ ρ ∈ Z, -h(ρ)/(z − ρ) + weilRemainderGlobal(z)`.
This is established separately when needed (each edge avoids `Z` since `Z` is
strictly interior). -/
theorem rectContourIntegral_weilIntegrand_eq_residue_sum
    {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (hσR : σR < 1)
    (hp_re : ∀ ρ ∈ Z, σL < ρ.re ∧ ρ.re < σR)
    (hp_im : ∀ ρ ∈ Z, -T < ρ.im ∧ ρ.im < T)
    (hh_an : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), AnalyticAt ℂ h s)
    (hζ_ne_off_Z : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        s ∉ Z → riemannZeta s ≠ 0)
    (h_f_eq_decomp :
        rectContourIntegral σL σR T (weilIntegrand h) =
        rectContourIntegral σL σR T
          (fun z => ∑ ρ ∈ Z, (-h ρ) / (z - ρ) +
            weilRemainderGlobal h Z hB hZ_ne_one z))
    (h_integral_eq : rectContourIntegral σL σR T
        (fun z => ∑ ρ ∈ Z, (-h ρ) / (z - ρ) +
          weilRemainderGlobal h Z hB hZ_ne_one z) =
      (∑ ρ ∈ Z, rectContourIntegral σL σR T (fun z => (-h ρ) / (z - ρ))) +
      rectContourIntegral σL σR T (weilRemainderGlobal h Z hB hZ_ne_one)) :
    rectContourIntegral σL σR T (weilIntegrand h) =
      2 * (Real.pi : ℂ) * I * ∑ ρ ∈ Z, (-h ρ) := by
  have hσord : σL ≤ σR := hσ.le
  -- `g` is DifferentiableOn the closed rectangle (from WF-2).
  have hg_diff :
      DifferentiableOn ℂ (weilRemainderGlobal h Z hB hZ_ne_one)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    weilRemainderGlobal_differentiableOn_rect hB hZ_ne_one σL σR T hσord hσR hh_an hζ_ne_off_Z
  -- Apply rectResidueTheorem_multi_pole_unconditional with the id-pole map + -h-residues.
  have h_id_pole : ∀ ρ ∈ Z, σL < ((id ρ : ℂ)).re ∧ ((id ρ : ℂ)).re < σR := by
    intro ρ hρ; exact hp_re ρ hρ
  have h_id_pole_im : ∀ ρ ∈ Z, -T < ((id ρ : ℂ)).im ∧ ((id ρ : ℂ)).im < T := by
    intro ρ hρ; exact hp_im ρ hρ
  have hres := rectResidueTheorem_multi_pole_unconditional hσ hT Z
    (p := fun ρ => ρ) (r := fun ρ => -h ρ)
    (g := weilRemainderGlobal h Z hB hZ_ne_one)
    h_id_pole h_id_pole_im hg_diff h_integral_eq
  -- Chain: rectContourIntegral weilIntegrand = rect(decomp) = 2πi · Σ -h(ρ).
  rw [h_f_eq_decomp]
  exact hres

#print axioms rectContourIntegral_weilIntegrand_eq_residue_sum

-- ═══════════════════════════════════════════════════════════════════════════
-- § Integral linearity for rectContourIntegral (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`rectContourIntegral` additivity.** For any two functions `f₁`, `f₂` both
interval-integrable on every rectangle edge, the contour integral distributes. -/
theorem rectContourIntegral_add
    (σL σR T : ℝ) (f₁ f₂ : ℂ → ℂ)
    (h₁_b : IntervalIntegrable (fun x : ℝ => f₁ (↑x + (-T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h₂_b : IntervalIntegrable (fun x : ℝ => f₂ (↑x + (-T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h₁_t : IntervalIntegrable (fun x : ℝ => f₁ (↑x + (T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h₂_t : IntervalIntegrable (fun x : ℝ => f₂ (↑x + (T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h₁_r : IntervalIntegrable (fun y : ℝ => f₁ (↑σR + ↑y * I))
      MeasureTheory.volume (-T) T)
    (h₂_r : IntervalIntegrable (fun y : ℝ => f₂ (↑σR + ↑y * I))
      MeasureTheory.volume (-T) T)
    (h₁_l : IntervalIntegrable (fun y : ℝ => f₁ (↑σL + ↑y * I))
      MeasureTheory.volume (-T) T)
    (h₂_l : IntervalIntegrable (fun y : ℝ => f₂ (↑σL + ↑y * I))
      MeasureTheory.volume (-T) T) :
    rectContourIntegral σL σR T (fun z => f₁ z + f₂ z) =
      rectContourIntegral σL σR T f₁ + rectContourIntegral σL σR T f₂ := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_add h₁_b h₂_b]
  rw [intervalIntegral.integral_add h₁_t h₂_t]
  rw [intervalIntegral.integral_add h₁_r h₂_r]
  rw [intervalIntegral.integral_add h₁_l h₂_l]
  simp only [smul_add]
  ring

#print axioms rectContourIntegral_add

/-- **`rectContourIntegral` distributes over finite sums.** -/
theorem rectContourIntegral_finset_sum
    (σL σR T : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h_b : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i (↑x + (-T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h_t : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i (↑x + (T : ℝ) * I))
      MeasureTheory.volume σL σR)
    (h_r : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i (↑σR + ↑y * I))
      MeasureTheory.volume (-T) T)
    (h_l : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i (↑σL + ↑y * I))
      MeasureTheory.volume (-T) T) :
    rectContourIntegral σL σR T (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, rectContourIntegral σL σR T (f i) := by
  unfold rectContourIntegral
  show (((∫ x in σL..σR, ∑ i ∈ s, f i (↑x + (-T : ℝ) * I)) -
          ∫ x in σL..σR, ∑ i ∈ s, f i (↑x + (T : ℝ) * I)) +
        I • ∫ y in -T..T, ∑ i ∈ s, f i (↑σR + ↑y * I)) -
      I • ∫ y in -T..T, ∑ i ∈ s, f i (↑σL + ↑y * I) = _
  rw [intervalIntegral.integral_finset_sum h_b]
  rw [intervalIntegral.integral_finset_sum h_t]
  rw [intervalIntegral.integral_finset_sum h_r]
  rw [intervalIntegral.integral_finset_sum h_l]
  rw [Finset.smul_sum, Finset.smul_sum]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

#print axioms rectContourIntegral_finset_sum

end Contour
end WeilPositivity
end ZD

end
