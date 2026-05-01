import Mathlib

/-!
# Converse Mellin inversion: `mellin (mellinInv σ F) s = F s`

Mathlib has `mellinInv_mellin_eq` (forward direction). This file provides the
CONVERSE: applying `mellin` to `mellinInv σ F` recovers `F` along the line
`Re s = σ`. Derived from `MeasureTheory.Integrable.fourier_fourierInv_eq`
via `mellin_eq_fourier` and `mellinInv_eq_fourierInv`.
-/

open Real Complex Set MeasureTheory
open scoped FourierTransform

namespace ZD.MellinInvMellin

/-- Parametrization: the Fourier data for `mellinInv σ F`. -/
noncomputable def fourierData (σ : ℝ) (F : ℂ → ℂ) (y : ℝ) : ℂ :=
  F (σ + 2 * π * y * I)

/-- The σ-shifted Mellin integrand for `f := mellinInv σ F` at `x = exp(-u)`,
EQUALS `𝓕⁻ G u` POINTWISE in `u`. -/
private lemma g_eq_fourierInv_pointwise (σ : ℝ) (F : ℂ → ℂ) (u : ℝ) :
    (Real.exp (-σ * u) : ℝ) • mellinInv σ F (Real.exp (-u)) =
    𝓕⁻ (fourierData σ F) u := by
  have hx : 0 < Real.exp (-u) := Real.exp_pos _
  rw [mellinInv_eq_fourierInv σ F hx]
  -- mellinInv σ F (exp(-u)) = (exp(-u) : ℂ)^(-σ:ℂ) • 𝓕⁻ G(-log(exp(-u)))
  --                        = (exp(-u) : ℂ)^(-σ:ℂ) • 𝓕⁻ G(u)
  have h_log : -Real.log (Real.exp (-u)) = u := by rw [Real.log_exp]; ring
  rw [h_log]
  -- Goal: (rexp(-σu) : ℝ) • ((exp(-u) : ℂ)^(-σ:ℂ) • 𝓕⁻ G u) = 𝓕⁻ G u
  -- Compute: (exp(-u) : ℂ)^(-σ:ℂ) = (rexp(σu) : ℂ).
  have h_cpow : ((Real.exp (-u) : ℝ) : ℂ) ^ (-σ : ℂ) =
      ((Real.exp (σ * u) : ℝ) : ℂ) := by
    have := Complex.ofReal_cpow hx.le (-σ : ℝ)
    rw [show ((-σ : ℝ) : ℂ) = (-σ : ℂ) from by push_cast; rfl] at this
    rw [← this]
    congr 1
    rw [Real.rpow_def_of_pos hx, Real.log_exp]
    congr 1; ring
  rw [h_cpow]
  -- Goal: (rexp(-σu) : ℝ) • ((rexp(σu) : ℝ : ℂ) • 𝓕⁻ G u) = 𝓕⁻ G u
  rw [← smul_assoc, Complex.real_smul, ← ofReal_mul,
      show Real.exp (-σ * u) * Real.exp (σ * u) = 1 from by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero,
      ofReal_one, one_smul]
  rfl

/-- **Converse Mellin inversion (axiom-clean).** -/
theorem mellin_mellinInv_eq (σ : ℝ) (F : ℂ → ℂ) (t : ℝ)
    (hG_int : Integrable (fourierData σ F))
    (hG_fwd_int : Integrable (𝓕 (fourierData σ F)))
    (hG_cont : ContinuousAt (fourierData σ F) (t / (2 * π))) :
    mellin (mellinInv σ F) ((σ : ℂ) + t * I) = F ((σ : ℂ) + t * I) := by
  -- Express as Fourier transform via `mellin_eq_fourier`.
  rw [mellin_eq_fourier]
  -- Goal: 𝓕 (fun u ↦ rexp(-σu) • mellinInv σ F (rexp(-u))) (t / (2π)) = F(σ + ti)
  have h_re : ((σ : ℂ) + t * I).re = σ := by simp
  have h_im : ((σ : ℂ) + t * I).im = t := by simp
  rw [h_re, h_im]
  -- Replace the Fourier integrand pointwise.
  have key : 𝓕 (fun u : ℝ => Real.exp (-σ * u) • mellinInv σ F (Real.exp (-u))) (t / (2 * π)) =
      𝓕 (𝓕⁻ (fourierData σ F)) (t / (2 * π)) :=
    congrArg (fun g : ℝ → ℂ => 𝓕 g (t / (2 * π)))
      (by funext u; exact g_eq_fourierInv_pointwise σ F u)
  -- Apply Fourier inversion (converse) and conclude.
  exact key.trans (by
    rw [MeasureTheory.Integrable.fourier_fourierInv_eq hG_int hG_fwd_int hG_cont]
    unfold fourierData; congr 1; push_cast; field_simp)

end ZD.MellinInvMellin
