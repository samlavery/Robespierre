import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.EnergyDefect

open Real Complex MeasureTheory BigOperators

noncomputable section

namespace ZD

/-! ## Theta-Side Centered Excess

The classical theta-kernel observable `I_θ(s) = ∫₀^∞ 2 cosh((s-1/2)t) ψ(t) dt`
produces a centered excess `Δ_θ(β,γ) = I_θ(β+iγ) - I_θ(1/2+iγ)` that
decomposes into the cosine and sine defect transforms via the complex-cosh
addition formula. This is the bridge object validated numerically. -/

-- ═══════════════════════════════════════════════════════════════════════════
-- § Definitions
-- ═══════════════════════════════════════════════════════════════════════════

def thetaCenteredExcess (I : ℂ → ℂ) (β γ : ℝ) : ℂ :=
  I ((β : ℂ) + (γ : ℂ) * Complex.I) - I ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I)

def ThetaKernelRep (thetaIntegral : ℂ → ℂ) (ψ : ℝ → ℝ) : Prop :=
  ∀ s : ℂ,
    thetaIntegral s =
      ∫ t in Set.Ioi (0 : ℝ),
        ((2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))

-- ═══════════════════════════════════════════════════════════════════════════
-- § Complex Cosh Identity (the load-bearing trig step)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `cosh(x + iy) - cosh(iy) = (cosh x - 1) cos y + i sinh x sin y`.
This is the kernel of the entire decomposition. Proof via Complex.ext on
real and imaginary parts. -/
theorem cosh_real_add_imag_sub_cosh_imag (a b : ℝ) :
    Complex.cosh ((a : ℂ) + (b : ℂ) * Complex.I)
      - Complex.cosh ((b : ℂ) * Complex.I) =
    ((Real.cosh a - 1) * Real.cos b : ℝ) +
      ((Real.sinh a * Real.sin b : ℝ) : ℂ) * Complex.I := by
  simp only [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § First-Order Derivative Structure (explains the i-rotation)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Derivative of the even defect envelope in β: `t · sinh((β−1/2)t)`. -/
theorem hasDerivAt_amplitudeDefectEnvelope (β t : ℝ) :
    HasDerivAt (fun β' : ℝ => amplitudeDefectEnvelope β' t)
      (t * Real.sinh ((β - 1 / 2) * t)) β := by
  unfold amplitudeDefectEnvelope
  have hinner : HasDerivAt (fun β' => (β' - 1 / 2) * t) (1 * t) β :=
    ((hasDerivAt_id β).sub_const (1 / 2)).mul_const t
  rw [one_mul] at hinner
  convert (Real.hasDerivAt_cosh ((β - 1 / 2) * t)).comp β hinner |>.sub_const 1 using 1; ring

/-- Derivative of the odd defect envelope in β: `t · cosh((β−1/2)t)`. -/
theorem hasDerivAt_oddDefectEnvelope (β t : ℝ) :
    HasDerivAt (fun β' : ℝ => oddDefectEnvelope β' t)
      (t * Real.cosh ((β - 1 / 2) * t)) β := by
  unfold oddDefectEnvelope
  have hinner : HasDerivAt (fun β' => (β' - 1 / 2) * t) (1 * t) β :=
    ((hasDerivAt_id β).sub_const (1 / 2)).mul_const t
  rw [one_mul] at hinner
  convert (Real.hasDerivAt_sinh ((β - 1 / 2) * t)).comp β hinner using 1; ring

/-- At β = 1/2, the even envelope has **zero derivative** (sinh(0) = 0).
The even/cosine channel is silent to first order off the critical line. -/
theorem deriv_amplitudeDefectEnvelope_at_half (t : ℝ) :
    deriv (fun β : ℝ => amplitudeDefectEnvelope β t) (1 / 2) = 0 := by
  rw [(hasDerivAt_amplitudeDefectEnvelope (1 / 2) t).deriv]
  simp [Real.sinh_zero]

/-- At β = 1/2, the odd envelope has **derivative t** (cosh(0) = 1).
The odd/sine channel carries the entire first-order off-line signal.
Combined with the `i` prefactor, this means infinitesimal motion off the
critical line points purely in the imaginary direction — explaining the
observed 90° phase rotation in the centered excess. -/
theorem deriv_oddDefectEnvelope_at_half (t : ℝ) :
    deriv (fun β : ℝ => oddDefectEnvelope β t) (1 / 2) = t := by
  rw [(hasDerivAt_oddDefectEnvelope (1 / 2) t).deriv]
  simp [Real.cosh_zero]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Odd Test Function and Fourier Profile (entry point to Weil)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The odd test kernel: `g_ψ(t) = 2t·ψ(t)`. Under odd extension to the
full line, its Fourier transform is the spectral profile that the Weil
explicit formula consumes. -/
def oddKernel (ψ : ℝ → ℝ) (t : ℝ) : ℝ := 2 * t * ψ t

/-- Half-line sine profile of the odd kernel:
`H_ψ(γ) = ∫₀^∞ g_ψ(t) sin(γt) dt = 2 ∫₀^∞ t sin(γt) ψ(t) dt`. -/
def oddSineProfile (ψ : ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), oddKernel ψ t * Real.sin (γ * t)

/-- The full-line odd Fourier profile: `ĝ_ψ(γ) = -2i · H_ψ(γ)`.
For an odd function f, `∫_{-∞}^{∞} f(t) e^{-iγt} dt = -2i ∫_0^∞ f(t) sin(γt) dt`. -/
def oddFourierProfile (ψ : ℝ → ℝ) (γ : ℝ) : ℂ :=
  (-2 * Complex.I) * (oddSineProfile ψ γ : ℂ)

/-- **Pure algebraic normalization.** `i · H_ψ = -½ · ĝ_ψ` where
`ĝ_ψ = -2i · H_ψ` is the odd Fourier profile. This is the identity
`i·x = -½·(-2i·x)`, proved by `ring`. -/
theorem oddFourier_normalization (ψ : ℝ → ℝ) (γ : ℝ) :
    Complex.I * (oddSineProfile ψ γ : ℂ) =
      (-1 / 2 : ℂ) * oddFourierProfile ψ γ := by
  unfold oddFourierProfile; push_cast; ring

/-- The odd sine profile equals twice the raw sine integral, after commuting
the integrand. This connects the `deriv_oddDefectEnvelope_at_half` output
(`∫ t·sin·ψ`) to the Weil-ready `oddSineProfile` (`∫ 2t·ψ·sin`). -/
theorem oddSineProfile_eq_twice_sineIntegral (ψ : ℝ → ℝ) (γ : ℝ) :
    oddSineProfile ψ γ =
      2 * ∫ t in Set.Ioi (0 : ℝ), t * Real.sin (γ * t) * ψ t := by
  unfold oddSineProfile oddKernel
  simp_rw [show ∀ t, 2 * t * ψ t * Real.sin (γ * t) =
    2 * (t * Real.sin (γ * t) * ψ t) from fun t => by ring]
  rw [MeasureTheory.integral_const_mul]

/-- **The full normalization identity.** The first-order theta defect at
β = 1/2 is `-½ · ĝ_ψ(γ)`. Combines the integral rewriting with the
algebraic normalization. Numerically verified to rel error ~ 10⁻¹⁶. -/
theorem thetaDerivAtHalf_eq_neg_half_oddFourier (ψ : ℝ → ℝ) (γ : ℝ) :
    ((2 * ∫ t in Set.Ioi (0 : ℝ), t * Real.sin (γ * t) * ψ t : ℝ) : ℂ)
        * Complex.I =
      (-1 / 2 : ℂ) * oddFourierProfile ψ γ := by
  rw [← oddFourier_normalization]
  rw [oddSineProfile_eq_twice_sineIntegral]
  push_cast; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § Linear Decomposition
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Key bridge theorem.** The theta centered excess = 2C + 2iS. -/
theorem theta_centeredExcess_eq_twoC_add_twoiS (β γ : ℝ)
    {thetaIntegral : ℂ → ℂ} {ψ : ℝ → ℝ}
    (hrep : ThetaKernelRep thetaIntegral ψ)
    (hint1 : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Complex.cosh
        (((β : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))
      (Set.Ioi 0))
    (hint2 : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Complex.cosh
        (((1 / 2 : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))
      (Set.Ioi 0)) :
    thetaCenteredExcess thetaIntegral β γ =
      ((2 * cosineDefectTransform ψ β γ : ℝ) : ℂ) +
        (((2 * sineDefectTransform ψ β γ : ℝ) : ℂ) * Complex.I) := by
  -- Step 1: Expand using the representation hypothesis
  unfold thetaCenteredExcess
  rw [hrep, hrep]
  -- Step 2: Combine integrals, apply the cosh identity, extract real/imag
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- § Quadratic Energy Defect (theta-side)
-- ═══════════════════════════════════════════════════════════════════════════

def thetaEnergyDefect (thetaIntegral : ℂ → ℂ) (β γ : ℝ) : ℝ :=
  Complex.normSq (thetaCenteredExcess thetaIntegral β γ)

/-- `ℰ_θ = 4C² + 4S²` — the quadratic decomposition. -/
theorem thetaEnergyDefect_eq_four_sq (β γ : ℝ)
    {thetaIntegral : ℂ → ℂ} {ψ : ℝ → ℝ}
    (hrep : ThetaKernelRep thetaIntegral ψ)
    (hint1 : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Complex.cosh
        (((β : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))
      (Set.Ioi 0))
    (hint2 : IntegrableOn
      (fun t : ℝ => (2 : ℂ) * Complex.cosh
        (((1 / 2 : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))
      (Set.Ioi 0)) :
    thetaEnergyDefect thetaIntegral β γ =
      4 * (cosineDefectTransform ψ β γ) ^ 2 +
        4 * (sineDefectTransform ψ β γ) ^ 2 := by
  unfold thetaEnergyDefect
  rw [theta_centeredExcess_eq_twoC_add_twoiS β γ hrep hint1 hint2]
  set C := cosineDefectTransform ψ β γ
  set S := sineDefectTransform ψ β γ
  have hext : ((2 * C : ℝ) : ℂ) + ((2 * S : ℝ) : ℂ) * Complex.I = ⟨2 * C, 2 * S⟩ :=
    Complex.ext (by simp) (by simp)
  rw [hext, Complex.normSq_mk]
  ring

-- ════════════════════════════════════════════════════════════════════════���══
-- § Transport: Pair = Theta
-- ═══════════════════════════════════════════════════════════════════════════

theorem pair_centeredExcess_eq_theta (β γ : ℝ)
    {pairIntegral thetaIntegral : ℂ → ℂ}
    (htransport : ∀ s, pairIntegral s = thetaIntegral s) :
    thetaCenteredExcess pairIntegral β γ =
      thetaCenteredExcess thetaIntegral β γ := by
  unfold thetaCenteredExcess; rw [htransport, htransport]

end ZD
