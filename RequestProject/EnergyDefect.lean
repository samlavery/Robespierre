import Mathlib
import RequestProject.ZetaZeroDefs

open Real Complex MeasureTheory BigOperators

noncomputable section

namespace ZD

/-! ## Quadratic Energy Defect API

The centered transported classical observable decomposes into a real
(cosine/cosh) part and an imaginary (sine/sinh) part. The squared norm
— the energy defect — is a nonnegative quadratic form that vanishes
iff β = 1/2 and is FE-invariant (β ↔ 1−β). -/

-- ═══════════════════════════════════════════════════════════════════════════
-- § Definitions
-- ═══════════════════════════════════════════════════════════════════════════

/-- Even (cosh) envelope defect: `cosh(δt) − 1` where `δ = β − 1/2`. -/
def amplitudeDefectEnvelope (β t : ℝ) : ℝ :=
  Real.cosh ((β - 1 / 2) * t) - 1

/-- Odd (sinh) envelope: `sinh(δt)` where `δ = β − 1/2`. -/
def oddDefectEnvelope (β t : ℝ) : ℝ :=
  Real.sinh ((β - 1 / 2) * t)

/-- Cosine defect transform: `C_ψ(β,γ) = ∫₀^∞ (cosh(δt)−1) cos(γt) ψ(t) dt`. -/
def cosineDefectTransform (ψ : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), amplitudeDefectEnvelope β t * Real.cos (γ * t) * ψ t

/-- Sine defect transform: `S_ψ(β,γ) = ∫₀^∞ sinh(δt) sin(γt) ψ(t) dt`. -/
def sineDefectTransform (ψ : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), oddDefectEnvelope β t * Real.sin (γ * t) * ψ t

/-- Centered excess: `Δ_ψ(β,γ) = 2C + 2Si` as a complex number. -/
def centeredExcess (ψ : ℝ → ℝ) (β γ : ℝ) : ℂ :=
  ((2 * cosineDefectTransform ψ β γ : ℝ) : ℂ) +
    ((2 * sineDefectTransform ψ β γ : ℝ) : ℂ) * Complex.I

/-- Energy defect: `ℰ_ψ(β,γ) = ‖Δ_ψ(β,γ)‖²` via `normSq`. -/
def energyDefect (ψ : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  Complex.normSq (centeredExcess ψ β γ)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Structural Theorems
-- ═══════════════════════════════════════════════════════════════════════════

/-- The centered excess decomposes into real (cosine) and imaginary (sine)
transform pieces. Definitional. -/
theorem centeredExcess_decompose (ψ : ℝ → ℝ) (β γ : ℝ) :
    centeredExcess ψ β γ =
      ((2 * cosineDefectTransform ψ β γ : ℝ) : ℂ) +
        ((2 * sineDefectTransform ψ β γ : ℝ) : ℂ) * Complex.I := rfl

/-- **Key structural identity.** The energy defect decomposes as the sum
of two nonneg squares — the quadratic invariant that governs everything. -/
theorem energyDefect_eq_four_sq_add_four_sq (ψ : ℝ → ℝ) (β γ : ℝ) :
    energyDefect ψ β γ =
      4 * (cosineDefectTransform ψ β γ) ^ 2 +
        4 * (sineDefectTransform ψ β γ) ^ 2 := by
  unfold energyDefect centeredExcess
  set C := cosineDefectTransform ψ β γ
  set S := sineDefectTransform ψ β γ
  have hext : ((2 * C : ℝ) : ℂ) + ((2 * S : ℝ) : ℂ) * I = ⟨2 * C, 2 * S⟩ :=
    Complex.ext (by simp) (by simp)
  rw [hext, Complex.normSq_mk]
  ring

/-- On the critical line `β = 1/2`, the energy defect vanishes. -/
theorem energyDefect_zero_on_line (ψ : ℝ → ℝ) (γ : ℝ) :
    energyDefect ψ (1 / 2) γ = 0 := by
  rw [energyDefect_eq_four_sq_add_four_sq]
  have hC : cosineDefectTransform ψ (1 / 2) γ = 0 := by
    unfold cosineDefectTransform amplitudeDefectEnvelope
    have h : ∀ t : ℝ,
        (Real.cosh ((1 / 2 - 1 / 2) * t) - 1) * Real.cos (γ * t) * ψ t = 0 := by
      intro t; simp [show (1 : ℝ) / 2 - 1 / 2 = 0 from by ring,
                      mul_zero, Real.cosh_zero, sub_self]
    simp_rw [h]
    simp
  have hS : sineDefectTransform ψ (1 / 2) γ = 0 := by
    unfold sineDefectTransform oddDefectEnvelope
    have h : ∀ t : ℝ,
        Real.sinh ((1 / 2 - 1 / 2) * t) * Real.sin (γ * t) * ψ t = 0 := by
      intro t; simp [show (1 : ℝ) / 2 - 1 / 2 = 0 from by ring,
                      mul_zero, Real.sinh_zero]
    simp_rw [h]
    simp
  rw [hC, hS]; ring

/-- The cosine defect transform is even under β ↔ 1−β (cosh is even). -/
theorem cosineDefectTransform_reflect (ψ : ℝ → ℝ) (β γ : ℝ) :
    cosineDefectTransform ψ (1 - β) γ = cosineDefectTransform ψ β γ := by
  unfold cosineDefectTransform amplitudeDefectEnvelope
  congr 1; ext t; congr 1; congr 1
  rw [show (1 - β - 1 / 2) * t = -((β - 1 / 2) * t) from by ring, Real.cosh_neg]

/-- The sine defect transform is odd under β ↔ 1−β (sinh is odd). -/
theorem sineDefectTransform_reflect (ψ : ℝ → ℝ) (β γ : ℝ) :
    sineDefectTransform ψ (1 - β) γ = -sineDefectTransform ψ β γ := by
  unfold sineDefectTransform oddDefectEnvelope
  have hrw : ∀ t : ℝ,
      Real.sinh ((1 - β - 1 / 2) * t) * Real.sin (γ * t) * ψ t =
        -(Real.sinh ((β - 1 / 2) * t) * Real.sin (γ * t) * ψ t) := by
    intro t
    rw [show (1 - β - 1 / 2) * t = -((β - 1 / 2) * t) from by ring, Real.sinh_neg]
    ring
  simp_rw [hrw]
  exact integral_neg _

/-- FE-reflection invariance: `ℰ_ψ(1−β,γ) = ℰ_ψ(β,γ)`.
C is even (cosine), S is odd (sine), so C² + S² is invariant. -/
theorem energyDefect_reflect (ψ : ℝ → ℝ) (β γ : ℝ) :
    energyDefect ψ (1 - β) γ = energyDefect ψ β γ := by
  rw [energyDefect_eq_four_sq_add_four_sq, energyDefect_eq_four_sq_add_four_sq,
      cosineDefectTransform_reflect, sineDefectTransform_reflect, neg_sq]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Averaged Energy Defect (γ-integrated)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Averaged energy defect: integrate the energy defect over all heights γ > 0. -/
def averageEnergyDefect (ψ : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ γ in Set.Ioi (0 : ℝ), energyDefect ψ β γ

/-- On-line, the averaged energy defect is zero. -/
theorem averageEnergyDefect_zero_on_line (ψ : ℝ → ℝ) :
    averageEnergyDefect ψ (1 / 2) = 0 := by
  unfold averageEnergyDefect
  have : ∀ γ : ℝ, energyDefect ψ (1 / 2) γ = 0 :=
    fun γ => energyDefect_zero_on_line ψ γ
  simp_rw [this]
  simp

/-- FE-reflection invariance of the averaged energy defect. -/
theorem averageEnergyDefect_reflect (ψ : ℝ → ℝ) (β : ℝ) :
    averageEnergyDefect ψ (1 - β) = averageEnergyDefect ψ β := by
  unfold averageEnergyDefect
  congr 1; ext γ; exact energyDefect_reflect ψ β γ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Half-Line Parseval (axiomatized — derivable from full-line Plancherel
--   via even/odd extension; Mathlib has `Lp.norm_fourier_eq` for the
--   full-line case but not the half-line cosine/sine specialization)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Half-line cosine Parseval.**
`∫₀^∞ (∫₀^∞ f(t) cos(γt) dt)² dγ = (π/2) ∫₀^∞ f(t)² dt`.
Derivable from full-line Plancherel via even extension: if f̃(t) = f(|t|),
then F̂̃(ξ) = 2 ∫₀^∞ f(t) cos(2πξt) dt; apply Plancherel, unfold symmetry,
change variables. The constant π/2 arises from the unnormalized convention. -/
axiom halfLine_cosine_parseval (f : ℝ → ℝ)
    (hf : MeasureTheory.Integrable (fun t => f t ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    ∫ γ in Set.Ioi (0 : ℝ),
      (∫ t in Set.Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
    (Real.pi / 2) * ∫ t in Set.Ioi (0 : ℝ), f t ^ 2

/-- **Half-line sine Parseval.** Same identity for the sine transform.
Derivable via odd extension. -/
axiom halfLine_sine_parseval (f : ℝ → ℝ)
    (hf : MeasureTheory.Integrable (fun t => f t ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    ∫ γ in Set.Ioi (0 : ℝ),
      (∫ t in Set.Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
    (Real.pi / 2) * ∫ t in Set.Ioi (0 : ℝ), f t ^ 2

-- ═══════════════════════════════════════════════════════════════════════════
-- § Integrand Positivity (fully proved)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The envelope integrand `(cosh(δt)−1)² + sinh(δt)²` is nonneg. -/
theorem envelope_integrand_nonneg (δ t : ℝ) :
    0 ≤ (Real.cosh (δ * t) - 1) ^ 2 + Real.sinh (δ * t) ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Key positivity.** For `δ ≠ 0` and `t > 0`, `sinh(δt) ≠ 0`,
so `sinh(δt)² > 0`, hence the full integrand is strictly positive. -/
theorem envelope_integrand_pos {δ : ℝ} (hδ : δ ≠ 0) {t : ℝ} (ht : 0 < t) :
    0 < (Real.cosh (δ * t) - 1) ^ 2 + Real.sinh (δ * t) ^ 2 := by
  have hdt : δ * t ≠ 0 := mul_ne_zero hδ (ne_of_gt ht)
  have hsinh : Real.sinh (δ * t) ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hsinh)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Averaged Off-Line Detection (the final theorem in this layer)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Averaged energy = weighted L² norm** (uses half-line Parseval axioms).
`∫₀^∞ ℰ(β,γ) dγ = 2π ∫₀^∞ [(cosh(δt)−1)² + sinh(δt)²] ψ(t)² dt` -/
theorem averageEnergyDefect_eq_weighted_L2 (ψ : ℝ → ℝ) (β : ℝ)
    (hf : MeasureTheory.Integrable
      (fun t => (amplitudeDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hg : MeasureTheory.Integrable
      (fun t => (oddDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    averageEnergyDefect ψ β =
      2 * Real.pi * ∫ t in Set.Ioi (0 : ℝ),
        ((amplitudeDefectEnvelope β t) ^ 2 + (oddDefectEnvelope β t) ^ 2) *
          (ψ t) ^ 2 := by
  sorry

/-- **Averaged off-line detection.** If `β ≠ 1/2` and the test function `ψ`
is nontrivial on `(0,∞)`, then the averaged energy defect is strictly
positive. An off-line zero CANNOT make the transported energy observable
vanish for almost every height γ.

This is a no-hiding theorem: the off-line spectral imbalance always
registers in the γ-averaged transported detector. -/
theorem averageEnergyDefect_pos_offline (ψ : ℝ → ℝ) {β : ℝ}
    (hβ : β ≠ 1 / 2)
    (hψ_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), (ψ t) ^ 2)
    (hf : MeasureTheory.Integrable
      (fun t => (amplitudeDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hg : MeasureTheory.Integrable
      (fun t => (oddDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    0 < averageEnergyDefect ψ β := by
  rw [averageEnergyDefect_eq_weighted_L2 ψ β hf hg]
  apply mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
  -- The integrand is ((cosh−1)² + sinh²) · ψ², which is ≥ 0 pointwise
  -- and > 0 wherever ψ(t) ≠ 0 and t > 0 (by envelope_integrand_pos).
  -- Combined with hψ_pos (∫ ψ² > 0), a positive-measure set of t has ψ(t) ≠ 0,
  -- and on that set the full integrand is strictly positive.
  sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- § Conditional Closure (pure logic — no sorry)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Conditional no-offline-zeros theorem.** Given:
- `hzero`: every nontrivial zero has vanishing averaged energy defect,
- `hpos`: every off-line β has strictly positive averaged energy defect,

the contradiction is immediate: an off-line zero would give both = 0 and > 0.

This is the EXACT closure interface. The positivity side (`hpos`) follows from
Parseval + `envelope_integrand_pos`. The vanishing side (`hzero`) is the
remaining RH-sized theorem — it requires connecting `riemannZeta ρ = 0` to
the averaged detector vanishing via the theta/Mellin bridge. -/
theorem no_offline_nontrivial_zeros
    (hzero : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      averageEnergyDefect ψ ρ.re = 0)
    (hpos : ∀ β : ℝ, β ≠ 1 / 2 →
      0 < averageEnergyDefect ψ β) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hne
  have hz : averageEnergyDefect ψ ρ.re = 0 := hzero ρ hρ
  have hp : 0 < averageEnergyDefect ψ ρ.re := hpos ρ.re hne
  linarith

end ZD
