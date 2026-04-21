import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.HalfLineParseval

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

/-- **Half-line cosine Parseval.** Proved from Mathlib Plancherel via
`HalfLineParseval.halfLine_cosine_parseval_strong`. Requires `Measurable f`
and `Integrable f` on `Ioi 0` in addition to the original L² hypothesis —
these support the Bochner-Fourier path for the even extension. -/
theorem halfLine_cosine_parseval (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_int : MeasureTheory.Integrable f
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hf : MeasureTheory.Integrable (fun t => f t ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    MeasureTheory.Integrable
        (fun γ => (∫ t in Set.Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    ∫ γ in Set.Ioi (0 : ℝ),
        (∫ t in Set.Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Set.Ioi (0 : ℝ), f t ^ 2 :=
  HalfLineParseval.halfLine_cosine_parseval_strong hf_meas hf_int hf

/-- **Half-line sine Parseval.** Proved analogously via the odd extension. -/
theorem halfLine_sine_parseval (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_int : MeasureTheory.Integrable f
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hf : MeasureTheory.Integrable (fun t => f t ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    MeasureTheory.Integrable
        (fun γ => (∫ t in Set.Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    ∫ γ in Set.Ioi (0 : ℝ),
        (∫ t in Set.Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Set.Ioi (0 : ℝ), f t ^ 2 :=
  HalfLineParseval.halfLine_sine_parseval_strong hf_meas hf_int hf

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

/-- **Averaged energy = weighted L² norm** (uses half-line Parseval theorems).
`∫₀^∞ ℰ(β,γ) dγ = 2π ∫₀^∞ [(cosh(δt)−1)² + sinh(δt)²] ψ(t)² dt` -/
theorem averageEnergyDefect_eq_weighted_L2 (ψ : ℝ → ℝ) (β : ℝ)
    (hψ_meas : Measurable ψ)
    (hf1 : MeasureTheory.Integrable
      (fun t => amplitudeDefectEnvelope β t * ψ t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hg1 : MeasureTheory.Integrable
      (fun t => oddDefectEnvelope β t * ψ t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
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
  unfold averageEnergyDefect
  simp_rw [energyDefect_eq_four_sq_add_four_sq]
  have hC_eq : ∀ γ, cosineDefectTransform ψ β γ =
      ∫ t in Set.Ioi (0 : ℝ),
        (amplitudeDefectEnvelope β t * ψ t) * Real.cos (γ * t) := by
    intro γ
    unfold cosineDefectTransform
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  have hS_eq : ∀ γ, sineDefectTransform ψ β γ =
      ∫ t in Set.Ioi (0 : ℝ),
        (oddDefectEnvelope β t * ψ t) * Real.sin (γ * t) := by
    intro γ
    unfold sineDefectTransform
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  simp_rw [hC_eq, hS_eq]
  have hAmpCont : Continuous (amplitudeDefectEnvelope β) := by
    unfold amplitudeDefectEnvelope; fun_prop
  have hOddCont : Continuous (oddDefectEnvelope β) := by
    unfold oddDefectEnvelope; fun_prop
  have hC_meas : Measurable (fun t => amplitudeDefectEnvelope β t * ψ t) :=
    hAmpCont.measurable.mul hψ_meas
  have hS_meas : Measurable (fun t => oddDefectEnvelope β t * ψ t) :=
    hOddCont.measurable.mul hψ_meas
  obtain ⟨hC_int, hC_val⟩ := halfLine_cosine_parseval
    (fun t => amplitudeDefectEnvelope β t * ψ t) hC_meas hf1 hf
  obtain ⟨hS_int, hS_val⟩ := halfLine_sine_parseval
    (fun t => oddDefectEnvelope β t * ψ t) hS_meas hg1 hg
  rw [MeasureTheory.integral_add (hC_int.const_mul 4) (hS_int.const_mul 4),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hC_val, hS_val]
  have hsum : (∫ t in Set.Ioi (0 : ℝ),
      ((amplitudeDefectEnvelope β t) ^ 2 + (oddDefectEnvelope β t) ^ 2) *
        (ψ t) ^ 2) =
      (∫ t in Set.Ioi (0 : ℝ), (amplitudeDefectEnvelope β t * ψ t) ^ 2) +
      (∫ t in Set.Ioi (0 : ℝ), (oddDefectEnvelope β t * ψ t) ^ 2) := by
    rw [← MeasureTheory.integral_add hf hg]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [hsum]
  ring

/-- **Averaged off-line detection.** If `β ≠ 1/2` and the test function `ψ`
is nontrivial on `(0,∞)`, then the averaged energy defect is strictly
positive. An off-line zero CANNOT make the transported energy observable
vanish for almost every height γ.

This is a no-hiding theorem: the off-line spectral imbalance always
registers in the γ-averaged transported detector. -/
theorem averageEnergyDefect_pos_offline (ψ : ℝ → ℝ) {β : ℝ}
    (hβ : β ≠ 1 / 2)
    (hψ_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), (ψ t) ^ 2)
    (hψ_meas : Measurable ψ)
    (hf1 : MeasureTheory.Integrable
      (fun t => amplitudeDefectEnvelope β t * ψ t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hg1 : MeasureTheory.Integrable
      (fun t => oddDefectEnvelope β t * ψ t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hf : MeasureTheory.Integrable
      (fun t => (amplitudeDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hg : MeasureTheory.Integrable
      (fun t => (oddDefectEnvelope β t * ψ t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    0 < averageEnergyDefect ψ β := by
  rw [averageEnergyDefect_eq_weighted_L2 ψ β hψ_meas hf1 hg1 hf hg]
  apply mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
  -- envelope(t) := (ADE β t)² + (ODE β t)² ≥ 0, strictly positive on Ioi 0 for β ≠ 1/2
  set envelope : ℝ → ℝ :=
    fun t => amplitudeDefectEnvelope β t ^ 2 + oddDefectEnvelope β t ^ 2 with henv
  have h_env_nn : ∀ t, 0 ≤ envelope t :=
    fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_env_pos : ∀ {t : ℝ}, 0 < t → envelope t ≠ 0 := by
    intro t ht
    simp only [henv, amplitudeDefectEnvelope, oddDefectEnvelope]
    have hδ : (β - 1 / 2) ≠ 0 := sub_ne_zero.mpr hβ
    have hsinh : Real.sinh ((β - 1 / 2) * t) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero hδ (ne_of_gt ht))
    have hpos : 0 < (Real.sinh ((β - 1 / 2) * t)) ^ 2 := by positivity
    exact ne_of_gt (by linarith [sq_nonneg (Real.cosh ((β - 1 / 2) * t) - 1)])
  have h_int : IntegrableOn (fun t => envelope t * ψ t ^ 2) (Set.Ioi (0 : ℝ)) := by
    have := hf.add hg
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, henv]; ring
  have hψ_nn : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ (ψ t) ^ 2 := Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hψ_intOn : IntegrableOn (fun t => (ψ t) ^ 2) (Set.Ioi (0 : ℝ)) := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hψ_pos
    exact lt_irrefl _ hψ_pos
  have hψ_supp_pos :
      0 < (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (Function.support (fun t => (ψ t) ^ 2)) := by
    rwa [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hψ_nn hψ_intOn] at hψ_pos
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun t => mul_nonneg (h_env_nn t) (sq_nonneg _)) h_int]
  refine lt_of_lt_of_le hψ_supp_pos ?_
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi,
      MeasureTheory.Measure.restrict_apply' measurableSet_Ioi]
  apply MeasureTheory.measure_mono
  rintro t ⟨ht_supp, ht_pos⟩
  refine ⟨?_, ht_pos⟩
  simp only [Function.mem_support, ne_eq] at ht_supp ⊢
  exact mul_ne_zero (h_env_pos ht_pos) ht_supp

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
