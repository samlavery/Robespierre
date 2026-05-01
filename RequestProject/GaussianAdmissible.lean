import Mathlib
import RequestProject.WeilBridge
import RequestProject.EnergyDefect

/-!
# Concrete Admissible Test Function: the Gaussian

Item (4) of the Weil-bridge completion program: supply a concrete
`ψ : ℝ → ℝ` satisfying `AdmissibleThetaKernel ψ`.

We take the Gaussian `ψ(t) = exp(-t²)`. The two nontrivial admissibility
fields (even- and odd-envelope L²-integrability) follow from a uniform
pointwise domination:

  `(env β t · exp(-t²))² ≤ exp((β - 1/2)²) · exp(-t²)`

proved via `cosh(x) ≤ exp|x|` and the AM-GM bound `2|δ||t| ≤ δ² + t²`.
The dominator is a constant multiple of the standard Gaussian, hence
integrable on all of ℝ — integrability on `Ioi 0` is then free.

The `nontrivial` field is `0 < ∫_{Ioi 0} (ψ t)² dt`, which reduces to
positivity of `volume (support · ∩ Ioi 0) = volume (Ioi 0) = ∞ > 0`
via `setIntegral_pos_iff_support_of_nonneg_ae`.

Axiom footprint: mathlib-standard only. No `sorry`, no custom axioms.
-/

open Real MeasureTheory Set

noncomputable section

namespace ZD

/-- The Gaussian test function `ψ(t) = exp(-t²)`. Canonical admissible ψ:
strictly positive everywhere, super-exponentially decaying, dominates
every `cosh((β - 1/2) · t)` after AM-GM. -/
def ψ_gaussian : ℝ → ℝ := fun t => Real.exp (-t^2)

theorem ψ_gaussian_pos (t : ℝ) : 0 < ψ_gaussian t := Real.exp_pos _

theorem ψ_gaussian_sq_eq (t : ℝ) :
    (ψ_gaussian t) ^ 2 = Real.exp (-2 * t ^ 2) := by
  unfold ψ_gaussian
  rw [pow_two, ← Real.exp_add]
  congr 1; ring

/-- Elementary bound: `cosh x ≤ exp |x|`. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq, abs_eq_max_neg]
  rcases le_total 0 x with h | h
  · rw [max_eq_left (by linarith)]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [max_eq_right (by linarith)]
    have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- **Domination inequality.** For any `δ, t ∈ ℝ`:

  `cosh²(δ·t) · exp(-2t²) ≤ exp(δ²) · exp(-t²)`.

Pointwise bound by AM-GM (`2|δ||t| ≤ δ² + t²`) after using
`cosh x ≤ exp|x|`. This is the integrability workhorse. -/
theorem cosh_sq_gaussian_dominated (δ t : ℝ) :
    Real.cosh (δ * t) ^ 2 * Real.exp (-2 * t ^ 2) ≤
      Real.exp (δ ^ 2) * Real.exp (-t ^ 2) := by
  have hcosh_nonneg : 0 ≤ Real.cosh (δ * t) := by
    linarith [Real.one_le_cosh (δ * t)]
  have hcosh : Real.cosh (δ * t) ≤ Real.exp |δ * t| := cosh_le_exp_abs _
  have hcosh_sq : Real.cosh (δ * t) ^ 2 ≤ Real.exp (2 * |δ * t|) := by
    calc Real.cosh (δ * t) ^ 2
        ≤ Real.exp |δ * t| ^ 2 := pow_le_pow_left₀ hcosh_nonneg hcosh 2
      _ = Real.exp (2 * |δ * t|) := by rw [← Real.exp_nat_mul]; ring_nf
  have habs : |δ * t| = |δ| * |t| := abs_mul _ _
  have hamgm : 2 * (|δ| * |t|) ≤ δ ^ 2 + t ^ 2 := by
    have hsq := sq_nonneg (|δ| - |t|)
    have hδ : |δ| ^ 2 = δ ^ 2 := sq_abs δ
    have ht : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hexp_le :
      Real.exp (2 * |δ * t|) * Real.exp (-2 * t ^ 2) ≤
        Real.exp (δ ^ 2) * Real.exp (-t ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [habs]; linarith
  calc Real.cosh (δ * t) ^ 2 * Real.exp (-2 * t ^ 2)
      ≤ Real.exp (2 * |δ * t|) * Real.exp (-2 * t ^ 2) :=
        mul_le_mul_of_nonneg_right hcosh_sq (Real.exp_nonneg _)
    _ ≤ Real.exp (δ ^ 2) * Real.exp (-t ^ 2) := hexp_le

/-- The one-variable Gaussian is integrable on ℝ. -/
theorem integrable_exp_neg_t_sq :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
  have := integrable_exp_neg_mul_sq (b := 1) (by norm_num : (0 : ℝ) < 1)
  convert this using 1
  ext t; ring_nf

theorem integrable_const_mul_gaussian (C : ℝ) :
    Integrable (fun t : ℝ => C * Real.exp (-t ^ 2)) :=
  integrable_exp_neg_t_sq.const_mul C

/-- The half-variance Gaussian is integrable on ℝ. -/
theorem integrable_exp_neg_half_t_sq :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2 / 2)) := by
  have := integrable_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
  convert this using 1
  ext t; ring_nf

/-- Even envelope squared is pointwise bounded by `cosh²`. -/
theorem amp_env_sq_le_cosh_sq (β t : ℝ) :
    (amplitudeDefectEnvelope β t) ^ 2 ≤ Real.cosh ((β - 1 / 2) * t) ^ 2 := by
  unfold amplitudeDefectEnvelope
  have h1 : 1 ≤ Real.cosh ((β - 1 / 2) * t) := Real.one_le_cosh _
  have hge : 0 ≤ Real.cosh ((β - 1 / 2) * t) - 1 := by linarith
  have hle : Real.cosh ((β - 1 / 2) * t) - 1 ≤ Real.cosh ((β - 1 / 2) * t) := by linarith
  exact pow_le_pow_left₀ hge hle 2

/-- Odd envelope squared is bounded by `cosh²` via `cosh² - sinh² = 1`. -/
theorem odd_env_sq_le_cosh_sq (β t : ℝ) :
    (oddDefectEnvelope β t) ^ 2 ≤ Real.cosh ((β - 1 / 2) * t) ^ 2 := by
  unfold oddDefectEnvelope
  rw [Real.sinh_sq]
  linarith [Real.one_le_cosh ((β - 1 / 2) * t),
            sq_nonneg (Real.cosh ((β - 1 / 2) * t))]

/-- **Pointwise integrand bound (even channel)**: `(E_β(t) · ψ(t))² ≤ exp((β-½)²) · exp(-t²)`. -/
theorem amp_env_mul_psi_sq_bound (β t : ℝ) :
    (amplitudeDefectEnvelope β t * ψ_gaussian t) ^ 2 ≤
      Real.exp ((β - 1 / 2) ^ 2) * Real.exp (-t ^ 2) := by
  rw [mul_pow, ψ_gaussian_sq_eq]
  calc (amplitudeDefectEnvelope β t) ^ 2 * Real.exp (-2 * t ^ 2)
      ≤ Real.cosh ((β - 1 / 2) * t) ^ 2 * Real.exp (-2 * t ^ 2) :=
        mul_le_mul_of_nonneg_right (amp_env_sq_le_cosh_sq β t) (Real.exp_nonneg _)
    _ ≤ Real.exp ((β - 1 / 2) ^ 2) * Real.exp (-t ^ 2) :=
        cosh_sq_gaussian_dominated _ _

/-- **Pointwise integrand bound (odd channel)**. -/
theorem odd_env_mul_psi_sq_bound (β t : ℝ) :
    (oddDefectEnvelope β t * ψ_gaussian t) ^ 2 ≤
      Real.exp ((β - 1 / 2) ^ 2) * Real.exp (-t ^ 2) := by
  rw [mul_pow, ψ_gaussian_sq_eq]
  calc (oddDefectEnvelope β t) ^ 2 * Real.exp (-2 * t ^ 2)
      ≤ Real.cosh ((β - 1 / 2) * t) ^ 2 * Real.exp (-2 * t ^ 2) :=
        mul_le_mul_of_nonneg_right (odd_env_sq_le_cosh_sq β t) (Real.exp_nonneg _)
    _ ≤ Real.exp ((β - 1 / 2) ^ 2) * Real.exp (-t ^ 2) :=
        cosh_sq_gaussian_dominated _ _

/-! ### Continuity (for AE-strongly-measurable hypotheses) -/

theorem continuous_ψ_gaussian : Continuous ψ_gaussian := by
  unfold ψ_gaussian
  exact Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))

theorem continuous_amplitudeDefectEnvelope (β : ℝ) :
    Continuous (amplitudeDefectEnvelope β) := by
  unfold amplitudeDefectEnvelope
  exact (Real.continuous_cosh.comp
    ((continuous_const.sub continuous_const).mul continuous_id)).sub continuous_const

theorem continuous_oddDefectEnvelope (β : ℝ) :
    Continuous (oddDefectEnvelope β) := by
  unfold oddDefectEnvelope
  exact Real.continuous_sinh.comp
    ((continuous_const.sub continuous_const).mul continuous_id)

theorem continuous_amp_env_mul_psi (β : ℝ) :
    Continuous (fun t => (amplitudeDefectEnvelope β t * ψ_gaussian t) ^ 2) :=
  ((continuous_amplitudeDefectEnvelope β).mul continuous_ψ_gaussian).pow 2

theorem continuous_odd_env_mul_psi (β : ℝ) :
    Continuous (fun t => (oddDefectEnvelope β t * ψ_gaussian t) ^ 2) :=
  ((continuous_oddDefectEnvelope β).mul continuous_ψ_gaussian).pow 2

/-! ### Integrability on ℝ (then restrict to `Ioi 0` for admissibility) -/

/-- **Even-channel integrability on ℝ.** The integrand is nonneg, continuous,
and dominated pointwise by `exp((β-½)²)·exp(-t²)`. -/
theorem integrable_amp_env_sq (β : ℝ) :
    Integrable
      (fun t => (amplitudeDefectEnvelope β t * ψ_gaussian t) ^ 2) volume := by
  apply Integrable.mono'
    (integrable_const_mul_gaussian (Real.exp ((β - 1 / 2) ^ 2)))
    (continuous_amp_env_mul_psi β).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact amp_env_mul_psi_sq_bound β t

/-- **Odd-channel integrability on ℝ.** -/
theorem integrable_odd_env_sq (β : ℝ) :
    Integrable
      (fun t => (oddDefectEnvelope β t * ψ_gaussian t) ^ 2) volume := by
  apply Integrable.mono'
    (integrable_const_mul_gaussian (Real.exp ((β - 1 / 2) ^ 2)))
    (continuous_odd_env_mul_psi β).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact odd_env_mul_psi_sq_bound β t

/-! ### L¹ bounds (for the `halfLine_{cos,sin}_parseval` hypotheses) -/

/-- **L¹ pointwise bound (even channel)**: the bound uses
`cosh(x) ≤ exp |x|` and `2ab ≤ a² + b²`:
`(cosh(δt) − 1) · exp(−t²) ≤ exp(δ²/2) · exp(−t²/2)`. -/
theorem amp_env_mul_psi_abs_bound (β t : ℝ) :
    |amplitudeDefectEnvelope β t * ψ_gaussian t| ≤
      Real.exp ((β - 1 / 2) ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := by
  set δ := β - 1 / 2 with hδ
  unfold amplitudeDefectEnvelope ψ_gaussian
  have hamp_nn : 0 ≤ Real.cosh (δ * t) - 1 := by linarith [Real.one_le_cosh (δ * t)]
  have hψ_nn : 0 ≤ Real.exp (-t ^ 2) := Real.exp_nonneg _
  rw [abs_of_nonneg (mul_nonneg hamp_nn hψ_nn)]
  calc (Real.cosh (δ * t) - 1) * Real.exp (-t ^ 2)
      ≤ Real.cosh (δ * t) * Real.exp (-t ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hψ_nn; linarith
    _ ≤ Real.exp |δ * t| * Real.exp (-t ^ 2) :=
        mul_le_mul_of_nonneg_right (cosh_le_exp_abs _) hψ_nn
    _ = Real.exp (|δ * t| + -t ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (δ ^ 2 / 2 + t ^ 2 / 2 + -t ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : |δ * t| ≤ δ ^ 2 / 2 + t ^ 2 / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|δ| - |t|), sq_abs δ, sq_abs t,
                     abs_nonneg δ, abs_nonneg t]
        linarith
    _ = Real.exp (δ ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **L¹ pointwise bound (odd channel)** — same bound via `|sinh x| ≤ cosh x`. -/
theorem odd_env_mul_psi_abs_bound (β t : ℝ) :
    |oddDefectEnvelope β t * ψ_gaussian t| ≤
      Real.exp ((β - 1 / 2) ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := by
  set δ := β - 1 / 2 with hδ
  unfold oddDefectEnvelope ψ_gaussian
  have hψ_nn : 0 ≤ Real.exp (-t ^ 2) := Real.exp_nonneg _
  rw [abs_mul, abs_of_nonneg hψ_nn]
  have habs_sinh_le_cosh : |Real.sinh (δ * t)| ≤ Real.cosh (δ * t) := by
    rw [Real.abs_sinh, ← Real.cosh_abs (δ * t)]
    have hdiff : Real.cosh |δ * t| - Real.sinh |δ * t| = Real.exp (-|δ * t|) := by
      rw [Real.cosh_eq, Real.sinh_eq]; ring
    linarith [Real.exp_nonneg (-|δ * t|)]
  calc |Real.sinh (δ * t)| * Real.exp (-t ^ 2)
      ≤ Real.cosh (δ * t) * Real.exp (-t ^ 2) :=
        mul_le_mul_of_nonneg_right habs_sinh_le_cosh hψ_nn
    _ ≤ Real.exp |δ * t| * Real.exp (-t ^ 2) :=
        mul_le_mul_of_nonneg_right (cosh_le_exp_abs _) hψ_nn
    _ = Real.exp (|δ * t| + -t ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (δ ^ 2 / 2 + t ^ 2 / 2 + -t ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : |δ * t| ≤ δ ^ 2 / 2 + t ^ 2 / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|δ| - |t|), sq_abs δ, sq_abs t,
                     abs_nonneg δ, abs_nonneg t]
        linarith
    _ = Real.exp (δ ^ 2 / 2) * Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **Even-channel L¹ integrability on ℝ.** -/
theorem integrable_amp_env_mul_psi (β : ℝ) :
    Integrable (fun t => amplitudeDefectEnvelope β t * ψ_gaussian t) volume := by
  apply Integrable.mono'
    (integrable_exp_neg_half_t_sq.const_mul (Real.exp ((β - 1 / 2) ^ 2 / 2)))
    ((continuous_amplitudeDefectEnvelope β).mul continuous_ψ_gaussian).aestronglyMeasurable
  filter_upwards with t using amp_env_mul_psi_abs_bound β t

/-- **Odd-channel L¹ integrability on ℝ.** -/
theorem integrable_odd_env_mul_psi (β : ℝ) :
    Integrable (fun t => oddDefectEnvelope β t * ψ_gaussian t) volume := by
  apply Integrable.mono'
    (integrable_exp_neg_half_t_sq.const_mul (Real.exp ((β - 1 / 2) ^ 2 / 2)))
    ((continuous_oddDefectEnvelope β).mul continuous_ψ_gaussian).aestronglyMeasurable
  filter_upwards with t using odd_env_mul_psi_abs_bound β t

/-! ### Positivity of the L² mass -/

/-- `0 < ∫_{Ioi 0} ψ_gaussian² dt`. The integrand is strictly positive everywhere,
so its support is all of ℝ, and `volume (Ioi 0) = ∞ > 0`. -/
theorem ψ_gaussian_nontrivial :
    0 < ∫ t in Ioi (0 : ℝ), (ψ_gaussian t) ^ 2 := by
  have h_int : IntegrableOn (fun t => (ψ_gaussian t) ^ 2) (Ioi (0 : ℝ)) := by
    have : Integrable (fun t => (ψ_gaussian t) ^ 2) volume := by
      simp_rw [ψ_gaussian_sq_eq]
      exact integrable_exp_neg_mul_sq (b := 2) (by norm_num)
    exact this.restrict
  have h_nonneg :
      0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))] fun t => (ψ_gaussian t) ^ 2 := by
    filter_upwards with t using sq_nonneg _
  rw [setIntegral_pos_iff_support_of_nonneg_ae h_nonneg h_int]
  have h_support : Function.support (fun t => (ψ_gaussian t) ^ 2) = univ := by
    ext t
    simp [Function.mem_support, (ψ_gaussian_pos t).ne']
  rw [h_support, univ_inter, volume_Ioi]
  exact ENNReal.zero_lt_top

/-! ### Capstone: admissibility -/

/-- **The Gaussian is an admissible test function** for the Weil bridge. -/
theorem ψ_gaussian_admissible : AdmissibleThetaKernel ψ_gaussian where
  nontrivial := ψ_gaussian_nontrivial
  measurable := continuous_ψ_gaussian.measurable
  l1_even := fun β => (integrable_amp_env_mul_psi β).restrict
  l1_odd := fun β => (integrable_odd_env_mul_psi β).restrict
  l2_even := fun β => (integrable_amp_env_sq β).restrict
  l2_odd := fun β => (integrable_odd_env_sq β).restrict

/-! ### Axiom hygiene -/

#print axioms ψ_gaussian_admissible

end ZD

end
