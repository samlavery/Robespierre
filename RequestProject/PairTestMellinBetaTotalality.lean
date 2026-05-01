import Mathlib
import RequestProject.WeilZeroOrthogonality

/-!
# Proof of PairTestMellinBetaTotality

This file proves `PairTestMellinBetaTotality`: if every β-projection of the
zero-side coefficient family vanishes, then `ZeroMellinSeries a t = 0` for
all `t > 0`.

## Proof outline

The pair-cosh-Gauss test function has the product factorization (proved in
`WeilContour.lean` as `pair_cosh_gauss_test_cosh_expansion`):

  g_β(t) = [cosh(αt) − 1] · [cosh(ct) − 1] · exp(−2t²)

where α = 1 − π/3 and c = 2β − 1 ∈ (−1, 1).

Under Fubini exchange (∑' ↔ ∫), the hypothesis ∑' a(ρ) · h(β,ρ) = 0 gives:

  ∫₀^∞ S(t) · W(t) · [cosh(ct) − 1] dt = 0    ∀ c ∈ (−1, 1)

where S(t) = ∑' a(ρ) t^{ρ−1} and W(t) = [cosh(αt) − 1] exp(−2t²) > 0
for t > 0.

Define Φ(c) := ∫ S(t) W(t) cosh(ct) dt. Then Φ is constant on (−1, 1).
By analyticity + identity theorem: Φ is constant on ℂ.
By Riemann–Lebesgue: the constant = 0.
By Fourier cosine injectivity: S·W = 0 a.e.
Since W > 0 for t > 0: S = 0.

### Note on previous version

The previous version of this file contained a lemma
`functional_equation_quadratic` that is **false** — a counterexample is
Φ(c) = c² + sin²(πc/α). The corrected proof avoids the functional
equation entirely and uses the product factorization directly.
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroOrthogonality

/-! ### Step 1: Identity theorem for entire functions -/

/-- The identity theorem for entire functions: if an entire function equals a
polynomial on (−1, 1), it equals that polynomial everywhere.
(Here specialized to constant functions: κ = 0 gives Φ = a₀ everywhere.) -/
private theorem identity_theorem_extension
    (Φ : ℂ → ℂ) (hΦ_analytic : AnalyticOnNhd ℂ Φ Set.univ)
    (a₀ κ : ℂ)
    (heq : ∀ c : ℝ, |c| < 1 → Φ c = a₀ + κ * c ^ 2) :
    ∀ c : ℂ, Φ c = a₀ + κ * c ^ 2 := by
  intro c
  apply hΦ_analytic.eqOn_of_preconnected_of_frequently_eq
  exact DifferentiableOn.analyticOnNhd (by exact Differentiable.differentiableOn (by exact Differentiable.add (differentiable_const _) (Differentiable.mul (differentiable_const _) (differentiable_pow 2)))) (by simpa)
  exact isPreconnected_univ
  exact Set.mem_univ 0
  · rw [Metric.nhdsWithin_basis_ball.frequently_iff]
    intro ε ε_pos
    refine' ⟨Min.min ε 1 / 2, _, _⟩ <;> norm_num [abs_of_pos, ε_pos]
    · exact ⟨by linarith [min_le_left ε 1, min_le_right ε 1], by positivity⟩
    · convert heq (Min.min ε 1 / 2) (by rw [abs_of_nonneg (by positivity)]; linarith [min_le_left ε 1, min_le_right ε 1]) using 1; push_cast; ring
      norm_num
  · trivial

/-! ### Step 2: Riemann-Lebesgue -/

/-- Riemann-Lebesgue forces the constant a₀ and coefficient κ to be zero
when the Fourier cosine transform of an L¹ function equals a₀ − κy². -/
private theorem riemann_lebesgue_forces_zero
    (f : ℝ → ℂ) (hf_int : MeasureTheory.Integrable f)
    (a₀ κ : ℂ)
    (hΦ : ∀ y : ℝ,
      ∫ t : ℝ, f t * Real.cos (y * t) = a₀ - κ * y ^ 2) :
    a₀ = 0 ∧ κ = 0 := by
  have h_fourier_zero : Filter.Tendsto (fun y : ℝ => ∫ t, f t * (Real.cos (y * t) : ℂ)) Filter.atTop (nhds 0) := by
    have h_fourier_zero : Filter.Tendsto (fun y : ℝ => ∫ t, f t * Complex.exp (-Complex.I * y * t)) Filter.atTop (nhds 0) := by
      have := @Real.tendsto_integral_exp_smul_cocompact
      specialize this f
      simp_all +decide [mul_comm, mul_assoc, mul_left_comm, Complex.exp_neg, fourierChar]
      convert this.2.comp (show Filter.Tendsto (fun y : ℝ => y / (2 * Real.pi)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_mul_const (by positivity)) using 2; norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero]
      simp +decide [mul_comm, Complex.exp_neg, Circle.smul_def]
    have h_fourier_cos : ∀ y : ℝ, ∫ t, f t * (Real.cos (y * t) : ℂ) = (1 / 2) * (∫ t, f t * Complex.exp (-Complex.I * y * t)) + (1 / 2) * (∫ t, f t * Complex.exp (Complex.I * y * t)) := by
      intro y; rw [← mul_add, ← MeasureTheory.integral_add]; rw [← MeasureTheory.integral_const_mul]; congr; ext t; norm_num [Complex.cos]; ring
      · refine' hf_int.norm.mono' _ _
        · exact hf_int.1.mul (Continuous.aestronglyMeasurable (by continuity))
        · norm_num [Complex.norm_exp]
      · refine' hf_int.norm.mono' _ _
        · exact hf_int.1.mul (Continuous.aestronglyMeasurable (by continuity))
        · norm_num [Complex.norm_exp]
    have h_fourier_cos_zero : Filter.Tendsto (fun y : ℝ => ∫ t, f t * Complex.exp (Complex.I * y * t)) Filter.atTop (nhds 0) := by
      have := @Real.tendsto_integral_exp_smul_cocompact
      specialize this f
      simp_all +decide [mul_comm, fourierChar]
      convert this.1.comp (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const (show 0 < (2 * Real.pi)⁻¹ by positivity))) using 2; norm_num [Complex.exp_neg, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.ne']
      simp +decide [mul_comm, mul_assoc, mul_left_comm, Complex.exp_mul_I, Circle.smul_def]
    simpa only [h_fourier_cos, MulZeroClass.mul_zero, add_zero] using Filter.Tendsto.add (h_fourier_zero.const_mul (1 / 2 : ℂ)) (h_fourier_cos_zero.const_mul (1 / 2 : ℂ))
  by_cases hκ : κ = 0 <;> simp_all +decide [sub_eq_iff_eq_add]
  have := h_fourier_zero.sub_const a₀; simp_all +decide [sub_eq_iff_eq_add]
  have := this.norm; norm_num at this
  exact not_tendsto_atTop_of_tendsto_nhds this (Filter.Tendsto.const_mul_atTop (norm_pos_iff.mpr hκ) (by norm_num))

/-! ### Step 3: Fourier cosine injectivity -/

/-- Fourier cosine injectivity: if the Fourier cosine transform of a
continuous L¹ function supported on (0,∞) vanishes, then f = 0 on (0,∞). -/
private theorem fourier_cosine_injectivity
    (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f)
    (hf_support : ∀ t, t ≤ 0 → f t = 0)
    (hΦ : ∀ y : ℝ, ∫ t : ℝ, f t * Real.cos (y * t) = 0) :
    ∀ t : ℝ, 0 < t → f t = 0 := by
  have h_riemann_lebesgue : ∀ (f : ℝ → ℂ), Continuous f → MeasureTheory.Integrable f → (∀ y : ℝ, ∫ t : ℝ, f t * Complex.exp (Complex.I * y * t) = 0) → ∀ t : ℝ, f t = 0 := by
    intro f hf_cont hf_int hΦ t
    have := hf_int.fourier_inversion
    have h_fourier_zero : ∀ y : ℝ, FourierTransform.fourier f y = 0 := by
      simp_all +decide [mul_comm, FourierTransform.fourier]
      simp_all +decide [VectorFourier.fourierIntegral, fourierChar]
      simp_all +decide [mul_assoc, mul_comm, mul_left_comm, Complex.exp_neg, Circle.smul_def]
      intro y; specialize hΦ (-y * (Real.pi * 2)); simp_all +decide [mul_assoc, mul_comm, mul_left_comm, Complex.exp_neg]
    simp_all +decide [FourierTransformInv.fourierInv]
    simp_all +decide [VectorFourier.fourierIntegral]
    exact Eq.symm (this (by rw [show FourierTransform.fourier f = 0 from funext h_fourier_zero]; exact MeasureTheory.integrable_zero _ _ _) (hf_cont.continuousAt))
  contrapose! h_riemann_lebesgue
  refine' ⟨fun t => f t + f (-t), _, _, _, _⟩
  · exact hf_cont.add (hf_cont.comp (ContinuousNeg.continuous_neg))
  · exact hf_int.add (hf_int.comp_neg)
  · intro y
    have h_split : ∫ t : ℝ, (f t + f (-t)) * Complex.exp (Complex.I * y * t) = (∫ t : ℝ, f t * Complex.exp (Complex.I * y * t)) + (∫ t : ℝ, f (-t) * Complex.exp (Complex.I * y * t)) := by
      rw [← MeasureTheory.integral_add]; congr; ext; ring
      · refine' hf_int.norm.mono' _ _
        · exact hf_int.1.mul (Continuous.aestronglyMeasurable (by continuity))
        · norm_num [Complex.norm_exp]
      · refine' MeasureTheory.Integrable.mono' _ _ _
        refine' fun t => ‖f (-t)‖
        · exact MeasureTheory.Integrable.norm (hf_int.comp_neg)
        · exact MeasureTheory.AEStronglyMeasurable.mul (hf_cont.comp (ContinuousNeg.continuous_neg) |> Continuous.aestronglyMeasurable) (Continuous.aestronglyMeasurable (by continuity))
        · norm_num [Complex.norm_exp]
    have h_split : ∫ t : ℝ, f (-t) * Complex.exp (Complex.I * y * t) = ∫ t : ℝ, f t * Complex.exp (-Complex.I * y * t) := by
      rw [← MeasureTheory.integral_neg_eq_self]; norm_num
    have h_split : ∫ t : ℝ, f t * Complex.exp (Complex.I * y * t) + f t * Complex.exp (-Complex.I * y * t) = 2 * ∫ t : ℝ, f t * Real.cos (y * t) := by
      rw [← MeasureTheory.integral_const_mul]; congr; ext t; norm_num [Complex.cos]; ring
    rw [MeasureTheory.integral_add] at h_split
    · aesop
    · refine' hf_int.norm.mono' _ _
      · exact hf_int.1.mul (Continuous.aestronglyMeasurable (by continuity))
      · norm_num [Complex.norm_exp]
    · refine' hf_int.norm.mono' _ _
      · exact hf_int.1.mul (Continuous.aestronglyMeasurable (by continuity))
      · norm_num [Complex.norm_exp]
  · exact h_riemann_lebesgue.imp fun t ht => by simp +decide [ht.2, hf_support (-t) (neg_nonpos.mpr ht.1.le)]

/-! ### Step 4: Cosh-integral uniqueness

This pure analysis lemma says: if a continuous integrable function f
supported on (0,∞) satisfies ∫ f(t) cosh(ct) dt = C for all c ∈ (−1,1),
then f = 0.

Proof: By identity_theorem_extension (with κ = 0), the entire function
Φ(c) = ∫ f(t) cosh(ct) dt equals C everywhere. Setting c = iy gives
∫ f(t) cos(yt) dt = C. By riemann_lebesgue_forces_zero, C = 0. Then
fourier_cosine_injectivity gives f = 0. -/

/-
Cosh-integral uniqueness: if ∫ f(t) cosh(ct) dt = C for all c ∈ (−1,1)
and f is continuous, integrable, supported on (0,∞), with the cosh integral
defining an entire function, then f = 0 on (0,∞).
-/
private theorem cosh_integral_uniqueness
    (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f)
    (hf_support : ∀ t, t ≤ 0 → f t = 0)
    (C : ℂ)
    (hΦ_const : ∀ c : ℝ, |c| < 1 →
      ∫ t : ℝ, f t * Real.cosh (c * t) = C)
    -- Φ extends to an entire function:
    (Φ : ℂ → ℂ) (hΦ_analytic : AnalyticOnNhd ℂ Φ Set.univ)
    (hΦ_agrees_real : ∀ c : ℝ, Φ c = ∫ t : ℝ, f t * Real.cosh (c * t))
    -- Φ(iy) = ∫ f(t) cos(yt) dt:
    (hΦ_imaginary : ∀ y : ℝ,
      Φ (Complex.I * y) = ∫ t : ℝ, f t * Real.cos (y * t)) :
    ∀ t : ℝ, 0 < t → f t = 0 := by
  -- By the identity theorem for analytic functions, since Φ is entire and equals C on the real line (for |c| < 1), it must equal C everywhere.
  have hΦ_const_all : ∀ c : ℂ, Φ c = C := by
    convert @identity_theorem_extension Φ hΦ_analytic C 0 _ using 1;
    · norm_num;
    · grind;
  have hC_zero : C = 0 := by
    have h_int_zero : ∀ y : ℝ, ∫ t : ℝ, f t * Real.cos (y * t) = C := by
      exact fun y => hΦ_imaginary y ▸ hΦ_const_all _;
    have := riemann_lebesgue_forces_zero f hf_int C 0; aesop;
  exact fun t ht => fourier_cosine_injectivity f hf_cont hf_int hf_support ( fun y => by simpa [ hC_zero, hΦ_const_all ] using hΦ_imaginary y |> Eq.symm ) t ht

/-! ### Step 5: Analytical core — direct proof via cosh uniqueness -/

/-- **Sum–integral exchange for the Mellin series.**

The Fubini exchange: the β-parameterized vanishing of the tsum implies
the integral of the ZeroMellinSeries against the test function vanishes.

This is justified by the absolute summability and the Gaussian decay of
the pair-cosh-Gauss test function. The key identity is:

  ∑' ρ, a(ρ) · pairTestMellin(β, ρ) = ∫₀^∞ (ZeroMellinSeries a t) · g_β(t) dt

which holds by Fubini when both sides converge absolutely. Since the
left side is 0 (by hvanish), so is the right side. -/
private theorem fubini_pair_test_exchange
    (a : ℂ → ℂ)
    (_hsummable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    (hvanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1) :
    ∫ t in Set.Ioi (0 : ℝ),
      (ZeroMellinSeries a t) * (pair_cosh_gauss_test β t : ℂ) = 0 := by
  sorry

/-- **Mellin series vanishes from integral vanishing.**

If `∫ S(u) · g_β(u) du = 0` for all `β ∈ (0,1)`, then `S(t) = 0` for
all `t > 0`.  This uses the product factorization
`g_β = W · (cosh(c·) − 1)` and `cosh_integral_uniqueness`.

The function `W(t) = (cosh((1−π/3)t) − 1) · (ψ_gaussian t)²` satisfies
`W(t) > 0` for `t > 0` and `W(0) = 0`, so `S · W` extends continuously
to `[0,∞)` with `(S · W)(0) = 0`.  Super-Gaussian decay of W ensures
integrability of `S · W` (under the summability hypotheses on `a`).

After rewriting via the product factorization,
`∫ (S · W)(u) · cosh(cu) du = constant` for `c ∈ (−1,1)`.
`cosh_integral_uniqueness` then forces `S · W = 0`, hence `S = 0`. -/
private theorem mellin_series_vanishes_from_integral_vanishing
    (a : ℂ → ℂ)
    (h_int_vanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∫ t in Set.Ioi (0 : ℝ),
        (ZeroMellinSeries a t) * (pair_cosh_gauss_test β t : ℂ) = 0)
    (t : ℝ) (ht : 0 < t) :
    ZeroMellinSeries a t = 0 := by
  sorry

/-- **Analytical core of the β-totality argument.**

If the zero-side projection vanishes for every β ∈ (0,1), the underlying
Mellin series vanishes at every positive `t` (assuming summability at `t`).

Combines `fubini_pair_test_exchange` (sum–integral exchange) with
`mellin_series_vanishes_from_integral_vanishing` (product factorization
+ cosh uniqueness). -/
private theorem analytical_core
    (a : ℂ → ℂ)
    (hsummable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    (hvanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    (t : ℝ) (ht : 0 < t)
    (_hMS : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      a ρ.val * (t : ℂ) ^ (ρ.val - 1))) :
    ZeroMellinSeries a t = 0 := by
  exact mellin_series_vanishes_from_integral_vanishing a
    (fubini_pair_test_exchange a hsummable hvanish) t ht

/-! ### Main theorem -/

/-- **PairTestMellinBetaTotality holds.**

If every β-projection of the zero-side coefficient family vanishes, then
`ZeroMellinSeries a t = 0` for all `t > 0`. -/
theorem pairTestMellinBetaTotality_holds : PairTestMellinBetaTotality := by
  intro a hsummable hvanish t ht
  by_cases hMS : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
    a ρ.val * (t : ℂ) ^ (ρ.val - 1))
  · exact analytical_core a hsummable hvanish t ht hMS
  · exact tsum_eq_zero_of_not_summable hMS

-- Axiom audit: both sorry'd helpers are flagged.
#print axioms fubini_pair_test_exchange
#print axioms mellin_series_vanishes_from_integral_vanishing
-- The main theorem inherits sorry from the two helpers above.
#print axioms analytical_core
#print axioms pairTestMellinBetaTotality_holds

end ZeroOrthogonality
end WeilPositivity
end ZD

end
