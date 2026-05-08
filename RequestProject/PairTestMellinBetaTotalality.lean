import Mathlib
import RequestProject.WeilZeroOrthogonality
import RequestProject.FubiniPairTestSwap
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilPairTestMellinExtend
import RequestProject.ThetaTransport

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

/-! ### Step 0: Countability of nontrivial zero subtype -/

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
    · rw [Set.iUnion_subset_iff]
      intro _; exact Set.inter_subset_left
  rw [h_eq]
  exact Set.countable_iUnion (fun n =>
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (n : ℝ)).countable)

instance : Countable {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  nontrivialZeros_countable.to_subtype

/-! ### Step 1: Identity theorem for entire functions -/

/-- The identity theorem for entire functions: if an entire function equals a
polynomial on (−1, 1), it equals that polynomial everywhere.
(Here specialized to constant functions: κ = 0 gives Φ = a₀ everywhere.) -/
theorem identity_theorem_extension
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
      intro y
      -- Pointwise: f t * cos(yt) = (1/2)(f t * exp(-iyt) + f t * exp(iyt)).
      have h_pw : ∀ t : ℝ, f t * (Real.cos (y * t) : ℂ) =
          1/2 * (f t * Complex.exp (-Complex.I * y * t)) +
          1/2 * (f t * Complex.exp (Complex.I * y * t)) := by
        intro t
        have hcos_id : (Real.cos (y * t) : ℂ) =
            (Complex.exp (Complex.I * y * t) + Complex.exp (-Complex.I * y * t)) / 2 := by
          rw [show ((Real.cos (y * t) : ℝ) : ℂ) = Complex.cos ((y * t : ℂ)) from by
            push_cast; rfl]
          unfold Complex.cos
          push_cast; ring
        rw [hcos_id]; ring
      -- Integrability of f * exp(±iyt) via bounded multiplication.
      have h_norm_pos : ∀ t : ℝ, ‖Complex.exp (Complex.I * y * t)‖ ≤ 1 := fun t => by
        rw [Complex.norm_exp]
        have : (Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by simp
        rw [this]; simp
      have h_norm_neg : ∀ t : ℝ, ‖Complex.exp (-Complex.I * y * t)‖ ≤ 1 := fun t => by
        rw [Complex.norm_exp]
        have : (-Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by simp
        rw [this]; simp
      have h_meas_pos : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (Complex.I * y * t)) volume :=
        Continuous.aestronglyMeasurable (by continuity)
      have h_meas_neg : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (-Complex.I * y * t)) volume :=
        Continuous.aestronglyMeasurable (by continuity)
      have h_int_pos : Integrable
          (fun t : ℝ => f t * Complex.exp (Complex.I * y * t)) volume :=
        hf_int.mul_bdd h_meas_pos (Filter.Eventually.of_forall h_norm_pos)
      have h_int_neg : Integrable
          (fun t : ℝ => f t * Complex.exp (-Complex.I * y * t)) volume :=
        hf_int.mul_bdd h_meas_neg (Filter.Eventually.of_forall h_norm_neg)
      -- Now compute the integral.
      have h_lhs_eq : (fun t : ℝ => f t * (Real.cos (y * t) : ℂ)) =
          (fun t : ℝ =>
            1/2 * (f t * Complex.exp (-Complex.I * y * t)) +
            1/2 * (f t * Complex.exp (Complex.I * y * t))) := funext h_pw
      rw [h_lhs_eq]
      rw [MeasureTheory.integral_add
        (h_int_neg.const_mul (1/2)) (h_int_pos.const_mul (1/2))]
      rw [show (∫ a : ℝ, (1/2 : ℂ) * (f a * Complex.exp (-Complex.I * y * a))) =
          (1/2 : ℂ) * ∫ t : ℝ, f t * Complex.exp (-Complex.I * y * t) from
        MeasureTheory.integral_const_mul (1/2) _]
      rw [show (∫ a : ℝ, (1/2 : ℂ) * (f a * Complex.exp (Complex.I * y * a))) =
          (1/2 : ℂ) * ∫ t : ℝ, f t * Complex.exp (Complex.I * y * t) from
        MeasureTheory.integral_const_mul (1/2) _]
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
      intro y
      rw [Real.fourier_real_eq_integral_exp_smul f y]
      have hΦ_at := hΦ (-2 * Real.pi * y)
      push_cast at hΦ_at
      rw [show (fun v : ℝ =>
            Complex.exp (((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I) • f v) =
          (fun v : ℝ => f v * Complex.exp (Complex.I * (-2 * (Real.pi : ℂ) * (y : ℂ)) * v)) from ?_]
      · exact hΦ_at
      · funext v
        rw [smul_eq_mul]
        push_cast
        rw [mul_comm (Complex.exp _) (f v)]
        congr 1
        ring
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
      -- f t * (exp(iyt) + exp(-iyt)) = 2 * f t * cos(yt)
      have h_pw : ∀ t : ℝ, f t * Complex.exp (Complex.I * y * t) +
          f t * Complex.exp (-Complex.I * y * t) =
          2 * (f t * (Real.cos (y * t) : ℂ)) := by
        intro t
        have hcos_id : (Real.cos (y * t) : ℂ) =
            (Complex.exp (Complex.I * y * t) + Complex.exp (-Complex.I * y * t)) / 2 := by
          rw [show ((Real.cos (y * t) : ℝ) : ℂ) = Complex.cos ((y * t : ℂ)) from by
            push_cast; rfl]
          unfold Complex.cos
          push_cast; ring
        rw [hcos_id]; ring
      have h_norm_pos : ∀ t : ℝ, ‖Complex.exp (Complex.I * y * t)‖ ≤ 1 := fun t => by
        rw [Complex.norm_exp]
        have : (Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by simp
        rw [this]; simp
      have h_norm_neg : ∀ t : ℝ, ‖Complex.exp (-Complex.I * y * t)‖ ≤ 1 := fun t => by
        rw [Complex.norm_exp]
        have : (-Complex.I * (y : ℂ) * (t : ℂ)).re = 0 := by simp
        rw [this]; simp
      have h_meas_pos : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (Complex.I * y * t)) volume :=
        Continuous.aestronglyMeasurable (by continuity)
      have h_meas_neg : AEStronglyMeasurable
          (fun t : ℝ => Complex.exp (-Complex.I * y * t)) volume :=
        Continuous.aestronglyMeasurable (by continuity)
      have h_int_pos : Integrable
          (fun t : ℝ => f t * Complex.exp (Complex.I * y * t)) volume :=
        hf_int.mul_bdd h_meas_pos (Filter.Eventually.of_forall h_norm_pos)
      have h_int_neg : Integrable
          (fun t : ℝ => f t * Complex.exp (-Complex.I * y * t)) volume :=
        hf_int.mul_bdd h_meas_neg (Filter.Eventually.of_forall h_norm_neg)
      rw [show (fun t : ℝ => f t * Complex.exp (Complex.I * y * t) +
              f t * Complex.exp (-Complex.I * y * t)) =
          (fun t : ℝ => 2 * (f t * (Real.cos (y * t) : ℂ))) from funext h_pw]
      rw [show (∫ t : ℝ, (2 : ℂ) * (f t * (Real.cos (y * t) : ℂ))) =
          (2 : ℂ) * ∫ t : ℝ, f t * (Real.cos (y * t) : ℂ) from
        MeasureTheory.integral_const_mul 2 _]
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

/-! ### Step 4.5: Continuity of `ZeroMellinSeries` on `(0, ∞)`

Under absolute summability of `‖a ρ‖`, the tsum `ZeroMellinSeries a t` converges
locally uniformly on compact subsets of `(0, ∞)` (Weierstrass M-test) and hence
defines a continuous function on `(0, ∞)`. -/

private theorem zeroMellinSeries_continuousOn_Ioi
    (a : ℂ → ℂ)
    (h_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖)) :
    ContinuousOn (ZeroMellinSeries a) (Set.Ioi (0 : ℝ)) := by
  intro t₀ ht₀
  apply ContinuousAt.continuousWithinAt
  have ht₀_pos : (0 : ℝ) < t₀ := ht₀
  set δ : ℝ := t₀ / 2 with hδ_def
  set M : ℝ := 2 * t₀ + 1 with hM_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_lt_t₀ : δ < t₀ := by rw [hδ_def]; linarith
  have ht₀_lt_M : t₀ < M := by rw [hM_def]; linarith
  set C : ℝ := δ⁻¹ + 1 with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  have hu_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖ * C) := h_summable.mul_right C
  -- Continuity on the compact interval [δ, M].
  have h_cont_on : ContinuousOn
      (fun t : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * (t : ℂ)^(ρ.val - 1)) (Set.Icc δ M) := by
    apply continuousOn_tsum
    · intro ρ
      apply ContinuousOn.mul continuousOn_const
      intro t ⟨ht_lo, _⟩
      apply ContinuousAt.continuousWithinAt
      have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hδ_pos ht_lo
      have h_slit : (t : ℂ) ∈ Complex.slitPlane := by left; exact_mod_cast ht_pos
      exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const h_slit
    · exact hu_summable
    · intro ρ t ⟨ht_lo, _⟩
      have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hδ_pos ht_lo
      have ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      have h_re_eq : (ρ.val - 1).re = ρ.val.re - 1 := by simp
      rw [h_re_eq]
      have h_pow_bd : t^(ρ.val.re - 1) ≤ C := by
        rw [hC_def]
        rcases le_or_gt t 1 with ht1 | ht1
        · have h1 : t^(ρ.val.re - 1) ≤ t^((-1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge ht_pos ht1 (by linarith)
          have h2 : t^((-1 : ℝ)) = t⁻¹ := Real.rpow_neg_one _
          have h3 : t⁻¹ ≤ δ⁻¹ := by
            rw [inv_le_inv₀ ht_pos hδ_pos]
            exact ht_lo
          have h_inv_nn : (0 : ℝ) ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ_pos)
          calc t^(ρ.val.re - 1)
              ≤ t^((-1 : ℝ)) := h1
            _ = t⁻¹ := h2
            _ ≤ δ⁻¹ := h3
            _ ≤ δ⁻¹ + 1 := by linarith
        · have h1 : t^(ρ.val.re - 1) ≤ t^(0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt ht1) (by linarith)
          have h2 : t^(0 : ℝ) = 1 := Real.rpow_zero _
          have h_inv_nn : (0 : ℝ) ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ_pos)
          calc t^(ρ.val.re - 1)
              ≤ t^(0 : ℝ) := h1
            _ = 1 := h2
            _ ≤ δ⁻¹ + 1 := by linarith
      have h_a_nn : (0 : ℝ) ≤ ‖a ρ.val‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_left h_pow_bd h_a_nn
  -- t₀ ∈ interior of [δ, M], hence Icc ∈ nhds t₀.
  have h_nhd : Set.Icc δ M ∈ nhds t₀ := by
    have h_open : IsOpen (Set.Ioo δ M) := isOpen_Ioo
    have h_t₀_mem : t₀ ∈ Set.Ioo δ M := ⟨hδ_lt_t₀, ht₀_lt_M⟩
    exact Filter.mem_of_superset (h_open.mem_nhds h_t₀_mem) Set.Ioo_subset_Icc_self
  -- ZeroMellinSeries a = the lambda by definition.
  show ContinuousAt (fun t : ℝ => ZeroMellinSeries a t) t₀
  have h_eq : (fun t : ℝ => ZeroMellinSeries a t) =
      (fun t : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * (t : ℂ)^(ρ.val - 1)) := by
    funext t; rfl
  rw [h_eq]
  exact h_cont_on.continuousAt h_nhd

/-! ### Step 4.6: Norm bounds for `ZeroMellinSeries` -/

/-- For `0 < u ≤ 1`, the norm of `ZeroMellinSeries a u` is bounded by `S/u`,
where `S := ∑' ‖a ρ‖`. Uses `Re ρ - 1 ≤ 0` so that `u^(Re ρ - 1) ≤ u⁻¹`. -/
private theorem zeroMellinSeries_norm_le_div_of_le_one
    (a : ℂ → ℂ)
    (h_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖))
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖ZeroMellinSeries a u‖ ≤
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ‖a ρ.val‖) / u := by
  unfold ZeroMellinSeries
  have h_term_bd : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖a ρ.val * (u : ℂ) ^ (ρ.val - 1)‖ ≤ ‖a ρ.val‖ * (1/u) := by
    intro ρ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp only [sub_re, one_re]
    have ⟨_, hRe_lt, _⟩ := ρ.property
    have h_pow : u ^ (ρ.val.re - 1) ≤ u ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
    rw [Real.rpow_neg_one] at h_pow
    have h_nn : 0 ≤ ‖a ρ.val‖ := norm_nonneg _
    calc ‖a ρ.val‖ * u ^ (ρ.val.re - 1)
        ≤ ‖a ρ.val‖ * u⁻¹ := mul_le_mul_of_nonneg_left h_pow h_nn
      _ = ‖a ρ.val‖ * (1/u) := by rw [one_div]
  have h_inner_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val * (u : ℂ) ^ (ρ.val - 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_bd
      (h_summable.mul_right (1/u))
  refine (norm_tsum_le_tsum_norm h_inner_summable).trans ?_
  have h_main : ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖a ρ.val * (u : ℂ) ^ (ρ.val - 1)‖ ≤
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ‖a ρ.val‖ * (1/u) :=
    Summable.tsum_le_tsum h_term_bd h_inner_summable (h_summable.mul_right (1/u))
  refine h_main.trans (le_of_eq ?_)
  rw [tsum_mul_right, mul_one_div]

/-- For `u ≥ 1`, the norm of `ZeroMellinSeries a u` is bounded by
`S := ∑' ‖a ρ‖`. Uses `Re ρ - 1 ≤ 0` so that `u^(Re ρ - 1) ≤ 1` when `u ≥ 1`. -/
private theorem zeroMellinSeries_norm_le_const_of_one_le
    (a : ℂ → ℂ)
    (h_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖))
    (u : ℝ) (hu : 1 ≤ u) :
    ‖ZeroMellinSeries a u‖ ≤
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ‖a ρ.val‖) := by
  have hu_pos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  unfold ZeroMellinSeries
  have h_term_bd : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖a ρ.val * (u : ℂ) ^ (ρ.val - 1)‖ ≤ ‖a ρ.val‖ := by
    intro ρ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
    simp only [sub_re, one_re]
    have ⟨_, hRe_lt, _⟩ := ρ.property
    have h_pow : u ^ (ρ.val.re - 1) ≤ u ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    rw [Real.rpow_zero] at h_pow
    have h_nn : 0 ≤ ‖a ρ.val‖ := norm_nonneg _
    calc ‖a ρ.val‖ * u ^ (ρ.val.re - 1)
        ≤ ‖a ρ.val‖ * 1 := mul_le_mul_of_nonneg_left h_pow h_nn
      _ = ‖a ρ.val‖ := mul_one _
  have h_inner_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val * (u : ℂ) ^ (ρ.val - 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_bd h_summable
  refine (norm_tsum_le_tsum_norm h_inner_summable).trans ?_
  exact Summable.tsum_le_tsum h_term_bd h_inner_summable h_summable

/-! ### Step 5: Final cosh-uniqueness step

Given `∫ ZeroMellinSeries a · g_β = 0` for all β ∈ (0,1), the cosh-decomposition
`g_β = (h_pure/2) · (cosh(c·) - 1)` with `c = 2β-1 ∈ (-1,1)` and
`h_pure(t) = 4 sinh²((1/2-π/6)t) · ψ²(t)` reduces the conclusion to
`cosh_integral_uniqueness` applied to `ZeroMellinSeries a · h_pure`. -/

/-- **Mellin series vanishes from integral vanishing.**

If `∫ S(u) · g_β(u) du = 0` for all `β ∈ (0,1)` and the zero coefficients are
absolutely summable, then `S(t) = 0` for all `t > 0`.

This uses the product factorization
`g_β = (h_pure / 2) · (cosh(c·) − 1)` with `c = 2β-1 ∈ (-1,1)` and
`h_pure(t) := 4 · sinh²((1/2 - π/6) t) · ψ_gaussian(t)²`, then applies
`cosh_integral_uniqueness` to `f := ZeroMellinSeries a · h_pure` (extended
by 0 on `(-∞, 0]`).  Since `h_pure(t) > 0` for `t > 0`, the conclusion
`ZeroMellinSeries a · h_pure = 0` on `(0,∞)` gives the result.

Discharging this proof requires:
* continuity of `ZeroMellinSeries a` on `(0,∞)` (uniform convergence on
  compacts under absolute summability of `‖a ρ‖`);
* integrability of `ZeroMellinSeries a · h_pure` on `(0,∞)` and ℝ-extension;
* the entire-extension `Φ : ℂ → ℂ` of `c ↦ ∫ (ZeroMellinSeries a · h_pure)(t) ·
  cosh(ct) dt` (differentiation under the integral via Gaussian decay).

These are routine analytic infrastructure pieces; left here as a focused
target. -/
private theorem mellin_series_vanishes_from_integral_vanishing
    (a : ℂ → ℂ)
    (h_summable_norm : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖a ρ.val‖))
    (h_int_vanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∫ t in Set.Ioi (0 : ℝ),
        (ZeroMellinSeries a t) * (pair_cosh_gauss_test β t : ℂ) = 0)
    (t : ℝ) (ht : 0 < t) :
    ZeroMellinSeries a t = 0 := by
  -- Architecture: define f := ZeroMellinSeries a · h_pure (extended by 0 on t ≤ 0)
  -- where h_pure(t) = 4 sinh²((1/2-π/6)t) · ψ²(t).
  -- For c = 2β - 1 ∈ (-1, 1), we'll show ∫ f cosh(ct) = ∫ f (constant in c).
  -- Then `cosh_integral_uniqueness` gives f = 0 on (0,∞), hence ZeroMellinSeries a t = 0.
  set α : ℝ := 1/2 - Real.pi/6 with hα_def
  set h_pure : ℝ → ℝ := fun u => 4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2 with hh_pure_def
  set f : ℝ → ℂ := fun u =>
    if 0 < u then ZeroMellinSeries a u * (h_pure u : ℂ) else 0 with hf_def
  -- Required infrastructure for `cosh_integral_uniqueness` (each piece is documented).
  -- Notation for the uniform `ℓ¹` bound on `‖a ρ‖`.
  set S : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ‖a ρ.val‖ with hS_def
  have hS_nn : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  -- Step (i): `h_pure =O[nhds 0] (· ^ 2)`.
  have h_h_pure_O_sq : (fun u : ℝ => h_pure u) =O[nhds 0] (fun u : ℝ => u^2) := by
    show (fun u : ℝ => 4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2) =O[nhds 0] _
    have h_sinh : (fun u : ℝ => Real.sinh (α * u)^2) =O[nhds 0] (fun u : ℝ => u^2) :=
      Contour.sinh_sq_mul_isBigO_sq_nhds_zero_real α
    have h_psi : (fun u : ℝ => (ψ_gaussian u)^2) =O[nhds 0] (fun _ : ℝ => (1 : ℝ)) :=
      Contour.psi_gaussian_sq_isBigO_one_nhds_zero_real
    have h1 : (fun u : ℝ => (4 : ℝ) * Real.sinh (α * u)^2) =O[nhds 0]
        (fun u : ℝ => u^2) := h_sinh.const_mul_left 4
    have h_prod := h1.mul h_psi
    have h_simp : (fun u : ℝ => u^2 * (1 : ℝ)) = (fun u : ℝ => u^2) := by
      funext u; ring
    rw [h_simp] at h_prod
    exact h_prod
  -- Step (ii): ZMS · h_pure → 0 as u → 0+.
  have h_zms_h_pure_tendsto_zero :
      Filter.Tendsto (fun u : ℝ => ZeroMellinSeries a u * (h_pure u : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- ZMS =O[nhdsWithin 0 (Ioi 0)] (1/u)
    have h_zms_O : (fun u : ℝ => ZeroMellinSeries a u) =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => (1/u : ℝ)) := by
      refine Asymptotics.IsBigO.of_bound S ?_
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Set.Ioo 0 1, ?_, ?_⟩
      · rw [mem_nhdsWithin]
        exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
          fun x ⟨hx1, hx2⟩ => ⟨hx2, hx1⟩⟩
      · intros u hu
        have hu_pos : 0 < u := hu.1
        have hu_lt1 : u < 1 := hu.2
        have h := zeroMellinSeries_norm_le_div_of_le_one a h_summable_norm
          u hu_pos hu_lt1.le
        calc ‖ZeroMellinSeries a u‖
            ≤ S / u := h
          _ = S * (1/u) := by rw [div_eq_mul_one_div]
          _ = S * ‖(1/u : ℝ)‖ := by
              rw [Real.norm_of_nonneg (by positivity)]
    -- h_pure =O[nhdsWithin] u²
    have h_h_pure_O_sq' : (fun u : ℝ => h_pure u) =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => u^2) := h_h_pure_O_sq.mono nhdsWithin_le_nhds
    have h_h_pure_C : (fun u : ℝ => (h_pure u : ℂ)) =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => u^2) :=
      Complex.isBigO_ofReal_left.mpr h_h_pure_O_sq'
    -- Product: =O[..] (1/u · u²) = O[..] u
    have h_mul := h_zms_O.mul h_h_pure_C
    have h_eq : (fun u : ℝ => (1/u : ℝ) * u^2) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => u) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.Ioi 0, self_mem_nhdsWithin, ?_⟩
      intros u hu
      have hu_pos : (0 : ℝ) < u := hu
      field_simp
    have h_prod_O := h_mul.trans h_eq.isBigO
    have h_id_tendsto : Filter.Tendsto (fun u : ℝ => u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Filter.Tendsto (fun u : ℝ => u) (nhds 0) (nhds 0) := Filter.tendsto_id
      exact h.mono_left nhdsWithin_le_nhds
    exact h_prod_O.trans_tendsto h_id_tendsto
  -- Step (iii): ZMS · h_pure is continuous on Ioi 0.
  have h_zms_cont : ContinuousOn (ZeroMellinSeries a) (Set.Ioi (0 : ℝ)) :=
    zeroMellinSeries_continuousOn_Ioi a h_summable_norm
  have h_h_pure_cont : Continuous (fun u : ℝ => (h_pure u : ℂ)) := by
    have h_real : Continuous (fun u : ℝ => h_pure u) := by
      show Continuous (fun u : ℝ => 4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2)
      unfold ψ_gaussian
      fun_prop
    exact Complex.continuous_ofReal.comp h_real
  have h_prod_contOn : ContinuousOn
      (fun u : ℝ => ZeroMellinSeries a u * (h_pure u : ℂ)) (Set.Ioi (0 : ℝ)) :=
    h_zms_cont.mul h_h_pure_cont.continuousOn
  -- Now assemble continuity of f.
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro u
    rcases lt_trichotomy u 0 with hu | hu | hu
    · -- u < 0: f is locally 0
      have hmem : ∀ᶠ x in nhds u, x < 0 := IsOpen.mem_nhds isOpen_Iio hu
      refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) u).congr ?_
      filter_upwards [hmem] with x hx
      simp [f, hf_def, not_lt.mpr (le_of_lt hx)]
    · -- u = 0
      subst hu
      have h_val : (if 0 < (0 : ℝ) then ZeroMellinSeries a 0 * (h_pure 0 : ℂ)
        else (0 : ℂ)) = 0 := by simp
      rw [ContinuousAt]
      show Filter.Tendsto f (nhds 0) (nhds (f 0))
      have hf0 : f 0 = 0 := by simp [f, hf_def]
      rw [hf0]
      rw [Metric.tendsto_nhds]
      intro ε εpos
      rw [Metric.tendsto_nhdsWithin_nhds] at h_zms_h_pure_tendsto_zero
      obtain ⟨δ, δpos, hδ⟩ :=
        h_zms_h_pure_tendsto_zero ε εpos
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Metric.ball 0 δ, Metric.ball_mem_nhds 0 δpos, ?_⟩
      intros x hx
      by_cases hxpos : 0 < x
      · have hd : dist x 0 < δ := by simpa using hx
        have hgx := hδ hxpos hd
        show dist (f x) 0 < ε
        simp only [f, hf_def, hxpos, if_true]
        simpa [dist_eq_norm] using hgx
      · show dist (f x) 0 < ε
        simp [f, hf_def, hxpos, εpos]
    · -- u > 0
      have h_open : Set.Ioi (0 : ℝ) ∈ nhds u := IsOpen.mem_nhds isOpen_Ioi hu
      have hg_at : ContinuousAt (fun u => ZeroMellinSeries a u * (h_pure u : ℂ)) u :=
        h_prod_contOn.continuousAt h_open
      refine hg_at.congr ?_
      filter_upwards [h_open] with x hx
      simp [f, hf_def, show (0 : ℝ) < x from hx]
  -- Step (iv): Pointwise norm bound `‖f(u)‖ ≤ 4·S·exp(α²)·exp(-u²)` for `u ≥ 1`.
  have h_f_decay : ∀ u : ℝ, 1 ≤ u →
      ‖f u‖ ≤ (4 * S * Real.exp (α^2)) * Real.exp (-u^2) := by
    intros u hu
    have hu_pos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
    have h_zms_le : ‖ZeroMellinSeries a u‖ ≤ S :=
      zeroMellinSeries_norm_le_const_of_one_le a h_summable_norm u hu
    have h_h_pure_nn : (0 : ℝ) ≤ h_pure u := by
      show 0 ≤ 4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2
      positivity
    have h_h_pure_le :
        h_pure u ≤ 4 * Real.exp (α^2) * Real.exp (-u^2) := by
      show 4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2 ≤ _
      have h_psi_sq : (ψ_gaussian u)^2 = Real.exp (-2 * u^2) := ψ_gaussian_sq_eq u
      rw [h_psi_sq]
      have h_sinh_sq_le : Real.sinh (α * u)^2 ≤ Real.cosh (α * u)^2 := by
        have h1 := Real.cosh_sq_sub_sinh_sq (α * u)
        nlinarith
      have h_dom := ZD.cosh_sq_gaussian_dominated α u
      calc 4 * Real.sinh (α * u)^2 * Real.exp (-2 * u^2)
          ≤ 4 * Real.cosh (α * u)^2 * Real.exp (-2 * u^2) := by
            have hexp : 0 ≤ Real.exp (-2 * u^2) := Real.exp_nonneg _
            nlinarith
        _ = 4 * (Real.cosh (α * u)^2 * Real.exp (-2 * u^2)) := by ring
        _ ≤ 4 * (Real.exp (α^2) * Real.exp (-u^2)) := by
            have h4 : (0 : ℝ) ≤ 4 := by norm_num
            exact mul_le_mul_of_nonneg_left h_dom h4
        _ = 4 * Real.exp (α^2) * Real.exp (-u^2) := by ring
    -- f u = ZMS u * h_pure u for u > 0.
    have h_fu_eq : f u = ZeroMellinSeries a u * (h_pure u : ℂ) := by
      simp [f, hf_def, hu_pos]
    rw [h_fu_eq]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h_h_pure_nn]
    calc ‖ZeroMellinSeries a u‖ * h_pure u
        ≤ S * h_pure u := by
          exact mul_le_mul_of_nonneg_right h_zms_le h_h_pure_nn
      _ ≤ S * (4 * Real.exp (α^2) * Real.exp (-u^2)) := by
          exact mul_le_mul_of_nonneg_left h_h_pure_le hS_nn
      _ = 4 * S * Real.exp (α^2) * Real.exp (-u^2) := by ring
  -- Step (v): integrability via the split [-, 1] ∪ [1, ∞).
  have hf_int : MeasureTheory.Integrable f := by
    rw [← MeasureTheory.integrableOn_univ]
    have h_univ : (Set.univ : Set ℝ) = Set.Iic 1 ∪ Set.Ici 1 := by ext; simp
    rw [h_univ]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · -- IntegrableOn f (Iic 1) via decomposition Iic 1 = Iic 0 ∪ Icc 0 1.
      have h_decomp : (Set.Iic 1 : Set ℝ) = Set.Iic 0 ∪ Set.Icc 0 1 := by
        ext x
        simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
        constructor
        · intro hx
          rcases lt_or_ge x 0 with h | h
          · exact Or.inl h.le
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h2⟩)
          · linarith
          · exact h2
      rw [h_decomp]
      refine MeasureTheory.IntegrableOn.union ?_ ?_
      · -- f = 0 on Iic 0.
        have hf_zero_le : ∀ u : ℝ, u ≤ 0 → f u = 0 := fun u hu => by
          simp [f, hf_def, not_lt.mpr hu]
        have hae : f =ᵐ[MeasureTheory.volume.restrict (Set.Iic 0)] 0 := by
          rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Iic]
          exact Filter.Eventually.of_forall hf_zero_le
        exact (MeasureTheory.integrable_zero ℝ ℂ
          (MeasureTheory.volume.restrict (Set.Iic 0))).congr hae.symm
      · -- f continuous on compact [0, 1].
        exact hf_cont.continuousOn.integrableOn_compact isCompact_Icc
    · -- IntegrableOn f (Ici 1) via Gaussian decay bound.
      have h_C_nn : 0 ≤ 4 * S * Real.exp (α^2) := by positivity
      have h_gauss : MeasureTheory.Integrable
          (fun u : ℝ => (4 * S * Real.exp (α^2)) * Real.exp (-u^2)) := by
        have h := (integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1)).const_mul (4 * S * Real.exp (α^2))
        have heq : (fun u : ℝ => (4 * S * Real.exp (α^2)) * Real.exp (-1 * u^2))
            = (fun u : ℝ => (4 * S * Real.exp (α^2)) * Real.exp (-u^2)) := by
          funext u; congr 2; ring
        rw [heq] at h; exact h
      have h_dom_on : MeasureTheory.IntegrableOn
          (fun u : ℝ => (4 * S * Real.exp (α^2)) * Real.exp (-u^2)) (Set.Ici 1) :=
        h_gauss.integrableOn
      have h_meas_f : MeasureTheory.AEStronglyMeasurable f
          (MeasureTheory.volume.restrict (Set.Ici 1)) :=
        hf_cont.aestronglyMeasurable.restrict
      show MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ici 1))
      refine MeasureTheory.Integrable.mono h_dom_on h_meas_f ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall (fun u hu => by
        rw [Real.norm_of_nonneg (mul_nonneg h_C_nn (Real.exp_nonneg _))]
        exact h_f_decay u hu)
  have hf_support : ∀ u, u ≤ 0 → f u = 0 := by
    intro u hu; simp [f, hf_def, not_lt.mpr hu]
  set K : ℂ := ∫ u, f u with hK_def
  -- Helper: integrability of `u ↦ f u * Complex.cosh (c · u)` for any complex c.
  -- Uses `f` Gaussian decay + `‖cosh(cu)‖ ≤ exp(‖c‖²/2 + u²/2)`.
  have hf_mul_cosh_complex_int : ∀ (c : ℂ),
      MeasureTheory.Integrable
        (fun u : ℝ => f u * Complex.cosh (c * (u : ℂ))) := by
    intro c
    have hg_bound : ∀ u : ℝ,
        ‖Complex.cosh (c * (u : ℂ))‖ ≤
          Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2) := by
      intro u
      have h1 : ‖Complex.cosh (c * (u : ℂ))‖ ≤ Real.exp ‖c * (u : ℂ)‖ :=
        ZD.norm_cosh_le_exp_norm _
      have h2 : ‖c * (u : ℂ)‖ = ‖c‖ * |u| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [h2] at h1
      have h_amgm : ‖c‖ * |u| ≤ ‖c‖^2 / 2 + u^2 / 2 := by
        have h := sq_nonneg (‖c‖ - |u|)
        have habs_sq : |u|^2 = u^2 := sq_abs u
        nlinarith
      have h3 : Real.exp (‖c‖ * |u|) ≤ Real.exp (‖c‖^2 / 2 + u^2 / 2) :=
        Real.exp_le_exp.mpr h_amgm
      rw [Real.exp_add] at h3
      exact h1.trans h3
    have h_g_cont : Continuous
        (fun u : ℝ => Complex.cosh (c * (u : ℂ))) := by
      have : Continuous (fun u : ℝ => c * (u : ℂ)) := by fun_prop
      exact Complex.continuous_cosh.comp this
    rw [← MeasureTheory.integrableOn_univ]
    rw [show (Set.univ : Set ℝ) = Set.Iic 1 ∪ Set.Ici 1 from by ext; simp]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · -- Iic 1
      have h_decomp : (Set.Iic 1 : Set ℝ) = Set.Iic 0 ∪ Set.Icc 0 1 := by
        ext x
        simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
        constructor
        · intro hx
          rcases lt_or_ge x 0 with h | h
          · exact Or.inl h.le
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h2⟩)
          · linarith
          · exact h2
      rw [h_decomp]
      refine MeasureTheory.IntegrableOn.union ?_ ?_
      · have hae : (fun u : ℝ => f u * Complex.cosh (c * (u : ℂ))) =ᵐ[
              MeasureTheory.volume.restrict (Set.Iic 0)] 0 := by
          rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Iic]
          refine Filter.Eventually.of_forall (fun u hu => ?_)
          simp [hf_support u hu]
        exact (MeasureTheory.integrable_zero ℝ ℂ
          (MeasureTheory.volume.restrict (Set.Iic 0))).congr hae.symm
      · exact (hf_cont.mul h_g_cont).continuousOn.integrableOn_compact isCompact_Icc
    · -- Ici 1: bound by C * exp(-u²/2)
      set C : ℝ := (4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2) with hC_def
      have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
      have h_dom_int : MeasureTheory.Integrable
          (fun u : ℝ => C * Real.exp (-(u^2 / 2))) := by
        have h := (integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1/2)).const_mul C
        have heq : (fun u : ℝ => C * Real.exp (-(1/2) * u^2))
            = (fun u : ℝ => C * Real.exp (-(u^2/2))) := by
          funext u; congr 2; ring
        rw [heq] at h; exact h
      have h_meas : MeasureTheory.AEStronglyMeasurable
          (fun u : ℝ => f u * Complex.cosh (c * (u : ℂ)))
          (MeasureTheory.volume.restrict (Set.Ici 1)) :=
        (hf_cont.mul h_g_cont).aestronglyMeasurable.restrict
      show MeasureTheory.Integrable (fun u : ℝ => f u * Complex.cosh (c * (u : ℂ)))
        (MeasureTheory.volume.restrict (Set.Ici 1))
      refine MeasureTheory.Integrable.mono h_dom_int.integrableOn h_meas ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have h_fu := h_f_decay u hu
      have h_gu := hg_bound u
      rw [norm_mul]
      have h_lhs : ‖f u‖ * ‖Complex.cosh (c * (u : ℂ))‖ ≤
          ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
            (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2)) :=
        mul_le_mul h_fu h_gu (norm_nonneg _) (by positivity)
      have h_rhs_eq : ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
            (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2)) =
          C * Real.exp (-(u^2/2)) := by
        have hexp_eq : Real.exp (-u^2) * Real.exp (u^2 / 2) = Real.exp (-(u^2/2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hC_def]
        calc ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
              (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2))
            = ((4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2)) *
                (Real.exp (-u^2) * Real.exp (u^2 / 2)) := by ring
          _ = ((4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2)) *
                Real.exp (-(u^2/2)) := by rw [hexp_eq]
      rw [h_rhs_eq] at h_lhs
      rw [Real.norm_of_nonneg (by positivity)]
      exact h_lhs
  -- Phase 3: hΦ_const_real (algebraic identity).
  have hΦ_const_real : ∀ c : ℝ, |c| < 1 →
      ∫ u : ℝ, f u * (Real.cosh (c * u) : ℂ) = K := by
    intros c hc_abs
    -- β = (c+1)/2 is in (0, 1)
    set β : ℝ := (c + 1) / 2 with hβ_def
    have hc_lt1 : c < 1 := (abs_lt.mp hc_abs).2
    have hc_gt_neg1 : -1 < c := (abs_lt.mp hc_abs).1
    have hβ_pos : 0 < β := by rw [hβ_def]; linarith
    have hβ_lt1 : β < 1 := by rw [hβ_def]; linarith
    have hβ_minus_half : β - 1/2 = c / 2 := by rw [hβ_def]; ring
    -- Real-form integrability via the complex helper.
    have h_int_fcosh : MeasureTheory.Integrable
        (fun u : ℝ => f u * (Real.cosh (c * u) : ℂ)) := by
      have h := hf_mul_cosh_complex_int (c : ℂ)
      have h_eq : (fun u : ℝ => f u * Complex.cosh ((c : ℂ) * (u : ℂ))) =
          (fun u : ℝ => f u * (Real.cosh (c * u) : ℂ)) := by
        funext u
        congr 1
        rw [show ((c : ℂ) * (u : ℂ)) = ((c * u : ℝ) : ℂ) from by push_cast; ring]
        exact (Complex.ofReal_cosh _).symm
      rw [h_eq] at h
      exact h
    -- Integrability of f · (cosh(c·) - 1) on ℝ.
    have h_int_diff : MeasureTheory.Integrable
        (fun u : ℝ => f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ)) := by
      have h_eq : (fun u : ℝ => f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ)) =
          (fun u : ℝ => f u * (Real.cosh (c * u) : ℂ) - f u) := by
        funext u; push_cast; ring
      rw [h_eq]
      exact h_int_fcosh.sub hf_int
    -- The pointwise identity on Ioi 0:
    -- 2 · ZMS u · pair_cosh_gauss_test β u = f u · (cosh(c u) - 1).
    have h_pointwise_Ioi : ∀ u : ℝ, 0 < u →
        (2 : ℂ) * (ZeroMellinSeries a u * (pair_cosh_gauss_test β u : ℂ)) =
          f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ) := by
      intros u hu
      have h_factor : pair_cosh_gauss_test β u =
          h_pure u * Real.sinh (c * u / 2)^2 := by
        rw [pair_cosh_gauss_test_sinh_factor β u]
        show 4 * Real.sinh ((1/2 - Real.pi/6) * u)^2 *
            Real.sinh ((β - 1/2) * u)^2 * (ψ_gaussian u)^2 =
            (4 * Real.sinh (α * u)^2 * (ψ_gaussian u)^2) * Real.sinh (c * u / 2)^2
        rw [hβ_minus_half]
        have h_arg : (c / 2) * u = c * u / 2 := by ring
        rw [h_arg]; ring
      have h_two_sinh_sq : 2 * Real.sinh (c * u / 2)^2 = Real.cosh (c * u) - 1 := by
        have h := Real.cosh_two_mul (c * u / 2)
        have h_arg : 2 * (c * u / 2) = c * u := by ring
        rw [h_arg] at h
        have h_sub := Real.cosh_sq_sub_sinh_sq (c * u / 2)
        linarith
      have h_fu : f u = ZeroMellinSeries a u * (h_pure u : ℂ) := by
        simp [f, hf_def, hu]
      rw [h_fu]
      have h_two_sinh_sq_C :
          (2 : ℂ) * ((Real.sinh (c * u / 2)^2 : ℝ) : ℂ) =
            ((Real.cosh (c * u) - 1 : ℝ) : ℂ) := by
        have := congrArg (fun x : ℝ => (x : ℂ)) h_two_sinh_sq
        push_cast at this ⊢
        linear_combination this
      calc (2 : ℂ) * (ZeroMellinSeries a u * (pair_cosh_gauss_test β u : ℂ))
          = (2 : ℂ) * (ZeroMellinSeries a u *
              ((h_pure u * Real.sinh (c * u / 2)^2 : ℝ) : ℂ)) := by
            rw [h_factor]
        _ = ZeroMellinSeries a u * ((h_pure u : ℂ)) *
              ((2 : ℂ) * ((Real.sinh (c * u / 2)^2 : ℝ) : ℂ)) := by
            push_cast; ring
        _ = ZeroMellinSeries a u * ((h_pure u : ℂ)) *
              ((Real.cosh (c * u) - 1 : ℝ) : ℂ) := by rw [h_two_sinh_sq_C]
    -- The integral over Ioi 0 of f · (cosh(c u) - 1) is 0.
    have h_int_Ioi_zero :
        ∫ u in Set.Ioi (0 : ℝ), f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ) = 0 := by
      have h_van := h_int_vanish β hβ_pos hβ_lt1
      have h_eq : ∫ u in Set.Ioi (0 : ℝ), f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ) =
          ∫ u in Set.Ioi (0 : ℝ),
            (2 : ℂ) * (ZeroMellinSeries a u * (pair_cosh_gauss_test β u : ℂ)) := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
        refine Filter.Eventually.of_forall (fun u hu => ?_)
        have hu_pos : (0 : ℝ) < u := hu
        exact (h_pointwise_Ioi u hu_pos).symm
      rw [h_eq]
      have h_pull : ∫ u in Set.Ioi (0 : ℝ),
            (2 : ℂ) * (ZeroMellinSeries a u * (pair_cosh_gauss_test β u : ℂ)) =
          (2 : ℂ) * ∫ u in Set.Ioi (0 : ℝ),
            ZeroMellinSeries a u * (pair_cosh_gauss_test β u : ℂ) :=
        MeasureTheory.integral_const_mul _ _
      rw [h_pull, h_van, mul_zero]
    -- ℝ-integral equals Ioi 0-integral since f · (cosh - 1) vanishes outside Ioi 0.
    have h_int_R_diff_zero :
        ∫ u : ℝ, f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ) = 0 := by
      have h_compl : ∀ u, u ∉ Set.Ioi (0 : ℝ) →
          f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ) = 0 := fun u hu => by
        have hu_le : u ≤ 0 := not_lt.mp hu
        simp [hf_support u hu_le]
      have h_eq := MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := MeasureTheory.volume)
        (f := fun u : ℝ => f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ))
        (s := Set.Ioi (0 : ℝ)) h_compl
      rw [← h_eq, h_int_Ioi_zero]
    -- Now ∫ f · cosh = ∫ f · (cosh - 1) + ∫ f = 0 + K = K.
    have h_split : ∫ u : ℝ, f u * (Real.cosh (c * u) : ℂ) =
        (∫ u : ℝ, f u * ((Real.cosh (c * u) - 1 : ℝ) : ℂ)) + ∫ u : ℝ, f u := by
      rw [← MeasureTheory.integral_add h_int_diff hf_int]
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun u => ?_)
      push_cast; ring
    rw [h_split, h_int_R_diff_zero, zero_add]
  set Φ : ℂ → ℂ := fun c => ∫ u : ℝ, f u * Complex.cosh (c * (u : ℂ)) with hΦ_def
  -- Helper: for any complex c, the integrability of `f u · u · sinh(c · u)` on ℝ.
  have hf_mul_u_sinh_int : ∀ (c : ℂ), MeasureTheory.Integrable
      (fun u : ℝ => f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ)))) := by
    intro c
    have hg_bound : ∀ u : ℝ,
        ‖(u : ℂ) * Complex.sinh (c * (u : ℂ))‖ ≤
          |u| * (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2)) := by
      intro u
      have h_sinh_le : ‖Complex.sinh (c * (u : ℂ))‖ ≤ Real.exp ‖c * (u : ℂ)‖ :=
        ZD.norm_sinh_le_exp_norm _
      have h_norm_mul : ‖c * (u : ℂ)‖ = ‖c‖ * |u| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [h_norm_mul] at h_sinh_le
      have h_amgm : ‖c‖ * |u| ≤ ‖c‖^2 / 2 + u^2 / 2 := by
        have h := sq_nonneg (‖c‖ - |u|)
        have habs_sq : |u|^2 = u^2 := sq_abs u
        nlinarith
      have h_exp_le : Real.exp (‖c‖ * |u|) ≤ Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2) := by
        have h := Real.exp_le_exp.mpr h_amgm
        rw [Real.exp_add] at h
        exact h
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h_combo := h_sinh_le.trans h_exp_le
      exact mul_le_mul_of_nonneg_left h_combo (abs_nonneg _)
    have h_g_cont : Continuous
        (fun u : ℝ => (u : ℂ) * Complex.sinh (c * (u : ℂ))) := by
      have h1 : Continuous (fun u : ℝ => (u : ℂ)) := Complex.continuous_ofReal
      have h2 : Continuous (fun u : ℝ => c * (u : ℂ)) := by fun_prop
      exact h1.mul (Complex.continuous_sinh.comp h2)
    rw [← MeasureTheory.integrableOn_univ]
    rw [show (Set.univ : Set ℝ) = Set.Iic 1 ∪ Set.Ici 1 from by ext; simp]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · -- Iic 1 split
      have h_decomp : (Set.Iic 1 : Set ℝ) = Set.Iic 0 ∪ Set.Icc 0 1 := by
        ext x
        simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
        constructor
        · intro hx
          rcases lt_or_ge x 0 with h | h
          · exact Or.inl h.le
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h2⟩)
          · linarith
          · exact h2
      rw [h_decomp]
      refine MeasureTheory.IntegrableOn.union ?_ ?_
      · have hae : (fun u : ℝ => f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ)))) =ᵐ[
              MeasureTheory.volume.restrict (Set.Iic 0)] 0 := by
          rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Iic]
          refine Filter.Eventually.of_forall (fun u hu => ?_)
          simp [hf_support u hu]
        exact (MeasureTheory.integrable_zero ℝ ℂ
          (MeasureTheory.volume.restrict (Set.Iic 0))).congr hae.symm
      · exact (hf_cont.mul h_g_cont).continuousOn.integrableOn_compact isCompact_Icc
    · -- Ici 1: bound by C · |u| · exp(-u²/2). |u| · exp(-u²/2) integrable.
      set C : ℝ := (4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2) with hC_def
      have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
      -- |u| · exp(-u²/2) integrable
      have h_int_u_exp : MeasureTheory.Integrable
          (fun u : ℝ => |u| * Real.exp (-(u^2 / 2))) := by
        have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := (2 : ℝ))
          (by norm_num : (0:ℝ) < 1/2) (by norm_num : (-1 : ℝ) < 2)
        have hexp_eq : ∀ u : ℝ, Real.exp (-(1/2) * u^2) = Real.exp (-(u^2/2)) := fun u => by
          congr 1; ring
        have h_pow : ∀ u : ℝ, u^(2 : ℝ) = u^2 := fun u => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have h_int_u_sq : MeasureTheory.Integrable
            (fun u : ℝ => u^2 * Real.exp (-(u^2/2))) := by
          have heq : (fun u : ℝ => u^(2:ℝ) * Real.exp (-(1/2) * u^2)) =
              (fun u : ℝ => u^2 * Real.exp (-(u^2/2))) := by
            funext u; rw [h_pow u, hexp_eq u]
          rw [heq] at h; exact h
        have h_int_one : MeasureTheory.Integrable
            (fun u : ℝ => Real.exp (-(u^2/2))) := by
          have h := integrable_exp_neg_mul_sq (b := (1/2 : ℝ))
            (by norm_num : (0:ℝ) < 1/2)
          have heq : (fun u : ℝ => Real.exp (-(1/2) * u^2)) =
              (fun u : ℝ => Real.exp (-(u^2/2))) := by funext u; rw [hexp_eq u]
          rw [heq] at h; exact h
        have h_int_sum : MeasureTheory.Integrable
            (fun u : ℝ => Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2))) :=
          h_int_one.add h_int_u_sq
        refine MeasureTheory.Integrable.mono h_int_sum ?_ ?_
        · fun_prop
        · refine Filter.Eventually.of_forall (fun u => ?_)
          rw [Real.norm_of_nonneg (by positivity)]
          have h_bound : |u| ≤ 1 + u^2 := by
            have h := sq_nonneg (|u| - 1)
            have h2 : |u|^2 = u^2 := sq_abs u
            nlinarith
          have h_step : |u| * Real.exp (-(u^2/2)) ≤
              (1 + u^2) * Real.exp (-(u^2/2)) :=
            mul_le_mul_of_nonneg_right h_bound (Real.exp_nonneg _)
          rw [show (1 + u^2) * Real.exp (-(u^2/2)) =
              Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2)) from by ring] at h_step
          refine h_step.trans ?_
          have h_nn_sum : 0 ≤ Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2)) := by
            positivity
          rw [Real.norm_of_nonneg h_nn_sum]
      have h_dom_int : MeasureTheory.Integrable
          (fun u : ℝ => C * (|u| * Real.exp (-(u^2 / 2)))) :=
        h_int_u_exp.const_mul C
      have h_meas : MeasureTheory.AEStronglyMeasurable
          (fun u : ℝ => f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ))))
          (MeasureTheory.volume.restrict (Set.Ici 1)) :=
        (hf_cont.mul h_g_cont).aestronglyMeasurable.restrict
      show MeasureTheory.Integrable
        (fun u : ℝ => f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ))))
        (MeasureTheory.volume.restrict (Set.Ici 1))
      refine MeasureTheory.Integrable.mono h_dom_int.integrableOn h_meas ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have h_fu := h_f_decay u hu
      have h_gu := hg_bound u
      rw [norm_mul]
      have h_lhs : ‖f u‖ * ‖(u : ℂ) * Complex.sinh (c * (u : ℂ))‖ ≤
          ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
            (|u| * (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2))) :=
        mul_le_mul h_fu h_gu (norm_nonneg _) (by positivity)
      have h_rhs_eq : ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
            (|u| * (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2))) =
          C * (|u| * Real.exp (-(u^2/2))) := by
        have hexp_eq : Real.exp (-u^2) * Real.exp (u^2 / 2) = Real.exp (-(u^2/2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hC_def]
        calc ((4 * S * Real.exp (α^2)) * Real.exp (-u^2)) *
              (|u| * (Real.exp (‖c‖^2 / 2) * Real.exp (u^2 / 2)))
            = ((4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2)) *
                (|u| * (Real.exp (-u^2) * Real.exp (u^2 / 2))) := by ring
          _ = ((4 * S * Real.exp (α^2)) * Real.exp (‖c‖^2 / 2)) *
                (|u| * Real.exp (-(u^2/2))) := by rw [hexp_eq]
      rw [h_rhs_eq] at h_lhs
      rw [Real.norm_of_nonneg (by positivity)]
      exact h_lhs
  -- Phase 4: hΦ_analytic via differentiation under the integral.
  have hΦ_analytic : AnalyticOnNhd ℂ Φ Set.univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    intros c₀ _
    refine DifferentiableAt.differentiableWithinAt ?_
    -- Pick neighborhood: ball around c₀ of radius 1.
    let s : Set ℂ := Metric.ball c₀ 1
    have hs_nhds : s ∈ nhds c₀ := Metric.ball_mem_nhds _ one_pos
    let R : ℝ := ‖c₀‖ + 1
    have hR_nn : 0 ≤ R := by show 0 ≤ ‖c₀‖ + 1; positivity
    have h_c_norm : ∀ c ∈ s, ‖c‖ ≤ R := by
      intros c hc
      have hc' : dist c c₀ < 1 := hc
      have h_dist : ‖c - c₀‖ < 1 := by simpa [dist_eq_norm] using hc'
      have h_tri : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := norm_le_norm_add_norm_sub' c c₀
      show ‖c‖ ≤ ‖c₀‖ + 1
      linarith
    -- Define bound: bound(u) = ‖f u‖ · |u| · exp(R · |u|).
    let bound : ℝ → ℝ := fun u => ‖f u‖ * |u| * Real.exp (R * |u|)
    have h_bound_nn : ∀ u, 0 ≤ bound u := fun u => by show 0 ≤ _; positivity
    have h_int_abs_u_exp : MeasureTheory.Integrable
        (fun u : ℝ => |u| * Real.exp (-(u^2 / 2))) := by
      have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := (2 : ℝ))
        (by norm_num : (0:ℝ) < 1/2) (by norm_num : (-1 : ℝ) < 2)
      have hexp_eq : ∀ u : ℝ, Real.exp (-(1/2) * u^2) = Real.exp (-(u^2/2)) := fun u => by
        congr 1; ring
      have h_pow : ∀ u : ℝ, u^(2 : ℝ) = u^2 := fun u => by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h_int_u_sq : MeasureTheory.Integrable
          (fun u : ℝ => u^2 * Real.exp (-(u^2/2))) := by
        have heq : (fun u : ℝ => u^(2:ℝ) * Real.exp (-(1/2) * u^2)) =
            (fun u : ℝ => u^2 * Real.exp (-(u^2/2))) := by
          funext u; rw [h_pow u, hexp_eq u]
        rw [heq] at h; exact h
      have h_int_one : MeasureTheory.Integrable
          (fun u : ℝ => Real.exp (-(u^2/2))) := by
        have h := integrable_exp_neg_mul_sq (b := (1/2 : ℝ))
          (by norm_num : (0:ℝ) < 1/2)
        have heq : (fun u : ℝ => Real.exp (-(1/2) * u^2)) =
            (fun u : ℝ => Real.exp (-(u^2/2))) := by funext u; rw [hexp_eq u]
        rw [heq] at h; exact h
      have h_int_sum : MeasureTheory.Integrable
          (fun u : ℝ => Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2))) :=
        h_int_one.add h_int_u_sq
      refine MeasureTheory.Integrable.mono h_int_sum ?_ ?_
      · fun_prop
      · refine Filter.Eventually.of_forall (fun u => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have h_bound : |u| ≤ 1 + u^2 := by
          have h := sq_nonneg (|u| - 1)
          have h2 : |u|^2 = u^2 := sq_abs u
          nlinarith
        have h_step : |u| * Real.exp (-(u^2/2)) ≤
            (1 + u^2) * Real.exp (-(u^2/2)) :=
          mul_le_mul_of_nonneg_right h_bound (Real.exp_nonneg _)
        rw [show (1 + u^2) * Real.exp (-(u^2/2)) =
            Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2)) from by ring] at h_step
        refine h_step.trans ?_
        have h_nn_sum : 0 ≤ Real.exp (-(u^2/2)) + u^2 * Real.exp (-(u^2/2)) := by
          positivity
        rw [Real.norm_of_nonneg h_nn_sum]
    have h_bound_int : MeasureTheory.Integrable bound := by
      show MeasureTheory.Integrable
        (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|))
      rw [← MeasureTheory.integrableOn_univ]
      rw [show (Set.univ : Set ℝ) = Set.Iic 1 ∪ Set.Ici 1 from by ext; simp]
      refine MeasureTheory.IntegrableOn.union ?_ ?_
      · -- Iic 1: split as Iic 0 ∪ Icc 0 1
        have h_decomp : (Set.Iic 1 : Set ℝ) = Set.Iic 0 ∪ Set.Icc 0 1 := by
          ext x
          simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
          constructor
          · intro hx
            rcases lt_or_ge x 0 with h | h
            · exact Or.inl h.le
            · exact Or.inr ⟨h, hx⟩
          · rintro (h | ⟨_, h2⟩)
            · linarith
            · exact h2
        rw [h_decomp]
        refine MeasureTheory.IntegrableOn.union ?_ ?_
        · -- f = 0 on Iic 0
          have hae :
              (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|)) =ᵐ[
                MeasureTheory.volume.restrict (Set.Iic 0)] 0 := by
            rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Iic]
            refine Filter.Eventually.of_forall (fun u hu => ?_)
            simp [hf_support u hu]
          exact (MeasureTheory.integrable_zero ℝ ℝ
            (MeasureTheory.volume.restrict (Set.Iic 0))).congr hae.symm
        · -- continuous on compact [0, 1]
          have h_cont : Continuous
              (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|)) := by
            have h1 : Continuous (fun u : ℝ => ‖f u‖) := hf_cont.norm
            have h3 : Continuous (fun u : ℝ => Real.exp (R * |u|)) := by
              have : Continuous (fun u : ℝ => R * |u|) :=
                continuous_const.mul continuous_abs
              exact Real.continuous_exp.comp this
            exact (h1.mul continuous_abs).mul h3
          exact h_cont.continuousOn.integrableOn_compact isCompact_Icc
      · -- Ici 1
        set C : ℝ := (4 * S * Real.exp (α^2)) * Real.exp (R^2 / 2) with hC_def
        have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
        have h_dom_int : MeasureTheory.Integrable
            (fun u : ℝ => C * (|u| * Real.exp (-(u^2 / 2)))) :=
          h_int_abs_u_exp.const_mul C
        have h_meas : MeasureTheory.AEStronglyMeasurable
            (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|))
            (MeasureTheory.volume.restrict (Set.Ici 1)) := by
          have h_cont : Continuous
              (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|)) := by
            have h1 : Continuous (fun u : ℝ => ‖f u‖) := hf_cont.norm
            have h3 : Continuous (fun u : ℝ => Real.exp (R * |u|)) := by
              have : Continuous (fun u : ℝ => R * |u|) :=
                continuous_const.mul continuous_abs
              exact Real.continuous_exp.comp this
            exact (h1.mul continuous_abs).mul h3
          exact h_cont.aestronglyMeasurable.restrict
        show MeasureTheory.Integrable
          (fun u : ℝ => ‖f u‖ * |u| * Real.exp (R * |u|))
          (MeasureTheory.volume.restrict (Set.Ici 1))
        refine MeasureTheory.Integrable.mono h_dom_int.integrableOn h_meas ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
        refine Filter.Eventually.of_forall (fun u hu => ?_)
        have h_fu := h_f_decay u hu
        have hu_nn : (0 : ℝ) ≤ u := le_trans zero_le_one hu
        have habs_u : |u| = u := abs_of_nonneg hu_nn
        have h_amgm : R * u - u^2 ≤ R^2 / 2 - u^2 / 2 := by
          have h := sq_nonneg (R - u)
          nlinarith
        have h_step1 : ‖f u‖ * |u| * Real.exp (R * |u|) ≤
            (4 * S * Real.exp (α^2) * Real.exp (-u^2)) * u * Real.exp (R * u) := by
          simp_rw [habs_u]
          have h_lhs : ‖f u‖ * u ≤
              (4 * S * Real.exp (α^2) * Real.exp (-u^2)) * u :=
            mul_le_mul_of_nonneg_right h_fu hu_nn
          exact mul_le_mul_of_nonneg_right h_lhs (Real.exp_nonneg _)
        have h_step2 :
            (4 * S * Real.exp (α^2) * Real.exp (-u^2)) * u * Real.exp (R * u) =
            (4 * S * Real.exp (α^2)) * u * Real.exp (R * u - u^2) := by
          have hexp_eq : Real.exp (-u^2) * Real.exp (R * u) =
              Real.exp (R * u - u^2) := by
            rw [← Real.exp_add]; congr 1; ring
          calc (4 * S * Real.exp (α^2) * Real.exp (-u^2)) * u * Real.exp (R * u)
              = (4 * S * Real.exp (α^2)) * u *
                  (Real.exp (-u^2) * Real.exp (R * u)) := by ring
            _ = (4 * S * Real.exp (α^2)) * u * Real.exp (R * u - u^2) := by
                rw [hexp_eq]
        have h_step3 : (4 * S * Real.exp (α^2)) * u * Real.exp (R * u - u^2) ≤
            C * (|u| * Real.exp (-(u^2 / 2))) := by
          have h_exp_le : Real.exp (R * u - u^2) ≤
              Real.exp (R^2 / 2 - u^2 / 2) := Real.exp_le_exp.mpr h_amgm
          have hu_nn_b : 0 ≤ (4 * S * Real.exp (α^2)) * u := by positivity
          have h_mul_le :
              (4 * S * Real.exp (α^2)) * u * Real.exp (R * u - u^2) ≤
              (4 * S * Real.exp (α^2)) * u * Real.exp (R^2 / 2 - u^2 / 2) :=
            mul_le_mul_of_nonneg_left h_exp_le hu_nn_b
          have h_eq_step : Real.exp (R^2 / 2 - u^2 / 2) =
              Real.exp (R^2 / 2) * Real.exp (-(u^2 / 2)) := by
            rw [← Real.exp_add]; ring_nf
          rw [h_eq_step] at h_mul_le
          rw [habs_u]
          have hgoal :
              (4 * S * Real.exp (α^2)) * u * Real.exp (R * u - u^2) ≤
              (4 * S * Real.exp (α^2)) * Real.exp (R^2 / 2) *
                (u * Real.exp (-(u^2 / 2))) := by
            have : (4 * S * Real.exp (α^2)) * u *
                (Real.exp (R^2 / 2) * Real.exp (-(u^2 / 2))) =
                (4 * S * Real.exp (α^2)) * Real.exp (R^2 / 2) *
                  (u * Real.exp (-(u^2 / 2))) := by ring
            linarith [h_mul_le, this]
          exact hgoal
        have h_combo := (h_step1.trans (le_of_eq h_step2)).trans h_step3
        have h_lhs_nn : (0 : ℝ) ≤ ‖f u‖ * |u| * Real.exp (R * |u|) := by positivity
        have h_rhs_nn : (0 : ℝ) ≤ C * (|u| * Real.exp (-(u^2 / 2))) := by positivity
        rw [Real.norm_of_nonneg h_lhs_nn, Real.norm_of_nonneg h_rhs_nn]
        exact h_combo
    have h_F_meas : ∀ᶠ c in nhds c₀, MeasureTheory.AEStronglyMeasurable
        (fun u => f u * Complex.cosh (c * (u : ℂ))) MeasureTheory.volume := by
      filter_upwards with c
      have h_g_cont : Continuous (fun u : ℝ => Complex.cosh (c * (u : ℂ))) := by
        have : Continuous (fun u : ℝ => c * (u : ℂ)) := by fun_prop
        exact Complex.continuous_cosh.comp this
      exact (hf_cont.mul h_g_cont).aestronglyMeasurable
    have h_F0_int : MeasureTheory.Integrable
        (fun u => f u * Complex.cosh (c₀ * (u : ℂ))) MeasureTheory.volume :=
      hf_mul_cosh_complex_int c₀
    have h_F'_meas : MeasureTheory.AEStronglyMeasurable
        (fun u => f u * ((u : ℂ) * Complex.sinh (c₀ * (u : ℂ))))
        MeasureTheory.volume := by
      have h_g_cont : Continuous
          (fun u : ℝ => (u : ℂ) * Complex.sinh (c₀ * (u : ℂ))) := by
        have h1 : Continuous (fun u : ℝ => (u : ℂ)) := Complex.continuous_ofReal
        have h2 : Continuous (fun u : ℝ => c₀ * (u : ℂ)) := by fun_prop
        exact h1.mul (Complex.continuous_sinh.comp h2)
      exact (hf_cont.mul h_g_cont).aestronglyMeasurable
    have h_bound_holds : ∀ᵐ u : ℝ, ∀ c ∈ s,
        ‖f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ)))‖ ≤ bound u := by
      refine Filter.Eventually.of_forall (fun u c hc => ?_)
      rw [norm_mul]
      have h_c_le_R : ‖c‖ ≤ R := h_c_norm c hc
      have h_sinh_le : ‖Complex.sinh (c * (u : ℂ))‖ ≤ Real.exp (R * |u|) := by
        have h := ZD.norm_sinh_le_exp_norm (c * (u : ℂ))
        have h_norm_eq : ‖c * (u : ℂ)‖ = ‖c‖ * |u| := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [h_norm_eq] at h
        refine h.trans (Real.exp_le_exp.mpr ?_)
        have habs_nn : 0 ≤ |u| := abs_nonneg _
        exact mul_le_mul_of_nonneg_right h_c_le_R habs_nn
      have h_norm_u : ‖(u : ℂ) * Complex.sinh (c * (u : ℂ))‖ ≤
          |u| * Real.exp (R * |u|) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left h_sinh_le (abs_nonneg _)
      show ‖f u‖ * ‖(u : ℂ) * Complex.sinh (c * (u : ℂ))‖ ≤
        ‖f u‖ * |u| * Real.exp (R * |u|)
      calc ‖f u‖ * ‖(u : ℂ) * Complex.sinh (c * (u : ℂ))‖
          ≤ ‖f u‖ * (|u| * Real.exp (R * |u|)) :=
            mul_le_mul_of_nonneg_left h_norm_u (norm_nonneg _)
        _ = ‖f u‖ * |u| * Real.exp (R * |u|) := by ring
    have h_diff : ∀ᵐ u : ℝ, ∀ c ∈ s,
        HasDerivAt (fun c : ℂ => f u * Complex.cosh (c * (u : ℂ)))
          (f u * ((u : ℂ) * Complex.sinh (c * (u : ℂ)))) c := by
      refine Filter.Eventually.of_forall (fun u c _ => ?_)
      have h1 : HasDerivAt (fun c : ℂ => c * (u : ℂ)) ((u : ℂ)) c := by
        have hh1 := hasDerivAt_id c
        have hh2 := hh1.mul_const ((u : ℂ))
        simpa using hh2
      have h2 := Complex.hasDerivAt_cosh (c * (u : ℂ))
      have h3 := h2.comp c h1
      have h4 := h3.const_mul (f u)
      convert h4 using 1
      ring
    have ⟨_, h_deriv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := s) (x₀ := c₀) (bound := bound) hs_nhds h_F_meas h_F0_int
      h_F'_meas h_bound_holds h_bound_int h_diff
    exact h_deriv.differentiableAt
  have hΦ_agrees_real : ∀ c : ℝ, Φ c = ∫ u : ℝ, f u * (Real.cosh (c * u) : ℂ) := by
    intro c
    show ∫ u : ℝ, f u * Complex.cosh ((c : ℂ) * (u : ℂ)) = _
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun u => ?_)
    show f u * Complex.cosh ((c : ℂ) * (u : ℂ)) = f u * ((Real.cosh (c * u) : ℝ) : ℂ)
    congr 1
    rw [show ((c : ℂ) * (u : ℂ)) = ((c * u : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cosh _).symm
  have hΦ_imaginary : ∀ y : ℝ,
      Φ (Complex.I * y) = ∫ u : ℝ, f u * (Real.cos (y * u) : ℂ) := by
    intro y
    show ∫ u : ℝ, f u * Complex.cosh ((Complex.I * (y : ℂ)) * (u : ℂ)) = _
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun u => ?_)
    show f u * Complex.cosh ((Complex.I * (y : ℂ)) * (u : ℂ)) =
      f u * ((Real.cos (y * u) : ℝ) : ℂ)
    congr 1
    rw [show ((Complex.I * (y : ℂ)) * (u : ℂ)) = ((y * u : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    rw [Complex.cosh_mul_I]
    exact (Complex.ofReal_cos _).symm
  have h_f_zero : ∀ u : ℝ, 0 < u → f u = 0 :=
    cosh_integral_uniqueness f hf_cont hf_int hf_support K hΦ_const_real Φ hΦ_analytic
      hΦ_agrees_real hΦ_imaginary
  -- Final: extract ZeroMellinSeries a t = 0 from f t = 0 and h_pure t > 0.
  have h_ft : f t = 0 := h_f_zero t ht
  have h_α_ne : α ≠ 0 := by
    rw [hα_def]; intro h
    have hπ : Real.pi = 3 := by linarith
    have h_pi_gt : 3.14 < Real.pi := Real.pi_gt_d2
    linarith
  have h_h_pure_pos : 0 < h_pure t := by
    rw [hh_pure_def]
    have h_sinh_pos : 0 < Real.sinh (α * t) ^ 2 := by
      have h_arg_ne : α * t ≠ 0 := mul_ne_zero h_α_ne (ne_of_gt ht)
      have h_sinh_ne : Real.sinh (α * t) ≠ 0 := Real.sinh_ne_zero.mpr h_arg_ne
      positivity
    have h_psi_pos : 0 < (ψ_gaussian t)^2 := by
      have h_psi_ne : ψ_gaussian t ≠ 0 := by
        unfold ψ_gaussian; exact ne_of_gt (Real.exp_pos _)
      positivity
    positivity
  have h_h_pure_ne : (h_pure t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h_h_pure_pos
  -- f t = ZeroMellinSeries a t * h_pure(t) since 0 < t.
  have h_ft_eq : f t = ZeroMellinSeries a t * (h_pure t : ℂ) := by
    simp [f, hf_def, ht]
  have h_prod_zero : ZeroMellinSeries a t * (h_pure t : ℂ) = 0 := h_ft_eq ▸ h_ft
  exact (mul_eq_zero.mp h_prod_zero).resolve_right h_h_pure_ne

/-! ### Main theorem -/

/-- **PairTestMellinBetaTotality holds.**

If every β-projection of the zero-side coefficient family vanishes, then
`ZeroMellinSeries a t = 0` for all `t > 0`. -/
theorem pairTestMellinBetaTotality_holds : PairTestMellinBetaTotality := by
  intro a h_summable_norm hsummable hvanish t ht
  -- Step 1: Module A gives ∫ ZeroMellinSeries · g_β = 0 for each β ∈ (0,1).
  have h_int_vanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∫ τ in Set.Ioi (0 : ℝ),
        ZeroMellinSeries a τ * (pair_cosh_gauss_test β τ : ℂ) = 0 := fun β hβ_pos hβ_lt =>
    FubiniPairTestSwap.integral_zero_of_tsum_zero a h_summable_norm hvanish hβ_pos hβ_lt
  -- Step 2: cosh-uniqueness chain to conclude ZeroMellinSeries a t = 0.
  -- ZeroMellinSeries · g_β = ZeroMellinSeries · h_pure(t) · sinh²((β-1/2)t)
  -- Setting c = 2β-1 ∈ (-1,1), this gives a function constant in c on (-1,1).
  -- cosh_integral_uniqueness then forces the function to vanish.
  exact mellin_series_vanishes_from_integral_vanishing a h_summable_norm h_int_vanish t ht

-- Axiom audit.
#print axioms mellin_series_vanishes_from_integral_vanishing
#print axioms pairTestMellinBetaTotality_holds

end ZeroOrthogonality
end WeilPositivity
end ZD

end
