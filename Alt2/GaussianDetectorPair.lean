import Mathlib
import RequestProject.GaussianClosedForm
import RequestProject.ZetaZeroDefs
import RequestProject.MellinPathToXi
import RequestProject.RiemannHypothesisBridge

/-!
# Gaussian-Paired Detector Observables

The project's cosh detectors live at shifts `π/6` and `1 − π/6`:
```
coshDetectorLeft  β t = cosh((β − π/6)·t)
coshDetectorRight β t = cosh((β − (1 − π/6))·t)
```
and their pair balance is the algebraic invariant `β = 1/2`.

The Gaussian observable `I_theta_of ψ_gaussian` from `GaussianClosedForm`
uses the **centered** cosh at shift `s − 1/2`, which does not see the π/6
pair structure. This file lifts the π/6 shifts into Gaussian-weighted
observables:
```
gaussianDetectorLeft  s = ∫ 2·cosh((s − π/6)·t)·ψ_gaussian(t) dt
gaussianDetectorRight s = ∫ 2·cosh((s − (1−π/6))·t)·ψ_gaussian(t) dt
```
Both have closed forms by the Gaussian cosh-moment identity
`cosh_gaussian_integral_Ioi`, and their pair difference vanishes iff
`s − 1/2` lies on a specific imaginary lattice — encoding the detector
balance point at `Re s = 1/2` in the Gaussian-weighted setting.
-/

open Real Complex MeasureTheory Set ZetaDefs

noncomputable section

namespace ZD

/-! ### Definitions -/

/-- **Left Gaussian detector observable.** `∫₀^∞ 2·cosh((s−π/6)·t)·ψ_gaussian(t) dt`. -/
noncomputable def gaussianDetectorLeft (s : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ),
    (2:ℂ) * Complex.cosh ((s - ((Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
      (ψ_gaussian t : ℂ)

/-- **Right Gaussian detector observable.**
`∫₀^∞ 2·cosh((s−(1−π/6))·t)·ψ_gaussian(t) dt`. -/
noncomputable def gaussianDetectorRight (s : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ),
    (2:ℂ) * Complex.cosh ((s - ((1 - Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
      (ψ_gaussian t : ℂ)

/-! ### Closed forms via the Gaussian cosh-moment identity -/

private lemma pi_half_eq_sqrt_pi' :
    (Real.pi : ℂ)^((1:ℂ)/2) = ((Real.sqrt Real.pi) : ℂ) := by
  rw [show ((1:ℂ)/2) = ((1/2 : ℝ) : ℂ) from by push_cast; ring]
  rw [← Complex.ofReal_cpow Real.pi_pos.le]
  rw [Real.sqrt_eq_rpow]

private lemma psi_gaussian_ofReal_eq' (t : ℝ) :
    (ψ_gaussian t : ℂ) = Complex.exp (-(t : ℂ)^2) := by
  unfold ψ_gaussian
  push_cast
  ring_nf

/-- **Closed form for the left Gaussian detector.** -/
theorem gaussianDetectorLeft_closed_form (s : ℂ) :
    gaussianDetectorLeft s =
      (Real.sqrt Real.pi : ℂ) *
        Complex.exp ((s - ((Real.pi/6 : ℝ) : ℂ))^2 / 4) := by
  unfold gaussianDetectorLeft
  have hinteg : ∀ t ∈ Ioi (0:ℝ),
      (2:ℂ) * Complex.cosh ((s - ((Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
        (ψ_gaussian t : ℂ) =
      (2:ℂ) * Complex.cosh ((s - ((Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
        Complex.exp (-(t : ℂ)^2) := by
    intro t _
    rw [psi_gaussian_ofReal_eq']
  rw [setIntegral_congr_fun measurableSet_Ioi hinteg]
  rw [cosh_gaussian_integral_Ioi (s - ((Real.pi/6 : ℝ) : ℂ))]
  rw [pi_half_eq_sqrt_pi']

/-- **Closed form for the right Gaussian detector.** -/
theorem gaussianDetectorRight_closed_form (s : ℂ) :
    gaussianDetectorRight s =
      (Real.sqrt Real.pi : ℂ) *
        Complex.exp ((s - ((1 - Real.pi/6 : ℝ) : ℂ))^2 / 4) := by
  unfold gaussianDetectorRight
  have hinteg : ∀ t ∈ Ioi (0:ℝ),
      (2:ℂ) * Complex.cosh ((s - ((1 - Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
        (ψ_gaussian t : ℂ) =
      (2:ℂ) * Complex.cosh ((s - ((1 - Real.pi/6 : ℝ) : ℂ)) * (t : ℂ)) *
        Complex.exp (-(t : ℂ)^2) := by
    intro t _
    rw [psi_gaussian_ofReal_eq']
  rw [setIntegral_congr_fun measurableSet_Ioi hinteg]
  rw [cosh_gaussian_integral_Ioi (s - ((1 - Real.pi/6 : ℝ) : ℂ))]
  rw [pi_half_eq_sqrt_pi']

/-! ### Pair difference

The detector pair's Gaussian-weighted difference factors through the
`(1 − π/3)·(2s − 1)` exponent structure, capturing the critical-line
balance point at `s − 1/2 = 0`. -/

/-- **Pair-difference closed form.** -/
theorem gaussianDetectorPair_diff (s : ℂ) :
    gaussianDetectorLeft s - gaussianDetectorRight s =
      (Real.sqrt Real.pi : ℂ) *
        (Complex.exp ((s - ((Real.pi/6 : ℝ) : ℂ))^2 / 4) -
          Complex.exp ((s - ((1 - Real.pi/6 : ℝ) : ℂ))^2 / 4)) := by
  rw [gaussianDetectorLeft_closed_form, gaussianDetectorRight_closed_form]
  ring

/-- **Pair-difference exponent identity.** The ratio of the two
exponents simplifies to `exp((1 − π/3)·(2s − 1) / 4)`. -/
theorem gaussianDetectorPair_ratio (s : ℂ) :
    Complex.exp ((s - ((Real.pi/6 : ℝ) : ℂ))^2 / 4) /
      Complex.exp ((s - ((1 - Real.pi/6 : ℝ) : ℂ))^2 / 4) =
    Complex.exp ((((1 - Real.pi/3 : ℝ) : ℂ)) * (2*s - 1) / 4) := by
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

#print axioms gaussianDetectorLeft_closed_form
#print axioms gaussianDetectorRight_closed_form
#print axioms gaussianDetectorPair_diff
#print axioms gaussianDetectorPair_ratio

/-! ### Gaussian-weighted pair defect — detector-pair framing for
imbalance detection

This section replaces single-cosh AED with a detector-pair defect, using
the π/6 and 1−π/6 shifts instead of the centered 1/2 shift. The
detector-pair difference `coshDetectorLeft β t − coshDetectorRight β t`
factors algebraically as `2·sinh((1/2−π/6)·t)·sinh((β−1/2)·t)`
(from `DoubleCoshKernelComparison.coshDetector_pair_diff_complex`).

The Gaussian-weighted squared pair-defect is then a non-negative
function of β that vanishes identically at β = 1/2 (because the
β-dependent sinh factor vanishes) and is strictly positive off the line. -/

/-- **Pointwise pair-detector difference squared.** By the pair-sinh
factorization: `(K_L − K_R)² = 4·sinh²((1/2−π/6)·t)·sinh²((β−1/2)·t)`. -/
noncomputable def pairDetectorSqDiff (β t : ℝ) : ℝ :=
  (coshDetectorLeft β t - coshDetectorRight β t)^2

/-- **Sinh-factored form of the pair-detector squared difference.** -/
theorem pairDetectorSqDiff_sinh_factor (β t : ℝ) :
    pairDetectorSqDiff β t =
      4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
          Real.sinh ((β - 1/2) * t)^2 := by
  unfold pairDetectorSqDiff coshDetectorLeft coshDetectorRight
  have h_add_sub : ∀ a b : ℝ,
      Real.cosh (a - b) - Real.cosh (a + b) =
        -(2 * Real.sinh a * Real.sinh b) := by
    intro a b
    rw [Real.cosh_sub, Real.cosh_add]; ring
  have key : Real.cosh ((β - Real.pi/6) * t) -
             Real.cosh ((β - (1 - Real.pi/6)) * t) =
             2 * Real.sinh ((1/2 - Real.pi/6) * t) *
                 Real.sinh ((β - 1/2) * t) := by
    have hrewL : (β - Real.pi/6) * t =
                 (β - 1/2) * t + (1/2 - Real.pi/6) * t := by ring
    have hrewR : (β - (1 - Real.pi/6)) * t =
                 (β - 1/2) * t - (1/2 - Real.pi/6) * t := by ring
    rw [hrewL, hrewR]
    have := h_add_sub ((β - 1/2) * t) ((1/2 - Real.pi/6) * t)
    linarith
  rw [key]; ring

/-- **Gaussian-weighted pair defect.** Integrates the squared
pair-detector difference against `ψ_gaussian²` on `(0, ∞)`. Vanishes at
β = 1/2, strictly positive off the critical line. -/
noncomputable def gaussianPairDefect (β : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), pairDetectorSqDiff β t * (ψ_gaussian t)^2

/-- **Pair-defect vanishes on the critical line.** At β = 1/2, the sinh
factor `sinh((β−1/2)·t) = 0` for all t, so the integrand is identically
zero. -/
theorem gaussianPairDefect_zero_on_line :
    gaussianPairDefect (1/2) = 0 := by
  unfold gaussianPairDefect
  have h : ∀ t : ℝ, pairDetectorSqDiff (1/2) t * (ψ_gaussian t)^2 = 0 := by
    intro t
    rw [pairDetectorSqDiff_sinh_factor]
    have : Real.sinh (((1:ℝ)/2 - 1/2) * t) = 0 := by
      have hzero : ((1:ℝ)/2 - 1/2) * t = 0 := by ring
      rw [hzero, Real.sinh_zero]
    rw [this]; ring
  simp_rw [h]
  simp

/-- **Pair-defect is non-negative** everywhere. -/
theorem gaussianPairDefect_nonneg (β : ℝ) :
    0 ≤ gaussianPairDefect β := by
  unfold gaussianPairDefect
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards with t using by
    rw [pairDetectorSqDiff_sinh_factor]
    exact mul_nonneg (by positivity) (sq_nonneg _)

/-! ### Forward-only RH closure using the pair defect

**No biconditionals here.** The forward implications chain:
- `gaussianPairDefect β = 0 → β = 1/2` (via positivity off-line + contrapositive)
- "pair defect vanishes at every zero" + cosh algebra → `ρ.re = 1/2`
- `no_offline_zeros_implies_rh` → `RiemannHypothesis`.

The *load-bearing* step is proving `gaussianPairDefect ρ.re = 0` at every
nontrivial zero unconditionally — that's the Stage-C-with-pair target. -/

/-- **Pair-defect off-line positivity.** For `β ≠ 1/2`, the pair defect
is strictly positive. Proof: both sinh factors are nonzero on `t > 0`
(since `π/6 ≠ 1/2` via `Real.pi_gt_three` and `β ≠ 1/2`), giving a
pointwise-positive integrand on Ioi 0; Gaussian weight makes it
integrable; integral-positivity via the support-of-nonneg
characterization. -/
theorem gaussianPairDefect_pos_offline
    {β : ℝ} (hβ : β ≠ 1/2) : 0 < gaussianPairDefect β := by
  unfold gaussianPairDefect
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hδ1 : ((1:ℝ)/2 - Real.pi/6) ≠ 0 := by
    intro h; linarith
  have hδ2 : β - (1:ℝ)/2 ≠ 0 := sub_ne_zero.mpr hβ
  -- Rewrite integrand via sinh factorization.
  have h_rewrite : ∀ t : ℝ,
      pairDetectorSqDiff β t * (ψ_gaussian t)^2 =
        4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 *
            Real.sinh ((β - 1/2) * t)^2 * (ψ_gaussian t)^2 := by
    intro t; rw [pairDetectorSqDiff_sinh_factor]
  simp_rw [h_rewrite]
  -- Integrability: integrand ≤ 4·exp(2(|δ1|+|δ2|)|t|)·exp(-2t²), Gaussian-dominated.
  set δ1 : ℝ := (1:ℝ)/2 - Real.pi/6
  set δ2 : ℝ := β - 1/2
  set C : ℝ := |δ1| + |δ2| with hC_def
  have hC_nn : 0 ≤ C := by positivity
  -- Convert (ψ_gaussian t)^2 to exp(-2t²).
  have h_psi_sq : ∀ t : ℝ, (ψ_gaussian t)^2 = Real.exp (-2 * t^2) := ψ_gaussian_sq_eq
  have h_integrand_eq : ∀ t : ℝ,
      4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2 =
      4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * Real.exp (-2 * t^2) := by
    intro t; rw [h_psi_sq]
  -- Integrability via dominated convergence by 4·e^(C²)·exp(-t²).
  have h_integrable :
      MeasureTheory.IntegrableOn
        (fun t => 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2)
        (Set.Ioi (0:ℝ)) := by
    apply MeasureTheory.Integrable.integrableOn
    have h_rewrite_int : (fun t : ℝ =>
        4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2) =
        (fun t : ℝ =>
          4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * Real.exp (-2 * t^2)) := by
      funext t; exact h_integrand_eq t
    rw [h_rewrite_int]
    apply MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => 4 * Real.exp (C^2) * Real.exp (-t^2))
    · have h_base : MeasureTheory.Integrable
          (fun x : ℝ => Real.exp (-x^2)) MeasureTheory.volume := by
        have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
        have heq : (fun x : ℝ => Real.exp (-1 * x^2)) =
                   (fun x : ℝ => Real.exp (-x^2)) := by
          funext x; ring_nf
        rw [heq] at h; exact h
      exact h_base.const_mul (4 * Real.exp (C^2))
    · apply Continuous.aestronglyMeasurable
      have h_sinh1 : Continuous (fun t : ℝ => Real.sinh (δ1 * t)) :=
        Real.continuous_sinh.comp (continuous_const.mul continuous_id)
      have h_sinh2 : Continuous (fun t : ℝ => Real.sinh (δ2 * t)) :=
        Real.continuous_sinh.comp (continuous_const.mul continuous_id)
      have h_gauss : Continuous (fun t : ℝ => Real.exp (-2 * t^2)) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))
      exact ((continuous_const.mul (h_sinh1.pow 2)).mul (h_sinh2.pow 2)).mul h_gauss
    · filter_upwards with t
      -- Bound: |4·sinh²·sinh²·exp(-2t²)| ≤ 4·e^(C²)·exp(-t²)
      have hcosh_le : ∀ a : ℝ, Real.cosh (a * t) ≤ Real.exp |a * t| := by
        intro a
        rw [Real.cosh_eq]
        rcases le_total 0 (a * t) with h | h
        · rw [abs_of_nonneg h]
          have : Real.exp (-(a * t)) ≤ Real.exp (a * t) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos (a * t), Real.exp_pos (-(a * t))]
        · rw [abs_of_nonpos h]
          have : Real.exp (a * t) ≤ Real.exp (-(a * t)) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith [Real.exp_pos (a * t), Real.exp_pos (-(a * t))]
      have hsinh_sq_le : ∀ a : ℝ, Real.sinh (a * t)^2 ≤ Real.exp (2 * |a * t|) := by
        intro a
        have h1 : Real.sinh (a * t)^2 ≤ Real.cosh (a * t)^2 := by
          have := Real.cosh_sq_sub_sinh_sq (a * t)  -- cosh² - sinh² = 1
          nlinarith [sq_nonneg (Real.sinh (a*t))]
        have h2 : Real.cosh (a * t)^2 ≤ Real.exp |a * t|^2 := by
          have := hcosh_le a
          have h_cosh_nn : 0 ≤ Real.cosh (a * t) := le_of_lt (Real.cosh_pos _)
          nlinarith [Real.exp_pos |a * t|]
        have h3 : Real.exp |a * t|^2 = Real.exp (2 * |a * t|) := by
          rw [sq, ← Real.exp_add]; ring_nf
        linarith [h1.trans h2, h3.le, h3.ge]
      -- Combine bounds
      have habs_δ1 : |δ1 * t| = |δ1| * |t| := abs_mul _ _
      have habs_δ2 : |δ2 * t| = |δ2| * |t| := abs_mul _ _
      have hs1 : Real.sinh (δ1 * t)^2 ≤ Real.exp (2 * (|δ1| * |t|)) := by
        have := hsinh_sq_le δ1; rw [habs_δ1] at this; exact this
      have hs2 : Real.sinh (δ2 * t)^2 ≤ Real.exp (2 * (|δ2| * |t|)) := by
        have := hsinh_sq_le δ2; rw [habs_δ2] at this; exact this
      have hs1_nn : 0 ≤ Real.sinh (δ1 * t)^2 := sq_nonneg _
      have hs2_nn : 0 ≤ Real.sinh (δ2 * t)^2 := sq_nonneg _
      have hexp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
      have hprod_le :
          Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 ≤
          Real.exp (2 * (|δ1| * |t|)) * Real.exp (2 * (|δ2| * |t|)) := by
        exact mul_le_mul hs1 hs2 hs2_nn (le_trans hs1_nn hs1)
      have hprod_eq :
          Real.exp (2 * (|δ1| * |t|)) * Real.exp (2 * (|δ2| * |t|)) =
          Real.exp (2 * C * |t|) := by
        rw [← Real.exp_add, hC_def]; ring_nf
      -- AM-GM: 2C|t| ≤ C² + t²
      have hAMGM : 2 * C * |t| ≤ C^2 + t^2 := by
        have habs_t_sq : |t|^2 = t^2 := sq_abs t
        nlinarith [sq_nonneg (C - |t|), abs_nonneg t, hC_nn]
      -- Final bound
      have h_nonneg : 0 ≤ 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 *
                          Real.exp (-2 * t^2) := by positivity
      rw [Real.norm_of_nonneg h_nonneg]
      calc 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * Real.exp (-2 * t^2)
          ≤ 4 * Real.exp (2 * C * |t|) * Real.exp (-2 * t^2) := by
            have hprod' : Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 ≤
                          Real.exp (2 * C * |t|) := hprod_le.trans_eq hprod_eq
            nlinarith [hprod', Real.exp_pos (2 * C * |t|)]
        _ = 4 * Real.exp (2 * C * |t| + -2 * t^2) := by
            rw [Real.exp_add]; ring
        _ ≤ 4 * Real.exp (C^2 - t^2) := by
            apply (mul_le_mul_iff_of_pos_left (by norm_num : (0:ℝ) < 4)).mpr
            exact Real.exp_le_exp.mpr (by linarith)
        _ = 4 * Real.exp (C^2) * Real.exp (-t^2) := by
            rw [show (C^2 - t^2 : ℝ) = C^2 + (-t^2) from by ring, Real.exp_add]; ring
  -- Positivity of integrand on Ioi 0.
  have h_pos_on_Ioi : ∀ t > 0,
      0 < 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2 := by
    intro t ht
    have hδ1t : δ1 * t ≠ 0 := mul_ne_zero hδ1 (ne_of_gt ht)
    have hδ2t : δ2 * t ≠ 0 := mul_ne_zero hδ2 (ne_of_gt ht)
    have hs1_ne : Real.sinh (δ1 * t) ≠ 0 := Real.sinh_ne_zero.mpr hδ1t
    have hs2_ne : Real.sinh (δ2 * t) ≠ 0 := Real.sinh_ne_zero.mpr hδ2t
    have hψpos : 0 < ψ_gaussian t := by
      unfold ψ_gaussian; exact Real.exp_pos _
    have hs1_sq : 0 < Real.sinh (δ1 * t)^2 := by positivity
    have hs2_sq : 0 < Real.sinh (δ2 * t)^2 := by positivity
    positivity
  -- Apply integral positivity.
  have h_nn_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        0 ≤ 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2 := by
    filter_upwards with t using by positivity
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae h_nn_ae h_integrable]
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi]
  have h_supp : Set.Ioi (0:ℝ) ⊆
      (Function.support
        (fun t => 4 * Real.sinh (δ1 * t)^2 * Real.sinh (δ2 * t)^2 * (ψ_gaussian t)^2)) := by
    intro t ht
    have hp := h_pos_on_Ioi t ht
    simp only [Function.mem_support]; exact ne_of_gt hp
  have hvol : 0 < MeasureTheory.volume ((Set.Ioi (0:ℝ)) ∩ Set.Ioi (0:ℝ)) := by
    rw [Set.inter_self]
    simp [Real.volume_Ioi]
  refine lt_of_lt_of_le hvol (MeasureTheory.measure_mono ?_)
  intro t ⟨ht1, ht2⟩
  exact ⟨h_supp ht1, ht2⟩

/-- **Forward implication: pair-defect vanishing forces β = 1/2.** -/
theorem re_half_of_gaussianPairDefect_zero
    (β : ℝ) (h : gaussianPairDefect β = 0) : β = 1/2 := by
  by_contra hne
  have hpos : 0 < gaussianPairDefect β := gaussianPairDefect_pos_offline hne
  linarith

/-- **Pair Gaussian bridge.** The detector-pair-based analog of the
single-cosh Gaussian bridge. Propositional content: at every nontrivial
zero of `ζ`, the Gaussian-weighted pair defect vanishes. -/
def PairGaussianBridge : Prop :=
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros → gaussianPairDefect ρ.re = 0

/-! The former `RiemannHypothesis_of_PairGaussianBridge` and
`RiemannHypothesis_from_pair_target` were removed. -/

#print axioms pairDetectorSqDiff_sinh_factor
#print axioms gaussianPairDefect_zero_on_line
#print axioms gaussianPairDefect_nonneg
#print axioms re_half_of_gaussianPairDefect_zero

end ZD

end
