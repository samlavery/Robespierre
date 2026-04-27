import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.MellinTransform
import RequestProject.WeilContour

/-!
# Residue of `s · coshGaussMellin c (s)` at `s = 0`

Mirrors the digamma-residue technique of `WeilArchKernelResidues.lean`.

## Important caveat — domain of the limit filter

The naive target

```
Tendsto (fun s : ℂ => s * coshGaussMellin c s) (nhdsWithin 0 {0}ᶜ) (nhds 1)
```

is **literally false**. Reason: `coshGaussMellin c s = mellin _ s` is defined as
a Bochner integral, which returns `0` whenever the integrand is non-integrable.
For `Re s ≤ 0` the factor `t^(s-1)` blows up at `t = 0⁺` and the integral is
non-integrable, so `coshGaussMellin c s = 0` and hence
`s · coshGaussMellin c s = 0` along all approach directions with `Re s ≤ 0`.
On the other hand for `Re s > 0` the value tends to `1`. Since `nhdsWithin 0 {0}ᶜ`
contains both half-planes, no single limit value exists.

We therefore prove the **honest half-plane version**, restricting the filter to
`{s : ℂ | 0 < s.re}`. This is the natural domain where the Mellin transform is
holomorphic and the residue is well-defined.

## Strategy

We split

```
coshGaussMellin c s = gaussMellin s + (coshGaussMellin c s - gaussMellin s).
```

The Gaussian Mellin reduces (via `mellin_comp_rpow` and `mellin_comp_mul_left`) to
`gaussMellin s = (1/2) · 2^{-s/2} · Γ(s/2)`, whose residue at `s = 0` is `1` via
`Complex.tendsto_self_mul_Gamma_nhds_zero`.

For the difference, the integrand `(cosh(c·t) - 1) · exp(-2t²)` is `O(t²)` at
`t = 0⁺`, which lets us extend the Mellin transform of the difference
holomorphically across `s = 0` via `mellin_differentiableAt_of_isBigO_rpow_exp`
with `b = -2`. In particular it is continuous at `s = 0`, so `s` times it tends
to `0`.

Combining: `s · coshGaussMellin c s → 1 + 0 = 1`.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set Asymptotics
open scoped Real

namespace ZD.CoshGaussMellinResidue

open ZD.WeilPositivity.Contour

/-! ### Closed form for `gaussMellin` -/

/-- `gaussMellin s = (1/2) · 2^(-s/2) · Γ(s/2)` for `Re s > 0`. Direct via
the Mellin substitutions `t ↦ t^2` and `u ↦ 2u`. -/
theorem gaussMellin_closed_form {s : ℂ} (hs : 0 < s.re) :
    gaussMellin s = (1/2 : ℂ) * (2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2) := by
  unfold gaussMellin
  have h_rpow : (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) =
                (fun t : ℝ => (fun u : ℝ => ((Real.exp (-(2*u)) : ℝ) : ℂ)) (t ^ (2:ℝ))) := by
    funext t
    have h_pow : t^(2:ℝ) = t^2 := by
      have h2 : (2:ℝ) = ((2:ℕ):ℝ) := by norm_num
      rw [h2, Real.rpow_natCast]
    show ((Real.exp (-2 * t^2) : ℝ) : ℂ) = ((Real.exp (-(2*(t^(2:ℝ)))) : ℝ) : ℂ)
    rw [h_pow]; congr 2; ring
  rw [h_rpow]
  rw [mellin_comp_rpow (fun u : ℝ => ((Real.exp (-(2*u)) : ℝ) : ℂ)) s (2:ℝ)]
  have h2cast : ((2:ℝ):ℂ) = (2:ℂ) := by norm_cast
  rw [h2cast]
  have hs2 : 0 < (s/2).re := by
    have : (s/2).re = s.re / 2 := by simp
    rw [this]; linarith
  have h_inner :
      mellin (fun u : ℝ => ((Real.exp (-(2*u)) : ℝ) : ℂ)) (s/2)
        = (2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2) := by
    have h_step1 :
      mellin (fun t : ℝ => ((Real.exp (-(2*t)) : ℝ) : ℂ)) (s/2)
        = (2 : ℂ) ^ (-(s/2)) • mellin (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (s/2) := by
      have key := mellin_comp_mul_left
                (f := fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (s := s/2) (a := (2:ℝ))
                (by norm_num : (0:ℝ) < 2)
      have heq : (fun t : ℝ => ((Real.exp (-(2*t)) : ℝ) : ℂ)) =
                 (fun t : ℝ => (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (2 * t)) := by
        funext t; rfl
      rw [heq]; exact key
    rw [h_step1]
    rw [show (mellin (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) (s/2) = Complex.Gamma (s/2)) from by
      rw [Complex.Gamma_eq_integral hs2, Complex.GammaIntegral_eq_mellin]]
    rw [smul_eq_mul]
  rw [h_inner]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  show ((2:ℝ)⁻¹ : ℝ) • ((2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2))
       = (1/2 : ℂ) * (2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)
  rw [show ((2:ℝ)⁻¹ : ℝ) • ((2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)) =
        (((2:ℝ)⁻¹ : ℝ) : ℂ) * ((2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)) from by
    rw [Complex.real_smul]]
  push_cast; ring

/-! ### Residue of `gaussMellin` at `s = 0` -/

/-- `s · gaussMellin s → 1` as `s → 0` along the half-plane `Re s > 0`. -/
theorem gaussMellin_residue_at_zero :
    Tendsto (fun s : ℂ => s * gaussMellin s)
      (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhds (1:ℂ)) := by
  have h_self : ({s : ℂ | 0 < s.re} : Set ℂ) ∈ nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re} :=
    self_mem_nhdsWithin
  have h_eq : (fun s : ℂ => s * gaussMellin s) =ᶠ[nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}]
              (fun s : ℂ => (2:ℂ)^(-(s/2)) * ((s/2) * Complex.Gamma (s/2))) := by
    filter_upwards [h_self] with s hs
    rw [gaussMellin_closed_form hs]
    ring
  refine Tendsto.congr' h_eq.symm ?_
  -- Factor 1: 2^(-s/2) → 1
  have h_pow : Tendsto (fun s : ℂ => (2:ℂ)^(-(s/2)))
               (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhds (1:ℂ)) := by
    have h_b_cont : ContinuousAt (fun s : ℂ => -(s/2)) 0 := by
      apply Continuous.continuousAt; continuity
    have hbase : ContinuousAt (fun z : ℂ => (2:ℂ)^z) (-((0:ℂ)/2)) :=
      continuousAt_const_cpow (by norm_num : (2:ℂ) ≠ 0)
    have h_cont : ContinuousAt (fun s : ℂ => (2:ℂ)^(-(s/2))) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => (2:ℂ)^z) (f := fun s : ℂ => -(s/2)) (x := 0)
        (by show ContinuousAt _ ((fun s : ℂ => -(s/2)) 0); convert hbase using 1)
        h_b_cont
    have hval : (2:ℂ)^(-((0:ℂ)/2)) = 1 := by simp
    have h_full : Tendsto (fun s : ℂ => (2:ℂ)^(-(s/2))) (𝓝 (0:ℂ)) (𝓝 (1:ℂ)) := by
      rw [show (1:ℂ) = (2:ℂ)^(-((0:ℂ)/2)) from hval.symm]
      rw [ContinuousAt] at h_cont
      exact h_cont
    exact h_full.mono_left nhdsWithin_le_nhds
  -- Factor 2: (s/2) * Γ(s/2) → 1
  have h_gam : Tendsto (fun s : ℂ => (s/2) * Complex.Gamma (s/2))
               (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhds (1:ℂ)) := by
    have h_arg : Tendsto (fun s : ℂ => s / 2)
                 (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhdsWithin (0:ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℂ => s / 2) (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by
          have h := (continuous_id.div_const (2:ℂ)).continuousAt (x := (0:ℂ))
          simpa [ContinuousAt] using h
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [h_self] with s hs h0
        have h0' : s / 2 = 0 := h0
        have hsdiv : s = 0 := by
          have h_iff := div_eq_zero_iff.mp h0'
          rcases h_iff with h | h
          · exact h
          · exfalso; norm_num at h
        rw [hsdiv] at hs; simp at hs
    exact Complex.tendsto_self_mul_Gamma_nhds_zero.comp h_arg
  have h_prod := h_pow.mul h_gam
  simp at h_prod
  exact h_prod

/-! ### Cosh-difference Mellin transform extends across `s = 0` -/

/-- `cosh(x) - 1 ≤ (x²/2) · exp(x²/2)` for any real `x`. -/
private lemma cosh_minus_one_bound (x : ℝ) :
    Real.cosh x - 1 ≤ (x^2 / 2) * Real.exp (x^2 / 2) := by
  have h1 : Real.cosh x ≤ Real.exp (x^2 / 2) := Real.cosh_le_exp_half_sq _
  set y := x^2 / 2 with hy_def
  have hy_nn : 0 ≤ y := by simp only [hy_def]; positivity
  have h_int_exp : IntervalIntegrable Real.exp MeasureTheory.volume 0 y :=
    Real.continuous_exp.intervalIntegrable _ _
  have h_int_const : IntervalIntegrable (fun _ => Real.exp y) MeasureTheory.volume 0 y :=
    intervalIntegrable_const
  have h_int : ∫ u in (0:ℝ)..y, Real.exp u = Real.exp y - Real.exp 0 := integral_exp
  rw [Real.exp_zero] at h_int
  have h_bound : ∫ u in (0:ℝ)..y, Real.exp u ≤ ∫ _ in (0:ℝ)..y, Real.exp y := by
    apply intervalIntegral.integral_mono_on hy_nn h_int_exp h_int_const
    intro u hu; exact Real.exp_le_exp.mpr hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h_bound
  linarith

/-- The integrand `(cosh(c·t) − 1) · exp(−2t²)` is `O(t²)` (= `O(t^(-(-2)))`)
near `0⁺`. Used to extend the Mellin transform of the difference across
`s = 0`. -/
theorem coshDiff_isBigO_rpow_two_nhds_zero (c : ℝ) :
    (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-2:ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (c^2 * Real.exp (c^2 / 2) / 2) ?_
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioc 0 1, ?_, fun t ht => ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Set.Iio 1, isOpen_Iio, by simp, ?_⟩
    intro t ⟨ht_lt, ht_pos⟩
    exact ⟨ht_pos, ht_lt.le⟩
  · have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ 1 := ht.2
    have h_cosh_nn : 0 ≤ Real.cosh (c * t) - 1 := by
      have := Real.one_le_cosh (c * t); linarith
    have h_exp_nn : 0 ≤ Real.exp (-2 * t^2) := (Real.exp_pos _).le
    have h_lhs_nn : 0 ≤ (Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) :=
      mul_nonneg h_cosh_nn h_exp_nn
    rw [show ‖(((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ =
        (Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) from by
      rw [Complex.norm_real]; exact abs_of_nonneg h_lhs_nn]
    have h_bound1 : Real.cosh (c * t) - 1 ≤ ((c * t)^2 / 2) * Real.exp ((c * t)^2 / 2) :=
      cosh_minus_one_bound (c * t)
    have h_t_sq : t^2 ≤ 1 := by nlinarith
    have h_ct_sq_le : (c * t)^2 ≤ c^2 := by
      have h : (c*t)^2 = c^2 * t^2 := by ring
      rw [h]
      calc c^2 * t^2 ≤ c^2 * 1 :=
            mul_le_mul_of_nonneg_left h_t_sq (sq_nonneg c)
        _ = c^2 := by ring
    have h_exp_le : Real.exp ((c * t)^2 / 2) ≤ Real.exp (c^2 / 2) := by
      apply Real.exp_le_exp.mpr; linarith
    have h_exp_le_one : Real.exp (-2 * t^2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ t^2 := sq_nonneg _
      nlinarith
    have h_pow_eq : t^(-(-2:ℝ)) = t^2 := by
      rw [neg_neg]
      have : (2:ℝ) = ((2:ℕ):ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    have h_norm_pow : ‖t^(-(-2:ℝ))‖ = t^2 := by
      rw [h_pow_eq, Real.norm_of_nonneg (sq_nonneg _)]
    rw [h_norm_pow]
    calc (Real.cosh (c * t) - 1) * Real.exp (-2 * t^2)
        ≤ ((c * t)^2 / 2 * Real.exp ((c * t)^2 / 2)) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_bound1 h_exp_nn
      _ ≤ ((c * t)^2 / 2 * Real.exp (c^2 / 2)) * Real.exp (-2 * t^2) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left h_exp_le; positivity
          · exact h_exp_nn
      _ ≤ ((c * t)^2 / 2 * Real.exp (c^2 / 2)) * 1 := by
          apply mul_le_mul_of_nonneg_left h_exp_le_one; positivity
      _ = ((c * t)^2 / 2) * Real.exp (c^2 / 2) := by ring
      _ = (c^2 * Real.exp (c^2 / 2) / 2) * t^2 := by ring

/-- The integrand `(cosh(c·t) − 1) · exp(−2t²)` decays exponentially at `+∞`. -/
theorem coshDiff_isBigO_exp_neg_atTop (c : ℝ) :
    (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))
      =O[atTop] (fun t : ℝ => Real.exp (-t)) := by
  -- Bound: |cosh(ct) - 1| ≤ cosh(ct) (since cosh ≥ 1).
  -- So |(cosh(ct)-1)·exp(-2t²)| ≤ cosh(ct)·exp(-2t²), and the latter is O(exp(-t))
  -- by `coshGauss_isBigO_exp_neg_atTop`.
  have h_cgo := coshGauss_isBigO_exp_neg_atTop c
  refine Asymptotics.IsBigO.trans (g := fun t : ℝ => ((Real.cosh (c*t) * Real.exp (-2*t^2) : ℝ) : ℂ))
    ?_ h_cgo
  refine Asymptotics.IsBigO.of_bound 1 ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun t _ => ?_⟩
  have h_cosh_minus_one_le : |Real.cosh (c * t) - 1| ≤ Real.cosh (c * t) := by
    have h1 : 1 ≤ Real.cosh (c * t) := Real.one_le_cosh _
    have hpos : 0 ≤ Real.cosh (c * t) - 1 := by linarith
    rw [abs_of_nonneg hpos]; linarith
  have h_exp_pos : 0 < Real.exp (-2 * t^2) := Real.exp_pos _
  -- Both sides have `Complex.norm_real` reducing to real abs.
  have h_lhs_eq : ‖(((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ =
                  |(Real.cosh (c * t) - 1) * Real.exp (-2 * t^2)| := Complex.norm_real _
  have h_rhs_eq : ‖((Real.cosh (c*t) * Real.exp (-2*t^2) : ℝ) : ℂ)‖ =
                  |Real.cosh (c*t) * Real.exp (-2*t^2)| := Complex.norm_real _
  rw [h_lhs_eq, h_rhs_eq, one_mul]
  rw [abs_mul, abs_mul, abs_of_nonneg h_exp_pos.le,
      abs_of_nonneg (Real.cosh_pos _).le]
  exact mul_le_mul_of_nonneg_right h_cosh_minus_one_le h_exp_pos.le

/-- LocallyIntegrable: `(cosh(c·t) − 1) · exp(−2t²)` is locally integrable on `Ioi 0`. -/
private lemma coshDiff_locallyIntegrableOn (c : ℝ) :
    LocallyIntegrableOn (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))
      (Ioi (0:ℝ)) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  apply Continuous.continuousOn
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.mul ?_ ?_
  · exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))

/-- The Mellin transform of the difference `(cosh(c·t) − 1) · exp(−2t²)` is
holomorphic on `Re s > -2`. In particular it is continuous at `s = 0`. -/
theorem coshDiffMellin_differentiableAt (c : ℝ) {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ
      (mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := -2)
    (by norm_num : (0:ℝ) < 1) (coshDiff_locallyIntegrableOn c)
  · -- =O[atTop] exp(-1·t)
    have : (fun t : ℝ => Real.exp (-t)) = (fun t : ℝ => Real.exp (-1 * t)) := by
      funext t; congr 1; ring
    rw [← this]
    exact coshDiff_isBigO_exp_neg_atTop c
  · exact coshDiff_isBigO_rpow_two_nhds_zero c
  · exact hs

/-- `coshGaussMellin c s − gaussMellin s` equals the Mellin transform of the
difference for `Re s > 0`. -/
theorem coshGaussMellin_sub_gaussMellin_eq (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    coshGaussMellin c s - gaussMellin s =
    mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
  -- Both Mellin integrals converge for Re s > 0. Subtract under the integral.
  -- Recast `coshGaussMellin` and `gaussMellin` into the cast-after form for
  -- compatibility with `mellinConvergent_coshGauss` and `integral_sub`.
  have h_cgm_eq : coshGaussMellin c s =
      mellin (fun t : ℝ => ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
    unfold coshGaussMellin
    congr 1; funext t; push_cast; ring
  have h_gm_eq : gaussMellin s =
      mellin (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
    unfold gaussMellin; rfl
  rw [h_cgm_eq, h_gm_eq]
  have h1 := mellinConvergent_coshGauss c hs
  have h2 : MellinConvergent (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) s := by
    have hzero := mellinConvergent_coshGauss 0 hs
    have h_eq : (fun t : ℝ => ((Real.cosh (0 * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =
                (fun t : ℝ => ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
      funext t
      have : Real.cosh (0 * t) = 1 := by simp
      rw [this, one_mul]
    rw [h_eq] at hzero
    exact hzero
  unfold mellin
  rw [← MeasureTheory.integral_sub h1 h2]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show (t : ℂ) ^ (s - 1) • ((Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ) -
       (t : ℂ) ^ (s - 1) • ((Real.exp (-2 * t^2) : ℝ) : ℂ) =
       (t : ℂ) ^ (s - 1) • (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)
  rw [← smul_sub]
  congr 1
  push_cast; ring

/-- `coshGaussMellin c s − gaussMellin s` is continuous at `s = 0` (extending
across the pole) along the half-plane `Re s > 0`. -/
theorem coshGaussMellin_sub_gaussMellin_tendsto_zero_residue (c : ℝ) :
    Tendsto (fun s : ℂ => s * (coshGaussMellin c s - gaussMellin s))
      (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhds (0:ℂ)) := by
  -- Express the difference as `mellin diff s` on the half-plane.
  have h_self : ({s : ℂ | 0 < s.re} : Set ℂ) ∈ nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re} :=
    self_mem_nhdsWithin
  have h_eq : (fun s : ℂ => s * (coshGaussMellin c s - gaussMellin s))
              =ᶠ[nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}]
              (fun s : ℂ => s *
                mellin (fun t : ℝ =>
                  (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s) := by
    filter_upwards [h_self] with s hs
    rw [coshGaussMellin_sub_gaussMellin_eq c hs]
  refine Tendsto.congr' h_eq.symm ?_
  -- mellin diff is continuous at 0 (since differentiable on Re > -2)
  have h_diff_at_zero : DifferentiableAt ℂ
      (mellin (fun t : ℝ =>
        (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) 0 := by
    apply coshDiffMellin_differentiableAt c
    show (-2:ℝ) < (0:ℂ).re
    simp
  have h_cont_at_zero : ContinuousAt
      (mellin (fun t : ℝ =>
        (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) 0 :=
    h_diff_at_zero.continuousAt
  have h_id_cont : ContinuousAt (fun s : ℂ => s) 0 := continuous_id.continuousAt
  have h_prod_cont : ContinuousAt
      (fun s : ℂ => s *
        mellin (fun t : ℝ =>
          (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s) 0 :=
    h_id_cont.mul h_cont_at_zero
  have h_val : (0:ℂ) * mellin (fun t : ℝ =>
        (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)) 0 = 0 := by simp
  have h_full : Tendsto
      (fun s : ℂ => s *
        mellin (fun t : ℝ =>
          (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)) s)
      (𝓝 (0:ℂ)) (nhds (0:ℂ)) := by
    have hh := h_prod_cont
    rw [ContinuousAt] at hh
    -- hh : Tendsto _ (𝓝 0) (𝓝 (0 * mellin _ 0))
    rw [h_val] at hh
    exact hh
  exact h_full.mono_left nhdsWithin_le_nhds

/-! ### Main result: residue of `coshGaussMellin c` at `s = 0` -/

/-- **Main theorem.** `s · coshGaussMellin c s → 1` as `s → 0` along the
half-plane `Re s > 0`. The residue at `s = 0` is `1`, independent of `c`.

The literal target with filter `nhdsWithin 0 {0}ᶜ` is false because the Mellin
integral diverges (and Bochner returns `0`) for `Re s ≤ 0`; see the module
docstring. -/
theorem coshGaussMellin_residue_at_zero (c : ℝ) :
    Tendsto (fun s : ℂ => s * coshGaussMellin c s)
      (nhdsWithin (0:ℂ) {s : ℂ | 0 < s.re}) (nhds (1:ℂ)) := by
  -- Split: s · coshGaussMellin c s = s · gaussMellin s + s · (coshGaussMellin c s - gaussMellin s).
  -- First piece → 1 by gaussMellin_residue_at_zero.
  -- Second piece → 0 by coshGaussMellin_sub_gaussMellin_tendsto_zero_residue.
  have h1 := gaussMellin_residue_at_zero
  have h2 := coshGaussMellin_sub_gaussMellin_tendsto_zero_residue c
  have h_sum := h1.add h2
  have h_target : (1:ℂ) + (0:ℂ) = 1 := by ring
  rw [h_target] at h_sum
  apply h_sum.congr
  intro s
  show s * gaussMellin s + s * (coshGaussMellin c s - gaussMellin s) = s * coshGaussMellin c s
  ring

#print axioms coshGaussMellin_residue_at_zero

end ZD.CoshGaussMellinResidue
