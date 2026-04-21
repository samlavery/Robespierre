import Mathlib
import RequestProject.WeilContour

/-!
# Weil Contour — Multiplicity-Aware Residue Calculus (B-refactor)

Unconditional generalization of cycles 28–32, 41 from `WeilContour.lean`,
replacing the simple-zero hypothesis `deriv f w ≠ 0` with the multiplicity
parameter `n = analyticOrderAt f w`.

## Why

The simple-zeros conjecture for `ζ` (∀ nontrivial ρ, `deriv ζ ρ ≠ 0`) is an
open problem in analytic number theory — independent of RH, believed true,
not proved unconditionally. For an unconditional RH formalization we must
handle zeros of any (finite) multiplicity.

## Strategy

For `f` analytic at `w`, `f w = 0`, and `n := analyticOrderAt f w` a finite
positive natural number:

1. **Factorization** (`zero_factor_of_order`): `f(z) = (z−w)^n · g(z)` near `w`
   with `g` analytic, `g w ≠ 0`. Direct from `AnalyticAt.analyticOrderAt_eq_natCast`.

2. **Log-deriv partial fraction** (`logDeriv_pole_of_order`):
   `deriv f z / f z = n · (z−w)⁻¹ + deriv g z / g z` on punctured nhds `w`.
   Algebra via product rule + `logDeriv_pow`.

3. **Weil integrand Laurent** (`weilIntegrand_laurent_at_zero_of_order`):
   `weilIntegrand h s = −(n · (s−w)⁻¹ + deriv g s / g s) · h s`.

4. **Circle integral** (`weilIntegrand_circle_integral_at_zero_of_order`):
   `∮_{C(w,r)} weilIntegrand h z dz = −(2πi · n) · h(w)`.

5. **Per-zero finite-set** (`weil_circle_integral_per_zero_of_order`):
   For a finite set of (possibly multiple) zeros of `ζ`, the circle integral
   at each is `−(2πi · analyticOrderAt ζ ρ) · h(ρ)`.

## Compatibility

The simple-zero versions in `WeilContour.lean` are unchanged; they specialize
the order-n versions at `n = 1`. Downstream callers can use either.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § Order-n zero factorization (generalizes cycle 21)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Order-n zero factorization.** If `f` is analytic at `w` with
`analyticOrderAt f w = n` (a natural number) and `n ≥ 1`, then
`f(z) = (z − w)^n · g(z)` on a neighborhood of `w`, where `g` is analytic
at `w` and `g w ≠ 0`.

This is the foundational factorization for residue calculus at a zero of
arbitrary order. Specializes to `simple_zero_factor` at `n = 1`. -/
theorem zero_factor_of_order {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w) (hf_order : analyticOrderAt f w = (n : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhds w, f z = (z - w)^n * g z := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := n)).mp hf_order
  refine ⟨g, hg_an, hg_ne, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz, smul_eq_mul]

#print axioms zero_factor_of_order

-- ═══════════════════════════════════════════════════════════════════════════
-- § Order-n log-derivative partial fraction (generalizes cycle 21)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Log-derivative has a simple pole with residue `n` at a zero of order `n`.**
If `f` is analytic at `w`, `f w = 0`, and `analyticOrderAt f w = n ≥ 1`, then on
a punctured nhds of `w`:

```
deriv f z / f z = n · (z − w)⁻¹ + deriv g z / g z
```

where `g` is the analytic factor from `zero_factor_of_order`. -/
theorem logDeriv_pole_of_order {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w) (hf_order : analyticOrderAt f w = (n : ℕ∞))
    (hn : 1 ≤ n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (n : ℂ) * (z - w)⁻¹ + deriv g z / g z := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := zero_factor_of_order hf hf_order
  refine ⟨g, hg_an, hg_ne, ?_⟩
  -- Punctured versions.
  have hfg_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ, f z = (z - w)^n * g z :=
    hfg.filter_mono nhdsWithin_le_nhds
  have hg_nonzero : ∀ᶠ z in nhds w, g z ≠ 0 :=
    hg_an.continuousAt.eventually_ne hg_ne
  have hg_nonzero_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ, g z ≠ 0 :=
    hg_nonzero.filter_mono nhdsWithin_le_nhds
  -- `f'` eventually equals `n·(z-w)^(n-1)·g(z) + (z-w)^n · g'(z)` via product rule.
  have hf_deriv_eq : ∀ᶠ z in nhds w,
      deriv f z = (n : ℂ) * (z - w)^(n-1) * g z + (z - w)^n * deriv g z := by
    have hfg_open : ∀ᶠ z in nhds w, ∀ᶠ y in nhds z, f y = (y - w)^n * g y := by
      filter_upwards [eventually_eventually_nhds.mpr hfg] with z hz
      exact hz
    filter_upwards [hfg_open, hg_an.eventually_analyticAt] with z hz hg_an_z
    have h_g : DifferentiableAt ℂ g z := hg_an_z.differentiableAt
    -- Derivative of (y - w)^n at z.
    have h_sub_z : HasDerivAt (fun y : ℂ => y - w) 1 z := (hasDerivAt_id z).sub_const w
    have h_pow : HasDerivAt (fun y : ℂ => (y - w)^n)
        ((n : ℂ) * (z - w)^(n-1) * 1) z := by
      have := h_sub_z.pow (n := n)
      simpa using this
    have h_pow' : HasDerivAt (fun y : ℂ => (y - w)^n) ((n : ℂ) * (z - w)^(n-1)) z := by
      convert h_pow using 1; ring
    -- Product rule.
    have h_prod_z : HasDerivAt (fun y : ℂ => (y - w)^n * g y)
        ((n : ℂ) * (z - w)^(n-1) * g z + (z - w)^n * deriv g z) z :=
      h_pow'.mul h_g.hasDerivAt
    have hz_eq : (fun y : ℂ => f y) =ᶠ[nhds z] fun y : ℂ => (y - w)^n * g y := hz
    have h_f_z : HasDerivAt f
        ((n : ℂ) * (z - w)^(n-1) * g z + (z - w)^n * deriv g z) z :=
      hz_eq.symm.hasDerivAt_iff.mp h_prod_z
    exact h_f_z.deriv
  have hf_deriv_punct : ∀ᶠ z in nhdsWithin w {w}ᶜ,
      deriv f z = (n : ℂ) * (z - w)^(n-1) * g z + (z - w)^n * deriv g z :=
    hf_deriv_eq.filter_mono nhdsWithin_le_nhds
  have h_sub_ne : ∀ᶠ z in nhdsWithin w {w}ᶜ, z - w ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero_of_ne hz
  filter_upwards [hfg_punct, hf_deriv_punct, hg_nonzero_punct, h_sub_ne]
    with z hfz hfdz hgz hsub
  -- Algebra: [n·(z-w)^(n-1)·g + (z-w)^n · g'] / [(z-w)^n · g] = n/(z-w) + g'/g.
  rw [hfz, hfdz]
  have h_pow_ne : (z - w)^n ≠ 0 := pow_ne_zero n hsub
  have h_pow_pred_ne : (z - w)^(n-1) ≠ 0 := pow_ne_zero (n-1) hsub
  -- Factor (z-w)^(n-1) from numerator via (z-w)^n = (z-w)·(z-w)^(n-1).
  have h_pow_split : (z - w)^n = (z - w) * (z - w)^(n-1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h_pow_split]
  field_simp

#print axioms logDeriv_pole_of_order

-- ═══════════════════════════════════════════════════════════════════════════
-- § Weil integrand Laurent at a zero of arbitrary order (generalizes cycle 28)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Weil integrand Laurent at a zero of order `n`.** At a zero `ρ` of `ζ`
with `analyticOrderAt ζ ρ = n ≥ 1`, the Weil integrand has the expansion

```
weilIntegrand h s = −(n · (s − ρ)⁻¹ + deriv g s / g s) · h s
```

on a punctured nhds of `ρ`, where `g` is the analytic factor with `g ρ ≠ 0`. -/
theorem weilIntegrand_laurent_at_zero_of_order
    {h : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (_hζ_zero : riemannZeta ρ = 0)
    (hζ_order : analyticOrderAt riemannZeta ρ = (n : ℕ∞))
    (hn : 1 ≤ n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s = -((n : ℂ) * (s - ρ)⁻¹ + deriv g s / g s) * h s := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := logDeriv_pole_of_order hζ_an hζ_order hn
  refine ⟨g, hg_an, hg_ne, ?_⟩
  filter_upwards [hfg] with s hs
  unfold weilIntegrand
  rw [show -deriv riemannZeta s / riemannZeta s =
      -(deriv riemannZeta s / riemannZeta s) by ring, hs]

#print axioms weilIntegrand_laurent_at_zero_of_order

-- ═══════════════════════════════════════════════════════════════════════════
-- § Circle integral at a zero of arbitrary order (generalizes cycles 30, 31, 32)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Circle integral from explicit order-n decomposition.** Given a sphere-level
decomposition `weilIntegrand h z = −n·h(z)/(z−ρ) + φ(z)` with both pieces
holomorphic on the closed disk, the circle integral equals `−(2πi · n) · h(ρ)`.

Generalization of cycle 30's simple-zero variant. -/
theorem weilIntegrand_circle_integral_from_decomposition_of_order
    {h φ : ℂ → ℂ} {ρ : ℂ} {r : ℝ} {n : ℕ} (hr : 0 < r)
    (hh_cont : ContinuousOn h (Metric.closedBall ρ r))
    (hh_diff : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z)
    (hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball ρ r))
    (hdecomp : ∀ z ∈ Metric.sphere ρ r,
        weilIntegrand h z = -(n : ℂ) * h z / (z - ρ) + φ z) :
    (∮ z in C(ρ, r), weilIntegrand h z) = -(2 * ↑π * I * (n : ℂ)) * h ρ := by
  -- Sphere points are ≠ ρ.
  have h_sphere_ne_ρ : ∀ z ∈ Metric.sphere ρ r, z ≠ ρ := by
    intro z hz hzρ
    rw [hzρ, Metric.mem_sphere, dist_self] at hz
    exact absurd hz.symm hr.ne'
  have h_sphere_sub_closed : Metric.sphere ρ r ⊆ Metric.closedBall ρ r :=
    Metric.sphere_subset_closedBall
  have hh_on_sphere : ContinuousOn h (Metric.sphere ρ r) :=
    hh_cont.mono h_sphere_sub_closed
  have hφ_cont_closure : ContinuousOn φ (closure (Metric.ball ρ r)) :=
    hφ_diffcontoncl.continuousOn
  have h_closure_eq : closure (Metric.ball ρ r) = Metric.closedBall ρ r :=
    closure_ball ρ hr.ne'
  rw [h_closure_eq] at hφ_cont_closure
  have hφ_on_sphere : ContinuousOn φ (Metric.sphere ρ r) :=
    hφ_cont_closure.mono h_sphere_sub_closed
  have h_polar_cont_sphere :
      ContinuousOn (fun z : ℂ => -(n : ℂ) * h z / (z - ρ)) (Metric.sphere ρ r) := by
    apply ContinuousOn.div
    · exact (continuousOn_const.mul hh_on_sphere)
    · exact (continuousOn_id.sub continuousOn_const)
    · intro z hz; exact sub_ne_zero_of_ne (h_sphere_ne_ρ z hz)
  -- Transfer integrand via integral_congr.
  rw [circleIntegral.integral_congr hr.le hdecomp]
  have h_polar_ci :
      CircleIntegrable (fun z : ℂ => -(n : ℂ) * h z / (z - ρ)) ρ r :=
    h_polar_cont_sphere.circleIntegrable hr.le
  have h_φ_ci : CircleIntegrable φ ρ r := hφ_on_sphere.circleIntegrable hr.le
  rw [circleIntegral.integral_add h_polar_ci h_φ_ci]
  -- φ vanishes by Cauchy-Goursat.
  rw [hφ_diffcontoncl.circleIntegral_eq_zero hr.le, add_zero]
  -- Polar part: ∮ -n·h/(z-ρ) = -n · ∮ h/(z-ρ) = -n · 2πi · h(ρ).
  have h_scalar_form : (fun z : ℂ => -(n : ℂ) * h z / (z - ρ)) =
      fun z : ℂ => -(n : ℂ) • (h z / (z - ρ)) := by
    funext z
    rw [smul_eq_mul]
    ring
  rw [h_scalar_form]
  rw [circleIntegral.integral_smul]
  have h_polar := polar_part_circle_integral hr hh_cont hh_diff
  rw [h_polar]
  simp only [smul_eq_mul]
  ring

#print axioms weilIntegrand_circle_integral_from_decomposition_of_order

/-- **Sphere decomposition from an order-n factorization.** Given `ζ(z) = (z−ρ)^n · g(z)`
on `ball ρ R` with `g` nonzero, the Weil integrand admits the explicit Laurent form

```
weilIntegrand h z = −n·h(z)/(z−ρ) + (−h(z) · g'(z)/g(z))    for z ∈ sphere ρ r.
```

Generalization of cycle 31 to arbitrary zero order. -/
theorem weilIntegrand_sphere_decomposition_from_factorization_of_order
    {h g : ℂ → ℂ} {ρ : ℂ} {r R : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hr : 0 < r) (hrR : r < R)
    (hfact : ∀ z ∈ Metric.ball ρ R, riemannZeta z = (z - ρ)^n * g z)
    (hg_diff : DifferentiableOn ℂ g (Metric.ball ρ R))
    (hg_ne : ∀ z ∈ Metric.ball ρ R, g z ≠ 0)
    (hh_diff : DifferentiableOn ℂ h (Metric.ball ρ R)) :
    ∀ z ∈ Metric.sphere ρ r,
      weilIntegrand h z =
        -(n : ℂ) * h z / (z - ρ) + (-h z * deriv g z / g z) := by
  intro z hz
  have hz_in_ball : z ∈ Metric.ball ρ R := by
    rw [Metric.mem_ball]
    calc dist z ρ = r := Metric.mem_sphere.mp hz
      _ < R := hrR
  have hz_ne_ρ : z ≠ ρ := by
    intro hzρ
    rw [hzρ, Metric.mem_sphere, dist_self] at hz
    exact absurd hz.symm hr.ne'
  have hfact_z : riemannZeta z = (z - ρ)^n * g z := hfact z hz_in_ball
  have hg_z_ne : g z ≠ 0 := hg_ne z hz_in_ball
  have h_sub_ne : z - ρ ≠ 0 := sub_ne_zero_of_ne hz_ne_ρ
  have h_pow_ne : (z - ρ)^n ≠ 0 := pow_ne_zero n h_sub_ne
  have hζ_z_ne : riemannZeta z ≠ 0 := by
    rw [hfact_z]; exact mul_ne_zero h_pow_ne hg_z_ne
  -- deriv ζ z via product rule on (z-ρ)^n · g z eventually.
  have hball_mem : Metric.ball ρ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz_in_ball
  have hfact_eventually : (fun w : ℂ => riemannZeta w) =ᶠ[nhds z]
      (fun w => (w - ρ)^n * g w) :=
    Filter.eventually_of_mem hball_mem (fun w hw => hfact w hw)
  have hg_diff_z : DifferentiableAt ℂ g z :=
    (hg_diff z hz_in_ball).differentiableAt hball_mem
  have h_sub_hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have h_pow_hd : HasDerivAt (fun w : ℂ => (w - ρ)^n) ((n : ℂ) * (z - ρ)^(n-1) * 1) z := by
    have := h_sub_hd.pow (n := n)
    simpa using this
  have h_pow_hd' : HasDerivAt (fun w : ℂ => (w - ρ)^n) ((n : ℂ) * (z - ρ)^(n-1)) z := by
    convert h_pow_hd using 1; ring
  have h_prod_hd : HasDerivAt (fun w : ℂ => (w - ρ)^n * g w)
      ((n : ℂ) * (z - ρ)^(n-1) * g z + (z - ρ)^n * deriv g z) z :=
    h_pow_hd'.mul hg_diff_z.hasDerivAt
  have hζ_hd : HasDerivAt riemannZeta
      ((n : ℂ) * (z - ρ)^(n-1) * g z + (z - ρ)^n * deriv g z) z :=
    hfact_eventually.symm.hasDerivAt_iff.mp h_prod_hd
  have hζ_deriv_z : deriv riemannZeta z =
      (n : ℂ) * (z - ρ)^(n-1) * g z + (z - ρ)^n * deriv g z := hζ_hd.deriv
  unfold weilIntegrand
  rw [hζ_deriv_z, hfact_z]
  -- n·(z-ρ)^(n-1)·g + (z-ρ)^n · g' over (z-ρ)^n · g
  --   = n·(z-ρ)^(-1) + g'/g  (after dividing num and denom by (z-ρ)^(n-1)·g)
  have h_pow_split : (z - ρ)^n = (z - ρ) * (z - ρ)^(n-1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h_pow_split]
  have h_pow_pred_ne : (z - ρ)^(n-1) ≠ 0 := pow_ne_zero (n-1) h_sub_ne
  field_simp
  ring

#print axioms weilIntegrand_sphere_decomposition_from_factorization_of_order

/-- **Per-zero circle integral at a zero of arbitrary order.** At a zero `ρ` of
`ζ` with `analyticOrderAt ζ ρ = n ≥ 1`, for `h` analytic at `ρ`, there exists
`r > 0` such that

```
∮_{C(ρ, r)} weilIntegrand h z dz = −(2πi · n) · h(ρ).
```

This is the multiplicity-aware replacement for cycle 32's
`weilIntegrand_circle_integral_at_simple_zero`.

**Proof**: compose `zero_factor_of_order`, `weilIntegrand_sphere_decomposition_
from_factorization_of_order`, and `weilIntegrand_circle_integral_from_decom
position_of_order`. The analytic remainder `φ = -h · g'/g` is analytic since
`g ≠ 0` on a ball. -/
theorem weilIntegrand_circle_integral_at_zero_of_order
    {h : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (_hζ_zero : riemannZeta ρ = 0)
    (hζ_order : analyticOrderAt riemannZeta ρ = (n : ℕ∞))
    (hn : 1 ≤ n)
    (hh_an : AnalyticAt ℂ h ρ) :
    ∃ r > 0,
      ∮ z in C(ρ, r), weilIntegrand h z = -(2 * ↑π * I * (n : ℂ)) * h ρ := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := zero_factor_of_order hζ_an hζ_order
  -- Extract balls for each analyticity/nonvanishing condition.
  rw [Metric.eventually_nhds_iff_ball] at hfg
  obtain ⟨ε₁, hε₁_pos, hfg_ball⟩ := hfg
  obtain ⟨ε₂, hε₂_pos, hg_analyticOn⟩ := hg_an.exists_ball_analyticOnNhd
  have hg_ne_nhds : ∀ᶠ z in nhds ρ, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
  rw [Metric.eventually_nhds_iff_ball] at hg_ne_nhds
  obtain ⟨ε₃, hε₃_pos, hg_ne_ball⟩ := hg_ne_nhds
  obtain ⟨ε₄, hε₄_pos, hh_analyticOn⟩ := hh_an.exists_ball_analyticOnNhd
  set R := min (min ε₁ ε₂) (min ε₃ ε₄) with hR_def
  have hR_pos : 0 < R := by simp only [hR_def]; positivity
  set r := R / 2 with hr_def
  have hr_pos : 0 < r := by simp only [hr_def]; linarith
  have hr_lt_R : r < R := by simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  have hR_le_ε₁ : R ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR_le_ε₂ : R ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR_le_ε₃ : R ≤ ε₃ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR_le_ε₄ : R ≤ ε₄ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub_ε₁ : Metric.ball ρ R ⊆ Metric.ball ρ ε₁ := Metric.ball_subset_ball hR_le_ε₁
  have hsub_ε₂ : Metric.ball ρ R ⊆ Metric.ball ρ ε₂ := Metric.ball_subset_ball hR_le_ε₂
  have hsub_ε₃ : Metric.ball ρ R ⊆ Metric.ball ρ ε₃ := Metric.ball_subset_ball hR_le_ε₃
  have hsub_ε₄ : Metric.ball ρ R ⊆ Metric.ball ρ ε₄ := Metric.ball_subset_ball hR_le_ε₄
  have hfact_R : ∀ z ∈ Metric.ball ρ R, riemannZeta z = (z - ρ)^n * g z :=
    fun z hz => hfg_ball z (hsub_ε₁ hz)
  have hg_an_R : AnalyticOnNhd ℂ g (Metric.ball ρ R) :=
    fun z hz => hg_analyticOn z (hsub_ε₂ hz)
  have hg_ne_R : ∀ z ∈ Metric.ball ρ R, g z ≠ 0 :=
    fun z hz => hg_ne_ball z (hsub_ε₃ hz)
  have hh_an_R : AnalyticOnNhd ℂ h (Metric.ball ρ R) :=
    fun z hz => hh_analyticOn z (hsub_ε₄ hz)
  have hg_diff_R : DifferentiableOn ℂ g (Metric.ball ρ R) := hg_an_R.differentiableOn
  have hh_diff_R : DifferentiableOn ℂ h (Metric.ball ρ R) := hh_an_R.differentiableOn
  -- Sphere decomposition.
  have hdecomp := weilIntegrand_sphere_decomposition_from_factorization_of_order
    hn hr_pos hr_lt_R hfact_R hg_diff_R hg_ne_R hh_diff_R
  set φ : ℂ → ℂ := fun z => -h z * deriv g z / g z with hφ_def
  have hφ_an_R : AnalyticOnNhd ℂ φ (Metric.ball ρ R) := by
    intro z hz
    have hhz : AnalyticAt ℂ h z := hh_an_R z hz
    have hgz : AnalyticAt ℂ g z := hg_an_R z hz
    have hgz_ne : g z ≠ 0 := hg_ne_R z hz
    have hdgz : AnalyticAt ℂ (deriv g) z := hgz.deriv
    exact (hhz.neg.mul hdgz).div hgz hgz_ne
  have hclosedBall_sub_ball : Metric.closedBall ρ r ⊆ Metric.ball ρ R := fun z hz => by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr_lt_R
  have hball_sub_ball : Metric.ball ρ r ⊆ Metric.ball ρ R :=
    (Metric.ball_subset_closedBall).trans hclosedBall_sub_ball
  have hh_cont_closed : ContinuousOn h (Metric.closedBall ρ r) :=
    fun z hz => (hh_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hh_diff_ball : ∀ z ∈ Metric.ball ρ r, DifferentiableAt ℂ h z :=
    fun z hz => (hh_an_R z (hball_sub_ball hz)).differentiableAt
  have hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball ρ r) := by
    refine ⟨?_, ?_⟩
    · exact fun z hz => (hφ_an_R z (hball_sub_ball hz)).differentiableAt.differentiableWithinAt
    · rw [closure_ball ρ hr_pos.ne']
      exact fun z hz => (hφ_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  exact weilIntegrand_circle_integral_from_decomposition_of_order
    hr_pos hh_cont_closed hh_diff_ball hφ_diffcontoncl hdecomp

#print axioms weilIntegrand_circle_integral_at_zero_of_order

-- ═══════════════════════════════════════════════════════════════════════════
-- § Per-zero finite set version (generalizes cycle 41)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-zero circle integral, finite zero set, multiplicity-aware.** For any
finite set of zeros of `ζ` (each with a supplied natural-number multiplicity
`n(ρ) ≥ 1`), and for `h` analytic at each zero, there exists a per-zero radius
giving circle integral `−(2πi · n(ρ)) · h(ρ)`.

Unconditional replacement for cycle 41's `weil_circle_integral_per_zero` (which
took `deriv ζ ρ ≠ 0` as hypothesis). -/
theorem weil_circle_integral_per_zero_of_order
    (zeros : Finset ℂ) (n : ℂ → ℕ) (h : ℂ → ℂ)
    (hh_an : ∀ ρ ∈ zeros, AnalyticAt ℂ h ρ)
    (hζ_an : ∀ ρ ∈ zeros, AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : ∀ ρ ∈ zeros, riemannZeta ρ = 0)
    (hζ_order : ∀ ρ ∈ zeros, analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hn_ge : ∀ ρ ∈ zeros, 1 ≤ n ρ) :
    ∀ ρ ∈ zeros, ∃ r > 0,
      ∮ z in C(ρ, r), weilIntegrand h z = -(2 * ↑π * I * (n ρ : ℂ)) * h ρ := by
  intro ρ hρ
  exact weilIntegrand_circle_integral_at_zero_of_order
    (hζ_an ρ hρ) (hζ_zero ρ hρ) (hζ_order ρ hρ) (hn_ge ρ hρ) (hh_an ρ hρ)

#print axioms weil_circle_integral_per_zero_of_order

-- ═══════════════════════════════════════════════════════════════════════════
-- § Named target: `analyticOrderAt ζ ρ` is a positive natural at nontrivial zero
-- ═══════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════
-- § Identity theorem: `ζ` not eventually zero at any point of `{1}ᶜ`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`{1}ᶜ ⊂ ℂ` is preconnected.** Since ℂ has `Module.rank ℝ ℂ = 2 > 1`,
removing a single point leaves a connected set. -/
private lemma compl_one_isPreconnected : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) := by
  have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two
  exact (isConnected_compl_singleton_of_one_lt_rank h_rank 1).isPreconnected

/-- **ζ is analytic on `{1}ᶜ`**. Use that `DifferentiableOn` on open set ⟹ `AnalyticOnNhd`. -/
private lemma riemannZeta_analyticOnNhd_ne_one :
    AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
  have h_diff_on : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact h_diff_on.analyticOnNhd isOpen_compl_singleton

/-- **`ζ` is not eventually zero near any `ρ ≠ 1`.** Identity theorem on
`{1}ᶜ` + `ζ(2) ≠ 0` (since `Re 2 > 1`). -/
theorem riemannZeta_not_eventually_zero_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    ¬ (∀ᶠ z in nhds ρ, riemannZeta z = 0) := by
  intro h_eventually
  -- ζ analytic on {1}ᶜ, preconnected, eventually zero at ρ ∈ {1}ᶜ ⟹ ζ = 0 on {1}ᶜ.
  have hρ_mem : ρ ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := hρ
  have h_eqEq : riemannZeta =ᶠ[nhds ρ] 0 := by
    filter_upwards [h_eventually] with z hz using hz
  have h_eqOn := riemannZeta_analyticOnNhd_ne_one.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    compl_one_isPreconnected hρ_mem h_eqEq
  -- Evaluate at s = 2 ∈ {1}ᶜ; ζ(2) ≠ 0 by `riemannZeta_ne_zero_of_one_lt_re`.
  have h2_mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro h; have : (2 : ℂ) = 1 := h; norm_num at this
  have h_zeta_2 : riemannZeta (2 : ℂ) = 0 := h_eqOn h2_mem
  have h_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp : (1:ℝ) < (2:ℂ).re)
  exact h_ne h_zeta_2

#print axioms riemannZeta_not_eventually_zero_of_ne_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § Analytic order at nontrivial zero is a finite positive natural
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`analyticOrderAt ζ ρ` is a finite positive natural at every nontrivial
zero.** Unconditional.

Proof: (i) `ρ ∈ NontrivialZeros ⊂ {1}ᶜ` via `Re ρ < 1`, so ζ is analytic at ρ.
(ii) ζ is not eventually zero near ρ by `riemannZeta_not_eventually_zero_of_ne_one`,
so `analyticOrderAt ζ ρ ≠ ⊤`. (iii) `ζ ρ = 0` forces `analyticOrderAt ζ ρ ≠ 0`. -/
theorem analyticOrderAt_riemannZeta_nontrivialZero_pos_nat {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt riemannZeta ρ = (n : ℕ∞) := by
  rcases hρ with ⟨hRe_pos, hRe_lt_1, hρ_zero⟩
  have hρ_ne_1 : ρ ≠ 1 := by
    intro h; rw [h] at hRe_lt_1; simp at hRe_lt_1
  have hρ_ne_0 : ρ ≠ 0 := by
    intro h; rw [h] at hRe_pos; simp at hRe_pos
  have hζ_an : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticOnNhd_ne_one ρ hρ_ne_1
  -- `analyticOrderAt ζ ρ ≠ ⊤`: ζ not eventually zero at ρ.
  have h_not_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h_top
    rw [analyticOrderAt_eq_top] at h_top
    exact riemannZeta_not_eventually_zero_of_ne_one hρ_ne_1 h_top
  -- `analyticOrderAt ζ ρ ≠ 0`: ζ ρ = 0.
  have h_not_zero : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h_zero
    rw [analyticOrderAt_eq_zero] at h_zero
    rcases h_zero with h_not_an | h_ne
    · exact h_not_an hζ_an
    · exact h_ne hρ_zero
  -- Extract the underlying natural: `ℕ∞ = WithTop ℕ`; not `⊤` ⟹ is `some n`.
  obtain ⟨n, hn_eq⟩ := WithTop.ne_top_iff_exists.mp h_not_top
  -- `hn_eq : ↑n = analyticOrderAt riemannZeta ρ`.
  -- `n ≥ 1` since `analyticOrderAt ≠ 0`.
  have hn_ge_1 : 1 ≤ n := by
    by_contra h
    rw [not_le, Nat.lt_one_iff] at h
    subst h
    apply h_not_zero
    rw [← hn_eq]; rfl
  refine ⟨n, hn_ge_1, hn_eq.symm⟩

#print axioms analyticOrderAt_riemannZeta_nontrivialZero_pos_nat

/-- **Named target form** (`Prop`) for downstream callers. Unconditionally discharged. -/
def analyticOrderAt_riemannZeta_nontrivialZero_pos_nat_target : Prop :=
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt riemannZeta ρ = (n : ℕ∞)

theorem analyticOrderAt_riemannZeta_nontrivialZero_pos_nat_target_holds :
    analyticOrderAt_riemannZeta_nontrivialZero_pos_nat_target :=
  fun _ρ hρ => analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ

#print axioms analyticOrderAt_riemannZeta_nontrivialZero_pos_nat_target_holds

-- ═══════════════════════════════════════════════════════════════════════════
-- § Residue form at a zero of arbitrary order
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Analytic extension of `(h(s) - h(ρ))/(s - ρ)` at `ρ`.** (Duplicated from
`WeilRectangleDecomposition.lean` to avoid circular imports.) If `h` is
analytic at `ρ`, the difference quotient extends analytically. -/
private theorem diff_quotient_analyticAt_aux {h : ℂ → ℂ} {ρ : ℂ}
    (hh : AnalyticAt ℂ h ρ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, (h s - h ρ) / (s - ρ) = q s := by
  have hg_an : AnalyticAt ℂ (fun s => h s - h ρ) ρ := hh.sub analyticAt_const
  have hg_zero : (fun s => h s - h ρ) ρ = 0 := by simp
  have h_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (fun s => h s - h ρ) ρ := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_zero_order
    rw [hg_an.analyticOrderAt_eq_zero] at h_zero_order
    exact h_zero_order hg_zero
  obtain ⟨q, hq_an, hq_eq⟩ :=
    ((natCast_le_analyticOrderAt hg_an).mp h_order_ge_one)
  refine ⟨q, hq_an, ?_⟩
  have h_mono : (fun s : ℂ => h s - h ρ) =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      (fun s => (s - ρ) ^ 1 • q s) :=
    hq_eq.filter_mono nhdsWithin_le_nhds
  have h_sub_ne : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, s - ρ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero_of_ne hs
  filter_upwards [h_mono, h_sub_ne] with s hs hne
  simp only [pow_one, smul_eq_mul] at hs
  rw [hs]; field_simp

/-- **Residue form at a zero of order `n`.** At a zero `ρ` of `ζ` with
`analyticOrderAt ζ ρ = n ≥ 1`, and `h` analytic at ρ, the Weil integrand has
the Laurent expansion

```
weilIntegrand h s = −(n · h(ρ))/(s − ρ) + ψ(s)
```

on a punctured nhds of `ρ`, with `ψ` analytic at `ρ`. **Residue = −n·h(ρ)**.

Unconditional generalization of `weilIntegrand_residue_form_at_simple_zero`
from `WeilRectangleDecomposition.lean`. -/
theorem weilIntegrand_residue_form_at_zero_of_order
    {h : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : riemannZeta ρ = 0)
    (hζ_order : analyticOrderAt riemannZeta ρ = (n : ℕ∞))
    (hn : 1 ≤ n)
    (hh_an : AnalyticAt ℂ h ρ) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s = -(n : ℂ) * h ρ / (s - ρ) + ψ s := by
  -- From weilIntegrand_laurent_at_zero_of_order:
  -- weilIntegrand h s = -(n·(s-ρ)⁻¹ + g'/g) · h s on punctured nhds.
  obtain ⟨g, hg_an, hg_ne, h_laurent⟩ :=
    weilIntegrand_laurent_at_zero_of_order hζ_an hζ_zero hζ_order hn
  -- Difference-quotient extension: (h s - h ρ)/(s - ρ) = q s.
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt_aux hh_an
  -- Build ψ = -n · q - (g'/g) · h.
  -- Verification:
  --   -(n·(s-ρ)⁻¹ + g'/g) · h s
  -- = -n · h s / (s-ρ) - (g'/g) · h s
  -- = -n · [h(ρ) + (h s - h ρ)] / (s-ρ) - (g'/g) · h s
  -- = -n · h(ρ)/(s-ρ) - n · q s - (g'/g) · h s
  refine ⟨fun s => -(n : ℂ) * q s - deriv g s / g s * h s, ?_, ?_⟩
  · -- Analyticity: -n·q analytic; g'/g analytic (g ≠ 0); h analytic.
    have hq_neg_n : AnalyticAt ℂ (fun s => -(n : ℂ) * q s) ρ :=
      analyticAt_const.mul hq_an
    have hg_deriv_an : AnalyticAt ℂ (deriv g) ρ := hg_an.deriv
    have hg_div_an : AnalyticAt ℂ (fun s => deriv g s / g s) ρ :=
      hg_deriv_an.div hg_an hg_ne
    have hg_div_h_an : AnalyticAt ℂ (fun s => deriv g s / g s * h s) ρ :=
      hg_div_an.mul hh_an
    exact hq_neg_n.sub hg_div_h_an
  · filter_upwards [h_laurent, hq_eq, self_mem_nhdsWithin] with s hs hq_s hs_mem
    have hs_ne : s ≠ ρ := hs_mem
    have hsub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne
    rw [hs]
    -- hq_s : (h s - h ρ) / (s - ρ) = q s
    -- Want: -((n:ℂ)·(s-ρ)⁻¹ + g'/g) · h s = -n·h(ρ)/(s-ρ) + (-n·q s - g'/g · h s).
    have h_split : (h s : ℂ) = h ρ + (h s - h ρ) := by ring
    have h_q_mul : (h s - h ρ) = q s * (s - ρ) := by
      have := hq_s
      field_simp at this
      linear_combination this
    rw [h_split, h_q_mul]
    field_simp
    ring

#print axioms weilIntegrand_residue_form_at_zero_of_order

end Contour
end WeilPositivity
end ZD

end
