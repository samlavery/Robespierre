import Mathlib
import RequestProject.WeilContour

/-!
# Weil contour residue at the pole `s = 1`

This file packages the local analytic input coming from the simple pole of `ζ` at `1`.

The main results are:

* `zetaPoleRegularizer_analyticAt_one`: the removable extension of `(s - 1) * ζ(s)`;
* `weilIntegrand_residue_form_at_one`: the Laurent form of `weilIntegrand h` at `1`;
* `weilIntegrand_circle_integral_at_one`: the resulting small-circle integral
  `2πi * h(1)`.

These are unconditional and isolate the `s = 1` contribution needed by the
contour proof of the ξ-log-derivative partial fraction.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- The removable extension of `(s - 1) * ζ(s)` across the pole at `s = 1`. -/
def zetaPoleRegularizer : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

lemma zetaPoleRegularizer_at_one : zetaPoleRegularizer 1 = 1 := by
  simp [zetaPoleRegularizer]

lemma zetaPoleRegularizer_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaPoleRegularizer s = (s - 1) * riemannZeta s := by
  simp [zetaPoleRegularizer, Function.update_of_ne hs]

/-- The classical residue theorem `((s - 1) * ζ(s)) → 1` gives an analytic extension through
`1`. -/
theorem zetaPoleRegularizer_analyticAt_one : AnalyticAt ℂ zetaPoleRegularizer 1 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have h_eq_on :
        zetaPoleRegularizer =ᶠ[nhds z] fun s : ℂ => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_ne.mem_nhds hz] with s hs
      exact zetaPoleRegularizer_of_ne_one hs
    rw [h_eq_on.differentiableAt_iff]
    exact ((differentiableAt_id.sub_const (1 : ℂ)).mul (differentiableAt_riemannZeta hz))
  · simpa only [zetaPoleRegularizer, continuousAt_update_same] using riemannZeta_residue_one

/-- Analytic extension of `(h(s) - h(1)) / (s - 1)` at `1`. -/
private theorem diff_quotient_analyticAt_one {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 1) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 1 ∧
      ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), (h s - h 1) / (s - 1) = q s := by
  have hg_an : AnalyticAt ℂ (fun s => h s - h 1) (1 : ℂ) := hh.sub analyticAt_const
  have hg_zero : (fun s => h s - h 1) (1 : ℂ) = 0 := by simp
  have h_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (fun s => h s - h 1) (1 : ℂ) := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_zero_order
    rw [hg_an.analyticOrderAt_eq_zero] at h_zero_order
    exact h_zero_order hg_zero
  obtain ⟨q, hq_an, hq_eq⟩ := ((natCast_le_analyticOrderAt hg_an).mp h_order_ge_one)
  refine ⟨q, hq_an, ?_⟩
  have h_mono :
      (fun s : ℂ => h s - h 1) =ᶠ[nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ)]
        (fun s => (s - 1) ^ 1 • q s) :=
    hq_eq.filter_mono nhdsWithin_le_nhds
  have h_sub_ne : ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), s - 1 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero_of_ne hs
  filter_upwards [h_mono, h_sub_ne] with s hs hne
  simp only [pow_one, smul_eq_mul] at hs
  rw [hs]
  field_simp [hne]

/-- Local Laurent form of `weilIntegrand h` at the pole `s = 1` of `ζ`.

The residue coefficient is `+h(1)`. -/
theorem weilIntegrand_residue_form_at_one {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 1) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 1 ∧
      ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), weilIntegrand h s = h 1 / (s - 1) + ψ s := by
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt_one hh
  have hG_an : AnalyticAt ℂ zetaPoleRegularizer 1 := zetaPoleRegularizer_analyticAt_one
  have hG_ne : zetaPoleRegularizer 1 ≠ 0 := by simp [zetaPoleRegularizer_at_one]
  have hG_nonzero : ∀ᶠ s in nhds (1 : ℂ), zetaPoleRegularizer s ≠ 0 :=
    hG_an.continuousAt.eventually_ne hG_ne
  have hG_nonzero_punct :
      ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), zetaPoleRegularizer s ≠ 0 :=
    hG_nonzero.filter_mono nhdsWithin_le_nhds
  have hG_eq_punct :
      ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ),
        zetaPoleRegularizer s = (s - 1) * riemannZeta s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact zetaPoleRegularizer_of_ne_one hs
  have hG_deriv_punct :
      ∀ᶠ s in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ),
        deriv zetaPoleRegularizer s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have h_eq_on :
        zetaPoleRegularizer =ᶠ[nhds s] fun z : ℂ => (z - 1) * riemannZeta z := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz
      exact zetaPoleRegularizer_of_ne_one hz
    rw [h_eq_on.deriv_eq]
    have h_prod :
        HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
          (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
      exact ((hasDerivAt_id s).sub_const (1 : ℂ)).mul (differentiableAt_riemannZeta hs).hasDerivAt
    simpa [one_mul] using h_prod.deriv
  refine ⟨fun s => q s - deriv zetaPoleRegularizer s / zetaPoleRegularizer s * h s, ?_, ?_⟩
  · have h_log_an :
        AnalyticAt ℂ (fun s => deriv zetaPoleRegularizer s / zetaPoleRegularizer s) 1 := by
      exact hG_an.deriv.div hG_an hG_ne
    exact hq_an.sub (h_log_an.mul hh)
  · filter_upwards [hq_eq, hG_nonzero_punct, hG_eq_punct, hG_deriv_punct, self_mem_nhdsWithin]
      with s hq_s hG_ne_s hG_eq_s hG_deriv_s hs
    have hsub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
    have hζ_ne : riemannZeta s ≠ 0 := by
      intro hζ_zero
      rw [hG_eq_s, hζ_zero, mul_zero] at hG_ne_s
      exact hG_ne_s rfl
    have h_log :
        -(deriv riemannZeta s / riemannZeta s) =
          (s - 1)⁻¹ - deriv zetaPoleRegularizer s / zetaPoleRegularizer s := by
      rw [hG_deriv_s, hG_eq_s]
      field_simp [hsub_ne, hζ_ne]
      ring
    have h_polar :
        (s - 1)⁻¹ * h s = h 1 / (s - 1) + q s := by
      rw [← hq_s]
      field_simp [hsub_ne]
      ring
    unfold weilIntegrand
    rw [show -deriv riemannZeta s / riemannZeta s * h s =
      (-(deriv riemannZeta s / riemannZeta s)) * h s by ring]
    calc
      -(deriv riemannZeta s / riemannZeta s) * h s =
          ((s - 1)⁻¹ - deriv zetaPoleRegularizer s / zetaPoleRegularizer s) * h s := by
            rw [h_log]
      _ = (s - 1)⁻¹ * h s - deriv zetaPoleRegularizer s / zetaPoleRegularizer s * h s := by ring
      _ = h 1 / (s - 1) + q s - deriv zetaPoleRegularizer s / zetaPoleRegularizer s * h s := by
            rw [h_polar]
      _ = h 1 / (s - 1) +
          (q s - deriv zetaPoleRegularizer s / zetaPoleRegularizer s * h s) := by
            ring

/-- Small-circle integral at the pole `s = 1` of `ζ`. -/
theorem weilIntegrand_circle_integral_at_one {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 1) :
    ∃ r > 0, ∮ z in C((1 : ℂ), r), weilIntegrand h z = 2 * ↑Real.pi * I * h 1 := by
  obtain ⟨φ, hφ_an, hdecomp⟩ := weilIntegrand_residue_form_at_one hh
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hdecomp
  obtain ⟨ε₁, hε₁_pos, hdecomp_ball⟩ := hdecomp
  obtain ⟨ε₂, hε₂_pos, hh_an_ball⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨ε₃, hε₃_pos, hφ_an_ball⟩ := hφ_an.exists_ball_analyticOnNhd
  set R := min ε₁ (min ε₂ ε₃) with hR_def
  have hR_pos : 0 < R := by
    simp only [hR_def]
    positivity
  set r := R / 2 with hr_def
  have hr_pos : 0 < r := by
    simp only [hr_def]
    linarith
  have hr_lt_R : r < R := by
    simp only [hr_def]
    linarith
  refine ⟨r, hr_pos, ?_⟩
  have hR_le_ε₁ : R ≤ ε₁ := min_le_left _ _
  have hR_le_ε₂ : R ≤ ε₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR_le_ε₃ : R ≤ ε₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub_ε₁ : Metric.ball (1 : ℂ) R ⊆ Metric.ball (1 : ℂ) ε₁ := Metric.ball_subset_ball hR_le_ε₁
  have hsub_ε₂ : Metric.ball (1 : ℂ) R ⊆ Metric.ball (1 : ℂ) ε₂ := Metric.ball_subset_ball hR_le_ε₂
  have hsub_ε₃ : Metric.ball (1 : ℂ) R ⊆ Metric.ball (1 : ℂ) ε₃ := Metric.ball_subset_ball hR_le_ε₃
  have hh_an_R : AnalyticOnNhd ℂ h (Metric.ball (1 : ℂ) R) :=
    fun z hz => hh_an_ball z (hsub_ε₂ hz)
  have hφ_an_R : AnalyticOnNhd ℂ φ (Metric.ball (1 : ℂ) R) :=
    fun z hz => hφ_an_ball z (hsub_ε₃ hz)
  have hclosedBall_sub_ball : Metric.closedBall (1 : ℂ) r ⊆ Metric.ball (1 : ℂ) R := fun z hz => by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr_lt_R
  have hball_sub_ball : Metric.ball (1 : ℂ) r ⊆ Metric.ball (1 : ℂ) R :=
    (Metric.ball_subset_closedBall).trans hclosedBall_sub_ball
  have hdecomp_sphere :
      ∀ z ∈ Metric.sphere (1 : ℂ) r, weilIntegrand h z = h 1 / (z - 1) + φ z := by
    intro z hz
    have hz_dist : dist z (1 : ℂ) < ε₁ := by
      rw [Metric.mem_sphere] at hz
      exact lt_of_eq_of_lt hz (lt_of_lt_of_le hr_lt_R hR_le_ε₁)
    have hz_ne : z ≠ 1 := by
      intro hz_eq
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hr_pos.ne' hz.symm
    exact hdecomp_ball hz_dist (by simpa using hz_ne)
  have hh_cont_closed : ContinuousOn h (Metric.closedBall (1 : ℂ) r) := fun z hz =>
    (hh_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball (1 : ℂ) r) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hφ_an_R z (hball_sub_ball hz)).differentiableAt.differentiableWithinAt
    · rw [closure_ball 1 hr_pos.ne']
      intro z hz
      exact (hφ_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hφ_cont_closed : ContinuousOn φ (Metric.closedBall (1 : ℂ) r) := by
    rw [← closure_ball (1 : ℂ) hr_pos.ne']
    exact hφ_diffcontoncl.continuousOn
  have h_polar_cont_sphere :
      ContinuousOn (fun z : ℂ => h 1 / (z - 1)) (Metric.sphere (1 : ℂ) r) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const)
    · intro z hz
      exact sub_ne_zero_of_ne <| by
        intro hz_eq
        rw [hz_eq, Metric.mem_sphere, dist_self] at hz
        exact hr_pos.ne' hz.symm
  have h_polar_ci : CircleIntegrable (fun z : ℂ => h 1 / (z - 1)) (1 : ℂ) r :=
    h_polar_cont_sphere.circleIntegrable hr_pos.le
  have h_φ_ci : CircleIntegrable φ (1 : ℂ) r :=
    (hφ_cont_closed.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  rw [circleIntegral.integral_congr hr_pos.le hdecomp_sphere]
  rw [circleIntegral.integral_add h_polar_ci h_φ_ci]
  rw [hφ_diffcontoncl.circleIntegral_eq_zero hr_pos.le, add_zero]
  simpa using
    (polar_part_circle_integral (h := fun _ : ℂ => h 1) hr_pos continuousOn_const
      (fun _ _ => differentiableAt_const _))

end Contour
end WeilPositivity
end ZD

end
