import Mathlib
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilPoleAtOne
import RequestProject.XiOrder

/-!
# Hadamard kernel for the contour proof of ξ'/ξ partial fractions

This file packages the rational kernel
`K_s(z) = 1 / (s - z) + 1 / z`
that appears in the classical contour proof of Hadamard's partial fraction.

The goal here is modest but reusable:

* show `K_s` is analytic at every nontrivial zero `ρ` whenever `s ∉ NontrivialZeros`;
* identify the multiplicity at nontrivial zeros of `ζ` with `xiOrderNat`;
* specialize the existing multiplicity-aware Weil residue calculus to obtain the
  per-zero circle-integral formula for `weilIntegrand (K_s)`.

This is unconditional groundwork for a future upstream contour proof of H8.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- The classical Hadamard kernel used to probe `ξ'/ξ` by contour integration. -/
def hadamardKernel (s z : ℂ) : ℂ := 1 / (s - z) + 1 / z

/-- Off its two poles, the Hadamard kernel collapses to a single rational term. -/
theorem hadamardKernel_eq_div_mul {s z : ℂ} (hz : z ≠ 0) (hsz : s ≠ z) :
    hadamardKernel s z = s / (z * (s - z)) := by
  unfold hadamardKernel
  field_simp [hz, sub_ne_zero.mpr hsz]
  ring

/-- Tail bound for the Hadamard kernel once `z` dominates `s` in norm. -/
theorem hadamardKernel_norm_le_two_mul_norm_div_sq {s z : ℂ}
    (hz : z ≠ 0) (hsz : s ≠ z) (hlarge : 2 * ‖s‖ ≤ ‖z‖) :
    ‖hadamardKernel s z‖ ≤ 2 * ‖s‖ / ‖z‖ ^ 2 := by
  rw [hadamardKernel_eq_div_mul hz hsz, norm_div, norm_mul]
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hs_le : ‖s‖ ≤ ‖z‖ / 2 := by linarith
  have hsub_ge : ‖z‖ / 2 ≤ ‖s - z‖ := by
    calc
      ‖z‖ / 2 ≤ ‖z‖ - ‖s‖ := by linarith
      _ ≤ ‖z - s‖ := norm_sub_norm_le z s
      _ = ‖s - z‖ := by rw [norm_sub_rev]
  have hprod_ge : ‖z‖ * (‖z‖ / 2) ≤ ‖z‖ * ‖s - z‖ := by
    exact mul_le_mul_of_nonneg_left hsub_ge (norm_nonneg z)
  have hhalf_pos : 0 < ‖z‖ / 2 := by positivity
  have hsub_pos : 0 < ‖s - z‖ := lt_of_lt_of_le hhalf_pos hsub_ge
  have hprod_pos : 0 < ‖z‖ * ‖s - z‖ := mul_pos hz_pos hsub_pos
  have hz_sq_pos : 0 < ‖z‖ ^ 2 := by positivity
  have hden_ge : ‖z‖ ^ 2 / 2 ≤ ‖z‖ * ‖s - z‖ := by
    nlinarith
  rw [div_le_div_iff₀ hprod_pos hz_sq_pos]
  nlinarith [hden_ge, norm_nonneg s]

/-- `Gammaℝ` is analytic on the open right half-plane. -/
private theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  refine
    (((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul ?_)
  have hs_half_re : 0 < (s / 2).re := by
    simp
    linarith
  refine (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
    (differentiableAt_id.div_const (2 : ℂ))
  intro m hm
  rw [hm] at hs_half_re
  simp at hs_half_re
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  linarith

/-- `Gammaℝ` is analytic on the open right half-plane. -/
private theorem analyticAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hdiff : DifferentiableOn ℂ Complex.Gammaℝ U := by
    intro z hz
    exact (differentiableAt_Gammaℝ_of_re_pos hz).differentiableWithinAt
  exact hdiff.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

/-- `ζ` is analytic at every point with real part `< 1`; in particular at every
nontrivial zero. -/
private theorem riemannZeta_analyticAt_of_re_lt_one {ρ : ℂ} (hρ_re_lt_one : ρ.re < 1) :
    AnalyticAt ℂ riemannZeta ρ := by
  have hρ_ne_one : ρ ≠ 1 := by
    intro h
    rw [h] at hρ_re_lt_one
    simp at hρ_re_lt_one
  have h_diff_on : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact (h_diff_on.analyticOnNhd isOpen_compl_singleton) ρ hρ_ne_one

/-- At every nontrivial zero, the analytic multiplicity of `ζ` equals
`xiOrderNat`. -/
theorem analyticOrderAt_riemannZeta_eq_xiOrderNat {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    analyticOrderAt riemannZeta ρ = (ZD.xiOrderNat ρ : ℕ∞) := by
  rcases hρ with ⟨hρ_re_pos, hρ_re_lt_one, _hρ_zero⟩
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h
    rw [h] at hρ_re_pos
    simp at hρ_re_pos
  have hρ_ne_one : ρ ≠ 1 := by
    intro h
    rw [h] at hρ_re_lt_one
    simp at hρ_re_lt_one
  let p : ℂ → ℂ := fun z => z * (z - 1) / 2
  have hp_analytic : AnalyticAt ℂ p ρ := by
    show AnalyticAt ℂ (fun z => z * (z - 1) / 2) ρ
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const
      two_ne_zero)
  have hp_nonzero : p ρ ≠ 0 := by
    dsimp [p]
    exact div_ne_zero (mul_ne_zero hρ_ne_zero (sub_ne_zero.mpr hρ_ne_one)) two_ne_zero
  have hGamma_analytic : AnalyticAt ℂ Complex.Gammaℝ ρ :=
    analyticAt_Gammaℝ_of_re_pos hρ_re_pos
  have hGamma_nonzero : Complex.Gammaℝ ρ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hρ_re_pos
  have hζ_analytic : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticAt_of_re_lt_one hρ_re_lt_one
  have h_factorization :
      riemannXi =ᶠ[nhds ρ] fun z => p z * (Complex.Gammaℝ z * riemannZeta z) := by
    let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1}
    have hU_open : IsOpen U :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hρ_mem : ρ ∈ U := ⟨hρ_re_pos, hρ_re_lt_one⟩
    refine Filter.eventuallyEq_of_mem (hU_open.mem_nhds hρ_mem) ?_
    intro z hz
    have hz_ne_zero : z ≠ 0 := by
      intro h
      rw [h] at hz
      exact (lt_irrefl 0) hz.1
    have hz_ne_one : z ≠ 1 := by
      intro h
      rw [h] at hz
      exact (lt_irrefl 1) hz.2
    have hGamma_nonzero_z : Complex.Gammaℝ z ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos hz.1
    have hzeta_def : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z :=
      riemannZeta_def_of_ne_zero hz_ne_zero
    have hcompleted :
        completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
      rw [hzeta_def]
      field_simp [hGamma_nonzero_z]
    calc
      riemannXi z = (z * (z - 1) / 2) * completedRiemannZeta z :=
        riemannXi_eq_classical_of_ne_zero_of_ne_one z hz_ne_zero hz_ne_one
      _ = p z * (Complex.Gammaℝ z * riemannZeta z) := by
        simp [p, hcompleted]
  have h_xi_order : analyticOrderAt riemannXi ρ = (ZD.xiOrderNat ρ : ℕ∞) := by
    unfold ZD.xiOrderNat analyticOrderNatAt
    exact (ENat.coe_toNat (ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ)).symm
  have hGamma_mul_order :
      analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ =
        analyticOrderAt riemannZeta ρ := by
    calc
      analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ
          = analyticOrderAt Complex.Gammaℝ ρ + analyticOrderAt riemannZeta ρ := by
              simpa using (analyticOrderAt_mul hGamma_analytic hζ_analytic)
      _ = analyticOrderAt riemannZeta ρ := by
            rw [(hGamma_analytic.analyticOrderAt_eq_zero).mpr hGamma_nonzero, zero_add]
  have hp_mul_order :
      analyticOrderAt (fun z => p z * (Complex.Gammaℝ z * riemannZeta z)) ρ =
        analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ := by
    calc
      analyticOrderAt (fun z => p z * (Complex.Gammaℝ z * riemannZeta z)) ρ
          = analyticOrderAt p ρ +
              analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ := by
                simpa using (analyticOrderAt_mul hp_analytic (hGamma_analytic.mul hζ_analytic))
      _ = analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ := by
            rw [(hp_analytic.analyticOrderAt_eq_zero).mpr hp_nonzero, zero_add]
  calc
    analyticOrderAt riemannZeta ρ =
        analyticOrderAt (fun z => Complex.Gammaℝ z * riemannZeta z) ρ := by
      symm
      exact hGamma_mul_order
    _ = analyticOrderAt (fun z => p z * (Complex.Gammaℝ z * riemannZeta z)) ρ := by
      symm
      exact hp_mul_order
    _ = analyticOrderAt riemannXi ρ := by
      symm
      exact analyticOrderAt_congr h_factorization
    _ = (ZD.xiOrderNat ρ : ℕ∞) := h_xi_order

/-- The Hadamard kernel is analytic at every point away from its two poles
`0` and `s`. -/
theorem hadamardKernel_analyticAt {s ρ : ℂ} (hsρ : s ≠ ρ) (hρ0 : ρ ≠ 0) :
    AnalyticAt ℂ (hadamardKernel s) ρ := by
  unfold hadamardKernel
  have h_left : AnalyticAt ℂ (fun z : ℂ => 1 / (s - z)) ρ := by
    simpa [one_div] using
      (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hsρ)
  have h_right : AnalyticAt ℂ (fun z : ℂ => 1 / z) ρ := by
    simpa [one_div] using analyticAt_id.inv hρ0
  exact h_left.add h_right

/-- Specialization: for fixed `s ∉ NontrivialZeros`, the Hadamard kernel is
analytic at every nontrivial zero `ρ`. -/
theorem hadamardKernel_analyticAt_nontrivialZero {s ρ : ℂ} (hs : s ∉ NontrivialZeros)
    (hρ : ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardKernel s) ρ := by
  have hρ_nonzero : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    simp [NontrivialZeros] at hρ
  have hsρ : s ≠ ρ := by
    intro h
    apply hs
    simpa [h] using hρ
  exact hadamardKernel_analyticAt hsρ hρ_nonzero

private theorem logDeriv_riemannZeta_analyticAt {s : ℂ}
    (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (fun z => -deriv riemannZeta z / riemannZeta z) s := by
  have h_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζ_an : AnalyticAt ℂ riemannZeta s :=
    (h_diff_on.analyticOnNhd isOpen_compl_singleton) s hs1
  exact hζ_an.deriv.neg.div hζ_an hsζ

private theorem diff_quotient_analyticAt {h : ℂ → ℂ} {ρ : ℂ} (hh : AnalyticAt ℂ h ρ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q ρ ∧
      ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, (h z - h ρ) / (z - ρ) = q z := by
  have hg_an : AnalyticAt ℂ (fun z => h z - h ρ) ρ := hh.sub analyticAt_const
  have hg_zero : (fun z => h z - h ρ) ρ = 0 := by simp
  have h_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (fun z => h z - h ρ) ρ := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_zero_order
    rw [hg_an.analyticOrderAt_eq_zero] at h_zero_order
    exact h_zero_order hg_zero
  obtain ⟨q, hq_an, hq_eq⟩ :=
    ((natCast_le_analyticOrderAt hg_an).mp h_order_ge_one)
  refine ⟨q, hq_an, ?_⟩
  have h_mono : (fun z : ℂ => h z - h ρ) =ᶠ[nhdsWithin ρ {ρ}ᶜ]
      (fun z => (z - ρ) ^ 1 • q z) :=
    hq_eq.filter_mono nhdsWithin_le_nhds
  have h_sub_ne : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, z - ρ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero_of_ne hz
  filter_upwards [h_mono, h_sub_ne] with z hz hne
  simp only [pow_one, smul_eq_mul] at hz
  rw [hz]
  field_simp [hne]

/-- At the kernel pole `z = 0`, the Hadamard-kernel Weil integrand has residue
`-ζ'(0) / ζ(0)`. -/
theorem weilIntegrand_residue_form_hadamardKernel_at_zero
    {s : ℂ} (hs0 : s ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧
      ∀ᶠ z in nhdsWithin 0 {0}ᶜ,
        weilIntegrand (hadamardKernel s) z =
          (-(deriv riemannZeta 0 / riemannZeta 0)) / z + ψ z := by
  let a : ℂ → ℂ := fun z => -deriv riemannZeta z / riemannZeta z
  have hζ0_ne : riemannZeta 0 ≠ 0 := by
    rw [zeta_at_zero]
    norm_num
  have ha_an : AnalyticAt ℂ a 0 := logDeriv_riemannZeta_analyticAt zero_ne_one hζ0_ne
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt ha_an
  have hs_ne_punct : ∀ᶠ z in nhdsWithin 0 {0}ᶜ, z ≠ s := by
    have hs_ne : ∀ᶠ z in nhds 0, z ≠ s := by
      filter_upwards [isOpen_ne.mem_nhds hs0.symm] with z hz
      simpa [eq_comm] using hz
    exact hs_ne.filter_mono nhdsWithin_le_nhds
  refine ⟨fun z => q z + a z / (s - z), ?_, ?_⟩
  · exact hq_an.add (ha_an.div (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hs0))
  · filter_upwards [hq_eq, hs_ne_punct, self_mem_nhdsWithin] with z hq hzs hz0
    have hz_ne : z ≠ 0 := hz0
    have hmain : a z * (1 / (s - z) + 1 / z) = a 0 / z + (q z + a z / (s - z)) := by
      calc
        a z * (1 / (s - z) + 1 / z) = a z / (s - z) + a z / z := by
          simp [div_eq_mul_inv, mul_add]
        _ = a z / (s - z) + (a 0 / z + q z) := by
          rw [show a z / z = a 0 / z + q z by
            have hq0 : (a z - a 0) / z = q z := by
              simpa using hq
            calc
              a z / z = a 0 / z + (a z - a 0) / z := by
                field_simp [hz_ne]
                ring
              _ = a 0 / z + q z := by rw [hq0]]
        _ = a 0 / z + (q z + a z / (s - z)) := by
          ring
    unfold weilIntegrand hadamardKernel
    calc
      -deriv riemannZeta z / riemannZeta z * (1 / (s - z) + 1 / z) =
          -deriv riemannZeta 0 / riemannZeta 0 / z +
            (q z + -deriv riemannZeta z / riemannZeta z / (s - z)) := by
              simpa [a] using hmain
      _ =
          (-(deriv riemannZeta 0 / riemannZeta 0)) / z +
            (q z + -deriv riemannZeta z / riemannZeta z / (s - z)) := by
              ring

/-- The Hadamard kernel captures its pole contribution at `z = 0`. -/
theorem weilIntegrand_circle_integral_hadamardKernel_at_zero
    {s : ℂ} (hs0 : s ≠ 0) :
    ∃ r > 0,
      ∮ z in C(0, r), weilIntegrand (hadamardKernel s) z =
        2 * ↑Real.pi * I * (-(deriv riemannZeta 0 / riemannZeta 0)) := by
  obtain ⟨φ, hφ_an, hdecomp⟩ := weilIntegrand_residue_form_hadamardKernel_at_zero hs0
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hdecomp
  obtain ⟨ε₁, hε₁_pos, hdecomp_ball⟩ := hdecomp
  obtain ⟨ε₂, hε₂_pos, hφ_an_ball⟩ := hφ_an.exists_ball_analyticOnNhd
  set R := min ε₁ ε₂ with hR_def
  have hR_pos : 0 < R := by
    simp [hR_def, hε₁_pos, hε₂_pos]
  set r := R / 2 with hr_def
  have hr_pos : 0 < r := by
    simp [hr_def]
    linarith
  have hr_lt_R : r < R := by
    simp [hr_def]
    linarith
  refine ⟨r, hr_pos, ?_⟩
  have hR_le_ε₁ : R ≤ ε₁ := min_le_left _ _
  have hR_le_ε₂ : R ≤ ε₂ := min_le_right _ _
  have hsub_ε₂ : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) ε₂ :=
    Metric.ball_subset_ball hR_le_ε₂
  have hφ_an_R : AnalyticOnNhd ℂ φ (Metric.ball (0 : ℂ) R) := by
    intro z hz
    exact hφ_an_ball z (hsub_ε₂ hz)
  have hclosedBall_sub_ball : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R := fun z hz => by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr_lt_R
  have hball_sub_ball : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) R :=
    (Metric.ball_subset_closedBall.trans hclosedBall_sub_ball)
  have hdecomp_sphere :
      ∀ z ∈ Metric.sphere (0 : ℂ) r,
        weilIntegrand (hadamardKernel s) z =
          (-(deriv riemannZeta 0 / riemannZeta 0)) / z + φ z := by
    intro z hz
    have hz_dist : dist z (0 : ℂ) < ε₁ := by
      rw [Metric.mem_sphere] at hz
      exact lt_of_eq_of_lt hz (lt_of_lt_of_le hr_lt_R hR_le_ε₁)
    have hz_ne : z ≠ 0 := by
      intro hz_eq
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hr_pos.ne' hz.symm
    exact hdecomp_ball hz_dist (by simpa using hz_ne)
  have hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball (0 : ℂ) r) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hφ_an_R z (hball_sub_ball hz)).differentiableAt.differentiableWithinAt
    · rw [closure_ball 0 hr_pos.ne']
      intro z hz
      exact (hφ_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hφ_cont_closed : ContinuousOn φ (Metric.closedBall (0 : ℂ) r) := by
    rw [← closure_ball (0 : ℂ) hr_pos.ne']
    exact hφ_diffcontoncl.continuousOn
  have h_polar_cont_sphere :
      ContinuousOn
        (fun z : ℂ => (-(deriv riemannZeta 0 / riemannZeta 0)) / z)
        (Metric.sphere (0 : ℂ) r) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id
    · intro z hz
      intro hz0
      have hz_eq : z = 0 := by simpa using hz0
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hr_pos.ne' hz.symm
  have h_polar_ci :
      CircleIntegrable
        (fun z : ℂ => (-(deriv riemannZeta 0 / riemannZeta 0)) / z)
        (0 : ℂ) r :=
    h_polar_cont_sphere.circleIntegrable hr_pos.le
  have h_φ_ci : CircleIntegrable φ (0 : ℂ) r :=
    (hφ_cont_closed.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  rw [circleIntegral.integral_congr hr_pos.le hdecomp_sphere]
  rw [circleIntegral.integral_add h_polar_ci h_φ_ci]
  rw [hφ_diffcontoncl.circleIntegral_eq_zero hr_pos.le, add_zero]
  simpa using
    (polar_part_circle_integral
      (ρ := (0 : ℂ))
      (h := fun _ : ℂ => -(deriv riemannZeta 0 / riemannZeta 0))
      hr_pos continuousOn_const (fun _ _ => differentiableAt_const _))

/-- At the kernel pole `z = s`, the Hadamard-kernel Weil integrand has residue
`ζ'(s) / ζ(s)`. -/
theorem weilIntegrand_residue_form_hadamardKernel_at_self
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ s ∧
      ∀ᶠ z in nhdsWithin s {s}ᶜ,
        weilIntegrand (hadamardKernel s) z =
          deriv riemannZeta s / riemannZeta s / (z - s) + ψ z := by
  let a : ℂ → ℂ := fun z => -deriv riemannZeta z / riemannZeta z
  have ha_an : AnalyticAt ℂ a s := logDeriv_riemannZeta_analyticAt hs1 hsζ
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt ha_an
  have hnot0_punct : ∀ᶠ z in nhdsWithin s {s}ᶜ, z ≠ 0 := by
    have hnot0 : ∀ᶠ z in nhds s, z ≠ 0 := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hs0] with z hz
      simpa using hz
    exact hnot0.filter_mono nhdsWithin_le_nhds
  refine ⟨fun z => -q z + a z / z, ?_, ?_⟩
  · have ha_div_id : AnalyticAt ℂ (fun z => a z / z) s := ha_an.div analyticAt_id hs0
    exact hq_an.neg.add ha_div_id
  · filter_upwards [hq_eq, self_mem_nhdsWithin, hnot0_punct] with z hq hz hz0
    have hz_ne : z ≠ s := hz
    have hsub_ne : z - s ≠ 0 := sub_ne_zero_of_ne hz_ne
    have hq_mul : a z - a s = q z * (z - s) := by
      have hq' := hq
      field_simp [hsub_ne] at hq'
      linear_combination hq'
    have hself :
        a z / (s - z) = deriv riemannZeta s / riemannZeta s / (z - s) - q z := by
      have h_as : -a s = deriv riemannZeta s / riemannZeta s := by
        change -(-deriv riemannZeta s / riemannZeta s) = deriv riemannZeta s / riemannZeta s
        ring_nf
      calc
        a z / (s - z) = a z / (-(z - s)) := by congr 1; ring
        _ = -(a z / (z - s)) := by rw [div_neg]
        _ = -(a s / (z - s) + (a z - a s) / (z - s)) := by
          field_simp [hsub_ne]
          ring
        _ = -a s / (z - s) - (a z - a s) / (z - s) := by ring
        _ = -a s / (z - s) - q z := by rw [hq]
        _ = deriv riemannZeta s / riemannZeta s / (z - s) - q z := by rw [h_as]
    change a z * (1 / (s - z) + 1 / z) =
      deriv riemannZeta s / riemannZeta s / (z - s) + (-q z + a z / z)
    calc
      a z * (1 / (s - z) + 1 / z) = a z / (s - z) + a z / z := by
        simp [div_eq_mul_inv, mul_add]
      _ = deriv riemannZeta s / riemannZeta s / (z - s) - q z + a z / z := by
        rw [hself]
      _ = deriv riemannZeta s / riemannZeta s / (z - s) + (-q z + a z / z) := by
        ring

/-- The Hadamard kernel captures its own pole contribution at `z = s`. -/
theorem weilIntegrand_circle_integral_hadamardKernel_at_self
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0) :
    ∃ r > 0,
      ∮ z in C(s, r), weilIntegrand (hadamardKernel s) z =
        2 * ↑Real.pi * I * (deriv riemannZeta s / riemannZeta s) := by
  obtain ⟨φ, hφ_an, hdecomp⟩ :=
    weilIntegrand_residue_form_hadamardKernel_at_self hs0 hs1 hsζ
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hdecomp
  obtain ⟨ε₁, hε₁_pos, hdecomp_ball⟩ := hdecomp
  obtain ⟨ε₂, hε₂_pos, hφ_an_ball⟩ := hφ_an.exists_ball_analyticOnNhd
  set R := min ε₁ ε₂ with hR_def
  have hR_pos : 0 < R := by
    simp [hR_def, hε₁_pos, hε₂_pos]
  set r := R / 2 with hr_def
  have hr_pos : 0 < r := by
    simp [hr_def]
    linarith
  have hr_lt_R : r < R := by
    simp [hr_def]
    linarith
  refine ⟨r, hr_pos, ?_⟩
  have hR_le_ε₁ : R ≤ ε₁ := min_le_left _ _
  have hR_le_ε₂ : R ≤ ε₂ := min_le_right _ _
  have hsub_ε₂ : Metric.ball s R ⊆ Metric.ball s ε₂ :=
    Metric.ball_subset_ball hR_le_ε₂
  have hφ_an_R : AnalyticOnNhd ℂ φ (Metric.ball s R) := by
    intro z hz
    exact hφ_an_ball z (hsub_ε₂ hz)
  have hclosedBall_sub_ball : Metric.closedBall s r ⊆ Metric.ball s R := fun z hz => by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr_lt_R
  have hball_sub_ball : Metric.ball s r ⊆ Metric.ball s R :=
    (Metric.ball_subset_closedBall.trans hclosedBall_sub_ball)
  have hdecomp_sphere :
      ∀ z ∈ Metric.sphere s r,
        weilIntegrand (hadamardKernel s) z =
          deriv riemannZeta s / riemannZeta s / (z - s) + φ z := by
    intro z hz
    have hz_dist : dist z s < ε₁ := by
      rw [Metric.mem_sphere] at hz
      exact lt_of_eq_of_lt hz (lt_of_lt_of_le hr_lt_R hR_le_ε₁)
    have hz_ne : z ≠ s := by
      intro hz_eq
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hr_pos.ne' hz.symm
    exact hdecomp_ball hz_dist (by simpa using hz_ne)
  have hφ_diffcontoncl : DiffContOnCl ℂ φ (Metric.ball s r) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hφ_an_R z (hball_sub_ball hz)).differentiableAt.differentiableWithinAt
    · rw [closure_ball s hr_pos.ne']
      intro z hz
      exact (hφ_an_R z (hclosedBall_sub_ball hz)).continuousAt.continuousWithinAt
  have hφ_cont_closed : ContinuousOn φ (Metric.closedBall s r) := by
    rw [← closure_ball s hr_pos.ne']
    exact hφ_diffcontoncl.continuousOn
  have h_polar_cont_sphere :
      ContinuousOn
        (fun z : ℂ => deriv riemannZeta s / riemannZeta s / (z - s))
        (Metric.sphere s r) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const)
    · intro z hz
      exact sub_ne_zero_of_ne <| by
        intro hz_eq
        rw [hz_eq, Metric.mem_sphere, dist_self] at hz
        exact hr_pos.ne' hz.symm
  have h_polar_ci :
      CircleIntegrable
        (fun z : ℂ => deriv riemannZeta s / riemannZeta s / (z - s)) s r :=
    h_polar_cont_sphere.circleIntegrable hr_pos.le
  have h_φ_ci : CircleIntegrable φ s r :=
    (hφ_cont_closed.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  rw [circleIntegral.integral_congr hr_pos.le hdecomp_sphere]
  rw [circleIntegral.integral_add h_polar_ci h_φ_ci]
  rw [hφ_diffcontoncl.circleIntegral_eq_zero hr_pos.le, add_zero]
  simpa using
    (polar_part_circle_integral
      (h := fun _ : ℂ => deriv riemannZeta s / riemannZeta s)
      hr_pos continuousOn_const (fun _ _ => differentiableAt_const _))

/-- Per-zero residue formula for the Hadamard kernel: at every nontrivial zero
`ρ`, the circle integral of `weilIntegrand (K_s)` is the multiplicity-weighted
term expected in the partial fraction proof. -/
theorem weilIntegrand_circle_integral_hadamardKernel_at_nontrivial_zero
    {s ρ : ℂ} (hs : s ∉ NontrivialZeros) (hρ : ρ ∈ NontrivialZeros) :
    ∃ r > 0,
      ∮ z in C(ρ, r), weilIntegrand (hadamardKernel s) z =
        -(2 * ↑Real.pi * I * (ZD.xiOrderNat ρ : ℂ)) * hadamardKernel s ρ := by
  have hρ_mem : ρ ∈ NontrivialZeros := hρ
  rcases hρ with ⟨_hρ_re_pos, hρ_re_lt_one, hρ_zero⟩
  have hζ_analytic : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticAt_of_re_lt_one hρ_re_lt_one
  simpa using
    (weilIntegrand_circle_integral_at_zero_of_order hζ_analytic hρ_zero
      (analyticOrderAt_riemannZeta_eq_xiOrderNat hρ_mem)
      (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ_mem))
      (hadamardKernel_analyticAt_nontrivialZero hs hρ_mem))

/-- The Hadamard kernel also captures the pole contribution at `s = 1`. -/
theorem weilIntegrand_circle_integral_hadamardKernel_at_one {s : ℂ} (hs : s ≠ 1) :
    ∃ r > 0,
      ∮ z in C(1, r), weilIntegrand (hadamardKernel s) z =
        2 * ↑Real.pi * I * hadamardKernel s 1 := by
  exact weilIntegrand_circle_integral_at_one
    (hadamardKernel_analyticAt (s := s) (ρ := 1) hs one_ne_zero)

end Contour
end WeilPositivity
end ZD

end
