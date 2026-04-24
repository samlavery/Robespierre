import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilContour
import RequestProject.WeilPairTestContinuity

/-!
# Extending `pairTestMellin` analyticity to `Re s > -4`

`pair β t = 4·sinh²(a·t)·sinh²(b·t)·ψ²(t) = O(t⁴)` near `0+`. Combined with
exp decay at `∞` + local integrability, Mathlib's
`mellin_differentiableAt_of_isBigO_rpow_exp` extends differentiability to
`Re s > -4`.
-/

open Complex Set Filter MeasureTheory Real Asymptotics

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

private lemma sinh_isBigO_id_nhds_zero_real :
    Asymptotics.IsBigO (nhds (0:ℝ)) Real.sinh (fun x : ℝ => x) := by
  have h : HasDerivAt Real.sinh 1 0 := by
    simpa [Real.cosh_zero] using Real.hasDerivAt_sinh 0
  have hsub := h.isBigO_sub
  simpa [Real.sinh_zero, sub_zero] using hsub

private lemma sinh_mul_isBigO_id_nhds_zero_real (c : ℝ) :
    Asymptotics.IsBigO (nhds (0:ℝ))
      (fun t : ℝ => Real.sinh (c * t)) (fun t : ℝ => t) := by
  have h_tendsto : Tendsto (fun t : ℝ => c * t) (nhds (0:ℝ)) (nhds (0:ℝ)) := by
    have : Continuous (fun t : ℝ => c * t) := by fun_prop
    have := this.tendsto 0
    simpa using this
  have h1 := sinh_isBigO_id_nhds_zero_real.comp_tendsto h_tendsto
  -- h1 : (fun t => sinh (c*t)) =O[𝓝 0] (fun t => c*t)
  have h2 : Asymptotics.IsBigO (nhds (0:ℝ)) (fun t : ℝ => c * t) (fun t : ℝ => t) :=
    (Asymptotics.isBigO_refl (fun t : ℝ => t) (nhds (0:ℝ))).const_mul_left c
  exact h1.trans h2

private lemma sinh_sq_mul_isBigO_sq_nhds_zero_real (c : ℝ) :
    Asymptotics.IsBigO (nhds (0:ℝ))
      (fun t : ℝ => Real.sinh (c * t) ^ 2) (fun t : ℝ => t ^ 2) := by
  have h := sinh_mul_isBigO_id_nhds_zero_real c
  have hh := h.mul h
  simpa [pow_two] using hh

private lemma psi_gaussian_sq_isBigO_one_nhds_zero_real :
    Asymptotics.IsBigO (nhds (0:ℝ))
      (fun t : ℝ => (ψ_gaussian t) ^ 2) (fun _ : ℝ => (1 : ℝ)) := by
  have h_cont : Continuous (fun t : ℝ => (ψ_gaussian t) ^ 2) := by
    unfold ψ_gaussian; fun_prop
  have h_tendsto := h_cont.tendsto 0
  refine (h_tendsto.isBigO_one ℝ)

/-- **Pair test is `O(t⁴)` near `t = 0+`** (cast to ℂ). -/
theorem pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero (β : ℝ) :
    Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Ioi 0))
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ))
      (fun t : ℝ => t ^ ((4:ℝ))) := by
  set a : ℝ := 1/2 - Real.pi/6
  set b : ℝ := β - 1/2
  have h_eq : (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) =
      fun t : ℝ => ((4 * Real.sinh (a * t)^2 *
        Real.sinh (b * t)^2 * (ψ_gaussian t)^2 : ℝ) : ℂ) := by
    funext t
    congr 1
    exact pair_cosh_gauss_test_sinh_factor β t
  rw [h_eq]
  have h_sa := sinh_sq_mul_isBigO_sq_nhds_zero_real a
  have h_sb := sinh_sq_mul_isBigO_sq_nhds_zero_real b
  have h_psi := psi_gaussian_sq_isBigO_one_nhds_zero_real
  have h_prod :
      Asymptotics.IsBigO (nhds (0:ℝ))
        (fun t : ℝ => (4 : ℝ) * Real.sinh (a * t) ^ 2 *
          Real.sinh (b * t) ^ 2 * (ψ_gaussian t) ^ 2)
        (fun t : ℝ => t ^ 2 * t ^ 2 * (1 : ℝ)) := by
    have h1 : Asymptotics.IsBigO (nhds (0:ℝ))
        (fun t : ℝ => (4 : ℝ) * Real.sinh (a * t) ^ 2) (fun t : ℝ => t ^ 2) :=
      h_sa.const_mul_left 4
    exact (h1.mul h_sb).mul h_psi
  have h_simp : (fun t : ℝ => t ^ 2 * t ^ 2 * (1 : ℝ)) = (fun t : ℝ => t ^ 4) := by
    funext t; ring
  rw [h_simp] at h_prod
  -- Cast to ℂ.
  have h_prod_C :
      Asymptotics.IsBigO (nhds (0:ℝ))
        (fun t : ℝ => (((4 : ℝ) * Real.sinh (a * t) ^ 2 *
          Real.sinh (b * t) ^ 2 * (ψ_gaussian t) ^ 2 : ℝ) : ℂ))
        (fun t : ℝ => ((t ^ 4 : ℝ) : ℂ)) := by
    refine (Complex.isBigO_ofReal_left).mpr ?_
    refine h_prod.trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, Complex.norm_real]
    simp [Real.norm_eq_abs]
  have h_restrict : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Ioi 0))
      (fun t : ℝ => (((4 : ℝ) * Real.sinh (a * t) ^ 2 *
          Real.sinh (b * t) ^ 2 * (ψ_gaussian t) ^ 2 : ℝ) : ℂ))
      (fun t : ℝ => ((t ^ 4 : ℝ) : ℂ)) :=
    h_prod_C.mono (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhds 0)
  refine h_restrict.trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : (0 : ℝ) < t := ht
  have h_rpow_eq : (t : ℝ) ^ ((4 : ℝ)) = t ^ (4 : ℕ) := by
    rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ t^4),
      Real.norm_of_nonneg (Real.rpow_nonneg ht_pos.le _), h_rpow_eq]
  linarith

#print axioms pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero

theorem pair_cosh_gauss_test_locallyIntegrableOn_ofReal (β : ℝ) :
    LocallyIntegrableOn
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) (Ioi 0) := by
  have h_cont : Continuous
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (pair_cosh_gauss_test_continuous β)
  exact h_cont.locallyIntegrable.locallyIntegrableOn (Ioi 0)

/-- **Extended differentiability of `pairTestMellin β`** to `Re s > -4`. -/
theorem pairTestMellin_differentiableAt_re_gt_neg_four
    (β : ℝ) {s : ℂ} (hs : -4 < s.re) :
    DifferentiableAt ℂ (pairTestMellin β) s := by
  unfold pairTestMellin
  have h_top : Asymptotics.IsBigO atTop
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ))
      (fun t : ℝ => Real.exp (-1 * t)) := by
    have h := pair_cosh_gauss_test_isBigO_exp_neg_atTop β
    refine h.congr_right (fun t => ?_)
    simp [neg_mul, one_mul]
  have h_bot : Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Ioi 0))
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ))
      (fun t : ℝ => t ^ (-((-4 : ℝ)))) := by
    have h := pair_cosh_gauss_test_isBigO_rpow_four_nhdsGT_zero β
    refine h.congr_right (fun t => ?_)
    congr 1
    norm_num
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) zero_lt_one
    (pair_cosh_gauss_test_locallyIntegrableOn_ofReal β) h_top h_bot hs

#print axioms pairTestMellin_differentiableAt_re_gt_neg_four

end Contour
end WeilPositivity
end ZD

end
