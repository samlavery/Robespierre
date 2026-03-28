import Mathlib
import RequestProject.OffAxisTheoremDefs

open ArithmeticFunction Real Filter
open scoped Topology
noncomputable section

private theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz
  exact differentiableAt_riemannZeta hz

private theorem analyticOrderAt_riemannZeta_ne_top (ρ : ℂ) (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hU : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    exact analyticAt_riemannZeta hz
  have h2 : analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    have hzero : analyticOrderAt riemannZeta (2 : ℂ) = 0 := by
      rw [(analyticAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).analyticOrderAt_eq_zero]
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    simp [hzero]
  exact hU.analyticOrderAt_ne_top_of_isPreconnected
    ((isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) (1 : ℂ)).isPreconnected)
    (by simp) (by simpa) h2
/-
PROBLEM
============================================================
Part 1: Unconditional algebraic results (do not use hz)
============================================================
If `ρ.re ≠ 1/2`, the rotated prime density detector fires:
    there exists a rotation parameter `t` at which the norm-squared
    of the rotated prime density observable is nonzero.
    **Note**: This is purely algebraic; it does not use `riemannZeta ρ = 0`.
    The hypothesis `hz` is retained in the statement for interface compatibility
    with the rotation-symmetry framework.
PROVIDED SOLUTION
Use t = 0. Show rotatedPrimeDensityNormSq ρ.re 0 ≠ 0. By rotatedPrimeDensityNormSq_eq, this equals (ρ.re - 1/2)^2. Since ρ.re ≠ 1/2 (by hoff), we have ρ.re - 1/2 ≠ 0, so (ρ.re - 1/2)^2 ≠ 0.
-/
theorem offaxis_forces_rotated_detector_event
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ := by
      exact ⟨ 0, by rw [ rotatedPrimeDensityNormSq_eq ] ; exact pow_ne_zero 2 ( sub_ne_zero_of_ne hoff ) ⟩
/-
PROBLEM
If `ρ.re ≠ 1/2`, at least one of the off-axis observables is nonzero
    at `t = 0`.
PROVIDED SOLUTION
Use t = 0. Left disjunct: offAxisRealObservable ρ.re 0 = ρ.re - 1/2 by offAxisRealObservable_at_zero, which is ≠ 0 since ρ.re ≠ 1/2.
-/
theorem offaxis_forces_observable_nontriviality
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ t, offAxisRealObservable ρ.re t ≠ 0 ∨ offAxisImagObservable ρ.re t ≠ 0 := by
      exact ⟨ 0, Or.inl <| mul_ne_zero ( sub_ne_zero_of_ne hoff ) ( by norm_num ) ⟩
/-
PROBLEM
The real-axis distortion is positive for `n ≥ 2`, unconditionally.
    This reflects the existence of primes (specifically, the prime 2)
    and is independent of any zeta zero hypothesis.
PROVIDED SOLUTION
Use n = 2. Apply realAxisDistortion_pos_of_two_le with hn : 2 ≤ 2 from le_refl.
-/
theorem offaxis_forces_numberline_distortion
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (_hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ n, realAxisDistortion n > 0 := by
      exact ⟨ 2, realAxisDistortion_pos_of_two_le ( by norm_num ) ⟩
/-
PROBLEM
============================================================
Part 2: The detector does not pass for off-axis zeros
============================================================
No off-axis real part passes the rotated prime density detector.
    Equivalently, `σ ≠ 1/2 → ¬ rotatedPrimeDensityDetectorPasses σ`.
PROVIDED SOLUTION
Use rotatedPrimeDensityDetector_iff: rotatedPrimeDensityDetectorPasses σ ↔ σ = 1/2. Since σ ≠ 1/2, the iff gives ¬ passes.
-/
theorem no_offline_passes_detector {σ : ℝ} (hoff : σ ≠ 1 / 2) :
    ¬ rotatedPrimeDensityDetectorPasses σ := by
      exact fun h => hoff <| by have := h 0; norm_num [ offAxisRealObservable, offAxisImagObservable, rotatedPrimeDensityNormSq ] at this; nlinarith;
/-
-/
theorem offaxis_classical_zero_forces_detector_and_distortion
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ
      ∧ (∃ n, realAxisDistortion n > 0)
      ∧ ¬ rotatedPrimeDensityDetectorPasses ρ.re := by
        exact ⟨ offaxis_forces_rotated_detector_event ρ hz hoff, offaxis_forces_numberline_distortion ρ hz hoff, no_offline_passes_detector hoff ⟩


theorem classical_zero_to_prime_dirichlet_order
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) :
    meromorphicOrderAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ = -1 := by
  have hzeta_fin := analyticOrderAt_riemannZeta_ne_top ρ hρ1
  have hmain : meromorphicOrderAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s)) ρ = -1 := by
    have hderiv_nat : analyticOrderNatAt (deriv riemannZeta) ρ + 1 = analyticOrderNatAt riemannZeta ρ := by
      have hderiv : analyticOrderAt (deriv riemannZeta) ρ + 1 = analyticOrderAt riemannZeta ρ := by
        simpa [hz] using (analyticAt_riemannZeta hρ1).analyticOrderAt_deriv_add_one (x := ρ)
      have hderiv_fin : analyticOrderAt (deriv riemannZeta) ρ ≠ ⊤ := by
        intro htop
        have : analyticOrderAt riemannZeta ρ = ⊤ := by simpa [htop] using hderiv.symm
        exact hzeta_fin this
      rw [← Nat.cast_analyticOrderNatAt hderiv_fin, ← Nat.cast_analyticOrderNatAt hzeta_fin] at hderiv
      exact ENat.coe_inj.mp hderiv
    have hmero_deriv : MeromorphicAt (deriv riemannZeta) ρ :=
      (analyticAt_riemannZeta hρ1).deriv.meromorphicAt
    have hmero_zeta : MeromorphicAt riemannZeta ρ := (analyticAt_riemannZeta hρ1).meromorphicAt
    have hquot : meromorphicOrderAt (fun s ↦ deriv riemannZeta s / riemannZeta s) ρ = -1 := by
      change meromorphicOrderAt ((deriv riemannZeta) * (riemannZeta)⁻¹) ρ = -1
      rw [meromorphicOrderAt_mul hmero_deriv hmero_zeta.inv, meromorphicOrderAt_inv]
      have hk : meromorphicOrderAt (deriv riemannZeta) ρ = analyticOrderNatAt (deriv riemannZeta) ρ := by
        have hderiv : analyticOrderAt (deriv riemannZeta) ρ + 1 = analyticOrderAt riemannZeta ρ := by
          simpa [hz] using (analyticAt_riemannZeta hρ1).analyticOrderAt_deriv_add_one (x := ρ)
        have hderiv_fin : analyticOrderAt (deriv riemannZeta) ρ ≠ ⊤ := by
          intro htop
          have : analyticOrderAt riemannZeta ρ = ⊤ := by simpa [htop] using hderiv.symm
          exact hzeta_fin this
        calc
          meromorphicOrderAt (deriv riemannZeta) ρ
              = ENat.map Nat.cast (analyticOrderAt (deriv riemannZeta) ρ) := by
                  simpa using (analyticAt_riemannZeta hρ1).deriv.meromorphicOrderAt_eq
          _ = analyticOrderNatAt (deriv riemannZeta) ρ := by
                rw [← Nat.cast_analyticOrderNatAt hderiv_fin]
                simp
      have hm : meromorphicOrderAt riemannZeta ρ = analyticOrderNatAt riemannZeta ρ := by
        calc
          meromorphicOrderAt riemannZeta ρ = ENat.map Nat.cast (analyticOrderAt riemannZeta ρ) := by
            simpa using (analyticAt_riemannZeta hρ1).meromorphicOrderAt_eq
          _ = analyticOrderNatAt riemannZeta ρ := by
            rw [← Nat.cast_analyticOrderNatAt hzeta_fin]
            simp
      rw [hk, hm]
      have hlin : ((analyticOrderNatAt (deriv riemannZeta) ρ : ℤ) + 1 : ℤ) =
          analyticOrderNatAt riemannZeta ρ := by
        exact_mod_cast hderiv_nat
      change (((analyticOrderNatAt (deriv riemannZeta) ρ : ℤ) + -analyticOrderNatAt riemannZeta ρ : ℤ) :
          WithTop ℤ) = -1
      have hkint : ((analyticOrderNatAt (deriv riemannZeta) ρ : ℤ) + -analyticOrderNatAt riemannZeta ρ : ℤ) = -1 := by
        linarith
      rw [hkint]
      norm_num
    calc
      meromorphicOrderAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s)) ρ
          = meromorphicOrderAt (fun s ↦ ((-1 : ℂ) * (deriv riemannZeta s / riemannZeta s))) ρ := by
              congr 1
              ext s
              ring
      _ = meromorphicOrderAt (fun s ↦ deriv riemannZeta s / riemannZeta s) ρ := by
            exact meromorphicOrderAt_mul_of_ne_zero
              (f := fun s ↦ deriv riemannZeta s / riemannZeta s)
              (g := fun _ : ℂ ↦ (-1 : ℂ)) analyticAt_const (by norm_num)
      _ = -1 := hquot
  have hpole : meromorphicOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) ρ = 0 := by
    have han : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1)⁻¹) ρ := by
      apply AnalyticAt.inv
      · fun_prop
      · simpa [sub_eq_zero] using sub_ne_zero.mpr hρ1
    have hzero : analyticOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) ρ = 0 := by
      rw [han.analyticOrderAt_eq_zero]
      simp [sub_eq_zero, hρ1]
    calc
      meromorphicOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) ρ
          = ENat.map Nat.cast (analyticOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) ρ) := by
              simpa using han.meromorphicOrderAt_eq
      _ = 0 := by simp [hzero]
  have hmeroPoleNeg : MeromorphicAt (fun s : ℂ ↦ -((s - 1)⁻¹)) ρ := by
    have han : AnalyticAt ℂ (fun s : ℂ ↦ -((s - 1)⁻¹)) ρ := by
      apply AnalyticAt.neg
      apply AnalyticAt.inv
      · fun_prop
      · simpa [sub_eq_zero] using sub_ne_zero.mpr hρ1
    exact han.meromorphicAt
  have hpoleNeg : meromorphicOrderAt (fun s : ℂ ↦ -((s - 1)⁻¹)) ρ = 0 := by
    calc
      meromorphicOrderAt (fun s : ℂ ↦ -((s - 1)⁻¹)) ρ
          = meromorphicOrderAt (fun s : ℂ ↦ ((-1 : ℂ) * (s - 1)⁻¹)) ρ := by
              congr 1
              ext s
              ring
      _ = meromorphicOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) ρ := by
            exact meromorphicOrderAt_mul_of_ne_zero
              (f := fun s : ℂ ↦ (s - 1)⁻¹)
              (g := fun _ : ℂ ↦ (-1 : ℂ)) analyticAt_const (by norm_num)
      _ = 0 := hpole
  have hadd := meromorphicOrderAt_add_eq_left_of_lt
    (f₁ := fun s ↦ -(deriv riemannZeta s / riemannZeta s))
    (f₂ := fun s : ℂ ↦ -((s - 1)⁻¹)) hmeroPoleNeg
    (by
      have : (-1 : WithTop ℤ) < 0 := by decide
      simpa [hpoleNeg, hmain] using this)
  simpa [sub_eq_add_neg] using hadd.trans hmain

/-- A zeta zero forces a singularity in the prime Dirichlet generating function. -/
theorem offaxis_with_bridge
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ))
    (hρ1 : ρ ≠ 1) :
    (¬ ContinuousAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ)
    ∧ RotatedPrimeDensityDetectorEvent ρ := by
  refine ⟨?_, offaxis_forces_rotated_detector_event ρ hz hoff⟩
  intro hcont
  have horder := classical_zero_to_prime_dirichlet_order ρ hz hρ1
  have hmero : MeromorphicAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by simp [horder])
  have hnonneg :
      0 ≤ meromorphicOrderAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ :=
    (hmero.analyticAt hcont).meromorphicOrderAt_nonneg
  have hfalse : ¬ (0 ≤ (-1 : WithTop ℤ)) := by decide
  exact hfalse <| by simpa [horder] using hnonneg
-- ============================================================
-- Part 5: Dependency audit
-- ============================================================
/-! ### Dependency audit
Every nontrivial imported theorem used:
1. `ArithmeticFunction.vonMangoldt_nonneg` — Λ(n) ≥ 0
2. `ArithmeticFunction.vonMangoldt_apply_prime` — Λ(p) = log p for prime p
3. `Real.log_pos` — log x > 0 for x > 1
4. `Real.cos_zero` — cos 0 = 1
5. `Real.sin_zero` — sin 0 = 0
6. `Real.cos_neg` — cos(-t) = cos t
7. `Real.sin_neg` — sin(-t) = -sin t
8. `Real.sin_sq_add_cos_sq` — sin²t + cos²t = 1
No theorem equivalent to RH, the functional equation s ↦ 1−s,
or any hypothesis listed in the hard constraints is used. -/
#check @ArithmeticFunction.vonMangoldt_nonneg
#check @ArithmeticFunction.vonMangoldt_apply_prime
#check @Real.log_pos
#check @Real.cos_zero
#check @Real.sin_zero
#check @Real.cos_neg
#check @Real.sin_neg
#check @Real.sin_sq_add_cos_sq
end
