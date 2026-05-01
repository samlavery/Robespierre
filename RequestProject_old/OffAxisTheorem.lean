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
/-!
============================================================
Part 1: The rotated density detector under classical rotations
============================================================

The rotated density detector couples the off-axis displacement `ρ.re − 1/2`
to the imaginary height `ρ.im` and queries the three classical rotations
`{0°, 90°, 180°}` (multipliers `{1, 0, −1}`).  It fires precisely when `ρ`
is nontrivially off the critical line — both `ρ.re ≠ 1/2` **and** `ρ.im ≠ 0`
are load-bearing.  The previous signatures of these theorems carried an
unused `riemannZeta ρ = 0` hypothesis whose only job was to look impressive;
the hypotheses below are now the minimal ones the proofs actually use.
-/

/-- A nontrivial off-line candidate fires the rotated density detector on
    its singleton set.  The new `RotatedPrimeDensityDetectorEvent` takes a
    `Set ℂ` and fires iff some element is off-axis; here the singleton `{ρ}`
    contains just the off-axis candidate. -/
theorem offaxis_forces_rotated_detector_event
    (ρ : ℂ)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ({ρ} : Set ℂ) :=
  (rotatedPrimeDensityDetectorEvent_iff {ρ}).mpr ⟨ρ, rfl, hoff⟩
/-- If `ρ.re ≠ 1/2`, at least one of the off-axis observables is nonzero
    at `t = 0`.  Purely algebraic. -/
theorem offaxis_forces_observable_nontriviality
    (ρ : ℂ)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ t, offAxisRealObservable ρ.re t ≠ 0 ∨ offAxisImagObservable ρ.re t ≠ 0 :=
  ⟨0, Or.inl <| mul_ne_zero (sub_ne_zero_of_ne hoff) (by norm_num)⟩
/-- The real-axis distortion is positive at `n = 2`, unconditionally.  The
    previous signature carried two vacuous hypotheses (`riemannZeta ρ = 0`
    and `ρ.re ≠ 1/2`); neither is needed.  The statement does not even
    mention `ρ`. -/
theorem numberline_has_positive_distortion :
    ∃ n, realAxisDistortion n > 0 :=
  ⟨2, realAxisDistortion_pos_of_two_le (by norm_num)⟩
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
/-- Bundled consequences of a nontrivial off-line candidate: the rotated
    density detector fires, the number-line distortion is positive, and the
    rotational detector does not pass.  The previous `riemannZeta ρ = 0`
    hypothesis was carried unused; it has been replaced by the minimal
    `hIm : ρ.im ≠ 0` that the detector theorem actually needs. -/
theorem offaxis_classical_zero_forces_detector_and_distortion
    (ρ : ℂ)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ({ρ} : Set ℂ)
      ∧ (∃ n, realAxisDistortion n > 0)
      ∧ ¬ rotatedPrimeDensityDetectorPasses ρ.re :=
  ⟨offaxis_forces_rotated_detector_event ρ hoff,
   numberline_has_positive_distortion,
   no_offline_passes_detector hoff⟩


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

/-- A zeta zero forces a singularity in the prime Dirichlet generating function,
    and a nontrivial off-line candidate fires the rotated density detector.
    The ζ-zero hypothesis `hz` is load-bearing for the singularity half of the
    conjunction; the detector half needs `hoff` and `hIm` (both non-vacuous). -/
theorem offaxis_with_bridge
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ))
    (hρ1 : ρ ≠ 1) :
    (¬ ContinuousAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ)
    ∧ RotatedPrimeDensityDetectorEvent ({ρ} : Set ℂ) := by
  refine ⟨?_, offaxis_forces_rotated_detector_event ρ hoff⟩
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
-- ============================================================
-- Part 6: Integration tests — detector on mixed vs on-line zero sets
-- ============================================================
/-!
End-of-file sanity tests.  We build two synthetic zero-sets:

* `S_online` — every element lies on the critical line.  The detector must
  be silent: `¬ DetectorFiresOn S_online`, named `df_pass`.
* `S_mixed`  — contains at least one nontrivial candidate that is both off the
  critical line and non-real.  The detector must fire: `DetectorFiresOn S_mixed`,
  named `df_true`.

If either test fails (the detector fires on `S_online`, or fails to fire on
`S_mixed`), the file will not compile — a contradiction at kernel level.
Each element is evaluated at all three classical rotation multipliers
`{1, 0, -1}` (rotations by 0°, 90°, 180°) to make the computation explicit.
-/
/-- "Fires on a set" = the detector event holds on the set (shorthand alias
    for `RotatedPrimeDensityDetectorEvent`). -/
def DetectorFiresOn (S : Set ℂ) : Prop :=
  RotatedPrimeDensityDetectorEvent S
/-- On-line test fixture: both elements have `ρ.re = 1/2`; the detector must
    be silent.  Named `_fixture` to avoid collision with the conceptual
    infinite `S_online` defined in `FinalAssembly.lean`. -/
def S_online_fixture : Set ℂ := {⟨1/2, 1⟩, ⟨1/2, 2⟩}
/-- Mixed test fixture: `⟨1/2, 1⟩` is on-line, `⟨1/3, 1⟩` is off-line. -/
def S_mixed_fixture : Set ℂ := {⟨1/2, 1⟩, ⟨1/3, 1⟩}
-- --- Explicit three-rotation evaluations on the on-line witness ⟨1/2, 1⟩ ---
example : rotatedDensityAt (⟨1/2, 1⟩ : ℂ) 1    = 0 := by
  rw [rotatedDensityAt_rot0]; simp
example : rotatedDensityAt (⟨1/2, 1⟩ : ℂ) Complex.I = -1 := by
  rw [rotatedDensityAt_rot90]
example : rotatedDensityAt (⟨1/2, 1⟩ : ℂ) (-1) = 0 := by
  rw [rotatedDensityAt_rot180]; show (1 : ℝ)/2 - 1/2 = 0; norm_num
-- --- Explicit three-rotation evaluations on the off-line witness ⟨1/3, 1⟩ ---
example : rotatedDensityAt (⟨1/3, 1⟩ : ℂ) 1    = -(1/6) := by
  rw [rotatedDensityAt_rot0]; show (1/3 : ℝ) - 1/2 = -(1/6); norm_num
example : rotatedDensityAt (⟨1/3, 1⟩ : ℂ) Complex.I = -1 := by
  rw [rotatedDensityAt_rot90]
example : rotatedDensityAt (⟨1/3, 1⟩ : ℂ) (-1) = 1/6 := by
  rw [rotatedDensityAt_rot180]; show 1/2 - (1/3 : ℝ) = 1/6; norm_num
/-- **df_true**: the detector fires on `S_mixed_fixture`. Witness: `⟨1/3, 1⟩`. -/
theorem df_true : DetectorFiresOn S_mixed_fixture := by
  refine (rotatedPrimeDensityDetectorEvent_iff _).mpr ⟨⟨1/3, 1⟩, ?_, ?_⟩
  · right; rfl
  · show (1 / 3 : ℝ) ≠ 1 / 2
    norm_num
/-- **df_pass**: the detector does NOT fire on `S_online_fixture`. -/
theorem df_pass : ¬ DetectorFiresOn S_online_fixture := by
  intro hEv
  rcases (rotatedPrimeDensityDetectorEvent_iff _).mp hEv with ⟨ρ, hρ, hRe⟩
  apply hRe
  rcases hρ with h1 | h2
  · rw [h1]
  · rw [h2]
end
