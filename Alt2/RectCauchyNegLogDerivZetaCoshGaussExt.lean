import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilPoleAtOne
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilRectangleDecompositionMult
import RequestProject.WeilRectangleResidueSum
import RequestProject.WeilRectangleResidueSumFull
import RequestProject.WeilRectResidueDischarge
import RequestProject.WeilRectResidueIdentityDischarge
import RequestProject.WeilFinalAssembly
import RequestProject.ZetaBound
import RequestProject.CoshGaussMellinContinuation
import RequestProject.ArchKernelCoshGaussRectangle

/-!
# Rectangle Cauchy for `weilIntegrand (coshGaussMellinExt c)` over `[-1, 2] × [-T, T]`

For any `c : ℝ` and `goodHeight T`, the rectangle contour integral of
`weilIntegrand (coshGaussMellinExt c) = (-ζ'/ζ) · coshGaussMellinExt c`
over `[-1, 2] × [-T, T]` equals

```
2πi · (A₀ + coshGaussMellinExt c 1 − Σ_{ρ ∈ Z} m(ρ) · coshGaussMellinExt c ρ)
```

where `A₀ = negLogDerivZeta0 = -ζ'(0)/ζ(0)` is the residue from `coshGaussMellinExt c`'s
simple pole at `s = 0`.

## Strategy

Three-pole index: `ι = Option (Option {ρ // ρ ∈ Z})` with poles `{0, 1} ∪ Z`.
The global remainder is `threePoleRemainder`, which at s ≠ 0 equals
`weilRemainderGlobalFull s - A₀/s`, and at s = 0 equals the analytic extension
`ψ₀(0) - h(1)/(-1) - Σ -(n ρ)*h(ρ)/(-ρ)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open Contour
open ZD.CoshGaussMellinContinuation
open ZD.ArchKernelCoshGaussRectangle

/-! ### Pole regularizer for `coshGaussMellinExt c` at `s = 0` -/

private noncomputable def coshGaussRegularizer (c : ℝ) : ℂ → ℂ :=
  Function.update (fun s : ℂ => s * coshGaussMellinExt c s) 0 1

private lemma coshGaussRegularizer_at_zero (c : ℝ) : coshGaussRegularizer c 0 = 1 := by
  simp [coshGaussRegularizer]

private lemma coshGaussRegularizer_of_ne_zero (c : ℝ) {s : ℂ} (hs : s ≠ 0) :
    coshGaussRegularizer c s = s * coshGaussMellinExt c s := by
  simp [coshGaussRegularizer, Function.update_of_ne hs]

private lemma coshGaussRegularizer_analyticAt_zero (c : ℝ) :
    AnalyticAt ℂ (coshGaussRegularizer c) 0 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨1, one_pos, fun z hz hz0 => ?_⟩
    have h_eq : coshGaussRegularizer c =ᶠ[nhds z] fun s => s * coshGaussMellinExt c s := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp [coshGaussRegularizer, Function.update_of_ne hw]
    rw [h_eq.differentiableAt_iff]
    have habs : ‖z‖ < 1 := by rwa [dist_zero_right] at hz
    have hre : -2 < z.re := by
      linarith [(abs_lt.mp (lt_of_le_of_lt (abs_re_le_norm z) habs)).1]
    have hh_an : AnalyticAt ℂ (coshGaussMellinExt c) z := by
      apply DifferentiableOn.analyticAt (s := {w : ℂ | -2 < w.re ∧ w ≠ 0})
      · intro w ⟨hwre, hw0⟩
        have h_gne : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
          intro m hm
          have hs_eq : w = -(2 * (m : ℂ)) := by linear_combination 2 * hm
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0; simp at hs_eq; exact hw0 hs_eq
          · have : w.re = -(2 * (m : ℝ)) := by rw [hs_eq]; simp
            linarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hmpos]
        exact ((((differentiableAt_const _).mul
          ((differentiableAt_id.div_const _).neg.const_cpow (Or.inl (by norm_num)))).mul
          ((Complex.differentiableAt_Gamma _ h_gne).comp w (differentiableAt_id.div_const _))).add
          (ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c hwre)).differentiableWithinAt
      · exact IsOpen.mem_nhds
          ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne) ⟨hre, hz0⟩
    exact differentiableAt_id.mul hh_an.differentiableAt
  · simp only [coshGaussRegularizer, continuousAt_update_same]
    exact coshGaussMellinExt_residue_at_zero c

/-! ### Residue at `s = 0` and Laurent form -/

private noncomputable def negLogDerivZeta0 : ℂ := -deriv riemannZeta 0 / riemannZeta 0

private lemma negLogDerivZeta_analyticAt_zero :
    AnalyticAt ℂ (fun s => -deriv riemannZeta s / riemannZeta s) 0 := by
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [zeta_at_zero]; norm_num
  have hζ_an : AnalyticAt ℂ riemannZeta 0 := by
    apply DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1})
    · intro s hs; exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    · exact IsOpen.mem_nhds isOpen_ne (by norm_num)
  exact hζ_an.deriv.neg.div hζ_an hζ0

private theorem diff_quotient_analyticAt_zero {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ s in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), (F s - F 0) / s = q s := by
  have hFm_an : AnalyticAt ℂ (fun s => F s - F 0) 0 := hF.sub analyticAt_const
  have hFm_zero : (fun s : ℂ => F s - F 0) 0 = 0 := by simp
  have h_order : (1 : ℕ∞) ≤ analyticOrderAt (fun s => F s - F 0) 0 := by
    rw [ENat.one_le_iff_ne_zero]; intro h0
    exact hFm_an.analyticOrderAt_eq_zero.mp h0 hFm_zero
  obtain ⟨q, hq_an, hq_eq⟩ := (natCast_le_analyticOrderAt hFm_an).mp h_order
  refine ⟨q, hq_an, ?_⟩
  filter_upwards [hq_eq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
  simp only [pow_one, smul_eq_mul, sub_zero] at hs
  rw [hs]; field_simp [Set.mem_compl_singleton_iff.mp hs0]

private theorem weilIntegrand_coshGaussExt_residue_form_at_zero (c : ℝ) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧
      ∀ᶠ s in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
        weilIntegrand (coshGaussMellinExt c) s = negLogDerivZeta0 / s + ψ s := by
  set F : ℂ → ℂ := fun s => (-deriv riemannZeta s / riemannZeta s) * coshGaussRegularizer c s
  have hF_an : AnalyticAt ℂ F 0 :=
    negLogDerivZeta_analyticAt_zero.mul (coshGaussRegularizer_analyticAt_zero c)
  have hF0 : F 0 = negLogDerivZeta0 := by
    simp [F, coshGaussRegularizer_at_zero, negLogDerivZeta0]
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt_zero hF_an
  refine ⟨q, hq_an, ?_⟩
  filter_upwards [hq_eq, self_mem_nhdsWithin] with s hs_q hs0
  have h_ne : s ≠ 0 := hs0
  unfold weilIntegrand
  rw [show (-deriv riemannZeta s / riemannZeta s) * coshGaussMellinExt c s = F s / s by
    simp only [F]; rw [coshGaussRegularizer_of_ne_zero c h_ne]; field_simp [h_ne]]
  rw [show F s / s = F 0 / s + (F s - F 0) / s by field_simp [h_ne]; ring]
  rw [hF0]; congr 1; rw [← hF0]; exact hs_q

/-! ### Analyticity of `coshGaussMellinExt c` -/

private lemma coshGaussMellinExt_analyticAt_re_gt_neg_two_ne_zero
    {c : ℝ} {s : ℂ} (hre : -2 < s.re) (hs0 : s ≠ 0) :
    AnalyticAt ℂ (coshGaussMellinExt c) s := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | -2 < z.re ∧ z ≠ 0})
  · intro z ⟨hzre, hz0⟩
    have h_gne : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hs_eq : z = -(2 * (m : ℂ)) := by linear_combination 2 * hm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp at hs_eq; exact hz0 hs_eq
      · have : z.re = -(2 * (m : ℝ)) := by rw [hs_eq]; simp
        linarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hmpos]
    exact ((((differentiableAt_const _).mul
      ((differentiableAt_id.div_const _).neg.const_cpow (Or.inl (by norm_num)))).mul
      ((Complex.differentiableAt_Gamma _ h_gne).comp z (differentiableAt_id.div_const _))).add
      (ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c hzre)).differentiableWithinAt
  · exact IsOpen.mem_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne) ⟨hre, hs0⟩

private lemma coshGaussMellinExt_analyticAt_nontrivialZero {c : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) : AnalyticAt ℂ (coshGaussMellinExt c) ρ :=
  coshGaussMellinExt_analyticAt_re_gt_neg_two_ne_zero
    (by obtain ⟨hlo, _, _⟩ := hρ; linarith)
    (by intro h; obtain ⟨hlo, _, _⟩ := hρ; simp [h] at hlo)

/-! ### Three-pole global remainder and its analyticity -/

/-- `0 ∉ Z` whenever `Z` is a set of ζ-zeros (since ζ(0) ≠ 0). -/
private lemma zero_not_in_Z_of_multZeroBundle
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) : (0 : ℂ) ∉ Z := by
  intro h0Z; have := hB.ζ_zero (ρ := 0) h0Z; rw [zeta_at_zero] at this; norm_num at this

/-- Near `s = 0` (punctured), `weilRemainderGlobalFull h Z n s - A₀/s` equals
`ψ₀ s - h 1/(s-1) - Σ -(n ρ)*h(ρ)/(s-ρ)`. -/
private lemma weilRemainderGlobalFull_minus_A0_near_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ)
    (hψ₀_eq : ∀ᶠ s in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, weilIntegrand h s = A₀ / s + ψ₀ s) :
    ∀ᶠ s in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
        weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z s - A₀ / s =
          ψ₀ s - h 1 / (s - 1) - ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ / (s - ρ) := by
  have h0_notZ := zero_not_in_Z_of_multZeroBundle hB
  have hnotZ_nhd : ∀ᶠ s in nhds (0 : ℂ), s ∉ Z :=
    Z.finite_toSet.isClosed.isOpen_compl.mem_nhds h0_notZ
  have hnotone_nhd : ∀ᶠ s in nhds (0 : ℂ), s ≠ 1 :=
    isOpen_compl_singleton.mem_nhds (one_ne_zero.symm)
  filter_upwards [hψ₀_eq, hnotZ_nhd.filter_mono nhdsWithin_le_nhds,
    hnotone_nhd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs_form hs_notZ hs_ne_one hs0
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  rw [weilRemainderGlobalFull_off_Z_and_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z hs_notZ hs_ne_one]
  unfold weilNaiveRemainderFull weilNaiveRemainderMult
  rw [hs_form]; simp only [neg_mul, neg_div, Finset.sum_neg_distrib]; ring

/-- The globally-analytic three-pole remainder:
at `s = 0`, equals the analytic extension `ψ₀ s - h 1/(s-1) - Σ -(n ρ)*h(ρ)/(s-ρ)`;
at `s ≠ 0`, equals `weilRemainderGlobalFull s - A₀/s`. -/
private noncomputable def threePoleRemainder
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ) : ℂ → ℂ := fun s =>
  if s = 0 then ψ₀ s - h 1 / (s - 1) - ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ / (s - ρ)
  else weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z s - A₀ / s

/-- `threePoleRemainder` is analytic at `s = 0`. -/
private lemma threePoleRemainder_analyticAt_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ) (hψ₀_an : AnalyticAt ℂ ψ₀ 0)
    (hψ₀_eq : ∀ᶠ s in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, weilIntegrand h s = A₀ / s + ψ₀ s) :
    AnalyticAt ℂ (threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀) 0 := by
  set gExt : ℂ → ℂ := fun s => ψ₀ s - h 1 / (s - 1) - ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ / (s - ρ)
  have hgExt_an : AnalyticAt ℂ gExt 0 := by
    have h0_notZ := zero_not_in_Z_of_multZeroBundle hB
    have hZ_ne_zero : ∀ ρ ∈ Z, ρ ≠ 0 := fun ρ hρ h0 => h0_notZ (h0 ▸ hρ)
    have h_one_an : AnalyticAt ℂ (fun s : ℂ => h 1 / (s - 1)) 0 :=
      analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (by simp)
    have h_sum_an : AnalyticAt ℂ (fun s => ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ / (s - ρ)) 0 := by
      have hterm : ∀ ρ ∈ Z, AnalyticAt ℂ (fun s : ℂ => -(n ρ : ℂ) * h ρ / (s - ρ)) 0 :=
        fun ρ hρ => analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
          (by simp [hZ_ne_zero ρ hρ])
      have := Finset.analyticAt_sum Z hterm
      convert this using 1; funext s; simp [Finset.sum_apply]
    exact hψ₀_an.sub h_one_an |>.sub h_sum_an
  apply hgExt_an.congr
  have h_agree_punct := weilRemainderGlobalFull_minus_A0_near_zero
    hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀ hψ₀_eq
  rw [eventually_nhdsWithin_iff] at h_agree_punct
  filter_upwards [h_agree_punct] with s hs
  by_cases hs0 : s = 0
  · subst hs0; simp [threePoleRemainder, gExt]
  · simp only [threePoleRemainder, hs0, if_false]; exact (hs hs0).symm

/-- `threePoleRemainder` is analytic at `s = 1`. -/
private lemma threePoleRemainder_analyticAt_one
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ) :
    AnalyticAt ℂ (threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀) 1 := by
  have h_rem_an : AnalyticAt ℂ
      (weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z) 1 :=
    weilRemainderGlobalFull_analyticAt_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z
  have h_eq : threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀ =ᶠ[nhds 1]
      fun s => weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z s - A₀ / s := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with s hs
    simp [threePoleRemainder, Set.mem_compl_singleton_iff.mp hs]
  exact (h_rem_an.sub (analyticAt_const.div analyticAt_id (by norm_num))).congr h_eq.symm

/-- `threePoleRemainder` is analytic at each `ρ ∈ Z`. -/
private lemma threePoleRemainder_analyticAt_Z
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ) {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀) ρ := by
  have hρ0 : ρ ≠ 0 := fun h0 => zero_not_in_Z_of_multZeroBundle hB (h0 ▸ hρ)
  have h_rem_an : AnalyticAt ℂ
      (weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z) ρ :=
    weilRemainderGlobalFull_analyticAt_zero hB hZ_ne_one hh1 h1_not_Z hh_an_Z hρ
  have h_eq : threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀ =ᶠ[nhds ρ]
      fun s => weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z s - A₀ / s := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ0] with s hs
    simp [threePoleRemainder, Set.mem_compl_singleton_iff.mp hs]
  exact (h_rem_an.sub (analyticAt_const.div analyticAt_id hρ0)).congr h_eq.symm

/-- `threePoleRemainder` is analytic off `Z ∪ {0, 1}`. -/
private lemma threePoleRemainder_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {n : ℂ → ℕ}
    (hB : MultZeroBundle h Z n) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    (A₀ : ℂ) (ψ₀ : ℂ → ℂ)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsZ : s ∉ Z)
    (hζ_ne : riemannZeta s ≠ 0) (hh_s : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀) s := by
  have h_rem_an : AnalyticAt ℂ
      (weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z) s :=
    weilRemainderGlobalFull_analyticAt_off_poles hB hZ_ne_one hh1 h1_not_Z hh_an_Z hs1 hsZ hζ_ne hh_s
  have h_eq : threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z A₀ ψ₀ =ᶠ[nhds s]
      fun z => weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z z - A₀ / z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs0] with z hz
    simp [threePoleRemainder, Set.mem_compl_singleton_iff.mp hz]
  exact (h_rem_an.sub (analyticAt_const.div analyticAt_id hs0)).congr h_eq.symm

/-! ### Local helper lemmas (copied from WeilRectResidueIdentityDischarge, where they are private) -/

private lemma zeta_ne_zero_on_rect_neg_one_two'
    {T : ℝ} (_hT_pos : 0 < T) (hGood : goodHeight T)
    {Z : Finset ℂ}
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z)
    {s : ℂ} (hs : s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T))
    (hsZ : s ∉ Z) (_hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have hs_re_mem : s.re ∈ Set.uIcc (-1 : ℝ) 2 := hs.1
  have hs_im_mem : s.im ∈ Set.uIcc (-T) T := hs.2
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hs_re_mem
  rw [Set.uIcc_of_le (by linarith : (-T) ≤ T)] at hs_im_mem
  obtain ⟨hs_re_lo, _hs_re_hi⟩ := hs_re_mem
  obtain ⟨hs_im_lo, hs_im_hi⟩ := hs_im_mem
  intro hζ0
  have h_not_triv : ∀ k : ℕ, s ≠ -2 * (↑k + 1) := by
    intro k hk; have h_re : s.re = -2 * (↑k + 1) := by rw [hk]; simp
    have hbound : (-2 : ℝ) * (↑k + 1) ≤ -2 := by
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; nlinarith
    linarith
  have h_bounds : 0 < s.re ∧ s.re < 1 :=
    riemannZeta_nontrivial_zero_re_bounds hζ0 h_not_triv
  have h_in_NZ : s ∈ NontrivialZeros := ⟨h_bounds.1, h_bounds.2, hζ0⟩
  have h_im_ne : s.im ≠ T ∧ s.im ≠ -T := hGood.1 s h_in_NZ
  have hs_im_lt : s.im < T := lt_of_le_of_ne hs_im_hi h_im_ne.1
  have hs_im_gt : -T < s.im := lt_of_le_of_ne hs_im_lo (fun h => h_im_ne.2 h.symm)
  exact hsZ (hZ_complete s h_in_NZ (by linarith [h_bounds.1])
    (by linarith [h_bounds.2]) hs_im_gt hs_im_lt)

private theorem rectContourIntegral_congr''
    {σL σR T : ℝ} {f g : ℂ → ℂ}
    (h_bottom : ∀ x ∈ Set.uIcc σL σR, f (↑x + (-T : ℝ) * I) = g (↑x + (-T : ℝ) * I))
    (h_top : ∀ x ∈ Set.uIcc σL σR, f (↑x + (T : ℝ) * I) = g (↑x + (T : ℝ) * I))
    (h_right : ∀ y ∈ Set.uIcc (-T) T, f (↑σR + ↑y * I) = g (↑σR + ↑y * I))
    (h_left : ∀ y ∈ Set.uIcc (-T) T, f (↑σL + ↑y * I) = g (↑σL + ↑y * I)) :
    rectContourIntegral σL σR T f = rectContourIntegral σL σR T g := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_congr fun x hx => h_bottom x hx]
  rw [intervalIntegral.integral_congr fun x hx => h_top x hx]
  rw [intervalIntegral.integral_congr fun y hy => h_right y hy]
  rw [intervalIntegral.integral_congr fun y hy => h_left y hy]

private theorem bottom_edge_II_cont'
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (-T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx; exact ⟨by simpa using hx, by simp⟩

private theorem top_edge_II_cont'
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx; exact ⟨by simpa using hx, by simp⟩

private theorem right_edge_II_cont'
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σR + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy; exact ⟨by simp, by simpa using hy⟩

private theorem left_edge_II_cont'
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σL + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy; exact ⟨by simp, by simpa using hy⟩

private theorem bottom_edge_II_pole'
    {σL σR T : ℝ} (r p : ℂ) (hp_im : -T < p.im) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (-T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const; · fun_prop
  intro x _ hx0
  have him : (((x : ℂ) + (-T : ℝ) * I - p).im : ℝ) = -T - p.im := by simp
  rw [hx0] at him; simp at him; linarith

private theorem top_edge_II_pole'
    {σL σR T : ℝ} (r p : ℂ) (hp_im : p.im < T) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const; · fun_prop
  intro x _ hx0
  have him : (((x : ℂ) + (T : ℝ) * I - p).im : ℝ) = T - p.im := by simp
  rw [hx0] at him; simp at him; linarith

private theorem right_edge_II_pole'
    {σR T : ℝ} (r p : ℂ) (hp_re : p.re < σR) :
    IntervalIntegrable (fun y : ℝ => r / ((σR : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const; · fun_prop
  intro y _ hy0
  have hre : (((σR : ℂ) + (y : ℂ) * I - p).re : ℝ) = σR - p.re := by simp
  rw [hy0] at hre; simp at hre; linarith

private theorem left_edge_II_pole'
    {σL T : ℝ} (r p : ℂ) (hp_re : σL < p.re) :
    IntervalIntegrable (fun y : ℝ => r / ((σL : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const; · fun_prop
  intro y _ hy0
  have hre : (((σL : ℂ) + (y : ℂ) * I - p).re : ℝ) = σL - p.re := by simp
  rw [hy0] at hre; simp at hre; linarith

/-! ### Main theorem -/

/-- **Rectangle Cauchy identity for `weilIntegrand (coshGaussMellinExt c)` at finite `T`.**

`rectContourIntegral (-1) 2 T (weilIntegrand (coshGaussMellinExt c)) =
  2πi · (A₀ + coshGaussMellinExt c 1 − Σ_{ρ ∈ Z} n(ρ) · coshGaussMellinExt c ρ)`

where `A₀ = -ζ'(0)/ζ(0)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    (c : ℝ) {T : ℝ} (hT : 1 < T) (hGood : goodHeight T)
    (n : ℂ → ℕ) (Z : Finset ℂ)
    (hZ_mem : ∀ ρ ∈ Z,
      ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z) :
    rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand (coshGaussMellinExt c)) =
      2 * ((Real.pi : ℝ) : ℂ) * I *
        (negLogDerivZeta0 +
          coshGaussMellinExt c 1 -
          ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * coshGaussMellinExt c ρ) := by
  set h : ℂ → ℂ := coshGaussMellinExt c with hh_def
  have hT_pos : 0 < T := by linarith
  have hσLR : ((-1 : ℝ) : ℝ) < 2 := by norm_num
  have hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1 := by
    intro ρ hρ heq
    obtain ⟨hNZ, _⟩ := hZ_mem ρ hρ; obtain ⟨_, hlt1, _⟩ := hNZ
    rw [heq] at hlt1; simp at hlt1
  have h1_not_Z : (1 : ℂ) ∉ Z := fun hmem => hZ_ne_one 1 hmem rfl
  have hh1 : AnalyticAt ℂ h 1 :=
    coshGaussMellinExt_analyticAt_re_gt_neg_two_ne_zero (by simp; norm_num) (by norm_num)
  have hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ := fun ρ hρ =>
    coshGaussMellinExt_analyticAt_nontrivialZero (hZ_mem ρ hρ).1
  have hh_an_rect_ne0 : ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T),
      s ≠ 0 → AnalyticAt ℂ h s := fun s hs hs0 =>
    coshGaussMellinExt_analyticAt_re_gt_neg_two_ne_zero
      (by rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hs; linarith [hs.1.1]) hs0
  have hB : MultZeroBundle h Z n := {
    ζ_an := fun ρ hρ => DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (IsOpen.mem_nhds isOpen_ne (hZ_ne_one ρ hρ))
    ζ_zero := fun ρ hρ => (hZ_mem ρ hρ).1.2.2
    order_pos := fun ρ hρ => by
      obtain ⟨hNZ, _, _, _, _, hn_eq⟩ := hZ_mem ρ hρ
      obtain ⟨m, hm_ge, hm_eq⟩ := analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hNZ
      have : m = n ρ := by exact_mod_cast hm_eq.symm.trans hn_eq
      rw [← this]; exact hm_ge
    order_eq := fun ρ hρ => (hZ_mem ρ hρ).2.2.2.2.2
    h_an := hh_an_Z }
  have hζ_ne_off_Z :
      ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T), s ∉ Z → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hsZ hs1 => zeta_ne_zero_on_rect_neg_one_two' hT_pos hGood hZ_complete hs hsZ hs1
  -- Three-pole index
  let ι := Option (Option {ρ : ℂ // ρ ∈ Z})
  let p : ι → ℂ := fun
    | none => (0 : ℂ)
    | some none => (1 : ℂ)
    | some (some ⟨ρ, _⟩) => ρ
  let r : ι → ℂ := fun
    | none => negLogDerivZeta0
    | some none => h 1
    | some (some ⟨ρ, _⟩) => -(n ρ : ℂ) * h ρ
  have hp_re : ∀ i ∈ (Finset.univ : Finset ι), (-1 : ℝ) < (p i).re ∧ (p i).re < 2 := by
    intro i _; cases i with
    | none => exact ⟨by norm_num, by norm_num⟩
    | some j => cases j with
      | none => exact ⟨by norm_num, by norm_num⟩
      | some ρmem =>
        obtain ⟨ρ, hρ⟩ := ρmem; obtain ⟨_, hlo, hhi, _, _, _⟩ := hZ_mem ρ hρ
        exact ⟨hlo, hhi⟩
  have hp_im : ∀ i ∈ (Finset.univ : Finset ι), (-T) < (p i).im ∧ (p i).im < T := by
    intro i _; cases i with
    | none =>
      show -T < (0 : ℂ).im ∧ (0 : ℂ).im < T
      simp only [Complex.zero_im]; exact ⟨by linarith, by linarith⟩
    | some j => cases j with
      | none =>
        show -T < (1 : ℂ).im ∧ (1 : ℂ).im < T
        simp only [Complex.one_im]; exact ⟨by linarith, by linarith⟩
      | some ρmem =>
        obtain ⟨ρ, hρ⟩ := ρmem; obtain ⟨_, _, _, hlo, hhi, _⟩ := hZ_mem ρ hρ
        exact ⟨hlo, hhi⟩
  -- Obtain ψ₀ from Laurent form at s = 0
  obtain ⟨ψ₀, hψ₀_an, hψ₀_eq⟩ := weilIntegrand_coshGaussExt_residue_form_at_zero c
  -- Define the globally-analytic three-pole remainder
  let g : ℂ → ℂ := threePoleRemainder hB hZ_ne_one hh1 h1_not_Z hh_an_Z negLogDerivZeta0 ψ₀
  -- Differentiability of g on the closed rectangle
  have hg_diff : DifferentiableOn ℂ g (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      exact (threePoleRemainder_analyticAt_zero hB hZ_ne_one hh1 h1_not_Z hh_an_Z
        negLogDerivZeta0 ψ₀ hψ₀_an hψ₀_eq).differentiableAt.differentiableWithinAt
    · by_cases hs1 : s = 1
      · subst hs1
        exact (threePoleRemainder_analyticAt_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z
          negLogDerivZeta0 ψ₀).differentiableAt.differentiableWithinAt
      · by_cases hsZ : s ∈ Z
        · exact (threePoleRemainder_analyticAt_Z hB hZ_ne_one hh1 h1_not_Z hh_an_Z
            negLogDerivZeta0 ψ₀ hsZ).differentiableAt.differentiableWithinAt
        · exact (threePoleRemainder_analyticAt_off_poles hB hZ_ne_one hh1 h1_not_Z hh_an_Z
            negLogDerivZeta0 ψ₀ hs0 hs1 hsZ (hζ_ne_off_Z s hs hsZ hs1)
            (hh_an_rect_ne0 s hs hs0)).differentiableAt.differentiableWithinAt
  -- Polar decomposition on the boundary
  -- Boundary points are never at 0, 1, or ρ ∈ Z (all strictly interior).
  -- For s on the boundary (s ≠ 0, s ≠ 1, s ∉ Z):
  --   weilIntegrand h s = h(1)/(s-1) + Σ -(n ρ)*h(ρ)/(s-ρ) + weilRemainderGlobalFull s
  --                     = Σ r(i)/(s-p(i)) + (weilRemainderGlobalFull s - A₀/s) + A₀/s
  --                     [add and subtract A₀/s]
  -- But g = weilRemainderGlobalFull s - A₀/s at s ≠ 0.
  -- So: weilIntegrand h s = A₀/s + h(1)/(s-1) + Σ -(n ρ)*h(ρ)/(s-ρ) + g(s)
  --                       = Σ r(i)/(s-p(i)) + g(s).
  have h_polar_eq : ∀ s : ℂ, s ∉ Z → s ≠ 1 → s ≠ 0 →
      weilIntegrand h s = ∑ i ∈ (Finset.univ : Finset ι), r i / (s - p i) + g s := by
    intro s hsZ hs1 hs0
    have hg_eq : g s = weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z s -
        negLogDerivZeta0 / s := by
      simp [g, threePoleRemainder, hs0]
    rw [hg_eq]
    rw [weilIntegrand_eq_polar_plus_global_full hB hZ_ne_one hh1 h1_not_Z hh_an_Z hsZ hs1]
    classical
    rw [Fintype.sum_option, Fintype.sum_option]
    simp only [p, r]
    rw [show (Finset.univ : Finset {ρ : ℂ // ρ ∈ Z}) = Z.attach from rfl]
    rw [Z.sum_attach (fun ρ => (-(n ρ : ℂ) * h ρ) / (s - ρ))]
    have hsum_eq : ∑ ρ ∈ Z, (-(n ρ : ℂ) * h ρ) / (s - ρ) =
        ∑ ρ ∈ Z, (-(n ρ : ℂ) * h ρ) / (s - ρ) := rfl
    ring
  -- The boundary decomposition equations
  -- (bottom: Im = -T, so not at any interior pole)
  have h_bnd : ∀ s : ℂ, s ∉ Z → s ≠ 1 → s ≠ 0 →
      weilIntegrand h s = ∑ i ∈ (Finset.univ : Finset ι), r i / (s - p i) + g s :=
    h_polar_eq
  -- Integrability of poles and remainder on each edge
  have h_pole_b : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable (fun x : ℝ => r i / ((x : ℂ) + (-T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 :=
    fun i hi => bottom_edge_II_pole' (r i) (p i) (hp_im i hi).1
  have h_pole_t : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable (fun x : ℝ => r i / ((x : ℂ) + (T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 :=
    fun i hi => top_edge_II_pole' (r i) (p i) (hp_im i hi).2
  have h_pole_r : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable (fun y : ℝ => r i / (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T :=
    fun i hi => right_edge_II_pole' (σR := (2 : ℝ)) (T := T) (r i) (p i) (hp_re i hi).2
  have h_pole_l : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable (fun y : ℝ => r i / (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T :=
    fun i hi => left_edge_II_pole' (σL := (-1 : ℝ)) (T := T) (r i) (p i) (hp_re i hi).1
  have hg_cont : ContinuousOn g (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) :=
    hg_diff.continuousOn
  -- Splitting of the integral
  have h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i) + g z) =
        (∑ i ∈ (Finset.univ : Finset ι),
          rectContourIntegral (-1 : ℝ) 2 T (fun z => r i / (z - p i))) +
          rectContourIntegral (-1 : ℝ) 2 T g := by
    classical
    let F : ι → ℝ → ℂ := fun i x => r i / ((x : ℂ) + (-T : ℝ) * I - p i)
    have hb : IntervalIntegrable (fun x : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
        ((x : ℂ) + (-T : ℝ) * I - p i)) MeasureTheory.volume (-1 : ℝ) 2 := by
      have : ∀ t : Finset ι, IntervalIntegrable (fun x : ℝ => ∑ i ∈ t, F i x)
          MeasureTheory.volume (-1 : ℝ) 2 := by
        intro t; refine Finset.induction_on t ?_ ?_
        · simp [F]
        · intro i t hi ih
          simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_b i (by simp)) ih
      simpa [F] using this (Finset.univ : Finset ι)
    let Ft : ι → ℝ → ℂ := fun i x => r i / ((x : ℂ) + (T : ℝ) * I - p i)
    have ht : IntervalIntegrable (fun x : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
        ((x : ℂ) + (T : ℝ) * I - p i)) MeasureTheory.volume (-1 : ℝ) 2 := by
      have : ∀ t : Finset ι, IntervalIntegrable (fun x : ℝ => ∑ i ∈ t, Ft i x)
          MeasureTheory.volume (-1 : ℝ) 2 := by
        intro t; refine Finset.induction_on t ?_ ?_
        · simp [Ft]
        · intro i t hi ih
          simpa [Ft, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_t i (by simp)) ih
      simpa [Ft] using this (Finset.univ : Finset ι)
    let Fr : ι → ℝ → ℂ := fun i y => r i / (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i)
    have hr : IntervalIntegrable (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
        (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i)) MeasureTheory.volume (-T) T := by
      have : ∀ t : Finset ι, IntervalIntegrable (fun y : ℝ => ∑ i ∈ t, Fr i y)
          MeasureTheory.volume (-T) T := by
        intro t; refine Finset.induction_on t ?_ ?_
        · simp [Fr]
        · intro i t hi ih
          simpa [Fr, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_r i (by simp)) ih
      simpa [Fr] using this (Finset.univ : Finset ι)
    let Fl : ι → ℝ → ℂ := fun i y => r i / (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i)
    have hl : IntervalIntegrable (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
        (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i)) MeasureTheory.volume (-T) T := by
      have : ∀ t : Finset ι, IntervalIntegrable (fun y : ℝ => ∑ i ∈ t, Fl i y)
          MeasureTheory.volume (-T) T := by
        intro t; refine Finset.induction_on t ?_ ?_
        · simp [Fl]
        · intro i t hi ih
          simpa [Fl, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_l i (by simp)) ih
      simpa [Fl] using this (Finset.univ : Finset ι)
    calc rectContourIntegral (-1 : ℝ) 2 T
            (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i) + g z)
        = rectContourIntegral (-1 : ℝ) 2 T
            (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) +
          rectContourIntegral (-1 : ℝ) 2 T g :=
          rectContourIntegral_add (-1 : ℝ) 2 T _ g hb
            (bottom_edge_II_cont' hg_cont) ht (top_edge_II_cont' hg_cont)
            hr (right_edge_II_cont' (σL := (-1 : ℝ)) (σR := (2 : ℝ)) (T := T) hg_cont)
            hl (left_edge_II_cont' (σL := (-1 : ℝ)) (σR := (2 : ℝ)) (T := T) hg_cont)
      _ = (∑ i ∈ (Finset.univ : Finset ι),
            rectContourIntegral (-1 : ℝ) 2 T (fun z => r i / (z - p i))) +
          rectContourIntegral (-1 : ℝ) 2 T g := by
            congr 1
            exact rectContourIntegral_finset_sum (-1 : ℝ) 2 T (Finset.univ : Finset ι)
              (fun i z => r i / (z - p i)) h_pole_b h_pole_t h_pole_r h_pole_l
  -- The weilIntegrand h agrees with the polar form on the boundary
  have h_f_eq_decomp :
      rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand h) =
        rectContourIntegral (-1 : ℝ) 2 T
          (fun z => (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) + g z) := by
    apply rectContourIntegral_congr''
    · intro x _
      have hx0 : ((x : ℂ) + (-T : ℝ) * I) ≠ 0 := by
        intro heq; have := congr_arg Complex.im heq; simp at this; linarith
      have hx1 : ((x : ℂ) + (-T : ℝ) * I) ≠ 1 := by
        intro heq; have := congr_arg Complex.im heq; simp at this; linarith
      have hxZ : ((x : ℂ) + (-T : ℝ) * I) ∉ Z := fun hmem =>
        absurd (hZ_mem _ hmem).2.2.2.1 (by simp)
      exact h_polar_eq _ hxZ hx1 hx0
    · intro x _
      have hx0 : ((x : ℂ) + (T : ℝ) * I) ≠ 0 := by
        intro heq; have := congr_arg Complex.im heq; simp at this; linarith
      have hx1 : ((x : ℂ) + (T : ℝ) * I) ≠ 1 := by
        intro heq; have := congr_arg Complex.im heq; simp at this; linarith
      have hxZ : ((x : ℂ) + (T : ℝ) * I) ∉ Z := fun hmem =>
        absurd (hZ_mem _ hmem).2.2.2.2.1 (by simp)
      exact h_polar_eq _ hxZ hx1 hx0
    · intro y _
      have hy0 : (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
        intro heq; have hre := congr_arg Complex.re heq; simp at hre
      have hy1 : (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro heq; have := congr_arg Complex.re heq; norm_num at this
      have hyZ : (((2 : ℝ) : ℂ) + (y : ℂ) * I) ∉ Z := fun hmem =>
        absurd (hZ_mem _ hmem).2.2.1 (by simp)
      exact h_polar_eq _ hyZ hy1 hy0
    · intro y _
      have hy0 : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
        intro heq; have := congr_arg Complex.re heq; norm_num at this
      have hy1 : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro heq; have := congr_arg Complex.re heq; norm_num at this
      have hyZ : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ∉ Z := fun hmem =>
        absurd (hZ_mem _ hmem).2.1 (by simp)
      exact h_polar_eq _ hyZ hy1 hy0
  -- Apply the multi-pole residue theorem
  have hmain := rectResidueTheorem_multi_pole_unconditional
    (σL := (-1 : ℝ)) (σR := 2) (T := T) hσLR hT_pos
    (poles := (Finset.univ : Finset ι)) (p := p) (r := r) (g := g)
    hp_re hp_im hg_diff h_integral_eq
  -- weilIntegrand h integral = 2πi * Σ r(i)
  have h_weil_eq :
      rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand h) =
        2 * ↑Real.pi * I * (∑ i ∈ (Finset.univ : Finset ι), r i) := by
    rw [h_f_eq_decomp]; exact hmain
  -- Sum of residues = A₀ + h(1) - Σ n(ρ)*h(ρ)
  have h_sum_r :
      (∑ i ∈ (Finset.univ : Finset ι), r i) =
        negLogDerivZeta0 + h 1 - ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * h ρ := by
    classical
    rw [Fintype.sum_option, Fintype.sum_option]
    rw [show (Finset.univ : Finset {ρ : ℂ // ρ ∈ Z}) = Z.attach from rfl]
    rw [Z.sum_attach (fun ρ => -(n ρ : ℂ) * h ρ)]
    simp [Finset.sum_neg_distrib]; ring
  rw [h_weil_eq, h_sum_r]

#print axioms rectContourIntegral_neg_logDerivZeta_coshGaussExt_eq_residue_sum

end FinalAssembly
end WeilPositivity
end ZD

end
