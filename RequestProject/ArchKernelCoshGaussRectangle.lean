import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Complex
import RequestProject.WeilContour
import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation

/-!
# Analyticity of `archKernel · coshGaussMellinExt` off its poles

The product `f(s) = archKernel s · coshGaussMellinExt c s` is the integrand
that would appear in a rectangle Cauchy contour over `[-1, 2] × [-T, T]`
with two singularities at `s = 0` and `s = 1`. Both factors have simple
poles at each of these points, so the product has a *double* pole at `0`
and at `1`.

This file establishes the infrastructural analyticity results used by
the rectangle Cauchy chain:

* `archKernel_analyticOnNhd_off_poles` — `archKernel` is analytic on the
  open set `{s : -1 < Re s < 2 ∧ s ≠ 0 ∧ s ≠ 1}`.
* `coshGaussMellinExt_analyticOnNhd_off_zero` — `coshGaussMellinExt c` is
  analytic on `{s : -1 < Re s < 2 ∧ s ≠ 0}`.
* `archKernel_coshGaussExt_analyticOnNhd_off_poles` — the product is
  analytic on `{s : -1 < Re s < 2 ∧ s ≠ 0 ∧ s ≠ 1}` (the rectangle interior
  punctured at the two poles).

All proofs are axiom-clean.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelCoshGaussRectangle

open ZD.WeilArchKernelResidues ZD.CoshGaussMellinContinuation
  ZD.WeilPositivity.Contour

/-! ### The open rectangle strip and its punctured forms -/

/-- The open vertical strip `-1 < Re s < 2`. -/
def stripRect : Set ℂ := {s : ℂ | -1 < s.re ∧ s.re < 2}

/-- Strip with `s = 0` removed (where `coshGaussMellinExt` has its pole). -/
def stripRectOffZero : Set ℂ := {s : ℂ | -1 < s.re ∧ s.re < 2 ∧ s ≠ 0}

/-- Strip with both poles `0` and `1` of `archKernel` removed. -/
def stripRectPunctured : Set ℂ :=
  {s : ℂ | -1 < s.re ∧ s.re < 2 ∧ s ≠ 0 ∧ s ≠ 1}

lemma stripRect_isOpen : IsOpen stripRect := by
  have h : stripRect = (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) := by
    ext s; simp [stripRect, Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_re

lemma stripRectOffZero_isOpen : IsOpen stripRectOffZero := by
  have h_eq : stripRectOffZero = stripRect ∩ ({0}ᶜ : Set ℂ) := by
    ext s; constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [h_eq]
  exact stripRect_isOpen.inter isOpen_compl_singleton

lemma stripRectPunctured_isOpen : IsOpen stripRectPunctured := by
  have h_eq : stripRectPunctured =
      stripRect ∩ ({0}ᶜ : Set ℂ) ∩ ({1}ᶜ : Set ℂ) := by
    ext s; constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  rw [h_eq]
  exact (stripRect_isOpen.inter isOpen_compl_singleton).inter isOpen_compl_singleton

lemma stripRectPunctured_subset_offZero :
    stripRectPunctured ⊆ stripRectOffZero := by
  intro s hs; exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-! ### `Γℝ` is nonzero on the strip except at `0`; on `1 - s` except at `1` -/

/-- Inside our strip, `Γℝ(s) ≠ 0` whenever `s ≠ 0`. Indeed `Γℝ` vanishes
only at non-positive even integers `0, -2, -4, …`, and the strip's real part
is `> -1`, so the only such point is `0`. -/
private lemma Gammaℝ_ne_zero_in_strip {s : ℂ} (hs : s ∈ stripRect) (hs0 : s ≠ 0) :
    s.Gammaℝ ≠ 0 := by
  intro hzero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
  have hre : s.re = -(2 * (n : ℝ)) := by
    have h := congrArg Complex.re hn
    simp at h; linarith
  have hstrip : -1 < s.re := hs.1
  rw [hre] at hstrip
  have hnlt : (2 * (n : ℝ)) < 1 := by linarith
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hne
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  rw [hn0] at hn; simp at hn
  exact hs0 hn

/-- Inside our strip, `Γℝ(1 - s) ≠ 0` whenever `s ≠ 1`. -/
private lemma Gammaℝ_one_sub_ne_zero_in_strip {s : ℂ}
    (hs : s ∈ stripRect) (hs1 : s ≠ 1) :
    Complex.Gammaℝ (1 - s) ≠ 0 := by
  intro hzero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
  have hsre : s.re = 1 + 2 * (n : ℝ) := by
    have h := congrArg Complex.re hn
    simp at h
    -- h : 1 - s.re = -(2 * ↑n)
    linarith
  have hstrip : s.re < 2 := hs.2
  rw [hsre] at hstrip
  have hnlt : (2 * (n : ℝ)) < 1 := by linarith
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hne
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  rw [hn0] at hn; simp at hn
  have : s = 1 := by linear_combination -hn
  exact hs1 this

/-! ### Analyticity of `archKernel` off the two poles -/

/-- The set `{z : ℂ | z.Gammaℝ ≠ 0}` is open. -/
private lemma Gammaℝ_ne_zero_isOpen : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {s : ℂ | s.Gammaℝ ≠ 0} =
      (fun s : ℂ => s.Gammaℝ⁻¹) ⁻¹' {z : ℂ | z ≠ 0} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine ⟨inv_ne_zero, fun h hs => ?_⟩
    apply h; rw [hs, inv_zero]
  rw [h_eq]
  exact IsOpen.preimage h_cont isOpen_ne

/-- `Γℝ` is analytic on its non-vanishing locus. -/
private lemma Gammaℝ_analyticOnNhd_ne_zero :
    AnalyticOnNhd ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz; exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
  · exact Gammaℝ_ne_zero_isOpen

/-- `deriv Γℝ` is analytic on the non-vanishing locus of `Γℝ`. -/
private lemma deriv_Gammaℝ_analyticOnNhd_ne_zero :
    AnalyticOnNhd ℂ (deriv Complex.Gammaℝ) {s : ℂ | s.Gammaℝ ≠ 0} :=
  Gammaℝ_analyticOnNhd_ne_zero.deriv

/-- `archKernel` is differentiable at any point of the strip other than `0, 1`. -/
theorem archKernel_differentiableAt_off_poles {s : ℂ} (hs : s ∈ stripRectPunctured) :
    DifferentiableAt ℂ archKernel s := by
  obtain ⟨h1, h2, hs0, hs1⟩ := hs
  have hsStrip : s ∈ stripRect := ⟨h1, h2⟩
  have hgs : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_in_strip hsStrip hs0
  have hgs1 : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_one_sub_ne_zero_in_strip hsStrip hs1
  have hg_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hgs
  have hg_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hgs1
  have hd_at_s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) s :=
    (deriv_Gammaℝ_analyticOnNhd_ne_zero s hgs).differentiableAt
  have hd_at_1s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) (1 - s) :=
    (deriv_Gammaℝ_analyticOnNhd_ne_zero (1 - s) hgs1).differentiableAt
  have h_one_sub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hd_comp_1s : DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ (1 - z)) s :=
    hd_at_1s.comp s h_one_sub
  have hg_comp_1s : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (1 - z)) s :=
    hg_1s.comp s h_one_sub
  unfold archKernel
  have hT1 : DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ z / z.Gammaℝ) s :=
    hd_at_s.div hg_s hgs
  have hT2 : DifferentiableAt ℂ
      (fun z : ℂ => deriv Complex.Gammaℝ (1 - z) / Complex.Gammaℝ (1 - z)) s :=
    hd_comp_1s.div hg_comp_1s hgs1
  exact hT1.add hT2

/-- `archKernel` is analytic on the strip with `{0, 1}` removed. -/
theorem archKernel_analyticOnNhd_off_poles :
    AnalyticOnNhd ℂ archKernel stripRectPunctured := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (archKernel_differentiableAt_off_poles hs).differentiableWithinAt
  · exact stripRectPunctured_isOpen

/-! ### Analyticity of `coshGaussMellinExt c` off the pole at `0` -/

/-- `coshGaussMellinExt c` is analytic at any point of the strip other than `0`.
The closed-form factor `gaussMellinClosed` has its only strip-pole at `0`
(other Gamma poles are at `−2, −4, …`, outside `Re > -1`); the difference
piece `mellin (coshDiff c)` is analytic on the entire strip. -/
theorem coshGaussMellinExt_differentiableAt_off_zero {c : ℝ} {s : ℂ}
    (hs : s ∈ stripRectOffZero) :
    DifferentiableAt ℂ (coshGaussMellinExt c) s := by
  obtain ⟨h1, h2, hs0⟩ := hs
  have hsStrip : s ∈ stripRect := ⟨h1, h2⟩
  -- Difference piece analytic on the strip {Re s > -2} ⊇ stripRect.
  have h_diff_strip : (-2 : ℝ) < s.re := by linarith
  have h_diff_anAt : AnalyticAt ℂ (mellin (coshDiff c)) s :=
    coshDiffMellin_analyticAt c h_diff_strip
  have h_diff_diff : DifferentiableAt ℂ (mellin (coshDiff c)) s :=
    h_diff_anAt.differentiableAt
  -- Closed-form piece: gaussMellinClosed s = (1/2) · 2^(-(s/2)) · Γ(s/2).
  -- Need Γ(s/2) differentiable at s. Γ has poles at non-positive integers.
  -- s/2 is non-positive integer iff s is non-positive even integer iff s ∈ {0, -2, ...}.
  -- In our strip with s ≠ 0, this never happens.
  have h_s_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    -- s = -2m. So s.re = -2m. m = 0 ⟹ s = 0. m ≥ 1 ⟹ s.re ≤ -2 < -1.
    have hs_eq : s = -(2 * (m : ℂ)) := by linear_combination 2 * hm
    have hsre : s.re = -(2 * (m : ℝ)) := by
      rw [hs_eq]; simp
    have hstrip : -1 < s.re := h1
    rw [hsre] at hstrip
    have hmlt : (2 * (m : ℝ)) < 1 := by linarith
    have hm0 : m = 0 := by
      by_contra hne
      have h1' : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr hne
      have h2' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1'
      linarith
    rw [hm0] at hs_eq; simp at hs_eq
    exact hs0 hs_eq
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ h_s_half_ne
  -- 2^(-(s/2)) differentiable.
  have h_id : DifferentiableAt ℂ (fun s : ℂ => s) s := differentiableAt_id
  have h_div : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := h_id.div_const 2
  have h_neg : DifferentiableAt ℂ (fun s : ℂ => -(s / 2)) s := h_div.neg
  have h_two_pow : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (-(s/2))) s := by
    refine DifferentiableAt.const_cpow (c := (2 : ℂ)) h_neg ?_
    left; norm_num
  have hΓ_comp : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    hΓ_diff.comp s h_div
  have h_const : DifferentiableAt ℂ (fun _ : ℂ => (1/2 : ℂ)) s :=
    differentiableAt_const _
  have h_prod1 : DifferentiableAt ℂ
      (fun s : ℂ => (1/2 : ℂ) * (2 : ℂ) ^ (-(s/2))) s :=
    h_const.mul h_two_pow
  have h_closed : DifferentiableAt ℂ gaussMellinClosed s := by
    show DifferentiableAt ℂ
      (fun s : ℂ => (1/2 : ℂ) * (2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s / 2)) s
    exact h_prod1.mul hΓ_comp
  -- Sum.
  show DifferentiableAt ℂ
    (fun s : ℂ => gaussMellinClosed s + mellin (coshDiff c) s) s
  exact h_closed.add h_diff_diff

/-- `coshGaussMellinExt c` is analytic on the strip with `0` removed. -/
theorem coshGaussMellinExt_analyticOnNhd_off_zero (c : ℝ) :
    AnalyticOnNhd ℂ (coshGaussMellinExt c) stripRectOffZero := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (coshGaussMellinExt_differentiableAt_off_zero hs).differentiableWithinAt
  · exact stripRectOffZero_isOpen

/-! ### Main result: analyticity of the product off both poles -/

/-- **Main result.** The product `archKernel s · coshGaussMellinExt c s` is
analytic on the open punctured strip `{s : -1 < Re s < 2 ∧ s ≠ 0 ∧ s ≠ 1}`.

This is the natural domain of analyticity for the integrand of a rectangle
contour integral over `[-1, 2] × [-T, T]` with the two singular points
`0, 1` excised. -/
theorem archKernel_coshGaussExt_analyticOnNhd_off_poles (c : ℝ) :
    AnalyticOnNhd ℂ (fun s => archKernel s * coshGaussMellinExt c s)
      stripRectPunctured := by
  have h1 : AnalyticOnNhd ℂ archKernel stripRectPunctured :=
    archKernel_analyticOnNhd_off_poles
  have h2_off_zero : AnalyticOnNhd ℂ (coshGaussMellinExt c) stripRectOffZero :=
    coshGaussMellinExt_analyticOnNhd_off_zero c
  have h2 : AnalyticOnNhd ℂ (coshGaussMellinExt c) stripRectPunctured :=
    h2_off_zero.mono stripRectPunctured_subset_offZero
  exact h1.mul h2

/-! ### Corollary: meromorphicity of the product on the punctured strip -/

/-- **Corollary.** The product is meromorphic on the punctured strip. -/
theorem archKernel_coshGaussExt_meromorphicOn_off_poles (c : ℝ) :
    MeromorphicOn (fun s => archKernel s * coshGaussMellinExt c s)
      stripRectPunctured :=
  (archKernel_coshGaussExt_analyticOnNhd_off_poles c).meromorphicOn

#print axioms archKernel_analyticOnNhd_off_poles
#print axioms coshGaussMellinExt_analyticOnNhd_off_zero
#print axioms archKernel_coshGaussExt_analyticOnNhd_off_poles
#print axioms archKernel_coshGaussExt_meromorphicOn_off_poles

end ZD.ArchKernelCoshGaussRectangle
