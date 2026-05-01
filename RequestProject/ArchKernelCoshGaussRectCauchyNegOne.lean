import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Complex
import RequestProject.WeilContour
import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation
import RequestProject.ArchKernelCoshGaussRectangle
import RequestProject.ArchKernelCoshGaussRectCauchy

/-!
# Left-edge identification for the rectangle integrand (`σ = -1`)

This is the σ = -1 mirror of `ArchKernelCoshGaussRectCauchy.lean`, which
identified the right edge of the Cauchy rectangle `[-1, 2] × [-T, T]`.

On the left edge `Re s = -1` we are **outside** the original convergence
half-plane of `coshGaussMellin`, so the meromorphic continuation
`coshGaussMellinExt` is genuinely needed there. We show that on the
line `Re s = -1` both `archKernel` and `coshGaussMellinExt c` are
regular (no poles), and that the product is continuous as a function
of the imaginary coordinate `y`.

## Pole accounting on `Re s = -1`

* `archKernel s = Γℝ'(s)/Γℝ(s) + Γℝ'(1-s)/Γℝ(1-s)`.  Zeros of `Γℝ` are
  exactly `{0, -2, -4, …}` (`Complex.Gammaℝ_eq_zero_iff`). At
  `s = -1 + iy`, neither `s` nor `1 - s = 2 - iy` is in that set
  (`Re s = -1 ∉ {0, -2, -4, …}` and `Re (1-s) = 2 > 0`).
* `coshGaussMellinExt c s = gaussMellinClosed s + mellin (coshDiff c) s`.
  - `gaussMellinClosed s = (1/2) · 2^{-s/2} · Γ(s/2)`. The `Γ(s/2)`
    factor has poles at `s/2 ∈ {0, -1, -2, …}`, i.e. `s ∈ {0, -2, -4, …}`.
    At `s = -1 + iy`, `s/2 = -1/2 + i·(y/2)` has real part `-1/2`, not
    a non-positive integer.
  - `mellin (coshDiff c)` is analytic on `Re s > -2`
    (`coshDiffMellin_differentiableAt`).

Both factors are therefore **regular at every point of the line
`Re s = -1`** — no `y ≠ 0` hypothesis is required.

## Main results

* `archKernel_differentiableAt_at_neg_one` — `archKernel` is
  differentiable at every `-1 + i·y`.
* `coshGaussMellinExt_continuousAt_at_neg_one` — `coshGaussMellinExt c`
  is continuous at every `-1 + i·y`.
* `archKernel_coshGaussExt_continuous_on_neg_one_line` — the full
  left-edge integrand is continuous as a function of `y : ℝ`.

All proofs are axiom-clean.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelCoshGaussRectCauchyNegOne

open ZD.WeilArchKernelResidues ZD.CoshGaussMellinContinuation
  ZD.WeilPositivity.Contour ZD.ArchKernelCoshGaussRectangle

/-! ### Non-vanishing of `Γℝ` on the line `Re = -1` -/

/-- `Γℝ(-1 + i·y) ≠ 0` for every real `y`. The zeros of `Γℝ` are exactly
the non-positive even integers `{0, -2, -4, …}`, none of which has real
part `-1`. -/
private lemma Gammaℝ_neg_one_plus_I_ne_zero (y : ℝ) :
    Complex.Gammaℝ ((-1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  rw [Complex.Gammaℝ_eq_zero_iff] at hzero
  obtain ⟨n, hn⟩ := hzero
  -- Real parts: Re ((-1) + i·y) = -1, Re (-(2 * n)) = -2n.
  have hRe : ((-1 : ℂ) + (y : ℂ) * Complex.I).re = (-(2 * (n : ℂ))).re :=
    congrArg Complex.re hn
  have hL : ((-1 : ℂ) + (y : ℂ) * Complex.I).re = -1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have hR : (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := by simp
  rw [hL, hR] at hRe
  -- So `2 * n = 1` in ℝ with `n : ℕ`.
  have h_eq : (2 : ℝ) * (n : ℝ) = 1 := by linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0] at h_eq; norm_num at h_eq
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have h_ge : (2 : ℝ) * (n : ℝ) ≥ 2 := by linarith
    linarith

/-- `Γℝ(1 - (-1 + i·y)) = Γℝ(2 - i·y) ≠ 0` since the real part is
positive. -/
private lemma Gammaℝ_one_sub_neg_one_plus_I_ne_zero (y : ℝ) :
    Complex.Gammaℝ (1 - ((-1 : ℂ) + (y : ℂ) * Complex.I)) ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-! ### Differentiability of `archKernel` on the line `Re s = -1` -/

/-- `{z : Γℝ z ≠ 0}` is open. (Re-derived locally to keep this file
self-contained; mirrors the helper in `ArchKernelCoshGaussRectCauchy`.) -/
private lemma Gammaℝ_ne_zero_isOpen' : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} =
      (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {w : ℂ | w ≠ 0} := by
    ext z
    constructor
    · intro hz; exact inv_ne_zero hz
    · intro hz hzero
      apply hz
      change z.Gammaℝ⁻¹ = 0
      rw [hzero, inv_zero]
  rw [h_eq]
  exact IsOpen.preimage h_cont isOpen_ne

/-- `Γℝ` is analytic at any point where `Γℝ ≠ 0`. -/
private lemma Gammaℝ_analyticAt_of_ne_zero {s : ℂ} (hs : Complex.Gammaℝ s ≠ 0) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have hAn : AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} := by
    apply DifferentiableOn.analyticOnNhd _ Gammaℝ_ne_zero_isOpen'
    intro z hz
    exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
  exact hAn s hs

/-- `archKernel` is differentiable at every point of the form `-1 + i·y`.
The two `Γℝ` factors are non-zero on that line. -/
theorem archKernel_differentiableAt_at_neg_one (y : ℝ) :
    DifferentiableAt ℂ archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) := by
  set s : ℂ := (-1 : ℂ) + (y : ℂ) * Complex.I with hs_def
  have hg_s : Complex.Gammaℝ s ≠ 0 := Gammaℝ_neg_one_plus_I_ne_zero y
  have hg_1s : Complex.Gammaℝ (1 - s) ≠ 0 := Gammaℝ_one_sub_neg_one_plus_I_ne_zero y
  have hd_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hg_s
  have hd_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hg_1s
  have hdd_s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) s :=
    ((Gammaℝ_analyticAt_of_ne_zero hg_s).deriv).differentiableAt
  have hdd_1s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) (1 - s) :=
    ((Gammaℝ_analyticAt_of_ne_zero hg_1s).deriv).differentiableAt
  have hquot_s :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ z / Complex.Gammaℝ z) s :=
    hdd_s.div hd_s hg_s
  have hsub_diff : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) s :=
    (differentiableAt_const _).sub differentiableAt_fun_id
  have hcomp_dGam :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ (1 - z)) s := by
    have h := hdd_1s.comp s hsub_diff
    simpa using h
  have hcomp_Gam :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (1 - z)) s := by
    have h := hd_1s.comp s hsub_diff
    simpa using h
  have hquot_1s :
      DifferentiableAt ℂ
        (fun z : ℂ => deriv Complex.Gammaℝ (1 - z) / Complex.Gammaℝ (1 - z)) s :=
    hcomp_dGam.div hcomp_Gam hg_1s
  have h_sum :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          deriv Complex.Gammaℝ z / Complex.Gammaℝ z +
            deriv Complex.Gammaℝ (1 - z) / Complex.Gammaℝ (1 - z)) s :=
    hquot_s.add hquot_1s
  exact h_sum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => rfl))

/-- `archKernel` is continuous at every point of the line `Re s = -1`. -/
theorem archKernel_continuousAt_at_neg_one (y : ℝ) :
    ContinuousAt archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) :=
  (archKernel_differentiableAt_at_neg_one y).continuousAt

/-! ### Continuity of `coshGaussMellinExt c` on the line `Re s = -1` -/

/-- `coshGaussMellinExt c` is continuous at every point of the line
`Re s = -1`.

The unfolded form is `gaussMellinClosed + mellin (coshDiff c)`:

* `gaussMellinClosed s = (1/2) · 2^{-s/2} · Γ(s/2)` is differentiable at
  `s = -1 + iy` because `s/2 = -1/2 + iy/2` is not a non-positive integer.
* `mellin (coshDiff c)` is analytic on `Re s > -2`
  (`coshDiffMellin_differentiableAt`); the line `Re s = -1` lies inside.
-/
theorem coshGaussMellinExt_continuousAt_at_neg_one (c : ℝ) (y : ℝ) :
    ContinuousAt (coshGaussMellinExt c) ((-1 : ℂ) + (y : ℂ) * Complex.I) := by
  unfold coshGaussMellinExt
  set s : ℂ := (-1 : ℂ) + (y : ℂ) * Complex.I with hs_def
  have hRe_s : s.re = -1 := by
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have hRe_half : (s / 2).re = -1 / 2 := by
    rw [Complex.div_re]
    simp [hRe_s, Complex.normSq]
    norm_num
  -- `Γ(s/2)` differentiable at `s/2 = -1/2 + iy/2`. Real part is `-1/2`,
  -- not equal to `-n` for any `n : ℕ` (since `n ≥ 0` ⇒ `-n ≤ 0`, but
  -- `-1/2` is strictly between `-1` and `0`, not equal to any integer).
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro n habs
    have hRe_eq : (s / 2).re = -(n : ℝ) := by
      rw [habs]; simp
    rw [hRe_half] at hRe_eq
    -- `-1/2 = -(n : ℝ)` ⇒ `n = 1/2`, impossible for `n : ℕ`.
    have hn_int : (n : ℝ) = 1 / 2 := by linarith
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0] at hn_int; norm_num at hn_int
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      linarith
  -- `gaussMellinClosed` differentiable at `s`.
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-(z / 2))) s := by
    have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
    have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_fun_id.div_const (2 : ℂ)
    exact (hdiv.neg).const_cpow (Or.inl h2_ne)
  have hGam_comp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_fun_id.div_const (2 : ℂ)
    have h := hGamma_diff.comp s hdiv
    simpa using h
  have h_closed : DifferentiableAt ℂ gaussMellinClosed s := by
    unfold gaussMellinClosed
    exact ((differentiableAt_const ((1/2 : ℂ))).mul hpow).mul hGam_comp
  -- `mellin (coshDiff c)` differentiable at `s` since `Re s = -1 > -2`.
  have h_mellin_diff : DifferentiableAt ℂ (mellin (coshDiff c)) s := by
    have h_in : -2 < s.re := by rw [hRe_s]; norm_num
    exact ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c h_in
  exact (h_closed.add h_mellin_diff).continuousAt

/-! ### Continuity of the left-edge integrand as a function of `y` -/

/-- The left-edge integrand
`y ↦ archKernel (-1 + iy) · coshGaussMellinExt c (-1 + iy)`
is continuous on all of `ℝ`. -/
theorem archKernel_coshGaussExt_continuous_on_neg_one_line (c : ℝ) :
    Continuous (fun y : ℝ =>
      archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt c ((-1 : ℂ) + (y : ℂ) * Complex.I)) := by
  have h_param : Continuous (fun y : ℝ => ((-1 : ℂ) + (y : ℂ) * Complex.I)) := by
    have h1 : Continuous (fun y : ℝ => (y : ℂ)) := Complex.continuous_ofReal
    exact continuous_const.add (h1.mul continuous_const)
  have h_arch :
      Continuous (fun y : ℝ => archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr (fun y => ?_)
    have h_at : ContinuousAt archKernel ((-1 : ℂ) + (y : ℂ) * Complex.I) :=
      archKernel_continuousAt_at_neg_one y
    have h_inner : ContinuousAt (fun y : ℝ => ((-1 : ℂ) + (y : ℂ) * Complex.I)) y :=
      h_param.continuousAt
    exact ContinuousAt.comp (g := archKernel)
            (f := fun y : ℝ => ((-1 : ℂ) + (y : ℂ) * Complex.I)) h_at h_inner
  have h_cosh : Continuous
      (fun y : ℝ => coshGaussMellinExt c ((-1 : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr (fun y => ?_)
    have h_at :
        ContinuousAt (coshGaussMellinExt c) ((-1 : ℂ) + (y : ℂ) * Complex.I) :=
      coshGaussMellinExt_continuousAt_at_neg_one c y
    have h_inner : ContinuousAt (fun y : ℝ => ((-1 : ℂ) + (y : ℂ) * Complex.I)) y :=
      h_param.continuousAt
    exact ContinuousAt.comp (g := coshGaussMellinExt c)
            (f := fun y : ℝ => ((-1 : ℂ) + (y : ℂ) * Complex.I)) h_at h_inner
  exact h_arch.mul h_cosh

/-! ### Axiom check -/

#print axioms archKernel_differentiableAt_at_neg_one
#print axioms coshGaussMellinExt_continuousAt_at_neg_one
#print axioms archKernel_continuousAt_at_neg_one
#print axioms archKernel_coshGaussExt_continuous_on_neg_one_line

end ZD.ArchKernelCoshGaussRectCauchyNegOne

end
