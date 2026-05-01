import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Complex
import RequestProject.WeilContour
import RequestProject.WeilArchKernelResidues
import RequestProject.CoshGaussMellinContinuation
import RequestProject.ArchKernelCoshGaussRectangle

/-!
# Right-edge identification for the rectangle integrand

The rectangle Cauchy contour for the product
`f(s) = archKernel s · coshGaussMellinExt c s`
over `[-1, 2] × [-T, T]` decomposes into four edge integrals plus the
two residues at `s = 0` and `s = 1`. The right edge `Re s = 2` lies in
the original convergence half-plane of `coshGaussMellin`, so on that edge
the *meromorphic continuation* `coshGaussMellinExt c` agrees with the
original Bochner-integral definition `coshGaussMellin c`.

This file pins down that agreement at the *level of the integrand*, so
that the right-edge contribution to the rectangle integral can later be
written in its native (un-extended) form.

## Main results

* `coshGaussMellinExt_eq_coshGaussMellin_on_re_pos_line` — at any point
  `σ + i·y` with `σ > 0` the meromorphic extension agrees with the
  original Mellin transform.
* `archKernel_coshGaussExt_eq_archKernel_coshGauss_on_re_pos_line` —
  the same identity for the full integrand (archKernel pre-multiplied).
* `archKernel_coshGaussExt_eq_archKernel_coshGauss_at_two` — the
  `σ = 2` specialisation that is used on the right edge of the
  `[-1, 2] × [-T, T]` rectangle.
* `archKernel_differentiableAt_at_two` — `archKernel` is in fact
  differentiable at every `2 + i·y` (since both `Γℝ(2+iy)` and
  `Γℝ(-1-iy)` are non-zero — the only zeros of `Γℝ` are at the
  non-positive even integers).
* `archKernel_coshGaussExt_continuous_on_two_line` — the right-edge
  integrand is continuous as a function of `y : ℝ`.

All proofs are axiom-clean: they are direct unfoldings, plus the
`Complex.Gammaℝ_eq_zero_iff` characterisation of the zero locus of
`Γℝ` to rule out poles at `Re s = 2`.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelCoshGaussRectCauchy

open ZD.WeilArchKernelResidues ZD.CoshGaussMellinContinuation
  ZD.WeilPositivity.Contour ZD.ArchKernelCoshGaussRectangle

/-! ### Pointwise identification of the integrand on `Re s > 0` -/

/-- On the open right half-plane the meromorphic extension agrees with
the original Mellin transform. This is just `coshGaussMellinExt_eq_coshGaussMellin`
re-stated so that it can be applied pointwise to a complex argument
written as `σ + i·y`. -/
theorem coshGaussMellinExt_eq_coshGaussMellin_on_re_pos_line
    (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    coshGaussMellinExt c ((σ : ℂ) + (y : ℂ) * Complex.I) =
      coshGaussMellin c ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  apply coshGaussMellinExt_eq_coshGaussMellin
  -- Re ((σ : ℂ) + (y : ℂ) * I) = σ
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
  exact hσ

/-- The full integrand identity on `Re s > 0`: pre-multiplying both
sides of the previous lemma by `archKernel`. -/
theorem archKernel_coshGaussExt_eq_archKernel_coshGauss_on_re_pos_line
    (c : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    archKernel ((σ : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt c ((σ : ℂ) + (y : ℂ) * Complex.I)
      = archKernel ((σ : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellin c ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  rw [coshGaussMellinExt_eq_coshGaussMellin_on_re_pos_line c hσ y]

/-- Specialisation to the right edge `σ = 2` of the rectangle
`[-1, 2] × [-T, T]`. This is the form of the integrand that the
rectangle Cauchy theorem will actually consume on that edge. -/
theorem archKernel_coshGaussExt_eq_archKernel_coshGauss_at_two
    (c : ℝ) (y : ℝ) :
    archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt c ((2 : ℂ) + (y : ℂ) * Complex.I)
      = archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellin c ((2 : ℂ) + (y : ℂ) * Complex.I) := by
  have h := archKernel_coshGaussExt_eq_archKernel_coshGauss_on_re_pos_line
              c (show (0 : ℝ) < 2 by norm_num) y
  -- Coerce the literal `(2 : ℝ) : ℂ` to the literal `(2 : ℂ)`.
  simpa using h

/-! ### Non-vanishing of `Γℝ` on vertical lines `Re = 2` and `Re = -1` -/

/-- `Γℝ(2 + i·y) ≠ 0` for every real `y` (positive real part). -/
private lemma Gammaℝ_two_plus_I_ne_zero (y : ℝ) :
    Complex.Gammaℝ ((2 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]

/-- `Γℝ(1 - (2 + i·y)) = Γℝ(-1 - i·y) ≠ 0`. The zeros of `Γℝ` are exactly
the non-positive even integers `−2n`, none of which has imaginary part on
the line `Im = -y` paired with real part `-1`. -/
private lemma Gammaℝ_one_sub_two_plus_I_ne_zero (y : ℝ) :
    Complex.Gammaℝ (1 - ((2 : ℂ) + (y : ℂ) * Complex.I)) ≠ 0 := by
  intro hzero
  rw [Complex.Gammaℝ_eq_zero_iff] at hzero
  obtain ⟨n, hn⟩ := hzero
  -- Real part of LHS = -1, real part of RHS = -2n.
  have hRe : (1 - ((2 : ℂ) + (y : ℂ) * Complex.I)).re = (-(2 * (n : ℂ))).re :=
    congrArg Complex.re hn
  -- Simplify both sides explicitly.
  have hRe' : (-1 : ℝ) = -(2 * (n : ℝ)) := by
    have hL : (1 - ((2 : ℂ) + (y : ℂ) * Complex.I)).re = -1 := by
      simp; ring
    have hR : (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := by
      simp
    rw [hL, hR] at hRe
    exact hRe
  -- So `2 * n = 1` in ℝ, with `n : ℕ`.
  have h_eq : (2 : ℝ) * (n : ℝ) = 1 := by linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0] at h_eq; norm_num at h_eq
  · have h_ge : (2 : ℝ) * (n : ℝ) ≥ 2 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      linarith
    linarith

/-! ### Differentiability of `archKernel` on the line `Re s = 2` -/

/-- `{z : Γℝ z ≠ 0}` is open. (Same proof as in `WeilArchKernelResidues`,
extracted as a private helper so we can re-use it in two places.) -/
private lemma Gammaℝ_ne_zero_isOpen' : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} =
      (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {w : ℂ | w ≠ 0} := by
    ext z
    constructor
    · intro hz; exact inv_ne_zero hz
    · intro hz hzero
      -- `hz : z.Gammaℝ⁻¹ ≠ 0`; `hzero : z.Gammaℝ = 0` ⇒ `z.Gammaℝ⁻¹ = 0`.
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

/-- `archKernel` is differentiable at every point of the form `2 + i·y`.
The two `Γℝ` factors in the denominator are non-zero on that line, so
both terms `Γℝ'(s)/Γℝ(s)` and `Γℝ'(1-s)/Γℝ(1-s)` are differentiable
there. -/
theorem archKernel_differentiableAt_at_two (y : ℝ) :
    DifferentiableAt ℂ archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) := by
  set s : ℂ := (2 : ℂ) + (y : ℂ) * Complex.I with hs_def
  have hg_s : Complex.Gammaℝ s ≠ 0 := Gammaℝ_two_plus_I_ne_zero y
  have hg_1s : Complex.Gammaℝ (1 - s) ≠ 0 := Gammaℝ_one_sub_two_plus_I_ne_zero y
  have hd_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hg_s
  have hd_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hg_1s
  have hdd_s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) s :=
    ((Gammaℝ_analyticAt_of_ne_zero hg_s).deriv).differentiableAt
  have hdd_1s : DifferentiableAt ℂ (deriv Complex.Gammaℝ) (1 - s) :=
    ((Gammaℝ_analyticAt_of_ne_zero hg_1s).deriv).differentiableAt
  -- First summand: differentiability of `s ↦ Γℝ'(s) / Γℝ(s)`.
  have hquot_s :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ z / Complex.Gammaℝ z) s :=
    hdd_s.div hd_s hg_s
  -- Second summand: compose with `1 - ·`.
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
  -- archKernel = sum of the two quotients (definitionally).
  have h_sum :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          deriv Complex.Gammaℝ z / Complex.Gammaℝ z +
            deriv Complex.Gammaℝ (1 - z) / Complex.Gammaℝ (1 - z)) s :=
    hquot_s.add hquot_1s
  -- Match shape with `archKernel`.
  exact h_sum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => rfl))

/-! ### Continuity of the right-edge integrand as a function of `y` -/

/-- Continuity of `coshGaussMellinExt c` at every point of the line
`Re s = 2`. (Pointwise argument: at such a point `coshGaussMellinExt`
agrees with `coshGaussMellin`, and the latter is the Mellin integral of
a continuous-in-`s` family.) -/
theorem coshGaussMellinExt_continuousAt_at_two (c : ℝ) (y : ℝ) :
    ContinuousAt (coshGaussMellinExt c) ((2 : ℂ) + (y : ℂ) * Complex.I) := by
  -- Use analyticity of `coshGaussMellinExt c` away from `s = 0`.
  -- `(2 : ℂ) + i·y ≠ 0` and lies in `stripRectOffZero`-style open set
  -- (-1 < Re < 2 fails: Re = 2, on the boundary). Use the strip
  -- `Re > -2`: the meromorphic-on lemma + the fact that the function is
  -- analytic at any non-pole.  Easier path: re-derive analyticity from
  -- `coshGaussMellinExt = gaussMellinClosed + mellin coshDiff`.
  unfold coshGaussMellinExt
  -- `gaussMellinClosed` is analytic everywhere except at `s/2 ∈ {0, -1, -2, …}`.
  -- The point `2 + iy` has `s/2 = 1 + iy/2`, with real part 1 > 0, so
  -- `Γ(s/2)` is differentiable there.
  set s : ℂ := (2 : ℂ) + (y : ℂ) * Complex.I with hs_def
  have hRe_s : s.re = 2 := by
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have hRe_half : (s / 2).re = 1 := by
    rw [Complex.div_re]
    simp [hRe_s, Complex.normSq]
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro n habs
    have hRe_neg : (s / 2).re = -(n : ℝ) := by
      rw [habs]; simp
    rw [hRe_half] at hRe_neg
    -- 1 = -n with n : ℕ — impossible.
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
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
  -- Continuity of `mellin (coshDiff c)` at `s`: use that `coshDiffMellin`
  -- is differentiable on `Re s > -2`.
  have h_mellin_diff : DifferentiableAt ℂ (mellin (coshDiff c)) s := by
    have h_in : -2 < s.re := by rw [hRe_s]; norm_num
    exact ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c h_in
  exact (h_closed.add h_mellin_diff).continuousAt

/-- Continuity of `archKernel` at every point of the line `Re s = 2`. -/
theorem archKernel_continuousAt_at_two (y : ℝ) :
    ContinuousAt archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) :=
  (archKernel_differentiableAt_at_two y).continuousAt

/-- The right-edge integrand `y ↦ archKernel (2+iy) · coshGaussMellinExt c (2+iy)`
is continuous on all of `ℝ`. -/
theorem archKernel_coshGaussExt_continuous_on_two_line (c : ℝ) :
    Continuous (fun y : ℝ =>
      archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellinExt c ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
  -- Both factors are continuous in `s` at each `2 + iy`, and `y ↦ 2 + iy`
  -- is continuous.
  have h_param : Continuous (fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    have h1 : Continuous (fun y : ℝ => (y : ℂ)) := Complex.continuous_ofReal
    exact continuous_const.add (h1.mul continuous_const)
  have h_arch : Continuous (fun y : ℝ => archKernel ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr (fun y => ?_)
    -- The function is `archKernel ∘ (fun y => (2 : ℂ) + (y : ℂ) * I)`.
    have h_at : ContinuousAt archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) :=
      archKernel_continuousAt_at_two y
    have h_inner : ContinuousAt (fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) y :=
      h_param.continuousAt
    exact ContinuousAt.comp (g := archKernel)
            (f := fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) h_at h_inner
  have h_cosh : Continuous
      (fun y : ℝ => coshGaussMellinExt c ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr (fun y => ?_)
    have h_at : ContinuousAt (coshGaussMellinExt c) ((2 : ℂ) + (y : ℂ) * Complex.I) :=
      coshGaussMellinExt_continuousAt_at_two c y
    have h_inner : ContinuousAt (fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) y :=
      h_param.continuousAt
    exact ContinuousAt.comp (g := coshGaussMellinExt c)
            (f := fun y : ℝ => ((2 : ℂ) + (y : ℂ) * Complex.I)) h_at h_inner
  exact h_arch.mul h_cosh

/-- The same continuity statement but expressed in terms of the original
(un-extended) `coshGaussMellin`. Useful for any subsequent right-edge
integral identification. -/
theorem archKernel_coshGauss_continuous_on_two_line (c : ℝ) :
    Continuous (fun y : ℝ =>
      archKernel ((2 : ℂ) + (y : ℂ) * Complex.I) *
        coshGaussMellin c ((2 : ℂ) + (y : ℂ) * Complex.I)) := by
  -- Replace `coshGaussMellinExt` by `coshGaussMellin` pointwise.
  have h := archKernel_coshGaussExt_continuous_on_two_line c
  refine h.congr (fun y => ?_)
  exact archKernel_coshGaussExt_eq_archKernel_coshGauss_at_two c y

/-! ### Axiom check -/

#print axioms coshGaussMellinExt_eq_coshGaussMellin_on_re_pos_line
#print axioms archKernel_coshGaussExt_eq_archKernel_coshGauss_at_two
#print axioms archKernel_differentiableAt_at_two
#print axioms coshGaussMellinExt_continuousAt_at_two
#print axioms archKernel_coshGaussExt_continuous_on_two_line
#print axioms archKernel_coshGauss_continuous_on_two_line

end ZD.ArchKernelCoshGaussRectCauchy

end
