import Mathlib
import RequestProject.CoshGaussMellinContinuation
import RequestProject.CoshGaussMellinResidue

/-!
# Boundedness of `coshGaussMellinExt c` on a strip avoiding the pole

The function `coshGaussMellinExt c` constructed in
`CoshGaussMellinContinuation.lean` is meromorphic on the strip `Re s > -2`
with the unique pole at `s = 0`.  In particular, on any compact subset of
`{ Re s > -2 } \ {0}` it is continuous and hence bounded.

This file proves a quantitative version of this boundedness statement: for
any `δ > 0` and any height parameter `Y > 0`, the function is bounded on
the compact rectangle

```
{ σ + i·y :  σ ∈ [-1 + δ, 1 - δ],  δ ≤ |y| ≤ Y }.
```

This rectangle stays inside `{ Re s > -2 } \ {0}` because:

* `σ ≥ -1 + δ > -2`, so the strip condition `Re s > -2` holds with
  `σ ≥ -1 + δ > -2`.
* `|y| ≥ δ > 0`, so `s ≠ 0`.
* For the same reason `s/2` has nonzero imaginary part `y/2 ≠ 0`, hence
  `s/2 ∉ {0, -1, -2, ...}` and `Γ(s/2)` is analytic at `s/2`.

The proof structure:

1. Show `coshGaussMellinExt c` is differentiable (and hence continuous) at
   every point `s = σ + i·y` with `σ > -2` and `y ≠ 0`.  This combines the
   analyticity of the closed-form Gauss-Mellin (away from the integer
   zeros of `Γ`) and the analyticity of the cosh-difference Mellin
   (proved in `CoshGaussMellinContinuation.lean` /
   `CoshGaussMellinResidue.lean`).
2. The compact rectangle described above is closed and bounded in `ℂ`,
   hence compact.
3. Apply `IsCompact.exists_bound_of_continuousOn`.

The σ-range `σ ∈ [-1 + δ, 1 - δ]` is the user's request.  In fact the
same proof gives a bound on the larger compact set
`σ ∈ [-2 + δ, A]` for any finite `A`, but we package the requested
σ-window for convenience.

## Why no quadratic decay in `y`

The user's first ask was the quadratic bound

```
‖coshGaussMellinExt c (σ + iy)‖ ≤ K · (1 + y²)⁻¹.
```

That bound *fails* uniformly across `σ ∈ (-1, 1)` because of the simple
pole at `s = 0`: as `y → 0` with `σ = 0`, the function blows up like
`1/y`, and any polynomial-decay bound `K · (1 + y²)⁻¹` would force
boundedness near `y = 0`.  The honest replacement is the present
"bounded on a compact rectangle avoiding the pole" statement.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.CoshGaussMellinExtStripBound

open ZD.CoshGaussMellinContinuation

/-! ### Differentiability of the pieces -/

/-- `gaussMellinClosed` is differentiable at every `s` with `s.im ≠ 0`.
The constraint `s.im ≠ 0` ensures `s/2` has nonzero imaginary part and
hence `s/2 ∉ {0, -1, -2, ...}`, so `Γ(s/2)` is differentiable at `s/2`.
The factor `2^{-(s/2)}` is entire. -/
lemma gaussMellinClosed_differentiableAt {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ gaussMellinClosed s := by
  unfold gaussMellinClosed
  -- Constant `1/2`
  have h_const : DifferentiableAt ℂ (fun _ : ℂ => (1/2 : ℂ)) s :=
    differentiableAt_const _
  -- Power `2^(-(s/2))`
  have h_pow : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (-(s/2))) s := by
    have h_base : DifferentiableAt ℂ (fun _ : ℂ => (2 : ℂ)) s :=
      differentiableAt_const _
    have h_id : DifferentiableAt ℂ (fun s : ℂ => s) s := differentiableAt_id
    have h_div : DifferentiableAt ℂ (fun s : ℂ => s/2) s := h_id.div_const _
    have h_neg : DifferentiableAt ℂ (fun s : ℂ => -(s/2)) s := h_div.neg
    -- Use AnalyticAt.differentiableAt path through cpow
    have h_base_an : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) s := analyticAt_const
    have h_id_an : AnalyticAt ℂ (fun s : ℂ => s) s := analyticAt_id
    have h_div_an : AnalyticAt ℂ (fun s : ℂ => s/2) s := h_id_an.div_const
    have h_neg_an : AnalyticAt ℂ (fun s : ℂ => -(s/2)) s := h_div_an.neg
    have h_slit : (2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; norm_num
    exact (h_base_an.cpow h_neg_an h_slit).differentiableAt
  -- Gamma at s/2: need s/2 ≠ -m for all m : ℕ.
  have h_gamma : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s/2)) s := by
    have h_div : DifferentiableAt ℂ (fun s : ℂ => s/2) s :=
      differentiableAt_id.div_const _
    have h_im_ne : (s/2).im ≠ 0 := by
      have h_eq : (s/2).im = s.im / 2 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
            Complex.div_ofReal_im]
      rw [h_eq]
      exact div_ne_zero hs (by norm_num)
    have h_gamma_at : DifferentiableAt ℂ Complex.Gamma (s/2) := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      -- s/2 = -m would force (s/2).im = 0, contradicting hs.
      have h_im : (s/2).im = (-(m : ℂ)).im := by rw [hm]
      simp at h_im
      -- h_im : s.im = 0
      exact hs h_im
    exact DifferentiableAt.comp s h_gamma_at h_div
  -- Combine: (1/2) * 2^(-(s/2)) * Γ(s/2)
  exact (h_const.mul h_pow).mul h_gamma

/-- `mellin (coshDiff c)` is differentiable at every `s` with `Re s > -2`.
This is just a restatement of `coshDiffMellin_differentiableAt` from
`CoshGaussMellinResidue.lean`, after unfolding `coshDiff`. -/
lemma coshDiffMellin_differentiableAt' (c : ℝ) {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (coshDiff c)) s := by
  have h := ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c hs
  -- h : DifferentiableAt ℂ (mellin (fun t : ℝ => (((Real.cosh (c*t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) s
  -- coshDiff is definitionally that.
  have h_eq : (mellin (coshDiff c)) =
      (mellin (fun t : ℝ =>
        (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) := rfl
  rw [h_eq]; exact h

/-- `coshGaussMellinExt c` is differentiable on
`{ s | -2 < s.re ∧ s.im ≠ 0 }`. -/
lemma coshGaussMellinExt_differentiableAt (c : ℝ) {s : ℂ}
    (hs_re : -2 < s.re) (hs_im : s.im ≠ 0) :
    DifferentiableAt ℂ (coshGaussMellinExt c) s := by
  unfold coshGaussMellinExt
  exact (gaussMellinClosed_differentiableAt hs_im).add
    (coshDiffMellin_differentiableAt' c hs_re)

/-- `coshGaussMellinExt c` is continuous at every point with `Re s > -2`
and `s.im ≠ 0`. -/
lemma coshGaussMellinExt_continuousAt (c : ℝ) {s : ℂ}
    (hs_re : -2 < s.re) (hs_im : s.im ≠ 0) :
    ContinuousAt (coshGaussMellinExt c) s :=
  (coshGaussMellinExt_differentiableAt c hs_re hs_im).continuousAt

/-! ### The compact box parameterization -/

/-- The map `(σ, y) ↦ σ + i·y` is continuous. -/
private lemma continuous_mk_complex :
    Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const

/-- The product set `Icc (-1 + δ) (1 - δ) ×ˢ (Icc (-Y) (-δ) ∪ Icc δ Y)`
is compact in `ℝ × ℝ`. -/
private lemma compact_param_box {δ Y : ℝ} :
    IsCompact ((Set.Icc (-1 + δ) (1 - δ)) ×ˢ
                (Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y)) := by
  apply IsCompact.prod isCompact_Icc
  exact (isCompact_Icc).union isCompact_Icc

/-- Given `(σ, y) ∈ Icc (-1 + δ) (1 - δ) ×ˢ (Icc (-Y) (-δ) ∪ Icc δ Y)`
with `δ > 0`, the corresponding complex point `s = σ + iy` satisfies
`-2 < s.re` and `s.im ≠ 0`. -/
private lemma point_in_safe_region {δ Y : ℝ} (hδ : 0 < δ)
    {σ y : ℝ}
    (hσ : σ ∈ Set.Icc (-1 + δ) (1 - δ))
    (hy : y ∈ Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y) :
    -2 < ((σ : ℂ) + (y : ℂ) * Complex.I).re ∧
    ((σ : ℂ) + (y : ℂ) * Complex.I).im ≠ 0 := by
  have h_re_eq : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
  have h_im_eq : ((σ : ℂ) + (y : ℂ) * Complex.I).im = y := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
  refine ⟨?_, ?_⟩
  · rw [h_re_eq]
    have h_lb : -1 + δ ≤ σ := hσ.1
    linarith
  · rw [h_im_eq]
    rcases hy with hy1 | hy2
    · -- y ∈ Icc (-Y) (-δ); then y ≤ -δ < 0.
      have : y ≤ -δ := hy1.2
      intro h0
      rw [h0] at this
      linarith
    · -- y ∈ Icc δ Y; then δ ≤ y, so y > 0.
      have : δ ≤ y := hy2.1
      intro h0
      rw [h0] at this
      linarith

/-- Continuity of `(σ, y) ↦ ‖coshGaussMellinExt c (σ + iy)‖` on the
parameter rectangle `Icc (-1 + δ) (1 - δ) ×ˢ (Icc (-Y) (-δ) ∪ Icc δ Y)`. -/
private lemma continuousOn_norm_extOnRect (c : ℝ) {δ Y : ℝ} (hδ : 0 < δ) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ‖coshGaussMellinExt c ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖)
      ((Set.Icc (-1 + δ) (1 - δ)) ×ˢ
        (Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y)) := by
  intro p hp
  -- Pointwise continuity at `p`.
  have hσ : p.1 ∈ Set.Icc (-1 + δ) (1 - δ) := hp.1
  have hy : p.2 ∈ Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y := hp.2
  obtain ⟨h_re, h_im⟩ := point_in_safe_region (Y := Y) hδ hσ hy
  have h_cont_pt :
      ContinuousAt (coshGaussMellinExt c)
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    coshGaussMellinExt_continuousAt c h_re h_im
  have h_cont_param :
      ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) p :=
    continuous_mk_complex.continuousAt
  have h_comp :
      ContinuousAt
        (fun q : ℝ × ℝ => coshGaussMellinExt c ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))
        p :=
    ContinuousAt.comp (g := coshGaussMellinExt c)
      (f := fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I)
      (x := p) h_cont_pt h_cont_param
  have h_norm :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          ‖coshGaussMellinExt c ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖) p :=
    continuous_norm.continuousAt.comp h_comp
  exact h_norm.continuousWithinAt

/-! ### Main theorem: bound on a compact rectangle avoiding the pole -/

/-- **Bound on a compact rectangle avoiding the pole at `s = 0`.**

For any `δ > 0` and any `Y ≥ δ`, the function `coshGaussMellinExt c`
is bounded on the rectangle

```
{ σ + i·y :  σ ∈ [-1 + δ, 1 - δ],  δ ≤ |y| ≤ Y }.
```

The σ-range covers most of the desired strip `(-1, 1)` (excluding only a
δ-buffer at the endpoints σ = ±1, which are not even in the open
interval), and the bound on `|y|` excludes the pole at `s = 0` (lower)
and is trivially required to make the rectangle compact (upper).

This is the honest "boundedness" version of the failed-quadratic-decay
target on the σ ∈ (-1, 1) strip. -/
theorem coshGaussMellinExt_bounded_on_box (c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (Y : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ σ : ℝ, σ ∈ Set.Icc (-1 + δ) (1 - δ) →
        ∀ y : ℝ, δ ≤ |y| → |y| ≤ Y →
          ‖ZD.CoshGaussMellinContinuation.coshGaussMellinExt c
              ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K := by
  -- Compact parameter box.
  set K_box : Set (ℝ × ℝ) :=
    (Set.Icc (-1 + δ) (1 - δ)) ×ˢ
      (Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y) with hK_box_def
  have h_compact : IsCompact K_box := compact_param_box
  -- Continuous norm function on the box.
  have h_cont :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          ‖coshGaussMellinExt c ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖)
        K_box :=
    continuousOn_norm_extOnRect c hδ
  -- Apply compact-bound (norm version).  The function is real-valued and
  -- we use `IsCompact.exists_bound_of_continuousOn`.
  obtain ⟨M, hM⟩ := h_compact.exists_bound_of_continuousOn h_cont
  -- M is a bound on the absolute value of the (already nonneg) norm.
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro σ hσ y hy_lo hy_hi
  -- Membership in the box.
  have hy_box : y ∈ Set.Icc (-Y) (-δ) ∪ Set.Icc δ Y := by
    rcases le_or_gt 0 y with hy0 | hy0
    · -- y ≥ 0 ⇒ |y| = y, so δ ≤ y ≤ Y.
      have h1 : δ ≤ y := by rw [abs_of_nonneg hy0] at hy_lo; exact hy_lo
      have h2 : y ≤ Y := by rw [abs_of_nonneg hy0] at hy_hi; exact hy_hi
      exact Or.inr ⟨h1, h2⟩
    · -- y < 0 ⇒ |y| = -y, so δ ≤ -y ≤ Y, i.e., -Y ≤ y ≤ -δ.
      have h1 : δ ≤ -y := by rw [abs_of_neg hy0] at hy_lo; exact hy_lo
      have h2 : -y ≤ Y := by rw [abs_of_neg hy0] at hy_hi; exact hy_hi
      exact Or.inl ⟨by linarith, by linarith⟩
  have hp : (σ, y) ∈ K_box := ⟨hσ, hy_box⟩
  have h_norm_le := hM (σ, y) hp
  -- h_norm_le : ‖‖cGMExt c (σ + iy)‖‖ ≤ M
  have h_abs_eq : ‖‖coshGaussMellinExt c ((σ : ℂ) + (y : ℂ) * Complex.I)‖‖ =
      ‖coshGaussMellinExt c ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [h_abs_eq] at h_norm_le
  exact h_norm_le.trans (le_max_right _ _)

#print axioms coshGaussMellinExt_bounded_on_box

end ZD.CoshGaussMellinExtStripBound
