import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Complex
import RequestProject.WeilContour
import RequestProject.CoshGaussMellinResidue

/-!
# Meromorphic continuation of `coshGaussMellin`

The function `coshGaussMellin c s = ∫_0^∞ cosh(c·t)·exp(-2t²)·t^{s-1} dt` is
defined as a Bochner integral, hence equals `0` for `Re s ≤ 0` (where the
integrand is non-integrable). This file constructs an explicit *meromorphic*
continuation that agrees with the original on the convergent half-plane
`Re s > 0`.

## Key idea

On `Re s > 0` we have

```
coshGaussMellin c s = gaussMellin s + (coshGaussMellin c s - gaussMellin s)
                    = gaussMellin s + mellin diff s
```

where `diff t = (cosh(c·t) − 1) · exp(−2t²)` (proved by
`coshGaussMellin_sub_gaussMellin_eq`).

* `gaussMellin s = (1/2) · 2^{-s/2} · Γ(s/2)` admits a global meromorphic
  expression (the closed form is meromorphic on all of `ℂ`, with simple poles
  at `s = 0, -2, -4, …`).
* `mellin diff s` is *holomorphic* on `Re s > -2` (proved by
  `coshDiffMellin_differentiableAt`) since `diff t = O(t²)` near `0⁺`.

We therefore define

```
coshGaussMellinExt c s := (1/2) · 2^{-s/2} · Γ(s/2) + mellin diff s.
```

This is meromorphic on the strip `Re s > -2`, holomorphic on
`{Re s > -2} \ {0}`, with a simple pole of residue `1` at `s = 0`. It agrees
with `coshGaussMellin c` on `Re s > 0`.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.CoshGaussMellinContinuation

open ZD.WeilPositivity.Contour ZD.CoshGaussMellinResidue

/-- The "cosh-difference" integrand whose Mellin transform extends across
`s = 0`. -/
def coshDiff (c : ℝ) : ℝ → ℂ :=
  fun t => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)

/-- The closed-form meromorphic representative of `gaussMellin`. Globally
defined and meromorphic on all of `ℂ`. -/
def gaussMellinClosed (s : ℂ) : ℂ :=
  (1/2 : ℂ) * (2 : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)

/-- **Meromorphic continuation of `coshGaussMellin c`.** For `Re s > 0` it
agrees with `coshGaussMellin c s`; on the strip `Re s > -2` it is meromorphic,
with the sole pole at `s = 0`. -/
def coshGaussMellinExt (c : ℝ) (s : ℂ) : ℂ :=
  gaussMellinClosed s + mellin (coshDiff c) s

/-! ### Agreement with `gaussMellin` and `coshGaussMellin` on the half-plane -/

theorem gaussMellinClosed_eq_gaussMellin {s : ℂ} (hs : 0 < s.re) :
    gaussMellinClosed s = gaussMellin s := by
  rw [gaussMellinClosed, gaussMellin_closed_form hs]

theorem coshGaussMellinExt_eq_coshGaussMellin (c : ℝ) {s : ℂ} (hs : 0 < s.re) :
    coshGaussMellinExt c s = coshGaussMellin c s := by
  unfold coshGaussMellinExt coshDiff
  rw [gaussMellinClosed_eq_gaussMellin hs]
  have h := coshGaussMellin_sub_gaussMellin_eq c hs
  -- h : coshGaussMellin c s - gaussMellin s = mellin diff s
  linear_combination -h

/-! ### Helper: openness of the strip -/

private lemma isOpen_re_gt (a : ℝ) : IsOpen {z : ℂ | a < z.re} := by
  have h : {z : ℂ | a < z.re} = Complex.re ⁻¹' Set.Ioi a := rfl
  exact h ▸ (isOpen_Ioi.preimage Complex.continuous_re)

/-! ### Meromorphicity of `gaussMellinClosed` -/

/-- `gaussMellinClosed` is meromorphic on any set. Poles are at `s = 0,
−2, −4, …` (where `Γ(s/2)` has poles). -/
theorem gaussMellinClosed_meromorphicOn (U : Set ℂ) :
    MeromorphicOn gaussMellinClosed U := by
  -- gaussMellinClosed = (1/2) · ((2)^(-(s/2))) · Γ(s/2)
  have h_const : MeromorphicOn (fun _ : ℂ => (1/2 : ℂ)) U := MeromorphicOn.const _
  have h_pow : MeromorphicOn (fun s : ℂ => (2 : ℂ) ^ (-(s/2))) U := by
    apply AnalyticOnNhd.meromorphicOn
    intro s _
    -- 2^(-(s/2)) = (const 2)^(-(s/2)); both base and exponent analytic, base in slitPlane.
    have h_base : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) s := analyticAt_const
    have h_exp : AnalyticAt ℂ (fun s : ℂ => -(s/2)) s := by
      have h_id : AnalyticAt ℂ (fun s : ℂ => s) s := analyticAt_id
      have h_div : AnalyticAt ℂ (fun s : ℂ => s/2) s := h_id.div_const
      exact h_div.neg
    have h_slit : (2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left; norm_num
    exact h_base.cpow h_exp h_slit
  have h_gamma : MeromorphicOn (fun s : ℂ => Complex.Gamma (s/2)) U := by
    intro s _
    -- Use congr to switch to `Γ ∘ (·/2)` form.
    have h_gam_at : MeromorphicAt Complex.Gamma (s/2) := Meromorphic.Gamma _
    have h_id : AnalyticAt ℂ (fun s : ℂ => s) s := analyticAt_id
    have h_div : AnalyticAt ℂ (fun s : ℂ => s/2) s := h_id.div_const
    -- Provide the goal in `f ∘ g` form by reasoning about composition.
    have h_comp :
        MeromorphicAt (fun z : ℂ => Complex.Gamma ((fun w : ℂ => w/2) z)) s := by
      have h := MeromorphicAt.comp_analyticAt
        (𝕜 := ℂ) (𝕜' := ℂ) (F := ℂ)
        (f := Complex.Gamma) (g := fun w : ℂ => w/2) (x := s) h_gam_at h_div
      -- h : MeromorphicAt (Complex.Gamma ∘ fun w => w/2) s
      exact h
    exact h_comp
  have h_prod1 : MeromorphicOn
      (fun s : ℂ => (1/2 : ℂ) * ((2 : ℂ) ^ (-(s/2)))) U :=
    h_const.mul h_pow
  have h_prod2 : MeromorphicOn
      (fun s : ℂ => (1/2 : ℂ) * ((2 : ℂ) ^ (-(s/2))) * Complex.Gamma (s/2)) U :=
    h_prod1.mul h_gamma
  exact h_prod2

/-! ### Holomorphicity of `mellin (coshDiff c)` on `Re s > -2` -/

theorem coshDiffMellin_analyticAt (c : ℝ) {s : ℂ} (hs : -2 < s.re) :
    AnalyticAt ℂ (mellin (coshDiff c)) s := by
  -- Rewrite mellin (coshDiff c) to match the form used in CoshGaussMellinResidue.
  have h_eq : (mellin (coshDiff c)) =
              (mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) := by
    rfl
  rw [h_eq]
  -- DifferentiableAt → AnalyticAt via DifferentiableOn on open neighborhood.
  have h_open : IsOpen {z : ℂ | -2 < z.re} := isOpen_re_gt (-2)
  have h_diffOn :
      DifferentiableOn ℂ
        (mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)))
        {z : ℂ | -2 < z.re} := by
    intro z hz
    exact (coshDiffMellin_differentiableAt c hz).differentiableWithinAt
  have h_anOn :
      AnalyticOnNhd ℂ
        (mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)))
        {z : ℂ | -2 < z.re} :=
    h_diffOn.analyticOnNhd h_open
  exact h_anOn s hs

theorem coshDiffMellin_meromorphicOn_strip (c : ℝ) :
    MeromorphicOn (mellin (coshDiff c)) {s : ℂ | -2 < s.re} := by
  apply AnalyticOnNhd.meromorphicOn
  intro s hs
  exact coshDiffMellin_analyticAt c hs

/-! ### Main meromorphicity statement -/

/-- **Main theorem.** `coshGaussMellinExt c` is meromorphic on the strip
`Re s > -2`. The unique pole in this strip is the simple pole at `s = 0`. -/
theorem coshGaussMellinExt_meromorphic_strip_neg_two (c : ℝ) :
    MeromorphicOn (coshGaussMellinExt c) {s : ℂ | -2 < s.re} := by
  have h_g : MeromorphicOn gaussMellinClosed {s : ℂ | -2 < s.re} :=
    gaussMellinClosed_meromorphicOn _
  have h_d : MeromorphicOn (mellin (coshDiff c)) {s : ℂ | -2 < s.re} :=
    coshDiffMellin_meromorphicOn_strip c
  -- `coshGaussMellinExt c = gaussMellinClosed + mellin coshDiff` pointwise.
  have h_eq : coshGaussMellinExt c =
              (fun s : ℂ => gaussMellinClosed s + mellin (coshDiff c) s) := by
    funext s; rfl
  rw [h_eq]
  exact h_g.add h_d

/-- **Corollary:** weaker statement on the strip `Re s > -1` (matches the user's
target signature). -/
theorem coshGaussMellinExt_meromorphic_strip_neg_one (c : ℝ) :
    MeromorphicOn (coshGaussMellinExt c) {s : ℂ | -1 < s.re} := by
  apply (coshGaussMellinExt_meromorphic_strip_neg_two c).mono_set
  intro s hs
  show -2 < s.re
  have : (-1 : ℝ) < s.re := hs
  linarith

/-! ### Residue at `s = 0` -/

/-- **Residue at zero — full filter version.** Since `coshGaussMellinExt c` IS
the meromorphic continuation, the limit `s · coshGaussMellinExt c s → 1`
holds along the full filter `nhdsWithin 0 {0}ᶜ`, not just the half-plane. -/
theorem coshGaussMellinExt_residue_at_zero (c : ℝ) :
    Tendsto (fun s : ℂ => s * coshGaussMellinExt c s)
      (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (1:ℂ)) := by
  -- s · coshGaussMellinExt c s = s · gaussMellinClosed s + s · mellin diff s.
  unfold coshGaussMellinExt
  have h_split : (fun s : ℂ => s * (gaussMellinClosed s + mellin (coshDiff c) s))
                  = (fun s : ℂ => s * gaussMellinClosed s + s * mellin (coshDiff c) s) := by
    funext s; ring
  rw [h_split]
  -- Piece 1: s · gaussMellinClosed s → 1 along nhdsWithin 0 {0}ᶜ.
  have h1 : Tendsto (fun s : ℂ => s * gaussMellinClosed s)
              (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (1:ℂ)) := by
    have h_eqf : (fun s : ℂ => s * gaussMellinClosed s) =
                 (fun s : ℂ => (2:ℂ)^(-(s/2)) * ((s/2) * Complex.Gamma (s/2))) := by
      funext s; unfold gaussMellinClosed; ring
    rw [h_eqf]
    have h_pow : Tendsto (fun s : ℂ => (2:ℂ)^(-(s/2)))
                  (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (1:ℂ)) := by
      have h_b_cont : ContinuousAt (fun s : ℂ => -(s/2)) 0 := by
        apply Continuous.continuousAt; continuity
      have hbase : ContinuousAt (fun z : ℂ => (2:ℂ)^z) (-((0:ℂ)/2)) :=
        continuousAt_const_cpow (by norm_num : (2:ℂ) ≠ 0)
      have h_cont : ContinuousAt (fun s : ℂ => (2:ℂ)^(-(s/2))) 0 :=
        ContinuousAt.comp (g := fun z : ℂ => (2:ℂ)^z) (f := fun s : ℂ => -(s/2)) (x := 0)
          (by show ContinuousAt _ ((fun s : ℂ => -(s/2)) 0); convert hbase using 1)
          h_b_cont
      have hval : (2:ℂ)^(-((0:ℂ)/2)) = 1 := by simp
      have h_full : Tendsto (fun s : ℂ => (2:ℂ)^(-(s/2))) (𝓝 (0:ℂ)) (𝓝 (1:ℂ)) := by
        rw [show (1:ℂ) = (2:ℂ)^(-((0:ℂ)/2)) from hval.symm]
        rw [ContinuousAt] at h_cont; exact h_cont
      exact h_full.mono_left nhdsWithin_le_nhds
    have h_gam : Tendsto (fun s : ℂ => (s/2) * Complex.Gamma (s/2))
                  (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (1:ℂ)) := by
      have h_arg : Tendsto (fun s : ℂ => s / 2)
                   (nhdsWithin (0:ℂ) {0}ᶜ) (nhdsWithin (0:ℂ) {0}ᶜ) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun s : ℂ => s / 2) (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by
            have h := (continuous_id.div_const (2:ℂ)).continuousAt (x := (0:ℂ))
            simpa [ContinuousAt] using h
          exact this.mono_left nhdsWithin_le_nhds
        · -- eventually s/2 ≠ 0 along nhdsWithin 0 {0}ᶜ
          have h_self : ({0}ᶜ : Set ℂ) ∈ nhdsWithin (0:ℂ) {0}ᶜ := self_mem_nhdsWithin
          filter_upwards [h_self] with s hs
          intro h0
          have h0' : s / 2 = 0 := h0
          have hs_eq : s = 0 := by
            have h_iff := div_eq_zero_iff.mp h0'
            rcases h_iff with h | h
            · exact h
            · exfalso; norm_num at h
          exact hs hs_eq
      exact Complex.tendsto_self_mul_Gamma_nhds_zero.comp h_arg
    have h_prod := h_pow.mul h_gam
    simpa using h_prod
  -- Piece 2: s · mellin diff s → 0.
  have h2 : Tendsto (fun s : ℂ => s * mellin (coshDiff c) s)
              (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (0:ℂ)) := by
    have h_diff_at_zero :
        DifferentiableAt ℂ
          (mellin (fun t : ℝ => (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ)))
          0 := by
      apply coshDiffMellin_differentiableAt c
      show (-2:ℝ) < (0:ℂ).re
      simp
    have h_diff_at_zero' : DifferentiableAt ℂ (mellin (coshDiff c)) 0 := by
      have h_eq : (mellin (coshDiff c)) =
                  (mellin (fun t : ℝ =>
                    (((Real.cosh (c * t) - 1) * Real.exp (-2 * t^2) : ℝ) : ℂ))) := rfl
      rw [h_eq]; exact h_diff_at_zero
    have h_cont : ContinuousAt (mellin (coshDiff c)) 0 :=
      h_diff_at_zero'.continuousAt
    have h_id_cont : ContinuousAt (fun s : ℂ => s) 0 := continuous_id.continuousAt
    have h_prod_cont : ContinuousAt (fun s : ℂ => s * mellin (coshDiff c) s) 0 :=
      h_id_cont.mul h_cont
    have h_val : (0:ℂ) * mellin (coshDiff c) 0 = 0 := by simp
    have h_full : Tendsto (fun s : ℂ => s * mellin (coshDiff c) s)
                    (𝓝 (0:ℂ)) (nhds (0:ℂ)) := by
      have hh := h_prod_cont
      rw [ContinuousAt] at hh
      rw [h_val] at hh
      exact hh
    exact h_full.mono_left nhdsWithin_le_nhds
  have h_sum := h1.add h2
  have hone : (1:ℂ) + (0:ℂ) = 1 := by ring
  rw [hone] at h_sum
  exact h_sum

#print axioms coshGaussMellinExt
#print axioms coshGaussMellinExt_eq_coshGaussMellin
#print axioms coshGaussMellinExt_meromorphic_strip_neg_two
#print axioms coshGaussMellinExt_meromorphic_strip_neg_one
#print axioms coshGaussMellinExt_residue_at_zero

end ZD.CoshGaussMellinContinuation
