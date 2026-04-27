import Mathlib
import RequestProject.GaussianDetectorPair
import RequestProject.GaussianClosedForm

/-!
# Real-analyticity of `gaussianPairDefect`

The Gaussian pair defect
```
gaussianPairDefect β = ∫_{Ioi 0} pairDetectorSqDiff β t · (ψ_gaussian t)^2 dt
```
admits the explicit closed form (Step 1 below)
```
gaussianPairDefect β =
    (1/2) · √(π/2) ·
      ( (1/2) · exp((2β − π/3)² / 8)
        + (1/2) · exp((π/3 + 2β − 2)² / 8)
        − exp((1 − π/3)² / 8)
        − exp((2β − 1)² / 8)
        + 1 ).
```
The right-hand side is a finite sum of `exp` of polynomials in `β`, so it is
real-analytic on all of `ℝ`. We conclude
`AnalyticOnNhd ℝ gaussianPairDefect Set.univ`.

No new axioms, no sorries.
-/

open Real Complex MeasureTheory Set ZetaDefs

noncomputable section

namespace ZD

/-! ### Step 1 — closed form for `gaussianPairDefect`.

We expand
`4 · sinh²((1/2 − π/6)·t) · sinh²((β − 1/2)·t) · exp(−2 t²)`
using `2·sinh²(x) = cosh(2x) − 1` (twice) and the product-to-sum identity
`2·cosh(x)·cosh(y) = cosh(x + y) + cosh(x − y)`. Each resulting term is
either a constant `cosh(c·t) · exp(−2 t²)` (with the four constants
`(2β − π/3), (π/3 + 2β − 2), (1 − π/3), (2β − 1)`) or the bare Gaussian
`exp(−2 t²)`. Each integrates to a closed form via `cosh_gaussian_half`
and `integral_gaussian_Ioi`. -/

theorem gaussianPairDefect_closed_form (β : ℝ) :
    gaussianPairDefect β =
      (1/2) * Real.sqrt (Real.pi / 2) *
        ( (1/2) * Real.exp ((2*β - Real.pi/3)^2 / 8)
          + (1/2) * Real.exp ((Real.pi/3 + 2*β - 2)^2 / 8)
          - Real.exp ((1 - Real.pi/3)^2 / 8)
          - Real.exp ((2*β - 1)^2 / 8)
          + 1 ) := by
  unfold gaussianPairDefect
  -- 1. Replace integrand with the algebraic expansion.
  set α : ℝ := 1 - Real.pi / 3 with hα_def
  set b : ℝ := 2*β - 1 with hb_def
  set u : ℝ := 2*β - Real.pi/3 with hu_def
  set v : ℝ := Real.pi/3 + 2*β - 2 with hv_def
  have h_psi_sq : ∀ t : ℝ, (ψ_gaussian t)^2 = Real.exp (-2 * t^2) := ψ_gaussian_sq_eq
  have h_integrand : ∀ t : ℝ,
      pairDetectorSqDiff β t * (ψ_gaussian t)^2 =
        ( (1/2) * Real.cosh (u * t)
          + (1/2) * Real.cosh (v * t)
          - Real.cosh (α * t)
          - Real.cosh (b * t)
          + 1 ) * Real.exp (-2 * t^2) := by
    intro t
    rw [pairDetectorSqDiff_sinh_factor, h_psi_sq]
    -- 4 · sinh²(A) · sinh²(B) = (cosh(2A) − 1)(cosh(2B) − 1)
    --                        = cosh(2A)·cosh(2B) − cosh(2A) − cosh(2B) + 1
    --                        = (1/2)(cosh(2A+2B) + cosh(2A-2B)) − cosh(2A) − cosh(2B) + 1
    -- with 2A = α·t, 2B = b·t, 2A+2B = u·t, 2A−2B = (α−b)·t = (1 − π/3 − 2β + 1)·t
    --                                        = (2 − π/3 − 2β)·t = −v·t
    -- Real.cosh is even, so cosh(−v·t) = cosh(v·t).
    have hAt : (2 : ℝ) * ((1/2 - Real.pi/6) * t) = α * t := by
      simp [hα_def]; ring
    have hBt : (2 : ℝ) * ((β - 1/2) * t) = b * t := by
      simp [hb_def]; ring
    -- 2·sinh²(x) = cosh(2x) − 1 → sinh²(x) = (cosh(2x) − 1)/2
    have hsinhsq_A : Real.sinh ((1/2 - Real.pi/6) * t)^2 =
        (Real.cosh (α * t) - 1) / 2 := by
      have h := Real.cosh_two_mul ((1/2 - Real.pi/6) * t)
      have hsq := Real.cosh_sq_sub_sinh_sq ((1/2 - Real.pi/6) * t)
      have : Real.cosh (2 * ((1/2 - Real.pi/6) * t)) =
             1 + 2 * Real.sinh ((1/2 - Real.pi/6) * t)^2 := by
        rw [h]; nlinarith [hsq]
      rw [hAt] at this
      linarith
    have hsinhsq_B : Real.sinh ((β - 1/2) * t)^2 =
        (Real.cosh (b * t) - 1) / 2 := by
      have h := Real.cosh_two_mul ((β - 1/2) * t)
      have hsq := Real.cosh_sq_sub_sinh_sq ((β - 1/2) * t)
      have : Real.cosh (2 * ((β - 1/2) * t)) =
             1 + 2 * Real.sinh ((β - 1/2) * t)^2 := by
        rw [h]; nlinarith [hsq]
      rw [hBt] at this
      linarith
    -- product-to-sum: cosh(α·t)·cosh(b·t) = (cosh(u·t) + cosh(v·t))/2
    -- where u = α + b, v = α − b (using cosh evenness for the sign).
    have hu_eq : α + b = u := by
      show (1 - Real.pi / 3) + (2*β - 1) = 2*β - Real.pi/3
      ring
    have hv_eq : α - b = -v := by
      show (1 - Real.pi / 3) - (2*β - 1) = -(Real.pi/3 + 2*β - 2)
      ring
    have hcosh_prod : Real.cosh (α * t) * Real.cosh (b * t) =
        (Real.cosh (u * t) + Real.cosh (v * t)) / 2 := by
      have hadd : Real.cosh (α * t + b * t) =
          Real.cosh (α * t) * Real.cosh (b * t) + Real.sinh (α * t) * Real.sinh (b * t) :=
        Real.cosh_add (α * t) (b * t)
      have hsub : Real.cosh (α * t - b * t) =
          Real.cosh (α * t) * Real.cosh (b * t) - Real.sinh (α * t) * Real.sinh (b * t) :=
        Real.cosh_sub (α * t) (b * t)
      have hsum :
          Real.cosh (α * t + b * t) + Real.cosh (α * t - b * t) =
            2 * (Real.cosh (α * t) * Real.cosh (b * t)) := by linarith
      have hadd' : α * t + b * t = u * t := by
        have : (α + b) * t = u * t := by rw [hu_eq]
        linarith [show α * t + b * t = (α + b) * t from by ring]
      have hsub' : α * t - b * t = -v * t := by
        have : (α - b) * t = -v * t := by rw [hv_eq]
        linarith [show α * t - b * t = (α - b) * t from by ring]
      rw [hadd', hsub', show -v * t = -(v * t) from by ring,
        Real.cosh_neg] at hsum
      linarith
    -- Put it all together.
    have hexpand :
        4 * Real.sinh ((1/2 - Real.pi/6) * t)^2 * Real.sinh ((β - 1/2) * t)^2 =
        (1/2) * Real.cosh (u * t)
          + (1/2) * Real.cosh (v * t)
          - Real.cosh (α * t)
          - Real.cosh (b * t)
          + 1 := by
      rw [hsinhsq_A, hsinhsq_B]
      have : (4 : ℝ) * ((Real.cosh (α * t) - 1) / 2) * ((Real.cosh (b * t) - 1) / 2) =
        Real.cosh (α * t) * Real.cosh (b * t)
          - Real.cosh (α * t) - Real.cosh (b * t) + 1 := by ring
      rw [this, hcosh_prod]; ring
    rw [hexpand]
  -- 2. Integrate term by term using cosh_gaussian_half + integral_gaussian_Ioi.
  simp_rw [h_integrand]
  -- Set up integrability of each piece.
  have hI_u : Integrable (fun t : ℝ => Real.cosh (u * t) * Real.exp (-2 * t^2)) :=
    cosh_exp_neg_two_sq_integrable u
  have hI_v : Integrable (fun t : ℝ => Real.cosh (v * t) * Real.exp (-2 * t^2)) :=
    cosh_exp_neg_two_sq_integrable v
  have hI_a : Integrable (fun t : ℝ => Real.cosh (α * t) * Real.exp (-2 * t^2)) :=
    cosh_exp_neg_two_sq_integrable α
  have hI_b : Integrable (fun t : ℝ => Real.cosh (b * t) * Real.exp (-2 * t^2)) :=
    cosh_exp_neg_two_sq_integrable b
  have hI_g : Integrable (fun t : ℝ => Real.exp (-2 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2)
  -- Split the big integrand into pieces.
  have hsplit : ∀ t : ℝ,
      ((1/2) * Real.cosh (u * t)
        + (1/2) * Real.cosh (v * t)
        - Real.cosh (α * t)
        - Real.cosh (b * t)
        + 1) * Real.exp (-2 * t^2) =
      (1/2) * (Real.cosh (u * t) * Real.exp (-2 * t^2))
        + (1/2) * (Real.cosh (v * t) * Real.exp (-2 * t^2))
        - (Real.cosh (α * t) * Real.exp (-2 * t^2))
        - (Real.cosh (b * t) * Real.exp (-2 * t^2))
        + Real.exp (-2 * t^2) := by
    intro t; ring
  simp_rw [hsplit]
  -- Linearity of integral.
  have hI_uh : Integrable (fun t : ℝ =>
      (1/2) * (Real.cosh (u * t) * Real.exp (-2 * t^2))) := hI_u.const_mul _
  have hI_vh : Integrable (fun t : ℝ =>
      (1/2) * (Real.cosh (v * t) * Real.exp (-2 * t^2))) := hI_v.const_mul _
  have hsum1 : Integrable (fun t : ℝ =>
      (1/2) * (Real.cosh (u * t) * Real.exp (-2 * t^2))
        + (1/2) * (Real.cosh (v * t) * Real.exp (-2 * t^2))) := hI_uh.add hI_vh
  have hsum2 : Integrable (fun t : ℝ =>
      (1/2) * (Real.cosh (u * t) * Real.exp (-2 * t^2))
        + (1/2) * (Real.cosh (v * t) * Real.exp (-2 * t^2))
        - (Real.cosh (α * t) * Real.exp (-2 * t^2))) := hsum1.sub hI_a
  have hsum3 : Integrable (fun t : ℝ =>
      (1/2) * (Real.cosh (u * t) * Real.exp (-2 * t^2))
        + (1/2) * (Real.cosh (v * t) * Real.exp (-2 * t^2))
        - (Real.cosh (α * t) * Real.exp (-2 * t^2))
        - (Real.cosh (b * t) * Real.exp (-2 * t^2))) := hsum2.sub hI_b
  rw [integral_add hsum3.integrableOn hI_g.integrableOn,
      integral_sub hsum2.integrableOn hI_b.integrableOn,
      integral_sub hsum1.integrableOn hI_a.integrableOn,
      integral_add hI_uh.integrableOn hI_vh.integrableOn,
      integral_const_mul, integral_const_mul,
      cosh_gaussian_half u, cosh_gaussian_half v,
      cosh_gaussian_half α, cosh_gaussian_half b,
      integral_gaussian_Ioi 2]
  -- Now everything reduces to algebra; sqrt(π/2) factors out cleanly.
  -- integral_gaussian_Ioi 2 gives `Real.sqrt (Real.pi / 2) / 2`.
  have hsqrt_eq : Real.sqrt (Real.pi / 2) / 2 = (1/2) * Real.sqrt (Real.pi / 2) := by ring
  ring

/-! ### Step 2 — analyticity of the closed-form expression. -/

/-- Real-analyticity of `gaussianPairDefect` on all of `ℝ`. -/
theorem gaussianPairDefect_analyticOnNhd_open :
    AnalyticOnNhd ℝ ZD.gaussianPairDefect Set.univ := by
  -- Rewrite using the closed form, then show the closed form is analytic.
  have h_eq : ZD.gaussianPairDefect = fun β : ℝ =>
      (1/2) * Real.sqrt (Real.pi / 2) *
        ( (1/2) * Real.exp ((2*β - Real.pi/3)^2 / 8)
          + (1/2) * Real.exp ((Real.pi/3 + 2*β - 2)^2 / 8)
          - Real.exp ((1 - Real.pi/3)^2 / 8)
          - Real.exp ((2*β - 1)^2 / 8)
          + 1 ) := by
    funext β; exact gaussianPairDefect_closed_form β
  rw [h_eq]
  -- The right-hand side is a polynomial-in-β combination of exp(poly(β)).
  -- Build it from analyticity of `id`, constants, +, −, ·, ², and `Real.exp`.
  -- The identity function ℝ → ℝ:
  have h_id : AnalyticOnNhd ℝ (fun β : ℝ => β) Set.univ := analyticOnNhd_id
  -- Three β-dependent linear functions.
  have h_lin1 : AnalyticOnNhd ℝ (fun β : ℝ => 2*β - Real.pi/3) Set.univ :=
    ((analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => (2:ℝ)) Set.univ).mul h_id).sub
      analyticOnNhd_const
  have h_lin2 : AnalyticOnNhd ℝ (fun β : ℝ => Real.pi/3 + 2*β - 2) Set.univ :=
    (analyticOnNhd_const.add
      ((analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => (2:ℝ)) Set.univ).mul h_id)).sub
      analyticOnNhd_const
  have h_lin3 : AnalyticOnNhd ℝ (fun β : ℝ => 2*β - 1) Set.univ :=
    ((analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => (2:ℝ)) Set.univ).mul h_id).sub
      analyticOnNhd_const
  -- Their squares divided by 8.
  have h_sq1 : AnalyticOnNhd ℝ (fun β : ℝ => (2*β - Real.pi/3)^2 / 8) Set.univ := by
    have := h_lin1.pow 2
    -- multiply by constant 1/8
    have h_const : AnalyticOnNhd ℝ (fun _ : ℝ => (1/8 : ℝ)) Set.univ := analyticOnNhd_const
    have hprod := h_const.mul this
    -- rewrite as `(·)^2 / 8`
    have hrew : (fun β : ℝ => (2*β - Real.pi/3)^2 / 8) =
        (fun β : ℝ => (1/8) * (2*β - Real.pi/3)^2) := by
      funext β; ring
    rw [hrew]; exact hprod
  have h_sq2 : AnalyticOnNhd ℝ (fun β : ℝ => (Real.pi/3 + 2*β - 2)^2 / 8) Set.univ := by
    have := h_lin2.pow 2
    have h_const : AnalyticOnNhd ℝ (fun _ : ℝ => (1/8 : ℝ)) Set.univ := analyticOnNhd_const
    have hprod := h_const.mul this
    have hrew : (fun β : ℝ => (Real.pi/3 + 2*β - 2)^2 / 8) =
        (fun β : ℝ => (1/8) * (Real.pi/3 + 2*β - 2)^2) := by
      funext β; ring
    rw [hrew]; exact hprod
  have h_sq3 : AnalyticOnNhd ℝ (fun β : ℝ => (2*β - 1)^2 / 8) Set.univ := by
    have := h_lin3.pow 2
    have h_const : AnalyticOnNhd ℝ (fun _ : ℝ => (1/8 : ℝ)) Set.univ := analyticOnNhd_const
    have hprod := h_const.mul this
    have hrew : (fun β : ℝ => (2*β - 1)^2 / 8) =
        (fun β : ℝ => (1/8) * (2*β - 1)^2) := by
      funext β; ring
    rw [hrew]; exact hprod
  -- Apply Real.exp.
  have h_exp1 : AnalyticOnNhd ℝ (fun β : ℝ => Real.exp ((2*β - Real.pi/3)^2 / 8)) Set.univ :=
    h_sq1.rexp
  have h_exp2 : AnalyticOnNhd ℝ
      (fun β : ℝ => Real.exp ((Real.pi/3 + 2*β - 2)^2 / 8)) Set.univ :=
    h_sq2.rexp
  have h_exp3 : AnalyticOnNhd ℝ (fun β : ℝ => Real.exp ((2*β - 1)^2 / 8)) Set.univ :=
    h_sq3.rexp
  -- Combine.
  have h_const_half : AnalyticOnNhd ℝ (fun _ : ℝ => (1/2 : ℝ)) Set.univ := analyticOnNhd_const
  have h_const_one : AnalyticOnNhd ℝ (fun _ : ℝ => (1 : ℝ)) Set.univ := analyticOnNhd_const
  have h_const_const : AnalyticOnNhd ℝ
      (fun _ : ℝ => Real.exp ((1 - Real.pi/3)^2 / 8)) Set.univ := analyticOnNhd_const
  have h_K : AnalyticOnNhd ℝ
      (fun _ : ℝ => (1/2 : ℝ) * Real.sqrt (Real.pi / 2)) Set.univ := analyticOnNhd_const
  have h_inner : AnalyticOnNhd ℝ
      (fun β : ℝ =>
        (1/2) * Real.exp ((2*β - Real.pi/3)^2 / 8)
        + (1/2) * Real.exp ((Real.pi/3 + 2*β - 2)^2 / 8)
        - Real.exp ((1 - Real.pi/3)^2 / 8)
        - Real.exp ((2*β - 1)^2 / 8)
        + 1) Set.univ := by
    exact ((((h_const_half.mul h_exp1).add (h_const_half.mul h_exp2)).sub
      h_const_const).sub h_exp3).add h_const_one
  exact h_K.mul h_inner

end ZD

end
