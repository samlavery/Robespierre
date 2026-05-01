import RequestProject.PairComboResidueAtZero
import RequestProject.RBetaClosedForm

/-!
# Elementary symmetry properties of `R_beta`

This file records three axiom-clean facts about `R_beta` that follow directly
from the cosh integrand and elementary identities.

## Results

* `R_beta_sinh_form` — the `sinh²` form:
  `R_beta β = 2 · ∫ (cosh((1-π/3) x) - 1) · sinh²((β-1/2) x) · exp(-2 x²) / x`.
  Direct from `cosh(2y) - 1 = 2 sinh²(y)` applied to `y = (β-1/2)x`.

* `R_beta_reflection` — `β ↔ 1-β` symmetry: `R_beta (1 - β) = R_beta β`.
  Immediate from the `sinh²` form (sinh² is invariant under `y ↦ -y`),
  but proved here directly via `cosh_neg` to avoid depending on the
  `sinh²` form.

* `R_beta_at_half` — `R_beta (1/2) = 0`. Immediate: `(2·(1/2) - 1) = 0`
  makes the `cosh - 1` factor vanish identically.

* `deriv_R_beta_at_half` — `(R_beta)'(1/2) = 0`. Differentiating the
  reflection identity at the FE-fixed point.

## Mathematical significance

The reflection identity says that `R_beta` is a function of `(2β-1)²`, hence
real-analytic in `(β-1/2)²` on all of `ℝ`. Combined with the existing
`R_beta_analyticOnNhd` (`RBetaClosedForm.lean`), this strengthens the local
Taylor structure: the Taylor series of `R_beta` at `β = 1/2` contains only
even powers of `(β - 1/2)`. The first-derivative vanishing
`deriv_R_beta_at_half` is the simplest concrete consequence.

The vanishing at `β = 1/2` is consistent with — and a necessary condition
for — the conjectural identity
`R(β) = Σ_ρ n(ρ) · pairTestMellin β ρ + Σ_n Λ(n)/n · pcgt β (1/n)`
(see `RBetaIdentity.H3_iff_R_beta_eq_zeroSum_under_rectCauchy`).
At `β = 1/2`, the right-hand sum must therefore also vanish — a non-trivial
prediction about the explicit-formula spectral side at the FE-fixed point.

All proofs axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Set Real

namespace ZD.PairComboResidueAtZero

/-! ## `sinh²` form of `R_beta` -/

/-- **`R_beta` in the manifestly `(β-1/2)`-symmetric `sinh²` form.**

```
R_beta β = 2 · ∫_{Ioi 0} (cosh((1-π/3)·x) - 1) · sinh²((β - 1/2)·x)
                          · exp(-2 x²) / x dx.
```

This rewrites the original `(cosh((2β-1)x) - 1)` factor using the half-angle
identity `cosh(2y) - 1 = 2 sinh²(y)` with `y = (β - 1/2) x`. -/
theorem R_beta_sinh_form (β : ℝ) :
    R_beta β = 2 * ∫ x in Set.Ioi (0 : ℝ),
      (Real.cosh ((1 - Real.pi / 3) * x) - 1) *
      (Real.sinh ((β - 1 / 2) * x)) ^ 2 *
      Real.exp (-2 * x ^ 2) / x := by
  unfold R_beta
  rw [← integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _
  show (Real.cosh ((1 - Real.pi / 3) * x) - 1) *
        (Real.cosh ((2 * β - 1) * x) - 1) * Real.exp (-2 * x ^ 2) / x =
       2 * ((Real.cosh ((1 - Real.pi / 3) * x) - 1) *
        (Real.sinh ((β - 1 / 2) * x)) ^ 2 * Real.exp (-2 * x ^ 2) / x)
  have h2y : (2 * β - 1) * x = 2 * ((β - 1 / 2) * x) := by ring
  rw [h2y, Real.cosh_two_mul]
  have hcs : Real.cosh ((β - 1 / 2) * x) ^ 2 - Real.sinh ((β - 1 / 2) * x) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq _
  have hkey : Real.cosh ((β - 1 / 2) * x) ^ 2 + Real.sinh ((β - 1 / 2) * x) ^ 2 - 1 =
              2 * (Real.sinh ((β - 1 / 2) * x)) ^ 2 := by linarith
  rw [hkey]; ring

/-! ## `β ↔ 1-β` reflection symmetry -/

/-- **`R_beta` is invariant under `β ↦ 1 - β`.**

`(2(1-β) - 1)·x = -((2β-1)·x)` and `cosh` is even, so the integrand is
pointwise unchanged. -/
theorem R_beta_reflection (β : ℝ) : R_beta (1 - β) = R_beta β := by
  unfold R_beta
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _
  show (Real.cosh ((1 - Real.pi / 3) * x) - 1) *
         (Real.cosh ((2 * (1 - β) - 1) * x) - 1) * Real.exp (-2 * x ^ 2) / x =
       (Real.cosh ((1 - Real.pi / 3) * x) - 1) *
         (Real.cosh ((2 * β - 1) * x) - 1) * Real.exp (-2 * x ^ 2) / x
  have h : (2 * (1 - β) - 1) * x = -((2 * β - 1) * x) := by ring
  rw [h, Real.cosh_neg]

/-! ## Vanishing at the FE-fixed point `β = 1/2` -/

/-- **`R_beta` vanishes at `β = 1/2`.**

At `β = 1/2`, `(2β - 1) = 0`, so `cosh((2β-1)·x) - 1 = cosh(0) - 1 = 0`
makes the integrand identically zero. -/
theorem R_beta_at_half : R_beta (1 / 2) = 0 := by
  unfold R_beta
  have h_int : ∀ x ∈ Ioi (0 : ℝ),
      (Real.cosh ((1 - Real.pi / 3) * x) - 1) *
      (Real.cosh ((2 * (1 / 2) - 1) * x) - 1) *
      Real.exp (-2 * x ^ 2) / x = 0 := by
    intro x _
    have h0 : (2 * (1 / 2 : ℝ) - 1) * x = 0 := by ring
    rw [h0, Real.cosh_zero]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_int]
  simp

/-! ## First-derivative vanishing at `β = 1/2` -/

/-- **`R_beta` has a critical point at `β = 1/2`.**

The reflection symmetry `R_beta (1 - β) = R_beta β` plus the proved
real-analyticity `R_beta_analyticOnNhd` (hence differentiability) of
`R_beta` together force `(R_beta)'(1/2) = 0`: differentiating the
symmetry identity at `β = 1/2` gives `(R_beta)'(1/2) = -(R_beta)'(1/2)`. -/
theorem deriv_R_beta_at_half : deriv R_beta (1 / 2) = 0 := by
  have h_anal := R_beta_analyticOnNhd
  have h_diff : Differentiable ℝ R_beta := fun x =>
    ((h_anal x (Set.mem_univ x)).differentiableAt)
  have h_g : deriv (fun x => R_beta (1 - x)) (1 / 2) = deriv R_beta (1 / 2) := by
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.Eventually.of_forall (fun x => R_beta_reflection x)
  have h_chain : deriv (fun x => R_beta (1 - x)) (1 / 2) =
      -deriv R_beta (1 - 1 / 2) := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) (1 / 2) := by
      simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
    have h2 : HasDerivAt R_beta (deriv R_beta (1 - 1 / 2)) (1 - 1 / 2) :=
      (h_diff (1 - 1 / 2)).hasDerivAt
    have hcomp : HasDerivAt (fun x => R_beta (1 - x))
        (deriv R_beta (1 - 1 / 2) * -1) (1 / 2) := h2.comp _ h1
    rw [hcomp.deriv]; ring
  rw [h_g] at h_chain
  have hh1 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hh1] at h_chain
  linarith

end ZD.PairComboResidueAtZero

end

/-! ## Axiom checks -/

#print axioms ZD.PairComboResidueAtZero.R_beta_sinh_form
#print axioms ZD.PairComboResidueAtZero.R_beta_reflection
#print axioms ZD.PairComboResidueAtZero.R_beta_at_half
#print axioms ZD.PairComboResidueAtZero.deriv_R_beta_at_half
