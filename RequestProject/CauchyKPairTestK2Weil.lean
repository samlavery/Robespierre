import Mathlib
import RequestProject.CauchyKPairTestPlancherel
import RequestProject.CauchyKPairTestLimit

/-!
# Per-t K₂-twisted Weil identity (conditional)

For each fixed `t : ℝ`, applies the conditional chunk-2 T → ∞ theorem at
`K = K_2_fn t` (the partially-applied cosh-pair kernel from the
Plancherel form).  Result:

```
∫_ℝ K_2(2+iy, t)·w(M)(2+iy) dy − ∫_ℝ K_2(-1+iy, t)·w(M)(-1+iy) dy
  = 2π · (K_2(1, t)·M(β, 1) − Σ' n(ρ)·K_2(ρ, t)·M(β, ρ))
```

The 4 chunk-2 targets are taken as hypotheses; their unconditional
discharge for `K_2(·, t)` is structurally identical to the discharge
for `gaussianDefectEntireKernel_local` (uniform `cosh(|σ-1/2|·|t|)`
bound on `‖K_2(σ+iy, t)‖` for `σ ∈ [-1, 2]`).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch

/-- `K_2(·, t)` as a function `ℂ → ℂ`. -/
noncomputable def K_2_fn (t : ℝ) : ℂ → ℂ := fun s => K_2 s t

/-- `K_2(·, t)` is differentiable on all of `ℂ`. -/
theorem K_2_fn_differentiable (t : ℝ) :
    Differentiable ℂ (K_2_fn t) := by
  unfold K_2_fn K_2
  have hL : Differentiable ℂ (fun s : ℂ => 2 * (s - 1/2) * (t : ℂ)) := by
    fun_prop
  have hM : Differentiable ℂ (fun s : ℂ => (s - 1/2) * (t : ℂ)) := by
    fun_prop
  exact (hL.ccosh.sub ((differentiable_const _).mul hM.ccosh)).add (differentiable_const _)

/-- **Per-t K₂-twisted Weil identity at finite T → ∞ (conditional).**

For each `t : ℝ`, `β ∈ Ioo 0 1`, and `Z_at` describing the in-rectangle
nontrivial zeros, the chunk-2 conditional theorem applied at
`K = K_2_fn t` gives the K_2-twisted whole-line Weil identity, conditional
on the 4 chunk-2 targets at `K_2_fn t`.

This is exactly the conditional chunk-2 theorem
`rectContourIntegral_K_pairTestMellin_T_limit` specialized to `K_2_fn t`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_K2_pairTestMellin_T_limit
    (t : ℝ) (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (n : ℂ → ℕ) (Z_at : ℝ → Finset ℂ)
    (hZ_mem : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ ∈ Z_at T,
      ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ : ℂ,
      ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z_at T)
    (h_horiz : K_pairTestMellin_horizontal_vanishes_target (K_2_fn t) β)
    (h_int_pos : K_pairTestMellin_vertical_at_two_integrable (K_2_fn t) β)
    (h_int_neg : K_pairTestMellin_vertical_at_neg_one_integrable (K_2_fn t) β)
    (h_res_tendsto : K_pairTestMellin_residue_sum_tendsto (K_2_fn t) β n Z_at) :
    (∫ y : ℝ, K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y : ℝ, K_2_fn t (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
    2 * ((Real.pi : ℝ) : ℂ) *
      (K_2_fn t 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((n ρ.val : ℕ) : ℂ) * K_2_fn t ρ.val * Contour.pairTestMellin β ρ.val) :=
  rectContourIntegral_K_pairTestMellin_T_limit
    (K_2_fn t) (K_2_fn_differentiable t) β hβ n Z_at hZ_mem hZ_complete
    h_horiz h_int_pos h_int_neg h_res_tendsto

#print axioms rectContourIntegral_K2_pairTestMellin_T_limit

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
