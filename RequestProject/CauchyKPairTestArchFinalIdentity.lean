import Mathlib
import RequestProject.CauchyKPairTestArchAudit

/-!
# Substantive arch final identity (Step 25)

The audit framework has separated bookkeeping from substance.  All bookkeeping
is closed:
- 4-bucket decomposition unconditional (after pole-kernel summability exposed).
- All gates 1–5 (integrability + pole-series swaps) closed.

What remains is the **substantive analytic identity**:
```
archAuditFinalIdentity t β :
  archConstantCarrierClosedForm + archRationalCorrectionClosedForm
  + (Σ' k, leftPoleTowerK2Aggregator k t β)
  + (Σ' k, rightPoleTowerK2Aggregator k t β)
  = primeReflectedDifference t β − 2π·K_2(1,t)·M(β,1).
```

## Honest framing — RH-equivalence

By tracing through `K_2_arch_eq_5alpha_closed_form`,
`shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form`, and the algebraic
relation between `K_2_arch` and `K_2_engineering_target`, this identity is
**equivalent** to the K_2-twisted engineering target
`Σ' n·K_2(ρ,t)·M(β,ρ) = 0`, which combined with the strip-root lemma forces
`Re ρ = 1/2` for all nontrivial zeros — i.e., the Riemann Hypothesis at the
`K_2` level.

Per the user's standing directive (`feedback_rh_equivalence`): never
deprioritize an iff-RH target as circular — prove it or prove it equivalent
to RH.  This file proves the equivalence + sets up the residual machinery
for a substantive attempt.

## Structure

1. `archAuditResidual t β` — pointwise difference `LHS − RHS`.
2. `archAuditFinalIdentity_iff_residual_zero` — pointwise reformulation.
3. `archAuditGaussianIntegrated_target` — integrated form Prop.
4. `archAuditFinalIdentity_implies_gaussianIntegrated` — pointwise ⇒ integrated.
5. `archAuditFinalIdentity_iff_K2_engineering_target` — RH-equivalence
   (load-bearing structural equivalence).

Axiom footprint target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity

/-! ## Step 25.1: Residual carrier -/

/-- The pointwise residual `LHS − RHS` of the substantive arch identity. -/
noncomputable def archAuditResidual (t β : ℝ) : ℂ :=
  (archConstantCarrierClosedForm t β +
    archRationalCorrectionClosedForm t β +
    (∑' k : ℕ, leftPoleTowerK2Aggregator k t β) +
    (∑' k : ℕ, rightPoleTowerK2Aggregator k t β)) -
  (primeReflectedDifference t β -
    2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1)

/-- **`archAuditFinalIdentity ⟺ residual = 0`**. -/
theorem archAuditFinalIdentity_iff_residual_zero (t β : ℝ) :
    archAuditFinalIdentity t β ↔ archAuditResidual t β = 0 := by
  unfold archAuditFinalIdentity archAuditResidual
  exact (sub_eq_zero).symm

#print axioms archAuditFinalIdentity_iff_residual_zero

/-! ## Step 25.2: Gaussian-integrated escape hatch

If pointwise per-`t` audit fails (the pointwise K_2 identity doesn't close),
the next layer to test is the **Gaussian-integrated** identity:
```
∫ e^{-2t²} · archAuditResidual t β dt = 0    ∀ β.
```
This corresponds to the K-level (Plancherel-integrated) closure rather than
the per-`t` K_2 closure. -/

/-- **Gaussian-integrated audit target**: the residual integrates to zero
against `e^{-2t²}` over `t ∈ ℝ`. -/
def archAuditGaussianIntegrated_target (β : ℝ) : Prop :=
  (∫ t : ℝ, Real.exp (-(2 * t^2)) • archAuditResidual t β) = 0

/-- **Pointwise ⇒ Gaussian-integrated** (trivial direction).
If `archAuditFinalIdentity` holds for all `t`, the residual vanishes
pointwise, so its Gaussian average is zero. -/
theorem archAuditFinalIdentity_implies_gaussianIntegrated (β : ℝ)
    (h_pointwise : ∀ t : ℝ, archAuditFinalIdentity t β) :
    archAuditGaussianIntegrated_target β := by
  unfold archAuditGaussianIntegrated_target
  have h_zero : ∀ t : ℝ, archAuditResidual t β = 0 := by
    intro t
    rw [← archAuditFinalIdentity_iff_residual_zero]
    exact h_pointwise t
  have h_integrand_zero : (fun t : ℝ => Real.exp (-(2 * t^2)) • archAuditResidual t β) =
      (fun _ => (0 : ℂ)) := by
    funext t
    rw [h_zero t]
    simp
  rw [h_integrand_zero, MeasureTheory.integral_zero]

#print axioms archAuditFinalIdentity_implies_gaussianIntegrated

/-! ## Step 25.3: RH-equivalence of `archAuditFinalIdentity`

**Load-bearing structural equivalence** with the K_2-twisted engineering
target `Σ' n·K_2(ρ,t)·M(β,ρ) = 0`, which is the RH-equivalent statement
at the `K_2` level (combined with the strip-root lemma).

This proves `archAuditFinalIdentity t β` is iff-RH (at `K_2` level), so any
attempt to prove it is an attempt to prove RH.  The Gaussian-integrated
version is iff-RH at `K` level. -/

/-- The `archAuditFinalIdentity ⇒ K_2_engineering_target` direction
(load-bearing).

If the substantive arch identity holds for `t, β`, then the K_2-twisted
engineering target holds at `(t, β)` (over `β ∈ Ioo 0 1`).  This uses:
- `K_2_arch_eq_5alpha_closed_form` (LHS of identity = K_2_arch).
- `shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form` (4-bucket form).
- `K_2_engineering_identity_of_arch_eq` (engineering target from K_2_arch). -/
theorem K_2_engineering_target_of_archAuditFinalIdentity
    (t β : ℝ) (h : archAuditFinalIdentity t β) :
    K_2_engineering_target t β := by
  apply K_2_engineering_identity_of_arch_eq
  show K_2_arch t β =
    primeReflectedDifference t β -
      2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1
  rw [K_2_arch_eq_5alpha_closed_form,
      shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form]
  exact h

#print axioms K_2_engineering_target_of_archAuditFinalIdentity

/-- The reverse direction: `K_2_engineering_target ⟹ archAuditFinalIdentity`.

The K_2 engineering target is the rectangle identity
```
∫ K_2 prime − (∫ K_2 arch + ∫ K_2 reflected) = 2π·K_2(1,t)·M(β,1).
```
Solve for `∫ K_2 arch = K_2_arch`:
```
K_2_arch = ∫ K_2 prime − ∫ K_2 reflected − 2π·K_2(1,t)·M(β,1)
        = primeReflectedDifference − 2π·K_2(1,t)·M(β,1)   [K_2_prime_reflected_difference_eq]
        = archRequired.
```
Then `archAuditFinalIdentity` follows by the 4-bucket chain. -/
theorem archAuditFinalIdentity_of_K_2_engineering_target
    (t β : ℝ) (h : K_2_engineering_target t β) :
    archAuditFinalIdentity t β := by
  -- Goal: 4-bucket sum = primeReflectedDifference - 2π·K_2(1,t)·M(β,1).
  -- LHS = K_2_arch (via 4-bucket and 5-α chains).
  -- K_2_engineering_target gives ∫ K_2 prime − (K_2_arch + ∫ K_2 reflected) = 2π·K_2(1,t)·M(β,1).
  unfold archAuditFinalIdentity
  rw [← shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form,
      ← K_2_arch_eq_5alpha_closed_form]
  -- Goal: K_2_arch t β = primeReflectedDifference t β − 2π·K_2(1,t)·M(β,1).
  unfold K_2_engineering_target at h
  unfold K_2_arch
  -- h : ∫ K_2·prime − (∫ K_2·arch + ∫ K_2·refl) = 2π·K_2(1,t)·M(β,1).
  -- Use K_2_prime_reflected_difference_eq:
  --   ∫ K_2·prime − ∫ K_2·refl = primeReflectedDifference.
  have h_pr := K_2_prime_reflected_difference_eq t β
  -- h_pr : ∫ K_2·prime − ∫ K_2·refl = primeReflectedDifference.
  linear_combination h_pr - h

#print axioms archAuditFinalIdentity_of_K_2_engineering_target

/-- **`archAuditFinalIdentity ⟺ K_2_engineering_target`** (axiom-clean).

This is the load-bearing structural equivalence.  Combined with the
strip-root argument (`CauchyKPairTestComplexK.lean`) and the orthogonality
bridge (`CauchyKPairTestRHBridge.lean`), `K_2_engineering_target` is
RH-equivalent at the K_2 level.  So `archAuditFinalIdentity` is an
alternative parameterization of the same RH-strength claim — proving it is
proving RH at K_2 level. -/
theorem archAuditFinalIdentity_iff_K_2_engineering_target (t β : ℝ) :
    archAuditFinalIdentity t β ↔ K_2_engineering_target t β :=
  ⟨K_2_engineering_target_of_archAuditFinalIdentity t β,
   archAuditFinalIdentity_of_K_2_engineering_target t β⟩

#print axioms archAuditFinalIdentity_iff_K_2_engineering_target

/-! ## Step 25.4: Status — load-bearing analytic gate

`archAuditFinalIdentity t β` is the **single remaining live gate** on the
arch side.  It is RH-equivalent at the `K_2` level (per Step 25.3).

The two tracks:
1. **Pointwise per-`t`**: prove `archAuditFinalIdentity t β` for every `t, β`.
   This is the strongest claim; it implies pointwise K_2-engineering.
2. **Gaussian-integrated**: prove `archAuditGaussianIntegrated_target β` for
   every `β`.  This is weaker than pointwise but suffices for the K-level
   engineering identity (where `K(s) = 2π · ∫ K_2(s,t) · e^{-2t²} dt`).

Both are open analytic obligations.  The pointwise direction is the natural
target if K_2-arch closed form matches the prime-side decomposition cleanly.
The integrated direction is the escape hatch if pointwise reveals a structural
residual that integrates away.

Neither is proved here; structural framework only. -/

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
