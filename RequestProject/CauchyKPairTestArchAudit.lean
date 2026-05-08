import Mathlib
import RequestProject.CauchyKPairTestEngineering
import RequestProject.CauchyKPairTestPoleSwap

/-!
# Arch audit (Step 17): `5-α sum of shiftedArchClosedForm = archRequired`

With all five analytic gates closed (three integrability + two pole swaps),
the arch side is unconditional:
```
shiftedArchIntegral β α = shiftedArchClosedForm β α     (unconditional)
```
where
```
shiftedArchClosedForm β α =
  -(log π + γ) · constantLogPiShiftedArchIntegral β α
  + (∑' k, digammaPoleKernelLeft k β α)
  + (∑' k, digammaPoleKernelRight k β α)
  + digammaRationalCorrectionIntegral β α.
```

This file performs the **`archRequired` audit**: the per-`t` 5-α-component
combination of `shiftedArchClosedForm β α` must equal `archRequired t β`.

```
(1/2)·e^{-3t}·shiftedArchClosedForm(β, 2t)
+ (1/2)·e^{3t}·shiftedArchClosedForm(β, -2t)
- e^{-(3/2)t}·shiftedArchClosedForm(β, t)
- e^{(3/2)t}·shiftedArchClosedForm(β, -t)
+ shiftedArchClosedForm(β, 0)
= archRequired t β.
```

## Audit by components (per user's plan)

The LHS expands by additivity into four component sums:

1. **Constant carrier**: `-(log π + γ) · [Σ_α c_α(t) · constantLogPi(β, α)]`.
2. **Left pole tower**: `Σ_α c_α(t) · Σ_k digammaPoleKernelLeft(k, β, α)`.
3. **Right pole tower**: `Σ_α c_α(t) · Σ_k digammaPoleKernelRight(k, β, α)`.
4. **Rational correction**: `Σ_α c_α(t) · digammaRationalCorrectionIntegral(β, α)`.

Each must combine into the matching component of `archRequired t β`.

If pointwise (per-`t`) audit closes, the K_2 engineering target holds
pointwise.  If only the Gaussian-integrated K-level closure works, switch
to that downstream.  This file commits to the **pointwise** target first.

## Naming for component pieces

```
shiftedArchClosedForm_5alpha_sum     — the LHS combination
archConstantCarrier5sum (t β)        — component 1 LHS at the 5 α-values
archLeftPoleTower5sum (t β)          — component 2 LHS
archRightPoleTower5sum (t β)         — component 3 LHS
archRationalCorrection5sum (t β)     — component 4 LHS
```

Axiom footprint target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity

/-! ## Step 17: Define the 5-α-component LHS sum

The 5-α-component `c_α(t)` Fourier coefficients used by
`K_2_arch_eq_five_shifted` (read from `K_2_archIntegrand_re_neg_one_eq`):
- α = 2t  : (1/2)·e^{-3t}
- α = -2t : (1/2)·e^{3t}
- α = t   : -e^{-(3/2)t}
- α = -t  : -e^{(3/2)t}
- α = 0   : 1. -/

/-- LHS combination: 5-α sum of `shiftedArchClosedForm β α` weighted by
the K_2 Fourier coefficients at `Re s = -1`. -/
noncomputable def shiftedArchClosedForm_5alpha_sum (t β : ℝ) : ℂ :=
  (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      shiftedArchClosedForm β (2 * t) +
  (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      shiftedArchClosedForm β (-(2 * t)) -
  Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      shiftedArchClosedForm β t -
  Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      shiftedArchClosedForm β (-t) +
  shiftedArchClosedForm β 0

/-- **5-α LHS = K_2 left-edge arch integral** (immediate from
`shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional` and
`K_2_arch_eq_five_shifted`). -/
theorem K_2_arch_eq_5alpha_closed_form (t β : ℝ) :
    K_2_arch t β = shiftedArchClosedForm_5alpha_sum t β := by
  rw [K_2_arch_eq_five_shifted]
  unfold shiftedArchClosedForm_5alpha_sum
  rw [shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional β (2 * t),
      shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional β (-(2 * t)),
      shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional β t,
      shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional β (-t),
      shiftedArchIntegral_eq_shiftedArchClosedForm_unconditional β 0]

#print axioms K_2_arch_eq_5alpha_closed_form

/-! ## Step 18: Audit target — `5-α LHS = archRequired`

This is the LOAD-BEARING audit comparison.  It has NOT yet been derived
mechanically; per the user's directive it must be done component-by-component
(constant carrier, rational correction, two pole towers) before being
asserted.

Per user's escape hatch: "If the only clean cancellation appears after
Gaussian e^{-2t²}-integration, switch to the integrated K-level closure
rather than fighting the wrong theorem." -/

/-- **Audit target** — pointwise per-`t`, the 5-α LHS combination matches
`archRequired t β`.  This is the comparison theorem the audit must close. -/
def shiftedArchClosedForm_5alpha_eq_archRequired_target (t β : ℝ) : Prop :=
  shiftedArchClosedForm_5alpha_sum t β =
    primeReflectedDifference t β -
      2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1

/-- Once the audit target holds, the K_2 engineering identity follows. -/
theorem K_2_engineering_identity_of_shifted_arch_closed_form_audit
    (t β : ℝ)
    (h_audit : shiftedArchClosedForm_5alpha_eq_archRequired_target t β) :
    K_2_engineering_target t β := by
  apply K_2_engineering_identity_of_arch_eq
  show K_2_arch t β =
    primeReflectedDifference t β -
      2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1
  rw [K_2_arch_eq_5alpha_closed_form]
  exact h_audit

#print axioms K_2_engineering_identity_of_shifted_arch_closed_form_audit

/-! ## Step 19: Component decomposition of the LHS

Expand `shiftedArchClosedForm β α` in the 5-α sum and group by the four
mechanism components: constant carrier, left pole tower, right pole tower,
rational correction. -/

/-- **Component 1 LHS**: the constant `-(log π + γ)·constantLogPi` carrier
combined across the 5 α-values. -/
noncomputable def archConstantCarrier5sum (t β : ℝ) : ℂ :=
  -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        constantLogPiShiftedArchIntegral β (2 * t) +
     (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        constantLogPiShiftedArchIntegral β (-(2 * t)) -
     Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
        constantLogPiShiftedArchIntegral β t -
     Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        constantLogPiShiftedArchIntegral β (-t) +
     constantLogPiShiftedArchIntegral β 0)

/-- **Component 2 LHS**: the left pole-tower combined across the 5 α-values
(per-`k` aggregator). -/
noncomputable def archLeftPoleTower5sum (t β : ℝ) : ℂ :=
  ∑' k : ℕ,
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        digammaPoleKernelLeft k β (2 * t) +
     (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        digammaPoleKernelLeft k β (-(2 * t)) -
     Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
        digammaPoleKernelLeft k β t -
     Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        digammaPoleKernelLeft k β (-t) +
     digammaPoleKernelLeft k β 0)

/-- **Component 3 LHS**: the right pole-tower combined across the 5 α-values. -/
noncomputable def archRightPoleTower5sum (t β : ℝ) : ℂ :=
  ∑' k : ℕ,
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        digammaPoleKernelRight k β (2 * t) +
     (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        digammaPoleKernelRight k β (-(2 * t)) -
     Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
        digammaPoleKernelRight k β t -
     Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        digammaPoleKernelRight k β (-t) +
     digammaPoleKernelRight k β 0)

/-- **Component 4 LHS**: the rational-correction combined across the 5 α-values. -/
noncomputable def archRationalCorrection5sum (t β : ℝ) : ℂ :=
  (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      digammaRationalCorrectionIntegral β (2 * t) +
  (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      digammaRationalCorrectionIntegral β (-(2 * t)) -
  Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      digammaRationalCorrectionIntegral β t -
  Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      digammaRationalCorrectionIntegral β (-t) +
  digammaRationalCorrectionIntegral β 0

/-- **Component decomposition** (conditional on tower swap of Σ_α and Σ_k):
the 5-α LHS sum equals the four-component combination. -/
def shiftedArchClosedForm_5alpha_sum_4component_target (t β : ℝ) : Prop :=
  shiftedArchClosedForm_5alpha_sum t β =
    archConstantCarrier5sum t β +
    archLeftPoleTower5sum t β +
    archRightPoleTower5sum t β +
    archRationalCorrection5sum t β

/-! ## Step 20: Audit subtargets per component

Per user's directive, audit **by components**:
1. constant carrier `archConstantCarrier5sum t β = ?`
2. rational correction `archRationalCorrection5sum t β = ?`
3. left pole tower `archLeftPoleTower5sum t β = ?`
4. right pole tower `archRightPoleTower5sum t β = ?`

Each `?` is a piece of `archRequired t β` (`primeReflectedDifference -
2π · K_2(1,t) · M(β,1)`) the corresponding component must produce.

Do **not** assert the per-component targets without explicit derivation.
This file leaves them as Props to be discharged by direct computation in
follow-up steps. -/

/-- The **constant carrier audit subtarget**.  Asserts that the constant
carrier sum produces a specific named piece of `archRequired t β`. -/
def archConstantCarrier5sum_audit_target (t β : ℝ) (P_const : ℂ) : Prop :=
  archConstantCarrier5sum t β = P_const

/-- The **rational correction audit subtarget**. -/
def archRationalCorrection5sum_audit_target (t β : ℝ) (P_rat : ℂ) : Prop :=
  archRationalCorrection5sum t β = P_rat

/-- The **left pole tower audit subtarget**. -/
def archLeftPoleTower5sum_audit_target (t β : ℝ) (P_left : ℂ) : Prop :=
  archLeftPoleTower5sum t β = P_left

/-- The **right pole tower audit subtarget**. -/
def archRightPoleTower5sum_audit_target (t β : ℝ) (P_right : ℂ) : Prop :=
  archRightPoleTower5sum t β = P_right

/-- **Audit assembly** (conditional): combine the four component subtargets
plus the additive decomposition target to derive the audit. -/
theorem shiftedArchClosedForm_5alpha_eq_archRequired_of_components
    (t β : ℝ)
    (P_const P_rat P_left P_right : ℂ)
    (h_decomp : shiftedArchClosedForm_5alpha_sum_4component_target t β)
    (h_const : archConstantCarrier5sum_audit_target t β P_const)
    (h_rat : archRationalCorrection5sum_audit_target t β P_rat)
    (h_left : archLeftPoleTower5sum_audit_target t β P_left)
    (h_right : archRightPoleTower5sum_audit_target t β P_right)
    (h_combine : P_const + P_left + P_right + P_rat =
      primeReflectedDifference t β -
        2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1) :
    shiftedArchClosedForm_5alpha_eq_archRequired_target t β := by
  unfold shiftedArchClosedForm_5alpha_eq_archRequired_target
  unfold shiftedArchClosedForm_5alpha_sum_4component_target at h_decomp
  unfold archConstantCarrier5sum_audit_target at h_const
  unfold archRationalCorrection5sum_audit_target at h_rat
  unfold archLeftPoleTower5sum_audit_target at h_left
  unfold archRightPoleTower5sum_audit_target at h_right
  rw [h_decomp, h_const, h_rat, h_left, h_right]
  linear_combination h_combine

#print axioms shiftedArchClosedForm_5alpha_eq_archRequired_of_components

/-! ## Step 21: Constant carrier audit — closed-form derivation

By `constantLogPiShiftedArchIntegral_eq`, each `constantLogPi(β, α)` equals
`2π · e^α · test_β(e^{-α})`, so the 5-α-component constant carrier reduces to
a finite, k-free, residue-free explicit expression:

```
archConstantCarrier5sum(t, β)
  = -(log π + γ) · 2π · [
      (1/2)·e^{-t}·test_β(e^{-2t})
      + (1/2)·e^{t}·test_β(e^{2t})
      - e^{-t/2}·test_β(e^{-t})
      - e^{t/2}·test_β(e^{t})
      + test_β(1)
    ].
```

Per the user's audit-first directive, this is computed before any pole-tower
work to expose `log π + γ` sign errors / `2π` convention mismatches early. -/

/-- Closed-form value of the constant-carrier 5-α sum.  Form matches the
direct substitution of `constantLogPiShiftedArchIntegral_eq` into each of the
five `α`-instantiated terms — outer prefactors stay as `Complex.exp` of real
linear combinations, inner `pair_cosh_gauss_test` arguments are `Real.exp`. -/
noncomputable def archConstantCarrierClosedForm (t β : ℝ) : ℂ :=
  -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          ((Real.exp (2 * t) : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-(2 * t))) : ℝ) : ℂ)) +
     (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)) -
     Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          ((Real.exp t : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-t)) : ℝ) : ℂ)) -
     Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          ((Real.exp (-t) : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (Real.exp (-(-t))) : ℝ) : ℂ)) +
     ((2 * Real.pi : ℝ) : ℂ) *
       ((Real.exp 0 : ℝ) : ℂ) *
       ((pair_cosh_gauss_test β (Real.exp (-0)) : ℝ) : ℂ))

/-- **Constant carrier closed-form** (axiom-clean):
`archConstantCarrier5sum t β = archConstantCarrierClosedForm t β`.

Pure substitution + algebra — no analytic content. -/
theorem archConstantCarrier5sum_closed_form (t β : ℝ) :
    archConstantCarrier5sum t β = archConstantCarrierClosedForm t β := by
  unfold archConstantCarrier5sum archConstantCarrierClosedForm
  rw [constantLogPiShiftedArchIntegral_eq, constantLogPiShiftedArchIntegral_eq,
      constantLogPiShiftedArchIntegral_eq, constantLogPiShiftedArchIntegral_eq,
      constantLogPiShiftedArchIntegral_eq]

#print axioms archConstantCarrier5sum_closed_form

/-- **Constant carrier audit subtarget holds** at the closed form value. -/
theorem archConstantCarrier5sum_audit_target_holds (t β : ℝ) :
    archConstantCarrier5sum_audit_target t β
      (archConstantCarrierClosedForm t β) := by
  exact archConstantCarrier5sum_closed_form t β

#print axioms archConstantCarrier5sum_audit_target_holds

/-! ## Step 22: Rational correction audit — closed-form derivation

`archRationalCorrection5sum t β` is finite in α (5 terms, no `k`-sum).
Mirror Step 21: substitute the definition of `digammaRationalCorrectionIntegral`
into each of the five `α`-instantiated terms, exposing the explicit
five-integral closed form.

The sign convention: `digammaRationalCorrectionIntegral β α := −∫ exp(iyα)·
(1/(−1+iy))·M(β,−1+iy) dy` (a leading minus, NOT `+1/(−1+iy)`).  The closed
form preserves this sign through each of the five `α`-instantiated integrals.

Per user's audit-first directive: keep separate from pole towers; this term
is the likely cancellation partner for a `k=0`-style residue and must not
be folded into either tower. -/

/-- Closed-form value of the rational-correction 5-α sum.  Form matches the
unfolded `archRationalCorrection5sum` directly — `digammaRationalCorrectionIntegral`
defs substituted into each of the five `α`-instantiated terms with the
leading minus on each integral preserved exactly. -/
noncomputable def archRationalCorrectionClosedForm (t β : ℝ) : ℂ :=
  (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (2 * t) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
  (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (-(2 * t)) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
  Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) -
  Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) +
  (-∫ y : ℝ, Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))

/-- **Rational correction closed-form** (axiom-clean):
`archRationalCorrection5sum t β = archRationalCorrectionClosedForm t β`.

Pure definitional unfolding (`rfl` — the closed form matches the unfolded
form literally). -/
theorem archRationalCorrection5sum_closed_form (t β : ℝ) :
    archRationalCorrection5sum t β = archRationalCorrectionClosedForm t β := by
  rfl

#print axioms archRationalCorrection5sum_closed_form

/-- **Rational correction audit subtarget holds** at the closed form value. -/
theorem archRationalCorrection5sum_audit_target_holds (t β : ℝ) :
    archRationalCorrection5sum_audit_target t β
      (archRationalCorrectionClosedForm t β) := by
  exact archRationalCorrection5sum_closed_form t β

#print axioms archRationalCorrection5sum_audit_target_holds

/-! ## Step 23: Pole tower per-`k` aggregators

Per the user's directive, attack pole towers via **per-`k` aggregation**:
isolate the inner 5-α-component combination at each fixed `k`, so
`archLeftPoleTower5sum t β = Σ' k, leftPoleTowerK2Aggregator k t β`.

This makes per-`k` comparison against the trivial-zero residue tower tractable.
The two towers stay distinct (left denominators `k + 1/2 + iy/2`, right
`k + 1 - iy/2`) — no merging here. -/

/-- **Left pole tower per-`k` aggregator**: the inner 5-α-component combination
at fixed `k` for the left pole tower. -/
noncomputable def leftPoleTowerK2Aggregator (k : ℕ) (t β : ℝ) : ℂ :=
  (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      digammaPoleKernelLeft k β (2 * t) +
  (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      digammaPoleKernelLeft k β (-(2 * t)) -
  Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      digammaPoleKernelLeft k β t -
  Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      digammaPoleKernelLeft k β (-t) +
  digammaPoleKernelLeft k β 0

/-- **Right pole tower per-`k` aggregator**. -/
noncomputable def rightPoleTowerK2Aggregator (k : ℕ) (t β : ℝ) : ℂ :=
  (1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      digammaPoleKernelRight k β (2 * t) +
  (1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      digammaPoleKernelRight k β (-(2 * t)) -
  Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      digammaPoleKernelRight k β t -
  Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      digammaPoleKernelRight k β (-t) +
  digammaPoleKernelRight k β 0

/-- **Left pole tower 5-α sum equals `∑' k` aggregator**.  By definition. -/
theorem archLeftPoleTower5sum_eq_aggregator_sum (t β : ℝ) :
    archLeftPoleTower5sum t β = ∑' k : ℕ, leftPoleTowerK2Aggregator k t β := by
  rfl

#print axioms archLeftPoleTower5sum_eq_aggregator_sum

/-- **Right pole tower 5-α sum equals `∑' k` aggregator**.  By definition. -/
theorem archRightPoleTower5sum_eq_aggregator_sum (t β : ℝ) :
    archRightPoleTower5sum t β = ∑' k : ℕ, rightPoleTowerK2Aggregator k t β := by
  rfl

#print axioms archRightPoleTower5sum_eq_aggregator_sum

/-- **Left pole tower audit subtarget holds** at the aggregator form. -/
theorem archLeftPoleTower5sum_audit_target_holds (t β : ℝ) :
    archLeftPoleTower5sum_audit_target t β
      (∑' k : ℕ, leftPoleTowerK2Aggregator k t β) :=
  archLeftPoleTower5sum_eq_aggregator_sum t β

#print axioms archLeftPoleTower5sum_audit_target_holds

/-- **Right pole tower audit subtarget holds** at the aggregator form. -/
theorem archRightPoleTower5sum_audit_target_holds (t β : ℝ) :
    archRightPoleTower5sum_audit_target t β
      (∑' k : ℕ, rightPoleTowerK2Aggregator k t β) :=
  archRightPoleTower5sum_eq_aggregator_sum t β

#print axioms archRightPoleTower5sum_audit_target_holds

/-! ## Step 24: 4-bucket decomposition (bookkeeping correctness)

Per user's directive: prove that the 5-α LHS sum equals the four-bucket
combination.  This is **bookkeeping** correctness — separating it from the
substantive mathematical identity keeps any later residual unambiguously
analytic, not Lean-syntactic.

The required pole-kernel summabilities
- `∀ α, Summable (fun k => digammaPoleKernelLeft k β α)`
- `∀ α, Summable (fun k => digammaPoleKernelRight k β α)`
are now public theorems (`summable_digammaPoleKernelLeft` /
`summable_digammaPoleKernelRight` in `CauchyKPairTestPoleSwap.lean`),
extracted from the L¹-summable control inside the pole-swap proof.  As a
result, all theorems below are **unconditional**. -/

/-- Summability of the **left pole tower per-`k` aggregator** at fixed `t, β`.
Unconditional: combines the public per-α summability of the left pole
kernel with finite linearity. -/
theorem summable_leftPoleTowerK2Aggregator (t β : ℝ) :
    Summable (fun k : ℕ => leftPoleTowerK2Aggregator k t β) := by
  unfold leftPoleTowerK2Aggregator
  refine Summable.add ?_ ?_
  refine Summable.sub ?_ ?_
  refine Summable.sub ?_ ?_
  refine Summable.add ?_ ?_
  · exact (summable_digammaPoleKernelLeft β (2 * t)).mul_left _
  · exact (summable_digammaPoleKernelLeft β (-(2 * t))).mul_left _
  · exact (summable_digammaPoleKernelLeft β t).mul_left _
  · exact (summable_digammaPoleKernelLeft β (-t)).mul_left _
  · exact summable_digammaPoleKernelLeft β 0

#print axioms summable_leftPoleTowerK2Aggregator

/-- Summability of the **right pole tower per-`k` aggregator**.
Unconditional. -/
theorem summable_rightPoleTowerK2Aggregator (t β : ℝ) :
    Summable (fun k : ℕ => rightPoleTowerK2Aggregator k t β) := by
  unfold rightPoleTowerK2Aggregator
  refine Summable.add ?_ ?_
  refine Summable.sub ?_ ?_
  refine Summable.sub ?_ ?_
  refine Summable.add ?_ ?_
  · exact (summable_digammaPoleKernelRight β (2 * t)).mul_left _
  · exact (summable_digammaPoleKernelRight β (-(2 * t))).mul_left _
  · exact (summable_digammaPoleKernelRight β t).mul_left _
  · exact (summable_digammaPoleKernelRight β (-t)).mul_left _
  · exact summable_digammaPoleKernelRight β 0

#print axioms summable_rightPoleTowerK2Aggregator

/-- **4-bucket closed-form decomposition** (axiom-clean, **unconditional**):
```
shiftedArchClosedForm_5alpha_sum t β =
  archConstantCarrierClosedForm t β +
  archRationalCorrectionClosedForm t β +
  (∑' k, leftPoleTowerK2Aggregator k t β) +
  (∑' k, rightPoleTowerK2Aggregator k t β).
```
This is the bookkeeping correctness theorem — pure linearity of `tsum`
through finite linear combinations, no analytic content. -/
theorem shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form (t β : ℝ) :
    shiftedArchClosedForm_5alpha_sum t β =
      archConstantCarrierClosedForm t β +
      archRationalCorrectionClosedForm t β +
      (∑' k : ℕ, leftPoleTowerK2Aggregator k t β) +
      (∑' k : ℕ, rightPoleTowerK2Aggregator k t β) := by
  -- Extract per-α summability from the public pole-kernel summability lemmas.
  have h_summL : ∀ α : ℝ, Summable (fun k : ℕ => digammaPoleKernelLeft k β α) :=
    fun α => summable_digammaPoleKernelLeft β α
  have h_summR : ∀ α : ℝ, Summable (fun k : ℕ => digammaPoleKernelRight k β α) :=
    fun α => summable_digammaPoleKernelRight β α
  -- Strategy: rewrite RHS via the per-bucket equalities back to the
  -- 4-component decomposition target (in terms of `archConstantCarrier5sum`
  -- etc.), then expand each `shiftedArchClosedForm β α` and redistribute
  -- the `tsum`s via `tsum_mul_left` and `tsum_add`/`tsum_sub`.
  rw [← archConstantCarrier5sum_closed_form,
      ← archRationalCorrection5sum_closed_form,
      ← archLeftPoleTower5sum_eq_aggregator_sum,
      ← archRightPoleTower5sum_eq_aggregator_sum]
  -- Goal: shiftedArchClosedForm_5alpha_sum t β =
  --       archConstantCarrier5sum t β + archRationalCorrection5sum t β +
  --       archLeftPoleTower5sum t β + archRightPoleTower5sum t β.
  unfold shiftedArchClosedForm_5alpha_sum shiftedArchClosedForm
    archConstantCarrier5sum archLeftPoleTower5sum archRightPoleTower5sum
    archRationalCorrection5sum
  -- Pull `c_α` into each `tsum` via `tsum_mul_left`, then combine 5 `tsum`s
  -- into a single `tsum` via `tsum_add`/`tsum_sub` (requires summability).
  have hL_2t := (h_summL (2 * t)).mul_left
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ))
  have hL_n2t := (h_summL (-(2 * t))).mul_left
    ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ))
  have hL_t := (h_summL t).mul_left
    (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ))
  have hL_nt := (h_summL (-t)).mul_left
    (Complex.exp ((((3/2) * t) : ℝ) : ℂ))
  have hL_0 := h_summL 0
  have hR_2t := (h_summR (2 * t)).mul_left
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ))
  have hR_n2t := (h_summR (-(2 * t))).mul_left
    ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ))
  have hR_t := (h_summR t).mul_left
    (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ))
  have hR_nt := (h_summR (-t)).mul_left
    (Complex.exp ((((3/2) * t) : ℝ) : ℂ))
  have hR_0 := h_summR 0
  -- Distribute each `c_α` through the 4-term sum so the `tsum_mul_left`
  -- pattern `c_α * (∑' k, ...)` actually appears, then push `c_α` into the
  -- tsums (in the reverse direction).  This produces, on the LHS, ten scattered
  -- `tsum`s (5 left-pole + 5 right-pole) plus 5 c_α·constantLogPi atoms and
  -- 5 c_α·rationalCorr atoms.
  simp only [mul_add, mul_sub, ← tsum_mul_left]
  -- Split each `aggregator` tsum on the RHS into 5 separate tsums via
  -- `Summable.tsum_add`/`Summable.tsum_sub` (forward direction).  After this
  -- both sides expose the same 10 tsums as ring atoms, and the non-tsum
  -- atoms are also matched up (modulo ring-rearrangement).
  rw [(((hL_2t.add hL_n2t).sub hL_t).sub hL_nt).tsum_add hL_0,
      ((hL_2t.add hL_n2t).sub hL_t).tsum_sub hL_nt,
      (hL_2t.add hL_n2t).tsum_sub hL_t,
      hL_2t.tsum_add hL_n2t]
  rw [(((hR_2t.add hR_n2t).sub hR_t).sub hR_nt).tsum_add hR_0,
      ((hR_2t.add hR_n2t).sub hR_t).tsum_sub hR_nt,
      (hR_2t.add hR_n2t).tsum_sub hR_t,
      hR_2t.tsum_add hR_n2t]
  -- Now LHS and RHS have the same 10 tsum atoms plus matching non-tsum atoms;
  -- close by `ring`, treating each tsum as an opaque atom.
  ring

#print axioms shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form

/-! ## Step 25: Substantive final identity (held separate from bookkeeping)

The mathematical heart of the audit.  Stated as a Prop so the bookkeeping
correctness above and the substantive mathematical cancellation below remain
clearly separated.

If `archAuditFinalIdentity t β` holds AND the bookkeeping decomposition
holds, the engineering target follows. -/

/-- **Substantive final identity**: the four buckets, each in clean closed
form, must algebraically combine to `primeReflectedDifference - 2π·K_2(1,t)·M(β,1)`. -/
def archAuditFinalIdentity (t β : ℝ) : Prop :=
  archConstantCarrierClosedForm t β +
  archRationalCorrectionClosedForm t β +
  (∑' k : ℕ, leftPoleTowerK2Aggregator k t β) +
  (∑' k : ℕ, rightPoleTowerK2Aggregator k t β) =
  primeReflectedDifference t β -
    2 * ((Real.pi : ℝ) : ℂ) * K_2 1 t * Contour.pairTestMellin β 1

/-- **`archRequired` audit from substantive identity** (conditional only on
the substantive final identity; bookkeeping is now unconditional).

Combines:
- `shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form` (bookkeeping,
  unconditional).
- `archAuditFinalIdentity t β` (substantive identity).

Output: `shiftedArchClosedForm_5alpha_eq_archRequired_target t β`. -/
theorem shiftedArchClosedForm_5alpha_eq_archRequired_of_final_identity
    (t β : ℝ)
    (h_identity : archAuditFinalIdentity t β) :
    shiftedArchClosedForm_5alpha_eq_archRequired_target t β := by
  unfold shiftedArchClosedForm_5alpha_eq_archRequired_target
  rw [shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form t β]
  exact h_identity

#print axioms shiftedArchClosedForm_5alpha_eq_archRequired_of_final_identity

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
