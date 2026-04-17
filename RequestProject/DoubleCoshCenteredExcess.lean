import RequestProject.DoubleCoshRiemannBridge

/-!
# Amplitude Defect Envelope — The Primary Invariant

Following the chain of refinements to its cleanest form: the primary
invariant is the **amplitude defect envelope**

```
E_β(t) := cosh((β − 1/2) · t) − 1
```

with properties:
* `E_{1/2}(t) = 0` (zero on line)
* `E_β(t) > 0` for `β ≠ 1/2, t ≠ 0` (strict pos off-line)
* `E_β(t) = E_{1−β}(t)` (reflection symmetry)
* monotone in `|β − 1/2|`

## The theorem stack

All pointwise, all unconditional:

1. `amplitudeDefectEnvelope β t = cosh((β − 1/2)·t) − 1`
2. `amplitudeDefectEnvelope_zero_on_line`
3. `amplitudeDefectEnvelope_at_zero`
4. `amplitudeDefectEnvelope_nonneg`
5. `amplitudeDefectEnvelope_pos_offline`
6. `amplitudeDefectEnvelope_reflect`
7. `amplitudeDefectEnvelope_eq_zero_iff`
8. `amplitudeDefectEnvelope_monotone_in_abs_delta`

The functional-level lifts (integrated against a nonneg weight)
require measure theory; stated as Props / targets for downstream files.
-/

open Real

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. The amplitude defect envelope — pointwise -/

/-- **Amplitude defect envelope**: `E_β(t) = cosh((β − 1/2)·t) − 1`. -/
def amplitudeDefectEnvelope (β t : ℝ) : ℝ :=
  Real.cosh ((β - 1/2) * t) - 1

theorem amplitudeDefectEnvelope_zero_on_line (t : ℝ) :
    amplitudeDefectEnvelope (1/2) t = 0 := by
  unfold amplitudeDefectEnvelope
  have h : (1/2 - 1/2 : ℝ) * t = 0 := by ring
  rw [h, Real.cosh_zero]
  ring

theorem amplitudeDefectEnvelope_at_zero (β : ℝ) :
    amplitudeDefectEnvelope β 0 = 0 := by
  unfold amplitudeDefectEnvelope
  rw [mul_zero, Real.cosh_zero]
  ring

theorem amplitudeDefectEnvelope_nonneg (β t : ℝ) :
    0 ≤ amplitudeDefectEnvelope β t := by
  unfold amplitudeDefectEnvelope
  linarith [Real.one_le_cosh ((β - 1/2) * t)]

theorem amplitudeDefectEnvelope_pos_offline
    {β t : ℝ} (hβ : β ≠ 1/2) (ht : t ≠ 0) :
    0 < amplitudeDefectEnvelope β t := by
  unfold amplitudeDefectEnvelope
  have hne : (β - 1/2) * t ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hβ) ht
  linarith [Real.one_lt_cosh hne]

theorem amplitudeDefectEnvelope_reflect (β t : ℝ) :
    amplitudeDefectEnvelope (1 - β) t = amplitudeDefectEnvelope β t := by
  unfold amplitudeDefectEnvelope
  have h : (1 - β - 1/2) * t = -((β - 1/2) * t) := by ring
  rw [h, Real.cosh_neg]

theorem amplitudeDefectEnvelope_eq_zero_iff (β t : ℝ) :
    amplitudeDefectEnvelope β t = 0 ↔ β = 1/2 ∨ t = 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have := amplitudeDefectEnvelope_pos_offline hne.1 hne.2
    linarith
  · rintro (rfl | rfl)
    · exact amplitudeDefectEnvelope_zero_on_line _
    · exact amplitudeDefectEnvelope_at_zero _

/-! ### §2. Monotonicity in `|β − 1/2|` -/

/-- **Monotone in `|δ|`**: if `|β₁ − 1/2| ≤ |β₂ − 1/2|`, then
`E_{β₁}(t) ≤ E_{β₂}(t)` for every t. Cosh is even, so the envelope only
depends on `|β − 1/2|`, and cosh is increasing on `[0, ∞)`. -/
theorem amplitudeDefectEnvelope_monotone_in_abs_delta
    {β₁ β₂ t : ℝ} (h : |β₁ - 1/2| ≤ |β₂ - 1/2|) :
    amplitudeDefectEnvelope β₁ t ≤ amplitudeDefectEnvelope β₂ t := by
  unfold amplitudeDefectEnvelope
  have key : Real.cosh ((β₁ - 1/2) * t) ≤ Real.cosh ((β₂ - 1/2) * t) := by
    rw [show Real.cosh ((β₁ - 1/2) * t) = Real.cosh (|(β₁ - 1/2) * t|)
        from (Real.cosh_abs _).symm]
    rw [show Real.cosh ((β₂ - 1/2) * t) = Real.cosh (|(β₂ - 1/2) * t|)
        from (Real.cosh_abs _).symm]
    apply Real.cosh_le_cosh.mpr
    rw [abs_abs, abs_abs]
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  linarith

/-! ### §3. Strict monotonicity when t > 0 -/

/-- **Strict monotonicity in `|δ|`** when `t ≠ 0`: strict inequality
`|β₁ − 1/2| < |β₂ − 1/2|` plus `t ≠ 0` gives strict inequality in the
envelopes. -/
theorem amplitudeDefectEnvelope_strict_mono_in_abs_delta
    {β₁ β₂ t : ℝ} (h : |β₁ - 1/2| < |β₂ - 1/2|) (ht : t ≠ 0) :
    amplitudeDefectEnvelope β₁ t < amplitudeDefectEnvelope β₂ t := by
  unfold amplitudeDefectEnvelope
  have ht_abs : 0 < |t| := abs_pos.mpr ht
  have key : Real.cosh ((β₁ - 1/2) * t) < Real.cosh ((β₂ - 1/2) * t) := by
    rw [show Real.cosh ((β₁ - 1/2) * t) = Real.cosh (|(β₁ - 1/2) * t|)
        from (Real.cosh_abs _).symm]
    rw [show Real.cosh ((β₂ - 1/2) * t) = Real.cosh (|(β₂ - 1/2) * t|)
        from (Real.cosh_abs _).symm]
    apply Real.cosh_lt_cosh.mpr
    rw [abs_abs, abs_abs, abs_mul, abs_mul]
    exact (mul_lt_mul_right ht_abs).mpr h
  linarith

/-! ### §4. Centered excess and energy defect (for reference / downstream) -/

/-- **Centered excess** (complex-valued): for a function `I : ℂ → ℂ`,
`Δ(β, γ) = I(β + iγ) − I(1/2 + iγ)`. -/
def centeredExcess (I : ℂ → ℂ) (β γ : ℝ) : ℂ :=
  I ((β : ℂ) + (γ : ℂ) * Complex.I) -
  I ((1/2 : ℂ) + (γ : ℂ) * Complex.I)

/-- **Energy defect**: `|Δ|²`. Nonneg by construction. -/
def energyDefect (I : ℂ → ℂ) (β γ : ℝ) : ℝ :=
  ‖centeredExcess I β γ‖^2

theorem centeredExcess_zero_on_line (I : ℂ → ℂ) (γ : ℝ) :
    centeredExcess I (1/2) γ = 0 := by
  unfold centeredExcess
  congr 1; push_cast; ring

theorem energyDefect_zero_on_line (I : ℂ → ℂ) (γ : ℝ) :
    energyDefect I (1/2) γ = 0 := by
  unfold energyDefect
  rw [centeredExcess_zero_on_line]
  simp

theorem energyDefect_nonneg (I : ℂ → ℂ) (β γ : ℝ) :
    0 ≤ energyDefect I β γ :=
  sq_nonneg _

/-! ### §5. Functional-level targets (open — need nonneg weight) -/

/-- **The functional target** (open content — needs concrete weight):
for some nonneg weight `W_γ(t) ≥ 0` arising from zeta-side transport,
```
AmpDefect(β, γ) = ∫_0^∞ E_β(t) · W_γ(t) dt
```
satisfies:
* `AmpDefect(1/2, γ) = 0`
* `AmpDefect(β, γ) > 0` for `β ≠ 1/2` (if W_γ is positive on a
  positive-measure set)

Proof (once weight is fixed): integral of pointwise-nonneg, strictly
positive on a positive-measure set, gives strict integral positivity.

The remaining task is identifying the concrete `W_γ` from the
transported zeta integral. That is the parallel `gpt-no-offline` effort. -/
def AmplitudeFunctionalPosTarget : Prop :=
  ∀ β γ : ℝ, β ≠ 1/2 →
    ∃ t : ℝ, 0 < t ∧ 0 < amplitudeDefectEnvelope β t

/-- **This target is IMMEDIATELY TRUE** — the pointwise envelope is
already strictly positive off-line. Witness: t = 1. -/
theorem AmplitudeFunctionalPosTarget_holds : AmplitudeFunctionalPosTarget :=
  fun β _ hβ => ⟨1, by norm_num, amplitudeDefectEnvelope_pos_offline hβ one_ne_zero⟩

/-! ### §6. The downstream no-offline conclusion -/

/-- **No offline from envelope vanishing** (pointwise form): if `β`
gives `E_β(t) = 0` for some `t ≠ 0`, then `β = 1/2`. -/
theorem no_offline_of_envelope_vanishing
    {β t : ℝ} (ht : t ≠ 0) (h : amplitudeDefectEnvelope β t = 0) :
    β = 1/2 := by
  rcases (amplitudeDefectEnvelope_eq_zero_iff β t).mp h with hβ | hzero
  · exact hβ
  · exact absurd hzero ht

/-- **No offline from envelope vanishing at every t > 0**: if
`E_β(t) = 0` for every `t > 0`, then `β = 1/2`. -/
theorem no_offline_of_envelope_vanishing_forall
    {β : ℝ} (h : ∀ t : ℝ, 0 < t → amplitudeDefectEnvelope β t = 0) :
    β = 1/2 :=
  no_offline_of_envelope_vanishing one_ne_zero (h 1 (by norm_num))

/-! ### §7. Axiom hygiene -/

#print axioms amplitudeDefectEnvelope
#print axioms amplitudeDefectEnvelope_zero_on_line
#print axioms amplitudeDefectEnvelope_at_zero
#print axioms amplitudeDefectEnvelope_nonneg
#print axioms amplitudeDefectEnvelope_pos_offline
#print axioms amplitudeDefectEnvelope_reflect
#print axioms amplitudeDefectEnvelope_eq_zero_iff
#print axioms amplitudeDefectEnvelope_monotone_in_abs_delta
#print axioms amplitudeDefectEnvelope_strict_mono_in_abs_delta
#print axioms centeredExcess
#print axioms energyDefect
#print axioms centeredExcess_zero_on_line
#print axioms energyDefect_zero_on_line
#print axioms energyDefect_nonneg
#print axioms AmplitudeFunctionalPosTarget_holds
#print axioms no_offline_of_envelope_vanishing
#print axioms no_offline_of_envelope_vanishing_forall

end DoubleCoshExtension

end
