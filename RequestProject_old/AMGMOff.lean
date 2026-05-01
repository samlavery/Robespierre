import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

/-!
# Amplitude Envelope Model for Zeta Zeros

We formalize the amplitude envelope framework relating balanced (on-line)
and off-line zero envelopes for the Riemann zeta function.

## Core definitions

* `E_bal R` — the balanced envelope `2 R^(1/2)`
* `E_off β R` — the off-line envelope `R^β + R^(1-β)`
* `D_excess β R` — the excess `E_off β R - E_bal R`
* `A_bal` — the balanced (unit) amplitude `1`
* `A_off β R` — the off-line amplitude `1 + D_excess β R`

## Key results

1. The excess equals the AM–GM gap: `D_excess β R = (R^(β/2) - R^((1-β)/2))²`
2. Under RH (β = 1/2): `D_excess (1/2) R = 0`, so `A_off (1/2) R = 1`
3. Off-line (β ≠ 1/2, R > 0, R ≠ 1): `D_excess β R > 0`, so `A_off β R > 1`

The logical order is:
  raw envelopes → excess D_β(R) → attach to unit baseline
-/

/-- The balanced envelope: `E_bal(R) = 2 R^(1/2)`. -/
def E_bal (R : ℝ) : ℝ := 2 * R ^ (1/2 : ℝ)

/-- The off-line envelope: `E_off(β, R) = R^β + R^(1-β)`. -/
def E_off (β R : ℝ) : ℝ := R ^ β + R ^ (1 - β)

/-- The excess (AM–GM gap): `D_β(R) = E_off(β, R) - E_bal(R)`. -/
def D_excess (β R : ℝ) : ℝ := E_off β R - E_bal R

/-- The balanced amplitude (unit baseline). -/
def A_bal : ℝ := 1

/-- The off-line amplitude: `A_off(β, R) = 1 + D_β(R)`.
    This attaches the excess to the unit baseline. -/
def A_off (β R : ℝ) : ℝ := 1 + D_excess β R

/-! ## Unfolded form of the excess -/

/-- The excess unfolds to `R^β + R^(1-β) - 2 R^(1/2)`. -/
theorem D_excess_eq (β R : ℝ) :
    D_excess β R = R ^ β + R ^ (1 - β) - 2 * R ^ (1/2 : ℝ) := by
  unfold D_excess E_off E_bal
  ring

/-! ## The AM–GM gap identity -/

/-
The excess equals the squared difference of half-power terms:
    `D_β(R) = (R^(β/2) - R^((1-β)/2))²`.
    This is just the AM–GM gap in disguise. Requires `R > 0`.
-/
theorem D_excess_eq_sq (β R : ℝ) (hR : 0 < R) :
    D_excess β R = (R ^ (β / 2) - R ^ ((1 - β) / 2)) ^ 2 := by
  rw [ D_excess_eq ] ; ring;
  norm_num [ sq, ← Real.rpow_add hR ] ; ring

/-! ## Under RH: β = 1/2 gives zero excess -/

/-
When β = 1/2 the excess vanishes: `D_{1/2}(R) = 0`.
-/
theorem D_excess_half (R : ℝ) (hR : 0 < R) :
    D_excess (1/2 : ℝ) R = 0 := by
  unfold D_excess;
  unfold E_off E_bal; ring

/-
Under RH (β = 1/2), the off-line amplitude equals the balanced amplitude:
    `A_off(1/2, R) = 1 = A_bal`.
-/
theorem A_off_half_eq_one (R : ℝ) (hR : 0 < R) :
    A_off (1/2 : ℝ) R = 1 := by
  grind +locals

theorem A_off_half_eq_A_bal (R : ℝ) (hR : 0 < R) :
    A_off (1/2 : ℝ) R = A_bal := by
  unfold A_bal
  exact A_off_half_eq_one R hR

/-! ## Off-line: β ≠ 1/2 gives positive excess -/

/-
The excess is always nonneg for R > 0.
-/
theorem D_excess_nonneg (β R : ℝ) (hR : 0 < R) :
    0 ≤ D_excess β R := by
  exact D_excess_eq_sq β R hR ▸ sq_nonneg _

/-
Off-line (β ≠ 1/2, R > 0, R ≠ 1), the excess is strictly positive.
-/
theorem D_excess_pos (β R : ℝ) (hR : 0 < R) (hR1 : R ≠ 1) (hβ : β ≠ 1/2) :
    0 < D_excess β R := by
  convert sq_pos_of_ne_zero _;
  convert D_excess_eq_sq β R hR;
  · infer_instance;
  · infer_instance;
  · contrapose! hβ; rw [ sub_eq_zero ] at *; rw [ Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hR ] at *; norm_num [ hR.ne', hR1 ] at *;
    linarith [ hβ.resolve_right ( by linarith ) ]

/-
Off-line, the amplitude strictly exceeds the unit baseline.
-/
theorem A_off_gt_one (β R : ℝ) (hR : 0 < R) (hR1 : R ≠ 1) (hβ : β ≠ 1/2) :
    1 < A_off β R := by
  exact lt_add_of_pos_right _ ( D_excess_pos β R hR hR1 hβ )

/-- Off-line, the amplitude strictly exceeds the balanced amplitude. -/
theorem A_off_gt_A_bal (β R : ℝ) (hR : 0 < R) (hR1 : R ≠ 1) (hβ : β ≠ 1/2) :
    A_bal < A_off β R := by
  unfold A_bal
  exact A_off_gt_one β R hR hR1 hβ

/-! ## Pairs of off-line zeros

Off-line zeros come in conjugate pairs at `β` and `1-β` (by the functional equation).
The off-line envelope `E_off β R = R^β + R^(1-β)` already encodes both members
of such a pair. The amplitude model `A_off β R = 1 + D_excess β R` therefore
captures the combined amplitude injection from a conjugate pair of off-line zeros.
-/

/-
The off-line envelope is symmetric in β ↔ 1-β, reflecting conjugate pairing.
-/
theorem E_off_symm (β R : ℝ) : E_off β R = E_off (1 - β) R := by
  unfold E_off; ring;

/-- The excess is symmetric in β ↔ 1-β. -/
theorem D_excess_symm (β R : ℝ) : D_excess β R = D_excess (1 - β) R := by
  unfold D_excess
  rw [E_off_symm]

/-- The off-line amplitude is symmetric in β ↔ 1-β. -/
theorem A_off_symm (β R : ℝ) : A_off β R = A_off (1 - β) R := by
  unfold A_off
  rw [D_excess_symm]

/-! ## Summary

The logical flow is:

1. **Raw envelopes** `E_bal`, `E_off` are defined purely from the power sums.
2. **Excess** `D_β(R) = E_off - E_bal` measures the AM–GM gap.
3. **Amplitude model** attaches the excess to the unit baseline:
   `A_off(β, R) = 1 + D_β(R)`.
4. **RH** ⟺ `β = 1/2` ⟺ `D = 0` ⟺ `A_off = 1 = A_bal`.
5. **Off-line** ⟺ `β ≠ 1/2` ⟺ `D > 0` ⟺ `A_off > 1 > A_bal`.

No circular reasoning: the unit baseline `A_bal = 1` is chosen *after* the
excess is derived from the raw envelopes.
-/

end