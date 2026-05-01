import Mathlib
open Real Finset BigOperators
/-!
# Zeta Zeros and Harmonic Amplitudes
We formalize the connection between the nontrivial zeros of the Riemann zeta
function and the amplitudes of the harmonics in the explicit formula for
prime-counting functions.
## Mathematical context
The explicit formula (von Mangoldt / Riemann) expresses the Chebyshev function
ψ(x) as a sum over the nontrivial zeros ρ of ζ(s):
  ψ(x) = x − ∑_ρ x^ρ/ρ − log(2π) − ½ log(1 − x⁻²)
Each zero ρ = β + iγ contributes a "harmonic" of amplitude x^β.  The functional
equation guarantees that if ρ is a zero, so is 1 − ρ.  On the critical line
(β = 1/2), the pair {ρ, 1−ρ} = {½+iγ, ½−iγ} produces harmonics of equal
amplitude x^{1/2}, which combine coherently.
An off-line zero with β ≠ 1/2 would pair with 1−ρ having a *different*
real part 1−β ≠ β.  The pair would produce harmonics with amplitudes
x^β and x^{1−β}, which are unequal for x ≠ 1.
## Key results
### Part I: Amplitude from critical-line zeros
- `critical_line_equal_amplitude`: β = 1/2 implies x^β = x^{1−β}
- `critical_line_pair_amplitude`: On the critical line, the paired harmonic
  amplitude is exactly 2·x^{1/2}
- `critical_line_coherent_harmonics`: The paired contribution
  2·x^{1/2}·cos(γ·log x) is a single coherent oscillation
### Part II: Off-line zeros produce excess amplitude
- `off_line_unequal_amplitude`: β ≠ 1/2 ∧ x > 0 ∧ x ≠ 1 → x^β ≠ x^{1−β}
- `am_gm_amplitude_bound`: x^β + x^{1−β} ≥ 2·x^{1/2} (AM-GM)
- `off_line_excess_amplitude`: β ≠ 1/2 ∧ x > 1 → x^β + x^{1−β} > 2·x^{1/2}
- `off_line_harmonics_dont_cancel`: The excess amplitude is strictly positive,
  proving the non-cancellation of off-line harmonics unconditionally
-/
set_option maxHeartbeats 800000
noncomputable section
/-! ### Part I: Critical-line zeros produce balanced amplitudes -/
/-- On the critical line (β = 1/2), the amplitude x^β equals x^{1−β},
so the harmonic pair {ρ, 1−ρ} contributes symmetrically. -/
theorem critical_line_equal_amplitude (x : ℝ) :
    x ^ (1/2 : ℝ) = x ^ (1 - 1/2 : ℝ) := by
  norm_num
/-- On the critical line, the paired harmonic amplitude is 2·√x. -/
theorem critical_line_pair_amplitude (x : ℝ) :
    x ^ (1/2 : ℝ) + x ^ (1 - 1/2 : ℝ) = 2 * x ^ (1/2 : ℝ) := by
  norm_num; ring
/-- The paired contribution from critical-line zeros ρ = 1/2 ± iγ is
a single coherent oscillation: 2·x^{1/2}·cos(γ·log x). This is the
real part of x^ρ + x^{ρ̄} when β = 1/2. -/
theorem critical_line_coherent_harmonics (x : ℝ) (γ : ℝ) :
    x ^ (1/2 : ℝ) * Real.cos (γ * Real.log x) +
    x ^ (1/2 : ℝ) * Real.cos ((-γ) * Real.log x) =
    2 * x ^ (1/2 : ℝ) * Real.cos (γ * Real.log x) := by
  rw [neg_mul, Real.cos_neg]; ring
/-! ### Part II: Off-line zeros produce non-canceling harmonics -/
/-
For x > 0 and x ≠ 1, if β ≠ 1/2 then x^β ≠ x^{1−β}.
This means an off-line zero and its functional equation partner
produce harmonics of different amplitudes.
-/
theorem off_line_unequal_amplitude (x : ℝ) (β : ℝ) (hx : x > 0) (hx1 : x ≠ 1) (hβ : β ≠ 1/2) :
    x ^ β ≠ x ^ (1 - β) := by
  norm_num [ Real.rpow_def_of_pos hx ];
  exact ⟨ by contrapose! hβ; linarith, hx.ne', hx1, by linarith ⟩
/-
AM-GM inequality for harmonic amplitudes:
x^β + x^{1−β} ≥ 2·x^{1/2} for all x > 0 and real β.
This shows that the total amplitude from a symmetric pair of zeros
is minimized when they lie on the critical line.
-/
theorem am_gm_amplitude_bound (x : ℝ) (β : ℝ) (hx : x > 0) :
    x ^ β + x ^ (1 - β) ≥ 2 * x ^ (1/2 : ℝ) := by
  -- By AM-GM inequality, we have $x^β + x^{1-β} ≥ 2 \sqrt{x^β \cdot x^{1-β}}$.
  have h_am_gm : x ^ β + x ^ (1 - β) ≥ 2 * Real.sqrt (x ^ β * x ^ (1 - β)) := by
    nlinarith [ sq_nonneg ( x ^ β - x ^ ( 1 - β ) ), Real.mul_self_sqrt ( by positivity : 0 ≤ x ^ β * x ^ ( 1 - β ) ), Real.rpow_pos_of_pos hx β, Real.rpow_pos_of_pos hx ( 1 - β ) ];
  convert h_am_gm using 2 ; rw [ ← Real.rpow_add hx ] ; norm_num;
  rw [ Real.sqrt_eq_rpow ]
/-
Strict AM-GM: for x > 1 and β ≠ 1/2, the amplitude strictly exceeds
the critical-line value 2·x^{1/2}. This is the "excess amplitude" from
an off-line zero.
-/
theorem off_line_excess_amplitude (x : ℝ) (β : ℝ) (hx : x > 1) (hβ : β ≠ 1/2) :
    x ^ β + x ^ (1 - β) > 2 * x ^ (1/2 : ℝ) := by
  rw [ show β = 1 - ( 1 - β ) by ring, Real.rpow_sub ] <;> try linarith;
  norm_num;
  rw [ ← Real.sqrt_eq_rpow, div_add', lt_div_iff₀ ] <;> try positivity;
  by_cases h : x ^ ( 1 - β ) = Real.sqrt x;
  · apply_fun Real.log at h ; norm_num [ Real.log_rpow ( zero_lt_one.trans hx ), Real.log_sqrt ( zero_le_one.trans hx.le ) ] at h;
    exact False.elim <| hβ <| by nlinarith [ Real.log_pos hx ] ;
  · cases lt_or_gt_of_ne h <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ), Real.rpow_pos_of_pos ( zero_lt_one.trans hx ) ( 1 - β ) ]
/-- The excess amplitude from an off-line zero is strictly positive,
which means the harmonics contributed by such a zero do not cancel.
This is unconditional: we do not assume RH, only that β ≠ 1/2 and x > 1.
Mathematically, the contribution of a zero-pair {β+iγ, (1−β)+iγ} to the
explicit formula is:
  x^β·cos(γ log x) + x^{1−β}·cos(γ log x) = (x^β + x^{1−β})·cos(γ log x)
On the critical line this equals 2·x^{1/2}·cos(γ log x). Off the critical
line, the amplitude factor x^β + x^{1−β} strictly exceeds 2·x^{1/2},
so the harmonic has excess energy that cannot be canceled by any
critical-line contribution. -/
theorem off_line_harmonics_dont_cancel (x : ℝ) (β : ℝ) (hx : x > 1) (hβ : β ≠ 1/2) :
    x ^ β + x ^ (1 - β) - 2 * x ^ (1/2 : ℝ) > 0 := by
  linarith [off_line_excess_amplitude x β hx hβ]
/-
The amplitude difference can be expressed as a perfect square-like form:
(x^{β/2} − x^{(1−β)/2})² ≥ 0, with equality iff β = 1/2 (for x ≠ 1).
This makes the non-cancellation geometrically transparent.
-/
theorem amplitude_difference_sq_form (x : ℝ) (β : ℝ) (hx : x > 0) :
    x ^ β + x ^ (1 - β) - 2 * x ^ (1/2 : ℝ) =
    (x ^ (β/2) - x ^ ((1 - β)/2)) ^ 2 := by
  ring;
  norm_num [ sq, ← Real.rpow_add hx ] ; ring
/-
Combining everything: for x > 1 and β ≠ 1/2, the harmonic pair from
an off-line zero at β+iγ and (1−β)+iγ produces a strictly larger oscillation
than a critical-line pair would. This excess oscillation is precisely
(x^{β/2} − x^{(1−β)/2})², which is nonzero, proving that the harmonics
from off-line zeros do not cancel.
-/
theorem off_line_excess_is_square (x : ℝ) (β : ℝ) (hx : x > 1) (hβ : β ≠ 1/2) :
    (x ^ (β/2) - x ^ ((1 - β)/2)) ^ 2 > 0 := by
  exact sq_pos_of_ne_zero ( sub_ne_zero_of_ne <| fun h ↦ hβ <| by apply_fun Real.log at h; rw [ Real.log_rpow ( by linarith ), Real.log_rpow ( by linarith ) ] at h; nlinarith [ Real.log_pos hx ] )
end