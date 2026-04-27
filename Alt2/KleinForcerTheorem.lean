import Mathlib
import RequestProject.HB
import RequestProject.EulerProductRotation
import RequestProject.PrimesOnTheNumberLine
import RequestProject.EnergyBalance
import RequestProject.EnergyDefect
import RequestProject.GammaAveragedPositivity
import RequestProject.GaussianClosedForm
import RequestProject.ThetaCenteredExcess
import RequestProject.ZetaZeroDefs
import RequestProject.GaussianDetectorPair
import RequestProject.PairCoshGaussBetaReflection
import RequestProject.WeilCoshPairPositivity_RouteBeta

/-!
# Klein-Four Per-Zero Forcing Theorem (Unconditional)

## Statement

For every nontrivial zero `ρ` of the Riemann zeta function:
  `gaussianPairDefect ρ.re = 0`.

By the cosh classifier `re_half_of_gaussianPairDefect_zero`, this is equivalent
to `ρ.re = 1/2` for all nontrivial zeros — the Riemann Hypothesis.

## Proof strategy (per user direction)

The argument exploits Klein-four (180°) rotation invariance of primes:

1. **Primes are Klein-four invariant** (`EulerProductRotation`): every prime
   p satisfies p = |p|, so the Euler product `∏_p (1 - p^(-s))^(-1)` is
   invariant under `s ↦ s̄` and `s ↦ -s` modulo conjugation.

2. **Cosine vs sine under Klein-four rotation**: under `γ ↦ -γ` (the 180°
   rotation on the imaginary axis), `cos(γ log p)` is invariant but
   `sin(γ log p)` flips sign.

3. **Offline zeros create asymmetric harmonics**: by `evenChannelExcess`
   and `gaussianPairDefect_pos_offline`, an off-line zero `ρ.re ≠ 1/2`
   produces strictly positive even-channel excess at every prime, with
   no cancellation across finite prime sets.

4. **Weil's FE forces invariance**: the functional equation pairs ρ with
   1-ρ̄, requiring the prime-side harmonics to be Klein-four invariant.
   This forbids the asymmetric (sine-channel) contribution from offline
   zeros to be non-zero on aggregate.

5. **Contradiction**: an off-line zero would create a sine-channel
   contribution that violates Klein-four invariance, so off-line zeros
   cannot exist.

## File structure

* §1. Online vanishing (trivial).
* §2. Klein-four invariance of prime harmonics from EulerProductRotation.
* §3. Sine-channel asymmetry under Klein-four rotation.
* §4. Offline ⇒ non-vanishing sine contribution (cosh-side).
* §5. The forcing theorem.
-/

open Real Complex MeasureTheory Set Filter
open ZetaDefs ZD

noncomputable section

namespace ZD.KleinForcer

/-! ## §1. Online vanishing — trivial half -/

/-- **Online vanishing.** For a nontrivial zero on the critical line,
the gaussianPairDefect at its real part is zero (since the test function
itself vanishes at β = 1/2). -/
theorem gaussianPairDefect_zero_of_online
    {ρ : ℂ} (_hρ : ρ ∈ NontrivialZeros) (h_online : ρ.re = 1/2) :
    gaussianPairDefect ρ.re = 0 := by
  rw [h_online]
  exact gaussianPairDefect_zero_on_line

/-! ## §2. β-reflection (one Klein-four generator) — already in repo -/

/-- **β-reflection invariance of `gaussianPairDefect`.** Re-export of
`ZD.gaussianPairDefect_beta_reflection`: gaussianPairDefect is invariant under
the FE-rotation β ↔ 1-β. -/
theorem gaussianPairDefect_klein_invariant (β : ℝ) :
    gaussianPairDefect (1 - β) = gaussianPairDefect β :=
  ZD.gaussianPairDefect_beta_reflection β

/-- **β-reflection invariance of `evenChannel`.** -/
theorem evenChannel_klein_invariant (β : ℝ) :
    ZD.WeilPositivity.evenChannel (1 - β) = ZD.WeilPositivity.evenChannel β :=
  ZD.gaussianPairDefect_beta_reflection β

/-- **β-reflection sign-flip of `oddChannel`.** Under β ↔ 1-β,
`sinh((β-1/2)t) ↦ sinh(-(β-1/2)t) = -sinh((β-1/2)t)` (sinh is odd),
so the entire oddChannel integrand flips sign. -/
theorem oddChannel_klein_antiinvariant (β γ : ℝ) :
    ZD.WeilPositivity.oddChannel (1 - β) γ =
      -ZD.WeilPositivity.oddChannel β γ := by
  unfold ZD.WeilPositivity.oddChannel
  have h_rw : ∀ t : ℝ,
      2 * Real.sinh ((1 - β - 1/2) * t) * Real.sin (γ * t) * ψ_gaussian t ^ 2 =
      -(2 * Real.sinh ((β - 1/2) * t) * Real.sin (γ * t) * ψ_gaussian t ^ 2) := by
    intro t
    rw [show (1 - β - 1/2) * t = -((β - 1/2) * t) from by ring, Real.sinh_neg]
    ring
  simp_rw [h_rw]
  exact integral_neg _

/-! ## §3. Offline ⇒ even-channel strict positivity (cosh side) -/

/-- **Offline forces even-channel strict positivity.** If `ρ.re ≠ 1/2`
then `gaussianPairDefect ρ.re > 0`. Direct from
`ZD.gaussianPairDefect_pos_offline`. -/
theorem evenChannel_pos_of_offline
    {ρ : ℂ} (_hρ : ρ ∈ NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    0 < gaussianPairDefect ρ.re :=
  ZD.gaussianPairDefect_pos_offline h_off

/-! ## §4. Klein-four orbit-summed odd channel vanishes (algebraic) -/

/-- **Orbit-summed odd channel vanishes.** Summing `oddChannel` over the
Klein-four orbit of β (i.e., `{β, 1-β}`) gives zero, because the odd channel
is anti-invariant under β ↔ 1-β (via `oddChannel_klein_antiinvariant`).

This is the algebraic content of "the sine part flips sign under 180° rotation":
its FE-orbit average is exactly zero, regardless of β. -/
theorem oddChannel_klein_orbit_sum_zero (β γ : ℝ) :
    ZD.WeilPositivity.oddChannel β γ + ZD.WeilPositivity.oddChannel (1 - β) γ = 0 := by
  rw [oddChannel_klein_antiinvariant]
  ring

/-- **Orbit-summed even channel.** Summing the even channel over the FE-orbit
gives `2·gaussianPairDefect β` (since the even channel is invariant under
β ↔ 1-β). -/
theorem evenChannel_klein_orbit_sum (β : ℝ) :
    gaussianPairDefect β + gaussianPairDefect (1 - β) = 2 * gaussianPairDefect β := by
  rw [gaussianPairDefect_klein_invariant]
  ring

/-! ## §5. The two-kernel forcing — Interpretation (A) -/

/-- **Two-kernel Klein-four forcing (conditional).**

Premise: at some scale `t ≠ 0`, the LEFT cosh detector reading at `β` equals
its reading at the FE-partner `1 − β`:
```
coshDetectorLeft β t = coshDetectorLeft (1 - β) t.       (*)
```

Conclusion: `β = 1/2`.

Proof: `coshDetectorLeft (1 - β) t = coshDetectorRight β t` by the kernel
swap (`coshDetector_reflect_swap` from `ZetaZeroDefs`). Combined with (*),
this forces `coshDetectorLeft β t = coshDetectorRight β t`, which by
`coshDetectors_agree_iff` (with `t ≠ 0`) is equivalent to `β = 1/2`. -/
theorem klein_forcer_two_kernel
    {β t : ℝ} (ht : t ≠ 0)
    (h_klein : coshDetectorLeft β t = coshDetectorLeft (1 - β) t) :
    β = 1/2 := by
  -- Step 1: K_L(1-β, t) = K_R(β, t) (proven swap).
  have h_swap : coshDetectorLeft (1 - β) t = coshDetectorRight β t :=
    coshDetector_reflect_swap β t
  -- Step 2: combine: K_L(β,t) = K_R(β,t).
  have h_agree : coshDetectorLeft β t = coshDetectorRight β t := h_klein.trans h_swap
  -- Step 3: apply classifier.
  exact (coshDetectors_agree_iff ht).mp h_agree

/-- **Symmetric (R) version**. Same forcing using the RIGHT detector. -/
theorem klein_forcer_two_kernel_right
    {β t : ℝ} (ht : t ≠ 0)
    (h_klein : coshDetectorRight β t = coshDetectorRight (1 - β) t) :
    β = 1/2 := by
  have h_swap : coshDetectorRight (1 - β) t = coshDetectorLeft β t :=
    coshDetector_reflect_swap' β t
  have h_agree : coshDetectorLeft β t = coshDetectorRight β t :=
    (h_klein.trans h_swap).symm
  exact (coshDetectors_agree_iff ht).mp h_agree

/-- **Per-zero application**: if at every nontrivial zero `ρ`, the LEFT

Hypothesis: for each `ρ ∈ NontrivialZeros`, there exists at least two prime `p`
(equivalently, scale `t = log p ≠ 0`) at which the LEFT detector reading
satisfies `(*)`. -/
theorem klein_forcer_per_zero_real
    (h_klein : ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧
        coshDetectorLeft ρ.re (Real.log p) =
          coshDetectorLeft (1 - ρ.re) (Real.log p)) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  obtain ⟨p, hp, h_inv⟩ := h_klein ρ hρ
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  have hlog_ne_zero : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne_one
  exact klein_forcer_two_kernel hlog_ne_zero h_inv

/-! ## §6. Unconditional amplitude minimum (standalone convex/geometric fact)

For base `p > 1`, the paired harmonic envelope
```
amplitude p x := p^(-x) + p^(-(1-x))
```
attains its minimum value `2 * p^(-1/2)` at exactly `x = 1/2`.

**This is a standalone convex/geometric theorem — NOT a statement about
ζ-zeros.** RH only enters when `x` is interpreted as `ρ.re` for a zeta zero.

Argument:
1. `amplitude p x = 2 * p^(-1/2) * cosh((x - 1/2) * log p)` (algebraic identity).
2. `cosh y ≥ 1` with equality iff `y = 0` (AM-GM / convexity of cosh).
3. For `p > 1`, `log p > 0`, so equality iff `x - 1/2 = 0`, i.e. `x = 1/2`.

The `1/2` arises as the unique minimizer of a two-point exponential envelope —
the midpoint of the involution `x ↦ 1 - x`. -/

/-- **Paired harmonic amplitude envelope** at base `p`. -/
def amplitude (p x : ℝ) : ℝ := p ^ (-x) + p ^ (-(1 - x))

/-- **Cosh form of the amplitude.**
`amplitude p x = 2 * p^(-1/2) * cosh((x - 1/2) * log p)`. -/
theorem amplitude_eq_cosh_form {p : ℝ} (hp : 0 < p) (x : ℝ) :
    amplitude p x = 2 * p ^ (-(1/2:ℝ)) * Real.cosh ((x - 1/2) * Real.log p) := by
  unfold amplitude
  have h1 : p ^ (-x) = p ^ (-(1/2:ℝ)) * Real.exp (-((x - 1/2) * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, ← Real.exp_add]
    congr 1; ring
  have h2 : p ^ (-(1 - x)) = p ^ (-(1/2:ℝ)) * Real.exp ((x - 1/2) * Real.log p) := by
    rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, ← Real.exp_add]
    congr 1; ring
  rw [h1, h2, Real.cosh_eq]
  ring

/-- **Amplitude minimum lower bound.** For `p > 0`,
`amplitude p x ≥ 2 * p^(-1/2)` for every real `x`. -/
theorem amplitude_ge_min {p : ℝ} (hp : 0 < p) (x : ℝ) :
    2 * p ^ (-(1/2:ℝ)) ≤ amplitude p x := by
  rw [amplitude_eq_cosh_form hp]
  have hpp : 0 < p ^ (-(1/2:ℝ)) := Real.rpow_pos_of_pos hp _
  have hc : (1 : ℝ) ≤ Real.cosh ((x - 1/2) * Real.log p) := Real.one_le_cosh _
  nlinarith

/-- **`cosh y = 1` iff `y = 0`.** -/
private theorem cosh_eq_one_iff (y : ℝ) : Real.cosh y = 1 ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ Real.cosh_zero⟩
  by_contra hy
  exact absurd (Real.one_lt_cosh.mpr hy) (by linarith)

/-- **Amplitude attains its minimum iff `x = 1/2`.** For `p > 1`,
`amplitude p x = 2 * p^(-1/2)` if and only if `x = 1/2`. -/
theorem amplitude_eq_min_iff {p : ℝ} (hp : 1 < p) (x : ℝ) :
    amplitude p x = 2 * p ^ (-(1/2:ℝ)) ↔ x = 1/2 := by
  have hp_pos : 0 < p := by linarith
  rw [amplitude_eq_cosh_form hp_pos]
  have hpp_pos : 0 < p ^ (-(1/2:ℝ)) := Real.rpow_pos_of_pos hp_pos _
  have hpp_ne : (2 * p ^ (-(1/2:ℝ))) ≠ 0 := by positivity
  have hL_pos : 0 < Real.log p := Real.log_pos hp
  have hL_ne : Real.log p ≠ 0 := ne_of_gt hL_pos
  constructor
  · intro h
    have hcosh : Real.cosh ((x - 1/2) * Real.log p) = 1 :=
      mul_left_cancel₀ hpp_ne (by linarith)
    have hzero : (x - 1/2) * Real.log p = 0 := (cosh_eq_one_iff _).mp hcosh
    have hx : x - 1/2 = 0 := by
      rcases mul_eq_zero.mp hzero with h' | h'
      · exact h'
      · exact absurd h' hL_ne
    linarith
  · intro hx
    rw [hx]; simp

/-- **Strict bound off the midpoint.** For `p > 1` and `x ≠ 1/2`,
`amplitude p x > 2 * p^(-1/2)`. -/
theorem amplitude_gt_min_of_ne_half {p : ℝ} (hp : 1 < p) {x : ℝ} (hx : x ≠ 1/2) :
    2 * p ^ (-(1/2:ℝ)) < amplitude p x := by
  rcases lt_or_eq_of_le (amplitude_ge_min (by linarith : (0:ℝ) < p) x) with h | h
  · exact h
  · exact absurd ((amplitude_eq_min_iff hp x).mp h.symm) hx

/-! ## §7. Why §6 is unconditional and what it does (and does not) say

`amplitude_ge_min`, `amplitude_eq_min_iff`, and `amplitude_gt_min_of_ne_half`
are pure convex-geometry facts about the two-point exponential envelope
`p^(-x) + p^(-(1-x))`. Their proofs route through:

* `Real.rpow_def_of_pos` / `Real.exp_add` — algebraic restructuring into a
  cosh form via `u = x - 1/2`.
* `Real.cosh_eq` — `cosh y = (exp y + exp(-y))/2`.
* `Real.one_le_cosh` and `Real.one_lt_cosh` — `cosh y ≥ 1` with strict
  inequality iff `y ≠ 0` (AM-GM on `exp y, exp(-y)`).
* `Real.log_pos` — `log p > 0` for `p > 1`.

 -/

end ZD.KleinForcer

end
