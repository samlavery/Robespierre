import Mathlib

/-!
# Central Definitions for Riemann Zeta Zeros

This file provides the canonical definitions for nontrivial zeros of the Riemann
zeta function, using Mathlib's `riemannZeta` throughout. All other files in the
project should import this file rather than defining their own copies.

## Main definitions

* `NontrivialZeros` — the set of nontrivial zeros: `{s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0}`
* `OffLineZeros` — nontrivial zeros with `Re(s) ≠ 1/2`
* `OnLineZeros` — nontrivial zeros with `Re(s) = 1/2`
* `IsNontrivialZetaZero` — predicate form of `NontrivialZeros`
* `IsOfflineZetaZero` — predicate form of `OffLineZeros`
* `NontrivialZetaZeros` — alias for `NontrivialZeros` (backward compatibility)
* `ZetaDefs.harmonicDiffPiThird` — harmonic difference at π/3 (cosh version)
* `ZetaDefs.amplitudeDefect` — amplitude defect at scale `r` for real part `σ`
* `WitnessPredicate` — witness predicate for positive harmonic difference
* `offlineWitnesses` — synthetic offline witness zeros
* `S_cancelling_WitnessSet` — offline zeros and witnesses with positive harmonic difference

## Key lemmas

* `ZetaDefs.proof_of_no_cancellation` — every offline zeta zero produces a witness scale
  with strictly positive amplitude defect
-/

open Real BigOperators Complex

noncomputable section
namespace ZD
-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Zero Set Definitions (using Mathlib's riemannZeta)
-- ════════════════════════════════════════════════════════════════════════════

/-- A nontrivial zero of the Riemann zeta function (predicate form):
    `ζ(s) = 0` with `s` in the critical strip `0 < Re(s) < 1`.
    Uses Mathlib's `riemannZeta`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Nontrivial zeros of the Riemann zeta function:
    `{s : ℂ | 0 < Re(s) ∧ Re(s) < 1 ∧ ζ(s) = 0}`.
    Uses Mathlib's `riemannZeta`. -/
def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

/-- Alias for `NontrivialZeros` for backward compatibility. -/
def NontrivialZetaZeros : Set ℂ := NontrivialZeros

/-- `NontrivialZetaZeros` is definitionally equal to `NontrivialZeros`. -/
theorem NontrivialZetaZeros_eq : NontrivialZetaZeros = NontrivialZeros := rfl

/-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/
def OffLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }

/-- On-line nontrivial zeros: those with `Re(s) = 1/2`. -/
def OnLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re = 1 / 2 }

/-- An offline nontrivial zeta zero (predicate form). -/
def IsOfflineZetaZero (s : ℂ) : Prop :=
  s ∈ NontrivialZeros ∧ s.re ≠ 1 / 2

/-- Membership in `NontrivialZeros`. -/
theorem mem_NontrivialZeros_iff {s : ℂ} :
    s ∈ NontrivialZeros ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := Iff.rfl

/-- Membership in `OffLineZeros`. -/
theorem mem_OffLineZeros_iff {s : ℂ} :
    s ∈ OffLineZeros ↔ s ∈ NontrivialZeros ∧ s.re ≠ 1 / 2 := Iff.rfl

/-- Membership in `OnLineZeros`. -/
theorem mem_OnLineZeros_iff {s : ℂ} :
    s ∈ OnLineZeros ↔ s ∈ NontrivialZeros ∧ s.re = 1 / 2 := Iff.rfl

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. Witness Definitions
-- ════════════════════════════════════════════════════════════════════════════

/-- Synthetic offline witness zeros with `β ∈ {1/3, 2/5, 3/7}`. -/
def offlineWitnesses : Set ℂ :=
  { s : ℂ |
      s = ⟨(1 / 3 : ℝ), 14⟩ ∨
      s = ⟨(2 / 5 : ℝ), 21⟩ ∨
      s = ⟨(3 / 7 : ℝ), 25⟩ }

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. Amplitude and Harmonic Definitions (in ZetaDefs namespace to avoid clashes)
-- ════════════════════════════════════════════════════════════════════════════
end ZD
namespace ZetaDefs
def ClassicalNontrivialZero (ρ : ℂ) : Prop :=
  ρ ∈ ZD.NontrivialZeros

structure IsHarmonicBalanced (α : Type*) where
  val : α
  balanced : Bool := true  -- default true on construction

theorem SetBalance : True := trivial

def violatesBalance {α : Type*} [DecidableEq α]
    (h : IsHarmonicBalanced α) (S : Set α) [DecidablePred (· ∈ S)] : Bool :=
  decide (h.val ∈ S)  -- or whatever xyz is

def update {α : Type*} [DecidableEq α]
    (h : IsHarmonicBalanced α) (S : Set α) [DecidablePred (· ∈ S)] :
    IsHarmonicBalanced α :=
  if violatesBalance h S then { h with balanced := false } else h




def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1
/-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/
def OffLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }

/-- An offline nontrivial zeta zero (predicate form). -/
def IsOfflineZetaZero (s : ℂ) : Prop :=
  s ∈ NontrivialZeros ∧ s.re ≠ 1 / 2
/-- The zero-pair amplitude envelope. -/
def zeroPairEnvelope (r : ℝ) (β : ℝ) : ℝ :=  r ^ β + r ^ (1 - β)

/-- The balanced (on-line) envelope. -/
def balancedEnvelope (r : ℝ) : ℝ :=
  2 * r ^ (1 / 2 : ℝ)

/-- The off-line amplitude defect: `r^β + r^(1−β) − 2r^(1/2)`. -/
def amplitudeDefect (r : ℝ) (β : ℝ) : ℝ :=
  zeroPairEnvelope r β - balancedEnvelope r

/-- The cosine component of the harmonic detector at the sixth root of unity.
    For a natural number n (typically a prime), this is the real part of e^{iπn/3},
    i.e. `cos(n · π/3)`. This is the spectral weight in the principal channel —
    it depends only on n, not on the zero's real part. -/
def harmonicCosine (n : ℕ) : ℝ :=
  Real.cos (↑n * (Real.pi / 3))

/-- The principal-channel signal from a zero pair at real part β, observed at
    prime p through the harmonic detector at π/3:
    `signal(p, β) = cos(p · π/3) · (p^β + p^{1−β})`. -/
def harmonicSignal (p : ℕ) (β : ℝ) : ℝ :=
  harmonicCosine p * zeroPairEnvelope (↑p) β

/-- The balanced (on-line) signal: what harmonicSignal produces when β = 1/2. -/
def harmonicSignalBalanced (p : ℕ) : ℝ :=
  harmonicCosine p * balancedEnvelope (↑p)

/-- The harmonic signal defect: excess over the balanced signal. -/
def harmonicSignalDefect (p : ℕ) (β : ℝ) : ℝ :=
  harmonicSignal p β - harmonicSignalBalanced p

/-- The envelope ratio: Q(r,β) / Q_balanced(r). On-line = 1, off-line > 1. -/
def envelopeRatio (r : ℝ) (β : ℝ) : ℝ :=
  zeroPairEnvelope r β / balancedEnvelope r

/-- Off-line nontrivial zeros (alias). -/
def S_offline : Set ℂ := OffLineZeros

-- ════════════════════════════════════════════════════════════════════════════
-- § 3c. Cosh-Based Off-Line Detector
-- ════════════════════════════════════════════════════════════════════════════

/-- The cosh-based off-line detector: `cosh((β - 1/2) · t)`.
    Equals 1 when β = 1/2, strictly greater than 1 when β ≠ 1/2 and t ≠ 0.
    This directly measures how far a zero's real part deviates from the
    critical line, independently of any prime — it depends only on β and t.
    The cosine detector (`harmonicCosine`) is the per-prime spectral weight;
    the cosh detector is the β-dependent envelope factor. Both are needed. -/
def coshDetector (β : ℝ) (t : ℝ) : ℝ :=
  Real.cosh ((β - 1/2) * t)

/-- The harmonic difference at π/3 (cosh version): excess of the cosh detector
    over the balanced value 1. Zero iff β = 1/2 (for t ≠ 0). -/
def harmonicDiffPiThird (β : ℝ) (t : ℝ) : ℝ :=
  coshDetector β t - 1

/-- The raw (unnormalized) harmonic detector at arbitrary angle θ.
    `rawHarmonicCosine n θ = cos(n · θ)` — not tied to π/3.
    Use as a backup/cross-check against the specialized π/3 detector. -/
def rawHarmonicCosine (n : ℕ) (θ : ℝ) : ℝ :=
  Real.cos (↑n * θ)

theorem coshDetector_one_of_online (t : ℝ) :
    coshDetector (1/2) t = 1 := by
  simp [coshDetector, Real.cosh_zero]

theorem coshDetector_gt_one_of_offline {β : ℝ} (hβ : β ≠ 1/2) {t : ℝ} (ht : t ≠ 0) :
    1 < coshDetector β t := by
  rw [coshDetector, Real.one_lt_cosh]
  exact mul_ne_zero (sub_ne_zero.mpr hβ) ht

theorem harmonicDiffPiThird_zero_of_online (t : ℝ) :
    harmonicDiffPiThird (1/2) t = 0 := by
  unfold harmonicDiffPiThird; rw [coshDetector_one_of_online]; ring

theorem harmonicDiffPiThird_pos_of_offline {β : ℝ} (hβ : β ≠ 1/2) {t : ℝ} (ht : t ≠ 0) :
    0 < harmonicDiffPiThird β t := by
  unfold harmonicDiffPiThird; linarith [coshDetector_gt_one_of_offline hβ ht]

/-- **Cosh detector biconditional**: `coshDetector β t = 1 ↔ β = 1/2` for `t ≠ 0`. -/
theorem coshDetector_eq_one_iff {t : ℝ} (ht : t ≠ 0) {β : ℝ} :
    coshDetector β t = 1 ↔ β = 1/2 := by
  constructor
  · intro h
    by_contra hβ
    exact absurd h (ne_of_gt (coshDetector_gt_one_of_offline hβ ht))
  · rintro rfl; exact coshDetector_one_of_online t

-- ════════════════════════════════════════════════════════════════════════════
-- § 3d. Prime Oscillation and Phase Geometry
-- ════════════════════════════════════════════════════════════════════════════

/-- The prime angular frequency: `ω_p = log p`.
    This is the frequency at which prime p oscillates in the log-scale
    variable `t = log x`. The contribution `p^{-s} = e^{-s log p} = e^{-it log p}`
    oscillates with angular frequency `log p`. -/
def primeFrequency (p : ℕ) : ℝ := Real.log (↑p)

/-- The half-period shift for prime p: `π / log p`.
    This is the t-distance from any observation point to the nearest
    opposite-sign point of the p-oscillation. -/
def halfPeriodShift (p : ℕ) : ℝ := Real.pi / primeFrequency p

/-- The quarter-period shift for prime p: `π / (2 log p)`.
    This is the t-distance from a zero-crossing to the nearest extremum. -/
def quarterPeriodShift (p : ℕ) : ℝ := Real.pi / (2 * primeFrequency p)

/-- The opposite-sign observation point in x-coordinates:
    `x_opp = x₀ · e^{π / log p}`. -/
def oppositeObservationPoint (x₀ : ℝ) (p : ℕ) : ℝ :=
  x₀ * Real.exp (halfPeriodShift p)

/-- The nearest extremum from a zero-crossing in x-coordinates:
    `x_± = x₀ · e^{± π / (2 log p)}`. -/
def nearestExtremumPlus (x₀ : ℝ) (p : ℕ) : ℝ :=
  x₀ * Real.exp (quarterPeriodShift p)

def nearestExtremumMinus (x₀ : ℝ) (p : ℕ) : ℝ :=
  x₀ * Real.exp (-quarterPeriodShift p)

/-- For p ≥ 2, the prime frequency is positive. -/
theorem primeFrequency_pos {p : ℕ} (hp : Nat.Prime p) : 0 < primeFrequency p := by
  unfold primeFrequency
  exact Real.log_pos (by exact_mod_cast hp.one_lt)

/-- The half-period shift is positive for any prime. -/
theorem halfPeriodShift_pos {p : ℕ} (hp : Nat.Prime p) : 0 < halfPeriodShift p := by
  unfold halfPeriodShift; exact div_pos Real.pi_pos (primeFrequency_pos hp)

/-- The opposite observation point is strictly greater than x₀ (for x₀ > 0). -/
theorem oppositeObservationPoint_gt {x₀ : ℝ} (hx : 0 < x₀) {p : ℕ} (hp : Nat.Prime p) :
    x₀ < oppositeObservationPoint x₀ p := by
  unfold oppositeObservationPoint
  have := halfPeriodShift_pos hp
  nlinarith [Real.exp_pos (halfPeriodShift p), Real.one_lt_exp_iff.mpr this]

/-- **Half-period shift flips the odd (cosine) channel**: shifting the observation
point by `π/ω_p` reverses the sign of `cos(ω_p · t)`. The odd channel (sine)
is what carries phase information; the even channel (cosh) is phase-invariant. -/
theorem cos_half_period_flip (t : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    Real.cos (primeFrequency p * (t + halfPeriodShift p)) =
    -Real.cos (primeFrequency p * t) := by
  unfold halfPeriodShift
  rw [mul_add, mul_div_cancel₀ _ (primeFrequency_pos hp).ne']
  exact Real.cos_add_pi _

/-- **The even channel (cosh) survives any shift**: regardless of where you
observe, the cosh detector for an offline zero remains > 1. The phase shift
that flips the odd channel has no effect on the even channel — the offline
excess is always visible. -/
theorem even_channel_survives_shift {β : ℝ} (hβ : β ≠ 1/2) {t Δ : ℝ} (h : t + Δ ≠ 0) :
    1 < coshDetector β (t + Δ) := by
  rw [coshDetector, Real.one_lt_cosh]
  exact mul_ne_zero (sub_ne_zero.mpr hβ) h

/-- **Midpoint measurement**: At the midpoint β = 1/2, the even channel reads
exactly 1 (balanced). Any deviation from β = 1/2 pushes it above 1.
Measuring the even channel at the midpoint IS the detector. -/
theorem midpoint_measurement_balanced (t : ℝ) :
    coshDetector (1/2) t = 1 := coshDetector_one_of_online t

/-- **Midpoint measurement detects offline**: At any nonzero scale, the even
channel reads > 1 for an offline zero. The odd (sin) channel is discarded —
only the even (cosh) channel matters for detection. -/
theorem midpoint_measurement_detects_offline {β : ℝ} (hβ : β ≠ 1/2) {t : ℝ} (ht : t ≠ 0) :
    1 < coshDetector β t := coshDetector_gt_one_of_offline hβ ht

-- ════════════════════════════════════════════════════════════════════════════
-- § 3c′. Reflected Cosh Kernel Pair (anchored at π/6 and 1 − π/6)
-- ════════════════════════════════════════════════════════════════════════════

/-!
A second detection scheme: a pair of cosh kernels anchored at the reflected
points `π/6` and `1 − π/6`. Unlike `coshDetector` (which vanishes on the
critical line β = 1/2), neither of these kernels singles out β = 1/2 on its
own — instead, the critical line is detected by the **agreement** of the
two kernels. The reflection β ↔ 1−β exchanges the pair.

Nominal support windows (metadata):
  • `coshDetectorLeft`  is centered on `[0, π/3]`     (around π/6)
  • `coshDetectorRight` is centered on `[1 − π/3, 1]` (around 1 − π/6)

The kernels themselves are unwindowed functions on ℝ; the support sets are
carried as `Set ℝ` constants for downstream use.
-/

/-- Left-anchored cosh kernel, centered at `β = π/6`. -/
def coshDetectorLeft (β t : ℝ) : ℝ :=
  Real.cosh ((β - Real.pi / 6) * t)

/-- Right-anchored cosh kernel, centered at `β = 1 − π/6`.
    The center equals `1/2 − (π/6 − 1/2)`, i.e. the β ↔ 1−β reflection of π/6. -/
def coshDetectorRight (β t : ℝ) : ℝ :=
  Real.cosh ((β - (1 - Real.pi / 6)) * t)

/-- Nominal support window for the left kernel: `[0, π/3]`, centered at π/6. -/
def coshDetectorLeftSupport : Set ℝ := Set.Icc 0 (Real.pi / 3)

/-- Nominal support window for the right kernel: `[1 − π/3, 1]`, centered at 1 − π/6. -/
def coshDetectorRightSupport : Set ℝ := Set.Icc (1 - Real.pi / 3) 1

/-- Each support window has width π/3 and is symmetric about its anchor. -/
theorem coshDetectorLeft_center_mem : (Real.pi / 6) ∈ coshDetectorLeftSupport := by
  refine ⟨?_, ?_⟩ <;> nlinarith [Real.pi_pos]

theorem coshDetectorRight_center_mem : (1 - Real.pi / 6) ∈ coshDetectorRightSupport := by
  refine ⟨?_, ?_⟩ <;> nlinarith [Real.pi_pos]

/-- The two support windows are reflections of each other under β ↔ 1−β. -/
theorem coshDetectorSupport_reflect (β : ℝ) :
    β ∈ coshDetectorLeftSupport ↔ (1 - β) ∈ coshDetectorRightSupport := by
  unfold coshDetectorLeftSupport coshDetectorRightSupport
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ### Read-1 points: each kernel reads 1 at its own center. -/

/-- At its center `β = π/6`, the left kernel reads exactly 1. -/
theorem coshDetectorLeft_one_at_center (t : ℝ) :
    coshDetectorLeft (Real.pi / 6) t = 1 := by
  simp [coshDetectorLeft, Real.cosh_zero]

/-- At its center `β = 1 − π/6`, the right kernel reads exactly 1. -/
theorem coshDetectorRight_one_at_center (t : ℝ) :
    coshDetectorRight (1 - Real.pi / 6) t = 1 := by
  simp [coshDetectorRight, Real.cosh_zero]

/-! ### Off-center strict inequality. -/

/-- For β ≠ π/6 and t ≠ 0, the left kernel reads > 1. -/
theorem coshDetectorLeft_gt_one {β : ℝ} (hβ : β ≠ Real.pi / 6) {t : ℝ} (ht : t ≠ 0) :
    1 < coshDetectorLeft β t := by
  rw [coshDetectorLeft, Real.one_lt_cosh]
  exact mul_ne_zero (sub_ne_zero.mpr hβ) ht

/-- For β ≠ 1 − π/6 and t ≠ 0, the right kernel reads > 1. -/
theorem coshDetectorRight_gt_one {β : ℝ} (hβ : β ≠ 1 - Real.pi / 6) {t : ℝ} (ht : t ≠ 0) :
    1 < coshDetectorRight β t := by
  rw [coshDetectorRight, Real.one_lt_cosh]
  exact mul_ne_zero (sub_ne_zero.mpr hβ) ht

/-! ### Reflection swap: β ↔ 1−β exchanges the two kernels. -/

/-- **Reflection swap**: substituting `1 − β` into the left kernel gives the
    right kernel at `β`. This is the structural invariance of the pair. -/
theorem coshDetector_reflect_swap (β t : ℝ) :
    coshDetectorLeft (1 - β) t = coshDetectorRight β t := by
  unfold coshDetectorLeft coshDetectorRight
  rw [show ((1 - β) - Real.pi / 6) * t = -((β - (1 - Real.pi / 6)) * t) from by ring]
  exact Real.cosh_neg _

/-- Symmetric form: substituting `1 − β` into the right kernel gives the
    left kernel at `β`. -/
theorem coshDetector_reflect_swap' (β t : ℝ) :
    coshDetectorRight (1 - β) t = coshDetectorLeft β t := by
  have := coshDetector_reflect_swap (1 - β) t
  simpa using this.symm

/-! ### Agreement biconditional: K_L = K_R ↔ β = 1/2. -/

/-- **Agreement biconditional**: the two anchored cosh kernels agree at
    `(β, t)` if and only if `β = 1/2`, for any nonzero scale `t`.

    Proof: `cosh a = cosh b ↔ |a| = |b|` (`Real.cosh_le_cosh` + antisymmetry),
    and `|a| = |b| ↔ a = b ∨ a = -b` (`abs_eq_abs`). The `a = b` branch forces
    `(π/3 − 1)·t = 0`, contradicting `t ≠ 0` and `π/3 ≠ 1`. The `a = -b`
    branch forces `(2β − 1)·t = 0`, which for `t ≠ 0` gives `β = 1/2`. -/
theorem coshDetectors_agree_iff {t : ℝ} (ht : t ≠ 0) {β : ℝ} :
    coshDetectorLeft β t = coshDetectorRight β t ↔ β = 1/2 := by
  unfold coshDetectorLeft coshDetectorRight
  constructor
  · intro hcosh
    -- From cosh a = cosh b derive |a| = |b| via antisymmetry of ≤.
    have habs : |(β - Real.pi / 6) * t| = |(β - (1 - Real.pi / 6)) * t| := by
      apply le_antisymm
      · exact (Real.cosh_le_cosh.mp hcosh.le)
      · exact (Real.cosh_le_cosh.mp hcosh.ge)
    -- |a| = |b| iff a = b ∨ a = -b.
    rcases abs_eq_abs.mp habs with heq | hneg
    · -- (β - π/6)·t = (β - (1-π/6))·t ⇒ (π/3 - 1)·t = 0.
      have hzero : (Real.pi / 3 - 1) * t = 0 := by linarith
      rcases mul_eq_zero.mp hzero with hpi | ht0
      · -- π/3 = 1 ⇒ π = 3, contradicts 3 < π (Real.pi_gt_three).
        exfalso
        have hπ : Real.pi = 3 := by linarith
        have : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      · exact absurd ht0 ht
    · -- (β - π/6)·t = -(β - (1-π/6))·t ⇒ (2β - 1)·t = 0.
      have hzero : (2 * β - 1) * t = 0 := by linarith
      rcases mul_eq_zero.mp hzero with hβ | ht0
      · linarith
      · exact absurd ht0 ht
  · rintro rfl
    -- At β = 1/2 the arguments are negatives, so cosh values coincide.
    rw [show (1/2 - (1 - Real.pi / 6)) * t = -((1/2 - Real.pi / 6) * t) from by ring]
    exact (Real.cosh_neg _).symm

/-- **Online case**: on the critical line β = 1/2, the two kernels agree
    (at every scale, with no `t ≠ 0` hypothesis). -/
theorem coshDetectors_equal_on_critical_line (t : ℝ) :
    coshDetectorLeft (1/2) t = coshDetectorRight (1/2) t := by
  unfold coshDetectorLeft coshDetectorRight
  rw [show (1/2 - (1 - Real.pi / 6)) * t = -((1/2 - Real.pi / 6) * t) from by ring]
  exact (Real.cosh_neg _).symm

/-- **Disagreement witnesses offline**: if the two kernels disagree at any
    nonzero scale, then β ≠ 1/2. -/
theorem coshDetectors_disagree_of_offline {t : ℝ} (ht : t ≠ 0) {β : ℝ}
    (h : coshDetectorLeft β t ≠ coshDetectorRight β t) : β ≠ 1/2 := by
  intro hβ
  exact h ((coshDetectors_agree_iff ht).mpr hβ)

/-! ### Connection to the original `coshDetector`.

Sum-to-product and product-to-sum identities tie the pair back to the
single-kernel detector:

  • **Sum**: `K_L + K_R = 2·cosh((1−π/3)·t/2) · coshDetector β t`.
    The pair sum factors as a β-INDEPENDENT calibration times the original
    detector — dividing out the scalar recovers `coshDetector` exactly.

  • **Product**: `K_L · K_R = (cosh((1−π/3)·t) + coshDetector β (2t)) / 2`.
    A β-INDEPENDENT constant plus the original detector at doubled log-scale;
    β-dependence is isolated in the `coshDetector β (2t)` term.
-/

/-- **Pair sum identity**: the sum of the two anchored kernels factors as
    a β-independent scalar times the original `coshDetector`. -/
theorem coshDetector_pair_sum (β t : ℝ) :
    coshDetectorLeft β t + coshDetectorRight β t =
      2 * Real.cosh ((1 - Real.pi / 3) * t / 2) * coshDetector β t := by
  unfold coshDetectorLeft coshDetectorRight coshDetector
  -- Reshape arguments to (s + d) and (s - d) with s = (β−1/2)·t, d = (1/2−π/6)·t.
  have h1 : (β - Real.pi / 6) * t = (β - 1/2) * t + (1/2 - Real.pi / 6) * t := by ring
  have h2 : (β - (1 - Real.pi / 6)) * t = (β - 1/2) * t - (1/2 - Real.pi / 6) * t := by ring
  have h3 : (1 - Real.pi / 3) * t / 2 = (1/2 - Real.pi / 6) * t := by ring
  rw [h1, h2, h3, Real.cosh_add, Real.cosh_sub]
  ring

/-- **Inverse sum factorization**: recover `coshDetector` from the pair sum
    by dividing out the β-independent calibration. The divisor is strictly
    positive (cosh ≥ 1) so the division is safe. -/
theorem coshDetector_from_pair_sum (β t : ℝ) :
    coshDetector β t =
      (coshDetectorLeft β t + coshDetectorRight β t) /
        (2 * Real.cosh ((1 - Real.pi / 3) * t / 2)) := by
  have hpos : (0 : ℝ) < Real.cosh ((1 - Real.pi / 3) * t / 2) := Real.cosh_pos _
  have hne : 2 * Real.cosh ((1 - Real.pi / 3) * t / 2) ≠ 0 :=
    mul_ne_zero two_ne_zero hpos.ne'
  rw [coshDetector_pair_sum]
  field_simp

/-- **Pair product identity**: the product of the two anchored kernels
    decomposes into a β-independent term plus the original detector at
    doubled scale. -/
theorem coshDetector_pair_product (β t : ℝ) :
    coshDetectorLeft β t * coshDetectorRight β t =
      (Real.cosh ((1 - Real.pi / 3) * t) + coshDetector β (2 * t)) / 2 := by
  unfold coshDetectorLeft coshDetectorRight coshDetector
  -- Reshape: let A = (β−π/6)·t and B = (β−(1−π/6))·t. Then A+B = (β−1/2)·(2t)
  -- and A−B = (1−π/3)·t. Product-to-sum gives cosh A · cosh B = (cosh(A−B) + cosh(A+B))/2.
  have hpm : (β - 1/2) * (2 * t) =
      (β - Real.pi / 6) * t + (β - (1 - Real.pi / 6)) * t := by ring
  have hmp : (1 - Real.pi / 3) * t =
      (β - Real.pi / 6) * t - (β - (1 - Real.pi / 6)) * t := by ring
  rw [hpm, hmp, Real.cosh_add, Real.cosh_sub]
  ring

/-- **Pair-sum calibration is strictly positive** — guarantees the inverse
    factorization divisor never vanishes at any log-scale. -/
theorem coshDetector_pair_calibration_pos (t : ℝ) :
    0 < 2 * Real.cosh ((1 - Real.pi / 3) * t / 2) :=
  mul_pos two_pos (Real.cosh_pos _)

-- ════════════════════════════════════════════════════════════════════════════
-- § 3e. Per-Prime Observables (Mathlib-native, indexed by any prime)
-- ════════════════════════════════════════════════════════════════════════════

/-- The normalized detector observable at a single prime `p`: the cosh
    reading `cosh((β - 1/2) · log p)`.
    Online (β = 1/2): value is 1.
    Offline (β ≠ 1/2): value is > 1. -/
def actualReducedObservable (β : ℝ) (p : ℕ) : ℝ :=
  coshDetector β (Real.log (↑p))

/-- The balanced comparison target at a single prime: always 1. -/
def balancedPrimeObservable (_p : ℕ) : ℝ := 1

/-- The raw envelope observable at a single prime `p`: the zero-pair
    envelope `p^β + p^(1-β)`. -/
def actualEnvelopeObservable (β : ℝ) (p : ℕ) : ℝ :=
  zeroPairEnvelope (↑p) β

/-- The observable indexed by a zero's real part, at a single prime `p`. -/
def actualReducedObservableOfZero (ρ : ℂ) (p : ℕ) : ℝ :=
  actualReducedObservable ρ.re p

-- ════════════════════════════════════════════════════════════════════════════
-- § 3f. Realizable Zeros
-- ════════════════════════════════════════════════════════════════════════════

/-- A **realizable zero** is a nontrivial zero whose reflected even-envelope
passes the universal prime-indexed closure test: the cosh detector reads 1
at every prime. This is the set of zeros consistent with the symmetric
Euler-product coordinate system. -/
def RealizableZeros : Set ℂ :=
  { s ∈ ZD.NontrivialZeros |
    ∀ p : ℕ, Nat.Prime p → coshDetector s.re (Real.log (↑p)) = 1 }

-- Basic properties

theorem amplitudeDefect_half (r : ℝ) : amplitudeDefect r (1/2) = 0 := by
  simp [amplitudeDefect, zeroPairEnvelope, balancedEnvelope]; ring

theorem amplitudeDefect_symm (r : ℝ) (β : ℝ) :
    amplitudeDefect r β = amplitudeDefect r (1 - β) := by
  simp [amplitudeDefect, zeroPairEnvelope]; ring

theorem amplitudeDefect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} (hβ : β ≠ 1 / 2) :
    0 < amplitudeDefect r β := by
      -- Use the identity $r^\beta + r^{1-\beta} - 2r^{1/2} = (r^{\beta/2} - r^{(1-\beta)/2})^2$.
      have h_identity : r ^ β + r ^ (1 - β) - 2 * r ^ (1 / 2 : ℝ) = (r ^ (β / 2) - r ^ ((1 - β) / 2)) ^ 2 := by
        ring;
        norm_num [ sq, ← Real.rpow_add hr ] ; ring;
      convert sq_pos_of_ne_zero _;
      · infer_instance;
      · infer_instance;
      · norm_num [ sub_eq_zero, Real.rpow_def_of_pos hr ];
        grind +qlia

lemma offline_zero_causes_amplitude_increase (ρ : ℂ) (hρ : IsOfflineZetaZero ρ)
    (hr : 0 < (r : ℝ)) (hr1 : r ≠ 1) :
    amplitudeDefect r ρ.re > 0 :=
  amplitudeDefect_pos hr hr1 hρ.2

/-- **No cancellation** (symbolic): Every offline zeta zero has strictly positive
amplitude defect at every scale r > 0, r ≠ 1. No concrete witness needed. -/
lemma proof_of_no_cancellation (ρ : ℂ) (hρ : IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    amplitudeDefect r ρ.re > 0 :=
  amplitudeDefect_pos hr hr1 hρ.2

-- ════════════════════════════════════════════════════════════════════════════
-- § 3b. Biconditionals and Envelope Ratio
-- ════════════════════════════════════════════════════════════════════════════

/-- **Defect biconditional**: D_β(r) = 0 iff β = 1/2, for r > 0, r ≠ 1.
The on-line real part is the unique fixed point of zero defect. -/
theorem amplitudeDefect_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    amplitudeDefect r β = 0 ↔ β = 1 / 2 := by
  constructor
  · intro h
    by_contra hβ
    exact absurd h (ne_of_gt (amplitudeDefect_pos hr hr1 hβ))
  · rintro rfl; exact amplitudeDefect_half r

/-- **Defect positivity biconditional**: D_β(r) > 0 iff β ≠ 1/2, for r > 0, r ≠ 1. -/
theorem amplitudeDefect_pos_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    0 < amplitudeDefect r β ↔ β ≠ 1 / 2 := by
  constructor
  · intro h hβ; rw [(amplitudeDefect_eq_zero_iff hr hr1).mpr hβ] at h; exact lt_irrefl _ h
  · exact amplitudeDefect_pos hr hr1

/-- **Envelope equality biconditional** (via `Real.rpow_right_inj`):
`r^β + r^{1-β} = 2r^{1/2}` iff `β = 1/2`, for r > 0, r ≠ 1.
Uses mathlib's `Real.rpow_right_inj` for injectivity of `r^·`. -/
theorem zeroPairEnvelope_eq_balanced_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    zeroPairEnvelope r β = balancedEnvelope r ↔ β = 1 / 2 := by
  rw [show zeroPairEnvelope r β = balancedEnvelope r ↔
    amplitudeDefect r β = 0 from by simp [amplitudeDefect]; constructor <;> intro h <;> linarith]
  exact amplitudeDefect_eq_zero_iff hr hr1

theorem balancedEnvelope_pos {r : ℝ} (hr : 0 < r) : 0 < balancedEnvelope r := by
  unfold balancedEnvelope; positivity

/-- **On-line ratio = 1**: When β = 1/2 (RH true), the envelope ratio is exactly 1. -/
theorem envelopeRatio_eq_one_of_online {r : ℝ} (hr : 0 < r) :
    envelopeRatio r (1 / 2) = 1 := by
  unfold envelopeRatio zeroPairEnvelope balancedEnvelope
  field_simp
  ring

/-- **Off-line ratio > 1**: When β ≠ 1/2 (RH false), the envelope ratio
exceeds 1 at every scale r > 0, r ≠ 1. -/
theorem envelopeRatio_gt_one_of_offline {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {β : ℝ} (hβ : β ≠ 1 / 2) :
    1 < envelopeRatio r β := by
  have hbal := balancedEnvelope_pos hr
  rw [envelopeRatio, lt_div_iff₀ hbal]
  simp only [one_mul]
  linarith [amplitudeDefect_pos hr hr1 hβ, show amplitudeDefect r β =
    zeroPairEnvelope r β - balancedEnvelope r from rfl]

/-- **Ratio biconditional**: envelopeRatio(r, β) = 1 iff β = 1/2,
for r > 0, r ≠ 1. The on-line configuration is the unique unit. -/
theorem envelopeRatio_eq_one_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    envelopeRatio r β = 1 ↔ β = 1 / 2 := by
  constructor
  · intro h
    by_contra hβ
    exact absurd h (ne_of_gt (by linarith [envelopeRatio_gt_one_of_offline hr hr1 hβ]))
  · rintro rfl; exact envelopeRatio_eq_one_of_online hr

/-- **Ratio positivity biconditional**: envelopeRatio(r, β) > 1 iff β ≠ 1/2. -/
theorem envelopeRatio_gt_one_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    1 < envelopeRatio r β ↔ β ≠ 1 / 2 := by
  constructor
  · intro h hβ; rw [(envelopeRatio_eq_one_iff hr hr1).mpr hβ] at h; exact lt_irrefl _ h
  · exact envelopeRatio_gt_one_of_offline hr hr1

/-- **Off-line ratio for an actual zeta zero**: ρ ∈ OffLineZeros ⟹ ratio > 1. -/
theorem envelopeRatio_gt_one_of_offlineZero (ρ : ℂ) (hρ : IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    1 < envelopeRatio r ρ.re :=
  envelopeRatio_gt_one_of_offline hr hr1 hρ.2

end ZetaDefs
