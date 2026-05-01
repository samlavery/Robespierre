/-
# RH Assumption Methods

Definitions and lemmas for the prime harmonic system at π/3
that assume the Riemann Hypothesis or GRH.

We use Mathlib's `riemannZeta` and `RiemannHypothesis` to define
the set of nontrivial zeta zeros and the RH-faithful envelope process.
-/

import Mathlib
import RequestProject.INDRHIndependentMethods

open Real BigOperators

noncomputable section

/-! ## GRH Balance Hypothesis -/

/-- **GRH mod-6 balance hypothesis**: Under GRH for L(s,χ₃), the character
    sum ∑_{p≤N} χ₃(p) is O(√N log N). This controls the nonprincipal
    (imaginary) channel of the prime harmonic invariant Q. -/
def GRH_mod6_balance : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.sin (↑p * Real.pi / 3))| ≤ C * Real.sqrt N * Real.log N

/-- Under GRH, the imaginary part of the Q partial sum is bounded. -/
theorem grh_implies_imaginary_bound (hGRH : GRH_mod6_balance) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
        (fun p => Real.sin (↑p * Real.pi / 3))| ≤ C * Real.sqrt N * Real.log N :=
  hGRH

/-! ## Nontrivial Zeta Zeros — Using Mathlib's riemannZeta

We define the set of nontrivial zeros using Mathlib's `riemannZeta`.
A nontrivial zero is ρ ∈ ℂ with ζ(ρ) = 0, 0 < Re(ρ) < 1.
(Trivial zeros are at s = -2n, n ≥ 1, which have Re(s) < 0.)
-/

/-- A **nontrivial zeta zero** is a complex number ρ in the critical strip
    (0 < Re(ρ) < 1) where Mathlib's `riemannZeta` vanishes. -/
def IsNontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The **set of nontrivial zeta zeros** as a subset of ℂ. -/
def NontrivialZetaZeros : Set ℂ :=
  { ρ : ℂ | IsNontrivialZetaZero ρ }

/-- Under Mathlib's `RiemannHypothesis`, every nontrivial zero has Re(ρ) = 1/2. -/
theorem rh_implies_critical_line (hRH : RiemannHypothesis)
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) : ρ.re = 1 / 2 := by
  obtain ⟨h_zero, h_re_pos, h_re_lt⟩ := hρ
  apply hRH ρ h_zero
  · rintro ⟨n, hn⟩
    have : ρ.re = (-2 * ((n : ℂ) + 1)).re := by rw [← hn]
    simp at this
    linarith
  · intro he
    rw [he] at h_re_lt
    simp at h_re_lt

/-! ## RH-Faithful Envelope Process

Under the Riemann Hypothesis, each nontrivial zero ρ has Re(ρ) = β = 1/2.
The zero-pair envelope has two sides:
  - Left side:  r^β      = r^(1/2)
  - Right side: r^(1-β)  = r^(1/2)

Both sides are equal, and the AM-GM defect vanishes:
  D_β(r) = r^β + r^(1-β) - 2·r^(1/2) = 0

This section makes this process explicit for each RH method.
-/

/-- The **left envelope side** at a zero with real part β: r^β. -/
def envelopeSideLeft (r β : ℝ) : ℝ := r ^ β

/-- The **right envelope side** at a zero with real part β: r^(1-β). -/
def envelopeSideRight (r β : ℝ) : ℝ := r ^ (1 - β)

/-- Under RH, β = 1/2, so the left envelope side is r^(1/2). -/
theorem envelopeSideLeft_under_RH (r : ℝ) :
    envelopeSideLeft r (1/2) = r ^ (1/2 : ℝ) := rfl

/-- Under RH, β = 1/2, so the right envelope side is also r^(1/2). -/
theorem envelopeSideRight_under_RH (r : ℝ) :
    envelopeSideRight r (1/2) = r ^ (1/2 : ℝ) := by
  unfold envelopeSideRight; norm_num

/-- Under RH, both envelope sides are equal. -/
theorem envelope_sides_equal_under_RH (r : ℝ) :
    envelopeSideLeft r (1/2) = envelopeSideRight r (1/2) := by
  rw [envelopeSideLeft_under_RH, envelopeSideRight_under_RH]

/-- The **AM-GM excess amplitude** from a zero-pair with real part β:
    D_β(r) = r^β + r^(1-β) - 2·r^(1/2). This is ≥ 0 by AM-GM. -/
def excessAmplitude (r β : ℝ) : ℝ :=
  envelopeSideLeft r β + envelopeSideRight r β - 2 * r ^ (1/2 : ℝ)

/-- Under RH (β = 1/2), the excess amplitude vanishes. -/
theorem excessAmplitude_zero_under_RH (r : ℝ) :
    excessAmplitude r (1/2) = 0 := by
  unfold excessAmplitude envelopeSideLeft envelopeSideRight
  norm_num; ring

/-- For any nontrivial zero ρ, if RH holds, the excess amplitude at r is 0. -/
theorem excessAmplitude_zero_for_RH_zero (hRH : RiemannHypothesis)
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    excessAmplitude r ρ.re = 0 := by
  have hβ : ρ.re = 1 / 2 := rh_implies_critical_line hRH ρ hρ
  rw [hβ]
  exact excessAmplitude_zero_under_RH r

/-! ## RH-Faithful Amplitude Pipeline

The pipeline for each RH method:
1. Compute the pre-normalized cosine amplitude: cos(pπ/3) = 1/2
2. Compute envelope sides: r^β and r^(1-β) with β = 1/2
3. Compute AM-GM excess: r^β + r^(1-β) - 2r^(1/2) = 0
4. Add excess to pre-normalized amplitude: 1/2 + 0 = 1/2
5. Normalize by dividing by |Q| = 1: (1/2) / 1 = 1/2

The result is unchanged, confirming faithfulness to RH.
-/

/-- The **pre-normalized cosine amplitude** for admissible primes: cos(pπ/3). -/
def preNormalizedCosAmplitude (p : ℕ) : ℝ := Real.cos (↑p * Real.pi / 3)

/-- The **RH-faithful amplitude**: pre-normalized amplitude + excess amplitude,
    normalized by dividing by the Q-norm (= 1).
    Under RH, excess = 0, so the result is cos(pπ/3) / 1 = cos(pπ/3). -/
def rhFaithfulAmplitude (p : ℕ) (β : ℝ) (r : ℝ) : ℝ :=
  (preNormalizedCosAmplitude p + excessAmplitude r β) / 1

/-- Under RH (β = 1/2), the RH-faithful amplitude equals the raw cosine amplitude. -/
theorem rhFaithfulAmplitude_under_RH (p : ℕ) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = preNormalizedCosAmplitude p := by
  unfold rhFaithfulAmplitude
  have : excessAmplitude r (1/2) = 0 := excessAmplitude_zero_under_RH r
  rw [this]; ring

/-- For admissible primes, the RH-faithful amplitude equals 1/2. -/
theorem rhFaithfulAmplitude_val (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = 1 / 2 := by
  rw [rhFaithfulAmplitude_under_RH]
  exact cos_prime_pi_div_three p hp hp5

end
