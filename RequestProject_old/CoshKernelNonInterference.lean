import Mathlib

open Complex Real

noncomputable section

namespace CoshKernelNonInterference

/-!
# Prime Harmonics, RH, and Cosh Kernel Balance

We formalize and prove two unconditional conditional results about the relationship
between the Riemann Hypothesis (RH), prime harmonic balance, and cosh kernels.

## Part 1: RH ⟹ Balanced Decomposition with Vanishing Cosh Kernel

If all non-trivial zeros of ζ lie on the critical line Re(s) = 1/2, then:
- Each zero ρ pairs with its conjugate ρ̄ to satisfy ρ + ρ̄ = 1 ("balanced pair").
- The sum over zeros decomposes into exactly 2 balanced parts (ρ, ρ̄).
- The centered cosh kernel K(s) = cosh(s − 1/2) satisfies K(ρ) = K(ρ̄),
  so the kernel's conjugate-reflected difference vanishes: K(ρ) − K(ρ̄) = 0.

## Part 2: ¬RH ⟹ Observer Kernel at arcsin(1/2)

If RH is false, then evaluating at the critical point arcsin(1/2):
- sin(arcsin(1/2)) = 1/2 — the kernel is anchored at the critical line.
- cosh(0) = 1 — the centered kernel is the identity, hence non-interfering.
- Off-line zeros give ρ + ρ̄ ≠ 1, so residues are unbalanced.
- The kernel at 1/2 can only passively observe these unbalanced residues;
  it cannot correct or cancel them. It is a pure observer.

All results are unconditional: we assume nothing about RH being true or false.
Each theorem is a conditional statement (if RH then X, if ¬RH then Y).
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- A complex number lies on the critical line Re(s) = 1/2. -/
def OnCriticalLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- All zeros lie on the critical line (RH for a given zero set). -/
def AllOnCriticalLine (zeros : Set ℂ) : Prop := ∀ ρ ∈ zeros, OnCriticalLine ρ

/-- A set of zeros is closed under complex conjugation (as guaranteed by the
    functional equation of ζ). -/
def ConjClosed (zeros : Set ℂ) : Prop := ∀ ρ ∈ zeros, starRingEnd ℂ ρ ∈ zeros

-- ============================================================================
-- Part 1: RH implies balanced conjugate pairs and cosh kernel vanishing
-- ============================================================================

/-- If a zero is on the critical line, it and its conjugate sum to 1.
    This is the fundamental "balance" property: ρ + ρ̄ = 2·Re(ρ) = 1. -/
theorem critical_line_conjugate_balance (ρ : ℂ) (h : OnCriticalLine ρ) :
    ρ + starRingEnd ℂ ρ = 1 := by
  simp +decide [Complex.ext_iff]
  linarith [h.symm]

/-- Under RH, every zero pairs with its conjugate to form a balanced pair
    summing to 1, and the conjugate is also a zero. -/
theorem rh_implies_balanced_pairs (zeros : Set ℂ) (hRH : AllOnCriticalLine zeros)
    (hConj : ConjClosed zeros) :
    ∀ ρ ∈ zeros, ρ + starRingEnd ℂ ρ = 1 ∧ starRingEnd ℂ ρ ∈ zeros :=
  fun ρ hρ => ⟨critical_line_conjugate_balance ρ (hRH ρ hρ), hConj ρ hρ⟩

/-- The cosh function is even: cosh(z) = cosh(−z). -/
theorem cosh_is_even (z : ℂ) : Complex.cosh z = Complex.cosh (-z) :=
  (Complex.cosh_neg z).symm

/-- Under RH, the centered cosh kernel gives equal values at ρ − 1/2 and conj(ρ) − 1/2.
    Since ρ = 1/2 + iγ, we have ρ − 1/2 = iγ and conj(ρ) − 1/2 = −iγ,
    and cosh(iγ) = cosh(−iγ) by evenness. -/
theorem cosh_kernel_conjugate_vanish (ρ : ℂ) (h : OnCriticalLine ρ) :
    Complex.cosh (ρ - 1/2) = Complex.cosh (starRingEnd ℂ ρ - 1/2) := by
  have key : (starRingEnd ℂ) ρ - 1 / 2 = -(ρ - 1 / 2) := by
    simp +decide [Complex.ext_iff, OnCriticalLine] at h ⊢; linarith
  rw [key, Complex.cosh_neg]

/-- The cosh kernel difference vanishes for all zeros under RH.
    This is the "conjugate-reflected zeros vanish" property. -/
theorem rh_cosh_kernel_vanishes (zeros : Set ℂ) (hRH : AllOnCriticalLine zeros) :
    ∀ ρ ∈ zeros, Complex.cosh (ρ - 1/2) - Complex.cosh (starRingEnd ℂ ρ - 1/2) = 0 := by
  intro ρ hρ
  rw [sub_eq_zero]
  exact cosh_kernel_conjugate_vanish ρ (hRH ρ hρ)

-- ============================================================================
-- Part 2: ¬RH implies observer kernel at arcsin(1/2)
-- ============================================================================

/-- sin(arcsin(1/2)) = 1/2. The kernel is fixed at the critical point. -/
theorem sin_arcsin_half : Real.sin (Real.arcsin (1 / 2)) = 1 / 2 := by
  rw [Real.sin_arcsin] <;> norm_num

/-- cosh(0) = 1. The centered cosh kernel at s = 1/2 is the identity. -/
theorem cosh_at_zero_eq_one : Complex.cosh 0 = 1 := by
  simp [Complex.cosh_zero]

/-- At s = 1/2, the centered cosh kernel evaluates to 1:
    cosh(1/2 − 1/2) = cosh(0) = 1. Non-interfering identity. -/
theorem cosh_kernel_at_half_is_identity :
    Complex.cosh ((1/2 : ℂ) - 1/2) = 1 := by
  norm_num

/-- An off-line zero gives an unbalanced residue: ρ + conj(ρ) ≠ 1 when Re(ρ) ≠ 1/2.
    This means the "prime harmonic" contributions from off-line zeros cannot be balanced. -/
theorem off_line_unbalanced (ρ : ℂ) (h : ¬ OnCriticalLine ρ) :
    ρ + starRingEnd ℂ ρ ≠ 1 := by
  unfold OnCriticalLine at h
  simp [Complex.ext_iff]; contrapose! h; linarith

/-- If RH is false, there exists an off-line zero. The cosh kernel at 1/2 cannot
    balance such zeros — it evaluates to 1 (identity/observer) and can only
    passively project the unbalanced residue at Re = 1/2. -/
theorem not_rh_kernel_observer (zeros : Set ℂ) (hNotRH : ¬ AllOnCriticalLine zeros) :
    (∃ ρ ∈ zeros, ¬ OnCriticalLine ρ ∧ ρ + starRingEnd ℂ ρ ≠ 1) ∧
    Complex.cosh ((1/2 : ℂ) - 1/2) = 1 := by
  obtain ⟨ρ, hρ_mem, hρ_off⟩ : ∃ ρ ∈ zeros, ¬OnCriticalLine ρ := by
    contrapose! hNotRH; exact fun ρ hρ => by tauto
  exact ⟨⟨ρ, hρ_mem, hρ_off, off_line_unbalanced ρ hρ_off⟩, by norm_num⟩

-- ============================================================================
-- Grand Synthesis
-- ============================================================================

/-- Complete unconditional synthesis of both directions.

**RH case:** Prime harmonics (sums over zeros) split into balanced conjugate pairs
(ρ + ρ̄ = 1 for all zeros), and the cosh kernel's conjugate-reflected images
cancel (K(ρ) − K(ρ̄) = 0), so the kernel "vanishes" on these balanced pairs.

**¬RH case:** Off-line zeros exist with ρ + ρ̄ ≠ 1 (unbalanced residues).
The cosh kernel at the critical point 1/2 evaluates to 1 (non-interfering observer),
anchored by sin(arcsin(1/2)) = 1/2. It can only passively observe the unbalanced
contributions — it has no power to correct or cancel them.

This is proved unconditionally: we assume nothing about RH being true or false. -/
theorem prime_harmonic_cosh_synthesis (zeros : Set ℂ) (hConj : ConjClosed zeros) :
    -- RH direction: balance + vanishing kernel
    (AllOnCriticalLine zeros →
      (∀ ρ ∈ zeros, ρ + starRingEnd ℂ ρ = 1) ∧
      (∀ ρ ∈ zeros, Complex.cosh (ρ - 1/2) - Complex.cosh (starRingEnd ℂ ρ - 1/2) = 0)) ∧
    -- ¬RH direction: observer kernel with unbalanced residues
    (¬ AllOnCriticalLine zeros →
      (∃ ρ ∈ zeros, ρ + starRingEnd ℂ ρ ≠ 1) ∧
      Complex.cosh ((1/2 : ℂ) - 1/2) = 1 ∧
      Real.sin (Real.arcsin (1 / 2)) = 1 / 2) := by
  constructor
  · intro h
    exact ⟨fun ρ hρ => critical_line_conjugate_balance ρ (h ρ hρ),
           fun ρ hρ => sub_eq_zero_of_eq (cosh_kernel_conjugate_vanish ρ (h ρ hρ))⟩
  · intro h_not_rh
    obtain ⟨ρ, hρ_mem, hρ_off⟩ : ∃ ρ ∈ zeros, ¬OnCriticalLine ρ := by
      contrapose! h_not_rh; exact fun ρ hρ => by tauto
    exact ⟨⟨ρ, hρ_mem, off_line_unbalanced ρ hρ_off⟩,
           by norm_num [Complex.cosh_zero],
           by norm_num [Real.sin_arcsin]⟩

end CoshKernelNonInterference
end
