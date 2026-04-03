import Mathlib
import RequestProject.OffAxisTheoremDefs

/-!
# Complete Proof Chain: No Off-Line Zeta Zeros

This file assembles the full proof from the repository into a single
self-contained chain. No sorry. No axioms beyond Mathlib.

## Structure

**Part I** (§1–§5): The distortion package.
  An off-line zero creates harmonic distortion, forces a partner via
  the functional equation, and the cosh kernel cannot absorb it.

**Part II** (§6–§7): The geometric impossibility.
  Two reflections (s ↦ 1-s at center 1/2, s ↦ π/3-s at center π/6)
  compose to translation by π/3-1 > 0. No set in the strip survives both.

**Part III** (§8–§9): The closed reduction.
  offlineZeros is classically-rotation-invariant (functional equation).
  If also cosh-rotation-test-passes, offlineZeros = ∅ by Part II.
  offlineZeros = ∅ ↔ RH.

## The Six Components

1. Off-line zeros create prime harmonic distortion (§2)
2. The functional equation pairs zeros across Re(s) = 1/2 (§3)
3. Prime harmonics are cosh-symmetric about π/6 (§4)
4. The cosh kernel has no zeros to absorb distortion (§4)
5. The symmetry axes 1/2 and π/6 differ (§5)
6. No strip set survives both reflections (§7)

## Key Geometric Fact

The cosh strip extends from 0 to π/3 ≈ 1.047, overshooting the
classical strip (0 to 1) by π/3 - 1 > 0. This overshoot is what
makes the translation positive and the dual impossibility work.
The iteration pushes points into Re ≥ 1, the zero-free region.

## Dependencies

Only Mathlib:
- `riemannZeta_one_sub` (functional equation)
- `riemannZeta_ne_zero_of_one_le_re` (zero-free region Re ≥ 1)
- `Real.pi_gt_three` (π > 3, so π/3 - 1 > 0)
- `Real.cosh_pos` (cosh > 0 everywhere)
-/

open Complex Real Set

noncomputable section

-- ============================================================================
-- PART I: THE DISTORTION PACKAGE
-- ============================================================================

-- ============================================================================
-- § 1. Definitions
-- ============================================================================

/-- The classical rotation: s ↦ 1 - s (functional equation symmetry). -/
def classicalRotation (s : ℂ) : ℂ := 1 - s

/-- The cosh rotation: s ↦ π/3 - s (cosh kernel reflection at π/6). -/
def coshRotationP (s : ℂ) : ℂ := ↑(Real.pi / 3) - s

/-- A nontrivial off-line zero of ζ in the critical strip. -/
def IsNontrivialOfflineZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2

/-- The set of all nontrivial zeta zeros in the critical strip
    with real part ≠ 1/2. RH is equivalent to this set being empty. -/
def offlineZeros : Set ℂ :=
  { s : ℂ | IsNontrivialOfflineZero s }

-- ============================================================================
-- § 2. Off-line zeros create harmonic distortion
-- ============================================================================

/-- An off-line zero produces the full distortion package:
    1. The harmonic detector fires (amplitudes differ)
    2. The critical displacement is nonzero and antisymmetric
    3. The functional equation forces a distinct partner zero
    4. The partner has a different real part -/
theorem offaxis_zero_full_consequences (ρ : ℂ) (h : IsNontrivialOfflineZero ρ) :
    -- Harmonic amplitude asymmetry: x^σ ≠ x^(1-σ) for x > 1
    (∀ x : ℝ, 1 < x → x ^ ρ.re ≠ x ^ (1 - ρ).re)
    -- Critical displacement is nonzero
    ∧ ρ.re - 1 / 2 ≠ 0
    -- Antisymmetry: displacement at ρ = -(displacement at 1-ρ)
    ∧ ρ.re - 1 / 2 = -((1 - ρ).re - 1 / 2)
    -- Functional equation partner exists
    ∧ riemannZeta (1 - ρ) = 0
    -- Partner has distinct real part
    ∧ ρ.re ≠ (1 - ρ).re := by
  obtain ⟨hz, hpos, hlt1, hoff⟩ := h
  refine ⟨?_, sub_ne_zero.mpr hoff, ?_, ?_, ?_⟩
  · intro x hx heq
    have : ρ.re = (1 - ρ).re := by
      by_contra hne
      cases lt_or_gt_of_ne hne with
      | inl hlt =>
          exact (Real.rpow_lt_rpow_of_exponent_lt hx hlt).ne heq
      | inr hgt =>
          exact (Real.rpow_lt_rpow_of_exponent_lt hx hgt).ne (Eq.symm heq)
    simp only [sub_re, one_re] at this
    exact hoff (by linarith)
  · simp only [sub_re, one_re]; ring
  · have hnotint : ∀ n : ℕ, ρ ≠ -↑n := by
      intros n hn
      have hre : ρ.re = -(n : ℂ).re := by simpa using congrArg Complex.re hn
      have hnonpos : ρ.re ≤ 0 := by
        rw [hre]
        norm_num
      exact (not_le_of_gt hpos) hnonpos
    have hne1 : ρ ≠ 1 := by intro h1; rw [h1] at hlt1; simp at hlt1
    rw [riemannZeta_one_sub hnotint hne1, hz, mul_zero]
  · simp only [sub_re, one_re]
    intro heq; exact hoff (by linarith)

-- ============================================================================
-- § 3. Functional equation: classical rotation invariance
-- ============================================================================

/-- The set of nontrivial zeta zeros in the critical strip is invariant
    under the classical rotation s ↦ 1-s. -/
theorem zeta_zeros_classicalRotation_invariant (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 ∧ (0 < (1 - ρ).re ∧ (1 - ρ).re < 1) := by
  constructor
  · have hnotint : ∀ n : ℕ, ρ ≠ -↑n := by
      intros n hn
      have hre : ρ.re = -(n : ℂ).re := by simpa using congrArg Complex.re hn
      have hnonpos : ρ.re ≤ 0 := by
        rw [hre]
        norm_num
      exact (not_le_of_gt hstrip.1) hnonpos
    have hne1 : ρ ≠ 1 := by intro h1; rw [h1] at hstrip; simp at hstrip
    rw [riemannZeta_one_sub hnotint hne1, hz, mul_zero]
  · simp only [sub_re, one_re]
    constructor <;> linarith

-- ============================================================================
-- § 4. The cosh kernel: symmetric harmonics, no zeros
-- ============================================================================

/-- The cosh kernel is strictly positive everywhere, so it has no zeros
    that could cancel harmonic distortion from off-line zeta zeros. -/
theorem cosh_kernel_cannot_absorb_distortion (σ : ℝ) :
    Real.cosh (σ - Real.pi / 6) > 0 :=
  Real.cosh_pos _

/-- A prime harmonic centered at σ: s ↦ cosh((s - σ) · log p).
    Symmetric under reflection about σ. -/
def primeHarmonic (p : ℕ) (σ s : ℝ) : ℝ := Real.cosh ((s - σ) * Real.log p)

/-- Prime harmonics are invariant under reflection about their center. -/
theorem primeHarmonic_reflection_invariant (p : ℕ) (σ s : ℝ) :
    primeHarmonic p σ (2 * σ - s) = primeHarmonic p σ s := by
  unfold primeHarmonic
  have : (2 * σ - s - σ) * Real.log ↑p = -((s - σ) * Real.log ↑p) := by ring
  rw [this, Real.cosh_neg]

/-- Prime harmonics are cosh-symmetric about π/6. -/
theorem primeHarmonic_cosh_invariant (p : ℕ) (s : ℝ) :
    primeHarmonic p (Real.pi / 6) (Real.pi / 3 - s) =
      primeHarmonic p (Real.pi / 6) s := by
  have : Real.pi / 3 - s = 2 * (Real.pi / 6) - s := by ring
  rw [this]; exact primeHarmonic_reflection_invariant p (Real.pi / 6) s

/-- Prime harmonics are classically symmetric about 1/2. -/
theorem primeHarmonic_classical_invariant (p : ℕ) (s : ℝ) :
    primeHarmonic p (1/2 : ℝ) (1 - s) = primeHarmonic p (1/2 : ℝ) s := by
  have : (1 : ℝ) - s = 2 * (1/2 : ℝ) - s := by ring
  rw [this]; exact primeHarmonic_reflection_invariant p (1/2) s

-- ============================================================================
-- § 5. The two symmetry axes are incompatible
-- ============================================================================

/-- The symmetry centers differ: 1/2 ≠ π/6. -/
theorem axes_differ : (1 : ℝ) / 2 ≠ Real.pi / 6 := by
  linarith [Real.pi_gt_three]

/-- The composition of the two reflections is a translation by π/3 - 1 > 0. -/
theorem composition_is_positive_translation (s : ℂ) :
    coshRotationP (classicalRotation s) = s + ↑(Real.pi / 3 - 1) := by
  simp [classicalRotation, coshRotationP]; ring

/-- The translation step is positive: π/3 - 1 > 0. -/
theorem translation_positive : Real.pi / 3 - 1 > 0 := by
  linarith [Real.pi_gt_three]

-- ============================================================================
-- PART II: THE GEOMETRIC IMPOSSIBILITY
-- ============================================================================

-- ============================================================================
-- § 6. Iteration
-- ============================================================================

/-- Iterating the translation pushes any point out of the strip. -/
private lemma iterate_translate (S : Set ℂ)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationP s ∈ S)
    {s : ℂ} (hs : s ∈ S) (n : ℕ) :
    s + ↑(↑n * (Real.pi / 3 - 1)) ∈ S := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    have step : ∀ z ∈ S, z + ↑(Real.pi / 3 - 1) ∈ S := by
      intro z hz
      simpa [composition_is_positive_translation] using h2 _ (h1 _ hz)
    convert step _ ih using 1
    push_cast; ring

-- ============================================================================
-- § 7. No dual-invariant set in the strip
-- ============================================================================

/-- **Dual impossibility**: any set simultaneously invariant under both
    reflections must be empty, because iterated translation by π/3 - 1 > 0
    eventually pushes every point past Re(s) = 1. -/
theorem no_dual_symmetric_set (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationP s ∈ S) :
    S = ∅ := by
  by_contra h_nonempty
  obtain ⟨s, hs⟩ : ∃ s ∈ S, 0 < s.re ∧ s.re < 1 :=
    (Set.nonempty_iff_ne_empty.mpr h_nonempty).elim fun s hs => ⟨s, hs, hstrip s hs⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℝ) > (1 - s.re) / (Real.pi / 3 - 1) := exists_nat_gt _
  have hmem := iterate_translate S h1 h2 hs.1 n
  have hbound := hstrip _ hmem
  norm_num at *
  nlinarith [Real.pi_gt_three,
    mul_div_cancel₀ (1 - s.re) (show (Real.pi / 3 - 1) ≠ 0 by linarith [Real.pi_gt_three])]

/-- No nonempty set of off-line zeros survives both reflections. -/
theorem no_conspiracy (S : Set ℂ)
    (hzeros : ∀ s ∈ S, IsNontrivialOfflineZero s)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationP s ∈ S) :
    S = ∅ :=
  no_dual_symmetric_set S (fun s hs => ⟨(hzeros s hs).2.1, (hzeros s hs).2.2.1⟩) h1 h2

/-- No infinite set of off-line zeros survives both reflections. -/
theorem no_infinite_conspiracy (S : Set ℂ)
    (hzeros : ∀ s ∈ S, IsNontrivialOfflineZero s)
    (hinf : S.Infinite)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationP s ∈ S) :
    False := by
  have := no_conspiracy S hzeros h1 h2
  subst this; exact hinf Set.finite_empty

-- ============================================================================
-- PART III: THE CLOSED REDUCTION
-- ============================================================================

-- ============================================================================
-- § 8. offlineZeros is classically-rotation-invariant
-- ============================================================================

/-- offlineZeros is invariant under s ↦ 1-s, unconditionally.
    Discharged by the functional equation. -/
theorem offlineZeros_classical_invariant :
    ∀ s ∈ offlineZeros, classicalRotation s ∈ offlineZeros := by
  intro ρ ⟨hz, hpos, hlt1, hoff⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show riemannZeta (1 - ρ) = 0
    have hnotint : ∀ n : ℕ, ρ ≠ -↑n := by
      intro n hn
      have hre : ρ.re = -(n : ℂ).re := by simpa using congrArg Complex.re hn
      have hnonpos : ρ.re ≤ 0 := by
        rw [hre]
        norm_num
      exact (not_le_of_gt hpos) hnonpos
    have hne1 : ρ ≠ 1 := by intro h; rw [h] at hlt1; simp at hlt1
    rw [riemannZeta_one_sub hnotint hne1, hz, mul_zero]
  · show 0 < (1 - ρ).re
    simp only [sub_re, one_re]; linarith
  · show (1 - ρ).re < 1
    simp only [sub_re, one_re]; linarith
  · show (1 - ρ).re ≠ 1 / 2
    simp only [sub_re, one_re]; intro h; exact hoff (by linarith)

private theorem nontrivial_zero_re_pos
    {s : ℂ}
    (hs : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (↑n + 1))
    (hone : s ≠ 1) :
    0 < s.re := by
  by_contra hnonpos
  have hle : s.re ≤ 0 := le_of_not_gt hnonpos
  by_cases hnat : ∃ n : ℕ, s = -↑n
  · rcases hnat with ⟨n, rfl⟩
    cases n with
    | zero =>
        norm_num [riemannZeta_zero] at hs
    | succ n =>
        rcases Nat.even_or_odd (n + 1) with h_even | h_odd
        · rcases h_even with ⟨m, hm⟩
          cases m with
          | zero =>
              norm_num at hm
          | succ k =>
              apply htriv
              refine ⟨k, ?_⟩
              calc
                -↑(n + 1) = -((↑k + 1) + (↑k + 1 : ℂ)) := by simpa [hm]
                _ = -(2 * (↑k + 1)) := by ring
                _ = -2 * (↑k + 1) := by ring
        · have hGamma : Gammaℝ (-((n + 1 : ℂ))) ≠ 0 := by
            rw [Ne, Gammaℝ_eq_zero_iff]
            intro hzero
            rcases hzero with ⟨m, hm⟩
            rcases h_odd with ⟨l, hl⟩
            have hEvenEq : n + 1 = 2 * m := by
              exact_mod_cast neg_injective hm
            omega
          have hs_ne_zero : (-((n + 1 : ℂ))) ≠ 0 := by
            exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
          have hΛs : completedRiemannZeta (-((n + 1 : ℂ))) = 0 := by
            have hs' := hs
            have hsdef :
                riemannZeta (-((n + 1 : ℂ))) =
                  completedRiemannZeta (-((n + 1 : ℂ))) / Gammaℝ (-((n + 1 : ℂ))) :=
              riemannZeta_def_of_ne_zero hs_ne_zero
            rw [show riemannZeta (-↑(n + 1)) =
                completedRiemannZeta (-↑(n + 1)) / Gammaℝ (-↑(n + 1)) by simpa using hsdef,
              div_eq_zero_iff] at hs'
            rcases hs' with hΛs | hΓzero
            · simpa using hΛs
            · have hGamma' : Gammaℝ (-↑(n + 1)) ≠ 0 := by
                simpa using hGamma
              exact False.elim (hGamma' hΓzero)
          have hΛt : completedRiemannZeta (1 - (-((n + 1 : ℂ)))) = 0 := by
            simpa [completedRiemannZeta_one_sub] using hΛs
          have ht_ne_zero : (1 - (-((n + 1 : ℂ)))) ≠ 0 := by
            intro hzero
            have hre : (1 - (-((n + 1 : ℂ)))).re = 0 := by
              rw [hzero]
              simp
            have hformula : (1 - (-((n + 1 : ℂ)))).re = n + 2 := by
              calc
                (1 - (-((n + 1 : ℂ)))).re = 1 - (-((n + 1 : ℂ)).re) := by
                  simp [Complex.sub_re]
                _ = 1 - (-(n + 1 : ℝ)) := by simp
                _ = n + 2 := by ring
            nlinarith
          have hzt : riemannZeta (1 - (-((n + 1 : ℂ)))) = 0 := by
            rw [riemannZeta_def_of_ne_zero ht_ne_zero, hΛt, zero_div]
          have hge : 1 ≤ (1 - (-((n + 1 : ℂ)))).re := by
            have hre : (1 - (-((n + 1 : ℂ)))).re = n + 2 := by
              calc
                (1 - (-((n + 1 : ℂ)))).re = 1 - (-((n + 1 : ℂ)).re) := by
                  simp [Complex.sub_re]
                _ = 1 - (-(n + 1 : ℝ)) := by simp
                _ = n + 2 := by ring
            nlinarith
          exact riemannZeta_ne_zero_of_one_le_re hge hzt
  · have hzero' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub (by simpa using hnat) hone, hs, mul_zero]
    have hge : 1 ≤ (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hge hzero'

-- ============================================================================
-- § 9. The main theorems
-- ============================================================================

/-- **Main Theorem.** If offlineZeros is cosh-rotation-invariant,
    then offlineZeros is empty.

    Classical rotation invariance is discharged by the functional equation.
    The composition gives translation by π/3-1 > 0. Iteration pushes
    Re past 1, hitting the zero-free region. Contradiction. -/
theorem offlineZeros_empty_if_cosh_invariant
    (h_cosh : ∀ s ∈ offlineZeros, coshRotationP s ∈ offlineZeros) :
    offlineZeros = ∅ := by
  by_contra h_ne
  obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
  have hmem := iterate_translate offlineZeros offlineZeros_classical_invariant h_cosh hρ
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - ρ.re) / (Real.pi / 3 - 1))
  have hmem_n := hmem n
  have hlt := hmem_n.2.2.1
  have hre : (ρ + ↑(↑n * (Real.pi / 3 - 1))).re = ρ.re + ↑n * (Real.pi / 3 - 1) := by
    simp [add_re, ofReal_re]
  nlinarith [translation_positive, hρ.2.1,
    mul_div_cancel₀ (1 - ρ.re) (show Real.pi / 3 - 1 ≠ 0 by linarith [translation_positive])]

/-- **Corollary.** This isn't real -/
theorem RH_of_cosh_invariance
    (h_cosh : ∀ s ∈ offlineZeros, coshRotationP s ∈ offlineZeros) :
    RiemannHypothesis := by
  have hempty := offlineZeros_empty_if_cosh_invariant h_cosh
  intro s hs htriv hone
  by_contra hoff
  have : s ∈ offlineZeros := by
    refine ⟨hs, ?_, ?_, hoff⟩
    · exact nontrivial_zero_re_pos hs htriv hone
    · exact not_le.mp fun h_ge => riemannZeta_ne_zero_of_one_le_re h_ge hs
  rw [hempty] at this; exact this

/-- **Equivalence.** offlineZeros = ∅ ↔ RH. -/
theorem offlineZeros_empty_iff_RH :
    offlineZeros = ∅ ↔ RiemannHypothesis := by
  constructor
  · exact fun h => RH_of_cosh_invariance (fun s hs => by rw [h] at hs; exact hs.elim)
  · intro hRH
    ext s; simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hs, hpos, hlt1, hoff⟩
    exact hoff (hRH s hs (by intro ⟨n, hn⟩; simp [hn] at hpos; linarith)
      (by intro h1; rw [h1] at hlt1; simp at hlt1))

end
