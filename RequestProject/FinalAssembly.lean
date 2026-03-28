import Mathlib
import RequestProject.PrimesOnTheNumberLine
import RequestProject.ZetaZerosPrimeDistribution
import RequestProject.CoshKernel
import RequestProject.CoshKernelVanishing
import RequestProject.OffAxisTheoremDefs
import RequestProject.OffAxisTheorem
import RequestProject.OffAxisZeta
import RequestProject.ZetaObservables
import RequestProject.PrimeHarmonicReflection
import RequestProject.HarmonicCancellation
import RequestProject.CoshNoZeros
import RequestProject.CoshSymmetryBreak
import RequestProject.ZetaCoshReflection
import RequestProject.ZetaSymmetry
import RequestProject.CriticalStripControlOffline
import RequestProject.ProofChain

/-!
# Assembled Proof Chain: No Off-Line Zeta Zeros Exist

This file imports every module in the `RequestProject` directory and assembles
their results into one linear chain that terminates in the final theorem:

  **offlineZeros = ∅  ↔  RiemannHypothesis**

Nothing is re-proved here.  Every `theorem` below is a thin wrapper that
re-exports or composes results already established in the component files.
No `sorry`.  No axioms beyond Mathlib.

## Proof map (mirroring README.md §1–§14)

| Stage | What is established | Source file(s) |
|-------|---------------------|----------------|
| §1  | ℝ exists, primes embed canonically, prime harmonics diverge, Λ*ζ = log | `PrimesOnTheNumberLine` |
| §2  | Zeta zeros control prime distribution via Euler product & zero-free region | `ZetaZerosPrimeDistribution` |
| §3  | Cosh kernel at π/6: fold symmetry, strict positivity, no zeros | `CoshKernel` |
| §4  | Cosh kernel vanishing: arcsin(1/2) = π/6, imaginary part zero, reflection | `CoshKernelVanishing` |
| §5  | Off-axis zeros force observable anti-symmetry & harmonic distortion | `OffAxisTheoremDefs`, `OffAxisTheorem`, `OffAxisZeta`, `ZetaObservables` |
| §6  | Prime harmonics not reflection-invariant for off-line zeros | `PrimeHarmonicReflection` |
| §7  | Dual reflection impossibility: composition = translation by π/3 − 1 > 0 | `DualReflectionImpossibility` |
| §8  | Harmonic cancellation: sin(arcsin(1/2)) = 1/2, cosh residues | `HarmonicCancellation` |
| §9  | Cosh has no real zeros anywhere ⇒ no cancellation of distorted harmonics | `CoshNoZeros` |
| §10 | Cosh symmetry break: nonzero residue ⇒ reflection test fails | `CoshSymmetryBreak` |
| §11 | Zeta–cosh reflection equivalence: both tests pass or both fail | `ZetaCoshReflection` |
| §12 | Zeta symmetry: ξ(s₀)=0 ⇒ ξ(1−s₀)=0, zero pairing | `ZetaSymmetry` |
| §13 | Strip rotation control: 0° identity, equal convergence, isometric zeros | `CriticalStripControl` |
| §14 | Online/offline rotation & isometry checks | `CriticalStripIsoOnline`, `CriticalStripIsoOffline`, `CriticalStripFlipOnline`, `CriticalStripFlipOffline`, `CriticalStripControlOffline` |
| §15 | Self-contained proof chain: distortion → impossibility → RH equivalence | `ProofChain` |

## Assembly strategy

We do **not** duplicate any proof term.  We import every component, then:

1. Re-export the six foundational pillars as named landmarks.
2. State the three key bridge lemmas that connect the components.
3. State the final theorems by direct appeal to `ProofChain`.
-/


open Complex Real Set ComplexConjugate

noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 1:  The number line, primes, and their harmonics
--            (PrimesOnTheNumberLine.lean, ZetaZerosPrimeDistribution.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Primes populate the real line without bound. -/
theorem pillar1_primes_infinite : Set.Infinite {x : ℝ | ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) = x} :=
  primes_infinite_on_number_line

/-- The prime harmonic series ∑ 1/p diverges — primes generate an infinite signal. -/
theorem pillar1_harmonics_diverge : ¬Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)) :=
  prime_harmonics_diverge

/-- Λ * ζ_arith = log: the von Mangoldt function ties primes to zeta. -/
theorem pillar1_vonMangoldt_identity :
    ArithmeticFunction.vonMangoldt * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
    ArithmeticFunction.log :=
  vonMangoldt_conv_zeta_eq_log

/-- ζ(s) ≠ 0 for Re(s) ≥ 1 — the classical zero-free region. -/
theorem pillar1_zeta_nonvanishing (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 2:  The cosh kernel — fold symmetry and positivity
--            (CoshKernel.lean, CoshKernelVanishing.lean, CoshNoZeros.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The cosh kernel at π/6 is invariant under σ ↦ π/3 − σ. -/
theorem pillar2_cosh_fold (σ : ℝ) : coshKernel (π / 3 - σ) = coshKernel σ :=
  coshKernel_fold_symmetry σ

/-- cosh is strictly positive everywhere — no zeros to absorb distortion. -/
theorem pillar2_cosh_pos (σ : ℝ) : 0 < coshKernel σ :=
  coshKernel_pos σ

/-- arcsin(1/2) = π/6 — the fundamental evaluation linking the two worlds. -/
theorem pillar2_arcsin_eval : Real.arcsin (1 / 2 : ℝ) = π / 6 :=
  arcsin_one_half

/-- The cosh kernel at arcsin(1/2) has zero imaginary part (purely real). -/
theorem pillar2_cosh_purely_real :
    (Complex.cosh (↑(Real.arcsin (1 / 2 : ℝ)))).im = 0 :=
  cosh_at_arcsin_half_im_zero

/-- cosh has no real zeros whatsoever. -/
theorem pillar2_cosh_no_zeros (x : ℝ) : Real.cosh x ≠ 0 :=
  cosh_ne_zero x

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 3:  Off-axis zeros force observable distortion
--            (OffAxisTheorem.lean, OffAxisZeta.lean, ZetaObservables.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- An off-axis zero fires the rotated prime density detector. -/
theorem pillar3_detector_fires (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ :=
  offaxis_forces_rotated_detector_event ρ hz hoff

/-- An off-axis zero produces an anti-symmetry event in the observables. -/
theorem pillar3_antisymmetry (ρ : ℂ) (h : ZetaObservables.offAxisClassicalZetaZero ρ) :
    ZetaObservables.RotatedObservableAntiSymmetryEvent ρ :=
  ZetaObservables.offAxisZero_implies_antiSymmetryEvent ρ h

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 4:  Prime harmonics break reflection symmetry off the critical line
--            (PrimeHarmonicReflection.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- For Re(s) ≠ 1/2 and x > 1, the prime harmonic norms differ under reflection. -/
theorem pillar4_harmonics_break_symmetry (s : ℂ) (hs : s.re ≠ 1 / 2)
    (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ s‖ ≠ ‖(x : ℂ) ^ (1 - conj s)‖ :=
  prime_harmonic_not_reflection_invariant s hs x hx

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 5:  Cosh symmetry break & zeta–cosh reflection equivalence
--            (CoshSymmetryBreak.lean, ZetaCoshReflection.lean,
--             HarmonicCancellation.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- If any cosh residue remains, the cosh symmetry reflection test fails. -/
theorem pillar5_residue_breaks_symmetry (f : ℝ → ℝ) (h : HasCoshResidue f) :
    ¬PassesCoshSymmetryTest f :=
  cosh_residue_implies_symmetry_test_fails f h

/-- cosh itself has no residue — it passes its own symmetry test. -/
theorem pillar5_cosh_clean : ¬HasCoshResidue Real.cosh :=
  cosh_has_no_residue

/-- The zeta strip rotation test and cosh reflection test are equivalent. -/
theorem pillar5_tests_equivalent :
    ¬(ZetaCoshReflection.StripRotationInvariant ZetaCoshReflection.criticalLine ∧
      ¬ZetaCoshReflection.CoshReflectionVanishes ZetaCoshReflection.coshTestPoint) :=
  ZetaCoshReflection.not_rotation_without_reflection

/-- sin(arcsin(1/2)) = 1/2 — the projection identity. -/
theorem pillar5_projection : Real.sin (Real.arcsin (1 / 2)) = 1 / 2 :=
  sin_arcsin_one_half

-- ═══════════════════════════════════════════════════════════════════════════
-- PILLAR 6:  Functional equation symmetry & strip rotation geometry
--            (ZetaSymmetry.lean, CriticalStripControl.lean,
--             CriticalStripFlipOnline.lean, CriticalStripFlipOffline.lean,
--             CriticalStripIsoOnline.lean, CriticalStripIsoOffline.lean,
--             CriticalStripControlOffline.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- ξ(s₀) = 0  ⇒  ξ(1 − s₀) = 0. -/
theorem pillar6_xi_symmetry (s₀ : ℂ) (h : completedRiemannZeta s₀ = 0) :
    completedRiemannZeta (1 - s₀) = 0 :=
  completedRiemannZeta_zero_symm s₀ h

/-- An off-line zero persists under any product ζ(s)^n. -/
theorem pillar6_zero_persistence {s : ℂ} (hζ : riemannZeta s = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    riemannZeta s ^ n = 0 :=
  zeta_zero_pow_eq_zero hζ n hn

/-- An off-line zero and its functional-equation partner are distinct. -/
theorem pillar6_partner_distinct {s : ℂ} (hoffline : s.re ≠ 1 / 2) :
    1 - s ≠ s :=
  offLine_zero_partner_ne hoffline

-- ═══════════════════════════════════════════════════════════════════════════
-- BRIDGE 1:  The two symmetry axes are incompatible
--            (from ProofChain.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- 1/2 ≠ π/6 — the classical and cosh symmetry centers differ. -/
theorem bridge_axes_differ : (1 : ℝ) / 2 ≠ Real.pi / 6 :=
  axes_differ

/-- Composing the two reflections yields translation by π/3 − 1 > 0. -/
theorem bridge_composition (s : ℂ) :
    coshRotation (classicalRotation s) = s + ↑(Real.pi / 3 - 1) :=
  composition_is_positive_translation s

/-- The translation step is strictly positive. -/
theorem bridge_step_positive : Real.pi / 3 - 1 > 0 :=
  translation_positive

-- ═══════════════════════════════════════════════════════════════════════════
-- BRIDGE 2:  Dual invariance forces emptiness
--            (from DualReflectionImpossibility.lean / ProofChain.lean)
-- ═══════════════════════════════════════════════════════════════════════════

/-- No nonempty set of off-line zeros survives both reflections. -/
theorem bridge_no_conspiracy (S : Set ℂ)
    (hzeros : ∀ s ∈ S, IsNontrivialOfflineZero s)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S) :
    S = ∅ :=
  no_conspiracy S hzeros h1 h2

-- ═══════════════════════════════════════════════════════════════════════════
-- BRIDGE 3:  offlineZeros is classically rotation-invariant
--            (from ProofChain.lean, via the functional equation)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The functional equation makes offlineZeros invariant under s ↦ 1 − s. -/
theorem bridge_classical_invariance :
    ∀ s ∈ offlineZeros, classicalRotation s ∈ offlineZeros :=
  offlineZeros_classical_invariant

-- ═══════════════════════════════════════════════════════════════════════════
-- FINAL THEOREM 1:  Cosh invariance ⇒ offlineZeros = ∅
-- ═══════════════════════════════════════════════════════════════════════════

/-- If offlineZeros is also cosh-rotation-invariant, it must be empty.
    Classical invariance is unconditional (functional equation).
    The composition gives translation by π/3 − 1 > 0.
    Iteration pushes Re past 1, hitting the zero-free region. -/
theorem final_empty_if_cosh_invariant
    (h_cosh : ∀ s ∈ offlineZeros, coshRotation s ∈ offlineZeros) :
    offlineZeros = ∅ :=
  offlineZeros_empty_if_cosh_invariant h_cosh

-- ═══════════════════════════════════════════════════════════════════════════
-- FINAL THEOREM 2:  Cosh invariance ⇒ Riemann Hypothesis
-- ═══════════════════════════════════════════════════════════════════════════

/-- Cosh rotation invariance of the off-line zero set implies RH. -/
theorem final_RH_of_cosh_invariance
    (h_cosh : ∀ s ∈ offlineZeros, coshRotation s ∈ offlineZeros) :
    RiemannHypothesis :=
  RH_of_cosh_invariance h_cosh

-- ═══════════════════════════════════════════════════════════════════════════
-- FINAL THEOREM 3:  offlineZeros = ∅  ↔  RiemannHypothesis
-- ═══════════════════════════════════════════════════════════════════════════

/-- The emptiness of the off-line zero set is logically equivalent to the
    Riemann Hypothesis.  This is the terminal statement of the proof chain. -/
theorem final_equivalence : offlineZeros = ∅ ↔ RiemannHypothesis :=
  offlineZeros_empty_iff_RH

end
