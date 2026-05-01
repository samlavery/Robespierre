import RequestProject.HarmonicDiagnostics

/-!
# Consumer-API Smoke Tests for the Two-Kernel Pair Diagnostic Framework

This file exercises the full pair-diagnostic API from `ZetaZeroDefs §3c′`,
`OfflineAmplitudeMethods §11`, and `HarmonicDiagnostics §7.1-§7.20 + §7.19b`
through `example :=` declarations. It provides **regression protection beyond
`#check`**: if a constructor or theorem breaks, or if the chain from raw
membership hypotheses (`ρ ∈ ZD.OnLineZeros` etc.) through bundles and
refutation lemmas breaks, this file fails to typecheck.

Axiom hygiene is documented in comments next to each `#print axioms` — the
expected footprint is mathlib-standard `[propext, Classical.choice, Quot.sound]`
on every listed lemma. If any runs with a larger axiom set, a custom axiom
leaked in upstream.
-/

namespace PairDiagnosticsTest

open ZetaDefs Real

-- ════════════════════════════════════════════════════════════════════════════
-- §1. Core kernel primitives (ZetaZeroDefs §3c′)
-- ════════════════════════════════════════════════════════════════════════════

/-- Left kernel reads 1 at its anchor β = π/6. -/
example (t : ℝ) : coshDetectorLeft (π / 6) t = 1 :=
  coshDetectorLeft_one_at_center t

/-- Right kernel reads 1 at its anchor β = 1 − π/6. -/
example (t : ℝ) : coshDetectorRight (1 - π / 6) t = 1 :=
  coshDetectorRight_one_at_center t

/-- Reflection β ↔ 1−β swaps the two kernels. -/
example (β t : ℝ) : coshDetectorLeft (1 - β) t = coshDetectorRight β t :=
  coshDetector_reflect_swap β t

/-- Agreement biconditional: K_L = K_R ↔ β = 1/2 (at nonzero scale). -/
example {t : ℝ} (ht : t ≠ 0) {β : ℝ} :
    coshDetectorLeft β t = coshDetectorRight β t ↔ β = 1 / 2 :=
  coshDetectors_agree_iff ht

-- ════════════════════════════════════════════════════════════════════════════
-- §2. Bridge identities (ZetaZeroDefs §3c′)
-- ════════════════════════════════════════════════════════════════════════════

/-- Sum factorization: `K_L + K_R = 2·cosh((1-π/3)·t/2) · coshDetector β t`. -/
example (β t : ℝ) :
    coshDetectorLeft β t + coshDetectorRight β t =
      2 * Real.cosh ((1 - π / 3) * t / 2) * coshDetector β t :=
  coshDetector_pair_sum β t

/-- Product decomposition: β-dependence isolated in `coshDetector β (2t)`. -/
example (β t : ℝ) :
    coshDetectorLeft β t * coshDetectorRight β t =
      (Real.cosh ((1 - π / 3) * t) + coshDetector β (2 * t)) / 2 :=
  coshDetector_pair_product β t

/-- Detector recovery: the original `coshDetector` is derivable from pair sum. -/
example (β t : ℝ) :
    coshDetector β t =
      (coshDetectorLeft β t + coshDetectorRight β t) /
        (2 * Real.cosh ((1 - π / 3) * t / 2)) :=
  coshDetector_from_pair_sum β t

/-- Calibration scalar is strictly positive (safe to divide by). -/
example (t : ℝ) : 0 < 2 * Real.cosh ((1 - π / 3) * t / 2) :=
  coshDetector_pair_calibration_pos t

-- ════════════════════════════════════════════════════════════════════════════
-- §3. Pair envelope theory (OfflineAmplitudeMethods §11)
-- ════════════════════════════════════════════════════════════════════════════

/-- Left envelope factors through left kernel at every positive scale. -/
example {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelopeLeft r β = balancedEnvelopeLeft r * coshDetectorLeft β (Real.log r) :=
  zeroPairEnvelopeLeft_eq_cosh hr β

/-- Right envelope factors through right kernel. -/
example {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelopeRight r β = balancedEnvelopeRight r * coshDetectorRight β (Real.log r) :=
  zeroPairEnvelopeRight_eq_cosh hr β

/-- Left envelope balanced-value biconditional. -/
example {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    amplitudeDefectLeft r β = 0 ↔ β = π / 6 :=
  amplitudeDefectLeft_eq_zero_iff hr hr1

/-- Pair-agreement defect biconditional: discriminating observable. -/
example {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    pairAgreementDefect r β = 0 ↔ β = 1 / 2 :=
  pairAgreementDefect_eq_zero_iff hr hr1

-- ════════════════════════════════════════════════════════════════════════════
-- §4. Diagnostic records (OfflineAmplitudeMethods §11)
-- ════════════════════════════════════════════════════════════════════════════

/-- Nontrivial-zero diagnostic: unconditional bundle. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) : TwoKernelDiagnostic ρ :=
  diagnostic_twoKernel ρ hρ

/-- Online diagnostic: kernels agree everywhere. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) : TwoKernelOnlineDiagnostic ρ :=
  diagnostic_twoKernel_online ρ hρ

/-- Offline diagnostic: kernels disagree at every nonzero scale. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) : TwoKernelOfflineDiagnostic ρ :=
  diagnostic_twoKernel_offline ρ hρ

-- ════════════════════════════════════════════════════════════════════════════
-- §5. Zero-indexed observables (HarmonicDiagnostics §7.1-§7.10)
-- ════════════════════════════════════════════════════════════════════════════

/-- Online zero: pair-diff is zero at every scale. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (y : ℝ) :
    coshPairDiff ρ y = 0 :=
  online_coshPairDiff_zero ρ hρ y

/-- Offline zero: pair-diff is nonzero at every nonzero scale. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) {y : ℝ} (hy : y ≠ 0) :
    coshPairDiff ρ y ≠ 0 :=
  offline_coshPairDiff_nonzero ρ hρ hy

/-- Infinite prime-indexed detection for offline zeros. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ p : ℕ, Nat.Prime p →
      coshDetectorLeft ρ.re (Real.log p) ≠ coshDetectorRight ρ.re (Real.log p) :=
  infinite_pair_detection ρ hρ

/-- Pair-agreement characterizes the critical line at any nonzero scale. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    pairAgreementDefect x ρ.re = 0 ↔ ρ.re = 1 / 2 :=
  pair_agreement_characterizes_line ρ hρ hx hx1

-- ════════════════════════════════════════════════════════════════════════════
-- §6. Measurement bundle (HarmonicDiagnostics §7.17)
-- ════════════════════════════════════════════════════════════════════════════

example (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) : PrimeHarmonicPairMeasurement ρ :=
  primeHarmonicPairMeasurement ρ hρ

-- ════════════════════════════════════════════════════════════════════════════
-- §7. Pair amplification at r = π/3 (HarmonicDiagnostics §7.19)
-- ════════════════════════════════════════════════════════════════════════════

example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) : pairAmplification ρ = 0 :=
  pairAmplification_zero_of_online ρ hρ

example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) : 0 < pairAmplification ρ :=
  pairAmplification_pos_of_offline ρ hρ

example (ρ : ℂ) : pairAmplification ρ = 0 ↔ ρ.re = 1 / 2 :=
  pairAmplification_zero_iff_online ρ

-- ════════════════════════════════════════════════════════════════════════════
-- §8. Realizability (HarmonicDiagnostics §7.15)
-- ════════════════════════════════════════════════════════════════════════════

example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) : ρ ∈ PairRealizableZeros :=
  online_pair_realizable ρ hρ

example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) : ρ ∉ PairRealizableZeros :=
  offline_not_pair_realizable ρ hρ

example (ρ : ℂ) (hρ : ρ ∈ PairRealizableZeros) : ρ.re = 1 / 2 :=
  pair_realizable_implies_online ρ hρ

-- ════════════════════════════════════════════════════════════════════════════
-- §9. Divergence (HarmonicDiagnostics §7.19b)
-- ════════════════════════════════════════════════════════════════════════════

example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ M : ℝ, ∃ p : ℕ, Nat.Prime p ∧
      M < coshDetectorLeft ρ.re (Real.log p) +
          coshDetectorRight ρ.re (Real.log p) :=
  offline_zero_pair_sum_unbounded ρ hρ

-- ════════════════════════════════════════════════════════════════════════════
-- §10. Online/offline bundles (HarmonicDiagnostics §7.20)
-- ════════════════════════════════════════════════════════════════════════════

example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) : OnlinePairZeroBundle ρ :=
  onlinePairZeroBundle ρ hρ

example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) : OfflinePairZeroBundle ρ :=
  offlinePairZeroBundle ρ hρ

/-- Online bundle delivers agreement + defect-zero at every prime. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (p : ℕ) (hp : Nat.Prime p) :
    coshDetectorLeft ρ.re (Real.log p) = coshDetectorRight ρ.re (Real.log p) ∧
    pairAgreementDefect p ρ.re = 0 :=
  (onlinePairZeroBundle ρ hρ).matches_prediction p hp

/-- Offline bundle delivers disagreement + defect-positivity at every prime. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) (p : ℕ) (hp : Nat.Prime p) :
    coshDetectorLeft ρ.re (Real.log p) ≠ coshDetectorRight ρ.re (Real.log p) ∧
    0 < pairAgreementDefect p ρ.re :=
  (offlinePairZeroBundle ρ hρ).matches_prediction p hp

/-- Offline bundle's unbounded-pair-sum field. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ M : ℝ, ∃ p : ℕ, Nat.Prime p ∧
      M < coshDetectorLeft ρ.re (Real.log p) +
          coshDetectorRight ρ.re (Real.log p) :=
  (offlinePairZeroBundle ρ hρ).unbounded_pair_sum

/-- Offline bundle's visible-on-interval field. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∀ x ∈ Set.Icc a b, 0 < pairAgreementDefect x ρ.re :=
  (offlinePairZeroBundle ρ hρ).visible_on_interval ha hab

-- ════════════════════════════════════════════════════════════════════════════
-- §11. RH refutation and equivalence (HarmonicDiagnostics §7.15, §7.20)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Offline zero refutes RH via pair observables only**. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ¬ (∀ ρ' : ℂ, ρ' ∈ ZD.NontrivialZeros → ρ'.re = 1 / 2) :=
  offline_pair_implies_unrealizable ρ (offlinePairZeroBundle ρ hρ)

/-- **RH equivalence stated entirely in pair kernel terms**. -/
example : (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ∀ p : ℕ, Nat.Prime p →
    coshDetectorLeft ρ.re (Real.log p) =
      coshDetectorRight ρ.re (Real.log p)) ↔
  (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2) :=
  rh_pair_internal_unconditional

/-- **Full dichotomy classification of nontrivial zeros via pair-agreement defect**. -/
example : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    riemannZeta ρ = 0 ∧
    ((ρ.re = 1/2 ∧ ∀ p : ℕ, Nat.Prime p → pairAgreementDefect p ρ.re = 0) ∨
     (ρ.re ≠ 1/2 ∧ ∀ p : ℕ, Nat.Prime p → 0 < pairAgreementDefect p ρ.re)) :=
  classify_all_nontrivial_zeros_pair

-- ════════════════════════════════════════════════════════════════════════════
-- §12. Axiom hygiene — expected footprint is mathlib-standard.
--
--   Run `#print axioms <name>` on each load-bearing lemma to verify.
--   Expected: `[propext, Classical.choice, Quot.sound]` only.
--   Any additional axiom indicates a leak upstream.
-- ════════════════════════════════════════════════════════════════════════════

-- Core primitives
#print axioms coshDetectors_agree_iff
#print axioms coshDetector_reflect_swap

-- Bridge
#print axioms coshDetector_pair_sum
#print axioms coshDetector_pair_product
#print axioms coshDetector_from_pair_sum

-- Envelopes
#print axioms zeroPairEnvelopeLeft_eq_cosh
#print axioms zeroPairEnvelopeRight_eq_cosh
#print axioms amplitudeDefectLeft_eq_zero_iff
#print axioms amplitudeDefectRight_eq_zero_iff
#print axioms pairAgreementDefect_eq_zero_iff

-- Diagnostic constructors
#print axioms diagnostic_twoKernel
#print axioms diagnostic_twoKernel_online
#print axioms diagnostic_twoKernel_offline

-- Measurement + bundles
#print axioms primeHarmonicPairMeasurement
#print axioms onlinePairZeroBundle
#print axioms offlinePairZeroBundle

-- Amplification + realizability
#print axioms pairAmplification_zero_iff_online
#print axioms pairAmplification_pos_iff_offline
#print axioms offline_not_pair_realizable
#print axioms online_pair_realizable
#print axioms pair_realizable_implies_online

-- Divergence
#print axioms prime_pair_sum_unbounded_of_offline

-- Capstones
#print axioms offline_pair_implies_unrealizable
#print axioms rh_pair_internal_unconditional
#print axioms classify_all_nontrivial_zeros_pair
#print axioms OnlinePairZeroBundle.matches_prediction
#print axioms OfflinePairZeroBundle.matches_prediction

end PairDiagnosticsTest
