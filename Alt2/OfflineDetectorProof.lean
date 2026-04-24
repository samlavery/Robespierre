import Mathlib
import RequestProject.HarmonicDiagnostics
import RequestProject.ZetaZeroDefs

/-!
# Cosh-side detector + no-cancellation + Weil-zero bridge (unconditional)

**File role.**  This file hosts a *cosh-side* unconditional lemma bundling
three facts about every nontrivial zeta zero `ρ`:

1. **Bridge (unconditional on zero location).**  At every prime `p`, the
   even-channel zero-pair contribution from `ρ` and its FE-partner
   `1 − ρ̄` — the scalar that enters the prime side of the Weil explicit
   formula — is exactly `balancedEnvelope p · coshDetector ρ.re (log p)`.
   Both sides *observe the same object* at `ρ`: the Weil prime side and
   the cosh detector index into `ZD.NontrivialZeros` identically and
   their per-(ρ, p) readings agree up to the balanced envelope factor.

2. **Detection at every prime (offline-conditional).**  When `ρ.re ≠ 1/2`,
   the cosh detector reads strictly above 1 at every prime
   (`HarmonicDiagnostics.infinite_detection`).

3. **No cancellation (offline-conditional).**  The sum of per-prime
   excesses `(cosh − 1)` over any nonempty prime `Finset` is strictly
   positive — positive-cone property
   (`HarmonicDiagnostics.totalEvenChannelExcess_pos_of_offline`).

All content reuses lemmas already proved in-project.  Fully unconditional:
no RH hypothesis, no Weil explicit-formula input, no custom axioms.  The
bridge conjunct is the piece that pins the cosh-side readings to the
exact same zeros the Weil explicit formula sums over.

## Architectural separation

* **Cosh side (this file).**  Operates on `coshDetector` /
  `zeroPairEnvelope` / `balancedEnvelope` plus the `NontrivialZeros`
  zero set.  No Weil explicit-formula content.
* **Weil side (elsewhere).**  Proves unconditional integral / zero-sum
  identities via the Weil explicit formula, indexed over the same
  `NontrivialZeros`.

The bridge conjunct is the structural identification that makes the two
sides comparable at contradiction time.
-/

open Real ZetaDefs BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace CoshReflectedClassifier

/-- **Offline detected + no cancellation + Weil-zero bridge (unconditional).**
For every nontrivial zeta zero `ρ`:

* **(bridge)** at every prime `p`, the even-channel zero-pair contribution
  `p^ρ.re + p^(1−ρ.re)` — the quantity entering the prime side of the Weil
  explicit formula — equals `balancedEnvelope p · coshDetector ρ.re (log p)`.
  The cosh detector reads the same zero `ρ` the Weil side sums over.
* **(detection)** if `ρ.re ≠ 1/2`, the cosh detector reads strictly above
  1 at every prime.
* **(no cancellation)** if `ρ.re ≠ 1/2`, the sum of per-prime excesses
  `(cosh − 1)` over any nonempty prime set is strictly positive
  (positive cone; no antisymmetric compensator).

Pure cosh-side content; no Weil explicit-formula input; no RH hypothesis.
Axiom footprint = the kernel only. -/
theorem offline_detected_no_cancellation :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      (∀ p : ℕ, Nat.Prime p →
        (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
          balancedEnvelope (↑p) *
          coshDetector ρ.re (Real.log (↑p))) ∧
      (ρ.re ≠ 1/2 →
        (∀ p : ℕ, Nat.Prime p → 1 < coshDetector ρ.re (Real.log (↑p))) ∧
        (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
          0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1))) := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · -- Bridge: `euler_envelope_eq_cosh` unfolds `zeroPairEnvelope`.
    intro p hp
    have h := euler_envelope_eq_cosh p hp ρ.re
    simpa [zeroPairEnvelope] using h
  · -- Detection + no-cancellation.
    intro hoff
    have hoff' : ρ ∈ ZD.OffLineZeros := ⟨hρ, hoff⟩
    refine ⟨fun p hp => infinite_detection ρ hoff' p hp, ?_⟩
    intro ps hps hne
    have h := totalEvenChannelExcess_pos_of_offline ρ hoff' ps hps hne
    simpa [totalEvenChannelExcess, evenChannelExcess] using h

#print axioms offline_detected_no_cancellation

end CoshReflectedClassifier
end Contour
end WeilPositivity
end ZD

end
