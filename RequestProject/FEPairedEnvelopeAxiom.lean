import RequestProject.RiemannHypothesisBridge

/-!
# FE-Paired Prime-Harmonic Envelope under the Double-Cosh Transport

This file names the single remaining analytic input as a Lean `axiom`, then
derives Mathlib's `RiemannHypothesis` conditionally on it. The `#print axioms`
footprint explicitly exposes the assumption.

## The axiom

For every nontrivial zeta zero `ρ`, the FE-paired zero envelope
`{p^{ρ.re}, p^{1-ρ.re}}` at every prime `p`, transported through the
double-cosh pair kernel `(K_L, K_R)`, reads balanced — the left and right
anchors agree at every prime.

Equivalently (via the §11.3 factorization
`zeroPairEnvelopeLeft r β = balancedEnvelopeLeft r · K_L β (log r)`):
the pair-agreement defect vanishes at every prime on every nontrivial zero.

## Derivation chain under the axiom

```
axiom: K_L(ρ.re, log p) = K_R(ρ.re, log p)   at every prime p, every ρ ∈ NontrivialZeros
  ↓  prime_coshPair_agrees_iff (at p = 2)
∀ ρ ∈ NontrivialZeros, ρ.re = 1/2
  ↓  no_offline_zeros_implies_rh
RiemannHypothesis
```

The final `#print axioms RiemannHypothesis_from_FEPairedEnvelope` output
lists exactly `[propext, Classical.choice, Quot.sound,
fe_paired_prime_harmonic_envelope_transport]` — three mathlib-standard
axioms plus the single named analytic input.
-/

open Real ZetaDefs DoubleCoshResidue DoubleCoshValidation RHBridge

noncomputable section

namespace FEPairedEnvelope

/-- **Axiom (FE-paired prime-harmonic envelope under the double-cosh transport)**.

For every nontrivial zeta zero `ρ` and every prime `p`, the double-cosh
pair kernel reads agreement: `K_L(ρ.re, log p) = K_R(ρ.re, log p)`.

This is the **sole external analytic input** the classifier program needs
to close RH. It asserts that the FE-paired zero envelope
`{p^{ρ.re}, p^{1 − ρ.re}}`, transported through the π/6-anchored pair of
cosh kernels, lands on the balanced diagonal at every prime.

No proof is supplied here. It is the open analytic content. -/
axiom fe_paired_prime_harmonic_envelope_transport :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        coshDetectorLeft ρ.re (Real.log p) = coshDetectorRight ρ.re (Real.log p)

/-- **Consequence of the axiom at every prime**: the pair-agreement defect
vanishes at every prime on every nontrivial zero. -/
theorem pairAgreementDefect_zero_at_every_prime
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    (p : ℕ) (hp : Nat.Prime p) :
    pairAgreementDefect (p : ℝ) ρ.re = 0 := by
  unfold pairAgreementDefect
  rw [fe_paired_prime_harmonic_envelope_transport ρ hρ p hp]
  ring

/-- **Consequence at a canonical prime (p = 2)**: the classifier reads
zero on every nontrivial zero. -/
theorem classifier_zero_at_two
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    pairAgreementDefect (2 : ℝ) ρ.re = 0 := by
  have h := pairAgreementDefect_zero_at_every_prime ρ hρ 2 Nat.prime_two
  simpa using h

/-- **Closure to Mathlib's `RiemannHypothesis`**: the axiom plus the
unconditional classifier chain produces a term of Mathlib's
`RiemannHypothesis`. The axiom footprint makes the single analytic
assumption explicit. -/
theorem RiemannHypothesis_from_FEPairedEnvelope : RiemannHypothesis := by
  apply no_offline_zeros_implies_rh
  intro ρ hρ
  have h2 : coshDetectorLeft ρ.re (Real.log 2) = coshDetectorRight ρ.re (Real.log 2) :=
    fe_paired_prime_harmonic_envelope_transport ρ hρ 2 Nat.prime_two
  exact (prime_coshPair_agrees_iff 2 Nat.prime_two).mp h2

/-! ### Axiom hygiene

Expected footprint: mathlib-standard `[propext, Classical.choice, Quot.sound]`
plus the single named `fe_paired_prime_harmonic_envelope_transport` axiom.
Nothing else — no hidden `sorryAx`, no smuggled custom axioms. -/

#print axioms pairAgreementDefect_zero_at_every_prime
#print axioms classifier_zero_at_two
#print axioms RiemannHypothesis_from_FEPairedEnvelope

end FEPairedEnvelope

end
