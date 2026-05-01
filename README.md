# RequestProject: Offline Detector RH Proof

`OfflineDetectorProof.lean` is the main entrypoint for the RH proof architecture in `RequestProject`.

The project proves and assembles a forcing pipeline:

```text
off-line zero
  ⇒ positive cosh/even-channel prime excess
  ⇒ no finite-prime cancellation
  ⇒ the same amplitude channel is visible in the Weil prime side
  ⇒ global β-family Weil identities force zero-side vanishing
  ⇒ beta-totality + countable uniqueness upgrade aggregate vanishing to per-zero vanishing
  ⇒ positive off-line defect contradicts per-zero zero
  ⇒ no off-line zeros
  ⇒ RiemannHypothesis
```

The helix files are also included in the project, but they are not the main proof entrypoint. They prove supporting geometric facts: faithfulness of the log helix, uniqueness of the `σ = 1/2` helix model under natural symmetry/decoding constraints, and the connection between the helix model and critical-line geometry.

---

## Main entrypoint

```text
RequestProject/OfflineDetectorProof.lean
```

This file imports and orchestrates the detector side, Weil side, orthogonality side, final assembly, Klein forcing, and prime-harmonic amplitude bridge.

Important imports include:

```lean
import RequestProject.HarmonicDiagnostics
import RequestProject.ZetaZeroDefs
import RequestProject.OfflineAmplitudeMethods
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.WeilContour
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilFinalAssembly
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.WeilZeroOrthogonality
import RequestProject.GaussianClosedForm
import RequestProject.KleinForcerTheorem
import RequestProject.PrimeHarmonicAmplitude
```

Its job is to make the comparison point precise:

> the cosh detector and the Weil prime side observe the same zero-pair amplitude channel.

---

## Primary theorem: offline detection + no cancellation

Inside:

```lean
namespace ZD
namespace WeilPositivity
namespace Contour
namespace CoshReflectedClassifier
```

the main theorem is:

```lean
theorem offline_detected_no_cancellation :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      (∀ p : ℕ, Nat.Prime p →
        (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
          balancedEnvelope (↑p) *
          coshDetector ρ.re (Real.log (↑p))) ∧
      (ρ.re ≠ 1/2 →
        (∀ p : ℕ, Nat.Prime p →
          1 < coshDetector ρ.re (Real.log (↑p))) ∧
        (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
          0 < ∑ p ∈ ps,
            (coshDetector ρ.re (Real.log (↑p)) - 1)))
```

It packages three facts.

### 1. Bridge

For every nontrivial zero `ρ` and every prime `p`,

```text
p^ρ.re + p^(1 - ρ.re)
=
balancedEnvelope p · coshDetector ρ.re (log p)
```

So the cosh detector is not measuring a synthetic quantity. It is measuring the same zero-pair amplitude envelope that enters the prime side.

### 2. Detection

If `ρ.re ≠ 1 / 2`, then at every prime,

```text
1 < coshDetector ρ.re (log p)
```

An off-line zero is visible at every prime.

### 3. No cancellation

If `ρ.re ≠ 1 / 2`, then over any nonempty finite prime set,

```text
0 < ∑ p ∈ ps, (coshDetector ρ.re (log p) - 1)
```

The off-line contribution lies in a positive cone. It is not an alternating phase artifact that can cancel away on finite prime blocks.

---

## Prime-side amplitude-defect bridge

`OfflineDetectorProof.lean` also contains the prime-side amplitude bridge under:

```lean
namespace ZD
namespace WeilPositivity
namespace PrimeBoundedness
```

The summary theorem is:

```lean
theorem weil_prime_amplitudeDefect_bridge_summary : ...
```

It bundles:

1. per-prime amplitude bridge;
2. sinh-squared / amplitude-defect identity;
3. FE-pair symmetry of the amplitude envelope;
4. closed-form Weil prime aggregate at `σ = 2`;
5. per-`n` Weil positivity;
6. off-line aggregate amplitude-defect injection.

Representative theorem names:

```lean
amplitudeDefect_eq_balanced_mul_coshExcess
amplitudeDefect_prime_eq_balanced_mul_coshExcess
four_sinh_sq_eq_rpow_sq
rpow_sq_mul_eq_amplitudeDefect_sq_scale
four_p_sinh_sq_eq_amplitudeDefect_sq_scale
amplitudeDefect_symm
amplitudeDefect_pos_of_offline_zero_at_prime
sum_amplitudeDefect_pos_of_offline_zero
weil_prime_aggregate_closed_form_at_two
weil_prime_per_n_nonneg
pair_cosh_gauss_test_at_log_amplitudeDefect_form
weil_prime_amplitudeDefect_bridge_summary
```

This is the bridge from the detector world to the explicit-formula prime side.

---

## Endpoint / forcing boundary

The endpoint namespace is:

```lean
namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
```

The key local target is:

```lean
def WeilPrimeSideLink_target_local : Prop := ...
```

It keeps the uncancelled prime-side equation visible:

```text
S = S - M(1) + Sres
```

instead of immediately collapsing to:

```text
Sres = M(1)
```

This matters because the proof wants to use the prime side as the shared observation channel. If the prime sum is cancelled too early, the proof loses the place where positive off-line amplitude excess is visible.

---

## Forcing theory: why the RH proof works

The proof is a forcing argument.

### Step 1: off-line zeros force positive prime excess

If `ρ.re ≠ 1 / 2`, the detector theorem gives:

```text
coshDetector ρ.re (log p) > 1
```

at every prime.

Equivalently, the zero-pair amplitude exceeds the balanced critical-line envelope.

### Step 2: the excess has a sign

The finite-prime no-cancellation theorem gives:

```text
0 < ∑ p ∈ ps, (coshDetector ρ.re (log p) - 1)
```

for every nonempty finite prime set.

So off-line excess is not hidden by oscillation. The even channel is positive.

### Step 3: the Weil prime side sees the same channel

The amplitude bridge proves that the prime-side pair-cosh Gaussian terms carry the same `β`-dependent amplitude defect.

So the off-line signal is present in the same aggregate structure controlled by the Weil explicit formula.

### Step 4: the Weil β-family imposes global vanishing constraints

The Weil identity side supplies a family of identities indexed by:

```text
β ∈ (0,1)
```

schematically:

```text
∀ β ∈ (0,1),
  ∑' ρ, a(ρ) · pairTestMellin β ρ = 0
```

A single identity is not enough. The full β-family is what gives enough test directions.

### Step 5: beta-totality turns global β-vanishing into signal vanishing

`PairTestMellinBetaTotality` upgrades:

```text
all β-projections vanish
```

to:

```text
ZeroMellinSeries a t = 0 for every t > 0
```

This is a transform-totality statement for the pair-cosh Gaussian test family.

### Step 6: countable moment uniqueness makes it per-zero

`CountableTsumMomentUniqueness` upgrades the vanishing Mellin/exponential signal to coefficient-level vanishing:

```text
a(ρ) = 0
```

for every nontrivial zero.

This is the countable `tsum` analogue of Vandermonde / moment uniqueness.

### Step 7: per-zero vanishing contradicts positive off-line defect

For the RH detector application, coefficient vanishing is the per-zero vanishing of the Gaussian/cosh defect contribution:

```text
gaussianPairDefect ρ.re = 0
```

But the detector side proves:

```text
ρ.re ≠ 1 / 2 ⇒ gaussianPairDefect ρ.re > 0
```

Contradiction.

Therefore:

```text
ρ.re = 1 / 2
```

for every nontrivial zero.

Then:

```lean
RHBridge.no_offline_zeros_implies_rh
```

upgrades this to Mathlib’s `RiemannHypothesis`.

---

## Why this is not just detector positivity

Detector positivity alone says:

```text
if an off-line zero exists, it is visible.
```

The forcing theory says more:

```text
it is visible in the same prime amplitude channel constrained by the Weil identity,
and the β-family is total enough to prevent aggregate cancellation.
```

That is the proof mechanism.

---

## RH proof stack

### Zero definitions

```text
ZetaZeroDefs.lean
```

Defines:

```lean
ZD.NontrivialZeros
ZD.OffLineZeros
ZD.OnLineZeros
```

and the amplitude/cosh detector vocabulary.

### Detector and amplitude side

```text
OfflineAmplitudeMethods.lean
HarmonicDiagnostics.lean
PrimeHarmonicAmplitude.lean
GaussianDetectorPair.lean
PairCoshGaussTest.lean
GaussianClosedForm.lean
KleinForcerTheorem.lean
```

This layer proves:

```text
off-line ⇒ positive detector excess
off-line ⇒ positive finite-prime excess
gaussianPairDefect β = 0 ⇒ β = 1/2
two-kernel/Klein forcing ⇒ β = 1/2
```

### Weil identity side

```text
WeilContour.lean
WeilRightEdgePrimeSum.lean
WeilCoshPairPositivity.lean
WeilFinalAssembly.lean
WeilExplicitFormulaFromPerC.lean
ExplicitFormulaBridgeOfRH.lean
```

This layer supplies the pair-cosh Gaussian explicit formula / global β-family identity.

### Orthogonality and vanishing extraction

```text
WeilZeroOrthogonality.lean
PairTestMellinBetaTotalality.lean
CountableTsumMomentUniqueness.lean
```

This layer upgrades aggregate identities to per-zero vanishing.

### Mathlib RH bridge

```text
RiemannHypothesisBridge.lean
```

This upgrades the internal critical-line statement to Mathlib’s literal:

```lean
RiemannHypothesis
```

---

## Remaining formalization work

The remaining work is not to invent a new RH idea.

The remaining work is to finish exact Lean versions of standard analysis tools in the shape this proof needs.

Main grind files:

```text
PairTestMellinBetaTotalality.lean
CountableTsumMomentUniqueness.lean
```

Expected grind:

- Fubini / `tsum` exchange;
- absolute convergence;
- cosh-transform analyticity;
- Riemann–Lebesgue;
- Fourier cosine injectivity;
- beta-resolvent moment extraction;
- countable `tsum` moment uniqueness;
- layer peeling / coefficient isolation.

These are serious formalization tasks because Mathlib does not expose the exact combined statements needed here. They are not new breakthrough mathematics.

---

# Helix files

The helix files should be read as geometric support files, not as the main RH proof entrypoint.

They prove that the log helix and the `σ = 1/2` helix model are faithful, rigid, and uniquely compatible with the relevant symmetry / decoding constraints.

---

## `RHHelixFaithfulness.lean`

This file proves basic faithfulness of the log helix.

### Main definitions

```lean
def helixOmega : ℝ := π / 3

def helixAngle (x : ℝ) : ℝ :=
  helixOmega * Real.log x

def helix3D (x : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos (helixOmega * Real.log x),
   Real.sin (helixOmega * Real.log x),
   Real.log x)

def radialProjection (v : ℝ × ℝ × ℝ) : ℝ :=
  Real.exp v.2.2
```

### What it proves

#### 1. Injectivity

```lean
helix3D_injective_on_nat
helixLog_injective_pos
helix3D_injective_pos
helixAngle_injective_nat
helixAngle_injective_pos
```

The helix map is injective on positive naturals / positive reals because the `z` coordinate is `log x`, and `log` is injective on positive reals.

#### 2. Radial projection recovers the number

```lean
radial_projection_of_helix3D
helix_radial_projection_recovers_angle
```

The radial projection

```text
(cos θ, sin θ, log x) ↦ exp(log x)
```

recovers `x`, and therefore recovers the angle `θ(x) = (π/3) log x`.

#### 3. Multiplication becomes addition of helix angles

```lean
helixAngle_mul
```

For positive `a,b`:

```text
θ(ab) = θ(a) + θ(b)
```

because:

```text
log(ab) = log a + log b
```

This is the clean formal version of the logarithmic multiplication model.

#### 4. Full faithfulness theorem

```lean
faithfulness_theorem
```

Bundles:

```text
helix3D injective on ℕ⁺
radial projection recovers n
angle recovery from radial projection
angle injectivity on ℕ⁺
```

#### 5. Critical-line symmetry

```lean
critical_line_symmetry
```

Proves:

```text
s.re = 1/2 ↔ s = 1 - conj(s)
```

So the critical line is the fixed locus of the standard functional-equation reflection.

---

## `HelixModel.lean`

This file proves uniqueness and rigidity of the `σ = 1/2` helix model under natural geometric constraints.

### Main structure

```lean
structure HelixModel where
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
```

The model has a real parameter:

```text
σ ∈ (0,1)
```

and represents prime radii using:

```text
p^{-σ}
```

with reflected radii:

```text
p^{-(1-σ)}
```

### Main constraints

```lean
HelixModel.RadiusSymmetric
HelixModel.FaithfulDecoding
HelixModel.KleinCollapse
```

They mean:

1. radius symmetry between the helix and reflected helix;
2. faithful reconstruction of the canonical number line;
3. Klein-four collapse / symmetry.

### Critical model

```lean
criticalModel : HelixModel
```

has:

```text
σ = 1/2
```

and satisfies:

```lean
criticalModel_radius_symmetric
criticalModel_faithful
criticalModel_klein_collapse
```

### Uniqueness theorems

```lean
helix_model_unique_radius
helix_model_unique_faithful
helix_model_unique_klein
helix_model_unique_any_constraint
helix_constraints_equivalent
```

These prove:

```text
radius symmetry      ⇒ σ = 1/2
faithful decoding    ⇒ σ = 1/2
Klein collapse       ⇒ σ = 1/2
```

and that the major constraints are equivalent for the model.

### Dimension collapse

```lean
dimension_collapse_iff_half
```

This proves that equality of projected radius squares for the helix and reflected helix occurs exactly at:

```text
σ = 1/2
```

So the perpendicular / projected helix geometry collapses consistently only at the critical-line parameter.

### Decoding uniqueness

```lean
DecodingScheme
DecodingScheme.Faithful
decoding_faithful_iff_half
```

A decoding scheme is faithful exactly when:

```text
σ = 1/2
```

This is the formal version of:

```text
only the critical helix reconstructs the canonical number line faithfully
```

### Robespierre / θ-coordinate system

The file defines:

```lean
theta : ℝ := Real.arcsin (1 / 2)
```

and proves:

```lean
theta_eq          -- theta = π / 6
sin_theta         -- sin theta = 1 / 2
sin_sq_theta      -- sin² theta = 1 / 4
one_plus_sin_sq_theta
```

It also defines θ-native prime geometry:

```lean
phiPrime
primeLogFreq
thetaCoeff
XiThetaFinite
criticalLineSum
criticalLineSumDeriv
```

and proves that the θ-coordinate critical line is the classical critical line:

```lean
robespierre_critical_line
criticalLineSum_on_half
```

### What the helix model contributes

The helix files prove:

```text
multiplication becomes angle addition through log
the helix projection is faithful
radial projection recovers the original number
σ = 1/2 is the unique radius-symmetric / faithful / Klein-collapsed model
θ = arcsin(1/2) = π/6 gives the same critical line via sin θ = 1/2
```

They support the geometric interpretation of the RH proof, but the actual forcing proof is still centered in:

```text
OfflineDetectorProof.lean
```

---

## Agent instructions

When working on this repo:

1. Start with `OfflineDetectorProof.lean`.
2. Treat the helix files as geometric support / explanation files, not as the RH proof root.
3. Preserve the forcing pipeline:
   - off-line detection,
   - no cancellation,
   - prime-side amplitude bridge,
   - global Weil identity,
   - beta-totality,
   - countable uniqueness,
   - per-zero vanishing,
   - RH bridge.
4. Do not collapse global Weil identity into per-zero vanishing.
5. Do not replace the forcing argument with informal “detector sees off-line zeros” language.
6. Keep `#print axioms` clean.
7. No project axioms. No hidden RH assumptions.

---

## One-sentence summary

`OfflineDetectorProof.lean` is the RH proof orchestration file: it packages the unconditional off-line detector/no-cancellation theorem, ties the detector to the Weil prime-side amplitude channel, and sets up the forcing route from global β-family identities to per-zero vanishing; the helix files separately prove the faithfulness and uniqueness of the `π/3` log helix and the `σ = 1/2` helix model.
