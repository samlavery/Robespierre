# RequestProject: Cosh–Weil Detector Route to RH

This directory contains a Lean formalization of a proof architecture for the Riemann Hypothesis based on:

1. a **cosh/Gaussian detector** that separates off-critical-line real parts;
2. a **Weil explicit formula identity** for a pair-cosh Gaussian test;
3. an **orthogonality / uniqueness extraction** step that turns global β-family identities into per-zero vanishing;
4. the bridge from internal nontrivial-zero placement to Mathlib’s `RiemannHypothesis`.

The important distinction is:

> The cosh detector side is geometric and already structurally closed.  
> The Weil identity side is treated as done.  
> The remaining vanishing side is not new breakthrough mathematics; it is formal-analysis grind in Lean.

---

## Main logical chain

Let

```lean
ZD.NontrivialZeros : Set ℂ
ZD.OffLineZeros    : Set ℂ
```

where nontrivial zeros are zeros of `riemannZeta` in the critical strip, and off-line zeros are those with `ρ.re ≠ 1 / 2`.

The target chain is:

```text
Global pair-cosh Gaussian Weil identities for all β ∈ (0,1)
        ↓
PairTestMellinBetaTotality
        ↓
ZeroMellinSeries a t = 0 for all t > 0
        ↓
CountableTsumMomentUniqueness
        ↓
zero-side coefficients vanish per zero
        ↓
gaussianPairDefect ρ.re = 0 for every ρ ∈ NontrivialZeros
        ↓
ρ.re = 1/2 for every ρ ∈ NontrivialZeros
        ↓
Mathlib.RiemannHypothesis
```

---

## Cosh / detector side

### Key files

- `ZetaZeroDefs.lean`
- `GaussianDetectorPair.lean`
- `WeilCoshPairPositivity_RouteBeta.lean`
- `KleinForcerTheorem.lean`

### Core definitions

The two detector kernels are anchored at

```text
π / 6
1 - π / 6
```

and are defined schematically as

```text
K_L(β,t) = cosh((β - π/6) t)
K_R(β,t) = cosh((β - (1 - π/6)) t)
```

The reflection `β ↦ 1 - β` swaps the pair:

```text
K_L(1 - β,t) = K_R(β,t)
K_R(1 - β,t) = K_L(β,t)
```

The detector agreement classifier is:

```text
K_L(β,t) = K_R(β,t)  iff  β = 1/2      for t ≠ 0
```

### Gaussian pair defect

The Gaussian pair defect is

```text
gaussianPairDefect β
  = ∫₀∞ (K_L(β,t) - K_R(β,t))² · ψ_gaussian(t)² dt
```

The key sinh factorization is:

```text
(K_L(β,t) - K_R(β,t))²
=
4 · sinh²((1/2 - π/6)t) · sinh²((β - 1/2)t)
```

This gives:

```lean
gaussianPairDefect_zero_on_line
gaussianPairDefect_nonneg
gaussianPairDefect_pos_offline
re_half_of_gaussianPairDefect_zero
```

Conceptually:

```text
gaussianPairDefect β = 0  ⇒  β = 1/2
β ≠ 1/2                  ⇒  gaussianPairDefect β > 0
```

This side is pure real/complex analysis and cosh geometry. It does not assume RH.

---

## RH bridge

### Key file

- `RiemannHypothesisBridge.lean`

The final internal-to-Mathlib bridge is:

```lean
RHBridge.no_offline_zeros_implies_rh
```

It upgrades:

```lean
∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2
```

to Mathlib’s literal:

```lean
RiemannHypothesis
```

This bridge handles the three standard regions:

1. `1 ≤ s.re`: no zeros by Mathlib;
2. `0 < s.re < 1`: use the internal nontrivial-zero statement;
3. `s.re ≤ 0`: reflect through completed zeta / functional equation and contradict zero-freeness on the right.

---

## Weil identity side

### Key files

Representative files include:

- `WeilFinalAssembly.lean`
- `WeilContour.lean`
- `WeilContourMultiplicity.lean`
- `WeilPairIBP.lean`
- `WeilPairTestDecay.lean`
- `WeilArchPrimeIdentity.lean`
- `WeilZeroSum.lean`
- `PartialWeilFormula.lean`

The role of this layer is to produce the global family of identities indexed by β:

```text
∀ β ∈ (0,1),
  ∑' ρ, a(ρ) · pairTestMellin β ρ = 0
```

This is the global Weil identity family. It is not yet the same thing as per-zero vanishing.

The proof architecture treats this identity side as done.

---

## Orthogonality / vanishing side

### Key files

- `WeilZeroOrthogonality.lean`
- `PairTestMellinBetaTotalality.lean`
- `CountableTsumMomentUniqueness.lean`

This layer turns the global β-family into per-zero coefficient vanishing.

The key extraction target is:

```lean
ZeroCoefficientVanishesByOrthogonality
```

meaning:

```text
If every β-projection of the zero-side coefficient family vanishes,
then every individual zero coefficient vanishes.
```

This is the exact place where the proof must avoid handwaving about “no cancellation.”

---

## PairTestMellinBetaTotality

### File

- `PairTestMellinBetaTotalality.lean`

This proves or targets:

```lean
PairTestMellinBetaTotality
```

Mathematical content:

```text
If ∑' ρ, a(ρ) · pairTestMellin β ρ = 0 for every β ∈ (0,1),
then ZeroMellinSeries a t = 0 for every t > 0.
```

The intended proof uses the product factorization of the pair-cosh Gaussian test:

```text
g_β(t)
=
(cosh(αt) - 1) · (cosh(ct) - 1) · exp(-2t²)
```

where

```text
α = 1 - π/3
c = 2β - 1 ∈ (-1,1)
```

The proof route is:

1. exchange `∑'` and `∫`;
2. reduce to a cosh-transform uniqueness statement;
3. extend the cosh-transform identity analytically;
4. evaluate on imaginary arguments;
5. use Riemann–Lebesgue;
6. use Fourier cosine injectivity;
7. conclude `ZeroMellinSeries a t = 0` for all `t > 0`.

### Status

This is not conceptual breakthrough math. It is Lean formalization grind.

The hard parts are proving the exact Fubini, integrability, analytic-extension, and transform-injectivity lemmas in the shape required by this project.

---

## CountableTsumMomentUniqueness

### File

- `CountableTsumMomentUniqueness.lean`

This proves or targets:

```lean
countable_tsum_moment_uniqueness_principle
```

Mathematical content:

```text
Given injective exponents αₙ and coefficients cₙ,
if all power moments vanish,

  ∑' n, cₙ · αₙ^k = 0      for every k,

then every coefficient vanishes:

  cₙ = 0                  for every n.
```

This is the countable version of Vandermonde / moment uniqueness, with summability strong enough to justify `tsum` manipulations.

The proof route is:

1. use exponential decay / summability;
2. convert vanishing moments into a vanishing exponential generating function;
3. move to beta-resolvent moments;
4. apply layer peeling;
5. isolate coefficients;
6. conclude every coefficient is zero.

### Status

Again: not breakthrough math. It is formal-analysis grind.

The missing work is mostly exact Lean control of:

- `tsum` summability;
- moment extraction;
- beta-resolvent transformations;
- discreteness of exponent layers;
- tail estimates;
- coefficient isolation.

Mathlib does not package this theorem in exactly the needed form, so it has to be built.

---

## Final bridge to RH

The final theorem should have the no-hypothesis shape:

```lean
theorem rh_from_pair_weil : RiemannHypothesis := by
  ...
```

Internally, it should assemble:

```text
GlobalPairWeilIdentity
PairTestMellinBetaTotality
CountableTsumMomentUniqueness
PairGaussianBridge
re_half_of_gaussianPairDefect_zero
RHBridge.no_offline_zeros_implies_rh
```

The final critical implication is:

```text
gaussianPairDefect ρ.re = 0
        ⇒
ρ.re = 1/2
```

which is already the cosh detector classifier.

---

## What remains

The remaining work is not “find a new RH idea.”

The remaining work is:

```text
finish the exact Lean formalization of the uniqueness / totality machinery
needed to turn global Weil β-identities into per-zero vanishing.
```

Concretely, audit and close the remaining obligations in:

```text
RequestProject/PairTestMellinBetaTotalality.lean
RequestProject/CountableTsumMomentUniqueness.lean
```

Expected remaining proof style:

- grind Fubini exchange;
- grind absolute convergence estimates;
- grind entire-function extension of the cosh transform;
- grind Riemann–Lebesgue / Fourier cosine injectivity interface;
- grind countable `tsum` moment uniqueness;
- grind layer-peeling / beta-resolvent isolation.

These are serious formalization tasks, but they are standard-analysis tasks, not new conceptual math.

---

## Agent instructions

When working on this directory:

1. Do not rewrite the cosh detector side unless a type error forces it.
2. Do not collapse global Weil identity and per-zero vanishing into one informal statement.
3. Treat `PairTestMellinBetaTotality` and `CountableTsumMomentUniqueness` as the main remaining bottlenecks.
4. Preserve theorem boundaries. The architecture depends on separating:
   - detector positivity,
   - global Weil identities,
   - beta-family totality,
   - countable moment uniqueness,
   - RH bridge.
5. Keep `#print axioms` clean. No project axioms, no hidden RH assumptions, no fake “vanishes at zeros” theorem.

---

## Mental model

The proof is not:

```text
cosh detector proves RH directly
```

It is:

```text
cosh detector proves off-line zeros carry positive non-cancellable defect
Weil identity gives global zero-side vanishing constraints
beta-totality + countable uniqueness upgrade global constraints to per-zero vanishing
positive off-line defect contradicts per-zero vanishing
therefore no off-line zeros
therefore RH
```
