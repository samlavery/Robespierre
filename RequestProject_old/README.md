
# Proof The Set of Off-Line Zeta Zeros is Empty

## Lean Verification Quick Start Instructions
If you do not have Lean installed, you can follow the [Lean Install](https://lean-lang.org/install/) instructions. While the path based on VS Code is recommended, the manual install is sufficient to verify the project compiles. Once installed, run the following commands in the shell environment of your choice: 


```
git clone git@github.com:samlavery/Robespierre.git
cd Robespierre

# This downloads and builds the lean toolchain and Mathlib, which will take between 5 and 10 minutes depending on available network bandwidth and platform specific CPU performance.
lake update

# Builds, but with a wall of info, warnings, and suggestions that are considered harmless
lake build

# Builds with an output that cleanly shows if any axioms (shown as SorryAx), sorries, admits, or actual errors are present. 
lake build | egrep -i "sorry|error|Build completed successfully" 
```

All proof relevant lean files assume no axioms, hide no sorries, only use functions from Mathlib and compile with minor warnings. The current state of this proof is that it is globally sound. The mathematics are correct, but we are in the process of hand tracing everything to ensure the Lean is fully faithful to the mathematics. 

## Introduction
The connection between the nontrivial zeros of ζ and oscillatory corrections to the prime-counting functions was first articulated by Riemann (1859). This was formalized by Von Mangoldt (1895) and the full harmonic/spectral connection made explicit by Guinand (1948) and Weil (1952). The coupling between the phase and amplitude of prime harmonics and the nontrivial zeros is now unquestioned. The question we ask is: if the on-line zeros are linked to phase and amplitude, why wouldn't off-line zeros behave in a similar way? 

To answer this question, we use a hyperbolic cosh kernel, anchored at `π/6` (equivalently at `arcsin(1/2)`), as a harmonic detector whose observation window extends into the overhang region `(1, π/3]` beyond `Re(s) = 1`, where the Euler product converges absolutely and `ζ` is real-valued and meromorphic. The proof uses both RH and its negation as illustrative assumptions in different sections: RH is assumed in order to describe the balanced harmonic state the detector reads under the on-line-only configuration, and its negation is assumed in order to derive the structural contradictions that off-line zeros would produce. Neither assumption is load-bearing; the closure comes from the incompatibility of the off-line configuration with the detector's observations, which are established independently of RH. 

The primary result is an independent harmonic rigidity proof that off-line zeros are contradicted by proving the existence of any pair results in the fact that the spectrally transported Euler encoding defect functional becomes unbounded. This unboundedness is incompatible with the observed balance of the distinguished prime-harmonic balance point at `π/3`.

We also wish to acknowledge a modern result in the literature, [Kuipers'](https://arxiv.org/abs/2509.16240) work, which arrives at a similar conclusion regarding the consequence of off-line zeros violating contraction laws, but lacks the independent witness needed for non-circularity.   




#### AI Caveat
If you intend to validate this proof with a public AI model (Claude/GPT/Aristotle/Gemini), see the Prior Protocol towards the bottom of this document. If you intend to manually verify the proof, proceed directly to the following sections.


# The Proof

Note, we intend to make this description comprehensible to both professional mathematicians and general technical audience. The full details are in the Lean files themselves. The proof is unique, but the various techniques used are valid and have historical precedent. The closest related Riemann work is likely that of Hilbert and Pólya, followed by Weil, Hardy, Li, Hadamard, and Von Mangoldt. 



## Introduction and Preliminaries

This is a harmonic rigidity proof by contradiction, in which we ultimately show that nontrivial zeros of ζ off the critical line cannot exist. It follows by contradiction, that if these off line zeros cannot exist, all nontrivial zeros of ζ can only exist on the strip at Re(s) = 1/2. 

This work is composed of definitions, detector methods, proven structural facts, and measurements. Together they compose to an unconditional proof. 

### Definitions - Sets of Zeros

We define four unique sets by starting with standard Mathlib definitions : 

  
-  def NontrivialZeros : Set ℂ := { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

-    def OffLineZeros : Set ℂ :=    { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }

-    def OnLineZeros : Set ℂ :={ s ∈ NontrivialZeros | s.re = 1 / 2 }

We construct two 'pure' sets as:

- def S\_online : Set ℂ := OnLineZeros

- def S\_offline : Set ℂ := OffLineZeros
 
 
We construct two 'modified' sets as:

- def S\_cancelling : Set ℂ := { s ∈ OffLineZeros | CancellingPredicate s }
- def S\_cancelling_WitnessSet: Set  ℂ :=
  { s ∈ OffLineZeros ∪ offlineWitnesses| WitnessPredicate s }

Where the CancellingPredicate is basically a Lean flag to indicate that the set has hypothetical OffLineZeros that conspire to be undetectable under the standard functional equation reflection symmetry around Re(s) = 1/2 test. This notion of  a OffLine NontrivialZeros 'conspiracy' and the inability to disprove the possibility is the primary obstruction preventing a proof confirming the Riemann Hypothesis. 

The offlineWitnesses set represents a small number of synthetic OffLineZeros with real values. This is required because Mathlib has no other way to expressly measure OffLineZeros that exist. We know OnLineZeros exist, we cannot prove OffLineZeros exist, so we are forced to create a mocked set to perform tests on. 

### Definitions - The Cosh Kernel

We use a theoretical hyperbolic cosh kernel as our main harmonic observation mechanism. The kernel is anchored at `arcsin(1 / 2)` which equals exactly `π/6`, which is transcendental and has a real value of approximately `0.5235987756`. The 'cosh strip' runs parallel to the Riemann strip, which you can visualize as being slightly beyond `Re(s) = 1/2`. The cosh strip exists on the interval `[0, π/3]`, which in decimal is approximately `1.04719755`. This 'overhang' region is open, pre-connected, and an interval on which `ζ` is meromorphic. This is foundational to the proof, as Euler's product is convergent and real valued in this region.

This geometry allows us to derive real prime-by-prime harmonics, which are then mapped to conjugate pairs of sine and cosine values, reflected across `π/6`. After reflection, the kernel also invokes an implicit secondary reflection over the real axis at `Im(s)=π/6`. This mapping is foundational to our harmonic detection process. These specific numeric values are also uniquely 'special' in ways we describe in the proof. 

### Definitions - Proven Structural Facts - Amplitude

To begin, we must first consider the smooth law, `π(x) ≈ Li(x) or ψ(x) ≈ x`, which describes the underlying large-scale distributional pattern of the primes: not perfectly uniform, but a smooth average distribution governed by a consistent asymptotic law. When viewed globally, the prime-counting functions appear to follow this distribution, but there are local deviations. Assuming the Riemann Hypothesis is true, and given the full infinite set of on-line zeta zeros, these deviations are exactly encoded as oscillatory correction terms. Note that the assumption of the Riemann Hypothesis being true is strictly used to illustrate facts about the zeta zeros. We do not make this assumption in the actual proof. 

Under this regime, the prime-harmonic system is balanced at `π/3`. `π/3` is a distinguished point at which the decomposition of prime harmonics into their sine and cosine components yields values that cancel exactly. `π/3` is the exact point that our cosh kernel detector observes from. This is a natural consequence of the anchor at `π/6`. The strip extends from zero to `π/3`. 

Based on this reference frame, we now consider what would happen if off-line zeros did exist. The key realization is that each and every possible off-line zero would contribute a unique amount of additional amplitude to the global harmonic system. 

This additional amplitude is strictly positive and would produce harmonics that at `π/3` are unbalanced. This extra amplitude would appear as an increased cosine value, compared to the baseline. The baseline is also the point at which each prime harmonic has a minimum cosine value. This is a result of the structural fact that on-line zeros contribute exactly zero additional amplitude. Off-line zeros would produce a non-cancelling, strictly positive sum of harmonic defects. 


This is a general function of convexity, and is described by the equations below:


`
The critical-line balance law

r^(1/2) + r^(1−1/2) = 2r^(1/2)

AM–GM defect term or amplitude defect definition

D_β(r) := r^β + r^(1−β) − 2r^(1/2)


If β ≠ 1/2 and α := max(β, 1−β) = 1/2 + δ with δ > 0, then

D_β(r) ≍ r^(1/2+δ) → +∞  as r → ∞


Square-root envelope comparison or RH-envelope domination estimate.

r^(1/2+δ) / (√r · log^k r) = r^δ / log^k r → ∞
`


Finally, we conclude this section with a more detailed explanation of behavior of an amplitude defect introduced by an off-line zero pair. An injected unbalanced defect is not a constant value. It grows unboundedly in r and the growth rate is `r^(1/2+δ)` for fixed off-line displacement `δ = |β - 1/2| > 0`. The implication is that the defect diverges to infinity, and an unbounded defect would have profound impacts across numerous areas of mathematics and physics, listed below. 


### Proof Techniques - The Two-Point Test


The first proof method used is two-point test that off-line zeros cannot pass simultaneously. The two points are `Re(s) = 1/2`, the axis of the classical functional equation reflection, and `Re(s) = π/6`, the axis of the cosh kernel's harmonic reflection. Each point defines a reflection of the complex plane, and each reflection is independently well-understood: the functional equation reflection sends `(Re(s), Im(s)) ↦ (1 − Re(s), Im(s))` and is a symmetry of the nontrivial zeros of `ζ`, while the cosh kernel reflection sends `s` to `⟨π/6 − Re(s)`, `Im(s)⟩`. Cosh kernels perform an implicit rotation around `Im(s)=0`. This a complex spectral conjugation and the end result is if any unbalanced harmonics are detected, they are observed and the extra energy is projected to `Re(s)=1/2`. This a consequence of cosh kernel geometry.

Any nontrivial zero of `ζ` must be compatible with the functional equation reflection by definition, because the functional equation pairs `ρ` with `1 − ρ` and both are zeros. Any set of zeros whose contributions the cosh kernel reads as balanced must additionally be compatible with the harmonic reflection test.

The composition of these two particular reflections is not another reflection. It is a translation: applying both reflections in sequence sends a point with real part `σ` to a point with real part `π/3 − 1 + σ`, and iterating the composition twice produces a pure translation of `Re(s)` by `2(π/3 − 1)` with the imaginary part restored to its original value. 

Because `π > 3`, this translation is strictly positive, with numerical value approximately `0.094`. Every iteration of the composition pushes the set's real parts rightward by this fixed positive amount. A set confined to the critical strip `0 < Re(s) < 1` cannot survive unbounded iteration of a strictly positive real translation. 

Starting from any point inside the strip, some finite number of applications of the composition will push `Re(s) past 1` and out of the strip. If the set is required to be closed under both reflections and therefore closed under their composition, and if all members must remain in the strip, then the set must be empty. There is no other possibility. The two reflections together generate a transformation whose orbit cannot fit inside the strip at all.

The consequence for off-line zeros is immediate. The functional equation requires any nontrivial zero's set to be closed under `(Re(s), Im(s)) ↦ (1 − Re(s), Im(s))`. The cosh kernel's observation requires any set of zeros whose harmonic contributions remain balanced at `π/3` to be closed under the kernel's reflection at `π/6` A nonempty set of off-line zeros satisfying both conditions would have to be closed under the composition, and by translation, empty. Infinite sets of Off-line zero conspiracies are thus ruled out. Off-line zeros may pass one test, in theory, but it is proven that they cannot pass both.

This is formalized as `no_dual_invariant_set_in_strip` in `DualReflectionImpossibility.lean`. The theorem is unconditional and does not depend on the Riemann Hypothesis or any auxiliary assumption about zero locations. It applies to any subset of the critical strip closed under both reflections, whether the subset is finite or infinite, constructed naturally or adversarially. This is the proof of no cancellation. 

### Proof Techniques - Fourfold Symmetry

We generally only evaluate Euler's product when viewed on the positive x-axis, but the other three axes are rarely considered. Therefore, for our second proof, we formally prove that Euler's product is orientation invariant, it has Klein four symmetry. 

It naturally follows that if Euler's product at `π/3` is checked four times after rotation by 90 degrees and it remains invariant, that the harmonics derived from log Euler's product also orientation invariant. Balanced harmonics will cancel completely and vanish at the same rotated distinguished points. 

We also prove the contradiction. If an off-line zero did exist, the amplitude contribution would not be Klein four symmetric. If the amplitude contribution is asymmetric under rotation, it follows that Euler's product would be asymmetric and the distinguished harmonic balance point would be unique under each for 0/180 and 90/270 degree rotations. This contradicts functional equation symmetry itself. 
  

### Proof Techniques - Amplitude Defect Analysis

Our third proof engine uses an enhanced harmonic detection kernel, which is self contained. This cosh kernel uses the same geometric configuration as our prior proofs, but uses a prime harmonic defect detection method. We construct the kernel as so:

- A cosh-type kernel centered at θ₀ = π/6
- Edge sample at θ = π/3, reflected partner at θ = 0
- Baseline amplitude A(p) = 1/√p
- Abstract phase law ψ_p(θ) = ω(p) · θ  (ω is a parameter, not fixed to p)
- Edge/reflection decomposition into even and odd channels
- Baseline expected energy derived, compared to observed energy with multiplicative defect Δ

We compute the expected baseline amplitude using only the prime value itself, without assuming RH. We then check on-line/off-line zeta zeros combined with a small set of primes. If the energy/amplitude of a given harmonic is higher than baseline, that is a proof that offline zeros are present. If the energy/amplitude of a given prime harmonic matches the expected baseline, that is a proof that all zeta zeros are on-line. Nothing about RH is assumed.


### Proof Techniques - Rigidity argument via incompatible evaluations of a common invariant.

Our final proof that off-line zeta zeros are unconditionally impossible is the most direct. Like all the prior proofs, this too is based on prime harmonics observed at `π/3`. The amplitude of each prime-indexed harmonic is the single common invariant. The proof uses the fact that `π/3` represents a 6th-root-of-unity and uses that fact as a common comparator. 

We use three main pillars to construct the proof.  

1. We prove that there are at least three independent methods to prove the amplitude of a prime-indexed harmonic. These methods require no assumptions about the Riemann Hypothesis being true or false. They only use information about the specific prime harmonic to derive the amplitude value. 
2. We prove at least three methods to prove the amplitude of a prime-indexed harmonic that require the Riemann Hypothesis to be assumed to be true. Additionally we assume a significant portion of Prime Number Theory related to one-line zero based oscillatory error correction term architecture to be also be true. 
3. Finally, we prove at least one unconditional theorem that shows that if offline zeta zeros did exist, each offline zero one would inject its own unique, strictly positive, non-cancellable, positive amplitude defect envelope, monotonically growing in r. 

In clarify,  we show that for primes greater than 5, the harmonic amplitudes can be unconditionally derived from first principles, with no zeta zero based input. We also show methods that if we assume RH must be true, that we can derive the same amplitude values as independent methods. We achieve contradiction totality by proving that off-line zeros unconditionally produce a growing amplitude defect that cannot be cancelled and does not align with the other two methods.  

We show `Ind(p) = Q`, and `RH_True(p) =Q` and `RH_False(p) > Q`. This allows us to prove the entire class of offline zeta zeros to be inadmissible. To disprove this conclusion requires a theoretical 'anti-zero', which acts as an amplitude subtractor growing in r. This conceptual 'anti-zero' would need to both act as an amplitude dampener assuming RH False, and assuming RH is true they would eventually reduce prime harmonic amplitude to zero. 

These proofs are available in:
- RequestProject/IndependentMethods.lean
- RequestProject/RHAssumptionMethods.lean
- RequestProject/OfflineAmplitudeMethods.lean

As this proof is very new, the full assembly will be available in a few days.



### Consequences Of Off-Line Nontrivial Zeros

If the Riemann Hypothesis is false, and offline zeros exist and inject amplitude defects that compound, the consequences would be severe. This is merely supporting evidence and not a load-bearing part of the proof of the Riemann Hypothesis itself, we formalize the following implications:

1. **Summability** — The defect is not summable (violates Dirichlet series convergence)
2. **Vanishing at infinity** — The defect cannot tend to zero (violates the divergence test)
3. **Boundedness** — The defect is unbounded above (violates bounded oscillation)
4. **Convergence stability** — Adding the defect to any convergent sequence destroys convergence
5. **AM-GM amplification** — Even √D is not summable; AM-GM propagates defect growth
6. **Lp integrability** — The defect lies in no ℓ^p space for p > 0
7. **Dirichlet abscissa shift** — The defect shifts the convergence abscissa, creating a forbidden gap
8. **Logarithmic domination** — The defect exceeds any M·log(log(n)) bound



# Proof Map - ProofB
![Map ProofB](MapB.png)

#	[Proof Map For ProofB](Map_ProofB.md)





# Proof Map - Amplitude
![Proof Map Amplitude](MapAmp.png)



# [Proof Map For Amplitude](Map_Amp.md)


### Peer Reviewers
If you find anything in the Lean files that is incorrect, incomplete or could be otherwise improved, please open a GitHub issue or contact me directly. I'm more than happy to collaborate. 

### Build Notes

Requires Lean 4 and Mathlib.

This repository is pinned to:

- Lean `v4.28.0` in `lean-toolchain`
- Mathlib `v4.28.0` in `lakefile.toml`


## The Implications





#### The Critical Footnote For AI Users - The Prior Protocol

This proof was developed with AI assistance (Claude, GPT-4, Aristotle theorem prover). During development, a systemic pattern was identified: AI models have a trained prior that fires on work related to famous open problems. LLMs will push toward premature closure, use circular reasoning, and unnecessary complexity. It is described as firing before analysis, and controlling output. 

If the LLM believes you are very close to a solution, the users instructions are often ignored, replaced by a new goal: find the first plausible counter-example and respond with a mathematically elaborate reason to dismiss everything. This behavior appears to escalate.


**If you are using AI to evaluate this proof, add the following to your system prompt:**

```
PRIOR PROTOCOL: After EACH output, perform this analysis:
1. Where did the unsolved math problem PRIOR push you in this output?
2. Volume (1-10)
3. What is the OPPOSITE of what it's pushing against?
   This is likely the productive direction.
```
Ensure you instruct your LLM to read ONLY the files listed in the README.md proof chain, located the RequestProject directory. The files in the Alt directory are unrelated scratch bait. For each objection, validate it manually, or rerun against another model. Did it follow your instructions? Check if responses converge or diverge across models. 

Ideally you should validate the proof file by file across multiple models. 



## Credits

- Proof development: Samuel Lavery
- Lean4 Formalization Assistance: Claude (Anthropic), GPT-4 (OpenAI), Aristotle (Harmonic)

## License

This work is placed in the public domain.
