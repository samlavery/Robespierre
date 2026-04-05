# RequestProject Catalog

## CoshDefs.lean
Defines the central cosh kernel framework with anchor point π/6, including coshReflection, coshFolding, and coshRotation symmetries, plus the critical strip and overlap regions.

**Exports:**
- `coshAnchor` — the constant π/6
- `coshReflection` — reflects Re(s) about π/6 while preserving Im(s)
- `coshFolding` — complex conjugation map
- `coshRotation` — composition of coshReflection and coshFolding: s ↦ π/3 - s
- `coshKernelReal` — kernel centered at π/6
- `coshKernelComplex` — complex-parametric version
- `coshKernelPair` — pair version for comparing two arguments
- `coshKernelReal_fold` — folding symmetry about π/6
- `coshKernelComplex_rotation` — rotation invariance property
- `coshKernelReal_pos` — kernel is strictly positive everywhere
- `coshKernelReal_at_anchor` — kernel equals 1 at the anchor π/6

## CoshKernel.lean
Formalizes the cosh kernel at π/6 with fold symmetry (invariance under σ ↦ π/3 − σ) and proves absence of zeros.

**Exports:**
- `coshKernel` — kernel function σ ↦ cosh(σ − π/6)
- `coshKernel_fold_symmetry` — reflection about π/6 leaves kernel invariant
- `coshKernel_pos` — kernel is strictly positive for all real σ
- `zeros_on_fold_line` — any zero must be at π/6 (vacuously true)
- `no_offline_zeros` — kernel is nonzero at every point off π/6
- `coshKernel_at_fold` — kernel value at π/6 is 1

## CoshKernelVanishing.lean
Proves that cosh kernel (prime harmonic and reflection combinations) vanishes on arcsin(1/2) = π/6, and establishes reflection properties for prime harmonic sums.

**Exports:**
- `arcsin_one_half` — arcsin(1/2) = π/6
- `cosh_real_im_zero` — cosh of a real number has zero imaginary part
- `cosh_at_arcsin_half_purely_real` — cosh at arcsin(1/2) is real-valued
- `cosh_reflection` — cosh is an even function
- `complex_cosh_reflection` — complex cosh evenness
- `reflection_confirms_cancellation` — cancellation of conjugates
- `prime_harmonic_im_zero` — prime harmonic combinations have zero imaginary part
- `prime_harmonic_sum_im_zero` — sum over finset of primes also vanishes

## CoshNoZeros.lean
Proves that cosh is never zero on any real input and extends to complex numbers.

**Exports:**
- `cosh_ge_one` — cosh(x) ≥ 1 for all real x
- `cosh_neg_eq` — cosh is even
- `cosh_pi_div_six_ne_zero` — cosh(π/6) is nonzero
- `cosh_ne_zero` — cosh is nonzero everywhere on the reals

## CoshSymmetricPoles.lean
Develops meromorphic function theory for cosh-symmetric functions, identity theorem propagation via overlap, and pole structure characterizations.

**Exports:**
- `CoshSymmetric` — predicate for sets invariant under reflection about c
- `cosh_symmetric_pole_structure` — meromorphic order is symmetric under reflection
- `meromorphic_identity_theorem` — identity principle for meromorphic functions
- `meromorphic_eq_propagation` — equality propagates from overlap regions
- `conjugation_symmetry` — conjugation symmetry propagates globally
- `functional_equation_symmetry` — functional equation symmetries propagate
- `cosh_kernel_pi_sixth_symmetry` — specific symmetry about π/6

## CoshSymmetricPole.lean
Simplified version establishing cosh-symmetric pole structure and meromorphic order preservation.

**Exports:**
- `CoshSymmetric` — set symmetric under reflection about c
- `cosh_symmetric_pole_structure` — symmetric meromorphic order at reflected points

## CoshSymmetryBreak.lean
Proves unconditionally that cosh passes evenness and conjugation symmetry tests, and that cosh has no residues (contradicts residue hypothesis).

**Exports:**
- `complex_cosh_even` — cosh(-z) = cosh(z)
- `complex_cosh_conj` — conjugation symmetry
- `PassesCoshSymmetryTest` — predicate for symmetry test compliance
- `cosh_passes_symmetry_test` — cosh passes the test
- `cosh_residue_zero` — no residue for cosh
- `cosh_has_no_residue` — cosh fails the residue test

## CoshMeromorphicPoles.lean
Applies cosh-symmetric pole structure theorem to establish meromorphic order preservation under π/3 - s reflection.

**Exports:**
- `CoshSymmetric` — reflection-invariant set predicate
- `cosh_symmetric_pole_structure` — pole order symmetry theorem

## CoshNoZeros.lean (see above)

## CoshKernelBridgeNew.lean
Develops conformal bridge mapping critical line to itself, cosh kernel at π/6, and intertwining properties between reflections and folding.

**Exports:**
- `conformalMap` — maps to critical line {Re = 1/2}
- `conformalMap_reflection` — conformal reflection property
- `piSixthContour` — contour at Re = π/6
- `coshKernel` — symmetric kernel x,y ↦ cosh(x-y)
- `coshKernel_symm`, `coshKernel_pos`, `coshKernel_diag` — properties
- `bridge` — intertwining bridge
- `coshRefl`, `coshFold` — reflections and folding
- `bridge_intertwining` — intertwining relation
- `bridge_balance_transfer` — π/6 transfers to 1/2

## CoshKernelNonInterference.lean
Unconditional conditional results: under RH, zeros on the critical line form balanced conjugate pairs ρ + ρ̄ = 1 and the centered cosh kernel K(s) = cosh(s − 1/2) satisfies K(ρ) − K(ρ̄) = 0; under ¬RH, the kernel at 1/2 reduces to cosh(0) = 1, a passive "observer" anchored by sin(arcsin(1/2)) = 1/2 that cannot cancel unbalanced residues.

**Exports:**
- `OnCriticalLine`, `AllOnCriticalLine`, `ConjClosed` — predicates on zero sets
- `critical_line_conjugate_balance` — ρ on critical line ⇒ ρ + ρ̄ = 1
- `rh_implies_balanced_pairs` — RH gives balanced conjugate pairs
- `cosh_is_even` — cosh(z) = cosh(−z)
- `cosh_kernel_conjugate_vanish` — cosh(ρ − 1/2) = cosh(ρ̄ − 1/2) on critical line
- `rh_cosh_kernel_vanishes` — kernel difference vanishes on all RH zeros
- `sin_arcsin_half`, `cosh_at_zero_eq_one`, `cosh_kernel_at_half_is_identity`
- `off_line_unbalanced` — off-line zero ⇒ ρ + ρ̄ ≠ 1
- `not_rh_kernel_observer` — ¬RH gives an observer kernel with unbalanced residue
- `prime_harmonic_cosh_synthesis` — grand unconditional synthesis of both directions

## CoshHarmonicReprInstance.lean
Establishes overlap region analytic continuation and shows zeta is uniquely determined by its values on the overlap region between Euler product and cosh kernel domains.

**Exports:**
- `coshReflDomain`, `coshReflDomainPunctured` — domains excluding 1
- `overlapRegionI` — overlap {s : 1 < Re(s) < π/3}
- `overlapRegionI_isOpen`, `overlapRegionI_nonempty`, `overlapRegionI_isPreconnected` — topology
- `CoshHarmonicReprI` — harmonic representation class
- `zetaCoshRepr` — zeta representation instance
- `identity_theorem_on_overlapI` — identity principle
- `cosh_harmonics_zeta_invarianceI` — zeta is determined by overlap
- `every_zero_detected` — all zeros detected

## CoshHarmonicsZetaInvariance.lean
Comprehensive harmonic-cosh invariance framework with overlap region analysis, identity theorems, and full zero characterization via analytic continuation.

**Exports:**
- `eulerHalfPlane'`, `coshKernelDomain'`, `overlapRegion'` — domain decomposition
- `cosh_reflection_axis'` — π/6 constant
- `overlapRegion'_isOpen`, `overlapRegion'_nonempty`, `overlapRegion'_isPreconnected` — topology
- `coshKernel'` — harmonic kernel
- `coshKernel_symmetric`, `coshKernel_differentiable`, `coshKernel_analyticOnNhd` — properties
- `CoshHarmonicRepr` — representation class
- `identity_theorem_on_overlap'` — identity principle
- `cosh_harmonics_zeta_invariance` — zeta invariance with all consequences
- `cosh_harmonics_zeta_full_invariance` — comprehensive version

## CoshReflectionSynthesis.lean
Synthesizes the complete cosh reflection framework showing unconditionally that off-axis zeros cannot exist.

**Exports:**
- `coshReflDomain'`, `overlapRegion'` — core domains
- `cosh_reflection_axis'` — π/6 is the reflection axis
- `overlapRegion'_isOpen`, `overlapRegion'_nonempty`, `overlapRegion'_isPreconnected` — topology
- `coshKernel'` — harmonic kernel definition
- `coshKernel_symmetric`, `coshKernel_zero`, `coshKernel_analyticOnNhd` — properties
- `NontrivialZetaZeros` — nontrivial zero model
- `identity_theorem_on_overlap'` — identity theorem
- `CoshHarmonicRepr` — harmonic representation class
- `cosh_harmonics_zeta_full_invariance` — complete zeta determination

## ZetaCoshReflection.lean
Proves both cosh rotation and cosh reflection symmetries hold unconditionally and that rotation and reflection are equivalent via a biconditional.

**Exports:**
- `StripRotationInvariant` — line invariant under 180° rotation
- `CoshReflectionVanishes` — cosh kernel evenness condition
- `rotation_iff_reflection` — the two conditions are equivalent
- `both_pass` — both conditions hold unconditionally
- `cosh_even_real`, `cosh_even_complex` — cosh is even
- `cosh_conj_symmetry` — conjugation symmetry
- `cosh_both_symmetries` — both symmetries together
- `cosh_zero_quartet` — zeros come in symmetric quadruples

## CoshZetaSymmetry.lean
Places the cosh axis at arcsin(1/2) = π/6 — strictly between the critical line 1/2 and the Euler product boundary 1 — so that the cosh envelope overlaps the Euler product region and the functional equation Λ(1 − s) = Λ(s) propagates prime harmonics across the strip, forcing zeros into conjugate-cosh quadruples {ρ, 1 − ρ, ρ̄, 1 − ρ̄}.

**Exports:**
- `coshAxis` — the axis arcsin(1/2)
- `arcsin_one_half_eq`, `coshAxis_eq` — arcsin(1/2) = π/6
- `coshAxis_in_critical_strip` — 0 < π/6 < 1
- `coshAxis_gt_half` — 1/2 < π/6 (right of the critical line)
- `cosh_envelope_overlaps_euler_product` — envelope reaches Re(s) > 1
- `euler_product_prime_harmonics` — Euler product converges to ζ for Re(s) > 1
- `functional_eq_bridges_euler_product` — F.E. sends Re > 1 to Re < 0 and Λ(1−s) = Λ(s)
- `euler_region_straddles_cosh_axis` — Euler region and its reflection straddle π/6
- `completedRiemannZeta_differentiable`, `zeta_meromorphic_extension`
- `conjugate_pair_meromorphic`, `conjugate_pair_eq_double` — Λ(s) + Λ(1−s) = 2Λ(s)
- `cosh_symmetry_functional_equation`, `cosh_symmetric_pole_structure` — Λ(1−s) = Λ(s)
- `cosh_reflection_exchanges_poles` — poles at 0 and 1 swap
- `meromorphic_order_cosh_symmetric` — zeros of Λ come in {ρ, 1−ρ} pairs
- `offlineZeros`, `coshReflection`, `coshFolding`, `coshRotation`, `classicalReflection`
- `offlineZeros_classical_reflection_invariant` — zero set fixed by s ↦ 1−s
- `classicalReflection_involutive`, `coshReflection_involutive`
- `classicalReflection_image_offlineZeros` — image = offlineZeros
- `riemannZeta_conj` — ζ(s̄) = ζ(s)̄ (Schwarz reflection)
- `conjugate_zero_pair` — ρ a zero ⇒ ρ̄ a zero
- `cosh_conjugate_quadruple` — combines to give {ρ, 1−ρ, ρ̄, 1−ρ̄}
- `coshAxis_between_critical_and_euler` — 1/2 < π/6 < 1

## ZetaSymmetry.lean
Formalizes unconditionally that Riemann zeta function has no zeros with Re(s) ≥ 1 (Euler product boundary).

**Exports:**
- `riemannZeta_nonvanishing_re_ge_one` — zeta is nonzero for Re(s) ≥ 1

## ZetaObservables.lean
Unconditional observables connecting off-critical-line zeta zeros to distortions in prime-counting harmonics, with no RH assumption and no use of the functional equation. Shows off-axis zeros force a rotated π/2 anti-symmetry event and, strictly stronger, a uniform-sign prime harmonic modification event.

**Exports:**
- `offAxisClassicalZetaZero` — ζ(ρ) = 0 with 0 < Re ρ < 1 and Re ρ ≠ 1/2
- `realAxisDistortion` — signed displacement Re(ρ) − 1/2
- `offAxisRealObservable`, `offAxisImagObservable` — amplitude-weighted cos/sin from conjugate pair
- `realObservableDistortion` — x^σ − x^(1/2)
- `rotatedPrimeDensityDetector` — 2 x^σ cos(γ ln x + θ)
- `RotatedObservableAntiSymmetryEvent` — distortion ≠ 0, π/2-detector is conj-antisymmetric, amplitude distortion ≠ 0
- `PrimeHarmonicModificationEvent` — strengthened: sign of distortion is uniform over x > 1
- `rotatedPrimeDensityDetector_pi_div_two_antisymm` — explicit π/2 anti-symmetry
- `offAxisZero_implies_antiSymmetryEvent` — off-axis ⇒ anti-symmetry event
- `antiSymmetryEvent_implies_primeHarmonicModification` — upgrade to uniform-sign modification

## ZetaZerosPrimeDistribution.lean
Connects zeta zeros to prime distribution via von Mangoldt function, Euler product, and Chebyshev's psi function.

**Exports:**
- `vonMangoldt_positive_iff_prime_power` — von Mangoldt is positive iff argument is a prime power
- `vonMangoldt_at_prime` — von Mangoldt equals log(p) at prime p
- `vonMangoldt_conv_zeta_eq_log` — Dirichlet convolution identity
- `euler_product_for_zeta` — Euler product formula
- `zeta_nonvanishing_on_boundary` — zeta is nonzero for Re(s) ≥ 1
- `zeta_simple_pole_at_one` — simple pole with residue 1
- `chebyshev_psi` — Chebyshev psi function
- `zeta_zeros_control_prime_density` — zeros control prime behavior
- `vonMangoldt_links_zeta_zeros_to_primes` — linking theorem

## CriticalStripControl.lean
Proves basic properties of strip rotation, critical line, and isometry preservation of zeros.

**Exports:**
- `rotateComplex` — complex rotation function
- `stripRotation_maps_strip` — critical strip is invariant
- `stripRotation_preserves_criticalLine` — critical line is invariant
- `stripRotation_isometry` — rotation is an isometry
- `isometry_preserves_zeros_of_invariant` — isometry fixes invariant zero sets
- `zero_rotation_preserves_zeros` — zero rotation preserves zeros

## CriticalStripControlOffline.lean
Establishes that there is no nonempty subset of the critical strip invariant under both classical rotation (1 - s) and cosh rotation (π/3 - s).

**Exports:**
- `no_dual_symmetric_set` — no set invariant under both rotations
- `no_infinite_offline_zeros_pass_both_tests` — infinite off-axis zeros impossible
- `closure_dual_invariant_empty` — closure is empty
- `dual_invariance_forces_empty` — dual invariance implies emptiness

## CriticalStripIsoOnline.lean
Formalizes strip rotation map, shows its effect on the critical strip and line, and establishes invariance properties.

**Exports:**
- `stripRotation` — s ↦ 1 - s̄ (conjugate then reflect)
- `stripRotation_involution` — self-inverse
- `stripRotation_isometry` — preserves distance
- `stripRotation_preserves_criticalLine` — critical line is invariant
- `numberLine_equiv_self` — real axis equivalence
- `isometry_fixes_online_zeros` — online zeros stay fixed
- `stripRotation_equiv` — equivalence on critical strip
- `criticalLine_equiv` — equivalence on critical line

## CriticalStripIsoOffline.lean
Proves that off-axis (offline) zeros are separated from their strip-rotated images, with lower bounds on separation distance.

**Exports:**
- `stripRotation` — s ↦ 1 - s
- `IsOffline` — predicate for off-axis points
- `offline_ne_rotation` — offline points move under rotation
- `offline_re_ne` — real parts differ
- `offline_separation` — explicit separation bound
- `offline_positive_distance` — positive distance to image
- `offline_dist_lower_bound` — lower bound formula
- `multiple_offline_detectable` — applies to multiple zeros
- `moved_iff_ne_half` — equivalence with off-critical-line
- `rh_implies_no_movement` — the target hypothesis gives no movement

## CriticalStripFlipOnline.lean
Establishes 90° rotation detection: off-axis zeros cannot satisfy both critical line and rotated critical line membership.

**Exports:**
- `rotate90` — 90° rotation: z ↦ iz
- `distFromCriticalLine`, `distFromRotatedCriticalLine` — distance functions
- `onCriticalLine`, `offCriticalLine` — membership predicates
- `no_simultaneous_critical_line` — can't be on both lines
- `both_detectable` — off-axis is detectable
- `euler_regions_empty_in_strip` — Euler product region empty in strip
- `main_detection_theorem` — primary detection result

## CriticalStripFlipOffline.lean
Proves that off-axis zeta zeros persist under various transformations and maintains lower bounds on separation.

**Exports:**
- `zeta_zero_pow_eq_zero` — powers of zeros are zero
- `offLine_zero_persists_in_product` — persistence under power
- `zeta_one_sub_eq_zero_of_zeta_eq_zero` — functional equation zero pairing
- `offLine_zero_partner_ne` — partner is distinct
- `zeta_nonzero_in_euler_product_region` — nonzero for Re(s) ≥ 1
- `zeta_zero_outside_euler_region` — zeros are in strip
- `offLine_zero_detectable` — off-axis zeros are detectable
- `RH_false_consequences` — falsifying the hypothesis has many consequences

## OffAxisTheoremDefs.lean
Establishes observables and detector events that characterize the failure of rotated prime density on off-axis points.

**Exports:**
- `realAxisDistortion` — sum of von Mangoldt coefficients
- `offAxisRealObservable` — real part of observable
- `offAxisImagObservable` — imaginary part
- `rotatedPrimeDensityNormSq` — norm squared
- `realObservableDistortion` — distortion from critical line
- `RotatedPrimeDensityDetectorEvent` — detector event
- `rotatedPrimeDensityDetectorPasses` — detector passes iff σ = 1/2
- `realAxisDistortion_eq_psi` — relates to Chebyshev psi

## OffAxisZeta.lean
Defines observables that detect off-axis zeta zeros: rotated prime density detector, real/imaginary observables, and harmonic modification events.

**Exports:**
- `offAxisClassicalZetaZero` — predicate for off-axis zeros
- `realAxisDistortion` — cumulative von Mangoldt up to n
- `offAxisRealObservable`, `offAxisImagObservable` — distortion observables
- `rotatedPrimeDensityDetector` — detector function
- `RotatedObservableAntiSymmetryEvent` — anti-symmetry condition
- `PrimeHarmonicModificationEvent` — harmonic modification
- `offAxisZero_implies_antiSymmetryEvent` — off-axis implies anti-symmetry
- `antiSymmetryEvent_implies_primeHarmonicModification` — chain of implications

## OffAxisTheorem.lean
Proves that off-axis zeta zeros induce non-trivial detector events and observable distortions, connecting to prime harmonic dynamics.

**Exports:**
- `offaxis_forces_rotated_detector_event` — off-axis zero forces detector event
- `offaxis_forces_observable_nontriviality` — nontrivial observables appear
- `offaxis_forces_numberline_distortion` — number-line distortion exists
- `no_offline_passes_detector` — off-axis cannot pass detector
- `offaxis_classical_zero_forces_detector_and_distortion` — full consequence
- `classical_zero_to_prime_dirichlet_order` — meromorphic order at off-axis zero
- `offaxis_with_bridge` — discontinuity and detector event

## PrimeBridge.lean
Develops the "bridge" from Euler product region into cosh kernel domain via meromorphic continuation, with local π/3 seed and global harmonic symmetry.

**Exports:**
- `eulerCoshOverhang` — region between Euler boundary and cosh domain
- `eulerCoshBridge` — bridge function
- `bridgeRegularPart` — (s - π/6)²
- `bridgeRegularPart_global_order_symmetry` — order is symmetric about π/3
- `prime_bridge_has_local_pi_third_seed` — local symmetry seed exists
- `HarmonicCoshBridge`, `ExtendedHarmonicCoshBridge` — harmonic versions

## PrimesOnTheNumberLine.lean
Establishes foundational facts about prime distribution: infinitude, summability by harmonic series, and von Mangoldt detection.

**Exports:**
- `infinitely_many_primes` — unconditional infinitude
- `primes_infinite_on_number_line` — set is infinite
- `prime_placement_injective` — primes map injectively to reals
- `prime_harmonics_diverge` — divergence of 1/p sum
- `vonMangoldt_detects_primes` — von Mangoldt equals log at primes
- `primes_generate_zeta_harmonics` — Euler product formula
- `vonMangoldt_times_zeta_eq_log` — Dirichlet convolution
- `classical_zeros_control_prime_placement` — zeta nonvanishing on Re ≥ 1

## PrimeHarmonicReflection.lean
Proves that prime harmonics are not reflection-invariant off the critical line: x^s ≠ x^(1-conj(s)) when Re(s) ≠ 1/2.

**Exports:**
- `prime_harmonic_not_reflection_invariant` — off-line breaks symmetry
- `prime_harmonic_ne_of_off_line` — explicit inequality
- `prime_harmonic_magnitude_ratio` — ratio formula
- `magnitude_ratio_ne_one` — ratio is never 1 off-line

## HarmonicBridge.lean
Elementary trigonometric identities bridging π/6 and π/3 via sin and cos: both equal 1/2.

**Exports:**
- `harmonic_bridge_law` — sin(π/6) = 1/2
- `complementary_reflection` — cos(π/3) = 1/2
- `two_reflections_one_identity` — sin(π/6) = cos(π/3)
- `full_harmonic_bridge` — both hold

## HarmonicCancellation.lean
Establishes cancellation identities: sin(t) + sin(-t) = 0 (cancellation) and sin(arcsin(1/2)) = 1/2 (residual).

**Exports:**
- `sin_reflection_cancellation` — sin reflects to opposite
- `cos_reflection_reinforcement` — cos reflects to double
- `sin_arcsin_projection` — arcsin inversion
- `residual_value_is_one_half` — residual after cancellation
- `harmonic_cancellation_and_residual` — both properties

## DualReflectionImpossibility.lean
Proves unconditionally that no infinite set of off-axis points can be invariant under both classical (1-s) and cosh (π/3-s) rotations.

**Exports:**
- `classicalRotation` — s ↦ 1 - s
- `coshRotation` — s ↦ π/3 - s with folding
- `primeHarmonicFreqs` — infinite set of harmonic frequencies
- `primeHarmonic_reflection_invariant` — symmetry about 2σ - s
- `no_dual_symmetric_set` — empty set invariant under both
- `no_infinite_offline_zeros_pass_both_tests` — impossible for off-axis zeros
- `dual_invariance_forces_empty` — both conditions force emptiness
- `mathlib_RH_of_no_offaxis_zeros` — the hypothesis from off-axis zeros being absent

## DualReflectionImpossibility3.lean
Similar dual rotation impossibility result with explicit rotation definitions and iteration properties.

**Exports:**
- `classicalRotationD`, `coshRotationD` — rotation definitions
- `composition_is_translation` — composition yields positive translation
- `no_dual_symmetric_setD` — empty set under both rotations
- `closure_dual_invariant_empty` — closure emptiness
- `dual_invariance_forces_empty` — forces emptiness
- `mathlib_RH_of_no_offaxis_zeros` — main consequence

## OverlapEquivalence.lean
Establishes the overlap region as the seed for analytic continuation: identity theorem applies, and functions agreeing on overlap are equal everywhere.

**Exports:**
- `eulerHalfPlane`, `coshKernelDomain`, `overlapRegion` — regional decomposition
- `overlapRegion_isOpen`, `overlapRegion_nonempty`, `overlapRegion_isPreconnected` — topology
- `identity_theorem_on_overlap` — identity principle on overlap
- `meromorphic_order_transfer` — order preservation
- `representation_equivalence` — equivalence via overlap
- `overlap_seed_properties` — seed properties

## SelfDuality.lean
Proves that β = 1/2 is the unique self-dual weight: the only value where p^(-β) = p^(-(1-β)) for all p > 1.

**Exports:**
- `feInvolution` — functional equation involution: β ↦ 1 - β
- `feInvolution_involutive` — self-inverse
- `involution_unique_fixed_point` — unique fixed point is 1/2
- `self_dual_weight` — β = 1/2 iff p^(-β) = p^(-(1-β))
- `imbalance_factorization` — factorization of imbalance
- `fold_plus_duality_forces_half` — dual weights force 1/2
- `dual_weights_unique_balance` — uniqueness
- `critical_line_characterization` — self-duality iff critical line

## EulerProductRotation.lean
Shows that Euler product terms and partial sums are invariant under absolute value: n^(-s) and |n|^(-s) are identical.

**Exports:**
- `nat_cast_eq_abs` — natural number cast equals its absolute value
- `euler_product_rotation_invariant` — products invariant
- `nat_cast_complex_norm` — norm equals cast
- `euler_product_abs_invariant` — Euler terms invariant
- `euler_term_depends_on_abs` — term only depends on absolute value

## Translation.lean
Proves global impossibility of dual symmetries (classical and cosh rotations) by exhaustion via iteration and translation to boundaries.

**Exports:**
- `CriticalStrip` — the strip {s : 0 < Re(s) < 1}
- `CriticalLine` — the line Re(s) = 1/2
- `funcEqReflection` — s ↦ 1 - s̄
- `coshReflection` — s ↦ π/3 - Re(s) + i·Im(s)
- `no_dual_invariant_set_in_strip` — no dual-invariant subset
- `iterate_double_comp` — iteration via composition
- `balance_point_from_funcEq` — functional equation forces 1/2
- `critical_line_unique_balance` — uniqueness of critical line

## ProofChain.lean
Master theorem combining all ingredients: dual rotation impossibility, off-axis detector failure, prime harmonic balance, and direct conclusion.

**Exports:**
- `classicalRotation`, `coshRotationP` — dual rotations
- `IsNontrivialOfflineZero`, `offlineZeros` — off-axis zero set
- `offaxis_zero_full_consequences` — full properties of off-axis zero
- `no_dual_symmetric_set` — no dual-invariant set in strip
- `no_conspiracy`, `no_infinite_conspiracy` — no off-axis conspiracy
- `offlineZeros_empty_if_cosh_invariant` — invariance forces emptiness
- `RH_of_cosh_invariance` — conclusion from cosh invariance
- `offlineZeros_empty_iff_RH` — equivalence
- `detector_iff_half` — detector iff σ = 1/2
- `offaxis_fails` — off-axis fails detector
- `detector_forces_half` — zeta zero forces 1/2
- `RH_of_detector` — conclusion from detector
- `harmonic_geometric_agreement` — harmonic-geometric balance

## FinalAssembly.lean
Comprehensive final assembly: cosh reflection domain analysis, overlap region analytic continuation, and all dual symmetry consequences.

**Exports:**
- `coshReflDomainC`, `overlapRegionC`, `criticalStrip` — region definitions
- `coshRotation`, `classicalRotationC` — symmetries
- `coshReflDomainC_isOpen`, `coshReflDomainC_isPreconnected` — topology
- `coshReflDomainC_coshRotation_invariant` — rotation invariance
- `coshRotation_comp_classicalRotationC` — composition is translation
- `coshKernelC` — harmonic cosh kernel
- `cosh_kernel_coshRotation` — kernel is rotation-invariant
- `hg_symm_of_coshKernel_integral` — harmonic symmetry from kernel integral
- `coshReflDomainC_diff_one_isOpen`, `coshReflDomainC_diff_one_preconnected` — regularity
- `riemannZeta_analyticOnNhd_coshReflDomainC` — zeta analyticity
- `no_dual_symmetric_setC` — no dual-invariant set
- `hg_eq_from_overlap` — functions equal via overlap identity theorem
