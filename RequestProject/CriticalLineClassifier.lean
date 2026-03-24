import Mathlib
import RequestProject.Defs

/-!
# Critical Line Classifier via Robespierre Coordinate System

We build a geometric classifier using the **Robespierre coordinate system**, an
alternative framework based on non-integer values. The primitive angle
θ = arcsin(1/2) = π/6 replaces the integer-basis value 1/2 throughout.
The critical line condition σ = 1/2 becomes σ = sin(θ).

## Robespierre Coordinate Primitives

- **θ (theta)**: The primitive angle θ = arcsin(1/2) = π/6
- **φ(p) (phiPrime)**: Circle-native prime geometry φ(p) = 2θ·p
- **u_p (primeLogFreq)**: Prime-log frequency u_p = log(φ(p))
- **a_p (thetaCoeff)**: Coefficient a_p = π/6 · ((2π - 3)/π)^p
- **Ξ_{θ,P}(s) (XiThetaFinite)**: Finite θ-native kernel
- **C_P(t) (criticalLineSum)**: Critical-line sum
- **C_P'(t) (criticalLineSumDeriv)**: Derivative of C_P

## Overview

The construction proceeds in seven stages:
0. **Robespierre primitives**: θ, φ(p), u_p, a_p, Ξ, C_P, C_P'
1. **Klein four orbit**: Orbit collapse at Re(s) = sin(θ)
2. **Helix construction**: Radii p^(-σ) with critical value at σ = sin(θ)
3. **Deprojection**: Decoded primes match canonical primes iff σ = sin(θ)
4. **Three-check detector**: Checks A, B, C characterize σ = sin(θ)
5. **Three number lines**: Faithful (σ = sin(θ)) vs unfaithful (σ ≠ sin(θ))
6. **Classification**: No off-line parameter passes the detector

## Anti-circularity

All reconstruction objects are defined purely from prime/helix data and the
Robespierre angle θ. The zeta function does not appear in any definition or
intermediate lemma.
-/

noncomputable section

open Real Complex Finset BigOperators

/-! ## Section 0: Robespierre Coordinate System Primitives -/

/-- The primitive angle θ = arcsin(1/2). This is the fundamental constant of the
    Robespierre coordinate system, replacing the integer-basis value 1/2. -/
def theta : ℝ := Real.arcsin (1 / 2)

/-- The primitive angle equals π/6. -/
theorem theta_eq_pi_div_six : theta = π / 6 := by
  unfold theta
  rw [show (1 : ℝ) / 2 = Real.sin (π / 6) from (Real.sin_pi_div_six).symm]
  exact Real.arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])

/-- sin(θ) = 1/2: the Robespierre angle recovers the critical-line value. -/
theorem sin_theta : Real.sin theta = 1 / 2 := by
  unfold theta
  exact Real.sin_arcsin (by norm_num) (by norm_num)

/-- Circle-native prime geometry: φ(p) = 2θ·p.
    Maps each prime p into the circle-native coordinate frame. -/
def phiPrime (p : ℕ) : ℝ := CircleNative.φ p

/-- Prime-log frequency: u_p = log(φ(p)) = log(2θp).
    The logarithmic frequency associated to prime p in the Robespierre system. -/
def primeLogFreq (p : ℕ) : ℝ := CircleNative.u p

/-- θ-native coefficient: a_p = π/6 · ((2π - 3)/π)^p.
    The weight assigned to each prime in the θ-native kernel. -/
def thetaCoeff (p : ℕ) : ℝ := CircleNative.a p

/-- The classifier angle agrees with the circle-native kernel angle. -/
theorem theta_eq_circle_theta : theta = CircleNative.θ := by
  rfl

/-- The classifier prime geometry agrees with the circle-native kernel base. -/
theorem phiPrime_eq_circle_phi (p : ℕ) : phiPrime p = CircleNative.φ p := by
  rfl

/-- The classifier frequency agrees with the circle-native kernel frequency. -/
theorem primeLogFreq_eq_circle_u (p : ℕ) : primeLogFreq p = CircleNative.u p := by
  rfl

/-- The classifier coefficient agrees with the circle-native kernel coefficient. -/
theorem thetaCoeff_eq_circle_a (p : ℕ) : thetaCoeff p = CircleNative.a p := by
  rfl

/-- The coefficient simplifies to the geometric decay law
    a_p = π/6 · ((2π - 3)/π)^p. -/
theorem thetaCoeff_simplified (p : ℕ) :
    thetaCoeff p =
      Real.pi / 6 * (((2 * Real.pi - 3) / Real.pi) ^ p) := by
  simp [thetaCoeff_eq_circle_a, CircleNative.a]

/-- Finite θ-native kernel over a finite prime set, aligned with the
    circle-native summands used in `RobespierreZeta`. -/
def XiThetaFinite (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ P.filter Nat.Prime,
    (thetaCoeff p : ℂ) *
      (CircleNative.cpowBase p (s - ↑CircleNative.θ) +
       CircleNative.cpowBase p (-(s - ↑CircleNative.θ)))

/-- The classifier finite kernel agrees with `CircleNative.ΞFinite` on
    the canonical prime prefix `primesBelow n`. -/
theorem XiThetaFinite_primesBelow_eq (n : ℕ) (s : ℂ) :
    XiThetaFinite (CircleNative.primesBelow n) s = CircleNative.ΞFinite n s := by
  unfold XiThetaFinite CircleNative.ΞFinite thetaCoeff
  rw [CircleNative.primesBelow, Finset.filter_filter]
  simp

/-- Critical-line sum aligned with the circle-native kernel. -/
def criticalLineSum (P : ℕ) (t : ℝ) : ℝ :=
  CircleNative.CriticalLineSum P t

/-- Derivative of the critical-line sum:
    aligned with the circle-native kernel derivative. -/
def criticalLineSumDeriv (P : ℕ) (t : ℝ) : ℝ :=
  CircleNative.CriticalLineSumDeriv P t

/-- At `t = 0`, the critical-line sum reduces to the coefficient sum. -/
theorem criticalLineSum_at_zero (P : ℕ) :
    criticalLineSum P 0 = ∑ p ∈ CircleNative.primesBelow P, thetaCoeff p := by
  unfold criticalLineSum CircleNative.CriticalLineSum thetaCoeff
  simp

/-- The derivative vanishes at t = 0 (all sines equal 0). -/
theorem criticalLineSumDeriv_at_zero (P : ℕ) :
    criticalLineSumDeriv P 0 = 0 := by
  unfold criticalLineSumDeriv CircleNative.CriticalLineSumDeriv
  simp

/-! ## Section 1: Klein Four Orbit (in θ-coordinates) -/

/-- The Klein four orbit of a complex number s under the ζ-symmetries:
    {s, 1-s, conj(s), 1-conj(s)}. -/
def KleinFourOrbit (s : ℂ) : Finset ℂ :=
  {s, 1 - s, starRingEnd ℂ s, 1 - starRingEnd ℂ s}

/-- The four named projections in the Klein-four orbit. -/
inductive KleinProjection where
  | self
  | reflect
  | conj
  | reflectConj
deriving DecidableEq, Repr

/-- The three-way comparison result used to detect symmetry, antisymmetry,
    and rogue asymmetric behaviour under quarter-turns. -/
inductive SymmetryClass where
  | symmetric
  | antisymmetric
  | asymmetric
deriving DecidableEq, Repr

/-- The explicit complex point seen by each Klein projection. -/
def kleinProjectedPoint (s : ℂ) : KleinProjection → ℂ
  | .self => s
  | .reflect => 1 - s
  | .conj => starRingEnd ℂ s
  | .reflectConj => 1 - starRingEnd ℂ s

/-- Quarter-turn the critical strip around the origin by 90 degrees. -/
def quarterTurn (s : ℂ) : ℂ :=
  Complex.I * s

/-- The real part seen by each Klein projection. Conjugation fixes the real
    part, while reflection sends `σ` to `1 - σ`. -/
def kleinProjectedSigma (σ : ℝ) : KleinProjection → ℝ
  | .self => σ
  | .reflect => 1 - σ
  | .conj => σ
  | .reflectConj => 1 - σ

/-- On the collapse line `σ = sin(θ) = 1/2`, all Klein projections have the
    same real part. -/
theorem kleinProjectedSigma_sin_theta (κ : KleinProjection) :
    kleinProjectedSigma (Real.sin theta) κ = Real.sin theta := by
  cases κ <;> unfold kleinProjectedSigma <;> rw [sin_theta] <;> norm_num

/-- The Klein four orbit is symmetric (collapses from 4 to ≤2 elements) iff
    s = 1 - conj(s), which forces Re(s) = sin(θ) = 1/2. -/
def KleinFourSymmetric (s : ℂ) : Prop :=
  s = 1 - starRingEnd ℂ s

/-- Klein four symmetry is equivalent to Re(s) = sin(θ).
    In the Robespierre system, orbit collapse occurs at the primitive angle's sine. -/
theorem klein_symmetric_iff_sin_theta (s : ℂ) :
    KleinFourSymmetric s ↔ s.re = Real.sin theta := by
  rw [sin_theta]
  unfold KleinFourSymmetric
  constructor
  · intro h
    have := congr_arg Complex.re h
    simp [Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  · intro h
    apply Complex.ext
    · simp [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp [Complex.sub_im, Complex.one_im, Complex.conj_im]

/-- On the critical line (Re(s) = sin(θ)), 1 - s = conj(s),
    so the orbit has at most 2 distinct elements. -/
theorem klein_orbit_collapse (s : ℂ) (h : s.re = Real.sin theta) :
    1 - s = starRingEnd ℂ s := by
  rw [sin_theta] at h
  apply Complex.ext
  · simp [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
  · simp [Complex.sub_im, Complex.one_im, Complex.conj_im]

/-! ## Section 2: Helix Construction (in θ-coordinates) -/

/-- Helix radius for prime p at real part σ: (p : ℝ)^(-σ).
    This is the modulus of p^{-s} = p^{-σ} · e^{-it log p}. -/
def helixRadius (p : ℕ) (σ : ℝ) : ℝ := (p : ℝ) ^ (-σ)

/-- Helix phase for prime p at imaginary part t: -t · log(p).
    This is the argument of p^{-s}. -/
def helixPhase (p : ℕ) (t : ℝ) : ℝ := -t * Real.log p

/-- Reflection helix radius (from 1-s): (p : ℝ)^(-(1-σ)).
    This is the modulus of p^{-(1-s)}. -/
def reflectionRadius (p : ℕ) (σ : ℝ) : ℝ := (p : ℝ) ^ (-(1 - σ))

/-- **Core algebraic fact**: The rpow function with base p > 1 is injective
    in the exponent. -/
theorem rpow_exponent_injective {p : ℕ} (hp : 1 < p) {a b : ℝ}
    (h : (p : ℝ) ^ a = (p : ℝ) ^ b) : a = b := by
  have hp' : (1 : ℝ) < (p : ℝ) := Nat.one_lt_cast.mpr hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp0 (ne_of_gt hp')
  have hh := congr_arg Real.log h
  rw [Real.log_rpow hp0, Real.log_rpow hp0] at hh
  exact mul_right_cancel₀ hlog hh

/-- **Fundamental**: Helix radii from s and 1-s match iff σ = sin(θ) = 1/2.
    This is the radius-level manifestation of Klein four symmetry in
    the Robespierre coordinate system. -/
theorem reflection_radius_match_iff_sin_theta {p : ℕ} (hp : 1 < p) (σ : ℝ) :
    helixRadius p σ = reflectionRadius p σ ↔ σ = Real.sin theta := by
  rw [sin_theta]
  unfold helixRadius reflectionRadius
  constructor
  · intro h
    have := rpow_exponent_injective hp h
    linarith
  · intro h; subst h; ring_nf

/-- Critical line planarity: on the critical line (σ = sin(θ)),
    both helices share radii. -/
theorem critical_line_planarity (p : ℕ) :
    helixRadius p (Real.sin theta) = reflectionRadius p (Real.sin theta) := by
  rw [sin_theta]; unfold helixRadius reflectionRadius; ring_nf

/-- Off-line bend: off the critical line, helices have different radii
    for any prime p > 1. -/
theorem offline_bend_nonzero {p : ℕ} (hp : 1 < p) {σ : ℝ}
    (hσ : σ ≠ Real.sin theta) :
    helixRadius p σ ≠ reflectionRadius p σ :=
  fun h => hσ ((reflection_radius_match_iff_sin_theta hp σ).mp h)

/-! ## Section 3: Deprojection and Number Lines (in θ-coordinates) -/

/-- The canonical number line: maps each natural number n to (n : ℝ).
    For primes, this gives the true prime value. -/
def CanonicalNumberLine (n : ℕ) : ℝ := (n : ℝ)

/-- Deprojected (decoded) prime value: given helix radius p^{-σ}, decode through
    the canonical (σ = sin(θ)) inverse formula r ↦ r^{-2}, yielding p^{2σ}.

    Derivation: if σ were sin(θ) = 1/2, then radius = p^{-1/2} and the inverse
    is r^{-2} = p. Applying this formula to radius p^{-σ} gives p^{2σ}. -/
def decodedPrime (p : ℕ) (σ : ℝ) : ℝ := (p : ℝ) ^ (2 * σ)

/-- The decoded value equals the canonical value iff σ = sin(θ) = 1/2.
    Because p^{2σ} = p iff 2σ = 1, i.e. σ = sin(θ). -/
theorem decoded_eq_canonical_iff_sin_theta {p : ℕ} (hp : 1 < p) (σ : ℝ) :
    decodedPrime p σ = CanonicalNumberLine p ↔ σ = Real.sin theta := by
  rw [sin_theta]
  unfold decodedPrime CanonicalNumberLine
  constructor
  · intro h
    have h1 : (p : ℝ) ^ (2 * σ) = (p : ℝ) ^ (1 : ℝ) := by rwa [Real.rpow_one]
    have := rpow_exponent_injective hp h1
    linarith
  · intro h; subst h; simp [Real.rpow_one]

/-- Faithful reconstruction: at σ, every decoded prime matches the canonical prime. -/
def FaithfulReconstruction (σ : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → decodedPrime p σ = CanonicalNumberLine p

/-- Faithful reconstruction holds iff σ = sin(θ). -/
theorem faithful_iff_sin_theta (σ : ℝ) :
    FaithfulReconstruction σ ↔ σ = Real.sin theta := by
  unfold FaithfulReconstruction
  constructor
  · intro h
    exact (decoded_eq_canonical_iff_sin_theta (by norm_num : 1 < 2) σ).mp
      (h 2 (by decide))
  · intro h p hp
    exact (decoded_eq_canonical_iff_sin_theta hp.one_lt σ).mpr h

/-- Finite prefix agreement: for any finite set containing a prime p > 1,
    decoded values match canonical values on the set iff σ = sin(θ). -/
theorem finite_prefix_agreement (S : Finset ℕ) (hS : ∃ p ∈ S, Nat.Prime p) (σ : ℝ) :
    (∀ p ∈ S, Nat.Prime p → decodedPrime p σ = CanonicalNumberLine p) ↔
      σ = Real.sin theta := by
  constructor
  · intro h
    exact (decoded_eq_canonical_iff_sin_theta
      (Nat.Prime.one_lt hS.choose_spec.2) σ).mp
      (h _ hS.choose_spec.1 hS.choose_spec.2)
  · intro h p _ hp
    exact (decoded_eq_canonical_iff_sin_theta hp.one_lt σ).mpr h

/-- Agreement on all primes implies σ = sin(θ). -/
theorem all_primes_determine_sin_theta (σ : ℝ)
    (h : ∀ p : ℕ, Nat.Prime p → decodedPrime p σ = CanonicalNumberLine p) :
    σ = Real.sin theta :=
  (faithful_iff_sin_theta σ).mp h

/-! ## Section 4: Three-Check Detector Across the Klein Four Projections -/

/-- Compare two real outputs by symmetry type. -/
def classifyRealSymmetry (x y : ℝ) : SymmetryClass :=
  if y = x then .symmetric else if y = -x then .antisymmetric else .asymmetric

/-- Compare two paired outputs by symmetry type. -/
def classifyPairSymmetry (x y : ℝ × ℝ) : SymmetryClass :=
  if y = x then .symmetric
  else if y = (-x.1, -x.2) then .antisymmetric
  else .asymmetric

/-- The radius-comparison output recorded at a given Klein projection. -/
def detectorAOutput (p : ℕ) (σ : ℝ) (κ : KleinProjection) : ℝ × ℝ :=
  let σκ := kleinProjectedSigma σ κ
  (helixRadius p σκ, reflectionRadius p σκ)

/-- Radius-comparison output on the full strip point seen through a
    Klein projection. -/
def detectorAComplexOutput (p : ℕ) (s : ℂ) (κ : KleinProjection) : ℝ × ℝ :=
  let sκ := kleinProjectedPoint s κ
  (helixRadius p sκ.re, reflectionRadius p sκ.re)

/-- The decoded-prime output recorded at a given Klein projection. -/
def detectorBOutput (p : ℕ) (σ : ℝ) (κ : KleinProjection) : ℝ :=
  decodedPrime p (kleinProjectedSigma σ κ)

/-- Decoding output on the full strip point seen through a Klein projection. -/
def detectorBComplexOutput (p : ℕ) (s : ℂ) (κ : KleinProjection) : ℝ :=
  decodedPrime p (kleinProjectedPoint s κ).re

/-- The classifier measures prime-density distortion relative to the
    critical-line baseline using the real displacement from `sin(θ)`. -/
def detectorPrimeDensityShift (σ : ℝ) : ℝ :=
  σ - Real.sin theta

/-- The rotation-aware density output recorded at a given Klein projection. -/
def detectorCOutput (σ α : ℝ) (κ : KleinProjection) : ℝ × ℝ :=
  let σκ := kleinProjectedSigma σ κ
  ( CircleNative.RotatedOffAxisRealObservable 2 (detectorPrimeDensityShift σκ) 0 α,
    CircleNative.RotatedOffAxisImagObservable 2 (detectorPrimeDensityShift σκ) 0 α )

/-- Rotation-aware density output on the full strip point seen through a
    Klein projection. -/
def detectorCComplexOutput (α : ℝ) (s : ℂ) (κ : KleinProjection) : ℝ × ℝ :=
  let sκ := kleinProjectedPoint s κ
  ( CircleNative.RotatedOffAxisRealObservable 2 (detectorPrimeDensityShift sκ.re) sκ.im α,
    CircleNative.RotatedOffAxisImagObservable 2 (detectorPrimeDensityShift sκ.re) sκ.im α )

/-- Quarter-turn classification for Check A on the real slice. -/
def detectorAQuarterTurnClassRealSlice (p : ℕ) (σ : ℝ) (κ : KleinProjection) : SymmetryClass :=
  classifyPairSymmetry
    (detectorAComplexOutput p ⟨σ, 0⟩ κ)
    (detectorAComplexOutput p (quarterTurn ⟨σ, 0⟩) κ)

/-- Quarter-turn classification for Check A on the full strip. -/
def detectorAQuarterTurnClassStrip (p : ℕ) (s : ℂ) (κ : KleinProjection) : SymmetryClass :=
  classifyPairSymmetry
    (detectorAComplexOutput p s κ)
    (detectorAComplexOutput p (quarterTurn s) κ)

/-- Quarter-turn classification for Check B on the real slice. -/
def detectorBQuarterTurnClassRealSlice (p : ℕ) (σ : ℝ) (κ : KleinProjection) : SymmetryClass :=
  classifyRealSymmetry
    (detectorBComplexOutput p ⟨σ, 0⟩ κ)
    (detectorBComplexOutput p (quarterTurn ⟨σ, 0⟩) κ)

/-- Quarter-turn classification for Check B on the full strip. -/
def detectorBQuarterTurnClassStrip (p : ℕ) (s : ℂ) (κ : KleinProjection) : SymmetryClass :=
  classifyRealSymmetry
    (detectorBComplexOutput p s κ)
    (detectorBComplexOutput p (quarterTurn s) κ)

/-- Quarter-turn classification for Check C on the real slice. -/
def detectorCQuarterTurnClassRealSlice (α : ℝ) (σ : ℝ) (κ : KleinProjection) : SymmetryClass :=
  classifyPairSymmetry
    (detectorCComplexOutput α ⟨σ, 0⟩ κ)
    (detectorCComplexOutput α (quarterTurn ⟨σ, 0⟩) κ)

/-- Quarter-turn classification for Check C on the full strip. -/
def detectorCQuarterTurnClassStrip (α : ℝ) (s : ℂ) (κ : KleinProjection) : SymmetryClass :=
  classifyPairSymmetry
    (detectorCComplexOutput α s κ)
    (detectorCComplexOutput α (quarterTurn s) κ)

/-- Record the quarter-turn behaviour of all three checks on the real slice. -/
def detectorQuarterTurnRecordRealSlice (p : ℕ) (α σ : ℝ) :
    KleinProjection → SymmetryClass × SymmetryClass × SymmetryClass :=
  fun κ =>
    ( detectorAQuarterTurnClassRealSlice p σ κ,
      detectorBQuarterTurnClassRealSlice p σ κ,
      detectorCQuarterTurnClassRealSlice α σ κ )

/-- Record the quarter-turn behaviour of all three checks on the full strip. -/
def detectorQuarterTurnRecordStrip (p : ℕ) (α : ℝ) (s : ℂ) :
    KleinProjection → SymmetryClass × SymmetryClass × SymmetryClass :=
  fun κ =>
    ( detectorAQuarterTurnClassStrip p s κ,
      detectorBQuarterTurnClassStrip p s κ,
      detectorCQuarterTurnClassStrip α s κ )

/-- Any quarter-turn classification counts as a recorded audit result. -/
def symmetryClassRecorded (_ : SymmetryClass) : Bool := true

/-- All three audit channels were recorded for a given Klein projection. -/
def symmetryTripleRecorded : SymmetryClass × SymmetryClass × SymmetryClass → Bool
  | (a, b, c) =>
      symmetryClassRecorded a &&
      symmetryClassRecorded b &&
      symmetryClassRecorded c

/-- End-of-audit completion check on the real slice:
    all three quarter-turn comparisons were recorded on all four Klein
    projections. -/
def detectorQuarterTurnAuditPassedRealSlice (p : ℕ) (α σ : ℝ) : Bool :=
  let record := detectorQuarterTurnRecordRealSlice p α σ
  symmetryTripleRecorded (record .self) &&
    symmetryTripleRecorded (record .reflect) &&
    symmetryTripleRecorded (record .conj) &&
    symmetryTripleRecorded (record .reflectConj)

/-- End-of-audit completion check on the full strip point:
    all three quarter-turn comparisons were recorded on all four Klein
    projections. -/
def detectorQuarterTurnAuditPassedStrip (p : ℕ) (α : ℝ) (s : ℂ) : Bool :=
  let record := detectorQuarterTurnRecordStrip p α s
  symmetryTripleRecorded (record .self) &&
    symmetryTripleRecorded (record .reflect) &&
    symmetryTripleRecorded (record .conj) &&
    symmetryTripleRecorded (record .reflectConj)

/-- Combined end-of-pipeline audit check:
    both the real-slice and full-strip quarter-turn comparisons completed. -/
def detectorQuarterTurnAuditPassed (p : ℕ) (α : ℝ) (s : ℂ) : Bool :=
  detectorQuarterTurnAuditPassedRealSlice p α s.re &&
    detectorQuarterTurnAuditPassedStrip p α s

/-- The real-slice quarter-turn audit always completes. -/
theorem detectorQuarterTurnAuditPassedRealSlice_eq_true (p : ℕ) (α σ : ℝ) :
    detectorQuarterTurnAuditPassedRealSlice p α σ = true := by
  simp [detectorQuarterTurnAuditPassedRealSlice, symmetryTripleRecorded,
    symmetryClassRecorded]

/-- The full-strip quarter-turn audit always completes. -/
theorem detectorQuarterTurnAuditPassedStrip_eq_true (p : ℕ) (α : ℝ) (s : ℂ) :
    detectorQuarterTurnAuditPassedStrip p α s = true := by
  simp [detectorQuarterTurnAuditPassedStrip, symmetryTripleRecorded,
    symmetryClassRecorded]

/-- The combined quarter-turn audit always completes. -/
theorem detectorQuarterTurnAuditPassed_eq_true (p : ℕ) (α : ℝ) (s : ℂ) :
    detectorQuarterTurnAuditPassed p α s = true := by
  simp [detectorQuarterTurnAuditPassed, detectorQuarterTurnAuditPassedRealSlice_eq_true,
    detectorQuarterTurnAuditPassedStrip_eq_true]

/-- A quarter-turn classification passes exactly when it is not asymmetric. -/
def symmetryClassPasses : SymmetryClass → Bool
  | .symmetric => true
  | .antisymmetric => true
  | .asymmetric => false

/-- All three quarter-turn classifications pass for a given Klein projection. -/
def symmetryTriplePasses : SymmetryClass × SymmetryClass × SymmetryClass → Bool
  | (a, b, c) =>
      symmetryClassPasses a &&
      symmetryClassPasses b &&
      symmetryClassPasses c

/-- Strict quarter-turn pass check on the real slice:
    every `A`, `B`, and `C` comparison passes on all four Klein projections. -/
def detectorQuarterTurnPassesRealSlice (p : ℕ) (α σ : ℝ) : Bool :=
  let record := detectorQuarterTurnRecordRealSlice p α σ
  symmetryTriplePasses (record .self) &&
    symmetryTriplePasses (record .reflect) &&
    symmetryTriplePasses (record .conj) &&
    symmetryTriplePasses (record .reflectConj)

/-- Strict quarter-turn pass check on the full strip point:
    every `A`, `B`, and `C` comparison passes on all four Klein projections. -/
def detectorQuarterTurnPassesStrip (p : ℕ) (α : ℝ) (s : ℂ) : Bool :=
  let record := detectorQuarterTurnRecordStrip p α s
  symmetryTriplePasses (record .self) &&
    symmetryTriplePasses (record .reflect) &&
    symmetryTriplePasses (record .conj) &&
    symmetryTriplePasses (record .reflectConj)

/-- The strict complete quarter-turn diagnostic:
    all quarter-turn checks pass on both the real slice and the full strip. -/
def detectorQuarterTurnPasses (p : ℕ) (α : ℝ) (s : ℂ) : Bool :=
  detectorQuarterTurnPassesRealSlice p α s.re &&
    detectorQuarterTurnPassesStrip p α s

/-- **Check A** (Internal self-consistency):
    every Klein projection gives the same radius-comparison output as the
    original projection, prime by prime. -/
def DetectorCheckA (σ : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∀ κ : KleinProjection,
    detectorAOutput p σ κ = detectorAOutput p σ KleinProjection.self

/-- **Check B** (External faithfulness):
    every Klein projection decodes back to the canonical number line. -/
def DetectorCheckB (σ : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∀ κ : KleinProjection,
    detectorBOutput p σ κ = CanonicalNumberLine p

/-- The reference rotated prime-density output on the critical line. -/
def detectorCBaseline (α : ℝ) : ℝ × ℝ :=
  (Real.cos α * criticalLineSum 2 0, Real.sin α * criticalLineSum 2 0)

/-- Base form of Check C for a single real part. -/
def DetectorCheckCBase (σ : ℝ) : Prop :=
  ∀ α : ℝ,
    detectorCOutput σ α KleinProjection.self = detectorCBaseline α

/-- **Check C** (Rotation-aware prime-density consistency):
    after shifting by `σ - sin(θ)`, each Klein projection produces the same
    rotated prime-density result as the critical-line baseline. -/
def DetectorCheckC (σ : ℝ) : Prop :=
  ∀ α : ℝ, ∀ κ : KleinProjection,
    detectorCOutput σ α κ = detectorCBaseline α

/-- The explicit `A ∧ B ∧ C` detector check. -/
def DetectorCheckABC (σ : ℝ) : Prop :=
  DetectorCheckA σ ∧ DetectorCheckB σ ∧ DetectorCheckC σ

/-- The full detector passes iff the explicit `A ∧ B ∧ C` check passes. -/
def DetectorPasses (σ : ℝ) : Prop :=
  DetectorCheckABC σ

/-- Plane A: the Klein-four collapse plane at `sin(θ) = 1/2`. -/
def CollapsePlaneCheck (σ : ℝ) : Prop :=
  DetectorPasses σ

/-- Check A passes iff σ = sin(θ). -/
theorem detector_A_iff_sin_theta (σ : ℝ) :
    DetectorCheckA σ ↔ σ = Real.sin theta := by
  constructor
  · intro h
    have hpair := h 2 (by decide) KleinProjection.reflect
    have hmatch : helixRadius 2 σ = reflectionRadius 2 σ := by
      have hfst := congrArg Prod.fst hpair
      simpa [detectorAOutput, kleinProjectedSigma] using hfst.symm
    exact (reflection_radius_match_iff_sin_theta (by norm_num : 1 < 2) σ).mp hmatch
  · intro h p hp κ
    cases κ with
    | self =>
        rfl
    | conj =>
        rfl
    | reflect =>
        have hmatch : helixRadius p σ = reflectionRadius p σ :=
          (reflection_radius_match_iff_sin_theta hp.one_lt σ).mpr h
        calc
          detectorAOutput p σ KleinProjection.reflect
              = (reflectionRadius p σ, helixRadius p σ) := by
                  simp [detectorAOutput, kleinProjectedSigma, helixRadius, reflectionRadius]
          _ = (helixRadius p σ, reflectionRadius p σ) := by
                exact Prod.ext hmatch.symm hmatch
          _ = detectorAOutput p σ KleinProjection.self := by
                simp [detectorAOutput, kleinProjectedSigma]
    | reflectConj =>
        have hmatch : helixRadius p σ = reflectionRadius p σ :=
          (reflection_radius_match_iff_sin_theta hp.one_lt σ).mpr h
        calc
          detectorAOutput p σ KleinProjection.reflectConj
              = (reflectionRadius p σ, helixRadius p σ) := by
                  simp [detectorAOutput, kleinProjectedSigma, helixRadius, reflectionRadius]
          _ = (helixRadius p σ, reflectionRadius p σ) := by
                exact Prod.ext hmatch.symm hmatch
          _ = detectorAOutput p σ KleinProjection.self := by
                simp [detectorAOutput, kleinProjectedSigma]

/-- Check B passes iff σ = sin(θ). -/
theorem detector_B_iff_sin_theta (σ : ℝ) :
    DetectorCheckB σ ↔ σ = Real.sin theta := by
  constructor
  · intro h
    exact (decoded_eq_canonical_iff_sin_theta (by norm_num : 1 < 2) σ).mp
      (h 2 (by decide) KleinProjection.self)
  · intro h p hp κ
    have hκ : kleinProjectedSigma σ κ = Real.sin theta := by
      subst h
      exact kleinProjectedSigma_sin_theta κ
    rw [detectorBOutput, hκ]
    exact (decoded_eq_canonical_iff_sin_theta hp.one_lt (Real.sin theta)).mpr rfl

/-- Base form of Check C passes iff σ = sin(θ). -/
theorem detector_CBase_iff_sin_theta (σ : ℝ) :
    DetectorCheckCBase σ ↔ σ = Real.sin theta := by
  constructor
  · intro hC
    have hα0 := hC 0
    have hre0 :
        CircleNative.RotatedOffAxisRealObservable 2 (detectorPrimeDensityShift σ) 0 0 =
          criticalLineSum 2 0 := by
      have hfst := congrArg Prod.fst hα0
      simpa [DetectorCheckCBase, detectorCOutput, detectorCBaseline, criticalLineSum,
        kleinProjectedSigma] using hfst
    have hre :
        CircleNative.OffAxisRealObservable 2 (detectorPrimeDensityShift σ) 0 =
          criticalLineSum 2 0 := by
      exact (CircleNative.rotatedOffAxisRealObservable_zero_angle
        2 (detectorPrimeDensityShift σ) 0).symm.trans hre0
    have hdist :
        CircleNative.RealAxisDistortion 2 (detectorPrimeDensityShift σ) = 0 := by
      unfold CircleNative.RealAxisDistortion
      exact sub_eq_zero.mpr hre
    have hshift : detectorPrimeDensityShift σ = 0 := by
      by_contra hx
      have hpos :=
        CircleNative.realAxisDistortion_pos_of_two_le (P := 2) (by norm_num) hx
      linarith
    unfold detectorPrimeDensityShift at hshift
    linarith
  · intro hσ
    subst hσ
    intro α
    have hreal :
        CircleNative.OffAxisRealObservable 2 0 0 = criticalLineSum 2 0 := by
      simpa [criticalLineSum] using CircleNative.offAxisRealObservable_axis 2 0
    have himag : CircleNative.OffAxisImagObservable 2 0 0 = 0 := by
      simpa using CircleNative.offAxisImagObservable_axis 2 0
    apply Prod.ext
    · simp [DetectorCheckCBase, detectorCOutput, detectorCBaseline, detectorPrimeDensityShift,
        kleinProjectedSigma, CircleNative.RotatedOffAxisRealObservable, hreal, himag, sin_theta]
    · simp [DetectorCheckCBase, detectorCOutput, detectorCBaseline, detectorPrimeDensityShift,
        kleinProjectedSigma, CircleNative.RotatedOffAxisImagObservable, hreal, himag, sin_theta]

/-- Check C passes iff σ = sin(θ). -/
theorem detector_C_iff_sin_theta (σ : ℝ) :
    DetectorCheckC σ ↔ σ = Real.sin theta := by
  constructor
  · intro hC
    have hbase : DetectorCheckCBase σ := by
      intro α
      exact hC α KleinProjection.self
    exact (detector_CBase_iff_sin_theta σ).mp hbase
  · intro hσ
    intro α κ
    subst hσ
    have hα : detectorCOutput (Real.sin theta) α KleinProjection.self = detectorCBaseline α :=
      (detector_CBase_iff_sin_theta (Real.sin theta)).mpr rfl α
    cases κ with
    | self =>
        simpa [detectorCOutput, detectorCBaseline, detectorPrimeDensityShift,
          kleinProjectedSigma, sin_theta] using hα
    | conj =>
        simpa [detectorCOutput, detectorCBaseline, detectorPrimeDensityShift,
          kleinProjectedSigma, sin_theta] using hα
    | reflect =>
        apply Prod.ext
        · change CircleNative.RotatedOffAxisRealObservable 2
            (detectorPrimeDensityShift (1 - Real.sin theta)) 0 α =
              Real.cos α * criticalLineSum 2 0
          rw [show detectorPrimeDensityShift (1 - Real.sin theta) =
              detectorPrimeDensityShift (Real.sin theta) by
                rw [sin_theta]
                norm_num [detectorPrimeDensityShift]]
          simpa [detectorCOutput, detectorCBaseline, kleinProjectedSigma] using
            congrArg Prod.fst hα
        · change CircleNative.RotatedOffAxisImagObservable 2
            (detectorPrimeDensityShift (1 - Real.sin theta)) 0 α =
              Real.sin α * criticalLineSum 2 0
          rw [show detectorPrimeDensityShift (1 - Real.sin theta) =
              detectorPrimeDensityShift (Real.sin theta) by
                rw [sin_theta]
                norm_num [detectorPrimeDensityShift]]
          simpa [detectorCOutput, detectorCBaseline, kleinProjectedSigma] using
            congrArg Prod.snd hα
    | reflectConj =>
        apply Prod.ext
        · change CircleNative.RotatedOffAxisRealObservable 2
            (detectorPrimeDensityShift (1 - Real.sin theta)) 0 α =
              Real.cos α * criticalLineSum 2 0
          rw [show detectorPrimeDensityShift (1 - Real.sin theta) =
              detectorPrimeDensityShift (Real.sin theta) by
                rw [sin_theta]
                norm_num [detectorPrimeDensityShift]]
          simpa [detectorCOutput, detectorCBaseline, kleinProjectedSigma] using
            congrArg Prod.fst hα
        · change CircleNative.RotatedOffAxisImagObservable 2
            (detectorPrimeDensityShift (1 - Real.sin theta)) 0 α =
              Real.sin α * criticalLineSum 2 0
          rw [show detectorPrimeDensityShift (1 - Real.sin theta) =
              detectorPrimeDensityShift (Real.sin theta) by
                rw [sin_theta]
                norm_num [detectorPrimeDensityShift]]
          simpa [detectorCOutput, detectorCBaseline, kleinProjectedSigma] using
            congrArg Prod.snd hα

/-- The detector passes iff σ = sin(θ). -/
theorem detector_iff_sin_theta (σ : ℝ) :
    DetectorPasses σ ↔ σ = Real.sin theta := by
  unfold DetectorPasses DetectorCheckABC
  constructor
  · rintro ⟨hA, _, _⟩
    exact (detector_A_iff_sin_theta σ).mp hA
  · intro h
    exact ⟨(detector_A_iff_sin_theta σ).mpr h,
      (detector_B_iff_sin_theta σ).mpr h,
      (detector_C_iff_sin_theta σ).mpr h⟩

/-! ## Section 4B: Symmetry-Axis Check at θ -/

/-- The kernel center θ is distinct from sin(θ) = 1/2. -/
theorem theta_ne_sin_theta : theta ≠ Real.sin theta := by
  rw [sin_theta, theta_eq_pi_div_six]
  linarith [Real.pi_gt_three]

/-- **Check Theta** (kernel symmetry axis):
    the real part is fixed by the reflection σ ↦ 2θ - σ. -/
def DetectorCheckTheta (σ : ℝ) : Prop :=
  σ = 2 * theta - σ

/-- The symmetry-axis check passes iff σ = θ. -/
theorem detector_theta_iff_theta (σ : ℝ) :
    DetectorCheckTheta σ ↔ σ = theta := by
  unfold DetectorCheckTheta
  constructor <;> intro h <;> linarith

/-- Plane B: the kernel symmetry plane at `θ = arcsin(1/2)`. -/
def SymmetryPlaneCheck (σ : ℝ) : Prop :=
  DetectorCheckTheta σ

/-- Plane A picks out the collapse locus `sin(θ)`. -/
theorem collapse_plane_iff_sin_theta (σ : ℝ) :
    CollapsePlaneCheck σ ↔ σ = Real.sin theta :=
  detector_iff_sin_theta σ

/-- Plane B picks out the symmetry axis `θ`. -/
theorem symmetry_plane_iff_theta (σ : ℝ) :
    SymmetryPlaneCheck σ ↔ σ = theta :=
  detector_theta_iff_theta σ

/-- Imaginary-axis reflection check at `θ`:
    the imaginary coordinate is fixed by the kernel reflection `t ↦ -t`. -/
def DetectorCheckThetaImag (t : ℝ) : Prop :=
  t = -t

/-- The imaginary reflection check passes exactly at height `0`. -/
theorem detector_theta_imag_iff_zero (t : ℝ) :
    DetectorCheckThetaImag t ↔ t = 0 := by
  unfold DetectorCheckThetaImag
  constructor <;> intro h <;> linarith

/-- Full reflection fixed-point check at the kernel axis:
    the complex point is fixed by `s ↦ 2θ - s`. -/
def ThetaReflectionFixedCheck (s : ℂ) : Prop :=
  s = 2 * ↑theta - s

/-- A point is reflection-fixed at the kernel axis exactly when it lies on
    `Re(s) = θ` and has zero imaginary part. -/
theorem theta_reflection_fixed_iff (s : ℂ) :
    ThetaReflectionFixedCheck s ↔ s.re = theta ∧ s.im = 0 := by
  unfold ThetaReflectionFixedCheck
  constructor
  · intro h
    constructor
    · have hre := congrArg Complex.re h
      simp [Complex.sub_re] at hre
      linarith
    · have him := congrArg Complex.im h
      simp [Complex.sub_im] at him
      linarith
  · rintro ⟨hre, him⟩
    apply Complex.ext
    · have htheta : theta = 2 * theta - theta := by ring
      simpa [Complex.sub_re, hre] using htheta
    · simp [Complex.sub_im, him]

/-- On the kernel axis `Re(s) = θ`, the reflection fixed-point check is
    equivalent to zero imaginary part. -/
theorem theta_reflection_fixed_iff_im_zero {s : ℂ} (hre : s.re = theta) :
    ThetaReflectionFixedCheck s ↔ s.im = 0 := by
  rw [theta_reflection_fixed_iff]
  simp [hre]

/-- The reflected Klein-four pair test:
    the collapse detector passes at `σ` and also at its kernel-reflected
    partner `2θ - σ`. This is the correct two-point test for a zero pair
    related by the symmetry `s ↦ 2θ - s`. -/
def KleinFourPairTest (σ : ℝ) : Prop :=
  DetectorPasses σ ∧ DetectorPasses (2 * theta - σ)

/-- Legacy name retained for the reflected two-point test. -/
def TwoPlaneDetectorPasses (σ : ℝ) : Prop :=
  KleinFourPairTest σ

/-- User-facing name: the two-plane test is the reflected Klein-four pair test. -/
def TwoPlaneTest (σ : ℝ) : Prop :=
  KleinFourPairTest σ

/-- θ passes the symmetry-axis check. -/
theorem theta_passes_theta_check : DetectorCheckTheta theta :=
  (detector_theta_iff_theta theta).mpr rfl

/-- sin(θ) fails the symmetry-axis check because sin(θ) ≠ θ. -/
theorem sinTheta_fails_theta_check : ¬ DetectorCheckTheta (Real.sin theta) := by
  intro h
  have htheta : Real.sin theta = theta := (detector_theta_iff_theta _).mp h
  exact theta_ne_sin_theta htheta.symm

/-- The kernel center `θ` does not pass the Klein-four collapse detector. -/
theorem theta_fails_detector : ¬ DetectorPasses theta := by
  intro h
  have htheta : theta = Real.sin theta := (detector_iff_sin_theta theta).mp h
  exact theta_ne_sin_theta htheta

/-- The reflected Klein-four pair test forces the symmetry axis `σ = θ`. -/
theorem klein_four_pair_forces_theta (σ : ℝ) :
    KleinFourPairTest σ → σ = theta := by
  intro h
  rcases h with ⟨hσ, hσrfl⟩
  have hs : σ = Real.sin theta := (detector_iff_sin_theta σ).mp hσ
  have hsr : 2 * theta - σ = Real.sin theta := (detector_iff_sin_theta (2 * theta - σ)).mp hσrfl
  linarith

/-- No off-axis real value can satisfy the reflected Klein-four pair test. -/
theorem two_plane_detector_fails (σ : ℝ) :
    σ ≠ theta → ¬ TwoPlaneDetectorPasses σ := by
  intro hne h
  exact hne (klein_four_pair_forces_theta σ h)

/-- Equivalent formulation: the two-plane detector never passes. -/
theorem two_plane_detector_complete (σ : ℝ) :
    TwoPlaneDetectorPasses σ ↔ False := by
  constructor
  · intro h
    have haxis : σ = theta := klein_four_pair_forces_theta σ h
    subst haxis
    exact theta_fails_detector h.1
  · intro h
    exact False.elim h

/-- The two-plane test never passes. -/
theorem two_plane_test_fails (σ : ℝ) :
    ¬ TwoPlaneTest σ := by
  intro h
  have h' : TwoPlaneDetectorPasses σ := by
    simpa [TwoPlaneTest, TwoPlaneDetectorPasses] using h
  exact (two_plane_detector_complete σ).mp h'

/-- Equivalent formulation for the two-plane test. -/
theorem two_plane_test_complete (σ : ℝ) :
    TwoPlaneTest σ ↔ False :=
  two_plane_detector_complete σ

/-! ## Section 5: Three Number Lines (in θ-coordinates) -/

/-- **Faithful line 1** (σ = sin(θ), from the s-helix): the detector passes. -/
theorem faithful_line_1_passes : DetectorPasses (Real.sin theta) :=
  (detector_iff_sin_theta _).mpr rfl

/-- **Faithful line 2** (σ = sin(θ), from the (1-s)-helix): the detector passes.
    Since σ = sin(θ) = 1/2, the s-helix and (1-s)-helix have identical radii. -/
theorem faithful_line_2_passes : DetectorPasses (Real.sin theta) :=
  faithful_line_1_passes

/-- **Unfaithful line** (σ ≠ sin(θ)): the detector fails. -/
theorem unfaithful_line_fails {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    ¬ DetectorPasses σ :=
  fun h => hσ ((detector_iff_sin_theta σ).mp h)

/-- The unfaithful line specifically fails Check A. -/
theorem unfaithful_fails_checkA {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    ¬ DetectorCheckA σ :=
  fun h => hσ ((detector_A_iff_sin_theta σ).mp h)

/-- The unfaithful line specifically fails Check B. -/
theorem unfaithful_fails_checkB {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    ¬ DetectorCheckB σ :=
  fun h => hσ ((detector_B_iff_sin_theta σ).mp h)

/-- The unfaithful line specifically fails the rotation-aware density check. -/
theorem unfaithful_fails_checkC {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    ¬ DetectorCheckC σ :=
  fun h => hσ ((detector_C_iff_sin_theta σ).mp h)

/-- Detector separation: the detector distinguishes faithful from unfaithful lines. -/
theorem detector_separation {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    DetectorPasses (Real.sin theta) ∧ ¬ DetectorPasses σ :=
  ⟨faithful_line_1_passes, unfaithful_line_fails hσ⟩

/-! ## Section 6: Final Classification Theorem (in θ-coordinates) -/

/-- **MAIN THEOREM**: No off-line parameter passes the detector.
    In the Robespierre coordinate system, any σ ≠ sin(θ) is detected as off-line. -/
theorem no_offline_passes_detector {σ : ℝ} (hσ : σ ≠ Real.sin theta) :
    ¬ DetectorPasses σ :=
  unfaithful_line_fails hσ

/-- The detector is a complete and sound classifier for the critical line.
    It accepts σ if and only if σ = sin(θ), where θ = arcsin(1/2) = π/6. -/
theorem classifier_complete (σ : ℝ) :
    DetectorPasses σ ↔ σ = Real.sin theta :=
  detector_iff_sin_theta σ

/-- Injecting an offline zero into the critical strip:
    even with the additional constraint 0 < σ < 1, the detector rejects σ ≠ sin(θ). -/
theorem strip_offline_rejected {σ : ℝ} (hσ : σ ≠ Real.sin theta)
    (_h0 : 0 < σ) (_h1 : σ < 1) : ¬ DetectorPasses σ :=
  no_offline_passes_detector hσ

/-- **Bridge theorem**: The Robespierre critical value sin(θ) equals
    the classical value 1/2. This confirms the coordinate systems agree
    on which line is critical. -/
theorem robespierre_classical_bridge :
    Real.sin theta = 1 / 2 := sin_theta

end
