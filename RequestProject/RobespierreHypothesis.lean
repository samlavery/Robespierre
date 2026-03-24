import Mathlib
import RequestProject.NoOffAxisZeros
import RequestProject.RobespierreNoOffAxisZeros
import RequestProject.StripTheorem

/-!
# The Robespierre Hypothesis from No Off-Axis Zeros

This file derives the Robespierre Hypothesis from the `NoOffAxisZeros` hypothesis.
The three supporting lemmas (value at 0, no zeros for Re(s) ≥ 1, trivial zeros)
follow from the StripTheorem infrastructure via the definitional equality
`RobespierreZeta = CircleNative.ΞInfinite`.
-/

noncomputable section

open Complex CircleNative

/-- The functional equation: RobespierreZeta reflects about θ = arcsin(1/2). -/
theorem RobespierreZeta_symm (s : ℂ) :
    RobespierreZeta s = RobespierreZeta (2 * ↑θ - s) := by
  simp only [RobespierreZeta, ΞInfinite]
  congr 1
  ext p
  split_ifs with hp <;> simp_all
  have hleft : (2 * ↑θ - s - ↑θ : ℂ) = -(s - ↑θ) := by ring
  left
  rw [hleft]
  rw [show (↑θ - (2 * ↑θ - s) : ℂ) = s - ↑θ by ring]
  ring_nf

/-- RobespierreZeta is nonzero on the right off-axis strip. -/
theorem RobespierreZeta_ne_zero_stripPlus {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (hδ : δ < 1)
    (h1 : HypHolomorphic (StripPlus ε δ))
    (h2 : HypLocallyUniform (StripPlus ε δ))
    (h3 : HypZeroFree (StripPlus ε δ))
    (h4 : HypNotIdenticallyZero (StripPlus ε δ)) :
    ∀ s ∈ StripPlus ε δ, RobespierreZeta s ≠ 0 := by
  let _ := hδ
  intro s hs
  simp only [RobespierreZeta]
  exact strip_theorem_plus hε hεδ h1 h2 h3 h4 s hs

/-- A bridge hypothesis asserting that a zero of `RobespierreZeta`
forces the Klein-four detector at its real part. -/
def ZeroDetectorBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → DetectorPasses s.re

/-- Observable dimension collapse:
    if a zero and its Robespierre symmetry partner both occur, then the planar
    observable geometry collapses onto the Klein-four plane at `1/2`, encoded
    by the detector at the original real part. This is the uniform-in-`t`
    theorem form of the user's geometric argument. -/
def ObservableDimensionCollapse : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    RobespierreZeta (2 * ↑θ - s) = 0 →
    DetectorPasses s.re

/-- Off-axis `0 ↔ 1` collapse compatibility:
    a Robespierre zero need not live at `1/2`, but if it is off the
    theta-centered axis then it must still satisfy the unscaled reflection
    collapse geometry. Since that unscaled geometry is anchored at `0` and `1`,
    its unique collapse locus is `1/2`. Formally, an off-axis zero forces the
    full reflected two-point collapse test. -/
def OffAxisZeroForcesHalfCollapse : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ → s.re ≠ θ →
    OffAxisTwoPlaneTest s.re

/-- Off-axis component A of the bridge: an off-axis zero of `RobespierreZeta`
    in the critical strip forces the collapse/radius-matching check
    at its real part. -/
def OffAxisZeroDetectorCheckABridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → 0 < s.re → s.re < 2 * θ → s.re ≠ θ → DetectorCheckA s.re

#check OffAxisZeroDetectorCheckABridge

/-- Symmetry-axis bridge: an off-axis zero of `RobespierreZeta` in the
    critical strip forces the `theta`-axis symmetry check at its real part. -/
def OffAxisZeroSymmetryBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → 0 < s.re → s.re < 2 * θ → s.re ≠ θ → DetectorCheckTheta s.re

/-- Preferred zeta-side bridge: zeros are only connected to the symmetry plane
    at `θ = arcsin(1/2)`, not to the collapse plane at `sin(θ) = 1/2`. -/
def ZeroAxisBridge : Prop :=
  OffAxisZeroSymmetryBridge

/-- Reflection fixed-point bridge on the kernel axis:
    if a Robespierre zero lies on `Re(s) = θ`, then it is fixed by the
    reflection `s ↦ 2θ - s`. Equivalently, its imaginary part vanishes. -/
def ZeroThetaReflectionFixedBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → s.re = theta → ThetaReflectionFixedCheck s

#check ZeroThetaReflectionFixedBridge

/-- Imaginary-collapse bridge on the kernel axis:
    if a Robespierre zero lies on `Re(s) = θ`, then its imaginary part is `0`. -/
def ZeroThetaImagBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → s.re = theta → DetectorCheckThetaImag s.im

#check ZeroThetaImagBridge

/-- Exact target form of the A-bridge. Any proof of
    `OffAxisZeroDetectorCheckABridge` can be used through this theorem. -/
theorem offAxis_zero_implies_detectorA
    (hA : OffAxisZeroDetectorCheckABridge)
    {s : ℂ} (hz : RobespierreZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 2 * θ) (hoff : s.re ≠ θ) :
    DetectorCheckA s.re :=
  hA s hz h0 h1 hoff

/-- Exact target form of the off-axis detector bridge in the user's preferred
    statement: an off-axis Robespierre zero in the critical strip forces the
    detector at its real part. This is proved from the full reflected
    half-collapse bridge by taking the first component of the two-plane test. -/
theorem offaxis_zero_forces_detector
    (hhalf : OffAxisZeroForcesHalfCollapse)
    {s : ℂ} (hz : RobespierreZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 2 * θ) (hoff : s.re ≠ θ) :
    DetectorPasses s.re :=
  (hhalf s hz h0 h1 hoff).1

/-- Exact target form of the symmetry bridge. -/
theorem offAxis_zero_implies_theta_check
    (hA : OffAxisZeroSymmetryBridge)
    {s : ℂ} (hz : RobespierreZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 2 * θ) (hoff : s.re ≠ θ) :
    DetectorCheckTheta s.re :=
  hA s hz h0 h1 hoff

/-- Exact target form of the preferred zeta-side axis bridge. -/
theorem offAxis_zero_implies_axis
    (hA : ZeroAxisBridge)
    {s : ℂ} (hz : RobespierreZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 2 * θ) (hoff : s.re ≠ θ) :
    SymmetryPlaneCheck s.re :=
  hA s hz h0 h1 hoff

/-- A reflection-fixed zero on the kernel axis has zero imaginary part. -/
theorem zeroThetaImagBridge_of_reflection_fixed
    (hT : ZeroThetaReflectionFixedBridge) :
    ZeroThetaImagBridge := by
  intro s hs hre
  exact (detector_theta_imag_iff_zero s.im).mpr
    ((theta_reflection_fixed_iff_im_zero hre).mp (hT s hs hre))

/-- User-facing form: a zero on the kernel axis has zero imaginary part. -/
theorem zero_on_theta_implies_imag_zero
    (hT : ZeroThetaImagBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0) (hre : s.re = theta) :
    s.im = 0 :=
  (detector_theta_imag_iff_zero s.im).mp (hT s hs hre)

/-- Component B of the bridge: a zero of `RobespierreZeta` forces the
    deprojection/faithfulness check at its real part. -/
def ZeroDetectorCheckBBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → DetectorCheckB s.re

#check ZeroDetectorCheckBBridge

/-- Full `A ∧ B ∧ C` bridge: a zero of `RobespierreZeta` forces the explicit
    three-check detector package at its real part. -/
def ZeroDetectorCheckABCBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → DetectorCheckABC s.re

#check ZeroDetectorCheckABCBridge

/-- Full `A ∧ B ∧ C` bridge with an end-of-pipeline quarter-turn audit:
    a zero of `RobespierreZeta` forces the explicit three-check detector
    package at its real part, and every quarter-turn comparison for `A`, `B`,
    and `C` passes on both the real slice and the full strip point for every
    sampled prime and
    observable rotation. -/
def ZeroDetectorQuarterTurnPassBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    ∀ p : ℕ, ∀ α : ℝ, detectorQuarterTurnPasses p α s = true

#check ZeroDetectorQuarterTurnPassBridge

/-- Full `A ∧ B ∧ C` bridge together with the strict quarter-turn pass gate. -/
def ZeroDetectorCheckABCAuditBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    DetectorCheckABC s.re ∧
      ∀ p : ℕ, ∀ α : ℝ, detectorQuarterTurnPasses p α s = true

#check ZeroDetectorCheckABCAuditBridge

/-- The reflected A-check pair for a prospective off-axis zero. -/
def OffAxisCheckATest (σ : ℝ) : Prop :=
  DetectorCheckA σ ∧ DetectorCheckA (2 * θ - σ)

/-- No real value can satisfy the reflected A-check pair. -/
theorem no_offaxis_checkA_test (σ : ℝ) : ¬ OffAxisCheckATest σ := by
  intro h
  rcases h with ⟨hσ, hσrfl⟩
  have hs : σ = Real.sin theta := (detector_A_iff_sin_theta σ).mp hσ
  have hsr : 2 * θ - σ = Real.sin theta := (detector_A_iff_sin_theta (2 * θ - σ)).mp hσrfl
  have hsep : θ ≠ Real.sin theta := by
    rw [CircleNative.θ_eq, sin_theta]
    linarith [Real.pi_gt_three]
  have hθ : θ = Real.sin theta := by
    linarith
  exact hsep hθ

/-- The full zero-to-detector bridge follows by proving the two detector
    components separately for zeros of `RobespierreZeta`. -/
theorem zeroDetectorBridge_of_components
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge) :
    ZeroDetectorBridge := by
  intro s hs
  by_cases haxis : s.re = θ
  · have hsep : θ ≠ Real.sin theta := by
      rw [CircleNative.θ_eq, sin_theta]
      linarith [Real.pi_gt_three]
    have hdetB : DetectorCheckB s.re := hB s hs
    have hsin : s.re = Real.sin theta := (detector_B_iff_sin_theta s.re).mp hdetB
    exfalso
    exact hsep (haxis.symm.trans hsin)
  · have hA' : DetectorCheckA s.re := by
      by_cases h0 : 0 < s.re
      · by_cases h1 : s.re < 2 * θ
        · exact hA s hs h0 h1 haxis
        · exfalso
          have hdetB : DetectorCheckB s.re := hB s hs
          have hsin : s.re = Real.sin theta := (detector_B_iff_sin_theta s.re).mp hdetB
          rw [sin_theta] at hsin
          linarith [CircleNative.one_lt_two_theta]
      · exfalso
        have hdetB : DetectorCheckB s.re := hB s hs
        have hsin : s.re = Real.sin theta := (detector_B_iff_sin_theta s.re).mp hdetB
        rw [sin_theta] at hsin
        linarith
    have hsin : s.re = Real.sin theta := (detector_A_iff_sin_theta s.re).mp hA'
    exact (detector_iff_sin_theta s.re).mpr hsin

/-- Observable dimension collapse immediately yields the zero-to-detector
    bridge, because the Robespierre symmetry partner exists automatically by
    the reflection symmetry of the kernel. -/
theorem zeroDetectorBridge_of_observableDimensionCollapse
    (hcollapse : ObservableDimensionCollapse) :
    ZeroDetectorBridge := by
  intro s hs
  have hsymm := RobespierreZeta_symm s
  have hsr_zero : RobespierreZeta (2 * ↑θ - s) = 0 := by
    simpa [hs] using hsymm.symm
  exact hcollapse s hs hsr_zero

/-- The explicit `A ∧ B ∧ C` bridge immediately yields the detector bridge. -/
theorem zeroDetectorBridge_of_checkABC
    (hABC : ZeroDetectorCheckABCBridge) :
    ZeroDetectorBridge := by
  intro s hs
  simpa [DetectorPasses] using hABC s hs

#check zeroDetectorBridge_of_checkABC
#print zeroDetectorBridge_of_checkABC

/-- The explicit `A ∧ B ∧ C` bridge together with the quarter-turn audit
    immediately yields the detector bridge. -/
theorem zeroDetectorBridge_of_checkABCAudit
    (hABC : ZeroDetectorCheckABCAuditBridge) :
    ZeroDetectorBridge := by
  intro s hs
  simpa [DetectorPasses] using (hABC s hs).1

#check zeroDetectorBridge_of_checkABCAudit
#print zeroDetectorBridge_of_checkABCAudit

/-- The kernel-side component bridges assemble into the explicit
    `A ∧ B ∧ C` detector bridge. -/
theorem zeroDetectorCheckABCBridge_of_components
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge) :
    ZeroDetectorCheckABCBridge := by
  intro s hs
  have hB' : DetectorCheckB s.re := hB s hs
  have hsin : s.re = Real.sin theta := (detector_B_iff_sin_theta s.re).mp hB'
  by_cases haxis : s.re = θ
  · have hsep : θ ≠ Real.sin theta := by
      rw [CircleNative.θ_eq, sin_theta]
      linarith [Real.pi_gt_three]
    exact False.elim (hsep (haxis.symm.trans hsin))
  · have h0 : 0 < s.re := by
      rw [hsin, sin_theta]
      norm_num
    have h1 : s.re < 2 * θ := by
      rw [hsin, sin_theta]
      linarith [CircleNative.one_lt_two_theta]
    have hA' : DetectorCheckA s.re := hA s hs h0 h1 haxis
    have hC' : DetectorCheckC s.re := (detector_C_iff_sin_theta s.re).mpr hsin
    exact ⟨hA', hB', hC'⟩

#check zeroDetectorCheckABCBridge_of_components
#print zeroDetectorCheckABCBridge_of_components

/-- The kernel-side component bridges assemble into the explicit
    `A ∧ B ∧ C` detector bridge together with the end-of-pipeline
    quarter-turn audit completion check. -/
theorem zeroDetectorCheckABCAuditBridge_of_components
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge)
    (hQ : ZeroDetectorQuarterTurnPassBridge) :
    ZeroDetectorCheckABCAuditBridge := by
  intro s hs
  refine ⟨zeroDetectorCheckABCBridge_of_components hA hB s hs, ?_⟩
  intro p α
  exact hQ s hs p α

#check zeroDetectorCheckABCAuditBridge_of_components
#print zeroDetectorCheckABCAuditBridge_of_components

/-- The off-axis half-collapse formulation is enough to recover the
    zero-to-detector bridge, since on-axis points are handled separately in the
    no-off-axis-zero argument. -/
theorem noOffAxisZeros_of_offAxis_halfCollapse
    (hhalf : OffAxisZeroForcesHalfCollapse) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  by_cases haxis : s.re = θ
  · simpa [θ] using haxis
  exact False.elim ((no_offaxis_two_plane_test s.re) (hhalf s hs hs_pos hs_lt haxis))

/-- An off-axis zero induces the reflected A-check pair once the A-component
    bridge is available and the reflected zero remains in the critical strip. -/
theorem zero_implies_offaxis_checkA_test
    (hA : OffAxisZeroDetectorCheckABridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) (hoff : s.re ≠ θ)
    (href_lt : 2 * θ - s.re < 2 * θ) :
    OffAxisCheckATest s.re := by
  constructor
  · exact hA s hs hs_pos hs_lt hoff
  · let sr : ℂ := 2 * ↑θ - s
    have hsymm := RobespierreZeta_symm s
    have hsr_zero : RobespierreZeta sr = 0 := by
      simpa [hs] using hsymm.symm
    have hsr_re : sr.re = 2 * θ - s.re := by
      simp [sr]
    have hsr_pos : 0 < sr.re := by
      rw [hsr_re]
      linarith [CircleNative.θ_eq, Real.pi_gt_three]
    have hsr_lt : sr.re < 2 * θ := by
      rw [hsr_re]
      exact href_lt
    have hsr_off : sr.re ≠ θ := by
      intro h_eq
      rw [hsr_re] at h_eq
      have hs_eq : s.re = θ := by linarith
      exact hoff hs_eq
    have hA_sr : DetectorCheckA sr.re := hA sr hsr_zero hsr_pos hsr_lt hsr_off
    rw [hsr_re] at hA_sr
    exact hA_sr

/-- Legacy A-only reduction: the no-off-axis-zero statement follows from the
    A-component bridge together with zero-freeness on the right tail
    `Re(s) ≥ 1`. New user-facing reductions should prefer the full detector
    bridge below. -/
theorem noOffAxisZeros_of_zero_detector_checkA_bridge
    (hA : OffAxisZeroDetectorCheckABridge)
    (hright : ∀ s : ℂ, 2 * θ ≤ s.re → RobespierreZeta s ≠ 0) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  by_cases haxis : s.re = θ
  · simpa [θ] using haxis
  have hsep : θ > 1 / 2 := by
    rw [CircleNative.θ_eq]
    linarith [Real.pi_gt_three]
  rcases lt_or_gt_of_ne haxis with hleft | hright'
  · let sr : ℂ := 2 * ↑θ - s
    have hsymm := RobespierreZeta_symm s
    have hsr_zero : RobespierreZeta sr = 0 := by
      simpa [sr, hs] using hsymm.symm
    have hsr_re : sr.re = 2 * θ - s.re := by
      simp [sr]
    by_cases hsr_lt : sr.re < 2 * θ
    · have hsr_pos : 0 < sr.re := by
        rw [hsr_re]
        linarith
      have hsr_off : sr.re ≠ θ := by
        intro h_eq
        rw [hsr_re] at h_eq
        linarith
      have hA_sr : DetectorCheckA sr.re := hA sr hsr_zero hsr_pos hsr_lt hsr_off
      have hsin : sr.re = Real.sin theta := (detector_A_iff_sin_theta sr.re).mp hA_sr
      rw [sin_theta] at hsin
      linarith
    · have hsr_ge : 2 * θ ≤ sr.re := by linarith
      exact False.elim ((hright sr hsr_ge) hsr_zero)
  · have hA_s : DetectorCheckA s.re := hA s hs hs_pos hs_lt haxis
    have hsin : s.re = Real.sin theta := (detector_A_iff_sin_theta s.re).mp hA_s
    rw [sin_theta] at hsin
    linarith

/-- The no-off-axis-zero statement follows immediately once an off-axis zero
    forces the symmetry-axis check at `theta`. -/
theorem noOffAxisZeros_of_zero_symmetry_bridge
    (hA : OffAxisZeroSymmetryBridge) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  by_cases haxis : s.re = θ
  · simpa [θ] using haxis
  have htheta : DetectorCheckTheta s.re := hA s hs hs_pos hs_lt haxis
  exact False.elim (haxis ((detector_theta_iff_theta s.re).mp htheta))

/-- The Robespierre zero statement follows from the preferred axis bridge. -/
theorem noOffAxisZeros_of_zero_axis_bridge
    (hA : ZeroAxisBridge) :
    NoOffAxisZeros :=
  noOffAxisZeros_of_zero_symmetry_bridge hA

/-- If off-axis zeros are already ruled out, then any purported off-axis zero
    in the critical strip automatically satisfies the symmetry-plane check. -/
theorem zeroAxisBridge_of_noOffAxisZeros
    (hno : NoOffAxisZeros) :
    ZeroAxisBridge := by
  intro s hs hs_pos hs_lt hoff
  have haxis : s.re = θ := hno s hs hs_pos hs_lt
  exact (symmetry_plane_iff_theta s.re).mpr haxis

/-- An off-axis zero induces the reflected two-plane test once the
zero-to-detector bridge is available. -/
theorem zero_implies_offaxis_two_plane_test
    (hbridge : ZeroDetectorBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0) (hoff : s.re ≠ θ) :
    OffAxisTwoPlaneTest s.re := by
  let _ := hoff
  constructor
  · exact hbridge s hs
  · let sr : ℂ := 2 * ↑θ - s
    have hsymm := RobespierreZeta_symm s
    have hsr_zero : RobespierreZeta sr = 0 := by
      simpa [hs] using hsymm.symm
    have hdet : DetectorPasses sr.re := hbridge sr hsr_zero
    have hsr_re : sr.re = 2 * θ - s.re := by
      simp [sr]
    rw [hsr_re] at hdet
    exact hdet

/-- Once every zero forces the detector at its real part, the two-plane
obstruction rules out all off-axis zeros in the critical strip. -/
theorem noOffAxisZeros_of_zero_detector_bridge
    (hbridge : ZeroDetectorBridge) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  by_contra hoff
  have htest : OffAxisTwoPlaneTest s.re :=
    zero_implies_offaxis_two_plane_test hbridge hs hoff
  exact (no_offaxis_two_plane_test s.re) htest

/-- The no-off-axis-zero statement follows once the two kernel-side bridge
    components are proved for zeros of `RobespierreZeta`. -/
theorem noOffAxisZeros_of_zero_detector_components
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge)
    (hQ : ZeroDetectorQuarterTurnPassBridge) :
    NoOffAxisZeros :=
  noOffAxisZeros_of_zero_detector_bridge
    (zeroDetectorBridge_of_checkABCAudit
      (zeroDetectorCheckABCAuditBridge_of_components hA hB hQ))

/-- If the right off-axis strips and the right tail are zero-free, then every
zero of RobespierreZeta in the critical strip lies on `Re(s) = arcsin(1/2)`. -/
theorem robespierreHypothesis_of_right_geometry
    (hstrip :
      ∀ {ε δ : ℝ}, 0 < ε → ε < δ → δ < 1 →
        ∀ s ∈ StripPlus ε δ, RobespierreZeta s ≠ 0)
    (hright :
      ∀ s : ℂ, θ + 1 ≤ s.re → RobespierreZeta s ≠ 0) :
    RobespierreHypothesis := by
  intro s hs hs_pos hs_lt
  by_cases haxis : s.re = θ
  · simpa [θ] using haxis
  have htrichotomy : s.re < θ ∨ θ < s.re := lt_or_gt_of_ne haxis
  rcases htrichotomy with hleft | hright'
  · let sr : ℂ := 2 * ↑θ - s
    have hsr_zero : RobespierreZeta sr = 0 := by
      have hsymm := RobespierreZeta_symm s
      simpa [sr, hs] using hsymm.symm
    have hsr_re : sr.re = 2 * θ - s.re := by
      simp [sr]
    have hsr_right : θ < sr.re := by
      linarith
    by_cases hsr_near : sr.re - θ < 1
    · let ε : ℝ := (sr.re - θ) / 2
      let δ : ℝ := (sr.re - θ + 1) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hεδ : ε < δ := by
        dsimp [ε, δ]
        linarith
      have hδ : δ < 1 := by
        dsimp [δ]
        linarith
      have hsr_mem : sr ∈ StripPlus ε δ := by
        dsimp [StripPlus, ε, δ]
        constructor <;> linarith
      exact False.elim ((hstrip hε hεδ hδ sr hsr_mem) hsr_zero)
    · have hsr_tail : θ + 1 ≤ sr.re := by
        linarith
      exact False.elim ((hright sr hsr_tail) hsr_zero)
  · by_cases hnear : s.re - θ < 1
    · let ε : ℝ := (s.re - θ) / 2
      let δ : ℝ := (s.re - θ + 1) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hεδ : ε < δ := by
        dsimp [ε, δ]
        linarith
      have hδ : δ < 1 := by
        dsimp [δ]
        linarith
      have hs_mem : s ∈ StripPlus ε δ := by
        dsimp [StripPlus, ε, δ]
        constructor <;> linarith
      exact False.elim ((hstrip hε hεδ hδ s hs_mem) hs)
    · have htail : θ + 1 ≤ s.re := by
        linarith
      exact False.elim ((hright s htail) hs)

/-- The Robespierre Hypothesis follows from the no-off-axis-zeros assumption. -/
theorem robespierreHypothesis (h : NoOffAxisZeros) : RobespierreHypothesis := by
  intro s hs hs_pos hs_lt
  exact h s hs hs_pos hs_lt

/-- If the Robespierre Hypothesis holds and zeros on the kernel axis satisfy
    the imaginary-collapse check, then every zero in the critical strip is the
    real point `θ` itself. -/
theorem robespierreZero_eq_theta_of_hypothesis_and_theta_imag
    (hRH : RobespierreHypothesis)
    (hT : ZeroThetaImagBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s = ↑theta := by
  have hre : s.re = theta := hRH s hs hs_pos hs_lt
  have him : s.im = 0 := zero_on_theta_implies_imag_zero hT hs hre
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- The Robespierre Hypothesis follows from the zero-to-detector bridge. -/
theorem robespierreHypothesis_of_zero_detector_bridge
    (hbridge : ZeroDetectorBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis (noOffAxisZeros_of_zero_detector_bridge hbridge)

/-- The Robespierre Hypothesis follows from the observable dimension collapse
    theorem at the Klein-four plane. -/
theorem robespierreHypothesis_of_observableDimensionCollapse
    (hcollapse : ObservableDimensionCollapse) :
    RobespierreHypothesis :=
  robespierreHypothesis_of_zero_detector_bridge
    (zeroDetectorBridge_of_observableDimensionCollapse hcollapse)

/-- Preferred wording of the thesis:
    an off-axis Robespierre zero is forced into the unscaled `0 ↔ 1` collapse
    geometry at `1/2`, but Robespierre zeros are theta-centered, so this is
    impossible. -/
theorem robespierreHypothesis_of_offAxis_halfCollapse
    (hhalf : OffAxisZeroForcesHalfCollapse) :
    RobespierreHypothesis :=
  robespierreHypothesis (noOffAxisZeros_of_offAxis_halfCollapse hhalf)

/-- The Robespierre Hypothesis follows from the full detector bridge:
    `A` is supplied directly, `B` is supplied directly, and `C` is recovered
    by the strengthened classifier. -/
theorem robespierreHypothesis_of_zero_detector_checkA_bridge
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge)
    (hQ : ZeroDetectorQuarterTurnPassBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis_of_zero_detector_bridge
    (zeroDetectorBridge_of_checkABCAudit
      (zeroDetectorCheckABCAuditBridge_of_components hA hB hQ))

/-- The Robespierre Hypothesis follows from the symmetry-axis bridge. -/
theorem robespierreHypothesis_of_zero_symmetry_bridge
    (hA : OffAxisZeroSymmetryBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis (noOffAxisZeros_of_zero_symmetry_bridge hA)

/-- Preferred final reduction: connect zeta zeros only to the symmetry plane
    at `θ = arcsin(1/2)`. -/
theorem robespierreHypothesis_of_zero_axis_bridge
    (hA : ZeroAxisBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis (noOffAxisZeros_of_zero_axis_bridge hA)

/-- The preferred axis bridge follows from the right-strip and right-tail
    geometric hypotheses, via the Robespierre Hypothesis itself. -/
theorem zeroAxisBridge_of_right_geometry
    (hstrip :
      ∀ {ε δ : ℝ}, 0 < ε → ε < δ → δ < 1 →
        ∀ s ∈ StripPlus ε δ, RobespierreZeta s ≠ 0)
    (hright :
      ∀ s : ℂ, θ + 1 ≤ s.re → RobespierreZeta s ≠ 0) :
    ZeroAxisBridge := by
  have hRH : RobespierreHypothesis :=
    robespierreHypothesis_of_right_geometry hstrip hright
  intro s hs hs_pos hs_lt hoff
  have haxis : s.re = θ := hRH s hs hs_pos hs_lt
  exact (symmetry_plane_iff_theta s.re).mpr haxis

/-- The Robespierre Hypothesis follows once the two detector components are
    each derived from zeros of `RobespierreZeta`. -/
theorem robespierreHypothesis_of_zero_detector_components
    (hA : OffAxisZeroDetectorCheckABridge)
    (hB : ZeroDetectorCheckBBridge)
    (hQ : ZeroDetectorQuarterTurnPassBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis_of_zero_detector_bridge
    (zeroDetectorBridge_of_checkABCAudit
      (zeroDetectorCheckABCAuditBridge_of_components hA hB hQ))

/-- `NoOffAxisZeros` from the A-bridge alone — no right-tail hypothesis needed.
    Structure: an off-axis zero is forced to `Re = sin θ = 1/2` (step 1, via `hA`).
    The reflected zero then has `Re = 2θ − 1/2`. Since `2θ − 1/2 ≠ θ`, `hA` applies
    again, forcing `2θ − 1/2 = 1/2`, i.e. `θ = 1/2`. But `θ = π/6 > 1/2`.
    Contradiction. -/
theorem noOffAxisZeros_of_checkA_alone
    (hA : OffAxisZeroDetectorCheckABridge) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  by_cases haxis : s.re = θ
  · simpa [θ] using haxis
  -- Step 1: forced to sin θ = 1/2
  have hre : s.re = Real.sin theta :=
    (detector_A_iff_sin_theta s.re).mp (hA s hs hs_pos hs_lt haxis)
  -- Step 2: reflected zero
  have hzero_r : RobespierreZeta (2 * ↑θ - s) = 0 := by
    simpa [hs] using (RobespierreZeta_symm s).symm
  -- Re(reflected) = 2θ − 1/2
  have hre_r : (2 * ↑θ - s).re = 2 * θ - 1 / 2 := by
    have h : (2 * ↑θ - s).re = 2 * θ - s.re := by simp
    rw [h, hre, sin_theta]
  -- Step 3: reflected zero is in the critical strip and off-axis
  have hpos_r : 0 < (2 * ↑θ - s).re := by
    rw [hre_r, CircleNative.θ_eq]; linarith [Real.pi_gt_three]
  have hlt_r : (2 * ↑θ - s).re < 2 * θ := by
    rw [hre_r]; linarith
  have hoff_r : (2 * ↑θ - s).re ≠ θ := by
    rw [hre_r, CircleNative.θ_eq]; intro h; linarith [Real.pi_gt_three]
  -- Step 4: hA on reflected → 2θ − 1/2 = 1/2 → θ = 1/2 → contradiction
  have hre_r2 : (2 * ↑θ - s).re = Real.sin theta :=
    (detector_A_iff_sin_theta _).mp (hA _ hzero_r hpos_r hlt_r hoff_r)
  rw [hre_r, CircleNative.θ_eq, sin_theta] at hre_r2
  linarith [Real.pi_gt_three]

/-- The Robespierre Hypothesis follows from the full detector bridge:
    `A` is supplied directly, `B` is supplied directly, and `C` is recovered
    from the strengthened `A ∧ B ∧ C` classifier, while the strict
    quarter-turn diagnostic is supplied separately. -/
theorem robespierreHypothesis_of_checkA_alone
    (hA : OffAxisZeroDetectorCheckABridge) :
    (hB : ZeroDetectorCheckBBridge) →
    (hQ : ZeroDetectorQuarterTurnPassBridge) →
    RobespierreHypothesis :=
  fun hB hQ => robespierreHypothesis_of_zero_detector_bridge
    (zeroDetectorBridge_of_checkABCAudit
      (zeroDetectorCheckABCAuditBridge_of_components hA hB hQ))

#check robespierreHypothesis_of_checkA_alone
#print robespierreHypothesis_of_checkA_alone

end
