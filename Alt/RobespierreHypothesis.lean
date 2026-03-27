import Mathlib
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RequestProject.NoOffAxisZeros
import RequestProject.RobespierreNoOffAxisZeros
import RequestProject.StripTheorem

/-!
# The Robespierre Hypothesis from No Off-Axis Zeros

This file derives the Robespierre Hypothesis from the `NoOffAxisZeros` hypothesis.
The strip/symmetry arguments still use the symmetric-sum model
`RobespierreZeta = CircleNative.ΞInfinite`.

The classical-RH correspondence layer is separate: there the preferred
Robespierre object is the transported classical model `RobespierreZetaO`.
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

/-- Direct observed-collapse bridge:
    every native zero in the θ-strip is observed on the classical
    one-dimensional collapse coordinate `1/2`. -/
def ZeroObservedDimensionalCollapseBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ →
    Real.sin s.re = 1 / 2

/-- Primary bridge name: every native zero in the θ-strip satisfies the
    planar dimensional-collapse condition. -/
abbrev ZeroPlanarDimensionalCollapseBridge : Prop :=
  ZeroObservedDimensionalCollapseBridge

/-- First-prime anchor bridge:
    every native zero in the θ-strip projects to the classical collapse
    coordinate `1/2`. This packages the proof in the arithmetic form
    “the first-prime anchor fixes the classical zero address”. -/
def FirstPrimeAnchorBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ →
    Real.sin s.re = 1 / 2

/-- Projected-detector bridge:
    every native zero in the θ-strip lands on the classical detector after
    projecting its real part by `sin`. This is the proof-facing version of
    “a native zero reads as an on-line classical zero”. -/
def ZeroProjectedDetectorBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ →
    DetectorPasses (Real.sin s.re)

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

/-- Abstract classical RH interface for a chosen complex function `ζ`:
    every nontrivial critical-strip zero lies on the classical line
    `Re(s) = 1 / 2`. -/
def ClassicalRH (ζ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ζ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- The classical Riemann Hypothesis phrased using mathlib's `riemannZeta`. -/
def ClassicalRiemannHypothesis : Prop :=
  ClassicalRH riemannZeta

/-- Mathlib's built-in formal statement of the Riemann Hypothesis. -/
abbrev MathlibRiemannHypothesis : Prop :=
  RiemannHypothesis

/-- Robespierre-zero statement for the transported classical model
    `RobespierreZetaO`. -/
def RobespierreOHypothesis : Prop :=
  ∀ s : ℂ, RobespierreZetaO s = 0 → 0 < s.re → s.re < 2 * θ → s.re = Real.arcsin (1 / 2)

/-- The Robespierre-to-classical lift keeps the height and sends the
    Robespierre real part `σ` to the classical detector value `sin σ`. -/
def robespierreToClassical (s : ℂ) : ℂ :=
  ⟨Real.sin s.re, s.im⟩

/-- The classical-to-Robespierre lift keeps the height and sends the classical
    real part `σ` to the Robespierre coordinate `arcsin σ`. -/
def classicalToRobespierre (s : ℂ) : ℂ :=
  ⟨Real.arcsin s.re, s.im⟩

/-- Primary user-facing name for the native-to-classical zero-address map:
    project the real part by `sin` and keep the height fixed. -/
abbrev ZeroAddressProjection : ℂ → ℂ :=
  robespierreToClassical

/-- Primary user-facing name for the classical-to-native zero-address map:
    lift the real part by `arcsin` and keep the height fixed. -/
abbrev ZeroAddressLift : ℂ → ℂ :=
  classicalToRobespierre

/-- Harmonic-prime rigidity bridge:
    the prime-controlled harmonic collapse and the projected classical
    collapse are locked together. Every native zero in the θ-strip therefore
    projects to a classical point whose Klein-four orbit collapses. -/
def HarmonicPrimeRigidityBridge : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ →
    KleinFourSymmetric (ZeroAddressProjection s)

/-- Backward-compatible name for the harmonic-prime rigidity bridge. -/
abbrev DoubleZeroProjectedKleinFourBridge : Prop :=
  HarmonicPrimeRigidityBridge

/-- The `RobespierreZetaO` bridge uses the linear strip-to-strip transport:
    it rescales the θ-native strip `(0, 2θ)` to the classical strip `(0, 1)`
    while keeping the height fixed. -/
def robespierreOToClassical (s : ℂ) : ℂ :=
  ⟨s.re / (2 * θ), s.im⟩

/-- The inverse linear transport for `RobespierreZetaO`: it rescales the
    classical strip `(0, 1)` to the θ-native strip `(0, 2θ)`. -/
def classicalToRobespierreO (s : ℂ) : ℂ :=
  ⟨(2 * θ) * s.re, s.im⟩

@[simp] theorem robespierreToClassical_re (s : ℂ) :
    (robespierreToClassical s).re = Real.sin s.re := by
  rfl

@[simp] theorem robespierreToClassical_im (s : ℂ) :
    (robespierreToClassical s).im = s.im := by
  rfl

@[simp] theorem classicalToRobespierre_re (s : ℂ) :
    (classicalToRobespierre s).re = Real.arcsin s.re := by
  rfl

@[simp] theorem classicalToRobespierre_im (s : ℂ) :
    (classicalToRobespierre s).im = s.im := by
  rfl

@[simp] theorem zeroAddressProjection_re (s : ℂ) :
    (ZeroAddressProjection s).re = Real.sin s.re := by
  rfl

@[simp] theorem zeroAddressProjection_im (s : ℂ) :
    (ZeroAddressProjection s).im = s.im := by
  rfl

@[simp] theorem zeroAddressLift_re (s : ℂ) :
    (ZeroAddressLift s).re = Real.arcsin s.re := by
  rfl

@[simp] theorem zeroAddressLift_im (s : ℂ) :
    (ZeroAddressLift s).im = s.im := by
  rfl

/-- On the classical strip, lifting and then projecting preserves the zero
    address exactly. -/
theorem zeroAddressProjection_zeroAddressLift {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ZeroAddressProjection (ZeroAddressLift s) = s := by
  have hs_neg : -1 ≤ s.re := by linarith
  apply Complex.ext
  · simp [ZeroAddressProjection, ZeroAddressLift, Real.sin_arcsin hs_neg hs1]
  · simp [ZeroAddressProjection, ZeroAddressLift]

/-- On the θ-native strip, projecting and then lifting preserves the zero
    address exactly. -/
theorem zeroAddressLift_zeroAddressProjection {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 2 * θ) :
    ZeroAddressLift (ZeroAddressProjection s) = s := by
  have hs_lt_pi_div_two : s.re < Real.pi / 2 := by
    have hs_lt_pi_div_three : s.re < Real.pi / 3 := by
      rw [show (2 * θ : ℝ) = Real.pi / 3 by rw [θ_eq]; ring] at hs1
      exact hs1
    linarith [hs_lt_pi_div_three, Real.pi_pos]
  apply Complex.ext
  · simp [ZeroAddressProjection, ZeroAddressLift,
      Real.arcsin_sin (by linarith [hs0]) hs_lt_pi_div_two.le]
  · simp [ZeroAddressProjection, ZeroAddressLift]

/-- Projecting the native axis address `θ + it` reads the same zero at the
    classical line address `1/2 + it`. -/
theorem zeroAddressProjection_theta_line (t : ℝ) :
    ZeroAddressProjection (↑θ + ↑t * Complex.I) = (1 / 2 : ℂ) + ↑t * Complex.I := by
  have hθ_half : Real.sin θ = 1 / 2 := by
    simpa [theta_eq_circle_theta] using sin_theta
  apply Complex.ext
  · simp [ZeroAddressProjection, hθ_half]
  · simp [ZeroAddressProjection]

/-- Lifting the classical line address `1/2 + it` reads the same zero at the
    native axis address `θ + it`. -/
theorem zeroAddressLift_half_line (t : ℝ) :
    ZeroAddressLift ((1 / 2 : ℂ) + ↑t * Complex.I) = ↑θ + ↑t * Complex.I := by
  apply Complex.ext
  · simp [ZeroAddressLift, CircleNative.θ]
  · simp [ZeroAddressLift]

/-- The native reflection center `θ = arcsin(1/2)` projects to a classical
    point with collapsed Klein-four orbit. This is the precise algebraic form
    of “`1/2` is the common rotation point, while `θ` is the native
    reflection point.” -/
theorem theta_axis_projection_kleinFourSymmetric {s : ℂ}
    (hre : s.re = θ) :
    KleinFourSymmetric (ZeroAddressProjection s) := by
  apply (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mpr
  simp [ZeroAddressProjection, hre, theta_eq_circle_theta]

@[simp] theorem robespierreOToClassical_re (s : ℂ) :
    (robespierreOToClassical s).re = s.re / (2 * θ) := by
  rfl

@[simp] theorem robespierreOToClassical_im (s : ℂ) :
    (robespierreOToClassical s).im = s.im := by
  rfl

@[simp] theorem classicalToRobespierreO_re (s : ℂ) :
    (classicalToRobespierreO s).re = (2 * θ) * s.re := by
  rfl

@[simp] theorem classicalToRobespierreO_im (s : ℂ) :
    (classicalToRobespierreO s).im = s.im := by
  rfl

@[simp] theorem robespierreOToClassical_classicalToRobespierreO (s : ℂ) :
    robespierreOToClassical (classicalToRobespierreO s) = s := by
  apply Complex.ext <;> simp [robespierreOToClassical, classicalToRobespierreO, two_theta_pos.ne']

/-- Mathlib's RH implies the local strip-level classical RH interface used by
    the Robespierre bridge theorems. -/
theorem classicalRiemannHypothesis_of_mathlibRiemannHypothesis
    (hRH : MathlibRiemannHypothesis) :
    ClassicalRiemannHypothesis := by
  intro s hs hs_pos hs_lt
  have hnontrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have hnonpos : ((-2 * (n + 1) : ℂ).re : ℝ) ≤ 0 := by
      simp
      positivity
    exact not_lt_of_ge hnonpos hs_pos
  have hs_ne_one : s ≠ 1 := by
    intro hs_one
    have : ¬ ((1 : ℂ).re < 1) := by norm_num
    exact this (by simpa [hs_one] using hs_lt)
  exact hRH s hs hnontrivial hs_ne_one

/-- The local strip-level classical RH interface is equivalent to mathlib's
    global `RiemannHypothesis`: nontrivial zeros cannot occur in `Re(s) ≥ 1`
    by nonvanishing, and they cannot occur in `Re(s) ≤ 0` because the
    completed functional equation reflects them into the nonvanishing region
    unless they are one of the trivial negative-even zeros. -/
theorem mathlibRiemannHypothesis_of_classicalRiemannHypothesis
    (hRH : ClassicalRiemannHypothesis) :
    MathlibRiemannHypothesis := by
  intro s hs htriv hs_ne_one
  have hs_lt_one : s.re < 1 := by
    by_contra hs_ge
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hs_ge)) hs
  have hs_pos : 0 < s.re := by
    by_contra hs_nonpos
    have hs_ne_zero : s ≠ 0 := by
      intro hs_zero
      subst hs_zero
      norm_num [riemannZeta_zero] at hs
    have hGamma_s_ne : Gammaℝ s ≠ 0 := by
      intro hGamma_s
      rcases Gammaℝ_eq_zero_iff.mp hGamma_s with ⟨n, hn⟩
      by_cases hn0 : n = 0
      · subst hn0
        exact hs_ne_zero (by simpa using hn)
      · rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨m, hm⟩
        apply htriv
        refine ⟨m, ?_⟩
        rw [hm] at hn
        simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    have hCompleted_s_zero : completedRiemannZeta s = 0 := by
      have hs_div : completedRiemannZeta s / Gammaℝ s = 0 := by
        simpa [riemannZeta_def_of_ne_zero hs_ne_zero] using hs
      rcases (div_eq_zero_iff).mp hs_div with hzero | hzero
      · exact hzero
      · exact False.elim (hGamma_s_ne hzero)
    have hCompleted_one_sub_zero : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]
      exact hCompleted_s_zero
    have h_one_sub_re_ge : 1 ≤ (1 - s).re := by
      simp
      linarith
    have hGamma_one_sub_ne : Gammaℝ (1 - s) ≠ 0 := by
      intro hGamma_one_sub
      rcases Gammaℝ_eq_zero_iff.mp hGamma_one_sub with ⟨n, hn⟩
      have h_nonpos : ((1 - s : ℂ).re) ≤ 0 := by
        rw [hn]
        simp
      linarith
    have h_one_sub_ne_zero : 1 - s ≠ 0 := sub_ne_zero.mpr hs_ne_one.symm
    have hZeta_one_sub_zero : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h_one_sub_ne_zero]
      exact (div_eq_zero_iff).mpr (Or.inl hCompleted_one_sub_zero)
    exact (riemannZeta_ne_zero_of_one_le_re h_one_sub_re_ge) hZeta_one_sub_zero
  exact hRH s hs hs_pos hs_lt_one

/-- The local strip-level RH interface and mathlib's built-in global
    `RiemannHypothesis` are equivalent. -/
theorem classicalRiemannHypothesis_iff_mathlibRiemannHypothesis :
    ClassicalRiemannHypothesis ↔ MathlibRiemannHypothesis := by
  constructor
  · exact mathlibRiemannHypothesis_of_classicalRiemannHypothesis
  · exact classicalRiemannHypothesis_of_mathlibRiemannHypothesis

/-- Local no-offline formulation of classical RH:
    in the classical critical strip, a zero of `riemannZeta` cannot live
    off the critical line `Re(s) = 1/2`. -/
theorem noOfflineRiemannZetaZeros_of_classicalRiemannHypothesis
    (hRH : ClassicalRiemannHypothesis) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 → False := by
  intro s hs hs_pos hs_lt hneq
  exact hneq (hRH s hs hs_pos hs_lt)

/-- Global no-offline formulation using mathlib's `RiemannHypothesis`:
    every nontrivial zero of `riemannZeta` already lies on the critical line,
    so an off-line nontrivial zero is impossible. -/
theorem noOfflineRiemannZetaZeros_of_mathlibRiemannHypothesis
    (hRH : MathlibRiemannHypothesis) :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re ≠ 1 / 2 → False := by
  intro s hs hnontrivial hs_ne_one hneq
  exact hneq (hRH s hs hnontrivial hs_ne_one)

/-- Formal zero-correspondence from the symmetric-sum Robespierre model
    `RobespierreZeta = ΞInfinite` to classical coordinates. -/
def XiRobespierreZeroToClassicalZero (ζ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 → 0 < s.re → s.re < 2 * θ →
    ζ (robespierreToClassical s) = 0

/-- Preferred formal zero-correspondence from the transported classical
    Robespierre model `RobespierreZetaO` to classical coordinates. -/
def RobespierreZeroToClassicalZero (ζ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, RobespierreZetaO s = 0 → 0 < s.re → s.re < 2 * θ →
    ζ (robespierreOToClassical s) = 0

/-- Formal zero-correspondence from classical coordinates into the
    symmetric-sum Robespierre model `RobespierreZeta = ΞInfinite`. -/
def ClassicalZeroToXiRobespierreZero (ζ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ζ s = 0 → 0 < s.re → s.re < 1 →
    0 < (classicalToRobespierre s).re ∧
      (classicalToRobespierre s).re < 2 * θ ∧
      RobespierreZeta (classicalToRobespierre s) = 0

/-- Preferred formal zero-correspondence from classical coordinates into the
    transported classical Robespierre model `RobespierreZetaO`. -/
def ClassicalZeroToRobespierreZero (ζ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ζ s = 0 → 0 < s.re → s.re < 1 →
    0 < (classicalToRobespierreO s).re ∧
      (classicalToRobespierreO s).re < 2 * θ ∧
      RobespierreZetaO (classicalToRobespierreO s) = 0

/-- The specialized symmetric-sum Robespierre-to-classical zero
    correspondence for mathlib's `riemannZeta`. -/
def XiRobespierreZeroToRiemannZetaZero : Prop :=
  XiRobespierreZeroToClassicalZero riemannZeta

/-- The specialized preferred Robespierre-to-classical zero correspondence for
    mathlib's `riemannZeta`, using `RobespierreZetaO`. -/
def RobespierreZeroToRiemannZetaZero : Prop :=
  RobespierreZeroToClassicalZero riemannZeta

/-- The specialized classical-to-symmetric-sum Robespierre zero
    correspondence for mathlib's `riemannZeta`. -/
def RiemannZetaZeroToXiRobespierreZero : Prop :=
  ClassicalZeroToXiRobespierreZero riemannZeta

/-- The specialized preferred classical-to-Robespierre zero correspondence for
    mathlib's `riemannZeta`, using `RobespierreZetaO`. -/
def RiemannZetaZeroToRobespierreZero : Prop :=
  ClassicalZeroToRobespierreZero riemannZeta

/-- If classical RH holds and zeros of the symmetric-sum Robespierre model map
    to classical zeros by the `sin` lift, then every Robespierre zero in the
    θ-native critical strip lies on `Re(s) = θ`. -/
theorem xiRobespierreHypothesis_of_classicalRH
    {ζ : ℂ → ℂ}
    (hRH : ClassicalRH ζ)
    (hcorr : XiRobespierreZeroToClassicalZero ζ) :
    RobespierreHypothesis := by
  intro s hs hs_pos hs_lt
  have hzero_classical : ζ (robespierreToClassical s) = 0 :=
    hcorr s hs hs_pos hs_lt
  have hs_lt_pi : s.re < Real.pi := by
    rw [θ_eq] at hs_lt
    linarith [hs_lt, Real.pi_pos]
  have hs_lt_pi_div_two : s.re < Real.pi / 2 := by
    rw [θ_eq] at hs_lt
    linarith [hs_lt, Real.pi_pos]
  have hclassical_pos : 0 < (robespierreToClassical s).re := by
    simp [robespierreToClassical]
    exact Real.sin_pos_of_pos_of_lt_pi hs_pos hs_lt_pi
  have hclassical_lt : (robespierreToClassical s).re < 1 := by
    have hsin_lt : Real.sin s.re < Real.sin (Real.pi / 2) := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hs_pos]) le_rfl hs_lt_pi_div_two
    simpa [robespierreToClassical, Real.sin_pi_div_two] using hsin_lt
  have hcrit : (robespierreToClassical s).re = 1 / 2 :=
    hRH (robespierreToClassical s) hzero_classical hclassical_pos hclassical_lt
  have hsin_eq : Real.sin s.re = Real.sin θ := by
    have hθ_half : Real.sin θ = 1 / 2 := by
      simpa [theta_eq_circle_theta] using sin_theta
    rw [hθ_half]
    simpa [robespierreToClassical] using hcrit
  have hs_mem : s.re ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hs_pos]
    · linarith [hs_lt_pi_div_two]
  have hθ_mem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [θ_eq]
    constructor <;> linarith [Real.pi_pos]
  exact Real.strictMonoOn_sin.injOn hs_mem hθ_mem hsin_eq

/-- Classical RH plus the `sin` zero-correspondence implies the preferred
    symmetry-axis bridge for zeros of the symmetric-sum Robespierre model. -/
theorem xiZeroAxisBridge_of_classicalRH
    {ζ : ℂ → ℂ}
    (hRH : ClassicalRH ζ)
    (hcorr : XiRobespierreZeroToClassicalZero ζ) :
    ZeroAxisBridge := by
  intro s hs hs_pos hs_lt hoff
  have haxis : s.re = θ :=
    xiRobespierreHypothesis_of_classicalRH hRH hcorr s hs hs_pos hs_lt
  exact (symmetry_plane_iff_theta s.re).mpr haxis

/-- If the symmetric-sum Robespierre hypothesis holds and classical zeros lift
    into the θ-native critical strip via `arcsin`, then classical RH follows. -/
theorem classicalRH_of_xiRobespierreHypothesis
    {ζ : ℂ → ℂ}
    (hRH : RobespierreHypothesis)
    (hcorr : ClassicalZeroToXiRobespierreZero ζ) :
    ClassicalRH ζ := by
  intro s hs hs_pos hs_lt
  rcases hcorr s hs hs_pos hs_lt with ⟨hrob_pos, hrob_lt, hrob_zero⟩
  have haxis : (classicalToRobespierre s).re = θ :=
    hRH (classicalToRobespierre s) hrob_zero hrob_pos hrob_lt
  have harcsin : Real.arcsin s.re = θ := by
    simpa [classicalToRobespierre] using haxis
  have hs_half : s.re = 1 / 2 := by
    have := congrArg Real.sin harcsin
    have hθ_half : Real.sin θ = 1 / 2 := by
      simpa [theta_eq_circle_theta] using sin_theta
    rw [Real.sin_arcsin (by linarith [hs_pos]) hs_lt.le, hθ_half] at this
    exact this
  exact hs_half

/-- Under the two explicit zero-correspondence lifts (`sin` from the
    symmetric-sum Robespierre model to classical coordinates, `arcsin` back),
    classical RH and the `ΞInfinite` Robespierre hypothesis are equivalent. -/
theorem classicalRH_iff_xiRobespierreHypothesis
    {ζ : ℂ → ℂ}
    (hRC : XiRobespierreZeroToClassicalZero ζ)
    (hCR : ClassicalZeroToXiRobespierreZero ζ) :
    ClassicalRH ζ ↔ RobespierreHypothesis := by
  constructor
  · exact fun h => xiRobespierreHypothesis_of_classicalRH h hRC
  · exact fun h => classicalRH_of_xiRobespierreHypothesis h hCR

/-- If classical RH holds and Robespierre zeros map to classical zeros by the
    linear strip transport, then every `RobespierreZetaO` zero in the
    θ-native critical strip lies on `Re(s)=θ`. This is the preferred
    classical bridge. -/
theorem robespierreHypothesis_of_classicalRH
    {ζ : ℂ → ℂ}
    (hRH : ClassicalRH ζ)
    (hcorr : RobespierreZeroToClassicalZero ζ) :
    RobespierreOHypothesis := by
  intro s hs hs_pos hs_lt
  have hzero_classical : ζ (robespierreOToClassical s) = 0 :=
    hcorr s hs hs_pos hs_lt
  have hclassical_pos : 0 < (robespierreOToClassical s).re := by
    simpa [robespierreOToClassical] using div_pos hs_pos two_theta_pos
  have hclassical_lt : (robespierreOToClassical s).re < 1 := by
    have hdiv : s.re / (2 * θ) < 1 := (div_lt_one two_theta_pos).2 hs_lt
    simpa [robespierreOToClassical] using hdiv
  have hcrit : (robespierreOToClassical s).re = 1 / 2 :=
    hRH (robespierreOToClassical s) hzero_classical hclassical_pos hclassical_lt
  have hscaled : s.re / (2 * θ) = 1 / 2 := by
    simpa [robespierreOToClassical] using hcrit
  have hscale_ne : (2 * θ : ℝ) ≠ 0 := ne_of_gt two_theta_pos
  have haxis' : s.re = (1 / 2 : ℝ) * (2 * θ) := (div_eq_iff hscale_ne).mp hscaled
  have haxis : s.re = θ := by
    nlinarith
  simpa [θ] using haxis

/-- If the transported-classical Robespierre hypothesis holds and classical
    zeros lift into `RobespierreZetaO` by the inverse linear strip transport,
    then classical RH follows. This is the preferred reverse bridge. -/
theorem classicalRH_of_robespierreHypothesis
    {ζ : ℂ → ℂ}
    (hRH : RobespierreOHypothesis)
    (hcorr : ClassicalZeroToRobespierreZero ζ) :
    ClassicalRH ζ := by
  intro s hs hs_pos hs_lt
  rcases hcorr s hs hs_pos hs_lt with ⟨hrob_pos, hrob_lt, hrob_zero⟩
  have haxis : (classicalToRobespierreO s).re = θ := by
    have htmp := hRH (classicalToRobespierreO s) hrob_zero hrob_pos hrob_lt
    simpa [θ] using htmp
  have hscaled : (2 * θ) * s.re = θ := by
    simpa [classicalToRobespierreO] using haxis
  have hs_half : s.re = 1 / 2 := by
    have hscale_ne : (2 * θ : ℝ) ≠ 0 := ne_of_gt two_theta_pos
    apply (mul_right_cancel₀ hscale_ne)
    calc
      s.re * (2 * θ) = (2 * θ) * s.re := by ring
      _ = θ := hscaled
      _ = (1 / 2 : ℝ) * (2 * θ) := by ring
  exact hs_half

/-- Structural equivalence between classical RH and the Euler-product
    Robespierre hypothesis, under the two explicit zero lifts. This is the
    preferred equivalence theorem. -/
theorem classicalRH_iff_robespierreHypothesis
    {ζ : ℂ → ℂ}
    (hRC : RobespierreZeroToClassicalZero ζ)
    (hCR : ClassicalZeroToRobespierreZero ζ) :
    ClassicalRH ζ ↔ RobespierreOHypothesis := by
  constructor
  · exact fun h => robespierreHypothesis_of_classicalRH h hRC
  · exact fun h => classicalRH_of_robespierreHypothesis h hCR

/-- The transported Robespierre model `RobespierreZetaO` maps its zeros to
    zeros of mathlib's `riemannZeta` by definition. -/
theorem robespierreZeroToRiemannZetaZero_transport :
    RobespierreZeroToRiemannZetaZero := by
  intro s hs _ _
  simpa [RobespierreZeroToRiemannZetaZero, RobespierreZeroToClassicalZero,
    RobespierreZetaO, robespierreOToClassical] using hs

/-- Classical `riemannZeta` zeros lift into the transported Robespierre model
    by the inverse linear strip transport. -/
theorem riemannZetaZeroToRobespierreZero_transport :
    RiemannZetaZeroToRobespierreZero := by
  intro s hs hs_pos hs_lt
  refine ⟨?_, ?_, ?_⟩
  · simpa [classicalToRobespierreO] using mul_pos two_theta_pos hs_pos
  · simpa [classicalToRobespierreO] using mul_lt_mul_of_pos_left hs_lt two_theta_pos
  · simpa [RiemannZetaZeroToRobespierreZero, ClassicalZeroToRobespierreZero,
      RobespierreZetaO, robespierreOToClassical, classicalToRobespierreO,
      two_theta_pos.ne'] using hs

/-- Specialized consequence for mathlib's `riemannZeta` for the
    symmetric-sum Robespierre model. -/
theorem xiRobespierreHypothesis_of_classicalRiemannHypothesis
    (hRH : ClassicalRiemannHypothesis)
    (hcorr : XiRobespierreZeroToRiemannZetaZero) :
    RobespierreHypothesis :=
  xiRobespierreHypothesis_of_classicalRH hRH hcorr

/-- Specialized axis-bridge consequence for the symmetric-sum model. -/
theorem xiZeroAxisBridge_of_classicalRiemannHypothesis
    (hRH : ClassicalRiemannHypothesis)
    (hcorr : XiRobespierreZeroToRiemannZetaZero) :
    ZeroAxisBridge :=
  xiZeroAxisBridge_of_classicalRH hRH hcorr

/-- Specialized reverse implication for the symmetric-sum model. -/
theorem classicalRiemannHypothesis_of_xiRobespierreHypothesis
    (hRH : RobespierreHypothesis)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    ClassicalRiemannHypothesis :=
  classicalRH_of_xiRobespierreHypothesis hRH hcorr

/-- Structural equivalence between classical RH for mathlib's `riemannZeta`
    and the symmetric-sum Robespierre hypothesis. -/
theorem classicalRiemannHypothesis_iff_xiRobespierreHypothesis
    (hRC : XiRobespierreZeroToRiemannZetaZero)
    (hCR : RiemannZetaZeroToXiRobespierreZero) :
    ClassicalRiemannHypothesis ↔ RobespierreHypothesis :=
  classicalRH_iff_xiRobespierreHypothesis hRC hCR

/-- Specialized consequence for mathlib's `riemannZeta` using the Euler-product
    Robespierre model `RobespierreZetaO`. The correspondence is now built into
    the definition, so no extra hypothesis is needed. -/
theorem robespierreHypothesis_of_classicalRiemannHypothesis
    (hRH : ClassicalRiemannHypothesis) :
    RobespierreOHypothesis :=
  robespierreHypothesis_of_classicalRH hRH robespierreZeroToRiemannZetaZero_transport

/-- Specialized reverse implication for the Euler-product Robespierre model.
    The transport is built in, so no extra hypothesis is needed. -/
theorem classicalRiemannHypothesis_of_robespierreHypothesis
    (hRH : RobespierreOHypothesis) :
    ClassicalRiemannHypothesis :=
  classicalRH_of_robespierreHypothesis hRH riemannZetaZeroToRobespierreZero_transport

/-- Structural equivalence between classical RH for mathlib's `riemannZeta`
    and the Euler-product Robespierre hypothesis. For `RobespierreZetaO`,
    the two zero lifts are definitional consequences of the transport. -/
theorem classicalRiemannHypothesis_iff_robespierreHypothesis
    :
    ClassicalRiemannHypothesis ↔ RobespierreOHypothesis :=
  classicalRH_iff_robespierreHypothesis
    robespierreZeroToRiemannZetaZero_transport
    riemannZetaZeroToRobespierreZero_transport

/-- Specialized consequence starting from mathlib's own `RiemannHypothesis`
    proposition. -/
theorem robespierreHypothesis_of_mathlibRiemannHypothesis
    (hRH : MathlibRiemannHypothesis) :
    RobespierreOHypothesis :=
  robespierreHypothesis_of_classicalRiemannHypothesis
    (classicalRiemannHypothesis_of_mathlibRiemannHypothesis hRH)

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

/-- User-facing axis consequence: under the preferred zeta-side bridge, every
    Robespierre zero in the critical strip lies on the kernel axis `Re(s)=θ`. -/
theorem robespierre_zero_forces_theta_axis
    (hA : ZeroAxisBridge)
    {s : ℂ} (hz : RobespierreZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 2 * θ) :
    s.re = θ := by
  by_cases hoff : s.re = θ
  · exact hoff
  · exact (symmetry_plane_iff_theta s.re).mp (offAxis_zero_implies_axis hA hz h0 h1 hoff)

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

/-- The observed-dimensional-collapse bridge is an immediate consequence of
    the Robespierre Hypothesis itself: once zeros are on `Re(s)=θ`, their
    observed coordinate is `sin θ = 1/2`. -/
theorem zeroObservedDimensionalCollapseBridge_of_robespierreHypothesis
    (hRH : RobespierreHypothesis) :
    ZeroObservedDimensionalCollapseBridge := by
  intro s hs hs_pos hs_lt
  have hre : s.re = θ := hRH s hs hs_pos hs_lt
  rw [hre]
  simpa [theta_eq_circle_theta] using sin_theta

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

/-- On the θ-native critical strip, the symmetry-axis address `θ` and the
    classical detector address `1/2` are the same location read in the
    `σ`-chart and the `sin σ`-chart respectively. -/
theorem theta_iff_sin_eq_half {σ : ℝ}
    (hσ_pos : 0 < σ) (hσ_lt : σ < 2 * θ) :
    σ = θ ↔ Real.sin σ = 1 / 2 := by
  have hσ_lt_pi_div_two : σ < Real.pi / 2 := by
    have hσ_lt_pi_div_three : σ < Real.pi / 3 := by
      rw [show (2 * θ : ℝ) = Real.pi / 3 by rw [θ_eq]; ring] at hσ_lt
      exact hσ_lt
    linarith [hσ_lt_pi_div_three, Real.pi_pos]
  constructor
  · intro hσ
    rw [hσ]
    have hθ_half : Real.sin θ = 1 / 2 := by
      simpa [theta_eq_circle_theta] using sin_theta
    exact hθ_half
  · intro hsin
    have hθ_half : Real.sin θ = 1 / 2 := by
      simpa [theta_eq_circle_theta] using sin_theta
    have harcsin_eq :
        Real.arcsin (Real.sin σ) = Real.arcsin (Real.sin θ) := by
      rw [hsin, hθ_half]
    rw [Real.arcsin_sin (by linarith [hσ_pos]) hσ_lt_pi_div_two.le,
      Real.arcsin_sin] at harcsin_eq
    · exact harcsin_eq
    · rw [θ_eq]
      linarith [Real.pi_pos]
    · rw [θ_eq]
      linarith [Real.pi_pos]

/-- The planar dimensional-collapse condition:
    projecting the native angle `σ` into the plane by `sin` lands on the
    classical observed collapse coordinate `1/2`. -/
def PlanarDimensionalCollapse (σ : ℝ) : Prop :=
  Real.sin σ = 1 / 2

/-- Backward-compatible name for the planar observed-collapse condition. -/
abbrev ObservedDimensionalCollapse (σ : ℝ) : Prop :=
  PlanarDimensionalCollapse σ

/-- The harmonic-collapse condition in the native cosine channel. -/
def HarmonicCollapse (t : ℝ) : Prop :=
  CriticalLineSumInf t = 0

/-- On the native axis, kernel zeros are exactly harmonic collapses of the
    infinite cosine channel. -/
theorem native_axis_zero_iff_harmonicCollapse (t : ℝ) :
    RobespierreZeta (↑θ + ↑t * Complex.I) = 0 ↔ HarmonicCollapse t := by
  simpa [RobespierreZeta, HarmonicCollapse] using ΞInfinite_theta_axis_zero_iff t

/-- On the θ-native critical strip, the native axis address and the planar
    dimensional-collapse coordinate are equivalent descriptions of the same
    location. -/
theorem theta_iff_planarDimensionalCollapse {σ : ℝ}
    (hσ_pos : 0 < σ) (hσ_lt : σ < 2 * θ) :
    σ = θ ↔ PlanarDimensionalCollapse σ := by
  simpa [PlanarDimensionalCollapse] using theta_iff_sin_eq_half hσ_pos hσ_lt

/-- Backward-compatible observed-collapse name for the planar theorem. -/
theorem theta_iff_observedDimensionalCollapse {σ : ℝ}
    (hσ_pos : 0 < σ) (hσ_lt : σ < 2 * θ) :
    σ = θ ↔ ObservedDimensionalCollapse σ :=
  theta_iff_planarDimensionalCollapse hσ_pos hσ_lt

/-- Unconditional chart equivalence for native Robespierre zeros in the
    θ-native critical strip: the same zero address can be read either as
    `Re(s) = θ` in the native chart or as `sin(Re(s)) = 1/2` in the
    detector chart. -/
theorem native_zero_address_equiv
    {s : ℂ} (_hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ ↔ Real.sin s.re = 1 / 2 :=
  theta_iff_sin_eq_half hs_pos hs_lt

/-- Strip-level relationship theorem: for a native Robespierre zero in the
    θ-native critical strip, harmonic collapse at the native axis and planar
    dimensional collapse at `1/2` are the same event in two coordinate charts. -/
theorem native_zero_iff_planarDimensionalCollapse
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ ↔ PlanarDimensionalCollapse s.re := by
  simpa [PlanarDimensionalCollapse] using native_zero_address_equiv hs hs_pos hs_lt

/-- Backward-compatible observed-collapse statement for native zeros. -/
theorem native_zero_iff_observedDimensionalCollapse
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ ↔ ObservedDimensionalCollapse s.re :=
  native_zero_iff_planarDimensionalCollapse hs hs_pos hs_lt

/-- Projected Klein-four collapse is exactly planar dimensional collapse:
    after applying the `sin` address map, the four classical orbit points
    collapse precisely when the projected real coordinate lands at `1/2`. -/
theorem projected_kleinFourSymmetric_iff_planarDimensionalCollapse (s : ℂ) :
    KleinFourSymmetric (ZeroAddressProjection s) ↔ PlanarDimensionalCollapse s.re := by
  constructor
  · intro hsymm
    have hre : Real.sin s.re = Real.sin theta := by
      simpa [ZeroAddressProjection] using
        (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mp hsymm
    rw [PlanarDimensionalCollapse]
    exact hre.trans sin_theta
  · intro hcollapse
    have hre : (ZeroAddressProjection s).re = Real.sin theta := by
      rw [sin_theta]
      simpa [PlanarDimensionalCollapse, ZeroAddressProjection] using hcollapse
    exact (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mpr hre

/-- On the θ-native strip, projected Klein-four collapse and native reflection
    collapse are the same event. This is the precise theorem form of
    “one zero, two addresses”. -/
theorem projected_kleinFourSymmetric_iff_theta
    {s : ℂ} (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ↔ s.re = θ := by
  rw [projected_kleinFourSymmetric_iff_planarDimensionalCollapse]
  simpa [iff_comm] using (theta_iff_planarDimensionalCollapse hs_pos hs_lt)

/-- Numberline uniqueness on the θ-native strip:
    once the projected address collapses to the unique classical numberline
    value `1/2`, the native address is forced to be `θ`. This is the
    unconditional `sin/arcsin` uniqueness step that closes the address map. -/
theorem projected_numberline_uniqueness
    {s : ℂ} (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ)
    (hproj : KleinFourSymmetric (ZeroAddressProjection s)) :
    s.re = θ :=
  (projected_kleinFourSymmetric_iff_theta hs_pos hs_lt).mp hproj

/-- The native symmetry axis is exactly the unique preimage of the projected
    Klein-four collapse point on the θ-strip. -/
theorem projected_numberline_uniqueness_iff
    {s : ℂ} (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ↔ s.re = θ :=
  projected_kleinFourSymmetric_iff_theta hs_pos hs_lt

/-- `cos` and `sin` package the same collapse event in two charts:
    for a native Robespierre zero in the strip, planar dimensional collapse
    in the `sin`-chart is equivalent to the existence of an axis parameter
    `t` where harmonic collapse occurs in the `cos`-channel. -/
theorem native_zero_cos_planar_equivalence
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    PlanarDimensionalCollapse s.re ↔
      ∃ t : ℝ, s = ↑θ + ↑t * Complex.I ∧ HarmonicCollapse t := by
  constructor
  · intro hobs
    have haxis : s.re = θ :=
      (theta_iff_planarDimensionalCollapse hs_pos hs_lt).mpr hobs
    have hs_eq : s = ↑θ + ↑s.im * Complex.I := by
      apply Complex.ext <;> simp [haxis]
    refine ⟨s.im, hs_eq, ?_⟩
    · have hs_axis : RobespierreZeta (↑θ + ↑s.im * Complex.I) = 0 := by
        exact hs_eq ▸ hs
      exact (native_axis_zero_iff_harmonicCollapse s.im).mp hs_axis
  · intro h
    rcases h with ⟨t, hs_axis, _⟩
    have haxis : s.re = θ := by
      simpa [hs_axis]
    exact (theta_iff_planarDimensionalCollapse hs_pos hs_lt).mp haxis

/-- Backward-compatible `cos/sin` collapse theorem using the older
    observed-collapse name. -/
theorem native_zero_cos_sin_equivalence
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    ObservedDimensionalCollapse s.re ↔
      ∃ t : ℝ, s = ↑θ + ↑t * Complex.I ∧ HarmonicCollapse t := by
  simpa [ObservedDimensionalCollapse] using
    native_zero_cos_planar_equivalence hs hs_pos hs_lt

/-- Direct same-zero formulation of the `cos/sin` relationship:
    for a native Robespierre zero in the strip, planar dimensional collapse
    in the `sin`-channel is equivalent to being on the native axis together
    with harmonic collapse in the `cos`-channel at the same height. -/
theorem native_zero_harmonic_planar_same_height_equivalence
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    PlanarDimensionalCollapse s.re ↔
      s.re = θ ∧ HarmonicCollapse s.im := by
  constructor
  · intro hobs
    have haxis : s.re = θ :=
      (theta_iff_planarDimensionalCollapse hs_pos hs_lt).mpr hobs
    have hs_axis : RobespierreZeta (↑θ + ↑s.im * Complex.I) = 0 := by
      have hs_eq : s = ↑θ + ↑s.im * Complex.I := by
        apply Complex.ext <;> simp [haxis]
      exact hs_eq ▸ hs
    exact ⟨haxis, (native_axis_zero_iff_harmonicCollapse s.im).mp hs_axis⟩
  · intro h
    exact (theta_iff_planarDimensionalCollapse hs_pos hs_lt).mp h.1

/-- Backward-compatible same-height `cos/sin` theorem using the older
    observed-collapse name. -/
theorem native_zero_cos_sin_same_height_equivalence
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    ObservedDimensionalCollapse s.re ↔
      s.re = θ ∧ HarmonicCollapse s.im := by
  simpa [ObservedDimensionalCollapse] using
    native_zero_harmonic_planar_same_height_equivalence hs hs_pos hs_lt

/-- Explanatory RH thesis:
    for a native Robespierre zero in the critical strip, the classical
    `1/2`-collapse is not a separate analytic event but the planar
    one-dimensional reading of the same native harmonic collapse.

    In this formulation, the reason the classical critical coordinate is `1/2`
    is geometric: harmonic cancellation occurs on the native axis `Re(s)=θ`,
    and dimensional collapse reads that same address through `sin`, producing
    the observed value `sin θ = 1/2`. -/
theorem rh_explanatory_thesis
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    PlanarDimensionalCollapse s.re ↔
      s.re = θ ∧ HarmonicCollapse s.im :=
  native_zero_harmonic_planar_same_height_equivalence hs hs_pos hs_lt

/-- If every native zero in the strip is observed to collapse at `1/2`,
    then no off-axis zero remains. This packages the `sin`-side collapse
    directly into the `θ`-axis statement. -/
theorem noOffAxisZeros_of_zeroObservedDimensionalCollapseBridge
    (hobs : ZeroObservedDimensionalCollapseBridge) :
    NoOffAxisZeros := by
  intro s hs hs_pos hs_lt
  exact (theta_iff_sin_eq_half hs_pos hs_lt).mpr (hobs s hs hs_pos hs_lt)

/-- Planar-dimensional-collapse bridge version of the no-off-axis theorem. -/
theorem noOffAxisZeros_of_zeroPlanarDimensionalCollapseBridge
    (hobs : ZeroPlanarDimensionalCollapseBridge) :
    NoOffAxisZeros :=
  noOffAxisZeros_of_zeroObservedDimensionalCollapseBridge hobs

/-- If every native zero in the strip is observed to collapse at `1/2`,
    then the Robespierre Hypothesis follows. -/
theorem robespierreHypothesis_of_zeroObservedDimensionalCollapseBridge
    (hobs : ZeroObservedDimensionalCollapseBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis
    (noOffAxisZeros_of_zeroObservedDimensionalCollapseBridge hobs)

/-- Planar-dimensional-collapse bridge version of the Robespierre
    hypothesis theorem. -/
theorem robespierreHypothesis_of_zeroPlanarDimensionalCollapseBridge
    (hobs : ZeroPlanarDimensionalCollapseBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis_of_zeroObservedDimensionalCollapseBridge hobs

/-- The planar-dimensional-collapse bridge is equivalent to the native
    Robespierre hypothesis: every zero in the strip projects to the
    classical collapse coordinate `1/2` exactly when every zero lies on the
    native axis `Re(s)=θ`. -/
theorem zeroPlanarDimensionalCollapseBridge_iff_robespierreHypothesis :
    ZeroPlanarDimensionalCollapseBridge ↔ RobespierreHypothesis := by
  constructor
  · exact robespierreHypothesis_of_zeroPlanarDimensionalCollapseBridge
  · exact zeroObservedDimensionalCollapseBridge_of_robespierreHypothesis

/-- Backward-compatible equivalence theorem using the older
    observed-dimensional-collapse bridge name. -/
theorem zeroObservedDimensionalCollapseBridge_iff_robespierreHypothesis :
    ZeroObservedDimensionalCollapseBridge ↔ RobespierreHypothesis :=
  zeroPlanarDimensionalCollapseBridge_iff_robespierreHypothesis

/-- The first-prime anchor bridge is exactly the planar-dimensional-collapse
    bridge, since the native-to-classical projection reads the real part
    through `sin`. -/
theorem firstPrimeAnchorBridge_iff_zeroPlanarDimensionalCollapseBridge :
    FirstPrimeAnchorBridge ↔ ZeroPlanarDimensionalCollapseBridge := by
  constructor
  · intro hanchor s hs hs_pos hs_lt
    simpa [FirstPrimeAnchorBridge, ZeroAddressProjection] using hanchor s hs hs_pos hs_lt
  · intro hplanar s hs hs_pos hs_lt
    simpa [FirstPrimeAnchorBridge, ZeroAddressProjection] using hplanar s hs hs_pos hs_lt

/-- The projected-detector bridge is exactly the first-prime anchor bridge:
    passing the detector after projection is equivalent to landing on the
    anchor value `1/2`. -/
theorem zeroProjectedDetectorBridge_iff_firstPrimeAnchorBridge :
    ZeroProjectedDetectorBridge ↔ FirstPrimeAnchorBridge := by
  constructor
  · intro hdet s hs hs_pos hs_lt
    have hpass : DetectorPasses (Real.sin s.re) := hdet s hs hs_pos hs_lt
    have hproj : Real.sin s.re = Real.sin theta :=
      (detector_iff_sin_theta (Real.sin s.re)).mp hpass
    simpa [sin_theta] using hproj
  · intro hanchor s hs hs_pos hs_lt
    have hsin : Real.sin s.re = Real.sin theta := by
      have hhalf : Real.sin s.re = 1 / 2 := hanchor s hs hs_pos hs_lt
      rw [sin_theta]
      exact hhalf
    exact (detector_iff_sin_theta (Real.sin s.re)).mpr hsin

/-- Full Klein-four collapse on the projected classical point implies the
    projected detector bridge. The four-way orbit collapse fixes the projected
    real coordinate at `sin θ = 1/2`, so the classical detector passes. -/
theorem zeroProjectedDetectorBridge_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge) :
    ZeroProjectedDetectorBridge := by
  intro s hs hs_pos hs_lt
  have hsymm : KleinFourSymmetric (ZeroAddressProjection s) :=
    hklein s hs hs_pos hs_lt
  have hre : (ZeroAddressProjection s).re = Real.sin theta :=
    (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mp hsymm
  simpa [ZeroAddressProjection] using
    (detector_iff_sin_theta ((ZeroAddressProjection s).re)).mpr hre

/-- The projected Klein-four bridge is equivalent to the first-prime anchor
    bridge: four-way orbit collapse on the projected point is exactly the
    statement that its real coordinate is the anchored value `1/2`. -/
theorem harmonicPrimeRigidityBridge_iff_firstPrimeAnchorBridge :
    HarmonicPrimeRigidityBridge ↔ FirstPrimeAnchorBridge := by
  constructor
  · intro hklein s hs hs_pos hs_lt
    have hsymm : KleinFourSymmetric (ZeroAddressProjection s) :=
      hklein s hs hs_pos hs_lt
    have hre : (ZeroAddressProjection s).re = Real.sin theta :=
      (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mp hsymm
    simpa [ZeroAddressProjection, sin_theta] using hre
  · intro hanchor s hs hs_pos hs_lt
    have hre : (ZeroAddressProjection s).re = Real.sin theta := by
      rw [sin_theta]
      simpa [ZeroAddressProjection] using hanchor s hs hs_pos hs_lt
    exact (klein_symmetric_iff_sin_theta (ZeroAddressProjection s)).mpr hre

/-- Detector form of the native closure: if every native zero projects to a
    detector pass in the classical coordinate, then the Robespierre
    Hypothesis follows. -/
theorem robespierreHypothesis_of_zeroProjectedDetectorBridge
    (hdet : ZeroProjectedDetectorBridge) :
    RobespierreHypothesis := by
  exact robespierreHypothesis_of_zeroPlanarDimensionalCollapseBridge
    ((firstPrimeAnchorBridge_iff_zeroPlanarDimensionalCollapseBridge.mp <|
      zeroProjectedDetectorBridge_iff_firstPrimeAnchorBridge.mp hdet))

/-- The first-prime anchor bridge is equivalent to the native Robespierre
    hypothesis. This is the proof-facing arithmetic closure of the statement
    “the first prime fixes the classical zero address `1/2`”. -/
theorem firstPrimeAnchorBridge_iff_robespierreHypothesis :
    FirstPrimeAnchorBridge ↔ RobespierreHypothesis := by
  rw [firstPrimeAnchorBridge_iff_zeroPlanarDimensionalCollapseBridge]
  exact zeroPlanarDimensionalCollapseBridge_iff_robespierreHypothesis

/-- If the first-prime anchor fixes the classical zero address `1/2` for every
    native zero in the strip, then the Robespierre Hypothesis follows. -/
theorem robespierreHypothesis_of_firstPrimeAnchorBridge
    (hanchor : FirstPrimeAnchorBridge) :
    RobespierreHypothesis := by
  exact (firstPrimeAnchorBridge_iff_robespierreHypothesis.mp hanchor)

/-- If every native zero in the strip satisfies planar dimensional collapse,
    then the native Robespierre hypothesis follows; combined with the existing
    classical-to-native zero lift, this yields mathlib's global
    `RiemannHypothesis`. -/
theorem mathlibRiemannHypothesis_of_zeroPlanarDimensionalCollapseBridge
    (hobs : ZeroPlanarDimensionalCollapseBridge)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    MathlibRiemannHypothesis :=
  mathlibRiemannHypothesis_of_classicalRiemannHypothesis <|
    classicalRiemannHypothesis_of_xiRobespierreHypothesis
      (robespierreHypothesis_of_zeroPlanarDimensionalCollapseBridge hobs) hcorr

/-- First-prime anchor version of the classical consequence:
    once the native zero address is forced to project to `1/2`, the existing
    native-to-classical lift yields mathlib's global `RiemannHypothesis`. -/
theorem mathlibRiemannHypothesis_of_firstPrimeAnchorBridge
    (hanchor : FirstPrimeAnchorBridge)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    MathlibRiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_zeroPlanarDimensionalCollapseBridge
    (firstPrimeAnchorBridge_iff_zeroPlanarDimensionalCollapseBridge.mp hanchor)
    hcorr

/-- Detector-form classical consequence:
    once every native zero projects to a classical detector pass, the
    native-to-classical zero lift yields mathlib's global RH. -/
theorem mathlibRiemannHypothesis_of_zeroProjectedDetectorBridge
    (hdet : ZeroProjectedDetectorBridge)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    MathlibRiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_firstPrimeAnchorBridge
    (zeroProjectedDetectorBridge_iff_firstPrimeAnchorBridge.mp hdet)
    hcorr

/-- Klein-four form of the native closure:
    if every native zero projects to a fully symmetric Klein-four orbit in
    classical coordinates, then the Robespierre Hypothesis follows. -/
theorem robespierreHypothesis_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge) :
    RobespierreHypothesis := by
  intro s hs hs_pos hs_lt
  exact projected_numberline_uniqueness hs_pos hs_lt (hklein s hs hs_pos hs_lt)

/-- Linked-collapse theorem:
    if every native zero projects to a collapsed Klein-four orbit, then any
    native zero in the strip simultaneously exhibits
    1. classical/projected Klein-four collapse at `1/2`, and
    2. native reflection collapse at the symmetry center `θ`.

    This packages the user's intended contradiction principle: both collapse
    systems must occur together for a genuine zero. -/
theorem zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧ SymmetryPlaneCheck s.re := by
  constructor
  · exact hklein s hs hs_pos hs_lt
  · exact (symmetry_plane_iff_theta s.re).mpr
      ((robespierreHypothesis_of_harmonicPrimeRigidityBridge hklein) s hs hs_pos hs_lt)

/-- Primary closure target:
    every native zero in the strip is a self-consistent collapse event,
    simultaneously exhibiting projected Klein-four collapse and native
    symmetry-plane collapse. -/
def NativeZeroSelfConsistentCollapse : Prop :=
  ∀ s : ℂ, RobespierreZeta s = 0 →
    0 < s.re → s.re < 2 * θ →
    KleinFourSymmetric (ZeroAddressProjection s) ∧ SymmetryPlaneCheck s.re

/-- Exact target theorem form:
    under harmonic-prime rigidity, every native zero is a self-consistent
    collapse event. -/
theorem native_zero_forces_self_consistent_collapse_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge) :
    NativeZeroSelfConsistentCollapse := by
  intro s hs hs_pos hs_lt
  exact zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge hklein hs hs_pos hs_lt

/-- Proving self-consistent collapse for every native zero is exactly the same
    remaining content as proving harmonic-prime rigidity. The projected part of
    the conjunction is the rigidity bridge, while the symmetry-plane part then
    follows from numberline uniqueness. -/
theorem nativeZeroSelfConsistentCollapse_iff_harmonicPrimeRigidityBridge :
    NativeZeroSelfConsistentCollapse ↔ HarmonicPrimeRigidityBridge := by
  constructor
  · intro h s hs hs_pos hs_lt
    exact (h s hs hs_pos hs_lt).1
  · intro hklein
    exact native_zero_forces_self_consistent_collapse_of_harmonicPrimeRigidityBridge hklein

/-- Final unconditional native target, recorded as a proposition:
    prove directly from the native kernel and projected detector that every
    native zero in the strip satisfies harmonic-prime rigidity. Once this
    proposition is inhabited, the rest of the Robespierre and classical RH
    chain is already formalized. -/
def HarmonicPrimeRigidityGoal : Prop :=
  HarmonicPrimeRigidityBridge

/-- Self-consistent dual collapse:
    a genuine native zero must collapse in both coupled systems at once.
    The projected/classical side collapses at `1/2`, while the native
    harmonic side collapses at `θ = π/6`. This is the formal theorem form of
    the user's “one zero, two addresses, one self-consistent event” claim. -/
theorem native_zero_forces_self_consistent_dual_collapse_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧ s.re = θ := by
  have hlinked :=
    zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge
      hklein hs hs_pos hs_lt
  refine ⟨hlinked.1, ?_⟩
  exact (symmetry_plane_iff_theta s.re).mp hlinked.2

/-- Proof-term packaging of the user's "one zero, two addresses" claim:
    for a genuine native zero in the `θ`-strip, the projected/classical
    collapse at `1 / 2` and the native harmonic collapse at `θ = π / 6`
    are one self-consistent event. The projected Klein-four symmetry is the
    prime-side witness, the planar collapse records the `1 / 2` address, and
    the native side is forced onto `θ` with harmonic collapse at the same
    height. -/
theorem native_zero_forces_self_consistent_collapse_event_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧
      PlanarDimensionalCollapse s.re ∧
      s.re = θ ∧ HarmonicCollapse s.im := by
  have hproj : KleinFourSymmetric (ZeroAddressProjection s) :=
    (zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge
      hklein hs hs_pos hs_lt).1
  have hplanar : PlanarDimensionalCollapse s.re :=
    (projected_kleinFourSymmetric_iff_planarDimensionalCollapse s).mp hproj
  have hsame : s.re = θ ∧ HarmonicCollapse s.im :=
    (native_zero_harmonic_planar_same_height_equivalence hs hs_pos hs_lt).mp hplanar
  exact ⟨hproj, hplanar, hsame⟩

/-- Reflected-numberline self-consistency for a native zero:
    once a zero in the `θ`-strip is anchored by either system, all collapse
    descriptions agree. The projected Klein-four address, the planar `1/2`
    address, the native symmetry-plane address `θ`, and the same-height
    harmonic collapse are equivalent readings of one reflected numberline
    event. This theorem is unconditional in the sense that it no longer
    assumes the global rigidity bridge; it only uses the specific zero `s`
    and its strip bounds. -/
theorem native_zero_reflected_numberline_self_consistency
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ↔
      PlanarDimensionalCollapse s.re ∧
        SymmetryPlaneCheck s.re ∧
        s.re = θ ∧
        HarmonicCollapse s.im := by
  constructor
  · intro hproj
    have hplanar : PlanarDimensionalCollapse s.re :=
      (projected_kleinFourSymmetric_iff_planarDimensionalCollapse s).mp hproj
    have hsame : s.re = θ ∧ HarmonicCollapse s.im :=
      (native_zero_harmonic_planar_same_height_equivalence hs hs_pos hs_lt).mp hplanar
    exact ⟨hplanar, (symmetry_plane_iff_theta s.re).mpr hsame.1, hsame⟩
  · intro h
    exact (projected_kleinFourSymmetric_iff_planarDimensionalCollapse s).mpr h.1

/-- Global-rigidity wrapper:
    if harmonic-prime rigidity is available as a global fact, a native zero in
    the strip is automatically a self-consistent collapse event in both charts. -/
theorem native_zero_forces_self_consistent_collapse_event
    [Fact HarmonicPrimeRigidityBridge]
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧
      PlanarDimensionalCollapse s.re ∧
      s.re = θ ∧ HarmonicCollapse s.im := by
  exact native_zero_forces_self_consistent_collapse_event_of_harmonicPrimeRigidityBridge
    Fact.out hs hs_pos hs_lt

/-- First-prime-anchor version of the same global theorem:
    if every native zero projects to the reflected numberline collapse value
    `1/2`, then any native zero in the strip is automatically the same
    harmonic-collapse event read in both systems. -/
theorem native_zero_forces_self_consistent_collapse_event_of_firstPrimeAnchorBridge
    (hanchor : FirstPrimeAnchorBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧
      PlanarDimensionalCollapse s.re ∧
      s.re = θ ∧ HarmonicCollapse s.im := by
  have hklein : HarmonicPrimeRigidityBridge :=
    (harmonicPrimeRigidityBridge_iff_firstPrimeAnchorBridge).2 hanchor
  exact native_zero_forces_self_consistent_collapse_event_of_harmonicPrimeRigidityBridge
    hklein hs hs_pos hs_lt

/-- Instance-style wrapper for the reflected `1/2` anchor formulation. -/
theorem native_zero_forces_self_consistent_collapse_event_of_global_anchor
    [Fact FirstPrimeAnchorBridge]
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧
      PlanarDimensionalCollapse s.re ∧
      s.re = θ ∧ HarmonicCollapse s.im := by
  exact native_zero_forces_self_consistent_collapse_event_of_firstPrimeAnchorBridge
    Fact.out hs hs_pos hs_lt

/-- One zero, two addresses:
    under the double projected Klein-four bridge, a native zero in the strip
    exhibits projected classical Klein-four collapse if and only if it lies on
    the native reflection axis `θ`. Both systems collapse together, or the zero
    cannot exist in the strip. -/
theorem native_zero_one_zero_two_addresses
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ↔ s.re = θ := by
  constructor
  · intro hproj
    exact projected_numberline_uniqueness hs_pos hs_lt hproj
  · intro hθ
    exact (zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge
      hklein hs hs_pos hs_lt).1

/-- Contradiction form of linked collapse:
    under the projected Klein-four bridge, an off-axis native zero cannot
    exist, because the projected classical collapse and the native reflection
    collapse must occur simultaneously. -/
theorem offaxis_zero_impossible_by_linked_collapse
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ)
    (hoff : s.re ≠ θ) :
    False := by
  have hlinked :=
    zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge
      hklein hs hs_pos hs_lt
  exact hoff ((symmetry_plane_iff_theta s.re).mp hlinked.2)

/-- Contradiction form of self-consistent dual collapse:
    an off-axis candidate cannot remain simultaneously consistent with the
    native harmonic collapse and the projected classical collapse. -/
theorem offaxis_zero_breaks_self_consistent_dual_collapse
    (hklein : HarmonicPrimeRigidityBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ)
    (hoff : s.re ≠ θ) :
    False :=
  offaxis_zero_impossible_by_linked_collapse hklein hs hs_pos hs_lt hoff

/-- Klein-four form of the classical consequence:
    full projected orbit collapse yields the projected detector bridge, hence
    the first-prime anchor, and then mathlib's global `RiemannHypothesis`. -/
theorem mathlibRiemannHypothesis_of_harmonicPrimeRigidityBridge
    (hklein : HarmonicPrimeRigidityBridge)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    MathlibRiemannHypothesis := by
  exact mathlibRiemannHypothesis_of_zeroProjectedDetectorBridge
    (zeroProjectedDetectorBridge_of_harmonicPrimeRigidityBridge hklein)
    hcorr

/-- Final RH closure through the transported model `RobespierreZetaO`:
    no extra zero-lift assumptions are needed, because the strip transport is
    already proved in this file. -/
theorem mathlibRiemannHypothesis_of_robespierreOHypothesis
    (hRH : RobespierreOHypothesis) :
    MathlibRiemannHypothesis :=
  mathlibRiemannHypothesis_of_classicalRiemannHypothesis <|
    classicalRiemannHypothesis_of_robespierreHypothesis hRH

/-- Typeclass wrapper for the transported-model closure of RH. -/
theorem mathlibRiemannHypothesis_closed_of_global_robespierreO
    [Fact RobespierreOHypothesis] :
    MathlibRiemannHypothesis :=
  mathlibRiemannHypothesis_of_robespierreOHypothesis Fact.out

/-- Final endpoint in mathlib prop form, using `RobespierreZetaO`. -/
theorem mathlibRiemannHypothesis_closed
    [Fact RobespierreOHypothesis] :
    RiemannHypothesis :=
  mathlibRiemannHypothesis_closed_of_global_robespierreO

/-- Backward-compatible projected-detector consequence of the rigidity bridge. -/
theorem zeroProjectedDetectorBridge_of_doubleZeroProjectedKleinFourBridge
    (hklein : DoubleZeroProjectedKleinFourBridge) :
    ZeroProjectedDetectorBridge :=
  zeroProjectedDetectorBridge_of_harmonicPrimeRigidityBridge hklein

/-- Backward-compatible equivalence with the first-prime anchor bridge. -/
theorem doubleZeroProjectedKleinFourBridge_iff_firstPrimeAnchorBridge :
    DoubleZeroProjectedKleinFourBridge ↔ FirstPrimeAnchorBridge :=
  harmonicPrimeRigidityBridge_iff_firstPrimeAnchorBridge

/-- Backward-compatible native closure theorem. -/
theorem robespierreHypothesis_of_doubleZeroProjectedKleinFourBridge
    (hklein : DoubleZeroProjectedKleinFourBridge) :
    RobespierreHypothesis :=
  robespierreHypothesis_of_harmonicPrimeRigidityBridge hklein

/-- Backward-compatible linked-collapse theorem. -/
theorem zero_forces_linked_collapse_of_doubleZeroProjectedKleinFourBridge
    (hklein : DoubleZeroProjectedKleinFourBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧ SymmetryPlaneCheck s.re :=
  zero_forces_linked_collapse_of_harmonicPrimeRigidityBridge hklein hs hs_pos hs_lt

/-- Backward-compatible self-consistent dual-collapse theorem. -/
theorem native_zero_forces_self_consistent_dual_collapse_of_doubleZeroProjectedKleinFourBridge
    (hklein : DoubleZeroProjectedKleinFourBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) ∧ s.re = θ :=
  native_zero_forces_self_consistent_dual_collapse_of_harmonicPrimeRigidityBridge
    hklein hs hs_pos hs_lt

/-- Backward-compatible classical consequence of the rigidity bridge. -/
theorem mathlibRiemannHypothesis_of_doubleZeroProjectedKleinFourBridge
    (hklein : DoubleZeroProjectedKleinFourBridge)
    (hcorr : RiemannZetaZeroToXiRobespierreZero) :
    MathlibRiemannHypothesis :=
  mathlibRiemannHypothesis_of_harmonicPrimeRigidityBridge hklein hcorr

/-- Under the observed-dimensional-collapse bridge, every native zero in the
    θ-strip lies on the native symmetry axis. -/
theorem native_zero_on_theta_of_zeroObservedDimensionalCollapseBridge
    (hobs : ZeroObservedDimensionalCollapseBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ := by
  exact (theta_iff_observedDimensionalCollapse hs_pos hs_lt).mpr
    (hobs s hs hs_pos hs_lt)

/-- Under the observed-dimensional-collapse bridge, every native zero in the
    θ-strip is the same-height `cos/sin` collapse event: the zero sits on the
    native axis and its height is a harmonic collapse of the cosine channel. -/
theorem native_zero_same_height_collapse_of_zeroObservedDimensionalCollapseBridge
    (hobs : ZeroObservedDimensionalCollapseBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ ∧ HarmonicCollapse s.im := by
  exact (native_zero_cos_sin_same_height_equivalence hs hs_pos hs_lt).mp
    (hobs s hs hs_pos hs_lt)

/-- Primary same-height `sin/cos` bridge statement:
    under the planar-dimensional-collapse bridge, every native zero in the
    strip is both on the native axis and a harmonic collapse at its height. -/
theorem native_zero_same_height_collapse_of_zeroPlanarDimensionalCollapseBridge
    (hobs : ZeroPlanarDimensionalCollapseBridge)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    s.re = θ ∧ HarmonicCollapse s.im :=
  native_zero_same_height_collapse_of_zeroObservedDimensionalCollapseBridge
    hobs hs hs_pos hs_lt

/-- Native-kernel to classical-line projection:
    if a zero of `RobespierreZeta = ΞInfinite` lies in the θ-native critical
    strip, then projecting its real part by `sin` lands on the classical
    critical-line coordinate `1/2`. This packages the proof split
    "axis collapse at `θ`, dimensional collapse at `sin θ = 1/2`". -/
theorem native_zero_projects_to_classical_line
    (hRH : RobespierreHypothesis)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    Real.sin s.re = 1 / 2 := by
  have hre : s.re = theta := hRH s hs hs_pos hs_lt
  rw [hre]
  simpa [theta_eq_circle_theta] using sin_theta

/-- Under the native Robespierre hypothesis, every native zero projects to a
    classical point whose Klein-four orbit collapses at the shared rotation
    center `1/2`. -/
theorem native_zero_projects_to_kleinFourCollapse
    (hRH : RobespierreHypothesis)
    {s : ℂ} (hs : RobespierreZeta s = 0)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 2 * θ) :
    KleinFourSymmetric (ZeroAddressProjection s) := by
  exact theta_axis_projection_kleinFourSymmetric (hRH s hs hs_pos hs_lt)

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
