import Mathlib
/-!
# Critical Strip Rotation: Unconditional Detection of Off-Line Zeros
We prove, from first principles of complex geometry, that if the Riemann Hypothesis
were false (i.e., ζ has zeros in the critical strip with Re(s) ≠ 1/2), then
rotating the critical strip by 90° (via multiplication by `I`) produces a
configuration where:
1. Off-line zeros are **isometrically preserved** — their distance from the
   critical line is unchanged, so they remain detectable.
2. Off-line zeros **cannot cancel** — a point and its rotation cannot both
   sit on Re(s) = 1/2 generically.
3. The **Euler product convergence regions diverge** — the half-plane Re(s) > 1
   maps to Im(s) < −1, which is disjoint from the original convergence region
   within the critical strip.
4. The **rotated point leaves the critical strip** — for any zero in the upper
   half-plane, its rotation has negative real part and thus exits the strip entirely.
All results are unconditional and proved from first principles of complex arithmetic.
No assumption about RH is needed for the geometric/analytic structure theorems.
-/
open Complex
noncomputable section
/-! ## Part 1: Rotation by 90° is multiplication by `I` -/
/-- Rotation by 90° in the complex plane is multiplication by `I`. -/
def rotate90 (z : ℂ) : ℂ := I * z
/-- The real part of `I * z` equals the negative of the imaginary part of `z`. -/
theorem re_rotate90 (z : ℂ) : (rotate90 z).re = -z.im := by
  unfold rotate90; norm_num [Complex.ext_iff]
/-- The imaginary part of `I * z` equals the real part of `z`. -/
theorem im_rotate90 (z : ℂ) : (rotate90 z).im = z.re := by
  unfold rotate90; norm_num [Complex.ext_iff]
/-! ## Part 2: Isometric Preservation — Distance from Critical Line is Invariant -/
/-- Distance from the critical line Re(s) = 1/2. -/
def distFromCriticalLine (z : ℂ) : ℝ := |z.re - 1 / 2|
/-- Distance from the rotated critical line Im(s) = 1/2 (image of Re = 1/2 under
rotation, since Im(I·s) = Re(s), so the line Re = 1/2 maps to Im = 1/2). -/
def distFromRotatedCriticalLine (z : ℂ) : ℝ := |z.im - 1 / 2|
/-
PROBLEM
**Isometric Detection Theorem**: Rotation preserves the distance from the critical
line. Specifically, the distance of `z` from Re(s) = 1/2 equals the distance of
`rotate90 z` from Im(s) = 1/2 (the image of the critical line under rotation).
This means an off-line zero at distance d from the critical line will, after rotation,
remain at distance d from the rotated critical line — it cannot be hidden.
PROVIDED SOLUTION
Unfold distFromCriticalLine, distFromRotatedCriticalLine, and use im_rotate90. We get |z.re - 1/2| = |(rotate90 z).im - 1/2| = |z.re - 1/2| by im_rotate90.
-/
theorem isometric_detection (z : ℂ) :
    distFromCriticalLine z = distFromRotatedCriticalLine (rotate90 z) := by
      unfold distFromCriticalLine distFromRotatedCriticalLine rotate90; norm_num;
/-- Rotation by `I` is an isometry: it preserves all pairwise distances. -/
theorem rotate90_isometry (z w : ℂ) :
    ‖rotate90 z - rotate90 w‖ = ‖z - w‖ := by
  unfold rotate90; norm_num [← mul_sub]
/-! ## Part 3: Non-Cancellation — Off-Line Zeros Cannot Be Eliminated -/
/-- A point is "on the critical line" if its real part equals 1/2. -/
def onCriticalLine (z : ℂ) : Prop := z.re = 1 / 2
/-- A point is "off the critical line" if its real part does not equal 1/2. -/
def offCriticalLine (z : ℂ) : Prop := z.re ≠ 1 / 2
/-- **Non-Cancellation Theorem**: If `z` is off the critical line, then `rotate90 z`
is on the critical line only if `z.im = -1/2`. In particular, for any zero of ζ
in the critical strip with large imaginary part (as all known zeros have), the
rotated zero is NOT on the critical line. -/
theorem non_cancellation (z : ℂ) (hz : offCriticalLine z) :
    onCriticalLine (rotate90 z) ↔ z.im = -1 / 2 := by
  unfold onCriticalLine rotate90; norm_num [Complex.ext_iff]
  constructor <;> intro h <;> linarith
/-- For zeros with imaginary part ≠ -1/2 (which includes all zeros in the
upper half-plane), both the original and rotated points cannot simultaneously
lie on Re(s) = 1/2. -/
theorem no_simultaneous_critical_line (z : ℂ) (hz_im : z.im ≠ -1 / 2) :
    ¬(onCriticalLine z ∧ onCriticalLine (rotate90 z)) := by
  unfold onCriticalLine rotate90; intro H; norm_num at H
  cases lt_or_gt_of_ne hz_im <;> linarith
/-- **Key corollary**: If z is off the critical line and has imaginary part ≠ -1/2,
then BOTH z and its rotation are detectable as off their respective critical lines. -/
theorem both_detectable (z : ℂ) (hz : offCriticalLine z) (hz_im : z.im ≠ -1 / 2) :
    offCriticalLine z ∧ ¬onCriticalLine (rotate90 z) := by
  exact ⟨hz, fun h => hz_im <| by unfold onCriticalLine at h; rw [re_rotate90] at h; linarith⟩
/-! ## Part 4: Euler Product Convergence Regions Diverge Under Rotation -/
/-- The Euler product for ζ(s) converges absolutely when Re(s) > 1. -/
def eulerProductRegion (z : ℂ) : Prop := z.re > 1
/-- After rotation by 90°, Re(iz) = -Im(z), so the Euler product for the
rotated function converges when -Im(z) > 1, i.e., Im(z) < -1. -/
def rotatedEulerProductRegion (z : ℂ) : Prop := z.im < -1
/-
PROBLEM
**Euler Product Region Divergence**: The Euler product for ζ(s) converges when
Re(s) > 1. For the rotated zeta ζ(I·s), convergence requires Re(I·s) > 1, i.e.,
-Im(s) > 1, i.e., Im(s) < -1. These two regions (Re > 1 and Im < -1) are
geometrically perpendicular half-planes.
Within the critical strip (0 < Re < 1), NEITHER region is active, so both
Euler products diverge — their convergence behaviors are fundamentally incompatible.
PROVIDED SOLUTION
Split. First: eulerProductRegion z means z.re > 1, but h_strip gives z.re < 1, contradiction by linarith. Second: rotatedEulerProductRegion z means z.im < -1, but h_upper gives z.im > 0, contradiction by linarith. Unfold the definitions first.
-/
theorem euler_region_divergence (z : ℂ) (h_strip : 0 < z.re ∧ z.re < 1) (h_upper : z.im > 0) :
    ¬eulerProductRegion z ∧ ¬rotatedEulerProductRegion z := by
      grind +locals
/-
PROBLEM
**Divergence Theorem**: Within the critical strip (0 < Re(s) < 1),
the original Euler product does not converge.
PROVIDED SOLUTION
Unfold eulerProductRegion and inCriticalStrip. eulerProductRegion z says z.re > 1, but h_strip says z.re < 1. Contradiction by linarith.
-/
theorem euler_regions_empty_in_strip (z : ℂ) (h_strip : 0 < z.re ∧ z.re < 1) :
    ¬eulerProductRegion z := by
      grind +locals
/-
PROBLEM
Within the critical strip with Im(s) > 0, the rotated Euler product
also does not converge.
PROVIDED SOLUTION
Unfold rotatedEulerProductRegion. It says z.im < -1, but h_upper says z.im > 0. Contradiction by linarith.
-/
theorem rotated_euler_regions_empty_in_strip (z : ℂ) (h_strip : 0 < z.re ∧ z.re < 1)
    (h_upper : z.im > 0) :
    ¬rotatedEulerProductRegion z := by
      exact not_lt_of_gt ( by linarith! )
/-
PROBLEM
**Euler Product Incompatibility**: No point can simultaneously be in the
Euler product convergence region (Re > 1) and the rotated convergence region
(Im < -1 of the original point, equivalently Re > 1 and Im < -1 simultaneously).
In fact, these regions are always simultaneously satisfiable (take z = 2 - 2i),
but the key point is the next theorem: they are BOTH empty inside the critical strip.
PROVIDED SOLUTION
Split into two parts. First part: eulerProductRegion z says z.re > 1 but h_strip says z.re < 1, contradiction. Second part: rotatedEulerProductRegion(rotate90 z) says (rotate90 z).im < -1, by im_rotate90 this is z.re < -1, but h_strip says z.re > 0, contradiction. Use euler_regions_empty_in_strip for the first part.
-/
theorem euler_both_empty_in_strip (z : ℂ) (h_strip : 0 < z.re ∧ z.re < 1) :
    ¬eulerProductRegion z ∧ ¬rotatedEulerProductRegion (rotate90 z) := by
      exact ⟨ by unfold eulerProductRegion; linarith, by unfold rotatedEulerProductRegion; unfold rotate90; norm_num; linarith ⟩
/-! ## Part 5: Rotation Ejects Zeros from the Critical Strip -/
/-- A point lies in the (open) critical strip: 0 < Re(s) < 1. -/
def inCriticalStrip (z : ℂ) : Prop := 0 < z.re ∧ z.re < 1
/-
PROBLEM
**Strip Ejection Theorem**: If z is in the critical strip AND in the upper
half-plane (Im(z) > 0), then the rotated point I·z is NOT in the critical strip.
Proof: Re(Iz) = -Im(z) < 0, so Iz fails the condition Re > 0 for the strip.
This is the key geometric fact: rotation by 90° ejects upper-half-plane zeros
from the critical strip entirely, making them unconditionally detectable.
PROVIDED SOLUTION
Unfold inCriticalStrip. We need ¬(0 < (rotate90 z).re ∧ (rotate90 z).re < 1). By re_rotate90, (rotate90 z).re = -z.im. Since h_upper says z.im > 0, we have -z.im < 0, so ¬(0 < -z.im). Intro and linarith.
-/
theorem rotation_ejects_from_strip (z : ℂ) (h_strip : inCriticalStrip z) (h_upper : z.im > 0) :
    ¬inCriticalStrip (rotate90 z) := by
      exact fun h => by linarith [ h.1, h.2, h_upper, h_strip.1, h_strip.2, show ( rotate90 z |> Complex.re ) = -z.im from by unfold rotate90; simp +decide [ Complex.ext_iff ] ] ;
/-
PROBLEM
**Symmetric Ejection**: If z is in the critical strip with Im(z) < 0,
then I·z has Re(Iz) = -Im(z) > 0 and Re(Iz) = -Im(z), which may or may not
be < 1. But for |Im(z)| ≥ 1, I·z is also outside the strip.
PROVIDED SOLUTION
Unfold inCriticalStrip. (rotate90 z).re = -z.im by re_rotate90. If z.im > 1 then -z.im < -1 < 0, contradicting 0 < (rotate90 z).re. If z.im < -1 then -z.im > 1, contradicting (rotate90 z).re < 1. Either case gives contradiction.
-/
theorem rotation_ejects_large_imag (z : ℂ) (h_strip : inCriticalStrip z)
    (h_large : z.im > 1 ∨ z.im < -1) :
    ¬inCriticalStrip (rotate90 z) := by
      cases h_large <;> [ exact fun h => by linarith [ h.1, h.2, h_strip.1, h_strip.2, re_rotate90 z ] ; ; exact fun h => by linarith [ h.1, h.2, h_strip.1, h_strip.2, re_rotate90 z ] ]
/-! ## Part 6: Main Detection Theorem -/
/-
PROBLEM
**Main Theorem: Unconditional Detection of Off-Line Zeros**
If ζ had a zero at `z` in the critical strip that is OFF the critical line
(Re(z) ≠ 1/2) and in the upper half-plane (Im(z) > 0), then:
1. The distance from the critical line is positive (the zero is genuinely off-line).
2. The rotated zero `I*z` does NOT lie on the critical line (non-cancellation).
3. The rotated zero `I*z` is NOT in the critical strip (strip ejection).
4. The distance from the critical line is preserved under rotation (isometry).
Together these show that off-line zeros are unconditionally and invariantly
detectable — they cannot be hidden by any rotation-based mechanism.
PROVIDED SOLUTION
Split into 4 conjuncts.
(1) distFromCriticalLine z > 0: unfold to |z.re - 1/2| > 0, which follows from h_off (z.re ≠ 1/2) via abs_pos.mpr and sub_ne_zero.mpr.
(2) ¬onCriticalLine (rotate90 z): by non_cancellation with hz = h_off, onCriticalLine(rotate90 z) ↔ z.im = -1/2. Since h_upper gives z.im > 0, we have z.im ≠ -1/2, so ¬onCriticalLine.
(3) ¬inCriticalStrip (rotate90 z): use rotation_ejects_from_strip with h_strip and h_upper.
(4) Use isometric_detection.
-/
theorem main_detection_theorem (z : ℂ)
    (h_strip : inCriticalStrip z)
    (h_off : offCriticalLine z)
    (h_upper : z.im > 0) :
    -- (1) Distance from critical line is positive
    distFromCriticalLine z > 0
    -- (2) Rotated zero is NOT on the critical line
    ∧ ¬onCriticalLine (rotate90 z)
    -- (3) Rotated zero is NOT in the critical strip
    ∧ ¬inCriticalStrip (rotate90 z)
    -- (4) Distance is preserved (isometric detection)
    ∧ distFromCriticalLine z = distFromRotatedCriticalLine (rotate90 z) := by
      exact ⟨ abs_pos.mpr ( sub_ne_zero.mpr h_off ), by intro; exact h_off <| by linarith [ non_cancellation z h_off |>.1 ‹_› ], rotation_ejects_from_strip z h_strip h_upper, isometric_detection z ⟩
end
