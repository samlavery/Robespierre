import Mathlib

/-!
# Cosh Kernel — Canonical Definitions

Single source of truth for the cosh kernel framework. All other files in
RequestProject should import this file for cosh-related definitions.

## The cosh strip

The cosh kernel is anchored at `x = arcsin(1/2) = π/6`. The cosh strip
extends from `Re(s) = 0` to `Re(s) = π/3`, crossing the Euler product
boundary at `Re(s) = 1` (since `π/3 > 1`).

## Two symmetries

The cosh kernel has two independent, automatic symmetries:

1. **coshReflection** — reflects `Re(s)` about `π/6`, preserving `Im(s)`.
   This is the real-part reflection: `s ↦ ⟨π/3 - Re(s), Im(s)⟩`.
   Derives from the evenness `cosh(z) = cosh(−z)` combined with Schwarz.

2. **coshFolding** — complex conjugation `s ↦ conj(s)`.
   Derives from `cosh` having real Taylor coefficients: `cosh(z̄) = conj(cosh(z))`.

Their composition (in either order) gives `coshRotation`: `s ↦ π/3 - s`
(full complex subtraction), which is the combined symmetry `s ↦ ⟨π/3 - Re(s), -Im(s)⟩`.
-/

open Complex Real Set Filter Topology

noncomputable section

namespace CoshDefs

/-! ## Constants -/

/-- The cosh anchor point: `arcsin(1/2) = π/6`. -/
def coshAnchor : ℝ := Real.pi / 6

/-- `arcsin(1/2) = π/6`. -/
theorem arcsin_half_eq : Real.arcsin (1 / 2) = coshAnchor := by
  unfold coshAnchor
  rw [← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-- `sin(π/6) = 1/2`. -/
theorem sin_coshAnchor : Real.sin coshAnchor = 1 / 2 := Real.sin_pi_div_six

/-- The cosh anchor lies strictly inside the classical critical strip `(0, 1)`. -/
theorem coshAnchor_pos : 0 < coshAnchor := by unfold coshAnchor; positivity

theorem coshAnchor_lt_one : coshAnchor < 1 := by
  unfold coshAnchor
  calc Real.pi / 6 < 4 / 6 := by
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 6)
        linarith [Real.pi_lt_four]
      _ < 1 := by norm_num

/-- The cosh anchor is strictly greater than `1/2`. -/
theorem coshAnchor_gt_half : (1 : ℝ) / 2 < coshAnchor := by
  unfold coshAnchor; linarith [Real.pi_gt_three]

/-- `π/3 > 1`: the cosh strip extends past the Euler product boundary. -/
theorem pi_div_three_gt_one : 1 < Real.pi / 3 := by linarith [Real.pi_gt_three]

/-- `π/3 = 2 * coshAnchor`. -/
theorem pi_div_three_eq : Real.pi / 3 = 2 * coshAnchor := by unfold coshAnchor; ring

/-! ## The two symmetries -/

/-- **Cosh reflection**: reflects `Re(s)` about `π/6`, preserving `Im(s)`.
    The cosh strip `[0, π/3]` maps to itself under this reflection. -/
def coshReflection (s : ℂ) : ℂ := ⟨Real.pi / 3 - s.re, s.im⟩

/-- **Cosh folding**: complex conjugation. Derives from `cosh` having
    real Taylor coefficients. -/
def coshFolding (s : ℂ) : ℂ := starRingEnd ℂ s

/-- **Cosh rotation**: the composition of coshReflection and coshFolding
    (in either order). This is `s ↦ π/3 - s` (full complex subtraction). -/
def coshRotation (s : ℂ) : ℂ := ↑(Real.pi / 3) - s

/-- **Classical reflection**: the functional equation symmetry `s ↦ 1 - s`. -/
def classicalReflection (s : ℂ) : ℂ := 1 - s

/-! ## Composition identities -/

theorem coshRotation_eq_reflection_comp_folding (s : ℂ) :
    coshRotation s = coshReflection (coshFolding s) := by
  simp [coshRotation, coshReflection, coshFolding, Complex.ext_iff,
        sub_re, ofReal_re, sub_im, ofReal_im]

theorem coshRotation_eq_folding_comp_reflection (s : ℂ) :
    coshRotation s = coshFolding (coshReflection s) := by
  simp [coshRotation, coshReflection, coshFolding, Complex.ext_iff,
        sub_re, ofReal_re, sub_im, ofReal_im]

/-! ## Involution properties -/

theorem coshReflection_involutive : Function.Involutive coshReflection := by
  intro s; simp [coshReflection]

theorem coshFolding_involutive : Function.Involutive coshFolding := by
  intro s; simp [coshFolding]

theorem coshRotation_involutive : Function.Involutive coshRotation := by
  intro s; simp [coshRotation, sub_sub_cancel]

theorem classicalReflection_involutive : Function.Involutive classicalReflection := by
  intro s; simp [classicalReflection, sub_sub_cancel]

/-! ## Re/Im behavior -/

theorem coshReflection_re (s : ℂ) : (coshReflection s).re = Real.pi / 3 - s.re := by
  simp [coshReflection]

theorem coshReflection_im (s : ℂ) : (coshReflection s).im = s.im := by
  simp [coshReflection]

theorem coshFolding_re (s : ℂ) : (coshFolding s).re = s.re := by
  simp [coshFolding]

theorem coshFolding_im (s : ℂ) : (coshFolding s).im = -s.im := by
  simp [coshFolding]

theorem coshRotation_re (s : ℂ) : (coshRotation s).re = Real.pi / 3 - s.re := by
  simp [coshRotation, sub_re, ofReal_re]

theorem coshRotation_im (s : ℂ) : (coshRotation s).im = -s.im := by
  simp [coshRotation, sub_im, ofReal_im]

theorem classicalReflection_re (s : ℂ) : (classicalReflection s).re = 1 - s.re := by
  simp [classicalReflection, sub_re, one_re]

theorem classicalReflection_im (s : ℂ) : (classicalReflection s).im = -s.im := by
  simp [classicalReflection, sub_im, one_im]

/-! ## Composition of classical and cosh reflections -/

/-- The composition of coshRotation after classicalReflection is translation
    by `π/3 - 1 > 0`. This is the key offset. -/
theorem coshRotation_comp_classical (s : ℂ) :
    coshRotation (classicalReflection s) = s + ↑(Real.pi / 3 - 1) := by
  simp [coshRotation, classicalReflection]; ring

theorem shift_positive : Real.pi / 3 - 1 > 0 := by linarith [Real.pi_gt_three]

/-! ## Domain definitions -/

/-- The **cosh strip**: `{s : ℂ | 0 < Re(s) < π/3}`. -/
def coshStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3}

/-- The **classical critical strip**: `{s : ℂ | 0 < Re(s) < 1}`. -/
def criticalStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The **critical line**: `{s : ℂ | Re(s) = 1/2}`. -/
def criticalLine : Set ℂ := {s : ℂ | s.re = 1 / 2}

/-- The **overlap region**: `{s : ℂ | 1 < Re(s) < π/3}`.
    This is where the cosh strip overlaps the Euler product half-plane. -/
def overlapRegion : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The critical strip is contained in the cosh strip. -/
theorem criticalStrip_subset_coshStrip : criticalStrip ⊆ coshStrip := by
  intro s ⟨h1, h2⟩; exact ⟨h1, lt_trans h2 pi_div_three_gt_one⟩

/-- The overlap region is contained in the cosh strip. -/
theorem overlapRegion_subset_coshStrip : overlapRegion ⊆ coshStrip := by
  intro s ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- The cosh strip is invariant under coshRotation. -/
theorem coshStrip_coshRotation_invariant :
    ∀ s ∈ coshStrip, coshRotation s ∈ coshStrip := by
  intro s ⟨h1, h2⟩
  refine ⟨?_, ?_⟩ <;> rw [coshRotation_re] <;> linarith

/-! ## Cosh kernel definitions -/

/-- The real cosh kernel centered at `π/6`:
    `K(σ) = cosh(σ - π/6)`. -/
def coshKernelReal (σ : ℝ) : ℝ := Real.cosh (σ - Real.pi / 6)

/-- The complex cosh kernel parameterized by frequency `t`:
    `K_t(s) = cosh(t · (s − π/6))`. -/
def coshKernelComplex (t : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh (↑t * (s - ↑(Real.pi / 6)))

/-- The two-point real cosh kernel:
    `K(x,y) = 1 / cosh((x-y)/2)`. -/
def coshKernelPair (x y : ℝ) : ℝ :=
  1 / Real.cosh ((x - y) / 2)

/-! ## Kernel symmetry at the anchor -/

/-- The real cosh kernel has fold symmetry: `K(π/3 - σ) = K(σ)`. -/
theorem coshKernelReal_fold (σ : ℝ) :
    coshKernelReal (Real.pi / 3 - σ) = coshKernelReal σ := by
  unfold coshKernelReal; rw [← Real.cosh_neg]; ring_nf

/-- The complex cosh kernel is invariant under cosh rotation: `K_t(π/3 - s) = K_t(s)`. -/
theorem coshKernelComplex_rotation (t : ℝ) (s : ℂ) :
    coshKernelComplex t (coshRotation s) = coshKernelComplex t s := by
  simp only [coshKernelComplex, coshRotation]
  have : ↑t * (↑(Real.pi / 3 : ℝ) - s - ↑(Real.pi / 6 : ℝ)) =
         -(↑t * (s - ↑(Real.pi / 6 : ℝ))) := by push_cast; ring
  rw [this, Complex.cosh_neg]

/-- The real cosh kernel is strictly positive. -/
theorem coshKernelReal_pos (σ : ℝ) : 0 < coshKernelReal σ := Real.cosh_pos _

/-- The real cosh kernel at the anchor equals 1. -/
theorem coshKernelReal_at_anchor : coshKernelReal coshAnchor = 1 := by
  simp [coshKernelReal, coshAnchor]

end CoshDefs
end
