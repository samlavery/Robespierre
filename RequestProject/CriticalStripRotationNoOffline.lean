/-
# Isometric Equivalence of Rotated Critical Strips
We prove unconditionally, from first principles, that:
1. **Rotation by 90°** (multiplication by `I` in `ℂ`) is an isometry of `ℂ`.
2. This rotation maps the **vertical critical strip** `{0 < Re(s) < 1}` to the
   **horizontal strip** `{0 < Im(s) < 1}`, and the critical line `Re(s) = 1/2`
   to `Im(s) = 1/2`.
3. The two "number lines" (vertical critical line and horizontal critical line)
   are **isometric to ℝ** and **to each other**.
4. Isometries **preserve zero sets**: zeros on the critical line map bijectively
   to zeros on the rotated line, with all inter-zero distances preserved.
   In particular, an isometric rotation cannot create, destroy, or move zeros.
5. The **Euler product** for `ζ(s)` converges unconditionally for `Re(s) > 1`,
   and the **Dirichlet series** is summable there. The convergence region in
   rotated coordinates is the exact isometric image of the original.
**All proofs are unconditional** — no assumption of RH or any conjecture is used.
Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` appear.
-/
import Mathlib
open Complex Function Set
namespace CriticalStripRotation
/-! ## Section 1: Rotation by 90° is an isometry -/
/-- Multiplication by `I` (rotation by `π/2`) is an isometry of `ℂ`. -/
theorem rotation90_isometry : Isometry (fun z : ℂ => I * z) := by
  rw [isometry_iff_dist_eq]
  norm_num [dist_eq_norm, Complex.normSq, Complex.norm_def]
  exact fun x y => congr_arg Real.sqrt (by ring)
/-- Rotation by 90° preserves distances between any two points. -/
theorem rotation90_dist_eq (z w : ℂ) : dist (I * z) (I * w) = dist z w :=
  rotation90_isometry.dist_eq z w
/-! ## Section 2: Rotation maps the critical strip to the horizontal strip -/
/-- Rotation maps the critical strip `{0 < Re(s) < 1}` bijectively
    to the horizontal strip `{0 < Im(s) < 1}`. -/
theorem rotation_strip_iff (s : ℂ) :
    (0 < s.re ∧ s.re < 1) ↔ (0 < (I * s).im ∧ (I * s).im < 1) := by
  aesop
/-- The real part of `s` equals the imaginary part of `I * s`. -/
theorem rotation_re_to_im (s : ℂ) : s.re = (I * s).im := by
  simp +zetaDelta
/-- The imaginary part of `s` equals minus the real part of `I * s`. -/
theorem rotation_im_to_re (s : ℂ) : s.im = -(I * s).re := by
  simp +zetaDelta
/-! ## Section 3: The two number lines are isometric to ℝ and to each other -/
/-- The vertical critical line embedding: `t ↦ 1/2 + ti`.
    This parameterizes `Re(s) = 1/2`. -/
noncomputable def verticalLine (t : ℝ) : ℂ := 1/2 + ↑t * I
/-- The horizontal critical line embedding: `t ↦ t + i/2`.
    This parameterizes `Im(s) = 1/2`. -/
noncomputable def horizontalLine (t : ℝ) : ℂ := ↑t + I / 2
/-- The vertical line embedding is an isometry from `ℝ` to `ℂ`. -/
theorem verticalLine_isometry : Isometry verticalLine := by
  refine Isometry.of_dist_eq fun x y => ?_
  unfold verticalLine; norm_num [Complex.dist_eq, Complex.normSq]; ring;
  norm_num [Complex.normSq, Complex.norm_def, dist_eq_norm]; ring;
  rw [← Real.sqrt_sq_eq_abs]; ring
/-- The horizontal line embedding is an isometry from `ℝ` to `ℂ`. -/
theorem horizontalLine_isometry : Isometry horizontalLine := by
  refine Isometry.of_dist_eq fun x y => ?_
  unfold horizontalLine
  norm_num [Complex.dist_eq, Complex.normSq]
  norm_cast
/-- Rotation maps the vertical critical line to the horizontal critical line:
    `I * (1/2 + ti) = -t + i/2`. -/
theorem rotation_maps_verticalLine (t : ℝ) :
    I * verticalLine t = horizontalLine (-t) := by
  unfold verticalLine horizontalLine; ring; norm_num
/-- Points on the vertical line have `Re = 1/2`. -/
theorem verticalLine_re (t : ℝ) : (verticalLine t).re = 1/2 := by
  unfold verticalLine; norm_num
/-- Points on the horizontal line have `Im = 1/2`. -/
theorem horizontalLine_im (t : ℝ) : (horizontalLine t).im = 1/2 := by
  unfold horizontalLine; norm_num
/-- Rotation maps `Re(s) = 1/2` to `Im(I·s) = 1/2`. -/
theorem rotation_critical_line (s : ℂ) (h : s.re = 1/2) :
    (I * s).im = 1/2 := by
  norm_num [h, Complex.ext_iff]
/-! ## Section 4: Isometries preserve zero sets — zeros do not change -/
/-- For **any** function `f : ℂ → ℂ`, the zero set is preserved pointwise by
    composition with an inverse. This is the core reason isometric rotations
    cannot force zeros to appear or disappear. -/
theorem zero_set_of_composition (f : ℂ → ℂ) (φ : ℂ ≃ ℂ) (z : ℂ) :
    f z = 0 ↔ (f ∘ φ.symm) (φ z) = 0 := by
  simp +zetaDelta
/-- If all zeros of `f` lie in a set `S`, then all zeros of `f ∘ φ⁻¹` lie in `φ '' S`. -/
theorem zero_set_image (f : ℂ → ℂ) (φ : ℂ ≃ ℂ) (S : Set ℂ) :
    (∀ z, f z = 0 → z ∈ S) → (∀ w, (f ∘ φ.symm) w = 0 → w ∈ φ '' S) := by
  aesop
/-- If `φ` is an isometry, then distances between image points equal distances
    between original points. Applied to zeros, this means the metric structure
    of the zero set is exactly preserved. -/
theorem isometry_preserves_zero_distances (f : ℂ → ℂ) (φ : ℂ → ℂ)
    (hφ : Isometry φ) (z₁ z₂ : ℂ)
    (_hf₁ : f z₁ = 0) (_hf₂ : f z₂ = 0) :
    dist (φ z₁) (φ z₂) = dist z₁ z₂ :=
  hφ.dist_eq _ _
/-- Rotation by 90° and its inverse (`-I · _`) compose to the identity.
    In particular, zeros on the critical line `Re = 1/2` map bijectively
    to zeros on `Im = 1/2`, and vice versa, with **no zeros created or destroyed**. -/
theorem rotation_preserves_zero_structure (f : ℂ → ℂ) (z : ℂ) :
    f z = 0 ↔ f ((-I) * (I * z)) = 0 := by
  norm_num [← mul_assoc]
/-! ## Section 5: Unconditional Euler product and Dirichlet series convergence -/
/-- The Euler product for `ζ(s)` converges unconditionally for `Re(s) > 1`.
    This is a **theorem**, not a conjecture — it requires no hypothesis about RH. -/
theorem euler_product_converges (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (↑(p : ℕ) : ℂ) ^ (-s))⁻¹)
      (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs
/-- The Dirichlet series `Σ 1/n^s` is summable for `Re(s) > 1` — unconditionally. -/
theorem dirichlet_series_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable 1 s := by
  have := @LSeriesSummable_one_iff
  aesop
/-- The Euler product converges to the same value `ζ(s)` regardless of
    perspective. For any `s` with `Re(s) > 1`, the Euler product equals `ζ(s)`. -/
theorem euler_product_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' (p : Nat.Primes), (1 - (↑(p : ℕ) : ℂ) ^ (-s))⁻¹ :=
  (riemannZeta_eulerProduct_tprod hs).symm
/-! ## Section 6: Non-divergence — the two strips give equivalent convergence -/
/-- In rotated coordinates (`w ↦ (-I) · w`), the real part becomes the
    imaginary part: `Re((-I) · w) = Im(w)`. -/
theorem rotated_convergence_equiv (w : ℂ) :
    ((-I) * w).re = w.im := by
  simp
/-- The Dirichlet series for `ζ` converges when `Im(w) > 1` in the rotated
    coordinate system, which is the **exact rotation** of `Re(s) > 1`.
    The convergence regions are isometric images of each other. -/
theorem convergence_region_rotation (w : ℂ) :
    1 < ((-I) * w).re ↔ 1 < w.im := by
  simp +decide
end CriticalStripRotation