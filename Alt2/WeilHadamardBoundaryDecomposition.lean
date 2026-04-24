import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilHadamardRectangleResidueSum

/-!
# Boundary decomposition for the Hadamard-kernel rectangle contour

This file rewrites the zero-free Hadamard rectangle contour into the explicit
boundary terms needed for the eventual `T → ∞` passage:

* the right edge is rewritten using the absolutely convergent Dirichlet series
  for `-ζ'/ζ` on `Re s > 1`;
* the left edge is rewritten using the functional-equation arch decomposition.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- The arch-side factor in the functional-equation decomposition of
`-ζ'/ζ(z)`. -/
def hadamardArchBoundaryTerm (z : ℂ) : ℂ :=
  deriv Complex.Gammaℝ z / z.Gammaℝ +
    deriv Complex.Gammaℝ (1 - z) / (1 - z).Gammaℝ +
    deriv riemannZeta (1 - z) / riemannZeta (1 - z)

private theorem weilIntegrand_hadamardKernel_eq_archBoundaryTerm_of_gamma_nonzero
    {s z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0) (hζ1z : riemannZeta (1 - z) ≠ 0)
    (hΓz : z.Gammaℝ ≠ 0) (hΓ1z : (1 - z).Gammaℝ ≠ 0) :
    weilIntegrand (hadamardKernel s) z = hadamardArchBoundaryTerm z * hadamardKernel s z := by
  simpa [hadamardArchBoundaryTerm] using
    (weilIntegrand_arch_decomposition (h := hadamardKernel s) hz0 hz1 hζz hζ1z hΓz hΓ1z)

private theorem weilIntegrand_hadamardKernel_eq_archBoundaryTerm
    {s z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0) (hζ1z : riemannZeta (1 - z) ≠ 0)
    (hz_re_pos : 0 < z.re) (h1z_re_pos : 0 < (1 - z).re) :
    weilIntegrand (hadamardKernel s) z = hadamardArchBoundaryTerm z * hadamardKernel s z := by
  have hΓz : z.Gammaℝ ≠ 0 := gammaℝ_ne_zero_of_re_pos hz_re_pos
  have hΓ1z : (1 - z).Gammaℝ ≠ 0 := gammaℝ_ne_zero_of_re_pos h1z_re_pos
  exact weilIntegrand_hadamardKernel_eq_archBoundaryTerm_of_gamma_nonzero
    hz0 hz1 hζz hζ1z hΓz hΓ1z

private lemma gammaR_ne_zero_neg_one_line (y : ℝ) :
    ((((-1 : ℝ) : ℂ) + (y : ℂ) * I)).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : ((((-1 : ℝ) : ℂ) + (y : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [hn]
  simp at hre
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
  omega

/-- On a zero-free rectangle, the Hadamard-kernel contour integral can be
rewritten with the right edge in prime-side form and the left edge in arch-side
form. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_zero_free
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0)
    (hζ_reflect_left :
      ∀ y ∈ Set.uIcc (-T) T,
        riemannZeta (((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      (((∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((σR : ℂ) + (y : ℂ) * I) *
                  hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((σL : ℂ) + (y : ℂ) * I) *
              hadamardKernel s ((σL : ℂ) + (y : ℂ) * I)) := by
  unfold rectContourIntegral
  have hσR_gt_one : 1 < σR := by simpa using h_one_re.2
  have hright :
      (∫ y : ℝ in (-T : ℝ)..T, weilIntegrand (hadamardKernel s) ((σR : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((σR : ℂ) + (y : ℂ) * I) *
            hadamardKernel s ((σR : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have h_re : 1 < (((σR : ℂ) + (y : ℂ) * I).re) := by simpa using hσR_gt_one
    simpa using
      (weilIntegrand_eq_vonMangoldt_LSeries
        (h := hadamardKernel s) (s := ((σR : ℂ) + (y : ℂ) * I)) h_re)
  have hleft :
      (∫ y : ℝ in (-T : ℝ)..T, weilIntegrand (hadamardKernel s) ((σL : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          hadamardArchBoundaryTerm ((σL : ℂ) + (y : ℂ) * I) *
            hadamardKernel s ((σL : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    let z : ℂ := (σL : ℂ) + (y : ℂ) * I
    have hz_mem : z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
      constructor
      · simpa [z, hσ.le]
      · simpa [z] using hy
    have hz0 : z ≠ 0 := by
      have hz_re_pos : 0 < z.re := by simpa [z] using hσL
      intro hz0
      rw [hz0] at hz_re_pos
      simp at hz_re_pos
    have hz1 : z ≠ 1 := by
      intro hz1
      have hre : (σL : ℝ) = 1 := by simpa [z] using congrArg Complex.re hz1
      have hσL_lt_one : σL < (1 : ℝ) := by simpa using h_one_re.1
      linarith
    have hζz : riemannZeta z ≠ 0 := hζ_ne_rect z hz_mem hz1
    have hζ1z : riemannZeta (1 - z) ≠ 0 := by
      have h1z_eq : 1 - z = (((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        simp [z]
        ring
      rw [h1z_eq]
      exact hζ_reflect_left y hy
    have hz_re_pos : 0 < z.re := by simpa [z] using hσL
    have h1z_re_pos : 0 < (1 - z).re := by
      have hσL_lt_one : σL < (1 : ℝ) := by simpa using h_one_re.1
      simpa [z] using sub_pos.mpr hσL_lt_one
    simpa [z] using
      (weilIntegrand_hadamardKernel_eq_archBoundaryTerm
        (s := s) (z := z) hz0 hz1 hζz hζ1z hz_re_pos h1z_re_pos)
  rw [hright, hleft]

/-- Explicit zero-free boundary identity: the residue-side expression for the
Hadamard kernel equals the boundary decomposition with prime-side right edge and
arch-side left edge. -/
theorem hadamard_zero_free_rectangle_explicit_boundary_identity
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0)
    (hζ_reflect_left :
      ∀ y ∈ Set.uIcc (-T) T,
        riemannZeta (((1 - σL : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) ≠ 0) :
    2 * ↑Real.pi * I * (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) =
      (((∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((σR : ℂ) + (y : ℂ) * I) *
                  hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((σL : ℂ) + (y : ℂ) * I) *
              hadamardKernel s ((σL : ℂ) + (y : ℂ) * I)) := by
  calc
    2 * ↑Real.pi * I * (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) =
        rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) := by
          symm
          exact rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_zero_free_explicit
            hs0 hs1 hsζ hσ hT hσL h_one_re hs_re hs_im hζ_ne_rect
    _ =
        (((∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
                (∫ x : ℝ in σL..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
              I •
                (∫ y : ℝ in (-T : ℝ)..T,
                  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                      ((σR : ℂ) + (y : ℂ) * I) *
                    hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
          I •
            (∫ y : ℝ in (-T : ℝ)..T,
              hadamardArchBoundaryTerm ((σL : ℂ) + (y : ℂ) * I) *
                hadamardKernel s ((σL : ℂ) + (y : ℂ) * I)) := by
            exact rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_zero_free
              hs0 hs1 hsζ hσ hT hσL h_one_re hs_re hs_im hζ_ne_rect hζ_reflect_left

/-- Boundary decomposition for the Hadamard-kernel rectangle with left edge
fixed at `Re z = -1`, so the rectangle contains the origin pole. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_with_origin_neg_one
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σR T : ℝ} (hσR : 1 < σR) (hT : 0 < T)
    (hs_re : (-1 : ℝ) < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc (-1 : ℝ) σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    rectContourIntegral (-1 : ℝ) σR T (weilIntegrand (hadamardKernel s)) =
      (((∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((σR : ℂ) + (y : ℂ) * I) *
                  hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
              hadamardKernel s ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  unfold rectContourIntegral
  have hright :
      (∫ y : ℝ in (-T : ℝ)..T, weilIntegrand (hadamardKernel s) ((σR : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((σR : ℂ) + (y : ℂ) * I) *
            hadamardKernel s ((σR : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have h_re : 1 < (((σR : ℂ) + (y : ℂ) * I).re) := by simpa using hσR
    simpa using
      (weilIntegrand_eq_vonMangoldt_LSeries
        (h := hadamardKernel s) (s := ((σR : ℂ) + (y : ℂ) * I)) h_re)
  have hleft :
      (∫ y : ℝ in (-T : ℝ)..T, weilIntegrand (hadamardKernel s) ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
            hadamardKernel s ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    let z : ℂ := (((-1 : ℝ) : ℂ)) + (y : ℂ) * I
    have hz_mem : z ∈ (Set.uIcc (-1 : ℝ) σR ×ℂ Set.uIcc (-T) T) := by
      constructor
      · simpa [z, le_of_lt hσR]
      · simpa [z] using hy
    have hz0 : z ≠ 0 := by
      intro hz0
      have hre : ((-1 : ℝ) : ℂ).re = (0 : ℂ).re := by simpa [z] using congrArg Complex.re hz0
      norm_num at hre
    have hz1 : z ≠ 1 := by
      intro hz1
      have hre : (((-1 : ℝ) : ℂ)).re = (1 : ℂ).re := by simpa [z] using congrArg Complex.re hz1
      norm_num at hre
    have hζz : riemannZeta z ≠ 0 := hζ_ne_rect z hz_mem hz1
    have hζ1z : riemannZeta (1 - z) ≠ 0 := by
      have h1z_re : 1 < (1 - z).re := by
        simp [z]
      exact zeta_ne_zero_of_one_lt_re h1z_re
    have hΓz : z.Gammaℝ ≠ 0 := by
      simpa [z] using gammaR_ne_zero_neg_one_line y
    have hΓ1z : (1 - z).Gammaℝ ≠ 0 := by
      have h1z_re_pos : 0 < (1 - z).re := by
        have h1z_re : 1 < (1 - z).re := by simp [z]
        linarith
      exact gammaℝ_ne_zero_of_re_pos h1z_re_pos
    simpa [z] using
      (weilIntegrand_hadamardKernel_eq_archBoundaryTerm_of_gamma_nonzero
        (s := s) (z := z) hz0 hz1 hζz hζ1z hΓz hΓ1z)
  rw [hright, hleft]

/-- Explicit boundary identity for the Hadamard-kernel rectangle with left edge
at `Re z = -1`, so the residue side includes the origin pole. -/
theorem hadamard_rectangle_with_origin_explicit_boundary_identity_neg_one
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σR T : ℝ} (hσR : 1 < σR) (hT : 0 < T)
    (hs_re : (-1 : ℝ) < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc (-1 : ℝ) σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    2 * ↑Real.pi * I *
        (hadamardOriginCoeff + deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) =
      (((∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((σR : ℂ) + (y : ℂ) * I) *
                  hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
              hadamardKernel s ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  have hσ : (-1 : ℝ) < σR := lt_trans (by norm_num) hσR
  have h_zero_re : (-1 : ℝ) < (0 : ℂ).re ∧ (0 : ℂ).re < σR := by
    constructor
    · norm_num
    · exact lt_trans (by norm_num) hσR
  have h_one_re : (-1 : ℝ) < 1 ∧ (1 : ℂ).re < σR := by
    constructor
    · norm_num
    · simpa using hσR
  calc
    2 * ↑Real.pi * I *
        (hadamardOriginCoeff + deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) =
        rectContourIntegral (-1 : ℝ) σR T (weilIntegrand (hadamardKernel s)) := by
          symm
          exact rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_zero_free_explicit
            hs0 hs1 hsζ hσ hT h_zero_re h_one_re hs_re hs_im hζ_ne_rect
    _ =
        (((∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (-T : ℝ) * I)) -
                (∫ x : ℝ in (-1 : ℝ)..σR, weilIntegrand (hadamardKernel s) ((x : ℂ) + (T : ℝ) * I))) +
              I •
                (∫ y : ℝ in (-T : ℝ)..T,
                  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                      ((σR : ℂ) + (y : ℂ) * I) *
                    hadamardKernel s ((σR : ℂ) + (y : ℂ) * I))) -
          I •
            (∫ y : ℝ in (-T : ℝ)..T,
              hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
                hadamardKernel s ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
            exact rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_with_origin_neg_one
              hs0 hs1 hsζ hσR hT hs_re hs_im hζ_ne_rect

end Contour
end WeilPositivity
end ZD

end
