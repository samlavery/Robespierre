import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilHadamardBoundaryDecomposition
import RequestProject.ZetaBound

/-!
# Boundary decomposition for the `pairTestMellin β` rectangle contour

This file ports the Hadamard rectangle-Cauchy boundary-form template
(`rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_with_origin_neg_one`
in `WeilHadamardBoundaryDecomposition.lean`) to the cosh-pair Gauss test
`pairTestMellin β` on the rectangle `[-1, 2] × [-T, T]`.

The right edge (`Re s = 2`) is rewritten via the von Mangoldt L-series form of
`weilIntegrand`. The left edge (`Re s = -1`) is rewritten via the
functional-equation arch decomposition. Both pieces are h-generic in the
Mellin factor, so the proof exactly mirrors the Hadamard version with
`hadamardKernel s ↦ pairTestMellin β` and `σR := 2`.

The non-vanishing of `ζ` on the rectangle interior is required as a hypothesis
(`hζ_ne_rect`) just as in the Hadamard analogue: `riemannZeta(-1 + iy) ≠ 0`
is not provable unconditionally for all `y ∈ [-T, T]`. The downstream consumer
in `WeilFinalAssemblyUnconditional.lean` already supplies this via `goodHeight T`
together with the rectangle zero-set hypotheses fed through
`archIntegrand_interval_eq_left_edge_integral_target`.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- Boundary decomposition for the `pairTestMellin β` rectangle with left edge
fixed at `Re z = -1` and right edge at `Re z = 2`, so the rectangle contains
the origin and the trivial pole at `s = 1`.

This is a direct port of
`rectContourIntegral_weilIntegrand_hadamardKernel_eq_boundary_forms_with_origin_neg_one`
from `WeilHadamardBoundaryDecomposition.lean` with `hadamardKernel s` replaced
by `pairTestMellin β`. The proof is identical because both
`weilIntegrand_eq_vonMangoldt_LSeries` (right edge) and
`weilIntegrand_arch_decomposition` (left edge) are generic in the Mellin
factor `h`. -/
theorem rectContourIntegral_weilIntegrand_pairTestMellin_eq_boundary_forms_with_origin_neg_one
    (β : ℝ) {T : ℝ} (_hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand (pairTestMellin β)) =
      (((∫ x : ℝ in (-1 : ℝ)..2, weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
              (∫ x : ℝ in (-1 : ℝ)..2, weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((2 : ℂ) + (y : ℂ) * I) *
                  pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
              pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  unfold rectContourIntegral
  have hσR : (1 : ℝ) < 2 := by norm_num
  -- Right edge: rewrite via the absolutely convergent Dirichlet series for
  -- `-ζ'/ζ` on `Re s > 1`.
  have hright :
      (∫ y : ℝ in (-T : ℝ)..T, weilIntegrand (pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((2 : ℂ) + (y : ℂ) * I) *
            pairTestMellin β ((2 : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    have h_re : 1 < (((2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
    simpa using
      (weilIntegrand_eq_vonMangoldt_LSeries
        (h := pairTestMellin β) (s := (((2 : ℝ) : ℂ) + (y : ℂ) * I)) h_re)
  -- Left edge: rewrite via the functional-equation arch decomposition.
  have hleft :
      (∫ y : ℝ in (-T : ℝ)..T,
          weilIntegrand (pairTestMellin β) ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
        ∫ y : ℝ in (-T : ℝ)..T,
          hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
            pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    let z : ℂ := (((-1 : ℝ) : ℂ)) + (y : ℂ) * I
    have hz_re : z.re = -1 := by simp [z]
    have hz_im : z.im = y := by simp [z]
    have hz0 : z ≠ 0 := by
      intro hz0
      have hre : z.re = (0 : ℂ).re := by rw [hz0]
      rw [hz_re] at hre
      norm_num at hre
    have hz1 : z ≠ 1 := by
      intro hz1
      have hre : z.re = (1 : ℂ).re := by rw [hz1]
      rw [hz_re] at hre
      norm_num at hre
    -- ζ(z) ≠ 0 on the line Re z = -1 (no nontrivial zeros there; ζ(-1) = -1/12).
    have hζz : riemannZeta z ≠ 0 := by
      by_cases hy0 : y = 0
      · have hz_eq : z = -1 := by
          apply Complex.ext
          · simp [hz_re]
          · simp [hz_im, hy0]
        rw [hz_eq]
        have h := riemannZeta_neg_nat_eq_bernoulli 1
        have hcast : ((-(1 : ℕ) : ℂ)) = (-1 : ℂ) := by push_cast; ring
        rw [hcast] at h
        rw [h]
        push_cast [bernoulli_two]
        norm_num
      · apply riemannZeta_ne_zero_of_re_neg_of_not_neg_int
        · rw [hz_re]; norm_num
        · intro n hn
          have him : z.im = (-↑n : ℂ).im := by rw [hn]
          rw [hz_im] at him
          simp at him
          exact hy0 him
    -- 1 - z has real part 2, so ζ(1-z) ≠ 0 by the Re > 1 nonvanishing.
    have h1z_re : (1 - z).re = 2 := by
      simp [z]; norm_num
    have hζ1z : riemannZeta (1 - z) ≠ 0 := by
      apply zeta_ne_zero_of_one_lt_re
      rw [h1z_re]; norm_num
    -- Γℝ(z) ≠ 0 on the line Re z = -1: requires the trivial-pole avoidance check.
    have hΓz : z.Gammaℝ ≠ 0 := by
      intro h
      rw [Complex.Gammaℝ_eq_zero_iff] at h
      obtain ⟨n, hn⟩ := h
      have hre : z.re = (-(2 * (n : ℂ))).re := by rw [hn]
      rw [hz_re] at hre
      simp at hre
      have h_int : (2 * n : ℤ) = 1 := by
        exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
      omega
    -- Γℝ(1-z) ≠ 0 since Re(1-z) = 2 > 0.
    have hΓ1z : (1 - z).Gammaℝ ≠ 0 := by
      apply gammaℝ_ne_zero_of_re_pos
      rw [h1z_re]; norm_num
    have h_arch :=
      weilIntegrand_arch_decomposition (h := pairTestMellin β) (s := z)
        hz0 hz1 hζz hζ1z hΓz hΓ1z
    -- Rewrite the arch decomposition into the hadamardArchBoundaryTerm form.
    simpa [z, hadamardArchBoundaryTerm] using h_arch
  rw [hright, hleft]

-- Axiom footprint: [propext, Classical.choice, Quot.sound]
-- (Verified by `#print axioms` during development.)

end Contour
end WeilPositivity
end ZD

end
