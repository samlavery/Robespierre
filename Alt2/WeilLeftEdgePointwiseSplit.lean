import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP

/-!
# Left-edge pointwise split of `weilIntegrand` at `σ = -1`

Mirror of the right-edge pointwise split
`weilIntegrand_pair_right_edge_two_split` (in
`WeilFinalAssemblyUnconditional.lean`). Specializes
`Contour.weilIntegrand_split_via_arch` to `s = -1 + iy`, identifying the two
pieces as `Contour.archIntegrand β (-1) y` and
`Contour.reflectedPrimeIntegrand β (-1) y`.

The required nonzero side conditions all hold unconditionally on the line
`Re s = -1`:

* `s ≠ 0`, `s ≠ 1` — trivial (`s.re = -1`).
* `Γℝ(s) ≠ 0` — poles of `Γℝ` are at `s ∈ -2 · ℕ`; `-1 + iy = -2k`
  forces `-1 = -2k` (impossible).
* `Γℝ(1-s) ≠ 0` — `(1-s).re = 2 > 0`, use `Gammaℝ_ne_zero_of_re_pos`.
* `ζ(1-s) ≠ 0` — `(1-s).re = 2 > 1`, use `riemannZeta_ne_zero_of_one_lt_re`.
* `ζ(s) ≠ 0` — derived via the completed-zeta reflection
  `completedRiemannZeta_one_sub`: `ξ(s) = ξ(1-s) ≠ 0` together with
  `Γℝ(s) ≠ 0` give `ζ(s) ≠ 0`.

No `goodHeight T` hypothesis is needed.
-/

noncomputable section

open Complex

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

/-- Pointwise left-edge split for `pairTestMellin β` at `σ = -1`.
Unconditional specialization of `Contour.weilIntegrand_split_via_arch` at
`s = -1 + iy`, identifying the two pieces as `Contour.archIntegrand β (-1) y`
and `Contour.reflectedPrimeIntegrand β (-1) y`. -/
theorem weilIntegrand_pair_left_edge_neg_one_split (β : ℝ) (y : ℝ) :
    Contour.weilIntegrand (Contour.pairTestMellin β)
        (((-1:ℝ):ℂ) + (y:ℂ) * I)
      = Contour.archIntegrand β (-1) y
        + Contour.reflectedPrimeIntegrand β (-1) y := by
  set s : ℂ := (((-1:ℝ):ℂ) + (y:ℂ) * I) with hs_def
  have hs_re : s.re = -1 := by simp [s]
  have h1s_re : (1 - s).re = 2 := by simp [s]; ring
  -- s ≠ 0
  have hne_zero : s ≠ 0 := fun h => by
    have hh : s.re = (0:ℂ).re := by rw [h]
    rw [hs_re] at hh; norm_num at hh
  -- s ≠ 1
  have hne_one : s ≠ 1 := fun h => by
    have hh : s.re = (1:ℂ).re := by rw [h]
    rw [hs_re] at hh; norm_num at hh
  -- Γℝ(s) ≠ 0 at σ = -1: poles of Γℝ are s ∈ -2·ℕ; -1+iy = -2k forces -1 = -2k.
  have hΓ_s : s.Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : s.re = (-(2 * (n:ℂ))).re := by rw [hn]
    rw [hs_re] at hre
    simp at hre
    have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n:ℝ)) = 1)
    omega
  -- Γℝ(1-s) ≠ 0: (1-s).re = 2 > 0
  have hΓ_1s : (1 - s).Gammaℝ ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [h1s_re]; norm_num
  -- ζ(1-s) ≠ 0: (1-s).re = 2 > 1
  have h1s_re_gt : (1:ℝ) < (1 - s).re := by rw [h1s_re]; norm_num
  have hζ_1s : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1s_re_gt
  -- 1 - s ≠ 0
  have h1s_ne_zero : (1 - s) ≠ 0 := by
    intro h
    have hh : (1 - s).re = (0:ℂ).re := by rw [h]
    rw [h1s_re] at hh; norm_num at hh
  -- ζ(s) ≠ 0 via completed-zeta reflection ξ(s) = ξ(1-s).
  have hζ_s : riemannZeta s ≠ 0 := by
    -- ξ(1-s) = Γℝ(1-s) · ζ(1-s) ≠ 0
    have h_xi_1s : completedRiemannZeta (1 - s) =
        (1 - s).Gammaℝ * riemannZeta (1 - s) :=
      Contour.completed_eq_gammaℝ_mul_zeta h1s_ne_zero hΓ_1s
    have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by
      rw [h_xi_1s]; exact mul_ne_zero hΓ_1s hζ_1s
    -- ξ(1-s) = ξ(s) via the functional equation.
    have h_xi_eq : completedRiemannZeta s = completedRiemannZeta (1 - s) := by
      simpa using (completedRiemannZeta_one_sub s).symm
    have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
      rw [h_xi_eq]; exact h_xi_1s_ne
    -- ζ(s) = ξ(s) / Γℝ(s).
    have h_zeta_s_eq :
        riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
      riemannZeta_def_of_ne_zero hne_zero
    rw [h_zeta_s_eq]
    exact div_ne_zero h_xi_s_ne hΓ_s
  -- Apply the split.
  have h_split := Contour.weilIntegrand_split_via_arch β s hne_zero hne_one
    hζ_s hζ_1s hΓ_s hΓ_1s
  -- Identify pieces with archIntegrand / reflectedPrimeIntegrand.
  show Contour.weilIntegrand (Contour.pairTestMellin β) s
      = Contour.archIntegrand β (-1) y + Contour.reflectedPrimeIntegrand β (-1) y
  rw [h_split]
  unfold Contour.archIntegrand Contour.reflectedPrimeIntegrand
  show (deriv Complex.Gammaℝ s / s.Gammaℝ +
         deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ) *
           Contour.pairTestMellin β s +
        deriv riemannZeta (1 - s) / riemannZeta (1 - s) *
           Contour.pairTestMellin β s
      = (deriv Complex.Gammaℝ ((((-1:ℝ)):ℂ) + (y:ℂ) * I) /
            ((((-1:ℝ)):ℂ) + (y:ℂ) * I).Gammaℝ +
          deriv Complex.Gammaℝ (1 - ((((-1:ℝ)):ℂ) + (y:ℂ) * I)) /
            (1 - ((((-1:ℝ)):ℂ) + (y:ℂ) * I)).Gammaℝ) *
          Contour.pairTestMellin β ((((-1:ℝ)):ℂ) + (y:ℂ) * I) +
        deriv riemannZeta (1 - ((((-1:ℝ)):ℂ) + (y:ℂ) * I)) /
          riemannZeta (1 - ((((-1:ℝ)):ℂ) + (y:ℂ) * I)) *
          Contour.pairTestMellin β ((((-1:ℝ)):ℂ) + (y:ℂ) * I)
  rfl

#print axioms weilIntegrand_pair_left_edge_neg_one_split

end FinalAssembly
end WeilPositivity
end ZD
