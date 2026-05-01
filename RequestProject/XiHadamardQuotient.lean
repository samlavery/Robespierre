import Mathlib
import RequestProject.XiProductZeros

/-!
# ξ has zeros exactly at nontrivial zeros of ζ (classical fact) + quotient well-defined

H4 of the Hadamard-track plan. Two pieces:

* **`riemannXi_eq_zero_iff`** — classical: `riemannXi z = 0 ↔ z ∈ NontrivialZeros`.
  Proven from the factorization `riemannXi = (s(s-1)/2) · completedRiemannZeta`,
  the functional equation `completedRiemannZeta s = completedRiemannZeta (1-s)`,
  and non-vanishing of ζ and Γℝ outside the critical strip.

* **`xiOverP_analytic_zero_free`** — given the zero-set equality, the raw quotient
  `z ↦ riemannXi z / xiProduct z` extends via removable singularities at each
  nontrivial zero (orders match by H7 of the B-agent's analyticOrderAt theorem
  10: one factor of `xiProduct` per nontrivial zero yields `analyticOrderAt
  xiProduct ρ = 1`; classical argument gives `analyticOrderAt riemannXi ρ =
  analyticOrderAt ζ ρ`; the H-track uses the multiplicity-indexed product where
  repetition matches each order exactly).

In the current simple-zero formulation of `xiProduct`, order matching holds
iff ζ has simple zeros (expected classically, but not independently proven —
hence the multiplicity-indexed reformulation is deferred to a separate pass).

**This file** discharges the zero-set equality (well-known, unconditional)
and provides the infrastructure for H5/H6. The multiplicity refactor of
`xiProduct` happens in a follow-up pass.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- **Key classical fact**: `completedRiemannZeta z = 0 ↔ z ∈ NontrivialZeros`.

Forward: if `completedRiemannZeta z = 0`:
* If `1 < z.re`: `ζ(z) ≠ 0` (Mathlib `riemannZeta_ne_zero_of_one_lt_re`), and
  `completedRiemannZeta = Gammaℝ · ζ` via `riemannZeta_def_of_ne_zero` with both factors
  nonzero — contradiction.
* If `z.re < 0`: FE `completedRiemannZeta z = completedRiemannZeta (1-z)` with
  `Re(1-z) > 1`, reduces to the previous case.
* If `0 < z.re < 1` and `z.re = 0` or `z.re = 1` boundary cases: classical zeros live
  in strictly open strip; boundary handled via non-vanishing on `Re = 1`.

Backward: `z ∈ NontrivialZeros` means `ζ(z) = 0` with `0 < Re z < 1`, so
`z ≠ 0, 1`, and `completedRiemannZeta = Gammaℝ · ζ = Gammaℝ · 0 = 0`. -/
theorem completedRiemannZeta_eq_zero_iff (z : ℂ) :
    completedRiemannZeta z = 0 ↔ z ∈ NontrivialZeros := by
  constructor
  · intro hcomp
    -- Work by case analysis on Re z.
    -- Need to exclude cases where Re z ≤ 0 or Re z ≥ 1.
    by_contra hnot
    -- Goal: derive False from `hcomp : completedRiemannZeta z = 0` and `hnot : z ∉ NontrivialZeros`.
    -- NontrivialZeros = {0 < Re z ∧ Re z < 1 ∧ ζ z = 0}.
    simp only [NontrivialZeros, Set.mem_setOf_eq, not_and] at hnot
    -- Case Re z ≤ 0: use FE to reduce to Re(1-z) ≥ 1.
    -- Case Re z ≥ 1: ζ ≠ 0 and Gammaℝ ≠ 0 (for Re > 0).
    -- Case 0 < Re z < 1 and ζ z ≠ 0: contradicts hcomp.
    by_cases hRe_lt : z.re < 1
    · by_cases hRe_pos : 0 < z.re
      · -- 0 < Re z < 1, so z ∉ NontrivialZeros means ζ z ≠ 0.
        have hζ_ne : riemannZeta z ≠ 0 := hnot hRe_pos hRe_lt
        -- completedRiemannZeta = Gammaℝ · ζ since z ≠ 0 (Re z > 0).
        have hz_ne0 : z ≠ 0 := by
          intro h; rw [h] at hRe_pos; simp at hRe_pos
        have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hRe_pos
        have hrw := riemannZeta_def_of_ne_zero hz_ne0
        -- hrw: ζ z = completedRiemannZeta z / Gammaℝ z.
        rw [hcomp, zero_div] at hrw
        exact hζ_ne hrw
      · -- Re z ≤ 0: use FE.
        push_neg at hRe_pos
        -- Re(1 - z) ≥ 1.
        have h1z_re : 1 ≤ (1 - z).re := by simp; linarith
        have h1z_re_pos : 0 < (1 - z).re := by linarith
        have h1z_ne0 : (1 - z) ≠ 0 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith
        -- FE: completedRiemannZeta (1-z) = completedRiemannZeta z, so LHS also 0.
        have hFE : completedRiemannZeta (1 - z) = completedRiemannZeta z :=
          completedRiemannZeta_one_sub z
        rw [← hFE] at hcomp
        -- Now (1 - z) has Re ≥ 1. If Re > 1, use non-vanishing of ζ and Gammaℝ.
        -- If Re = 1, still non-vanishing (ζ doesn't vanish on Re = 1).
        rcases eq_or_lt_of_le h1z_re with hRe_eq | hRe_gt
        · -- Re(1-z) = 1 case: ζ ≠ 0 on Re = 1 (Mathlib riemannZeta_ne_zero_of_one_le_re).
          have hζ_1z : riemannZeta (1 - z) ≠ 0 :=
            riemannZeta_ne_zero_of_one_le_re (by linarith : (1 : ℝ) ≤ (1 - z).re)
          have hGammaℝ_1z : Complex.Gammaℝ (1 - z) ≠ 0 :=
            Complex.Gammaℝ_ne_zero_of_re_pos h1z_re_pos
          have hrw := riemannZeta_def_of_ne_zero h1z_ne0
          rw [hcomp, zero_div] at hrw
          exact hζ_1z hrw
        · -- Re(1-z) > 1: ζ ≠ 0.
          have hζ_1z : riemannZeta (1 - z) ≠ 0 :=
            riemannZeta_ne_zero_of_one_lt_re hRe_gt
          have hGammaℝ_1z : Complex.Gammaℝ (1 - z) ≠ 0 :=
            Complex.Gammaℝ_ne_zero_of_re_pos h1z_re_pos
          have hrw := riemannZeta_def_of_ne_zero h1z_ne0
          rw [hcomp, zero_div] at hrw
          exact hζ_1z hrw
    · -- Re z ≥ 1.
      push_neg at hRe_lt
      have hz_re_pos : 0 < z.re := by linarith
      have hz_ne0 : z ≠ 0 := by
        intro h; rw [h] at hz_re_pos; simp at hz_re_pos
      have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz_re_pos
      have hζ_ne : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hRe_lt
      have hrw := riemannZeta_def_of_ne_zero hz_ne0
      rw [hcomp, zero_div] at hrw
      exact hζ_ne hrw
  · intro ⟨hre_pos, hre_lt, hζ⟩
    -- completedRiemannZeta z = Gammaℝ z · ζ z = Gammaℝ z · 0 = 0.
    have hz_ne0 : z ≠ 0 := by
      intro h; rw [h] at hre_pos; simp at hre_pos
    rw [riemannZeta_def_of_ne_zero hz_ne0] at hζ
    have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre_pos
    exact (div_eq_zero_iff.mp hζ).resolve_right hGammaℝ_ne

#print axioms completedRiemannZeta_eq_zero_iff

/-- **`riemannXi` zero set equals `NontrivialZeros`** (classical unconditional fact).

For `z ≠ 0, 1`: `riemannXi z = (z(z-1)/2) · completedRiemannZeta z`, and the polynomial
prefactor is nonzero, so zeros of `riemannXi` coincide with zeros of `completedRiemannZeta`.
For `z = 0` or `z = 1`: `riemannXi z = 1/2 ≠ 0` (from the `+ 1/2` constant in our
`ZD.riemannXi` definition). -/
theorem riemannXi_eq_zero_iff (z : ℂ) :
    ZD.riemannXi z = 0 ↔ z ∈ NontrivialZeros := by
  by_cases hz0 : z = 0
  · rw [hz0, ZD.ZeroCount.riemannXi_zero]
    constructor
    · intro h; exfalso; norm_num at h
    · intro ⟨hre_pos, _, _⟩; exfalso; simp at hre_pos
  by_cases hz1 : z = 1
  · rw [hz1]
    have h_xi_one : ZD.riemannXi 1 = 1 / 2 := by
      have h := ZD.ZeroCount.riemannXi_one_sub 0
      -- h : ZD.riemannXi (1 - 0) = ZD.riemannXi 0
      have h' : ZD.riemannXi 1 = ZD.riemannXi 0 := by
        rw [show (1 : ℂ) = 1 - 0 from by ring]; exact h
      rw [h', ZD.ZeroCount.riemannXi_zero]
    rw [h_xi_one]
    constructor
    · intro h; exfalso; norm_num at h
    · intro ⟨_, hre_lt, _⟩; exfalso; simp at hre_lt
  -- Now z ≠ 0, 1: use classical form.
  rw [riemannXi_eq_classical_of_ne_zero_of_ne_one z hz0 hz1]
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with hpoly | hcomp
    · -- z(z-1)/2 = 0, but z ≠ 0 and z ≠ 1, contradiction.
      exfalso
      have h_zz1 : z * (z - 1) = 0 :=
        (div_eq_zero_iff.mp hpoly).resolve_right two_ne_zero
      rcases mul_eq_zero.mp h_zz1 with h | h
      · exact hz0 h
      · exact hz1 (by linear_combination h)
    · -- completedRiemannZeta z = 0 ⟺ z ∈ NontrivialZeros.
      exact (completedRiemannZeta_eq_zero_iff z).mp hcomp
  · intro hntz
    right
    exact (completedRiemannZeta_eq_zero_iff z).mpr hntz

#print axioms riemannXi_eq_zero_iff

end ZD
