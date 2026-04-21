import Mathlib
import RequestProject.WeilHorizontalDecay

/-!
# Uniform bound for `-ζ'/ζ` on right half-planes `Re s ≥ σL > 1`

On any closed right half-plane `{s : ℂ | σL ≤ Re s}` with `σL > 1`, the
Dirichlet series `LSeries Λ (s) = ∑ Λ(n)/n^s` converges absolutely, and its
norm is dominated term-by-term by the absolutely convergent real series
`∑ Λ(n)/n^σL`, a fixed real constant.

Therefore `‖LSeries Λ s‖` is uniformly bounded on the strip, and the identity
`LSeries Λ s = -ζ'(s)/ζ(s)` (Mathlib's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`) transfers
this bound to `‖ζ'(s)/ζ(s)‖`.

This gives an *unconditional* polynomial bound (with exponent `N = 0`)
matching the shape `logDerivZeta_polynomial_bound_target σL σR` when `σL > 1`.

Delivered:

* `LSeries_vonMangoldt_bounded_of_right_of_one` — primary uniform bound.
* `logDerivZeta_bounded_of_right_of_one` — consequence on `ζ'/ζ`.
* `logDerivZeta_polynomial_bound_of_right_of_one` — instantiates the
  `WeilHorizontalDecay.lean` named target with `N = 0`.
-/

open Complex Real ArithmeticFunction

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- For `σL > 1` and `Re s ≥ σL`, each term of the `Λ`-Dirichlet series is
dominated in norm by the nonneg real `Λ(n) / n^σL`. -/
lemma term_norm_le_of_right (σL : ℝ) (s : ℂ) (hs : σL ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σL := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [LSeries.term_zero]
  · have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnrpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn', norm_div, Complex.norm_natCast_cpow_of_pos hn]
    rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
          = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hpow : (n : ℝ) ^ σL ≤ (n : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hnr hs
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_pos_of_pos hnrpos σL) hpow

/-- For `σL > 1`, the real series `∑ Λ(n) / n^σL` is summable. This is the
dominating series used for the uniform strip bound. -/
lemma summable_vonMangoldt_rpow (σL : ℝ) (hσL : 1 < σL) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σL) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σL : ℂ) := by
    apply LSeriesSummable_vonMangoldt
    simpa using hσL
  have hs' : Summable
      (fun n => ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σL : ℂ) n‖) :=
    hs.norm
  refine hs'.of_nonneg_of_le ?_ ?_
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) σL).le
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [LSeries.term_zero]
    · have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
      rw [LSeries.term_of_ne_zero hn', norm_div, Complex.norm_natCast_cpow_of_pos hn]
      rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
            = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simp

/-- **Primary bound.** On any closed right half-plane `Re s ≥ σL > 1`, the
Dirichlet L-series of `Λ` is uniformly bounded in norm. -/
theorem LSeries_vonMangoldt_bounded_of_right_of_one
    (σL : ℝ) (hσL : 1 < σL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤ C := by
  set C : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σL with hCdef
  have hsum_R : Summable
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σL) :=
    summable_vonMangoldt_rpow σL hσL
  have hC_nn : 0 ≤ C := by
    refine tsum_nonneg fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) σL).le
  refine ⟨C, hC_nn, fun s hs => ?_⟩
  have hs1 : 1 < s.re := lt_of_lt_of_le hσL hs
  have hsumm_s : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    LSeriesSummable_vonMangoldt hs1
  have hsumm_norm : Summable
      (fun n => ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖) :=
    hsumm_s.norm
  calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
      = ‖∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σL :=
        Summable.tsum_le_tsum (term_norm_le_of_right σL s hs) hsumm_norm hsum_R
    _ = C := hCdef.symm

/-- **Consequence.** `‖-ζ'/ζ(s)‖ = ‖ζ'/ζ(s)‖` is uniformly bounded on
`Re s ≥ σL > 1`, via the identity
`LSeries Λ = -ζ'/ζ`. -/
theorem logDerivZeta_bounded_of_right_of_one
    (σL : ℝ) (hσL : 1 < σL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC_nn, hC_bnd⟩ := LSeries_vonMangoldt_bounded_of_right_of_one σL hσL
  refine ⟨C, hC_nn, fun s hs => ?_⟩
  have hs1 : 1 < s.re := lt_of_lt_of_le hσL hs
  have hid : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have hnorm_eq : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
    rw [hid, neg_div, norm_neg]
  rw [← hnorm_eq]
  exact hC_bnd s hs

/-- **Good-heights polynomial-bound target discharged unconditionally when
`σL > 1`.** For the right-half-plane `σL > 1`, no zeros of `ζ` have real part
in `(σL, σR)` (by `riemannZeta_ne_zero_of_one_lt_re`), so any `T ∈ [T₁, T₁+1]`
avoids zero ordinates (vacuously). Take `T = T₁`. The log-derivative bound at
`(σ+iT₁)` is the uniform constant from `logDerivZeta_bounded_of_right_of_one`.

Matches the good-heights redefinition of
`logDerivZeta_polynomial_bound_target` in `WeilHorizontalDecay.lean`. -/
theorem logDerivZeta_polynomial_bound_of_right_of_one
    (σL σR : ℝ) (hσL : 1 < σL) (_hσR : σL ≤ σR) :
    ZD.WeilPositivity.Contour.logDerivZeta_polynomial_bound_target σL σR := by
  obtain ⟨C, hC_nn, hC_bnd⟩ := logDerivZeta_bounded_of_right_of_one σL hσL
  refine ⟨C + 1, 0, 2, by linarith, by norm_num, ?_⟩
  intro T₁ hT₁
  refine ⟨T₁, le_rfl, by linarith, ?_, ?_⟩
  · intro ρ hρ hρmem
    exfalso
    exact (riemannZeta_ne_zero_of_one_lt_re (by linarith [hσL, hρmem.1])) hρ
  · intro σ hσ
    have hσre : σL ≤ ((σ : ℂ) + (T₁ : ℂ) * I).re := by
      have : ((σ : ℂ) + (T₁ : ℂ) * I).re = σ := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      rw [this]
      exact hσ.1
    have hbnd := hC_bnd _ hσre
    rw [Real.rpow_zero, mul_one]
    linarith

end Contour
end WeilPositivity
end ZD

-- Axiom footprint: [propext, Classical.choice, Quot.sound]
#print axioms ZD.WeilPositivity.Contour.LSeries_vonMangoldt_bounded_of_right_of_one
#print axioms ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one
#print axioms ZD.WeilPositivity.Contour.logDerivZeta_polynomial_bound_of_right_of_one
