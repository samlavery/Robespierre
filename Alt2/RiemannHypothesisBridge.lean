import RequestProject.DoubleCoshValidation

/-!
# Bridge to Mathlib's `RiemannHypothesis`

Upgrades the classifier chain so its final output is Mathlib's literal
`RiemannHypothesis` predicate, not just our internal statement
`∀ ρ ∈ NontrivialZeros, ρ.re = 1/2`.

## Two predicates, three cases

Mathlib's `RiemannHypothesis` quantifies over **all** complex zeros of
`riemannZeta`, asserting `s.re = 1/2` under two exclusions:
* `s ≠ -2(n+1)` for every `n : ℕ` (exclude the trivial zeros)
* `s ≠ 1` (exclude the pole)

Our `ZD.NontrivialZeros` is the narrower set `{s | 0 < s.re < 1 ∧ ζ(s) = 0}`.
The bridge handles three cases for a zero `s` satisfying the Mathlib exclusions:
* `1 ≤ s.re` → no zeros there (Mathlib: `riemannZeta_ne_zero_of_one_le_re`).
* `0 < s.re < 1` → `s ∈ NontrivialZeros`, apply our hypothesis.
* `s.re ≤ 0` → route through the completed-zeta functional equation
   `Λ(1-s) = Λ(s)`, getting `ζ(1-s) = 0` with `Re(1-s) ≥ 1`, contradiction.

## Capstones

* `no_offline_zeros_implies_rh` — the core bridge from
  `∀ ρ ∈ NontrivialZeros, ρ.re = 1/2` to Mathlib's `RiemannHypothesis`.
* `RiemannHypothesis_implies_classifier_balance` — the
  RH → observable direction.
-/

open Real ZetaDefs DoubleCoshResidue DoubleCoshValidation Complex

noncomputable section

namespace RHBridge

/-! ### §1. Core bridge -/

/-- **Core bridge**: universal on-line placement of `NontrivialZeros` implies
Mathlib's `RiemannHypothesis`. Three-case analysis on `s.re`; the `s.re ≤ 0`
case routes through the completed-zeta FE. -/
theorem no_offline_zeros_implies_rh
    (hline : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hs hnt hne1
  by_cases h1 : 1 ≤ s.re
  · exact absurd hs (riemannZeta_ne_zero_of_one_le_re h1)
  push_neg at h1
  by_cases h0 : 0 < s.re
  · exact hline s ⟨h0, h1, hs⟩
  push_neg at h0
  exfalso
  have hne0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp [riemannZeta_zero] at hs
  have hdef : completedRiemannZeta s / s.Gammaℝ = 0 :=
    (riemannZeta_def_of_ne_zero hne0).symm.trans hs
  rw [div_eq_zero_iff] at hdef
  have hξ : completedRiemannZeta s = 0 := by
    rcases hdef with h | h
    · exact h
    · exfalso
      simp only [Complex.Gammaℝ] at h
      have hpi : (↑Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
      have hΓ : Complex.Gamma (s / 2) = 0 :=
        (mul_eq_zero.mp h).resolve_left hpi
      rw [Complex.Gamma_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hs_eq : s = -2 * (m : ℂ) := by linear_combination 2 * hm
      rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
      · rw [hm0] at hs_eq; simp at hs_eq; exact hne0 hs_eq
      · apply hnt
        refine ⟨m - 1, ?_⟩
        have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
          have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel hm_pos
          exact_mod_cast h
        rw [hs_eq, ← hcast]
  have hξ1 : completedRiemannZeta (1 - s) = 0 :=
    (completedRiemannZeta_one_sub s).trans hξ
  have hne1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hζ1s : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero hne1', hξ1, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re
    (by simp only [Complex.sub_re, Complex.one_re]; linarith) hζ1s


end RHBridge

end
