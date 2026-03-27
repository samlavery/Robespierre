import Mathlib
/--

-/

theorem mathlib_RH_of_no_offaxis_zeros_one
  (h_no_offaxis :
    ∀ s : ℂ,
      riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re ≠ 1 / 2 →
      False) :
  RiemannHypothesis :=
  fun s hs htriv hone => by_contra (h_no_offaxis s hs htriv hone)

/--

-/
theorem mathlib_RH_of_no_offaxis_zeros
  (h_no_offaxis :
    ∀ s : ℂ,
      riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re ≠ 1 / 2 →
      False) :
  RiemannHypothesis :=
  fun s hs htriv hone => by_contra (h_no_offaxis s hs htriv hone)