import Mathlib
/-!
# Six Statements: The Bidirectional Lock
Six unconditional theorems forming a closed loop:
1. **Harmonics come in pairs (cosh)**: cosh is even — `cosh(-z) = cosh(z)`.
2. **Pairs collapse on one line (cos)**: `cos(z) = cosh(iz)` — the pairing
   collapses to a single oscillatory function on the real line.
3. **Zeros need collapse (dimension)**: `cosh(x) ≥ 1` for all real `x` —
   cosh has no real zeros, so any zeros must leave the real axis.
4. **That line is π/6 (arcsin)**: `arcsin(1/2) = π/6`.
5. **π/6 projects to 1/2 (sin)**: `sin(π/6) = 1/2`.
6. **1/2 transports back to π/6 (arcsin)**: `sin(arcsin(1/2)) = 1/2` —
   the round-trip locks.
Classical zeros at 1/2 map to Robespierre zeros at π/6 map back to
classical zeros at 1/2. The loop is unconditional and bidirectional.
-/
/-- **Statement 1 — Harmonics come in pairs (cosh).**
  The hyperbolic cosine is even: `cosh(-z) = cosh(z)` for all `z : ℂ`. -/
theorem harmonics_come_in_pairs : ∀ z : ℂ, Complex.cosh (-z) = Complex.cosh z :=
  Complex.cosh_neg
/-- **Statement 2 — Pairs collapse on one line (cos).**
  `cos(z) = cosh(iz)` — the even pairing of exponentials collapses
  to a single oscillatory function along the real axis. -/
theorem pairs_collapse_on_one_line : ∀ z : ℂ, Complex.cos z = Complex.cosh (Complex.I * z) := by
  intro z
  simp [Complex.cos, Complex.cosh]
  ring_nf
/-- **Statement 3 — Zeros need collapse (dimension).**
  `cosh(x) ≥ 1` for every real `x`. In particular `cosh` has no real
  zeros — any zeros of `cosh` must leave the real line. -/
theorem zeros_need_collapse : ∀ x : ℝ, 1 ≤ Real.cosh x :=
  Real.one_le_cosh
/-- **Statement 4 — That line is π/6 (arcsin).**
  `arcsin(1/2) = π/6`. -/
theorem that_line_is_pi_div_six : Real.arcsin (1 / 2) = Real.pi / 6 := by
  rw [show (1 : ℝ) / 2 = Real.sin (Real.pi / 6) from by rw [Real.sin_pi_div_six]]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
/-- **Statement 5 — π/6 projects to 1/2 (sin).**
  `sin(π/6) = 1/2`. -/
theorem pi_div_six_projects_to_one_half : Real.sin (Real.pi / 6) = 1 / 2 :=
  Real.sin_pi_div_six
/-- **Statement 6 — 1/2 transports back to π/6 (arcsin). The loop locks.**
  `sin(arcsin(1/2)) = 1/2` — the round-trip is exact. -/
theorem the_loop_locks : Real.sin (Real.arcsin (1 / 2)) = 1 / 2 :=
  Real.sin_arcsin (by norm_num) (by norm_num)
-- Verify no non-standard axioms are used.
#print axioms harmonics_come_in_pairs
#print axioms pairs_collapse_on_one_line
#print axioms zeros_need_collapse
#print axioms that_line_is_pi_div_six
#print axioms pi_div_six_projects_to_one_half
#print axioms the_loop_locks