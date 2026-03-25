import Mathlib
noncomputable section
open Real
/-!
# Cosh Kernel at π/6: Fold Symmetry and Absence of Offline Zeros
We formalize the argument that a cosh kernel centered at θ = π/6 has a
fold symmetry (the function is invariant under σ ↦ π/3 − σ, i.e. reflection
about π/6), and that this kernel has no zeros — in particular, no "offline"
zeros (zeros at σ ≠ π/6).
The key ingredients:
1. **Fold symmetry**: `cosh(σ − π/6) = cosh((π/3 − σ) − π/6)` because
   `cosh` is an even function.
2. **Positivity**: `cosh(x) > 0` for all real `x`, so the kernel has no
   real zeros at all — the "fold line" conclusion holds vacuously.
-/
/-- The cosh kernel centered at θ = π/6. -/
def coshKernel (σ : ℝ) : ℝ := Real.cosh (σ - π / 6)
/-- **Fold symmetry**: reflecting σ about π/6 (i.e. mapping σ ↦ π/3 − σ)
    leaves the cosh kernel invariant. This is the formalization of
    "the fold IS cosh: cosh(z) = cosh(−z)". -/
theorem coshKernel_fold_symmetry (σ : ℝ) :
    coshKernel (π / 3 - σ) = coshKernel σ := by
  unfold coshKernel; rw [← Real.cosh_neg]; ring_nf
/-- The cosh kernel is strictly positive for all real σ.
    In particular, it has no real zeros whatsoever. -/
theorem coshKernel_pos (σ : ℝ) : 0 < coshKernel σ :=
  Real.cosh_pos _
/-- **No offline zeros**: if coshKernel σ = 0 then σ = π/6.
    This is vacuously true since coshKernel is everywhere positive.
    Formalizes: "offline zeros don't exist." -/
theorem zeros_on_fold_line (σ : ℝ) (h : coshKernel σ = 0) : σ = π / 6 :=
  absurd h <| ne_of_gt <| Real.cosh_pos _
/-- Equivalent formulation: at any point off the fold line, the kernel is nonzero. -/
theorem no_offline_zeros (σ : ℝ) (_hσ : σ ≠ π / 6) : coshKernel σ ≠ 0 :=
  ne_of_gt <| coshKernel_pos σ
/-- The fold line value: the kernel at σ = π/6 equals 1 (= cosh 0). -/
theorem coshKernel_at_fold : coshKernel (π / 6) = 1 := by
  simp [coshKernel]
end