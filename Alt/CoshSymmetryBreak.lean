import Mathlib

open Real

/-!
# Cosh Residue vs. Cosh Symmetry Reflection Test

The hyperbolic cosine function `cosh` is even: `cosh(x) = cosh(-x)` for all `x`.
The **cosh symmetry reflection test** checks whether a function `f` shares this
even-symmetry property, i.e., whether `∀ x, f(x) = f(-x)`.

The **cosh residue** of `f` at a point `x` is the asymmetric remainder
`f(x) - f(-x)`. If any such residue is nonzero — meaning there exists an `x`
with `f(x) ≠ f(-x)` — then the symmetry reflection test must fail.

We formalize this in several forms below.
-/

/-- A function passes the cosh symmetry reflection test iff it is even. -/
def PassesCoshSymmetryTest (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

/-- The cosh residue of `f` at `x` is `f(x) - f(-x)`. -/
noncomputable def coshResidue (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - f (-x)

/-- A cosh residue remains if there exists a point where the residue is nonzero. -/
def HasCoshResidue (f : ℝ → ℝ) : Prop :=
  ∃ x, coshResidue f x ≠ 0

/-- **Main theorem**: If any cosh residue remains, the cosh symmetry reflection
test must fail. -/
theorem cosh_residue_implies_symmetry_test_fails
    (f : ℝ → ℝ) (h : HasCoshResidue f) : ¬ PassesCoshSymmetryTest f := by
  exact fun H => h.choose_spec <| sub_eq_zero_of_eq <| H _ ▸ rfl

/-- `cosh` itself passes the symmetry test, since `cosh(-x) = cosh(x)`. -/
theorem cosh_passes_symmetry_test : PassesCoshSymmetryTest cosh := by
  unfold PassesCoshSymmetryTest; aesop

/-- The cosh residue of `cosh` is zero everywhere. -/
theorem cosh_residue_zero : ∀ x, coshResidue cosh x = 0 := by
  unfold coshResidue; aesop

/-- `cosh` has no cosh residue. -/
theorem cosh_has_no_residue : ¬ HasCoshResidue cosh := by
  exact fun ⟨x, hx⟩ => hx (by rw [coshResidue, Real.cosh_neg]; ring)
