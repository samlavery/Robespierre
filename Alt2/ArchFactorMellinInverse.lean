import Mathlib

/-!
# Inverse Mellin transform of the archimedean log-derivative factor at σ = 2

We work with the **archimedean factor**

`archFactor s := Γℝ'/Γℝ(s) + Γℝ'/Γℝ(1 − s)`

and the meromorphic function

`archFactorMellinIntegrand s := archFactor s / (s · (s + 1))`

obtained by dividing by the standard `s(s+1)` denominator that appears when
splitting `arch_factor / (s · (1 − s))` between residues.

The goal of this file is to **define** the inverse Mellin transform of
`archFactorMellinIntegrand` along the vertical line `Re s = 2` and to expose
the resulting function `archFactorKernel : ℝ → ℂ` together with the basic
unfolding lemmas that future turns can use to prove the forward Mellin
identity

`mellin (archFactorKernel) s = archFactorMellinIntegrand s`

for `1 < Re s < 3`.

## Status of the forward identity (honest report)

Mathlib currently provides only the forward direction
`mellinInv σ (mellin f) = f` (`Mathlib.Analysis.MellinInversion`,
`mellinInv_mellin_eq`).  The converse direction, namely

`mellin (mellinInv σ F) = F`

for an absolutely integrable `F` along `Re s = σ`, is **not** in mathlib at
the time of writing.  Proving it in this generality requires the Fourier
inversion theorem applied through `mellin_eq_fourier`, plus regularity
hypotheses on `F` that are non-trivial for the digamma factor here.  Without
either (a) extending `Mathlib.Analysis.MellinInversion` or (b) carrying out
a term-by-term Hurwitz expansion of `digamma`, the forward Mellin identity
cannot be proved axiom-clean in a single turn.

What we deliver below is therefore the part of the construction that is
fully unconditional:

1. The definitions `archFactor`, `archFactorMellinIntegrand`, and
   `archFactorKernel`.
2. The definitional unfolding lemmas
   `archFactorKernel_def` and `mellinInv_archFactor_eq_kernel`.

These give downstream callers a stable name and a concrete formula for the
inverse-Mellin kernel at `σ = 2`.  Adding the forward Mellin identity to
this file is the natural next task once the converse Mellin-inversion
direction has been added to mathlib (or proved locally for the digamma
class).

## References to repo infrastructure (not re-proved here)

* `RequestProject.UniformGammaRBound`:
  `digamma_log_bound_uniform_sigma01`, `gammaR_logDeriv_uniform_criticalStrip`
  — σ-uniform `O(log T)` bounds on `Γℝ'/Γℝ` along vertical lines in the
  critical strip (not directly applied at σ = 2; the σ = 2 bound goes via
  the recurrence `digamma(z+1) = digamma(z) + 1/z`).
* `RequestProject.WeilArchPrimeIdentity.archIntegrand`
  — the same arch factor, multiplied by `pairTestMellin β`, integrated
  along `Re s = σ₀` rather than inverse-Mellin-transformed.
-/

open Complex MeasureTheory

noncomputable section

namespace ArchFactorMellinInverse

/-- The **archimedean log-derivative factor**

`archFactor s = Γℝ'/Γℝ(s) + Γℝ'/Γℝ(1 − s)`.

This is the same factor that appears as the prefactor of `pairTestMellin`
in `RequestProject.WeilArchPrimeIdentity.archIntegrand`. -/
def archFactor (s : ℂ) : ℂ :=
  deriv Complex.Gammaℝ s / s.Gammaℝ +
    deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ

/-- The integrand of the inverse Mellin transform we are studying:
`archFactor(s) / (s · (s + 1))`. -/
def archFactorMellinIntegrand (s : ℂ) : ℂ :=
  archFactor s / (s * (s + 1))

/-- The **inverse-Mellin kernel** of the arch-factor integrand at `σ = 2`.

By definition this is `mellinInv 2 archFactorMellinIntegrand x`, the
contour integral

`(1 / (2π)) · ∫ y, x ^ -(2 + iy) · archFactorMellinIntegrand (2 + iy) dy`.

The forward identity `mellin archFactorKernel s = archFactorMellinIntegrand s`
is **not** proved in this file — see the file-level docstring for the
honest reason. -/
def archFactorKernel (x : ℝ) : ℂ :=
  mellinInv 2 archFactorMellinIntegrand x

/-- Definitional unfolding of `archFactorKernel`. -/
theorem archFactorKernel_def (x : ℝ) :
    archFactorKernel x =
      (1 / (2 * Real.pi)) •
        ∫ y : ℝ,
          (x : ℂ) ^ (-((2 : ℂ) + y * I)) •
            archFactorMellinIntegrand ((2 : ℂ) + y * I) := by
  rfl

/-- The kernel is, by construction, the `mellinInv` of the arch-factor
integrand at `σ = 2`. -/
theorem mellinInv_archFactor_eq_kernel :
    mellinInv 2 archFactorMellinIntegrand = archFactorKernel := by
  rfl

/-- Restatement: at every `x : ℝ`, the kernel agrees with the inverse
Mellin transform. -/
theorem mellinInv_archFactor_apply (x : ℝ) :
    mellinInv 2 archFactorMellinIntegrand x = archFactorKernel x := rfl

end ArchFactorMellinInverse

end
