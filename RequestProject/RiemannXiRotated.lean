import Mathlib
import RequestProject.ThetaTransport
import RequestProject.ZeroCountJensen

/-!
# Rotated Riemann ξ function

Defines `riemannXiRotated z := riemannXi (1/2 + i z)` — an entire function
in the rotated variable where the functional equation becomes `Ξ(-z) = Ξ(z)`
(even). This is the standard normalization used by Hadamard-Jensen arguments
over short height windows `[T-1, T+1]`.

Ported from Aristotle's Hadamard-Jensen package (codex2).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- Rotated Riemann ξ-function for Hadamard arguments:
`Ξ(z) = ξ(1 / 2 + i z)`. -/
def riemannXiRotated (z : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.I * z)

theorem riemannXiRotated_differentiable :
    Differentiable ℂ riemannXiRotated := by
  have hAffine : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) :=
    Differentiable.const_add (1 / 2 : ℂ)
      (Differentiable.const_mul differentiable_id Complex.I)
  change Differentiable ℂ (riemannXi ∘ fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z)
  exact riemannXi_differentiable.comp hAffine

theorem riemannXiRotated_continuous :
    Continuous riemannXiRotated :=
  riemannXiRotated_differentiable.continuous

theorem riemannXiRotated_analyticOnNhd_univ :
    AnalyticOnNhd ℂ riemannXiRotated Set.univ :=
  riemannXiRotated_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- The rotated ξ-function is even, which is the clean functional-equation form
for Hadamard arguments. -/
theorem riemannXiRotated_even (z : ℂ) :
    riemannXiRotated (-z) = riemannXiRotated z := by
  unfold riemannXiRotated
  calc
    riemannXi ((1 / 2 : ℂ) + Complex.I * (-z))
      = riemannXi (1 - ((1 / 2 : ℂ) + Complex.I * z)) := by
          congr 1
          ring
    _ = riemannXi ((1 / 2 : ℂ) + Complex.I * z) :=
          ZD.ZeroCount.riemannXi_one_sub ((1 / 2 : ℂ) + Complex.I * z)

/-- Zero pairing in rotated coordinates. -/
theorem riemannXiRotated_zero_pairing {z : ℂ}
    (hz : riemannXiRotated z = 0) :
    riemannXiRotated (-z) = 0 := by
  rw [riemannXiRotated_even]
  exact hz

/-- Every nontrivial zero of `ζ` gives a zero of rotated ξ after the affine
change of variables `ρ = 1 / 2 + i z`. -/
theorem riemannXiRotated_eq_zero_of_mem_NontrivialZeros
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    riemannXiRotated ((ρ - (1 / 2 : ℂ)) / Complex.I) = 0 := by
  unfold riemannXiRotated
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have harg : (1 / 2 : ℂ) + Complex.I * ((ρ - (1 / 2 : ℂ)) / Complex.I) = ρ := by
    field_simp [hI]
    ring
  rw [harg]
  exact riemannXi_eq_zero_of_mem_NontrivialZeros ρ hρ

end ZD
