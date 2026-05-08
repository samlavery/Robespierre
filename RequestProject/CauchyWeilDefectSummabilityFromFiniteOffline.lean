import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.GaussianClosedForm
import RequestProject.GaussianAdmissible
import RequestProject.ExplicitFormulaBridgeOfRH

/-!
# ℓ¹ summability of `GaussianDefectCoefficient_local` from finite off-line zero set

This file discharges Component (1) of `CauchyWeilGaussianDefectExtraction_target_local`
from a single named hypothesis: that the off-line nontrivial zero set is finite.
The hypothesis `Set.Finite {ρ ∈ NontrivialZeros | ρ.re ≠ 1/2}` is strictly weaker
than RH (RH ⟹ the set is empty, hence finite), but is not currently provable in
the project from existing infrastructure.

Mathematical content: by `averageEnergyDefect_gaussian_closed_form`, the
coefficient evaluates as `π·√(π/2) · (exp(δ²/8) − 1)²` with `δ = ρ.re − 1/2`.
The factor `(exp(δ²/8) − 1)²` vanishes exactly at `δ = 0`, i.e. for `ρ` on the
critical line. Outside the off-line set the summand is zero, so the sum has
finite support.
-/

open Real Complex MeasureTheory BigOperators
open scoped Classical

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

/-- For a nontrivial zero `ρ` on the critical line, the Gaussian defect
coefficient vanishes. -/
theorem GaussianDefectCoefficient_eq_zero_of_re_half
    (ρ : ℂ) (h : ρ.re = 1/2) :
    GaussianDefectCoefficient_local ρ = 0 := by
  unfold GaussianDefectCoefficient_local
  show ((ZD.averageEnergyDefect ZD.gaussianKernel ρ.re : ℝ) : ℂ) = 0
  change ((ZD.averageEnergyDefect ZD.ψ_gaussian ρ.re : ℝ) : ℂ) = 0
  rw [ZD.averageEnergyDefect_gaussian_closed_form ρ.re, h]
  -- After substituting `ρ.re = 1/2`, `δ = 0`, so
  -- `exp(0) − 2·exp(0) + 1 = 1 − 2 + 1 = 0`.
  have h_delta : ((1 : ℝ)/2 - 1/2)^2 = 0 := by norm_num
  have h_inner : Real.exp (((1:ℝ)/2 - 1/2)^2 / 2) -
      2 * Real.exp (((1:ℝ)/2 - 1/2)^2 / 8) + 1 = 0 := by
    rw [h_delta]
    simp [Real.exp_zero]
    norm_num
  rw [h_inner]
  push_cast
  ring

/-- The off-line subset of nontrivial zeros, lifted to the subtype. -/
def offlineSubtypeSet :
    Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ρ.val.re ≠ 1/2}

/-- The off-line subset of `NontrivialZeros` (as a `Set ℂ`). -/
def offlineSet : Set ℂ :=
  {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ ρ.re ≠ 1/2}

/-- Lifting finiteness of `offlineSet` to finiteness of its subtype lift. -/
theorem offlineSubtypeSet_finite_of_offlineSet_finite
    (h_fin : Set.Finite offlineSet) :
    Set.Finite offlineSubtypeSet := by
  -- Map subtype-elements `ρ : {ρ // ρ ∈ NTZ}` with `ρ.val.re ≠ 1/2` to `ρ.val ∈ offlineSet`.
  have h_inj :
      Set.InjOn (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ρ.val) offlineSubtypeSet := by
    intro a _ b _ h
    exact Subtype.ext h
  have h_image :
      (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ρ.val) '' offlineSubtypeSet ⊆ offlineSet := by
    rintro x ⟨ρ, hρ_mem, rfl⟩
    refine ⟨ρ.property, ?_⟩
    exact hρ_mem
  exact (h_fin.subset h_image).of_finite_image h_inj

/-- **Component (1) discharge from finite off-line zero set.**

Under the hypothesis that only finitely many nontrivial zeros are off the
critical line, the ℓ¹ summability of `GaussianDefectCoefficient_local` follows
from finite support: on-line zeros contribute `0` (by
`GaussianDefectCoefficient_eq_zero_of_re_half`), and off-line zeros form a
finite set. -/
theorem cauchyWeilDefectSummableNorm_of_finite_offline
    (h_fin : Set.Finite offlineSet) :
    CauchyWeilGaussianDefectSummableNorm_target_local := by
  -- Lift finiteness to the subtype.
  have h_fin_sub : Set.Finite offlineSubtypeSet :=
    offlineSubtypeSet_finite_of_offlineSet_finite h_fin
  -- The summand `‖GaussianDefectCoefficient_local ρ.val‖` is zero outside
  -- `offlineSubtypeSet` (where it equals 0 by the on-line case) and arbitrary
  -- inside. Hence its support is contained in `offlineSubtypeSet`, which is
  -- finite.
  have h_supp :
      (Function.support (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
          ‖GaussianDefectCoefficient_local ρ.val‖)) ⊆ offlineSubtypeSet := by
    intro ρ hρ
    -- `hρ : ‖GaussianDefectCoefficient_local ρ.val‖ ≠ 0`
    -- ⟹ `GaussianDefectCoefficient_local ρ.val ≠ 0` ⟹ `ρ.val.re ≠ 1/2`.
    have hne : GaussianDefectCoefficient_local ρ.val ≠ 0 := fun h0 => by
      apply hρ
      show ‖GaussianDefectCoefficient_local ρ.val‖ = 0
      rw [h0]; exact norm_zero
    show ρ.val.re ≠ 1/2
    intro h_re
    exact hne (GaussianDefectCoefficient_eq_zero_of_re_half ρ.val h_re)
  have h_supp_finite : (Function.support (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖GaussianDefectCoefficient_local ρ.val‖)).Finite :=
    h_fin_sub.subset h_supp
  exact summable_of_hasFiniteSupport h_supp_finite

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
