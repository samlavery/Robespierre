import Mathlib
import RequestProject.XiHadamardFactorization

import RequestProject.XiProductMultPartialFraction

/-!
# H8: Partial fraction `ξ'/ξ(s) = A + Σ_ρ xiOrderNat(ρ) · [1/(s-ρ) + 1/ρ]`

Unconditional partial fraction for `logDeriv xiProductMult`, and the H6-derived
version for `riemannXi`.
-/

open Complex Filter Topology Set

noncomputable section

namespace ZD

#print axioms logDeriv_xiProductMult_partial_fraction

-- ═══════════════════════════════════════════════════════════════════════════
-- § Main H8: ξ'/ξ partial fraction from the weaker constant-difference input
-- ═══════════════════════════════════════════════════════════════════════════

/-- **H8 main theorem**: Hadamard partial fraction for `ξ'/ξ` with
multiplicity-weighted residues. Derived from the weaker constancy theorem
`xi_logDeriv_sub_product_const_off_zeros` plus
`logDeriv_xiProductMult_partial_fraction`. -/
theorem xi_logDeriv_partial_fraction :
    ∃ A : ℂ, ∀ s : ℂ, s ∉ NontrivialZeros →
      deriv riemannXi s / riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨A, hA⟩ := xi_logDeriv_sub_product_const_off_zeros
  refine ⟨A, fun s hs => ?_⟩
  have h_diff := hA s hs
  calc
    deriv riemannXi s / riemannXi s =
        (deriv riemannXi s / riemannXi s - logDeriv xiProductMult s) +
          logDeriv xiProductMult s := by
          ring
    _ = A + logDeriv xiProductMult s := by
          rw [h_diff]
    _ = A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
          rw [logDeriv_xiProductMult_partial_fraction hs]

#print axioms xi_logDeriv_partial_fraction

end ZD
