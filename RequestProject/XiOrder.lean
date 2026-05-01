import Mathlib
import RequestProject.XiHadamardQuotient

/-!
# Zero orders of `riemannXi` at nontrivial zeros

Defines `xiOrder ρ := analyticOrderNatAt riemannXi ρ : ℕ` for `ρ ∈ NontrivialZeros`.
Proves:
* `xiOrder_ne_top`: Finiteness of the order — follows from identity theorem (ξ
  not locally zero since ξ(0) = 1/2 ≠ 0).
* `xiOrder_pos`: Strictly positive since ρ ∈ NontrivialZeros ⟹ ξ(ρ) = 0.

Used by the multiplicity-indexed Weierstrass product (next file).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- `analyticOrderAt riemannXi ρ ≠ ⊤` for every `ρ`. ξ is not identically zero on
any neighborhood because ξ(0) = 1/2 ≠ 0 + identity theorem. -/
theorem riemannXi_analyticOrderAt_ne_top_everywhere (z : ℂ) :
    analyticOrderAt riemannXi z ≠ ⊤ :=
  ZD.ZeroCount.riemannXi_analyticOrderAt_ne_top z

/-- **Zero order of `riemannXi` at a point**, as a natural number (finite since
ξ is entire non-identically-zero). -/
def xiOrderNat (z : ℂ) : ℕ := analyticOrderNatAt riemannXi z

/-- **Zero order at a nontrivial zero is positive.** ξ(ρ) = 0 + analyticOrder ≠ 0
(since order = 0 would mean ξ(ρ) ≠ 0). -/
theorem xiOrderNat_pos_of_mem_NontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    0 < xiOrderNat ρ := by
  unfold xiOrderNat
  have h_anal : AnalyticAt ℂ riemannXi ρ :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ (Set.mem_univ _)
  have hξ : riemannXi ρ = 0 := (riemannXi_eq_zero_iff ρ).mpr hρ
  have h_ord_ne_zero : analyticOrderAt riemannXi ρ ≠ 0 := by
    intro h_ord
    exact (h_anal.analyticOrderAt_eq_zero.mp h_ord) hξ
  have h_ne_top : analyticOrderAt riemannXi ρ ≠ ⊤ :=
    riemannXi_analyticOrderAt_ne_top_everywhere ρ
  -- analyticOrderNatAt = (analyticOrderAt).toNat, and toNat = 0 iff = 0 or = ⊤.
  by_contra h_le_zero
  push_neg at h_le_zero
  have h_nat_zero : analyticOrderNatAt riemannXi ρ = 0 := Nat.le_zero.mp h_le_zero
  -- analyticOrderNatAt = 0 and ≠ ⊤ ⟹ analyticOrderAt = 0.
  have : analyticOrderAt riemannXi ρ = 0 := by
    rw [← ENat.coe_toNat_eq_self.mpr h_ne_top]
    show ((analyticOrderNatAt riemannXi ρ : ℕ) : ℕ∞) = 0
    rw [h_nat_zero]; rfl
  exact h_ord_ne_zero this

#print axioms xiOrderNat_pos_of_mem_NontrivialZeros

end ZD
