import Mathlib
import RequestProject.XiProductMultOrder
import RequestProject.XiHadamardQuotient

/-!
# H5: entire zero-free analytic continuation of `riemannXi / xiProductMult`

Uses Mathlib's `toMeromorphicNFOn` machinery to produce the canonical
normal-form representative of `fun z ↦ riemannXi z / xiProductMult z`. By
order matching (H3.6), `meromorphicOrderAt` is `0` at every nontrivial
zero, hence the normal form is analytic everywhere. Trailing-coefficient
ratio nonzero gives zero-free.

Avoids the Lean `0/0 = 0` issue at nontrivial zeros: `toMeromorphicNFOn`
chooses analytic values at singularities.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

/-- **Entire zero-free continuation** of `riemannXi / xiProductMult` via
Mathlib's normal-form representative. -/
def xiOverP : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => riemannXi z / xiProductMult z) Set.univ

/-- The literal ratio is meromorphic (entire / entire). -/
theorem ratio_meromorphicOn :
    MeromorphicOn (fun z => riemannXi z / xiProductMult z) Set.univ := by
  apply MeromorphicOn.fun_div
  · exact (riemannXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  · exact (xiProductMult_differentiable.differentiableOn.analyticOnNhd
      isOpen_univ).meromorphicOn

/-- xiOverP is in meromorphic normal form on ℂ. -/
theorem xiOverP_meromorphicNFOn : MeromorphicNFOn xiOverP Set.univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

/-- xiOverP equals the literal ratio on a codiscrete set (i.e., off a
nowhere-dense set, in particular off NontrivialZeros). -/
theorem xiOverP_eq_ratio_codiscretely :
    (fun z => riemannXi z / xiProductMult z) =ᶠ[codiscreteWithin Set.univ] xiOverP :=
  toMeromorphicNFOn_eqOn_codiscrete ratio_meromorphicOn

/-- Order of the literal ratio at any z = order of ξ - order of xiProductMult.
At nontrivial zeros, this is 0 by order matching (H3.6). At other points,
ratio of analytic functions with denom nonzero gives order 0. -/
theorem ratio_meromorphicOrderAt_eq_zero (z : ℂ) :
    meromorphicOrderAt (fun w => riemannXi w / xiProductMult w) z = 0 := by
  have h_anal_xi : AnalyticAt ℂ riemannXi z :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ _)
  have h_anal_P : AnalyticAt ℂ xiProductMult z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable) z
      (Set.mem_univ _)
  -- Orders of ξ and xiProductMult coincide at every z.
  have h_orders : analyticOrderAt riemannXi z = analyticOrderAt xiProductMult z := by
    by_cases hz : z ∈ NontrivialZeros
    · -- Both equal `xiOrderNat z`: ξ by definition of `xiOrderNat`, `xiProductMult` by H3.6.
      have hxi_def : analyticOrderAt riemannXi z = (ZD.xiOrderNat z : ℕ∞) := by
        unfold ZD.xiOrderNat analyticOrderNatAt
        exact (ENat.coe_toNat (ZD.riemannXi_analyticOrderAt_ne_top_everywhere z)).symm
      have hP_def := ZD.analyticOrderAt_xiProductMult_eq_xiOrderNat hz
      rw [hxi_def, hP_def]
    · -- Off the zero set, both are nonzero hence the analytic order is 0.
      have h_xi_ne : riemannXi z ≠ 0 := fun h => hz ((ZD.riemannXi_eq_zero_iff z).mp h)
      have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hz
      rw [h_anal_xi.analyticOrderAt_eq_zero.mpr h_xi_ne,
          h_anal_P.analyticOrderAt_eq_zero.mpr h_P_ne]
  have h_xi_ne_top : analyticOrderAt riemannXi z ≠ ⊤ :=
    ZD.riemannXi_analyticOrderAt_ne_top_everywhere z
  have h_P_ne_top : analyticOrderAt xiProductMult z ≠ ⊤ := h_orders ▸ h_xi_ne_top
  rw [fun_meromorphicOrderAt_div h_anal_xi.meromorphicAt h_anal_P.meromorphicAt,
      h_anal_xi.meromorphicOrderAt_eq, h_anal_P.meromorphicOrderAt_eq, h_orders]
  have ha : analyticOrderAt xiProductMult z =
      ((analyticOrderAt xiProductMult z).toNat : ℕ∞) :=
    (ENat.coe_toNat h_P_ne_top).symm
  rw [ha]
  simp

/-- xiOverP is analytic at every z. -/
theorem xiOverP_analyticAt (z : ℂ) : AnalyticAt ℂ xiOverP z := by
  have h_nf : MeromorphicNFAt xiOverP z := xiOverP_meromorphicNFOn (Set.mem_univ z)
  rcases meromorphicNFAt_iff_analyticAt_or.mp h_nf with h | ⟨_, h_lt, _⟩
  · exact h
  · -- Order < 0 case impossible: meromorphicOrderAt xiOverP z = meromorphicOrderAt (ratio) z = 0.
    exfalso
    -- Codiscrete equality ⟹ punctured-nhds equality.
    have h_codisc := xiOverP_eq_ratio_codiscretely
    have h_punct : (fun w => riemannXi w / xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ] xiOverP := by
      have h_mem : {w | (fun w => riemannXi w / xiProductMult w) w = xiOverP w} ∈
          codiscreteWithin (Set.univ : Set ℂ) := h_codisc
      rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
      have := h_mem z (Set.mem_univ z)
      simp only [Set.compl_univ, Set.union_empty] at this
      exact this
    have h_order_eq : meromorphicOrderAt xiOverP z =
        meromorphicOrderAt (fun w => riemannXi w / xiProductMult w) z :=
      meromorphicOrderAt_congr h_punct.symm
    rw [h_order_eq, ratio_meromorphicOrderAt_eq_zero] at h_lt
    exact absurd h_lt (by norm_num)

/-- xiOverP is differentiable everywhere. -/
theorem xiOverP_differentiable : Differentiable ℂ xiOverP :=
  fun z => (xiOverP_analyticAt z).differentiableAt

/-- **xiOverP is zero-free**. Since `xiOverP` is in meromorphic normal form and its
order at every point is 0 (from `ratio_meromorphicOrderAt_eq_zero` transported via
codiscrete equality), `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` gives
nonvanishing. -/
theorem xiOverP_ne_zero (z : ℂ) : xiOverP z ≠ 0 := by
  have h_nf : MeromorphicNFAt xiOverP z := xiOverP_meromorphicNFOn (Set.mem_univ z)
  -- meromorphicOrderAt xiOverP z = meromorphicOrderAt (ratio) z = 0.
  have h_codisc := xiOverP_eq_ratio_codiscretely
  have h_punct : (fun w => riemannXi w / xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ] xiOverP := by
    have h_mem : {w | (fun w => riemannXi w / xiProductMult w) w = xiOverP w} ∈
        codiscreteWithin (Set.univ : Set ℂ) := h_codisc
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    have := h_mem z (Set.mem_univ z)
    simp only [Set.compl_univ, Set.union_empty] at this
    exact this
  have h_order_eq : meromorphicOrderAt xiOverP z =
      meromorphicOrderAt (fun w => riemannXi w / xiProductMult w) z :=
    meromorphicOrderAt_congr h_punct.symm
  rw [ratio_meromorphicOrderAt_eq_zero z] at h_order_eq
  exact h_nf.meromorphicOrderAt_eq_zero_iff.mp h_order_eq

end ZD
