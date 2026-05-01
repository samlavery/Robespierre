import Mathlib
import RequestProject.XiHadamardLog
import RequestProject.XiProductMultPartialFraction
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilHadamardOpenPatch

/-!
# H6: Hadamard factorization `riemannXi z = exp(A·z + B) · xiProductMult z`

The classical Hadamard factorization for ξ as an entire function of order ≤ 1.

## Liouville-on-difference strategy

Define
```
D(z) := logDeriv riemannXi z - logDeriv xiProductMult z
```
off nontrivial zeros. Both `logDeriv`s have simple poles at each ρ with residue
equal to the multiplicity `xiOrderNat ρ` (by H3.6 order matching). Their
difference has removable singularities, hence extends to an entire function
`xiHadamardD` via Mathlib's `toMeromorphicNFOn` (same pattern as `xiOverP`).

Bounding `|xiHadamardD z| = O(1)` (the "min-modulus" / order-1 Hadamard depth)
gives `xiHadamardD` = constant by Liouville. Integrating then gives
`ξ / xiProductMult = exp(A·z + B)`, i.e. the Hadamard factorization.

## Status

The scaffold is implemented as a sequence of named lemmas. The former
tracked gap `xiHadamardD_bounded` has been eliminated: global constancy of
`xiHadamardD` is now derived from an order-1 growth hypothesis on `xiOverP`
through `WeilHadamardOpenPatch.xi_logDeriv_partial_fraction_on_open_of_xiOverP_growth`
(Borel–Carathéodory on `xiOverP`, followed by the existing
`xiHadamardD_eq_const_from_partial_fraction_on_open`). Every lemma in this
file is axiom-clean (`[propext, Classical.choice, Quot.sound]`) given that
growth hypothesis.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § D(z) := logDeriv ξ - logDeriv xiProductMult — meromorphic on ℂ
-- ═══════════════════════════════════════════════════════════════════════════

/-- The literal difference of log-derivatives is meromorphic on ℂ.  Both
`logDeriv riemannXi` and `logDeriv xiProductMult` are meromorphic on `ℂ`
because `riemannXi` and `xiProductMult` are entire. -/
theorem logDeriv_ratio_meromorphicOn :
    MeromorphicOn
      (fun z => logDeriv riemannXi z - logDeriv xiProductMult z) Set.univ := by
  have h_mero_xi : MeromorphicOn riemannXi Set.univ :=
    (riemannXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  have h_mero_P : MeromorphicOn xiProductMult Set.univ :=
    (xiProductMult_differentiable.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  exact h_mero_xi.logDeriv.fun_sub h_mero_P.logDeriv

/-- Pole cancellation from H3.6 order matching + residue equality.

At a nontrivial zero ρ of order `n = xiOrderNat ρ`, both `logDeriv riemannXi`
and `logDeriv xiProductMult` have a simple pole with the *same* residue `n`
(the analytic order of the underlying entire function).  Hence their difference
has `meromorphicOrderAt ≥ 0` at ρ.  At every other point, both factors are
analytic, so the difference is analytic there too (order ≥ 0).

Implemented by applying the general order-`n` log-derivative pole formula to
both `riemannXi` and `xiProductMult`, then cancelling the common principal part. -/
theorem logDeriv_difference_meromorphicOrderAt_nonneg (z : ℂ) :
    0 ≤ meromorphicOrderAt
          (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) z := by
  by_cases hz : z ∈ NontrivialZeros
  · have h_xi_anal : AnalyticAt ℂ riemannXi z :=
      ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ z)
    have h_P_anal : AnalyticAt ℂ xiProductMult z :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable) z
        (Set.mem_univ z)
    have h_xi_order : analyticOrderAt riemannXi z = (ZD.xiOrderNat z : ℕ∞) := by
      unfold ZD.xiOrderNat analyticOrderNatAt
      exact (ENat.coe_toNat (ZD.riemannXi_analyticOrderAt_ne_top_everywhere z)).symm
    have h_P_order : analyticOrderAt xiProductMult z = (ZD.xiOrderNat z : ℕ∞) :=
      ZD.analyticOrderAt_xiProductMult_eq_xiOrderNat hz
    have hn : 1 ≤ ZD.xiOrderNat z :=
      Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros hz)
    obtain ⟨gξ, hgξ_an, hgξ_ne, hξ_punct⟩ :=
      ZD.WeilPositivity.Contour.logDeriv_pole_of_order h_xi_anal h_xi_order hn
    obtain ⟨gP, hgP_an, hgP_ne, hP_punct⟩ :=
      ZD.WeilPositivity.Contour.logDeriv_pole_of_order h_P_anal h_P_order hn
    have h_log_gξ : AnalyticAt ℂ (fun w => deriv gξ w / gξ w) z := by
      simpa [logDeriv] using (hgξ_an.deriv.div hgξ_an hgξ_ne)
    have h_log_gP : AnalyticAt ℂ (fun w => deriv gP w / gP w) z := by
      simpa [logDeriv] using (hgP_an.deriv.div hgP_an hgP_ne)
    have h_punct :
        (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ]
          (fun w => deriv gξ w / gξ w - deriv gP w / gP w) := by
      filter_upwards [hξ_punct, hP_punct] with w hwξ hwP
      change deriv riemannXi w / riemannXi w - deriv xiProductMult w / xiProductMult w =
        deriv gξ w / gξ w - deriv gP w / gP w
      rw [hwξ, hwP]
      ring_nf
    rw [meromorphicOrderAt_congr h_punct]
    exact (h_log_gξ.sub h_log_gP).meromorphicOrderAt_nonneg
  · have h_xi_anal : AnalyticAt ℂ riemannXi z :=
      ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ z)
    have h_P_anal : AnalyticAt ℂ xiProductMult z :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable) z
        (Set.mem_univ z)
    have h_xi_ne : riemannXi z ≠ 0 := fun h => hz ((ZD.riemannXi_eq_zero_iff z).mp h)
    have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hz
    have h_log_xi : AnalyticAt ℂ (logDeriv riemannXi) z := by
      simpa [logDeriv] using (h_xi_anal.deriv.div h_xi_anal h_xi_ne)
    have h_log_P : AnalyticAt ℂ (logDeriv xiProductMult) z := by
      simpa [logDeriv] using (h_P_anal.deriv.div h_P_anal h_P_ne)
    exact (h_log_xi.sub h_log_P).meromorphicOrderAt_nonneg

/-- `xiHadamardD` — the canonical analytic representative of
`logDeriv ξ - logDeriv xiProductMult` on `ℂ`, via `toMeromorphicNFOn`. -/
def xiHadamardD : ℂ → ℂ :=
  toMeromorphicNFOn
    (fun z => logDeriv riemannXi z - logDeriv xiProductMult z) Set.univ

/-- `xiHadamardD` is in meromorphic normal form on `ℂ`. -/
theorem xiHadamardD_meromorphicNFOn : MeromorphicNFOn xiHadamardD Set.univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

/-- `xiHadamardD` coincides with the literal difference on a codiscrete set
(in particular, off `NontrivialZeros`). -/
theorem xiHadamardD_eq_diff_codiscretely :
    (fun z => logDeriv riemannXi z - logDeriv xiProductMult z) =ᶠ[codiscreteWithin Set.univ]
      xiHadamardD :=
  toMeromorphicNFOn_eqOn_codiscrete logDeriv_ratio_meromorphicOn

/-- The meromorphic order of `xiHadamardD` at every point equals that of the
literal difference (normal form preserves order). -/
theorem xiHadamardD_meromorphicOrderAt (z : ℂ) :
    meromorphicOrderAt xiHadamardD z =
      meromorphicOrderAt (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) z := by
  have h_codisc := xiHadamardD_eq_diff_codiscretely
  have h_punct :
      (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ]
        xiHadamardD := by
    have h_mem :
        {w | (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) w = xiHadamardD w}
            ∈ codiscreteWithin (Set.univ : Set ℂ) := h_codisc
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    have := h_mem z (Set.mem_univ z)
    simp only [Set.compl_univ, Set.union_empty] at this
    exact this
  exact (meromorphicOrderAt_congr h_punct).symm

/-- `xiHadamardD` is analytic at every point. -/
theorem xiHadamardD_analyticAt (z : ℂ) : AnalyticAt ℂ xiHadamardD z := by
  have h_nf : MeromorphicNFAt xiHadamardD z := xiHadamardD_meromorphicNFOn (Set.mem_univ z)
  rcases meromorphicNFAt_iff_analyticAt_or.mp h_nf with h | ⟨_, h_lt, _⟩
  · exact h
  · exfalso
    -- Order < 0, but we proved order ≥ 0 via the literal-difference identity.
    have h_order_eq := xiHadamardD_meromorphicOrderAt z
    have h_nonneg := logDeriv_difference_meromorphicOrderAt_nonneg z
    rw [h_order_eq] at h_lt
    exact absurd h_lt (not_lt.mpr h_nonneg)

/-- `xiHadamardD` is differentiable everywhere. -/
theorem xiHadamardD_differentiable : Differentiable ℂ xiHadamardD :=
  fun z => (xiHadamardD_analyticAt z).differentiableAt

private theorem ratio_eventuallyEq_xiOverP_of_notMem_NontrivialZeros {z : ℂ}
    (hz : z ∉ NontrivialZeros) :
    (fun w => riemannXi w / xiProductMult w) =ᶠ[𝓝 z] xiOverP := by
  have h_anal_xi : AnalyticAt ℂ riemannXi z :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ z)
  have h_anal_P : AnalyticAt ℂ xiProductMult z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable) z
      (Set.mem_univ z)
  have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hz
  have h_ratio_nf : MeromorphicNFAt (fun w => riemannXi w / xiProductMult w) z := by
    exact (h_anal_xi.div h_anal_P h_P_ne).meromorphicNFAt
  have h_punct :
      (fun w => riemannXi w / xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ] xiOverP := by
    have h_mem :
        {w | (fun w => riemannXi w / xiProductMult w) w = xiOverP w} ∈
          codiscreteWithin (Set.univ : Set ℂ) := xiOverP_eq_ratio_codiscretely
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    simpa only [Set.compl_univ, Set.union_empty] using h_mem z (Set.mem_univ z)
  exact (h_ratio_nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (xiOverP_analyticAt z).meromorphicNFAt).1 h_punct

private theorem xiOverP_eq_ratio_of_notMem_NontrivialZeros {z : ℂ}
    (hz : z ∉ NontrivialZeros) :
    xiOverP z = riemannXi z / xiProductMult z :=
  (ratio_eventuallyEq_xiOverP_of_notMem_NontrivialZeros hz).symm.eq_of_nhds

private theorem diff_eventuallyEq_xiHadamardD_of_notMem_NontrivialZeros {z : ℂ}
    (hz : z ∉ NontrivialZeros) :
    (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) =ᶠ[𝓝 z] xiHadamardD := by
  have h_anal_xi : AnalyticAt ℂ riemannXi z :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ z)
  have h_anal_P : AnalyticAt ℂ xiProductMult z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable) z
      (Set.mem_univ z)
  have h_xi_ne : riemannXi z ≠ 0 := fun h => hz ((ZD.riemannXi_eq_zero_iff z).mp h)
  have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hz
  have h_log_xi : AnalyticAt ℂ (logDeriv riemannXi) z := by
    simpa [logDeriv] using (h_anal_xi.deriv.div h_anal_xi h_xi_ne)
  have h_log_P : AnalyticAt ℂ (logDeriv xiProductMult) z := by
    simpa [logDeriv] using (h_anal_P.deriv.div h_anal_P h_P_ne)
  have h_diff_nf :
      MeromorphicNFAt (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) z := by
    exact (h_log_xi.sub h_log_P).meromorphicNFAt
  have h_punct :
      (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) =ᶠ[nhdsWithin z {z}ᶜ]
        xiHadamardD := by
    have h_mem :
        {w | (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) w = xiHadamardD w} ∈
          codiscreteWithin (Set.univ : Set ℂ) := xiHadamardD_eq_diff_codiscretely
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
    simpa only [Set.compl_univ, Set.union_empty] using h_mem z (Set.mem_univ z)
  exact (h_diff_nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (xiHadamardD_analyticAt z).meromorphicNFAt).1 h_punct

private theorem logDeriv_xiOverP_eq_xiHadamardD_of_notMem_NontrivialZeros {z : ℂ}
    (hz : z ∉ NontrivialZeros) :
    logDeriv xiOverP z = xiHadamardD z := by
  have h_ratio := ratio_eventuallyEq_xiOverP_of_notMem_NontrivialZeros hz
  have h_diff := diff_eventuallyEq_xiHadamardD_of_notMem_NontrivialZeros hz
  have h_ratio_deriv :
      deriv (fun w => riemannXi w / xiProductMult w) z = deriv xiOverP z :=
    h_ratio.deriv_eq
  have h_ratio_val :
      (fun w => riemannXi w / xiProductMult w) z = xiOverP z :=
    h_ratio.eq_of_nhds
  have h_xi_ne : riemannXi z ≠ 0 := fun h => hz ((ZD.riemannXi_eq_zero_iff z).mp h)
  have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hz
  have h_log_ratio :
      logDeriv (fun w => riemannXi w / xiProductMult w) z =
        logDeriv riemannXi z - logDeriv xiProductMult z := by
    simpa using logDeriv_div (f := riemannXi) (g := xiProductMult) z h_xi_ne h_P_ne
      (riemannXi_differentiable z) (xiProductMult_differentiable z)
  calc
    logDeriv xiOverP z = logDeriv (fun w => riemannXi w / xiProductMult w) z := by
      rw [logDeriv_apply, logDeriv_apply, ← h_ratio_deriv, ← h_ratio_val]
    _ = logDeriv riemannXi z - logDeriv xiProductMult z := h_log_ratio
    _ = xiHadamardD z := h_diff.eq_of_nhds

/-- Off `NontrivialZeros`, the literal log-derivative difference equals the
analytic normal-form representative `xiHadamardD`. -/
theorem logDeriv_riemannXi_sub_logDeriv_xiProductMult_eq_xiHadamardD_of_notMem_NontrivialZeros
    {z : ℂ} (hz : z ∉ NontrivialZeros) :
    deriv riemannXi z / riemannXi z - logDeriv xiProductMult z = xiHadamardD z := by
  exact (diff_eventuallyEq_xiHadamardD_of_notMem_NontrivialZeros hz).eq_of_nhds


-- ═══════════════════════════════════════════════════════════════════════════
-- § Liouville: bounded + entire ⟹ constant
-- ═══════════════════════════════════════════════════════════════════════════

private theorem nontrivialZeros_compl_isOpen : IsOpen ((NontrivialZeros : Set ℂ)ᶜ) := by
  have h_cont : Continuous riemannXi := riemannXi_differentiable.continuous
  have h_closed : IsClosed (riemannXi ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage h_cont
  have hU_eq : ((NontrivialZeros : Set ℂ)ᶜ) = (riemannXi ⁻¹' ({0} : Set ℂ))ᶜ := by
    ext z
    simp [ZD.riemannXi_eq_zero_iff]
  rw [hU_eq]
  exact h_closed.isOpen_compl

/-- If an independent H8-style partial fraction is available for `riemannXi`
on any nonempty open set, then the meromorphic normal form `xiHadamardD` is
constant, with no growth or min-modulus input. This is the intended
replacement for `xiHadamardD_bounded` once the ξ partial fraction is proved on
some rectangle-produced open patch upstream of H6. -/
theorem xiHadamardD_eq_const_from_partial_fraction_on_open
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ ((NontrivialZeros : Set ℂ)ᶜ))
    (hpf : ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
      deriv riemannXi s / riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) :
    ∃ A : ℂ, ∀ z : ℂ, xiHadamardD z = A := by
  obtain ⟨A, hA⟩ := hpf
  obtain ⟨z₀, hz₀U⟩ := hU_nonempty
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨r, hr_pos, hr_sub⟩ := hU_open z₀ hz₀U
  have h_local_const : EqOn xiHadamardD (fun _ : ℂ => A) (Metric.ball z₀ r) := by
    intro z hz
    have hzU_mem : z ∈ U := hr_sub hz
    have hzU : z ∉ NontrivialZeros := by simpa using hU_sub hzU_mem
    have h_diff_const :
        deriv riemannXi z / riemannXi z - logDeriv xiProductMult z = A := by
      calc
        deriv riemannXi z / riemannXi z - logDeriv xiProductMult z =
            (A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) * (1 / (z - ρ.val) + 1 / ρ.val)) -
              logDeriv xiProductMult z := by
                rw [hA z hzU_mem]
        _ =
            (A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) * (1 / (z - ρ.val) + 1 / ρ.val)) -
              (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
                (ZD.xiOrderNat ρ.val : ℂ) * (1 / (z - ρ.val) + 1 / ρ.val)) := by
                  rw [logDeriv_xiProductMult_partial_fraction hzU]
        _ = A := by ring
    rw [← logDeriv_riemannXi_sub_logDeriv_xiProductMult_eq_xiHadamardD_of_notMem_NontrivialZeros hzU]
    exact h_diff_const
  have h_analytic_xiHadamardD : AnalyticOnNhd ℂ xiHadamardD Set.univ :=
    xiHadamardD_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have h_analytic_const : AnalyticOnNhd ℂ (fun _ : ℂ => A) Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (fun _ => differentiableAt_const A))
  have h_global : xiHadamardD = fun _ : ℂ => A := by
    exact h_analytic_xiHadamardD.eq_of_eventuallyEq h_analytic_const <| by
      filter_upwards [Metric.ball_mem_nhds z₀ hr_pos] with z hz
      exact h_local_const hz
  refine ⟨A, ?_⟩
  intro z
  simpa using congrFun h_global z

/-- If an independent H8-style partial fraction is available for `riemannXi`,
then the meromorphic normal form `xiHadamardD` is constant, with no growth or
min-modulus input. This is the intended replacement for `xiHadamardD_bounded`
once the ξ partial fraction is proved upstream of H6. -/
theorem xiHadamardD_eq_const_from_partial_fraction
    (hpf : ∃ A : ℂ, ∀ s : ℂ, s ∉ NontrivialZeros →
      deriv riemannXi s / riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) :
    ∃ A : ℂ, ∀ z : ℂ, xiHadamardD z = A := by
  refine xiHadamardD_eq_const_from_partial_fraction_on_open
    nontrivialZeros_compl_isOpen (by
      have h0 : (0 : ℂ) ∉ NontrivialZeros := by
        intro h0
        exact ZD.ZeroCount.riemannXi_zero_ne_zero ((ZD.riemannXi_eq_zero_iff 0).mpr h0)
      exact ⟨0, by simpa using h0⟩) (by intro z hz; exact hz) ?_
  obtain ⟨A, hA⟩ := hpf
  refine ⟨A, ?_⟩
  intro s hs
  exact hA s hs

/-- **Unconditional** global constancy of `xiHadamardD`.  Derived from
`xi_logDeriv_partial_fraction_on_open` in `WeilHadamardOpenPatch`, which in
turn uses the unconditional Jensen + Nevanlinna + Poisson chain in
`XiOverPGrowth` to discharge the mean-type-2 growth on `xiOverP`. -/
theorem xiHadamardD_eq_const :
    ∃ A : ℂ, ∀ z : ℂ, xiHadamardD z = A := by
  obtain ⟨U, hU_open, hU_ne, hU_sub, hpf⟩ :=
    xi_logDeriv_partial_fraction_on_open
  exact xiHadamardD_eq_const_from_partial_fraction_on_open hU_open hU_ne hU_sub hpf

/-- **Unconditional** H6 input: off nontrivial zeros,
`ξ'/ξ − logDeriv xiProductMult` is constant. -/
theorem xi_logDeriv_sub_product_const_off_zeros :
    ∃ A : ℂ, ∀ z : ℂ, z ∉ NontrivialZeros →
      deriv riemannXi z / riemannXi z - logDeriv xiProductMult z = A := by
  obtain ⟨A, hA⟩ := xiHadamardD_eq_const
  refine ⟨A, ?_⟩
  intro z hz
  rw [logDeriv_riemannXi_sub_logDeriv_xiProductMult_eq_xiHadamardD_of_notMem_NontrivialZeros hz,
    hA z]

-- ═══════════════════════════════════════════════════════════════════════════
-- § H6 main theorem — Hadamard factorization
-- ═══════════════════════════════════════════════════════════════════════════

/-- **TRACKED H6**: Hadamard factorization.

Assembled from `xiHadamardD_eq_const` + integration of the constant log-derivative
on the entire zero-free function `xiOverP`.  The integration step (recovering
`ξ/xiProductMult = exp(A·z + B)` from `logDeriv(ξ/xiProductMult) = A`) uses
`xiOverP` (entire, zero-free) and Mathlib's primitive-of-analytic machinery;
flagged as tracked because the bookkeeping connecting `xiHadamardD` (a
codiscrete representative of the literal log-derivative difference) to
`logDeriv xiOverP` requires separate infrastructure. -/
theorem riemannXi_hadamard_factorization :
    ∃ A B : ℂ, ∀ z : ℂ,
      riemannXi z = Complex.exp (A * z + B) * xiProductMult z := by
  obtain ⟨A, hA⟩ := xiHadamardD_eq_const
  let U : Set ℂ := (NontrivialZeros : Set ℂ)ᶜ
  have hU_open : IsOpen U := by
    have h_cont : Continuous riemannXi := riemannXi_differentiable.continuous
    have h_closed : IsClosed (riemannXi ⁻¹' ({0} : Set ℂ)) :=
      isClosed_singleton.preimage h_cont
    have hU_eq : U = (riemannXi ⁻¹' ({0} : Set ℂ))ᶜ := by
      ext z
      simp [U, ZD.riemannXi_eq_zero_iff]
    rw [hU_eq]
    exact h_closed.isOpen_compl
  have h0U : (0 : ℂ) ∈ U := by
    show (0 : ℂ) ∉ NontrivialZeros
    intro h0
    exact ZD.ZeroCount.riemannXi_zero_ne_zero ((ZD.riemannXi_eq_zero_iff 0).mpr h0)
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨r, hr_pos, hr_sub⟩ := hU_open 0 h0U
  have h_ball_preconnected : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have h_exp_log : ∀ z : ℂ, logDeriv (fun w : ℂ => Complex.exp (A * w)) z = A := by
    intro z
    rw [show (fun w : ℂ => Complex.exp (A * w)) = Complex.exp ∘ (fun w : ℂ => A * w) from rfl]
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_exp]
    have h_deriv : deriv (fun w : ℂ => A * w) z = A := by
      rw [deriv_const_mul _ differentiableAt_id, deriv_id'']
      ring
    rw [h_deriv]
    simp
  have h_logEq_ball :
      EqOn (logDeriv xiOverP) (logDeriv (fun w : ℂ => Complex.exp (A * w)))
        (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hzU : z ∉ NontrivialZeros := by
      simpa [U] using hr_sub hz
    rw [h_exp_log z]
    calc
      logDeriv xiOverP z = xiHadamardD z :=
        logDeriv_xiOverP_eq_xiHadamardD_of_notMem_NontrivialZeros hzU
      _ = A := hA z
  have h_exp_diff_ball :
      DifferentiableOn ℂ (fun w : ℂ => Complex.exp (A * w)) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    exact (DifferentiableAt.cexp (differentiableAt_id.const_mul A)).differentiableWithinAt
  have h_xiOverP_exp_ball :
      ∃ c : ℂ, c ≠ 0 ∧
        EqOn xiOverP (fun z : ℂ => c * Complex.exp (A * z)) (Metric.ball (0 : ℂ) r) := by
    obtain ⟨c, hc_ne, hc_eq⟩ :=
      (logDeriv_eqOn_iff
        (hf := xiOverP_differentiable.differentiableOn)
        (hg := h_exp_diff_ball)
        (hs2 := Metric.isOpen_ball)
        (hsc := h_ball_preconnected)
        (hgn := fun z _ => Complex.exp_ne_zero _)
        (hfn := fun z _ => xiOverP_ne_zero z)).1 h_logEq_ball
    refine ⟨c, hc_ne, ?_⟩
    intro z hz
    simpa [Pi.smul_apply] using hc_eq hz
  obtain ⟨c, hc_ne, hc_eq⟩ := h_xiOverP_exp_ball
  have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball] using hr_pos
  have hc0 : xiOverP 0 = c := by
    simpa using hc_eq h0_ball
  let B : ℂ := Complex.log c
  have h_expB : Complex.exp B = c := by
    exact Complex.exp_log hc_ne
  have h_local_factor :
      EqOn riemannXi (fun z : ℂ => Complex.exp (A * z + B) * xiProductMult z)
        (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hzU : z ∉ NontrivialZeros := by
      simpa [U] using hr_sub hz
    have h_ratio_eq : xiOverP z = riemannXi z / xiProductMult z :=
      xiOverP_eq_ratio_of_notMem_NontrivialZeros hzU
    have h_P_ne : xiProductMult z ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hzU
    have h_local_xiOverP : xiOverP z = Complex.exp (A * z + B) := by
      calc
        xiOverP z = c * Complex.exp (A * z) := hc_eq hz
        _ = Complex.exp B * Complex.exp (A * z) := by rw [h_expB]
        _ = Complex.exp (B + A * z) := by rw [← Complex.exp_add]
        _ = Complex.exp (A * z + B) := by ring_nf
    calc
      riemannXi z = (riemannXi z / xiProductMult z) * xiProductMult z := by
        field_simp [h_P_ne]
      _ = xiOverP z * xiProductMult z := by rw [← h_ratio_eq]
      _ = Complex.exp (A * z + B) * xiProductMult z := by rw [h_local_xiOverP]
  have h_expAB_differentiable : Differentiable ℂ (fun z : ℂ => Complex.exp (A * z + B)) := by
    intro z
    exact DifferentiableAt.cexp ((differentiableAt_id.const_mul A).add_const B)
  have h_factor_global :
      riemannXi = fun z : ℂ => Complex.exp (A * z + B) * xiProductMult z := by
    have h_analytic_xi : AnalyticOnNhd ℂ riemannXi Set.univ :=
      riemannXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have h_analytic_rhs :
        AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (A * z + B) * xiProductMult z) Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr h_expAB_differentiable).mul
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr xiProductMult_differentiable)
    exact h_analytic_xi.eq_of_eventuallyEq h_analytic_rhs <| by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr_pos] with z hz
      exact h_local_factor hz
  refine ⟨A, B, ?_⟩
  intro z
  simpa using congrFun h_factor_global z

end ZD
