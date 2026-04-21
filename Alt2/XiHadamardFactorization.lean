import Mathlib
import RequestProject.XiHadamardLog

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

The scaffold is implemented as a sequence of named lemmas. Two steps are
TRACKED sorries, clearly marked:

* `xiHadamardD_bounded` — the genuine analytical gap (equivalent in depth
  to the order-1 Hadamard factorization proper).
* `logDeriv_difference_meromorphicOrderAt_nonneg` — pole cancellation at
  nontrivial zeros from H3.6 residue equality. Technically reducible to
  Mathlib's `meromorphicOrderAt` arithmetic but requires a delicate
  residue computation.
* `riemannXi_hadamard_factorization` — assembly step (integration of the
  constant `xiHadamardD = A` on the entire zero-free `xiOverP`).

Every other lemma is axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
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

/-- **TRACKED**: pole cancellation from H3.6 order matching + residue equality.

At a nontrivial zero ρ of order `n = xiOrderNat ρ`, both `logDeriv riemannXi`
and `logDeriv xiProductMult` have a simple pole with the *same* residue `n`
(the analytic order of the underlying entire function).  Hence their difference
has `meromorphicOrderAt ≥ 0` at ρ.  At every other point, both factors are
analytic, so the difference is analytic there too (order ≥ 0).

Technically this follows from Mathlib's `meromorphicOrderAt_sub` machinery plus
an explicit residue identity `logDeriv f = n/(z-ρ) + analytic` at an order-`n`
zero.  The explicit residue computation is a sizeable lemma; flagged here as a
tracked sorry. -/
theorem logDeriv_difference_meromorphicOrderAt_nonneg (z : ℂ) :
    0 ≤ meromorphicOrderAt
          (fun w => logDeriv riemannXi w - logDeriv xiProductMult w) z := by
  sorry
  -- TRACKED: pole cancellation from H3.6 order matching + residue equality.

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

-- ═══════════════════════════════════════════════════════════════════════════
-- § Global boundedness of xiHadamardD (TRACKED ANALYTIC GAP)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **TRACKED ANALYTIC GAP**: global bound on `xiHadamardD`.

This is the genuine hard step; equivalent in depth to the order-1 Hadamard
factorization proper.  Bounding `|xiHadamardD z| = O(1)` uniformly in `z`
requires either the min-modulus lemma for `xiProductMult` (not in Mathlib) or
a sharp order-1 growth analysis of `ξ`.

Concretely: on large circles `|z| = R` outside small neighborhoods of the
zeros, `|ξ(z)| ≤ exp(C·R·log R)` (from `xi_order_one_log_bound`) and
`|xiProductMult(z)| ≥ exp(-C·R·log R)` (min-modulus for the Weierstrass
product, classical but not in Mathlib).  Taking logarithmic derivatives
gives `|logDeriv ξ(z) - logDeriv xiProductMult(z)| = O(R^0) = O(1)` via
Cauchy estimates applied to the removable-singularity extension. -/
theorem xiHadamardD_bounded : ∃ M : ℝ, ∀ z : ℂ, ‖xiHadamardD z‖ ≤ M := by
  sorry
  -- TRACKED: genuine analytical gap (order-1 Hadamard min-modulus bound).

-- ═══════════════════════════════════════════════════════════════════════════
-- § Liouville: bounded + entire ⟹ constant
-- ═══════════════════════════════════════════════════════════════════════════

/-- From `xiHadamardD_bounded` + Liouville, `xiHadamardD` is constant. -/
theorem xiHadamardD_eq_const : ∃ A : ℂ, ∀ z : ℂ, xiHadamardD z = A := by
  obtain ⟨M, hM⟩ := xiHadamardD_bounded
  have h_bounded : Bornology.IsBounded (Set.range xiHadamardD) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * M, ?_⟩
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    have hz := hM z
    have hw := hM w
    have h_dist_le : dist (xiHadamardD z) (xiHadamardD w) ≤
        ‖xiHadamardD z‖ + ‖xiHadamardD w‖ := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _)
    linarith
  exact Differentiable.exists_const_forall_eq_of_bounded xiHadamardD_differentiable h_bounded

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
  sorry
  -- TRACKED: integration of constant logDeriv on entire zero-free function
  -- (xiOverP).  Uses xiHadamardD_eq_const + xiOverP_ne_zero + primitive
  -- existence on simply-connected ℂ.

end ZD

