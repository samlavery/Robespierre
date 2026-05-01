import Mathlib

/-!
# Cosh-Symmetric Pole Structure

This file provides the infrastructure for reasoning about meromorphic functions
that are symmetric under the cosh-kernel reflection `s ↦ c - s` on connected
open domains.

## Cosh kernel symmetries

The hyperbolic cosine kernel `cosh` has two fundamental symmetries that are
"automatic" — baked into its analytic structure:

1. **Re-axis reflection (evenness)**: `cosh(z) = cosh(−z)`, the even-function
   property. This gives the reflection `s ↦ −s` (or `s ↦ c − s` when anchored
   at `c/2`).

2. **Im = 0 fold (conjugate symmetry)**: `cosh(z̄) = conj(cosh(z))`, which
   follows from `cosh` having real Taylor coefficients. This is the Schwarz
   reflection principle applied to the real axis.

Together these symmetries force zeros of cosh-based kernels to appear in
balanced quartets (or pairs on the symmetry axes).

## Main definitions

- `CoshSymmetric c U`: the set `U` is invariant under `s ↦ c - s`.

## Main results

- `cosh_symmetric_pole_structure`: if a meromorphic function `f` on a connected
  open domain `U` satisfies `f(s) = f(c - s)` on a nonempty open subset `V ⊆ U`,
  then the meromorphic order of `f` at any `z ∈ U` equals its order at `c - z`.
-/

open Complex Set Metric Filter Topology

noncomputable section

/-- A set `U ⊆ ℂ` is **cosh-symmetric** with respect to `c` if it is invariant
under the reflection `s ↦ c - s`. This is the set-level symmetry induced by
the cosh kernel's evenness when anchored at `c/2`. -/
def CoshSymmetric (c : ℂ) (U : Set ℂ) : Prop :=
  ∀ s ∈ U, c - s ∈ U

/-- The cosh reflection map `s ↦ c - s` is an involution. -/
lemma cosh_reflect_involution (c s : ℂ) : c - (c - s) = s := by ring

/-- A meromorphic function that agrees with its cosh reflection on a nonempty
open subset of a connected open domain must have the same meromorphic order
at reflected points throughout the domain.

This captures the "automatic fold" property: once the reflection identity
`f(s) = f(c - s)` is verified on any nonempty open seed region, analytic
continuation forces the meromorphic order symmetry globally. -/
theorem cosh_symmetric_pole_structure
    (f : ℂ → ℂ) (c : ℂ) (U V : Set ℂ)
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hU_sym : CoshSymmetric c U)
    (hV_open : IsOpen V) (hV_sub : V ⊆ U) (hV_ne : V.Nonempty)
    (hf_mero : MeromorphicOn f U)
    (hf_sym : ∀ s ∈ V, f s = f (c - s))
    (z : ℂ) (hz : z ∈ U) :
    meromorphicOrderAt f z = meromorphicOrderAt f (c - z) := by
  let g : ℂ → ℂ := fun s => f (c - s)
  have hg_mero : MeromorphicOn g U := by
    intro s hs
    have h1 : MeromorphicAt f (c - s) := hf_mero (c - s) (hU_sym s hs)
    have h2 : AnalyticAt ℂ (fun w => c - w) s := analyticAt_const.sub analyticAt_id
    exact h1.comp_analyticAt h2
  let S := {w ∈ U | f =ᶠ[𝓝[≠] w] g}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hwU : w ∈ U := hw.1
    have hw_eq : f =ᶠ[𝓝[≠] w] g := hw.2
    have h_eventually : ∀ᶠ x in 𝓝 w, x ≠ w → f x = g x := eventually_nhdsWithin_iff.mp hw_eq
    rcases (nhds_basis_opens w).mem_iff.mp h_eventually with ⟨W, ⟨hwW, hW_open⟩, hW_sub⟩
    let O := U ∩ W
    have hO_open : IsOpen O := hU_open.inter hW_open
    have hwO : w ∈ O := ⟨hwU, hwW⟩
    have h_eq_on_O : ∀ x ∈ O, x ≠ w → f x = g x := fun x hx hxw => hW_sub hx.2 hxw
    have h_O_sub_S : O ⊆ S := by
      intro v hv
      refine ⟨hv.1, ?_⟩
      by_cases hvw : v = w
      · rwa [hvw]
      · have hv_in_diff : v ∈ O \ {w} := ⟨hv, hvw⟩
        have h_diff_open : IsOpen (O \ {w}) := hO_open.sdiff isClosed_singleton
        have h_mem_nhds : O \ {w} ∈ 𝓝 v := h_diff_open.mem_nhds hv_in_diff
        filter_upwards [nhdsWithin_le_nhds h_mem_nhds] with x hx
        exact h_eq_on_O x hx.1 hx.2
    exact Filter.mem_of_superset (hO_open.mem_nhds hwO) h_O_sub_S
  have h_clos_sub : closure S ∩ U ⊆ S := by
    rintro w ⟨hw_clos, hwU⟩
    have hw_mero_f : MeromorphicAt f w := hf_mero w hwU
    have hw_mero_g : MeromorphicAt g w := hg_mero w hwU
    by_cases hwS : w ∈ S
    · exact hwS
    · have h_freq : ∃ᶠ x in 𝓝[≠] w, f x = g x := by
        rw [frequently_iff]
        intro W hW
        have h_exists_O : ∃ O, IsOpen O ∧ w ∈ O ∧ O \ {w} ⊆ W := by
          have := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW
          rcases this with ⟨V', hV_nhds, hV_sub⟩
          rcases (nhds_basis_opens w).mem_iff.mp hV_nhds with ⟨O, ⟨hwO, hO_open⟩, hO_sub⟩
          exact ⟨O, hO_open, hwO, subset_trans (diff_subset_diff_left hO_sub) hV_sub⟩
        rcases h_exists_O with ⟨O, hO_open, hwO, hO_sub⟩
        have h_int : (O ∩ S).Nonempty := by
          rw [mem_closure_iff_nhds] at hw_clos
          exact hw_clos O (hO_open.mem_nhds hwO)
        rcases h_int with ⟨y, hyO, hyS⟩
        have hy_neq : y ≠ w := by rintro rfl; exact hwS hyS
        have hy_in_diff : y ∈ O \ {w} := ⟨hyO, hy_neq⟩
        have hy_eq_ev : f =ᶠ[𝓝[≠] y] g := hyS.2
        have h_diff_open : IsOpen (O \ {w}) := hO_open.sdiff isClosed_singleton
        have hy_nhds : O \ {w} ∈ 𝓝 y := h_diff_open.mem_nhds hy_in_diff
        have hy_nhds_ne : O \ {w} ∈ 𝓝[≠] y := nhdsWithin_le_nhds hy_nhds
        have h_ev_and : ∀ᶠ x in 𝓝[≠] y, x ∈ O \ {w} ∧ f x = g x :=
          (eventually_of_mem hy_nhds_ne (fun x hx => hx)).and hy_eq_ev
        rcases h_ev_and.exists with ⟨x, hx_in, hx_eq⟩
        exact ⟨x, hO_sub hx_in, hx_eq⟩
      have h_ev : f =ᶠ[𝓝[≠] w] g := (MeromorphicAt.frequently_eq_iff_eventuallyEq hw_mero_f hw_mero_g).mp h_freq
      exact ⟨hwU, h_ev⟩
  have h_int_ne : (U ∩ S).Nonempty := by
    rcases hV_ne with ⟨v, hvV⟩
    have hvU : v ∈ U := hV_sub hvV
    have hv_nhds : V ∈ 𝓝 v := hV_open.mem_nhds hvV
    have hv_nhds_ne : V ∈ 𝓝[≠] v := nhdsWithin_le_nhds hv_nhds
    have hv_eq_ev : f =ᶠ[𝓝[≠] v] g := eventually_of_mem hv_nhds_ne (fun x hx => hf_sym x hx)
    exact ⟨v, hvU, hvU, hv_eq_ev⟩
  have h_U_sub_S : U ⊆ S := hU_conn.subset_of_closure_inter_subset hS_open h_int_ne h_clos_sub
  have hf_eq : f =ᶠ[𝓝[≠] z] g := (h_U_sub_S hz).2
  have h1 : meromorphicOrderAt f z = meromorphicOrderAt g z :=
    meromorphicOrderAt_congr hf_eq
  have hg_an : AnalyticAt ℂ (fun s => c - s) z := analyticAt_const.sub analyticAt_id
  have hg_deriv : deriv (fun s => c - s) z ≠ 0 := by
    have : HasDerivAt (fun s => c - s) (-1) z := (hasDerivAt_id z).neg.const_add c
    rw [this.deriv]; norm_num
  have h2 : meromorphicOrderAt g z = meromorphicOrderAt f (c - z) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero hg_an hg_deriv
  exact h1.trans h2

end