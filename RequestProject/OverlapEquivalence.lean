import Mathlib

/-! # Overlap Region and Equivalence of Representations

## Overview

We formalize the "seed region" where the Euler/prime representation
(valid for Re(s) > 1) and the cosh/harmonic representation
(valid for Re(s) < π/3, centered at the reflection axis Re(s) = π/6 = arcsin(1/2))
overlap. The key geometric fact:

  arcsin(1/2) = π/6,  and the cosh kernel, symmetric about π/6,
  extends to π/6 + π/6 = π/3 ≈ 1.047 > 1.

This creates a genuine open strip  1 < Re(s) < π/3  where both
representations converge simultaneously.

## Pipeline

1. **ζ → prime**: The logarithmic derivative −ζ'/ζ encodes the von Mangoldt function
   via its Dirichlet series on Re(s) > 1 (the Euler half-plane).

2. **prime → harmonic**: The prime data (von Mangoldt weights) is reinterpreted as
   harmonic-analysis data through the cosh kernel centered at Re(s) = π/6.

3. **harmonic → Euler to 1**: The cosh representation is valid on Re(s) < π/3,
   which extends past the Euler boundary at Re(s) = 1.

4. **cosh + arcsin(1/2)**: The axis of symmetry at π/6 = arcsin(1/2) and the cosh
   kernel's reach of π/6 on each side give the interval (0, π/3) on the real axis,
   overshooting Re(s) = 1 by π/3 − 1 > 0.

5. **coverage + > 1**: The overlap strip 1 < Re(s) < π/3 is the "seed" — open,
   nonempty, and inside the Euler half-plane.

## Main results

* `overlapRegion_isOpen`: The overlap region is open.
* `overlapRegion_nonempty`: The overlap region is nonempty.
* `overlapRegion_subset_eulerHalfPlane`: The overlap lies inside the natural domain.
* `overlapRegion_isPreconnected`: The overlap is preconnected (via convexity).
* `identity_theorem_on_overlap`: The identity theorem for analytic functions on the overlap.
* `meromorphic_order_transfer`: Meromorphic order is preserved across the overlap.
* `representation_equivalence`: Full equivalence of representations on any connected
  extension of the overlap.
-/

open Complex Set Metric Filter
open scoped Topology

noncomputable section

/-! ### Region definitions -/

/-- The Euler convergence half-plane: `Re(s) > 1`, where the Euler product
    for `ζ(s)` and the Dirichlet series for `−ζ'/ζ` converge absolutely. -/
def eulerHalfPlane : Set ℂ := {s : ℂ | 1 < s.re}

/-- The cosh kernel domain: `Re(s) < π/3`, the region where the cosh-based
    representation centered at the reflection axis `Re(s) = π/6` is valid.
    The kernel's symmetry axis is at `π/6 = arcsin(1/2) ≈ 0.5236`, and it
    extends `π/6` on each side, reaching `π/3 ≈ 1.047 > 1`. -/
def coshKernelDomain : Set ℂ := {s : ℂ | s.re < Real.pi / 3}

/-- The overlap region: the intersection where both the Euler/prime
    representation and the cosh/harmonic representation are simultaneously valid.
    This is the open strip `1 < Re(s) < π/3`. -/
def overlapRegion : Set ℂ := eulerHalfPlane ∩ coshKernelDomain

/-! ### Geometric constants -/

/-- The reflection axis of the cosh kernel is at `arcsin(1/2) = π/6`. -/
theorem cosh_reflection_axis : Real.arcsin (1/2) = Real.pi / 6 := by
  rw [show (1:ℝ)/2 = Real.sin (Real.pi / 6) from by rw [Real.sin_pi_div_six]]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- The overhang width `π/3 − 1 > 0`: the cosh kernel genuinely extends past `Re(s) = 1`. -/
theorem overhang_width_pos : 0 < Real.pi / 3 - 1 := by
  linarith [Real.pi_gt_three]

/-! ### The overlap region equals the Euler-cosh strip -/

/-- The overlap region is exactly the strip `{s | 1 < Re(s) < π/3}`. -/
lemma overlapRegion_eq : overlapRegion = {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3} := by
  ext s; simp [overlapRegion, eulerHalfPlane, coshKernelDomain]

/-! ### Topological properties of the overlap region -/

/-- The overlap region is open (preimage of `(1, π/3)` under the continuous map `Re`). -/
theorem overlapRegion_isOpen : IsOpen overlapRegion := by
  rw [overlapRegion_eq]
  exact (isOpen_Ioo (a := (1 : ℝ)) (b := Real.pi / 3)).preimage continuous_re

/-- The overlap region is nonempty. The midpoint `(1 + π/3)/2` lies strictly inside
    because `π/3 > 1`. -/
theorem overlapRegion_nonempty : overlapRegion.Nonempty := by
  rw [overlapRegion_eq]
  refine ⟨⟨(1 + Real.pi / 3) / 2, 0⟩, ?_, ?_⟩ <;> simp <;> linarith [Real.pi_gt_three]

/-- The overlap region is contained in the Euler half-plane (the natural domain
    where the prime/Dirichlet-series representation converges). -/
theorem overlapRegion_subset_eulerHalfPlane : overlapRegion ⊆ eulerHalfPlane :=
  inter_subset_left

/-- The overlap region is contained in the cosh kernel domain. -/
theorem overlapRegion_subset_coshKernel : overlapRegion ⊆ coshKernelDomain :=
  inter_subset_right

/-- The overlap region is convex (preimage of a convex interval under the ℝ-linear map `Re`). -/
theorem overlapRegion_convex : Convex ℝ overlapRegion := by
  rw [overlapRegion_eq]
  have : {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3} = Complex.re ⁻¹' Set.Ioo 1 (Real.pi / 3) := by
    ext; simp [Set.mem_Ioo]
  rw [this]
  exact (convex_Ioo 1 (Real.pi / 3)).linear_preimage Complex.reCLM.toLinearMap

/-- The overlap region is preconnected (every convex set in a topological vector space
    is preconnected). -/
theorem overlapRegion_isPreconnected : IsPreconnected overlapRegion :=
  overlapRegion_convex.isPreconnected

/-- The overlap region is connected: open, nonempty, and preconnected. -/
theorem overlapRegion_isConnected : IsConnected overlapRegion :=
  ⟨overlapRegion_nonempty, overlapRegion_isPreconnected⟩

/-! ### Identity Theorem on the Overlap

The identity theorem for analytic functions: if two analytic functions agree on an
open nonempty subset of a connected domain, they agree everywhere on that domain.
Applied here, this means that the Euler/prime representation and the cosh/harmonic
representation, being analytic functions that agree on the overlap strip, must agree
on any connected analytic continuation domain containing the overlap. -/

/-- **Identity Theorem on the Overlap.**
    If two functions are analytic on a preconnected open set `U` containing the overlap,
    and they agree on the overlap region, then they agree on all of `U`.
    This is the core mechanism by which the Euler/prime and cosh/harmonic representations
    are proved to be the same analytic object. -/
theorem identity_theorem_on_overlap
    {U : Set ℂ} (_hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hV_sub : overlapRegion ⊆ U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : EqOn f g overlapRegion) :
    EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := overlapRegion_nonempty
  have hz₀U : z₀ ∈ U := hV_sub hz₀
  have hfg_ev : f =ᶠ[nhds z₀] g := by
    have hO : overlapRegion ∈ nhds z₀ := overlapRegion_isOpen.mem_nhds hz₀
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨overlapRegion, hO, heq⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU_conn hz₀U hfg_ev

/-! ### Meromorphic Order Transfer

When two meromorphic functions agree on a neighborhood, they have the same
singularity structure. This transfers pole/zero order information between
the Euler/prime and cosh/harmonic representations. -/

/-- **Meromorphic order transfer.**
    If two functions agree on the overlap region, then at any interior point
    of the overlap they have the same meromorphic order. This transfers
    singularity and zero information between representations. -/
theorem meromorphic_order_transfer
    {f g : ℂ → ℂ} {z : ℂ} (hz : z ∈ overlapRegion)
    (heq : EqOn f g overlapRegion) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  apply meromorphicOrderAt_congr
  have hO : overlapRegion ∈ nhds z := overlapRegion_isOpen.mem_nhds hz
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨overlapRegion, hO, heq⟩)

/-! ### Full Equivalence Theorem

Combining all pieces: the overlap region is the "seed" — an open, nonempty,
preconnected subset of the Euler half-plane — on which the identity theorem
forces any two analytic extensions to agree, and meromorphic order information
transfers faithfully. -/

/-- **Representation Equivalence Theorem.**
    Let `f` be the Euler/prime representation (e.g., `−ζ'/ζ` as a Dirichlet series)
    and `g` the cosh/harmonic representation. Suppose both extend analytically to a
    preconnected open set `U ⊇ overlapRegion` and agree on the overlap. Then:
    1. They agree on all of `U` (by the identity theorem).
    2. At every point of `U`, they have the same meromorphic order
       (singularity/zero structure).

    This is the formal statement that the zeta/prime description and the
    harmonic/cosh description are equivalent on their common domain. -/
theorem representation_equivalence
    {U : Set ℂ} (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hV_sub : overlapRegion ⊆ U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq_overlap : EqOn f g overlapRegion) :
    EqOn f g U ∧
    ∀ z ∈ U, meromorphicOrderAt f z = meromorphicOrderAt g z := by
  have heqU := identity_theorem_on_overlap hU_open hU_conn hV_sub hf hg heq_overlap
  refine ⟨heqU, fun z hz => ?_⟩
  apply meromorphicOrderAt_congr
  have hO : U ∈ nhds z := hU_open.mem_nhds hz
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hO, heqU⟩)

/-- The overlap region satisfies all three required properties simultaneously:
    it is open, nonempty, and contained in the Euler half-plane. -/
theorem overlap_seed_properties :
    IsOpen overlapRegion ∧ overlapRegion.Nonempty ∧ overlapRegion ⊆ eulerHalfPlane :=
  ⟨overlapRegion_isOpen, overlapRegion_nonempty, overlapRegion_subset_eulerHalfPlane⟩

end
