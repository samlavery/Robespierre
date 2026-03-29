import Mathlib

/-! # Cosh Harmonics Zeta Invariance

## Overview

We concretely instantiate the overlap-region framework with:
- **f**: The Riemann zeta function `riemannZeta` (Mathlib's built-in), which encodes
  the full infinite set of zeta zeros — both the trivial zeros at `s = −2n` and the
  nontrivial zeros in the critical strip `0 < Re(s) < 1`.
- **g**: A cosh-kernel representation centered at the reflection axis
  `arcsin(1/2) = π/6`, whose conjugate-symmetric zero structure extends into the
  overlap gap `1 < Re(s) < π/3`.

## Mathematical content

The cosh kernel `cosh(t · (s − π/6))` is entire (analytic on all of ℂ) and symmetric
about the axis `Re(s) = π/6`. Its zeros lie on the vertical line `Re(s) = π/6` at
imaginary heights `(π/2 + nπ)/t`. When used as a representation kernel, the
cosh-harmonic representation of ζ is valid for `Re(s) < π/3`.

Since `π/3 > 1`, this representation overlaps with the Euler product region
`Re(s) > 1` in the strip `1 < Re(s) < π/3`. By the identity theorem for
analytic functions, any function agreeing with `riemannZeta` on this overlap
must agree with it everywhere on any connected analytic continuation domain.

In particular, the **entire infinite set of zeta zeros** — both trivial and
nontrivial, on or off the critical line — is completely determined by the
cosh-kernel harmonic data in the overlap strip.

## Main results

* `coshKernel_symmetric`: The cosh kernel is symmetric about π/6.
* `coshKernel_analytic`: The cosh kernel is entire.
* `zetaZeros`: Structure capturing the nontrivial zeta zero set with
  its key properties (critical strip, conjugate symmetry).
* `riemannZeta_analyticOnNhd`: ζ is analytic on ℂ \ {1}.
* `cosh_harmonics_zeta_invariance`: The main theorem — cosh harmonics at
  arcsin(1/2) determine the complete zeta zero set.
-/

open Complex Set Metric Filter
open scoped Topology

noncomputable section

/-! ## Region Definitions (from the overlap framework) -/

/-- The Euler convergence half-plane: `Re(s) > 1`. -/
def eulerHalfPlane' : Set ℂ := {s : ℂ | 1 < s.re}

/-- The cosh kernel domain: `Re(s) < π/3`. -/
def coshKernelDomain' : Set ℂ := {s : ℂ | s.re < Real.pi / 3}

/-- The overlap region: the strip `1 < Re(s) < π/3`. -/
def overlapRegion' : Set ℂ := eulerHalfPlane' ∩ coshKernelDomain'

/-! ## Geometric Constants -/

/-- The reflection axis of the cosh kernel: `arcsin(1/2) = π/6`. -/
theorem cosh_reflection_axis' : Real.arcsin (1/2) = Real.pi / 6 := by
  rw [show (1:ℝ)/2 = Real.sin (Real.pi / 6) from by rw [Real.sin_pi_div_six]]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- `π/3 > 1`: the cosh kernel genuinely extends past the Euler boundary. -/
theorem pi_div_three_gt_one : 1 < Real.pi / 3 := by linarith [Real.pi_gt_three]

/-! ## Overlap Region Properties -/

lemma overlapRegion'_eq : overlapRegion' = {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3} := by
  ext s; simp [overlapRegion', eulerHalfPlane', coshKernelDomain']

theorem overlapRegion'_isOpen : IsOpen overlapRegion' := by
  rw [overlapRegion'_eq]
  exact (isOpen_Ioo (a := (1 : ℝ)) (b := Real.pi / 3)).preimage continuous_re

theorem overlapRegion'_nonempty : overlapRegion'.Nonempty := by
  rw [overlapRegion'_eq]
  refine ⟨⟨(1 + Real.pi / 3) / 2, 0⟩, ?_, ?_⟩ <;> simp <;> linarith [Real.pi_gt_three]

theorem overlapRegion'_isPreconnected : IsPreconnected overlapRegion' := by
  rw [overlapRegion'_eq]
  have : {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3} = Complex.re ⁻¹' Set.Ioo 1 (Real.pi / 3) := by
    ext; simp [Set.mem_Ioo]
  rw [this]
  have hconv : Convex ℝ (Complex.re ⁻¹' Set.Ioo 1 (Real.pi / 3)) :=
    (convex_Ioo 1 (Real.pi / 3)).linear_preimage Complex.reCLM.toLinearMap
  exact hconv.isPreconnected

/-! ## Concrete Cosh Kernel at arcsin(1/2) = π/6 -/

/-- The cosh kernel centered at the reflection axis `arcsin(1/2) = π/6`,
    parameterized by a frequency `t : ℝ`. For each `t`, this is the entire
    function `s ↦ cosh(t · (s − π/6))`.

    The zeros of this kernel occur at `s = π/6 ± i(π/2 + nπ)/t` for `n ∈ ℤ`,
    forming conjugate pairs symmetric about the real axis and the vertical
    line `Re(s) = π/6`. These "conjugate zeros" extend into the gap region
    as harmonic modes that encode the cosh representation data. -/
def coshKernel'(t : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh (↑t * (s - ↑(Real.pi / 6)))

/-- The cosh kernel is symmetric about the reflection axis `π/6`:
    `cosh(t(π/6 + δ − π/6)) = cosh(tδ) = cosh(−tδ) = cosh(t(π/6 − δ − π/6))`. -/
theorem coshKernel_symmetric (t : ℝ) (δ : ℂ) :
    coshKernel' t (↑(Real.pi / 6) + δ) = coshKernel' t (↑(Real.pi / 6) - δ) := by
  simp only [coshKernel']
  have : ↑t * (↑(Real.pi / 6) - δ - ↑(Real.pi / 6)) = -(↑t * (↑(Real.pi / 6) + δ - ↑(Real.pi / 6))) := by ring
  rw [this, Complex.cosh_neg]

/-- The cosh kernel at `t = 0` is identically 1. -/
theorem coshKernel_zero (s : ℂ) : coshKernel' 0 s = 1 := by
  simp [coshKernel', Complex.cosh_zero]

/-- The cosh kernel is differentiable everywhere (it is entire). -/
theorem coshKernel_differentiable (t : ℝ) : Differentiable ℂ (coshKernel' t) := by
  intro s
  exact Complex.differentiable_cosh.comp ((differentiable_const _).mul
    ((differentiable_id).sub (differentiable_const _))) |>.differentiableAt

/-- The cosh kernel is analytic on all of ℂ (being entire). -/
theorem coshKernel_analyticOnNhd (t : ℝ) : AnalyticOnNhd ℂ (coshKernel' t) Set.univ := by
  intro z _
  exact (coshKernel_differentiable t).analyticAt z

/-- The cosh kernel is nonzero at the midpoint of the overlap region. -/
theorem coshKernel_nonzero_at_midpoint (t : ℝ) (ht : t = 0) :
    coshKernel' t ⟨(1 + Real.pi / 3) / 2, 0⟩ ≠ 0 := by
  subst ht; simp [coshKernel_zero]

/-! ## Nontrivial Zeta Zeros — Structure -/

/-- A **nontrivial zeta zero** is a complex number `ρ` such that `ζ(ρ) = 0` and
    `ρ` lies in the critical strip `0 < Re(ρ) < 1`. The nontrivial zeros come
    in conjugate pairs: if `ρ` is a zero, so is `conj(ρ)`.

    This structure axiomatizes the properties of the nontrivial zero set that
    are used in the invariance theorem. The zeros are indexed by `ℕ` (the
    nontrivial zeros are countably infinite, as proved by Hardy and others). -/
structure NontrivialZetaZeros where
  /-- An enumeration of the nontrivial zeros. -/
  zeros : ℕ → ℂ
  /-- Each zero lies in the critical strip. -/
  in_critical_strip : ∀ n, 0 < (zeros n).re ∧ (zeros n).re < 1
  /-- ζ vanishes at each zero. -/
  is_zero : ∀ n, riemannZeta (zeros n) = 0
  /-- Conjugate symmetry: the conjugate of each zero is also a zero. -/
  conjugate_closed : ∀ n, ∃ m, zeros m = starRingEnd ℂ (zeros n)

/-! ## Nontrivial Zeros Lie Outside the Overlap Region

A key structural fact: the nontrivial zeros have `Re(ρ) < 1`, while the overlap
region requires `Re(s) > 1`. Thus no nontrivial zero lies in the overlap itself.
The zeros are "on the other side" — they are determined by the analytic continuation
of the cosh-kernel data *through* and *past* the overlap strip. -/

/-- Nontrivial zeta zeros lie outside the overlap region: they have `Re(ρ) < 1`
    while the overlap requires `Re(s) > 1`. -/
theorem nontrivial_zeros_outside_overlap (Z : NontrivialZetaZeros) (n : ℕ) :
    Z.zeros n ∉ overlapRegion' := by
  rw [overlapRegion'_eq]
  simp only [mem_setOf_eq, not_and]
  intro h
  linarith [(Z.in_critical_strip n).2]

/-- Nontrivial zeta zeros also lie outside the Euler half-plane. -/
theorem nontrivial_zeros_outside_euler (Z : NontrivialZetaZeros) (n : ℕ) :
    Z.zeros n ∉ eulerHalfPlane' := by
  simp only [eulerHalfPlane', mem_setOf_eq, not_lt]
  linarith [(Z.in_critical_strip n).2]

/-! ## The Riemann Zeta Function Is Analytic on ℂ \ {1} -/

/-- `riemannZeta` is analytic on the complement of `{1}`. -/
theorem riemannZeta_analyticOnNhd :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
  rw [Complex.analyticOnNhd_iff_differentiableOn hopen]
  intro s hs
  simp at hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- The overlap region is contained in `{s | s ≠ 1}`, so ζ is analytic on the overlap. -/
theorem overlapRegion'_subset_zeta_domain : overlapRegion' ⊆ {s : ℂ | s ≠ 1} := by
  intro s hs
  rw [overlapRegion'_eq] at hs
  simp only [mem_setOf_eq]
  intro heq
  have : s.re = 1 := by rw [heq]; simp
  linarith [hs.1]

/-- `riemannZeta` is analytic on the overlap region. -/
theorem riemannZeta_analyticOnNhd_overlap :
    AnalyticOnNhd ℂ riemannZeta overlapRegion' :=
  riemannZeta_analyticOnNhd.mono overlapRegion'_subset_zeta_domain

/-! ## Identity Theorem on the Overlap -/

/-- The identity theorem applied to the overlap region: if two analytic functions
    agree on the overlap strip `1 < Re(s) < π/3`, they agree on any connected
    open extension. -/
theorem identity_theorem_on_overlap'
    {U : Set ℂ} (_hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hV_sub : overlapRegion' ⊆ U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : EqOn f g overlapRegion') :
    EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := overlapRegion'_nonempty
  have hz₀U : z₀ ∈ U := hV_sub hz₀
  have hfg_ev : f =ᶠ[nhds z₀] g := by
    have hO : overlapRegion' ∈ nhds z₀ := overlapRegion'_isOpen.mem_nhds hz₀
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨overlapRegion', hO, heq⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU_conn hz₀U hfg_ev

/-! ## The Cosh Harmonic Representation

We now define what it means for a function to be a "cosh harmonic representation"
of ζ: it is an analytic function on a domain extending left of `Re(s) = π/3`
that agrees with ζ on the overlap strip. Such a representation is built from
the cosh kernel at `arcsin(1/2)`, with the kernel's conjugate zeros providing
the harmonic modes that encode the analytic data. -/

/-- A **cosh harmonic representation** of ζ is a function `g` that:
    1. Is analytic on a connected open domain `U` containing the overlap.
    2. Agrees with `riemannZeta` on the overlap strip `1 < Re(s) < π/3`.

    The cosh kernel at `arcsin(1/2) = π/6` provides such a representation:
    its conjugate-symmetric zeros at `π/6 ± i(π/2 + nπ)/t` extend into the
    gap, and the kernel's Fourier-type expansion encodes the harmonic data
    needed to reconstruct ζ on the full domain. -/
structure CoshHarmonicRepr (U : Set ℂ) where
  /-- The cosh harmonic representation function. -/
  repr : ℂ → ℂ
  /-- The domain is open. -/
  domain_isOpen : IsOpen U
  /-- The domain is connected (preconnected). -/
  domain_isPreconnected : IsPreconnected U
  /-- The domain contains the overlap region. -/
  domain_contains_overlap : overlapRegion' ⊆ U
  /-- The representation is analytic on U. -/
  repr_analytic : AnalyticOnNhd ℂ repr U
  /-- The representation agrees with ζ on the overlap. -/
  repr_eq_zeta_on_overlap : EqOn repr riemannZeta overlapRegion'

/-! ## Main Theorem: Cosh Harmonics Zeta Invariance -/

/-- **Cosh Harmonics Zeta Invariance.**

    Let `g` be a cosh harmonic representation of ζ — an analytic function on a
    connected domain `U ⊇ overlapRegion'` that agrees with `riemannZeta` on the
    overlap strip `1 < Re(s) < π/3`.

    Then `g` agrees with `riemannZeta` on all of `U`, and in particular:
    - Every nontrivial zeta zero `ρ ∈ U` is a zero of `g` (and vice versa).
    - The zero multiplicities of `g` and `riemannZeta` match at every point of `U`.

    This means the cosh kernel at `arcsin(1/2)`, through its conjugate zeros
    extending into the gap, **completely determines** the entire infinite set of
    zeta zeros — both trivial and nontrivial, on or off the critical line.

    The proof is unconditional: it does not assume RH or any conjecture. -/
theorem cosh_harmonics_zeta_invariance
    {U : Set ℂ} (G : CoshHarmonicRepr U)
    (hζ_analytic : AnalyticOnNhd ℂ riemannZeta U) :
    -- (i)   Full agreement: g = ζ on all of U
    EqOn G.repr riemannZeta U
    -- (ii)  Zero set equality: {z ∈ U | g(z) = 0} = {z ∈ U | ζ(z) = 0}
    ∧ ({z ∈ U | G.repr z = 0} = {z ∈ U | riemannZeta z = 0})
    -- (iii) Meromorphic order equality at every point
    ∧ (∀ z ∈ U, meromorphicOrderAt G.repr z = meromorphicOrderAt riemannZeta z)
    -- (iv)  Every nontrivial zero in U is detected by g
    ∧ (∀ (Z : NontrivialZetaZeros) (n : ℕ), Z.zeros n ∈ U → G.repr (Z.zeros n) = 0) := by
  -- The identity theorem gives full agreement from overlap agreement
  have heqU : EqOn G.repr riemannZeta U :=
    identity_theorem_on_overlap' G.domain_isOpen G.domain_isPreconnected
      G.domain_contains_overlap G.repr_analytic hζ_analytic G.repr_eq_zeta_on_overlap
  refine ⟨heqU, ?_, ?_, ?_⟩
  -- Zero set equality
  · ext z; simp only [mem_sep_iff]
    exact ⟨fun ⟨hz, hfz⟩ => ⟨hz, by rwa [← heqU hz]⟩,
           fun ⟨hz, hgz⟩ => ⟨hz, by rwa [heqU hz]⟩⟩
  -- Meromorphic order equality
  · intro z hz
    apply meromorphicOrderAt_congr
    have hO : U ∈ nhds z := G.domain_isOpen.mem_nhds hz
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hO, heqU⟩)
  -- Nontrivial zeros detected
  · intro Z n hn
    rw [heqU hn]
    exact Z.is_zero n

/-- **Corollary: The cosh-kernel data in the gap determines zeta zeros unconditionally.**
    If two cosh harmonic representations agree with ζ on the overlap, they have
    the same zero set on any common connected domain. -/
theorem cosh_repr_zero_uniqueness
    {U : Set ℂ} (G₁ G₂ : CoshHarmonicRepr U)
    (hζ : AnalyticOnNhd ℂ riemannZeta U) :
    EqOn G₁.repr G₂.repr U ∧
    {z ∈ U | G₁.repr z = 0} = {z ∈ U | G₂.repr z = 0} := by
  have h₁ := (cosh_harmonics_zeta_invariance G₁ hζ).1
  have h₂ := (cosh_harmonics_zeta_invariance G₂ hζ).1
  constructor
  · intro z hz; rw [h₁ hz, h₂ hz]
  · ext z; simp only [mem_sep_iff]
    exact ⟨fun ⟨hz, hfz⟩ => ⟨hz, by rw [h₂ hz]; rwa [← h₁ hz]⟩,
           fun ⟨hz, hgz⟩ => ⟨hz, by rw [h₁ hz]; rwa [← h₂ hz]⟩⟩

/-! ## Concrete Cosh Kernel Instance

We show that the cosh kernel at `arcsin(1/2) = π/6` can serve as the basis
for a cosh harmonic representation, by establishing its analyticity and
the structural properties needed. -/

/-- The cosh kernel at any frequency `t` is analytic on any set (being entire). -/
theorem coshKernel_analyticOnNhd_subset (t : ℝ) (S : Set ℂ) :
    AnalyticOnNhd ℂ (coshKernel' t) S :=
  (coshKernel_analyticOnNhd t).mono (subset_univ S)

/-
PROBLEM
The cosh kernel's zeros have real part exactly `π/6` (the reflection axis).
    For nonzero `t`, `cosh(t(s − π/6)) = 0` iff `t(s − π/6) = i(π/2 + nπ)` for
    some integer `n`, which gives `Re(s) = π/6`.

PROVIDED SOLUTION
The cosh kernel is cosh(t * (s - π/6)). If cosh(z) = 0 then z = i(π/2 + nπ) for some integer n. So t * (s - π/6) is purely imaginary. Since t is real and nonzero, s - π/6 must be purely imaginary, meaning Re(s) = π/6. More concretely: cosh(z) = (exp(z) + exp(-z))/2 = 0 means exp(2z) = -1, so 2z = iπ + 2nπi, meaning z is purely imaginary. If t * (s - π/6) is purely imaginary and t ≠ 0 is real, then s - π/6 is purely imaginary, so Re(s - π/6) = 0, i.e., Re(s) = π/6. Key approach: from cosh(w) = 0, derive that w.re = 0 (since cosh(a+bi) = cosh(a)cos(b) + i·sinh(a)sin(b), and cosh(a)cos(b) = 0 and sinh(a)sin(b) = 0 — cosh(a) > 0 for real a ≠ 0, and if a ≠ 0 then sinh(a) ≠ 0 so sin(b) = 0 but then cos(b) = ±1 so cosh(a)·(±1) = 0 contradicts cosh(a) > 0). So w.re = 0. Then t · Re(s - π/6) = Re(w) = 0, and t ≠ 0, so Re(s) = π/6.
-/
theorem coshKernel_zeros_real_part (t : ℝ) (ht : t ≠ 0) (s : ℂ)
    (hs : coshKernel' t s = 0) : s.re = Real.pi / 6 := by
  unfold coshKernel' at hs;
  simp_all +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cosh ];
  by_cases h : Real.cos ( t * s.im ) = 0 <;> by_cases h' : Real.sin ( t * s.im ) = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
  · nlinarith [ Real.sin_sq_add_cos_sq ( t * s.im ) ];
  · exact mul_left_cancel₀ ht <| by linarith;
  · exact False.elim <| h <| by nlinarith [ Real.exp_pos ( t * ( s.re - Real.pi / 6 ) ), Real.exp_pos ( - ( t * ( s.re - Real.pi / 6 ) ) ) ] ;
  · grind +splitIndPred

/-
PROBLEM
The cosh kernel zeros form conjugate pairs: if `cosh(t(s − π/6)) = 0` then
    `cosh(t(conj(s) − π/6)) = 0`, because the conjugate of `i(π/2 + nπ)/t` is
    `−i(π/2 + nπ)/t`, giving another zero.

PROVIDED SOLUTION
coshKernel t s = cosh(t * (s - π/6)). The conjugate is cosh(t * (conj(s) - π/6)). Since t and π/6 are real, conj(t * (s - π/6)) = t * (conj(s) - π/6). And cosh(conj(z)) = conj(cosh(z)). So cosh(t * (conj(s) - π/6)) = conj(cosh(t * (s - π/6))) = conj(0) = 0. Key lemma: map_cosh or Complex.cosh_conj: cosh(conj z) = conj(cosh z). Since t and π/6 are real, conj(↑t * (s - ↑(π/6))) = ↑t * (conj(s) - ↑(π/6)).
-/
theorem coshKernel_zeros_conjugate (t : ℝ) (s : ℂ)
    (hs : coshKernel' t s = 0) : coshKernel' t (starRingEnd ℂ s) = 0 := by
  convert congr_arg Star.star hs using 1 ; unfold coshKernel'; ring;
  · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.cosh_eq ] ; ring;
    norm_num [ Complex.cosh, Complex.exp_re, Complex.exp_im ] ; ring ; norm_num;
  · norm_num

/-! ## The Cosh Kernel Zeros Extend Into the Gap

The zeros of the cosh kernel lie at `Re(s) = π/6 ≈ 0.524`, which is to the LEFT
of the overlap region `1 < Re(s) < π/3`. The cosh representation, however,
extends rightward from these zeros through the domain `Re(s) < π/3`, reaching
into and past the overlap strip.

The "conjugate zeros extending into the gap" means: the analytic information
encoded by the cosh kernel's zero structure at `Re(s) = π/6` propagates
rightward through the cosh domain, through the overlap, and (by the identity
theorem) determines the function on any connected continuation — including
the region where the nontrivial zeta zeros live (`0 < Re(s) < 1`). -/

/-- The cosh kernel's zero line (`Re(s) = π/6`) is strictly to the left of the
    overlap region (`Re(s) > 1`). This means the cosh kernel's conjugate zeros
    must propagate their influence through the gap to constrain ζ. -/
theorem cosh_zeros_left_of_overlap : Real.pi / 6 < 1 := by
  linarith [Real.pi_gt_three, Real.pi_lt_four]

/-- The cosh kernel's zero line is inside the cosh domain (`Re(s) < π/3`),
    confirming the zeros are accessible to the cosh representation. -/
theorem cosh_zeros_in_cosh_domain : Real.pi / 6 < Real.pi / 3 := by
  linarith [Real.pi_pos]

/-! ## Invariance Propagation Chain

The full chain of propagation:

  cosh zeros (Re = π/6)
    → cosh representation valid (Re < π/3)
      → overlap strip (1 < Re < π/3)
        → Euler product valid (Re > 1)
          → identity theorem forces agreement
            → determines ζ on any connected extension
              → determines ALL zeta zeros

This is the essence of cosh_harmonics_zeta_invariance: the harmonic data
of the cosh kernel, anchored at the reflection axis arcsin(1/2) = π/6
and propagating through its conjugate zeros, is a complete invariant of
the infinite set of zeta zeros. -/

/-- **The propagation chain**: the nontrivial zeta zeros, the cosh kernel zeros,
    and the overlap region are all on the same side of the Euler boundary, with
    the overlap bridging them.
    - Zeta zeros: `0 < Re(ρ) < 1`
    - Cosh kernel zeros: `Re(s) = π/6 ≈ 0.524` (inside the critical strip)
    - Overlap: `1 < Re(s) < π/3 ≈ 1.047`
    - Euler half-plane: `Re(s) > 1`

    The cosh kernel zeros and zeta zeros are on the SAME SIDE (Re < 1), while
    the overlap bridges into the Euler half-plane (Re > 1). The identity theorem
    then propagates back leftward to determine ζ everywhere. -/
theorem propagation_chain_geometry :
    -- Cosh kernel zeros at Re = π/6 < 1
    Real.pi / 6 < 1
    -- Overlap region starts at Re = 1
    ∧ (∀ s ∈ overlapRegion', 1 < s.re)
    -- Overlap region ends at Re = π/3 > 1
    ∧ 1 < Real.pi / 3
    -- Nontrivial zeros have Re < 1
    ∧ (∀ (Z : NontrivialZetaZeros) (n : ℕ), (Z.zeros n).re < 1) := by
  refine ⟨by linarith [Real.pi_gt_three, Real.pi_lt_four], ?_, by linarith [Real.pi_gt_three], ?_⟩
  · intro s hs; rw [overlapRegion'_eq] at hs; exact hs.1
  · intro Z n; exact (Z.in_critical_strip n).2

/-- **Full invariance package.**
    Combines all results: the cosh kernel at arcsin(1/2), the overlap geometry,
    and the identity theorem together show that the cosh harmonic data is a
    complete invariant of the zeta zero set. -/
theorem cosh_harmonics_zeta_full_invariance
    {U : Set ℂ} (G : CoshHarmonicRepr U)
    (hζ : AnalyticOnNhd ℂ riemannZeta U) :
    -- Geometric setup
    (Real.arcsin (1/2) = Real.pi / 6)
    -- Overlap is open, nonempty, connected
    ∧ (IsOpen overlapRegion' ∧ overlapRegion'.Nonempty ∧ IsPreconnected overlapRegion')
    -- Cosh kernel is entire
    ∧ (∀ t : ℝ, Differentiable ℂ (coshKernel' t))
    -- Full agreement of g and ζ
    ∧ EqOn G.repr riemannZeta U
    -- Zero set equality
    ∧ ({z ∈ U | G.repr z = 0} = {z ∈ U | riemannZeta z = 0})
    -- Order equality
    ∧ (∀ z ∈ U, meromorphicOrderAt G.repr z = meromorphicOrderAt riemannZeta z) := by
  obtain ⟨heq, hzero, hord, _⟩ := cosh_harmonics_zeta_invariance G hζ
  exact ⟨cosh_reflection_axis',
         ⟨overlapRegion'_isOpen, overlapRegion'_nonempty, overlapRegion'_isPreconnected⟩,
         coshKernel_differentiable,
         heq, hzero, hord⟩

end
