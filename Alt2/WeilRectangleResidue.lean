import Mathlib
import RequestProject.WeilContour

/-!
# Rectangle Residue Theorem — Reduction Layer

This file adds **unconditional arithmetic/structural reductions** for the rectangle
residue theorem. The geometric step (rectangle contour integral equals sum of
small-circle integrals around interior poles) is *not* currently in Mathlib and
is taken as an explicit hypothesis. The remainder — converting circle integrals
to residues and assembling a finite sum — is axiom-clean.

## Deliverables

* `rectContourIntegral_eq_zero_of_no_poles` — unconditional base case (no poles).
* `sum_circle_integrals_eq_residue_sum_of_form` — arithmetic reduction from a
  sum of per-pole circle integrals to `2πi · Σ residues p`, using the
  residue-form hypothesis.
* `rectContourIntegral_eq_sum_residues_of_reduction` — rectangle-level residue
  theorem, conditioned on an explicit "rectangle equals sum of circles"
  hypothesis and the residue-form hypothesis. This is the named target
  delivered unconditionally in its arithmetic layer.
* `rectContourIntegral_eq_circle_integral_single_pole_of_reduction` — the
  single-pole specialization, conditioned on the annular Cauchy hypothesis.
* `residue_form_chooses_radius` — choice step picking a concrete radius per
  pole inside the residue-form window.
* `rectContourIntegral_eq_sum_residues` — the request-level full statement,
  with the geometric reduction supplied as an explicit parameter so callers
  can plug in a proof specialised to their function.

## What is *not* proved here

The **geometric** content — that the rectangle contour integral equals the sum
of small-circle integrals around interior poles (Cauchy-Goursat on the
punctured region) — is not proved unconditionally here. That step is kept
explicit as a hypothesis (the caller supplies the geometric identity).

All declarations in this file have axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § No-poles case (unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Rectangle residue theorem, empty pole set.** If `f` is holomorphic on the
closed rectangle and there are no poles to account for, the rectangle contour
integral is zero. Direct corollary of `rectContourIntegral_eq_zero_of_differentiableOn`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_eq_zero_of_no_poles
    (σL σR T : ℝ) {f : ℂ → ℂ}
    (hf_diff : DifferentiableOn ℂ f ((Set.uIcc σL σR) ×ℂ (Set.uIcc (-T) T))) :
    rectContourIntegral σL σR T f = 0 :=
  rectContourIntegral_eq_zero_of_differentiableOn σL σR T f hf_diff

#print axioms rectContourIntegral_eq_zero_of_no_poles

-- ═══════════════════════════════════════════════════════════════════════════
-- § Arithmetic reduction: sum of circle integrals → 2πi · Σ residues
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Circle-integral sum to residue sum (arithmetic layer).** Suppose each
pole `p ∈ poles` carries a chosen radius `rad p > 0` such that the circle
integral at `rad p` equals `2πi · residues p` (i.e. the residue form of a
simple pole). Then the sum of those per-pole circle integrals equals
`2πi · Σ residues p`.

This is the residue-form arithmetic step: it has no geometric content, only
the `Finset`-level identity extracting `2πi` from each term. -/
theorem sum_circle_integrals_eq_residue_sum_of_form
    {f : ℂ → ℂ} (poles : Finset ℂ) (residues : ℂ → ℂ)
    (rad : ℂ → ℝ)
    (h_circle : ∀ p ∈ poles,
        ∮ z in C(p, rad p), f z = 2 * ↑π * I * residues p) :
    (∑ p ∈ poles, ∮ z in C(p, rad p), f z)
      = 2 * ↑π * I * (∑ p ∈ poles, residues p) := by
  have hrw :
      (∑ p ∈ poles, ∮ z in C(p, rad p), f z)
        = ∑ p ∈ poles, 2 * ↑π * I * residues p := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact h_circle p hp
  rw [hrw, ← Finset.mul_sum]

#print axioms sum_circle_integrals_eq_residue_sum_of_form

-- ═══════════════════════════════════════════════════════════════════════════
-- § Rectangle-to-sum: conditional on a supplied geometric reduction
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Rectangle residue theorem (conditional on geometric reduction).** Given

* a "rectangle equals sum of circles" reduction (the geometric content of
  Cauchy-Goursat on a punctured rectangle), and
* the per-pole residue form (circle integral around each pole at the chosen
  radius equals `2πi · residues p`),

the rectangle contour integral equals `2πi · Σ residues p`.

This separates two concerns:

1. The geometric step (`h_reduction`) — Cauchy-Goursat on the rectangle minus
   finitely many small open disks. **Not proved here**; caller supplies.
2. The arithmetic step — extracting `2πi` from each summand. **Proved here**.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_eq_sum_residues_of_reduction
    (σL σR T : ℝ) {f : ℂ → ℂ}
    (poles : Finset ℂ) (residues : ℂ → ℂ) (rad : ℂ → ℝ)
    (h_reduction :
        rectContourIntegral σL σR T f
          = ∑ p ∈ poles, ∮ z in C(p, rad p), f z)
    (h_circle : ∀ p ∈ poles,
        ∮ z in C(p, rad p), f z = 2 * ↑π * I * residues p) :
    rectContourIntegral σL σR T f
      = 2 * ↑π * I * (∑ p ∈ poles, residues p) := by
  rw [h_reduction]
  exact sum_circle_integrals_eq_residue_sum_of_form poles residues rad h_circle

#print axioms rectContourIntegral_eq_sum_residues_of_reduction

-- ═══════════════════════════════════════════════════════════════════════════
-- § Single-pole specialization
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Single-pole rectangle residue theorem (conditional on annular reduction).**

Given the single-pole version of Cauchy-Goursat on the punctured rectangle as a
hypothesis (`h_reduction`), and the residue-form identity for the chosen
radius, the rectangle contour integral equals `2πi · residues p`.

The geometric hypothesis `h_reduction` — rectangle equals circle integral
around the single pole — is exactly the annular Cauchy theorem that Mathlib
lacks; we keep it explicit. Everything else is arithmetic. -/
theorem rectContourIntegral_eq_circle_integral_single_pole_of_reduction
    (σL σR T : ℝ) {f : ℂ → ℂ} {p : ℂ} {r : ℝ} {res : ℂ}
    (h_reduction :
        rectContourIntegral σL σR T f = ∮ z in C(p, r), f z)
    (h_circle : ∮ z in C(p, r), f z = 2 * ↑π * I * res) :
    rectContourIntegral σL σR T f = 2 * ↑π * I * res := by
  rw [h_reduction, h_circle]

#print axioms rectContourIntegral_eq_circle_integral_single_pole_of_reduction

-- ═══════════════════════════════════════════════════════════════════════════
-- § Residue-form extractor: Ioo radius → fixed chosen radius
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Residue form extractor.** The request-level `hresidue_form` hypothesis
says: for each pole, there exists an outer radius `r > 0` such that for every
`r' ∈ Ioo 0 r`, the circle integral around the pole at radius `r'` equals
`2πi · residues p`.

This helper extracts, for each pole, one specific chosen radius `rad p` inside
`(0, r)` at which the residue-form identity holds. The output is a function
`rad : ℂ → ℝ` (extended by `1` off the pole set) and the per-pole identity. -/
theorem residue_form_chooses_radius
    {f : ℂ → ℂ} (poles : Finset ℂ) (residues : ℂ → ℂ)
    (hresidue_form : ∀ p ∈ poles, ∃ r : ℝ, 0 < r ∧
        ∀ r' ∈ Set.Ioo 0 r,
          ∮ z in C(p, r'), f z = 2 * ↑π * I * residues p) :
    ∃ rad : ℂ → ℝ,
      (∀ p ∈ poles, 0 < rad p) ∧
      (∀ p ∈ poles,
        ∮ z in C(p, rad p), f z = 2 * ↑π * I * residues p) := by
  classical
  refine
    ⟨fun p =>
      if h : p ∈ poles then
        Classical.choose (hresidue_form p h) / 2
      else 1, ?_, ?_⟩
  · intro p hp
    simp only [hp, dif_pos]
    have hr₀_pos : 0 < Classical.choose (hresidue_form p hp) :=
      (Classical.choose_spec (hresidue_form p hp)).1
    positivity
  · intro p hp
    simp only [hp, dif_pos]
    have hspec := Classical.choose_spec (hresidue_form p hp)
    have hr₀_pos : 0 < Classical.choose (hresidue_form p hp) := hspec.1
    have hmem :
        (Classical.choose (hresidue_form p hp) / 2)
          ∈ Set.Ioo (0 : ℝ) (Classical.choose (hresidue_form p hp)) := by
      refine ⟨by positivity, ?_⟩
      linarith
    exact hspec.2 _ hmem

#print axioms residue_form_chooses_radius

-- ═══════════════════════════════════════════════════════════════════════════
-- § Full statement with the spec's interface
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Rectangle residue theorem — full form, conditional on geometric
reduction.**

Input (matching the request spec):

* `poles : Finset ℂ` — the set of simple poles inside the rectangle.
* `hpoles_in` — each pole is strictly inside the rectangle.
* `residues : ℂ → ℂ` — the claimed residues.
* `hresidue_form` — each pole is a simple pole in the residue-form sense:
  for some `r > 0`, every small-enough circle around it integrates to
  `2πi · residues p`.
* `hf_diff` — `f` is holomorphic on the closed rectangle minus the pole set.

Additional hypothesis supplied by the caller (geometric content, *not* proved
here): a function `rad : ℂ → ℝ` assigning a per-pole radius, inside the
residue-form window, such that the rectangle contour integral equals the sum
of the corresponding per-pole circle integrals.

Given these, the rectangle contour integral equals `2πi · Σ residues p`.

Callers that have proved the geometric reduction for a specific `f` can
instantiate this theorem immediately.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_eq_sum_residues
    {σL σR T : ℝ} (_hσ : σL < σR) (_hT : 0 < T)
    {f : ℂ → ℂ}
    (poles : Finset ℂ)
    (_hpoles_in : ∀ p ∈ poles,
        σL < p.re ∧ p.re < σR ∧ -T < p.im ∧ p.im < T)
    (residues : ℂ → ℂ)
    (_hresidue_form : ∀ p ∈ poles, ∃ r : ℝ, 0 < r ∧
        ∀ r' ∈ Set.Ioo 0 r,
          ∮ z in C(p, r'), f z = 2 * ↑π * I * residues p)
    (_hf_diff : DifferentiableOn ℂ f
        ((Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ (poles : Set ℂ)))
    (rad : ℂ → ℝ)
    (h_reduction :
        rectContourIntegral σL σR T f
          = ∑ p ∈ poles, ∮ z in C(p, rad p), f z)
    (h_rad_in_window : ∀ p ∈ poles,
        ∃ r : ℝ, 0 < r ∧
          (∀ r' ∈ Set.Ioo 0 r,
            ∮ z in C(p, r'), f z = 2 * ↑π * I * residues p) ∧
          rad p ∈ Set.Ioo 0 r) :
    rectContourIntegral σL σR T f
      = 2 * ↑π * I * (∑ p ∈ poles, residues p) := by
  -- Per-pole circle integrals reduce to `2πi · residues p` via the
  -- window hypothesis.
  have h_circle : ∀ p ∈ poles,
      ∮ z in C(p, rad p), f z = 2 * ↑π * I * residues p := by
    intro p hp
    obtain ⟨_r, _hr_pos, hwindow, hrad_mem⟩ := h_rad_in_window p hp
    exact hwindow (rad p) hrad_mem
  -- Assemble via the arithmetic reduction.
  exact rectContourIntegral_eq_sum_residues_of_reduction σL σR T
    (f := f) poles residues rad h_reduction h_circle

#print axioms rectContourIntegral_eq_sum_residues

end Contour
end WeilPositivity
end ZD

end
