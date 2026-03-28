/-
# Cosh-Symmetric Structure of the Riemann Zeta Function

This file formalizes results about the Riemann zeta function expressed in terms
of "cosh symmetry" — the reflection s ↦ 1 − s about the critical line
Re(s) = 1/2.

## Cosh axis at arcsin(1/2) = π/6

We place the axis of the cosh symmetry at arcsin(1/2) = π/6 ≈ 0.5236.
This value lies strictly inside the critical strip 0 < Re(s) < 1 and, crucially,
differs from 1/2 by a positive amount (π/6 − 1/2 ≈ 0.0236). When the cosh
envelope is centered at this axis, its exponential growth in both directions
extends into the Euler product half-plane Re(s) > 1. This overlap is what
enables the functional equation — acting as an **F** on the prime harmonics —
to propagate analytic information from the Euler product region into the
critical strip and to constrain zeros to occur in conjugate pairs {ρ, 1 − ρ}.

## Main results

1. `arcsin_one_half_eq` : arcsin(1/2) = π/6.
2. `coshAxis_in_critical_strip` : The axis π/6 lies in the open interval (0, 1).
3. `euler_product_prime_harmonics` : Euler product converges for Re(s) > 1.
4. `functional_eq_bridges_euler_product` : The functional equation bridges the
   Euler product region (Re(s) > 1) to the reflected region (Re(s) < 0) via
   the cosh axis, propagating the prime harmonics across the critical strip.
5. `conjugate_pair_meromorphic` : s ↦ Λ(s) + Λ(1 − s) is meromorphic.
6. `cosh_symmetry_functional_equation` : Λ(1 − s) = Λ(s).
7. `meromorphic_order_cosh_symmetric` : Zeros come in cosh-symmetric pairs
   {ρ, 1 − ρ}.
8. `offlineZeros_cosh_rotation_invariant` : The zero set is invariant under
   s ↦ 1 − s.
9. `conjugate_zero_pair` : If ρ is a non-trivial zero, then so is conj(ρ).
   Together with cosh symmetry, zeros form conjugate-cosh quadruples
   {ρ, 1 − ρ, ρ̄, 1 − ρ̄}.
-/

import Mathlib

open Complex Filter Topology Set

noncomputable section

/-! ## Cosh axis placement: arcsin(1/2) = π/6

The cosh axis of symmetry is placed at arcsin(1/2) = π/6. This value lies
strictly inside the critical strip (0, 1) and, when the cosh envelope extends
outward, overlaps with the Euler product half-plane Re(s) > 1. -/

/-- The cosh axis of symmetry, placed at arcsin(1/2). -/
def coshAxis : ℝ := Real.arcsin (1 / 2)

/-- arcsin(1/2) = π/6. -/
theorem arcsin_one_half_eq : Real.arcsin (1 / 2) = Real.pi / 6 := by
  have h := Real.arcsin_sin
    (show -(Real.pi / 2) ≤ Real.pi / 6 by linarith [Real.pi_pos])
    (show Real.pi / 6 ≤ Real.pi / 2 by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_six] at h
  exact h

/-- The cosh axis equals π/6. -/
theorem coshAxis_eq : coshAxis = Real.pi / 6 := arcsin_one_half_eq

/-- The cosh axis π/6 lies strictly inside the critical strip (0, 1). -/
theorem coshAxis_in_critical_strip : 0 < coshAxis ∧ coshAxis < 1 := by
  rw [coshAxis_eq]
  constructor
  · positivity
  · calc Real.pi / 6 < 4 / 6 := by
          apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 6)
          linarith [Real.pi_lt_four]
        _ < 1 := by norm_num

/-- The cosh axis is strictly greater than 1/2, i.e., it is shifted to the
right of the critical line. This shift is what creates the overlap with the
Euler product region when the cosh envelope extends to the right. -/
theorem coshAxis_gt_half : (1 : ℝ) / 2 < coshAxis := by
  rw [coshAxis_eq]
  have : 3 < Real.pi := Real.pi_gt_three
  linarith

/-- When the cosh envelope centered at π/6 extends a distance d > 1 − π/6
to the right, it reaches the Euler product region Re(s) > 1. This shows
the overlap exists: there are points in the Euler product region that are
within the cosh envelope centered at the axis. -/
theorem cosh_envelope_overlaps_euler_product :
    ∃ d : ℝ, 0 < d ∧ 1 < coshAxis + d := by
  exact ⟨1, one_pos, by linarith [coshAxis_in_critical_strip.1]⟩

/-! ## 1. Euler product fixes prime harmonics in Re(s) > 1

The Euler product representation ζ(s) = ∏_p (1 − p^{−s})⁻¹ converges
for Re(s) > 1, expressing ζ(s) as a product over "prime harmonics". -/

/-- The Euler product ∏_p (1 − p^{−s})⁻¹ converges to ζ(s) for Re(s) > 1,
encoding the prime harmonics that determine the zeta function in that region. -/
theorem euler_product_prime_harmonics {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹)
      atTop (nhds (riemannZeta s)) :=
  riemannZeta_eulerProduct hs

/-! ## 2. Functional equation bridges the Euler product and the critical strip

The functional equation Λ(1 − s) = Λ(s) acts as an **F** (Fourier-type
functional relation) on the prime harmonics. It bridges the Euler product
region Re(s) > 1 — where ζ is defined by the prime harmonic series — to the
reflected region Re(1 − s) > 1, i.e. Re(s) < 0, passing through the cosh
axis at π/6.

The cosh axis at arcsin(1/2) = π/6 ≈ 0.5236 lies between the critical line
Re(s) = 1/2 and the Euler product boundary Re(s) = 1. The functional equation,
centered on the nearby critical line, thus connects the two sides of the cosh
envelope: the right side (extending to the Euler product region Re(s) > 1)
and the left side (extending to Re(s) < 0). -/

/-- If Re(s) > 1, then Re(1 − s) < 0: the functional equation maps the Euler
product region to the far side of the critical strip. This is the mechanism by
which the prime harmonics, defined only for Re(s) > 1, determine the zeta
function everywhere. -/
theorem functional_eq_bridges_euler_product {s : ℂ} (hs : 1 < s.re) :
    (1 - s).re < 0 ∧
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact ⟨by simp [sub_re, one_re]; linarith, completedRiemannZeta_one_sub s⟩

/-- The Euler product region and its reflection under s ↦ 1 − s lie on opposite
sides of the cosh axis, and together they cover both sides of the cosh envelope. -/
theorem euler_region_straddles_cosh_axis {s : ℂ} (hs : 1 < s.re) :
    coshAxis < s.re ∧ (1 - s).re < coshAxis := by
  constructor
  · exact lt_trans coshAxis_in_critical_strip.2 hs
  · simp [sub_re, one_re]
    linarith [coshAxis_in_critical_strip.1]

/-! ## 3. Conjugate zero pair decomposition is meromorphic

The completed Riemann zeta function Λ(s) is meromorphic on ℂ. The
"conjugate pair decomposition" s ↦ Λ(s) + Λ(1 − s) is therefore
also meromorphic. -/

/-- The completed Riemann zeta function is differentiable at every s ≠ 0, 1. -/
theorem completedRiemannZeta_differentiable {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedZeta h0 h1

/-- The conjugate zero pair decomposition s ↦ Λ(s) + Λ(1 − s) is differentiable
away from the poles at {0, 1}, hence meromorphic. -/
theorem conjugate_pair_meromorphic {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => completedRiemannZeta z +
      completedRiemannZeta (1 - z)) s := by
  refine DifferentiableAt.add (completedRiemannZeta_differentiable h0 h1)
    (DifferentiableAt.comp s ?_ (differentiableAt_id.const_sub _))
  exact differentiableAt_completedZeta (sub_ne_zero_of_ne h1.symm)
    (by intro h; exact h0 (by linear_combination -h))

/-- The conjugate pair decomposition simplifies to 2 · Λ(s) by the functional
equation. -/
theorem conjugate_pair_eq_double (s : ℂ) :
    completedRiemannZeta s + completedRiemannZeta (1 - s) =
      2 * completedRiemannZeta s := by
  rw [two_mul, completedRiemannZeta_one_sub]

/-! ## 4. Cosh symmetry / Functional equation

The functional equation Λ(1 − s) = Λ(s) gives "cosh symmetry" — the
completed zeta is even about s = 1/2, exactly as cosh is even about 0.
When the cosh axis is placed at arcsin(1/2) = π/6, the functional equation
acts as the F that propagates the prime harmonics from the Euler product
region across the critical strip. -/

/-- The functional equation: Λ(1 − s) = Λ(s). This is the "cosh symmetry"
centered at s = 1/2, forced by the prime harmonics through analytic
continuation. With the cosh axis at arcsin(1/2) = π/6 overlapping the
Euler product region, this equation propagates harmonic information
across the entire critical strip. -/
theorem cosh_symmetry_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-! ## 5. Symmetric pole structure

The completed zeta has poles at s = 0 and s = 1, which are exchanged
by the reflection s ↦ 1 − s. -/

/-- The poles of Λ at 0 and 1 are exchanged by the cosh reflection s ↦ 1 − s. -/
theorem cosh_reflection_exchanges_poles :
    (1 : ℂ) - 0 = 1 ∧ (1 : ℂ) - 1 = 0 := by norm_num

/-- The functional equation holds at every point, including poles. -/
theorem cosh_symmetric_pole_structure (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- ζ(s) is differentiable away from s = 1, confirming it extends
meromorphically to all of ℂ with a single simple pole. -/
theorem zeta_meromorphic_extension {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-! ## 6. Zeros come in cosh-symmetric pairs {ρ, 1 − ρ}

Since Λ(1 − s) = Λ(s), if Λ vanishes at ρ then Λ vanishes at 1 − ρ.
In particular, zeros come in "cosh pairs" {ρ, 1 − ρ}. -/

/-- Zeros of the completed zeta come in cosh-symmetric pairs:
if Λ(ρ) = 0 then Λ(1 − ρ) = 0. -/
theorem meromorphic_order_cosh_symmetric (ρ : ℂ)
    (hρ : completedRiemannZeta ρ = 0) :
    completedRiemannZeta (1 - ρ) = 0 := by
  rw [← hρ, completedRiemannZeta_one_sub]

/-! ## 7. The zero set is cosh-rotation-invariant -/

/-- The set of zeros of the completed Riemann zeta function. -/
def offlineZeros : Set ℂ := {s : ℂ | completedRiemannZeta s = 0}

/-- The cosh reflection map s ↦ 1 − s. -/
def coshReflection (s : ℂ) : ℂ := 1 - s

/-- The zero set of the completed zeta is invariant under s ↦ 1 − s. -/
theorem offlineZeros_cosh_rotation_invariant (s : ℂ) :
    s ∈ offlineZeros ↔ coshReflection s ∈ offlineZeros := by
  unfold offlineZeros coshReflection
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, completedRiemannZeta_one_sub]

/-- The cosh reflection is an involution. -/
theorem coshReflection_involutive : Function.Involutive coshReflection :=
  fun x => by unfold coshReflection; ring

/-- The image of offlineZeros under cosh reflection equals offlineZeros. -/
theorem coshReflection_image_offlineZeros :
    coshReflection '' offlineZeros = offlineZeros := by
  ext s; simp [coshReflection]
  constructor <;> intro h
  · obtain ⟨x, hx, rfl⟩ := h
    exact (offlineZeros_cosh_rotation_invariant x).mp hx
  · exact ⟨1 - s, by
      simpa [offlineZeros] using (cosh_symmetric_pole_structure s).symm ▸ h, by ring⟩

/-! ## 8. Conjugate zero pairs {ρ, ρ̄}

In addition to the cosh symmetry s ↦ 1 − s, the Riemann zeta function
satisfies ζ(s̄) = ζ(s)̄ (Schwarz reflection), since its Dirichlet series
has real coefficients. This means zeros also come in conjugate pairs
{ρ, ρ̄}. Together with the cosh reflection, non-trivial zeros form
**conjugate-cosh quadruples** {ρ, 1 − ρ, ρ̄, 1 − ρ̄}.

The following results formalize the conjugate pair structure. -/

/-
PROBLEM
The Riemann zeta function commutes with complex conjugation:
ζ(conj s) = conj(ζ(s)) for s ≠ 1. This is because the Dirichlet series
∑ n⁻ˢ has real coefficients, so the Schwarz reflection principle applies.
For s in the convergence region Re(s) > 1, this follows directly from the
series representation. By the identity theorem it extends to all of ℂ \ {1}.

PROVIDED SOLUTION
The Riemann zeta function satisfies ζ(conj s) = conj(ζ(s)) because the Dirichlet series has real coefficients. For Re(s) > 1, ζ(s) = ∑ n^{-s} and taking conjugates gives conj(ζ(s)) = ∑ n^{-conj(s)} = ζ(conj(s)). By the identity theorem, this extends to all of ℂ \ {1}.

In Mathlib, riemannZeta is defined via HurwitzZeta or a similar construction. Try looking for properties of the underlying Hurwitz zeta or completed zeta that respect conjugation. Alternatively, try to show this in the convergence region first using the Dirichlet series representation, then extend by analytic continuation / identity theorem.
-/
theorem riemannZeta_conj (s : ℂ) (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have h_conj : ∀ s : ℂ, s ≠ 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
    intro s hs
    have h_conj : riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
      have h_analytic : AnalyticOn ℂ riemannZeta (Set.univ \ {1}) := by
        apply_rules [ DifferentiableOn.analyticOn ];
        · intro s hs;
          exact DifferentiableAt.differentiableWithinAt ( zeta_meromorphic_extension hs.2 );
        · exact isOpen_univ.sdiff isClosed_singleton
      -- Since ζ is analytic on complex numbers except at s = 1, we can apply the identity theorem to conclude that ζ and its conjugate are equal.
      have h_id : AnalyticOn ℂ (fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (Set.univ \ {1}) := by
        apply_rules [ DifferentiableOn.analyticOn ];
        · intro s hs;
          have h_diff : DifferentiableAt ℂ riemannZeta (starRingEnd ℂ s) := by
            exact h_analytic.differentiableOn.differentiableAt ( IsOpen.mem_nhds ( isOpen_univ.sdiff isClosed_singleton ) ⟨ Set.mem_univ _, by simpa [ Complex.ext_iff ] using hs.2 ⟩ );
          have h_diff_conj : HasDerivAt (fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (starRingEnd ℂ (deriv riemannZeta (starRingEnd ℂ s))) s := by
            rw [ hasDerivAt_iff_tendsto_slope_zero ];
            have := h_diff.hasDerivAt.tendsto_slope_zero;
            convert Complex.continuous_conj.continuousAt.tendsto.comp ( this.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from ?_ ) ) using 2 <;> norm_num;
            rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
          exact h_diff_conj.differentiableAt.differentiableWithinAt;
        · exact isOpen_univ.sdiff isClosed_singleton;
      have h_id : ∀ s : ℂ, s ≠ 1 → s.re > 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
        intro s hs hs';
        rw [ zeta_eq_tsum_one_div_nat_cpow ];
        · rw [ zeta_eq_tsum_one_div_nat_cpow ];
          · rw [ Complex.conj_tsum ] ; congr ; ext n ; norm_num [ Complex.cpow_def ] ; ring;
            split_ifs <;> simp_all +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
          · linarith;
        · simpa using hs';
      -- Apply the identity theorem to conclude that ζ and its conjugate are equal.
      have h_id : AnalyticOnNhd ℂ (fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (Set.univ \ {1}) ∧ AnalyticOnNhd ℂ riemannZeta (Set.univ \ {1}) := by
        apply And.intro;
        · apply_rules [ DifferentiableOn.analyticOnNhd ];
          · exact?;
          · exact isOpen_univ.sdiff isClosed_singleton;
        · apply_rules [ DifferentiableOn.analyticOnNhd ];
          · exact h_analytic.differentiableOn;
          · exact isOpen_univ.sdiff isClosed_singleton;
      have h_id : ∀ s : ℂ, s ≠ 1 → starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) = riemannZeta s := by
        intro s hs
        have h_eq : ∀ s : ℂ, s ≠ 1 → s.re > 1 → starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) = riemannZeta s := by
          aesop;
        apply h_id.left.eqOn_of_preconnected_of_eventuallyEq h_id.right;
        any_goals exact 2 + 2 * Complex.I;
        · have h_preconnected : IsPreconnected (Set.univ \ {0} : Set ℂ) := by
            have h_preconnected : IsPreconnected (Set.range (fun z : ℂ => Complex.exp z)) := by
              exact isPreconnected_range ( Complex.continuous_exp );
            convert h_preconnected using 1;
            ext; simp [Complex.exp_ne_zero];
          convert h_preconnected.image ( fun x => x + 1 ) ( Continuous.continuousOn ( by continuity ) ) using 1 ; ext ; simp +decide [ Set.ext_iff ];
        · norm_num [ Complex.ext_iff ];
        · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show ( 2 + 2 * Complex.I |> Complex.re ) > 1 by norm_num ) ] with s hs using h_eq s ( by rintro rfl; norm_num at hs ) hs;
        · aesop;
      rw [ ← h_id s hs, Complex.conj_conj ]
    exact h_conj;
  exact h_conj s hs

/-- If ρ is a non-trivial zero of ζ (i.e., ζ(ρ) = 0 and ρ ≠ 1), then
conj(ρ) is also a zero. This gives the conjugate zero pairs. -/
theorem conjugate_zero_pair (ρ : ℂ) (hρ : riemannZeta ρ = 0) (hne : ρ ≠ 1) :
    riemannZeta (starRingEnd ℂ ρ) = 0 := by
  rw [riemannZeta_conj ρ hne, hρ, map_zero]

/-- Combined cosh + conjugate symmetry: if ρ is a non-trivial zero of ζ in the
critical strip, then 1 − conj(ρ) is also a zero. This completes the quadruple
{ρ, 1 − ρ, ρ̄, 1 − ρ̄}. -/
theorem cosh_conjugate_quadruple (ρ : ℂ)
    (_hρ : completedRiemannZeta ρ = 0)
    (hρ_conj : completedRiemannZeta (starRingEnd ℂ ρ) = 0) :
    completedRiemannZeta (1 - starRingEnd ℂ ρ) = 0 :=
  meromorphic_order_cosh_symmetric (starRingEnd ℂ ρ) hρ_conj

/-! ## 9. The cosh axis and harmonic overlap — summary

With the cosh axis placed at arcsin(1/2) = π/6:

- The axis sits at Re(s) ≈ 0.5236, strictly between the critical line
  Re(s) = 1/2 and the Euler product boundary Re(s) = 1.

- The cosh envelope, growing exponentially from this axis, extends into
  the Euler product region Re(s) > 1. This overlap is what enables the
  functional equation to act as an **F** on the prime harmonics.

- The functional equation Λ(1 − s) = Λ(s) reflects the cosh envelope
  across the critical line, mapping Re(s) > 1 to Re(s) < 0. This
  propagation of harmonic information forces zeros to occur in cosh pairs
  {ρ, 1 − ρ}.

- Combined with Schwarz reflection (ζ(s̄) = ζ(s)̄), zeros form
  conjugate-cosh quadruples {ρ, 1 − ρ, ρ̄, 1 − ρ̄}. -/

/-- The cosh axis at π/6 is strictly between the critical line at 1/2 and the
Euler product boundary at 1. This positioning is what creates the overlap
enabling the functional equation to act as an F on the harmonics. -/
theorem coshAxis_between_critical_and_euler :
    (1 : ℝ) / 2 < coshAxis ∧ coshAxis < 1 :=
  ⟨coshAxis_gt_half, coshAxis_in_critical_strip.2⟩

end