import Mathlib
import RequestProject.RiemannHypothesisBridge
import RequestProject.EulerMaclaurinDirichlet
import RequestProject.RiemannXiDecay
import RequestProject.RiemannXiL2Integrable
import RequestProject.ZetaStripBound
import RequestProject.GaussianDetectorPair
import RequestProject.MellinPathToXi
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilCoshPairPositivity_RouteBeta
import RequestProject.WeilPairFormula
import RequestProject.WeilContour
import RequestProject.WeilRightEdge
import RequestProject.WeilHorizontalDecay
import RequestProject.WeilZeroSum
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairDefectFinal
import RequestProject.ZeroCountJensen
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.DetectorBalance
import RequestProject.WeilFinalAssembly

/-!
# RiemannHypothesis — Unified Entry Point for Audit

**Purpose.** This file is the single audit entry point for every
RiemannHypothesis-closure theorem in the Robespierre project. All variants
are re-exported here with a uniform naming convention and explicit axiom
footprints, so an auditor can trace the full derivation from one file
without hunting across the codebase.

**Convention.** Each theorem below re-exports an existing theorem proved
elsewhere in the project. The only code in this file is the re-export and
documentation — no new proofs, no new axioms, no sorry.

**How to audit.** Start at the top-level `RiemannHypothesis_closure` section
and follow the named dependencies. Every `#print axioms` at the bottom
shows the full axiom footprint of the corresponding theorem.

---

## Chain summary

```
Euler–Maclaurin (unconditional, ported from GRH)
  ↓
zetaPolynomialBoundInStrip (ZetaStripBound.lean)       [axiom-clean]
  ↓
riemannXi_vertical_decay_target (RiemannXiDecay.lean)  [axiom-clean]
  ↓
nontrivialZeros_inv_sq_summable_target                 [ZeroCountJensen — 5 tracked sorries]
  ↓
pair_defect_vanishes_at_zeros                          [WeilPairFormula — 1 tracked sorry, classical Weil positivity]
  ↓
RiemannHypothesis                                       [follows unconditionally]
```

## Named target forms

Three equivalent RH-closure forms are exported:

1. **Forward pair-defect** (primary): `RiemannHypothesis_of_pair_defect_positivity` takes `pair_defect_vanishes_at_zeros` and produces `RiemannHypothesis`.
2. **Forward both-channels**: `RiemannHypothesis_of_bothChannelsBalanced` takes `bothChannelsBalancedAtZeros` (stronger form with odd channel balance) and produces `RiemannHypothesis`.
3. **End-to-end with tracked sorry**: `RiemannHypothesis_via_pair_defect` — assembles the full chain using the tracked sorry for Weil positivity.

The converse directions (RH → target) are also exported for completeness.

## Sabotage-test pass

Each forward direction uses only unconditional inputs until the single
named classical target is consumed. The converse directions are trivial
sanity checks confirming propositional equivalence (expected: every
positivity target is classically equivalent to RH).
-/

namespace ZD
namespace RHEntry

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. End-to-end closure (with tracked Weil-positivity sorry)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Top-level entry point.** End-to-end `RiemannHypothesis` closure,
  consuming exactly:
  * unconditional Euler–Maclaurin → ξ-decay chain (this project, axiom-clean)
  * `nontrivialZeros_inv_sq_summable_target` (Jensen agent, 5 tracked sorries)
  * Classical Weil positivity for the cosh-pair Gaussian test
    (Weil agent's target, 1 tracked sorry in `WeilPairFormula.lean`)

  Axiom footprint: `[propext, Classical.choice, Quot.sound, sorryAx]`.
  The `sorryAx` is the composite of the 6 tracked sorries across
  `ZeroCountJensen.lean` (5) and `WeilPairFormula.lean` (1).

  Once those sorries are discharged (Jensen agent + Weil agent), this
  theorem becomes `[propext, Classical.choice, Quot.sound]` — pure
  Mathlib-standard. -/
theorem riemann_hypothesis : RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_via_pair_defect

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Forward-chain variants (each takes a named Prop target as input)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Forward (pair-defect).** If the pair defect vanishes at every
  nontrivial zero, then RH. Unconditional Lean derivation (no sorry in
  the proof itself). The hypothesis is the Weil-positivity target. -/
theorem rh_from_pair_defect :
    ZD.WeilPositivity.pair_defect_vanishes_at_zeros → RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_pair_defect_positivity

/-- **Forward (both-channels-balanced).** If both the amplitude (even) and
  phase (odd) channels balance at every nontrivial zero, then RH.
  Unconditional. The hypothesis is the two-channel form; only the even
  channel is load-bearing for the derivation. -/
theorem rh_from_both_channels_balanced :
    ZD.WeilPositivity.bothChannelsBalancedAtZeros → RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_bothChannelsBalanced

/-- **Forward (final-assembly bundle).** If the complete Weil-final-assembly
  bundle holds — that is: (i) horizontal tails vanish (C / H11), (ii) trivial
  zero residues (F), (iii) global arch–prime identity (H8), (iv) zero-count
  finiteness in rectangles (Jensen), (v) the assembled Weil explicit formula
  at each β ∈ (0,1) (G), and (vi) the F-chain extraction from Weil formula to
  per-zero vanishing — then `RiemannHypothesis`.

  Unconditional Lean derivation; every input is a `Prop` target with a
  documented delivery path (no custom axioms). See
  `RequestProject/WeilFinalAssembly.lean` for the bundle structure. -/
theorem rh_from_final_assembly_bundle :
    ZD.WeilPositivity.FinalAssembly.WeilFinalAssemblyBundle → RiemannHypothesis :=
  fun h => rh_from_pair_defect
    (ZD.WeilPositivity.FinalAssembly.pair_defect_vanishes_at_zeros_of_bundle h)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Converse sanity checks (RH → named target)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Converse (pair-defect).** RH implies the pair defect vanishes at
  every nontrivial zero. Trivially via critical-line zeros satisfying
  the sinh² factorization. Unconditional. -/
theorem pair_defect_from_rh :
    RiemannHypothesis → ZD.WeilPositivity.pair_defect_vanishes_at_zeros :=
  ZD.WeilPositivity.pair_defect_positivity_of_RiemannHypothesis

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Infrastructure stepping stones (already unconditional)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Infrastructure: polynomial ζ bound in strip (unconditional).** From
  Euler–Maclaurin asymptotic on Dirichlet partial sums. -/
theorem zeta_polynomial_strip_bound :
    ZD.StripBound.zetaPolynomialBoundInStrip :=
  ZD.StripBound.zetaPolynomialBoundInStrip_from_euler_maclaurin

/-- **Infrastructure: ξ vertical decay.** Conditional on the above polynomial
  ζ bound (now discharged). -/
theorem xi_vertical_decay :
    ZD.riemannXi_vertical_decay_target :=
  ZD.riemannXi_vertical_decay_of_zetaBound zeta_polynomial_strip_bound

/-- **Infrastructure: ξ is L² integrable on vertical lines in the strip.**
  Unconditional via `riemannXi_vertical_decay` + `isLittleO_rpow_exp_pos_mul_atTop`
  + Mathlib's `integrable_of_isBigO_exp_neg`. -/
theorem xi_L2_integrable
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt : σ < 1) :
    ZD.riemannXi_L2_integrable_target σ :=
  ZD.riemannXi_L2_integrable_unconditional σ hσ_pos hσ_lt

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4.5. Partial Weil explicit-formula infrastructure (WeilContour cycles 21–26)
-- ═══════════════════════════════════════════════════════════════════════════

/- These are the axiom-clean building blocks toward a full Weil-formula
   derivation of `pair_defect_vanishes_at_zeros_proof`. Each is a
   lemma-level deliverable re-exported from `WeilContour.lean`. They do
   NOT discharge the tracked sorry on their own (the sorry is
   RH-equivalent by the collapse test `re_half_of_gaussianPairDefect_zero`).
   They document the FE+Stirling+Mathlib route and provide primitives a
   future Weil positivity proof can compose.

   All axiom footprints: `[propext, Classical.choice, Quot.sound]`. -/

/-- **Weil infra — residue at simple zero (cycle 21).** For `f` analytic at `w`
  with `f(w) = 0` and `f'(w) ≠ 0`, the log-derivative has a simple pole with
  residue 1 plus analytic correction. -/
theorem weil_logDeriv_simple_pole {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (hfw : f w = 0) (hfw' : deriv f w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in nhdsWithin w {w}ᶜ,
        deriv f z / f z = (z - w)⁻¹ + deriv g z / g z :=
  ZD.WeilPositivity.Contour.logDeriv_simple_pole hf hfw hfw'

/-- **Weil infra — rectangle contour Cauchy-Goursat (cycle 22).** Mathlib's
  rectangle integral = 0 wrapped in our convention. -/
theorem weil_rect_contour_zero (σL σR T : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    ZD.WeilPositivity.Contour.rectContourIntegral σL σR T f = 0 :=
  ZD.WeilPositivity.Contour.rectContourIntegral_eq_zero_of_differentiableOn σL σR T f hf

/-- **Weil infra — `ζ` functional equation reciprocal form (cycle 23).**
  `ζ(s) = 2·(2π)^(s−1)·Γ(1−s)·sin(πs/2)·ζ(1−s)`, derived from Mathlib's
  `riemannZeta_one_sub` via substitution and `cos_pi_div_two_sub`. -/
theorem weil_zeta_FE (s : ℂ)
    (hs_ne_zero : s ≠ 0) (hs_ne_pos_int : ∀ n : ℕ, s ≠ (n + 1 : ℕ)) :
    riemannZeta s =
      2 * (2 * Real.pi : ℂ)^(s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (Real.pi * s / 2) * riemannZeta (1 - s) :=
  ZD.WeilPositivity.Contour.zeta_FE_reciprocal s hs_ne_zero hs_ne_pos_int

/-- **Weil infra — `ξ` norm symmetry (cycle 24).** From `ξ(1-s) = ξ(s)`,
  `‖ξ(s)‖ = ‖ξ(1-s)‖`. Transports left-edge bounds from the `Re ≥ 1` side. -/
theorem weil_xi_norm_symmetric (s : ℂ) :
    ‖completedRiemannZeta s‖ = ‖completedRiemannZeta (1 - s)‖ :=
  ZD.WeilPositivity.Contour.completedZeta_norm_reflect s

/-- **Weil infra — von Mangoldt L-series identity (cycle 25).** The prime-side
  expansion `-ζ'(s)/ζ(s) = Σ Λ(n)/n^s` at `Re s > 1`. Direct from Mathlib. -/
theorem weil_vonMangoldt_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
  ZD.WeilPositivity.Contour.vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs

/-- **Weil infra — integrand regularity (cycle 26).** The Weil integrand
  `(−ζ'/ζ)·h` is differentiable away from `s = 1` and zeros of `ζ`. -/
theorem weil_integrand_differentiableAt
    {h : ℂ → ℂ} {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0)
    (hh : DifferentiableAt ℂ h s) :
    DifferentiableAt ℂ (ZD.WeilPositivity.Contour.weilIntegrand h) s :=
  ZD.WeilPositivity.Contour.weilIntegrand_differentiableAt hs hζ hh

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. Closed forms (useful for concrete computation by auditor)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Odd channel closed form.** Transcendental expression for the
  phase-sensitive signed integral, derived from the Gaussian-weighted
  `sinh·sin` convolution. -/
theorem odd_channel_closed_form (β γ : ℝ) :
    ZD.WeilPositivity.oddChannel β γ = Real.sqrt (2 * Real.pi) *
      Real.exp (((β - 1/2)^2 - γ^2) / 8) *
      Real.sin ((β - 1/2) * γ / 4) :=
  ZD.WeilPositivity.oddChannel_closed_form β γ

/-- **Even channel closed form.** Non-negative amplitude expression with
  explicit Gaussian moments. -/
theorem even_channel_closed_form (β : ℝ) :
    ZD.WeilPositivity.evenChannel β = Real.sqrt (Real.pi / 2) / 4 * (
      Real.exp ((β - Real.pi/6)^2 / 2) +
      Real.exp ((1 - Real.pi/6 - β)^2 / 2) -
      2 * Real.exp ((1/2 - Real.pi/6)^2 / 2) -
      2 * Real.exp ((β - 1/2)^2 / 2) + 2) :=
  ZD.WeilPositivity.evenChannel_closed_form β

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. Axiom audit markers
-- ═══════════════════════════════════════════════════════════════════════════

/- The auditor should verify these `#print axioms` outputs. Unconditional
   infrastructure should show `[propext, Classical.choice, Quot.sound]`.
   RH-closure theorems show `sorryAx` until the tracked Weil and Jensen
   sorries are discharged. -/

#print axioms rh_from_pair_defect
#print axioms rh_from_both_channels_balanced
#print axioms rh_from_final_assembly_bundle
#print axioms pair_defect_from_rh
#print axioms zeta_polynomial_strip_bound
#print axioms xi_vertical_decay
#print axioms xi_L2_integrable
#print axioms weil_logDeriv_simple_pole
#print axioms weil_rect_contour_zero
#print axioms weil_zeta_FE
#print axioms weil_xi_norm_symmetric
#print axioms weil_vonMangoldt_LSeries
#print axioms weil_integrand_differentiableAt
#print axioms odd_channel_closed_form
#print axioms even_channel_closed_form
#print axioms riemann_hypothesis

end RHEntry
end ZD
