import Mathlib
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.WeilIdentityAtPairTest
import RequestProject.PairTestRectangleCauchy
import RequestProject.WeilHadamardBoundaryDecomposition
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.ArchKernelRectCauchy
import RequestProject.ArchKernelRectCauchyTransport

/-!
# Explicit-formula placeholder for the cosh-pair Gauss test

Isolates the **classical Weil explicit formula** specialised to the
cosh-pair Gauss test as a single named placeholder
`weil_explicit_formula_cosh_pair_target`, and discharges the
(now ε-relaxed) target
`archIntegrand_interval_eq_left_edge_integral_target` conditional on it.

## Why this isolation

The strict finite-T form of `archIntegrand_interval_eq_left_edge_integral_target`
was not provable from existing axiom-clean infrastructure: rectangle Cauchy
on `[-1, 2] × [-T, T]` produces, in addition to the boundary-form
decomposition, a per-zero residue contribution
`Σ_{ρ} n(ρ)·pairTestMellin β ρ` over nontrivial zeros inside the rectangle.
The horizontal piece vanishes asymptotically and the
`pairTestMellin β 1 = gaussianPairDefect β` pole-at-1 residue collapses via
`pair_axes_sum`, but the per-zero sum carries the actual explicit-formula
content for the cosh-pair test — the open H3 closure target tracked in
`session_goal_explicit_formula.md`.

The target was weakened to its limit (ε-relaxed) form in
`WeilFinalAssemblyUnconditional.lean`. This file:

* Names the residue↔reflected-prime bridge as
  `weil_explicit_formula_cosh_pair_target β`, in its strongest natural
  form (whole-line equality of the two integrands).
* Provides the integrability bridge
  `leftEdge_weilIntegrand_pairTestMellin_integrable` from
  `PairTestIdentity.leftEdge_pairTestMellin_integrable` via the
  unconditional pointwise FE rewrite on the line `Re = -1`.
* Proves the conditional discharge
  `archIntegrand_interval_eq_left_edge_integral_target_of_explicit_formula`
  via `MeasureTheory.intervalIntegral_tendsto_integral` applied to both
  whole-line integrals.

The remaining open obligation — discharging
`weil_explicit_formula_cosh_pair_target` itself — is the H3-closure
explicit-formula content.
-/

open Complex MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

/-- **Explicit-formula content placeholder for the pair-cosh-Gauss test.**
The classical Weil explicit formula specialised to the cosh-pair Gauss
test, in its strongest natural whole-line form: the integrated arch
integrand on `σ = 2` equals the integrated left-edge `weilIntegrand` on
`σ = -1`. Discharging this is the open H3-closure content. -/
def weil_explicit_formula_cosh_pair_target (β : ℝ) : Prop :=
  (∫ y : ℝ, Contour.archIntegrand β 2 y) =
    ∫ y : ℝ,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)

/-- Pointwise FE rewrite of `weilIntegrand (pairTestMellin β)` on the
left edge `Re s = -1`. Unconditional: every side condition holds for all
real `y` (no zeros of `ζ` on the line `Re = -1`; the trivial zeros sit at
`-2, -4, …`). Mirrors the `hleft` block of
`rectContourIntegral_weilIntegrand_pairTestMellin_eq_boundary_forms_with_origin_neg_one`. -/
private theorem weilIntegrand_pairTestMellin_left_edge_eq_hadamardArchBoundaryTerm
    (β : ℝ) (y : ℝ) :
    Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)
      = Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
  set z : ℂ := (((-1 : ℝ) : ℂ)) + (y : ℂ) * I with hz_def
  have hz_re : z.re = -1 := by simp [z]
  have hz_im : z.im = y := by simp [z]
  have hz0 : z ≠ 0 := by
    intro hz0
    have hre : z.re = (0 : ℂ).re := by rw [hz0]
    rw [hz_re] at hre; norm_num at hre
  have hz1 : z ≠ 1 := by
    intro hz1
    have hre : z.re = (1 : ℂ).re := by rw [hz1]
    rw [hz_re] at hre; norm_num at hre
  have hζz : riemannZeta z ≠ 0 := by
    by_cases hy0 : y = 0
    · have hz_eq : z = -1 := by
        apply Complex.ext
        · simp [hz_re]
        · simp [hz_im, hy0]
      rw [hz_eq]
      have h := riemannZeta_neg_nat_eq_bernoulli 1
      have hcast : ((-(1 : ℕ) : ℂ)) = (-1 : ℂ) := by push_cast; ring
      rw [hcast] at h
      rw [h]
      push_cast [bernoulli_two]
      norm_num
    · apply riemannZeta_ne_zero_of_re_neg_of_not_neg_int
      · rw [hz_re]; norm_num
      · intro n hn
        have him : z.im = (-↑n : ℂ).im := by rw [hn]
        rw [hz_im] at him
        simp at him
        exact hy0 him
  have h1z_re : (1 - z).re = 2 := by simp [z]; norm_num
  have hζ1z : riemannZeta (1 - z) ≠ 0 := by
    apply Contour.zeta_ne_zero_of_one_lt_re
    rw [h1z_re]; norm_num
  have hΓz : z.Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : z.re = (-(2 * (n : ℂ))).re := by rw [hn]
    rw [hz_re] at hre
    simp at hre
    have h_int : (2 * n : ℤ) = 1 := by
      exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
    omega
  have hΓ1z : (1 - z).Gammaℝ ≠ 0 := by
    apply Contour.gammaℝ_ne_zero_of_re_pos
    rw [h1z_re]; norm_num
  have h_arch :=
    Contour.weilIntegrand_arch_decomposition (h := Contour.pairTestMellin β) (s := z)
      hz0 hz1 hζz hζ1z hΓz hΓ1z
  simpa [z, Contour.hadamardArchBoundaryTerm] using h_arch

/-- Integrability of `weilIntegrand (pairTestMellin β) (-1+iy)` on ℝ.
Bridges from `PairTestIdentity.leftEdge_pairTestMellin_integrable` via the
unconditional pointwise FE rewrite. -/
theorem leftEdge_weilIntegrand_pairTestMellin_integrable (β : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ =>
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  refine (PairTestIdentity.leftEdge_pairTestMellin_integrable β).congr
    (MeasureTheory.ae_of_all _ ?_)
  intro y
  exact (weilIntegrand_pairTestMellin_left_edge_eq_hadamardArchBoundaryTerm β y).symm

/-- Discharge of the (ε-form) interval identity from the explicit-formula
placeholder. Both `archIntegrand β 2` and the left-edge `weilIntegrand` are
integrable on ℝ, so each truncated `[-T, T]` integral converges to its
whole-line integral; the two whole-line integrals are equal by hypothesis,
so the difference of truncated integrals tends to `0`. -/
theorem archIntegrand_interval_eq_left_edge_integral_target_of_explicit_formula
    (β : ℝ) (h : weil_explicit_formula_cosh_pair_target β) :
    archIntegrand_interval_eq_left_edge_integral_target β := by
  intro ε hε
  have h_arch_int : MeasureTheory.Integrable (Contour.archIntegrand β 2) :=
    Contour.archIntegrand_integrable_at_two β
  have h_left_int : MeasureTheory.Integrable (fun y : ℝ =>
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) :=
    leftEdge_weilIntegrand_pairTestMellin_integrable β
  have h_arch_tendsto :
      Filter.Tendsto
        (fun T : ℝ => ∫ y : ℝ in (-T)..T, Contour.archIntegrand β 2 y)
        Filter.atTop
        (nhds (∫ y : ℝ, Contour.archIntegrand β 2 y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral h_arch_int
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have h_left_tendsto :
      Filter.Tendsto
        (fun T : ℝ => ∫ y : ℝ in (-T)..T,
            Contour.weilIntegrand (Contour.pairTestMellin β)
              ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
        Filter.atTop
        (nhds (∫ y : ℝ,
          Contour.weilIntegrand (Contour.pairTestMellin β)
            ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral h_left_int
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have h_diff_tendsto :
      Filter.Tendsto
        (fun T : ℝ =>
          (∫ y : ℝ in (-T)..T, Contour.archIntegrand β 2 y) -
          (∫ y : ℝ in (-T)..T, Contour.weilIntegrand (Contour.pairTestMellin β)
              ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)))
        Filter.atTop (nhds (0 : ℂ)) := by
    have h_sub := h_arch_tendsto.sub h_left_tendsto
    have h_zero :
        (∫ y : ℝ, Contour.archIntegrand β 2 y) -
            (∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
              ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) = 0 := by
      rw [h]; ring
    rwa [h_zero] at h_sub
  have h_ball : Metric.ball (0 : ℂ) ε ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds _ hε
  have h_eventually := h_diff_tendsto.eventually h_ball
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨T₁, hT₁⟩ := h_eventually
  refine ⟨max T₁ 1, by positivity, ?_⟩
  intro T hT _hGood
  have hT_ge_T₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have h_close := hT₁ T hT_ge_T₁
  simpa [dist_eq_norm] using h_close

/-! ## Route 2 — bridge the residue side to `∫reflectedPrime`

The user's "Plancherel/Parseval bridge" recast in concrete terms. The
existing infrastructure (`primeIntegrand_integral_eq_prime_sum` for the
prime side, `verticalEdgeDifference_limit` for the residue side) lets us
reformulate `weil_explicit_formula_cosh_pair_target` as the concrete
identity
```
∫_ℝ reflectedPrimeIntegrand β 2 = 2π · (pairTestMellin β 1 − Σ' residues)
```
i.e., the integrated reflected-prime kernel equals 2π times the
"residue defect" (pole-at-1 residue minus per-zero residue sum). This
**is** the classical Weil explicit formula identity for the cosh-pair
test; the equivalence with `weil_explicit_formula_cosh_pair_target` is
proved unconditionally below. The remaining open content is then the
single concrete identity in `weil_explicit_formula_cosh_pair_residue_form`.
-/

/-- **Algebraic right-edge split under integration.** From the proved
pointwise right-edge split `weilIntegrand_pair_right_edge_two_split` and
integrability of all three integrands at `σ = 2`, integrating gives
`∫prime = ∫arch + ∫reflectedPrime` on `ℝ`.

Combined with `primeIntegrand_integral_eq_prime_sum β 2`, the right-hand
side is the von-Mangoldt sum `2π·∑'_n Λ(n)·pair_cosh_gauss_test β n`. -/
theorem archIntegrand_plus_reflectedPrime_integral_eq_prime_sum (β : ℝ) :
    (∫ y : ℝ, Contour.archIntegrand β 2 y) +
        (∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y)
      = 2 * (Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  have h_prime_sum := Contour.primeIntegrand_integral_eq_prime_sum β 2 (by norm_num : (1:ℝ) < 2)
  have h_arch_int : MeasureTheory.Integrable (Contour.archIntegrand β 2) :=
    Contour.archIntegrand_integrable_at_two β
  have h_ref_int : MeasureTheory.Integrable (Contour.reflectedPrimeIntegrand β 2) :=
    Contour.reflectedPrimeIntegrand_integrable_at_two β
  have h_ptw : ∀ y : ℝ,
      Contour.primeIntegrand β 2 y
        = Contour.archIntegrand β 2 y + Contour.reflectedPrimeIntegrand β 2 y := by
    intro y
    have h_split := weilIntegrand_pair_right_edge_two_split β y
    have h_weil_eq : Contour.weilIntegrand (Contour.pairTestMellin β)
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) = Contour.primeIntegrand β 2 y :=
      Contour.weilIntegrand_eq_primeIntegrand_on_right_edge β
        (by norm_num : (1:ℝ) < 2) y
    rw [← h_weil_eq]; exact h_split
  have h_split_int : (∫ y : ℝ, Contour.primeIntegrand β 2 y)
      = (∫ y : ℝ, Contour.archIntegrand β 2 y) +
        (∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y) := by
    rw [show (fun y : ℝ => Contour.primeIntegrand β 2 y) =
        (fun y => Contour.archIntegrand β 2 y +
                  Contour.reflectedPrimeIntegrand β 2 y) from funext h_ptw]
    exact MeasureTheory.integral_add h_arch_int h_ref_int
  rw [← h_split_int]
  exact h_prime_sum

/-- **Whole-line left-edge weil-integrand integral equals the
explicit-formula expression.** The (♣) identity bridging the left-edge
weil integral to the prime sum, the s=1 pole residue, and the per-zero
residue sum.

Combines:
* `weilIntegrand_pairTestMellin_left_edge_eq_hadamardArchBoundaryTerm`
  (pointwise FE rewrite);
* `PairTestIdentity.verticalEdgeDifference_limit` (boundary-form
  difference → residue side, in ε-form along good heights);
* `PairTestIdentity.rightEdge_integral_tendsto`,
  `PairTestIdentity.leftEdge_integral_tendsto` (whole-line integral
  convergence along `atTop`);
* `Contour.primeIntegrand_integral_eq_prime_sum` (whole-line prime side).

The limit-uniqueness step combines the `atTop`-convergence of the
boundary-form difference with the `atTop ⊓ {goodHeight}`-convergence from
`verticalEdgeDifference_limit`, using `exists_goodHeight_strong_ge` for
nontriviality of the subfilter. -/
theorem weilIntegrand_left_edge_integral_value
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
      = 2 * (Real.pi : ℂ) *
        ((∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ))
         - Contour.pairTestMellin β 1
         + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (((Classical.choose
                (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
                : ℕ) : ℂ)) *
              Contour.pairTestMellin β ρ.val) := by
  -- Bridge weilIntegrand ↔ hadamardArchBoundaryTerm·pairTest on the left edge.
  have h_int_eq : (∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
        = ∫ y : ℝ, Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
            Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact weilIntegrand_pairTestMellin_left_edge_eq_hadamardArchBoundaryTerm β y
  rw [h_int_eq]
  -- Abbreviations.
  set L : ℂ := ∫ y : ℝ, Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
                Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hL_def
  set P : ℂ := ∫ y : ℝ, Contour.primeIntegrand β 2 y with hP_def
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) with hS_def
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
          : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val with hSres_def
  -- Goal: L = 2π·(S - pairTestMellin β 1 + Sres).
  -- Step 1: P = 2π·S.
  have hP_eq : P = 2 * (Real.pi : ℂ) * S :=
    Contour.primeIntegrand_integral_eq_prime_sum β 2 (by norm_num : (1:ℝ) < 2)
  -- Step 2: f(T) := I·∫_{-T}^T prime - I·∫_{-T}^T arch_bdy_form converges to I·P - I·L
  -- along atTop (via rightEdge + leftEdge tendstos).
  have h_prime_tendsto :
      Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, Contour.primeIntegrand β 2 y)
        Filter.atTop (nhds P) := PairTestIdentity.rightEdge_integral_tendsto β
  have h_left_tendsto :
      Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T,
          Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
        Filter.atTop (nhds L) := PairTestIdentity.leftEdge_integral_tendsto β
  -- Bridge: rightEdge integrand in LSeries form = primeIntegrand pointwise.
  have h_right_form_eq : ∀ T : ℝ,
      (∫ y : ℝ in (-T)..T,
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((2 : ℂ) + (y : ℂ) * I) *
            Contour.pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T)..T, Contour.primeIntegrand β 2 y := by
    intro T
    apply intervalIntegral.integral_congr
    intro y _
    exact PairTestIdentity.rightEdge_integrand_eq_primeIntegrand β y
  -- Combined tendsto along atTop: f(T) → I·P - I·L.
  have h_diff_tendsto_atTop :
      Filter.Tendsto (fun T : ℝ =>
        I • (∫ y : ℝ in (-T)..T,
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                ((2 : ℂ) + (y : ℂ) * I) *
              Contour.pairTestMellin β ((2 : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in (-T)..T,
          Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)))
        Filter.atTop (nhds (I • P - I • L)) := by
    have h_prime_tendsto' :
        Filter.Tendsto (fun T : ℝ =>
            ∫ y : ℝ in (-T)..T,
              LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  ((2 : ℂ) + (y : ℂ) * I) *
                Contour.pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))
          Filter.atTop (nhds P) := by
      refine h_prime_tendsto.congr' ?_
      filter_upwards with T
      exact (h_right_form_eq T).symm
    exact (h_prime_tendsto'.const_smul I).sub (h_left_tendsto.const_smul I)
  -- Step 3: f(T) → 2πi·(pairTestMellin β 1 - Sres) along atTop ⊓ {goodHeight}.
  set R : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I * (Contour.pairTestMellin β 1 - Sres)
    with hR_def
  have h_diff_tendsto_subfilter :
      Filter.Tendsto (fun T : ℝ =>
        I • (∫ y : ℝ in (-T)..T,
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                ((2 : ℂ) + (y : ℂ) * I) *
              Contour.pairTestMellin β ((2 : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in (-T)..T,
          Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)))
        (Filter.atTop ⊓ Filter.principal {T : ℝ | goodHeight T}) (nhds R) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_inf_principal]
    obtain ⟨T₀, _, hT₀⟩ := PairTestIdentity.verticalEdgeDifference_limit β hβ ε hε
    filter_upwards [Filter.eventually_ge_atTop T₀] with T hT_ge hT_good
    rw [dist_eq_norm]
    exact hT₀ T hT_ge hT_good
  -- Subfilter NeBot via exists_goodHeight_strong_ge.
  haveI h_neBot : (Filter.atTop ⊓ Filter.principal {T : ℝ | goodHeight T}).NeBot := by
    rw [← Filter.frequently_iff_neBot, Filter.frequently_atTop]
    intro a
    obtain ⟨T, hT_ge, hT_good⟩ := exists_goodHeight_strong_ge a
    exact ⟨T, hT_ge, hT_good⟩
  -- Step 4: Uniqueness of limits along the subfilter.
  have hkey : I • P - I • L = R :=
    tendsto_nhds_unique
      (h_diff_tendsto_atTop.mono_left (inf_le_left :
        (Filter.atTop : Filter ℝ) ⊓ Filter.principal {T : ℝ | goodHeight T} ≤ Filter.atTop))
      h_diff_tendsto_subfilter
  -- Step 5: Solve for L. From I·P - I·L = R, derive L = P + I·R via mul_left_cancel
  -- by I, then substitute P = 2π·S and compute I·R using I*I = -1.
  have hI2 : I * I = -1 := Complex.I_mul_I
  have hL_eq : L = P + I * R := by
    have h_eq : I * P - I * L = R := by
      have h := hkey; simp only [smul_eq_mul] at h; exact h
    have h_target_mul : I * (P + I * R) = I * P - R := by
      have h1 : I * (P + I * R) = I * P + I * I * R := by ring
      rw [h1, hI2]; ring
    have h_IL_eq : I * L = I * P - R := by linear_combination -h_eq
    exact mul_left_cancel₀ Complex.I_ne_zero (h_IL_eq.trans h_target_mul.symm)
  have hIR_eq : I * R =
      2 * (Real.pi : ℂ) * Sres - 2 * (Real.pi : ℂ) * Contour.pairTestMellin β 1 := by
    rw [hR_def]
    have h1 : I * (2 * ((Real.pi : ℝ) : ℂ) * I * (Contour.pairTestMellin β 1 - Sres))
        = (I * I) * (2 * (Real.pi : ℂ)) * (Contour.pairTestMellin β 1 - Sres) := by ring
    rw [h1, hI2]; ring
  rw [hL_eq, hP_eq, hIR_eq]; ring

/-- **Residue form of the explicit-formula content placeholder.**
The whole-line reflected-prime integral equals `2π` times the
"residue defect" (pole-at-1 residue minus the per-zero residue sum).
Equivalent to `weil_explicit_formula_cosh_pair_target β` for
`β ∈ (0, 1)`, by `weil_explicit_formula_cosh_pair_target_iff_residue_form`. -/
def weil_explicit_formula_cosh_pair_residue_form (β : ℝ) : Prop :=
  (∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y)
    = 2 * (Real.pi : ℂ) *
      (Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
            : ℕ) : ℂ)) *
          Contour.pairTestMellin β ρ.val)

/-- **Equivalence of the two named forms of the explicit-formula
placeholder.** For `β ∈ (0, 1)`, the original whole-line equality
`∫arch β 2 = ∫weil(pairTest β)(-1+iy)` is equivalent to the residue-form
`∫reflectedPrime β 2 = 2π·(pairTestMellin β 1 - Σ residues)`.

Proof: by `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum`,
`∫arch + ∫reflected = 2π·prime_sum`. By
`weilIntegrand_left_edge_integral_value`,
`∫weil(-1+iy) = 2π·(prime_sum - pairTestMellin β 1 + Σ residues)`.
Subtracting: `∫arch - ∫weil(-1+iy) = 2π·pairTestMellin β 1 - 2π·Σ residues - ∫reflected`.
The target identity is `∫arch = ∫weil(-1+iy)`, equivalent to
`∫reflected = 2π·(pairTestMellin β 1 - Σ residues)`. -/
theorem weil_explicit_formula_cosh_pair_target_iff_residue_form
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    weil_explicit_formula_cosh_pair_target β
      ↔ weil_explicit_formula_cosh_pair_residue_form β := by
  unfold weil_explicit_formula_cosh_pair_target weil_explicit_formula_cosh_pair_residue_form
  have h_split := archIntegrand_plus_reflectedPrime_integral_eq_prime_sum β
  have h_left := weilIntegrand_left_edge_integral_value β hβ
  set A : ℂ := ∫ y : ℝ, Contour.archIntegrand β 2 y with hA_def
  set Refl : ℂ := ∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y with hRefl_def
  set W : ℂ := ∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
                ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hW_def
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) with hS_def
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
          : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val with hSres_def
  -- h_split : A + Refl = 2π·S
  -- h_left  : W = 2π·(S - pairTestMellin β 1 + Sres)
  constructor
  · intro h_AW   -- A = W
    -- Goal: Refl = 2π·(pairTestMellin β 1 - Sres)
    have : A + Refl - W = 2 * (Real.pi : ℂ) * S - 2 * (Real.pi : ℂ) *
              (S - Contour.pairTestMellin β 1 + Sres) := by
      rw [h_split, h_left]
    have h_simp : A + Refl - W = Refl := by rw [h_AW]; ring
    rw [h_simp] at this
    linear_combination this
  · intro h_Refl  -- Refl = 2π·(pairTestMellin β 1 - Sres)
    -- Goal: A = W
    have : A = (2 * (Real.pi : ℂ) * S) - Refl := by linear_combination h_split
    rw [this, h_Refl, h_left]
    ring

/-! ## Route 2 attack — discharging `archDiff` via horizontal vanishing

`F_rectContourIntegral_value` (axiom-clean, in `ArchKernelRectCauchy`) gives the
**finite-T** rect contour integral value:
```
rectContourIntegral (-1) 2 T (archKernel · pairTest β) = 2πi · (-pairTest β 0 + gaussianPairDefect β)
```
By the four-edge expansion and tendsto of vertical edges, the only missing piece
is **horizontal vanishing** for `archKernel · pairTest β` at `Im = ±T`.

This section delivers:

* `archKernel_pairTest_horizontal_vanishes_target β` — named horizontal-vanishing
  obligation.
* `archIntegrand_diff_at_two_minus_neg_one_holds_of_horizontal_vanishes` —
  conditional discharge: horizontal vanishing → arch-difference identity at the
  whole-line limit. This is the **corrected** version of
  `ZD.ArchKernelRectCauchyTransport.archDiff_eq_residue_sum_target` (which has
  a spurious factor of `I`; see the docstring on the corrected statement).

NOTE on the existing `archDiff_eq_residue_sum_target` def
(`ArchKernelRectCauchyTransport.lean:83`): its RHS is `2π·I·(…)` but the correct
identity is `2π·(…)` — the rect contour integral equals `2πi·(residue sum)`, and
dividing by the `I` from the vertical-edge prefactor leaves only `2π`. The buggy
def has no consumers in the repo (verified). We use the corrected statement here.
-/

/-- Horizontal vanishing for `archKernel · pairTest β` at `Im = ±T`,
along atTop with goodHeight side-condition. -/
def archKernel_pairTest_horizontal_vanishes_target (β : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖(∫ x : ℝ in (-1 : ℝ)..2,
        ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
          ((x : ℂ) + (-T : ℝ) * I)) -
        (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℝ) * I))‖ < ε

/-- **Corrected (♥) identity**: `(∫arch β 2) - (∫arch β -1) = 2π·(-pairTest β 0 + gaussianPairDefect β)`.
This is the limit-form of `F_rectContourIntegral_value` after dividing through
by the `I` factor on the vertical-edge prefactor. No extra `I` on the RHS
(unlike the buggy `archDiff_eq_residue_sum_target` def). -/
def archIntegrand_diff_at_two_minus_neg_one_target (β : ℝ) : Prop :=
  (∫ t : ℝ, Contour.archIntegrand β 2 t) -
      (∫ y : ℝ, Contour.archIntegrand β (-1) y) =
    2 * ((Real.pi : ℝ) : ℂ) *
      ((-Contour.pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ))

/-- **Conditional discharge of the corrected (♥) identity** from horizontal
vanishing. Combines `F_rectContourIntegral_value` with vertical tendstos
(via `archIntegrand_at_two_integrable`, `archIntegrand_at_neg_one_integrable`),
horizontal vanishing on the subfilter `atTop ⊓ {goodHeight}`, and
`tendsto_nhds_unique`. -/
theorem archIntegrand_diff_at_two_minus_neg_one_of_horizontal_vanishes
    (β : ℝ) (h_horiz : archKernel_pairTest_horizontal_vanishes_target β) :
    archIntegrand_diff_at_two_minus_neg_one_target β := by
  -- Abbreviations.
  set R : ℂ :=
      (-Contour.pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ) with hR_def
  set Aplus : ℂ := ∫ t : ℝ, Contour.archIntegrand β 2 t with hAplus_def
  set Aminus : ℂ := ∫ y : ℝ, Contour.archIntegrand β (-1) y with hAminus_def
  -- Goal: Aplus - Aminus = 2π · R.
  show Aplus - Aminus = 2 * ((Real.pi : ℝ) : ℂ) * R
  -- Strategy: show I·(Aplus - Aminus) = 2πI·R, then cancel I.
  -- Step 1: vertical tendstos along atTop.
  have h_arch_int_pos : MeasureTheory.Integrable (Contour.archIntegrand β 2) :=
    Contour.archIntegrand_integrable_at_two β
  have h_arch_int_neg : MeasureTheory.Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_pos_tendsto :
      Filter.Tendsto (fun T : ℝ => ∫ t : ℝ in (-T)..T, Contour.archIntegrand β 2 t)
        Filter.atTop (nhds Aplus) :=
    MeasureTheory.intervalIntegral_tendsto_integral h_arch_int_pos
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have h_neg_tendsto :
      Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, Contour.archIntegrand β (-1) y)
        Filter.atTop (nhds Aminus) :=
    MeasureTheory.intervalIntegral_tendsto_integral h_arch_int_neg
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  -- Step 2: vertical-edge form of F using F_at_two and F_at_neg_one bridges.
  have h_right_form : ∀ T : ℝ,
      (∫ y : ℝ in (-T)..T,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            (((2 : ℝ) : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T)..T, Contour.archIntegrand β 2 y := by
    intro T
    apply intervalIntegral.integral_congr
    intro y _
    exact ZD.ArchKernelRectCauchyTransport.F_at_two_eq_archIntegrand β y
  have h_left_form : ∀ T : ℝ,
      (∫ y : ℝ in (-T)..T,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ in (-T)..T, Contour.archIntegrand β (-1) y := by
    intro T
    apply intervalIntegral.integral_congr
    intro y _
    have h := ZD.ArchKernelRectCauchyTransport.F_at_neg_one_eq_archIntegrand β y
    have h_eq : (((-1 : ℝ) : ℂ) : ℂ) = (-1 : ℂ) := by push_cast; rfl
    rw [h_eq]; exact h
  -- Step 3: define f(T) = (bottom_T - top_T) + I·(right_T - left_T) = rect_T.
  -- By F_rectContourIntegral_value, f(T) = 2πi·R for all T > 0.
  -- Hence I·(right_T - left_T) = 2πi·R - (bottom_T - top_T).
  set Rfull : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * R with hRfull_def
  set f : ℝ → ℂ := fun T =>
    I • ((∫ y : ℝ in (-T)..T, Contour.archIntegrand β 2 y) -
         (∫ y : ℝ in (-T)..T, Contour.archIntegrand β (-1) y))
    with hf_def
  -- f(T) → I·(Aplus - Aminus) along atTop (via vertical tendstos).
  have h_f_atTop :
      Filter.Tendsto f Filter.atTop (nhds (I • (Aplus - Aminus))) := by
    simp only [hf_def]
    exact (h_pos_tendsto.sub h_neg_tendsto).const_smul I
  -- f(T) → I·(2π·R) = 2πI·R = Rfull*I along atTop ⊓ {goodHeight} (via h_horiz).
  -- Compute: f(T) = rect_T - (bottom_T - top_T) = 2πi·R - (bottom_T - top_T).
  have h_f_eq : ∀ T : ℝ, 0 < T → f T =
      2 * ((Real.pi : ℝ) : ℂ) * I * R -
      ((∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (-T : ℝ) * I)) -
        (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℝ) * I))) := by
    intro T hT_pos
    have h_rect := ZD.ArchKernelRectCauchy.F_rectContourIntegral_value β hT_pos
    -- Unfold rectContourIntegral
    simp only [Contour.rectContourIntegral] at h_rect
    -- h_rect: (bottom - top) + I•right - I•left = 2πi·R
    -- Rearrange to: I•(right - left) = 2πi·R - (bottom - top)
    -- Substitute h_right_form and h_left_form into the right/left of h_rect.
    rw [h_right_form T, h_left_form T] at h_rect
    simp only [hf_def, hR_def]
    have h_smul_sub : I • ((∫ y in (-T:ℝ)..T, Contour.archIntegrand β 2 y) -
        (∫ y in (-T:ℝ)..T, Contour.archIntegrand β (-1) y)) =
        I • (∫ y in (-T:ℝ)..T, Contour.archIntegrand β 2 y) -
        I • (∫ y in (-T:ℝ)..T, Contour.archIntegrand β (-1) y) := by
      rw [smul_sub]
    rw [h_smul_sub]
    linear_combination h_rect
  -- Tendsto along subfilter for f.
  set Rtarg : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I * R with hRtarg_def
  have h_f_subfilter :
      Filter.Tendsto f
        (Filter.atTop ⊓ Filter.principal {T : ℝ | goodHeight T})
        (nhds Rtarg) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_inf_principal]
    obtain ⟨T_h, hT_h_pos, hT_h⟩ := h_horiz ε hε
    filter_upwards [Filter.eventually_ge_atTop (max T_h 1)] with T hT_ge hT_good
    have hT_pos : (0 : ℝ) < T := by
      have h1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT_ge
      linarith
    have hT_ge_T_h : T_h ≤ T := le_trans (le_max_left _ _) hT_ge
    rw [dist_eq_norm]
    rw [h_f_eq T hT_pos]
    rw [show (2 * ((Real.pi : ℝ) : ℂ) * I * R) -
        ((∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (T : ℝ) * I))) - Rtarg =
        -((∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (T : ℝ) * I))) from by rw [hRtarg_def]; ring]
    rw [norm_neg]
    exact hT_h T hT_ge_T_h hT_good
  -- NeBot of subfilter.
  haveI h_neBot : (Filter.atTop ⊓ Filter.principal {T : ℝ | goodHeight T}).NeBot := by
    rw [← Filter.frequently_iff_neBot, Filter.frequently_atTop]
    intro a
    obtain ⟨T, hT_ge, hT_good⟩ := exists_goodHeight_strong_ge a
    exact ⟨T, hT_ge, hT_good⟩
  -- Apply uniqueness of limits along subfilter.
  have h_unique : I • (Aplus - Aminus) = Rtarg :=
    tendsto_nhds_unique
      (h_f_atTop.mono_left (inf_le_left :
        (Filter.atTop : Filter ℝ) ⊓ Filter.principal {T : ℝ | goodHeight T} ≤ Filter.atTop))
      h_f_subfilter
  -- Cancel I: I·(Aplus - Aminus) = 2πI·R ⟹ Aplus - Aminus = 2π·R.
  have hI2 : I * I = -1 := Complex.I_mul_I
  have h_target_mul : I * (2 * ((Real.pi : ℝ) : ℂ) * R) = Rtarg := by
    rw [hRtarg_def]; ring
  have h_IL_eq : I * (Aplus - Aminus) = Rtarg := by
    have h := h_unique
    simp only [smul_eq_mul] at h
    exact h
  exact mul_left_cancel₀ Complex.I_ne_zero (h_IL_eq.trans h_target_mul.symm)

/-! ## Discharge of `archKernel_pairTest_horizontal_vanishes_target` (the open piece)

Strategy: bound `‖archKernel·pairTest β‖` pointwise on `σ ∈ (-1, 2]` at goodHeight
`T ≥ T₀` via the FE rewrite `archKernel(s) = -ζ'/ζ(s) - ζ'/ζ(1-s)` plus
`full_strip_logDerivZeta_bound_N_lt_4_unconditional`/`_neg` plus
`uniform_pairMellin_quartic_target_pos`/`_neg`. Integrate over σ to bound the
horizontal integrals by `K · T^(N-4) → 0`.
-/

/-- ζ non-vanishing on the line `Im s = T` for `σ ∈ [-1, 2]` at goodHeight T. -/
private lemma zeta_ne_zero_strip_top {σ T : ℝ}
    (hσ_mem : σ ∈ Set.Icc (-1:ℝ) 2) (hT_pos : 0 < T) (hGood : goodHeight T) :
    riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = T := by simp [s]
  by_cases h_lt_one : σ < 1
  · by_cases h_pos : 0 < σ
    · -- σ ∈ (0, 1): nontrivial-zero candidate; goodHeight forbids Im = T.
      intro hζ
      have h_nt : s ∈ NontrivialZeros :=
        ⟨by show 0 < s.re; rw [hs_re]; exact h_pos,
         by show s.re < 1; rw [hs_re]; exact h_lt_one,
         hζ⟩
      have h_im_ne_T := (hGood.1 s h_nt).1
      rw [hs_im] at h_im_ne_T; exact h_im_ne_T rfl
    · -- σ ≤ 0: use ξ(s) = ξ(1-s) and ζ(1-s) ≠ 0 on Re ≥ 1.
      push_neg at h_pos
      have h1ms_re_ge : (1 : ℝ) ≤ (1 - s).re := by
        show (1 : ℝ) ≤ (1 - s).re
        have : (1 - s).re = 1 - σ := by simp [s]
        rw [this]; linarith
      have hζ_1s : riemannZeta (1 - s) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re h1ms_re_ge
      have h1ms_re_pos : (0 : ℝ) < (1 - s).re := by linarith
      have hΓ_1s : (1 - s).Gammaℝ ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos h1ms_re_pos
      have hs_ne_zero : s ≠ 0 := by
        intro h; have := congr_arg Complex.im h
        rw [hs_im] at this; simp at this; linarith
      have hΓ_s : s.Gammaℝ ≠ 0 := by
        intro h
        rw [Complex.Gammaℝ_eq_zero_iff] at h
        obtain ⟨n, hn⟩ := h
        have h_im : s.im = (-(2 * (n : ℂ))).im := by rw [hn]
        rw [hs_im] at h_im; simp at h_im; linarith
      have h1ms_ne_zero : (1 - s) ≠ 0 := by
        intro h
        have := congr_arg Complex.re h
        rw [show (1 - s).re = 1 - σ from by simp [s]] at this
        simp at this; linarith
      intro hζ_zero
      have h_xi_1s_form : completedRiemannZeta (1 - s)
          = (1 - s).Gammaℝ * riemannZeta (1 - s) :=
        ZD.WeilPositivity.Contour.completed_eq_gammaℝ_mul_zeta h1ms_ne_zero hΓ_1s
      have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by
        rw [h_xi_1s_form]; exact mul_ne_zero hΓ_1s hζ_1s
      have h_xi_eq : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
        (completedRiemannZeta_one_sub s).symm
      have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
        rw [h_xi_eq]; exact h_xi_1s_ne
      have h_zeta_eq : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
        riemannZeta_def_of_ne_zero hs_ne_zero
      rw [h_zeta_eq] at hζ_zero
      rcases div_eq_zero_iff.mp hζ_zero with h | h
      · exact h_xi_s_ne h
      · exact hΓ_s h
  · -- σ ≥ 1: direct.
    push_neg at h_lt_one
    apply riemannZeta_ne_zero_of_one_le_re
    rw [hs_re]; exact h_lt_one

/-- ζ non-vanishing on the line `Im s = -T` for `σ ∈ [-1, 2]` at goodHeight T.
Mirrors `zeta_ne_zero_strip_top` with sign flip on Im. -/
private lemma zeta_ne_zero_strip_bottom {σ T : ℝ}
    (hσ_mem : σ ∈ Set.Icc (-1:ℝ) 2) (hT_pos : 0 < T) (hGood : goodHeight T) :
    riemannZeta ((σ : ℂ) + (-T : ℂ) * I) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (-T : ℂ) * I with hs_def
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = -T := by simp [s]
  by_cases h_lt_one : σ < 1
  · by_cases h_pos : 0 < σ
    · intro hζ
      have h_nt : s ∈ NontrivialZeros :=
        ⟨by show 0 < s.re; rw [hs_re]; exact h_pos,
         by show s.re < 1; rw [hs_re]; exact h_lt_one,
         hζ⟩
      have h_im_ne_negT := (hGood.1 s h_nt).2
      rw [hs_im] at h_im_ne_negT; exact h_im_ne_negT rfl
    · push_neg at h_pos
      have h1ms_re_ge : (1 : ℝ) ≤ (1 - s).re := by
        show (1 : ℝ) ≤ (1 - s).re
        have : (1 - s).re = 1 - σ := by simp [s]
        rw [this]; linarith
      have hζ_1s : riemannZeta (1 - s) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re h1ms_re_ge
      have h1ms_re_pos : (0 : ℝ) < (1 - s).re := by linarith
      have hΓ_1s : (1 - s).Gammaℝ ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos h1ms_re_pos
      have hs_ne_zero : s ≠ 0 := by
        intro h; have := congr_arg Complex.im h
        rw [hs_im] at this; simp at this; linarith
      have hΓ_s : s.Gammaℝ ≠ 0 := by
        intro h
        rw [Complex.Gammaℝ_eq_zero_iff] at h
        obtain ⟨n, hn⟩ := h
        have h_im : s.im = (-(2 * (n : ℂ))).im := by rw [hn]
        rw [hs_im] at h_im; simp at h_im; linarith
      have h1ms_ne_zero : (1 - s) ≠ 0 := by
        intro h
        have := congr_arg Complex.re h
        rw [show (1 - s).re = 1 - σ from by simp [s]] at this
        simp at this; linarith
      intro hζ_zero
      have h_xi_1s_form : completedRiemannZeta (1 - s)
          = (1 - s).Gammaℝ * riemannZeta (1 - s) :=
        ZD.WeilPositivity.Contour.completed_eq_gammaℝ_mul_zeta h1ms_ne_zero hΓ_1s
      have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by
        rw [h_xi_1s_form]; exact mul_ne_zero hΓ_1s hζ_1s
      have h_xi_eq : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
        (completedRiemannZeta_one_sub s).symm
      have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
        rw [h_xi_eq]; exact h_xi_1s_ne
      have h_zeta_eq : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
        riemannZeta_def_of_ne_zero hs_ne_zero
      rw [h_zeta_eq] at hζ_zero
      rcases div_eq_zero_iff.mp hζ_zero with h | h
      · exact h_xi_s_ne h
      · exact hΓ_s h
  · push_neg at h_lt_one
    apply riemannZeta_ne_zero_of_one_le_re
    rw [hs_re]; exact h_lt_one

/-- FE rewrite of `archKernel(σ + iT)` at goodHeight T, σ ∈ [-1, 2]. -/
private lemma archKernel_FE_top {σ T : ℝ}
    (hσ_mem : σ ∈ Set.Icc (-1:ℝ) 2) (hT_pos : 0 < T) (hGood : goodHeight T) :
    ZD.WeilArchKernelResidues.archKernel ((σ : ℂ) + (T : ℂ) * I) =
      -(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
      (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))) := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have hs_im : s.im = T := by simp [s]
  have h1ms_im : (1 - s).im = -T := by simp [s]
  have hs_ne_zero : s ≠ 0 := by
    intro h; have := congr_arg Complex.im h
    rw [hs_im] at this; simp at this; linarith
  have hs_ne_one : s ≠ 1 := by
    intro h; have := congr_arg Complex.im h
    rw [hs_im] at this; simp at this; linarith
  have hζ_s : riemannZeta s ≠ 0 := zeta_ne_zero_strip_top hσ_mem hT_pos hGood
  -- ζ(1-s) ≠ 0: 1 - s = ((1-σ):ℂ) + (-T:ℂ) * I, apply bottom helper at σ' = 1-σ.
  have h1mσ_mem : (1 - σ) ∈ Set.Icc (-1:ℝ) 2 := by
    constructor
    · linarith [hσ_mem.2]
    · linarith [hσ_mem.1]
  have hζ_1s : riemannZeta (1 - s) ≠ 0 := by
    have h_bridge : (1 - s) = (((1-σ : ℝ)) : ℂ) + (-T : ℂ) * I := by
      simp [s]; push_cast; ring
    rw [h_bridge]
    exact zeta_ne_zero_strip_bottom h1mσ_mem hT_pos hGood
  have hΓ_s : s.Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h_im : s.im = (-(2 * (n : ℂ))).im := by rw [hn]
    rw [hs_im] at h_im; simp at h_im; linarith
  have hΓ_1s : (1 - s).Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h_im : (1 - s).im = (-(2 * (n : ℂ))).im := by rw [hn]
    rw [h1ms_im] at h_im; simp at h_im; linarith
  have h_arch := ZD.WeilPositivity.Contour.zeta_logDeriv_arch_form
    hs_ne_zero hs_ne_one hζ_s hζ_1s hΓ_s hΓ_1s
  unfold ZD.WeilArchKernelResidues.archKernel
  linear_combination -h_arch

/-- Same FE rewrite at `Im s = -T`. -/
private lemma archKernel_FE_bottom {σ T : ℝ}
    (hσ_mem : σ ∈ Set.Icc (-1:ℝ) 2) (hT_pos : 0 < T) (hGood : goodHeight T) :
    ZD.WeilArchKernelResidues.archKernel ((σ : ℂ) + (-T : ℂ) * I) =
      -(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (-T : ℂ) * I)) -
      (deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
          riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I))) := by
  set s : ℂ := (σ : ℂ) + (-T : ℂ) * I with hs_def
  have hs_im : s.im = -T := by simp [s]
  have h1ms_im : (1 - s).im = T := by simp [s]
  have hs_ne_zero : s ≠ 0 := by
    intro h; have := congr_arg Complex.im h
    rw [hs_im] at this; simp at this; linarith
  have hs_ne_one : s ≠ 1 := by
    intro h; have := congr_arg Complex.im h
    rw [hs_im] at this; simp at this; linarith
  have hζ_s : riemannZeta s ≠ 0 := zeta_ne_zero_strip_bottom hσ_mem hT_pos hGood
  have h1mσ_mem : (1 - σ) ∈ Set.Icc (-1:ℝ) 2 := by
    constructor
    · linarith [hσ_mem.2]
    · linarith [hσ_mem.1]
  have hζ_1s : riemannZeta (1 - s) ≠ 0 := by
    have h_bridge : (1 - s) = (((1-σ : ℝ)) : ℂ) + (T : ℂ) * I := by
      simp [s]; push_cast; ring
    rw [h_bridge]
    exact zeta_ne_zero_strip_top h1mσ_mem hT_pos hGood
  have hΓ_s : s.Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h_im : s.im = (-(2 * (n : ℂ))).im := by rw [hn]
    rw [hs_im] at h_im; simp at h_im; linarith
  have hΓ_1s : (1 - s).Gammaℝ ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h_im : (1 - s).im = (-(2 * (n : ℂ))).im := by rw [hn]
    rw [h1ms_im] at h_im; simp at h_im; linarith
  have h_arch := ZD.WeilPositivity.Contour.zeta_logDeriv_arch_form
    hs_ne_zero hs_ne_one hζ_s hζ_1s hΓ_s hΓ_1s
  unfold ZD.WeilArchKernelResidues.archKernel
  linear_combination -h_arch

/-- Pointwise bound on `F(σ + iT) = archKernel(σ + iT) · pairTest β (σ + iT)`
at goodHeight `T ≥ T₀`, for `σ ∈ [-1, 2]`. -/
private lemma F_pointwise_bound_top (β : ℝ) :
    ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
      ∀ T : ℝ, T₀ ≤ T → goodHeight T →
        ∀ σ ∈ Set.Icc (-1:ℝ) 2,
          ‖ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ (N - 4) := by
  obtain ⟨C₁, N₁, T₀₁, hC₁_pos, hT₀₁, hN₁_lt, h_LD_pos⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_unconditional
  obtain ⟨C₂, N₂, T₀₂, hC₂_pos, hT₀₂, hN₂_lt, h_LD_neg⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, h_M⟩ :=
    uniform_pairMellin_quartic_target_pos β
  refine ⟨(C₁ + C₂) * (C_M + 1), max N₁ N₂, max (max T₀₁ T₀₂) (max T₀_M 2),
    ?_, ?_, ?_, ?_⟩
  · -- C > 0: (C₁ + C₂) * (C_M + 1) > 0 since both factors > 0.
    apply mul_pos (by linarith) (by linarith)
  · -- T₀ > 1: max (max T₀₁ T₀₂) (max T₀_M 2) ≥ T₀₁ > 1.
    exact lt_of_lt_of_le hT₀₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  · -- max N₁ N₂ < 4
    exact max_lt hN₁_lt hN₂_lt
  · -- Pointwise bound.
    intro T hT hGood σ hσ_mem
    have hT_ge_T₀₁ : T₀₁ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
    have hT_ge_T₀₂ : T₀₂ ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
    have hT_ge_T₀_M : T₀_M ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
    have hT_ge_2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
    have hT_pos : 0 < T := by linarith
    have hT_ge_1 : (1 : ℝ) ≤ T := by linarith
    -- FE rewrite at top.
    have h_FE : ZD.WeilArchKernelResidues.archKernel ((σ : ℂ) + (T : ℂ) * I) =
        -(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
        (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))) :=
      archKernel_FE_top hσ_mem hT_pos hGood
    -- Bound the two ζ'/ζ pieces.
    have h_z_pos := h_LD_pos T hT_ge_T₀₁ hGood σ hσ_mem
    have h1mσ_mem : (1 - σ) ∈ Set.Icc (-1:ℝ) 2 := by
      constructor
      · linarith [hσ_mem.2]
      · linarith [hσ_mem.1]
    have h_bridge_neg : (1 - ((σ : ℂ) + (T : ℂ) * I)) =
        (((1 - σ : ℝ)) : ℂ) + (-T : ℂ) * I := by
      push_cast; ring
    have h_z_neg_raw := h_LD_neg T hT_ge_T₀₂ hGood (1 - σ) h1mσ_mem
    have h_z_neg : ‖deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
        riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))‖ ≤ C₂ * T ^ N₂ := by
      rw [h_bridge_neg]; exact h_z_neg_raw
    -- pairTest bound.
    have h_M_bd := h_M T hT_ge_T₀_M σ hσ_mem
    -- Compose: ‖F(σ+iT)‖ ≤ (‖ζ'/ζ(s)‖ + ‖ζ'/ζ(1-s)‖) · ‖pairTest(s)‖ ≤ ...
    show ‖ZD.WeilArchKernelResidues.archKernel ((σ : ℂ) + (T : ℂ) * I) *
        Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      (C₁ + C₂) * (C_M + 1) * T ^ (max N₁ N₂ - 4)
    rw [norm_mul, h_FE]
    -- ‖-a - b‖ ≤ ‖a‖ + ‖b‖
    have h_arch_bd : ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)))‖ ≤
        C₁ * T ^ N₁ + C₂ * T ^ N₂ := by
      calc ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
              (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)))‖
          ≤ ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I))‖ +
            ‖deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))‖ := norm_sub_le _ _
        _ = ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ +
            ‖deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))‖ := by rw [norm_neg]
        _ ≤ C₁ * T ^ N₁ + C₂ * T ^ N₂ := by linarith
    have h_TN_pos : 0 < T ^ N₁ := Real.rpow_pos_of_pos hT_pos _
    have h_TN_pos' : 0 < T ^ N₂ := Real.rpow_pos_of_pos hT_pos _
    -- Bound the sum: C₁·T^N₁ + C₂·T^N₂ ≤ (C₁+C₂)·T^max(N₁,N₂) for T ≥ 1.
    have h_TN1_le : T ^ N₁ ≤ T ^ (max N₁ N₂) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge_1 (le_max_left _ _)
    have h_TN2_le : T ^ N₂ ≤ T ^ (max N₁ N₂) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge_1 (le_max_right _ _)
    have h_TN_max_pos : 0 < T ^ (max N₁ N₂) := Real.rpow_pos_of_pos hT_pos _
    have h_arch_bd' : ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)))‖ ≤
        (C₁ + C₂) * T ^ (max N₁ N₂) := by
      calc _ ≤ C₁ * T ^ N₁ + C₂ * T ^ N₂ := h_arch_bd
        _ ≤ C₁ * T ^ (max N₁ N₂) + C₂ * T ^ (max N₁ N₂) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h_TN1_le hC₁_pos.le
            · exact mul_le_mul_of_nonneg_left h_TN2_le hC₂_pos.le
        _ = (C₁ + C₂) * T ^ (max N₁ N₂) := by ring
    -- Multiply by pairTest bound.
    have h_pairTest_le : ‖Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤
        (C_M + 1) / T ^ 4 := by
      have hT4_pos : (0:ℝ) < T ^ 4 := by positivity
      calc ‖Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖
          ≤ C_M / T ^ 4 := h_M_bd
        _ ≤ (C_M + 1) / T ^ 4 := by
            apply div_le_div_of_nonneg_right _ hT4_pos.le
            linarith
    have h_pos_arch : (0:ℝ) ≤ ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)))‖ := norm_nonneg _
    have h_pos_C12 : (0:ℝ) ≤ (C₁ + C₂) * T ^ (max N₁ N₂) := by
      apply mul_nonneg (by linarith) h_TN_max_pos.le
    have h_pos_pT : (0:ℝ) ≤ ‖Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ :=
      norm_nonneg _
    have h_combined : ‖-(deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)))‖ *
        ‖Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤
        ((C₁ + C₂) * T ^ (max N₁ N₂)) * ((C_M + 1) / T ^ 4) :=
      mul_le_mul h_arch_bd' h_pairTest_le h_pos_pT h_pos_C12
    apply h_combined.trans_eq
    -- Simplify: (C₁+C₂)·T^N · (C_M+1)/T^4 = (C₁+C₂)·(C_M+1)·T^(N-4)
    have h_pow_div : T ^ (max N₁ N₂) / T ^ 4 = T ^ (max N₁ N₂ - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : (C₁ + C₂) * T ^ (max N₁ N₂) * ((C_M + 1) / T ^ 4) =
        (C₁ + C₂) * (C_M + 1) * (T ^ (max N₁ N₂) / T ^ 4) := by ring
    rw [this, h_pow_div]

/-- Pointwise bound on `F(σ - iT)` (bottom edge analog). -/
private lemma F_pointwise_bound_bottom (β : ℝ) :
    ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
      ∀ T : ℝ, T₀ ≤ T → goodHeight T →
        ∀ σ ∈ Set.Icc (-1:ℝ) 2,
          ‖ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * T ^ (N - 4) := by
  obtain ⟨C₁, N₁, T₀₁, hC₁_pos, hT₀₁, hN₁_lt, h_LD_pos⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_unconditional
  obtain ⟨C₂, N₂, T₀₂, hC₂_pos, hT₀₂, hN₂_lt, h_LD_neg⟩ :=
    full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, h_M⟩ :=
    uniform_pairMellin_quartic_target_neg β
  refine ⟨(C₁ + C₂) * (C_M + 1), max N₁ N₂, max (max T₀₁ T₀₂) (max T₀_M 2),
    ?_, ?_, ?_, ?_⟩
  · apply mul_pos (by linarith) (by linarith)
  · exact lt_of_lt_of_le hT₀₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact max_lt hN₁_lt hN₂_lt
  · intro T hT hGood σ hσ_mem
    have hT_ge_T₀₁ : T₀₁ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
    have hT_ge_T₀₂ : T₀₂ ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
    have hT_ge_T₀_M : T₀_M ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
    have hT_ge_2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
    have hT_pos : 0 < T := by linarith
    have hT_ge_1 : (1 : ℝ) ≤ T := by linarith
    have h_FE := archKernel_FE_bottom hσ_mem hT_pos hGood
    have h_z_neg := h_LD_neg T hT_ge_T₀₂ hGood σ hσ_mem
    have h1mσ_mem : (1 - σ) ∈ Set.Icc (-1:ℝ) 2 := by
      constructor
      · linarith [hσ_mem.2]
      · linarith [hσ_mem.1]
    have h_bridge_pos : (1 - ((σ : ℂ) + (-T : ℂ) * I)) =
        (((1 - σ : ℝ)) : ℂ) + (T : ℂ) * I := by
      push_cast; ring
    have h_z_pos_raw := h_LD_pos T hT_ge_T₀₁ hGood (1 - σ) h1mσ_mem
    have h_z_pos : ‖deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
        riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I))‖ ≤ C₁ * T ^ N₁ := by
      rw [h_bridge_pos]; exact h_z_pos_raw
    have h_M_bd := h_M T hT_ge_T₀_M σ hσ_mem
    show ‖ZD.WeilArchKernelResidues.archKernel ((σ : ℂ) + (-T : ℂ) * I) *
        Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ ≤
      (C₁ + C₂) * (C_M + 1) * T ^ (max N₁ N₂ - 4)
    rw [norm_mul, h_FE]
    have h_arch_bd : ‖-(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)))‖ ≤
        C₂ * T ^ N₂ + C₁ * T ^ N₁ := by
      calc ‖-(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (-T : ℂ) * I)) -
              (deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)))‖
          ≤ ‖-(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (-T : ℂ) * I))‖ +
            ‖deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I))‖ := norm_sub_le _ _
        _ = ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ +
            ‖deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
                riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I))‖ := by rw [norm_neg]
        _ ≤ C₂ * T ^ N₂ + C₁ * T ^ N₁ := by linarith
    have h_TN_pos : 0 < T ^ N₁ := Real.rpow_pos_of_pos hT_pos _
    have h_TN_pos' : 0 < T ^ N₂ := Real.rpow_pos_of_pos hT_pos _
    have h_TN1_le : T ^ N₁ ≤ T ^ (max N₁ N₂) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge_1 (le_max_left _ _)
    have h_TN2_le : T ^ N₂ ≤ T ^ (max N₁ N₂) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge_1 (le_max_right _ _)
    have h_TN_max_pos : 0 < T ^ (max N₁ N₂) := Real.rpow_pos_of_pos hT_pos _
    have h_arch_bd' : ‖-(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)))‖ ≤
        (C₁ + C₂) * T ^ (max N₁ N₂) := by
      calc _ ≤ C₂ * T ^ N₂ + C₁ * T ^ N₁ := h_arch_bd
        _ ≤ C₂ * T ^ (max N₁ N₂) + C₁ * T ^ (max N₁ N₂) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h_TN2_le hC₂_pos.le
            · exact mul_le_mul_of_nonneg_left h_TN1_le hC₁_pos.le
        _ = (C₁ + C₂) * T ^ (max N₁ N₂) := by ring
    have h_pairTest_le : ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ ≤
        (C_M + 1) / T ^ 4 := by
      have hT4_pos : (0:ℝ) < T ^ 4 := by positivity
      calc ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖
          ≤ C_M / T ^ 4 := h_M_bd
        _ ≤ (C_M + 1) / T ^ 4 := by
            apply div_le_div_of_nonneg_right _ hT4_pos.le
            linarith
    have h_pos_C12 : (0:ℝ) ≤ (C₁ + C₂) * T ^ (max N₁ N₂) := by
      apply mul_nonneg (by linarith) h_TN_max_pos.le
    have h_pos_pT : (0:ℝ) ≤ ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ :=
      norm_nonneg _
    have h_combined : ‖-(deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)) -
          (deriv riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)) /
            riemannZeta (1 - ((σ : ℂ) + (-T : ℂ) * I)))‖ *
        ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ ≤
        ((C₁ + C₂) * T ^ (max N₁ N₂)) * ((C_M + 1) / T ^ 4) :=
      mul_le_mul h_arch_bd' h_pairTest_le h_pos_pT h_pos_C12
    apply h_combined.trans_eq
    have h_pow_div : T ^ (max N₁ N₂) / T ^ 4 = T ^ (max N₁ N₂ - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : (C₁ + C₂) * T ^ (max N₁ N₂) * ((C_M + 1) / T ^ 4) =
        (C₁ + C₂) * (C_M + 1) * (T ^ (max N₁ N₂) / T ^ 4) := by ring
    rw [this, h_pow_div]

/-- **Discharge of `archKernel_pairTest_horizontal_vanishes_target`.**
Combines the pointwise bounds on F at top and bottom edges with
`intervalIntegral.norm_integral_le_of_norm_le_const`, then triangle
inequality and the standard "pick T big enough" argument for `T^(N-4) → 0`. -/
theorem archKernel_pairTest_horizontal_vanishes_target_holds (β : ℝ) :
    archKernel_pairTest_horizontal_vanishes_target β := by
  obtain ⟨C_top, N_top, T₀_top, hC_top_pos, hT₀_top, hN_top_lt, h_top_bd⟩ :=
    F_pointwise_bound_top β
  obtain ⟨C_bot, N_bot, T₀_bot, hC_bot_pos, hT₀_bot, hN_bot_lt, h_bot_bd⟩ :=
    F_pointwise_bound_bottom β
  -- Combined constants.
  set N : ℝ := max N_top N_bot with hN_def
  set C : ℝ := 3 * (C_top + C_bot) with hC_def
  have hN_lt_4 : N < 4 := max_lt hN_top_lt hN_bot_lt
  have hC_pos : 0 < C := by rw [hC_def]; linarith
  set K : ℝ := C + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith
  intro ε hε
  have h4mN_pos : 0 < 4 - N := by linarith
  have hKε : 0 < K / ε := div_pos hK_pos hε
  set Tbig : ℝ := (K / ε) ^ (1 / (4 - N))
  have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
  set T₀ : ℝ := max (max T₀_top T₀_bot) (max Tbig 2)
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hT_ge_top : T₀_top ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_ge_bot : T₀_bot ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_ge_Tbig : Tbig ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_ge_2 : (2 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT_pos : 0 < T := by linarith
  have hT_ge_1 : (1 : ℝ) ≤ T := by linarith
  -- Pointwise bounds rephrased over uIoc (-1) 2.
  have h_uIoc_eq : Set.uIoc (-1:ℝ) 2 = Set.Ioc (-1:ℝ) 2 :=
    Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 2)
  -- Top pointwise bound.
  have h_top_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
      ‖ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C_top * T ^ (N_top - 4) := by
    intro σ hσ
    rw [h_uIoc_eq] at hσ
    have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
    exact h_top_bd T hT_ge_top hGood σ hσ_Icc
  -- Bottom pointwise bound.
  have h_bot_inner : ∀ σ ∈ Set.uIoc (-1:ℝ) 2,
      ‖ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C_bot * T ^ (N_bot - 4) := by
    intro σ hσ
    rw [h_uIoc_eq] at hσ
    have hσ_Icc : σ ∈ Set.Icc (-1:ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
    exact h_bot_bd T hT_ge_bot hGood σ hσ_Icc
  -- Integral bounds.
  have h_top_int : ‖∫ σ in (-1:ℝ)..2,
      ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C_top * T ^ (N_top - 4) * |2 - (-1:ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_top_inner
  have h_bot_int : ‖∫ σ in (-1:ℝ)..2,
      ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C_bot * T ^ (N_bot - 4) * |2 - (-1:ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_bot_inner
  have habs : |(2 - (-1:ℝ))| = (3 : ℝ) := by norm_num
  rw [habs] at h_top_int h_bot_int
  -- Bridge: ((T : ℝ) : ℂ) = (T : ℂ) and ((-T : ℝ) : ℂ) = (-T : ℂ).
  have h_top_eq :
      (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℝ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro y _; rfl
  have h_bot_eq :
      (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (-T : ℝ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (-T : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro y _
    have : ((-T : ℝ) : ℂ) = (-T : ℂ) := by push_cast; rfl
    show ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((y : ℂ) + ((-T : ℝ) : ℂ) * I) =
      ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
        ((y : ℂ) + (-T : ℂ) * I)
    rw [this]
  -- Triangle inequality on bottom - top.
  have h_diff_bd :
      ‖(∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (-T : ℝ) * I)) -
        (∫ x : ℝ in (-1 : ℝ)..2,
          ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
            ((x : ℂ) + (T : ℝ) * I))‖ ≤
      C_bot * T ^ (N_bot - 4) * 3 + C_top * T ^ (N_top - 4) * 3 := by
    rw [h_top_eq, h_bot_eq]
    calc ‖(∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (-T : ℂ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
              ((x : ℂ) + (T : ℂ) * I))‖
        ≤ ‖∫ x : ℝ in (-1 : ℝ)..2,
              ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
                ((x : ℂ) + (-T : ℂ) * I)‖ +
          ‖∫ x : ℝ in (-1 : ℝ)..2,
              ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β
                ((x : ℂ) + (T : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ C_bot * T ^ (N_bot - 4) * 3 + C_top * T ^ (N_top - 4) * 3 := by
          linarith
  -- Bound by C * T^(N-4).
  have h_TN_top_pos : 0 < T ^ (N_top - 4) := Real.rpow_pos_of_pos hT_pos _
  have h_TN_bot_pos : 0 < T ^ (N_bot - 4) := Real.rpow_pos_of_pos hT_pos _
  have h_TN_neg_top : T ^ (N_top - 4) ≤ T ^ (N - 4) := by
    apply Real.rpow_le_rpow_of_exponent_le hT_ge_1
    have : N_top ≤ N := le_max_left _ _
    linarith
  have h_TN_neg_bot : T ^ (N_bot - 4) ≤ T ^ (N - 4) := by
    apply Real.rpow_le_rpow_of_exponent_le hT_ge_1
    have : N_bot ≤ N := le_max_right _ _
    linarith
  have h_combined_bd :
      C_bot * T ^ (N_bot - 4) * 3 + C_top * T ^ (N_top - 4) * 3 ≤
        C * T ^ (N - 4) := by
    have h1 : C_bot * T ^ (N_bot - 4) * 3 ≤ C_bot * T ^ (N - 4) * 3 := by
      have := mul_le_mul_of_nonneg_left h_TN_neg_bot hC_bot_pos.le
      have hh : C_bot * T ^ (N_bot - 4) * 3 ≤ C_bot * T ^ (N - 4) * 3 := by
        apply mul_le_mul_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 3)
      exact hh
    have h2 : C_top * T ^ (N_top - 4) * 3 ≤ C_top * T ^ (N - 4) * 3 := by
      have := mul_le_mul_of_nonneg_left h_TN_neg_top hC_top_pos.le
      have hh : C_top * T ^ (N_top - 4) * 3 ≤ C_top * T ^ (N - 4) * 3 := by
        apply mul_le_mul_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 3)
      exact hh
    have : C_bot * T ^ (N - 4) * 3 + C_top * T ^ (N - 4) * 3 = C * T ^ (N - 4) := by
      rw [hC_def]; ring
    linarith
  -- Final: C * T^(N-4) < ε via Tbig choice.
  have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
    rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
  have hT_pow_ge : (K / ε) ≤ T ^ (4 - N) := by
    have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
      Real.rpow_le_rpow hTbig_pos.le hT_ge_Tbig h4mN_pos.le
    have h_Tbig_pow : Tbig ^ (4 - N) = K / ε := by
      rw [show Tbig = (K / ε) ^ (1 / (4 - N)) from rfl, ← Real.rpow_mul hKε.le]
      have h_one : 1 / (4 - N) * (4 - N) = 1 := by field_simp
      rw [h_one, Real.rpow_one]
    linarith
  have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
  have h_final : C * T ^ (N - 4) < ε := by
    rw [h_pow_neg]
    have hC_lt_K : C < K := by rw [hK_def]; linarith
    calc C * (1 / T ^ (4 - N))
        < K * (1 / T ^ (4 - N)) := by
          apply mul_lt_mul_of_pos_right hC_lt_K
          exact div_pos one_pos hT_pow_pos
      _ ≤ K * (ε / K) := by
          apply mul_le_mul_of_nonneg_left _ hK_pos.le
          rw [div_le_div_iff₀ hT_pow_pos hK_pos]
          have h := (div_le_iff₀ hε).mp hT_pow_ge
          nlinarith
      _ = ε := by field_simp
  linarith

/-- **Unconditional discharge of the corrected `(♥)` identity.** Combines
the conditional discharge `archIntegrand_diff_at_two_minus_neg_one_of_horizontal_vanishes`
with the unconditional `archKernel_pairTest_horizontal_vanishes_target_holds`.
This is the **corrected** version of the buggy
`ZD.ArchKernelRectCauchyTransport.archDiff_eq_residue_sum_target` (no extra `I`
factor on the RHS). -/
theorem archIntegrand_diff_at_two_minus_neg_one_target_holds (β : ℝ) :
    archIntegrand_diff_at_two_minus_neg_one_target β :=
  archIntegrand_diff_at_two_minus_neg_one_of_horizontal_vanishes β
    (archKernel_pairTest_horizontal_vanishes_target_holds β)

/-! ## Composition: unconditional value of `∫reflectedPrimeIntegrand β 2`

Combining the four axiom-clean identities:

* `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum`: `∫arch β 2 + ∫reflectedPrime β 2 = 2π·prime_sum`.
* `weilIntegrand_left_edge_integral_value` (β ∈ (0,1)): `∫weil(-1+iy) = 2π·(prime_sum - pairTest β 1 + Σ residues)`.
* `archIntegrand_diff_at_two_minus_neg_one_target_holds` (♥): `∫arch β 2 - ∫arch β (-1) = 2π·(gaussianPairDefect β - pairTest β 0)`.
* `LeftEdgePrimeSum.leftEdge_reflectedPrime_eq_sum`: `∫ζ'/ζ(2-iy)·pairTest(-1+iy) dy = -2π·∑Λ(n)/n·test(1/n)`.
* `LeftEdgePrimeSum.leftEdge_integrand_decomposition`: `weilIntegrand(-1+iy) = arch β (-1) y + ζ'/ζ(2-iy)·pairTest(-1+iy)` (pointwise).

These compose to give a closed-form value for `∫reflectedPrimeIntegrand β 2`.
-/

/-- **Bridge**: integral form of `weil(-1+iy) = arch β (-1) y + ζ'/ζ(2-iy)·pairTest(-1+iy)`. -/
private lemma weil_left_edge_integral_eq_arch_plus_Z (β : ℝ) :
    (∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      (∫ y : ℝ, Contour.archIntegrand β (-1) y) +
      (∫ y : ℝ,
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
          riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  -- Pointwise FE bridge from weilIntegrand to hadamardArchBoundaryTerm·pairTest.
  have h_pt_FE : ∀ y : ℝ,
      Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)
        = Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) :=
    weilIntegrand_pairTestMellin_left_edge_eq_hadamardArchBoundaryTerm β
  -- Pointwise decomposition: hadamardArchBoundaryTerm·pairTest = arch + (ζ'/ζ(2-iy)·pairTest).
  have h_pt_decomp : ∀ y : ℝ,
      Contour.hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) =
      Contour.archIntegrand β (-1) y +
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
        riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := fun y =>
    ZD.WeilPositivity.LeftEdgePrimeSum.leftEdge_integrand_decomposition β y
  -- Combined pointwise: weil = arch + Z-integrand.
  have h_pt_full : ∀ y : ℝ,
      Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) =
      Contour.archIntegrand β (-1) y +
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
        riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) := fun y => by
    rw [h_pt_FE y]; exact h_pt_decomp y
  -- Integrate. Need integrability of arch (-1) and Z integrand.
  have h_arch_int : MeasureTheory.Integrable (Contour.archIntegrand β (-1)) :=
    ZD.WeilPositivity.ArchAtNegOne.archIntegrand_at_neg_one_integrable β
  have h_weil_int : MeasureTheory.Integrable (fun y : ℝ =>
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) :=
    leftEdge_weilIntegrand_pairTestMellin_integrable β
  -- Z integrand = weil - arch, both integrable, so integrable.
  have h_Z_int : MeasureTheory.Integrable (fun y : ℝ =>
      (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
        riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
      Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
    have h_eq : (fun y : ℝ =>
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
          riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
        (fun y : ℝ => Contour.weilIntegrand (Contour.pairTestMellin β)
            ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) - Contour.archIntegrand β (-1) y) := by
      funext y
      have h := h_pt_full y
      linear_combination -h
    rw [h_eq]
    exact h_weil_int.sub h_arch_int
  -- Now integrate the pointwise identity.
  rw [show (∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      ∫ y : ℝ, (Contour.archIntegrand β (-1) y +
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
          riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact h_pt_full y]
  exact MeasureTheory.integral_add h_arch_int h_Z_int

/-- **Unconditional value of `∫reflectedPrimeIntegrand β 2`.** Combines:
* `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum`
* `weilIntegrand_left_edge_integral_value` (β ∈ (0,1))
* `archIntegrand_diff_at_two_minus_neg_one_target_holds` (♥)
* `weil_left_edge_integral_eq_arch_plus_Z` (W = A_- + Z)
* `LeftEdgePrimeSum.leftEdge_reflectedPrime_eq_sum` (Z = -2π·∑Λ(n)/n·test(1/n))

Result: `∫reflectedPrime β 2 = 2π·(pairTest β 0 - Σ residues - ∑Λ(n)/n·test(1/n))`. -/
theorem reflectedPrime_integral_value (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y) =
      2 * (Real.pi : ℂ) *
        (Contour.pairTestMellin β 0 -
         (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (((Classical.choose
              (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
              : ℕ) : ℂ)) *
            Contour.pairTestMellin β ρ.val) -
         (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ))) := by
  -- Abbreviations.
  set m0 : ℂ := Contour.pairTestMellin β 0 with hm0_def
  set m1 : ℂ := Contour.pairTestMellin β 1 with hm1_def
  set Aplus : ℂ := ∫ t : ℝ, Contour.archIntegrand β 2 t with hAplus_def
  set Aminus : ℂ := ∫ y : ℝ, Contour.archIntegrand β (-1) y with hAminus_def
  set Refl : ℂ := ∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y with hRefl_def
  set W : ℂ := ∫ y : ℝ, Contour.weilIntegrand (Contour.pairTestMellin β)
                ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hW_def
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                 ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) with hS_def
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
          : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val with hSres_def
  set Z : ℂ := ∫ y : ℝ,
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
          riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hZ_def
  set Sinv : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                  ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ) with hSinv_def
  -- (1) A_+ + Refl = 2π·S
  have h1 : Aplus + Refl = 2 * (Real.pi : ℂ) * S :=
    archIntegrand_plus_reflectedPrime_integral_eq_prime_sum β
  -- (2) W = 2π·(S - m1 + Sres)
  have h2 : W = 2 * (Real.pi : ℂ) * (S - m1 + Sres) :=
    weilIntegrand_left_edge_integral_value β hβ
  -- (♥): A_+ - A_- = 2π·(m1 - m0). Note: gaussianPairDefect β = m1 via pairTestMellin_at_one.
  have hm1_real : m1 = ((gaussianPairDefect β : ℝ) : ℂ) := by
    rw [hm1_def]; exact Contour.pairTestMellin_at_one β
  have h_arch_diff := archIntegrand_diff_at_two_minus_neg_one_target_holds β
  have hheart : Aplus - Aminus =
      2 * ((Real.pi : ℝ) : ℂ) * ((-m0) + ((gaussianPairDefect β : ℝ) : ℂ)) := h_arch_diff
  have hheart' : Aplus - Aminus = 2 * (Real.pi : ℂ) * (m1 - m0) := by
    rw [hheart, hm1_real]; ring
  -- W = A_- + Z (bridge from FE-image decomposition + integration).
  have h_W_decomp : W = Aminus + Z :=
    weil_left_edge_integral_eq_arch_plus_Z β
  -- (4) Z = -2π·Sinv
  have h_Z_eq : Z = -2 * (Real.pi : ℂ) * Sinv := by
    show (∫ y : ℝ,
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) /
          riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) *
        Contour.pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) =
      -2 * ((Real.pi : ℝ) : ℂ) * Sinv
    have h_sum := ZD.WeilPositivity.LeftEdgePrimeSum.leftEdge_reflectedPrime_eq_sum β
    rw [h_sum]
  -- Compose:
  -- From h_W_decomp: Aminus = W - Z.
  -- From hheart': Aplus = Aminus + 2π(m1 - m0) = W - Z + 2π(m1 - m0).
  -- From h1: Refl = 2π·S - Aplus = 2π·S - W + Z - 2π(m1 - m0).
  --        = 2π·S - 2π(S - m1 + Sres) + Z - 2π(m1 - m0)   [using h2]
  --        = 2π·m1 - 2π·Sres + Z - 2π·m1 + 2π·m0
  --        = -2π·Sres + Z + 2π·m0
  --        = -2π·Sres + (-2π·Sinv) + 2π·m0     [using h_Z_eq]
  --        = 2π·(m0 - Sres - Sinv)
  show Refl = 2 * (Real.pi : ℂ) * (m0 - Sres - Sinv)
  linear_combination h1 - h2 - hheart' + h_W_decomp + h_Z_eq

/-- **Test-function form of the H3 closure content** — the classical Weil
explicit formula in test-function form for the cosh-pair Gauss test:
```
pairTestMellin β 0 - gaussianPairDefect β = ∑_n Λ(n)/n · pair_cosh_gauss_test β (1/n)
```
This is (★) — the open H3 closure obligation, now isolated as a single
concrete numerical identity. -/
def weil_explicit_formula_cosh_pair_test_function_form (β : ℝ) : Prop :=
  Contour.pairTestMellin β 0 - ((gaussianPairDefect β : ℝ) : ℂ) =
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
      ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)

/-- **Equivalence between the residue form and the test-function form (★)**, for
β ∈ (0, 1). Composition of `reflectedPrime_integral_value` with the residue-form
def. -/
theorem weil_explicit_formula_cosh_pair_residue_form_iff_test_function_form
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    weil_explicit_formula_cosh_pair_residue_form β ↔
      weil_explicit_formula_cosh_pair_test_function_form β := by
  unfold weil_explicit_formula_cosh_pair_residue_form
    weil_explicit_formula_cosh_pair_test_function_form
  have h_refl_val := reflectedPrime_integral_value β hβ
  have hm1_real : Contour.pairTestMellin β 1 = ((gaussianPairDefect β : ℝ) : ℂ) :=
    Contour.pairTestMellin_at_one β
  set m0 : ℂ := Contour.pairTestMellin β 0
  set m1g : ℂ := ((gaussianPairDefect β : ℝ) : ℂ)
  set Refl : ℂ := ∫ y : ℝ, Contour.reflectedPrimeIntegrand β 2 y
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
          : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val
  set Sinv : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                  ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)
  -- h_refl_val : Refl = 2π·(m0 - Sres - Sinv)
  -- hm1_real : pairTestMellin β 1 = m1g
  -- Residue form: Refl = 2π·(pairTestMellin β 1 - Sres) = 2π·(m1g - Sres)
  -- Test form: m0 - m1g = Sinv
  -- Equivalence: 2π·(m1g - Sres) = 2π·(m0 - Sres - Sinv) ⟺ m1g = m0 - Sinv ⟺ m0 - m1g = Sinv. ✓
  rw [hm1_real]
  constructor
  · intro h_residue
    -- h_residue : Refl = 2π·(m1g - Sres)
    -- h_refl_val : Refl = 2π·(m0 - Sres - Sinv)
    -- Combine: 2π·(m1g - Sres) = 2π·(m0 - Sres - Sinv) ⟹ m0 - m1g = Sinv.
    have h_eq : 2 * (Real.pi : ℂ) * (m1g - Sres) = 2 * (Real.pi : ℂ) * (m0 - Sres - Sinv) := by
      rw [← h_residue]; exact h_refl_val
    have hπ_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
      apply mul_ne_zero (by norm_num : (2:ℂ) ≠ 0)
      exact_mod_cast Real.pi_ne_zero
    have h_eq' : m1g - Sres = m0 - Sres - Sinv := mul_left_cancel₀ hπ_ne h_eq
    linear_combination -h_eq'
  · intro h_test
    -- h_test : m0 - m1g = Sinv
    -- Want: Refl = 2π·(m1g - Sres)
    -- Using h_refl_val: Refl = 2π·(m0 - Sres - Sinv) = 2π·(m0 - Sres - (m0 - m1g)) = 2π·(m1g - Sres). ✓
    rw [h_refl_val]
    linear_combination 2 * (Real.pi : ℂ) * h_test

/-- **Equivalence between the original placeholder and the test-function form (★)**,
for β ∈ (0, 1). Chains `weil_explicit_formula_cosh_pair_target_iff_residue_form`
with `weil_explicit_formula_cosh_pair_residue_form_iff_test_function_form`. -/
theorem weil_explicit_formula_cosh_pair_target_iff_test_function_form
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    weil_explicit_formula_cosh_pair_target β ↔
      weil_explicit_formula_cosh_pair_test_function_form β :=
  (weil_explicit_formula_cosh_pair_target_iff_residue_form β hβ).trans
    (weil_explicit_formula_cosh_pair_residue_form_iff_test_function_form β hβ)

end FinalAssembly
end WeilPositivity
end ZD

end
