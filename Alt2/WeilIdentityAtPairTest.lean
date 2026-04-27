import Mathlib
import RequestProject.PairTestRectangleCauchy
import RequestProject.WeilRectResidueIdentityDischarge
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.WeilHadamardBoundaryIntegrability
import RequestProject.WeilHorizontalTailsDischarge

/-!
# Weil identity at the cosh-pair Gauss test — finite T composition

This file composes the proved residue identity
(`rectangleResidueIdentity_target_holds_neg_one_two`) with the proved boundary
decomposition
(`rectContourIntegral_weilIntegrand_pairTestMellin_eq_boundary_forms_with_origin_neg_one`)
to obtain a finite-`T` equation linking the four boundary integrals to the
sum over the inside-rectangle residues.

This is **Step 1a** of the gap analysis plan. It is the finite-`T` precursor to
the whole-line Weil explicit formula at our test.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace PairTestIdentity

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZetaDefs

/-- **Step 1a (finite-`T`)**: composing the rectangle residue identity with the
boundary-form decomposition for `weilIntegrand (pairTestMellin β)` at
`σ_L = -1, σ_R = 2`.

The four boundary integrals — bottom (`y = -T`), top (`y = T`), right edge
(`Re s = 2`, expressed as `LSeries (vonMangoldt) · pairTestMellin β`), left edge
(`Re s = -1`, expressed as `hadamardArchBoundaryTerm · pairTestMellin β`) —
balance against `2πi · (pairTestMellin β 1 − Σ_{ρ∈Z} n(ρ)·pairTestMellin β ρ)`.

This is unconditional. Hypotheses:
* `hβ : β ∈ (0, 1)` — selects the cosh-pair Gauss test.
* `hT : 1 < T`, `hGood : goodHeight T` — needed by the residue identity to
  ensure no zeros lie on the rectangle contour.
* `n, Z, hZ_mem, hZ_complete` — finite enumeration of the nontrivial zeros
  inside the rectangle, with their multiplicities.

No further analytic content beyond the proved infrastructure is invoked. -/
theorem finite_T_boundary_balance
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    {T : ℝ} (hT : 1 < T) (hGood : goodHeight T)
    (n : ℂ → ℕ) (Z : Finset ℂ)
    (hZ_mem : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z) :
    (((∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
            (∫ x : ℝ in (-1 : ℝ)..2,
              weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))) +
            I •
              (∫ y : ℝ in (-T : ℝ)..T,
                LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                    ((2 : ℂ) + (y : ℂ) * I) *
                  pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))) -
        I •
          (∫ y : ℝ in (-T : ℝ)..T,
            hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
              pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
      = 2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * pairTestMellin β ρ) := by
  have hT_pos : 0 < T := by linarith
  have h_res :=
    rectangleResidueIdentity_target_holds_neg_one_two β hβ T hT hGood n Z hZ_mem hZ_complete
  have h_bnd :=
    rectContourIntegral_weilIntegrand_pairTestMellin_eq_boundary_forms_with_origin_neg_one
      β (T := T) hT_pos
  rw [h_bnd] at h_res
  exact h_res

/-! ## §1b. Right edge and left edge identifications -/

/-- **Right edge identification (pointwise).** On the line `Re s = 2`, the
right-edge boundary integrand from `finite_T_boundary_balance` is exactly
`primeIntegrand β 2 y` by definition. -/
theorem rightEdge_integrand_eq_primeIntegrand (β : ℝ) (y : ℝ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((2 : ℂ) + (y : ℂ) * I) *
      pairTestMellin β ((2 : ℂ) + (y : ℂ) * I)
      = primeIntegrand β 2 y := by
  unfold primeIntegrand
  push_cast
  ring

/-- **Left edge identification (pointwise).** On the line `Re s = -1`, the
left-edge boundary integrand `hadamardArchBoundaryTerm(-1+iy) · pairTestMellin β (-1+iy)`
equals `archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y` by
direct unfolding. -/
theorem leftEdge_integrand_eq_arch_plus_reflected (β : ℝ) (y : ℝ) :
    hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)
      = archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y := by
  unfold hadamardArchBoundaryTerm archIntegrand reflectedPrimeIntegrand
  push_cast
  ring

/-- **Right edge integral identification.** The finite-`T` right edge integral
equals the finite-interval prime integrand integral. -/
theorem rightEdge_integral_eq_primeIntegrand_integral (β : ℝ) (T : ℝ) :
    (∫ y : ℝ in (-T : ℝ)..T,
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((2 : ℂ) + (y : ℂ) * I) *
          pairTestMellin β ((2 : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ in (-T : ℝ)..T, primeIntegrand β 2 y := by
  apply intervalIntegral.integral_congr
  intro y _
  exact rightEdge_integrand_eq_primeIntegrand β y

/-- **Left edge integral identification.** The finite-`T` left edge integral
equals the finite-interval `archIntegrand + reflectedPrimeIntegrand` integral
at `σ₀ = -1`. -/
theorem leftEdge_integral_eq_arch_plus_reflected_integral (β : ℝ) (T : ℝ) :
    (∫ y : ℝ in (-T : ℝ)..T,
        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
          pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
      = ∫ y : ℝ in (-T : ℝ)..T,
          archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y := by
  apply intervalIntegral.integral_congr
  intro y _
  exact leftEdge_integrand_eq_arch_plus_reflected β y

/-- **Step 1a + 1b combined**: finite-`T` boundary balance with the right and
left edge integrals expressed in terms of `primeIntegrand` and
`archIntegrand + reflectedPrimeIntegrand`. -/
theorem finite_T_boundary_balance_via_integrands
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    {T : ℝ} (hT : 1 < T) (hGood : goodHeight T)
    (n : ℂ → ℕ) (Z : Finset ℂ)
    (hZ_mem : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z) :
    (((∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
            (∫ x : ℝ in (-1 : ℝ)..2,
              weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))) +
            I • (∫ y : ℝ in (-T : ℝ)..T, primeIntegrand β 2 y)) -
        I • (∫ y : ℝ in (-T : ℝ)..T,
            archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y)
      = 2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * pairTestMellin β ρ) := by
  have h_eq := finite_T_boundary_balance β hβ hT hGood n Z hZ_mem hZ_complete
  rw [rightEdge_integral_eq_primeIntegrand_integral,
      leftEdge_integral_eq_arch_plus_reflected_integral] at h_eq
  exact h_eq

/-! ## §1d. Horizontal tails vanish as `T → ∞` -/

/-- **Step 1d (horizontal tails).** The bottom-minus-top edge difference
vanishes as `T → ∞` along good heights. Combines `topEdgeVanishes_target` and
`bottomEdgeVanishes_target` (both proved unconditionally for our test) by
norm-triangle. -/
theorem horizontalEdgeDifference_vanishes (β : ℝ) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖(∫ x : ℝ in (-1 : ℝ)..2,
          weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ < ε := by
  intro ε hε
  have h_top : topEdgeVanishes_target β (-1) 2 :=
    h_top_of_full_strip_logDeriv β full_strip_logDerivZeta_bound_N_lt_4_unconditional
  have h_bot : bottomEdgeVanishes_target β (-1) 2 :=
    h_bottom_of_full_strip_logDeriv β full_strip_logDerivZeta_bound_N_lt_4_neg_unconditional
  obtain ⟨T_top, hT_top_pos, hT_top⟩ := h_top (ε / 2) (by linarith)
  obtain ⟨T_bot, hT_bot_pos, hT_bot⟩ := h_bot (ε / 2) (by linarith)
  refine ⟨max T_top T_bot, lt_of_lt_of_le hT_top_pos (le_max_left _ _), fun T hT hGood => ?_⟩
  have hT_ge_top : T_top ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_bot : T_bot ≤ T := le_trans (le_max_right _ _) hT
  have hbot_lt : ‖∫ x : ℝ in (-1 : ℝ)..2,
        weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ < ε / 2 :=
    hT_bot T hT_ge_bot hGood
  have htop_lt : ‖∫ x : ℝ in (-1 : ℝ)..2,
        weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ < ε / 2 :=
    hT_top T hT_ge_top hGood
  calc ‖(∫ x : ℝ in (-1 : ℝ)..2,
          weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖
      ≤ ‖∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)‖ +
          ‖∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I)‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ## §1c. T → ∞ vertical-edge difference limit -/

/-- **Step 1c**: along good heights, the vertical-edge difference of boundary
forms converges to `2πi · (pairTestMellin β 1 − Σ' n(ρ)·pairTestMellin β ρ)`.

Proof: rectangle integral splits via boundary decomposition; horizontal
difference vanishes (Step 1d); rectangle integral converges to residue side
(`rectangleLimit_target`, proved unconditionally). -/
theorem verticalEdgeDifference_limit
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖(I • (∫ y : ℝ in (-T : ℝ)..T,
              LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  ((2 : ℂ) + (y : ℂ) * I) *
                pairTestMellin β ((2 : ℂ) + (y : ℂ) * I)) -
          I • (∫ y : ℝ in (-T : ℝ)..T,
              hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
                pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) -
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (pairTestMellin β 1 -
            ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
              (((Classical.choose
                (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
                : ℕ) : ℂ)) *
              pairTestMellin β ρ.val)‖ < ε := by
  -- Construct rectangleLimit_target β unconditionally.
  have h_lim : rectangleLimit_target β :=
    rectangleLimit_of_residue_identity_and_summability β
      (h_rect_residue_unconditional β hβ)
      (h_sum_unconditional β) h_fin_unconditional
  obtain ⟨limitVal, h_conv, h_eq⟩ := h_lim
  have h_hor := horizontalEdgeDifference_vanishes β
  intro ε hε
  obtain ⟨T_rect, hT_rect_pos, hT_rect⟩ := h_conv (ε / 2) (by linarith)
  obtain ⟨T_hor, hT_hor_pos, hT_hor⟩ := h_hor (ε / 2) (by linarith)
  refine ⟨max T_rect T_hor, lt_of_lt_of_le hT_rect_pos (le_max_left _ _),
    fun T hT hGood => ?_⟩
  have hT_ge_rect : T_rect ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_hor : T_hor ≤ T := le_trans (le_max_right _ _) hT
  have hT_pos : 0 < T := lt_of_lt_of_le hT_rect_pos hT_ge_rect
  -- Boundary decomposition at finite T.
  have h_bnd :=
    rectContourIntegral_weilIntegrand_pairTestMellin_eq_boundary_forms_with_origin_neg_one
      β (T := T) hT_pos
  -- rectContour close to limitVal.
  have h_rect_close : ‖rectContourIntegral (-1 : ℝ) 2 T
        (weilIntegrand (pairTestMellin β)) - limitVal‖ < ε / 2 :=
    hT_rect T hT_ge_rect hGood
  -- Horizontal diff close to 0.
  have h_hor_close : ‖(∫ x : ℝ in (-1 : ℝ)..2,
        weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I)) -
          (∫ x : ℝ in (-1 : ℝ)..2,
            weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I))‖ < ε / 2 :=
    hT_hor T hT_ge_hor hGood
  -- Substitute h_bnd into h_rect_close.
  rw [h_bnd] at h_rect_close
  -- h_rect_close : ‖((∫bot - ∫top) + I·∫right) - I·∫left - limitVal‖ < ε / 2
  -- Goal: ‖(I·∫right - I·∫left) - 2πi·(...)‖ < ε
  -- Use h_eq : limitVal = 2πi·(...), substitute back.
  rw [← h_eq]
  -- Triangle inequality: ‖(I·∫right - I·∫left) - limitVal‖
  --   ≤ ‖((∫bot - ∫top) + I·∫right - I·∫left) - limitVal‖ + ‖∫bot - ∫top‖
  set bot := ∫ x : ℝ in (-1 : ℝ)..2,
      weilIntegrand (pairTestMellin β) ((x : ℂ) + (-T : ℝ) * I) with hbot_def
  set top := ∫ x : ℝ in (-1 : ℝ)..2,
      weilIntegrand (pairTestMellin β) ((x : ℂ) + (T : ℝ) * I) with htop_def
  set right := ∫ y : ℝ in (-T : ℝ)..T,
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((2 : ℂ) + (y : ℂ) * I) *
        pairTestMellin β ((2 : ℂ) + (y : ℂ) * I) with hright_def
  set left := ∫ y : ℝ in (-T : ℝ)..T,
      hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) with hleft_def
  -- h_rect_close : ‖((bot - top) + I•right - I•left) - limitVal‖ < ε/2
  -- h_hor_close : ‖bot - top‖ < ε/2
  -- Goal: ‖(I•right - I•left) - limitVal‖ < ε
  have h_rearrange : (I • right - I • left) - limitVal =
      (((bot - top) + I • right) - I • left - limitVal) - (bot - top) := by ring
  rw [h_rearrange]
  calc ‖(((bot - top) + I • right) - I • left - limitVal) - (bot - top)‖
      ≤ ‖((bot - top) + I • right) - I • left - limitVal‖ + ‖bot - top‖ :=
        norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ## §1e. T → ∞ right-edge integral limit -/

/-- **Step 1e (right edge)**: `∫_(-T)^T primeIntegrand β 2 y dy → ∫_ℝ primeIntegrand β 2 y dy`
as `T → ∞`. Uses the proved integrability of `primeIntegrand β 2`. -/
theorem rightEdge_integral_tendsto (β : ℝ) :
    Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, primeIntegrand β 2 y)
      Filter.atTop (nhds (∫ y : ℝ, primeIntegrand β 2 y)) := by
  refine MeasureTheory.intervalIntegral_tendsto_integral
    (primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)) ?_ ?_
  · exact Filter.tendsto_neg_atTop_atBot
  · exact Filter.tendsto_id

/-! ## §1e (continued). Left edge: pairTestMellin global quadratic bound at σ = -1 -/

/-- Continuity of `pairTestMellin β (-1 + iy)` in `y`. From
`pairTestMellin_differentiableAt_re_gt_neg_four`. -/
theorem pairTestMellin_left_edge_continuous (β : ℝ) :
    Continuous (fun y : ℝ => pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply ContinuousAt.comp
  · exact (Contour.pairTestMellin_differentiableAt_re_gt_neg_four β
              (s := ((-1 : ℝ) : ℂ) + (y : ℂ) * I) (by simp)).continuousAt
  · exact (by fun_prop : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I)).continuousAt

/-- Global quadratic majorant `K · 1/(1+y²)` for `‖pairTestMellin β (-1+iy)‖`.
Combines `pairTestMellin_quartic_bound_extended` (tail decay for `|y| ≥ 2`)
with continuity (compact-bounded on `|y| ≤ 2`). -/
theorem pairTestMellin_left_edge_global_quadratic_bound (β : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      ‖pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  -- Conjugate symmetry: ‖pairTestMellin β (-1 + y*I)‖ = ‖pairTestMellin β (-1 + (-y)*I)‖
  have h_sym : ∀ y : ℝ, ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖ =
      ‖pairTestMellin β (((-1:ℝ):ℂ) + (-y:ℂ)*I)‖ := by
    intro y
    simp only [pairTestMellin, mellin]
    have h_eq : ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (((-1:ℝ):ℂ) + (y:ℂ)*I - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
        starRingEnd ℂ (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (((-1:ℝ):ℂ) + (-y:ℂ)*I - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)) := by
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem
          measurableSet_Ioi (fun t (ht : (0:ℝ) < t) => ?_))]
      · exact integral_conj
      · simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
        congr 1
        rw [show (((-1:ℝ):ℂ) + (y:ℂ)*I - 1) =
            starRingEnd ℂ (((-1:ℝ):ℂ) + (-y:ℂ)*I - 1) from by
          simp only [map_add, map_sub, map_mul, map_neg,
                     Complex.conj_ofReal, Complex.conj_I, map_one]; ring]
        rw [Complex.cpow_conj _ _ (by
          rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne)]
        rw [Complex.conj_ofReal]
    rw [h_eq, RCLike.norm_conj]
  obtain ⟨C, hC_nn, hC_bd⟩ := HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended β
  -- Continuous on compact [-2, 2] gives bound M.
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-2:ℝ)) (b := 2))
    (pairTestMellin_left_edge_continuous β).norm.continuousOn
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  refine ⟨max (5 * C) (5 * M), le_max_of_le_left (by positivity), fun y => ?_⟩
  have h_pos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rcases le_or_gt 2 |y| with hy | hy
  · -- |y| ≥ 2: use quartic bound.
    have hσ_in : (-1 : ℝ) ∈ Set.Icc (-1:ℝ) 2 := ⟨le_refl _, by norm_num⟩
    -- Bound ‖.‖ ≤ C / |y|^4
    have hbnd_abs : ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖ ≤ C / |y|^4 := by
      rcases le_or_gt 0 y with hy_nn | hy_neg
      · rw [abs_of_nonneg hy_nn]
        have h := hC_bd (-1) hσ_in y (by rwa [abs_of_nonneg hy_nn] at hy)
        exact h
      · rw [abs_of_neg hy_neg, h_sym y]
        have h := hC_bd (-1) hσ_in (-y) (by rwa [abs_of_neg hy_neg] at hy)
        convert h using 2; push_cast; ring
    have habs4 : |y|^4 = y^4 := by
      nlinarith [sq_nonneg (|y|^2 - y^2), sq_abs y]
    rw [habs4] at hbnd_abs
    have hy2 : (4:ℝ) ≤ y^2 := by nlinarith [sq_abs y]
    have hy4_pos : (0:ℝ) < y^4 := by nlinarith [sq_nonneg y]
    calc ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖
        ≤ C / y^4 := hbnd_abs
      _ ≤ max (5 * C) (5 * M) * (1 + y^2)⁻¹ := by
          have h_step : C / y^4 ≤ 5 * C / (1 + y^2) := by
            rw [div_le_div_iff₀ hy4_pos h_pos]
            nlinarith [sq_nonneg (y^2 - 1)]
          calc C / y^4 ≤ 5 * C / (1 + y^2) := h_step
            _ = 5 * C * (1 + y^2)⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ max (5 * C) (5 * M) * (1 + y^2)⁻¹ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- |y| < 2: use compact bound M.
    have hmem : y ∈ Set.Icc (-2:ℝ) 2 :=
      ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    have hbnd : ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖ ≤ M := by
      have := hM y hmem
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
    have h1y2 : 1 + y^2 < 5 := by nlinarith [sq_abs y, abs_nonneg y]
    calc ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖
        ≤ M := hbnd
      _ ≤ 5 * M * (1 + y^2)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ h_pos]; nlinarith
      _ ≤ max (5 * C) (5 * M) * (1 + y^2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Local helper: the arch pair at the reflected right line for the left-edge. -/
private noncomputable def leftEdgeArchPair (y : ℝ) : ℂ :=
  deriv Complex.Gammaℝ ((2:ℂ) + (-y:ℂ)*I) / ((2:ℂ) + (-y:ℂ)*I).Gammaℝ +
    deriv Complex.Gammaℝ (1 - ((2:ℂ) + (-y:ℂ)*I)) / (1 - ((2:ℂ) + (-y:ℂ)*I)).Gammaℝ

/-- Local helper: the reflected right line for the left-edge integrability. -/
private noncomputable def leftEdgeReflectedLine (y : ℝ) : ℂ := (2:ℂ) + (-y:ℂ)*I

/-- The arch-pair term at `z = -1+y*I` equals `leftEdgeArchPair y`. -/
private lemma leftEdgeArchPair_eq (y : ℝ) :
    deriv Complex.Gammaℝ (((-1:ℝ):ℂ) + (y:ℂ)*I) / (((-1:ℝ):ℂ) + (y:ℂ)*I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - (((-1:ℝ):ℂ) + (y:ℂ)*I)) /
        (1 - (((-1:ℝ):ℂ) + (y:ℂ)*I)).Gammaℝ = leftEdgeArchPair y := by
  simp only [leftEdgeArchPair]; push_cast; ring

/-- The log-deriv-zeta term at `z = -1+y*I` equals `-LSeries vonMangoldt (2-y*I)`. -/
private lemma leftEdgeZeta_eq (y : ℝ) :
    deriv riemannZeta (1 - (((-1:ℝ):ℂ) + (y:ℂ)*I)) /
      riemannZeta (1 - (((-1:ℝ):ℂ) + (y:ℂ)*I)) =
    -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (leftEdgeReflectedLine y) := by
  have hre : (1:ℝ) < (leftEdgeReflectedLine y).re := by simp [leftEdgeReflectedLine]
  have h_eq := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hconv : (1 - (((-1:ℝ):ℂ) + (y:ℂ)*I)) = leftEdgeReflectedLine y := by
    simp [leftEdgeReflectedLine]; ring
  rw [hconv, h_eq]; ring

/-- `hadamardArchBoundaryTerm(-1+y*I) = leftEdgeArchPair y - LSeries vonMangoldt (2-y*I)`. -/
private lemma hadamardArchBoundaryTerm_leftEdge_eq (y : ℝ) :
    hadamardArchBoundaryTerm (((-1:ℝ):ℂ) + (y:ℂ)*I) =
      leftEdgeArchPair y -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (leftEdgeReflectedLine y) := by
  simp only [hadamardArchBoundaryTerm]
  rw [leftEdgeZeta_eq, ← leftEdgeArchPair_eq]
  ring

/-- `leftEdgeArchPair` is continuous. -/
private lemma leftEdgeArchPair_continuous :
    Continuous leftEdgeArchPair := by
  -- Key non-vanishing facts: Gammaℝ ≠ 0 on Re s > 0
  have hGamma_ne : ∀ t : ℝ, ((2:ℂ) + (t:ℂ)*I).Gammaℝ ≠ 0 := fun t =>
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  have hGamma_refl_ne : ∀ t : ℝ, (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ ≠ 0 := fun t => by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : (1 - ((2 : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [hn]
    simp at hre
    have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
    omega
  -- Gammaℝ is analytic (and hence continuous) on the open set where it's nonzero
  have hOpen : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
    have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
      Complex.differentiable_Gammaℝ_inv.continuous
    have h_eq : {s : ℂ | s.Gammaℝ ≠ 0} = (fun s : ℂ => s.Gammaℝ⁻¹) ⁻¹' {z : ℂ | z ≠ 0} := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_preimage]; exact ⟨inv_ne_zero, fun h hs => h (by rw [hs, inv_zero])⟩
    rw [h_eq]; exact IsOpen.preimage h_cont isOpen_ne
  have hAnalytic : AnalyticOnNhd ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
    apply DifferentiableOn.analyticOnNhd
    · intro s hs; exact (Contour.differentiableAt_Gammaℝ_of_ne_zero hs).differentiableWithinAt
    · exact hOpen
  -- Continuity of Gammaℝ and deriv Gammaℝ on the line Re=2
  have h_line : Continuous (fun t : ℝ => (2:ℂ) + (t:ℂ)*I) := by fun_prop
  have h_refl : Continuous (fun t : ℝ => 1 - ((2:ℂ) + (t:ℂ)*I)) := by fun_prop
  have h_line_mem : ∀ t : ℝ, (2:ℂ) + (t:ℂ)*I ∈ {s : ℂ | s.Gammaℝ ≠ 0} := hGamma_ne
  have h_refl_mem : ∀ t : ℝ, 1 - ((2:ℂ) + (t:ℂ)*I) ∈ {s : ℂ | s.Gammaℝ ≠ 0} := hGamma_refl_ne
  have h_GCont : Continuous (fun t : ℝ => ((2:ℂ) + (t:ℂ)*I).Gammaℝ) :=
    hAnalytic.continuousOn.comp_continuous h_line h_line_mem
  have h_GReflCont : Continuous (fun t : ℝ => (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) :=
    hAnalytic.continuousOn.comp_continuous h_refl h_refl_mem
  have h_dGCont : Continuous (fun t : ℝ => deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I)) :=
    hAnalytic.deriv.continuousOn.comp_continuous h_line h_line_mem
  have h_dGReflCont : Continuous (fun t : ℝ => deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I))) :=
    hAnalytic.deriv.continuousOn.comp_continuous h_refl h_refl_mem
  have h_arch : Continuous (fun t : ℝ =>
      deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I) / ((2:ℂ) + (t:ℂ)*I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I)) / (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) :=
    (h_dGCont.div h_GCont hGamma_ne).add (h_dGReflCont.div h_GReflCont hGamma_refl_ne)
  -- leftEdgeArchPair y = arch operator at t = -y
  have h_comp : leftEdgeArchPair = (fun t : ℝ =>
      deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I) / ((2:ℂ) + (t:ℂ)*I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I)) /
        (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) ∘ Neg.neg := by
    ext y; simp [leftEdgeArchPair, Function.comp]
  rw [h_comp]
  exact h_arch.comp continuous_neg

/-- The reflected LSeries is continuous along the left edge. -/
private lemma leftEdgeReflectedLine_LSeries_continuous :
    Continuous (fun y : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (leftEdgeReflectedLine y)) := by
  -- LSeries vonMangoldt has a derivative at every s with Re s > 1 (via LSeries_hasDerivAt)
  -- and the reflected line has Re = 2 > 1.
  set f := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have h_line : Continuous (fun y : ℝ => leftEdgeReflectedLine y) := by
    simp only [leftEdgeReflectedLine]; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro y
  have h_re : LSeries.abscissaOfAbsConv f < ↑(leftEdgeReflectedLine y).re := by
    have h1 : (leftEdgeReflectedLine y).re = 2 := by simp [leftEdgeReflectedLine]
    rw [h1]
    calc LSeries.abscissaOfAbsConv f
        ≤ (1 : EReal) := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
              (fun σ hσ => ArithmeticFunction.LSeriesSummable_vonMangoldt
                (by exact_mod_cast hσ))
      _ < (2 : ℝ) := by norm_cast
  exact ((LSeries_differentiableOn f).differentiableAt
      (isOpen_re_gt_EReal _ |>.mem_nhds h_re)).continuousAt.comp h_line.continuousAt

private lemma one_plus_abs_sq_le (t : ℝ) : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
  have h_t_sq : t^2 = |t|^2 := (sq_abs t).symm
  have h_twoabs : 2 * |t| ≤ 1 + |t|^2 := by nlinarith [sq_nonneg (|t| - 1)]
  nlinarith [h_t_sq, h_twoabs]

private lemma pow_div_le_rpow_local (t : ℝ) {N : ℝ} (hN_nn : 0 ≤ N) :
    (1 + |t|)^N / (1 + t^2) ≤ 2^(N / 2) * (1 + t^2)^((N - 2) / 2) := by
  have h_base_nn : (0 : ℝ) ≤ 1 + |t| := by positivity
  have h_t_sq_nn : (0 : ℝ) ≤ 1 + t^2 := by positivity
  have h_t_sq_pos : (0 : ℝ) < 1 + t^2 := by positivity
  have h_pow_bd : (1 + |t|)^N ≤ 2^(N / 2) * (1 + t^2)^(N / 2) := by
    have h_sq_le : (1 + |t|)^2 ≤ 2 * (1 + t^2) := one_plus_abs_sq_le t
    have hN_half_nn : (0 : ℝ) ≤ N / 2 := by linarith
    have h_lhs_eq : ((1 + |t|)^2)^(N / 2) = (1 + |t|)^N := by
      rw [show ((1 + |t|)^2 : ℝ) = (1 + |t|)^(2 : ℕ) from rfl,
          ← Real.rpow_natCast (1 + |t|) 2, ← Real.rpow_mul h_base_nn]
      congr 1; push_cast; ring
    have h_rhs_eq : (2 * (1 + t^2))^(N / 2) = 2^(N / 2) * (1 + t^2)^(N / 2) :=
      Real.mul_rpow (by norm_num) h_t_sq_nn
    rw [← h_lhs_eq, ← h_rhs_eq]
    exact Real.rpow_le_rpow (by positivity) h_sq_le hN_half_nn
  have h_split : 2^(N / 2) * (1 + t^2)^(N / 2) / (1 + t^2) =
      2^(N / 2) * (1 + t^2)^((N - 2) / 2) := by
    rw [mul_div_assoc]; congr 1
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (1 + t^2), ← Real.rpow_add h_t_sq_pos]
    congr 1; ring
  calc (1 + |t|)^N / (1 + t^2)
      ≤ 2^(N / 2) * (1 + t^2)^(N / 2) / (1 + t^2) :=
        div_le_div_of_nonneg_right h_pow_bd h_t_sq_nn
    _ = 2^(N / 2) * (1 + t^2)^((N - 2) / 2) := h_split

/-- The left-edge boundary form is integrable on ℝ for `pairTestMellin β`. -/
theorem leftEdge_pairTestMellin_integrable (β : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ =>
      hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
      pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) := by
  obtain ⟨C_A, N, hC_A_nn, hN_nn, hN_lt_1, hA_bd⟩ := Contour.arch_subunit_bound_at_two
  obtain ⟨C_L, hC_L_nn, hL_bd⟩ :=
    Contour.LSeries_vonMangoldt_bounded_of_right_of_one 2 (by norm_num)
  obtain ⟨K, hK_nn, hK_bd⟩ := pairTestMellin_left_edge_global_quadratic_bound β
  -- Define the helper function and show it equals the integrand
  let g : ℝ → ℂ := fun y =>
    (leftEdgeArchPair y -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (leftEdgeReflectedLine y)) *
      pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)
  -- Continuity of g
  have h_cont : Continuous g := by
    simp only [g]
    exact (leftEdgeArchPair_continuous.sub leftEdgeReflectedLine_LSeries_continuous).mul
      (pairTestMellin_left_edge_continuous β)
  -- rpow majorant
  let α : ℝ := (N - 2) / 2
  have h_r_gt_one : (1 : ℝ) < 2 - N := by linarith
  have h_rpow_integrable :
      MeasureTheory.Integrable (fun y : ℝ => (1 + ‖y‖^2)^(-(2 - N) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [Module.finrank_self]; exact_mod_cast h_r_gt_one
  have h_rpow_integrable' :
      MeasureTheory.Integrable (fun y : ℝ => (1 + y^2)^α) := by
    refine h_rpow_integrable.congr (MeasureTheory.ae_of_all _ ?_)
    intro y
    change (1 + ‖y‖^2)^(-(2-N)/2) = (1 + y^2)^α
    rw [Real.norm_eq_abs, sq_abs]; congr 1; simp [α]
  have h_arch_int :
      MeasureTheory.Integrable (fun y : ℝ => C_A * K * (2^(N/2) * (1 + y^2)^α)) :=
    ((h_rpow_integrable'.const_mul (2^(N/2))).const_mul (C_A * K)).congr
      (MeasureTheory.ae_of_all _ (fun y => by ring))
  have h_prime_int :
      MeasureTheory.Integrable (fun y : ℝ => C_L * K * (1 + y^2)⁻¹) :=
    (integrable_inv_one_add_sq).const_mul (C_L * K)
  have h_majorant_int :
      MeasureTheory.Integrable
        (fun y : ℝ => C_A * K * (2^(N/2) * (1 + y^2)^α) + C_L * K * (1 + y^2)⁻¹) :=
    h_arch_int.add h_prime_int
  -- Pointwise bound on g
  have h_ptwise : ∀ y : ℝ,
      ‖g y‖ ≤ C_A * K * (2^(N/2) * (1 + y^2)^α) + C_L * K * (1 + y^2)⁻¹ := by
    intro y
    have hArch : ‖leftEdgeArchPair y‖ ≤ C_A * (1 + |y|)^N := by
      simp only [leftEdgeArchPair]
      have h := hA_bd (-y)
      simp only [abs_neg] at h; push_cast at h; exact h
    have hL : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (leftEdgeReflectedLine y)‖ ≤ C_L := by
      apply hL_bd
      simp [leftEdgeReflectedLine]
    have hK_y : ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖ ≤ K * (1 + y^2)⁻¹ := hK_bd y
    have h_sum_nn : 0 ≤ C_A * (1 + |y|)^N + C_L :=
      add_nonneg (mul_nonneg hC_A_nn (Real.rpow_nonneg (by positivity) _)) hC_L_nn
    simp only [g]
    rw [norm_mul]
    calc ‖leftEdgeArchPair y -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (leftEdgeReflectedLine y)‖ *
          ‖pairTestMellin β (((-1:ℝ):ℂ) + (y:ℂ)*I)‖
        ≤ (C_A * (1 + |y|)^N + C_L) * (K * (1 + y^2)⁻¹) := by
          apply mul_le_mul _ hK_y (norm_nonneg _) h_sum_nn
          exact (norm_sub_le _ _).trans (add_le_add hArch hL)
      _ = C_A * K * ((1 + |y|)^N / (1 + y^2)) + C_L * K * (1 + y^2)⁻¹ := by ring
      _ ≤ C_A * K * (2^(N/2) * (1 + y^2)^α) + C_L * K * (1 + y^2)⁻¹ := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left
            (pow_div_le_rpow_local y hN_nn) (mul_nonneg hC_A_nn hK_nn)
  have h_int_g : MeasureTheory.Integrable g :=
    h_majorant_int.mono' h_cont.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ h_ptwise)
  -- g equals the original integrand pointwise
  refine h_int_g.congr (MeasureTheory.ae_of_all _ (fun y => ?_))
  simp only [g]
  rw [hadamardArchBoundaryTerm_leftEdge_eq]

/-- Step 1e (left edge): `∫_(-T)^T → ∫_ℝ` for the left-edge boundary integrand. -/
theorem leftEdge_integral_tendsto (β : ℝ) :
    Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T,
        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))
      Filter.atTop
      (nhds (∫ y : ℝ,
        hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I))) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (leftEdge_pairTestMellin_integrable β)
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id

end PairTestIdentity
end WeilPositivity
end ZD

end
