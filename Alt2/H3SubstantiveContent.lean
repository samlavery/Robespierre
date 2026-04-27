import Mathlib
import RequestProject.PairComboClosurePaths
import RequestProject.WeilZeroSumSplitClosedForm
import RequestProject.WeilArchAtNegOne
import RequestProject.WeilWholeLineIdentity
import RequestProject.WeilLeftEdgePrimeSum
import RequestProject.WeilArchPrimeIdentity


open Complex MeasureTheory

noncomputable section

namespace ZD.WeilPositivity.H3SubstantiveContent

open ZD.WeilPositivity.Contour

/-! ## Named substantive content -/

/-- The substantive Weil-side identity reducing H3 to a contour-shift
difference between `∫arch β 2` and `∫arch β (-1)`. -/
def archDiff_eq_zeroSumComplement (β : ℝ) : Prop :=
  (∫ t : ℝ, archIntegrand β 2 t) - (∫ y : ℝ, archIntegrand β (-1) y) =
    (2 * ((Real.pi : ℝ) : ℂ)) *
      (pairTestMellin β 1 -
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
          pairTestMellin β ρ.val) -
        (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
                   ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)))

/-! ## The reduction theorem

H3 ⟺ this named identity (axiom-clean, pure algebra from Step 3c). -/

theorem H3_iff_archDiff (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, reflectedPrimeIntegrand β 2 t) = 0 ↔
    archDiff_eq_zeroSumComplement β := by
  rw [ZD.WeilPositivity.PairComboClosurePaths.form_C_iff_archEqPrimeSum β hβ]
  have h_3c := ZD.WeilPositivity.ZeroSumSplit.zeroSum_closed_form_split β hβ
  unfold archDiff_eq_zeroSumComplement
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_ne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h_pi_pos.ne'
  -- Direct linear_combination attempt using h_3c with coefficient 2π.
  -- The h_3c has (1/(2π))·∫arch term which linear_combination handles.
  constructor
  · intro h
    linear_combination (norm := (field_simp; ring))
      h + (2 * ((Real.pi : ℝ) : ℂ)) * h_3c
  · intro h
    linear_combination (norm := (field_simp; ring))
      h - (2 * ((Real.pi : ℝ) : ℂ)) * h_3c

/-! ## Unconditional equational form of the H3 obstruction

The iff `H3_iff_archDiff` is the cleanest reduction of H3, but it is iff-shaped:
to USE it one must already know either H3 or `archDiff_eq_zeroSumComplement`. The
following theorem strengthens this by extracting an *unconditional* equational
identity that exposes `∫reflectedPrimeIntegrand β 2` as a *single explicit
correction term* relative to `archDiff_eq_zeroSumComplement`.

Concretely, for every `β ∈ (0, 1)`,
```
∫arch β 2 − ∫arch β (-1)
   = 2π · (M(1) − Σ' − Σ_-)
     − ∫reflectedPrimeIntegrand β 2
```
holds **with no extra hypotheses**. Closing H3 (i.e. proving the integral on
the RHS vanishes) and proving `archDiff_eq_zeroSumComplement β` are
*propositionally identical* — this theorem makes that identity explicit at the
level of named complex numbers, so downstream code can do residue/contour
manipulations against `∫reflectedPrimeIntegrand β 2` directly without going
through the iff.

The proof composes three previously proved unconditional facts:
* `wholeLineWeilIdentity` (Step 1f) — the residue-side identity at infinity.
* `weilArchPrimeIdentityTarget_at_two` — `∫arch β 2 = ∫prime β 2 − ∫reflected β 2`.
* `leftEdge_reflectedPrime_eq_sum` (Step 2b) — `∫reflected β (-1) = -2π · Σ_-`.
plus `leftEdge_integrand_decomposition` (split of the σ=-1 boundary integrand).
-/

open ZD.WeilPositivity.PairTestIdentity
open ZD.WeilPositivity.LeftEdgePrimeSum
open ZD.WeilPositivity.ArchAtNegOne

/-- **Unconditional equational form of the H3 reduction.**

Combines `wholeLineWeilIdentity`, `weilArchPrimeIdentityTarget_at_two`,
`leftEdge_integrand_decomposition`, and `leftEdge_reflectedPrime_eq_sum` to
extract the explicit unconditional equation
```
∫arch β 2 − ∫arch β (-1) = 2π · (M(1) − Σ' − Σ_-) − ∫reflectedPrimeIntegrand β 2.
```
In particular, `archDiff_eq_zeroSumComplement β` ↔ `∫reflectedPrimeIntegrand β 2 = 0`
follows directly by inspection of this equation, mirroring `H3_iff_archDiff`
without the iff. -/
theorem archDiff_eq_zeroSumComplement_minus_reflected
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, archIntegrand β 2 t) - (∫ y : ℝ, archIntegrand β (-1) y) =
      (2 * ((Real.pi : ℝ) : ℂ)) *
        (pairTestMellin β 1 -
          (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (((Classical.choose
              (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
            pairTestMellin β ρ.val) -
          (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
            ((pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ))) -
      ∫ t : ℝ, reflectedPrimeIntegrand β 2 t := by
  have h_1f := wholeLineWeilIdentity β hβ
  have h_2b := leftEdge_reflectedPrime_eq_sum β
  have h_FE := weilArchPrimeIdentityTarget_at_two β
  have h_LE_int :
    (∫ y : ℝ, hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I) *
              pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I)) =
      (∫ y : ℝ, archIntegrand β (-1) y) +
      (∫ y : ℝ,
        (deriv riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I)) /
         riemannZeta (1 - ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I))) *
        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I)) := by
    rw [← MeasureTheory.integral_add (archIntegrand_at_neg_one_integrable β)
        (reflectedPrimeIntegrand_at_neg_one_integrable β)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    exact leftEdge_integrand_decomposition β y
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_1f' : (∫ y : ℝ, primeIntegrand β 2 y) -
                (∫ y : ℝ, hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I) *
                          pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I)) =
              (2 * ((Real.pi : ℝ) : ℂ)) *
                (pairTestMellin β 1 -
                  ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
                    (((Classical.choose
                      (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
                    pairTestMellin β ρ.val) := by
    have h2 : Complex.I * ((∫ y : ℝ, primeIntegrand β 2 y) -
              (∫ y : ℝ, hadamardArchBoundaryTerm ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I) *
                        pairTestMellin β ((((-1 : ℝ) : ℂ)) + (y : ℂ) * Complex.I))) =
              Complex.I * ((2 * ((Real.pi : ℝ) : ℂ)) *
                (pairTestMellin β 1 -
                  ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
                    (((Classical.choose
                      (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
                    pairTestMellin β ρ.val)) := by
      simp only [smul_eq_mul] at h_1f
      linear_combination h_1f
    exact mul_left_cancel₀ hI_ne h2
  rw [h_LE_int, h_2b] at h_1f'
  rw [h_FE]
  -- Unfold `reflectedPrimeIntegrand` definitionally so `linear_combination` matches.
  have h_ref_eq : (∫ t : ℝ, reflectedPrimeIntegrand β 2 t) =
                  ∫ t : ℝ, deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) /
                            riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) *
                            pairTestMellin β ((2 : ℂ) + (t : ℂ) * Complex.I) := rfl
  rw [h_ref_eq]
  linear_combination h_1f'

#print axioms archDiff_eq_zeroSumComplement_minus_reflected

/-- **Direct iff via the equational form.** Combines
`archDiff_eq_zeroSumComplement_minus_reflected` with arithmetic to give the
H3 ⟺ archDiff iff in a single chain (alternative proof of `H3_iff_archDiff`
that does not use `zeroSum_closed_form_split`). Recorded for completeness;
mathematically equivalent to `H3_iff_archDiff`. -/
theorem H3_iff_archDiff_via_wholeLine (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, reflectedPrimeIntegrand β 2 t) = 0 ↔
    archDiff_eq_zeroSumComplement β := by
  have h := archDiff_eq_zeroSumComplement_minus_reflected β hβ
  unfold archDiff_eq_zeroSumComplement
  constructor
  · intro hH3
    rw [hH3, sub_zero] at h
    exact h
  · intro hAD
    -- h  : LHS = X - ∫reflected
    -- hAD: LHS = X
    -- ⇒ ∫reflected = 0
    linear_combination h - hAD

#print axioms H3_iff_archDiff_via_wholeLine

end ZD.WeilPositivity.H3SubstantiveContent
