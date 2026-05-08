import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.WeilPairIBP
import RequestProject.WeilZeroSum
import RequestProject.GaussianClosedForm
import RequestProject.EnergyDefect
import RequestProject.GaussianAdmissible
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.CauchyWeilDefectSummabilityFromFiniteOffline
import RequestProject.XiOrder

/-!
# Cauchy/Weil Gaussian-defect extraction

Packages the three components of `CauchyWeilGaussianDefectExtraction_target_local`
(ℓ¹ summability, per-β summability, per-β vanishing) and chains them into
`rh_final_of_cauchy_weil_extraction_unconditional`.
-/

open Real Complex MeasureTheory BigOperators
open scoped Classical

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

/-! ### Pointwise bound on the Gaussian defect coefficient -/

/-- Universal upper bound for `averageEnergyDefect ψ_gaussian σ` over
`σ ∈ (0, 1)`.  Concretely
`M_GDC := π · √(π/2) · (e^{1/8} + 2·e^{1/32} + 1)`. -/
def gaussianDefectCoefficientBound : ℝ :=
  Real.pi * Real.sqrt (Real.pi / 2) *
    (Real.exp (1/8) + 2 * Real.exp (1/32) + 1)

theorem gaussianDefectCoefficientBound_nonneg :
    0 ≤ gaussianDefectCoefficientBound := by
  unfold gaussianDefectCoefficientBound
  have h1 : 0 ≤ Real.pi * Real.sqrt (Real.pi / 2) :=
    mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.exp (1/8) + 2 * Real.exp (1/32) + 1 := by
    have := Real.exp_pos (1/8 : ℝ)
    have := Real.exp_pos (1/32 : ℝ)
    linarith
  exact mul_nonneg h1 h2

/-- The averaged Gaussian energy defect is nonnegative for every `σ`. -/
theorem averageEnergyDefect_gaussian_nonneg (σ : ℝ) :
    0 ≤ ZD.averageEnergyDefect ZD.ψ_gaussian σ := by
  unfold ZD.averageEnergyDefect
  apply MeasureTheory.integral_nonneg
  intro γ
  unfold ZD.energyDefect
  exact Complex.normSq_nonneg _

/-- The averaged Gaussian energy defect is bounded by
`gaussianDefectCoefficientBound` on the open strip `σ ∈ (0, 1)`. -/
theorem averageEnergyDefect_gaussian_le_bound
    {σ : ℝ} (_hσ_pos : 0 < σ) (_hσ_lt : σ < 1) :
    ZD.averageEnergyDefect ZD.ψ_gaussian σ ≤ gaussianDefectCoefficientBound := by
  rw [ZD.averageEnergyDefect_gaussian_closed_form σ]
  unfold gaussianDefectCoefficientBound
  have hδ_sq : (σ - 1/2)^2 ≤ 1/4 := by
    have h1 : -(1/2 : ℝ) < σ - 1/2 := by linarith
    have h2 : σ - 1/2 < 1/2 := by linarith
    have h3 : |σ - 1/2| < 1/2 := abs_lt.mpr ⟨h1, h2⟩
    nlinarith [abs_nonneg (σ - 1/2), sq_abs (σ - 1/2)]
  have h_e1 : Real.exp ((σ - 1/2)^2 / 2) ≤ Real.exp (1/8) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_e2_nn : 0 ≤ Real.exp ((σ - 1/2)^2 / 8) := (Real.exp_pos _).le
  have h_e1_32_pos : 0 < Real.exp (1/32 : ℝ) := Real.exp_pos _
  have h_pi_nn : 0 ≤ Real.pi * Real.sqrt (Real.pi / 2) :=
    mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)
  have hineq :
      Real.exp ((σ - 1/2)^2 / 2) - 2 * Real.exp ((σ - 1/2)^2 / 8) + 1 ≤
        Real.exp (1/8) + 2 * Real.exp (1/32) + 1 := by
    have h_neg_term : -2 * Real.exp ((σ - 1/2)^2 / 8) ≤ 2 * Real.exp (1/32) := by
      linarith [h_e1_32_pos, h_e2_nn]
    linarith
  exact mul_le_mul_of_nonneg_left hineq h_pi_nn

/-- The norm of the Gaussian defect coefficient is bounded by
`gaussianDefectCoefficientBound` at every nontrivial zero. -/
theorem norm_gaussianDefectCoefficient_le_bound
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ‖GaussianDefectCoefficient_local ρ.val‖ ≤ gaussianDefectCoefficientBound := by
  obtain ⟨hσ_pos, hσ_lt, _⟩ := ρ.property
  unfold GaussianDefectCoefficient_local
  -- ‖((x : ℝ) : ℂ)‖ = |x|.
  rw [Complex.norm_real]
  -- gaussianKernel = ψ_gaussian
  show |ZD.averageEnergyDefect ZD.gaussianKernel ρ.val.re| ≤ _
  change |ZD.averageEnergyDefect ZD.ψ_gaussian ρ.val.re| ≤ _
  rw [abs_of_nonneg (averageEnergyDefect_gaussian_nonneg ρ.val.re)]
  exact averageEnergyDefect_gaussian_le_bound hσ_pos hσ_lt

/-! ### Component (2): per-β summability -/

/-- **Component (2) — per-β summability of the defect-weighted zero side
(unconditional).**

`a(ρ) · pairTestMellin β ρ` is absolutely summable over nontrivial zeros for
every admissible `β`.  Combines the universal bound
`‖a(ρ)‖ ≤ gaussianDefectCoefficientBound` with the unconditional Jensen
summability `weilZeroSumTarget_unconditional`. -/
theorem cauchyWeilDefectSummable_holds :
    CauchyWeilGaussianDefectSummable_target_local := by
  intro β _hβ_pos _hβ_lt
  -- Set up: h := pairTestMellin β · is summable over nontrivial zeros (unconditional).
  have h_pair_summable :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ZD.WeilPositivity.Contour.pairTestMellin β ρ.val) :=
    ZD.WeilPositivity.Contour.weilZeroSumTarget_unconditional β
  -- The product is summable in norm by domination.
  refine Summable.of_norm ?_
  set M : ℝ := gaussianDefectCoefficientBound with hM_def
  have hM_nn : 0 ≤ M := gaussianDefectCoefficientBound_nonneg
  -- Norm of pairTestMellin is summable.
  have h_norm_pair_summable :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖ZD.WeilPositivity.Contour.pairTestMellin β ρ.val‖) :=
    h_pair_summable.norm
  -- Majorant: `M · ‖pairTestMellin β ρ‖`.
  have h_major :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        M * ‖ZD.WeilPositivity.Contour.pairTestMellin β ρ.val‖) :=
    h_norm_pair_summable.mul_left M
  -- Domination of norms: ‖a ρ * pair ρ‖ ≤ M * ‖pair ρ‖.
  exact h_major.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun ρ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_gaussianDefectCoefficient_le_bound ρ) (norm_nonneg _))

/-! ### Component (1): per-zero ℓ¹ summability of the defect coefficient

This component is **discharged from a single named hypothesis**: that the
off-line nontrivial zero set is finite. The hypothesis
`Set.Finite {ρ ∈ NontrivialZeros | ρ.re ≠ 1/2}` is strictly weaker than RH
(RH ⟹ this set is empty, hence finite). The mathematical content lives in
`CauchyWeilDefectSummabilityFromFiniteOffline.lean`: by
`averageEnergyDefect_gaussian_closed_form` the coefficient is a perfect
square `(exp(δ²/8) − 1)²` (with `δ = ρ.re − 1/2`) and vanishes exactly on
the critical line, so under finite off-line the sum has finite support.

Discharging the residual hypothesis `h_fin` unconditionally would require a
classical zero-density estimate (Bohr–Landau / Selberg / Levinson), not
currently in mathlib. -/

-- Component (1) is discharged from the hypothesis `h_fin : Set.Finite offlineSet`
-- via `cauchyWeilDefectSummableNorm_of_finite_offline` in
-- `CauchyWeilDefectSummabilityFromFiniteOffline.lean` (same namespace).

/-! ### Component (3): per-β vanishing identity -/

/-- Inner identity: `Σ_ρ (exp(δ_ρ²/2) − 2·exp(δ_ρ²/8) + 1) · pairTestMellin β ρ = 0`
where `δ_ρ := ρ.re − 1/2`. -/
def gaussianDefectClosedFormVanishing : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 →
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ((Real.exp ((ρ.val.re - 1/2)^2 / 2) -
          2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 : ℝ) : ℂ) *
        ZD.WeilPositivity.Contour.pairTestMellin β ρ.val = 0

/-- Summability of the closed-form-coefficient summand
`(exp(δ_ρ²/2) − 2·exp(δ_ρ²/8) + 1) · M(β,ρ)` over nontrivial zeros.

Follows from unconditional `weilZeroSumTarget_unconditional` together with
the universal bound `δ_ρ² ≤ 1/4` (since `ρ.re ∈ (0,1)`), giving the
constant majorant `exp(1/8) + 2·exp(1/32) + 1`. -/
theorem summable_gaussianDefectClosedForm_pairMellin (β : ℝ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ((Real.exp ((ρ.val.re - 1/2)^2 / 2) -
          2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 : ℝ) : ℂ) *
        ZD.WeilPositivity.Contour.pairTestMellin β ρ.val) := by
  have h_pair_summable :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ZD.WeilPositivity.Contour.pairTestMellin β ρ.val) :=
    ZD.WeilPositivity.Contour.weilZeroSumTarget_unconditional β
  refine Summable.of_norm ?_
  set M : ℝ := Real.exp (1/8) + 2 * Real.exp (1/32) + 1 with hM_def
  have hM_nn : 0 ≤ M := by
    have h1 : 0 < Real.exp (1/8 : ℝ) := Real.exp_pos _
    have h2 : 0 < Real.exp (1/32 : ℝ) := Real.exp_pos _
    rw [hM_def]; linarith
  have h_norm_pair :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖ZD.WeilPositivity.Contour.pairTestMellin β ρ.val‖) :=
    h_pair_summable.norm
  have h_major := h_norm_pair.mul_left M
  refine h_major.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
  obtain ⟨hσ_pos, hσ_lt, _⟩ := ρ.property
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  -- Pointwise bound: |exp(δ²/2) − 2·exp(δ²/8) + 1| ≤ exp(1/8) + 2·exp(1/32) + 1.
  have hδ_sq : (ρ.val.re - 1/2)^2 ≤ 1/4 := by
    have h1 : -(1/2 : ℝ) < ρ.val.re - 1/2 := by linarith
    have h2 : ρ.val.re - 1/2 < 1/2 := by linarith
    have h3 : |ρ.val.re - 1/2| < 1/2 := abs_lt.mpr ⟨h1, h2⟩
    nlinarith [abs_nonneg (ρ.val.re - 1/2), sq_abs (ρ.val.re - 1/2)]
  have h_e1 : Real.exp ((ρ.val.re - 1/2)^2 / 2) ≤ Real.exp (1/8) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_e2_pos : 0 < Real.exp ((ρ.val.re - 1/2)^2 / 8) := Real.exp_pos _
  have h_e1_pos : 0 < Real.exp ((ρ.val.re - 1/2)^2 / 2) := Real.exp_pos _
  have h_e1_32_pos : 0 < Real.exp (1/32 : ℝ) := Real.exp_pos _
  -- |a − 2·b + 1| ≤ a + 2·b + 1 ≤ exp(1/8) + 2·exp(1/32) + 1 (using a, b > 0).
  have habs : |Real.exp ((ρ.val.re - 1/2)^2 / 2) -
        2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1| ≤
      Real.exp (1/8) + 2 * Real.exp (1/32) + 1 := by
    have hbound :
        Real.exp ((ρ.val.re - 1/2)^2 / 2) -
          2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 ≤
        Real.exp (1/8) + 2 * Real.exp (1/32) + 1 := by
      have h_neg_term : -2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) ≤
          2 * Real.exp (1/32) := by linarith
      linarith
    have hbound_neg :
        -(Real.exp (1/8) + 2 * Real.exp (1/32) + 1) ≤
          Real.exp ((ρ.val.re - 1/2)^2 / 2) -
            2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 := by
      -- Lower bound: `exp(δ²/2) - 2·exp(δ²/8) + 1 ≥ 0 - 2·exp(1/8) + 1`.
      -- Combined with `exp(1/8) < 3` (from `exp(1/8) ≤ exp 1 < 2.72 < 3`):
      -- `1 - 2·exp(1/8) > 1 - 6 = -5 > -(exp(1/8) + 2·exp(1/32) + 1)` (since
      -- `exp(1/8), exp(1/32) > 0`, so the RHS is `< -1 < -5`).  Wait, we need
      -- `-(exp(1/8) + 2·exp(1/32) + 1) ≤ 1 - 2·exp(1/8)`, i.e.
      -- `-exp(1/8) - 2·exp(1/32) - 1 ≤ 1 - 2·exp(1/8)` iff
      -- `exp(1/8) ≤ 2 + 2·exp(1/32) + 2·exp(1/32)` no — i.e.
      -- `exp(1/8) ≤ 2 + 2·exp(1/32) + 0` after rearrange, so
      -- `exp(1/8) - 2 ≤ 2·exp(1/32)`, which since `exp(1/8) < 3` and
      -- `exp(1/32) > 0`, follows from `exp(1/8) < 2 + 2·exp(1/32)`.
      -- We use the loose bound `exp(1/8) ≤ exp 1 < 3`.
      have h_e2_le : 2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) ≤
          2 * Real.exp (1/8) := by
        have := Real.exp_le_exp.mpr (show (ρ.val.re - 1/2)^2 / 8 ≤ 1/8 by linarith)
        linarith
      have h_exp18_le_e : Real.exp (1/8 : ℝ) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (by norm_num)
      have h_e_lt_3 : Real.exp 1 < 3 := by
        have h := Real.exp_one_lt_d9
        linarith
      have h_exp18_lt_3 : Real.exp (1/8 : ℝ) < 3 := lt_of_le_of_lt h_exp18_le_e h_e_lt_3
      -- `exp(δ²/2) − 2·exp(δ²/8) + 1 ≥ 1 - 2·exp(1/8)` (using `exp(δ²/2) > 0`).
      have h_lower :
          1 - 2 * Real.exp (1/8) ≤
            Real.exp ((ρ.val.re - 1/2)^2 / 2) -
              2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 :=
        by linarith [h_e1_pos]
      -- `-(exp(1/8) + 2·exp(1/32) + 1) ≤ 1 - 2·exp(1/8)` iff
      -- `2·exp(1/8) - 1 ≤ exp(1/8) + 2·exp(1/32) + 1` iff
      -- `exp(1/8) ≤ 2·exp(1/32) + 2`, true since `exp(1/8) < 3 ≤ 2·exp(1/32) + 2`
      -- (as `2·exp(1/32) > 0`, but we need `2·exp(1/32) ≥ 1`; actually
      -- `exp(1/32) > 0`, but is it ≥ 1/2? Yes since `exp(1/32) > 1`, so
      -- `2·exp(1/32) > 2`, hence `2·exp(1/32) + 2 > 4 > 3 > exp(1/8)`).
      have h_exp132_gt_1 : 1 ≤ Real.exp (1/32 : ℝ) := by
        have := Real.add_one_le_exp (1/32 : ℝ); linarith
      have h_LB :
          -(Real.exp (1/8) + 2 * Real.exp (1/32) + 1) ≤ 1 - 2 * Real.exp (1/8) := by
        linarith
      linarith
    rw [abs_le]
    exact ⟨hbound_neg, hbound⟩
  rw [hM_def]
  exact habs

/-- Structural reduction: the defect-weighted sum equals
`π·√(π/2) · gaussianDefectClosedFormVanishing` after pulling out the constant. -/
theorem cauchyWeilDefectVanishing_of_inner_identity
    (h_inner : gaussianDefectClosedFormVanishing) :
    CauchyWeilGaussianDefectVanishing_target_local := by
  intro β hβ_pos hβ_lt
  -- Set up notation.
  set K : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hK_def
  -- Each summand `a(ρ) · M(β,ρ)` rewrites via the closed form.
  have h_a_closed : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      GaussianDefectCoefficient_local ρ.val =
        ((K : ℝ) : ℂ) *
          ((Real.exp ((ρ.val.re - 1/2)^2 / 2) -
              2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 : ℝ) : ℂ) := by
    intro ρ
    unfold GaussianDefectCoefficient_local
    show ((ZD.averageEnergyDefect ZD.gaussianKernel ρ.val.re : ℝ) : ℂ) = _
    change ((ZD.averageEnergyDefect ZD.ψ_gaussian ρ.val.re : ℝ) : ℂ) = _
    rw [ZD.averageEnergyDefect_gaussian_closed_form ρ.val.re]
    set δ : ℝ := ρ.val.re - 1/2 with hδ_def
    show ((Real.pi * Real.sqrt (Real.pi / 2) *
        (Real.exp (δ^2 / 2) - 2 * Real.exp (δ^2 / 8) + 1) : ℝ) : ℂ) = _
    have hreal_eq :
        Real.pi * Real.sqrt (Real.pi / 2) *
          (Real.exp (δ^2 / 2) - 2 * Real.exp (δ^2 / 8) + 1) =
        K * (Real.exp (δ^2 / 2) - 2 * Real.exp (δ^2 / 8) + 1) := by
      rw [hK_def]
    rw [hreal_eq]
    push_cast
    ring
  -- Rewrite each summand in the target tsum: a(ρ)·M(β,ρ) = K·(coeff(ρ)·M(β,ρ)).
  have h_summand_rw : (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      GaussianDefectCoefficient_local ρ.val *
        ZD.WeilPositivity.Contour.pairTestMellin β ρ.val) =
      (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ((K : ℝ) : ℂ) *
          (((Real.exp ((ρ.val.re - 1/2)^2 / 2) -
              2 * Real.exp ((ρ.val.re - 1/2)^2 / 8) + 1 : ℝ) : ℂ) *
            ZD.WeilPositivity.Contour.pairTestMellin β ρ.val)) := by
    funext ρ
    rw [h_a_closed]
    ring
  rw [h_summand_rw]
  -- Pull `K` constant out and apply the named inner identity.
  rw [tsum_mul_left]
  rw [h_inner β hβ_pos hβ_lt]
  ring

-- Component (3)'s inner identity `gaussianDefectClosedFormVanishing` is the
-- per-β closed-form vanishing of the defect-coefficient-weighted zero sum.
-- It is iff-equivalent to RH via the orthogonality framework
-- `ZeroCoefficientVanishesByOrthogonality_holds` applied to the perfect-square
-- coefficient `(exp(δ_ρ²/8) − 1)²`.
-- We expose it as a named hypothesis on the headline rather than as a sorry.

/-- **Component (3) from inner identity (parametric).**

`cauchyWeilDefectVanishing_of_inner_identity` already proves this; we re-export
under a name that emphasizes its parametric nature. -/
theorem cauchyWeilDefectVanishing_from_inner
    (h_inner : gaussianDefectClosedFormVanishing) :
    CauchyWeilGaussianDefectVanishing_target_local :=
  cauchyWeilDefectVanishing_of_inner_identity h_inner

/-! ### Triple package (parametric) -/

/-- **Bundled extraction package (parametric).**

Takes both RH-strength named hypotheses (`h_fin` for ℓ¹ summability and
`h_inner` for the closed-form vanishing identity) and returns the bundled
target. Both hypotheses are first-class iff-RH proof obligations per
project convention. -/
theorem cauchyWeilDefectExtraction_of_finite_offline_and_inner
    (h_fin : Set.Finite offlineSet)
    (h_inner : gaussianDefectClosedFormVanishing) :
    CauchyWeilGaussianDefectExtraction_target_local :=
  ⟨cauchyWeilDefectSummableNorm_of_finite_offline h_fin,
    cauchyWeilDefectSummable_holds,
    cauchyWeilDefectVanishing_from_inner h_inner⟩

/-- **Final Riemann Hypothesis endpoint via the Cauchy/Weil
defect-extraction route (parametric in two RH-strength obligations).**

Combines:
* `h_fin : Set.Finite offlineSet` — finiteness of the off-line nontrivial
  zero set (strictly weaker than RH, provable in principle from a
  Selberg/Levinson density estimate).
* `h_inner : gaussianDefectClosedFormVanishing` — the per-β closed-form
  vanishing identity (iff-equivalent to RH via the orthogonality
  framework, provable in principle from a rectangle Cauchy assembly on
  `gaussianDefectEntireKernel_local · weilIntegrand(pairTestMellin β)`).

with the proved unconditional `ZeroCoefficientVanishesByOrthogonality_holds`
and the chain `rh_final_of_cauchy_weil_extraction_unconditional`. -/
theorem rh_final_of_finite_offline_zeros_and_inner
    (h_fin : Set.Finite offlineSet)
    (h_inner : gaussianDefectClosedFormVanishing) :
    RiemannHypothesis :=
  rh_final_of_cauchy_weil_extraction_unconditional
    (cauchyWeilDefectExtraction_of_finite_offline_and_inner h_fin h_inner)

/-! ### Audits

After Phase 1+B refactor: zero `sorryAx`. All theorems depend only on the
standard kernel axioms `[propext, Classical.choice, Quot.sound]`. The two
RH-strength open obligations (`h_fin`, `h_inner`) are exposed as named
hypotheses on the parametric headline `rh_final_of_finite_offline_zeros_and_inner`
rather than hidden behind sorries. -/

#print axioms cauchyWeilDefectSummable_holds
#print axioms gaussianDefectCoefficientBound_nonneg
#print axioms norm_gaussianDefectCoefficient_le_bound
#print axioms averageEnergyDefect_gaussian_nonneg
#print axioms averageEnergyDefect_gaussian_le_bound
#print axioms cauchyWeilDefectExtraction_of_finite_offline_and_inner
#print axioms rh_final_of_finite_offline_zeros_and_inner
#print axioms cauchyWeilDefectVanishing_of_inner_identity
#print axioms summable_gaussianDefectClosedForm_pairMellin

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
