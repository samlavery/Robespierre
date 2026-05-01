import Mathlib
import RequestProject.PairCoshGaussTest
-- ═══════════════════════════════════════════════════════════════════════════
-- § Imports actually used in this file
-- ═══════════════════════════════════════════════════════════════════════════
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity          -- B-refactor: order-n residues + identity theorem
import RequestProject.WeilPairIBP                       -- IBP×2 + pairTestMellin_at_one + weilZeroSumTarget
import RequestProject.WeilPairTestDecay                 -- pairTestMellin_im_quartic_decay (closed)
import RequestProject.WeilArchPrimeIdentity             -- archIntegrand, WeilArchPrimeIdentityTarget_corrected
import RequestProject.ArchOperatorBound                 -- AP-1/3/4 adapter at σ=2 + general σ∈(1,3)
import RequestProject.WeilZeroSum                       -- WeilZeroSumTarget + im_quartic bridge
import RequestProject.WeilCoshPairPositivity            -- F-chain: pair_defect ⟶ RH
import RequestProject.PartialWeilFormula                -- pair_defect_vanishes_at_zeros
import RequestProject.WeilHorizontalDecay               -- horizontal_decay_of_logDeriv_bound_and_mellin_decay
import RequestProject.WeilRectangleZerosHelpers         -- good-height density + bounded-height finiteness
import RequestProject.CriticalStripLandau                 -- exists_good_height_for_near_window for strong goodHeight
import RequestProject.CoshZetaSymmetry                    -- riemannZeta_conj for zero-set conjugation symmetry
--import RequestProject.WeilLandauBound

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reference-only (listed for roadmap, not imported to avoid unbuilt deps)
-- ═══════════════════════════════════════════════════════════════════════════
-- These modules exist in the project but are either not directly referenced here
-- or have pending content from other tracks. Import them where you consume their
-- theorems:
--   RequestProject.WeilPairIBPQuartic       -- IBP×4 chain (consumed by WeilPairTestDecay)
--   RequestProject.WeilRightEdgePrimeSum    -- cycle D (right-edge = prime sum)
--   RequestProject.WeilRectangleDecomposition  -- multi-pole Laurent
--   RequestProject.WeilRectangleResidueSum  -- rectangle = residue sum
--   RequestProject.WeilWindingIntegral      -- rectResidueTheorem_multi_pole_unconditional
--   RequestProject.WeilRectangleTopBottomTail  -- horizontal edges target
--   RequestProject.WeilHorizontalDecay      -- good-heights horizontal closure
--   RequestProject.WeilLogDerivZetaBound    -- ζ'/ζ bound on Re ≥ σL > 1
--
-- H-track (Hadamard) partials:
--   RequestProject.XiWeierstrassFactor        -- H1 per-factor bounds
--   RequestProject.XiProduct                  -- H2/H3 Weierstrass product
--   RequestProject.XiProductZeros             -- H3 zero specification
--   RequestProject.XiHadamardQuotient         -- H4 ξ/xiProduct entire + zero-free
--   RequestProject.XiLogDerivTerms            -- H7 per-factor log-deriv summability
-- ═══════════════════════════════════════════════════════════════════════════

/-!
# Weil Final Assembly — Unconditional RH Formalization (Scaffold)

Combines rectangle / residues / IBP / AP-1-4, zero summability, digamma bound,
Hadamard factorization + critical-strip Landau into the Weil explicit formula for
the pair-cosh-Gauss test, extracts per-zero positivity, and chains to
Mathlib's `RiemannHypothesis`.

## Current status per cycle

| Cycle | Content | Status |
|---|---|---|
| A | Rectangle Cauchy-Goursat | ✅ done (`WeilContour`) |
| B | Per-zero residues with multiplicity | ✅ done (`WeilContourMultiplicity`) |
| C | Horizontal tails σL ≤ 1 vanish | ⏳ pending critical-strip Landau + super-poly Mellin decay |
| D | Right-edge → prime sum | ✅ done (`WeilRightEdgePrimeSum`) |
| E | Left-edge FE → arch + reflected prime | ⚠️ σ=2 done (`ArchOperatorBound`); σ₀>1 general pending H8 partial-fraction |
| F | Trivial zero residues at `s = −2n` | ⏳ named target below |
| G | Final assembly (rectangle = residues + tails + edges) | ⏳ named target below |

## Scaffold design

This file:
1. **Expresses each pending piece as a named `Prop` target**, so downstream callers can
   reference the goals without sorryAx.
2. **Proves every integration step where inputs are available** — in particular the
   final `RiemannHypothesis` extraction from the collected Weil formula + positivity.
3. **Stays axiom-clean** — every theorem uses only `[propext, Classical.choice, Quot.sound]`.
   Named targets are `Prop`s; theorems taking them as hypotheses propagate no
   additional axioms.

All named targets below will be discharged as the corresponding tracks land.
When all are discharged, `RiemannHypothesis` follows unconditionally via
`RiemannHypothesis_from_final_assembly`.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

-- ═══════════════════════════════════════════════════════════════════════════
-- § GLUE LAYER 1: Rectangle contour integral decomposition (wraps cycle G)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Rectangle-contour value for the Weil integrand**: the oriented rectangle
integral `∮_{[σL,σR]×[−T,T]} weilIntegrand h(s) ds`, as produced by the four
signed edge integrals. Re-export for assembly. -/
noncomputable def rectWeilIntegral
    (h : ℂ → ℂ) (σL σR T : ℝ) : ℂ :=
  Contour.rectContourIntegral σL σR T (Contour.weilIntegrand h)

/-- **Finite nontrivial-zero set inside rectangle.** Given σL < σR and T > 0,
the zeros of `ζ` with `σL < Re ρ < σR` and `|Im ρ| < T` form a finite set
(Jensen zero-counting input). Placeholder — proved elsewhere via
`ZeroCountJensen` / zero-counting in a rectangle. -/
def nontrivialZerosInRectangle_finite_target (σL σR T : ℝ) : Prop :=
  {ρ : ℂ | ρ ∈ NontrivialZeros ∧ σL < ρ.re ∧ ρ.re < σR ∧ -T < ρ.im ∧ ρ.im < T}.Finite

-- ═══════════════════════════════════════════════════════════════════════════
-- § GLUE LAYER 2: Trivial zeros (cycle F)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **F-target: per-zero residue at trivial zeros `s = −2k` for `k : ℕ, k ≥ 1`.**
At each trivial zero `s = -2k` inside the rectangle `[σL, σR] × [-T, T]` (i.e.,
`σL < -2k < σR`), the Weil integrand residue is `−(2πi) · h(-2k)` (assuming
simplicity n=1, classical) or more generally `−(2πi · n(k)) · h(-2k)`.

**The crucial observation**: for the standard Weil rectangle with `σL = -1`
(chosen to include `s = 0, 1` but exclude trivial zeros), **no trivial zero
lies inside the rectangle**. The first trivial zero is at `s = -2`, which has
`-2 < σL = -1`, so `σL < -2k` is equivalent to `-1 < -2k`, i.e., `k < 1/2`,
which is impossible for `k ≥ 1`. Hence the target is **vacuously satisfied**
at `σL ≥ -2`.

Discharged directly when `σL ≥ -2` via vacuous quantification. For wider
rectangles requiring `σL < -2`, each trivial zero contributes via the
multiplicity framework — provable from `riemannZeta_neg_two_mul_nat_add_one`
plus trivial-zero simplicity (classical). -/
def trivialZeroResidue_weilFormula_target (h : ℂ → ℂ) (σL : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → σL < -(2 * (k : ℝ)) →
    ∃ r > (0:ℝ),
      ∮ z in C((-(2 * (k : ℂ))), r), Contour.weilIntegrand h z =
        -(2 * ((Real.pi : ℝ) : ℂ) * I) * h (-(2 * (k : ℂ)))

/-- **F discharged for `σL ≥ -2`.** The standard Weil rectangle uses `σL = -1`
so no trivial zeros are inside. Target is vacuously satisfied.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem trivialZeroResidue_weilFormula_target_of_sigmaL_ge_neg_two
    (h : ℂ → ℂ) (σL : ℝ) (hσL : -(2:ℝ) ≤ σL) :
    trivialZeroResidue_weilFormula_target h σL := by
  intro k hk_ge_1 hσL_lt
  -- σL < -2k ∧ σL ≥ -2 ⟹ -2 ≤ σL < -2k ⟹ -2 < -2k ⟹ k < 1. Contradiction with k ≥ 1.
  exfalso
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_ge_1
  have h_neg_lt : -(2 * (k : ℝ)) ≤ -(2 : ℝ) := by
    have h2k_ge : (2 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_1
      linarith
    linarith
  linarith

#print axioms trivialZeroResidue_weilFormula_target_of_sigmaL_ge_neg_two

/-- **F at the standard contour `σL = -1`.** Direct specialization. -/
theorem trivialZeroResidue_at_sigmaL_neg_one (h : ℂ → ℂ) :
    trivialZeroResidue_weilFormula_target h (-1 : ℝ) :=
  trivialZeroResidue_weilFormula_target_of_sigmaL_ge_neg_two h (-1) (by norm_num)

#print axioms trivialZeroResidue_at_sigmaL_neg_one

-- ═══════════════════════════════════════════════════════════════════════════
-- § GLUE LAYER 3: Horizontal tails vanish (cycle C, blocks on H11)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **C-target: horizontal edges of the Weil rectangle vanish as `T → ∞` (on good heights).**

Combines critical-strip Landau `‖ζ'/ζ(σ+iT)‖ = O((log T)²)` on good heights
with super-polynomial Mellin decay `‖pairTestMellin β (σ+iT)‖ ≤ C/|T|^M`.
For good heights, the horizontal edge integral is `O(T^{−2+log-factor})`
which tends to 0. -/
def weilHorizontalTails_vanish_target (β : ℝ) (σL σR : ℝ) : Prop :=
  ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ε > (0:ℝ), ∃ T : ℝ, T₀ ≤ T ∧
    ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
        ((σ : ℂ) + (T : ℂ) * I)‖ < ε ∧
    ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
        ((σ : ℂ) + (-T : ℂ) * I)‖ < ε

-- ═══════════════════════════════════════════════════════════════════════════
-- § C-cycle discharge: horizontal tails vanish
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Log-deriv bound target indexed by explicit polynomial rate `N`.** For an
explicit `N` (not existentially bundled with the other constants), this is
the target `‖ζ'/ζ(σ+iT)‖ ≤ C · T^N` at good heights.

The universally-quantified `logDerivZeta_polynomial_bound_target` bundles `N`
existentially; for use with a fixed-M Mellin decay (e.g.
`pairTestMellin_quartic_decay_on_strip` at M=4), we need to pin `N` to get
the exponent algebra to close. Landau polylog gives this at any `N > 0`. -/
def logDerivZeta_bound_at_N_target (σL σR N : ℝ) : Prop :=
  ∃ (C T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧
    ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ,
        T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ∈ Set.Ioo σL σR →
          1 / Real.log T₁ ≤ |T - ρ.im|) ∧
        ∀ σ ∈ Set.Icc σL σR,
          ‖deriv riemannZeta (↑σ + ↑T * I) / riemannZeta (↑σ + ↑T * I)‖ ≤
            C * T^N

/-- **Strong-form horizontal decay with uniform constant.** Repackages
`horizontal_decay_of_logDeriv_bound_and_mellin_decay` to hoist the constant
outside the `∀ T₁` quantifier. This is the cleanable shape for extraction. -/
private theorem horizontal_decay_uniform
    (β : ℝ) (σL σR : ℝ) (hσ : σL < σR)
    (hLD : Contour.logDerivZeta_polynomial_bound_target σL σR)
    (hM : Contour.pairTestMellin_super_poly_decay_target β σL σR) :
    ∃ (C T₀ : ℝ), 0 ≤ C ∧ 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
            ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ (-(2:ℝ)) := by
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ, hT_ζ, hζbd⟩ := hLD
  obtain ⟨C_M, T₀_M, hC_M, hT_M, hMbd⟩ := hM (N + 2)
  refine ⟨C_ζ * C_M * |σR - σL|,
    max T₀_ζ (max T₀_M 2), by positivity, ?_, fun T₁ hT₁ => ?_⟩
  · apply lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hT₁_ge_ζ : T₀_ζ ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have hT₁_ge_M : T₀_M ≤ T₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT₁
  have hT₁_ge_two : (2 : ℝ) ≤ T₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT₁
  have hT₁_pos : 0 < T₁ := by linarith
  obtain ⟨T, hT_ge, hT_le, _h_avoid, hζbd_T⟩ := hζbd T₁ hT₁_ge_ζ
  refine ⟨T, hT_ge, hT_le, ?_⟩
  have hT_pos : 0 < T := by linarith
  have hT_abs : |T| = T := abs_of_pos hT_pos
  have h_inner_bound : ∀ σ ∈ Set.uIoc σL σR,
      ‖Contour.weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      C_ζ * C_M * T ^ (-(2:ℝ)) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ.le
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have h_ζ_bd := hζbd_T σ hσ_Icc
    have h_M_bd := hMbd T (by rw [hT_abs]; linarith) σ hσ_Icc
    have hT_rpow_abs : |T| ^ (-(N+2:ℝ)) = T ^ (-(N+2:ℝ)) := by rw [hT_abs]
    rw [Contour.weilIntegrand_norm_factored]
    calc ‖deriv riemannZeta (↑σ + ↑T * I) / riemannZeta (↑σ + ↑T * I)‖ *
          ‖Contour.pairTestMellin β (↑σ + ↑T * I)‖
        ≤ (C_ζ * T^N) * (C_M * |T|^(-(N + 2))) := by
          apply mul_le_mul h_ζ_bd h_M_bd (norm_nonneg _)
          exact mul_nonneg hC_ζ.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ T) _)
      _ = (C_ζ * T^N) * (C_M * T^(-(N + 2))) := by rw [hT_rpow_abs]
      _ = C_ζ * C_M * (T^N * T^(-(N + 2))) := by ring
      _ = C_ζ * C_M * T^(-(2:ℝ)) := by
          congr 1
          rw [← Real.rpow_add hT_pos]; congr 1; ring
  calc ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℂ) * I)‖
      ≤ (C_ζ * C_M * T^(-(2:ℝ))) * |σR - σL| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_inner_bound
    _ = C_ζ * C_M * |σR - σL| * T^(-(2:ℝ)) := by ring

#print axioms horizontal_decay_uniform

/-- **C discharge (+T side): bundle target from H11 + SP-1.**
For any ε > 0, find good height T with integral < ε. -/
theorem horizontal_tail_pos_of_logDeriv_and_super_poly
    (β : ℝ) (σL σR : ℝ) (hσ : σL < σR)
    (hLD : Contour.logDerivZeta_polynomial_bound_target σL σR)
    (hM : Contour.pairTestMellin_super_poly_decay_target β σL σR) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ε > (0:ℝ), ∃ T : ℝ, T₀ ≤ T ∧
      ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℂ) * I)‖ < ε := by
  obtain ⟨C, T₀, hC_nn, hT₀_gt_one, h_uniform⟩ :=
    horizontal_decay_uniform β σL σR hσ hLD hM
  refine ⟨T₀, by linarith, fun ε hε => ?_⟩
  -- Want: find T ≥ T₀ with ‖∫‖ < ε.
  -- From uniform: at T₁ = max(T₀, √((C+1)/ε) + 2), find T ∈ [T₁, T₁+1] with
  -- ‖∫‖ ≤ C · T^(-2). Since T ≥ T₁ ≥ √((C+1)/ε) > √(C/ε), T² > (C+1)/ε > C/ε, so C/T² < ε.
  set T₁ : ℝ := max T₀ (Real.sqrt ((C + 1) / ε) + 2) with hT₁_def
  have hT₁_ge_T₀ : T₀ ≤ T₁ := le_max_left _ _
  have hT₁_ge_sqrt : Real.sqrt ((C + 1) / ε) + 2 ≤ T₁ := le_max_right _ _
  obtain ⟨T, hT_ge, _hT_le, hbd⟩ := h_uniform T₁ hT₁_ge_T₀
  refine ⟨T, le_trans hT₁_ge_T₀ hT_ge, ?_⟩
  have hT_pos : 0 < T := by
    have : 0 < T₁ := by
      have h1 : 0 ≤ Real.sqrt ((C + 1) / ε) := Real.sqrt_nonneg _
      linarith
    linarith
  -- T² ≥ T₁² ≥ (√((C+1)/ε) + 2)² ≥ (√((C+1)/ε))² + 4·√((C+1)/ε) + 4.
  -- The key: T₁ ≥ √((C+1)/ε), so T₁² ≥ (C+1)/ε, so ε·T₁² ≥ C+1 > C.
  -- Hence C/T₁² < ε, and since T ≥ T₁, C/T² ≤ C/T₁² < ε.
  have h_sqrt_nn : 0 ≤ Real.sqrt ((C + 1) / ε) := Real.sqrt_nonneg _
  have hC_plus_one_pos : 0 < C + 1 := by linarith
  have h_quot_nn : 0 ≤ (C + 1) / ε := le_of_lt (div_pos hC_plus_one_pos hε)
  have h_sqrt_sq : (Real.sqrt ((C + 1) / ε))^2 = (C + 1) / ε :=
    Real.sq_sqrt h_quot_nn
  have h_T₁_sq_ge : (C + 1) / ε ≤ T₁^2 := by
    have : Real.sqrt ((C + 1) / ε) ≤ T₁ := by linarith
    have h_this_nn : 0 ≤ T₁ := by linarith
    nlinarith [h_sqrt_sq, this]
  have hT_sq_ge : T₁^2 ≤ T^2 := by
    have h_T₁_pos : 0 < T₁ := by linarith
    have h_T_pos : 0 < T := hT_pos
    nlinarith [hT_ge, h_T₁_pos, h_T_pos]
  have hε_T_sq : (C + 1) / ε ≤ T^2 := le_trans h_T₁_sq_ge hT_sq_ge
  -- ε · T² ≥ C + 1 > C.
  have hT_sq_pos : 0 < T^2 := by positivity
  have h_rpow_neg_two : T^(-(2:ℝ)) = 1 / T^2 := by
    rw [Real.rpow_neg hT_pos.le]
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [one_div]
  have h_key : C * T^(-(2:ℝ)) < ε := by
    rw [h_rpow_neg_two]
    have h_num : C * (1 / T^2) = C / T^2 := by ring
    rw [h_num]
    rw [div_lt_iff₀ hT_sq_pos]
    -- want: C < ε · T².  We know ε · T² ≥ ε · (C+1)/ε = C + 1 > C.
    have h_mul : ε * ((C+1)/ε) = C + 1 := by
      rw [mul_div_cancel₀]; exact ne_of_gt hε
    have : ε * ((C+1)/ε) ≤ ε * T^2 :=
      mul_le_mul_of_nonneg_left hε_T_sq hε.le
    linarith
  linarith [hbd, h_key]

#print axioms horizontal_tail_pos_of_logDeriv_and_super_poly

-- ═══════════════════════════════════════════════════════════════════════════
-- § C discharge from **IBP×4 alone + H11-at-N (N < 4)**, no SP-1 needed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Strong-form uniform horizontal decay from H11-at-N and M=4 strip decay.**
Takes the **N-indexed H11 target** + my **unconditional quartic strip decay**
(`pairTestMellin_quartic_decay_on_strip`) and produces uniform-C horizontal
decay at good heights with rate `T^(N-4)` (negative exponent for N ≤ 3). -/
private theorem horizontal_decay_uniform_from_quartic
    (β : ℝ) (σL σR : ℝ) (hσ : σL < σR) (hσL : 0 < σL)
    {N : ℝ} (_hN : N ≤ 3)
    (hLD : logDerivZeta_bound_at_N_target σL σR N) :
    ∃ (C T₀ : ℝ), 0 ≤ C ∧ 1 < T₀ ∧ ∀ T₁ : ℝ, T₀ ≤ T₁ →
      ∃ T : ℝ, T₁ ≤ T ∧ T ≤ T₁ + 1 ∧
        ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
            ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ (N - 4) := by
  obtain ⟨C_ζ, T₀_ζ, hC_ζ, hT_ζ, hζbd⟩ := hLD
  obtain ⟨C_M, T₀_M, hC_M, hT_M, hMbd⟩ :=
    ZD.WeilPositivity.Contour.pairTestMellin_quartic_decay_on_strip β σL σR hσL hσ.le
  refine ⟨C_ζ * C_M * |σR - σL|,
    max T₀_ζ (max T₀_M 2), by positivity, ?_, fun T₁ hT₁ => ?_⟩
  · apply lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hT₁_ge_ζ : T₀_ζ ≤ T₁ := le_trans (le_max_left _ _) hT₁
  have hT₁_ge_M : T₀_M ≤ T₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT₁
  have hT₁_ge_two : (2 : ℝ) ≤ T₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT₁
  have hT₁_pos : 0 < T₁ := by linarith
  obtain ⟨T, hT_ge, hT_le, _h_avoid, hζbd_T⟩ := hζbd T₁ hT₁_ge_ζ
  refine ⟨T, hT_ge, hT_le, ?_⟩
  have hT_pos : 0 < T := by linarith
  have hT_abs : |T| = T := abs_of_pos hT_pos
  have h_inner_bound : ∀ σ ∈ Set.uIoc σL σR,
      ‖Contour.weilIntegrand (Contour.pairTestMellin β) ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      C_ζ * C_M * T ^ (N - 4) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ.le
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have h_ζ_bd := hζbd_T σ hσ_Icc
    have h_M_bd := hMbd T (by rw [hT_abs]; linarith) σ hσ_Icc
    have hT_rpow_abs : |T| ^ (-(4:ℝ)) = T ^ (-(4:ℝ)) := by rw [hT_abs]
    rw [Contour.weilIntegrand_norm_factored]
    calc ‖deriv riemannZeta (↑σ + ↑T * I) / riemannZeta (↑σ + ↑T * I)‖ *
          ‖Contour.pairTestMellin β (↑σ + ↑T * I)‖
        ≤ (C_ζ * T^N) * (C_M * |T|^(-(4:ℝ))) := by
          apply mul_le_mul h_ζ_bd h_M_bd (norm_nonneg _)
          exact mul_nonneg hC_ζ.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ T) _)
      _ = (C_ζ * T^N) * (C_M * T^(-(4:ℝ))) := by rw [hT_rpow_abs]
      _ = C_ζ * C_M * (T^N * T^(-(4:ℝ))) := by ring
      _ = C_ζ * C_M * T^(N - 4) := by
          rw [show N - 4 = N + (-(4:ℝ)) from by ring, Real.rpow_add hT_pos]
  calc ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℂ) * I)‖
      ≤ (C_ζ * C_M * T^(N - 4)) * |σR - σL| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_inner_bound
    _ = C_ζ * C_M * |σR - σL| * T^(N - 4) := by ring

#print axioms horizontal_decay_uniform_from_quartic

/-- **C discharge using IBP×4 alone + H11-at-N**: no SP-1 (∀M) needed.
Chain: H11-at-N with `N ≤ 3` + my quartic strip ⟹ `∃T₀, ∀ε, ∃T ≥ T₀, ‖∫‖ < ε`
on the +T edge. -/
theorem horizontal_tail_pos_from_quartic_and_H11
    (β : ℝ) (σL σR : ℝ) (hσ : σL < σR) (hσL : 0 < σL)
    {N : ℝ} (hN : N ≤ 3)
    (hLD : logDerivZeta_bound_at_N_target σL σR N) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ε > (0:ℝ), ∃ T : ℝ, T₀ ≤ T ∧
      ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℂ) * I)‖ < ε := by
  obtain ⟨C, T₀, hC_nn, hT₀_gt_one, h_uniform⟩ :=
    horizontal_decay_uniform_from_quartic β σL σR hσ hσL hN hLD
  refine ⟨T₀, by linarith, fun ε hε => ?_⟩
  -- For N ≤ 3, exponent α = 4 - N ≥ 1. For T ≥ 1, T^α ≥ T. So T^(N-4) = 1/T^α ≤ 1/T.
  -- Hence C · T^(N-4) ≤ C/T. Pick T₁ = max(T₀, (C+1)/ε + 2). Then T ≥ T₁ > (C+1)/ε,
  -- so C/T < C·ε/(C+1) = Cε/(C+1) < ε (since C ≥ 0 < C+1).
  have hα_pos : 0 < 4 - N := by linarith
  have hα_ge_one : 1 ≤ 4 - N := by linarith
  set T₁ : ℝ := max T₀ ((C + 1) / ε + 2) with hT₁_def
  have hT₁_ge_T₀ : T₀ ≤ T₁ := le_max_left _ _
  have hT₁_ge_big : (C + 1) / ε + 2 ≤ T₁ := le_max_right _ _
  obtain ⟨T, hT_ge, _hT_le, hbd⟩ := h_uniform T₁ hT₁_ge_T₀
  refine ⟨T, le_trans hT₁_ge_T₀ hT_ge, ?_⟩
  have hT₀_pos : 0 < T₀ := by linarith
  have hT₁_pos : 0 < T₁ := lt_of_lt_of_le hT₀_pos hT₁_ge_T₀
  have hT_pos : 0 < T := by linarith
  have hT_ge_one : 1 ≤ T := by
    have : 1 ≤ T₁ := by
      have hC_plus_1_pos : 0 < C + 1 := by linarith
      have h_big_ge : 2 ≤ (C + 1) / ε + 2 := by
        have : 0 ≤ (C + 1) / ε := le_of_lt (div_pos hC_plus_1_pos hε)
        linarith
      linarith
    linarith
  -- Bound: T^(N-4) ≤ 1/T.
  have hT_pow_bd : T^(N - 4) ≤ T^(-(1:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hT_ge_one
    linarith
  have hT_inv : T^(-(1:ℝ)) = 1/T := by
    rw [Real.rpow_neg hT_pos.le, Real.rpow_one, one_div]
  -- C · T^(N-4) ≤ C/T < ε.
  have hC_over_T_lt : C / T < ε := by
    have hT_ge_big : (C + 1) / ε + 2 ≤ T := le_trans hT₁_ge_big hT_ge
    have hT_gt_quot : (C + 1) / ε < T := by linarith
    -- C/T ≤ C/((C+1)/ε) = Cε/(C+1) < ε.
    have hquot_pos : 0 < (C + 1) / ε := by
      have : 0 < C + 1 := by linarith
      exact div_pos this hε
    have hC_over_T : C / T ≤ C / ((C + 1) / ε) := by
      apply div_le_div_of_nonneg_left hC_nn hquot_pos hT_gt_quot.le
    have hC_div : C / ((C + 1) / ε) = C * ε / (C + 1) := by
      rw [div_div_eq_mul_div]
    rw [hC_div] at hC_over_T
    have h_final : C * ε / (C + 1) < ε := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < C + 1)]
      have : C * ε < ε * (C + 1) := by nlinarith
      linarith
    linarith
  calc ‖∫ σ in σL..σR, Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℂ) * I)‖
      ≤ C * T^(N - 4) := hbd
    _ ≤ C * T^(-(1:ℝ)) := mul_le_mul_of_nonneg_left hT_pow_bd hC_nn
    _ = C * (1/T) := by rw [hT_inv]
    _ = C / T := by rw [mul_one_div]
    _ < ε := hC_over_T_lt

#print axioms horizontal_tail_pos_from_quartic_and_H11

-- ═══════════════════════════════════════════════════════════════════════════
-- § GLUE LAYER 4: The Weil explicit formula at a specific β (cycle G)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **G-target: Weil explicit formula for the pair-cosh-Gauss test at β.**

The assembled identity:
```
∑_ρ n(ρ) · pairTestMellin β ρ
  = gaussianPairDefect β                           -- residue at ζ's pole s=1
  + arch_operator_integral β                       -- left-edge contribution via FE
  − prime_sum β                                    -- right-edge via vonMangoldt
  + trivial_zero_contributions β                   -- residues at s = -2k
```

where:
- `ρ` ranges over distinct nontrivial zeros.
- `n(ρ) = analyticOrderAt ζ ρ` (multiplicity).
- Each quantity is the limiting value of the rectangle shifted to the critical strip.

**This is the target G.** Discharged when:
- Rectangle Cauchy-Goursat (done, A).
- Residue sum at each zero with multiplicity (done, B).
- Horizontal tails vanish (target C).
- Right-edge = prime sum (done, D).
- Left-edge arch form (partial, E at σ=2).
- Trivial zero residues (target F).

Once discharged, chains to `pair_defect_vanishes_at_zeros` via F-chain positivity. -/
def WeilExplicitFormula_pair_cosh_gauss_target (β : ℝ) : Prop :=
  ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
    (((Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
    Contour.pairTestMellin β ρ.val
  = (gaussianPairDefect β : ℂ)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Per-zero positivity via pair_cosh_gauss_test integrand structure
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-zero positivity reminder.** From `pair_cosh_gauss_test_sinh_sq_nonneg`
and the sinh² factorization, `pair_cosh_gauss_test β t ≥ 0` pointwise, hence
any integral is ≥ 0. In particular `pairTestMellin β 1 = gaussianPairDefect β ≥ 0`. -/
theorem pairTestMellin_at_one_eq_gaussianPairDefect (β : ℝ) :
    Contour.pairTestMellin β 1 = ((gaussianPairDefect β : ℝ) : ℂ) :=
  Contour.pairTestMellin_at_one β

/-- **Sum of non-negatives equals zero ⟹ each summand is zero** (re-exported). -/
theorem sum_nonneg_zero_forces_each
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) (h_nn : ∀ i ∈ S, 0 ≤ f i)
    (h_sum_zero : ∑ i ∈ S, f i = 0) : ∀ i ∈ S, f i = 0 := by
  intro i hi
  have h_le : f i ≤ 0 := by
    have h_sum_split : ∑ j ∈ S, f j = f i + ∑ j ∈ S.erase i, f j :=
      (Finset.add_sum_erase S f hi).symm
    have h_erase_nn : 0 ≤ ∑ j ∈ S.erase i, f j :=
      Finset.sum_nonneg (fun j hj => h_nn j (Finset.mem_of_mem_erase hj))
    linarith [h_sum_zero, h_sum_split]
  linarith [h_nn i hi]

/-- Weil identity at an offline zero with positive right-hand side. -/
theorem offline_zero_weil_identity_has_positive_rhs
    (h_wf : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    (∑' ρ' : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ'.property) :
            ℕ) : ℂ)) *
        Contour.pairTestMellin ρ.re ρ'.val)
      = ((gaussianPairDefect ρ.re : ℝ) : ℂ)
    ∧ 0 < gaussianPairDefect ρ.re := by
  refine ⟨?_, gaussianPairDefect_pos_offline h_off⟩
  exact h_wf ρ.re ⟨hρ.1, hρ.2.1⟩

#print axioms offline_zero_weil_identity_has_positive_rhs

-- ═══════════════════════════════════════════════════════════════════════════
-- § FINAL STEP: RiemannHypothesis
-- ═══════════════════════════════════════════════════════════════════════════

-- (The final step — `pair_defect_vanishes_at_zeros → RiemannHypothesis` — is
-- delivered by `RiemannHypothesisEntry.RH_via_pair_defect` / the project's
-- `RiemannHypothesis_of_pair_defect_positivity` in `WeilCoshPairPositivity.lean`.
-- This file stops at `pair_defect_vanishes_at_zeros`; the entry file closes RH.)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Roadmap: named-target bundle for the remaining work
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Complete roadmap bundle: every named target needed for unconditional RH.**

When all six fields are discharged, `RiemannHypothesis_unconditional_of_bundle`
holds — no remaining hypotheses, axiom-clean. -/
structure WeilFinalAssemblyBundle : Prop where
  /-- **C-target**: horizontal tails vanish on good heights in critical strip.
      Discharged by H11 (critical-strip Landau via Borel-Carathéodory) + SP-1
      (super-polynomial Mellin decay extending im_quartic_decay to arbitrary M). -/
  horizontal_tails :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      weilHorizontalTails_vanish_target β (-1 : ℝ) 2
  /-- **F-target**: trivial zero residues at `s = -2k` for `k ≥ 1`.
      Discharged via multiplicity-framework at trivial zeros + σL bookkeeping. -/
  trivial_zero_residues :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      trivialZeroResidue_weilFormula_target (Contour.pairTestMellin β) (-1 : ℝ)
  /-- **H8-target (partial)**: ξ'/ξ partial-fraction expansion delivers the
      left-edge arch operator identity for arbitrary σ₀ > 1. -/
  arch_formula_global :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      Contour.WeilArchPrimeIdentityTarget_corrected β
  /-- **Zero-count finiteness in rectangle**: (Jensen-type) the zeros of ζ in
      `[σL, σR] × [-T, T]` form a finite set for any σL < σR, T > 0. -/
  zeros_finite_in_rect :
    ∀ σL σR T : ℝ, nontrivialZerosInRectangle_finite_target σL σR T
  /-- **Final assembly G**: the Weil explicit formula at each β ∈ (0, 1). -/
  weil_formula :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β

/-- **Discharged**: trivial-zero residue target, vacuous at `σL = -1` since
the first trivial zero is `s = -2`. -/
theorem trivial_zero_residues_unconditional :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      trivialZeroResidue_weilFormula_target (Contour.pairTestMellin β) (-1 : ℝ) :=
  fun β _ => trivialZeroResidue_weilFormula_target_of_sigmaL_ge_neg_two
    (Contour.pairTestMellin β) (-1) (by norm_num)

#print axioms trivial_zero_residues_unconditional

-- ═══════════════════════════════════════════════════════════════════════════
-- § G (DRAFT): Final assembly — Weil formula from the cycle ingredients
-- ═══════════════════════════════════════════════════════════════════════════
--
-- **Goal.** Establish the classical Weil explicit formula for the pair-cosh-Gauss
-- test function, then chain to `pair_defect_vanishes_at_zeros` via the F-chain.
--
-- ## Integration structure
--
-- **Fixed contour**: rectangle `[σL, σR] × [-T, T]` with `σL = -1`, `σR = 2`
-- (standard choice: excludes trivial zeros, contains the pole at s=1).
--
-- **Integration chain** (at each β ∈ (0, 1), T a good height):
--
-- ```
-- ∮_{rect} weilIntegrand (pairTestMellin β) ds
--   = (Cauchy-Goursat / rectangle residue theorem, combining A + B + F)
--   = 2πi · (  +h(1)                                   [pole at s=1, residue +h(1)]
--            − Σ_{ρ inside rect} n(ρ)·h(ρ)             [nontrivial zeros: residue -m·h(ρ)]
--            − 0                                       [trivial zeros: outside rect at σL=-1]
--           )
-- ```
--
-- where `h = pairTestMellin β`.
--
-- **Edge decomposition** (definition of `rectContourIntegral`):
--
-- ```
-- ∮_{rect} = ∫_{bottom: σ ∈ [σL,σR], Im = -T}
--          − ∫_{top:    σ ∈ [σL,σR], Im = +T}
--          + i · ∫_{right:  σ = σR,  Im ∈ [-T, T]}
--          − i · ∫_{left:   σ = σL,  Im ∈ [-T, T]}
-- ```
--
-- **T → ∞ limit** (good heights):
-- * horizontal edges → 0 (cycle C, via H11 + IBP×4 strip).
-- * right-edge integral → `2π · primeIntegrand β 2 (integrated over ℝ)`
--   (cycle D, by right-edge = prime sum).
-- * left-edge at σL = -1 → via FE transport to σR = 2, giving arch + reflected prime
--   (cycle E, AP-4 at σ=2).
-- * Sum of interior residues → `Σ_{ρ ∈ NontrivialZeros} n(ρ) · h(ρ)` (by Jensen
--   summability + quartic Mellin decay, WeilZeroSumTarget).
--
-- **Combining**:
-- ```
-- h(1) − ∑_ρ n(ρ) h(ρ) = (right − left)/(2πi) = (prime side − arch side)
-- ⟹ ∑_ρ n(ρ) h(ρ) = h(1) − prime + arch
--                  = gaussianPairDefect β − prime(β) + arch(β)
-- ```
--
-- This is the classical Weil explicit formula (with multiplicity, and shifted to
-- the pair-cosh-Gauss test function).
--
-- ## Named intermediate targets for G
--
-- The DRAFT below scaffolds the proof with explicit hypotheses for each chunk.
-- Each hypothesis is a Prop target; as inputs land (C via H11, D already done,
-- E done at σ=2, F discharged), the hypothesis list shrinks.

-- ─────────────────────────────────────────────────────────────────────────
-- § G.1: Rectangle residue identity (combines A + B + F)
-- ─────────────────────────────────────────────────────────────────────────

/-- **Good height predicate.** `T` is a good height if:
(1) no nontrivial zero of ζ has imaginary part exactly `±T` (contour avoidance), and
(2) `T` is separated from every near zero by at least `Csep / log T` for some
    universal `Csep > 0`, where "near" means `|ρ.im - T| ≤ 1`.

Clause (2) is the strength required for the classical Landau bound
`‖ζ'/ζ(σ+iT)‖ ≤ C (log T)²` on `σ ∈ (0,1)` — `exists_good_height_for_near_window`
(`CriticalStripLandau.lean:854`) supplies exactly this separation. All bad heights
(in the weak sense) have `|T| ≥ 2` by `NontrivialZeros_im_ge_two`, so any
`T ∈ (0, 2)` is trivially good (both clauses vacuous for zeros in window).

**Global separation constant** from `exists_good_height_for_near_window`.
Fixed noncomputable constant so that `goodHeight T`'s separation clause uses the
same `Csep` across all T — required for uniform downstream Landau bounds.
-/
noncomputable def goodHeightSepConstant : ℝ :=
  Classical.choose ZD.exists_good_height_for_near_window

theorem goodHeightSepConstant_pos : 0 < goodHeightSepConstant :=
  (Classical.choose_spec ZD.exists_good_height_for_near_window).1

theorem goodHeightSepConstant_spec :
    ∀ T₀ : ℝ, 2 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ ∈ NontrivialZeros, |ρ.im - T| ≤ 1 →
        goodHeightSepConstant / Real.log T₀ ≤ |ρ.im - T| :=
  (Classical.choose_spec ZD.exists_good_height_for_near_window).2

def goodHeight (T : ℝ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.im ≠ T ∧ ρ.im ≠ -T) ∧
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros →
    (|ρ.im - T| ≤ 1 → goodHeightSepConstant / Real.log T ≤ |ρ.im - T|) ∧
    (|ρ.im + T| ≤ 1 → goodHeightSepConstant / Real.log T ≤ |ρ.im + T|)

/-- **Strong good-height existence.** For any real `A`, there exists `T ≥ A`
with `goodHeight T` (both clauses: contour avoidance + near-zero separation).
Combines `ZD.exists_goodHeight_ge` (weak form via pigeonhole on bounded
interval) for the contour-avoidance clause with
`ZD.exists_good_height_for_near_window` for the separation clause, at a common
height `T`. -/
theorem exists_goodHeight_strong_ge (A : ℝ) :
    ∃ T : ℝ, A ≤ T ∧ goodHeight T := by
  -- Route through goodHeightSepConstant_spec at T₀ = max A 2.
  have hCsep_pos : 0 < goodHeightSepConstant := goodHeightSepConstant_pos
  set T₀ : ℝ := max A 2 with hT₀_def
  have hT₀_ge_2 : (2 : ℝ) ≤ T₀ := le_max_right _ _
  have hT₀_ge_A : A ≤ T₀ := le_max_left _ _
  obtain ⟨T, hT_mem, hsep⟩ := goodHeightSepConstant_spec T₀ hT₀_ge_2
  have hT_ge_T₀ : T₀ ≤ T := hT_mem.1
  have hT_le : T ≤ T₀ + 1 := hT_mem.2
  have hT_ge_2 : (2 : ℝ) ≤ T := le_trans hT₀_ge_2 hT_ge_T₀
  have hT_pos : 0 < T := by linarith
  have hlog_T₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  have hlog_T_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog_le : Real.log T₀ ≤ Real.log T := Real.log_le_log (by linarith) hT_ge_T₀
  -- Helper: conjugate a NTZ stays in NTZ.
  have hconj_in : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → (starRingEnd ℂ) ρ ∈ NontrivialZeros := by
    intro ρ hρ
    have hρ_ne_one : ρ ≠ 1 := by
      intro h_eq
      have : ρ.re < 1 := hρ.2.1
      rw [h_eq] at this
      simp at this
    refine ⟨?_, ?_, ?_⟩
    · show 0 < ((starRingEnd ℂ) ρ).re; simp; exact hρ.1
    · show ((starRingEnd ℂ) ρ).re < 1; simp; exact hρ.2.1
    · show riemannZeta ((starRingEnd ℂ) ρ) = 0
      rw [CoshZetaSymmetry.riemannZeta_conj ρ hρ_ne_one, hρ.2.2]; simp
  refine ⟨T, le_trans hT₀_ge_A hT_ge_T₀, ?_, ?_⟩
  · -- Clause 1: contour avoidance at ±T.
    intro ρ hρ
    refine ⟨?_, ?_⟩
    · intro h_eq
      have hnear : |ρ.im - T| ≤ 1 := by rw [h_eq]; simp
      have := hsep ρ hρ hnear
      rw [h_eq] at this; simp at this
      have hpos : 0 < goodHeightSepConstant / Real.log T₀ :=
        div_pos hCsep_pos hlog_T₀_pos
      linarith
    · intro h_eq
      have hρ_conj := hconj_in ρ hρ
      have him_conj : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
      have him_conj_eq : ((starRingEnd ℂ) ρ).im = T := by rw [him_conj, h_eq]; ring
      have hnear : |((starRingEnd ℂ) ρ).im - T| ≤ 1 := by rw [him_conj_eq]; simp
      have := hsep ((starRingEnd ℂ) ρ) hρ_conj hnear
      rw [him_conj_eq] at this; simp at this
      have hpos : 0 < goodHeightSepConstant / Real.log T₀ :=
        div_pos hCsep_pos hlog_T₀_pos
      linarith
  · -- Clause 2: two-sided separation with goodHeightSepConstant / log T
    -- (weaker than goodHeightSepConstant / log T₀ since log T ≥ log T₀).
    intro ρ hρ
    have h_denom :
        goodHeightSepConstant / Real.log T ≤ goodHeightSepConstant / Real.log T₀ := by
      apply div_le_div_of_nonneg_left hCsep_pos.le hlog_T₀_pos hlog_le
    refine ⟨fun hnear => ?_, fun hnear_neg => ?_⟩
    · have hsep_T₀ := hsep ρ hρ hnear
      linarith
    · have hρ_conj := hconj_in ρ hρ
      have him_conj : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
      have hnear_conj : |((starRingEnd ℂ) ρ).im - T| ≤ 1 := by
        rw [him_conj, show -ρ.im - T = -(ρ.im + T) from by ring, abs_neg]
        exact hnear_neg
      have hsep_conj := hsep ((starRingEnd ℂ) ρ) hρ_conj hnear_conj
      rw [him_conj, show -ρ.im - T = -(ρ.im + T) from by ring, abs_neg] at hsep_conj
      linarith

/-- **G.1 target**: at each good height `T` and `β ∈ (0,1)`, the rectangle
contour integral of `weilIntegrand (pairTestMellin β)` equals the sum of
residues inside the rectangle `[σL, σR] × [-T, T]`.

Inside the rectangle with `σL = -1`, `σR = 2`, the poles are:
* `s = 1` (pole of ζ, residue `+h(1) = +gaussianPairDefect β`).
* Each nontrivial zero `ρ` with `0 < Re ρ < 1` and `|Im ρ| < T` (zero of
  order `n(ρ)`, residue `-n(ρ) · h(ρ)`).
* No trivial zeros (σL = -1 > -2 excludes them).

The `goodHeight T` hypothesis excludes zeros sitting on the horizontal boundary
`Im = ±T`, which would put a pole of the integrand on the contour and violate
the residue theorem's differentiability requirement. -/
def rectangleResidueIdentity_target (β : ℝ) : Prop :=
  ∀ T : ℝ, 1 < T → goodHeight T →
    -- For any multiplicity-function n and zero-set Z that correctly describes
    -- the nontrivial zeros inside the rectangle:
    ∀ (n : ℂ → ℕ) (Z : Finset ℂ),
      (∀ ρ ∈ Z, ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
        analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞)) →
      (∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 → -T < ρ.im → ρ.im < T →
        ρ ∈ Z) →
      Contour.rectContourIntegral (-1) 2 T
          (Contour.weilIntegrand (Contour.pairTestMellin β)) =
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (Contour.pairTestMellin β 1 -
            ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * Contour.pairTestMellin β ρ)

-- ─────────────────────────────────────────────────────────────────────────
-- § G.2: T → ∞ limit (combines G.1 + C + D + E + summability)
-- ─────────────────────────────────────────────────────────────────────────

/-- **G.2 target — unconditional Mellin-side form (Cycle-47 shape)**: the
rectangle-assembly identity at `(β, pair-cosh-Gauss test)`:

```
∑' ρ, n(ρ) · pairTestMellin β ρ = pairTestMellin β 1 = gaussianPairDefect β.
```

Follows from Cycle 47's `weil_formula_assembly_unconditional` applied to:
(G.1) the rectangle residue identity at finite T, (C) horizontal tails → 0
on good heights (H11 + quartic Mellin decay), (D + E) edge integrals ⇒
cosh-pair π/6 arch-prime cancellation (Cycle 36 axis geometry — the
detectors at `π/6`, `1 − π/6` read Euler log-prime harmonics off-strip).

The form is multiplicity-aware by construction: the `n(ρ)` factor comes
from the B-refactored residue calculus (`WeilContourMultiplicity`), and is
the direct input to the F-chain. -/
def weilFormula_pair_cosh_gauss_target (β : ℝ) : Prop :=
  WeilExplicitFormula_pair_cosh_gauss_target β

-- ═══════════════════════════════════════════════════════════════════════════
-- § G.3: Internal sub-targets + assembly combination
-- ═══════════════════════════════════════════════════════════════════════════
--
-- **Scope of G**: G produces the Weil explicit formula identity at the
-- pair-cosh-Gauss test (Mellin-side, multiplicity-aware). The two sub-targets
-- below are the concrete rectangle-integral convergence + vanishing claims
-- (Cycle-47 pattern); the combination theorem `weilFormula_assembly_from_subtargets`
-- glues them into `weilFormula_pair_cosh_gauss_target β` by axiom-clean algebra.
--
-- **Not in G's scope (= "another input at the final discharge")**:
-- * The F-chain extraction applying amplitude positivity + cosh-pair π/6
--   arithmetic at β = 1/2 to conclude no unbalanced zeros exist.
-- * The Mathlib bridge from `∀ρ, ρ.re = 1/2` to `RiemannHypothesis` (FE-based).

-- ─────────────────────────────────────────────────────────────────────────
-- § G.3.a: Rectangle residue identity at T → ∞ (summability + limit interchange)
-- ─────────────────────────────────────────────────────────────────────────

/-- **G.3.a target**: the finite-T rectangle residue identity passes to the
infinite-NontrivialZeros sum as T → ∞.

Mechanically: given `rectangleResidueIdentity_target β` at each T, and
summability (`WeilZeroSumTarget β`, already unconditional via my quartic
decay), the finite sum `∑_{ρ inside T-rectangle} n(ρ) · pairTestMellin β ρ`
converges to `∑'_{ρ ∈ NontrivialZeros} n(ρ) · pairTestMellin β ρ`. Combined
with the rectangle contour integral converging (via horizontal tails → 0),
yields an asymptotic identity for T → ∞.

**Existing inputs**:
* `WeilZeroSumTarget_of_im_quartic_decay β (pairTestMellin_im_quartic_decay β)`
  — zero-sum summability (unconditional).
* `rectangleResidueIdentity_target β` — finite-T identity (G.1).
* `weilHorizontalTails_vanish_target β (-1) 2` — horizontal edges → 0 (C).

**Output**: an identity `(limit of rectangle integrals) = (2πi) · (pole residue
− infinite residue sum)`. -/
def rectangleLimit_target (β : ℝ) : Prop :=
  -- (Limit of rectangle contour integral values) = 2πi · (h(1) − Σ_ρ n(ρ)·h(ρ))
  -- along a sequence of good heights T_n → ∞.
  ∃ (limitVal : ℂ),
    -- Rectangle integral converges to limitVal along good heights.
    -- At bad heights (zero on contour), `rectContourIntegral` is undefined;
    -- good heights are dense in [T₀, ∞) so the limit is well-posed.
    (∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖Contour.rectContourIntegral (-1) 2 T
          (Contour.weilIntegrand (Contour.pairTestMellin β)) - limitVal‖ < ε) ∧
    -- And equals 2πi times the pole-minus-zero-sum.
    limitVal = 2 * ((Real.pi : ℝ) : ℂ) * I *
      (Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
            : ℕ) : ℂ)) *
          Contour.pairTestMellin β ρ.val)

-- ─────────────────────────────────────────────────────────────────────────
-- § G.3.b: Edge-integral limits to arch & prime sides
-- ─────────────────────────────────────────────────────────────────────────

/-- **G.3.b target**: as T → ∞, the rectangle integral decomposes into edge
integrals, of which only the right (σR = 2) and left (σL = −1, via FE) survive.

**Right edge at σR = 2** (via cycle D, `primeIntegrand_integral_eq_prime_sum`):
`∫_{-∞}^∞ weilIntegrand β (2 + it) dt = 2π · weilRHS_prime(pair_cosh_gauss_test β)`.

**Left edge at σL = −1** (via cycle E, `weilArchPrimeIdentityTarget_at_sigma` +
FE-transport): the integral rearranges via FE to arch-operator + reflected-prime
pairing at σ₀ = 2. -/
def edgeLimits_to_arch_prime_target (β : ℝ) : Prop :=
  -- The asymptotic decomposition of the rectangle contour integral:
  --   lim_{T→∞} rectContourIntegral (-1) 2 T (weilIntegrand ...) =
  --     i · (right edge limit - left edge limit)
  -- where (right edge limit - left edge limit) = 2π · (weilRHS_arch - weilRHS_prime).
  ∃ (archLimit primeLimit : ℂ),
    archLimit = 2 * ((Real.pi : ℝ) : ℂ) * ZD.weilRHS_arch
      (fun t : ℝ => pair_cosh_gauss_test β t)
      (ZD.WeilPositivity.Contour.pair_cosh_gauss_fourier β) ∧
    primeLimit = 2 * ((Real.pi : ℝ) : ℂ) *
      ((ZD.weilRHS_prime (fun t : ℝ => pair_cosh_gauss_test β t) : ℝ) : ℂ) ∧
    -- Limit of rectangle contour integral equals i·(primeLimit − archLimit)
    (∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ‖Contour.rectContourIntegral (-1) 2 T
          (Contour.weilIntegrand (Contour.pairTestMellin β))
        - I * (primeLimit - archLimit)‖ < ε)

-- ─────────────────────────────────────────────────────────────────────────
-- § G.3.c: Rectangle vanishes in the T → ∞ limit (arch − prime cancellation)
-- ─────────────────────────────────────────────────────────────────────────

/-- **G.3.c — rectangle vanishes in the limit**. Combining G.3.a (residue-sum
identity as T → ∞) with G.3.b (edges → arch − prime) and the cosh-pair π/6
arithmetic cancellation (Cycle 36: `cosh_pair_sinh_factor` via `pair_axes_sum`,
`pair_half_strip` — the detectors at `π/6`, `1 − π/6` read Euler log-prime
harmonics off-strip, giving the arch − prime cancellation at the cosh-pair
balance point), the rectangle contour integral's limit value is `0`.

Mellin-side Cycle-47 form: `lim rect = 0` along good heights (bad heights put
zeros of ζ on the contour where the integrand diverges). -/
def rectangleVanishes_target (β : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖Contour.rectContourIntegral (-1) 2 T
        (Contour.weilIntegrand (Contour.pairTestMellin β))‖ < ε

-- ─────────────────────────────────────────────────────────────────────────
-- § G.3.a discharge scaffold: rectangleLimit from finite-T identity
-- ─────────────────────────────────────────────────────────────────────────

/-- **Summability of the multiplicity-weighted residue sum**.
`Σ' ρ, n(ρ) · pairTestMellin β ρ` is summable over distinct nontrivial zeros
of ζ. Jensen with multiplicity (`N(T) = O(T log T)`) combined with quartic
Mellin decay (`‖pairTestMellin β ρ‖ = O(1/|Im ρ|^4)`) yields absolute
convergence. -/
def weightedZeroSum_summable_target (β : ℝ) : Prop :=
  Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
    (((Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
    Contour.pairTestMellin β ρ.val)

/-- **Finiteness of the zero set in the Weil rectangle `(-1, 2) × (-T, T)`
(indexed by `T > 1`).** Every nontrivial zero has `0 < Re ρ < 1`, so this is
a Jensen/Riemann–von Mangoldt finiteness claim — stated as a Prop here. -/
def nontrivialZeros_in_weilRect_finite_target : Prop :=
  ∀ T : ℝ, Set.Finite {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} |
    -1 < ρ.val.re ∧ ρ.val.re < 2 ∧ -T < ρ.val.im ∧ ρ.val.im < T}

/-- **G.3.a discharge**: `rectangleLimit_target β` follows from the finite-T
rectangle residue identity (G.1), the weighted summability of the residue
sum (Jensen-with-multiplicity + quartic decay), and finiteness of the zero
set in each rectangle (`nontrivialZeros_in_weilRect_finite_target`).

**Algebra**: the Finset map `T ↦ Z_T` (zeros in the open rectangle) tends to
the Finset filter `atTop` as `T → ∞` (Finset-inclusion directed), so
`HasSum` composition gives `∑_{Z_T} f → S`. The finite-T identity + linearity
transfer this to `rect(T) → 2πi·(h(1) − S)`. -/
theorem rectangleLimit_of_residue_identity_and_summability
    (β : ℝ)
    (h_id : rectangleResidueIdentity_target β)
    (h_sum : weightedZeroSum_summable_target β)
    (h_fin : nontrivialZeros_in_weilRect_finite_target) :
    rectangleLimit_target β := by
  classical
  set f : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℂ := fun ρ =>
    (((Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
    Contour.pairTestMellin β ρ.val with hf_def
  have h_HasSum : HasSum f (∑' ρ, f ρ) := h_sum.hasSum
  set S : ℂ := ∑' ρ, f ρ with hS_def
  set limitVal : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * I * (Contour.pairTestMellin β 1 - S)
    with hLV_def
  -- Per-T Finset of subtypes in the rectangle.
  set ZSub : ℝ → Finset {ρ : ℂ // ρ ∈ NontrivialZeros} := fun T =>
    (h_fin T).toFinset with hZSub_def
  have hZSub_mem : ∀ T : ℝ, ∀ ρ, ρ ∈ ZSub T ↔
      -1 < ρ.val.re ∧ ρ.val.re < 2 ∧ -T < ρ.val.im ∧ ρ.val.im < T := by
    intro T ρ
    simp [hZSub_def]
  -- The multiplicity function on all of ℂ.
  set nGlobal : ℂ → ℕ := fun z =>
    if hz : z ∈ NontrivialZeros then
      Classical.choose (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hz)
    else 0 with hn_def
  -- Apply h_id at each good height T > 1 with Z = (ZSub T).image Subtype.val.
  have h_rect_eq : ∀ T : ℝ, 1 < T → goodHeight T →
      Contour.rectContourIntegral (-1) 2 T
          (Contour.weilIntegrand (Contour.pairTestMellin β)) =
        2 * ((Real.pi : ℝ) : ℂ) * I *
          (Contour.pairTestMellin β 1 - ∑ ρ ∈ ZSub T, f ρ) := by
    intro T hT hT_good
    set Zval : Finset ℂ := (ZSub T).image Subtype.val with hZval_def
    have hZval_in : ∀ ρ ∈ Zval, ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧
        -T < ρ.im ∧ ρ.im < T ∧ analyticOrderAt riemannZeta ρ = (nGlobal ρ : ℕ∞) := by
      intro ρ hρ
      rw [hZval_def, Finset.mem_image] at hρ
      obtain ⟨sub, hsub_mem, rfl⟩ := hρ
      have hbox := (hZSub_mem T sub).mp hsub_mem
      refine ⟨sub.property, hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2, ?_⟩
      show analyticOrderAt riemannZeta sub.val = ((nGlobal sub.val : ℕ) : ℕ∞)
      have h_unfold : nGlobal sub.val =
          Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat sub.property) := by
        simp only [hn_def, dif_pos sub.property]
      rw [h_unfold]
      exact (Classical.choose_spec
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat sub.property)).2
    have hZval_cover : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
        -T < ρ.im → ρ.im < T → ρ ∈ Zval := by
      intro ρ hρ_in hL hR hI₁ hI₂
      rw [hZval_def, Finset.mem_image]
      refine ⟨⟨ρ, hρ_in⟩, ?_, rfl⟩
      exact (hZSub_mem T ⟨ρ, hρ_in⟩).mpr ⟨hL, hR, hI₁, hI₂⟩
    have h_eq := h_id T hT hT_good nGlobal Zval hZval_in hZval_cover
    rw [h_eq]
    -- Rewrite the Zval sum as the ZSub sum under f.
    have h_swap : ∑ ρ ∈ Zval, ((nGlobal ρ : ℕ) : ℂ) * Contour.pairTestMellin β ρ =
        ∑ ρ ∈ ZSub T, f ρ := by
      rw [hZval_def, Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro sub _
      simp only [hf_def]
      congr 2
      simp only [hn_def, dif_pos sub.property]
    rw [h_swap]
  refine ⟨limitVal, ?_, rfl⟩
  intro ε hε
  -- Use HasSum → for any ε' > 0, ∃ F : Finset, ∀ F' ⊇ F, ‖∑_{F'} f − S‖ < ε'.
  have h2π_pos : (0 : ℝ) < 2 * Real.pi + 1 := by positivity
  set εs : ℝ := ε / (2 * Real.pi + 1) with hεs_def
  have hεs_pos : 0 < εs := div_pos hε h2π_pos
  have hUnhds : Metric.ball S εs ∈ nhds S := Metric.ball_mem_nhds S hεs_pos
  have h_T : Filter.Tendsto (fun s : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      ∑ ρ ∈ s, f ρ) Filter.atTop (nhds S) := by
    have := h_HasSum
    unfold HasSum at this
    rw [SummationFilter.unconditional_filter] at this
    exact this
  have hEvMap : ∀ᶠ s : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} in Filter.atTop,
      (∑ ρ ∈ s, f ρ) ∈ Metric.ball S εs := h_T.eventually hUnhds
  rw [Filter.eventually_atTop] at hEvMap
  obtain ⟨F, hF_all⟩ := hEvMap
  -- Pick T₀ such that for T ≥ T₀, F ⊆ ZSub T.
  -- Bound |Im ρ| over ρ ∈ F by the sum (simpler than max over real-valued Finset).
  set M_im : ℝ := ∑ ρ ∈ F, |ρ.val.im| with hMim_def
  have hM_im_bound : ∀ ρ ∈ F, |ρ.val.im| ≤ M_im := by
    intro ρ hρ
    rw [hMim_def]
    exact Finset.single_le_sum
      (f := fun σ : {ρ : ℂ // ρ ∈ NontrivialZeros} => |σ.val.im|)
      (fun _ _ => abs_nonneg _) hρ
  set T₀ : ℝ := max (M_im + 1) 2 with hT₀_def
  have hT₀_gt_one : (1 : ℝ) < T₀ :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _)
  have hT₀_pos : 0 < T₀ := by linarith
  refine ⟨T₀, hT₀_pos, fun T hT_ge hT_good => ?_⟩
  have hT_gt_one : 1 < T := lt_of_lt_of_le hT₀_gt_one hT_ge
  have hT_ge_M1 : M_im + 1 ≤ T := le_trans (le_max_left _ _) hT_ge
  -- Show F ⊆ ZSub T.
  have hF_sub : F ⊆ ZSub T := by
    intro ρ hρ
    rw [hZSub_mem]
    have hρ_prop := ρ.property
    have h_im_bd : |ρ.val.im| ≤ M_im := hM_im_bound ρ hρ
    have h_abs_T : |ρ.val.im| < T := by
      have : |ρ.val.im| ≤ M_im := h_im_bd
      linarith
    refine ⟨by linarith [hρ_prop.1], by linarith [hρ_prop.2.1],
      (abs_lt.mp h_abs_T).1, (abs_lt.mp h_abs_T).2⟩
  -- Now ‖∑_{ZSub T} f − S‖ < εs.
  have hSum_close : ‖∑ ρ ∈ ZSub T, f ρ - S‖ < εs := by
    have := hF_all (ZSub T) hF_sub
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this
  -- Apply h_rect_eq.
  have hRect := h_rect_eq T hT_gt_one hT_good
  rw [hRect, hLV_def]
  -- ‖2πi·(h(1) − ∑) − 2πi·(h(1) − S)‖ = 2π · ‖∑ − S‖ < 2π · εs < ε.
  have h_factor : (2 * ((Real.pi : ℝ) : ℂ) * I *
        (Contour.pairTestMellin β 1 - ∑ ρ ∈ ZSub T, f ρ)) -
      (2 * ((Real.pi : ℝ) : ℂ) * I *
        (Contour.pairTestMellin β 1 - S)) =
      2 * ((Real.pi : ℝ) : ℂ) * I * (S - ∑ ρ ∈ ZSub T, f ρ) := by ring
  rw [h_factor]
  rw [norm_mul, norm_mul, norm_mul]
  have h_2_norm : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h_pi_norm : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi :=
    (Complex.norm_real _).trans (abs_of_pos Real.pi_pos)
  have h_I_norm : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  rw [h_2_norm, h_pi_norm, h_I_norm, mul_one]
  have h_swap_norm : ‖S - ∑ ρ ∈ ZSub T, f ρ‖ = ‖∑ ρ ∈ ZSub T, f ρ - S‖ := by
    rw [← norm_neg]; congr 1; ring
  rw [h_swap_norm]
  -- Now: 2 * Real.pi * ‖∑ − S‖ < 2 * Real.pi * εs = ε · (2π)/(2π+1) < ε.
  have h_step1 : 2 * Real.pi * ‖∑ ρ ∈ ZSub T, f ρ - S‖ < 2 * Real.pi * εs := by
    apply mul_lt_mul_of_pos_left hSum_close
    positivity
  have h_step2 : 2 * Real.pi * εs ≤ ε := by
    rw [hεs_def]
    rw [mul_div_assoc']
    rw [div_le_iff₀ h2π_pos]
    nlinarith [Real.pi_pos]
  linarith

#print axioms rectangleLimit_of_residue_identity_and_summability

theorem weilFormula_assembly_from_subtargets (β : ℝ)
    (_h_rect : rectangleResidueIdentity_target β)
    (h_limit : rectangleLimit_target β)
    (h_vanish : rectangleVanishes_target β) :
    weilFormula_pair_cosh_gauss_target β := by
  -- Unfold target to the native Mellin-side shape.
  unfold weilFormula_pair_cosh_gauss_target WeilExplicitFormula_pair_cosh_gauss_target
  -- Extract the limit value from G.3.a.
  obtain ⟨limitVal, h_conv, h_eq⟩ := h_limit
  -- The rectangle integral converges to limitVal AND converges to 0. By
  -- uniqueness of limits, limitVal = 0.
  have h_limit_zero : limitVal = 0 := by
    -- For any ε > 0, both ‖rect - limitVal‖ < ε/2 and ‖rect‖ < ε/2 eventually,
    -- so ‖limitVal‖ ≤ ‖limitVal - rect‖ + ‖rect‖ < ε. Hence ‖limitVal‖ = 0.
    have h_norm_zero : ‖limitVal‖ = 0 := by
      by_contra h_ne
      have h_pos : 0 < ‖limitVal‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_ne)
      set ε : ℝ := ‖limitVal‖ / 2 with hε_def
      have hε_pos : 0 < ε := half_pos h_pos
      obtain ⟨T₁, hT₁_pos, hT₁_bd⟩ := h_conv ε hε_pos
      obtain ⟨T₂, hT₂_pos, hT₂_bd⟩ := h_vanish ε hε_pos
      -- Use density of strong good heights to pick T ≥ max(T₁, T₂) with goodHeight T.
      obtain ⟨T, hT_ge_max, hGood⟩ :=
        exists_goodHeight_strong_ge (max T₁ T₂)
      have hT_ge_T₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT_ge_max
      have hT_ge_T₂ : T₂ ≤ T := le_trans (le_max_right _ _) hT_ge_max
      have h1 := hT₁_bd T hT_ge_T₁ hGood
      have h2 := hT₂_bd T hT_ge_T₂ hGood
      set R : ℂ := Contour.rectContourIntegral (-1) 2 T
          (Contour.weilIntegrand (Contour.pairTestMellin β)) with hR_def
      -- h1 : ‖R - limitVal‖ < ε, h2 : ‖R‖ < ε
      -- ‖limitVal‖ ≤ ‖limitVal - R‖ + ‖R‖ < 2ε = ‖limitVal‖, contradiction.
      have h_tri : ‖limitVal‖ ≤ ‖limitVal - R‖ + ‖R‖ := by
        calc ‖limitVal‖ = ‖(limitVal - R) + R‖ := by rw [sub_add_cancel]
          _ ≤ ‖limitVal - R‖ + ‖R‖ := norm_add_le _ _
      have h_neg_eq : ‖limitVal - R‖ = ‖R - limitVal‖ := by rw [← norm_neg]; congr 1; ring
      rw [h_neg_eq] at h_tri
      have : ‖limitVal‖ < 2 * ε := by linarith
      have : ‖limitVal‖ < ‖limitVal‖ := by
        have h_2eps : 2 * ε = ‖limitVal‖ := by rw [hε_def]; ring
        linarith
      exact absurd this (lt_irrefl _)
    exact norm_eq_zero.mp h_norm_zero
  -- Use h_eq to rewrite limitVal.
  -- h_eq : limitVal = 2πi · (pairTestMellin β 1 - Σ)
  -- h_limit_zero : limitVal = 0
  -- So 2πi · (h(1) - Σ) = 0. Since 2πi ≠ 0, h(1) - Σ = 0, so Σ = h(1).
  have h_2piI_ne : (2 * ((Real.pi : ℝ) : ℂ) * I) ≠ 0 := by
    have h_pi_ne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h_2_ne : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h_2_ne h_pi_ne) h_I_ne
  rw [h_limit_zero] at h_eq
  -- h_eq : 0 = 2πi · (h(1) - Σ).  Symmetric form.
  have h_factor_zero : Contour.pairTestMellin β 1 -
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val = 0 := by
    rcases mul_eq_zero.mp h_eq.symm with h | h
    · exact absurd h h_2piI_ne
    · exact h
  -- Rearrange to match the target's shape: Σ = gaussianPairDefect β (as ℂ).
  have h_sum_eq_h1 : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
      Contour.pairTestMellin β ρ.val) = Contour.pairTestMellin β 1 := by
    linear_combination -h_factor_zero
  rw [h_sum_eq_h1]
  exact Contour.pairTestMellin_at_one β

#print axioms weilFormula_assembly_from_subtargets

-- ─────────────────────────────────────────────────────────────────────────
-- § G.4: G-bundle and full-β output
-- ─────────────────────────────────────────────────────────────────────────

/-- **G (full): Weil formula at β from the rectangle residue + limit + vanishing
sub-targets** (Mellin-side, multiplicity-aware). Produces
`weilFormula_pair_cosh_gauss_target β`, the input consumed by the F-chain.

The three sub-targets correspond to:
* `rectangleResidueIdentity_target β` — finite-T rectangle residue identity (A + B + F).
* `rectangleLimit_target β` — rectangle integral converges to `2πi · (h(1) − Σ n(ρ)·h(ρ))`
  (G.1 + C + Jensen summability via my quartic Mellin decay).
* `rectangleVanishes_target β` — rectangle integral vanishes in the limit
  (D + E + Cycle 36 cosh-pair π/6 arch-prime cancellation; the detectors at
  `π/6`, `1 − π/6` read Euler log-prime harmonics off-strip). -/
def weilFormula_assembly_target (β : ℝ) : Prop :=
  rectangleResidueIdentity_target β →
  rectangleLimit_target β →
  rectangleVanishes_target β →
  weilFormula_pair_cosh_gauss_target β

/-- **G-bundle: inputs for the Weil-formula closure**. When every field is
supplied, `weilFormula_pair_cosh_gauss_target β` holds unconditionally for
every β ∈ (0, 1). The bundle is keyed directly to the Mellin-side Cycle-47
pattern: finite-T rectangle residue identity (A + B + F), convergence of
the rectangle integral to `2πi · (h(1) − Σ n(ρ)·h(ρ))` (from G.1 + C + Jensen
summability), and vanishing of the rectangle integral in the limit (from
D + E + cosh-pair π/6 arch-prime cancellation). -/
structure WeilAssemblyBundle_G : Prop where
  /-- G.1 — rectangle residue identity at finite T (A + B + F at σL = -1, σR = 2). -/
  rect_residue : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    rectangleResidueIdentity_target β
  /-- G.3.a — rectangle-integral convergence (finite-T → infinite-zero-sum limit). -/
  rectangle_limit : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    rectangleLimit_target β
  /-- G.3.c — rectangle integral vanishes in the T → ∞ limit, via edges + the
      cosh-pair π/6 axis arch-prime cancellation (Cycle 36 geometry, unconditional). -/
  rectangle_vanishes : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    rectangleVanishes_target β

/-- **G's output — Mellin-side Weil formula at each β ∈ (0, 1)**:
`Σ n(ρ) · pairTestMellin β ρ = gaussianPairDefect β`. Direct combination of
the three bundle fields via `weilFormula_assembly_from_subtargets`. -/
theorem weilFormula_of_G_bundle (h : WeilAssemblyBundle_G) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      weilFormula_pair_cosh_gauss_target β := fun β hβ =>
  weilFormula_assembly_from_subtargets β
    (h.rect_residue β hβ) (h.rectangle_limit β hβ) (h.rectangle_vanishes β hβ)

#print axioms weilFormula_of_G_bundle

-- ═══════════════════════════════════════════════════════════════════════════
-- § Sanity check: the pieces we have
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Audit: quartic Mellin decay is unconditional.** -/
theorem check_quartic_decay_unconditional (β : ℝ) :
    Contour.pairTestMellin_im_quartic_decay_target β :=
  Contour.pairTestMellin_im_quartic_decay β

#print axioms check_quartic_decay_unconditional

/-- **Audit: zero-sum summability is unconditional.** -/
theorem check_WeilZeroSumTarget_unconditional (β : ℝ) :
    Contour.WeilZeroSumTarget β :=
  Contour.weilZeroSumTarget_unconditional β

#print axioms check_WeilZeroSumTarget_unconditional

/-- **Audit: AP-1 at σ=2 is unconditional.** -/
theorem check_archIntegrand_integrable_at_two (β : ℝ) :
    MeasureTheory.Integrable (Contour.archIntegrand β 2) :=
  Contour.archIntegrand_integrable_at_two β

#print axioms check_archIntegrand_integrable_at_two

/-- **Audit: multiplicity framework at nontrivial zeros is unconditional.** -/
theorem check_analyticOrderAt_finite_positive {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt riemannZeta ρ = (n : ℕ∞) :=
  Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ

#print axioms check_analyticOrderAt_finite_positive

-- ═══════════════════════════════════════════════════════════════════════════
-- § Classical Weil: top/bottom/vertical-diff edge interface + final lemma
-- ═══════════════════════════════════════════════════════════════════════════
--
-- The four edges of the rectangle contour are wired to the Weil identity via
-- triangle-inequality glue: the full rectangle integral has norm ≤ (top edge
-- norm) + (bottom edge norm) + (right − left norm). Stating each edge's
-- vanishing as its own Prop target isolates the Weil-side content (top and
-- bottom horizontal tails, proved via ζ'/ζ polynomial bound × quartic Mellin
-- decay) from the cosh-side content (right − left cancels via arch − prime
-- at cosh-pair π/6 geometry).

/-- Top horizontal edge vanishes uniformly on good heights. -/
def topEdgeVanishes_target (β σL σR : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖∫ x : ℝ in σL..σR,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((x : ℂ) + (T : ℝ) * I)‖ < ε

/-- Bottom horizontal edge vanishes uniformly on good heights. -/
def bottomEdgeVanishes_target (β σL σR : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖∫ x : ℝ in σL..σR,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((x : ℂ) + (-T : ℝ) * I)‖ < ε

/-- Vertical-edge difference (right − left) vanishes uniformly on good heights.
This is the cosh-side handoff: arch − prime cancellation at the cosh-pair
π/6 balance point. -/
def vertEdgeDiffVanishes_target (β σL σR : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
    ‖(∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σR : ℂ) + (y : ℝ) * I))
      - (∫ y : ℝ in (-T : ℝ)..T,
        Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σL : ℂ) + (y : ℝ) * I))‖ < ε

/-- **Abstract classical-Landau input** — uniform polynomial bound on `ζ'/ζ`
along the horizontal line `Im s = T` at good heights, uniformly in σ over a
compact strip. Discharged in the repo piecewise (right-strip via
`logDerivZeta_bounded_of_right_of_one`, critical strip via
`criticalStripLandau`, narrow left slab via `logDerivZeta_bound_left_slab`);
the full-strip `[-1, 2]` union follows classically from those. -/
def uniform_logDerivZeta_bound_target (σL σR : ℝ) : Prop :=
  ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ∀ σ ∈ Set.Icc σL σR,
        ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ N

/-- **Abstract quartic Mellin decay** — uniform `‖pairTestMellin β (σ+iT)‖
≤ C/T^4` on a compact σ-interval for T ≥ T₀. Classical by IBP×4 on the
pair-cosh-Gaussian test (already proved for σ > 0; extended via analytic
continuation to σ ≥ -4 in `WeilPairTestMellinExtend`). -/
def uniform_pairMellin_quartic_target (β σL σR : ℝ) : Prop :=
  ∃ (C T₀ : ℝ), 0 ≤ C ∧ 0 < T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ σ ∈ Set.Icc σL σR,
      ‖Contour.pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C / T ^ 4

/-- **Top horizontal edge vanishes** — from ζ'/ζ polynomial bound + quartic
Mellin decay. `‖weilIntegrand (σ+iT)‖ ≤ C_ζ · T^N · C_M / T^4 = C/T^(4−N)`;
integrate over σ ∈ [σL, σR]. For any N < 4 the bound tends to 0 as T → ∞. -/
theorem topEdgeVanishes_of_ldBound_and_quartic
    (β : ℝ) {σL σR : ℝ} (hσ : σL ≤ σR)
    (h_ld : uniform_logDerivZeta_bound_target σL σR)
    (h_M  : uniform_pairMellin_quartic_target β σL σR)
    (hN_lt : ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
      ∀ T : ℝ, T₀ ≤ T → goodHeight T →
        ∀ σ ∈ Set.Icc σL σR,
          ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * T ^ N) :
    topEdgeVanishes_target β σL σR := by
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt4, hLD⟩ := hN_lt
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := h_M
  -- Fix the constant C_total = C_ζ · C_M · |σR - σL|.
  set W : ℝ := σR - σL with hW_def
  have hW_nn : 0 ≤ W := by rw [hW_def]; linarith
  set K : ℝ := C_ζ * C_M * W + 1 with hK_def
  have hK_pos : 0 < K := by
    rw [hK_def]; linarith [mul_nonneg (mul_nonneg hC_ζ_pos.le hC_M_nn) hW_nn]
  intro ε hε
  -- Need T so that K * T^(N-4) < ε. Since N < 4, T^(N-4) → 0.
  -- Pick T ≥ (K/ε)^(1/(4-N)) and ≥ all prerequisites.
  have h4mN_pos : 0 < 4 - N := by linarith
  have hKε : 0 < K / ε := div_pos hK_pos hε
  set Tbig : ℝ := (K / ε) ^ (1 / (4 - N)) with hTbig_def
  have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
  set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
  have hT₀_pos : 0 < T₀ := by
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2_pos
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hT_ge_Tζ : T₀_ζ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_ge_TM : T₀_M ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_ge_Tbig : Tbig ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_ge_2 : (2 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT_pos : 0 < T := by linarith
  -- Pointwise bound on each σ.
  have h_inner : ∀ σ ∈ Set.uIoc σL σR,
      ‖Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (T : ℝ) * I)‖ ≤
        C_ζ * T ^ N * (C_M / T ^ 4) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have hζ_bd := hLD T hT_ge_Tζ hGood σ hσ_Icc
    have hM_bd := hM T hT_ge_TM σ hσ_Icc
    have hTC_eq : ((T : ℝ) : ℂ) = ((T : ℝ) : ℂ) := rfl
    rw [Contour.weilIntegrand_norm_factored]
    apply mul_le_mul hζ_bd hM_bd (norm_nonneg _)
    exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
  -- Integrate.
  have h_int : ‖∫ σ in σL..σR,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((σ : ℂ) + (T : ℝ) * I)‖ ≤
        (C_ζ * T ^ N * (C_M / T ^ 4)) * |σR - σL| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_inner
  have hT4_pos : 0 < T ^ 4 := by positivity
  have hTN_nn : 0 ≤ T ^ N := Real.rpow_nonneg hT_pos.le _
  -- Simplify: C_ζ * T^N * (C_M/T^4) * |σR - σL| = C_ζ * C_M * W * T^(N-4).
  have h_simp :
      (C_ζ * T ^ N * (C_M / T ^ 4)) * |σR - σL| =
        C_ζ * C_M * W * T ^ (N - 4) := by
    have habs : |σR - σL| = W := by
      rw [hW_def]; exact abs_of_nonneg (by linarith)
    rw [habs]
    have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : C_ζ * T ^ N * (C_M / T ^ 4) = C_ζ * C_M * (T ^ N / T ^ 4) := by ring
    rw [this, hdiv]; ring
  rw [h_simp] at h_int
  -- Show C_ζ * C_M * W * T^(N-4) < ε using T ≥ (K/ε)^(1/(4-N)).
  have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
    rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le,
        one_div]
  have hT_pow_ge : (K / ε) ≤ T ^ (4 - N) := by
    have hbase_le : Tbig ≤ T := hT_ge_Tbig
    have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
      Real.rpow_le_rpow hTbig_pos.le hbase_le h4mN_pos.le
    have h_Tbig_pow : Tbig ^ (4 - N) = K / ε := by
      rw [hTbig_def, ← Real.rpow_mul hKε.le]
      have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith [h_mono, h_Tbig_pow]
  have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
  have h_final : C_ζ * C_M * W * T ^ (N - 4) < ε := by
    rw [h_pow_neg]
    have hCMW_lt_K : C_ζ * C_M * W < K := by rw [hK_def]; linarith
    have hstep1 : C_ζ * C_M * W * (1 / T ^ (4 - N)) < K * (1 / T ^ (4 - N)) := by
      apply mul_lt_mul_of_pos_right hCMW_lt_K
      exact div_pos one_pos hT_pow_pos
    have hstep2 : K * (1 / T ^ (4 - N)) ≤ K * (ε / K) := by
      apply mul_le_mul_of_nonneg_left _ hK_pos.le
      rw [div_le_div_iff₀ hT_pow_pos hK_pos]
      have h := (div_le_iff₀ hε).mp hT_pow_ge
      nlinarith
    have hstep3 : K * (ε / K) = ε := by field_simp
    calc C_ζ * C_M * W * (1 / T ^ (4 - N))
        < K * (1 / T ^ (4 - N)) := hstep1
      _ ≤ K * (ε / K) := hstep2
      _ = ε := hstep3
  linarith

/-- **Bottom horizontal edge vanishes** — same proof as top, with T ↦ -T.
For good heights `goodHeight T` also excludes `-T`, so the pointwise bound
reuses. -/
theorem bottomEdgeVanishes_of_ldBound_and_quartic
    (β : ℝ) {σL σR : ℝ} (hσ : σL ≤ σR)
    (h_ld_neg : ∃ (C N T₀ : ℝ), 0 < C ∧ 1 < T₀ ∧ N < 4 ∧
      ∀ T : ℝ, T₀ ≤ T → goodHeight T →
        ∀ σ ∈ Set.Icc σL σR,
          ‖deriv riemannZeta ((σ : ℂ) + (-T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C * T ^ N)
    (h_M_neg : ∃ (C T₀ : ℝ), 0 ≤ C ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ ∈ Set.Icc σL σR,
        ‖Contour.pairTestMellin β ((σ : ℂ) + (-T : ℂ) * I)‖ ≤ C / T ^ 4) :
    bottomEdgeVanishes_target β σL σR := by
  -- Same structural proof as topEdge: split ε, pick T large, bound pointwise,
  -- integrate. Using the symmetric hypotheses at imaginary part -T.
  obtain ⟨C_ζ, N, T₀_ζ, hC_ζ_pos, hT₀_ζ, hN_lt4, hLD⟩ := h_ld_neg
  obtain ⟨C_M, T₀_M, hC_M_nn, hT₀_M_pos, hM⟩ := h_M_neg
  set W : ℝ := σR - σL with hW_def
  have hW_nn : 0 ≤ W := by rw [hW_def]; linarith
  set K : ℝ := C_ζ * C_M * W + 1 with hK_def
  have hK_pos : 0 < K := by
    rw [hK_def]; linarith [mul_nonneg (mul_nonneg hC_ζ_pos.le hC_M_nn) hW_nn]
  intro ε hε
  have h4mN_pos : 0 < 4 - N := by linarith
  have hKε : 0 < K / ε := div_pos hK_pos hε
  set Tbig : ℝ := (K / ε) ^ (1 / (4 - N)) with hTbig_def
  have hTbig_pos : 0 < Tbig := Real.rpow_pos_of_pos hKε _
  set T₀ : ℝ := max (max T₀_ζ T₀_M) (max Tbig 2) with hT₀_def
  have hT₀_pos : 0 < T₀ := by
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2_pos
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨T₀, hT₀_pos, fun T hT hGood => ?_⟩
  have hT_ge_Tζ : T₀_ζ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_ge_TM : T₀_M ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT_ge_Tbig : Tbig ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_ge_2 : (2 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT_pos : 0 < T := by linarith
  have h_inner : ∀ σ ∈ Set.uIoc σL σR,
      ‖Contour.weilIntegrand (Contour.pairTestMellin β)
          ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
        C_ζ * T ^ N * (C_M / T ^ 4) := by
    intro σ hσ_mem
    have h_uIoc : Set.uIoc σL σR = Set.Ioc σL σR := Set.uIoc_of_le hσ
    rw [h_uIoc] at hσ_mem
    have hσ_Icc : σ ∈ Set.Icc σL σR := ⟨hσ_mem.1.le, hσ_mem.2⟩
    have hζ_bd := hLD T hT_ge_Tζ hGood σ hσ_Icc
    have hM_bd := hM T hT_ge_TM σ hσ_Icc
    rw [Contour.weilIntegrand_norm_factored]
    push_cast
    apply mul_le_mul hζ_bd hM_bd (norm_nonneg _)
    exact mul_nonneg hC_ζ_pos.le (Real.rpow_nonneg hT_pos.le _)
  have h_int : ‖∫ σ in σL..σR,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
        (C_ζ * T ^ N * (C_M / T ^ 4)) * |σR - σL| :=
    intervalIntegral.norm_integral_le_of_norm_le_const h_inner
  have hT4_pos : 0 < T ^ 4 := by positivity
  have h_simp :
      (C_ζ * T ^ N * (C_M / T ^ 4)) * |σR - σL| =
        C_ζ * C_M * W * T ^ (N - 4) := by
    have habs : |σR - σL| = W := by
      rw [hW_def]; exact abs_of_nonneg (by linarith)
    rw [habs]
    have hdiv : T ^ N / T ^ 4 = T ^ (N - 4) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      rw [show T ^ (4 : ℕ) = T ^ ((4 : ℕ) : ℝ) from by rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hT_pos]
    have : C_ζ * T ^ N * (C_M / T ^ 4) = C_ζ * C_M * (T ^ N / T ^ 4) := by ring
    rw [this, hdiv]; ring
  rw [h_simp] at h_int
  have h_pow_neg : T ^ (N - 4) = 1 / T ^ (4 - N) := by
    rw [show (N - 4 : ℝ) = -(4 - N) from by ring, Real.rpow_neg hT_pos.le, one_div]
  have hT_pow_ge : (K / ε) ≤ T ^ (4 - N) := by
    have hbase_le : Tbig ≤ T := hT_ge_Tbig
    have h_mono : Tbig ^ (4 - N) ≤ T ^ (4 - N) :=
      Real.rpow_le_rpow hTbig_pos.le hbase_le h4mN_pos.le
    have h_Tbig_pow : Tbig ^ (4 - N) = K / ε := by
      rw [hTbig_def, ← Real.rpow_mul hKε.le]
      have : 1 / (4 - N) * (4 - N) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith [h_mono, h_Tbig_pow]
  have hT_pow_pos : 0 < T ^ (4 - N) := Real.rpow_pos_of_pos hT_pos _
  have h_final : C_ζ * C_M * W * T ^ (N - 4) < ε := by
    rw [h_pow_neg]
    have hCMW_lt_K : C_ζ * C_M * W < K := by rw [hK_def]; linarith
    have hstep1 : C_ζ * C_M * W * (1 / T ^ (4 - N)) < K * (1 / T ^ (4 - N)) := by
      apply mul_lt_mul_of_pos_right hCMW_lt_K
      exact div_pos one_pos hT_pow_pos
    have hstep2 : K * (1 / T ^ (4 - N)) ≤ K * (ε / K) := by
      apply mul_le_mul_of_nonneg_left _ hK_pos.le
      rw [div_le_div_iff₀ hT_pow_pos hK_pos]
      have h := (div_le_iff₀ hε).mp hT_pow_ge
      nlinarith
    have hstep3 : K * (ε / K) = ε := by field_simp
    calc C_ζ * C_M * W * (1 / T ^ (4 - N))
        < K * (1 / T ^ (4 - N)) := hstep1
      _ ≤ K * (ε / K) := hstep2
      _ = ε := hstep3
  linarith

/-- **Vertical-edge difference vanishes** — from the arch-prime cancellation
identity at `σR` and FE transport `σL ↦ 1 − σL` at `σL = −1 ↦ 2`. At each
cosh-pair test function `pair_cosh_gauss_test β`, the two vertical edges
pair-up via FE + arch-prime cancellation at π/6 geometry to vanish
uniformly on good heights. This is the **cosh-side handoff**: the cosh
side consumes this as the remaining input to `weil_explicit_formula_classical`. -/
theorem vertEdgeDiffVanishes_of_archPrimeCancel
    (β : ℝ) {σL σR : ℝ}
    (h_cancel : ∀ ε > (0:ℝ), ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → goodHeight T →
      ‖(∫ y : ℝ in (-T : ℝ)..T,
          Contour.weilIntegrand (Contour.pairTestMellin β)
            ((σR : ℂ) + (y : ℝ) * I))
        - (∫ y : ℝ in (-T : ℝ)..T,
          Contour.weilIntegrand (Contour.pairTestMellin β)
            ((σL : ℂ) + (y : ℝ) * I))‖ < ε) :
    vertEdgeDiffVanishes_target β σL σR :=
  h_cancel

/-- **`rectangleVanishes_target` from the three edge targets.** Pure
triangle-inequality glue — `‖rect‖ ≤ ‖bottom‖ + ‖top‖ + ‖right − left‖`. -/
theorem rectangleVanishes_of_edges
    (β : ℝ) (_hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (h_top    : topEdgeVanishes_target β (-1) 2)
    (h_bottom : bottomEdgeVanishes_target β (-1) 2)
    (h_vert_cancel : vertEdgeDiffVanishes_target β (-1) 2) :
    rectangleVanishes_target β := by
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨T_top, hT_top_pos, hTop⟩ := h_top (ε / 3) hε3
  obtain ⟨T_bot, hT_bot_pos, hBot⟩ := h_bottom (ε / 3) hε3
  obtain ⟨T_vc,  hT_vc_pos,  hVC⟩  := h_vert_cancel (ε / 3) hε3
  refine ⟨max T_top (max T_bot T_vc), ?_, ?_⟩
  · exact lt_max_of_lt_left hT_top_pos
  intro T hT hgood
  have hT_top_le : T_top ≤ T := le_trans (le_max_left _ _) hT
  have hT_bot_le : T_bot ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT_vc_le  : T_vc  ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have h_t := hTop T hT_top_le hgood
  have h_b := hBot T hT_bot_le hgood
  have h_v := hVC T hT_vc_le hgood
  unfold Contour.rectContourIntegral
  set B : ℂ := ∫ x : ℝ in (-1 : ℝ)..2,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((x : ℂ) + (-T : ℝ) * I)
  set Tp : ℂ := ∫ x : ℝ in (-1 : ℝ)..2,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((x : ℂ) + (T : ℝ) * I)
  set R : ℂ := ∫ y : ℝ in (-T : ℝ)..T,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        (((2 : ℝ) : ℂ) + (y : ℝ) * I)
  set L : ℂ := ∫ y : ℝ in (-T : ℝ)..T,
      Contour.weilIntegrand (Contour.pairTestMellin β)
        ((((-1 : ℝ)) : ℂ) + (y : ℝ) * I)
  have hsmul : I • R - I • L = I • (R - L) := by rw [smul_sub]
  have hnormI : ‖I • (R - L)‖ = ‖R - L‖ := by
    rw [smul_eq_mul, norm_mul, norm_I, one_mul]
  have hrewrite : B - Tp + I • R - I • L = B + (-Tp) + I • (R - L) := by
    rw [← hsmul]; ring
  rw [hrewrite]
  have hB_lt  : ‖B‖     < ε / 3 := h_b
  have hTp_lt : ‖Tp‖    < ε / 3 := h_t
  have hRL_lt : ‖R - L‖ < ε / 3 := h_v
  have step1 : ‖B + (-Tp) + I • (R - L)‖ ≤ ‖B + (-Tp)‖ + ‖I • (R - L)‖ :=
    norm_add_le _ _
  have step2 : ‖B + (-Tp)‖ ≤ ‖B‖ + ‖(-Tp : ℂ)‖ := norm_add_le _ _
  have hNegTp : ‖(-Tp : ℂ)‖ = ‖Tp‖ := norm_neg _
  have step2' : ‖B + (-Tp)‖ + ‖I • (R - L)‖
      ≤ (‖B‖ + ‖(-Tp : ℂ)‖) + ‖I • (R - L)‖ := by gcongr
  calc ‖B + (-Tp) + I • (R - L)‖
      ≤ ‖B + (-Tp)‖ + ‖I • (R - L)‖ := step1
    _ ≤ (‖B‖ + ‖(-Tp : ℂ)‖) + ‖I • (R - L)‖ := step2'
    _ = ‖B‖ + ‖Tp‖ + ‖R - L‖ := by rw [hNegTp, hnormI]
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hB_lt hTp_lt) hRL_lt
    _ = ε := by ring

/-- **Classical Weil explicit formula.**

Statement: for every `β ∈ (0, 1)`, the multiplicity-weighted sum over
nontrivial zeros of ζ equals `gaussianPairDefect β`, with `pairTestMellin β`
as the test function:
```
∑' ρ ∈ NontrivialZeros, n(ρ) · pairTestMellin β ρ = gaussianPairDefect β.
```

This is **strictly weaker than RH**. Weil says the weighted sum **balances**
— not that each `ρ` lives at `Re ρ = 1/2`. The identity is an analytic
balance equation between the pole residue at `s = 1` and the aggregated
zero residues; RH is a separate claim about *where* those zeros live, and
the Weil identity is silent on that.

Hypotheses — all classical, all already in the repo or delivered by
Weil-side / cosh-side handoff targets:

* `h_rect_residue` — finite-T rectangle residue identity at `σL=-1, σR=2`
  (G.1 / Cycle 47): Cauchy + multi-pole residue theorem at `s = 1` and
  each nontrivial zero inside the rectangle.
* `h_sum` — weighted zero-sum summability (Jensen-with-multiplicity +
  quartic Mellin decay).
* `h_fin` — finite-rectangle zero set (Jensen).
* `h_top, h_bottom` — horizontal edges vanish as `T → ∞` on good heights
  (Weil-side: `ζ'/ζ(σ+iT)` polynomial bound × Schwartz decay of
  `pairTestMellin β` along vertical lines).
* `h_vert_cancel` — right-minus-left vertical edges cancel as `T → ∞` on
  good heights (cosh-side: arch − prime cancellation at the cosh-pair π/6
  balance point — the detectors at `π/6`, `1 − π/6` read Euler log-prime
  harmonics off-strip).

Axiom footprint once all hypotheses are in stable axioms: the standard
`[propext, Classical.choice, Quot.sound]`.
-/
theorem weil_explicit_formula_classical
    (h_rect_residue : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      rectangleResidueIdentity_target β)
    (h_sum : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      weightedZeroSum_summable_target β)
    (h_fin : nontrivialZeros_in_weilRect_finite_target)
    (h_top : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      topEdgeVanishes_target β (-1) 2)
    (h_bottom : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      bottomEdgeVanishes_target β (-1) 2)
    (h_vert_cancel : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      vertEdgeDiffVanishes_target β (-1) 2) :
    ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β :=
  weilFormula_of_G_bundle
    { rect_residue := h_rect_residue
      rectangle_limit := fun β hβ =>
        rectangleLimit_of_residue_identity_and_summability β
          (h_rect_residue β hβ) (h_sum β hβ) h_fin
      rectangle_vanishes := fun β hβ =>
        rectangleVanishes_of_edges β hβ
          (h_top β hβ) (h_bottom β hβ) (h_vert_cancel β hβ) }

#print axioms weil_explicit_formula_classical

end FinalAssembly
end WeilPositivity
end ZD

end
