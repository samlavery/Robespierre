import Mathlib
import RequestProject.CauchyKPairTestFinal
import RequestProject.CauchyKPairTestRHBridge
import RequestProject.CauchyKPairTestArchAudit
import RequestProject.CauchyKPairTestEngineering
import RequestProject.CauchyKPairTestPlancherel
import RequestProject.WeilLeftEdgePointwiseSplit
import RequestProject.WeilArchPrimeIdentity

/-!
# Track A: K-level engineering identity (Step 26)

Per the user's decision (2026-05-08), switch from pointwise K_2 to the
**Gaussian-integrated K-level identity**.  This file names the K-level
rectangle target and exposes the bridge to the engineering identity via the
unconditional K-level Weil identity.

## Layered structure

1. **K-level Weil identity** (UNCONDITIONAL,
   `rectContourIntegral_K_pairTestMellin_T_limit_unconditional`):
   ```
   ∫ K · weilIntegrand(M) at 2  −  ∫ K · weilIntegrand(M) at -1
     = 2π · (K(1)·M(β,1) − Σ' n(ρ)·K(ρ)·M(β,ρ)).
   ```

2. **K-rectangle target** (live gate):
   ```
   ∫ K · weilIntegrand(M) at 2  −  ∫ K · weilIntegrand(M) at -1
     = 2π · K(1)·M(β,1)    ∀ β ∈ (0,1).
   ```
   Subtracting from the Weil identity gives `Σ' n·K(ρ)·M(β,ρ) = 0`,
   i.e. `K_complex_zeroSum_vanishes`.

3. **RH endpoint**: `critical_line_of_K_complex_zeroSum_vanishes`
   (proved conditional on engineering + uniqueness) closes RH.

## Track A target

Discharge `K_rectangle_eq_residue_at_one_target` for every `β ∈ (0,1)`.
This is **RH-strength** at the K-complex level.

Axiom footprint target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.OfflineDetectorEndpoint

/-! ## Step 26: K-level rectangle target -/

/-- **K-rectangle target**: the LHS of the K-level Weil identity equals
`2π · K(1) · M(β, 1)`. -/
def K_rectangle_eq_residue_at_one_target (β : ℝ) : Prop :=
  (∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
    (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
  2 * ((Real.pi : ℝ) : ℂ) *
    (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1)

/-- **Bridge: K-rectangle target ⟹ K-complex engineering**.

The K-level Weil identity says `LHS = 2π · (K(1)·M − Σ' n·K(ρ)·M(β,ρ))`.
The rectangle target says `LHS = 2π · K(1)·M`.  Subtracting and dividing by
`2π` gives `Σ' n·K(ρ)·M(β,ρ) = 0`. -/
theorem K_complex_zeroSum_vanishes_of_K_rectangle_target
    (h : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 → K_rectangle_eq_residue_at_one_target β) :
    K_complex_zeroSum_vanishes := by
  intro β hβ_pos hβ_lt
  have hβ : β ∈ Set.Ioo (0:ℝ) 1 := ⟨hβ_pos, hβ_lt⟩
  have h_weil := rectContourIntegral_K_pairTestMellin_T_limit_unconditional β hβ
  have h_rect_raw := h β hβ
  have h_rect : (∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      2 * ((Real.pi : ℝ) : ℂ) *
        (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1) := h_rect_raw
  -- h_weil and h_rect both give expressions for the same LHS; equate the RHSs.
  have h_combined :
      2 * ((Real.pi : ℝ) : ℂ) *
        (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1 -
          ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            ((nMult ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
              Contour.pairTestMellin β ρ.val) =
      2 * ((Real.pi : ℝ) : ℂ) *
        (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1) := by
    linear_combination h_rect - h_weil
  have h_2pi_ne : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    simp [this]
  have h_paren_eq :
      (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((nMult ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
            Contour.pairTestMellin β ρ.val) =
      (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1) :=
    mul_left_cancel₀ h_2pi_ne h_combined
  -- The bracket equality forces the residue sum (with `nMult`) to vanish.
  have h_nMult_sum_zero :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        ((nMult ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
          Contour.pairTestMellin β ρ.val) = 0 := by
    linear_combination -h_paren_eq
  -- `K_complex_zeroSum_vanishes` uses `Classical.choose` instead of `nMult`.
  -- Convert: at each `ρ ∈ NontrivialZeros`, `nMult ρ = Classical.choose ...`.
  refine (tsum_congr (fun ρ => ?_)).trans h_nMult_sum_zero
  have hρ_NTZ : ρ.val ∈ NontrivialZeros := ρ.property
  have h_nMult_eq : nMult ρ.val =
      Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) :=
    nMult_at_nontrivialZero hρ_NTZ
  rw [h_nMult_eq]

#print axioms K_complex_zeroSum_vanishes_of_K_rectangle_target

/-! ## Step 27: K-level four-bucket framework via Gaussian integration

Per user directive (2026-05-08): build the K-level four-bucket structure
by Gaussian-integrating the existing K_2 buckets (NO arch rebuild).

```
KBucket(β) := 2π · ∫_{(0,∞)} e^{-2t²} · K2Bucket(t, β) dt.
```

The integration domain `Ioi 0` matches the project's
`K_zeroSum_eq_t_integral_inner_sum` normalization:
```
Σ' n·K(ρ)·M(β,ρ) = 2π · ∫_{Ioi 0} (K_2 inner sum) · e^{-2t²} dt
```
By even-symmetry of `K_2(s, t)` in `t`, this equals `π · ∫_ℝ ...`.

The K-level four buckets correspond to the K_2-arch four buckets from
`CauchyKPairTestArchAudit.lean` (Step 19). -/

open ZD.WeilPositivity.OfflineDetectorPlancherel

/-- **K-level constant carrier bucket**: Gaussian integral of the K_2-level
constant carrier. -/
noncomputable def K_const_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β

/-- **K-level rational correction bucket**: Gaussian integral of the
K_2-level rational correction. -/
noncomputable def K_rational_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β

/-- **K-level left pole tower bucket**: Gaussian integral of the K_2-level
left pole tower. -/
noncomputable def K_leftTower_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      (∑' k : ℕ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β)

/-- **K-level right pole tower bucket**: Gaussian integral of the K_2-level
right pole tower. -/
noncomputable def K_rightTower_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      (∑' k : ℕ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β)

/-- **K-level prime/reflected-prime difference bucket**: Gaussian integral
of the K_2-level prime/reflected-prime difference (the right-edge minus
left-edge reflected prime contribution). -/
noncomputable def K_primeReflectedDifference_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference t β

/-- **K-level arch bucket**: Gaussian integral of the K_2-level arch integral
`K_2_arch t β`.  By the K_2 4-bucket decomposition, this equals
`K_const + K_rational + K_left + K_right` modulo Fubini. -/
noncomputable def K_arch_bucket (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
    Complex.exp (-2 * (t : ℂ)^2) *
      ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β

/-! ## Step 27.1: Structural decompositions (Fubini-conditional)

The structural identities at K level mirror the K_2-level ones:
- K-arch bucket = sum of 4 K-buckets (K-arch four-bucket decomposition).
- K-rectangle LHS = K-prime/reflected-difference bucket − K-arch bucket.

Both follow from the K_2-level structural identities by Gaussian integration
(Fubini swap of `t` and `y` integrations).  The Fubini swap is a separate
technical obligation.

Stated as Props for downstream discharge. -/

/-- **K-arch four-bucket decomposition** target: `K_arch = K_const + K_rat + K_left + K_right`.
Follows from `shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form` by
Gaussian integration in `t` (Fubini swap with the y-integration inside K_2_arch). -/
def K_arch_four_bucket_target (β : ℝ) : Prop :=
  K_arch_bucket β =
    K_const_bucket β + K_rational_bucket β +
    K_leftTower_bucket β + K_rightTower_bucket β

/-- **K-rectangle LHS as K-bucket difference** target: K-rectangle LHS
equals `K_primeReflectedDifference_bucket − K_arch_bucket`.
Follows from `K_2_prime_reflected_difference_eq` and Fubini. -/
def K_rectangle_LHS_eq_pRD_minus_arch_target (β : ℝ) : Prop :=
  ((∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
    (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
      weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
  K_primeReflectedDifference_bucket β - K_arch_bucket β

/-! ## Step 27.2: Final K-level four-bucket identity

The substantive K-level identity (live RH-strength gate):
```
K_primeReflectedDifference_bucket β − (K_const + K_rat + K_left + K_right) = 2π · K(1) · M(β, 1).
```

Equivalent (via the structural theorems) to `K_rectangle_eq_residue_at_one_target β`. -/

/-- **K-level integrated four-bucket identity** (the live RH-strength gate). -/
def K_integrated_four_bucket_identity (β : ℝ) : Prop :=
  K_primeReflectedDifference_bucket β -
    (K_const_bucket β + K_rational_bucket β +
      K_leftTower_bucket β + K_rightTower_bucket β) =
  2 * ((Real.pi : ℝ) : ℂ) *
    (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1)

/-- **Bridge: K-integrated four-bucket identity ⟹ K-rectangle target**
(combined with the two structural theorems). -/
theorem K_rectangle_eq_residue_at_one_target_of_four_bucket
    (β : ℝ)
    (h_arch_decomp : K_arch_four_bucket_target β)
    (h_LHS_decomp : K_rectangle_LHS_eq_pRD_minus_arch_target β)
    (h_identity : K_integrated_four_bucket_identity β) :
    K_rectangle_eq_residue_at_one_target β := by
  unfold K_rectangle_eq_residue_at_one_target
  unfold K_rectangle_LHS_eq_pRD_minus_arch_target at h_LHS_decomp
  unfold K_arch_four_bucket_target at h_arch_decomp
  unfold K_integrated_four_bucket_identity at h_identity
  rw [h_LHS_decomp]
  -- Goal: K_pRD_bucket - K_arch_bucket = 2π · K(1) · M(β, 1).
  rw [h_arch_decomp]
  -- Goal: K_pRD_bucket - (K_const + K_rat + K_left + K_right) = 2π · K(1) · M(β, 1).
  exact h_identity

#print axioms K_rectangle_eq_residue_at_one_target_of_four_bucket

/-! ## Step 27.3: Status

The K-level live gate is now decomposed into:
1. **Two structural Fubini obligations** (`K_arch_four_bucket_target`,
   `K_rectangle_LHS_eq_pRD_minus_arch_target`) — mechanical, follow from
   K_2 4-bucket + Gaussian-integration Fubini.
2. **One substantive analytic identity** (`K_integrated_four_bucket_identity`)
   — the live RH-strength gate.

The substantive K-level identity:
```
K_primeReflectedDifference_bucket β
  − (K_const_bucket β + K_rational_bucket β +
     K_leftTower_bucket β + K_rightTower_bucket β)
= 2π · K(1) · M(β, 1).
```

This is where the **K-level cancellation** must close (possibly succeeding
where pointwise K_2 fails, due to Gaussian averaging).  No further structural
reduction of this identity is forced; the live work is the identity itself. -/

/-! ## Step 27.4: Structural Fubini theorems

The two structural decompositions are now discharged with explicit
integrability hypotheses (mechanical Fubini-style splits, no analytic
content beyond the K_2-level structural identities).
-/

/-- **Theorem 1: K-arch four-bucket decomposition.** Mechanical split of
the K-arch bucket into the four K-level buckets via the K_2-level
4-bucket identity (`shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form`)
and pointwise Gaussian integration.  Requires integrability of each
bucket's integrand on `Ioi 0` (a Fubini sub-obligation; in the project
each bucket is dominated by a Gaussian-decaying tail).

Note: the four `Integrable*` hypotheses encode the per-bucket
integrability needed by `integral_add`. -/
theorem K_arch_four_bucket_target_holds (β : ℝ)
    (h_int_const : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β)
        (Set.Ioi (0:ℝ)))
    (h_int_rat : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β)
        (Set.Ioi (0:ℝ)))
    (h_int_left : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β))
        (Set.Ioi (0:ℝ)))
    (h_int_right : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β))
        (Set.Ioi (0:ℝ))) :
    K_arch_four_bucket_target β := by
  unfold K_arch_four_bucket_target
  unfold K_arch_bucket K_const_bucket K_rational_bucket
    K_leftTower_bucket K_rightTower_bucket
  -- Goal: 2π · ∫ e^{-2t²} · K_2_arch = 2π · ∫ e^{-2t²} · CC + 2π · ∫ e^{-2t²} · RC + ...
  -- Strategy: pull out 2π, then split the integral on the LHS into 4 via integral_add
  -- after rewriting K_2_arch = CC + RC + LeftSum + RightSum pointwise.
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β =
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β +
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β +
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β) +
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β) := by
    intro t _
    rw [ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch_eq_5alpha_closed_form,
        ZD.WeilPositivity.OfflineDetectorPlancherel.shiftedArchClosedForm_5alpha_sum_eq_4bucket_closed_form]
    ring
  -- Replace LHS integrand using pointwise equality.
  rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
  -- Now split the integral via integral_add three times.
  -- Step A: ∫ (CC + RC + Left) + Right = ∫ (CC + RC + Left) + ∫ Right.
  have h_int_CC_RC : IntegrableOn (fun t : ℝ =>
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β +
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β)
      (Set.Ioi (0:ℝ)) :=
    h_int_const.add h_int_rat
  have h_int_CC_RC_L : IntegrableOn (fun t : ℝ =>
      (Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β +
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β) +
      Complex.exp (-2 * (t : ℂ)^2) *
        (∑' k : ℕ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β))
      (Set.Ioi (0:ℝ)) :=
    h_int_CC_RC.add h_int_left
  rw [show (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β +
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β +
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β) +
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β))
      = (fun t : ℝ =>
        ((Complex.exp (-2 * (t : ℂ)^2) *
            ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β +
          Complex.exp (-2 * (t : ℂ)^2) *
            ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β) +
          Complex.exp (-2 * (t : ℂ)^2) *
            (∑' k : ℕ,
              ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β)) +
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β))
        from rfl]
  rw [integral_add h_int_CC_RC_L h_int_right]
  rw [integral_add h_int_CC_RC h_int_left]
  rw [integral_add h_int_const h_int_rat]
  ring

#print axioms K_arch_four_bucket_target_holds

/-- **Theorem 2: K-rectangle LHS = K-pRD-bucket − K-arch-bucket.**

Combines four ingredients:
1. **Pointwise integrand decomposition on rectangle edges**:
   * Right edge (Re s = 2 > 1): `weilIntegrand pairTestMellin (2+iy) = primeIntegrand β 2 y`
     (`weilIntegrand_eq_primeIntegrand_on_right_edge`, axiom-clean).
   * Left edge (Re s = -1): `weilIntegrand pairTestMellin (-1+iy) =
     archIntegrand β (-1) y + reflectedPrimeIntegrand β (-1) y`
     (`weilIntegrand_pair_left_edge_neg_one_split`, axiom-clean).
2. **Plancherel relation** `K(s) = 2π · ∫_{Ioi 0} K_2(s,t) · e^{-2t²} dt`
   (`gaussianDefectEntireKernel_eq_K2_integral`, axiom-clean).
3. **Fubini swap** of `t` and `y` integrations (encoded as the
   `h_fubini_right`, `h_fubini_left_arch`, `h_fubini_left_refl` hypotheses).
4. **K_2-level prime/reflected-prime difference identity**
   (`K_2_prime_reflected_difference_eq`, axiom-clean).

The Fubini and `integral_add`/`integral_sub` integrability hypotheses
encode the genuine analytic sub-obligations along the way; the rest is
mechanical. -/
theorem K_rectangle_LHS_eq_pRD_minus_arch_target_holds (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    -- Fubini-Plancherel relation on the right edge (Re s = 2):
    -- ∫_y K(2+iy) · primeIntegrand β 2 y dy =
    --   2π · ∫_t e^{-2t²} · (∫_y K_2(2+iy,t) · primeIntegrand β 2 y dy) dt.
    (h_fubini_right :
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.primeIntegrand β 2 y) =
        2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-2 * (t : ℂ)^2) *
            (∫ y : ℝ,
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Contour.primeIntegrand β 2 y))
    -- Fubini-Plancherel relation on the left edge, arch piece:
    -- ∫_y K(-1+iy) · archIntegrand β (-1) y dy =
    --   2π · ∫_t e^{-2t²} · K_2_arch t β dt   (= K_arch_bucket β).
    (h_fubini_left_arch :
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.archIntegrand β (-1) y) =
        2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-2 * (t : ℂ)^2) *
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_arch t β)
    -- Fubini-Plancherel relation on the left edge, reflected-prime piece:
    -- ∫_y K(-1+iy) · reflectedPrime β (-1) y dy =
    --   2π · ∫_t e^{-2t²} · (∫_y K_2(-1+iy,t) · reflectedPrime β (-1) y dy) dt.
    (h_fubini_left_refl :
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.reflectedPrimeIntegrand β (-1) y) =
        2 * ((Real.pi : ℝ) : ℂ) * ∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-2 * (t : ℂ)^2) *
            (∫ y : ℝ,
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
                riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))))
    -- Integrability hypotheses for `integral_add`/`integral_sub` linearity steps.
    (h_int_left_arch : Integrable (fun y : ℝ =>
        gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.archIntegrand β (-1) y))
    (h_int_left_refl : Integrable (fun y : ℝ =>
        gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.reflectedPrimeIntegrand β (-1) y))
    (h_int_inner_right : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
            Contour.primeIntegrand β 2 y) (Set.Ioi (0:ℝ)))
    (h_int_inner_refl : IntegrableOn (fun t : ℝ =>
        Complex.exp (-2 * (t : ℂ)^2) *
          ∫ y : ℝ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
              (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
            ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
              riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
            Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))
        (Set.Ioi (0:ℝ))) :
    K_rectangle_LHS_eq_pRD_minus_arch_target β := by
  unfold K_rectangle_LHS_eq_pRD_minus_arch_target
  unfold K_primeReflectedDifference_bucket K_arch_bucket
  -- Step 1: rewrite weilIntegrand pointwise on each edge.
  have h_right_eq : ∀ y : ℝ,
      Contour.weilIntegrand (Contour.pairTestMellin β)
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) =
        Contour.primeIntegrand β 2 y :=
    fun y => Contour.weilIntegrand_eq_primeIntegrand_on_right_edge β
      (by norm_num : (1:ℝ) < 2) y
  have h_left_eq : ∀ y : ℝ,
      Contour.weilIntegrand (Contour.pairTestMellin β)
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) =
        Contour.archIntegrand β (-1) y +
          Contour.reflectedPrimeIntegrand β (-1) y :=
    fun y => ZD.WeilPositivity.FinalAssembly.weilIntegrand_pair_left_edge_neg_one_split β y
  -- Apply pointwise rewrites under the y-integrals.
  have h_lhs_right : (∫ y : ℝ,
        gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.weilIntegrand (Contour.pairTestMellin β)
            (((2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.primeIntegrand β 2 y := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only
    rw [h_right_eq y]
  have h_lhs_left : (∫ y : ℝ,
        gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.weilIntegrand (Contour.pairTestMellin β)
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          (Contour.archIntegrand β (-1) y +
            Contour.reflectedPrimeIntegrand β (-1) y) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only
    rw [h_left_eq y]
  rw [h_lhs_right, h_lhs_left]
  -- Step 2: split the left-edge integral via linearity over (arch + refl).
  have h_left_split :
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          (Contour.archIntegrand β (-1) y +
            Contour.reflectedPrimeIntegrand β (-1) y)) =
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.archIntegrand β (-1) y) +
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
          Contour.reflectedPrimeIntegrand β (-1) y) := by
    rw [show (fun y : ℝ =>
          gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            (Contour.archIntegrand β (-1) y +
              Contour.reflectedPrimeIntegrand β (-1) y))
        = (fun y : ℝ =>
          gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            Contour.archIntegrand β (-1) y +
          gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
            Contour.reflectedPrimeIntegrand β (-1) y) from by
      funext y; ring]
    exact integral_add h_int_left_arch h_int_left_refl
  rw [h_left_split]
  -- Step 3: apply Fubini-swap hypotheses.
  rw [h_fubini_right, h_fubini_left_arch, h_fubini_left_refl]
  -- Goal now (after Fubini): 2π · ∫_t e^{-2t²} · IR(t) dt
  --   − (2π · ∫_t e^{-2t²} · K_2_arch + 2π · ∫_t e^{-2t²} · IRefl(t) dt)
  -- = 2π · ∫_t e^{-2t²} · primeReflectedDifference - 2π · ∫_t e^{-2t²} · K_2_arch.
  -- Combine to: 2π · (∫_t e^{-2t²} · IR - ∫_t e^{-2t²} · IRefl)
  --           = 2π · ∫_t e^{-2t²} · primeReflectedDifference.
  -- Use integral_sub on the LHS combining IR - IRefl, and pointwise identity
  -- IR(t) - IRefl(t) = primeReflectedDifference t β.
  have h_inner_diff : ∀ t : ℝ,
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
        Contour.primeIntegrand β 2 y) -
      (∫ y : ℝ,
        ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
          (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
        ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
          riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference t β :=
    fun t => ZD.WeilPositivity.OfflineDetectorPlancherel.K_2_prime_reflected_difference_eq t β
  -- Pointwise on Ioi 0:
  -- e^{-2t²} · IR(t) - e^{-2t²} · IRefl(t) = e^{-2t²} · primeReflectedDifference t β.
  have h_pointwise_diff : ∀ t ∈ Set.Ioi (0:ℝ),
      Complex.exp (-2 * (t : ℂ)^2) *
        (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
          Contour.primeIntegrand β 2 y) -
      Complex.exp (-2 * (t : ℂ)^2) *
        (∫ y : ℝ,
          ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
          ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
            riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
          Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) =
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference t β := by
    intro t _
    rw [← mul_sub, h_inner_diff t]
  -- Compute: ∫ e^{-2t²} · IR - ∫ e^{-2t²} · IRefl = ∫ (e^{-2t²}·IR - e^{-2t²}·IRefl)
  --   = ∫ e^{-2t²} · primeReflectedDifference (using h_pointwise_diff).
  have h_diff_integral :
      (∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-2 * (t : ℂ)^2) *
            (∫ y : ℝ,
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((2 : ℝ) : ℂ) + (y : ℂ) * I) t *
              Contour.primeIntegrand β 2 y)) -
      (∫ t in Set.Ioi (0:ℝ),
          Complex.exp (-2 * (t : ℂ)^2) *
            (∫ y : ℝ,
              ZD.WeilPositivity.OfflineDetectorPlancherel.K_2
                (((-1 : ℝ) : ℂ) + (y : ℂ) * I) t *
              ((deriv riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) /
                riemannZeta (1 - (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) *
              Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))) =
      ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference t β := by
    rw [← integral_sub h_int_inner_right h_int_inner_refl]
    exact setIntegral_congr_fun measurableSet_Ioi h_pointwise_diff
  -- Now algebraically manipulate the goal using h_diff_integral.
  linear_combination
    (2 * ((Real.pi : ℝ) : ℂ)) * h_diff_integral

#print axioms K_rectangle_LHS_eq_pRD_minus_arch_target_holds

/-! ## Step 28: K-integrated residual

Per user directive (2026-05-08): expose the residual of the K-integrated
four-bucket identity as a single named expression so its cancellation /
failure mode is visible.

```
KIntegratedResidual β :=
  K_pRD_bucket β
  - (K_const_bucket β + K_rational_bucket β + K_leftTower_bucket β + K_rightTower_bucket β)
  - 2π · K(1) · M(β, 1).
```

`K_integrated_four_bucket_identity β ⟺ KIntegratedResidual β = 0`.

Component-mechanism decomposition (`R_const + R_rat + R_left + R_right`)
deferred until closed-form analysis exposes the natural mechanism split
(which depends on how `2π·K(1)·M(β,1)` partitions across buckets — likely
via `K(1)` closed-form `π√(π/2)·(exp(1/8) − 2·exp(1/32) + 1)` matching the
constant carrier mechanism). -/

/-- **K-integrated residual**: the single named expression measuring failure
of the substantive K-level four-bucket identity. -/
noncomputable def KIntegratedResidual (β : ℝ) : ℂ :=
  K_primeReflectedDifference_bucket β -
    (K_const_bucket β + K_rational_bucket β +
      K_leftTower_bucket β + K_rightTower_bucket β) -
  2 * ((Real.pi : ℝ) : ℂ) *
    gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1

/-- **K-integrated four-bucket identity ⟺ residual = 0**. -/
theorem K_integrated_four_bucket_identity_iff_residual_zero (β : ℝ) :
    K_integrated_four_bucket_identity β ↔ KIntegratedResidual β = 0 := by
  unfold K_integrated_four_bucket_identity KIntegratedResidual
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

#print axioms K_integrated_four_bucket_identity_iff_residual_zero

/-! ## Step 28.1: Track A reduction summary (current state)

Now the K-side reduction is FULLY structured:

```
KIntegratedResidual β = 0  ∀ β ∈ (0,1)              ← THE single substantive gate
+ structural Fubini gates × 2 (10 sub-hypotheses)    ← mechanical, project tooling
+ K-level Weil identity (UNCONDITIONAL)              ← already proved
+ critical_line bridge (conditional on uniqueness)   ← Track B
                                                     ⇓
RiemannHypothesis (at K-complex level)
```

Any failure of `KIntegratedResidual β = 0` is **mathematical** — the
constant/rational/tower mechanisms not cancelling.  The component
decomposition (deferred) will localize the failure if any. -/

/-! ## Step 29: Closed-form expansions for each K-level bucket

For each `K_X_bucket β = 2π · ∫_{Ioi 0} e^{-2t²} · K_2_X_closedForm t β dt`, we
expose a structurally explicit closed form: outer constants pulled out, the
integrand split via linearity into a finite sum (or `Σ' k`-sum, for towers)
of "clean-shape" Gaussian-moment integrals with the `e^{-2t²}` weight kept
as a named atom integrand.

Each `*_closedForm` definition leaves the inner per-piece
`∫ t in Ioi 0, e^{-2t²} · (piece) dt` integrals visible.  The `*_eq_closedForm`
theorem proves the bucket equals its closed form via integral linearity on
the per-piece integrability hypotheses.

Per the request, integrability hypotheses are accepted as theorem
hypotheses; pole-tower theorems further accept a `Σ' k` Fubini-swap
hypothesis.

All identities are purely algebraic on the per-piece integrability /
swap inputs; each closed form is a finite linear combination of
clean-shape Gaussian-moment integrals with `(log π + γ)` and `(2π)`
constants visible. -/

/-- Atomic per-piece Gaussian-moment integrand for the constant carrier.
The `archConstantCarrierClosedForm` is `-(log π + γ) · [P1 + P2 - P3 - P4 + P5]`
where the five pieces are the five products `c_α(t) · 2π · e^{β·t} ·
test_β(e^{γ·t})` from the unfolded constant carrier closed form.
We define the per-piece atomic integrands `K_const_piece_i t β`. -/
noncomputable def K_const_piece1 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) *
        ((Real.exp (2 * t) : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          (Real.exp (-(2 * t))) : ℝ) : ℂ)))

noncomputable def K_const_piece2 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) *
        ((Real.exp (-(2 * t)) : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          (Real.exp (-(-(2 * t)))) : ℝ) : ℂ)))

noncomputable def K_const_piece3 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) *
        ((Real.exp t : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          (Real.exp (-t)) : ℝ) : ℂ)))

noncomputable def K_const_piece4 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ) *
        ((Real.exp (-t) : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          (Real.exp (-(-t))) : ℝ) : ℂ)))

noncomputable def K_const_piece5 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) *
      ((Real.exp 0 : ℝ) : ℂ) *
      ((ZD.WeilPositivity.pair_cosh_gauss_test β
        (Real.exp (-0)) : ℝ) : ℂ))

/-- **Closed form for `K_const_bucket β`**: the outer prefactor
`-(log π + γ) · 2π` is pulled out, and the 5-piece sum becomes a
5-piece linear combination of "clean-shape" Gaussian-moment integrals
on `Ioi 0`. -/
noncomputable def K_const_bucket_closedForm (β : ℝ) : ℂ :=
  -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
    (2 * ((Real.pi : ℝ) : ℂ)) *
    ((∫ t in Set.Ioi (0:ℝ), K_const_piece1 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_const_piece2 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_const_piece3 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_const_piece4 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_const_piece5 t β))

/-- **`K_const_bucket β = K_const_bucket_closedForm β`** under per-piece
integrability hypotheses.  Proof is mechanical: pull the `-(log π + γ)`
constant and the `2π` outside, then split the integral via
`integral_add`/`integral_sub`. -/
theorem K_const_bucket_eq_closedForm (β : ℝ)
    (h1 : IntegrableOn (fun t : ℝ => K_const_piece1 t β) (Set.Ioi (0:ℝ)))
    (h2 : IntegrableOn (fun t : ℝ => K_const_piece2 t β) (Set.Ioi (0:ℝ)))
    (h3 : IntegrableOn (fun t : ℝ => K_const_piece3 t β) (Set.Ioi (0:ℝ)))
    (h4 : IntegrableOn (fun t : ℝ => K_const_piece4 t β) (Set.Ioi (0:ℝ)))
    (h5 : IntegrableOn (fun t : ℝ => K_const_piece5 t β) (Set.Ioi (0:ℝ))) :
    K_const_bucket β = K_const_bucket_closedForm β := by
  unfold K_const_bucket K_const_bucket_closedForm
  -- Pointwise rewrite the integrand using the closed form definition and
  -- distributing the outer Gaussian factor across the 5-piece sum.
  set C : ℂ := -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ))
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm t β =
      C * (K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
            K_const_piece4 t β + K_const_piece5 t β) := by
    intro t _
    unfold ZD.WeilPositivity.OfflineDetectorPlancherel.archConstantCarrierClosedForm
    unfold K_const_piece1 K_const_piece2 K_const_piece3 K_const_piece4 K_const_piece5
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
  -- Now: 2π · ∫ C · (P1+P2-P3-P4+P5) = C · 2π · (∫P1 + ∫P2 - ∫P3 - ∫P4 + ∫P5).
  have hi1 : Integrable (fun t : ℝ => K_const_piece1 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h1
  have hi2 : Integrable (fun t : ℝ => K_const_piece2 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h2
  have hi3 : Integrable (fun t : ℝ => K_const_piece3 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h3
  have hi4 : Integrable (fun t : ℝ => K_const_piece4 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h4
  have hi5 : Integrable (fun t : ℝ => K_const_piece5 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h5
  have e1 : (∫ (t : ℝ) in Set.Ioi 0, C *
        (K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
          K_const_piece4 t β + K_const_piece5 t β)) =
      C * (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
          K_const_piece4 t β + K_const_piece5 t β) :=
    MeasureTheory.integral_const_mul C _
  have e2 : (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
          K_const_piece4 t β + K_const_piece5 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
          K_const_piece4 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece5 t β) :=
    MeasureTheory.integral_add (((hi1.add hi2).sub hi3).sub hi4) hi5
  have e3 : (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β -
          K_const_piece4 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece4 t β) :=
    MeasureTheory.integral_sub ((hi1.add hi2).sub hi3) hi4
  have e4 : (∫ (t : ℝ) in Set.Ioi 0,
        K_const_piece1 t β + K_const_piece2 t β - K_const_piece3 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece1 t β + K_const_piece2 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece3 t β) :=
    MeasureTheory.integral_sub (hi1.add hi2) hi3
  have e5 : (∫ (t : ℝ) in Set.Ioi 0, K_const_piece1 t β + K_const_piece2 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece1 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_const_piece2 t β) :=
    MeasureTheory.integral_add hi1 hi2
  rw [e1, e2, e3, e4, e5]
  ring

#print axioms K_const_bucket_eq_closedForm

/-! ### Priority 2: K-rational bucket closed form -/

/-- Atomic per-piece integrand for the rational correction bucket.  Each
piece is `e^{-2t²} · coeff_α(t) · (-∫ y, e^{iyα}·(1/(-1+iy))·M(β,-1+iy) dy)`. -/
noncomputable def K_rational_piece1 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ((1/2 : ℂ) * Complex.exp ((-(3 * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (2 * t) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))

noncomputable def K_rational_piece2 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ((1/2 : ℂ) * Complex.exp ((3 * t : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (-(2 * t)) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))

noncomputable def K_rational_piece3 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (Complex.exp ((((-(3/2)) * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))

noncomputable def K_rational_piece4 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (Complex.exp ((((3/2) * t) : ℝ) : ℂ) *
      (-∫ y : ℝ, Complex.exp (((y * (-t) : ℝ) : ℂ) * I) *
        (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
        Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I)))

noncomputable def K_rational_piece5 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (-∫ y : ℝ, Complex.exp (((y * (0 : ℝ) : ℝ) : ℂ) * I) *
      (1 / ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)) *
      Contour.pairTestMellin β (((-1 : ℝ) : ℂ) + (y : ℂ) * I))

/-- **Closed form for `K_rational_bucket β`**: outer `2π` constant pulled out,
splitting the rational correction's 5-piece structure into 5 named
clean-shape Gaussian-moment integrals on `Ioi 0`. -/
noncomputable def K_rational_bucket_closedForm (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) *
    ((∫ t in Set.Ioi (0:ℝ), K_rational_piece1 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_rational_piece2 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_rational_piece3 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_rational_piece4 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_rational_piece5 t β))

/-- **`K_rational_bucket β = K_rational_bucket_closedForm β`** under per-piece
integrability hypotheses. -/
theorem K_rational_bucket_eq_closedForm (β : ℝ)
    (h1 : IntegrableOn (fun t : ℝ => K_rational_piece1 t β) (Set.Ioi (0:ℝ)))
    (h2 : IntegrableOn (fun t : ℝ => K_rational_piece2 t β) (Set.Ioi (0:ℝ)))
    (h3 : IntegrableOn (fun t : ℝ => K_rational_piece3 t β) (Set.Ioi (0:ℝ)))
    (h4 : IntegrableOn (fun t : ℝ => K_rational_piece4 t β) (Set.Ioi (0:ℝ)))
    (h5 : IntegrableOn (fun t : ℝ => K_rational_piece5 t β) (Set.Ioi (0:ℝ))) :
    K_rational_bucket β = K_rational_bucket_closedForm β := by
  unfold K_rational_bucket K_rational_bucket_closedForm
  -- Pointwise rewrite: e^{-2t²} · archRationalCorrectionClosedForm =
  --                    P1 + P2 - P3 - P4 + P5.
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm t β =
      K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β -
        K_rational_piece4 t β + K_rational_piece5 t β := by
    intro t _
    unfold ZD.WeilPositivity.OfflineDetectorPlancherel.archRationalCorrectionClosedForm
    unfold K_rational_piece1 K_rational_piece2 K_rational_piece3 K_rational_piece4 K_rational_piece5
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
  -- Linearity: split the integral via integral_add/sub.
  have hi1 : Integrable (fun t : ℝ => K_rational_piece1 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h1
  have hi2 : Integrable (fun t : ℝ => K_rational_piece2 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h2
  have hi3 : Integrable (fun t : ℝ => K_rational_piece3 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h3
  have hi4 : Integrable (fun t : ℝ => K_rational_piece4 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h4
  have hi5 : Integrable (fun t : ℝ => K_rational_piece5 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := h5
  have e2 : (∫ (t : ℝ) in Set.Ioi 0,
        K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β -
          K_rational_piece4 t β + K_rational_piece5 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β -
          K_rational_piece4 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece5 t β) :=
    MeasureTheory.integral_add (((hi1.add hi2).sub hi3).sub hi4) hi5
  have e3 : (∫ (t : ℝ) in Set.Ioi 0,
        K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β -
          K_rational_piece4 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece4 t β) :=
    MeasureTheory.integral_sub ((hi1.add hi2).sub hi3) hi4
  have e4 : (∫ (t : ℝ) in Set.Ioi 0,
        K_rational_piece1 t β + K_rational_piece2 t β - K_rational_piece3 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece1 t β + K_rational_piece2 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece3 t β) :=
    MeasureTheory.integral_sub (hi1.add hi2) hi3
  have e5 : (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece1 t β + K_rational_piece2 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece1 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_rational_piece2 t β) :=
    MeasureTheory.integral_add hi1 hi2
  rw [e2, e3, e4, e5]

#print axioms K_rational_bucket_eq_closedForm

/-! ### Priority 3: K-pRD bucket (prime/reflected difference) closed form -/

/-- pRD piece A1: `e^{-2t²} · π · e^{-t} · Σ' Λ(n)·test_β(n·e^{-2t})`. -/
noncomputable def K_pRD_pieceA1 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((n : ℝ) * Real.exp (-(2*t))) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceA2 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((n : ℝ) * Real.exp (2*t)) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceA3 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((n : ℝ) * Real.exp (-t)) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceA4 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((n : ℝ) * Real.exp t) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceA5 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)))

/-- pRD piece B1: reflected version, divides Λ(n)/n and uses 1/n inside. -/
noncomputable def K_pRD_pieceB1 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((Real.pi : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((1 / (n : ℝ)) * Real.exp (-(2*t))) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceB2 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((Real.pi : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((1 / (n : ℝ)) * Real.exp (2*t)) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceB3 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(t/2)) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((1 / (n : ℝ)) * Real.exp (-t)) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceB4 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (t/2) : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β
          ((1 / (n : ℝ)) * Real.exp t) : ℝ) : ℂ)))

noncomputable def K_pRD_pieceB5 (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    (((2 * Real.pi : ℝ) : ℂ) *
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) *
        ((ZD.WeilPositivity.pair_cosh_gauss_test β (1 / (n : ℝ)) : ℝ) : ℂ)))

/-- **Closed form for `K_primeReflectedDifference_bucket β`**: outer `2π`
constant pulled out; `primeReflectedDifference`'s 10-piece structure
(5 prime + 5 reflected) becomes 10 named clean-shape Gaussian-moment
integrals on `Ioi 0`. -/
noncomputable def K_pRD_bucket_closedForm (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) *
    ((∫ t in Set.Ioi (0:ℝ), K_pRD_pieceA1 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceA2 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceA3 t β) -
     (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceA4 t β) +
     (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceA5 t β) -
     (-(∫ t in Set.Ioi (0:ℝ), K_pRD_pieceB1 t β) -
      (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceB2 t β) +
      (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceB3 t β) +
      (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceB4 t β) -
      (∫ t in Set.Ioi (0:ℝ), K_pRD_pieceB5 t β)))

/-- **`K_primeReflectedDifference_bucket β = K_pRD_bucket_closedForm β`** under
per-piece integrability hypotheses. -/
theorem K_pRD_bucket_eq_closedForm (β : ℝ)
    (hA1 : IntegrableOn (fun t : ℝ => K_pRD_pieceA1 t β) (Set.Ioi (0:ℝ)))
    (hA2 : IntegrableOn (fun t : ℝ => K_pRD_pieceA2 t β) (Set.Ioi (0:ℝ)))
    (hA3 : IntegrableOn (fun t : ℝ => K_pRD_pieceA3 t β) (Set.Ioi (0:ℝ)))
    (hA4 : IntegrableOn (fun t : ℝ => K_pRD_pieceA4 t β) (Set.Ioi (0:ℝ)))
    (hA5 : IntegrableOn (fun t : ℝ => K_pRD_pieceA5 t β) (Set.Ioi (0:ℝ)))
    (hB1 : IntegrableOn (fun t : ℝ => K_pRD_pieceB1 t β) (Set.Ioi (0:ℝ)))
    (hB2 : IntegrableOn (fun t : ℝ => K_pRD_pieceB2 t β) (Set.Ioi (0:ℝ)))
    (hB3 : IntegrableOn (fun t : ℝ => K_pRD_pieceB3 t β) (Set.Ioi (0:ℝ)))
    (hB4 : IntegrableOn (fun t : ℝ => K_pRD_pieceB4 t β) (Set.Ioi (0:ℝ)))
    (hB5 : IntegrableOn (fun t : ℝ => K_pRD_pieceB5 t β) (Set.Ioi (0:ℝ))) :
    K_primeReflectedDifference_bucket β = K_pRD_bucket_closedForm β := by
  unfold K_primeReflectedDifference_bucket K_pRD_bucket_closedForm
  -- Pointwise rewrite using primeReflectedDifference's definition.
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      Complex.exp (-2 * (t : ℂ)^2) *
        ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference t β =
      K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
        K_pRD_pieceA4 t β + K_pRD_pieceA5 t β -
      (-K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
        K_pRD_pieceB4 t β - K_pRD_pieceB5 t β) := by
    intro t _
    unfold ZD.WeilPositivity.OfflineDetectorPlancherel.primeReflectedDifference
    unfold K_pRD_pieceA1 K_pRD_pieceA2 K_pRD_pieceA3 K_pRD_pieceA4 K_pRD_pieceA5
    unfold K_pRD_pieceB1 K_pRD_pieceB2 K_pRD_pieceB3 K_pRD_pieceB4 K_pRD_pieceB5
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
  -- Linearity: split the 10-piece integral into 10 named integrals.
  have hiA1 : Integrable (fun t : ℝ => K_pRD_pieceA1 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hA1
  have hiA2 : Integrable (fun t : ℝ => K_pRD_pieceA2 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hA2
  have hiA3 : Integrable (fun t : ℝ => K_pRD_pieceA3 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hA3
  have hiA4 : Integrable (fun t : ℝ => K_pRD_pieceA4 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hA4
  have hiA5 : Integrable (fun t : ℝ => K_pRD_pieceA5 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hA5
  have hiB1 : Integrable (fun t : ℝ => K_pRD_pieceB1 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hB1
  have hiB2 : Integrable (fun t : ℝ => K_pRD_pieceB2 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hB2
  have hiB3 : Integrable (fun t : ℝ => K_pRD_pieceB3 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hB3
  have hiB4 : Integrable (fun t : ℝ => K_pRD_pieceB4 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hB4
  have hiB5 : Integrable (fun t : ℝ => K_pRD_pieceB5 t β)
      (volume.restrict (Set.Ioi (0:ℝ))) := hB5
  -- Build the integral split via repeated `integral_add`/`integral_sub`.
  -- Goal: ∫_t (P_A1 + P_A2 - P_A3 - P_A4 + P_A5 - (-P_B1 - P_B2 + P_B3 + P_B4 - P_B5))
  --     = (∫P_A1 + ∫P_A2 - ∫P_A3 - ∫P_A4 + ∫P_A5)
  --       - (-∫P_B1 - ∫P_B2 + ∫P_B3 + ∫P_B4 - ∫P_B5).
  have hA12 := hiA1.add hiA2
  have hA123 := hA12.sub hiA3
  have hA1234 := hA123.sub hiA4
  have hA12345 := hA1234.add hiA5
  have hB1' := hiB1.neg
  have hB12' := hB1'.sub hiB2
  have hB123' := hB12'.add hiB3
  have hB1234' := hB123'.add hiB4
  have hB12345' := hB1234'.sub hiB5
  -- Split outermost: ∫(A_part - B_part) = ∫A_part - ∫B_part.
  have e_outer :
      (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
          K_pRD_pieceA4 t β + K_pRD_pieceA5 t β -
        (-K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
          K_pRD_pieceB4 t β - K_pRD_pieceB5 t β)) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
          K_pRD_pieceA4 t β + K_pRD_pieceA5 t β) -
      (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
          K_pRD_pieceB4 t β - K_pRD_pieceB5 t β) :=
    MeasureTheory.integral_sub hA12345 hB12345'
  -- Split A_part as before:
  have eA1 : (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
          K_pRD_pieceA4 t β + K_pRD_pieceA5 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
          K_pRD_pieceA4 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA5 t β) :=
    MeasureTheory.integral_add hA1234 hiA5
  have eA2 : (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β -
          K_pRD_pieceA4 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA4 t β) :=
    MeasureTheory.integral_sub hA123 hiA4
  have eA3 : (∫ (t : ℝ) in Set.Ioi 0,
        K_pRD_pieceA1 t β + K_pRD_pieceA2 t β - K_pRD_pieceA3 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA1 t β + K_pRD_pieceA2 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA3 t β) :=
    MeasureTheory.integral_sub hA12 hiA3
  have eA4 : (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA1 t β + K_pRD_pieceA2 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA1 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceA2 t β) :=
    MeasureTheory.integral_add hiA1 hiA2
  -- Split B_part:
  -- ∫(-B1 - B2 + B3 + B4 - B5)
  --   = ∫(-B1 - B2 + B3 + B4) - ∫B5
  --   = ∫(-B1 - B2 + B3) + ∫B4 - ∫B5
  --   = ∫(-B1 - B2) + ∫B3 + ∫B4 - ∫B5
  --   = (-∫B1) - ∫B2 + ∫B3 + ∫B4 - ∫B5.
  have eB1 : (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
          K_pRD_pieceB4 t β - K_pRD_pieceB5 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
          K_pRD_pieceB4 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceB5 t β) :=
    MeasureTheory.integral_sub hB1234' hiB5
  have eB2 : (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β +
          K_pRD_pieceB4 t β) =
      (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceB4 t β) :=
    MeasureTheory.integral_add hB123' hiB4
  have eB3 : (∫ (t : ℝ) in Set.Ioi 0,
        -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β + K_pRD_pieceB3 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β) +
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceB3 t β) :=
    MeasureTheory.integral_add hB12' hiB3
  have eB4 : (∫ (t : ℝ) in Set.Ioi 0, -K_pRD_pieceB1 t β - K_pRD_pieceB2 t β) =
      (∫ (t : ℝ) in Set.Ioi 0, -K_pRD_pieceB1 t β) -
      (∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceB2 t β) :=
    MeasureTheory.integral_sub hB1' hiB2
  have eB5 : (∫ (t : ℝ) in Set.Ioi 0, -K_pRD_pieceB1 t β) =
      -(∫ (t : ℝ) in Set.Ioi 0, K_pRD_pieceB1 t β) := by
    rw [MeasureTheory.integral_neg]
  rw [e_outer, eA1, eA2, eA3, eA4, eB1, eB2, eB3, eB4, eB5]

#print axioms K_pRD_bucket_eq_closedForm

/-! ### Priority 4: K-leftTower bucket closed form

The pole-tower buckets contain a `Σ' k`-sum inside the t-integral.  The
closed-form expansion swaps the order to `2π · Σ' k · ∫_t e^{-2t²} ·
leftPoleTowerK2Aggregator k t β dt`.

This swap is genuinely analytic (uniform/dominated convergence), accepted
here as a `h_swap` hypothesis (cf. `MeasureTheory.integral_tsum_of_summable_integral_norm`). -/

/-- Per-`k` Gaussian-moment integrand for the left pole tower. -/
noncomputable def K_leftTower_kPiece (k : ℕ) (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β

/-- **Closed form for `K_leftTower_bucket β`**: outer `2π` pulled out and
the t-integral / k-sum order swapped.  The closed form is `2π · Σ' k,
∫_t e^{-2t²} · leftPoleTowerK2Aggregator k t β dt`. -/
noncomputable def K_leftTower_bucket_closedForm (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) *
    (∑' k : ℕ, ∫ t in Set.Ioi (0:ℝ), K_leftTower_kPiece k t β)

/-- **`K_leftTower_bucket β = K_leftTower_bucket_closedForm β`** under the
t-integral / k-sum interchange hypothesis `h_swap`. -/
theorem K_leftTower_bucket_eq_closedForm (β : ℝ)
    (h_swap :
      (∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.leftPoleTowerK2Aggregator k t β)) =
      ∑' k : ℕ, ∫ t in Set.Ioi (0:ℝ), K_leftTower_kPiece k t β) :
    K_leftTower_bucket β = K_leftTower_bucket_closedForm β := by
  unfold K_leftTower_bucket K_leftTower_bucket_closedForm
  rw [h_swap]

#print axioms K_leftTower_bucket_eq_closedForm

/-! ### Priority 5: K-rightTower bucket closed form

Symmetric to the left tower. -/

/-- Per-`k` Gaussian-moment integrand for the right pole tower. -/
noncomputable def K_rightTower_kPiece (k : ℕ) (t β : ℝ) : ℂ :=
  Complex.exp (-2 * (t : ℂ)^2) *
    ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β

/-- **Closed form for `K_rightTower_bucket β`**: outer `2π` pulled out and
the t-integral / k-sum order swapped. -/
noncomputable def K_rightTower_bucket_closedForm (β : ℝ) : ℂ :=
  2 * ((Real.pi : ℝ) : ℂ) *
    (∑' k : ℕ, ∫ t in Set.Ioi (0:ℝ), K_rightTower_kPiece k t β)

/-- **`K_rightTower_bucket β = K_rightTower_bucket_closedForm β`** under the
t-integral / k-sum interchange hypothesis `h_swap`. -/
theorem K_rightTower_bucket_eq_closedForm (β : ℝ)
    (h_swap :
      (∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-2 * (t : ℂ)^2) *
          (∑' k : ℕ,
            ZD.WeilPositivity.OfflineDetectorPlancherel.rightPoleTowerK2Aggregator k t β)) =
      ∑' k : ℕ, ∫ t in Set.Ioi (0:ℝ), K_rightTower_kPiece k t β) :
    K_rightTower_bucket β = K_rightTower_bucket_closedForm β := by
  unfold K_rightTower_bucket K_rightTower_bucket_closedForm
  rw [h_swap]

#print axioms K_rightTower_bucket_eq_closedForm

/-! ## Step 29: Cancellation table — pattern matching, NOT proof search

Per user directive (2026-05-08): build a cancellation table on the 27 named
pieces before attempting algebraic cancellation.  The pRD A/B form has been
confirmed (matching prefactors `+π·e^{-t}, +π·e^{t}, −2π·e^{-t/2},
−2π·e^{t/2}, +2π·1` on each side; A uses `Λ(n)·test_β(n·e^{c·t})`,
B uses `Λ(n)/n·test_β((1/n)·e^{c·t})`).

### Candidate groupings (NOT yet asserted; informal cancellation table)

- **Residue-at-one ↔ const-carrier α=0**: `K_const_piece5` (constant carrier
  with `α = 0`) carries `−(log π + γ)·(2π)²·∫_{Ioi 0} e^{-2t²}·test_β(1) dt`
  — likely matches `2π·K(1)·M(β,1)` modulo a normalization that needs
  inspection.
- **Prime ↔ reflected-prime FE pairing**: `K_pRD_pieceA{i} + K_pRD_pieceB{i}`
  per `i ∈ {1..5}` should combine via the FE pair `n ↔ 1/n`.
- **Rational correction ↔ pole tower endpoint**: `K_rational_piece{i}` may
  cancel a `k=0`-style residue from `K_{left,right}Tower_kPiece`.

These groupings are STRUCTURAL HYPOTHESES.  The actual cancellation must be
verified by direct closed-form analysis, not by guessing. -/

/-- **Candidate: residue at `s = 1`** — a candidate combination that should
match `2π · K(1) · M(β, 1)` in the cancellation analysis. -/
noncomputable def K_residueAtOne_candidate (β : ℝ) : ℂ :=
  -(Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
    ((2 * Real.pi : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) *
      ∫ t in Set.Ioi (0:ℝ), Complex.exp (-2 * (t : ℂ)^2) *
        ((pair_cosh_gauss_test β 1 : ℝ) : ℂ))

/-- **Candidate: trivial-zero tower union** — left + right pole towers
combined. -/
noncomputable def K_trivialZeroTower_candidate (β : ℝ) : ℂ :=
  K_leftTower_bucket β + K_rightTower_bucket β

/-- **Candidate: gamma/arch carrier** — the constant carrier minus its
`α=0` piece (the residue-at-one match). -/
noncomputable def K_gammaArch_candidate (β : ℝ) : ℂ :=
  K_const_bucket β - K_residueAtOne_candidate β

/-! ## Step 29.1: Structural reformulation of the residual

The residual reorganizes into the candidate groupings.  Pure algebra,
no analytic content. -/

/-- **Structural rearrangement** of `KIntegratedResidual` by candidate
groupings. -/
theorem KIntegratedResidual_structural_form (β : ℝ) :
    KIntegratedResidual β =
      (K_primeReflectedDifference_bucket β -
        K_gammaArch_candidate β -
        K_rational_bucket β -
        K_trivialZeroTower_candidate β) -
      (K_residueAtOne_candidate β +
        2 * ((Real.pi : ℝ) : ℂ) *
          gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1) := by
  unfold KIntegratedResidual K_gammaArch_candidate K_trivialZeroTower_candidate
  ring

#print axioms KIntegratedResidual_structural_form

/-! ## Step 29.2: Status — cancellation table in place

The 27 named pieces are now organized into 3 candidate groupings:
1. `K_residueAtOne_candidate` — natural match for `2π·K(1)·M(β,1)`.
2. `K_trivialZeroTower_candidate` — pole towers combined.
3. `K_gammaArch_candidate` — constant carrier minus residue-at-one piece.

The structural form `KIntegratedResidual_structural_form` rewrites the
residual as
```
KIntegratedResidual β =
  (K_pRD_bucket β − K_gammaArch − K_rational_bucket β − K_trivialZeroTower)
  − (K_residueAtOne_candidate + 2π·K(1)·M(β,1)).
```

**Next decision**:
- Inspect `K_residueAtOne_candidate` vs `2π·K(1)·M(β,1)` for normalization match.
- Inspect `K_pRD_bucket β − K_gammaArch − K_rational_bucket β − K_trivialZeroTower`
  for the FE-paired prime/reflected cancellation.

Held back from proving any specific cancellation; structure only. -/

/-! ## Step 30: Residual = `−2π · K-complex zero sum`

After inspecting the closed-form pieces (per Step 29 cancellation table), the
residue-at-one term `2π · K(1) · M(β, 1)` does **NOT** appear in any single
bucket — it sits OUTSIDE the bucket decomposition as the residue at `s = 1`
from the rectangle Cauchy.  No bucket piece is shape-proportional to
`pairTestMellin β 1`.

This means the residual is NOT a finite-cancellation algebraic identity.  By
the unconditional K-level Weil identity:
```
LHS_K_rect = 2π · (K(1)·M(β,1) − Σ' n·K(ρ)·M(β,ρ))
```
combined with the structural Fubini decompositions:
```
LHS_K_rect = K_pRD_bucket − K_arch_bucket
           = K_pRD_bucket − (K_const + K_rat + K_left + K_right)
```
gives:
```
KIntegratedResidual β = LHS_K_rect − 2π·K(1)·M(β,1) = −2π · Σ' n·K(ρ)·M(β,ρ).
```

So `KIntegratedResidual β = −2π · K-complex-zero-sum at β`.

This is the **honest collapse** of Track A: the residual is literally the
K-complex zero sum (up to `−2π`), which is RH-equivalent at K-complex level
via `critical_line_of_K_complex_zeroSum_vanishes`.

The cancellation analysis (candidate groupings, Step 29) was diagnostically
useful but the cancellation is NOT structural — it's the substantive
RH-strength identity. -/

/-- **Residual = `−2π · K-complex zero sum`** (conditional on the two
structural Fubini hypotheses from Step 27).

Combines:
- `K_arch_four_bucket_target` (4-bucket structural identity).
- `K_rectangle_LHS_eq_pRD_minus_arch_target` (rectangle = pRD − arch).
- `rectContourIntegral_K_pairTestMellin_T_limit_unconditional` (K-Weil identity). -/
theorem KIntegratedResidual_eq_neg_2pi_zeroSum
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (h_arch_decomp : K_arch_four_bucket_target β)
    (h_LHS_decomp : K_rectangle_LHS_eq_pRD_minus_arch_target β) :
    KIntegratedResidual β =
      -(2 * ((Real.pi : ℝ) : ℂ)) *
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((nMult ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
            Contour.pairTestMellin β ρ.val := by
  unfold KIntegratedResidual
  unfold K_arch_four_bucket_target at h_arch_decomp
  unfold K_rectangle_LHS_eq_pRD_minus_arch_target at h_LHS_decomp
  have h_weil := rectContourIntegral_K_pairTestMellin_T_limit_unconditional β hβ
  -- h_weil : LHS_rect = 2π·(K(1)·M − Σ').
  -- h_LHS_decomp : LHS_rect = K_pRD − K_arch.
  -- h_arch_decomp : K_arch = K_const + K_rat + K_left + K_right.
  -- Combining: K_pRD − (K_const + K_rat + K_left + K_right) = 2π·(K(1)·M − Σ').
  -- KIntegratedResidual = (above) − 2π·K(1)·M = −2π·Σ'.
  linear_combination h_weil - h_LHS_decomp + h_arch_decomp

#print axioms KIntegratedResidual_eq_neg_2pi_zeroSum

/-! ## Step 30.1: Track A final collapse

The K-side reduction is now COMPLETELY transparent:

```
KIntegratedResidual β  =  −2π · Σ' n·K(ρ)·M(β,ρ)        (modulo Fubini structurals)
                       = −2π · (K-complex zero sum at β).
```

**Three equivalent statements** (all RH-strength at K-complex level):
1. `KIntegratedResidual β = 0    ∀ β ∈ (0,1)`.
2. `K_rectangle_eq_residue_at_one_target β    ∀ β ∈ (0,1)`.
3. `K_complex_zeroSum_vanishes`.

Combined with `critical_line_of_K_complex_zeroSum_vanishes` (proved,
conditional on Track B uniqueness) ⟹ RH at K-complex level.

The cancellation table was diagnostically valuable: it confirmed that
**no closed-form bucket piece contains `pairTestMellin β 1`-shape**, so the
residue at `s=1` does NOT cancel structurally inside the bucket
decomposition.  The K-complex zero sum vanishing IS the RH-strength
substantive content. -/

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
