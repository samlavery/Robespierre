import Mathlib
import RequestProject.RBetaIdentity
import RequestProject.ArchKernelRectCauchy
import RequestProject.ArchKernelRectCauchyTransport
import RequestProject.FArchKernelHorizontalDecay
import RequestProject.WeilContour

/-!
# Proof of `rectCauchyIdentity_R_form_holds`

Takes the proved finite-T rectangle Cauchy identity
`ZD.ArchKernelRectCauchy.F_rectContourIntegral_value β hT`
(valid for all `T > 0`) and passes to the limit `T → ∞`:

* Top edge → 0: `F_horizontal_edge_tendsto_zero β`.
* Bottom edge → 0: derived from `F_horizontal_edge_tendsto_zero_neg β` at `atBot`.
* Right edge → `∫_ℝ archIntegrand β 2`: via
  `intervalIntegral_tendsto_integral` + `archIntegrand_at_two_integrable` +
  `rectContour_F_right_edge_eq_archIntegrand`.
* Left edge → `∫_ℝ archIntegrand β (−1)`: analogous.
* Residues: `pairTestMellin_at_zero_eq_R_beta` and `pairTestMellin_at_one`.
-/

open Complex MeasureTheory Set Real Filter

noncomputable section

namespace ZD
namespace RBetaIdentity

open ZD.WeilPositivity.Contour
open ZD.ArchKernelRectCauchy
open ZD.ArchKernelRectCauchyTransport
open ZD.ArchKernelRectShift
open ZD.PairComboResidueAtZero

/-! ## Auxiliary limit statements -/

/-- Bottom-edge integral `∫ F(x − iT) dx` tends to `0` as `T → +∞`. -/
private theorem F_bottom_edge_tendsto_zero (β : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ in (-1 : ℝ)..2,
          pairTestMellin_archKernel_product β ((x : ℂ) + (-T : ℝ) * I))
      Filter.atTop (nhds 0) := by
  have h := F_horizontal_edge_tendsto_zero_neg β
  rw [show Filter.atBot (α := ℝ) = Filter.map Neg.neg Filter.atTop from
    Filter.map_neg_atTop.symm] at h
  rw [Filter.tendsto_map'_iff] at h
  simp only [Function.comp_def] at h
  convert h using 2

/-- Right-edge truncated integral converges to the whole-line integral of
`archIntegrand β 2`. -/
private theorem archIntegrand_right_tendsto (β : ℝ) :
    Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, archIntegrand β 2 y)
      Filter.atTop (nhds (∫ y : ℝ, archIntegrand β 2 y)) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (archIntegrand_at_two_integrable β)
    Filter.tendsto_neg_atTop_atBot
    Filter.tendsto_id

/-- Left-edge truncated integral converges to the whole-line integral of
`archIntegrand β (−1)`. -/
private theorem archIntegrand_left_tendsto (β : ℝ) :
    Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, archIntegrand β (-1) y)
      Filter.atTop (nhds (∫ y : ℝ, archIntegrand β (-1) y)) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (archIntegrand_at_neg_one_integrable β)
    Filter.tendsto_neg_atTop_atBot
    Filter.tendsto_id

/-! ## Main theorem -/

/-- **Unconditional `R(β)`-form of the rectangle Cauchy identity.** -/
theorem rectCauchyIdentity_R_form_holds (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    ZD.RBetaIdentity.rectCauchyIdentity_R_form β := by
  unfold rectCauchyIdentity_R_form
  -- Abbreviate whole-line integrals.
  set P : ℂ := ∫ t : ℝ, archIntegrand β 2 t with hP_def
  set Q : ℂ := ∫ y : ℝ, archIntegrand β (-1) y with hQ_def
  -- Substitute M(1) = gaussianPairDefect β; R_beta β already appears via def.
  rw [ZD.WeilPositivity.Contour.pairTestMellin_at_one]
  -- Goal: P - Q = 2π · (gaussianPairDefect β - R_beta β).
  set RHS : ℂ := (2 * ((Real.pi : ℝ) : ℂ)) *
      (((gaussianPairDefect β : ℝ) : ℂ) - ((R_beta β : ℝ) : ℂ)) with hRHS_def
  change P - Q = RHS
  -- Prove by contradiction.
  by_contra hne
  have h_pos : 0 < ‖(P - Q) - RHS‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set ε : ℝ := ‖(P - Q) - RHS‖ / 4 with hε_def
  have hε_pos : 0 < ε := by positivity
  -- (1) Top edge → 0.
  have h_top_ev :=
    (F_horizontal_edge_tendsto_zero β).eventually (Metric.ball_mem_nhds (0 : ℂ) hε_pos)
  rw [Filter.eventually_atTop] at h_top_ev
  obtain ⟨T₁, hT₁⟩ := h_top_ev
  -- (2) Bottom edge → 0.
  have h_bot_ev :=
    (F_bottom_edge_tendsto_zero β).eventually (Metric.ball_mem_nhds (0 : ℂ) hε_pos)
  rw [Filter.eventually_atTop] at h_bot_ev
  obtain ⟨T₂, hT₂⟩ := h_bot_ev
  -- (3) Right edge → P.
  have h_right_ev :=
    (archIntegrand_right_tendsto β).eventually (Metric.ball_mem_nhds P hε_pos)
  rw [Filter.eventually_atTop] at h_right_ev
  obtain ⟨T₃, hT₃⟩ := h_right_ev
  -- (4) Left edge → Q.
  have h_left_ev :=
    (archIntegrand_left_tendsto β).eventually (Metric.ball_mem_nhds Q hε_pos)
  rw [Filter.eventually_atTop] at h_left_ev
  obtain ⟨T₄, hT₄⟩ := h_left_ev
  -- Pick T ≥ max(1, T₁, T₂, T₃, T₄), in particular T > 0.
  set T : ℝ := max 1 (max T₁ (max T₂ (max T₃ T₄))) with hT_def
  have hT_pos : (0 : ℝ) < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT_ge1 : T₁ ≤ T :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hT_ge2 : T₂ ≤ T := by simp [T]
  have hT_ge3 : T₃ ≤ T := by simp [T]
  have hT_ge4 : T₄ ≤ T := by simp [T]
  -- Finite-T edge integrals.
  set right_T : ℂ := ∫ y : ℝ in (-T)..T, archIntegrand β 2 y
  set left_T  : ℂ := ∫ y : ℝ in (-T)..T, archIntegrand β (-1) y
  set top_T   : ℂ := ∫ x : ℝ in (-1:ℝ)..2,
      pairTestMellin_archKernel_product β ((x : ℂ) + (T : ℝ) * I)
  set bot_T   : ℂ := ∫ x : ℝ in (-1:ℝ)..2,
      pairTestMellin_archKernel_product β ((x : ℂ) + (-T : ℝ) * I)
  -- The finite-T identity (from F_rectContourIntegral_value + edge identification).
  have h_finiteT : bot_T - top_T + I • right_T - I • left_T =
      (2 : ℂ) * ((Real.pi : ℝ) : ℂ) * I *
        ((-pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ)) := by
    have h_rect := F_rectContourIntegral_value β hT_pos
    -- h_rect: rectContourIntegral (-1) 2 T F = 2πI·(-M(0) + gpd β)
    -- Unfold and use set-equality for the four edge integrals.
    unfold rectContourIntegral at h_rect
    -- Rewrite right edge using archIntegrand identification.
    have h_right_eq : ∫ y : ℝ in (-T)..T,
        pairTestMellin_archKernel_product β (↑(2:ℝ) + ↑y * I) =
        right_T := by
      rw [show (↑(2:ℝ) : ℂ) = (2:ℂ) from by norm_cast]
      exact (rectContour_F_right_edge_eq_archIntegrand β T).symm
    -- Rewrite left edge.
    have h_left_eq : ∫ y : ℝ in (-T)..T,
        pairTestMellin_archKernel_product β (↑(-1:ℝ) + ↑y * I) =
        left_T := by
      rw [show (↑(-1:ℝ) : ℂ) = (-1:ℂ) from by norm_cast]
      exact rectContour_F_left_edge_eq_archIntegrand β T
    rw [h_right_eq, h_left_eq] at h_rect
    exact h_rect
  -- Rewrite RHS of h_finiteT using M(0) = R_beta β.
  rw [pairTestMellin_at_zero_eq_R_beta] at h_finiteT
  have h_rhs_factor : (2 : ℂ) * ((Real.pi : ℝ) : ℂ) * I *
      ((-((R_beta β : ℝ) : ℂ)) + ((gaussianPairDefect β : ℝ) : ℂ)) = I * RHS := by
    rw [hRHS_def]; ring
  rw [h_rhs_factor] at h_finiteT
  -- Algebraic key: (P - Q) - RHS = (P - right_T) - (Q - left_T) - I*(top_T - bot_T).
  have h_I_sq : Complex.I ^ 2 = -1 := Complex.I_sq
  have h_key : (P - Q) - RHS = (P - right_T) - (Q - left_T) - I * (top_T - bot_T) := by
    simp only [smul_eq_mul] at h_finiteT
    -- h_finiteT: bot_T - top_T + I*right_T - I*left_T = I*RHS
    have h1 : I * (right_T - left_T) = I * RHS + (top_T - bot_T) := by
      linear_combination h_finiteT
    -- Solve for right_T - left_T by multiplying by -I (= I⁻¹).
    have h_rl : right_T - left_T = RHS - I * (top_T - bot_T) := by
      calc right_T - left_T
          = 1 * (right_T - left_T) := (one_mul _).symm
        _ = (I * -I) * (right_T - left_T) := by
            congr 1; rw [show I * -I = -(I ^ 2) by ring, h_I_sq]; ring
        _ = -I * (I * (right_T - left_T)) := by ring
        _ = -I * (I * RHS + (top_T - bot_T)) := by rw [h1]
        _ = RHS - I * (top_T - bot_T) := by
            rw [show -I * (I * RHS + (top_T - bot_T)) =
              -(I ^ 2) * RHS - I * (top_T - bot_T) by ring, h_I_sq]; ring
    have : (P - Q) - RHS = (P - right_T) - (Q - left_T) + ((right_T - left_T) - RHS) := by ring
    rw [this, h_rl]; ring
  -- Norm bound.
  have h_norm_bd : ‖(P - Q) - RHS‖ ≤
      ‖P - right_T‖ + ‖Q - left_T‖ + ‖top_T‖ + ‖bot_T‖ := by
    rw [h_key]
    calc ‖(P - right_T) - (Q - left_T) - I * (top_T - bot_T)‖
        ≤ ‖(P - right_T) - (Q - left_T)‖ + ‖I * (top_T - bot_T)‖ := norm_sub_le _ _
      _ ≤ (‖P - right_T‖ + ‖Q - left_T‖) + ‖I‖ * ‖top_T - bot_T‖ :=
          add_le_add (norm_sub_le _ _) (norm_mul_le _ _)
      _ = ‖P - right_T‖ + ‖Q - left_T‖ + ‖top_T - bot_T‖ := by
          rw [Complex.norm_I, one_mul]
      _ ≤ ‖P - right_T‖ + ‖Q - left_T‖ + (‖top_T‖ + ‖bot_T‖) := by
          gcongr; exact norm_sub_le top_T bot_T
      _ = ‖P - right_T‖ + ‖Q - left_T‖ + ‖top_T‖ + ‖bot_T‖ := by ring
  -- Each piece is < ε.
  have h_top : ‖top_T‖ < ε := by
    have h := hT₁ T hT_ge1
    rwa [dist_zero_right] at h
  have h_bot : ‖bot_T‖ < ε := by
    have h := hT₂ T hT_ge2
    rwa [dist_zero_right] at h
  have h_right : ‖P - right_T‖ < ε := by
    have h := hT₃ T hT_ge3
    rwa [dist_comm, dist_eq_norm] at h
  have h_left : ‖Q - left_T‖ < ε := by
    have h := hT₄ T hT_ge4
    rwa [dist_comm, dist_eq_norm] at h
  -- Contradiction: ‖(P-Q)-RHS‖ ≤ 4ε < ‖(P-Q)-RHS‖.
  have h_sum : ‖P - right_T‖ + ‖Q - left_T‖ + ‖top_T‖ + ‖bot_T‖ < 4 * ε := by linarith
  have h_4eps : 4 * ε = ‖(P - Q) - RHS‖ := by rw [hε_def]; ring
  linarith [h_norm_bd]

end RBetaIdentity
end ZD

/-! ## Axiom check -/

#print axioms ZD.RBetaIdentity.rectCauchyIdentity_R_form_holds

end
