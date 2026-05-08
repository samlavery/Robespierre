import Mathlib
import RequestProject.CauchyWeilDefectScratch

/-!
# K-twisted Cauchy formula on a rectangle: multi-pole version

Builds on `rectContourIntegral_K_inv_plus_analytic` (single pole) to give the
multi-pole case: for entire `K`, entire remainder `g`, residues `r_i` at
strictly interior poles `p_i`,
  `∮ K(s) · (Σ_i r_i / (s − p_i) + g(s)) ds = 2πi · Σ_i K(p_i) · r_i`.
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour

/-- **K-twisted Cauchy: multi-pole + entire holomorphic remainder.**

Special case where the remainder `g` is entire.  See
`rectContourIntegral_K_multi_inv_plus_diffOn` for the rect-differentiable
generalization. -/
theorem rectContourIntegral_K_multi_inv_plus_analytic
    (K : ℂ → ℂ) (hK : Differentiable ℂ K)
    (σL σR T : ℝ) (hσ : σL < σR) (hT : 0 < T)
    {ι : Type*} [DecidableEq ι] (poles : Finset ι) (p : ι → ℂ) (r : ι → ℂ)
    (hp_re : ∀ i ∈ poles, σL < (p i).re ∧ (p i).re < σR)
    (hp_im : ∀ i ∈ poles, -T < (p i).im ∧ (p i).im < T)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    rectContourIntegral σL σR T
        (fun s => K s * (∑ i ∈ poles, r i / (s - p i) + g s)) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ i ∈ poles, K (p i) * r i := by
  classical
  induction poles using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_add, mul_zero]
    exact rectContourIntegral_eq_zero_of_differentiableOn σL σR T _
      (hK.mul hg).differentiableOn
  | @insert i₀ S hi₀_notmem ih =>
    -- Inductive step: split off i₀.
    have hp_re_i₀ : σL < (p i₀).re ∧ (p i₀).re < σR :=
      hp_re i₀ (Finset.mem_insert_self _ _)
    have hp_im_i₀ : -T < (p i₀).im ∧ (p i₀).im < T :=
      hp_im i₀ (Finset.mem_insert_self _ _)
    have hp_re_S : ∀ j ∈ S, σL < (p j).re ∧ (p j).re < σR :=
      fun j hj => hp_re j (Finset.mem_insert_of_mem hj)
    have hp_im_S : ∀ j ∈ S, -T < (p j).im ∧ (p j).im < T :=
      fun j hj => hp_im j (Finset.mem_insert_of_mem hj)
    -- Pointwise split:
    --   Σ_{insert i₀ S} r/(s - p) + g s = r(i₀)/(s - p(i₀)) + (Σ_S r/(s - p) + g s)
    have h_sum_split : ∀ s : ℂ,
        (∑ i ∈ insert i₀ S, r i / (s - p i) + g s) =
        (r i₀ / (s - p i₀)) + (∑ i ∈ S, r i / (s - p i) + g s) := by
      intro s
      rw [Finset.sum_insert hi₀_notmem]; ring
    -- Therefore K(s)·(...) = K(s)·r(i₀)/(s - p(i₀)) + K(s)·(Σ_S + g).
    have h_factor_split : (fun s : ℂ => K s *
        (∑ i ∈ insert i₀ S, r i / (s - p i) + g s)) =
        (fun s : ℂ => K s * (r i₀ / (s - p i₀)) +
          K s * (∑ i ∈ S, r i / (s - p i) + g s)) := by
      funext s; rw [h_sum_split s]; ring
    rw [h_factor_split]
    -- Linearity: split via rectContourIntegral_add.  Continuity witnesses needed.
    have hKcont : Continuous K := hK.continuous
    -- Boundary points are not equal to any pole p_j (poles strictly interior).
    have h_seg_ne : ∀ j ∈ insert i₀ S, ∀ (z_of : ℝ → ℂ), Continuous z_of →
        (∀ t : ℝ, ((z_of t).im < -T ∨ T < (z_of t).im ∨
          (z_of t).re < σL ∨ σR < (z_of t).re)) → ∀ t : ℝ, z_of t ≠ p j := by
      intro j hj z_of hcont houtside t heq
      have hRe := (hp_re j hj).1
      have hRe' := (hp_re j hj).2
      have hIm := (hp_im j hj).1
      have hIm' := (hp_im j hj).2
      rcases houtside t with h | h | h | h
      · rw [heq] at h; linarith
      · rw [heq] at h; linarith
      · rw [heq] at h; linarith
      · rw [heq] at h; linarith
    -- Specialize to the four boundary segments.
    have h_bot_ne : ∀ j ∈ insert i₀ S, ∀ x : ℝ, ((x : ℂ) + (-T : ℝ) * I) ≠ p j := by
      intro j hj x heq
      have him : ((x : ℂ) + (-T : ℝ) * I).im = -T := by simp
      rw [heq] at him; linarith [(hp_im j hj).1]
    have h_top_ne : ∀ j ∈ insert i₀ S, ∀ x : ℝ, ((x : ℂ) + (T : ℝ) * I) ≠ p j := by
      intro j hj x heq
      have him : ((x : ℂ) + (T : ℝ) * I).im = T := by simp
      rw [heq] at him; linarith [(hp_im j hj).2]
    have h_right_ne : ∀ j ∈ insert i₀ S, ∀ y : ℝ, ((σR : ℂ) + (y : ℝ) * I) ≠ p j := by
      intro j hj y heq
      have hre : ((σR : ℂ) + (y : ℝ) * I).re = σR := by simp
      rw [heq] at hre; linarith [(hp_re j hj).2]
    have h_left_ne : ∀ j ∈ insert i₀ S, ∀ y : ℝ, ((σL : ℂ) + (y : ℝ) * I) ≠ p j := by
      intro j hj y heq
      have hre : ((σL : ℂ) + (y : ℝ) * I).re = σL := by simp
      rw [heq] at hre; linarith [(hp_re j hj).1]
    -- Continuity of K(s) · r(i₀) / (s - p(i₀)) on each segment.
    have hf_seg : ∀ (z_of : ℝ → ℂ) (h_cont : Continuous z_of)
        (h_ne : ∀ t : ℝ, z_of t ≠ p i₀),
        Continuous (fun t : ℝ => K (z_of t) * (r i₀ / (z_of t - p i₀))) := by
      intro z_of hcont hne
      refine (hKcont.comp hcont).mul ?_
      refine continuous_const.div (hcont.sub continuous_const) ?_
      intro t; exact sub_ne_zero.mpr (hne t)
    -- Explicit continuity of each boundary parameterization (avoid `continuity` timeouts).
    have h_param_bot : Continuous (fun x : ℝ => ((x : ℂ) + (-T : ℝ) * I)) :=
      (Complex.continuous_ofReal).add continuous_const
    have h_param_top : Continuous (fun x : ℝ => ((x : ℂ) + (T : ℝ) * I)) :=
      (Complex.continuous_ofReal).add continuous_const
    have h_param_right : Continuous (fun y : ℝ => ((σR : ℂ) + (y : ℝ) * I)) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_param_left : Continuous (fun y : ℝ => ((σL : ℂ) + (y : ℝ) * I)) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hf_bot := hf_seg (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) h_param_bot
      (h_bot_ne i₀ (Finset.mem_insert_self _ _))
    have hf_top := hf_seg (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) h_param_top
      (h_top_ne i₀ (Finset.mem_insert_self _ _))
    have hf_right := hf_seg (fun y : ℝ => (σR : ℂ) + (y : ℝ) * I) h_param_right
      (h_right_ne i₀ (Finset.mem_insert_self _ _))
    have hf_left := hf_seg (fun y : ℝ => (σL : ℂ) + (y : ℝ) * I) h_param_left
      (h_left_ne i₀ (Finset.mem_insert_self _ _))
    -- Continuity of K(s) · (Σ_S r/(s - p) + g s) on each segment.
    have hRest_seg : ∀ (z_of : ℝ → ℂ) (h_cont : Continuous z_of)
        (h_ne : ∀ j ∈ S, ∀ t : ℝ, z_of t ≠ p j),
        Continuous (fun t : ℝ =>
          K (z_of t) * (∑ i ∈ S, r i / (z_of t - p i) + g (z_of t))) := by
      intro z_of hcont hne
      refine (hKcont.comp hcont).mul ?_
      refine Continuous.add ?_ (hg.continuous.comp hcont)
      apply continuous_finset_sum
      intro i hi
      refine continuous_const.div (hcont.sub continuous_const) ?_
      intro t; exact sub_ne_zero.mpr (hne i hi t)
    have hRest_bot := hRest_seg (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) h_param_bot
      (fun j hj t => h_bot_ne j (Finset.mem_insert_of_mem hj) t)
    have hRest_top := hRest_seg (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) h_param_top
      (fun j hj t => h_top_ne j (Finset.mem_insert_of_mem hj) t)
    have hRest_right := hRest_seg (fun y : ℝ => (σR : ℂ) + (y : ℝ) * I) h_param_right
      (fun j hj t => h_right_ne j (Finset.mem_insert_of_mem hj) t)
    have hRest_left := hRest_seg (fun y : ℝ => (σL : ℂ) + (y : ℝ) * I) h_param_left
      (fun j hj t => h_left_ne j (Finset.mem_insert_of_mem hj) t)
    -- Apply linearity.
    rw [rectContourIntegral_add σL σR T _ _
        hf_bot hf_top hf_right hf_left hRest_bot hRest_top hRest_right hRest_left]
    -- First piece: ∮ K · r(i₀) / (s - p(i₀)) = K(p(i₀)) · r(i₀) · 2πi.
    have h_first_eq : (fun s : ℂ => K s * (r i₀ / (s - p i₀))) =
        (fun s : ℂ => r i₀ * (K s / (s - p i₀))) := by
      funext s; rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have h_first :
        rectContourIntegral σL σR T (fun s => K s * (r i₀ / (s - p i₀))) =
        r i₀ * (2 * (Real.pi : ℂ) * Complex.I * K (p i₀)) := by
      rw [h_first_eq, rectContourIntegral_const_mul]
      rw [rectContourIntegral_K_inv_eq_twoPiI_K K hK σL σR T hσ hT (p i₀) hp_re_i₀ hp_im_i₀]
    -- Second piece: by IH.
    have h_second := ih hp_re_S hp_im_S
    rw [h_first, h_second]
    rw [Finset.sum_insert hi₀_notmem]
    ring

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.rectContourIntegral_K_multi_inv_plus_analytic
