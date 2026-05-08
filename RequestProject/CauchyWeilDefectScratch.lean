import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.RectCauchyNegLogDerivZetaCoshGaussExt
import RequestProject.WeilWindingIntegral
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.CoshGaussMellinContinuation

/-!
# Scratch: K-twisted Weil identity for the gaussian-defect entire kernel
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

/-! ### Section 1: Symmetries of `gaussianDefectEntireKernel_local` -/

/-- **FE-symmetry of the entire kernel.**  `K(1 − s) = K(s)` because the
exponents `(s − 1/2)²` are invariant under `s ↦ 1 − s`. -/
theorem gaussianDefectEntireKernel_FE (s : ℂ) :
    gaussianDefectEntireKernel_local (1 - s) =
      gaussianDefectEntireKernel_local s := by
  unfold gaussianDefectEntireKernel_local
  have hsq : ((1 - s - 1/2 : ℂ))^2 = (s - 1/2)^2 := by ring
  rw [hsq]

/-- **Conjugate-symmetry of the entire kernel.** -/
theorem gaussianDefectEntireKernel_conj (s : ℂ) :
    gaussianDefectEntireKernel_local (star s) =
      star (gaussianDefectEntireKernel_local s) := by
  -- For ℂ, `star = (starRingEnd ℂ)`.  Bridge via Complex.star_def (the
  -- conjugation-as-ring-hom).
  have h_star_eq : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  unfold gaussianDefectEntireKernel_local
  rw [h_star_eq, h_star_eq]
  -- Now: K((conj s)) = conj (K s) where conj := starRingEnd ℂ.
  set conj : ℂ →+* ℂ := starRingEnd ℂ with hconj_def
  rw [map_mul conj, Complex.conj_ofReal,
    map_add conj, map_sub conj, map_one conj]
  rw [show conj (2 * Complex.exp ((s - 1/2)^2 / 8)) =
        conj 2 * conj (Complex.exp ((s - 1/2)^2 / 8)) from map_mul conj _ _]
  rw [show conj (2 : ℂ) = (2 : ℂ) by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, Complex.conj_ofReal]]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  rw [map_div₀ conj, map_div₀ conj]
  rw [show conj (2 : ℂ) = (2 : ℂ) by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, Complex.conj_ofReal]]
  rw [show conj (8 : ℂ) = (8 : ℂ) by
    rw [show (8 : ℂ) = (((8 : ℝ)) : ℂ) by norm_num, Complex.conj_ofReal]]
  -- We have RHS containing `conj ((s - 1/2)^2)`.  Pull conj inside:
  --   conj ((s - 1/2)^2) = (conj (s - 1/2))^2 = (conj s - 1/2)^2.
  rw [show conj ((s - 1/2 : ℂ)^2) = (conj s - 1/2)^2 by
    rw [map_pow conj, map_sub conj,
      show conj (1/2 : ℂ) = (1/2 : ℂ) by
        rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num, Complex.conj_ofReal]]]

/-! ### Section 2: Cauchy-K on a rectangle

Goal: `∮_rect K(s) / (s - p) ds = 2πi · K(p)` for `K` analytic on the rectangle
and `p` strictly interior. -/

/-- If `K` is analytic at `p`, then the difference quotient `(K(s) - K(p)) / (s - p)`
extends to a function analytic at `p`. -/
lemma diffq_K_analyticAt {K : ℂ → ℂ} {p : ℂ} (hK : AnalyticAt ℂ K p) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q p ∧
      ∀ᶠ s in nhdsWithin p {p}ᶜ, (K s - K p) / (s - p) = q s := by
  have hg_an : AnalyticAt ℂ (fun s => K s - K p) p := hK.sub analyticAt_const
  have hg_zero : (fun s => K s - K p) p = 0 := by simp
  have h_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (fun s => K s - K p) p := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_zero_order
    rw [hg_an.analyticOrderAt_eq_zero] at h_zero_order
    exact h_zero_order hg_zero
  obtain ⟨q, hq_an, hq_eq⟩ :=
    ((natCast_le_analyticOrderAt hg_an).mp h_order_ge_one)
  refine ⟨q, hq_an, ?_⟩
  have h_mono : (fun s : ℂ => K s - K p) =ᶠ[nhdsWithin p {p}ᶜ]
      (fun s => (s - p) ^ 1 • q s) :=
    hq_eq.filter_mono nhdsWithin_le_nhds
  have h_sub_ne : ∀ᶠ s in nhdsWithin p {p}ᶜ, s - p ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero_of_ne hs
  filter_upwards [h_mono, h_sub_ne] with s hs hne
  simp only [pow_one, smul_eq_mul] at hs
  rw [hs]; field_simp

/-- The analytic extension `diffq hK` of `(K(s) - K(p))/(s - p)`: choose any
analytic `q` agreeing with the difference quotient on a punctured nhd of `p`
(which exists by `diffq_K_analyticAt`).  Indexed directly by the analyticity
proof to avoid `if-then-else` and Decidable resolution issues. -/
noncomputable def diffq {K : ℂ → ℂ} {p : ℂ} (hK : AnalyticAt ℂ K p) : ℂ → ℂ :=
  Classical.choose (diffq_K_analyticAt hK)

/-- `diffq hK` is analytic at `p`. -/
lemma diffq_analyticAt_pole {K : ℂ → ℂ} {p : ℂ} (hK : AnalyticAt ℂ K p) :
    AnalyticAt ℂ (diffq hK) p :=
  (Classical.choose_spec (diffq_K_analyticAt hK)).1

/-- Off `p`, `diffq hK` agrees with the actual difference quotient (eventually). -/
lemma diffq_eq_on_nhdsWithin {K : ℂ → ℂ} {p : ℂ} (hK : AnalyticAt ℂ K p) :
    ∀ᶠ s in nhdsWithin p {p}ᶜ, (K s - K p) / (s - p) = diffq hK s :=
  (Classical.choose_spec (diffq_K_analyticAt hK)).2

/-! ### Section 3: Global analytic extension of the difference quotient -/

/-- The global analytic extension of `(K s − K p) / (s − p)` to all of `ℂ`.
At `s = p` it equals `deriv K p`; elsewhere it equals the difference quotient.
For entire `K`, this is differentiable everywhere. -/
noncomputable def globalDiffq (K : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (K s - K p) / (s - p)) p (deriv K p)

/-- Off `p`, `globalDiffq` agrees with the bare difference quotient. -/
lemma globalDiffq_of_ne {K : ℂ → ℂ} {p s : ℂ} (hs : s ≠ p) :
    globalDiffq K p s = (K s - K p) / (s - p) := by
  unfold globalDiffq
  rw [Function.update_of_ne hs]

/-- At `p`, `globalDiffq` is `deriv K p`. -/
lemma globalDiffq_at_pole (K : ℂ → ℂ) (p : ℂ) :
    globalDiffq K p p = deriv K p := by
  unfold globalDiffq
  rw [Function.update_self]

/-- Off `p`, `globalDiffq K p` is differentiable from `K` differentiable. -/
lemma globalDiffq_differentiableAt_of_ne {K : ℂ → ℂ} {p s : ℂ}
    (hK : Differentiable ℂ K) (hs : s ≠ p) :
    DifferentiableAt ℂ (globalDiffq K p) s := by
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hs
  have h_diff_q : DifferentiableAt ℂ (fun z => (K z - K p) / (z - p)) s := by
    apply DifferentiableAt.div
    · exact (hK s).sub_const _
    · exact differentiableAt_id.sub_const _
    · exact hsub
  -- globalDiffq K p agrees with the bare diffq on a nhd of s (since s ≠ p).
  have h_eq : (globalDiffq K p) =ᶠ[nhds s] (fun z => (K z - K p) / (z - p)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_ne hs] with z hz
    exact globalDiffq_of_ne hz
  exact h_diff_q.congr_of_eventuallyEq h_eq

/-- At `p`, `globalDiffq K p` is differentiable via the analytic extension
of the difference quotient. -/
lemma globalDiffq_differentiableAt_pole {K : ℂ → ℂ} {p : ℂ}
    (hK : Differentiable ℂ K) :
    DifferentiableAt ℂ (globalDiffq K p) p := by
  have hK_diffOn : DifferentiableOn ℂ K Set.univ := hK.differentiableOn
  have hKan_on : AnalyticOnNhd ℂ K Set.univ :=
    hK_diffOn.analyticOnNhd isOpen_univ
  have hKan : AnalyticAt ℂ K p := hKan_on p (Set.mem_univ p)
  have h_q_an : AnalyticAt ℂ (diffq hKan) p := diffq_analyticAt_pole hKan
  -- Step 1: `diffq hKan p = deriv K p`, hence `globalDiffq K p p = diffq hKan p`.
  have h_at_p : globalDiffq K p p = diffq hKan p := by
    have h_qcont : ContinuousAt (diffq hKan) p := h_q_an.continuousAt
    have h_dq_tendsto :
        Filter.Tendsto (fun s => (K s - K p) / (s - p)) (nhdsWithin p {p}ᶜ)
          (nhds (deriv K p)) := by
      have hHasDeriv : HasDerivAt K (deriv K p) p := (hK p).hasDerivAt
      have h_slope := hHasDeriv.tendsto_slope
      have h_eq_fun : (fun s => slope K p s) = (fun s => (K s - K p) / (s - p)) := by
        funext s
        simp [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul, mul_comm]
      rw [← h_eq_fun]
      exact h_slope
    have h_q_tendsto : Filter.Tendsto (diffq hKan) (nhdsWithin p {p}ᶜ)
        (nhds (deriv K p)) :=
      h_dq_tendsto.congr' (diffq_eq_on_nhdsWithin hKan)
    have h_q_full : Filter.Tendsto (diffq hKan) (nhdsWithin p {p}ᶜ)
        (nhds (diffq hKan p)) :=
      h_qcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [globalDiffq_at_pole, tendsto_nhds_unique h_q_full h_q_tendsto]
  -- Step 2: `globalDiffq K p =ᶠ[nhds p] diffq hKan`.
  have h_eq : (globalDiffq K p) =ᶠ[nhds p] (diffq hKan) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    have h_punc := diffq_eq_on_nhdsWithin hKan
    rw [Filter.eventually_iff_exists_mem] at h_punc
    obtain ⟨U, hU_in, hU_eq⟩ := h_punc
    rw [mem_nhdsWithin] at hU_in
    obtain ⟨V, hV_open, hV_p, hV_sub⟩ := hU_in
    refine ⟨V, hV_open.mem_nhds hV_p, fun z hz_V => ?_⟩
    by_cases hz_eq : z = p
    · rw [hz_eq]; exact h_at_p
    · have hz_in_U : z ∈ U := hV_sub ⟨hz_V, hz_eq⟩
      rw [globalDiffq_of_ne hz_eq]
      exact hU_eq z hz_in_U
  -- Step 3: differentiability transfers via eventuallyEq.
  exact h_q_an.differentiableAt.congr_of_eventuallyEq h_eq

/-- `globalDiffq K p` is differentiable everywhere when `K` is. -/
lemma globalDiffq_differentiable {K : ℂ → ℂ} (p : ℂ) (hK : Differentiable ℂ K) :
    Differentiable ℂ (globalDiffq K p) := by
  intro s
  by_cases hs : s = p
  · rw [hs]; exact globalDiffq_differentiableAt_pole hK
  · exact globalDiffq_differentiableAt_of_ne hK hs

/-! ### Section 4: Cauchy-K on a rectangle -/

open ZD.WeilPositivity.Contour

/-- `rectContourIntegral` pulls out a complex constant from the integrand. -/
lemma rectContourIntegral_const_mul (σL σR T : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    rectContourIntegral σL σR T (fun z => c * f z) =
      c * rectContourIntegral σL σR T f := by
  have h1 : (∫ x : ℝ in σL..σR, (fun z => c * f z) (↑x + (-T : ℝ) * I)) =
      c * ∫ x : ℝ in σL..σR, f (↑x + (-T : ℝ) * I) :=
    intervalIntegral.integral_const_mul c (fun x : ℝ => f (↑x + (-T : ℝ) * I))
  have h2 : (∫ x : ℝ in σL..σR, (fun z => c * f z) (↑x + (T : ℝ) * I)) =
      c * ∫ x : ℝ in σL..σR, f (↑x + (T : ℝ) * I) :=
    intervalIntegral.integral_const_mul c (fun x : ℝ => f (↑x + (T : ℝ) * I))
  have h3 : (∫ y : ℝ in (-T : ℝ)..T, (fun z => c * f z) (↑σR + ↑y * I)) =
      c * ∫ y : ℝ in (-T : ℝ)..T, f (↑σR + ↑y * I) :=
    intervalIntegral.integral_const_mul c (fun y : ℝ => f (↑σR + ↑y * I))
  have h4 : (∫ y : ℝ in (-T : ℝ)..T, (fun z => c * f z) (↑σL + ↑y * I)) =
      c * ∫ y : ℝ in (-T : ℝ)..T, f (↑σL + ↑y * I) :=
    intervalIntegral.integral_const_mul c (fun y : ℝ => f (↑σL + ↑y * I))
  unfold rectContourIntegral
  rw [h1, h2, h3, h4]
  simp only [smul_eq_mul]; ring

/-- `rectContourIntegral` is additive on its integrand argument when both
parts are continuous on the rectangle boundary. -/
lemma rectContourIntegral_add (σL σR T : ℝ) (f g : ℂ → ℂ)
    (hf_bot : Continuous (fun x : ℝ => f ((x : ℂ) + (-T : ℝ) * I)))
    (hf_top : Continuous (fun x : ℝ => f ((x : ℂ) + (T : ℝ) * I)))
    (hf_right : Continuous (fun y : ℝ => f ((σR : ℂ) + (y : ℝ) * I)))
    (hf_left : Continuous (fun y : ℝ => f ((σL : ℂ) + (y : ℝ) * I)))
    (hg_bot : Continuous (fun x : ℝ => g ((x : ℂ) + (-T : ℝ) * I)))
    (hg_top : Continuous (fun x : ℝ => g ((x : ℂ) + (T : ℝ) * I)))
    (hg_right : Continuous (fun y : ℝ => g ((σR : ℂ) + (y : ℝ) * I)))
    (hg_left : Continuous (fun y : ℝ => g ((σL : ℂ) + (y : ℝ) * I))) :
    rectContourIntegral σL σR T (fun z => f z + g z) =
      rectContourIntegral σL σR T f + rectContourIntegral σL σR T g := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_add (hf_bot.intervalIntegrable _ _) (hg_bot.intervalIntegrable _ _),
      intervalIntegral.integral_add (hf_top.intervalIntegrable _ _) (hg_top.intervalIntegrable _ _),
      intervalIntegral.integral_add (hf_right.intervalIntegrable _ _) (hg_right.intervalIntegrable _ _),
      intervalIntegral.integral_add (hf_left.intervalIntegrable _ _) (hg_left.intervalIntegrable _ _)]
  simp only [smul_add]
  ring

/-- **Cauchy's integral formula for an entire `K` on an axis-aligned rectangle.**
For `K` differentiable on `ℂ` and `p` strictly inside the rectangle, the
contour integral of `K(s) / (s − p)` equals `2πi · K(p)`. -/
theorem rectContourIntegral_K_inv_eq_twoPiI_K
    (K : ℂ → ℂ) (hK : Differentiable ℂ K)
    (σL σR T : ℝ) (hσ : σL < σR) (hT : 0 < T) (p : ℂ)
    (hp_re : σL < p.re ∧ p.re < σR) (hp_im : -T < p.im ∧ p.im < T) :
    rectContourIntegral σL σR T (fun s => K s / (s - p)) =
      2 * (Real.pi : ℂ) * Complex.I * K p := by
  -- Pointwise decomposition for s ≠ p:
  --   K(s)/(s - p) = K(p)/(s - p) + globalDiffq K p s.
  have h_decomp : ∀ s : ℂ, s ≠ p →
      K s / (s - p) = K p / (s - p) + globalDiffq K p s := by
    intro s hs
    rw [globalDiffq_of_ne hs]
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring
  -- The four boundary points all have s ≠ p (p is strictly interior).
  have h_bot_ne : ∀ x : ℝ, ((x : ℂ) + (-T : ℝ) * I) ≠ p := by
    intro x heq
    have him : ((x : ℂ) + (-T : ℝ) * I).im = -T := by simp
    rw [heq] at him
    have : p.im = -T := him
    linarith [hp_im.1]
  have h_top_ne : ∀ x : ℝ, ((x : ℂ) + (T : ℝ) * I) ≠ p := by
    intro x heq
    have him : ((x : ℂ) + (T : ℝ) * I).im = T := by simp
    rw [heq] at him
    have : p.im = T := him
    linarith [hp_im.2]
  have h_right_ne : ∀ y : ℝ, ((σR : ℂ) + (y : ℝ) * I) ≠ p := by
    intro y heq
    have hre : ((σR : ℂ) + (y : ℝ) * I).re = σR := by simp
    rw [heq] at hre
    have : p.re = σR := hre
    linarith [hp_re.2]
  have h_left_ne : ∀ y : ℝ, ((σL : ℂ) + (y : ℝ) * I) ≠ p := by
    intro y heq
    have hre : ((σL : ℂ) + (y : ℝ) * I).re = σL := by simp
    rw [heq] at hre
    have : p.re = σL := hre
    linarith [hp_re.1]
  -- Rewrite the integrand on each boundary segment via h_decomp.
  have h_bot_decomp : ∀ x : ℝ,
      K ((x : ℂ) + (-T : ℝ) * I) / (((x : ℂ) + (-T : ℝ) * I) - p) =
      K p / (((x : ℂ) + (-T : ℝ) * I) - p) +
        globalDiffq K p ((x : ℂ) + (-T : ℝ) * I) := fun x => h_decomp _ (h_bot_ne x)
  have h_top_decomp : ∀ x : ℝ,
      K ((x : ℂ) + (T : ℝ) * I) / (((x : ℂ) + (T : ℝ) * I) - p) =
      K p / (((x : ℂ) + (T : ℝ) * I) - p) +
        globalDiffq K p ((x : ℂ) + (T : ℝ) * I) := fun x => h_decomp _ (h_top_ne x)
  have h_right_decomp : ∀ y : ℝ,
      K ((σR : ℂ) + (y : ℝ) * I) / (((σR : ℂ) + (y : ℝ) * I) - p) =
      K p / (((σR : ℂ) + (y : ℝ) * I) - p) +
        globalDiffq K p ((σR : ℂ) + (y : ℝ) * I) := fun y => h_decomp _ (h_right_ne y)
  have h_left_decomp : ∀ y : ℝ,
      K ((σL : ℂ) + (y : ℝ) * I) / (((σL : ℂ) + (y : ℝ) * I) - p) =
      K p / (((σL : ℂ) + (y : ℝ) * I) - p) +
        globalDiffq K p ((σL : ℂ) + (y : ℝ) * I) := fun y => h_decomp _ (h_left_ne y)
  -- The remainder is differentiable on the rectangle.
  have h_g_diff : Differentiable ℂ (globalDiffq K p) :=
    globalDiffq_differentiable p hK
  have h_g_diffOn : DifferentiableOn ℂ (globalDiffq K p)
      ((Set.uIcc σL σR) ×ℂ (Set.uIcc (-T) T)) :=
    h_g_diff.differentiableOn
  -- Therefore its rectangle integral vanishes.
  have h_g_zero : rectContourIntegral σL σR T (globalDiffq K p) = 0 :=
    rectContourIntegral_eq_zero_of_differentiableOn σL σR T _ h_g_diffOn
  -- The K(p)·(s - p)⁻¹ piece gives 2πi · K(p) (factor out the constant K(p)).
  have h_const : rectContourIntegral σL σR T (fun s => K p / (s - p)) =
      K p * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h_inv : rectContourIntegral σL σR T (fun s => (s - p)⁻¹) =
        2 * (Real.pi : ℂ) * Complex.I :=
      rectContourIntegral_inv_center_eq_twoPiI σL σR T hσ hT p hp_re hp_im
    have h_eq : (fun s : ℂ => K p / (s - p)) = (fun s : ℂ => K p * (s - p)⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [h_eq, rectContourIntegral_const_mul, h_inv]
  -- Helper: each boundary integrand of `K(p)/(s - p)` is continuous, hence integrable.
  -- Separately, the boundary integrand of `globalDiffq K p` is continuous (from
  -- differentiability), hence integrable.  These give intervalIntegrability for
  -- the four `intervalIntegral.integral_add` steps below.
  -- Construct each of the 4 segment-wise integrability witnesses.
  have h_inv_bot : IntervalIntegrable
      (fun x : ℝ => K p / (((x : ℂ) + (-T : ℝ) * I) - p)) MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (by continuity : Continuous (fun x : ℝ => ((x : ℂ) + (-T : ℝ) * I) - p)).continuousOn
    · intro x _; exact sub_ne_zero.mpr (h_bot_ne x)
  have h_inv_top : IntervalIntegrable
      (fun x : ℝ => K p / (((x : ℂ) + (T : ℝ) * I) - p)) MeasureTheory.volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (by continuity : Continuous (fun x : ℝ => ((x : ℂ) + (T : ℝ) * I) - p)).continuousOn
    · intro x _; exact sub_ne_zero.mpr (h_top_ne x)
  have h_inv_right : IntervalIntegrable
      (fun y : ℝ => K p / (((σR : ℂ) + (y : ℝ) * I) - p)) MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (by continuity : Continuous (fun y : ℝ => ((σR : ℂ) + (y : ℝ) * I) - p)).continuousOn
    · intro y _; exact sub_ne_zero.mpr (h_right_ne y)
  have h_inv_left : IntervalIntegrable
      (fun y : ℝ => K p / (((σL : ℂ) + (y : ℝ) * I) - p)) MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (by continuity : Continuous (fun y : ℝ => ((σL : ℂ) + (y : ℝ) * I) - p)).continuousOn
    · intro y _; exact sub_ne_zero.mpr (h_left_ne y)
  -- Continuity-based intervalIntegrability for the globalDiffq side.
  have h_g_cont : Continuous (globalDiffq K p) := h_g_diff.continuous
  have h_g_bot_cont : Continuous (fun x : ℝ => globalDiffq K p ((x : ℂ) + (-T : ℝ) * I)) :=
    h_g_cont.comp (by continuity)
  have h_g_top_cont : Continuous (fun x : ℝ => globalDiffq K p ((x : ℂ) + (T : ℝ) * I)) :=
    h_g_cont.comp (by continuity)
  have h_g_right_cont : Continuous (fun y : ℝ => globalDiffq K p ((σR : ℂ) + (y : ℝ) * I)) :=
    h_g_cont.comp (by continuity)
  have h_g_left_cont : Continuous (fun y : ℝ => globalDiffq K p ((σL : ℂ) + (y : ℝ) * I)) :=
    h_g_cont.comp (by continuity)
  have h_g_bot : IntervalIntegrable
      (fun x : ℝ => globalDiffq K p ((x : ℂ) + (-T : ℝ) * I))
      MeasureTheory.volume σL σR :=
    h_g_bot_cont.intervalIntegrable _ _
  have h_g_top : IntervalIntegrable
      (fun x : ℝ => globalDiffq K p ((x : ℂ) + (T : ℝ) * I))
      MeasureTheory.volume σL σR :=
    h_g_top_cont.intervalIntegrable _ _
  have h_g_right : IntervalIntegrable
      (fun y : ℝ => globalDiffq K p ((σR : ℂ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    h_g_right_cont.intervalIntegrable _ _
  have h_g_left : IntervalIntegrable
      (fun y : ℝ => globalDiffq K p ((σL : ℂ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    h_g_left_cont.intervalIntegrable _ _
  -- Now split each of the 4 boundary integrals using integral_congr + integral_add.
  have h_split : rectContourIntegral σL σR T (fun s => K s / (s - p)) =
      rectContourIntegral σL σR T (fun s => K p / (s - p)) +
      rectContourIntegral σL σR T (globalDiffq K p) := by
    unfold rectContourIntegral
    rw [intervalIntegral.integral_congr (g := fun x =>
          K p / (((x : ℂ) + (-T : ℝ) * I) - p) +
            globalDiffq K p ((x : ℂ) + (-T : ℝ) * I))
        (fun x _ => h_bot_decomp x)]
    rw [intervalIntegral.integral_congr (g := fun x =>
          K p / (((x : ℂ) + (T : ℝ) * I) - p) +
            globalDiffq K p ((x : ℂ) + (T : ℝ) * I))
        (fun x _ => h_top_decomp x)]
    rw [intervalIntegral.integral_congr (g := fun y =>
          K p / (((σR : ℂ) + (y : ℝ) * I) - p) +
            globalDiffq K p ((σR : ℂ) + (y : ℝ) * I))
        (fun y _ => h_right_decomp y)]
    rw [intervalIntegral.integral_congr (g := fun y =>
          K p / (((σL : ℂ) + (y : ℝ) * I) - p) +
            globalDiffq K p ((σL : ℂ) + (y : ℝ) * I))
        (fun y _ => h_left_decomp y)]
    rw [intervalIntegral.integral_add h_inv_bot h_g_bot,
        intervalIntegral.integral_add h_inv_top h_g_top,
        intervalIntegral.integral_add h_inv_right h_g_right,
        intervalIntegral.integral_add h_inv_left h_g_left]
    -- Rearrange the 8 boundary integrals into two groups of 4.
    rw [smul_add, smul_add]
    ring
  rw [h_split, h_g_zero, add_zero, h_const]; ring

/-! ### Section 5: K-twisted Cauchy with analytic remainder -/

/-- **K-twisted Cauchy: single pole + entire holomorphic remainder.**
For entire `K`, entire remainder `g`, residue `r` at strictly interior pole `p`:
`∮ K(s) · (r / (s − p) + g(s)) ds = 2πi · K(p) · r`.

The two pieces:
* `∮ K(s) · r / (s − p) ds = r · 2πi · K(p)` via const-pull-out + `rectContourIntegral_K_inv_eq_twoPiI_K`.
* `∮ K(s) · g(s) ds = 0` since K·g is entire (Cauchy-Goursat). -/
theorem rectContourIntegral_K_inv_plus_analytic
    (K : ℂ → ℂ) (hK : Differentiable ℂ K)
    (σL σR T : ℝ) (hσ : σL < σR) (hT : 0 < T) (p : ℂ)
    (hp_re : σL < p.re ∧ p.re < σR) (hp_im : -T < p.im ∧ p.im < T)
    (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    rectContourIntegral σL σR T (fun s => K s * (r / (s - p) + g s)) =
      2 * (Real.pi : ℂ) * Complex.I * K p * r := by
  -- Distribute: K(s) · (r/(s-p) + g(s)) = K(s)·r/(s-p) + K(s)·g(s).
  have h_dist : (fun s : ℂ => K s * (r / (s - p) + g s)) =
      (fun s : ℂ => K s * r * (1 / (s - p)) + K s * g s) := by
    funext s; rw [mul_add]; ring
  rw [h_dist]
  -- Continuity witnesses for `rectContourIntegral_add`.
  have hKcont : Continuous K := hK.continuous
  have hgcont : Continuous g := hg.continuous
  -- Boundary points are not equal to p.
  have h_bot_ne : ∀ x : ℝ, ((x : ℂ) + (-T : ℝ) * I) ≠ p := fun x heq => by
    have him : ((x : ℂ) + (-T : ℝ) * I).im = -T := by simp
    rw [heq] at him; linarith [hp_im.1]
  have h_top_ne : ∀ x : ℝ, ((x : ℂ) + (T : ℝ) * I) ≠ p := fun x heq => by
    have him : ((x : ℂ) + (T : ℝ) * I).im = T := by simp
    rw [heq] at him; linarith [hp_im.2]
  have h_right_ne : ∀ y : ℝ, ((σR : ℂ) + (y : ℝ) * I) ≠ p := fun y heq => by
    have hre : ((σR : ℂ) + (y : ℝ) * I).re = σR := by simp
    rw [heq] at hre; linarith [hp_re.2]
  have h_left_ne : ∀ y : ℝ, ((σL : ℂ) + (y : ℝ) * I) ≠ p := fun y heq => by
    have hre : ((σL : ℂ) + (y : ℝ) * I).re = σL := by simp
    rw [heq] at hre; linarith [hp_re.1]
  -- Continuity of K·r·(1/(s-p)) on each boundary segment.
  have hf_cont : ∀ (z_of : ℝ → ℂ), Continuous z_of →
      (∀ t : ℝ, z_of t ≠ p) →
      Continuous (fun t : ℝ => K (z_of t) * r * (1 / (z_of t - p))) := by
    intro z_of hcont hne
    refine ((hKcont.comp hcont).mul continuous_const).mul ?_
    refine continuous_const.div (hcont.sub continuous_const) ?_
    intro t; exact sub_ne_zero.mpr (hne t)
  -- Continuity of K·g on each boundary.
  have hKg_cont : Continuous (fun s : ℂ => K s * g s) := hKcont.mul hgcont
  have hKg_seg : ∀ (z_of : ℝ → ℂ), Continuous z_of →
      Continuous (fun t : ℝ => K (z_of t) * g (z_of t)) := fun z_of hcont =>
    hKg_cont.comp hcont
  -- Apply linearity.
  rw [rectContourIntegral_add σL σR T
        (fun s => K s * r * (1 / (s - p))) (fun s => K s * g s)
        (hf_cont (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) (by continuity) h_bot_ne)
        (hf_cont (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) (by continuity) h_top_ne)
        (hf_cont (fun y : ℝ => (σR : ℂ) + (y : ℝ) * I) (by continuity) h_right_ne)
        (hf_cont (fun y : ℝ => (σL : ℂ) + (y : ℝ) * I) (by continuity) h_left_ne)
        (hKg_seg (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) (by continuity))
        (hKg_seg (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) (by continuity))
        (hKg_seg (fun y : ℝ => (σR : ℂ) + (y : ℝ) * I) (by continuity))
        (hKg_seg (fun y : ℝ => (σL : ℂ) + (y : ℝ) * I) (by continuity))]
  -- Second piece: ∮ K·g = 0 since K·g is entire.
  have h_Kg_zero : rectContourIntegral σL σR T (fun s => K s * g s) = 0 :=
    rectContourIntegral_eq_zero_of_differentiableOn σL σR T _
      (hK.mul hg).differentiableOn
  -- First piece: ∮ K(s)·r·(1/(s-p)) = K p · r · 2πi via const-pull-out + Cauchy-K.
  have h_eq_first : (fun s : ℂ => K s * r * (1 / (s - p))) =
      (fun s : ℂ => r * (K s / (s - p))) := by
    funext s; rw [div_eq_mul_inv]; ring
  have h_first : rectContourIntegral σL σR T (fun s => K s * r * (1 / (s - p))) =
      r * (2 * (Real.pi : ℂ) * Complex.I * K p) := by
    rw [h_eq_first]
    rw [rectContourIntegral_const_mul σL σR T r (fun s => K s / (s - p))]
    rw [rectContourIntegral_K_inv_eq_twoPiI_K K hK σL σR T hσ hT p hp_re hp_im]
  rw [h_first, h_Kg_zero, add_zero]
  ring

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.globalDiffq_differentiable
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.rectContourIntegral_K_inv_eq_twoPiI_K
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.rectContourIntegral_K_inv_plus_analytic
