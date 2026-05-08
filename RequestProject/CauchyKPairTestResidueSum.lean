import Mathlib
import RequestProject.CauchyKPairTestLimit
import RequestProject.OfflineDetectorProof
import RequestProject.WeilFinalAssemblyUnconditional

/-!
# Discharge: residue-sum tendsto for the K-twisted Cauchy/Weil identity

Discharges
`K_pairTestMellin_residue_sum_tendsto K β n Z_at`
conditional on:

* absolute summability of `n(ρ) · K(ρ) · M(β,ρ)` over the subtype of
  nontrivial zeros (target Prop `K_pairTestMellin_zeroSum_summable`),
* `Z_at` returning the in-rectangle set of nontrivial zeros: every
  element of `Z_at T` is a nontrivial zero, and every nontrivial zero
  with `|Im ρ| < T` belongs to `Z_at T`.

The latter two conditions are *exactly* the `hZ_mem`/`hZ_complete`
hypotheses already used in
`rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum`
(chunk 1) — the discharge consumes the same data.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

/-- Absolute summability of `n(ρ) · K(ρ) · M(β,ρ)` over the subtype of
nontrivial zeros. This is the analytic input the residue-sum tendsto
target requires. -/
def K_pairTestMellin_zeroSum_summable
    (K : ℂ → ℂ) (β : ℝ) (n : ℂ → ℕ) : Prop :=
  Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
    ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val)

/-- **Discharge of `K_pairTestMellin_residue_sum_tendsto`** from absolute
summability + the in-rectangle structure of `Z_at`.

`hZ_in_NTZ`/`hZ_complete_im` are the same data as `hZ_mem`/`hZ_complete`
used by the chunk-1 finite-T identity, so this composes directly with
chunk 2.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem K_pairTestMellin_residue_sum_tendsto_of_summable
    (K : ℂ → ℂ) (β : ℝ) (n : ℂ → ℕ)
    (Z_at : ℝ → Finset ℂ)
    (hZ_in_NTZ : ∀ T : ℝ, ∀ ρ ∈ Z_at T, ρ ∈ NontrivialZeros)
    (hZ_complete_im : ∀ T : ℝ, ∀ ρ : ℂ,
      ρ ∈ NontrivialZeros → -T < ρ.im → ρ.im < T → ρ ∈ Z_at T)
    (hSummable : K_pairTestMellin_zeroSum_summable K β n) :
    K_pairTestMellin_residue_sum_tendsto K β n Z_at := by
  unfold K_pairTestMellin_residue_sum_tendsto
  -- Lift Z_at to a finset on the subtype.
  set f : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℂ :=
    fun ρ => ((n ρ.val : ℕ) : ℂ) * K ρ.val * Contour.pairTestMellin β ρ.val with hf_def
  set S : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, f ρ with hS_def
  -- The lifted finset on the subtype.
  set Z_lift : ℝ → Finset {ρ : ℂ // ρ ∈ NontrivialZeros} := fun T =>
    (Z_at T).attach.image
      (fun ρ : Z_at T => ⟨ρ.val, hZ_in_NTZ T ρ.val ρ.property⟩) with hZ_lift_def
  -- The sum over Z_at equals the sum over Z_lift via this lifting.
  have h_sum_eq : ∀ T : ℝ,
      (∑ ρ ∈ Z_at T, ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ) =
      (∑ ρ ∈ Z_lift T, f ρ) := by
    intro T
    rw [hZ_lift_def]
    rw [Finset.sum_image (by
      intro a _ b _ hab
      have h_val : a.val = b.val := by
        have := Subtype.mk.injEq (a.val) (hZ_in_NTZ T a.val a.property) (b.val)
                  (hZ_in_NTZ T b.val b.property) |>.mp hab
        exact this
      exact Subtype.ext h_val)]
    rw [← Finset.sum_attach]
  -- HasSum f S along Filter.atTop on Finset of subtype.
  have h_hasSum : HasSum f S := hSummable.hasSum
  -- Tendsto on the subtype filter.
  have h_subtype_tendsto :
      Tendsto (fun s : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} => ∑ ρ ∈ s, f ρ)
        Filter.atTop (nhds S) := h_hasSum
  -- Z_lift is cofinal in Finset _.
  have h_Z_lift_cofinal :
      Tendsto Z_lift
        (Filter.atTop ⊓ Filter.principal {T : ℝ | FinalAssembly.goodHeight T})
        (Filter.atTop : Filter (Finset {ρ : ℂ // ρ ∈ NontrivialZeros})) := by
    rw [Filter.tendsto_atTop]
    intro s
    -- For each ρ ∈ s, pick a height past |Im ρ|. Since s is a finite set,
    -- Finset.exists_le over the image gives an upper bound.
    obtain ⟨T₀, hT₀⟩ : ∃ M : ℝ, ∀ ρ ∈ s, |ρ.val.im| < M := by
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨0, fun ρ hρ => by simp at hρ⟩
      | insert ρ₀ S hρ₀_notmem ih =>
        obtain ⟨M_S, hM_S⟩ := ih
        refine ⟨max M_S (|ρ₀.val.im| + 1), fun ρ hρ => ?_⟩
        rcases Finset.mem_insert.mp hρ with rfl | hρ_S
        · have : |ρ.val.im| < |ρ.val.im| + 1 := by linarith
          exact lt_of_lt_of_le this (le_max_right _ _)
        · exact lt_of_lt_of_le (hM_S ρ hρ_S) (le_max_left _ _)
    rw [Filter.eventually_inf_principal]
    filter_upwards [Filter.eventually_ge_atTop T₀] with T hT_ge _hGood
    intro ρ hρ
    rw [hZ_lift_def, Finset.mem_image]
    have h_ρ_in_NTZ : ρ.val ∈ NontrivialZeros := ρ.property
    have h_im_bound : |ρ.val.im| < T₀ := hT₀ ρ hρ
    have h_im_lt_T : |ρ.val.im| < T := lt_of_lt_of_le h_im_bound hT_ge
    have h_lo : -T < ρ.val.im := by
      have := abs_lt.mp h_im_lt_T
      linarith [this.1]
    have h_hi : ρ.val.im < T := by
      have := abs_lt.mp h_im_lt_T
      linarith [this.2]
    have h_in_Z : ρ.val ∈ Z_at T := hZ_complete_im T ρ.val h_ρ_in_NTZ h_lo h_hi
    refine ⟨⟨ρ.val, h_in_Z⟩, Finset.mem_attach _ _, ?_⟩
    rfl
  -- Compose: the tendsto of Z_lift composed with the tendsto on subtype-finset.
  have h_lifted_tendsto :
      Tendsto (fun T : ℝ => ∑ ρ ∈ Z_lift T, f ρ)
        (Filter.atTop ⊓ Filter.principal {T : ℝ | FinalAssembly.goodHeight T})
        (nhds S) :=
    h_subtype_tendsto.comp h_Z_lift_cofinal
  -- Bridge back to Z_at via h_sum_eq.
  refine h_lifted_tendsto.congr' ?_
  filter_upwards with T
  exact (h_sum_eq T).symm

/-! ## Unconditional summability for `K = gaussianDefectEntireKernel_local` -/

/-- **Uniform bound on `K = gaussianDefectEntireKernel_local` on the critical strip.**
Every nontrivial zero `ρ` has `0 < Re ρ < 1`, so `(Re ρ - 1/2)² ≤ 1/4`. Combined with
`(Im ρ)²/k ≥ 0` in the exponent, `‖K(ρ)‖ ≤ π√(π/2)·(exp(1/8) + 2·exp(1/32) + 1)`. -/
private lemma gaussianDefectEntireKernel_bounded_on_NTZ :
    ∃ C : ℝ, ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ‖gaussianDefectEntireKernel_local ρ‖ ≤ C := by
  set Cprefac : ℝ := Real.pi * Real.sqrt (Real.pi / 2) with hCprefac_def
  have hCprefac_nn : 0 ≤ Cprefac := mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _)
  refine ⟨Cprefac * (Real.exp (1/8) + 2 * Real.exp (1/32) + 1), fun ρ hρ => ?_⟩
  unfold gaussianDefectEntireKernel_local
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCprefac_nn]
  apply mul_le_mul_of_nonneg_left _ hCprefac_nn
  obtain ⟨h_re_pos, h_re_lt_one, _⟩ := hρ
  -- ‖exp((ρ-1/2)²/k)‖ = exp(((Re ρ-1/2)² - (Im ρ)²)/k) ≤ exp((Re ρ-1/2)²/k) ≤ exp(1/(4k)).
  have h_re_diff_sq_le : (ρ.re - 1/2) ^ 2 ≤ 1/4 := by
    have h1 : -(1/2 : ℝ) < ρ.re - 1/2 := by linarith
    have h2 : ρ.re - 1/2 < 1/2 := by linarith
    have habs : |ρ.re - 1/2| < 1/2 := abs_lt.mpr ⟨h1, h2⟩
    nlinarith [abs_nonneg (ρ.re - 1/2), sq_abs (ρ.re - 1/2)]
  have h_im_sq_nn : 0 ≤ ρ.im ^ 2 := sq_nonneg _
  have h_sub_re : ((ρ - (1/2 : ℂ)) ^ 2).re = (ρ.re - 1/2)^2 - ρ.im^2 := by
    have h1 : (ρ - (1/2 : ℂ)).re = ρ.re - 1/2 := by simp
    have h2 : (ρ - (1/2 : ℂ)).im = ρ.im := by simp
    rw [sq, Complex.mul_re, h1, h2]; ring
  -- Bound exp /2.
  have h_exp2_norm : ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 2)‖ ≤ Real.exp (1/8) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have h_re : ((ρ - (1/2 : ℂ))^2 / 2).re = ((ρ.re - 1/2)^2 - ρ.im^2) / 2 := by
      have h_div_re : ((ρ - (1/2 : ℂ))^2 / 2).re = ((ρ - (1/2 : ℂ))^2).re / 2 := by
        simp [Complex.div_re, Complex.ofReal_re]
      rw [h_div_re, h_sub_re]
    rw [h_re]; linarith
  -- Bound exp /8.
  have h_exp8_norm : ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 8)‖ ≤ Real.exp (1/32) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have h_re : ((ρ - (1/2 : ℂ))^2 / 8).re = ((ρ.re - 1/2)^2 - ρ.im^2) / 8 := by
      have h_div_re : ((ρ - (1/2 : ℂ))^2 / 8).re = ((ρ - (1/2 : ℂ))^2).re / 8 := by
        simp [Complex.div_re, Complex.ofReal_re]
      rw [h_div_re, h_sub_re]
    rw [h_re]; linarith
  calc ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 2) -
        2 * Complex.exp ((ρ - (1/2 : ℂ))^2 / 8) + 1‖
      ≤ ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 2) -
            2 * Complex.exp ((ρ - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 2)‖ +
          ‖2 * Complex.exp ((ρ - (1/2 : ℂ))^2 / 8)‖ + ‖(1 : ℂ)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp (1/8) + (2 * Real.exp (1/32)) + 1 := by
        have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h_norm_one]
        have h_2_norm : ‖2 * Complex.exp ((ρ - (1/2 : ℂ))^2 / 8)‖ ≤
            2 * Real.exp (1/32) := by
          rw [norm_mul]
          have : ‖(2 : ℂ)‖ = 2 := by simp
          rw [this]
          have h_e2_nn : 0 ≤ ‖Complex.exp ((ρ - (1/2 : ℂ))^2 / 8)‖ := norm_nonneg _
          linarith [h_exp8_norm]
        linarith [h_exp2_norm]

/-- **Unconditional summability of the K-twisted multiplicity-weighted zero sum**
for `K = gaussianDefectEntireKernel_local`. Consumes
`WeilFinalAssemblyUnconditional.h_sum_unconditional` (un-twisted summability) and
the boundedness of `K` on the critical strip. -/
theorem K_pairTestMellin_zeroSum_summable_holds (β : ℝ) :
    K_pairTestMellin_zeroSum_summable
      gaussianDefectEntireKernel_local β
      (fun ρ : ℂ => by
        classical
        exact if hρ : ρ ∈ NontrivialZeros then
          Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
        else 0) := by
  unfold K_pairTestMellin_zeroSum_summable
  classical
  set n : ℂ → ℕ := fun ρ : ℂ =>
    if hρ : ρ ∈ NontrivialZeros then
      Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
    else 0
    with hn_def
  -- Un-twisted summability: Σ' (n ρ : ℂ) · M(β, ρ) summable.
  have h_un_twisted : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        Contour.pairTestMellin β ρ.val) :=
    ZD.WeilPositivity.FinalAssembly.h_sum_unconditional β
  -- Bound on K.
  obtain ⟨M_K, hM_K⟩ := gaussianDefectEntireKernel_bounded_on_NTZ
  -- Norm of K-twisted summand bounded by M_K * norm of un-twisted summand.
  -- Use Summable.of_norm + bdd_mul style domination.
  have h_norm_summable : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        ‖((n ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
          Contour.pairTestMellin β ρ.val‖) := by
    have h_un_twisted_norm : Summable
        (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
          ‖(((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
              : ℕ) : ℂ)) * Contour.pairTestMellin β ρ.val‖) :=
      h_un_twisted.norm
    have h_dominated : Summable
        (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
          M_K * ‖(((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
              : ℕ) : ℂ)) * Contour.pairTestMellin β ρ.val‖) :=
      h_un_twisted_norm.mul_left M_K
    refine h_dominated.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
    -- Pointwise: ‖n·K·M‖ = n · ‖K‖ · ‖M‖ ≤ n · M_K · ‖M‖ = M_K · ‖n·M‖.
    have hKbd : ‖gaussianDefectEntireKernel_local ρ.val‖ ≤ M_K := hM_K ρ.val ρ.property
    have hKnn : 0 ≤ ‖gaussianDefectEntireKernel_local ρ.val‖ := norm_nonneg _
    have h_choose_eq :
        (n ρ.val : ℕ) = Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) := by
      rw [hn_def]; simp [ρ.property]
    rw [norm_mul, norm_mul, norm_mul]
    rw [h_choose_eq]
    set m : ℕ := Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property)
      with hm_def
    have h_n_norm : ‖((m : ℕ) : ℂ)‖ = ((m : ℕ) : ℝ) := by simp
    rw [h_n_norm]
    have h_pm_nn : 0 ≤ ‖Contour.pairTestMellin β ρ.val‖ := norm_nonneg _
    have h_n_nn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    -- We want: n * ‖K‖ * ‖M‖ ≤ M_K * (n * ‖M‖).
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKbd h_n_nn) h_pm_nn,
      mul_nonneg h_n_nn hKnn]
  exact Summable.of_norm h_norm_summable

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_pairTestMellin_residue_sum_tendsto_of_summable
#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.K_pairTestMellin_zeroSum_summable_holds
