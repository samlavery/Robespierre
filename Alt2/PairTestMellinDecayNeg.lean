import Mathlib
import RequestProject.WeilHorizontalTailsDischarge
import RequestProject.WeilPairTestMellinExtend
import RequestProject.WeilArchKernelResidues

set_option maxHeartbeats 800000

/-!
# `pairTestMellin` decay extended to negative `σ` via IBP shift

This file packages the IBP-twice shift trick: for `σ ∈ [-1, 0]`, the function
`pairTestMellin β (σ + iT)` is defined by analytic continuation and lacks
direct decay; via `pairTestMellin_eq_ibp4_on_upper_strip`
(equivalently the IBP-twice version `pairTestMellin_ibp_twice` lifted by
analytic continuation), the function inherits quartic decay from the
shifted Mellin transform of the 4th derivative on the convergent
half-plane.

The hard work — analytic continuation of the IBP×4 identity — is done in
`HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended`, which
gives

```
∀ σ ∈ [-1, 2], ∀ T ≥ 2, ‖pairTestMellin β (σ+iT)‖ ≤ C / T^4.
```

This file packages the consequence in the form

```
∀ σ ∈ [-1+δ, 1-δ], ∀ |T| ≥ 1, ‖pairTestMellin β (σ+iT)‖ ≤ K / (1+T²)².
```

(quadratic decay in `1 + T²`, equivalent to `1 / T^4` up to a constant)
and uses conjugation symmetry to extend to negative `T`.

## Scope

This file delivers Step 1 of the requested two-step extension. Step 2
(the integral-decay statement `F_horizontal_edge_decay` for
`F = archKernel · pairTestMellin β` on `σ ∈ [-1+δ, 2]`) requires a
polynomial bound on `archKernel` uniform on `σ ∈ [-1+δ, 2]` for large
`T`. The codebase currently only has `gammaR_logDeriv_uniform_criticalStrip`
(σ ∈ (0, 1) only); extending to `σ ∈ [-1+δ, 0]` and `σ ∈ [1, 2]` requires
new Stirling-style work on the reflected Γℝ'/Γℝ that is not yet in
mathlib or this project. Conditional discharge would require named
targets (e.g. `leftOfCriticalStrip_target`, `rightOfCriticalStrip_target`
in `WeilFinalAssemblyUnconditional`) that themselves remain open. Per
project rules ("No new conditional work"), Step 2 is left as a separate
target to be discharged once those archKernel bounds are proved.
-/

noncomputable section

open Complex Set Filter MeasureTheory Real

namespace ZD
namespace WeilPositivity
namespace PairTestMellinDecayNeg

open Contour HorizontalTailsDischarge

/-! ### Conjugate symmetry of `pairTestMellin β` -/

/-- `pairTestMellin β` has conjugation symmetry
`‖pairTestMellin β (σ + iT)‖ = ‖pairTestMellin β (σ - iT)‖` for any
real `σ, T`, since `pair_cosh_gauss_test β` is real-valued. -/
private theorem pairTestMellin_norm_conj_symm (β : ℝ) (σ T : ℝ) :
    ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ =
      ‖pairTestMellin β ((σ : ℂ) + ((-T) : ℂ) * I)‖ := by
  simp only [pairTestMellin, mellin]
  have h_eq : ∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I - 1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ) =
      starRingEnd ℂ (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ ((σ : ℂ) + ((-T) : ℂ) * I - 1) •
          ((pair_cosh_gauss_test β t : ℝ) : ℂ)) := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem
        measurableSet_Ioi (fun t (ht : (0:ℝ) < t) => ?_))]
    · exact integral_conj
    · simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
      congr 1
      rw [show ((σ : ℂ) + (T : ℂ) * I - 1) =
          starRingEnd ℂ ((σ : ℂ) + ((-T) : ℂ) * I - 1) from by
        simp only [map_add, map_sub, map_mul, map_neg,
                   Complex.conj_ofReal, Complex.conj_I, map_one]; ring]
      rw [Complex.cpow_conj _ _ (by
        rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne)]
      rw [Complex.conj_ofReal]
  rw [h_eq, RCLike.norm_conj]

/-! ### Joint continuity of `pairTestMellin β` on the strip `Re s > -4` -/

/-- `(σ, T) ↦ pairTestMellin β (σ + iT)` is continuous on the open
half-plane `{p | -4 < p.1}` (`σ > -4`). -/
private theorem pairTestMellin_continuous_on_re_gt_neg_four (β : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
        pairTestMellin β ((p.1 : ℂ) + (p.2 : ℂ) * I))
      {p : ℝ × ℝ | -4 < p.1} := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have h_diff : DifferentiableAt ℂ (pairTestMellin β)
      ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    apply pairTestMellin_differentiableAt_re_gt_neg_four
    simp; exact hp
  have h_cont_inner : Continuous (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I) := by
    fun_prop
  exact ContinuousAt.comp (g := pairTestMellin β)
    (f := fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * I)
    h_diff.continuousAt h_cont_inner.continuousAt

/-- Compact bound for `‖pairTestMellin β (σ + iT)‖` on the box
`[-1, 1] × [-2, 2]` (in `(σ, T)`). -/
private theorem pairTestMellin_bound_on_compact_box (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ T : ℝ, σ ∈ Set.Icc (-1 : ℝ) 1 →
      T ∈ Set.Icc (-2 : ℝ) 2 →
        ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ M := by
  set K : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2 with hK
  have hK_compact : IsCompact K :=
    (isCompact_Icc).prod (isCompact_Icc)
  have hK_subset : K ⊆ {p : ℝ × ℝ | -4 < p.1} := by
    intro p hp; show -4 < p.1
    have := hp.1.1; linarith
  have h_cont : ContinuousOn (fun p : ℝ × ℝ =>
      pairTestMellin β ((p.1 : ℂ) + (p.2 : ℂ) * I)) K :=
    (pairTestMellin_continuous_on_re_gt_neg_four β).mono hK_subset
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn hK_compact h_cont.norm
  refine ⟨M, ?_, ?_⟩
  · -- M ≥ ‖pair (0+0i)‖ ≥ 0.
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ K := by
      refine ⟨?_, ?_⟩ <;> · constructor <;> norm_num
    have hbd := hM ((0:ℝ), (0:ℝ)) h0
    have hnn : 0 ≤ ‖pairTestMellin β (((0:ℝ):ℂ) + ((0:ℝ):ℂ) * I)‖ :=
      norm_nonneg _
    have hbd' : ‖‖pairTestMellin β (((0:ℝ):ℂ) + ((0:ℝ):ℂ) * I)‖‖ ≤ M := hbd
    rw [Real.norm_of_nonneg hnn] at hbd'
    linarith
  · intro σ T hσ hT
    have hp_mem : (σ, T) ∈ K := ⟨hσ, hT⟩
    have hbd := hM (σ, T) hp_mem
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at hbd

/-! ### Main theorem: `pairTestMellin` decay on `σ ∈ [-1+δ, 1-δ]` -/

/-- **`pairTestMellin` decay extended to the strip `σ ∈ [-1+δ, 1-δ]` via
the IBP-twice shift trick.**

For any `δ > 0`, there exists `K` such that for all `σ ∈ [-1+δ, 1-δ]` and
all `T` with `|T| ≥ 1`,
`‖pairTestMellin β (σ + iT)‖ ≤ K / (1 + T²)²`.

The bound holds via:
- `HorizontalTailsDischarge.pairTestMellin_quartic_bound_extended` for
  `|T| ≥ 2` (which itself uses the analytically-continued IBP×4 identity
  to shift the Mellin transform to the convergent half-plane);
- compactness on `1 ≤ |T| ≤ 2` (continuity of `pairTestMellin` on the
  strip);
- conjugation symmetry to handle negative `T`.

This is the IBP-shift extension promised by the math: for `σ < 0`, the
direct integral diverges, but `pairTestMellin β s = (1/(s(s+1))) ·
M[d²pcgt](s+2)` continues analytically; for `σ ∈ [-1+δ, 0]`,
`Re(s+2) ∈ [1+δ, 2]` is convergent, and the quartic-decay bound transfers
down. -/
theorem pairTestMellin_decay_on_strip_neg (β : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ σ : ℝ, σ ∈ Set.Icc (-1 + δ) (1 - δ) → ∀ T : ℝ, |T| ≥ 1 →
      ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ K / (1 + T^2)^2 := by
  obtain ⟨C, hC_nn, hC_bd⟩ := pairTestMellin_quartic_bound_extended β
  obtain ⟨M, hM_nn, hM_bd⟩ := pairTestMellin_bound_on_compact_box β
  refine ⟨max (4 * C) (25 * M), le_max_of_le_left (by positivity), ?_⟩
  intro σ hσ T hT_abs_ge
  have h_one_plus_T_sq_pos : (0 : ℝ) < 1 + T^2 := by positivity
  have h_denom_pos : (0 : ℝ) < (1 + T^2)^2 := by positivity
  have hσ_in_neg1_2 : σ ∈ Set.Icc (-1 : ℝ) 2 :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  rcases le_or_gt 2 |T| with hT_ge2 | hT_lt2
  · -- |T| ≥ 2: use quartic bound (with conjugation if T < 0).
    have h_pair_bd : ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C / T^4 := by
      rcases le_or_gt 0 T with hT_nn | hT_neg
      · have hT_eq : |T| = T := abs_of_nonneg hT_nn
        have hT_ge2' : 2 ≤ T := by rw [← hT_eq]; exact hT_ge2
        exact hC_bd σ hσ_in_neg1_2 T hT_ge2'
      · have hT_eq : |T| = -T := abs_of_neg hT_neg
        have hnegT_ge2 : 2 ≤ -T := by rw [← hT_eq]; exact hT_ge2
        have h := hC_bd σ hσ_in_neg1_2 (-T) hnegT_ge2
        -- Normalize ↑(-T) to -↑T in `h`.
        have h' : ‖pairTestMellin β ((σ : ℂ) + (-(T : ℂ)) * I)‖ ≤ C / (-T) ^ 4 := by
          have heq : ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) = ((σ : ℂ) + (-(T : ℂ)) * I) := by
            push_cast; ring
          rw [heq] at h; exact h
        -- Conjugation symmetry: ‖pair (σ + T·I)‖ = ‖pair (σ + (-T)·I)‖
        have h_sym := pairTestMellin_norm_conj_symm β σ T
        rw [h_sym]
        have h_T4 : T^4 = (-T)^4 := by ring
        rw [h_T4]
        exact h'
    have hT_sq_ge_one : 1 ≤ T^2 := by
      have hT_abs_sq : T^2 = |T|^2 := (sq_abs T).symm
      rw [hT_abs_sq]
      have h1le : (1:ℝ) ≤ |T| := hT_abs_ge
      nlinarith [abs_nonneg T]
    have h_T4_pos : (0 : ℝ) < T^4 := by
      have : 0 < T^2 := by linarith
      nlinarith
    have h_one_plus_T_sq_sq_le : (1 + T^2)^2 ≤ 4 * T^4 := by
      nlinarith [sq_nonneg (1 + T^2), hT_sq_ge_one, sq_nonneg T]
    have h_4C_T4 : C / T^4 ≤ (4 * C) / (1 + T^2)^2 := by
      rw [div_le_div_iff₀ h_T4_pos h_denom_pos]
      nlinarith [hC_nn, h_one_plus_T_sq_sq_le]
    calc ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖
        ≤ C / T^4 := h_pair_bd
      _ ≤ (4 * C) / (1 + T^2)^2 := h_4C_T4
      _ ≤ max (4 * C) (25 * M) / (1 + T^2)^2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) h_denom_pos.le
  · -- 1 ≤ |T| < 2: use compact bound M.
    have hT_in : T ∈ Set.Icc (-2 : ℝ) 2 := by
      have hT_le := le_of_lt hT_lt2
      refine ⟨?_, ?_⟩
      · linarith [neg_abs_le T]
      · linarith [le_abs_self T]
    have hσ_in_neg1_1 : σ ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have h_pair_bd : ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ M :=
      hM_bd σ T hσ_in_neg1_1 hT_in
    have h_T_sq_le : T^2 ≤ 4 := by
      have hT_le := le_of_lt hT_lt2
      have hT_abs_sq : T^2 = |T|^2 := (sq_abs T).symm
      rw [hT_abs_sq]; nlinarith [abs_nonneg T]
    have h_one_plus_T_sq_sq_le : (1 + T^2)^2 ≤ 25 := by
      nlinarith [sq_nonneg (1 + T^2)]
    have h_25M : M ≤ (25 * M) / (1 + T^2)^2 := by
      rw [le_div_iff₀ h_denom_pos]
      have h_25M : (1 + T^2)^2 * M ≤ 25 * M :=
        mul_le_mul_of_nonneg_right h_one_plus_T_sq_sq_le hM_nn
      linarith
    calc ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖
        ≤ M := h_pair_bd
      _ ≤ (25 * M) / (1 + T^2)^2 := h_25M
      _ ≤ max (4 * C) (25 * M) / (1 + T^2)^2 :=
          div_le_div_of_nonneg_right (le_max_right _ _) h_denom_pos.le

#print axioms pairTestMellin_decay_on_strip_neg

end PairTestMellinDecayNeg
end WeilPositivity
end ZD
