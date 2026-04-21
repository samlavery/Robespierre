import Mathlib
import RequestProject.DigammaVerticalBound
import RequestProject.WeilArchPrimeIdentity
import RequestProject.WeilPairIBP
import RequestProject.WeilDigammaReduction

/-!
# AP-1 Adapter: arch operator polynomial bound at σ₀ = 2

Discharges `archOperator_polynomial_bound_target 2` unconditionally using
Aristotle's `Complex.digamma_vertical_log_bound` +
`gammaℝ_logDeriv_digamma_form` + digamma reflection.

## Strategy

For `s = 2 + it`:
* `Gammaℝ'/Gammaℝ(s) = -(log π)/2 + (1/2)·ψ(1 + it/2)`. `Re(1 + it/2) = 1 > 0`,
  so Aristotle gives `‖ψ(1 + it/2)‖ ≤ C log(1 + |t/2|)` for `|t/2| ≥ 1`.
* `Gammaℝ'/Gammaℝ(1-s) = -(log π)/2 + (1/2)·ψ(-1/2 - it/2)`. `Re = -1/2 < 0`,
  so Aristotle doesn't apply. Use **digamma reflection**
  `ψ(z) = ψ(1-z) - π·cot(π·z)` at `z = -1/2 - it/2`:
  `ψ(-1/2 - it/2) = ψ(3/2 + it/2) - π·cot(-π/2 - πit/2)`.
* `cot(-π/2 - πit/2) = i·tanh(πt/2)`, bounded by 1.
* `ψ(3/2 + it/2)` has `Re = 3/2 > 0`, Aristotle applies.

Result: `‖arch(2+it)‖ = O(log(1+|t|))`, dominated by linear `(1+|t|)`,
so `archOperator_polynomial_bound_target 2` holds with `N = 1`.

## Delivered

* `archOperator_polynomial_bound_at_two` — discharges the target for σ₀ = 2.
* `archIntegrand_integrable_at_two` — AP-1 closure for σ₀ = 2.
* `reflectedPrimeIntegrand_integrable_at_two` — AP-3 closure for σ₀ = 2.
* `weilArchPrimeIdentityTarget_corrected_at_two` — AP-4 closure for σ₀ = 2.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real

noncomputable section

namespace ZD.WeilPositivity.Contour

/-- **Log bound for `ψ` on the right half-plane `Re s > 0`**, restated from
Aristotle's `Complex.digamma_vertical_log_bound`. Bounds `‖ψ(σ+it)‖` for all
`t ∈ ℝ` (including `|t| < 1` via constant), at rate `log(1+|t|) + const`. -/
theorem digamma_log_bound_all_t (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * (1 + Real.log (1 + |t|)) := by
  -- Aristotle gives the bound for |t| ≥ 1. Need to extend to all t via continuity.
  obtain ⟨C₀, hC₀_pos, hC₀_bd⟩ := Complex.digamma_vertical_log_bound σ hσ
  -- For |t| < 1, use continuity on the compact [-1, 1].
  -- The function `t ↦ ψ(σ+it)` is continuous on ℝ (since Re(σ+it) = σ > 0 ≠ 0).
  have h_diffAt : ∀ t : ℝ,
      DifferentiableAt ℂ Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    refine Complex.differentiableAt_Gamma _ ?_
    intro m heq
    have h_re : ((σ : ℂ) + (t : ℂ) * Complex.I).re = -(m : ℝ) := by
      rw [heq]; simp
    simp at h_re
    have : σ = -(m : ℝ) := h_re
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h_ne_zero : ∀ t : ℝ,
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    apply Complex.Gamma_ne_zero
    intro m heq
    have h_re : ((σ : ℂ) + (t : ℂ) * Complex.I).re = -(m : ℝ) := by
      rw [heq]; simp
    simp at h_re
    have : σ = -(m : ℝ) := h_re
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h_cont : Continuous (fun t : ℝ =>
      deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have h_s_cont : Continuous (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_Γ_diffOn : DifferentiableOn ℂ Complex.Gamma {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
      intro z hz
      exact (Complex.differentiableAt_Gamma _ hz).differentiableWithinAt
    have h_U_open : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := nonpole_isOpen
    have h_derivΓ_cont : Continuous (fun t : ℝ =>
        deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      have h_derivΓ_diffOn : DifferentiableOn ℂ (deriv Complex.Gamma)
          {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := h_Γ_diffOn.deriv h_U_open
      have : Continuous ((deriv Complex.Gamma) ∘ (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
        apply ContinuousOn.comp_continuous (h_derivΓ_diffOn.continuousOn) h_s_cont
        intro t m heq
        have h_re : ((σ : ℂ) + (t : ℂ) * Complex.I).re = -(m : ℝ) := by
          rw [heq]; simp
        simp at h_re
        linarith [Nat.cast_nonneg m (α := ℝ)]
      exact this
    have h_Γ_cont : Continuous (fun t : ℝ =>
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      have : Continuous (Complex.Gamma ∘ (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
        apply ContinuousOn.comp_continuous (h_Γ_diffOn.continuousOn) h_s_cont
        intro t m heq
        have h_re : ((σ : ℂ) + (t : ℂ) * Complex.I).re = -(m : ℝ) := by
          rw [heq]; simp
        simp at h_re
        linarith [Nat.cast_nonneg m (α := ℝ)]
      exact this
    exact h_derivΓ_cont.div h_Γ_cont (fun t => h_ne_zero t)
  -- Compact bound on [-1, 1].
  have h_compact : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have h_cont_on : ContinuousOn (fun t : ℝ =>
      ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) (Set.Icc (-1 : ℝ) 1) :=
    h_cont.norm.continuousOn
  have hBdd := h_compact.bddAbove_image h_cont_on
  set M : ℝ := sSup ((fun t : ℝ => ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) '' Set.Icc (-1 : ℝ) 1)
  have hM_nn : 0 ≤ M := by
    have h0 : ‖deriv Complex.Gamma ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ ≤ M :=
      le_csSup hBdd (Set.mem_image_of_mem _ (by simp : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1))
    exact le_trans (norm_nonneg _) h0
  -- Combine: take C = max(C₀, M).
  refine ⟨max C₀ M, le_max_of_le_left hC₀_pos.le, fun t => ?_⟩
  by_cases ht : 1 ≤ |t|
  · -- Use Aristotle bound.
    have h_Aris := hC₀_bd t ht
    have h_log_nn : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by have := abs_nonneg t; linarith)
    calc ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
            Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C₀ * Real.log (1 + |t|) := h_Aris
      _ ≤ max C₀ M * Real.log (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h_log_nn
      _ ≤ max C₀ M * (1 + Real.log (1 + |t|)) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · exact le_max_of_le_left hC₀_pos.le
  · -- |t| < 1: use compact bound M.
    rw [not_le] at ht
    have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · have := abs_lt.mp ht
        linarith [this.1]
      · have := abs_lt.mp ht
        linarith [this.2]
    have h_M_bd : ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M := by
      apply le_csSup hBdd
      exact Set.mem_image_of_mem _ ht_mem
    calc ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
            Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ M := h_M_bd
      _ ≤ max C₀ M := le_max_right _ _
      _ = max C₀ M * 1 := by ring
      _ ≤ max C₀ M * (1 + Real.log (1 + |t|)) := by
          apply mul_le_mul_of_nonneg_left
          · have : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by have := abs_nonneg t; linarith)
            linarith
          · exact le_max_of_le_left hC₀_pos.le

#print axioms digamma_log_bound_all_t

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helper: log(1+|t|) ≤ 2·(1+|t|)^(1/2)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`log(1+|t|) ≤ 2·(1+|t|)^(1/2)`**, from `Real.log_le_rpow_div` at `ε = 1/2`. -/
private lemma log_one_add_abs_le_two_rpow_half (t : ℝ) :
    Real.log (1 + |t|) ≤ 2 * (1 + |t|)^((1:ℝ)/2) := by
  have h_nn : (0:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h_half_pos : (0:ℝ) < (1:ℝ)/2 := by norm_num
  have h_log_le := Real.log_le_rpow_div h_nn h_half_pos
  -- log(1+|t|) ≤ (1+|t|)^(1/2) / (1/2)
  have h_div_eq : (1 + |t|)^((1:ℝ)/2) / ((1:ℝ)/2) = 2 * (1 + |t|)^((1:ℝ)/2) := by
    field_simp
  linarith [h_log_le, h_div_eq.le]

/-- **One plus log bound is at most a half-power**: combining
`1 ≤ (1+|t|)^(1/2)` with the log bound gives a clean single-power majorant. -/
private lemma one_add_log_le_three_rpow_half (t : ℝ) :
    1 + Real.log (1 + |t|) ≤ 3 * (1 + |t|)^((1:ℝ)/2) := by
  have h_base_ge_one : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h_rpow_ge_one : (1:ℝ) ≤ (1 + |t|)^((1:ℝ)/2) := by
    have h1 : (1:ℝ)^((1:ℝ)/2) = 1 := Real.one_rpow _
    have h2 : (1:ℝ)^((1:ℝ)/2) ≤ (1 + |t|)^((1:ℝ)/2) :=
      Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h_base_ge_one (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  have h_log := log_one_add_abs_le_two_rpow_half t
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Single-side Γℝ log-derivative bound at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Γℝ(2+tI) ≠ 0** for every real `t`. Follows from `Gammaℝ_ne_zero_of_re_pos`. -/
private lemma gammaR_ne_zero_two (t : ℝ) :
    ((2 : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  show (0:ℝ) < ((2 : ℂ) + (t : ℂ) * I).re
  simp

private lemma two_plus_tI_ne_neg_two_nat (t : ℝ) :
    ∀ n : ℕ, ((2 : ℂ) + (t : ℂ) * I) ≠ -(2 * (n : ℂ)) := by
  intro n h
  have hre : ((2 : ℂ) + (t : ℂ) * I).re = (-(2 * (n : ℂ))).re := by rw [h]
  simp at hre
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **Single-side log bound at σ = 2.** For every `t : ℝ`,
`‖Γℝ'/Γℝ(2+tI)‖ ≤ C · (1 + log(1+|t|))` for some constant `C ≥ 0`.

Proof: `Γℝ'/Γℝ(s) = −(log π)/2 + (1/2)·ψ(s/2)` via `gammaℝ_logDeriv_digamma_form`
at `s = 2+tI`, where `s/2 = 1 + (t/2)I` has `Re = 1 > 0`. Apply
`digamma_log_bound_all_t 1` and use `log(1+|t/2|) ≤ log(1+|t|)`. -/
theorem gammaR_logDeriv_log_bound_at_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
          ((2 : ℂ) + (t : ℂ) * I).Gammaℝ‖ ≤ C * (1 + Real.log (1 + |t|)) := by
  obtain ⟨C_d, hC_d_nn, hC_d_bd⟩ := digamma_log_bound_all_t 1 (by norm_num : (0:ℝ) < 1)
  refine ⟨|Real.log Real.pi| / 2 + C_d / 2, by positivity, fun t => ?_⟩
  -- Apply gammaℝ_logDeriv_digamma_form at s = 2+tI.
  have hGammaℝ_ne : ((2 : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := gammaR_ne_zero_two t
  have hne2n : ∀ n : ℕ, ((2 : ℂ) + (t : ℂ) * I) ≠ -(2 * (n : ℂ)) :=
    two_plus_tI_ne_neg_two_nat t
  rw [gammaℝ_logDeriv_digamma_form _ hGammaℝ_ne hne2n]
  -- Rewrite s/2 = 1 + (t/2)I.
  have h_half_eq : ((2 : ℂ) + (t : ℂ) * I) / 2 = (1 : ℂ) + ((t/2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h_half_eq]
  -- Apply Aristotle's digamma bound at σ = 1, t' = t/2.
  have h_dig := hC_d_bd (t/2)
  -- ‖−(log π)/2 + (1/2)·ψ‖ ≤ (log π)/2 + (1/2)·‖ψ‖.
  have h_triangle :
      ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          (1 / 2 : ℂ) *
            (deriv Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
              Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ ≤
        ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ := norm_add_le _ _
  -- Bound the two pieces.
  have h_logpi_bd : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div]
    rw [show ‖-(Complex.log (Real.pi : ℂ))‖ = ‖Complex.log (Real.pi : ℂ)‖ from norm_neg _]
    rw [show (Complex.log (Real.pi : ℂ)) = ((Real.log Real.pi : ℝ) : ℂ) by
      have := Complex.ofReal_log Real.pi_pos.le; exact this.symm]
    rw [Complex.norm_real]
    simp
  have h_scaled_bd :
      ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ ≤
        (1/2) * (C_d * (1 + Real.log (1 + |t/2|))) := by
    rw [norm_mul]
    have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real]; norm_num
    rw [h_half_norm]
    exact mul_le_mul_of_nonneg_left h_dig (by norm_num)
  -- log(1+|t/2|) ≤ log(1+|t|).
  have h_abs_half : |t/2| ≤ |t| := by
    rw [abs_div]
    have : |t| / |(2:ℝ)| ≤ |t| := by
      rw [show |(2:ℝ)| = 2 from abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_nonneg t; linarith
    exact this
  have h_log_mono : Real.log (1 + |t/2|) ≤ Real.log (1 + |t|) := by
    apply Real.log_le_log
    · linarith [abs_nonneg (t/2)]
    · linarith
  -- Assemble.
  calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          (1 / 2 : ℂ) *
            (deriv Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
              Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖
      ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma ((1 : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ := h_triangle
    _ ≤ |Real.log Real.pi| / 2 + (1/2) * (C_d * (1 + Real.log (1 + |t/2|))) := by
        rw [h_logpi_bd]; linarith [h_scaled_bd]
    _ ≤ |Real.log Real.pi| / 2 + (1/2) * (C_d * (1 + Real.log (1 + |t|))) := by
        have : C_d * (1 + Real.log (1 + |t/2|)) ≤ C_d * (1 + Real.log (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC_d_nn
        linarith
    _ ≤ (|Real.log Real.pi| / 2 + C_d / 2) * (1 + Real.log (1 + |t|)) := by
        have h_log_nn : (0:ℝ) ≤ Real.log (1 + |t|) :=
          Real.log_nonneg (by linarith [abs_nonneg t])
        have h_logpi_nn : (0:ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
        nlinarith [h_log_nn, h_logpi_nn, hC_d_nn]

#print axioms gammaR_logDeriv_log_bound_at_two

-- ═══════════════════════════════════════════════════════════════════════════
-- § Digamma shift identity ψ(s) = ψ(s+1) − 1/s
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Derivative recurrence.** Differentiating `Γ(s+1) = s · Γ(s)` gives
`deriv Γ (s+1) = Γ s + s · deriv Γ s`, for `s` not a non-positive integer. -/
private lemma Gamma_deriv_recurrence {s : ℂ}
    (hs_ne_neg : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    deriv Complex.Gamma (s + 1) = Complex.Gamma s + s * deriv Complex.Gamma s := by
  have hs_ne_zero : s ≠ 0 := fun h => hs_ne_neg 0 (by rw [h]; simp)
  have hΓs_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ hs_ne_neg
  have hs1_ne_neg : ∀ m : ℕ, s + 1 ≠ -(m : ℂ) := by
    intro m h
    apply hs_ne_neg (m + 1)
    have : s = -((m : ℂ) + 1) := by linear_combination h
    rw [this]; push_cast; ring
  have hΓs1_diff : DifferentiableAt ℂ Complex.Gamma (s + 1) :=
    Complex.differentiableAt_Gamma _ hs1_ne_neg
  -- Γ(z+1) = z · Γ z eventually in nhds s.
  have h_eq : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[nhds s]
              (fun z : ℂ => z * Complex.Gamma z) := by
    have h_open : ∀ᶠ z in nhds s, z ≠ 0 := isOpen_compl_singleton.mem_nhds hs_ne_zero
    filter_upwards [h_open] with z hz using Complex.Gamma_add_one z hz
  -- Product rule on z · Γ z.
  have h_rhs_hd : HasDerivAt (fun z : ℂ => z * Complex.Gamma z)
      (1 * Complex.Gamma s + s * deriv Complex.Gamma s) s :=
    (hasDerivAt_id s).mul hΓs_diff.hasDerivAt
  -- Transport to Γ(z+1) via eventual equality.
  have h_lhs_hd : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (1 * Complex.Gamma s + s * deriv Complex.Gamma s) s :=
    h_eq.symm.hasDerivAt_iff.mp h_rhs_hd
  -- Chain rule directly on Γ(z+1).
  have h_inner : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
  have h_chain : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (deriv Complex.Gamma (s + 1)) s := by
    have := hΓs1_diff.hasDerivAt.comp s h_inner
    simpa using this
  -- Uniqueness of derivative.
  have h_eq_deriv : deriv Complex.Gamma (s + 1) =
      1 * Complex.Gamma s + s * deriv Complex.Gamma s := h_chain.unique h_lhs_hd
  linear_combination h_eq_deriv

/-- **Digamma shift identity.** `ψ(s) = ψ(s+1) − 1/s` for `s` not a non-positive
integer. Derived from the derivative recurrence above. -/
private lemma digamma_shift_eq {s : ℂ}
    (hs_ne_neg : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    deriv Complex.Gamma s / Complex.Gamma s =
      deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) - 1 / s := by
  have hs_ne_zero : s ≠ 0 := fun h => hs_ne_neg 0 (by rw [h]; simp)
  have hΓs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs_ne_neg
  have h_recurrence : Complex.Gamma (s + 1) = s * Complex.Gamma s :=
    Complex.Gamma_add_one s hs_ne_zero
  have h_deriv_recurrence := Gamma_deriv_recurrence hs_ne_neg
  rw [h_recurrence, h_deriv_recurrence]
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reflected-side Γℝ log-derivative bound at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Γℝ(−1−tI) ≠ 0** for every real `t`. Follows from `Gammaℝ_eq_zero_iff`:
the only zeros of `Γℝ` are at `s = −(2n)` for `n : ℕ`, and `−1 − tI ≠ −(2n)`
since the real parts disagree (gives `2n = 1`, impossible in ℕ). -/
private lemma gammaR_ne_zero_reflected_two (t : ℝ) :
    (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : (1 - ((2 : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [hn]
  simp at hre
  -- hre : 1 - 2 = -(2·n), i.e., -1 = -2n, i.e., 2n = 1. Impossible in ℕ.
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
  omega

private lemma one_sub_two_plus_tI_ne_neg_two_nat (t : ℝ) :
    ∀ n : ℕ, (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ -(2 * (n : ℂ)) := by
  intro n h
  have hre : (1 - ((2 : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [h]
  simp at hre
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
  omega

/-- The half-point `(-1-tI)/2 = -1/2 - (t/2)·I` is not a non-positive integer.
Its real part is `-1/2`, so `-1/2 = -n` forces `n = 1/2`, impossible in ℕ. -/
private lemma neg_half_minus_half_tI_ne_neg_nat (t : ℝ) :
    ∀ n : ℕ, (-(1:ℂ)/2 + -((t/2:ℝ) : ℂ) * I) ≠ -(n : ℂ) := by
  intro n h
  have hre : (-(1:ℂ)/2 + -((t/2:ℝ) : ℂ) * I).re = (-(n : ℂ)).re := by rw [h]
  simp at hre
  -- hre : -1/2 = -n. So 2n = 1.
  have h_int : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 1)
  omega

/-- The shifted half-point `1/2 - (t/2)·I` is not a non-positive integer
(its real part is `1/2 > 0`). -/
private lemma half_minus_half_tI_ne_neg_nat (t : ℝ) :
    ∀ n : ℕ, ((1/2:ℂ) + -((t/2:ℝ) : ℂ) * I) ≠ -(n : ℂ) := by
  intro n h
  have hre : ((1/2:ℂ) + -((t/2:ℝ) : ℂ) * I).re = (-(n : ℂ)).re := by rw [h]
  simp at hre
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Norm lower bound `‖(-1/2) - (t/2)·I‖ ≥ 1/2` for every real `t`. -/
private lemma norm_neg_half_minus_half_tI_ge (t : ℝ) :
    (1/2 : ℝ) ≤ ‖(-(1:ℂ)/2 + -((t/2 : ℝ) : ℂ) * I)‖ := by
  -- Rewrite in form x + y·I with real x = -1/2, y = -t/2.
  have h_rewrite : (-(1:ℂ)/2 + -((t/2 : ℝ) : ℂ) * I) =
      ((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_rewrite]
  have h_normSq : Complex.normSq (((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I) =
      ((-1/2 : ℝ))^2 + ((-t/2 : ℝ))^2 := Complex.normSq_add_mul_I _ _
  have h_normSq_val : Complex.normSq (((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I) =
      (1 + t^2)/4 := by rw [h_normSq]; ring
  have h_sq_eq : ‖((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖^2 = (1 + t^2)/4 := by
    rw [← Complex.normSq_eq_norm_sq]; exact h_normSq_val
  have h_ge_quarter : ((1:ℝ)/2)^2 ≤
      ‖((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖^2 := by
    rw [h_sq_eq]
    have := sq_nonneg t; nlinarith
  have h_norm_nn : (0:ℝ) ≤ ‖((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖ := norm_nonneg _
  nlinarith [sq_nonneg ((1:ℝ)/2 - ‖((-1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖), h_norm_nn]

/-- **Reflected-side log bound at σ = 2.** For every `t : ℝ`,
`‖Γℝ'/Γℝ(−1−tI)‖ ≤ C · (1 + log(1+|t|))` for some constant `C ≥ 0`.

Proof: `Γℝ'/Γℝ(−1−tI) = −(log π)/2 + (1/2)·ψ(−1/2 − tI/2)`. Use the digamma
shift `ψ(s) = ψ(s+1) − 1/s` at `s = −1/2 − tI/2` (whose `s + 1 = 1/2 − tI/2`
has `Re = 1/2 > 0`). Bound `ψ(1/2 − tI/2)` via `digamma_log_bound_all_t (1/2)`.
Bound `|1/s|` by `2` since `|s| = √(1+t²)/2 ≥ 1/2`. -/
theorem gammaR_logDeriv_reflected_log_bound_at_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ‖ ≤ C * (1 + Real.log (1 + |t|)) := by
  obtain ⟨C_d, hC_d_nn, hC_d_bd⟩ := digamma_log_bound_all_t (1/2) (by norm_num : (0:ℝ) < 1/2)
  -- Constant: |log π|/2 + C_d/2 + 1.
  refine ⟨|Real.log Real.pi| / 2 + C_d / 2 + 1, by positivity, fun t => ?_⟩
  -- Apply gammaℝ_logDeriv_digamma_form at s = 1 - (2+tI).
  have hGammaℝ_ne := gammaR_ne_zero_reflected_two t
  have hne2n := one_sub_two_plus_tI_ne_neg_two_nat t
  rw [gammaℝ_logDeriv_digamma_form _ hGammaℝ_ne hne2n]
  -- s/2 = -1/2 - (t/2)·I.
  have h_half_eq : (1 - ((2 : ℂ) + (t : ℂ) * I)) / 2 =
      -(1:ℂ)/2 + -((t/2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h_half_eq]
  -- Shift: ψ(s) = ψ(s+1) - 1/s at s = -1/2 - (t/2)I.
  have h_shift_hypo : ∀ n : ℕ, (-(1:ℂ)/2 + -((t/2:ℝ) : ℂ) * I) ≠ -(n : ℂ) :=
    neg_half_minus_half_tI_ne_neg_nat t
  rw [digamma_shift_eq h_shift_hypo]
  -- (s+1) = 1/2 - (t/2)I. Convert to the form that matches digamma_log_bound_all_t.
  have h_s_plus_one : (-(1:ℂ)/2 + -((t/2:ℝ) : ℂ) * I) + 1 =
      ((1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_s_plus_one]
  -- Apply digamma bound at σ=1/2, t'=-t/2.
  have h_dig := hC_d_bd (-t/2)
  -- Abbreviations.
  set u : ℂ := (-(1:ℂ)/2 + -((t/2:ℝ) : ℂ) * I) with hu_def
  set ψ_arg : ℂ := ((1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I with hψ_arg
  set ψ_val : ℂ := deriv Complex.Gamma ψ_arg / Complex.Gamma ψ_arg with hψ_val
  -- Triangle inequality bound.
  have h_triangle :
      ‖-(Complex.log (Real.pi : ℂ)) / 2 + (1/2 : ℂ) * (ψ_val - 1 / u)‖ ≤
        ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1/2 : ℂ) * (ψ_val - 1 / u)‖ := norm_add_le _ _
  have h_tri2 : ‖(1/2 : ℂ) * (ψ_val - 1/u)‖ ≤
      ‖(1/2 : ℂ)‖ * (‖ψ_val‖ + ‖1/u‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  -- Constant bounds.
  have h_logpi_bd : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div]
    rw [show ‖-(Complex.log (Real.pi : ℂ))‖ = ‖Complex.log (Real.pi : ℂ)‖ from norm_neg _]
    rw [show (Complex.log (Real.pi : ℂ)) = ((Real.log Real.pi : ℝ) : ℂ) by
      have := Complex.ofReal_log Real.pi_pos.le; exact this.symm]
    rw [Complex.norm_real]
    simp
  have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real]; norm_num
  -- ‖1/u‖ ≤ 2.
  have h_u_norm_ge : (1/2 : ℝ) ≤ ‖u‖ := by
    simp only [hu_def]
    exact norm_neg_half_minus_half_tI_ge t
  have h_u_ne_zero : u ≠ 0 := by
    intro hu
    have : ‖u‖ = 0 := by rw [hu]; exact norm_zero
    linarith
  have h_inv_u_bd : ‖1 / u‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have h_pos : (0:ℝ) < ‖u‖ := by linarith
    have h_one_div : (1 : ℝ) / ‖u‖ ≤ 1 / (1/2) :=
      one_div_le_one_div_of_le (by norm_num) h_u_norm_ge
    have h_half_inv : (1:ℝ) / (1/2) = 2 := by norm_num
    linarith
  -- ‖ψ_val‖ ≤ C_d · (1 + log(1+|-t/2|)) ≤ C_d · (1 + log(1+|t|)).
  have h_abs_neg_half : |(-t:ℝ)/2| ≤ |t| := by
    rw [show (-t:ℝ)/2 = -(t/2) from by ring]
    rw [abs_neg, abs_div]
    have : |t| / |(2:ℝ)| ≤ |t| := by
      rw [show |(2:ℝ)| = 2 from abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_nonneg t; linarith
    exact this
  have h_log_mono : Real.log (1 + |(-t:ℝ)/2|) ≤ Real.log (1 + |t|) := by
    apply Real.log_le_log
    · linarith [abs_nonneg ((-t:ℝ)/2)]
    · linarith
  have h_psi_bd : ‖ψ_val‖ ≤ C_d * (1 + Real.log (1 + |t|)) := by
    simp only [hψ_val, hψ_arg]
    calc ‖deriv Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((1/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I)‖
        ≤ C_d * (1 + Real.log (1 + |(-t)/2|)) := h_dig
      _ ≤ C_d * (1 + Real.log (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC_d_nn
  -- Assemble final bound.
  have h_log_nn : (0:ℝ) ≤ Real.log (1 + |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have h_logpi_nn : (0:ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
  calc ‖-(Complex.log (Real.pi : ℂ)) / 2 + (1/2 : ℂ) * (ψ_val - 1 / u)‖
      ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1/2 : ℂ) * (ψ_val - 1 / u)‖ := h_triangle
    _ ≤ |Real.log Real.pi| / 2 + ‖(1/2 : ℂ)‖ * (‖ψ_val‖ + ‖1/u‖) := by
        rw [h_logpi_bd]; linarith [h_tri2]
    _ ≤ |Real.log Real.pi| / 2 + (1/2) * (C_d * (1 + Real.log (1 + |t|)) + 2) := by
        rw [h_half_norm]
        have : (1/2 : ℝ) * (‖ψ_val‖ + ‖1/u‖) ≤
               (1/2) * (C_d * (1 + Real.log (1 + |t|)) + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [h_psi_bd, h_inv_u_bd]
        linarith
    _ ≤ (|Real.log Real.pi| / 2 + C_d / 2 + 1) * (1 + Real.log (1 + |t|)) := by
        nlinarith [h_log_nn, h_logpi_nn, hC_d_nn]

#print axioms gammaR_logDeriv_reflected_log_bound_at_two

-- ═══════════════════════════════════════════════════════════════════════════
-- § Sub-unit polynomial bound at σ = 2 (combines both log bounds)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Sub-unit arch bound at σ = 2.** Discharges `arch_subunit_bound_target 2`
with exponent `N = 1/2 < 1`.

Combines `gammaR_logDeriv_log_bound_at_two` (single side) and
`gammaR_logDeriv_reflected_log_bound_at_two` (reflected side) via triangle
inequality, then converts `log(1+|t|)` to `(1+|t|)^(1/2)` using
`one_add_log_le_three_rpow_half`. -/
theorem arch_subunit_bound_at_two : arch_subunit_bound_target 2 := by
  obtain ⟨C_s, hC_s_nn, h_s_bd⟩ := gammaR_logDeriv_log_bound_at_two
  obtain ⟨C_r, hC_r_nn, h_r_bd⟩ := gammaR_logDeriv_reflected_log_bound_at_two
  refine ⟨3 * (C_s + C_r), 1/2, by positivity, by norm_num, by norm_num, fun t => ?_⟩
  -- Unify the cast `((2:ℝ) : ℂ) = (2:ℂ)` used in `arch_subunit_bound_target`.
  have h_cast : (((2:ℝ) : ℂ) : ℂ) = (2 : ℂ) := by push_cast; rfl
  rw [show ((2:ℝ) : ℂ) = (2 : ℂ) from by push_cast; rfl]
  -- Triangle inequality on the joint norm.
  have h_triangle := norm_add_le
    (deriv Complex.Gammaℝ ((2 : ℂ) + (t : ℂ) * I) /
      ((2 : ℂ) + (t : ℂ) * I).Gammaℝ)
    (deriv Complex.Gammaℝ (1 - ((2 : ℂ) + (t : ℂ) * I)) /
      (1 - ((2 : ℂ) + (t : ℂ) * I)).Gammaℝ)
  have h_s := h_s_bd t
  have h_r := h_r_bd t
  have h_conv := one_add_log_le_three_rpow_half t
  have h_sum_nn : (0:ℝ) ≤ C_s + C_r := by linarith
  have h_log_mul : (C_s + C_r) * (1 + Real.log (1 + |t|)) ≤
      3 * (C_s + C_r) * (1 + |t|) ^ ((1:ℝ)/2) := by
    calc (C_s + C_r) * (1 + Real.log (1 + |t|))
        ≤ (C_s + C_r) * (3 * (1 + |t|)^((1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left h_conv h_sum_nn
      _ = 3 * (C_s + C_r) * (1 + |t|)^((1:ℝ)/2) := by ring
  linarith

#print axioms arch_subunit_bound_at_two

/-- **Polynomial bound at σ = 2.** Discharges `archOperator_polynomial_bound_target 2`.
Direct consequence of `arch_subunit_bound_at_two` (same `C` and `N`; the `N < 1`
strictness is dropped). -/
theorem archOperator_polynomial_bound_at_two :
    archOperator_polynomial_bound_target 2 := by
  obtain ⟨C, N, hC_nn, hN_nn, _hN_lt_1, h_bd⟩ := arch_subunit_bound_at_two
  exact ⟨C, N, hC_nn, hN_nn, h_bd⟩

#print axioms archOperator_polynomial_bound_at_two

-- ═══════════════════════════════════════════════════════════════════════════
-- § Measurability of archIntegrand along Re s = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- The set `{s : Γℝ(s) ≠ 0}` is open. Proved via `Γℝ⁻¹` being entire
(`Complex.differentiable_Gammaℝ_inv`) and preimage of `{c : c ≠ 0}` under
continuous is open. -/
private lemma Gammaℝ_ne_zero_isOpen : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {s : ℂ | s.Gammaℝ ≠ 0} =
      (fun s : ℂ => s.Gammaℝ⁻¹) ⁻¹' {z : ℂ | z ≠ 0} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine ⟨inv_ne_zero, fun h hs => ?_⟩
    apply h; rw [hs, inv_zero]
  rw [h_eq]
  exact IsOpen.preimage h_cont isOpen_ne

/-- `Γℝ` is analytic on `{s : Γℝ(s) ≠ 0}`. -/
private lemma Gammaℝ_analyticOnNhd :
    AnalyticOnNhd ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs; exact (differentiableAt_Gammaℝ_of_ne_zero hs).differentiableWithinAt
  · exact Gammaℝ_ne_zero_isOpen

/-- `deriv Γℝ` is analytic on `{s : Γℝ(s) ≠ 0}`. -/
private lemma deriv_Gammaℝ_analyticOnNhd :
    AnalyticOnNhd ℂ (deriv Complex.Gammaℝ) {s : ℂ | s.Gammaℝ ≠ 0} :=
  Gammaℝ_analyticOnNhd.deriv

/-- `Γℝ` is continuous on `{s : Γℝ(s) ≠ 0}`. -/
private lemma Gammaℝ_continuousOn :
    ContinuousOn Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} :=
  Gammaℝ_analyticOnNhd.continuousOn

/-- `deriv Γℝ` is continuous on `{s : Γℝ(s) ≠ 0}`. -/
private lemma deriv_Gammaℝ_continuousOn :
    ContinuousOn (deriv Complex.Gammaℝ) {s : ℂ | s.Gammaℝ ≠ 0} :=
  deriv_Gammaℝ_analyticOnNhd.continuousOn

/-- `t ↦ 2 + tI` is continuous. -/
private lemma vertical_line_continuous_two :
    Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) := by
  apply Continuous.add continuous_const
  exact Complex.continuous_ofReal.mul continuous_const

/-- `t ↦ 1 - (2 + tI)` is continuous. -/
private lemma reflected_line_continuous_two :
    Continuous (fun t : ℝ => 1 - ((2 : ℂ) + (t : ℂ) * I)) :=
  continuous_const.sub vertical_line_continuous_two

/-- Continuity of the joint arch operator along `Re s = 2`. -/
private lemma archOperator_continuous_at_two :
    Continuous (fun t : ℝ =>
      deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I) / ((2:ℂ) + (t:ℂ)*I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I)) /
        (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) := by
  -- Compose `deriv Γℝ` and `Γℝ` with the continuous line maps.
  have h_line := vertical_line_continuous_two
  have h_refl := reflected_line_continuous_two
  have h_line_mem : ∀ t : ℝ, (2:ℂ) + (t:ℂ)*I ∈ {s : ℂ | s.Gammaℝ ≠ 0} := fun t =>
    gammaR_ne_zero_two t
  have h_refl_mem : ∀ t : ℝ, 1 - ((2:ℂ) + (t:ℂ)*I) ∈ {s : ℂ | s.Gammaℝ ≠ 0} := fun t =>
    gammaR_ne_zero_reflected_two t
  have h_Gammaℝ_line_cont : Continuous (fun t : ℝ => ((2:ℂ) + (t:ℂ)*I).Gammaℝ) :=
    Gammaℝ_continuousOn.comp_continuous h_line h_line_mem
  have h_Gammaℝ_refl_cont : Continuous (fun t : ℝ => (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) :=
    Gammaℝ_continuousOn.comp_continuous h_refl h_refl_mem
  have h_derivGammaℝ_line_cont :
      Continuous (fun t : ℝ => deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I)) :=
    deriv_Gammaℝ_continuousOn.comp_continuous h_line h_line_mem
  have h_derivGammaℝ_refl_cont :
      Continuous (fun t : ℝ => deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I))) :=
    deriv_Gammaℝ_continuousOn.comp_continuous h_refl h_refl_mem
  apply Continuous.add
  · exact h_derivGammaℝ_line_cont.div h_Gammaℝ_line_cont (fun t => gammaR_ne_zero_two t)
  · exact h_derivGammaℝ_refl_cont.div h_Gammaℝ_refl_cont
      (fun t => gammaR_ne_zero_reflected_two t)

/-- `archIntegrand β 2` is continuous. -/
private lemma archIntegrand_continuous_at_two (β : ℝ) :
    Continuous (archIntegrand β 2) := by
  unfold archIntegrand
  have h_arch := archOperator_continuous_at_two
  -- pairTestMellin continuity: Re = 2 > 0.
  have h_pair := pairTestMellin_continuous_along_vertical β 2 (by norm_num : (0:ℝ) < 2)
  -- Unify the cast ((2:ℝ):ℂ) with (2:ℂ).
  have h_pair' : Continuous (fun t : ℝ =>
      pairTestMellin β ((2:ℂ) + (t:ℂ)*I)) := by
    have h_eq : (fun t : ℝ => pairTestMellin β (((2 : ℝ) : ℂ) + (t:ℂ)*I)) =
                (fun t : ℝ => pairTestMellin β ((2:ℂ) + (t:ℂ)*I)) := by
      funext t
      have : ((2:ℝ):ℂ) = (2:ℂ) := by push_cast; rfl
      rw [this]
    rw [h_eq] at h_pair
    exact h_pair
  have h_prod := h_arch.mul h_pair'
  -- Match cast forms.
  have h_cast_eq : (fun t : ℝ =>
      (deriv Complex.Gammaℝ (((2:ℝ):ℂ) + (t:ℂ)*I) / (((2:ℝ):ℂ) + (t:ℂ)*I).Gammaℝ +
       deriv Complex.Gammaℝ (1 - (((2:ℝ):ℂ) + (t:ℂ)*I)) /
         (1 - (((2:ℝ):ℂ) + (t:ℂ)*I)).Gammaℝ) *
      pairTestMellin β (((2:ℝ):ℂ) + (t:ℂ)*I)) =
    (fun t : ℝ =>
      (deriv Complex.Gammaℝ ((2:ℂ) + (t:ℂ)*I) / ((2:ℂ) + (t:ℂ)*I).Gammaℝ +
       deriv Complex.Gammaℝ (1 - ((2:ℂ) + (t:ℂ)*I)) /
         (1 - ((2:ℂ) + (t:ℂ)*I)).Gammaℝ) *
      pairTestMellin β ((2:ℂ) + (t:ℂ)*I)) := by
    funext t
    have h : ((2:ℝ):ℂ) = (2:ℂ) := by push_cast; rfl
    rw [h]
  rw [h_cast_eq]
  exact h_prod

-- ═══════════════════════════════════════════════════════════════════════════
-- § AP-1 closure at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **AP-1 at σ = 2.** `archIntegrand β 2` is integrable, unconditionally.

Combines:
* `arch_subunit_bound_at_two` — arch operator polynomially bounded (exponent 1/2).
* `archIntegrand_continuous_at_two` — continuity implies aestronglymeasurable.
* `archIntegrand_integrable_of_arch_subunit` — sub-unit bound + measurability → integrable. -/
theorem archIntegrand_integrable_at_two (β : ℝ) :
    MeasureTheory.Integrable (archIntegrand β 2) := by
  apply archIntegrand_integrable_of_arch_subunit β 2 (by norm_num : (0:ℝ) < 2)
    arch_subunit_bound_at_two
  exact (archIntegrand_continuous_at_two β).aestronglyMeasurable

#print axioms archIntegrand_integrable_at_two

-- ═══════════════════════════════════════════════════════════════════════════
-- § Zero-avoidance kit at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- `(2+tI) ≠ 0` for every real `t`. -/
private lemma two_plus_tI_ne_zero (t : ℝ) : ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have : ((2 : ℂ) + (t : ℂ) * I).re = 0 := by rw [h]; simp
  simp at this

/-- `(2+tI) ≠ 1`. -/
private lemma two_plus_tI_ne_one (t : ℝ) : ((2 : ℂ) + (t : ℂ) * I) ≠ 1 := by
  intro h
  have : ((2 : ℂ) + (t : ℂ) * I).re = 1 := by rw [h]; simp
  simp at this

/-- `1 - (2+tI) ≠ 0`. -/
private lemma one_sub_two_plus_tI_ne_zero (t : ℝ) :
    (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  intro h
  have hre : (1 - ((2 : ℂ) + (t : ℂ) * I)).re = 0 := by rw [h]; simp
  simp at hre
  linarith

/-- `ζ(2+tI) ≠ 0`. Direct from `riemannZeta_ne_zero_of_one_lt_re`. -/
private lemma zeta_ne_zero_two (t : ℝ) :
    riemannZeta ((2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp : (1:ℝ) < ((2:ℂ) + (t:ℂ)*I).re)

/-- `ζ(1-(2+tI)) = ζ(-1-tI) ≠ 0`. Proved via `completedRiemannZeta_one_sub`:
`ξ(1-s) = ξ(s) = Γℝ(s)·ζ(s)`, and `ζ(1-s) = ξ(1-s)/Γℝ(1-s)`. All three factors
`Γℝ(s), ζ(s), Γℝ(1-s)` are nonzero at `s = 2+tI`, hence so is `ζ(1-s)`. -/
private lemma zeta_ne_zero_reflected_two (t : ℝ) :
    riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs_def
  have h_zeta_s_ne : riemannZeta s ≠ 0 := zeta_ne_zero_two t
  have h_GammaR_s_ne : s.Gammaℝ ≠ 0 := gammaR_ne_zero_two t
  have h_GammaR_1s_ne : (1 - s).Gammaℝ ≠ 0 := gammaR_ne_zero_reflected_two t
  have h_s_ne_zero : s ≠ 0 := two_plus_tI_ne_zero t
  have h_1s_ne_zero : (1 - s) ≠ 0 := one_sub_two_plus_tI_ne_zero t
  have h_xi_s : completedRiemannZeta s = s.Gammaℝ * riemannZeta s :=
    completed_eq_gammaℝ_mul_zeta h_s_ne_zero h_GammaR_s_ne
  have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
    rw [h_xi_s]; exact mul_ne_zero h_GammaR_s_ne h_zeta_s_ne
  have h_xi_1s : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by rw [h_xi_1s]; exact h_xi_s_ne
  have h_zeta_1s_eq : riemannZeta (1 - s) = completedRiemannZeta (1 - s) / (1 - s).Gammaℝ :=
    riemannZeta_def_of_ne_zero h_1s_ne_zero
  rw [h_zeta_1s_eq]
  exact div_ne_zero h_xi_1s_ne h_GammaR_1s_ne

-- ═══════════════════════════════════════════════════════════════════════════
-- § AP-3 + AP-4 closures at σ = 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **AP-3 at σ = 2.** Reflected-prime integrand is integrable.
Chains from `archIntegrand_integrable_at_two` via the pointwise identity
`reflected = primeIntegrand - arch`. -/
theorem reflectedPrimeIntegrand_integrable_at_two (β : ℝ) :
    MeasureTheory.Integrable (reflectedPrimeIntegrand β 2) := by
  apply reflectedPrimeIntegrand_integrable_of_AP1 β 2 (by norm_num : (1:ℝ) < 2)
    (archIntegrand_integrable_at_two β)
  · intro t; exact two_plus_tI_ne_zero t
  · intro t; exact zeta_ne_zero_reflected_two t
  · intro t; exact zeta_ne_zero_two t
  · intro t; exact gammaR_ne_zero_two t
  · intro t; exact gammaR_ne_zero_reflected_two t

#print axioms reflectedPrimeIntegrand_integrable_at_two

/-- **AP-4 at σ = 2.** The `archIntegrand = primeIntegrand − reflectedPrimeIntegrand`
integral identity at the specific vertical line `Re s = 2`. -/
theorem weilArchPrimeIdentityTarget_at_two (β : ℝ) :
    (∫ t : ℝ, archIntegrand β 2 t) =
      (∫ t : ℝ, primeIntegrand β 2 t) -
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
         riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
        pairTestMellin β ((2 : ℂ) + (t : ℂ) * I)) := by
  have h_arch := archIntegrand_integrable_at_two β
  have h_prime := primeIntegrand_integrable β 2 (by norm_num : (1:ℝ) < 2)
  have h_ref := reflectedPrimeIntegrand_integrable_at_two β
  -- Pointwise identity.
  have h_ptw : ∀ t : ℝ,
      archIntegrand β 2 t = primeIntegrand β 2 t - reflectedPrimeIntegrand β 2 t := by
    intro t
    unfold reflectedPrimeIntegrand
    exact archIntegrand_eq_primeIntegrand_minus_reflected β (by norm_num : (1:ℝ) < 2) t
      (two_plus_tI_ne_zero t) (two_plus_tI_ne_one t)
      (zeta_ne_zero_two t) (zeta_ne_zero_reflected_two t)
      (gammaR_ne_zero_two t) (gammaR_ne_zero_reflected_two t)
  have h_fn_eq : archIntegrand β 2 =
      (fun t => primeIntegrand β 2 t - reflectedPrimeIntegrand β 2 t) := by
    funext t; exact h_ptw t
  calc (∫ t : ℝ, archIntegrand β 2 t)
      = ∫ t : ℝ, primeIntegrand β 2 t - reflectedPrimeIntegrand β 2 t := by
          rw [h_fn_eq]
    _ = (∫ t : ℝ, primeIntegrand β 2 t) -
        ∫ t : ℝ, reflectedPrimeIntegrand β 2 t :=
          MeasureTheory.integral_sub h_prime h_ref
    _ = (∫ t : ℝ, primeIntegrand β 2 t) -
        ∫ t : ℝ, deriv riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((2 : ℂ) + (t : ℂ) * I)) *
          pairTestMellin β ((2 : ℂ) + (t : ℂ) * I) := by
          rfl

#print axioms weilArchPrimeIdentityTarget_at_two

-- ═══════════════════════════════════════════════════════════════════════════
-- § GENERAL-σ CHAIN (extends σ=2 to σ ∈ (1, 3))
-- ═══════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════
-- § General-σ single-side Γℝ log-derivative bound
-- ═══════════════════════════════════════════════════════════════════════════

/-- `(σ+tI).Gammaℝ ≠ 0` for every real `t` and σ > 0. -/
private lemma gammaR_ne_zero_at_sigma {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  show (0:ℝ) < ((σ : ℂ) + (t : ℂ) * I).re
  simp; exact hσ

private lemma sigma_plus_tI_ne_neg_two_nat {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∀ n : ℕ, ((σ : ℂ) + (t : ℂ) * I) ≠ -(2 * (n : ℂ)) := by
  intro n h
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = (-(2 * (n : ℂ))).re := by rw [h]
  simp at hre
  have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **Single-side log bound at arbitrary σ > 0.** Generalizes
`gammaR_logDeriv_log_bound_at_two`. -/
theorem gammaR_logDeriv_log_bound_at_sigma {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * I) /
          ((σ : ℂ) + (t : ℂ) * I).Gammaℝ‖ ≤ C * (1 + Real.log (1 + |t|)) := by
  obtain ⟨C_d, hC_d_nn, hC_d_bd⟩ := digamma_log_bound_all_t (σ/2) (by linarith : (0:ℝ) < σ/2)
  refine ⟨|Real.log Real.pi| / 2 + C_d / 2, by positivity, fun t => ?_⟩
  have hGammaℝ_ne := gammaR_ne_zero_at_sigma hσ t
  have hne2n := sigma_plus_tI_ne_neg_two_nat hσ t
  rw [gammaℝ_logDeriv_digamma_form _ hGammaℝ_ne hne2n]
  have h_half_eq : ((σ : ℂ) + (t : ℂ) * I) / 2 =
      ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_half_eq]
  have h_dig := hC_d_bd (t/2)
  have h_triangle :
      ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          (1 / 2 : ℂ) *
            (deriv Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ ≤
        ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ := norm_add_le _ _
  have h_logpi_bd : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div]
    rw [show ‖-(Complex.log (Real.pi : ℂ))‖ = ‖Complex.log (Real.pi : ℂ)‖ from norm_neg _]
    rw [show (Complex.log (Real.pi : ℂ)) = ((Real.log Real.pi : ℝ) : ℂ) by
      have := Complex.ofReal_log Real.pi_pos.le; exact this.symm]
    rw [Complex.norm_real]; simp
  have h_scaled_bd :
      ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ ≤
        (1/2) * (C_d * (1 + Real.log (1 + |t/2|))) := by
    rw [norm_mul]
    have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real]; norm_num
    rw [h_half_norm]
    exact mul_le_mul_of_nonneg_left h_dig (by norm_num)
  have h_abs_half : |t/2| ≤ |t| := by
    rw [abs_div]
    have : |t| / |(2:ℝ)| ≤ |t| := by
      rw [show |(2:ℝ)| = 2 from abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_nonneg t; linarith
    exact this
  have h_log_mono : Real.log (1 + |t/2|) ≤ Real.log (1 + |t|) := by
    apply Real.log_le_log
    · linarith [abs_nonneg (t/2)]
    · linarith
  calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          (1 / 2 : ℂ) *
            (deriv Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
              Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖
      ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1 / 2 : ℂ) *
          (deriv Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))‖ := h_triangle
    _ ≤ |Real.log Real.pi| / 2 + (1/2) * (C_d * (1 + Real.log (1 + |t/2|))) := by
        rw [h_logpi_bd]; linarith [h_scaled_bd]
    _ ≤ |Real.log Real.pi| / 2 + (1/2) * (C_d * (1 + Real.log (1 + |t|))) := by
        have : C_d * (1 + Real.log (1 + |t/2|)) ≤ C_d * (1 + Real.log (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC_d_nn
        linarith
    _ ≤ (|Real.log Real.pi| / 2 + C_d / 2) * (1 + Real.log (1 + |t|)) := by
        have h_log_nn : (0:ℝ) ≤ Real.log (1 + |t|) :=
          Real.log_nonneg (by linarith [abs_nonneg t])
        have h_logpi_nn : (0:ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
        nlinarith [h_log_nn, h_logpi_nn, hC_d_nn]

#print axioms gammaR_logDeriv_log_bound_at_sigma

-- ═══════════════════════════════════════════════════════════════════════════
-- § General-σ reflected Γℝ log-derivative bound (σ ∈ (1, 3))
-- ═══════════════════════════════════════════════════════════════════════════

/-- `Γℝ(1-σ-tI) ≠ 0` for σ ∈ (1, 3) (excluding odd-integer trivial pole points). -/
private lemma gammaR_ne_zero_reflected_sigma {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) (t : ℝ) :
    (1 - ((σ : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre : (1 - ((σ : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [hn]
  simp at hre
  -- hre : 1 - σ = -(2n), i.e., σ - 1 = 2n, with σ ∈ (1, 3) means σ - 1 ∈ (0, 2).
  -- So 2n ∈ (0, 2), i.e., n ∈ (0, 1). No natural n satisfies this.
  have hn_nn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : (n : ℝ) < 1 := by linarith
  have : n = 0 := by exact_mod_cast (Nat.lt_one_iff).mp (by exact_mod_cast this)
  rw [this] at hre; norm_num at hre; linarith

private lemma one_sub_sigma_plus_tI_ne_neg_two_nat {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) (t : ℝ) :
    ∀ n : ℕ, (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ -(2 * (n : ℂ)) := by
  intro n h
  have hre : (1 - ((σ : ℂ) + (t : ℂ) * I)).re = (-(2 * (n : ℂ))).re := by rw [h]
  simp at hre
  have hn_nn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : (n : ℝ) < 1 := by linarith
  have : n = 0 := by exact_mod_cast (Nat.lt_one_iff).mp (by exact_mod_cast this)
  rw [this] at hre; norm_num at hre; linarith

/-- Half-point `(1-σ)/2 - tI/2` is not a non-positive integer for σ ∈ (1, 3). -/
private lemma half_1_sub_sigma_minus_half_tI_ne_neg_nat
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) (t : ℝ) :
    ∀ n : ℕ, (((1-σ)/2 : ℝ) : ℂ) + -((t/2:ℝ) : ℂ) * I ≠ -(n : ℂ) := by
  intro n h
  have hre : ((((1-σ)/2 : ℝ) : ℂ) + -((t/2:ℝ) : ℂ) * I).re = (-(n : ℂ)).re := by rw [h]
  simp at hre
  -- hre : (1-σ)/2 = -n, so σ = 1 + 2n.
  -- For σ ∈ (1, 3), 2n ∈ (0, 2), n ∈ (0, 1), no natural n.
  have hn_nn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : (n : ℝ) < 1 := by linarith
  have : n = 0 := by exact_mod_cast (Nat.lt_one_iff).mp (by exact_mod_cast this)
  rw [this] at hre; norm_num at hre; linarith

/-- Norm lower bound `‖(1-σ)/2 - (t/2)I‖ ≥ (σ-1)/2` for σ > 1 and every `t`. -/
private lemma norm_half_1_sub_sigma_minus_half_tI_ge {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (σ - 1)/2 ≤ ‖(((1-σ)/2 : ℝ) : ℂ) + -((t/2 : ℝ) : ℂ) * I‖ := by
  -- Rewrite in form x + y·I with real x = (1-σ)/2, y = -t/2.
  have h_rewrite : (((1-σ)/2 : ℝ) : ℂ) + -((t/2 : ℝ) : ℂ) * I =
      (((1-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_rewrite]
  have h_normSq : Complex.normSq (((( 1 - σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I) =
      (((1-σ)/2 : ℝ))^2 + ((-t/2 : ℝ))^2 := Complex.normSq_add_mul_I _ _
  have h_normSq_val : Complex.normSq (((( 1 - σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I) =
      ((σ-1)/2)^2 + (t/2)^2 := by
    rw [h_normSq]; ring
  have h_sq_eq : ‖(((1-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖^2 = ((σ-1)/2)^2 + (t/2)^2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact h_normSq_val
  have h_sigma_half_nn : 0 ≤ (σ-1)/2 := by linarith
  have h_ge_quarter : ((σ-1)/2)^2 ≤ ‖(((1-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖^2 := by
    rw [h_sq_eq]; have := sq_nonneg (t/2); linarith
  have h_norm_nn : (0:ℝ) ≤ ‖(((1-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖ := norm_nonneg _
  nlinarith [sq_nonneg ((σ-1)/2 - ‖(((1-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I‖), h_norm_nn]

/-- **Reflected-side log bound at general σ ∈ (1, 3).**
`‖Γℝ'/Γℝ(1-σ-tI)‖ ≤ C · (1 + log(1+|t|))` for some `C ≥ 0`. -/
theorem gammaR_logDeriv_reflected_log_bound_at_sigma
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv Complex.Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) /
          (1 - ((σ : ℂ) + (t : ℂ) * I)).Gammaℝ‖ ≤ C * (1 + Real.log (1 + |t|)) := by
  -- ψ bound at shifted argument σ' = (3-σ)/2 > 0.
  have h_shifted_pos : (0:ℝ) < (3-σ)/2 := by linarith
  obtain ⟨C_d, hC_d_nn, hC_d_bd⟩ := digamma_log_bound_all_t ((3-σ)/2) h_shifted_pos
  -- |1/s| bound: |s| ≥ (σ-1)/2, so |1/s| ≤ 2/(σ-1).
  have h_sigma_minus_one_pos : (0:ℝ) < σ - 1 := by linarith
  have h_inv_bound : (2 : ℝ) / (σ - 1) ≥ 0 := by positivity
  refine ⟨|Real.log Real.pi| / 2 + C_d / 2 + 1/(σ-1), by positivity, fun t => ?_⟩
  have hGammaℝ_ne := gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t
  have hne2n := one_sub_sigma_plus_tI_ne_neg_two_nat hσ_gt hσ_lt t
  rw [gammaℝ_logDeriv_digamma_form _ hGammaℝ_ne hne2n]
  -- s/2 = (1-σ)/2 - (t/2)·I.
  have h_half_eq : (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2 =
      (((1-σ)/2 : ℝ) : ℂ) + -((t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_half_eq]
  -- Shift: ψ(s) = ψ(s+1) - 1/s at s = (1-σ)/2 - (t/2)I.
  have h_shift_hypo : ∀ n : ℕ, (((1-σ)/2 : ℝ) : ℂ) + -((t/2:ℝ) : ℂ) * I ≠ -(n : ℂ) :=
    half_1_sub_sigma_minus_half_tI_ne_neg_nat hσ_gt hσ_lt t
  rw [digamma_shift_eq h_shift_hypo]
  -- (s+1) = ((3-σ)/2 : ℝ) + (-(t/2))·I.
  have h_s_plus_one : (((1-σ)/2 : ℝ) : ℂ) + -((t/2:ℝ) : ℂ) * I + 1 =
      (((3-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h_s_plus_one]
  have h_dig := hC_d_bd (-t/2)
  set u : ℂ := (((1-σ)/2 : ℝ) : ℂ) + -((t/2:ℝ) : ℂ) * I with hu_def
  set ψ_arg : ℂ := (((3-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I with hψ_arg
  set ψ_val : ℂ := deriv Complex.Gamma ψ_arg / Complex.Gamma ψ_arg with hψ_val
  have h_triangle :
      ‖-(Complex.log (Real.pi : ℂ)) / 2 + (1/2 : ℂ) * (ψ_val - 1 / u)‖ ≤
        ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1/2 : ℂ) * (ψ_val - 1 / u)‖ := norm_add_le _ _
  have h_tri2 : ‖(1/2 : ℂ) * (ψ_val - 1/u)‖ ≤
      ‖(1/2 : ℂ)‖ * (‖ψ_val‖ + ‖1/u‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have h_logpi_bd : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div]
    rw [show ‖-(Complex.log (Real.pi : ℂ))‖ = ‖Complex.log (Real.pi : ℂ)‖ from norm_neg _]
    rw [show (Complex.log (Real.pi : ℂ)) = ((Real.log Real.pi : ℝ) : ℂ) by
      have := Complex.ofReal_log Real.pi_pos.le; exact this.symm]
    rw [Complex.norm_real]; simp
  have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real]; norm_num
  -- ‖1/u‖ ≤ 2/(σ-1).
  have h_u_norm_ge : (σ-1)/2 ≤ ‖u‖ := by
    simp only [hu_def]; exact norm_half_1_sub_sigma_minus_half_tI_ge hσ_gt t
  have h_u_ne_zero : u ≠ 0 := by
    intro hu
    have : ‖u‖ = 0 := by rw [hu]; exact norm_zero
    have : (σ-1)/2 ≤ 0 := this ▸ h_u_norm_ge
    linarith
  have h_inv_u_bd : ‖1 / u‖ ≤ 2/(σ-1) := by
    rw [norm_div, norm_one]
    have h_pos : (0:ℝ) < ‖u‖ := by
      have := h_u_norm_ge; have h1 : (0:ℝ) < (σ-1)/2 := by linarith
      linarith
    have h_one_div : (1 : ℝ) / ‖u‖ ≤ 1 / ((σ-1)/2) :=
      one_div_le_one_div_of_le (by linarith) h_u_norm_ge
    have h_inv_simp : (1:ℝ) / ((σ-1)/2) = 2/(σ-1) := by
      rw [div_div_eq_mul_div]; ring
    linarith
  have h_abs_neg_half : |(-t:ℝ)/2| ≤ |t| := by
    rw [show (-t:ℝ)/2 = -(t/2) from by ring]
    rw [abs_neg, abs_div]
    have : |t| / |(2:ℝ)| ≤ |t| := by
      rw [show |(2:ℝ)| = 2 from abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_nonneg t; linarith
    exact this
  have h_log_mono : Real.log (1 + |(-t:ℝ)/2|) ≤ Real.log (1 + |t|) := by
    apply Real.log_le_log
    · linarith [abs_nonneg ((-t:ℝ)/2)]
    · linarith
  have h_psi_bd : ‖ψ_val‖ ≤ C_d * (1 + Real.log (1 + |t|)) := by
    simp only [hψ_val, hψ_arg]
    calc ‖deriv Complex.Gamma (((((3-σ)/2 : ℝ) : ℂ)) + ((-t/2 : ℝ) : ℂ) * I) /
            Complex.Gamma ((((3-σ)/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * I)‖
        ≤ C_d * (1 + Real.log (1 + |(-t)/2|)) := h_dig
      _ ≤ C_d * (1 + Real.log (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC_d_nn
  have h_log_nn : (0:ℝ) ≤ Real.log (1 + |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have h_logpi_nn : (0:ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
  have h_sigma_minus_one_inv_nn : (0:ℝ) ≤ 1/(σ-1) := by positivity
  calc ‖-(Complex.log (Real.pi : ℂ)) / 2 + (1/2 : ℂ) * (ψ_val - 1 / u)‖
      ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
        ‖(1/2 : ℂ) * (ψ_val - 1 / u)‖ := h_triangle
    _ ≤ |Real.log Real.pi| / 2 + ‖(1/2 : ℂ)‖ * (‖ψ_val‖ + ‖1/u‖) := by
        rw [h_logpi_bd]; linarith [h_tri2]
    _ ≤ |Real.log Real.pi| / 2 +
          (1/2) * (C_d * (1 + Real.log (1 + |t|)) + 2/(σ-1)) := by
        rw [h_half_norm]
        have : (1/2 : ℝ) * (‖ψ_val‖ + ‖1/u‖) ≤
               (1/2) * (C_d * (1 + Real.log (1 + |t|)) + 2/(σ-1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [h_psi_bd, h_inv_u_bd]
        linarith
    _ ≤ (|Real.log Real.pi| / 2 + C_d / 2 + 1/(σ-1)) * (1 + Real.log (1 + |t|)) := by
        -- Expand: RHS - LHS = L · (|logπ|/2 + 1/(σ-1)) ≥ 0.
        have h_logπ_half_plus_inv_nn : (0:ℝ) ≤ |Real.log Real.pi| / 2 + 1/(σ-1) := by
          linarith
        have h_mul_nn : (0:ℝ) ≤ Real.log (1 + |t|) * (|Real.log Real.pi| / 2 + 1/(σ-1)) :=
          mul_nonneg h_log_nn h_logπ_half_plus_inv_nn
        -- RHS = |logπ|/2 + C_d/2 + 1/(σ-1) + L·|logπ|/2 + L·C_d/2 + L/(σ-1)
        -- LHS = |logπ|/2 + C_d/2 + L·C_d/2 + 1/(σ-1)
        -- RHS - LHS = L·|logπ|/2 + L/(σ-1) = L·(|logπ|/2 + 1/(σ-1)) ≥ 0
        have h_diff :
            (|Real.log Real.pi| / 2 + C_d / 2 + 1/(σ-1)) * (1 + Real.log (1 + |t|)) -
            (|Real.log Real.pi| / 2 + (1/2) *
              (C_d * (1 + Real.log (1 + |t|)) + 2/(σ-1))) =
            Real.log (1 + |t|) * (|Real.log Real.pi| / 2 + 1/(σ-1)) := by ring
        linarith [h_mul_nn, h_diff]

#print axioms gammaR_logDeriv_reflected_log_bound_at_sigma

-- ═══════════════════════════════════════════════════════════════════════════
-- § General-σ arch subunit bound + polynomial bound target (σ ∈ (1, 3))
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Sub-unit arch bound at σ ∈ (1, 3).** Discharges `arch_subunit_bound_target σ`
with exponent `N = 1/2 < 1`. -/
theorem arch_subunit_bound_at_sigma
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    arch_subunit_bound_target σ := by
  obtain ⟨C_s, hC_s_nn, h_s_bd⟩ :=
    gammaR_logDeriv_log_bound_at_sigma (by linarith : (0:ℝ) < σ)
  obtain ⟨C_r, hC_r_nn, h_r_bd⟩ :=
    gammaR_logDeriv_reflected_log_bound_at_sigma hσ_gt hσ_lt
  refine ⟨3 * (C_s + C_r), 1/2, by positivity, by norm_num, by norm_num, fun t => ?_⟩
  have h_triangle := norm_add_le
    (deriv Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * I) /
      ((σ : ℂ) + (t : ℂ) * I).Gammaℝ)
    (deriv Complex.Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) /
      (1 - ((σ : ℂ) + (t : ℂ) * I)).Gammaℝ)
  have h_s := h_s_bd t
  have h_r := h_r_bd t
  have h_conv := one_add_log_le_three_rpow_half t
  have h_sum_nn : (0:ℝ) ≤ C_s + C_r := by linarith
  have h_log_mul : (C_s + C_r) * (1 + Real.log (1 + |t|)) ≤
      3 * (C_s + C_r) * (1 + |t|) ^ ((1:ℝ)/2) := by
    calc (C_s + C_r) * (1 + Real.log (1 + |t|))
        ≤ (C_s + C_r) * (3 * (1 + |t|)^((1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left h_conv h_sum_nn
      _ = 3 * (C_s + C_r) * (1 + |t|)^((1:ℝ)/2) := by ring
  linarith

#print axioms arch_subunit_bound_at_sigma

/-- **Polynomial bound at σ ∈ (1, 3).** Discharges `archOperator_polynomial_bound_target σ`. -/
theorem archOperator_polynomial_bound_at_sigma
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    archOperator_polynomial_bound_target σ := by
  obtain ⟨C, N, hC_nn, hN_nn, _hN_lt_1, h_bd⟩ := arch_subunit_bound_at_sigma hσ_gt hσ_lt
  exact ⟨C, N, hC_nn, hN_nn, h_bd⟩

#print axioms archOperator_polynomial_bound_at_sigma

-- ═══════════════════════════════════════════════════════════════════════════
-- § General-σ archIntegrand continuity + AP-1 at σ ∈ (1, 3)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `t ↦ σ + tI` is continuous. -/
private lemma vertical_line_continuous_at_sigma {σ : ℝ} :
    Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by
  apply Continuous.add continuous_const
  exact Complex.continuous_ofReal.mul continuous_const

/-- `t ↦ 1 − (σ + tI)` is continuous. -/
private lemma reflected_line_continuous_at_sigma {σ : ℝ} :
    Continuous (fun t : ℝ => 1 - ((σ : ℂ) + (t : ℂ) * I)) :=
  continuous_const.sub vertical_line_continuous_at_sigma

/-- Continuity of the joint arch operator along `Re s = σ` for `σ ∈ (1, 3)`. -/
private lemma archOperator_continuous_at_sigma
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    Continuous (fun t : ℝ =>
      deriv Complex.Gammaℝ ((σ:ℂ) + (t:ℂ)*I) / ((σ:ℂ) + (t:ℂ)*I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((σ:ℂ) + (t:ℂ)*I)) /
        (1 - ((σ:ℂ) + (t:ℂ)*I)).Gammaℝ) := by
  have h_line := vertical_line_continuous_at_sigma (σ := σ)
  have h_refl := reflected_line_continuous_at_sigma (σ := σ)
  have h_line_mem : ∀ t : ℝ, (σ:ℂ) + (t:ℂ)*I ∈ {s : ℂ | s.Gammaℝ ≠ 0} := fun t =>
    gammaR_ne_zero_at_sigma (by linarith : (0:ℝ) < σ) t
  have h_refl_mem : ∀ t : ℝ, 1 - ((σ:ℂ) + (t:ℂ)*I) ∈ {s : ℂ | s.Gammaℝ ≠ 0} := fun t =>
    gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t
  have h_Gammaℝ_line_cont : Continuous (fun t : ℝ => ((σ:ℂ) + (t:ℂ)*I).Gammaℝ) :=
    Gammaℝ_continuousOn.comp_continuous h_line h_line_mem
  have h_Gammaℝ_refl_cont : Continuous (fun t : ℝ => (1 - ((σ:ℂ) + (t:ℂ)*I)).Gammaℝ) :=
    Gammaℝ_continuousOn.comp_continuous h_refl h_refl_mem
  have h_derivGammaℝ_line_cont :
      Continuous (fun t : ℝ => deriv Complex.Gammaℝ ((σ:ℂ) + (t:ℂ)*I)) :=
    deriv_Gammaℝ_continuousOn.comp_continuous h_line h_line_mem
  have h_derivGammaℝ_refl_cont :
      Continuous (fun t : ℝ => deriv Complex.Gammaℝ (1 - ((σ:ℂ) + (t:ℂ)*I))) :=
    deriv_Gammaℝ_continuousOn.comp_continuous h_refl h_refl_mem
  apply Continuous.add
  · exact h_derivGammaℝ_line_cont.div h_Gammaℝ_line_cont
      (fun t => gammaR_ne_zero_at_sigma (by linarith : (0:ℝ) < σ) t)
  · exact h_derivGammaℝ_refl_cont.div h_Gammaℝ_refl_cont
      (fun t => gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t)

/-- `archIntegrand β σ` is continuous for σ ∈ (1, 3). -/
private lemma archIntegrand_continuous_at_sigma
    (β : ℝ) {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    Continuous (archIntegrand β σ) := by
  unfold archIntegrand
  have h_arch := archOperator_continuous_at_sigma hσ_gt hσ_lt
  have h_pair := pairTestMellin_continuous_along_vertical β σ (by linarith : (0:ℝ) < σ)
  have h_pair' : Continuous (fun t : ℝ => pairTestMellin β ((σ:ℂ) + (t:ℂ)*I)) := by
    have h_eq : (fun t : ℝ => pairTestMellin β (((σ : ℝ) : ℂ) + (t:ℂ)*I)) =
                (fun t : ℝ => pairTestMellin β ((σ:ℂ) + (t:ℂ)*I)) := by
      funext t
      have hcast : ((σ:ℝ):ℂ) = (σ:ℂ) := rfl
      rw [hcast]
    rw [h_eq] at h_pair; exact h_pair
  have h_prod := h_arch.mul h_pair'
  have h_cast_eq : (fun t : ℝ =>
      (deriv Complex.Gammaℝ (((σ:ℝ):ℂ) + (t:ℂ)*I) / (((σ:ℝ):ℂ) + (t:ℂ)*I).Gammaℝ +
       deriv Complex.Gammaℝ (1 - (((σ:ℝ):ℂ) + (t:ℂ)*I)) /
         (1 - (((σ:ℝ):ℂ) + (t:ℂ)*I)).Gammaℝ) *
      pairTestMellin β (((σ:ℝ):ℂ) + (t:ℂ)*I)) =
    (fun t : ℝ =>
      (deriv Complex.Gammaℝ ((σ:ℂ) + (t:ℂ)*I) / ((σ:ℂ) + (t:ℂ)*I).Gammaℝ +
       deriv Complex.Gammaℝ (1 - ((σ:ℂ) + (t:ℂ)*I)) /
         (1 - ((σ:ℂ) + (t:ℂ)*I)).Gammaℝ) *
      pairTestMellin β ((σ:ℂ) + (t:ℂ)*I)) := by
    funext t
    have h : ((σ:ℝ):ℂ) = (σ:ℂ) := rfl
    rw [h]
  rw [h_cast_eq]; exact h_prod

/-- **AP-1 at σ ∈ (1, 3).** `archIntegrand β σ` is integrable unconditionally. -/
theorem archIntegrand_integrable_at_sigma
    (β : ℝ) {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    MeasureTheory.Integrable (archIntegrand β σ) := by
  apply archIntegrand_integrable_of_arch_subunit β σ (by linarith : (0:ℝ) < σ)
    (arch_subunit_bound_at_sigma hσ_gt hσ_lt)
  exact (archIntegrand_continuous_at_sigma β hσ_gt hσ_lt).aestronglyMeasurable

#print axioms archIntegrand_integrable_at_sigma

-- ═══════════════════════════════════════════════════════════════════════════
-- § Zero-avoidance kit + AP-3 / AP-4 at σ ∈ (1, 3)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `(σ + tI) ≠ 0` for σ > 0. -/
private lemma sigma_plus_tI_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have : ((σ : ℂ) + (t : ℂ) * I).re = 0 := by rw [h]; simp
  simp at this; linarith

/-- `(σ + tI) ≠ 1` for σ > 1. -/
private lemma sigma_plus_tI_ne_one {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
  intro h
  have : ((σ : ℂ) + (t : ℂ) * I).re = 1 := by rw [h]; simp
  simp at this; linarith

/-- `ζ(σ + tI) ≠ 0` for σ > 1. -/
private lemma zeta_ne_zero_at_sigma {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (show (1:ℝ) < ((σ:ℂ) + (t:ℂ)*I).re by simp; exact hσ)

/-- `ζ(1 - σ - tI) ≠ 0` for σ ∈ (1, 3) (via FE + `ξ` non-vanishing route). -/
private lemma zeta_ne_zero_reflected_sigma
    {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) (t : ℝ) :
    riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs_def
  have h_zeta_s_ne : riemannZeta s ≠ 0 := zeta_ne_zero_at_sigma hσ_gt t
  have h_GammaR_s_ne : s.Gammaℝ ≠ 0 :=
    gammaR_ne_zero_at_sigma (by linarith : (0:ℝ) < σ) t
  have h_GammaR_1s_ne : (1 - s).Gammaℝ ≠ 0 :=
    gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t
  have h_s_ne_zero : s ≠ 0 := sigma_plus_tI_ne_zero (by linarith) t
  have h_1s_ne_zero : (1 - s) ≠ 0 := by
    intro h
    have hre : (1 - s).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.one_re, hs_def, Complex.add_re,
               Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
               Complex.I_re, Complex.I_im] at hre
    linarith
  have h_xi_s : completedRiemannZeta s = s.Gammaℝ * riemannZeta s :=
    completed_eq_gammaℝ_mul_zeta h_s_ne_zero h_GammaR_s_ne
  have h_xi_s_ne : completedRiemannZeta s ≠ 0 := by
    rw [h_xi_s]; exact mul_ne_zero h_GammaR_s_ne h_zeta_s_ne
  have h_xi_1s : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  have h_xi_1s_ne : completedRiemannZeta (1 - s) ≠ 0 := by rw [h_xi_1s]; exact h_xi_s_ne
  have h_zeta_1s_eq : riemannZeta (1 - s) = completedRiemannZeta (1 - s) / (1 - s).Gammaℝ :=
    riemannZeta_def_of_ne_zero h_1s_ne_zero
  rw [h_zeta_1s_eq]; exact div_ne_zero h_xi_1s_ne h_GammaR_1s_ne

/-- **AP-3 at σ ∈ (1, 3).** -/
theorem reflectedPrimeIntegrand_integrable_at_sigma
    (β : ℝ) {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    MeasureTheory.Integrable (reflectedPrimeIntegrand β σ) := by
  apply reflectedPrimeIntegrand_integrable_of_AP1 β σ hσ_gt
    (archIntegrand_integrable_at_sigma β hσ_gt hσ_lt)
  · intro t; exact sigma_plus_tI_ne_zero (by linarith : (0:ℝ) < σ) t
  · intro t; exact zeta_ne_zero_reflected_sigma hσ_gt hσ_lt t
  · intro t; exact zeta_ne_zero_at_sigma hσ_gt t
  · intro t; exact gammaR_ne_zero_at_sigma (by linarith : (0:ℝ) < σ) t
  · intro t; exact gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t

#print axioms reflectedPrimeIntegrand_integrable_at_sigma

/-- **AP-4 at σ ∈ (1, 3).** Integral identity. -/
theorem weilArchPrimeIdentityTarget_at_sigma
    (β : ℝ) {σ : ℝ} (hσ_gt : 1 < σ) (hσ_lt : σ < 3) :
    (∫ t : ℝ, archIntegrand β σ t) =
      (∫ t : ℝ, primeIntegrand β σ t) -
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * I)) /
         riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * I)) *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) := by
  have h_arch := archIntegrand_integrable_at_sigma β hσ_gt hσ_lt
  have h_prime := primeIntegrand_integrable β σ hσ_gt
  have h_ref := reflectedPrimeIntegrand_integrable_at_sigma β hσ_gt hσ_lt
  have h_ptw : ∀ t : ℝ,
      archIntegrand β σ t = primeIntegrand β σ t - reflectedPrimeIntegrand β σ t := by
    intro t
    unfold reflectedPrimeIntegrand
    exact archIntegrand_eq_primeIntegrand_minus_reflected β hσ_gt t
      (sigma_plus_tI_ne_zero (by linarith : (0:ℝ) < σ) t) (sigma_plus_tI_ne_one hσ_gt t)
      (zeta_ne_zero_at_sigma hσ_gt t) (zeta_ne_zero_reflected_sigma hσ_gt hσ_lt t)
      (gammaR_ne_zero_at_sigma (by linarith : (0:ℝ) < σ) t)
      (gammaR_ne_zero_reflected_sigma hσ_gt hσ_lt t)
  have h_fn_eq : archIntegrand β σ =
      (fun t => primeIntegrand β σ t - reflectedPrimeIntegrand β σ t) := by
    funext t; exact h_ptw t
  calc (∫ t : ℝ, archIntegrand β σ t)
      = ∫ t : ℝ, primeIntegrand β σ t - reflectedPrimeIntegrand β σ t := by rw [h_fn_eq]
    _ = (∫ t : ℝ, primeIntegrand β σ t) - ∫ t : ℝ, reflectedPrimeIntegrand β σ t :=
          MeasureTheory.integral_sub h_prime h_ref
    _ = (∫ t : ℝ, primeIntegrand β σ t) -
        ∫ t : ℝ, deriv riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * I)) *
          pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) := by rfl

#print axioms weilArchPrimeIdentityTarget_at_sigma

end ZD.WeilPositivity.Contour

end
