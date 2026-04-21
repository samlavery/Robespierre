import Mathlib
import RequestProject.XiPartialFraction
import RequestProject.LogDerivIdentity
import RequestProject.ArchOperatorBound
import RequestProject.WeilLogDerivZetaBound

/-!
# H10: Short-window zero count `#{γ : |γ - T| ≤ 1} ≤ C·log T`

The classical Riemann–von Mangoldt short-window count, derived from the
Hadamard partial fraction (H8) evaluated at `s = 2 + iT`.

## Strategy

1. Apply H8's partial fraction at `s = 2 + iT`:
   `ξ'/ξ(2+iT) = A + Σ_ρ xiOrderNat(ρ) · [1/(2+iT - ρ) + 1/ρ]`.

2. Take real parts. For ρ = β + iγ with `0 < β < 1`:
   `Re(1/(2+iT-ρ) + 1/ρ) = (2-β)/((2-β)² + (T-γ)²) + β/(β² + γ²) ≥ 0`.
   For ρ with `|γ - T| ≤ 1`: `(2-β)² + (T-γ)² ≤ 4 + 1 = 5`, so the first
   summand is `≥ (2-β)/5 ≥ 1/5` (since `1 ≤ 2-β ≤ 2`).

3. From H9 (`riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ`):
   `ξ'/ξ(2+iT) = ζ'/ζ(2+iT) + 1/(2+iT) + 1/(1+iT) + logDeriv Γℝ (2+iT)`.
   Bounds on each piece:
   * `‖ζ'/ζ(2+iT)‖ ≤ Cζ` (uniform on `Re s ≥ 3/2`, via
     `logDerivZeta_bounded_of_right_of_one`).
   * `‖1/(2+iT)‖, ‖1/(1+iT)‖ ≤ 1`.
   * `‖logDeriv Γℝ (2+iT)‖ ≤ CΓ · (1 + log(1+|T|))` via
     `gammaR_logDeriv_log_bound_at_two`.
   Combining: `‖ξ'/ξ(2+iT)‖ ≤ K · log T` for `T ≥ 2`.

4. Summability of the weighted tsum at `s = 2+iT ∉ NontrivialZeros`
   (derived via `Summable.sigma` on `summable_logDeriv_multi`) permits taking
   real parts term-by-term.

5. Lower-bounding each filtered term by `(xiOrderNat ρ)/5` gives
   `(1/5) · Σ_{|γ-T|≤1} xiOrderNat(ρ) ≤ Re(ξ'/ξ(2+iT) - A) ≤ K log T + ‖A‖`,
   hence the weighted count is `O(log T)`.

6. Distinct count follows from `xiOrderNat ρ ≥ 1` at each nontrivial zero.

## Status

LANDED. Depends on H8 (partial fraction), H9 (log-deriv bridge),
`logDerivZeta_bounded_of_right_of_one`, `gammaR_logDeriv_log_bound_at_two`.
Axiom footprint: `[propext, Classical.choice, Quot.sound]` plus transitive
`sorryAx` via H6/H8.
-/

open Complex Filter Topology

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helpers
-- ═══════════════════════════════════════════════════════════════════════════

/-- `(2 + iT) ∉ NontrivialZeros`: the real part is 2, but nontrivial zeros have
`0 < Re ρ < 1`. -/
private lemma two_plus_tI_notMem_NontrivialZeros (T : ℝ) :
    ((2 : ℂ) + (T : ℂ) * I) ∉ NontrivialZeros := by
  intro h
  have h_re : ((2 : ℂ) + (T : ℂ) * I).re = 2 := by simp
  have := h.2.1
  rw [h_re] at this
  linarith

/-- **Key per-ρ lower bound.** For `ρ ∈ NontrivialZeros` with `|ρ.im - T| ≤ 1`,
`Re(1/(2+iT - ρ) + 1/ρ) ≥ 1/5`. The `Re(1/ρ)` term is nonneg, and
`Re(1/(2+iT - ρ)) = (2-β)/((2-β)² + (T-γ)²) ≥ 1/5` since
`1 ≤ 2-β ≤ 2` and `(T-γ)² ≤ 1`. -/
private lemma short_window_re_zero_term_lower
    (T : ℝ) (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) (hγ : |ρ.im - T| ≤ 1) :
    (1/5 : ℝ) ≤ ((1 : ℂ) / ((2 : ℂ) + (T : ℂ) * I - ρ) + 1 / ρ).re := by
  set β := ρ.re with hβ_def
  set γ := ρ.im with hγ_def
  have hβ₀ : 0 < β := hρ.1
  have hβ₁ : β < 1 := hρ.2.1
  have hρ_eq : ρ = (β : ℂ) + (γ : ℂ) * I := by rw [hβ_def, hγ_def, Complex.re_add_im]
  rw [hρ_eq, Complex.add_re]
  have h_re_one_div_ρ_nn : 0 ≤ ((1 : ℂ) / ((β : ℂ) + (γ : ℂ) * I)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · show 0 ≤ ((β : ℂ) + (γ : ℂ) * I).re; simp [hβ₀.le]
    · exact Complex.normSq_nonneg _
  have h_re_one_div_ge : (1/5 : ℝ) ≤
      ((1 : ℂ) / ((2 : ℂ) + (T : ℂ) * I - ((β : ℂ) + (γ : ℂ) * I))).re := by
    have h_sub : (2 : ℂ) + (T : ℂ) * I - ((β : ℂ) + (γ : ℂ) * I) =
        ((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_sub, show (1 : ℂ) / (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * I) =
        (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * I)⁻¹ from by rw [one_div], Complex.inv_re]
    have h_re_eq : (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * I).re = 2 - β := by simp
    rw [h_re_eq]
    have h_normSq :
        Complex.normSq (((2 - β : ℝ) : ℂ) + ((T - γ : ℝ) : ℂ) * I) = (2-β)^2 + (T-γ)^2 := by
      rw [Complex.normSq_add_mul_I]
    rw [h_normSq]
    have hβ_sub : (1 : ℝ) ≤ 2 - β := by linarith
    have hβ_sub_le : 2 - β ≤ 2 := by linarith
    have hγT_sq : (T - γ)^2 ≤ 1 := by
      have hle : |T - γ| ≤ 1 := by
        rw [show T - γ = -(γ - T) from by ring, abs_neg]; exact hγ
      nlinarith [sq_abs (T - γ), abs_nonneg (T - γ)]
    have h_sum_pos : 0 < (2-β)^2 + (T-γ)^2 := by nlinarith
    have h_sum_le : (2-β)^2 + (T-γ)^2 ≤ 5 := by nlinarith
    rw [le_div_iff₀ h_sum_pos]; nlinarith [sq_nonneg (T - γ)]
  linarith

/-- **Upper bound on `‖ξ'/ξ(2+iT)‖` by `C · log T` for `T ≥ 2`.** Assembles:
* `logDerivZeta_bounded_of_right_of_one` (uniform `ζ'/ζ` bound on `Re s ≥ 3/2`),
* `gammaR_logDeriv_log_bound_at_two` (digamma-via-reflection log bound),
via H9 (`riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ`). -/
private lemma xi_logDeriv_norm_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ‖deriv riemannXi ((2 : ℂ) + (T : ℂ) * I) /
        riemannXi ((2 : ℂ) + (T : ℂ) * I)‖ ≤ C * Real.log T := by
  obtain ⟨Cζ, hCζ_nn, hCζ_bd⟩ :=
    ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one (3/2) (by norm_num)
  obtain ⟨CΓ, hCΓ_nn, hCΓ_bd⟩ :=
    ZD.WeilPositivity.Contour.gammaR_logDeriv_log_bound_at_two
  set K : ℝ := (Cζ + 2 + CΓ) / Real.log 2 + 2 * CΓ with hK_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK_nn : 0 ≤ K := by
    rw [hK_def]
    have h1 : 0 ≤ (Cζ + 2 + CΓ) / Real.log 2 := div_nonneg (by linarith) hlog2_pos.le
    positivity
  refine ⟨K, hK_nn, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  set s : ℂ := (2 : ℂ) + (T : ℂ) * I with hs_def
  have hs_re : s.re = 2 := by simp [hs_def]
  have hs_re_gt_1 : 1 < s.re := by rw [hs_re]; norm_num
  have h9 := ZD.riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ s hs_re_gt_1
  have h_xi_eq : deriv riemannXi s / riemannXi s =
      deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
    linear_combination -h9
  rw [h_xi_eq]
  have h_bound_ζ : ‖deriv riemannZeta s / riemannZeta s‖ ≤ Cζ := by
    apply hCζ_bd; rw [hs_re]; norm_num
  have h_s_norm_ge : (2 : ℝ) ≤ ‖s‖ := by
    have h_normsq : Complex.normSq s = 4 + T^2 := by
      rw [hs_def]
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im]
      ring
    have h_norm_sq : ‖s‖^2 = Complex.normSq s := Complex.sq_norm _
    have h_ge_4 : (4 : ℝ) ≤ ‖s‖^2 := by rw [h_norm_sq, h_normsq]; nlinarith [sq_nonneg T]
    nlinarith [norm_nonneg s]
  have h_bound_s_inv : ‖(1 : ℂ) / s‖ ≤ 1 := by
    have h_s_ne : s ≠ 0 := by
      intro heq; have := congrArg Complex.re heq; rw [hs_re] at this; simp at this
    have h_s_pos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr h_s_ne
    rw [norm_div, norm_one, div_le_iff₀ h_s_pos, one_mul]
    linarith
  have h_sm1_re : (s - 1).re = 1 := by simp [hs_def]; norm_num
  have h_sm1_ne : s - 1 ≠ 0 := by
    intro heq; have := congrArg Complex.re heq; rw [h_sm1_re] at this; simp at this
  have h_sm1_norm_ge : (1 : ℝ) ≤ ‖s - 1‖ := by
    calc (1 : ℝ) = |(s-1).re| := by rw [h_sm1_re]; simp
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have h_bound_sm1_inv : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    have h_sm1_pos : (0 : ℝ) < ‖s - 1‖ := norm_pos_iff.mpr h_sm1_ne
    rw [norm_div, norm_one, div_le_iff₀ h_sm1_pos, one_mul]
    exact h_sm1_norm_ge
  have h_bound_gamma : ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * (1 + Real.log (1 + |T|)) := by
    rw [logDeriv_apply]; exact hCΓ_bd T
  have h_triangle :
      ‖deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s‖ ≤
        Cζ + 1 + 1 + CΓ * (1 + Real.log (1 + |T|)) := by
    have h1 := norm_add_le
      (deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1))
      (logDeriv Complex.Gammaℝ s)
    have h2 := norm_add_le
      (deriv riemannZeta s / riemannZeta s + 1 / s) ((1 : ℂ) / (s - 1))
    have h3 := norm_add_le
      (deriv riemannZeta s / riemannZeta s) ((1 : ℂ) / s)
    linarith
  refine h_triangle.trans ?_
  have h_abs_T : |T| = T := abs_of_pos hT_pos
  have h_log_bound : Real.log (1 + |T|) ≤ 2 * Real.log T := by
    rw [h_abs_T]
    have h_1pT : 1 + T ≤ T^2 := by nlinarith
    have h_pos : 0 < 1 + T := by linarith
    calc Real.log (1 + T) ≤ Real.log (T^2) := Real.log_le_log h_pos h_1pT
      _ = 2 * Real.log T := by rw [Real.log_pow]; ring
  have h_ge_div : 1 ≤ Real.log T / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos, one_mul]
    exact Real.log_le_log (by norm_num) hT
  have h_one_plus : 1 + Real.log (1 + |T|) ≤ Real.log T / Real.log 2 + 2 * Real.log T := by
    linarith
  calc Cζ + 1 + 1 + CΓ * (1 + Real.log (1 + |T|))
      ≤ Cζ + 2 + CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) := by
        have h1 : CΓ * (1 + Real.log (1 + |T|)) ≤
            CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) :=
          mul_le_mul_of_nonneg_left h_one_plus hCΓ_nn
        linarith
    _ ≤ (Cζ + 2) * (Real.log T / Real.log 2) +
          CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) := by
        have h_Cζ_nn : 0 ≤ Cζ + 2 := by linarith
        have : Cζ + 2 ≤ (Cζ + 2) * (Real.log T / Real.log 2) := by
          calc Cζ + 2 = (Cζ + 2) * 1 := by ring
            _ ≤ (Cζ + 2) * (Real.log T / Real.log 2) :=
                mul_le_mul_of_nonneg_left h_ge_div h_Cζ_nn
        linarith
    _ = ((Cζ + 2 + CΓ) / Real.log 2 + 2 * CΓ) * Real.log T := by field_simp; ring
    _ = K * Real.log T := by rw [hK_def]

/-- **Summability of the weighted partial-fraction tsum** at `s ∉ NontrivialZeros`.
Derived from `summable_logDeriv_multi` via `Summable.sigma` on the per-factor
reduction `logDeriv (factor) = s/(ρ·(s-ρ))` and the algebraic identity
`s/(ρ·(s-ρ)) = 1/(s-ρ) + 1/ρ`. -/
private lemma summable_weighted_partial_fraction {s : ℂ} (hs : s ∉ NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
  have h_multi_summ := summable_logDeriv_multi hs
  have h_eq : ∀ p : MultiZeroIdx,
      logDeriv (fun w => 1 + xiWeierstrassTerm p.1.val w) s =
      s / (p.1.val * (s - p.1.val)) := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq; have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
    exact logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ
  have h_sigma_summ : Summable (fun p : MultiZeroIdx =>
      s / (p.1.val * (s - p.1.val))) := h_multi_summ.congr h_eq
  have h_sigma := h_sigma_summ.sigma
  refine h_sigma.congr ?_
  intro ρ
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq; have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
    rw [heq] at hre; simp at hre
  have hs_ne_ρ : s - ρ.val ≠ 0 := by
    intro heq; have : s = ρ.val := by linear_combination heq
    exact hs (this ▸ ρ.property)
  have h_simp : (fun c : Fin (xiOrderNat ρ.val) => s / ((⟨ρ, c⟩ : MultiZeroIdx).1.val *
      (s - (⟨ρ, c⟩ : MultiZeroIdx).1.val))) = fun _ : Fin (xiOrderNat ρ.val) =>
      s / (ρ.val * (s - ρ.val)) := by funext c; rfl
  rw [h_simp, tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h_alg : s / (ρ.val * (s - ρ.val)) = 1 / (s - ρ.val) + 1 / ρ.val := by field_simp; ring
  rw [h_alg, nsmul_eq_mul]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Main H10 + corollary
-- ═══════════════════════════════════════════════════════════════════════════

/-- **H10**: Multiplicity-weighted short-window zero count. -/
theorem nontrivialZeros_short_window_weighted_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 1)).toFinset.filter
        (fun ρ => |ρ.im - T| ≤ 1)),
        (ZD.xiOrderNat ρ : ℝ)) ≤ C * Real.log T := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  obtain ⟨K, hK_nn, hK_bd⟩ := xi_logDeriv_norm_log_bound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := 5 * (K + (‖A‖ + 1) / Real.log 2) with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    have : 0 < (‖A‖ + 1) / Real.log 2 :=
      div_pos (by linarith [norm_nonneg A]) hlog2_pos
    positivity
  refine ⟨C, hC_pos, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have h_ge_div : 1 ≤ Real.log T / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos, one_mul]
    exact Real.log_le_log (by norm_num) hT
  set s : ℂ := (2 : ℂ) + (T : ℂ) * I with hs_def
  have hs_notMem : s ∉ NontrivialZeros := two_plus_tI_notMem_NontrivialZeros T
  have h8 := hA s hs_notMem
  have h_summ := summable_weighted_partial_fraction hs_notMem
  have h8' : deriv riemannXi s / riemannXi s - A =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
    rw [h8]; ring
  have h_re : Complex.re (deriv riemannXi s / riemannXi s - A) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        Complex.re ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    rw [h8']; exact Complex.re_tsum h_summ
  have h_term_eq : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      Complex.re ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) =
      (ZD.xiOrderNat ρ.val : ℝ) * Complex.re (1 / (s - ρ.val) + 1 / ρ.val) := by
    intro ρ; simp [Complex.mul_re]
  have h_term_nn : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      0 ≤ Complex.re ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    intro ρ
    rw [h_term_eq]
    apply mul_nonneg (Nat.cast_nonneg _)
    have hρ_re_pos : 0 < ρ.val.re := ρ.property.1
    have hρ_re_lt : ρ.val.re < 1 := ρ.property.2.1
    rw [Complex.add_re]
    apply add_nonneg
    · rw [one_div, Complex.inv_re]
      apply div_nonneg _ (Complex.normSq_nonneg _)
      show 0 ≤ (s - ρ.val).re
      rw [Complex.sub_re]
      have : s.re = 2 := by simp [hs_def]
      linarith
    · rw [one_div, Complex.inv_re]
      exact div_nonneg hρ_re_pos.le (Complex.normSq_nonneg _)
  have h_summ_re : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      Complex.re ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))) :=
    Complex.reCLM.summable h_summ
  set F : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 1)).toFinset.filter
      (fun ρ => |ρ.im - T| ≤ 1)) with hF_def
  have hF_in : ∀ ρ ∈ F, ρ ∈ NontrivialZeros := by
    intro ρ hρ
    rw [hF_def, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    exact hρ.1.1
  have hF_window : ∀ ρ ∈ F, |ρ.im - T| ≤ 1 := by
    intro ρ hρ
    rw [hF_def, Finset.mem_filter] at hρ
    exact hρ.2
  let g : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ := fun ρ =>
    Complex.re ((ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val))
  let f : {ρ : ℂ // ρ ∈ F} → {ρ : ℂ // ρ ∈ NontrivialZeros} :=
    fun ρ => ⟨ρ.val, hF_in ρ.val ρ.property⟩
  have h_inj_f : Function.Injective f := by
    intro a b h
    have : a.val = b.val := by
      have := congrArg Subtype.val h
      simpa [f] using this
    exact Subtype.ext this
  set G : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} := F.attach.image f with hG_def
  have h_lower_G : ∀ ρ ∈ G, (1/5 : ℝ) * (ZD.xiOrderNat ρ.val : ℝ) ≤ g ρ := by
    intro ρ hρ_G
    rw [hG_def, Finset.mem_image] at hρ_G
    obtain ⟨a, haF, hfa⟩ := hρ_G
    have ha_window : |a.val.im - T| ≤ 1 := hF_window a.val a.property
    simp only [g]
    rw [h_term_eq ρ]
    have h_re_lower : (1/5 : ℝ) ≤ Complex.re (1 / (s - ρ.val) + 1 / ρ.val) := by
      have ha_in : a.val ∈ NontrivialZeros := hF_in a.val a.property
      have : ρ.val = a.val := by
        have := congrArg Subtype.val hfa
        simpa [f] using this.symm
      rw [this]
      exact short_window_re_zero_term_lower T a.val ha_in ha_window
    have h_xi_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_sum_lower : ∑ ρ ∈ G, (1/5 : ℝ) * (ZD.xiOrderNat ρ.val : ℝ) ≤ ∑ ρ ∈ G, g ρ :=
    Finset.sum_le_sum h_lower_G
  have h_sum_le_tsum : ∑ ρ ∈ G, g ρ ≤ ∑' ρ, g ρ :=
    sum_le_hasSum G (fun ρ _ => h_term_nn ρ) h_summ_re.hasSum
  have h_tsum_val : ∑' ρ, g ρ = Complex.re (deriv riemannXi s / riemannXi s - A) := by
    simp only [g]; rw [h_re]
  have h_re_le_norm : Complex.re (deriv riemannXi s / riemannXi s - A) ≤
      ‖deriv riemannXi s / riemannXi s - A‖ := Complex.re_le_norm _
  have h_norm_diff_le : ‖deriv riemannXi s / riemannXi s - A‖ ≤
      ‖deriv riemannXi s / riemannXi s‖ + ‖A‖ := norm_sub_le _ _
  have h_xi_bd : ‖deriv riemannXi s / riemannXi s‖ ≤ K * Real.log T := hK_bd T hT
  have h_tsum_bd : ∑' ρ, g ρ ≤ K * Real.log T + ‖A‖ := by
    calc ∑' ρ, g ρ = Complex.re (deriv riemannXi s / riemannXi s - A) := h_tsum_val
      _ ≤ ‖deriv riemannXi s / riemannXi s - A‖ := h_re_le_norm
      _ ≤ ‖deriv riemannXi s / riemannXi s‖ + ‖A‖ := h_norm_diff_le
      _ ≤ K * Real.log T + ‖A‖ := by linarith
  have h_sum_F_G : ∑ ρ ∈ F, (ZD.xiOrderNat ρ : ℝ) =
      ∑ ρ ∈ G, (ZD.xiOrderNat ρ.val : ℝ) := by
    show ∑ ρ ∈ F, (ZD.xiOrderNat ρ : ℝ) = ∑ ρ ∈ F.attach.image f, (ZD.xiOrderNat ρ.val : ℝ)
    rw [Finset.sum_image (fun a _ b _ h => h_inj_f h)]
    rw [← Finset.sum_attach F (fun ρ => (ZD.xiOrderNat ρ : ℝ))]
  rw [h_sum_F_G]
  have h_half_sum :
      (1/5 : ℝ) * ∑ ρ ∈ G, (ZD.xiOrderNat ρ.val : ℝ) ≤ ∑ ρ ∈ G, g ρ := by
    rw [Finset.mul_sum]
    exact h_sum_lower
  have h_final : ∑ ρ ∈ G, (ZD.xiOrderNat ρ.val : ℝ) ≤ 5 * (K * Real.log T + ‖A‖) := by
    have := h_half_sum.trans (h_sum_le_tsum.trans h_tsum_bd)
    linarith
  refine h_final.trans ?_
  have h_A_le : 5 * ‖A‖ ≤ 5 * ((‖A‖ + 1) / Real.log 2 * Real.log T) := by
    have h_log_ge : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have : ‖A‖ ≤ (‖A‖ + 1) / Real.log 2 * Real.log T := by
      have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
      calc ‖A‖ = ‖A‖ * 1 := by ring
        _ ≤ ‖A‖ * (Real.log T / Real.log 2) :=
          mul_le_mul_of_nonneg_left h_ge_div hA_nn
        _ ≤ (‖A‖ + 1) / Real.log 2 * Real.log T := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
          have hle : ‖A‖ ≤ ‖A‖ + 1 := by linarith
          exact mul_le_mul_of_nonneg_right hle
            (by positivity : (0:ℝ) ≤ Real.log T / Real.log 2)
    linarith
  calc 5 * (K * Real.log T + ‖A‖)
      = 5 * K * Real.log T + 5 * ‖A‖ := by ring
    _ ≤ 5 * K * Real.log T + 5 * ((‖A‖ + 1) / Real.log 2 * Real.log T) := by linarith
    _ = (5 * (K + (‖A‖ + 1) / Real.log 2)) * Real.log T := by ring
    _ = C * Real.log T := by rw [hC_def]

/-- **H10' (corollary)**: Distinct short-window zero count. Follows from the
weighted version via `xiOrderNat ρ ≥ 1` at each nontrivial zero. -/
theorem nontrivialZeros_short_window_distinct_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 1)).toFinset.filter
        (fun ρ => |ρ.im - T| ≤ 1)).card : ℝ) ≤ C * Real.log T := by
  obtain ⟨C, hC_pos, hC_bd⟩ := nontrivialZeros_short_window_weighted_count_bound
  refine ⟨C, hC_pos, fun T hT => ?_⟩
  set F : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 1)).toFinset.filter
      (fun ρ => |ρ.im - T| ≤ 1)) with hF_def
  have h_card_le : (F.card : ℝ) ≤ ∑ ρ ∈ F, (ZD.xiOrderNat ρ : ℝ) := by
    rw [show (F.card : ℝ) = ∑ _ ∈ F, (1 : ℝ) from by simp]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hρ_in : ρ ∈ NontrivialZeros := by
      rw [hF_def, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      exact hρ.1.1
    have h_pos : 0 < ZD.xiOrderNat ρ := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ_in
    exact_mod_cast h_pos
  exact h_card_le.trans (hC_bd T hT)

end ZD
