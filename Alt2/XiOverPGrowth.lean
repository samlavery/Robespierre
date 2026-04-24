import Mathlib
import RequestProject.ZeroCountJensen
import RequestProject.XiProductMult
import RequestProject.XiHadamardLog
import RequestProject.XiOrderSummable
import RequestProject.ZetaBound

/-!
# Unconditional mean-type growth bound on `xiOverP = ξ / xiProductMult`

This file discharges the growth hypothesis `hG` used throughout the Hadamard
factorization chain.  The final export, `xiOverP_growth_meanType`, is
UNCONDITIONAL: no hypotheses beyond what the project already proves.

## Strategy

`xiOverP` is entire and zero-free (`xiOverP_ne_zero`).  Since it is zero-free,
`log ‖xiOverP‖` is harmonic on all of ℂ.

The chain uses **Nevanlinna theory** (circle averages, proximity function) +
**Poisson representation** to convert an average bound on log-modulus to a
pointwise bound:

```
Step A   pointwise upper bound on ‖ξ(z)‖           (from ZeroCountJensen.xi_order_one_log_bound)
Step B   pointwise upper bound on ‖xiProductMult(z)‖ (direct canonical product estimate)
Step C   Jensen's formula on xiProductMult          (MeromorphicOn.circleAverage_log_norm)
Step D   proximity functions m(R, ξ), m(R, P), m(R, 1/P) in O(R log²R)
Step E   m(R, xiOverP) ≤ m(R, ξ) + m(R, 1/P) = O(R log²R)
Step F   Poisson: pointwise log‖xiOverP‖ ≤ O(|z| log²(|z|+2))
Step G   Exponential form: ‖xiOverP z‖ ≤ exp(C ‖z‖ log²(‖z‖+2) + D)
```

The `log²` factor (rather than tight `log`) avoids the Abel-summation step
needed for the sharp Jensen bound.  The looser form is sufficient because the
downstream `secondDeriv_zero_of_meanType_logSq` helper (generalized from the
existing `secondDeriv_zero_of_meanType`) only requires `(growth)/R² → 0`, and
`log²R / R → 0`.

## Axiom footprint

`[propext, Classical.choice, Quot.sound]` after all sorries are filled.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step A: pointwise upper bound on ‖ξ(z)‖
-- ═══════════════════════════════════════════════════════════════════════════

/-- Pointwise upper bound on `log ‖ξ(z)‖` in mean-type-1 form.
Reformulation of `ZD.ZeroCount.xi_order_one_log_bound` into a functional bound
that holds for all `z` (not just `‖z‖ ≤ R`), by specialising `R := ‖z‖`. -/
theorem riemannXi_pointwise_meanType_bound :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log (‖riemannXi z‖ + 1) ≤ C * ‖z‖ * Real.log (‖z‖ + 2) + D := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hBound⟩ := ZD.ZeroCount.xi_order_one_log_bound
  obtain ⟨M, hM_nn, hM⟩ := ZD.ZeroCount.riemannXi_bounded_on_closedBall R₀
  refine ⟨C₀, Real.log (M + 1), fun z => ?_⟩
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have hlog_z_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
  have hC₀_nn : 0 ≤ C₀ := le_of_lt hC₀_pos
  have hlogM_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  by_cases hz_small : ‖z‖ ≤ R₀
  · have h_xi_bd : ‖riemannXi z‖ ≤ M := hM z (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz_small)
    have h_log_le : Real.log (‖riemannXi z‖ + 1) ≤ Real.log (M + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h_lhs_nn : 0 ≤ C₀ * ‖z‖ * Real.log (‖z‖ + 2) :=
      mul_nonneg (mul_nonneg hC₀_nn hz_nn) hlog_z_nn
    linarith
  · have hz_gt : ‖z‖ > R₀ := not_le.mp hz_small
    have hRpos : R₀ ≤ ‖z‖ := le_of_lt hz_gt
    have h_xi_bd := hBound ‖z‖ hRpos z (le_refl _)
    have hz_pos : 0 < ‖z‖ := lt_trans hR₀_pos hz_gt
    have h_log_z_le : Real.log ‖z‖ ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log hz_pos (by linarith)
    have h1 : C₀ * ‖z‖ * Real.log ‖z‖ ≤ C₀ * ‖z‖ * Real.log (‖z‖ + 2) := by
      apply mul_le_mul_of_nonneg_left h_log_z_le
      exact mul_nonneg hC₀_nn hz_nn
    linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step B: pointwise upper bound on canonical product
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Dyadic sub-lemmas for Step B

The pointwise bound on `log ‖P(z)‖` reduces to two classical dyadic-shell
estimates on weighted sums of zero moduli.  Each follows the template in
`XiOrderSummable.summable_xiOrderNat_div_norm_sq_nontrivialZeros`.
-/

/-- **Sub-lemma 1 (tail)**: `∑_{‖ρ‖ > R} n_ρ / ‖ρ‖² ≤ C · log R / R`.  Dyadic
shells indexed by `k ≥ 0` with shell `2^k R < ‖ρ‖ ≤ 2^{k+1} R`.  Per-shell
bound `N(2^{k+1} R) / (2^k R)² ≤ C · 2 · log(2^{k+1} R) / (2^k R)`.  Summed
via `∑ (k + log R) / 2^k = O(log R)` gives `O(log R / R)`. -/
theorem xiOrderNat_div_norm_sq_tail_bound :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros}),
        (∀ ρ ∈ S, R < ‖ρ.val‖) →
        (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤
          C * Real.log R / R := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hWB⟩ := xi_weighted_zero_count_disk_bound
  have hSumm := summable_xiOrderNat_div_norm_sq_nontrivialZeros
  set T_glob : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ T_glob := by
    rw [hT_def]; exact tsum_nonneg (fun ρ => by positivity)
  have h_summ_geom : Summable (fun k : ℕ => ((k : ℝ) + 2) / 2^k) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) * (1/2)^k) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (show ‖(1/2:ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
      convert this using 1; funext k; simp [pow_one]
    have h2 : Summable (fun k : ℕ => (1/2 : ℝ)^k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h_sum : Summable (fun k : ℕ => (k : ℝ) * (1/2)^k + 2 * (1/2 : ℝ)^k) :=
      h1.add (h2.mul_left 2)
    convert h_sum using 1
    funext k
    have h_eq : (1/2 : ℝ)^k = 1/2^k := by rw [div_pow, one_pow]
    rw [h_eq]; field_simp
  set S_geom : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) / 2^k with hSgeom_def
  have hSgeom_nn : 0 ≤ S_geom := tsum_nonneg (fun k => by positivity)
  set R_fence : ℝ := max 2 R₀ with hRf_def
  have hRf_ge_two : (2 : ℝ) ≤ R_fence := le_max_left _ _
  have hRf_ge_R₀ : R₀ ≤ R_fence := le_max_right _ _
  have hRf_pos : 0 < R_fence := by linarith
  set C_dyad : ℝ := 2 * C₀ * S_geom with hCd_def
  have hCd_nn : 0 ≤ C_dyad := by rw [hCd_def]; positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C_glob : ℝ := T_glob * R_fence / Real.log 2 with hCg_def
  have hCg_nn : 0 ≤ C_glob := by rw [hCg_def]; positivity
  set C : ℝ := C_glob + C_dyad with hC_def
  refine ⟨C, ?_⟩
  intro R hR S hS_far
  have hR_pos : 0 < R := by linarith
  have hlog_R_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog_R_nn : 0 ≤ Real.log R := hlog_R_pos.le
  have hlog2_le_logR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_sum_nn : 0 ≤ ∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 :=
    Finset.sum_nonneg (fun ρ _ => by positivity)
  have h_sum_le_T : (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ T_glob := by
    rw [hT_def]; exact Summable.sum_le_tsum _ (fun i _ => by positivity) hSumm
  by_cases hR_case : R_fence ≤ R
  · have hR_ge_R₀ : R₀ ≤ R := le_trans hRf_ge_R₀ hR_case
    let kf : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℕ := fun ρ =>
      if h : (1 : ℝ) ≤ ‖ρ.val‖ / R
      then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
      else 0
    have h_kf_prop :
        ∀ ρ ∈ S, (2 : ℝ) ^ kf ρ * R ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 1) * R := by
      intro ρ hρ
      have hgt : R < ‖ρ.val‖ := hS_far ρ hρ
      have h_ratio : 1 ≤ ‖ρ.val‖ / R := by
        rw [le_div_iff₀ hR_pos]; linarith
      simp only [kf, dif_pos h_ratio]
      have ⟨h1, h2⟩ := (exists_nat_pow_near h_ratio (by norm_num : (1:ℝ) < 2)).choose_spec
      refine ⟨?_, ?_⟩
      · rwa [le_div_iff₀ hR_pos] at h1
      · rwa [div_lt_iff₀ hR_pos] at h2
    set K_max : ℕ := S.sup kf + 1 with hKmax_def
    have h_kf_le : ∀ ρ ∈ S, kf ρ < K_max := fun ρ hρ => by
      have := Finset.le_sup (f := kf) hρ
      omega
    have h_per_elem :
        ∀ ρ ∈ S,
          (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤
          (ZD.xiOrderNat ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 := by
      intro ρ hρ
      have ⟨h_lb, _⟩ := h_kf_prop ρ hρ
      have h_sq_pos : (0 : ℝ) < ((2 : ℝ) ^ kf ρ * R) ^ 2 := by positivity
      have hρ_pos : 0 < ‖ρ.val‖ := by linarith [hS_far ρ hρ]
      have hρ_sq_pos : (0 : ℝ) < ‖ρ.val‖ ^ 2 := by positivity
      have h_sq_le : ((2 : ℝ) ^ kf ρ * R) ^ 2 ≤ ‖ρ.val‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) h_lb 2
      apply div_le_div_of_nonneg_left (by positivity) h_sq_pos h_sq_le
    have h_shell_bound : ∀ k : ℕ,
        (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)) ≤
        C₀ * ((2 : ℝ) ^ (k + 1) * R) * Real.log ((2 : ℝ) ^ (k + 1) * R) := by
      intro k
      have hR_target_ge : R₀ ≤ (2 : ℝ) ^ (k + 1) * R := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        have : R ≤ (2 : ℝ) ^ (k + 1) * R := by nlinarith
        linarith
      apply hWB ((2 : ℝ) ^ (k + 1) * R) hR_target_ge
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have ⟨_, h_ub⟩ := h_kf_prop ρ hρ.1
      rw [hρ.2] at h_ub
      linarith
    have h_shell_bound_scaled : ∀ k : ℕ,
        (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)) / ((2:ℝ)^k * R)^2 ≤
        2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) := by
      intro k
      set x : ℝ := ∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)
      have hx_nn : 0 ≤ x := Finset.sum_nonneg (fun ρ _ => Nat.cast_nonneg _)
      have h_bd : x ≤ C₀ * ((2:ℝ)^(k+1) * R) * Real.log ((2:ℝ)^(k+1) * R) := h_shell_bound k
      have h_log_expand : Real.log ((2:ℝ)^(k+1) * R) = (k+1 : ℝ) * Real.log 2 + Real.log R := by
        rw [Real.log_mul (by positivity) (by linarith)]
        rw [Real.log_pow]; push_cast; ring
      have h_log_le : (k+1 : ℝ) * Real.log 2 + Real.log R ≤ (k+2) * Real.log R := by
        have hk_nn : 0 ≤ (k+1 : ℝ) := by positivity
        nlinarith
      have h_bd' : x ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) := by
        rw [h_log_expand] at h_bd
        have h_pos : 0 ≤ C₀ * ((2:ℝ)^(k+1) * R) := by positivity
        calc x ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+1 : ℝ) * Real.log 2 + Real.log R) := h_bd
          _ ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) :=
              mul_le_mul_of_nonneg_left h_log_le h_pos
      have h2R_sq_pos : (0 : ℝ) < ((2 : ℝ) ^ k * R) ^ 2 := by positivity
      calc x / ((2:ℝ)^k * R)^2
          ≤ C₀ * ((2:ℝ)^(k+1) * R) * ((k+2 : ℝ) * Real.log R) / ((2:ℝ)^k * R)^2 := by gcongr
        _ = 2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) := by
            have h2k1 : (2 : ℝ) ^ (k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
            rw [h2k1]; field_simp
    have h_dyad_sum :
        (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤
        C_dyad * Real.log R / R := by
      calc (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
          ≤ ∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 :=
            Finset.sum_le_sum h_per_elem
        _ = ∑ k ∈ Finset.range K_max,
              ∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
                (ZD.xiOrderNat ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2 := by
            rw [← Finset.sum_fiberwise_of_maps_to
              (t := Finset.range K_max) (g := kf)
              (f := fun ρ => (ZD.xiOrderNat ρ.val : ℝ) / ((2 : ℝ) ^ kf ρ * R) ^ 2)]
            intro ρ hρ
            exact Finset.mem_range.mpr (h_kf_le ρ hρ)
        _ = ∑ k ∈ Finset.range K_max,
              (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)) /
                ((2 : ℝ) ^ k * R) ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl; intro ρ hρ
            simp only [Finset.mem_filter] at hρ
            rw [hρ.2]
        _ ≤ ∑ k ∈ Finset.range K_max,
              2 * C₀ * Real.log R / R * ((k + 2 : ℝ) / 2^k) :=
            Finset.sum_le_sum (fun k _ => h_shell_bound_scaled k)
        _ = 2 * C₀ * Real.log R / R * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 2) / 2^k := by
            rw [← Finset.mul_sum]
        _ ≤ 2 * C₀ * Real.log R / R * S_geom := by
            have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 2) / 2^k := fun k => by positivity
            have h_bd : (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2) / 2^k) ≤ S_geom :=
              Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ_geom
            have h_outer_nn : 0 ≤ 2 * C₀ * Real.log R / R := by positivity
            exact mul_le_mul_of_nonneg_left h_bd h_outer_nn
        _ = C_dyad * Real.log R / R := by rw [hCd_def]; ring
    have h_expand : C * Real.log R / R = C_glob * Real.log R / R + C_dyad * Real.log R / R := by
      rw [hC_def]; ring
    have h_glob_nn : 0 ≤ C_glob * Real.log R / R := by positivity
    linarith
  · push_neg at hR_case
    have hR_lt_Rf : R < R_fence := hR_case
    have hR_le_Rf : R ≤ R_fence := hR_lt_Rf.le
    have h_Rf_logR_ge : R * Real.log 2 ≤ R_fence * Real.log R := by
      have h1 : R * Real.log 2 ≤ R * Real.log R :=
        mul_le_mul_of_nonneg_left hlog2_le_logR hR_pos.le
      have h2 : R * Real.log R ≤ R_fence * Real.log R :=
        mul_le_mul_of_nonneg_right hR_le_Rf hlog_R_nn
      linarith
    have h_Cg : C_glob * Real.log R / R = T_glob * R_fence * Real.log R / (Real.log 2 * R) := by
      rw [hCg_def]; ring
    have h_Cg_ge_T : T_glob ≤ C_glob * Real.log R / R := by
      rw [h_Cg]
      have h_div_ge_1 : 1 ≤ R_fence * Real.log R / (Real.log 2 * R) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc T_glob = T_glob * 1 := by ring
        _ ≤ T_glob * (R_fence * Real.log R / (Real.log 2 * R)) :=
            mul_le_mul_of_nonneg_left h_div_ge_1 hT_nn
        _ = T_glob * R_fence * Real.log R / (Real.log 2 * R) := by ring
    have h_expand : C * Real.log R / R = C_glob * Real.log R / R + C_dyad * Real.log R / R := by
      rw [hC_def]; ring
    have h_dyad_nn : 0 ≤ C_dyad * Real.log R / R := by positivity
    linarith

/-- **Sub-lemma 2 (partial sum)**: `∑_{‖ρ‖ ≤ R} n_ρ / ‖ρ‖ ≤ C · (log R)²`.
Dyadic shells with `2 · 2^k ≤ ‖ρ‖ < 2 · 2^{k+1}`.  Per-shell sum
`n_ρ/‖ρ‖ ≤ weighted_count(2·2^{k+1}) / (2 · 2^k) ≤ 2C · log(2^{k+2})`.
Summed over `k = 0, …, ⌊log₂ R⌋`: `O((log R)²)`. -/
theorem xiOrderNat_div_norm_partial_sum_bound :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros}),
        (∀ ρ ∈ S, ‖ρ.val‖ ≤ R) →
        (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
          C * (Real.log R) ^ 2 := by
  obtain ⟨C₃, hC₃_pos, R₀_step3, _, hBound⟩ := ZD.xi_weighted_zero_count_disk_bound
  set M_low : ℝ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite R₀_step3).toFinset.sum
      (fun ρ => (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖) with hM_low_def
  have hM_low_nn : 0 ≤ M_low := by
    apply Finset.sum_nonneg
    intro ρ _
    exact div_nonneg (by positivity) (by positivity)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC₃_nn : 0 ≤ C₃ := hC₃_pos.le
  refine ⟨M_low / (Real.log 2)^2 + 18 * C₃ / Real.log 2, ?_⟩
  intro R hR S hS_bd
  have hR_pos : (0 : ℝ) < R := by linarith
  have hR_log_ge_log2 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hR_log_pos : 0 < Real.log R := lt_of_lt_of_le hlog2_pos hR_log_ge_log2
  have hR_log_nn : 0 ≤ Real.log R := hR_log_pos.le
  have h_two_le_norm : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, (2 : ℝ) ≤ ‖ρ.val‖ := fun ρ => by
    have hρ := ρ.property
    have hzero : riemannZeta ρ.val = 0 := hρ.2.2
    have htriv : ∀ n : ℕ, ρ.val ≠ -2 * ((n : ℂ) + 1) := fun n hk => by
      have h_re := congrArg Complex.re hk
      simp at h_re
      have hpos : (0:ℝ) < ρ.val.re := hρ.1
      linarith
    have hIm_ge : 2 ≤ |ρ.val.im| := riemannZeta_nontrivial_zero_im_ge_two hzero htriv
    exact le_trans hIm_ge (Complex.abs_im_le_norm _)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => ‖ρ.val‖ ≤ R₀_step3)]
  have h_lo_bound :
      (∑ ρ ∈ S.filter (fun ρ => ‖ρ.val‖ ≤ R₀_step3),
        (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤ M_low := by
    rw [hM_low_def,
        show (∑ ρ ∈ S.filter (fun ρ => ‖ρ.val‖ ≤ R₀_step3),
              (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) =
            ∑ ρ ∈ (S.filter (fun ρ => ‖ρ.val‖ ≤ R₀_step3)).image Subtype.val,
                (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ from ?_]
    swap
    · rw [Finset.sum_image]
      intro x _ y _ h; exact Subtype.val_injective h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
      simp only [Finset.mem_filter] at hρ'_in
      simp only [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · subst hρ'_eq; exact ρ'.property
      · rw [Metric.mem_closedBall, dist_zero_right]
        subst hρ'_eq; exact hρ'_in.2
    · intros; positivity
  set S_hi : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
    S.filter (fun ρ => ¬ ‖ρ.val‖ ≤ R₀_step3) with hShi_def
  have h_hi_gt_R0 : ∀ ρ ∈ S_hi, R₀_step3 < ‖ρ.val‖ := by
    intro ρ hρ
    simp only [hShi_def, Finset.mem_filter, not_le] at hρ
    exact hρ.2
  have h_hi_le_R : ∀ ρ ∈ S_hi, ‖ρ.val‖ ≤ R := by
    intro ρ hρ
    simp only [hShi_def, Finset.mem_filter] at hρ
    exact hS_bd ρ hρ.1
  let kf : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℕ := fun ρ =>
    if h : (1 : ℝ) ≤ ‖ρ.val‖ / 2
    then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
    else 0
  have h_kf_spec : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (2 : ℝ) ^ (kf ρ) ≤ ‖ρ.val‖ / 2 ∧ ‖ρ.val‖ / 2 < (2 : ℝ) ^ (kf ρ + 1) := by
    intro ρ
    have h2 := h_two_le_norm ρ
    have h1 : (1 : ℝ) ≤ ‖ρ.val‖ / 2 := by linarith
    simp only [kf, dif_pos h1]
    exact (exists_nat_pow_near h1 (by norm_num : (1:ℝ) < 2)).choose_spec
  have h_norm_ge : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (2 : ℝ) ^ (kf ρ + 1) ≤ ‖ρ.val‖ := by
    intro ρ
    have ⟨h1, _⟩ := h_kf_spec ρ
    rw [pow_succ]; linarith
  have h_norm_lt : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 2) := by
    intro ρ
    have ⟨_, h2⟩ := h_kf_spec ρ
    have : ‖ρ.val‖ < 2 * (2 : ℝ) ^ (kf ρ + 1) := by linarith
    rw [pow_succ] at this ⊢; linarith
  set K_max : ℕ := S_hi.sup kf + 1 with hKmax_def
  have h_kf_lt : ∀ ρ ∈ S_hi, kf ρ < K_max := by
    intro ρ hρ
    have := Finset.le_sup (f := kf) hρ
    omega
  have h_pow_gt_R0 : ∀ ρ ∈ S_hi, R₀_step3 < (2 : ℝ) ^ (kf ρ + 2) := by
    intro ρ hρ
    exact lt_trans (h_hi_gt_R0 ρ hρ) (h_norm_lt ρ)
  have h_kf_log_bd : ∀ ρ ∈ S_hi, ((kf ρ : ℝ) + 1) ≤ Real.log R / Real.log 2 := by
    intro ρ hρ
    have hge := h_norm_ge ρ
    have hle := h_hi_le_R ρ hρ
    have hR_pos' : (0 : ℝ) < (2:ℝ)^(kf ρ + 1) := pow_pos (by norm_num) _
    have h_pow_le_R : (2:ℝ)^(kf ρ + 1) ≤ R := le_trans hge hle
    have h_log_pow_le : Real.log ((2:ℝ)^(kf ρ + 1)) ≤ Real.log R :=
      Real.log_le_log hR_pos' h_pow_le_R
    rw [Real.log_pow] at h_log_pow_le
    push_cast at h_log_pow_le
    rw [le_div_iff₀ hlog2_pos]
    linarith
  have h_sup_bd : ((S_hi.sup kf : ℕ) : ℝ) ≤ Real.log R / Real.log 2 - 1 := by
    by_cases hS : S_hi.Nonempty
    · obtain ⟨m, hm_mem, hm_max⟩ := S_hi.exists_max_image (f := kf) hS
      have h_sup_eq : S_hi.sup kf = kf m := by
        apply le_antisymm
        · exact Finset.sup_le hm_max
        · exact Finset.le_sup hm_mem
      rw [h_sup_eq]
      have := h_kf_log_bd m hm_mem
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      rw [hS, Finset.sup_empty]
      simp
      have h_div_ge_one : (1 : ℝ) ≤ Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]; linarith
      linarith
  have h_Kmax_le_logR : (K_max : ℝ) ≤ Real.log R / Real.log 2 := by
    rw [hKmax_def]; push_cast; linarith
  have h_hi_bound :
      (∑ ρ ∈ S_hi, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
      ∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2 := by
    have h_per_elem : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ≤
        (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) := by
      intro ρ
      have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (kf ρ + 1) := pow_pos (by norm_num) _
      exact div_le_div_of_nonneg_left (by positivity) h_pow_pos (h_norm_ge ρ)
    calc (∑ ρ ∈ S_hi, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖)
        ≤ ∑ ρ ∈ S_hi, (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) := by
          exact Finset.sum_le_sum (fun ρ _ => h_per_elem ρ)
      _ = ∑ k ∈ Finset.range K_max,
            ∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
              (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1) := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (t := Finset.range K_max) (g := kf)
            (f := fun ρ => (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (kf ρ + 1))]
          intro ρ hρ
          exact Finset.mem_range.mpr (h_kf_lt ρ hρ)
      _ = ∑ k ∈ Finset.range K_max,
            (∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
                (ZD.xiOrderNat ρ.val : ℝ)) / (2 : ℝ) ^ (k + 1) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          rw [hρ.2]
      _ ≤ ∑ k ∈ Finset.range K_max,
            (C₃ * (2 : ℝ)^(k+2) * ((k+2 : ℝ) * Real.log 2)) / (2 : ℝ) ^ (k + 1) := by
          apply Finset.sum_le_sum
          intro k _
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
          have h_shell_bd :
              (∑ ρ ∈ S_hi.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)) ≤
                C₃ * (2 : ℝ)^(k+2) * ((k+2 : ℝ) * Real.log 2) := by
            by_cases h_empty : (S_hi.filter (fun ρ => kf ρ = k)).Nonempty
            · obtain ⟨ρ₀, hρ₀⟩ := h_empty
              simp only [Finset.mem_filter] at hρ₀
              have hR0_le : R₀_step3 ≤ (2:ℝ)^(k+2) := by
                have := h_pow_gt_R0 ρ₀ hρ₀.1
                rw [hρ₀.2] at this
                exact this.le
              have h_norm_bd : ∀ ρ ∈ S_hi.filter (fun ρ => kf ρ = k),
                  ‖ρ.val‖ ≤ (2:ℝ)^(k+2) := by
                intro ρ hρ
                simp only [Finset.mem_filter] at hρ
                have := h_norm_lt ρ
                rw [hρ.2] at this
                exact this.le
              have hApp := hBound ((2:ℝ)^(k+2)) hR0_le
                (S_hi.filter (fun ρ => kf ρ = k)) h_norm_bd
              have h_log_eq : Real.log ((2:ℝ)^(k+2)) = ((k+2 : ℕ) : ℝ) * Real.log 2 :=
                Real.log_pow _ _
              rw [h_log_eq] at hApp
              push_cast at hApp
              exact hApp
            · rw [Finset.not_nonempty_iff_eq_empty] at h_empty
              rw [h_empty]
              simp
              positivity
          apply div_le_div_of_nonneg_right h_shell_bd h_pow_pos.le
      _ = ∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_pow_succ : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by
            rw [pow_succ]; ring
          rw [h_pow_succ]
          have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
          field_simp
  have h_sum_bd :
      (∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2) ≤
      2 * C₃ * Real.log 2 * ((K_max : ℝ) + 2)^2 := by
    have h_gauss : (∑ k ∈ Finset.range K_max, (k : ℝ)) = (K_max * (K_max - 1) : ℝ) / 2 := by
      induction K_max with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    have h_sum_eq : (∑ k ∈ Finset.range K_max, 2 * C₃ * ((k : ℝ) + 2) * Real.log 2) =
        2 * C₃ * Real.log 2 * (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros; ring
    have h_sum_shift : (∑ k ∈ Finset.range K_max, ((k : ℝ) + 2)) =
        (∑ k ∈ Finset.range K_max, (k : ℝ)) + 2 * K_max := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Finset.card_range]
      ring
    rw [h_sum_eq, h_sum_shift, h_gauss]
    apply mul_le_mul_of_nonneg_left
    · nlinarith [sq_nonneg ((K_max : ℝ)), sq_nonneg ((K_max : ℝ) + 2)]
    · positivity
  have h_Kmax_sq : ((K_max : ℝ) + 2)^2 ≤ 9 * (Real.log R)^2 / (Real.log 2)^2 := by
    have h_three_bd : (K_max : ℝ) + 2 ≤ 3 * Real.log R / Real.log 2 := by
      have h2_le : (2 : ℝ) ≤ 2 * Real.log R / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]; linarith
      have h_sum : Real.log R / Real.log 2 + 2 * Real.log R / Real.log 2 =
          3 * Real.log R / Real.log 2 := by
        field_simp; ring
      linarith [h_Kmax_le_logR]
    have h_rhs_nn : 0 ≤ 3 * Real.log R / Real.log 2 := by positivity
    have h_lhs_nn : 0 ≤ (K_max : ℝ) + 2 := by positivity
    have hK_sq : ((K_max : ℝ) + 2)^2 ≤ (3 * Real.log R / Real.log 2)^2 := by
      apply sq_le_sq' _ h_three_bd
      linarith
    have h_sq_eq : (3 * Real.log R / Real.log 2)^2 = 9 * (Real.log R)^2 / (Real.log 2)^2 := by
      field_simp; ring
    linarith
  have h_Mlow_bd : M_low ≤ M_low / (Real.log 2)^2 * (Real.log R)^2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h_sq_le : (Real.log 2)^2 ≤ (Real.log R)^2 :=
      pow_le_pow_left₀ hlog2_pos.le hR_log_ge_log2 _
    have : M_low * (Real.log 2)^2 ≤ M_low * (Real.log R)^2 :=
      mul_le_mul_of_nonneg_left h_sq_le hM_low_nn
    linarith
  have h_hi_total : (∑ ρ ∈ S_hi, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
      18 * C₃ / Real.log 2 * (Real.log R)^2 := by
    have h1 : 2 * C₃ * Real.log 2 * ((K_max : ℝ) + 2)^2 ≤
        2 * C₃ * Real.log 2 * (9 * (Real.log R)^2 / (Real.log 2)^2) :=
      mul_le_mul_of_nonneg_left h_Kmax_sq (by positivity)
    have h2 : 2 * C₃ * Real.log 2 * (9 * (Real.log R)^2 / (Real.log 2)^2) =
        18 * C₃ / Real.log 2 * (Real.log R)^2 := by
      field_simp; ring
    linarith [h_hi_bound, h_sum_bd]
  linarith [h_lo_bound, h_hi_total, h_Mlow_bd]

/-- Pointwise upper bound on `log ‖xiProductMult(z)‖` in mean-type-2 form.
Obtained by the direct product estimate splitting into near zeros
(`‖ρ‖ ≤ ‖z‖`, bounded by `xiOrderNat_div_norm_partial_sum_bound`) and far
zeros (`‖ρ‖ > ‖z‖`, bounded by `xiOrderNat_div_norm_sq_tail_bound`). -/
theorem xiProductMult_pointwise_meanType_bound :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log (‖xiProductMult z‖ + 1) ≤
        C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
  obtain ⟨C_tail, hC_tail⟩ := xiOrderNat_div_norm_sq_tail_bound
  obtain ⟨C_part, hC_part⟩ := xiOrderNat_div_norm_partial_sum_bound
  rcases (isCompact_closedBall (0 : ℂ) 2).bddAbove_image
    xiProductMult_differentiable.continuous.norm.continuousOn with ⟨M₀, hM₀⟩
  set M : ℝ := max M₀ 1
  have hM_ge_1 : 1 ≤ M := le_max_right _ _
  have hM_bd : ∀ s ∈ Metric.closedBall (0:ℂ) 2, ‖xiProductMult s‖ ≤ M :=
    fun s hs => le_trans (hM₀ ⟨s, hs, rfl⟩) (le_max_left _ _)
  refine ⟨3 * |C_tail| + 2 * |C_part|, Real.log (M + 1) + Real.log 2, fun z => ?_⟩
  have h_C_tail_abs_nn : 0 ≤ |C_tail| := abs_nonneg _
  have h_C_part_abs_nn : 0 ≤ |C_part| := abs_nonneg _
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have hlog_z2_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
  have hlog_z2_sq_nn : 0 ≤ (Real.log (‖z‖ + 2)) ^ 2 := sq_nonneg _
  have hC_combined_nn : 0 ≤ 3 * |C_tail| + 2 * |C_part| := by positivity
  have hM1_pos : 0 < M + 1 := by linarith
  have hlog_M1_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hz_small : ‖z‖ ≤ 2
  · have hz_in : z ∈ Metric.closedBall (0:ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz_small
    have h_P_bd := hM_bd z hz_in
    have hlog_le : Real.log (‖xiProductMult z‖ + 1) ≤ Real.log (M + 1) := by
      apply Real.log_le_log (by linarith [norm_nonneg (xiProductMult z)]); linarith
    have h_rhs_nn : 0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
      positivity
    linarith
  · have hz_ge_2 : 2 < ‖z‖ := not_le.mp hz_small
    have hz_pos : 0 < ‖z‖ := by linarith
    have hz_ge_2' : (2:ℝ) ≤ ‖z‖ := hz_ge_2.le
    have hlog_z_pos : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
    have hlog_z_nn : 0 ≤ Real.log ‖z‖ := hlog_z_pos.le
    have hlog_z_le_z2 : Real.log ‖z‖ ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log hz_pos (by linarith)
    have hlog_z_sq_le_z2_sq : (Real.log ‖z‖)^2 ≤ (Real.log (‖z‖ + 2))^2 := by
      apply sq_le_sq' (by linarith) hlog_z_le_z2
    have hlog_z2_ge_log4 : Real.log 4 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog4_ge_1 : (1:ℝ) ≤ Real.log 4 := by
      have h1 : Real.exp 1 < 4 := by
        have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith
      have h2 : Real.log (Real.exp 1) ≤ Real.log 4 := Real.log_le_log (Real.exp_pos _) h1.le
      rw [Real.log_exp] at h2; exact h2
    have hlog_z2_ge_1 : (1:ℝ) ≤ Real.log (‖z‖ + 2) := by linarith
    have hlog_z2_le_sq : Real.log (‖z‖ + 2) ≤ (Real.log (‖z‖ + 2))^2 := by
      have h1 : Real.log (‖z‖+2) * 1 ≤ Real.log (‖z‖+2) * Real.log (‖z‖+2) :=
        mul_le_mul_of_nonneg_left hlog_z2_ge_1 hlog_z2_nn
      have h2 : Real.log (‖z‖+2) * Real.log (‖z‖+2) = (Real.log (‖z‖+2))^2 := by ring
      linarith
    have hlog_z_le_z2_sq : Real.log ‖z‖ ≤ (Real.log (‖z‖ + 2))^2 :=
      le_trans hlog_z_le_z2 hlog_z2_le_sq
    by_cases hz_ntz : z ∈ NontrivialZeros
    · have h_zero : xiProductMult z = 0 := xiProductMult_zero_of_mem_NontrivialZeros hz_ntz
      rw [h_zero, norm_zero, zero_add, Real.log_one]
      have h_rhs_nn : 0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
        positivity
      linarith
    · have h_summ_norm : Summable (fun p : MultiZeroIdx => ‖xiWeierstrassTerm p.1.val z‖) := by
        set Mn : ℝ := ‖z‖ + 1
        have hMn_pos : 0 < Mn := by positivity
        have h_bd := xiWeierstrassTerm_mult_closedBall_bound Mn hMn_pos
        have h_summ := summable_multi_weierstrassTerm_bound Mn hMn_pos
        apply Summable.of_norm_bounded_eventually h_summ
        filter_upwards [h_bd] with p hp
        have h1 := hp z (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact h1
      have h_summ_log := h_summ_norm.summable_log_norm_one_add
      have h_log_eq : Real.log ‖xiProductMult z‖ =
          ∑' p : MultiZeroIdx, Real.log ‖1 + xiWeierstrassTerm p.1.val z‖ := by
        have h_mult : Multipliable (fun p : MultiZeroIdx => 1 + xiWeierstrassTerm p.1.val z) :=
          xiProductMult_multipliable z
        have h_norm : ‖xiProductMult z‖ = ∏' p : MultiZeroIdx, ‖1 + xiWeierstrassTerm p.1.val z‖ := by
          unfold xiProductMult; exact h_mult.norm_tprod
        have h_ne : ∀ p : MultiZeroIdx, 1 + xiWeierstrassTerm p.1.val z ≠ 0 := by
          intro p
          have hρ_ne : p.1.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
            rw [heq] at hre; simp at hre
          have hz_ne : z ≠ p.1.val := fun heq => hz_ntz (heq ▸ p.1.property)
          exact one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne hz_ne
        have h_pos : ∀ p : MultiZeroIdx, 0 < ‖1 + xiWeierstrassTerm p.1.val z‖ :=
          fun p => norm_pos_iff.mpr (h_ne p)
        rw [h_norm]
        have h_exp := Real.rexp_tsum_eq_tprod h_pos h_summ_log
        exact (congrArg Real.log h_exp).symm.trans (Real.log_exp _)
      have h_summ_weighted : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
          (xiOrderNat ρ.val : ℝ) * Real.log ‖1 + xiWeierstrassTerm ρ.val z‖) := by
        have h := h_summ_log.sigma' (fun _ => Summable.of_finite)
        refine h.congr ?_
        intro ρ
        show (∑' (_c : Fin (xiOrderNat ρ.val)),
            Real.log ‖1 + xiWeierstrassTerm ρ.val z‖) = _
        rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]; ring
      have h_log_eq_ρ :
          (∑' p : MultiZeroIdx, Real.log ‖1 + xiWeierstrassTerm p.1.val z‖) =
          ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (xiOrderNat ρ.val : ℝ) * Real.log ‖1 + xiWeierstrassTerm ρ.val z‖ := by
        rw [h_summ_log.tsum_sigma' (fun _ => Summable.of_finite)]
        apply tsum_congr
        intro ρ
        show (∑' (_c : Fin (xiOrderNat ρ.val)),
            Real.log ‖1 + xiWeierstrassTerm ρ.val z‖) = _
        rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]; ring
      have h_split := h_summ_weighted.tsum_subtype_add_tsum_subtype_compl
        ({ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ ≤ ‖z‖} : Set _)
      have h_near_bd :
          (∑' ρ : ({ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ ≤ ‖z‖} : Set _),
            (xiOrderNat ρ.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm ρ.val.val z‖) ≤
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by
        have h_rhs_nn : 0 ≤ 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by positivity
        apply tsum_le_of_sum_le' h_rhs_nn
        intro T
        let T' : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} := T.image (·.val)
        have hT'_bd : ∀ ρ ∈ T', ‖ρ.val‖ ≤ ‖z‖ := by
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨x, _, heq⟩ := hρ
          rw [← heq]; exact x.property
        have h_crude : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            Real.log ‖1 + xiWeierstrassTerm ρ.val z‖ ≤ 2 * (‖z‖ / ‖ρ.val‖) := by
          intro ρ
          have hρ_ne : ρ.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
            rw [heq] at hre; simp at hre
          rw [one_add_xiWeierstrassTerm]; unfold xiWeierstrassFactor
          rw [norm_mul, Complex.norm_exp]
          by_cases h_zero : ‖1 - z/ρ.val‖ = 0
          · rw [h_zero, zero_mul, Real.log_zero]; positivity
          · have h1 : 0 < ‖1 - z/ρ.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
            have h2 : 0 < Real.exp ((z/ρ.val).re) := Real.exp_pos _
            rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2), Real.log_exp]
            have h_norm_bd : ‖1 - z/ρ.val‖ ≤ 1 + ‖z‖/‖ρ.val‖ := by
              calc ‖1 - z/ρ.val‖ ≤ ‖(1:ℂ)‖ + ‖z/ρ.val‖ := norm_sub_le _ _
                _ = 1 + ‖z‖/‖ρ.val‖ := by rw [norm_one, norm_div]
            have h_log_bd : Real.log ‖1 - z/ρ.val‖ ≤ ‖z‖/‖ρ.val‖ := by
              have hle : Real.log ‖1 - z/ρ.val‖ ≤ Real.log (1 + ‖z‖/‖ρ.val‖) :=
                Real.log_le_log h1 h_norm_bd
              have hlog_sub : Real.log (1 + ‖z‖/‖ρ.val‖) ≤ (1 + ‖z‖/‖ρ.val‖) - 1 :=
                Real.log_le_sub_one_of_pos (by positivity)
              linarith
            have h_re_bd : (z/ρ.val).re ≤ ‖z/ρ.val‖ := Complex.re_le_norm _
            rw [norm_div] at h_re_bd
            linarith
        have h_sum_bd : (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm x.val.val z‖) ≤
            ∑ x ∈ T, (xiOrderNat x.val.val : ℝ) * (2 * (‖z‖ / ‖x.val.val‖)) := by
          apply Finset.sum_le_sum
          intro x _
          have h_n_nn : (0 : ℝ) ≤ (xiOrderNat x.val.val : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left (h_crude x.val) h_n_nn
        have h_sum_eq :
            (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) * (2 * (‖z‖ / ‖x.val.val‖))) =
            2 * ‖z‖ * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) := by
          rw [show T' = T.image (Subtype.val : _ → {ρ : ℂ // ρ ∈ NontrivialZeros}) from rfl]
          rw [Finset.sum_image]
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          · intro x _ y _ h; exact Subtype.ext h
        have hT'_sum : (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
            C_part * (Real.log ‖z‖)^2 := hC_part ‖z‖ hz_ge_2' T' hT'_bd
        have h_abs : C_part * (Real.log ‖z‖)^2 ≤ |C_part| * (Real.log ‖z‖)^2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        have hT'_sum' : (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
            |C_part| * (Real.log ‖z‖)^2 := by linarith
        have h_2z_nn : 0 ≤ 2 * ‖z‖ := by linarith
        have h_final : 2 * ‖z‖ * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) ≤
            2 * ‖z‖ * (|C_part| * (Real.log ‖z‖)^2) :=
          mul_le_mul_of_nonneg_left hT'_sum' h_2z_nn
        calc (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm x.val.val z‖)
            ≤ ∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
                (2 * (‖z‖ / ‖x.val.val‖)) := h_sum_bd
          _ = 2 * ‖z‖ * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖) := h_sum_eq
          _ ≤ 2 * ‖z‖ * (|C_part| * (Real.log ‖z‖)^2) := h_final
          _ = 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 := by ring
      have h_far_bd :
          (∑' ρ : (({ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ ≤ ‖z‖}ᶜ : Set _)),
            (xiOrderNat ρ.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm ρ.val.val z‖) ≤
          3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by
        have h_rhs_nn : 0 ≤ 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by positivity
        apply tsum_le_of_sum_le' h_rhs_nn
        intro T
        let T' : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} := T.image (·.val)
        have hT'_bd : ∀ ρ ∈ T', ‖z‖ < ‖ρ.val‖ := by
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨x, _, heq⟩ := hρ
          rw [← heq]
          have := x.property
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at this
          exact this
        have h_quad : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, ‖z‖ < ‖ρ.val‖ →
            Real.log ‖1 + xiWeierstrassTerm ρ.val z‖ ≤ 3 * ‖z‖^2 / ‖ρ.val‖^2 := by
          intro ρ hρ_gt
          have hρ_ne : ρ.val ≠ 0 := by
            intro heq
            have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
            rw [heq] at hre; simp at hre
          have hzρ : ‖z‖ ≤ ‖ρ.val‖ := hρ_gt.le
          have h_term_bd := norm_xiWeierstrassTerm_le hρ_ne hzρ
          have h_norm_bd :
              ‖1 + xiWeierstrassTerm ρ.val z‖ ≤ 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by
            calc ‖1 + xiWeierstrassTerm ρ.val z‖
                ≤ ‖(1:ℂ)‖ + ‖xiWeierstrassTerm ρ.val z‖ := norm_add_le _ _
              _ = 1 + ‖xiWeierstrassTerm ρ.val z‖ := by rw [norm_one]
              _ ≤ 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by linarith
          by_cases h_zero : ‖1 + xiWeierstrassTerm ρ.val z‖ = 0
          · rw [h_zero, Real.log_zero]; positivity
          · have hpos : 0 < ‖1 + xiWeierstrassTerm ρ.val z‖ :=
              lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
            have h_rhs_pos : 0 < 1 + 3 * ‖z‖^2 / ‖ρ.val‖^2 := by positivity
            have h_log_le : Real.log ‖1 + xiWeierstrassTerm ρ.val z‖ ≤
                Real.log (1 + 3 * ‖z‖^2 / ‖ρ.val‖^2) := Real.log_le_log hpos h_norm_bd
            have h_log_lt : Real.log (1 + 3 * ‖z‖^2 / ‖ρ.val‖^2) ≤
                3 * ‖z‖^2 / ‖ρ.val‖^2 := by
              have := Real.log_le_sub_one_of_pos h_rhs_pos
              linarith
            linarith
        have h_sum_bd : (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm x.val.val z‖) ≤
            ∑ x ∈ T, (xiOrderNat x.val.val : ℝ) * (3 * ‖z‖^2 / ‖x.val.val‖^2) := by
          apply Finset.sum_le_sum
          intro x _
          have h_n_nn : (0 : ℝ) ≤ (xiOrderNat x.val.val : ℝ) := Nat.cast_nonneg _
          have hx_prop : ‖z‖ < ‖x.val.val‖ := by
            have := x.property
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at this
            exact this
          exact mul_le_mul_of_nonneg_left (h_quad x.val hx_prop) h_n_nn
        have h_sum_eq :
            (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) * (3 * ‖z‖^2 / ‖x.val.val‖^2)) =
            3 * ‖z‖^2 * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) := by
          rw [show T' = T.image (Subtype.val : _ → {ρ : ℂ // ρ ∈ NontrivialZeros}) from rfl]
          rw [Finset.sum_image]
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          · intro x _ y _ h; exact Subtype.ext h
        have hT'_sum : (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            C_tail * Real.log ‖z‖ / ‖z‖ := hC_tail ‖z‖ hz_ge_2' T' hT'_bd
        have h_abs : C_tail * Real.log ‖z‖ / ‖z‖ ≤ |C_tail| * Real.log ‖z‖ / ‖z‖ := by
          have h_factor_nn : 0 ≤ Real.log ‖z‖ / ‖z‖ := by positivity
          have : C_tail * (Real.log ‖z‖ / ‖z‖) ≤ |C_tail| * (Real.log ‖z‖ / ‖z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h_factor_nn
          have h1 : C_tail * Real.log ‖z‖ / ‖z‖ = C_tail * (Real.log ‖z‖ / ‖z‖) := by ring
          have h2 : |C_tail| * Real.log ‖z‖ / ‖z‖ = |C_tail| * (Real.log ‖z‖ / ‖z‖) := by ring
          linarith
        have hT'_sum' : (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            |C_tail| * Real.log ‖z‖ / ‖z‖ := by linarith
        have h_3z2_nn : 0 ≤ 3 * ‖z‖^2 := by positivity
        have h_final : 3 * ‖z‖^2 * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) ≤
            3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) :=
          mul_le_mul_of_nonneg_left hT'_sum' h_3z2_nn
        have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
        have h_simplify : 3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) =
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by field_simp
        calc (∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
              Real.log ‖1 + xiWeierstrassTerm x.val.val z‖)
            ≤ ∑ x ∈ T, (xiOrderNat x.val.val : ℝ) *
                (3 * ‖z‖^2 / ‖x.val.val‖^2) := h_sum_bd
          _ = 3 * ‖z‖^2 * (∑ ρ ∈ T', (xiOrderNat ρ.val : ℝ) / ‖ρ.val‖^2) := h_sum_eq
          _ ≤ 3 * ‖z‖^2 * (|C_tail| * Real.log ‖z‖ / ‖z‖) := h_final
          _ = 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := h_simplify
      have h_log_P_bd : Real.log ‖xiProductMult z‖ ≤
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 +
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ := by
        rw [h_log_eq, h_log_eq_ρ, ← h_split]
        exact add_le_add h_near_bd h_far_bd
      have h_z_bd :
          2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 +
            3 * |C_tail| * ‖z‖ * Real.log ‖z‖ ≤
          (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
        have h1 : 2 * |C_part| * ‖z‖ * (Real.log ‖z‖)^2 ≤
            2 * |C_part| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          have h_coeff_nn : 0 ≤ 2 * |C_part| * ‖z‖ := by positivity
          exact mul_le_mul_of_nonneg_left hlog_z_sq_le_z2_sq h_coeff_nn
        have h2 : 3 * |C_tail| * ‖z‖ * Real.log ‖z‖ ≤
            3 * |C_tail| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          have h_coeff_nn : 0 ≤ 3 * |C_tail| * ‖z‖ := by positivity
          exact mul_le_mul_of_nonneg_left hlog_z_le_z2_sq h_coeff_nn
        have h_expand : (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 =
            2 * |C_part| * ‖z‖ * (Real.log (‖z‖ + 2))^2 +
            3 * |C_tail| * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by ring
        linarith
      have hP_nn : 0 ≤ ‖xiProductMult z‖ := norm_nonneg _
      rcases le_or_gt ‖xiProductMult z‖ 1 with hP_small | hP_big
      · have : Real.log (‖xiProductMult z‖ + 1) ≤ Real.log 2 := by
          apply Real.log_le_log (by linarith) (by linarith)
        have h_rhs_nn :
            0 ≤ (3 * |C_tail| + 2 * |C_part|) * ‖z‖ * (Real.log (‖z‖ + 2))^2 := by
          positivity
        linarith
      · have hP_pos : 0 < ‖xiProductMult z‖ := by linarith
        have : Real.log (‖xiProductMult z‖ + 1) ≤ Real.log (2 * ‖xiProductMult z‖) := by
          apply Real.log_le_log (by linarith) (by linarith)
        have h_log_2P :
            Real.log (2 * ‖xiProductMult z‖) = Real.log 2 + Real.log ‖xiProductMult z‖ :=
          Real.log_mul (by norm_num) (ne_of_gt hP_pos)
        linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step C: Jensen's formula applied to xiProductMult
-- ═══════════════════════════════════════════════════════════════════════════

/-- Jensen's formula applied to `xiProductMult` at center 0.
`xiProductMult` is entire (`xiProductMult_differentiable`) with
`xiProductMult 0 = 1` (every factor evaluates to `(1 - 0)·exp(0) = 1`).
The RHS lists the multiplicity-weighted log of R/‖ρ‖ for zeros inside the
disk; it is nonnegative and bounded by `N(R) · log R = O(R log² R)`. -/
theorem xiProductMult_circleAverage_log_eq :
    ∀ R : ℝ, 0 < R →
      Real.circleAverage (fun z => Real.log ‖xiProductMult z‖) 0 R =
        ∑ᶠ u : ℂ,
          (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
            Real.log (R * ‖u‖⁻¹) := by
  intro R hR
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have h0_in : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) |R| := by
    rw [Metric.mem_closedBall]; simp [abs_of_pos hR, hR.le]
  have h_anal_0 : AnalyticAt ℂ xiProductMult 0 :=
    xiProductMult_differentiable.analyticAt 0
  have h_xi0 : xiProductMult 0 = 1 := by
    unfold xiProductMult
    simp [xiWeierstrassTerm, xiWeierstrassFactor]
  have h_ne_0 : xiProductMult 0 ≠ 0 := by rw [h_xi0]; exact one_ne_zero
  have h_mero : MeromorphicOn xiProductMult (Metric.closedBall 0 |R|) :=
    fun z _ => (xiProductMult_differentiable.analyticAt z).meromorphicAt
  have h_order_0 : analyticOrderAt xiProductMult 0 = 0 :=
    h_anal_0.analyticOrderAt_eq_zero.mpr h_ne_0
  have h_div_0 : (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|)) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply h_mero h0_in]
    rw [h_anal_0.meromorphicOrderAt_eq, h_order_0]; rfl
  have h_trail : meromorphicTrailingCoeffAt xiProductMult 0 = 1 := by
    have := AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero h_anal_0 h_ne_0
    rw [this, h_xi0]
  have h_jensen :=
    MeromorphicOn.circleAverage_log_norm hR_ne h_mero
  -- Simplify the RHS: rewrite `‖0 - u‖ = ‖u‖`, divisor(0) = 0, and trailing coeff = 1.
  rw [h_jensen]
  have h_rewrite : (fun u : ℂ =>
        (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖(0 : ℂ) - u‖⁻¹)) =
      (fun u : ℂ =>
        (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹)) := by
    funext u
    congr 2
    rw [zero_sub, norm_neg]
  rw [h_rewrite, h_div_0, h_trail]
  simp

/-- Upper bound on the Jensen RHS: `∑_{ρ ∈ closedBall 0 R} n_ρ · log(R/‖ρ‖)
   ≤ O(R log² R)`.  Uses `xi_zero_count_disk_bound N(R) = O(R log R)` and
the trivial estimate `log(R/‖ρ‖) ≤ log R`. -/
theorem xiProductMult_jensen_rhs_upper :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹) ≤
        C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C₀, hC₀_pos, R₀, hR₀_pos, hWB⟩ := xi_weighted_zero_count_disk_bound
  have hN₁_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) 1).Finite :=
    ZeroCount.NontrivialZeros_inter_closedBall_finite 1
  have hN_R₀_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) R₀).Finite :=
    ZeroCount.NontrivialZeros_inter_closedBall_finite R₀
  classical
  set A_N₁ : ℝ := ∑ ρ ∈ hN₁_fin.toFinset, (ZD.xiOrderNat ρ : ℝ) * |Real.log ‖ρ‖| with hA_def
  set N_M : ℝ := ∑ ρ ∈ hN₁_fin.toFinset, (ZD.xiOrderNat ρ : ℝ) with hNM_def
  set B_R₀ : ℝ := ∑ ρ ∈ hN_R₀_fin.toFinset,
    (ZD.xiOrderNat ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) with hB_def
  have hA_nn : 0 ≤ A_N₁ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hN_M_nn : 0 ≤ N_M := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB_nn : 0 ≤ B_R₀ := by
    apply Finset.sum_nonneg; intro ρ _
    apply mul_nonneg (Nat.cast_nonneg _)
    have h1 : 0 ≤ max (Real.log R₀) 0 := le_max_right _ _
    have h2 : 0 ≤ |Real.log ‖ρ‖| := abs_nonneg _
    linarith
  refine ⟨C₀ + N_M, A_N₁ + N_M + B_R₀, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  have hlog_R_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hS'_spec : ∀ u : ℂ, u ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset ↔
      u ∈ NontrivialZeros ∩ Metric.closedBall (0 : ℂ) R :=
    fun u => Set.Finite.mem_toFinset _
  have h_finset_eq :
    ∑ᶠ u : ℂ,
      (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
        Real.log (R * ‖u‖⁻¹) =
    ∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset,
      (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) := by
    set f : ℂ → ℝ := fun u =>
      (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
        Real.log (R * ‖u‖⁻¹)
    have hmero : MeromorphicOn xiProductMult (Metric.closedBall 0 |R|) :=
      fun z _ => (xiProductMult_differentiable.analyticAt z).meromorphicAt
    have h_supp_subset : Function.support f ⊆
        ↑((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset) := by
      intro u hu
      simp only [Function.mem_support] at hu
      have h1 : ((MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|)) u : ℝ) ≠ 0 := by
        intro hz; apply hu; show _ * _ = (0 : ℝ); rw [hz, zero_mul]
      have hmem : u ∈ Metric.closedBall (0 : ℂ) |R| := by
        by_contra h; apply h1
        have := Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|)) h
        simp [this]
      have h_anal_u : AnalyticAt ℂ xiProductMult u :=
        xiProductMult_differentiable.analyticAt u
      have h_nz : xiProductMult u = 0 := by
        by_contra hne; apply h1
        rw [MeromorphicOn.divisor_apply hmero hmem, h_anal_u.meromorphicOrderAt_eq]
        rw [h_anal_u.analyticOrderAt_eq_zero.mpr hne]; simp
      have h_NT : u ∈ NontrivialZeros := (xiProductMult_eq_zero_iff u).mp h_nz
      have hmem' : u ∈ Metric.closedBall (0 : ℂ) R := by rwa [habs] at hmem
      exact (hS'_spec u).mpr ⟨h_NT, hmem'⟩
    rw [finsum_eq_sum_of_support_subset f h_supp_subset]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρ' := (hS'_spec ρ).mp hρ
    obtain ⟨hρ_NT, hρ_ball⟩ := hρ'
    have hmem : ρ ∈ Metric.closedBall (0 : ℂ) |R| := by rw [habs]; exact hρ_ball
    have h_anal_ρ : AnalyticAt ℂ xiProductMult ρ :=
      xiProductMult_differentiable.analyticAt ρ
    have h_div_eq :
        ((MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|)) ρ : ℝ) =
          (ZD.xiOrderNat ρ : ℝ) := by
      rw [MeromorphicOn.divisor_apply hmero hmem, h_anal_ρ.meromorphicOrderAt_eq]
      rw [ZD.analyticOrderAt_xiProductMult_eq_xiOrderNat hρ_NT]; simp
    show ((MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|)) ρ : ℝ) *
        Real.log (R * ‖ρ‖⁻¹) = (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹)
    rw [h_div_eq]
  rw [h_finset_eq]
  by_cases hR_ge : R₀ ≤ R
  · rw [← Finset.sum_filter_add_sum_filter_not
      (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset (fun ρ => ‖ρ‖ ≤ 1)]
    have h_small_subset :
        ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1) ⊆
          hN₁_fin.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, h_small⟩ := hρ
      have hρ' := (hS'_spec ρ).mp hρ_mem
      rw [Set.Finite.mem_toFinset]
      exact ⟨hρ'.1, by rw [Metric.mem_closedBall, dist_zero_right]; exact h_small⟩
    have h_small_term_bd : ∀ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ‖ρ‖ ≤ 1),
        (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (ZD.xiOrderNat ρ : ℝ) * Real.log R + (ZD.xiOrderNat ρ : ℝ) * |Real.log ‖ρ‖| := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, _⟩ := hρ
      have hρ' := (hS'_spec ρ).mp hρ_mem
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_xi_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
      have h_abs : -Real.log ‖ρ‖ ≤ |Real.log ‖ρ‖| := neg_le_abs _
      rw [h_log_mul, h_log_inv]
      have : Real.log R + -Real.log ‖ρ‖ ≤ Real.log R + |Real.log ‖ρ‖| := by linarith
      have := mul_le_mul_of_nonneg_left this h_xi_nn
      linarith
    have h_small_sum_bd := Finset.sum_le_sum h_small_term_bd
    have h_small_split :
      ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        ((ZD.xiOrderNat ρ : ℝ) * Real.log R + (ZD.xiOrderNat ρ : ℝ) * |Real.log ‖ρ‖|) =
      (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        (ZD.xiOrderNat ρ : ℝ)) * Real.log R +
      (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter (fun ρ => ‖ρ‖ ≤ 1),
        (ZD.xiOrderNat ρ : ℝ) * |Real.log ‖ρ‖|) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have h_wN_small_le :
        (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
           (fun ρ => ‖ρ‖ ≤ 1), (ZD.xiOrderNat ρ : ℝ)) ≤ N_M := by
      rw [hNM_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg h_small_subset
      intros; exact Nat.cast_nonneg _
    have h_wA_small_le :
        (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
           (fun ρ => ‖ρ‖ ≤ 1), (ZD.xiOrderNat ρ : ℝ) * |Real.log ‖ρ‖|) ≤ A_N₁ := by
      rw [hA_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg h_small_subset
      intros; exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    have h_big_term_bd : ∀ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)),
        (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (ZD.xiOrderNat ρ : ℝ) * Real.log R := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρ_mem, h_not_small⟩ := hρ
      have h_gt : 1 < ‖ρ‖ := not_le.mp h_not_small
      have hρ' := (hS'_spec ρ).mp hρ_mem
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_log_ρ_pos : 0 < Real.log ‖ρ‖ := Real.log_pos h_gt
      have h_xi_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
      rw [h_log_mul, h_log_inv]
      have : Real.log R + -Real.log ‖ρ‖ ≤ Real.log R := by linarith
      have := mul_le_mul_of_nonneg_left this h_xi_nn
      linarith
    have h_big_sum_bd := Finset.sum_le_sum h_big_term_bd
    have h_big_factor :
        ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (ZD.xiOrderNat ρ : ℝ) * Real.log R =
        (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) * Real.log R := by
      rw [← Finset.sum_mul]
    have h_sum_attach :
        (∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset, (ZD.xiOrderNat ρ : ℝ)) =
        ∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset.attach.image
          (fun ρ : {x // x ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset} =>
            (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros})),
          (ZD.xiOrderNat ρ.val : ℝ) := by
      rw [Finset.sum_image
        (f := fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => (ZD.xiOrderNat ρ.val : ℝ))
        (g := fun ρ : {x // x ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset} =>
          (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}))
        (s := (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset.attach)
        (?_)]
      · exact (Finset.sum_attach _ _).symm
      · intro a _ b _ hab
        exact Subtype.ext (Subtype.mk.injEq _ _ _ _ |>.mp hab)
    set S_attach : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
      (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset.attach.image
        (fun ρ : {x // x ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset} =>
          (⟨ρ.val, ((hS'_spec ρ.val).mp ρ.property).1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros})) with hSa_def
    have hS_attach_bd : ∀ ρ ∈ S_attach, ‖ρ.val‖ ≤ R := by
      intro ρ hρ
      simp only [hSa_def, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hρ
      obtain ⟨ρ', hρ', heq⟩ := hρ
      have hρ'' := (hS'_spec ρ').mp hρ'
      have : ρ' ∈ Metric.closedBall (0 : ℂ) R := hρ''.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      rw [← heq]; exact this
    have hWB_R := hWB R hR_ge S_attach hS_attach_bd
    rw [← h_sum_attach] at hWB_R
    have h_big_weight_le :
        (∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤
        ∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset, (ZD.xiOrderNat ρ : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intros; exact Nat.cast_nonneg _
    have h_log_le_sq : Real.log R ≤ R * (Real.log R)^2 + 1 := by
      have h1 : Real.log R ≤ (Real.log R)^2 + 1 := by
        nlinarith [sq_nonneg (Real.log R - 1/2)]
      have h2 : (Real.log R)^2 ≤ R * (Real.log R)^2 := by
        have := mul_le_mul_of_nonneg_right hR (sq_nonneg (Real.log R))
        linarith
      linarith
    have h_big_sum_le_final :
        ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ¬(‖ρ‖ ≤ 1)),
          (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        C₀ * R * Real.log R * Real.log R := by
      calc ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
            (fun ρ => ¬(‖ρ‖ ≤ 1)),
            (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹)
          ≤ ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
            (fun ρ => ¬(‖ρ‖ ≤ 1)), (ZD.xiOrderNat ρ : ℝ) * Real.log R := h_big_sum_bd
        _ = _ := h_big_factor
        _ ≤ (∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset,
              (ZD.xiOrderNat ρ : ℝ)) * Real.log R :=
            mul_le_mul_of_nonneg_right h_big_weight_le hlog_R_nn
        _ ≤ C₀ * R * Real.log R * Real.log R :=
            mul_le_mul_of_nonneg_right hWB_R hlog_R_nn
    have h_small_sum_le_final :
        ∑ ρ ∈ ((ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset).filter
          (fun ρ => ‖ρ‖ ≤ 1),
          (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        N_M * Real.log R + A_N₁ := by
      calc _ ≤ _ := h_small_sum_bd
        _ = _ := h_small_split
        _ ≤ N_M * Real.log R + A_N₁ := by
            have := mul_le_mul_of_nonneg_right h_wN_small_le hlog_R_nn
            linarith
    have hC₀_sq : C₀ * R * Real.log R * Real.log R = C₀ * R * (Real.log R)^2 := by ring
    have h_NM_logR : N_M * Real.log R ≤ N_M * R * (Real.log R)^2 + N_M := by
      have := mul_le_mul_of_nonneg_left h_log_le_sq hN_M_nn
      nlinarith
    linarith
  · push_neg at hR_ge
    have hR_lt : R < R₀ := hR_ge
    have hR_le : R ≤ R₀ := hR_lt.le
    have h_S_subset : (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset ⊆
        hN_R₀_fin.toFinset := by
      intro ρ hρ
      have hρ' := (hS'_spec ρ).mp hρ
      rw [Set.Finite.mem_toFinset]
      refine ⟨hρ'.1, ?_⟩
      have := hρ'.2
      rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
      linarith
    have h_term_bd : ∀ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset,
        (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤
        (ZD.xiOrderNat ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) := by
      intro ρ hρ
      have hρ' := (hS'_spec ρ).mp hρ
      obtain ⟨hNT, _⟩ := hρ'
      have hρ_ne : ρ ≠ 0 := by
        intro h; rw [h] at hNT; have := hNT.1; simp at this
      have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
      have hρ_inv_pos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ_pos
      have h_log_mul : Real.log (R * ‖ρ‖⁻¹) = Real.log R + Real.log ‖ρ‖⁻¹ :=
        Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hρ_inv_pos)
      have h_log_inv : Real.log ‖ρ‖⁻¹ = -Real.log ‖ρ‖ := Real.log_inv _
      have h_xi_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
      have h_abs : -Real.log ‖ρ‖ ≤ |Real.log ‖ρ‖| := neg_le_abs _
      have h_log_R_le : Real.log R ≤ Real.log R₀ := Real.log_le_log hR_pos hR_le
      have h_log_R₀_le_max : Real.log R₀ ≤ max (Real.log R₀) 0 := le_max_left _ _
      rw [h_log_mul, h_log_inv]
      have h_ineq : Real.log R + -Real.log ‖ρ‖ ≤ max (Real.log R₀) 0 + |Real.log ‖ρ‖| := by linarith
      have := mul_le_mul_of_nonneg_left h_ineq h_xi_nn
      linarith
    have h_sum_le_B :
        ∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset,
          (ZD.xiOrderNat ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) ≤ B_R₀ := by
      calc _ ≤ ∑ ρ ∈ (ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset,
              (ZD.xiOrderNat ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) :=
            Finset.sum_le_sum h_term_bd
        _ ≤ ∑ ρ ∈ hN_R₀_fin.toFinset,
              (ZD.xiOrderNat ρ : ℝ) * (max (Real.log R₀) 0 + |Real.log ‖ρ‖|) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg h_S_subset
            intro ρ _ _
            apply mul_nonneg (Nat.cast_nonneg _)
            have h1 : 0 ≤ max (Real.log R₀) 0 := le_max_right _ _
            have h2 : 0 ≤ |Real.log ‖ρ‖| := abs_nonneg _
            linarith
        _ = B_R₀ := hB_def.symm
    have hC_R_logSq_nn : 0 ≤ (C₀ + N_M) * R * (Real.log R)^2 := by
      apply mul_nonneg
      · exact mul_nonneg (by linarith [hC₀_pos, hN_M_nn]) hR_pos.le
      · exact sq_nonneg _
    linarith

/-- The Jensen RHS is nonnegative (divisor nonneg for entire function, and
`log(R/‖ρ‖) ≥ 0` when `‖ρ‖ ≤ R`). -/
theorem xiProductMult_jensen_rhs_nonneg :
    ∀ R : ℝ, 1 ≤ R →
      0 ≤ ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u : ℝ) *
          Real.log (R * ‖u‖⁻¹) := by
  intro R hR
  have hR_pos : 0 < R := by linarith
  have h_anal : AnalyticOnNhd ℂ xiProductMult (Metric.closedBall 0 |R|) := by
    intro z _
    exact xiProductMult_differentiable.analyticAt z
  have h_div_nn :
      0 ≤ MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg h_anal
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |R|
  · have hu_norm : ‖u‖ ≤ R := by
      have : ‖u‖ ≤ |R| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hu
      rwa [abs_of_pos hR_pos] at this
    have h_div_u_nn :
        (0 : ℤ) ≤ MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u :=
      h_div_nn u
    have h_div_u_real_nn :
        (0 : ℝ) ≤ (MeromorphicOn.divisor xiProductMult
          (Metric.closedBall 0 |R|) u : ℝ) := by exact_mod_cast h_div_u_nn
    have h_log_nn : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
      by_cases hu_zero : u = 0
      · subst hu_zero
        simp
      · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_zero
        have h_arg_ge_one : 1 ≤ R * ‖u‖⁻¹ := by
          rw [le_mul_inv_iff₀ hu_pos]
          linarith
        exact Real.log_nonneg h_arg_ge_one
    exact mul_nonneg h_div_u_real_nn h_log_nn
  · have h_zero :
        MeromorphicOn.divisor xiProductMult (Metric.closedBall 0 |R|) u = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
    simp [h_zero]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step D: proximity functions m(R, ·)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Nevanlinna proximity `m(R, f) = (1/2π) ∫ log⁺ ‖f(Re^{iθ})‖ dθ`. -/
def proximity (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Real.circleAverage (fun z => max (Real.log ‖f z‖) 0) 0 R

/-- `proximity f R ≥ 0`. -/
theorem proximity_nonneg (f : ℂ → ℂ) (R : ℝ) : 0 ≤ proximity f R := by
  unfold proximity
  apply Real.circleAverage_nonneg_of_nonneg
  intro x _
  exact le_max_right _ _

/-- Basic inequality: `(1/2π) ∫ log ‖f‖ = proximity f R − (1/2π) ∫ log⁻‖f‖`. -/
theorem circleAverage_log_eq_posLog_sub_negLog
    (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|)) :
    Real.circleAverage (fun z => Real.log ‖f z‖) 0 R =
      proximity f R -
        Real.circleAverage (fun z => max (-(Real.log ‖f z‖)) 0) 0 R := by
  unfold proximity
  have h_pt : (fun z : ℂ => Real.log ‖f z‖) =
      (fun z : ℂ => max (Real.log ‖f z‖) 0) - (fun z : ℂ => max (-(Real.log ‖f z‖)) 0) := by
    funext z
    show Real.log ‖f z‖ = max (Real.log ‖f z‖) 0 - max (-(Real.log ‖f z‖)) 0
    have h := @Real.posLog_sub_posLog_inv ‖f z‖
    simp only [Real.posLog_def] at h
    have hinv : Real.log ‖f z‖⁻¹ = -(Real.log ‖f z‖) := Real.log_inv _
    rw [hinv] at h
    rw [max_comm 0, max_comm 0] at h
    linarith
  have h_ci_posLog :
      CircleIntegrable (fun z => max (Real.log ‖f z‖) 0) 0 R := by
    have := circleIntegrable_posLog_norm_meromorphicOn (f := f) (c := (0 : ℂ)) (R := R) hf
    convert this using 1
    funext z
    rw [Real.posLog_def, max_comm]
  have hf_inv : MeromorphicOn (fun z => (f z)⁻¹) (Metric.sphere (0 : ℂ) |R|) := hf.inv
  have h_ci_negLog :
      CircleIntegrable (fun z => max (-(Real.log ‖f z‖)) 0) 0 R := by
    have h_inv_pos := circleIntegrable_posLog_norm_meromorphicOn (f := fun z => (f z)⁻¹)
      (c := (0 : ℂ)) (R := R) hf_inv
    convert h_inv_pos using 1
    funext z
    rw [Real.posLog_def, max_comm]
    congr 1
    rw [norm_inv, Real.log_inv]
  rw [h_pt]
  exact Real.circleAverage_sub h_ci_posLog h_ci_negLog

/-- `m(R, ξ) ≤ O(R log R)`.  Direct from the pointwise bound Step A: integrate
`log⁺ ‖ξ‖ ≤ log(‖ξ‖+1) ≤ C R log R` over the circle. -/
theorem riemannXi_proximity_bound :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity riemannXi R ≤ C * R * Real.log R + D := by
  obtain ⟨C₀, D₀, hBd⟩ := riemannXi_pointwise_meanType_bound
  refine ⟨2 * |C₀|, D₀ + |C₀| * 2 * Real.log 4, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  unfold proximity
  have h_ci : CircleIntegrable (fun z : ℂ => max (Real.log ‖riemannXi z‖) 0) 0 R := by
    have hMero : MeromorphicOn riemannXi (Metric.sphere (0 : ℂ) |R|) := fun z _ =>
      (riemannXi_differentiable.analyticAt z).meromorphicAt
    have := circleIntegrable_posLog_norm_meromorphicOn (f := riemannXi)
      (c := (0 : ℂ)) (R := R) hMero
    convert this using 1; funext z
    rw [Real.posLog_def, max_comm]
  have h_sphere_bd : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      max (Real.log ‖riemannXi z‖) 0 ≤ C₀ * R * Real.log (R + 2) + D₀ := by
    intro z hz
    have hz_norm : ‖z‖ = R := by
      rw [habs] at hz
      have : dist z 0 = R := hz
      rwa [dist_zero_right] at this
    have hnn : 0 ≤ ‖riemannXi z‖ := norm_nonneg _
    have h1 : max (Real.log ‖riemannXi z‖) 0 ≤ Real.log (‖riemannXi z‖ + 1) := by
      rcases le_or_gt ‖riemannXi z‖ 1 with h | h
      · have hlog_nn : 0 ≤ Real.log (‖riemannXi z‖ + 1) := Real.log_nonneg (by linarith)
        have hmax : max (Real.log ‖riemannXi z‖) 0 = 0 := by
          apply max_eq_right; exact Real.log_nonpos hnn h
        rw [hmax]; exact hlog_nn
      · have hlog_nn : 0 ≤ Real.log ‖riemannXi z‖ := Real.log_nonneg h.le
        have hmax : max (Real.log ‖riemannXi z‖) 0 = Real.log ‖riemannXi z‖ := max_eq_left hlog_nn
        rw [hmax]
        exact Real.log_le_log (by linarith) (by linarith)
    have h2 := hBd z
    rw [hz_norm] at h2
    linarith
  have h_step1 := Real.circleAverage_mono_on_of_le_circle h_ci h_sphere_bd
  have hC₀_abs_nn : 0 ≤ |C₀| := abs_nonneg _
  have hC₀_le : C₀ ≤ |C₀| := le_abs_self _
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog_R2_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_final : C₀ * R * Real.log (R + 2) ≤ 2 * |C₀| * R * Real.log R + |C₀| * 2 * Real.log 4 := by
    rcases le_or_gt R 2 with hR2 | hR2
    · have hR2_bd : R + 2 ≤ 4 := by linarith
      have hR2_pos : 0 < R + 2 := by linarith
      have hlog_R2_le : Real.log (R + 2) ≤ Real.log 4 := Real.log_le_log hR2_pos hR2_bd
      have h_Rle : R ≤ 2 := hR2
      have h1 : C₀ * R * Real.log (R + 2) ≤ |C₀| * R * Real.log (R + 2) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀_le hR_nn) hlog_R2_nn
        linarith
      have h2 : |C₀| * R * Real.log (R + 2) ≤ |C₀| * 2 * Real.log 4 := by
        have hR_bound : R * Real.log (R + 2) ≤ 2 * Real.log 4 := by
          have hR_R2 : R * Real.log (R + 2) ≤ R * Real.log 4 :=
            mul_le_mul_of_nonneg_left hlog_R2_le hR_nn
          have h_R_bound : R * Real.log 4 ≤ 2 * Real.log 4 :=
            mul_le_mul_of_nonneg_right h_Rle hlog_4_pos.le
          linarith
        have := mul_le_mul_of_nonneg_left hR_bound hC₀_abs_nn
        nlinarith
      have h3 : 0 ≤ 2 * |C₀| * R * Real.log R :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀_abs_nn) hR_nn) hlogR_nn
      linarith
    · have hR_ge : 2 ≤ R := hR2.le
      have hlog_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
        have h_sq : R + 2 ≤ R ^ 2 := by nlinarith
        have hR2_pos : 0 < R + 2 := by linarith
        have h1 := Real.log_le_log hR2_pos h_sq
        have h2 : Real.log (R ^ 2) = 2 * Real.log R := by
          rw [show (R^2 : ℝ) = R * R from by ring,
              Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hR_pos)]; ring
        linarith
      have h1 : C₀ * R * Real.log (R + 2) ≤ |C₀| * R * Real.log (R + 2) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀_le hR_nn) hlog_R2_nn
        linarith
      have h2 : |C₀| * R * Real.log (R + 2) ≤ |C₀| * R * (2 * Real.log R) := by
        apply mul_le_mul_of_nonneg_left hlog_bd
        exact mul_nonneg hC₀_abs_nn hR_nn
      have h3 : 0 ≤ |C₀| * 2 * Real.log 4 :=
        mul_nonneg (mul_nonneg hC₀_abs_nn (by norm_num)) hlog_4_pos.le
      nlinarith
  linarith

/-- `m(R, P) ≤ O(R log² R)`.  From the pointwise bound Step B. -/
theorem xiProductMult_proximity_bound :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity xiProductMult R ≤ C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C₀, D₀, hBd⟩ := ZD.xiProductMult_pointwise_meanType_bound
  refine ⟨|C₀| * 4, D₀ + |C₀| * 2 * (Real.log 4)^2, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR_pos
  unfold proximity
  have h_ci : CircleIntegrable (fun z : ℂ => max (Real.log ‖xiProductMult z‖) 0) 0 R := by
    have hMero : MeromorphicOn xiProductMult (Metric.sphere (0 : ℂ) |R|) := fun z _ =>
      (xiProductMult_differentiable.analyticAt z).meromorphicAt
    have := circleIntegrable_posLog_norm_meromorphicOn (f := xiProductMult)
      (c := (0 : ℂ)) (R := R) hMero
    convert this using 1; funext z
    rw [Real.posLog_def, max_comm]
  have h_sphere_bd : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      max (Real.log ‖xiProductMult z‖) 0 ≤ C₀ * R * (Real.log (R + 2))^2 + D₀ := by
    intro z hz
    have hz_norm : ‖z‖ = R := by
      rw [habs] at hz
      have : dist z 0 = R := hz
      rwa [dist_zero_right] at this
    have hnn : 0 ≤ ‖xiProductMult z‖ := norm_nonneg _
    have h1 : max (Real.log ‖xiProductMult z‖) 0 ≤ Real.log (‖xiProductMult z‖ + 1) := by
      rcases le_or_gt ‖xiProductMult z‖ 1 with h | h
      · have hlog_nn : 0 ≤ Real.log (‖xiProductMult z‖ + 1) := Real.log_nonneg (by linarith)
        have hmax : max (Real.log ‖xiProductMult z‖) 0 = 0 := by
          apply max_eq_right; exact Real.log_nonpos hnn h
        rw [hmax]; exact hlog_nn
      · have hlog_nn : 0 ≤ Real.log ‖xiProductMult z‖ := Real.log_nonneg h.le
        have hmax : max (Real.log ‖xiProductMult z‖) 0 = Real.log ‖xiProductMult z‖ := max_eq_left hlog_nn
        rw [hmax]
        exact Real.log_le_log (by linarith) (by linarith)
    have h2 := hBd z
    rw [hz_norm] at h2
    linarith
  have h_step1 := Real.circleAverage_mono_on_of_le_circle h_ci h_sphere_bd
  have hC₀_abs_nn : 0 ≤ |C₀| := abs_nonneg _
  have hC₀_le : C₀ ≤ |C₀| := le_abs_self _
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogR_sq_nn : 0 ≤ (Real.log R)^2 := sq_nonneg _
  have hlog_R2_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_R2_sq_nn : 0 ≤ (Real.log (R+2))^2 := sq_nonneg _
  have hlog_4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog_4_nn : 0 ≤ Real.log 4 := hlog_4_pos.le
  have hlog_4_sq_nn : 0 ≤ (Real.log 4)^2 := sq_nonneg _
  have h_final : C₀ * R * (Real.log (R + 2))^2 ≤
      |C₀| * 4 * R * (Real.log R)^2 + |C₀| * 2 * (Real.log 4)^2 := by
    rcases le_or_gt R 2 with hR2 | hR2
    · have hR2_bd : R + 2 ≤ 4 := by linarith
      have hR2_pos : 0 < R + 2 := by linarith
      have hlog_R2_le : Real.log (R + 2) ≤ Real.log 4 := Real.log_le_log hR2_pos hR2_bd
      have hlog_R2_sq_le : (Real.log (R+2))^2 ≤ (Real.log 4)^2 := by
        apply sq_le_sq'
        · linarith
        · exact hlog_R2_le
      have h_Rle : R ≤ 2 := hR2
      have h1 : C₀ * R * (Real.log (R+2))^2 ≤ |C₀| * R * (Real.log (R+2))^2 := by
        have ha : C₀ * R ≤ |C₀| * R := mul_le_mul_of_nonneg_right hC₀_le hR_nn
        have := mul_le_mul_of_nonneg_right ha hlog_R2_sq_nn
        linarith
      have h2 : |C₀| * R * (Real.log (R+2))^2 ≤ |C₀| * 2 * (Real.log 4)^2 := by
        have h2a : R * (Real.log (R+2))^2 ≤ 2 * (Real.log 4)^2 := by
          have hR_le : R * (Real.log (R+2))^2 ≤ R * (Real.log 4)^2 :=
            mul_le_mul_of_nonneg_left hlog_R2_sq_le hR_nn
          have h_R_bound : R * (Real.log 4)^2 ≤ 2 * (Real.log 4)^2 :=
            mul_le_mul_of_nonneg_right h_Rle hlog_4_sq_nn
          linarith
        have := mul_le_mul_of_nonneg_left h2a hC₀_abs_nn
        nlinarith
      have h3 : 0 ≤ |C₀| * 4 * R * (Real.log R)^2 := by positivity
      linarith
    · have hR_ge : 2 ≤ R := hR2.le
      have hlog_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
        have h_sq : R + 2 ≤ R ^ 2 := by nlinarith
        have hR2_pos : 0 < R + 2 := by linarith
        have h1 := Real.log_le_log hR2_pos h_sq
        have h2 : Real.log (R ^ 2) = 2 * Real.log R := by
          rw [show (R^2 : ℝ) = R * R from by ring,
              Real.log_mul (ne_of_gt hR_pos) (ne_of_gt hR_pos)]; ring
        linarith
      have hlog_bd_sq : (Real.log (R + 2))^2 ≤ 4 * (Real.log R)^2 := by
        have hle : (Real.log (R+2))^2 ≤ (2 * Real.log R)^2 := by
          apply sq_le_sq'
          · linarith
          · exact hlog_bd
        calc (Real.log (R+2))^2 ≤ (2 * Real.log R)^2 := hle
          _ = 4 * (Real.log R)^2 := by ring
      have h1 : C₀ * R * (Real.log (R+2))^2 ≤ |C₀| * R * (Real.log (R+2))^2 := by
        have ha : C₀ * R ≤ |C₀| * R := mul_le_mul_of_nonneg_right hC₀_le hR_nn
        have := mul_le_mul_of_nonneg_right ha hlog_R2_sq_nn
        linarith
      have h2 : |C₀| * R * (Real.log (R+2))^2 ≤ |C₀| * R * (4 * (Real.log R)^2) := by
        apply mul_le_mul_of_nonneg_left hlog_bd_sq
        exact mul_nonneg hC₀_abs_nn hR_nn
      have h_expand : |C₀| * R * (4 * (Real.log R)^2) = 4 * |C₀| * R * (Real.log R)^2 := by ring
      have h_eq2 : |C₀| * 4 * R * (Real.log R)^2 = 4 * |C₀| * R * (Real.log R)^2 := by ring
      have h3 : 0 ≤ |C₀| * 2 * (Real.log 4)^2 := by positivity
      linarith
  linarith

/-- `m(R, 1/P) ≤ O(R log² R)`.  From the identity
`m(R, 1/P) = m(R, P) − (1/2π) ∫ log ‖P‖`, Jensen (Step C), and the proximity
bound on `P`. -/
theorem xiProductMult_inv_proximity_bound :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity (fun z => (xiProductMult z)⁻¹) R ≤
        C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C, D, hPbd⟩ := ZD.xiProductMult_proximity_bound
  refine ⟨C, D, fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have hmero : Meromorphic xiProductMult := fun z =>
    (xiProductMult_differentiable.analyticAt z).meromorphicAt
  have hid := @ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage xiProductMult hmero
  have hid_R : ValueDistribution.proximity xiProductMult ⊤ R -
      ValueDistribution.proximity xiProductMult⁻¹ ⊤ R =
      Real.circleAverage (fun x => Real.log ‖xiProductMult x‖) 0 R := by
    have := congrArg (fun f => f R) hid
    simp only [Pi.sub_apply] at this
    exact this
  have hJensen := xiProductMult_circleAverage_log_eq R hR_pos
  have hJnn := xiProductMult_jensen_rhs_nonneg R hR
  rw [hJensen] at hid_R
  unfold proximity
  have hP_bridge :
    Real.circleAverage (fun z => max (Real.log ‖xiProductMult z‖) 0) 0 R =
      ValueDistribution.proximity xiProductMult ⊤ R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have hPinv_bridge :
    Real.circleAverage (fun z => max (Real.log ‖(xiProductMult z)⁻¹‖) 0) 0 R =
      ValueDistribution.proximity xiProductMult⁻¹ ⊤ R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z
    show max (Real.log ‖(xiProductMult z)⁻¹‖) 0 = max 0 (Real.log ‖xiProductMult⁻¹ z‖)
    simp only [Pi.inv_apply]
    exact max_comm _ _
  rw [hPinv_bridge]
  have h_prox_le :
      ValueDistribution.proximity xiProductMult⁻¹ ⊤ R ≤
      ValueDistribution.proximity xiProductMult ⊤ R := by linarith
  have hP_bound : ValueDistribution.proximity xiProductMult ⊤ R ≤ C * R * (Real.log R)^2 + D := by
    have := hPbd R hR
    unfold proximity at this
    rw [hP_bridge] at this
    exact this
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step E: Nevanlinna first inequality for xiOverP
-- ═══════════════════════════════════════════════════════════════════════════

/-- Nevanlinna first inequality for a product: `log⁺‖a·b‖ ≤ log⁺‖a‖ + log⁺‖b‖ + log 2`
at every point, hence circle-averaged inequality. -/
theorem proximity_mul_le
    (f g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : Meromorphic f) (hg : Meromorphic g) :
    proximity (fun z => f z * g z) R ≤
      proximity f R + proximity g R + Real.log 2 := by
  unfold proximity
  have h1 :
    Real.circleAverage (fun z => max (Real.log ‖f z * g z‖) 0) 0 R =
      ValueDistribution.proximity (fun z => f z * g z) (⊤ : WithTop ℂ) R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h2 :
    Real.circleAverage (fun z => max (Real.log ‖f z‖) 0) 0 R =
      ValueDistribution.proximity f (⊤ : WithTop ℂ) R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h3 :
    Real.circleAverage (fun z => max (Real.log ‖g z‖) 0) 0 R =
      ValueDistribution.proximity g (⊤ : WithTop ℂ) R := by
    rw [ValueDistribution.proximity_top]
    simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  rw [h1, h2, h3]
  have hfg := ValueDistribution.proximity_mul_top_le hf hg
  have hfg_R := hfg R
  simp only [Pi.add_apply] at hfg_R
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have heq : (fun z => f z * g z) = f * g := rfl
  rw [heq]
  linarith

/-- `m(R, xiOverP) ≤ m(R, ξ) + m(R, 1/P) + log 2 = O(R log² R)`. -/
theorem xiOverP_proximity_bound :
    ∃ C D : ℝ, ∀ R : ℝ, 1 ≤ R →
      proximity xiOverP R ≤ C * R * (Real.log R) ^ 2 + D := by
  obtain ⟨C_xi, D_xi, hXi⟩ := ZD.riemannXi_proximity_bound
  obtain ⟨C_inv, D_inv, hInv⟩ := ZD.xiProductMult_inv_proximity_bound
  refine ⟨|C_xi| + |C_inv|, |D_xi| + |D_inv| + Real.log 2 + |C_xi| * Real.exp 1,
    fun R hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have h_codisc : (fun z => riemannXi z * (xiProductMult z)⁻¹) =ᶠ[Filter.codiscrete ℂ] xiOverP := by
    have hratio : (fun z => riemannXi z / xiProductMult z) =ᶠ[Filter.codiscrete ℂ] xiOverP :=
      xiOverP_eq_ratio_codiscretely
    filter_upwards [hratio] with z hz
    rw [← hz, div_eq_mul_inv]
  unfold proximity
  have h_bridge_xi :
    Real.circleAverage (fun z => max (Real.log ‖riemannXi z‖) 0) 0 R =
      ValueDistribution.proximity riemannXi ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h_bridge_xiOverP :
    Real.circleAverage (fun z => max (Real.log ‖xiOverP z‖) 0) 0 R =
      ValueDistribution.proximity xiOverP ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z; exact max_comm _ _
  have h_bridge_Pinv :
    Real.circleAverage (fun z => max (Real.log ‖(xiProductMult z)⁻¹‖) 0) 0 R =
      ValueDistribution.proximity xiProductMult⁻¹ ⊤ R := by
    rw [ValueDistribution.proximity_top]; simp only [Real.posLog_def]
    congr 1; funext z
    show max (Real.log ‖(xiProductMult z)⁻¹‖) 0 = max 0 (Real.log ‖xiProductMult⁻¹ z‖)
    simp only [Pi.inv_apply]; exact max_comm _ _
  rw [h_bridge_xiOverP]
  have h_prox_eq : ValueDistribution.proximity xiOverP ⊤ R =
      ValueDistribution.proximity (fun z => riemannXi z * (xiProductMult z)⁻¹) ⊤ R :=
    (ValueDistribution.proximity_congr_codiscrete h_codisc hR_ne).symm
  rw [h_prox_eq]
  have hmero_xi : Meromorphic riemannXi := fun z =>
    (riemannXi_differentiable.analyticAt z).meromorphicAt
  have hmero_P : Meromorphic xiProductMult := fun z =>
    (xiProductMult_differentiable.analyticAt z).meromorphicAt
  have hmero_Pinv : Meromorphic xiProductMult⁻¹ := hmero_P.inv
  have h_mul : ValueDistribution.proximity (riemannXi * xiProductMult⁻¹) ⊤ ≤
      ValueDistribution.proximity riemannXi ⊤ + ValueDistribution.proximity xiProductMult⁻¹ ⊤ :=
    ValueDistribution.proximity_mul_top_le hmero_xi hmero_Pinv
  have h_mul_R : ValueDistribution.proximity (riemannXi * xiProductMult⁻¹) ⊤ R ≤
      ValueDistribution.proximity riemannXi ⊤ R + ValueDistribution.proximity xiProductMult⁻¹ ⊤ R := by
    have := h_mul R
    simp only [Pi.add_apply] at this
    exact this
  have h_fun_eq : (fun z => riemannXi z * (xiProductMult z)⁻¹) = (riemannXi * xiProductMult⁻¹) := by
    funext z; rfl
  rw [h_fun_eq]
  have hXi_R : ValueDistribution.proximity riemannXi ⊤ R ≤ C_xi * R * Real.log R + D_xi := by
    have := hXi R hR
    unfold proximity at this
    rw [h_bridge_xi] at this; exact this
  have hInv_R : ValueDistribution.proximity xiProductMult⁻¹ ⊤ R ≤
      C_inv * R * (Real.log R)^2 + D_inv := by
    have := hInv R hR
    unfold proximity at this
    rw [h_bridge_Pinv] at this; exact this
  have h_sum : ValueDistribution.proximity (riemannXi * xiProductMult⁻¹) ⊤ R ≤
      C_xi * R * Real.log R + D_xi + (C_inv * R * (Real.log R)^2 + D_inv) := by linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  have hlog_R_nn : 0 ≤ Real.log R := Real.log_nonneg hR
  have hC_xi_le : C_xi ≤ |C_xi| := le_abs_self _
  have hC_inv_le : C_inv ≤ |C_inv| := le_abs_self _
  have hCxi_abs_nn : 0 ≤ |C_xi| := abs_nonneg _
  have hCinv_abs_nn : 0 ≤ |C_inv| := abs_nonneg _
  have hlogSq_nn : 0 ≤ (Real.log R)^2 := sq_nonneg _
  have h_RlogR_bd : R * Real.log R ≤ R * (Real.log R)^2 + Real.exp 1 := by
    rcases le_or_gt R (Real.exp 1) with hRe | hRe
    · have hlogR_le : Real.log R ≤ 1 := by
        have := Real.log_le_log hR_pos hRe
        rwa [Real.log_exp] at this
      have h_RlogR_le_e : R * Real.log R ≤ Real.exp 1 * 1 :=
        mul_le_mul hRe hlogR_le hlog_R_nn (Real.exp_pos _).le
      have h_sqR_nn : 0 ≤ R * (Real.log R)^2 := mul_nonneg hR_nn hlogSq_nn
      linarith
    · have hlogR_ge_one : 1 ≤ Real.log R := by
        have := Real.log_le_log (Real.exp_pos 1) hRe.le
        rwa [Real.log_exp] at this
      have hlog_sq : Real.log R ≤ (Real.log R)^2 := by
        have := mul_le_mul_of_nonneg_left hlogR_ge_one hlog_R_nn
        nlinarith
      have h_RlogR : R * Real.log R ≤ R * (Real.log R)^2 :=
        mul_le_mul_of_nonneg_left hlog_sq hR_nn
      have h_exp_nn : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      linarith
  have h1 : C_xi * R * Real.log R ≤ |C_xi| * R * (Real.log R)^2 + |C_xi| * Real.exp 1 := by
    have h_step_a : C_xi * R * Real.log R ≤ |C_xi| * R * Real.log R := by
      have h_l1 : C_xi * R ≤ |C_xi| * R := mul_le_mul_of_nonneg_right hC_xi_le hR_nn
      exact mul_le_mul_of_nonneg_right h_l1 hlog_R_nn
    have h_step_b : |C_xi| * R * Real.log R ≤ |C_xi| * (R * (Real.log R)^2 + Real.exp 1) := by
      have := mul_le_mul_of_nonneg_left h_RlogR_bd hCxi_abs_nn
      nlinarith
    linarith
  have h2 : C_inv * R * (Real.log R)^2 ≤ |C_inv| * R * (Real.log R)^2 := by
    have h_l1 : C_inv * R ≤ |C_inv| * R := mul_le_mul_of_nonneg_right hC_inv_le hR_nn
    exact mul_le_mul_of_nonneg_right h_l1 hlogSq_nn
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD_xi_le : D_xi ≤ |D_xi| := le_abs_self _
  have hD_inv_le : D_inv ≤ |D_inv| := le_abs_self _
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step F: Poisson representation — pointwise bound from proximity
-- ═══════════════════════════════════════════════════════════════════════════

/-- Since `xiOverP` is entire and zero-free, `log ‖xiOverP‖` is harmonic on
all of ℂ.  The Poisson formula at center 0 radius R gives pointwise
`log ‖xiOverP z‖ ≤ ((R+‖z‖)/(R-‖z‖)) · (m(R, xiOverP) + m(R, 1/xiOverP))`
for `‖z‖ < R`.  Set `R = 2‖z‖` to get `log ‖xiOverP z‖ ≤ 3·O(‖z‖ log²‖z‖)`. -/
theorem xiOverP_pointwise_log_bound :
    ∃ C D : ℝ, ∀ z : ℂ,
      Real.log ‖xiOverP z‖ ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
  obtain ⟨Cp, Dp, hProx⟩ := ZD.xiOverP_proximity_bound
  refine ⟨72 * |Cp|, 48 * |Cp| * (Real.log 3)^2 + 3 * |Dp|, fun z => ?_⟩
  have hLogCont : Continuous (fun z => Real.log ‖xiOverP z‖) :=
    Continuous.log (continuous_norm.comp xiOverP_differentiable.continuous)
      (fun z => norm_ne_zero_iff.mpr (xiOverP_ne_zero z))
  set t := ‖z‖ with ht_def
  have ht_nn : 0 ≤ t := norm_nonneg _
  set R : ℝ := 2 * t + 2 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hR_ge_one : 1 ≤ R := by rw [hR_def]; linarith
  have htR : t < R := by rw [hR_def]; linarith
  have hR_sub : R - t = t + 2 := by rw [hR_def]; ring
  have hR_add : R + t = 3*t + 2 := by rw [hR_def]; ring
  have hHarm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖xiOverP z‖)
      (Metric.closedBall (0:ℂ) R) :=
    fun x _ => (xiOverP_analyticAt x).harmonicAt_log_norm (xiOverP_ne_zero x)
  have hzB : z ∈ Metric.ball (0:ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; exact htR
  have hPoissonEq := hHarm.circleAverage_poissonKernel_smul hzB
  have hPCont : ContinuousOn (fun x => poissonKernel 0 z x) (Metric.sphere (0:ℂ) R) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    refine Complex.continuous_re.continuousOn.comp ?_ (fun _ _ => Set.mem_univ _)
    rw [herglotzRieszKernel_fun_def]
    simp only [sub_zero]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hxR : ‖x‖ = R := by
      have : dist x 0 = R := hx
      rwa [dist_zero_right] at this
    intro hzero
    have hzw : x = z := by
      have h0 : x - z = 0 := by linear_combination hzero
      linear_combination h0
    rw [hzw] at hxR; linarith
  set M : ℝ := (R + t) / (R - t) with hM_def
  have hR_sub_pos : 0 < R - t := by linarith
  have hR_add_nn : 0 ≤ R + t := by linarith
  have hM_nn : 0 ≤ M := div_nonneg hR_add_nn hR_sub_pos.le
  have hM_le_3 : M ≤ 3 := by
    rw [hM_def, hR_sub, hR_add]
    have h2 : 0 < t + 2 := by linarith
    rw [div_le_iff₀ h2]; linarith
  have hBd : ∀ x ∈ Metric.sphere (0:ℂ) |R|,
      (poissonKernel 0 z • (fun w => Real.log ‖xiOverP w‖)) x ≤
        M * max (Real.log ‖xiOverP x‖) 0 := by
    intro x hx
    have hxR : x ∈ Metric.sphere (0:ℂ) R := by
      rw [show |R| = R from abs_of_pos hR_pos] at hx; exact hx
    have hP_le_M : poissonKernel 0 z x ≤ M := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      have h := re_herglotzRieszKernel_le (c := (0:ℂ)) (R := R) (z := x) (w := z) hxR hzB
      simp only [Function.comp_apply]
      rw [herglotzRieszKernel_def]
      simpa using h
    have hP_nn : 0 ≤ poissonKernel 0 z x := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      have hineq := le_re_herglotzRieszKernel (c := (0:ℂ)) (R := R) (z := x) (w := z) hxR hzB
      simp only [Function.comp_apply]
      rw [herglotzRieszKernel_def]
      have h_lb : 0 ≤ (R - t) / (R + t) :=
        div_nonneg hR_sub_pos.le hR_add_nn
      simp only [sub_zero] at hineq
      simp only [sub_zero]
      linarith
    have hlog_le : Real.log ‖xiOverP x‖ ≤ max (Real.log ‖xiOverP x‖) 0 := le_max_left _ _
    show poissonKernel 0 z x * Real.log ‖xiOverP x‖ ≤ M * max (Real.log ‖xiOverP x‖) 0
    have hmax_nn : 0 ≤ max (Real.log ‖xiOverP x‖) 0 := le_max_right _ _
    calc poissonKernel 0 z x * Real.log ‖xiOverP x‖
        ≤ poissonKernel 0 z x * max (Real.log ‖xiOverP x‖) 0 :=
          mul_le_mul_of_nonneg_left hlog_le hP_nn
      _ ≤ M * max (Real.log ‖xiOverP x‖) 0 := mul_le_mul_of_nonneg_right hP_le_M hmax_nn
  have hCI_Plog : CircleIntegrable (poissonKernel 0 z • (fun w => Real.log ‖xiOverP w‖)) 0 R := by
    refine ContinuousOn.circleIntegrable (hR := hR_pos.le) ?_
    exact ContinuousOn.mul hPCont hLogCont.continuousOn
  have hMero_xi : MeromorphicOn xiOverP (Metric.sphere (0:ℂ) |R|) := fun x _ =>
    (xiOverP_analyticAt x).meromorphicAt
  have hCI_posLog : CircleIntegrable (fun w => max (Real.log ‖xiOverP w‖) 0) 0 R := by
    have := circleIntegrable_posLog_norm_meromorphicOn (f := xiOverP)
      (c := (0:ℂ)) (R := R) hMero_xi
    convert this using 1; funext w
    rw [Real.posLog_def, max_comm]
  have hCI_Mpos : CircleIntegrable (fun w => M * max (Real.log ‖xiOverP w‖) 0) 0 R :=
    hCI_posLog.const_mul M
  have h_ca_mono := Real.circleAverage_mono hCI_Plog hCI_Mpos hBd
  rw [hPoissonEq] at h_ca_mono
  have h_rhs_eq : Real.circleAverage (fun w => M * max (Real.log ‖xiOverP w‖) 0) 0 R =
      M * proximity xiOverP R := by
    unfold proximity
    have h1 : (fun w => M * max (Real.log ‖xiOverP w‖) 0) =
        (M • fun w => max (Real.log ‖xiOverP w‖) 0) := by funext w; rfl
    rw [h1, Real.circleAverage_smul, smul_eq_mul]
  rw [h_rhs_eq] at h_ca_mono
  have hPoisson : Real.log ‖xiOverP z‖ ≤ M * proximity xiOverP R := h_ca_mono
  have hProxR : proximity xiOverP R ≤ Cp * R * (Real.log R)^2 + Dp := hProx R hR_ge_one
  have hProx_nn : 0 ≤ proximity xiOverP R := proximity_nonneg _ _
  have habsCp : Cp ≤ |Cp| := le_abs_self _
  have habsCp_nn : 0 ≤ |Cp| := abs_nonneg _
  have habsDp : Dp ≤ |Dp| := le_abs_self _
  have habsDp_nn : 0 ≤ |Dp| := abs_nonneg _
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR_ge_one
  have hR_nn : 0 ≤ R := hR_pos.le
  have h1 : Real.log ‖xiOverP z‖ ≤ 3 * proximity xiOverP R := by
    have hProd_le : M * proximity xiOverP R ≤ 3 * proximity xiOverP R :=
      mul_le_mul_of_nonneg_right hM_le_3 hProx_nn
    linarith
  have h2 : proximity xiOverP R ≤ |Cp| * R * (Real.log R)^2 + |Dp| := by
    have h_Cp : Cp * R * (Real.log R)^2 ≤ |Cp| * R * (Real.log R)^2 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habsCp hR_nn)
        (sq_nonneg (Real.log R))
      linarith
    linarith
  have h3 : Real.log ‖xiOverP z‖ ≤ 3 * |Cp| * R * (Real.log R)^2 + 3 * |Dp| := by
    have h23 : 3 * proximity xiOverP R ≤ 3 * (|Cp| * R * (Real.log R)^2 + |Dp|) := by
      apply mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  have ht_plus_2_pos : 0 < t + 2 := by linarith
  have hlog_t2_ge_log2 : Real.log 2 ≤ Real.log (t + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog_t2_nn : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hlogR_le : Real.log R ≤ 2 * Real.log (t + 2) := by
    have hR_eq : R = 2 * (t + 1) := by rw [hR_def]; ring
    rw [hR_eq]
    have h2_pos : (0:ℝ) < 2 := by norm_num
    have ht1_pos : 0 < t + 1 := by linarith
    rw [Real.log_mul (ne_of_gt h2_pos) (ne_of_gt ht1_pos)]
    have hlog_t1_le : Real.log (t + 1) ≤ Real.log (t + 2) :=
      Real.log_le_log ht1_pos (by linarith)
    linarith
  have hlogSq_le : (Real.log R)^2 ≤ 4 * (Real.log (t + 2))^2 := by
    have : (Real.log R)^2 ≤ (2 * Real.log (t + 2))^2 := by
      apply sq_le_sq'
      · linarith
      · exact hlogR_le
    calc (Real.log R)^2 ≤ (2 * Real.log (t + 2))^2 := this
      _ = 4 * (Real.log (t + 2))^2 := by ring
  have hR_le : R ≤ 2 * (t + 2) := by rw [hR_def]; linarith
  have hRlogSq_le : R * (Real.log R)^2 ≤
      8 * t * (Real.log (t+2))^2 + 16 * (Real.log (t+2))^2 := by
    have hsq_nn : 0 ≤ (Real.log (t+2))^2 := sq_nonneg _
    have hstep1 : R * (Real.log R)^2 ≤ R * (4 * (Real.log (t+2))^2) :=
      mul_le_mul_of_nonneg_left hlogSq_le hR_nn
    have hstep2 : R * (4 * (Real.log (t+2))^2) ≤ 2*(t+2) * (4 * (Real.log (t+2))^2) := by
      apply mul_le_mul_of_nonneg_right hR_le
      exact mul_nonneg (by norm_num) hsq_nn
    have h_expand : 2*(t+2) * (4 * (Real.log (t+2))^2) =
        8 * t * (Real.log (t+2))^2 + 16 * (Real.log (t+2))^2 := by ring
    linarith
  have hlog_t2_sq_bound : (Real.log (t+2))^2 ≤ t * (Real.log (t+2))^2 + (Real.log 3)^2 := by
    rcases le_or_gt 1 t with ht1 | ht1
    · have : (Real.log (t+2))^2 ≤ t * (Real.log (t+2))^2 := by
        have h := mul_le_mul_of_nonneg_right ht1 (sq_nonneg (Real.log (t+2)))
        linarith
      have hlog3_sq_nn : 0 ≤ (Real.log 3)^2 := sq_nonneg _
      linarith
    · have hlog_le_log3 : Real.log (t+2) ≤ Real.log 3 :=
        Real.log_le_log ht_plus_2_pos (by linarith)
      have hlog_t2_sq_le : (Real.log (t+2))^2 ≤ (Real.log 3)^2 := by
        apply sq_le_sq'
        · have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          linarith
        · exact hlog_le_log3
      have ht_log : 0 ≤ t * (Real.log (t+2))^2 := mul_nonneg ht_nn (sq_nonneg _)
      linarith
  have hRlogSq_simplified : R * (Real.log R)^2 ≤
      24 * t * (Real.log (t+2))^2 + 16 * (Real.log 3)^2 := by
    have h := hlog_t2_sq_bound
    have h16 : 16 * (Real.log (t+2))^2 ≤ 16 * (t * (Real.log (t+2))^2 + (Real.log 3)^2) := by
      apply mul_le_mul_of_nonneg_left h (by norm_num)
    have h16' : 16 * (t * (Real.log (t+2))^2 + (Real.log 3)^2) =
        16 * t * (Real.log (t+2))^2 + 16 * (Real.log 3)^2 := by ring
    linarith
  have h_final_term : 3 * |Cp| * R * (Real.log R)^2 ≤
      72 * |Cp| * t * (Real.log (t+2))^2 + 48 * |Cp| * (Real.log 3)^2 := by
    have h3Cp_nn : 0 ≤ 3 * |Cp| := by positivity
    have := mul_le_mul_of_nonneg_left hRlogSq_simplified h3Cp_nn
    nlinarith [habsCp_nn, sq_nonneg (Real.log (t+2)), sq_nonneg (Real.log 3), ht_nn]
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Main: unconditional mean-type-2 growth of `xiOverP`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **UNCONDITIONAL growth bound.**  For all `z ∈ ℂ`,
`‖xiOverP z‖ ≤ exp (C ‖z‖ log²(‖z‖ + 2) + D)`.

Feeds directly into the generalized `logDeriv_xiOverP_const_of_logSqGrowth`
helper in `WeilHadamardOpenPatch`. -/
theorem xiOverP_growth_meanType :
    ∃ C D : ℝ, ∀ z : ℂ,
      ‖xiOverP z‖ ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) := by
  obtain ⟨C, D, hBound⟩ := xiOverP_pointwise_log_bound
  refine ⟨C, D, fun z => ?_⟩
  have h_xi_ne : xiOverP z ≠ 0 := xiOverP_ne_zero z
  have h_pos : 0 < ‖xiOverP z‖ := norm_pos_iff.mpr h_xi_ne
  have h_logle : Real.log ‖xiOverP z‖ ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D :=
    hBound z
  have h_exp_mono :
      Real.exp (Real.log ‖xiOverP z‖) ≤
        Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) :=
    Real.exp_le_exp.mpr h_logle
  rw [Real.exp_log h_pos] at h_exp_mono
  exact h_exp_mono

end ZD
end
