import Mathlib
import RequestProject.XiWeierstrassFactor
import RequestProject.ZeroCountJensen

/-!
# Locally uniformly convergent Weierstrass product over nontrivial ζ zeros

For every compact K ⊂ ℂ, `∏_ρ (1 + xiWeierstrassTerm ρ z)` converges absolutely
and uniformly, hence locally uniformly on ℂ. This uses:

* **`Σ_ρ 1/‖ρ‖² < ∞`**: proved by the same dyadic argument as
  `ZeroCountJensen.nontrivialZeros_inv_sq_summable`, adapted from the
  `1/normSq(ρ(ρ-1))` form to the weaker `1/‖ρ‖²`. Uses
  `xi_zero_count_disk_bound` + `summable_nat_succ_div_two_pow`.
* **Per-compact majorant**: for `‖z‖ ≤ M` and `‖ρ‖ ≥ M`,
  `‖xiWeierstrassTerm ρ z‖ ≤ 3M²/‖ρ‖²` from H1's quadratic bound.
* **Mathlib**: `multipliableUniformlyOn_one_add` (compact K) +
  `multipliableLocallyUniformlyOn_of_of_forall_exists_nhds` (lift to ℂ).

Deliverable: `xiWeierstrassProduct_multipliableLocallyUniformlyOn` and the
definition `xiProduct z := ∏' ρ : NontrivialZeros, (1 + xiWeierstrassTerm ρ.val z)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

/-- **Helper summability**: `Σ_{k ≥ 0} (k+1)/2^k < ∞`. Majorant for the
dyadic-shell bound `1/‖ρ‖²` over nontrivial zeros. -/
theorem summable_nat_succ_div_two_pow :
    Summable (fun k : ℕ => (k + 1 : ℝ) / 2 ^ k) := by
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
    convert this using 1
    funext k
    simp [pow_one]
  have h2 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h_sum : Summable (fun k : ℕ => (k : ℝ) * (1 / 2) ^ k + (1 / 2 : ℝ) ^ k) :=
    h1.add h2
  convert h_sum using 1
  funext k
  have h_eq : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
  rw [h_eq]
  field_simp

/-- **Main summability** for the Weierstrass product: `Σ_ρ 1/‖ρ‖² < ∞` over
nontrivial zeros. Proven by the same dyadic-shell argument as
`nontrivialZeros_inv_sq_summable`, with the `1/‖ρ‖²` per-element bound
(instead of `4/‖ρ‖⁴`) and the `(k+1)/2^k` dyadic majorant (instead of
`(k+1)/8^k`).

Uses `xi_zero_count_disk_bound` (N(R) = O(R log R)) to bound the shell
cardinality. -/
theorem summable_inv_norm_sq_nontrivialZeros :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => (1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  -- Use the dyadic argument: partition zeros by `‖ρ‖ ∈ [2^k, 2^{k+1})`.
  -- (lo) ‖ρ‖ < 2: absorbed into M_lo.
  -- (mid) 2 ≤ ‖ρ‖ < 2^(N+1): absorbed into M_mid.
  -- (hi) ‖ρ‖ ≥ 2^(N+1): dyadic shells k ≥ N, shell contribution ≤
  --   (2·C·log 2) · (k+1)/2^k; geometric series converges.
  obtain ⟨C₃, hC₃, R₀_step3, hR₀_step3, hBound_step3⟩ :=
      ZD.ZeroCount.xi_zero_count_disk_bound
  -- N with 2^N ≥ max(R₀_step3, 2).
  set R_th : ℝ := max R₀_step3 2 with hRth_def
  have hRth_pos : 0 < R_th := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hRth_ge_two : (2 : ℝ) ≤ R_th := le_max_right _ _
  have hRth_ge_R₀ : R₀_step3 ≤ R_th := le_max_left _ _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R_th ≤ (2 : ℝ) ^ N := by
    rcases pow_unbounded_of_one_lt R_th (by norm_num : (1:ℝ) < 2) with ⟨N, hN⟩
    exact ⟨N, le_of_lt hN⟩
  set M_lo : ℝ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite 2).toFinset.sum
      (fun ρ => 1 / ‖ρ‖ ^ 2) with hM_lo_def
  set M_mid : ℝ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
      ((2 : ℝ) ^ (N + 1))).toFinset.sum (fun ρ => 1 / ‖ρ‖ ^ 2) with hM_mid_def
  set C_tail : ℝ := 2 * C₃ * Real.log 2 with hC_tail_def
  refine summable_of_sum_le
    (fun ρ => div_nonneg (by norm_num) (by positivity))
    (c := M_lo + M_mid + C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2)]
  -- lo part
  have h_lo_bound :
      (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), 1 / ‖ρ.val‖ ^ 2) ≤ M_lo := by
    rw [hM_lo_def]
    rw [show (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), (1 : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2)).image Subtype.val,
            (1 : ℝ) / ‖ρ‖ ^ 2 from ?_]
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
        subst hρ'_eq; linarith [hρ'_in.2]
    · intros; positivity
  -- Split hi=not-lo into mid (< 2^{N+1}) and tail (≥ 2^{N+1}).
  rw [← Finset.sum_filter_add_sum_filter_not (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2))
    (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))]
  -- mid part
  have h_mid_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
        1 / ‖ρ.val‖ ^ 2) ≤ M_mid := by
    rw [hM_mid_def]
    rw [show
        (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
            (1 : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ ((u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))).image Subtype.val,
            (1 : ℝ) / ‖ρ‖ ^ 2 from ?_]
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
        subst hρ'_eq; linarith [hρ'_in.2]
    · intros; positivity
  -- hi part (tail)
  have h_hi_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
        1 / ‖ρ.val‖ ^ 2)
      ≤ C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k := by
    set S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
      (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
        (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)) with hS_def
    have h_mem : ∀ ρ ∈ S, (2 : ℝ) ^ (N + 1) ≤ ‖ρ.val‖ := by
      intro ρ hρ
      simp only [hS_def, Finset.mem_filter, not_lt] at hρ
      exact hρ.2
    have h_one_le : ∀ ρ ∈ S, (1 : ℝ) ≤ ‖ρ.val‖ := by
      intro ρ hρ
      have hle := h_mem ρ hρ
      have h2N1_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
      linarith
    let kf : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℕ := fun ρ =>
      if h : (1 : ℝ) ≤ ‖ρ.val‖
      then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
      else 0
    have h_kf_prop :
        ∀ ρ ∈ S, (2 : ℝ) ^ kf ρ ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 1) := by
      intro ρ hρ
      have h := h_one_le ρ hρ
      simp only [kf, dif_pos h]
      exact (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose_spec
    have h_kf_ge : ∀ ρ ∈ S, N + 1 ≤ kf ρ := by
      intro ρ hρ
      have ⟨_, h_lt⟩ := h_kf_prop ρ hρ
      have h_ge := h_mem ρ hρ
      have hlt_pow : (2 : ℝ) ^ (N + 1) < (2 : ℝ) ^ (kf ρ + 1) := lt_of_le_of_lt h_ge h_lt
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hlt_pow
      omega
    set K_max : ℕ := S.sup kf + 1 with hKmax_def
    have h_kf_le : ∀ ρ ∈ S, kf ρ < K_max := by
      intro ρ hρ
      have := Finset.le_sup (f := kf) hρ
      omega
    -- Per-element bound: 1/‖ρ‖² ≤ 1/(2^k)² = 1/4^k = 1/(2^(2k)).
    have h_per_elem :
        ∀ ρ ∈ S, (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤ 1 / (2 : ℝ) ^ (2 * kf ρ) := by
      intro ρ hρ
      have ⟨h_pow_le, _⟩ := h_kf_prop ρ hρ
      have h_one := h_one_le ρ hρ
      have h_pos : (0 : ℝ) < ‖ρ.val‖ := by linarith
      have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ kf ρ := pow_pos (by norm_num) _
      have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * kf ρ) := pow_pos (by norm_num) _
      have h_rho_pow2_pos : (0 : ℝ) < ‖ρ.val‖ ^ 2 := by positivity
      have h_pow2_le : (2 : ℝ) ^ (2 * kf ρ) ≤ ‖ρ.val‖ ^ 2 := by
        rw [show (2 * kf ρ) = (kf ρ) * 2 from by ring, pow_mul]
        exact pow_le_pow_left₀ h_pow_pos.le h_pow_le 2
      rw [div_le_div_iff₀ h_rho_pow2_pos h_pow2k_pos]
      linarith
    calc (∑ ρ ∈ S, (1 : ℝ) / ‖ρ.val‖ ^ 2)
        ≤ ∑ ρ ∈ S, (1 : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
          apply Finset.sum_le_sum h_per_elem
      _ = ∑ k ∈ Finset.range K_max,
            ∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (1 : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (t := Finset.range K_max) (g := kf)
            (f := fun ρ => (1 : ℝ) / (2 : ℝ) ^ (2 * kf ρ))]
          intro ρ hρ
          exact Finset.mem_range.mpr (h_kf_le ρ hρ)
      _ = ∑ k ∈ Finset.range K_max,
            (S.filter (fun ρ => kf ρ = k)).card *
              ((1 : ℝ) / (2 : ℝ) ^ (2 * k)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_congr rfl
            (g := fun _ => (1 : ℝ) / (2 : ℝ) ^ (2 * k))]
          · rw [Finset.sum_const, nsmul_eq_mul]
          · intro ρ hρ
            simp only [Finset.mem_filter] at hρ
            rw [hρ.2]
      _ ≤ ∑ k ∈ Finset.range K_max,
            (if N + 1 ≤ k then C_tail * (k + 1 : ℝ) / 2 ^ k else 0) := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk_ge : N + 1 ≤ k
          · rw [if_pos hk_ge]
            have h_subset_NTZ :
                (S.filter (fun ρ => kf ρ = k)).image Subtype.val ⊆
                  (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
                    ((2 : ℝ) ^ (k + 1))).toFinset := by
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨ρ, hρ_in, hρ_eq⟩
              simp only [Finset.mem_filter] at hρ_in
              have hρ_in_S := hρ_in.1
              have h_kfeq := hρ_in.2
              simp only [Set.Finite.mem_toFinset]
              refine ⟨?_, ?_⟩
              · subst hρ_eq; exact ρ.property
              · rw [Metric.mem_closedBall, dist_zero_right]
                have ⟨_, h_lt⟩ := h_kf_prop ρ hρ_in_S
                rw [h_kfeq] at h_lt
                subst hρ_eq
                linarith
            have h_card_eq :
                (S.filter (fun ρ => kf ρ = k)).card =
                  ((S.filter (fun ρ => kf ρ = k)).image Subtype.val).card := by
              rw [Finset.card_image_of_injective _ Subtype.val_injective]
            have h_ncard_bound :
                ((NontrivialZeros ∩
                  Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) ≤
                C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
              have h_R_ge : R₀_step3 ≤ (2 : ℝ) ^ (k + 1) := by
                calc R₀_step3 ≤ R_th := hRth_ge_R₀
                  _ ≤ (2 : ℝ) ^ N := hN
                  _ ≤ (2 : ℝ) ^ (k + 1) :=
                      pow_le_pow_right₀ (by norm_num) (by omega)
              have h_sub :
                  NontrivialZeros ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ⊆
                  Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                    {z | ZD.riemannXi z = 0} := by
                intro z hz
                exact ⟨hz.2, ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros z hz.1⟩
              have hfin_big :=
                ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall ((2 : ℝ) ^ (k + 1))
              have h_ncard_mono :
                  (NontrivialZeros ∩
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard ≤
                  (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                    {z | ZD.riemannXi z = 0}).ncard :=
                Set.ncard_le_ncard h_sub hfin_big
              calc ((NontrivialZeros ∩
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ)
                  ≤ (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                    {z | ZD.riemannXi z = 0}).ncard := by exact_mod_cast h_ncard_mono
                _ ≤ _ := hBound_step3 _ h_R_ge
            have h_card_le :
                ((S.filter (fun ρ => kf ρ = k)).card : ℝ) ≤
                ((NontrivialZeros ∩
                  Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) := by
              rw [h_card_eq]
              rw [Set.ncard_eq_toFinset_card _
                (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ (k + 1)))]
              exact_mod_cast Finset.card_le_card h_subset_NTZ
            have h_log_pow :
                Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
              rw [Real.log_pow]; push_cast; ring
            have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := pow_pos (by norm_num) _
            have hdiv_nn : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (2 * k) := by positivity
            calc ((S.filter (fun ρ => kf ρ = k)).card : ℝ) * (1 / (2 : ℝ) ^ (2 * k))
                ≤ ((NontrivialZeros ∩
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) *
                    (1 / (2 : ℝ) ^ (2 * k)) :=
                  mul_le_mul_of_nonneg_right h_card_le hdiv_nn
              _ ≤ (C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1))) *
                    (1 / (2 : ℝ) ^ (2 * k)) :=
                  mul_le_mul_of_nonneg_right h_ncard_bound hdiv_nn
              _ = C_tail * (k + 1 : ℝ) / 2 ^ k := by
                  rw [h_log_pow, hC_tail_def]
                  have h2pk1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
                    rw [pow_succ]; ring
                  have h22k : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
                    rw [show (2 * k) = k * 2 from by ring, pow_mul]
                  have hpk_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
                  rw [h2pk1, h22k]
                  field_simp
          · rw [if_neg hk_ge]
            have h_filter_empty : S.filter (fun ρ => kf ρ = k) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro ρ hρ heq
              have := h_kf_ge ρ hρ
              omega
            rw [h_filter_empty]
            simp
      _ ≤ ∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk_ge : N + 1 ≤ k
          · rw [if_pos hk_ge]
          · rw [if_neg hk_ge]
            have : 0 ≤ C_tail * (k + 1 : ℝ) / 2 ^ k := by
              rw [hC_tail_def]; positivity
            linarith
      _ ≤ C_tail * ∑' k : ℕ, ((k : ℝ) + 1) / 2 ^ k := by
          have h_sum_eq :
              (∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k) =
                C_tail * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 1) / 2 ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intros; ring
          rw [h_sum_eq]
          apply mul_le_mul_of_nonneg_left _ (by rw [hC_tail_def]; positivity)
          have h_summ := summable_nat_succ_div_two_pow
          have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) / 2 ^ k := fun k => by positivity
          exact Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ
  linarith

#print axioms summable_nat_succ_div_two_pow
#print axioms summable_inv_norm_sq_nontrivialZeros

-- ═══════════════════════════════════════════════════════════════════════════
-- § Multipliability of the Weierstrass product on ℂ
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Majorant on a closed ball**: for `z ∈ closedBall 0 M` and `‖ρ‖ ≥ M`,
`‖xiWeierstrassTerm ρ z‖ ≤ 3 M² / ‖ρ‖²`. Immediate consequence of H1's quadratic bound.

Only finitely many nontrivial zeros have `‖ρ‖ < M` (by
`NontrivialZeros_inter_closedBall_finite`), so the bound holds cofinitely. -/
theorem xiWeierstrassTerm_closedBall_bound (M : ℝ) (hM : 0 < M) :
    ∀ᶠ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} in cofinite,
      ∀ z ∈ Metric.closedBall (0 : ℂ) M,
        ‖xiWeierstrassTerm ρ.val z‖ ≤ 3 * M ^ 2 / ‖ρ.val‖ ^ 2 := by
  have hfin : {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < M}.Finite := by
    have h_ntz_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) M).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite M
    have h_image_fin :
        ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
          {ρ | ‖ρ.val‖ < M}).Finite := by
      apply h_ntz_fin.subset
      intro z hz
      rcases hz with ⟨ρ, hρ_lt, hρ_eq⟩
      simp only [Set.mem_setOf_eq] at hρ_lt
      subst hρ_eq
      refine ⟨ρ.property, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    exact h_image_fin.of_finite_image Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with ρ hρ
  have hρ_ge_M : M ≤ ‖ρ.val‖ := by
    by_contra h; push_neg at h; exact hρ h
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hz_le_ρ : ‖z‖ ≤ ‖ρ.val‖ := le_trans hz hρ_ge_M
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hρ_ge_M
    linarith
  have hbound := norm_xiWeierstrassTerm_le hρ_ne hz_le_ρ
  have hρ_sq_pos : (0 : ℝ) < ‖ρ.val‖ ^ 2 := by positivity
  calc ‖xiWeierstrassTerm ρ.val z‖
      ≤ 3 * ‖z‖ ^ 2 / ‖ρ.val‖ ^ 2 := hbound
    _ ≤ 3 * M ^ 2 / ‖ρ.val‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ hρ_sq_pos.le
        have h_z_sq_le : ‖z‖ ^ 2 ≤ M ^ 2 := by
          have h_z_nn : 0 ≤ ‖z‖ := norm_nonneg _
          have hM_nn : 0 ≤ M := hM.le
          exact pow_le_pow_left₀ h_z_nn hz 2
        linarith

#print axioms xiWeierstrassTerm_closedBall_bound

/-- **Multipliable on compact balls**: `∏_ρ (1 + xiWeierstrassTerm ρ z)` is
uniformly convergent on `closedBall 0 M` for every M > 0. -/
theorem xiWeierstrassProduct_multipliableUniformlyOn_closedBall (M : ℝ) (hM : 0 < M) :
    MultipliableUniformlyOn
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        fun z : ℂ => 1 + xiWeierstrassTerm ρ.val z)
      (Metric.closedBall (0 : ℂ) M) := by
  set u : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ :=
    fun ρ => 3 * M ^ 2 / ‖ρ.val‖ ^ 2 with hu_def
  have hu_summable : Summable u := by
    have := summable_inv_norm_sq_nontrivialZeros.mul_left (3 * M ^ 2)
    refine this.congr ?_
    intro ρ
    show 3 * M ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) = u ρ
    rw [hu_def]
    ring
  have h_bound := xiWeierstrassTerm_closedBall_bound M hM
  apply Summable.multipliableUniformlyOn_one_add (isCompact_closedBall _ _) hu_summable h_bound
  intro ρ
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
    rw [heq] at hre
    simp at hre
  exact (xiWeierstrassTerm_differentiable hρ_ne).continuous.continuousOn

#print axioms xiWeierstrassProduct_multipliableUniformlyOn_closedBall

/-- **Main: multipliable locally uniformly on ℂ**. The Weierstrass product
over nontrivial zeros converges locally uniformly on all of ℂ. -/
theorem xiWeierstrassProduct_multipliableLocallyUniformlyOn_univ :
    MultipliableLocallyUniformlyOn
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        fun z : ℂ => 1 + xiWeierstrassTerm ρ.val z) Set.univ := by
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z _
  refine ⟨Metric.closedBall z 1, ?_, ?_⟩
  · -- closedBall z 1 is a nhds-within-univ of z.
    have : Metric.closedBall z 1 ∈ nhds z := Metric.closedBall_mem_nhds z zero_lt_one
    exact nhdsWithin_le_nhds this
  · -- Multipliable uniformly on closedBall z 1. Need to shift to closedBall 0 (‖z‖ + 1).
    -- Any closed ball is contained in a closedBall 0 M for M = ‖z‖ + 1.
    set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have h_sub : Metric.closedBall z 1 ⊆ Metric.closedBall (0 : ℂ) M := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall] at hw
      calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            have := norm_sub_norm_le w z
            linarith [norm_sub_rev w z]
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖z‖ := by linarith
        _ = M := by rw [hM_def]; ring
    exact (xiWeierstrassProduct_multipliableUniformlyOn_closedBall M hM_pos).mono h_sub

#print axioms xiWeierstrassProduct_multipliableLocallyUniformlyOn_univ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Definition of xiProduct
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The Weierstrass product over nontrivial zeros**: candidate for the
Hadamard factorization of ξ. Defined as `∏' ρ, (1 + xiWeierstrassTerm ρ.val z)`
= `∏' ρ, E₁(z/ρ)`. -/
def xiProduct (z : ℂ) : ℂ :=
  ∏' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, (1 + xiWeierstrassTerm ρ.val z)

#print axioms xiProduct

end ZD
