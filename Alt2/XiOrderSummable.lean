import Mathlib
import RequestProject.XiOrder
import RequestProject.XiProduct

/-!
# Multiplicity-weighted summability `Σ_ρ xiOrderNat(ρ) / ‖ρ‖² < ∞`

The key unconditional input for the multiplicity-indexed Weierstrass product.

Strategy: reuse the infrastructure of `xi_zero_count_disk_bound` (which
already employs divisor-weighted Jensen) to prove the stronger weighted
count, then run the same dyadic argument as in
`summable_inv_norm_sq_nontrivialZeros`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZD

/-- **Multiplicity-weighted zero count bound** for `riemannXi` in a closed ball.
For `R` large, `Σ_{ρ ∈ closedBall R} divisor_ξ(ρ) ≤ C · R · log R`.

Proof: Jensen identity at radius 2R gives `Σ_u divisor(u) · log(2R/‖u‖) + log‖ξ(0)‖
= circleAverage`. Since ξ has order-one growth and `log‖ξ(0)‖ = -log 2`:
`Σ_u divisor(u) · log(2R/‖u‖) ≤ C·R·log R + log 2`. For u with ‖u‖ ≤ R,
`log(2R/‖u‖) ≥ log 2 > 0`, giving `(log 2) · weighted_count ≤ C·R·log R + log 2`. -/
theorem xi_weighted_zero_count_disk_bound :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ∀ (S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros}),
        (∀ ρ ∈ S, ‖ρ.val‖ ≤ R) →
        ((∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ)) ≤ C * R * Real.log R) := by
  obtain ⟨C1, hC1_pos, R1, hR1_pos, hBound1⟩ := ZD.ZeroCount.xi_order_one_log_bound
  refine ⟨(4 * C1 + 4) / Real.log 2, by positivity, max R1 (Real.exp 1), by positivity, ?_⟩
  intro R hR S hS_bd
  have hR_R1 : R1 ≤ R := le_trans (le_max_left _ _) hR
  have hR_e : Real.exp 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR_e
  have hR_ge_one : (1 : ℝ) ≤ R := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  have hR_log_ge_1 : (1 : ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_e
    rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Set up Jensen at 2R.
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have h2R_R1 : R1 ≤ 2 * R := by linarith
  have habs2R : |(2:ℝ) * R| = 2 * R := abs_of_pos h2R_pos
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) (|(2:ℝ) * R|) with hCB_def
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi CB :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hMero : MeromorphicOn ZD.riemannXi CB := hAnal.meromorphicOn
  -- Connect Finset S to divisor: divisor(ρ) = xiOrderNat(ρ) for ρ ∈ NontrivialZeros in CB.
  -- Each ρ ∈ S has ‖ρ.val‖ ≤ R ≤ 2R = |2R|, so ρ.val ∈ CB.
  have hS_sub_CB : ∀ ρ ∈ S, ρ.val ∈ CB := by
    intro ρ hρ
    rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R]
    linarith [hS_bd ρ hρ]
  -- At each ρ ∈ NontrivialZeros ∩ CB: divisor ξ CB ρ = xiOrderNat ρ = analyticOrderNatAt ξ ρ.
  have h_divisor_eq_order : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, ρ.val ∈ CB →
      (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) = ZD.xiOrderNat ρ.val := by
    intro ρ hρ_cb
    have hAnalρ : AnalyticAt ℂ ZD.riemannXi ρ.val :=
      ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ.val (Set.mem_univ _)
    have h_ord_ne_top := riemannXi_analyticOrderAt_ne_top_everywhere ρ.val
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt ZD.riemannXi ρ.val :=
      ENat.ne_top_iff_exists.mp h_ord_ne_top
    have h_nat_eq : ZD.xiOrderNat ρ.val = n := by
      unfold ZD.xiOrderNat analyticOrderNatAt
      rw [← hn]
      simp
    rw [MeromorphicOn.divisor_apply hMero hρ_cb, hAnalρ.meromorphicOrderAt_eq, ← hn]
    simp [h_nat_eq]
  -- Convert S-sum to divisor sum on CB.
  have h_S_sum_eq_divisor_finsum :
      (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ)) =
      ∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact (h_divisor_eq_order ρ (hS_sub_CB ρ hρ)).symm
  rw [h_S_sum_eq_divisor_finsum]
  -- Jensen identity (keep `|2*R|` form to match CB).
  have hJensen := ZD.ZeroCount.xi_jensen_at_zero (2 * R) h2R_pos
  have hAnalSph : AnalyticOnNhd ℂ ZD.riemannXi (Metric.sphere (0 : ℂ) (|2 * R|)) :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hCI : CircleIntegrable (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) :=
    circleIntegrable_log_norm_meromorphicOn hAnalSph.meromorphicOn
  have hCircAvg_le :
      circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) ≤
        C1 * (2 * R) * Real.log (2 * R) := by
    apply circleAverage_mono_on_of_le_circle hCI
    intro s hs
    rw [Metric.mem_sphere, dist_zero_right, habs2R] at hs
    have h_log_le : Real.log ‖ZD.riemannXi s‖ ≤ Real.log (‖ZD.riemannXi s‖ + 1) := by
      rcases eq_or_lt_of_le (norm_nonneg (ZD.riemannXi s)) with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact Real.log_nonneg (by linarith [norm_nonneg (ZD.riemannXi s)])
      · exact Real.log_le_log hpos (by linarith)
    have h_bd := hBound1 (2 * R) h2R_R1 s (le_of_eq hs)
    linarith
  have hlog_xi0 : Real.log ‖ZD.riemannXi 0‖ = -Real.log 2 := by
    rw [ZD.ZeroCount.riemannXi_zero]; simp
  -- The full divisor-weighted Jensen finsum ≤ C1·2R·log(2R) + log 2.
  have h_full_finsum_bd :
      (∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) * Real.log (2 * R * ‖u‖⁻¹))
        ≤ C1 * (2 * R) * Real.log (2 * R) + Real.log 2 := by
    have h_eq : (∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
        Real.log (2 * R * ‖u‖⁻¹)) =
        circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) -
          Real.log ‖ZD.riemannXi 0‖ := by rw [hJensen]; ring
    rw [h_eq, hlog_xi0]; linarith
  -- Nonnegativity of each divisor term in the finsum.
  have hD_nn : ∀ u, 0 ≤ MeromorphicOn.divisor ZD.riemannXi CB u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnal u
  -- Each term: div(u) · log(2R/‖u‖) ≥ 0 on CB (since ‖u‖ ≤ 2R).
  have h_term_nn : ∀ u, 0 ≤ (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                           Real.log (2 * R * ‖u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ CB
    · rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R] at hu
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · have h_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hlog_nn : 0 ≤ Real.log (2 * R * ‖u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show (2 * R * ‖u‖⁻¹) = (2 * R) / ‖u‖ from by ring, le_div_iff₀ h_norm_pos]
          linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := (MeromorphicOn.divisor ZD.riemannXi CB).apply_eq_zero_of_notMem hu
      simp [hD0]
  -- Lower-bound the sum over S by (log 2) · (Σ_ρ∈S divisor ρ.val) via log(2R/‖ρ‖) ≥ log 2
  -- when ‖ρ‖ ≤ R.
  have h_S_lower :
      (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ)) * Real.log 2 ≤
      ∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) *
        Real.log (2 * R * ‖ρ.val‖⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hρ_le_R : ‖ρ.val‖ ≤ R := hS_bd ρ hρ
    have hρ_ne : ρ.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
      rw [heq] at hre; simp at hre
    have h_norm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ_ne
    have hlog_ge : Real.log 2 ≤ Real.log (2 * R * ‖ρ.val‖⁻¹) := by
      apply Real.log_le_log (by norm_num)
      rw [show (2 * R * ‖ρ.val‖⁻¹) = (2 * R) / ‖ρ.val‖ from by ring, le_div_iff₀ h_norm_pos]
      linarith
    exact mul_le_mul_of_nonneg_left hlog_ge (by exact_mod_cast hD_nn ρ.val)
  -- Injectivity of Subtype.val on S (needed to cast sum to finsum).
  have hS_inj : Set.InjOn (fun ρ : {ρ // ρ ∈ NontrivialZeros} => ρ.val) S := by
    intro x _ y _ h; exact Subtype.val_injective h
  -- Bound the S-weighted sum by the full finsum via injection.
  have h_S_to_finsum :
      (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) *
        Real.log (2 * R * ‖ρ.val‖⁻¹)) ≤
      ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
        Real.log (2 * R * ‖u‖⁻¹) := by
    -- Convert the S-sum to a sum over the image (via Finset.sum_image).
    have h_image :
        (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) *
            Real.log (2 * R * ‖ρ.val‖⁻¹)) =
        ∑ u ∈ S.image Subtype.val,
          (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) * Real.log (2 * R * ‖u‖⁻¹) := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
    rw [h_image]
    -- Apply finsum_le_finsum-style: a Finset sum ≤ finsum when summand nonneg.
    have h_fs : (Function.support fun u => (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
        Real.log (2 * R * ‖u‖⁻¹)).Finite := by
      apply ((MeromorphicOn.divisor ZD.riemannXi CB).finiteSupport
        (isCompact_closedBall 0 _)).subset
      intro u hu
      simp only [Function.mem_support] at hu ⊢
      intro hd; apply hu; rw [hd]; simp
    rw [finsum_eq_sum _ h_fs]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      simp only [Set.Finite.mem_toFinset, Function.mem_support]
      rw [Finset.mem_image] at hu
      obtain ⟨ρ, hρ, rfl⟩ := hu
      -- Need the S-image term to be in divisor's support.
      -- Divisor(ρ.val) ≥ 1 > 0 since ρ is a zero of ξ.
      have hρ_zero : ZD.riemannXi ρ.val = 0 :=
        (riemannXi_eq_zero_iff _).mpr ρ.property
      have h_div_ge_1 : (1 : ℤ) ≤ MeromorphicOn.divisor ZD.riemannXi CB ρ.val :=
        ZD.ZeroCount.xi_divisor_ge_one_of_zero hMero ρ.val (hS_sub_CB ρ hρ) hρ_zero
      intro h_prod_zero
      -- The product = 0 iff div = 0 or log = 0.
      rcases mul_eq_zero.mp h_prod_zero with hd | hl
      · have : (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) = 0 := hd
        have : MeromorphicOn.divisor ZD.riemannXi CB ρ.val = 0 := by exact_mod_cast this
        rw [this] at h_div_ge_1; norm_num at h_div_ge_1
      · -- log(2R/‖ρ‖) = 0 means 2R/‖ρ‖ = 1 or 0, i.e., ‖ρ‖ = 2R or 0. First impossible
        -- (‖ρ‖ ≤ R < 2R), second impossible (ρ is a nontrivial zero).
        have hρ_le_R : ‖ρ.val‖ ≤ R := hS_bd ρ hρ
        have hρ_ne : ρ.val ≠ 0 := by
          intro heq
          have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
          rw [heq] at hre; simp at hre
        have h_norm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ_ne
        have : Real.log (2 * R * ‖ρ.val‖⁻¹) > 0 := by
          apply Real.log_pos
          rw [show (2 * R * ‖ρ.val‖⁻¹) = (2 * R) / ‖ρ.val‖ from by ring,
            lt_div_iff₀ h_norm_pos, one_mul]
          linarith
        linarith
    · intros; exact h_term_nn _
  -- Chain: S-weighted-count · log 2 ≤ S-log-weighted-sum ≤ full-finsum ≤ C1·2R·log(2R) + log 2.
  have h_chain :
      (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ)) * Real.log 2 ≤
      C1 * (2 * R) * Real.log (2 * R) + Real.log 2 := by
    calc (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ)) * Real.log 2
        ≤ ∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ) *
            Real.log (2 * R * ‖ρ.val‖⁻¹) := h_S_lower
      _ ≤ ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
            Real.log (2 * R * ‖u‖⁻¹) := h_S_to_finsum
      _ ≤ C1 * (2 * R) * Real.log (2 * R) + Real.log 2 := h_full_finsum_bd
  -- Divide by log 2.
  have h_divide :
      (∑ ρ ∈ S, (MeromorphicOn.divisor ZD.riemannXi CB ρ.val : ℝ)) ≤
      (C1 * (2 * R) * Real.log (2 * R) + Real.log 2) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr h_chain
  -- Bound the RHS.
  have h_log_2R_le : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR_pos.ne']
    have : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num)
      (le_trans Real.exp_one_gt_two.le hR_e)
    linarith
  have h_final_bd :
      (C1 * (2 * R) * Real.log (2 * R) + Real.log 2) / Real.log 2 ≤
      (4 * C1 + 4) / Real.log 2 * R * Real.log R := by
    have h_num : C1 * (2 * R) * Real.log (2 * R) + Real.log 2 ≤
        (4 * C1 + 4) * R * Real.log R := by
      have h1 : C1 * (2 * R) * Real.log (2 * R) ≤ 4 * C1 * R * Real.log R := by
        calc C1 * (2 * R) * Real.log (2 * R)
            ≤ C1 * (2 * R) * (2 * Real.log R) := by
              apply mul_le_mul_of_nonneg_left h_log_2R_le; positivity
          _ = 4 * C1 * R * Real.log R := by ring
      have h2 : Real.log 2 ≤ 4 * R * Real.log R := by
        have hR_ge_two : Real.log 2 ≤ 1 :=
          (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
        have : (1 : ℝ) ≤ 4 * R * Real.log R := by
          nlinarith [hR_ge_one, hR_log_ge_1]
        linarith
      linarith
    rw [div_le_iff₀ hlog2_pos]
    calc C1 * (2 * R) * Real.log (2 * R) + Real.log 2
        ≤ (4 * C1 + 4) * R * Real.log R := h_num
      _ = (4 * C1 + 4) / Real.log 2 * R * Real.log R * Real.log 2 := by
          field_simp
  exact le_trans h_divide h_final_bd

#print axioms xi_weighted_zero_count_disk_bound

-- ═══════════════════════════════════════════════════════════════════════════
-- § Multiplicity-weighted summability `Σ_ρ xiOrderNat(ρ) / ‖ρ‖² < ∞`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Summability of `xiOrderNat(ρ) / ‖ρ‖²`** over nontrivial zeros. Dyadic
argument using the weighted count from `xi_weighted_zero_count_disk_bound`. -/
theorem summable_xiOrderNat_div_norm_sq_nontrivialZeros :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  obtain ⟨C₃, hC₃, R₀_step3, hR₀_step3, hBound_step3⟩ := xi_weighted_zero_count_disk_bound
  -- Dyadic partition as in summable_inv_norm_sq_nontrivialZeros, but with
  -- xiOrderNat weight.
  set R_th : ℝ := max R₀_step3 2 with hRth_def
  have hRth_ge_R₀ : R₀_step3 ≤ R_th := le_max_left _ _
  have hRth_ge_two : (2 : ℝ) ≤ R_th := le_max_right _ _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R_th ≤ (2 : ℝ) ^ N := by
    rcases pow_unbounded_of_one_lt R_th (by norm_num : (1:ℝ) < 2) with ⟨N, hN⟩
    exact ⟨N, le_of_lt hN⟩
  set M_lo : ℝ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite 2).toFinset.sum
      (fun ρ => (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2) with hM_lo_def
  set M_mid : ℝ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
      ((2 : ℝ) ^ (N + 1))).toFinset.sum
        (fun ρ => (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2) with hM_mid_def
  set C_tail : ℝ := 2 * C₃ with hC_tail_def
  refine summable_of_sum_le
    (fun ρ => div_nonneg (by positivity) (by positivity))
    (c := M_lo + M_mid + C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2)]
  have h_lo_bound :
      (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2),
        (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ M_lo := by
    rw [hM_lo_def]
    rw [show (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2),
          (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2)).image Subtype.val,
            (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2 from ?_]
    swap
    · rw [Finset.sum_image]; intro x _ y _ h; exact Subtype.val_injective h
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
  rw [← Finset.sum_filter_add_sum_filter_not (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2))
    (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))]
  have h_mid_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
        (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤ M_mid := by
    rw [hM_mid_def]
    rw [show
        (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
            (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
        ∑ ρ ∈ ((u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))).image Subtype.val,
            (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2 from ?_]
    swap
    · rw [Finset.sum_image]; intro x _ y _ h; exact Subtype.val_injective h
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
  -- hi part (tail) — shell indexing.
  have h_hi_bound :
      (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
            (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
        (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ≤
      C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k := by
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
    -- Per-element: xiOrderNat(ρ) / ‖ρ‖² ≤ xiOrderNat(ρ) / (2^k)².
    have h_per_elem :
        ∀ ρ ∈ S,
          (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤
          (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
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
      apply div_le_div_of_nonneg_left (by positivity) h_pow2k_pos h_pow2_le
    -- Shell bound: Σ_{ρ in shell k} xiOrderNat(ρ) ≤ weighted count(2^{k+1}) ≤ C₃·2^{k+1}·(k+1)·log 2.
    -- Per shell sum: Σ_{kf ρ = k} xiOrderNat(ρ) · 1/(2^(2k)) ≤ weighted count · 1/4^k
    --                ≤ C₃·2^{k+1}·(k+1)·log 2 / 4^k = C_tail · (k+1)/2^k (where log 2 absorbed).
    calc (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
        ≤ ∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
          apply Finset.sum_le_sum h_per_elem
      _ = ∑ k ∈ Finset.range K_max,
            ∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
              (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (t := Finset.range K_max) (g := kf)
            (f := fun ρ => (ZD.xiOrderNat ρ.val : ℝ) / (2 : ℝ) ^ (2 * kf ρ))]
          intro ρ hρ
          exact Finset.mem_range.mpr (h_kf_le ρ hρ)
      _ = ∑ k ∈ Finset.range K_max,
            (∑ ρ ∈ S.filter (fun ρ => kf ρ = k),
                (ZD.xiOrderNat ρ.val : ℝ)) / (2 : ℝ) ^ (2 * k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          rw [hρ.2]
      _ ≤ ∑ k ∈ Finset.range K_max,
            (if N + 1 ≤ k then C_tail * (k + 1 : ℝ) / 2 ^ k else 0) := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk_ge : N + 1 ≤ k
          · rw [if_pos hk_ge]
            -- Shell weighted count ≤ weighted count in disk(2^{k+1}) ≤ C₃·2^{k+1}·log(2^{k+1}) = C₃·2^{k+1}·(k+1)·log 2.
            have h_shell_bound :
                (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ)) ≤
                C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
              have hR_ge : R₀_step3 ≤ (2 : ℝ) ^ (k + 1) := by
                calc R₀_step3 ≤ R_th := hRth_ge_R₀
                  _ ≤ (2 : ℝ) ^ N := hN
                  _ ≤ (2 : ℝ) ^ (k + 1) :=
                      pow_le_pow_right₀ (by norm_num) (by omega)
              apply hBound_step3 ((2 : ℝ) ^ (k + 1)) hR_ge
              intro ρ hρ
              simp only [Finset.mem_filter] at hρ
              have ⟨_, h_lt⟩ := h_kf_prop ρ hρ.1
              rw [hρ.2] at h_lt
              linarith
            have h_log_pow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
              rw [Real.log_pow]; push_cast; ring
            have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := pow_pos (by norm_num) _
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hlog2_le_one : Real.log 2 ≤ 1 :=
              (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
            calc (∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (ZD.xiOrderNat ρ.val : ℝ))
                    / (2 : ℝ) ^ (2 * k)
                ≤ (C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)))
                    / (2 : ℝ) ^ (2 * k) :=
                  div_le_div_of_nonneg_right h_shell_bound h_pow2k_pos.le
              _ ≤ C_tail * (k + 1 : ℝ) / 2 ^ k := by
                rw [h_log_pow, hC_tail_def]
                have h2pk1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
                  rw [pow_succ]; ring
                have h22k : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
                  rw [show (2 * k) = k * 2 from by ring, pow_mul]
                have hpk_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
                rw [h2pk1, h22k]
                rw [show (2 * C₃) * (k + 1 : ℝ) / 2 ^ k = 2 * C₃ * (k + 1) / 2 ^ k from rfl]
                have h_numer : C₃ * (2 * (2:ℝ) ^ k) * ((↑k + 1) * Real.log 2) =
                    2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 := by ring
                rw [h_numer]
                have h_num_le : 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 ≤
                    2 * C₃ * ((2:ℝ)^k) * (↑k + 1) := by
                  have h_nn : 0 ≤ 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) := by positivity
                  nlinarith [hlog2_le_one, hlog2_pos]
                calc 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) * Real.log 2 / ((2:ℝ)^k)^2
                    ≤ 2 * C₃ * ((2:ℝ)^k) * (↑k + 1) / ((2:ℝ)^k)^2 :=
                      div_le_div_of_nonneg_right h_num_le (by positivity)
                  _ = 2 * C₃ * (↑k + 1) / (2:ℝ)^k := by
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

#print axioms summable_xiOrderNat_div_norm_sq_nontrivialZeros

end ZD
