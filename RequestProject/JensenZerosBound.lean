import Mathlib

open Real Complex MeasureTheory Filter Topology Set
open scoped Real Pointwise

noncomputable section

namespace ZD
namespace JensenZerosBound

/-- Jensen zero-count bound for an analytic function on a disk, normalized by `f 0 = 1`. -/
theorem zeros_bound
    {f : ℂ → ℂ} {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hB : 1 ≤ B)
    (hAnal : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ((Metric.closedBall (0 : ℂ) r ∩ {z | f z = 0}).ncard : ℝ) ≤
      Real.log B / Real.log (R / r) := by
  have hRpos : 0 < R := lt_trans hr hrR
  have hR_ne : R ≠ 0 := hRpos.ne'
  let CB : Set ℂ := Metric.closedBall (0 : ℂ) |R|
  have hAnalCB : AnalyticOnNhd ℂ f CB := by
    simpa [CB, abs_of_pos hRpos] using hAnal
  have hCB0 : (0 : ℂ) ∈ CB := by
    simp [CB, Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos, hRpos.le]
  have hMero : MeromorphicOn f CB := hAnalCB.meromorphicOn
  have hJensen :
      circleAverage (fun z => Real.log ‖f z‖) 0 R =
        ∑ᶠ u, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹)
          + (MeromorphicOn.divisor f CB 0 : ℝ) * Real.log R
          + Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    simpa [CB] using MeromorphicOn.circleAverage_log_norm hR_ne hMero
  have hAnal0 : AnalyticAt ℂ f 0 := hAnalCB 0 hCB0
  have hf0_ne : f 0 ≠ 0 := by simpa [hf0]
  have hDiv0 : MeromorphicOn.divisor f CB 0 = 0 := by
    rw [MeromorphicOn.divisor_apply hMero hCB0]
    have hOrd0 : analyticOrderAt f 0 = 0 := by
      rw [hAnal0.analyticOrderAt_eq_zero]
      exact hf0_ne
    rw [hAnal0.meromorphicOrderAt_eq, hOrd0]
    rfl
  have hTrail : meromorphicTrailingCoeffAt f 0 = f 0 :=
    hAnal0.meromorphicTrailingCoeffAt_of_ne_zero hf0_ne
  have hAnalSph : AnalyticOnNhd ℂ f (Metric.sphere (0 : ℂ) R) :=
    hAnal.mono (Metric.sphere_subset_closedBall)
  have hCI : CircleIntegrable (fun z => Real.log ‖f z‖) 0 R :=
    circleIntegrable_log_norm_meromorphicOn_of_nonneg hAnalSph.meromorphicOn hRpos.le
  have hCircAvg_le : circleAverage (fun z => Real.log ‖f z‖) 0 R ≤ Real.log B := by
    apply circleAverage_mono_on_of_le_circle hCI
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos hRpos] at hz
    have hfz : ‖f z‖ ≤ B := hbound z (by
      simpa [CB, Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos] using hz.le)
    rcases eq_or_lt_of_le (norm_nonneg (f z)) with h0 | h0
    · have h0' : ‖f z‖ = 0 := by simpa using h0.symm
      rw [h0', Real.log_zero]
      exact Real.log_nonneg hB
    · exact Real.log_le_log h0 hfz
  have hAnalOrd_ne_top : ∀ z ∈ CB, analyticOrderAt f z ≠ ⊤ := by
    intro z hz
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hfre : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
      have : ∀ᶠ w in 𝓝[≠] z, f w = 0 := htop.filter_mono nhdsWithin_le_nhds
      exact this.frequently
    have hEq :=
      hAnalCB.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_closedBall (0 : ℂ) |R|).isPreconnected hz hfre
    have h0 := hEq hCB0
    simpa [hf0] using h0
  have hD_nn : ∀ u, 0 ≤ MeromorphicOn.divisor f CB u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnalCB u
  have h_term_nn :
      ∀ u, 0 ≤ (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ CB
    · have hu' : ‖u‖ ≤ R := by
        simpa [CB, Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos] using hu
      by_cases hu0 : u = 0
      · simp [hu0, hDiv0, Real.log_zero]
      · have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hlog_nn : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show R * ‖u‖⁻¹ = R / ‖u‖ by ring, le_div_iff₀ hnorm_pos]
          linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := (MeromorphicOn.divisor f CB).apply_eq_zero_of_notMem hu
      simp [hD0]
  have hS_fin : (Metric.closedBall (0 : ℂ) r ∩ {z | f z = 0}).Finite := by
    have hDiv_fin :=
      (MeromorphicOn.divisor f CB).finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
    apply hDiv_fin.subset
    intro z hz
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz.1
    have hz_zero : f z = 0 := hz.2
    have hz_mem_CB : z ∈ CB := by
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos]
      rw [Metric.mem_closedBall, dist_zero_right] at hz_ball
      linarith
    have hAnalz : AnalyticAt ℂ f z := hAnalCB z hz_mem_CB
    have hOrd_ne_zero : analyticOrderAt f z ≠ 0 := by
      intro hzero
      rw [hAnalz.analyticOrderAt_eq_zero] at hzero
      exact hzero hz_zero
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt f z :=
      ENat.ne_top_iff_exists.mp (hAnalOrd_ne_top z hz_mem_CB)
    have hn_ne : n ≠ 0 := by
      intro h
      apply hOrd_ne_zero
      rw [← hn, h]
      rfl
    simp only [Function.mem_support]
    rw [MeromorphicOn.divisor_apply hMero hz_mem_CB, hAnalz.meromorphicOrderAt_eq, ← hn]
    simp [hn_ne]
  set S : Set ℂ := Metric.closedBall (0 : ℂ) r ∩ {z | f z = 0}
  have hS_sub_CB : S ⊆ CB := by
    intro u hu
    rcases hu with ⟨hu_ball, _⟩
    rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos]
    rw [Metric.mem_closedBall, dist_zero_right] at hu_ball
    linarith
  have hlog_ratio_pos : 0 < Real.log (R / r) := by
    apply Real.log_pos
    rw [one_lt_div hr]
    exact hrR
  have hS_each :
      ∀ ρ ∈ S,
        Real.log (R / r) ≤
          (MeromorphicOn.divisor f CB ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) := by
    intro ρ hρ_mem
    have hρ_mem' := hρ_mem
    rcases hρ_mem with ⟨hρ_ball, hρ_zero⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    have hρ_ne_zero : ρ ≠ 0 := fun h0 => by simpa [h0, hf0] using hρ_zero
    have hρ_mem_CB : ρ ∈ CB := hS_sub_CB hρ_mem'
    have hAnalρ : AnalyticAt ℂ f ρ := hAnalCB ρ hρ_mem_CB
    have hOrd_ne_zero : analyticOrderAt f ρ ≠ 0 := by
      intro hzero
      rw [hAnalρ.analyticOrderAt_eq_zero] at hzero
      exact hzero hρ_zero
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt f ρ :=
      ENat.ne_top_iff_exists.mp (hAnalOrd_ne_top ρ hρ_mem_CB)
    have hn_ne : n ≠ 0 := fun h => hOrd_ne_zero (by rw [← hn, h]; rfl)
    have hD_ge_one :
        (1 : ℤ) ≤ MeromorphicOn.divisor f CB ρ := by
      have hn_ge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne
      rw [MeromorphicOn.divisor_apply hMero hρ_mem_CB, hAnalρ.meromorphicOrderAt_eq, ← hn]
      simp only [ENat.map_coe, WithTop.coe_natCast, WithTop.untop₀_natCast, Nat.one_le_cast,
        ge_iff_le]
      exact hn_ge
    have hnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne_zero
    have hratio_ge : R / r ≤ R / ‖ρ‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hr hnorm_pos).2 hρ_ball) hRpos.le
    have hlog_ge : Real.log (R / r) ≤ Real.log (R * ‖ρ‖⁻¹) := by
      simpa [div_eq_mul_inv] using Real.log_le_log (by positivity : 0 < R / r) hratio_ge
    have hlog_ratio_nn : 0 ≤ Real.log (R / r) := hlog_ratio_pos.le
    have hD_ge_one_R : (1 : ℝ) ≤ (MeromorphicOn.divisor f CB ρ : ℝ) := by
      exact_mod_cast hD_ge_one
    calc Real.log (R / r)
        = 1 * Real.log (R / r) := by ring
      _ ≤ (MeromorphicOn.divisor f CB ρ : ℝ) * Real.log (R / r) :=
          mul_le_mul_of_nonneg_right hD_ge_one_R hlog_ratio_nn
      _ ≤ (MeromorphicOn.divisor f CB ρ : ℝ) * Real.log (R * ‖ρ‖⁻¹) := by
          apply mul_le_mul_of_nonneg_left hlog_ge
          linarith
  have h_D_fs : (MeromorphicOn.divisor f CB).support.Finite :=
    (MeromorphicOn.divisor f CB).finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hS_sub_Dsupp : S ⊆ (MeromorphicOn.divisor f CB).support := by
    intro ρ hρ_mem
    have hρ_mem' := hρ_mem
    rcases hρ_mem with ⟨hρ_ball, hρ_zero⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    have hρ_mem_CB : ρ ∈ CB := hS_sub_CB hρ_mem'
    have hAnalρ : AnalyticAt ℂ f ρ := hAnalCB ρ hρ_mem_CB
    have hOrd_ne_zero : analyticOrderAt f ρ ≠ 0 := by
      intro hzero
      rw [hAnalρ.analyticOrderAt_eq_zero] at hzero
      exact hzero hρ_zero
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt f ρ :=
      ENat.ne_top_iff_exists.mp (hAnalOrd_ne_top ρ hρ_mem_CB)
    have hn_ne : n ≠ 0 := fun h => hOrd_ne_zero (by rw [← hn, h]; rfl)
    have hD_ge_one :
        (1 : ℤ) ≤ MeromorphicOn.divisor f CB ρ := by
      have hn_ge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne
      rw [MeromorphicOn.divisor_apply hMero hρ_mem_CB, hAnalρ.meromorphicOrderAt_eq, ← hn]
      simp only [ENat.map_coe, WithTop.coe_natCast, WithTop.untop₀_natCast, Nat.one_le_cast,
        ge_iff_le]
      exact hn_ge
    simp only [Function.mem_support]
    intro hD0
    rw [hD0] at hD_ge_one
    exact absurd hD_ge_one (by norm_num)
  have h_finsum_eq :
      (∑ᶠ u, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹)) =
        ∑ u ∈ h_D_fs.toFinset, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro hD0
    apply hu
    rw [hD0]
    simp
  have h_sub_fs : hS_fin.toFinset ⊆ h_D_fs.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hS_sub_Dsupp hu
  have h_lower :
      (S.ncard : ℝ) * Real.log (R / r) ≤
        ∑ᶠ u, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
    rw [Set.ncard_eq_toFinset_card S hS_fin, h_finsum_eq]
    calc (hS_fin.toFinset.card : ℝ) * Real.log (R / r)
        = ∑ u ∈ hS_fin.toFinset, Real.log (R / r) := by rw [Finset.sum_const]; ring
      _ ≤ ∑ u ∈ hS_fin.toFinset,
            (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [Set.Finite.mem_toFinset] at hu
          exact hS_each u hu
      _ ≤ ∑ u ∈ h_D_fs.toFinset,
            (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_sub_fs
          intro u _ _
          exact h_term_nn u
  have h_upper :
      ∑ᶠ u, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) ≤ Real.log B := by
    have h_eq :
        circleAverage (fun z => Real.log ‖f z‖) 0 R =
          ∑ᶠ u, (MeromorphicOn.divisor f CB u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      rw [hJensen, hDiv0, hTrail, hf0]
      simp
    rw [← h_eq]
    exact hCircAvg_le
  have h_final : (S.ncard : ℝ) ≤ Real.log B / Real.log (R / r) := by
    rw [le_div_iff₀ hlog_ratio_pos]
    exact le_trans h_lower h_upper
  simpa [S] using h_final

/-- Centered form of `zeros_bound`, normalized by the center value `f c`. -/
theorem zeros_bound_centered
    {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hB : 1 ≤ B)
    (hAnal : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfc : f c ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B * ‖f c‖) :
    ((Metric.closedBall c r ∩ {z | f z = 0}).ncard : ℝ) ≤
      Real.log B / Real.log (R / r) := by
  let g : ℂ → ℂ := fun z => f (z + c) / f c
  have hRpos : 0 < R := lt_trans hr hrR
  have hsub_shift :
      Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall c R + ({(-c : ℂ)} : Set ℂ) := by
    intro z hz
    rw [Set.mem_add]
    refine ⟨z + c, ?_, -c, by simp, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using hz
    · ring
  have hAnalShift :
      AnalyticOnNhd ℂ (fun z => f (z + c)) (Metric.closedBall (0 : ℂ) R) := by
    simpa [g, sub_eq_add_neg] using (hAnal.comp_sub (-c)).mono hsub_shift
  have hAnalG : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) R) := by
    simpa [g] using (hAnalShift.div_const (c := f c))
  have hg0 : g 0 = 1 := by
    simp [g, hfc]
  have hfc_norm_pos : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hboundG : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B := by
    intro z hz
    have hz' : z + c ∈ Metric.closedBall c R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using hz
    rw [show g z = f (z + c) / f c by rfl, norm_div]
    rw [div_le_iff₀ hfc_norm_pos]
    simpa [mul_assoc] using hbound (z + c) hz'
  have h_main := zeros_bound hr hrR hB hAnalG hg0 hboundG
  set S : Set ℂ := Metric.closedBall c r ∩ {z | f z = 0}
  have h_image :
      (fun z : ℂ => z - c) '' S = Metric.closedBall (0 : ℂ) r ∩ {z | g z = 0} := by
    ext z
    constructor
    · rintro ⟨w, hwS, rfl⟩
      rcases hwS with ⟨hw_ball, hw_zero⟩
      constructor
      · simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hw_ball
      · have hw_zero' : f w = 0 := by simpa using hw_zero
        simp [g, hw_zero', hfc]
    · intro hz
      rcases hz with ⟨hz_ball, hz_zero⟩
      refine ⟨z + c, ?_, by ring⟩
      constructor
      · simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hz_ball
      · simpa [g, hfc] using hz_zero
  have h_ncard :
      S.ncard = (Metric.closedBall (0 : ℂ) r ∩ {z | g z = 0}).ncard := by
    rw [← h_image]
    simpa using (Set.ncard_image_of_injective S (sub_left_injective : Function.Injective
      (fun z : ℂ => z - c))).symm
  have h_main' : (S.ncard : ℝ) ≤ Real.log B / Real.log (R / r) := by
    simpa [S, h_ncard] using h_main
  simpa [S] using h_main'

/-- Centered Jensen bound from a lower bound at the center and a uniform outer bound. -/
theorem zeros_bound_centered_of_center_norm_le
    {f : ℂ → ℂ} {c : ℂ} {r R m M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m)
    (hAnal : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hcenter : m ≤ ‖f c‖)
    (hbound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ M) :
    ((Metric.closedBall c r ∩ {z | f z = 0}).ncard : ℝ) ≤
      Real.log (M / m) / Real.log (R / r) := by
  have hfc : f c ≠ 0 := by
    intro hfc0
    rw [hfc0, norm_zero] at hcenter
    linarith
  have hRpos : 0 < R := lt_trans hr hrR
  have hc_mem : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hRpos.le
  have hm_le_M : m ≤ M := le_trans hcenter (hbound c hc_mem)
  have hM_nonneg : 0 ≤ M := le_trans hm.le hm_le_M
  have hB : 1 ≤ M / m := by
    rw [one_le_div hm]
    exact hm_le_M
  have hscaled : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ (M / m) * ‖f c‖ := by
    intro z hz
    have hscale : M ≤ (M / m) * ‖f c‖ := by
      calc M = M * 1 := by ring
        _ ≤ M * (‖f c‖ / m) := by
            apply mul_le_mul_of_nonneg_left ?_ hM_nonneg
            rw [one_le_div hm]
            exact hcenter
        _ = (M / m) * ‖f c‖ := by ring
    exact (hbound z hz).trans hscale
  simpa using zeros_bound_centered hr hrR hB hAnal hfc hscaled

end JensenZerosBound
end ZD
