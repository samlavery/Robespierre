import Mathlib
-- import RequestProject.XiPartialFraction
import RequestProject.XiShortWindowCount
import RequestProject.LogDerivIdentity
import RequestProject.WeilPigeonhole
import RequestProject.DigammaVerticalBound
import RequestProject.FarZeroShellBound
import RequestProject.UniformGammaRBound

/-!
# H11: Critical-strip Landau `‖ζ'/ζ(σ + iT*)‖ = O((log T)²)`

Final unconditional Landau bound on the critical strip at good heights.
-/

open Complex

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Helpers
-- ═══════════════════════════════════════════════════════════════════════════

/-- Variant of `exists_point_far_from_finset` without the `hS` hypothesis
(since `hS` is unused in the original proof). -/
private theorem exists_point_far_from_finset' {a b : ℝ} (hab : a < b) (S : Finset ℝ) :
    ∃ x ∈ Set.Icc a b, ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |x - s| := by
  by_contra! h_contra
  have h_union : Set.Icc a b ⊆ ⋃ s ∈ S, Set.Ioo
      (s - (b - a) / (2 * (S.card + 1))) (s + (b - a) / (2 * (S.card + 1))) := by
    exact fun x hx => by
      rcases h_contra x hx with ⟨s, hs, hs'⟩
      exact Set.mem_iUnion₂.mpr
        ⟨s, hs, ⟨by linarith [abs_lt.mp hs'], by linarith [abs_lt.mp hs']⟩⟩
  have h_measure : MeasureTheory.volume
      (⋃ s ∈ S, Set.Ioo (s - (b - a) / (2 * (S.card + 1)))
        (s + (b - a) / (2 * (S.card + 1)))) ≤
      ∑ s ∈ S, MeasureTheory.volume
        (Set.Ioo (s - (b - a) / (2 * (S.card + 1)))
          (s + (b - a) / (2 * (S.card + 1)))) := by
    convert MeasureTheory.measure_biUnion_finset_le _ _
    infer_instance
  have := h_measure.trans' (MeasureTheory.measure_mono h_union)
  norm_num at this
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at this
  ring_nf at this
  rw [ENNReal.ofReal_le_ofReal_iff] at this <;>
    nlinarith [mul_inv_cancel_left₀ (by linarith : (2 + S.card * 2 : ℝ) ≠ 0) (b - a)]

/-- **Summability of the weighted partial-fraction tsum** at `s ∉ NontrivialZeros`
(local copy of the private lemma from XiShortWindowCount). Derived from
`summable_logDeriv_multi` via `Summable.sigma` and the per-factor reduction. -/
lemma summable_weighted_partial_fraction_local {s : ℂ} (hs : s ∉ NontrivialZeros) :
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

/-- Local short-window decomposition of `ξ'/ξ` into nearby zero terms + tail,
with H8's Hadamard constant `A` exposed. Derived by splitting H8's tsum against
the `|ρ.im - s.im| ≤ 1` predicate via `Summable.tsum_add_tsum_compl` plus the
subtype-subtype equivalence. -/
theorem xi_logDeriv_short_window_decomp :
    ∃ A : ℂ, ∀ s : ℂ, s ∉ NontrivialZeros →
      deriv riemannXi s / riemannXi s =
        A +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  refine ⟨A, fun s hs => ?_⟩
  have hA_s := hA s hs
  let F : ℂ → ℂ := fun ρ => (ZD.xiOrderNat ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  have h_summ_NTZ : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => F ρ.val) :=
    summable_weighted_partial_fraction_local hs
  -- Direct approach via Equiv: construct the equiv between {ρ // ρ ∈ NTZ ∧ P} and
  -- the outer subtype on {ρ // ρ ∈ NTZ}.
  -- f_eP : (inner type) -> (target type), i.e., {x : {y // y ∈ NTZ} // |x.val.im-s.im|≤1}
  -- --> {ρ : ℂ // ρ ∈ NTZ ∧ |ρ.im-s.im|≤1}
  let eP : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // |x.val.im - s.im| ≤ 1} ≃
      {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1} := {
    toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let ePc : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // ¬ |x.val.im - s.im| ≤ 1} ≃
      {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬ |ρ.im - s.im| ≤ 1} := {
    toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  -- Split the NTZ tsum.
  set g : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℂ := fun ρ => F ρ.val with hg_def
  set S : Set {ρ : ℂ // ρ ∈ NontrivialZeros} := {ρ | |ρ.val.im - s.im| ≤ 1} with hS_def
  have h_sub_S : Summable (fun ρ : S => g ρ.val) := h_summ_NTZ.subtype S
  have h_sub_Sc : Summable (fun ρ : ↥Sᶜ => g ρ.val) := h_summ_NTZ.subtype Sᶜ
  have h_split :
      (∑' ρ : S, g ρ.val) + (∑' ρ : ↥Sᶜ, g ρ.val) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, g ρ :=
    Summable.tsum_add_tsum_compl (f := g) h_sub_S h_sub_Sc
  -- Reindex S-tsum and Sᶜ-tsum.
  have hP_reindex :
      (∑' ρ : S, g ρ.val) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1}, F ρ.val := by
    have h_S_is_subtype :
        (∑' ρ : S, g ρ.val) =
        ∑' x : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // |x.val.im - s.im| ≤ 1}, g x.val := rfl
    rw [h_S_is_subtype]
    -- Apply eP.symm to switch index types.
    have := eP.symm.tsum_eq
      (fun x : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // |x.val.im - s.im| ≤ 1} => g x.val)
    rw [← this]
    apply tsum_congr
    intro c
    -- Reduce g (eP.symm c).val to F c.val.
    show F ((eP.symm c).val.val) = F c.val
    rfl
  have hPc_reindex :
      (∑' ρ : ↥Sᶜ, g ρ.val) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬ |ρ.im - s.im| ≤ 1}, F ρ.val := by
    have h_Sc_is_subtype :
        (∑' ρ : ↥Sᶜ, g ρ.val) =
        ∑' x : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // ¬ |x.val.im - s.im| ≤ 1}, g x.val := rfl
    rw [h_Sc_is_subtype]
    have := ePc.symm.tsum_eq
      (fun x : {x : {ρ : ℂ // ρ ∈ NontrivialZeros} // ¬ |x.val.im - s.im| ≤ 1} => g x.val)
    rw [← this]
    apply tsum_congr
    intro c
    show F ((ePc.symm c).val.val) = F c.val
    rfl
  rw [hA_s, ← h_split, hP_reindex, hPc_reindex, add_assoc]

/-- **σ=2 subtraction identity** at a fixed imaginary height `T`:
`1/(s-ρ) - 1/(s₀-ρ) = (2-σ)/((s-ρ)(s₀-ρ))` where `s = σ+iT`, `s₀ = 2+iT`.
The `1/ρ` terms cancel, giving absolutely convergent far sums. -/
private lemma one_div_sub_one_div_formula
    (σ : ℝ) (T : ℝ) (ρ : ℂ) (hρ_s : (σ : ℂ) + (T : ℂ) * I - ρ ≠ 0)
    (hρ_s₀ : (2 : ℂ) + (T : ℂ) * I - ρ ≠ 0) :
    (1 : ℂ) / ((σ : ℂ) + (T : ℂ) * I - ρ) - 1 / ((2 : ℂ) + (T : ℂ) * I - ρ) =
    ((2 - σ : ℝ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I - ρ) * ((2 : ℂ) + (T : ℂ) * I - ρ)) := by
  field_simp
  push_cast
  ring

/-- The H10 short-window finset at height `T`. -/
def shortWindowFinset (T : ℝ) : Finset ℂ :=
  ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T + 1)).toFinset.filter
    (fun ρ => |ρ.im - T| ≤ 1))

/-- A zero lies in the H10 short-window finset if it is in the corresponding
window and its imaginary part has absolute value at most the center height. -/
private lemma mem_shortWindowFinset_of_near_and_abs_im_le
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hρ_near : |ρ.im - T| ≤ 1) (hρ_im_abs : |ρ.im| ≤ T) :
    ρ ∈ shortWindowFinset T := by
  rw [shortWindowFinset, Finset.mem_filter, Set.Finite.mem_toFinset]
  refine ⟨⟨hρ, ?_⟩, hρ_near⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by
    have hβ_lt : ρ.re < 1 := hρ.2.1
    have hβ_pos : 0 < ρ.re := hρ.1
    nlinarith
  have hγ_sq_le : ρ.im ^ 2 ≤ T ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have := mul_self_le_mul_self h_abs_nn hρ_im_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im ^ 2 by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  have h_norm_sq_lt : ‖ρ‖ ^ 2 < (T + 1) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    nlinarith
  have hTp1_pos : 0 < T + 1 := by linarith
  nlinarith [norm_nonneg ρ]

/-- Pointwise far-zero bound by the inverse square ordinate gap. -/
private lemma far_sub_term_norm_le_gap_sq
    (σ T : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hfar : ¬ |ρ.im - T| ≤ 1) :
    ‖(ZD.xiOrderNat ρ : ℂ) *
        (1 / ((σ : ℂ) + (T : ℂ) * I - ρ) -
         1 / ((2 : ℂ) + (T : ℂ) * I - ρ))‖
      ≤ 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hgap_gt_one : 1 < |ρ.im - T| := by
    by_contra h
    exact hfar (not_lt.mp h)
  have hgap_pos : 0 < |ρ.im - T| := lt_trans zero_lt_one hgap_gt_one
  have hs_ne : s - ρ ≠ 0 := by
    intro hs_eq
    have him : T - ρ.im = 0 := by
      simpa [s] using congrArg Complex.im hs_eq
    have hsub : ρ.im - T = 0 := by linarith
    have : |ρ.im - T| = 0 := by simp [hsub]
    linarith
  have hs₀_ne : s₀ - ρ ≠ 0 := by
    intro hs_eq
    have hre := congrArg Complex.re hs_eq
    simp [s₀] at hre
    linarith [hρ.2.1]
  have hsgap : |ρ.im - T| ≤ ‖s - ρ‖ := by
    calc
      |ρ.im - T| = |(s - ρ).im| := by simp [s, abs_sub_comm]
      _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
  have hs₀gap : |ρ.im - T| ≤ ‖s₀ - ρ‖ := by
    calc
      |ρ.im - T| = |(s₀ - ρ).im| := by simp [s₀, abs_sub_comm]
      _ ≤ ‖s₀ - ρ‖ := Complex.abs_im_le_norm _
  have hnum_le : ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2 := by
    have hσ_nonneg : 0 ≤ σ := le_of_lt hσ.1
    have hσ_le : σ ≤ 1 := le_of_lt hσ.2
    have hreal : |2 - σ| ≤ 2 := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    change ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2
    rw [Complex.norm_real]
    exact hreal
  have hden_ge : |ρ.im - T| ^ 2 ≤ ‖s - ρ‖ * ‖s₀ - ρ‖ := by
    nlinarith
  have hdiv :
      ‖((2 - σ : ℝ) : ℂ)‖ / (‖s - ρ‖ * ‖s₀ - ρ‖) ≤ 2 / |ρ.im - T| ^ 2 := by
    have hden_pos : 0 < ‖s - ρ‖ * ‖s₀ - ρ‖ := by positivity
    have hgap_sq_pos : 0 < |ρ.im - T| ^ 2 := by positivity
    rw [div_le_div_iff₀ hden_pos hgap_sq_pos]
    nlinarith
  rw [one_div_sub_one_div_formula σ T ρ hs_ne hs₀_ne, norm_mul, Complex.norm_natCast, norm_div,
    norm_mul]
  have hxi_nonneg : 0 ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hdiv hxi_nonneg
  simpa [s, s₀, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

/-- Large-norm far-zero bound by `‖ρ‖⁻²`. -/
private lemma far_sub_term_norm_le_norm_sq
    (σ T : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hT_nonneg : 0 ≤ T)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hρ_norm : 2 * T + 5 ≤ ‖ρ‖) :
    ‖(ZD.xiOrderNat ρ : ℂ) *
        (1 / ((σ : ℂ) + (T : ℂ) * I - ρ) -
         1 / ((2 : ℂ) + (T : ℂ) * I - ρ))‖
      ≤ 8 * (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hs_norm_le : ‖s‖ ≤ T + 1 := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = σ + T := by
        have hσ_nonneg : 0 ≤ σ := le_of_lt hσ.1
        simp [s, abs_of_nonneg hσ_nonneg, abs_of_nonneg hT_nonneg]
      _ ≤ T + 1 := by linarith [hσ.2]
  have hs₀_norm_le : ‖s₀‖ ≤ T + 2 := by
    calc
      ‖s₀‖ ≤ |s₀.re| + |s₀.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 2 + T := by
        simp [s₀, abs_of_nonneg hT_nonneg]
      _ = T + 2 := by ring
  have hhalf_s : ‖s‖ ≤ ‖ρ‖ / 2 := by
    have : T + 1 ≤ ‖ρ‖ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact hs_norm_le.trans this
  have hhalf_s₀ : ‖s₀‖ ≤ ‖ρ‖ / 2 := by
    have : T + 2 ≤ ‖ρ‖ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact hs₀_norm_le.trans this
  have hs_ne : s - ρ ≠ 0 := by
    have hρ_pos : 0 < ‖ρ‖ := by
      have : 0 < 2 * T + 5 := by linarith
      exact lt_of_lt_of_le this hρ_norm
    have hpos : 0 < ‖ρ‖ / 2 := by positivity
    intro hs_eq
    have hzero : ‖s - ρ‖ = 0 := by simpa [hs_eq]
    have hlower : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
      calc
        ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s‖ := by linarith
        _ ≤ ‖ρ - s‖ := norm_sub_norm_le ρ s
        _ = ‖s - ρ‖ := by rw [norm_sub_rev]
    linarith
  have hs₀_ne : s₀ - ρ ≠ 0 := by
    have hρ_pos : 0 < ‖ρ‖ := by
      have : 0 < 2 * T + 5 := by linarith
      exact lt_of_lt_of_le this hρ_norm
    have hpos : 0 < ‖ρ‖ / 2 := by positivity
    intro hs_eq
    have hzero : ‖s₀ - ρ‖ = 0 := by simpa [hs_eq]
    have hlower : ‖ρ‖ / 2 ≤ ‖s₀ - ρ‖ := by
      calc
        ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s₀‖ := by linarith
        _ ≤ ‖ρ - s₀‖ := norm_sub_norm_le ρ s₀
        _ = ‖s₀ - ρ‖ := by rw [norm_sub_rev]
    linarith
  have hsgap : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    calc
      ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s‖ := by linarith
      _ ≤ ‖ρ - s‖ := norm_sub_norm_le ρ s
      _ = ‖s - ρ‖ := by rw [norm_sub_rev]
  have hs₀gap : ‖ρ‖ / 2 ≤ ‖s₀ - ρ‖ := by
    calc
      ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s₀‖ := by linarith
      _ ≤ ‖ρ - s₀‖ := norm_sub_norm_le ρ s₀
      _ = ‖s₀ - ρ‖ := by rw [norm_sub_rev]
  have hnum_le : ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2 := by
    have hσ_nonneg : 0 ≤ σ := le_of_lt hσ.1
    have hσ_le : σ ≤ 1 := le_of_lt hσ.2
    have hreal : |2 - σ| ≤ 2 := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    change ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2
    rw [Complex.norm_real]
    exact hreal
  have hden_ge : ‖ρ‖ ^ 2 / 4 ≤ ‖s - ρ‖ * ‖s₀ - ρ‖ := by
    nlinarith
  have hdiv :
      ‖((2 - σ : ℝ) : ℂ)‖ / (‖s - ρ‖ * ‖s₀ - ρ‖) ≤ 8 / ‖ρ‖ ^ 2 := by
    have hρ_pos : 0 < ‖ρ‖ := by
      have : 0 < 2 * T + 5 := by linarith
      exact lt_of_lt_of_le this hρ_norm
    have hhalf_pos : 0 < ‖ρ‖ / 2 := by positivity
    have hs_pos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hhalf_pos hsgap
    have hs₀_pos : 0 < ‖s₀ - ρ‖ := lt_of_lt_of_le hhalf_pos hs₀gap
    have hden_pos : 0 < ‖s - ρ‖ * ‖s₀ - ρ‖ := mul_pos hs_pos hs₀_pos
    have hnorm_sq_pos : 0 < ‖ρ‖ ^ 2 := by
      positivity
    rw [div_le_div_iff₀ hden_pos hnorm_sq_pos]
    nlinarith
  rw [one_div_sub_one_div_formula σ T ρ hs_ne hs₀_ne, norm_mul, Complex.norm_natCast, norm_div,
    norm_mul]
  have hxi_nonneg : 0 ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hdiv hxi_nonneg
  simpa [s, s₀, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

private lemma log_twoT_add_six_le_four_log {T : ℝ} (hT : 2 ≤ T) :
    Real.log (2 * T + 6) ≤ 4 * Real.log T := by
  have hT_pos : 0 < T := by linarith
  have harg_pos : 0 < 2 * T + 6 := by linarith
  have hT_sq : 4 ≤ T ^ 2 := by nlinarith
  have hpow : 2 * T + 6 ≤ T ^ 4 := by
    have h1 : (8 : ℝ) ≤ T ^ 3 := by nlinarith [sq_nonneg (T - 2), hT_sq]
    have h2 : (8 : ℝ) * T ≤ T ^ 4 := by nlinarith [h1, sq_nonneg T]
    nlinarith [h2]
  calc
    Real.log (2 * T + 6) ≤ Real.log (T ^ 4) := Real.log_le_log harg_pos hpow
    _ = 4 * Real.log T := by rw [Real.log_pow]; push_cast; ring

private lemma max_radius_log_le_const_mul
    {R₀ T : ℝ} (hR₀_pos : 0 < R₀) (hT : 2 ≤ T) :
    max R₀ (2 * T + 5) * Real.log (max R₀ (2 * T + 5))
      ≤ ((R₀ + 5) * (Real.log (R₀ + 5) / Real.log 2 + 1)) * T * Real.log T := by
  have hT_pos : 0 < T := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hA_pos : 0 < R₀ + 5 := by linarith
  have hR_pos : 0 < max R₀ (2 * T + 5) := by
    exact lt_of_lt_of_le hR₀_pos (le_max_left _ _)
  have hR_le : max R₀ (2 * T + 5) ≤ (R₀ + 5) * T := by
    refine max_le ?_ ?_
    · have h_one_le : (1 : ℝ) ≤ T := by linarith
      calc
        R₀ = R₀ * 1 := by ring
        _ ≤ R₀ * T := by gcongr
        _ ≤ (R₀ + 5) * T := by gcongr; linarith
    · calc
        2 * T + 5 ≤ 5 * T := by linarith
        _ ≤ (R₀ + 5) * T := by
          have : 5 ≤ R₀ + 5 := by linarith
          gcongr
  have hlog_factor :
      Real.log (max R₀ (2 * T + 5))
        ≤ (Real.log (R₀ + 5) / Real.log 2 + 1) * Real.log T := by
    have hlog_le :
        Real.log (max R₀ (2 * T + 5)) ≤ Real.log ((R₀ + 5) * T) :=
      Real.log_le_log hR_pos hR_le
    rw [Real.log_mul hA_pos.ne' hT_pos.ne'] at hlog_le
    have hratio : 1 ≤ Real.log T / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos, one_mul]
      exact Real.log_le_log (by norm_num) hT
    have hconst_nonneg : 0 ≤ Real.log (R₀ + 5) := Real.log_nonneg (by linarith)
    have hconst :
        Real.log (R₀ + 5) ≤ (Real.log (R₀ + 5) / Real.log 2) * Real.log T := by
      calc
        Real.log (R₀ + 5) = Real.log (R₀ + 5) * 1 := by ring
        _ ≤ Real.log (R₀ + 5) * (Real.log T / Real.log 2) := by
              gcongr
        _ = (Real.log (R₀ + 5) / Real.log 2) * Real.log T := by ring
    linarith
  have hcoeff_nonneg : 0 ≤ Real.log (R₀ + 5) / Real.log 2 + 1 := by
    have hlog_R₀_nn : 0 ≤ Real.log (R₀ + 5) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (R₀ + 5) / Real.log 2 := div_nonneg hlog_R₀_nn hlog2_pos.le
    linarith
  calc
    max R₀ (2 * T + 5) * Real.log (max R₀ (2 * T + 5))
      ≤ max R₀ (2 * T + 5) *
          ((Real.log (R₀ + 5) / Real.log 2 + 1) * Real.log T) := by
            gcongr
    _ ≤ ((R₀ + 5) * T) * ((Real.log (R₀ + 5) / Real.log 2 + 1) * Real.log T) := by
            gcongr
    _ = ((R₀ + 5) * (Real.log (R₀ + 5) / Real.log 2 + 1)) * T * Real.log T := by
            ring

/-- **Far-zero subtraction bound**: `‖Σ_{|γ-T|>1} xiOrderNat(ρ) ·
(1/(σ+iT - ρ) - 1/(2+iT - ρ))‖ = O(log T)`. Uses cancellation-of-`1/ρ`
subtraction form: `|1/(s-ρ) - 1/(s₀-ρ)| ≤ 2/|T-γ|²` for far zeros and
`≤ 8/‖ρ‖²` for `‖ρ‖ ≥ 2T+5`. Tail summability + dyadic shells + H10.

-/
theorem xi_logDeriv_sub_far_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (0:ℝ) 2, ∀ T : ℝ, 2 ≤ T →
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ C * Real.log T :=
  ZD.FarShell.xi_logDeriv_sub_far_bound_proved

/-- Good height existence: for every `T₀ ≥ 2` there is a height `T ∈ [T₀, T₀+1]`
such that every zero `ρ` with `|ρ.im - T₀| ≤ 1` has `|ρ.im - T| ≥ C / log T₀` for
a uniform constant `C`. Proved via the pigeonhole helper
`exists_point_far_from_finset'` applied to the H10 short-window finset. -/
theorem exists_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, 2 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ ∈ NontrivialZeros, |ρ.im - T₀| ≤ 1 →
        C / Real.log T₀ ≤ |ρ.im - T| := by
  obtain ⟨C₀, hC₀_pos, hC₀_bd⟩ := nontrivialZeros_short_window_distinct_count_bound
  refine ⟨1 / (20 * (C₀ + 1)), ?_, ?_⟩
  · positivity
  intro T₀ hT₀
  have hT₀_pos : (0 : ℝ) < T₀ := by linarith
  have hlog_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : Real.log 2 ≤ Real.log T₀ := Real.log_le_log (by norm_num) hT₀
  -- The finset of zeros with |γ - T₀| ≤ 1 (using radius T₀ + 2 to comfortably
  -- contain all such zeros, regardless of the H10 radius convention).
  set F : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T₀ + 2)).toFinset.filter
      (fun ρ => |ρ.im - T₀| ≤ 1)) with hF_def
  -- Card bound via H10's finset + subset.
  set F_H10 : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T₀ + 1)).toFinset.filter
      (fun ρ => |ρ.im - T₀| ≤ 1)) with hFH10_def
  have hF_card_H10 : (F_H10.card : ℝ) ≤ C₀ * Real.log T₀ := hC₀_bd T₀ hT₀
  -- We use F (radius T₀+2) for membership; card of F may be slightly larger but
  -- still bounded by log T₀ (up to constants) - but we need to prove it.
  -- Strategy: bound F.card ≤ F_H10.card + small, or just apply H10 with a shifted
  -- T and use the card of F directly via `nontrivialZeros_short_window_distinct_count_bound`.
  -- Actually: F is the filter of `|γ - T₀| ≤ 1`, which implies |γ| ≤ T₀ + 1, and
  -- we have |ρ|² < 1 + (T₀+1)² < (T₀+2)² (since T₀ ≥ 2 ⟹ 2T₀+3 > 0 obviously;
  -- (T₀+2)² = T₀² + 4T₀ + 4 > T₀² + 2T₀ + 2 = (T₀+1)² + 1).
  -- So F_H10 ⊆ F (in both directions actually? No — F uses larger ball so F_H10 ⊆ F).
  -- But we want F.card ≤ ... we need F's card bounded.
  -- Crucial observation: F = F_H10 as SETS, since all zeros with |γ-T₀|≤1 and 0<β<1
  -- lie in BOTH balls (of radius T₀+1 AND T₀+2). Wait, do they lie in ball of T₀+1?
  -- |ρ|² < 1 + (T₀+1)² — this is not ≤ (T₀+1)². So not necessarily.
  -- But they DO lie in ball of T₀+2 since |ρ|² < 1 + (T₀+1)² ≤ (T₀+2)² requires
  -- 1 + (T₀+1)² ≤ (T₀+2)² ⟺ 1 + T₀² + 2T₀ + 1 ≤ T₀² + 4T₀ + 4 ⟺ 2 ≤ 2T₀ + 3 ✓.
  -- So F contains all such zeros, and F_H10 ⊆ F. But we need F.card bounded.
  -- Use hC₀_bd directly — but hC₀_bd only bounds the T₀+1-radius finset, not F.
  -- Solution: apply hC₀_bd at T = T₀, but we need a bound on F's card, not F_H10's.
  -- Alt: enlarge statement — use the weighted count bound or derive via card monotonicity.
  -- Pragmatic fix: we just need |S| ≤ C₀ · log T₀ where S is image of F by im.
  -- The image collapses multiplicities: S.card ≤ #(distinct γ values) ≤ (# zeros).
  -- We shift H10 to apply at T₀ using the actual set we need. But H10 wraps with
  -- the radius T₀+1 ball. To sidestep, define S via an intermediate: just S = image
  -- of F_H10 (which is bounded by H10), and check that F_H10 contains all relevant
  -- zeros' γ values. But it might not.
  -- Alternative: since the pigeonhole needs a bound on S.card only, and we can
  -- use `F_H10.card ≤ C₀ * log T₀`, use S := F_H10.image im (not F.image im),
  -- and then show membership via: for any ρ NTZ with |γ-T₀|≤1, if ρ's γ is
  -- absent from F_H10's image, the pigeonhole bound trivially fails — but
  -- conceptually we need ρ.im ∈ S for the T* bound.
  -- The cleanest path: show F_H10 actually contains all such ρ.
  -- Claim: For ρ NTZ with |γ - T₀| ≤ 1 and T₀ ≥ 2, |ρ| ≤ T₀ + 1. PROOF:
  -- β² < 1, γ² ≤ (T₀+1)², so |ρ|² < 1 + (T₀+1)². We need |ρ| ≤ T₀ + 1,
  -- i.e., |ρ|² ≤ (T₀+1)². This requires 1 + (T₀+1)² ≤ (T₀+1)², i.e., 1 ≤ 0.
  -- FALSE. So the claim is false.
  -- However, if β ≤ 1 - 1/(2(T₀+1)) (approx), then β² ≤ 1 - 1/(T₀+1), and
  -- |ρ|² ≤ 1 - 1/(T₀+1) + (T₀+1)² ≤ (T₀+1)² iff 1 ≤ 1/(T₀+1)... still false.
  -- So there genuinely can be zeros with |γ-T₀|≤1 but not in ball T₀+1.
  -- FIX: use card bound differently. Apply H10 at T = T₀ with its own finset F_H10,
  -- which gives # in F_H10 ≤ C₀ log T₀. The set we pigeonhole against should be
  -- S := F_H10.image im. Then for any ρ NTZ with |γ-T₀|≤1, either ρ.im ∈ S (the
  -- good case) OR ρ.im ∉ S. In the latter, we need to still bound |ρ.im - T|.
  -- But the point is we're proving ∀ρ, and we can only handle ρ with ρ.im ∈ S.
  -- Workaround: choose S differently. Since our NonTrivialZeros_inter_closedBall_finite
  -- is monotone, we can use radius T₀+2 and apply H10 at a shifted T, OR use a
  -- suitable auxiliary.
  -- Simplest: change the radius in the finset argument. hC₀_bd doesn't care about
  -- the radius (it's a hypothesis), just the filter. Let's just use H10 but at
  -- radius T₀+2. Wait — H10 picks radius T+1 internally. The finset is predetermined.
  -- Final solution: we CAN pick S using F (radius T₀+2 ball), and prove S.card
  -- bound by going through the WEIGHTED H10 counting or by noting F.card bounded.
  -- Use the following argument:
  --   F ⊇ F_H10, so F.card ≥ F_H10.card. But we have upper bound on F_H10.card,
  --   not lower. So F.card might be much larger.
  -- Alternative: observe the difference F \ F_H10 consists of zeros with
  --   |ρ| > T₀ + 1 AND |γ - T₀| ≤ 1 AND β ∈ (0,1).
  --   So |γ|² > (T₀+1)² - 1, i.e., γ > √((T₀+1)² - 1) or γ < -√(...).
  --   But |γ - T₀| ≤ 1 means γ ∈ [T₀-1, T₀+1]. Combined: γ > √((T₀+1)²-1) ≈ T₀+0.99.
  --   So the offset zeros have γ ∈ (√((T₀+1)²-1), T₀+1]. This is a VERY thin
  --   strip — width at most 1. For those γ, β² > (T₀+1)² - γ². For γ close to T₀+1,
  --   β² could be small but must exceed the gap.
  -- Actually, simpler bound: F \ F_H10 ⊆ {ρ NTZ : |γ-T₀|≤1 ∧ β²+γ² > (T₀+1)²}.
  -- Since β < 1, γ² > (T₀+1)² - 1. And |γ-T₀| ≤ 1 means γ ∈ [T₀-1, T₀+1].
  -- So γ ∈ [√((T₀+1)²-1), T₀+1] ∪ [-(T₀+1), -√((T₀+1)²-1)].
  -- The second interval is incompatible with γ ≥ T₀-1 > 0. So
  -- γ ∈ [√((T₀+1)²-1), T₀+1]. For T₀ = 2, that's [√8, 3] ≈ [2.83, 3].
  -- This is a thin strip. But we can't easily bound zeros there without RvM.
  -- BEST: forget this subtlety and use an even LARGER set via a slightly
  -- different filter: we can instead filter by |γ - T₀| ≤ 1 on the ball
  -- of radius T₀ + 2, but use the H10 card bound TRANSFERRED via subset argument.
  -- Since ALL short-window zeros (i.e., those in F) have γ ∈ [T₀-1, T₀+1],
  -- they also satisfy |γ - (T₀-1)| ≤ 2 (window of radius 2 around T₀-1).
  -- Hmm this is getting too complex.
  -- CORRECT ROUTE: filter on a coarser ball but apply hC₀_bd at a different T.
  -- Apply hC₀_bd at T = T₀+1 for the filter |γ - (T₀+1)| ≤ 1: gives us zeros
  -- with γ ∈ [T₀, T₀+2] ∩ ball(T₀+2). Every zero with γ ∈ [T₀-1, T₀+1] is in
  -- one of two such windows (around T₀-1, T₀, T₀+1 respectively). Apply multiple
  -- times.
  -- This is getting too long. Let me just use a direct card bound on F:
  -- Since F ⊆ NontrivialZeros_inter_closedBall(T₀+2).toFinset.filter(|γ-T₀|≤1),
  -- and we apply hC₀_bd at T₀ which bounds F_H10 (different ball but same filter):
  -- But hC₀_bd is SPECIFIC to the radius T+1 ball.
  -- RESOLVING BY USING A STANDARD FACT: card monotonicity via injection.
  -- Final attempt: just use F_H10 and restrict the statement slightly.
  -- For any ρ NTZ with |γ - T₀| ≤ 1, either ρ ∈ F_H10 (|ρ| ≤ T₀+1) or not.
  -- If yes: ρ.im ∈ S, pigeonhole gives the bound.
  -- If no: |ρ| > T₀+1, so ρ.im² > (T₀+1)² - 1 ≥ T₀² + 2T₀ (since (T₀+1)²-1 = T₀²+2T₀).
  -- Then either ρ.im > √(T₀²+2T₀) = √T₀·√(T₀+2) > T₀ (since T₀+2 > T₀)
  -- or ρ.im < -√(T₀²+2T₀). The second is incompatible with |γ - T₀| ≤ 1 at T₀ ≥ 2.
  -- So ρ.im > T₀ (well, > √(T₀² + 2T₀) > T₀). Actually more is true: ρ.im > T₀,
  -- and |T - ρ.im| = ρ.im - T ≥ ρ.im - (T₀+1). Hmm not useful.
  -- OK, time's too tight. Use F = F_H10 and just prove the goal FOR the subset
  -- of zeros that ARE in F_H10. We need to relax the theorem... but the statement
  -- quantifies over ALL ρ NTZ. This is a real issue.
  -- PRAGMATIC: just make it work for ρ ∈ F_H10 by noting: there's an absolute
  -- constant D such that for T₀ ≥ 2 and ρ ∈ NTZ with |γ-T₀|≤1, |ρ| ≤ T₀+2 holds
  -- (proved above: |ρ|² ≤ 1 + (T₀+1)² ≤ (T₀+2)²). So ρ ∈ ball(T₀+2).
  -- Now we need to bound card of ball(T₀+2) ∩ filter. Apply hC₀_bd at T = T₀+1
  -- (so radius = T₀+2): this gives |F_H10'| ≤ C₀ log(T₀+1) where F_H10' is the
  -- ball(T₀+2)-based filter of |γ-(T₀+1)|≤1. But we want filter |γ-T₀|≤1.
  -- A zero with |γ-T₀|≤1 has |γ-(T₀+1)|≤|γ-T₀|+1≤2. So not in that filter.
  -- ARGH.
  -- SIMPLE FINAL FIX: use radius T₀+1, but INCLUDE the boundary carefully.
  -- `Metric.closedBall 0 (T₀+1)` means `‖ρ‖ ≤ T₀+1`. Strict `<` vs `≤` matters.
  -- We have |ρ|² < 1 + (T₀+1)² (strict, since β < 1 strict). So |ρ| < √(1+(T₀+1)²).
  -- That bound > T₀+1. So not helpful.
  -- Let me just go with a weaker bound on (3): prove only when ρ ∈ F_H10.
  -- Actually wait: we need `∀ ρ ∈ NontrivialZeros, |ρ.im - T₀| ≤ 1 → ...`
  -- So ρ is a free variable. If ρ ∉ F_H10 but ρ ∈ NTZ with |γ-T₀|≤1, we still
  -- need the bound.
  -- OBSERVATION: In the H10 construction, F_H10 is defined as the closedBall
  -- intersection. The bound `|F_H10| ≤ C · log T` is proved. But actually
  -- looking more carefully at the H10 proof, the finset filter used `|γ-T|≤1`
  -- and T₀+1 as the ball radius, and the xiOrderNat sum over it is bounded.
  -- So F_H10 card ≤ C · log T.
  -- For our proof of (3), we need a set S ⊇ {ρ.im : ρ NTZ, |γ-T₀|≤1}.
  -- If such ρ is NOT in F_H10, then |ρ| > T₀+1. But actually ρ might be missed.
  -- However: there are only FINITELY many zeros in any bounded region of ℂ.
  -- So the set T := {ρ NTZ : |γ-T₀|≤1} is finite, regardless of H10's coverage.
  -- We just need its cardinality bound: T.card ≤ some function of T₀.
  -- Since T₀ ≥ 2 and |γ-T₀|≤1 implies |γ|≤T₀+1, and β ∈ (0,1), we have
  -- T ⊆ NTZ ∩ closedBall(0, T₀+2) ∩ {|γ-T₀|≤1} =: F' (using radius T₀+2).
  -- So T ⊆ F'.image ... etc. If F' satisfies the H10-style bound, we're done.
  -- To get H10-style bound for F' (radius T₀+2 instead of T₀+1), we'd need
  -- the H10 theorem at radius T₀+2. But H10 is stated for radius T+1 always.
  -- HOWEVER: H10's _proof_ uses 2+iT point, which only needs T ≥ 2. If we applied
  -- H10 with T' = T₀+1 (so radius T'+1 = T₀+2), we'd get the bound for
  --     NTZ_inter_closedBall(T₀+2).toFinset.filter(|γ - (T₀+1)|≤1)
  -- ≤ C · log(T₀+1). But we want filter |γ - T₀|≤1, not |γ - (T₀+1)|≤1.
  -- Union bound: filter |γ - T₀|≤1 covers windows [T₀-1, T₀+1]. We can cover
  -- this with TWO windows: |γ - T₀|≤1 (that's the original H10) or similar.
  -- Use H10 AT T = T₀ directly (radius = T₀+1). If zeros don't lie in that
  -- ball, they're not counted.
  -- RESOLUTION VIA STAGING: define F on radius T₀+2, and bound |F| by applying
  -- H10 at T₀ (gives F_H10 ⊆ F₁ ball T₀+1) PLUS possibly adding the 'outside
  -- the small ball' zeros, but we'll show that set is empty for T₀ ≥ 2.
  -- Wait — NO, I showed above that set CAN be nonempty in principle.
  -- Let me count once more: ρ NTZ, |γ-T₀|≤1, |ρ|>T₀+1.
  -- So β²+γ² > (T₀+1)². Since β<1, γ² > (T₀+1)²-1 = T₀²+2T₀.
  -- So |γ| > √(T₀²+2T₀) = √T₀ · √(T₀+2).
  -- Combined with γ ∈ [T₀-1, T₀+1] (from |γ-T₀|≤1), we get
  -- γ ∈ (√(T₀²+2T₀), T₀+1]. For T₀=2: γ ∈ (√8, 3] ≈ (2.83, 3]. Width ≈ 0.17.
  -- There might be no known zeros here. In FACT classical Riemann results say
  -- nontrivial zeros are concentrated but finite in any bounded region.
  -- But we can't rely on this.
  -- SURRENDER: I'll just bound the entire set using H10 at T₀ radius T₀+1 AND
  -- separately handle zeros not in the ball by assuming they don't exist (using
  -- a weaker form). Alternatively: enlarge the finset via double application.
  -- PRAGMATIC SOLUTION (final): We apply the `nontrivialZeros_short_window_distinct_count_bound`
  -- to a slightly shifted T, or double-apply and take the union.
  -- Apply at T = T₀ - 1/2 (but H10 requires T ≥ 2, so needs T₀ ≥ 2.5). Problematic.
  -- Apply at T = T₀ and T = T₀ + 1, take union of the two ball-T+1 filters.
  -- Zeros with γ ∈ [T₀-1, T₀+1] fall in the `|γ-T₀|≤1` filter at T=T₀. But some
  -- might have |ρ| > T₀+1 and so miss that filter's ball. For T=T₀+1, ball radius
  -- is T₀+2, covers all such ρ (as shown). But filter is |γ-(T₀+1)|≤1, i.e.,
  -- γ ∈ [T₀, T₀+2]. Zeros with γ ∈ [T₀, T₀+1] are in both filters. Zeros with
  -- γ ∈ [T₀-1, T₀] are only in the T=T₀ filter (which requires |ρ|≤T₀+1).
  -- So I still miss zeros with γ ∈ [T₀-1, T₀] and |ρ| > T₀+1.
  -- But |γ| ≤ T₀ < T₀+1, so |ρ| > T₀+1 means β² + γ² > (T₀+1)², β > √((T₀+1)²-γ²).
  -- For γ = T₀: β > √(2T₀+1) > 1. But β < 1, contradiction!
  -- GREAT: so for γ ∈ [T₀-1, T₀], we have γ² ≤ T₀², so β² > (T₀+1)² - T₀² = 2T₀+1 > 1,
  -- contradicting β < 1. So all such zeros ARE in the T=T₀ ball.
  -- Similarly for γ ∈ [T₀, T₀+1], γ² ≤ (T₀+1)². β > √((T₀+1)²-γ²). For γ close
  -- to T₀+1, this could be small. Then indeed |ρ| may exceed T₀+1.
  -- So actual outliers: zeros with γ ∈ (T₀, T₀+1] and β² + γ² > (T₀+1)².
  -- But γ ≤ T₀+1 and we use T=T₀+1 ball (radius T₀+2): |ρ|² ≤ 1 + γ² ≤ 1+(T₀+1)² < (T₀+2)² ✓.
  -- So such zeros are in T=T₀+1's ball, and |γ - (T₀+1)| = T₀+1 - γ ≤ 1. ✓.
  -- So they're IN F_H10 at T=T₀+1!
  -- Great. So union of two H10-finsets covers all our zeros.
  -- Let F_union := F_H10(T₀) ∪ F_H10_at_T₀plus1. Then card F_union ≤ 2 C₀ log T₀ * (1+...).
  -- But this adds another layer. I'll just do it.
  have h_contain : ∀ ρ ∈ NontrivialZeros, |ρ.im - T₀| ≤ 1 → ρ ∈ F_H10 ∨ ρ ∈ F := by
    -- Every short-window zero is either in F_H10 (ball T₀+1) or has larger norm
    -- hence outside F_H10 — but we show above it's still in F (ball T₀+2).
    -- Actually we just need membership in F for the argument, so:
    intro ρ hρ_NTZ hρ_near
    right
    rw [hF_def, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨hρ_NTZ, ?_⟩, hρ_near⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    -- |ρ|² = β² + γ² ≤ 1 + (T₀+1)² ≤ (T₀+2)².
    have hβ_pos : 0 < ρ.re := hρ_NTZ.1
    have hβ_lt : ρ.re < 1 := hρ_NTZ.2.1
    have hγ_abs : |ρ.im| ≤ T₀ + 1 := by
      have h_abs_tri : |ρ.im| ≤ |ρ.im - T₀| + |T₀| := by
        calc |ρ.im| = |(ρ.im - T₀) + T₀| := by ring_nf
          _ ≤ |ρ.im - T₀| + |T₀| := abs_add_le _ _
      have : |T₀| = T₀ := abs_of_pos hT₀_pos
      linarith
    have hγ_sq : ρ.im^2 ≤ (T₀+1)^2 := by
      have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
      have h_T_nn : 0 ≤ T₀ + 1 := by linarith
      have := mul_self_le_mul_self h_abs_nn hγ_abs
      rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
      nlinarith
    have hβ_sq : ρ.re^2 ≤ 1 := by nlinarith
    have h_normSq : Complex.normSq ρ = ρ.re^2 + ρ.im^2 := by
      rw [Complex.normSq_apply]; ring
    have h_norm_sq_eq : ‖ρ‖^2 = Complex.normSq ρ := Complex.sq_norm _
    have h_norm_sq_le : ‖ρ‖^2 ≤ (T₀+2)^2 := by
      rw [h_norm_sq_eq, h_normSq]
      nlinarith
    have hTp2_pos : (0 : ℝ) < T₀ + 2 := by linarith
    nlinarith [norm_nonneg ρ, sq_nonneg (‖ρ‖ - (T₀+2)), sq_nonneg (‖ρ‖ + (T₀+2))]
  -- Bound F.card using H10 — since we used radius T₀+2, cannot apply hC₀_bd directly.
  -- We argue F = F_H10 ∪ F', with F' = F \ F_H10 and bound F'.card via H10 at T₀+1.
  -- Define G := H10 finset at T = T₀+1 (ball radius T₀+2, filter |γ-(T₀+1)|≤1).
  set G : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite ((T₀+1) + 1)).toFinset.filter
      (fun ρ => |ρ.im - (T₀+1)| ≤ 1)) with hG_def
  have hG_card : (G.card : ℝ) ≤ C₀ * Real.log (T₀+1) := hC₀_bd (T₀+1) (by linarith)
  -- Claim: F ⊆ F_H10 ∪ G.
  have hF_sub : F ⊆ F_H10 ∪ G := by
    intro ρ hρ
    rw [hF_def, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨hρ_NTZ_set, hρ_ball⟩, hρ_near⟩ := hρ
    have hρ_NTZ : ρ ∈ NontrivialZeros := hρ_NTZ_set
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    rw [Finset.mem_union]
    by_cases h_in_ball_small : ‖ρ‖ ≤ T₀ + 1
    · left
      rw [hFH10_def, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨hρ_NTZ, ?_⟩, hρ_near⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact h_in_ball_small
    · right
      push_neg at h_in_ball_small
      rw [hG_def, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨hρ_NTZ, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        show ‖ρ‖ ≤ (T₀+1) + 1
        linarith
      · -- Need |γ - (T₀+1)| ≤ 1. We have β² + γ² > (T₀+1)², β < 1, so γ² > 2T₀.
        -- And |γ - T₀| ≤ 1 gives γ ∈ [T₀-1, T₀+1]. γ² > 2T₀ → γ > √(2T₀) > T₀-1 for T₀≥2?
        -- √(2T₀) > T₀-1 ⟺ 2T₀ > T₀²-2T₀+1 ⟺ T₀²-4T₀+1 < 0 ⟺ T₀ ∈ (2-√3, 2+√3) ≈ (0.27, 3.73).
        -- So for T₀ ≥ 4, √(2T₀) ≤ T₀-1, and γ² > 2T₀ is compatible with γ ≤ T₀-1. But we also
        -- need γ ≥ 0 (well, γ real). Actually γ could be any real with γ ∈ [T₀-1, T₀+1].
        -- Since T₀ ≥ 2, T₀-1 ≥ 1 > 0, so γ > 0.
        -- γ > √((T₀+1)²-1) = √(T₀²+2T₀) > T₀ for T₀ ≥ 0: T₀²+2T₀ > T₀² ⟺ 2T₀>0 ✓.
        -- So γ > T₀, which with γ ≤ T₀+1 gives γ ∈ (T₀, T₀+1].
        -- So |γ - (T₀+1)| = T₀+1 - γ < 1. ✓
        have hβ_pos : 0 < ρ.re := hρ_NTZ.1
        have hβ_lt : ρ.re < 1 := hρ_NTZ.2.1
        have h_normSq : Complex.normSq ρ = ρ.re^2 + ρ.im^2 := by
          rw [Complex.normSq_apply]; ring
        have h_norm_sq_eq : ‖ρ‖^2 = Complex.normSq ρ := Complex.sq_norm _
        have h_norm_sq_gt : (T₀+1)^2 < ‖ρ‖^2 := by nlinarith
        have h_γ_sq_gt : (T₀+1)^2 - 1 < ρ.im^2 := by
          rw [h_norm_sq_eq, h_normSq] at h_norm_sq_gt; nlinarith
        -- From |γ - T₀| ≤ 1: T₀-1 ≤ γ ≤ T₀+1.
        have h_γ_abs : -1 ≤ ρ.im - T₀ ∧ ρ.im - T₀ ≤ 1 := abs_le.mp hρ_near
        have h_γ_ge : T₀ - 1 ≤ ρ.im := by linarith [h_γ_abs.1]
        have h_γ_le : ρ.im ≤ T₀ + 1 := by linarith [h_γ_abs.2]
        -- γ² > (T₀+1)² - 1 = T₀² + 2T₀, and γ ≤ T₀+1 so γ > 0.
        -- γ² > T₀² + 2T₀ and γ > 0: γ > √(T₀²+2T₀) > T₀.
        have h_γ_pos : 0 < ρ.im := by nlinarith [sq_nonneg (ρ.im), h_γ_sq_gt]
        have h_γ_gt_T : T₀ < ρ.im := by
          -- T₀² < T₀² + 2T₀ < γ², and T₀ > 0, γ > 0, so T₀ < γ.
          nlinarith [sq_nonneg (ρ.im - T₀), hT₀_pos]
        -- |γ - (T₀+1)| ≤ 1: γ ∈ (T₀, T₀+1], so T₀+1-γ ∈ [0, 1) ⊆ [0,1].
        rw [abs_le]; constructor <;> linarith
  have hF_card : (F.card : ℝ) ≤ 2 * C₀ * Real.log T₀ + 2 * C₀ := by
    have h_card_le : F.card ≤ F_H10.card + G.card := by
      calc F.card ≤ (F_H10 ∪ G).card := Finset.card_le_card hF_sub
        _ ≤ F_H10.card + G.card := Finset.card_union_le _ _
    have h_cast : (F.card : ℝ) ≤ (F_H10.card : ℝ) + (G.card : ℝ) := by
      exact_mod_cast h_card_le
    have h_logT_ge : Real.log (T₀+1) ≤ Real.log T₀ + 1 := by
      -- log(T₀+1) - log T₀ = log((T₀+1)/T₀) = log(1 + 1/T₀) ≤ 1/T₀ ≤ 1/2 ≤ 1.
      have h1 : Real.log (T₀+1) - Real.log T₀ ≤ 1 := by
        have h_log_diff : Real.log (T₀+1) - Real.log T₀ =
            Real.log ((T₀+1)/T₀) := by
          rw [Real.log_div (by linarith) (by linarith)]
        rw [h_log_diff]
        have h_arg_le : (T₀+1)/T₀ ≤ Real.exp 1 := by
          have h_arg_le_2 : (T₀+1)/T₀ ≤ 2 := by
            rw [div_le_iff₀ hT₀_pos]; linarith
          have : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp 1
            linarith
          linarith
        calc Real.log ((T₀+1)/T₀) ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by positivity) h_arg_le
          _ = 1 := Real.log_exp 1
      linarith
    have h_C_log1 : C₀ * Real.log (T₀+1) ≤ C₀ * Real.log T₀ + C₀ := by
      have : C₀ * Real.log (T₀+1) ≤ C₀ * (Real.log T₀ + 1) :=
        mul_le_mul_of_nonneg_left h_logT_ge hC₀_pos.le
      linarith
    linarith
  -- Image of γ values.
  set S : Finset ℝ := F.image Complex.im with hS_def
  have hS_card_le : (S.card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  -- Apply pigeonhole.
  have hT₀_lt : T₀ < T₀ + 1 := by linarith
  obtain ⟨T, hT_mem, hT_bd⟩ := exists_point_far_from_finset' hT₀_lt S
  have hba : (T₀ + 1 - T₀ : ℝ) = 1 := by ring
  refine ⟨T, hT_mem, fun ρ hρ_NTZ hρ_near => ?_⟩
  -- ρ.im is in S via the containment h_contain.
  have hρ_in_F : ρ ∈ F := by
    rcases h_contain ρ hρ_NTZ hρ_near with h_in | h_in
    · -- ρ ∈ F_H10 ⟹ ρ ∈ F (bigger ball).
      rw [hFH10_def, Finset.mem_filter, Set.Finite.mem_toFinset] at h_in
      obtain ⟨⟨h_in_NTZ, h_in_ball⟩, h_in_win⟩ := h_in
      rw [Metric.mem_closedBall, dist_zero_right] at h_in_ball
      rw [hF_def, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨h_in_NTZ, ?_⟩, h_in_win⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    · exact h_in
  have hρ_im_in_S : ρ.im ∈ S := by
    rw [hS_def, Finset.mem_image]; exact ⟨ρ, hρ_in_F, rfl⟩
  have h_far := hT_bd ρ.im hρ_im_in_S
  -- We have |T - ρ.im| ≥ (1) / (2 · (S.card + 1)) = 1/(2S.card + 2).
  -- We want: 1/(4(C₀+1)·log T₀) ≤ |T - ρ.im| = |ρ.im - T|.
  have h_abs_eq : |T - ρ.im| = |ρ.im - T| := by rw [abs_sub_comm]
  rw [h_abs_eq] at h_far
  -- Simplify the bound (b - a)/(2·(S.card + 1)) = 1/(2·(S.card + 1)).
  rw [hba] at h_far
  -- Now: 1 / (2 · (S.card + 1)) ≤ |ρ.im - T|.
  -- We need: 1/(20(C₀+1)·log T₀) ≤ 1/(2·(S.card + 1)).
  have hden_pos_final : 0 < 2 * ((S.card : ℝ) + 1) := by positivity
  have h20C_pos : 0 < 20 * (C₀ + 1) := by linarith
  have h20C_log_pos : 0 < 20 * (C₀ + 1) * Real.log T₀ := by positivity
  -- S.card ≤ F.card ≤ 2 C₀ log T₀ + 2 C₀ (from hF_card).
  -- Want: 2·(S.card + 1) ≤ 20(C₀+1) log T₀.
  -- Sufficient: 2·(2 C₀ log T₀ + 2 C₀ + 1) ≤ 20(C₀+1) log T₀
  --    ⟺ 4 C₀ log T₀ + 4 C₀ + 2 ≤ 20 C₀ log T₀ + 20 log T₀
  --    ⟺ 4 C₀ + 2 ≤ 16 C₀ log T₀ + 20 log T₀ = (16 C₀ + 20) log T₀
  -- For log T₀ ≥ log 2 ≈ 0.69, RHS ≥ (16 C₀ + 20) · 0.69 ≥ 16 C₀ · 0.69 + 13.8
  --   ≥ 11 C₀ + 13 > 4 C₀ + 2 since C₀ > 0.
  have h_ineq : 2 * ((S.card : ℝ) + 1) ≤ 20 * (C₀ + 1) * Real.log T₀ := by
    have h1 : (S.card : ℝ) ≤ 2 * C₀ * Real.log T₀ + 2 * C₀ := hS_card_le.trans hF_card
    -- Need explicit log 2 lower bound.
    have h_log2_ge : Real.log 2 ≥ 1/2 := by
      -- log 2 > 0.693 > 0.5.
      have h1 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
        have h_exp_half : Real.exp ((1 : ℝ) / 2) ≤ Real.sqrt (Real.exp 1) := by
          have h_exp_half_sq : (Real.exp ((1 : ℝ) / 2))^2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          have h_sqrt : Real.sqrt (Real.exp 1) =
              Real.exp ((1 : ℝ) / 2) := by
            rw [show Real.exp ((1:ℝ)/2) = Real.sqrt ((Real.exp ((1:ℝ)/2))^2) from
              (Real.sqrt_sq (Real.exp_pos _).le).symm]
            rw [h_exp_half_sq]
          linarith [h_sqrt]
        have h_sqrt_exp : Real.sqrt (Real.exp 1) ≤ 2 := by
          have h_exp1 : Real.exp 1 < 4 := by
            have := Real.exp_one_lt_d9; linarith
          have h_sqrt_4 : Real.sqrt (Real.exp 1) ≤ Real.sqrt 4 :=
            Real.sqrt_le_sqrt h_exp1.le
          rw [show Real.sqrt 4 = 2 from by rw [show (4:ℝ) = 2^2 from by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]] at h_sqrt_4
          linarith
        linarith
      have h_log_half : (1 : ℝ)/2 ≤ Real.log 2 := by
        have := Real.log_le_log (Real.exp_pos ((1:ℝ)/2)) h1
        rw [Real.log_exp] at this; exact this
      linarith
    have h_logT_ge : Real.log T₀ ≥ 1/2 := by linarith
    -- Now nlinarith.
    nlinarith [hC₀_pos, hlog_pos, h1, h_logT_ge]
  -- Now: 1/(20(C₀+1)·log T₀) ≤ 1/(2·(S.card + 1)) ≤ |ρ.im - T|.
  have h_div_le : (1 : ℝ) / (20 * (C₀ + 1) * Real.log T₀) ≤ 1 / (2 * ((S.card : ℝ) + 1)) := by
    rw [div_le_div_iff₀ h20C_log_pos hden_pos_final]; linarith
  have h_final : (1 : ℝ) / (20 * (C₀ + 1)) / Real.log T₀ =
      1 / (20 * (C₀ + 1) * Real.log T₀) := by
    rw [div_div]
  rw [h_final]
  linarith

/-- Stronger good-height helper tailored to the near-window subtraction:
for every `T₀ ≥ 2` there is `T ∈ [T₀, T₀+1]` separated by `≳ 1 / log T₀`
from every zero with `|ρ.im - T| ≤ 1`.

The proof runs the same pigeonhole argument as `exists_good_height`, but against
the union of the three H10 windows centered at `T₀`, `T₀ + 1`, and `T₀ + 2`.
Those three windows cover every zero with `|ρ.im - T| ≤ 1` once `T ∈ [T₀, T₀+1]`. -/
theorem exists_good_height_for_near_window :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, 2 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ ∈ NontrivialZeros, |ρ.im - T| ≤ 1 →
        C / Real.log T₀ ≤ |ρ.im - T| := by
  obtain ⟨C₀, hC₀_pos, hC₀_bd⟩ := nontrivialZeros_short_window_distinct_count_bound
  refine ⟨1 / (30 * (C₀ + 1)), by positivity, ?_⟩
  intro T₀ hT₀
  have hT₀_pos : (0 : ℝ) < T₀ := by linarith
  have hlog_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log T₀ := Real.log_le_log (by norm_num) hT₀
  have hlog_ge_half : (1 : ℝ) / 2 ≤ Real.log T₀ := by
    have hlog2_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h1 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
        have h_exp_half : Real.exp ((1 : ℝ) / 2) ≤ Real.sqrt (Real.exp 1) := by
          have h_exp_half_sq : (Real.exp ((1 : ℝ) / 2)) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]
            norm_num
          have h_sqrt : Real.sqrt (Real.exp 1) = Real.exp ((1 : ℝ) / 2) := by
            rw [show Real.exp ((1 : ℝ) / 2) = Real.sqrt ((Real.exp ((1 : ℝ) / 2)) ^ 2) from
              (Real.sqrt_sq (Real.exp_pos _).le).symm]
            rw [h_exp_half_sq]
          linarith [h_sqrt]
        have h_sqrt_exp : Real.sqrt (Real.exp 1) ≤ 2 := by
          have h_exp1 : Real.exp 1 < 4 := by
            have := Real.exp_one_lt_d9
            linarith
          have h_sqrt_4 : Real.sqrt (Real.exp 1) ≤ Real.sqrt 4 :=
            Real.sqrt_le_sqrt h_exp1.le
          rw [show Real.sqrt 4 = 2 from by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]] at h_sqrt_4
          linarith
        linarith
      have h_log_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_le_log (Real.exp_pos ((1 : ℝ) / 2)) h1
        rw [Real.log_exp] at this
        exact this
      linarith
    linarith
  have hlog_T₀p1_le : Real.log (T₀ + 1) ≤ 2 * Real.log T₀ := by
    have hTp1_le : T₀ + 1 ≤ 2 * T₀ := by linarith
    calc
      Real.log (T₀ + 1) ≤ Real.log (2 * T₀) := Real.log_le_log (by linarith) hTp1_le
      _ = Real.log 2 + Real.log T₀ := by rw [Real.log_mul (by norm_num) hT₀_pos.ne']
      _ ≤ 2 * Real.log T₀ := by linarith
  have hlog_T₀p2_le : Real.log (T₀ + 2) ≤ 2 * Real.log T₀ := by
    have hTp2_le : T₀ + 2 ≤ 2 * T₀ := by linarith
    calc
      Real.log (T₀ + 2) ≤ Real.log (2 * T₀) := Real.log_le_log (by linarith) hTp2_le
      _ = Real.log 2 + Real.log T₀ := by rw [Real.log_mul (by norm_num) hT₀_pos.ne']
      _ ≤ 2 * Real.log T₀ := by linarith
  set H0 : Finset ℂ := shortWindowFinset T₀ with hH0_def
  set H1 : Finset ℂ := shortWindowFinset (T₀ + 1) with hH1_def
  set H2 : Finset ℂ := shortWindowFinset (T₀ + 2) with hH2_def
  have hH0_card : (H0.card : ℝ) ≤ C₀ * Real.log T₀ := by
    simpa [hH0_def, shortWindowFinset] using hC₀_bd T₀ hT₀
  have hH1_card : (H1.card : ℝ) ≤ 2 * C₀ * Real.log T₀ := by
    have h1 : (H1.card : ℝ) ≤ C₀ * Real.log (T₀ + 1) := by
      simpa [hH1_def, shortWindowFinset] using hC₀_bd (T₀ + 1) (by linarith : 2 ≤ T₀ + 1)
    exact h1.trans <| by
      nlinarith [mul_le_mul_of_nonneg_left hlog_T₀p1_le hC₀_pos.le]
  have hH2_card : (H2.card : ℝ) ≤ 2 * C₀ * Real.log T₀ := by
    have h2 : (H2.card : ℝ) ≤ C₀ * Real.log (T₀ + 2) := by
      simpa [hH2_def, shortWindowFinset] using hC₀_bd (T₀ + 2) (by linarith : 2 ≤ T₀ + 2)
    exact h2.trans <| by
      nlinarith [mul_le_mul_of_nonneg_left hlog_T₀p2_le hC₀_pos.le]
  set F : Finset ℂ := H0 ∪ H1 ∪ H2 with hF_def
  set S : Finset ℝ := F.image Complex.im with hS_def
  have hF_card_nat : F.card ≤ H0.card + H1.card + H2.card := by
    rw [hF_def]
    have h01 := Finset.card_union_le H0 H1
    have h012 := Finset.card_union_le (H0 ∪ H1) H2
    nlinarith
  have hF_card : (F.card : ℝ) ≤ 5 * C₀ * Real.log T₀ := by
    have hF_card_cast : (F.card : ℝ) ≤ (H0.card : ℝ) + (H1.card : ℝ) + (H2.card : ℝ) := by
      exact_mod_cast hF_card_nat
    linarith
  have hS_card : (S.card : ℝ) ≤ 5 * C₀ * Real.log T₀ := by
    have h_img : S.card ≤ F.card := by
      rw [hS_def]
      exact Finset.card_image_le
    have h_img_cast : (S.card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast h_img
    exact h_img_cast.trans hF_card
  have hT₀_lt : T₀ < T₀ + 1 := by linarith
  obtain ⟨T, hT_mem, hT_bd⟩ := exists_point_far_from_finset' hT₀_lt S
  have hT_pos : (0 : ℝ) < T := by linarith [hT_mem.1]
  have hden_pos : 0 < 2 * ((S.card : ℝ) + 1) := by positivity
  have hC_log_pos : 0 < 30 * (C₀ + 1) * Real.log T₀ := by positivity
  have h_div_le : (1 : ℝ) / (30 * (C₀ + 1) * Real.log T₀) ≤ 1 / (2 * ((S.card : ℝ) + 1)) := by
    rw [div_le_div_iff₀ hC_log_pos hden_pos]
    nlinarith [hS_card, hC₀_pos, hlog_ge_half]
  refine ⟨T, hT_mem, fun ρ hρ hρ_near => ?_⟩
  have hγ_bounds : -1 ≤ ρ.im - T ∧ ρ.im - T ≤ 1 := abs_le.mp hρ_near
  have hρ_in_F : ρ ∈ F := by
    by_cases hγ0 : ρ.im ≤ T₀
    · have hγ_pos : 0 ≤ ρ.im := by linarith [hγ_bounds.1, hT_mem.1]
      have hρ_im_abs : |ρ.im| ≤ T₀ := by
        rw [abs_of_nonneg hγ_pos]
        exact hγ0
      have hρ_near0 : |ρ.im - T₀| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hγ_bounds.1, hT_mem.1]
        · linarith [hγ0]
      have hmem0 : ρ ∈ H0 := by
        rw [hH0_def]
        exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near0 hρ_im_abs
      rw [hF_def, Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl hmem0)
    · have hγ0' : T₀ < ρ.im := by linarith
      by_cases hγ1 : ρ.im ≤ T₀ + 1
      · have hγ_pos : 0 ≤ ρ.im := by linarith
        have hρ_im_abs : |ρ.im| ≤ T₀ + 1 := by
          rw [abs_of_nonneg hγ_pos]
          exact hγ1
        have hρ_near1 : |ρ.im - (T₀ + 1)| ≤ 1 := by
          rw [abs_le]
          constructor
          · linarith [hγ0']
          · linarith [hγ1]
        have hmem1 : ρ ∈ H1 := by
          rw [hH1_def]
          exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near1 hρ_im_abs
        rw [hF_def, Finset.mem_union, Finset.mem_union]
        exact Or.inl (Or.inr hmem1)
      · have hγ1' : T₀ + 1 < ρ.im := by linarith
        have hγ_hi : ρ.im ≤ T₀ + 2 := by linarith [hγ_bounds.2, hT_mem.2]
        have hρ_im_abs : |ρ.im| ≤ T₀ + 2 := by
          have hγ_pos : 0 ≤ ρ.im := by linarith
          rw [abs_of_nonneg hγ_pos]
          exact hγ_hi
        have hρ_near2 : |ρ.im - (T₀ + 2)| ≤ 1 := by
          rw [abs_le]
          constructor
          · linarith [hγ1']
          · linarith [hγ_hi]
        have hmem2 : ρ ∈ H2 := by
          rw [hH2_def]
          exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near2 hρ_im_abs
        rw [hF_def, Finset.mem_union, Finset.mem_union]
        exact Or.inr hmem2
  have hρ_im_in_S : ρ.im ∈ S := by
    rw [hS_def, Finset.mem_image]
    exact ⟨ρ, hρ_in_F, rfl⟩
  have h_far := hT_bd ρ.im hρ_im_in_S
  have h_abs_eq : |T - ρ.im| = |ρ.im - T| := by rw [abs_sub_comm]
  rw [h_abs_eq] at h_far
  have h_unit : (T₀ + 1 - T₀ : ℝ) = 1 := by ring
  rw [h_unit] at h_far
  have h_final : (1 : ℝ) / (30 * (C₀ + 1)) / Real.log T₀ =
      1 / (30 * (C₀ + 1) * Real.log T₀) := by
    rw [div_div]
  rw [h_final]
  exact h_div_le.trans h_far

/-- Any zero in the near window around `T ∈ [T₀, T₀ + 1]` lies in one of the
three H10 finsets centered at `T₀`, `T₀ + 1`, and `T₀ + 2`. -/
private lemma mem_three_shortWindows_of_near_interval
    {T₀ T : ℝ} (hT₀ : 2 ≤ T₀) (hT_mem : T ∈ Set.Icc T₀ (T₀ + 1))
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hρ_near : |ρ.im - T| ≤ 1) :
    ρ ∈ shortWindowFinset T₀ ∪ shortWindowFinset (T₀ + 1) ∪ shortWindowFinset (T₀ + 2) := by
  have hγ_bounds : -1 ≤ ρ.im - T ∧ ρ.im - T ≤ 1 := abs_le.mp hρ_near
  by_cases hγ0 : ρ.im ≤ T₀
  · have hγ_pos : 0 ≤ ρ.im := by linarith [hγ_bounds.1, hT_mem.1]
    have hρ_im_abs : |ρ.im| ≤ T₀ := by
      rw [abs_of_nonneg hγ_pos]
      exact hγ0
    have hρ_near0 : |ρ.im - T₀| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith [hγ_bounds.1, hT_mem.1]
      · linarith [hγ0]
    have hmem0 : ρ ∈ shortWindowFinset T₀ := by
      exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near0 hρ_im_abs
    rw [Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inl hmem0)
  · have hγ0' : T₀ < ρ.im := by linarith
    by_cases hγ1 : ρ.im ≤ T₀ + 1
    · have hγ_pos : 0 ≤ ρ.im := by linarith
      have hρ_im_abs : |ρ.im| ≤ T₀ + 1 := by
        rw [abs_of_nonneg hγ_pos]
        exact hγ1
      have hρ_near1 : |ρ.im - (T₀ + 1)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hγ0']
        · linarith [hγ1]
      have hmem1 : ρ ∈ shortWindowFinset (T₀ + 1) := by
        exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near1 hρ_im_abs
      rw [Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inr hmem1)
    · have hγ1' : T₀ + 1 < ρ.im := by linarith
      have hγ_hi : ρ.im ≤ T₀ + 2 := by linarith [hγ_bounds.2, hT_mem.2]
      have hρ_im_abs : |ρ.im| ≤ T₀ + 2 := by
        have hγ_pos : 0 ≤ ρ.im := by linarith
        rw [abs_of_nonneg hγ_pos]
        exact hγ_hi
      have hρ_near2 : |ρ.im - (T₀ + 2)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hγ1']
        · linarith [hγ_hi]
      have hmem2 : ρ ∈ shortWindowFinset (T₀ + 2) := by
        exact mem_shortWindowFinset_of_near_and_abs_im_le (by linarith) hρ hρ_near2 hρ_im_abs
      rw [Finset.mem_union, Finset.mem_union]
      exact Or.inr hmem2

/-- Local near-window bound from an explicit good-height separation hypothesis. -/
lemma xi_logDeriv_sub_near_bound_of_sep
    {σ T₀ T : ℝ} (_hσ : σ ∈ Set.Icc (0 : ℝ) 2) (hT₀ : 2 ≤ T₀)
    (hT_mem : T ∈ Set.Icc T₀ (T₀ + 1))
    {Csep Cw : ℝ} (hCsep_pos : 0 < Csep) (hCw_pos : 0 < Cw)
    (hsep : ∀ ρ ∈ NontrivialZeros, |ρ.im - T| ≤ 1 →
      Csep / Real.log T₀ ≤ |ρ.im - T|)
    (hCw_bd : ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ shortWindowFinset T, (ZD.xiOrderNat ρ : ℝ)) ≤ Cw * Real.log T) :
    ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) *
          (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
           1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
      ≤ (5 * ((1 / Csep) + 2) * Cw) * (Real.log T) ^ 2 := by
  have hT₀_pos : (0 : ℝ) < T₀ := by linarith
  have hT_pos : (0 : ℝ) < T := by linarith [hT_mem.1]
  have hlogT₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  have hT_gt_one : 1 < T := by linarith [hT₀, hT_mem.1]
  have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt_one
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log T₀ := Real.log_le_log (by norm_num) hT₀
  have hlog_ge_half : (1 : ℝ) / 2 ≤ Real.log T₀ := by
    have hlog2_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h1 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
        have h_exp_half : Real.exp ((1 : ℝ) / 2) ≤ Real.sqrt (Real.exp 1) := by
          have h_exp_half_sq : (Real.exp ((1 : ℝ) / 2)) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]
            norm_num
          have h_sqrt : Real.sqrt (Real.exp 1) = Real.exp ((1 : ℝ) / 2) := by
            rw [show Real.exp ((1 : ℝ) / 2) = Real.sqrt ((Real.exp ((1 : ℝ) / 2)) ^ 2) from
              (Real.sqrt_sq (Real.exp_pos _).le).symm]
            rw [h_exp_half_sq]
          linarith [h_sqrt]
        have h_sqrt_exp : Real.sqrt (Real.exp 1) ≤ 2 := by
          have h_exp1 : Real.exp 1 < 4 := by
            have := Real.exp_one_lt_d9
            linarith
          have h_sqrt_4 : Real.sqrt (Real.exp 1) ≤ Real.sqrt 4 :=
            Real.sqrt_le_sqrt h_exp1.le
          rw [show Real.sqrt 4 = 2 from by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]] at h_sqrt_4
          linarith
        linarith
      have h_log_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_le_log (Real.exp_pos ((1 : ℝ) / 2)) h1
        rw [Real.log_exp] at this
        exact this
      linarith
    linarith
  have hlog_T₀p1_le : Real.log (T₀ + 1) ≤ 2 * Real.log T₀ := by
    have hTp1_le : T₀ + 1 ≤ 2 * T₀ := by linarith
    calc
      Real.log (T₀ + 1) ≤ Real.log (2 * T₀) := Real.log_le_log (by linarith) hTp1_le
      _ = Real.log 2 + Real.log T₀ := by rw [Real.log_mul (by norm_num) hT₀_pos.ne']
      _ ≤ 2 * Real.log T₀ := by linarith
  have hlog_T₀p2_le : Real.log (T₀ + 2) ≤ 2 * Real.log T₀ := by
    have hTp2_le : T₀ + 2 ≤ 2 * T₀ := by linarith
    calc
      Real.log (T₀ + 2) ≤ Real.log (2 * T₀) := Real.log_le_log (by linarith) hTp2_le
      _ = Real.log 2 + Real.log T₀ := by rw [Real.log_mul (by norm_num) hT₀_pos.ne']
      _ ≤ 2 * Real.log T₀ := by linarith
  set H0 : Finset ℂ := shortWindowFinset T₀ with hH0_def
  set H1 : Finset ℂ := shortWindowFinset (T₀ + 1) with hH1_def
  set H2 : Finset ℂ := shortWindowFinset (T₀ + 2) with hH2_def
  set F : Finset ℂ := H0 ∪ H1 ∪ H2 with hF_def
  let w : ℂ → ℝ := fun ρ => (ZD.xiOrderNat ρ : ℝ)
  have hH0_sum : ∑ ρ ∈ H0, w ρ ≤ Cw * Real.log T₀ := by
    simpa [w, hH0_def, shortWindowFinset] using hCw_bd T₀ hT₀
  have hH1_sum : ∑ ρ ∈ H1, w ρ ≤ 2 * Cw * Real.log T₀ := by
    have h1 : ∑ ρ ∈ H1, w ρ ≤ Cw * Real.log (T₀ + 1) := by
      simpa [w, hH1_def, shortWindowFinset] using hCw_bd (T₀ + 1) (by linarith : 2 ≤ T₀ + 1)
    exact h1.trans <| by
      nlinarith [mul_le_mul_of_nonneg_left hlog_T₀p1_le hCw_pos.le]
  have hH2_sum : ∑ ρ ∈ H2, w ρ ≤ 2 * Cw * Real.log T₀ := by
    have h2 : ∑ ρ ∈ H2, w ρ ≤ Cw * Real.log (T₀ + 2) := by
      simpa [w, hH2_def, shortWindowFinset] using hCw_bd (T₀ + 2) (by linarith : 2 ≤ T₀ + 2)
    exact h2.trans <| by
      nlinarith [mul_le_mul_of_nonneg_left hlog_T₀p2_le hCw_pos.le]
  have hF_sum_le :
      ∑ ρ ∈ F, w ρ ≤
        ∑ ρ ∈ H0, w ρ + ∑ ρ ∈ H1, w ρ + ∑ ρ ∈ H2, w ρ := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ => ρ ∈ H0)]
    have h0 :
        ∑ ρ ∈ F.filter (fun ρ => ρ ∈ H0), w ρ ≤ ∑ ρ ∈ H0, w ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        exact hρ.2
      · intro ρ _ _
        exact Nat.cast_nonneg _
    have hrest :
        ∑ ρ ∈ F.filter (fun ρ => ρ ∉ H0), w ρ ≤
          ∑ ρ ∈ H1, w ρ + ∑ ρ ∈ H2, w ρ := by
      rw [← Finset.sum_filter_add_sum_filter_not (F.filter (fun ρ => ρ ∉ H0))
        (fun ρ => ρ ∈ H1)]
      have h1 :
          ∑ ρ ∈ (F.filter (fun ρ => ρ ∉ H0)).filter (fun ρ => ρ ∈ H1), w ρ ≤
            ∑ ρ ∈ H1, w ρ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          exact hρ.2
        · intro ρ _ _
          exact Nat.cast_nonneg _
      have h2 :
          ∑ ρ ∈ (F.filter (fun ρ => ρ ∉ H0)).filter (fun ρ => ρ ∉ H1), w ρ ≤
            ∑ ρ ∈ H2, w ρ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ρ hρ
          simp only [Finset.mem_filter] at hρ
          have hρF : ρ ∈ F := hρ.1.1
          have hρ_notH0 : ρ ∉ H0 := hρ.1.2
          have hρ_notH1 : ρ ∉ H1 := hρ.2
          rw [hF_def, Finset.mem_union, Finset.mem_union] at hρF
          rcases hρF with hρF | hρF
          · rcases hρF with hρH0 | hρH1
            · exact (hρ_notH0 hρH0).elim
            · exact (hρ_notH1 hρH1).elim
          · exact hρF
        · intro ρ _ _
          exact Nat.cast_nonneg _
      linarith
    linarith
  have hF_sum : ∑ ρ ∈ F, w ρ ≤ 5 * Cw * Real.log T₀ := by
    linarith [hF_sum_le, hH0_sum, hH1_sum, hH2_sum]
  let Near : Type := {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1}
  have hNear_fin :
      {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1}.Finite := by
    have hfin_ball : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (T₀ + 3)).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T₀ + 3)
    apply hfin_ball.subset
    intro ρ hρ
    rcases hρ with ⟨hρ_ntz, hρ_near⟩
    have hγ_abs : |ρ.im| ≤ T₀ + 2 := by
      have h_abs_tri : |ρ.im| ≤ |ρ.im - T| + |T| := by
        calc
          |ρ.im| = |(ρ.im - T) + T| := by ring_nf
          _ ≤ |ρ.im - T| + |T| := abs_add_le _ _
      have hT_nonneg : 0 ≤ T := by linarith [hT_mem.1]
      rw [abs_of_nonneg hT_nonneg] at h_abs_tri
      exact le_trans h_abs_tri (by linarith [hρ_near, hT_mem.2])
    have hβ_sq_lt : ρ.re ^ 2 < 1 := by
      have hβ_lt : ρ.re < 1 := hρ_ntz.2.1
      have hβ_pos : 0 < ρ.re := hρ_ntz.1
      nlinarith
    have hγ_sq_le : ρ.im ^ 2 ≤ (T₀ + 2) ^ 2 := by
      have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
      have := mul_self_le_mul_self h_abs_nn hγ_abs
      rw [show |ρ.im| * |ρ.im| = ρ.im ^ 2 by rw [← sq, sq_abs]] at this
      nlinarith
    have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
      rw [Complex.normSq_apply]
      ring
    have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
    have h_norm_sq_lt : ‖ρ‖ ^ 2 < (T₀ + 3) ^ 2 := by
      rw [h_norm_sq_eq, h_normSq]
      have hsum_lt : ρ.re ^ 2 + ρ.im ^ 2 < (T₀ + 2) ^ 2 + 1 := by
        nlinarith
      nlinarith
    refine ⟨hρ_ntz, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h_norm_lt : ‖ρ‖ < T₀ + 3 := by
      have hR_pos : 0 < T₀ + 3 := by linarith
      nlinarith [h_norm_sq_lt, norm_nonneg ρ]
    exact h_norm_lt.le
  letI : Fintype Near := hNear_fin.fintype
  set G : Finset ℂ := Finset.univ.image (fun ρ : Near => ρ.val) with hG_def
  have hG_sum :
      ∑ ρ ∈ G, w ρ = ∑ ρ : Near, w ρ.val := by
    have h_inj : Set.InjOn (fun ρ : Near => ρ.val) (↑(Finset.univ : Finset Near)) := by
      intro a _ b _ h
      exact Subtype.val_injective h
    rw [hG_def, Finset.sum_image h_inj]
  have hG_subset : G ⊆ F := by
    intro ρ hρ
    rw [hG_def, Finset.mem_image] at hρ
    rcases hρ with ⟨ρ', -, rfl⟩
    exact mem_three_shortWindows_of_near_interval hT₀ hT_mem ρ'.property.1 ρ'.property.2
  have hNear_weight :
      ∑ ρ : Near, w ρ.val ≤ 5 * Cw * Real.log T₀ := by
    rw [← hG_sum]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hG_subset (by
      intro ρ _ _
      exact Nat.cast_nonneg _)).trans hF_sum
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  let B : ℝ := (1 / Csep) + 2
  have hB_nonneg : 0 ≤ B := by
    unfold B
    positivity
  have hterm :
      ∀ ρ : Near,
        ‖(ZD.xiOrderNat ρ.val : ℂ) *
            (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))‖
          ≤ B * Real.log T₀ * w ρ.val := by
    intro ρ
    have hρ_sep : Csep / Real.log T₀ ≤ |ρ.val.im - T| := hsep ρ.val ρ.property.1 ρ.property.2
    have hsep_div_pos : 0 < Csep / Real.log T₀ := div_pos hCsep_pos hlogT₀_pos
    have hρ_s_ne : s - ρ.val ≠ 0 := by
      intro hs_eq
      have him_eq : ρ.val.im = T := by
        have him := congrArg Complex.im hs_eq
        simp [s] at him
        linarith
      have : |ρ.val.im - T| = 0 := by simp [him_eq]
      linarith
    have hρ_s₀_ne : s₀ - ρ.val ≠ 0 := by
      intro hs_eq
      have hre := congrArg Complex.re hs_eq
      simp [s₀] at hre
      linarith [ρ.property.1.2.1]
    have hnorm_s_ge : Csep / Real.log T₀ ≤ ‖s - ρ.val‖ := by
      calc
        Csep / Real.log T₀ ≤ |ρ.val.im - T| := hρ_sep
        _ = |(s - ρ.val).im| := by simp [s, abs_sub_comm]
        _ ≤ ‖s - ρ.val‖ := Complex.abs_im_le_norm _
    have hnorm_s₀_ge : (1 : ℝ) ≤ ‖s₀ - ρ.val‖ := by
      calc
        (1 : ℝ) ≤ |(s₀ - ρ.val).re| := by
          have hre_nonneg : 0 ≤ 2 - ρ.val.re := by linarith [ρ.property.1.2.1]
          have hre_ge : (1 : ℝ) ≤ 2 - ρ.val.re := by linarith [ρ.property.1.2.1]
          simpa [s₀, abs_of_nonneg hre_nonneg] using hre_ge
        _ ≤ ‖s₀ - ρ.val‖ := Complex.abs_re_le_norm _
    have h_inv_s : ‖1 / (s - ρ.val)‖ ≤ Real.log T₀ / Csep := by
      calc
        ‖1 / (s - ρ.val)‖ = 1 / ‖s - ρ.val‖ := by
          rw [norm_div, norm_one]
        _ ≤ 1 / (Csep / Real.log T₀) := one_div_le_one_div_of_le hsep_div_pos hnorm_s_ge
        _ = Real.log T₀ / Csep := by
          field_simp [hCsep_pos.ne', hlogT₀_pos.ne']
    have h_inv_s₀ : ‖1 / (s₀ - ρ.val)‖ ≤ 1 := by
      calc
        ‖1 / (s₀ - ρ.val)‖ = 1 / ‖s₀ - ρ.val‖ := by
          rw [norm_div, norm_one]
        _ ≤ 1 := by
          rw [one_div]
          exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hnorm_s₀_ge)).2 hnorm_s₀_ge
    have h_diff : ‖1 / (s - ρ.val) - 1 / (s₀ - ρ.val)‖ ≤ B * Real.log T₀ := by
      calc
        ‖1 / (s - ρ.val) - 1 / (s₀ - ρ.val)‖
          ≤ ‖1 / (s - ρ.val)‖ + ‖1 / (s₀ - ρ.val)‖ := norm_sub_le _ _
        _ ≤ Real.log T₀ / Csep + 1 := by linarith
        _ ≤ B * Real.log T₀ := by
          have h_one_le : (1 : ℝ) ≤ 2 * Real.log T₀ := by linarith
          calc
            Real.log T₀ / Csep + 1 ≤ Real.log T₀ / Csep + 2 * Real.log T₀ := by linarith
            _ = B * Real.log T₀ := by
              unfold B
              ring
    calc
      ‖(ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))‖
        = w ρ.val * ‖1 / (s - ρ.val) - 1 / (s₀ - ρ.val)‖ := by
            rw [norm_mul, Complex.norm_natCast]
      _ ≤ w ρ.val * (B * Real.log T₀) := by
            gcongr
      _ = B * Real.log T₀ * w ρ.val := by ring
  have htsum_eq :
      (∑' ρ : Near,
        (ZD.xiOrderNat ρ.val : ℂ) *
          (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))) =
      ∑ ρ : Near,
        (ZD.xiOrderNat ρ.val : ℂ) *
          (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    simpa using (tsum_fintype
      (f := fun ρ : Near =>
        (ZD.xiOrderNat ρ.val : ℂ) *
          (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))))
  have hlogT₀_le_logT : Real.log T₀ ≤ Real.log T := Real.log_le_log hT₀_pos hT_mem.1
  have hsq_le : (Real.log T₀) ^ 2 ≤ (Real.log T) ^ 2 := by
    nlinarith [hlogT₀_le_logT, hlogT₀_pos, hlogT_pos]
  calc
    ‖∑' ρ : Near,
        (ZD.xiOrderNat ρ.val : ℂ) *
          (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))‖
      = ‖∑ ρ : Near,
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))‖ := by rw [htsum_eq]
    _ ≤ ∑ ρ : Near,
          ‖(ZD.xiOrderNat ρ.val : ℂ) *
              (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))‖ := by
            exact norm_sum_le Finset.univ
              (fun ρ : Near =>
                (ZD.xiOrderNat ρ.val : ℂ) *
                  (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)))
    _ ≤ ∑ ρ : Near, B * Real.log T₀ * w ρ.val := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact hterm ρ
    _ = B * Real.log T₀ * ∑ ρ : Near, w ρ.val := by
          rw [Finset.mul_sum]
    _ ≤ B * Real.log T₀ * (5 * Cw * Real.log T₀) := by
          gcongr
    _ = (5 * ((1 / Csep) + 2) * Cw) * (Real.log T₀) ^ 2 := by
          unfold B
          ring
    _ ≤ (5 * ((1 / Csep) + 2) * Cw) * (Real.log T) ^ 2 := by
          gcongr

/-- **Near-zero subtraction bound at good height**: `‖Σ_{|γ-T*|≤1} xiOrderNat(ρ) ·
(1/(σ+iT* - ρ) - 1/(2+iT* - ρ))‖ = O((log T)²)` at a good height T*.

At T* with separation `C/log T₀` (from `exists_good_height`):
- `|s - ρ| = |(σ-β) + i(T*-γ)| ≥ |T*-γ| ≥ C/log T₀` for ρ in the short window.
- `|s₀ - ρ| ≥ 2 - β ≥ 1` (since β < 1).
- Term ≤ `|2-σ|/(|s-ρ||s₀-ρ|) ≤ 2 · (log T₀) / C`.
- Count of near zeros ≤ `C_d · log T` (H10).
- Product: O((log T)²).

-/
theorem xi_logDeriv_sub_near_bound_at_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Ioo (0:ℝ) 1, ∀ T₀ : ℝ, 2 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1),
        ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) *
              (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
               1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
          ≤ C * (Real.log T) ^ 2 := by
  obtain ⟨Csep, hCsep_pos, hgood⟩ := exists_good_height_for_near_window
  obtain ⟨Cw, hCw_pos, hCw_bd⟩ := nontrivialZeros_short_window_weighted_count_bound
  refine ⟨5 * ((1 / Csep) + 2) * Cw, by positivity, ?_⟩
  intro σ hσ T₀ hT₀
  obtain ⟨T, hT_mem, hsep⟩ := hgood T₀ hT₀
  refine ⟨T, hT_mem, ?_⟩
  simpa [shortWindowFinset] using
    xi_logDeriv_sub_near_bound_of_sep
      ⟨hσ.1.le, by linarith [hσ.2]⟩ hT₀ hT_mem hCsep_pos hCw_pos hsep
      (fun U hU => by simpa [shortWindowFinset] using hCw_bd U hU)

/-- Local copy of the H10-side `ξ'/ξ(2+iT) = O(log T)` bound, kept non-private
to this file so the final Landau assembly can use it directly. -/
lemma xi_logDeriv_norm_log_bound_local :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ‖deriv riemannXi ((2 : ℂ) + (T : ℂ) * I) /
        riemannXi ((2 : ℂ) + (T : ℂ) * I)‖ ≤ C * Real.log T := by
  obtain ⟨Cζ, hCζ_nn, hCζ_bd⟩ :=
    ZD.WeilPositivity.Contour.logDerivZeta_bounded_of_right_of_one (3 / 2) (by norm_num)
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
    apply hCζ_bd
    rw [hs_re]
    norm_num
  have h_s_norm_ge : (2 : ℝ) ≤ ‖s‖ := by
    have h_normsq : Complex.normSq s = 4 + T ^ 2 := by
      rw [hs_def]
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    have h_norm_sq : ‖s‖ ^ 2 = Complex.normSq s := Complex.sq_norm _
    have h_ge_4 : (4 : ℝ) ≤ ‖s‖ ^ 2 := by
      rw [h_norm_sq, h_normsq]
      nlinarith [sq_nonneg T]
    nlinarith [norm_nonneg s]
  have h_bound_s_inv : ‖(1 : ℂ) / s‖ ≤ 1 := by
    have h_s_ne : s ≠ 0 := by
      intro heq
      have := congrArg Complex.re heq
      rw [hs_re] at this
      simp at this
    have h_s_pos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr h_s_ne
    rw [norm_div, norm_one, div_le_iff₀ h_s_pos, one_mul]
    linarith
  have h_sm1_re : (s - 1).re = 1 := by
    simp [hs_def]
    norm_num
  have h_sm1_ne : s - 1 ≠ 0 := by
    intro heq
    have := congrArg Complex.re heq
    rw [h_sm1_re] at this
    simp at this
  have h_sm1_norm_ge : (1 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 : ℝ) = |(s - 1).re| := by rw [h_sm1_re]; simp
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have h_bound_sm1_inv : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    have h_sm1_pos : (0 : ℝ) < ‖s - 1‖ := norm_pos_iff.mpr h_sm1_ne
    rw [norm_div, norm_one, div_le_iff₀ h_sm1_pos, one_mul]
    exact h_sm1_norm_ge
  have h_bound_gamma : ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * (1 + Real.log (1 + |T|)) := by
    rw [logDeriv_apply]
    exact hCΓ_bd T
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
    have h_1pT : 1 + T ≤ T ^ 2 := by nlinarith
    have h_pos : 0 < 1 + T := by linarith
    calc
      Real.log (1 + T) ≤ Real.log (T ^ 2) := Real.log_le_log h_pos h_1pT
      _ = 2 * Real.log T := by rw [Real.log_pow]; ring
  have h_ge_div : 1 ≤ Real.log T / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos, one_mul]
    exact Real.log_le_log (by norm_num) hT
  have h_one_plus : 1 + Real.log (1 + |T|) ≤ Real.log T / Real.log 2 + 2 * Real.log T := by
    linarith
  calc
    Cζ + 1 + 1 + CΓ * (1 + Real.log (1 + |T|))
      ≤ Cζ + 2 + CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) := by
          have h1 : CΓ * (1 + Real.log (1 + |T|)) ≤
              CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) :=
            mul_le_mul_of_nonneg_left h_one_plus hCΓ_nn
          linarith
    _ ≤ (Cζ + 2) * (Real.log T / Real.log 2) +
          CΓ * (Real.log T / Real.log 2 + 2 * Real.log T) := by
          have h_Cζ_nn : 0 ≤ Cζ + 2 := by linarith
          have : Cζ + 2 ≤ (Cζ + 2) * (Real.log T / Real.log 2) := by
            calc
              Cζ + 2 = (Cζ + 2) * 1 := by ring
              _ ≤ (Cζ + 2) * (Real.log T / Real.log 2) :=
                mul_le_mul_of_nonneg_left h_ge_div h_Cζ_nn
          linarith
    _ = ((Cζ + 2 + CΓ) / Real.log 2 + 2 * CΓ) * Real.log T := by field_simp; ring
    _ = K * Real.log T := by rw [hK_def]

/-- **Generalized H9** at `s = σ + iT` with σ ∈ (0,1), T ≥ 2, `s ∉ NontrivialZeros`.
The identity `ζ'/ζ = ξ'/ξ - 1/s - 1/(s-1) - logDeriv Γℝ` holds on the full
domain where ζ, Γℝ, s, s-1 are all nonzero; restricting to σ ∈ (0,1) just
requires `ζ(s) ≠ 0` (ensured by `s ∉ NontrivialZeros`) and `Γℝ(s) ≠ 0`
(ensured by `σ > 0`).

-/
lemma riemannZeta_logDeriv_eq_generalized
    (s : ℂ) (hs_ne0 : s ≠ 0) (hs_ne1 : s ≠ 1)
    (hζ_ne : riemannZeta s ≠ 0) (hΓ_ne : Complex.Gammaℝ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannXi s / riemannXi s -
        1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
  exact ZD.riemannZeta_logDeriv_eq_xi_minus_pole_minus_gammaℝ_of_ne
    s hs_ne0 hs_ne1 hζ_ne hΓ_ne

set_option maxHeartbeats 16000000 in
/-- **H11 main**: critical-strip Landau bound at good heights, via
σ=2 subtraction.

### Strategy

At `s = σ + iT*`, `s₀ = 2 + iT*` with σ ∈ (0,1) and T* a good height:

1. `ξ'/ξ(s) = ξ'/ξ(s₀) + (ξ'/ξ(s) - ξ'/ξ(s₀))`.
2. `|ξ'/ξ(s₀)| ≤ C·log T` from `xi_logDeriv_norm_log_bound` (H10 machinery).
3. `ξ'/ξ(s) - ξ'/ξ(s₀) = Σ xiOrderNat(ρ) · (1/(s-ρ) - 1/(s₀-ρ))` after
   cancellation of `1/ρ` (the Hadamard constant A also cancels):
   - Far piece (`|γ-T*|>1`): O(log T) via `xi_logDeriv_sub_far_bound`.
   - Near piece (`|γ-T*|≤1` at good T*): O((log T)²) via
     `xi_logDeriv_sub_near_bound_at_good_height`.
4. Combine: `|ξ'/ξ(s)| ≤ C·log T + C·(log T)² ≤ C'·(log T)²` for T ≥ 2.
5. Generalized H9 at s: `ζ'/ζ = ξ'/ξ - 1/s - 1/(s-1) - logDeriv Γℝ`.
   - `|1/s| ≤ 1/T ≤ 1/2`, `|1/(s-1)| ≤ 1`.
   - `|logDeriv Γℝ(s)| = O(log T)` via `Complex.digamma_vertical_log_bound`
     + Gammaℝ = π^(-s/2)·Γ(s/2) reflection.
6. Total: `|ζ'/ζ(s)| ≤ O((log T)²) + O(log T) = O((log T)²)`.

-/
theorem criticalStripLandau :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Ioo (0:ℝ) 1, ∀ T₀ : ℝ, 2 ≤ T₀ →
      ∃ T ∈ Set.Icc T₀ (T₀ + 1),
        ‖deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2 := by
  -- Extract constants from dependencies.
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  obtain ⟨Cfar, hCfar_pos, hCfar_bd⟩ := xi_logDeriv_sub_far_bound
  obtain ⟨Cxi0, hCxi0_nn, hCxi0_bd⟩ := xi_logDeriv_norm_log_bound_local
  obtain ⟨CΓ, hCΓ_pos, hCΓ_bd⟩ :=
    ZD.UniformGammaR.gammaR_logDeriv_uniform_criticalStrip
  -- Use the near-bound packaged theorem, but derive the separation/s ∉ NTZ fact
  -- separately via `exists_good_height_for_near_window`.
  obtain ⟨Csep, hCsep_pos, hgood⟩ := exists_good_height_for_near_window
  obtain ⟨Cw, hCw_pos, hCw_bd⟩ := nontrivialZeros_short_window_weighted_count_bound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Cnear from the near-bound lemma.
  set Cnear : ℝ := 5 * ((1 / Csep) + 2) * Cw with hCnear_def
  have hCnear_pos : 0 < Cnear := by rw [hCnear_def]; positivity
  -- Universal constant.
  set C_total : ℝ :=
    (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 + Cnear + 1 with hC_total_def
  have hC_total_pos : 0 < C_total := by
    rw [hC_total_def]
    have h1 : 0 ≤ (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 := by
      apply div_nonneg _ hlog2_pos.le
      linarith [hCxi0_nn, hCfar_pos.le, hCΓ_pos.le, norm_nonneg A]
    linarith [hCnear_pos]
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro σ hσ T₀ hT₀
  -- Get good height T with separation.
  obtain ⟨T, hT_mem, hsep⟩ := hgood T₀ hT₀
  refine ⟨T, hT_mem, ?_⟩
  have hT_pos : (0 : ℝ) < T := by linarith [hT_mem.1]
  have hT_ge_2 : (2 : ℝ) ≤ T := le_trans hT₀ hT_mem.1
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT_ge_2
  have hlogT_sq_pos : 0 < (Real.log T) ^ 2 := by positivity
  have hlogT₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  -- Near-bound at this T via the existing of-sep helper.
  have hNear_bd :
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ Cnear * (Real.log T) ^ 2 := by
    simpa [shortWindowFinset, Cnear, hCnear_def] using
      xi_logDeriv_sub_near_bound_of_sep
        ⟨hσ.1.le, by linarith [hσ.2]⟩ hT₀ hT_mem hCsep_pos hCw_pos hsep
        (fun U hU => by simpa [shortWindowFinset] using hCw_bd U hU)
  -- Far-bound at this T.
  have hFar_bd :
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ Cfar * Real.log T :=
    hCfar_bd σ ⟨hσ.1.le, by linarith [hσ.2]⟩ T hT_ge_2
  -- Set up s, s₀.
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I with hs₀_def
  have hs_re : s.re = σ := by simp [hs_def]
  have hs_im : s.im = T := by simp [hs_def]
  have hs₀_re : s₀.re = 2 := by simp [hs₀_def]
  have hs₀_im : s₀.im = T := by simp [hs₀_def]
  have hσ_pos : 0 < σ := hσ.1
  have hσ_lt : σ < 1 := hσ.2
  have hs_ne_0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hs_re] at this; simp at this; linarith
  have hs_ne_1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hs_re] at this; simp at this; linarith
  -- s ∉ NontrivialZeros via separation at good height.
  have hs_notMem : s ∉ NontrivialZeros := by
    intro hmem
    by_cases hnear : |s.im - T| ≤ 1
    · -- s is near T — separation forces |s.im - T| ≥ Csep/log T₀ > 0, but s.im = T ⟹ 0.
      have hsep_s : Csep / Real.log T₀ ≤ |s.im - T| := hsep s hmem hnear
      rw [hs_im] at hsep_s
      simp at hsep_s
      have h_div_pos : 0 < Csep / Real.log T₀ := div_pos hCsep_pos hlogT₀_pos
      linarith
    · -- s is far: |s.im - T| > 1, but s.im = T gives 0 ≤ 1, contradiction.
      apply hnear
      rw [hs_im]; simp
  -- ζ(s) ≠ 0 follows from s ∉ NTZ.
  have hζ_s_ne : riemannZeta s ≠ 0 := by
    intro hz
    exact hs_notMem ⟨by rw [hs_re]; exact hσ_pos, by rw [hs_re]; exact hσ_lt, hz⟩
  -- Γℝ(s) ≠ 0 from Re(s) > 0.
  have hΓ_s_ne : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs_re]; exact hσ_pos)
  -- s₀ = 2+iT, Re = 2 > 1, so s₀ ∉ NTZ.
  have hs₀_notMem : s₀ ∉ NontrivialZeros := by
    intro hmem
    have : s₀.re < 1 := hmem.2.1
    rw [hs₀_re] at this; norm_num at this
  -- Bound ‖ξ'/ξ(s₀)‖ via the σ=2 bound.
  have hξ_s₀_bd :
      ‖deriv riemannXi s₀ / riemannXi s₀‖ ≤ Cxi0 * Real.log T :=
    hCxi0_bd T hT_ge_2
  -- Key identity: `ξ'/ξ(s) - ξ'/ξ(s₀) = near_sub + far_sub`. Follows from H8
  -- applied at both s and s₀: the Hadamard constant `A` and `1/ρ` terms
  -- cancel term-by-term in the subtraction.
  -- Formalization uses `xi_logDeriv_short_window_decomp` at both points.
  have hxi_s_eq := hA s hs_notMem
  have hxi_s₀_eq := hA s₀ hs₀_notMem
  -- Summabilities needed for tsum_sub.
  have h_summ_s :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) :=
    summable_weighted_partial_fraction_local hs_notMem
  have h_summ_s₀ :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) :=
    summable_weighted_partial_fraction_local hs₀_notMem
  -- Diff of tsums = tsum of diffs.
  have h_tsum_sub :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    rw [← Summable.tsum_sub h_summ_s h_summ_s₀]
    apply tsum_congr
    intro ρ; ring
  -- Final bound chain. Use H9 to convert ξ'/ξ → ζ'/ζ, then bound each piece.
  have hζ_s_eq :
      deriv riemannZeta s / riemannZeta s =
        deriv riemannXi s / riemannXi s -
          1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s :=
    riemannZeta_logDeriv_eq_generalized s hs_ne_0 hs_ne_1 hζ_s_ne hΓ_s_ne
  -- Bound ‖1/s‖ ≤ 1/T ≤ 1/log 2 · log T
  have h_inv_s : ‖(1 : ℂ) / s‖ ≤ 1 := by
    have h_s_re_pos : 0 < s.re := by rw [hs_re]; exact hσ_pos
    have h_s_norm_ge : (1 : ℝ) ≤ ‖s‖ := by
      have h_normSq : Complex.normSq s = σ^2 + T^2 := by
        rw [hs_def]
        simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im]; ring
      have h_norm_sq : ‖s‖^2 = Complex.normSq s := Complex.sq_norm _
      have h_ge_1 : (1 : ℝ) ≤ ‖s‖^2 := by
        rw [h_norm_sq, h_normSq]
        nlinarith [sq_nonneg σ, sq_nonneg T, hT_ge_2]
      nlinarith [norm_nonneg s]
    have h_s_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le zero_lt_one h_s_norm_ge
    rw [norm_div, norm_one, div_le_iff₀ h_s_pos]; linarith
  -- Bound ‖1/(s-1)‖ ≤ 1
  have h_sm1_re : (s - 1).re = σ - 1 := by simp [hs_def]
  have h_sm1_im : (s - 1).im = T := by simp [hs_def]
  have h_sm1_ne : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [h_sm1_im] at this; simp at this; linarith
  have h_inv_sm1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    have h_sm1_norm_ge : (1 : ℝ) ≤ ‖s - 1‖ := by
      have h_normSq : Complex.normSq (s - 1) = (σ - 1)^2 + T^2 := by
        rw [hs_def]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      have h_norm_sq : ‖s - 1‖^2 = Complex.normSq (s - 1) := Complex.sq_norm _
      have h_ge_1 : (1 : ℝ) ≤ ‖s - 1‖^2 := by
        rw [h_norm_sq, h_normSq]
        nlinarith [sq_nonneg (σ-1), sq_nonneg T, hT_ge_2]
      nlinarith [norm_nonneg (s - 1)]
    have h_sm1_pos : (0 : ℝ) < ‖s - 1‖ := lt_of_lt_of_le zero_lt_one h_sm1_norm_ge
    rw [norm_div, norm_one, div_le_iff₀ h_sm1_pos]; linarith
  -- Bound ‖logDeriv Γℝ(s)‖ ≤ CΓ·log T via uniform bound.
  have h_Γ_s_bd : ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * Real.log T := by
    simpa [hs_def] using hCΓ_bd σ hσ T hT_ge_2
  -- Apply short-window decomp at s and s₀, SAME A' existential witness.
  obtain ⟨A', hA'⟩ := xi_logDeriv_short_window_decomp
  have hdecomp_s := hA' s hs_notMem
  have hdecomp_s₀ := hA' s₀ hs₀_notMem
  -- Rewrite s₀ decomp using s.im = s₀.im = T so the subtype predicates match.
  have h_im_eq : s.im = s₀.im := by rw [hs_im, hs₀_im]
  have hdecomp_s₀' :
      deriv riemannXi s₀ / riemannXi s₀ =
        A' +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    rw [h_im_eq]; exact hdecomp_s₀
  -- ξ'/ξ(s) - ξ'/ξ(s₀) by subtracting the two decomps; A' cancels.
  have h_xi_diff :
      deriv riemannXi s / riemannXi s - deriv riemannXi s₀ / riemannXi s₀ =
        ((∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
         (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val))) +
        ((∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
         (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val))) := by
    rw [hdecomp_s, hdecomp_s₀']; ring
  -- Rewrite s.im as T in subtypes for matching hNear_bd/hFar_bd.
  have h_im_sub : s.im = T := hs_im
  -- Summability of near/far-subtype restrictions (restriction of summable series).
  have h_summ_near_s : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    have h_summable : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
      exact summable_weighted_partial_fraction_local hs_notMem
    convert h_summable.comp_injective _;
    rotate_left;
    exact fun x => ⟨ x.val, x.property.1 ⟩;
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h;
    · rfl -- restriction of summable_weighted_partial_fraction_local
  have h_summ_near_s₀ : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs₀_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_summ_far_s : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  have h_summ_far_s₀ : Summable
      (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1} =>
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) := by
    convert (summable_weighted_partial_fraction_local hs₀_notMem).comp_injective _
    rotate_left
    exact fun x => ⟨x.val, x.property.1⟩
    · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h
    · rfl
  -- Near tsum sub = tsum of differences
  have h_near_sub :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    rw [← Summable.tsum_sub h_summ_near_s h_summ_near_s₀]
    apply tsum_congr; intro ρ; ring
  -- Far tsum sub = tsum of differences
  have h_far_sub :
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) -
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s₀ - ρ.val) + 1 / ρ.val)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)) := by
    rw [← Summable.tsum_sub h_summ_far_s h_summ_far_s₀]
    apply tsum_congr; intro ρ; ring
  -- ξ'/ξ(s) = ξ'/ξ(s₀) + near_diff + far_diff
  have h_xi_s_eq :
      deriv riemannXi s / riemannXi s =
        deriv riemannXi s₀ / riemannXi s₀ +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))) +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))) := by
    have h1 := h_xi_diff
    rw [h_near_sub, h_far_sub] at h1
    linear_combination h1
  -- Rewrite hNear_bd and hFar_bd to use s.im instead of T
  rw [← hs_im] at hNear_bd hFar_bd
  -- Step 1: Bound ‖ξ'/ξ(s)‖ via triangle inequality with s₀ subtraction.
  have h_xi_s_norm : ‖deriv riemannXi s / riemannXi s‖ ≤
      Cxi0 * Real.log T + Cnear * (Real.log T) ^ 2 + Cfar * Real.log T := by
    rw [h_xi_s_eq]
    have h1 := norm_add_le (deriv riemannXi s₀ / riemannXi s₀ +
        (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val))))
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)))
    have h2 := norm_add_le (deriv riemannXi s₀ / riemannXi s₀)
      (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ |ρ.im - s.im| ≤ 1},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) - 1 / (s₀ - ρ.val)))
    grind
  -- Step 2: Tighter bounds on 1/s and 1/(s-1): use ‖s‖ ≥ T, ‖s-1‖ ≥ T
  have h_s_norm_ge_T : T ≤ ‖s‖ := by
    have : T = |s.im| := by rw [hs_im]; exact (abs_of_pos hT_pos).symm
    rw [this]; exact Complex.abs_im_le_norm s
  have h_sm1_norm_ge_T : T ≤ ‖s - 1‖ := by
    have him : (s - 1).im = T := by simp [hs_def]
    have : T = |(s - 1).im| := by rw [him]; exact (abs_of_pos hT_pos).symm
    rw [this]; exact Complex.abs_im_le_norm (s - 1)
  have h_inv_s_T : ‖(1 : ℂ) / s‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hT_pos h_s_norm_ge_T
  have h_inv_sm1_T : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / T := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hT_pos h_sm1_norm_ge_T
  -- Step 3: Key absorbing inequality: logT ≤ logT²/log 2
  have h_logT_absorb : Real.log T ≤ (Real.log T) ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    nlinarith [hlogT_ge_log2]
  -- Step 4: 1/T ≤ logT²/log 2
  have h_inv_T_absorb : 1 / T ≤ (Real.log T) ^ 2 / Real.log 2 := by
    -- Since $T \geq 2$, we have $1/T \leq 1/2$.
    have h_inv_T_le_half : 1 / T ≤ 1 / 2 := by
      gcongr;
    -- Since $1/2 \leq \log T$ and $\log T \leq \log T^2 / \log 2$, we can combine these inequalities.
    have h_combined : 1 / 2 ≤ Real.log T ∧ Real.log T ≤ Real.log T ^ 2 / Real.log 2 := by
      exact ⟨ by have := Real.log_two_gt_d9; norm_num1 at *; linarith, h_logT_absorb ⟩;
    exact le_trans h_inv_T_le_half h_combined.1 |> le_trans <| h_combined.2
  -- Step 5: Triangle inequality for ζ'/ζ
  have h_zeta_tri : ‖deriv riemannXi s / riemannXi s - 1 / s - 1 / (s - 1) -
      logDeriv Complex.Gammaℝ s‖ ≤
      ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
        ‖logDeriv Complex.Gammaℝ s‖ := by
    -- Apply the triangle inequality to the four terms.
    have h_triangle : ∀ a b c d : ℂ, ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      exact fun a b c d => by linarith [ norm_sub_le a b, norm_sub_le ( a - b ) c, norm_sub_le ( a - b - c ) d ] ;
    -- Apply the triangle inequality to the four terms using the hypothesis h_triangle.
    apply h_triangle
  -- Step 6: Final assembly
  rw [hζ_s_eq]
  have h_total : ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C_total * (Real.log T) ^ 2 := by
    have hbd1 : ‖(1 : ℂ) / s‖ ≤ (Real.log T) ^ 2 / Real.log 2 :=
      le_trans h_inv_s_T h_inv_T_absorb
    have hbd2 : ‖(1 : ℂ) / (s - 1)‖ ≤ (Real.log T) ^ 2 / Real.log 2 :=
      le_trans h_inv_sm1_T h_inv_T_absorb
    have hbd3 : ‖deriv riemannXi s / riemannXi s‖ ≤
        ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by
      calc ‖deriv riemannXi s / riemannXi s‖
          ≤ Cxi0 * Real.log T + Cnear * (Real.log T) ^ 2 + Cfar * Real.log T := h_xi_s_norm
        _ ≤ Cxi0 * ((Real.log T) ^ 2 / Real.log 2) +
            Cnear * (Real.log T) ^ 2 +
            Cfar * ((Real.log T) ^ 2 / Real.log 2) := by
          nlinarith [h_logT_absorb, hCxi0_nn, hCfar_pos.le]
        _ = ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by ring
    have hbd4 : ‖logDeriv Complex.Gammaℝ s‖ ≤
        CΓ / Real.log 2 * (Real.log T) ^ 2 := by
      calc ‖logDeriv Complex.Gammaℝ s‖ ≤ CΓ * Real.log T := h_Γ_s_bd
        _ ≤ CΓ * ((Real.log T) ^ 2 / Real.log 2) := by
          nlinarith [h_logT_absorb, hCΓ_pos]
        _ = CΓ / Real.log 2 * (Real.log T) ^ 2 := by ring
    calc ‖deriv riemannXi s / riemannXi s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖logDeriv Complex.Gammaℝ s‖
        ≤ ((Cxi0 + Cfar) / Real.log 2 + Cnear) * (Real.log T) ^ 2 +
          (Real.log T) ^ 2 / Real.log 2 +
          (Real.log T) ^ 2 / Real.log 2 +
          CΓ / Real.log 2 * (Real.log T) ^ 2 := by linarith [hbd1, hbd2, hbd3, hbd4]
      _ = ((Cxi0 + Cfar + CΓ + 2) / Real.log 2 + Cnear) * (Real.log T) ^ 2 := by ring
      _ ≤ C_total * (Real.log T) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hlogT_sq_pos.le
          rw [hC_total_def]
          have hA_nn := norm_nonneg A
          have h_extra : 0 ≤ ‖A‖ / Real.log 2 := div_nonneg hA_nn hlog2_pos.le
          have h_sum : (Cxi0 + Cfar + CΓ + ‖A‖ + 2) / Real.log 2 =
              (Cxi0 + Cfar + CΓ + 2) / Real.log 2 + ‖A‖ / Real.log 2 := by ring
          linarith [h_extra, h_sum]
  linarith [h_zeta_tri, h_total]

end ZD
