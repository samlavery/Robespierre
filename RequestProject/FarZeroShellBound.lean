import Mathlib

import RequestProject.XiShortWindowCount
import RequestProject.XiOrderSummable
import RequestProject.ZeroCountJensen
import RequestProject.ZetaBound

/-- Nontrivial zeros of the Riemann zeta function.
    Membership gives `0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0`. -/
def NontrivialZeros : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

/-- **Gram bound**: every nontrivial zero has `|ρ.im| ≥ 2`.
    Discharged via `ZetaBound.riemannZeta_nontrivial_zero_im_ge_two`. -/
theorem NontrivialZeros_im_ge_two {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 2 ≤ |ρ.im| := by
  apply riemannZeta_nontrivial_zero_im_ge_two hρ.2.2
  intro n h
  -- ρ = -2*(n+1) would give Re ρ = -2*(n+1) ≤ -2, but ρ.re > 0. Contradict.
  have h_re : ρ.re = -2 * ((n : ℝ) + 1) := by
    have := congrArg Complex.re h
    simp at this
    convert this using 1
    push_cast; ring
  have hρ_re_pos : 0 < ρ.re := hρ.1
  have : (0 : ℝ) < -2 * ((n : ℝ) + 1) := h_re ▸ hρ_re_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-!
# Far-zero subtraction bound via dyadic shell decomposition

Proves the tracked sorry `xi_logDeriv_sub_far_bound` from `CriticalStripLandau.lean`:

For `σ ∈ (0,1)`, `T ≥ 2`:
  ‖∑_{|γ-T|>1} xiOrderNat(ρ) · (1/((σ+iT)-ρ) - 1/((2+iT)-ρ))‖ ≤ C · log T

Strategy:
1. Tail (`‖ρ‖ ≥ 2T+5`): pointwise bound `8 n(ρ)/‖ρ‖²` + summability of
   `summable_xiOrderNat_div_norm_sq_nontrivialZeros` → O(1) contribution.
2. Body (`‖ρ‖ < 2T+5`, `|γ-T|>1`): finite set, partition by shells
   `S_k^± = {ρ : γ ∈ T±[k, k+1)}` for integer `k ≥ 1`; per-shell weighted count
   via H10 at shifted center; per-term bound `2 n(ρ)/k²` via `|γ-T| ≥ k`;
   geometric-series sum.
-/

open Complex

noncomputable section

namespace ZD
namespace FarShell

/-! ### Private helper copies (to keep the new file self-contained) -/

/-- `1/(s-ρ) - 1/(s₀-ρ) = (2-σ)/((s-ρ)(s₀-ρ))` at fixed height `T`. -/
private lemma one_div_sub_one_div_formula
    (σ : ℝ) (T : ℝ) (ρ : ℂ) (hρ_s : (σ : ℂ) + (T : ℂ) * I - ρ ≠ 0)
    (hρ_s₀ : (2 : ℂ) + (T : ℂ) * I - ρ ≠ 0) :
    (1 : ℂ) / ((σ : ℂ) + (T : ℂ) * I - ρ) - 1 / ((2 : ℂ) + (T : ℂ) * I - ρ) =
    ((2 - σ : ℝ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I - ρ) * ((2 : ℂ) + (T : ℂ) * I - ρ)) := by
  field_simp
  push_cast
  ring

/-- Per-term bound `2 n(ρ)/|γ-T|²` for far zeros. -/
private lemma far_sub_term_norm_le_gap_sq
    (σ T : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 2)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hfar : ¬ |ρ.im - T| ≤ 1) :
    ‖(ZD.xiOrderNat ρ : ℂ) *
        (1 / ((σ : ℂ) + (T : ℂ) * I - ρ) -
         1 / ((2 : ℂ) + (T : ℂ) * I - ρ))‖
      ≤ 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hgap_gt_one : 1 < |ρ.im - T| := by
    by_contra h; exact hfar (not_lt.mp h)
  have hgap_pos : 0 < |ρ.im - T| := lt_trans zero_lt_one hgap_gt_one
  have hs_ne : s - ρ ≠ 0 := by
    intro hs_eq
    have him : T - ρ.im = 0 := by simpa [s] using congrArg Complex.im hs_eq
    have hsub : ρ.im - T = 0 := by linarith
    have : |ρ.im - T| = 0 := by simp [hsub]
    linarith
  have hs₀_ne : s₀ - ρ ≠ 0 := by
    intro hs_eq
    have hre := congrArg Complex.re hs_eq
    simp [s₀] at hre
    linarith [hρ.2.1]
  have hsgap : |ρ.im - T| ≤ ‖s - ρ‖ := by
    calc |ρ.im - T| = |(s - ρ).im| := by simp [s, abs_sub_comm]
      _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
  have hs₀gap : |ρ.im - T| ≤ ‖s₀ - ρ‖ := by
    calc |ρ.im - T| = |(s₀ - ρ).im| := by simp [s₀, abs_sub_comm]
      _ ≤ ‖s₀ - ρ‖ := Complex.abs_im_le_norm _
  have hnum_le : ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2 := by
    have hσ_nonneg : 0 ≤ σ := hσ.1
    have hσ_le : σ ≤ 2 := hσ.2
    have hreal : |2 - σ| ≤ 2 := by rw [abs_of_nonneg] <;> linarith
    change ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2
    rw [Complex.norm_real]; exact hreal
  have hden_ge : |ρ.im - T| ^ 2 ≤ ‖s - ρ‖ * ‖s₀ - ρ‖ := by nlinarith
  have hdiv : ‖((2 - σ : ℝ) : ℂ)‖ / (‖s - ρ‖ * ‖s₀ - ρ‖) ≤ 2 / |ρ.im - T| ^ 2 := by
    have hden_pos : 0 < ‖s - ρ‖ * ‖s₀ - ρ‖ := by positivity
    have hgap_sq_pos : 0 < |ρ.im - T| ^ 2 := by positivity
    rw [div_le_div_iff₀ hden_pos hgap_sq_pos]; nlinarith
  rw [one_div_sub_one_div_formula σ T ρ hs_ne hs₀_ne, norm_mul, Complex.norm_natCast, norm_div,
    norm_mul]
  have hxi_nonneg : 0 ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hdiv hxi_nonneg
  simpa [s, s₀, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

/-- Per-term bound `8 n(ρ)/‖ρ‖²` for zeros with `‖ρ‖ ≥ 2T+5`. -/
private lemma far_sub_term_norm_le_norm_sq
    (σ T : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 2) (hT_nonneg : 0 ≤ T)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hρ_norm : 2 * T + 5 ≤ ‖ρ‖) :
    ‖(ZD.xiOrderNat ρ : ℂ) *
        (1 / ((σ : ℂ) + (T : ℂ) * I - ρ) -
         1 / ((2 : ℂ) + (T : ℂ) * I - ρ))‖
      ≤ 8 * (ZD.xiOrderNat ρ : ℝ) / ‖ρ‖ ^ 2 := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  set s₀ : ℂ := (2 : ℂ) + (T : ℂ) * I
  have hs_norm_le : ‖s‖ ≤ T + 2 := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = σ + T := by
        have hσ_nonneg : 0 ≤ σ := hσ.1
        simp [s, abs_of_nonneg hσ_nonneg, abs_of_nonneg hT_nonneg]
      _ ≤ T + 2 := by linarith [hσ.2]
  have hs₀_norm_le : ‖s₀‖ ≤ T + 2 := by
    calc ‖s₀‖ ≤ |s₀.re| + |s₀.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 2 + T := by simp [s₀, abs_of_nonneg hT_nonneg]
      _ = T + 2 := by ring
  have hρ_pos : 0 < ‖ρ‖ := by
    have : 0 < 2 * T + 5 := by linarith
    exact lt_of_lt_of_le this hρ_norm
  have hhalf_s : ‖s‖ ≤ ‖ρ‖ / 2 := by
    have : T + 2 ≤ ‖ρ‖ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
    exact hs_norm_le.trans this
  have hhalf_s₀ : ‖s₀‖ ≤ ‖ρ‖ / 2 := by
    have : T + 2 ≤ ‖ρ‖ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
    exact hs₀_norm_le.trans this
  have hs_ne : s - ρ ≠ 0 := by
    have hpos : 0 < ‖ρ‖ / 2 := by positivity
    intro hs_eq
    have hzero : ‖s - ρ‖ = 0 := by simpa [hs_eq]
    have hlower : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
      calc ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s‖ := by linarith
        _ ≤ ‖ρ - s‖ := norm_sub_norm_le ρ s
        _ = ‖s - ρ‖ := by rw [norm_sub_rev]
    linarith
  have hs₀_ne : s₀ - ρ ≠ 0 := by
    have hpos : 0 < ‖ρ‖ / 2 := by positivity
    intro hs_eq
    have hzero : ‖s₀ - ρ‖ = 0 := by simpa [hs_eq]
    have hlower : ‖ρ‖ / 2 ≤ ‖s₀ - ρ‖ := by
      calc ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s₀‖ := by linarith
        _ ≤ ‖ρ - s₀‖ := norm_sub_norm_le ρ s₀
        _ = ‖s₀ - ρ‖ := by rw [norm_sub_rev]
    linarith
  have hsgap : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    calc ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s‖ := by linarith
      _ ≤ ‖ρ - s‖ := norm_sub_norm_le ρ s
      _ = ‖s - ρ‖ := by rw [norm_sub_rev]
  have hs₀gap : ‖ρ‖ / 2 ≤ ‖s₀ - ρ‖ := by
    calc ‖ρ‖ / 2 ≤ ‖ρ‖ - ‖s₀‖ := by linarith
      _ ≤ ‖ρ - s₀‖ := norm_sub_norm_le ρ s₀
      _ = ‖s₀ - ρ‖ := by rw [norm_sub_rev]
  have hnum_le : ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2 := by
    have hσ_nonneg : 0 ≤ σ := hσ.1
    have hσ_le : σ ≤ 2 := hσ.2
    have hreal : |2 - σ| ≤ 2 := by rw [abs_of_nonneg] <;> linarith
    change ‖((2 - σ : ℝ) : ℂ)‖ ≤ 2
    rw [Complex.norm_real]; exact hreal
  have hden_ge : ‖ρ‖ ^ 2 / 4 ≤ ‖s - ρ‖ * ‖s₀ - ρ‖ := by nlinarith
  have hdiv : ‖((2 - σ : ℝ) : ℂ)‖ / (‖s - ρ‖ * ‖s₀ - ρ‖) ≤ 8 / ‖ρ‖ ^ 2 := by
    have hhalf_pos : 0 < ‖ρ‖ / 2 := by positivity
    have hs_pos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hhalf_pos hsgap
    have hs₀_pos : 0 < ‖s₀ - ρ‖ := lt_of_lt_of_le hhalf_pos hs₀gap
    have hden_pos : 0 < ‖s - ρ‖ * ‖s₀ - ρ‖ := mul_pos hs_pos hs₀_pos
    have hnorm_sq_pos : 0 < ‖ρ‖ ^ 2 := by positivity
    rw [div_le_div_iff₀ hden_pos hnorm_sq_pos]; nlinarith
  rw [one_div_sub_one_div_formula σ T ρ hs_ne hs₀_ne, norm_mul, Complex.norm_natCast, norm_div,
    norm_mul]
  have hxi_nonneg : 0 ≤ (ZD.xiOrderNat ρ : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hdiv hxi_nonneg
  simpa [s, s₀, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

/-! ### Shell finsets -/

/-- Shifted H10 finset at center `c` (of arbitrary real value): nontrivial zeros
ρ in the ball of radius `c+1` with `|γ - c| ≤ 1`. -/
private def windowFinset (c : ℝ) : Finset ℂ :=
  ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (c + 1)).toFinset.filter
    (fun ρ => |ρ.im - c| ≤ 1))

/-- Membership criterion for `windowFinset`. -/
private lemma mem_windowFinset {c : ℝ} (hc : 0 ≤ c) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) (hρ_near : |ρ.im - c| ≤ 1)
    (hρ_norm : ‖ρ‖ ≤ c + 1) :
    ρ ∈ windowFinset c := by
  unfold windowFinset
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  refine ⟨⟨hρ, ?_⟩, hρ_near⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hρ_norm

/-- Ball-based finset: all nontrivial zeros with `‖ρ‖ ≤ R`. -/
private def ballFinset (R : ℝ) : Finset ℂ :=
  (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite R).toFinset

private lemma mem_ballFinset {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) (hρ_norm : ‖ρ‖ ≤ R) :
    ρ ∈ ballFinset R := by
  unfold ballFinset
  rw [Set.Finite.mem_toFinset]
  exact ⟨hρ, by rw [Metric.mem_closedBall, dist_zero_right]; exact hρ_norm⟩

/-! ### Shell bound helpers -/

/-- Helper: for `c ≥ 0`, zeros with `|γ - c| ≤ 1` and `β ∈ (0,1)` satisfy
`‖ρ‖ ≤ c + 2` (since `β² < 1` and `γ² ≤ (c+1)²`, so `‖ρ‖² < 1 + (c+1)² ≤ (c+2)²`). -/
private lemma norm_le_of_im_near
    {c : ℝ} (hc_nonneg : 0 ≤ c) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hρ_near : |ρ.im - c| ≤ 1) : ‖ρ‖ ≤ c + 2 := by
  have hβ_pos : 0 < ρ.re := hρ.1
  have hβ_lt : ρ.re < 1 := hρ.2.1
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by nlinarith
  have hγ_abs : |ρ.im| ≤ c + 1 := by
    have h_abs_tri : |ρ.im| ≤ |ρ.im - c| + |c| := by
      calc |ρ.im| = |(ρ.im - c) + c| := by ring_nf
        _ ≤ |ρ.im - c| + |c| := abs_add_le _ _
    have : |c| = c := abs_of_nonneg hc_nonneg
    linarith
  have hγ_sq : ρ.im ^ 2 ≤ (c+1) ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have h_c_nn : 0 ≤ c + 1 := by linarith
    have := mul_self_le_mul_self h_abs_nn hγ_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  have h_norm_sq_le : ‖ρ‖ ^ 2 ≤ (c + 2) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    nlinarith
  have hcp2_pos : (0 : ℝ) < c + 2 := by linarith
  nlinarith [norm_nonneg ρ, sq_nonneg (‖ρ‖ - (c+2))]

/-- Stronger norm bound: for NTZ ρ with γ ∈ [c-1, c+1] and β ∈ (0,1), `‖ρ‖ < c+2` (strict). -/
private lemma norm_lt_of_im_near
    {c : ℝ} (hc_nonneg : 0 ≤ c) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hρ_near : |ρ.im - c| ≤ 1) : ‖ρ‖ < c + 2 := by
  have hβ_pos : 0 < ρ.re := hρ.1
  have hβ_lt : ρ.re < 1 := hρ.2.1
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by nlinarith
  have hγ_abs : |ρ.im| ≤ c + 1 := by
    have h_abs_tri : |ρ.im| ≤ |ρ.im - c| + |c| := by
      calc |ρ.im| = |(ρ.im - c) + c| := by ring_nf
        _ ≤ |ρ.im - c| + |c| := abs_add_le _ _
    have : |c| = c := abs_of_nonneg hc_nonneg
    linarith
  have hγ_sq : ρ.im ^ 2 ≤ (c+1) ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have := mul_self_le_mul_self h_abs_nn hγ_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  have h_norm_sq_lt : ‖ρ‖ ^ 2 < (c + 2) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    nlinarith
  have hcp2_pos : (0 : ℝ) < c + 2 := by linarith
  have h_sq_diff_pos : 0 < (c+2)^2 - ‖ρ‖^2 := by linarith
  have h_factored : (c+2)^2 - ‖ρ‖^2 = ((c+2) - ‖ρ‖) * ((c+2) + ‖ρ‖) := by ring
  have h_sum_pos : 0 < (c+2) + ‖ρ‖ := by linarith [norm_nonneg ρ]
  nlinarith [norm_nonneg ρ, h_factored, h_sq_diff_pos, h_sum_pos]

/-- Helper: if ρ is NTZ with γ ∈ [T+k, T+k+1] (width-1 upper shell),
ρ ∈ windowFinset (T+k+1). -/
private lemma upper_shell_in_windowFinset
    {T : ℝ} (hT : 2 ≤ T) (k : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) (hρ_im_lo : T + k ≤ ρ.im) (hρ_im_hi : ρ.im ≤ T + k + 1) :
    ρ ∈ windowFinset (T + k + 1) := by
  have h_center_ge : (0 : ℝ) ≤ T + k + 1 := by
    have h1 : (0 : ℝ) ≤ T := by linarith
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hρ_near : |ρ.im - (T + k + 1)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  -- Establish ‖ρ‖ ≤ T+k+2 using the narrow range γ ∈ [T+k, T+k+1].
  apply mem_windowFinset h_center_ge hρ hρ_near
  have hβ_pos : 0 < ρ.re := hρ.1
  have hβ_lt : ρ.re < 1 := hρ.2.1
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by nlinarith
  -- |ρ.im| ≤ T+k+1 (since 0 ≤ T+k ≤ γ ≤ T+k+1).
  have hγ_nn : 0 ≤ ρ.im := by linarith
  have hγ_abs : |ρ.im| ≤ T + k + 1 := by rw [abs_of_nonneg hγ_nn]; linarith
  have hγ_sq_le : ρ.im ^ 2 ≤ (T+k+1) ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have := mul_self_le_mul_self h_abs_nn hγ_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  -- ‖ρ‖² < 1 + (T+k+1)² ≤ (T+k+2)²
  have h_ineq : ‖ρ‖ ^ 2 < (T + k + 2) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    nlinarith
  have h_pos : (0 : ℝ) < T + k + 2 := by linarith
  nlinarith [norm_nonneg ρ, sq_nonneg (‖ρ‖ - (T+k+2))]

/-- Helper: if ρ is NTZ with γ ∈ [T-k-1, T-k] (width-1 lower shell) and
`k ≤ T-2` (so center `T-k ≥ 2`), then ρ ∈ windowFinset (T-k). -/
private lemma lower_shell_in_windowFinset
    {T : ℝ} (hT : 2 ≤ T) (k : ℕ) (hk_upper : (k : ℝ) ≤ T - 2) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros)
    (hρ_im_lo : T - k - 1 ≤ ρ.im) (hρ_im_hi : ρ.im ≤ T - k) :
    ρ ∈ windowFinset (T - k) := by
  have h_center_ge : (0 : ℝ) ≤ T - k := by linarith
  have hρ_near : |ρ.im - (T - k)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  apply mem_windowFinset h_center_ge hρ hρ_near
  have hβ_pos : 0 < ρ.re := hρ.1
  have hβ_lt : ρ.re < 1 := hρ.2.1
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by nlinarith
  -- |ρ.im| ≤ T-k since 0 ≤ T-k-1 ≤ γ ≤ T-k (with T-k ≥ 2 > 0).
  have hTk_ge : (1 : ℝ) ≤ T - k - 1 := by linarith
  have hγ_nn : 0 ≤ ρ.im := by linarith
  have hγ_abs : |ρ.im| ≤ T - k := by rw [abs_of_nonneg hγ_nn]; linarith
  have hγ_sq_le : ρ.im ^ 2 ≤ (T-k) ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have hTk_nn : 0 ≤ T - k := by linarith
    have := mul_self_le_mul_self h_abs_nn hγ_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  -- ‖ρ‖² < 1 + (T-k)² ≤ (T-k+1)² since 1 ≤ 2(T-k)+1 (for T-k ≥ 0).
  have h_ineq : ‖ρ‖ ^ 2 < (T - k + 1) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    nlinarith
  have h_pos : (0 : ℝ) < T - k + 1 := by linarith
  nlinarith [norm_nonneg ρ, sq_nonneg (‖ρ‖ - (T-k+1))]

/-- Helper: if ρ is NTZ with γ ∈ [T-k-1, T-k] for any k ≥ 1, then ρ is
in `ballFinset (T + k + 2)` (using a generous ball that works for all k). -/
private lemma lower_shell_in_ballFinset
    {T : ℝ} (hT_nonneg : 0 ≤ T) (k : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros)
    (hρ_im_lo : T - k - 1 ≤ ρ.im) (hρ_im_hi : ρ.im ≤ T - k) :
    ρ ∈ ballFinset (T + k + 2) := by
  apply mem_ballFinset hρ
  have hβ_pos : 0 < ρ.re := hρ.1
  have hβ_lt : ρ.re < 1 := hρ.2.1
  have hβ_sq_lt : ρ.re ^ 2 < 1 := by nlinarith
  have hγ_abs : |ρ.im| ≤ T + k + 1 := by
    -- |γ - T| ≤ k + 1 (from γ ∈ [T-k-1, T-k]), so |γ| ≤ |γ-T| + T ≤ (k+1) + T.
    have hγ_minus_T_abs : |ρ.im - T| ≤ k + 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |ρ.im| = |(ρ.im - T) + T| := by ring_nf
      _ ≤ |ρ.im - T| + |T| := abs_add_le _ _
      _ ≤ (k + 1) + T := by
          have : |T| = T := abs_of_nonneg hT_nonneg
          linarith
      _ = T + k + 1 := by ring
  have hγ_sq_le : ρ.im ^ 2 ≤ (T + k + 1) ^ 2 := by
    have h_abs_nn : 0 ≤ |ρ.im| := abs_nonneg _
    have hbd_nn : 0 ≤ T + k + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have := mul_self_le_mul_self h_abs_nn hγ_abs
    rw [show |ρ.im| * |ρ.im| = ρ.im^2 from by rw [← sq, sq_abs]] at this
    nlinarith
  have h_normSq : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_norm_sq_eq : ‖ρ‖ ^ 2 = Complex.normSq ρ := Complex.sq_norm _
  have h_ineq : ‖ρ‖ ^ 2 < (T + k + 2) ^ 2 := by
    rw [h_norm_sq_eq, h_normSq]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_pos : (0 : ℝ) < T + k + 2 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith [norm_nonneg ρ, sq_nonneg (‖ρ‖ - (T+k+2))]

/-! ### Basel-type dyadic majorant for shell sums -/

/-- `2/((k+1)(k+2)) = 2/(k+1) - 2/(k+2)`. Telescopes. -/
private lemma two_over_telescopes (k : ℕ) :
    2 / ((k + 1 : ℝ) * (k + 2 : ℝ)) =
      2 / (k + 1 : ℝ) - 2 / (k + 2 : ℝ) := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  field_simp
  ring

/-- Exact telescope: `∑_{k<K} 2/((k+1)(k+2)) = 2 - 2/(K+1)`. -/
private lemma sum_two_over_telescopes_exact (K : ℕ) :
    (∑ k ∈ Finset.range K, 2 / ((k + 1 : ℝ) * (k + 2 : ℝ)))
      = 2 - 2 / (K + 1 : ℝ) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, two_over_telescopes K]
      have hK1 : (0 : ℝ) < K + 1 := by positivity
      have hK2 : (0 : ℝ) < K + 2 := by positivity
      push_cast
      field_simp
      ring

/-- Crude Basel bound: `∑_{k<K} 1/(k+1)² ≤ 2`. Suffices for shell summation. -/
private lemma sum_inv_nat_succ_sq_le_two (K : ℕ) :
    (∑ k ∈ Finset.range K, (1 : ℝ) / ((k + 1 : ℝ) ^ 2)) ≤ 2 := by
  calc (∑ k ∈ Finset.range K, (1 : ℝ) / ((k + 1 : ℝ) ^ 2))
      ≤ ∑ k ∈ Finset.range K, 2 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro k _
        have hk1 : (0 : ℝ) < k + 1 := by positivity
        have hk2 : (0 : ℝ) < k + 2 := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = 2 - 2 / (K + 1 : ℝ) := sum_two_over_telescopes_exact K
    _ ≤ 2 := by
        have : (0 : ℝ) ≤ 2 / (K + 1 : ℝ) := by positivity
        linarith

/-! ### Body shell bound (core mathematical content, left as a named lemma) -/

/-- **Body vertical-shell bound for the far-zero subtraction**. The body
contribution `∑ ρ ∈ bodyFS, 2·n(ρ)/|γ-T|²` is `O(log T)`. Proof partitions
`bodyFS` by vertical distance `k = ⌊|ρ.im - T|⌋`; upper shells and lower
"good" shells (k ≤ ⌊T⌋-2) use H10 short-window weighted counts, while lower
edge shells (k > ⌊T⌋-2) are absorbed by the disk bound. The helper
`sum_inv_nat_succ_sq_le_two` bounds `∑ 1/k² ≤ 2`, which combined with
per-shell `O(log T)` yields the overall `O(log T)` bound.

Structural proof is ~80-180 lines of Finset shell partition via
`Finset.sum_fiberwise_of_maps_to` with `kf ρ := ⌊|ρ.im-T|⌋.toNat`.

For T ≥ 2, log(2T+6) ≤ 4 * log T. -/
private lemma log_2T_plus_6_le {T : ℝ} (hT : 2 ≤ T) :
    Real.log (2 * T + 6) ≤ 4 * Real.log T := by
  erw [← Real.log_pow, Real.log_le_log_iff] <;> nlinarith [sq_nonneg (T - 2)]

/-- 20 * CH10 ≤ 40 * (CH10 + Cdisk + 1) * (R₀disk + 1) for positive constants. -/
private lemma shell_constant_bound {CH10 Cdisk R₀disk : ℝ}
    (hCH10 : 0 < CH10) (hCdisk : 0 < Cdisk) (hR₀ : 0 < R₀disk) :
    20 * CH10 ≤ 40 * (CH10 + Cdisk + 1) * (R₀disk + 1) := by
  nlinarith

/-
Each ρ ∈ bodyFS satisfies the expected properties.
-/
private lemma bodyFS_pos_mem {T : ℝ}
    {bodyFS : Finset ℂ}
    (h_bodyFS_def : bodyFS =
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
        (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im)))
    {ρ : ℂ} (hρ : ρ ∈ bodyFS) :
    ρ ∈ NontrivialZeros ∧ ‖ρ‖ ≤ 2 * T + 5 ∧ 1 < |ρ.im - T| ∧ 2 ≤ ρ.im := by
  simp_all +decide [ Finset.mem_filter, Set.Finite.mem_toFinset ]

/-
The shell sum over bodyFS is bounded by a sum over windows via
    the fiberwise decomposition with shell index `k = ⌊|ρ.im - T|⌋₊`.
    For each shell k ≥ 1, the weighted count is bounded by at most
    2 windows (upper and lower), each ≤ CH10 * log(center).
    Per-shell contribution ≤ (2/k²) * 5 * CH10 * log T.
    Total ≤ 10 * CH10 * log T * ∑ 1/k² ≤ 20 * CH10 * log T ≤ 40 * CH10 * log T.

Per-shell bound: for each shell, the fiber's contribution is small.
    Shell k (k ≥ 1) consists of ρ with ⌊|ρ.im - T|⌋₊ = k.
    Upper half-shell is in windowFinset(T+k+1), lower is in windowFinset(T-k).
    Per-shell contribution ≤ (2/k²) * 5 * CH10 * logT.

    Upper half-shell weighted count: ρ with ρ.im > T and ⌊ρ.im - T⌋₊ = k.
    These are in windowFinset(T+k+1), giving count ≤ CH10*log(T+k+1) ≤ 4*CH10*logT.
-/
private lemma upper_shell_wt_count
    {T : ℝ} (hT : 2 ≤ T) {CH10 : ℝ}
    (hCH10_bd : ∀ T' : ℝ, 2 ≤ T' →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T' + 1)).toFinset.filter
        (fun ρ => |ρ.im - T'| ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T')
    (bodyFS : Finset ℂ)
    (h_bodyFS_def : bodyFS =
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
        (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im)))
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im > T),
      (ZD.xiOrderNat ρ : ℝ)) ≤ 4 * CH10 * Real.log T := by
  by_cases h_filter_empty : (bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im > T)).Nonempty;
  · have h_upper_half_shell_subset : bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im > T) ⊆ windowFinset (T + k + 1) := by
      intro ρ hρ
      simp [h_bodyFS_def] at hρ;
      apply upper_shell_in_windowFinset hT k hρ.left.left.left (by
      rw [ Nat.floor_eq_iff ] at hρ <;> cases abs_cases ( ρ.im - T ) <;> linarith) (by
      rw [ Nat.floor_eq_iff ] at hρ <;> cases abs_cases ( ρ.im - T ) <;> linarith);
    refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_upper_half_shell_subset ?_ ) ?_;
    · exact fun _ _ _ => Nat.cast_nonneg _;
    · refine le_trans ( hCH10_bd ( T + k + 1 ) ( by linarith ) ) ?_;
      have h_log_bound : Real.log (T + k + 1) ≤ 4 * Real.log T := by
        have h_log_bound : T + k + 1 ≤ 2 * T + 6 := by
          obtain ⟨ ρ, hρ ⟩ := h_filter_empty; simp_all +decide [ windowFinset ] ;
          have := Nat.floor_le ( abs_nonneg ( ρ.im - T ) ) ; rw [ hρ.2.1 ] at this; rw [ abs_of_nonneg ] at this <;> linarith [ abs_le.mp ( Complex.abs_im_le_norm ρ ) ] ;
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
        nlinarith [ sq_nonneg ( T - 2 ) ];
      nlinarith [ show 0 ≤ CH10 by have := hCH10_bd 2 ( by norm_num ) ; exact le_of_not_gt fun h => by { exact absurd this ( by { exact not_le_of_gt ( by { exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos h ( Real.log_pos ( by norm_num ) ) ) ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) } ) } ) } ];
  · have hCH10_nonneg : 0 ≤ CH10 := by
      contrapose! hCH10_bd;
      exact ⟨ 2, by norm_num, lt_of_lt_of_le ( mul_neg_of_neg_of_pos hCH10_bd ( Real.log_pos ( by norm_num ) ) ) ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ⟩;
    rw [ Finset.not_nonempty_iff_eq_empty.mp h_filter_empty ] ; norm_num ; nlinarith [ Real.log_nonneg ( by linarith : ( 1 : ℝ ) ≤ T ) ]

/-
Lower half-shell weighted count: ρ with ρ.im ≤ T and ⌊T - ρ.im⌋₊ = k.
    These are in windowFinset(T-k) when T-k ≥ 2, giving count ≤ CH10*logT.
    When T-k < 2, the shell is empty (since ρ.im ≥ 2).
-/
private lemma lower_shell_wt_count
    {T : ℝ} (hT : 2 ≤ T) {CH10 : ℝ}
    (hCH10_bd : ∀ T' : ℝ, 2 ≤ T' →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T' + 1)).toFinset.filter
        (fun ρ => |ρ.im - T'| ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T')
    (bodyFS : Finset ℂ)
    (h_bodyFS_def : bodyFS =
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
        (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im)))
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im ≤ T),
      (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T := by
  by_cases hk_le : k ≤ T - 2;
  · refine' le_trans _ ( hCH10_bd ( T - k ) ( by linarith ) |> le_trans <| mul_le_mul_of_nonneg_left ( Real.log_le_log ( by linarith ) <| by linarith ) <| _ );
    · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => Nat.cast_nonneg _ );
      convert rfl.le using 1;
      intro ρ hρ; simp_all +decide [ Nat.floor_eq_iff ] ;
      constructor;
      · exact le_trans ( Complex.norm_le_abs_re_add_abs_im _ ) ( by cases abs_cases ( ρ.re ) <;> cases abs_cases ( ρ.im ) <;> cases abs_cases ( ρ.im - T ) <;> linarith [ hρ.1.1.1.1, hρ.1.1.1.2.1 ] );
      · exact abs_le.mpr ⟨ by cases abs_cases ( ρ.im - T ) <;> linarith, by cases abs_cases ( ρ.im - T ) <;> linarith ⟩;
    · contrapose! hCH10_bd;
      exact ⟨ 2, by norm_num, lt_of_lt_of_le ( mul_neg_of_neg_of_pos hCH10_bd ( Real.log_pos ( by norm_num ) ) ) ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ⟩;
  · rw [ Finset.sum_eq_zero ];
    · have := hCH10_bd 2 ( by norm_num );
      exact mul_nonneg ( le_of_not_gt fun h => by have := this.trans' ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ; nlinarith [ Real.log_pos one_lt_two ] ) ( Real.log_nonneg ( by linarith ) );
    · simp_all +decide [ Nat.floor_eq_iff ];
      grind

/-
Per-shell bound combining upper and lower half-shells.
-/
private lemma per_shell_bound
    {T : ℝ} (hT : 2 ≤ T) {CH10 : ℝ}
    (hCH10_bd : ∀ T' : ℝ, 2 ≤ T' →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T' + 1)).toFinset.filter
        (fun ρ => |ρ.im - T'| ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T')
    (bodyFS : Finset ℂ)
    (h_bodyFS_def : bodyFS =
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
        (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im)))
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k),
      2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      10 * CH10 * Real.log T / (k : ℝ) ^ 2 := by
  refine' le_trans ( Finset.sum_le_sum _ ) _;
  use fun ρ => 2 * ( xiOrderNat ρ : ℝ ) / k ^ 2;
  · intro ρ hρ; gcongr;
    exact_mod_cast Finset.mem_filter.mp hρ |>.2 ▸ Nat.floor_le ( abs_nonneg _ );
  · have h_split : (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k), (ZD.xiOrderNat ρ : ℝ)) ≤ 5 * CH10 * Real.log T := by
      have h_combined : (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im > T), (xiOrderNat ρ : ℝ)) + (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k ∧ ρ.im ≤ T), (xiOrderNat ρ : ℝ)) ≤ 5 * CH10 * Real.log T := by
        refine' le_trans ( add_le_add ( upper_shell_wt_count hT hCH10_bd bodyFS h_bodyFS_def k hk ) ( lower_shell_wt_count hT hCH10_bd bodyFS h_bodyFS_def k hk ) ) _ ; ring_nf ; norm_num;
      convert h_combined using 1;
      rw [ ← Finset.sum_union ];
      · rcongr ρ ; by_cases h : ρ.im > T <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    rw [ ← Finset.sum_div _ _ _, ← Finset.mul_sum _ _ _ ] ; convert mul_le_mul_of_nonneg_right h_split ( by positivity : ( 0 : ℝ ) ≤ 2 / k ^ 2 ) using 1 <;> ring;

lemma bodyFS_shell_bound_core
    {T : ℝ} (hT : 2 ≤ T) {CH10 : ℝ}
    (hCH10_bd : ∀ T' : ℝ, 2 ≤ T' →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T' + 1)).toFinset.filter
        (fun ρ => |ρ.im - T'| ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T')
    (bodyFS : Finset ℂ)
    (h_bodyFS_def : bodyFS =
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
        (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im))) :
    (∑ ρ ∈ bodyFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      40 * CH10 * Real.log T := by
  -- By partitioning the sum over `bodyFS` into subsets where `⌊|ρ.im - T|⌋₊ = k`, we can apply the per_shell_bound lemma to each subset.
  have h_partition : ∀ K : ℕ, (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ ≤ K), 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤ 10 * CH10 * Real.log T * (∑ k ∈ Finset.range K, (1 : ℝ) / ((k + 1 : ℝ) ^ 2)) := by
    intro K
    have h_partition : (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ ≤ K), 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) = ∑ k ∈ Finset.range K, (∑ ρ ∈ bodyFS.filter (fun ρ => ⌊|ρ.im - T|⌋₊ = k + 1), 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) := by
      rw [ ← Finset.sum_biUnion ];
      · refine' Finset.sum_subset _ _ <;> intro ρ hρ <;> simp_all +decide [ Finset.mem_biUnion ];
        · exact ⟨ ⌊|ρ.im - T|⌋₊ - 1, by rw [ tsub_lt_iff_left ] <;> linarith [ show ⌊|ρ.im - T|⌋₊ ≥ 1 from Nat.floor_pos.mpr hρ.1.2.1.le ], by rw [ Nat.sub_add_cancel ( Nat.floor_pos.mpr hρ.1.2.1.le ) ] ⟩;
        · grind;
      · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
    rw [ h_partition, Finset.mul_sum _ _ _ ];
    refine Finset.sum_le_sum fun k hk => ?_;
    convert per_shell_bound hT hCH10_bd bodyFS h_bodyFS_def ( k + 1 ) ( by linarith ) using 1 ; norm_num ; ring;
  -- Let $K$ be the maximum value of $\lfloor|\rho.im - T|\rfloor$ for $\rho \in \text{bodyFS}$.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ ρ ∈ bodyFS, ⌊|ρ.im - T|⌋₊ ≤ K := by
    exact ⟨ Finset.sup bodyFS fun ρ => ⌊|ρ.im - T|⌋₊, fun ρ hρ => Finset.le_sup ( f := fun ρ => ⌊|ρ.im - T|⌋₊ ) hρ ⟩;
  have := h_partition K;
  refine le_trans ?_ ( this.trans ?_ );
  · rw [ Finset.filter_true_of_mem hK ];
  · have := sum_inv_nat_succ_sq_le_two K;
    nlinarith [ show 0 ≤ CH10 * Real.log T by exact mul_nonneg ( show 0 ≤ CH10 by have := hCH10_bd 2 ( by norm_num ) ; exact le_of_not_gt fun h => by { exact absurd this ( by { exact not_le_of_gt ( by { exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos h ( Real.log_pos ( by norm_num ) ) ) ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) } ) } ) } ) ( Real.log_nonneg ( by linarith ) ) ]

lemma bodyFS_shell_bound
    {T : ℝ} (hT : 2 ≤ T)
    {CH10 Cdisk R₀disk : ℝ}
    (hCH10_pos : 0 < CH10) (hCdisk_pos : 0 < Cdisk) (hR₀disk_pos : 0 < R₀disk)
    (hCH10_bd : ∀ T' : ℝ, 2 ≤ T' →
      (∑ ρ ∈ ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (T' + 1)).toFinset.filter
        (fun ρ => |ρ.im - T'| ≤ 1)), (ZD.xiOrderNat ρ : ℝ)) ≤ CH10 * Real.log T')
    (hCdisk_bd : ∀ R : ℝ, R₀disk ≤ R →
      ∀ S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros},
        (∀ ρ ∈ S, ‖ρ.val‖ ≤ R) →
          (∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ)) ≤ Cdisk * R * Real.log R)
    (bodyFS : Finset ℂ)
    (h_bodyFS_def :
      bodyFS =
        ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
          (fun ρ => 1 < |ρ.im - T|))) :
    (∑ ρ ∈ bodyFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      40 * (CH10 + Cdisk + 1) * (R₀disk + 1) ^ 2 * Real.log T := by
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- Split bodyFS into positive-imaginary and negative-imaginary parts
  set base := (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset
  set posFS := bodyFS.filter (fun ρ => (2 : ℝ) ≤ ρ.im) with hposFS_def
  set negFS := bodyFS.filter (fun ρ => ¬((2 : ℝ) ≤ ρ.im)) with hnegFS_def
  have h_disj : Disjoint posFS negFS := by
    rw [hposFS_def, hnegFS_def]; exact Finset.disjoint_filter_filter_not _ _ _
  have h_union : bodyFS = posFS ∪ negFS := by
    ext ρ; simp only [hposFS_def, hnegFS_def, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [h_union, Finset.sum_union h_disj]
  -- Membership properties
  have h_mem : ∀ ρ ∈ bodyFS,
      ρ ∈ NontrivialZeros ∧ ‖ρ‖ ≤ 2 * T + 5 ∧ 1 < |ρ.im - T| := by
    intro ρ hρ
    rw [h_bodyFS_def, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    refine ⟨hρ.1.1, ?_, hρ.2⟩
    have := hρ.1.2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
  -- Part 1: positive-imaginary contribution via shell bound core
  have h_posFS_def : posFS = base.filter (fun ρ => 1 < |ρ.im - T| ∧ 2 ≤ ρ.im) := by
    rw [hposFS_def, h_bodyFS_def]
    ext ρ; simp only [Finset.mem_filter]; tauto
  have h_pos : (∑ ρ ∈ posFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      40 * CH10 * Real.log T :=
    bodyFS_shell_bound_core hT hCH10_bd posFS h_posFS_def
  -- Part 2: negative-imaginary contribution (ρ.im ≤ -2 by Gram, so |ρ.im - T| ≥ T + 2)
  have h_neg_mem : ∀ ρ ∈ negFS, ρ ∈ NontrivialZeros ∧ ‖ρ‖ ≤ 2 * T + 5 ∧
      1 < |ρ.im - T| ∧ ρ.im ≤ -2 := by
    intro ρ hρ
    rw [hnegFS_def, Finset.mem_filter] at hρ
    obtain ⟨hρ_body, hρ_neg⟩ := hρ
    obtain ⟨hρ_ntz, hρ_norm, hρ_far⟩ := h_mem ρ hρ_body
    refine ⟨hρ_ntz, hρ_norm, hρ_far, ?_⟩
    push_neg at hρ_neg
    have him := NontrivialZeros_im_ge_two hρ_ntz
    by_contra h_not_le; push_neg at h_not_le
    have : |ρ.im| < 2 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have h_neg_gap : ∀ ρ ∈ negFS, (T + 2) ^ 2 ≤ |ρ.im - T| ^ 2 := by
    intro ρ hρ
    obtain ⟨_, _, _, hρ_im⟩ := h_neg_mem ρ hρ
    have : T + 2 ≤ |ρ.im - T| := by
      rw [abs_sub_comm]; rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith
  have h_neg_term : ∀ ρ ∈ negFS,
      2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2 ≤
        2 * (ZD.xiOrderNat ρ : ℝ) / (T + 2) ^ 2 := by
    intro ρ hρ
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (h_neg_gap ρ hρ)
  have h_neg_sum : (∑ ρ ∈ negFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      2 / (T + 2) ^ 2 * ∑ ρ ∈ negFS, (ZD.xiOrderNat ρ : ℝ) := by
    calc ∑ ρ ∈ negFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2
        ≤ ∑ ρ ∈ negFS, 2 * (ZD.xiOrderNat ρ : ℝ) / (T + 2) ^ 2 :=
          Finset.sum_le_sum h_neg_term
      _ = 2 / (T + 2) ^ 2 * ∑ ρ ∈ negFS, (ZD.xiOrderNat ρ : ℝ) := by
          rw [Finset.mul_sum]; congr 1; ext; ring
  -- Bound negative-imaginary contribution using disk bound
  -- Step 1: Convert negFS to subtype finset and apply disk bound
  have h_neg_wt_count : (∑ ρ ∈ negFS, (ZD.xiOrderNat ρ : ℝ)) ≤
      Cdisk * max R₀disk (2 * T + 5) * Real.log (max R₀disk (2 * T + 5)) := by
    convert hCdisk_bd ( Max.max R₀disk ( 2 * T + 5 ) ) ( le_max_left _ _ ) ( Finset.subtype ( fun ρ => ρ ∈ NontrivialZeros ) negFS ) _ using 1;
    convert Finset.sum_image ?_;
    all_goals norm_num [ Finset.ext_iff ];
    · exact fun ρ hρ => h_neg_mem ρ hρ |>.1;
    · infer_instance;
    · exact fun _ => Classical.dec _;
    · exact fun ρ hρ₁ hρ₂ => Or.inr ( h_neg_mem ρ hρ₂ |>.2.1 )
  -- Step 2: Arithmetic bound
  have h_neg_final : (∑ ρ ∈ negFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
      8 * Cdisk * (R₀disk + 1) ^ 2 * Real.log T := by
    refine le_trans h_neg_sum <| le_trans ( mul_le_mul_of_nonneg_left h_neg_wt_count <| by positivity ) ?_;
    by_cases h_case : R₀disk ≤ 2 * T + 5;
    · -- Since $R₀disk \leq 2T + 5$, we have $\log(2T + 5) \leq 4 \log T$.
      have h_log_bound : Real.log (2 * T + 5) ≤ 4 * Real.log T := by
        erw [ ← Real.log_pow ] ; gcongr ; nlinarith [ sq_nonneg ( T - 2 ) ];
      rw [ max_eq_right h_case ];
      refine le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left h_log_bound <| by positivity ) <| by positivity ) ?_;
      field_simp;
      nlinarith only [ sq_nonneg ( T - 2 ), sq_nonneg ( R₀disk - 1 ), hT, hR₀disk_pos, mul_le_mul_of_nonneg_left hT hR₀disk_pos.le ];
    · rw [ max_eq_left ( by linarith ) ];
      -- We can cancel out $Cdisk$ from both sides since it is positive.
      suffices h_cancel : 2 * R₀disk * Real.log R₀disk / (T + 2) ^ 2 ≤ 8 * (R₀disk + 1) ^ 2 * Real.log T by
        convert mul_le_mul_of_nonneg_left h_cancel hCdisk_pos.le using 1 <;> ring;
      rw [ div_le_iff₀ ( by positivity ) ];
      have h_log_bound : Real.log R₀disk ≤ R₀disk := by
        linarith [ Real.log_le_sub_one_of_pos hR₀disk_pos ];
      have h_log_bound : Real.log T ≥ 1 / 2 := by
        exact le_trans ( Real.log_two_gt_d9.le.trans' <| by norm_num ) ( Real.log_le_log ( by norm_num ) hT );
      nlinarith [ sq_nonneg ( R₀disk - 2 * T - 5 ), mul_le_mul_of_nonneg_left h_log_bound ( show 0 ≤ R₀disk by positivity ), mul_le_mul_of_nonneg_left h_log_bound ( show 0 ≤ T by positivity ), mul_le_mul_of_nonneg_left h_log_bound ( show 0 ≤ T ^ 2 by positivity ) ]
  -- Combine both parts
  calc (∑ ρ ∈ posFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) +
      (∑ ρ ∈ negFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2)
      ≤ 40 * CH10 * Real.log T + 8 * Cdisk * (R₀disk + 1) ^ 2 * Real.log T := by
        linarith [h_pos, h_neg_final]
    _ = (40 * CH10 + 8 * Cdisk * (R₀disk + 1) ^ 2) * Real.log T := by ring
    _ ≤ 40 * (CH10 + Cdisk + 1) * (R₀disk + 1) ^ 2 * Real.log T := by
        apply mul_le_mul_of_nonneg_right _ hlogT_pos.le
        nlinarith [sq_nonneg R₀disk, sq_nonneg (R₀disk + 1)]

/-! ### Main theorem -/

/-- **Main theorem**: `‖∑_{|γ-T|>1} n(ρ)·(1/(s-ρ) - 1/(s₀-ρ))‖ ≤ C · log T`.
Far-zero subtraction bound via dyadic shell decomposition. -/
theorem xi_logDeriv_sub_far_bound_proved :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (0:ℝ) 2, ∀ T : ℝ, 2 ≤ T →
      ‖∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - T| ≤ 1},
          (ZD.xiOrderNat ρ.val : ℂ) *
            (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
             1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))‖
        ≤ C * Real.log T := by
  -- Extract H10 and disk bound constants.
  obtain ⟨CH10, hCH10_pos, hCH10_bd⟩ :=
    ZD.nontrivialZeros_short_window_weighted_count_bound
  obtain ⟨Cdisk, hCdisk_pos, R₀disk, hR₀disk_pos, hCdisk_bd⟩ :=
    ZD.xi_weighted_zero_count_disk_bound
  -- M_tot is the total summable sum of n(ρ)/‖ρ‖² over NTZ.
  have hsumm_sq := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros
  set M_tot : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 with hM_tot_def
  have hMtot_nn : 0 ≤ M_tot :=
    tsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity))
  -- Universal constant. Absorb the π²/6 bound, edge contribution, and tail.
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Shell body bound constant and tail bound constant.
  set C_body : ℝ := 40 * (CH10 + Cdisk + 1) * (R₀disk + 1) ^ 2 with hC_body_def
  have hC_body_nn : 0 ≤ C_body := by
    rw [hC_body_def]; positivity
  set C_total : ℝ := 8 * M_tot / Real.log 2 + C_body with hC_total_def
  have hC_total_pos : 0 < C_total := by
    rw [hC_total_def]
    have h1 : 0 ≤ 8 * M_tot / Real.log 2 := div_nonneg (by linarith) hlog2_pos.le
    have h2 : 0 < C_body := by rw [hC_body_def]; positivity
    linarith
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro σ hσ T hT
  have hT_pos : (0 : ℝ) < T := by linarith
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT_ge_log2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  -- Define the Far subtype and termF.
  let Far : Type := {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ¬|ρ.im - T| ≤ 1}
  let termF : Far → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) *
      (1 / ((σ : ℂ) + (T : ℂ) * I - ρ.val) -
       1 / ((2 : ℂ) + (T : ℂ) * I - ρ.val))
  -- Define the majorant g : Far → ℝ.
  let g : Far → ℝ := fun ρ =>
    if ‖ρ.val‖ < 2 * T + 5 then
      2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2
    else
      8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2
  have hg_nn : ∀ ρ : Far, 0 ≤ g ρ := by
    intro ρ
    show 0 ≤ (if ‖ρ.val‖ < 2 * T + 5 then _ else _)
    split_ifs with h
    · have hfar : ¬ |ρ.val.im - T| ≤ 1 := ρ.property.2
      have hgap : 1 < |ρ.val.im - T| := by by_contra h; exact hfar (not_lt.mp h)
      have hgap_sq_pos : 0 < |ρ.val.im - T| ^ 2 := by positivity
      positivity
    · positivity
  have h_term_le_g : ∀ ρ : Far, ‖termF ρ‖ ≤ g ρ := by
    intro ρ
    show ‖(ZD.xiOrderNat ρ.val : ℂ) * _‖ ≤ if ‖ρ.val‖ < 2 * T + 5 then _ else _
    by_cases h : ‖ρ.val‖ < 2 * T + 5
    · rw [if_pos h]
      exact far_sub_term_norm_le_gap_sq σ T hσ ρ.property.1 ρ.property.2
    · rw [if_neg h]
      push_neg at h
      exact far_sub_term_norm_le_norm_sq σ T hσ hT_nonneg ρ.property.1 h
  -- Summable upper bound: U ρ = 8n/‖ρ‖² + 2n·𝟙[‖ρ‖<2T+5].
  let U : Far → ℝ := fun ρ =>
    8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 +
      (if ‖ρ.val‖ < 2 * T + 5 then 2 * (ZD.xiOrderNat ρ.val : ℝ) else 0)
  -- Piecewise check: g ρ ≤ U ρ.
  have h_g_le_U : ∀ ρ : Far, g ρ ≤ U ρ := by
    intro ρ
    show (if ‖ρ.val‖ < 2 * T + 5 then _ else _) ≤ _
    have hxi_nn : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
    have hinv_nn : 0 ≤ 8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by positivity
    by_cases h : ‖ρ.val‖ < 2 * T + 5
    · rw [if_pos h]
      show 2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2 ≤
          8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 +
            if ‖ρ.val‖ < 2 * T + 5 then 2 * (ZD.xiOrderNat ρ.val : ℝ) else 0
      rw [if_pos h]
      have hfar : ¬ |ρ.val.im - T| ≤ 1 := ρ.property.2
      have hgap_gt_one : 1 < |ρ.val.im - T| := by
        by_contra hh; exact hfar (not_lt.mp hh)
      have hgap_sq_gt : 1 < |ρ.val.im - T| ^ 2 := by nlinarith
      have h_bound : 2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2 ≤
          2 * (ZD.xiOrderNat ρ.val : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · rw [if_neg h]
      show 8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤
          8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 +
            if ‖ρ.val‖ < 2 * T + 5 then 2 * (ZD.xiOrderNat ρ.val : ℝ) else 0
      rw [if_neg h]
      linarith
  -- Part 1: the norm-sq part is summable by comparison to hsumm_sq.
  have h_U1_summ : Summable (fun ρ : Far =>
      8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
    have h_emb_inj : Function.Injective
        (fun ρ : Far => (⟨ρ.val, ρ.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros})) := by
      intro ρ₁ ρ₂ h
      have h1 : (⟨ρ₁.val, ρ₁.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}).val =
          (⟨ρ₂.val, ρ₂.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}).val :=
        congrArg Subtype.val h
      exact Subtype.ext h1
    have h_comp := hsumm_sq.comp_injective h_emb_inj
    have h_mul := h_comp.mul_left 8
    refine h_mul.congr ?_
    intro ρ
    show 8 * ((fun ρ' : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ'.val : ℝ) / ‖ρ'.val‖ ^ 2) ∘
        (fun ρ' : Far => (⟨ρ'.val, ρ'.property.1⟩ :
          {ρ : ℂ // ρ ∈ NontrivialZeros}))) ρ =
      8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2
    simp only [Function.comp]
    ring
  -- Part 2: the body part is finitely supported, hence summable.
  have h_body_fin : {ρ : Far | ‖ρ.val‖ < 2 * T + 5}.Finite := by
    have h_ntz_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (2 * T + 5)).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)
    -- Use injection ρ : Far ↦ ρ.val ∈ ℂ; the image lands in the finite set.
    have h_inj : Set.InjOn (fun ρ : Far => ρ.val) {ρ : Far | ‖ρ.val‖ < 2 * T + 5} := by
      intro ρ₁ _ ρ₂ _ h
      exact Subtype.ext h
    apply Set.Finite.of_finite_image _ h_inj
    apply h_ntz_fin.subset
    intro z hz
    rcases hz with ⟨ρ, hρ_in, hρ_eq⟩
    have h_val_eq : z = ρ.val := hρ_eq.symm
    refine ⟨?_, ?_⟩
    · rw [h_val_eq]; exact ρ.property.1
    · rw [Metric.mem_closedBall, dist_zero_right, h_val_eq]
      exact le_of_lt hρ_in
  have h_U2_summ : Summable (fun ρ : Far =>
      if ‖ρ.val‖ < 2 * T + 5 then 2 * (ZD.xiOrderNat ρ.val : ℝ) else 0) := by
    apply summable_of_finite_support
    apply Set.Finite.subset h_body_fin
    intro ρ hρ
    simp only [Function.mem_support, ne_eq] at hρ
    show ‖ρ.val‖ < 2 * T + 5
    by_contra h
    apply hρ
    simp [if_neg h]
  have h_U_summ : Summable U := h_U1_summ.add h_U2_summ
  -- Conclude: g summable via comparison.
  have h_g_summ : Summable g :=
    Summable.of_nonneg_of_le hg_nn h_g_le_U h_U_summ
  -- Apply Summable.of_norm_bounded to termF.
  have h_termF_summ : Summable termF :=
    Summable.of_norm_bounded h_g_summ h_term_le_g
  -- ‖∑' termF‖ ≤ ∑' ‖termF‖ ≤ ∑' g, with Summable ‖termF‖.
  have h_norm_summ : Summable (fun ρ : Far => ‖termF ρ‖) :=
    h_termF_summ.norm
  have h_tsum_le_g : ∑' ρ : Far, ‖termF ρ‖ ≤ ∑' ρ : Far, g ρ :=
    Summable.tsum_le_tsum h_term_le_g h_norm_summ h_g_summ
  have h_norm_tsum_le : ‖∑' ρ : Far, termF ρ‖ ≤ ∑' ρ : Far, ‖termF ρ‖ :=
    norm_tsum_le_tsum_norm h_norm_summ
  -- Bound ∑' g = ∑' g_tail + ∑' g_body.
  -- Where g_tail(ρ) = if ‖ρ‖ < 2T+5 then 0 else g ρ and g_body(ρ) = else case.
  let g_tail : Far → ℝ := fun ρ =>
    if ‖ρ.val‖ < 2 * T + 5 then 0 else 8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2
  let g_body : Far → ℝ := fun ρ =>
    if ‖ρ.val‖ < 2 * T + 5 then 2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2 else 0
  have h_g_split : ∀ ρ : Far, g ρ = g_tail ρ + g_body ρ := by
    intro ρ
    show (if ‖ρ.val‖ < 2 * T + 5 then _ else _) =
      (if ‖ρ.val‖ < 2 * T + 5 then (0 : ℝ) else _) +
      (if ‖ρ.val‖ < 2 * T + 5 then _ else (0 : ℝ))
    split_ifs with h <;> ring
  have hg_tail_nn : ∀ ρ : Far, 0 ≤ g_tail ρ := by
    intro ρ
    show 0 ≤ (if ‖ρ.val‖ < 2 * T + 5 then (0 : ℝ) else _)
    split_ifs with h
    · exact le_refl _
    · positivity
  have hg_body_nn : ∀ ρ : Far, 0 ≤ g_body ρ := by
    intro ρ
    show 0 ≤ (if ‖ρ.val‖ < 2 * T + 5 then _ else (0 : ℝ))
    split_ifs with h
    · have hfar : ¬ |ρ.val.im - T| ≤ 1 := ρ.property.2
      have hgap_gt : 1 < |ρ.val.im - T| := by by_contra hh; exact hfar (not_lt.mp hh)
      have hgap_sq : 0 < |ρ.val.im - T| ^ 2 := by positivity
      positivity
    · exact le_refl _
  -- Summability of g_tail and g_body separately.
  have h_g_tail_le : ∀ ρ : Far, g_tail ρ ≤ 8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by
    intro ρ
    show (if ‖ρ.val‖ < 2 * T + 5 then (0 : ℝ) else _) ≤ _
    split_ifs with h
    · positivity
    · exact le_refl _
  have h_g_tail_summ : Summable g_tail :=
    Summable.of_nonneg_of_le hg_tail_nn h_g_tail_le h_U1_summ
  have h_g_body_summ : Summable g_body := by
    apply summable_of_finite_support
    apply Set.Finite.subset h_body_fin
    intro ρ hρ
    simp only [Function.mem_support, ne_eq] at hρ
    show ‖ρ.val‖ < 2 * T + 5
    by_contra h
    apply hρ
    show (if ‖ρ.val‖ < 2 * T + 5 then _ else (0 : ℝ)) = 0
    rw [if_neg h]
  -- ∑' g = ∑' g_tail + ∑' g_body.
  have h_tsum_g_split : ∑' ρ : Far, g ρ = (∑' ρ : Far, g_tail ρ) + (∑' ρ : Far, g_body ρ) := by
    rw [← Summable.tsum_add h_g_tail_summ h_g_body_summ]
    exact tsum_congr h_g_split
  -- Bound ∑' g_tail ≤ 8 * M_tot.
  have h_tail_bound : (∑' ρ : Far, g_tail ρ) ≤ 8 * M_tot := by
    -- Embed Far into NTZ_subtype; bound via injective comparison.
    have h_emb_inj : Function.Injective
        (fun ρ : Far => (⟨ρ.val, ρ.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros})) := by
      intro ρ₁ ρ₂ h
      have h1 : (⟨ρ₁.val, ρ₁.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}).val =
          (⟨ρ₂.val, ρ₂.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}).val :=
        congrArg Subtype.val h
      exact Subtype.ext h1
    -- Composed summable: n(ρ)/‖ρ‖² on Far via hsumm_sq
    have h_comp := hsumm_sq.comp_injective h_emb_inj
    -- Show ∑' ρ : Far, n(ρ)/‖ρ‖² ≤ M_tot.
    have h_far_le_tot : ∑' ρ : Far, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 ≤ M_tot := by
      rw [hM_tot_def]
      have h_eq : (fun ρ : Far => (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
          ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
              (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) ∘
            (fun ρ : Far => (⟨ρ.val, ρ.property.1⟩ : {ρ : ℂ // ρ ∈ NontrivialZeros}))) := by
        funext ρ; rfl
      rw [h_eq]
      exact tsum_comp_le_tsum_of_inj hsumm_sq
        (fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)) h_emb_inj
    calc (∑' ρ : Far, g_tail ρ)
        ≤ ∑' ρ : Far, 8 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 :=
          Summable.tsum_le_tsum h_g_tail_le h_g_tail_summ h_U1_summ
      _ = 8 * ∑' ρ : Far, (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro ρ; ring
      _ ≤ 8 * M_tot := by nlinarith [h_far_le_tot]
  -- Bound ∑' g_body ≤ C_body · log T via shells.
  -- The bodyFinset on ℂ.
  set bodyFS : Finset ℂ :=
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * T + 5)).toFinset.filter
      (fun ρ => 1 < |ρ.im - T|)) with h_bodyFS_def
  -- ∑' g_body ≤ ∑ ρ ∈ bodyFS, 2 n(ρ)/|γ-T|² (inequality: bodyFS uses closedBall ≤ 2T+5
  -- while g_body uses strict < 2T+5; Finset may include extra boundary zero(s)).
  have h_body_sum_le : ∑' ρ : Far, g_body ρ ≤
      ∑ ρ ∈ bodyFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2 := by
    -- Step 1: rewrite ∑' g_body as finset sum on Far-indexed finset (g_body 0 outside body).
    set FarBody : Finset Far := h_body_fin.toFinset with hFarBody_def
    have h_tsum_to_sum : ∑' ρ : Far, g_body ρ = ∑ ρ ∈ FarBody, g_body ρ := by
      apply tsum_eq_sum
      intro ρ hρ
      have h_norm_ge : 2 * T + 5 ≤ ‖ρ.val‖ := by
        by_contra h_lt
        push_neg at h_lt
        have : ρ ∈ FarBody := by
          rw [hFarBody_def, Set.Finite.mem_toFinset]
          exact h_lt
        exact hρ this
      show (if ‖ρ.val‖ < 2 * T + 5 then _ else (0 : ℝ)) = 0
      rw [if_neg (not_lt.mpr h_norm_ge)]
    rw [h_tsum_to_sum]
    -- Step 2: g_body on FarBody = 2*n/|γ-T|² (if-branch since ρ ∈ FarBody means ‖ρ.val‖ < 2T+5).
    have h_g_body_on_FB : ∀ ρ ∈ FarBody,
        g_body ρ = 2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2 := by
      intro ρ hρ
      have h_lt : ‖ρ.val‖ < 2 * T + 5 := by
        rw [hFarBody_def, Set.Finite.mem_toFinset] at hρ
        exact hρ
      show (if ‖ρ.val‖ < 2 * T + 5 then _ else (0 : ℝ)) = _
      rw [if_pos h_lt]
    rw [Finset.sum_congr rfl h_g_body_on_FB]
    -- Step 3: map FarBody into bodyFS via ρ ↦ ρ.val. Show image ⊆ bodyFS and sum over image = sum over FarBody.
    have h_val_inj : Set.InjOn (fun ρ : Far => ρ.val) FarBody := by
      intro ρ₁ _ ρ₂ _ h
      exact Subtype.ext h
    rw [show (∑ ρ ∈ FarBody, 2 * (ZD.xiOrderNat ρ.val : ℝ) / |ρ.val.im - T| ^ 2) =
        ∑ z ∈ FarBody.image (fun ρ : Far => ρ.val),
          2 * (ZD.xiOrderNat z : ℝ) / |z.im - T| ^ 2 from ?_]
    swap
    · rw [Finset.sum_image h_val_inj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨ρ, hρ_in, hρ_eq⟩
      have h_norm_lt : ‖ρ.val‖ < 2 * T + 5 := by
        rw [hFarBody_def, Set.Finite.mem_toFinset] at hρ_in
        exact hρ_in
      show z ∈ bodyFS
      rw [h_bodyFS_def, Finset.mem_filter, Set.Finite.mem_toFinset]
      subst hρ_eq
      refine ⟨⟨ρ.property.1, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; linarith
      · have hfar : ¬ |ρ.val.im - T| ≤ 1 := ρ.property.2
        by_contra h_le
        push_neg at h_le
        exact hfar h_le
    · intro ρ _ _; positivity
  -- Bound the Finset sum by shells (delegated to named lemma).
  have h_body_shell_bound :
      (∑ ρ ∈ bodyFS, 2 * (ZD.xiOrderNat ρ : ℝ) / |ρ.im - T| ^ 2) ≤
        C_body * Real.log T := by
    rw [hC_body_def]
    exact bodyFS_shell_bound hT hCH10_pos hCdisk_pos hR₀disk_pos
      hCH10_bd hCdisk_bd bodyFS h_bodyFS_def
  -- Combine all bounds.
  have h_g_tsum_bound : (∑' ρ : Far, g ρ) ≤ 8 * M_tot + C_body * Real.log T := by
    rw [h_tsum_g_split]
    have h_body_bound : (∑' ρ : Far, g_body ρ) ≤ C_body * Real.log T :=
      h_body_sum_le.trans h_body_shell_bound
    linarith
  -- Final chain.
  have h_div : (8 * M_tot) / Real.log 2 * Real.log 2 = 8 * M_tot := by
    field_simp
  have h_tail_bd : 8 * M_tot ≤ (8 * M_tot / Real.log 2) * Real.log T := by
    calc 8 * M_tot = (8 * M_tot / Real.log 2) * Real.log 2 := by rw [h_div]
      _ ≤ (8 * M_tot / Real.log 2) * Real.log T := by
          apply mul_le_mul_of_nonneg_left hlogT_ge_log2
          positivity
  calc ‖∑' ρ : Far, termF ρ‖
      ≤ ∑' ρ : Far, ‖termF ρ‖ := h_norm_tsum_le
    _ ≤ ∑' ρ : Far, g ρ := h_tsum_le_g
    _ ≤ 8 * M_tot + C_body * Real.log T := h_g_tsum_bound
    _ ≤ (8 * M_tot / Real.log 2) * Real.log T + C_body * Real.log T := by linarith
    _ = C_total * Real.log T := by rw [hC_total_def]; ring

end FarShell
end ZD

end
