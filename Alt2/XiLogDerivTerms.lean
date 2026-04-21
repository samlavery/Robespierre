import Mathlib
import RequestProject.XiWeierstrassFactor
import RequestProject.XiProduct

/-!
# Per-factor log-derivative + summability

H7 of the Hadamard-track plan. For each nontrivial zero `ρ`, the Weierstrass
factor `(1 - z/ρ) · exp(z/ρ)` has log-derivative:

```
d/dz log((1 - z/ρ)·exp(z/ρ)) = z / (ρ · (z - ρ))     for z ≠ ρ, ρ ≠ 0.
```

Equivalently: `1/(z - ρ) + 1/ρ`. The two forms are algebraically equal.

For `z ∉ NontrivialZeros`, the series `Σ_ρ z/(ρ·(z - ρ))` converges absolutely,
bounded by `Σ (2‖z‖/‖ρ‖²)` for `‖ρ‖ ≥ 2‖z‖`, which is summable via H2.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- **Per-factor log-derivative**: `logDeriv((1 - z/ρ)·exp(z/ρ)) z = z/(ρ·(z-ρ))`
for `z ≠ ρ` and `ρ ≠ 0`. -/
theorem logDeriv_one_add_xiWeierstrassTerm {ρ z : ℂ} (hρ : ρ ≠ 0) (hzρ : z ≠ ρ) :
    logDeriv (fun w => 1 + xiWeierstrassTerm ρ w) z = z / (ρ * (z - ρ)) := by
  have h_sub : (1 - z / ρ) ≠ 0 := by
    intro h
    have : z / ρ = 1 := by linear_combination -h
    have : z = ρ := by
      have heq : z = (z / ρ) * ρ := by field_simp
      rw [heq, this, one_mul]
    exact hzρ this
  have hzρ_sub : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  have h_factor_ne : (1 - z / ρ) * Complex.exp (z / ρ) ≠ 0 :=
    mul_ne_zero h_sub (Complex.exp_ne_zero _)
  -- Rewrite as (1 + term) = factor, use logDeriv_mul on factor = (1-z/ρ)·exp(z/ρ).
  have h_fun_eq :
      (fun w => 1 + xiWeierstrassTerm ρ w) =
        fun w => (1 - w / ρ) * Complex.exp (w / ρ) := by
    funext w
    rw [one_add_xiWeierstrassTerm]
    rfl
  rw [h_fun_eq]
  -- logDeriv (f · g) = logDeriv f + logDeriv g where f = 1 - z/ρ, g = exp(z/ρ).
  have h_f_diff : DifferentiableAt ℂ (fun w : ℂ => 1 - w / ρ) z :=
    ((differentiableAt_const 1).sub (differentiableAt_id.div_const ρ))
  have h_g_diff : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w / ρ)) z := by
    have h_div : DifferentiableAt ℂ (fun w : ℂ => w / ρ) z :=
      differentiableAt_id.div_const ρ
    exact Complex.differentiable_exp.differentiableAt.comp z h_div
  have h_mul := logDeriv_mul (f := fun w : ℂ => 1 - w / ρ)
    (g := fun w : ℂ => Complex.exp (w / ρ)) z h_sub (Complex.exp_ne_zero _) h_f_diff h_g_diff
  rw [h_mul]
  -- logDeriv (1 - z/ρ) at z = -1/ρ / (1 - z/ρ).
  have h_logDeriv_sub : logDeriv (fun w : ℂ => 1 - w / ρ) z = -1 / (ρ * (1 - z / ρ)) := by
    rw [logDeriv_apply]
    have h_deriv : deriv (fun w : ℂ => 1 - w / ρ) z = -1 / ρ := by
      rw [deriv_const_sub, deriv_div_const, deriv_id'']; ring
    rw [h_deriv]
    field_simp
  -- logDeriv (exp(z/ρ)) at z = 1/ρ.
  have h_logDeriv_exp : logDeriv (fun w : ℂ => Complex.exp (w / ρ)) z = 1 / ρ := by
    rw [show (fun w : ℂ => Complex.exp (w / ρ)) = Complex.exp ∘ (fun w : ℂ => w / ρ) from rfl]
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_exp]
    rw [deriv_div_const, deriv_id'']
    simp [Pi.one_apply]
  rw [h_logDeriv_sub, h_logDeriv_exp]
  -- Algebra: -1/(ρ(1 - z/ρ)) + 1/ρ = z/(ρ(z - ρ)).
  have h_ρz_ne : ρ - z ≠ 0 := fun h => hzρ (sub_eq_zero.mp h).symm
  have h_zρ_ne : z - ρ ≠ 0 := hzρ_sub
  have h1ρ_ne : (1 - z / ρ) ≠ 0 := h_sub
  field_simp
  ring

#print axioms logDeriv_one_add_xiWeierstrassTerm

/-- **Summability of the log-derivative series** at any `z ∉ NontrivialZeros`.
For every such `z`, `Σ_ρ z/(ρ·(z-ρ))` converges absolutely. -/
theorem summable_logDeriv_xiWeierstrassTerm {z : ℂ} (hz : z ∉ NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      z / (ρ.val * (z - ρ.val))) := by
  -- Threshold: ‖ρ‖ ≥ 2‖z‖ + 1 (so ‖z - ρ‖ ≥ ‖ρ‖ - ‖z‖ ≥ (‖ρ‖ + 1)/2 > 0).
  -- Majorant: 2‖z‖/‖ρ‖² (which is summable via H2, summable_inv_norm_sq_nontrivialZeros).
  set K : ℝ := 2 * ‖z‖ + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith [norm_nonneg z]
  -- Summable majorant: 2‖z‖/‖ρ‖² over all ρ.
  have h_maj : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
      2 * ‖z‖ / ‖ρ.val‖ ^ 2) := by
    have := summable_inv_norm_sq_nontrivialZeros.mul_left (2 * ‖z‖)
    refine this.congr ?_
    intro ρ; show 2 * ‖z‖ * ((1 : ℝ) / ‖ρ.val‖ ^ 2) = _; ring
  -- Cofinite: for ‖ρ‖ ≥ K, bound holds.
  refine h_maj.of_norm_bounded_eventually ?_
  -- Finite set: ρ with ‖ρ‖ < K.
  have hfin : {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < K}.Finite := by
    have h_ntz_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) K).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite K
    have h_image_fin :
        ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
          {ρ | ‖ρ.val‖ < K}).Finite := by
      apply h_ntz_fin.subset
      intro w hw
      rcases hw with ⟨ρ, hρ_lt, hρ_eq⟩
      simp only [Set.mem_setOf_eq] at hρ_lt
      subst hρ_eq
      refine ⟨ρ.property, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    exact h_image_fin.of_finite_image Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with ρ hρ
  have hρ_ge_K : K ≤ ‖ρ.val‖ := by
    by_contra h; push_neg at h; exact hρ h
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hρ_ge_K
    linarith
  have hρ_norm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hρ_ne
  -- ‖z - ρ‖ ≥ ‖ρ‖ - ‖z‖ ≥ K - ‖z‖ = ‖z‖ + 1 > 0
  have h_z_sub : ‖z‖ + 1 ≤ ‖z - ρ.val‖ := by
    have h_abs : |‖ρ.val‖ - ‖z‖| ≤ ‖ρ.val - z‖ := abs_norm_sub_norm_le ρ.val z
    have h_rev : ‖ρ.val - z‖ = ‖z - ρ.val‖ := norm_sub_rev _ _
    have h1 : ‖ρ.val‖ - ‖z‖ ≤ ‖z - ρ.val‖ := by
      have := le_abs_self (‖ρ.val‖ - ‖z‖)
      linarith
    linarith
  have h_z_sub_pos : 0 < ‖z - ρ.val‖ := by
    have : 0 < ‖z‖ + 1 := by linarith [norm_nonneg z]
    linarith
  have h_z_sub_ne : z - ρ.val ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at h_z_sub_pos
    linarith
  -- Compute the bound.
  have h_bound : ‖z / (ρ.val * (z - ρ.val))‖ ≤ 2 * ‖z‖ / ‖ρ.val‖ ^ 2 := by
    rw [norm_div, norm_mul]
    have h_denom_pos : 0 < ‖ρ.val‖ * ‖z - ρ.val‖ := by positivity
    have h_rhs_denom : 0 < ‖ρ.val‖ ^ 2 := by positivity
    rw [div_le_div_iff₀ h_denom_pos h_rhs_denom]
    have h_z_nn : 0 ≤ ‖z‖ := norm_nonneg z
    have h_triangle : ‖ρ.val‖ ≤ ‖z‖ + ‖z - ρ.val‖ := by
      have h := norm_sub_norm_le ρ.val z
      have hrev : ‖ρ.val - z‖ = ‖z - ρ.val‖ := norm_sub_rev _ _
      linarith
    have h_sub_bd : ‖ρ.val‖ ≤ 2 * ‖z - ρ.val‖ := by linarith [h_z_sub, h_triangle]
    -- ‖z‖ · ‖ρ.val‖² ≤ 2·‖z‖·(‖ρ.val‖·‖z - ρ.val‖) ⟺ ‖z‖·‖ρ.val‖·(‖ρ.val‖ - 2‖z-ρ.val‖) ≤ 0.
    have h_gap : ‖ρ.val‖ * (‖ρ.val‖ - 2 * ‖z - ρ.val‖) ≤ 0 := by
      have h_pos : 0 ≤ ‖ρ.val‖ := norm_nonneg _
      have h_neg : ‖ρ.val‖ - 2 * ‖z - ρ.val‖ ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos h_pos h_neg
    nlinarith [h_gap, h_z_nn, h_denom_pos.le]
  exact h_bound

#print axioms summable_logDeriv_xiWeierstrassTerm

end ZD
