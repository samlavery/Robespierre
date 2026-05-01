import Mathlib
import RequestProject.StirlingBound
import RequestProject.EulerMaclaurinDirichlet

/-!
# Polynomial Bound on ζ in the Critical Strip (Phragmén–Lindelöf route)

Target: for each `σ ∈ (0, 1)`, `|ζ(σ + iγ)| ≤ C · |γ|^N` for `|γ|` large.

Route: Hadamard three-lines / Phragmén–Lindelöf applied to `(s-1)·ζ(s)` on
the strip `Re s ∈ [-1, 2]`, using:

* Phase 1 (this file): `|ζ(s)| ≤ ζ(Re s) ≤ ζ(2)` for `Re s ≥ 2`.
* Phase 2: `|ζ(s)| ≤ C · |Im s|^N` for `Re s = -1` via FE + Γ-ratio.
* Phase 3: regularize pole at `s = 1` via `(s - 1)·ζ(s)`.
* Phase 4: apply `Complex.PhragmenLindelof.strip` to interpolate.

This file implements **Phase 1**.
-/

open Complex Real

noncomputable section

namespace ZD

namespace StripBound

/-- **Phase 1: absolute-convergence bound for ζ on `Re s ≥ 2`.**
For `Re s ≥ 2`, `|ζ(s)| ≤ ζ(Re s)` where `ζ(Re s)` denotes the real-valued
Dirichlet-series sum. Derived directly from `zeta_eq_tsum_one_div_nat_cpow`. -/
theorem norm_zeta_le_zeta_re_of_two_le_re
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' (n : ℕ), 1 / (n : ℝ) ^ s.re := by
  have hs1 : 1 < s.re := by linarith
  -- Per-term norm bound: ‖1/n^s‖ = 1/n^(Re s)
  have h_term : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
      have h_pos : 0 < s.re := by linarith
      simp [Complex.zero_cpow hs_ne, Real.zero_rpow (ne_of_gt h_pos)]
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
  -- Summability of the complex series (needed for norm_tsum_le_tsum_norm)
  have h_summ_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖) := by
    have : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
      Real.summable_one_div_nat_rpow.mpr hs1
    exact this.congr (fun n => (h_term n).symm)
  -- ζ(s) = Σ 1/n^s
  rw [zeta_eq_tsum_one_div_nat_cpow hs1]
  calc ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm h_summ_norm
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
        congr 1; funext n; exact h_term n

/-- **Monotonicity of the ζ-Dirichlet series in the real argument.**
For `1 < σ ≤ τ`, `Σ 1/n^τ ≤ Σ 1/n^σ`. -/
theorem tsum_one_div_nat_rpow_antitone {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ τ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ σ := by
  have hτ : 1 < τ := lt_of_lt_of_le hσ hστ
  have h_summ_σ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  have h_summ_τ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ τ) :=
    Real.summable_one_div_nat_rpow.mpr hτ
  refine Summable.tsum_le_tsum ?_ h_summ_τ h_summ_σ
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hσ_pos : 0 < σ := by linarith
    have hτ_pos : 0 < τ := by linarith
    simp [Real.zero_rpow (ne_of_gt hσ_pos), Real.zero_rpow (ne_of_gt hτ_pos)]
  · have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_pow_le : (n : ℝ) ^ σ ≤ (n : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le hn_one hστ
    have h_pow_σ_pos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn_pos _
    have h_pow_τ_pos : 0 < (n : ℝ) ^ τ := Real.rpow_pos_of_pos hn_pos _
    rw [div_le_div_iff₀ h_pow_τ_pos h_pow_σ_pos]
    linarith

/-- **ζ(2) upper bound for ζ on `Re s ≥ 2`.**
Combining `norm_zeta_le_zeta_re_of_two_le_re` with monotonicity. -/
theorem norm_zeta_le_zeta_two_of_two_le_re
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) := by
  calc ‖riemannZeta s‖
      ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := norm_zeta_le_zeta_re_of_two_le_re hs
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) :=
        tsum_one_div_nat_rpow_antitone (by norm_num : (1:ℝ) < 2) hs

#print axioms norm_zeta_le_zeta_re_of_two_le_re
#print axioms tsum_one_div_nat_rpow_antitone
#print axioms norm_zeta_le_zeta_two_of_two_le_re

/-! ## Phase 2: bound on `Re s = -1` via FE + Stirling

Classical FE: `ζ(1-s) = 2·(2π)^(-s)·Γ(s)·cos(πs/2)·ζ(s)`.

Rearranged with `u := 1 - s` (so `s = 1 - u`): for `u` not `1+n`, `u ≠ 0`,
```
  ζ(u) = 2·(2π)^(u-1)·Γ(1-u)·sin(πu/2)·ζ(1-u).
```

For `u = -1 + iγ` with `|γ| ≥ 1`:
* `|(2π)^(u-1)| = (2π)^(-2)` (constant).
* `|sin(πu/2)| ≤ cosh(π|γ|/2) ≤ exp(π|γ|/2)`.
* `|Γ(1-u)| = |Γ(2-iγ)|` ≤ Stirling bound `C·|γ|^(3/2)·exp(-π|γ|/2)`.
* `|ζ(1-u)| ≤ ζ(2)` (Phase 1).

Product: polynomial `|γ|^(3/2)` (the two exp factors cancel). -/

section PhaseTwo

/-- **Cosh bound via exp of absolute value.** -/
private lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith [Real.exp_pos |x|]

/-- **Phase 2a: `|sin(π·(σ + iγ)/2)| ≤ exp(π|γ|/2)` for real σ, γ.**
Because `sin(a + ib) = sin a · cosh b + i cos a · sinh b`, the norm is
`√(sin²a·cosh²b + cos²a·sinh²b) ≤ cosh b ≤ exp |b|`. -/
theorem norm_sin_pi_half_le_exp (σ γ : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (γ : ℂ) * Complex.I) / 2)‖ ≤
      Real.exp (Real.pi * |γ| / 2) := by
  have h_arg : (Real.pi : ℂ) * ((σ : ℂ) + (γ : ℂ) * Complex.I) / 2 =
      ((Real.pi * σ / 2 : ℝ) : ℂ) + ((Real.pi * γ / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h_arg, Complex.sin_add_mul_I]
  -- compute norm of sin(a)·cosh(b) + i·cos(a)·sinh(b) for real a, b
  set a : ℝ := Real.pi * σ / 2
  set b : ℝ := Real.pi * γ / 2
  have h_sina : Complex.sin (a : ℂ) = ((Real.sin a : ℝ) : ℂ) := by
    exact_mod_cast Complex.ofReal_sin a
  have h_cosa : Complex.cos (a : ℂ) = ((Real.cos a : ℝ) : ℂ) := by
    exact_mod_cast Complex.ofReal_cos a
  have h_coshb : Complex.cosh (b : ℂ) = ((Real.cosh b : ℝ) : ℂ) := by
    exact_mod_cast Complex.ofReal_cosh b
  have h_sinhb : Complex.sinh (b : ℂ) = ((Real.sinh b : ℝ) : ℂ) := by
    exact_mod_cast Complex.ofReal_sinh b
  rw [h_sina, h_cosa, h_coshb, h_sinhb]
  -- norm² = sin²a·cosh²b + cos²a·sinh²b
  have h_normsq : ‖(((Real.sin a : ℝ) : ℂ) * ((Real.cosh b : ℝ) : ℂ) +
      ((Real.cos a : ℝ) : ℂ) * ((Real.sinh b : ℝ) : ℂ) * Complex.I)‖^2 =
      (Real.sin a)^2 * (Real.cosh b)^2 + (Real.cos a)^2 * (Real.sinh b)^2 := by
    have hrw : ((Real.sin a : ℝ) : ℂ) * ((Real.cosh b : ℝ) : ℂ) +
        ((Real.cos a : ℝ) : ℂ) * ((Real.sinh b : ℝ) : ℂ) * Complex.I =
        ((Real.sin a * Real.cosh b : ℝ) : ℂ) +
          ((Real.cos a * Real.sinh b : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hrw, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring
  -- Bound: sin²a·cosh²b + cos²a·sinh²b ≤ cosh²b
  -- since sinh²b = cosh²b - 1 ≤ cosh²b, and sin²a + cos²a = 1.
  have h_upper : (Real.sin a)^2 * (Real.cosh b)^2 + (Real.cos a)^2 * (Real.sinh b)^2 ≤
      (Real.cosh b)^2 := by
    have h_sinhsq : (Real.sinh b)^2 = (Real.cosh b)^2 - 1 := by
      have := Real.cosh_sq_sub_sinh_sq b
      linarith
    rw [h_sinhsq]
    have h_sc : (Real.sin a)^2 + (Real.cos a)^2 = 1 := Real.sin_sq_add_cos_sq a
    have h_cos_nn : (Real.cos a)^2 ≥ 0 := sq_nonneg _
    have h_cosh_sq_ge : (Real.cosh b)^2 ≥ 1 := by
      have := Real.one_le_cosh b; nlinarith
    nlinarith [sq_nonneg (Real.sin a), sq_nonneg (Real.cos a),
      Real.sin_sq_add_cos_sq a]
  have h_target_sq : ‖(((Real.sin a : ℝ) : ℂ) * ((Real.cosh b : ℝ) : ℂ) +
      ((Real.cos a : ℝ) : ℂ) * ((Real.sinh b : ℝ) : ℂ) * Complex.I)‖^2 ≤
      (Real.cosh b)^2 := by rw [h_normsq]; exact h_upper
  have h_nn : 0 ≤ Real.cosh b := (Real.cosh_pos b).le
  have h_norm_le_cosh : ‖(((Real.sin a : ℝ) : ℂ) * ((Real.cosh b : ℝ) : ℂ) +
      ((Real.cos a : ℝ) : ℂ) * ((Real.sinh b : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.cosh b :=
    abs_le_of_sq_le_sq' h_target_sq h_nn |>.2
  -- cosh b ≤ exp |b|, and |b| = π|γ|/2
  have h_abs_b : |b| = Real.pi * |γ| / 2 := by
    simp [b, abs_mul, abs_div, abs_of_pos Real.pi_pos]
  calc ‖(((Real.sin a : ℝ) : ℂ) * ((Real.cosh b : ℝ) : ℂ) +
        ((Real.cos a : ℝ) : ℂ) * ((Real.sinh b : ℝ) : ℂ) * Complex.I)‖
      ≤ Real.cosh b := h_norm_le_cosh
    _ ≤ Real.exp |b| := cosh_le_exp_abs b
    _ = Real.exp (Real.pi * |γ| / 2) := by rw [h_abs_b]

#print axioms norm_sin_pi_half_le_exp

/-- **Phase 2e: polynomial bound on ζ at `Re s = -1`.**
For `u = -1 + iγ` with `|γ| ≥ T₀`, `|ζ(u)| ≤ C · |γ|^(3/2)`. -/
theorem zeta_polynomial_bound_neg_one :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ γ : ℝ, T₀ ≤ |γ| →
        ‖riemannZeta ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C * |γ|^((3:ℝ)/2) := by
  obtain ⟨_C_lo, C_Γ, T_Γ, _hClo, hCΓ, hTΓ, hbnd⟩ :=
    ZD.StirlingBound.gamma_stirling_bound
      (hUpper := ZD.StirlingBound.gammaRatioUpperHalf_proved) (2 : ℝ) (by norm_num)
  -- The ζ(2) sum is positive (bounded below by the n=1 term)
  set ζ2 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)
  refine ⟨2 * (2 * Real.pi)^(-(2:ℝ)) * C_Γ * max ζ2 1, max 1 T_Γ,
    by positivity, lt_max_of_lt_left one_pos, ?_⟩
  intro γ hγ
  have hγ_one : 1 ≤ |γ| := le_of_max_le_left hγ
  have hγ_Γ : T_Γ ≤ |γ| := le_of_max_le_right hγ
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le one_pos hγ_one
  -- s := 2 - iγ, u := -1 + iγ
  set s : ℂ := 2 - (γ : ℂ) * Complex.I with hs_def
  set u : ℂ := (-1 : ℂ) + (γ : ℂ) * Complex.I
  have h_1ms : (1 : ℂ) - s = u := by simp [hs_def, u]; ring
  have h_s_re : s.re = 2 := by simp [hs_def]
  -- Preconditions for FE
  have h_s_ne_neg : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n h
    have h_re := congrArg Complex.re h
    rw [h_s_re, Complex.neg_re, Complex.natCast_re] at h_re
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_s_ne_one : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h; rw [h_s_re] at this; norm_num at this
  have h_fe := riemannZeta_one_sub h_s_ne_neg h_s_ne_one
  rw [h_1ms] at h_fe
  -- h_fe : riemannZeta u = 2 * (2π)^(-s) * Γ(s) * cos(πs/2) * ζ(s)
  -- Take norms
  have h_norm_eq : ‖riemannZeta u‖ =
      2 * ‖((2 * Real.pi : ℂ))^(-s)‖ * ‖Complex.Gamma s‖ *
        ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ * ‖riemannZeta s‖ := by
    rw [h_fe]
    repeat rw [norm_mul]
    simp
  rw [h_norm_eq]
  -- Bound each factor
  -- (a) ‖(2π)^(-s)‖ = (2π)^(-2)
  have h_twopi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_twopi_norm : ‖((2 * Real.pi : ℂ))^(-s)‖ = (2 * Real.pi) ^ (-(2:ℝ)) := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h_twopi_pos]
    rw [Complex.neg_re, h_s_re]
  rw [h_twopi_norm]
  -- (b) ‖Γ(s)‖ bound via Stirling
  have h_s_as_mk : s = (⟨2, -γ⟩ : ℂ) := by
    apply Complex.ext <;> simp [hs_def, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have h_abs_neg_γ : |(-γ)| = |γ| := abs_neg γ
  have hbnd_at := (hbnd (-γ) (by rw [h_abs_neg_γ]; exact hγ_Γ)).2
  rw [h_abs_neg_γ] at hbnd_at
  have h_Γ_bound : ‖Complex.Gamma s‖ ≤
      C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2) := by
    rw [h_s_as_mk]
    convert hbnd_at using 2
    norm_num
  -- (c) ‖cos(πs/2)‖ = ‖sin(π·u/2)‖ ≤ exp(π|γ|/2)
  have h_cos_eq : Complex.cos ((Real.pi : ℂ) * s / 2) =
      Complex.sin ((Real.pi : ℂ) * u / 2) := by
    have hrw : (Real.pi : ℂ) * s / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * u / 2 := by
      rw [← h_1ms]; ring
    rw [hrw]
    exact Complex.cos_pi_div_two_sub _
  have h_u_form : u = ((-1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by push_cast [u]; ring
  have h_cos_bound : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ Real.exp (Real.pi * |γ| / 2) := by
    rw [h_cos_eq, h_u_form]
    exact norm_sin_pi_half_le_exp (-1 : ℝ) γ
  -- (d) ‖ζ(s)‖ ≤ ζ(2)
  have h_zeta_bound : ‖riemannZeta s‖ ≤ ζ2 :=
    norm_zeta_le_zeta_two_of_two_le_re (s := s) (by rw [h_s_re])
  have h_zeta_bound_max : ‖riemannZeta s‖ ≤ max ζ2 1 :=
    le_trans h_zeta_bound (le_max_left _ _)
  -- Nonnegativity
  have h_twopi_pow_nn : (0:ℝ) ≤ (2 * Real.pi) ^ (-(2:ℝ)) := by positivity
  have h_γ_pow_nn : (0:ℝ) ≤ |γ| ^ ((3:ℝ)/2) := Real.rpow_nonneg (abs_nonneg _) _
  have h_Γ_nn : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have h_cos_nn : 0 ≤ ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ := norm_nonneg _
  have h_ζ_nn : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have h_exp_neg_pos : 0 < Real.exp (-Real.pi * |γ| / 2) := Real.exp_pos _
  have h_exp_pos_pos : 0 < Real.exp (Real.pi * |γ| / 2) := Real.exp_pos _
  have hmaxζ2_pos : 0 < max ζ2 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- Chain of mul_le_mul applications
  have h_step_ab : 2 * (2 * Real.pi)^(-(2:ℝ)) * ‖Complex.Gamma s‖ ≤
      2 * (2 * Real.pi)^(-(2:ℝ)) *
        (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) :=
    mul_le_mul_of_nonneg_left h_Γ_bound (by positivity)
  have h_rhs_ab_nn : 0 ≤ 2 * (2 * Real.pi)^(-(2:ℝ)) *
      (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) := by positivity
  have h_step_abc : 2 * (2 * Real.pi)^(-(2:ℝ)) * ‖Complex.Gamma s‖ *
        ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤
      2 * (2 * Real.pi)^(-(2:ℝ)) *
        (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) *
        Real.exp (Real.pi * |γ| / 2) :=
    mul_le_mul h_step_ab h_cos_bound h_cos_nn h_rhs_ab_nn
  have h_rhs_abc_nn : 0 ≤ 2 * (2 * Real.pi)^(-(2:ℝ)) *
      (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) *
      Real.exp (Real.pi * |γ| / 2) := by positivity
  have h_step_all : 2 * (2 * Real.pi)^(-(2:ℝ)) * ‖Complex.Gamma s‖ *
        ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ * ‖riemannZeta s‖ ≤
      2 * (2 * Real.pi)^(-(2:ℝ)) *
        (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) *
        Real.exp (Real.pi * |γ| / 2) * max ζ2 1 :=
    mul_le_mul h_step_abc h_zeta_bound_max h_ζ_nn h_rhs_abc_nn
  -- Algebra: simplify the RHS
  have h_exp_cancel : Real.exp (-Real.pi * |γ| / 2) * Real.exp (Real.pi * |γ| / 2) = 1 := by
    rw [← Real.exp_add]
    have : -Real.pi * |γ| / 2 + Real.pi * |γ| / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  have h_rhs_simp : 2 * (2 * Real.pi)^(-(2:ℝ)) *
        (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) *
        Real.exp (Real.pi * |γ| / 2) * max ζ2 1 =
      2 * (2 * Real.pi)^(-(2:ℝ)) * C_Γ * max ζ2 1 * |γ|^((3:ℝ)/2) := by
    have : 2 * (2 * Real.pi)^(-(2:ℝ)) *
          (C_Γ * |γ|^((3:ℝ)/2) * Real.exp (-Real.pi * |γ| / 2)) *
          Real.exp (Real.pi * |γ| / 2) * max ζ2 1 =
        2 * (2 * Real.pi)^(-(2:ℝ)) * C_Γ * |γ|^((3:ℝ)/2) *
          (Real.exp (-Real.pi * |γ| / 2) * Real.exp (Real.pi * |γ| / 2)) * max ζ2 1 := by ring
    rw [this, h_exp_cancel]
    ring
  linarith [h_step_all, h_rhs_simp]

#print axioms zeta_polynomial_bound_neg_one

end PhaseTwo

/-! ## Phase 3 + 4 (outline): regularize and apply Phragmén–Lindelöf

The classical route for `|ζ(σ+iγ)| ≤ C·|γ|^N` on `σ ∈ (0,1)`: apply
Phragmén–Lindelöf to the regularizer
```
F(s) := ζ(s)·(s-1) / (s+2)^3.
```
* Holomorphicity: ζ is meromorphic with a simple pole at `s = 1`; the `(s-1)`
  factor yields a removable singularity. The denominator `(s+2)^3` vanishes
  only at `s = -2 ∉ [-1, 2]`, so `F` is holomorphic on the open strip.
* Edge bound on `Re s = 2`: `|F| ≤ ζ(2)·(1+|γ|)/|s+2|^3 → 0` as `|γ|→∞`,
  and `F` is continuous, hence bounded on `Re s = 2` by some constant.
  (Phase 1 supplies `|ζ(s)| ≤ ζ(2)` on `Re s ≥ 2`.)
* Edge bound on `Re s = -1`: by Phase 2 above, `|ζ(s)| ≤ C·|γ|^(3/2)`, so
  `|F| ≤ C·|γ|^(3/2)·(2+|γ|)/|s+2|^3 → 0`. Combined with continuity at
  bounded |γ|, `|F|` is bounded on `Re s = -1`.
* Interior subexponential growth: classical — ζ has polynomial growth in any
  closed substrip. Not currently packaged in Mathlib; stated below as the
  named `zetaSubexponentialInStrip` target.

Phragmén–Lindelöf (`Complex.PhragmenLindelof.vertical_strip`) then gives
`|F(s)| ≤ C` on the closed strip, from which
`|ζ(σ+iγ)| = |F(s)|·|s+2|^3/|s-1| ≤ C·|s+2|^3/|s-1|`, polynomial in `|γ|`.

This file stops at Phases 1+2. Phase 3 (`riemannZeta_mul_sub_one_differentiable`,
the removable singularity at `s=1`) and Phase 4 (PL application) are the remaining
classical steps — known formalizable but substantial. -/

/-! ### Phase 3: the regularizer `F(s) := ζ(s)·(s-1)/(s+2)^3`.

Pointwise definition has a discontinuity at `s = 1` (value `0` instead of the
residue-based value `1/27`). We extend with `Function.update` to the
analytically correct value. The resulting function is entire except at
`s = -2` (denominator zero). -/

/-- Core pointwise expression (discontinuous at `s = 1`). -/
noncomputable def zetaRegularizerCore (s : ℂ) : ℂ :=
  riemannZeta s * (s - 1) / (s + 2) ^ 3

/-- Extended regularizer with analytic value `1/27` at `s = 1`
(the removable-singularity value, since `lim (s-1)·ζ(s) = 1` and `(1+2)^3 = 27`). -/
noncomputable def zetaRegularizer : ℂ → ℂ :=
  Function.update zetaRegularizerCore 1 (1 / 27)

/-- Value at `s = 1` by definition. -/
lemma zetaRegularizer_at_one : zetaRegularizer 1 = 1 / 27 := by
  simp [zetaRegularizer]

/-- On `s ≠ 1`, `zetaRegularizer` agrees with `zetaRegularizerCore`. -/
lemma zetaRegularizer_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaRegularizer s = zetaRegularizerCore s := by
  unfold zetaRegularizer
  exact Function.update_of_ne hs _ _

/-- `zetaRegularizerCore` is differentiable everywhere except `s = 1` and `s = -2`. -/
lemma zetaRegularizerCore_differentiableAt
    {s : ℂ} (hs1 : s ≠ 1) (hs2 : s ≠ -2) :
    DifferentiableAt ℂ zetaRegularizerCore s := by
  unfold zetaRegularizerCore
  have h_zeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have h_sub : DifferentiableAt ℂ (fun w : ℂ => w - 1) s :=
    differentiableAt_id.sub (differentiableAt_const 1)
  have h_mul : DifferentiableAt ℂ (fun w : ℂ => riemannZeta w * (w - 1)) s :=
    h_zeta.mul h_sub
  have h_den_ne : (s + 2) ^ 3 ≠ 0 := pow_ne_zero _ (by
    intro h
    have : s = -2 := by
      have := sub_eq_zero.mpr h
      linear_combination h
    exact hs2 this)
  have h_den : DifferentiableAt ℂ (fun w : ℂ => (w + 2) ^ 3) s :=
    (differentiableAt_id.add (differentiableAt_const 2)).pow 3
  exact h_mul.div h_den h_den_ne

/-- `zetaRegularizerCore s → 1/27` as `s → 1`, `s ≠ 1`. -/
lemma zetaRegularizerCore_tendsto_one :
    Filter.Tendsto zetaRegularizerCore (nhdsWithin 1 {1}ᶜ) (nhds (1 / 27)) := by
  have h_res : Filter.Tendsto (fun s => (s - 1) * riemannZeta s)
      (nhdsWithin 1 {1}ᶜ) (nhds 1) := riemannZeta_residue_one
  have h_den : Filter.Tendsto (fun s : ℂ => (s + 2) ^ 3)
      (nhdsWithin 1 {1}ᶜ) (nhds 27) := by
    have : Filter.Tendsto (fun s : ℂ => (s + 2) ^ 3) (nhds 1) (nhds ((1 + 2) ^ 3)) :=
      ((continuous_id.add continuous_const).pow 3).continuousAt.tendsto
    have h_val : ((1 : ℂ) + 2) ^ 3 = 27 := by norm_num
    rw [h_val] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h_quot := h_res.div h_den (by norm_num : (27 : ℂ) ≠ 0)
  -- h_quot : Tendsto ((fun s => (s-1)·ζ(s)) / (fun s => (s+2)^3)) ... (nhds (1/27))
  have h_eq : ((fun s : ℂ => (s - 1) * riemannZeta s) /
      fun s : ℂ => (s + 2) ^ 3) = zetaRegularizerCore := by
    funext s
    unfold zetaRegularizerCore
    simp [Pi.div_apply]
    ring
  rw [h_eq] at h_quot
  exact h_quot

/-- `zetaRegularizer` is continuous at `s = 1`. -/
lemma zetaRegularizer_continuousAt_one : ContinuousAt zetaRegularizer 1 := by
  rw [← continuousWithinAt_compl_self]
  -- ContinuousWithinAt zetaRegularizer {1}ᶜ 1
  -- ⟺ Tendsto zetaRegularizer (nhdsWithin 1 {1}ᶜ) (nhds (zetaRegularizer 1))
  unfold ContinuousWithinAt
  rw [zetaRegularizer_at_one]
  -- goal: Tendsto zetaRegularizer (nhdsWithin 1 {1}ᶜ) (nhds (1/27))
  have h_eq : zetaRegularizer =ᶠ[nhdsWithin 1 {1}ᶜ] zetaRegularizerCore := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact zetaRegularizer_of_ne_one hx
  exact (zetaRegularizerCore_tendsto_one).congr' h_eq.symm

/-- **Phase 3 main: the extended regularizer is differentiable away from `s = -2`.** -/
theorem zetaRegularizer_differentiableAt {s : ℂ} (hs : s ≠ -2) :
    DifferentiableAt ℂ zetaRegularizer s := by
  by_cases hs1 : s = 1
  · subst hs1
    -- Use removable singularity: punctured-nhd-diff + continuousAt ⇒ analyticAt.
    have h_punct : ∀ᶠ z in nhdsWithin (1 : ℂ) {1}ᶜ, DifferentiableAt ℂ zetaRegularizer z := by
      -- The set {z | z ≠ 1, z ≠ -2} is open and contains all z near 1 except 1 itself.
      have h_ne_neg2 : ∀ᶠ z : ℂ in nhds (1 : ℂ), z ≠ -2 := by
        have : (1 : ℂ) ≠ -2 := by
          intro h; apply_fun Complex.re at h; norm_num at h
        exact isOpen_ne.eventually_mem this
      have h_ne_neg2' : ∀ᶠ z : ℂ in nhdsWithin 1 {1}ᶜ, z ≠ -2 :=
        h_ne_neg2.filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, h_ne_neg2'] with z hz1 hz2
      -- On z ≠ 1, zetaRegularizer z = zetaRegularizerCore z
      have h_eq_on : zetaRegularizer =ᶠ[nhds z] zetaRegularizerCore := by
        have h_open : IsOpen ({w : ℂ | w ≠ 1}) := isOpen_ne
        filter_upwards [h_open.mem_nhds hz1] with w hw
        exact zetaRegularizer_of_ne_one hw
      rw [h_eq_on.differentiableAt_iff]
      exact zetaRegularizerCore_differentiableAt hz1 hz2
    have h_cont : ContinuousAt zetaRegularizer 1 := zetaRegularizer_continuousAt_one
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      h_punct h_cont).differentiableAt
  · -- s ≠ 1: zetaRegularizer = zetaRegularizerCore eventually near s.
    have h_eq_on : zetaRegularizer =ᶠ[nhds s] zetaRegularizerCore := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
      exact zetaRegularizer_of_ne_one hw
    rw [h_eq_on.differentiableAt_iff]
    exact zetaRegularizerCore_differentiableAt hs1 hs

#print axioms zetaRegularizerCore_tendsto_one
#print axioms zetaRegularizer_continuousAt_one
#print axioms zetaRegularizer_differentiableAt

/-! ### Phase 4a: right-edge bound (Re s = 2).

For `s = 2 + iγ`: `|s-1|² = 1+γ²` and `|s+2|² = 16+γ²`, so
`|s-1|/|s+2|³ = √(1+γ²)/(16+γ²)^(3/2) ≤ 1/(16+γ²) ≤ 1/16`.
Combined with `|ζ(s)| ≤ ζ(2)` (Phase 1). -/

/-- **Phase 4a: explicit bound on `|zetaRegularizer|` at `Re s = 2`.**
Uses Phase 1 `|ζ| ≤ ζ(2)` and the explicit algebraic decay of `|s-1|/|s+2|³`. -/
theorem zetaRegularizer_bound_right (γ : ℝ) :
    ‖zetaRegularizer ((2 : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
      (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) / 16 := by
  set s : ℂ := (2 : ℂ) + (γ : ℂ) * Complex.I with hs_def
  have h_s_ne_one : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hs_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
  rw [zetaRegularizer_of_ne_one h_s_ne_one]
  unfold zetaRegularizerCore
  have h_s_re : s.re = 2 := by simp [hs_def]
  -- |ζ(s)| ≤ ζ(2)
  have h_zeta : ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) :=
    norm_zeta_le_zeta_two_of_two_le_re (by rw [h_s_re])
  -- ‖s - 1‖² = 1 + γ²
  have h_sm1_sq : ‖s - 1‖^2 = 1 + γ^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show s - 1 = ((1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I from by
      rw [hs_def]; push_cast; ring]
    rw [Complex.normSq_add_mul_I]
    ring
  -- ‖s + 2‖² = 16 + γ²
  have h_sp2_sq : ‖s + 2‖^2 = 16 + γ^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show s + 2 = ((4 : ℝ) : ℂ) + (γ : ℂ) * Complex.I from by
      rw [hs_def]; push_cast; ring]
    rw [Complex.normSq_add_mul_I]
    ring
  have h_sm1_nn : 0 ≤ ‖s - 1‖ := norm_nonneg _
  have h_sp2_nn : 0 ≤ ‖s + 2‖ := norm_nonneg _
  have h_γ2_nn : 0 ≤ γ^2 := sq_nonneg _
  -- ‖s - 1‖² ≤ ‖s + 2‖² (since 1+γ² ≤ 16+γ²)
  have h_compare : ‖s - 1‖^2 ≤ ‖s + 2‖^2 := by rw [h_sm1_sq, h_sp2_sq]; linarith
  -- Hence ‖s - 1‖ ≤ ‖s + 2‖
  have h_le : ‖s - 1‖ ≤ ‖s + 2‖ := by
    exact abs_le_of_sq_le_sq' h_compare h_sp2_nn |>.2
  -- ‖s + 2‖^2 ≥ 16
  have h_sp2_sq_ge : (16 : ℝ) ≤ ‖s + 2‖^2 := by rw [h_sp2_sq]; linarith
  have h_sp2_ge : (4 : ℝ) ≤ ‖s + 2‖ := by
    have h4_nn : (0 : ℝ) ≤ 4 := by norm_num
    have : (4 : ℝ)^2 ≤ ‖s + 2‖^2 := by norm_num; exact h_sp2_sq_ge
    exact abs_le_of_sq_le_sq' this h_sp2_nn |>.2
  have h_sp2_pos : 0 < ‖s + 2‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) h_sp2_ge
  have h_sp2_ne : (s + 2 : ℂ) ≠ 0 := by
    intro h; rw [h] at h_sp2_pos; simp at h_sp2_pos
  have h_sp2_pow_ne : ((s + 2)^3 : ℂ) ≠ 0 := pow_ne_zero _ h_sp2_ne
  -- ‖ζ·(s-1)/(s+2)^3‖ = ‖ζ‖·‖s-1‖/‖s+2‖^3
  rw [norm_div, norm_mul, norm_pow]
  -- Target: ‖ζ‖·‖s-1‖ / ‖s+2‖³ ≤ ζ(2)/16
  -- Strategy: ‖s-1‖ ≤ ‖s+2‖, so ‖ζ‖·‖s-1‖/‖s+2‖³ ≤ ‖ζ‖/‖s+2‖² ≤ ‖ζ‖/16 ≤ ζ(2)/16
  have h_sp2_pow_pos : 0 < ‖s + 2‖^3 := by positivity
  have h_sp2_sq_pos : 0 < ‖s + 2‖^2 := by positivity
  have h_zeta_nn : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  -- Step 1: ‖ζ‖·‖s-1‖/‖s+2‖³ ≤ ‖ζ‖·‖s+2‖/‖s+2‖³ = ‖ζ‖/‖s+2‖²
  have h_step1 : ‖riemannZeta s‖ * ‖s - 1‖ / ‖s + 2‖^3 ≤
      ‖riemannZeta s‖ / ‖s + 2‖^2 := by
    rw [div_le_div_iff₀ h_sp2_pow_pos h_sp2_sq_pos]
    have : ‖riemannZeta s‖ * ‖s - 1‖ * ‖s + 2‖^2 ≤
        ‖riemannZeta s‖ * ‖s + 2‖ * ‖s + 2‖^2 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_le h_zeta_nn)
      positivity
    calc ‖riemannZeta s‖ * ‖s - 1‖ * ‖s + 2‖^2
        ≤ ‖riemannZeta s‖ * ‖s + 2‖ * ‖s + 2‖^2 := this
      _ = ‖riemannZeta s‖ * ‖s + 2‖^3 := by ring
  -- Step 2: ‖ζ‖/‖s+2‖² ≤ ‖ζ‖/16
  have h_step2 : ‖riemannZeta s‖ / ‖s + 2‖^2 ≤ ‖riemannZeta s‖ / 16 := by
    apply div_le_div_of_nonneg_left h_zeta_nn (by norm_num) h_sp2_sq_ge
  -- Step 3: ‖ζ‖/16 ≤ ζ(2)/16
  have h_step3 : ‖riemannZeta s‖ / 16 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) / 16 := by
    apply div_le_div_of_nonneg_right h_zeta (by norm_num)
  linarith

#print axioms zetaRegularizer_bound_right

/-! ### Phase 4b: left-edge bound (Re s = -1), asymptotic part.

For `s = -1 + iγ`:
* `|s-1|² = 4+γ²`, `|s+2|² = 1+γ²`.
* `√(4+γ²) ≤ 2·√(1+γ²)` (from `4+γ² ≤ 4·(1+γ²)`).
* Hence `|s-1|/|s+2|³ ≤ 2/(1+γ²)`.
* For `|γ| ≥ 1`: `|γ|^(3/2)·2/(1+γ²) ≤ 2/|γ|^(1/2) ≤ 2`.

So for `|γ| ≥ max(T_ζ, 1)`, `|zetaRegularizer| ≤ 2·C_ζ`. -/

/-- **Phase 4b (large-γ): asymptotic bound on `|zetaRegularizer|` at `Re s = -1`.**
For `|γ| ≥ max(T_ζ, 1)` where `T_ζ` is from `zeta_polynomial_bound_neg_one`. -/
theorem zetaRegularizer_bound_left_asymptotic :
    ∃ (C₀ T₀ : ℝ), 0 < C₀ ∧ 0 < T₀ ∧
      ∀ γ : ℝ, T₀ ≤ |γ| →
        ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C₀ := by
  obtain ⟨C_ζ, T_ζ, hCζ, hTζ, hζb⟩ := zeta_polynomial_bound_neg_one
  refine ⟨2 * C_ζ, max 1 T_ζ, by positivity, lt_max_of_lt_left one_pos, ?_⟩
  intro γ hγ
  have hγ_one : 1 ≤ |γ| := le_of_max_le_left hγ
  have hγ_ζ : T_ζ ≤ |γ| := le_of_max_le_right hγ
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le one_pos hγ_one
  set s : ℂ := (-1 : ℂ) + (γ : ℂ) * Complex.I with hs_def
  have h_s_ne_one : s ≠ 1 := by
    intro h
    have h_re := congrArg Complex.re h
    simp [hs_def] at h_re
    linarith
  rw [zetaRegularizer_of_ne_one h_s_ne_one]
  unfold zetaRegularizerCore
  -- ‖ζ(s)‖ ≤ C_ζ · |γ|^(3/2)
  have h_zeta : ‖riemannZeta s‖ ≤ C_ζ * |γ|^((3:ℝ)/2) := hζb γ hγ_ζ
  -- ‖s - 1‖² = 4 + γ²
  have h_sm1_sq : ‖s - 1‖^2 = 4 + γ^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show s - 1 = ((-2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I from by
      rw [hs_def]; push_cast; ring]
    rw [Complex.normSq_add_mul_I]
    ring
  -- ‖s + 2‖² = 1 + γ²
  have h_sp2_sq : ‖s + 2‖^2 = 1 + γ^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show s + 2 = ((1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I from by
      rw [hs_def]; push_cast; ring]
    rw [Complex.normSq_add_mul_I]
    ring
  have h_sm1_nn : 0 ≤ ‖s - 1‖ := norm_nonneg _
  have h_sp2_nn : 0 ≤ ‖s + 2‖ := norm_nonneg _
  -- ‖s - 1‖² ≤ 4 · ‖s + 2‖² (since 4+γ² ≤ 4·(1+γ²))
  have h_compare : ‖s - 1‖^2 ≤ 4 * ‖s + 2‖^2 := by
    rw [h_sm1_sq, h_sp2_sq]; nlinarith
  have h_sm1_le : ‖s - 1‖ ≤ 2 * ‖s + 2‖ := by
    have h2sp2_nn : 0 ≤ 2 * ‖s + 2‖ := by linarith
    have : ‖s - 1‖^2 ≤ (2 * ‖s + 2‖)^2 := by
      rw [mul_pow]; linarith
    exact abs_le_of_sq_le_sq' this h2sp2_nn |>.2
  -- ‖s + 2‖² = 1 + γ² ≥ γ²
  have h_sp2_sq_ge : γ^2 ≤ ‖s + 2‖^2 := by rw [h_sp2_sq]; linarith [sq_nonneg γ]
  have h_γ_nn : 0 ≤ |γ| := abs_nonneg _
  have h_γ_eq_sq : γ^2 = |γ|^2 := (sq_abs γ).symm
  have h_sp2_ge_abs : |γ| ≤ ‖s + 2‖ := by
    have : |γ|^2 ≤ ‖s + 2‖^2 := by rw [← h_γ_eq_sq]; exact h_sp2_sq_ge
    exact abs_le_of_sq_le_sq' this h_sp2_nn |>.2
  have h_sp2_pos : 0 < ‖s + 2‖ := lt_of_lt_of_le hγ_pos h_sp2_ge_abs
  -- Compute: ‖ζ(s-1)/(s+2)^3‖ = ‖ζ‖·‖s-1‖/‖s+2‖³
  rw [norm_div, norm_mul, norm_pow]
  -- Target: ‖ζ‖·‖s-1‖/‖s+2‖³ ≤ 2·C_ζ
  -- Chain: ≤ C_ζ·|γ|^(3/2)·2·‖s+2‖/‖s+2‖³ = 2·C_ζ·|γ|^(3/2)/‖s+2‖²
  --      ≤ 2·C_ζ·|γ|^(3/2)/|γ|² = 2·C_ζ/|γ|^(1/2) ≤ 2·C_ζ (since |γ|≥1)
  have h_zeta_nn : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have h_sp2_pow_pos : 0 < ‖s + 2‖^3 := by positivity
  have h_step1 : ‖riemannZeta s‖ * ‖s - 1‖ / ‖s + 2‖^3 ≤
      C_ζ * |γ|^((3:ℝ)/2) * (2 * ‖s + 2‖) / ‖s + 2‖^3 := by
    apply div_le_div_of_nonneg_right _ h_sp2_pow_pos.le
    exact mul_le_mul h_zeta h_sm1_le h_sm1_nn (by positivity)
  have h_γ_pow_nn : 0 ≤ |γ|^((3:ℝ)/2) := Real.rpow_nonneg h_γ_nn _
  have h_step2 : C_ζ * |γ|^((3:ℝ)/2) * (2 * ‖s + 2‖) / ‖s + 2‖^3 =
      2 * C_ζ * |γ|^((3:ℝ)/2) / ‖s + 2‖^2 := by
    field_simp
  rw [h_step2] at h_step1
  -- Now bound 2·C_ζ·|γ|^(3/2)/‖s+2‖² ≤ 2·C_ζ
  have h_sp2_sq_ge_γsq : |γ|^2 ≤ ‖s + 2‖^2 := by rw [← h_γ_eq_sq]; exact h_sp2_sq_ge
  -- |γ|^(3/2) / ‖s+2‖² ≤ |γ|^(3/2) / |γ|^2 = |γ|^(-1/2) ≤ 1 for |γ| ≥ 1
  have h_γsq_pos : 0 < |γ|^2 := by positivity
  have h_step3 : |γ|^((3:ℝ)/2) / ‖s + 2‖^2 ≤ |γ|^((3:ℝ)/2) / |γ|^2 := by
    apply div_le_div_of_nonneg_left h_γ_pow_nn h_γsq_pos h_sp2_sq_ge_γsq
  -- |γ|^(3/2) / |γ|^2 = |γ|^(-1/2)
  have h_γ_pow_simplify : |γ|^((3:ℝ)/2) / |γ|^2 = |γ|^(-(1:ℝ)/2) := by
    rw [show |γ|^(2 : ℕ) = |γ|^(2 : ℝ) from (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_sub hγ_pos]
    congr 1; norm_num
  -- |γ|^(-1/2) ≤ 1 for |γ| ≥ 1
  have h_neg_half : |γ|^(-(1:ℝ)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hγ_one (by norm_num)
  -- Combine
  have h_bound_final : 2 * C_ζ * |γ|^((3:ℝ)/2) / ‖s + 2‖^2 ≤ 2 * C_ζ := by
    calc 2 * C_ζ * |γ|^((3:ℝ)/2) / ‖s + 2‖^2
        = 2 * C_ζ * (|γ|^((3:ℝ)/2) / ‖s + 2‖^2) := by ring
      _ ≤ 2 * C_ζ * (|γ|^((3:ℝ)/2) / |γ|^2) := by
          apply mul_le_mul_of_nonneg_left h_step3 (by positivity)
      _ = 2 * C_ζ * |γ|^(-(1:ℝ)/2) := by rw [h_γ_pow_simplify]
      _ ≤ 2 * C_ζ * 1 := by
          apply mul_le_mul_of_nonneg_left h_neg_half (by positivity)
      _ = 2 * C_ζ := by ring
  linarith

#print axioms zetaRegularizer_bound_left_asymptotic

/-! ### Phase 4b: left-edge bound, compact part. -/

/-- `zetaRegularizer` is continuous everywhere except possibly at `s = -2`. -/
lemma zetaRegularizer_continuousAt {s : ℂ} (hs : s ≠ -2) :
    ContinuousAt zetaRegularizer s :=
  (zetaRegularizer_differentiableAt hs).continuousAt

/-- **Left edge `γ ↦ ‖zetaRegularizer(-1 + iγ)‖` is continuous as a function of `γ`.** -/
lemma continuous_zetaRegularizer_left_edge :
    Continuous (fun γ : ℝ => ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖) := by
  have h_map_cont : Continuous (fun γ : ℝ => ((-1 : ℂ) + (γ : ℂ) * Complex.I)) := by
    have h1 : Continuous (fun γ : ℝ => ((γ : ℂ) * Complex.I)) :=
      Complex.continuous_ofReal.mul continuous_const
    exact continuous_const.add h1
  -- Use that `zetaRegularizer` is continuous at every point ≠ -2, and the left-edge image
  -- never hits -2: -1 + iγ = -2 iff Re = -2 but our Re = -1.
  have h_ne : ∀ γ : ℝ, ((-1 : ℂ) + (γ : ℂ) * Complex.I) ≠ -2 := by
    intro γ h
    have h_re := congrArg Complex.re h
    simp at h_re
  have h_zr_cont : Continuous (fun γ : ℝ => zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun γ => ?_
    have h_arg_ne : ((-1 : ℂ) + (γ : ℂ) * Complex.I) ≠ -2 := h_ne γ
    have h_inner_cont : ContinuousAt (fun γ : ℝ => ((-1 : ℂ) + (γ : ℂ) * Complex.I)) γ :=
      h_map_cont.continuousAt
    exact ContinuousAt.comp (x := γ) (zetaRegularizer_continuousAt h_arg_ne) h_inner_cont
  exact h_zr_cont.norm

/-- **Phase 4b (compact part): bound on `[-T, T]` on the left edge.** -/
theorem zetaRegularizer_bound_left_compact (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, ∀ γ : ℝ, |γ| ≤ T →
      ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ M := by
  have h_cont : Continuous (fun γ : ℝ => ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖) :=
    continuous_zetaRegularizer_left_edge
  have h_compact : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  have h_bdd : BddAbove
      ((fun γ : ℝ => ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖) '' Set.Icc (-T) T) :=
    h_compact.bddAbove_image h_cont.continuousOn
  obtain ⟨M, hM⟩ := h_bdd
  refine ⟨M, fun γ hγ => ?_⟩
  apply hM
  refine Set.mem_image_of_mem _ ?_
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have := abs_le.mp hγ; linarith
  · have := abs_le.mp hγ; linarith

#print axioms zetaRegularizer_bound_left_compact

/-- **Phase 4b (combined): global bound on the left edge.** -/
theorem zetaRegularizer_bound_left :
    ∃ C : ℝ, ∀ γ : ℝ,
      ‖zetaRegularizer ((-1 : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hasymp⟩ := zetaRegularizer_bound_left_asymptotic
  obtain ⟨M, hM⟩ := zetaRegularizer_bound_left_compact T₀ hT₀
  refine ⟨max C₀ M, fun γ => ?_⟩
  by_cases h : T₀ ≤ |γ|
  · exact le_trans (hasymp γ h) (le_max_left _ _)
  · push_neg at h
    exact le_trans (hM γ h.le) (le_max_right _ _)

#print axioms zetaRegularizer_bound_left

/-! ### Phase 4c: Phragmén–Lindelöf application.

Given the subexponential growth hypothesis `zetaSubexponentialInStrip`, apply
`PhragmenLindelof.vertical_strip` on `Re s ∈ (-1, 2)` to obtain a uniform bound on
`zetaRegularizer`. The three hypotheses are:

1. `DiffContOnCl`: follows from `zetaRegularizer_differentiableAt` since `-2 ∉ [-1, 2]`.
2. Subexponential `=O` bound: the strip bound on `zetaRegularizerCore` transfers to
   `zetaRegularizer` via eventuality (for large `|im|`, `s ≠ 1` so the two agree).
3. Edge bounds: `zetaRegularizer_bound_left` and `zetaRegularizer_bound_right`.

Note: `zetaSubexponentialInStrip` and `zetaPolynomialBoundInStrip` are defined below;
the theorems in phases 4c and 4d appear after those definitions.
-/

/-- **Named target: polynomial bound on ζ in the strip.**
For each `σ ∈ (0,1)`, there exist `C, N, T₀` such that for `|γ| ≥ T₀`,
`|ζ(σ + iγ)| ≤ C · |γ|^N`. Classical convexity theorem derivable from
Phragmén–Lindelöf applied to `ζ(s)·(s-1)/(s+2)^3` + Phases 1–2 for edge
bounds. -/
def zetaPolynomialBoundInStrip : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∃ (C N T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ γ : ℝ, T₀ ≤ |γ| →
        ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C * |γ|^N

/-- **Named target: subexponential growth of ζ in the closed strip.** For all
`σ ∈ [-1, 2]` and all `|γ|`, `|ζ(σ+iγ)| ≤ A·exp(B·|γ|^c)` for some `c < 1`.
(The Phragmén–Lindelöf hypothesis in `vertical_strip` needs this plus a
stricter bound `exp(B·exp(c·|γ|))` for `c < π/(b-a) = π/3`.) -/
def zetaSubexponentialInStrip : Prop :=
  ∃ (A B c : ℝ), 0 < A ∧ 0 < B ∧ 0 < c ∧ c < Real.pi / 3 ∧
    ∀ (s : ℂ), (-1 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖riemannZeta s * (s - 1) / (s + 2)^3‖ ≤ A * Real.exp (B * Real.exp (c * |s.im|))

/-- **Phase 4c: uniform bound on `zetaRegularizer` in the strip via Phragmén–Lindelöf.**
Assumes the subexponential growth hypothesis `zetaSubexponentialInStrip`. -/
theorem zetaRegularizer_bound_in_strip (h_subexp : zetaSubexponentialInStrip) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖zetaRegularizer s‖ ≤ C := by
  obtain ⟨A, B, c, hA, hB, hc, hc3, h_bnd⟩ := h_subexp
  obtain ⟨C_left, hCL⟩ := zetaRegularizer_bound_left
  set C_right := (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) / 16
  -- Edge constant: max of left, right, and 1 to guarantee positivity
  set C_edge := max (max C_left C_right) 1
  -- (1) DiffContOnCl on the open strip re ∈ (-1, 2)
  have h_dcoc : DiffContOnCl ℂ zetaRegularizer (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) := by
    apply DifferentiableOn.diffContOnCl
    have h_closure : closure (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) =
        Complex.re ⁻¹' Set.Icc (-1 : ℝ) 2 := by
      rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 2),
        ← (Complex.isOpenMap_re).preimage_closure_eq_closure_preimage Complex.continuous_re _]
    rw [h_closure]
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply zetaRegularizer_differentiableAt
    -- s ≠ -2: since s.re ∈ [-1, 2], but (-2).re = -2 ∉ [-1, 2]
    intro h
    rw [Set.mem_preimage, Set.mem_Icc] at hs
    rw [h] at hs; simp at hs
  -- (2) Subexponential =O bound on the filter
  -- Strategy: zetaRegularizerCore =O exp(...) from h_bnd, and
  -- zetaRegularizerCore =ᶠ zetaRegularizer on the filter (since large |im| ⇒ s ≠ 1)
  have h_bO : zetaRegularizer =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2)]
      fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    set F := Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2)
    -- Eventually in F, z ≠ 1 (since comap |im| atTop forces |im| > 0)
    have h_ne1 : ∀ᶠ z in F, z ≠ 1 := by
      apply Filter.Eventually.filter_mono inf_le_left
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx z hz
      intro heq1
      have : |Complex.im (1 : ℂ)| = x := by rwa [heq1] at hz
      simp at this; linarith
    -- Eventually in F, z is in the closed strip
    have h_strip : ∀ᶠ z in F, -1 ≤ z.re ∧ z.re ≤ 2 := by
      have hmem : Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2 ∈
          Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) :=
        Filter.mem_principal.mpr (Set.Subset.refl _)
      filter_upwards [inf_le_right (a := Filter.comap (abs ∘ Complex.im) Filter.atTop) hmem]
          with z hz
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    -- zetaRegularizerCore =O exp(B * exp(c * |im|)) on F
    have h_core_bO : zetaRegularizerCore =O[F]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨A, ?_⟩
      filter_upwards [h_strip] with z ⟨h1, h2⟩
      simp only [zetaRegularizerCore]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      linarith [h_bnd z h1 h2]
    -- zetaRegularizerCore =ᶠ zetaRegularizer on F (via h_ne1)
    have h_eq : zetaRegularizerCore =ᶠ[F] zetaRegularizer := by
      filter_upwards [h_ne1] with z hz using (zetaRegularizer_of_ne_one hz).symm
    exact h_core_bO.congr' h_eq (Filter.Eventually.of_forall fun _ => rfl)
  -- (3) Apply Phragmén–Lindelöf
  refine ⟨C_edge, by positivity, ?_⟩
  intro s hs_lo hs_hi
  apply PhragmenLindelof.vertical_strip h_dcoc
  · -- Subexponential bound with c < π/(2-(-1)) = π/3
    refine ⟨c, ?_, B, h_bO⟩
    have : (2 : ℝ) - (-1) = 3 := by norm_num
    rw [this]; exact hc3
  · -- Left edge bound: Re z = -1 ⇒ z = -1 + im*I
    intro z hz
    have h_decomp : z = (-1 : ℂ) + (z.im : ℂ) * Complex.I :=
      Complex.ext (by simp [hz]) (by simp)
    rw [h_decomp]
    exact le_trans (hCL z.im) (le_trans (le_max_left _ _) (le_max_left _ _))
  · -- Right edge bound: Re z = 2 ⇒ z = 2 + im*I
    intro z hz
    have h_decomp : z = (2 : ℂ) + (z.im : ℂ) * Complex.I :=
      Complex.ext (by simp [hz]) (by simp)
    rw [h_decomp]
    exact le_trans (zetaRegularizer_bound_right z.im) (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact hs_lo
  · exact hs_hi

#print axioms zetaRegularizer_bound_in_strip

/-! ### Phase 4d: unwind to `zetaPolynomialBoundInStrip`.

From the uniform bound `‖zetaRegularizer s‖ ≤ C_PL` on the strip, recover the
polynomial bound on `ζ` itself. For `σ ∈ (0,1)`, `s = σ + iγ`, `σ ≠ 1`:
* `zetaRegularizer s = zetaRegularizerCore s = ζ(s)·(s-1)/(s+2)^3`.
* Hence `‖ζ(s)‖ ≤ C_PL · ‖s+2‖³ / ‖s-1‖`.
* For `|γ| ≥ 1`: `‖s+2‖ ≤ σ+2+|γ| ≤ 3+|γ| ≤ 4|γ|`, so `‖s+2‖³ ≤ 64|γ|³`.
* `‖s-1‖² = (σ-1)²+γ² ≥ γ² ≥ 1`, so `‖s-1‖ ≥ 1`.
* Result: `‖ζ(s)‖ ≤ 64·C_PL·|γ|³`. -/

/-- **Phase 4d: polynomial bound on ζ in the strip, given subexponential hypothesis.**
Derives `zetaPolynomialBoundInStrip` from `zetaSubexponentialInStrip` via
Phragmén–Lindelöf (Phase 4c) and algebraic unwinding (Phase 4d). -/
theorem zetaPolynomialBoundInStrip_of_subexp (h_subexp : zetaSubexponentialInStrip) :
    zetaPolynomialBoundInStrip := by
  -- Phase 4c: get uniform strip bound on zetaRegularizer
  obtain ⟨C_PL, hC_PL, h_strip_bound⟩ := zetaRegularizer_bound_in_strip h_subexp
  -- Phase 4d: unwind for each σ
  intro σ hσ0 hσ1
  -- Take N = 3, C = 64 * C_PL, T₀ = 1
  refine ⟨64 * C_PL, 3, 1, by positivity, one_pos, ?_⟩
  intro γ hγ
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
  -- s ≠ 1 since s.re = σ < 1
  have hs_ne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [s] at this; linarith
  have hs_re1 : -1 ≤ s.re := by simp [s]; linarith
  have hs_re2 : s.re ≤ 2 := by simp [s]; linarith
  -- zetaRegularizer s = zetaRegularizerCore s
  have h_reg : ‖riemannZeta s * (s - 1) / (s + 2) ^ 3‖ ≤ C_PL := by
    have h := h_strip_bound s hs_re1 hs_re2
    rwa [zetaRegularizer_of_ne_one hs_ne1] at h
  rw [norm_div, norm_mul, norm_pow] at h_reg
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le one_pos hγ
  -- s - 1 ≠ 0 (since im(s-1) = γ ≠ 0 when |γ| ≥ 1)
  have h_sm1_ne : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [s] at this
    rw [this, abs_zero] at hγ; linarith
  -- s + 2 ≠ 0 (since re(s+2) = σ+2 > 0)
  have h_sp2_ne : s + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [s] at this; linarith
  have h_sm1_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr h_sm1_ne
  have h_sp2_pow_pos : 0 < ‖s + 2‖ ^ 3 := by positivity
  -- Rearrange: ‖ζ(s)‖ ≤ C_PL * ‖s+2‖³ / ‖s-1‖
  have h_zeta_bound : ‖riemannZeta s‖ ≤ C_PL * ‖s + 2‖ ^ 3 / ‖s - 1‖ := by
    rw [div_le_iff₀ h_sp2_pow_pos] at h_reg
    rw [le_div_iff₀ h_sm1_pos]; linarith
  -- ‖s+2‖³ ≤ 64 * |γ|³
  have h_sp2_bound : ‖s + 2‖ ^ 3 ≤ 64 * |γ| ^ 3 := by
    have h_sp2_eq : s + 2 = ((σ + 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
      push_cast [s]; ring
    have h_sp2_norm : ‖s + 2‖ ≤ σ + 2 + |γ| := by
      rw [h_sp2_eq]
      calc ‖((σ + 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I‖
          ≤ ‖((σ + 2 : ℝ) : ℂ)‖ + ‖(γ : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = (σ + 2) + |γ| := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by linarith),
                norm_mul, Complex.norm_real, Complex.norm_I, mul_one]; rfl
    calc ‖s + 2‖ ^ 3
        ≤ (4 * |γ|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _)
              (le_trans h_sp2_norm (by nlinarith)) 3
      _ = 64 * |γ| ^ 3 := by ring
  -- ‖s-1‖ ≥ 1
  have h_sm1_bound : 1 ≤ ‖s - 1‖ := by
    have h_sm1_eq : s - 1 = ((σ - 1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
      push_cast [s]; ring
    rw [h_sm1_eq]
    have h_sq : 1 ≤ ‖((σ - 1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq (((σ - 1 : ℝ) : ℂ) + _), Complex.normSq_add_mul_I]
      nlinarith [sq_nonneg (σ - 1), sq_abs γ]
    nlinarith [norm_nonneg (((σ - 1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I),
              sq_nonneg (‖((σ - 1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I‖ - 1)]
  -- Chain the bounds; note |γ|^(3:ℝ) = rpow while |γ|^(3:ℕ) = pow; they agree
  have h_rpow_eq : |γ| ^ (3 : ℕ) = |γ| ^ (3 : ℝ) := by norm_cast
  -- Final bound: C_PL * ‖s+2‖³/‖s-1‖ ≤ 64 * C_PL * |γ|³
  -- Step: use div_le_div (numerator bound, denominator bound)
  have h_final : ‖riemannZeta s‖ ≤ 64 * C_PL * |γ| ^ (3 : ℕ) := by
    calc ‖riemannZeta s‖
        ≤ C_PL * ‖s + 2‖ ^ 3 / ‖s - 1‖ := h_zeta_bound
      _ ≤ C_PL * ‖s + 2‖ ^ 3 / 1 := by
            apply div_le_div_of_nonneg_left _ one_pos h_sm1_bound
            positivity
      _ = C_PL * ‖s + 2‖ ^ 3 := div_one _
      _ ≤ C_PL * (64 * |γ| ^ 3) := by
            nlinarith [mul_le_mul_of_nonneg_left h_sp2_bound (le_of_lt hC_PL)]
      _ = 64 * C_PL * |γ| ^ (3 : ℕ) := by ring
  calc ‖riemannZeta s‖
      ≤ 64 * C_PL * |γ| ^ (3 : ℕ) := h_final
    _ = 64 * C_PL * |γ| ^ (3 : ℝ) := by rw [h_rpow_eq]

#print axioms zetaPolynomialBoundInStrip_of_subexp

/-! ### Euler–Maclaurin route to `zetaPolynomialBoundInStrip`.

An alternative derivation bypassing the subexponential hypothesis. Given
`GRH.EulerMaclaurinDirichlet.euler_maclaurin_dirichlet`, which says that for
`s = σ + iγ` with `σ ∈ (0, 1)` and `s ≠ 1`,
  `‖S s N - ζ(s) - N^(1-s)/(1-s)‖ ≤ C_EM · N^{-σ}` for `N ≥ 2`,
we obtain a polynomial bound on `‖ζ(s)‖` in `|γ|` directly.

**Strategy:** choose `N := ⌊|γ|⌋₊ + 2` (so `|γ| + 1 ≤ N ≤ |γ| + 2`, `N ≥ 2`),
and bound each piece of the triangle inequality
`‖ζ(s)‖ ≤ ‖S s N‖ + ‖N^(1-s)/(1-s)‖ + C_EM · N^{-σ}`.
-/

/-- **Polynomial bound on ζ in the strip via Euler–Maclaurin.**
Discharges `zetaPolynomialBoundInStrip` using only
`GRH.EulerMaclaurinDirichlet.euler_maclaurin_dirichlet` (no Phragmén–Lindelöf,
no subexponential hypothesis).

**Outline.** For `s = σ + iγ` with `|γ| ≥ 2`, choose `N := ⌊|γ|⌋₊ + 2` so that
`|γ| + 1 ≤ N ≤ |γ| + 2` and `N ≥ 2`. Euler–Maclaurin gives
  `‖S s N - ζ(s) - N^{1-s}/(1-s)‖ ≤ (‖s‖/σ + 1) · N^{-σ}`.
Triangle inequality and crude bounds `n^{-σ} ≤ 1`, `N^{1-σ} ≤ N`,
`‖1-s‖ ≥ |γ|` then yield `‖ζ(s)‖ ≤ (4 + 1/σ) · |γ|`.
-/
theorem zetaPolynomialBoundInStrip_from_euler_maclaurin :
    zetaPolynomialBoundInStrip := by
  intro σ hσ_pos hσ_lt
  refine ⟨6 + 2 / σ, 1, 2, by positivity, by norm_num, ?_⟩
  intro γ hγ
  -- Abbreviations
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hs_def
  have hγ_pos : (0 : ℝ) < |γ| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hγ
  have hγ_one : (1 : ℝ) ≤ |γ| := le_trans (by norm_num : (1:ℝ) ≤ 2) hγ
  -- s.re = σ, s.im = γ
  have hs_re : s.re = σ := by simp [hs_def]
  have hs_im : s.im = γ := by simp [hs_def]
  -- s ≠ 1 since s.im = γ ≠ 0
  have hs_ne_one : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hs_im] at this; simp at this
    rw [this, abs_zero] at hγ_pos; linarith
  -- Apply Euler–Maclaurin (explicit form: constant C_EM = ‖s‖/σ + 1)
  have hs_re_pos : 0 < s.re := by rw [hs_re]; exact hσ_pos
  have hs_re_lt : s.re < 1 := by rw [hs_re]; exact hσ_lt
  obtain ⟨hCem_pos, h_em⟩ :=
    GRH.EulerMaclaurinDirichlet.euler_maclaurin_dirichlet_explicit s hs_re_pos
      hs_re_lt hs_ne_one
  -- Choose N := ⌊|γ|⌋₊ + 2
  set N : ℕ := ⌊|γ|⌋₊ + 2 with hN_def
  have hN_ge2 : 2 ≤ N := by simp [hN_def]
  have hN_pos : 0 < N := by omega
  have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  -- |γ| + 1 ≤ N ≤ |γ| + 2 (as reals)
  have h_floor_le : (⌊|γ|⌋₊ : ℝ) ≤ |γ| := Nat.floor_le (le_of_lt hγ_pos)
  have h_lt_floor : |γ| < (⌊|γ|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one |γ|
  have hN_upper : (N : ℝ) ≤ |γ| + 2 := by
    have hNcast : (N : ℝ) = (⌊|γ|⌋₊ : ℝ) + 2 := by
      simp [hN_def, Nat.cast_add, Nat.cast_ofNat]
    rw [hNcast]; linarith
  have hN_lower : |γ| + 1 ≤ (N : ℝ) := by
    have hNcast : (N : ℝ) = (⌊|γ|⌋₊ : ℝ) + 2 := by
      simp [hN_def, Nat.cast_add, Nat.cast_ofNat]
    rw [hNcast]; linarith
  -- Specialize EM to our N
  have h_bnd := h_em N hN_ge2
  -- Rearrange: ‖ζ(s)‖ ≤ ‖S s N‖ + ‖N^(1-s)/(1-s)‖ + C_EM * N^{-σ}
  -- From `‖S s N - ζ(s) - N^(1-s)/(1-s)‖ ≤ C_EM · N^{-σ}`, get
  -- `‖ζ(s)‖ ≤ ‖S s N‖ + ‖N^(1-s)/(1-s)‖ + C_EM · N^{-σ}`.
  set C_EM := ‖s‖ / s.re + 1 with hCem_def
  -- Piece 1: ‖S s N‖ ≤ N (since each term has norm ≤ 1).
  have h_term_le_one : ∀ n : ℕ, ‖(↑(n + 1) : ℂ) ^ (-s)‖ ≤ 1 := by
    intro n
    rw [GRH.SpiralInduction.term_norm n s]
    have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    have hn1_one : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
    -- (n+1)^(-σ) ≤ 1 since n+1 ≥ 1 and -σ ≤ 0.
    have h_exp_le : (-s.re : ℝ) ≤ 0 := by linarith
    have : (n + 1 : ℝ) ^ (-s.re) ≤ (n + 1 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1_one h_exp_le
    rw [Real.rpow_zero] at this
    exact this
  have h_S_norm_le : ‖GRH.SpiralInduction.S s N‖ ≤ (N : ℝ) := by
    simp only [GRH.SpiralInduction.S]
    calc ‖∑ n ∈ Finset.range N, (↑(n + 1) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.range N, ‖(↑(n + 1) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum (fun n _ => h_term_le_one n)
      _ = (N : ℝ) := by simp
  -- Piece 2: ‖N^(1-s)/(1-s)‖ ≤ N / |γ| ≤ (|γ|+2)/|γ| ≤ 2
  have h_one_sub_s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs_ne_one)
  have h_norm_Npow : ‖(↑N : ℂ) ^ ((1 : ℂ) - s)‖ = (N : ℝ) ^ (1 - σ) := by
    rw [Complex.norm_natCast_cpow_of_pos hN_pos]
    congr 1; simp [hs_re]
  have h_norm_one_sub_s_ge : |γ| ≤ ‖(1 : ℂ) - s‖ := by
    -- ‖1 - s‖² = (1-σ)² + γ² ≥ γ²
    have h_im : (1 - s).im = -γ := by simp [hs_im]
    calc |γ| = |(-γ : ℝ)| := by rw [abs_neg]
      _ = |(1 - s).im| := by rw [h_im]
      _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
  have h_norm_one_sub_s_pos : 0 < ‖(1 : ℂ) - s‖ :=
    norm_pos_iff.mpr h_one_sub_s_ne
  have h_piece2 : ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤ 2 := by
    rw [norm_div, h_norm_Npow]
    -- N^{1-σ} / ‖1-s‖ ≤ N / |γ| ≤ (|γ|+2)/|γ| ≤ 2
    have hNpow_le_N : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) := by
      have hN_one : (1 : ℝ) ≤ (N : ℝ) := by
        have : (1 : ℝ) ≤ |γ| + 1 := by linarith
        linarith [hN_lower]
      have h_exp : (1 - σ) ≤ 1 := by linarith
      calc (N : ℝ) ^ (1 - σ)
          ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN_one h_exp
        _ = (N : ℝ) := Real.rpow_one _
    have hNpow_nonneg : 0 ≤ (N : ℝ) ^ (1 - σ) :=
      Real.rpow_nonneg hN_cast_pos.le _
    have h1 : (N : ℝ) ^ (1 - σ) / ‖(1 : ℂ) - s‖ ≤ (N : ℝ) / ‖(1 : ℂ) - s‖ := by
      exact div_le_div_of_nonneg_right hNpow_le_N h_norm_one_sub_s_pos.le
    have h2 : (N : ℝ) / ‖(1 : ℂ) - s‖ ≤ (N : ℝ) / |γ| := by
      apply div_le_div_of_nonneg_left hN_cast_pos.le hγ_pos h_norm_one_sub_s_ge
    have h3 : (N : ℝ) / |γ| ≤ (|γ| + 2) / |γ| := by
      exact div_le_div_of_nonneg_right hN_upper hγ_pos.le
    have h4 : (|γ| + 2) / |γ| ≤ 2 := by
      rw [div_le_iff₀ hγ_pos]; linarith
    linarith
  -- Piece 3: C_EM * N^{-σ} ≤ C_EM (since N^{-σ} ≤ 1)
  have h_Npow_neg_le_one : (N : ℝ) ^ (-σ) ≤ 1 := by
    have hN_one : (1 : ℝ) ≤ (N : ℝ) := by linarith [hN_lower]
    have : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hN_one
      linarith
    rw [Real.rpow_zero] at this; exact this
  -- Bound C_EM = ‖s‖/σ + 1 ≤ 2 + |γ|/σ  (using ‖s‖ ≤ σ + |γ|)
  have h_norm_s_le : ‖s‖ ≤ σ + |γ| := by
    rw [hs_def]
    have h_decomp : (σ : ℂ) + (γ : ℂ) * Complex.I =
        ((σ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I := rfl
    calc ‖(σ : ℂ) + (γ : ℂ) * Complex.I‖
        ≤ ‖((σ : ℝ) : ℂ)‖ + ‖((γ : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
      _ = |σ| + |γ| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_real,
                Complex.norm_I, mul_one]
            rfl
      _ = σ + |γ| := by rw [abs_of_pos hσ_pos]
  have h_CEM_le : C_EM ≤ 2 + |γ| / σ := by
    rw [hCem_def, hs_re]
    have hdiv : ‖s‖ / σ ≤ (σ + |γ|) / σ :=
      div_le_div_of_nonneg_right h_norm_s_le hσ_pos.le
    have h_split : (σ + |γ|) / σ = 1 + |γ| / σ := by
      field_simp
    linarith
  have h_piece3 : C_EM * (N : ℝ) ^ (-σ) ≤ 2 + |γ| / σ := by
    have h1 : C_EM * (N : ℝ) ^ (-σ) ≤ C_EM * 1 := by
      apply mul_le_mul_of_nonneg_left h_Npow_neg_le_one hCem_pos.le
    rw [mul_one] at h1
    linarith
  -- Combine via triangle inequality
  -- ‖ζ(s)‖ = ‖(S s N) - (S s N - ζ(s) - N^(1-s)/(1-s)) - N^(1-s)/(1-s)‖
  -- Equivalently: ζ(s) = S s N - D - N^(1-s)/(1-s), where D is the EM difference.
  set D : ℂ := GRH.SpiralInduction.S s N - riemannZeta s -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) with hD_def
  have h_zeta_eq : riemannZeta s = GRH.SpiralInduction.S s N - D -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) := by
    rw [hD_def]; ring
  -- Specialize h_bnd: hs_re is σ, so (↑N : ℝ)^(-s.re) = (↑N : ℝ)^(-σ)
  have h_bnd_σ : ‖D‖ ≤ C_EM * (N : ℝ) ^ (-σ) := by
    rw [hD_def, hCem_def, hs_re] at *
    have := h_bnd
    rw [hs_re] at this
    exact this
  have h_final : ‖riemannZeta s‖ ≤
      ‖GRH.SpiralInduction.S s N‖ + ‖D‖ +
      ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ := by
    rw [h_zeta_eq]
    have h_triangle1 : ‖GRH.SpiralInduction.S s N - D -
          (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤
        ‖GRH.SpiralInduction.S s N - D‖ +
          ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ := norm_sub_le _ _
    have h_triangle2 : ‖GRH.SpiralInduction.S s N - D‖ ≤
        ‖GRH.SpiralInduction.S s N‖ + ‖D‖ := norm_sub_le _ _
    linarith
  calc ‖riemannZeta s‖
      ≤ ‖GRH.SpiralInduction.S s N‖ + ‖D‖ +
        ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ := h_final
    _ ≤ (|γ| + 2) + (2 + |γ| / σ) + 2 := by
          have h1 : ‖GRH.SpiralInduction.S s N‖ ≤ |γ| + 2 :=
            le_trans h_S_norm_le hN_upper
          have h2 : ‖D‖ ≤ 2 + |γ| / σ := le_trans h_bnd_σ h_piece3
          linarith
    _ ≤ (6 + 2 / σ) * |γ| ^ (1 : ℝ) := by
          rw [Real.rpow_one]
          -- Goal: |γ| + 2 + (2 + |γ|/σ) + 2 ≤ (6 + 2/σ) * |γ|
          -- (6 + 2/σ)|γ| - (|γ| + 6 + |γ|/σ) = 5|γ| + 2|γ|/σ - 6 - |γ|/σ
          --   = 5|γ| - 6 + |γ|/σ ≥ 5·2 - 6 + 2/σ = 4 + 2/σ > 0.
          have hσ_inv_pos : (0 : ℝ) < 1 / σ := by positivity
          have h_gamma_div_nonneg : (0 : ℝ) ≤ |γ| / σ :=
            div_nonneg hγ_pos.le hσ_pos.le
          have h_expand : (6 + 2 / σ) * |γ| =
              6 * |γ| + (2 / σ) * |γ| := by ring
          have h_gamma_div_eq : (2 / σ) * |γ| = 2 * (|γ| / σ) := by
            field_simp
          rw [h_expand, h_gamma_div_eq]
          -- Goal: |γ| + 2 + (2 + |γ|/σ) + 2 ≤ 6|γ| + 2(|γ|/σ)
          linarith

#print axioms zetaPolynomialBoundInStrip_from_euler_maclaurin

end StripBound

end ZD

end
