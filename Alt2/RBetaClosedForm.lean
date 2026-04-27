import Mathlib
import RequestProject.PairComboResidueAtZero

/-!
# Real-analyticity of `R_beta` on `Set.univ`

The β-dependent product integral
```
R_beta β = ∫_{Ioi 0}
    (cosh((1 - π/3)·x) - 1) · (cosh((2β - 1)·x) - 1) · exp(-2 x²) / x dx
```
is real-analytic in `β` on all of `ℝ`.

## Strategy

By `coshDiffM_pair_combo_eq_R_beta` (already proved in
`PairComboResidueAtZero`),
```
R_beta β =
    (1/2)·coshDiffM(2β − π/3) + (1/2)·coshDiffM(2 − π/3 − 2β)
      − coshDiffM(1 − π/3) − coshDiffM(2β − 1) + coshDiffM(0)
```
so it suffices to show that `coshDiffM` is real-analytic in `c`.

We do this by introducing a complex extension `coshDiffMC : ℂ → ℂ` defined by
the same integral (with `Real.cosh` replaced by `Complex.cosh`), proving it
is complex-differentiable in `c`, and then descending to `ℝ` via composition
with `Complex.ofRealCLM`.

Key bounds (uniform for `c` in a complex ball of norm ≤ K):

* original integrand: `‖(cosh(c·x) − 1)·exp(−2x²)/x‖ ≤
                        K·exp(K²/4)·exp(−x²)` on `Ioi 0`
  (uses `‖cosh z − 1‖ ≤ ‖z‖·exp ‖z‖` and quadratic completion);
* c-derivative `sinh(c·x)·exp(−2x²)`: `≤ exp(K²/4)·exp(−t²)` (no `1/x`!).

No new axioms, no sorries.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD.PairComboResidueAtZero

/-! ### § 1 — Complex-`c` extension of `coshDiffM`. -/

/-- Complex extension of `coshDiffM`:
`coshDiffMC c = ∫_{Ioi 0} (Complex.cosh (c·x) - 1) · exp(-2 x²) / x dx`. -/
def coshDiffMC (c : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi (0 : ℝ),
    (Complex.cosh (c * (x : ℂ)) - 1) * ((Real.exp (-2 * x^2) : ℝ) : ℂ) / (x : ℂ)

/-! ### § 2 — Auxiliary norm bounds on `Complex.sinh` and `Complex.cosh - 1`. -/

/-- `‖Complex.sinh w‖ ≤ Real.sinh ‖w‖`, via the power series. -/
lemma complex_sinh_norm_le_real_sinh (w : ℂ) :
    ‖Complex.sinh w‖ ≤ Real.sinh ‖w‖ := by
  have h1 : Complex.sinh w = ∑' n : ℕ, w ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ) :=
    Complex.sinh_eq_tsum w
  rw [h1]
  have h_norm_bound : ∀ n : ℕ,
      ‖w ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)‖ ≤
      ‖w‖ ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℝ) := by
    intro n; rw [norm_div, norm_pow]
    rw [show ‖(((2 * n + 1).factorial : ℕ) : ℂ)‖ = (((2 * n + 1).factorial : ℕ) : ℝ) from
      Complex.norm_natCast _]
  have h_summable :
      Summable (fun n : ℕ => ‖w‖ ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℝ)) :=
    (Real.hasSum_sinh ‖w‖).summable
  have h_summable_norm :
      Summable (fun n : ℕ => ‖w ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)‖) := by
    refine h_summable.of_nonneg_of_le ?_ h_norm_bound
    intro n; exact norm_nonneg _
  calc ‖∑' n : ℕ, w ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)‖
      ≤ ∑' n : ℕ, ‖w ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)‖ :=
        norm_tsum_le_tsum_norm h_summable_norm
    _ ≤ ∑' n : ℕ, ‖w‖ ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℝ) :=
        h_summable_norm.tsum_le_tsum h_norm_bound h_summable
    _ = Real.sinh ‖w‖ := (Real.sinh_eq_tsum ‖w‖).symm

/-- `‖Complex.cosh z - 1‖ ≤ ‖z‖ · Real.exp ‖z‖`. -/
lemma complex_cosh_sub_one_norm_bound (z : ℂ) :
    ‖Complex.cosh z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  -- Step 1: cosh z - 1 = 2 sinh²(z/2).
  have h_id : Complex.cosh z - 1 = 2 * (Complex.sinh (z / 2))^2 := by
    have h := Complex.cosh_two_mul (z / 2)
    have h2z : 2 * (z / 2) = z := by ring
    rw [h2z] at h
    have hsq := Complex.cosh_sq_sub_sinh_sq (z/2)
    linear_combination h + hsq
  rw [h_id]
  have h_norm : ‖(2 : ℂ) * Complex.sinh (z/2) ^ 2‖ = 2 * ‖Complex.sinh (z/2)‖^2 := by
    rw [norm_mul, norm_pow]; norm_num
  rw [h_norm]
  have h_norm_nn : 0 ≤ ‖z‖ := norm_nonneg _
  -- Step 2: ‖sinh(z/2)‖ ≤ Real.sinh(‖z‖/2).
  have h_sinh_le : ‖Complex.sinh (z/2)‖ ≤ Real.sinh (‖z‖ / 2) := by
    have h1 := complex_sinh_norm_le_real_sinh (z/2)
    have h2 : ‖z/2‖ = ‖z‖ / 2 := by rw [norm_div]; simp
    rw [h2] at h1; exact h1
  have h_sinh_nn : 0 ≤ Real.sinh (‖z‖ / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  have h_sinh_sq_le : ‖Complex.sinh (z/2)‖^2 ≤ (Real.sinh (‖z‖/2))^2 := by
    apply sq_le_sq'
    · linarith [norm_nonneg (Complex.sinh (z/2))]
    · exact h_sinh_le
  have h_2sinh_sq_le :
      2 * ‖Complex.sinh (z/2)‖^2 ≤ 2 * (Real.sinh (‖z‖/2))^2 := by linarith
  -- Step 3: 2·sinh²(‖z‖/2) = cosh ‖z‖ - 1.
  have h_cosh_id : 2 * (Real.sinh (‖z‖/2))^2 = Real.cosh ‖z‖ - 1 := by
    have h := Real.cosh_two_mul (‖z‖/2)
    have h2z : 2 * (‖z‖/2) = ‖z‖ := by ring
    rw [h2z] at h
    have hsq := Real.cosh_sq_sub_sinh_sq (‖z‖/2)
    linear_combination -h - hsq
  rw [h_cosh_id] at h_2sinh_sq_le
  -- Step 4: cosh ‖z‖ - 1 ≤ ‖z‖ · exp ‖z‖.
  have h_real_bound : Real.cosh ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
    have h1 : Real.cosh ‖z‖ - 1 ≤ Real.exp ‖z‖ - 1 := by
      rw [Real.cosh_eq]
      have h_neg_le : Real.exp (-‖z‖) ≤ Real.exp ‖z‖ :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have h2 : Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
      have h_int : ∫ u in (0:ℝ)..‖z‖, Real.exp u = Real.exp ‖z‖ - Real.exp 0 := integral_exp
      rw [Real.exp_zero] at h_int
      have h_int_exp : IntervalIntegrable Real.exp MeasureTheory.volume 0 ‖z‖ :=
        Real.continuous_exp.intervalIntegrable _ _
      have h_int_const : IntervalIntegrable (fun _ => Real.exp ‖z‖) MeasureTheory.volume 0 ‖z‖ :=
        intervalIntegrable_const
      have h_bound : ∫ u in (0:ℝ)..‖z‖, Real.exp u ≤ ∫ _ in (0:ℝ)..‖z‖, Real.exp ‖z‖ := by
        apply intervalIntegral.integral_mono_on h_norm_nn h_int_exp h_int_const
        intro u hu; exact Real.exp_le_exp.mpr hu.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at h_bound
      linarith
    linarith
  linarith

/-- `‖Complex.sinh w‖ ≤ Real.exp ‖w‖`. (Looser than `Real.sinh ‖w‖`,
but more convenient.) -/
lemma complex_sinh_norm_le_exp (w : ℂ) :
    ‖Complex.sinh w‖ ≤ Real.exp ‖w‖ := by
  refine le_trans (complex_sinh_norm_le_real_sinh w) ?_
  rw [Real.sinh_eq]
  have h_neg_pos : 0 ≤ Real.exp ‖w‖ + Real.exp (-‖w‖) := by
    positivity
  have h_neg_le : Real.exp (-‖w‖) ≤ Real.exp ‖w‖ :=
    Real.exp_le_exp.mpr (by linarith [norm_nonneg w])
  have h_sinh_form : (Real.exp ‖w‖ - Real.exp (-‖w‖)) / 2 ≤ Real.exp ‖w‖ := by
    have h_neg_pos' : 0 ≤ Real.exp (-‖w‖) := (Real.exp_pos _).le
    nlinarith [Real.exp_pos ‖w‖]
  exact h_sinh_form

/-! ### § 3 — Agreement on real `c`. -/

/-- `coshDiffMC` agrees with `coshDiffM` on real `c`. -/
lemma coshDiffMC_ofReal (c : ℝ) :
    coshDiffMC (c : ℂ) = ((coshDiffM c : ℝ) : ℂ) := by
  unfold coshDiffMC coshDiffM
  rw [show ((∫ x in Ioi (0:ℝ), (Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x : ℝ) : ℂ) =
        ∫ x in Ioi (0:ℝ),
          (((Real.cosh (c * x) - 1) * Real.exp (-2 * x^2) / x : ℝ) : ℂ) from
      integral_ofReal.symm]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx_pos : (0 : ℝ) < x := hx
  have hxC_ne : (x : ℂ) ≠ 0 := by exact_mod_cast hx_pos.ne'
  simp only
  have h_cx_real : ((c : ℂ) * (x : ℂ)) = (((c * x : ℝ)) : ℂ) := by push_cast; ring
  rw [h_cx_real, ← Complex.ofReal_cosh]
  push_cast
  ring

/-! ### § 4 — Quadratic-completion and pointwise bounds. -/

/-- Quadratic-completion bound: `K·t - 2·t² ≤ K²/4 - t²` for all real `K, t`. -/
lemma quadratic_completion_bound (K t : ℝ) :
    K * t - 2 * t^2 ≤ K^2 / 4 - t^2 := by
  nlinarith [sq_nonneg (K - 2*t), sq_nonneg t]

/-- Pointwise bound on the original integrand: for `‖c‖ ≤ K` and `t > 0`,
`‖(cosh(c·t) - 1) · exp(-2t²) / t‖ ≤ K · exp(K²/4) · exp(-t²)`. -/
lemma coshDiffMC_integrand_pointwise_bound
    {c : ℂ} {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : ‖c‖ ≤ K) :
    ‖(Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ)‖ ≤
      K * Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by
  have ht_nn : (0 : ℝ) ≤ t := ht.le
  have htC_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- ‖cosh(c·t) - 1‖ ≤ ‖c·t‖ · exp(‖c·t‖) = (‖c‖·t) · exp(‖c‖·t).
  have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
  have h_cosh_bd : ‖Complex.cosh (c * (t : ℂ)) - 1‖ ≤ ‖c‖ * t * Real.exp (‖c‖ * t) := by
    have h := complex_cosh_sub_one_norm_bound (c * (t : ℂ))
    rw [h_norm_ct] at h
    exact h
  -- ‖exp(-2t²) : ℂ‖ = exp(-2t²).
  have h_exp_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- ‖t : ℂ‖ = t.
  have h_t_norm : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
  -- Compute the LHS norm.
  rw [norm_div, norm_mul, h_exp_norm, h_t_norm]
  -- LHS = ‖cosh(c·t) - 1‖ · exp(-2t²) / t.
  -- Bound the numerator first:
  have h_num_bd : ‖Complex.cosh (c * (t : ℂ)) - 1‖ * Real.exp (-2 * t^2) ≤
      ‖c‖ * t * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
    mul_le_mul_of_nonneg_right h_cosh_bd (Real.exp_pos _).le
  -- Combine the exponentials: exp(‖c‖·t) · exp(-2t²) = exp(‖c‖·t - 2t²).
  have h_exp_combine : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) =
      Real.exp (‖c‖ * t - 2 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  -- Bound by K via the K-norm assumption: ‖c‖ ≤ K means
  -- Real.exp(‖c‖·t) ≤ Real.exp(K·t).
  have h_K_exp : Real.exp (‖c‖ * t - 2 * t^2) ≤ Real.exp (K * t - 2 * t^2) :=
    Real.exp_le_exp.mpr (by nlinarith [hK, ht.le])
  -- Quadratic completion: K·t - 2t² ≤ K²/4 - t².
  have h_quad : Real.exp (K * t - 2 * t^2) ≤ Real.exp (K^2 / 4 - t^2) :=
    Real.exp_le_exp.mpr (quadratic_completion_bound K t)
  -- exp(K²/4 - t²) = exp(K²/4) · exp(-t²) = exp(K²/4) · exp(-1·t²).
  have h_split : Real.exp (K^2 / 4 - t^2) = Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  -- Bound ‖c‖ ≤ K.
  have h_K_nn : 0 ≤ K := le_trans (norm_nonneg c) hK
  -- Chain: ‖cosh - 1‖ · exp(-2t²) ≤ K·t · exp(K²/4) · exp(-t²).
  have h_chain : ‖Complex.cosh (c * (t : ℂ)) - 1‖ * Real.exp (-2 * t^2) ≤
      K * t * (Real.exp (K^2 / 4) * Real.exp (-1 * t^2)) := by
    calc ‖Complex.cosh (c * (t : ℂ)) - 1‖ * Real.exp (-2 * t^2)
        ≤ ‖c‖ * t * Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) := h_num_bd
      _ = ‖c‖ * t * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by ring
      _ = ‖c‖ * t * Real.exp (‖c‖ * t - 2 * t^2) := by rw [h_exp_combine]
      _ ≤ K * t * Real.exp (‖c‖ * t - 2 * t^2) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hK ht_nn
          · exact (Real.exp_pos _).le
      _ ≤ K * t * Real.exp (K * t - 2 * t^2) := by
          apply mul_le_mul_of_nonneg_left h_K_exp
          exact mul_nonneg h_K_nn ht_nn
      _ ≤ K * t * Real.exp (K^2 / 4 - t^2) := by
          apply mul_le_mul_of_nonneg_left h_quad
          exact mul_nonneg h_K_nn ht_nn
      _ = K * t * (Real.exp (K^2 / 4) * Real.exp (-1 * t^2)) := by rw [h_split]
  -- Divide by t > 0: K·t · A / t = K · A.
  rw [div_le_iff₀ ht]
  calc ‖Complex.cosh (c * (t : ℂ)) - 1‖ * Real.exp (-2 * t^2)
      ≤ K * t * (Real.exp (K^2 / 4) * Real.exp (-1 * t^2)) := h_chain
    _ = K * Real.exp (K^2 / 4) * Real.exp (-1 * t^2) * t := by ring

/-- Pointwise bound on the c-derivative integrand: for `‖c‖ ≤ K` and `t > 0`,
`‖sinh(c·t) · exp(-2t²)‖ ≤ exp(K²/4) · exp(-t²)`. The `1/x` singularity has
cancelled with the formal derivative of `(cosh(c·x) - 1)/x` in `c` (which
gives `sinh(c·x)`, no `1/x`). -/
lemma coshDiffMC_deriv_pointwise_bound
    {c : ℂ} {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : ‖c‖ ≤ K) :
    ‖Complex.sinh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ ≤
      Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by
  have ht_nn : (0 : ℝ) ≤ t := ht.le
  have h_K_nn : 0 ≤ K := le_trans (norm_nonneg c) hK
  -- ‖sinh(c·t)‖ ≤ exp(‖c·t‖) = exp(‖c‖·t).
  have h_norm_ct : ‖c * (t : ℂ)‖ = ‖c‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht_nn]
  have h_sinh_bd : ‖Complex.sinh (c * (t : ℂ))‖ ≤ Real.exp (‖c‖ * t) := by
    have h := complex_sinh_norm_le_exp (c * (t : ℂ))
    rw [h_norm_ct] at h; exact h
  have h_exp_norm : ‖((Real.exp (-2 * t^2) : ℝ) : ℂ)‖ = Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [norm_mul, h_exp_norm]
  -- ‖sinh(c·t)‖ · exp(-2t²) ≤ exp(‖c‖·t) · exp(-2t²) = exp(‖c‖·t - 2t²).
  have h_step1 : ‖Complex.sinh (c * (t : ℂ))‖ * Real.exp (-2 * t^2) ≤
      Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) :=
    mul_le_mul_of_nonneg_right h_sinh_bd (Real.exp_pos _).le
  have h_combine : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) =
      Real.exp (‖c‖ * t - 2 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  have h_K_exp : Real.exp (‖c‖ * t - 2 * t^2) ≤ Real.exp (K * t - 2 * t^2) :=
    Real.exp_le_exp.mpr (by nlinarith [hK, ht.le])
  have h_quad : Real.exp (K * t - 2 * t^2) ≤ Real.exp (K^2 / 4 - t^2) :=
    Real.exp_le_exp.mpr (quadratic_completion_bound K t)
  have h_split : Real.exp (K^2 / 4 - t^2) = Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Complex.sinh (c * (t : ℂ))‖ * Real.exp (-2 * t^2)
      ≤ Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) := h_step1
    _ = Real.exp (‖c‖ * t - 2 * t^2) := h_combine
    _ ≤ Real.exp (K * t - 2 * t^2) := h_K_exp
    _ ≤ Real.exp (K^2 / 4 - t^2) := h_quad
    _ = Real.exp (K^2 / 4) * Real.exp (-1 * t^2) := h_split

/-! ### § 5 — Parametric integral differentiability of `coshDiffMC` in `c`. -/

/-- The c-derivative of the cosh-Diff integrand at a point. -/
lemma hasDerivAt_coshDiffMC_integrand (t : ℝ) (ht : 0 < t) (c₀ : ℂ) :
    HasDerivAt
      (fun c : ℂ =>
        (Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ))
      (Complex.sinh (c₀ * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      c₀ := by
  have htC_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- d/dc [cosh(c·t) - 1] = sinh(c·t) · t.
  have h_inner : HasDerivAt (fun c : ℂ => c * (t : ℂ)) (t : ℂ) c₀ := by
    simpa using (hasDerivAt_id c₀).mul_const (t : ℂ)
  have h_cosh : HasDerivAt (fun c : ℂ => Complex.cosh (c * (t : ℂ)))
      (Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) c₀ := h_inner.ccosh
  have h_cosh_sub : HasDerivAt (fun c : ℂ => Complex.cosh (c * (t : ℂ)) - 1)
      (Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) c₀ := by
    simpa using h_cosh.sub_const (1 : ℂ)
  -- Multiply by exp(-2t²).
  have h_with_exp : HasDerivAt
      (fun c : ℂ => (Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      ((Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ))
      c₀ :=
    h_cosh_sub.mul_const _
  -- Divide by (t : ℂ).
  have h_div : HasDerivAt
      (fun c : ℂ =>
        (Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ))
      ((Complex.sinh (c₀ * (t : ℂ)) * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ))
      c₀ := h_with_exp.div_const _
  convert h_div using 1
  field_simp

/-- Integrability of the dominating bound `K · exp(K²/4) · exp(-t²)` on `Ioi 0`. -/
lemma coshDiffMC_bound_integrable (K : ℝ) :
    IntegrableOn (fun t : ℝ => K * Real.exp (K^2 / 4) * Real.exp (-1 * t^2))
      (Ioi (0 : ℝ)) := by
  have h_base : Integrable (fun t : ℝ => Real.exp (-1 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  exact (h_base.const_mul (K * Real.exp (K^2 / 4))).integrableOn

/-- Integrability of the derivative-bound `exp(K²/4) · exp(-t²)` on `Ioi 0`. -/
lemma coshDiffMC_deriv_bound_integrable (K : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (K^2 / 4) * Real.exp (-1 * t^2))
      (Ioi (0 : ℝ)) := by
  have h_base : Integrable (fun t : ℝ => Real.exp (-1 * t^2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  exact (h_base.const_mul (Real.exp (K^2 / 4))).integrableOn

/-- Continuity of the integrand `t ↦ (cosh(c·t) - 1) · exp(-2t²) / t` on `Ioi 0`. -/
lemma coshDiffMC_integrand_continuousOn_t (c : ℂ) :
    ContinuousOn
      (fun t : ℝ =>
        (Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ))
      (Ioi (0 : ℝ)) := by
  intro t ht
  have ht_pos : (0 : ℝ) < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ Complex.continuous_ofReal.continuousAt ?_
  · refine ContinuousAt.mul ?_ ?_
    · refine ContinuousAt.sub ?_ continuousAt_const
      exact Complex.continuous_cosh.continuousAt.comp
        ((continuous_const.mul Complex.continuous_ofReal).continuousAt)
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact Real.continuous_exp.continuousAt.comp
        ((continuous_const.mul (continuous_id.pow 2)).continuousAt)
  · exact_mod_cast ht_pos.ne'

/-- Continuity of the derivative integrand `t ↦ sinh(c·t) · exp(-2t²)` on `ℝ`. -/
lemma coshDiffMC_deriv_integrand_continuousOn_t (c : ℂ) :
    Continuous (fun t : ℝ => Complex.sinh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)) := by
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_sinh.comp (continuous_const.mul Complex.continuous_ofReal)
  · exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))

/-- **Differentiability of `coshDiffMC c` in `c` (complex).**

The function `c ↦ coshDiffMC c` is `Differentiable ℂ` at every `c₀`. -/
theorem coshDiffMC_differentiableAt_in_c (c₀ : ℂ) :
    DifferentiableAt ℂ (fun c : ℂ => coshDiffMC c) c₀ := by
  -- Take ball of radius 1 around c₀.
  set R : ℝ := 1
  set K : ℝ := ‖c₀‖ + R
  set s : Set ℂ := Metric.ball c₀ R
  have hs : s ∈ nhds c₀ := Metric.ball_mem_nhds c₀ (by norm_num : (0 : ℝ) < R)
  have hK_nn : 0 ≤ K := by
    have := norm_nonneg c₀; simp [K, R]; linarith
  -- Define F and F'.
  set F : ℂ → ℝ → ℂ := fun c t =>
    (Complex.cosh (c * (t : ℂ)) - 1) * ((Real.exp (-2 * t^2) : ℝ) : ℂ) / (t : ℂ)
  set F' : ℂ → ℝ → ℂ := fun c t =>
    Complex.sinh (c * (t : ℂ)) * ((Real.exp (-2 * t^2) : ℝ) : ℂ)
  set bound_F : ℝ → ℝ := fun t =>
    K * Real.exp (K^2 / 4) * Real.exp (-1 * t^2)
  set bound_F' : ℝ → ℝ := fun t =>
    Real.exp (K^2 / 4) * Real.exp (-1 * t^2)
  -- AEStronglyMeasurable for F c on Ioi 0.
  have h_meas_F : ∀ c : ℂ, AEStronglyMeasurable (F c) (volume.restrict (Ioi (0:ℝ))) := by
    intro c
    exact (coshDiffMC_integrand_continuousOn_t c).aestronglyMeasurable measurableSet_Ioi
  have hF_meas : ∀ᶠ x in nhds c₀,
      AEStronglyMeasurable (F x) (volume.restrict (Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun c => h_meas_F c)
  -- Bound for F c₀ on Ioi 0.
  have h_F_bound_ae :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))), ‖F c₀ a‖ ≤ bound_F a := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht
    have hK_le : ‖c₀‖ ≤ K := by simp [K, R]
    exact coshDiffMC_integrand_pointwise_bound (c := c₀) (t := t) ht hK_le
  -- Integrability of bound_F.
  have h_bound_F_int : Integrable bound_F (volume.restrict (Ioi (0:ℝ))) := by
    exact coshDiffMC_bound_integrable K
  -- Integrability of F c₀.
  have hF_int : Integrable (F c₀) (volume.restrict (Ioi (0:ℝ))) := by
    refine Integrable.mono' h_bound_F_int (h_meas_F c₀) ?_
    exact h_F_bound_ae
  -- AEStronglyMeasurable for F' c₀.
  have h_meas_F' : AEStronglyMeasurable (F' c₀) (volume.restrict (Ioi (0:ℝ))) :=
    (coshDiffMC_deriv_integrand_continuousOn_t c₀).aestronglyMeasurable.restrict
  -- Bound for F' c on s.
  have h_bound :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))), ∀ x ∈ s, ‖F' x a‖ ≤ bound_F' a := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht x hx
    have hx_norm : ‖x‖ ≤ K := by
      have h1 : dist x c₀ < R := hx
      have h2 : ‖x‖ ≤ ‖c₀‖ + dist x c₀ := by
        have := norm_le_norm_add_norm_sub' x c₀
        simpa [dist_eq_norm] using this
      simp [K]; linarith
    exact coshDiffMC_deriv_pointwise_bound (c := x) (t := t) ht hx_norm
  -- bound_F' integrable.
  have h_bound_F'_int : Integrable bound_F' (volume.restrict (Ioi (0:ℝ))) :=
    coshDiffMC_deriv_bound_integrable K
  -- HasDerivAt for F at every (x, a).
  have h_diff :
      ∀ᵐ a ∂(volume.restrict (Ioi (0:ℝ))),
        ∀ x ∈ s, HasDerivAt (fun y => F y a) (F' x a) x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro t ht x _hx
    exact hasDerivAt_coshDiffMC_integrand t ht x
  -- Apply the parametric integral derivative theorem.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := F) (x₀ := c₀) (s := s)
    (bound := bound_F') (F' := F')
    hs hF_meas hF_int h_meas_F' h_bound h_bound_F'_int h_diff
  obtain ⟨_, hd⟩ := key
  have h_int_eq : (fun n => ∫ a, F n a ∂(volume.restrict (Ioi (0:ℝ)))) =
      (fun c : ℂ => coshDiffMC c) := by
    funext c
    rfl
  rw [h_int_eq] at hd
  exact hd.differentiableAt

/-! ### § 7 — Analyticity of `coshDiffMC` on `Set.univ`. -/

/-- `coshDiffMC` is `Differentiable ℂ`. -/
theorem coshDiffMC_differentiable_in_c :
    Differentiable ℂ (fun c : ℂ => coshDiffMC c) :=
  fun c₀ => coshDiffMC_differentiableAt_in_c c₀

/-- `coshDiffMC` is `AnalyticOnNhd ℂ` on `Set.univ`. -/
theorem coshDiffMC_analyticOnNhd :
    AnalyticOnNhd ℂ (fun c : ℂ => coshDiffMC c) Set.univ :=
  coshDiffMC_differentiable_in_c.differentiableOn.analyticOnNhd isOpen_univ

/-! ### § 8 — Real-analyticity of `coshDiffM` on `Set.univ`. -/

set_option backward.isDefEq.respectTransparency false in
/-- `coshDiffM c` is real-analytic in real `c` on `Set.univ`. -/
theorem coshDiffM_analyticOnNhd :
    AnalyticOnNhd ℝ (fun c : ℝ => coshDiffM c) Set.univ := by
  have h_ℂ : AnalyticOnNhd ℂ (fun c : ℂ => coshDiffMC c) Set.univ :=
    coshDiffMC_analyticOnNhd
  -- Restrict scalars: ℂ-analytic ⇒ ℝ-analytic in c : ℂ.
  have h_ℝ_ℂ : AnalyticOnNhd ℝ (fun c : ℂ => coshDiffMC c) Set.univ :=
    h_ℂ.restrictScalars
  -- Compose with Complex.ofRealCLM : ℝ →L[ℝ] ℂ.
  have h_comp :
      AnalyticOnNhd ℝ
        ((fun c : ℂ => coshDiffMC c) ∘ Complex.ofRealCLM)
        (Complex.ofRealCLM ⁻¹' Set.univ) :=
    AnalyticOnNhd.compContinuousLinearMap (u := Complex.ofRealCLM) h_ℝ_ℂ
  have h_pre : Complex.ofRealCLM ⁻¹' (Set.univ : Set ℂ) = Set.univ := by
    rw [Set.preimage_univ]
  rw [h_pre] at h_comp
  -- Composition equals `c ↦ coshDiffMC (c : ℂ) = (coshDiffM c : ℂ)`,
  -- which is `Complex.ofRealCLM ∘ coshDiffM`. Use AnalyticAt.real_of_complex via
  -- the equality coshDiffMC (c : ℂ) = (coshDiffM c : ℂ) and the fact that
  -- ofReal-coercion preserves analyticity.
  -- Pull AnalyticOnNhd to ℝ → ℝ via restricting to the imaginary line and re.
  -- Equality at every point (as ℂ-valued functions):
  have h_eq : ((fun c : ℂ => coshDiffMC c) ∘ Complex.ofRealCLM) =
      (fun c : ℝ => ((coshDiffM c : ℝ) : ℂ)) := by
    funext c
    simp [Function.comp, Complex.ofRealCLM_apply, coshDiffMC_ofReal]
  rw [h_eq] at h_comp
  -- `(fun c : ℝ => ((coshDiffM c : ℝ) : ℂ))` is real-analytic ⇒ `coshDiffM` is.
  -- Use the fact that `Complex.reCLM ∘ ofReal = id` to recover the real function.
  -- Specifically: `coshDiffM c = (((coshDiffM c : ℝ) : ℂ)).re = Complex.reCLM ((coshDiffM c : ℂ))`.
  have h_re : (fun c : ℝ => coshDiffM c) =
      (fun c : ℝ => Complex.reCLM (((coshDiffM c : ℝ) : ℂ))) := by
    funext c; simp
  rw [h_re]
  -- Compose with the real-CLM Complex.reCLM.
  exact (Complex.reCLM.analyticOnNhd Set.univ).comp h_comp (fun _ _ => Set.mem_univ _)

/-! ### § 9 — Real-analyticity of `R_beta` on `Set.univ`. -/

/-- The β-affine maps used in the pair-combo decomposition are real-analytic. -/
private lemma analyticOnNhd_affine_2β_sub_pi3 :
    AnalyticOnNhd ℝ (fun β : ℝ => 2*β - Real.pi/3) Set.univ := fun _ _ =>
  (analyticAt_const.mul analyticAt_id).sub analyticAt_const

private lemma analyticOnNhd_affine_2_sub_pi3_sub_2β :
    AnalyticOnNhd ℝ (fun β : ℝ => 2 - Real.pi/3 - 2*β) Set.univ := fun _ _ =>
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))

private lemma analyticOnNhd_affine_2β_sub_1 :
    AnalyticOnNhd ℝ (fun β : ℝ => 2*β - 1) Set.univ := fun _ _ =>
  (analyticAt_const.mul analyticAt_id).sub analyticAt_const

/-- **Real-analyticity of `R_beta` on `Set.univ`.**

By `coshDiffM_pair_combo_eq_R_beta`,
```
R_beta β = (1/2)·coshDiffM(2β−π/3) + (1/2)·coshDiffM(2−π/3−2β)
            − coshDiffM(1−π/3) − coshDiffM(2β−1) + coshDiffM(0)
```
and each summand is real-analytic in β by composition with affine functions. -/
theorem R_beta_analyticOnNhd :
    AnalyticOnNhd ℝ (fun β : ℝ => R_beta β) Set.univ := by
  set M : ℝ → ℝ := fun c => coshDiffM c with hM_def
  have h_M : AnalyticOnNhd ℝ M Set.univ := coshDiffM_analyticOnNhd
  have h_M1 : AnalyticOnNhd ℝ (fun β : ℝ => M (2*β - Real.pi/3)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2*β - Real.pi/3) (Set.mem_univ _))
      (analyticOnNhd_affine_2β_sub_pi3 β (Set.mem_univ _))
  have h_M2 : AnalyticOnNhd ℝ (fun β : ℝ => M (2 - Real.pi/3 - 2*β)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2 - Real.pi/3 - 2*β) (Set.mem_univ _))
      (analyticOnNhd_affine_2_sub_pi3_sub_2β β (Set.mem_univ _))
  have h_M3 : AnalyticOnNhd ℝ (fun _ : ℝ => M (1 - Real.pi/3)) Set.univ :=
    analyticOnNhd_const
  have h_M4 : AnalyticOnNhd ℝ (fun β : ℝ => M (2*β - 1)) Set.univ := by
    intro β _
    exact AnalyticAt.comp' (h_M (2*β - 1) (Set.mem_univ _))
      (analyticOnNhd_affine_2β_sub_1 β (Set.mem_univ _))
  have h_M0 : AnalyticOnNhd ℝ (fun _ : ℝ => M 0) Set.univ := analyticOnNhd_const
  -- Combination matching the pair-combo formula.
  set g : ℝ → ℝ := fun β =>
    (1/2 : ℝ) * M (2*β - Real.pi/3) +
    (1/2 : ℝ) * M (2 - Real.pi/3 - 2*β) -
    M (1 - Real.pi/3) -
    M (2*β - 1) +
    M 0 with hg_def
  have hg : AnalyticOnNhd ℝ g Set.univ := by
    refine ((((analyticOnNhd_const.mul h_M1).add (analyticOnNhd_const.mul h_M2)).sub
      h_M3).sub h_M4).add h_M0
  have h_eq : (fun β : ℝ => R_beta β) = g := by
    funext β
    have h := coshDiffM_pair_combo_eq_R_beta β
    show R_beta β = g β
    simp only [hg_def, hM_def]
    linarith
  rw [h_eq]
  exact hg

end ZD.PairComboResidueAtZero

end
