import Mathlib
import RequestProject.PairCoshGaussTest
import RequestProject.WeilPairIBP
import RequestProject.WeilZeroSum

/-!
# Weil Pair-Test Quartic Mellin Decay (IBP×4)

Extends `WeilPairIBP.lean`'s 2-step IBP infrastructure to 4-step, unconditionally
discharging `pairTestMellin_im_quartic_decay_target β`.

## Strategy

For `f = pair_cosh_gauss_test β`, apply `mellin_ibp` four times:

```
pairTestMellin β s
  = -(1/s)         · pairDerivMellin   β (s+1)    [IBP #1, existing]
  = -(1/s)·-(1/(s+1)) · pairDeriv2Mellin β (s+2)  [IBP #2, existing]
  = ...            · pairDeriv3Mellin  β (s+3)    [IBP #3, NEW]
  = (1/(s(s+1)(s+2)(s+3))) · pairDeriv4Mellin β (s+4)  [IBP #4, NEW]
```

Each new step requires explicit `coshGaussDeriv{3,4}Val c t`, Gaussian decay,
near-zero boundedness, Mellin convergence, and boundary vanishing of
`t^s · iteratedDeriv k pair(t)` for `k = 2, 3`.

The 4th-derivative Mellin transform is uniformly bounded on compact strips,
and combined with `∏_{k=0..3} |ρ+k|² ≥ (1 + (Im ρ)²)²` for nontrivial zeros
(where `0 < Re ρ < 1`), yields `‖pairTestMellin β ρ‖ ≤ C / (1 + (Im ρ)²)²`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3rd derivative of cosh(c·t)·exp(-2t²)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **3rd derivative of `cosh(c·t)·exp(-2t²)`.**
Derived from the recurrence `H_{n+1}^c = (H_n^c)' − 4t·H_n^c`:
```
H_3^c(t) = (48t − 12tc² − 64t³)·cosh(c·t) + (c³ − 12c + 48t²c)·sinh(c·t)
```
multiplied by `exp(-2t²)`. -/
noncomputable def coshGaussDeriv3Val (c t : ℝ) : ℝ :=
  ((48 * t - 12 * t * c^2 - 64 * t^3) * Real.cosh (c * t) +
    (c^3 - 12 * c + 48 * t^2 * c) * Real.sinh (c * t)) *
    Real.exp (-2 * t^2)

/-- **HasDerivAt for `coshGaussDeriv2Val`**: its derivative is `coshGaussDeriv3Val`. -/
theorem coshGauss_hasDerivAt_iter3 (c t : ℝ) :
    HasDerivAt (coshGaussDeriv2Val c) (coshGaussDeriv3Val c t) t := by
  unfold coshGaussDeriv2Val coshGaussDeriv3Val
  have h_inner : HasDerivAt (fun u : ℝ => c * u) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h_cosh : HasDerivAt (fun u : ℝ => Real.cosh (c * u)) (Real.sinh (c * t) * c) t :=
    (Real.hasDerivAt_cosh (c * t)).comp t h_inner
  have h_sinh : HasDerivAt (fun u : ℝ => Real.sinh (c * u)) (Real.cosh (c * t) * c) t :=
    (Real.hasDerivAt_sinh (c * t)).comp t h_inner
  -- Polynomial A(t) := c² - 4 + 16·t²
  have h_A : HasDerivAt (fun u : ℝ => c^2 - 4 + 16 * u^2) (32 * t) t := by
    have h1 : HasDerivAt (fun u : ℝ => u^2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun u : ℝ => 16 * u^2) (16 * (2 * t)) t := h1.const_mul 16
    have h3 := (hasDerivAt_const t (c^2 - 4)).add h2
    convert h3 using 1
    ring
  -- A(t) · cosh(c·t)
  have h_A_cosh : HasDerivAt (fun u : ℝ => (c^2 - 4 + 16 * u^2) * Real.cosh (c * u))
      (32 * t * Real.cosh (c * t) + (c^2 - 4 + 16 * t^2) * (Real.sinh (c * t) * c)) t :=
    h_A.mul h_cosh
  -- Polynomial B(t) := 8·c·t
  have h_B : HasDerivAt (fun u : ℝ => 8 * c * u) (8 * c) t := by
    have := (hasDerivAt_id t).const_mul (8 * c)
    simpa [mul_one] using this
  -- B(t) · sinh(c·t)
  have h_B_sinh : HasDerivAt (fun u : ℝ => 8 * c * u * Real.sinh (c * u))
      (8 * c * Real.sinh (c * t) + 8 * c * t * (Real.cosh (c * t) * c)) t :=
    h_B.mul h_sinh
  -- [A·cosh - B·sinh](t)
  have h_u : HasDerivAt
      (fun u : ℝ => (c^2 - 4 + 16 * u^2) * Real.cosh (c * u) -
                    8 * c * u * Real.sinh (c * u))
      (32 * t * Real.cosh (c * t) + (c^2 - 4 + 16 * t^2) * (Real.sinh (c * t) * c) -
       (8 * c * Real.sinh (c * t) + 8 * c * t * (Real.cosh (c * t) * c))) t :=
    h_A_cosh.sub h_B_sinh
  -- exp(-2t²)
  have h_arg : HasDerivAt (fun u : ℝ => -2 * u^2) (-2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-2 : ℝ)
    simpa [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have h_exp : HasDerivAt (fun u : ℝ => Real.exp (-2 * u^2))
      (Real.exp (-2 * t^2) * (-2 * (2 * t))) t :=
    h_arg.exp
  have h_prod := h_u.mul h_exp
  convert h_prod using 1
  ring

#print axioms coshGaussDeriv3Val
#print axioms coshGauss_hasDerivAt_iter3

/-- **Shared helper: `sinh(c·t)·exp(-2t²) =O[atTop] exp(-t)`.** Analog of
`coshGauss_isBigO_exp_neg_atTop` with sinh instead of cosh. Uses `|sinh(x)| ≤ cosh(x)`. -/
private lemma sinhGauss_isBigO_exp_neg_atTop (c : ℝ) :
    (fun t : ℝ => ((Real.sinh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
  have h_cosh := coshGauss_isBigO_exp_neg_atTop c
  refine Asymptotics.IsBigO.trans ?_ h_cosh
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
  have h_sinh_le : |Real.sinh (c*t)| ≤ Real.cosh (c*t) := by
    rw [Real.abs_sinh, ← Real.cosh_abs (c*t)]
    exact (Real.sinh_lt_cosh _).le
  have h_exp_pos : 0 < Real.exp (-2 * t^2) := Real.exp_pos _
  have h_cosh_nn : 0 ≤ Real.cosh (c*t) := (Real.cosh_pos _).le
  have h_prod_nn : 0 ≤ Real.cosh (c*t) * Real.exp (-2 * t^2) :=
    mul_nonneg h_cosh_nn h_exp_pos.le
  rw [Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos h_exp_pos,
      Real.norm_of_nonneg h_prod_nn, one_mul]
  exact mul_le_mul_of_nonneg_right h_sinh_le h_exp_pos.le

#print axioms sinhGauss_isBigO_exp_neg_atTop

/-- **Gaussian decay of `coshGaussDeriv3Val c =O[atTop] exp(-t/2)`.**
Decomposition: `polynomial(t) · cosh(c·t)·exp(-2t²) + polynomial(t) · sinh(c·t)·exp(-2t²)`.
Each piece is `polynomial × O(exp(-t)) = o(exp(t/2))·O(exp(-t)) = o(exp(-t/2))`. -/
theorem coshGaussDeriv3Val_isBigO_exp_neg_half_atTop (c : ℝ) :
    (fun t : ℝ => ((coshGaussDeriv3Val c t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  -- Rewrite: deriv3Val = [A·cosh + B·sinh]·exp(-2t²)
  -- with A(t) = 48t - 12tc² - 64t³, B(t) = c³ - 12c + 48t²c.
  -- Split into sum: A·cosh·exp + B·sinh·exp.
  have h_pow1_lito : (fun t : ℝ => t) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_pow2_lito : (fun t : ℝ => t^2) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_pow3_lito : (fun t : ℝ => t^3) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_const_lito : (fun _ : ℝ => (1:ℝ)) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have h : (fun t : ℝ => t^0) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
      have := isLittleO_pow_exp_pos_mul_atTop 0 (by norm_num : (0:ℝ) < 1/2)
      simpa using this
    simpa using h
  have h_cosh_gauss_R :
      (fun t : ℝ => (Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    have h := coshGauss_isBigO_exp_neg_atTop c
    rw [Asymptotics.isBigO_iff] at h ⊢
    obtain ⟨C, hC⟩ := h
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rwa [Complex.norm_real] at ht
  have h_sinh_gauss_R :
      (fun t : ℝ => (Real.sinh (c * t) * Real.exp (-2 * t^2) : ℝ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    have h := sinhGauss_isBigO_exp_neg_atTop c
    rw [Asymptotics.isBigO_iff] at h ⊢
    obtain ⟨C, hC⟩ := h
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    have h_abs : ‖(Real.sinh (c * t) * Real.exp (-2 * t^2) : ℝ)‖ =
        ‖((Real.sinh (c * t) * Real.exp (-2 * t^2) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real]
    rw [h_abs]; exact ht
  have h_half_sum : (fun t : ℝ => Real.exp ((1/2) * t) * Real.exp (-t)) =
      (fun t : ℝ => Real.exp (-t/2)) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  -- Each polynomial × cosh/sinh-gauss =o exp(-t/2).
  have h_lin_cosh_R :
      (fun t : ℝ => t * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow1_lito.mul_isBigO h_cosh_gauss_R
    rw [← h_half_sum]; exact this
  have h_cub_cosh_R :
      (fun t : ℝ => t^3 * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow3_lito.mul_isBigO h_cosh_gauss_R
    rw [← h_half_sum]; exact this
  have h_const_sinh_R :
      (fun t : ℝ => (1:ℝ) * (Real.sinh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_const_lito.mul_isBigO h_sinh_gauss_R
    rw [← h_half_sum]; exact this
  have h_quad_sinh_R :
      (fun t : ℝ => t^2 * (Real.sinh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow2_lito.mul_isBigO h_sinh_gauss_R
    rw [← h_half_sum]; exact this
  -- Combine five pieces.  coshGaussDeriv3Val c t =
  --   [48·(t·cosh·exp) - 12c²·(t·cosh·exp) - 64·(t³·cosh·exp)] +
  --   [(c³-12c)·(1·sinh·exp) + 48c·(t²·sinh·exp)]
  have h_coerced_R :
      (fun t : ℝ => ((coshGaussDeriv3Val c t : ℝ) : ℂ)) =
      fun t : ℝ =>
        (((48 : ℝ) * (t * (Real.cosh (c*t) * Real.exp (-2*t^2))) -
         (12 * c^2) * (t * (Real.cosh (c*t) * Real.exp (-2*t^2))) -
         (64 : ℝ) * (t^3 * (Real.cosh (c*t) * Real.exp (-2*t^2))) +
         (c^3 - 12*c) * ((1:ℝ) * (Real.sinh (c*t) * Real.exp (-2*t^2))) +
         (48 * c) * (t^2 * (Real.sinh (c*t) * Real.exp (-2*t^2))) : ℝ) : ℂ) := by
    funext t
    unfold coshGaussDeriv3Val
    push_cast; ring
  rw [h_coerced_R]
  -- Lift each piece to ℂ and use IsBigO/IsLittleO.
  have lift : ∀ (f : ℝ → ℝ), (f =o[atTop] fun t => Real.exp (-t/2)) →
      (fun t : ℝ => ((f t : ℝ) : ℂ)) =o[atTop] (fun t : ℝ => Real.exp (-t/2)) := by
    intro f hf
    rw [Asymptotics.isLittleO_iff] at hf ⊢
    intro c hc
    filter_upwards [hf hc] with t ht
    rwa [Complex.norm_real]
  have hL1 := lift _ h_lin_cosh_R
  have hL2 := lift _ h_cub_cosh_R
  have hL3 := lift _ h_const_sinh_R
  have hL4 := lift _ h_quad_sinh_R
  -- Scale each and combine.
  have h1 := hL1.isBigO.const_mul_left ((48 : ℝ) : ℂ)
  have h2 := hL1.isBigO.const_mul_left (((- (12 * c^2)) : ℝ) : ℂ)
  have h3 := hL2.isBigO.const_mul_left (((- (64 : ℝ)) : ℝ) : ℂ)
  have h4 := hL3.isBigO.const_mul_left (((c^3 - 12*c) : ℝ) : ℂ)
  have h5 := hL4.isBigO.const_mul_left (((48 * c) : ℝ) : ℂ)
  have h_final_sum := (((h1.add h2).add h3).add h4).add h5
  refine h_final_sum.congr_left ?_
  intro t; push_cast; ring

#print axioms coshGaussDeriv3Val_isBigO_exp_neg_half_atTop

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4th derivative of cosh(c·t)·exp(-2t²)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **4th derivative of `cosh(c·t)·exp(-2t²)`.**
```
H_4^c(t) = (256t⁴ − 384t² + 96c²t² + c⁴ − 24c² + 48)·cosh(c·t)
         + (192ct − 16c³t − 256ct³)·sinh(c·t)
```
multiplied by `exp(-2t²)`. -/
noncomputable def coshGaussDeriv4Val (c t : ℝ) : ℝ :=
  ((256 * t^4 - 384 * t^2 + 96 * c^2 * t^2 + c^4 - 24 * c^2 + 48) * Real.cosh (c * t) +
    (192 * c * t - 16 * c^3 * t - 256 * c * t^3) * Real.sinh (c * t)) *
    Real.exp (-2 * t^2)

/-- **HasDerivAt for `coshGaussDeriv3Val`**: its derivative is `coshGaussDeriv4Val`. -/
theorem coshGauss_hasDerivAt_iter4 (c t : ℝ) :
    HasDerivAt (coshGaussDeriv3Val c) (coshGaussDeriv4Val c t) t := by
  unfold coshGaussDeriv3Val coshGaussDeriv4Val
  have h_inner : HasDerivAt (fun u : ℝ => c * u) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h_cosh : HasDerivAt (fun u : ℝ => Real.cosh (c * u)) (Real.sinh (c * t) * c) t :=
    (Real.hasDerivAt_cosh (c * t)).comp t h_inner
  have h_sinh : HasDerivAt (fun u : ℝ => Real.sinh (c * u)) (Real.cosh (c * t) * c) t :=
    (Real.hasDerivAt_sinh (c * t)).comp t h_inner
  -- Polynomial A(t) := 48t - 12tc² - 64t³ (coefficient of cosh(ct)).
  have h_A : HasDerivAt (fun u : ℝ => 48 * u - 12 * u * c^2 - 64 * u^3)
      (48 - 12 * c^2 - 192 * t^2) t := by
    have h1 : HasDerivAt (fun u : ℝ => u^3) (3 * t^2) t := by
      simpa using hasDerivAt_pow 3 t
    have h_id : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
    have h48 : HasDerivAt (fun u : ℝ => 48 * u) 48 t := by
      simpa using h_id.const_mul (48 : ℝ)
    have h12 : HasDerivAt (fun u : ℝ => 12 * u * c^2) (12 * c^2) t := by
      have := (h_id.const_mul (12 : ℝ)).mul_const (c^2)
      simpa using this
    have h64 : HasDerivAt (fun u : ℝ => 64 * u^3) (192 * t^2) t := by
      have := h1.const_mul (64 : ℝ)
      convert this using 1
      ring
    have h_sub := (h48.sub h12).sub h64
    exact h_sub
  have h_A_cosh : HasDerivAt
      (fun u : ℝ => (48 * u - 12 * u * c^2 - 64 * u^3) * Real.cosh (c * u))
      ((48 - 12 * c^2 - 192 * t^2) * Real.cosh (c * t) +
       (48 * t - 12 * t * c^2 - 64 * t^3) * (Real.sinh (c * t) * c)) t :=
    h_A.mul h_cosh
  -- Polynomial B(t) := c³ - 12c + 48t²c (coefficient of sinh(ct)).
  have h_B : HasDerivAt (fun u : ℝ => c^3 - 12 * c + 48 * u^2 * c) (96 * t * c) t := by
    have h1 : HasDerivAt (fun u : ℝ => u^2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h48 : HasDerivAt (fun u : ℝ => 48 * u^2 * c) (48 * (2 * t) * c) t := by
      have := (h1.const_mul (48 : ℝ)).mul_const c
      simpa using this
    have h_sum := (hasDerivAt_const t (c^3 - 12 * c)).add h48
    convert h_sum using 1
    ring
  have h_B_sinh : HasDerivAt
      (fun u : ℝ => (c^3 - 12 * c + 48 * u^2 * c) * Real.sinh (c * u))
      ((96 * t * c) * Real.sinh (c * t) +
       (c^3 - 12 * c + 48 * t^2 * c) * (Real.cosh (c * t) * c)) t :=
    h_B.mul h_sinh
  have h_u : HasDerivAt
      (fun u : ℝ => (48 * u - 12 * u * c^2 - 64 * u^3) * Real.cosh (c * u) +
                    (c^3 - 12 * c + 48 * u^2 * c) * Real.sinh (c * u))
      ((48 - 12 * c^2 - 192 * t^2) * Real.cosh (c * t) +
       (48 * t - 12 * t * c^2 - 64 * t^3) * (Real.sinh (c * t) * c) +
       ((96 * t * c) * Real.sinh (c * t) +
        (c^3 - 12 * c + 48 * t^2 * c) * (Real.cosh (c * t) * c))) t :=
    h_A_cosh.add h_B_sinh
  -- exp(-2t²)
  have h_arg : HasDerivAt (fun u : ℝ => -2 * u^2) (-2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-2 : ℝ)
    simpa [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have h_exp : HasDerivAt (fun u : ℝ => Real.exp (-2 * u^2))
      (Real.exp (-2 * t^2) * (-2 * (2 * t))) t :=
    h_arg.exp
  have h_prod := h_u.mul h_exp
  convert h_prod using 1
  ring

#print axioms coshGaussDeriv4Val
#print axioms coshGauss_hasDerivAt_iter4

/-- **Gaussian decay `coshGaussDeriv4Val c =O[atTop] exp(-t/2)`.** -/
theorem coshGaussDeriv4Val_isBigO_exp_neg_half_atTop (c : ℝ) :
    (fun t : ℝ => ((coshGaussDeriv4Val c t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  have h_pow1_lito : (fun t : ℝ => t) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_pow2_lito : (fun t : ℝ => t^2) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_pow3_lito : (fun t : ℝ => t^3) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_pow4_lito : (fun t : ℝ => t^4) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 4 (by norm_num : (0:ℝ) < 1/2)
    simpa using this
  have h_const_lito : (fun _ : ℝ => (1:ℝ)) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have h : (fun t : ℝ => t^0) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
      have := isLittleO_pow_exp_pos_mul_atTop 0 (by norm_num : (0:ℝ) < 1/2)
      simpa using this
    simpa using h
  have h_cosh_gauss_R :
      (fun t : ℝ => (Real.cosh (c * t) * Real.exp (-2 * t^2) : ℝ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    have h := coshGauss_isBigO_exp_neg_atTop c
    rw [Asymptotics.isBigO_iff] at h ⊢
    obtain ⟨C, hC⟩ := h
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rwa [Complex.norm_real] at ht
  have h_sinh_gauss_R :
      (fun t : ℝ => (Real.sinh (c * t) * Real.exp (-2 * t^2) : ℝ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    have h := sinhGauss_isBigO_exp_neg_atTop c
    rw [Asymptotics.isBigO_iff] at h ⊢
    obtain ⟨C, hC⟩ := h
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rwa [Complex.norm_real] at ht
  have h_half_sum : (fun t : ℝ => Real.exp ((1/2) * t) * Real.exp (-t)) =
      (fun t : ℝ => Real.exp (-t/2)) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  -- Five o-small pieces: const, t², t⁴, t, t³ multiplied by cosh-gauss or sinh-gauss.
  have h_const_cosh_R :
      (fun t : ℝ => (1:ℝ) * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_const_lito.mul_isBigO h_cosh_gauss_R
    rw [← h_half_sum]; exact this
  have h_quad_cosh_R :
      (fun t : ℝ => t^2 * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow2_lito.mul_isBigO h_cosh_gauss_R
    rw [← h_half_sum]; exact this
  have h_quart_cosh_R :
      (fun t : ℝ => t^4 * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow4_lito.mul_isBigO h_cosh_gauss_R
    rw [← h_half_sum]; exact this
  have h_lin_sinh_R :
      (fun t : ℝ => t * (Real.sinh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow1_lito.mul_isBigO h_sinh_gauss_R
    rw [← h_half_sum]; exact this
  have h_cub_sinh_R :
      (fun t : ℝ => t^3 * (Real.sinh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have := h_pow3_lito.mul_isBigO h_sinh_gauss_R
    rw [← h_half_sum]; exact this
  have lift : ∀ (f : ℝ → ℝ), (f =o[atTop] fun t => Real.exp (-t/2)) →
      (fun t : ℝ => ((f t : ℝ) : ℂ)) =o[atTop] (fun t : ℝ => Real.exp (-t/2)) := by
    intro f hf
    rw [Asymptotics.isLittleO_iff] at hf ⊢
    intro c hc
    filter_upwards [hf hc] with t ht
    rwa [Complex.norm_real]
  -- coshGaussDeriv4Val c t =
  --   (c⁴ - 24c² + 48) · 1·cosh·exp
  --   + (96c² - 384) · t²·cosh·exp
  --   + 256 · t⁴·cosh·exp
  --   + (192c - 16c³) · t·sinh·exp
  --   + (-256c) · t³·sinh·exp
  have h_coerced_R :
      (fun t : ℝ => ((coshGaussDeriv4Val c t : ℝ) : ℂ)) =
      fun t : ℝ =>
        ((c^4 - 24*c^2 + 48) * ((1:ℝ) * (Real.cosh (c*t) * Real.exp (-2*t^2))) +
         (96*c^2 - 384) * (t^2 * (Real.cosh (c*t) * Real.exp (-2*t^2))) +
         (256 : ℝ) * (t^4 * (Real.cosh (c*t) * Real.exp (-2*t^2))) +
         (192*c - 16*c^3) * (t * (Real.sinh (c*t) * Real.exp (-2*t^2))) +
         (-256*c) * (t^3 * (Real.sinh (c*t) * Real.exp (-2*t^2))) : ℂ) := by
    funext t
    unfold coshGaussDeriv4Val
    push_cast; ring
  rw [h_coerced_R]
  have hL1 := (lift _ h_const_cosh_R).isBigO.const_mul_left (((c^4 - 24*c^2 + 48) : ℝ) : ℂ)
  have hL2 := (lift _ h_quad_cosh_R).isBigO.const_mul_left (((96*c^2 - 384) : ℝ) : ℂ)
  have hL3 := (lift _ h_quart_cosh_R).isBigO.const_mul_left (((256 : ℝ)) : ℂ)
  have hL4 := (lift _ h_lin_sinh_R).isBigO.const_mul_left (((192*c - 16*c^3) : ℝ) : ℂ)
  have hL5 := (lift _ h_cub_sinh_R).isBigO.const_mul_left (((-256*c) : ℝ) : ℂ)
  have h_final := (((hL1.add hL2).add hL3).add hL4).add hL5
  refine h_final.congr_left ?_
  intro t; push_cast; ring

#print axioms coshGaussDeriv4Val_isBigO_exp_neg_half_atTop

-- ═══════════════════════════════════════════════════════════════════════════
-- § Pair test 3rd and 4th derivatives (finite sum via cosh expansion)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **HasDerivAt for `deriv² pair`**: its derivative is the sum of `coshGaussDeriv3Val`. -/
theorem pair_cosh_gauss_test_hasDerivAt_iter3 (β t : ℝ) :
    HasDerivAt (deriv (deriv (pair_cosh_gauss_test β)))
      ((1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) t +
        (1/2) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t -
        coshGaussDeriv3Val (1 - Real.pi/3) t -
        coshGaussDeriv3Val (2*β - 1) t +
        coshGaussDeriv3Val 0 t) t := by
  have h_fun_eq : deriv (deriv (pair_cosh_gauss_test β)) = fun u =>
      (1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) u +
      (1/2) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) u -
      coshGaussDeriv2Val (1 - Real.pi/3) u -
      coshGaussDeriv2Val (2*β - 1) u +
      coshGaussDeriv2Val 0 u := by
    funext u; exact pair_cosh_gauss_test_deriv2_eq β u
  rw [h_fun_eq]
  have h1 := (coshGauss_hasDerivAt_iter3 (2*β - Real.pi/3) t).const_mul (1/2 : ℝ)
  have h2 := (coshGauss_hasDerivAt_iter3 (2 - Real.pi/3 - 2*β) t).const_mul (1/2 : ℝ)
  have h3 := coshGauss_hasDerivAt_iter3 (1 - Real.pi/3) t
  have h4 := coshGauss_hasDerivAt_iter3 (2*β - 1) t
  have h5 := coshGauss_hasDerivAt_iter3 0 t
  exact (((h1.add h2).sub h3).sub h4).add h5

/-- **Explicit `deriv³` formula for the pair test.** -/
theorem pair_cosh_gauss_test_deriv3_eq (β t : ℝ) :
    deriv (deriv (deriv (pair_cosh_gauss_test β))) t =
      (1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) t +
      (1/2) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t -
      coshGaussDeriv3Val (1 - Real.pi/3) t -
      coshGaussDeriv3Val (2*β - 1) t +
      coshGaussDeriv3Val 0 t :=
  (pair_cosh_gauss_test_hasDerivAt_iter3 β t).deriv

#print axioms pair_cosh_gauss_test_hasDerivAt_iter3
#print axioms pair_cosh_gauss_test_deriv3_eq

/-- **HasDerivAt for `deriv³ pair`**: its derivative is the sum of `coshGaussDeriv4Val`. -/
theorem pair_cosh_gauss_test_hasDerivAt_iter4 (β t : ℝ) :
    HasDerivAt (deriv (deriv (deriv (pair_cosh_gauss_test β))))
      ((1/2 : ℝ) * coshGaussDeriv4Val (2*β - Real.pi/3) t +
        (1/2) * coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t -
        coshGaussDeriv4Val (1 - Real.pi/3) t -
        coshGaussDeriv4Val (2*β - 1) t +
        coshGaussDeriv4Val 0 t) t := by
  have h_fun_eq : deriv (deriv (deriv (pair_cosh_gauss_test β))) = fun u =>
      (1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) u +
      (1/2) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) u -
      coshGaussDeriv3Val (1 - Real.pi/3) u -
      coshGaussDeriv3Val (2*β - 1) u +
      coshGaussDeriv3Val 0 u := by
    funext u; exact pair_cosh_gauss_test_deriv3_eq β u
  rw [h_fun_eq]
  have h1 := (coshGauss_hasDerivAt_iter4 (2*β - Real.pi/3) t).const_mul (1/2 : ℝ)
  have h2 := (coshGauss_hasDerivAt_iter4 (2 - Real.pi/3 - 2*β) t).const_mul (1/2 : ℝ)
  have h3 := coshGauss_hasDerivAt_iter4 (1 - Real.pi/3) t
  have h4 := coshGauss_hasDerivAt_iter4 (2*β - 1) t
  have h5 := coshGauss_hasDerivAt_iter4 0 t
  exact (((h1.add h2).sub h3).sub h4).add h5

/-- **Explicit `deriv⁴` formula for the pair test.** -/
theorem pair_cosh_gauss_test_deriv4_eq (β t : ℝ) :
    deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t =
      (1/2 : ℝ) * coshGaussDeriv4Val (2*β - Real.pi/3) t +
      (1/2) * coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t -
      coshGaussDeriv4Val (1 - Real.pi/3) t -
      coshGaussDeriv4Val (2*β - 1) t +
      coshGaussDeriv4Val 0 t :=
  (pair_cosh_gauss_test_hasDerivAt_iter4 β t).deriv

#print axioms pair_cosh_gauss_test_hasDerivAt_iter4
#print axioms pair_cosh_gauss_test_deriv4_eq

-- ═══════════════════════════════════════════════════════════════════════════
-- § Gaussian decay + near-zero bounds for pair deriv3, deriv4
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`deriv³ (pair β) =O[atTop] exp(-t/2)`.** Five-term cosh expansion. -/
theorem pair_cosh_gauss_test_deriv3_isBigO_exp_neg_half_atTop (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  have h_eq : (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (((1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) t : ℝ) : ℂ) +
        (((1/2 : ℝ) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ) -
        ((coshGaussDeriv3Val (1 - Real.pi/3) t : ℝ) : ℂ) -
        ((coshGaussDeriv3Val (2*β - 1) t : ℝ) : ℂ) +
        ((coshGaussDeriv3Val 0 t : ℝ) : ℂ)) := by
    funext t
    rw [pair_cosh_gauss_test_deriv3_eq]
    push_cast; ring
  rw [h_eq]
  have h1 := (coshGaussDeriv3Val_isBigO_exp_neg_half_atTop (2*β - Real.pi/3)).const_mul_left (1/2 : ℂ)
  have h2 := (coshGaussDeriv3Val_isBigO_exp_neg_half_atTop (2 - Real.pi/3 - 2*β)).const_mul_left (1/2 : ℂ)
  have h3 := coshGaussDeriv3Val_isBigO_exp_neg_half_atTop (1 - Real.pi/3)
  have h4 := coshGaussDeriv3Val_isBigO_exp_neg_half_atTop (2*β - 1)
  have h5 := coshGaussDeriv3Val_isBigO_exp_neg_half_atTop 0
  have h1' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv3Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv3Val (2*β - Real.pi/3) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h1
  have h2' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv3Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h2
  exact ((((h1'.add h2').sub h3).sub h4).add h5)

#print axioms pair_cosh_gauss_test_deriv3_isBigO_exp_neg_half_atTop

/-- **`deriv⁴ (pair β) =O[atTop] exp(-t/2)`.** Five-term cosh expansion. -/
theorem pair_cosh_gauss_test_deriv4_isBigO_exp_neg_half_atTop (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  have h_eq : (fun t : ℝ =>
      ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (((1/2 : ℝ) * coshGaussDeriv4Val (2*β - Real.pi/3) t : ℝ) : ℂ) +
        (((1/2 : ℝ) * coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ) -
        ((coshGaussDeriv4Val (1 - Real.pi/3) t : ℝ) : ℂ) -
        ((coshGaussDeriv4Val (2*β - 1) t : ℝ) : ℂ) +
        ((coshGaussDeriv4Val 0 t : ℝ) : ℂ)) := by
    funext t
    rw [pair_cosh_gauss_test_deriv4_eq]
    push_cast; ring
  rw [h_eq]
  have h1 := (coshGaussDeriv4Val_isBigO_exp_neg_half_atTop (2*β - Real.pi/3)).const_mul_left (1/2 : ℂ)
  have h2 := (coshGaussDeriv4Val_isBigO_exp_neg_half_atTop (2 - Real.pi/3 - 2*β)).const_mul_left (1/2 : ℂ)
  have h3 := coshGaussDeriv4Val_isBigO_exp_neg_half_atTop (1 - Real.pi/3)
  have h4 := coshGaussDeriv4Val_isBigO_exp_neg_half_atTop (2*β - 1)
  have h5 := coshGaussDeriv4Val_isBigO_exp_neg_half_atTop 0
  have h1' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv4Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv4Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv4Val (2*β - Real.pi/3) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h1
  have h2' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv4Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h2
  exact ((((h1'.add h2').sub h3).sub h4).add h5)

#print axioms pair_cosh_gauss_test_deriv4_isBigO_exp_neg_half_atTop

/-- **`deriv³ (pair β)` bounded near `0`**: continuity at 0 ⟹ bounded. -/
theorem pair_cosh_gauss_test_deriv3_isBigO_one_nhds_zero (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(0:ℝ))) := by
  have h_deriv3_cont : Continuous (deriv (deriv (deriv (pair_cosh_gauss_test β)))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 3
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_cont : Continuous
      (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_deriv3_cont
  have h_tendsto : Filter.Tendsto
      (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((deriv (deriv (deriv (pair_cosh_gauss_test β))) 0 : ℝ) : ℂ))) :=
    (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
    funext x; rw [neg_zero, Real.rpow_zero]
  rw [h_rpow_eq]
  exact h_tendsto.isBigO_one ℝ

#print axioms pair_cosh_gauss_test_deriv3_isBigO_one_nhds_zero

/-- **`deriv⁴ (pair β)` bounded near `0`**: continuity at 0 ⟹ bounded. -/
theorem pair_cosh_gauss_test_deriv4_isBigO_one_nhds_zero (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ))
      =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  have h_deriv4_cont : Continuous (deriv (deriv (deriv (deriv (pair_cosh_gauss_test β))))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 4
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_cont : Continuous
      (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_deriv4_cont
  have h_tendsto : Filter.Tendsto
      (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) 0 : ℝ) : ℂ))) :=
    (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
    funext x; rw [neg_zero, Real.rpow_zero]
  rw [h_rpow_eq]
  exact h_tendsto.isBigO_one ℝ

#print axioms pair_cosh_gauss_test_deriv4_isBigO_one_nhds_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § MellinConvergent for pair deriv3, deriv4
-- ═══════════════════════════════════════════════════════════════════════════

/-- **MellinConvergent for pair deriv³ on Re s > 0.** -/
theorem mellinConvergent_pair_cosh_gauss_test_deriv3 (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0) (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 3
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  · have h := pair_cosh_gauss_test_deriv3_isBigO_exp_neg_half_atTop β
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]; exact h
  · exact pair_cosh_gauss_test_deriv3_isBigO_one_nhds_zero β
  · exact hs

#print axioms mellinConvergent_pair_cosh_gauss_test_deriv3

/-- **MellinConvergent for pair deriv⁴ on Re s > 0.** -/
theorem mellinConvergent_pair_cosh_gauss_test_deriv4 (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0) (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 4
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  · have h := pair_cosh_gauss_test_deriv4_isBigO_exp_neg_half_atTop β
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]; exact h
  · exact pair_cosh_gauss_test_deriv4_isBigO_one_nhds_zero β
  · exact hs

#print axioms mellinConvergent_pair_cosh_gauss_test_deriv4

-- ═══════════════════════════════════════════════════════════════════════════
-- § Boundary vanishing of t^s · iteratedDeriv k pair at t=0 and t=∞
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Value of deriv² pair at t=0 equals finite constant.** -/
theorem pair_cosh_gauss_test_deriv2_at_zero (β : ℝ) :
    ∃ M : ℝ, |deriv (deriv (pair_cosh_gauss_test β)) 0| ≤ M := by
  exact ⟨|deriv (deriv (pair_cosh_gauss_test β)) 0|, le_refl _⟩

/-- Boundary vanishing pattern: generic — for a continuous function `f : ℝ → ℝ`
and `Re s > 0`, `f(t) · t^s → 0` as `t → 0⁺`. -/
private lemma cpow_tendsto_zero_nhdsWithin_zero_of_continuous
    (f : ℝ → ℝ) (hf_cont : Continuous f) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => ((f t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- |f(t) · t^s| ≤ |f(t)| · t^Re(s). f continuous ⟹ bounded near 0. t^Re(s) → 0.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h_tendsto : Filter.Tendsto f (nhds 0) (nhds (f 0)) := hf_cont.continuousAt.tendsto
  rw [Metric.tendsto_nhds_nhds] at h_tendsto
  -- Bound |f(t) - f(0)| < 1 ⟹ |f(t)| < |f(0)| + 1 for t near 0.
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h_tendsto 1 (by norm_num : (0:ℝ) < 1)
  set M : ℝ := |f 0| + 1 with hM_def
  have hM_pos : 0 < M := by simp [hM_def]; positivity
  -- Choose δ = min δ₁ (ε/M)^(1/Re s).
  refine ⟨min δ₁ ((ε/M) ^ (1 / s.re)),
    lt_min hδ₁_pos (Real.rpow_pos_of_pos (div_pos hε hM_pos) _), ?_⟩
  intro t ht_pos ht_δ
  have ht_pos' : 0 < t := ht_pos
  have h_t_lt_δ₁ : dist t 0 < δ₁ := lt_of_lt_of_le ht_δ (min_le_left _ _)
  have h_t_lt_ε_rpow : dist t 0 < (ε/M) ^ (1 / s.re) := lt_of_lt_of_le ht_δ (min_le_right _ _)
  have h_f_lt : |f t| < M := by
    have := hδ₁ h_t_lt_δ₁
    rw [Real.dist_eq] at this
    have h_abs : |f t| ≤ |f t - f 0| + |f 0| := by
      calc |f t| = |(f t - f 0) + f 0| := by ring_nf
        _ ≤ |f t - f 0| + |f 0| := abs_add_le _ _
    simp [hM_def]; linarith
  have h_t_cpow_norm : ‖(t : ℂ)^s‖ = t^s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos' s
  have h_t_lt_ε_rpow_abs : t < (ε/M) ^ (1 / s.re) := by
    rw [Real.dist_eq, sub_zero] at h_t_lt_ε_rpow
    have : |t| = t := abs_of_pos ht_pos'
    rw [this] at h_t_lt_ε_rpow; exact h_t_lt_ε_rpow
  have hεM_pos : 0 < ε / M := div_pos hε hM_pos
  have h_t_rpow_lt : t ^ s.re < ε / M := by
    calc t ^ s.re < ((ε/M) ^ (1 / s.re)) ^ s.re :=
          Real.rpow_lt_rpow (le_of_lt ht_pos') h_t_lt_ε_rpow_abs hs
      _ = (ε/M) ^ ((1 / s.re) * s.re) := by rw [← Real.rpow_mul hεM_pos.le]
      _ = (ε/M) ^ (1:ℝ) := by rw [div_mul_cancel₀ _ hs.ne']
      _ = ε/M := Real.rpow_one _
  have h_t_rpow_pos : 0 < t ^ s.re := Real.rpow_pos_of_pos ht_pos' _
  have h_f_nn : 0 ≤ |f t| := abs_nonneg _
  calc dist (((f t : ℝ) : ℂ) * (t : ℂ)^s) 0
      = ‖((f t : ℝ) : ℂ) * (t : ℂ)^s‖ := by rw [dist_zero_right]
    _ = |f t| * t^s.re := by
          rw [norm_mul, h_t_cpow_norm]
          congr 1; exact Complex.norm_real _
    _ ≤ M * t^s.re := by
          apply mul_le_mul_of_nonneg_right h_f_lt.le h_t_rpow_pos.le
    _ < M * (ε/M) := by
          apply mul_lt_mul_of_pos_left h_t_rpow_lt hM_pos
    _ = ε := by field_simp

/-- Boundary vanishing pattern at infinity: for `f : ℝ → ℝ` with
`(fun t => (f t : ℂ)) =O[atTop] exp(-t/2)`, `f(t) · t^s → 0` as `t → ∞`. -/
private lemma cpow_tendsto_zero_atTop_of_exp_neg_half_bigO
    (f : ℝ → ℝ)
    (hf : (fun t : ℝ => ((f t : ℝ) : ℂ)) =O[atTop] (fun t : ℝ => Real.exp (-t/2)))
    (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => ((f t : ℝ) : ℂ) * (t : ℂ)^s) Filter.atTop (nhds 0) := by
  have h_bigO : (fun t : ℝ => ((f t : ℝ) : ℂ) * (t : ℂ)^s) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) := by
    have h_cpow_bigO : (fun t : ℝ => (t : ℂ)^s) =O[atTop] (fun t : ℝ => t^s.re) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
    exact hf.mul h_cpow_bigO
  have h_tendsto_dom :
      Filter.Tendsto (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) atTop (nhds 0) := by
    have h_lit : (fun t : ℝ => t^s.re) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) :=
      isLittleO_rpow_exp_pos_mul_atTop s.re (by norm_num : (0:ℝ) < 1/2)
    have h_tendsto :
        Filter.Tendsto (fun t : ℝ => t^s.re / Real.exp ((1/2) * t)) atTop (nhds 0) :=
      h_lit.tendsto_div_nhds_zero
    have h_eq : (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) =
        (fun t : ℝ => t^s.re / Real.exp ((1/2) * t)) := by
      funext t
      have h1 : (-t/2 : ℝ) = -((1/2) * t) := by ring
      rw [h1, Real.exp_neg]; field_simp
    rw [h_eq]; exact h_tendsto
  exact h_bigO.trans_tendsto h_tendsto_dom

/-- **Boundary vanishing of `t^s · deriv² pair(t)` at `t → 0⁺`** for `Re s > 0`. -/
theorem pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_nhdsWithin_zero
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ =>
        ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cont : Continuous (deriv (deriv (pair_cosh_gauss_test β))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 2
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  exact cpow_tendsto_zero_nhdsWithin_zero_of_continuous _ h_cont hs

/-- **Boundary vanishing of `t^s · deriv² pair(t)` at `t → ∞`** for any `s`. -/
theorem pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_atTop (β : ℝ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ =>
        ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  cpow_tendsto_zero_atTop_of_exp_neg_half_bigO _
    (pair_cosh_gauss_test_deriv2_isBigO_exp_neg_half_atTop β) s

/-- **Boundary vanishing of `t^s · deriv³ pair(t)` at `t → 0⁺`** for `Re s > 0`. -/
theorem pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_nhdsWithin_zero
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ =>
        ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cont : Continuous (deriv (deriv (deriv (pair_cosh_gauss_test β)))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 3
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  exact cpow_tendsto_zero_nhdsWithin_zero_of_continuous _ h_cont hs

/-- **Boundary vanishing of `t^s · deriv³ pair(t)` at `t → ∞`** for any `s`. -/
theorem pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_atTop (β : ℝ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ =>
        ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) :=
  cpow_tendsto_zero_atTop_of_exp_neg_half_bigO _
    (pair_cosh_gauss_test_deriv3_isBigO_exp_neg_half_atTop β) s

#print axioms pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_nhdsWithin_zero
#print axioms pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_atTop
#print axioms pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_nhdsWithin_zero
#print axioms pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_atTop

-- ═══════════════════════════════════════════════════════════════════════════
-- § pairDeriv3Mellin, pairDeriv4Mellin + IBP steps 3,4
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Abbreviation: `pairDeriv3Mellin`.** Mellin of the 3rd derivative, coerced. -/
noncomputable def pairDeriv3Mellin (β : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) s

/-- **Abbreviation: `pairDeriv4Mellin`.** Mellin of the 4th derivative, coerced. -/
noncomputable def pairDeriv4Mellin (β : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) s

/-- **HasDerivAt for the coerced 2nd derivative (complex-valued).** -/
theorem coerced_pair_deriv2_hasDerivAt (β : ℝ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) y : ℝ) : ℂ))
      (((deriv (deriv (deriv (pair_cosh_gauss_test β))) t : ℝ) : ℂ)) t := by
  have h_diff : Differentiable ℝ (deriv (deriv (pair_cosh_gauss_test β))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_differentiable β 2
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  exact (h_diff t).hasDerivAt.ofReal_comp

/-- **HasDerivAt for the coerced 3rd derivative.** -/
theorem coerced_pair_deriv3_hasDerivAt (β : ℝ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((deriv (deriv (deriv (pair_cosh_gauss_test β))) y : ℝ) : ℂ))
      (((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)) t := by
  have h_diff : Differentiable ℝ (deriv (deriv (deriv (pair_cosh_gauss_test β)))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_differentiable β 3
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  exact (h_diff t).hasDerivAt.ofReal_comp

/-- **IBP step 3: single IBP on `pairDeriv2Mellin`.** For `0 < Re s`:
```
pairDeriv2Mellin β (s+2) = -(1/(s+2)) · pairDeriv3Mellin β (s+3).
```
-/
theorem pairDeriv2Mellin_ibp_once (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairDeriv2Mellin β (s + 2) = -(1/(s+2)) * pairDeriv3Mellin β (s + 3) := by
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have hs2_ne : (s + 2) ≠ 0 := fun h => by rw [h] at hs2_re; simp at hs2_re
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have h_rewrite : s + 2 + 1 = s + 3 := by ring
  unfold pairDeriv2Mellin pairDeriv3Mellin
  have := mellin_ibp (s := s + 2) hs2_ne
    (fun t _ => coerced_pair_deriv2_hasDerivAt β t)
    (mellinConvergent_pair_cosh_gauss_test_deriv2 β hs2_re)
    (by rw [h_rewrite]; exact mellinConvergent_pair_cosh_gauss_test_deriv3 β hs3_re)
    (pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_nhdsWithin_zero β hs2_re)
    (pair_cosh_gauss_test_deriv2_cpow_tendsto_zero_atTop β (s + 2))
  rw [h_rewrite] at this
  exact this

#print axioms pairDeriv2Mellin_ibp_once

/-- **IBP step 4: single IBP on `pairDeriv3Mellin`.** For `0 < Re s`:
```
pairDeriv3Mellin β (s+3) = -(1/(s+3)) · pairDeriv4Mellin β (s+4).
```
-/
theorem pairDeriv3Mellin_ibp_once (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairDeriv3Mellin β (s + 3) = -(1/(s+3)) * pairDeriv4Mellin β (s + 4) := by
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have hs3_ne : (s + 3) ≠ 0 := fun h => by rw [h] at hs3_re; simp at hs3_re
  have hs4_re : 0 < (s + 4).re := by simp; linarith
  have h_rewrite : s + 3 + 1 = s + 4 := by ring
  unfold pairDeriv3Mellin pairDeriv4Mellin
  have := mellin_ibp (s := s + 3) hs3_ne
    (fun t _ => coerced_pair_deriv3_hasDerivAt β t)
    (mellinConvergent_pair_cosh_gauss_test_deriv3 β hs3_re)
    (by rw [h_rewrite]; exact mellinConvergent_pair_cosh_gauss_test_deriv4 β hs4_re)
    (pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_nhdsWithin_zero β hs3_re)
    (pair_cosh_gauss_test_deriv3_cpow_tendsto_zero_atTop β (s + 3))
  rw [h_rewrite] at this
  exact this

#print axioms pairDeriv3Mellin_ibp_once

/-- **Four-step Mellin IBP on `pairTestMellin β`.** Composing the 2-step IBP
(already proved) with the two new steps:
```
pairTestMellin β s = (1/(s·(s+1)·(s+2)·(s+3))) · pairDeriv4Mellin β (s+4).
```
-/
theorem pairTestMellin_ibp_four_times (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairTestMellin β s =
      1/(s*(s+1)*(s+2)*(s+3)) * pairDeriv4Mellin β (s + 4) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have hs2_ne : (s + 2) ≠ 0 := fun h => by rw [h] at hs2_re; simp at hs2_re
  have hs3_re : 0 < (s + 3).re := by simp; linarith
  have hs3_ne : (s + 3) ≠ 0 := fun h => by rw [h] at hs3_re; simp at hs3_re
  rw [pairTestMellin_ibp_twice β hs]
  rw [pairDeriv2Mellin_ibp_once β hs]
  rw [pairDeriv3Mellin_ibp_once β hs]
  field_simp

#print axioms pairTestMellin_ibp_four_times

-- ═══════════════════════════════════════════════════════════════════════════
-- § Uniform norm bound on `pairDeriv4Mellin` on compact strip
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Real Mellin integrand of `|deriv⁴ pair β|` is integrable on `Ioi 0`.** -/
theorem pair_deriv4_mellin_integrand_integrableOn (β : ℝ) (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ =>
      t^(σ-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) (Ioi 0) := by
  set s : ℂ := (σ : ℂ)
  have hs_re : (0 : ℝ) < s.re := by simp [s]; exact hσ
  have hConv := mellinConvergent_pair_cosh_gauss_test_deriv4 β hs_re
  unfold MellinConvergent at hConv
  have hnorm := hConv.norm
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr hnorm
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real]
  simp [s]

/-- **Pointwise norm bound**: `‖pairDeriv4Mellin β s‖ ≤ ∫ t^(σ-1)·|deriv⁴ pair|`. -/
theorem pairDeriv4Mellin_norm_le_real_integral (β : ℝ) (s : ℂ) :
    ‖pairDeriv4Mellin β s‖ ≤
      ∫ t in Ioi (0:ℝ),
        t^(s.re - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| := by
  unfold pairDeriv4Mellin mellin
  calc ‖∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) •
          ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1) •
          ((deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t : ℝ) : ℂ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0:ℝ), t^(s.re - 1) *
          |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
          Complex.sub_re, Complex.one_re, Real.norm_eq_abs]

/-- **Uniform norm bound on `pairDeriv4Mellin` on compact strip `[σL, σR]`.** -/
theorem pairDeriv4Mellin_norm_bound_on_compact_strip
    (β : ℝ) (σL σR : ℝ) (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR →
      ‖pairDeriv4Mellin β s‖ ≤ C := by
  have h_int_L := pair_deriv4_mellin_integrand_integrableOn β σL hσL
  have h_int_R := pair_deriv4_mellin_integrand_integrableOn β σR (lt_of_lt_of_le hσL hσLR)
  set I_L : ℝ := ∫ t in Ioi (0:ℝ),
    t^(σL-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|
  set I_R : ℝ := ∫ t in Ioi (0:ℝ),
    t^(σR-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|
  set C : ℝ := I_L + I_R
  have hI_L_nonneg : 0 ≤ I_L :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (abs_nonneg _))
  have hI_R_nonneg : 0 ≤ I_R :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (abs_nonneg _))
  refine ⟨C, add_nonneg hI_L_nonneg hI_R_nonneg, fun s hσL_le_re hre_le_R => ?_⟩
  have hbound := pairDeriv4Mellin_norm_le_real_integral β s
  have h_dom : ∀ t ∈ Ioi (0:ℝ),
      t^(s.re - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| ≤
        t^(σL - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| +
          t^(σR - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    have h_d4_nn : 0 ≤ |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| :=
      abs_nonneg _
    have h_rpow_bd : t^(s.re - 1) ≤ t^(σL-1) + t^(σR-1) := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(s.re - 1) ≤ t^(σL-1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σR - 1)]
      · have h1 : t^(s.re - 1) ≤ t^(σR-1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
    calc t^(s.re - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|
        ≤ (t^(σL - 1) + t^(σR-1)) *
            |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_d4_nn
      _ = t^(σL - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| +
            t^(σR-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| := by
          ring
  have h_rhs_integrable : IntegrableOn (fun t : ℝ =>
      t^(σL - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| +
      t^(σR-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) (Ioi 0) :=
    h_int_L.add h_int_R
  have h_lhs_integrable : IntegrableOn (fun t : ℝ =>
      t^(s.re - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) (Ioi 0) :=
    pair_deriv4_mellin_integrand_integrableOn β s.re (by linarith)
  have h_integral_le :
      (∫ t in Ioi (0:ℝ),
        t^(s.re - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) ≤
      ∫ t in Ioi (0:ℝ),
        (t^(σL - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| +
         t^(σR-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|) :=
    MeasureTheory.setIntegral_mono_on h_lhs_integrable h_rhs_integrable
      measurableSet_Ioi h_dom
  have h_integral_split :
      (∫ t in Ioi (0:ℝ),
          (t^(σL - 1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t| +
           t^(σR-1) * |deriv (deriv (deriv (deriv (pair_cosh_gauss_test β)))) t|)) =
      I_L + I_R := by
    rw [MeasureTheory.integral_add h_int_L h_int_R]
  linarith

#print axioms pairDeriv4Mellin_norm_bound_on_compact_strip

-- ═══════════════════════════════════════════════════════════════════════════
-- § Quartic decay on vertical strip (uniform in σ, M=4 specific)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Quartic decay of `pairTestMellin β` on vertical strip `[σL, σR]` with `σL > 0`.**
Unconditional: for every `β`, `σL ∈ (0, ∞)`, `σR ∈ [σL, ∞)`, `T` with `|T| ≥ 1`,
`‖pairTestMellin β (σ+iT)‖ ≤ C_{β,σL,σR} / |T|^4` for every `σ ∈ [σL, σR]`.

This is the **M=4 uniform-on-strip** Mellin decay — the specific instance of
`pairTestMellin_super_poly_decay_target` at `M = 4`, derivable from IBP×4
without requiring the universal-M Schwartz machinery. -/
theorem pairTestMellin_quartic_decay_on_strip (β : ℝ) (σL σR : ℝ)
    (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ |T| → ∀ σ ∈ Set.Icc σL σR,
        ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * |T|^(-(4:ℝ)) := by
  obtain ⟨M, hM_nn, hM⟩ :=
    pairDeriv4Mellin_norm_bound_on_compact_strip β (σL + 4) (σR + 4)
      (by linarith) (by linarith)
  refine ⟨max M 1, 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    by norm_num, ?_⟩
  intro T hT_ge σ hσ_mem
  obtain ⟨hσL_le, hσ_le_R⟩ := hσ_mem
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = T := by simp [s]
  have hs_re_pos : 0 < s.re := by rw [hs_re]; linarith
  -- Apply 4-step IBP.
  have h_ibp := pairTestMellin_ibp_four_times β hs_re_pos
  -- Bound pairDeriv4Mellin at s+4: Re(s+4) ∈ [σL+4, σR+4].
  have h_re_s4 : (s + 4).re = s.re + 4 := by simp
  have h_s4_in : σL + 4 ≤ (s + 4).re ∧ (s + 4).re ≤ σR + 4 := by
    rw [h_re_s4, hs_re]; exact ⟨by linarith, by linarith⟩
  have h_deriv4_bd : ‖pairDeriv4Mellin β (s + 4)‖ ≤ M :=
    hM (s + 4) h_s4_in.1 h_s4_in.2
  -- |T| ≥ 1 ⟹ T ≠ 0.
  have hT_pos : 0 < |T| := lt_of_lt_of_le zero_lt_one hT_ge
  have hT_ne : T ≠ 0 := by intro h; rw [h] at hT_pos; simp at hT_pos
  have h_s_ne : s ≠ 0 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hs_im] at this; exact hT_ne this
  have h_s1_ne : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).im = 0 := by rw [h]; simp
    have : s.im = 0 := by simpa using this
    rw [hs_im] at this; exact hT_ne this
  have h_s2_ne : s + 2 ≠ 0 := by
    intro h
    have : (s + 2).im = 0 := by rw [h]; simp
    have : s.im = 0 := by simpa using this
    rw [hs_im] at this; exact hT_ne this
  have h_s3_ne : s + 3 ≠ 0 := by
    intro h
    have : (s + 3).im = 0 := by rw [h]; simp
    have : s.im = 0 := by simpa using this
    rw [hs_im] at this; exact hT_ne this
  -- |s|² ≥ T², |s+k|² ≥ T² for k = 1, 2, 3 (since Im = T in all cases).
  have hT_abs_sq : |T|^2 = T^2 := sq_abs T
  have h_s_abs_ge_T : ‖s‖ ≥ |T| := by
    have h_normSq : Complex.normSq s = s.re^2 + s.im^2 := by
      rw [Complex.normSq_apply]; ring
    have h_normSq_eq : ‖s‖^2 = Complex.normSq s := (Complex.normSq_eq_norm_sq s).symm
    have h_sq_ge : ‖s‖^2 ≥ T^2 := by
      rw [h_normSq_eq, h_normSq, hs_im]
      nlinarith [sq_nonneg s.re, sq_nonneg T]
    have h_nn : 0 ≤ ‖s‖ := norm_nonneg _
    have : ‖s‖^2 ≥ |T|^2 := by rw [hT_abs_sq]; exact h_sq_ge
    exact abs_le_of_sq_le_sq' this h_nn |>.2
  have h_sk_abs_ge_T : ∀ k : ℕ, ‖s + (k : ℂ)‖ ≥ |T| := by
    intro k
    have h_normSq : Complex.normSq (s + k) = (s + k).re^2 + (s + k).im^2 := by
      rw [Complex.normSq_apply]; ring
    have h_normSq_eq : ‖s + k‖^2 = Complex.normSq (s + k) :=
      (Complex.normSq_eq_norm_sq _).symm
    have h_im : (s + k).im = T := by
      rw [Complex.add_im, hs_im]; simp
    have h_sq_ge : ‖s + k‖^2 ≥ T^2 := by
      rw [h_normSq_eq, h_normSq, h_im]
      nlinarith [sq_nonneg (s + k).re, sq_nonneg T]
    have h_nn : 0 ≤ ‖s + k‖ := norm_nonneg _
    have : ‖s + k‖^2 ≥ |T|^2 := by rw [hT_abs_sq]; exact h_sq_ge
    exact abs_le_of_sq_le_sq' this h_nn |>.2
  have h_s1_ge : ‖s + 1‖ ≥ |T| := by
    have := h_sk_abs_ge_T 1; simpa using this
  have h_s2_ge : ‖s + 2‖ ≥ |T| := by
    have := h_sk_abs_ge_T 2; simpa using this
  have h_s3_ge : ‖s + 3‖ ≥ |T| := by
    have := h_sk_abs_ge_T 3; simpa using this
  -- |s·(s+1)·(s+2)·(s+3)| ≥ |T|^4.
  have h_prod_abs_ge : ‖s * (s + 1) * (s + 2) * (s + 3)‖ ≥ |T|^4 := by
    rw [show (s * (s + 1) * (s + 2) * (s + 3) : ℂ) = s * ((s + 1) * ((s + 2) * (s + 3))) by ring]
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : 0 ≤ ‖s‖ := norm_nonneg _
    have h2 : 0 ≤ ‖s + 1‖ := norm_nonneg _
    have h3 : 0 ≤ ‖s + 2‖ := norm_nonneg _
    have h4 : 0 ≤ ‖s + 3‖ := norm_nonneg _
    have hT_abs_nn : 0 ≤ |T| := abs_nonneg _
    calc ‖s‖ * (‖s + 1‖ * (‖s + 2‖ * ‖s + 3‖))
        ≥ |T| * (|T| * (|T| * |T|)) := by
          apply mul_le_mul h_s_abs_ge_T _ (by positivity) h1
          apply mul_le_mul h_s1_ge _ (by positivity) h2
          apply mul_le_mul h_s2_ge h_s3_ge hT_abs_nn h3
      _ = |T|^4 := by ring
  have h_prod_ne : s * (s + 1) * (s + 2) * (s + 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h_s_ne h_s1_ne) h_s2_ne) h_s3_ne
  have h_prod_pos : 0 < ‖s * (s + 1) * (s + 2) * (s + 3)‖ := norm_pos_iff.mpr h_prod_ne
  have hT_pow4_pos : 0 < |T|^(4:ℝ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    positivity
  -- Rewrite target: C · |T|^(-4) = C / |T|^4.
  have h_rpow_neg : |T|^(-(4:ℝ)) = 1 / |T|^(4:ℝ) := by
    rw [Real.rpow_neg (abs_nonneg _)]; rw [one_div]
  rw [h_rpow_neg, h_ibp, norm_mul, norm_div, norm_one]
  have hT_pow4_eq_nat : |T|^(4:ℝ) = |T|^4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have h_div_bd : 1 / ‖s * (s + 1) * (s + 2) * (s + 3)‖ ≤ 1 / |T|^(4:ℝ) := by
    rw [hT_pow4_eq_nat]
    rw [div_le_div_iff₀ h_prod_pos (by positivity : (0:ℝ) < |T|^4)]
    linarith [h_prod_abs_ge]
  calc 1 / ‖s * (s + 1) * (s + 2) * (s + 3)‖ * ‖pairDeriv4Mellin β (s + 4)‖
      ≤ 1 / |T|^(4:ℝ) * M := by
        apply mul_le_mul h_div_bd h_deriv4_bd (norm_nonneg _) (by positivity)
    _ ≤ max M 1 * (1 / |T|^(4:ℝ)) := by
        rw [mul_comm (1/|T|^(4:ℝ)) M]
        apply mul_le_mul_of_nonneg_right (le_max_left M 1) (by positivity)

#print axioms pairTestMellin_quartic_decay_on_strip

-- ═══════════════════════════════════════════════════════════════════════════
-- § High-Im quartic decay: direct from IBP×4 + product lower bound
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Product lower bound.** For `ρ` with `0 < Re ρ < 1` and `1 ≤ |Im ρ|`:
`|ρ·(ρ+1)·(ρ+2)·(ρ+3)|² ≥ (1+Im²ρ)⁴ / 2`. -/
theorem abs_rho_prod_four_ge_quartic {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (h_Im : 1 ≤ |ρ.im|) :
    (1 + ρ.im^2)^2 / Real.sqrt 2 ≤ ‖ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)‖ := by
  rcases hρ with ⟨hRe_pos, hRe_lt, _⟩
  have h_im_sq_ge : (1:ℝ) ≤ ρ.im^2 := by
    have : ρ.im^2 = |ρ.im|^2 := by rw [sq_abs]
    rw [this]; nlinarith [h_Im]
  -- Lower bounds on individual normSq factors.
  have h_ρ_sq : ρ.im^2 ≤ Complex.normSq ρ := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg ρ.re]
  have h_ρ1_sq : 1 + ρ.im^2 ≤ Complex.normSq (ρ + 1) := by
    rw [Complex.normSq_apply]
    have h_re : (ρ + 1).re = ρ.re + 1 := by simp
    have h_im : (ρ + 1).im = ρ.im := by simp
    rw [h_re, h_im]
    nlinarith [hRe_pos, sq_nonneg ρ.im]
  have h_ρ2_sq : 4 + ρ.im^2 ≤ Complex.normSq (ρ + 2) := by
    rw [Complex.normSq_apply]
    have h_re : (ρ + 2).re = ρ.re + 2 := by simp
    have h_im : (ρ + 2).im = ρ.im := by simp
    rw [h_re, h_im]
    nlinarith [hRe_pos, sq_nonneg ρ.im]
  have h_ρ3_sq : 9 + ρ.im^2 ≤ Complex.normSq (ρ + 3) := by
    rw [Complex.normSq_apply]
    have h_re : (ρ + 3).re = ρ.re + 3 := by simp
    have h_im : (ρ + 3).im = ρ.im := by simp
    rw [h_re, h_im]
    nlinarith [hRe_pos, sq_nonneg ρ.im]
  -- Convert each lower bound to (1+Im²ρ)/2 or (1+Im²ρ).
  have hQ : 0 ≤ 1 + ρ.im^2 := by linarith [sq_nonneg ρ.im]
  have hQ_pos : 0 < 1 + ρ.im^2 := by linarith [sq_nonneg ρ.im]
  have h_ρ_sq' : (1 + ρ.im^2) / 2 ≤ Complex.normSq ρ := by
    have : (1 + ρ.im^2) / 2 ≤ ρ.im^2 := by linarith
    linarith
  have h_ρ2_sq' : 1 + ρ.im^2 ≤ Complex.normSq (ρ + 2) := by linarith
  have h_ρ3_sq' : 1 + ρ.im^2 ≤ Complex.normSq (ρ + 3) := by linarith
  -- Combine into normSq of product.
  have h_normSq_prod :
      Complex.normSq (ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)) =
        Complex.normSq ρ * Complex.normSq (ρ + 1) *
        Complex.normSq (ρ + 2) * Complex.normSq (ρ + 3) := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  -- ‖·‖² = normSq.
  have h_prod_normSq_ge :
      (1 + ρ.im^2)^4 / 2 ≤ Complex.normSq (ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)) := by
    rw [h_normSq_prod]
    have h_normSq_nn1 : 0 ≤ Complex.normSq ρ := Complex.normSq_nonneg _
    have h_normSq_nn2 : 0 ≤ Complex.normSq (ρ + 1) := Complex.normSq_nonneg _
    have h_normSq_nn3 : 0 ≤ Complex.normSq (ρ + 2) := Complex.normSq_nonneg _
    have h_normSq_nn4 : 0 ≤ Complex.normSq (ρ + 3) := Complex.normSq_nonneg _
    have h_q_nn : 0 ≤ (1 + ρ.im^2) / 2 := by linarith
    have h_q_nn' : 0 ≤ 1 + ρ.im^2 := hQ
    calc (1 + ρ.im^2)^4 / 2
        = ((1 + ρ.im^2) / 2) * ((1 + ρ.im^2) * ((1 + ρ.im^2) * (1 + ρ.im^2))) := by ring
      _ ≤ Complex.normSq ρ *
            ((1 + ρ.im^2) * ((1 + ρ.im^2) * (1 + ρ.im^2))) :=
          mul_le_mul_of_nonneg_right h_ρ_sq'
            (mul_nonneg h_q_nn' (mul_nonneg h_q_nn' h_q_nn'))
      _ ≤ Complex.normSq ρ *
            (Complex.normSq (ρ + 1) * ((1 + ρ.im^2) * (1 + ρ.im^2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h_ρ1_sq
              (mul_nonneg h_q_nn' h_q_nn')) h_normSq_nn1
      _ ≤ Complex.normSq ρ *
            (Complex.normSq (ρ + 1) *
              (Complex.normSq (ρ + 2) * (1 + ρ.im^2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h_ρ2_sq' h_q_nn')
              h_normSq_nn2)
            h_normSq_nn1
      _ ≤ Complex.normSq ρ *
            (Complex.normSq (ρ + 1) *
              (Complex.normSq (ρ + 2) * Complex.normSq (ρ + 3))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_ρ3_sq' h_normSq_nn3)
              h_normSq_nn2)
            h_normSq_nn1
      _ = Complex.normSq ρ * Complex.normSq (ρ + 1) *
            Complex.normSq (ρ + 2) * Complex.normSq (ρ + 3) := by ring
  -- Convert normSq to norm.
  have h_norm_prod_sq : ‖ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)‖^2 =
      Complex.normSq (ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)) :=
    (Complex.normSq_eq_norm_sq _).symm
  have h_quartic_nn : 0 ≤ (1 + ρ.im^2)^4 / 2 := by positivity
  have h_sq_ge : (1 + ρ.im^2)^4 / 2 ≤ ‖ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)‖^2 := by
    rw [h_norm_prod_sq]; exact h_prod_normSq_ge
  -- Extract sqrt.
  have h_norm_nn : 0 ≤ ‖ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)‖ := norm_nonneg _
  -- Want: (1+Im²ρ)²/√2 ≤ ‖·‖. Equivalent: ((1+Im²ρ)²/√2)² ≤ ‖·‖² = normSq.
  have h_lhs_sq_eq : ((1 + ρ.im^2)^2 / Real.sqrt 2)^2 = (1 + ρ.im^2)^4 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have h_sq_chain : ((1 + ρ.im^2)^2 / Real.sqrt 2)^2 ≤
      ‖ρ * (ρ + 1) * (ρ + 2) * (ρ + 3)‖^2 := by
    rw [h_lhs_sq_eq]; exact h_sq_ge
  have h_lhs_nn : 0 ≤ (1 + ρ.im^2)^2 / Real.sqrt 2 := by
    apply div_nonneg
    · positivity
    · exact Real.sqrt_nonneg _
  exact abs_le_of_sq_le_sq' h_sq_chain h_norm_nn |>.2

#print axioms abs_rho_prod_four_ge_quartic

/-- **Non-vanishing of `ρ(ρ+1)(ρ+2)(ρ+3)`** for nontrivial zeros.
Since `Re ρ > 0`, each `ρ+k` (k=0,1,2,3) has `Re(ρ+k) > 0`, hence `≠ 0`. -/
theorem nontrivialZero_prod_four_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) ≠ 0 := by
  rcases hρ with ⟨hRe_pos, _, _⟩
  have h1 : ρ ≠ 0 := fun h => by
    have : ρ.re = 0 := by rw [h]; simp
    linarith
  have h2 : ρ + 1 ≠ 0 := fun h => by
    have hre : (ρ + 1).re = 0 := by rw [h]; simp
    simp at hre; linarith
  have h3 : ρ + 2 ≠ 0 := fun h => by
    have hre : (ρ + 2).re = 0 := by rw [h]; simp
    simp at hre; linarith
  have h4 : ρ + 3 ≠ 0 := fun h => by
    have hre : (ρ + 3).re = 0 := by rw [h]; simp
    simp at hre; linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4

/-- **Quartic Im-decay for `|Im ρ| ≥ 1`.** -/
theorem pairTestMellin_im_quartic_decay_high (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, 1 ≤ |ρ.val.im| →
      ‖pairTestMellin β ρ.val‖ ≤ C / (1 + ρ.val.im^2)^2 := by
  -- Uniform bound on pairDeriv4Mellin on Re s ∈ [4, 5].
  obtain ⟨M, hM_nn, hM⟩ := pairDeriv4Mellin_norm_bound_on_compact_strip β 4 5
    (by norm_num : (0:ℝ) < 4) (by norm_num : (4:ℝ) ≤ 5)
  refine ⟨M * Real.sqrt 2, by positivity, fun ρ h_Im => ?_⟩
  have hρ := ρ.property
  rcases hρ with ⟨hRe_pos, hRe_lt, _⟩
  -- Apply IBP×4 at s = ρ.
  have h_s_re : 0 < ρ.val.re := hRe_pos
  have h_ibp := pairTestMellin_ibp_four_times β h_s_re
  -- ρ+4 has Re ∈ [4, 5].
  have h_re_add : (ρ.val + 4).re = ρ.val.re + 4 := by simp
  have h_bound_M : ‖pairDeriv4Mellin β (ρ.val + 4)‖ ≤ M := by
    apply hM (ρ.val + 4)
    · rw [h_re_add]; linarith
    · rw [h_re_add]; linarith
  -- Product lower bound.
  have h_prod_ge := abs_rho_prod_four_ge_quartic ρ.property h_Im
  have h_prod_ne := nontrivialZero_prod_four_ne_zero ρ.property
  have h_prod_pos : 0 < ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ :=
    norm_pos_iff.mpr h_prod_ne
  have h_quartic_pos : 0 < (1 + ρ.val.im^2)^2 := by positivity
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- Assemble.
  rw [h_ibp, norm_mul, norm_div, norm_one]
  have h_denom_ne : ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3) ≠ 0 := h_prod_ne
  -- 1/‖prod‖ · ‖M4‖ ≤ 1/(1+Im²)²/√2 · M ≤ √2 · M / (1+Im²)² = M · √2 / (1+Im²)².
  have h_inv_le : 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ ≤
      Real.sqrt 2 / (1 + ρ.val.im^2)^2 := by
    rw [div_le_div_iff₀ h_prod_pos h_quartic_pos]
    have := mul_le_mul_of_nonneg_left h_prod_ge (show (0:ℝ) ≤ 1 from by norm_num)
    have h_lhs : (1 : ℝ) * ((1 + ρ.val.im^2)^2) = (1 + ρ.val.im^2)^2 := one_mul _
    have h_rhs_eq : Real.sqrt 2 * ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ ≥
        Real.sqrt 2 * ((1 + ρ.val.im^2)^2 / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left h_prod_ge (Real.sqrt_nonneg _)
    calc (1:ℝ) * (1 + ρ.val.im^2)^2
        = (1 + ρ.val.im^2)^2 := by ring
      _ = Real.sqrt 2 * ((1 + ρ.val.im^2)^2 / Real.sqrt 2) := by
          field_simp
      _ ≤ Real.sqrt 2 * ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ :=
          mul_le_mul_of_nonneg_left h_prod_ge (Real.sqrt_nonneg _)
  calc 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ *
        ‖pairDeriv4Mellin β (ρ.val + 4)‖
      ≤ Real.sqrt 2 / (1 + ρ.val.im^2)^2 * M :=
        mul_le_mul h_inv_le h_bound_M (norm_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) h_quartic_pos.le)
    _ = M * Real.sqrt 2 / (1 + ρ.val.im^2)^2 := by field_simp

#print axioms pairTestMellin_im_quartic_decay_high

end Contour
end WeilPositivity
end ZD

end
