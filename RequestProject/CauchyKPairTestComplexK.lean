import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.ZetaBound

/-!
# K-zeros in the critical strip force `Re ρ = 1/2`

The strip-root lemma:
```
ρ ∈ NontrivialZeros ∧ gaussianDefectEntireKernel_local ρ = 0 → Re ρ = 1/2.
```

`K(ρ) = 0 ⟺ v⁴ − 2v + 1 = 0` for `v = exp((ρ−1/2)²/8)`.
Factor `v⁴ − 2v + 1 = (v−1)·(v−r)·(v² + (1+r)v + 1/r)`, where `r ∈ (0.5, 0.6)`
is the unique real root of the cubic `v³+v²+v−1 = 0`.

For `ρ ∈ NontrivialZeros`: `0 < Re ρ < 1` gives `(Re ρ−1/2)² < 1/4`;
`riemannZeta_ne_zero_of_im_lt_two` gives `(Im ρ)² ≥ 4`. Hence
`Re((ρ−1/2)²) = (Re ρ−1/2)² − (Im ρ)² ≤ 1/4 − 4 = −15/4`.

Setting `δ := Re ρ − 1/2`, `τ := Im ρ`, `z := (ρ−1/2)²/8`:
- `Re z = (δ²−τ²)/8 ≤ −15/32`, `Im z = δτ/4`.
- `Re v = exp(Re z)·cos(Im z)`, `Im v = exp(Re z)·sin(Im z)`.

Cases on the quartic root:
- `v = 1`: `|v| = 1` ⇒ `exp(Re z) = 1` ⇒ `δ²−τ² = 0`, contradicting `δ²−τ² ≤ −15/4`.
- `v = r` (real): `Im v = 0` ⇒ `sin(Im z) = 0` ⇒ `Im z = πk`. With `Re v = r > 0`,
  `cos(πk) = 1`, so `k = 2m`, `Im z = 2πm`, `δτ = 8πm`.
  - `m = 0`: `δτ = 0`. `τ ≠ 0` (since `|τ| ≥ 2`), so `δ = 0`, i.e., `Re ρ = 1/2`.
  - `m ≠ 0`: `|δτ| ≥ 8π`. From `Re v = r ∈ (0.5, 0.6)`: `exp((δ²−τ²)/8) = r`, so
    `δ²−τ² = 8 ln r`. With `δ² < 1/4` and `τ² = δ² − 8 ln r < 1/4 − 8 ln 0.5`,
    `|τ| < √(1/4 − 8 ln 0.5)`, so `|δτ| < (1/2)·|τ| < small`, contradicting `≥ 8π`.
- `v` solves `v² + (1+r)v + 1/r = 0`: real coefficients, discriminant `(1+r)² − 4/r < 0`
  (for `r ∈ (0.5, 0.6)`), so `v` is non-real and `|v|² = 1/r > 5/3 > 1`.
  But `|v|² = exp(2 Re z) = exp((δ²−τ²)/4)`, with `δ²−τ² ≤ −15/4 < 0`, gives
  `|v|² < 1`, contradiction.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1600000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

/-! ## Polynomial helpers -/

/-- `v⁴ − 2v + 1 = (v−1)·(v³+v²+v−1)` over `ℂ`. -/
private lemma quartic_factor (v : ℂ) :
    v^4 - 2*v + 1 = (v - 1) * (v^3 + v^2 + v - 1) := by ring

/-- The cubic `h(x) = x³+x²+x−1` is strictly increasing on `ℝ`. -/
private lemma cubic_strictMono :
    StrictMono (fun x : ℝ => x^3 + x^2 + x - 1) := by
  have h_pos : ∀ x : ℝ, 0 < 3*x^2 + 2*x + 1 := by
    intro x
    have h_ident : 3*x^2 + 2*x + 1 = 2*x^2 + (x+1)^2 := by ring
    rw [h_ident]
    rcases eq_or_ne x 0 with rfl | hx_ne
    · simp
    · have h1 : 0 < 2*x^2 := by positivity
      have h2 : 0 ≤ (x+1)^2 := sq_nonneg _
      linarith
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x^3 + x^2 + x - 1)
      (3*x^2 + 2*x + 1) x := by
    intro x
    have h := ((hasDerivAt_pow 3 x).add (hasDerivAt_pow 2 x)).add (hasDerivAt_id x)
    convert h.sub_const 1 using 1
    push_cast; ring
  intro a b hab
  have h_strictMonoOn : StrictMonoOn (fun x : ℝ => x^3 + x^2 + x - 1) Set.univ := by
    apply strictMonoOn_of_hasDerivWithinAt_pos
      (convex_univ) (by fun_prop : Continuous _).continuousOn
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x _; exact h_pos x
  exact h_strictMonoOn (Set.mem_univ _) (Set.mem_univ _) hab

/-- The cubic has a unique real root in `(0.5, 0.6)`. -/
private lemma cubic_unique_real_root :
    ∃ r : ℝ, r^3 + r^2 + r - 1 = 0 ∧ 0.5 < r ∧ r < 0.6 := by
  have h_05 : (0.5:ℝ)^3 + (0.5:ℝ)^2 + 0.5 - 1 < 0 := by norm_num
  have h_06 : (0.6:ℝ)^3 + (0.6:ℝ)^2 + 0.6 - 1 > 0 := by norm_num
  have hcont : Continuous (fun x : ℝ => x^3 + x^2 + x - 1) := by fun_prop
  obtain ⟨r, hr_mem, hr_zero⟩ :=
    intermediate_value_Ioo (a := (0.5:ℝ)) (b := 0.6) (by norm_num)
      hcont.continuousOn ⟨h_05, h_06⟩
  exact ⟨r, hr_zero, hr_mem.1, hr_mem.2⟩

/-- `K(ρ) = 0 ⟺ v⁴ − 2v + 1 = 0` for `v = exp((ρ−1/2)²/8)`. -/
private lemma K_eq_zero_iff_quartic (ρ : ℂ) :
    gaussianDefectEntireKernel_local ρ = 0 ↔
      (Complex.exp ((ρ - 1/2)^2 / 8))^4 -
        2 * Complex.exp ((ρ - 1/2)^2 / 8) + 1 = 0 := by
  unfold gaussianDefectEntireKernel_local
  set v : ℂ := Complex.exp ((ρ - 1/2)^2 / 8)
  have hv_pow : Complex.exp ((ρ - 1/2)^2 / 2) = v^4 := by
    have h1 : ((ρ - 1/2)^2 / 2 : ℂ) = ((4 : ℕ) : ℂ) * ((ρ - 1/2)^2 / 8) := by
      push_cast; ring
    rw [h1, Complex.exp_nat_mul]
  rw [hv_pow]
  have hCprefac_ne : ((Real.pi * Real.sqrt (Real.pi / 2) : ℝ) : ℂ) ≠ 0 := by
    have hreal_pos : 0 < Real.pi * Real.sqrt (Real.pi / 2) :=
      mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by positivity))
    exact_mod_cast ne_of_gt hreal_pos
  constructor
  · intro h
    have hfac : ((Real.pi * Real.sqrt (Real.pi / 2) : ℝ) : ℂ) *
        (v^4 - 2*v + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd h1 hCprefac_ne
    · exact h1
  · intro h
    have : ((Real.pi * Real.sqrt (Real.pi / 2) : ℝ) : ℂ) *
        (v^4 - 2*v + 1) = 0 := by rw [h]; ring
    linear_combination this

/-- Re/Im of `(ρ - 1/2)²`. -/
private lemma sq_re_im (ρ : ℂ) :
    ((ρ - 1/2)^2).re = (ρ.re - 1/2)^2 - ρ.im^2 ∧
    ((ρ - 1/2)^2).im = 2 * (ρ.re - 1/2) * ρ.im := by
  have h_sub_re : (ρ - 1/2).re = ρ.re - 1/2 := by simp
  have h_sub_im : (ρ - 1/2).im = ρ.im := by simp
  refine ⟨?_, ?_⟩
  · rw [sq, Complex.mul_re, h_sub_re, h_sub_im]; ring
  · rw [sq, Complex.mul_im, h_sub_re, h_sub_im]; ring

/-- Re/Im of `(ρ - 1/2)² / 8`. -/
private lemma sq_div_re_im (ρ : ℂ) :
    ((ρ - 1/2)^2 / 8).re = ((ρ.re - 1/2)^2 - ρ.im^2) / 8 ∧
    ((ρ - 1/2)^2 / 8).im = (ρ.re - 1/2) * ρ.im / 4 := by
  obtain ⟨h_re, h_im⟩ := sq_re_im ρ
  have h_eight_re : ((8 : ℂ)).re = 8 := by simp
  have h_eight_im : ((8 : ℂ)).im = 0 := by simp
  have h_nsq : Complex.normSq (8 : ℂ) = 64 := by
    rw [Complex.normSq_apply, h_eight_re, h_eight_im]; ring
  have h_div_re : ((ρ - 1/2)^2 / 8).re = ((ρ - 1/2)^2).re / 8 := by
    rw [Complex.div_re, h_eight_re, h_eight_im, h_nsq]; ring
  have h_div_im : ((ρ - 1/2)^2 / 8).im = ((ρ - 1/2)^2).im / 8 := by
    rw [Complex.div_im, h_eight_re, h_eight_im, h_nsq]; ring
  refine ⟨?_, ?_⟩
  · rw [h_div_re, h_re]
  · rw [h_div_im, h_im]; ring

/-- Norm-squared of `v = exp(z)` is `exp(2 Re z)`. -/
private lemma norm_sq_exp (z : ℂ) :
    ‖Complex.exp z‖^2 = Real.exp (2 * z.re) := by
  rw [Complex.norm_exp]
  rw [show (Real.exp z.re)^2 = Real.exp (2 * z.re) from by
    rw [show (2 : ℝ) * z.re = z.re + z.re from by ring, Real.exp_add]
    ring]

/-- For `v² + bv + c = 0` with `b, c : ℝ`, `b² < 4c`, then `‖v‖² = c`. -/
private lemma quadratic_complex_norm_sq {b c : ℝ} {v : ℂ}
    (hv : v^2 + (b:ℂ) * v + (c:ℂ) = 0) (hdisc : b^2 < 4*c) :
    ‖v‖^2 = c := by
  -- Real and imaginary parts of the equation.
  have hRe_eq : v.re^2 - v.im^2 + b * v.re + c = 0 := by
    have h := congr_arg Complex.re hv
    have h_sq_re : (v^2).re = v.re^2 - v.im^2 := by
      rw [sq, Complex.mul_re]; ring
    have h_bv_re : ((b:ℂ) * v).re = b * v.re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    simp [Complex.add_re, h_sq_re, h_bv_re, Complex.ofReal_re] at h
    linarith
  have hIm_eq : 2 * v.re * v.im + b * v.im = 0 := by
    have h := congr_arg Complex.im hv
    have h_sq_im : (v^2).im = 2 * v.re * v.im := by
      rw [sq, Complex.mul_im]; ring
    have h_bv_im : ((b:ℂ) * v).im = b * v.im := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    simp [Complex.add_im, h_sq_im, h_bv_im, Complex.ofReal_im] at h
    linarith
  -- Imaginary equation factors: v.im * (2 v.re + b) = 0.
  have hIm_factor : v.im * (2 * v.re + b) = 0 := by linarith
  -- Discriminant negative ⟹ v.im ≠ 0 (else real solution would force disc ≥ 0).
  have h_im_ne : v.im ≠ 0 := by
    intro h_im_zero
    have h_real : v.re^2 + b * v.re + c = 0 := by
      rw [h_im_zero] at hRe_eq; nlinarith
    have h_disc : 0 ≤ b^2 - 4*c := by
      have : (2*v.re + b)^2 = b^2 - 4*c := by nlinarith [h_real]
      nlinarith [sq_nonneg (2*v.re + b), this]
    linarith
  -- So 2 v.re + b = 0.
  have h_2re_b : 2 * v.re + b = 0 := by
    rcases mul_eq_zero.mp hIm_factor with h | h
    · exact absurd h h_im_ne
    · exact h
  have h_re_eq : v.re = -b/2 := by linarith
  -- From real equation: v.im² = c - b²/4.
  have h_im_sq : v.im^2 = c - b^2/4 := by
    have := hRe_eq; rw [h_re_eq] at this; nlinarith
  -- ‖v‖² = v.re² + v.im² = b²/4 + c - b²/4 = c.
  have h_norm_sq : ‖v‖^2 = v.re^2 + v.im^2 := by
    have h := Complex.sq_norm_sub_sq_re v
    linarith
  rw [h_norm_sq, h_re_eq, h_im_sq]
  ring

/-! ## Main lemma -/

/-- **Strip-root lemma**: for `ρ ∈ NontrivialZeros` with `K(ρ) = 0`, `Re ρ = 1/2`. -/
theorem K_zeros_in_strip_force_critical_line {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros)
    (hKzero : gaussianDefectEntireKernel_local ρ = 0) :
    ρ.re = 1/2 := by
  obtain ⟨h_re_pos, h_re_lt_one, h_zeta_zero⟩ := hρ
  -- |Im ρ| ≥ 2 from project's `riemannZeta_ne_zero_of_im_lt_two`.
  have h_im_ge_two : 2 ≤ |ρ.im| := by
    by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_im_lt_two h_re_pos h_re_lt_one h h_zeta_zero
  -- δ := Re ρ - 1/2, |δ| < 1/2, δ² < 1/4.
  have h_delta_sq_lt : (ρ.re - 1/2)^2 < 1/4 := by
    have h_lo : -1/2 < ρ.re - 1/2 := by linarith
    have h_hi : ρ.re - 1/2 < 1/2 := by linarith
    nlinarith [sq_nonneg (ρ.re - 1/2)]
  -- τ² ≥ 4.
  have h_tau_sq_ge : 4 ≤ ρ.im^2 := by
    have := sq_abs ρ.im
    nlinarith [h_im_ge_two, abs_nonneg ρ.im, sq_abs ρ.im]
  -- δ² - τ² ≤ -15/4.
  have h_delta_sub_tau_sq : (ρ.re - 1/2)^2 - ρ.im^2 ≤ -15/4 := by linarith
  -- Strict version: δ² - τ² < 0.
  have h_delta_sub_tau_sq_neg : (ρ.re - 1/2)^2 - ρ.im^2 < 0 := by linarith
  -- Convert K = 0 to quartic.
  have h_quartic : (Complex.exp ((ρ - 1/2)^2 / 8))^4 -
      2 * Complex.exp ((ρ - 1/2)^2 / 8) + 1 = 0 :=
    (K_eq_zero_iff_quartic ρ).mp hKzero
  set v : ℂ := Complex.exp ((ρ - 1/2)^2 / 8) with hv_def
  set z : ℂ := (ρ - 1/2)^2 / 8 with hz_def
  have hv_eq : v = Complex.exp z := rfl
  -- Re/Im of z.
  have ⟨h_z_re, h_z_im⟩ := sq_div_re_im ρ
  -- Re v = exp(Re z) cos(Im z), Im v = exp(Re z) sin(Im z).
  have hv_re : v.re = Real.exp z.re * Real.cos z.im := by
    rw [hv_eq, Complex.exp_re]
  have hv_im : v.im = Real.exp z.re * Real.sin z.im := by
    rw [hv_eq, Complex.exp_im]
  -- |v|² = exp(2 Re z).
  have hv_norm_sq : ‖v‖^2 = Real.exp (2 * z.re) := norm_sq_exp z
  -- Re z = (δ²-τ²)/8 < 0, so |v|² = exp(2 Re z) < 1.
  have h_z_re_neg : z.re < 0 := by rw [h_z_re]; linarith
  have h_2z_re_neg : 2 * z.re < 0 := by linarith
  have hv_norm_sq_lt_one : ‖v‖^2 < 1 := by
    rw [hv_norm_sq]
    have := Real.exp_lt_one_iff.mpr h_2z_re_neg
    linarith
  -- Strict bound: |v|² ≤ exp(-15/16).
  have h_2z_re_le : 2 * z.re ≤ -15/16 := by rw [h_z_re]; linarith
  have hv_norm_sq_le : ‖v‖^2 ≤ Real.exp (-15/16) := by
    rw [hv_norm_sq]; exact Real.exp_le_exp.mpr h_2z_re_le
  -- Factor quartic.
  have h_factor1 : (v - 1) * (v^3 + v^2 + v - 1) = 0 := by
    have h_id : v^4 - 2*v + 1 = (v - 1) * (v^3 + v^2 + v - 1) := quartic_factor v
    linear_combination h_quartic - h_id
  rcases mul_eq_zero.mp h_factor1 with h_v1 | h_cubic
  · -- Case A: v = 1. Then |v|² = 1, contradicting |v|² < 1.
    exfalso
    have hv_eq_one : v = 1 := sub_eq_zero.mp h_v1
    have h_norm_one : ‖v‖^2 = 1 := by
      rw [hv_eq_one]; simp
    linarith [hv_norm_sq_lt_one, h_norm_one]
  · -- Case B: v³+v²+v-1 = 0. Use cubic_factor.
    obtain ⟨r, hr_zero, hr_lo, hr_hi⟩ := cubic_unique_real_root
    have hr_pos : 0 < r := by linarith
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hrC_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_ne
    -- Cubic factors: v³+v²+v-1 = (v - r)(v² + (1+r)v + 1/r).
    have h_cubic_factor : (v - (r:ℂ)) *
        (v^2 + ((1+r:ℝ):ℂ) * v + ((1/r:ℝ):ℂ)) = v^3 + v^2 + v - 1 := by
      have h_one_div_r : ((1/r:ℝ):ℂ) = 1 / (r:ℂ) := by push_cast; ring
      have h_one_plus_r : ((1+r:ℝ):ℂ) = 1 + (r:ℂ) := by push_cast; ring
      rw [h_one_div_r, h_one_plus_r]
      have hcubic_C : (r:ℂ)^3 + (r:ℂ)^2 + (r:ℂ) = 1 := by
        have : ((r^3 + r^2 + r - 1 : ℝ):ℂ) = 0 := by exact_mod_cast hr_zero
        push_cast at this; linear_combination this
      have hr_inv : (r:ℂ) * (1 / (r:ℂ)) = 1 := mul_one_div_cancel hrC_ne
      have key : (r:ℂ) * ((v - (r:ℂ)) * (v^2 + (1 + (r:ℂ)) * v + 1 / (r:ℂ))) =
                 (r:ℂ) * (v^3 + v^2 + v - 1) := by
        have rewrite_key :
            (r:ℂ) * ((v - (r:ℂ)) * (v^2 + (1 + (r:ℂ)) * v + 1 / (r:ℂ))) =
            (v - (r:ℂ)) * ((r:ℂ) * v^2 + (r:ℂ) * (1 + (r:ℂ)) * v +
              ((r:ℂ) * (1 / (r:ℂ)))) := by ring
        rw [rewrite_key, hr_inv]
        linear_combination -v * hcubic_C
      exact mul_left_cancel₀ hrC_ne key
    rw [← h_cubic_factor] at h_cubic
    rcases mul_eq_zero.mp h_cubic with h_vr | h_quad
    · -- Case B1: v = r (real, in (0.5, 0.6)).
      have hv_eq_r : v = (r:ℂ) := sub_eq_zero.mp h_vr
      -- Im v = 0 (since r is real ⟹ (r:ℂ).im = 0).
      have hv_im_zero : v.im = 0 := by
        rw [hv_eq_r]; simp
      have hv_re_eq : v.re = r := by
        rw [hv_eq_r]; simp
      -- From hv_im: exp(Re z) * sin(Im z) = 0. exp > 0, so sin(Im z) = 0.
      have h_exp_re_pos : 0 < Real.exp z.re := Real.exp_pos _
      have h_sin_zero : Real.sin z.im = 0 := by
        have heq : Real.exp z.re * Real.sin z.im = 0 := by rw [← hv_im, hv_im_zero]
        rcases mul_eq_zero.mp heq with h | h
        · linarith
        · exact h
      -- Re v = r > 0 ⟹ exp(Re z) * cos(Im z) > 0. exp > 0, so cos(Im z) > 0.
      have h_cos_pos : 0 < Real.cos z.im := by
        have h_re_pos_v : 0 < v.re := by rw [hv_re_eq]; exact hr_pos
        rw [hv_re] at h_re_pos_v
        rcases lt_or_ge 0 (Real.cos z.im) with h | h
        · exact h
        · exfalso
          have h_nonpos : Real.exp z.re * Real.cos z.im ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_exp_re_pos) h
          linarith
      -- sin = 0 and cos > 0 ⟹ cos = 1 (from sin² + cos² = 1).
      have h_cos_eq_one : Real.cos z.im = 1 := by
        have h_sq : Real.cos z.im ^ 2 = 1 := by
          have hsc := Real.sin_sq_add_cos_sq z.im
          rw [h_sin_zero] at hsc
          nlinarith
        have h_factor : (Real.cos z.im - 1) * (Real.cos z.im + 1) = 0 := by
          have h_diff : Real.cos z.im^2 - 1 = (Real.cos z.im - 1) * (Real.cos z.im + 1) := by
            ring
          linarith [h_sq, h_diff]
        rcases mul_eq_zero.mp h_factor with h | h
        · linarith
        · linarith
      -- z.im = 2πn for some n : ℤ.
      obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff z.im).mp h_cos_eq_one
      -- hm : (m : ℝ) * (2 * Real.pi) = z.im
      have h_im_z : z.im = 2 * Real.pi * m := by linarith [hm]
      -- Translate Im z = 2πm into δτ = 8πm.
      have h_delta_tau : (ρ.re - 1/2) * ρ.im = 8 * Real.pi * m := by
        have := h_z_im
        rw [h_im_z] at this
        linarith
      -- Re v = r ⟹ exp(Re z) = r.
      have h_exp_re_eq_r : Real.exp z.re = r := by
        have := hv_re
        rw [hv_re_eq, h_cos_eq_one] at this
        linarith
      -- Re z = ln r.
      have h_z_re_eq : z.re = Real.log r := by
        rw [← Real.log_exp z.re, h_exp_re_eq_r]
      -- (δ²-τ²)/8 = ln r.
      have h_delta_minus_tau_sq : (ρ.re - 1/2)^2 - ρ.im^2 = 8 * Real.log r := by
        have := h_z_re; rw [h_z_re_eq] at this; linarith
      -- Two sub-cases: m = 0 or m ≠ 0.
      by_cases hm_zero : m = 0
      · -- m = 0: δτ = 0. τ ≠ 0 (since τ² ≥ 4 > 0). So δ = 0.
        have h_delta_tau_zero : (ρ.re - 1/2) * ρ.im = 0 := by
          rw [h_delta_tau]; rw [hm_zero]; push_cast; ring
        have h_tau_ne : ρ.im ≠ 0 := by
          intro h
          rw [h] at h_tau_sq_ge; norm_num at h_tau_sq_ge
        rcases mul_eq_zero.mp h_delta_tau_zero with h | h
        · linarith
        · exact absurd h h_tau_ne
      · -- m ≠ 0: |δτ| ≥ 8π. From δ² - τ² = 8 ln r, τ² = δ² - 8 ln r,
        -- with δ² < 1/4 and ln r ∈ (ln 0.5, ln 0.6), τ² < 1/4 + 8|ln 0.5| ≈ 5.8.
        -- So |τ| < √6, |δτ| < (1/2)√6 < 1.225 < 8π ≈ 25.13. Contradiction.
        exfalso
        -- ln r is bounded above by ln 0.6 < 0 and below by ln 0.5.
        -- So 8 ln r ∈ (-8 ln 2, 8 ln(0.6)). |8 ln r| ≤ 8 ln 2 ≈ 5.545.
        -- Thus τ² = δ² + |8 ln r| ≤ 1/4 + 8 ln 2.
        have h_log_r_neg : Real.log r < 0 := Real.log_neg hr_pos (by linarith)
        have h_log_r_lb : -Real.log 2 ≤ Real.log r := by
          have h1 : Real.log (1/2) ≤ Real.log r :=
            Real.log_le_log (by norm_num) (by linarith)
          rw [Real.log_div (by norm_num) (by norm_num)] at h1
          rw [Real.log_one] at h1
          linarith
        -- τ² = δ² - 8 ln r. Since ln r < 0, -8 ln r > 0.
        -- |τ|² = δ² + 8|ln r| ≤ 1/4 + 8 ln 2 ≈ 5.8.
        -- |δτ|² = δ²·τ² ≤ (1/4)(1/4 + 8 ln 2) = 1/16 + 2 ln 2 ≈ 1.45.
        -- |8πm|² ≥ 64π² ≈ 631. Contradiction.
        have h_tau_sq_eq : ρ.im^2 = (ρ.re - 1/2)^2 - 8 * Real.log r := by linarith
        have h_tau_sq_ub : ρ.im^2 < 1/4 + 8 * Real.log 2 := by
          rw [h_tau_sq_eq]
          have : -8 * Real.log r ≤ 8 * Real.log 2 := by linarith
          linarith
        -- Now use h_delta_tau: (δτ) = 8πm with m ≠ 0, so |δτ|² ≥ 64π².
        have hm_ne_R : (m : ℝ) ≠ 0 := by exact_mod_cast hm_zero
        have hm_sq_ge_one : 1 ≤ (m:ℝ)^2 := by
          have h1 : 1 ≤ |(m:ℝ)| := by
            have h := Int.one_le_abs hm_zero
            have h2 : (1:ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h
            simp at h2; exact h2
          nlinarith [sq_abs (m:ℝ), h1]
        have h_delta_tau_sq : ((ρ.re - 1/2) * ρ.im)^2 = 64 * Real.pi^2 * (m:ℝ)^2 := by
          have := h_delta_tau
          have hsq : ((ρ.re - 1/2) * ρ.im)^2 = (8 * Real.pi * (m:ℝ))^2 := by
            rw [this]
          rw [hsq]; ring
        have h_delta_tau_sq_ge : ((ρ.re - 1/2) * ρ.im)^2 ≥ 64 * Real.pi^2 := by
          rw [h_delta_tau_sq]
          have h_pi_sq_pos : 0 ≤ 64 * Real.pi^2 := by positivity
          nlinarith [hm_sq_ge_one, sq_nonneg Real.pi, Real.pi_pos]
        -- (δτ)² = δ²τ² ≤ (1/4)(1/4 + 8 ln 2) = 1/16 + 2 ln 2.
        have h_delta_tau_sq_ub : ((ρ.re - 1/2) * ρ.im)^2 < 1/16 + 2 * Real.log 2 := by
          have h_dt_sq : ((ρ.re - 1/2) * ρ.im)^2 = (ρ.re - 1/2)^2 * ρ.im^2 := by ring
          rw [h_dt_sq]
          have h_delta_sq_nn : 0 ≤ (ρ.re - 1/2)^2 := sq_nonneg _
          have h_tau_sq_pos : 0 < ρ.im^2 := by linarith
          calc (ρ.re - 1/2)^2 * ρ.im^2
              ≤ (1/4) * ρ.im^2 := by nlinarith
            _ < (1/4) * (1/4 + 8 * Real.log 2) := by nlinarith
            _ = 1/16 + 2 * Real.log 2 := by ring
        -- Now 64 π² > 1/16 + 2 ln 2.  π > 3, so π² > 9, 64π² > 576. ln 2 < 1, so 1/16 + 2 ln 2 < 3.
        have h_pi_gt : Real.pi > 3 := Real.pi_gt_three
        have h_log_2_lt : Real.log 2 < 1 := by
          have h_e_gt : (2 : ℝ) < Real.exp 1 := by
            have := Real.exp_one_gt_d9
            linarith
          have h1 : Real.log 2 < Real.log (Real.exp 1) :=
            Real.log_lt_log (by norm_num) h_e_gt
          rw [Real.log_exp] at h1; exact h1
        have h_lhs : 64 * Real.pi^2 > 1/16 + 2 * Real.log 2 := by nlinarith
        linarith
    · -- Case B2: v² + (1+r)v + 1/r = 0 with discriminant negative.
      exfalso
      -- Discriminant: (1+r)² - 4/r < 0 for r ∈ (0.5, 0.6).
      -- (1+r)² < (1.6)² = 2.56 and 4/r > 4/0.6 ≈ 6.67. Use nlinarith on r·((1+r)² - 4/r) < 0.
      have h_disc : (1+r)^2 < 4 * (1/r) := by
        have hr_inv_pos : 0 < 1/r := by positivity
        -- r * ((1+r)² * r - 4) < 0 since for r ∈ (0.5, 0.6), (1+r)²·r < (1.6)²·0.6 = 1.536 < 4.
        have h_key : (1+r)^2 * r < 4 := by nlinarith [sq_nonneg (1+r), hr_lo, hr_hi]
        have : (1+r)^2 < 4/r := by
          rw [lt_div_iff₀ hr_pos]; linarith
        rw [show (4:ℝ) * (1/r) = 4/r from by ring]
        exact this
      have hv_norm_sq_eq_inv_r : ‖v‖^2 = 1/r :=
        quadratic_complex_norm_sq h_quad h_disc
      -- 1/r > 5/3 > 1.
      have h_inv_r_gt_one : 1/r > 1 := by
        rw [gt_iff_lt, lt_div_iff₀ hr_pos]; linarith
      linarith [hv_norm_sq_lt_one, hv_norm_sq_eq_inv_r, h_inv_r_gt_one]

#print axioms K_zeros_in_strip_force_critical_line

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
