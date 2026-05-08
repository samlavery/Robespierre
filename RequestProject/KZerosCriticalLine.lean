import Mathlib
import RequestProject.OfflineDetectorProof

set_option maxHeartbeats 1600000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

/-! ## Polynomial-root analysis -/

/-- `v⁴ − 2v + 1 = (v−1)·(v³+v²+v−1)` over `ℂ`. -/
private lemma quartic_factor (v : ℂ) :
    v^4 - 2*v + 1 = (v - 1) * (v^3 + v^2 + v - 1) := by ring

/-
Real cubic `h(x) = x³+x²+x−1` is strictly increasing on `ℝ`.
-/
private lemma cubic_strictMono :
    StrictMono (fun x : ℝ => x^3 + x^2 + x - 1) := by
  apply strictMono_of_deriv_pos
  intro x
  have h_deriv : deriv (fun x : ℝ => x^3 + x^2 + x - 1) x = 3 * x^2 + 2 * x + 1 := by
    have h1 : HasDerivAt (fun x : ℝ => x^3 + x^2 + x - 1) (3 * x^2 + 2 * x + 1) x := by
      have h_pow3 : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
        simpa using (hasDerivAt_pow 3 x)
      have h_pow2 : HasDerivAt (fun x : ℝ => x^2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x)
      have h_id : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
      have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
      have h_sum := ((h_pow3.add h_pow2).add h_id).sub h_const
      convert h_sum using 1
      ring
    exact h1.deriv
  rw [h_deriv]
  nlinarith [sq_nonneg (x + 1), sq_nonneg x, sq_nonneg (3*x + 1)]

/-- Real cubic `x³+x²+x−1` has a unique real root in `(0.5, 0.6)`. -/
private lemma cubic_unique_real_root :
    ∃ r : ℝ, r^3 + r^2 + r - 1 = 0 ∧ 0.5 < r ∧ r < 0.6 := by
  have h_05 : (0.5:ℝ)^3 + (0.5:ℝ)^2 + 0.5 - 1 < 0 := by norm_num
  have h_06 : (0.6:ℝ)^3 + (0.6:ℝ)^2 + 0.6 - 1 > 0 := by norm_num
  have hcont : Continuous (fun x : ℝ => x^3 + x^2 + x - 1) := by fun_prop
  obtain ⟨r, hr_mem, hr_zero⟩ :=
    intermediate_value_Ioo (a := (0.5:ℝ)) (b := 0.6) (by norm_num)
      hcont.continuousOn ⟨h_05, h_06⟩
  exact ⟨r, hr_zero, hr_mem.1, hr_mem.2⟩

/-
`‖v(ρ)‖ ≤ exp(1/32)` for `ρ` in the critical strip.
-/
private lemma v_norm_le_strip {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ‖Complex.exp ((ρ - 1/2)^2 / 8)‖ ≤ Real.exp (1/32) := by
      norm_num [ Complex.norm_exp ];
      field_simp;
      norm_num [ sq, Complex.normSq, Complex.div_re ] at *;
      nlinarith [ hρ.1, hρ.2.1 ]

/-
exp(1/16) < 5/3.
-/
private lemma exp_one_sixteenth_lt : Real.exp (1/16 : ℝ) < 5/3 := by
  rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  exact Real.exp_one_lt_d9.trans_le <| by norm_num;

/-
For `(ρ-1/2)² = 8·c + 16π·i·k`, decompose into real/imaginary parts.
-/
private lemma sq_real_imag_decomp {ρ : ℂ} {c : ℝ} {k : ℤ}
    (hsq : (ρ - 1/2)^2 = ((8 * c : ℝ) : ℂ) + ((k : ℂ)) * (16 * Real.pi * I)) :
    (ρ.re - 1/2)^2 - ρ.im^2 = 8 * c ∧
    2 * (ρ.re - 1/2) * ρ.im = 16 * Real.pi * (k : ℝ) := by
      simp_all +decide [ Complex.ext_iff, sq ];
      grind

/-
If `p(r)=0`, then `x³+x²+x-1 = (x-r)(x²+(1+r)x+1/r)`.
-/
private lemma cubic_factor_over_C (r : ℝ) (hr : r^3 + r^2 + r - 1 = 0) (_hr_pos : 0 < r) :
    ∀ x : ℂ, x^3 + x^2 + x - 1 =
      (x - (r : ℂ)) * (x^2 + ((1 + r : ℝ) : ℂ) * x + ((1/r : ℝ) : ℂ)) := by
        intro x; norm_num [ Complex.ext_iff, pow_succ ] ; ring;
        grind

/-
If `v` is a root of `x²+(1+r)x+1/r` with `r ∈ (0.5, 0.6)`,
then `‖v‖² = 1/r`.
-/
private lemma quadratic_root_norm_sq (r : ℝ) (hr_pos : 0 < r) (hr_lo : 0.5 < r)
    (hr_hi : r < 0.6) (v : ℂ)
    (hv : v^2 + ((1 + r : ℝ) : ℂ) * v + ((1/r : ℝ) : ℂ) = 0) :
    ‖v‖^2 = 1/r := by
      norm_num [ Complex.ext_iff, sq ] at *;
      norm_num [ Complex.normSq, Complex.norm_def ];
      rw [ Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ ) ) ];
      by_cases h_im : v.im = 0;
      · nlinarith [ inv_pos.2 hr_pos, mul_inv_cancel₀ hr_pos.ne', sq_nonneg ( v.re + ( 1 + r ) / 2 ) ];
      · grind

/-
If `exp(z) = r` (real, positive) then `z = log(r) + 2πik` for some `k : ℤ`.
-/
private lemma exp_eq_real_pos {z : ℂ} {r : ℝ} (hr_pos : 0 < r)
    (h : Complex.exp z = (r : ℂ)) :
    ∃ k : ℤ, z = ((Real.log r : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * I) := by
      have := Complex.exp_eq_exp_iff_exists_int.mp ( show Complex.exp z = Complex.exp ( Real.log r ) from ?_ );
      · exact this;
      · exact h.trans ( by rw [ ← Complex.ofReal_exp ] ; norm_num [ Real.exp_log hr_pos ] )


/-! ## Main lemma: K-zeros in strip force critical line -/

/-
`K(ρ) = 0 ⟺ v⁴ − 2v + 1 = 0` for `v = exp((ρ−1/2)²/8)`.
-/
private lemma K_eq_zero_iff_quartic (ρ : ℂ) :
    gaussianDefectEntireKernel_local ρ = 0 ↔
      (Complex.exp ((ρ - 1/2)^2 / 8))^4 -
        2 * Complex.exp ((ρ - 1/2)^2 / 8) + 1 = 0 := by
          unfold gaussianDefectEntireKernel_local;
          constructor <;> intro h <;> simp_all +decide [ ← Complex.exp_nat_mul ];
          · convert h.resolve_left ( by positivity ) using 2 ; ring;
          · exact Or.inr ( Eq.trans ( by ring ) h )

/-- **Main lemma**: for `ρ ∈ NontrivialZeros` with `K(ρ) = 0`, `Re ρ = 1/2`. -/
theorem K_zeros_in_strip_force_critical_line {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros)
    (hKzero : gaussianDefectEntireKernel_local ρ = 0) :
    ρ.re = 1/2 := by
  have hρ_mem := hρ
  obtain ⟨h_re_pos, h_re_lt_one, h_zeta_zero⟩ := hρ
  have h_delta_sq_lt : (ρ.re - 1/2)^2 < 1/4 := by nlinarith
  have hv_norm_le : ‖Complex.exp ((ρ - 1/2)^2 / 8)‖ ≤ Real.exp (1/32) :=
    v_norm_le_strip hρ_mem
  have hv_norm_sq_le : ‖Complex.exp ((ρ - 1/2)^2 / 8)‖^2 ≤ Real.exp (1/16) := by
    have h_exp_sq : Real.exp (1/32) ^ 2 = Real.exp (1/16) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    nlinarith [norm_nonneg (Complex.exp ((ρ - 1/2)^2 / 8)), Real.exp_pos (1/32 : ℝ)]
  have h_exp_lt : Real.exp (1/16) < 5/3 := exp_one_sixteenth_lt
  have h_quartic : (Complex.exp ((ρ - 1/2)^2 / 8))^4 -
      2 * Complex.exp ((ρ - 1/2)^2 / 8) + 1 = 0 :=
    (K_eq_zero_iff_quartic ρ).mp hKzero
  set v : ℂ := Complex.exp ((ρ - 1/2)^2 / 8) with hv_def
  have h_factor : (v - 1) * (v^3 + v^2 + v - 1) = 0 := by
    have := quartic_factor v; linear_combination h_quartic - this
  rcases mul_eq_zero.mp h_factor with h_v1 | h_cubic
  · -- Case A: v = 1.
    have hv_eq_one : v = 1 := sub_eq_zero.mp h_v1
    rw [hv_def] at hv_eq_one
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hv_eq_one
    have hsq_form : (ρ - 1/2)^2 = ((8 * 0 : ℝ) : ℂ) + (k : ℂ) * (16 * Real.pi * I) := by
      have : (ρ - 1/2)^2 = 8 * ((k : ℂ) * (2 * ↑Real.pi * I)) := by
        linear_combination 8 * hk
      rw [this]; push_cast; ring
    obtain ⟨h_re_eq, h_im_eq⟩ := sq_real_imag_decomp hsq_form
    -- h_re_eq: δ² - τ² = 0, h_im_eq: 2δτ = 16π·k.
    have h_dsq_eq_tsq : (ρ.re - 1/2)^2 = ρ.im^2 := by linarith
    have h_dt : 2 * (ρ.re - 1/2) * ρ.im = 16 * Real.pi * (k : ℝ) := h_im_eq
    by_cases hk_zero : (k : ℤ) = 0
    · -- k = 0: forces δ = 0, hence Re ρ = 1/2.
      have hk_r : ((k : ℤ) : ℝ) = 0 := by exact_mod_cast hk_zero
      have h_dt_zero : (ρ.re - 1/2) * ρ.im = 0 := by
        have := h_dt; rw [hk_r] at this; nlinarith
      rcases mul_eq_zero.mp h_dt_zero with hδ | hτ
      · linarith
      · -- τ = 0 ⟹ δ² = τ² = 0 ⟹ δ = 0.
        have : (ρ.re - 1/2)^2 = 0 := by rw [h_dsq_eq_tsq, hτ]; ring
        nlinarith [sq_nonneg (ρ.re - 1/2)]
    · -- k ≠ 0: τ² ≥ 8π but τ² = δ² < 1/4 < 8π.
      exfalso
      have hk_sq_ge : (((k : ℤ) : ℝ))^2 ≥ 1 := by
        have : (1 : ℝ) ≤ |((k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hk_zero
        nlinarith [sq_abs ((k : ℤ) : ℝ)]
      -- 4δ²τ² = 256π²k² ≥ 256π², with δ²=τ² gives 4τ⁴ ≥ 256π²
      have h_4t4 : 4 * ρ.im^2 * ρ.im^2 ≥ 256 * Real.pi^2 := by
        have h1 : (2 * (ρ.re - 1/2) * ρ.im)^2 = 4 * (ρ.re - 1/2)^2 * ρ.im^2 := by ring
        have h2 : (2 * (ρ.re - 1/2) * ρ.im)^2 = (16 * Real.pi * (k : ℝ))^2 := by rw [h_dt]
        have h3 : (16 * Real.pi * (k : ℝ))^2 = 256 * Real.pi^2 * ((k : ℤ) : ℝ)^2 := by ring
        rw [h_dsq_eq_tsq] at h1; nlinarith [Real.pi_pos]
      -- τ² ≥ 8π
      have h_tsq_ge : ρ.im^2 ≥ 8 * Real.pi := by
        nlinarith [sq_nonneg (ρ.im^2 - 8 * Real.pi), Real.pi_pos, sq_nonneg ρ.im]
      linarith [h_dsq_eq_tsq, Real.pi_gt_three]
  · -- Case B: v³+v²+v-1 = 0.
    obtain ⟨r, hr_zero, hr_lo, hr_hi⟩ := cubic_unique_real_root
    have hr_pos : 0 < r := by linarith
    have h_cubic_id := cubic_factor_over_C r hr_zero hr_pos
    rw [h_cubic_id v] at h_cubic
    rcases mul_eq_zero.mp h_cubic with h_v_r | h_quadratic
    · -- v = r, real ∈ (0.5, 0.6).
      have hv_eq_r : v = (r : ℂ) := sub_eq_zero.mp h_v_r
      rw [hv_def] at hv_eq_r
      obtain ⟨k, hk⟩ := exp_eq_real_pos hr_pos hv_eq_r
      have hsq_form : (ρ - 1/2)^2 = ((8 * Real.log r : ℝ) : ℂ) +
          (k : ℂ) * (16 * Real.pi * I) := by
        have : (ρ - 1/2)^2 = 8 * (((Real.log r : ℝ) : ℂ) +
            (k : ℂ) * (2 * ↑Real.pi * I)) := by linear_combination 8 * hk
        rw [this]; push_cast; ring
      obtain ⟨h_re_eq, h_im_eq⟩ := sq_real_imag_decomp hsq_form
      have h_log_neg : Real.log r < 0 := Real.log_neg hr_pos (by linarith)
      by_cases hk_zero : (k : ℤ) = 0
      · have hk_r : ((k : ℤ) : ℝ) = 0 := by exact_mod_cast hk_zero
        have h_dt_zero : (ρ.re - 1/2) * ρ.im = 0 := by
          have := h_im_eq; rw [hk_r] at this; nlinarith
        rcases mul_eq_zero.mp h_dt_zero with hδ | hτ
        · linarith
        · exfalso
          have hτ_sq : ρ.im^2 = 0 := by rw [hτ]; ring
          nlinarith [sq_nonneg (ρ.re - 1/2), h_re_eq]
      · exfalso
        have hk_sq_ge : (((k : ℤ) : ℝ))^2 ≥ 1 := by
          have : (1 : ℝ) ≤ |((k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hk_zero
          nlinarith [sq_abs ((k : ℤ) : ℝ)]
        -- |2δτ| = |16πk| ≥ 16π, so 4δ²τ² ≥ 256π²
        have h_4dt : 4 * (ρ.re - 1/2)^2 * ρ.im^2 ≥ 256 * Real.pi^2 := by
          have h1 : (2 * (ρ.re - 1/2) * ρ.im)^2 = 4 * (ρ.re - 1/2)^2 * ρ.im^2 := by ring
          have h2 : (2 * (ρ.re - 1/2) * ρ.im)^2 = (16 * Real.pi * (k : ℝ))^2 := by rw [h_im_eq]
          have h3 : (16 * Real.pi * (k : ℝ))^2 = 256 * Real.pi^2 * ((k : ℤ) : ℝ)^2 := by ring
          nlinarith [Real.pi_pos]
        -- δ² < 1/4, so τ² > 1024π²
        have h_tsq_lb : ρ.im^2 > 256 * Real.pi^2 := by
          by_contra h; push_neg at h; nlinarith [sq_nonneg (ρ.re - 1/2)]
        -- δ² = τ² + 8·log(r). Since log(r) > log(0.5) > -1, δ² > 256π² - 8 ≫ 1/4
        have h_log_lb : Real.log r > -1 := by
          have h1 : Real.log r > Real.log (0.5 : ℝ) := Real.log_lt_log (by norm_num) hr_lo
          have h2 : Real.log (0.5 : ℝ) ≥ -1 := by
            have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 from by norm_num)
            -- log 2 ≤ 1, log(1/2) = -log 2 ≥ -1
            have hlog_half : Real.log (0.5 : ℝ) = -Real.log 2 := by
              rw [show (0.5 : ℝ) = 2⁻¹ from by norm_num, Real.log_inv]
            linarith [hlog_half]
          linarith
        have h_pi_sq_lb : Real.pi^2 > 9 := by nlinarith [Real.pi_gt_three]
        -- δ² - τ² = 8·log(r), δ² = τ² + 8·log(r) > 256π² + 8·log(r) > 256π² - 8
        nlinarith [h_re_eq]
    · -- |v|² = 1/r > 5/3 > exp(1/16), contradiction.
      have hv_norm_sq : ‖v‖^2 = 1/r :=
        quadratic_root_norm_sq r hr_pos hr_lo hr_hi v h_quadratic
      have h_one_div_r_gt : 1/r > 5/3 := by
        linarith [one_div_lt_one_div_of_lt hr_pos hr_hi, show (1:ℝ)/0.6 = 5/3 from by norm_num]
      linarith [hv_norm_sq_le, h_exp_lt]

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end