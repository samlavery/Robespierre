import Mathlib
open scoped BigOperators Real
open Complex Real
set_option maxHeartbeats 800000
namespace TranslationC

/-!
# Harmonic Balance and the Critical Line
We prove that the "harmonic balance" function, which measures the symmetric
deviation of Euler-product harmonics from the critical-line baseline, is
strictly positive for off-line points and vanishes only on the critical line.
## Main results
* `harmonicBalance_pos`: For `r > 1` and `σ ≠ 1/2`, `r^σ + r^(1-σ) > 2·r^(1/2)`.
* `harmonicBalance_eq_zero_iff_half`: `r^σ + r^(1-σ) = 2·r^(1/2)` for some `r > 1`
  iff `σ = 1/2`.
* `offLine_no_harmonic_balance`: No off-line point (i.e., `σ ≠ 1/2` in the critical strip)
  can satisfy the harmonic balance for any Euler base `r > 1`.
The key tool is the strict convexity of `x ↦ r^x` for `r > 1`.
-/
/-! ## Definitions -/
/-- An "off-line" real part: lies in the critical strip but not on the critical line. -/
def OffLineReal (σ : ℝ) : Prop := 0 < σ ∧ σ < 1 ∧ σ ≠ 1 / 2
/-- The harmonic balance function measuring deviation from the critical-line baseline.
    For a point with real part `σ` and its FE-partner `1 - σ`, their combined Euler-harmonic
    contribution at base `r` is `r^σ + r^(1-σ)`, while the critical-line baseline is `2·r^(1/2)`.
    The balance is the difference. -/
noncomputable def harmonicBalance (r : ℝ) (σ : ℝ) : ℝ :=
  r ^ σ + r ^ (1 - σ) - 2 * r ^ (1 / 2 : ℝ)
/-! ## Core convexity lemma -/
/-
**Key lemma**: For `r > 1` and `σ ≠ 1/2`, the harmonic balance is strictly positive.
    This follows from the strict convexity of `x ↦ r^x`:
    `(r^σ + r^(1-σ))/2 > r^((σ + (1-σ))/2) = r^(1/2)`.
-/
theorem harmonicBalance_pos (r σ : ℝ) (hr : 1 < r) (hσ : σ ≠ 1 / 2) :
    0 < harmonicBalance r σ := by
  -- Let $f(x) = r^x$. Since $r > 1$, $f$ is strictly convex.
  set f : ℝ → ℝ := fun x => r^x
  have hf_convex : StrictConvexOn ℝ Set.univ f := by
    apply strictConvexOn_of_deriv2_pos ( convex_univ );
    · exact continuousOn_of_forall_continuousAt fun x _ => ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith;
    · unfold deriv;
      norm_num [ f, Real.rpow_def_of_pos ( zero_lt_one.trans hr ), mul_comm, fderiv_apply_one_eq_deriv ];
      exact fun x => mul_pos ( Real.log_pos hr ) ( mul_pos ( Real.log_pos hr ) ( Real.exp_pos _ ) );
  have := hf_convex.2 ( Set.mem_univ σ ) ( Set.mem_univ ( 1 - σ ) );
  contrapose! this;
  refine' ⟨ _, 1 / 2, 1 / 2, _, _, _, _ ⟩ <;> norm_num;
  · cases lt_or_gt_of_ne hσ <;> linarith;
  · unfold harmonicBalance at this; ring_nf at *; linarith;
/-
The harmonic balance vanishes if and only if the point is on the critical line.
-/
theorem harmonicBalance_eq_zero_iff (r σ : ℝ) (hr : 1 < r) :
    harmonicBalance r σ = 0 ↔ σ = 1 / 2 := by
  constructor <;> intro H <;> unfold harmonicBalance at * <;> norm_num at *;
  · contrapose! H;
    exact ne_of_gt ( harmonicBalance_pos r σ hr H );
  · subst H; ring;
/-! ## Main theorems -/
/-- **Main theorem (real version)**: No off-line point can satisfy the harmonic balance
    equation for any Euler base `r > 1`. This is unconditional (no RH assumption). -/
theorem offLine_no_harmonic_balance (σ : ℝ) (hσ : OffLineReal σ) :
    ∀ r : ℝ, 1 < r → harmonicBalance r σ ≠ 0 := by
  intro r hr heq
  have := harmonicBalance_pos r σ hr hσ.2.2
  linarith
/-
**Strongest form**: The only real number `σ` for which `harmonicBalance r σ = 0`
    for all `r > 1` is `σ = 1/2`.
-/
theorem harmonic_balance_forces_half (σ : ℝ) :
    (∀ r : ℝ, 1 < r → harmonicBalance r σ = 0) ↔ σ = 1 / 2 := by
  constructor;
  · contrapose!;
    exact fun h => ⟨ 2, by norm_num, ne_of_gt ( harmonicBalance_pos 2 σ ( by norm_num ) h ) ⟩;
  · unfold harmonicBalance; norm_num;
    grind
/-! ## Complex extension -/
/-- The complex harmonic residue: for `ρ ∈ ℂ` and base `r > 1`, measures the
    combined Euler-harmonic contribution of `ρ` and its FE-partner `1 - ρ`
    minus the critical-line baseline `2·r^(1/2)`. -/
noncomputable def harmonicResidue (r : ℝ) (ρ : ℂ) : ℂ :=
  (↑r : ℂ) ^ (ρ : ℂ) + (↑r : ℂ) ^ ((1 : ℂ) - ρ) - 2 * (↑r : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
/-
**Complex version**: If the harmonic residue vanishes for all Euler bases `r > 1`,
    then the real part of `ρ` equals `1/2`, i.e., `ρ` lies on the critical line.
    The proof reduces to the real case via the imaginary-part equation:
    `(r^σ - r^(1-σ)) · sin(t·ln r) = 0` for all `r > 1`,
    which (for `σ ≠ 1/2`) forces `sin(t·ln r) = 0` for all `r`,
    and then the real-part equation contradicts `σ ≠ 1/2` by convexity.
-/
theorem harmonicResidue_forces_critical_line (ρ : ℂ)
    (h : ∀ r : ℝ, 1 < r → harmonicResidue r ρ = 0) :
    ρ.re = 1 / 2 := by
  -- By definition of $harmonicResidue$, we know that for all $r > 1$, $(r : ℂ) ^ (ρ : ℂ) + (r : ℂ) ^ ((1 : ℂ) - ρ) = 2 * (r : ℂ) ^ ((1 / 2 : ℝ) : ℂ)$.
  have h_eq : ∀ r : ℝ, 1 < r → (r : ℂ) ^ (ρ : ℂ) + (r : ℂ) ^ ((1 : ℂ) - ρ) = 2 * (r : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    exact fun r hr => eq_of_sub_eq_zero ( h r hr );
  -- For $r > 1$, taking the real part of the harmonic residue equation gives $(r^σ + r^(1-σ)) * cos(t * ln r) = 2 * r^(1/2)$.
  have h_real : ∀ r : ℝ, 1 < r → (r ^ ρ.re + r ^ (1 - ρ.re)) * Real.cos (ρ.im * Real.log r) = 2 * r ^ (1 / 2 : ℝ) := by
    intro r hr; specialize h_eq r hr; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero ( show ( r : ℂ ) ≠ 0 by norm_cast; linarith ) ] at h_eq ⊢;
    norm_num [ Complex.arg_ofReal_of_nonneg ( by positivity : 0 ≤ r ), Real.rpow_def_of_pos ( by positivity : 0 < r ) ] at * ; ring_nf at * ; aesop;
  -- If $\rho.im \neq 0$, then the equation $(r^σ + r^(1-σ)) * cos(t * ln r) = 2 * r^(1/2)$ cannot hold for all $r > 1$.
  by_cases h_im : ρ.im = 0;
  · have := harmonicBalance_eq_zero_iff 2 ρ.re; norm_num at *;
    unfold harmonicBalance at this; specialize h_real 2; norm_num [ h_im ] at h_real; aesop;
  · -- If $\rho.im \neq 0$, then there exists some $r > 1$ such that $\cos(t \ln r) = 0$.
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, 1 < r ∧ Real.cos (ρ.im * Real.log r) = 0 := by
      -- Since $\rho.im \neq 0$, we can choose $r$ such that $\rho.im \ln r = \frac{\pi}{2} + k\pi$ for some integer $k$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 < Real.exp ((Real.pi / 2 + k * Real.pi) / ρ.im) := by
        cases lt_or_gt_of_ne h_im;
        · exact ⟨ -1, by rw [ ← Real.exp_zero ] ; exact Real.exp_lt_exp.mpr ( by rw [ div_eq_mul_inv ] ; nlinarith [ Real.pi_pos, mul_inv_cancel₀ h_im ] ) ⟩;
        · exact ⟨ 1, by norm_num; positivity ⟩;
      exact ⟨ Real.exp ( ( Real.pi / 2 + k * Real.pi ) / ρ.im ), hk, by rw [ Real.log_exp ] ; exact Real.cos_eq_zero_iff.mpr ⟨ k, by rw [ mul_div_cancel₀ _ h_im ] ; ring ⟩ ⟩;
    specialize h_real r hr₁; norm_num [ hr₂ ] at h_real; linarith [ Real.rpow_pos_of_pos ( zero_lt_one.trans hr₁ ) ( 1 / 2 : ℝ ) ] ;
/-
**Strongest complex form**: If the harmonic residue vanishes for all `r > 1`,
    then `ρ = 1/2` exactly (not just `Re(ρ) = 1/2`, but also `Im(ρ) = 0`).
-/
theorem harmonicResidue_forces_half (ρ : ℂ)
    (h : ∀ r : ℝ, 1 < r → harmonicResidue r ρ = 0) :
    ρ = 1 / 2 := by
  -- From `harmonicResidue_forces_critical_line`, we know that `ρ.re = 1 / 2`.
  have h_re : ρ.re = 1 / 2 := by
    exact?;
  simp_all +decide [ Complex.ext_iff, harmonicResidue ];
  -- Using the fact that ρ.re = 1/2, we can simplify the expression for the imaginary part.
  have h_im_simplified : ∀ r : ℝ, 1 < r → (Real.cos (ρ.im * Real.log r) + Real.cos (-ρ.im * Real.log r)) = 2 := by
    intro r hr; specialize h r hr; simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ;
    split_ifs at h <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
    · norm_num;
    · norm_num [ Complex.arg ] at h;
      split_ifs at h <;> simp_all +decide [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log ( zero_lt_one.trans hr ) ];
      · exact mul_left_cancel₀ ( ne_of_gt ( Real.exp_pos ( Real.log r * 2⁻¹ ) ) ) ( by ring_nf at *; linarith );
      · grobner;
  contrapose! h_im_simplified;
  refine' ⟨ Real.exp ( Real.pi / |ρ.im| ), _, _ ⟩ <;> norm_num [ abs_div, abs_mul, Real.exp_pos, h_im_simplified ];
  · positivity;
  · cases abs_cases ρ.im <;> simp +decide [ *, mul_div_cancel₀ ];
    · norm_num;
    · ring_nf; norm_num [ h_im_simplified ];
      norm_num [ mul_assoc, mul_comm Real.pi, h_im_simplified ]



end TranslationC
