import Mathlib
open scoped BigOperators Real
open Complex Real
set_option maxHeartbeats 800000
/-!
# Harmonic Balance and the Critical Line
We prove that the "harmonic balance" function, which measures the symmetric
deviation of Euler-product harmonics from the critical-line baseline, is
strictly positive for off-line points and vanishes only on the critical line.
## Single-entry API
* `euler_harmonic_off_line_false`: The one theorem you need.
  Given `σ ≠ 1/2`, if every `r > 1` satisfies
  `r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)` (i.e. a zero of the harmonic
  balance lives at `σ`), the conclusion is `False`.
  In other words, **no off-line zero can preserve the Euler-harmonic
  baseline** — calling this with any `σ ≠ 1/2` immediately refutes the
  existence of such a zero.
## Supporting results (used internally, but also exported)
### Real results
* `rpow_convexity_strict_ineq`: For `r > 1` and `σ ≠ 1/2`,
  `r ^ σ + r ^ (1 - σ) > 2 * r ^ (1/2)`.
* `rpow_sum_eq_baseline_iff`: `r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)` iff `σ = 1/2`.
* `rpow_sum_eq_baseline_forall_iff`:
  `(∀ r > 1, r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)) ↔ σ = 1/2`.
### Complex results
* `cpow_sum_eq_baseline_forall_imp`: If `(r : ℂ) ^ ρ + (r : ℂ) ^ (1 - ρ) = 2 * (r : ℂ) ^ (1/2)`
  for all `r > 1`, then `ρ.re = 1/2`.
## Internal definitions
* `HarmonicBalance.balance`: `r ^ σ + r ^ (1 - σ) - 2 * r ^ (1/2)`.
* `HarmonicBalance.residue`: complex analogue.
* `HarmonicBalance.OffLineReal`: `0 < σ ∧ σ < 1 ∧ σ ≠ 1/2`.
The key tool is the strict convexity of `x ↦ r^x` for `r > 1`.
-/
/-! ## Internal definitions and proofs -/
namespace HarmonicBalance
/-- An "off-line" real part: lies in the critical strip but not on the critical line. -/
def OffLineReal (σ : ℝ) : Prop := 0 < σ ∧ σ < 1 ∧ σ ≠ 1 / 2
/-- The harmonic balance function measuring deviation from the critical-line baseline. -/
noncomputable def balance (r : ℝ) (σ : ℝ) : ℝ :=
  r ^ σ + r ^ (1 - σ) - 2 * r ^ (1 / 2 : ℝ)
/-- The complex harmonic residue. -/
noncomputable def residue (r : ℝ) (ρ : ℂ) : ℂ :=
  (↑r : ℂ) ^ (ρ : ℂ) + (↑r : ℂ) ^ ((1 : ℂ) - ρ) - 2 * (↑r : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
theorem balance_pos (r σ : ℝ) (hr : 1 < r) (hσ : σ ≠ 1 / 2) :
    0 < balance r σ := by
  unfold balance;
  rw [ Real.rpow_sub ] <;> norm_num;
  · rw [ ← Real.sqrt_eq_rpow ];
    -- Since $r > 1$ and $\sigma \neq 1/2$, we have $r^\sigma \neq r^{1/2}$.
    have h_neq : r ^ σ ≠ Real.sqrt r := by
      rw [ Real.sqrt_eq_rpow ] ; exact fun h => hσ <| by apply_fun Real.log at h; rw [ Real.log_rpow <| by positivity, Real.log_rpow <| by positivity ] at h; nlinarith [ Real.log_pos hr ] ;
    cases lt_or_gt_of_ne h_neq <;> nlinarith [ Real.sqrt_nonneg r, Real.sq_sqrt ( show 0 ≤ r by positivity ), Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) σ, mul_div_cancel₀ r ( ne_of_gt ( Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) σ ) ) ];
  · positivity
theorem balance_eq_zero_iff (r σ : ℝ) (hr : 1 < r) :
    balance r σ = 0 ↔ σ = 1 / 2 := by
  constructor <;> intro h;
  · exact Classical.not_not.1 fun h' => ne_of_gt ( HarmonicBalance.balance_pos r σ hr h' ) h;
  · unfold balance; norm_num [ h ];
    ring
theorem balance_forces_half (σ : ℝ) :
    (∀ r : ℝ, 1 < r → balance r σ = 0) ↔ σ = 1 / 2 := by
  constructor <;> intro h;
  · exact balance_eq_zero_iff 2 σ ( by norm_num ) |>.1 ( h 2 ( by norm_num ) );
  · unfold balance; norm_num [ h ];
    exact fun r hr => by ring;
theorem residue_forces_critical_line (ρ : ℂ)
    (h : ∀ r : ℝ, 1 < r → residue r ρ = 0) :
    ρ.re = 1 / 2 := by
  by_cases h_abs : ρ.im = 0 <;> simp_all +decide [ Complex.ext_iff ];
  · -- For real ρ, residue r ρ = 0 ⇔ balance r ρ.re = 0. Apply balance_forces_half.
    have h_real : ∀ r : ℝ, 1 < r → (r ^ ρ.re + r ^ (1 - ρ.re) - 2 * r ^ (1 / 2 : ℝ)) = 0 := by
      simp_all +decide [ residue, Complex.cpow_def ];
      intro r hr; specialize h r hr; simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Real.rpow_def_of_pos ( zero_lt_one.trans hr ) ] ;
      split_ifs at h <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      · linarith;
      · erw [ Complex.arg_ofReal_of_nonneg ( by positivity ) ] at h ; aesop;
    exact balance_forces_half _ |>.1 h_real ▸ by norm_num;
  · -- Choose $r = \exp(\pi/(2|\rho.im|))$ so that $\cos(\rho.im \log r) = \cos(\pm\pi/2) = 0$.
    have hr : ∃ r : ℝ, 1 < r ∧ Real.cos (ρ.im * Real.log r) = 0 := by
      refine' ⟨ Real.exp ( Real.pi / ( 2 * |ρ.im| ) ), _, _ ⟩ <;> norm_num [ Real.exp_pos, h_abs ];
      · positivity;
      · cases abs_cases ρ.im <;> simp +decide [ *, mul_div, mul_comm ];
        · exact Real.cos_eq_zero_iff.mpr ⟨ 1 / 2, by ring_nf; norm_num [ mul_assoc, mul_comm, mul_left_comm, h_abs ] ⟩;
        · ring_nf; norm_num [ mul_div, h_abs ];
    obtain ⟨ r, hr₁, hr₂ ⟩ := hr; specialize h r hr₁; simp_all +decide [ residue ] ;
    norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def_of_ne_zero ( by norm_cast; linarith : ( r : ℂ ) ≠ 0 ) ] at *;
    norm_num [ Complex.arg_ofReal_of_nonneg ( by linarith : 0 ≤ r ) ] at *;
    simp_all +decide [ mul_comm ]
end HarmonicBalance
/-! ## Public API -/
/-- For `r > 1` and `σ ≠ 1/2`, the Euler-harmonic sum strictly exceeds
the critical-line baseline: `r ^ σ + r ^ (1 - σ) > 2 * r ^ (1/2)`. -/
theorem rpow_convexity_strict_ineq (r σ : ℝ) (hr : 1 < r) (hσ : σ ≠ 1 / 2) :
    2 * r ^ (1 / 2 : ℝ) < r ^ σ + r ^ (1 - σ) := by
  have := HarmonicBalance.balance_pos r σ hr hσ
  unfold HarmonicBalance.balance at this; linarith
/-- `r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)` for a fixed `r > 1` iff `σ = 1/2`. -/
theorem rpow_sum_eq_baseline_iff (r σ : ℝ) (hr : 1 < r) :
    r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) ↔ σ = 1 / 2 := by
  have h := HarmonicBalance.balance_eq_zero_iff r σ hr
  unfold HarmonicBalance.balance at h
  constructor
  · intro heq; exact h.mp (by linarith)
  · intro heq; have := h.mpr heq; linarith
/-- The Euler-harmonic sum equals the critical-line baseline for *every* `r > 1`
iff `σ = 1/2`. -/
theorem rpow_sum_eq_baseline_forall_iff (σ : ℝ) :
    (∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) ↔ σ = 1 / 2 := by
  have h := HarmonicBalance.balance_forces_half σ
  constructor
  · intro hall
    apply h.mp
    intro r hr
    unfold HarmonicBalance.balance; linarith [hall r hr]
  · intro heq
    intro r hr
    have := (HarmonicBalance.balance_eq_zero_iff r σ hr).mpr heq
    unfold HarmonicBalance.balance at this; linarith
/-- **Complex version**: If the complex Euler-harmonic equation
`(r : ℂ) ^ ρ + (r : ℂ) ^ (1 - ρ) = 2 * (r : ℂ) ^ (1/2)`
holds for all `r > 1`, then `ρ.re = 1/2`. -/
theorem cpow_sum_eq_baseline_forall_imp (ρ : ℂ)
    (h : ∀ r : ℝ, 1 < r →
      (↑r : ℂ) ^ (ρ : ℂ) + (↑r : ℂ) ^ ((1 : ℂ) - ρ) =
        2 * (↑r : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) :
    ρ.re = 1 / 2 := by
  apply HarmonicBalance.residue_forces_critical_line
  intro r hr
  unfold HarmonicBalance.residue
  exact sub_eq_zero.mpr (h r hr)
/-!
## ★ Single-entry API ★
**`euler_harmonic_off_line_false`** is the one theorem you call.
Given any `σ ≠ 1/2`, if the Euler-harmonic identity
`r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)` were to hold for every `r > 1`
(which would be the case if an off-line zero existed that preserved the
harmonic balance), the conclusion is `False`.
### Usage
```lean
example (σ : ℝ) (hσ : σ ≠ 1 / 2)
    (h : ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) :
    False :=
  euler_harmonic_off_line_false σ hσ h
```
-/
/-- **The single API you need.**
If `σ ≠ 1/2`, then there is no way for all `r > 1` to satisfy the
Euler-harmonic baseline identity `r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)`.
Equivalently, no off-line zero (or any zero at `σ ≠ 1/2`) can preserve
the Euler harmonics — calling this with such a `σ` immediately yields `False`. -/
theorem euler_harmonic_off_line_false (σ : ℝ) (hσ : σ ≠ 1 / 2)
    (h : ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) :
    False := by
  have := rpow_convexity_strict_ineq 2 σ (by norm_num) hσ
  linarith [h 2 (by norm_num)]


theorem euler_harmonic_off_line_neg (σ : ℝ) (hσ : σ ≠ 1 / 2)
  (h : ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) :
    False := by
  --intro h
  exact absurd ((rpow_sum_eq_baseline_forall_iff σ).mp h) hσ
