import Mathlib

open scoped BigOperators Real
open Complex Real
set_option maxHeartbeats 800000
/-!
# Harmonic Balance as a Cosine-Envelope Residual Detector

## Harmonic interpretation

Consider conjugate exponents `σ + it` and `(1-σ) - it`.  For a real base
`r > 0`, the pair `r^(σ+it)` and `r^((1-σ)-it)` are complex conjugates,
so their **sine components cancel** under addition while the
**cosine channel survives**:

  r^(σ+it) + r^((1-σ)-it) = r^σ · e^{it log r} + r^{1-σ} · e^{-it log r}
                            = (r^σ + r^{1-σ}) cos(t log r)
                              + i (r^σ - r^{1-σ}) sin(t log r).

The imaginary (sine) part vanishes precisely when `σ = 1/2` (since then
`r^σ = r^{1-σ}`).  The real (cosine) part simplifies to
`r^σ + r^{1-σ}`, which equals the critical-line baseline `2 r^{1/2}`
if and only if `σ = 1/2`, by strict convexity of `x ↦ r^x`.

**`HarmonicBalance.balance r σ`** is therefore the *centered
cosine-amplitude defect*: the amount by which the surviving cosine
envelope exceeds the on-line value.  It is **zero on-line** (`σ = 1/2`)
and **strictly positive off-line** (`σ ≠ 1/2`, `r > 1`).

## Spectral / harmonic names

We introduce the following spectral-oriented wrappers:

* `cosineEnvelopeResidual r σ` — synonym for `HarmonicBalance.balance r σ`.
* `harmonicResidualPiThird σ` — synonym for `harmonicDiffPiThird σ`,
  the residual evaluated at the probe frequency `r = π/3`.
* `harmonicResidual_pos` — `σ ≠ 1/2 → harmonicResidualPiThird σ > 0`.
* `harmonicResidual_eq_zero_iff_half` — characterizes the on-line locus.
* `harmonicResidual_eq_balance` — bridge to `HarmonicBalance.balance`.

## Three-witness harmonic detector

The "three synthetic witnesses" `σ₁, σ₂, σ₃` (all off-line) yield
pairwise-distinct, strictly positive harmonic residuals, each different
from the on-line baseline `harmonicResidualPiThird (1/2) = 0`.
This is repackaged as `harmonicDetector_three_witnesses`.

## Single-entry API

* `euler_harmonic_off_line_false`: Given `σ ≠ 1/2`, if every `r > 1`
  satisfies `r ^ σ + r ^ (1 - σ) = 2 * r ^ (1/2)`, the conclusion is
  `False`.  No off-line zero can preserve the Euler-harmonic baseline.

## Supporting results

### Real results
* `rpow_convexity_strict_ineq`
* `rpow_sum_eq_baseline_iff`
* `rpow_sum_eq_baseline_forall_iff`

### Complex results
* `cpow_sum_eq_baseline_forall_imp`

## Internal definitions
* `HarmonicBalance.balance` (= `cosineEnvelopeResidual`)
* `HarmonicBalance.residue`
* `HarmonicBalance.OffLineReal`

The key tool is the strict convexity of `x ↦ r^x` for `r > 1`.
-/

/-! ## Internal definitions and proofs -/
namespace HarmonicBalance

/-- An "off-line" real part: lies in the critical strip but not on the critical line. -/
def OffLineReal (σ : ℝ) : Prop := 0 < σ ∧ σ < 1 ∧ σ ≠ 1 / 2

/-- The harmonic balance function: the centered cosine-amplitude defect.
After conjugate sine cancellation, this is the residual of the surviving
cosine envelope relative to the critical-line baseline `2 r^{1/2}`.
It is zero when `σ = 1/2` and strictly positive for `σ ≠ 1/2`, `r > 1`. -/
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

/-! ## Harmonic / spectral wrappers -/

/-- **Cosine-envelope residual**: synonym for `HarmonicBalance.balance`.
After conjugate-pair sine cancellation, this is the residual of the
surviving cosine amplitude relative to the on-line baseline `2 r^{1/2}`. -/
noncomputable def cosineEnvelopeResidual (r : ℝ) (σ : ℝ) : ℝ :=
  HarmonicBalance.balance r σ

@[simp] theorem cosineEnvelopeResidual_eq_balance (r σ : ℝ) :
    cosineEnvelopeResidual r σ = HarmonicBalance.balance r σ := rfl

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
## ★ h-free API ★
These are the recommended entry points. They state the result directly,
without requiring the caller to supply an `h` hypothesis about the harmonic
balance identity holding.
-/

/-- For `σ ≠ 1/2`, the Euler-harmonic baseline identity **cannot** hold
for all `r > 1`.  This is the negation form of `euler_harmonic_off_line_false`
and does not require the caller to supply `h`. -/
theorem euler_harmonic_off_line_neg_hfree (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ¬ ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) := by
  intro h
  exact absurd ((rpow_sum_eq_baseline_forall_iff σ).mp h) hσ

/-- For `σ ≠ 1/2`, there **exists** an `r > 1` witnessing the failure of the
Euler-harmonic baseline identity.  Concretely `r = 2` works. -/
theorem euler_harmonic_off_line_witness (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ∃ r : ℝ, 1 < r ∧ r ^ σ + r ^ (1 - σ) ≠ 2 * r ^ (1 / 2 : ℝ) :=
  ⟨2, by norm_num, ne_of_gt (rpow_convexity_strict_ineq 2 σ (by norm_num) hσ)⟩

/-- **Complex version, h-free**: If `ρ.re ≠ 1/2`, the complex Euler-harmonic
identity cannot hold for all `r > 1`. -/
theorem cpow_sum_ne_baseline_forall (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    ¬ ∀ r : ℝ, 1 < r →
      (↑r : ℂ) ^ (ρ : ℂ) + (↑r : ℂ) ^ ((1 : ℂ) - ρ) =
        2 * (↑r : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
  intro h
  exact absurd (cpow_sum_eq_baseline_forall_imp ρ h) hρ

/-!
## ★ Single-entry API (legacy) ★
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

/-!
## ★ π/3-witness API — harmonic residual at probe frequency r = π/3 ★

Since `π > 3` we have `π/3 > 1`, so `r = π/3` is a valid probe frequency
for the cosine-envelope residual.  The residual at this frequency serves as
a **harmonic detector** for off-line displacement from `σ = 1/2`.
-/

/-- The harmonic residual (cosine-envelope defect) evaluated at probe
frequency `r = π/3`.  Equivalently, `HarmonicBalance.balance (π/3) σ`.
For `σ = 1/2` this is zero; for `σ ≠ 1/2` it is strictly positive. -/
noncomputable def harmonicDiffPiThird (σ : ℝ) : ℝ :=
  (π / 3) ^ σ + (π / 3) ^ (1 - σ) - 2 * (π / 3) ^ (1 / 2 : ℝ)

/-- `harmonicResidualPiThird` — spectral-oriented name for `harmonicDiffPiThird`. -/
noncomputable def harmonicResidualPiThird (σ : ℝ) : ℝ :=
  harmonicDiffPiThird σ

@[simp] theorem harmonicResidualPiThird_eq (σ : ℝ) :
    harmonicResidualPiThird σ = harmonicDiffPiThird σ := rfl

/-- `π / 3 > 1`. -/
theorem pi_div_three_gt_one : 1 < π / 3 := by
  linarith [pi_gt_three]

/-! ### Bridge: `harmonicDiffPiThird` is a specialization of `balance` -/

/-- The harmonic residual at `r = π/3` equals `HarmonicBalance.balance (π/3) σ`. -/
theorem harmonicResidual_eq_balance (σ : ℝ) :
    harmonicDiffPiThird σ = HarmonicBalance.balance (π / 3) σ := by
  unfold harmonicDiffPiThird HarmonicBalance.balance; ring

/-- The on-line value: the harmonic residual vanishes at `σ = 1/2`. -/
theorem harmonicDiffPiThird_half : harmonicDiffPiThird (1 / 2) = 0 := by
  unfold harmonicDiffPiThird; ring

/-- The harmonic residual at `r = π/3` is strictly positive for `σ ≠ 1/2`. -/
theorem harmonicDiffPiThird_pos (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < harmonicDiffPiThird σ := by
  rw [harmonicResidual_eq_balance]
  exact HarmonicBalance.balance_pos (π / 3) σ pi_div_three_gt_one hσ

/-- `harmonicResidual_pos`: spectral-oriented name. -/
theorem harmonicResidual_pos (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < harmonicResidualPiThird σ := by
  exact harmonicDiffPiThird_pos σ hσ

/-- The harmonic residual at `r = π/3` is zero iff `σ = 1/2`. -/
theorem harmonicResidual_eq_zero_iff_half (σ : ℝ) :
    harmonicDiffPiThird σ = 0 ↔ σ = 1 / 2 := by
  rw [harmonicResidual_eq_balance]
  exact HarmonicBalance.balance_eq_zero_iff (π / 3) σ pi_div_three_gt_one

/-- For `σ ≠ 1/2`, the harmonic residual differs from the on-line baseline. -/
theorem harmonicDiffPiThird_ne_baseline (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    harmonicDiffPiThird σ ≠ harmonicDiffPiThird (1 / 2) := by
  rw [harmonicDiffPiThird_half]
  exact ne_of_gt (harmonicDiffPiThird_pos σ hσ)

/-- For `σ ≠ 1/2`, returns the strictly positive harmonic residual witnessed
at `r = π / 3`. -/
noncomputable def rawComparableHarmonicDiff (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    { d : ℝ // 0 < d ∧ d = harmonicDiffPiThird σ } :=
  ⟨harmonicDiffPiThird σ, harmonicDiffPiThird_pos σ hσ, rfl⟩

/-- For `σ ≠ 1/2`, there exists an `r > 1` witnessing the failure of the
Euler-harmonic baseline identity, with `r = π / 3`. -/
theorem euler_harmonic_off_line_witness_pi_third (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ∃ r : ℝ, 1 < r ∧ r ^ σ + r ^ (1 - σ) ≠ 2 * r ^ (1 / 2 : ℝ) :=
  ⟨π / 3, pi_div_three_gt_one,
   ne_of_gt (rpow_convexity_strict_ineq (π / 3) σ pi_div_three_gt_one hσ)⟩

/-!
## ★ Strict monotonicity of the cosine envelope ★

For `r > 1`, the function `σ ↦ r^σ + r^(1-σ)` is strictly decreasing on
`(-∞, 1/2)` (its derivative is `ln(r)(r^σ - r^{1-σ}) < 0` there) and
symmetric about `σ = 1/2`.  This is used to separate distinct off-line
witnesses on the same side of the critical line.
-/

/-
For `r > 1` and `a < b`, we have `r^a < r^b`.
-/
theorem rpow_lt_rpow_of_lt {r a b : ℝ} (hr : 1 < r) (hab : a < b) :
    r ^ a < r ^ b := by
  exact?

/-
For `r > 1` and `a < b < 1/2`, the cosine envelope is strictly
decreasing: `r^a + r^(1-a) > r^b + r^(1-b)`.
-/
theorem cosineEnvelope_strict_anti {r a b : ℝ} (hr : 1 < r)
    (hab : a < b) (hb : b < 1 / 2) :
    r ^ b + r ^ (1 - b) < r ^ a + r ^ (1 - a) := by
  -- Since $a < b < \frac{1}{2}$, we have $r^a (r^{b-a} - 1) < r^{1-b} (r^{b-a} - 1)$.
  have h_ratio : r ^ a * (r ^ (b - a) - 1) < r ^ (1 - b) * (r ^ (b - a) - 1) := by
    exact mul_lt_mul_of_pos_right ( Real.rpow_lt_rpow_of_exponent_lt hr ( by linarith ) ) ( sub_pos_of_lt ( Real.one_lt_rpow hr ( by linarith ) ) );
  rw [ show r ^ b = r ^ a * r ^ ( b - a ) by rw [ ← Real.rpow_add ( by positivity ) ] ; ring, show r ^ ( 1 - a ) = r ^ ( 1 - b ) * r ^ ( b - a ) by rw [ ← Real.rpow_add ( by positivity ) ] ; ring ] ; linarith

/-
Strict monotonicity of `balance` on `(-∞, 1/2)`: if `a < b < 1/2`
then `balance r a > balance r b > 0`.
-/
theorem balance_strict_anti {r a b : ℝ} (hr : 1 < r)
    (hab : a < b) (hb : b < 1 / 2) :
    HarmonicBalance.balance r b < HarmonicBalance.balance r a := by
  exact sub_lt_sub_right ( cosineEnvelope_strict_anti hr hab hb ) _

/-!
## ★ Three-witness harmonic detector ★

Three synthetic off-line witnesses `σ₁ = 1/5`, `σ₂ = 1/4`, `σ₃ = 1/3`
(all in `(0, 1/2)`) demonstrate that the harmonic residual at `r = π/3`:
1. is strictly positive at each witness (off-line detection),
2. differs from the on-line baseline `harmonicDiffPiThird (1/2) = 0`,
3. produces pairwise-distinct outputs (the detector separates off-line points),
   via strict monotonicity of the cosine envelope on `(-∞, 1/2)`.
-/

/-- The three synthetic off-line witnesses, all in `(0, 1/2)`. -/
noncomputable def threeWitnesses : Fin 3 → ℝ := ![1/5, 1/4, 1/3]

/-- All three witnesses are off-line (`≠ 1/2`). -/
theorem threeWitnesses_ne_half : ∀ i : Fin 3, threeWitnesses i ≠ 1 / 2 := by
  intro i; fin_cases i <;> simp [threeWitnesses]

/-- All three witnesses yield strictly positive harmonic residuals. -/
theorem harmonicDetector_all_pos :
    ∀ i : Fin 3, 0 < harmonicDiffPiThird (threeWitnesses i) :=
  fun i => harmonicDiffPiThird_pos _ (threeWitnesses_ne_half i)

/-- All three witnesses differ from the on-line harmonic baseline. -/
theorem harmonicDetector_ne_baseline :
    ∀ i : Fin 3, harmonicDiffPiThird (threeWitnesses i) ≠ harmonicDiffPiThird (1 / 2) :=
  fun i => harmonicDiffPiThird_ne_baseline _ (threeWitnesses_ne_half i)

/-
The three witness outputs are pairwise distinct, by strict monotonicity
of the cosine envelope on `(0, 1/2)`. Since `1/5 < 1/4 < 1/3 < 1/2`,
the balance values are strictly decreasing.
-/
theorem harmonicDetector_pairwise_distinct :
    ∀ i j : Fin 3, i ≠ j →
      harmonicDiffPiThird (threeWitnesses i) ≠ harmonicDiffPiThird (threeWitnesses j) := by
  intro i j hij;
  fin_cases i <;> fin_cases j <;> simp +decide at hij ⊢;
  all_goals linarith! [ balance_strict_anti ( pi_div_three_gt_one ) ( show 1 / 5 < 1 / 4 by norm_num ) ( by norm_num ), balance_strict_anti ( pi_div_three_gt_one ) ( show 1 / 4 < 1 / 3 by norm_num ) ( by norm_num ) ]

/-- **Three-witness harmonic detector** (combined statement):
the residual is positive at every witness, differs from baseline, and
the three outputs are pairwise distinct. -/
theorem harmonicDetector_three_witnesses :
    (∀ i : Fin 3, 0 < harmonicDiffPiThird (threeWitnesses i)) ∧
    (∀ i : Fin 3, harmonicDiffPiThird (threeWitnesses i) ≠ harmonicDiffPiThird (1 / 2)) ∧
    (∀ i j : Fin 3, i ≠ j →
      harmonicDiffPiThird (threeWitnesses i) ≠ harmonicDiffPiThird (threeWitnesses j)) :=
  ⟨harmonicDetector_all_pos, harmonicDetector_ne_baseline, harmonicDetector_pairwise_distinct⟩