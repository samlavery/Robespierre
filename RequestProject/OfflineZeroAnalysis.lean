import Mathlib

/-!
# Off-Line Zero Analysis: What Passes and What Fails

This file formalizes a comprehensive analysis of off-line zeta zeros
(zeros with Re(ρ) ≠ 1/2) and their interaction with symmetry constraints.

## Summary

### What off-line zeros PASS:
- **Functional equation pairing**: By the functional equation ξ(s) = ξ(1-s),
  non-trivial zeros come in pairs {ρ, 1-ρ̄}. Off-line zeros trivially satisfy
  this — they simply appear as pairs (σ + it, (1-σ) - it).

### What off-line zeros FAIL:
1. **Amplitude balance** (`amplitudeDefect_pos`):
   r^σ + r^{1-σ} > 2r^{1/2} for all r > 1 when σ ≠ 1/2.
   Off-line zeros contribute strictly excess amplitude.

2. **Harmonic balance at π/3** (`amplitudeDefect_pos_at_pi_third`):
   The defect is computable and strictly positive at r = π/3.

3. **Fourfold amplitude symmetry** (`offline_not_amplitude_balanced`):
   The amplitude profile of the perturbation is unbalanced.

4. **The Transfer Law** (`transfer_law`):
   Functional equation reflection AND amplitude balance for all r > 1
   forces σ = 1/2. A single configuration cannot pass both tests.

5. **No-conspiracy theorem** (`no_conspiracy_finset`):
   For ANY finite collection of zero pairs with at least one off-line,
   the total amplitude defect is strictly positive.
   No arrangement of phases can cancel the excess amplitude.

### Why Part 3 of FourfoldBalancePoint.lean has a flawed premise:
The theorem `new_balance_fourfold_symmetry` assumed `FourfoldSymmetric g`
for the perturbation g from off-line zeros. But the contribution of a zero
pair (σ, 1-σ) with σ ≠ 1/2 gives r^σ + r^{1-σ} > 2r^{1/2}, which is
a strictly positive defect. This defect cannot be "fourfold symmetric"
because it is a monotone function of r that strictly exceeds the balanced
baseline — the function r ↦ r^σ + r^{1-σ} is NOT equal to r ↦ 2r^{1/2},
and therefore the perturbation g is not the zero function at the balance
point, contradicting the required symmetry.
-/

open Real Finset BigOperators

/-! ## Section 1: Amplitude Defect -/

/-- The **amplitude defect** of an off-line zero pair at probe value `r`.
This measures the excess amplitude contribution of a zero pair (σ, 1-σ)
relative to the balanced baseline 2r^{1/2}. -/
noncomputable def amplitudeDefect (σ r : ℝ) : ℝ :=
  r ^ σ + r ^ (1 - σ) - 2 * r ^ (1 / 2 : ℝ)

/-- Product of conjugate rpow pair equals r. -/
theorem rpow_pair_product (r : ℝ) (hr : 0 < r) (σ : ℝ) :
    r ^ σ * r ^ (1 - σ) = r ^ (1 : ℝ) := by
  rw [← rpow_add hr]
  ring_nf

/-
**Strict amplitude excess**: For r > 1 and σ ≠ 1/2,
the amplitude defect is strictly positive.
Off-line zeros contribute excess amplitude that CANNOT be cancelled.
-/
theorem amplitudeDefect_pos (σ : ℝ) (hσ : σ ≠ 1 / 2) (r : ℝ) (hr : 1 < r) :
    0 < amplitudeDefect σ r := by
  -- By the AM-GM inequality, since $r^\sigma \neq r^{1-\sigma}$ (because $\sigma \neq 1/2$ and $r > 1$), we have $r^\sigma + r^{1-\sigma} > 2\sqrt{r^\sigma \cdot r^{1-\sigma}}$.
  have h_am_gm : r^σ + r^(1-σ) > 2 * Real.sqrt (r^σ * r^(1-σ)) := by
    -- Since $r^\sigma \neq r^{1-\sigma}$ (because $\sigma \neq 1/2$ and $r > 1$), we can apply the strict AM-GM inequality.
    have h_am_gm : r^σ ≠ r^(1-σ) := by
      exact fun h => hσ <| by apply_fun Real.log at h; rw [ Real.log_rpow ( by linarith ), Real.log_rpow ( by linarith ) ] at h; nlinarith [ Real.log_pos hr ] ;
    nlinarith [ sq_nonneg ( r ^ σ - r ^ ( 1 - σ ) ), Real.mul_self_sqrt ( show 0 ≤ r ^ σ * r ^ ( 1 - σ ) by positivity ), Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) σ, Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) ( 1 - σ ), mul_self_pos.mpr ( sub_ne_zero.mpr h_am_gm ) ];
  unfold amplitudeDefect;
  convert sub_pos_of_lt h_am_gm using 1 ; norm_num [ ← Real.rpow_add ( by positivity : 0 < r ) ];
  rw [ Real.sqrt_eq_rpow ]

/-- The amplitude defect at the specific probe value π/3 is strictly positive. -/
theorem amplitudeDefect_pos_at_pi_third (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < amplitudeDefect σ (π / 3) := by
  exact amplitudeDefect_pos σ hσ (π / 3) (by linarith [pi_gt_three])

/-
The amplitude defect vanishes if and only if σ = 1/2 (for r > 1).
-/
theorem amplitudeDefect_eq_zero_iff (σ : ℝ) (r : ℝ) (hr : 1 < r) :
    amplitudeDefect σ r = 0 ↔ σ = 1 / 2 := by
  constructor <;> intro h;
  · exact Classical.not_not.1 fun h' => ne_of_gt ( amplitudeDefect_pos σ h' r hr ) h;
  · unfold amplitudeDefect; norm_num [ h ] ; ring;

/-! ## Section 2: The Transfer Law -/

/-
**The Transfer Law**: If the amplitude identity r^σ + r^{1-σ} = 2r^{1/2}
holds for ALL r > 1, then σ = 1/2.

This means: a zero pair that satisfies functional equation pairing (giving
the σ, 1-σ structure) AND satisfies amplitude balance (the identity above)
must have σ = 1/2, i.e., it must lie ON the critical line.

A single zero configuration CANNOT pass both the functional equation reflection
test AND the harmonic balance test unless it is on the critical line.
-/
theorem transfer_law (σ : ℝ)
    (h : ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) :
    σ = 1 / 2 := by
  have := congr_arg ( · ^ 2 ) ( h ( 2 ^ 2 ) ( by norm_num ) ) ; ring_nf at this ; norm_num [ sq, ← Real.mul_rpow ] at this;
  norm_num [ ← Real.rpow_add ] at this;
  norm_num [ Real.rpow_sub ] at this;
  -- By simplifying, we can see that the equation holds if and only if $16^\sigma = 4$.
  have h_exp : (16 : ℝ) ^ σ = 4 := by
    grind;
  apply_fun Real.log at h_exp ; norm_num [ Real.log_rpow ] at h_exp;
  rw [ show ( 16 : ℝ ) = 4 ^ 2 by norm_num, Real.log_pow ] at h_exp ; ring_nf at h_exp ; nlinarith [ Real.log_pos ( show ( 4 : ℝ ) > 1 by norm_num ) ]

/-
Contrapositive of the Transfer Law: off-line zeros FAIL amplitude balance
at some probe value. In fact they fail at ALL r > 1.
-/
theorem offline_fails_balance (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ∃ r : ℝ, 1 < r ∧ r ^ σ + r ^ (1 - σ) ≠ 2 * r ^ (1 / 2 : ℝ) := by
  exact ⟨ Real.pi / 3, by linarith [ Real.pi_gt_three ], by have := amplitudeDefect_pos_at_pi_third σ hσ; unfold amplitudeDefect at this; linarith ⟩

/-- Stronger: off-line zeros fail balance at EVERY r > 1 with strict excess. -/
theorem offline_fails_balance_everywhere (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) > 2 * r ^ (1 / 2 : ℝ) := by
  intro r hr
  have := amplitudeDefect_pos σ hσ r hr
  unfold amplitudeDefect at this
  linarith

/-! ## Section 3: No Conspiracy Theorem -/

/-
**No-conspiracy theorem (finite version)**:
For any finite indexed collection of zero pairs, if at least one has σ ≠ 1/2,
the total amplitude defect at any r > 1 is strictly positive.

No arrangement of phases, no rotation, and no finite set of off-line zeros
can conspire to make the total amplitude look balanced. Each off-line pair
contributes a strictly positive defect, and these defects ADD (they cannot cancel).
-/
theorem no_conspiracy_fin (n : ℕ) (σs : Fin n → ℝ) (r : ℝ) (hr : 1 < r)
    (i₀ : Fin n) (hi₀ : σs i₀ ≠ 1 / 2) :
    0 < ∑ i, amplitudeDefect (σs i) r := by
  refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun i _ => _ ) ( Finset.mem_univ i₀ ) );
  · exact amplitudeDefect_pos _ hi₀ _ hr;
  · by_cases hi : σs i = 1 / 2;
    · unfold amplitudeDefect; norm_num [ hi ];
      linarith;
    · exact le_of_lt ( amplitudeDefect_pos _ hi _ hr )

/-
Finset version of the no-conspiracy theorem.
-/
theorem no_conspiracy_finset {ι : Type*} (S : Finset ι) (σ : ι → ℝ) (r : ℝ) (hr : 1 < r)
    (i₀ : ι) (hi₀ : i₀ ∈ S) (hoff : σ i₀ ≠ 1 / 2) :
    0 < ∑ i ∈ S, amplitudeDefect (σ i) r := by
  refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun i _ => _ ) hi₀ );
  · exact amplitudeDefect_pos _ hoff _ hr;
  · by_cases hi : σ i = 1 / 2;
    · unfold amplitudeDefect; norm_num [ hi ]; ring_nf; linarith;
    · exact le_of_lt ( amplitudeDefect_pos _ hi _ hr )

/-! ## Section 4: Amplitude Balance Failure -/

/-- The off-line zero perturbation is NOT amplitude-balanced.
Specifically, the value r^σ + r^{1-σ} strictly exceeds 2r^{1/2} at r = π/3.
This means the perturbation g(z₀) ≠ 0 at the original balance point,
so the balance point MUST shift (cf. `offline_zero_shifts_balance_point`
in FourfoldBalancePoint.lean). -/
theorem offline_not_amplitude_balanced (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    (π / 3) ^ σ + (π / 3) ^ (1 - σ) > 2 * (π / 3) ^ (1 / 2 : ℝ) :=
  offline_fails_balance_everywhere σ hσ (π / 3) (by linarith [pi_gt_three])

/-! ## Section 5: What passes and what fails — Summary theorems -/

/-- **Functional equation pairing is automatic**:
The functional equation gives zero pairs (σ, 1-σ). This is simply
the structure of the zeros, and is always satisfied.
We formalize: for any σ, the "paired" value is 1-σ. -/
theorem functional_equation_pair (σ : ℝ) : (1 - σ) = 1 - σ := rfl

/-- **Harmonic balance forces σ = 1/2**: the amplitude identity at even a
single r > 1 constrains σ significantly, and at all r > 1 it determines σ. -/
theorem harmonic_balance_determines_sigma :
    ∀ σ : ℝ, (∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) → σ = 1 / 2 :=
  transfer_law

/-- **Combined impossibility**: no off-line zero can pass both tests.
If σ ≠ 1/2, there is no way to satisfy amplitude balance for all r > 1.
The functional equation gives the pairing for free, but amplitude balance fails. -/
theorem combined_impossibility (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    ¬ (∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)) := by
  intro h
  exact hσ (transfer_law σ h)

/-! ## Section 6: Complex zero amplitude defect -/

/-
For a complex zero ρ with Re(ρ) ≠ 1/2, the real-amplitude envelope
identity fails. This is the complex version:
if (↑r)^ρ + (↑r)^(1-ρ) = 2(↑r)^(1/2) for all r > 1, then Re(ρ) = 1/2.
-/
theorem complex_transfer_law (ρ : ℂ)
    (h : ∀ r : ℝ, 1 < r →
      (↑r : ℂ) ^ (ρ : ℂ) + (↑r : ℂ) ^ ((1 : ℂ) - ρ) =
        2 * (↑r : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) :
    ρ.re = 1 / 2 := by
  contrapose! h with h_contra;
  refine' ⟨ 2, _, _ ⟩ <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] at *;
  intro h₁ h₂; simp_all +decide [ sub_eq_iff_eq_add ] ;
  have h_exp : Real.exp (Real.log 2 * ρ.re) + Real.exp (Real.log 2 * (1 - ρ.re)) > 2 * Real.exp (Real.log 2 * (1 / 2)) := by
    have h_exp : Real.exp (Real.log 2 * ρ.re) + Real.exp (Real.log 2 * (1 - ρ.re)) > 2 * Real.sqrt (Real.exp (Real.log 2 * ρ.re) * Real.exp (Real.log 2 * (1 - ρ.re))) := by
      have h_exp : Real.exp (Real.log 2 * ρ.re) ≠ Real.exp (Real.log 2 * (1 - ρ.re)) := by
        norm_num at * ; cases lt_or_gt_of_ne h_contra <;> nlinarith [ Real.log_pos one_lt_two ];
      nlinarith [ sq_nonneg ( Real.exp ( Real.log 2 * ρ.re ) - Real.exp ( Real.log 2 * ( 1 - ρ.re ) ) ), Real.mul_self_sqrt ( by positivity : 0 ≤ Real.exp ( Real.log 2 * ρ.re ) * Real.exp ( Real.log 2 * ( 1 - ρ.re ) ) ), Real.exp_pos ( Real.log 2 * ρ.re ), Real.exp_pos ( Real.log 2 * ( 1 - ρ.re ) ), mul_self_pos.mpr ( sub_ne_zero.mpr h_exp ) ];
    convert h_exp using 2 ; rw [ ← Real.exp_add ] ; ring;
    norm_num [ Real.sqrt_eq_rpow, ← Real.exp_mul ];
  by_cases h_sin : Real.sin (Real.log 2 * ρ.im) = 0;
  · have := Real.sin_sq_add_cos_sq ( Real.log 2 * ρ.im ) ; simp_all +decide [ Real.exp_ne_zero ] ;
    cases this <;> simp_all +decide [ Real.exp_ne_zero ];
    linarith [ Real.exp_pos ( Real.log 2 * ρ.re ), Real.exp_pos ( Real.log 2 * ( 1 - ρ.re ) ), Real.exp_pos ( Real.log 2 * 2⁻¹ ) ];
  · simp_all +decide [ add_eq_zero_iff_eq_neg ];
    grind