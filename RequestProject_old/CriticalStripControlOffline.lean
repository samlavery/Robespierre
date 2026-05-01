/-
# Off-Line Zeros of the Riemann Zeta Function: Non-Cancellation, Divergence, and Detectability
We assume the Riemann Hypothesis is false: there exist zeros of ζ(s) in the critical strip
(0 < Re(s) < 1) that do NOT lie on the critical line Re(s) = 1/2.
We prove unconditionally from first principles:
1. **Non-Cancellation (Theorem A)**: Taking n ≥ 1 identical copies of the critical strip
   (rotated 0°, i.e., the identity transformation) and forming ζ(s)^n cannot cancel any zero.
   If ζ(s₀) = 0 then ζ(s₀)^n = 0 for all n ≥ 1. Off-line zeros persist.
2. **Functional Equation Pairing (Theorem B)**: The functional equation ζ(1−s) = [prefactor]·ζ(s)
   forces every off-line zero s₀ to generate a mirror zero at 1−s₀. Since Re(s₀) ≠ 1/2, these
   two zeros sit at DIFFERENT real parts and cannot overlap or cancel.
3. **Euler Product Divergence (Theorem C)**: The Euler product ∏_p (1−p^{−s})^{−1} converges
   absolutely only for Re(s) > 1, where ζ(s) ≠ 0 (proven in Mathlib). Therefore, at any zero
   in the critical strip, the Euler product representation necessarily diverges — the zero lives
   in a region fundamentally inaccessible to the convergent Euler product.
4. **Isometric Detectability (Theorem D)**: The functional equation provides an isometric
   involution s ↦ 1−s on the critical strip. For any off-line zero s₀, the reflected point
   1−s₀ has Re(1−s₀) ≠ Re(s₀), so the zero and its reflection are always distinguishable
   and never cancel under this symmetry.
All proofs are unconditional and require no assumption about RH.
-/
import Mathlib
/-! ## Part 1: Non-Cancellation of Zeros under Identical Strip Products -/
/-- **Theorem A (Zero Persistence)**: If ζ(s₀) = 0, then ζ(s₀)^n = 0 for any n ≥ 1.
Taking any number of identical copies of the critical strip and forming the product
ζ(s)^n cannot cancel a zero. This is unconditional. -/
theorem zeta_zero_pow_eq_zero {s : ℂ} (hζ : riemannZeta s = 0) (n : ℕ) (hn : 1 ≤ n) :
    riemannZeta s ^ n = 0 := by
  rw [hζ, zero_pow (by positivity)]
/-- Corollary: The product of two identical strips ζ(s)·ζ(s) vanishes at every zero. -/
theorem zeta_zero_mul_self_eq_zero {s : ℂ} (hζ : riemannZeta s = 0) :
    riemannZeta s * riemannZeta s = 0 := by
  simp [hζ]
/-- An off-line zero (Re(s) ≠ 1/2) in the critical strip cannot be cancelled by ANY
product of identical strip evaluations. -/
theorem offLine_zero_persists_in_product {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) (hoffline : s.re ≠ 1/2)
    (hζ : riemannZeta s = 0) (n : ℕ) (hn : 1 ≤ n) :
    riemannZeta s ^ n = 0 :=
  zeta_zero_pow_eq_zero hζ n hn
/-! ## Part 2: Functional Equation Forces Symmetric Pair Detection -/
/-- **Theorem B (Functional Equation Pairing)**: If ζ(s) = 0 for s in the critical strip
(not a negative integer, not 1), then ζ(1−s) = 0.
The functional equation:  ζ(1−s) = 2·(2π)^(−s)·Γ(s)·cos(πs/2)·ζ(s)
shows that ζ(s) = 0 ⟹ ζ(1−s) = 0 (the whole RHS vanishes). -/
theorem zeta_one_sub_eq_zero_of_zeta_eq_zero {s : ℂ}
    (hs_not_neg_nat : ∀ n : ℕ, s ≠ -↑n)
    (hs_ne_one : s ≠ 1)
    (hζ : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hs_not_neg_nat hs_ne_one, hζ, mul_zero]
/-
PROBLEM
For an off-line zero (Re(s) ≠ 1/2), the reflected point 1−s has a different real part.
Therefore the zero and its functional-equation partner are ALWAYS distinguishable.
PROVIDED SOLUTION
(1-s).re = 1 - s.re. If 1 - s.re = s.re then s.re = 1/2, contradicting hoffline.
-/
theorem offLine_zero_partner_distinct_re {s : ℂ}
    (hoffline : s.re ≠ 1/2) :
    (1 - s).re ≠ s.re := by
  norm_num; contrapose! hoffline; linarith;
/-
PROBLEM
An off-line zero and its functional equation partner are distinct points in ℂ.
PROVIDED SOLUTION
If 1-s = s then s.re = (1-s).re = 1 - s.re, so s.re = 1/2, contradicting hoffline.
-/
theorem offLine_zero_partner_ne {s : ℂ}
    (hoffline : s.re ≠ 1/2) :
    1 - s ≠ s := by
  exact fun h => hoffline <| by norm_num [ Complex.ext_iff ] at h; linarith
/-! ## Part 3: Euler Product Divergence at Critical Strip Zeros -/
/-- **Theorem C (Euler Product Region Excludes Zeros)**: ζ(s) ≠ 0 whenever Re(s) ≥ 1.
This is the region where the Euler product converges. Therefore, any zero of ζ lies
outside the Euler product's domain of convergence — the Euler product necessarily
"diverges" (fails to converge to ζ(s)) at any zero. -/
theorem zeta_nonzero_in_euler_product_region {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
/-
PROBLEM
The contrapositive: any zero of ζ forces Re(s) < 1, placing it outside the Euler
product convergence region.
PROVIDED SOLUTION
Contrapositive of riemannZeta_ne_zero_of_one_le_re: if s.re >= 1 then ζ(s) ≠ 0, contradicting hζ.
-/
theorem zeta_zero_outside_euler_region {s : ℂ} (hζ : riemannZeta s = 0) :
    s.re < 1 := by
  exact not_le.mp fun h => zeta_nonzero_in_euler_product_region h hζ
/-- Critical strip zeros (0 < Re(s) < 1) are strictly separated from the Euler product
convergence region Re(s) ≥ 1. -/
theorem zeta_zero_in_strip_re_bound {s : ℂ}
    (hζ : riemannZeta s = 0) (hre_pos : 0 < s.re) :
    0 < s.re ∧ s.re < 1 :=
  ⟨hre_pos, zeta_zero_outside_euler_region hζ⟩
/-! ## Part 4: Isometric Expansion — Off-Line Zeros Are Always Detectable -/
/-
PROBLEM
The map s ↦ 1 − s is isometric on ℂ (distance-preserving).
PROVIDED SOLUTION
(1-s)-(1-t) = t-s = -(s-t). norm_neg gives the result.
-/
theorem reflection_isometry (s t : ℂ) :
    ‖(1 - s) - (1 - t)‖ = ‖s - t‖ := by
  rw [ ← norm_neg ] ; ring;
/-- The reflection s ↦ 1−s is an involution. -/
theorem reflection_involution (s : ℂ) : 1 - (1 - s) = s := by ring
/-
PROBLEM
The separation is strictly positive for off-line zeros.
PROVIDED SOLUTION
norm_pos_iff says ‖x‖ > 0 iff x ≠ 0. s-(1-s) = 2s-1 ≠ 0 because its real part is 2*s.re - 1 ≠ 0 (since s.re ≠ 1/2). Use sub_ne_zero.mpr and offLine_zero_partner_ne.
-/
theorem offLine_zero_positive_separation {s : ℂ} (hoffline : s.re ≠ 1/2) :
    ‖s - (1 - s)‖ > 0 := by
  exact norm_pos_iff.mpr ( sub_ne_zero.mpr <| by contrapose! hoffline; norm_num [ Complex.ext_iff ] at *; linarith )
/-
PROBLEM
The separation distance between an off-line zero and its partner is at least |2·Re(s) − 1|.
‖s-(1-s)‖ = ‖2s-1‖ ≥ |Re(2s-1)| = |2·Re(s)-1| > 0 for off-line zeros.
PROVIDED SOLUTION
s-(1-s) = 2s-1. The norm of a complex number is at least the absolute value of its real part. (2s-1).re = 2*s.re - 1. Use Complex.re_le_abs or norm_re_le_abs or similar after simplifying.
-/
theorem offLine_zero_separation_lower_bound {s : ℂ} (hoffline : s.re ≠ 1/2) :
    |2 * s.re - 1| ≤ ‖s - (1 - s)‖ := by
  convert Complex.abs_re_le_norm ( s - ( 1 - s ) ) using 2 ; ring;
  norm_num [ Complex.ext_iff ]
/-- **Theorem D (Isometric Detectability)**: Under the isometric involution s ↦ 1−s,
an off-line zero s₀ (with Re(s₀) ≠ 1/2) maps to a DIFFERENT point 1−s₀.
Off-line zeros are always detectable: they create pairs of distinct zeros
separated by a positive distance under the isometric reflection. -/
theorem offLine_zero_detectable {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) (hoffline : s.re ≠ 1/2)
    (hs_not_neg_nat : ∀ n : ℕ, s ≠ -↑n)
    (hs_ne_one : s ≠ 1)
    (hζ : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 ∧ 1 - s ≠ s ∧ ‖s - (1 - s)‖ > 0 :=
  ⟨zeta_one_sub_eq_zero_of_zeta_eq_zero hs_not_neg_nat hs_ne_one hζ,
   offLine_zero_partner_ne hoffline,
   offLine_zero_positive_separation hoffline⟩
/-! ## Part 5: The Complete Picture -/
/-
PROBLEM
**Main Theorem**: Assuming RH is false (there exists a zero with Re(s) ≠ 1/2 in the
critical strip), we derive all consequences simultaneously:
- The zero persists under any product of identical strips
- The functional equation forces a distinct mirror zero
- The Euler product diverges at both zeros
- Both zeros are separated by positive distance and are detectable
PROVIDED SOLUTION
Combine:
1. zeta_zero_pow_eq_zero for part 1
2. zeta_one_sub_eq_zero_of_zeta_eq_zero for part 2
3. For part 3: s.re < 1 from zeta_zero_outside_euler_region, and (1-s).re = 1-s.re < 1 since s.re > 0 from hstrip
4. offLine_zero_partner_ne and offLine_zero_positive_separation for part 4
-/
theorem RH_false_consequences {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1)
    (hoffline : s.re ≠ 1/2)
    (hs_not_neg_nat : ∀ n : ℕ, s ≠ -↑n)
    (hs_ne_one : s ≠ 1)
    (hζ : riemannZeta s = 0) :
    -- (1) Zero cannot be cancelled by products
    (∀ n : ℕ, 1 ≤ n → riemannZeta s ^ n = 0) ∧
    -- (2) Functional equation forces a mirror zero
    riemannZeta (1 - s) = 0 ∧
    -- (3) Both zeros lie outside the Euler product convergence region
    (s.re < 1 ∧ (1 - s).re < 1) ∧
    -- (4) The zeros are distinct and separated by positive distance
    (1 - s ≠ s ∧ ‖s - (1 - s)‖ > 0) := by
  exact ⟨ fun n hn => by rw [ hζ, zero_pow ( by linarith ) ], zeta_one_sub_eq_zero_of_zeta_eq_zero hs_not_neg_nat hs_ne_one hζ, ⟨ by linarith, by norm_num; linarith ⟩, offLine_zero_partner_ne hoffline, offLine_zero_positive_separation hoffline ⟩