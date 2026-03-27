import Mathlib
/-! # Prime Distribution Observables under Rotation Symmetry
This file defines the key observables for detecting off-axis behavior
of Riemann zeta zeros in the prime distribution, following the
rotation-symmetry framework.
## Main definitions
* `realAxisDistortion` — Chebyshev-type partial sum of the von Mangoldt function
* `offAxisRealObservable` — real component of the rotated off-axis observable
* `offAxisImagObservable` — imaginary component of the rotated off-axis observable
* `rotatedPrimeDensityNormSq` — squared norm of the rotated prime density
* `realObservableDistortion` — combined distortion observable
* `RotatedPrimeDensityDetectorEvent` — the detector fires for off-axis zeros
-/
open ArithmeticFunction Real
noncomputable section
/-- The real-axis distortion at `n` is the partial Chebyshev sum `∑_{k=1}^{n} Λ(k)`,
    measuring cumulative prime-power density on the number line. -/
def realAxisDistortion : ℕ → ℝ
  | 0 => 0
  | (n + 1) => realAxisDistortion n + Λ (n + 1)
/-- The off-axis real observable parametrized by `(σ, t)` where `σ` is the real part
    of a zeta zero and `t` is the rotation parameter. Measures the real component
    of the departure from critical-line behavior. -/
def offAxisRealObservable (σ t : ℝ) : ℝ :=
  (σ - 1 / 2) * cos t
/-- The off-axis imaginary observable. -/
def offAxisImagObservable (σ t : ℝ) : ℝ :=
  (σ - 1 / 2) * sin t
/-- Squared norm of the rotated prime density contribution. -/
def rotatedPrimeDensityNormSq (σ t : ℝ) : ℝ :=
  (offAxisRealObservable σ t) ^ 2 + (offAxisImagObservable σ t) ^ 2
/-- The real observable distortion combines the off-axis deviation
    with the prime-counting distortion. -/
def realObservableDistortion (σ : ℝ) (n : ℕ) : ℝ :=
  (σ - 1 / 2) * realAxisDistortion n
/-- The rotated prime density detector event fires when the squared norm
    is nonzero for some rotation parameter, detecting off-axis zeros. -/
def RotatedPrimeDensityDetectorEvent (ρ : ℂ) : Prop :=
  ∃ t : ℝ, rotatedPrimeDensityNormSq ρ.re t ≠ 0
/-- The rotated prime density detector: σ passes iff σ = 1/2. -/
def rotatedPrimeDensityDetectorPasses (σ : ℝ) : Prop :=
  ∀ t : ℝ, rotatedPrimeDensityNormSq σ t = 0
/-
PROBLEM
============================================================
Basic lemmas about realAxisDistortion
============================================================
PROVIDED SOLUTION
Induction on n. Base case: both sides are 0 (empty sum). Step: realAxisDistortion (n+1) = realAxisDistortion n + Λ(n+1) by definition, and the sum over range (n+1) = sum over range n + Λ(n+1) by Finset.sum_range_succ.
-/
theorem realAxisDistortion_eq_sum (n : ℕ) :
    realAxisDistortion n = ∑ k ∈ Finset.range n, Λ (k + 1) := by
      -- We proceed by induction on $n$.
      induction' n with n ih;
      · rfl;
      · rw [ Finset.sum_range_succ, show realAxisDistortion ( n + 1 ) = realAxisDistortion n + Λ ( n + 1 ) from rfl, ih ]
/-
PROVIDED SOLUTION
Direct from the definition of realAxisDistortion.
-/
theorem realAxisDistortion_succ (n : ℕ) :
    realAxisDistortion (n + 1) = realAxisDistortion n + Λ (n + 1) := by
      rfl
/-
PROVIDED SOLUTION
This is vonMangoldt_nonneg.
-/
theorem realAxisDistortion_increment_nonneg (n : ℕ) :
    0 ≤ Λ (n + 1) := by
      grind +suggestions
/-
PROVIDED SOLUTION
Use vonMangoldt_apply_prime to get Λ(p) = log p, then log p > 0 since p ≥ 2 > 1.
-/
theorem realAxisDistortion_increment_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < (Λ p : ℝ) := by
      simp +decide [ ArithmeticFunction.vonMangoldt, hp ];
      exact if_pos ( hp.isPrimePow ) ▸ Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt )
/-
PROVIDED SOLUTION
For n ≥ 2, realAxisDistortion n ≥ realAxisDistortion 2 = realAxisDistortion 1 + Λ(2) = 0 + Λ(2) = log 2 > 0. Show by induction or by direct computation that realAxisDistortion is monotone (increments are nonneg by vonMangoldt_nonneg) and that realAxisDistortion 2 = Λ(1) + Λ(2). Actually realAxisDistortion 1 = realAxisDistortion 0 + Λ(1) = 0 + 0 = 0 (since Λ(1) = 0), and realAxisDistortion 2 = 0 + Λ(2) = log 2 > 0. Then for n ≥ 2, realAxisDistortion n ≥ realAxisDistortion 2 > 0 since each increment is nonneg.
-/
theorem realAxisDistortion_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < realAxisDistortion n := by
      induction hn <;> norm_num [ pow_succ', * ] at *;
      · rw [ show realAxisDistortion 2 = realAxisDistortion 1 + Λ 2 by rfl ] ; norm_num [ Nat.Prime, realAxisDistortion ];
        exact realAxisDistortion_increment_pos_of_prime Nat.prime_two;
      · exact add_pos_of_pos_of_nonneg ‹_› ( realAxisDistortion_increment_nonneg _ )
/-
PROBLEM
============================================================
Basic lemmas about offAxisRealObservable
============================================================
PROVIDED SOLUTION
Unfold offAxisRealObservable, then (1/2 - 1/2) * cos t = 0 * cos t = 0.
-/
theorem offAxisRealObservable_axis (t : ℝ) :
    offAxisRealObservable (1 / 2) t = 0 := by
      unfold offAxisRealObservable; norm_num;
/-
PROVIDED SOLUTION
Unfold, cos 0 = 1, so (σ - 1/2) * 1 = σ - 1/2.
-/
theorem offAxisRealObservable_at_zero (σ : ℝ) :
    offAxisRealObservable σ 0 = σ - 1 / 2 := by
      unfold offAxisRealObservable; norm_num;
/-
PROVIDED SOLUTION
offAxisRealObservable σ 0 = σ - 1/2 by offAxisRealObservable_at_zero, which is > 0 since σ > 1/2.
-/
theorem offAxisRealObservable_at_zero_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < offAxisRealObservable σ 0 := by
      unfold offAxisRealObservable; norm_num; linarith;
/-
PROVIDED SOLUTION
Unfold: (1-σ - 1/2) * cos t = (1/2 - σ) * cos t = -(σ - 1/2) * cos t. Use ring.
-/
theorem offAxisRealObservable_neg_x (σ t : ℝ) :
    offAxisRealObservable (1 - σ) t = -offAxisRealObservable σ t := by
      unfold offAxisRealObservable; ring;
/-
PROVIDED SOLUTION
Unfold, use cos(-t) = cos t.
-/
theorem offAxisRealObservable_neg_t (σ t : ℝ) :
    offAxisRealObservable σ (-t) = offAxisRealObservable σ t := by
      unfold offAxisRealObservable; simp +decide [ Real.cos_neg ] ;
/-
PROBLEM
============================================================
Basic lemmas about offAxisImagObservable
============================================================
PROVIDED SOLUTION
Unfold: (1/2 - 1/2) * sin t = 0.
-/
theorem offAxisImagObservable_axis (t : ℝ) :
    offAxisImagObservable (1 / 2) t = 0 := by
      unfold offAxisImagObservable; norm_num;
/-
PROVIDED SOLUTION
Unfold, sin 0 = 0, so (σ - 1/2) * 0 = 0.
-/
theorem offAxisImagObservable_at_zero (σ : ℝ) :
    offAxisImagObservable σ 0 = 0 := by
      unfold offAxisImagObservable; norm_num;
/-
PROVIDED SOLUTION
Unfold: (1-σ - 1/2) * sin t = -(σ - 1/2) * sin t. Use ring.
-/
theorem offAxisImagObservable_neg_x (σ t : ℝ) :
    offAxisImagObservable (1 - σ) t = -offAxisImagObservable σ t := by
      unfold offAxisImagObservable; ring;
/-
PROVIDED SOLUTION
Unfold, use sin(-t) = -sin t, so (σ - 1/2) * (-sin t) = -(σ - 1/2) * sin t.
-/
theorem offAxisImagObservable_neg_t (σ t : ℝ) :
    offAxisImagObservable σ (-t) = -offAxisImagObservable σ t := by
      unfold offAxisImagObservable; ring;
      rw [ Real.sin_neg ] ; ring;
/-
PROBLEM
============================================================
Rotated prime density norm and detector
============================================================
PROVIDED SOLUTION
Unfold rotatedPrimeDensityNormSq, offAxisRealObservable, offAxisImagObservable. Get ((σ-1/2)*cos t)^2 + ((σ-1/2)*sin t)^2 = (σ-1/2)^2 * (cos²t + sin²t) = (σ-1/2)^2. Use sin_sq_add_cos_sq or cos_sq_add_sin_sq and ring.
-/
theorem rotatedPrimeDensityNormSq_eq (σ t : ℝ) :
    rotatedPrimeDensityNormSq σ t = (σ - 1 / 2) ^ 2 := by
      unfold rotatedPrimeDensityNormSq offAxisRealObservable offAxisImagObservable; ring;
      rw [ Real.sin_sq, Real.cos_sq ] ; ring;
/-
PROVIDED SOLUTION
Unfold rotatedPrimeDensityDetectorPasses. Using rotatedPrimeDensityNormSq_eq, we need (∀ t, (σ-1/2)^2 = 0) ↔ σ = 1/2. The LHS simplifies since (σ-1/2)^2 doesn't depend on t: just (σ-1/2)^2 = 0 ↔ σ-1/2 = 0 ↔ σ = 1/2. Use sq_eq_zero_iff and sub_eq_zero.
-/
theorem rotatedPrimeDensityDetector_iff (σ : ℝ) :
    rotatedPrimeDensityDetectorPasses σ ↔ σ = 1 / 2 := by
      unfold rotatedPrimeDensityDetectorPasses;
      -- Using `rotatedPrimeDensityNormSq_eq`, we can rewrite the goal in terms of `σ - 1/2`.
      simp [rotatedPrimeDensityNormSq_eq];
      rw [ sub_eq_zero ]
/-
PROBLEM
============================================================
Real observable distortion
============================================================
PROVIDED SOLUTION
Unfold realObservableDistortion and use realAxisDistortion_eq_sum.
-/
theorem realObservableDistortion_eq_sum (σ : ℝ) (n : ℕ) :
    realObservableDistortion σ n =
      (σ - 1 / 2) * ∑ k ∈ Finset.range n, Λ (k + 1) := by
        exact realAxisDistortion_eq_sum n ▸ rfl
/-
PROVIDED SOLUTION
Unfold realObservableDistortion. realAxisDistortion 0 = 0 by definition, so (σ - 1/2) * 0 = 0.
-/
theorem realObservableDistortion_at_zero (σ : ℝ) :
    realObservableDistortion σ 0 = 0 := by
      exact MulZeroClass.mul_zero _

/-- `realAxisDistortion` written in the same `Ioc` form as `Chebyshev.psi`. -/
theorem realAxisDistortion_eq_sum_Ioc (n : ℕ) :
    realAxisDistortion n = ∑ k ∈ Finset.Ioc 0 n, Λ k := by
  induction' n with n ih
  · simp [realAxisDistortion]
  · rw [show realAxisDistortion (n + 1) = realAxisDistortion n + Λ (n + 1) from rfl,
      ih, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- `realAxisDistortion` is the Chebyshev `ψ` function evaluated at natural inputs. -/
theorem realAxisDistortion_eq_psi (n : ℕ) :
    realAxisDistortion n = Chebyshev.psi n := by
  rw [realAxisDistortion_eq_sum_Ioc, Chebyshev.psi]
  norm_num

/-- Rewriting the distortion error in terms of the standard Chebyshev `ψ` function. -/
theorem realAxisDistortion_sub_eq_psi_sub (n : ℕ) :
    realAxisDistortion n - (n : ℝ) = Chebyshev.psi n - (n : ℝ) := by
  rw [realAxisDistortion_eq_psi]
end
