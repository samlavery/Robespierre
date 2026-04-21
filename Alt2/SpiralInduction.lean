/-
  GRH.SpiralInduction.lean — Spiral Induction Framework for Dirichlet Series
  ======================================================================

  The Dirichlet series ζ(s) = Σ n^{-s} traces a spiral in ℂ: each term
  has amplitude n^{-σ} and phase -t·log n. Consecutive integers give
  regular phase increments Δθ ≈ t/n.

  Engine: ‖S_{N+1}‖² = ‖S_N‖² + (N+1)^{-2σ} + 2·Re(S_N · conj((N+1)^{-s}))

  STRUCTURAL NOTE: In the critical strip (1/2 < σ < 1), the partial
  sums S(s,N) diverge — Euler-Maclaurin gives S(s,N) = ζ(s) + N^{1-s}/(1-s) + O(N^{-σ}),
  where the main term N^{1-s}/(1-s) has growing amplitude N^{1-σ} → ∞.
  Therefore partial sum nonvanishing does NOT imply ζ(s) ≠ 0 (the sums
  are nonzero regardless of whether ζ has zeros). See GRH.Mertens341.lean
  and GRH.SpiralNonvanishing.lean for approaches that DO connect to ζ values.

  What this file provides: infrastructure for studying partial Dirichlet
  sums — the normSq recurrence, cross-term bounds, and base case.
  The StepMonotone sorry is exploratory (and likely false per-step;
  anti-aligned steps decrease normSq).

  Proved (zero axioms):
  • Base case: ‖S(s,2)‖ ≥ 1 - 2^{-σ} > 0
  • normSq recurrence and window telescoping
  • StepMonotone → normSq non-decreasing → ‖S(s,N)‖ > 0 for all N ≥ 2
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace GRH.SpiralInduction

/-! ## Definitions -/

noncomputable def S (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (↑(n + 1) : ℂ) ^ (-s)

/-! ## Basic identities -/

theorem S_zero (s : ℂ) : S s 0 = 0 := by simp [S]

theorem S_one (s : ℂ) : S s 1 = 1 := by simp [S]

theorem S_succ (s : ℂ) (N : ℕ) :
    S s (N + 1) = S s N + (↑(N + 1) : ℂ) ^ (-s) := by
  simp [S, Finset.sum_range_succ]

theorem term_norm (n : ℕ) (s : ℂ) :
    ‖(↑(n + 1) : ℂ) ^ (-s)‖ = ((n + 1) : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1)]
  simp [Complex.neg_re]

/-! ## The normSq recurrence (the engine) -/

theorem normSq_recurrence (s : ℂ) (N : ℕ) :
    Complex.normSq (S s (N + 1)) =
    Complex.normSq (S s N) +
    Complex.normSq ((↑(N + 1) : ℂ) ^ (-s)) +
    2 * (S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re := by
  rw [S_succ]; exact Complex.normSq_add _ _

theorem cross_term_bound (s : ℂ) (N : ℕ) :
    |2 * (S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re| ≤
    2 * ‖S s N‖ * ‖(↑(N + 1) : ℂ) ^ (-s)‖ := by
  calc |2 * (S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re|
      = 2 * |(S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ‖S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))‖ := by
        apply mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = 2 * (‖S s N‖ * ‖(↑(N + 1) : ℂ) ^ (-s)‖) := by
        rw [norm_mul, Complex.norm_conj]
    _ = 2 * ‖S s N‖ * ‖(↑(N + 1) : ℂ) ^ (-s)‖ := by ring

theorem normSq_window (s : ℂ) (N K : ℕ) :
    Complex.normSq (S s (N + K)) =
    Complex.normSq (S s N) +
    ∑ k ∈ Finset.range K,
      (Complex.normSq ((↑(N + k + 1) : ℂ) ^ (-s)) +
       2 * (S s (N + k) * starRingEnd ℂ ((↑(N + k + 1) : ℂ) ^ (-s))).re) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show N + (K + 1) = (N + K) + 1 from by omega]
    rw [normSq_recurrence, ih, Finset.sum_range_succ]
    simp only [add_assoc]

/-! ## Base case -/

theorem S_two_norm_pos (s : ℂ) (hσ : 0 < s.re) : 0 < ‖S s 2‖ := by
  have h2 : S s 2 = 1 + (↑(2 : ℕ) : ℂ) ^ (-s) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, S_succ, S_one]
  rw [h2, norm_pos_iff]
  intro h
  have h1 : (↑(2 : ℕ) : ℂ) ^ (-s) = -1 := by linear_combination h
  have h2 : ‖(↑(2 : ℕ) : ℂ) ^ (-s)‖ = 1 := by rw [h1, norm_neg, norm_one]
  rw [Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re] at h2
  exact absurd h2 (ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (show 1 < 2 by omega)) (by linarith)))

theorem S_two_lower_bound (s : ℂ) (_hσ : 0 < s.re) :
    1 - (2 : ℝ) ^ (-s.re) ≤ ‖S s 2‖ := by
  have h2 : S s 2 = 1 + (↑(2 : ℕ) : ℂ) ^ (-s) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, S_succ, S_one]
  rw [h2]
  have hle : ‖(1 : ℂ)‖ - ‖(↑(2 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ) + (↑(2 : ℕ) : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(↑(2 : ℕ) : ℂ) ^ (-s))
    rw [norm_neg, sub_neg_eq_add] at h
    linarith [abs_le.mp (abs_norm_sub_norm_le (1 : ℂ) (-(↑(2 : ℕ) : ℂ) ^ (-s)))]
  calc 1 - (2 : ℝ) ^ (-s.re) =
      ‖(1 : ℂ)‖ - ‖(↑(2 : ℕ) : ℂ) ^ (-s)‖ := by
        rw [norm_one, Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re]
        push_cast; ring
    _ ≤ ‖(1 : ℂ) + (↑(2 : ℕ) : ℂ) ^ (-s)‖ := hle

/-! ## The gap: StepMonotone

StepMonotone s says: at each step N ≥ 2,
  (N+1)^{-2σ} + 2·Re(S_N · conj((N+1)^{-s})) ≥ 0

Equivalently: cos(angle between S_N and (N+1)^{-s}) > -(N+1)^{-σ}/(2‖S_N‖).

This is a Baker-type statement: the spiral's phase rotation
(increment ≈ t/N per step) prevents exact anti-alignment.
As ‖S_N‖ grows, the bound becomes easier to satisfy. -/

def StepMonotone (s : ℂ) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    Complex.normSq (S s N) ≤ Complex.normSq (S s (N + 1))

/-! ## StepMonotone → nonvanishing (PROVED) -/

theorem lower_bound_of_monotone (s : ℂ) (_hσ : 0 < s.re)
    (hmono : StepMonotone s) :
    ∀ N : ℕ, 2 ≤ N → Complex.normSq (S s 2) ≤ Complex.normSq (S s N) := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn : 2 ≤ n
    · exact le_trans (ih hn) (hmono n hn)
    · have : n = 1 := by omega
      subst this; norm_num

theorem partial_sums_nonvanishing (s : ℂ) (hσ : 0 < s.re)
    (hmono : StepMonotone s) :
    ∀ N : ℕ, 2 ≤ N → 0 < ‖S s N‖ := by
  intro N hN
  have hbase := S_two_norm_pos s hσ
  have hlb := lower_bound_of_monotone s hσ hmono N hN
  rw [norm_pos_iff]; intro h; rw [h, map_zero] at hlb
  linarith [Complex.normSq_pos.mpr (norm_pos_iff.mp hbase)]

end GRH.SpiralInduction
