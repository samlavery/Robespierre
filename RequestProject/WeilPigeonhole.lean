import Mathlib

/-!
# Metric Pigeonhole / Covering Lemma

Given a finite set of `N` real numbers all lying in `[a, b]`, there exists a point
`x ∈ [a, b]` at distance at least `(b - a) / (2 * (N + 1))` from every element of the set.

This is the key combinatorial input to `exists_point_far_from_finset_inv_log`:
when `N ≤ C · log T`, the guaranteed separation becomes `≥ c / log T`.

Extracted from Aristotle's Landau package. Axiom footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Set Finset

set_option maxHeartbeats 800000

noncomputable section

namespace ZD.WeilPositivity.Contour

/-- Given `N` reals in `[a, b]`, there is a point in `[a, b]` at distance
`≥ (b-a)/(2*(N+1))` from all of them. Pigeonhole: divide `[a,b]` into `N+1`
subintervals; at least one is free of the given points; its midpoint works. -/
theorem exists_point_far_from_finset {a b : ℝ} (hab : a < b) (S : Finset ℝ)
    (hS : ∀ s ∈ S, s ∈ Icc a b) :
    ∃ x ∈ Icc a b, ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |x - s| := by
  by_contra! h_contra
  have h_union : Set.Icc a b ⊆ ⋃ s ∈ S, Set.Ioo
      (s - (b - a) / (2 * (S.card + 1))) (s + (b - a) / (2 * (S.card + 1))) := by
    exact fun x hx => by
      rcases h_contra x hx with ⟨s, hs, hs'⟩
      exact Set.mem_iUnion₂.mpr
        ⟨s, hs, ⟨by linarith [abs_lt.mp hs'], by linarith [abs_lt.mp hs']⟩⟩
  have h_measure : MeasureTheory.volume
      (⋃ s ∈ S, Set.Ioo (s - (b - a) / (2 * (S.card + 1)))
        (s + (b - a) / (2 * (S.card + 1)))) ≤
      ∑ s ∈ S, MeasureTheory.volume
        (Set.Ioo (s - (b - a) / (2 * (S.card + 1)))
          (s + (b - a) / (2 * (S.card + 1)))) := by
    convert MeasureTheory.measure_biUnion_finset_le _ _
    infer_instance
  have := h_measure.trans' (MeasureTheory.measure_mono h_union)
  norm_num at this
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at this
  ring_nf at this
  rw [ENNReal.ofReal_le_ofReal_iff] at this <;>
    nlinarith [mul_inv_cancel_left₀ (by linarith : (2 + S.card * 2 : ℝ) ≠ 0) (b - a)]

#print axioms exists_point_far_from_finset

/-- Specialization: if `S.card ≤ C * log T` and the interval has length 1
(say `[1, 2]`), the distance is at least `1 / (2*(C * log T + 1))`, which
is `≥ c / log T`. -/
theorem exists_point_far_from_finset_inv_log {C T : ℝ} (hC : 0 < C) (hT : 1 < T)
    (S : Finset ℝ) (hS : ∀ s ∈ S, s ∈ Icc (1 : ℝ) 2)
    (hcard : (S.card : ℝ) ≤ C * Real.log T) :
    ∃ x ∈ Icc (1 : ℝ) 2,
      ∀ s ∈ S, 1 / (2 * (C * Real.log T + 1)) ≤ |x - s| := by
  obtain ⟨x, hx⟩ : ∃ x ∈ Set.Icc 1 2, ∀ s ∈ S, |x - s| ≥ (2 - 1) / (2 * (S.card + 1)) := by
    exact exists_point_far_from_finset (by linarith : (1 : ℝ) < 2) S hS
  exact ⟨x, hx.1, fun s hs =>
    le_trans (by rw [div_le_div_iff₀] <;> linarith) (hx.2 s hs)⟩

#print axioms exists_point_far_from_finset_inv_log

end ZD.WeilPositivity.Contour

end
