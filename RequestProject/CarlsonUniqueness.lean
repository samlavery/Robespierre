import Mathlib

/-!
# Carlson uniqueness on positive even integers (standalone)

This file provides the complex-analysis tool needed to discharge Gap (ii) of
the β-tower extraction in `CauchyKExtractionViaBetaTower.lean`, factored
out as a self-contained, RH-free lemma.

## Theorem shape

If `φ : ℂ → ℂ` is analytic on a right half-plane `{σ₀ < s.re}`, has
exponential type `< π/2` there, and vanishes at every positive even
integer, then `φ ≡ 0` on the half-plane.

Proof strategy: substitute `f(w) := φ(2*w + 2*K)` for `K` chosen so that
`{−1 < w.re}` lands inside `{σ₀ < s.re}`.  Then `f` is analytic on
`{−1 < w.re}`, has type `2τ < π`, and vanishes at every non-negative
integer (because `2*(n+K)` is a positive even integer for `n ≥ 0` and
`K ≥ 1`).  Apply classical Carlson to `f` (named
`CarlsonClassical_unit_zeros_target`) to conclude `f ≡ 0` on
`{0 < w.re}`, i.e., `φ ≡ 0` on `{2*K < s.re}`.  Lift back to
`{σ₀ < s.re}` by analytic continuation (the half-plane is preconnected,
and `φ` vanishes on a non-empty open subset).

## What is unconditional and what is not

`carlson_even_integer_uniqueness_of_classical` is unconditional in the
sense that, given `CarlsonClassical_unit_zeros_target`, it discharges the
even-integer version.  The classical Carlson core is named as the
remaining complex-analysis obligation — its proof would use mathlib's
`Complex.PhragmenLindelof.right_half_plane_*` applied to
`f(s) / sin(π s)`.

## Axiom footprint

`[propext, Classical.choice, Quot.sound]` for everything proved in this
file.
-/

set_option maxHeartbeats 800000

open Complex Real Set Filter

noncomputable section

namespace ZD.Carlson

/-! ## Classical Carlson on non-negative integers (named target) -/

/-- **Classical Carlson** on a right half-plane with zeros at every
non-negative integer and exponential type `< π`.  Stated as a target
Prop.  The classical proof: `H(s) := f(s) / sin(π s)` removes the
simple poles of `1/sin(π s)` at non-negative integers (since `f` vanishes
there), giving an analytic function on a neighborhood of the closed
right half-plane.  `|sin(π s)| ≥ c · sinh(π |Im s|)` for `Re s` away
from integers, so `‖H s‖ → 0` as `|Im s| → ∞` whenever `τ < π`.  PL on
the right half-plane gives a uniform bound on `H`, and decay forces
`H ≡ 0`, hence `f ≡ 0`. -/
def CarlsonClassical_unit_zeros_target : Prop :=
  ∀ (f : ℂ → ℂ) (B τ : ℝ),
    AnalyticOnNhd ℂ f {s : ℂ | -1 < s.re} →
    0 ≤ B → 0 < τ → τ < Real.pi →
    (∀ s : ℂ, -1 < s.re → ‖f s‖ ≤ B * Real.exp (τ * ‖s‖)) →
    (∀ n : ℕ, f ((n : ℕ) : ℂ) = 0) →
    ∀ s : ℂ, 0 < s.re → f s = 0

/-! ## Helper: shift amount -/

/-- Choose `K : ℕ` so that `K ≥ 1` and `σ₀/2 + 1 ≤ K`, equivalently
`2*K - 2 ≥ σ₀`.  The substitution `s = 2*w + 2*K` then maps
`{−1 < w.re}` to `{σ₀ < s.re}`. -/
private def shiftAmount (σ₀ : ℝ) : ℕ := max 1 (⌈σ₀ / 2 + 1⌉₊)

private lemma shiftAmount_pos (σ₀ : ℝ) : 1 ≤ shiftAmount σ₀ :=
  le_max_left _ _

private lemma shiftAmount_real_pos (σ₀ : ℝ) : 1 ≤ (shiftAmount σ₀ : ℝ) := by
  exact_mod_cast shiftAmount_pos σ₀

private lemma shiftAmount_ge_halfplus_one (σ₀ : ℝ) :
    σ₀ / 2 + 1 ≤ (shiftAmount σ₀ : ℝ) := by
  unfold shiftAmount
  have h_ceil : σ₀ / 2 + 1 ≤ (⌈σ₀ / 2 + 1⌉₊ : ℝ) := Nat.le_ceil _
  have h_max : ((⌈σ₀ / 2 + 1⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈σ₀ / 2 + 1⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  linarith

private lemma shiftAmount_two_minus_two_ge (σ₀ : ℝ) :
    σ₀ ≤ 2 * (shiftAmount σ₀ : ℝ) - 2 := by
  have := shiftAmount_ge_halfplus_one σ₀
  linarith

/-! ## Substitution map -/

/-- The substitution `g(w) := 2*w + 2*K` (with `K = shiftAmount σ₀`).
Maps `{−1 < w.re}` to `{σ₀ < s.re}`. -/
private def shiftMap (K : ℕ) (w : ℂ) : ℂ := 2 * w + 2 * (K : ℂ)

private lemma shiftMap_re (K : ℕ) (w : ℂ) :
    (shiftMap K w).re = 2 * w.re + 2 * K := by
  unfold shiftMap
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im, Complex.ofReal_natCast]

private lemma shiftMap_natCast (K n : ℕ) :
    shiftMap K (n : ℂ) = ((2 * (n + K) : ℕ) : ℂ) := by
  unfold shiftMap
  push_cast
  ring

/-- `g(w) = 2*w + 2*K` is entire (linear). -/
private lemma shiftMap_analyticAt (K : ℕ) (w : ℂ) :
    AnalyticAt ℂ (shiftMap K) w := by
  unfold shiftMap
  exact (analyticAt_const.fun_mul analyticAt_id).add analyticAt_const

private lemma shiftMap_norm_bound (K : ℕ) (w : ℂ) :
    ‖shiftMap K w‖ ≤ 2 * ‖w‖ + 2 * K := by
  unfold shiftMap
  have h2w : ‖(2 : ℂ) * w‖ = 2 * ‖w‖ := by
    rw [norm_mul]; norm_num
  have h2K : ‖(2 : ℂ) * ((K : ℕ) : ℂ)‖ = 2 * (K : ℝ) := by
    rw [norm_mul, Complex.norm_natCast]; norm_num
  calc ‖(2 : ℂ) * w + 2 * ((K : ℕ) : ℂ)‖
      ≤ ‖(2 : ℂ) * w‖ + ‖(2 : ℂ) * ((K : ℕ) : ℂ)‖ := norm_add_le _ _
    _ = 2 * ‖w‖ + 2 * K := by rw [h2w, h2K]

/-! ## The reduction theorem (conditional on classical Carlson) -/

/-- **Even-integer Carlson uniqueness, conditional on classical Carlson.**

Hypotheses:
* `h_classical` — the classical Carlson uniqueness on non-negative
  integers, stated as `CarlsonClassical_unit_zeros_target`.
* `φ` is analytic on the right half-plane `{σ₀ < s.re}`.
* `φ` has exponential type `< π/2` on the half-plane.
* `φ` vanishes at every positive even integer `2*k` for `k ≥ 1`.

Conclusion: `φ ≡ 0` on the half-plane. -/
theorem carlson_even_integer_uniqueness_of_classical
    (h_classical : CarlsonClassical_unit_zeros_target)
    {σ₀ : ℝ} (φ : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ φ {s : ℂ | σ₀ < s.re})
    {B τ : ℝ}
    (hB : 0 ≤ B) (hτ_pos : 0 < τ) (hτ_lt : τ < Real.pi / 2)
    (h_growth : ∀ s : ℂ, σ₀ < s.re → ‖φ s‖ ≤ B * Real.exp (τ * ‖s‖))
    (h_zeros : ∀ k : ℕ, 1 ≤ k → φ ((2*k : ℕ) : ℂ) = 0) :
    ∀ s : ℂ, σ₀ < s.re → φ s = 0 := by
  set K : ℕ := shiftAmount σ₀ with hK_def
  have hK_pos : 1 ≤ K := shiftAmount_pos σ₀
  have hK_real_pos : 1 ≤ (K : ℝ) := shiftAmount_real_pos σ₀
  have hK_bound : σ₀ ≤ 2 * (K : ℝ) - 2 := shiftAmount_two_minus_two_ge σ₀
  -- Map: w ↦ 2w + 2K maps {-1 < Re w} into {σ₀ < Re s}.
  set f : ℂ → ℂ := fun w => φ (shiftMap K w) with hf_def
  -- Step (a): Re-mapping.
  have h_re_map : ∀ w : ℂ, -1 < w.re → σ₀ < (shiftMap K w).re := by
    intro w hw
    rw [shiftMap_re]
    have : (-1 : ℝ) < w.re := hw
    nlinarith [hK_bound]
  -- Step (b): f analytic on {-1 < w.re}.
  have hf_analytic : AnalyticOnNhd ℂ f {w : ℂ | -1 < w.re} := by
    intro w hw
    have hg := shiftMap_analyticAt K w
    have hφ : AnalyticAt ℂ φ (shiftMap K w) := h_analytic _ (h_re_map w hw)
    exact hφ.comp hg
  -- Step (c): growth bound for f with τ' := 2τ < π.
  set τ' : ℝ := 2 * τ with hτ'_def
  have hτ'_pos : 0 < τ' := by positivity
  have hτ'_lt : τ' < Real.pi := by
    have := hτ_lt
    have : τ < Real.pi / 2 := this
    linarith
  set B' : ℝ := B * Real.exp (τ' * (K : ℝ)) with hB'_def
  have hB'_nonneg : 0 ≤ B' := by
    apply mul_nonneg hB
    exact (Real.exp_pos _).le
  have hf_growth : ∀ w : ℂ, -1 < w.re → ‖f w‖ ≤ B' * Real.exp (τ' * ‖w‖) := by
    intro w hw
    have h_in : σ₀ < (shiftMap K w).re := h_re_map w hw
    have h1 : ‖f w‖ ≤ B * Real.exp (τ * ‖shiftMap K w‖) := h_growth _ h_in
    have h2 : ‖shiftMap K w‖ ≤ 2 * ‖w‖ + 2 * K := shiftMap_norm_bound K w
    have h3 : τ * ‖shiftMap K w‖ ≤ τ * (2 * ‖w‖ + 2 * K) := by
      exact mul_le_mul_of_nonneg_left h2 hτ_pos.le
    have h4 : Real.exp (τ * ‖shiftMap K w‖) ≤ Real.exp (τ * (2 * ‖w‖ + 2 * K)) :=
      Real.exp_le_exp.mpr h3
    have h5 : τ * (2 * ‖w‖ + 2 * K) = τ' * ‖w‖ + τ' * (K : ℝ) := by
      simp [hτ'_def]; ring
    rw [h5] at h4
    have h6 : Real.exp (τ' * ‖w‖ + τ' * (K : ℝ))
              = Real.exp (τ' * ‖w‖) * Real.exp (τ' * (K : ℝ)) :=
      Real.exp_add _ _
    rw [h6] at h4
    calc ‖f w‖ ≤ B * Real.exp (τ * ‖shiftMap K w‖) := h1
      _ ≤ B * (Real.exp (τ' * ‖w‖) * Real.exp (τ' * (K : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 hB
      _ = (B * Real.exp (τ' * (K : ℝ))) * Real.exp (τ' * ‖w‖) := by ring
      _ = B' * Real.exp (τ' * ‖w‖) := by rw [hB'_def]
  -- Step (d): zeros of f at non-negative integers.
  have hf_zeros : ∀ n : ℕ, f ((n : ℕ) : ℂ) = 0 := by
    intro n
    show φ (shiftMap K (n : ℂ)) = 0
    rw [shiftMap_natCast K n]
    have hnK : 1 ≤ n + K := by omega
    have h2nK : φ ((2 * (n + K) : ℕ) : ℂ) = 0 := h_zeros (n + K) hnK
    exact h2nK
  -- Step (e): apply classical Carlson.
  have hf_zero : ∀ w : ℂ, 0 < w.re → f w = 0 :=
    h_classical f B' τ' hf_analytic hB'_nonneg hτ'_pos hτ'_lt hf_growth hf_zeros
  -- Step (f): translate back.  For Re s > 2K, write s = 2w + 2K with Re w > 0.
  have h_phi_zero_far : ∀ s : ℂ, 2 * (K : ℝ) < s.re → φ s = 0 := by
    intro s hs
    set w : ℂ := (s - 2 * (K : ℂ)) / 2 with hw_def
    have h_g_w : shiftMap K w = s := by
      show (2 : ℂ) * w + 2 * (K : ℂ) = s
      rw [hw_def]; ring
    have h_smap_re : (shiftMap K w).re = 2 * w.re + 2 * K := shiftMap_re K w
    have h_s_eq : s.re = 2 * w.re + 2 * K := by rw [← h_g_w]; exact h_smap_re
    have h_w_pos : 0 < w.re := by linarith
    have h_f_w : f w = φ s := by
      show φ (shiftMap K w) = φ s
      rw [h_g_w]
    rw [← h_f_w]
    exact hf_zero w h_w_pos
  -- Step (g): identity theorem on the connected open half-plane.
  intro s hs
  -- The half-plane is preconnected.
  have h_preconn : IsPreconnected {s : ℂ | σ₀ < s.re} :=
    (convex_halfSpace_re_gt σ₀).isPreconnected
  -- Pick a witness point in {Re s > 2K} ⊂ {Re s > σ₀}.
  let z₀ : ℂ := (2 * (K : ℝ) + 1 : ℝ)
  have h_z₀_re : z₀.re = 2 * (K : ℝ) + 1 := by simp [z₀]
  have h_z₀_in : z₀ ∈ {s : ℂ | σ₀ < s.re} := by
    show σ₀ < z₀.re
    rw [h_z₀_re]; linarith
  have h_z₀_far : 2 * (K : ℝ) < z₀.re := by rw [h_z₀_re]; linarith
  -- Open neighborhood of z₀ where φ vanishes: {Re s > 2K} is open.
  have h_far_open : IsOpen {s : ℂ | 2 * (K : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h_phi_eventuallyEq : φ =ᶠ[nhds z₀] 0 := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{s : ℂ | 2 * (K : ℝ) < s.re}, ?_, ?_⟩
    · exact h_far_open.mem_nhds h_z₀_far
    · intro s hs
      exact h_phi_zero_far s hs
  -- Apply identity theorem.
  have h_eqOn :=
    h_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      h_preconn h_z₀_in h_phi_eventuallyEq
  exact h_eqOn hs

#print axioms carlson_even_integer_uniqueness_of_classical

end ZD.Carlson

end
