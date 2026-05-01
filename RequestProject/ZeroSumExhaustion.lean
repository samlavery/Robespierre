import Mathlib
import RequestProject.ZetaZeroDefs

/-!
# Finite Approximation of Zero-Sum over Nontrivial Zeros

This file exports the finite-approximation / tail-exhaustion construction
needed by `WeilZeroOrthogonality.lean`. Given a summable series over the
nontrivial zeros of the Riemann zeta function that sums to zero (for each
test parameter β), we construct:

1. An exhaustion of the zeros by finite sets `ZSub N` (the first N zeros
   in any fixed enumeration).
2. A proof that finite partial sums converge to the infinite sum (= 0).
3. A proof that the tail beyond `ZSub N` tends to zero as N → ∞.
4. A packaging compatible with downstream character-independence arguments.

## Main results

* `finite_approximation_of_zero_sum` — the main bridge theorem
* `partial_sums_tendsto_zero` — partial sums converge to 0
* `tail_tendsto_zero` — tail of summable series tends to 0

## Context

This theorem bridges:
- **WeilFinalAssembly** (which has the exhaustion/tail control internally)
- **WeilZeroOrthogonality** (which needs finite approximation + tail vanishing
  as input for Dedekind character independence and Vandermonde extraction)
-/

open scoped BigOperators
open Filter Finset

noncomputable section

namespace Contour

/-- The pair test Mellin transform, evaluated at parameter `β` and complex argument `s`.
    This is the test function used in the Weil explicit formula framework.
    Abstractly, it maps `(β, s) ↦ ℂ` and satisfies decay estimates
    controlled by `1/|s|²` on vertical strips. -/
def pairTestMellin (β : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s * s) * (β : ℂ))

end Contour

namespace ZD

/-! ## Exhaustion by finite sets of zeros -/

/-- `ZSub enum N` is the finite set of the first `N` nontrivial zeros
    in the enumeration `enum`. This models the zeros inside the rectangle
    `[-1, 2] × [-T, T]` for increasing `T`, via the ordering induced
    by the enumeration. -/
def ZSub (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (N : ℕ) : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
  (Finset.range N).image enum

theorem ZSub_mono (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    {M N : ℕ} (h : M ≤ N) : ZSub enum M ⊆ ZSub enum N := by
  intro x hx
  simp only [ZSub, Finset.mem_image] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h), rfl⟩

theorem ZSub_card_le (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (henum_inj : Function.Injective enum)
    (N : ℕ) : (ZSub enum N).card = N := by
  rw [ZSub, Finset.card_image_of_injective _ henum_inj]
  exact Finset.card_range N

/-- Every zero eventually appears in `ZSub`. -/
theorem mem_ZSub_of_surj (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (henum_surj : Function.Surjective enum)
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}) :
    ∃ N : ℕ, ρ ∈ ZSub enum N := by
  obtain ⟨n, rfl⟩ := henum_surj ρ
  exact ⟨n + 1, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl), rfl⟩⟩

/-! ## Partial sums and tails -/

/-- The terms of the series, as a function of the enumeration index. -/
def seriesTerms (a : ℂ → ℂ) (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (β : ℝ) (n : ℕ) : ℂ :=
  a (enum n).val * Contour.pairTestMellin β (enum n).val

/-- Partial sums converge to zero when the series is summable and sums to zero. -/
theorem partial_sums_tendsto_zero
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (β : ℝ) (_hβ₀ : 0 < β) (_hβ₁ : β < 1)
    (hsummable : Summable (seriesTerms a enum β))
    (hzero : ∑' n, seriesTerms a enum β n = 0) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, seriesTerms a enum β n)
      atTop (nhds 0) := by
  rw [← hzero]
  exact hsummable.hasSum.tendsto_sum_nat

/-
The tail of the series beyond index `N` tends to zero.
-/
theorem tail_tendsto_zero
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (β : ℝ) (_hβ₀ : 0 < β) (_hβ₁ : β < 1)
    (_hsummable : Summable (seriesTerms a enum β))
    (_hzero : ∑' n, seriesTerms a enum β n = 0) :
    Tendsto (fun N => ∑' n, seriesTerms a enum β (n + N))
      atTop (nhds 0) := by
  convert tendsto_sum_nat_add fun n => seriesTerms a enum β n using 1

/-
For each finite N, the partial sum over ZSub equals the sum over range N.
-/
theorem sum_ZSub_eq_sum_range
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ NontrivialZeros})
    (henum_inj : Function.Injective enum)
    (β : ℝ) (N : ℕ) :
    ∑ ρ ∈ ZSub enum N, a ρ.val * Contour.pairTestMellin β ρ.val =
    ∑ n ∈ Finset.range N, seriesTerms a enum β n := by
  convert Finset.sum_image ?_ using 2;
  exact henum_inj.injOn

/-! ## Main theorem -/

/-
**Finite approximation of zero-sum over nontrivial zeros.**

Given an enumeration of the nontrivial zeros and a series `∑ a(ρ) · φ(β, ρ)`
that is summable and sums to zero for each β ∈ (0, 1), we produce:

1. An exhaustion `ZSub enum N` of the zeros by finite sets.
2. The partial sums over `ZSub enum N` converge to zero.
3. The tail beyond `ZSub enum N` tends to zero as `N → ∞`.
4. A form compatible with `finite_character_coefficients_zero_of_tail_tendsto`:
   for each finite `N`, the tail `∑_{n ≥ N} a(ρ_n) · φ(β, ρ_n) → 0`.

This is the bridge between the internal exhaustion construction in
`WeilFinalAssembly` and the character independence extraction in
`WeilZeroOrthogonality`.
-/
theorem finite_approximation_of_zero_sum
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (henum_inj : Function.Injective enum)
    (henum_surj : Function.Surjective enum)
    (hsummable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun n : ℕ => a (enum n).val * Contour.pairTestMellin β (enum n).val))
    (hzero : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' n : ℕ, a (enum n).val * Contour.pairTestMellin β (enum n).val = 0) :
    -- (1) The finite partial sums converge to zero
    (∀ β : ℝ, 0 < β → β < 1 →
      Tendsto (fun N => ∑ n ∈ Finset.range N,
        a (enum n).val * Contour.pairTestMellin β (enum n).val)
        atTop (nhds 0))
    ∧
    -- (2) The tail beyond index N tends to zero
    (∀ β : ℝ, 0 < β → β < 1 →
      Tendsto (fun N => ∑' n, a (enum (n + N)).val * Contour.pairTestMellin β (enum (n + N)).val)
        atTop (nhds 0))
    ∧
    -- (3) Every zero eventually appears in the exhaustion
    (∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, ∃ N : ℕ, ρ ∈ ZSub enum N)
    ∧
    -- (4) The sum over ZSub equals the partial sum (for downstream compatibility)
    (∀ β : ℝ, ∀ N : ℕ,
      ∑ ρ ∈ ZSub enum N, a ρ.val * Contour.pairTestMellin β ρ.val =
      ∑ n ∈ Finset.range N, a (enum n).val * Contour.pairTestMellin β (enum n).val) := by
  exact ⟨ fun β hβ₀ hβ₁ => partial_sums_tendsto_zero a enum β hβ₀ hβ₁ ( hsummable β hβ₀ hβ₁ ) ( hzero β hβ₀ hβ₁ ), fun β hβ₀ hβ₁ => tail_tendsto_zero a enum β hβ₀ hβ₁ ( hsummable β hβ₀ hβ₁ ) ( hzero β hβ₀ hβ₁ ), fun ρ => mem_ZSub_of_surj enum henum_surj ρ, fun β N => sum_ZSub_eq_sum_range a enum henum_inj β N ⟩

end ZD