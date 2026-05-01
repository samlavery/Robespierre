import Mathlib

/-!
# Weierstrass elementary factor `E₁` for the ξ Hadamard product

The genus-1 Weierstrass factor `E₁(w) = (1 - w) · exp(w)` satisfies
`E₁(0) = 1`, `E₁(1) = 0`, and `‖E₁(w) - 1‖ ≤ 3 ‖w‖²` for `‖w‖ ≤ 1`. This
is the building block for Hadamard's factorization of ξ over the nontrivial
zeros of ζ.

For the ξ product, we use `E₁(z/ρ) = (1 - z/ρ) · exp(z/ρ)` per nontrivial zero
`ρ`. The quadratic bound `‖E₁(w)-1‖ ≤ 3‖w‖²` is the majorant that makes
`∑_ρ ‖E₁(z/ρ) - 1‖` summable via `∑ 1/‖ρ‖² < ∞`.

Ported from codex2's `DigammaVerticalLogBound.lean:18-39`, sign-flipped for
`1 - w` form (codex2 uses `(1+w)·exp(-w)` for Γ). Pure analysis.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD

/-- **Weierstrass elementary factor `E₁`** of genus 1. Vanishes at `w = 1`. -/
def xiWeierstrassFactor (w : ℂ) : ℂ := (1 - w) * Complex.exp w

@[simp] theorem xiWeierstrassFactor_zero : xiWeierstrassFactor 0 = 1 := by
  simp [xiWeierstrassFactor]

@[simp] theorem xiWeierstrassFactor_one : xiWeierstrassFactor 1 = 0 := by
  simp [xiWeierstrassFactor]

theorem xiWeierstrassFactor_differentiable :
    Differentiable ℂ xiWeierstrassFactor := by
  unfold xiWeierstrassFactor
  exact ((differentiable_const 1).sub differentiable_id).mul
    Complex.differentiable_exp

theorem xiWeierstrassFactor_deriv (w : ℂ) :
    deriv xiWeierstrassFactor w = -w * Complex.exp w := by
  unfold xiWeierstrassFactor
  have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h2 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
  have := h1.mul h2
  have heq : -1 * Complex.exp w + (1 - w) * Complex.exp w = -w * Complex.exp w := by ring
  rw [heq] at this
  exact this.deriv

/-- **Quadratic bound for `E₁(w) - 1` on the unit disk**: for `‖w‖ ≤ 1`,
`‖(1 - w) · exp(w) - 1‖ ≤ 3 · ‖w‖²`.

Variant of codex2's `norm_one_add_mul_exp_neg_sub_one_le_three_mul_sq`
applied with `w ↦ -w` (since `(1 + (-w)) · exp(-(-w)) = (1 - w) · exp(w)`). -/
theorem norm_xiWeierstrassFactor_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖xiWeierstrassFactor w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  unfold xiWeierstrassFactor
  -- Decomposition: (1-w)·exp(w) - 1 = (exp(w) - 1 - w) + (-w) · (exp(w) - 1).
  have hdecomp :
      (1 - w) * Complex.exp w - 1 =
        (Complex.exp w - 1 - w) + (-w) * (Complex.exp w - 1) := by
    ring
  -- Bound term 1: ‖exp(w) - 1 - w‖ ≤ ‖w‖².
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w) hw
    simpa [sub_sub] using this
  -- Bound term 2: ‖(-w)·(exp(w) - 1)‖ ≤ 2 · ‖w‖².
  have h2 : ‖(-w) * (Complex.exp w - 1)‖ ≤ 2 * ‖w‖ ^ 2 := by
    calc ‖(-w) * (Complex.exp w - 1)‖
        ≤ ‖(-w)‖ * ‖Complex.exp w - 1‖ := norm_mul_le _ _
      _ = ‖w‖ * ‖Complex.exp w - 1‖ := by rw [norm_neg]
      _ ≤ ‖w‖ * (2 * ‖w‖) := by
          gcongr
          exact Complex.norm_exp_sub_one_le (x := w) hw
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hdecomp]
  calc ‖(Complex.exp w - 1 - w) + (-w) * (Complex.exp w - 1)‖
      ≤ ‖Complex.exp w - 1 - w‖ + ‖(-w) * (Complex.exp w - 1)‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ ^ 2 := add_le_add h1 h2
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- **Per-zero Weierstrass term**: `E₁(z/ρ) - 1`. The building block of the
product `ξ = exp(·) · ∏_ρ E₁(z/ρ)`. Used in `∏(1 + xiWeierstrassTerm ρ z)` form
to pair with Mathlib's `multipliableUniformlyOn_nat_one_add`. -/
def xiWeierstrassTerm (ρ z : ℂ) : ℂ := xiWeierstrassFactor (z / ρ) - 1

theorem one_add_xiWeierstrassTerm (ρ z : ℂ) :
    1 + xiWeierstrassTerm ρ z = xiWeierstrassFactor (z / ρ) := by
  unfold xiWeierstrassTerm; ring

/-- **Quadratic bound**: `‖xiWeierstrassTerm ρ z‖ ≤ 3 · ‖z‖² / ‖ρ‖²` for `‖z‖ ≤ ‖ρ‖`.
Consequence of `norm_xiWeierstrassFactor_sub_one_le` at `w = z/ρ`. -/
theorem norm_xiWeierstrassTerm_le {ρ z : ℂ} (hρ : ρ ≠ 0) (hzρ : ‖z‖ ≤ ‖ρ‖) :
    ‖xiWeierstrassTerm ρ z‖ ≤ 3 * ‖z‖ ^ 2 / ‖ρ‖ ^ 2 := by
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hw : ‖z / ρ‖ ≤ 1 := by
    rw [norm_div, div_le_one hρ_pos]; exact hzρ
  unfold xiWeierstrassTerm
  have hbound := norm_xiWeierstrassFactor_sub_one_le hw
  have hratio : ‖z / ρ‖ ^ 2 = ‖z‖ ^ 2 / ‖ρ‖ ^ 2 := by
    rw [norm_div, div_pow]
  calc ‖xiWeierstrassFactor (z / ρ) - 1‖
      ≤ 3 * ‖z / ρ‖ ^ 2 := hbound
    _ = 3 * (‖z‖ ^ 2 / ‖ρ‖ ^ 2) := by rw [hratio]
    _ = 3 * ‖z‖ ^ 2 / ‖ρ‖ ^ 2 := by ring

/-- `xiWeierstrassTerm ρ` is differentiable in z. -/
theorem xiWeierstrassTerm_differentiable {ρ : ℂ} (hρ : ρ ≠ 0) :
    Differentiable ℂ (fun z => xiWeierstrassTerm ρ z) := by
  unfold xiWeierstrassTerm
  have h_div : Differentiable ℂ (fun z : ℂ => z / ρ) := by
    intro w; exact (differentiableAt_id.div_const ρ)
  exact (xiWeierstrassFactor_differentiable.comp h_div).sub_const 1

/-- `1 + xiWeierstrassTerm ρ` is differentiable in z. -/
theorem one_add_xiWeierstrassTerm_differentiable {ρ : ℂ} (hρ : ρ ≠ 0) :
    Differentiable ℂ (fun z => 1 + xiWeierstrassTerm ρ z) := by
  have hfun : (fun z => 1 + xiWeierstrassTerm ρ z) = (fun z => xiWeierstrassFactor (z / ρ)) := by
    funext z; exact one_add_xiWeierstrassTerm ρ z
  rw [hfun]
  have h_div : Differentiable ℂ (fun z : ℂ => z / ρ) := by
    intro w; exact (differentiableAt_id.div_const ρ)
  exact xiWeierstrassFactor_differentiable.comp h_div

/-- **Vanishes at ρ**: `1 + xiWeierstrassTerm ρ ρ = E₁(ρ/ρ) = E₁(1) = 0`. -/
theorem one_add_xiWeierstrassTerm_at_zero {ρ : ℂ} (hρ : ρ ≠ 0) :
    1 + xiWeierstrassTerm ρ ρ = 0 := by
  rw [one_add_xiWeierstrassTerm]
  have : ρ / ρ = 1 := div_self hρ
  rw [this]
  exact xiWeierstrassFactor_one

#print axioms xiWeierstrassFactor_differentiable
#print axioms xiWeierstrassFactor_deriv
#print axioms norm_xiWeierstrassFactor_sub_one_le
#print axioms norm_xiWeierstrassTerm_le
#print axioms xiWeierstrassTerm_differentiable
#print axioms one_add_xiWeierstrassTerm_differentiable
#print axioms one_add_xiWeierstrassTerm_at_zero

end ZD
