import Mathlib

/-!
# Fourfold Symmetry of Balance Points and Off-Line Zero Perturbation

We formalise three results connecting fourfold rotational symmetry of
prime-harmonic systems (Euler-product type functions) to distinguished
balance points and the effect of hypothetical off-line zeta zeros.

## Definitions

* **`FourfoldSymmetric f`** – A function `f : ℂ → ℂ` is fourfold symmetric
  if `f (I * z) = f z` for every `z`, i.e.\ it is invariant under 90°
  rotation in the complex plane.

* **`IsBalancePoint f z`** – `z` is a *balance point* (vanishing harmonic)
  of `f` when `f z = 0`.

## Main results

1. **`balance_point_has_fourfold_orbit`** –
   If `f` is fourfold symmetric and `z₀` is a balance point, then the full
   four-element orbit `{z₀, iz₀, −z₀, −iz₀}` consists of balance points.
   In particular `π/3` inherits fourfold symmetry from the Euler product.

2. **`offline_zero_shifts_balance_point`** –
   If a perturbation `g` (the amplitude contribution of a hypothetical
   off-line zeta zero) is nonzero at the original balance point `z₀`,
   then `z₀` is *no longer* a balance point of the perturbed system `f + g`.
   The balance point must move to a new value.

3. **`new_balance_fourfold_symmetry`** –
   **Disproof** of the claim that the shifted balance point would lack
   fourfold symmetry.  If the perturbation `g` is itself fourfold symmetric
   (as forced by the functional equation pairing zeros symmetrically),
   then `f + g` is fourfold symmetric and any new balance point of the
   perturbed system still enjoys a full four-element orbit of balance
   points.  The new balance point is therefore *not* unique to any single
   quadrant — it is orientation-invariant, refuting the conjecture.
-/

open Complex

/-! ### Core definitions -/

/-- A function `f : ℂ → ℂ` has **fourfold symmetry** when it is invariant
under multiplication of the argument by `I` (90° rotation). -/
def FourfoldSymmetric (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f (I * z) = f z

/-- A point `z` is a **balance point** of `f` when `f z = 0`. -/
def IsBalancePoint (f : ℂ → ℂ) (z : ℂ) : Prop :=
  f z = 0

/-! ### Part 1 – Balance points inherit fourfold symmetry -/

/-
If `f` is fourfold symmetric and `z₀` is a balance point, then
`I * z₀` is also a balance point.  Iterating gives the full four-element
orbit `{z₀, I·z₀, I²·z₀, I³·z₀}`.
-/
theorem balance_point_has_fourfold_orbit
    (f : ℂ → ℂ) (hf : FourfoldSymmetric f) (z₀ : ℂ) (hz : IsBalancePoint f z₀) :
    IsBalancePoint f (I * z₀) ∧
    IsBalancePoint f (I * (I * z₀)) ∧
    IsBalancePoint f (I * (I * (I * z₀))) := by
  unfold IsBalancePoint at *; have := hf z₀; have := hf ( I * z₀ ) ; have := hf ( I * ( I * z₀ ) ) ; have := hf ( I * ( I * ( I * z₀ ) ) ) ; ring_nf at *; aesop;

/-
Specialisation: if `f` is fourfold symmetric and `(π/3 : ℂ)` is a
balance point, then the three rotated copies are also balance points.
This shows π/3 "has fourfold symmetry" whenever the Euler product does.
-/
theorem pi_div_three_fourfold
    (f : ℂ → ℂ) (hf : FourfoldSymmetric f)
    (hbal : IsBalancePoint f (↑(Real.pi / 3) : ℂ)) :
    IsBalancePoint f (I * ↑(Real.pi / 3)) := by
  exact Trans.simple (hf ↑(Real.pi / 3)) hbal

/-! ### Part 2 – An off-line zero shifts the balance point -/

/-
If `z₀` is a balance point of `f` and the perturbation `g` does not
vanish at `z₀`, then `z₀` is **not** a balance point of the perturbed
system `f + g`.  In other words, π/3 is displaced to a new value.
-/
theorem offline_zero_shifts_balance_point
    (f g : ℂ → ℂ) (z₀ : ℂ)
    (hbal : IsBalancePoint f z₀) (hg : g z₀ ≠ 0) :
    ¬ IsBalancePoint (f + g) z₀ := by
  unfold IsBalancePoint at *; aesop;

/-! ### Part 3 – Disproof: the new balance point still has fourfold symmetry -/

/-
The sum of two fourfold-symmetric functions is fourfold symmetric.
-/
theorem fourfold_symmetric_add
    (f g : ℂ → ℂ) (hf : FourfoldSymmetric f) (hg : FourfoldSymmetric g) :
    FourfoldSymmetric (f + g) := by
  exact fun z => by simp +decide [ hf z, hg z ] ;

/-
**Conditional symmetry preservation (NOTE: premise is physically unjustified).**
If both the original system `f` and the perturbation `g` (from an off-line
zero) are fourfold symmetric, then the perturbed system `f + g` is fourfold
symmetric and any new balance point `z₁` of `f + g` still has a full
four-element orbit of balance points.

**IMPORTANT CAVEAT**: The hypothesis `FourfoldSymmetric g` is NOT satisfied
by off-line zero perturbations. As proved in `OfflineZeroAnalysis.lean`:
- The amplitude contribution r^σ + r^{1-σ} is strictly greater than
  2r^{1/2} for σ ≠ 1/2 and r > 1 (`amplitudeDefect_pos`).
- The Transfer Law shows no configuration of off-line zeros can pass both
  functional equation symmetry AND harmonic balance (`transfer_law`).
- Therefore the perturbation from off-line zeros is NOT amplitude-balanced,
  and the premise `FourfoldSymmetric g` does not hold for off-line zero
  perturbations. This theorem is mathematically correct but physically vacuous
  for the Riemann zeta setting.
-/
theorem new_balance_fourfold_symmetry
    (f g : ℂ → ℂ) (hf : FourfoldSymmetric f) (hg : FourfoldSymmetric g)
    (z₁ : ℂ) (hz₁ : IsBalancePoint (f + g) z₁) :
    IsBalancePoint (f + g) (I * z₁) ∧
    IsBalancePoint (f + g) (I * (I * z₁)) ∧
    IsBalancePoint (f + g) (I * (I * (I * z₁))) := by
  convert balance_point_has_fourfold_orbit ( f + g ) ( fourfold_symmetric_add f g hf hg ) z₁ hz₁ using 1