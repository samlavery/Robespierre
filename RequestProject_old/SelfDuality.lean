/-
# Self-Duality and the Critical Line

We formalize the algebraic/spectral argument that β = 1/2 is the unique
self-dual point under the functional-equation involution β ↦ 1 − β.

## Main results

1. `involution_unique_fixed_point`: The involution x ↦ 1 − x on ℝ has
   unique fixed point x = 1/2.

2. `self_dual_weight`: For any base p > 1 (e.g. a prime), the equality
   p^{-β} = p^{-(1-β)} holds iff β = 1/2.  This is the "weight matching"
   condition: the harmonic amplitude at a zero ρ = β + iγ equals the
   amplitude at its dual 1 − ρ̄ = (1−β) + iγ precisely on the critical line.

3. `imbalance_vanishes`: The imbalance factor p^{-(β − 1/2)} = 1
   iff β = 1/2.

4. After folding at Im = 0, the oscillatory cos factor is eliminated but
   the amplitude p^{-β} survives. Duality under the functional equation
   then forces β = 1/2 (`fold_plus_duality_forces_half`).

5. `critical_line_characterization`: The critical line β = 1/2 is
   characterized as the unique locus where fold-symmetry and
   functional-equation duality are simultaneously satisfied.

## Mathematical context

In the zeta framework, what forces Re(ρ) = 1/2 is the combination of:
- The functional equation ξ(s) = ξ(1-s), which pairs s ↔ 1-s
- Self-dual spectral normalization

In the "folding" language used by the user:
- Fold at Im = 0 kills top/bottom antisymmetry (conjugate pairs collapse)
- The strip anchor selects the balanced sector
- Duality x ↔ 1-x says only the midpoint x = 1/2 is invariant
- Therefore the only residue-free real location is x = 1/2

The crisp conclusion: x = 1/2 is forced if and only if the operator or
harmonic transport enforces self-duality under x ↦ 1-x and excludes
residual off-center weights. Without that exclusion, folding alone gives
symmetry reduction but not critical-line localization.
-/

import Mathlib

open Real

noncomputable section

/-! ## Part 1: The involution x ↦ 1 − x has unique fixed point 1/2 -/

/-- The functional-equation involution on real parts. -/
def feInvolution (x : ℝ) : ℝ := 1 - x

theorem feInvolution_involutive : Function.Involutive feInvolution := by
  intro x; simp [feInvolution]

/-- The unique fixed point of β ↦ 1 − β is β = 1/2. -/
theorem involution_unique_fixed_point (β : ℝ) :
    feInvolution β = β ↔ β = 1 / 2 := by
  simp [feInvolution]; constructor <;> intro h <;> linarith

/-! ## Part 2: Self-dual weight matching p^{-β} = p^{-(1-β)} iff β = 1/2 -/

/-- For p > 1, the dual weights p^{-β} and p^{-(1-β)} are equal iff β = 1/2.
    This encodes the key spectral self-duality condition: the harmonic amplitude
    at a zero matches its functional-equation dual precisely on the critical line. -/
theorem self_dual_weight (p β : ℝ) (hp : 1 < p) :
    p ^ (-β) = p ^ (-(1 - β)) ↔ β = 1 / 2 := by
  rw [Real.rpow_def_of_pos, Real.rpow_def_of_pos] <;> norm_num <;> try linarith
  constructor <;> intro h <;> nlinarith [Real.log_pos hp]

/-! ## Part 3: The imbalance factor p^{-(β - 1/2)} = 1 iff β = 1/2 -/

/-- The factorization p^{-β} = p^{-1/2} · p^{-(β-1/2)}.
    The universal piece is p^{-1/2}; the residual imbalance is p^{-(β-1/2)}. -/
theorem imbalance_factorization (p β : ℝ) (hp : 0 < p) :
    p ^ (-β) = p ^ (-(1/2 : ℝ)) * p ^ (-(β - 1/2)) := by
  rw [← Real.rpow_add hp]; ring_nf

/-- The imbalance factor p^{-(β-1/2)} equals 1 precisely when β = 1/2. -/
theorem imbalance_vanishes (p β : ℝ) (hp : 1 < p) :
    p ^ (-(β - 1/2)) = 1 ↔ β = 1/2 := by
  rw [Real.rpow_def_of_pos] <;> norm_num <;> try linarith
  exact ⟨fun h => by rcases h with ((rfl | rfl | rfl) | h) <;> linarith,
         fun h => Or.inr <| by linarith⟩

/-! ## Part 4: Conjugate-pair folding

The conjugate pair at ρ = β + iγ and ρ̄ = β − iγ contributes
  p^{-ρ} + p^{-ρ̄} = 2 p^{-β} cos(γ log p).
Folding at Im = 0 (averaging over ±γ) kills the odd (sin) part; the surviving
even amplitude is p^{-β}. Duality then forces this amplitude to β = 1/2. -/

/-- After folding (the cos factor averages out or is projected away),
    the surviving amplitude is p^{-β}. Duality then forces β = 1/2. -/
theorem fold_plus_duality_forces_half (p β : ℝ) (hp : 1 < p)
    (h_self_dual : p ^ (-β) = p ^ (-(1 - β))) :
    β = 1 / 2 :=
  (self_dual_weight p β hp).mp h_self_dual

/-! ## Part 5: Synthesis — the balanced-conjugate argument

Combining all pieces:
- Conjugate pairs fold to amplitude p^{-β}.
- The functional equation pairs β with 1 − β.
- Self-duality (no residual imbalance) requires p^{-β} = p^{-(1-β)}.
- The unique solution is β = 1/2.

Therefore x = 1/2 is the unique residue-free balance point. -/

/-- If for every p > 1 the spectral weight at β equals its dual weight
    at 1 − β, then β = 1/2. (Instantiating at p = 2 suffices.) -/
theorem dual_weights_unique_balance (β : ℝ)
    (h_dual : ∀ p : ℝ, 1 < p → p ^ (-β) = p ^ (-(1 - β))) :
    β = 1 / 2 :=
  (self_dual_weight 2 β (by norm_num)).mp (h_dual 2 (by norm_num))

/-- Conversely, β = 1/2 satisfies all duality conditions. -/
theorem half_is_self_dual (p : ℝ) :
    p ^ (-(1/2 : ℝ)) = p ^ (-(1 - 1/2 : ℝ)) := by
  norm_num

/-- **Main theorem.** The critical line β = 1/2 is the unique locus where
    the self-dual weight condition p^{-β} = p^{-(1-β)} holds for all p > 1.
    This is the formalization of the "fold + duality ⟹ critical line"
    argument: folding kills antisymmetry, duality x ↔ 1-x selects the
    midpoint, and the only residue-free balance point is x = 1/2. -/
theorem critical_line_characterization (β : ℝ) :
    (∀ p : ℝ, 1 < p → p ^ (-β) = p ^ (-(1 - β))) ↔ β = 1 / 2 :=
  ⟨fun h => dual_weights_unique_balance β h,
   fun h _ _ => by subst h; ring_nf⟩

end
